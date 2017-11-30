/*
 *  Copyright (C) 2013-2014  Ying Ye, PhD Candidate, Boston University
 *  Advisor: Richard West
 *
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

#include <linux/module.h>
#include <linux/init.h>
#include <linux/kernel.h>
#include <linux/tty.h>
#include <linux/sched.h>
#include <linux/slab.h>
#include <asm-generic/memory_model.h>
#include <asm/tlbflush.h>
#include <asm/msr.h>
#include <linux/spinlock.h>
#include <linux/rcupdate.h>
#include <linux/color_alloc.h>
#include <linux/mm.h>
#include <linux/string.h>
#include <linux/highmem.h>
#include <linux/rwsem.h>
#include <linux/hrtimer.h>
#include <linux/ktime.h>
#include <linux/cpumask.h>
#include <linux/ioctl.h>
#include <linux/proc_fs.h>
#include <linux/kthread.h>
#include <linux/pagemap.h>
#include <linux/rmap.h>
#include "list.h"

/* XXX: Multi-threading not supported yet */

MODULE_LICENSE("GPL");
MODULE_AUTHOR("Ying Ye <yingy@bu.edu>");

//#define ALLOC_DEBUG
#define REDISTRIBUTION
//#define SEL_MOVE
#define REC_COUNT
#define TEST_TIME 3600


#define MY_CHECK_ALL      _IOW(0, 0, long)
#define MY_CHECK_ONE      _IOW(0, 1, long)
#define MY_CHECK_RESERVE  _IOW(0, 2, long)
#define MY_CHECK_FILE     _IOW(0, 3, long)
#define MY_CHECK_IPC      _IOW(0, 4, long)
#define MY_CHECK_HOT      _IOW(0, 5, long)

static struct file_operations proc_operations;
static struct proc_dir_entry *proc_entry;
int debug_ioctl(struct file *, unsigned int, unsigned long);


extern struct page * (*colored_alloc)(struct mm_struct *mm, int zero);
extern struct page * (*colored_alloc_file)(struct file *filp);
extern void (*assign_colors)(struct mm_struct *mm);
extern int (*colored_free)(struct page *pg, struct zone *zone);
extern int (*check_apps)(struct file *filp);
extern int (*recolor_mm)(struct mm_struct *mm, int isExpand);
extern void (*color_collect)(struct mm_struct *mm);
extern void (*finish_recolor)(struct mm_struct *mm);
extern void (*collect_inst)(struct task_struct *task);
extern int cmr_high_threshold;
extern int cmr_low_threshold;
extern int recolor_delay;
extern unsigned int sample_stages[NR_CPUS];

/* 
 * 32-bit system, LLC size 4MB, 16 ways, page size 4KB
 * color number = (LLC size / number of ways) / page size
 */
#define PG_SIZE (4*1024)
#define WAY_ASSOC 16
/* if color number is changed, GET_COLOR should be modified */
#define COLOR_NUM 64
/* 1GB RAM for coloring */
#define RAM_SIZE (1024*1024*1024)
/* 4 cores */
#define NUM_CORES 4

/* number of applications supported */
#define MAX_APPS 30

/* recoloring parameters */
#define CMR_HIGH_INIT 75
#define CMR_LOW_INIT 30
#define SAMPLE_PERIOD 5
#define REC_DELAY 10
#define MAX_COLORS 48
#define MIN_COLORS 4
#define SCAN_WIN 3000000
#define COLORS_ONCE 4
#define COLORS_TRY 4

struct _Scanner {
  struct hrtimer timer;
  int working;
  spinlock_t lock;
};

static struct _Scanner scanner;

/* array of colors */
static LIST color_lists[COLOR_NUM];
/* 
 * used when filling in memory pool
 * page of unwanted color should not be freed before pool is full
 * otherwise, it may be reallocated to us again and again
 */
static LIST page_buf;
/* locks for each color list */
static spinlock_t color_locks[COLOR_NUM];

/* 
 * hotness for every color 
 * count: global hotness
 * remote: remote hotness
 */
struct _GHotness {
  spinlock_t lock;
  int count[COLOR_NUM];
  int remote[COLOR_NUM];
};

static struct _GHotness global_hotness;


static int pg_num;
static struct page template;
static int e_counter = 0;

static char *apps[MAX_APPS];
static int nr_apps;
module_param_array(apps, charp, &nr_apps, 0644);

static int qos_pair[2*MAX_APPS];
module_param_array(qos_pair, int, NULL, 0644);

struct MyQoS {
  int high[MAX_APPS];
  int low[MAX_APPS];
};

static struct MyQoS app_qos;

static int quanta[MAX_APPS];

static struct color_set assignment[MAX_APPS];
static unsigned int cpu_pin[MAX_APPS];

static unsigned int app_inst_l[MAX_APPS];
static unsigned int app_inst_h[MAX_APPS];
static unsigned int app_ref_l[MAX_APPS];
static unsigned int app_ref_h[MAX_APPS];
static unsigned int app_miss_l[MAX_APPS];
static unsigned int app_miss_h[MAX_APPS];

static spinlock_t app_locks[MAX_APPS];

/* XXX: only needed for coloring code segment */
struct pureHack {
  int hit[MAX_APPS];
  struct address_space *mapping[MAX_APPS];
  struct address_space *target[MAX_APPS];
  int cur_color[MAX_APPS];
};

static struct pureHack hackdata;

static const unsigned int select_msr_inst = 0xC0 | (0x00 << 8) | (0x01 << 16) 
                                          | (0x01 << 22);
static const unsigned int select_msr_cyc = 0x3C | (0x00 << 8) | (0x01 << 16) 
                                          | (0x01 << 22);
static const unsigned int select_msr_ref = 0x2E | (0x4F << 8) | (0x01 << 16) 
                                          | (0x01 << 22);
static const unsigned int select_msr_miss = 0x2E | (0x41 << 8) | (0x01 << 16)
					  | (0x01 << 22);
static struct hrtimer ipc_timer[NUM_CORES];
static int ipc_sig[NUM_CORES];
static struct hrtimer sample_timer[NUM_CORES];
static spinlock_t ipc_lock;
static volatile int ipc_apps = 0;

/* *********Utilities********* */
#define GET_COLOR(pfn) (pfn & 0x3F)


static void init_check(void) {

  int i, j;
  for (i = 0; i < COLOR_NUM; i++) {
    if (color_lists[i].num != pg_num) {
      printk(KERN_ERR "color %d not full: %d pages\n", i, color_lists[i].num);
    }

    struct list_head *cur = color_lists[i].head;
    int flag = 0;
    for (j = 0; j < pg_num; j++) {
      if (GET_COLOR(page_to_pfn(list_to_page(cur))) != i) {
        flag = 1;
      }
      cur = cur->next; 
    }

    if (flag) {
      printk(KERN_ERR "color %d has pages of different colors\n", i);
    }
  }
}

static inline void check_page(struct page *pg);

static void free_list_pgs(LIST *list) {

  struct page *pg;
  while(list->num > 0) {
    pg = list_remove(list);

#ifdef ALLOC_DEBUG
    check_page(pg);
#endif

    pg->lru.next = LIST_POISON1;
    pg->lru.prev = LIST_POISON2;
    __free_page(pg);
  }
}

static void check_lists(void) {

  int i, flag = 0;
  for (i = 0; i < COLOR_NUM; i++) {
    if (color_lists[i].num != 0) {
      flag = 1;
      printk(KERN_ERR "color not freed: %d\n", i);
      free_list_pgs(&color_lists[i]);
    }
  }
  if (flag) printk(KERN_ERR "Memory pool not freed completely!\n");
}

static inline void my_dump_page(struct page *pg) {

  printk(KERN_ERR "page %x: %x %x %x %x %x %x %x %x\n", (unsigned long)pg, pg->flags, 
        pg->_count.counter, pg->_mapcount.counter, pg->private, (long)pg->mapping, 
        pg->index, (unsigned long)pg->lru.next, (unsigned long)pg->lru.prev);
}

static inline void check_page(struct page *pg) {

  if (pg->_count.counter != template._count.counter) goto next;
  if (pg->_mapcount.counter != template._mapcount.counter) goto next;
  if (pg->mapping != template.mapping) goto next;
  if (pg->lru.next != template.lru.next) goto next;
  if (pg->lru.prev != template.lru.prev) goto next;
  if ((pg->flags & ((1 << __NR_PAGEFLAGS) - 1)) != 
    (template.flags & ((1 << __NR_PAGEFLAGS) - 1))) goto next;

  return;

next:
  e_counter++;
  my_dump_page(pg);
}

static inline void zero_page(struct page *pg) {

  void *addr = kmap_atomic(pg);

  memset(addr, 0, PG_SIZE);
  kunmap_atomic(addr);
}

static void check_assignment(int index) {

  int j;
  
  printk(KERN_ERR "%s:", apps[index]);
  for (j = 0; j < quanta[index]; j++) {
    printk(KERN_ERR " %d", assignment[index].colors[j]);
  }
  printk(KERN_ERR "\n");
}

/* str1 should be the string to be checked */
static int string_eq(char *str1, char *str2) {

  int i = 0;
  while(str1[i] != '\0' && str2[i] != '\0') {
    if (str1[i] != str2[i]) return 0;
    i++;
  }

  if (str2[i] != '\0') return 0;
  else return 1;
}


int fire_timer(void *arg);

/* *********Allocator********* */

static int __init alloc_init(void) {

  proc_operations.unlocked_ioctl = debug_ioctl;

  proc_entry = create_proc_entry("alloc", 0444, NULL);
  if (!proc_entry) {
    printk(KERN_ERR "Error creating /proc entry.\n");
    return 1;
  }

  proc_entry->proc_fops = &proc_operations;

  pg_num = RAM_SIZE / (COLOR_NUM * PG_SIZE);
  struct page *new_pg;
  int k;

  if (PG_SIZE != PAGE_SIZE) {
    printk(KERN_ERR "only 4KB page size is supported!\n");
    return 1;
  }

  cmr_high_threshold = CMR_HIGH_INIT;
  cmr_low_threshold = CMR_LOW_INIT;
  recolor_delay = REC_DELAY;
  for (k = 0; k < NUM_CORES; k++)
    sample_stages[k] = 0;

  spin_lock_init(&scanner.lock);
  scanner.working = 0;

  spin_lock_init(&ipc_lock);

  /* initialize global hotness */
  for (k = 0; k < COLOR_NUM; k++) {
    global_hotness.count[k] = 0;
    global_hotness.remote[k] = 0;
  }
  spin_lock_init(&global_hotness.lock);

  /* initialize locks */
  for (k = 0; k < COLOR_NUM; k++)
    spin_lock_init(&color_locks[k]);

  int start = 0, iter;
  for (iter = 0; iter < nr_apps; iter++)
    quanta[iter] = COLOR_NUM / NUM_CORES;

  for (iter = 0; iter < nr_apps; iter++) {
    if (quanta[iter] > COLOR_BASE) {
      printk(KERN_ERR "quanta is larger than max!\n");
      return 1;
    }

    app_qos.high[iter] = qos_pair[2*iter];
    app_qos.low[iter] = qos_pair[2*iter + 1];

    spin_lock_init(&app_locks[iter]);

    app_inst_h[iter] = 0;
    app_inst_l[iter] = 0;
    app_ref_h[iter] = 0;
    app_ref_l[iter] = 0;
    app_miss_l[iter] = 0;
    app_miss_h[iter] = 0;

    hackdata.cur_color[iter] = 0;

    k = 0;
    while(k < quanta[iter]) {
      assignment[iter].colors[k] = start; 
      k++;
      start = (start + 1) % COLOR_NUM;
    }

    cpu_pin[iter] = assignment[iter].colors[0] / (COLOR_NUM / NUM_CORES);

#ifdef ALLOC_DEBUG
    printk(KERN_ERR "assigned cpu: %d\n", cpu_pin[iter]);
    check_assignment(iter);
#endif

    hackdata.hit[iter] = 0;
  }

  /* fill in memory pool */
  int count = 0, color, num;
  unsigned long frame;

  for (k = 0; k < COLOR_NUM; k++) {
    color_lists[k].num = 0;
    color_lists[k].head = NULL;
  }

  page_buf.num = 0;
  page_buf.head = NULL;

#ifdef ALLOC_DEBUG
  struct page *t_pg;
  t_pg = alloc_page(__GFP_HIGHMEM | __GFP_MOVABLE);

  template._count.counter = t_pg->_count.counter;
  template._mapcount.counter = t_pg->_mapcount.counter;
  template.mapping = t_pg->mapping;
  template.lru.next = t_pg->lru.next;
  template.lru.prev = t_pg->lru.prev;
  template.flags = t_pg->flags;
#endif

  while(count != COLOR_NUM) {
    new_pg = alloc_page(__GFP_HIGHMEM | __GFP_MOVABLE); 

    frame = page_to_pfn(new_pg);
    color = GET_COLOR(frame);

    num = color_lists[color].num;
    if (num >= pg_num) { /* color list is full */
      list_insert(&page_buf, new_pg);
    }
    else {
#ifdef ALLOC_DEBUG
      check_page(new_pg);
#endif
      if (page_zone(new_pg)->name[0] != 'H') {
        printk(KERN_ERR "pages have to be taken from HighMem\n");
        return 1;
      }

      list_insert(&color_lists[color], new_pg);

      if (color_lists[color].num == pg_num) count++;
    }
  }

#ifdef ALLOC_DEBUG
  __free_page(t_pg);
  printk(KERN_ERR "counter: %d\n", e_counter);
#endif

  /* free page buffer */
  free_list_pgs(&page_buf);

  /* load functions */
/*
  colored_free = free_colored_page;
  color_collect = release_colors;
  colored_alloc = alloc_colored_page;
  colored_alloc_file = alloc_colored_page_file;
  check_apps = apps_check;
  finish_recolor = move_pages;
  collect_inst = inst_read;
  recolor_mm = mm_recoloring;
  assign_colors = get_color_set;
*/
  for (k = 0; k < NUM_CORES; k++)
    kthread_run(fire_timer, (void *)k, "my thread");
  
#ifdef ALLOC_DEBUG
  init_check();
#endif

  printk(KERN_ERR "Allocator loaded!\n");
  return 0;
}


static void __exit alloc_cleanup(void) {

  remove_proc_entry("alloc", NULL);

  int i;
  for (i = 0; i < COLOR_NUM; i++) {
    spin_lock(&color_locks[i]);
  }

  /* unload functions */
  // XXX: synchronization may be needed
  assign_colors = NULL;
  recolor_mm = NULL;
  collect_inst = NULL;
  finish_recolor = NULL;
  check_apps = NULL;
  colored_alloc_file = NULL;
  colored_alloc = NULL;
  color_collect = NULL;
  colored_free = NULL;

  /* free memory pool */
  for (i = 0; i < COLOR_NUM; i++) {
    free_list_pgs(&color_lists[i]);
  }

  for (i = 0; i < COLOR_NUM; i++) {
    spin_unlock(&color_locks[i]);
  }

  /* FIXME: wait for apps to exit module functions */
  schedule();

  for (i = 0; i < COLOR_NUM; i++) {
    spin_lock(&color_locks[i]);
  }

  /* for pages freed after function unloaded */
  for (i = 0; i < COLOR_NUM; i++) {
    free_list_pgs(&color_lists[i]);
  }

  for (i = 0; i < COLOR_NUM; i++) {
    spin_unlock(&color_locks[i]);
  }

  free_list_pgs(&page_buf);

#ifdef ALLOC_DEBUG
  check_lists();
#endif

  printk(KERN_ERR "Allocator unloaded!\n");
}

enum hrtimer_restart ipc_count(struct hrtimer *timer) {

  ktime_t ktime;
  int cpu = smp_processor_id();

  if (!ipc_sig[cpu]) {
    wrmsr(0xC3, 0, 0);

    /* get result after some time */
    ktime = ktime_set(TEST_TIME, 0);
    hrtimer_forward_now(timer, ktime);
    ipc_sig[cpu] = 1;

    /* periodic sampling */
    ktime = ktime_set(SAMPLE_PERIOD, 0);
    hrtimer_init(&sample_timer[cpu], CLOCK_MONOTONIC, HRTIMER_MODE_REL_PINNED);
    sample_timer[cpu].function = do_sample;
    hrtimer_start(&sample_timer[cpu], ktime, HRTIMER_MODE_REL_PINNED);

    printk(KERN_ERR "%s: first stage\n", __func__);

    return HRTIMER_RESTART;
  }
  else {
    hrtimer_cancel(&sample_timer[cpu]);

    ipc_sig[cpu] = 0;

    printk(KERN_ERR "%s: second stage\n", __func__);

    return HRTIMER_NORESTART;
  }
}

int fire_timer(void *arg) {

  struct cpumask mask;
  unsigned int cpu = (unsigned int)arg;
  ktime_t ktime;

  /* pin to cpu */
  cpumask_clear(&mask);
  cpumask_set_cpu(cpu, &mask);

  sched_setaffinity(0, &mask);

  /* when next time gets scheduled, runs on designated cpu */
  while(ipc_apps != nr_apps) schedule();

  if (smp_processor_id() != cpu) {
    printk(KERN_ERR "Fails to fire timer %d!\n", cpu);
    return 0;
  }

  ipc_sig[smp_processor_id()] = 0;

  /* install hrtimer */
  /* start counting after 1 min */
  ktime = ktime_set(60, 0);
  hrtimer_init(&ipc_timer[cpu], CLOCK_MONOTONIC, HRTIMER_MODE_REL_PINNED);
  ipc_timer[cpu].function = ipc_count;
  hrtimer_start(&ipc_timer[cpu], ktime, HRTIMER_MODE_REL_PINNED);

  return 0;
}

/* ioctl entry point, debugging tool */
int debug_ioctl(struct file *file, unsigned int cmd, unsigned long arg) {

  struct task_struct *p;
  struct mm_struct *mm;
  int index, i;
  struct color_set *set_ptr;

  if (cmd == MY_CHECK_ALL) {
    read_lock(&tasklist_lock);

    for_each_process(p) {
      mm = p->mm;
      /* ignore kernel threads and irrelevant processes */
      if (mm != NULL && mm->color_num > 0) {
        printk(KERN_ERR "%s (pid %d, tgid %d, mm addr %x, colors %d): ", p->comm,
          p->pid, p->tgid, (unsigned int)mm, mm->color_num);

        index = 0;
        set_ptr = &(mm->my_colors);

        do {
          printk(KERN_ERR "%d ", set_ptr->colors[index]);
          index++;
        } while(index < mm->color_num);

        printk(KERN_ERR " current: %d\n", mm->color_cur);

        printk(KERN_ERR "QoS: %d %d\n", mm->h_thred, mm->l_thred);
      }
    }

    read_unlock(&tasklist_lock);
  }
  else if (cmd == MY_CHECK_ONE) {
    rcu_read_lock();

    /* look up thread by pid */
    p = find_task_by_vpid((pid_t)arg);

    rcu_read_unlock();

    if (p == NULL) {
      printk(KERN_ERR "No process found!\n");
    }
    else if (p->mm == NULL) {
      printk(KERN_ERR "PID belongs to kernel thread!\n");
    }
    else if (p->mm->color_num == 0) {
      printk(KERN_ERR "No color assigned to it!\n");
    }
    else {
      mm = p->mm;
      index = 0;
      set_ptr = &(mm->my_colors);

      printk(KERN_ERR "Process %s: ", p->comm);
      do {
        printk(KERN_ERR "%d ", set_ptr->colors[index]);
        index++;
      } while(index < mm->color_num);

      printk(KERN_ERR " current: %d\n", mm->color_cur);

      printk(KERN_ERR "QoS: %d %d\n", mm->h_thred, mm->l_thred);
    }
  }
  else if (cmd == MY_CHECK_RESERVE) {
    printk(KERN_ERR "Color statistic: ");

    for (i = 0; i < COLOR_NUM; i++)
      printk(KERN_ERR "color %d (%d) ", i, (int)(color_lists[i].num));

    printk(KERN_ERR "\n");
  }
  else if (cmd == MY_CHECK_FILE) {
    printk(KERN_ERR "assignments: ");

    for (i = 0; i < nr_apps; i++) {
      printk(KERN_ERR "%s (%d): ", apps[i], quanta[i]);

      index = 0;
      set_ptr = &assignment[i];
      do {
        printk(KERN_ERR "%d ", set_ptr->colors[index]);
        index++;
      } while(index < quanta[i]);

      printk(KERN_ERR " current: %d\n", hackdata.cur_color[i]);

      printk(KERN_ERR "QoS: %d %d\n", app_qos.high[i], app_qos.low[i]);
    }
  }
  else if (cmd == MY_CHECK_IPC) {
    printk(KERN_ERR "IPCs: ");

    for (i = 0; i < nr_apps; i++)
      printk(KERN_ERR "app %s, inst %u %u\n", apps[i], app_inst_h[i], 
        app_inst_l[i]);

    for (i = 0; i < nr_apps; i++)
      printk(KERN_ERR "app %s, miss %u %u, ref %u %u\n", apps[i], app_miss_h[i], 
        app_miss_l[i], app_ref_h[i], app_ref_l[i]);
  }
  else if (cmd == MY_CHECK_HOT) {
    printk(KERN_ERR "Hotness: ");

    for (i = 0; i < COLOR_NUM; i++)
      printk(KERN_ERR "color %d: %d remote %d\n", i, global_hotness.count[i], 
        global_hotness.remote[i]);
  }
  else {
    printk(KERN_ERR "Invalid input command!\n");
    return -1;
  }

  return 0;
}


module_init(alloc_init);
module_exit(alloc_cleanup);

/* vi: set et sw=2 sts=2: */
