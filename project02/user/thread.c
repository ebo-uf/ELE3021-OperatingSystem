#include "thread.h"
#include "kernel/riscv.h"
#include "user/user.h"

int
thread_create(void (*start_routine)(void *, void *), void *arg1, void *arg2)
{
  void *stack = malloc(PGSIZE*2);
  if(stack == 0)
    return -1;
  int pid = clone(start_routine, arg1, arg2, stack);
  if(pid < 0) {
    free(stack);
    return -1;
  }

  return pid;
}

int
thread_join(void)
{
  void *stack;
  int pid = join(&stack);
  if(pid < 0)
    return -1;
  free(stack);
  return pid;
}