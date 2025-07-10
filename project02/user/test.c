#include "kernel/types.h"
#include "kernel/stat.h"
#include "user/user.h"
#include "thread.h"

int cnt = 0;

void
thread_func(void *arg1, void *arg2)
{
  cnt++;
  printf("Thread started: arg1='%s', arg2='%s'\n", (char *)arg1, (char *)arg2);
  exit(1);
}

int
main(int argc, char *argv[])
{
  char *msg1 = "Hello";
  char *msg2 = "xv6";

  for(int i=0;i<2;i++) {
    if(thread_create(thread_func, msg1, msg2) < 0){
      printf("thread_create failed\n");
    }
  }
  printf("thread_create succeeded\n");
  exit(1);
}
