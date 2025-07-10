#include "kernel/types.h"

int thread_create(void (*start_routine)(void *, void *), void *arg1, void *arg2);
int thread_join(void);
