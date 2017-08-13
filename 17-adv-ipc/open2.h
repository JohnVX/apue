#include "apue.h"
#include <errno.h>

#define CL_OPEN "open"
#define CS_OPEN "/tmp/opend.socket"

int csopen(char *, int);
