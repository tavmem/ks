#ifndef INCS_H
#define INCS_H

#ifdef WIN32
#ifndef WIN32_LEAN_AND_MEAN
#define WIN32_LEAN_AND_MEAN
#endif
#define _WIN32_WINNT 0x0501
#include <stdint.h>
#include <_mingw.h>
#include <winsock2.h>
#include <windef.h>
#include <ws2tcpip.h>
#include "win/dlfcn.h"
#include "win/mman.h"  //mmap
#else
#include <fnmatch.h>
#include <netdb.h>
#include <dlfcn.h>
#include <sys/mman.h>  //mmap
#ifndef MAP_NORESERVE
#define MAP_NORESERVE 0
#endif
#endif

#include <limits.h>
#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>    //M()/OOM_CD()
#include <math.h>
#include <time.h>
#include <string.h>
#include <ctype.h>
#include <errno.h>
#include <sys/stat.h>

#include <unistd.h>    //sbrk,sysconf
#include <fcntl.h>     //O_RDWR etc
#define _TIMESPEC_DEFINED
#include <pthread.h>

#include "ts.h" //data types + macros

#define _exit __exit //stdlib.h already defines "_exit" but we need it for reserved r.c's _exit function

extern I kreci;
extern V krec[1000000];
extern K _ssr(K a,K b,K c);

#endif
