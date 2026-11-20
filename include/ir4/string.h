#ifndef _STRING_H
#define _STRING_H

#ifndef NULL
#define NULL ((void *)0)
#endif

#ifndef _SIZE_T_DEFINED
#define _SIZE_T_DEFINED
typedef unsigned int size_t;
#endif

extern void *__c_memcpy(void *dst, const void *src, size_t len);
#define memcpy(d, s, n) __c_memcpy((d), (s), (n))
extern void *memset(void *dst, int val, size_t len);
extern int memcmp(const void *a, const void *b, size_t len);
extern size_t strlen(const char *s);
extern int strcmp(const char *a, const char *b);
extern char *strcpy(char *dst, const char *src);

#endif
