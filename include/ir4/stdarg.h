#ifndef _STDARG_H
#define _STDARG_H

typedef char *va_list;
extern char *__ir4_va_ptr(void);

#define va_start(ap, last) ((ap) = __ir4_va_ptr())
#define va_arg(ap, T) (*(T *)(((ap) += (sizeof(T) < sizeof(int) ? sizeof(int) : sizeof(T))) - (sizeof(T) < sizeof(int) ? sizeof(int) : sizeof(T))))
#define va_end(ap) ((void)0)

#endif
