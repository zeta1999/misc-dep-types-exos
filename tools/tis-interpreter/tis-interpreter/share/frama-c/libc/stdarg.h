/**************************************************************************/
/*                                                                        */
/*  This file is part of Frama-C.                                         */
/*                                                                        */
/*  Copyright (C) 2007-2015                                               */
/*    CEA (Commissariat à l'énergie atomique et aux énergies              */
/*         alternatives)                                                  */
/*                                                                        */
/*  you can redistribute it and/or modify it under the terms of the GNU   */
/*  Lesser General Public License as published by the Free Software       */
/*  Foundation, version 2.1.                                              */
/*                                                                        */
/*  It is distributed in the hope that it will be useful,                 */
/*  but WITHOUT ANY WARRANTY; without even the implied warranty of        */
/*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         */
/*  GNU Lesser General Public License for more details.                   */
/*                                                                        */
/*  See the GNU Lesser General Public License version 2.1                 */
/*  for more details (enclosed in the file licenses/LGPLv2.1).            */
/*                                                                        */
/**************************************************************************/

/* ISO C: 7.15 */
#ifndef __FC_STDARG
#define __FC_STDARG
#include "features.h"
__BEGIN_DECLS
typedef __builtin_va_list va_list;
__END_DECLS
#define va_arg(ap,typ)     __builtin_va_arg(ap,typ)
#define va_copy(dest,src)  __builtin_va_copy(dest,src)
#define va_end(ap)         __builtin_va_end(ap)
#define va_start(ap,parmN) __builtin_va_start(ap,parmN)
#endif
