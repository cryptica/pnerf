// vim:sw=4
/*
   This file is part of mist2.

   mist2 is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 2 of the License, or
   (at your option) any later version.

   mist2 is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with mist2; if not, write to the Free Software
   Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

   Copyright 2003, 2004, Anthony Piron, Ganty Pierre

   Introduced into IC3WSTS by Johannes Kloos, 2012.
 */

#ifndef __XMALLOC_H
#define __XMALLOC_H

#ifdef __cplusplus
extern "C" {
#endif

#include <stdlib.h>
#include <sys/types.h>

    void* xmalloc(size_t size);
    void* xrealloc(void* ptr, size_t size);
    void xfree(void* ptr);

#ifdef __cplusplus
}
#endif

#endif
