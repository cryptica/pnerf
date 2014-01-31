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

   Copyright 2002, Anthony Piron

   Introduced into IC3WSTS by Johannes Kloos, 2012.
 */

#ifndef __TBSYMBOL_H
#define __TBSYMBOL_H

#ifdef __cplusplus
extern "C" {
#endif

#include <sys/types.h>

#define MAX_STR 257

    typedef struct {
        char name[MAX_STR];
        void* info;
    } T_tbsymbol_entry;

    typedef T_tbsymbol_entry* T_PTR_tbsymbol_entry;

    typedef struct {
        size_t size, nbr_entries;
        T_PTR_tbsymbol_entry table;
    } T_tbsymbol;

    typedef T_tbsymbol* T_PTR_tbsymbol;


    void tbsymbol_init(T_PTR_tbsymbol* tbsymbol, size_t tb_size);
    void tbsymbol_destroy(T_PTR_tbsymbol* tbsymbol);

    T_PTR_tbsymbol_entry tbsymbol_insert(T_PTR_tbsymbol tbsymbol, char* name);
    T_PTR_tbsymbol_entry tbsymbol_select(T_PTR_tbsymbol tbsymbol, char* name);
    void tbsymbol_setinfo(T_PTR_tbsymbol_entry entry, void* info, size_t size);
    void* tbsymbol_getinfo(T_PTR_tbsymbol_entry entry);

    void tbsymbol_dump(T_PTR_tbsymbol tbsymbol,
                       void (*callback)(T_PTR_tbsymbol_entry entry));

#ifdef __cplusplus
}
#endif

#endif
