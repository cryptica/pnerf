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

#ifndef __TBSYMBOLINFO_H
#define __TBSYMBOLINFO_H

#ifdef __cplusplus
extern "C" {
#endif

#include "tbsymbol.h"

#define tbsymbol_INFO_ID 1
#define tbsymbol_INFO_NB 2

    typedef struct {
        int addr;
    } T_tbsymbol_id;


    typedef struct {
        int value;
    } T_tbsymbol_nbr;


    typedef union {
        T_tbsymbol_id id;
        T_tbsymbol_nbr nb;
    } T_tbsymbol_union;


    typedef struct {
        int tag;
        T_tbsymbol_union info;
    } T_tbsymbol_info;


    typedef T_tbsymbol_info* T_PTR_tbsymbol_info;

    T_PTR_tbsymbol_info tbsymbol_info_new();
    void tbsymbol_info_destroy(T_PTR_tbsymbol_info* info);

#ifdef __cplusplus
}
#endif

#endif
