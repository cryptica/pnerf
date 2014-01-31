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

   Copyright 2002, 2003, 2004, Pierre Ganty, Anthony Piron

   Introduced into IC3WSTS by Johannes Kloos, 2012.
 */

#ifndef __LAPARSER_H
#define __LAPARSER_H

#ifdef __cplusplus
extern "C" {
#endif

#include <string.h>
#include <stdlib.h>
#include "error.h"
#include "xmalloc.h"
#include "tbsymbol.h"
#include "tbsymbolinfo.h"
#include "tree.h"

#ifndef __LOCAL
#define EXTERN extern
#endif

    extern int linenumber;
    extern unsigned int nbr_var;
    extern T_PTR_tbsymbol tbsymbol;

    int my_yyparse(T_PTR_tree* tree, char* filename, void (*callback)(T_PTR_tbsymbol_entry entry));

#ifdef __cplusplus
}
#endif

#endif
