// vim:sw=4
/*
   This file is part of IC3WSTS.

   IC3WSTS is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 2 of the License, or
   (at your option) any later version.

   IC3WSTS is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with IC3WSTS; if not, write to the Free Software
   Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

   Copyright 2012, Johannes Kloos
 */
#ifndef IC3_H_INCLUDED
#define IC3_H_INCLUDED

#include "laparser.h"
#include "wsts.h"

/** Transform a parse tree, obtained from my_yyparse, into
 * a representation of a WSTS coverability problem as given by ic3_data. */
ic3_data build_problem_instance(T_PTR_tree atree, const std::vector<std::string>& var_names);

/** Check whether an instance of the WSTS coverability problem is valid.
 * Returns true iff the problem instance is valid. */
bool ic3_check(const ic3_data&);

#endif // IC3_H_INCLUDED
