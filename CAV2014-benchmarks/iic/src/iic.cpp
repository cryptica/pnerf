// vim:sw=4 :cindent
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

 Copyright 2002-2007 Pierre Ganty, Laurent Van Begin

 Introduced into IC3WSTS by Johannes Kloos.
 Copyright 2012 Johannes Kloos.
 */

#include <cstdio>
#include <cstdlib>
#include <iostream>
#include <vector>
#include <string>

#include "laparser.h"
#include "iic.h"
#include "helpers.h"
#include "wsts.h"
#include "exceptions.h"

std::vector<std::string> var_names;

void insert_var_name(T_PTR_tbsymbol_entry entry) {
	T_PTR_tbsymbol_info info = static_cast<T_PTR_tbsymbol_info>(tbsymbol_getinfo(entry));
	if (info->tag == tbsymbol_INFO_ID && info->info.id.addr >= 0) // we have a variable
		var_names.push_back(std::string(entry->name));
}

int main(int argc, char *argv[]) {
	T_PTR_tree atree;

	debuglog <<  "Preparing to analyze " << argv[1] << std::endl;
	linenumber = 1;
	//tbsymbol_init(&tbsymbol, 4096);

	try {
		debuglog <<  "Parsing" << std::endl;
		my_yyparse(&atree, argv[1], &insert_var_name);
		ic3_data d(build_problem_instance(atree, var_names));

		debuglog <<  "Analyzing" << std::endl;
		if (ic3_check(d)) {
			std::cout << "The system is safe: Cover and target states are disjoint" << std::endl;
		} else {
			std::cout << "The system is unsafe: Cover and target states intersect" << std::endl;
		}
	} catch (parse_exception &e) {
		debuglog << e.what() << std::endl;
		return EXIT_FAILURE;
	}
}
