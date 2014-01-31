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
#ifndef IC3_WSTS_H
#define IC3_WSTS_H 1

#include "vass_state_sets.h"
#include <vector>
#include <string>

struct ic3_transition {
	ic3_state guard;
	std::vector<int32_t> delta;
	ic3_transition(const ic3_state guard_, std::vector<int32_t> delta_) :
			guard(guard_), delta(delta_) {
	}
};

struct ic3_data {
	uint32_t nbr_var;
	ic3_ucs bad;
	constrained_set init;
	std::vector<ic3_transition> transition;
	std::vector<std::string> var_names;
	ic3_data(uint32_t nbr_var_, const ic3_ucs& bad_, const constrained_set& init_, const std::vector<ic3_transition>& t,
			const std::vector<std::string>& var_names_) :
			nbr_var(nbr_var_), bad(bad_), init(init_), transition(t), var_names(var_names_) {
	}
};

#endif
