// vim:sw=4:cindent
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

 Copyright 2012 Johannes Kloos.
 */
#include "vass_global_state.h"
#include "wsts.h"
#include "helpers.h"
#include <algorithm>
#include <vector>
#include <list>
#include <cassert>
#include <iostream>
#include <boost/optional.hpp>
#include <string>
#include <sstream>

state_activity_wrapper::state_activity_wrapper(const ic3_state& _state) :
		state(_state), active(true) {
}

ic3_state& state_activity_wrapper::get_state() {
	return state;
}

const ic3_state& state_activity_wrapper::get_state() const {
	return state;
}

bool state_activity_wrapper::is_active() const {
	return active;
}

void state_activity_wrapper::inactivate() {
	active = false;
}

state_activity_wrapper state_activity_wrapper::active_copy() const {
	return state_activity_wrapper(state);
}

std::ostream& operator<<(std::ostream& os, const state_activity_wrapper& wrapper) {
	return os << wrapper.get_state();
}

ic3_state_vector::ic3_state_vector(const ic3_data& data) {
	// calculate the downward closure of init.
	F_latest.push_back(downward_closure(data.nbr_var, data.init));
	debuglog<< "R[0] = " << F_latest[0] << std::endl;
	F_latest.push_back(std::vector<state_activity_wrapper>());
}

std::vector<state_activity_wrapper> ic3_state_vector::F(uint32_t index) const {
	uint32_t sz = F_latest.size();
	assert(sz > 1);
	return F_latest[std::min(index, sz - 1)];
}

void ic3_state_vector::unfold() {
	F_latest.insert(F_latest.begin() + F_latest.size() - 1, std::vector<state_activity_wrapper>());
}

void ic3_state_vector::block(uint32_t t, const ic3_state& x, bool purge_immediately) {
	// Inactivate subsumed.
	for (uint32_t i = 1; i <= t; ++i) {
		for (std::vector<state_activity_wrapper>::iterator it(F_latest[i].begin()); it != F_latest[i].end(); ++it)
			if (it->is_active() && state_le(x, it->get_state()))
				it->inactivate();
		if (purge_immediately)
			purge_inactive(i);
	}
	F_latest[t].push_back(state_activity_wrapper(x));
}

opt_timed_state ic3_state_vector::blocking_state_at(uint32_t t, const ic3_state& x) const {
	for (std::vector<state_activity_wrapper>::const_iterator it(F_latest[t].begin()); it != F_latest[t].end(); ++it)
		if (it->is_active() && state_le(it->get_state(), x))
			return opt_timed_state(timed_state(t, it->get_state()));
	return opt_timed_state();
}

opt_timed_state ic3_state_vector::blocking_state(uint32_t t, const ic3_state& x, uint32_t hint) const {
	if (t == 0)
		return blocking_state_at(0, x);
	hint = std::max(t, hint);
	for (uint32_t i = hint; i < F_latest.size(); i++) {
		opt_timed_state ots = blocking_state_at(i, x);
		if (ots)
			return ots;
	}
	for (uint32_t i = hint - 1; i >= t; i--) {
		opt_timed_state ots = blocking_state_at(i, x);
		if (ots)
			return ots;
	}
	return opt_timed_state();
}

bool ic3_state_vector::is_blocked(uint32_t t, const ic3_state& x) const {
	return blocking_state(t, x);
}

void ic3_state_vector::purge_inactive(uint32_t t) {
	uint32_t i = 0, j = F_latest[t].size();
	while (i < j) {
		while (i < F_latest[t].size() && F_latest[t][i].is_active())
			++i;
		while (j > 0 && !F_latest[t][j - 1].is_active())
			--j;
		if (i < j)
			std::swap(F_latest[t][i++], F_latest[t][--j]);
	}
	F_latest[t].erase(F_latest[t].begin() + i, F_latest[t].end());
}

void ic3_state_vector::purge_inactive_all() {
	for (uint32_t i = 1; i < F_latest.size(); ++i)
		purge_inactive(i);
}

bool ic3_state_vector::has_active(uint32_t t) const {
	for (std::vector<state_activity_wrapper>::const_iterator it(F_latest[t].begin()); it != F_latest[t].end(); ++it)
		if (it->is_active())
			return true;
	return false;
}

void ic3_state_vector::print_invariant(uint32_t t, const std::vector<std::string>& var_names) const {
	int num_clauses(0), num_atoms(0);
	std::ostringstream out_stream;
	std::string delim("");
	for (uint32_t i = t; i < F_latest.size(); ++i) {
		for (std::vector<state_activity_wrapper>::const_iterator it(F_latest[i].begin()); it != F_latest[i].end(); ++it)
			if (it->is_active()) {
				std::string inner_delim(delim + "(");
				const ic3_state &state(it->get_state());
				for (uint32_t j = 0; j < state.size(); ++j)
					if (state[j] != 0) {
						out_stream << inner_delim << var_names[j] << " < " << state[j];
						num_atoms++;
						inner_delim = " or ";
					}
				if (inner_delim != "(")
					out_stream << ")";
				num_clauses++;
				delim = " and ";
			}
	}
	std::cout << "Invariant: " << out_stream.str() << std::endl;
	std::cout << "Invariant (clauses): " << num_clauses << std::endl;
	std::cout << "Invariant (atoms): " << num_atoms << std::endl;
	std::cout << "Invariant (chars): " << out_stream.str().size() << std::endl;
}

