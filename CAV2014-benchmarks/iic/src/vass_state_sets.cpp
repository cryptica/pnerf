// vim:sw=4 :cindent
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
#include "vass_state_sets.h"
#include <vector>
#include <set>
#include <stdint.h>
#include <iostream>
#include <exception>
#include <cassert>
#include <algorithm>
#include <limits>

// Note that the default operator== is sufficient because the
// sigma-order can be proved
// to be a partial order, not just a quasi-order.

void ic3_closed_set::write(std::ostream& os) const {
    if (gen.empty()) {
        switch (mode) {
        case IC3_UCI:
            os << "[empty set (uc)]";
            break;
        case IC3_LCE:
            os << "[full set (lc)]";
            break;
        }
        return;
    }
    switch (mode) {
    case IC3_UCI:
        os << "uc ";
	break;
    case IC3_LCE:
        os << "Sigma \\ uc {";
        break;
    }
    ic3_state_set_it it = gen.begin();
    os << *it;
    for (it++; it != gen.end(); it++) {
        os << ", " << *it;
    }
    os << "}";
}

static bool subsumes_forward(const ic3_state_set_it&, const ic3_state_set_it&,
                             const ic3_state&);

typedef std::set<ic3_state>::const_reverse_iterator ic3_state_set_rit;

ic3_state_set do_subsumption(const ic3_state_set& gen,
                                    ic3_closed_set_internal_mode mode) {
    /* Here, we make use of our nice ordering above: By iterating through
     * the state set, we check for each later element whether it is
     * subsumed by earlier ones. We could even build up an extra data
     * structure that helps us check containment, while guaranteeing
     * completeness due to the ordering.
     *
     * The only thing we need to take case of here is to use the right
     * direction - for downward-closed sets, the direction is reversed,
     * and for exclusion-based sets, the order is also reverse (i.e.,
     * downward-closed exlcusion-based sets have the same order as
     * upward-closed sets). Luckily, that is the only case distinction we
     * need.
     * */
    ic3_state_set subsumed;
    for (ic3_state_set_it it(gen.begin()); it != gen.end(); it++) {
        if (!subsumes_forward(subsumed.begin(), subsumed.end(), *it)) {
            subsumed.insert(*it);
        }
    }
    return subsumed;
}

// Check that some element in the range [from, to) is greater or
// equal to s.
static bool subsumes_forward(const ic3_state_set_it& from,
                             const ic3_state_set_it& to, const ic3_state& s) {
    /* Iterate over base points and check. */
    ic3_state_set_it it(from);
    while (it != to) {
        assert(from->size() == s.size());
        // Check whether *from >= s
	if (state_le(*it, s))
	    return true;
	it++;
    }
    // No valid base point found.
    return false;
}

ic3_closed_set::ic3_closed_set(const ic3_state_set& gen_,
                               ic3_closed_set_internal_mode mode_, bool needs_subsumption):
    gen(needs_subsumption ? do_subsumption(gen_, mode_) : gen_),
    mode(mode_) {}

// Operations on closed sets
ic3_ucs add(const ic3_ucs& fst, const ic3_ucs& snd) {
    ic3_state_set s(fst.gen);
    for (ic3_state_set_it it(snd.gen.begin()); it != snd.gen.end(); it++) {
        if (!subsumes_forward(s.begin(), s.end(), *it))
            s.insert(*it);
    }
    return s;
}

/* The comparison predicate */
bool state_le(const ic3_state& a, const ic3_state& b) {
	for (ic3_state_it ita(a.begin()), itb(b.begin()); ita != a.end(); ++ita, ++itb)
		if (*ita > *itb)
			return false;
	return true;
}

/* Upper-closed sets are modelled as containing their minor points. */
bool contained(const ic3_state& p, const ic3_ucs& s) {
    /* The ordering of the states allows us to exclude all those states
     * that are greater in the set ordering from the comparison. */
    ic3_state_set_it it(s.gen.begin()), /*end(s.gen.upper_bound(p))*/
		     end(s.gen.end());
    for (; it != end; it++) {
        if (state_le(*it, p)) {
	    return true;
	}
    }
    return false;
}

constraint::constraint(uint32_t lower_bound_) :
		lower_bound(lower_bound_), upper_bound(std::numeric_limits<uint32_t>::max()), upper_bounded(false) {
}

constraint::constraint(uint32_t lower_bound_, uint32_t upper_bound_) :
		lower_bound(lower_bound_), upper_bound(upper_bound_), upper_bounded(true) {
}

bool constraint::is_upper_bounded() const {
	return upper_bounded;
}

uint32_t constraint::get_lower_bound() const {
	return lower_bound;
}

uint32_t constraint::get_upper_bound() const {
	return upper_bound;
}

constrained_set::constrained_set(uint32_t num_vars) :
		constraints(num_vars) {
}

void constrained_set::add_constraint(uint32_t var, const constraint &c) {
	uint32_t new_lower_bound = std::max(constraints[var].get_lower_bound(), c.get_lower_bound());
	if (constraints[var].is_upper_bounded() || c.is_upper_bounded()) {
		uint32_t new_upper_bound = std::min(constraints[var].get_upper_bound(), c.get_upper_bound());
		constraints[var] = constraint(new_lower_bound, new_upper_bound);
	} else
		constraints[var] = constraint(new_lower_bound);
}

bool constrained_set::is_consistent() const {
	for (std::vector<constraint>::const_iterator it(constraints.begin()); it != constraints.end(); ++it) {
		if (it->get_lower_bound() > it->get_upper_bound())
			return false;
	}
	return true;
}

bool constrained_set::is_upward_closed() const {
	for (std::vector<constraint>::const_iterator it(constraints.begin()); it != constraints.end(); ++it) {
		if (it->is_upper_bounded())
			return false;
	}
	return true;
}

bool constrained_set::is_upper_bounded(uint32_t var) const {
	return constraints[var].is_upper_bounded();
}

uint32_t constrained_set::get_lower_bound(uint32_t var) const {
	return constraints[var].get_lower_bound();
}

uint32_t constrained_set::get_upper_bound(uint32_t var) const {
	return constraints[var].get_upper_bound();
}

ic3_state constrained_set::get_minor() const {
	ic3_state minor;
	for (std::vector<constraint>::const_iterator it(constraints.begin()); it != constraints.end(); ++it) {
		minor.push_back(it->get_lower_bound());
	}
	return minor;
}

std::ostream& constrained_set::print(std::ostream& os) const {
	os << "(";
	for (uint32_t i = 0; i < constraints.size(); ++i) {
		if (is_upper_bounded(i))
			os << " " << get_upper_bound(i);
		else
			os << " w";
	}
	os << ")" << std::endl;
	return os;
}
std::ostream& operator<<(std::ostream& os, const constrained_set& set) {
	return set.print(os);
}

std::vector<state_activity_wrapper> downward_closure(uint32_t nbr_var, const constrained_set& s) {
	std::vector<state_activity_wrapper> result;
	for (uint32_t i = 0; i < nbr_var; ++i) {
		if (s.is_upper_bounded(i)) {
			ic3_state state(nbr_var);
			state[i] = s.get_upper_bound(i) + 1;
			result.push_back(state_activity_wrapper(state));
		}
	}
	return result;
}


