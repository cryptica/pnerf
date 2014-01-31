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
#ifndef IC3_SOLVER_H
#define IC3_SOLVER_H 1

#include "vass_state_sets.h"
#include "vass_global_state.h"
#include "wsts.h"
#include <boost/optional.hpp>
#include <boost/variant.hpp>
#include <list>

/** Solver result type. If a pre-image for the given state has been found,
 * return an ic3_state. Otherwise, return an instance of the corresponding
 * blocking vector. */
typedef boost::variant<ic3_state, timed_state> preimage_or_blocking_data;

/** Try to find a pre-image state for the given state <s, i> that lies in R_i-1.
 * Return that pre-image state, or a witness blocking set. */
preimage_or_blocking_data solve_preimage(ic3_state_vector*, const ic3_data&,
        const timed_state&);
/** Try to find a relative inductive set. Returns either "no set found",
 * or a generalization with associated R_i set. */
opt_timed_state solve_induction(ic3_state_vector*, const ic3_data&,
        uint32_t, ic3_state);

ic3_state pointwise_max(const ic3_state&, const ic3_state&);

bool verify_inductive_invariant(ic3_state_vector*, const ic3_data&, uint32_t);

std::list<constrained_set> forward_expansion(const ic3_data&);

bool check_zero_one_omega(const std::list<constrained_set>&, const ic3_data&);

#endif
