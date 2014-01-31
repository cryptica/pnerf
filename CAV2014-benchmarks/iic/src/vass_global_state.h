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
#ifndef IC3_GLOBAL_STATE_H
#define IC3_GLOBAL_STATE_H 1

#include <iostream>
#include <vector>
#include <list>
#include "wsts.h"
#include "vass_state_sets.h"

std::ostream& operator<<(std::ostream&, const state_activity_wrapper&);

/* In constrast to all other IC3 data structures,
 * this data structure represents global state and is hence
 * mutable.
 */
class ic3_state_vector {
private:
    std::vector<std::vector<state_activity_wrapper> > F_latest;
public:
    /* Initialization */
    explicit ic3_state_vector(const ic3_data& data);
    /* Accessor for the state vector */
    //ic3_lcs R(uint32_t index) const;
    std::vector<state_activity_wrapper> F(uint32_t index) const;
    /* The possible modifications of the state vector */
    // Unfold: Add another element to the state vector
    void unfold();
    // Block: Block the upper closure of a point
    void block(uint32_t t, const ic3_state& x, bool purge_immediately = true);
    opt_timed_state blocking_state(uint32_t t, const ic3_state& x, uint32_t hint = 0) const;
    bool is_blocked(uint32_t t, const ic3_state& x) const;
    // Get N
    uint32_t get_N() const {
        return F_latest.size() - 2;
    }
    // Check if time is infinity
    bool is_infinite(uint32_t t) const {
        return t > get_N();
    }
    void purge_inactive(uint32_t t);
    void purge_inactive_all();
    bool has_active(uint32_t t) const;
    void print_invariant(uint32_t, const std::vector<std::string>&) const;
private:
    opt_timed_state blocking_state_at(uint32_t t, const ic3_state& x) const;
};

#endif
