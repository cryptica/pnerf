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
#ifndef IC3_STATE_SETS_H
#define IC3_STATE_SETS_H 1

#include <vector>
#include <set>
#include <list>
#include <stdint.h>
#include <iostream>
#include <exception>
#include <boost/optional.hpp>
#include <boost/unordered_set.hpp>

#include "helpers.h"

typedef std::vector<uint32_t> ic3_state;
std::ostream& operator<<(std::ostream&, const ic3_state&);

bool state_le(const ic3_state& a, const ic3_state& b);

typedef boost::unordered_set<ic3_state> ic3_state_set;
typedef ic3_state::const_iterator ic3_state_it;
typedef ic3_state_set::const_iterator ic3_state_set_it;

template<typename IT>
void write_range(std::ostream& os, 
	char start, char end, char sep, IT from, IT to) {
    if (from == to) {
	os << start << end;
    }
    char d = start;
    while (from != to) {
	os << d << ' ' << *from;
	from++;
	d = sep;
    }
    os << end;
}

template<typename T>
std::ostream& operator<<(std::ostream& os, const std::vector<T>& v) {
    write_range(os, '[', ']', ',', v.begin(), v.end());
    return os;
}

template<typename T>
std::ostream& operator<<(std::ostream& os, const std::set<T>& s) {
    write_range(os, '{', '}', ',', s.begin(), s.end());
    return os;
}

template<typename T>
std::ostream& operator<<(std::ostream& os, const std::list<T>& s) {
    write_range(os, '<', '>', ',', s.begin(), s.end());
    return os;
}

struct timed_state {
    uint32_t t;
    ic3_state s;
    timed_state(uint32_t t_, const ic3_state& s_): t(t_), s(s_) {}
    bool operator<(const timed_state& o) const {
        if (t > o.t) return true;
        if (t < o.t) return false;
	return false;
    }
};
std::ostream& operator<<(std::ostream& os, const timed_state&);

typedef boost::optional<timed_state> opt_timed_state;

class ic3_generic_state_set {
public:
    virtual void write(std::ostream& os) const {
        os << "[generic state set]";
    }
    virtual ~ic3_generic_state_set() {}
};

enum ic3_closed_set_internal_mode {
    IC3_UCI,
    IC3_LCE
};

class ic3_closed_set: public ic3_generic_state_set {
public:
    const ic3_state_set gen;
    const ic3_closed_set_internal_mode mode;
    bool operator==(const ic3_closed_set& s) {
        return (s.gen == gen) && (s.mode == mode);
    }
    void write(std::ostream& os) const;
protected:
    ic3_closed_set(const ic3_state_set& gen_,
                   ic3_closed_set_internal_mode mode_,
                   bool needs_subsumption = false);
};
std::ostream& operator<<(std::ostream& os, const ic3_closed_set&);

/** Upper closed set */
class ic3_ucs: public ic3_closed_set {
public:
    /** Upper-closed set with no generators, i.e., the empty set */
    ic3_ucs(): ic3_closed_set(ic3_state_set(), IC3_UCI) {}
    /** Upper closure of the given point */
    ic3_ucs(const ic3_state& s):
        ic3_closed_set(singleton(s), IC3_UCI) {}
    /** Upper closure of the given set of points */
    ic3_ucs(const ic3_state_set& s): ic3_closed_set(s, IC3_UCI, true) {}
    /** Copy constructor */
    ic3_ucs(const ic3_ucs& s): ic3_closed_set(s.gen, s.mode) {}
    /** Construct from subsumption-minimal set of generators.
     * disc is just used to discriminate from the upper closure
     * constructor, and can be used as a kind of checking token. */
    ic3_ucs(const ic3_state_set& s, void *disc):
        ic3_closed_set(s, IC3_UCI, false) {}
};

// Operations on closed sets
ic3_ucs add(const ic3_ucs&, const ic3_ucs&);
bool contained(const ic3_state&, const ic3_ucs&);

class constraint {
private:
	uint32_t lower_bound;
	uint32_t upper_bound;
	bool upper_bounded;
public:
	explicit constraint(uint32_t = 0);
	constraint(uint32_t, uint32_t);
	bool is_upper_bounded() const;
	uint32_t get_lower_bound() const;
	uint32_t get_upper_bound() const;
};

class constrained_set {
private:
	std::vector<constraint> constraints;
public:
	explicit constrained_set(uint32_t);
	void add_constraint(uint32_t, const constraint &);
	bool is_consistent() const;
	bool is_upward_closed() const;
	uint32_t get_lower_bound(uint32_t) const;
	uint32_t get_upper_bound(uint32_t) const;
	bool is_upper_bounded(uint32_t) const;
	ic3_state get_minor() const;
	std::ostream& print(std::ostream& os) const;
};

std::ostream& operator<<(std::ostream& os, const constrained_set& set);

class state_activity_wrapper {
private:
	ic3_state state;
	bool active;
public:
	explicit state_activity_wrapper(const ic3_state& _state);
	ic3_state& get_state();
	const ic3_state& get_state() const;
	bool is_active() const;
	void inactivate();
	state_activity_wrapper active_copy() const;
};


std::vector<state_activity_wrapper> downward_closure(uint32_t nbr_var, const constrained_set& s);
#endif
