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

   Copyright 2012 Johannes Kloos and Filip Niskic.
 */
#include "solver_petri_net.h"
#include "vass_state_sets.h"
#include "wsts.h"
#include "laparser.h"
#include <boost/variant.hpp>
#include <boost/foreach.hpp>
#include <cassert>
#include <vector>
#include <queue>
#include <list>

typedef std::vector<int32_t> ic3_sstate;
/* Provide helper functions to make code clearer */
ic3_sstate operator+(const ic3_state&s, const std::vector<int32_t>& delta) {
    assert(s.size() == delta.size());
    ic3_sstate res(s.size());
    for (size_t i = 0; i < s.size(); i++) {
	res[i] = ((int32_t)s[i] + delta[i]);
    }
    return res;
}

ic3_sstate operator-(const ic3_state&s, const std::vector<int32_t>& delta) {
    assert(s.size() == delta.size());
    ic3_sstate res(s.size());
    for (size_t i = 0; i < s.size(); i++) {
	res[i] = ((int32_t)s[i] - delta[i]);
    }
    return res;
}

ic3_state pointwise_max(const ic3_sstate& a, const ic3_state& b) {
    assert(a.size() == b.size());
    ic3_state res(a.size());
    for (size_t i = 0; i < a.size(); i++) {
	if (a[i] <= 0)
	    res[i] = b[i];
	else
	    res[i] = (std::max((uint32_t)a[i], b[i]));
    }
    return res;
}

ic3_state pointwise_max(const ic3_state& a, const ic3_state& b) {
    assert(a.size() == b.size());
    ic3_state res(a.size());
    for (size_t i = 0; i < a.size(); i++) {
	res[i] = (std::max(a[i], b[i]));
    }
    return res;
}

ic3_state pointwise_min(const ic3_state& a, const ic3_state& b) {
	ic3_state res(a.size());
	for (uint32_t i = 0; i < a.size(); ++i) {
		res[i] = std::min(a[i], b[i]);
	}
	return res;
}

constrained_set apply_delta(const constrained_set& a, const std::vector<int32_t>& delta) {
	constrained_set res(delta.size());
	for (uint32_t i = 0; i < delta.size(); ++i) {
		if (a.is_upper_bounded(i)) {
			uint32_t new_upper_bound = a.get_upper_bound(i) + delta[i];
			if (new_upper_bound <= 1)
				res.add_constraint(i, constraint(0, new_upper_bound));
		}
	}
	return res;
}

preimage_or_blocking_data solve_relative(ic3_state_vector* sv,
        const ic3_data& d, const timed_state& ts) {
    /* The relevant python code:
    _solve_relative(self, i, a, no_ind=False)

	Repeated in pieces:
     */

    /*
        gen_a = [0] * self.instance.n
        min_k = self.N + 1
     */
    ic3_state gen_a(d.nbr_var);
    uint32_t min_k = sv->get_N() + 1; // oo

    //  for t in self.instance.trans:
    for (std::vector<ic3_transition>::const_iterator it(d.transition.begin());
            it != d.transition.end(); it++) {
        //  b = [max(a[j] - t.d[j], t.w[j]) for j in xrange(self.instance.n)]
        ic3_state b = pointwise_max(ts.s - it->delta, it->guard);

        //  if no_ind or not self._lte(a, b):
        if (!state_le(ts.s, b)) {
            //  (k, c) = self._blocking_clause(i, b, min_k)
            opt_timed_state bc = sv->blocking_state(ts.t - 1, b, min_k);
            //  if k == None:
            if (!bc)
                //  return (None, b)
                return preimage_or_blocking_data(b);
            //  else:
            //      min_k = min(min_k, k)
            min_k = std::min(min_k, bc->t);
            //      gen_a = [max(gen_a[j], 0 if t.w[j] >= c[j] else c[j] + t.d[j]) for j in xrange(self.instance.n)]
			ic3_state c(bc->s);
            for (uint32_t j = 0; j < nbr_var; j++) {
				/* Case analysis:
				 * 1. t.w[j] >= c[j]. Then new_a[j] = 0, hence
				 *    gen_a[j] = gen_a[j] by max(x, 0) = x.
				 * 2. t.w[j] < c[j]. Then new_a[j] = c[j] + t.d[j],
				 *    so gen_a[j] = max(gen_a[j], c[j] + t.d[j])
				 */
                if (it->guard[j] < c[j] && (int32_t)c[j] + it->delta[j] > 0) {
	                gen_a[j] = std::max(gen_a[j], c[j] + it->delta[j]);
                }
            }
        }
    }
    //  if self._lte(gen_a, self.instance.init):
    //      j = next(j for j in xrange(self.instance.n) if self.instance.init[j] < a[j])
    //      gen_a[j] = self.instance.init[j] + 1
	if (!sv->is_blocked(0, gen_a)) {
		opt_timed_state state_blocking_ts = sv->blocking_state(0, ts.s);
		gen_a = pointwise_max(gen_a, state_blocking_ts->s);
	}
    min_k = (min_k < sv->get_N() ? min_k + 1 : min_k);
    assert(state_le(gen_a, ts.s));
    //  return (min_k, gen_a)
    return preimage_or_blocking_data(timed_state(min_k, gen_a));
}

opt_timed_state solve_induction(ic3_state_vector* sv, const ic3_data& d, uint32_t t, ic3_state s) {
    preimage_or_blocking_data res = solve_relative(sv, d, timed_state(t + 1, s));
    if (boost::get<ic3_state>(&res) != NULL) {
        // The \pre condition was not satisfied
        return opt_timed_state();
    }
    return opt_timed_state(boost::get<timed_state>(res));
}

preimage_or_blocking_data solve_preimage(ic3_state_vector* sv, const ic3_data& d, const timed_state& ts) {
    return solve_relative(sv, d, ts);
}

bool verify_inductive_invariant(ic3_state_vector* s, const ic3_data& d, uint32_t k) {
	debuglog << "Verifying the inductive invariant." << std::endl;
	for (uint32_t i = k; i < s->get_N() + 2; ++i) {
		const std::vector<state_activity_wrapper>& F_i(s->F(i));
		BOOST_FOREACH(const state_activity_wrapper state, F_i) {
			if (state.is_active()) {
				BOOST_FOREACH(const ic3_transition transition, d.transition) {
					const ic3_state predecessor = pointwise_max(state.get_state() - transition.delta, transition.guard);
					bool blocked = false;
					for (uint32_t j = k; j < s->get_N() + 2 && !blocked; ++j) {
						const std::vector<state_activity_wrapper>& F_j(s->F(j));
						BOOST_FOREACH(const state_activity_wrapper blocking_state, F_j) {
							if (blocking_state.is_active() && state_le(blocking_state.get_state(), predecessor)) {
								blocked = true;
								break;
							}
						}
					}
					if (!blocked) {
						debuglog << state << " has an unblocked predecessor " << predecessor << std::endl;
						return false;
					}
				}
			}
		}
	}
	return true;
}

uint32_t get_limit(const ic3_data& d) {
	uint32_t limit(0);
	for (ic3_state_set_it it(d.bad.gen.begin()); it != d.bad.gen.end(); ++it)
		for (ic3_state_it jt(it->begin()); jt != it->end(); ++jt)
			limit = std::max(limit, *jt);
	return limit;
}

bool constr_set_le(const constrained_set& a, const constrained_set& b, uint32_t n) {
	for (uint32_t i = 0; i < n; ++i)
		if (a.get_upper_bound(i) > b.get_upper_bound(i))
			return false;
	return true;
}

bool constr_set_le(const ic3_state& a, const constrained_set& b, uint32_t n) {
	for (uint32_t i = 0; i < n; ++i)
		if (a[i] > b.get_upper_bound(i))
			return false;
	return true;
}

bool check_zero_one_omega(const std::list<constrained_set>& extended_init, const ic3_data& data) {
	BOOST_FOREACH(const ic3_state bad_state, data.bad.gen) {
		BOOST_FOREACH(const constrained_set limit_set, extended_init) {
			if (constr_set_le(bad_state, limit_set, data.nbr_var))
				return false;
		}
	}
	return true;
}

constrained_set turn_into_omega(const constrained_set& set, uint32_t n) {
	constrained_set result(n);
	for (uint32_t i = 0; i < n; ++i) {
		if (set.get_upper_bound(i) <= 1)
			result.add_constraint(i, constraint(0, set.get_upper_bound(i)));
	}
	return result;
}

std::list<constrained_set> forward_expansion(const ic3_data& d) {
	std::list<constrained_set> cover;
	std::queue<constrained_set> unprocessed;

	unprocessed.push(turn_into_omega(d.init, d.nbr_var));

	while (!unprocessed.empty()) {
		const constrained_set& state(unprocessed.front());

		bool contained(false);
		for (std::list<constrained_set>::const_iterator it(cover.begin()); it != cover.end() && !contained; ++it)
			if (constr_set_le(state, *it, d.nbr_var))
				contained = true;

		if (!contained) {
			std::list<constrained_set>::iterator it(cover.begin());
			while (it != cover.end()) {
				if (constr_set_le(*it, state, d.nbr_var)) {
					std::list<constrained_set>::iterator current(it);
					++it;
					cover.erase(current);
					continue;
				}
				++it;
			}

			cover.push_back(state);

			for (std::vector<ic3_transition>::const_iterator it(d.transition.begin()); it != d.transition.end(); ++it)
				if (constr_set_le(it->guard, state, d.nbr_var))
					unprocessed.push(apply_delta(state, it->delta));
		}

		unprocessed.pop();
	}

	return cover;
}
