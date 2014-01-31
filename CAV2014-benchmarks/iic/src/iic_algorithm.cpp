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
#include "vass_state_sets.h"
#include "wsts.h"
#include "solver_petri_net.h"
#include "helpers.h"
#include "parallelization.h"
#include <queue>
#include <list>
#include <exception>
#include <boost/variant.hpp>

ic3_state_vector *initialize(const ic3_data& d) {
	return new ic3_state_vector(d);
}

class invalid_exception {
	/* we could store the backtrace in here */
};

void enqueue_or_invalid(std::priority_queue<timed_state>& q, const ic3_data& d, uint32_t t, ic3_state s) {
	debuglog<< "Trying to enqueue " << s << " at " << t << std::endl;
	/* ModelSyn */
	if (t == 0) {
		debuglog << "MODELSYN" << std::endl;
		throw invalid_exception();
	}
	/* ModelSem */
	bool is_initial = true;
	for (uint32_t i = 0; i < d.nbr_var && is_initial; ++i) {
		if (!d.init.is_upper_bounded(i) || s[i] > d.init.get_upper_bound(i))
		is_initial = false;
	}
	if (is_initial) {
		debuglog << "Initial state found: " << s << std::endl;
		throw invalid_exception();
	}
	/* Decide/Candidate - queue manipulation part */
	q.push(timed_state(t, s));
}

void inner_loop(ic3_state_vector *sv, const ic3_data& d, ic3_state s) {
	std::priority_queue<timed_state> q;
	enqueue_or_invalid(q, d, sv->get_N(), s);
	while (!q.empty()) {
		if (forward_search_zero_one_omega_done)
			return;
		timed_state a(q.top());
		q.pop();

		/* Filip: I've added the check. It sometimes introduces
		 * a considerable slow-down, but I'm not sure the code
		 * is correct without it.
		 */
		if (sv->is_blocked(a.t, a.s)) {
			debuglog<< "Already blocked, ignoring: " << a << std::endl;
			continue;
		}

		/* Since we're here, q is non-empty, and by
		 * construction, we know that no queue entry
		 * satisfies ModelSyn or ModelSem. Thus,
		 * check if we can apply Decide, and otherwise,
		 * do Conflict.
		 */
		debuglog<< "Getting pre-image for " << a << std::endl;
		preimage_or_blocking_data res = solve_preimage(sv, d, a);
		ic3_state *p;
		if ((p = boost::get<ic3_state>(&res)) != NULL) {
			/* Decide */
			debuglog<< "DECIDE" << std::endl;
			debuglog << "Pre-image: " << *p << std::endl;
			q.push(a); // re-add
			assert(a.t > 0);
			enqueue_or_invalid(q, d, a.t - 1, *p);
		} else {
			/* Conflict */
			debuglog << "CONFLICT" << std::endl;
			timed_state b = boost::get<timed_state>(res);

			/* Trying to improve the returned generalization. */
			while (b.t < sv->get_N()) {
				preimage_or_blocking_data better_res = solve_preimage(sv, d, timed_state(b.t + 1, b.s));
				timed_state *new_b = boost::get<timed_state>(&better_res);
				if (new_b != NULL) {
					b = *new_b;
				} else {
					break;
				}
			}

			debuglog << "Blocking " << b << std::endl;
			sv->block(b.t, b.s);

			/* Also, re-add element for prolonged search if time < N */
			if (b.t < sv->get_N())
			enqueue_or_invalid(q, d, b.t + 1, a.s);
		}
	}
	debuglog<< "Inner loop done" << std::endl;
}

static void print_F(const ic3_state_vector* s) {
	debuglog<< "Vector F:" << std::endl;
	for (size_t i = 0; i <= s->get_N() + 1; i++) {
		debuglog << s->F(i) << std::endl;
	}
}

bool forward_search_zero_one_omega_done = false;
bool forward_search_zero_one_omega_result;
bool forward_search_done = false;

void ic3_check_zero_one_omega(const ic3_data& d) {
	forward_search_zero_one_omega_result = false;
	std::list<constrained_set> expanded_init(forward_expansion(d));

	debuglog<< "Expanded init: " << expanded_init << std::endl;

	debuglog<< "Zero-one-omega test: " << std::endl;
	if (check_zero_one_omega(expanded_init, d)) {
		debuglog<< "Zero-one-omega valid!" << std::endl;
		forward_search_zero_one_omega_result = true;
		forward_search_zero_one_omega_done = true;
	}
}

// returns true if Cover <= P.
bool ic3_check(const ic3_data& d) {
	// spawn_zero_one_omega(d);

	debuglog<< "INITIALIZE" << std::endl;
	ic3_state_vector *s = initialize(d);
	for (;;) {
		for (ic3_state_set_it c(d.bad.gen.begin()); c != d.bad.gen.end(); c++) {
			debuglog<< "Considering " << *c <<std::endl;
			// Is the next candidate already blocked?
			if (s->is_blocked(s->get_N(), *c)) {
				debuglog << "Skipped, already blocked." << std::endl;
				continue;
			}
			debuglog << "CANDIDATE: " << *c << std::endl;
			/* Candidate */
			try {
				inner_loop(s, d, *c);
			} catch (invalid_exception& e) {
				debuglog << "Got Invalid" << std::endl;
				delete s;
				return false;
			}
			if (forward_search_done) {
				if (forward_search_zero_one_omega_done) {
					debuglog << "Got result from 0-1-w" <<std::endl;;
					delete s;
					return forward_search_zero_one_omega_result;
				} else {
					std::cerr << "01w done" <<std::endl;
					forward_search_done = false;
				}
			}
			print_F(s);
		}

		s->unfold();
		debuglog << "UNFOLD" << std::endl;

		/* Induction */
		debuglog << "INDUCTION" << std::endl;
		bool invariant_found = false;
		uint32_t invariant_index = 0;
		for (uint32_t i = 1; i < s->get_N(); i++) {
			const std::vector<state_activity_wrapper>& F(s->F(i));
			debuglog << "  layer " << i << std::endl;
			debuglog << "  to consider: " << F << std::endl;
			for (std::vector<state_activity_wrapper>::const_iterator it(F.begin()); it != F.end(); ++it)
			if (it->is_active()) {
				debuglog << "Considering " << *it << std::endl;
				boost::optional<timed_state> gen = solve_induction(s, d, i, it->get_state());
				if (gen) {
					debuglog << gen->t << std::endl;
					s->block(gen->t, gen->s, false);
				}
			}
			if (!s->has_active(i)) {
				debuglog << "VALID" << std::endl;
				/*if (verify_inductive_invariant(s, d, i)) {
					debuglog << "Inductive invariant confirmed." << std::endl;
				} else {
					debuglog << "Bogus inductive invariant!" << std::endl;
				}*/
				/* Valid */
				invariant_found = true;
				invariant_index = i;
			}
		}

		if (invariant_found) {
			s->print_invariant(invariant_index, d.var_names);
			delete s;
			return true;
		}

		debuglog << "valid did not apply" << std::endl;
		if (forward_search_zero_one_omega_done) {
			debuglog << "Got result from 0-1-w" <<std::endl;;
			delete s;
			return forward_search_zero_one_omega_result;
		}
		s->purge_inactive_all();
	}

	// Should never be reached.
	return false;
}
