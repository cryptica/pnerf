// vim:sw=4
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

   Copyright 2003, 2004, Pierre Ganty, Anthony Piron

   Introduced into IC3WSTS by Johannes Kloos
   Copyright 2012 Johannes Kloos
 */

#include "error.h"
#include "xmalloc.h"
#include "tbsymbol.h"
#include "laparser.h"
#include "wsts.h"
#include "exceptions.h"
#include <cassert>
#include <boost/optional.hpp>
#include <boost/variant.hpp>
#include <boost/unordered_set.hpp>
#include <map>
#include <utility>

ic3_ucs *bad;
constrained_set *init;
std::vector<ic3_transition> transitions;

static constrained_set collect_multiple_constraints(T_PTR_tree entry);
static std::pair<uint32_t, constraint> collect_one_constraint(T_PTR_tree entry);
static ic3_ucs goalscode_produce(T_PTR_tree entry);
static constrained_set initcode_produce(T_PTR_tree entry);
static std::vector<ic3_transition> rulescode_produce(T_PTR_tree entry);

static void callback_tree_before(T_PTR_tree entry) {
    char* info = (char*) tree_getinfo(entry);
    if (strcmp(info, "rules") == 0) {
        tree_brk_branch(entry);
        /* nbr_rules will be fill at this point */
        transitions = rulescode_produce(entry);
    } else if (strcmp(info, "init") == 0) {
        tree_brk_branch(entry);
        init = new constrained_set(initcode_produce(tree_subtree(entry, 0)));
    } else if (strcmp(info, "target") == 0) {
        tree_brk_branch(entry);
        /* system is a OUT parameter */
        bad = new ic3_ucs(goalscode_produce(tree_subtree(entry, 0)));
    } else if (strcmp(info,"invariants") == 0) {
        tree_brk_branch(entry);
        /* system and init are IN/OUT parameters */
        // ignore
        //invariantscode_produce(tree_subtree(entry,0), _system, _init);
    }
}

ic3_data build_problem_instance(T_PTR_tree atree, const std::vector<std::string>& var_names) {
    tree_dump(atree, callback_tree_before, NULL, NULL);
    assert(bad);
    assert(init);
    ic3_data result(nbr_var, *bad, *init, transitions, var_names);
    delete bad;
    delete init;
    return result;
}

static ic3_ucs goalscode_produce(T_PTR_tree entry) {
	if (entry) {
		char* info = (char*) tree_getinfo(entry);
		boost::unordered_set<ic3_state> minors;
		if (strcmp(info, "or") == 0) {
			for (size_t i = 0; i < tree_nbrsubtrees(entry); i++) {
				constrained_set s = collect_multiple_constraints(tree_subtree(entry, i));
				if (s.is_upward_closed())
					minors.insert(s.get_minor());
				else
					throw parse_exception(parse_exception::TARGET_NOT_UPWARD_CLOSED);
			}
		} else if (strcmp(info, "and") == 0) {
			constrained_set s = collect_multiple_constraints(entry);
			if (s.is_upward_closed())
				minors.insert(s.get_minor());
			else
				throw parse_exception(parse_exception::TARGET_NOT_UPWARD_CLOSED);
		}
		return ic3_ucs(minors);
	}
	return ic3_ucs();
}

static constrained_set collect_multiple_constraints(T_PTR_tree entry) {
    constrained_set result(nbr_var);
    if (entry) {
    	for (uint32_t i = 0; i < tree_nbrsubtrees(entry); i++) {
        	T_PTR_tree subtree = tree_subtree(entry, i);
        	if (subtree && tree_nbrsubtrees(subtree)) {
        		std::pair<uint32_t, constraint> pair = collect_one_constraint(subtree);
        		result.add_constraint(pair.first, pair.second);
        	}
        }
    }
    return result;
}

static std::pair<uint32_t, constraint> collect_one_constraint(T_PTR_tree entry) {
	T_PTR_tbsymbol_info infoid, infonb_left, infonb_right;
	char *info = (char *) tree_getinfo(entry);
	infoid = static_cast<T_PTR_tbsymbol_info>(tbsymbol_getinfo(static_cast<T_PTR_tbsymbol_entry>(tree_getinfo(tree_subtree(entry, 0)))));
	infonb_left = static_cast<T_PTR_tbsymbol_info>(tbsymbol_getinfo(static_cast<T_PTR_tbsymbol_entry>(tree_getinfo(tree_subtree(entry, 1)))));
	if (strcmp(info, "=") == 0) {
		return std::make_pair(infoid->info.id.addr, constraint(infonb_left->info.nb.value, infonb_left->info.nb.value));
	} else if (strcmp(info, ">=") == 0) {
		return std::make_pair(infoid->info.id.addr, constraint(infonb_left->info.nb.value));
	} else { //if (strcmp(info, "in") == 0) {
		infonb_right = static_cast<T_PTR_tbsymbol_info>(tbsymbol_getinfo(static_cast<T_PTR_tbsymbol_entry>(tree_getinfo(tree_subtree(entry, 2)))));
		return std::make_pair(infoid->info.id.addr, constraint(infonb_left->info.nb.value, infonb_right->info.nb.value));
	}
}

static constrained_set initcode_produce(T_PTR_tree entry) {
	constrained_set init_set = collect_multiple_constraints(entry);
	if (!init_set.is_consistent())
		throw parse_exception(parse_exception::INCONSISTENT_INITIAL_CONDITION);
	return init_set;
}

typedef boost::variant<ic3_state, std::vector<int32_t> > guard_or_cmd;
static boost::optional<ic3_transition> rule(T_PTR_tree entry);
static guard_or_cmd guardedcmd(T_PTR_tree entry);
static void cmd(T_PTR_tree entry, std::map<uint32_t, int32_t>& trans);
static int32_t cmdrhs(T_PTR_tree entry, T_PTR_tbsymbol_info infoid,
                      bool& messyspec, bool& istransfer);

static std::vector<ic3_transition>
rulescode_produce(T_PTR_tree entry) {
    size_t nbr_rules, i;
    std::vector<ic3_transition> res;

    if (entry) {
        nbr_rules = tree_nbrsubtrees(entry);
        for (i = 0 ; i < nbr_rules ; i++) {
            boost::optional<ic3_transition> t = rule(tree_subtree(entry, i));
            if (t) res.push_back(*t);
        }
    }
    return res;
}

static boost::optional<ic3_transition>
rule(T_PTR_tree entry) {
    char* info;

    if (entry) {
        info = (char*) tree_getinfo(entry);
        if (strcmp(info,"guardedcmd") == 0) {
            guard_or_cmd gc1 = guardedcmd(tree_subtree(entry,0));
            guard_or_cmd gc2 = guardedcmd(tree_subtree(entry,1));
            if (boost::get<ic3_state>(&gc1)
                    && boost::get<std::vector<int32_t> >(&gc2)) {
                return boost::optional<ic3_transition>(
                           ic3_transition(boost::get<ic3_state>(gc1),
                                          boost::get<std::vector<int32_t> >(gc2)));
            }
        }
    }
    return boost::optional<ic3_transition>();
}

static guard_or_cmd
guardedcmd(T_PTR_tree entry) {
    size_t i;
    char* info;
    if (entry) {
        info = (char*) tree_getinfo(entry);
        if (strcmp(info,"guard") == 0) {
            constrained_set s = collect_multiple_constraints(entry);
            if (s.is_upward_closed())
                return guard_or_cmd(s.get_minor());
            else
            	throw parse_exception(parse_exception::GUARD_NOT_UPWARD_CLOSED);
        } else if (strcmp(info,"statement") == 0) {
            /* It's a new transition, possibly with transfers */
            std::map<uint32_t, int32_t> trans;
            for (i = 0 ; i < tree_nbrsubtrees(entry) ; i++)
                cmd(tree_subtree(entry, i), trans);
            std::vector<int32_t> res;
            for (i = 0; i < nbr_var; i++) {
                res.push_back(trans[i]);
            }
            return guard_or_cmd(res);
        }
    }
    return guard_or_cmd(ic3_state());
}

static void cmd(T_PTR_tree entry, std::map<uint32_t, int32_t>& trans) {
    T_PTR_tbsymbol_info infoid;
    T_PTR_tree rhs;
    bool messy_spec, istransfer;

    if (entry) {
        infoid = static_cast<T_PTR_tbsymbol_info>(tbsymbol_getinfo(
                     static_cast<T_PTR_tbsymbol_entry>(tree_getinfo(
                                 tree_subtree(entry, 0)))));
        rhs = tree_subtree(entry, 1);
        /* We assume that cmd is not a transfer */
        istransfer = false;
        /* We assume the user does not know how to write specification */
        messy_spec = true;
        /* For instance X' = c s.t. c > 0 is a messy_spec
         * we must check for it. If we meet a var in RHS or RHS = 0
         * then messy_spec = false.
         */
        trans[infoid->info.id.addr] = cmdrhs(rhs, infoid, messy_spec, istransfer);
        if (messy_spec == true)
            err_quit("\nCannot handle transition\n");
#if 0
        // We don't handle transfers ATM
        if (istransfer == true) {
            /* We are ready for a new transfer, pay attention to the ++ */
            sys->transition[nbrcmd].transfers[nbrtransfers].target =
                infoid->info.id.addr;
            sys->transition[nbrcmd].nbr_transfers = ++nbrtransfers;
            istransfer = false;

        }
#endif

    }
}

static int32_t
cmdrhs(T_PTR_tree entry, T_PTR_tbsymbol_info infoid, bool& messyspec,
       bool& istransfer) {
    T_PTR_tree lhs, rhs;
    T_PTR_tbsymbol_info entry_info;
    char* entry_info_char;

    if (entry) {
        if (tree_nbrsubtrees(entry)) {

            entry_info_char = (char*) tree_getinfo(entry);

            lhs = tree_subtree(entry, 0);
            rhs = tree_subtree(entry, 1);

            if (strcmp(entry_info_char,"+") == 0) {
                return cmdrhs(lhs, infoid, messyspec, istransfer)
                       + cmdrhs(rhs, infoid, messyspec, istransfer);
            } else if (strcmp(entry_info_char,"-") == 0) {
                return cmdrhs(lhs, infoid, messyspec, istransfer)
                       - cmdrhs(rhs, infoid, messyspec, istransfer);
            }
        } else { /* Leaf */
            entry_info = static_cast<T_PTR_tbsymbol_info>(
                             tbsymbol_getinfo(
                                 static_cast<T_PTR_tbsymbol_entry>(tree_getinfo(entry))));

            if (entry_info->tag == tbsymbol_INFO_ID) {
                /* At least one variable occurs in the cmd RHS */
                messyspec = false;
                if (entry_info != infoid) {
                    /* It is a transfer */
                    // We do not currently handle transfer Petri nets
                    err_quit("Transfers are not supported");
                }
                return 0;
            } else if (entry_info->tag == tbsymbol_INFO_NB) {
                return entry_info->info.nb.value;
#if 0
                // This check allows reset nets; we de not currently
                // handle them, so consider them messy.
                if (entry_info->info.nb.value == 0)
                    messy_spec = false;
#endif
            } else
                err_quit("Unrecognized tbsymbol entry\n");
        }
    }
    return 0;
}
