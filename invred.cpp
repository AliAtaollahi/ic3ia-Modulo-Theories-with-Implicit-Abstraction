/** -*- C++ -*-
 * 
 * invariant reduction
 * author: Alberto Griggio <griggio@fbk.eu>
 * 
 * This file is part of ic3ia.
 * Copyright (C) 2021 Fondazione Bruno Kessler.
 *
 * ic3ia is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * ic3ia is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with ic3ia.  If not, see <http://www.gnu.org/licenses/>.
 */

#include "invred.h"
#include "utils.h"
#include "solver.h"
#include <memory>
#include <random>


namespace ic3ia {

class InvariantReducer {
public:
    InvariantReducer(TransitionSystem &ts, const Options &opts);
    bool reduce(std::vector<TermList> &inv);

private:
    typedef std::unordered_set<size_t> IntSet;
    
    // NEC and FEAS algorithms from:
    // A. Ivrii, A. Gurfinkel, A. Belov: Small Inductive Safe Invariants,
    // FMCAD 2014
    void nec(const std::vector<TermList> &inv, const IntSet &n0, IntSet &out);
    bool feas(const std::vector<TermList> &inv0, const IntSet &n0, IntSet &out);
    bool initial(const std::vector<TermList> &inv, IntSet &out);
    
    TransitionSystem &ts_;
    const Options &opts_;
};


InvariantReducer::InvariantReducer(TransitionSystem &ts, const Options &opts):
    ts_(ts),
    opts_(opts)
{
}


bool InvariantReducer::reduce(std::vector<TermList> &inv)
{
    if (ts_.live_prop()) {
        return false;
    }

    IntSet n0;
    if (!initial(inv, n0)) {
        return false;
    }
    logger(2) << "invreduce: initial N0 size is: " << n0.size()
              << " / " << inv.size() << endlog;
    IntSet n;
    nec(inv, n0, n);
    logger(2) << "invreduce: NEC found " << n.size()
              << " necessary clauses" << endlog;
    IntSet &out = n0;
    if (!feas(inv, n, out)) {
        return false;
    }
    logger(2) << "invreduce: FEAS found " << out.size()
              << " invariant clauses" << endlog;
    size_t i, j;
    for (i = j = 0; i < inv.size(); ++i) {
        if (out.find(i) != out.end()) {
            inv[j++] = inv[i];
        }
    }
    inv.resize(j);
    return true;
}


namespace {

void mus(int seed, Solver &solver, TermSet &core)
{
    std::minstd_rand rng(seed);
    TermList assumps;

    while (true) {
        core = solver.unsat_assumptions();
        if (core.size() == 1) {
            return;
        }
        assumps.assign(core.begin(), core.end());
        shuffle(assumps, rng);
        for (auto &l : assumps) {
            solver.assume(l);
        }
        bool sat = solver.check();
        core = solver.unsat_assumptions();
        if (core.size() == assumps.size()) {
            return;
        }
    }
}

} // namespace


bool InvariantReducer::initial(const std::vector<TermList> &inv, IntSet &out)
{
    auto env = ts_.get_env();
    auto bad = msat_make_not(env, ts_.prop());

    Solver solver(env, opts_);
    auto tt = msat_make_true(env);
    solver.add(bad, tt);

    VarProvider vp(env);
    
    TermList lbls;
    for (size_t i = 0; i < inv.size(); ++i) {
        auto l = vp.fresh_var();
        lbls.push_back(l);
        solver.add_clause(inv[i], l);
        solver.assume(l);
    }
    bool sat = solver.check();

    if (sat) {
        return false;
    }

    TermSet core;
    mus(opts_.seed, solver, core);
    for (size_t i = 0; i < inv.size(); ++i) {
        if (core.find(lbls[i]) != core.end()) {
            out.insert(i);
        }
    }
    
    return true;
}


void InvariantReducer::nec(const std::vector<TermList> &inv,
                           const IntSet &n0, IntSet &out)
{
    auto env = ts_.get_env();
    Solver solver(env, opts_);
    auto tt = msat_make_true(env);

    VarProvider vp(env);

    TermList lbls;
    for (size_t i = 0; i < inv.size(); ++i) {
        if (n0.find(i) != n0.end()) {
            solver.add_clause(inv[i], tt);
        } else {
            auto a = vp.fresh_var();
            auto cls = make_or(env, inv[i]);
            auto f = msat_make_iff(env, a, cls);
            solver.add(f, tt);
            lbls.push_back(a);
        }
    }
    msat_term bound = make_atmost(env, lbls, 1, true);
    solver.add(bound, tt);
    solver.add(ts_.trans(), tt);

    IntSet &n = out;
    n.clear();
    IntSet w;
    n.insert(n0.begin(), n0.end());
    w.insert(n0.begin(), n0.end());

    TermList assumps;
    
    while (!w.empty()) {
        size_t d = *(w.begin());
        w.erase(d);
        msat_term cls = make_or(env, inv[d]);
        msat_term cls1 = ts_.next(cls);
        solver.push();
        solver.add(msat_make_not(env, cls1), tt);
        while (true) {
            for (auto a : assumps) {
                solver.assume(a);
            }
            bool sat = solver.check();
            if (!sat) {
                break;
            }
            size_t j = 0;
            for (size_t i = 0; i < inv.size(); ++i) {
                if (n0.find(i) == n0.end()) {
                    bool val = solver.model_value(lbls[j]);
                    if (!val) {
                        assumps.push_back(lbls[j]);
                        n.insert(i);
                        w.insert(i);
                        break;
                    }
                    ++j;
                }
            }
        }
        solver.pop();
    }
}


bool InvariantReducer::feas(const std::vector<TermList> &inv0,
                            const IntSet &n, IntSet &out)
{
    IntSet &inv = out;
    inv.clear();
    inv.insert(n.begin(), n.end());
    IntSet w;
    w.insert(n.begin(), n.end());

    auto env = ts_.get_env();
    Solver solver(env, opts_);
    auto tt = msat_make_true(env);

    TermList lbls;
    msat_term undef;
    MSAT_MAKE_ERROR_TERM(undef);
    VarProvider vp(env);
    
    solver.add(ts_.trans(), tt);
    for (size_t i = 0; i < inv0.size(); ++i) {
        if (inv.find(i) != inv.end()) {
            solver.add_clause(inv0[i], tt);
            lbls.push_back(undef);
        } else {
            auto l = vp.fresh_var();
            lbls.push_back(l);
            solver.add_clause(inv0[i], l);
        }
    }

    TermSet core;
    
    while (!w.empty()) {
        solver.push();
        msat_term neg_c = msat_make_false(env);
        for (size_t i = 0; i < inv0.size(); ++i) {
            if (w.find(i) != w.end()) {
                msat_term cls = make_or(env, inv0[i]);
                neg_c = msat_make_or(env, neg_c,
                                     msat_make_not(env, ts_.next(cls)));
            }
        }
        solver.add(neg_c, tt);
        for (size_t i = 0; i < inv0.size(); ++i) {
            if (inv.find(i) == inv.end()) {
                solver.assume(lbls[i]);
            }
        }
        bool sat = solver.check();
        if (sat) {
            logger(4) << "invreduce: unexpected sat result in FEAS" << endlog;
            return false;
        }
        mus(opts_.seed, solver, core);
        solver.pop();
        w.clear();
        for (size_t i = 0; i < lbls.size(); ++i) {
            if (!MSAT_ERROR_TERM(lbls[i]) && core.find(lbls[i]) != core.end()) {
                inv.insert(i);
                solver.add(lbls[i], tt);
                w.insert(i);
            }
        }
    }

    return true;
}


bool reduce_invar(TransitionSystem &ts, const Options &opts,
                  std::vector<TermList> &inv)
{
    InvariantReducer r(ts, opts);
    size_t orig = inv.size();
    if (r.reduce(inv)) {
        logger(1) << "reduced inductive invariant from " << orig << " to "
                  << inv.size() << " clauses" << endlog;
        return true;
    } else {
        logger(1) << "failed to reduce inductive invariant" << endlog;
        return false;
    }
}

} // namespace ic3ia
