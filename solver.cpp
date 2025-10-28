/** -*- C++ -*-
 * 
 * SMT solver interface for IC3
 * author: Alberto Griggio <griggio@fbk.eu>
 * 
 * This file is part of ic3ia.
 * Copyright (C) 2015-2016 Fondazione Bruno Kessler.
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

#include "solver.h"

namespace ic3ia {


Solver::Solver(msat_env env, const Options &opts):
    parent_env_(env),
    is_approx_(opts.solver_approx),
    trace_(opts.trace)
{
    create_env();
}


Solver::~Solver()
{
    if (!MSAT_ERROR_ENV(env_)) {
        msat_destroy_env(env_);
    }
}


void Solver::create_env()
{
    msat_config cfg = get_config(FULL_MODEL, false, is_approx_);
    if (!trace_.empty()) {
        auto name = trace_ + (is_approx_ ? ".approx" : "") + ".main.smt2";
        msat_set_option(cfg, "debug.api_call_trace", "1");
        msat_set_option(cfg, "debug.api_call_trace_filename", name.c_str());
    }
    env_ = msat_create_shared_env(cfg, parent_env_);
    msat_destroy_config(cfg);
}


void Solver::reset(bool precise)
{
    if (!precise || !is_approx_) {
        msat_reset_env(env_);
    } else {
        msat_destroy_env(env_);
        is_approx_ = false;
        create_env();
    }
}


void Solver::add(msat_term formula, msat_term label)
{
    msat_assert_formula(env_, msat_make_or(env_, msat_make_not(env_, label),
                                           formula));
}


void Solver::add_clause(const TermList &clause, msat_term label)
{
    msat_term f = msat_make_not(env_, label);
    for (msat_term t : clause) {
        f = msat_make_or(env_, f, t);
    }
    msat_assert_formula(env_, f);
}


void Solver::push()
{
    msat_push_backtrack_point(env_);
}


void Solver::pop()
{
    msat_pop_backtrack_point(env_);
}


void Solver::add_cube_as_clause(const TermList &cube, msat_term label)
{
    msat_term c = msat_make_false(env_);
    for (msat_term t : cube) {
        c = msat_make_or(env_, c, msat_make_not(env_, t));
    }
    if (!MSAT_ERROR_TERM(label)) {
        c = msat_make_or(env_, msat_make_not(env_, label), c);
    }
    msat_assert_formula(env_, c);
}


void Solver::add_cube_as_clause(const TermList &cube)
{
    msat_term label;
    MSAT_MAKE_ERROR_TERM(label);
    add_cube_as_clause(cube, label);
}


void Solver::assume(msat_term a)
{
    a_.push_back(a);
}


static inline std::string msat_smt2_term_safe(msat_env e, msat_term t) {
    if (MSAT_ERROR_TERM(t)) return std::string("<?>");
    char *c = msat_to_smtlib2_term(e, t);  // must free via msat_free()
    if (!c) return std::string("<print-error>");
    std::string s(c);
    msat_free(c);
    return s;
}

// ... inside namespace ic3ia ... (your Solver method)
bool Solver::check()
{
    uc_.clear();

    // ---- DEBUG: log everything passed to msat_solve_with_assumptions ----
    {
        logger(2) << "[solve] msat_solve_with_assumptions BEGIN" << endlog;

        // msat_env is a wrapper struct; print its internal pointer
        logger(3) << "[solve]   env.repr=" << env_.repr << endlog;  // FIX

        const size_t n = a_.size();
        logger(3) << "[solve]   assumptions.count = " << n << endlog;

        for (size_t i = 0; i < n; ++i) {
            msat_term ai = a_[i];
            logger(3) << "[solve]     A[" << i << "] term_id=" << msat_term_id(ai)
                      << "  " << msat_smt2_term_safe(env_, ai) << endlog;
        }

        if (n == 0) {
            logger(4) << "[solve]   (passing nullptr, 0)" << endlog;
        } else {
            // (optional) show the raw pointer & count we pass
            msat_term *ptr = &a_[0];
            logger(4) << "[solve]   ptr=" << static_cast<const void*>(ptr)
                      << "  size=" << n << endlog;
        }
    }
    // --------------------------------------------------------------------

    // IMPORTANT: avoid UB when a_ is empty; pass nullptr with count 0
    msat_term *ptr = a_.empty() ? nullptr : &a_[0];

    // MathSAT call (this creates/uses the current model on env_) 
    // API: msat_result msat_solve_with_assumptions(msat_env, msat_term*, size_t)
    msat_result res = msat_solve_with_assumptions(env_, ptr, a_.size());  // :contentReference[oaicite:1]{index=1}

    logger(2) << "[solve]   result = "
              << (res == MSAT_SAT ? "MSAT_SAT"
                  : res == MSAT_UNSAT ? "MSAT_UNSAT"
                  : "MSAT_UNKNOWN")
              << endlog;
    logger(2) << "[solve] msat_solve_with_assumptions END" << endlog;

    assert(res != MSAT_UNKNOWN);
    a_.clear();
    return (res == MSAT_SAT);
}


const TermSet &Solver::unsat_assumptions()
{
    if (uc_.empty()) {
        size_t sz;
        msat_term *u = msat_get_unsat_assumptions(env_, &sz);
        assert(u);
        for (size_t i = 0; i < sz; ++i) {
            msat_term l = u[i];
            uc_.insert(l);
            logger(4) << "unsat assumption: " << logterm(env_, l) << endlog;
        }
        msat_free(u);
    }
    return uc_;
}


bool Solver::model_value(msat_term pred)
{
    msat_term v = msat_get_model_value(env_, pred);
    switch (msat_decl_get_tag(env_, msat_term_get_decl(v))) {
    case MSAT_TAG_TRUE:
        return true;
        break;
    case MSAT_TAG_FALSE:
        return false;
        break;
    default:
        return false; // pick a random assignment
    }
}


} // namespace ic3ia
