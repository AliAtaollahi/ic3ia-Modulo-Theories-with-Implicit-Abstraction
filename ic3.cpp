/** -*- C++ -*-
 * 
 * IC3 with implicit abstraction
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

#include "ic3.h"
#include <sstream>
#include <iomanip>
#include <algorithm>
#include <vector>
#include <sstream>
#include <string>

namespace ic3ia {

IC3::IC3(TransitionSystem &ts, const Options &opts, LiveEncoder &l2s):
    ts_(ts),
    opts_(opts),
    vp_(ts.get_env()),
    rng_(opts.seed),
    solver_(ts.get_env(), opts),
    abs_(ts, opts),
    ref_(ts, opts, abs_),
    l2s_(l2s),
    liveref_(ts, opts, abs_, l2s_),
    cb_(nullptr)
{
    init_label_ = make_label("init");
    trans_label_ = make_label("trans");
    bad_label_ = make_label("bad");
    wit_loopback_ = CEX_NO_LOOP;

    last_reset_calls_ = 0;
    try_gen_pre_ = opts_.generalize_pre;
    
    num_solve_calls_ = 0;
    num_solve_sat_calls_ = 0;
    num_solve_unsat_calls_ = 0;
    num_solver_reset_ = 0;
    num_added_cubes_ = 0;
    num_subsumed_cubes_ = 0;
    num_block_ = 0;
    num_generalize_pre_ = 0;
    num_refinements_ = 0;
    num_predicates_ = 0;
    num_liveness_refinements_ = 0;
    num_liveness_predicates_ = 0;
    num_liveness_rankrels_ = 0;
    max_cube_size_ = 0;
    avg_cube_size_ = 0;
    solve_time_ = 0;
    solve_sat_time_ = 0;
    solve_unsat_time_ = 0;
    block_time_ = 0;
    generalize_and_push_time_ = 0;
    generalize_pre_time_ = 0;
    rec_block_time_ = 0;
    propagate_time_ = 0;
    refinement_time_ = 0;
    liveness_refinement_time_ = 0;
    prove_time_ = 0;
}


//-----------------------------------------------------------------------------
// public methods
//-----------------------------------------------------------------------------

void IC3::set_search_bound_callback(SearchBoundCallback *cb)
{
    cb_ = cb;
}


void IC3::set_initial_predicates(const TermList &preds)
{
    preds_.insert(preds.begin(), preds.end());
}


msat_truth_value IC3::prove()
{
    int outer_iteration = 0;
    int inner_iteration = 0;
    TimeKeeper t(prove_time_);
    initialize();
    if (!check_init()) {
        return MSAT_FALSE;
    }
    if (cb_ && !(*cb_)(0)) {
        return MSAT_UNDEF;
    }


    while (true) {
        Cube bad;
        logger(1) << "=======================\n\touter_iteration "
            << outer_iteration
            <<"\n=======================\n";
        outer_iteration++;
        inner_iteration = 0;
        while (get_bad(bad)) {
            logger(1) << "=======================\n\tinner_iteration "
                << inner_iteration
                <<"\n=======================\n";
            inner_iteration++;
            logger(1) << "==> before msat_truth_value s = rec_block(bad);" << endlog;
            msat_truth_value s = rec_block(bad);
            logger(1) << "==> after msat_truth_value s = rec_block(bad);" << endlog;
            if (s == MSAT_FALSE) {
                logger(1) << "found counterexample at depth " << depth()
                          << endlog;
                return s;
            } else if (s == MSAT_UNDEF) {
                logger(1) << "unknown result at depth " << depth()
                          << endlog;
                return s;
            }
        }
        logger(1) << "==> before new_frame();" << endlog;
        new_frame();
        logger(1) << "==> after new_frame();" << endlog;
        logger(1) << "==> before if (propagate())" << endlog;
        if (propagate()) {
            return MSAT_TRUE;
        }
        logger(1) << "==> after if (propagate())" << endlog;
        if (cb_ && !(*cb_)(depth())) {
            return MSAT_UNDEF;
        }
    }
}


int IC3::witness(std::vector<TermList> &out)
{
    if (!wit_.empty()) {
        std::swap(wit_, out);
        return wit_loopback_;
    }
    return CEX_ERROR;
}


void IC3::print_stats(std::ostream &out) const
{
#define print_stat(n)                        \
    out << #n << " = " << std::setprecision(3) << std::fixed       \
        << n ## _ << "\n"

    print_stat(num_solve_calls);
    print_stat(num_solve_sat_calls);
    print_stat(num_solve_unsat_calls);
    print_stat(num_solver_reset);
    print_stat(num_added_cubes);
    print_stat(num_subsumed_cubes);
    print_stat(num_block);
    if (opts_.generalize_pre) {
        print_stat(num_generalize_pre);
    }
    print_stat(num_refinements);
    print_stat(num_predicates);
    if (ts_.live_prop()) {
        print_stat(num_liveness_refinements);
        print_stat(num_liveness_predicates);
        print_stat(num_liveness_rankrels);
    }
    print_stat(max_cube_size);
    print_stat(avg_cube_size);
    print_stat(solve_time);
    print_stat(solve_sat_time);
    print_stat(solve_unsat_time);
    print_stat(block_time);
    print_stat(generalize_and_push_time);
    if (opts_.generalize_pre) {
        print_stat(generalize_pre_time);
    }
    print_stat(rec_block_time);
    print_stat(propagate_time);
    print_stat(refinement_time);
    if (ts_.live_prop()) {
        print_stat(liveness_refinement_time);
    }
    print_stat(prove_time);
}


//-----------------------------------------------------------------------------
// major methods
//-----------------------------------------------------------------------------


bool IC3::check_init()
{
    TimeKeeper t(solve_time_);

    activate_frame(0); // frame_[0] is init
    activate_bad();
    
    bool sat = solve();

    if (sat && solver_.is_approx()) {
        logger(2) << "possible counterexample found at depth 0, "
                  << "setting solver to precise" << endlog;
        solver_.reset(true);
        reset_solver();
        activate_frame(0);
        activate_bad();
        sat = solve();
    }

    if (sat) {
        wit_.push_back(TermList());
        // this is a bit more abstract than it could...
        get_cube_from_model(wit_.back());
        concretize(wit_.back());
        wit_loopback_ = CEX_NO_LOOP;
    }
    
    return !sat;
}


bool IC3::get_bad(Cube &out)
{
    try_gen_pre_ = opts_.generalize_pre;
    activate_frame(depth());
    activate_bad();

    if (solve()) {
        get_cube_from_model(out);
        generalize_bad(out);

        logger(3) << "got bad cube of size " << out.size()
                  << ": ";
        logcube(4, out);
        logger(3) << endlog;

        return true;
    } else {
        return false;
    }
}


inline void IC3::generalize_bad(Cube &c)
{
    for (msat_term l : c) {
        solver_.assume(l);
    }
    solver_.push();
    msat_term prop = ts_.live_prop() ? l2s_.prop() : ts_.prop();
    solver_.add(prop, msat_make_true(ts_.get_env()));
    bool sat = solve();
    if (!sat) {
        const TermSet &core = solver_.unsat_assumptions();
        auto it = std::remove_if(c.begin(), c.end(),
                                 [&core](msat_term l)
                                 { return core.find(l) == core.end(); });
        c.resize(it - c.begin());
    }
    solver_.pop();
}

msat_truth_value IC3::rec_block(const Cube &bad)
{
    TimeKeeper t(rec_block_time_);

    auto tv2str = [](msat_truth_value s) {
        switch (s) { case MSAT_TRUE: return "MSAT_TRUE";
                     case MSAT_FALSE: return "MSAT_FALSE";
                     default: return "MSAT_UNDEF"; }
    };
    auto chain_len = [](const ProofObligation *p) {
        size_t n = 0; while (p) { ++n; p = p->next; } return n;
    };
    auto syntactic_blocking_frame = [&](const Cube &c, unsigned int from_idx)->int {
        for (size_t i = from_idx; i < frames_.size(); ++i) {
            Frame &f = frames_[i];
            for (size_t j = 0; j < f.size(); ++j) {
                if (subsumes(f[j], c)) return static_cast<int>(i);
            }
        }
        return -1;
    };

    logger(2) << "[rec_block] start: depth=" << depth()
              << "  bad.size=" << bad.size() << endlog;

    ProofQueue queue;
    queue.push_new(bad, depth());
    size_t qsize_est = 1;

    while (!queue.empty()) {
        // Full queue dump (top..bottom), like the Python logger
        if (get_verbosity() >= 4) {
            auto snap = queue.snapshot();
            logger(4) << "[rec_block] queue dump (top..bottom)"
                      << "  size_est=" << qsize_est
                      << "  real_size=" << snap.size() << endlog;
            for (size_t i = 0; i < snap.size(); ++i) {
                const ProofObligation *qpo = snap[i];
                logger(4) << "  [" << i << "]"
                          << " idx=" << qpo->idx
                          << " cube_size=" << qpo->cube.size()
                          << " chain_len=" << chain_len(qpo)
                          << "  cube=";
                logcube(4, qpo->cube);
                logger(4) << endlog;
            }
        }

        // periodic solver reset (unchanged)
        if (opts_.solver_reset_interval &&
            num_solve_calls_ - last_reset_calls_ > opts_.solver_reset_interval) {
            logger(3) << "[rec_block] solver reset threshold hit: "
                      << "num_solve_calls=" << num_solve_calls_
                      << " last_reset_calls=" << last_reset_calls_
                      << " interval=" << opts_.solver_reset_interval << endlog;
            reset_solver();
        }

        ProofObligation *p = queue.top();
        logger(3) << "[rec_block] queue_top  size_est=" << qsize_est
                  << "  idx=" << p->idx
                  << "  cube_size=" << p->cube.size()
                  << "  chain_len=" << chain_len(p)
                  << "  cube=";
        logcube(4, p->cube);
        logger(3) << endlog;

        if (p->idx == 0) {
            std::vector<TermList> cex;
            for (const ProofObligation *q = p; q; q = q->next) cex.push_back(q->cube);

            logger(2) << "[rec_block] reached frame 0; "
                      << "candidate CEX length=" << cex.size() << endlog;
            if (get_verbosity() >= 4) {
                for (size_t i = 0; i < cex.size(); ++i) {
                    logger(4) << "  cex[" << i << "] = ";
                    logcube(4, cex[i]);
                    logger(4) << endlog;
                }
            }

            msat_truth_value s = refine_abstraction(cex);
            logger(2) << "[rec_block] refine_abstraction result = "
                      << tv2str(s) << endlog;

            if (s == MSAT_TRUE) {
                while (!queue.empty()) queue.pop();
                qsize_est = 0;
                if (get_verbosity() >= 4) {
                    logger(4) << "[rec_block] queue dump (after refine): empty" << endlog;
                }
            }
            return s;
        }

        if (!is_blocked(p->cube, p->idx)) {
            logger(3) << "[rec_block] is_blocked = false; attempting relative induction:  ~C & F["
                      << (p->idx-1) << "] & T |= ~C'  (calling block)" << endlog;

            Cube c;
            bool ok = block(p->cube, p->idx, &c, /*compute_cti=*/true);

            if (ok) {
                logger(3) << "[rec_block] block => UNSAT. "
                          << "inductive subcube size=" << c.size()
                          << " rel. to F[" << (p->idx-1) << "], c=";
                logcube(4, c); logger(3) << endlog;

                unsigned int idx = p->idx, before_idx = idx;
                size_t before_size = c.size();

                logger(3) << "[rec_block] generalize_and_push: "
                          << "input size=" << before_size
                          << " at idx=" << before_idx << endlog;
                generalize_and_push(c, idx);
                logger(3) << "[rec_block] generalize_and_push: "
                          << "output size=" << c.size()
                          << " pushed_to_idx=" << idx
                          << " (delta_idx=" << (int(idx)-int(before_idx)) << ")"
                          << endlog;

                add_blocked(c, idx);

                if (idx < depth() && !opts_.stack) {
                    queue.push_new(p->cube, p->idx+1, p->next);
                    ++qsize_est;
                }
                queue.pop();
                --qsize_est;
            } else {
                logger(3) << "[rec_block] block => SAT. CTI predecessor size="
                          << c.size() << " : ";
                logcube(4, c); logger(3) << endlog;

                queue.push_new(c, p->idx-1, p);
                ++qsize_est;
            }
        } else {
            int where = syntactic_blocking_frame(p->cube, p->idx);
            logger(3) << "[rec_block] is_blocked = true; "
                      << (where >= 0 ? "syntactically subsumed by frame[" +
                                        std::to_string(where) + "]"
                                     : "semantically blocked")
                      << "  (pop current PO)" << endlog;
            queue.pop();
            --qsize_est;
        }
    }

    if (get_verbosity() >= 4) {
        logger(4) << "[rec_block] queue dump (after loop): empty" << endlog;
    }
    logger(2) << "[rec_block] done: queue empty, returning MSAT_TRUE" << endlog;
    return MSAT_TRUE;
}


bool IC3::propagate()
{
    TimeKeeper t(propagate_time_);

    size_t k = 1;
    for (; k < depth(); ++k) {
        Frame &f_k = frames_[k];

        // Snapshot frames [1..k+1] BEFORE any flush, to compute deltas later.
        std::vector<Frame> prev;
        prev.resize(k + 2); // index 0 unused for convenience
        for (size_t d = 1; d <= k + 1; ++d) prev[d] = frames_[d];

        // Try to push every cube from F[k] to F[k+1].
        std::vector<std::pair<Cube, Cube>> pushed_pairs; // (orig, pushed)
        std::vector<Cube> failed;

        for (size_t i = 0; i < f_k.size(); ++i) {
            const Cube &orig = f_k[i];
            Cube pushed_candidate;

            logger(3) << "trying to propagate cube of size " << orig.size() << ": ";
            logcube(4, orig);
            logger(3) << " from " << k << " to " << (k + 1) << endlog;

            // generalize=false during propagation, but block() may still
            // shrink the cube via UNSAT core extraction.
            if (!block(orig, k + 1, &pushed_candidate, /*compute_cti=*/false)) {
                failed.push_back(orig);
            } else {
                pushed_pairs.emplace_back(orig, pushed_candidate);
            }
        }

        // Flush all successful pushes to F[k+1]
        for (auto &pr : pushed_pairs) {
            Cube pushed = pr.second;             // (may equal pr.first)
            add_blocked(pushed, k + 1);          // no header change needed
        }

        // ---------- Delta reporting for this k -> k+1 step ----------
        // Helper: set-like membership for Cube vectors
        auto contains = [](const Frame &fs, const Cube &c) {
            return std::find(fs.begin(), fs.end(), c) != fs.end();
        };
        auto diff_vec = [&](const Frame &before, const Frame &after) {
            std::vector<Cube> out;
            for (const Cube &c : before) if (!contains(after, c)) out.push_back(c);
            return out;
        };
        auto add_vec = [&](const Frame &before, const Frame &after) {
            std::vector<Cube> out;
            for (const Cube &c : after) if (!contains(before, c)) out.push_back(c);
            return out;
        };

        // Count strengthened pushes (pushed cube != original cube)
        size_t strengthened = 0;
        for (auto &pr : pushed_pairs) if (pr.first != pr.second) ++strengthened;

        // What changed in F[k] and F[k+1]?
        const Frame &after_k   = frames_[k];
        const Frame &after_k1  = frames_[k + 1];
        const auto removed_k   = diff_vec(prev[k], after_k);
        const auto removed_all = [&](){
            // Subsumption may remove from frames 1..k as well, not just k.
            std::vector<Cube> agg;
            for (size_t d = 1; d <= k; ++d) {
                auto r = diff_vec(prev[d], frames_[d]);
                agg.insert(agg.end(), r.begin(), r.end());
            }
            return agg;
        }();
        const auto added_k1    = add_vec(prev[k + 1], after_k1);

        logger(3) << "[propagate] k=" << k << " -> " << (k + 1)
                  << "  pushed=" << pushed_pairs.size()
                  << " (strengthened=" << strengthened << ")"
                  << "  failed=" << failed.size()
                  << "  removed_by_subsumption=" << removed_all.size()
                  << "  sizes: |F[" << k << "]|=" << after_k.size()
                  << "  |F[" << (k + 1) << "]|=" << after_k1.size()
                  << endlog;

        if (get_verbosity() >= 4) {
            if (!pushed_pairs.empty()) {
                logger(4) << "  pushed cubes (orig -> pushed):" << endlog;
                for (auto &pr : pushed_pairs) {
                    logger(4) << "    ";
                    logcube(4, pr.first);
                    logger(4) << "  ->  ";
                    logcube(4, pr.second);
                    logger(4) << endlog;
                }
            }
            if (!failed.empty()) {
                logger(4) << "  not pushed:" << endlog;
                for (const Cube &c : failed) {
                    logger(4) << "    ";
                    logcube(4, c);
                    logger(4) << endlog;
                }
            }
            if (!removed_all.empty()) {
                logger(4) << "  removed by subsumption (any frame ≤ " << k << "):" << endlog;
                for (const Cube &c : removed_all) {
                    logger(4) << "    ";
                    logcube(4, c);
                    logger(4) << endlog;
                }
            }
            if (!added_k1.empty()) {
                logger(4) << "  newly in frame[" << (k + 1) << "]:" << endlog;
                for (const Cube &c : added_k1) {
                    logger(4) << "    ";
                    logcube(4, c);
                    logger(4) << endlog;
                }
            }

            // Fresh snapshot AFTER the flush
            logger(4) << "[frames] snapshot after propagate step "
                      << k << "->" << (k + 1) << ":" << endlog;
            logger(4) << "frame[" << k << "] := {" << endlog;
            for (const Cube &c : frames_[k]) {
                logger(4) << "   "; logcube(4, c); logger(4) << endlog;
            }
            logger(4) << "}" << endlog;
            logger(4) << "frame[" << (k + 1) << "] := {" << endlog;
            for (const Cube &c : frames_[k + 1]) {
                logger(4) << "   "; logcube(4, c); logger(4) << endlog;
            }
            logger(4) << "}" << endlog;
        }
        // ------------------------------------------------------------

        // Fixpoint check unchanged
        if (frames_[k].empty()) break;
    }

    // Original end-of-propagate invariant printing logic (unchanged)
    if (k < depth()) {
        logger(2) << "fixpoint found at frame " << k << endlog;
        logger(2) << "invariant:" << endlog;
        wit_.clear();
        for (size_t i = k + 1; i < frames_.size(); ++i) {
            Frame &f = frames_[i];
            for (Cube &c : f) {
                logcube(2, c); logger(2) << endlog;
                wit_.push_back(c);
                concretize(wit_.back());
                for (msat_term &l : wit_.back()) {
                    l = msat_make_not(ts_.get_env(), l);
                }
            }
        }
        return true;
    }
    return false;
}

// ---- helpers for printing terms and model values ----
static inline std::string smt2(msat_env e, msat_term t)
{
    char *c = msat_to_smtlib2_term(e, t);     // MathSAT allocates
    std::string s = c ? c : "";
    if (c) { msat_free(c); }
    return s;
}

static inline const char *bool_value_str(msat_env e, msat_term v)
{
    switch (msat_decl_get_tag(e, msat_term_get_decl(v))) {
    case MSAT_TAG_TRUE:  return "true";
    case MSAT_TAG_FALSE: return "false";
    default:             return nullptr; // non-constant bool
    }
}

static inline std::string smt2_term(msat_env e, msat_term t) {
    if (MSAT_ERROR_TERM(t)) return std::string("<?>");
    char *c = msat_to_smtlib2_term(e, t);
    if (!c) return std::string("<print-error>");
    std::string s(c);
    msat_free(c);
    return s;
}

static inline std::string smt2_any(msat_env e, msat_term t) {
    if (MSAT_ERROR_TERM(t)) return std::string("<?>");
    char *c = msat_to_smtlib2_term(e, t);
    if (!c) {
        c = msat_to_smtlib2(e, t);
        if (!c) return std::string("<print-error>");
    }
    std::string s(c);
    msat_free(c);
    return s;
}

static inline std::string model_bool_str(msat_env e, msat_term t) {
    if (MSAT_ERROR_TERM(t)) return std::string("<?>");
    msat_term mv = msat_get_model_value(e, t);
    if (MSAT_ERROR_TERM(mv)) return std::string("<?>");
    auto tag = msat_decl_get_tag(e, msat_term_get_decl(mv));
    if (tag == MSAT_TAG_TRUE)  return "true";
    if (tag == MSAT_TAG_FALSE) return "false";
    return smt2_term(e, mv);
}

void IC3::dump_full_model() {
    msat_env env = solver_.env();  // IMPORTANT: use solver's env (owns the model)

    logger(2) << "[model] ===== FULL MODEL DUMP (BEGIN) =====" << endlog;

    // (1) Base (non-Boolean) state variables: numerals (need FULL model gen)
    for (msat_term v : ts_.statevars()) {
        msat_type ty = msat_term_get_type(v);
        if (MSAT_ERROR_TYPE(ty) || msat_is_bool_type(env, ty)) continue;
        msat_term mv = msat_get_model_value(env, v);
        logger(2) << "[model] base   " << smt2_any(env, v)
                  << " = " << smt2_any(env, mv) << endlog;
    }

    // (2) Boolean labels and their predicates/next
    for (msat_term l : state_vars_) {
        std::string lname = smt2_any(env, l);
        std::string lval  = model_bool_str(env, l);

        auto pit = lbl2pred_.find(l);
        if (pit != lbl2pred_.end()) {
            msat_term p = pit->second;
            logger(2) << "[model] label  " << lname << " = " << lval
                      << "    (pred: " << smt2_any(env, p)
                      << " = " << model_bool_str(env, p) << ")"
                      << endlog;
        } else {
            logger(2) << "[model] label  " << lname << " = " << lval << endlog;
        }

        auto nit = lbl2next_.find(l);
        if (nit != lbl2next_.end()) {
            msat_term ln = nit->second;
            logger(2) << "[model] next   " << smt2_any(env, ln)
                      << " = " << model_bool_str(env, ln) << endlog;
        }
    }

    // (3) Inputs (boolean only)
    {
        bool any = false;
        for (msat_term i : ts_.inputvars()) {
            if (msat_term_is_boolean_constant(env, i)) {
                any = true;
                logger(2) << "[model] input  " << smt2_any(env, i)
                          << " = " << model_bool_str(env, i) << endlog;
            }
        }
        if (!any) {
            logger(2) << "[model] input  <none or not boolean>" << endlog;
        }
    }

    logger(2) << "[model] ===== FULL MODEL DUMP (END) =====" << endlog;
}


static bool eval_symbol(msat_env env, msat_model mdl, const char* name, std::string &out) {
    msat_decl d = msat_find_decl(env, name);
    if (MSAT_ERROR_DECL(d)) return false;                  // symbol not found
    msat_term sym = msat_make_constant(env, d);
    msat_term val = msat_model_eval(mdl, sym);             // << correct API
    if (MSAT_ERROR_TERM(val)) return false;                // model didn't give a value
    char* raw = msat_to_smtlib2_term(env, val);
    out = raw ? std::string(raw) : std::string("?");
    if (raw) msat_free(raw);
    return true;
}

static std::string clause_of_negated_cube(msat_env env,
                                          const std::vector<msat_term> &cube) {
    if (cube.empty()) return "false";
    std::ostringstream oss;
    oss << "(or";
    for (msat_term l : cube) {
        const bool is_not = msat_term_is_not(env, l);
        msat_term v      = is_not ? msat_term_get_arg(l, 0) : l;  // literal variable
        msat_term comp   = is_not ? v : msat_make_not(env, v);    // complement to form ~literal
        oss << " " << smt2(env, comp);
    }
    oss << ")";
    return oss.str();
}

bool IC3::block(const Cube &c, unsigned int idx, Cube *out, bool compute_cti)
{
    TimeKeeper t(block_time_);
    ++num_block_;
    assert(idx > 0);

    logger(2) << "\n------------------------------------------------------\nturn " << turn++ << "\n";
    logger(2) << "================================================================================" << endlog;
    logger(2) << "[block] ENTER  idx=" << idx
              << "  compute_cti=" << (compute_cti ? "true" : "false")
              << "  depth=" << depth()
              << "  |c|=" << c.size() << endlog;

    logger(2) << "[block] input cube: ";
    logcube(2, c); logger(2) << endlog;

    // F[idx-1] & T (adds assumptions inside)
    logger(3) << "[block] activate_frame(" << (idx-1) << "), activate_trans()" << endlog;
    activate_frame(idx-1);
    activate_trans();

    // c' (primed) in the same order as c
    Cube primed = get_next(c);
    logger(3) << "[block] preparing assumptions over c' (order preserved), |c'|="
              << primed.size() << endlog;

    std::vector<msat_term> primed_assumptions;
    primed_assumptions.reserve(primed.size());
    for (size_t i = 0; i < primed.size(); ++i) {
        logger(4) << "  assume c'[" << i << "] term_id=" << msat_term_id(primed[i])
                  << "  (paired orig term_id=" << msat_term_id(c[i]) << ")" << endlog;
        solver_.assume(primed[i]);
        primed_assumptions.push_back(primed[i]);
    }
    if (!opts_.seed) {
        logger(4) << "[block] opts_.seed=false  (natural order assumptions)" << endlog;
    }

    // Start a SAT scope; assert the single clause (~c)
    logger(3) << "[block] solver_.push(); add_cube_as_clause(~c); solve()" << endlog;
    solver_.push();
    solver_.add_cube_as_clause(c);

    // ---------- Python-like [block.pre] dump ----------
    std::vector<msat_term> all_as;
    all_as.reserve(frame_labels_.size() + 2 + primed_assumptions.size());

    // frames (activate_frame(idx-1) => assume(not frame_label[k]) for k<idx-1, POS otherwise)
    for (size_t k = 0; k < frame_labels_.size(); ++k) {
        msat_term a = lit(frame_labels_[k], k < (idx - 1));
        all_as.push_back(a);
    }
    // trans/bad (activate_trans() => trans POS, bad NOT)
    all_as.push_back(lit(trans_label_, false));
    all_as.push_back(lit(bad_label_,   true));

    // c' assumptions we just added
    all_as.insert(all_as.end(), primed_assumptions.begin(), primed_assumptions.end());

    logger(3) << "[block.pre] assumptions.count = " << all_as.size() << endlog;
    for (size_t i = 0; i < all_as.size(); ++i) {
        logger(3) << "[block.pre]  A[" << i << "] term_id=" << msat_term_id(all_as[i])
                  << "  " << logterm(all_as[i]) << endlog;
    }

    // Show the exact "~c" clause asserted in this temporary scope
    logger(3) << "[block.pre] asserted ~c clause: "
              << clause_of_negated_cube(ts_.get_env(), c) << endlog;

    // Frames / names
    logger(4) << "[block.pre] frames:" << endlog;
    for (size_t k = 0; k < frame_labels_.size(); ++k) {
        bool neg = (k < (idx - 1));
        logger(4) << "    frame[" << k << "]: term_id=" << msat_term_id(frame_labels_[k])
                  << "  assumed=" << (neg ? "NOT" : "POS")
                  << "  name=" << logterm(frame_labels_[k]) << endlog;
    }
    logger(4) << "[block.pre] trans/bad:" << endlog;
    logger(4) << "    trans term_id=" << msat_term_id(trans_label_)
              << "  assumed=POS  name=" << logterm(trans_label_) << endlog;
    logger(4) << "    bad   term_id=" << msat_term_id(bad_label_)
              << "  assumed=NOT  name=" << logterm(bad_label_)   << endlog;

    // c' again, as in python
    logger(4) << "[block.pre] c' (order preserved), |c'|=" << primed_assumptions.size() << endlog;
    for (size_t i = 0; i < primed_assumptions.size(); ++i) {
        logger(4) << "    c'[" << i << "]: term_id=" << msat_term_id(primed_assumptions[i])
                  << "  (paired orig term_id=" << msat_term_id(c[i]) << ")" << endlog;
    }

    logger(3) << "[block.pre] INPUT cube c (will assert clause(~c) in this scope): ";
    logcube(3, c); logger(3) << endlog;
    // --------------------------------------------------

    // Solve
    bool sat = solve();
    logger(2) << "[block] solve() => " << (sat ? "SAT  (not inductive)" : "UNSAT  (inductive)") << endlog;

    if (!sat) {
        // UNSAT: relative induction succeeded
        if (out) {
            const TermSet &core = solver_.unsat_assumptions();  // core over primed lits
            logger(3) << "[block] UNSAT core size=" << core.size()
                      << " (over primed literals)" << endlog;

            Cube &candidate = *out;
            Cube rest;
            candidate.clear();
            for (size_t i = 0; i < primed.size(); ++i) {
                if (core.find(primed[i]) != core.end()) candidate.push_back(c[i]);
                else                                     rest.push_back(c[i]);
            }

            logger(2) << "[block] candidate BEFORE ensure_not_initial (|cand|="
                      << candidate.size() << "): ";
            logcube(2, candidate); logger(2) << endlog;

            solver_.pop();  // end UNSAT scope
            logger(3) << "[block] solver_.pop()  (UNSAT scope ended)" << endlog;

            logger(3) << "[block] ensure_not_initial(candidate, rest)" << endlog;
            ensure_not_initial(candidate, rest);

            logger(2) << "[block] candidate AFTER ensure_not_initial (|cand|="
                      << candidate.size() << "): ";
            logcube(2, candidate); logger(2) << endlog;
        } else {
            solver_.pop();
            logger(3) << "[block] solver_.pop()  (UNSAT && out==NULL)" << endlog;
        }

        logger(2) << "[block] RETURN: true (UNSAT)" << endlog;
        logger(2) << "================================================================================" << endlog;
        return true;
    } else {
        // SAT: build CTI predecessor (and optional inputs)
        Cube inputs;
        if (compute_cti) {
            assert(out);
            get_cube_from_model(*out, &inputs);
            logger(2) << "[block] CTI predecessor from model (|out|=" << out->size() << "): ";
            logcube(2, *out); logger(2) << endlog;
            if (!inputs.empty()) {
                logger(4) << "[block] CTI inputs (|inputs|=" << inputs.size() << "): ";
                logcube(4, inputs); logger(4) << endlog;
            }
        }

        solver_.pop();
        logger(3) << "[block] solver_.pop()  (SAT path)" << endlog;

        if (compute_cti) {
            size_t before = out->size();
            logger(3) << "[block] generalize_pre(primed, inputs, out)  before |out|="
                      << before << endlog;
            generalize_pre(primed, inputs, *out);
            size_t after = out->size();
            logger(3) << "[block] generalize_pre done  |out| " << before << " -> " << after << endlog;
        }

        logger(2) << "[block] RETURN: false (SAT" << (compute_cti ? "+CTI" : "") << ")" << endlog;
        logger(2) << "================================================================================" << endlog;
        return false;
    }
}


void IC3::generalize(Cube &c, unsigned int &idx)
{
    tmp_ = c;
    gen_needed_.clear();
    
    typedef std::uniform_int_distribution<int> RandInt;
    RandInt dis;

    logger(3) << "trying to generalize cube of size " << c.size()
              << " at " << idx << ": ";
    logcube(4, c);
    logger(3) << endlog;

    // ~c is inductive relative to idx-1, and we want to generalize ~c to a
    // stronger clause ~g. We do this by dropping literals and calling block()
    // again: every time block() succeeds, it will further generalize its
    // input cube using the unsat core found by the SMT solver (see above)
    // 
    // More sophisticated (more effective but harder to understand) strategies
    // exist, see e.g. the paper
    // - Hassan, Somenzi, Bradley: Better generalization in IC3. FMCAD'13
    //
    for (size_t i = 0; i < tmp_.size() && tmp_.size() > 1; ) {
        // randomly pick the next literal to drop
        size_t j = (opts_.seed ?
                    dis(rng_, RandInt::param_type(1, tmp_.size())) - 1 :
                    i);
        msat_term l = tmp_[j];
        if (gen_needed_.find(l) == gen_needed_.end()) {
            auto it = tmp_.erase(tmp_.begin()+j);

            logger(4) << "trying to drop " << logterm(l) << endlog;

            if (is_initial(tmp_) || !block(tmp_, idx, &tmp_, false)) {
                // remember that we failed to remove l, so that we do not try
                // this again later in the loop
                gen_needed_.insert(l);
                tmp_.insert(it, l);
                ++i;
            }
        }
    }

    std::swap(tmp_, c);
}


void IC3::push(Cube &c, unsigned int &idx)
{
    // find the highest idx frame in F which can successfully block c. As a
    // byproduct, this also further strenghens ~c if possible
    while (idx < depth()-1) {
        tmp_.clear();
        if (block(c, idx+1, &tmp_, false)) {
            std::swap(tmp_, c);
            ++idx;
        } else {
            break;
        }
    }
}


inline void IC3::concretize(Cube &c)
{
    for (msat_term &t : c)
    {
        std::cout << "before concretization: " << msat_to_smtlib2_term(ts_.get_env(), t) << std::endl;
        auto it = lbl2pred_.find(var(t));

        assert(it != lbl2pred_.end());
        t = lit(it->second, it->first != t);
        std::cout << "after concretizations: " << msat_to_smtlib2_term(ts_.get_env(), t) << std::endl;
    }
}


msat_truth_value IC3::refine_abstraction(std::vector<TermList> &cex)
{
    TimeKeeper t(refinement_time_);
    ++num_refinements_;

    logger(2) << "trying to refine cex of length " << cex.size() << endlog;

    if (!preds_.empty()) {
        // replace each label with the corresponding predicate
        for (TermList &l : cex) {
            concretize(l);
        }
    }

    if (ref_.refine(cex)) {
        // if refinement is successful, we extract new predicates from the
        // sequence interpolant
        int c = 0;
        for (msat_term p : ref_.used_predicates()) {
            if (preds_.insert(p).second) {
                ++c;
                add_pred(p);
            }
        }
        if (c == 0) {
            if (solver_.is_approx()) {
                logger(2) << "no new predicate found, setting solver to precise"
                          << endlog;
                solver_.reset(true);
                reset_solver();
                return MSAT_TRUE;
            } else {
                logger(2) << "refinement failure (no new predicate found)"
                          << endlog;
                return MSAT_UNDEF;
            }
        }
        logger(2) << "refinement added " << c << " new predicates" << endlog;
        return MSAT_TRUE;
    } else if (ts_.live_prop()) {
        TimeKeeper tt(liveness_refinement_time_);
        ++num_liveness_refinements_;
        
        msat_truth_value res = liveref_.refine(cex, livepreds_, rankrels_);
        if (res == MSAT_TRUE) {
            // refinement successful, add new predicates and perform new l2s
            // encoding
            int c = 0, l = 0;
            for (msat_term p : liveref_.used_predicates()) {
                if (preds_.insert(p).second) {
                    ++c;
                    add_pred(p);
                }
                if (livepreds_.insert(p).second) {
                    ++l;

                    logger(2) << "adding liveness predicate "
                              << livepreds_.size()
                              << ": " << logterm(p) << endlog;
                    ++num_liveness_predicates_;
                }
            }
            const RankRelList &rl = liveref_.used_rankrels();
            logger(2) << "liveness refinement added " << c
                      << " new state predicates, "
                      << l << " new live predicates and " << rl.size()
                      << " new ranking relations" << endlog;
            rankrels_.insert(rankrels_.end(), rl.begin(), rl.end());
            l2s_.encode(livepreds_, rankrels_);
            num_liveness_rankrels_ += rl.size();

            for (msat_term v : l2s_.new_statevars()) {
                if (msat_term_is_boolean_constant(ts_.get_env(), v)) {
                    state_vars_.push_back(v);
                    lbl2next_[v] = ts_.next(v);
                    lbl2pred_[v] = v;
                }
            }
            solver_.add(l2s_.init_constraint(), init_label_);
            solver_.add(abs_.abstract(l2s_.trans_constraint()), trans_label_);
            solver_.add(lit(bad_label_, true), msat_make_true(ts_.get_env()));

            for (msat_term p : l2s_.init_predicates()) {
                if (preds_.insert(p).second) {
                    add_pred(p);
                }
            }

            bad_label_ = make_label("bad");
            msat_term bad = lit(l2s_.prop(), true);
            solver_.add(bad, bad_label_);
            return MSAT_TRUE;
        } else if (res == MSAT_FALSE) {
            wit_.clear();
            wit_loopback_ = liveref_.counterexample(wit_);
            return MSAT_FALSE;
        } else {
            logger(1) << "impossible to refine liveness abstraction, "
                      << "returning unknown" << endlog;
            return MSAT_UNDEF;
        }
    } else {
        wit_.clear();
        ref_.counterexample(wit_);
        wit_loopback_ = CEX_NO_LOOP;
        return MSAT_FALSE;
    }
}


//-----------------------------------------------------------------------------
// minor/helper methods
//-----------------------------------------------------------------------------


void IC3::initialize()
{
    l2s_.initialize();
    liveref_.initialize();

    for (msat_term v : ts_.statevars()) {
        if (msat_term_is_boolean_constant(ts_.get_env(), v)) {
            state_vars_.push_back(v);
            // fill the maps lbl2next_ and lbl2next_ also for Boolean state
            // vars. This makes the implementation of get_next() and refine()
            // simpler, as we do not need to check for special cases
            lbl2next_[v] = ts_.next(v);
            lbl2pred_[v] = v;
        }
    }

    solver_.add(ts_.init(), init_label_);
    solver_.add(abs_.abstract(ts_.trans()), trans_label_);

    abs_.initial_predicates(preds_);
    for (msat_term t : preds_) {
        add_pred(t);
    }

    msat_term bad;
    if (ts_.live_prop()) {
        for (msat_term p : preds_) {
            livepreds_.insert(p);
            logger(2) << "adding liveness predicate " << livepreds_.size()
                      << ": " << logterm(p) << endlog;
            ++num_liveness_predicates_;
        }
        
        l2s_.encode(livepreds_, rankrels_);
        bad = lit(l2s_.prop(), true);

        for (msat_term v : l2s_.new_statevars()) {
            if (msat_term_is_boolean_constant(ts_.get_env(), v)) {
                state_vars_.push_back(v);
                lbl2next_[v] = ts_.next(v);
                lbl2pred_[v] = v;
            }
        }
        solver_.add(l2s_.init_constraint(), init_label_);
        solver_.add(abs_.abstract(l2s_.trans_constraint()), trans_label_);

        for (msat_term p : l2s_.init_predicates()) {
            if (preds_.insert(p).second) {
                add_pred(p);
            }
        }
    } else {
        bad = lit(ts_.prop(), true);
    }
    solver_.add(bad, bad_label_);
    
    // the first frame is init
    frames_.push_back(Frame());
    frame_labels_.push_back(init_label_);

    // NEW: log frame creation + full snapshot
    logger(3) << "[frames] created frame[0] (init)" << endlog;
    if (get_verbosity() >= 4) {
        logger(4) << "[frames] snapshot after initialize:" << endlog;
        logger(4) << "frame[0] := {\n}" << endlog;
    }

    logger(1) << "initialized IC3: " << ts_.statevars().size() << " state vars,"
              << " " << ts_.inputvars().size() << " input vars, "
              << preds_.size() << " predicates" << endlog;
}


void IC3::new_frame()
{
    if (depth()) {
        logger(1) << depth() << ": " << flushlog;
        for (size_t i = 1; i <= depth(); ++i) {
            Frame &f = frames_[i];
            logger(1) << f.size() << " ";
        }
        logger(1) << "{" << num_predicates_ << "|" << num_refinements_ << "}";
        if (ts_.live_prop()) {
            logger(1) << "[" << num_liveness_predicates_ << "|"
                      << num_liveness_refinements_ << "]";
        }
        logger(1) << endlog;
    }

    frames_.push_back(Frame());
    frame_labels_.push_back(make_label("frame"));

    // NEW: log frame creation + full snapshot
    size_t new_idx = frames_.size() - 1;
    logger(3) << "[frames] created frame[" << new_idx << "]" << endlog;

    if (get_verbosity() >= 4) {
        logger(4) << "[frames] snapshot after new_frame:" << endlog;
        for (size_t i = 1; i < frames_.size(); ++i) {
            Frame &f = frames_[i];
            logger(4) << "frame[" << i << "] := {" << endlog;
            for (Cube &c : f) {
                logger(4) << "   ";
                logcube(4, c);
                logger(4) << endlog;
            }
            logger(4) << "}" << endlog;
        }
        logger(4) << endlog;
    }
}


void IC3::generalize_and_push(Cube &c, unsigned int &idx)
{
    TimeKeeper t(generalize_and_push_time_);
    
    generalize(c, idx);
    push(c, idx);
}


void IC3::add_blocked(Cube &c, unsigned int idx)
{
    // whenever we add a clause ~c to an element of F, we also remove subsumed
    // clauses. This automatically keeps frames_ in a "delta encoded" form, in
    // which each clause is stored only in the last frame in which it
    // occurs. However, this does not remove subsumed clauses from the
    // underlying SMT solver. We address this by resetting the solver every
    // once in a while (see the comment in rec_block())
    for (size_t d = 1; d < idx+1; ++d) {
        Frame &fd = frames_[d];
        size_t j = 0;

        // NEW: track and report removals
        std::vector<Cube> removed;

        for (size_t i = 0; i < fd.size(); ++i) {
            if (!subsumes(c, fd[i])) {
                fd[j++] = fd[i];
            } else {
                ++num_subsumed_cubes_;
                removed.push_back(fd[i]);
            }
        }
        fd.resize(j);

        if (!removed.empty()) {
            logger(3) << "[frames] subsumption removed "
                      << removed.size() << " cube(s) from frame[" << d << "]"
                      << endlog;
            if (get_verbosity() >= 4) {
                for (Cube &rc : removed) {
                    logger(4) << "   - ";
                    logcube(4, rc);
                    logger(4) << endlog;
                }
            }
        }
    }

    // add ~c to solver and to in-memory frame
    solver_.add_cube_as_clause(c, frame_labels_[idx]);
    frames_[idx].push_back(c);

    // existing detailed add log
    logger(3) << "adding cube of size " << c.size() << " at level " << idx
              << ": ";
    logcube(4, c);
    logger(3) << endlog;

    // NEW: concise event + full snapshot of ALL frames
    logger(3) << "[frames] added cube to frame[" << idx << "]: ";
    logcube(3, c);
    logger(3) << endlog;

    if (get_verbosity() >= 4) {
        logger(4) << "[frames] snapshot after add_blocked:" << endlog;
        for (size_t i = 1; i < frames_.size(); ++i) {
            Frame &f = frames_[i];
            logger(4) << "frame[" << i << "] := ";
            if (i+1 < frames_.size()) {
                logger(4) << "frame[" << (i+1) << "] + ";
            }
            logger(4) << "{" << endlog;
            for (Cube &cc : f) {
                logger(4) << "   ";
                logcube(4, cc);
                logger(4) << endlog;
            }
            logger(4) << "}" << endlog;
        }
        logger(4) << endlog;
    }

    ++num_added_cubes_;
    max_cube_size_ = std::max(uint32_t(c.size()), max_cube_size_);
    avg_cube_size_ += (double(c.size()) - avg_cube_size_) / num_added_cubes_;
}


IC3::Cube IC3::get_next(const Cube &c)
{
    Cube ret;
    ret.reserve(c.size());

    for (msat_term l : c) {
        auto it = lbl2next_.find(var(l));
        assert(it != lbl2next_.end());
        ret.push_back(lit(it->second, l != it->first));
    }
    return ret;
}

static std::string eval_smt2(msat_env env, msat_model mdl, msat_term t) {
    msat_term val = msat_model_eval(mdl, t);
    char *raw = msat_to_smtlib2_term(env, val);
    std::string out = raw ? std::string(raw) : std::string();
    if (raw) msat_free(raw);
    return out;
}

// Return the SMT-LIB2 rendering of the current model value of term t
static std::string value_smt2(msat_env env, msat_term t) {
    msat_term val = msat_get_model_value(env, t);
    char *raw = msat_to_smtlib2_term(env, val);
    std::string out = raw ? std::string(raw) : std::string();
    if (raw) msat_free(raw);
    return out;
}

static bool try_value_smt2(msat_env env, msat_term t, std::string &out) {
    msat_term val = msat_get_model_value(env, t);
    // Guard against invalid/error terms (defensive: treat non-positive ids as invalid)
    int vid = msat_term_id(val);
    if (vid <= 0) return false;

    char *raw = msat_to_smtlib2_term(env, val);
    if (!raw) return false;
    out.assign(raw);
    msat_free(raw);
    return true;
}

static inline std::string smt2_int(int k) {
    if (k < 0) {
        return "(- " + std::to_string(-k) + ")";
    }
    return std::to_string(k);
}

static bool probe_small_int(msat_env env,
                            ic3ia::Solver &solver,
                            msat_term v,
                            int lo, int hi,
                            std::string &out_s)
{
    // only makes sense for non-Boolean terms
    if (msat_term_is_boolean_constant(env, v)) return false;

    for (int k = lo; k <= hi; ++k) {
        msat_term kn = msat_make_number(env, std::to_string(k).c_str());
        msat_term eq = msat_make_equal(env, v, kn);   // (v = k)
        // Ask the model for the truth value of this Boolean atom.
        // This path is known-safe in your codebase.
        bool is_true = solver.model_value(eq);
        if (is_true) {
            out_s = smt2_int(k);
            return true;
        }
    }
    return false;
}


void IC3::get_cube_from_model(Cube &out, Cube *inputs)
{
    out.clear();

    logger(2) << "[get_cube_from_model] BEGIN" << endlog;

    // (A) Assumptions
    {
        const TermList &A = solver_.assumptions();
        logger(2) << "[get_cube_from_model] assumptions.count = " << A.size() << endlog;
        if (!A.empty()) {
            msat_env env = solver_.env();  // use solver env
            for (std::size_t i = 0; i < A.size(); ++i) {
                msat_term a = A[i];
                logger(2) << "[get_cube_from_model]  A[" << i
                          << "] term_id=" << msat_term_id(a)
                          << "  " << smt2_any(env, a) << endlog;
            }
        }
    }

    // (B) One-line numerals (non-Boolean state vars)
    {
        msat_env env = solver_.env();  // use solver env
        std::ostringstream oss;
        bool any = false;
        for (msat_term v : ts_.statevars()) {
            msat_type ty = msat_term_get_type(v);
            if (MSAT_ERROR_TYPE(ty) || msat_is_bool_type(env, ty)) continue;
            if (any) oss << ", ";
            any = true;
            msat_term mv = msat_get_model_value(env, v);
            oss << smt2_any(env, v) << "=" << smt2_any(env, mv);
        }
        if (any) {
            logger(2) << "[get_cube_from_model] numerals: " << oss.str() << endlog;
        }
    }

    // (C) Full model dump
    dump_full_model();

    // --- original behavior: build predecessor cube from labels ---
    for (msat_term v : state_vars_) {
        out.push_back(lit(v, !solver_.model_value(v)));
    }
    std::sort(out.begin(), out.end());

    if (inputs) {
        msat_env env = solver_.env();  // use solver env
        for (auto i : ts_.inputvars()) {
            if (msat_term_is_boolean_constant(env, i)) {
                inputs->push_back(lit(i, !solver_.model_value(i)));
            }
        }
    }
}


void IC3::generalize_pre(const Cube &target, const Cube &inputs, Cube &out)
{
    if (!try_gen_pre_) {
        return;
    }

    TimeKeeper tk(generalize_pre_time_);
    
    for (auto i : inputs) {
        solver_.assume(i);
    }
    for (auto l : out) {
        solver_.assume(l);
    }
    activate_trans();
    solver_.push();
    solver_.add_cube_as_clause(target);
    bool sat = solve();
    if (!sat) {
        const TermSet &core = solver_.unsat_assumptions();
        size_t n = out.size();
        auto it = std::remove_if(out.begin(), out.end(), 
                                 [&core](msat_term l)
                                 { return core.find(l) == core.end(); });
        out.resize(it - out.begin());
        if (out.size() < n) {
            ++num_generalize_pre_;
        }
    } else {
        try_gen_pre_ = false;
    }
    solver_.pop();
}


inline bool IC3::subsumes(const Cube &a, const Cube &b)
{
    return (a.size() <= b.size() &&
            std::includes(b.begin(), b.end(), a.begin(), a.end()));
}


bool IC3::is_blocked(const Cube &c, unsigned int idx)
{
    // first check syntactic subsumption
    for (size_t i = idx; i < frames_.size(); ++i) {
        Frame &f = frames_[i];
        for (size_t j = 0; j < f.size(); ++j) {
            Cube &fj = f[j];
            if (subsumes(fj, c)) {
                ++num_subsumed_cubes_;
                return true;
            }
        }
    }

    if (preds_.empty()) {
        return false;
    }

    // then semantic
    activate_frame(idx);
    activate_trans_bad(false, false);

    for (size_t i = 0; i < c.size(); ++i) {
        solver_.assume(c[i]);
    }
    bool sat = solve();

    return !sat;
}


bool IC3::is_initial(const Cube &c)
{
    activate_frame(0);
    activate_trans_bad(false, false);
    
    for (msat_term l : c) {
        solver_.assume(l);
    }
    bool sat = solve();
    return sat;
}


void IC3::ensure_not_initial(Cube &c, Cube &rest)
{
    // we know that "init & c & rest" is unsat. If "init & c" is sat, we find
    // a small subset of "rest" to add-back to c to restore unsatisfiability
    if (is_initial(c)) {
        size_t n = c.size();
        c.insert(c.end(), rest.begin(), rest.end());
        
        bool yes = is_initial(c);
        assert(!yes);

        const TermSet &core = solver_.unsat_assumptions();
        c.resize(n);

        for (msat_term l : rest) {
            if (core.find(l) != core.end()) {
                c.push_back(l);
            }
        }
        
        std::sort(c.begin(), c.end());
    }
}


inline void IC3::activate_frame(unsigned int idx)
{
    for (unsigned int i = 0; i < frame_labels_.size(); ++i) {
        solver_.assume(lit(frame_labels_[i], i < idx));
    }
}


inline void IC3::activate_bad() { activate_trans_bad(false, true); }
inline void IC3::activate_trans() { activate_trans_bad(true, false); }

inline void IC3::activate_trans_bad(bool trans_active, bool bad_active)
{
    solver_.assume(lit(trans_label_, !trans_active));
    solver_.assume(lit(bad_label_, !bad_active));
}


bool IC3::solve()
{
    double elapse = 0;
    bool ret = false;
    {
        TimeKeeper t(elapse);
        ++num_solve_calls_;
        
        ret = solver_.check();
    }
    solve_time_ += elapse;
    if (ret) {
        solve_sat_time_ += elapse;
        ++num_solve_sat_calls_;
    } else {
        solve_unsat_time_ += elapse;
        ++num_solve_unsat_calls_;
    }
    return ret;
}


void IC3::add_pred(msat_term p)
{
    msat_term n = ts_.next(p);
    msat_term a = abs_.abstract(n);
    msat_term f = msat_make_iff(ts_.get_env(), n, a);
    // link the concrete and abstract version of the predicate (this is
    // implicit abstraction)
    solver_.add(f, trans_label_);

    // create Boolean labels for the predicate definition
    // one for the current-state predicate
    msat_term l = vp_.fresh_var("pred");
    pred2lbl_[p] = l;
    lbl2pred_[l] = p;
    // one for the next-state predicate
    msat_term ln = vp_.fresh_var("pred_next");
    lbl2next_[l] = ln;

    logger(2) << "adding predicate " << (++num_predicates_) << ": "
              << logterm(l) << " := " << logterm(p) << endlog;

    
    // add the definitions to the solver
    solver_.add(msat_make_and(ts_.get_env(),
                              msat_make_iff(ts_.get_env(), l, p),
                              msat_make_iff(ts_.get_env(), ln, n)),
                msat_make_true(ts_.get_env()));
    // now consider the predicate label as a state variable
    state_vars_.push_back(l);
    // inform the refiner of the new predicate
    ref_.add_predicate(p);

}


void IC3::reset_solver()
{
    logger(3) << "resetting SMT solver" << endlog;
    ++num_solver_reset_;
    solver_.reset();
    last_reset_calls_ = num_solve_calls_;

    // re-add initial states, transition relation and bad states
    solver_.add(ts_.init(), init_label_);
    solver_.add(abs_.abstract(ts_.trans()), trans_label_);
    msat_term bad = lit(ts_.live_prop() ? l2s_.prop() : ts_.prop(), true);
    solver_.add(bad, bad_label_);

    // re-add all the definitions for the predicates (see add_pred())
    msat_term label = msat_make_true(ts_.get_env());
    for (msat_term t : preds_) {
        msat_term n = ts_.next(t);
        msat_term a = abs_.abstract(n);
        msat_term f = msat_make_iff(ts_.get_env(), n, a);
        solver_.add(f, trans_label_);
        msat_term l = pred2lbl_[t];
        msat_term ln = lbl2next_[l];
        solver_.add(msat_make_iff(ts_.get_env(), l, t), label);
        solver_.add(msat_make_iff(ts_.get_env(), ln, n), label);
    }

    // re-add all the clauses in the frames
    for (size_t i = 0; i < frames_.size(); ++i) {
        msat_term l = frame_labels_[i];
        for (Cube &c : frames_[i]) {
            solver_.add_cube_as_clause(c, l);
        }
    }
}


inline size_t IC3::depth()
{
    return frames_.size()-1;
}


inline msat_term IC3::make_label(const char *name)
{
    return vp_.fresh_var(name);
}


inline msat_term IC3::var(msat_term t)
{
    return ic3ia::var(ts_.get_env(), t);
}


inline msat_term IC3::lit(msat_term t, bool neg)
{
    return ic3ia::lit(ts_.get_env(), t, neg);
}


Logger &IC3::logcube(unsigned int level, const Cube &c)
{
    logger(level) << "[ ";
    for (msat_term l : c) {
        msat_term v = lbl2pred_[var(l)];
        logger(level) << (l == var(l) ? "" : "~") << logterm(v) <<" ";
    }
    logger(level) << "]" << flushlog;
    return Logger::get();
}


inline ic3ia::logterm IC3::logterm(msat_term t)
{
    return ic3ia::logterm(ts_.get_env(), t);
}

int IC3::frame_index_of_label(msat_term v) {
  for (unsigned i = 0; i < frame_labels_.size(); ++i) {
    if (msat_term_id(v) == msat_term_id(frame_labels_[i])) {
      return static_cast<int>(i);
    }
  }
  return -1;
}

void IC3::dump_assumptions(const std::vector<msat_term> &as)
{
    logger(3) << "[block.pre] assumptions.count = " << as.size() << endlog;
    for (size_t i = 0; i < as.size(); ++i) {
        logger(3) << "[block.pre]  A[" << i << "] term_id=" << msat_term_id(as[i])
                  << "  " << logterm(as[i]) << endlog;
    }
}

void IC3::dump_unsat_core_explained(const TermSet &core)
{
    logger(4) << "[block] UNSAT core explained (primed literals):" << endlog;
    for (msat_term t : core) {
        logger(4) << "    core term_id=" << msat_term_id(t)
                  << "  " << logterm(t) << endlog;
    }
}


} // namespace ic3ia
