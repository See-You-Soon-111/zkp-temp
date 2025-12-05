#ifndef ZERO_CHECK_H
#define ZERO_CHECK_H

#include "subroutines/poly_iop/sum_check/sumcheck.h"
#include "arithmetic/virtual_polynomial.h"
#include <memory>
#include <vector>
#include <iostream>

/// A zero check IOP subclaim for `f(x)` consists of the following:
///   - the initial challenge vector r which is used to build eq(x, r) in
///     SumCheck
///   - the random vector `v` to be evaluated
///   - the claimed evaluation of `f(v)`
template <typename F>
struct ZeroCheckSubClaim
{
    // the evaluation point
    vector<F> point;
    // the expected evaluation
    F expected_evaluation;
    // the initial challenge r which is used to build eq(x, r)
    vector<F> init_challenge;
};

template <typename F>
class ZeroCheck
{
public:
    using MultilinearExtension = shared_ptr<DenseMultilinearExtension<F>>;
    using ZeroCheckProof = IOPProof<F>;
    using Transcript = SimpleTranscript;

    SumCheck<F> sum_check;

    Transcript init_transcript()
    {
        return SimpleTranscript("Initializing ZeroCheck transcript");
    }

    ZeroCheckProof prove(
        const VirtualPolynomial<F> &poly,
        Transcript &transcript)
    {
        size_t length = poly.aux_info.num_variables;
        vector<F> r = transcript.get_and_append_challenge_vector<F>("0check r", length);

        VirtualPolynomial<F> f_hat = build_f_hat<F>(poly, r);

        return sum_check.prove(f_hat, transcript);
    }

    ZeroCheckSubClaim<F> verify(
        const ZeroCheckProof &proof,
        const VPAuxInfo &fx_aux_info,
        Transcript &transcript)
    {
        F sum = proof.proofs[0].evaluations[0] + proof.proofs[0].evaluations[1];
        if (sum != F::zero())
        {
            cout << "zero check: sum is not zero";
        }

        size_t length = fx_aux_info.num_variables;
        vector<F> r = transcript.get_and_append_challenge_vector<F>("0check r", length);
        // hat_fx's max degree is increased by eq(x, r).degree() which is 1
        VPAuxInfo hat_fx_aux_info = fx_aux_info;
        hat_fx_aux_info.max_degree += 1;

        SumCheckSubClaim<F> sum_subclaim = sum_check.verify(F::zero(), proof, hat_fx_aux_info, transcript);

        F eq_x_r_eval = eq_eval<F>(sum_subclaim.point, r);
        F expected_evaluation = sum_subclaim.expected_evaluation * eq_x_r_eval.inverse();

        return ZeroCheckSubClaim<F>{
            sum_subclaim.point,
            expected_evaluation,
            r};
    }
};

#endif