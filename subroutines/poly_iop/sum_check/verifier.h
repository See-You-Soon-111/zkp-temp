#ifndef VERIFIER_H
#define VERIFIER_H

#include <vector>
#include "subroutines/poly_iop/structs.h"
#include "transcript/transcript.h"
#include "arithmetic/virtual_polynomial.h"

using namespace std;
/// compute the factorial(a) = 1 * 2 * ... * a
template <typename F>
F field_factorial(size_t a)
{
    F res = F::one();
    for (size_t i = 2; i <= a; ++i)
    {
        res *= F(static_cast<uint64_t>(i));
    }
    return res;
}

/// Interpolate a uni-variate degree-`p_i.len()-1` polynomial and evaluate this
/// polynomial at `eval_at`:
///
///   \sum_{i=0}^len p_i * (\prod_{j!=i} (eval_at - j)/(i-j) )
///
/// This implementation is linear in number of inputs in terms of field
/// operations. It also has a quadratic term in primitive operations which is
/// negligible compared to field operations.
/// TODO: The quadratic term can be removed by precomputing the lagrange
/// coefficients.

// 例子f(0)=1,f(1)=2,f(2)=4,eval_at=3,len=3
template <typename F>
F interpolate_uni_poly(vector<F> &p_i, const F &eval_at)
{
    size_t len = p_i.size();
    vector<F> evals;
    F prod = eval_at;
    evals.push_back(eval_at);

    // `prod = \prod_{j} (eval_at - j) for j=1 to len-1`
    // prod=3*2*1=6
    // evals=[3,3-1,3-2]=[3,2,1]
    for (size_t e = 1; e < len; ++e)
    {
        F tmp = eval_at - F(static_cast<uint64_t>(e));
        evals.push_back(tmp);
        prod = prod * tmp;
    }
    F res = F::zero();

    // we want to compute \prod (j!=i) (i-j) for a given i
    //
    // we start from the last step, which is
    //  denom[len-1] = (len-1) * (len-2) *... * 2 * 1
    // the step before that is
    //  denom[len-2] = (len-2) * (len-3) * ... * 2 * 1 * -1
    // and the step before that is
    //  denom[len-3] = (len-3) * (len-4) * ... * 2 * 1 * -1 * -2
    //
    // i.e., for any i, the one before this will be derived from
    //  denom[i-1] = denom[i] * (len-i) / i
    //
    // that is, we only need to store
    // - the last denom for i = len-1, and
    // - the ratio between current step and fhe last step, which is the product of
    //   (len-i) / i from all previous steps and we store this product as a fraction
    //   number to reduce field divisions.

    // We know
    //  - 2^61 < factorial(20) < 2^62
    //  - 2^122 < factorial(33) < 2^123
    // so we will be able to compute the ratio
    //  - for len <= 20 with i64
    //  - for len <= 33 with i128
    //  - for len >  33 with BigInt
    // 直接all in 大整数

    // denom_up=2,denom_down=1
    F denom_up = field_factorial<F>(len - 1);
    F denom_down = F::one();

    // \prod (j!=i) (i-j) for a given i
    for (size_t i = len; i > 0; --i)
    {
        size_t idx = i - 1;
        F term = p_i[idx] * prod * denom_down * ((denom_up * evals[idx]).inverse());
        res = res + term;

        // compute denom for the next step is current_denom * (len-i)/i
        if (idx != 0)
        {
            denom_up = denom_up * (-F(static_cast<uint64_t>(len - idx)));
            denom_down = denom_down * F(static_cast<uint64_t>(idx));
        }
    }
    return res;
}

template <typename F>
class SumCheckVerifier
{
private:
    IOPVerifierState<F> state_;

public:
    // using VPAuxInfo=VPAuxInfo<F>;
    using ProverMessage = IOPProverMessage<F>;
    using Challenge = F;
    using Transcript = SimpleTranscript;
    // using SumCheckSubClaim=SumCheckSubClaim<F>;

    SumCheckVerifier verifier_init(const VPAuxInfo &index_info)
    {
        SumCheckVerifier verifier;
        verifier.state_.round = 1;
        verifier.state_.num_vars = index_info.num_variables;
        verifier.state_.max_degree = index_info.max_degree;
        verifier.state_.finished = false;
        verifier.state_.polynomials_received.reserve(index_info.num_variables);
        verifier.state_.challenge.reserve(index_info.num_variables);
        return verifier;
    }

    /// Run verifier for the current round, given a prover message.
    ///
    /// Note that `verify_round_and_update_state` only samples and stores
    /// challenges; and update the verifier's state accordingly. The actual
    /// verifications are deferred (in batch) to `check_and_generate_subclaim`
    /// at the last step.

    Challenge verify_round_and_update_state(
        const ProverMessage &prover_msg,
        Transcript &transcript)
    {
        // 结束抛出错误

        if (state_.finished)
        {
            throw;
        }

        // In an interactive protocol, the verifier should
        //
        // 1. check if the received 'P(0) + P(1) = expected`.
        // 2. set `expected` to P(r)`
        //
        // When we turn the protocol to a non-interactive one, it is sufficient to defer
        // such checks to `check_and_generate_subclaim` after the last round.

        F challenge = transcript.get_and_append_challenge<F>("Internal round");
        state_.challenge.push_back(challenge);
        state_.polynomials_received.push_back(prover_msg.evaluations);

        if (state_.round == state_.num_vars)
        {
            state_.finished = true;
        }
        else
        {
            state_.round += 1;
        }

        return challenge;
    }

    /// This function verifies the deferred checks in the interactive version of
    /// the protocol; and generate the subclaim. Returns an error if the
    /// proof failed to verify.
    ///
    /// If the asserted sum is correct, then the multilinear polynomial
    /// evaluated at `subclaim.point` will be `subclaim.expected_evaluation`.
    /// Otherwise, it is highly unlikely that those two will be equal.
    /// Larger field size guarantees smaller soundness error.

    SumCheckSubClaim<F> check_and_generate_subclaim(const F &asserted_sum)
    {
        // 交互还没结束，不应该验证

        if (!state_.finished)
        {
            throw;
        }
        if (state_.polynomials_received.size() != state_.num_vars)
        {
            throw;
        }

        // the deferred check during the interactive phase:
        // 2. set `expected` to P(r)`

        vector<F> expected_vec;
        expected_vec.reserve(state_.num_vars + 1);

        for (size_t i = 0; i < state_.num_vars; ++i)
        {
            vector<F> &evaluations = state_.polynomials_received[i];

            /*
            cout<<"debug i :"<<i<<endl;
            for(auto i:evaluations){
                i.print();
            }
            cout<<endl;
            */
            const F &challenge = state_.challenge[i];

            /*
            if(evaluations.size()!=state_.max_degree+1){
                throw;
            }
            */
            F interpolated = interpolate_uni_poly<F>(evaluations, challenge);

            expected_vec.push_back(interpolated);
        }

        // insert the asserted_sum to the first position of the expected vector
        // 将期望值插入到头
        expected_vec.insert(expected_vec.begin(), asserted_sum);

        for (size_t i = 0; i < state_.num_vars; ++i)
        {
            const auto &evaluations = state_.polynomials_received[i];

            /*
            cout<<"check evaluations:"<<endl;
            for(auto& e:evaluations){
                e.print();
            }
            cout<<endl;
            */
            const F &expected = expected_vec[i];

            // the deferred check during the interactive phase:
            // 1. check if the received 'P(0) + P(1) = expected`.
            // 每一轮的和等于上一轮的期望值
            if (evaluations[0] + evaluations[1] != expected)
            {
                /*
                cout<<"debug verifier  i:   "<<i<<endl;
                expected.print();
                cout<<endl;
                (evaluations[0]+evaluations[1]).print();
                cout<<endl;
                */
                throw;
            }
        }
        // the last expected value (not checked within this function) will be included in the
        // subclaim
        return SumCheckSubClaim<F>{
            state_.challenge,
            expected_vec[state_.num_vars]};
    }
};

void debug_interpolate_uni_poly()
{
    cout << "=== Debug interpolate_uni_poly ===" << endl;

    // 最简单的测试：2个点
    vector<libff::alt_bn128_Fq> points = {
        libff::alt_bn128_Fq(1), // f(0)=1
        libff::alt_bn128_Fq(3)  // f(1)=3
    };

    cout << "Input points: ";
    for (const auto &p : points)
    {
        p.print();
        cout << " ";
    }
    cout << endl;

    // 测试在几个点插值
    vector<libff::alt_bn128_Fq> test_points = {
        // libff::alt_bn128_Fq(0),  // 应该返回1
        // libff::alt_bn128_Fq(1),  // 应该返回3
        libff::alt_bn128_Fq(2), // 应该返回5
        libff::alt_bn128_Fq(3)  // 应该返回7
    };

    for (const auto &eval_at : test_points)
    {
        auto result = interpolate_uni_poly(points, eval_at);
        cout << "Interpolate at ";
        eval_at.print();
        cout << " = ";
        result.print();
        cout << endl;
    }
}

#endif // VERIFIER_H