#ifndef STRUCTS_H
#define STRUCTS_H

#include <vector>

#include "arithmetic/virtual_polynomial.h"

// Prover --> Verifier 多项式的求值列表
template <typename F>
struct IOPProverMessage
{
    std::vector<F> evaluations;
};

// IOP Proof：
// P --> V的每一轮信息
// transcript生成的用于求值的点(交互过程生成的评估点)
template <typename F>
struct IOPProof
{
    std::vector<F> point;
    std::vector<IOPProverMessage<F>> proofs;
};

// Prover State:
template <typename F>
struct IOPProverState
{
    std::vector<F> challenges;
    size_t round;
    // pointer to the virtual polynomial
    VirtualPolynomial<F> poly;
    // points with precomputed barycentric weights for extrapolating smaller
    // degree uni-polys to `max_degree + 1` evaluations.
    std::vector<std::pair<std::vector<F>, std::vector<F>>> extrapolation_aux;
};

template <typename F>
struct IOPVerifierState
{
    size_t round;
    size_t num_vars;
    size_t max_degree;
    bool finished;
    vector<std::vector<F>> polynomials_received;
    vector<F> challenge;
};

template <typename F>
struct SumCheckSubClaim
{
    std::vector<F> point;
    F expected_evaluation;
};

#endif // STRUCTS_H