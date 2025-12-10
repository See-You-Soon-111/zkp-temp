#ifndef PROD_CHECK_UTIL_H
#define PROD_CHECK_UTIL_H

#include<memory>
#include"field_and_polynomial/temp.h"
#include <libff/algebra/field_utils/field_utils.hpp>
#include"arithmetic/util.h"
#include"subroutines/poly_iop/structs.h"
#include"arithmetic/virtual_polynomial.h"
#include"transcript/transcript.h"
#include"subroutines/poly_iop/zero_check/zerocheck.h"

using namespace std;

/// Compute multilinear fractional polynomial s.t. frac(x) = f1(x) * ... * fk(x)
/// / (g1(x) * ... * gk(x)) for all x \in {0,1}^n
///
/// The caller needs to sanity-check that the number of polynomials and
/// variables match in fxs and gxs; and gi(x) has no zero entries.
template<typename F>
shared_ptr<DenseMultilinearExtension<F>> compute_frac_poly
(
    const vector<shared_ptr<DenseMultilinearExtension<F>>>& fxs,
    const vector<shared_ptr<DenseMultilinearExtension<F>>>& gxs
){
    size_t num_vars=(*fxs[0]).num_vars();

    size_t num_points=1UL<<num_vars;

    vector<F> f_evals(num_points,F::one());

    for(shared_ptr<DenseMultilinearExtension<F>> fx:fxs){
        auto& evaluations=(*fx).get_evaluations();
        //cout<<evaluations.size();
        for(size_t i=0;i<num_points;++i){
            f_evals[i]*=evaluations[i];
        }
    }

    vector<F> g_evals(num_points,F::one());
    for(shared_ptr<DenseMultilinearExtension<F>> gx:gxs){
        auto& evaluations=(*gx).get_evaluations();
        for(size_t i=0;i<num_points;++i){
            g_evals[i]*=evaluations[i];
        }
    }
    libff::batch_invert(g_evals);

    for(size_t i=0;i<num_points;++i){
        f_evals[i]*=g_evals[i];
    }

    return make_shared<DenseMultilinearExtension<F>>(num_vars,move(f_evals)); 
}

/// Compute the product polynomial `prod(x)` such that
/// `prod(x) = [(1-x1)*frac(x2, ..., xn, 0) + x1*prod(x2, ..., xn, 0)] *
/// [(1-x1)*frac(x2, ..., xn, 1) + x1*prod(x2, ..., xn, 1)]` on the boolean
/// hypercube {0,1}^n
///
/// The caller needs to check num_vars matches in f and g
/// Cost: linear in N.

// 计算论文中的V(1,x)
template<typename F>
shared_ptr<DenseMultilinearExtension<F>> compute_product_poly
(
    shared_ptr<DenseMultilinearExtension<F>>& frac_poly
){
    size_t num_vars=(*frac_poly).num_vars();
    vector<F> frac_evaluations=(*frac_poly).get_evaluations();

    // ===================================
    // prod(x)
    // ===================================
    //
    // `prod(x)` can be computed via recursing the following formula for 2^n-1
    // times
    //
    // `prod(x_1, ..., x_n) :=
    //      [(1-x1)*frac(x2, ..., xn, 0) + x1*prod(x2, ..., xn, 0)] *
    //      [(1-x1)*frac(x2, ..., xn, 1) + x1*prod(x2, ..., xn, 1)]`
    //
    // At any given step, the right hand side of the equation
    // is available via either frac_x or the current view of prod_x

    vector<F> prod_x_evals;
    prod_x_evals.reserve((1UL<<num_vars)-1);

    for(size_t x=0;x<(1UL<<num_vars)-1;++x){
        // sign will decide if the evaluation should be looked up from frac_x or
        // prod_x; x_zero_index is the index for the evaluation (x_2, ..., x_n,
        // 0); x_one_index is the index for the evaluation (x_2, ..., x_n, 1);     
        auto [x_zero_index,x_one_index,sign]=get_index(x,num_vars);

        if(!sign){
            prod_x_evals.push_back(frac_evaluations[x_zero_index]*frac_evaluations[x_one_index]);
        }else{
            // sanity check: if we are trying to look up from the prod_x_evals table,
            // then the target index must already exist
            if(x_zero_index>=prod_x_evals.size()||x_one_index>=prod_x_evals.size()){
                throw;
            }
            prod_x_evals.push_back(prod_x_evals[x_zero_index]*prod_x_evals[x_one_index]);
        }
    }

    // prod(1, 1, ..., 1) := 0
    prod_x_evals.push_back(F::zero());

    return make_shared<DenseMultilinearExtension<F>>(num_vars,move(prod_x_evals));
}


/// generate the zerocheck proof for the virtual polynomial
///    prod(x) - p1(x) * p2(x) + alpha * [frac(x) * g1(x) * ... * gk(x) - f1(x)
/// * ... * fk(x)] where p1(x) = (1-x1) * frac(x2, ..., xn, 0) + x1 * prod(x2,
///   ..., xn, 0), p2(x) = (1-x1) * frac(x2, ..., xn, 1) + x1 * prod(x2, ...,
///   xn, 1)
///
/// Returns proof.
///
/// Cost: O(N)
template<typename F>
pair<IOPProof<F>,VirtualPolynomial<F>> prove_zero_check
(
    vector<shared_ptr<DenseMultilinearExtension<F>>>& fxs,
    vector<shared_ptr<DenseMultilinearExtension<F>>>& gxs,
    shared_ptr<DenseMultilinearExtension<F>>& frac_poly,
    shared_ptr<DenseMultilinearExtension<F>>& prod_x,
    const F& alpha,
    SimpleTranscript& transcript
){
    size_t num_vars=(*frac_poly).num_vars();
    const vector<F> frac_evals=(*frac_poly).get_evaluations();
    const vector<F> prod_evals=(*prod_x).get_evaluations();

    // compute p1(x) = (1-x1) * frac(x2, ..., xn, 0) + x1 * prod(x2, ..., xn, 0)
    // compute p2(x) = (1-x1) * frac(x2, ..., xn, 1) + x1 * prod(x2, ..., xn, 1)
    vector<F> p1_evals(1Ul<<num_vars,F::zero());
    vector<F> p2_evals(1UL<<num_vars,F::zero());

    
    for(size_t x=0;x<(1UL<<num_vars);++x){
        auto [x0,x1,sign]=get_index(x,num_vars);
        if(!sign){
            p1_evals[x]=frac_evals[x0];
            p2_evals[x]=frac_evals[x1];
        }else{
            p1_evals[x]=prod_evals[x0];
            p2_evals[x]=prod_evals[x1];
        }
    }


    shared_ptr<DenseMultilinearExtension<F>> p1=make_shared<DenseMultilinearExtension<F>>(num_vars,move(p1_evals));
    shared_ptr<DenseMultilinearExtension<F>> p2=make_shared<DenseMultilinearExtension<F>>(num_vars,move(p2_evals));

    // compute Q(x)
    // prod(x)
    VirtualPolynomial<F> q_x;
    q_x=q_x.new_from_mle(prod_x,F::one());

    //   prod(x)
    // - p1(x) * p2(x)
    q_x.add_mle_list({p1,p2},-F::one());
   
    //   prod(x)
    // - p1(x) * p2(x)
    // + alpha * frac(x) * g1(x) * ... * gk(x)
    vector<shared_ptr<DenseMultilinearExtension<F>>> mle_list=gxs;
    mle_list.push_back(frac_poly);
    q_x.add_mle_list(mle_list,alpha);

    //   prod(x)
    // - p1(x) * p2(x)
    // + alpha * frac(x) * g1(x) * ... * gk(x)
    // - alpha * f1(x) * ... * fk(x)]
    q_x.add_mle_list(fxs,-alpha);

    
    ZeroCheck<F> zerocheck;
    IOPProof<F> iop_proof=zerocheck.prove(q_x,transcript);

    return make_pair(iop_proof,q_x);

}

#endif