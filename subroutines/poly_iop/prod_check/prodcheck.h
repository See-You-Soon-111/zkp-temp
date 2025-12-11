#ifndef PRODCHECK_H
#define PRODCHECK_H

#include<iostream>
#include<memory>
#include"subroutines/poly_iop/prod_check/prod_check_util.h"
#include"subroutines/poly_iop/zero_check/zerocheck.h"
#include"subroutines/pcs/batching.h"
#include"subroutines/pcs/multilinear_KZG.h"

using namespace std;

/// A product check subclaim consists of
/// - A zero check IOP subclaim for the virtual polynomial
/// - The random challenge `alpha`
/// - A final query for `prod(1, ..., 1, 0) = 1`.
// Note that this final query is in fact a constant that
// is independent from the proof. So we should avoid
// (de)serialize it.
template<typename F>
struct ProductCheckSubClaim{
    ZeroCheckSubClaim<F> zero_check_sub_claim;
    pair<vector<F>,F> final_query;
    F alpha;
};

/// A product check proof consists of
/// - a zerocheck proof
/// - a product polynomial commitment
/// - a polynomial commitment for the fractional polynomial
template<typename P,typename scalar_field>
struct ProductCheckProof{
    IOPProof<scalar_field> zero_check_proof;
    Commitment<P> prod_x_com;
    Commitment<P> frac_comm;
};


/// `(f1, f2, ..., fk)` and `(g1, ..., gk)` satisfy:
/// \prod_{x \in {0,1}^n} f1(x) * ... * fk(x) = \prod_{x \in {0,1}^n} g1(x) *
/// ... * gk(x)
///
/// A ProductCheck is derived from ZeroCheck.
///
/// Prover steps:
/// 1. build MLE `frac(x)` s.t. `frac(x) = f1(x) * ... * fk(x) / (g1(x) * ... *
///    gk(x))` for all x \in {0,1}^n 2. build `prod(x)` from `frac(x)`, where
///    `prod(x)` equals to `v(1,x)` in the paper
/// 2. push commitments of `frac(x)` and `prod(x)` to the transcript,    and
///    `generate_challenge` from current transcript (generate alpha) 3. generate
///    the zerocheck proof for the virtual polynomial:
///
///    Q(x) = prod(x) - p1(x) * p2(x) + alpha * frac(x) * g1(x) * ... * gk(x)
///     - alpha * f1(x) * ... * fk(x)
///
///    where p1(x) = (1-x1) * frac(x2, ..., xn, 0) + x1 * prod(x2, ..., xn, 0),
///    and p2(x) = (1-x1) * frac(x2, ..., xn, 1) + x1 * prod(x2, ..., xn, 1)
///
/// Verifier steps:
/// 1. Extract commitments of `frac(x)` and `prod(x)` from the proof, push them
///    to the transcript
/// 2. `generate_challenge` from current transcript (generate alpha)
/// 3. `verify` to verify the zerocheck proof and generate the subclaim for
///    polynomial evaluations

template<typename P,typename scalar_field,typename PCS>
class ProductCheck{
public:
    SimpleTranscript init_transcript(){
        return SimpleTranscript("Initializing ProductCheck transcript");
    }

    tuple
    <
    ProductCheckProof<P,scalar_field>,
    shared_ptr<DenseMultilinearExtension<scalar_field>>,
    shared_ptr<DenseMultilinearExtension<scalar_field>>
    > prove(
        MultilinearProverParam<P>& pcs_param,
        vector<shared_ptr<DenseMultilinearExtension<scalar_field>>>& fxs,
        vector<shared_ptr<DenseMultilinearExtension<scalar_field>>>& gxs,
        SimpleTranscript& transcript
    ){
        /*
        if(fxs.empty()||fxs.size()!=gxs.size()){

        }
        */
        
        // compute the fractional polynomial frac_p s.t.
        // frac_p(x) = f1(x) * ... * fk(x) / (g1(x) * ... * gk(x))  
        shared_ptr<DenseMultilinearExtension<scalar_field>> frac_poly=compute_frac_poly<scalar_field>(fxs,gxs);

        // compute the product polynomial
        shared_ptr<DenseMultilinearExtension<scalar_field>> prod_x=compute_product_poly<scalar_field>(frac_poly);

        // generate challenge
        PCS pcs;
        Commitment<P> frac_comm=pcs.commit(pcs_param,frac_poly);
        Commitment<P> prod_x_comm=pcs.commit(pcs_param,prod_x);
        transcript.append_serializable_element("frac(x)",frac_comm);
        transcript.append_serializable_element("prod(x)",prod_x_comm);
        scalar_field alpha=transcript.get_and_append_challenge<scalar_field>("alpha");

        // build the zero-check proof
        auto [zero_check_proof,_]=prove_zero_check<scalar_field>(fxs,gxs,frac_poly,prod_x,alpha,transcript);


        return make_tuple(
            ProductCheckProof<P,scalar_field>{
                zero_check_proof,
                prod_x_comm,
                frac_comm
            },
            prod_x,
            frac_poly
        );
    }

    ProductCheckSubClaim<scalar_field> verify(
        ProductCheckProof<P,scalar_field>& proof,
        VPAuxInfo& aux_info,
        SimpleTranscript& transcript
    ){
        // update transcript and generate challenge
        transcript.append_serializable_element("frac(x)",proof.frac_comm);
        transcript.append_serializable_element("prod(x)",proof.prod_x_com);
        scalar_field alpha=transcript.get_and_append_challenge<scalar_field>("alpha");

        // invoke the zero check on the iop_proof
        // the virtual poly info for Q(x)
        ZeroCheck<scalar_field> zero_check;
        ZeroCheckSubClaim<scalar_field> zero_check_sub_claim=zero_check.verify(proof.zero_check_proof,aux_info,transcript);

        // the final query is on prod_x
        vector<scalar_field> final_query(aux_info.num_variables,scalar_field::one());
        final_query[0]=scalar_field::zero();
        scalar_field final_eval=scalar_field::one();

        return ProductCheckSubClaim<scalar_field>{
            zero_check_sub_claim,
            {final_query,final_eval},
            alpha
        };
    } 

};

#endif