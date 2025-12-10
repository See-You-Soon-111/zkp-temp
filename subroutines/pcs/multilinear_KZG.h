#ifndef MULTILINEAR_KZG_H
#define MULTILINEAR_KZG_H


#include<iostream>
#include<memory>
#include"subroutines/pcs/batching.h"
using namespace std;
using namespace libff; 


/// On input a polynomial `p` and a point `point`, outputs a proof for the
/// same. This function does not need to take the evaluation value as an
/// input.
///
/// This function takes 2^{num_var} number of scalar multiplications over
/// G1:
/// - it proceeds with `num_var` number of rounds,
/// - at round i, we compute an MSM for `2^{num_var - i}` number of G1 elements.
template<typename P,typename scalar_field>
pair<MultilinearKzgProof<P>,scalar_field> open_internal(
    const MultilinearProverParam<P>& prover_param,
    DenseMultilinearExtension<scalar_field>& polynomial,
    const vector<scalar_field>& point
){

    if(polynomial.num_vars()>prover_param.num_vars){
        throw;
    }
    if(polynomial.num_vars()!=point.size()){
        throw;
    }

    size_t nv=polynomial.num_vars();
    // the first `ignored` SRS vectors are unused for opening.
    size_t ignored=prover_param.num_vars-nv+1;
    vector<scalar_field> f=polynomial.get_evaluations();

    vector<G1<P>> proofs;
    proofs.reserve(nv);

    for(size_t i=0;i<nv;++i){
        const scalar_field& point_at_k=point[i];
        const auto& gi=prover_param.power_of_g[ignored+i];

        size_t k=nv-1-i;
        size_t cur_dim=1<<k;
        vector<scalar_field> q(cur_dim,scalar_field::zero());
        vector<scalar_field> r(cur_dim,scalar_field::zero());

        // 这里q 就是证据多项式吧
        for(size_t b=0;b<cur_dim;++b){
            // q[b]=f[1,b]-f[0,b]
            q[b]=f[(b<<1)+1]-f[b<<1];
            // r[b]=f[0,b]+q[b]*p
            r[b]=f[b<<1]+(q[b]*point_at_k);
        }

        f=move(r);

        G1<P> proof_point=libff::multi_exp<G1<P>,scalar_field,multi_exp_method_BDLO12>(
            gi.evals.begin(),gi.evals.end(),
            q.begin(),q.end(),
            1
        );

        proofs.push_back(proof_point);
    }

    scalar_field eval=polynomial.evaluate(point);

    return make_pair(MultilinearKzgProof<P>{proofs},eval);
}
/// Verifies that `value` is the evaluation at `x` of the polynomial
/// committed inside `comm`.
///
/// This function takes
/// - num_var number of pairing product.
/// - num_var number of MSM
template<typename P,typename scalar_field>
bool verify_internal(
    const MultilinearVerifierParam<P>& verifier_param,
    const Commitment<P>& commitment,
    const vector<scalar_field>& point,
    const scalar_field& value,
    const MultilinearKzgProof<P>& proof
){
    size_t num_var=point.size();
    
    if(num_var>verifier_param.num_vars){
        throw;
    }
    
    size_t scalar_size=scalar_field::num_bits;
    size_t window_size=libff::get_exp_window_size<G2<P>>(num_var);
    auto h_table=libff::get_window_table<G2<P>>(scalar_size,window_size,verifier_param.h);
    // Compute h_mul=h^{point[0]} ,..., h^{point[nv-1]}
    vector<G2<P>> h_mul=libff::batch_exp<G2<P>,scalar_field>(scalar_size,window_size,h_table,point);

    size_t ignored=verifier_param.num_vars-num_var;

    // Compute h_vec[i]=h_mask[i]-h_mul[i]
    vector<G2<P>> h_vec;
    h_vec.reserve(num_var);
    for(size_t i=0;i<num_var;++i){
        G2<P> h_mask_g2=verifier_param.h_mask[ignored+i];
        h_vec.push_back(h_mask_g2-h_mul[i]);
    }

    // Prepare pairing for the proof elements
    vector<pair<G1_precomp<P>,G2_precomp<P>>> pairings;
    pairings.reserve(num_var+1);

    // Add pairings for each proof element
    for(size_t i=0;i<num_var;++i){
        G1_precomp<P> g1_pre=P::precompute_G1(proof.proofs[i]);
        G2_precomp<P> g2_pre=P::precompute_G2(h_vec[i]);
        pairings.emplace_back(g1_pre,g2_pre);
    }


    pairings.emplace_back(
        P::precompute_G1(value*verifier_param.g-commitment.point),
        P::precompute_G2(verifier_param.h)
    );

    vector<G1_precomp<P>> g1_ele;
    vector<G2_precomp<P>> g2_ele;
    g1_ele.reserve(pairings.size());
    g2_ele.reserve(pairings.size());

    for(const auto& pairing:pairings){
        g1_ele.push_back(pairing.first);
        g2_ele.push_back(pairing.second);
    }

    GT<P> res=GT<P>::one();
    for(size_t i=0;i<pairings.size();++i){
        auto miller_result=P::miller_loop(g1_ele[i],g2_ele[i]);
        auto result=P::final_exponentiation(miller_result);
        res=res*result;
    }

    return (res==GT<P>::one());

}

template<typename P,typename scalar_field>
class MultilinearKzgPCS{
public:
    StructuredReferenceString<P,scalar_field> gen_srs_for_test(size_t log_size){
        StructuredReferenceString<P,scalar_field> srs;
        return srs.get_srs_for_test(log_size);
    }

    pair<MultilinearProverParam<P>,MultilinearVerifierParam<P>> trims(
        StructuredReferenceString<P,scalar_field>& srs,
        size_t supported_num_vars
    ){
        return srs.trim(supported_num_vars);
    }

    Commitment<P> commit(
        MultilinearProverParam<P>& prover_param,
        shared_ptr<DenseMultilinearExtension<scalar_field>>& poly
    ){
        if (prover_param.num_vars < poly->num_vars()) {
            throw std::invalid_argument(
                "MlE length (" + std::to_string(poly->num_vars()) + 
                ") exceeds param limit (" + std::to_string(prover_param.num_vars) + ")"
            );
        }

        size_t ignored=prover_param.num_vars-(*poly).num_vars();
        vector<scalar_field> scalars=(*poly).get_evaluations();

        G1<P> commitment_point=libff::multi_exp<G1<P>,scalar_field,multi_exp_method_BDLO12>(
            prover_param.power_of_g[ignored].evals.begin(),prover_param.power_of_g[ignored].evals.end(),
            scalars.begin(),scalars.end(),
            1
        );
        
        return Commitment<P>{commitment_point};

    }

    pair<MultilinearKzgProof<P>,scalar_field> open(
        const MultilinearProverParam<P>& prover_param,
        const shared_ptr<DenseMultilinearExtension<scalar_field>>& polynomial,
        const vector<scalar_field>& point
    ){
        return open_internal<P,scalar_field>(prover_param,*polynomial,point);
    }

    BatchProof<P,scalar_field,MultilinearKzgPCS<P,scalar_field>> multi_open(
        const MultilinearProverParam<P>& prover_param,
        const vector<shared_ptr<DenseMultilinearExtension<scalar_field>>>& polynomials,
        const vector<vector<scalar_field>>& points,
        const vector<scalar_field>& evals,
        SimpleTranscript& transcript
    ){
        return multi_open_internal<P,scalar_field,MultilinearKzgPCS<P,scalar_field>>(
            prover_param,
            polynomials,
            points,
            evals,
            transcript
        );
    }

    bool verify(
        const MultilinearVerifierParam<P>& verifier_param,
        const Commitment<P>& commitment,
        const vector<scalar_field>& point,
        const scalar_field& value,
        const MultilinearKzgProof<P>& proof
    ){
        return verify_internal<P,scalar_field>(
            verifier_param,
            commitment,
            point,
            value,
            proof
        );
    }

    bool batch_verify(
        const MultilinearVerifierParam<P>& verifier_param,
        const vector<Commitment<P>>& commitments,
        const vector<vector<scalar_field>>& points,
        const BatchProof<P,scalar_field,MultilinearKzgPCS<P,scalar_field>>& batch_proof,
        SimpleTranscript& transcript
    ){
        return batch_verify_internal<P,scalar_field,MultilinearKzgPCS<P,scalar_field>>(
            verifier_param,
            commitments,
            points,
            batch_proof,
            transcript
        );
    }
};







#endif