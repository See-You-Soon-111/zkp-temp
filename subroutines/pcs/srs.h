#ifndef SRS_H
#define SRS_H

#include<iostream>
#include<memory>
#include<list>

#include"arithmetic/virtual_polynomial.h"
#include <libff/algebra/scalar_multiplication/multiexp.hpp>

// 用于测试
#include <libff/algebra/curves/bls12_381/bls12_381_pp.hpp> 

using namespace std;
using namespace libff; 

/// Generate eq(t,x), a product of multilinear polynomials with fixed t.
/// eq(a,b) is takes extensions of a,b in {0,1}^num_vars such that if a and b in
/// {0,1}^num_vars are equal then this polynomial evaluates to 1.
template<typename F>
vector<DenseMultilinearExtension<F>> eq_extension(const vector<F>& t){
    size_t dim=t.size();
    vector<DenseMultilinearExtension<F>> result;
    result.reserve(dim);

    for(size_t i=0;i<dim;++i){
        F ti=t[i];
        vector<F> poly(1<<dim);

        for(size_t x=0;x<(1UL<<dim);++x){
            F xi=((x>>i)&1)==1?F::one():F::zero();
            poly[x]=ti*xi+ti*xi-xi-ti+F::one();
        }
        result.push_back(DenseMultilinearExtension<F>(dim,move(poly)));
    }

    return result;
}



/// fix first `pad` variables of `poly` represented in evaluation form to zero
template<typename F>
// poly.size()=2^k
vector<F> remove_dummy_variable(const vector<F>& poly,size_t pad){
    if(pad==0){
        return poly;
    }

    size_t nv=log2(poly.size())-pad;
    vector<F> result;
    result.reserve(1<<nv);
    for(size_t x=0;x<(1UL<<nv);++x){
        result.push_back(poly[x<<pad]);
    }

    return result;
}


// Evaluations over {0,1}^n for G1 or G2
template<typename C>
struct Evaluations{
    vector<C> evals;
};

// Prover Parameters
template<typename P>
struct MultilinearProverParam{
    size_t num_vars;
    /// `pp_{0}`, `pp_{1}`, ...,pp_{nu_vars} defined
    /// by XZZPD19 where pp_{nv-0}=g and
    /// pp_{nv-i}=g^{eq((t_1,..t_i),(X_1,..X_i))}
    vector<Evaluations<G1<P>>> power_of_g;
    /// generator for G1
    G1<P> g;
    /// generator for G2
    G2<P> h;
};

// Universal Parameter
template<typename P>
struct MultilinearUniversalParams{
    MultilinearProverParam<P> prover_param;
    /// h^randomness: h^t1, h^t2, ..., **h^{t_nv}**
    vector<G2<P>> h_mask;
};


/// Verifier Parameters
template<typename P>
struct MultilinearVerifierParam{
    size_t num_vars;
    G1<P> g;
    G2<P> h;
    vector<G2<P>> h_mask;
};


template<typename P,typename scalar_field>
class StructuredReferenceString{
private:
    MultilinearUniversalParams<P> universal_params_;
public:
    using ProverParam=MultilinearProverParam<P>;
    using VerifierParam=MultilinearVerifierParam<P>;

    StructuredReferenceString()=default;

    StructuredReferenceString(const MultilinearUniversalParams<P>& params)
    :universal_params_(params){}

    StructuredReferenceString(MultilinearUniversalParams<P>&& params)
    :universal_params_(move(params)){}

    const MultilinearUniversalParams<P>& universal_params() const {
        return universal_params_;
    }

    /// Extract the prover parameters from the public parameters.
    ProverParam extract_prover_param(size_t supported_num_vars){
        ProverParam prover_param=universal_params_.prover_param;

        size_t to_reduce=prover_param.num_vars-supported_num_vars;
        ProverParam param;
        param.num_vars=supported_num_vars;
        param.g=prover_param.g;
        param.h=prover_param.h;

        param.power_of_g.assign(prover_param.power_of_g.begin()+to_reduce,prover_param.power_of_g.end());

        return param;
    }
    /// Extract the verifier parameters from the public parameters.
    VerifierParam extract_verifier_param(size_t supported_num_vars){
        ProverParam prover_param=universal_params_.prover_param;

        size_t to_reduce=prover_param.num_vars-supported_num_vars;

        VerifierParam param;
        param.num_vars=supported_num_vars;
        param.g=prover_param.g;
        param.h=prover_param.h;

        param.h_mask.assign(universal_params_.h_mask.begin()+to_reduce,universal_params_.h_mask.end());
    }
    /// Trim the universal parameters to specialize the public parameters
    /// for multilinear polynomials to the given `supported_num_vars`, and
    /// returns committer key and verifier key. `supported_num_vars` should
    /// be in range `1..=params.num_vars`
    pair<ProverParam,VerifierParam> trim(size_t supported_num_vars){
        ProverParam prover_param=universal_params_.prover_param;

        if (supported_num_vars == 0 || supported_num_vars > prover_param.num_vars) {
            throw std::invalid_argument(
                "SRS does not support target number of vars " + 
                std::to_string(supported_num_vars) +
                ", max supported: " + std::to_string(prover_param.num_vars)
            );
        }
        
        size_t to_reduce=prover_param.num_vars-supported_num_vars;

        ProverParam ck;
        ck.num_vars=supported_num_vars;
        ck.g=prover_param.g;
        ck.h=prover_param.h;
        ck.power_of_g.assign(prover_param.power_of_g.begin()+to_reduce,prover_param.power_of_g.end());

        VerifierParam vk;
        vk.num_vars=supported_num_vars;
        vk.g=prover_param.g;
        vk.h=prover_param.h;
        vk.h_mask.assign(universal_params_.h_mask.begin()+to_reduce,universal_params_.h_mask.end());

        return {move(ck),move(vk)};
    }


    StructuredReferenceString get_srs_for_test(size_t num_vars){
        
        if(num_vars==0){
            cout<<"const polynomial not supported"<<endl;
            throw;
        }

        G1<P> g=G1<P>::one();
        G2<P> h=G2<P>::one();

        vector<Evaluations<G1<P>>> power_of_g;

        vector<scalar_field> t;
        t.reserve(num_vars);
        for(size_t i=0;i<num_vars;++i){
            t.push_back(scalar_field::random_element());
        }

        vector<DenseMultilinearExtension<scalar_field>> eq_polys=eq_extension<scalar_field>(t);

        list<DenseMultilinearExtension<scalar_field>> eq_list(eq_polys.begin(),eq_polys.end());
        list<vector<scalar_field>> eq_arr;
        vector<scalar_field> base=eq_list.back().get_evaluations();
        eq_list.pop_back();

        // 构建完整的eq，也就是将每个(1-x_i)(1-t_i)+x_i*t_i 乘起来
        for(size_t i=num_vars;i>0;--i){
            size_t idx=i-1;
            // 这里好像是定义 eq(i,x)=eq(t_i,x)
            eq_arr.push_front(remove_dummy_variable<scalar_field>(base,idx));
            if(idx!=0){
                vector<scalar_field> mul=eq_list.back().get_evaluations();
                eq_list.pop_back();

                vector<scalar_field> new_base;
                new_base.reserve(base.size());

                for(size_t j=0;j<base.size();++j){
                    new_base.push_back(base[j]*mul[j]);
                }
                base=move(new_base);
            }
        }
        
        // 汇总所有评估值以及总的标量数量
        // pp_power=[eq0[0],...eq0[size0-1],eq1[0],...,eq1[size1-1],...]
        // total_scalar=pp_power.size()
        vector<scalar_field> pp_powers;
        size_t total_scalar=0;

        for(size_t i=0;i<num_vars;++i){
            vector<scalar_field> eq=eq_arr.front();
            eq_arr.pop_front();

            size_t size=1UL<<(num_vars-i);
            for(size_t x=0;x<size;++x){
                pp_powers.push_back(eq[x]);
            }
            total_scalar+=size;
        }

        size_t scalar_bits=scalar_field::num_bits;

        size_t windows_size=libff::get_exp_window_size<G1<P>>(total_scalar);
        auto g_table=libff::get_window_table<G1<P>>(scalar_bits,windows_size,g);

       
        // 计算 g^pp_power
        auto pp_g=libff::batch_exp<G1<P>,scalar_field>(scalar_bits,windows_size,g_table,pp_powers);

        /*
        for(auto& point:pp_g){
            point.to_affine_coordinates();
        }
        */
        // power_of_g[i]=[g^eqi[0],...g^eqi[sizei-1]
        size_t start=0;
        for(size_t i=0;i<num_vars;++i){
            size_t size=1UL<<(num_vars-i);
            Evaluations<G1<P>> pp_k_g;
            pp_k_g.evals.assign(pp_g.begin()+start,pp_g.begin()+start+size);

            // 验证正确性
            vector<scalar_field> zero_vec(num_vars-i,scalar_field::zero());
            scalar_field t_eval_0=eq_eval<scalar_field>(zero_vec,vector<scalar_field>(t.begin()+i,t.end()));
            assert(t_eval_0*g==pp_k_g.evals[0] && "PP correctness check failed");

            power_of_g.push_back(pp_k_g);
            start+=size;
        }
        
        // 添加生成元
        Evaluations<G1<P>> gg;
        gg.evals={g};
        power_of_g.push_back(gg);

        // 构建Prover参数
        ProverParam pp;
        pp.num_vars=num_vars;
        pp.g=g;
        pp.h=h;
        pp.power_of_g=move(power_of_g);

 
        size_t vp_window_size=libff::get_exp_window_size<G2<P>>(num_vars);
        auto h_table=libff::get_window_table<G2<P>>(scalar_bits,vp_window_size,h);

        auto h_mask=libff::batch_exp<G2<P>,scalar_field>(scalar_bits,vp_window_size,h_table,t);
        
        // 构建通用参数
        MultilinearUniversalParams<P> universal_params;
        universal_params.prover_param=move(pp);
        universal_params.h_mask=move(h_mask);

        return StructuredReferenceString(move(universal_params));

    }



};
template<typename P,typename scalar_field>
void print_h_mask(StructuredReferenceString<P,scalar_field>& srs){
    cout<<" h_mask: "<<endl;
    vector<G2<P>> h_mask=srs.universal_params().h_mask;
    for(auto& h:h_mask){
        h.to_affine_coordinates();
        h.print();
    }
    cout<<endl;
}

template<typename P,typename scalar_field>
void test_srs_for_check_h_mask(size_t num_vars){
    StructuredReferenceString<P,scalar_field> srs;
    srs=srs.get_srs_for_test(num_vars);
    print_h_mask(srs);
}


#endif