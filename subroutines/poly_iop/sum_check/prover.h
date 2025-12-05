#ifndef PROVER_H
#define PROVER_H

#include <vector>
#include <optional>
#include "arithmetic/virtual_polynomial.h"
#include "subroutines/poly_iop/structs.h"
#include <libff/algebra/field_utils/field_utils.hpp>
#include "arithmetic/multilinear_polynomial.h"
using namespace std;

// 计算w_j=1/prod_{i\neq j}(x_i-x_j)
template <typename F>
vector<F> barycenter_weights(const vector<F> &points)
{
    vector<F> weights;
    weights.reserve(points.size());

    for (size_t j = 0; j < points.size(); ++j)
    {
        F product = F::one();
        const F &point_j = points[j];

        for (size_t i = 0; i < points.size(); ++i)
        {
            if (i != j)
            {
                product = product * (point_j - points[i]);
            }
        }

        weights.push_back(product);
    }

    // 域批量求逆
    libff::batch_invert(weights);

    return weights;
}

template <typename F>
F extrapolate(
    const vector<F> &points,
    const vector<F> &weights,
    const vector<F> &evals,
    const F &at)
{
    if (points.size() != weights.size() || points.size() != evals.size())
    {
        throw;
    }

    vector<F> coeffs;
    coeffs.reserve(points.size());

    // 计算coeffs[i]=1/(at-points[i])
    for (F point : points)
    {
        coeffs.push_back(at - point);
    }

    libff::batch_invert(coeffs);

    // 计算coeffs[i]=w_i/(at-points[i])
    F sum = F::zero();
    for (size_t i = 0; i < coeffs.size(); ++i)
    {
        coeffs[i] = coeffs[i] * weights[i];
        sum += coeffs[i];
    }

    // 计算 sum_inv=1/sum(w_i/(at-points[i]))
    F sum_inv = sum.inverse();

    // 计算 sum(coeffs[i]*f_i)=sum((w_i*f_i)/(at-points[i]))
    F numerator = F::zero();
    for (size_t i = 0; i < coeffs.size(); ++i)
    {
        numerator = numerator + (coeffs[i] * evals[i]);
    }

    return numerator * sum_inv;
}

template <typename F>
class SumCheckProver
{
private:
    IOPProverState<F> state_;

public:
    IOPProverState<F> &get_state()
    {
        return state_;
    }
    // using VirtualPolynomial=VirtualPolynomial<F>;
    using ProverMessage = IOPProverMessage<F>;
    using ProverState = IOPProverState<F>;

    SumCheckProver prover_init(const VirtualPolynomial<F> &polynomial)
    {
        // 常多项式报错
        if (polynomial.aux_info.num_variables == 0)
        {
            throw;
        }
        SumCheckProver prover;
        prover.state_.challenges.reserve(polynomial.aux_info.num_variables);
        prover.state_.round = 0;
        prover.state_.poly = polynomial;

        for (size_t degree = 1; degree < polynomial.aux_info.max_degree; ++degree)
        {
            vector<F> points;
            for (size_t i = 0; i <= degree; ++i)
            {
                points.push_back(F(static_cast<uint64_t>(i)));
            }
            vector<F> weights = barycenter_weights<F>(points);
            prover.state_.extrapolation_aux.emplace_back(move(points), move(weights));
        }

        return prover;
    }

    // 从V收到message，生成Prover message，并进入下一轮
    ProverMessage prover_round_and_update_state(const optional<F> &challenge)
    {
        // 轮数不应该超过变量数
        if (state_.round >= state_.poly.aux_info.num_variables)
        {
            throw;
        }

        // Step 1:
        // fix argument and evaluate f(x) over x_m = r; where r is the challenge
        // for the current round, and m is the round number, indexed from 1
        //
        // i.e.:
        // at round m <= n, for each mle g(x_1, ... x_n) within the flattened_mle
        // which has already been evaluated to
        //
        //    g(r_1, ..., r_{m-1}, x_m ... x_n)
        //
        // eval g over r_m, and mutate g to g(r_1, ... r_m,, x_{m+1}... x_n)

        vector<DenseMultilinearExtension<F>> flattened_ml_extensions;
        flattened_ml_extensions.reserve(state_.poly.flattened_ml_extensions.size());
        for (const auto &ext : state_.poly.flattened_ml_extensions)
        {
            flattened_ml_extensions.push_back(*ext);
        }

        // challege不为空
        if (challenge.has_value())
        {
            // 协议从P开始
            if (state_.round == 0)
            {
                throw;
            }
            state_.challenges.push_back(challenge.value());
            F r = state_.challenges[state_.round - 1];
            // 固定变量
            for (auto &mle : flattened_ml_extensions)
            {
                mle = fix_variables_no_par<F>(mle, vector<F>{r});
            }
        }
        else if (state_.round > 0)
        {
            // V的消息为空
            throw;
        }
        /*
        cout<<"check mle:"<<endl;
        for(DenseMultilinearExtension<F> DM:flattened_ml_extensions){
            for(auto& e:DM.get_evaluations()){
                e.print();
            }
        }
        */

        state_.round++;

        const auto &products_list = state_.poly.products;
        vector<F> products_sum(state_.poly.aux_info.max_degree + 1, F::zero());

        /*
        cout<<"check products:"<<endl;
        state_.poly.printproduct();
        cout<<endl;
        */

        // Step 2: generate sum for the partial evaluated polynomial:
        // f(r_1, ... r_m,, x_{m+1}... x_n)

        // 循环每个乘积项
        for (const auto &[coefficient, product_indices] : products_list)
        {
            size_t remaining_vars = state_.poly.aux_info.num_variables - state_.round;
            size_t num_points = 1ULL << remaining_vars;

            vector<F> sum(product_indices.size() + 1, F::zero());
            // 乘积项中的每个mle (例如[g_1,g_2])，
            // 计算 acc[i]=sum g_1(r_1,r_2,...,r_m,i,vec{b})*g_2(r_1,...,r_m,i,vec{b})

            /*
            cout<<"check num_point:"<<endl;
            cout<<num_points<<endl;
            */
            for (size_t b = 0; b < num_points; ++b)
            {

                vector<pair<F, F>> buf; //(eval,step)
                for (size_t idx : product_indices)
                {
                    const auto &table = flattened_ml_extensions[idx];
                    F eval = table.get_evaluations()[b << 1];
                    F step = table.get_evaluations()[(b << 1) + 1] - table.get_evaluations()[b << 1];
                    buf.emplace_back(eval, step);
                }

                F product = coefficient;
                for (const auto &[eval, _] : buf)
                {
                    product = product * eval;
                }
                sum[0] = sum[0] + product;

                for (size_t i = 1; i <= product_indices.size(); ++i)
                {
                    // 更新eval
                    for (auto &[eval, step] : buf)
                    {
                        eval = eval + step;
                    }
                    product = coefficient;
                    for (const auto &[eval, _] : buf)
                    {
                        product = product * eval;
                    }
                    sum[i] = sum[i] + product;
                }
            }

            /*
            cout<<"check sum product:"<<endl;
            for(auto & s:sum){
                s.print();
            }
            cout<<endl;
            */

            if (!product_indices.empty() && product_indices.size() - 1 < state_.extrapolation_aux.size())
            {
                const auto &[points, weights] = state_.extrapolation_aux[product_indices.size() - 1];
                for (size_t i = 0; i < state_.poly.aux_info.max_degree; ++i)
                {
                    F at = F(static_cast<uint64_t>(product_indices.size() + 1 + i));
                    F extrapolated = extrapolate<F>(points, weights, sum, at);
                    if (product_indices.size() + 1 + i < products_sum.size())
                    {
                        products_sum[product_indices.size() + 1 + i] += extrapolated;
                    }
                }
            }

            for (size_t i = 0; i < min(sum.size(), products_sum.size()); ++i)
            {
                products_sum[i] += sum[i];
            }
        }
        /*
        cout<<"debug prover message:"<<endl;
        for(auto& e:products_sum){
            e.print();
        }
        cout<<endl;
        */
        // 更新Prover状态
        state_.poly.flattened_ml_extensions.clear();
        for (const auto &ext : flattened_ml_extensions)
        {
            state_.poly.flattened_ml_extensions.push_back(make_shared<DenseMultilinearExtension<F>>(ext));
        }

        return ProverMessage{products_sum};
    }
};

#endif // PROVER_H