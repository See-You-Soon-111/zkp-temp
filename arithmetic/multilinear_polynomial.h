#ifndef MULTILINEAR_POLYNOMIAL_H
#define MULTILINEAR_POLYNOMIAL_H

#include <iostream>
#include <random>
#include <memory>
#include <cassert>
#include <vector>
#include <utility>

// 假设这些头文件存在
#include "field_and_polynomial/temp.h"

using namespace std;

// 随机生成每个MLE在各个布尔顶点上的值
// 计算 sum_{x \in B_\mu} { \prod_i MLE_i(x) }
// 并返回MLE列表
template <typename F>
pair<vector<shared_ptr<DenseMultilinearExtension<F>>>, F>
random_mle_list(size_t nv, size_t degree)
{

    vector<vector<F>> multiplicands(degree);
    for (auto &vec : multiplicands)
    {
        vec.reserve(1 << nv);
    }
    F sum = F::zero();
    // 遍历布尔超立方体的所有点 (2^nv 个点)
    for (size_t i = 0; i < (1UL << nv); ++i)
    {
        F product = F::one();

        // 为每个多项式生成随机值并计算乘积
        for (auto &eval_vec : multiplicands)
        {
            F val = F::random_element();
            eval_vec.push_back(val);
            product *= val;
        }
        sum += product;
    }

    // 构建多项式列表
    vector<shared_ptr<DenseMultilinearExtension<F>>> list;
    list.reserve(degree);
    for (auto &eval_vec : multiplicands)
    {
        list.push_back(make_shared<DenseMultilinearExtension<F>>(nv, move(eval_vec)));
    }
    return {list, sum};
}

// 创建和为0的MLEs：固定MLE_1=0即可
template <typename F>
vector<shared_ptr<DenseMultilinearExtension<F>>>
random_zero_mle_list(size_t nv, size_t degree)
{
    vector<vector<F>> multiplicands(degree);
    for (auto &vec : multiplicands)
    {
        vec.reserve(1 << nv);
    }

    for (size_t i = 0; i < (1UL << nv); ++i)
    {
        // MLE_1=0
        multiplicands[0].push_back(F::zero());
        // 其余MLE随机生成
        for (size_t j = 1; j < degree; ++j)
        {
            multiplicands[j].push_back(F::random_element());
        }
    }
    // 构建多项式列表
    vector<shared_ptr<DenseMultilinearExtension<F>>> list;
    list.reserve(degree);
    for (auto &eval_vec : multiplicands)
    {
        list.push_back(make_shared<DenseMultilinearExtension<F>>(nv, move(eval_vec)));
    }

    return list;
}

// 表示恒等置换的多项式,每个chunk生成一个MLE
template <typename F>
vector<F> identity_permutation(size_t num_var, size_t num_chunks)
{
    size_t len = num_chunks * (1ULL << num_var);
    vector<F> result;
    result.reserve(len);

    for (size_t i = 0; i < len; ++i)
    {
        result.push_back(F(i));
    }
    return result;
}

template <typename F>
vector<shared_ptr<DenseMultilinearExtension<F>>>
identity_permutation_mles(size_t num_vars, size_t num_chunks)
{
    vector<shared_ptr<DenseMultilinearExtension<F>>> res;
    res.reserve(num_chunks);

    for (size_t i = 0; i < num_chunks; ++i)
    {
        uint64_t shift = i * (1ULL << num_vars);
        vector<F> s_id_vec;
        s_id_vec.reserve(1ULL << num_vars);

        // 生成从 shift 到 shift + 2^num_vars - 1 的序列
        for (uint64_t j = shift; j < shift + (1ULL << num_vars); ++j)
        {
            s_id_vec.push_back(F(j));
        }

        res.push_back(make_shared<DenseMultilinearExtension<F>>(num_vars, move(s_id_vec)));
    }

    return res;
}

// 代表随机置换的多项式
template <typename F>
vector<F> random_permutation(size_t num_vars, size_t num_chunks)
{
    size_t len = num_chunks * (1ULL << num_vars);
    vector<F> s_id_vec;
    s_id_vec.reserve(len);
    // 创建恒等置换[0,1,2,...,len-1]
    for (size_t i = 0; i < len; ++i)
    {
        s_id_vec.push_back(F(i));
    }
    // 随机打乱排序
    vector<F> s_perm_vec;
    s_perm_vec.reserve(len);
    // 洗牌
    for (size_t i = len; i > 0; --i)
    {   
        random_device rd;
        mt19937 gen(rd());
        uniform_int_distribution<size_t> dist(0, s_id_vec.size() - 1);
        size_t index = dist(gen);
        s_perm_vec.push_back(move(s_id_vec[index]));
        s_id_vec.erase(s_id_vec.begin() + index);
    }
    return s_perm_vec;
}

template <typename F>
vector<shared_ptr<DenseMultilinearExtension<F>>>
random_permutation_mles(size_t num_vars, size_t num_chunks)
{
    vector<F> s_perm_vec = random_permutation<F>(num_vars, num_chunks);
    vector<shared_ptr<DenseMultilinearExtension<F>>> res;
    res.reserve(num_chunks);

    size_t n = 1ULL << num_vars;
    for (size_t i = 0; i < num_chunks; ++i)
    {
        vector<F> chunk_evaluations(
            s_perm_vec.begin() + i * n,
            s_perm_vec.begin() + i * n + n);
        res.push_back(make_shared<DenseMultilinearExtension<F>>(num_vars, move(chunk_evaluations)));
    }
    return res;
}

// 计算MLE(partial_point,rest_var)
template <typename F>
DenseMultilinearExtension<F> fix_variables_no_par(
    const DenseMultilinearExtension<F> &poly,
    const vector<F> &partial_point)
{
    assert(partial_point.size() <= poly.num_vars() &&
           "invalid size of partial point");

    size_t nv = poly.num_vars();
    vector<F> poly_evals = poly.get_evaluations();
    size_t dim = partial_point.size();

    for (size_t i = 1; i <= dim; ++i)
    {
        const F &r = partial_point[i - 1];
        for (size_t b = 0; b < (1ULL << (nv - i)); ++b)
        {
            poly_evals[b] = poly_evals[b << 1] + (poly_evals[(b << 1) + 1] - poly_evals[b << 1]) * r;
        }
    }

    return DenseMultilinearExtension<F>(
        nv - dim,
        std::vector<F>(poly_evals.begin(), poly_evals.begin() + (1ULL << (nv - dim))));
}
// 固定所有变量:MLE(point)
template <typename F>
F evaluation_no_par(
    const DenseMultilinearExtension<F> &poly,
    const vector<F> &point)
{
    assert(poly.num_vars() == point.size() &&
           "Number of variables must match point dimension");

    return fix_variables_no_par(poly, point).evaluations[0];
}

// 合并多个MLE，将多个MLE的求值列表直接拼接即可（若需要则补零）
template <typename F>
shared_ptr<DenseMultilinearExtension<F>> merge_polynomial(
    const vector<shared_ptr<DenseMultilinearExtension<F>>> &polynomials)
{
    size_t nv = polynomials[0].num_vars();
    for (const auto &poly : polynomials)
    {
        if (nv != poly.num_vars())
        {
            throw invalid_argument("num_vars do not match for polynomials");
        }
    }
    // 计算合并后的变量数量
    size_t merge_nv = get_batched_nv(nv, polynomials.size());
    // 收集所有多项式的评估值
    vector<F> scalars;
    // 计算总大小
    size_t total_size = 0;
    for (const auto &poly : polynomials)
    {
        total_size += poly.to_evaluations().size();
    }
    scalars.reserve(total_size);

    // 合并所有评估值
    for (const auto &poly : polynomials)
    {
        const auto &evals = poly.to_evaluations();
        scalars.insert(scalars.end(), evals.begin(), evals.end());
    }
    // 用0填充到目标大小
    size_t target_size = 1ULL << merge_nv;
    if (scalars.size() < target_size)
    {
        scalars.resize(target_size, F::zero());
    }

    return make_shared<DenseMultilinearExtension<F>>(
        DenseMultilinearExtension<F>::from_evaluations_vec(merge_nv, move(scalars)));
}

// 从后往前固定变量
template <typename F>
DenseMultilinearExtension<F> fix_last_variable_no_par(
    const DenseMultilinearExtension<F> &poly,
    const F &partial_point)
{
    size_t nv = poly.num_vars();
    assert(nv > 0 && "Cannot fix variable from 0-variable polynomial");

    // 固定一个变量后，评估点列表长度减半
    size_t half_len = 1ULL << (nv - 1);
    vector<F> res;
    res.reserve(half_len);

    const auto &evaluations = poly.get_evaluations();
    for (size_t i = 0; i < half_len; ++i)
    {
        F val = evaluations[i] + partial_point * (evaluations[i + half_len] - evaluations[i]);
        res.push_back(move(val));
    }

    return DenseMultilinearExtension<F>::from_evaluations_vec(nv - 1, move(res));
}

template <typename F>
DenseMultilinearExtension<F> fix_last_variables_no_par(
    const DenseMultilinearExtension<F> &poly,
    const vector<F> &partial_point)
{
    if (partial_point.empty())
    {
        return poly;
    }
    // 从最后一个变量开始固定
    auto res = fix_last_variable_no_par(poly, partial_point.back());

    for (auto it = partial_point.rbegin() + 1; it != partial_point.rend(); ++it)
    {
        res = fix_last_variable_no_par(res, *it);
    }
    return res;
}

#endif // MULTILINEAR_POLYNOMIAL_H