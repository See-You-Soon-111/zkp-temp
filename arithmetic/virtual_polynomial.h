#ifndef VIRTUAL_POLYNOMIAL_H
#define VIRTUAL_POLYNOMIAL_H

#include <iostream>
#include <unordered_map>
#include <vector>
#include <memory>
#include <utility>
#include <random>

#include "field_and_polynomial/temp.h"
#include "multilinear_polynomial.h"
#include "util.h"

class VPAuxInfo
{
public:
    size_t max_degree;
    size_t num_variables;

    VPAuxInfo(size_t num_vars = 0) : max_degree(0), num_variables(num_vars)
    {
    }
};

// 虚拟多项式是使用多个MLE表示多项式的方法
// aux_info 记录多项式的度数和变量数
// 设f=c0 * f0 * f1 * f2 + c1 * f3 * f4
// products 记录每个[系数，乘积项]
//          在此例子中为：[(c0, [0, 1, 2]), (c1, [3, 4])]

// flattened_ml_extensions 存储所有的MLE，此例子中为f0, f1, f2, f3, f4
// raw_pointers_lookup_table 将 fi 映射到 i

template <typename F>
class VirtualPolynomial
{
private:
    unordered_map<const DenseMultilinearExtension<F> *, size_t> raw_pointers_lookup_table;

public:
    VPAuxInfo aux_info;
    vector<pair<F, vector<size_t>>> products;
    vector<shared_ptr<DenseMultilinearExtension<F>>> flattened_ml_extensions;

    VirtualPolynomial(size_t num_variables = 0) : aux_info(num_variables)
    {
    }

    // 从MLE创建一个新虚拟多项式
    VirtualPolynomial new_from_mle(
        const shared_ptr<DenseMultilinearExtension<F>> &mle,
        const F &coefficient)
    {
        VirtualPolynomial poly;
        poly.aux_info.max_degree = 1;
        poly.aux_info.num_variables = mle.num_vars();

        // 待完善，获取mle指针
        auto mle_ptr = mle.get();
        poly.raw_pointers_lookup_table[mle_ptr] = 0;
        poly.products.emplace_back(coefficient, vector<size_t>{0});
        poly.flattened_ml_extensions.push_back(mle);

        return poly;
    }

    void printproduct()
    {
        // 输出products的内容
        std::cout << "Products (" << products.size() << " items):" << std::endl;
        for (size_t i = 0; i < products.size(); ++i)
        {
            const auto &product = products[i];
            std::cout << "Item " << i << ": coefficient = ";
            product.first.print();

            std::cout << ", indices = [";
            for (size_t j = 0; j < product.second.size(); ++j)
            {
                std::cout << product.second[j];
                if (j < product.second.size() - 1)
                {
                    std::cout << ", ";
                }
            }
            std::cout << "]" << std::endl;
        }
    }
    // 添加形为 coe * MLE1 * MLE2 * ... * MLEn的乘积项
    void add_mle_list(
        const vector<shared_ptr<DenseMultilinearExtension<F>>> &mle_list,
        const F &coefficient)
    {
        // 空列表则返回错误
        if (mle_list.empty())
        {
            throw;
        }

        // 更新degree
        aux_info.max_degree = max(aux_info.max_degree, mle_list.size());
        vector<size_t> indexed_product;
        indexed_product.reserve(mle_list.size());

        for (shared_ptr<DenseMultilinearExtension<F>> mle : mle_list)
        {
            // 变量不等则抛出错误
            if (mle->num_vars() != aux_info.num_variables)
            {
                throw;
            }

            auto mle_ptr = mle.get();
            auto it = raw_pointers_lookup_table.find(mle_ptr);
            // 如果mle出现在之前的乘积项中，则不需要建立映射
            // 否则需要对其建立映射
            if (it != raw_pointers_lookup_table.end())
            {
                indexed_product.push_back(it->second);
            }
            else
            {
                size_t curr_index = flattened_ml_extensions.size();
                flattened_ml_extensions.push_back(mle);
                raw_pointers_lookup_table[mle_ptr] = curr_index;
                indexed_product.push_back(curr_index);
            }
        }

        products.emplace_back(coefficient, move(indexed_product));
    }

    // 实现VirtualPolynomial * (coe * mle)
    void mul_by_mle(
        const shared_ptr<DenseMultilinearExtension<F>> &mle,
        const F &coefficient)
    {
        // 变量数不等抛出错误
        if ((*mle).num_vars() != aux_info.num_variables)
        {
            throw;
        }

        auto mle_ptr = mle.get();
        size_t mle_index;

        auto it = raw_pointers_lookup_table.find(mle_ptr);
        // 更新 raw_pointers_lookup_table和flattened_ml_extensions
        if (it != raw_pointers_lookup_table.end())
        {
            mle_index = it->second;
        }
        else
        {
            mle_index = flattened_ml_extensions.size();
            raw_pointers_lookup_table[mle_ptr] = mle_index;
            flattened_ml_extensions.push_back(mle);
        }
        // 更新products
        for (auto &[prod_coef, indices] : products)
        {
            indices.push_back(mle_index);
            prod_coef = prod_coef * coefficient;
        }

        aux_info.max_degree += 1;
    }

    // 计算VirtualPolynomial在某个point上的值
    F evaluate(const vector<F> &point)
    {
        // 变量不一致抛出错误
        if (aux_info.num_variables != point.size())
        {
            throw;
        }

        vector<F> evals;
        evals.reserve(flattened_ml_extensions.size());
        // 先计算每个mle在point上的值
        for (shared_ptr<DenseMultilinearExtension<F>> ext : flattened_ml_extensions)
        {
            evals.push_back((*ext).evaluate(point));
        }

        F result = F::zero();
        for (const auto &[coef, indices] : products)
        {
            F product_val = coef;
            for (size_t idx : indices)
            {
                product_val *= evals[idx];
            }
            result += product_val;
        }

        return result;
    }

    // 随机生成虚拟多项式,并返回其在布尔超立方体上的总和

    pair<VirtualPolynomial, F> rand(
        size_t nv,
        pair<size_t, size_t> num_multiplicands_range,
        size_t num_products)
    {
        VirtualPolynomial poly(nv);
        F sum = F ::zero();

        // gen是一个使用rd()作种子初始化的标准梅森旋转算法的随机数发生器
        random_device rd;
        mt19937 gen(rd());
        // 随机数生成器
        uniform_int_distribution<size_t> dist(
            num_multiplicands_range.first,
            num_multiplicands_range.second - 1);

        for (size_t i = 0; i < num_products; ++i)
        {
            // 先随机生成mle_list
            size_t num_multiplicands = dist(gen);
            auto [product, product_sum] = random_mle_list<F>(nv, num_multiplicands);
            F coefficient = F ::random_element();
            // 再添加到VirtualPolynomial
            poly.add_mle_list(product, coefficient);
            sum = sum + product_sum * coefficient;
        }

        return {poly, sum};
    }

    // 生成和为0的随机虚拟多项式

    VirtualPolynomial rand_zero(
        size_t nv,
        pair<size_t, size_t> num_multiplicands_range,
        size_t num_products)
    {
        VirtualPolynomial poly(nv);

        // gen是一个使用rd()作种子初始化的标准梅森旋转算法的随机数发生器
        random_device rd;
        mt19937 gen(rd());

        uniform_int_distribution<size_t> dist(
            num_multiplicands_range.first,
            num_multiplicands_range.second - 1);

        for (size_t i = 0; i < num_products; ++i)
        {
            size_t num_multiplicands = dist(gen);
            auto product = random_zero_mle_list<F>(nv, num_multiplicands);
            F coefficient = F::random_element();

            poly.add_mle_list(product, coefficient);
        }

        return poly;
    }

    // 用于测试
    void print_evals()
    {
        if (aux_info.num_variables > 5)
        {
            throw std::runtime_error(
                "this function is used for testing only. cannot print more than 5 num_vars");
        }

        for (size_t i = 0; i < (1ULL << aux_info.num_variables); ++i)
        {
            auto point = bit_decompose(i, aux_info.num_variables);
            vector<F> point_fr;
            point_fr.reserve(point.size());
            for (bool bit : point)
            {
                point_fr.push_back(F::from(bit));
            }
            cout << i << " " << evaluate(point_fr) << endl;
        }
        cout << endl;
    }
};

template <typename F>
void build_eq_x_r_helper(
    const vector<F> &r,
    vector<F> &buf)
{
    // r为空，则抛出错误
    if (r.empty())
    {
        throw;
    }
    else if (r.size() == 1)
    {
        buf.clear();
        buf.push_back(F::one() - r[0]);
        buf.push_back(r[0]);
    }
    else
    {
        vector<F> sub_r(r.begin() + 1, r.end());
        build_eq_x_r_helper(sub_r, buf);

        // suppose at the previous step we received [b_1, ..., b_k]
        // for the current step we will need
        // if x_0 = 0:   (1-r0) * [b_1, ..., b_k]
        // if x_0 = 1:   r0 * [b_1, ..., b_k]
        // let mut res = vec![];
        // for &b_i in buf.iter() {
        //     let tmp = r[0] * b_i;
        //     res.push(b_i - tmp);
        //     res.push(tmp);
        // }
        // *buf = res;
        vector<F> res(buf.size() * 2);

        for (size_t i = 0; i < buf.size(); ++i)
        {
            F tmp = r[0] * buf[i];
            res[2 * i] = buf[i] - tmp;
            res[2 * i + 1] = tmp;
        }
        buf = move(res);
    }
}

template <typename F>
vector<F> build_eq_x_r_vec(const vector<F> &r)
{
    // we build eq(x,r) from its evaluations
    // we want to evaluate eq(x,r) over x \in {0, 1}^num_vars
    // for example, with num_vars = 4, x is a binary vector of 4, then
    //  0 0 0 0 -> (1-r0)   * (1-r1)    * (1-r2)    * (1-r3)
    //  1 0 0 0 -> r0       * (1-r1)    * (1-r2)    * (1-r3)
    //  0 1 0 0 -> (1-r0)   * r1        * (1-r2)    * (1-r3)
    //  1 1 0 0 -> r0       * r1        * (1-r2)    * (1-r3)
    //  ....
    //  1 1 1 1 -> r0       * r1        * r2        * r3
    // we will need 2^num_var evaluations

    // r为空，则抛出错误
    if (r.empty())
    {
        throw;
    }
    vector<F> eval;
    build_eq_x_r_helper(r, eval);
    return eval;
}
/// This function build the eq(x, r) polynomial for any given r.
///
/// Evaluate
///      eq(x,y) = \prod_i=1^num_var (x_i * y_i + (1-x_i)*(1-y_i))
/// over r, which is
///      eq(x,y) = \prod_i=1^num_var (x_i * r_i + (1-x_i)*(1-r_i))
template <typename F>
shared_ptr<DenseMultilinearExtension<F>> build_eq_x_r(const vector<F> &r)
{
    auto evals = build_eq_x_r_vec<F>(r);
    return make_shared<DenseMultilinearExtension<F>>(r.size(), move(evals));
}

// 计算 \hat f(x) = \sum_{x_i \in eval_x} f(x_i) eq(x,r)
template <typename F>
VirtualPolynomial<F> build_f_hat(
    const VirtualPolynomial<F> &poly,
    const vector<F> &r)
{
    // 变量不相等则抛出错误
    if (poly.aux_info.num_variables != r.size())
    {
        throw;
    }
    auto eq_x_r = build_eq_x_r<F>(r);
    VirtualPolynomial<F> res = poly;
    res.mul_by_mle(eq_x_r, F::one());

    return res;
}

// 计算 eq(x,y)=\prod (x_i * y_i + (1-x_i) * (1-y_i))
template <typename F>
F eq_eval(
    const vector<F> &x,
    const vector<F> &y)
{
    // 两个向量长度不相等，抛出错误
    if (x.size() != y.size())
    {
        throw;
    }
    F res = F::one();
    for (size_t i = 0; i < x.size(); ++i)
    {
        F xi_yi = x[i] * y[i];
        res = res * (F::one() + xi_yi + xi_yi - x[i] - y[i]);
    }
    return res;
}

#endif // VIRTUAL_POLYNOMIAL_H