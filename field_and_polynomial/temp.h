#ifndef TEMP_H
#define TEMP_H

#include <iostream>
#include <optional>
#include <vector>
#include <cassert>
#include <memory>
#include <libff/common/utils.hpp> 

using namespace std;
// 假设的类型和函数声明
/*
template<typename F>
class Radix2EvaluationDomain {
public:
    static unique_ptr<Radix2EvaluationDomain<F>> new(size_t size);
    size_t size() const;
};

template<typename F>
class DensePolynomial {
    // 稠密多项式实现
};

template<typename F>
class Evaluations {
public:
    static Evaluations<F> from_vec_and_domain(const std::vector<F>& eval, const Radix2EvaluationDomain<F>& domain);
    DensePolynomial<F> interpolate() const;
};

// 错误类型
enum class ArithErrors {
    InvalidParameters
};

*/
template <typename F>
class DenseMultilinearExtension
{
private:
    size_t num_vars_;
    vector<F> evaluations_;

public:
    DenseMultilinearExtension(size_t num_vars)
        : num_vars_(num_vars),evaluations_(1ULL<<num_vars,F::zero()) {}

    DenseMultilinearExtension(size_t num_vars, const vector<F> &evaluations)
        : num_vars_(num_vars), evaluations_(evaluations) {}

    size_t num_vars() const { return num_vars_; }

    const vector<F> &get_evaluations() const { return evaluations_; }

    DenseMultilinearExtension<F> rand(size_t num_var){
        vector<F> evals;
        evals.reserve(1ULL<<num_var);
        for(size_t i=0;i<(1ULL<<num_var);++i){
            evals.push_back(libff::random_element_non_zero<F>());
        }
        return DenseMultilinearExtension<F>(num_var,evals);
    }

    /*
        DenseMultilinearExtension<F> from_evaluations_slice(
            size_t num_vars, const F* evaluations
        ) {
            return from_evaluations_vec(num_vars,vector(evaluations));
        }
    */
    DenseMultilinearExtension<F> from_evaluations_slice(
        size_t num_vars, const F *evaluations, size_t evaluations_size)
    {
        return from_evaluations_vec(
            num_vars,
            vector<F>(evaluations, evaluations + evaluations_size));
    }

    DenseMultilinearExtension<F> from_evaluations_vec(
        size_t num_vars, vector<F> evaluations)
    {
        assert(evaluations.size() == (1ULL << num_vars) && "The size of evaluations should be 2^num_vars.");

        return DenseMultilinearExtension<F>(num_vars, move(evaluations));
    }

    //template <typename R>
    //DenseMultilinearExtension<F> rand(size_t num_vars, R &rng);

    DenseMultilinearExtension<F> fix_variables(const vector<F> &partial_point)
    {
        assert(partial_point.size() <= num_vars_ &&
               "invalid size of partial point");

        vector<F> poly = evaluations_;
        size_t nv = num_vars_;
        size_t dim = partial_point.size();

        // 从左到右评估部分点的单个变量
        for (size_t i = 1; i < dim + 1; ++i)
        {
            const F &r = partial_point[i - 1];
            for (size_t b = 0; b < (1ULL << (nv - i)); ++b)
            {
                size_t left_index = b << 1;
                size_t right_index = left_index + 1;
                const F &left = poly[left_index];
                const F &right = poly[right_index];
                poly[b] = left + r * (right - left);
            }
        }

        return DenseMultilinearExtension<F>::from_evaluations_vec(
            nv - dim,
            vector<F>(poly.begin(), poly.begin() + (1ULL << (nv - dim))));
    }
    // 固定所有变量
    F evaluate(const vector<F> &point) 
    {/*
        if (point.size() == num_vars_)
        {
            DenseMultilinearExtension<F> fixed = fix_variables(point);
            return fixed.evaluations_[0];
        }
    */
        DenseMultilinearExtension<F> fixed = fix_variables(point);
        return fixed.evaluations_[0];

    }

    void scalar_multiply(const F& scalar){
        for(auto& eval:evaluations_){
            eval*=scalar;
        }
    }

    DenseMultilinearExtension operator*(const F& scalar) const{
        DenseMultilinearExtension result=*this;
        result.scalar_multiply(scalar);
        return result;
    }

    DenseMultilinearExtension& operator+=(const DenseMultilinearExtension& other){
        assert(num_vars_=other.num_vars_);
        assert(evaluations_.size()==other.evaluations_.size());

        for(size_t i=0;i<evaluations_.size();++i){
            evaluations_[i]+=other.evaluations_[i];
        }

        return *this;
    }

    DenseMultilinearExtension operator+(const DenseMultilinearExtension& other) const{
        DenseMultilinearExtension result=*this;
        result+=other;
        return result;
    }

    
};

#endif