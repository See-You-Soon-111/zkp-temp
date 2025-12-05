#ifndef UTIL_H
#define UTIL_H

#include <vector>
#include <cstdint>
#include <tuple>

// 将整数转化为小端存储的二进制向量
// 5 --> [1,0,1,0]
std::vector<bool> bit_decompose(uint64_t input, size_t num_var);

// 合并求值点
// [F(2),F(3)],index=2 --> [F(2),F(3),F(1),F(0)]
template <typename F>
std::vector<F> gen_eval_point(size_t index, size_t index_len, const std::vector<F> &point);

// 返回合并MLE后的变量数
size_t get_batched_nv(size_t num_var, size_t polynomials_len);

// 将小段存储的二进制向量转为整数
uint64_t project(const std::vector<bool> &input);

/// Input index
/// - `i := (i_0, ...i_{n-1})`,
/// - `num_vars := n`
/// return three elements:
/// - `x0 := (i_1, ..., i_{n-1}, 0)`
/// - `x1 := (i_1, ..., i_{n-1}, 1)`
/// - `sign := i_0`
std::tuple<size_t, size_t, bool> get_index(size_t i, size_t num_vars);

#endif // UTIL_H