#include <iostream>
#include <vector>
#include <cmath>
#include <cstdint>
#include <tuple>

using namespace std;

// 将整数转化为小端存储的二进制向量
// 5 --> [1,0,1,0]
vector<bool> bit_decompose(uint64_t input, size_t num_var)
{
    vector<bool> res;
    res.reserve(num_var);
    uint64_t i = input;
    for (size_t j = 0; j < num_var; j++)
    {
        res.push_back((i & 1) == 1);
        i >>= 1;
    }
    return res;
}

// 合并求值点
// [F(2),F(3)],index=2 --> [F(2),F(3),F(1),F(0)]
template <typename F>
vector<F> gen_eval_point(size_t index, size_t index_len, const vector<F> &point)
{
    // 分解索引为比特位
    auto index_bits = bit_decompose(static_cast<uint64_t>(index), index_len);

    // 将比特位转换为域元素
    // 待完善
    vector<F> index_vec;
    index_vec.reserve(index_len);
    for (bool bit : index_bits)
    {
        index_vec.push_back(F::from(bit));
    }

    // 合并 point 和 index_vec
    vector<F> result;
    result.reserve(point.size() + index_vec.size());
    result.insert(result.end(), point.begin(), point.end());
    result.insert(result.end(), index_vec.begin(), index_vec.end());

    return result;
}

// 返回合并MLE后的变量数
size_t get_batched_nv(size_t num_var, size_t polynomials_len)
{
    return num_var + static_cast<size_t>(log2(polynomials_len));
}

// 将小段存储的二进制向量转为整数
uint64_t project(const vector<bool> &input)
{
    uint64_t res = 0;
    for (auto it = input.rbegin(); it != input.rend(); ++it)
    {
        res <<= 1;
        res += *it ? 1 : 0;
    }
    return res;
}

/// Input index
/// - `i := (i_0, ...i_{n-1})`,
/// - `num_vars := n`
/// return three elements:
/// - `x0 := (i_1, ..., i_{n-1}, 0)`
/// - `x1 := (i_1, ..., i_{n-1}, 1)`
/// - `sign := i_0`
tuple<size_t, size_t, bool> get_index(size_t i, size_t num_vars)
{
    vector<bool> bit_sequence = bit_decompose(static_cast<uint64_t>(i), num_vars);

    // 构建 base_bits: bit_sequence[0..num_vars-2] (去掉最后一个bit)
    vector<bool> base_bits(bit_sequence.begin() + 1, bit_sequence.end());

    // 构建 x0_bits
    vector<bool> x0_bits = base_bits;
    x0_bits.push_back(false);

    // 构建 x1_bits
    vector<bool> x1_bits = base_bits;
    x1_bits.push_back(true);

    size_t x0 = static_cast<size_t>(project(x0_bits));
    size_t x1 = static_cast<size_t>(project(x1_bits));
    bool sign = bit_sequence[0];

    return make_tuple(x0, x1, sign);
}

/*
// Input index
// - `i := (i_0, ...i_{n-1})`,
// - `num_vars := n`
// return three elements:
// - `x0 := (i_1, ..., i_{n-1}, 0)`
// - `x1 := (i_1, ..., i_{n-1}, 1)`
// - `sign := i_0`
tuple<size_t, size_t, bool> get_index(size_t i, size_t num_vars) {
    // 提取最低位 (i_0)
    bool sign = (i & (1ULL << (num_vars - 1))) != 0;

    // 移除最高位，保留 i_1 到 i_{n-1}
    size_t base = i & ((1ULL << (num_vars - 1)) - 1);

    // x0 = (base << 1) | 0
    size_t x0 = base << 1;

    // x1 = (base << 1) | 1
    size_t x1 = (base << 1) | 1;

    return make_tuple(x0, x1, sign);
}
*/
