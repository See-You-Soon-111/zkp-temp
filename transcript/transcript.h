#ifndef TRANSCRIPT_H
#define TRANSCRIPT_H

#include <vector>
#include <cstdint>
#include <string>
using namespace std;

class SimpleTranscript
{
private:
    vector<uint8_t> message_buffer;
    bool is_empty;

    vector<uint8_t> string_to_bytes(const string &str)
    {
        return vector<uint8_t>(str.begin(), str.end());
    }

    // 将结构体或者类转化为字节
    // 这个别用，tmd有错误我服了
    template <typename T>
    vector<uint8_t> to_bytes([[maybe_unused]] const T &obj)
    {
        return vector<uint8_t>{0xDE, 0xAD, 0xBE, 0xEF};
    }

    // 将一个 size_t 类型的整数（大小）以 4字节小端序 的形式追加到 message_buffer 中
    void append_size(size_t size)
    {
        for (int i = 0; i < 4; ++i)
        {
            message_buffer.push_back(static_cast<uint8_t>((size >> (8 * i)) & 0xFF));
        }
    }

    /// 这一部分先这样放着

    // 生成挑战字节
    std::vector<uint8_t> generate_challenge_bytes(const std::string &label, size_t output_len)
    {
        // 简单实现：使用标准哈希函数
        // 实际中应该使用加密安全的哈希函数

        std::vector<uint8_t> input = message_buffer;
        auto label_bytes = string_to_bytes(label);
        input.insert(input.end(), label_bytes.begin(), label_bytes.end());

        // 使用简单的哈希（实际中应该用SHA256等）

        return simple_hash(input, output_len);
    }

    // 简单的哈希函数（实际中应该替换为加密安全的哈希）
    std::vector<uint8_t> simple_hash(const std::vector<uint8_t> &input, size_t output_len)
    {
        std::vector<uint8_t> output(output_len, 0);

        // 简单的XOR哈希，仅用于演示
        for (size_t i = 0; i < input.size(); i++)
        {
            output[i % output_len] ^= input[i];
        }

        return output;
    }

public:
    SimpleTranscript(const string &label = "") : is_empty(true)
    {

        if (!label.empty())
        {
            append_message("label", string_to_bytes(label));
        }
    }

    void append_message(const string &label, const vector<uint8_t> &msg)
    {
        // 添加标签长度和标签
        auto label_vec = string_to_bytes(label);
        append_size(label_vec.size());
        message_buffer.insert(message_buffer.end(), label_vec.begin(), label_vec.end());

        // 添加消息长度和消息
        append_size(msg.size());
        message_buffer.insert(message_buffer.end(), msg.begin(), msg.end());

        is_empty = false;
    }

    // 添加域元素
    template <typename F>
    void append_field_element(const string &label, const F &field_elem)
    {
        append_message(label, to_bytes(field_elem));
    }

    // 添加CanonicalSerialize元素（可序列化？？）
    template <typename S>
    void append_serializable_element(const string label, const S &elem)
    {
        append_message(label, to_bytes(elem));
    }

    // 根据之前的信息生成challenge，并将其添加到transcript
    template <typename F>
    F get_and_append_challenge(const string &label)
    {
        // transcript为空是需要拒绝
        if (is_empty)
        {
        }

        // 简易实现：使用哈希从当前消息生成挑战
        auto challenge_bytes = generate_challenge_bytes(label, 64);
        // 从byte获取field元素
        // 转换类型
        std::vector<uint64_t> words;
        // 假设每8个byte组成一个uint64_t
        for (size_t i = 0; i < challenge_bytes.size(); i += 8)
        {
            uint64_t word = 0;
            for (size_t j = 0; j < 8 && i + j < challenge_bytes.size(); ++j)
            {
                word |= static_cast<uint64_t>(challenge_bytes[i + j]) << (8 * j);
            }
            words.push_back(word);
        }

        F challenge;
        challenge.from_words(words);

        append_field_element(label, challenge);

        return challenge;
    }

    template <typename F>
    vector<F> get_and_append_challenge_vector(const string &label, size_t len)
    {
        vector<F> challenges;
        for (size_t i = 0; i < len; ++i)
        {
            challenges.push_back(get_and_append_challenge<F>(label + "_" + to_string(i)));
        }
        return challenges;
    }

    const vector<uint8_t> &get_message_buffer() const
    {
        return message_buffer;
    }

    void print_buffer_hex() const
    {
        std::cout << "Transcript Buffer (hex): ";
        for (auto b : message_buffer)
        {
            printf("%02x", b);
        }
        std::cout << std::endl;
    }
};

#endif // TRANSCRIPT_H