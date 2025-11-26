#ifndef TEST_H
#define TEST_H

#include <iostream>
#include <libff/algebra/curves/alt_bn128/alt_bn128_init.hpp>
#include <libff/algebra/curves/alt_bn128/alt_bn128_fields.hpp>
#include <random>
#include "arithmetic/virtual_polynomial.h"
#include "subroutines/poly_iop/sum_check/prover.h"
#include "subroutines/poly_iop/sum_check/verifier.h"
#include "subroutines/poly_iop/sum_check/sumcheck.h"
#include "transcript/transcript.h"
#include "subroutines/poly_iop/zero_check/zerocheck.h"

using namespace std;
using namespace libff;


void test_sum_check_trivial(){
    // 初始化 ALT-BN128 参数
    libff::init_alt_bn128_params();
    
    // 使用 ALT-BN128 的基域 Fq
    typedef libff::alt_bn128_Fq Fp;

    cout << "=== SumCheck Protocol Example ===" << endl;

    try {
        //    创建随机数生成器
        std::random_device rd;
        std::mt19937_64 rng(rd());
        
        //    创建一个更复杂的虚拟多项式进行测试
        //    例如：f(x,y,z) = 2*x*y + 3*y*z + 4*x*z，在布尔超立方体上的和为 9
        size_t num_vars = 3;
        
        // 创建三个MLE：f1(x,y,z) = x, f2(x,y,z) = y, f3(x,y,z) = z
        // 3变量有 2^3 = 8 个评估点，顺序为：000, 001, 010, 011, 100, 101, 110, 111
        vector <Fp> eval_x = {
            Fp::zero(), Fp::one(),  Fp::zero(), Fp::one(),   // 000, 100, 010, 110
            Fp::zero(), Fp::one(),  Fp::zero(), Fp::one()    // 001, 101, 011, 111
        };

        vector <Fp> eval_y = {
            Fp::zero(), Fp::zero(), Fp::one(),  Fp::one(),   // 000, 100, 010, 110
            Fp::zero(), Fp::zero(), Fp::one(),  Fp::one()    // 001, 101, 011, 111
        };

        vector <Fp> eval_z = {
            Fp::zero(), Fp::zero(), Fp::zero(), Fp::zero(),  // 000, 100, 010, 110
            Fp::one(),  Fp::one(),  Fp::one(),  Fp::one()    // 001, 101, 011, 111
        };

        auto mle_x = std::make_shared<DenseMultilinearExtension<Fp>>(num_vars, eval_x);
        auto mle_y = std::make_shared<DenseMultilinearExtension<Fp>>(num_vars, eval_y);
        auto mle_z = std::make_shared<DenseMultilinearExtension<Fp>>(num_vars, eval_z);
        
        // 创建虚拟多项式：f(x,y,z) = 2*x*y + 3*y*z + 4*x*z
        VirtualPolynomial<Fp> poly(num_vars);
        
        // 第一项：2*x*y
        vector<shared_ptr<DenseMultilinearExtension<Fp>>> term1 = {mle_x, mle_y};
        poly.add_mle_list(term1, Fp(2));  // 系数为2
        
        // 第二项：3*y*z  
        vector<shared_ptr<DenseMultilinearExtension<Fp>>> term2 = {mle_y, mle_z};
        poly.add_mle_list(term2, Fp(3));  // 系数为3
        
        // 第三项：4*x*z
        vector<shared_ptr<DenseMultilinearExtension<Fp>>> term3 = {mle_x, mle_z};
        poly.add_mle_list(term3, Fp(4));  // 系数为4
            
        cout << "Created virtual polynomial with " << num_vars << " variables" << endl;
        cout << "Max degree: " << poly.aux_info.max_degree << endl;
        cout << "Number of product terms: " << poly.products.size() << endl;
        
        //    计算真实的和（用于验证）
        //    对于 f(x,y,z) = 2*x*y + 3*y*z + 4*x*z，在布尔超立方体上的和为：
        //    计算所有8个点的值：
        //    000: 2*0*0 + 3*0*0 + 4*0*0 = 0
        //    001: 2*0*0 + 3*0*1 + 4*0*1 = 0  
        //    010: 2*0*1 + 3*1*0 + 4*0*0 = 0
        //    011: 2*0*1 + 3*1*1 + 4*0*1 = 3
        //    100: 2*1*0 + 3*0*0 + 4*1*0 = 0
        //    101: 2*1*0 + 3*0*1 + 4*1*1 = 4
        //    110: 2*1*1 + 3*1*0 + 4*1*0 = 2
        //    111: 2*1*1 + 3*1*1 + 4*1*1 = 2 + 3 + 4 = 9
        //    总和 = 0+0+0+3+0+4+2+9 = 18
        Fp true_sum = Fp(18);
        cout << "True sum over Boolean hypercube: ";
        true_sum.print();
        
        // 运行SumCheck协议
        SumCheck<Fp> sumcheck;
        
        // Prover端
        cout << "\n--- Prover Side ---" << endl;
        auto transcript_prover = sumcheck.init_transcript();


        auto proof = sumcheck.prove(poly, transcript_prover);
        
        cout << "Proof generated with " << proof.proofs.size() << " rounds" << endl;
        cout << "Challenge point: "<<endl;
        for (const auto& p : proof.point) {
            p.print();
        }
        
        // Verifier端
        cout << "\n--- Verifier Side ---" << endl;

        auto transcript_verifier = sumcheck.init_transcript();
        
        auto subclaim = sumcheck.verify(true_sum, proof, poly.aux_info, transcript_verifier);
        

        cout << "Verification completed successfully!" << endl;
        cout << "Subclaim point: ";
        
        for (const auto& p : subclaim.point) {
            p.print();
        }
        cout << "Expected evaluation: ";
        subclaim.expected_evaluation.print();
        
        // 验证子声明
        cout << "\n--- Verifying Subclaim ---" << endl;
        // 在子声明点上计算多项式值
        auto actual_eval = poly.evaluate(subclaim.point);
        cout << "Actual evaluation at subclaim point: ";
        actual_eval.print();
        
        if (actual_eval == subclaim.expected_evaluation) {
            cout << "✓ Subclaim VERIFIED: Actual evaluation matches expected!" << endl;
            cout << "✓ SumCheck protocol completed SUCCESSFULLY!" << endl;
        } else {
            cout << "✗ Subclaim FAILED: Actual evaluation does not match expected!" << endl;
            return;

        }
                
    } catch (const exception& e) {
        cerr << "Error: " << e.what() << endl;
        return;
    }
    
    cout << "\n=== SumCheck Example Completed ===" << endl;

}


void test_zero_check_trivial() {
    // 初始化 ALT-BN128 参数
    libff::init_alt_bn128_params();
    
    // 使用 ALT-BN128 的基域 Fq
    typedef libff::alt_bn128_Fq Fp;

    cout << "=== Complex ZeroCheck Protocol Example ===" << endl;

    try {
        
        //  创建一个在布尔超立方体上求和为零的多项式
        //  例如：f(x,y,z) = x*y - x*y，在布尔超立方体上的和显然为0
        size_t num_vars = 3;
        
        // 创建三个MLE：f1(x,y,z) = x, f2(x,y,z) = y, f3(x,y,z) = z
        vector<Fp> eval_x = {
            Fp::zero(), Fp::one(),  Fp::zero(), Fp::one(),   // 000, 100, 010, 110
            Fp::zero(), Fp::one(),  Fp::zero(), Fp::one()    // 001, 101, 011, 111
        };

        vector<Fp> eval_y = {
            Fp::zero(), Fp::zero(), Fp::one(),  Fp::one(),   // 000, 100, 010, 110
            Fp::zero(), Fp::zero(), Fp::one(),  Fp::one()    // 001, 101, 011, 111
        };

        vector<Fp> eval_z = {
            Fp::zero(), Fp::zero(), Fp::zero(), Fp::zero(),  // 000, 100, 010, 110
            Fp::one(),  Fp::one(),  Fp::one(),  Fp::one()    // 001, 101, 011, 111
        };

        auto mle_x = std::make_shared<DenseMultilinearExtension<Fp>>(num_vars, eval_x);
        auto mle_y = std::make_shared<DenseMultilinearExtension<Fp>>(num_vars, eval_y);
        auto mle_z = std::make_shared<DenseMultilinearExtension<Fp>>(num_vars, eval_z);
        
        // 创建虚拟多项式：f(x,y,z) = x*y - x*y + y*z - y*z
        // 这个多项式在布尔超立方体上的和显然为0
        VirtualPolynomial<Fp> poly(num_vars);
        
        // 第一项：x*y (正项)
        vector<shared_ptr<DenseMultilinearExtension<Fp>>> term1 = {mle_x, mle_y};
        poly.add_mle_list(term1, Fp(1));
        
        // 第二项：x*y (负项)  
        vector<shared_ptr<DenseMultilinearExtension<Fp>>> term2 = {mle_x, mle_y};
        poly.add_mle_list(term2, Fp(-1));
        
        // 第三项：y*z (正项)
        vector<shared_ptr<DenseMultilinearExtension<Fp>>> term3 = {mle_y, mle_z};
        poly.add_mle_list(term3, Fp(1));
        
        // 第四项：y*z (负项)
        vector<shared_ptr<DenseMultilinearExtension<Fp>>> term4 = {mle_y, mle_z};
        poly.add_mle_list(term4, Fp(-1));
            
        cout << "Created zero polynomial with " << num_vars << " variables" << endl;
        cout << "Max degree: " << poly.aux_info.max_degree << endl;
        cout << "Number of product terms: " << poly.products.size() << endl;
        // 运行ZeroCheck协议
        ZeroCheck<Fp> zerocheck;
        
        // Prover端
        cout << "\n--- Prover Side ---" << endl;
        auto transcript_prover = zerocheck.init_transcript();
        auto proof = zerocheck.prove(poly, transcript_prover);
        
        cout << "Complex ZeroCheck proof generated with " << proof.proofs.size() << " rounds" << endl;
        
        // Verifier端
        cout << "\n--- Verifier Side ---" << endl;
        auto transcript_verifier = zerocheck.init_transcript();
        auto subclaim = zerocheck.verify(proof, poly.aux_info, transcript_verifier);
        
        cout << "Complex ZeroCheck verification completed successfully!" << endl;
        
        // 验证子声明
        cout << "\n--- Verifying Complex ZeroCheck Subclaim ---" << endl;
        auto actual_eval = poly.evaluate(subclaim.point);
        cout << "Actual evaluation at subclaim point: ";
        actual_eval.print();
        
        if (actual_eval == subclaim.expected_evaluation) {
            cout << "✓ Complex ZeroCheck Subclaim VERIFIED!" << endl;
            cout << "✓ Complex ZeroCheck protocol completed SUCCESSFULLY!" << endl;
        } else {
            cout << "✗ Complex ZeroCheck Subclaim FAILED!" << endl;
            return;
        }
        
    } catch (const exception& e) {
        cerr << "Error: " << e.what() << endl;
        return;
    }
    
    cout << "\n=== Complex ZeroCheck Example Completed ===" << endl;
}


void test_sum_check_random() {
    // 初始化 ALT-BN128 参数
    libff::init_alt_bn128_params();
    
    // 使用 ALT-BN128 的基域 Fq
    typedef libff::alt_bn128_Fq Fp;

    cout << "=== Random SumCheck Protocol Example ===" << endl;

    try {
        
        // 生成随机虚拟多项式
        size_t num_vars = 3;
        auto num_multiplicands_range = make_pair(1, 4);  // 每个乘积项有1-3个MLE
        size_t num_products = 5;  // 5个乘积项
        
        cout << "Generating random polynomial..." << endl;
        cout << "Number of variables: " << num_vars << endl;
        cout << "Number of product terms: " << num_products << endl;
        cout << "Multiplicands range: [" << num_multiplicands_range.first 
             << ", " << num_multiplicands_range.second << "]" << endl;
        
        // 生成随机多项式和它的真实和
        VirtualPolynomial<Fp> poly1;
        auto [poly, true_sum] = poly1.rand(num_vars, num_multiplicands_range, num_products);
        
        cout << "Random polynomial created successfully!" << endl;
        cout << "Max degree: " << poly.aux_info.max_degree << endl;
        cout << "Number of product terms: " << poly.products.size() << endl;
        cout << "True sum over Boolean hypercube: ";
        true_sum.print();
        cout << endl;
        
        // 运行SumCheck协议
        SumCheck<Fp> sumcheck;
        
        // Prover端
        cout << "\n--- Prover Side ---" << endl;
        auto transcript_prover = sumcheck.init_transcript();
        auto proof = sumcheck.prove(poly, transcript_prover);
        
        cout << "Proof generated with " << proof.proofs.size() << " rounds" << endl;
        
        // Verifier端
        cout << "\n--- Verifier Side ---" << endl;
        auto transcript_verifier = sumcheck.init_transcript();
        auto subclaim = sumcheck.verify(true_sum, proof, poly.aux_info, transcript_verifier);
        
        cout << "Verification completed successfully!" << endl;
        cout << "Subclaim point: ";
        for (const auto& p : subclaim.point) {
            p.print();
            cout << " ";
        }
        cout << endl;
        cout << "Expected evaluation: ";
        subclaim.expected_evaluation.print();
        cout << endl;
        
        // 验证子声明
        cout << "\n--- Verifying Subclaim ---" << endl;
        // 在子声明点上计算多项式值
        auto actual_eval = poly.evaluate(subclaim.point);
        cout << "Actual evaluation at subclaim point: ";
        actual_eval.print();
        cout << endl;
        
        if (actual_eval == subclaim.expected_evaluation) {
            cout << "✓ Subclaim VERIFIED: Actual evaluation matches expected!" << endl;
            cout << "✓ Random SumCheck protocol completed SUCCESSFULLY!" << endl;
        } else {
            cout << "✗ Subclaim FAILED: Actual evaluation does not match expected!" << endl;
            cout << "Difference: ";
            (actual_eval - subclaim.expected_evaluation).print();
            cout << endl;
            return;
        }
        
    } catch (const exception& e) {
        cerr << "Error: " << e.what() << endl;
        return;
    }
    
    cout << "\n=== Random SumCheck Example Completed ===" << endl;
}


void test_zero_check_random(){
    // 初始化 ALT-BN128 参数
    libff::init_alt_bn128_params();
    
    // 使用 ALT-BN128 的基域 Fq
    typedef libff::alt_bn128_Fq Fp;

    cout << "=== Random SumCheck Protocol Example ===" << endl;

    try {
        
        // 生成随机虚拟多项式
        size_t num_vars = 3;
        auto num_multiplicands_range = make_pair(1, 4);  // 每个乘积项有1-3个MLE
        size_t num_products = 5;  // 5个乘积项
        
        cout << "Generating random polynomial..." << endl;
        cout << "Number of variables: " << num_vars << endl;
        cout << "Number of product terms: " << num_products << endl;
        cout << "Multiplicands range: [" << num_multiplicands_range.first 
             << ", " << num_multiplicands_range.second << "]" << endl;
        
        // 生成随机0多项式
        VirtualPolynomial<Fp> poly1;
        auto poly = poly1.rand_zero(num_vars, num_multiplicands_range, num_products);
        
        Fp true_sum=Fp::zero();
        cout << "Random polynomial created successfully!" << endl;
        cout << "Max degree: " << poly.aux_info.max_degree << endl;
        cout << "Number of product terms: " << poly.products.size() << endl;
        cout << "True sum over Boolean hypercube: ";
        true_sum.print();
        cout << endl;

        // 运行ZeroCheck协议
        ZeroCheck<Fp> zerocheck;
        
        // Prover端
        cout << "\n--- Prover Side ---" << endl;
        auto transcript_prover = zerocheck.init_transcript();
        auto proof = zerocheck.prove(poly, transcript_prover);
        
        cout << "Complex ZeroCheck proof generated with " << proof.proofs.size() << " rounds" << endl;
        
        // Verifier端
        cout << "\n--- Verifier Side ---" << endl;
        auto transcript_verifier = zerocheck.init_transcript();
        auto subclaim = zerocheck.verify(proof, poly.aux_info, transcript_verifier);
        
        cout << "Complex ZeroCheck verification completed successfully!" << endl;
        
        // 验证子声明
        cout << "\n--- Verifying Complex ZeroCheck Subclaim ---" << endl;
        auto actual_eval = poly.evaluate(subclaim.point);
        cout << "Actual evaluation at subclaim point: ";
        actual_eval.print();
        
        if (actual_eval == subclaim.expected_evaluation) {
            cout << "✓ Complex ZeroCheck Subclaim VERIFIED!" << endl;
            cout << "✓ Complex ZeroCheck protocol completed SUCCESSFULLY!" << endl;
        } else {
            cout << "✗ Complex ZeroCheck Subclaim FAILED!" << endl;
            return;
        }
        
    } catch (const exception& e) {
        cerr << "Error: " << e.what() << endl;
        return;
    }
    
    cout << "\n=== Complex ZeroCheck Example Completed ===" << endl;
}
    
#endif