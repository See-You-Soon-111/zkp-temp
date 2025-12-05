#ifndef SUMCHECK_H
#define SUMCHECK_H
#include <iostream>
#include <optional>
#include "prover.h"
#include "verifier.h"

using namespace std;

template <typename F>
class SumCheck
{
public:
    // using VirtualPolynomial=VirtualPolynomial<F>;
    using MultilinearExtension = shared_ptr<DenseMultilinearExtension<F>>;
    using SumCheckProof = IOPProof<F>;
    using Transcript = SimpleTranscript;
    // using SumCheckSubClaim=SumCheckSubClaim<F>;

    F extract_sum(SumCheckProof &proof)
    {
        F &res = proof.proofs[0].evaluations[0] + proof.proofs[0].evaluations[1];
        return res;
    }

    Transcript init_transcript()
    {
        return SimpleTranscript("Initializing SumCheck transcript");
    }

    SumCheckProof prove(
        const VirtualPolynomial<F> &poly,
        Transcript &transcript)
    {
        transcript.append_serializable_element("aux info", poly.aux_info);

        SumCheckProver<F> prover_state;
        prover_state = prover_state.prover_init(poly);

        optional<F> challenge = nullopt;
        vector<IOPProverMessage<F>> prover_msgs;
        prover_msgs.reserve(poly.aux_info.num_variables);

        for (size_t i = 0; i < poly.aux_info.num_variables; ++i)
        {
            auto prover_msg = prover_state.prover_round_and_update_state(challenge);

            /*
            cout<<"debug sumcheck: "<<i<<endl;
            for(auto& e:prover_msg.evaluations){
                e.print();
            }
            cout<<endl;
            */
            transcript.append_serializable_element("prover msg", prover_msg);
            prover_msgs.push_back(prover_msg);
            challenge = transcript.get_and_append_challenge<F>("Internal round");
        }
        // pushing the last challenge point to the state
        if (challenge.has_value())
        {
            prover_state.get_state().challenges.push_back(challenge.value());
        }

        return IOPProof<F>{
            prover_state.get_state().challenges,
            move(prover_msgs)};
    }

    SumCheckSubClaim<F> verify(
        const F &claimed_sum,
        const SumCheckProof &proof,
        const VPAuxInfo &aux_info,
        Transcript &transcript)
    {
        transcript.append_serializable_element("aux info", aux_info);
        SumCheckVerifier<F> verifier_state;
        verifier_state = verifier_state.verifier_init(aux_info);

        for (size_t i = 0; i < aux_info.num_variables; ++i)
        {
            const auto &prover_msg = proof.proofs[i];
            transcript.append_serializable_element("prover msg", prover_msg);
            verifier_state.verify_round_and_update_state(prover_msg, transcript);
        }
        return verifier_state.check_and_generate_subclaim(claimed_sum);
    }
};

#endif