// SPDX-License-Identifier: MIT
pragma solidity =0.8.36;

import {GkrWhirRegistry} from "./GkrWhirRegistry.sol";

/// Research adapter for commit 129f827's packed Proth120 calldata format only.
/// The trusted constructor must receive a reproducibly derived setup-cap hash
/// and recursion-chain digest. No NEAR guest or quantum-security claim is made.
contract PinnedStatementVerifier {
    GkrWhirRegistry public immutable registry;
    address public immutable gkr;
    address public immutable whir;
    bytes32 public immutable setupCapHash;
    bytes32 public immutable recursionChain;

    constructor(GkrWhirRegistry r, bytes32 setupHash, bytes32 chain) {
        registry = r;
        gkr = r.gkrVerifier();
        whir = r.whirVerifier();
        require(gkr.code.length > 0 && whir.code.length > 0, "missing verifiers");
        setupCapHash = setupHash;
        recursionChain = chain;
    }

    /// expectedOutput must be derived from the application's canonical claim,
    /// including its protocol/domain context; it is not a prover-selected label.
    function verify(bytes calldata gkrProof, bytes calldata whirProof, bytes32 expectedOutput)
        external returns (bytes32 commitment)
    {
        require(gkrProof.length + whirProof.length < 300000, "proof size");
        require(gkrProof.length >= 660 && whirProof.length >= 992, "short proof");

        // GKR cap is 64 LE u32 words at 404; WHIR uses BE u32 at 736.
        // Pin both representations: a previously accepted registry key must not
        // let an unrelated GKR call supply the setup check for another proof.
        bytes memory capBE = new bytes(256);
        for (uint256 i = 0; i < 64; i++) {
            for (uint256 j = 0; j < 4; j++) {
                capBE[4*i+j] = gkrProof[404+4*i+3-j];
            }
        }
        require(keccak256(capBE) == setupCapHash, "GKR setup");
        require(keccak256(whirProof[736:992]) == setupCapHash, "WHIR setup");

        commitment = keccak256(whirProof[:992]);
        (bool okGkr,) = gkr.call(gkrProof);
        require(okGkr, "GKR rejected");
        (bool okWhir,) = whir.call(whirProof);
        require(okWhir, "WHIR rejected");
        // Verifiers currently ignore the return value of their registry call.
        // Successful low-level calls alone are consequently insufficient.
        require(registry.verificationMask(commitment) == GkrWhirRegistry.VerificationMask.Both,
                "unverified pair");
        (bytes32 output, bytes32 chain) = registry.commitmentPublicData(commitment);
        require(output == expectedOutput, "output mismatch");
        require(chain == recursionChain, "recursion chain");
    }
}
