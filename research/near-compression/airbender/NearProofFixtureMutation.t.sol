// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

/// Targeted rejection checks derived from the upstream two-transaction fixture harness.
/// Uses the actual compiled GKR/WHIR verifiers and registered authority pair.
/// These tests do not establish general soundness or quantum security.

import {GkrWhirRegistry} from "../src/GkrWhirRegistry.sol";

interface Vm {
    function readFile(string calldata path) external view returns (string memory);
    function parseBytes(string calldata s) external pure returns (bytes memory);
    function parseJsonBytes(string calldata json, string calldata key) external pure returns (bytes memory);
    function etch(address who, bytes calldata code) external;
    function recordLogs() external;
    function getRecordedLogs() external returns (Log[] memory);
}
struct Log { bytes32[] topics; bytes data; }

contract NearProofFixtureMutationTest {
    Vm constant vm = Vm(0x7109709ECfa91a80626fF3989D68f67F5b1DD12D);
    address constant REGISTRY = address(uint160(0xCAFE0001));
    address constant GKR = address(uint160(0x611b0001));
    address constant WHIR = address(uint160(0x11170001));

    event log_named_bytes32(string key, bytes32 val);

    function _calldata(string memory p) internal view returns (bytes memory) {
        return vm.parseBytes(string.concat("0x", vm.readFile(p)));
    }

    // deployedBytecode.object from a sibling project's compiled artifact JSON.
    function _deployed(string memory artifactPath) internal view returns (bytes memory) {
        return vm.parseJsonBytes(vm.readFile(artifactPath), ".deployedBytecode.object");
    }

    function checkMutation(bool gkr, uint256 offset, uint256 mode) internal {
        // Registry at the fixed address both verifiers call; the two verifiers etched from the
        // sibling projects' compiled bytecode.
        GkrWhirRegistry impl = new GkrWhirRegistry(address(this));
        vm.etch(REGISTRY, address(impl).code);
        vm.etch(GKR, _deployed("../gkr/out/GkrVerifier.sol/GKRVerifier.json"));
        vm.etch(WHIR, _deployed("../whir/out/WhirVerifier.sol/WhirVerifier.json"));
        GkrWhirRegistry(REGISTRY).initialize_verifiers(GKR, WHIR);

        bytes memory gkrCd = _calldata("../../debug_data/gkr_full_calldata.hex");
        bytes memory whirCd = _calldata("../../debug_data/proth120_whir_calldata_from_proof.hex");

        bytes memory original = gkr ? gkrCd : whirCd;
        bytes memory changed;
        if (mode == 0) {
            changed = original;
            changed[offset] = bytes1(uint8(changed[offset]) ^ 1);
        } else {
            uint256 len = mode == 1 ? original.length - 1 : original.length + 1;
            changed = new bytes(len);
            for (uint256 i = 0; i < len && i < original.length; i++) changed[i] = original[i];
        }
        if (gkr) gkrCd = changed; else whirCd = changed;

        // ---- tx1: GKR verifier ----
        vm.recordLogs();
        (bool ok1, ) = GKR.call(gkrCd);
        if (gkr) { require(!ok1, "corrupted GKR accepted"); return; }
        require(ok1, "honest GKR reverted");
        Log[] memory l1 = vm.getRecordedLogs();
        require(l1.length == 1, "expected 1 GkrVerified event");

        // ---- tx2: WHIR verifier ----
        vm.recordLogs();
        (bool ok2, ) = WHIR.call(whirCd);
        require(!ok2, "corrupted WHIR accepted");
        return;
    }
    function test_gkr_first_bit_flip() external { checkMutation(true, 0, 0); }
    function test_gkr_middle_bit_flip() external { checkMutation(true, 17298, 0); }
    function test_gkr_last_bit_flip() external { checkMutation(true, 34595, 0); }
    function test_gkr_truncated() external { checkMutation(true, 0, 1); }
    function test_gkr_appended() external { checkMutation(true, 0, 2); }
    function test_whir_first_bit_flip() external { checkMutation(false, 0, 0); }
    function test_whir_middle_bit_flip() external { checkMutation(false, 38272, 0); }
    function test_whir_last_bit_flip() external { checkMutation(false, 76543, 0); }
    function test_whir_truncated() external { checkMutation(false, 0, 1); }
    function test_whir_appended() external { checkMutation(false, 0, 2); }
}
