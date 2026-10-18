/-
DKT26 verification (lane/pq-dkt-verify): axiom audit of the ArkLib declarations that
MCA-UPGRADE.md relies on.  Classic (non-`module`) file on purpose: a classic importer loads the
proof bodies, so `#print axioms` sees the whole dependency cone.
Run from an ArkLib checkout at quangvdao/ArkLib@a5aa2677 after building the imported modules:
  lake env lean <this file>
-/
import ArkLib.Data.CodingTheory.ReedSolomon.PaperGuide
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.Squarefree.Sharp
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.CurveCertificate
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.FirstOrder.Profile
import ArkLib.Data.CodingTheory.ProximityGenerator.BinaryTensorFoldAgreement

-- O-1: Thm 5.12 (Johnson line MCA, every characteristic) and list (67, pairwise part)
#print axioms ReedSolomon.johnson_lineMCA_probability
#print axioms ReedSolomon.exists_exceptional_johnson_lineMCA_allChar
#print axioms ReedSolomon.exists_exceptional_johnson_lineMCA_at_ceil
#print axioms ReedSolomon.closePolynomialSet_finite_and_ncard_le_johnsonPairwise
#print axioms ReedSolomon.exists_exceptional_weightedJohnsonMCA_fullAgreement
#print axioms ReedSolomon.weightedJohnson_mcaError_le
-- Cor 7.7 (interleaving) and Cor 7.8 (multilinear folds)
#print axioms ReedSolomon.uniformExactInterleavedPowerAgreement_of_scalar_arbitrary
#print axioms ReedSolomon.fullSetLevelWitness_interleaved_of_exactAgreement
#print axioms TensorMCA.tensorFoldBad_card_le
#print axioms TensorMCA.hasFullTensorDecomposition_of_not_mem_bad
#print axioms ReedSolomon.interleavedRS_tensorFoldBad_card_le_heightThree
-- O-2: first order (Thm 5.8 / Prop 5.10 / Lemmas 5.9, 5.11 / Cor 7.3)
#print axioms ReedSolomon.FirstOrder.firstOrderBranch_finiteLength_finiteSlack_bounds
#print axioms ReedSolomon.FirstOrder.firstOrderBranch_finiteLength_rate_bounds
#print axioms ReedSolomon.FirstOrder.firstOrderBranch_finiteLength_mcaError_le
#print axioms ReedSolomon.FirstOrder.Squarefree.exists_exceptional_retainedSquarefreeCurveMCA_sharp
#print axioms ReedSolomon.FirstOrder.Squarefree.exists_exceptional_retainedSquarefreeCurveMCA_sharp_at
#print axioms ReedSolomon.FirstOrder.Squarefree.exists_exceptional_retainedSquarefreeCurveMCA_sharp_optimized
#print axioms ReedSolomon.CurveProfile.LineProfile.CurveVerification.exists_certificate
#print axioms ReedSolomon.CurveCertificate.exists_exceptional_exact_powerAgreement
#print axioms ReedSolomon.CurveCertificate.exists_exceptional_exact_powerAgreement_squarefree_sharp
#print axioms ReedSolomon.CurveCertificate.exists_exceptional_exact_powerAgreement_squarefree_sharp_optimized
#print axioms ReedSolomon.CurveCertificate.exists_exceptional_exact_powerAgreement_squarefree_sharp_le
#print axioms ReedSolomon.CurveCertificate.exists_exceptional_exact_powerAgreement_best
#print axioms ReedSolomon.CurveCertificate.exists_exceptional_exact_powerAgreement_best_optimized
#print axioms ReedSolomon.CurveCertificate.finiteListBound_of_profile
#print axioms ReedSolomon.CurveCertificate.finiteSquarefreeListBound_of_profile
