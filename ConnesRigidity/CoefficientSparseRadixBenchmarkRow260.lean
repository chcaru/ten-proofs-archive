


import ConnesRigidity.CoefficientSparseRadixBenchmarkBase
import ConnesRigidity.CertificateLiterals.CoefficientSparseRadixBenchmarkRow260.Entry000





namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSparseExpectedRow260 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.CoefficientSparseRadixBenchmarkRow260.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientSparseRadixRow260Check :
    sparseRadixNormalize 17 0
        (coefficientFactorTermRowData productIndexDataRow260
          coefficientFullGramDataRow260) =
      sparseTermsOfIntPairs coefficientSparseExpectedRow260.toList := by
  unfold coefficientSparseExpectedRow260
    coefficientFactorTermRowData
    coefficientFullGramDataRow260
    productIndexDataRow260
  decide +kernel

set_option maxHeartbeats 0 in

theorem coefficientSparseTrieRow260Check :
    sparseTrieNormalize
        (coefficientFactorTermRowData productIndexDataRow260
          coefficientFullGramDataRow260) =
      sparseTermsOfIntPairs coefficientSparseExpectedRow260.toList := by
  unfold coefficientSparseExpectedRow260
    coefficientFactorTermRowData
    coefficientFullGramDataRow260
    productIndexDataRow260
  decide +kernel


end AffineSymplecticCertificate

end ConnesRigidity
