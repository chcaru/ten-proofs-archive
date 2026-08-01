


import ConnesRigidity.CoefficientSparseRadixBenchmarkBase
import ConnesRigidity.CertificateLiterals.CoefficientSparseTrieBenchmarkRow260.Entry000





namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSparseTrieExpectedRow260 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.CoefficientSparseTrieBenchmarkRow260.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientSparseTrieOnlyRow260Check :
    sparseTrieNormalize
        (coefficientFactorTermRowData productIndexDataRow260
          coefficientFullGramDataRow260) =
      sparseTermsOfIntPairs
        coefficientSparseTrieExpectedRow260.toList := by
  unfold coefficientSparseTrieExpectedRow260
    coefficientFactorTermRowData
    coefficientFullGramDataRow260
    productIndexDataRow260
  decide +kernel


end AffineSymplecticCertificate

end ConnesRigidity
