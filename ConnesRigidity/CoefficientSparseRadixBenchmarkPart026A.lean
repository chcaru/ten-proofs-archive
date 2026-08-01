


import ConnesRigidity.CoefficientSparseRadixBenchmarkBase
import ConnesRigidity.CertificateLiterals.CoefficientSparseRadixBenchmarkPart026A.Entry000





namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSparseRadixExpectedPart026A :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.CoefficientSparseRadixBenchmarkPart026A.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientSparseRadixPart026ACheck :
    sparseRadixNormalize 17 0
        ((coefficientFactorTermChunk026).take 2125) =
      sparseTermsOfIntPairs
        coefficientSparseRadixExpectedPart026A.toList := by
  unfold coefficientSparseRadixExpectedPart026A
    coefficientFactorTermChunk026
    coefficientFactorTermRowData
    coefficientFullGramDataRow260
    coefficientFullGramDataRow261
    coefficientFullGramDataRow262
    coefficientFullGramDataRow263
    coefficientFullGramDataRow264
    coefficientFullGramDataRow265
    coefficientFullGramDataRow266
    coefficientFullGramDataRow267
    coefficientFullGramDataRow268
    coefficientFullGramDataRow269
    productIndexDataRow260
    productIndexDataRow261
    productIndexDataRow262
    productIndexDataRow263
    productIndexDataRow264
    productIndexDataRow265
    productIndexDataRow266
    productIndexDataRow267
    productIndexDataRow268
    productIndexDataRow269
  decide +kernel


end AffineSymplecticCertificate

end ConnesRigidity
