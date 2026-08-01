
import ConnesRigidity.CoefficientSparseRadixBenchmarkBase
import ConnesRigidity.CertificateLiterals.CoefficientSparseQuadTrieBenchmarkPart026A.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSparseQuadExpectedPart026A :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.CoefficientSparseQuadTrieBenchmarkPart026A.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientSparseQuadTriePart026ACheck :
    sparseQuadTrieNormalize
        ((coefficientFactorTermChunk026).take 2125) =
      sparseTermsOfIntPairs
        coefficientSparseQuadExpectedPart026A.toList := by
  unfold coefficientSparseQuadExpectedPart026A
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
