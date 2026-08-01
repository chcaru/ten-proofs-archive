


import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Part080B.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_080_b :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Part080B.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_080_b :
    coefficientCheckData ((coefficientPositiveTermChunk 17).drop 643) =
      (coefficientSourceEncoding_080_b,
        2336542416) := by
  unfold coefficientCheckData coefficientSourceEncoding_080_b
  unfold coefficientPositiveTermChunk coefficientPositiveEdgeChunks
    coefficientPositiveChunkSizes positiveEdges positiveEdgeData
    positiveEdgeTermRow positiveEdgeEntries integerOuterTerms
    edgeOfData tableIndex productIndex
    productIndexDataRow
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
