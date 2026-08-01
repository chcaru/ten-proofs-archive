


import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Part059B.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_059_b :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Part059B.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_059_b :
    coefficientCheckData ((coefficientNegativeTermChunk 16).drop 2000) =
      (coefficientSourceEncoding_059_b,
        3850891136) := by
  unfold coefficientCheckData coefficientSourceEncoding_059_b
  unfold coefficientNegativeTermChunk coefficientNegativeEdgeChunks
    coefficientNegativeChunkSizes negativeEdges negativeEdgeData
    negativeEdgeTermRow negativeEdgeEntries integerOuterTerms
    edgeOfData tableIndex productIndex
    productIndexDataRow
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
