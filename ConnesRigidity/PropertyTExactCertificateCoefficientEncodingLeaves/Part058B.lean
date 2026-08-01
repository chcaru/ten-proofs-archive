


import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Part058B.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_058_b :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Part058B.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_058_b :
    coefficientCheckData ((coefficientNegativeTermChunk 15).drop 2000) =
      (coefficientSourceEncoding_058_b,
        3840083296) := by
  unfold coefficientCheckData coefficientSourceEncoding_058_b
  unfold coefficientNegativeTermChunk coefficientNegativeEdgeChunks
    coefficientNegativeChunkSizes negativeEdges negativeEdgeData
    negativeEdgeTermRow negativeEdgeEntries integerOuterTerms
    edgeOfData tableIndex productIndex
    productIndexDataRow
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
