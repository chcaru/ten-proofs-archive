


import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Part053A.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_053_a :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Part053A.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_053_a :
    coefficientCheckData ((coefficientNegativeTermChunk 10).take 2000) =
      (coefficientSourceEncoding_053_a,
        3855728512) := by
  unfold coefficientCheckData coefficientSourceEncoding_053_a
  unfold coefficientNegativeTermChunk coefficientNegativeEdgeChunks
    coefficientNegativeChunkSizes negativeEdges negativeEdgeData
    negativeEdgeTermRow negativeEdgeEntries integerOuterTerms
    edgeOfData tableIndex productIndex
    productIndexDataRow
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
