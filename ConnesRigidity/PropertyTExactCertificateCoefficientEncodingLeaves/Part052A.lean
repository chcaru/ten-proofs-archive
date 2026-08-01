


import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Part052A.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_052_a :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Part052A.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_052_a :
    coefficientCheckData ((coefficientNegativeTermChunk 9).take 2000) =
      (coefficientSourceEncoding_052_a,
        4859031584) := by
  unfold coefficientCheckData coefficientSourceEncoding_052_a
  unfold coefficientNegativeTermChunk coefficientNegativeEdgeChunks
    coefficientNegativeChunkSizes negativeEdges negativeEdgeData
    negativeEdgeTermRow negativeEdgeEntries integerOuterTerms
    edgeOfData tableIndex productIndex
    productIndexDataRow
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
