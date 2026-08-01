


import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Part073B.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_073_b :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Part073B.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_073_b :
    coefficientCheckData ((coefficientPositiveTermChunk 10).drop 4500) =
      (coefficientSourceEncoding_073_b,
        20495298688) := by
  unfold coefficientCheckData coefficientSourceEncoding_073_b
  unfold coefficientPositiveTermChunk coefficientPositiveEdgeChunks
    coefficientPositiveChunkSizes positiveEdges positiveEdgeData
    positiveEdgeTermRow positiveEdgeEntries integerOuterTerms
    edgeOfData tableIndex productIndex
    productIndexDataRow
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
