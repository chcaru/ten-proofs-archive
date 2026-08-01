


import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Part071B.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_071_b :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Part071B.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_071_b :
    coefficientCheckData ((coefficientPositiveTermChunk 8).drop 4500) =
      (coefficientSourceEncoding_071_b,
        14266874496) := by
  unfold coefficientCheckData coefficientSourceEncoding_071_b
  unfold coefficientPositiveTermChunk coefficientPositiveEdgeChunks
    coefficientPositiveChunkSizes positiveEdges positiveEdgeData
    positiveEdgeTermRow positiveEdgeEntries integerOuterTerms
    edgeOfData tableIndex productIndex
    productIndexDataRow
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
