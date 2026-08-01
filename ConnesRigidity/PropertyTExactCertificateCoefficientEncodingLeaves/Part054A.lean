


import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Part054A.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_054_a :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Part054A.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_054_a :
    coefficientCheckData ((coefficientNegativeTermChunk 11).take 2000) =
      (coefficientSourceEncoding_054_a,
        4006444448) := by
  unfold coefficientCheckData coefficientSourceEncoding_054_a
  unfold coefficientNegativeTermChunk coefficientNegativeEdgeChunks
    coefficientNegativeChunkSizes negativeEdges negativeEdgeData
    negativeEdgeTermRow negativeEdgeEntries integerOuterTerms
    edgeOfData tableIndex productIndex
    productIndexDataRow
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
