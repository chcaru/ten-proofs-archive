


import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Part063A.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_063_a :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Part063A.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_063_a :
    coefficientCheckData ((coefficientPositiveTermChunk 0).take 4018) =
      (coefficientSourceEncoding_063_a,
        64046410128) := by
  unfold coefficientCheckData coefficientSourceEncoding_063_a
  unfold coefficientPositiveTermChunk coefficientPositiveEdgeChunks
    coefficientPositiveChunkSizes positiveEdges positiveEdgeData
    positiveEdgeTermRow positiveEdgeEntries integerOuterTerms
    edgeOfData tableIndex productIndex
    productIndexDataRow
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
