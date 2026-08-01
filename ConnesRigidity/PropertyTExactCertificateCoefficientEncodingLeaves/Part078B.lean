


import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Part078B.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_078_b :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Part078B.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_078_b :
    coefficientCheckData ((coefficientPositiveTermChunk 15).drop 4500) =
      (coefficientSourceEncoding_078_b,
        16393184128) := by
  unfold coefficientCheckData coefficientSourceEncoding_078_b
  unfold coefficientPositiveTermChunk coefficientPositiveEdgeChunks
    coefficientPositiveChunkSizes positiveEdges positiveEdgeData
    positiveEdgeTermRow positiveEdgeEntries integerOuterTerms
    edgeOfData tableIndex productIndex
    productIndexDataRow
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
