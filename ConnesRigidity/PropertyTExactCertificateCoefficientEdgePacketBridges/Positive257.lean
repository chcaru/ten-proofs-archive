


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive257
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_257 :
    coefficientPositivePacketTerms257 =
      (positiveEdgeTerms.drop 148032).take 576 := by
  unfold coefficientPositivePacketTerms257 coefficientPositivePacketRows257
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
