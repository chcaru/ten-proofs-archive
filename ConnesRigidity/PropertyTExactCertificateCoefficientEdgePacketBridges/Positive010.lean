


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive010
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_010 :
    coefficientPositivePacketTerms010 =
      (positiveEdgeTerms.drop 5760).take 576 := by
  unfold coefficientPositivePacketTerms010 coefficientPositivePacketRows010
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
