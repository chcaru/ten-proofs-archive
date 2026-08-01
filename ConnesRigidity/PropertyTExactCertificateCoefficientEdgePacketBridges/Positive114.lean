


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive114
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_114 :
    coefficientPositivePacketTerms114 =
      (positiveEdgeTerms.drop 65664).take 576 := by
  unfold coefficientPositivePacketTerms114 coefficientPositivePacketRows114
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
