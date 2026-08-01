


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive225
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_225 :
    coefficientPositivePacketTerms225 =
      (positiveEdgeTerms.drop 129600).take 576 := by
  unfold coefficientPositivePacketTerms225 coefficientPositivePacketRows225
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
