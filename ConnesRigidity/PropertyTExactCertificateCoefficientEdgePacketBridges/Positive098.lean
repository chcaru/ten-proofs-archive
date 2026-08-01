


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive098
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_098 :
    coefficientPositivePacketTerms098 =
      (positiveEdgeTerms.drop 56448).take 576 := by
  unfold coefficientPositivePacketTerms098 coefficientPositivePacketRows098
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
