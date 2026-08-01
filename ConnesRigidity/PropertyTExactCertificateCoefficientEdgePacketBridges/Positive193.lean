


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive193
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_193 :
    coefficientPositivePacketTerms193 =
      (positiveEdgeTerms.drop 111168).take 576 := by
  unfold coefficientPositivePacketTerms193 coefficientPositivePacketRows193
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
