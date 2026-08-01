


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive195
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_195 :
    coefficientPositivePacketTerms195 =
      (positiveEdgeTerms.drop 112320).take 576 := by
  unfold coefficientPositivePacketTerms195 coefficientPositivePacketRows195
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
