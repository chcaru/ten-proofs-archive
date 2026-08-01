


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive027
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_027 :
    coefficientPositivePacketTerms027 =
      (positiveEdgeTerms.drop 15552).take 576 := by
  unfold coefficientPositivePacketTerms027 coefficientPositivePacketRows027
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
