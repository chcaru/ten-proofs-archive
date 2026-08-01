


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive089
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_089 :
    coefficientPositivePacketTerms089 =
      (positiveEdgeTerms.drop 51264).take 576 := by
  unfold coefficientPositivePacketTerms089 coefficientPositivePacketRows089
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
