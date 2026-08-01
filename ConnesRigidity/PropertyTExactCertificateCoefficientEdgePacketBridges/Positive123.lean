


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive123
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_123 :
    coefficientPositivePacketTerms123 =
      (positiveEdgeTerms.drop 70848).take 576 := by
  unfold coefficientPositivePacketTerms123 coefficientPositivePacketRows123
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
