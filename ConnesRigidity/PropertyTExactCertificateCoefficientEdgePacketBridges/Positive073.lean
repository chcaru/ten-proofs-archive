


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive073
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_073 :
    coefficientPositivePacketTerms073 =
      (positiveEdgeTerms.drop 42048).take 576 := by
  unfold coefficientPositivePacketTerms073 coefficientPositivePacketRows073
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
