


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive133
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_133 :
    coefficientPositivePacketTerms133 =
      (positiveEdgeTerms.drop 76608).take 576 := by
  unfold coefficientPositivePacketTerms133 coefficientPositivePacketRows133
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
