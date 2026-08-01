


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive025
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_025 :
    coefficientPositivePacketTerms025 =
      (positiveEdgeTerms.drop 14400).take 576 := by
  unfold coefficientPositivePacketTerms025 coefficientPositivePacketRows025
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
