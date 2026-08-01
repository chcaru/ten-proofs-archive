


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive245
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_245 :
    coefficientPositivePacketTerms245 =
      (positiveEdgeTerms.drop 141120).take 576 := by
  unfold coefficientPositivePacketTerms245 coefficientPositivePacketRows245
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
