


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive095
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_095 :
    coefficientPositivePacketTerms095 =
      (positiveEdgeTerms.drop 54720).take 576 := by
  unfold coefficientPositivePacketTerms095 coefficientPositivePacketRows095
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
