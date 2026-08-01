


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive149
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_149 :
    coefficientPositivePacketTerms149 =
      (positiveEdgeTerms.drop 85824).take 576 := by
  unfold coefficientPositivePacketTerms149 coefficientPositivePacketRows149
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
