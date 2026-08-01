


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive109
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_109 :
    coefficientPositivePacketTerms109 =
      (positiveEdgeTerms.drop 62784).take 576 := by
  unfold coefficientPositivePacketTerms109 coefficientPositivePacketRows109
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
