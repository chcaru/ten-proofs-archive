


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive153
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_153 :
    coefficientPositivePacketTerms153 =
      (positiveEdgeTerms.drop 88128).take 576 := by
  unfold coefficientPositivePacketTerms153 coefficientPositivePacketRows153
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
