


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive155
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_155 :
    coefficientPositivePacketTerms155 =
      (positiveEdgeTerms.drop 89280).take 576 := by
  unfold coefficientPositivePacketTerms155 coefficientPositivePacketRows155
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
