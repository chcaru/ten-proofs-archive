


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive156
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_156 :
    coefficientPositivePacketTerms156 =
      (positiveEdgeTerms.drop 89856).take 576 := by
  unfold coefficientPositivePacketTerms156 coefficientPositivePacketRows156
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
