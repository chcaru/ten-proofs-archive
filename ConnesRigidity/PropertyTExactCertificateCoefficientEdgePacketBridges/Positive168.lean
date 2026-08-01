


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive168
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_168 :
    coefficientPositivePacketTerms168 =
      (positiveEdgeTerms.drop 96768).take 576 := by
  unfold coefficientPositivePacketTerms168 coefficientPositivePacketRows168
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
