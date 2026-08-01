


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive251
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_251 :
    coefficientPositivePacketTerms251 =
      (positiveEdgeTerms.drop 144576).take 576 := by
  unfold coefficientPositivePacketTerms251 coefficientPositivePacketRows251
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
