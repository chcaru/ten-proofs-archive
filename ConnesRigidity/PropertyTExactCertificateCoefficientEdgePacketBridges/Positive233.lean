


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive233
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_233 :
    coefficientPositivePacketTerms233 =
      (positiveEdgeTerms.drop 134208).take 576 := by
  unfold coefficientPositivePacketTerms233 coefficientPositivePacketRows233
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
