


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive030
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_030 :
    coefficientPositivePacketTerms030 =
      (positiveEdgeTerms.drop 17280).take 576 := by
  unfold coefficientPositivePacketTerms030 coefficientPositivePacketRows030
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
