


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive124
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_124 :
    coefficientPositivePacketTerms124 =
      (positiveEdgeTerms.drop 71424).take 576 := by
  unfold coefficientPositivePacketTerms124 coefficientPositivePacketRows124
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
