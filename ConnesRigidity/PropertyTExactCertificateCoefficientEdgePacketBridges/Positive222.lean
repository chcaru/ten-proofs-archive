


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive222
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_222 :
    coefficientPositivePacketTerms222 =
      (positiveEdgeTerms.drop 127872).take 576 := by
  unfold coefficientPositivePacketTerms222 coefficientPositivePacketRows222
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
