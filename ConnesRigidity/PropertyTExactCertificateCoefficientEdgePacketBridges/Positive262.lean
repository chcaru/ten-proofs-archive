


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive262
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_262 :
    coefficientPositivePacketTerms262 =
      (positiveEdgeTerms.drop 150912).take 576 := by
  unfold coefficientPositivePacketTerms262 coefficientPositivePacketRows262
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
