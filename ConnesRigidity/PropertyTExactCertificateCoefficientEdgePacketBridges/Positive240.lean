


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive240
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_240 :
    coefficientPositivePacketTerms240 =
      (positiveEdgeTerms.drop 138240).take 576 := by
  unfold coefficientPositivePacketTerms240 coefficientPositivePacketRows240
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
