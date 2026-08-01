


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive048
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_048 :
    coefficientPositivePacketTerms048 =
      (positiveEdgeTerms.drop 27648).take 576 := by
  unfold coefficientPositivePacketTerms048 coefficientPositivePacketRows048
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
