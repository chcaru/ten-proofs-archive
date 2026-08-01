
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive104
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_104 :
    coefficientPositivePacketTerms104 =
      (positiveEdgeTerms.drop 59904).take 576 := by
  unfold coefficientPositivePacketTerms104 coefficientPositivePacketRows104
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
