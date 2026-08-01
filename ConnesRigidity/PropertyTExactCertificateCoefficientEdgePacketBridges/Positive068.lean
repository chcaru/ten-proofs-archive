
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive068
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_068 :
    coefficientPositivePacketTerms068 =
      (positiveEdgeTerms.drop 39168).take 576 := by
  unfold coefficientPositivePacketTerms068 coefficientPositivePacketRows068
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
