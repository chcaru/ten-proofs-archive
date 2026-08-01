
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive100
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_100 :
    coefficientPositivePacketTerms100 =
      (positiveEdgeTerms.drop 57600).take 576 := by
  unfold coefficientPositivePacketTerms100 coefficientPositivePacketRows100
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
