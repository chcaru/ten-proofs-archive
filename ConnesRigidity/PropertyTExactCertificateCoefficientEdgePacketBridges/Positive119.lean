
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive119
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_119 :
    coefficientPositivePacketTerms119 =
      (positiveEdgeTerms.drop 68544).take 576 := by
  unfold coefficientPositivePacketTerms119 coefficientPositivePacketRows119
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
