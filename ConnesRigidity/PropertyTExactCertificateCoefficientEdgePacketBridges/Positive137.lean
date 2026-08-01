
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive137
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_137 :
    coefficientPositivePacketTerms137 =
      (positiveEdgeTerms.drop 78912).take 576 := by
  unfold coefficientPositivePacketTerms137 coefficientPositivePacketRows137
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
