
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive256
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_256 :
    coefficientPositivePacketTerms256 =
      (positiveEdgeTerms.drop 147456).take 576 := by
  unfold coefficientPositivePacketTerms256 coefficientPositivePacketRows256
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
