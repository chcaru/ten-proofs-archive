
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive081
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_081 :
    coefficientPositivePacketTerms081 =
      (positiveEdgeTerms.drop 46656).take 576 := by
  unfold coefficientPositivePacketTerms081 coefficientPositivePacketRows081
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
