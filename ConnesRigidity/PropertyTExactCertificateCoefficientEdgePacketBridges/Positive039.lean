
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive039
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_039 :
    coefficientPositivePacketTerms039 =
      (positiveEdgeTerms.drop 22464).take 576 := by
  unfold coefficientPositivePacketTerms039 coefficientPositivePacketRows039
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
