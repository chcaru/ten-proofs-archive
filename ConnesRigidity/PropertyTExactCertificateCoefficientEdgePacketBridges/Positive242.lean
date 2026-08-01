
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive242
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_242 :
    coefficientPositivePacketTerms242 =
      (positiveEdgeTerms.drop 139392).take 576 := by
  unfold coefficientPositivePacketTerms242 coefficientPositivePacketRows242
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
