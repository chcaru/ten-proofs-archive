
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive101
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_101 :
    coefficientPositivePacketTerms101 =
      (positiveEdgeTerms.drop 58176).take 576 := by
  unfold coefficientPositivePacketTerms101 coefficientPositivePacketRows101
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
