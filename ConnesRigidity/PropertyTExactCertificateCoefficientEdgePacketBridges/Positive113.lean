
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive113
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_113 :
    coefficientPositivePacketTerms113 =
      (positiveEdgeTerms.drop 65088).take 576 := by
  unfold coefficientPositivePacketTerms113 coefficientPositivePacketRows113
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
