
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive120
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_120 :
    coefficientPositivePacketTerms120 =
      (positiveEdgeTerms.drop 69120).take 576 := by
  unfold coefficientPositivePacketTerms120 coefficientPositivePacketRows120
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
