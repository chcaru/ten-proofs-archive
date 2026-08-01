
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive179
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_179 :
    coefficientPositivePacketTerms179 =
      (positiveEdgeTerms.drop 103104).take 576 := by
  unfold coefficientPositivePacketTerms179 coefficientPositivePacketRows179
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
