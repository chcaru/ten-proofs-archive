
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive157
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_157 :
    coefficientPositivePacketTerms157 =
      (positiveEdgeTerms.drop 90432).take 576 := by
  unfold coefficientPositivePacketTerms157 coefficientPositivePacketRows157
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
