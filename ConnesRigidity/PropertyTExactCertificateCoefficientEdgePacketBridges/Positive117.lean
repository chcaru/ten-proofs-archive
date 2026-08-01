
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive117
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_117 :
    coefficientPositivePacketTerms117 =
      (positiveEdgeTerms.drop 67392).take 576 := by
  unfold coefficientPositivePacketTerms117 coefficientPositivePacketRows117
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
