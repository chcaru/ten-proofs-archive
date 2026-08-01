
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive215
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_215 :
    coefficientPositivePacketTerms215 =
      (positiveEdgeTerms.drop 123840).take 576 := by
  unfold coefficientPositivePacketTerms215 coefficientPositivePacketRows215
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
