
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive127
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_127 :
    coefficientPositivePacketTerms127 =
      (positiveEdgeTerms.drop 73152).take 576 := by
  unfold coefficientPositivePacketTerms127 coefficientPositivePacketRows127
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
