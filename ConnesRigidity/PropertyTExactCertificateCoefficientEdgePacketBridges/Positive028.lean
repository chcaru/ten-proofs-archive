
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive028
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_028 :
    coefficientPositivePacketTerms028 =
      (positiveEdgeTerms.drop 16128).take 576 := by
  unfold coefficientPositivePacketTerms028 coefficientPositivePacketRows028
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
