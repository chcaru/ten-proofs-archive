
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive099
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_099 :
    coefficientPositivePacketTerms099 =
      (positiveEdgeTerms.drop 57024).take 576 := by
  unfold coefficientPositivePacketTerms099 coefficientPositivePacketRows099
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
