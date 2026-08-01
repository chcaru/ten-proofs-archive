
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive115
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_115 :
    coefficientPositivePacketTerms115 =
      (positiveEdgeTerms.drop 66240).take 576 := by
  unfold coefficientPositivePacketTerms115 coefficientPositivePacketRows115
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
