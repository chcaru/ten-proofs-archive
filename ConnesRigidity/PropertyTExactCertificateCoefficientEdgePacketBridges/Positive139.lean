
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive139
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_139 :
    coefficientPositivePacketTerms139 =
      (positiveEdgeTerms.drop 80064).take 576 := by
  unfold coefficientPositivePacketTerms139 coefficientPositivePacketRows139
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
