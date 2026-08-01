
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive053
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_053 :
    coefficientPositivePacketTerms053 =
      (positiveEdgeTerms.drop 30528).take 576 := by
  unfold coefficientPositivePacketTerms053 coefficientPositivePacketRows053
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
