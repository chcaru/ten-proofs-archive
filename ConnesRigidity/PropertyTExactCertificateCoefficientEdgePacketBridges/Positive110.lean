
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive110
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_110 :
    coefficientPositivePacketTerms110 =
      (positiveEdgeTerms.drop 63360).take 576 := by
  unfold coefficientPositivePacketTerms110 coefficientPositivePacketRows110
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
