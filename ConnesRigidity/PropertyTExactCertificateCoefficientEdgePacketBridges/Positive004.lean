
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive004
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_004 :
    coefficientPositivePacketTerms004 =
      (positiveEdgeTerms.drop 2304).take 576 := by
  unfold coefficientPositivePacketTerms004 coefficientPositivePacketRows004
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
