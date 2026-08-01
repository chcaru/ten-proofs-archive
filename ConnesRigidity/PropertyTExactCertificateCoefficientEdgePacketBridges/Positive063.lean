
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive063
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_063 :
    coefficientPositivePacketTerms063 =
      (positiveEdgeTerms.drop 36288).take 576 := by
  unfold coefficientPositivePacketTerms063 coefficientPositivePacketRows063
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
