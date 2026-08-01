
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive007
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_007 :
    coefficientPositivePacketTerms007 =
      (positiveEdgeTerms.drop 4032).take 576 := by
  unfold coefficientPositivePacketTerms007 coefficientPositivePacketRows007
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
