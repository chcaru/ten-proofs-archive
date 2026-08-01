
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive042
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_042 :
    coefficientPositivePacketTerms042 =
      (positiveEdgeTerms.drop 24192).take 576 := by
  unfold coefficientPositivePacketTerms042 coefficientPositivePacketRows042
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
