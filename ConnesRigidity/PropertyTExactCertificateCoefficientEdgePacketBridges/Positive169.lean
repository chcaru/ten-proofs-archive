
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive169
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_169 :
    coefficientPositivePacketTerms169 =
      (positiveEdgeTerms.drop 97344).take 576 := by
  unfold coefficientPositivePacketTerms169 coefficientPositivePacketRows169
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
