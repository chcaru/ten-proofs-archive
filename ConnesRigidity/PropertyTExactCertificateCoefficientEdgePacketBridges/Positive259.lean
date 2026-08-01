
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive259
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_259 :
    coefficientPositivePacketTerms259 =
      (positiveEdgeTerms.drop 149184).take 576 := by
  unfold coefficientPositivePacketTerms259 coefficientPositivePacketRows259
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
