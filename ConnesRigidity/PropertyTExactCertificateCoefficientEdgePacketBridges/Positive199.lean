
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive199
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_199 :
    coefficientPositivePacketTerms199 =
      (positiveEdgeTerms.drop 114624).take 576 := by
  unfold coefficientPositivePacketTerms199 coefficientPositivePacketRows199
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
