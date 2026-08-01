
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive064
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_064 :
    coefficientPositivePacketTerms064 =
      (positiveEdgeTerms.drop 36864).take 576 := by
  unfold coefficientPositivePacketTerms064 coefficientPositivePacketRows064
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
