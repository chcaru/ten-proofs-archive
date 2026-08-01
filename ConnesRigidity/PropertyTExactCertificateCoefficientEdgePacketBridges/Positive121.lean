
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive121
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_121 :
    coefficientPositivePacketTerms121 =
      (positiveEdgeTerms.drop 69696).take 576 := by
  unfold coefficientPositivePacketTerms121 coefficientPositivePacketRows121
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
