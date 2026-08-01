
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive214
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_214 :
    coefficientPositivePacketTerms214 =
      (positiveEdgeTerms.drop 123264).take 576 := by
  unfold coefficientPositivePacketTerms214 coefficientPositivePacketRows214
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
