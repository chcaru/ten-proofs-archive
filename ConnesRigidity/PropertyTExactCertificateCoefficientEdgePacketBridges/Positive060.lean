


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive060
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_060 :
    coefficientPositivePacketTerms060 =
      (positiveEdgeTerms.drop 34560).take 576 := by
  unfold coefficientPositivePacketTerms060 coefficientPositivePacketRows060
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
