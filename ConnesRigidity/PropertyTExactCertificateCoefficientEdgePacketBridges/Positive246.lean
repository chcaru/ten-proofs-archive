


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive246
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_246 :
    coefficientPositivePacketTerms246 =
      (positiveEdgeTerms.drop 141696).take 576 := by
  unfold coefficientPositivePacketTerms246 coefficientPositivePacketRows246
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
