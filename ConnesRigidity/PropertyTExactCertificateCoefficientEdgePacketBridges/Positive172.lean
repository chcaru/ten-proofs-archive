


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive172
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_172 :
    coefficientPositivePacketTerms172 =
      (positiveEdgeTerms.drop 99072).take 576 := by
  unfold coefficientPositivePacketTerms172 coefficientPositivePacketRows172
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
