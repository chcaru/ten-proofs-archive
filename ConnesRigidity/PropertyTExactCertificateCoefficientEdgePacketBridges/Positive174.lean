


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive174
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_174 :
    coefficientPositivePacketTerms174 =
      (positiveEdgeTerms.drop 100224).take 576 := by
  unfold coefficientPositivePacketTerms174 coefficientPositivePacketRows174
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
