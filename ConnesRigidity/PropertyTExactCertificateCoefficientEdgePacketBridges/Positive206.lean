


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive206
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_206 :
    coefficientPositivePacketTerms206 =
      (positiveEdgeTerms.drop 118656).take 576 := by
  unfold coefficientPositivePacketTerms206 coefficientPositivePacketRows206
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
