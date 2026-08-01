


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive111
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_111 :
    coefficientPositivePacketTerms111 =
      (positiveEdgeTerms.drop 63936).take 576 := by
  unfold coefficientPositivePacketTerms111 coefficientPositivePacketRows111
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
