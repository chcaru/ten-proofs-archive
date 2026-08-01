


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive093
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_093 :
    coefficientPositivePacketTerms093 =
      (positiveEdgeTerms.drop 53568).take 576 := by
  unfold coefficientPositivePacketTerms093 coefficientPositivePacketRows093
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
