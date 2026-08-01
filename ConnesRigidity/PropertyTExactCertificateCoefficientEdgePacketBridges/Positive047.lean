


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive047
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_047 :
    coefficientPositivePacketTerms047 =
      (positiveEdgeTerms.drop 27072).take 576 := by
  unfold coefficientPositivePacketTerms047 coefficientPositivePacketRows047
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
