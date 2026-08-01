


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive266
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_266 :
    coefficientPositivePacketTerms266 =
      (positiveEdgeTerms.drop 153216).take 108 := by
  unfold coefficientPositivePacketTerms266 coefficientPositivePacketRows266
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
