


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive254
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_254 :
    coefficientPositivePacketTerms254 =
      (positiveEdgeTerms.drop 146304).take 576 := by
  unfold coefficientPositivePacketTerms254 coefficientPositivePacketRows254
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
