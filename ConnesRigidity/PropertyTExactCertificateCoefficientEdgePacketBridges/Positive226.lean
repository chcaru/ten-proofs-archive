


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive226
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_226 :
    coefficientPositivePacketTerms226 =
      (positiveEdgeTerms.drop 130176).take 576 := by
  unfold coefficientPositivePacketTerms226 coefficientPositivePacketRows226
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
