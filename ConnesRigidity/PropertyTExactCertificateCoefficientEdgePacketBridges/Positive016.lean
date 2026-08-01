


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive016
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_016 :
    coefficientPositivePacketTerms016 =
      (positiveEdgeTerms.drop 9216).take 576 := by
  unfold coefficientPositivePacketTerms016 coefficientPositivePacketRows016
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
