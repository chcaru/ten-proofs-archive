


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive062
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_062 :
    coefficientPositivePacketTerms062 =
      (positiveEdgeTerms.drop 35712).take 576 := by
  unfold coefficientPositivePacketTerms062 coefficientPositivePacketRows062
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
