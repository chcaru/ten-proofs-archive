


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive012
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_012 :
    coefficientPositivePacketTerms012 =
      (positiveEdgeTerms.drop 6912).take 576 := by
  unfold coefficientPositivePacketTerms012 coefficientPositivePacketRows012
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
