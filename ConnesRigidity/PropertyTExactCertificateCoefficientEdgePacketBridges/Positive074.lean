


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive074
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_074 :
    coefficientPositivePacketTerms074 =
      (positiveEdgeTerms.drop 42624).take 576 := by
  unfold coefficientPositivePacketTerms074 coefficientPositivePacketRows074
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
