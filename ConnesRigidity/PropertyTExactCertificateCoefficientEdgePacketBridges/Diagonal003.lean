


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Diagonal003
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientDiagonalPacketTermsBridge_003 :
    coefficientDiagonalPacketTerms003 =
      (diagonalTerms.drop 768).take 256 := by
  unfold coefficientDiagonalPacketTerms003 coefficientDiagonalPacketRows003
  unfold coefficientDiagonalPacketsTerms
  unfold coefficientDiagonalPacketTerms
    decodeCoefficientDiagonalPacket
    coefficientDiagonalDecodedPacketTerms coefficientEdgeTerm
  unfold diagonalTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
