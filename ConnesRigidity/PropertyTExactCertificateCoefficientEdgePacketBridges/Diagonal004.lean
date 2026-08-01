
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Diagonal004
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientDiagonalPacketTermsBridge_004 :
    coefficientDiagonalPacketTerms004 =
      (diagonalTerms.drop 1024).take 256 := by
  unfold coefficientDiagonalPacketTerms004 coefficientDiagonalPacketRows004
  unfold coefficientDiagonalPacketsTerms
  unfold coefficientDiagonalPacketTerms
    decodeCoefficientDiagonalPacket
    coefficientDiagonalDecodedPacketTerms coefficientEdgeTerm
  unfold diagonalTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
