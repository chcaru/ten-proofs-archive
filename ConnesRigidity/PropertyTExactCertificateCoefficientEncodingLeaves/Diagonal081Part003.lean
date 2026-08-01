


import ConnesRigidity.PropertyTExactCertificateCoefficientChecker
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Diagonal003
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Diagonal081Part003.Entry000







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_081_003 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Diagonal081Part003.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingDiagonal081PartCheck_003 :
    coefficientCheckData coefficientDiagonalPacketTerms003 =
      (coefficientSourceEncoding_081_003, 10149708297952) := by
  unfold coefficientCheckData coefficientSourceEncoding_081_003
  unfold coefficientDiagonalPacketTerms003 coefficientDiagonalPacketRows003
  unfold coefficientDiagonalPacketsTerms coefficientDiagonalPacketTerms
    decodeCoefficientDiagonalPacket
    coefficientDiagonalDecodedPacketTerms coefficientEdgeTerm
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
