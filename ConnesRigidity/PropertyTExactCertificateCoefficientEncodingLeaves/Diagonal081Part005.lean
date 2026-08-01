


import ConnesRigidity.PropertyTExactCertificateCoefficientChecker
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Diagonal005
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Diagonal081Part005.Entry000







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_081_005 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Diagonal081Part005.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingDiagonal081PartCheck_005 :
    coefficientCheckData coefficientDiagonalPacketTerms005 =
      (coefficientSourceEncoding_081_005, 10137741019968) := by
  unfold coefficientCheckData coefficientSourceEncoding_081_005
  unfold coefficientDiagonalPacketTerms005 coefficientDiagonalPacketRows005
  unfold coefficientDiagonalPacketsTerms coefficientDiagonalPacketTerms
    decodeCoefficientDiagonalPacket
    coefficientDiagonalDecodedPacketTerms coefficientEdgeTerm
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
