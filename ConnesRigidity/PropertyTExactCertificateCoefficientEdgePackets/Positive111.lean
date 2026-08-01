
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgeBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEdgePackets.Positive111.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

@[irreducible] noncomputable def coefficientPositivePacketRows111 :
    List (List Int) :=
  ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEdgePackets.Positive111.Entry000.data

noncomputable def coefficientPositivePacketTerms111 :
    List (IntegerTableTerm 73033) :=
  coefficientPositivePacketsTerms coefficientPositivePacketRows111

end AffineSymplecticCertificate

end ConnesRigidity
