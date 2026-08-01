
import ConnesRigidity.TotalGramPrototype.ChunkRow261Part0Data

namespace ConnesRigidity

namespace AffineSymplecticCertificate

namespace TotalGramPrototype

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem residualRow260Part0_check :
    let row := residualChunkRows
      fullReducedRow260Part0 totalReducedRow260Part0
    (row, residualSliceAbsoluteTotal 260 0 row) =
      (residualRow260Part0Expected, 28522560) := by
  unfold residualChunkRows residualSliceAbsoluteTotal
    offDiagonalAbsoluteTotal fullReducedRow260Part0
    totalReducedRow260Part0 residualRow260Part0Expected
  decide +kernel

end TotalGramPrototype

end AffineSymplecticCertificate

end ConnesRigidity
