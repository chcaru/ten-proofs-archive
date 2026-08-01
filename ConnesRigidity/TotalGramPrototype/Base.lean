


import Lean
import Init.Data.Int.Bitwise









namespace ConnesRigidity

namespace AffineSymplecticCertificate

namespace TotalGramPrototype

set_option maxRecDepth 1000000

structure Term where
  key : Nat
  numerator : Int
deriving DecidableEq

structure Lane where
  key : Nat
  encoded : Int
deriving DecidableEq



def termRow (productRow totalRow : Array Int) : List Term :=
  List.zipWith
    (fun key numerator => { key := key.toNat, numerator })
    productRow.toList totalRow.toList



def termRowSlice
    (start count : Nat) (productRow totalRow : Array Int) : List Term :=
  List.zipWith
    (fun key numerator => { key := key.toNat, numerator })
    (productRow.toList.drop start |>.take count)
    (totalRow.toList.drop start |>.take count)

def rangeSortTerms : Nat → Nat → List Term → List Term
  | 0, _, terms => terms
  | bit + 1, lower, terms =>
      let middle := lower + 2 ^ bit
      let parts := terms.partition fun term =>
        decide (term.key < middle)
      rangeSortTerms bit lower parts.1 ++
        rangeSortTerms bit middle parts.2

def sparseSummary (terms : List Term) : List (List Int) :=
  (rangeSortTerms 17 0 terms).map fun term =>
    [Int.ofNat term.key, term.numerator]

def toLane (width : Nat) (term : Term) : Lane :=
  { key := term.key / width
    encoded :=
      Int.shiftLeft term.numerator (64 * (term.key % width)) }

def rangeSortLanes : Nat → Nat → List Lane → List Lane
  | 0, _, lanes => lanes
  | bit + 1, lower, lanes =>
      let middle := lower + 2 ^ bit
      let parts := lanes.partition fun lane =>
        decide (lane.key < middle)
      rangeSortLanes bit lower parts.1 ++
        rangeSortLanes bit middle parts.2

def collapseLanes : List Lane → List Lane
  | [] => []
  | lane :: lanes =>
      match collapseLanes lanes with
      | [] => if lane.encoded = 0 then [] else [lane]
      | next :: rest =>
          if lane.key = next.key then
            let encoded := lane.encoded + next.encoded
            if encoded = 0 then rest
            else { key := lane.key, encoded } :: rest
          else if lane.encoded = 0 then next :: rest
          else lane :: next :: rest


def laneSummary (width : Nat) (terms : List Term) : List (List Int) :=
  (collapseLanes
      (rangeSortLanes 13 0 (terms.map (toLane width)))).map fun lane =>
    [Int.ofNat lane.key, lane.encoded]

def absoluteTotal (terms : List Term) : Nat :=
  (terms.map fun term => term.numerator.natAbs).sum



def residualRow (fullRow totalRow : Array Int) : List Int :=
  List.zipWith (fun total full => total - 8 * full)
    (totalRow.toList.drop 1) (fullRow.toList.drop 1)


def residualRowSlice
    (start count : Nat) (fullRow totalRow : Array Int) : List Int :=
  List.zipWith (fun total full => total - 8 * full)
    (totalRow.toList.drop (start + 1) |>.take count)
    (fullRow.toList.drop (start + 1) |>.take count)


def residualChunkRows
    (fullRow totalRow : Array Int) : List Int :=
  List.zipWith (fun total full => total - 8 * full)
    totalRow.toList fullRow.toList

def offDiagonalAbsoluteTotal : Nat → Nat → List Int → Nat
  | _, _, [] => 0
  | diagonal, index, entry :: entries =>
      (if index = diagonal then 0 else entry.natAbs) +
        offDiagonalAbsoluteTotal diagonal (index + 1) entries


def residualSliceAbsoluteTotal
    (diagonal start : Nat) (row : List Int) : Nat :=
  offDiagonalAbsoluteTotal diagonal start row


def residualSliceCheckData
    (diagonal start count : Nat) (fullRow totalRow : Array Int) :
    List Int × Nat :=
  let row := residualRowSlice start count fullRow totalRow
  (row, residualSliceAbsoluteTotal diagonal start row)

def residualSlack (diagonal : Nat) (row : List Int) : Int :=
  row.getD diagonal 0 -
    Int.ofNat (offDiagonalAbsoluteTotal diagonal 0 row)

def residualCheckData
    (diagonal : Nat) (fullRow totalRow : Array Int) :
    List Int × Int :=
  let row := residualRow fullRow totalRow
  (row, residualSlack diagonal row)

end TotalGramPrototype

end AffineSymplecticCertificate

end ConnesRigidity
