import PaperVerifier.ADComplete.PSDFoldCompiler
import PaperVerifier.ADComplete.PSDMinorsCompiler
import PaperVerifier.ADComplete.PSDFoldedFrame
import PaperVerifier.ADComplete.IntegerBounds

/-! The complete factory below depends only on N. Every determinant is
evaluated by a shared division-free Bird DAG. No input-dependent rank
test or supplied determinant port is part of this definition. -/
namespace ADComplete.PSDFactory
open CircuitAudit.CircuitCosts CircuitAudit.ProbeCircuit
open ADComplete.PSDBird ADComplete.PSDFoldCompiler

def M (N : ℕ) : ℕ := N*(N+1)/2
def tau (N : ℕ) : ℕ := PSDFoldedFrame.tau N (M N-1) (IntegerBounds.RNat N)

structure Frame (N : ℕ) where
  circuit : Circuit
  j : PairRef
  z : Fin N → PairRef

def frame (N : ℕ) : Frame N :=
  let p := probePrefix N
  let j := CircuitAudit.DistanceCircuit.build N p.circuit
  let z := PSDFoldCompiler.stage N (tau N) oneRef (p.probes.drop 1) j.1
  ⟨z.1,j.2,z.2⟩

def prefixIndex {N : ℕ} (r : Fin (N-1)) : Fin (r.val+1) → Fin N :=
  Fin.castLE (by have := r.isLt; omega)

def nextIndex {N : ℕ} (r : Fin (N-1)) : Fin N := ⟨r.val+1,by have := r.isLt; omega⟩

def residualStep {N : ℕ} (Z : Fin N → PairRef)
    (G : Matrix (Fin N) (Fin N) PairRef) (r : Fin (N-1)) (c : Circuit) : Result :=
  let e := prefixIndex r
  let k := nextIndex r
  let A := G.submatrix e e
  let b := fun i => G (e i) k
  let ds := determinantBatch (cramerVariants A b) c
  residual (Z k) (ds.2 0) (fun i => Z (e i)) (fun i => ds.2 i.succ) ds.1

def residualScan {N : ℕ} (Z : Fin N → PairRef) (G : Matrix (Fin N) (Fin N) PairRef) :
    Circuit → (Fin N → PairRef) → List (Fin (N-1)) → Circuit × (Fin N → PairRef)
  | c,V,[] => (c,V)
  | c,V,r::rs =>
    let v := residualStep Z G r c
    residualScan Z G v.1 (PSDBird.vectorWrite V (nextIndex r) v.2) rs

def residualStage {N : ℕ} (j : PairRef) (Z : Fin N → PairRef)
    (G : Matrix (Fin N) (Fin N) PairRef) (c : Circuit) : Circuit × (Fin N → PairRef) :=
  residualScan Z G c (fun _ => j) (List.finRange (N-1))

def square (p : PairRef) (c : Circuit) : Result := pairMul c p p.swap

def squareSum {ι : Type*} (W : ι → PairRef) (c : Circuit) : List ι → Result
  | [] => pairZero c
  | i::is =>
    let s := squareSum W c is
    let w := square (W i) s.1
    pairAdd w.1 w.2 s.2

def currentIndex {N : ℕ} (r : Fin (N-1)) : Fin N := ⟨r.val,by have := r.isLt; omega⟩

def chainSquare {N : ℕ} (V : Fin N → PairRef) (r : Fin (N-1)) (c : Circuit) : Result :=
  let w := pairAdd c (V (currentIndex r)) (V (nextIndex r))
  square w.2 w.1

def chainSquareSum {N : ℕ} (V : Fin N → PairRef) (c : Circuit) : List (Fin (N-1)) → Result
  | [] => pairZero c
  | r::rs =>
    let s := chainSquareSum V c rs
    let w := chainSquare V r s.1
    pairAdd w.1 w.2 s.2

def sos {N : ℕ} (hN : 0<N) (V : Fin N → PairRef) (c : Circuit) : Result :=
  let s := chainSquareSum V c (List.finRange (N-1))
  let v := square (V ⟨0,hN⟩) s.1
  pairAdd v.1 v.2 s.2

def unitCircuit : Circuit := Circuit.empty.snoc .ident
def unitRef : PairRef := ⟨0,0⟩

def compiled (N : ℕ) : Result :=
  if hN : N≤1 then (unitCircuit,unitRef) else
    let f := frame N
    let g := gramStage f.j f.z f.circuit
    let v := residualStage f.j f.z g.2 g.1
    sos (by omega) v.2 v.1

@[simp] theorem compiled_one : compiled 1=(unitCircuit,unitRef) := by simp [compiled]

end ADComplete.PSDFactory
