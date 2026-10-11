import PaperVerifier.ADComplete.PSDFactoryValues

namespace ADComplete.PSDFactory
open ADComplete.PSDBird ADComplete.PSDHomogeneousLift

theorem nextIndex_injective {N : ℕ} : Function.Injective (@nextIndex N) := by
  intro r s h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [nextIndex] at hv
  omega

theorem nextIndex_ne_zero {N : ℕ} (hN : 0<N) (r : Fin (N-1)) : nextIndex r≠⟨0,hN⟩ := by
  intro he
  have hv := congrArg Fin.val he
  simp only [nextIndex] at hv
  omega

theorem residualVectorScan_next {N n : ℕ} (z : Fin N → Matrix (Fin n) (Fin n) ℝ)
    (g : Matrix (Fin N) (Fin N) ℝ) (w : Fin N → Matrix (Fin n) (Fin n) ℝ)
    (rs : List (Fin (N-1))) (r : Fin (N-1)) :
    residualVectorScan z g w rs (nextIndex r)=if r∈rs then residualValue z g r else w (nextIndex r) := by
  induction rs generalizing w with
  | nil => simp [residualVectorScan]
  | cons s ss ih =>
    rw [residualVectorScan,ih]
    by_cases ht : r∈ss
    · simp only [List.mem_cons,ht,or_true,ite_true]
    · by_cases he : r=s
      · subst r
        simp only [ht,ite_false,vectorWrite,ite_true,List.mem_cons,true_or]
      · have hi : nextIndex r≠nextIndex s := fun h => he (nextIndex_injective h)
        simp only [ht,ite_false,vectorWrite,hi,List.mem_cons,he,or_self]

theorem residualVectorScan_zero {N n : ℕ} (hN : 0<N)
    (z : Fin N → Matrix (Fin n) (Fin n) ℝ) (g : Matrix (Fin N) (Fin N) ℝ)
    (w : Fin N → Matrix (Fin n) (Fin n) ℝ) (rs : List (Fin (N-1))) :
    residualVectorScan z g w rs ⟨0,hN⟩=w ⟨0,hN⟩ := by
  induction rs generalizing w with
  | nil => rfl
  | cons r rs ih =>
    rw [residualVectorScan,ih]
    simp only [vectorWrite,Ne.symm (nextIndex_ne_zero hN r),ite_false]

def writtenResiduals {N n : ℕ} (z : Fin N → Matrix (Fin n) (Fin n) ℝ)
    (g : Matrix (Fin N) (Fin N) ℝ) : Fin N → Matrix (Fin n) (Fin n) ℝ :=
  fun i => if hi : i.val=0 then J n else residualValue z g ⟨i.val-1,by have := i.isLt; omega⟩

theorem residualVectorScan_complete {N n : ℕ} (hN : 0<N)
    (z : Fin N → Matrix (Fin n) (Fin n) ℝ) (g : Matrix (Fin N) (Fin N) ℝ) :
    residualVectorScan z g (fun _ => J n) (List.finRange (N-1))=writtenResiduals z g := by
  funext i
  by_cases hi : i.val=0
  · have he : i=⟨0,hN⟩ := Fin.ext hi
    subst i
    simpa [writtenResiduals] using residualVectorScan_zero hN z g (fun _ => J n) (List.finRange (N-1))
  · let r : Fin (N-1) := ⟨i.val-1,by have := i.isLt; omega⟩
    have he : nextIndex r=i := by apply Fin.ext; simp only [nextIndex,r]; omega
    have hv := residualVectorScan_next z g (fun _ => J n) (List.finRange (N-1)) r
    rw [he] at hv
    simpa only [List.mem_finRange,ite_true,writtenResiduals,dif_neg hi,r] using hv

#print axioms residualVectorScan_complete
end ADComplete.PSDFactory
