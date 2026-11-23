import PEqualNP.Defs
import PEqualNP.MetaComplexity.L100
import PEqualNP.MetaComplexity.L153

namespace PEqualNP.Outside.L_meta_764

open PEqualNP.MetaComplexity

def g3 : (Fin 3 → Bool) → Bool :=
  fun x : Fin 3 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 0 && x 2)

def f5 : (Fin 5 → Bool) → Bool :=
  fun x : Fin 5 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4)

lemma g3_nc : ∃ y y' : Fin 3 → Bool, g3 y ≠ g3 y' :=
  ⟨fun _ => false, fun _ => true, by decide⟩

lemma f5_eq : f5 = (fun x : Fin (2 + 3) → Bool => (x (Fin.castAdd 3 0) && x (Fin.castAdd 3 1)) || g3 (fun j : Fin 3 => x (Fin.natAdd 2 j))) := by
  funext x
  change ((x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4)) =
    ((x 0 && x 1) || ((x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4)))
  cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> cases x 4 <;> rfl

lemma hasCircuitSize_mono {n : ℕ} {f : (Fin n → Bool) → Bool} {s t : ℕ} (hst : s ≤ t)
    (h : HasCircuitSize n f s) : HasCircuitSize n f t := by
  obtain ⟨C, h1, h2, h3⟩ := h
  exact ⟨C, h1, le_trans h2 hst, h3⟩

lemma size_add_two (t : ℕ) : HasCircuitSize 5 f5 (t + 2) ↔ 4 ≤ t := by
  rw [f5_eq]
  exact (PEqualNP.MetaComplexity.L153 3 t g3 g3_nc).trans (PEqualNP.MetaComplexity.L100 t)

end PEqualNP.Outside.L_meta_764

open PEqualNP.Outside.L_meta_764 in
theorem PEqualNP.Outside.L_meta_764 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4)) s ↔ 6 ≤ s := by
  intro s
  change PEqualNP.MetaComplexity.HasCircuitSize 5 f5 s ↔ 6 ≤ s
  constructor
  · intro h
    by_contra hlt
    have h6 : PEqualNP.MetaComplexity.HasCircuitSize 5 f5 (3 + 2) := hasCircuitSize_mono (by omega) h
    have h4 : 4 ≤ 3 := (size_add_two 3).mp h6
    omega
  · intro hs
    have heq : s = (s - 2) + 2 := by omega
    rw [heq]
    exact (size_add_two (s - 2)).mpr (by omega)
