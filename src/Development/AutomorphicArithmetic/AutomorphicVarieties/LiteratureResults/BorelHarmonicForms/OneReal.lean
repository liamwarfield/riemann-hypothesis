module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.PetEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.AdmEx

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.OneReal
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct ComplexOrder

theorem UpperTheory.V.Lit.Bor.oneReal :
    UpperTheory.V.Lit.Bor.OneReal := by
  intro E _ _ _ a Ξ
  obtain ⟨hL, hS⟩ := xiSchur E a Ξ
  obtain ⟨G, hG, hadj⟩ := admEx E a Ξ
  have h1 : oneL E a = toL (1 : Matrix (Fin a) (Fin a) (Cinf E)) := rfl
  obtain ⟨c, hc⟩ := hS (Ξ.dmat (oneL E a)) fun X => by
    have h := hL 1 (Matrix.of X)
    rw [one_mul, mul_one, sub_self] at h
    have h0 : toL (0 : Matrix (Fin a) (Fin a) (Cinf E)) = 0 := rfl
    rw [h0, map_zero, sub_eq_zero] at h
    exact h
  have h := hadj 1
  rw [star_one, ← h1, hc, conjTranspose_smul, conjTranspose_one, smul_mul_assoc, one_mul, mul_smul_comm, mul_one] at h
  refine ⟨c.re, ?_⟩
  unfold HasOne
  rw [hc]
  ext i j
  have hi := congrFun (congrFun h i) i
  have hp : G i i ≠ 0 := (hG.diag_pos (i := i)).ne'
  simp only [Matrix.smul_apply, smul_eq_mul] at hi
  have hs : star c = c := mul_right_cancel₀ hp hi
  rw [← Complex.conj_eq_iff_re.1 hs]
  simp
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.CasXi
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

theorem UpperTheory.V.Lit.Bor.casXi :
    UpperTheory.V.Lit.Bor.CasXi := by
  intro E _ _ _ a n e he Ξ r
  obtain ⟨h1, h2⟩ := UpperTheory.V.Lit.Bor.xiSchur E a Ξ
  have h3 : IsLieHom (shift Ξ.dmat r) := (UpperTheory.V.Lit.Bor.ellFacts E a).2.2.2 _ _ r h1
  refine h2 _ fun X => ?_
  have h4 := UpperTheory.V.Lit.Bor.casComm E a n e he _ _ h3 X
  rw [shift_apply] at h4
  have h5 : Commute (cas (shift Ξ.dmat r) e) ((r * ell E a X) • (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ)) :=
    (Commute.one_right _).smul_right _
  simpa using h4.sub_right h5
end
