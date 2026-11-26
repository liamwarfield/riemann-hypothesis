module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPadicEquiv
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertHeckeOperatorPreservesLevelInvariants

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertLocalSurjectiveFromTrivOutside
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertLocalSurjectiveFromTrivOutside
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open TensorProduct

namespace GlobalTheory.InertSurj

theorem exists_supported (L : Type) [Field L] [NumberField L] [IsCMField L]
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (m : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L)) :
    ∃ z : AL L, compAt L v z = m ∧ ∀ u, u ≠ v → compAt L u z = 0 := by
  let b : Module.Basis (Fin 2) (maximalRealSubfield L) L := Module.finBasisOfFinrankEq _ _
    (Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield L) L)
  obtain ⟨a, c, h⟩ := GlobalTheory.InertUmax.tensor_decomp b m
  refine ⟨b 0 ⊗ₜ[maximalRealSubfield L] GlobalTheory.InertUmax.sgl L v a +
    b 1 ⊗ₜ[maximalRealSubfield L] GlobalTheory.InertUmax.sgl L v c, ?_, ?_⟩
  · rw [map_add (f := _), GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.sgl_same,
      GlobalTheory.InertUmax.sgl_same, h]
  · intro u hu
    rw [map_add (f := _), GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.sgl_ne L v a hu,
      GlobalTheory.InertUmax.sgl_ne L v c hu, tmul_zero, tmul_zero, add_zero]

theorem compAt_conjAL (L : Type) [Field L] [NumberField L] [IsCMField L]
    (u : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (z : AL L) :
    compAt L u (conjAL L z) = Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom
      (u.adicCompletion (maximalRealSubfield L)) (compAt L u z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [GlobalTheory.InertUmax.compAt_tmul]
    simp [conjAL, Formalism.UG.sigR, Algebra.TensorProduct.map_tmul, GlobalTheory.InertUmax.compAt_tmul]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem loc_surj : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (y : GL (Fin n) (w.adicCompletion L)), y ∈ Formalism.UG.GU Dv.σw n → ∃ x : GAf L n, TrivOutside {v} x ∧ Dv.loc x = y := by
  intro L _ _ _ n v w Dv y hy
  classical
  let sig := Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom (v.adicCompletion (maximalRealSubfield L))
  let eS : w.adicCompletion L →+* L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L) :=
    Dv.e.symm.toRingHom
  have hcomm : ∀ a, sig (eS a) = eS (Dv.σw a) := by
    intro a
    apply Dv.e.injective
    have h := Dv.comm (eS a)
    simp only [eS, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply] at h ⊢
    exact h
  let Pm : Matrix (Fin n) (Fin n) (w.adicCompletion L) := (Dv.P : Matrix (Fin n) (Fin n) _)
  let Qm : Matrix (Fin n) (Fin n) (w.adicCompletion L) := ((Dv.P⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _)
  let Ym : Matrix (Fin n) (Fin n) (w.adicCompletion L) := (y : Matrix (Fin n) (Fin n) _)
  have hPQ : Pm * Qm = 1 := by simp [Pm, Qm]
  have hy' : Formalism.UG.cT Dv.σw Ym * Formalism.UG.antiJ (w.adicCompletion L) n * Ym =
      Formalism.UG.antiJ (w.adicCompletion L) n := hy
  let X := Pm * Ym * Qm
  have hX : Formalism.UG.cT Dv.σw X * X = 1 := by
    have hP := Dv.Panti
    change Formalism.UG.cT Dv.σw Pm * Pm = _ at hP
    calc Formalism.UG.cT Dv.σw X * X
        = Formalism.UG.cT Dv.σw Qm * (Formalism.UG.cT Dv.σw Ym * (Formalism.UG.cT Dv.σw Pm * Pm) * Ym) * Qm := by
          simp only [X, Formalism.UG.cT_mul, Matrix.mul_assoc]
      _ = Formalism.UG.cT Dv.σw Qm * (Formalism.UG.cT Dv.σw Pm * Pm) * Qm := by rw [hP, hy']
      _ = Formalism.UG.cT Dv.σw (Pm * Qm) * (Pm * Qm) := by
          simp only [Formalism.UG.cT_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hPQ, Formalism.UG.cT_one, Matrix.one_mul]
  have hX' : X * Formalism.UG.cT Dv.σw X = 1 := mul_eq_one_comm.mp hX
  let M := X.map eS
  have hMc : conjT sig M = (Formalism.UG.cT Dv.σw X).map eS := by
    ext i j
    simp [M, conjT, Formalism.UG.cT, hcomm]
  have hM : M * conjT sig M = 1 := by
    rw [hMc]
    change X.map eS * (Formalism.UG.cT Dv.σw X).map eS = 1
    rw [← Matrix.map_mul, hX', Matrix.map_one _ (map_zero _) (map_one _)]
  choose lift hlv hlw using GlobalTheory.InertSurj.exists_supported L v
  let E : AL L := (1 : L) ⊗ₜ[maximalRealSubfield L] GlobalTheory.InertUmax.sgl L v 1
  have hEv : compAt L v E = 1 := by
    rw [GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.sgl_same]; rfl
  have hEw : ∀ u, u ≠ v → compAt L u E = 0 := by
    intro u hu
    rw [GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.sgl_ne L v 1 hu, tmul_zero]
  let Z : Matrix (Fin n) (Fin n) (AL L) := M.map lift + (1 - E) • (1 : Matrix (Fin n) (Fin n) (AL L))
  have hZv : Z.map (compAt L v) = M := by
    ext i j
    simp only [Z, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add (f := _), map_mul,
      map_sub, map_one, hEv, hlv, sub_self, zero_mul, add_zero]
  have hZw : ∀ u, u ≠ v → Z.map (compAt L u) = 1 := by
    intro u hu
    ext i j
    simp only [Z, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add (f := _), map_mul,
      map_sub, map_one, hEw u hu, hlw _ u hu, sub_zero, one_mul, zero_add]
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hZconj : ∀ u, (conjT (conjAL L) Z).map (compAt L u) =
      conjT (Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom (u.adicCompletion (maximalRealSubfield L)))
        (Z.map (compAt L u)) := by
    intro u
    ext i j
    simp [conjT, GlobalTheory.InertSurj.compAt_conjAL]
  have hZZ : Z * conjT (conjAL L) Z = 1 := by
    ext i j
    rw [← sub_eq_zero]
    apply GlobalTheory.InertUmax.eq_zero_of_compAt
    intro u
    have key : (Z * conjT (conjAL L) Z).map (compAt L u) = 1 := by
      rw [Matrix.map_mul, hZconj]
      rcases eq_or_ne u v with rfl | hu
      · rw [hZv]; exact hM
      · rw [hZw u hu, conjT_one, Matrix.one_mul]
    have h1 := congrFun (congrFun key i) j
    have h2 := congrFun (congrFun (Matrix.map_one (compAt L u) (map_zero _) (map_one _)) i) j
    simp only [Matrix.map_apply] at h1 h2
    rw [map_sub, h1, h2, sub_self]
  have hZZ' : conjT (conjAL L) Z * Z = 1 := mul_eq_one_comm.mp hZZ
  let g : GL (Fin n) (AL L) := ⟨Z, conjT (conjAL L) Z, hZZ, hZZ'⟩
  have hg : g ∈ ReciprocityTheory.Aut.GA L n := hZZ
  refine ⟨⟨g, hg⟩, ?_, ?_⟩
  · intro u hu
    exact hZw u (by simpa using hu)
  · have hb : Formalism.UG.bc (n := Fin n)
        (Dv.e : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L) →+* w.adicCompletion L)
        (Matrix.GeneralLinearGroup.map (compAt L v) (((⟨g, hg⟩ : GAf L n)) : GL (Fin n) (AL L))) =
        Dv.P * y * Dv.P⁻¹ := by
      apply Units.ext
      change (Z.map (compAt L v)).map _ = X
      rw [hZv]
      ext i j
      simp [M, eS]
    unfold InertDatum.loc
    rw [hb]
    group

end GlobalTheory.InertSurj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertLocalSurjectiveFromTrivOutsideStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertLocal_surjective_from_trivOutside : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (y : GL (Fin n) (w.adicCompletion L)), y ∈ Formalism.UG.GU Dv.σw n → ∃ x : GAf L n, TrivOutside {v} x ∧ Dv.loc x = y := by
  first | exact @GlobalTheory.InertSurj.loc_surj | exact GlobalTheory.InertSurj.loc_surj | (intros; apply GlobalTheory.InertSurj.loc_surj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertHeckeOperatorPreservesProductLevelInvarianc
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertHeckeOperatorPreservesProductLevelInvarianc
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.InertSatInv.heckeFunI_rt_invariant_prod : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (U : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) → (∀ κ ∈ U, ∃ a b : GAf L n, κ = a * b ∧ a ∈ Umax L n ∧ TrivOutside {v} a ∧ b ∈ U ∧ ∀ x : GAf L n, TrivOutside {v} x → b * x = x * b) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (h : Formalism.UG.GU Dv.σw n → ℂ), h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n) → ∀ f : GAf L n → W, (∀ κ ∈ U, NG.rt L n κ f = f) → ∀ κ ∈ U, NG.rt L n κ (heckeFunI L n U Dv h f) = heckeFunI L n U Dv h f := by
  intro L _ _ _ n v w Dv U hU hsplit W _ _ h hh f hf κ hκ
  refine GlobalTheory.heckeFunI_rt_invariant L n v w Dv U hU ?_ W h hh f hf κ hκ
  intro u hu
  obtain ⟨a, b, rfl, haM, hat, hbU, hbc⟩ := hsplit u hu
  exact ⟨a, b, rfl, (hU a hat).2 haM, hat, hbU, fun x hx => (hbc x hx).symm⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertHeckeOperatorPreservesProductLevelInvariancStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertHeckeOperator_preserves_productLevel_invariance : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (U : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) → (∀ κ ∈ U, ∃ a b : GAf L n, κ = a * b ∧ a ∈ Umax L n ∧ TrivOutside {v} a ∧ b ∈ U ∧ ∀ x : GAf L n, TrivOutside {v} x → b * x = x * b) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (h : Formalism.UG.GU Dv.σw n → ℂ), h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n) → ∀ f : GAf L n → W, (∀ κ ∈ U, NG.rt L n κ f = f) → ∀ κ ∈ U, NG.rt L n κ (heckeFunI L n U Dv h f) = heckeFunI L n U Dv h f := by
  exact @GlobalTheory.InertSatInv.heckeFunI_rt_invariant_prod
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertHeckeOperatorMaximalCompactIndicatorEqId
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertHeckeOperatorMaximalCompactIndicatorEqId
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open Formalism.UG

namespace GlobalTheory.InertHeckeOne


open Classical in
theorem heckeFunI_one : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (U : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (f : GAf L n → W), (∀ κ ∈ U, NG.rt L n κ f = f) → heckeFunI L n U Dv (Formalism.UG.dosetInd ℂ (Formalism.UG.KU Dv.σw n) 1) f = f := by
  intro L _ _ _ n v w Dv U hU W _ _ f hf
  have hfU : ∀ κ ∈ U, ∀ g, f (g * κ) = f g := fun κ hκ g => congrFun (hf κ hκ) g
  have key : ∀ x : GAf L n, TrivOutside {v} x →
      Dv.hval (Formalism.UG.dosetInd ℂ (Formalism.UG.KU Dv.σw n) 1) (Dv.loc x) = if x ∈ U then 1 else 0 := by
    intro x hx
    have hg := GlobalTheory.T.inertLocal_mem_unitaryGroup_antidiagonalForm L n v w Dv x
    unfold InertDatum.hval
    rw [dite_eq_left hg]
    by_cases hxU : x ∈ U
    · rw [if_pos hxU]
      have hK := GlobalTheory.T.inertLocal_mem_integralPoints_of_latticeStabilizer L n v w Dv x ((hU x hx).1 hxU) hg
      unfold Formalism.UG.dosetInd
      rw [Set.indicator_of_mem]
      · rfl
      · rw [DoubleCoset.mem_doubleCoset]
        exact ⟨_, hK, 1, one_mem _, by simp⟩
    · rw [if_neg hxU]
      unfold Formalism.UG.dosetInd
      apply Set.indicator_of_notMem
      intro hmem
      rw [DoubleCoset.mem_doubleCoset] at hmem
      obtain ⟨a, ha, b, hb, e⟩ := hmem
      have hK : (⟨Dv.loc x, hg⟩ : Formalism.UG.GU Dv.σw n) ∈ Formalism.UG.KU Dv.σw n := by
        rw [e, mul_one]; exact mul_mem ha hb
      have hK' := hK
      simp only [Formalism.UG.KU, Subgroup.mem_subgroupOf, Formalism.UG.intPts, Subgroup.mem_inf] at hK'
      apply hxU
      refine (hU x hx).2 (GlobalTheory.InertUmax.mem_Umax_of_trivOutside_of_loc_integral L n v w Dv x hx ?_)
      intro i j
      exact GlobalTheory.InertUmax.entries_mem_of_range _ _ hK'.2 i j
  funext g
  unfold heckeFunI
  have h1 : TrivOutside {v} (1 : GAf L n) := by
    intro u _
    simp
  rw [finsum_eq_single _ ((1 : GAf L n) : GAf L n ⧸ U)]
  · have hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = ((1 : GAf L n) : GAf L n ⧸ U) ∧ TrivOutside {v} x := ⟨1, rfl, h1⟩
    rw [dite_eq_left hc]
    have hmem : hc.choose ∈ U := by
      have := QuotientGroup.eq.1 hc.choose_spec.1.symm
      simpa using this
    rw [key _ hc.choose_spec.2, if_pos hmem, one_smul, hfU _ hmem]
  · intro c hc1
    split_ifs with hc
    · rw [key _ hc.choose_spec.2, if_neg, zero_smul]
      intro hmem
      apply hc1
      rw [← hc.choose_spec.1]
      exact QuotientGroup.eq.2 (by simpa using U.inv_mem hmem)
    · rfl

end GlobalTheory.InertHeckeOne
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertHeckeOperatorMaximalCompactIndicatorEqIdStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertHeckeOperator_maximalCompact_indicator_eq_id : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (U : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (f : GAf L n → W), (∀ κ ∈ U, NG.rt L n κ f = f) → heckeFunI L n U Dv (Formalism.UG.dosetInd ℂ (Formalism.UG.KU Dv.σw n) 1) f = f := by
  first | exact @GlobalTheory.InertHeckeOne.heckeFunI_one | exact GlobalTheory.InertHeckeOne.heckeFunI_one | (intros; apply GlobalTheory.InertHeckeOne.heckeFunI_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertHeckeOperatorConvolutionEqComp
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertHeckeOperatorConvolutionEqComp
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.UG

noncomputable section

open GlobalTheory.SatInd

namespace GlobalTheory.InertConvMul

theorem eq_of_coset {G : Type} [Group G] {K : Subgroup G} {k : Type} {H : G → k}
    (hH : ∀ (a : G) (c : K), H (a * c) = H a) {a b : G} (hab : (a : G ⧸ K) = b) : H a = H b := by
  have hc := QuotientGroup.eq.1 hab
  have := hH a ⟨a⁻¹ * b, hc⟩
  change H (a * (a⁻¹ * b)) = H a at this
  rw [mul_inv_cancel_left] at this
  exact this.symm

theorem finsum_eq_of_support_subset_range {α β M : Type} [AddCommMonoid M] {F : α → M} {e : β → α}
    (he : Function.Injective e) (hs : Function.support F ⊆ Set.range e) :
    ∑ᶠ c, F c = ∑ᶠ d, F (e d) := by
  rw [← finsum_mem_range he, ← finsum_mem_inter_support, Set.inter_eq_right.2 hs, finsum_mem_support]

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
  {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {w : HeightOneSpectrum (𝓞 L)}

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem conv_of (Dv : InertDatum L n v w) (U : Subgroup (GAf L n))
    (hU : ∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n))
    (hA : ∀ x : GAf L n, Dv.loc x ∈ GU Dv.σw n)
    (hK : ∀ u ∈ Umax L n, (⟨Dv.loc u, hA u⟩ : GU Dv.σw n) ∈ KU Dv.σw n)
    (hC : ∀ y ∈ GU Dv.σw n, ∃ x : GAf L n, TrivOutside {v} x ∧ Dv.loc x = y)
    (W : Type) [AddCommGroup W] [Module ℂ W]
    (h : GU Dv.σw n → ℂ) (hh : h ∈ Hecke ℂ (KU Dv.σw n))
    (h' : GU Dv.σw n → ℂ) (hh' : h' ∈ Hecke ℂ (KU Dv.σw n))
    (f : GAf L n → W) (hf : ∀ κ ∈ U, NG.rt L n κ f = f) :
    heckeFunI L n U Dv (conv (KU Dv.σw n) h h') f =
      heckeFunI L n U Dv h (heckeFunI L n U Dv h' f) := by
  classical
  set K := KU Dv.σw n with hKdef
  let lam : GAf L n →* GU Dv.σw n := MonoidHom.codRestrict (GlobalTheory.SatInd.CosetFin.locHom Dv) _ hA
  have hlam : ∀ x, ((lam x : GU Dv.σw n) : GL (Fin n) (w.adicCompletion L)) = Dv.loc x := fun _ => rfl
  have hK1 : ∀ u ∈ Umax L n, lam u ∈ K := hK
  have hR : ∀ x x' : GAf L n, TrivOutside {v} x → TrivOutside {v} x' →
      ((x : GAf L n ⧸ U) = x' ↔ ((lam x : GU Dv.σw n ⧸ K) = lam x')) := by
    intro x x' hx hx'
    have ht : TrivOutside {v} (x⁻¹ * x') :=
      GlobalTheory.SatInd.CosetFin.trivOutside_mul (GlobalTheory.SatInd.CosetFin.trivOutside_inv hx) hx'
    rw [QuotientGroup.eq, QuotientGroup.eq, ← map_inv, ← map_mul]
    constructor
    · intro hu; exact hK1 _ ((hU _ ht).1 hu)
    · intro hk
      exact (hU _ ht).2 (GlobalTheory.InertUmax.mem_Umax_of_trivOutside_of_loc_integral L n v w Dv _ ht fun i j => GlobalTheory.SatInd.CosetFin.entries_int hk i j)
  have hCs : ∀ d : GU Dv.σw n ⧸ K, ∃ x : GAf L n, TrivOutside {v} x ∧ lam x = d.out := fun d => by
    obtain ⟨x, hx, e⟩ := hC _ d.out.2
    exact ⟨x, hx, Subtype.ext e⟩
  choose s hs1 hs2 using hCs
  have heT : ∀ d : GU Dv.σw n ⧸ K, ∃ x : GAf L n, (x : GAf L n ⧸ U) = (s d : GAf L n ⧸ U) ∧
      TrivOutside {v} x := fun d => ⟨s d, rfl, hs1 d⟩
  have hρ1 : ∀ d, TrivOutside {v} (heT d).choose := fun d => (heT d).choose_spec.2
  have hρ2 : ∀ d, ((lam (heT d).choose : GU Dv.σw n) : GU Dv.σw n ⧸ K) = d := fun d => by
    rw [(hR _ _ (hρ1 d) (hs1 d)).1 (heT d).choose_spec.1, hs2 d, QuotientGroup.out_eq']
  have he : Function.Injective (fun d : GU Dv.σw n ⧸ K => ((s d : GAf L n) : GAf L n ⧸ U)) := by
    intro d d' hdd
    have := (hR _ _ (hs1 d) (hs1 d')).1 hdd
    rwa [hs2, hs2, QuotientGroup.out_eq', QuotientGroup.out_eq'] at this

  have step2 : ∀ (H : GU Dv.σw n → ℂ), (∀ (a : GU Dv.σw n) (c : K), H (a * c) = H a) →
      ∀ (F : GAf L n → W) (g : GAf L n),
      heckeFunI L n U Dv H F g = ∑ᶠ d : GU Dv.σw n ⧸ K, H d.out • F (g * (heT d).choose) := by
    intro H hH F g
    show (∑ᶠ c : GAf L n ⧸ U, _) = _
    rw [finsum_eq_of_support_subset_range he]
    · refine finsum_congr fun d => ?_
      rw [dite_eq_left (heT d)]
      have hv : Dv.hval H (Dv.loc (heT d).choose) = H d.out := by
        rw [InertDatum.hval, dite_eq_left (hA _)]
        exact eq_of_coset hH (by rw [QuotientGroup.out_eq']; exact hρ2 d)
      rw [hv]
    · intro c hc
      rw [Function.mem_support] at hc
      by_cases hT : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x
      · obtain ⟨x, hxc, hx⟩ := hT
        refine ⟨(lam x : GU Dv.σw n ⧸ K), ?_⟩
        show ((s _ : GAf L n) : GAf L n ⧸ U) = c
        rw [← hxc]
        refine (hR _ _ (hs1 _) hx).2 ?_
        rw [hs2, QuotientGroup.out_eq']
      · rw [dite_eq_right hT] at hc
        exact absurd rfl hc

  have hRi : ∀ (H : GU Dv.σw n → ℂ), H ∈ Hecke ℂ K → ∀ (a : GU Dv.σw n) (c : K), H (a * c) = H a :=
    fun H hH a c => by simpa using hH.1 1 c a
  have hLi : ∀ (H : GU Dv.σw n → ℂ), H ∈ Hecke ℂ K → ∀ (c : K) (a : GU Dv.σw n), H (c * a) = H a :=
    fun H hH c a => by simpa using hH.1 c 1 a
  have hconvR : ∀ (a : GU Dv.σw n) (c : K), conv K h h' (a * c) = conv K h h' a := by
    intro a c
    simp only [Formalism.UG.conv]
    refine finsum_congr fun x => ?_
    rw [← mul_assoc, hRi h' hh']
  have hfin : ∀ H ∈ Hecke ℂ K, Set.Finite {d : GU Dv.σw n ⧸ K | H d.out ≠ 0} := by
    rintro H ⟨-, S, hS⟩
    refine (S.finite_toSet.biUnion fun t _ => GlobalTheory.SatInd.DCoset.finite_dcoset Dv.ϖ Dv.σw _ n Dv.unram t).subset ?_
    intro d hd
    obtain ⟨t, ht, a, b, hab⟩ := hS _ hd
    refine Set.mem_biUnion ht ⟨(a : GU Dv.σw n), a.2, ?_⟩
    conv_rhs => rw [← QuotientGroup.out_eq' d]
    rw [hab]
    exact (QuotientGroup.mk_mul_of_mem _ b.2).symm
  have hfU : ∀ a b : GAf L n, (a : GAf L n ⧸ U) = b → ∀ g, f (g * a) = f (g * b) := by
    intro a b hab g
    have hu := QuotientGroup.eq.1 hab
    have : f (g * a * (a⁻¹ * b)) = f (g * a) := congrFun (hf _ hu) (g * a)
    rw [← this, mul_assoc, mul_inv_cancel_left]
  funext g
  rw [step2 _ hconvR f g, step2 h (hRi h hh) _ g]
  have inner : ∀ d : GU Dv.σw n ⧸ K,
      heckeFunI L n U Dv h' f (g * (heT d).choose) =
        ∑ᶠ e : GU Dv.σw n ⧸ K, h' (d.out⁻¹ * e.out) • f (g * (heT e).choose) := by
    intro d
    rw [step2 h' (hRi h' hh') f]
    set x := lam (heT d).choose with hx
    have hk : x⁻¹ * d.out ∈ K := QuotientGroup.eq.1 (by rw [QuotientGroup.out_eq']; exact hρ2 d)
    have hL : ∀ y, h' (d.out⁻¹ * y) = h' (x⁻¹ * y) := by
      intro y
      have := hLi h' hh' ⟨(x⁻¹ * d.out)⁻¹, inv_mem hk⟩ (x⁻¹ * y)
      rw [← this]
      congr 1
      show _ = (x⁻¹ * d.out)⁻¹ * (x⁻¹ * y)
      group
    refine Eq.trans ?_ (finsum_comp_equiv (MulAction.toPerm x : Equiv.Perm (GU Dv.σw n ⧸ K)))
    refine finsum_congr fun e => ?_
    simp only [MulAction.toPerm_apply]
    congr 1
    · rw [hL]
      refine eq_of_coset (hRi h' hh') ?_
      rw [QuotientGroup.out_eq', ← smul_eq_mul, ← MulAction.Quotient.smul_mk, QuotientGroup.out_eq',
        inv_smul_smul]
    · rw [mul_assoc]
      refine hfU _ _ ((hR _ _ (GlobalTheory.SatInd.CosetFin.trivOutside_mul (hρ1 d) (hρ1 e)) (hρ1 _)).2 ?_) g
      rw [map_mul, hρ2, ← hx, ← smul_eq_mul, ← MulAction.Quotient.smul_mk, hρ2]
  rw [finsum_congr fun d => congrArg (h d.out • ·) (inner d)]
  have hSe : Set.Finite (⋃ (d : GU Dv.σw n ⧸ K) (_ : d ∈ {d : GU Dv.σw n ⧸ K | h d.out ≠ 0}),
      (fun c : GU Dv.σw n ⧸ K => (d.out • c : GU Dv.σw n ⧸ K)) '' {c : GU Dv.σw n ⧸ K | h' c.out ≠ 0}) :=
    (hfin h hh).biUnion fun d _ => (hfin h' hh').image _
  have hmem : ∀ d e : GU Dv.σw n ⧸ K, h d.out ≠ 0 → h' (d.out⁻¹ * e.out) ≠ 0 →
      e ∈ hSe.toFinset := by
    intro d e hd he'
    rw [Set.Finite.mem_toFinset]
    refine Set.mem_biUnion hd ⟨d.out⁻¹ • e, ?_, smul_inv_smul d.out e⟩
    have hc : (((d.out⁻¹ • e).out : GU Dv.σw n) : GU Dv.σw n ⧸ K) = ↑(d.out⁻¹ * e.out) := by
      rw [QuotientGroup.out_eq', ← smul_eq_mul, ← MulAction.Quotient.smul_mk, QuotientGroup.out_eq']
    show h' (d.out⁻¹ • e).out ≠ 0
    rw [eq_of_coset (hRi h' hh') hc]
    exact he'
  have hL1 : (∑ᶠ e : GU Dv.σw n ⧸ K, conv K h h' e.out • f (g * (heT e).choose)) =
      ∑ e ∈ hSe.toFinset, (∑ d ∈ (hfin h hh).toFinset, h d.out * h' (d.out⁻¹ * e.out)) •
        f (g * (heT e).choose) := by
    rw [finsum_eq_sum_of_support_subset _ (s := hSe.toFinset) ?_]
    · refine Finset.sum_congr rfl fun e _ => ?_
      congr 1
      show (∑ᶠ d : GU Dv.σw n ⧸ K, h d.out * h' (d.out⁻¹ * e.out)) = _
      apply finsum_eq_sum_of_support_subset
      intro d hd
      rw [Function.mem_support] at hd
      rw [Set.Finite.coe_toFinset]
      exact left_ne_zero_of_mul hd
    · intro e he
      rw [Function.mem_support] at he
      have h1 : conv K h h' e.out ≠ 0 := fun h0 => he (by rw [h0, zero_smul])
      obtain ⟨d, hd⟩ : ∃ d : GU Dv.σw n ⧸ K, h d.out * h' (d.out⁻¹ * e.out) ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        exact h1 (finsum_eq_zero_of_forall_eq_zero hcon)
      exact hmem d e (left_ne_zero_of_mul hd) (right_ne_zero_of_mul hd)
  have hR1 : (∑ᶠ d : GU Dv.σw n ⧸ K, h d.out • ∑ᶠ e : GU Dv.σw n ⧸ K,
      h' (d.out⁻¹ * e.out) • f (g * (heT e).choose)) =
      ∑ d ∈ (hfin h hh).toFinset, ∑ e ∈ hSe.toFinset, (h d.out * h' (d.out⁻¹ * e.out)) •
        f (g * (heT e).choose) := by
    rw [finsum_eq_sum_of_support_subset _ (s := (hfin h hh).toFinset) ?_]
    · refine Finset.sum_congr rfl fun d hd => ?_
      rw [Set.Finite.mem_toFinset] at hd
      rw [finsum_eq_sum_of_support_subset _ (s := hSe.toFinset) ?_, Finset.smul_sum]
      · exact Finset.sum_congr rfl fun e _ => by rw [mul_smul]
      · intro e he
        rw [Function.mem_support] at he
        exact hmem d e hd (fun h0 => he (by rw [h0, zero_smul]))
    · intro d hd
      rw [Function.mem_support] at hd
      rw [Set.Finite.coe_toFinset]
      exact fun h0 => hd (by rw [h0, zero_smul])
  rw [hL1, hR1, Finset.sum_comm]
  exact Finset.sum_congr rfl fun e _ => by rw [Finset.sum_smul]

theorem heckeFunI_conv_mul : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (U : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (h₁ h₂ : Formalism.UG.GU Dv.σw n → ℂ), h₁ ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n) → h₂ ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n) → ∀ f : GAf L n → W, (∀ κ ∈ U, NG.rt L n κ f = f) → heckeFunI L n U Dv (Formalism.UG.conv (Formalism.UG.KU Dv.σw n) h₁ h₂) f = heckeFunI L n U Dv h₁ (heckeFunI L n U Dv h₂ f) := by
  intro L _ _ _ n v w Dv U hU W _ _ h₁ h₂ hh₁ hh₂ f hf
  exact conv_of Dv U hU (GlobalTheory.T.inertLocal_mem_unitaryGroup_antidiagonalForm L n v w Dv)
    (fun u hu => GlobalTheory.T.inertLocal_mem_integralPoints_of_latticeStabilizer L n v w Dv u hu _) (GlobalTheory.T.inertLocal_surjective_from_trivOutside L n v w Dv) W h₁ hh₁ h₂ hh₂ f hf

end GlobalTheory.InertConvMul
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertHeckeOperatorConvolutionEqCompStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertHeckeOperator_convolution_eq_comp : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (U : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (h₁ h₂ : Formalism.UG.GU Dv.σw n → ℂ), h₁ ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n) → h₂ ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n) → ∀ f : GAf L n → W, (∀ κ ∈ U, NG.rt L n κ f = f) → heckeFunI L n U Dv (Formalism.UG.conv (Formalism.UG.KU Dv.σw n) h₁ h₂) f = heckeFunI L n U Dv h₁ (heckeFunI L n U Dv h₂ f) := by
  first | exact @GlobalTheory.InertConvMul.heckeFunI_conv_mul | exact GlobalTheory.InertConvMul.heckeFunI_conv_mul | (intros; apply GlobalTheory.InertConvMul.heckeFunI_conv_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLevelFullAtInertPlacePrincipalElsewhere
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLevelFullAtInertPlacePrincipalElsewhere
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open TensorProduct

namespace GlobalTheory.InertLevel

section MixMat
variable {R : Type*} [CommRing R] {n : ℕ}

theorem mix_mul (p : R) (hp : p * p = p) (A B C D : Matrix (Fin n) (Fin n) R) :
    (p • A + (1 - p) • B) * (p • C + (1 - p) • D) = p • (A * C) + (1 - p) • (B * D) := by
  have h1 : p * (1 - p) = 0 := by rw [mul_sub, mul_one, hp, sub_self]
  have h2 : (1 - p) * p = 0 := by rw [mul_comm, h1]
  have h3 : (1 - p) * (1 - p) = 1 - p := by rw [sub_mul, one_mul, h1, sub_zero]
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hp, h1, h2, h3,
    zero_smul, add_zero, zero_add]

theorem mix_one (p : R) : p • (1 : Matrix (Fin n) (Fin n) R) + (1 - p) • 1 = 1 := by
  rw [← add_smul, add_sub_cancel, one_smul]

theorem conjT_mix (σ : R →+* R) (p : R) (hp : σ p = p) (A B : Matrix (Fin n) (Fin n) R) :
    conjT σ (p • A + (1 - p) • B) = p • conjT σ A + (1 - p) • conjT σ B := by
  ext i j
  simp [conjT, map_sub, hp]

end MixMat

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem mem_GA_iff (x : GL (Fin n) (AL L)) :
    x ∈ ReciprocityTheory.Aut.GA L n ↔ (x : Matrix (Fin n) (Fin n) (AL L)) * conjT (conjAL L) x = 1 := Iff.rfl

def mixG (p : AL L) (hp : p * p = p) (hc : conjAL L p = p) (g h : GAf L n) : GAf L n :=
  ⟨⟨p • (g.1 : Matrix (Fin n) (Fin n) (AL L)) + (1 - p) • (h.1 : Matrix (Fin n) (Fin n) (AL L)),
    p • ((g.1⁻¹ : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) +
      (1 - p) • ((h.1⁻¹ : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)),
    by rw [mix_mul p hp, Units.mul_inv, Units.mul_inv, mix_one],
    by rw [mix_mul p hp, Units.inv_mul, Units.inv_mul, mix_one]⟩, by
    rw [mem_GA_iff]
    show (p • (g.1 : Matrix (Fin n) (Fin n) (AL L)) + (1 - p) • (h.1 : Matrix (Fin n) (Fin n) (AL L))) *
      conjT (conjAL L) (p • (g.1 : Matrix (Fin n) (Fin n) (AL L)) + (1 - p) • (h.1 : Matrix (Fin n) (Fin n) (AL L))) = 1
    rw [conjT_mix _ p hc, mix_mul p hp, (mem_GA_iff _).1 g.2, (mem_GA_iff _).1 h.2, mix_one]⟩

theorem mixG_val (p : AL L) (hp : p * p = p) (hc : conjAL L p = p) (g h : GAf L n) :
    ((mixG p hp hc g h).1 : Matrix (Fin n) (Fin n) (AL L)) =
      p • (g.1 : Matrix (Fin n) (Fin n) (AL L)) + (1 - p) • (h.1 : Matrix (Fin n) (Fin n) (AL L)) := rfl

end GlobalTheory.InertLevel

namespace GlobalTheory.InertLevel

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}


open GlobalTheory.InertUmax in
def idemAt (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : AL L :=
  (1 : L) ⊗ₜ[maximalRealSubfield L] sgl L v 1

section Idem
variable (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))

theorem compAt_idemAt_self : compAt L v (idemAt v) = 1 := by
  rw [idemAt, GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.sgl_same, ← Algebra.TensorProduct.one_def]

theorem compAt_idemAt_ne {w} (hw : w ≠ v) : compAt L w (idemAt v) = 0 := by
  rw [idemAt, GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.sgl_ne L v 1 hw, tmul_zero]

theorem idemAt_mul_self : idemAt (L := L) v * idemAt v = idemAt v := by
  rw [← sub_eq_zero]
  apply GlobalTheory.InertUmax.eq_zero_of_compAt
  intro w
  rw [map_sub, map_mul]
  rcases eq_or_ne w v with rfl | hw
  · rw [compAt_idemAt_self]; simp
  · rw [compAt_idemAt_ne v hw]; simp

theorem conjAL_idemAt : conjAL L (idemAt v) = idemAt v := by
  simp [idemAt, conjAL, Algebra.TensorProduct.map_tmul]

theorem idemAt_mem : idemAt (L := L) v ∈ ALint L :=
  GlobalTheory.InertUmax.one_tmul_sgl_mem L v 1 (one_mem _)

theorem one_sub_idemAt_mem : 1 - idemAt (L := L) v ∈ ALint L :=
  Subring.sub_mem _ (one_mem _) (idemAt_mem v)

theorem one_entry_mem (S : Subring (AL L)) (i j : Fin n) :
    (1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ S := by
  rw [Matrix.one_apply]; split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem compAt_one_entry (w : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (i j : Fin n) :
    compAt L w ((1 : Matrix (Fin n) (Fin n) (AL L)) i j) = (1 : Matrix (Fin n) (Fin n) _) i j := by
  simp only [Matrix.one_apply]
  split_ifs <;> simp

theorem away_eq_zero {x : GAf L n} (hx : TrivOutside {v} x) (i j : Fin n) :
    (1 - idemAt v) * ((x.1 : Matrix (Fin n) (Fin n) (AL L)) i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j) = 0 := by
  apply GlobalTheory.InertUmax.eq_zero_of_compAt
  intro w
  rw [map_mul, map_sub, map_sub, map_one, compAt_one_entry]
  rcases eq_or_ne w v with rfl | hw
  · rw [compAt_idemAt_self]; simp
  · have h := congrFun (congrFun (hx w (by simpa using hw)) i) j
    rw [Matrix.map_apply] at h
    rw [h, sub_self, mul_zero]

end Idem

def DivBy (N : ℕ) (M : Matrix (Fin n) (Fin n) (AL L)) : Prop :=
  ∀ i j, ∃ y ∈ ALint L, M i j = (N : AL L) * y

theorem DivBy.add {N : ℕ} {A B : Matrix (Fin n) (Fin n) (AL L)} (hA : DivBy N A) (hB : DivBy N B) :
    DivBy N (A + B) := fun i j => by
  obtain ⟨y, hy, e⟩ := hA i j
  obtain ⟨z, hz, f⟩ := hB i j
  exact ⟨y + z, Subring.add_mem _ hy hz, by rw [Matrix.add_apply, e, f, mul_add]⟩

theorem DivBy.neg {N : ℕ} {A : Matrix (Fin n) (Fin n) (AL L)} (hA : DivBy N A) : DivBy N (-A) := fun i j => by
  obtain ⟨y, hy, e⟩ := hA i j
  exact ⟨-y, Subring.neg_mem _ hy, by rw [Matrix.neg_apply, e, mul_neg]⟩

theorem DivBy.mul_int {N : ℕ} {A B : Matrix (Fin n) (Fin n) (AL L)} (hA : DivBy N A)
    (hB : ∀ i j, B i j ∈ ALint L) : DivBy N (A * B) := fun i j => by
  choose y hy e using hA
  exact ⟨∑ k, y i k * B k j, Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hy i k) (hB k j), by
    simp only [Matrix.mul_apply, e, Finset.mul_sum, mul_assoc]⟩

theorem DivBy.int_mul {N : ℕ} {A B : Matrix (Fin n) (Fin n) (AL L)} (hA : DivBy N A)
    (hB : ∀ i j, B i j ∈ ALint L) : DivBy N (B * A) := fun i j => by
  choose y hy e using hA
  exact ⟨∑ k, B i k * y k j, Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hB i k) (hy k j), by
    simp only [Matrix.mul_apply, e, Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => by ring⟩

def levelAt (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (N : ℕ) : Subgroup (GAf L n) where
  carrier := {κ | κ ∈ Umax L n ∧
    DivBy N ((1 - idemAt v) • ((κ.1 : Matrix (Fin n) (Fin n) (AL L)) - 1))}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨(Umax L n).mul_mem ha hb, ?_⟩
    have e : ((a * b).1 : Matrix (Fin n) (Fin n) (AL L)) - 1 =
        ((a.1 : Matrix (Fin n) (Fin n) (AL L)) - 1) * (b.1 : Matrix (Fin n) (Fin n) (AL L)) +
          ((b.1 : Matrix (Fin n) (Fin n) (AL L)) - 1) := by
      simp only [Subgroup.coe_mul, Units.val_mul, sub_mul, one_mul]; abel
    rw [e, smul_add, ← Matrix.smul_mul]
    exact (ha'.mul_int hb).add hb'
  one_mem' := ⟨(Umax L n).one_mem, fun i j => ⟨0, zero_mem _, by simp⟩⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨(Umax L n).inv_mem ha, ?_⟩
    have e : ((a⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) - 1 =
        -(((a⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) * ((a.1 : Matrix (Fin n) (Fin n) (AL L)) - 1)) := by
      rw [mul_sub, mul_one]
      have : ((a⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) * (a.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 := by
        rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
      rw [this]; abel
    rw [e, smul_neg, ← Matrix.mul_smul]
    exact (ha'.int_mul ((Umax L n).inv_mem ha)).neg

end GlobalTheory.InertLevel

namespace GlobalTheory.InertLevel

theorem exists_level : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (N : ℕ), 0 < N → ∃ U : Subgroup (GAf L n), (∀ κ, NG.Cong L n N κ → κ ∈ U) ∧ (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) ∧ ∀ κ ∈ U, ∃ a b : GAf L n, κ = a * b ∧ a ∈ Umax L n ∧ TrivOutside {v} a ∧ NG.Cong L n N b ∧ ∀ x : GAf L n, TrivOutside {v} x → b * x = x * b := by
  intro L _ _ _ n v N _
  have hp := idemAt_mul_self (L := L) v
  have hc := conjAL_idemAt (L := L) v
  refine ⟨levelAt (n := n) v N, ?_, ?_, ?_⟩
  · rintro κ ⟨hU, hκ⟩
    refine ⟨hU, fun i j => ?_⟩
    obtain ⟨y, hy, e⟩ := hκ i j
    refine ⟨(1 - idemAt v) * y, Subring.mul_mem _ (one_sub_idemAt_mem v) hy, ?_⟩
    rw [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, e]; ring
  · intro κ hκ
    refine ⟨fun h => h.1, fun h => ⟨h, fun i j => ⟨0, zero_mem _, ?_⟩⟩⟩
    rw [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, away_eq_zero v hκ, mul_zero]
  · rintro κ ⟨hU, hκ⟩
    refine ⟨mixG (idemAt v) hp hc κ 1, mixG (idemAt v) hp hc 1 κ, ?_, ?_, ?_, ⟨?_, ?_⟩, ?_⟩
    · apply Subtype.ext; apply Units.ext
      simp only [Subgroup.coe_mul, Units.val_mul, mixG_val, mix_mul _ hp, OneMemClass.coe_one, Units.val_one,
        mul_one, one_mul]
      rw [← add_smul, add_sub_cancel, one_smul]
    · intro i j
      rw [mixG_val, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
      exact Subring.add_mem _ (Subring.mul_mem _ (idemAt_mem v) (hU i j))
        (Subring.mul_mem _ (one_sub_idemAt_mem v) (by simpa using one_entry_mem (ALint L) i j))
    · intro w hw
      have hw' : w ≠ v := by simpa using hw
      ext i j
      rw [Matrix.map_apply, mixG_val, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul,
        smul_eq_mul, map_add, map_mul, map_mul, map_sub, map_one, compAt_idemAt_ne v hw']
      simp only [OneMemClass.coe_one, Units.val_one, compAt_one_entry, zero_mul, zero_add, sub_zero, one_mul]
    · intro i j
      rw [mixG_val, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
      exact Subring.add_mem _ (Subring.mul_mem _ (idemAt_mem v) (by simpa using one_entry_mem (ALint L) i j))
        (Subring.mul_mem _ (one_sub_idemAt_mem v) (hU i j))
    · intro i j
      obtain ⟨y, hy, e⟩ := hκ i j
      refine ⟨y, hy, ?_⟩
      rw [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul] at e
      rw [← e, mixG_val, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
      simp only [OneMemClass.coe_one, Units.val_one]
      ring
    · intro x hx
      have hX : (x.1 : Matrix (Fin n) (Fin n) (AL L)) =
          idemAt v • (x.1 : Matrix (Fin n) (Fin n) (AL L)) + (1 - idemAt v) • 1 := by
        ext i j
        have h := away_eq_zero v hx i j
        rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
        linear_combination h
      apply Subtype.ext; apply Units.ext
      simp only [Subgroup.coe_mul, Units.val_mul, mixG_val, OneMemClass.coe_one, Units.val_one]
      rw [hX, mix_mul _ hp, mix_mul _ hp]
      simp only [mul_one, one_mul]

end GlobalTheory.InertLevel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLevelFullAtInertPlacePrincipalElsewhereStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_level_full_at_inert_place_principal_elsewhere : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (N : ℕ), 0 < N → ∃ U : Subgroup (GAf L n), (∀ κ, NG.Cong L n N κ → κ ∈ U) ∧ (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) ∧ ∀ κ ∈ U, ∃ a b : GAf L n, κ = a * b ∧ a ∈ Umax L n ∧ TrivOutside {v} a ∧ NG.Cong L n N b ∧ ∀ x : GAf L n, TrivOutside {v} x → b * x = x * b := by
  first | exact @GlobalTheory.InertLevel.exists_level | exact GlobalTheory.InertLevel.exists_level | (intros; apply GlobalTheory.InertLevel.exists_level <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSatUEigenvector
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSatUEigenvector
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.HeckeSatakeEigen

theorem exists_satU_eigenvector : ∀ {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] [CompleteSpace K] (ϖ : K) (σ : K →+* K) (q n : ℕ), Formalism.UG.IsUnramInv ϖ σ q → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (T : (Formalism.UG.GU σ n → ℂ) → Module.End ℂ V), (∀ h₁ ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), ∀ h₂ ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), T (h₁ + h₂) = T h₁ + T h₂) → (∀ (c : ℂ), ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), T (c • h) = c • T h) → T (Formalism.UG.dosetInd ℂ (Formalism.UG.KU σ n) 1) = 1 → (∀ h₁ ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), ∀ h₂ ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), T (Formalism.UG.conv (Formalism.UG.KU σ n) h₁ h₂) = T h₁ * T h₂) → ∀ x₀ : V, x₀ ≠ 0 → ∃ α : Fin (n / 2) → ℂ, ∃ x : V, x ≠ 0 ∧ ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), T h x = Formalism.UG.SatU ϖ q h α • x := by
  intro K _ _ _ ϖ σ q n hU V _ _ _ T hadd hsmul h1 hmul x₀ hx₀
  haveI : Nontrivial V := ⟨⟨x₀, 0, hx₀⟩⟩
  have hcomm : ∀ a b : Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), T a.1 * T b.1 = T b.1 * T a.1 := by
    intro a b
    rw [← hmul _ a.2 _ b.2, ← hmul _ b.2 _ a.2, GlobalTheory.UnitarySwap.heckeCommU K ϖ σ q n ℂ hU _ a.2 _ b.2]
  obtain ⟨x, hx0, hx⟩ := GlobalTheory.exists_common_eigenvector_of_commute
    (fun b : Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n) => T b.1) hcomm
  choose c hc using hx
  have hinj : Function.Injective fun a : ℂ => a • x := smul_left_injective ℂ hx0
  let l : Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n) →ₗ[ℂ] ℂ :=
    { toFun := c
      map_add' := fun a b => hinj (by
        show c (a + b) • x = (c a + c b) • x
        rw [← hc, add_smul, ← hc, ← hc]
        show T (a.1 + b.1) x = _
        rw [hadd _ a.2 _ b.2]; rfl)
      map_smul' := fun r a => hinj (by
        show c (r • a) • x = (r * c a) • x
        rw [← hc, mul_smul, ← hc]
        show T (r • a.1) x = _
        rw [hsmul r _ a.2]; rfl) }
  have hl1 : l ⟨_, Formalism.UG.Final.DosetIndMem _ _ ℂ 1⟩ = 1 := hinj (by
    show c _ • x = (1 : ℂ) • x
    rw [← hc, one_smul]
    show T (Formalism.UG.dosetInd ℂ _ 1) x = x
    rw [h1]; rfl)
  have hlm : ∀ f f' : Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n),
      l ⟨_, Formalism.UG.Final.HeckeConvMem _ _ ℂ (Formalism.UG.P.isCommensurated_integral_unitary_of_unramified hU n) _ f.2 _ f'.2⟩ = l f * l f' :=
    fun f f' => hinj (by
      show c _ • x = (c f * c f') • x
      rw [← hc]
      show T (Formalism.UG.conv _ f.1 f'.1) x = _
      rw [hmul _ f.2 _ f'.2, Module.End.mul_apply, hc f', map_smul, hc f, smul_smul, mul_comm])
  obtain ⟨α, hα⟩ := GlobalTheory.LFun.SatCompare.exists_satU_eq hU l hl1 hlm
  refine ⟨fun i => (α i : ℂ), x, hx0, fun h hh => ?_⟩
  rw [hc ⟨h, hh⟩]
  congr 1
  exact hα ⟨h, hh⟩

end GlobalTheory.HeckeSatakeEigen
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSatUEigenvectorStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_satU_eigenvector_alt : ∀ {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] [CompleteSpace K] (ϖ : K) (σ : K →+* K) (q n : ℕ), Formalism.UG.IsUnramInv ϖ σ q → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (T : (Formalism.UG.GU σ n → ℂ) → Module.End ℂ V), (∀ h₁ ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), ∀ h₂ ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), T (h₁ + h₂) = T h₁ + T h₂) → (∀ (c : ℂ), ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), T (c • h) = c • T h) → T (Formalism.UG.dosetInd ℂ (Formalism.UG.KU σ n) 1) = 1 → (∀ h₁ ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), ∀ h₂ ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), T (Formalism.UG.conv (Formalism.UG.KU σ n) h₁ h₂) = T h₁ * T h₂) → ∀ x₀ : V, x₀ ≠ 0 → ∃ α : Fin (n / 2) → ℂ, ∃ x : V, x ≠ 0 ∧ ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), T h x = Formalism.UG.SatU ϖ q h α • x := by
  first | exact @GlobalTheory.HeckeSatakeEigen.exists_satU_eigenvector | exact GlobalTheory.HeckeSatakeEigen.exists_satU_eigenvector | (intros; apply GlobalTheory.HeckeSatakeEigen.exists_satU_eigenvector <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSatakeParameterInertDatumOfDictionarySpher
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.SatExist

theorem exists_satAt : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (π : NG.AutRep L n) (U : Submodule ℂ (UA L n → ℂ)), Dict F π U → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → π.SphAt v → ∀ Dv : InertDatum L n v w, ∃ α, NG.SatAt π Dv α := by
  classical
  intro L _ _ _ n F π U₀ _ v w _ hsph Dv
  obtain ⟨f₀, hf₀S, hf₀0, hf₀K⟩ := hsph
  obtain ⟨-, N, hN, hf₀N⟩ := π.irrS.1.le hf₀S
  obtain ⟨U, hCU, hU, hdec⟩ := GlobalTheory.T.exists_level_full_at_inert_place_principal_elsewhere L n v N hN
  have hdec' : ∀ κ ∈ U, ∃ a b : GAf L n, κ = a * b ∧ a ∈ Umax L n ∧ TrivOutside {v} a ∧ b ∈ U ∧
      ∀ x : GAf L n, TrivOutside {v} x → b * x = x * b := fun κ hκ => by
    obtain ⟨a, b, e, ha, hta, hb, hc⟩ := hdec κ hκ
    exact ⟨a, b, e, ha, hta, hCU b hb, hc⟩
  have hf₀U : ∀ κ ∈ U, NG.rt L n κ f₀ = f₀ := fun κ hκ => by
    obtain ⟨a, b, rfl, ha, hta, hb, -⟩ := hdec κ hκ
    funext g
    show f₀ (g * (a * b)) = f₀ g
    rw [← mul_assoc, hf₀N b hb]
    exact congrFun (hf₀K a ha hta) g
  let V : Submodule ℂ (GAf L n → π.W) :=
    { carrier := {f | f ∈ π.S ∧ ∀ κ ∈ U, NG.rt L n κ f = f}
      add_mem' := fun {f f'} hf hf' => ⟨π.S.add_mem hf.1 hf'.1, fun κ hκ => by
        rw [map_add (f := _), hf.2 κ hκ, hf'.2 κ hκ]⟩
      zero_mem' := ⟨π.S.zero_mem, fun κ _ => map_zero _⟩
      smul_mem' := fun c f hf => ⟨π.S.smul_mem c hf.1, fun κ hκ => by rw [map_smul, hf.2 κ hκ]⟩ }
  haveI : FiniteDimensional ℂ π.W := π.alg.1
  haveI := GlobalTheory.AlgFormsFin.fixedForms_finite L n π.ρ (GlobalTheory.T.finite_doubleCosets_definiteUnitary_maximalLevel L n) hN
  haveI hVfin : FiniteDimensional ℂ V :=
    Submodule.finiteDimensional_of_le (S₂ := GlobalTheory.AlgFormsFin.fixedForms L n π.ρ N) fun f hf =>
      ⟨(π.irrS.1.le hf.1).1, fun κ hκ g => congrFun (hf.2 κ (hCU κ hκ)) g⟩
  have hfin := fun h hh => GlobalTheory.SatInd.CosetFin.finite_inert_support L n v w Dv
    (GlobalTheory.SatInd.DCoset.finite_dcoset Dv.ϖ Dv.σw _ n Dv.unram)
    (GlobalTheory.InertUmax.mem_Umax_of_trivOutside_of_loc_integral L n v w Dv) U hU h hh
  have hsum : ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n),
      ∃ (C : Finset (GAf L n ⧸ U)) (a : GAf L n ⧸ U → ℂ) (x : GAf L n ⧸ U → GAf L n),
        ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (φ : GAf L n → W),
          heckeFunI L n U Dv h φ = ∑ c ∈ C, a c • NG.rt L n (x c) φ := by
    intro h hh
    let hf := hfin h hh
    refine ⟨hf.toFinset,
      fun c => if hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x then
        Dv.hval h (Dv.loc hc.choose) else 0,
      fun c => if hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x then
        hc.choose else 1, fun W _ _ φ => ?_⟩
    funext g
    unfold heckeFunI
    rw [finsum_eq_sum_of_support_subset (s := hf.toFinset)]
    · rw [Finset.sum_apply]
      refine Finset.sum_congr rfl fun c _ => ?_
      by_cases hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x
      · simp only [dif_pos hc]
        rfl
      · simp only [dif_neg hc, zero_smul]
        rfl
    · intro c hc0
      rw [Function.mem_support] at hc0
      by_cases hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x
      · rw [dif_pos hc] at hc0
        rw [Set.Finite.coe_toFinset]
        refine ⟨hc.choose, hc.choose_spec.1, hc.choose_spec.2, fun h0 => hc0 ?_⟩
        rw [h0, zero_smul]
      · exact absurd (dif_neg hc) hc0
  have hmemV : ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n), ∀ f ∈ V, heckeFunI L n U Dv h f ∈ V := by
    intro h hh f hf
    refine ⟨?_, GlobalTheory.T.inertHeckeOperator_preserves_productLevel_invariance L n v w Dv U hU hdec' π.W h hh f hf.2⟩
    obtain ⟨C, a, x, hC⟩ := hsum h hh
    rw [hC]
    exact π.S.sum_mem fun c _ => π.S.smul_mem _ (π.irrS.1.stable _ _ hf.1)
  let T : (Formalism.UG.GU Dv.σw n → ℂ) → Module.End ℂ V := fun h =>
    if hh : h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n) then
      { toFun := fun f => ⟨heckeFunI L n U Dv h f, hmemV h hh f f.2⟩
        map_add' := fun f f' => Subtype.ext (by
          obtain ⟨C, a, x, hC⟩ := hsum h hh
          simp only [Submodule.coe_add, hC, map_add (f := _), smul_add, Finset.sum_add_distrib])
        map_smul' := fun c f => Subtype.ext (by
          obtain ⟨C, a, x, hC⟩ := hsum h hh
          simp only [Submodule.coe_smul, hC, map_smul, RingHom.id_apply, Finset.smul_sum]
          exact Finset.sum_congr rfl fun c' _ => smul_comm _ _ _) }
    else 0
  have hT : ∀ h (hh : h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n)) (f : V),
      ((T h f : V) : GAf L n → π.W) = heckeFunI L n U Dv h f := fun h hh f => by
    simp only [T, dif_pos hh]
    rfl
  have hK := Formalism.UG.P.isCommensurated_integral_unitary_of_unramified Dv.unram n
  obtain ⟨α, x, hx0, hx⟩ := GlobalTheory.T.exists_satU_eigenvector_alt Dv.ϖ Dv.σw _ n Dv.unram V T
    (fun h₁ hh₁ h₂ hh₂ => LinearMap.ext fun f => Subtype.ext (by
      rw [LinearMap.add_apply, Submodule.coe_add, hT (h₁ + h₂) (add_mem hh₁ hh₂) f, hT h₁ hh₁ f, hT h₂ hh₂ f]
      exact (GlobalTheory.T.heckeFunI_add_and_smul L n v w Dv U hU π.W h₁ h₂ hh₁ hh₂ 0 f).1))
    (fun c h hh => LinearMap.ext fun f => Subtype.ext (by
      rw [LinearMap.smul_apply, Submodule.coe_smul, hT (c • h) (Submodule.smul_mem _ c hh) f, hT h hh f]
      exact (GlobalTheory.T.heckeFunI_add_and_smul L n v w Dv U hU π.W h h hh hh c f).2))
    (LinearMap.ext fun f => Subtype.ext (by
      rw [hT _ (Formalism.UG.Final.DosetIndMem _ _ ℂ 1) f]
      exact GlobalTheory.T.inertHeckeOperator_maximalCompact_indicator_eq_id L n v w Dv U hU π.W f f.2.2))
    (fun h₁ hh₁ h₂ hh₂ => LinearMap.ext fun f => Subtype.ext (by
      rw [Module.End.mul_apply, hT _ (Formalism.UG.Final.HeckeConvMem _ _ ℂ hK _ hh₁ _ hh₂) f, hT h₁ hh₁ (T h₂ f), hT h₂ hh₂ f]
      exact GlobalTheory.T.inertHeckeOperator_convolution_eq_comp L n v w Dv U hU π.W h₁ h₂ hh₁ hh₂ f f.2.2))
    ⟨f₀, hf₀S, hf₀U⟩ (fun h => hf₀0 (congrArg Subtype.val h))
  refine ⟨α, x, x.2.1, fun h => hx0 (Subtype.ext h), U, x.2.2, hU, fun h hh => ?_⟩
  have e := congrArg Subtype.val (hx h hh)
  rw [hT h hh] at e
  exact e

end GlobalTheory.SatExist
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSatakeParameterInertDatumOfDictionarySpherStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_satakeParameter_inertDatum_of_dictionary_spherical : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (π : NG.AutRep L n) (U : Submodule ℂ (UA L n → ℂ)), Dict F π U → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → π.SphAt v → ∀ Dv : InertDatum L n v w, ∃ α, NG.SatAt π Dv α := by
  first | exact @GlobalTheory.SatExist.exists_satAt | exact GlobalTheory.SatExist.exists_satAt | (intros; apply GlobalTheory.SatExist.exists_satAt <;> assumption)
end
