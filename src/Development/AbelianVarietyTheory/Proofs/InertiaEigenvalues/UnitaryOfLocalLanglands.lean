module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDictionaryCmFieldAutomorphic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertSatakeParametersAgreeUnderDictionary
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSatakeParameterInertDatumOfDictionarySpher
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClass

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalComponentsAgreeSplitPlaceDictionary
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalComponentsAgreeSplitPlaceDictionary
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.SplitDict
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
local notation3 "L⁺" => NumberField.maximalRealSubfield L

theorem under_w (s : SplitPlace L) : s.w.under (𝓞 L⁺) = s.v := by
  ext1
  exact s.w_under

theorem exists_basis : ∃ b : Module.Basis (Fin 2) L⁺ L, b 0 = 1 := by
  obtain ⟨e, hne⟩ : ∃ e : L, e ≠ IsCMField.complexConj L e := by
    by_contra hcon
    push Not at hcon
    exact IsCMField.complexConj_ne_one L (AlgEquiv.ext fun x => (hcon x).symm)
  have hli : LinearIndependent L⁺ ![(1 : L), e] := by
    rw [LinearIndependent.pair_iff]
    intro a t h
    have h' := congrArg (IsCMField.complexConj L) h
    simp only [Algebra.smul_def, map_add (f := _), map_mul, AlgEquiv.commutes, map_one, map_zero] at h h'
    have hd : algebraMap L⁺ L t * (e - IsCMField.complexConj L e) = 0 := by
      linear_combination h - h'
    have ht : t = 0 := by
      rcases mul_eq_zero.1 hd with h0 | h0
      · simpa using h0
      · exact absurd (sub_eq_zero.1 h0) hne
    subst ht
    simpa using h
  have hcard : Fintype.card (Fin 2) = Module.finrank L⁺ L := by
    rw [Algebra.IsQuadraticExtension.finrank_eq_two L⁺ L]; simp
  exact ⟨basisOfLinearIndependentOfCardEqFinrank hli hcard, by simp⟩

theorem kappa_eq_zero (F : FinIso L n) (u : HeightOneSpectrum (𝓞 L)) (z : AL L)
    (hz : compAt L (u.under (𝓞 L⁺)) z = 0) : F.κ z u = 0 := by
  obtain ⟨i', -, hi'⟩ := F.right u (u.under (𝓞 L⁺)) rfl
  obtain ⟨b, hb0⟩ := exists_basis (L := L)
  obtain ⟨A, B, hAB⟩ := GlobalTheory.tensor_exists_decomp b z
  rw [hb0] at hAB
  have hAB0 : A (u.under (𝓞 L⁺)) = 0 ∧ B (u.under (𝓞 L⁺)) = 0 := by
    rw [hAB] at hz
    apply GlobalTheory.tensor_decomp_eq_zero b
    rw [hb0]
    simp [ReciprocityTheory.Aut.compAt, Algebra.TensorProduct.map_tmul] at hz
    exact hz
  have h2 : b 1 ⊗ₜ[L⁺] B = (b 1 ⊗ₜ[L⁺] (1 : AFplus L)) * ((1 : L) ⊗ₜ[L⁺] B) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [hAB, h2, map_add (f := _), map_mul]
  change F.κ (1 ⊗ₜ A) u + F.κ (b 1 ⊗ₜ 1) u * F.κ (1 ⊗ₜ B) u = 0
  rw [hi', hi', hAB0.1, hAB0.2, map_zero, mul_zero, add_zero]

theorem j_mem_locU (F : FinIso L n) (s : SplitPlace L) (y : GAf L n) (hy : TrivOutside {s.v} y) :
    F.j y ∈ locU n s.w := by
  refine Subgroup.mem_inf.2 ⟨F.fin y, ?_⟩
  rw [Subgroup.mem_iInf]
  intro u
  rw [Subgroup.mem_iInf]
  intro hu
  rw [MonoidHom.mem_ker]
  rw [under_w] at hu
  refine Units.ext (Matrix.ext fun a c => ?_)
  rw [F.loc]
  have h1 := congrFun (congrFun (hy (u.under (𝓞 L⁺)) hu) a) c
  simp only [Matrix.map_apply] at h1
  have h2 : compAt L (u.under (𝓞 L⁺)) (((y : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) a c -
      (1 : Matrix (Fin n) (Fin n) (AL L)) a c) = 0 := by
    rw [map_sub, h1]
    simp only [Matrix.one_apply]
    split_ifs <;> simp
  have h3 := kappa_eq_zero F u _ h2
  rw [map_sub] at h3
  change F.κ _ u - F.κ _ u = 0 at h3
  rw [sub_eq_zero] at h3
  rw [h3]
  simp only [Units.val_one, Matrix.one_apply]
  split_ifs <;> simp <;> rfl
end GlobalTheory.SplitDict

namespace GlobalTheory.SplitDict
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
local notation3 "L⁺" => NumberField.maximalRealSubfield L

theorem kappa_split (F : FinIso L n) (s : SplitPlace L) (i : s.v.adicCompletion L⁺ ≃+* s.w.adicCompletion L)
    (hic : Continuous i) (hi : ∀ x : L, i (s.i x) = algebraMap L (s.w.adicCompletion L) x) (z : AL L) :
    F.κ z s.w = i (s.proj z) := by
  obtain ⟨i', hic', hi'⟩ := F.right s.w s.v s.w_under
  have hL : ∀ k : L⁺, i' (algebraMap L⁺ (s.v.adicCompletion L⁺) k) =
      algebraMap L (s.w.adicCompletion L) (algebraMap L⁺ L k) := fun k => by
    have h1 := hi' (algebraMap L⁺ (AFplus L) k)
    have h2 : (1 : L) ⊗ₜ[L⁺] algebraMap L⁺ (AFplus L) k = algebraMap L⁺ L k ⊗ₜ[L⁺] (1 : AFplus L) := by
      rw [← Algebra.TensorProduct.algebraMap_apply', Algebra.TensorProduct.algebraMap_apply]
    rw [h2, F.left] at h1
    exact h1.symm
  have hR : ∀ k : L⁺, i (algebraMap L⁺ (s.v.adicCompletion L⁺) k) =
      algebraMap L (s.w.adicCompletion L) (algebraMap L⁺ L k) := fun k => by
    rw [← hi, AlgHom.commutes]
  have heq : ∀ a : s.v.adicCompletion L⁺, i' a = i a := fun a =>
    (HeightOneSpectrum.denseRange_algebraMap L⁺ s.v).induction_on (p := fun a => i' a = i a) a
      (isClosed_eq hic' hic) fun k => by rw [hL, hR]
  induction z using TensorProduct.induction_on with
  | zero => simp <;> rfl
  | add x y hx hy =>
    rw [map_add (f := _), map_add (f := _), map_add (f := _)]
    change F.κ x s.w + F.κ y s.w = _
    rw [hx, hy]
  | tmul l a =>
    have h2 : l ⊗ₜ[L⁺] a = (l ⊗ₜ[L⁺] (1 : AFplus L)) * ((1 : L) ⊗ₜ[L⁺] a) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [GlobalTheory.SplitLift.proj_tmul, map_mul, hi, h2, map_mul]
    change F.κ (l ⊗ₜ 1) s.w * F.κ (1 ⊗ₜ a) s.w = _
    rw [hi', heq, F.left]
    rfl

theorem cLoc_j (F : FinIso L n) (s : SplitPlace L) (i : s.v.adicCompletion L⁺ ≃+* s.w.adicCompletion L)
    (hic : Continuous i) (hi : ∀ x : L, i (s.i x) = algebraMap L (s.w.adicCompletion L) x) (y : GAf L n) :
    cLoc s.w (F.j y) = Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n y) := by
  refine Units.ext (Matrix.ext fun a c => ?_)
  rw [F.loc, kappa_split F s i hic hi]
  rfl

theorem isSplitAt_w (F : FinIso L n) (s : SplitPlace L) (i : s.v.adicCompletion L⁺ ≃+* s.w.adicCompletion L)
    (hic : Continuous i) (hi : ∀ x : L, i (s.i x) = algebraMap L (s.w.adicCompletion L) x) : IsSplitAt s.w := by
  by_contra hns
  obtain ⟨y, hy⟩ := DFunLike.ne_iff.mp (IsCMField.complexConj_ne_one L)
  set δ : L := y - IsCMField.complexConj L y with hδdef
  have hδ : IsCMField.complexConj L δ = -δ := by
    rw [hδdef, map_sub, IsCMField.complexConj_apply_apply]; ring
  have hδ0 : δ ≠ 0 := sub_ne_zero.2 (Ne.symm hy)
  have hfix : IsCMField.complexConj L (δ * δ) = δ * δ := by rw [map_mul, hδ]; ring
  let d : L⁺ := ⟨δ * δ, (IsCMField.complexConj_eq_self_iff L _).1 hfix⟩
  have hd : δ * δ = algebraMap L⁺ L d := rfl
  have hr : s.i δ ≠ 0 := (map_ne_zero _).2 hδ0
  have hk : F.κ (GlobalTheory.SplitLift.Em s δ) = 0 := by
    ext1 u
    change F.κ (GlobalTheory.SplitLift.Em s δ) u = 0
    by_cases hu : u = s.w
    · subst hu
      rw [kappa_split F s i hic hi, GlobalTheory.SplitLift.proj_Em s δ d hd hr, map_zero]
    · apply kappa_eq_zero
      apply GlobalTheory.SplitLift.compAt_Em
      rw [← under_w s]
      exact fun h => hns ⟨u, hu, h⟩
  have h0 : GlobalTheory.SplitLift.Em s δ = 0 := F.κ.injective (hk.trans (map_zero _).symm)
  have h1 := GlobalTheory.SplitLift.proj_Ep s δ d hd hr
  rw [← GlobalTheory.SplitLift.conj_Em s δ hδ, h0, map_zero, map_zero] at h1
  exact zero_ne_one h1
end GlobalTheory.SplitDict

namespace GlobalTheory.SplitDict

theorem locComp_agree : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (π : NG.AutRep L n)
    (U : Submodule ℂ (UA L n → ℂ)), Dict F π U → ∀ (s : SplitPlace L) (σ : SmIrr (GL (Fin n) (s.w.adicCompletion L))),
    IsCompAlong U (locU n s.w) ((cLoc s.w).comp (locU n s.w).subtype) σ.ρ →
    ∃ τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L)), IsLocS π.S s τ ∧ Nonempty (τ.ρ.Equiv σ.ρ) := by
  intro L _ _ _ n F π U hD s σ hσ
  obtain ⟨τ, hτ, -⟩ := GlobalTheory.T.splitPlaceLocalComponent_exists_unique_class L n π s
  refine ⟨τ, hτ, ?_⟩
  obtain ⟨i, T, hic, hi, hTinj, hTS, hTeq⟩ := hτ
  have hsplit : IsSplitAt s.w := isSplitAt_w F s i hic hi
  obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL L n s.w hsplit
  obtain ⟨sec, hsecT, hsecL⟩ := GlobalTheory.SplitEmb.exists_hom_trivOutside_loc L n s
  have hlift : ∀ x : locU n s.w, ∃ y, TrivOutside {s.v} y ∧ F.j y = x := by
    intro x
    refine ⟨sec (Matrix.GeneralLinearGroup.map i.symm.toRingHom (cLoc s.w (x : UA L n))), hsecT _, ?_⟩
    have hm := j_mem_locU F s _ (hsecT (Matrix.GeneralLinearGroup.map i.symm.toRingHom (cLoc s.w (x : UA L n))))
    have h1 : e ⟨_, hm⟩ = e x := by
      rw [he, he, cLoc_j F s i hic hi, hsecL]
      refine Units.ext (Matrix.ext fun a c => ?_)
      simp
    exact congrArg Subtype.val (e.injective h1)
  let R : U →ₗ[ℂ] (GAf L n → ℂ) := (LinearMap.funLeft ℂ ℂ F.j).comp U.subtype
  have hRinj : Function.Injective R := by
    refine (injective_iff_map_eq_zero R).2 fun φ hφ => ?_
    have h0 : ∀ y ∈ finU (E := L) (n := n), (φ : UA L n → ℂ) y = 0 := fun y hy => by
      obtain ⟨x, rfl⟩ := F.onto y hy
      exact congrFun hφ x
    exact Subtype.ext (GlobalTheory.T.definiteUnitaryAutForm_eq_zero_of_finitePoints L n φ (hD.1.aut φ φ.2) h0)
  have hRrange : LinearMap.range R = U.map (LinearMap.funLeft ℂ ℂ F.j) := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  obtain ⟨hnt, -⟩ := (GlobalTheory.CuspRep.isIrreducible_iff _).1 τ.irr
  obtain ⟨a0, ha0⟩ := exists_ne (0 : τ.V)
  have hTa0 : T a0 ≠ 0 := fun h => ha0 (hTinj (h.trans (map_zero T).symm))
  obtain ⟨g0, hg0⟩ : ∃ g0, T a0 g0 ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hTa0 (funext hc)
  obtain ⟨lam, hlam⟩ : ∃ lam : Module.Dual ℂ π.W, lam (T a0 g0) ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hg0 ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 hc)
  let T' : τ.V →ₗ[ℂ] (GAf L n → ℂ) := (LinearMap.compLeft lam (GAf L n)).comp T
  have hT'mem : ∀ a, T' a ∈ LinearMap.range R := fun a => by
    rw [hRrange, hD.2]
    exact Submodule.subset_span ⟨T a, hTS a, lam, rfl⟩
  let eR := LinearEquiv.ofInjective R hRinj
  let f : τ.V →ₗ[ℂ] (UA L n → ℂ) := U.subtype ∘ₗ eR.symm.toLinearMap ∘ₗ T'.codRestrict _ hT'mem
  have hfU : ∀ a, f a ∈ U := fun a => (eR.symm _).2
  have hf : ∀ a y, f a (F.j y) = lam (T a y) := fun a y => by
    have h1 := congrArg Subtype.val (eR.apply_symm_apply ⟨T' a, hT'mem a⟩)
    exact congrFun h1 y
  have hcomp : IsCompAlong U (locU n s.w) ((cLoc s.w).comp (locU n s.w).subtype) τ.ρ := by
    refine ⟨τ.irr, f, fun h => hlam ?_, hfU, fun x a => ?_⟩
    · have h1 := hf a0 g0
      rw [h] at h1
      exact h1.symm
    · obtain ⟨y, hyT, hyx⟩ := hlift x
      have hm2 : RU L n (x : UA L n) (f a) ∈ U := hD.1.stable _ _ (hfU a)
      have h1 : R ⟨_, hfU (τ.ρ (((cLoc s.w).comp (locU n s.w).subtype) x) a)⟩ = R ⟨_, hm2⟩ := by
        funext g
        change f _ (F.j g) = f a (F.j g * x)
        rw [hf, ← hyx, ← map_mul, hf]
        have h2 := hTeq y hyT a
        rw [← cLoc_j F s i hic hi, hyx] at h2
        change lam (T (τ.ρ (cLoc s.w (x : UA L n)) a) g) = _
        rw [h2]
        rfl
      exact congrArg Subtype.val (hRinj h1)
  let P : GlobalTheory.DefU.AutSub L n := ⟨U, hD.1⟩
  let τ' : SmIrr (GL (Fin n) (s.w.adicCompletion L)) := ⟨τ.V, τ.ρ, τ.smooth, τ.irr⟩
  have h1 : (GlobalTheory.DefU.AU.mk P).IsLoc s.w (Quotient.mk _ τ') := hcomp
  have h2 : (GlobalTheory.DefU.AU.mk P).IsLoc s.w (Quotient.mk _ σ) := hσ
  have h3 := GlobalTheory.DefU.AU.isLoc_unique_of_isSplitAt L n _ s.w _ _ hsplit h1 h2
  obtain ⟨φ⟩ := Quotient.exact h3
  exact ⟨φ⟩

end GlobalTheory.SplitDict
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalComponentsAgreeSplitPlaceDictionaryStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localComponents_agree_splitPlace_dictionary : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (π : NG.AutRep L n) (U : Submodule ℂ (UA L n → ℂ)), Dict F π U → ∀ (s : SplitPlace L) (σ : SmIrr (GL (Fin n) (s.w.adicCompletion L))), IsCompAlong U (locU n s.w) ((cLoc s.w).comp (locU n s.w).subtype) σ.ρ → ∃ τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L)), IsLocS π.S s τ ∧ Nonempty (τ.ρ.Equiv σ.ρ) := by
  first | exact @GlobalTheory.SplitDict.locComp_agree | exact GlobalTheory.SplitDict.locComp_agree | (intros; apply GlobalTheory.SplitDict.locComp_agree <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraicWeightAgreesUnderModularFormDictionary
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualWeylModuleIntertwinesGLOfUnitaryGroup
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualWeylModuleIntertwinesGLOfUnitaryGroup
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped Matrix

noncomputable section

namespace GlobalTheory.AlgWtHW

theorem eval_adjugate_mvPolynomialX {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n) :
    MvPolynomial.eval (fun p : Fin n × Fin n => g p.1 p.2)
      ((Matrix.mvPolynomialX (Fin n) (Fin n) ℂ).adjugate x y) = g.adjugate x y := by
  have h := RingHom.map_adjugate (MvPolynomial.eval (fun p : Fin n × Fin n => g p.1 p.2))
    (Matrix.mvPolynomialX (Fin n) (Fin n) ℂ)
  have h2 : (MvPolynomial.eval (fun p : Fin n × Fin n => g p.1 p.2)).mapMatrix
      (Matrix.mvPolynomialX (Fin n) (Fin n) ℂ) = g := by
    ext i j; simp [Matrix.mvPolynomialX]
  rw [h2] at h
  simpa using congrFun (congrFun h x) y

theorem eval_det_mvPolynomialX {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) :
    MvPolynomial.eval (fun p : Fin n × Fin n => g p.1 p.2) (Matrix.mvPolynomialX (Fin n) (Fin n) ℂ).det = g.det := by
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [Matrix.mvPolynomialX]

theorem det_mul_inv_apply {n : ℕ} (B : GL (Fin n) ℂ) (x y : Fin n) :
    B.val.det * (B⁻¹).val x y = B.val.adjugate x y := by
  have h : B.val.adjugate = B.val.det • (B⁻¹).val := by
    calc B.val.adjugate = B.val.adjugate * (B.val * (B⁻¹).val) := by rw [Units.mul_inv, Matrix.mul_one]
      _ = (B.val.adjugate * B.val) * (B⁻¹).val := by rw [Matrix.mul_assoc]
      _ = _ := by rw [Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
  rw [h, Matrix.smul_apply, smul_eq_mul]

theorem exists_det_pow_mul_eq_poly {n : ℕ} (Q : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ) :
    ∃ (d : ℕ) (P : MvPolynomial (Fin n × Fin n) ℂ), ∀ B : GL (Fin n) ℂ,
      B.val.det ^ d * MvPolynomial.eval (Sum.elim (fun p => B.val p.1 p.2) (fun p => (B⁻¹).val p.1 p.2)) Q =
        MvPolynomial.eval (fun p => B.val p.1 p.2) P := by
  induction Q using MvPolynomial.induction_on with
  | C a => exact ⟨0, MvPolynomial.C a, fun B => by simp⟩
  | add p q hp hq =>
    obtain ⟨d₁, P₁, h₁⟩ := hp
    obtain ⟨d₂, P₂, h₂⟩ := hq
    refine ⟨d₁ + d₂, P₁ * (Matrix.mvPolynomialX (Fin n) (Fin n) ℂ).det ^ d₂ +
      P₂ * (Matrix.mvPolynomialX (Fin n) (Fin n) ℂ).det ^ d₁, fun B => ?_⟩
    simp only [map_add (f := _), map_mul, map_pow, eval_det_mvPolynomialX, ← h₁ B, ← h₂ B]
    ring
  | mul_X p v hp =>
    obtain ⟨d, P, h⟩ := hp
    cases v with
    | inl x =>
      refine ⟨d, P * MvPolynomial.X x, fun B => ?_⟩
      simp only [map_mul, MvPolynomial.eval_X, Sum.elim_inl, ← h B]
      ring
    | inr x =>
      refine ⟨d + 1, P * (Matrix.mvPolynomialX (Fin n) (Fin n) ℂ).adjugate x.1 x.2, fun B => ?_⟩
      simp only [map_mul, MvPolynomial.eval_X, Sum.elim_inr, eval_adjugate_mvPolynomialX, ← h B,
        ← det_mul_inv_apply]
      ring

theorem sqRep_intertwines_of_unitary : ∀ (n : ℕ) (lam : DomWeight n) (ι : Type) [Fintype ι] [DecidableEq ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ), GlobalTheory.AlgWtHW.IsPolyRep Φ → ∀ M : nablaSq ℂ n lam →ₗ[ℂ] (ι → ℂ), (∀ (u : Matrix.unitaryGroup (Fin n) ℂ) (v : nablaSq ℂ n lam), M (GlobalTheory.Branching.sqRep ℂ n lam (GlobalTheory.Branching.unitaryIncl n u) v) = Matrix.mulVec (Φ (GlobalTheory.Branching.unitaryIncl n u)) (M v)) → ∀ (B : GL (Fin n) ℂ) (v : nablaSq ℂ n lam), M (GlobalTheory.Branching.sqRep ℂ n lam B v) = Matrix.mulVec (Φ B) (M v) := by
  classical
  intro n lam ι _ _ Φ hΦ M hU B v
  funext k
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (nablaSq ℂ n lam)
  let π := (nablaSq ℂ n lam).linearProjOfIsCompl C hC
  let l : Module.Dual ℂ (MvPolynomial (Fin n × Fin n) ℂ) := LinearMap.proj k ∘ₗ M ∘ₗ π
  have hl : ∀ B' : GL (Fin n) ℂ, M (GlobalTheory.Branching.sqRep ℂ n lam B' v) k =
      detPow ℂ n B' lam.detShift * l (Formalism.GradedWeylDivisibility.rowAct ℂ (B'.val)ᵀ v.1) := by
    intro B'
    calc M (GlobalTheory.Branching.sqRep ℂ n lam B' v) k = l (sqAct ℂ n lam B' v.1) := by
          simp only [l, π, LinearMap.comp_apply, LinearMap.proj_apply]
          have := Submodule.linearProjOfIsCompl_apply_left hC (GlobalTheory.Branching.sqRep ℂ n lam B' v)
          rw [← GlobalTheory.Branching.sqRep_coe]
          exact (congrArg (fun w => M w k) this).symm
      _ = _ := by rw [sqAct, map_smul, smul_eq_mul]
  obtain ⟨P₁, hP₁⟩ := GlobalTheory.Branching.exists_poly_rowAct_coef n n v.1 l
  let R₁ := MvPolynomial.rename Prod.swap P₁
  have hR₁ : ∀ g : Matrix (Fin n) (Fin n) ℂ,
      MvPolynomial.eval (fun x => g x.1 x.2) R₁ = l (Formalism.GradedWeylDivisibility.rowAct ℂ gᵀ v.1) := by
    intro g
    rw [hP₁, MvPolynomial.eval_rename]
    rfl
  choose Q hQ using hΦ.poly
  let Qs := ∑ j, Q k j * MvPolynomial.C ((M v) j)
  have hQs : ∀ B' : GL (Fin n) ℂ,
      MvPolynomial.eval (Sum.elim (fun p => B'.val p.1 p.2) (fun p => (B'⁻¹).val p.1 p.2)) Qs = (Φ B' *ᵥ M v) k := by
    intro B'
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Qs, map_sum, map_mul, MvPolynomial.eval_C, ← hQ, Matrix.mulVec, dotProduct]
  obtain ⟨d, P₂, hP₂⟩ := exists_det_pow_mul_eq_poly Qs
  set a := lam.detShift
  set m : ℕ := a.natAbs
  have ha : 0 ≤ a + (m : ℤ) := by omega
  have hdet : ∀ B' : GL (Fin n) ℂ, B'.val.det ≠ 0 := fun B' => (Matrix.isUnits_det_units B').ne_zero
  have hdp : ∀ B' : GL (Fin n) ℂ, detPow ℂ n B' a = B'.val.det ^ a := by
    intro B'
    simp [detPow, Units.val_zpow_eq_zpow_val]
  have key : ∀ B' : GL (Fin n) ℂ,
      B'.val.det ^ d * B'.val.det ^ (a + (m : ℤ)).toNat * l (Formalism.GradedWeylDivisibility.rowAct ℂ (B'.val)ᵀ v.1) -
        B'.val.det ^ m * MvPolynomial.eval (fun p => B'.val p.1 p.2) P₂ =
      B'.val.det ^ d * B'.val.det ^ m * (M (GlobalTheory.Branching.sqRep ℂ n lam B' v) k - (Φ B' *ᵥ M v) k) := by
    intro B'
    have hx := hdet B'
    rw [hl, ← hQs, ← hP₂, hdp]
    have e1 : B'.val.det ^ (a + (m : ℤ)).toNat = B'.val.det ^ m * B'.val.det ^ a := by
      rw [← zpow_natCast (B'.val.det) (a + (m : ℤ)).toNat, Int.toNat_of_nonneg ha, zpow_add₀ hx, zpow_natCast]
      ring
    rw [e1]
    ring
  let Dp := (Matrix.mvPolynomialX (Fin n) (Fin n) ℂ).det
  let Qd := Dp ^ d * Dp ^ (a + (m : ℤ)).toNat * R₁ - Dp ^ m * P₂
  have hQd : ∀ g : Matrix (Fin n) (Fin n) ℂ, MvPolynomial.eval (fun x => g x.1 x.2) Qd =
      g.det ^ d * g.det ^ (a + (m : ℤ)).toNat * l (Formalism.GradedWeylDivisibility.rowAct ℂ gᵀ v.1) -
        g.det ^ m * MvPolynomial.eval (fun p => g p.1 p.2) P₂ := by
    intro g
    simp only [Qd, Dp, map_sub, map_mul, map_pow, eval_det_mvPolynomialX, hR₁]
  have Q0 : Qd = 0 := by
    refine GlobalTheory.Branching.eq_zero_of_vanish_unitaryGroup n Qd fun u hu => ?_
    have h1 := key (GlobalTheory.Branching.unitaryIncl n ⟨u, hu⟩)
    have h2 := congrFun (hU ⟨u, hu⟩ v) k
    rw [h2, sub_self, mul_zero] at h1
    rw [hQd]
    exact h1
  have h3 := key B
  rw [← hQd, Q0, map_zero] at h3
  have hx := hdet B
  have h4 : B.val.det ^ d * B.val.det ^ m ≠ 0 := mul_ne_zero (pow_ne_zero _ hx) (pow_ne_zero _ hx)
  exact sub_eq_zero.1 ((mul_eq_zero.1 h3.symm).resolve_left h4)

end GlobalTheory.AlgWtHW
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualWeylModuleIntertwinesGLOfUnitaryGroupStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualWeylModule_intertwines_GL_of_unitaryGroup : ∀ (n : ℕ) (lam : DomWeight n) (ι : Type) [Fintype ι] [DecidableEq ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ), GlobalTheory.AlgWtHW.IsPolyRep Φ → ∀ M : nablaSq ℂ n lam →ₗ[ℂ] (ι → ℂ), (∀ (u : Matrix.unitaryGroup (Fin n) ℂ) (v : nablaSq ℂ n lam), M (GlobalTheory.Branching.sqRep ℂ n lam (GlobalTheory.Branching.unitaryIncl n u) v) = Matrix.mulVec (Φ (GlobalTheory.Branching.unitaryIncl n u)) (M v)) → ∀ (B : GL (Fin n) ℂ) (v : nablaSq ℂ n lam), M (GlobalTheory.Branching.sqRep ℂ n lam B v) = Matrix.mulVec (Φ B) (M v) := by
  first | exact @GlobalTheory.AlgWtHW.sqRep_intertwines_of_unitary | exact GlobalTheory.AlgWtHW.sqRep_intertwines_of_unitary | (intros; apply GlobalTheory.AlgWtHW.sqRep_intertwines_of_unitary <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHighestWeightVectorDualWeylModuleUpper
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHighestWeightVectorDualWeylModuleUpper
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.HwUpper

theorem telescope (d : ℕ → ℂ) (f : ℕ → ℕ) (hf : ∀ s, f (s + 1) ≤ f s) (m : ℕ) :
    (∏ s ∈ Finset.range m, (∏ k ∈ Finset.range (s + 1), d k) ^ (f s - f (s + 1))) *
      (∏ k ∈ Finset.range m, d k) ^ f m = ∏ k ∈ Finset.range m, d k ^ f k := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ (fun k => d k ^ f k), ← ih, mul_assoc, mul_assoc]
    congr 1
    rw [← pow_add, Nat.sub_add_cancel (hf m), Finset.prod_range_succ, mul_pow]

theorem hwScal_transpose {n : ℕ} (ν : Fin n → ℕ) (hν : Antitone ν) (B : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.BasicNotions.Examples₂.NZ.hwScal ℂ (le_refl n) ν B.transpose = ∏ i, B i i ^ ν i := by
  classical
  set d : ℕ → ℂ := fun k => if h : k < n then B ⟨k, h⟩ ⟨k, h⟩ else 1 with hd
  set f : ℕ → ℕ := fun k => if h : k < n then ν ⟨k, h⟩ else 0 with hfd
  have hf : ∀ s, f (s + 1) ≤ f s := by
    intro s
    by_cases h : s + 1 < n
    · simp only [hfd, dif_pos h, dif_pos (show s < n by omega)]
      exact hν (show (⟨s, by omega⟩ : Fin n) ≤ ⟨s + 1, h⟩ from Fin.mk_le_mk.mpr (by omega))
    · simp only [hfd, dif_neg h]
      exact Nat.zero_le _
  have hinner : ∀ s : Fin n, (∏ a : Fin (s.val + 1),
      B.transpose (Fin.castLE (by omega) a) (Fin.castLE (by omega) a)) = ∏ k ∈ Finset.range (s.val + 1), d k := by
    intro s
    rw [← Fin.prod_univ_eq_prod_range]
    refine Finset.prod_congr rfl fun a _ => ?_
    have ha : a.val < n := by omega
    simp only [hd, dif_pos ha, Matrix.transpose_apply]
    rfl
  have hexp : ∀ s : Fin n, ν s - Formalism.GradedWeylDivisibility.nuNext ν s = f s.val - f (s.val + 1) := by
    intro s
    simp only [hfd, dif_pos s.2, Formalism.GradedWeylDivisibility.nuNext]
  unfold Formalism.BasicNotions.Examples₂.NZ.hwScal
  simp_rw [hinner, hexp]
  rw [Fin.prod_univ_eq_prod_range (fun s => (∏ k ∈ Finset.range (s + 1), d k) ^ (f s - f (s + 1))) n]
  have hfn : f n = 0 := by simp [hfd]
  have ht := telescope d f hf n
  rw [hfn, pow_zero, mul_one] at ht
  rw [ht, ← Fin.prod_univ_eq_prod_range (fun k => d k ^ f k) n]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [hd, hfd, dif_pos i.2]

theorem exists_hw_upper : ∀ (n : ℕ) (lam : DomWeight n), ∃ v : nablaSq ℂ n lam, v ≠ 0 ∧
    ∀ B : GL (Fin n) ℂ, (B : Matrix (Fin n) (Fin n) ℂ).BlockTriangular id →
      GlobalTheory.Branching.sqRep ℂ n lam B v = (∏ i, ((B : Matrix (Fin n) (Fin n) ℂ) i i) ^ (lam.w i)) • v := by
  intro n lam
  have ha : Antitone lam.natW := fun i j hij => by
    have := lam.anti hij
    simp only [DomWeight.natW]
    omega
  refine ⟨⟨extremal ℂ n lam, Formalism.GradedWeylDivisibility.hwMem ℂ n n le_rfl _ ha⟩, fun h =>
    Formalism.GradedWeylDivisibility.hwNe ℂ n n le_rfl lam.natW (congrArg Subtype.val h), fun B hB => ?_⟩
  apply Subtype.ext
  set M : Matrix (Fin n) (Fin n) ℂ := (B : Matrix (Fin n) (Fin n) ℂ) with hM
  have hl : ∀ i j : Fin n, i < j → M.transpose i j = 0 := fun i j hij => by
    rw [Matrix.transpose_apply]; exact hB hij
  have hdet : M.det = ∏ i, M i i := Matrix.det_of_upperTriangular hB
  have hne : ∀ i, M i i ≠ 0 := by
    have h0 : M.det ≠ 0 := by
      have := (Matrix.GeneralLinearGroup.det B).ne_zero
      simpa [hM] using this
    rw [hdet, Finset.prod_ne_zero_iff] at h0
    exact fun i => h0 i (Finset.mem_univ i)
  have hw_eq : ∀ i, (lam.natW i : ℤ) + lam.detShift = lam.w i := by
    intro i
    have hle : lam.detShift ≤ lam.w i := by
      unfold DomWeight.detShift
      have hn : 0 < n := Fin.pos i
      rw [dif_pos hn]
      exact lam.anti (Fin.mk_le_mk.mpr (by omega) : i ≤ ⟨n - 1, by omega⟩)
    simp only [DomWeight.natW]
    omega
  rw [GlobalTheory.Branching.sqRep_coe, Submodule.coe_smul]
  show detPow ℂ n B lam.detShift • Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) M.transpose (extremal ℂ n lam) = _
  unfold extremal
  rw [Formalism.BasicNotions.Examples₂.NZ.rowAct_hw ℂ le_rfl lam.natW M.transpose hl, hwScal_transpose lam.natW ha M, smul_smul]
  congr 1
  unfold detPow
  rw [Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply, ← hM, hdet, ← Finset.prod_zpow,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← zpow_natCast, ← zpow_add₀ (hne i), add_comm, hw_eq]

end GlobalTheory.HwUpper
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHighestWeightVectorDualWeylModuleUpperStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_highest_weight_vector_dualWeylModule_upper : ∀ (n : ℕ) (lam : DomWeight n), ∃ v : nablaSq ℂ n lam, v ≠ 0 ∧ ∀ B : GL (Fin n) ℂ, (B : Matrix (Fin n) (Fin n) ℂ).BlockTriangular id → GlobalTheory.Branching.sqRep ℂ n lam B v = (∏ i, ((B : Matrix (Fin n) (Fin n) ℂ) i i) ^ (lam.w i)) • v := by
  first | exact @GlobalTheory.HwUpper.exists_hw_upper | exact GlobalTheory.HwUpper.exists_hw_upper | (intros; apply GlobalTheory.HwUpper.exists_hw_upper <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraicWeightAgreesUnderModularFormDictionary
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open Matrix Topology Pointwise

noncomputable section

namespace GlobalTheory.WeightDict

theorem exists_pair_ne_zero {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (hρ : ρ.IsIrreducible) (hσ : σ.IsIrreducible)
    (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (hB0 : B ≠ 0) (hB : ∀ γ x y, B (ρ γ x) (σ γ y) = B x y) {x : V} (hx : x ≠ 0)
    {y : W} (hy : y ≠ 0) : ∃ γ, B (ρ γ x) y ≠ 0 := by
  by_contra hc
  push Not at hc
  let K : Subrepresentation ρ :=
    { toSubmodule :=
        { carrier := {w | ∀ γ, B (ρ γ w) y = 0}
          add_mem' := fun {a b} ha hb γ => by rw [map_add (f := _), map_add (f := _), LinearMap.add_apply, ha γ, hb γ, add_zero]
          zero_mem' := fun γ => by simp
          smul_mem' := fun c a ha γ => by rw [map_smul, map_smul, LinearMap.smul_apply, ha γ, smul_zero] }
      apply_mem_toSubmodule := fun g w hw γ => by
        have := hw (γ * g)
        rwa [map_mul] at this }
  let K' : Subrepresentation σ :=
    { toSubmodule := LinearMap.ker B.flip
      apply_mem_toSubmodule := fun g z hz => by
        rw [LinearMap.mem_ker] at hz ⊢
        ext w
        have h1 := hB g (ρ g⁻¹ w) z
        rw [Representation.self_inv_apply] at h1
        exact h1.trans (LinearMap.congr_fun hz _) }
  rcases hρ.eq_bot_or_eq_top K with h | h
  · have h1 : K.toSubmodule = ⊥ := congrArg Subrepresentation.toSubmodule h
    have h2 : x ∈ K.toSubmodule := hc
    rw [h1] at h2
    exact hx h2
  · have h1 : K.toSubmodule = ⊤ := congrArg Subrepresentation.toSubmodule h
    have hyK : y ∈ K'.toSubmodule := by
      change B.flip y = 0
      ext w
      have h2 : w ∈ K.toSubmodule := by rw [h1]; exact Submodule.mem_top
      have h3 : B (ρ 1 w) y = 0 := h2 1
      rw [map_one] at h3
      exact h3
    rcases hσ.eq_bot_or_eq_top K' with h' | h'
    · have h3 : K'.toSubmodule = ⊥ := congrArg Subrepresentation.toSubmodule h'
      rw [h3] at hyK
      exact hy hyK
    · have h3 : LinearMap.ker B.flip = ⊤ := congrArg Subrepresentation.toSubmodule h'
      refine hB0 (LinearMap.ext fun w => LinearMap.ext fun z => ?_)
      have h4 : z ∈ LinearMap.ker B.flip := by rw [h3]; exact Submodule.mem_top
      exact LinearMap.congr_fun (LinearMap.mem_ker.1 h4) w

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem coord_conjugate (τ : L →+* ℂ) (z : Cinf L) :
    coord (ComplexEmbedding.conjugate τ) z = starRingEnd ℂ (coord τ z) := by
  have hm : InfinitePlace.mk (ComplexEmbedding.conjugate τ) = InfinitePlace.mk τ := InfinitePlace.mk_conjugate_eq τ
  have hne : ComplexEmbedding.conjugate τ ≠ τ := fun h =>
    IsTotallyComplex.complexEmbedding_not_isReal τ (ComplexEmbedding.isReal_iff.2 h)
  rw [GlobalTheory.EmbUnitary.coord_eq, GlobalTheory.EmbUnitary.coord_eq, hm]
  unfold GlobalTheory.EmbUnitary.twist
  rw [hm]
  rcases InfinitePlace.embedding_mk_eq τ with h | h
  · rw [if_pos h, if_neg (by rw [h]; exact hne.symm)]
    rfl
  · rw [if_pos h, if_neg (by rw [h]; exact hne)]
    simp

theorem polyMat_embU {ι : Type} (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ) (τ : L →+* ℂ)
    (x : embU n τ) : GlobalTheory.WeightRealExt.polyMat P (x : UA L n) = GlobalTheory.AlgWtHW.evM P (NG.evPt τ (cEmb τ (x : UA L n))) := by
  ext i j
  change MvPolynomial.eval _ _ = MvPolynomial.eval _ _
  congr 2
  funext p
  obtain ⟨σ, s, t⟩ := p
  change (cEmb σ (x : UA L n)).val s t = _
  unfold NG.evPt
  dsimp only
  split_ifs with h1 h2 h3
  · rw [h1]
  · rw [h2]
    have hu := Matrix.mem_unitaryGroup_iff.1 (GlobalTheory.EmbUnitary.cEmb_mem τ (x : UA L n))
    rw [Units.inv_eq_of_mul_eq_one_right hu]
    exact coord_conjugate τ _
  all_goals
    have hk : InfinitePlace.mk σ ≠ InfinitePlace.mk τ := fun h => by
      rcases InfinitePlace.mk_eq_iff.1 h with h | h
      · exact h1 h
      · exact h2 (by rw [← h]; ext z; simp)
    have h4 := MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 x.2).2 σ) hk)
    rw [h4]
    simp [Matrix.one_apply, h3]

theorem pair_ext {W : Type} [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ (GQ L n) W} (a : NG.AlgWt L n)
    (R : UA L n →* Module.End ℂ W) (hfin : ∀ k ∈ finU (E := L) (n := n), R k = 1)
    (hrat : ∀ (γ : UA L n) (γQ : GQ L n) (γ₀ : GL (Fin n) L), γ.1 = ratGL L n γ₀ →
      (((γQ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
        (γ₀ : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom → R γ = ρ γQ)
    (hcont : ∀ (v : W) (μ : Module.Dual ℂ W), Continuous fun g : UA L n => μ (R g v))
    (B : W →ₗ[ℂ] a.W →ₗ[ℂ] ℂ) (hB : ∀ γ x y, B (ρ γ x) (a.ρ γ y) = B x y)
    {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ a.W)
    (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ) (hP : GlobalTheory.AlgWtHW.Agrees a b P)
    (w : W) (c : ι → ℂ) (g : UA L n) :
    B (R g⁻¹ w) (b.equivFun.symm c) = B w (b.equivFun.symm (GlobalTheory.WeightRealExt.polyMat P g *ᵥ c)) := by
  have h1 : Continuous fun g : UA L n => B (R g⁻¹ w) (b.equivFun.symm c) :=
    (hcont w (B.flip (b.equivFun.symm c))).comp continuous_inv
  have h2 : Continuous fun g : UA L n => B w (b.equivFun.symm (GlobalTheory.WeightRealExt.polyMat P g *ᵥ c)) :=
    (LinearMap.continuous_of_finiteDimensional (B w ∘ₗ b.equivFun.symm.toLinearMap)).comp
      ((GlobalTheory.WeightRealExt.continuous_polyMat P).matrix_mulVec continuous_const)
  refine congrFun (Continuous.ext_on GlobalTheory.WeightRealExt.dense_rat_fin h1 h2 fun z hz => ?_) g
  obtain ⟨γ, hγ, k, hk, rfl⟩ := Set.mem_mul.1 hz
  obtain ⟨γ₀, hγ₀⟩ := GlobalTheory.WeightRealExt.exists_unitaryRationalMatrix_of_mem_definiteUnitaryRational hγ
  have hR : R γ = ρ ((GlobalTheory.WeightRealExt.ratPt (E := L) (n := n)) γ₀) := hrat γ _ γ₀.1 hγ₀ rfl
  have hM : GlobalTheory.WeightRealExt.polyMat P (γ * k) = LinearMap.toMatrix b b (a.ρ ((GlobalTheory.WeightRealExt.ratPt (E := L) (n := n)) γ₀)) := by
    have hk' : cInf k = 1 := hk
    rw [GlobalTheory.WeightRealExt.polyMat_congr P (g := γ * k) (h := γ) (by rw [map_mul, hk', mul_one]),
      GlobalTheory.WeightRealExt.polyMat_rat P γ γ₀.1 hγ₀]
    exact (hP _ γ₀.1 rfl).symm
  have e1 : b.equivFun.symm (GlobalTheory.WeightRealExt.polyMat P (γ * k) *ᵥ c) =
      a.ρ ((GlobalTheory.WeightRealExt.ratPt (E := L) (n := n)) γ₀) (b.equivFun.symm c) := by
    rw [hM, LinearEquiv.symm_apply_eq]
    have := LinearMap.toMatrix_mulVec_repr b b (a.ρ ((GlobalTheory.WeightRealExt.ratPt (E := L) (n := n)) γ₀)) (b.equivFun.symm c)
    rw [← b.equivFun_apply, ← b.equivFun_apply, LinearEquiv.apply_symm_apply] at this
    exact this
  have e2 : ρ ((GlobalTheory.WeightRealExt.ratPt (E := L) (n := n)) γ₀) (R (γ * k)⁻¹ w) = w := by
    rw [_root_.mul_inv_rev, map_mul, hfin _ ((finU (E := L) (n := n)).inv_mem hk), one_mul, ← hR, ← Module.End.mul_apply, ← map_mul,
      mul_inv_cancel, map_one, Module.End.one_apply]
  change B (R (γ * k)⁻¹ w) _ = B w _
  rw [e1, ← hB ((GlobalTheory.WeightRealExt.ratPt (E := L) (n := n)) γ₀), e2]

theorem phi_mem {F : FinIso L n} {π : NG.AutRep L n} {U : Submodule ℂ (UA L n → ℂ)} (hU : Dict F π U)
    (R : UA L n →* Module.End ℂ π.W) (hfin : ∀ k ∈ finU (E := L) (n := n), R k = 1)
    (hrat : ∀ (γ : UA L n) (γQ : GQ L n) (γ₀ : GL (Fin n) L), γ.1 = ratGL L n γ₀ →
      (((γQ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
        (γ₀ : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom → R γ = π.ρ γQ)
    (hcont : ∀ (v : π.W) (μ : Module.Dual ℂ π.W), Continuous fun g : UA L n => μ (R g v))
    {f : GAf L n → π.W} (hf : f ∈ π.S) (μ : Module.Dual ℂ π.W) : GlobalTheory.FormDictEx.phi F R f μ ∈ U := by
  haveI : FiniteDimensional ℂ π.W := π.alg.1
  have hmem : (fun x => μ (f x)) ∈ U.map (LinearMap.funLeft ℂ ℂ F.j) := by
    rw [hU.2]
    exact Submodule.subset_span ⟨f, hf, μ, rfl⟩
  obtain ⟨u, hu, hue⟩ := hmem
  have ha : GlobalTheory.FormDictEx.phi F R f μ ∈ GlobalTheory.DefU.autU L n :=
    GlobalTheory.FormDictEx.isAutFormU_phi F π.ρ R hfin hrat hcont (π.irrS.1.le hf) μ
  have hu' : u ∈ GlobalTheory.DefU.autU L n := hU.1.aut u hu
  have h0 := GlobalTheory.DefiniteDense.eq_zero_of_finU L n _ ((GlobalTheory.DefU.autU L n).sub_mem ha hu') fun y hy => by
    obtain ⟨x, rfl⟩ := F.onto y hy
    rw [Pi.sub_apply, GlobalTheory.FormDictEx.phi_j F R hfin, sub_eq_zero]
    exact (congrFun hue x).symm
  rw [sub_eq_zero.1 h0]
  exact hu

theorem weight_agree : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (π : NG.AutRep L n)
    (U : Submodule ℂ (UA L n → ℂ)), Dict F π U → ∀ (a : NG.AlgWt L n), π.toAlgWt.IsDual a → ∀ τ : L →+* ℂ,
      ∃ lam, HasWeightAt U τ lam ∧ a.HWAt τ lam.w := by
  intro L _ _ _ n F π U hU a hdual τ
  obtain ⟨B, hB0, hB⟩ := hdual
  obtain ⟨R, hfin, hrat, hcont⟩ := GlobalTheory.WeightRealExt.exists_extension L n π.toAlgWt
  obtain ⟨_, ι, _, _, b, P, hP⟩ := a.alg
  obtain ⟨e, he⟩ := GlobalTheory.EmbUnitary.exists_equiv_unitaryGroup L n τ
  have hΦ := GlobalTheory.T.isPolynomialRepGLComplex_algebraicWeight_evalPoint L n a ι b P hP τ
  set Φ : GL (Fin n) ℂ → Matrix ι ι ℂ := fun A => GlobalTheory.AlgWtHW.evM P (NG.evPt τ A) with hΦd
  have hΦx : ∀ x : embU n τ, Φ (cEmb τ (x : UA L n)) = GlobalTheory.WeightRealExt.polyMat P (x : UA L n) := fun x =>
    (polyMat_embU P τ x).symm
  let σ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) (ι → ℂ) :=
    { toFun := fun u => Matrix.mulVecLin (Φ (GlobalTheory.Branching.unitaryIncl n u))
      map_one' := by
        rw [map_one, hΦ.one, Matrix.mulVecLin_one]
        rfl
      map_mul' := fun u u' => by
        rw [map_mul, hΦ.mul, Matrix.mulVecLin_mul]
        rfl }
  have hσc : ∀ (l : Module.Dual ℂ (ι → ℂ)) (v : ι → ℂ), Continuous fun u => l (σ u v) := by
    intro l v
    have h1 : ∀ u, σ u v = GlobalTheory.WeightRealExt.polyMat P (e.symm u : UA L n) *ᵥ v := fun u => by
      rw [← hΦx, ← he, e.apply_symm_apply]
      rfl
    simp only [h1]
    exact (LinearMap.continuous_of_finiteDimensional l).comp
      (((GlobalTheory.WeightRealExt.continuous_polyMat P).comp (continuous_subtype_val.comp e.symm.continuous)).matrix_mulVec
        continuous_const)
  haveI : Nontrivial a.W := by
    by_contra hs
    rw [not_nontrivial_iff_subsingleton] at hs
    exact hB0 (LinearMap.ext fun w => LinearMap.ext fun z => by rw [Subsingleton.elim z 0, map_zero, map_zero])
  haveI : Nontrivial (ι → ℂ) := b.equivFun.symm.toEquiv.nontrivial
  obtain ⟨lam, M₀, hM₀⟩ := GlobalTheory.UnitaryContainsType.exists_smallRep_intertwining n (ι → ℂ) σ hσc
  let M : nablaSq ℂ n lam →ₗ[ℂ] (ι → ℂ) := M₀.toLinearMap
  have hM := GlobalTheory.T.dualWeylModule_intertwines_GL_of_unitaryGroup n lam ι Φ hΦ M fun u v => Representation.IntertwiningMap.isIntertwining _ _ M₀ u v
  have hirr := GlobalTheory.DefU.isIrreducible_sqRep n lam
  have hinj : ∀ v, v ≠ 0 → M v ≠ 0 := by
    intro v hv hMv
    let K : Subrepresentation (GlobalTheory.Branching.sqRep ℂ n lam) :=
      { toSubmodule := LinearMap.ker M
        apply_mem_toSubmodule := fun g z hz => by
          rw [LinearMap.mem_ker] at hz ⊢
          rw [hM, hz, Matrix.mulVec_zero] }
    rcases hirr.eq_bot_or_eq_top K with h | h
    · have h1 : LinearMap.ker M = ⊥ := congrArg Subrepresentation.toSubmodule h
      exact hv (by rw [← Submodule.mem_bot ℂ, ← h1]; exact hMv)
    · have h1 : LinearMap.ker M = ⊤ := congrArg Subrepresentation.toSubmodule h
      exact hM₀ (Representation.IntertwiningMap.ext (LinearMap.ker_eq_top.1 h1))
  obtain ⟨v₀, hv₀, hw⟩ := GlobalTheory.T.exists_highest_weight_vector_dualWeylModule_upper n lam
  refine ⟨lam, ?_, ι, inferInstance, inferInstance, b, P, hP, M v₀, hinj v₀ hv₀, fun A hA => ?_⟩
  · obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot π.irrS.2.1
    obtain ⟨x₀, hx₀⟩ : ∃ x, f x ≠ 0 := by
      by_contra h
      push Not at h
      exact hf0 (funext h)
    refine ⟨hirr, GlobalTheory.FormDictEx.phiR F R f ∘ₗ B.flip ∘ₗ b.equivFun.symm.toLinearMap ∘ₗ M, fun h0 => ?_,
      fun v => phi_mem hU R hfin hrat hcont hf (B.flip (b.equivFun.symm (M v))), fun x v => ?_⟩
    · obtain ⟨γ, hγ⟩ := exists_pair_ne_zero π.irr a.irr B hB0 hB hx₀
        ((LinearEquiv.map_ne_zero_iff b.equivFun.symm).2 (hinj v₀ hv₀))
      apply hγ
      have h1 := congrFun (LinearMap.congr_fun h0 v₀) (F.j ((γ : GAf L n) * x₀))
      change GlobalTheory.FormDictEx.phi F R f (B.flip (b.equivFun.symm (M v₀))) _ = 0 at h1
      rw [GlobalTheory.FormDictEx.phi_j F R hfin, (π.irrS.1.le hf).1] at h1
      exact h1
    · change GlobalTheory.FormDictEx.phi F R f (B.flip (b.equivFun.symm (M (GlobalTheory.Branching.sqRep ℂ n lam (cEmb τ (x : UA L n)) v)))) =
        RU L n (x : UA L n) (GlobalTheory.FormDictEx.phi F R f (B.flip (b.equivFun.symm (M v))))
      rw [GlobalTheory.FormDictEx.RU_phi, GlobalTheory.FormDictEx.fy_inf F (Subgroup.mem_inf.1 x.2).1, GlobalTheory.FormDictEx.rt_one, hM, hΦx]
      congr 1
      exact LinearMap.ext fun w => (pair_ext a R hfin hrat hcont B hB b P hP w (M v) x).symm
  · have h1 := hM A v₀
    rw [hw A hA, map_smul] at h1
    exact h1.symm

end GlobalTheory.WeightDict

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraicWeightAgreesUnderModularFormDictionaryStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraicWeight_agrees_under_modularForm_dictionary : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (π : NG.AutRep L n) (U : Submodule ℂ (UA L n → ℂ)), Dict F π U → ∀ (a : NG.AlgWt L n), π.toAlgWt.IsDual a → ∀ τ : L →+* ℂ, ∃ lam, HasWeightAt U τ lam ∧ a.HWAt τ lam.w := by
  first | exact @GlobalTheory.WeightDict.weight_agree | exact GlobalTheory.WeightDict.weight_agree | (intros; apply GlobalTheory.WeightDict.weight_agree <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryFiniteAdeleIdentificationNonemptyPresenta
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryFiniteAdeleIdentificationNonemptyPresenta
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
open Matrix
open scoped TensorProduct

namespace GlobalTheory.FinIsoProof

open GlobalTheory.DefU.ClassFin GlobalTheory.AdeleBaseChange

theorem nonempty_finIso (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) : Nonempty (FinIso L n) := by
  obtain ⟨ι, hι⟩ := exists_toAd (maximalRealSubfield L) L
  let κ : AL L ≃+* FiniteAdeleRing (𝓞 L) L := RingEquiv.ofBijective ι ⟨map_injective hι, map_surjective hι⟩
  have hκ : ∀ x a, κ (x ⊗ₜ a) = algebraMap L _ x * adMap (maximalRealSubfield L) L a := hι
  have hc : ∀ y, κ (conjAL L y) = conjFin (cc L) (κ y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul x a =>
      change κ ((IsCMField.complexConj L x) ⊗ₜ a) = _
      rw [hκ, hκ, map_mul, conjFin_adMap (cc L) (fun k => IsCMField.complexConj_apply_eq_self L k), conjFin_algebraMap]
      rfl
  have hc' : ∀ y, κ.symm (conjFin (cc L) y) = conjAL L (κ.symm y) := fun y => by
    rw [RingEquiv.symm_apply_eq, hc, RingEquiv.apply_symm_apply]
  let p : GAf L n →* GL (Fin n) (FiniteAdeleRing (𝓞 L) L) :=
    (GeneralLinearGroup.map κ.toRingHom).comp (ReciprocityTheory.Aut.GA L n).subtype
  have hp : ∀ x, Formalism.UG.cT (conjFin (cc L)) (p x).val * (p x).val = 1 := fun x =>
    unitary_map κ.toRingHom (conjAL L) (conjFin (cc L)) hc x.1.val (mul_eq_one_comm.mp x.2)
  let j : GAf L n →* UA L n := ((finGL L n).comp p).codRestrict (UA L n) fun x => finGL_mem_UA _ (hp x)
  refine ⟨⟨κ, map_tmul_one hι, ?_, j, fun x => MonoidHom.mem_ker.2 (pInf_finGL (p x)), ?_, ?_⟩⟩
  · intro w v h
    have hv : w.under (𝓞 (maximalRealSubfield L)) = v := HeightOneSpectrum.ext h
    subst hv
    refine ⟨locMap _ w, GlobalTheory.LFun.InertChart.continuous_complMap (rfl : w.under (𝓞 (maximalRealSubfield L)) = _), fun a => ?_⟩
    rw [hκ, map_one, one_mul]
    rfl
  · intro x w s t
    have h1 : (finGL L n (p x)).val.map (pFin L) = (p x).val := congrArg Units.val (pFin_finGL (p x))
    exact congrArg (pLoc L w) (congrFun₂ h1 s t)
  · intro y hy
    let z := GeneralLinearGroup.map (pFin L) y.1
    have hz : Formalism.UG.cT (conjFin (cc L)) z.val * z.val = 1 := cT_pFin y
    have hm : GeneralLinearGroup.map κ.symm.toRingHom z ∈ ReciprocityTheory.Aut.GA L n :=
      mul_eq_one_comm.mp (unitary_map κ.symm.toRingHom _ _ hc' z.val hz)
    refine ⟨⟨_, hm⟩, Subtype.ext ?_⟩
    have e : p ⟨_, hm⟩ = z := Units.ext (Matrix.ext fun i k => κ.apply_symm_apply _)
    change finGL L n (p ⟨_, hm⟩) = _
    rw [e]
    exact finGL_pFin ⟨y, hy⟩

theorem finIso_nonempty : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ), Nonempty (FinIso L n) :=
  fun L _ _ _ n => nonempty_finIso L n

end GlobalTheory.FinIsoProof
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryFiniteAdeleIdentificationNonemptyPresentaStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryFiniteAdeleIdentification_nonempty_presentations : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ), Nonempty (FinIso L n) := by
  first | exact @GlobalTheory.FinIsoProof.finIso_nonempty | exact GlobalTheory.FinIsoProof.finIso_nonempty | (intros; apply GlobalTheory.FinIsoProof.finIso_nonempty <;> assumption)
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.UnitaryReadTrue

theorem host_conj_eq (D : D7) (x : D.host.E) : D.host.conj x = IsCMField.complexConj D.host.E x :=
  D.host.φ₀.injective (by
    rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply])

theorem coe_cO (D : D7) (x : 𝓞 D.host.E) :
    ((IsCMField.ringOfIntegersComplexConj D.host.E x : 𝓞 D.host.E) : D.host.E) = D.host.conj (x : D.host.E) := by
  rw [IsCMField.coe_ringOfIntegersComplexConj, host_conj_eq]

theorem exists_splitPlace_w (D : D7) (w : PlE D.host) (hw : IsSplitPl D.host w) :
    ∃ s : SplitPlace D.host.E, s.w = w := by
  obtain ⟨s, -, hc, -⟩ := GlobalTheory.SplitConjPlace.splitEx_all D w hw
  refine ⟨GlobalTheory.SplitConjPlace.conjSP s, HeightOneSpectrum.ext (Ideal.ext fun x => ?_)⟩
  change Valued.v (s.i (IsCMField.complexConj D.host.E (x : D.host.E))) < 1 ↔ _
  change IsCMField.ringOfIntegersComplexConj D.host.E x ∈ s.w.asIdeal ↔ _
  exact (hc x _ (coe_cO D x)).symm

theorem not_isSplitAt (D : D7) (w : PlE D.host) (hw : ¬ IsSplitPl D.host w) : ¬ IsSplitAt w := by
  rintro ⟨u, hu, he⟩
  apply hw
  let cO := IsCMField.ringOfIntegersComplexConj D.host.E
  have cc (x : 𝓞 D.host.E) : cO (cO x) = x := by
    apply RingOfIntegers.ext
    simp only [cO, IsCMField.coe_ringOfIntegersComplexConj]
    exact IsCMField.complexConj_apply_apply D.host.E (x : D.host.E)
  let Q : PlE D.host := {
    asIdeal := w.asIdeal.comap (cO : 𝓞 D.host.E →+* 𝓞 D.host.E)
    isPrime := Ideal.comap_isPrime _ _
    ne_bot := by
      obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
      refine (Submodule.ne_bot_iff _).2 ⟨cO y, ?_, ?_⟩
      · change cO (cO y) ∈ w.asIdeal
        rwa [cc]
      · intro h
        apply hy0
        rw [← cc y, h, map_zero] }
  have hQ (x : 𝓞 D.host.E) : x ∈ Q.asIdeal ↔ cO x ∈ w.asIdeal := Iff.rfl
  have hne : Q ≠ w := by
    intro h
    have nle : ∀ P : PlE D.host, u ≠ P → ¬ u.asIdeal ≤ P.asIdeal := fun P hne hle =>
      hne (HeightOneSpectrum.ext (u.isMaximal.eq_of_le P.isPrime.ne_top hle))
    obtain ⟨x, hx, hxw⟩ := Set.not_subset.mp (nle w hu)
    have hxc : cO x ∉ w.asIdeal := by
      intro hxc
      have : x ∈ Q.asIdeal := (hQ x).2 hxc
      exact hxw (h ▸ this)
    have hfix : cO (x * cO x) = x * cO x := by rw [map_mul, cc, mul_comm]
    obtain ⟨y, hy⟩ := (IsCMField.ringOfIntegersComplexConj_eq_self_iff D.host.E _).1 hfix
    have hyu : y ∈ u.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) := by
      rw [Ideal.mem_comap, hy]; exact u.asIdeal.mul_mem_right _ hx
    change y ∈ (u.under (𝓞 (maximalRealSubfield D.host.E))).asIdeal at hyu
    rw [he] at hyu
    change y ∈ w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) at hyu
    rw [Ideal.mem_comap, hy] at hyu
    rcases w.isPrime.mem_or_mem hyu with h1 | h1
    · exact hxw h1
    · exact hxc h1
  have hle : ¬ w.asIdeal ≤ Q.asIdeal := fun hle =>
    hne (HeightOneSpectrum.ext (w.isMaximal.eq_of_le Q.isPrime.ne_top hle)).symm
  obtain ⟨x, hx, hx'⟩ := Set.not_subset.mp hle
  refine ⟨x, hx, fun y hy hyw => hx' ?_⟩
  refine (hQ x).2 ?_
  have : y = IsCMField.ringOfIntegersComplexConj D.host.E x := RingOfIntegers.ext (by rw [hy, coe_cO])
  rwa [← this]

theorem infOf_eq_infOfWeight {n : ℕ} (lam : DomWeight n) : NG.infOf lam.w = infOfWeight lam := by
  unfold NG.infOf infOfWeight
  congr 1
  funext k
  ring

end GlobalTheory.UnitaryReadTrue
