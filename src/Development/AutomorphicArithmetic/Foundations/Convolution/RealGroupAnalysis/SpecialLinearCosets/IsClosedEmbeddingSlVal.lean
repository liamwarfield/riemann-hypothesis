module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.Cols

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.DetMulInv
section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.IntegrableSB
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical NNReal

namespace UpperTheory.ConvolutionTheory.R2.I.CentralConjugation

section

variable {K : Type} [Field K] [TopologicalSpace K] [IsTopologicalRing K]

private def cjE (x : GL (Fin 2) K) :
    Matrix.SpecialLinearGroup (Fin 2) K ≃ₜ* Matrix.SpecialLinearGroup (Fin 2) K where
  toFun m := ⟨(x⁻¹).val * m.1 * x.val, by
    rw [Matrix.det_mul, Matrix.det_mul, m.2, mul_one, ← Matrix.det_mul, Units.inv_mul, Matrix.det_one]⟩
  invFun m := ⟨x.val * m.1 * (x⁻¹).val, by
    rw [Matrix.det_mul, Matrix.det_mul, m.2, mul_one, ← Matrix.det_mul, Units.mul_inv, Matrix.det_one]⟩
  left_inv m := by
    apply Subtype.ext
    show x.val * ((x⁻¹).val * m.1 * x.val) * (x⁻¹).val = m.1
    simp only [mul_assoc, Units.mul_inv_cancel_left, Units.mul_inv, mul_one]
  right_inv m := by
    apply Subtype.ext
    show (x⁻¹).val * (x.val * m.1 * (x⁻¹).val) * x.val = m.1
    simp only [mul_assoc, Units.inv_mul_cancel_left, Units.inv_mul, mul_one]
  map_mul' m n := by
    apply Subtype.ext
    show (x⁻¹).val * (m.1 * n.1) * x.val = ((x⁻¹).val * m.1 * x.val) * ((x⁻¹).val * n.1 * x.val)
    simp only [mul_assoc, Units.mul_inv_cancel_left]
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const

variable [LocallyCompactSpace (Matrix.SpecialLinearGroup (Fin 2) K)]
  [MeasurableSpace (Matrix.SpecialLinearGroup (Fin 2) K)]
  [BorelSpace (Matrix.SpecialLinearGroup (Fin 2) K)]

private noncomputable def cc (x : GL (Fin 2) K) : ℝ≥0 := mulEquivHaarChar (cjE x)

private theorem cc_ne (x : GL (Fin 2) K) : cc x ≠ 0 := (mulEquivHaarChar_pos (cjE x)).ne'

private theorem cc_mul (x y : GL (Fin 2) K) : cc (x * y) = cc x * cc y := by
  have h : cjE (x * y) = (cjE x).trans (cjE y) := by
    ext1 m
    apply Subtype.ext
    show ((x * y)⁻¹).val * m.1 * (x * y).val = (y⁻¹).val * ((x⁻¹).val * m.1 * x.val) * y.val
    simp only [_root_.mul_inv_rev, Units.val_mul, mul_assoc]
  unfold cc
  rw [h, mulEquivHaarChar_trans]

private theorem cc_central (z : GL (Fin 2) K) (hz : ∀ m : Matrix (Fin 2) (Fin 2) K, z.val * m = m * z.val) :
    cc z = 1 := by
  have h : cjE z = ContinuousMulEquiv.refl _ := by
    ext1 m
    apply Subtype.ext
    show (z⁻¹).val * m.1 * z.val = m.1
    rw [mul_assoc, ← hz, Units.inv_mul_cancel_left]
  unfold cc
  rw [h, mulEquivHaarChar_refl]

private theorem cc_of_sq (d t : GL (Fin 2) K) (h : d * t = t * t * d) : cc t = 1 := by
  have e := congrArg cc h
  rw [cc_mul, cc_mul, cc_mul] at e
  apply mul_left_cancel₀ (mul_ne_zero (cc_ne t) (cc_ne d))
  rw [mul_one, show cc t * cc d * cc t = cc t * cc t * cc d by ring, ← e]
  ring


variable (K) in
private noncomputable def ccS : Matrix.SpecialLinearGroup (Fin 2) K →* ℝ≥0 where
  toFun g := cc (Matrix.SpecialLinearGroup.toGL g)
  map_one' := by
    rw [map_one]
    exact cc_central 1 (by simp)
  map_mul' g h := by rw [map_mul, cc_mul]

private theorem cc_SL (h2 : (2 : K) ≠ 0) (g : Matrix.SpecialLinearGroup (Fin 2) K) :
    cc (Matrix.SpecialLinearGroup.toGL g) = 1 := by
  let d₁ : GL (Fin 2) K := ⟨!![2, 0; 0, 1], !![2⁻¹, 0; 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [h2],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [h2]⟩
  let d₂ : GL (Fin 2) K := ⟨!![1, 0; 0, 2], !![1, 0; 0, 2⁻¹],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [h2],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [h2]⟩
  have hT := UpperTheory.ConvolutionTheory.R2.I.genSL K (ccS K).ker
    (fun g b hg => by
      rw [MonoidHom.mem_ker]
      refine cc_of_sq d₁ _ (Units.ext ?_)
      show d₁.val * g.1 = g.1 * g.1 * d₁.val
      rw [hg]
      ext i j; fin_cases i <;> fin_cases j <;> simp [d₁, Matrix.mul_apply, Fin.sum_univ_two] <;> ring)
    (fun g c hg => by
      rw [MonoidHom.mem_ker]
      refine cc_of_sq d₂ _ (Units.ext ?_)
      show d₂.val * g.1 = g.1 * g.1 * d₂.val
      rw [hg]
      ext i j; fin_cases i <;> fin_cases j <;> simp [d₂, Matrix.mul_apply, Fin.sum_univ_two] <;> ring)
  have : g ∈ (ccS K).ker := by rw [hT]; trivial
  exact this

private theorem cc_eq_one (h2 : (2 : K) ≠ 0) (x : GL (Fin 2) K) : cc x = 1 := by
  have hd : x.val.det ≠ 0 := by
    intro h0
    have h1 : x.val.det * (x⁻¹).val.det = 1 := by
      rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  set t := x.val.det with ht
  let s : Matrix.SpecialLinearGroup (Fin 2) K := ⟨t⁻¹ • (x.val * x.val), by
    rw [Matrix.det_smul, Matrix.det_mul, ← ht]
    simp only [Fintype.card_fin]
    field_simp⟩
  let z : GL (Fin 2) K := ⟨t • 1, t⁻¹ • 1, by simp [smul_smul, hd], by simp [smul_smul, hd]⟩
  have hx : x * x = z * Matrix.SpecialLinearGroup.toGL s := by
    apply Units.ext
    show x.val * x.val = (t • (1 : Matrix (Fin 2) (Fin 2) K)) * (t⁻¹ • (x.val * x.val))
    simp [smul_smul, hd]
  have hz : cc z = 1 := cc_central z (fun m => by
    show (t • (1 : Matrix (Fin 2) (Fin 2) K)) * m = m * (t • (1 : Matrix (Fin 2) (Fin 2) K))
    simp)
  have e := congrArg cc hx
  rw [cc_mul, cc_mul, hz, cc_SL h2, one_mul] at e
  have e' : ((cc x : ℝ≥0) : ℝ) * (cc x : ℝ≥0) = 1 := by exact_mod_cast e
  rcases mul_self_eq_one_iff.1 e' with h | h
  · exact_mod_cast h
  · have := (cc x).coe_nonneg
    linarith

private theorem mp_cjE (h2 : (2 : K) ≠ 0) (x : GL (Fin 2) K) :
    MeasurePreserving (cjE x) (Measure.haar : Measure (Matrix.SpecialLinearGroup (Fin 2) K)) Measure.haar := by
  refine ⟨(map_continuous (cjE x)).measurable, ?_⟩
  have h := mulEquivHaarChar_smul_map (Measure.haar : Measure (Matrix.SpecialLinearGroup (Fin 2) K)) (cjE x)
  have h1 : mulEquivHaarChar (cjE x) = 1 := cc_eq_one h2 x
  rwa [h1, one_smul] at h

private theorem integral_cjE (h2 : (2 : K) ≠ 0) (x : GL (Fin 2) K)
    (f : Matrix.SpecialLinearGroup (Fin 2) K → ℂ) :
    ∫ m, f (cjE x m) ∂(Measure.haar) = ∫ m, f m ∂(Measure.haar) :=
  (mp_cjE h2 x).integral_comp (cjE x).toHomeomorph.measurableEmbedding f

private theorem integrable_SB (a : SB (Matrix.SpecialLinearGroup (Fin 2) K)) :
    Integrable a.1 (Measure.haar : Measure (Matrix.SpecialLinearGroup (Fin 2) K)) :=
  a.2.1.continuous.integrable_of_hasCompactSupport a.2.2

private theorem exists_I (h2 : (2 : K) ≠ 0) :
    ∃ I : SB (Matrix.SpecialLinearGroup (Fin 2) K) →ₗ[ℂ] ℂ,
      (∀ (g : Matrix.SpecialLinearGroup (Fin 2) K) (a a' : SB (Matrix.SpecialLinearGroup (Fin 2) K)),
        (∀ m, a'.1 m = a.1 (m * g)) → I a' = I a) ∧
      (∀ (x : GL (Fin 2) K) (a a' : SB (Matrix.SpecialLinearGroup (Fin 2) K)),
        (∀ m m' : Matrix.SpecialLinearGroup (Fin 2) K, m'.1 = (x⁻¹).val * m.1 * x.val → a'.1 m = a.1 m') →
          I a' = I a) ∧
      (∀ (U : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)) (a : SB (Matrix.SpecialLinearGroup (Fin 2) K)),
        IsOpen (U : Set (Matrix.SpecialLinearGroup (Fin 2) K)) → a.1 = ind U → I a ≠ 0) := by
  let I : SB (Matrix.SpecialLinearGroup (Fin 2) K) →ₗ[ℂ] ℂ :=
    { toFun := fun a => ∫ m, a.1 m ∂(Measure.haar)
      map_add' := fun a b => integral_add (integrable_SB a) (integrable_SB b)
      map_smul' := fun c a => integral_smul c a.1 }
  have hI : ∀ a, I a = ∫ m, a.1 m ∂(Measure.haar) := fun _ => rfl
  refine ⟨I, ?_, ?_, ?_⟩
  · intro g a a' h
    have hm : ∀ m, m * g = g * cjE (Matrix.SpecialLinearGroup.toGL g) m := by
      intro m
      apply Subtype.ext
      show m.1 * g.1 = g.1 * (((Matrix.SpecialLinearGroup.toGL g)⁻¹).val * m.1 * (Matrix.SpecialLinearGroup.toGL g).val)
      have e : g.1 * ((Matrix.SpecialLinearGroup.toGL g)⁻¹).val = 1 :=
        Units.mul_inv (Matrix.SpecialLinearGroup.toGL g)
      rw [← mul_assoc, ← mul_assoc, e, one_mul]
      rfl
    rw [hI, hI]
    simp_rw [h, hm]
    rw [integral_cjE h2 _ (fun y => a.1 (g * y))]
    exact integral_mul_left_eq_self a.1 g
  · intro x a a' h
    rw [hI, hI]
    simp_rw [fun m => h m (cjE x m) rfl]
    exact integral_cjE h2 x a.1
  · intro U a hU ha
    have hs : Function.support a.1 = (U : Set _) := by
      rw [ha]
      ext m
      by_cases hm : m ∈ (U : Set _) <;> simp [ind, hm]
    have hfin : (Measure.haar : Measure (Matrix.SpecialLinearGroup (Fin 2) K)) (U : Set _) ≠ ⊤ := by
      have hc : IsCompact (tsupport a.1) := a.2.2
      exact ((measure_mono (hs ▸ subset_tsupport a.1)).trans_lt hc.measure_lt_top).ne
    have hpos : (Measure.haar : Measure (Matrix.SpecialLinearGroup (Fin 2) K)) (U : Set _) ≠ 0 :=
      (hU.measure_pos _ ⟨1, U.one_mem⟩).ne'
    rw [hI, ha]
    unfold ind
    rw [integral_indicator_const _ hU.measurableSet]
    simp only [Measure.real, smul_eq_mul, Complex.real_smul, mul_one]
    exact_mod_cast (ENNReal.toReal_ne_zero.2 ⟨hpos, hfin⟩)

end

end UpperTheory.ConvolutionTheory.R2.I.CentralConjugation

theorem UpperTheory.ConvolutionTheory.R2.I.invI :
    ∀ (F : Type) [Field F] [NumberField F] (v : P F), ∃ I : SB (SL v) →ₗ[ℂ] ℂ, InvI I := by
  intro F _ _ v
  letI : MeasurableSpace (SL v) := borel _
  haveI : BorelSpace (SL v) := ⟨rfl⟩
  haveI : LocallyCompactSpace (M2 v) := inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → Kv v))
  haveI : LocallyCompactSpace (SL v) :=
    (Matrix.SpecialLinearGroup.isClosedEmbedding_val (n := Fin 2) (R := Kv v)).locallyCompactSpace
  have h2 : (2 : Kv v) ≠ 0 := by
    haveI : CharZero (Kv v) := charZero_of_injective_algebraMap (algebraMap F (Kv v)).injective
    exact two_ne_zero
  obtain ⟨I, h₁, h₂, h₃⟩ := UpperTheory.ConvolutionTheory.R2.I.CentralConjugation.exists_I (K := Kv v) h2
  exact ⟨I, ⟨h₁, h₂, h₃⟩⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.TranslateMemSB
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

section SlopeTestRemainingChoices

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

private theorem ind_mem_SB (U : Subgroup G) (ho : IsOpen (U : Set G)) (hc : IsCompact (U : Set G)) :
    ind U ∈ SB G := by
  have hcl : IsClopen (U : Set G) := ⟨U.isClosed_of_isOpen ho, ho⟩
  refine GroundTheory.LocalField.mem_schwartzBruhat.mpr ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_exists_open]
    intro x
    by_cases hx : x ∈ U
    · refine ⟨U, ho, hx, fun y hy => ?_⟩
      simp [ind, Set.indicator, hx, show y ∈ U from hy]
    · refine ⟨(U : Set G)ᶜ, hcl.compl.isOpen, hx, fun y hy => ?_⟩
      simp [ind, Set.indicator, hx, show y ∉ U from hy]
  · refine HasCompactSupport.intro hc fun x hx => ?_
    simp [ind, Set.indicator, show x ∉ U from hx]

private theorem translate_mem_SB (a : SB G) (g : G) : (fun m => a.1 (m * g)) ∈ SB G := by
  obtain ⟨h1, h2⟩ := GroundTheory.LocalField.mem_schwartzBruhat.mp a.2
  exact GroundTheory.LocalField.mem_schwartzBruhat.mpr
    ⟨h1.comp_continuous (continuous_mul_const g), h2.comp_homeomorph (Homeomorph.mulRight g)⟩

private theorem scale (B : SB G →ₗ[ℂ] ℂ) (U U' : Subgroup G) (s : Finset G) (hs : ∀ g ∈ s, g ∈ U)
    (hsum : ∀ x, ind U x = ∑ g ∈ s, ind U' (x * g⁻¹)) (a a' : SB G) (ha : a.1 = ind U)
    (ha' : a'.1 = ind U')
    (hB : ∀ g ∈ U, ∀ b b' : SB G, (∀ m, b'.1 m = b.1 (m * g)) → B b' = B b) :
    B a = (s.card : ℂ) * B a' := by
  let t : G → SB G := fun g => ⟨fun m => a'.1 (m * g⁻¹), translate_mem_SB a' g⁻¹⟩
  have hat : a = ∑ g ∈ s, t g := by
    apply Subtype.ext
    funext x
    rw [ha, hsum x, Submodule.coe_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun g _ => ?_
    change ind U' (x * g⁻¹) = a'.1 (x * g⁻¹)
    rw [ha']
  have ht : ∀ g ∈ s, B (t g) = B a' := fun g hg =>
    hB g⁻¹ (U.inv_mem (hs g hg)) a' (t g) fun _ => rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hat, map_sum, Finset.sum_congr rfl ht, Finset.sum_const, nsmul_eq_mul]

variable [T2Space G]

private theorem cross_le (B C : SB G →ₗ[ℂ] ℂ) (U U' : Subgroup G) (hle : U' ≤ U)
    (hc : IsCompact (U : Set G)) (ho : IsOpen (U' : Set G)) (a a' : SB G) (ha : a.1 = ind U)
    (ha' : a'.1 = ind U')
    (hB : ∀ g ∈ U, ∀ b b' : SB G, (∀ m, b'.1 m = b.1 (m * g)) → B b' = B b)
    (hC : ∀ g ∈ U, ∀ b b' : SB G, (∀ m, b'.1 m = b.1 (m * g)) → C b' = C b) :
    B a * C a' = B a' * C a := by
  obtain ⟨s, -, hs, hsum⟩ := cosetSum G U U' hle hc ho
  rw [scale B U U' s hs hsum a a' ha ha' hB, scale C U U' s hs hsum a a' ha ha' hC]
  ring

private theorem core {V : Type} [AddCommGroup V] [Module ℂ V] (hL : Lgrp G) (act : G → V →ₗ[ℂ] V)
    (hact : ∀ f, {g | act g f = f} ∈ 𝓝 (1 : G)) (I : SB G →ₗ[ℂ] ℂ)
    (hI : ∀ (g : G) (a a' : SB G), (∀ m, a'.1 m = a.1 (m * g)) → I a' = I a)
    (hne : ∀ (U : Subgroup G) (a : SB G), IsOpen (U : Set G) → a.1 = ind U → I a ≠ 0)
    (β : V →ₗ[ℂ] SB G →ₗ[ℂ] ℂ)
    (hβ : ∀ (g : G) f (a a' : SB G), (∀ m, a'.1 m = a.1 (m * g)) → β (act g f) a' = β f a) :
    ∃ Λ : V →ₗ[ℂ] ℂ, ∀ f (U : Subgroup G) (a : SB G), IsOpen (U : Set G) → a.1 = ind U →
      (∀ g ∈ U, act g f = f) → β f a = I a * Λ f := by

  have hinv : ∀ (f : V) (U : Subgroup G), (∀ g ∈ U, act g f = f) →
      ∀ g ∈ U, ∀ b b' : SB G, (∀ m, b'.1 m = b.1 (m * g)) → β f b' = β f b := by
    intro f U hf g hg b b' hb
    have := hβ g f b b' hb
    rwa [hf g hg] at this

  have hex : ∀ f f' : V, ∃ U : Subgroup G, IsOpen (U : Set G) ∧ IsCompact (U : Set G) ∧
      (∀ g ∈ U, act g f = f) ∧ (∀ g ∈ U, act g f' = f') := by
    intro f f'
    obtain ⟨U, ho, hc, hsub⟩ := hL _ (Filter.inter_mem (hact f) (hact f'))
    exact ⟨U, ho, hc, fun g hg => (hsub hg).1, fun g hg => (hsub hg).2⟩

  have hcpt : ∀ (U : Subgroup G) (a : SB G), IsOpen (U : Set G) → a.1 = ind U →
      IsCompact (U : Set G) := by
    intro U a ho ha
    obtain ⟨-, h2⟩ := GroundTheory.LocalField.mem_schwartzBruhat.mp a.2
    refine IsCompact.of_isClosed_subset h2 (U.isClosed_of_isOpen ho) fun x hx => ?_
    refine subset_tsupport _ ?_
    rw [Function.mem_support, ha]
    simp [ind, Set.indicator, show x ∈ U from hx]

  have hcross : ∀ (f : V) (U₁ U₂ : Subgroup G) (a₁ a₂ : SB G), IsOpen (U₁ : Set G) →
      IsOpen (U₂ : Set G) → a₁.1 = ind U₁ → a₂.1 = ind U₂ → (∀ g ∈ U₁, act g f = f) →
      (∀ g ∈ U₂, act g f = f) → β f a₁ * I a₂ = β f a₂ * I a₁ := by
    intro f U₁ U₂ a₁ a₂ ho₁ ho₂ h₁ h₂ hf₁ hf₂
    have hc₁ := hcpt U₁ a₁ ho₁ h₁
    have hc₂ := hcpt U₂ a₂ ho₂ h₂
    have ho₃ : IsOpen ((U₁ ⊓ U₂ : Subgroup G) : Set G) := by
      rw [Subgroup.coe_inf]
      exact ho₁.inter ho₂
    have hc₃ : IsCompact ((U₁ ⊓ U₂ : Subgroup G) : Set G) :=
      IsCompact.of_isClosed_subset hc₁ ((U₁ ⊓ U₂).isClosed_of_isOpen ho₃) fun x hx => hx.1
    let a₃ : SB G := ⟨ind (U₁ ⊓ U₂), ind_mem_SB _ ho₃ hc₃⟩
    have e₁ := cross_le (β f) I U₁ (U₁ ⊓ U₂) inf_le_left hc₁ ho₃ a₁ a₃ h₁ rfl
      (hinv f U₁ hf₁) fun g _ => hI g
    have e₂ := cross_le (β f) I U₂ (U₁ ⊓ U₂) inf_le_right hc₂ ho₃ a₂ a₃ h₂ rfl
      (hinv f U₂ hf₂) fun g _ => hI g
    have h₃ : I a₃ ≠ 0 := hne _ a₃ ho₃ rfl
    apply mul_right_cancel₀ h₃
    linear_combination I a₂ * e₁ - I a₁ * e₂
  choose W hWo hWc hWf _ using fun f : V => hex f f
  let A : V → SB G := fun f => ⟨ind (W f), ind_mem_SB _ (hWo f) (hWc f)⟩
  let Λ₀ : V → ℂ := fun f => β f (A f) / I (A f)
  have key : ∀ f (U : Subgroup G) (a : SB G), IsOpen (U : Set G) → a.1 = ind U →
      (∀ g ∈ U, act g f = f) → β f a = I a * Λ₀ f := by
    intro f U a ho ha hf
    have h := hcross f U (W f) a (A f) ho (hWo f) ha rfl hf (hWf f)
    have hA : I (A f) ≠ 0 := hne _ (A f) (hWo f) rfl
    change β f a = I a * (β f (A f) / I (A f))
    field_simp
    linear_combination h
  have hadd : ∀ f f', Λ₀ (f + f') = Λ₀ f + Λ₀ f' := by
    intro f f'
    obtain ⟨U, ho, hc, h₁, h₂⟩ := hex f f'
    let a : SB G := ⟨ind U, ind_mem_SB _ ho hc⟩
    have hIa : I a ≠ 0 := hne U a ho rfl
    apply mul_left_cancel₀ hIa
    have hf : ∀ g ∈ U, act g (f + f') = f + f' := fun g hg => by
      rw [map_add (f := _), h₁ g hg, h₂ g hg]
    rw [mul_add, ← key f U a ho rfl h₁, ← key f' U a ho rfl h₂, ← key (f + f') U a ho rfl hf,
      map_add, LinearMap.add_apply]
  have hsmul : ∀ (c : ℂ) f, Λ₀ (c • f) = c * Λ₀ f := by
    intro c f
    obtain ⟨U, ho, hc, h₁, -⟩ := hex f f
    let a : SB G := ⟨ind U, ind_mem_SB _ ho hc⟩
    have hIa : I a ≠ 0 := hne U a ho rfl
    apply mul_left_cancel₀ hIa
    have hf : ∀ g ∈ U, act g (c • f) = c • f := fun g hg => by
      rw [map_smul, h₁ g hg]
    rw [mul_left_comm, ← key f U a ho rfl h₁, ← key (c • f) U a ho rfl hf, map_smul,
      LinearMap.smul_apply, smul_eq_mul]
  exact ⟨⟨⟨Λ₀, hadd⟩, fun c f => by simpa using hsmul c f⟩, key⟩

end SlopeTestRemainingChoices

theorem UpperTheory.ConvolutionTheory.R2.I.lamEx :
    ∀ (F : Type) [Field F] [NumberField F] (v : P F) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GLv v) V), (∀ f, IsOpen {g | ρ g f = f}) →
      ∀ (I : SB (SL v) →ₗ[ℂ] ℂ), InvI I → ∀ β : V →ₗ[ℂ] SB (SL v) →ₗ[ℂ] ℂ,
      (∀ (g : SL v) f (a a' : SB (SL v)), (∀ m, a'.1 m = a.1 (m * g)) → β (ρ (Matrix.SpecialLinearGroup.toGL g) f) a' = β f a) →
      ∃ Λ : V →ₗ[ℂ] ℂ, ∀ f (U : Subgroup (SL v)) (a : SB (SL v)), IsOpen (U : Set (SL v)) → a.1 = ind U →
        (∀ g ∈ U, ρ (Matrix.SpecialLinearGroup.toGL g) f = f) → β f a = I a * Λ f := by
  intro F _ _ v V _ _ ρ hρ I hI β hβ
  refine core (lgrp F v).1 (fun g => ρ (Matrix.SpecialLinearGroup.toGL g)) (fun f => ?_) I
    hI.right hI.ne β hβ
  have ho : IsOpen {g : SL v | ρ (Matrix.SpecialLinearGroup.toGL g) f = f} :=
    (hρ f).preimage Matrix.SpecialLinearGroup.continuous_toGL
  exact ho.mem_nhds (by simp)
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

section SlopeTestRemainingChoices

variable {F : Type} [Field F] [NumberField F] {v : P F}

private lemma det_inv_mul (y : GLv v) : ((y⁻¹).val).det * (y.val).det = 1 := by
  rw [← Matrix.det_mul, Units.inv_mul, Matrix.det_one]

private lemma det_mul_inv (y : GLv v) : (y.val).det * ((y⁻¹).val).det = 1 := by
  rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]

private noncomputable def tw (y h : GLv v) (e : (y.val).det = (h.val).det) : SL v ≃ₜ SL v where
  toFun m := ⟨(y⁻¹).val * m.1 * h.val, by
    rw [Matrix.det_mul, Matrix.det_mul, m.2, mul_one, ← e, det_inv_mul]⟩
  invFun m := ⟨y.val * m.1 * (h⁻¹).val, by
    rw [Matrix.det_mul, Matrix.det_mul, m.2, mul_one, e, det_mul_inv]⟩
  left_inv m := by
    apply Subtype.ext
    have hy : y.val * (y⁻¹).val = 1 := Units.mul_inv y
    have hh : h.val * (h⁻¹).val = 1 := Units.mul_inv h
    change y.val * ((y⁻¹).val * m.1 * h.val) * (h⁻¹).val = m.1
    calc y.val * ((y⁻¹).val * m.1 * h.val) * (h⁻¹).val
        = (y.val * (y⁻¹).val) * m.1 * (h.val * (h⁻¹).val) := by simp only [Matrix.mul_assoc]
      _ = m.1 := by rw [hy, hh, Matrix.one_mul, Matrix.mul_one]
  right_inv m := by
    apply Subtype.ext
    have hy : (y⁻¹).val * y.val = 1 := Units.inv_mul y
    have hh : (h⁻¹).val * h.val = 1 := Units.inv_mul h
    change (y⁻¹).val * (y.val * m.1 * (h⁻¹).val) * h.val = m.1
    calc (y⁻¹).val * (y.val * m.1 * (h⁻¹).val) * h.val
        = ((y⁻¹).val * y.val) * m.1 * ((h⁻¹).val * h.val) := by simp only [Matrix.mul_assoc]
      _ = m.1 := by rw [hy, hh, Matrix.one_mul, Matrix.mul_one]
  continuous_toFun := by
    refine Matrix.SpecialLinearGroup.isClosedEmbedding_val.isInducing.continuous_iff.2 ?_
    exact (continuous_const.matrix_mul Matrix.SpecialLinearGroup.isClosedEmbedding_val.continuous).matrix_mul continuous_const
  continuous_invFun := by
    refine Matrix.SpecialLinearGroup.isClosedEmbedding_val.isInducing.continuous_iff.2 ?_
    exact (continuous_const.matrix_mul Matrix.SpecialLinearGroup.isClosedEmbedding_val.continuous).matrix_mul continuous_const

private noncomputable def cj (w : GLv v) : SL v →* SL v where
  toFun := tw w w rfl
  map_one' := by
    apply Subtype.ext
    have hw : (w⁻¹).val * w.val = 1 := Units.inv_mul w
    change (w⁻¹).val * (1 : M2 v) * w.val = 1
    rw [Matrix.mul_one, hw]
  map_mul' m n := by
    apply Subtype.ext
    have hw : w.val * (w⁻¹).val = 1 := Units.mul_inv w
    change (w⁻¹).val * (m.1 * n.1) * w.val = ((w⁻¹).val * m.1 * w.val) * ((w⁻¹).val * n.1 * w.val)
    calc (w⁻¹).val * (m.1 * n.1) * w.val
        = (w⁻¹).val * m.1 * (1 : M2 v) * n.1 * w.val := by
          rw [Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = ((w⁻¹).val * m.1 * w.val) * ((w⁻¹).val * n.1 * w.val) := by
          rw [← hw]; simp only [Matrix.mul_assoc]

private lemma sb_comp {X : Type} [TopologicalSpace X] (e : X ≃ₜ X) {b : X → ℂ} (hb : b ∈ SB X) :
    b ∘ e ∈ SB X :=
  ⟨hb.1.comp_continuous e.continuous, hb.2.comp_homeomorph e⟩

private lemma ind_mem {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    {U : Subgroup G} (hUo : IsOpen (U : Set G)) (hUc : IsCompact (U : Set G)) : ind U ∈ SB G := by
  refine ⟨(IsLocallyConstant.iff_exists_open _).2 fun x => ?_,
    HasCompactSupport.intro hUc fun x hx => Set.indicator_of_notMem hx _⟩
  by_cases hx : x ∈ (U : Set G)
  · exact ⟨U, hUo, hx, fun y hy => by
      simp only [ind]; rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]⟩
  · exact ⟨(U : Set G)ᶜ, (U.isClosed_of_isOpen hUo).isOpen_compl, hx, fun y hy => by
      simp only [ind]; rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩

private lemma one_term {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GLv v) V)
    (β : V →ₗ[ℂ] SB (SL v) →ₗ[ℂ] ℂ)
    (hβ : ∀ (g : SL v) f (a a' : SB (SL v)), (∀ m, a'.1 m = a.1 (m * g)) →
      β (ρ (Matrix.SpecialLinearGroup.toGL g) f) a' = β f a)
    (I : SB (SL v) →ₗ[ℂ] ℂ) (hI : InvI I) (Λ : V →ₗ[ℂ] ℂ)
    (hΛ : ∀ f (U : Subgroup (SL v)) (a : SB (SL v)), IsOpen (U : Set (SL v)) → a.1 = ind U →
      (∀ g ∈ U, ρ (Matrix.SpecialLinearGroup.toGL g) f = f) → β f a = I a * Λ f)
    (U : Subgroup (SL v)) (hUo : IsOpen (U : Set (SL v))) (a0 : SB (SL v)) (ha0 : a0.1 = ind U)
    (f : V) (hfix : ∀ u ∈ U, ρ (Matrix.SpecialLinearGroup.toGL u) f = f)
    (w d : GLv v) (e : (w.val).det = (d.val).det) (b : SB (SL v))
    (hb : ∀ m, b.1 m = ind U (tw w d e m)) :
    β (ρ d f) b = I a0 * Λ (ρ w f) := by
  have hdi : (d⁻¹).val * d.val = 1 := Units.inv_mul d
  have hwi : w.val * (w⁻¹).val = 1 := Units.mul_inv w
  let g' : SL v := ⟨w.val * (d⁻¹).val, by rw [Matrix.det_mul, e, det_mul_inv]⟩
  have hg' : Matrix.SpecialLinearGroup.toGL g' * d = w := by
    apply Units.ext
    change w.val * (d⁻¹).val * d.val = w.val
    rw [Matrix.mul_assoc, hdi, Matrix.mul_one]
  let Uc : Subgroup (SL v) := U.comap (cj w)
  have hUco : IsOpen (Uc : Set (SL v)) := hUo.preimage (tw w w rfl).continuous
  have hU0 : ind U ∈ SB (SL v) := ha0 ▸ a0.2
  let a1 : SB (SL v) := ⟨ind U ∘ (tw w w rfl), sb_comp _ hU0⟩
  have h1 : a1.1 = ind Uc := by
    funext m
    change ind U (tw w w rfl m) = ind Uc m
    unfold ind
    by_cases h : tw w w rfl m ∈ U
    · rw [Set.indicator_of_mem (show _ ∈ (U : Set (SL v)) from h),
        Set.indicator_of_mem (show m ∈ (Uc : Set (SL v)) from h)]
    · rw [Set.indicator_of_notMem (show _ ∉ (U : Set (SL v)) from h),
        Set.indicator_of_notMem (show m ∉ (Uc : Set (SL v)) from h)]
  have h2 : β (ρ (Matrix.SpecialLinearGroup.toGL g') (ρ d f)) a1 = β (ρ d f) b :=
    hβ g' (ρ d f) b a1 fun m => by
      rw [hb]
      change ind U (tw w w rfl m) = ind U (tw w d e (m * g'))
      congr 1
      apply Subtype.ext
      change (w⁻¹).val * m.1 * w.val = (w⁻¹).val * (m.1 * (w.val * (d⁻¹).val)) * d.val
      simp only [Matrix.mul_assoc]
      rw [hdi, Matrix.mul_one]
  have h3 : ρ (Matrix.SpecialLinearGroup.toGL g') (ρ d f) = ρ w f := by
    rw [← Module.End.mul_apply, ← map_mul, hg']
  have h4 : ∀ u ∈ Uc, ρ (Matrix.SpecialLinearGroup.toGL u) (ρ w f) = ρ w f := by
    intro u hu
    have hw : Matrix.SpecialLinearGroup.toGL u * w = w * Matrix.SpecialLinearGroup.toGL (tw w w rfl u) := by
      apply Units.ext
      change u.1 * w.val = w.val * ((w⁻¹).val * u.1 * w.val)
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hwi, Matrix.one_mul]
    have h5 : ρ (Matrix.SpecialLinearGroup.toGL (tw w w rfl u)) f = f := hfix _ hu
    calc ρ (Matrix.SpecialLinearGroup.toGL u) (ρ w f)
        = ρ (Matrix.SpecialLinearGroup.toGL u * w) f := by rw [map_mul, Module.End.mul_apply]
      _ = ρ w (ρ (Matrix.SpecialLinearGroup.toGL (tw w w rfl u)) f) := by
          rw [hw, map_mul, Module.End.mul_apply]
      _ = ρ w f := by rw [h5]
  have h6 : I a1 = I a0 := hI.conj w a0 a1 fun m m' h => by
    have : m' = tw w w rfl m := Subtype.ext h
    rw [this, ha0]
    rfl
  rw [← h2, h3, hΛ (ρ w f) Uc a1 hUco h1 h4, h6]

end SlopeTestRemainingChoices

theorem UpperTheory.ConvolutionTheory.R2.I.absS :
    ∀ (F : Type) [Field F] [NumberField F] (v : P F) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GLv v) V), (∀ f, IsOpen {g | ρ g f = f}) →
      ∀ β : V →ₗ[ℂ] SB (SL v) →ₗ[ℂ] ℂ,
      (∀ (g : SL v) f (a a' : SB (SL v)), (∀ m, a'.1 m = a.1 (m * g)) → β (ρ (Matrix.SpecialLinearGroup.toGL g) f) a' = β f a) →
      ∀ f (a : SB (SL v)) (aa : GLv v → SB (SL v)),
        (∀ x (m m' : SL v), m'.1 = (x⁻¹).val * m.1 * (dd x).val → (aa x).1 m = a.1 m') → (fun x => β (ρ (dd x) f) (aa x)) ∈ MC ρ := by
  intro F _ _ v V _ _ ρ hsm β hβ f a aa haa
  obtain ⟨I, hI⟩ := UpperTheory.ConvolutionTheory.R2.I.invI F v
  obtain ⟨Λ, hΛ⟩ := UpperTheory.ConvolutionTheory.R2.I.lamEx F v V ρ hsm I hI β hβ
  have hN : (Matrix.SpecialLinearGroup.toGL : SL v → GLv v) ⁻¹' {g | ρ g f = f} ∈ 𝓝 (1 : SL v) :=
    ((hsm f).preimage Matrix.SpecialLinearGroup.continuous_toGL).mem_nhds (by simp)
  obtain ⟨U, s, c, hUo, hUc, hUN, hsum⟩ :=
    UpperTheory.ConvolutionTheory.R2.I.cosetSpan (SL v) (UpperTheory.ConvolutionTheory.R2.I.lgrp F v).1 a.1 a.2 _ hN
  let a0 : SB (SL v) := ⟨ind U, ind_mem hUo hUc⟩
  have hfix : ∀ u ∈ U, ρ (Matrix.SpecialLinearGroup.toGL u) f = f := fun u hu => hUN hu
  have hdet0 : ∀ x : GLv v, (x.val).det = ((dd x).val).det := by
    intro x
    change _ = (!![(((1 : (Kv v)ˣ)) : Kv v), 0; 0, ((Matrix.GeneralLinearGroup.det x : (Kv v)ˣ) : Kv v)]).det
    simp [Matrix.det_fin_two_of]
  have hdet : ∀ (x : GLv v) (g : SL v),
      ((x * Matrix.SpecialLinearGroup.toGL g).val).det = ((dd x).val).det := by
    intro x g
    rw [← hdet0 x, Units.val_mul, Matrix.det_mul]
    have : ((Matrix.SpecialLinearGroup.toGL g).val).det = 1 := g.2
    rw [this, mul_one]
  have hval : ∀ x, β (ρ (dd x) f) (aa x) =
      ∑ g ∈ s, (c g * I a0) * Λ (ρ x (ρ (Matrix.SpecialLinearGroup.toGL g) f)) := by
    intro x
    let B : SL v → SB (SL v) := fun g =>
      ⟨ind U ∘ tw (x * Matrix.SpecialLinearGroup.toGL g) (dd x) (hdet x g), sb_comp _ a0.2⟩
    have hs : aa x = ∑ g ∈ s, c g • B g := by
      apply Subtype.ext
      funext m
      rw [haa x m (tw x (dd x) (hdet0 x) m) rfl, hsum]
      simp only [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply, Submodule.coe_smul,
        Pi.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun g _ => ?_
      congr 1
      change ind U _ = ind U (tw (x * Matrix.SpecialLinearGroup.toGL g) (dd x) (hdet x g) m)
      congr 1
      apply Subtype.ext
      have hinv : ((x * Matrix.SpecialLinearGroup.toGL g)⁻¹).val = (g⁻¹).1 * (x⁻¹).val := by
        rw [_root_.mul_inv_rev, ← map_inv, Units.val_mul]
        rfl
      change (g⁻¹).1 * ((x⁻¹).val * m.1 * (dd x).val) =
        ((x * Matrix.SpecialLinearGroup.toGL g)⁻¹).val * m.1 * (dd x).val
      rw [hinv]
      simp only [Matrix.mul_assoc]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hs, map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [map_smul, smul_eq_mul,
      one_term ρ β hβ I hI Λ hΛ U hUo a0 rfl f hfix (x * Matrix.SpecialLinearGroup.toGL g) (dd x)
        (hdet x g) (B g) (fun m => rfl), map_mul, Module.End.mul_apply, mul_assoc]
  have hfun : (fun x => β (ρ (dd x) f) (aa x)) =
      ∑ g ∈ s, (c g * I a0) • (fun x => Λ (ρ x (ρ (Matrix.SpecialLinearGroup.toGL g) f))) := by
    funext x
    rw [hval x]
    simp [Finset.sum_apply]
  rw [hfun]
  exact Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Λ, _, rfl⟩)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.ClosedEmbeddingVal
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

private theorem trace_compactOpen {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {i : Y → X}
    (hi : IsClosedEmbedding i)
    (hb : ∀ x, ∀ N ∈ 𝓝 x, ∃ O : Set X, IsOpen O ∧ IsCompact O ∧ x ∈ O ∧ O ⊆ N)
    {C : Set Y} (hCo : IsOpen C) (hCc : IsCompact C) :
    ∃ O : Set X, IsOpen O ∧ IsCompact O ∧ i ⁻¹' O = C := by
  have hcl : IsClosed (i '' Cᶜ) := hi.isClosedMap _ hCo.isClosed_compl
  have hloc : ∀ y ∈ C, ∃ O : Set X, IsOpen O ∧ IsCompact O ∧ i y ∈ O ∧ O ⊆ (i '' Cᶜ)ᶜ := by
    intro y hy
    refine hb (i y) _ (hcl.isOpen_compl.mem_nhds ?_)
    rintro ⟨y', hy', e⟩
    exact hy' (hi.injective e ▸ hy)
  choose! O hOo hOc hOy hON using hloc
  obtain ⟨t, ht, hcov⟩ := hCc.elim_nhds_subcover (fun y => i ⁻¹' O y)
    (fun y hy => ((hOo y hy).preimage hi.continuous).mem_nhds (hOy y hy))
  refine ⟨⋃ y ∈ t, O y, isOpen_biUnion fun y hy => hOo y (ht y hy),
    t.isCompact_biUnion fun y hy => hOc y (ht y hy), ?_⟩
  ext y
  simp only [Set.mem_preimage, Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨z, hz, hy⟩
    by_contra hc
    exact hON z (ht z hz) hy ⟨y, hc, rfl⟩
  · intro hy
    simpa using hcov hy

private theorem indicator_mem_SB {X : Type} [TopologicalSpace X] [T2Space X] {O : Set X}
    (hO : IsOpen O) (hc : IsCompact O) : O.indicator (fun _ => (1 : ℂ)) ∈ SB X := by
  refine ⟨?_, HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _⟩
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  by_cases hx : x ∈ O
  · exact ⟨O, hO, hx, fun y hy => by rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]⟩
  · exact ⟨Oᶜ, hc.isClosed.isOpen_compl, hx, fun y hy => by
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩

private theorem extend_SB {X Y : Type} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] {i : Y → X}
    (hi : IsClosedEmbedding i)
    (hb : ∀ x, ∀ N ∈ 𝓝 x, ∃ O : Set X, IsOpen O ∧ IsCompact O ∧ x ∈ O ∧ O ⊆ N)
    (a : Y → ℂ) (ha : a ∈ SB Y) : ∃ b ∈ SB X, ∀ y, b (i y) = a y := by
  obtain ⟨hlc, hcs⟩ := ha
  have hK : IsCompact (tsupport a) := hcs
  haveI : CompactSpace (tsupport a) := isCompact_iff_compactSpace.mp hK
  have hfin : (Set.range ((tsupport a).restrict a)).Finite :=
    (hlc.comp_continuous continuous_subtype_val).range_finite
  have hfib : ∀ c : ℂ, c ≠ 0 → ∃ O : Set X, IsOpen O ∧ IsCompact O ∧ i ⁻¹' O = a ⁻¹' {c} := by
    intro c hc
    refine trace_compactOpen hi hb (hlc.isOpen_fiber c) (hK.of_isClosed_subset (hlc.isClosed_fiber c) ?_)
    intro y hy
    refine subset_tsupport _ ?_
    rw [Function.mem_support, show a y = c from hy]
    exact hc
  choose! O hOo hOc hOt using hfib
  let S : Finset ℂ := hfin.toFinset.erase 0
  refine ⟨fun x => ∑ c ∈ S, c * (O c).indicator (fun _ => (1 : ℂ)) x, ?_, ?_⟩
  · have : (fun x => ∑ c ∈ S, c * (O c).indicator (fun _ => (1 : ℂ)) x) =
        ∑ c ∈ S, c • (O c).indicator (fun _ => (1 : ℂ)) := by
      ext x
      simp [Finset.sum_apply]
    rw [this]
    refine Submodule.sum_mem _ fun c hc => Submodule.smul_mem _ _ ?_
    have hc0 : c ≠ 0 := (Finset.mem_erase.mp hc).1
    exact indicator_mem_SB (hOo c hc0) (hOc c hc0)
  · intro y
    have hterm : ∀ c ∈ S, c * (O c).indicator (fun _ => (1 : ℂ)) (i y) = if c = a y then c else 0 := by
      intro c hc
      have hc0 : c ≠ 0 := (Finset.mem_erase.mp hc).1
      have hm : i y ∈ O c ↔ a y = c := by
        have := Set.ext_iff.mp (hOt c hc0) y
        simpa using this
      by_cases h : c = a y
      · rw [Set.indicator_of_mem (hm.mpr h.symm), if_pos h, mul_one]
      · have : i y ∉ O c := fun h' => h (hm.mp h').symm
        rw [Set.indicator_of_notMem this, if_neg h, mul_zero]
    change ∑ c ∈ S, c * (O c).indicator (fun _ => (1 : ℂ)) (i y) = a y
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' S (a y) (fun c => c)]
    split_ifs with h
    · rfl
    · have h0 : a y = 0 := by
        by_contra hne
        exact h (Finset.mem_erase.mpr ⟨hne, hfin.mem_toFinset.mpr ⟨⟨y, subset_tsupport _ hne⟩, rfl⟩⟩)
      exact h0.symm

private theorem closedEmbedding_val (F : Type) [Field F] [NumberField F] (v : P F) :
    IsClosedEmbedding (Subtype.val : SL v → M2 v) := by
  have h : IsClosed {m : M2 v | m.det = 1} :=
    isClosed_singleton.preimage (show Continuous (fun m : M2 v => m.det) from continuous_id.matrix_det)
  exact h.isClosedEmbedding_subtypeVal

private theorem compactOpen_basis (F : Type) [Field F] [NumberField F] (v : P F) (x : M2 v) (N : Set (M2 v))
    (hN : N ∈ 𝓝 x) : ∃ O : Set (M2 v), IsOpen O ∧ IsCompact O ∧ x ∈ O ∧ O ⊆ N := by
  have h0 : (fun y : M2 v => x + y) ⁻¹' N ∈ 𝓝 (0 : M2 v) :=
    (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds (by simpa using hN)
  obtain ⟨U, hUo, hUc, hUN⟩ := (UpperTheory.ConvolutionTheory.R2.I.lgrp F v).2
    ((fun y : Multiplicative (M2 v) => Multiplicative.toAdd y) ⁻¹' ((fun y : M2 v => x + y) ⁻¹' N))
    (by
      have : Tendsto (fun y : Multiplicative (M2 v) => Multiplicative.toAdd y) (𝓝 1) (𝓝 (0 : M2 v)) :=
        continuous_toAdd.tendsto _
      exact this h0)
  let e : Multiplicative (M2 v) → M2 v := fun y => x + Multiplicative.toAdd y
  have he : IsOpenEmbedding e := (Homeomorph.addLeft x).isOpenEmbedding
  refine ⟨e '' U, he.isOpenMap _ hUo, hUc.image he.continuous, ⟨1, U.one_mem, by simp [e]⟩, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  exact hUN hy

theorem UpperTheory.ConvolutionTheory.R2.I.ext :
    ∀ (F : Type) [Field F] [NumberField F] (v : P F) (a : SB (SL v)), ∃ b : SB (M2 v), ∀ m : SL v, b.1 m.1 = a.1 m := by
  intro F _ _ v a
  obtain ⟨b, hb, h⟩ := extend_SB (closedEmbedding_val F v) (compactOpen_basis F v) a.1 a.2
  exact ⟨⟨b, hb⟩, h⟩
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

private theorem isClosedEmbedding_slVal {F : Type} [Field F] [NumberField F] (v : P F) :
    IsClosedEmbedding (fun m : SL v => (m.1 : M2 v)) := by
  have hc : IsClosed {A : M2 v | A.det = 1} :=
    isClosed_eq (Continuous.matrix_det continuous_id) continuous_const
  exact hc.isClosedEmbedding_subtypeVal

private noncomputable def resL {F : Type} [Field F] [NumberField F] (v : P F) :
    SB (M2 v) →ₗ[ℂ] SB (SL v) where
  toFun b := ⟨fun m => b.1 m.1,
    b.2.1.comp_continuous (isClosedEmbedding_slVal v).continuous,
    b.2.2.comp_isClosedEmbedding (isClosedEmbedding_slVal v)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable def trM {F : Type} [Field F] [NumberField F] {v : P F} (g : SL v)
    (b : SB (M2 v)) : SB (M2 v) :=
  let e : M2 v ≃ₜ M2 v :=
    { toFun := fun m => m * g.1
      invFun := fun m => m * (g⁻¹ : SL v).1
      left_inv := fun m => by
        show m * g.1 * (g⁻¹ : SL v).1 = m
        rw [mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
          Matrix.SpecialLinearGroup.coe_one, mul_one]
      right_inv := fun m => by
        show m * (g⁻¹ : SL v).1 * g.1 = m
        rw [mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
          Matrix.SpecialLinearGroup.coe_one, mul_one]
      continuous_toFun := continuous_id.matrix_mul continuous_const
      continuous_invFun := continuous_id.matrix_mul continuous_const }
  ⟨fun m => b.1 (e m), b.2.1.comp_continuous e.continuous, b.2.2.comp_homeomorph e⟩

theorem UpperTheory.ConvolutionTheory.R2.I.absM :
    ∀ (F : Type) [Field F] [NumberField F] (v : P F) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GLv v) V), (∀ f, IsOpen {g | ρ g f = f}) →
      ∀ β : V →ₗ[ℂ] SB (M2 v) →ₗ[ℂ] ℂ,
      (∀ (g : SL v) f (a a' : SB (M2 v)), (∀ m, a'.1 m = a.1 (m * g.1)) → β (ρ (Matrix.SpecialLinearGroup.toGL g) f) a' = β f a) →
      (∀ f (s : Kv v) (a a' : SB (M2 v)), (∀ m, a'.1 m = ψl v (-(s * m.det)) * a.1 m) → β f a' = ψl v (-s) * β f a) →
      ∀ f (a : SB (M2 v)) (aa : GLv v → SB (M2 v)),
        (∀ x m, (aa x).1 m = a.1 ((x⁻¹).val * m * (dd x).val)) → (fun x => β (ρ (dd x) f) (aa x)) ∈ MC ρ := by
  intro F _ _ v V _ _ ρ hρ β hinv hψ f a aa haa
  have hsurj : Function.Surjective (resL v) := by
    intro c
    obtain ⟨b, hb⟩ := UpperTheory.ConvolutionTheory.R2.I.ext F v c
    exact ⟨b, Subtype.ext (funext hb)⟩
  obtain ⟨s, hs⟩ := (resL v).exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hsurj)
  have hs' : ∀ c, resL v (s c) = c := fun c => LinearMap.congr_fun hs c
  have hdep : ∀ (h : V) (b : SB (M2 v)), β h (s (resL v b)) = β h b := by
    intro h b
    have hz : β h (s (resL v b) - b) = 0 := by
      refine UpperTheory.ConvolutionTheory.R2.I.loc F v (β h) (fun t a a' ha => hψ h t a a' ha) _ ?_
      intro m hm
      have h1 : (s (resL v b)).1 m = b.1 m :=
        congrArg (fun c : SB (SL v) => c.1 ⟨m, hm⟩) (hs' (resL v b))
      show (s (resL v b)).1 m - b.1 m = 0
      rw [h1, sub_self]
    rw [map_sub, sub_eq_zero] at hz
    exact hz
  have key := UpperTheory.ConvolutionTheory.R2.I.absS F v V ρ hρ (β.compl₂ s) ?_ f (resL v a)
    (fun x => resL v (aa x)) ?_
  · have hfun : (fun x => β (ρ (dd x) f) (aa x)) =
        fun x => (β.compl₂ s) (ρ (dd x) f) (resL v (aa x)) := by
      funext x
      rw [LinearMap.compl₂_apply, hdep]
    rw [hfun]
    exact key
  · intro g h c c' hc
    rw [LinearMap.compl₂_apply, LinearMap.compl₂_apply]
    have e : resL v (trM g (s c)) = c' := by
      apply Subtype.ext
      funext m
      have h1 : (s c).1 (m * g).1 = c.1 (m * g) :=
        congrArg (fun d : SB (SL v) => d.1 (m * g)) (hs' c)
      rw [hc m, ← h1]
      rfl
    rw [← e, hdep]
    exact hinv g h (s c) (trM g (s c)) (fun m => rfl)
  · intro x m m' hm
    show (aa x).1 m.1 = a.1 m'.1
    rw [haa, hm]
