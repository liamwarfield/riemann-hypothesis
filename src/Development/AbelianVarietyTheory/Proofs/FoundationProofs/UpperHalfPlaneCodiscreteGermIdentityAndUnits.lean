module

public import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharInertiaSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivialIff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiagMod

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneCodiscreteGermIdentityAndUnits
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneCodiscreteGermIdentityAndUnits
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
open Filter Topology

namespace GlobalTheory.FN

theorem isOpen_Hs : IsOpen Hs := isOpen_lt continuous_const Complex.continuous_im

theorem isPreconnected_Hs : IsPreconnected Hs := (convex_halfSpace_im_gt 0).isPreconnected

theorem codiscreteWithin_Hs_neBot : (Filter.codiscreteWithin Hs).NeBot := by
  rw [Filter.neBot_iff]
  intro h
  have h0 : (∅ : Set ℂ) ∈ Filter.codiscreteWithin Hs := h ▸ Filter.mem_bot
  rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE] at h0
  have hI : Complex.I ∈ Hs := by show (0 : ℝ) < Complex.I.im; simp
  have h1 := h0 Complex.I hI
  rw [Set.empty_union] at h1
  have h2 : Hs ∈ 𝓝[≠] Complex.I := mem_nhdsWithin_of_mem_nhds (isOpen_Hs.mem_nhds hI)
  have h3 : (∅ : Set ℂ) ∈ 𝓝[≠] Complex.I := by
    have := Filter.inter_mem h2 h1
    simpa using this
  exact (Filter.empty_mem_iff_bot.mp h3 ▸ (inferInstance : (𝓝[≠] Complex.I).NeBot)).ne rfl

theorem eqOn_zero_of_germ_eq_zero {a : ℂ → ℂ} (ha : DifferentiableOn ℂ a Hs) (h0 : (a : Mero) = 0) :
    ∀ z ∈ Hs, a z = 0 := by
  haveI := codiscreteWithin_Hs_neBot
  have han : AnalyticOnNhd ℂ a Hs := ha.analyticOnNhd isOpen_Hs
  rcases han.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_Hs with h | h
  · exact fun z hz => h hz
  · exfalso
    have he : a =ᶠ[Filter.codiscreteWithin Hs] (0 : ℂ → ℂ) := Filter.Germ.coe_eq.mp h0
    obtain ⟨z, hz1, hz2⟩ := (h.and he).exists
    exact hz1 hz2

theorem germ_main : Nontrivial Mero ∧ (∀ a b : ℂ → ℂ, DifferentiableOn ℂ a Hs → DifferentiableOn ℂ b Hs → (a : Mero) = (b : Mero) → ∀ z ∈ Hs, a z = b z) ∧ ∀ a : ℂ → ℂ, DifferentiableOn ℂ a Hs → (a : Mero) ≠ 0 → (∀ᶠ z in Filter.codiscreteWithin Hs, a z ≠ 0) ∧ IsUnit (a : Mero) := by
  haveI := codiscreteWithin_Hs_neBot
  refine ⟨inferInstance, ?_, ?_⟩
  · intro a b ha hb hab z hz
    have h0 : ((a - b : ℂ → ℂ) : Mero) = 0 := by
      rw [Filter.Germ.coe_sub, hab, sub_self]
    have := eqOn_zero_of_germ_eq_zero (ha.sub hb) h0 z hz
    simpa [sub_eq_zero] using this
  · intro a ha hne
    have han : AnalyticOnNhd ℂ a Hs := ha.analyticOnNhd isOpen_Hs
    have hev : ∀ᶠ z in Filter.codiscreteWithin Hs, a z ≠ 0 := by
      rcases han.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_Hs with h | h
      · exfalso
        apply hne
        rw [← Filter.Germ.coe_zero, Filter.Germ.coe_eq]
        filter_upwards [Filter.self_mem_codiscreteWithin Hs] with z hz
        exact h hz
      · exact h
    refine ⟨hev, ?_⟩
    refine ⟨⟨(a : Mero), ((fun z => (a z)⁻¹ : ℂ → ℂ) : Mero), ?_, ?_⟩, rfl⟩
    · rw [← Filter.Germ.coe_mul, ← Filter.Germ.coe_one, Filter.Germ.coe_eq]
      filter_upwards [hev] with z hz
      simp [hz]
    · rw [← Filter.Germ.coe_mul, ← Filter.Germ.coe_one, Filter.Germ.coe_eq]
      filter_upwards [hev] with z hz
      simp [hz]

end GlobalTheory.FN
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneCodiscreteGermIdentityAndUnitsStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.upperHalfPlaneCodiscreteGerm_identity_and_units : Nontrivial Mero ∧ (∀ a b : ℂ → ℂ, DifferentiableOn ℂ a Hs → DifferentiableOn ℂ b Hs → (a : Mero) = (b : Mero) → ∀ z ∈ Hs, a z = b z) ∧ ∀ a : ℂ → ℂ, DifferentiableOn ℂ a Hs → (a : Mero) ≠ 0 → (∀ᶠ z in Filter.codiscreteWithin Hs, a z ≠ 0) ∧ IsUnit (a : Mero) := by
  first | exact @GlobalTheory.FN.germ_main | exact GlobalTheory.FN.germ_main | (intros; apply GlobalTheory.FN.germ_main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemTranslationInvariantSubfieldIffExponents
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemTranslationInvariantSubfieldIffExponents
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

noncomputable section

namespace GlobalTheory.Glue.KTExp

theorem exists_prim_root_of_isAlgClosed (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] (n : ℕ) (hn : 0 < n) :
    ∃ ζ : Ω, IsPrimitiveRoot ζ n := by
  haveI : NeZero (n : Ω) := ⟨by exact_mod_cast hn.ne'⟩
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic n Ω)
    (by rw [Polynomial.degree_cyclotomic]; exact_mod_cast (Nat.totient_pos.2 hn).ne')
  exact ⟨ζ, (Polynomial.isRoot_cyclotomic_iff).1 hζ⟩

theorem map_eOm {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ)
    (x : ℚ) : ε (eOm ε x) = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hε : Function.Injective ε := ε.injective
  unfold eOm
  apply Function.invFun_eq
  obtain ⟨ζ, hζ⟩ := exists_prim_root_of_isAlgClosed Ω x.den x.den_pos
  have hζ' : IsPrimitiveRoot (ε ζ) x.den := hζ.map_of_injective hε
  haveI : NeZero x.den := ⟨x.den_nz⟩
  have hpow : (Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))) ^ x.den = 1 := by
    rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
    refine ⟨x.num, ?_⟩
    have hx : (x : ℂ) * x.den = x.num := by exact_mod_cast Rat.mul_den_eq_num x
    calc (x.den : ℂ) * (2 * Real.pi * Complex.I * (x : ℂ)) = ((x : ℂ) * x.den) * (2 * Real.pi * Complex.I) := by ring
      _ = _ := by rw [hx]
  obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_pow_eq_one hpow
  exact ⟨ζ ^ i, by rw [map_pow, hi]⟩

theorem eOm_eq_one_iff {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (x : ℚ) :
    eOm ε x = 1 ↔ x.den = 1 := by
  have hε : Function.Injective ε := ε.injective
  rw [← hε.eq_iff, map_one, map_eOm, Complex.exp_eq_one_iff]
  have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  constructor
  · rintro ⟨n, hn⟩
    have h3 : ((x : ℚ) : ℂ) = ((n : ℚ) : ℂ) := by
      apply mul_left_cancel₀ hne
      push_cast
      rw [hn]; ring
    have : x = n := by exact_mod_cast h3
    rw [this]; rfl
  · intro h
    refine ⟨x.num, ?_⟩
    have : x = (x.num : ℚ) := by
      exact ((Rat.den_eq_one_iff x).1 h).symm
    rw [this]; push_cast; simp; ring

theorem ent_T_pow (L : ℕ) :
    ent (ofSL (ModularGroup.T ^ L)) 0 0 = 1 ∧ ent (ofSL (ModularGroup.T ^ L)) 0 1 = L ∧
    ent (ofSL (ModularGroup.T ^ L)) 1 0 = 0 ∧ ent (ofSL (ModularGroup.T ^ L)) 1 1 = 1 := by
  have h : ((ModularGroup.T ^ L : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, (L : ℤ); 0, 1] := by
    rw [← zpow_natCast, ModularGroup.coe_T_zpow]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · change (((ModularGroup.T ^ L : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℚ)) _ _ = _
    rw [h]; simp

end GlobalTheory.Glue.KTExp

namespace GlobalTheory.Glue.KTExp

theorem mem_KT_iff : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), ∀ (L : ℕ), 0 < L → ∀ f : X.K, (f ∈ KT X L ↔ ∀ r : ℚ, (X.exp f).coeff r ≠ 0 → (r * L).den = 1) := by
  intro Ω _ _ _ ε X L _ f
  obtain ⟨h00, h01, h10, h11⟩ := ent_T_pow L
  have key : ∀ r : ℚ, (X.exp (X.sl (ofSL (ModularGroup.T ^ L)) f)).coeff r = eOm ε (r * L) * (X.exp f).coeff r := by
    intro r
    have := X.exp_upper (ofSL (ModularGroup.T ^ L)) h10 f r
    rwa [h00, h01, h11, mul_one, div_one, div_one] at this
  have hmem : f ∈ KT X L ↔ X.sl (ofSL (ModularGroup.T ^ L)) f = f := by
    unfold KT
    rw [RingHom.mem_eqLocusField]
    rfl
  rw [hmem]
  constructor
  · intro h r hr
    have k := key r
    rw [h] at k
    have h1 : eOm ε (r * L) = 1 := by
      have : (1 - eOm ε (r * L)) * (X.exp f).coeff r = 0 := by rw [sub_mul, one_mul, ← k, sub_self]
      exact (sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hr)).symm
    exact (eOm_eq_one_iff ε _).1 h1
  · intro h
    apply (X.exp : X.K →+* HahnSeries ℚ Ω).injective
    ext r
    change (X.exp (X.sl (ofSL (ModularGroup.T ^ L)) f)).coeff r = (X.exp f).coeff r
    rw [key r]
    by_cases hr : (X.exp f).coeff r = 0
    · rw [hr, mul_zero]
    · rw [(eOm_eq_one_iff ε _).2 (h r hr), one_mul]

end GlobalTheory.Glue.KTExp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemTranslationInvariantSubfieldIffExponentsStatement
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_translationInvariantSubfield_iff_exponents : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), ∀ (L : ℕ), 0 < L → ∀ f : X.K, (f ∈ KT X L ↔ ∀ r : ℚ, (X.exp f).coeff r ≠ 0 → (r * L).den = 1) := by
  first | exact @GlobalTheory.Glue.KTExp.mem_KT_iff | exact GlobalTheory.Glue.KTExp.mem_KT_iff | (intros; apply GlobalTheory.Glue.KTExp.mem_KT_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlTwoPosRatMobiusUpperHalfPlaneProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlTwoPosRatMobiusUpperHalfPlaneProperties
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FNMob

theorem det_pos (g : GQ) : 0 < ent g 0 0 * ent g 1 1 - ent g 0 1 * ent g 1 0 := by
  have h := (Matrix.mem_glpos (g : GL (Fin 2) ℚ)).1 g.2
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two] at h
  simpa [ent] using h

theorem im_frac (a b c d : ℝ) (z : ℂ) :
    (((a : ℂ) * z + b) / ((c : ℂ) * z + d)).im = (a * d - b * c) * z.im / Complex.normSq ((c : ℂ) * z + d) := by
  rw [Complex.div_im]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem denom_ne (g : GQ) {z : ℂ} (hz : z ∈ Hs) : (ent g 1 0 : ℂ) * z + (ent g 1 1 : ℂ) ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  have hr := congrArg Complex.re h
  simp at hi hr
  have hz' : 0 < z.im := hz
  have hc : ent g 1 0 = 0 := by
    rcases hi with h1 | h1
    · exact_mod_cast h1
    · exact absurd h1 hz'.ne'
  rw [hc] at hr
  have hd : ent g 1 1 = 0 := by simpa using hr
  have := det_pos g
  rw [hc, hd] at this
  simp at this

theorem mob_mem (g : GQ) {z : ℂ} (hz : z ∈ Hs) : mob g z ∈ Hs := by
  have hne := denom_ne g hz
  have e : mob g z = ((((ent g 0 0 : ℝ)) : ℂ) * z + ((ent g 0 1 : ℝ) : ℂ)) /
      ((((ent g 1 0 : ℝ)) : ℂ) * z + ((ent g 1 1 : ℝ) : ℂ)) := by
    simp [mob]
  show 0 < (mob g z).im
  rw [e, im_frac]
  have hn : 0 < Complex.normSq ((((ent g 1 0 : ℝ)) : ℂ) * z + ((ent g 1 1 : ℝ) : ℂ)) := by
    rw [Complex.normSq_pos]; simpa using hne
  have hd : (0 : ℝ) < (ent g 0 0 : ℝ) * (ent g 1 1 : ℝ) - (ent g 0 1 : ℝ) * (ent g 1 0 : ℝ) := by
    exact_mod_cast det_pos g
  have hz' : 0 < z.im := hz
  positivity

theorem ent_mul (g h : GQ) (i j : Fin 2) : ent (g * h) i j = ent g i 0 * ent h 0 j + ent g i 1 * ent h 1 j := by
  simp [ent, Matrix.mul_apply, Fin.sum_univ_two]

theorem frac_comp (a b c d N D : ℂ) (hD : D ≠ 0) :
    (a * (N / D) + b) / (c * (N / D) + d) = (a * N + b * D) / (c * N + d * D) := by
  rw [show a * (N / D) + b = (a * N + b * D) / D by field_simp,
    show c * (N / D) + d = (c * N + d * D) / D by field_simp, div_div_div_cancel_right₀ hD]

theorem mob_mul (g h : GQ) {z : ℂ} (hz : z ∈ Hs) : mob (g * h) z = mob g (mob h z) := by
  have hne := denom_ne h hz
  simp only [mob, ent_mul]
  push_cast
  rw [frac_comp _ _ _ _ _ _ hne]
  congr 1 <;> ring

theorem mob_one (z : ℂ) : mob 1 z = z := by simp [mob, ent]

theorem mob_ofSL (γ : SL(2, ℤ)) (τ : ℍ) : mob (ofSL γ) τ = ((γ • τ : ℍ) : ℂ) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [mob, ent, ofSL]

theorem mob_diff (g : GQ) : DifferentiableOn ℂ (mob g) Hs := by
  intro z hz
  have hne := denom_ne g hz
  show DifferentiableWithinAt ℂ (fun z : ℂ => ((ent g 0 0 : ℂ) * z + (ent g 0 1 : ℂ)) /
    ((ent g 1 0 : ℂ) * z + (ent g 1 1 : ℂ))) Hs z
  have h1 : DifferentiableAt ℂ (fun z : ℂ => (ent g 0 0 : ℂ) * z + (ent g 0 1 : ℂ)) z := by fun_prop
  have h2 : DifferentiableAt ℂ (fun z : ℂ => (ent g 1 0 : ℂ) * z + (ent g 1 1 : ℂ)) z := by fun_prop
  exact (h1.div h2 hne).differentiableWithinAt

theorem mob_upper (g : GQ) (hc : ent g 1 0 = 0) : 0 < ent g 0 0 / ent g 1 1 ∧
    ∀ z : ℂ, mob g z = ((ent g 0 0 / ent g 1 1 : ℚ) : ℂ) * z + ((ent g 0 1 / ent g 1 1 : ℚ) : ℂ) := by
  have hdet := det_pos g
  rw [hc, mul_zero, sub_zero] at hdet
  have hd : ent g 1 1 ≠ 0 := by rintro h; rw [h, mul_zero] at hdet; exact lt_irrefl _ hdet
  refine ⟨?_, fun z => ?_⟩
  · have : ent g 0 0 / ent g 1 1 = ent g 0 0 * ent g 1 1 / (ent g 1 1 * ent g 1 1) := by
      field_simp
    rw [this]; exact div_pos hdet (mul_self_pos.2 hd)
  · have hd' : (ent g 1 1 : ℂ) ≠ 0 := by exact_mod_cast hd
    simp only [mob, hc]
    push_cast
    simp only [zero_mul, zero_add]
    rw [add_div, mul_div_right_comm]

end GlobalTheory.FNMob

theorem GlobalTheory.FN.mob_props : (∀ (g : GQ) (z : ℂ), z ∈ Hs → mob g z ∈ Hs) ∧ (∀ (g h : GQ) (z : ℂ), z ∈ Hs → mob (g * h) z = mob g (mob h z)) ∧ (∀ z : ℂ, mob 1 z = z) ∧ (∀ (γ : SL(2, ℤ)) (τ : ℍ), mob (ofSL γ) τ = ((γ • τ : ℍ) : ℂ)) ∧ (∀ g : GQ, DifferentiableOn ℂ (mob g) Hs) ∧ ∀ g : GQ, ent g 1 0 = 0 → 0 < ent g 0 0 / ent g 1 1 ∧ ∀ z : ℂ, mob g z = ((ent g 0 0 / ent g 1 1 : ℚ) : ℂ) * z + ((ent g 0 1 / ent g 1 1 : ℚ) : ℂ) :=
  ⟨fun g _ hz => GlobalTheory.FNMob.mob_mem g hz, fun g h _ hz => GlobalTheory.FNMob.mob_mul g h hz, GlobalTheory.FNMob.mob_one,
    GlobalTheory.FNMob.mob_ofSL, GlobalTheory.FNMob.mob_diff, GlobalTheory.FNMob.mob_upper⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlTwoPosRatMobiusUpperHalfPlanePropertiesStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glTwoPosRatMobius_upperHalfPlane_properties : (∀ (g : GQ) (z : ℂ), z ∈ Hs → mob g z ∈ Hs) ∧ (∀ (g h : GQ) (z : ℂ), z ∈ Hs → mob (g * h) z = mob g (mob h z)) ∧ (∀ z : ℂ, mob 1 z = z) ∧ (∀ (γ : SL(2, ℤ)) (τ : ℍ), mob (ofSL γ) τ = ((γ • τ : ℍ) : ℂ)) ∧ (∀ g : GQ, DifferentiableOn ℂ (mob g) Hs) ∧ ∀ g : GQ, ent g 1 0 = 0 → 0 < ent g 0 0 / ent g 1 1 ∧ ∀ z : ℂ, mob g z = ((ent g 0 0 / ent g 1 1 : ℚ) : ℂ) * z + ((ent g 0 1 / ent g 1 1 : ℚ) : ℂ) := by
  first | exact @GlobalTheory.FN.mob_props | exact GlobalTheory.FN.mob_props | (intros; apply GlobalTheory.FN.mob_props <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexStabilizer
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.InertiaPowers

theorem cycMod_Ine_surjective (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω]
    [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω) (hA : A.valuation (l : Ω) < 1) (n : ℕ) :
    Function.Surjective ((cycMod ℚ Ω l n).comp (Ine (F := ℚ) A).subtype) := by
  intro u
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · haveI : Subsingleton (ZMod (l ^ 0)) := by rw [pow_zero]; infer_instance
    exact ⟨1, Subsingleton.elim _ _⟩
  haveI : Fact (1 < l ^ n) := ⟨Nat.one_lt_pow hn.ne' (Fact.out : l.Prime).one_lt⟩
  have hs : Function.Surjective (PadicInt.toZModPow n : ℤ_[l] →+* ZMod (l ^ n)) :=
    ZMod.ringHom_surjective _
  haveI := IsLocalHom.of_surjective _ hs
  obtain ⟨v, hv⟩ := IsLocalRing.surjective_units_map_of_local_ringHom _ hs this u
  obtain ⟨σ, hσ, hσv⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hA v
  refine ⟨⟨σ, hσ⟩, ?_⟩
  simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
  rw [cycMod, MonoidHom.comp_apply, hσv]
  exact hv

end GlobalTheory.InertiaPowers
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneGermRingHomAndRestrict
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneGermRingHomAndRestrict
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory

theorem FN.germ_ringHom_and_restrict : (∃ A : (ℍ → ℂ) →+* Mero, ∀ f, A f = germ f) ∧ (∀ f : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f ↔ DifferentiableOn ℂ (up f) Hs) ∧ (∀ a b : ℂ → ℂ, (∀ z ∈ Hs, a z = b z) → (a : Mero) = (b : Mero)) ∧ (∀ a : ℂ → ℂ, germ (fun τ : ℍ => a τ) = (a : Mero)) ∧ ∀ τ : ℍ, (τ : ℂ) ∈ Hs := by
  refine ⟨⟨(Filter.Germ.coeRingHom _).comp (Pi.ringHom fun z => Pi.evalRingHom (fun _ : ℍ => ℂ) (UpperHalfPlane.ofComplex z)), fun f => rfl⟩, fun f => ?_, ?_, ?_, fun τ => τ.2⟩
  · exact UpperHalfPlane.mdifferentiable_iff
  · intro a b h
    rw [Filter.Germ.coe_eq]
    filter_upwards [Filter.self_mem_codiscreteWithin Hs] with z hz using h z hz
  · intro a
    unfold germ up
    rw [Filter.Germ.coe_eq]
    filter_upwards [Filter.self_mem_codiscreteWithin Hs] with z hz
    simp [UpperHalfPlane.ofComplex_apply_of_im_pos hz]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneGermRingHomAndRestrictStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.upperHalfPlane_germ_ringHom_and_restrict : (∃ A : (ℍ → ℂ) →+* Mero, ∀ f, A f = germ f) ∧ (∀ f : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f ↔ DifferentiableOn ℂ (up f) Hs) ∧ (∀ a b : ℂ → ℂ, (∀ z ∈ Hs, a z = b z) → (a : Mero) = (b : Mero)) ∧ (∀ a : ℂ → ℂ, germ (fun τ : ℍ => a τ) = (a : Mero)) ∧ ∀ τ : ℍ, (τ : ℂ) ∈ Hs := by
  first | exact @GlobalTheory.FN.germ_ringHom_and_restrict | exact GlobalTheory.FN.germ_ringHom_and_restrict | (intros; apply GlobalTheory.FN.germ_ringHom_and_restrict <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MdifferentiableOfHasSomeLevelOver
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MdifferentiableOfHasSomeLevelOver
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem dd_mdifferentiable : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => DD τ) :=
  (CuspForm.discriminant).holo'

theorem inR_mdifferentiable : ∀ (E : Subring ℂ) (f : ℍ → ℂ), InR E f → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f := by
  intro E f ⟨N, w, hN, _, hq⟩
  obtain ⟨a, ha, _⟩ := hq 1
  have hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => DD τ ^ w * f ((1 : SL(2, ℤ)) • τ)) :=
    ha.mdifferentiable hN
  have hD : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => DD τ ^ w) := fun τ => (dd_mdifferentiable τ).pow w
  have hdiv := hg.div hD (fun τ => pow_ne_zero _ (ReciprocityTheory.ChartRestriction.L1.DD_ne_zero τ))
  have heq : ((fun τ : ℍ => DD τ ^ w * f ((1 : SL(2, ℤ)) • τ)) / fun τ : ℍ => DD τ ^ w) = f := by
    funext τ
    have h0 : DD τ ^ w ≠ 0 := pow_ne_zero _ (ReciprocityTheory.ChartRestriction.L1.DD_ne_zero τ)
    simp only [Pi.div_apply, one_smul]
    field_simp
  rwa [heq] at hdiv

end GlobalTheory.FN
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MdifferentiableOfHasSomeLevelOverStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mdifferentiable_of_hasSomeLevelOver : ∀ (E : Subring ℂ) (f : ℍ → ℂ), InR E f → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f := by
  first | exact @GlobalTheory.FN.inR_mdifferentiable | exact GlobalTheory.FN.inR_mdifferentiable | (intros; apply GlobalTheory.FN.inR_mdifferentiable <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulOfIsPrimitiveIntegralHahnGauss
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulOfIsPrimitiveIntegralHahnGauss
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.Glue

theorem Prim.mul {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (P Q : HahnSeries ℚ Ω) :
    Prim A P → Prim A Q → Prim A (P * Q) := by
  classical
  rintro ⟨hPA, rP, hrP0, hrPi⟩ ⟨hQA, rQ, hrQ0, hrQi⟩
  let lift : ∀ φ : HahnSeries ℚ Ω, (∀ r, φ.coeff r ∈ A) → HahnSeries ℚ A := fun φ h =>
    { coeff := fun r => ⟨φ.coeff r, h r⟩
      isPWO_support' := φ.isPWO_support.mono (fun r hr h' => hr (Subtype.ext (by simpa using h'))) }
  let P' := lift P hPA
  let Q' := lift Q hQA
  let ι : A →ₙ+* Ω := (A.subtype : A →+* Ω)
  have hPm : P'.map ι = P := by ext r; rfl
  have hQm : Q'.map ι = Q := by ext r; rfl
  have hmul : (P' * Q').map ι = P * Q := by rw [HahnSeries.map_mul, hPm, hQm]
  have hcoeff : ∀ r, (P * Q).coeff r = (((P' * Q').coeff r : A) : Ω) := by
    intro r; rw [← hmul]; rfl

  have hunit : ∀ (x : Ω) (hx : x ∈ A), x ≠ 0 → x⁻¹ ∈ A → IsUnit (⟨x, hx⟩ : A) := by
    intro x hx h0 hi
    have h : (⟨x, hx⟩ : A) * ⟨x⁻¹, hi⟩ = 1 := Subtype.ext (by simp [mul_inv_cancel₀ h0])
    exact (Units.mkOfMulEqOne _ _ h).isUnit
  let π : A →ₙ+* IsLocalRing.ResidueField A := (IsLocalRing.residue A : A →+* IsLocalRing.ResidueField A)
  have hred : ∀ (φ : HahnSeries ℚ Ω) (h : ∀ r, φ.coeff r ∈ A) (r : ℚ), φ.coeff r ≠ 0 → (φ.coeff r)⁻¹ ∈ A →
      (lift φ h).map π ≠ 0 := by
    intro φ h r h0 hi hz
    have := congrArg (fun ψ : HahnSeries ℚ (IsLocalRing.ResidueField A) => ψ.coeff r) hz
    simp only [HahnSeries.coeff_zero] at this
    have hu := hunit _ (h r) h0 hi
    have hres : IsLocalRing.residue A (⟨φ.coeff r, h r⟩ : A) = 0 := this
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hres
    exact hres hu
  have hne : (P' * Q').map π ≠ 0 := by
    rw [HahnSeries.map_mul]
    exact mul_ne_zero (hred P hPA rP hrP0 hrPi) (hred Q hQA rQ hrQ0 hrQi)
  obtain ⟨r, hr⟩ : ∃ r, ((P' * Q').map π).coeff r ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (HahnSeries.ext (funext h))
  have hr' : IsLocalRing.residue A ((P' * Q').coeff r) ≠ 0 := hr
  rw [Ne, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hr'
  obtain ⟨u, hu⟩ := hr'
  have h1 : (((P' * Q').coeff r : A) : Ω) * (((u⁻¹ : Aˣ) : A) : Ω) = 1 := by
    rw [← hu]
    have := congrArg (fun a : A => (a : Ω)) u.mul_inv
    simpa only [MulMemClass.coe_mul, OneMemClass.coe_one] using this
  refine ⟨fun r => by rw [hcoeff r]; exact ((P' * Q').coeff r).2, r, ?_, ?_⟩
  · rw [hcoeff r]; exact left_ne_zero_of_mul_eq_one h1
  · rw [hcoeff r, inv_eq_of_mul_eq_one_right h1]; exact ((u⁻¹ : Aˣ) : A).2

end GlobalTheory.Glue
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulOfIsPrimitiveIntegralHahnGaussStatement
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mul_of_isPrimitiveIntegral_hahn_gauss : ∀ {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (P Q : HahnSeries ℚ Ω), Prim A P → Prim A Q → Prim A (P * Q) := by
  first | exact @GlobalTheory.Glue.Prim.mul | exact GlobalTheory.Glue.Prim.mul | (intros; apply GlobalTheory.Glue.Prim.mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneHolomorphicGermProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneHolomorphicGermProperties
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct
open Filter Topology

namespace GlobalTheory.KZ.Germ

theorem isOpen_Hs : IsOpen Hs := isOpen_lt continuous_const Complex.continuous_im

theorem isPreconnected_Hs : IsPreconnected Hs := (convex_halfSpace_im_gt 0).isPreconnected

theorem eventually_of_germ_eq {φ ψ : ℂ → ℂ} (h : (φ : Mero) = (ψ : Mero)) :
    ∀ τ ∈ Hs, ∀ᶠ z in 𝓝[≠] τ, φ z = ψ z := by
  intro τ hτ
  have h1 := (mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 (Filter.Germ.coe_eq.mp h)) τ hτ
  have h2 : Hs ∈ 𝓝[≠] τ := mem_nhdsWithin_of_mem_nhds (isOpen_Hs.mem_nhds hτ)
  filter_upwards [h1, h2] with z hz1 hz2
  rcases hz1 with hz | hz
  · exact hz
  · exact absurd hz2 hz

theorem eq_zero_or_eq_zero {a b : ℂ → ℂ} (ha : DifferentiableOn ℂ a Hs) (hb : DifferentiableOn ℂ b Hs)
    (h : ∀ z ∈ Hs, a z * b z = 0) : (∀ z ∈ Hs, a z = 0) ∨ (∀ z ∈ Hs, b z = 0) := by
  by_cases hA : ∀ z ∈ Hs, a z = 0
  · exact Or.inl hA
  · right
    push Not at hA
    obtain ⟨z₀, hz₀, hne⟩ := hA
    have hcont : ContinuousAt a z₀ := (ha.continuousOn).continuousAt (isOpen_Hs.mem_nhds hz₀)
    have hev : ∀ᶠ z in 𝓝 z₀, a z ≠ 0 := hcont.eventually_ne hne
    have hb0 : b =ᶠ[𝓝 z₀] 0 := by
      filter_upwards [hev, isOpen_Hs.mem_nhds hz₀] with z hz1 hz2
      have := h z hz2
      simpa [hz1] using this
    intro z hz
    exact (hb.analyticOnNhd isOpen_Hs).eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_Hs hz₀ hb0 hz

theorem exists_eq_zero_of_prod {ι : Type} [DecidableEq ι] (s : Finset ι) (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ s, DifferentiableOn ℂ (f i) Hs) (h : ∀ z ∈ Hs, ∏ i ∈ s, f i z = 0) :
    ∃ i ∈ s, ∀ z ∈ Hs, f i z = 0 := by
  induction s using Finset.induction_on with
  | empty =>
    exfalso
    have hI : Complex.I ∈ Hs := by show (0 : ℝ) < Complex.I.im; simp
    simpa using h _ hI
  | insert j s hj ih =>
    have hP : DifferentiableOn ℂ (fun z => ∏ i ∈ s, f i z) Hs := by
      exact DifferentiableOn.fun_finsetProd (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    rcases eq_zero_or_eq_zero (hf j (Finset.mem_insert_self j s)) hP
        (fun z hz => by have := h z hz; rwa [Finset.prod_insert hj] at this) with h1 | h1
    · exact ⟨j, Finset.mem_insert_self j s, h1⟩
    · obtain ⟨i, hi, hi'⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)) h1
      exact ⟨i, Finset.mem_insert_of_mem hi, hi'⟩

theorem tendsto_mob (g : GQ) {x : ℂ} (hx : x ∈ Hs) : Tendsto (mob g) (𝓝[≠] x) (𝓝[≠] (mob g x)) := by
  obtain ⟨hH, hmul, hone, hdiff, -, -⟩ := GlobalTheory.T.glTwoPosRatMobius_basic_laws
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · exact ((hdiff g).continuousOn.continuousAt (isOpen_Hs.mem_nhds hx)).tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (isOpen_Hs.mem_nhds hx)] with z hz1 hz2
    intro heq
    apply hz1
    show z = x
    have e1 : mob g⁻¹ (mob g z) = z := by rw [← hmul _ _ z hz2, inv_mul_cancel, hone]
    have e2 : mob g⁻¹ (mob g x) = x := by rw [← hmul _ _ x hx, inv_mul_cancel, hone]
    have : mob g z = mob g x := heq
    rw [← e1, this, e2]

theorem germ_comp (g : GQ) (φ ψ : ℂ → ℂ) (h : (φ : Mero) = (ψ : Mero)) :
    ((fun z => φ (mob g z) : ℂ → ℂ) : Mero) = ((fun z => ψ (mob g z) : ℂ → ℂ) : Mero) := by
  obtain ⟨hH, -, -, -, -, -⟩ := GlobalTheory.T.glTwoPosRatMobius_basic_laws
  apply Filter.Germ.coe_eq.mpr
  apply mem_codiscreteWithin_iff_forall_mem_nhdsNE.2
  intro x hx
  have h1 := (tendsto_mob g hx).eventually (eventually_of_germ_eq h (mob g x) (hH g x hx))
  filter_upwards [h1] with z hz
  exact Or.inl hz

theorem main : (∀ a b : ℂ → ℂ, DifferentiableOn ℂ a Hs → DifferentiableOn ℂ b Hs → (((a : Mero) = (b : Mero)) ↔ ∀ z ∈ Hs, a z = b z)) ∧ (∀ a b : ℂ → ℂ, DifferentiableOn ℂ a Hs → DifferentiableOn ℂ b Hs → (∀ z ∈ Hs, a z * b z = 0) → (∀ z ∈ Hs, a z = 0) ∨ (∀ z ∈ Hs, b z = 0)) ∧ (∀ (g : GQ) (φ ψ : ℂ → ℂ), (φ : Mero) = (ψ : Mero) → ((fun z => φ (mob g z) : ℂ → ℂ) : Mero) = ((fun z => ψ (mob g z) : ℂ → ℂ) : Mero)) ∧ (∀ (φ ψ : ℂ → ℂ), (φ : Mero) = (ψ : Mero) → ∀ τ ∈ Hs, ∀ᶠ z in nhdsWithin τ {τ}ᶜ, φ z = ψ z) ∧ (∀ (m : ℕ) (a b : ℂ → ℂ), 0 < m → DifferentiableOn ℂ a Hs → DifferentiableOn ℂ b Hs → (∀ z ∈ Hs, a z ^ m = b z ^ m) → ∃ k : ℕ, ∀ z ∈ Hs, a z = Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) / (m : ℂ)) * b z) := by
  refine ⟨?_, fun a b ha hb h => eq_zero_or_eq_zero ha hb h, germ_comp, fun φ ψ h => eventually_of_germ_eq h, ?_⟩
  · intro a b ha hb
    constructor
    · intro hab z hz
      have hI : Complex.I ∈ Hs := by show (0 : ℝ) < Complex.I.im; simp
      exact (ha.analyticOnNhd isOpen_Hs).eqOn_of_preconnected_of_frequently_eq (hb.analyticOnNhd isOpen_Hs)
        isPreconnected_Hs hI (eventually_of_germ_eq hab _ hI).frequently hz
    · intro h
      apply Filter.Germ.coe_eq.mpr
      filter_upwards [Filter.self_mem_codiscreteWithin Hs] with z hz
      exact h z hz
  · intro m a b hm ha hb h
    have hm0 : m ≠ 0 := hm.ne'
    have : NeZero m := ⟨hm0⟩
    have hζ := Complex.isPrimitiveRoot_exp m hm0
    obtain ⟨ξ, hξ, hξ'⟩ := exists_eq_zero_of_prod (Polynomial.nthRootsFinset m (1 : ℂ)) (fun ξ z => a z - ξ * b z)
      (fun ξ _ => ha.sub (hb.const_mul ξ))
      (fun z hz => by rw [← hζ.pow_sub_pow_eq_prod_sub_mul (a z) (b z) hm, h z hz, sub_self])
    have hξm : ξ ^ m = 1 := (Polynomial.mem_nthRootsFinset hm (1 : ℂ)).1 hξ
    obtain ⟨k, -, hk⟩ := hζ.eq_pow_of_pow_eq_one hξm
    refine ⟨k, fun z hz => ?_⟩
    have e : Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) / (m : ℂ)) = ξ := by
      rw [← hk, ← Complex.exp_nat_mul]; congr 1; ring
    rw [e]
    exact sub_eq_zero.mp (hξ' z hz)

end GlobalTheory.KZ.Germ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneHolomorphicGermPropertiesStatement
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.upperHalfPlane_holomorphic_germ_properties : (∀ a b : ℂ → ℂ, DifferentiableOn ℂ a Hs → DifferentiableOn ℂ b Hs → (((a : Mero) = (b : Mero)) ↔ ∀ z ∈ Hs, a z = b z)) ∧ (∀ a b : ℂ → ℂ, DifferentiableOn ℂ a Hs → DifferentiableOn ℂ b Hs → (∀ z ∈ Hs, a z * b z = 0) → (∀ z ∈ Hs, a z = 0) ∨ (∀ z ∈ Hs, b z = 0)) ∧ (∀ (g : GQ) (φ ψ : ℂ → ℂ), (φ : Mero) = (ψ : Mero) → ((fun z => φ (mob g z) : ℂ → ℂ) : Mero) = ((fun z => ψ (mob g z) : ℂ → ℂ) : Mero)) ∧ (∀ (φ ψ : ℂ → ℂ), (φ : Mero) = (ψ : Mero) → ∀ τ ∈ Hs, ∀ᶠ z in nhdsWithin τ {τ}ᶜ, φ z = ψ z) ∧ (∀ (m : ℕ) (a b : ℂ → ℂ), 0 < m → DifferentiableOn ℂ a Hs → DifferentiableOn ℂ b Hs → (∀ z ∈ Hs, a z ^ m = b z ^ m) → ∃ k : ℕ, ∀ z ∈ Hs, a z = Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) / (m : ℂ)) * b z) := by
  first | exact @GlobalTheory.KZ.Germ.main | exact GlobalTheory.KZ.Germ.main | (intros; apply GlobalTheory.KZ.Germ.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.QuotientIntegralHolomorphic
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.QuotientIntegralHolomorphic
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
open Filter Topology

namespace GlobalTheory

theorem norm_root_monic_le (n : ℕ) (s : Fin n → ℂ) (y : ℂ)
    (hy : y ^ n + ∑ j, s j * y ^ (j : ℕ) = 0) : ‖y‖ ≤ 1 + ∑ j, ‖s j‖ := by
  have hS : 0 ≤ ∑ j, ‖s j‖ := Finset.sum_nonneg fun j _ => norm_nonneg _
  by_cases h1 : ‖y‖ ≤ 1
  · linarith
  push_neg at h1
  cases n with
  | zero => simp at hy
  | succ m =>
    have hyn : y ^ (m + 1) = -∑ j, s j * y ^ (j : ℕ) := eq_neg_of_add_eq_zero_left hy
    have hle : ‖y‖ ^ (m + 1) ≤ (∑ j, ‖s j‖) * ‖y‖ ^ m := by
      calc ‖y‖ ^ (m + 1) = ‖y ^ (m + 1)‖ := (norm_pow _ _).symm
        _ = ‖∑ j, s j * y ^ (j : ℕ)‖ := by rw [hyn, norm_neg]
        _ ≤ ∑ j, ‖s j * y ^ (j : ℕ)‖ := norm_sum_le _ _
        _ ≤ ∑ j : Fin (m + 1), ‖s j‖ * ‖y‖ ^ m := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [norm_mul, norm_pow]
          gcongr
          · exact h1.le
          · exact Nat.lt_succ_iff.1 j.isLt
        _ = (∑ j, ‖s j‖) * ‖y‖ ^ m := by rw [Finset.sum_mul]
    have hpos : 0 < ‖y‖ ^ m := pow_pos (by linarith) _
    rw [pow_succ] at hle
    have : ‖y‖ ≤ ∑ j, ‖s j‖ := by
      by_contra hc
      push_neg at hc
      have := mul_lt_mul_of_pos_left hc hpos
      nlinarith
    linarith

end GlobalTheory

namespace GlobalTheory

theorem quotient_integral_holomorphic : ∀ (U : Set ℂ) (n : ℕ) (A D : ℂ → ℂ) (s : Fin n → ℂ → ℂ), IsOpen U → IsPreconnected U → DifferentiableOn ℂ A U → DifferentiableOn ℂ D U → (∀ j, DifferentiableOn ℂ (s j) U) → (∃ z ∈ U, D z ≠ 0) → (∀ z ∈ U, A z ^ n + ∑ j, s j z * A z ^ (j : ℕ) * D z ^ (n - j) = 0) → ∃ h : ℂ → ℂ, DifferentiableOn ℂ h U ∧ (∀ z ∈ U, A z = h z * D z) ∧ ∀ z ∈ U, h z ^ n + ∑ j, s j z * h z ^ (j : ℕ) = 0 := by
  intro U n A D s hU hUc hA hD hs ⟨z₁, hz₁U, hz₁⟩ heq
  classical
  have hiso : ∀ z₀ ∈ U, ∀ᶠ w in 𝓝[≠] z₀, D w ≠ 0 := by
    intro z₀ hz₀
    by_contra hcon
    rw [Filter.not_eventually] at hcon
    simp only [not_not] at hcon
    have := (hD.analyticOnNhd hU).eqOn_zero_of_preconnected_of_frequently_eq_zero hUc hz₀ hcon
    exact hz₁ (this hz₁U)
  have hroot : ∀ w ∈ U, D w ≠ 0 → (A w / D w) ^ n + ∑ j, s j w * (A w / D w) ^ (j : ℕ) = 0 := by
    intro w hw hDw
    have hDn : D w ^ n ≠ 0 := pow_ne_zero _ hDw
    have key : D w ^ n * ((A w / D w) ^ n + ∑ j, s j w * (A w / D w) ^ (j : ℕ))
        = A w ^ n + ∑ j, s j w * A w ^ (j : ℕ) * D w ^ (n - j) := by
      rw [mul_add, Finset.mul_sum]
      congr 1
      · rw [div_pow, mul_div_cancel₀ _ hDn]
      · refine Finset.sum_congr rfl fun j _ => ?_
        have hj : (j : ℕ) ≤ n := j.isLt.le
        have hsplit : D w ^ n = D w ^ (j : ℕ) * D w ^ (n - j) := by
          rw [← pow_add, Nat.add_sub_cancel' hj]
        rw [hsplit, div_pow]
        field_simp
    have := heq w hw
    rw [← key] at this
    exact (mul_eq_zero.1 this).resolve_left hDn
  have hAz : ∀ w ∈ U, D w = 0 → A w = 0 := by
    intro w hw hDw
    have := heq w hw
    have hsum : ∑ j : Fin n, s j w * A w ^ (j : ℕ) * D w ^ (n - j) = 0 := by
      refine Finset.sum_eq_zero fun j _ => ?_
      have := j.isLt
      rw [hDw, zero_pow (by omega : n - (j : ℕ) ≠ 0), mul_zero]
    rw [hsum, add_zero] at this
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp at this
    · exact (pow_eq_zero_iff hn.ne').1 this
  obtain ⟨h, hh⟩ : ∃ h : ℂ → ℂ, ∀ z, h z =
      if D z = 0 then limUnder (𝓝[≠] z) (fun w => A w / D w) else A z / D z := ⟨_, fun z => rfl⟩
  have hdiffAt : ∀ z₀ ∈ U, DifferentiableAt ℂ h z₀ := by
    intro z₀ hz₀
    have hUn : U ∈ 𝓝 z₀ := hU.mem_nhds hz₀
    by_cases hDz : D z₀ = 0
    · have h1 : ∀ᶠ w in 𝓝 z₀, w ∈ U := hUn
      have h2 : ∀ᶠ w in 𝓝 z₀, w ≠ z₀ → D w ≠ 0 := eventually_nhdsWithin_iff.1 (hiso z₀ hz₀)
      have h3 : ∀ᶠ w in 𝓝 z₀, ∀ j, ‖s j w‖ < ‖s j z₀‖ + 1 := by
        rw [Filter.eventually_all]
        intro j
        have hc : ContinuousAt (fun w => ‖s j w‖) z₀ :=
          ((hs j).differentiableAt hUn).continuousAt.norm
        exact hc.eventually (Iio_mem_nhds (lt_add_one _))
      obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 (h1.and (h2.and h3))
      have hsub : ∀ w ∈ Metric.ball z₀ r, w ∈ U := fun w hw => (hball w hw).1
      have hne : ∀ w ∈ Metric.ball z₀ r, w ≠ z₀ → D w ≠ 0 := fun w hw => (hball w hw).2.1
      have hsb : ∀ w ∈ Metric.ball z₀ r, ∀ j, ‖s j w‖ < ‖s j z₀‖ + 1 := fun w hw => (hball w hw).2.2
      have hfd : DifferentiableOn ℂ (fun w => A w / D w) (Metric.ball z₀ r \ {z₀}) := by
        intro w hw
        have hwU : U ∈ 𝓝 w := hU.mem_nhds (hsub w hw.1)
        exact ((hA.differentiableAt hwU).div (hD.differentiableAt hwU)
          (hne w hw.1 hw.2)).differentiableWithinAt
      have hbd : BddAbove (norm ∘ (fun w => A w / D w) '' (Metric.ball z₀ r \ {z₀})) := by
        refine ⟨1 + ∑ j, (‖s j z₀‖ + 1), ?_⟩
        rintro _ ⟨w, hw, rfl⟩
        have := GlobalTheory.norm_root_monic_le n (fun j => s j w) (A w / D w) (hroot w (hsub w hw.1) (hne w hw.1 hw.2))
        show ‖A w / D w‖ ≤ _
        refine this.trans ?_
        gcongr with j
        exact (hsb w hw.1 j).le
      have hg := Complex.differentiableOn_update_limUnder_of_bddAbove
        (Metric.ball_mem_nhds z₀ hr) hfd hbd
      have heqg : h =ᶠ[𝓝 z₀] Function.update (fun w => A w / D w) z₀
          (limUnder (𝓝[≠] z₀) (fun w => A w / D w)) := by
        filter_upwards [Metric.ball_mem_nhds z₀ hr] with w hw
        by_cases hw0 : w = z₀
        · subst hw0; rw [hh, if_pos hDz, Function.update_self]
        · rw [hh, if_neg (hne w hw hw0), Function.update_of_ne hw0]
      exact (hg.differentiableAt (Metric.ball_mem_nhds z₀ hr)).congr_of_eventuallyEq heqg
    · have hDc : ContinuousAt D z₀ := (hD.differentiableAt hUn).continuousAt
      have heqf : h =ᶠ[𝓝 z₀] fun w => A w / D w := by
        filter_upwards [hDc.eventually_ne hDz] with w hw
        rw [hh, if_neg hw]
      exact ((hA.differentiableAt hUn).div (hD.differentiableAt hUn) hDz).congr_of_eventuallyEq heqf
  refine ⟨h, fun z hz => (hdiffAt z hz).differentiableWithinAt, ?_, ?_⟩
  · intro z hz
    by_cases hDz : D z = 0
    · rw [hDz, mul_zero]; exact hAz z hz hDz
    · rw [hh, if_neg hDz, div_mul_cancel₀ _ hDz]
  · intro z hz
    by_cases hDz : D z = 0
    · have hUn : U ∈ 𝓝 z := hU.mem_nhds hz
      have hFd : DifferentiableAt ℂ (fun w => h w ^ n + ∑ j, s j w * h w ^ (j : ℕ)) z := by
        apply ((hdiffAt z hz).pow n).add
        have hsum := DifferentiableAt.sum (u := Finset.univ)
          (A := fun (j : Fin n) (w : ℂ) => s j w * h w ^ (j : ℕ))
          (fun j _ => ((hs j).differentiableAt hUn).mul ((hdiffAt z hz).pow _))
        convert hsum using 1
        ext w
        simp [Finset.sum_apply]
      have hev : ∀ᶠ w in 𝓝[≠] z, h w ^ n + ∑ j, s j w * h w ^ (j : ℕ) = 0 := by
        filter_upwards [hiso z hz, nhdsWithin_le_nhds hUn] with w hw hwU
        rw [hh, if_neg hw]
        exact hroot w hwU hw
      have ht : Tendsto (fun w => h w ^ n + ∑ j, s j w * h w ^ (j : ℕ)) (𝓝[≠] z) (𝓝 0) :=
        tendsto_const_nhds.congr' (hev.mono fun w hw => hw.symm)
      exact tendsto_nhds_unique (hFd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) ht
    · rw [hh, if_neg hDz]
      exact hroot z hz hDz

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.QuotientIntegralHolomorphicStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_differentiableOn_quotient_of_integral : ∀ (U : Set ℂ) (n : ℕ) (A D : ℂ → ℂ) (s : Fin n → ℂ → ℂ), IsOpen U → IsPreconnected U → DifferentiableOn ℂ A U → DifferentiableOn ℂ D U → (∀ j, DifferentiableOn ℂ (s j) U) → (∃ z ∈ U, D z ≠ 0) → (∀ z ∈ U, A z ^ n + ∑ j, s j z * A z ^ (j : ℕ) * D z ^ (n - j) = 0) → ∃ h : ℂ → ℂ, DifferentiableOn ℂ h U ∧ (∀ z ∈ U, A z = h z * D z) ∧ ∀ z ∈ U, h z ^ n + ∑ j, s j z * h z ^ (j : ℕ) = 0 := by
  first | exact @GlobalTheory.quotient_integral_holomorphic | exact GlobalTheory.quotient_integral_holomorphic | (intros; apply GlobalTheory.quotient_integral_holomorphic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularDiscriminantPowMulSlashTwelveMul
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularDiscriminantPowMulSlashTwelveMul
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory

theorem disc_pow_mul_slash : ∀ (w : ℕ) (f : ℍ → ℂ) (γ : SL(2, ℤ)), ((fun τ => DD τ ^ w * f τ) ∣[((12 * w : ℕ) : ℤ)] γ) = fun τ => DD τ ^ w * f (γ • τ) := by
  intro w f γ
  funext τ
  rw [ModularForm.SL_slash_apply]
  have hd : (UpperHalfPlane.denom γ τ) ≠ 0 := UpperHalfPlane.denom_ne_zero _ τ
  rw [ReciprocityTheory.ChartRestriction.L1.DD_smul, mul_pow, ← pow_mul]
  rw [zpow_neg, zpow_natCast]
  field_simp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularDiscriminantPowMulSlashTwelveMulStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modularDiscriminant_pow_mul_slash_twelve_mul : ∀ (w : ℕ) (f : ℍ → ℂ) (γ : SL(2, ℤ)), ((fun τ => DD τ ^ w * f τ) ∣[((12 * w : ℕ) : ℤ)] γ) = fun τ => DD τ ^ w * f (γ • τ) := by
  first | exact @GlobalTheory.disc_pow_mul_slash | exact GlobalTheory.disc_pow_mul_slash | (intros; apply GlobalTheory.disc_pow_mul_slash <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUnitEvalEqKummerClass
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUnitEvalEqKummerClass
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.KZ.ES

theorem exists_un_eval_eq_cls : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (l n : ℕ) [Fact l.Prime], ∀ a ∈ X.A l, ∃ f ∈ X.Un (l ^ n), AdicCompletion.eval (idl l) (X.Kl l) n a = X.cls l n f := by
  intro Ω _ _ _ ε X hj l n _ a ha
  obtain ⟨-, -, hmul, hone, hsmul, -, -⟩ := GlobalTheory.KZ.H3.cls_props Ω ε X l n
  obtain ⟨u1, umul, -, -, -, upow, -⟩ := GlobalTheory.KZ.UnClosure.un_closure ε X ε.injective hj (l ^ n)
  unfold Tower.A at ha
  induction ha using Submodule.span_induction with
  | mem x hx => exact hx n
  | zero => exact ⟨1, u1, by rw [map_zero, hone]⟩
  | add x y _ _ hx hy =>
    obtain ⟨f, hf, ef⟩ := hx
    obtain ⟨g, hg, eg⟩ := hy
    exact ⟨f * g, umul f g hf hg, by rw [map_add (f := _), ef, eg, hmul]⟩
  | smul c x _ hx =>
    obtain ⟨f, hf, ef⟩ := hx
    exact ⟨_, upow _ f hf, by rw [map_smul, ef, hsmul]⟩

end GlobalTheory.KZ.ES
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUnitEvalEqKummerClassStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_eval_eq_kummer_class : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (l n : ℕ) [Fact l.Prime], ∀ a ∈ X.A l, ∃ f ∈ X.Un (l ^ n), AdicCompletion.eval (idl l) (X.Kl l) n a = X.cls l n f := by
  first | exact @GlobalTheory.KZ.ES.exists_un_eval_eq_cls | exact GlobalTheory.KZ.ES.exists_un_eval_eq_cls | (intros; apply GlobalTheory.KZ.ES.exists_un_eval_eq_cls <;> assumption)
end
end
