module

public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
public import Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan.LatSOfLocBasis
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EqNegOfCommute
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletedLatticeStabilizerCompactOpen
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiscreteTopologyRatN
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousDistribHaarCharUnits

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocallyCompactSecondCountableT2
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Datum
open Formalism.MainNotions.S hiding Af
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MemberAdelicTop

theorem locallyCompact_secondCountable_t2 : ∀ (D : D7) (V : HSp D), LocallyCompactSpace (GA D V) ∧ SecondCountableTopology (GA D V) ∧ T2Space (GA D V) := fun D V =>
  GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary D.host.F D.host.E D.sp.cm.sig V.rank V.gram

end GlobalTheory.MemberAdelicTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RePosOfIsMultIP
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Datum
open Formalism.MainNotions.S hiding Af
open scoped TensorProduct InnerProductSpace Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SchurConst

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem left_cont_of_mem (θ : InfFam D) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (T : MMap M)
    (hT : T ∈ Mult θ M J χ) (v : M.Vec) :
    Continuous (T v) ∧ ∀ γ ∈ GQ V, ∀ g, T v (γ * g) = T v g := by
  unfold Mult at hT
  induction hT using Submodule.span_induction with
  | mem x hx => exact ⟨(IsMultMap.aut hx v).cont, (IsMultMap.aut hx v).left⟩
  | zero => exact ⟨continuous_const, fun _ _ _ => rfl⟩
  | add x y _ _ hx hy =>
    refine ⟨hx.1.add hy.1, fun γ hγ g => ?_⟩
    show x v (γ * g) + y v (γ * g) = x v g + y v g
    rw [hx.2 γ hγ, hy.2 γ hγ]
  | smul a x _ hx =>
    refine ⟨hx.1.const_smul a, fun γ hγ g => ?_⟩
    show a • x v (γ * g) = a • x v g
    rw [hx.2 γ hγ]

theorem eq_zero_of_ae (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (hμ : μ.IsHaarMeasure)
    (hF : IsFundamentalDomain (GQ V) 𝓕 μ) (φ : GA D V → ℂ) (hc : Continuous φ)
    (hL : ∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) (h2 : ∀ᵐ g ∂(μ.restrict 𝓕), φ g = 0) : φ = 0 := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA D.sp.cm.sig V.gram
  have : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup (GQ V)
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup (GQ V) μ
  let t : Set (GA D V) := {g | φ g ≠ 0}
  have ht : IsOpen t := hc.isOpen_preimage _ isOpen_ne
  have htm : MeasurableSet t := ht.measurableSet
  have h3 : μ (t ∩ 𝓕) = 0 := by
    rw [← Measure.restrict_apply htm]
    exact ae_iff.1 h2
  have hinv : ∀ γ : GQ V, γ • t = t := by
    intro γ
    ext g
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    show φ (((γ⁻¹ : GQ V) : GA D V) * g) ≠ 0 ↔ φ g ≠ 0
    rw [hL _ (γ⁻¹).2]
  have h4 : μ t = 0 := hF.measure_zero_of_invariant t hinv h3
  have h5 : t = ∅ := (ht.measure_eq_zero_iff μ).1 h4
  funext g
  by_contra hg
  have : g ∈ t := hg
  rw [h5] at this
  exact this

theorem exists_vec (M : DSModel V S) (h : ∀ τ, M.sm τ ≠ ⊥) :
    ∃ v : M.Vec, ∏ τ, ⟪(v τ : M.H τ), (v τ : M.H τ)⟫_ℂ ≠ 0 := by
  choose w hw hw0 using fun τ => (Submodule.ne_bot_iff _).1 (h τ)
  refine ⟨fun τ => ⟨w τ, hw τ⟩, Finset.prod_ne_zero_iff.2 fun τ _ => ?_⟩
  exact fun e => hw0 τ (inner_self_eq_zero.1 e)

theorem isMultiplicityInner_add_smul_right (M : DSModel V S) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (T T' T'' : MMap M)
    {a b : ℂ} (c : ℂ) (h : IsMultIP M μ 𝓕 T T' a) (h' : IsMultIP M μ 𝓕 T T'' b) :
    IsMultIP M μ 𝓕 T (T' + c • T'') (a + c * b) := by
  intro v v'
  have e : (fun g => star (T v g) * (T' + c • T'') v' g) =
      fun g => star (T v g) * T' v' g + c * (star (T v g) * T'' v' g) := by
    funext g
    show star (T v g) * (T' v' g + c * T'' v' g) = _
    ring
  have i2 : IntegrableOn (fun g => c * (star (T v g) * T'' v' g)) 𝓕 μ := (h' v v').1.const_mul c
  rw [e]
  refine ⟨(h v v').1.add i2, ?_⟩
  rw [integral_add (h v v').1 i2, integral_const_mul, (h v v').2, (h' v v').2]
  ring

theorem isMultiplicityInner_symm (M : DSModel V S) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (T T' : MMap M)
    {a : ℂ} (h : IsMultIP M μ 𝓕 T T' a) : IsMultIP M μ 𝓕 T' T (star a) := by
  intro v v'
  have e : (fun g => star (T' v g) * T v' g) = fun g => (starRingEnd ℂ) (star (T v' g) * T' v g) := by
    funext g
    rw [starRingEnd_apply, star_mul, star_star]
  rw [e]
  refine ⟨?_, ?_⟩
  · exact (Complex.conjCLE.toContinuousLinearMap.integrable_comp (h v' v).1 :)
  · rw [integral_conj, (h v' v).2, map_mul, map_prod]
    simp only [inner_conj_symm]
    rfl

theorem re_pos_of_isMultIP (M : DSModel V S) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (hμ : μ.IsHaarMeasure)
    (hF : IsFundamentalDomain (GQ V) 𝓕 μ) (T : MMap M) {a : ℂ} (h : IsMultIP M μ 𝓕 T T a) (v : M.Vec)
    (hc : Continuous (T v)) (hL : ∀ γ ∈ GQ V, ∀ g, T v (γ * g) = T v g) (h0 : T v ≠ 0) : 0 < a.re := by
  obtain ⟨hi, he⟩ := h v v
  have e : (fun g => star (T v g) * T v g) = fun g => ((‖T v g‖ ^ 2 : ℝ) : ℂ) := by
    funext g
    rw [Complex.star_def, Complex.conj_mul']
    push_cast
    rfl
  rw [e] at hi he
  have hi' : IntegrableOn (fun g => ‖T v g‖ ^ 2) 𝓕 μ := by
    have := hi.re
    simp only [RCLike.re_to_complex, Complex.ofReal_re] at this
    exact this
  rw [integral_complex_ofReal] at he
  have e2 : ∏ τ, ⟪(v τ : M.H τ), (v τ : M.H τ)⟫_ℂ = ((∏ τ, ‖(v τ : M.H τ)‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  rw [e2] at he
  have he' := congrArg Complex.re he
  rw [Complex.ofReal_re, Complex.re_mul_ofReal] at he'
  have hp : 0 ≤ ∏ τ, ‖(v τ : M.H τ)‖ ^ 2 := Finset.prod_nonneg fun τ _ => by positivity
  have hnn : 0 ≤ ∫ g in 𝓕, ‖T v g‖ ^ 2 ∂μ := integral_nonneg fun g => by positivity
  have hne : ∫ g in 𝓕, ‖T v g‖ ^ 2 ∂μ ≠ 0 := by
    intro hz
    have := (integral_eq_zero_iff_of_nonneg (fun g => by positivity) hi').1 hz
    refine h0 (eq_zero_of_ae μ 𝓕 hμ hF _ hc hL ?_)
    filter_upwards [this] with g hg
    simpa using hg
  have hpos : 0 < a.re * ∏ τ, ‖(v τ : M.H τ)‖ ^ 2 := he' ▸ lt_of_le_of_ne hnn hne.symm
  by_contra hn
  exact absurd hpos (not_lt.2 (mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hn) hp))

theorem ipM_posDef : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), IsInfFam θ → μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ → SchurMult θ M J χ μ 𝓕 → (∀ τ, M.sm τ ≠ ⊥) → (∀ T ∈ Mult θ M J χ, ∀ T' ∈ Mult θ M J χ, ∀ T'' ∈ Mult θ M J χ, ∀ c : ℂ, ipM M μ 𝓕 T (T' + c • T'') = ipM M μ 𝓕 T T' + c * ipM M μ 𝓕 T T'' ∧ ipM M μ 𝓕 T' T = star (ipM M μ 𝓕 T T')) ∧ ∀ T ∈ Mult θ M J χ, T ≠ 0 → 0 < (ipM M μ 𝓕 T T).re := by
  intro D θ V S M J χ μ 𝓕 hθ hμ hF hS hsm
  obtain ⟨v0, hv0⟩ := exists_vec M hsm
  have hs : ∀ T ∈ Mult θ M J χ, ∀ T' ∈ Mult θ M J χ, IsMultIP M μ 𝓕 T T' (ipM M μ 𝓕 T T') :=
    fun T hT T' hT' => ipM_spec M μ 𝓕 T T' (hS hθ hμ hF T hT T' hT')
  refine ⟨fun T hT T' hT' T'' hT'' c => ⟨?_, ?_⟩, fun T hT h0 => ?_⟩
  · exact hasPeterssonInner_unique M μ 𝓕 _ _ v0 hv0
      (hs T hT _ (Submodule.add_mem _ hT' (Submodule.smul_mem _ c hT'')))
      (isMultiplicityInner_add_smul_right M μ 𝓕 T T' T'' c (hs T hT T' hT') (hs T hT T'' hT''))
  · exact hasPeterssonInner_unique M μ 𝓕 _ _ v0 hv0 (hs T' hT' T hT) (isMultiplicityInner_symm M μ 𝓕 T T' (hs T hT T' hT'))
  · obtain ⟨v, hv⟩ : ∃ v, T v ≠ 0 := by
      by_contra hn
      push_neg at hn
      exact h0 (MultilinearMap.ext hn)
    have := left_cont_of_mem θ M J χ T hT v
    exact re_pos_of_isMultIP M μ 𝓕 hμ hF T (hs T hT T hT) v this.1 this.2 hv

end GlobalTheory.SchurConst
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNormalisedGraphClosure
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.GraphClosure

theorem charZero_residueField_of_flat {R : Type} [CommRing R] [IsDomain R] [CharZero R] {W : Scheme.{0}}
    (s : W ⟶ Sp R) [Flat s] {x : W} (hx : x ∈ genericPoints W) : CharZero (W.residueField x) := by
  have hsp : genericPoint (Sp R) ⤳ s x := (genericPoint_spec (Sp R)).specializes trivial
  obtain ⟨x', hx', e⟩ := Flat.generalizingMap s hsp
  obtain rfl := eq_of_specializes_of_mem_genericPoints hx hx'
  have : CharZero ((Sp R).residueField (s x')) := by
    rw [e]
    have : Nonempty (⊤ : (Sp R).Opens) := ⟨⟨genericPoint (Sp R), trivial⟩⟩
    have : CharZero (Sp R).functionField :=
      charZero_of_injective_ringHom (R := R)
        (f := ((Scheme.ΓSpecIso (.of R)).inv ≫ (Sp R).germToFunctionField ⊤).hom)
        (((Sp R).germToFunctionField_injective ⊤).comp
          (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).inv).1)
    exact charZero_of_injective_ringHom (R := (Sp R).functionField)
      ((Sp R).residue (genericPoint (Sp R))).hom.injective
  exact charZero_of_injective_ringHom (s.residueFieldMap x').hom.injective

end GlobalTheory.GraphClosure
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryCompletionMapsDualLattices
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryCompletionMapsDualLattices
open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.DualCompletion

open Formalism.L2.G.RelativeIndexFlags

theorem hform_mulVec_left {A : Type} [CommRing A] {n : ℕ} (τ : A →+* A) (J B : Matrix (Fin n) (Fin n) A)
    (t x : Fin n → A) : hform τ J (B *ᵥ t) x = ∑ a, τ (t a) * ((cT τ B * J) *ᵥ x) a := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hform, cT, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => by ring

theorem hform_col {A : Type} [CommRing A] {n : ℕ} (τ : A →+* A) (J B : Matrix (Fin n) (Fin n) A)
    (a : Fin n) (c : A) (x : Fin n → A) :
    hform τ J (B *ᵥ Pi.single a c) x = τ c * ((cT τ B * J) *ᵥ x) a := by
  rw [hform_mulVec_left, Finset.sum_eq_single a]
  · rw [Pi.single_eq_same]
  · intro b _ hb; rw [Pi.single_eq_of_ne hb, map_zero, zero_mul]
  · intro h; exact (h (Finset.mem_univ a)).elim

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem mem_dualL (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (y : Fin n → E) :
    y ∈ dualL σ J Λ ↔ y ∈ dualSet σ J Λ := by
  refine ⟨fun hy => ?_, fun hy => Submodule.subset_span hy⟩
  induction hy using Submodule.span_induction with
  | mem y hy => exact hy
  | zero => intro x _; simp [hform]
  | add y z _ _ hy hz =>
    intro x hx
    have : hform σ J x (y + z) = hform σ J x y + hform σ J x z := by
      simp [hform, mul_add, Finset.sum_add_distrib]
    rw [this]; exact add_mem (hy x hx) (hz x hx)
  | smul a y _ hy =>
    intro x hx
    have : hform σ J x (a • y) = algebraMap (𝓞 E) E a * hform σ J x y := by
      simp only [hform, Finset.mul_sum, Pi.smul_apply, Algebra.smul_def]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [this]; exact mul_mem ⟨a, rfl⟩ (hy x hx)

theorem exists_common_den {p : ℕ} (hp : p.Prime) (M : Submodule (𝓞 E) (Fin n → E)) (hM : M.FG) (B : GL (Fin n) E)
    (hB : IsLocBasis p (M : Set (Fin n → E)) B) :
    ∃ s : ℕ, ¬ p ∣ s ∧ ∀ m ∈ M, ∀ a, (s : E) * ((B⁻¹).1 *ᵥ m) a ∈ (algebraMap (𝓞 E) E).range := by
  classical
  have h1 : ¬ p ∣ 1 := fun h => hp.ne_one (Nat.dvd_one.1 h)
  obtain ⟨S, rfl⟩ := hM
  choose s hs H using fun m : S => (hB m.1).1 ⟨1, h1, by
    rw [Nat.cast_one, one_smul]; exact Submodule.subset_span m.2⟩
  refine ⟨∏ m, s m, fun hd => ?_, fun m hm => ?_⟩
  · obtain ⟨a, _, ha⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1 hd
    exact hs a ha
  · induction hm using Submodule.span_induction with
    | mem y hy =>
      intro a
      rw [← Finset.mul_prod_erase Finset.univ s (Finset.mem_univ ⟨y, hy⟩), mul_comm (s _), Nat.cast_mul, mul_assoc]
      exact mul_mem (natCast_mem _ _) (H ⟨y, hy⟩ a)
    | zero => intro a; simp
    | add y z _ _ hy hz => intro a; rw [Matrix.mulVec_add, Pi.add_apply, mul_add]; exact add_mem (hy a) (hz a)
    | smul c y _ hy =>
      intro a
      rw [Matrix.mulVec_smul, Pi.smul_apply, Algebra.smul_def, mul_left_comm]
      exact mul_mem ⟨c, rfl⟩ (hy a)

theorem isLocBasis_dual (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) {p : ℕ} (hp : p.Prime)
    (M : Submodule (𝓞 E) (Fin n → E)) (hM : M.FG) (B : GL (Fin n) E)
    (hB : IsLocBasis p (M : Set (Fin n → E)) B) (C : GL (Fin n) E) (hC : C.1 = cT (σ : E →+* E) B.1 * J) :
    IsLocBasis p (dualL (σ : E →+* E) J M : Set (Fin n → E)) C⁻¹ := by
  classical
  have h1 : ¬ p ∣ 1 := fun h => hp.ne_one (Nat.dvd_one.1 h)
  intro x
  rw [inv_inv, hC]
  simp only [SetLike.mem_coe, mem_dualL]
  constructor
  · rintro ⟨s, hs, hx⟩
    choose t ht H using fun a : Fin n => (hB (B.1 *ᵥ Pi.single a 1)).2 ⟨1, h1, fun b => by
      rw [Nat.cast_one, one_mul]; exact latB_col B a b⟩
    refine ⟨(∏ a, t a) * s, fun hd => ?_, fun a => ?_⟩
    · rcases (Nat.Prime.dvd_mul hp).1 hd with hd | hd
      · obtain ⟨a, _, ha⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1 hd
        exact ht a ha
      · exact hs hd
    · have h := hx _ (H a)
      rw [Formalism.UG.P.csDual_hform_smul_left, hform_col, map_one, one_mul, map_natCast, Matrix.mulVec_smul,
        Pi.smul_apply, smul_eq_mul] at h
      rw [← Finset.mul_prod_erase Finset.univ t (Finset.mem_univ a), mul_comm (t a), Nat.cast_mul, Nat.cast_mul,
        mul_assoc, mul_assoc]
      exact mul_mem (natCast_mem _ _) h
  · rintro ⟨s, hs, hx⟩
    obtain ⟨t, ht, H⟩ := exists_common_den hp M hM B hB
    refine ⟨t * s, fun hd => ((Nat.Prime.dvd_mul hp).1 hd).elim ht hs, fun m hm => ?_⟩
    have e : m = B.1 *ᵥ ((B⁻¹).1 *ᵥ m) := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    rw [e, hform_mulVec_left]
    refine sum_mem fun a _ => ?_
    obtain ⟨b, hb⟩ := H m hm a
    have h2 := sig_int σ b
    rw [hb, map_mul, map_natCast] at h2
    have h3 := mul_mem h2 (hx a)
    convert h3 using 1
    rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, Nat.cast_mul]
    show σ _ * _ = _
    ring

theorem mem_latS_dualL (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (hJ : IsUnit J.det)
    (v : HeightOneSpectrum (𝓞 F)) (M : Submodule (𝓞 E) (Fin n → E)) (hM : Submodule.IsFullLattice E M)
    (w : Fin n → E ⊗[F] v.adicCompletion F) :
    w ∈ latS (F := F) (v.adicCompletion F) (intV E v) (dualL (σ : E →+* E) J M) ↔
      ∀ u ∈ latS (F := F) (v.adicCompletion F) (intV E v) M,
        hform (sigR σ (v.adicCompletion F)) (J.map (inclE (F := F) (v.adicCompletion F))) u w ∈ intV E v := by
  classical
  haveI := v.isMaximal
  obtain ⟨p, -, -, hv, hp, -⟩ := Ideal.exists_prime_and_absNorm_eq_pow v.asIdeal
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨B, hB⟩ := LocB.exists_isLocBasis p E M hM.fg hM.span_eq_top
  have hu : IsUnit (cT (σ : E →+* E) B.1 * J).det := by
    rw [Matrix.det_mul, cT, Matrix.det_transpose]
    refine IsUnit.mul ?_ hJ
    have := ((Matrix.isUnit_iff_isUnit_det _).1 B.isUnit).map (σ : E →+* E)
    rwa [RingHom.map_det] at this
  let C : GL (Fin n) E := Matrix.GeneralLinearGroup.mk'' _ hu
  have hC : C.1 = cT (σ : E →+* E) B.1 * J := rfl
  have hD := isLocBasis_dual σ J hp M hM.fg B hB C hC
  rw [latS_of_locBasis v hp hv _ _ hD, latS_of_locBasis v hp hv _ _ hB, mem_latS_latB, map_inv, inv_inv]
  have hC' : (bc (inclE (F := F) (v.adicCompletion F)) C).1 =
      cT (sigR σ (v.adicCompletion F)) (bc (inclE (F := F) (v.adicCompletion F)) B).1 *
        J.map (inclE (F := F) (v.adicCompletion F)) := by
    show C.1.map (inclE (F := F) (v.adicCompletion F)) =
      cT (sigR σ (v.adicCompletion F)) (B.1.map (inclE (F := F) (v.adicCompletion F))) * _
    rw [hC, Matrix.map_mul]
    congr 1
  rw [hC']
  set B' := bc (inclE (F := F) (v.adicCompletion F)) B with hB'
  constructor
  · intro h u hu
    rw [mem_latS_latB] at hu
    have e : u = B'.1 *ᵥ ((B'⁻¹).1 *ᵥ u) := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    rw [e, hform_mulVec_left]
    exact sum_mem fun a _ => mul_mem (sigR_mem v σ (hu a)) (h a)
  · intro h a
    have h1 := h (B'.1 *ᵥ Pi.single a 1) (by
      rw [mem_latS_latB]
      intro b
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      by_cases hb : b = a
      · subst hb; rw [Pi.single_eq_same]; exact one_mem _
      · rw [Pi.single_eq_of_ne hb]; exact zero_mem _)
    rwa [hform_col, map_one, one_mul] at h1

theorem dual_move (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F)) (L Lb : Submodule (𝓞 E) (Fin n → E))
    (y : GL (Fin n) (E ⊗[F] v.adicCompletion F)) (hJ : IsUnit J.det) (hL : Submodule.IsFullLattice E L)
    (hLb : Submodule.IsFullLattice E Lb) (hy : y ∈ UPts σ J (v.adicCompletion F))
    (hyl : ∀ x, x ∈ latS (F := F) (v.adicCompletion F) (intV E v) L ↔
      (y⁻¹).1 *ᵥ x ∈ latS (F := F) (v.adicCompletion F) (intV E v) Lb) :
    ∀ x, x ∈ latS (F := F) (v.adicCompletion F) (intV E v) (dualL (σ : E →+* E) J L) ↔
      (y⁻¹).1 *ᵥ x ∈ latS (F := F) (v.adicCompletion F) (intV E v) (dualL (σ : E →+* E) J Lb) := by
  have hyU : cT (sigR σ (v.adicCompletion F)) y.1 * J.map (inclE (F := F) (v.adicCompletion F)) * y.1 =
      J.map (inclE (F := F) (v.adicCompletion F)) := hy
  have key : ∀ z x : Fin n → E ⊗[F] v.adicCompletion F,
      hform (sigR σ (v.adicCompletion F)) (J.map (inclE (F := F) (v.adicCompletion F))) z ((y⁻¹).1 *ᵥ x) =
      hform (sigR σ (v.adicCompletion F)) (J.map (inclE (F := F) (v.adicCompletion F))) (y.1 *ᵥ z) x := by
    intro z x
    have e := Formalism.UG.P.hform_mulVec (sigR σ (v.adicCompletion F)) (J.map (inclE (F := F) (v.adicCompletion F)))
      y.1 z ((y⁻¹).1 *ᵥ x)
    rw [hyU, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec] at e
    exact e.symm
  intro x
  rw [mem_latS_dualL σ J hJ v L hL, mem_latS_dualL σ J hJ v Lb hLb]
  refine ⟨fun H z hz => ?_, fun H z hz => ?_⟩
  · rw [key]
    refine H _ ((hyl _).2 ?_)
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    exact hz
  · have h1 := H _ ((hyl z).1 hz)
    rw [key, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec] at h1
    exact h1

end GlobalTheory.DualCompletion

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryCompletionMapsDualLatticesStatement
open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_completion_maps_dualLattices : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F)) (L Lb : Submodule (𝓞 E) (Fin n → E)) (y : GL (Fin n) (E ⊗[F] v.adicCompletion F)), IsUnit J.det → Submodule.IsFullLattice E L → Submodule.IsFullLattice E Lb → y ∈ UPts σ J (v.adicCompletion F) → (∀ x, x ∈ latS (F := F) (v.adicCompletion F) (intV E v) L ↔ (y⁻¹).1 *ᵥ x ∈ latS (F := F) (v.adicCompletion F) (intV E v) Lb) → ∀ x, x ∈ latS (F := F) (v.adicCompletion F) (intV E v) (dualL (σ : E →+* E) J L) ↔ (y⁻¹).1 *ᵥ x ∈ latS (F := F) (v.adicCompletion F) (intV E v) (dualL (σ : E →+* E) J Lb) := by
  first | exact @GlobalTheory.DualCompletion.dual_move | exact GlobalTheory.DualCompletion.dual_move | (intros; apply GlobalTheory.DualCompletion.dual_move <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIdeleAt
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct Kronecker ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OneMapRef.RealMove

theorem exists_factor {m : ℕ} (P : Matrix (Fin m) (Fin m) ℂ) (hP : P * P = P) :
    ∃ (p : ℕ) (U : Matrix (Fin m) (Fin p) ℂ) (V : Matrix (Fin p) (Fin m) ℂ), U * V = P ∧ V * U = 1 := by
  let L := Matrix.toLin' P
  let b := Module.finBasis ℂ (LinearMap.range L)
  let e := Pi.basisFun ℂ (Fin m)
  refine ⟨_, LinearMap.toMatrix b e (LinearMap.range L).subtype, LinearMap.toMatrix e b L.rangeRestrict, ?_, ?_⟩
  · rw [← LinearMap.toMatrix_comp, LinearMap.subtype_comp_codRestrict, LinearMap.toMatrix_eq_toMatrix']
    exact LinearMap.toMatrix'_toLin' P
  · rw [← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_id b]
    congr 1
    ext ⟨_, y, rfl⟩ : 1
    apply Subtype.ext
    show L (L y) = L y
    rw [← LinearMap.comp_apply, ← Matrix.toLin'_mul, hP]

theorem det_idem_kron {m n : ℕ} (P : Matrix (Fin m) (Fin m) ℂ) (hP : P * P = P) :
    ∃ p : ℕ, P.trace = p ∧ ∀ a : Matrix (Fin n) (Fin n) ℂ,
      (P ⊗ₖ a + (1 - P) ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)).det = a.det ^ p := by
  obtain ⟨p, U, V, h1, h2⟩ := exists_factor P hP
  refine ⟨p, by rw [← h1, Matrix.trace_mul_comm, h2]; simp, fun a => ?_⟩
  have e : P ⊗ₖ a + (1 - P) ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) =
      1 + (U ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) * (V ⊗ₖ (a - 1)) := by
    rw [← Matrix.mul_kronecker_mul, h1, Matrix.one_mul, ← Matrix.one_kronecker_one]
    ext ⟨i, j⟩ ⟨k, l⟩
    simp only [Matrix.add_apply, Matrix.kroneckerMap_apply, Matrix.sub_apply]
    ring
  have e2 : 1 + (V ⊗ₖ (a - 1)) * (U ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) = (1 : Matrix (Fin p) (Fin p) ℂ) ⊗ₖ a := by
    rw [← Matrix.mul_kronecker_mul, h2, Matrix.mul_one, ← Matrix.one_kronecker_one]
    ext ⟨i, j⟩ ⟨k, l⟩
    simp only [Matrix.add_apply, Matrix.kroneckerMap_apply, Matrix.sub_apply]
    ring
  rw [e, Matrix.det_one_add_mul_comm, e2, Matrix.det_kronecker]
  simp

theorem detPlus_one {m n : ℕ} (s : Matrix (Fin m) (Fin m) ℂ) (hs : s * s = 1) :
    ∃ p : ℕ, s.trace = 2 * p - m ∧ ∀ (a : Matrix (Fin n) (Fin n) ℂ) (b : Matrix (Fin m) (Fin m) ℂ), s * b = b * s →
      GlobalTheory.WeilParts.detPlus 1 s a b = ((1 / 2 : ℂ) • (1 + s) * b + (1 / 2 : ℂ) • (1 - s)).det ^ n * a.det ^ p ∧
      b.det = ((1 / 2 : ℂ) • (1 + s) * b + (1 / 2 : ℂ) • (1 - s)).det *
        ((1 / 2 : ℂ) • (1 - s) * b + (1 / 2 : ℂ) • (1 + s)).det := by
  obtain ⟨P, hPd⟩ : ∃ P, P = (1 / 2 : ℂ) • (1 + s) := ⟨_, rfl⟩
  have hQ : (1 / 2 : ℂ) • (1 - s) = 1 - P := by rw [hPd]; module
  have hP : P * P = P := by
    rw [hPd, Matrix.smul_mul, Matrix.mul_smul, add_mul, mul_add, mul_add, hs, one_mul, mul_one, one_mul]; module
  obtain ⟨p, hp, hd⟩ := det_idem_kron (n := n) P hP
  refine ⟨p, ?_, fun a b hb => ?_⟩
  · rw [hPd, Matrix.trace_smul, Matrix.trace_add, Matrix.trace_one, Fintype.card_fin, smul_eq_mul] at hp
    linear_combination 2 * hp
  have hc : P * b = b * P := by
    rw [hPd, Matrix.smul_mul, Matrix.mul_smul, add_mul, mul_add, hb, one_mul, mul_one]
  have hc2 : P * b * P = P * b := by rw [mul_assoc, ← hc, ← mul_assoc, hP]
  rw [← hPd, hQ]
  constructor
  · have e1 : (1 / 2 : ℂ) • ((1 + s ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)ᵀ) * (b ⊗ₖ aᵀ)) +
        (1 / 2 : ℂ) • (1 - s ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)ᵀ) =
        (P * b) ⊗ₖ aᵀ + (1 - P) ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) := by
      rw [← hQ, hPd, Matrix.transpose_one, add_mul, ← Matrix.mul_kronecker_mul, Matrix.smul_mul, add_mul, one_mul, one_mul,
        one_mul, ← Matrix.one_kronecker_one]
      ext ⟨i, j⟩ ⟨k, l⟩
      simp only [Matrix.add_apply, Matrix.kroneckerMap_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    have e2 : (P * b) ⊗ₖ aᵀ + (1 - P) ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) =
        ((P * b + (1 - P)) ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) *
          (P ⊗ₖ aᵀ + (1 - P) ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) := by
      have f1 : (P * b + (1 - P)) * P = P * b := by rw [add_mul, hc2, sub_mul, one_mul, hP, sub_self, add_zero]
      have f2 : (P * b + (1 - P)) * (1 - P) = 1 - P := by rw [mul_sub, f1, mul_one]; abel
      rw [mul_add, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, f1, f2, one_mul, one_mul]
    unfold GlobalTheory.WeilParts.detPlus
    rw [e1, e2, Matrix.det_mul, hd, Matrix.det_kronecker]
    simp
  · rw [← Matrix.det_mul]
    congr 1
    have f3 : P * b * ((1 - P) * b) = 0 := by
      rw [← mul_assoc, mul_sub, mul_one, hc2, sub_self, zero_mul]
    have f4 : (1 - P) * ((1 - P) * b) = (1 - P) * b := by
      rw [← mul_assoc, sub_mul, mul_sub, mul_sub, hP]; simp
    have f5 : (1 - P) * P = 0 := by rw [sub_mul, hP, one_mul, sub_self]
    rw [add_mul, mul_add, mul_add, f3, f4, f5, hc2, sub_mul]; simp

variable {D : D7}

theorem hasInfExp_twist {χ η : (AE D)ˣ →* Circle} {τ : D.what₂.Tau} {a : ℚ} (hχ : HasInfExp D χ τ a)
    (hη : HasInfExp D η τ (1 / 2)) (k : ℕ) : HasInfExp D (χ * (η ^ k)⁻¹) τ (a - k / 2) := by
  obtain ⟨n, hn, h0, h⟩ := hχ
  obtain ⟨n', hn', -, h'⟩ := hη
  have e : n' = 1 := by
    have : (n' : ℚ) = 1 := by rw [hn']; norm_num
    exact_mod_cast this
  subst e
  refine ⟨n - k, by push_cast; rw [hn]; ring, h0, fun θ hθ x h1 h2 => ?_⟩
  have hne : θ τ (infPart D (x : AE D)) / (‖θ τ (infPart D (x : AE D))‖ : ℂ) ≠ 0 := by
    have := h' θ hθ x h1 h2
    rw [zpow_one] at this
    rw [← this]; exact Circle.coe_ne_zero _
  rw [zpow_sub₀ hne, ← h θ hθ x h1 h2, zpow_natCast]
  have := h' θ hθ x h1 h2
  rw [zpow_one] at this
  rw [← this]
  simp [div_eq_mul_inv]

theorem adele_ext {θ : InfFam D} (hθ : IsInfFam θ) {x y : AE D} (h1 : finPart D x = finPart D y)
    (h2 : ∀ τ, θ τ (infPart D x) = θ τ (infPart D y)) : x = y := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.FockCompare.exists_chart hθ
  rw [← sub_eq_zero]
  exact hσ.ext _ (by rw [RingHom.map_sub, h1, sub_self]) fun τ => by
    rw [RingHom.map_sub, RingHom.map_sub, h2, sub_self]


open Classical in
theorem exists_idele_at {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (w : ℂ) (hw : w ≠ 0) :
    ∃ x : (AE D)ˣ, finPart D (x : AE D) = 1 ∧ ∀ τ', θ τ' (infPart D (x : AE D)) = if τ' = τ then w else 1 := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.FockCompare.exists_chart hθ
  have key : ∀ w : ℂ, ∃ x : AE D, finPart D x = 1 ∧ ∀ τ', θ τ' (infPart D x) = if τ' = τ then w else 1 := fun w =>
    ⟨1 + σ fun τ' => (if τ' = τ then w else 1) - 1, by rw [RingHom.map_add (f := _), hσ.fin, RingHom.map_one, add_zero], fun τ' => by
      rw [RingHom.map_add (f := _), RingHom.map_add (f := _), hσ.comp, RingHom.map_one, RingHom.map_one]; ring⟩
  obtain ⟨x, hx1, hx2⟩ := key w
  obtain ⟨y, hy1, hy2⟩ := key w⁻¹
  have hxy : x * y = 1 := adele_ext hθ (by rw [RingHom.map_mul, hx1, hy1, RingHom.map_one, one_mul]) fun τ' => by
    rw [RingHom.map_mul, RingHom.map_mul, hx2, hy2, RingHom.map_one, RingHom.map_one]
    split_ifs
    · exact mul_inv_cancel₀ hw
    · exact one_mul 1
  have hyx : y * x = 1 := (mul_comm y x).trans hxy
  refine ⟨⟨x, y, hxy, hyx⟩, ?_, ?_⟩
  · rw [Units.val_mk]; exact hx1
  · rw [Units.val_mk]; exact hx2

theorem det_compAt (θ : InfFam D) (τ : D.what₂.Tau) {k : ℕ} (M : Matrix (Fin k) (Fin k) (AE D)) :
    (compAt θ τ M).det = θ τ (infPart D M.det) :=
  (RingHom.map_det ((θ τ).comp (infPart D)) M).symm

theorem finPart_cA (z : AE D) (hz : finPart D z = 1) : finPart D (cA D z) = 1 := by
  have key : ∀ z : AE D, finPart D (cA D z) = sigR (Af D.host.F) D.sp.cm.sig (finPart D z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul a x => rfl
  rw [key, hz, map_one]

theorem exists_root {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (hV : ∀ τ, (gramAt D V τ).det ≠ 0)
    (g : GA D V) (hg : g ∈ GinfC V) :
    ∃ x, IsDetRoot V g x ∧ ∀ (ν : (AE D)ˣ →* Circle) (c : D.what₂.Tau → ℤ), (∀ τ, HasInfExp D ν τ (c τ)) →
      ((ν x : Circle) : ℂ) = ∏ τ, (compAt θ τ (Formalism.L2.Theta.mt V g)).det ^ c τ := by
  classical
  have hu : ∀ τ, ‖(compAt θ τ (Formalism.L2.Theta.mt V g)).det‖ = 1 := fun τ => by
    have h : (compAt θ τ (Formalism.L2.Theta.mt V g))ᴴ * gramAt D V τ * compAt θ τ (Formalism.L2.Theta.mt V g) = gramAt D V τ :=
      GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V g τ
    have h2 := congrArg (fun M => ‖Matrix.det M‖) h
    simp only [Matrix.det_mul, Matrix.det_conjTranspose, norm_mul, norm_star] at h2
    have h3 : ‖(gramAt D V τ).det‖ ≠ 0 := norm_ne_zero_iff.2 (hV τ)
    have h4 : ‖(compAt θ τ (Formalism.L2.Theta.mt V g)).det‖ ^ 2 = 1 := by
      apply mul_left_cancel₀ h3; linear_combination h2
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h4
  have hw : ∀ τ, ∃ w : ℂ, w ^ 2 = (compAt θ τ (Formalism.L2.Theta.mt V g)).det ∧ ‖w‖ = 1 := fun τ => by
    obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (compAt θ τ (Formalism.L2.Theta.mt V g)).det two_pos
    refine ⟨w, hw, (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 ?_⟩
    rw [← norm_pow, hw, hu]
  choose w hw1 hw2 using hw
  have hw0 : ∀ τ, w τ ≠ 0 := fun τ h => by simpa [h] using hw2 τ
  choose x hx1 hx2 using fun τ => exists_idele_at hθ τ (w τ) (hw0 τ)
  have hf : finPart D ((∏ τ, x τ : (AE D)ˣ) : AE D) = 1 := by
    rw [Units.coe_prod, map_prod]; exact Finset.prod_eq_one fun τ _ => hx1 τ
  have hi : ∀ τ, θ τ (infPart D ((∏ τ, x τ : (AE D)ˣ) : AE D)) = w τ := fun τ => by
    rw [Units.coe_prod, map_prod, map_prod]
    simp [hx2]
  refine ⟨∏ τ, x τ, ?_, fun ν c hc => ?_⟩
  · refine adele_ext hθ ?_ fun τ => ?_
    · have hd : finPart D (Formalism.L2.Theta.mt V g).det = 1 := by
        have hg' : finHom V g = 1 := hg
        have : (Formalism.L2.Theta.mt V g).map (finPart D) = 1 := congrArg Units.val hg'
        rw [RingHom.map_det]
        exact (congrArg Matrix.det this).trans Matrix.det_one
      rw [map_mul, hf]
      exact ((congrArg₂ (· * ·) hd (finPart_cA _ hf)).trans (one_mul 1)).symm
    · rw [map_mul, map_mul, hi]
      have e1 := GlobalTheory.FockCompare.comp_cA hθ τ ((∏ τ, x τ : (AE D)ˣ) : AE D)
      have e2 := det_compAt θ τ (Formalism.L2.Theta.mt V g)
      rw [hi] at e1
      refine Eq.trans ?_ (congrArg₂ (· * ·) e2 e1.symm)
      have : w τ * starRingEnd ℂ (w τ) = 1 := by rw [Complex.mul_conj', hw2]; simp
      rw [← hw1]; linear_combination (-w τ) * this
  · rw [map_prod]
    rw [show ((∏ τ, ν (x τ) : Circle) : ℂ) = ∏ τ, (ν (x τ) : ℂ) from map_prod Circle.coeHom _ _]
    refine Finset.prod_congr rfl fun τ _ => ?_
    obtain ⟨n, hn, -, h⟩ := hc τ
    have e : n = 2 * c τ := by exact_mod_cast hn
    rw [h θ hθ (x τ) (hx1 τ) (fun τ' h' => by rw [hx2, if_neg h']), hx2, if_pos rfl, hw2, e, ← hw1, _root_.zpow_mul]
    simp

end GlobalTheory.OneMapRef.RealMove

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsUnitaryAdelicVolumeMeasure
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatCFullLattice
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open Formalism.MainNotions.S hiding Af
open scoped TensorProduct

namespace GlobalTheory.Mem.Vol

theorem latC_full_lattice : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (W : HSpace E), ∃ L : Submodule (𝓞 E) (Fin W.rank → E), (L : Set (Fin W.rank → E)) = latC W ∧ L.FG ∧ Submodule.span E (L : Set (Fin W.rank → E)) = ⊤ := by
  intro E _ _ _ W
  refine ⟨W.L0.map (W.frame.equivFun.toLinearMap.restrictScalars (𝓞 E)), ?_, W.standardTuple_isLattice.fg.map _, ?_⟩
  · ext x
    simp only [latC, SetLike.mem_coe, Submodule.mem_map, Set.mem_ofPred_eq]
    rw [← W.frame.equivFun_symm_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro h
      exact ⟨_, h, W.frame.equivFun.apply_symm_apply x⟩
  · have h : Submodule.span E (W.L0 : Set W.V) = ⊤ := by
      let U := Submodule.span E (W.L0 : Set W.V)
      change U = ⊤
      by_contra h
      let e : W.V ≃ₗ⋆[E] W.V :=
        (W.frame.equivFun.trans (starLinearEquiv E)).trans W.frame.equivFun.symm
      let g : W.V →ₗ[E] Module.Dual E U :=
        (LinearMap.domRestrict' U).comp (W.hT.comp e.toLinearMap)
      have hdim : Module.finrank E (Module.Dual E U) < Module.finrank E W.V := by
        rw [Subspace.dual_finrank_eq]
        exact Submodule.finrank_lt h
      obtain ⟨z, hz, hz₀⟩ :=
        Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
      have hsmul (a : E) : a • e z ∈ W.L0 := by
        rw [← W.baseLattice_isUnimodular]
        simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual,
          Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]
        intro y hy
        have hzy : W.hT (e z) y = 0 :=
          congrArg (fun f : Module.Dual E U => f ⟨y, Submodule.subset_span hy⟩)
            (LinearMap.mem_ker.mp hz)
        have hyz : W.hT y (e z) = 0 := by
          have hh := W.herm.eq (e z) y
          simpa [hzy] using hh.symm
        simp [hyz]
      let i : E →ₗ[𝓞 E] W.L0 :=
        ((LinearMap.toSpanSingleton E _ (e z)).restrictScalars (𝓞 E)).codRestrict W.L0 hsmul
      let : Module.Finite (𝓞 E) W.L0 := Module.Finite.iff_fg.mpr W.standardTuple_isLattice.fg
      let : Module.Finite (𝓞 E) E := Module.Finite.of_injective i fun a b hab =>
        smul_left_injective E (fun hzero => hz₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
      exact RingOfIntegers.not_isField E
        (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 E) E) (Field.toIsField E))
    have : ((W.L0.map (W.frame.equivFun.toLinearMap.restrictScalars (𝓞 E)) : Submodule (𝓞 E) (Fin W.rank → E)) :
        Set (Fin W.rank → E)) = W.frame.equivFun.toLinearMap '' (W.L0 : Set W.V) := rfl
    rw [this, ← Submodule.map_span, h, Submodule.map_top, LinearEquiv.range]

end GlobalTheory.Mem.Vol
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsUnitaryAdelicVolumeMeasure
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open Formalism.MainNotions.S hiding Af
open scoped TensorProduct

namespace GlobalTheory.Mem.VolExists

theorem exists_haar_prod {G H I : Type} [Fintype I] {U : I → Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] [T2Space G]
    [Group H] [TopologicalSpace H] [∀ i, Group (U i)] [∀ i, TopologicalSpace (U i)]
    [∀ i, IsTopologicalGroup (U i)] [∀ i, MeasurableSpace (U i)] [∀ i, BorelSpace (U i)]
    [∀ i, SecondCountableTopology (U i)] [∀ i, LocallyCompactSpace (U i)]
    (ν : ∀ i, Measure (U i)) [∀ i, (ν i).IsHaarMeasure] (e : G ≃ₜ* (∀ i, U i) × H) (K : Subgroup H)
    (hKo : IsOpen (K : Set H)) (hKc : IsCompact (K : Set H)) :
    ∃ μ : Measure G, μ.IsHaarMeasure ∧ ∀ B : ∀ i, Set (U i), (∀ i, MeasurableSet (B i)) →
      μ {h | (e h).2 ∈ K ∧ ∀ i, (e h).1 i ∈ B i} = ∏ i, ν i (B i) := by
  let j : H →* G := (e.symm.toMulEquiv.toMonoidHom).comp (MonoidHom.inr _ _)
  have hj : Topology.IsEmbedding j :=
    e.symm.toHomeomorph.isEmbedding.comp (isEmbedding_prodMkRight (1 : ∀ i, U i))
  haveI : IsTopologicalGroup H := hj.isInducing.topologicalGroup j
  haveI : SecondCountableTopology H := hj.secondCountableTopology
  haveI : T2Space H := hj.t2Space
  haveI : LocallyCompactSpace H :=
    hKc.locallyCompactSpace_of_mem_nhds_of_group (hKo.mem_nhds K.one_mem)
  letI : MeasurableSpace H := borel H
  haveI : BorelSpace H := ⟨rfl⟩
  let K0 : TopologicalSpace.PositiveCompacts H :=
    ⟨⟨K, hKc⟩, by
      show (interior (K : Set H)).Nonempty
      rw [hKo.interior_eq]; exact ⟨1, K.one_mem⟩⟩
  let m : Measure ((∀ i, U i) × H) := (Measure.pi ν).prod (Measure.haarMeasure K0)
  haveI : m.IsHaarMeasure := inferInstanceAs (((Measure.pi ν).prod (Measure.haarMeasure K0)).IsHaarMeasure)
  refine ⟨m.map e.symm, e.symm.isHaarMeasure_map m, fun B hB => ?_⟩
  have hme : MeasurableEmbedding e.symm := e.symm.toHomeomorph.measurableEmbedding
  rw [hme.map_apply]
  have : e.symm ⁻¹' {h | (e h).2 ∈ K ∧ ∀ i, (e h).1 i ∈ B i} = (Set.univ.pi B) ×ˢ (K : Set H) := by
    ext x
    simp [and_comm]
  rw [this, Measure.prod_prod, Measure.pi_pi]
  have h1 : Measure.haarMeasure K0 (K : Set H) = 1 := Measure.haarMeasure_self
  rw [h1, mul_one]

theorem mat_mul {P Q : ℕ} (a b : UpqT P Q) : UpqT.mat (a * b) = UpqT.mat a * UpqT.mat b := rfl

theorem mat_one {P Q : ℕ} : UpqT.mat (1 : UpqT P Q) = 1 := rfl

theorem exists_upq_mul {P Q M : ℕ} (A A' : Matrix (Fin P ⊕ Fin Q) (Fin M) ℂ)
    (B B' : Matrix (Fin M) (Fin P ⊕ Fin Q) ℂ) (h1 : A * B = 1) (h2 : B * A = 1) (h3 : A' * B' = 1)
    (h4 : B' * A' = 1) (h : Aᴴ * Formalism.UG.Jpq P Q * A = A'ᴴ * Formalism.UG.Jpq P Q * A') :
    ∃ u : UpqT P Q, UpqT.mat u * A = A' := by
  let g : GL (Fin P ⊕ Fin Q) ℂ := ⟨A' * B, A * B',
    by rw [Matrix.mul_assoc, ← Matrix.mul_assoc B, h2, Matrix.one_mul, h3],
    by rw [Matrix.mul_assoc, ← Matrix.mul_assoc B', h4, Matrix.one_mul, h1]⟩
  have hg : g ∈ Formalism.UG.Upq P Q := by
    show (A' * B)ᴴ * Formalism.UG.Jpq P Q * (A' * B) = Formalism.UG.Jpq P Q
    calc (A' * B)ᴴ * Formalism.UG.Jpq P Q * (A' * B) = Bᴴ * (A'ᴴ * Formalism.UG.Jpq P Q * A') * B := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (A * B)ᴴ * Formalism.UG.Jpq P Q * (A * B) := by
          rw [← h]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Formalism.UG.Jpq P Q := by rw [h1]; simp
  refine ⟨(⟨g, hg⟩ : Formalism.UG.Upq P Q), ?_⟩
  show A' * B * A = A'
  rw [Matrix.mul_assoc, h2, Matrix.mul_one]

theorem exists_isVolMeasF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (I : Type) [Fintype I] (τ : I → (E →+* ℂ)) (cd : CDHaar) (W : HSpace E), IsCMFam τ → W.SigOK → ∃ μ, IsVolMeasF cm τ cd W (fun ρ => (W.sig (τ ρ)).1) (fun ρ => (W.sig (τ ρ)).2) μ := by
  intro F E _ _ _ _ _ _ cm I _ τ cd W hτ hW
  obtain ⟨hcm, -⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND F E cm
  have hθ := GlobalTheory.Mem.VolEmb.existsUnique_infEmb F E cm.sig hcm
  choose θ hθ1 hθ2 using fun i => hθ (τ i)
  have hA := fun i => GlobalTheory.Mem.SignatureFactor.exists_factor _ _ _ _ (hW (τ i))
  choose A hA1 using fun i => (hA i).2.1
  obtain ⟨e1, he1⟩ := GlobalTheory.T.unitaryGroup_realPoints_equiv_pi_indefiniteUnitary F E cm.sig W.rank W.gram I τ θ (fun ρ => (W.sig (τ ρ)).1)
    (fun ρ => (W.sig (τ ρ)).2) A hcm hτ hθ1 (fun i => hW (τ i)) hA1
  obtain ⟨e0, he0⟩ := GlobalTheory.Mem.VolSplit.exists_adelic_split F E cm.sig W.rank W.gram
  obtain ⟨L, hL, hLfg, hLsp⟩ := GlobalTheory.Mem.Vol.latC_full_lattice E W
  obtain ⟨K, hK, hKo, hKc⟩ := GlobalTheory.T.completedLattice_stabilizer_compact_open F E cm.sig W.rank W.gram L hLfg hLsp
  obtain ⟨-, hsc, ht2⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary F E cm.sig W.rank W.gram
  haveI : IsTopologicalGroup (HA (AF F) cm.sig W.gram) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : BorelSpace (HA (AF F) cm.sig W.gram) := ⟨rfl⟩
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.2.1
  have hinj := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.2.2.injective
  haveI := cd.haar
  let e : HA (AF F) cm.sig W.gram ≃ₜ*
      (∀ i, UpqT (W.sig (τ i)).1 (W.sig (τ i)).2) × HA (Af F) cm.sig W.gram :=
    e0.trans
      { e1.toMulEquiv.prodCongr (MulEquiv.refl _) with
        continuous_toFun := e1.continuous_toFun.prodMap continuous_id
        continuous_invFun := e1.continuous_invFun.prodMap continuous_id }
  have hee : ∀ h, e h = (e1 (e0 h).1, (e0 h).2) := fun h => rfl
  obtain ⟨μ, hμ, hμB⟩ := exists_haar_prod (fun i => cd.cd (W.sig (τ i)).1 (W.sig (τ i)).2) e K hKo hKc
  refine ⟨μ, hμ, ⟨θ, hθ1⟩, fun θ' hθ' => ?_⟩
  obtain rfl : θ' = θ := funext fun i => hθ2 i _ (hθ' i)
  refine ⟨⟨A, hA1⟩, fun A' hA' B hB => ?_⟩
  have hu : ∀ i, ∃ u : UpqT (W.sig (τ i)).1 (W.sig (τ i)).2, UpqT.mat u * A i = A' i := by
    intro i
    obtain ⟨C, h1, h2⟩ := (hA i).2.2 _ (hA1 i)
    obtain ⟨C', h3, h4⟩ := (hA i).2.2 _ (hA' i)
    exact exists_upq_mul _ _ C C' h1 h2 h3 h4 ((hA1 i).trans (hA' i).symm)
  choose u hu using hu
  have key := hμB (fun i => (fun g => u i * g) ⁻¹' ((fun g => g * (u i)⁻¹) ⁻¹' B i))
    (fun i => measurable_const_mul _ (measurable_mul_const _ (hB i)))
  have hcj : ∀ i, cd.cd (W.sig (τ i)).1 (W.sig (τ i)).2
      ((fun g => u i * g) ⁻¹' ((fun g => g * (u i)⁻¹) ⁻¹' B i)) =
      cd.cd (W.sig (τ i)).1 (W.sig (τ i)).2 (B i) := by
    intro i
    haveI := GlobalTheory.UpqHaarRight.isMulRightInvariant _ _ _ (cd.haar (W.sig (τ i)).1 (W.sig (τ i)).2)
    rw [measure_preimage_mul, measure_preimage_mul_right]
  rw [Finset.prod_congr rfl (fun i _ => hcj i)] at key
  rw [← key]
  congr 1
  ext h
  simp only [Set.mem_setOf_eq, hee, Set.mem_preimage]
  rw [hK, (he0 h).1, hL]
  refine and_congr_right fun _ => forall_congr' fun i => ?_
  have h1 : UpqT.mat (e1 (e0 h).1 i) * A i = A i * infMat cm.sig W.gram (θ' i) h := by
    rw [he1, (he0 h).2]; rfl
  have h2 : UpqT.mat (u i * e1 (e0 h).1 i * (u i)⁻¹) * A' i = A' i * infMat cm.sig W.gram (θ' i) h := by
    have h3 : UpqT.mat (u i)⁻¹ * A' i = A i := by
      rw [← hu i, ← Matrix.mul_assoc, ← mat_mul, inv_mul_cancel, mat_one, Matrix.one_mul]
    rw [mat_mul, mat_mul, Matrix.mul_assoc, h3, Matrix.mul_assoc, h1, ← Matrix.mul_assoc, hu i]
  constructor
  · rintro ⟨b, hb, hbe⟩
    obtain ⟨C', h3, -⟩ := (hA i).2.2 _ (hA' i)
    have : b = u i * e1 (e0 h).1 i * (u i)⁻¹ := by
      apply hinj
      have h5 := congrArg (· * C') (hbe.trans h2.symm)
      simpa only [Matrix.mul_assoc, h3, Matrix.mul_one] using h5
    exact this ▸ hb
  · intro hb
    exact ⟨_, hb, h2⟩

end GlobalTheory.Mem.VolExists
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsUnitaryAdelicVolumeMeasureStatement
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open Formalism.MainNotions.S hiding Af
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isUnitaryAdelicVolumeMeasure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (I : Type) [Fintype I] (τ : I → (E →+* ℂ)) (cd : CDHaar) (W : HSpace E), IsCMFam τ → W.SigOK → ∃ μ, IsVolMeasF cm τ cd W (fun ρ => (W.sig (τ ρ)).1) (fun ρ => (W.sig (τ ρ)).2) μ := by
  first | exact @GlobalTheory.Mem.VolExists.exists_isVolMeasF | exact GlobalTheory.Mem.VolExists.exists_isVolMeasF | (intros; apply GlobalTheory.Mem.VolExists.exists_isVolMeasF <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiscreteCountableGQ
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta NumberField
open scoped TensorProduct

namespace GlobalTheory.RationalCountable

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem discrete_countable_GQ :
    ∀ (D : D7) (V : HSp D), DiscreteTopology (GQ V) ∧ Countable (GQ V) :=
  fun D V => ⟨GlobalTheory.RationalDiscrete.discreteTopology_GQ D V,
    Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig V.gram⟩

end GlobalTheory.RationalCountable
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsUnitDetOneSubConjTransposeMulContractions
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsUnitDetOneSubConjTransposeMulContractions
open Matrix
open scoped ComplexOrder

namespace GlobalTheory

theorem isUnit_det_one_sub_conjTranspose_mul_of_contractions (P Q : ℕ)
    (A B : Matrix (Fin P) (Fin Q) ℂ) (hA : (1 - Aᴴ * A).PosDef) (hB : (1 - Bᴴ * B).PosDef) :
    IsUnit (1 - Aᴴ * B).det := by
  rw [isUnit_iff_ne_zero]
  intro h
  obtain ⟨u, hu, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  have hsum : ((1 - Aᴴ * A) + (1 - Bᴴ * B) + (A - B)ᴴ * (A - B)).PosDef :=
    (hA.add hB).add_posSemidef (Matrix.posSemidef_conjTranspose_mul_self _)
  have heq : (1 - Aᴴ * A) + (1 - Bᴴ * B) + (A - B)ᴴ * (A - B)
      = (1 - Aᴴ * B) + (1 - Aᴴ * B)ᴴ := by
    simp only [conjTranspose_sub, conjTranspose_one, conjTranspose_mul,
      conjTranspose_conjTranspose, Matrix.sub_mul, Matrix.mul_sub]
    abel
  rw [heq] at hsum
  have hpos := hsum.dotProduct_mulVec_pos hu
  have h2 : star u ⬝ᵥ ((1 - Aᴴ * B)ᴴ *ᵥ u) = 0 := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, h0]
    simp
  rw [Matrix.add_mulVec, dotProduct_add, h0, h2] at hpos
  simp at hpos

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsUnitDetOneSubConjTransposeMulContractionsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnit_det_one_sub_conjTranspose_mul_contractions : ∀ (P Q : ℕ) (A B : Matrix (Fin P) (Fin Q) ℂ), (1 - Aᴴ * A).PosDef → (1 - Bᴴ * B).PosDef → IsUnit (1 - Aᴴ * B).det := by
  first | exact @GlobalTheory.isUnit_det_one_sub_conjTranspose_mul_of_contractions | exact GlobalTheory.isUnit_det_one_sub_conjTranspose_mul_of_contractions | (intros; apply GlobalTheory.isUnit_det_one_sub_conjTranspose_mul_of_contractions <;> assumption)
end
end
