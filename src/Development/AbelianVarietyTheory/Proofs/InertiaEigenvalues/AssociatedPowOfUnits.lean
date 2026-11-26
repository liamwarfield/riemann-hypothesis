module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ForallFieldIffForallSubgroup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteSemisimple
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompactGroupRepDefinedOverFiniteExtension
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConvZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormUnitPowSubOne
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CellDef

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AssociatedPowOfUnits
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.BdRDVR

section General

variable {R : Type*} [CommRing R]

theorem irreducible_of_units [IsDomain R] {x : R} (hx0 : x ≠ 0) (hxu : ¬ IsUnit x)
    (hu : ∀ y : R, ¬ x ∣ y → IsUnit y) : Irreducible x := by
  refine ⟨hxu, fun a b hab => ?_⟩
  by_cases ha : x ∣ a
  · right
    obtain ⟨c, rfl⟩ := ha
    have h1 : x * 1 = x * (c * b) := by rw [mul_one, ← mul_assoc]; exact hab
    have h2 := mul_left_cancel₀ hx0 h1
    exact IsUnit.of_mul_eq_one_right c h2.symm
  · exact Or.inl (hu a ha)

theorem associated_pow_of_units {x : R} (hu : ∀ y : R, ¬ x ∣ y → IsUnit y)
    [IsHausdorff (Ideal.span {x}) R] {y : R} (hy : y ≠ 0) : ∃ n : ℕ, Associated (x ^ n) y := by
  classical
  have hex : ∃ n : ℕ, ¬ x ^ n ∣ y := by
    by_contra h
    push_neg at h
    apply hy
    refine IsHausdorff.haus (I := Ideal.span {x}) inferInstance y fun n => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact h n
  have hN := Nat.find_spec hex
  have hN0 : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hN
    exact hN (one_dvd _)
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hN0
  have hmin : x ^ m ∣ y := by
    have := Nat.find_min hex (m := m) (by omega)
    exact not_not.1 this
  obtain ⟨c, rfl⟩ := hmin
  have hc : IsUnit c := hu c fun hxc => hN (by
    rw [hm, pow_succ]
    exact mul_dvd_mul_left _ hxc)
  exact ⟨m, hc.unit, rfl⟩

end General

theorem core_dvr (l : ℕ) [Fact l.Prime] (C : Core l) : C.DVR := by
  have he := core_isEps l C
  obtain ⟨hdom, hinj, hfield, hden⟩ := BdRField.bdR_isField l
  obtain ⟨hfil, hreg, hcomp, -⟩ := filtration_eq_xi_pow l C.ε he
  obtain ⟨-, hker, hunit, -, -⟩ := thetaD_props l
  obtain ⟨-, ht1, ht2, -⟩ := core_t_unit_fil l C
  have hden' := hden C.ε he
  clear hden
  generalize aDp l (xi C.ε) = x at hfil hreg hcomp hden'
  have hθ : ∀ y : Per.BdRp l, Per.θD l y = 0 ↔ x ∣ y := fun y => by
    rw [hker, hfil, pow_one]
  have hu : ∀ y : Per.BdRp l, ¬ x ∣ y → IsUnit y := fun y hy => hunit y fun h => hy ((hθ y).1 h)
  have hx0 : x ≠ 0 := fun h => one_ne_zero (hreg 1 (by rw [h, zero_mul]))
  have hxu : ¬ IsUnit x := fun h => (h.map (Per.θD l)).ne_zero ((hθ x).2 dvd_rfl)
  have hirr : Irreducible x := irreducible_of_units hx0 hxu hu
  haveI : IsHausdorff (Ideal.span {x}) (Per.BdRp l) := hcomp.toIsHausdorff
  haveI hdvr : IsDiscreteValuationRing (Per.BdRp l) :=
    IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
      ⟨x, hirr, fun hy => associated_pow_of_units hu hy⟩
  have hmax : IsLocalRing.maximalIdeal (Per.BdRp l) = Ideal.span {x} := hirr.maximalIdeal_eq
  have hassoc : Associated x (C.j C.t) := by
    obtain ⟨c, hc⟩ := (hfil 1 _).1 ht1
    rw [pow_one] at hc
    have hcu : IsUnit c := hu c fun hxc => ht2 ((hfil 2 _).2 (by
      rw [hc, pow_two]
      exact mul_dvd_mul_left _ hxc))
    exact ⟨hcu.unit, hc.symm⟩
  refine ⟨hdom, hdvr, ?_, ?_, ?_, fun n => ?_, ?_⟩
  · rw [hmax]
    exact Ideal.span_singleton_eq_span_singleton.2 hassoc
  · rw [hmax]
    ext y
    rw [Ideal.mem_span_singleton, RingHom.mem_ker, hθ]
  · rw [hmax]
    exact hcomp
  · ext y
    rw [hfil, Ideal.mem_span_singleton]
    exact (hassoc.pow_pow (n := n)).dvd_iff_dvd_left
  · refine (isLocalization_iff _ _).2 ⟨fun y => ?_, fun z => ?_, fun {a b} h => ⟨1, by rw [hinj h]⟩⟩
    · have hy : algebraMap (Per.BdRp l) (Per.BdR l) y ≠ 0 := fun h =>
        nonZeroDivisors.ne_zero y.2 (hinj (h.trans (map_zero _).symm))
      obtain ⟨b, hb⟩ := hfield.mul_inv_cancel hy
      exact IsUnit.of_mul_eq_one b hb
    · obtain ⟨n, y, h⟩ := hden' z
      exact ⟨(y, ⟨x ^ n, mem_nonZeroDivisors_of_ne_zero (pow_ne_zero n hx0)⟩), by
        simpa only [map_pow] using h⟩

end GlobalTheory.MemLoc.BdRDVR
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAddValuationFinExt
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Per

namespace GlobalTheory.Per.Val

variable {l : ℕ} [Fact l.Prime]

open Polynomial in
theorem _root_.GlobalTheory.Per.Val.exists_norm_eq (x : _root_.Formalism.BasicNotions.Loc.Om l) (hx : x ≠ 0) :
    ∃ q : ℚ, ‖x‖ = (l : ℝ) ^ (-(q : ℝ)) := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have hc := minpoly.coeff_zero_ne_zero hi hx
  have hn : (minpoly ℚ_[l] x).natDegree ≠ 0 := (minpoly.natDegree_pos hi).ne'
  refine ⟨((minpoly ℚ_[l] x).coeff 0).valuation / (minpoly ℚ_[l] x).natDegree, ?_⟩
  have h1 : ‖x‖ = ‖(minpoly ℚ_[l] x).coeff 0‖ ^ (1 / ((minpoly ℚ_[l] x).natDegree : ℝ)) :=
    spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow ℚ_[l] (_root_.Formalism.BasicNotions.Loc.Om l) x
  rw [h1, Padic.norm_eq_zpow_neg_valuation hc, ← Real.rpow_intCast,
    ← Real.rpow_mul (Nat.cast_nonneg l)]
  congr 1
  have hn' : ((minpoly ℚ_[l] x).natDegree : ℝ) ≠ 0 := by exact_mod_cast hn
  push_cast
  field_simp

open Polynomial in
theorem _root_.GlobalTheory.Per.Val.mem_OL_iff (LL : _root_.Formalism.BasicNotions.Loc.FinExt l) (x : ↥LL.1) :
    x ∈ _root_.Formalism.BasicNotions.Loc.OL LL ↔ ‖(x : _root_.Formalism.BasicNotions.Loc.Om l)‖ ≤ 1 := by
  haveI := LL.2
  unfold _root_.Formalism.BasicNotions.Loc.OL
  rw [mem_integralClosure_iff]
  have hK : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have hnorm : ‖(x : _root_.Formalism.BasicNotions.Loc.Om l)‖ = spectralValue (minpoly ℚ_[l] x) := by
    rw [IntermediateField.minpoly_eq x]; rfl
  rw [hnorm, spectralValue_le_one_iff (minpoly.monic hK)]
  constructor
  · intro hi n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] hi, coeff_map]
    simpa using PadicInt.norm_le_one ((minpoly ℤ_[l] x).coeff n)
  · intro h
    have hl : minpoly ℚ_[l] x ∈ lifts (algebraMap ℤ_[l] ℚ_[l]) := by
      rw [lifts_iff_coeff_lifts]
      intro n
      exact ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hm⟩ := lifts_and_natDegree_eq_and_monic hl (minpoly.monic hK)
    refine ⟨q, hm, ?_⟩
    rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] ↥LL.1, ← eval₂_map, hq]
    exact minpoly.aeval ℚ_[l] x

open Classical in
def vf (x : Om l) : WithTop ℚ := if h : x = 0 then ⊤ else ((exists_norm_eq x h).choose : ℚ)

open Polynomial in
private theorem exists_rat_vf_eq_norm_eq_rpow_of_ne_zero {x : _root_.Formalism.BasicNotions.Loc.Om l} (hx : x ≠ 0) :
    ∃ q : ℚ, _root_.GlobalTheory.Per.Val.vf x = q ∧ ‖x‖ = (l : ℝ) ^ (-(q : ℝ)) :=
  ⟨_, by simp [_root_.GlobalTheory.Per.Val.vf, hx],
    (_root_.GlobalTheory.Per.Val.exists_norm_eq x hx).choose_spec⟩

open Polynomial in
private theorem prime_rpow_neg_le_iff (a b : ℚ) :
    (l : ℝ) ^ (-(a : ℝ)) ≤ (l : ℝ) ^ (-(b : ℝ)) ↔ b ≤ a := by
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  rw [Real.rpow_le_rpow_left_iff hl, neg_le_neg_iff]
  exact_mod_cast Iff.rfl

open Polynomial in
private theorem prime_rpow_neg_inj (a b : ℚ) :
    (l : ℝ) ^ (-(a : ℝ)) = (l : ℝ) ^ (-(b : ℝ)) ↔ a = b := by
  constructor
  · intro h
    exact le_antisymm ((prime_rpow_neg_le_iff b a).1 h.ge) ((prime_rpow_neg_le_iff a b).1 h.le)
  · rintro rfl; rfl

open Polynomial in
theorem _root_.GlobalTheory.Per.Val.vf_eq_iff (x : _root_.Formalism.BasicNotions.Loc.Om l) (q : ℚ) :
    _root_.GlobalTheory.Per.Val.vf x = (q : WithTop ℚ) ↔ ‖x‖ = (l : ℝ) ^ (-(q : ℝ)) := by
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  by_cases hx : x = 0
  · subst hx
    simp only [_root_.GlobalTheory.Per.Val.vf, dif_pos, norm_zero, WithTop.top_ne_coe, false_iff]
    exact (Real.rpow_pos_of_pos hl _).ne
  · obtain ⟨a, ha, hn⟩ := exists_rat_vf_eq_norm_eq_rpow_of_ne_zero hx
    rw [ha, hn, WithTop.coe_eq_coe, prime_rpow_neg_inj]

open Polynomial in
theorem _root_.GlobalTheory.Per.Val.vf_zero : _root_.GlobalTheory.Per.Val.vf (0 : _root_.Formalism.BasicNotions.Loc.Om l) = ⊤ := by
  simp [_root_.GlobalTheory.Per.Val.vf]

open Polynomial in
theorem _root_.GlobalTheory.Per.Val.le_vf_iff (x : _root_.Formalism.BasicNotions.Loc.Om l) (q : ℚ) :
    (q : WithTop ℚ) ≤ _root_.GlobalTheory.Per.Val.vf x ↔ ‖x‖ ≤ (l : ℝ) ^ (-(q : ℝ)) := by
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  by_cases hx : x = 0
  · subst hx
    simp only [_root_.GlobalTheory.Per.Val.vf_zero, le_top, norm_zero, true_iff]
    exact (Real.rpow_pos_of_pos hl _).le
  · obtain ⟨a, ha, hn⟩ := exists_rat_vf_eq_norm_eq_rpow_of_ne_zero hx
    rw [ha, hn, WithTop.coe_le_coe, prime_rpow_neg_le_iff]

open Polynomial in
theorem _root_.GlobalTheory.Per.Val.vf_mul (x y : _root_.Formalism.BasicNotions.Loc.Om l) :
    _root_.GlobalTheory.Per.Val.vf (x * y) =
      _root_.GlobalTheory.Per.Val.vf x + _root_.GlobalTheory.Per.Val.vf y := by
  by_cases hx : x = 0
  · simp [hx, _root_.GlobalTheory.Per.Val.vf_zero]
  by_cases hy : y = 0
  · simp [hy, _root_.GlobalTheory.Per.Val.vf_zero]
  obtain ⟨a, ha, hna⟩ := exists_rat_vf_eq_norm_eq_rpow_of_ne_zero hx
  obtain ⟨b, hb, hnb⟩ := exists_rat_vf_eq_norm_eq_rpow_of_ne_zero hy
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  rw [ha, hb, ← WithTop.coe_add, _root_.GlobalTheory.Per.Val.vf_eq_iff, norm_mul, hna, hnb,
    ← Real.rpow_add hl]
  push_cast
  ring_nf

open Polynomial in
theorem _root_.GlobalTheory.Per.Val.vf_add (x y : _root_.Formalism.BasicNotions.Loc.Om l) :
    min (_root_.GlobalTheory.Per.Val.vf x) (_root_.GlobalTheory.Per.Val.vf y) ≤
      _root_.GlobalTheory.Per.Val.vf (x + y) := by
  by_cases hxy : x + y = 0
  · simp [hxy, _root_.GlobalTheory.Per.Val.vf_zero]
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  obtain ⟨a, ha, hna⟩ := exists_rat_vf_eq_norm_eq_rpow_of_ne_zero hx
  obtain ⟨b, hb, hnb⟩ := exists_rat_vf_eq_norm_eq_rpow_of_ne_zero hy
  obtain ⟨c, hc, hnc⟩ := exists_rat_vf_eq_norm_eq_rpow_of_ne_zero hxy
  rw [ha, hb, hc, ← WithTop.coe_min, WithTop.coe_le_coe]
  have hmax : ‖x + y‖ ≤ max ‖x‖ ‖y‖ := IsUltrametricDist.norm_add_le_max x y
  rw [hna, hnb, hnc] at hmax
  rcases le_total a b with h | h
  · rw [min_eq_left h]
    rw [max_eq_left ((prime_rpow_neg_le_iff b a).2 h), prime_rpow_neg_le_iff] at hmax
    exact hmax
  · rw [min_eq_right h]
    rw [max_eq_right ((prime_rpow_neg_le_iff a b).2 h), prime_rpow_neg_le_iff] at hmax
    exact hmax

open Polynomial in
theorem _root_.GlobalTheory.Per.Val.vf_one : _root_.GlobalTheory.Per.Val.vf (1 : _root_.Formalism.BasicNotions.Loc.Om l) = 0 := by
  have := (_root_.GlobalTheory.Per.Val.vf_eq_iff (1 : _root_.Formalism.BasicNotions.Loc.Om l) 0).2 (by simp)
  exact_mod_cast this

open Polynomial in
theorem _root_.GlobalTheory.Per.Val.vf_l : _root_.GlobalTheory.Per.Val.vf ((l : ℕ) : _root_.Formalism.BasicNotions.Loc.Om l) = 1 := by
  have h : ‖((l : ℕ) : _root_.Formalism.BasicNotions.Loc.Om l)‖ = (l : ℝ) ^ (-((1 : ℚ) : ℝ)) := by
    have : ((l : ℕ) : _root_.Formalism.BasicNotions.Loc.Om l) = algebraMap ℚ_[l] (_root_.Formalism.BasicNotions.Loc.Om l) (l : ℚ_[l]) := by simp
    rw [this, PadicAlgCl.norm_extends, Padic.norm_p]
    simp [Real.rpow_neg_one]
  exact_mod_cast (_root_.GlobalTheory.Per.Val.vf_eq_iff _ 1).2 h

def vOm (l : ℕ) [Fact l.Prime] : AddValuation (Om l) (WithTop ℚ) :=
  AddValuation.of vf vf_zero vf_one vf_add vf_mul

end GlobalTheory.Per.Val

namespace GlobalTheory.Per

end GlobalTheory.Per
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfRestrictGaloisDescent
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfRestrictGaloisDescent
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.DeRhamDescent

theorem finrank_fixed {R G M K L : Type} [Field R] [Group G] [AddCommGroup M] [Module R M]
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (A : G →* Module.End R M) (m : L →+* Module.End R M) (ε : G →* (L ≃ₐ[K] L))
    (hs : Function.Surjective ε) (hε : ∀ g a x, A g (m a x) = m (ε g a) (A g x))
    (D D' : Submodule R M) (hD : ∀ x, x ∈ D ↔ ∀ g, A g x = x)
    (hD' : ∀ x, x ∈ D' ↔ ∀ g, ε g = 1 → A g x = x) :
    Module.finrank R D' = Module.finrank K L * Module.finrank R D := by
  classical
  have hc : Fintype.card (L ≃ₐ[K] L) = Module.finrank K L := by
    rw [← Nat.card_eq_fintype_card]; exact IsGalois.card_aut_eq_finrank K L
  let b : Module.Basis (L ≃ₐ[K] L) K L :=
    (Module.finBasis K L).reindex (Fintype.equivFinOfCardEq hc).symm
  let μ : Module.Basis (L ≃ₐ[K] L) K L := b.traceDual
  let Pm : Matrix (L ≃ₐ[K] L) (L ≃ₐ[K] L) L := Matrix.of fun σ i => σ (b i)
  let Qm : Matrix (L ≃ₐ[K] L) (L ≃ₐ[K] L) L := Matrix.of fun j σ => σ (μ j)
  have hQP : Qm * Pm = 1 := by
    ext j i
    simp only [Matrix.mul_apply, Pm, Qm, Matrix.of_apply, ← map_mul]
    rw [← trace_eq_sum_automorphisms, Module.Basis.trace_traceDual_mul, Matrix.one_apply]
    by_cases h : j = i
    · simp [h]
    · simp [h, Ne.symm h]
  have hPQ : Pm * Qm = 1 := mul_eq_one_comm.1 hQP
  have h1 : ∀ j i, ∑ σ : L ≃ₐ[K] L, σ (μ j) * σ (b i) = if j = i then 1 else 0 := fun j i => by
    have := congrFun (congrFun hQP j) i
    simpa only [Matrix.mul_apply, Pm, Qm, Matrix.of_apply, Matrix.one_apply] using this
  have h2 : ∀ σ : L ≃ₐ[K] L, ∑ i, b i * σ (μ i) = if 1 = σ then 1 else 0 := fun σ => by
    have := congrFun (congrFun hPQ 1) σ
    simpa only [Matrix.mul_apply, Pm, Qm, Matrix.of_apply, Matrix.one_apply,
      AlgEquiv.one_apply] using this
  choose s hs' using hs
  have hm : ∀ a, ∀ x ∈ D', m a x ∈ D' := fun a x hx => by
    rw [hD'] at hx ⊢
    intro g hg
    rw [hε, hg, hx g hg, AlgEquiv.one_apply]
  have hDD : D ≤ D' := fun x hx => (hD' x).2 fun g _ => (hD x).1 hx g
  have hA : ∀ x ∈ D', ∀ g g', ε g = ε g' → A g x = A g' x := fun x hx g g' h => by
    have := (hD' x).1 hx (g'⁻¹ * g) (by rw [map_mul, map_inv, h, inv_mul_cancel])
    conv_rhs => rw [← this]
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
  let Φ₀ : ((L ≃ₐ[K] L) → D) →ₗ[R] M :=
    ∑ i, (m (b i)) ∘ₗ D.subtype ∘ₗ LinearMap.proj i
  have hΦ : ∀ x, Φ₀ x = ∑ i, m (b i) (x i) := fun x => by
    simp [Φ₀]
  have hinj : Function.Injective Φ₀ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    have h3 : ∀ σ : L ≃ₐ[K] L, ∑ i, m (σ (b i)) (x i) = 0 := fun σ => by
      have := congrArg (A (s σ)) hx
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hΦ, map_sum, map_zero] at this
      rw [← this]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hε, hs', (hD _).1 (x i).2]
    funext j
    apply Subtype.ext
    have h4 : ∑ σ : L ≃ₐ[K] L, m (σ (μ j)) (∑ i, m (σ (b i)) (x i)) = 0 := by
      simp only [h3, map_zero, Finset.sum_const_zero]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, ← Module.End.mul_apply, ← map_mul m] at h4
    rw [Finset.sum_comm] at h4
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [← LinearMap.sum_apply, ← map_sum m, h1] at h4
    rw [Finset.sum_eq_single j (fun i _ hi => by simp [Ne.symm hi]) (by simp)] at h4
    simpa using h4
  have hr : LinearMap.range Φ₀ = D' := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      rw [hΦ]
      exact D'.sum_mem fun i _ => hm _ _ (hDD (x i).2)
    · intro x hx
      refine ⟨fun i => ⟨∑ σ, A (s σ) (m (μ i) x), (hD _).2 fun g => ?_⟩, ?_⟩
      · set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, ← Equiv.sum_comp (Equiv.mulLeft (ε g))
          (fun σ => A (s σ) (m (μ i) x))]
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [← Module.End.mul_apply, ← map_mul]
        exact hA _ (hm _ _ hx) _ _ (by simp [hs'])
      · rw [hΦ]
        have hmm : ∀ a a' y, m a (m a' y) = m (a * a') y := fun a a' y => by
          rw [map_mul, Module.End.mul_apply]
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [hε, hs', map_sum, hmm]
        rw [Finset.sum_comm]
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [← LinearMap.sum_apply, ← map_sum m, h2]
        rw [Finset.sum_eq_single 1 (fun i _ hi => by simp [Ne.symm hi]) (by simp)]
        simpa using (hD' x).1 hx _ (hs' 1)
  rw [← hr, LinearMap.finrank_range_of_inj hinj]
  by_cases hf : Module.Finite R D
  · rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, hc, smul_eq_mul]
  · rw [Module.finrank_of_not_finite hf, mul_zero, Module.finrank_of_not_finite]
    intro h
    exact hf (Module.Finite.of_surjective
      (LinearMap.proj (R := R) (φ := fun _ : L ≃ₐ[K] L => D) (1 : L ≃ₐ[K] L))
      (fun y => ⟨fun _ => y, rfl⟩))

open GlobalTheory.JumpDescent TensorProduct in
theorem isDR_of_restrict : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K K' LL : FinExt l)
    (hle : GK K' ≤ GK K), K.1 ≤ K'.1 → (∀ g ∈ GK K, ∀ x ∈ K'.1, g x ∈ K'.1) →
    ∀ (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V]
      [IsScalarTower ℚ_[l] ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V),
      IsDR (P.PD K') (V := V) (ρ.comp (Subgroup.inclusion hle)) → IsDR (P.PD K) ρ := by
  intro l _ P K K' LL hle h hst V _ _ _ _ ρ hρ
  unfold IsDR at hρ ⊢
  haveI : FiniteDimensional ℚ_[l] ↥K'.1 := K'.2
  let L : IntermediateField ↥K.1 (Om l) := IntermediateField.extendScalars h
  haveI : FiniteDimensional ℚ_[l] ↥L := K'.2
  haveI : FiniteDimensional ↥K.1 ↥L := Module.Finite.of_restrictScalars_finite ℚ_[l] _ _
  haveI : Normal ↥K.1 (Om l) := Normal.tower_top_of_normal ℚ_[l] _ _
  let e : ↥(GK K) ≃* (Om l ≃ₐ[↥K.1] Om l) := IntermediateField.fixingSubgroupEquiv K.1
  have he : ∀ (g : ↥(GK K)) (x : Om l), e g x = (g : GQ l) x := fun _ _ => rfl
  haveI : Normal ↥K.1 ↥L := IntermediateField.normal_iff_forall_map_le'.2 fun σ => by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨g, rfl⟩ := e.surjective σ
    exact hst g.1 g.2 x hx
  haveI : IsGalois ↥K.1 ↥L := {}
  let ε : ↥(GK K) →* (↥L ≃ₐ[↥K.1] ↥L) := (AlgEquiv.restrictNormalHom ↥L).comp e.toMonoidHom
  have hεa : ∀ (g : ↥(GK K)) (x : ↥L), ((ε g x : ↥L) : Om l) = (g : GQ l) x := fun g x =>
    AlgEquiv.restrictNormalHom_apply L (e g) x
  let A : ↥(GK K) →* Module.End ↥LL.1 (V ⊗[ℚ_[l]] P.R.BdR) :=
    { toFun := actVdR (P.PD K) ρ
      map_one' := by ext v b; simp [actVdR_tmul]
      map_mul' := fun g g' => by ext v b; simp [actVdR_tmul] }
  let m : ↥L →+* Module.End ↥LL.1 (V ⊗[ℚ_[l]] P.R.BdR) :=
    { toFun := fun c => mulOm P (c : Om l)
      map_one' := by ext v b; simp [mulOm_tmul]
      map_mul' := fun g g' => by ext v b; simp [mulOm_tmul, mul_assoc]
      map_zero' := by ext v b; simp [mulOm_tmul]
      map_add' := fun g g' => by ext v b; simp [mulOm_tmul, add_mul, tmul_add] }
  have key := finrank_fixed A m ε
    ((AlgEquiv.restrictNormalHom_surjective (F := ↥K.1) (K₁ := ↥L) (Om l)).comp e.surjective)
    (fun g c x => by
      change actVdR (P.PD K) ρ g (mulOm (LL := ↥LL.1) P (c : Om l) x) =
        mulOm (LL := ↥LL.1) P ((ε g c : ↥L) : Om l) (actVdR (P.PD K) ρ g x)
      rw [hεa]
      induction x using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul v b => simp [mulOm_tmul, actVdR_tmul, P.actQdR_Om]
      | add y z hy hz => simp only [map_add (f := _), hy, hz])
    (DdR (P.PD K) ρ) (DdR (P.PD K') (ρ.comp (Subgroup.inclusion hle)))
    (fun x => mem_DdR P K ρ x)
    (fun x => by
      rw [mem_DdR]
      constructor
      · intro hx g hg
        have hg' : g.1 ∈ GK K' := fun a => by
          have := hεa g ⟨a.1, a.2⟩
          rw [hg] at this
          exact this.symm
        have := hx ⟨g.1, hg'⟩
        rw [actVdR_comp P h] at this
        exact this
      · intro hx g
        rw [actVdR_comp P h]
        apply hx
        ext a
        rw [hεa]
        exact g.2 ⟨a.1, a.2⟩)
  have hfin : Module.finrank ℚ_[l] ↥K'.1 = Module.finrank ℚ_[l] ↥K.1 * Module.finrank ↥K.1 ↥L :=
    (Module.finrank_mul_finrank ℚ_[l] ↥K.1 ↥L).symm
  have hpos : 0 < Module.finrank ↥K.1 ↥L := Module.finrank_pos
  rw [key, hfin] at hρ
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [hρ]
  ring

end GlobalTheory.DeRhamDescent
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfRestrictGaloisDescentStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDeRham_of_restrict_galois_descent : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K K' LL : FinExt l) (hle : GK K' ≤ GK K), K.1 ≤ K'.1 → (∀ g ∈ GK K, ∀ x ∈ K'.1, g x ∈ K'.1) → ∀ (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), IsDR (P.PD K') (V := V) (ρ.comp (Subgroup.inclusion hle)) → IsDR (P.PD K) ρ := by
  first | exact @GlobalTheory.DeRhamDescent.isDR_of_restrict | exact GlobalTheory.DeRhamDescent.isDR_of_restrict | (intros; apply GlobalTheory.DeRhamDescent.isDR_of_restrict <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteExtensionEntriesOfCompactRep
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteExtensionEntriesOfCompactRep
open Formalism.MainNotions.N GlobalTheory.Cong GlobalTheory.PsChar

namespace GlobalTheory.CompactRepField

theorem exists_finiteDimensional_entries_mem_of_continuous :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (a : ℕ) (r : Γ →* GL (Fin a) (PadicAlgCl l)), Continuous r → ∃ L : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] L ∧ ∀ g i j, ((r g : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l)) i j ∈ L := by
  intro l _ Γ _ _ _ _ a r hr
  let H : Subgroup (GL (Fin a) (PadicAlgCl l)) := r.range
  haveI : CompactSpace H := by
    have hc : IsCompact (H : Set (GL (Fin a) (PadicAlgCl l))) := by
      have : (H : Set (GL (Fin a) (PadicAlgCl l))) = Set.range r := by
        ext x; simp [H]
      rw [this]; exact isCompact_range hr
    exact isCompact_iff_compactSpace.1 hc
  obtain ⟨K, hK, hmem⟩ := exists_finiteDimensional_entries_mem l H a H.subtype
    fun i j => ((Units.continuous_val.comp continuous_subtype_val).matrix_elem i j)
  refine ⟨K, hK, fun g i j => ?_⟩
  exact hmem ⟨r g, ⟨g, rfl⟩⟩ i j

end GlobalTheory.CompactRepField
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteExtensionEntriesOfCompactRepStatement
open Formalism.MainNotions.N GlobalTheory.Cong GlobalTheory.PsChar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteExtension_entries_of_compact_rep : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (a : ℕ) (r : Γ →* GL (Fin a) (PadicAlgCl l)), Continuous r → ∃ L : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] L ∧ ∀ g i j, ((r g : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l)) i j ∈ L := by
  first | exact @GlobalTheory.CompactRepField.exists_finiteDimensional_entries_mem_of_continuous | exact GlobalTheory.CompactRepField.exists_finiteDimensional_entries_mem_of_continuous | (intros; apply GlobalTheory.CompactRepField.exists_finiteDimensional_entries_mem_of_continuous <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTmulOneOfFrobFixedOfMemFilZero
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory

theorem equivFinsuppOfBasisLeft_lTensor_apply {F : Type} [Field F] {V M N : Type}
    [AddCommGroup V] [Module F V] [AddCommGroup M] [Module F M] [AddCommGroup N] [Module F N]
    {ι : Type} [DecidableEq ι] (b : Module.Basis ι F V) (f : M →ₗ[F] N) (x : V ⊗[F] M) (i : ι) :
    equivFinsuppOfBasisLeft b (f.lTensor V x) i = f (equivFinsuppOfBasisLeft b x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v m => simp
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]

theorem algebraTensorModule_map_id_apply {F L : Type} [Field F] [Field L] [Algebra F L]
    {V M N : Type} [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V]
    [AddCommGroup M] [Module F M] [AddCommGroup N] [Module F N]
    (f : M →ₗ[F] N) (x : V ⊗[F] M) :
    AlgebraTensorModule.map (LinearMap.id : V →ₗ[L] V) f x = f.lTensor V x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v m => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem exists_tmul_one_of_frob_fixed_of_mem_fil_zero :
    ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] (x : V ⊗[Qp] B), φVB PD (LL := LL) (V := V) x = x → ιV PD (LL := LL) (V := V) x ∈ FilV PD (LL := LL) (V := V) 0 → ∃ v : V, x = v ⊗ₜ[Qp] (1 : B) := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL _ _ V _ _ _ _ x hφ hF
  classical
  let b := Module.Basis.ofVectorSpace Qp V
  have key : ∀ i, ∃ c : Qp, algebraMap Qp B c = equivFinsuppOfBasisLeft b x i := by
    intro i
    apply PD.fund
    · have h := equivFinsuppOfBasisLeft_lTensor_apply b PD.φ.toLinearMap x i
      rw [← algebraTensorModule_map_id_apply (L := LL)] at h
      have h2 : AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) PD.φ.toLinearMap x = x := hφ
      rw [h2] at h
      exact h.symm
    · obtain ⟨y, hy⟩ := hF
      have h := equivFinsuppOfBasisLeft_lTensor_apply b
        (PD.ι.toLinearMap.restrictScalars Qp) x i
      rw [← algebraTensorModule_map_id_apply (L := LL)] at h
      have h' := equivFinsuppOfBasisLeft_lTensor_apply b
        ((PD.Fil 0).restrictScalars Qp).subtype y i
      rw [← algebraTensorModule_map_id_apply (L := LL), hy] at h'
      have h3 : PD.ι (equivFinsuppOfBasisLeft b x i)
          = ((PD.Fil 0).restrictScalars Qp).subtype (equivFinsuppOfBasisLeft b y i) :=
        h.symm.trans h'
      rw [h3]
      exact (equivFinsuppOfBasisLeft b y i).2
  choose c hc using key
  refine ⟨∑ i ∈ (equivFinsuppOfBasisLeft b x).support, c i • b i, ?_⟩
  have hx : x = (equivFinsuppOfBasisLeft b).symm (equivFinsuppOfBasisLeft b x) := by simp
  rw [equivFinsuppOfBasisLeft_symm_apply, Finsupp.sum] at hx
  rw [TensorProduct.sum_tmul]
  refine hx.trans (Finset.sum_congr rfl fun i _ => ?_)
  rw [← hc i, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDeRhamTensorCoordinatesOfBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDeRhamTensorCoordinatesOfBasis
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory

theorem exists_tensor_coord_of_basis {k V M : Type} [Field k] [AddCommGroup V] [Module k V]
    [AddCommGroup M] [Module k M] {d : ℕ} (bV : Module.Basis (Fin d) k V) :
    ∃ Φ : V ⊗[k] M ≃ₗ[k] (Fin d → M), (∀ (v : V) (b : M) (i : Fin d), Φ (v ⊗ₜ b) i = bV.repr v i • b) ∧
      ∀ z, z = ∑ i, bV i ⊗ₜ[k] Φ z i := by
  classical
  let Φ : V ⊗[k] M ≃ₗ[k] (Fin d → M) :=
    (TensorProduct.congr bV.equivFun (LinearEquiv.refl k M)).trans
      ((TensorProduct.comm k _ _).trans (TensorProduct.piScalarRight k k M (Fin d)))
  have h : ∀ (v : V) (b : M) (i : Fin d), Φ (v ⊗ₜ b) i = bV.repr v i • b := by
    intro v b i
    simp [Φ]
  refine ⟨Φ, h, fun z => ?_⟩
  apply Φ.injective
  funext j
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_apply]
  simp only [h, Module.Basis.repr_self]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [Finsupp.single_apply, hij]
  · simp

theorem exists_coord_tensor_dR : ∀ {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] (ρ : Representation LL G V) {d : ℕ} (bV : Module.Basis (Fin d) Qp V), ∃ Φ : V ⊗[Qp] BdR ≃ₗ[Qp] (Fin d → BdR), (∀ (a : ℤ) (z : V ⊗[Qp] BdR), z ∈ FilV PD (LL := LL) (V := V) a ↔ ∀ i, Φ z i ∈ PD.Fil a) ∧ ∀ (g : G) (z : V ⊗[Qp] BdR), Φ (actVdR PD ρ g z) = (Matrix.of fun i j => algebraMap Qp BdR (bV.repr (ρ g (bV j)) i)).mulVec (fun i => PD.actdR g (Φ z i)) := by
  intro G _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL _ _ V _ _ _ _ ρ d bV
  obtain ⟨Φ, h, hz⟩ := exists_tensor_coord_of_basis (M := BdR) bV
  refine ⟨Φ, fun a z => ⟨?_, fun H => ?_⟩, fun g z => ?_⟩
  · rintro ⟨w, rfl⟩ i
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      rw [AlgebraTensorModule.map_tmul, h]
      exact ((PD.Fil a).restrictScalars Qp).smul_mem _ b.2
    | add x y hx hy =>
      rw [map_add (f := _), map_add (f := _), Pi.add_apply]
      exact add_mem hx hy
  · rw [hz z]
    refine Submodule.sum_mem _ fun i _ => ⟨bV i ⊗ₜ ⟨Φ z i, H i⟩, ?_⟩
    rw [AlgebraTensorModule.map_tmul]
    rfl
  · have hact : ∀ (v : V) (b : BdR), actVdR PD ρ g (v ⊗ₜ b) = ρ g v ⊗ₜ PD.actdR g b := by
      intro v b
      unfold actVdR
      rw [AlgebraTensorModule.map_tmul]
      rfl
    funext i
    conv_lhs => rw [hz z]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum, Finset.sum_apply]
    simp only [hact, h, Matrix.mulVec, dotProduct, Matrix.of_apply, Algebra.smul_def]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDeRhamTensorCoordinatesOfBasisStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_deRham_tensor_coordinates_of_basis : ∀ {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] (ρ : Representation LL G V) {d : ℕ} (bV : Module.Basis (Fin d) Qp V), ∃ Φ : V ⊗[Qp] BdR ≃ₗ[Qp] (Fin d → BdR), (∀ (a : ℤ) (z : V ⊗[Qp] BdR), z ∈ FilV PD (LL := LL) (V := V) a ↔ ∀ i, Φ z i ∈ PD.Fil a) ∧ ∀ (g : G) (z : V ⊗[Qp] BdR), Φ (actVdR PD ρ g z) = (Matrix.of fun i j => algebraMap Qp BdR (bV.repr (ρ g (bV j)) i)).mulVec (fun i => PD.actdR g (Φ z i)) := by
  first | exact @GlobalTheory.exists_coord_tensor_dR | exact GlobalTheory.exists_coord_tensor_dR | (intros; apply GlobalTheory.exists_coord_tensor_dR <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyClosureHomTiltField
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsBisAlt
namespace GlobalTheory.ProofStatement

theorem main : ∀ (l : ℕ) [hl : Fact (Nat.Prime l)] (a : AlgebraicClosure (ZMod l)), a ≠ (0 : AlgebraicClosure (ZMod l)) → ∃ (m : ℕ), (0 : ℕ) < m ∧ ¬l ∣ m ∧ a ^ m = (1 : AlgebraicClosure (ZMod l)) := by
  intro l hl a ha
  set K := IntermediateField.adjoin (ZMod l) ({a} : Set (AlgebraicClosure (ZMod l))) with hK
  haveI : FiniteDimensional (ZMod l) K :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral a)
  haveI : Finite K := Module.finite_of_finite (ZMod l)
  letI : Fintype K := Fintype.ofFinite K
  haveI : CharP K l := charP_of_injective_algebraMap (algebraMap (ZMod l) K).injective l
  obtain ⟨n, _, hcard⟩ := FiniteField.card K l
  have ha' : (⟨a, IntermediateField.mem_adjoin_simple_self (ZMod l) a⟩ : K) ≠ 0 := by
    intro h; apply ha; exact congrArg Subtype.val h
  have hpow := FiniteField.pow_card_sub_one_eq_one _ ha'
  have hl1 : 2 ≤ l := hl.out.two_le
  have hn : 1 ≤ (n : ℕ) := n.pos
  have hq : l ≤ l ^ (n : ℕ) := Nat.le_self_pow (by omega) l
  refine ⟨Fintype.card K - 1, by omega, ?_, ?_⟩
  · rw [hcard]
    intro hd
    have h2 : l ∣ l ^ (n : ℕ) := dvd_pow_self l (by omega)
    have h3 : l ∣ l ^ (n : ℕ) - (l ^ (n : ℕ) - 1) := Nat.dvd_sub h2 hd
    rw [Nat.sub_sub_self (by omega)] at h3
    exact hl.out.one_lt.ne' (Nat.dvd_one.mp h3)
  · have := congrArg Subtype.val hpow
    simpa using this

end GlobalTheory.ProofStatement
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyClosureHomTiltField
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.Per

theorem exists_pow_eq_one_of_algClosure_zmod (l : ℕ) [hl : Fact l.Prime] (a : AlgebraicClosure (ZMod l))
    (ha : a ≠ 0) : ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧ a ^ m = 1 := by
  first
  | exact @_root_.GlobalTheory.ProofStatement.main
  | exact _root_.GlobalTheory.ProofStatement.main
  | (apply _root_.GlobalTheory.ProofStatement.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.ProofStatement.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ProofStatement.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ProofStatement.main ..)

theorem exists_isPrimitiveRoot_tilt (l : ℕ) [hl : Fact l.Prime] (m : ℕ) (hm : 0 < m) (hlm : ¬ l ∣ m) :
    ∃ e : Per.Fl l, IsPrimitiveRoot e m := by
  haveI : NeZero m := ⟨hm.ne'⟩
  obtain ⟨x, hx⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) m
  obtain ⟨e, he, hex⟩ := exists_tilt_root_of_unity l x m hm hlm hx.pow_eq_one
  refine ⟨e, he, fun d hd => hx.dvd_of_pow_eq_one d ?_⟩
  have h1 : e.untilt ^ d = 1 := by rw [← map_pow, hd, map_one]
  have h2 : (x : ℂ_[l]) ^ d = 1 := by
    rw [← hex]
    exact_mod_cast congrArg Subtype.val h1
  apply (algebraMap (Om l) ℂ_[l]).injective
  rw [map_pow, map_one]
  exact h2

theorem nonempty_algClosure_zmod_to_tilt :
    ∀ (l : ℕ) [Fact l.Prime], Nonempty (AlgebraicClosure (ZMod l) →+* Per.Fl l) := by
  intro l hl
  haveI : IsDomain (Per.Fl l) := inferInstance
  haveI : CharP (Per.Fl l) l := inferInstance
  let Ω := AlgebraicClosure (FractionRing (Per.Fl l))
  let j : Per.Fl l →+* Ω :=
    (algebraMap (FractionRing (Per.Fl l)) Ω).comp (algebraMap (Per.Fl l) (FractionRing (Per.Fl l)))
  have hj : Function.Injective j :=
    (algebraMap (FractionRing (Per.Fl l)) Ω).injective.comp (IsFractionRing.injective _ _)
  haveI : CharP Ω l := charP_of_injective_ringHom hj l
  letI : Algebra (ZMod l) Ω := ZMod.algebra Ω l
  let f₀ : AlgebraicClosure (ZMod l) →ₐ[ZMod l] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hr : ∀ a, (f₀ : AlgebraicClosure (ZMod l) →+* Ω) a ∈ j.range := by
    intro a
    by_cases ha : a = 0
    · rw [ha, map_zero]; exact zero_mem _
    obtain ⟨m, hm, hlm, ham⟩ := exists_pow_eq_one_of_algClosure_zmod l a ha
    obtain ⟨e, he⟩ := exists_isPrimitiveRoot_tilt l m hm hlm
    haveI : NeZero m := ⟨hm.ne'⟩
    obtain ⟨i, -, hi⟩ := (he.map_of_injective hj).eq_pow_of_pow_eq_one
      (ξ := (f₀ : AlgebraicClosure (ZMod l) →+* Ω) a) (by rw [← map_pow, ham, map_one])
    exact ⟨e ^ i, by rw [map_pow, hi]⟩
  let E : Per.Fl l ≃+* j.range := RingEquiv.ofBijective j.rangeRestrict
    ⟨fun x y h => hj (congrArg Subtype.val h), j.rangeRestrict_surjective⟩
  exact ⟨E.symm.toRingHom.comp ((f₀ : AlgebraicClosure (ZMod l) →+* Ω).codRestrict j.range hr)⟩

end GlobalTheory.Per
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyClosureHomTiltFieldStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_closure_hom_tilt_field : ∀ (l : ℕ) [Fact l.Prime], Nonempty (AlgebraicClosure (ZMod l) →+* Per.Fl l) := by
  first | exact @GlobalTheory.Per.nonempty_algClosure_zmod_to_tilt | exact GlobalTheory.Per.nonempty_algClosure_zmod_to_tilt | (intros; apply GlobalTheory.Per.nonempty_algClosure_zmod_to_tilt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBeta
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

namespace GlobalTheory.HWLBeta

theorem exists_beta : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ LL : FinExt l, ∃ β : RA LL →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B, IsBeta AI β := by
  intro l _ P AI T LL
  have hz := (GlobalTheory.TiedMu.tied_mu_units l P AI T).2.2.2
  let _ : Algebra ℤ_[l] (↥LL.1 ⊗[ℚ_[l]] P.R.B) :=
    ((algebraMap ℚ_[l] (↥LL.1 ⊗[ℚ_[l]] P.R.B)).comp (algebraMap ℤ_[l] ℚ_[l])).toAlgebra
  let f : ↥(OL LL) →ₐ[ℤ_[l]] ↥LL.1 ⊗[ℚ_[l]] P.R.B :=
    { toRingHom := (Algebra.TensorProduct.includeLeftRingHom).comp (OL LL).val.toRingHom
      commutes' := fun z => by
        show ((algebraMap ℤ_[l] ↥LL.1 z) ⊗ₜ[ℚ_[l]] (1 : P.R.B)) =
          algebraMap ℚ_[l] (↥LL.1 ⊗[ℚ_[l]] P.R.B) (algebraMap ℤ_[l] ℚ_[l] z)
        rw [Algebra.TensorProduct.algebraMap_apply, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL.1] }
  let g : Ainf l →ₐ[ℤ_[l]] ↥LL.1 ⊗[ℚ_[l]] P.R.B :=
    { toRingHom := (Algebra.TensorProduct.includeRight (R := ℚ_[l]) (A := ↥LL.1)).toRingHom.comp AI.ιA
      commutes' := fun z => by
        show Algebra.TensorProduct.includeRight (R := ℚ_[l]) (A := ↥LL.1)
            (AI.ιA (algebraMap ℤ_[l] (Ainf l) z)) =
          algebraMap ℚ_[l] (↥LL.1 ⊗[ℚ_[l]] P.R.B) (algebraMap ℤ_[l] ℚ_[l] z)
        rw [hz, AlgHom.commutes]
        rfl }
  refine ⟨(Algebra.TensorProduct.productMap f g).toRingHom, fun o w => ?_⟩
  show Algebra.TensorProduct.productMap f g (o ⊗ₜ[ℤ_[l]] w) = _
  rw [Algebra.TensorProduct.productMap_apply_tmul]
  show ((o : ↥LL.1) ⊗ₜ[ℚ_[l]] (1 : P.R.B)) * ((1 : ↥LL.1) ⊗ₜ[ℚ_[l]] AI.ιA w) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

end GlobalTheory.HWLBeta
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepWeilJumps
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory
open Formalism.MainNotions.SumRepresentations.At

section Tw
variable {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ}

theorem twGL_val (ρ : Γ →* GL (Fin a) k) (χ : Γ →* GL (Fin 1) k) (g : Γ) :
    ((twGL ρ (Matrix.GeneralLinearGroup.det.comp χ) g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) =
      ((χ g : GL (Fin 1) k) : Matrix (Fin 1) (Fin 1) k).det • ((ρ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) := by
  simp only [twGL, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_mul, Units.coe_map]
  simp [Algebra.algebraMap_eq_smul_one, Matrix.GeneralLinearGroup.val_det_apply]

theorem isInv_twGL_iff (ρ : Γ →* GL (Fin a) k) (χ : Γ →* GL (Fin 1) k) (W : Submodule k (Fin a → k)) :
    IsInv (twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) W ↔ IsInv ρ W := by
  constructor
  · intro h g v hv
    have hu : ((χ g : GL (Fin 1) k) : Matrix (Fin 1) (Fin 1) k).det ≠ 0 :=
      (Matrix.isUnit_iff_isUnit_det _).1 (χ g).isUnit |>.ne_zero
    have := W.smul_mem (((χ g : GL (Fin 1) k) : Matrix (Fin 1) (Fin 1) k).det)⁻¹ (h g v hv)
    rw [twGL_val, Matrix.smul_mulVec, smul_smul, inv_mul_cancel₀ hu, one_smul] at this
    exact this
  · intro h g v hv
    rw [twGL_val, Matrix.smul_mulVec]
    exact W.smul_mem _ (h g v hv)

theorem isSSRep_twGL (ρ : Γ →* GL (Fin a) k) (χ : Γ →* GL (Fin 1) k) (h : IsSSRep ρ) :
    IsSSRep (twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) := by
  intro W hW
  obtain ⟨W', hW', hc⟩ := h W ((isInv_twGL_iff ρ χ W).1 hW)
  exact ⟨W', (isInv_twGL_iff ρ χ W').2 hW', hc⟩

end Tw

theorem contQ_twGL (D : D7) (i : D.nd.Loc) {a : ℕ} (ρ : GE D.nd →* GL (Fin a) (Qbar (D.nd.l i)))
    (χ : GE D.nd →* GL (Fin 1) (Qbar (D.nd.l i))) (hρ : ContQ D.nd i ρ) (hχ : ContQ D.nd i χ) :
    ContQ D.nd i (twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) := by
  unfold ContQ at *
  simp only [twGL_val]
  exact (hχ.matrix_det).smul hρ

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUpUniMul
namespace GlobalTheory.UpperUnipotentMul

open Matrix

theorem isUpUni_mul {K : Type} [Field K] {n : ℕ} {A B : Matrix (Fin n) (Fin n) K}
    (hA : Formalism.MainNotions.S.IsUpUni A) (hB : Formalism.MainNotions.S.IsUpUni B) : Formalism.MainNotions.S.IsUpUni (A * B) := by
  intro i j
  refine ⟨fun hji => ?_, fun hij => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero (fun k _ => ?_)
    rcases lt_or_ge k i with hki | hik
    · rw [(hA i k).1 hki, zero_mul]
    · rw [(hB k j).1 (lt_of_lt_of_le hji hik), mul_zero]
  · subst hij
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [(hA i i).2 rfl, (hB i i).2 rfl, one_mul]
    · intro k _ hki
      rcases lt_or_gt_of_ne hki with h | h
      · rw [(hA i k).1 h, zero_mul]
      · rw [(hB k i).1 h, mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h

end GlobalTheory.UpperUnipotentMul
end
