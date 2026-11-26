module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafSectionsExact
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TsenLangRatFunc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMayerVietorisConnectingExact
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRepFam
public import GroundTheory.Brauer.Degree

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdmissibleAdelicMatrixFamilyPullbackExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumOrderPlacesAboveEqFinrankMul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumOrderPlacesAboveEqFinrankMul
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.Nef

theorem finsum_ord_pull_eq_finrank_mul : ∀ (k F E : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Field E] [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E] [FiniteDimensional F E], IsFF k F →
  ∀ ρ : Place k E → Place k F, IsRes ρ → (∀ s : Set (Place k F), s.Finite → (ρ ⁻¹' s).Finite) ∧ ∀ φ : Place k F → F, {v | ord v (φ v) ≠ 0}.Finite → ∑ᶠ p : Place k E, ord p (algebraMap F E (φ (ρ p))) = Module.finrank F E * ∑ᶠ v, ord v (φ v) := by
  intro k F E _ _ _ _ _ _ _ _ _ _ hFF ρ hρ
  classical
  have hunif : ∀ v : Place k F, ∃ π : F, π ≠ 0 ∧ ord v π = 1 := fun v => (GlobalTheory.T.functionFieldPlaceOrder_calculus k F v).2.2.2.2.2.1
  choose π hπ0 hπ1 using hunif
  have hfib : ∀ v, {p | ρ p = v}.Finite ∧
      ∑ᶠ p ∈ {p | ρ p = v}, ord p (algebraMap F E (π v)) = Module.finrank F E :=
    fun v => GlobalTheory.T.functionFieldPlace_sum_order_eq_finrank k F E hFF ρ hρ v (π v) (hπ0 v) (hπ1 v)
  have hkey : ∀ p x, ord p (algebraMap F E x) = ord p (algebraMap F E (π (ρ p))) * ord (ρ p) x := by
    intro p x
    obtain ⟨e, -, -, he⟩ := (GlobalTheory.T.functionFieldPlace_restriction_exists_pow k F E).2 ρ hρ p
    rw [he x, he (π (ρ p)), hπ1, mul_one]
  have hpre : ∀ s : Set (Place k F), s.Finite → (ρ ⁻¹' s).Finite := by
    intro s hs
    have h : ρ ⁻¹' s = ⋃ v ∈ s, {p | ρ p = v} := by ext p; simp
    rw [h]; exact hs.biUnion fun v _ => (hfib v).1
  refine ⟨hpre, fun φ hφ => ?_⟩
  have hT := hpre _ hφ
  have hsupp : (Function.support fun p => ord p (algebraMap F E (φ (ρ p)))) ⊆ ↑hT.toFinset := by
    intro p hp
    simp only [Function.mem_support] at hp
    simp only [Set.Finite.coe_toFinset, Set.mem_preimage, Set.mem_setOf_eq]
    intro h; apply hp; rw [hkey, h, mul_zero]
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  rw [finsum_eq_sum_of_support_subset _ (s := hφ.toFinset) (by intro v hv; simpa using hv)]
  rw [← Finset.sum_fiberwise_of_maps_to (g := ρ) (t := hφ.toFinset) (by intro p hp; simpa using hp)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun v hv => ?_
  have hc : ∀ p ∈ hT.toFinset.filter (fun p => ρ p = v),
      ord p (algebraMap F E (φ (ρ p))) = ord p (algebraMap F E (π v)) * ord v (φ v) := by
    intro p hp
    have hpv := (Finset.mem_filter.1 hp).2
    rw [hkey, hpv]
  rw [Finset.sum_congr rfl hc, ← Finset.sum_mul]
  congr 1
  rw [← (hfib v).2, finsum_mem_eq_finite_toFinset_sum _ (hfib v).1]
  congr 1
  ext p
  simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_setOf_eq]
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hv
  constructor
  · exact fun h => h.2
  · intro h; exact ⟨h ▸ hv, h⟩

end GlobalTheory.Nef
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumOrderPlacesAboveEqFinrankMulStatement
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_order_placesAbove_eq_finrank_mul : ∀ (k F E : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Field E] [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E] [FiniteDimensional F E], IsFF k F →
  ∀ ρ : Place k E → Place k F, IsRes ρ → (∀ s : Set (Place k F), s.Finite → (ρ ⁻¹' s).Finite) ∧ ∀ φ : Place k F → F, {v | ord v (φ v) ≠ 0}.Finite → ∑ᶠ p : Place k E, ord p (algebraMap F E (φ (ρ p))) = Module.finrank F E * ∑ᶠ v, ord v (φ v) := by
  first | exact @GlobalTheory.Nef.finsum_ord_pull_eq_finrank_mul | exact GlobalTheory.Nef.finsum_ord_pull_eq_finrank_mul | (intros; apply GlobalTheory.Nef.finsum_ord_pull_eq_finrank_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdmissibleAdelicMatrixFamilyPullbackExtension
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option autoImplicit false

namespace GlobalTheory.Nef.PullAd

section
variable {k F E : Type} [Field k] [Field F] [Field E] [Algebra k F] [Algebra k E] [Algebra F E] {n : ℕ}

theorem val_eq_one_iff {K : Type} [Field K] (w : Valuation K (WithZero (Multiplicative ℤ))) {z : K}
    (hz : z ≠ 0) : w z = 1 ↔ w z ≤ 1 ∧ w z⁻¹ ≤ 1 := by
  constructor
  · intro h; simp [map_inv₀, h]
  · rintro ⟨h1, h2⟩
    rw [map_inv₀] at h2
    have h0 : w z ≠ 0 := (Valuation.ne_zero_iff w).2 hz
    refine le_antisymm h1 ?_
    calc (1 : WithZero (Multiplicative ℤ)) = w z * (w z)⁻¹ := (mul_inv_cancel₀ h0).symm
      _ ≤ w z * 1 := mul_le_mul_right h2 _
      _ = w z := mul_one _

theorem res_eq_one {ρ : Place k E → Place k F} (hρ : IsRes ρ) (p : Place k E) {x : F} (hx : x ≠ 0) :
    p.1 (algebraMap F E x) = 1 ↔ (ρ p).1 x = 1 := by
  rw [val_eq_one_iff _ hx, val_eq_one_iff _ ((map_ne_zero _).2 hx), ← map_inv₀, hρ, hρ]

theorem res_mono {ρ : Place k E → Place k F} (hρ : IsRes ρ) (p : Place k E) {x y : F}
    (h : (ρ p).1 x ≤ (ρ p).1 y) : p.1 (algebraMap F E x) ≤ p.1 (algebraMap F E y) := by
  by_cases hy : y = 0
  · subst hy
    have h0 : (ρ p).1 x = 0 := le_antisymm (by simpa using h) zero_le'
    have hx : x = 0 := (Valuation.zero_iff _).1 h0
    simp [hx]
  · have h1 : (ρ p).1 (x * y⁻¹) ≤ 1 := by
      have h0 : (ρ p).1 y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
      rw [map_mul, map_inv₀]
      calc (ρ p).1 x * ((ρ p).1 y)⁻¹ ≤ (ρ p).1 y * ((ρ p).1 y)⁻¹ := mul_le_mul_left h _
        _ = 1 := mul_inv_cancel₀ h0
    have h2 := (hρ p (x * y⁻¹)).2 h1
    have e : algebraMap F E x = algebraMap F E (x * y⁻¹) * algebraMap F E y := by
      rw [← map_mul, inv_mul_cancel_right₀ hy]
    rw [e, map_mul]
    exact mul_le_of_le_one_left' h2

theorem det_map (M : Matrix (Fin n) (Fin n) F) :
    (M.map (algebraMap F E)).det = algebraMap F E M.det := by
  rw [RingHom.map_det]; rfl

theorem unimod_map {ρ : Place k E → Place k F} (hρ : IsRes ρ) (p : Place k E)
    (M : Matrix (Fin n) (Fin n) F) (hM : M.det ≠ 0) :
    Unimod p (M.map (algebraMap F E)) ↔ Unimod (ρ p) M := by
  unfold Unimod
  rw [det_map, res_eq_one hρ p hM]
  simp only [Matrix.map_apply]
  exact and_congr_left fun _ => forall_congr' fun i => forall_congr' fun j => hρ p _

theorem nrm_of_max (v : Place k F) (x : Fin n → F) (i : Fin n) (h : ∀ j, v.1 (x j) ≤ v.1 (x i)) :
    nrm v x = v.1 (x i) :=
  le_antisymm (Finset.sup_le fun j _ => h j) (Finset.le_sup (f := fun j => v.1 (x j)) (Finset.mem_univ i))

end

theorem adm_pullAd_and_deg_mul_finrank : ∀ (k F E : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Field E] [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E] [FiniteDimensional F E], IsFF k F →
  ∀ ρ : Place k E → Place k F, IsRes ρ → ∀ (n : ℕ) (g : Place k F → Matrix (Fin n) (Fin n) F), admitted g → admitted (pullAd ρ g) ∧ deg (pullAd ρ g) = Module.finrank F E * deg g ∧ (∀ w : Fin n → F, w ≠ 0 → degLine (pullAd ρ g) (fun i => algebraMap F E (w i)) = Module.finrank F E * degLine g w) ∧ ∀ b : ℝ, LinesLE g b → LinesLE (pullAd ρ g) (b * Module.finrank F E) := by
  intro k F E _ _ _ _ _ _ _ _ _ _ hFF ρ hρ n g hg
  have hP := GlobalTheory.T.finsum_order_placesAbove_eq_finrank_mul k F E hFF ρ hρ
  have hdet : ∀ p, (pullAd ρ g p).det = algebraMap F E (g (ρ p)).det := fun p => det_map _
  have hadm : admitted (pullAd ρ g) := by
    refine ⟨fun p => by rw [hdet]; exact (map_ne_zero _).2 (hg.1 _), ?_⟩
    refine (hP.1 _ hg.2).subset fun p hp => ?_
    exact fun h => hp ((unimod_map hρ p (g (ρ p)) (hg.1 _)).2 h)
  have hdeg : deg (pullAd ρ g) = Module.finrank F E * deg g := by
    have hfin : {v | ord v (g v).det ≠ 0}.Finite := hg.2.subset fun v hv hu => hv (by simp [ord, hu.2])
    unfold deg
    rw [← hP.2 (fun v => (g v).det) hfin]
    exact finsum_congr fun p => by rw [hdet]
  have hline : ∀ w : Fin n → F, w ≠ 0 → degLine (pullAd ρ g) (fun i => algebraMap F E (w i))
      = Module.finrank F E * degLine g w := by
    intro w hw
    have hne : (Finset.univ : Finset (Fin n)).Nonempty := by
      obtain ⟨i, -⟩ := Function.ne_iff.1 hw; exact ⟨i, Finset.mem_univ _⟩
    have hmax : ∀ v : Place k F, ∃ i, ∀ j, v.1 ((g v).mulVec w j) ≤ v.1 ((g v).mulVec w i) := fun v => by
      obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun i => v.1 ((g v).mulVec w i)) hne
      exact ⟨i, fun j => hi j (Finset.mem_univ _)⟩
    choose idx hidx using hmax
    let φ : Place k F → F := fun v => (g v).mulVec w (idx v)
    have hvo : ∀ v, ordVec v ((g v).mulVec w) = ord v (φ v) := fun v => by
      simp only [ordVec, ord, φ, nrm_of_max v _ _ (hidx v)]
    have hpo : ∀ p, ordVec p ((pullAd ρ g p).mulVec (fun i => algebraMap F E (w i)))
        = ord p (algebraMap F E (φ (ρ p))) := fun p => by
      have e : (pullAd ρ g p).mulVec (fun i => algebraMap F E (w i))
          = fun i => algebraMap F E ((g (ρ p)).mulVec w i) := by
        funext i; exact (RingHom.map_mulVec _ _ _ _).symm
      rw [e]
      simp only [ordVec, ord, φ]
      rw [nrm_of_max p _ (idx (ρ p)) fun j => res_mono hρ p (hidx (ρ p) j)]
    have hfin : {v | ord v (φ v) ≠ 0}.Finite := by
      have hS : ({v | ¬ Unimod v (g v)} ∪ ⋃ i, {v : Place k F | w i ≠ 0 ∧ v.1 (w i) ≠ 1}).Finite := by
        refine hg.2.union (Set.finite_iUnion fun i => ?_)
        by_cases hi : w i = 0
        · simp [hi]
        · exact (GlobalTheory.T.functionField_finite_support_sum_order_eq_zero k F hFF (w i) hi).1.subset fun v hv => hv.2
      refine hS.subset fun v hv => ?_
      by_contra hc
      simp only [Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq, not_or, not_exists, not_and,
        not_not] at hc
      obtain ⟨hu, hw1⟩ := hc
      apply hv
      rw [← hvo v]
      have h1 : nrm v w = 1 := by
        obtain ⟨i0, hi0⟩ := Function.ne_iff.1 hw
        replace hi0 : w i0 ≠ 0 := hi0
        apply le_antisymm
        · refine Finset.sup_le fun j _ => ?_
          by_cases hj : w j = 0
          · simp [hj]
          · exact (hw1 j hj).le
        · rw [← hw1 i0 hi0]; exact Finset.le_sup (f := fun j => v.1 (w j)) (Finset.mem_univ i0)
      simp only [ordVec]
      rw [(GlobalTheory.T.functionFieldPlaceOrder_calculus k F v).2.2.2.2.2.2.2.2.1 n (g v) w hu, h1]
      simp
    unfold degLine
    rw [finsum_congr hpo, hP.2 φ hfin, finsum_congr hvo]
  have hlines : ∀ b : ℝ, LinesLE g b → LinesLE (pullAd ρ g) (b * Module.finrank F E) := by
    intro b hb E' _ _ _ _ _ ρ' hρ' w hw
    letI : Algebra F E' := ((algebraMap E E').comp (algebraMap F E)).toAlgebra
    haveI : IsScalarTower F E E' := IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : IsScalarTower k F E' := IsScalarTower.of_algebraMap_eq fun x => by
      rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply k F E,
        ← IsScalarTower.algebraMap_apply k E E']
    haveI : FiniteDimensional F E' := Module.Finite.trans E E'
    have hres : IsRes (fun p => ρ (ρ' p)) := fun p x => (hρ' p (algebraMap F E x)).trans (hρ (ρ' p) x)
    have heq : pullAd ρ' (pullAd ρ g) = pullAd (fun p => ρ (ρ' p)) g := by
      funext p; ext i j; rfl
    have hb' := hb E' (fun p => ρ (ρ' p)) hres w hw
    rw [heq]
    calc (degLine (pullAd (fun p => ρ (ρ' p)) g) w : ℝ) ≤ b * Module.finrank F E' := hb'
      _ = b * Module.finrank F E * Module.finrank E E' := by
        rw [← Module.finrank_mul_finrank F E E']; push_cast; ring
  exact ⟨hadm, hdeg, hline, hlines⟩

end GlobalTheory.Nef.PullAd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdmissibleAdelicMatrixFamilyPullbackExtensionStatement
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAdmissibleAdelicMatrixFamily_pullback_extension : ∀ (k F E : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Field E] [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E] [FiniteDimensional F E], IsFF k F →
  ∀ ρ : Place k E → Place k F, IsRes ρ → ∀ (n : ℕ) (g : Place k F → Matrix (Fin n) (Fin n) F), admitted g → admitted (pullAd ρ g) ∧ deg (pullAd ρ g) = Module.finrank F E * deg g ∧ (∀ w : Fin n → F, w ≠ 0 → degLine (pullAd ρ g) (fun i => algebraMap F E (w i)) = Module.finrank F E * degLine g w) ∧ ∀ b : ℝ, LinesLE g b → LinesLE (pullAd ρ g) (b * Module.finrank F E) := by
  first | exact @GlobalTheory.Nef.PullAd.adm_pullAd_and_deg_mul_finrank | exact GlobalTheory.Nef.PullAd.adm_pullAd_and_deg_mul_finrank | (intros; apply GlobalTheory.Nef.PullAd.adm_pullAd_and_deg_mul_finrank <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinrankQuotientSpanModEqOne
open Polynomial

namespace GlobalTheory

theorem isLocalization_fractionRing_of_finite_polynomial (k A : Type) [Field k] [CommRing A] [IsDomain A]
    [Algebra k[X] A] [Module.Finite k[X] A] [FaithfulSMul k[X] A] :
    IsLocalization (Algebra.algebraMapSubmonoid A (nonZeroDivisors k[X])) (FractionRing A) := by
  have hinj : Function.Injective (algebraMap k[X] A) := FaithfulSMul.algebraMap_injective k[X] A
  have hle : Algebra.algebraMapSubmonoid A (nonZeroDivisors k[X]) ≤ nonZeroDivisors A := by
    rintro _ ⟨p, hp, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero
      ((map_ne_zero_iff _ hinj).mpr (nonZeroDivisors.ne_zero hp))
  refine
    { map_units := fun y => IsLocalization.map_units (FractionRing A) ⟨y.1, hle y.2⟩
      surj := fun z => ?_
      exists_of_eq := fun {x y} hxy => ⟨1, by rw [IsFractionRing.injective A (FractionRing A) hxy]⟩ }
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors A) z
  have hb0 : (b : A) ≠ 0 := nonZeroDivisors.ne_zero b.2
  have hne := Ideal.comap_ne_bot_of_integral_mem (R := k[X]) hb0 (Ideal.mem_span_singleton_self (b : A))
    (Algebra.IsIntegral.isIntegral _)
  obtain ⟨p, hpI, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hpI
  refine ⟨⟨c * a, ⟨_, ⟨p, mem_nonZeroDivisors_of_ne_zero hp0, rfl⟩⟩⟩, ?_⟩
  simp only
  rw [← hc, map_mul, map_mul, ← hab]
  ring

end GlobalTheory

namespace GlobalTheory

theorem exists_finrank_quotient_span_mod_eq_one :
    ∀ (k A : Type) [Field k] [IsAlgClosed k] [CommRing A] [IsDomain A] [Algebra k A] [Algebra k[X] A]
      [IsScalarTower k k[X] A] [Module.Finite k[X] A] [Module.Free k[X] A] (N : ℕ), 1 ≤ N →
      ∃ f : A, f ≠ 0 ∧ Module.finrank k (A ⧸ Ideal.span {f}) % N = 1 % N := by
  intro k A _ _ _ _ _ _ _ _ _ N hN
  have : FaithfulSMul k[X] A := inferInstance
  have hinjA : Function.Injective (algebraMap k[X] A) := FaithfulSMul.algebraMap_injective k[X] A
  set L := FractionRing A
  have hinjL : Function.Injective (algebraMap k[X] L) := by
    rw [IsScalarTower.algebraMap_eq k[X] A L]
    exact (IsFractionRing.injective A L).comp hinjA
  have : FaithfulSMul k[X] L := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinjL
  letI : Algebra (RatFunc k) L := RatFunc.liftAlgebra k L
  have : IsLocalization (Algebra.algebraMapSubmonoid A (nonZeroDivisors k[X])) L :=
    isLocalization_fractionRing_of_finite_polynomial k A
  have : Module.Finite (RatFunc k) L :=
    Module.Finite.of_isLocalization k[X] A (Rₚ := RatFunc k) (Sₚ := L) (nonZeroDivisors k[X])
  have hC1 : GlobalTheory.NeedB.IsFirstChernClassOfLineBundle (RatFunc k) :=
    GlobalTheory.is_c1_of_finite_of_tsen_lang_systems (RatFunc k) (RatFunc k) (GlobalTheory.tsenLang_ratFunc k)
  obtain ⟨h, hh⟩ := GlobalTheory.norm_surjective_of_is_c1 (RatFunc k) L hC1 RatFunc.X RatFunc.X_ne_zero
  obtain ⟨⟨x, ⟨_, ⟨m, hm0, rfl⟩⟩⟩, hx⟩ :=
    IsLocalization.surj (Algebra.algebraMapSubmonoid A (nonZeroDivisors k[X])) h
  have hm0' : m ≠ 0 := nonZeroDivisors.ne_zero hm0
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  set g : A := x * algebraMap k[X] A (m ^ M) with hg
  have hgL : algebraMap A L g
      = h * algebraMap (RatFunc k) L (algebraMap k[X] (RatFunc k) (m ^ (M + 1))) := by
    simp only at hx
    rw [hg, map_mul, ← hx, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply, pow_succ, map_mul]
    ring
  have hnorm : Algebra.norm k[X] g = X * (m ^ (M + 1)) ^ Module.finrank (RatFunc k) L := by
    apply IsFractionRing.injective k[X] (RatFunc k)
    rw [← Algebra.norm_localization k[X] (Rₘ := RatFunc k) (Sₘ := L) (nonZeroDivisors k[X]) g, hgL, map_mul, hh,
      Algebra.norm_algebraMap, map_mul, RatFunc.algebraMap_X, ← map_pow]
  have hp : (m ^ (M + 1)) ^ Module.finrank (RatFunc k) L ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hm0')
  have hg0 : g ≠ 0 := by
    intro h0
    rw [h0, Algebra.norm_zero] at hnorm
    exact mul_ne_zero X_ne_zero hp hnorm.symm
  refine ⟨g, hg0, ?_⟩
  rw [finrank_quotient_span_eq_natDegree_norm (Module.Free.chooseBasis k[X] A) hg0, hnorm,
    natDegree_mul X_ne_zero hp, natDegree_X, natDegree_pow, natDegree_pow, mul_left_comm,
    Nat.add_mul_mod_self_left]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniqueCochainOnDiscProduct
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryIso
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec

noncomputable section
namespace GlobalTheory.EtC.GlueDisc

def pe (k : ℕ) (V : Scheme.{0}) : Spc ⥤ Type :=
  (evaluation _ _).obj (op (SimplexCategory.mk k)) ⋙ (evaluation _ _).obj (op V)

instance (k : ℕ) (V : Scheme.{0}) : PreservesLimitsOfShape (Discrete WalkingPair) (pe k V) := by
  unfold pe; infer_instance

def pairE (A B : Spc) (k : ℕ) (V : Scheme.{0}) : Sx (A ⨯ B) k V ≃ Sx A k V × Sx B k V :=
  ((PreservesLimitPair.iso (pe k V) A B) ≪≫ Types.binaryProductIso _ _).toEquiv

theorem pairE_apply (A B : Spc) (k : ℕ) (V : Scheme.{0}) (z : Sx (A ⨯ B) k V) :
    pairE A B k V z = (Sx.map prod.fst z, Sx.map prod.snd z) := by
  apply Prod.ext
  · change ((Types.binaryProductIso _ _).hom ((prodComparison (pe k V) A B) z)).1 = _
    rw [Types.binaryProductIso_hom_comp_fst_apply]
    exact ConcreteCategory.congr_hom (prodComparison_fst (pe k V) A B) z
  · change ((Types.binaryProductIso _ _).hom ((prodComparison (pe k V) A B) z)).2 = _
    rw [Types.binaryProductIso_hom_comp_snd_apply]
    exact ConcreteCategory.congr_hom (prodComparison_snd (pe k V) A B) z

theorem prod_ext {A B : Spc} {k : ℕ} {V : Scheme.{0}} (z z' : Sx (A ⨯ B) k V)
    (h₁ : Sx.map prod.fst z = Sx.map prod.fst z') (h₂ : Sx.map prod.snd z = Sx.map prod.snd z') : z = z' :=
  (pairE A B k V).injective (by rw [pairE_apply, pairE_apply, h₁, h₂])

def mk {A B : Spc} {k : ℕ} {V : Scheme.{0}} (a : Sx A k V) (b : Sx B k V) : Sx (A ⨯ B) k V :=
  (pairE A B k V).symm (a, b)

theorem mk_fst {A B : Spc} {k : ℕ} {V : Scheme.{0}} (a : Sx A k V) (b : Sx B k V) : Sx.map prod.fst (mk a b) = a := by
  have h := (pairE A B k V).apply_symm_apply (a, b)
  rw [pairE_apply] at h
  exact congrArg Prod.fst h

theorem mk_snd {A B : Spc} {k : ℕ} {V : Scheme.{0}} (a : Sx A k V) (b : Sx B k V) : Sx.map prod.snd (mk a b) = b := by
  have h := (pairE A B k V).apply_symm_apply (a, b)
  rw [pairE_apply] at h
  exact congrArg Prod.snd h

theorem map_res {E E' : Spc} (f : E ⟶ E') {V W : Scheme.{0}} (h : W ⟶ V) {k : ℕ} (a : Sx E k V) :
    Sx.map f (Sx.res h a) = Sx.res h (Sx.map f a) :=
  ConcreteCategory.congr_hom ((f.app (op (SimplexCategory.mk k))).naturality h.op) a

theorem map_prodMap_fst {A A' B B' : Spc} (f : A ⟶ A') (g : B ⟶ B') {k : ℕ} {V : Scheme.{0}} (z : Sx (A ⨯ B) k V) :
    Sx.map prod.fst (Sx.map (prod.map f g) z) = Sx.map f (Sx.map prod.fst z) := by
  change Sx.map (prod.map f g ≫ prod.fst) z = Sx.map (prod.fst ≫ f) z
  rw [prod.map_fst]

theorem map_prodMap_snd {A A' B B' : Spc} (f : A ⟶ A') (g : B ⟶ B') {k : ℕ} {V : Scheme.{0}} (z : Sx (A ⨯ B) k V) :
    Sx.map prod.snd (Sx.map (prod.map f g) z) = Sx.map g (Sx.map prod.snd z) := by
  change Sx.map (prod.map f g ≫ prod.snd) z = Sx.map (prod.snd ≫ g) z
  rw [prod.map_snd]

variable {F : PSh} {B : Spc}

def lift {k : ℕ} {V : Scheme.{0}} (z : Sx (disc.obj F ⨯ B) k V) : Sx (sch.obj V ⨯ B) k V :=
  mk (show Sx (sch.obj V) k V from 𝟙 V) (Sx.map prod.snd z)

theorem lift_spec {k : ℕ} {V : Scheme.{0}} (z : Sx (disc.obj F ⨯ B) k V) :
    Sx.map (E := sch.obj V ⨯ B) (prod.map (disc.map (yonedaEquiv.symm (Sx.map prod.fst z))) (𝟙 B)) (lift z) = z := by
  apply prod_ext
  · have h := map_prodMap_fst (A := sch.obj V)
      (show sch.obj V ⟶ disc.obj F from disc.map (yonedaEquiv.symm (Sx.map prod.fst z))) (𝟙 B) (lift z)
    rw [lift, mk_fst] at h
    refine h.trans ?_
    change F.map (𝟙 V).op (Sx.map prod.fst z) = _
    simp
  · have h := map_prodMap_snd (A := sch.obj V)
      (show sch.obj V ⟶ disc.obj F from disc.map (yonedaEquiv.symm (Sx.map prod.fst z))) (𝟙 B) (lift z)
    rw [lift, mk_snd] at h
    exact h

theorem lift_res {k : ℕ} {V W : Scheme.{0}} (g : W ⟶ V) (z : Sx (disc.obj F ⨯ B) k V) :
    Sx.res g (lift z) = Sx.map (prod.map (sch.map g) (𝟙 B)) (lift (Sx.res g z)) := by
  apply prod_ext
  · rw [map_prodMap_fst, map_res, lift, lift, mk_fst, mk_fst]
    change g ≫ 𝟙 V = 𝟙 W ≫ g
    rw [Category.comp_id, Category.id_comp]
  · rw [map_prodMap_snd, map_res, lift, lift, mk_snd, mk_snd, map_res]
    rfl

theorem fst_pull {k : ℕ} {U W : Scheme.{0}} (x : F.obj (op U)) (y : Sx (sch.obj U ⨯ B) k W) :
    Sx.map prod.fst (Sx.map (E := sch.obj U ⨯ B) (prod.map (disc.map (yonedaEquiv.symm x)) (𝟙 B)) y) =
      F.map (Quiver.Hom.op (Sx.map prod.fst y : W ⟶ U)) x :=
  map_prodMap_fst (A := sch.obj U)
    (show sch.obj U ⟶ disc.obj F from disc.map (yonedaEquiv.symm x)) (𝟙 B) y

theorem lift_pull {k : ℕ} {U W : Scheme.{0}} (x : F.obj (op U)) (y : Sx (sch.obj U ⨯ B) k W) :
    Sx.map (prod.map (sch.map (Sx.map prod.fst y : W ⟶ U)) (𝟙 B))
      (lift (Sx.map (E := sch.obj U ⨯ B) (prod.map (disc.map (yonedaEquiv.symm x)) (𝟙 B)) y)) = y := by
  apply prod_ext
  · rw [map_prodMap_fst, lift, mk_fst]
    exact Category.id_comp (Sx.map prod.fst y : W ⟶ U)
  · rw [map_prodMap_snd, lift, mk_snd]
    exact map_prodMap_snd (A := sch.obj U)
      (show sch.obj U ⟶ disc.obj F from disc.map (yonedaEquiv.symm x)) (𝟙 B) y

end GlobalTheory.EtC.GlueDisc

namespace GlobalTheory.EtC
open GlueDisc

theorem cochain_disc_glue (R : Type) [CommRing R] (q N : ℕ) (I : Cx R) (F : PSh) (n : ℤ)
    (c : ∀ U : Scheme.{0}, F.obj (op U) → Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) I n)
    (hc : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : F.obj (op U)),
      c V (F.map g.op x) = (Cochain.ofHom ((chains R).map (prod.map (sch.map g) (𝟙 (fibQ q N))))).comp (c U x) (zero_add n)) :
    ∃! γ : Cochain ((chains R).obj (disc.obj F ⨯ fibQ q N)) I n, ∀ (U : Scheme.{0}) (x : F.obj (op U)),
      (Cochain.ofHom ((chains R).map (prod.map (disc.map (yonedaEquiv.symm x)) (𝟙 (fibQ q N))))).comp γ (zero_add n) =
        c U x := by
  obtain ⟨γ, hγ⟩ := ev_exists (R := R) (E := disc.obj F ⨯ fibQ q N) (I := I) (n := n)
    (fun p s h V z => ev (c V (Sx.map prod.fst z)) p s h V (lift z)) (by
      intro p s h V U g z
      rw [ev_res, lift_res, map_res]
      refine (ev_pull (prod.map (sch.map g) (𝟙 (fibQ q N))) (c U (Sx.map prod.fst z)) p s h V
        (lift (Sx.res g z))).symm.trans ?_
      rw [← hc]
      rfl)
  refine ⟨γ, fun U x => ev_ext (E := sch.obj U ⨯ fibQ q N) _ _ fun p s h W y => ?_, fun γ' hγ' => ev_ext _ _ fun p s h V z => ?_⟩
  · refine (ev_pull (E' := sch.obj U ⨯ fibQ q N) (prod.map (disc.map (yonedaEquiv.symm x)) (𝟙 (fibQ q N))) γ
      p s h W y).trans ?_
    rw [hγ, fst_pull]
    refine (congrArg (fun α => ev α p s h W _) (hc W U (Sx.map prod.fst y : W ⟶ U) x)).trans ?_
    rw [ev_pull, lift_pull]
  · rw [hγ, ← hγ' V (Sx.map prod.fst z)]
    refine (congrArg (ev γ' p s h V) (lift_spec z)).symm.trans ?_
    exact (ev_pull (E' := sch.obj V ⨯ fibQ q N) _ γ' p s h V (lift z)).symm

end GlobalTheory.EtC
end
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unique_cochain_on_disc_product : ∀ (R : Type) [CommRing R] (q N : ℕ) (I : Cx R) (F : PSh) (n : ℤ) (c : ∀ U : Scheme.{0}, F.obj (op U) → Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) I n), (∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : F.obj (op U)), c V (F.map g.op x) = (Cochain.ofHom ((chains R).map (prod.map (sch.map g) (𝟙 (fibQ q N))))).comp (c U x) (zero_add n)) → ∃! γ : Cochain ((chains R).obj (disc.obj F ⨯ fibQ q N)) I n, ∀ (U : Scheme.{0}) (x : F.obj (op U)), (Cochain.ofHom ((chains R).map (prod.map (disc.map (yonedaEquiv.symm x)) (𝟙 (fibQ q N))))).comp γ (zero_add n) = c U x := by
  first | (exact @GlobalTheory.EtC.cochain_disc_glue) | (exact GlobalTheory.EtC.cochain_disc_glue) | (intros; apply GlobalTheory.EtC.cochain_disc_glue  <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSimpleRingOfCentralIdem
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsReducedTensorIntNumberField
open NumberField
open scoped TensorProduct

namespace GlobalTheory

theorem isReduced_tensor_int_numberField (F K : Type) [Field F] [NumberField F] [Field K] :
    IsReduced (K ⊗[ℤ] F) := by
  haveI : Algebra.FormallyUnramified ℤ ℚ := Algebra.FormallyUnramified.of_isLocalization (nonZeroDivisors ℤ)
  haveI : Algebra.FormallyUnramified ℚ F := Algebra.FormallyUnramified.of_isSeparable ℚ F
  haveI : Algebra.FormallyUnramified ℤ F := Algebra.FormallyUnramified.comp ℤ ℚ F
  haveI : Algebra.EssFiniteType ℤ ℚ := Algebra.EssFiniteType.of_isLocalization ℚ (nonZeroDivisors ℤ)
  haveI : Algebra.EssFiniteType ℤ F := Algebra.EssFiniteType.comp ℤ ℚ F
  haveI : Algebra.FormallyUnramified K (K ⊗[ℤ] F) := inferInstance
  haveI : Algebra.EssFiniteType K (K ⊗[ℤ] F) := inferInstance
  exact Algebra.FormallyUnramified.isReduced_of_field K (K ⊗[ℤ] F)

end GlobalTheory
end

noncomputable section
namespace GlobalTheory.UPel.HT.Gen

open NumberField
open scoped TensorProduct

theorem GDatum.O_nontrivial (G : GDatum) : Nontrivial G.O := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  have h1 := G.rankO
  rw [Module.finrank_zero_of_subsingleton] at h1
  have : 0 < G.m ^ 2 * Module.finrank ℚ G.F := Nat.mul_pos (pow_pos G.m_pos 2) Module.finrank_pos
  omega

theorem GDatum.tmul_one_injective (G : GDatum) : Function.Injective (fun o : G.O => (1 : ℚ) ⊗ₜ[ℤ] o) := by
  haveI := G.freeO
  have := Algebra.TensorProduct.includeRight_injective (R := ℤ) (A := ℚ) (B := G.O)
    (algebraMap ℤ ℚ).injective_int
  exact fun a b h => this h

theorem GDatum.exists_smul_eq_tmul (G : GDatum) (z : ℚ ⊗[ℤ] G.O) :
    ∃ N : ℤ, N ≠ 0 ∧ ∃ x : G.O, N • z = (1 : ℚ) ⊗ₜ x := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨1, one_ne_zero, 0, by simp⟩
  | tmul q o =>
    refine ⟨q.den, by exact_mod_cast q.den_nz, q.num • o, ?_⟩
    have : ((q.den : ℤ) • q) = (q.num : ℤ) • (1 : ℚ) := by
      rw [zsmul_eq_mul, zsmul_eq_mul, mul_one]; push_cast; exact Rat.den_mul_eq_num q
    rw [TensorProduct.smul_tmul', this, TensorProduct.smul_tmul]
  | add x y ihx ihy =>
    obtain ⟨N1, h1, x1, e1⟩ := ihx
    obtain ⟨N2, h2, x2, e2⟩ := ihy
    refine ⟨N1 * N2, mul_ne_zero h1 h2, N2 • x1 + N1 • x2, ?_⟩
    rw [smul_add, mul_smul, mul_smul, smul_comm N1 N2 x, e1, e2, TensorProduct.tmul_add,
      TensorProduct.tmul_smul, TensorProduct.tmul_smul]

theorem GDatum.algebraMap_injective (G : GDatum) : Function.Injective (algebraMap (𝓞 G.F) G.O) := by
  haveI := G.freeO
  haveI := GDatum.O_nontrivial G
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro c hc
  by_contra h0
  have hI : (RingHom.ker (algebraMap (𝓞 G.F) G.O)).comap (algebraMap ℤ (𝓞 G.F)) ≠ ⊥ :=
    Ideal.comap_ne_bot_of_integral_mem h0 hc (Algebra.IsIntegral.isIntegral c)
  obtain ⟨k, hk, hk0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  rw [Ideal.mem_comap, RingHom.mem_ker, ← IsScalarTower.algebraMap_apply] at hk
  have h2 : k • (1 : G.O) = 0 := by rw [zsmul_eq_mul, mul_one]; simpa using hk
  exact one_ne_zero ((smul_eq_zero.mp h2).resolve_left hk0)

theorem GDatum.smul_eq_zero_int (G : GDatum) {N : ℤ} (hN : N ≠ 0) {z : ℚ ⊗[ℤ] G.O} (h : N • z = 0) : z = 0 := by
  rw [← Int.cast_smul_eq_zsmul ℚ] at h
  exact (smul_eq_zero.mp h).resolve_left (by exact_mod_cast hN)

theorem GDatum.central_idem (G : GDatum) (e : ℚ ⊗[ℤ] G.O) (he : IsIdempotentElem e)
    (hc : ∀ y, e * y = y * e) : e = 0 ∨ e = 1 := by
  obtain ⟨N, hN, x, hx⟩ := GDatum.exists_smul_eq_tmul G e
  have hxc : ∀ y : G.O, x * y = y * x := by
    intro y
    apply GDatum.tmul_one_injective G
    have e1 : (1:ℚ) ⊗ₜ[ℤ] (x*y) = N • (e * (1 ⊗ₜ y)) := by
      rw [← smul_mul_assoc, hx, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    have e2 : (1:ℚ) ⊗ₜ[ℤ] (y*x) = N • ((1 ⊗ₜ y) * e) := by
      rw [← mul_smul_comm, hx, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    show (1:ℚ) ⊗ₜ[ℤ] (x*y) = (1:ℚ) ⊗ₜ[ℤ] (y*x)
    rw [e1, e2, hc]
  obtain ⟨c, k, hk, hkc⟩ := G.central x hxc
  set a := algebraMap (𝓞 G.F) G.O c with ha
  set M := N * k with hMdef
  have hM0 : M ≠ 0 := mul_ne_zero hN hk
  have hM : M • e = (1:ℚ) ⊗ₜ[ℤ] a := by
    rw [hMdef, mul_comm, mul_smul, hx, ← TensorProduct.tmul_smul, hkc]
  have hsq : (1:ℚ) ⊗ₜ[ℤ] (a * a) = (1:ℚ) ⊗ₜ[ℤ] (M • a) := by
    calc (1:ℚ) ⊗ₜ[ℤ] (a * a) = ((1:ℚ) ⊗ₜ[ℤ] a) * ((1:ℚ) ⊗ₜ[ℤ] a) := by
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
      _ = (M • e) * (M • e) := by rw [hM]
      _ = M • (M • (e * e)) := by rw [smul_mul_assoc, mul_smul_comm]
      _ = M • ((1:ℚ) ⊗ₜ[ℤ] a) := by rw [he.eq, hM]
      _ = _ := by rw [TensorProduct.tmul_smul]
  have haa : a * a = M • a := GDatum.tmul_one_injective G hsq
  have hc2 : c * (c - (M : 𝓞 G.F)) = 0 := by
    apply GDatum.algebraMap_injective G
    rw [map_mul, map_sub, map_intCast, map_zero, mul_sub, sub_eq_zero, ← ha, haa, zsmul_eq_mul]
    exact Int.cast_comm M a
  rcases mul_eq_zero.mp hc2 with h | h
  · left
    apply GDatum.smul_eq_zero_int G hM0
    rw [hM, ha, h, map_zero, TensorProduct.tmul_zero]
  · right
    rw [sub_eq_zero] at h
    have : M • (e - 1) = 0 := by
      rw [smul_sub, hM, ha, h, map_intCast, Algebra.TensorProduct.one_def, ← TensorProduct.tmul_smul,
        zsmul_eq_mul, mul_one, sub_self]
    exact sub_eq_zero.mp (GDatum.smul_eq_zero_int G hM0 this)

theorem isSimpleRing_of_central_idem {R : Type} [Ring R] [IsSemisimpleRing R] [Nontrivial R]
    (h : ∀ e : R, IsIdempotentElem e → (∀ y, e * y = y * e) → e = 0 ∨ e = 1) : IsSimpleRing R := by
  obtain ⟨n, D, d, _, hd, ⟨φ⟩⟩ := IsSemisimpleRing.exists_ringEquiv_pi_matrix_divisionRing R
  have hne : ∀ i, (1 : Matrix (Fin (d i)) (Fin (d i)) (D i)) ≠ 0 := fun i => by
    haveI := hd i
    exact one_ne_zero
  obtain _ | _ | n := n
  · exfalso
    obtain ⟨a, b, hab⟩ := exists_pair_ne R
    exact hab (φ.injective (Subsingleton.elim _ _))
  · haveI : Unique (Fin (0 + 1)) := inferInstanceAs (Unique (Fin 1))
    exact IsSimpleRing.of_ringEquiv (φ.trans (RingEquiv.piUnique _)).symm inferInstance
  · exfalso
    let s : (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) := Pi.single 0 1
    have hs : ∀ y, s * y = y * s := fun y => by
      funext i
      by_cases hi : i = 0
      · subst hi; simp [s]
      · simp [s, Pi.single_apply, hi]
    have hidem : IsIdempotentElem (φ.symm s) := by
      rw [IsIdempotentElem, ← map_mul]; congr 1
      funext i; by_cases hi : i = 0
      · subst hi; simp [s]
      · simp [s, Pi.single_apply, hi]
    rcases h (φ.symm s) hidem (fun y => by
        apply φ.injective; rw [map_mul, map_mul, RingEquiv.apply_symm_apply, hs]) with h0 | h1
    · have : s = 0 := by rw [← map_zero φ.symm] at h0; exact φ.symm.injective h0
      exact hne 0 (by simpa [s] using congr_fun this 0)
    · have : s = 1 := by rw [← map_one φ.symm] at h1; exact φ.symm.injective h1
      have h1' := congr_fun this 1
      simp [s, Pi.single_apply] at h1' <;> exact hne 1 h1'.symm

theorem GDatum.isSemisimpleRing (G : GDatum) : IsSemisimpleRing (ℚ ⊗[ℤ] G.O) := by
  haveI := G.finO
  haveI := G.freeO
  haveI : IsArtinianRing (ℚ ⊗[ℤ] G.O) := IsArtinianRing.of_finite ℚ _
  obtain ⟨q, hq, ⟨Φ⟩⟩ := G.splitSome
  rw [IsArtinianRing.isSemisimpleRing_iff_jacobson, eq_bot_iff]
  obtain ⟨k, hk⟩ := IsSemiprimaryRing.isNilpotent (R := ℚ ⊗[ℤ] G.O)
  have hnil : ∀ z ∈ Ring.jacobson (ℚ ⊗[ℤ] G.O), z ^ k = 0 := fun z hz => by
    have := Ideal.pow_mem_pow hz k
    rw [hk, Submodule.zero_eq_bot, Submodule.mem_bot] at this
    exact this
  intro z hz
  rw [Submodule.mem_bot]
  obtain ⟨N, hN, x, hx⟩ := GDatum.exists_smul_eq_tmul G z
  have hxJ : (1:ℚ) ⊗ₜ[ℤ] x ∈ Ring.jacobson (ℚ ⊗[ℤ] G.O) := hx ▸ zsmul_mem hz N
  have hox : ∀ o : G.O, (o * x) ^ k = 0 := fun o => by
    apply GDatum.tmul_one_injective G
    have hm : ((1:ℚ) ⊗ₜ[ℤ] o) * ((1:ℚ) ⊗ₜ[ℤ] x) ∈ Ring.jacobson (ℚ ⊗[ℤ] G.O) :=
      Ideal.mul_mem_left _ _ hxJ
    have := hnil _ hm
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, Algebra.TensorProduct.tmul_pow, one_pow] at this
    show (1:ℚ) ⊗ₜ[ℤ] ((o * x) ^ k) = (1:ℚ) ⊗ₜ[ℤ] 0
    rw [this, TensorProduct.tmul_zero]
  haveI : IsReduced (𝓞 G.F ⊗[ℤ] ℤ_[q]) := by
    have h1 : Function.Injective
        ((algebraMap ℤ_[q] ℚ_[q]).toIntAlgHom.toLinearMap.lTensor (𝓞 G.F)) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ (IsFractionRing.injective ℤ_[q] ℚ_[q])
    have h2 : Function.Injective
        ((algebraMap (𝓞 G.F) G.F).toIntAlgHom.toLinearMap.rTensor ℚ_[q]) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ (IsFractionRing.injective (𝓞 G.F) G.F)
    let f : 𝓞 G.F ⊗[ℤ] ℤ_[q] →ₐ[ℤ] ℚ_[q] ⊗[ℤ] G.F :=
      (Algebra.TensorProduct.comm ℤ G.F ℚ_[q]).toAlgHom.comp
        (Algebra.TensorProduct.map (algebraMap (𝓞 G.F) G.F).toIntAlgHom (algebraMap ℤ_[q] ℚ_[q]).toIntAlgHom)
    have hmap : Function.Injective (Algebra.TensorProduct.map (algebraMap (𝓞 G.F) G.F).toIntAlgHom
        (algebraMap ℤ_[q] ℚ_[q]).toIntAlgHom) := by
      have : ⇑(Algebra.TensorProduct.map (algebraMap (𝓞 G.F) G.F).toIntAlgHom
          (algebraMap ℤ_[q] ℚ_[q]).toIntAlgHom) =
          ((algebraMap (𝓞 G.F) G.F).toIntAlgHom.toLinearMap.rTensor ℚ_[q]) ∘
          ((algebraMap ℤ_[q] ℚ_[q]).toIntAlgHom.toLinearMap.lTensor (𝓞 G.F)) := by
        funext w
        induction w using TensorProduct.induction_on with
        | zero => simp
        | tmul a b => rfl
        | add a b ha hb => simp only [map_add (f := _), Function.comp_apply] at ha hb ⊢; rw [ha, hb]
      rw [this]; exact h2.comp h1
    have hf : Function.Injective f := fun a b hab => hmap ((Algebra.TensorProduct.comm ℤ G.F ℚ_[q]).injective hab)
    haveI := GlobalTheory.isReduced_tensor_int_numberField G.F ℚ_[q]
    exact isReduced_of_injective f.toRingHom hf
  set y := Φ (x ⊗ₜ[ℤ] (1 : ℤ_[q])) with hy
  have htr : ∀ w : G.O ⊗[ℤ] ℤ_[q], (Φ w * y).trace = 0 := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul o c =>
      apply IsReduced.eq_zero
      apply Matrix.isNilpotent_trace_of_isNilpotent
      refine ⟨k, ?_⟩
      rw [hy, ← map_mul, ← map_pow, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
        Algebra.TensorProduct.tmul_pow, hox, TensorProduct.zero_tmul, map_zero]
    | add a b ha hb => rw [map_add (f := _), add_mul, Matrix.trace_add, ha, hb, add_zero]
  have hy0 : y = 0 := by
    ext i j
    have := htr (Φ.symm (Matrix.single j i 1))
    rw [AlgEquiv.apply_symm_apply, Matrix.trace_single_mul, one_smul] at this
    exact this
  have hx0 : x = 0 := by
    have h0 : x ⊗ₜ[ℤ] (1 : ℤ_[q]) = 0 := Φ.injective (hy0.trans (map_zero Φ).symm)
    have hinj := Algebra.TensorProduct.includeLeft_injective (R := ℤ) (S := ℤ) (A := G.O) (B := ℤ_[q])
      (algebraMap ℤ ℤ_[q]).injective_int
    exact hinj (h0.trans (TensorProduct.zero_tmul _ _).symm)
  apply GDatum.smul_eq_zero_int G hN
  rw [hx, hx0, TensorProduct.tmul_zero]

theorem GDatum.isSimpleRing (G : GDatum) : IsSimpleRing (ℚ ⊗[ℤ] G.O) := by
  haveI := GDatum.isSemisimpleRing G
  haveI := GDatum.O_nontrivial G
  haveI : Nontrivial (ℚ ⊗[ℤ] G.O) := by
    refine ⟨⟨1, 0, fun h => ?_⟩⟩
    have : (1 : G.O) = 0 := GDatum.tmul_one_injective G (by
      show (1:ℚ) ⊗ₜ[ℤ] (1 : G.O) = (1:ℚ) ⊗ₜ[ℤ] 0
      rw [TensorProduct.tmul_zero]; exact h)
    exact one_ne_zero this
  exact isSimpleRing_of_central_idem (fun e he hc => GDatum.central_idem G e he hc)
end GlobalTheory.UPel.HT.Gen
end
end
