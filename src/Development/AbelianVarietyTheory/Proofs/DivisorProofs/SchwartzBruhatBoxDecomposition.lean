module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeakExponentialActionOnFockVectors
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertiaFixedFieldMaximalIdealDvdUniformizer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.SevenLogLeLOfPowerBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumPowersUnramifiedEtaTilde
public import Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatBoxDecomposition
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatBoxDecomposition
open ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.RankCoinv.Decomp
open GlobalTheory.SplitFlip GlobalTheory.RankCoinv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A D : Type}

theorem val_unif_pow_le {ϖ : kˣ} (hϖ : IsUnif ϖ) {n m : ℕ} (h : n ≤ m) :
    valuation k ((ϖ ^ m : kˣ) : k) ≤ valuation k ((ϖ ^ n : kˣ) : k) := by
  simp only [Units.val_pow_eq_pow_val, map_pow]
  exact pow_le_pow_right_of_le_one' (show valuation k (ϖ : k) ≤ 1 from hϖ ▸ uniformizer_lt_one.le) h

theorem box_mono {ϖ : kˣ} (hϖ : IsUnif ϖ) (X : Matrix A D k) {n m : ℕ} (h : n ≤ m) :
    box ϖ X (fun _ => m) ⊆ box ϖ X (fun _ => n) :=
  fun _ hY i j => (hY i j).trans (val_unif_pow_le hϖ h)

theorem mem_box_self (ϖ : kˣ) (X : Matrix A D k) (e : A → ℕ) : X ∈ box ϖ X e :=
  fun i j => by simp

theorem eq_of_forall_mem_box {ϖ : kˣ} (hϖ : IsUnif ϖ) {X Y : Matrix A D k}
    (h : ∀ n : ℕ, Y ∈ box ϖ X (fun _ => n)) : Y = X := by
  ext i j
  by_contra hne
  have h0 : valuation k (Y i j - X i j) ≠ 0 := by simpa [sub_eq_zero] using hne
  obtain ⟨n, hn⟩ := exists_pow_lt₀ (show valuation k (ϖ : k) < 1 from hϖ ▸ uniformizer_lt_one) (Units.mk0 _ h0)
  have := h n i j
  simp only [Units.val_pow_eq_pow_val, map_pow] at this
  exact absurd this (not_le.2 hn)

variable [Fintype A] [Fintype D]

theorem exists_box_subset {ϖ : kˣ} (hϖ : IsUnif ϖ) {X : Matrix A D k} {U : Set (Matrix A D k)}
    (hU : U ∈ nhds X) : ∃ n : ℕ, box ϖ X (fun _ => n) ⊆ U := by
  refine exists_subset_nhds_of_isCompact' (V := fun n : ℕ => box ϖ X (fun _ => n))
    (Antitone.directed_ge fun a b h => box_mono hϖ X h) (fun n => isCompact_box ϖ X _)
    (fun n => (isClopen_box ϖ X _).isClosed) ?_
  apply mem_nhdsSet_iff_forall.2
  intro Y hY
  have hYX : Y = X := eq_of_forall_mem_box hϖ (Set.mem_iInter.1 hY)
  simpa only [hYX] using hU

theorem exists_sum_boxFn (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ) (hϖ : GlobalTheory.SplitFlip.IsUnif ϖ) :
    ∀ Φ ∈ GlobalTheory.WeilM.SB (Matrix A D k), ∃ m₁ : ℕ, ∀ m ≥ m₁, ∃ s : Finset (Matrix A D k),
      Φ = ∑ c ∈ s, Φ c • GlobalTheory.RankCoinv.boxFn ϖ c (fun _ => m) ∧
      ∀ c ∈ s, ∀ X ∈ GlobalTheory.RankCoinv.box ϖ c (fun _ => m), Φ X = Φ c := by
  classical
  intro Φ hΦ
  obtain ⟨hlc, hcs⟩ := hΦ
  have hrad : ∀ X, ∃ n : ℕ, box ϖ X (fun _ => n) ⊆ {Y | Φ Y = Φ X} := fun X =>
    exists_box_subset hϖ ((hlc.isOpen_fiber (Φ X)).mem_nhds rfl)
  choose n hn using hrad
  obtain ⟨t, ht⟩ := IsCompact.elim_finite_subcover hcs (fun X => box ϖ X (fun _ => n X))
    (fun X => (isClopen_box ϖ X _).isOpen) (fun Y _ => Set.mem_iUnion.2 ⟨Y, mem_box_self ϖ Y _⟩)
  refine ⟨t.sup n, fun m hm => ?_⟩
  have hconst : ∀ Y ∈ tsupport Φ, ∀ Z ∈ box ϖ Y (fun _ => m), Φ Z = Φ Y := by
    intro Y hY Z hZ
    obtain ⟨X, hXt, hYX⟩ := Set.mem_iUnion₂.1 (ht hY)
    have hsub : box ϖ Y (fun _ => m) ⊆ box ϖ X (fun _ => n X) := by
      rw [← box_eq_of_mem hYX]; exact box_mono hϖ Y ((Finset.le_sup hXt).trans hm)
    have h1 : Φ Z = Φ X := hn X (hsub hZ)
    have h2 : Φ Y = Φ X := hn X (hsub (mem_box_self ϖ Y _))
    rw [h1, h2]
  let rep : Set (Matrix A D k) → Matrix A D k := fun B =>
    if h : ∃ Z, box ϖ Z (fun _ => m) = B then h.choose else 0
  have hrep : ∀ Y, box ϖ (rep (box ϖ Y (fun _ => m))) (fun _ => m) = box ϖ Y (fun _ => m) := by
    intro Y
    have h : ∃ Z, box ϖ Z (fun _ => m) = box ϖ Y (fun _ => m) := ⟨Y, rfl⟩
    rw [show rep (box ϖ Y (fun _ => m)) = h.choose from dif_pos h]
    exact h.choose_spec
  obtain ⟨s₀, hs₀⟩ := IsCompact.elim_finite_subcover hcs
    (fun Y : tsupport Φ => box ϖ (Y : Matrix A D k) (fun _ => m))
    (fun Y => (isClopen_box ϖ _ _).isOpen) (fun Y hY => Set.mem_iUnion.2 ⟨⟨Y, hY⟩, mem_box_self ϖ Y _⟩)
  let s : Finset (Matrix A D k) := s₀.image (fun Y : tsupport Φ => rep (box ϖ (Y : Matrix A D k) (fun _ => m)))
  have hs : ∀ c ∈ s, ∃ Y ∈ tsupport Φ, c = rep (box ϖ Y (fun _ => m)) := by
    intro c hc
    obtain ⟨Y, -, rfl⟩ := Finset.mem_image.1 hc
    exact ⟨Y, Y.2, rfl⟩
  have hval : ∀ c ∈ s, ∀ Z ∈ box ϖ c (fun _ => m), Φ Z = Φ c := by
    intro c hc Z hZ
    obtain ⟨Y, hY, rfl⟩ := hs c hc
    rw [hrep] at hZ
    have hcY : rep (box ϖ Y (fun _ => m)) ∈ box ϖ Y (fun _ => m) := by
      have := mem_box_self ϖ (rep (box ϖ Y (fun _ => m))) (fun _ => m)
      rwa [hrep] at this
    rw [hconst Y hY Z hZ, hconst Y hY _ hcY]
  have huniq : ∀ c ∈ s, ∀ c' ∈ s, ∀ Z, Z ∈ box ϖ c (fun _ => m) → Z ∈ box ϖ c' (fun _ => m) → c = c' := by
    intro c hc c' hc' Z hZ hZ'
    obtain ⟨Y, -, rfl⟩ := hs c hc
    obtain ⟨Y', -, rfl⟩ := hs c' hc'
    have e1 := box_eq_of_mem hZ
    have e2 := box_eq_of_mem hZ'
    rw [hrep] at e1 e2
    rw [← e1, ← e2]
  have hcov : ∀ Z, Φ Z ≠ 0 → ∃ c ∈ s, Z ∈ box ϖ c (fun _ => m) := by
    intro Z hZ
    obtain ⟨Y, hY, hZY⟩ := Set.mem_iUnion₂.1 (hs₀ (subset_tsupport Φ hZ))
    refine ⟨rep (box ϖ (Y : Matrix A D k) (fun _ => m)), Finset.mem_image_of_mem _ hY, ?_⟩
    rw [hrep]; exact hZY
  refine ⟨s, ?_, hval⟩
  funext Z
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, boxFn]
  by_cases h : ∃ c ∈ s, Z ∈ box ϖ c (fun _ => m)
  · obtain ⟨c, hc, hZ⟩ := h
    rw [Finset.sum_eq_single c]
    · rw [Set.indicator_of_mem hZ, Pi.one_apply, mul_one, hval c hc Z hZ]
    · intro c' hc' hne
      rw [Set.indicator_of_notMem (fun hZ' => hne (huniq c' hc' c hc Z hZ' hZ)), mul_zero]
    · intro hcs'; exact absurd hc hcs'
  · push_neg at h
    rw [Finset.sum_eq_zero fun c hc => by rw [Set.indicator_of_notMem (h c hc), mul_zero]]
    by_contra hZ
    obtain ⟨c, hc, hZc⟩ := hcov Z hZ
    exact h c hc hZc

end GlobalTheory.RankCoinv.Decomp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatBoxDecompositionStatement
open ValuativeRel Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_bruhat_box_decomposition : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ Φ ∈ GlobalTheory.WeilM.SB (Matrix A D k), ∃ m₁ : ℕ, ∀ m ≥ m₁, ∃ s : Finset (Matrix A D k), Φ = ∑ c ∈ s, Φ c • GlobalTheory.RankCoinv.boxFn ϖ c (fun _ => m) ∧ ∀ c ∈ s, ∀ X ∈ GlobalTheory.RankCoinv.box ϖ c (fun _ => m), Φ X = Φ c := by
  first | exact @GlobalTheory.RankCoinv.Decomp.exists_sum_boxFn | exact GlobalTheory.RankCoinv.Decomp.exists_sum_boxFn | (intros; apply GlobalTheory.RankCoinv.Decomp.exists_sum_boxFn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDiscreteValuationRingFixedFieldInertia
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDiscreteValuationRingFixedFieldInertia
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.InertiaFixedDVR

theorem isDiscreteValuationRing_fixedField_inertia : ∀ (R K Ω : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K]
    [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring →
    IsDiscreteValuationRing (V.comap (algebraMap (IntermediateField.fixedField (inertia K V)) Ω)) := by
  intro R K Ω _ _ _ _ _ _ _ _ _ _ V hV
  classical
  set K' := IntermediateField.fixedField (inertia K V) with hK'
  set W := V.comap (algebraMap K' Ω) with hW
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  set c : Ω := algebraMap K Ω (algebraMap R K π) with hc
  have hπK : algebraMap R K π ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]; exact hπ.ne_zero
  have hc0 : c ≠ 0 := (map_ne_zero _).2 hπK
  have hcV : c ∈ V := by
    have h : algebraMap R K π ∈ V.toSubring.comap (algebraMap K Ω) := by rw [hV]; exact ⟨π, rfl⟩
    exact h
  have hcinv : c⁻¹ ∉ V := by
    intro h
    have h' : (algebraMap R K π)⁻¹ ∈ V.toSubring.comap (algebraMap K Ω) := by
      change algebraMap K Ω (algebraMap R K π)⁻¹ ∈ V
      rw [map_inv₀]; exact h
    rw [hV] at h'
    obtain ⟨r, hr⟩ := h'
    apply hπ.not_isUnit
    refine isUnit_iff_exists_inv.2 ⟨r, IsFractionRing.injective R K ?_⟩
    rw [map_mul, hr, map_one, mul_inv_cancel₀ hπK]
  have hcK' : c ∈ K' := K'.algebraMap_mem _

  let j : W → Ω := fun w => ((w : K') : Ω)
  have hjinj : Function.Injective j := fun a b h => Subtype.ext (Subtype.ext h)
  have hjV : ∀ w : W, j w ∈ V := fun w => w.2
  have hjK : ∀ w : W, j w ∈ K' := fun w => (w : K').2
  have hj_mul : ∀ a b : W, j (a * b) = j a * j b := fun _ _ => rfl
  have hj_zero : j 0 = 0 := rfl
  have hj_one : j 1 = 1 := rfl
  have hj_pow : ∀ (a : W) (n : ℕ), j (a ^ n) = j a ^ n := by
    intro a n
    induction n with
    | zero => simpa using hj_one
    | succ n ih => rw [pow_succ, hj_mul, ih, pow_succ]
  let mk : (y : Ω) → y ∈ K' → y ∈ V → W := fun y h1 h2 => ⟨⟨y, h1⟩, h2⟩
  have hunit : ∀ w : W, j w ≠ 0 → (j w)⁻¹ ∈ V → IsUnit w := by
    intro w h0 hinv
    refine isUnit_iff_exists_inv.2 ⟨mk (j w)⁻¹ (K'.inv_mem (hjK w)) hinv, hjinj ?_⟩
    rw [hj_mul, hj_one]
    exact mul_inv_cancel₀ h0
  have hdvd : ∀ w : W, ¬ IsUnit w → ∃ u : W, w = mk c hcK' hcV * u := by
    intro w hw
    have hnu : j w ∈ V.nonunits := by
      rw [GlobalTheory.FixInertUnram.mem_nonunits_iff']
      by_cases h0 : j w = 0
      · exact Or.inl h0
      · exact Or.inr fun h => hw (hunit w h0 h)
    have hq := GlobalTheory.FixInertUnram.div_uniformizer_mem R K Ω V hV π hπ (j w) (hjK w) hnu
    refine ⟨mk (j w / c) (K'.div_mem (hjK w) hcK') hq, hjinj ?_⟩
    rw [hj_mul]
    change j w = c * (j w / c)
    field_simp
  set ϖ : W := mk c hcK' hcV with hϖ
  have hϖnu : ¬ IsUnit ϖ := by
    intro h
    obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.1 h
    apply hcinv
    have e : c * j v = 1 := by
      have := congrArg j hv
      rw [hj_mul, hj_one] at this
      exact this
    rw [inv_eq_of_mul_eq_one_right e]
    exact hjV v
  have hϖ0 : ϖ ≠ 0 := fun h => hc0 (by have := congrArg j h; rw [hj_zero] at this; exact this)
  have hirr : Irreducible ϖ := by
    refine ⟨hϖnu, fun a b hab => ?_⟩
    by_contra hne
    push_neg at hne
    obtain ⟨a', rfl⟩ := hdvd a hne.1
    obtain ⟨b', rfl⟩ := hdvd b hne.2
    apply hϖnu
    have e : ϖ * 1 = ϖ * (ϖ * (a' * b')) := by
      rw [_root_.mul_one]
      calc ϖ = ϖ * a' * (ϖ * b') := hab
        _ = ϖ * (ϖ * (a' * b')) := by ring
    have h1 := mul_left_cancel₀ hϖ0 e
    exact isUnit_iff_exists_inv.2 ⟨a' * b', h1.symm⟩
  refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨ϖ, hirr, fun {x} hx => ?_⟩
  have hx0 : j x ≠ 0 := fun h => hx (hjinj (h.trans hj_zero.symm))
  have hex : ∃ n : ℕ, j x / c ^ n ∉ V := GlobalTheory.not_mem_div_uniformizer_pow R K Ω V hV π hπ (j x) hx0
  obtain ⟨n, hn, hmin⟩ : ∃ n : ℕ, j x / c ^ n ∉ V ∧ ∀ k < n, j x / c ^ k ∈ V :=
    ⟨Nat.find hex, Nat.find_spec hex, fun k hk => by simpa using Nat.find_min hex hk⟩
  have hn0 : n ≠ 0 := by
    rintro rfl
    apply hn
    rw [pow_zero, div_one]
    exact hjV x
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hmV : j x / c ^ m ∈ V := hmin m (by omega)
  have hyK : j x / c ^ m ∈ K' := K'.div_mem (hjK x) (pow_mem hcK' m)
  have hy0 : j x / c ^ m ≠ 0 := div_ne_zero hx0 (pow_ne_zero _ hc0)
  have hyinv : (j x / c ^ m)⁻¹ ∈ V := by
    by_contra hyi
    have hq := GlobalTheory.FixInertUnram.div_uniformizer_mem R K Ω V hV π hπ (j x / c ^ m) hyK
      ((GlobalTheory.FixInertUnram.mem_nonunits_iff' V _).2 (Or.inr hyi))
    apply hn
    rw [pow_succ, ← div_div]
    exact hq
  have hu : IsUnit (mk (j x / c ^ m) hyK hmV) := hunit _ hy0 hyinv
  refine ⟨m, hu.unit, hjinj ?_⟩
  rw [IsUnit.unit_spec, hj_mul, hj_pow]
  change c ^ m * (j x / c ^ m) = j x
  field_simp

end GlobalTheory.InertiaFixedDVR
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDiscreteValuationRingFixedFieldInertiaStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDiscreteValuationRing_fixedField_inertia_alt : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → IsDiscreteValuationRing (V.comap (algebraMap (IntermediateField.fixedField (inertia K V)) Ω)) := by
  first | exact @GlobalTheory.InertiaFixedDVR.isDiscreteValuationRing_fixedField_inertia | exact GlobalTheory.InertiaFixedDVR.isDiscreteValuationRing_fixedField_inertia | (intros; apply GlobalTheory.InertiaFixedDVR.isDiscreteValuationRing_fixedField_inertia <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothCharacterOrbitalIntegralStable
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothCharacterOrbitalIntegralStable
noncomputable section

open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix Topology

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL

namespace GlobalTheory.FullRankCoinv.Average

theorem integral_comp_finite {G V : Type*} [MeasurableSpace G] (μ : Measure G) [IsFiniteMeasure μ] (F : G → V)
    (T : Finset V) (hT : ∀ᵐ g ∂μ, F g ∈ T) (hm : ∀ v, MeasurableSet (F ⁻¹' {v})) (φ : V → ℂ) :
    ∫ g, φ (F g) ∂μ = ∑ v ∈ T, (μ.real (F ⁻¹' {v}) : ℂ) * φ v := by
  classical
  have h1 : (fun g => φ (F g)) =ᵐ[μ] fun g => ∑ v ∈ T, (F ⁻¹' {v}).indicator (fun _ => φ v) g := by
    filter_upwards [hT] with g hg
    rw [Finset.sum_eq_single (F g)]
    · rw [Set.indicator_of_mem (by simp)]
    · intro v _ hv
      exact Set.indicator_of_notMem (by simpa using hv.symm) _
    · exact fun h => absurd hg h
  rw [integral_congr_ae h1, integral_finsetSum _ fun v _ => (integrable_const _).indicator (hm v)]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [integral_indicator_const _ (hm v), Complex.real_smul]

theorem sb_left_invariant {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n d : ℕ} (Ψ : Matrix (Fin n) (Fin d) k → ℂ) (hΨ : Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k)) :
    ∀ᶠ u in 𝓝 (1 : GL (Fin n) k), ∀ X : Matrix (Fin n) (Fin d) k, Ψ (u.val * X) = Ψ X := by
  have h1 : ∀ᶠ u in 𝓝 (1 : GL (Fin n) k), ∀ X ∈ tsupport Ψ, Ψ (u.val * X) = Ψ X := by
    refine IsCompact.eventually_forall_of_forall_eventually hΨ.2 fun y _ => ?_
    have h2 : IsLocallyConstant fun q : GL (Fin n) k × Matrix (Fin n) (Fin d) k => (Ψ (q.1.val * q.2), Ψ q.2) :=
      (hΨ.1.comp_continuous (by fun_prop)).prodMk (hΨ.1.comp_continuous continuous_snd)
    filter_upwards [h2.eventually_eq (1, y)] with q hq
    simp only [Prod.mk.injEq, Units.val_one, Matrix.one_mul] at hq
    rw [hq.1, hq.2]
  have h3 : ∀ᶠ u in 𝓝 (1 : GL (Fin n) k), ∀ X ∈ tsupport Ψ, Ψ ((u⁻¹).val * X) = Ψ X := by
    have ht : Filter.Tendsto (fun u : GL (Fin n) k => u⁻¹) (𝓝 1) (𝓝 1) := by
      simpa using (continuous_inv.tendsto (1 : GL (Fin n) k))
    exact ht.eventually h1
  filter_upwards [h1, h3] with u hu1 hu2 X
  by_cases hX : X ∈ tsupport Ψ
  · exact hu1 X hX
  by_cases hX' : u.val * X ∈ tsupport Ψ
  · have := hu2 _ hX'
    rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul] at this
    exact this.symm
  · rw [image_eq_zero_of_notMem_tsupport hX, image_eq_zero_of_notMem_tsupport hX']

theorem mem_augRk_of_smallF_eq_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (n d : ℕ) (ν : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν →
    ∀ (S : Set (Matrix (Fin n) (Fin d) k)),
    (∀ (E : GL (Fin n) k), ∀ Y ∈ S, E.val * Y ∈ S → E ∈ GlobalTheory.SplitWeil.KO k (Fin n)) →
    (∀ E ∈ GlobalTheory.SplitWeil.KO k (Fin n), ∀ Y ∈ S, E.val * Y ∈ S) →
    ∀ Φ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, (∀ Y, Y ∉ S → Φ Y = 0) →
    (∀ Y ∈ S, smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Φ Y = 0) → Φ ∈ GlobalTheory.FullRankCoinv.augRk n d ν := by
  intro k _ _ _ _ _ _ n d ν hν S hrig hst Φ hΦ hsupp h0
  have : BorelSpace (GL (Fin n) k) := borel_GL
  set K := GlobalTheory.SplitWeil.KO k (Fin n) with hK
  have hKo : IsOpen (K : Set (GL (Fin n) k)) := isOpen_KO
  have hKm : MeasurableSet (K : Set (GL (Fin n) k)) := hKo.measurableSet
  have hK1 : haarVol K K = 1 := haarVol_self isOpen_KO le_rfl
  let F : GL (Fin n) k → Matrix (Fin n) (Fin d) k → ℂ :=
    fun g Y => Φ (g.val * Y) * (ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card (Fin d) : ℂ) / 2)
  have hFl : ∀ g, F g = lact ν (invT g)⁻¹ Φ := fun g => by
    funext Y
    have e1 : gdet (invT g)⁻¹ = gdet g := by
      rw [show gdet (invT g)⁻¹ = (gdet (invT g))⁻¹ from map_inv _ _, gdet_invT, inv_inv]
    simp only [F, lact, e1, invT_inv_val, Matrix.transpose_transpose, Fintype.card_fin]
    ring
  have hev : ∀ᶠ u in 𝓝 (1 : GL (Fin n) k), ∀ g, F (u * g) = F g := by
    have h2 : ∀ᶠ u in 𝓝 (1 : GL (Fin n) k), ν (gdet u) = 1 := by
      have : IsOpen ((fun u : GL (Fin n) k => Matrix.GeneralLinearGroup.det u) ⁻¹' (ν.ker : Set kˣ)) :=
        IsOpen.preimage Matrix.GeneralLinearGroup.continuous_det hν
      exact this.mem_nhds (by simp)
    filter_upwards [sb_left_invariant Φ hΦ.1, h2, hKo.mem_nhds (one_mem K)] with u h1 h2 h3 g
    funext Y
    simp only [F, gdet_mul, map_mul, h2, apow_mul, apow_of_valuation_eq_one (valuation_gdet_of_mem_KO h3),
      Units.val_mul, Matrix.mul_assoc, h1, one_mul]
  have hlc : IsLocallyConstant F := by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
    have ht : Filter.Tendsto (fun y : GL (Fin n) k => y * x⁻¹) (𝓝 x) (𝓝 1) := by
      simpa using ((continuous_mul_const x⁻¹).tendsto x)
    filter_upwards [ht.eventually hev] with y hy
    simpa using hy x
  have hfin : (F '' K).Finite := by
    have : CompactSpace K := isCompact_iff_compactSpace.1 (isCompact_KO (k := k) (n := Fin n))
    have h := (hlc.comp_continuous (continuous_subtype_val (p := fun g => g ∈ K))).range_finite
    refine h.subset ?_
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨⟨g, hg⟩, rfl⟩
  set μ := (haarVol K).restrict K with hμ
  have hμ1 : μ Set.univ = 1 := by rw [hμ, Measure.restrict_apply_univ, hK1]
  have : IsFiniteMeasure μ := ⟨by rw [hμ1]; exact ENNReal.one_lt_top⟩
  have hI := integral_comp_finite μ F hfin.toFinset
    (by
      filter_upwards [ae_restrict_mem hKm] with g hg
      exact hfin.mem_toFinset.2 ⟨g, hg, rfl⟩)
    (fun v => (hlc.isOpen_fiber v).measurableSet)
  have hs1 : ∑ v ∈ hfin.toFinset, (μ.real (F ⁻¹' {v}) : ℂ) = 1 := by
    have := hI fun _ => 1
    simpa [Measure.real, hμ1] using this.symm
  have hA : ∑ v ∈ hfin.toFinset, (μ.real (F ⁻¹' {v}) : ℂ) • v = 0 := by
    funext Y
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [← hI fun v => v Y]
    by_cases hY : Y ∈ S
    · rw [hμ, setIntegral_eq_integral_of_forall_compl_eq_zero]
      · exact h0 Y hY
      · intro g hg
        have : g.val * Y ∉ S := fun h => hg (hrig g Y hY h)
        simp [F, hsupp _ this]
    · refine setIntegral_eq_zero_of_forall_eq_zero fun g hg => ?_
      have : g.val * Y ∉ S := fun h => hY (by
        have := hst g⁻¹ (inv_mem hg) _ h
        rwa [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul] at this)
      simp [F, hsupp _ this]
  have hΦe : Φ = -∑ v ∈ hfin.toFinset, (μ.real (F ⁻¹' {v}) : ℂ) • (v - Φ) := by
    simp only [smul_sub, Finset.sum_sub_distrib, hA, ← Finset.sum_smul, hs1, one_smul, zero_sub, neg_neg]
  rw [hΦe]
  refine neg_mem (Submodule.sum_mem _ fun v hv => Submodule.smul_mem _ _ ?_)
  obtain ⟨g, -, rfl⟩ := hfin.mem_toFinset.1 hv
  exact Submodule.subset_span ⟨(invT g)⁻¹, Φ, hΦ, by rw [hFl]⟩

end GlobalTheory.FullRankCoinv.Average
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothCharacterOrbitalIntegralStableStatement
open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_character_orbital_integral_stable : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (n d : ℕ) (ν : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν →
    ∀ (S : Set (Matrix (Fin n) (Fin d) k)),
    (∀ (E : GL (Fin n) k), ∀ Y ∈ S, E.val * Y ∈ S → E ∈ GlobalTheory.SplitWeil.KO k (Fin n)) →
    (∀ E ∈ GlobalTheory.SplitWeil.KO k (Fin n), ∀ Y ∈ S, E.val * Y ∈ S) →
    ∀ Φ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, (∀ Y, Y ∉ S → Φ Y = 0) →
    (∀ Y ∈ S, smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Φ Y = 0) → Φ ∈ GlobalTheory.FullRankCoinv.augRk n d ν := by
  first | exact @GlobalTheory.FullRankCoinv.Average.mem_augRk_of_smallF_eq_zero | exact GlobalTheory.FullRankCoinv.Average.mem_augRk_of_smallF_eq_zero | (intros; apply GlobalTheory.FullRankCoinv.Average.mem_augRk_of_smallF_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamRowsSizes
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwoLeOfLogPos
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2 GlobalTheory.CoreHt
open GlobalTheory.ColumnNormCompare (numDatumOfParameters codeRec plRec)
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.CoreHt.RowsOfDesign

theorem two_le_of_log_pos' (n : ℕ) (h : 0 < Real.log (n : ℝ)) : 2 ≤ n := by
  by_contra hn
  have h1 : n = 0 ∨ n = 1 := by omega
  rcases h1 with rfl | rfl <;> simp at h

theorem two_le_rdE' (D : D7) (hq : 2 ≤ D.host.q) (hd : 2 ≤ D.host.d) : 2 ≤ D.host.rdE := by
  have h := (factRd D.R D.host).2.2
  have hf : (2 : ℝ) ≤ D.R.f := by
    have := D.host.four_le_n'
    have h2 : D.R.f = 2 * D.R.n := rfl
    exact_mod_cast (by omega : 2 ≤ D.R.f)
  have h0 : 0 ≤ D.host.rdE := by unfold Host.rdE; positivity
  nlinarith

theorem rows_of_design : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L), Formalism.MainNotions.SizesAt L → Real.log (4 * L.sc.x) ≤ L.sc.L →
    DelNat D → ThickUp L → HtRowsS L P.CYL := by
  intro D L P hS hx4 hDN hTU
  obtain ⟨-, -, -, -, hT, hCond, hQD, -, hLa, hRho, hBot, -, -, hEta, hNodes, -, hDel, -⟩ := hS
  have hx1 : 1 < L.sc.x := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have hL1 : 1 ≤ L.sc.L := by unfold Scale.L; exact Real.one_le_rpow hx1.le L.sc.eps_pos.le
  have hq2 : 2 ≤ D.host.q := two_le_of_log_pos' _ (lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hQD.1)
  have hd2 : 2 ≤ D.host.d := two_le_of_log_pos' _ (lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hQD.2.2.2.1)
  have hq' : (2 : ℝ) ≤ D.host.q := by exact_mod_cast hq2
  have hd' : (2 : ℝ) ≤ D.host.d := by exact_mod_cast hd2
  have hrd2 := two_le_rdE' D hq2 hd2
  have hn1 : (1 : ℝ) ≤ D.R.n := by
    have : 1 ≤ D.R.n := by have := D.host.four_le_n'; omega
    exact_mod_cast this
  have ht1 : (1 : ℝ) ≤ D.R.t := hT.1
  have hm1 : (1 : ℝ) ≤ D.R.m := by
    have : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
    exact_mod_cast this
  have hk0 : (0 : ℝ) < D.R.k := by
    have : 0 < D.R.k := by have := D.R.m_add_three_le_k; omega
    exact_mod_cast this
  have hb1 : 1 ≤ L.sc.b := by unfold Scale.b; exact Real.one_le_exp (by linarith)
  refine ⟨⟨P⟩, ⟨?_, hQD.2.2.2.2.2.1, hx4⟩, ?_, ⟨?_, hEta.1, hEta.2.2.2.2.1, hDel.2.2.2.1, ?_⟩, hDN, hTU⟩
  ·
    have hqd : (1 : ℝ) ≤ (D.host.q : ℝ) * D.host.d := by nlinarith
    have hs : Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ (D.host.q : ℝ) * D.host.d :=
      Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
    have hc : D.host.rdE ≤ Formalism.MainNotions.szCond L := by
      refine hQD.2.2.2.2.2.2.2.trans ?_
      unfold Formalism.MainNotions.szCond
      have : (D.host.QS : ℝ) / 2 * Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤
          (D.host.QS : ℝ) / 2 * ((D.host.q : ℝ) * D.host.d) := mul_le_mul_of_nonneg_left hs (by positivity)
      have h0 : 0 ≤ (D.host.QS : ℝ) * ((D.host.q : ℝ) * D.host.d) := by positivity
      nlinarith
    have hc1 : 1 ≤ Formalism.MainNotions.szCond L := by linarith
    have h36 : Formalism.MainNotions.szCond L ≤ Formalism.MainNotions.szCond L ^ 36 := le_self_pow₀ hc1 (by norm_num)
    have h150 : Formalism.MainNotions.szCond L ^ 36 ≤ Formalism.MainNotions.szCond L ^ 36 * (D.R.t : ℝ) ^ 150 :=
      le_mul_of_one_le_right (by positivity) (one_le_pow₀ ht1)
    have hsb : Real.sqrt L.sc.b ≤ L.sc.b := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
    have hfin : D.host.rdE ≤ L.sc.b := hc.trans (h36.trans (h150.trans (hCond.trans hsb)))
    have := Real.log_le_log (by linarith) hfin
    rwa [show Real.log L.sc.b = L.sc.L by unfold Scale.b; exact Real.log_exp _] at this
  · intro i
    obtain ⟨Y, hY1, -, hY3, hY4⟩ := P.g_Y
    have hY0 : 0 < Y := lt_of_lt_of_le (by positivity) hY1
    have hg0 : (0 : ℝ) < D.host.g i := lt_of_lt_of_le hY0 (hY4 i).1
    have h1 := Real.log_le_log hg0 (hY4 i).2
    rw [Real.log_mul (by norm_num) hY0.ne'] at h1
    have h2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
    linarith
  · have h1 := hNodes.2.2.2.1
    have h2 : L.etaSz / D.R.m ≤ L.etaSz := div_le_self L.etaSz_pos.le hm1
    have h3 : (0 : ℝ) ≤ D.R.t := by linarith
    linarith
  · intro t
    have h1 := hBot t
    have hLa0 : 0 ≤ L.LaG := le_trans (Real.rpow_pos_of_pos hx0 _).le hLa.1
    have h2 : 0 ≤ L.sc.x ^ Formalism.MainNotions.szTh L * Real.log L.sc.x * L.LaG / D.R.k :=
      div_nonneg (mul_nonneg (mul_nonneg (Real.rpow_pos_of_pos hx0 _).le (Real.log_nonneg hx1.le)) hLa0) hk0.le
    have h3 : L.sc.x ^ (-2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1.le (by norm_num)
    have hb' : 0 ≤ L.sc.b' := by
      unfold Scale.b' Scale.a Scale.X' Scale.b
      positivity
    have hR : 4 * Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k +
        L.sc.x ^ Formalism.MainNotions.szTh L * Real.log L.sc.x * L.LaG / D.R.k ≤ L.sc.x ^ (-2 : ℝ) := hRho
    have h4 : Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k ≤ 1 := by
      have : 4 * Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k =
          4 * (Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) := by ring
      have h0 : 0 ≤ Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k := by
        unfold Formalism.MainNotions.szNst Scale.delta1
        have := Real.rpow_pos_of_pos hx0 (-(L.sc.eps / 8))
        have := Real.rpow_pos_of_pos hx0 L.sc.eps
        positivity
      linarith
    have h5 : Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k =
        Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k * L.sc.b' := by ring
    rw [h5] at h1
    nlinarith

end GlobalTheory.CoreHt.RowsOfDesign
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScaleLargeThree
open Formalism.BasicNotions

namespace GlobalTheory

theorem scale_large_three (eps : ℝ) (he : 0 < eps) : ∃ x0 : ℝ, ∀ s : Scale, s.eps = eps → x0 ≤ s.x →
    Real.log (4 * s.x) ≤ s.L ∧ 8 ≤ s.X' ∧ 2 ≤ s.x := by
  have h1 : ∀ᶠ x : ℝ in Filter.atTop, Real.log x ≤ (1/2) * x ^ eps := by
    have := (isLittleO_log_rpow_atTop he).bound (c := 1/2) (by norm_num)
    filter_upwards [this, Filter.eventually_gt_atTop 1] with x hx hx1
    have hl : 0 ≤ Real.log x := Real.log_nonneg hx1.le
    have hp : 0 ≤ x ^ eps := Real.rpow_nonneg (by linarith) _
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hl, abs_of_nonneg hp] at hx
    exact hx
  have h2 : ∀ᶠ x : ℝ in Filter.atTop, Real.log 4 ≤ (1/2) * x ^ eps := by
    have := (tendsto_rpow_atTop he).eventually_ge_atTop (2 * Real.log 4)
    filter_upwards [this] with x hx
    linarith
  have h3 : ∀ᶠ x : ℝ in Filter.atTop, (3 : ℝ) ≤ x ^ (eps / 3) :=
    (tendsto_rpow_atTop (by linarith : 0 < eps / 3)).eventually_ge_atTop 3
  obtain ⟨x0, hx0⟩ := Filter.eventually_atTop.1
    (h1.and (h2.and (h3.and (Filter.eventually_ge_atTop (2 : ℝ)))))
  refine ⟨x0, fun s hs hx => ?_⟩
  obtain ⟨a1, a2, a3, a4⟩ := hx0 s.x hx
  have hxpos : 0 < s.x := by linarith
  refine ⟨?_, ?_, a4⟩
  · show Real.log (4 * s.x) ≤ s.x ^ s.eps
    rw [Real.log_mul (by norm_num) hxpos.ne', hs]
    linarith
  · show 8 ≤ Real.exp (s.x ^ (s.eps / 3))
    rw [hs]
    have he1 : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ); linarith
    have h8 : (8 : ℝ) ≤ Real.exp 3 := by
      have : Real.exp 3 = Real.exp 1 ^ 3 := by
        rw [← Real.exp_nat_mul]; norm_num
      rw [this]
      nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) he1 3]
    exact h8.trans (Real.exp_le_exp.2 a3)

end GlobalTheory
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2 GlobalTheory.CoreHt
open GlobalTheory.ColumnNormCompare (numDatumOfParameters codeRec plRec)
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.CoreHt

theorem famRowsSizes : ∀ {eps : ℝ} (Fm : FamP eps), TuSize Fm → ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, GlobalTheory.CoreHt.DelNat (Fm.D x i) → GlobalTheory.CoreHt.HtRowsS (Fm.L x i) Fm.CYL ∧ 8 ≤ (Fm.L x i).sc.X' ∧ 2 ≤ (Fm.L x i).sc.x ∧ (∀ u, 4 * (Fm.L x i).sc.a < (((Fm.D x i).mem u).A.T : ℝ)) ∧ ∀ u, Real.log ((((Fm.D x i).mem u).A.T : ℕ) : ℝ) ≤ max Fm.CTu 0 * (Fm.D x i).R.m * (Fm.L x i).sc.L := by
  intro eps Fm hTu
  have he : 0 < eps := by
    obtain ⟨i⟩ := Fm.Ix_zero
    rw [← Fm.L_eps 0 i]; exact (Fm.L 0 i).sc.eps_pos
  obtain ⟨x1, hT⟩ := hTu
  obtain ⟨xL, hL⟩ := GlobalTheory.scale_large_three eps he
  obtain ⟨x3, h3⟩ := flipTwoThree.le_rpow_for_large_x ((2 : ℝ) / 5) (by norm_num) 4
  obtain ⟨x4, h4⟩ := flipTwoThree.pow_le_exp_rpow_for_large_x 2 eps he
  refine ⟨max (max (max x1 xL) x3) (max x4 (max 9 (Fm.x1 + 1))), fun x hx i hDel => ?_⟩
  have e1 : x1 ≤ x := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hx
  have eL : xL ≤ x := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hx
  have e3 : x3 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have e4 : x4 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have e9 : (9 : ℝ) ≤ x :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hx
  have e5 : Fm.x1 < x := by
    have := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hx
    linarith
  have hsx : (Fm.L x i).sc.x = x := Fm.L_x x i e5
  have hse : (Fm.L x i).sc.eps = eps := Fm.L_eps x i
  obtain ⟨hlog, h8, h2⟩ := hL (Fm.L x i).sc hse (by rw [hsx]; exact eL)
  have hThick : ThickUp (Fm.L x i) := fun j j1 j2 τ hc => ((Fm.L x i).win_thick j j1 j2 τ hc).2
  have hrows : HtRowsS (Fm.L x i) Fm.CYL := by
    have := GlobalTheory.CoreHt.RowsOfDesign.rows_of_design (Fm.D x i) (Fm.L x i) (Fm.params x e5 i) (Fm.sizes x e5 i) hlog hDel hThick
    rwa [Fm.params_CYL x e5 i] at this
  have hm : (4 : ℝ) ≤ (Fm.D x i).R.m := by
    have z1 := (flipTwoThree.size_bounds_of_scale (Fm.L x i) (Fm.sizes x e5 i) (by rw [hsx]; linarith)).1
    rw [hsx] at z1
    exact le_trans (h3 x e3) z1
  have hx0 : 0 < x := by linarith
  have hb1 : 1 ≤ (Fm.L x i).sc.b := by
    unfold Scale.b; exact Real.one_le_exp (Real.rpow_nonneg (by linarith [(Fm.L x i).sc.one_lt_alt]) _)
  have hb0 : 0 < (Fm.L x i).sc.b := by linarith
  have h8b : 8 * x < (Fm.L x i).sc.b := by
    have hx2 := h4 x e4
    have hbe : (Fm.L x i).sc.b = Real.exp (x ^ eps) := by
      unfold Scale.b Scale.L; rw [hsx, hse]
    rw [hbe]
    nlinarith
  have hb2 : (Fm.L x i).sc.b ^ (2 : ℝ) ≤ (Fm.L x i).sc.b ^ (((Fm.D x i).R.m : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hb1 (by linarith)
  rw [Real.rpow_two] at hb2
  have hL0 : 0 ≤ (Fm.L x i).sc.L := by
    unfold Scale.L; exact Real.rpow_nonneg (by linarith [(Fm.L x i).sc.one_lt_alt]) _
  have hm0 : (0 : ℝ) ≤ (Fm.D x i).R.m := by linarith
  refine ⟨hrows, h8, h2, fun u => ?_, fun u => ?_⟩
  · have hTge := (hT x e1 i).1 u
    have ha : (Fm.L x i).sc.a = x * (Fm.L x i).sc.b := by unfold Scale.a; rw [hsx]
    rw [ha]
    have : 8 * (x * (Fm.L x i).sc.b) < (Fm.L x i).sc.b ^ 2 := by
      rw [← mul_assoc, sq]; exact mul_lt_mul_of_pos_right h8b hb0
    have hxb : 0 < x * (Fm.L x i).sc.b := mul_pos hx0 hb0
    linarith
  · refine le_trans ((hT x e1 i).2 u) ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hm0) hL0

end GlobalTheory.CoreHt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TprodConstantPolynomialsNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TprodConstantPolynomialsNeZero
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

namespace GlobalTheory

theorem tprod_one_pol_ne_zero : ∀ (F : Type) [Field F] [NumberField F] (P Q R S : ℕ),
    (PiTensorProduct.tprod ℂ fun _ : InfinitePlace F => (1 : Formalism.BasicNotions.TH.Pol P Q R S)) ≠ 0 := by
  intro F _ _ P Q R S h
  let c : Formalism.BasicNotions.TH.Pol P Q R S →ₗ[ℂ] ℂ := (MvPolynomial.aeval (fun _ => (0:ℂ))).toLinearMap
  have key := congrArg (PiTensorProduct.lift
      ((MultilinearMap.mkPiAlgebra ℂ (InfinitePlace F) ℂ).compLinearMap (fun _ => c))) h
  simp [PiTensorProduct.lift.tprod, c] at key

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TprodConstantPolynomialsNeZeroStatement
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tprod_constant_polynomials_ne_zero : ∀ (F : Type) [Field F] [NumberField F] (P Q R S : ℕ),
    (PiTensorProduct.tprod ℂ fun _ : InfinitePlace F => (1 : Formalism.BasicNotions.TH.Pol P Q R S)) ≠ 0 := by
  first | exact @GlobalTheory.tprod_one_pol_ne_zero | exact GlobalTheory.tprod_one_pol_ne_zero | (intros; apply GlobalTheory.tprod_one_pol_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussAbsEqISup
set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open Polynomial (nthRootsFinset)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

namespace GlobalTheory.HSChoice.BaseChange

theorem gaussAbs_eq_iSup {K ι : Type} [Field K] [NumberField K] (v : FinitePlace K) (g : MvPolynomial ι K)
    (s : Finset (ι →₀ ℕ)) (hs : g.support ⊆ s) (hne : s.Nonempty) :
    ReciprocityTheory.MultiplicativeHeights.gaussAbs v g = ⨆ k : s, v (AddMonoidAlgebra.coeff g (k : ι →₀ ℕ)) := by
  classical
  have : Nonempty s := hne.to_subtype
  have hsup : (g.support.sup fun m => (v (AddMonoidAlgebra.coeff g m)).toNNReal) = s.sup fun m => (v (AddMonoidAlgebra.coeff g m)).toNNReal := by
    refine le_antisymm (Finset.sup_mono hs) (Finset.sup_le fun m hm => ?_)
    by_cases hm' : m ∈ g.support
    · exact Finset.le_sup (f := fun m => (v (AddMonoidAlgebra.coeff g m)).toNNReal) hm'
    · rw [MvPolynomial.notMem_support_iff.1 hm', map_zero, Real.toNNReal_zero]
      exact bot_le
  unfold ReciprocityTheory.MultiplicativeHeights.gaussAbs
  rw [hsup]
  obtain ⟨k, hk, hkeq⟩ := Finset.exists_mem_eq_sup s hne fun m => (v (AddMonoidAlgebra.coeff g m)).toNNReal
  rw [hkeq, Real.coe_toNNReal _ (apply_nonneg _ _)]
  refine le_antisymm (le_ciSup (f := fun k : s => v (AddMonoidAlgebra.coeff g (k : ι →₀ ℕ))) (Set.finite_range _).bddAbove ⟨k, hk⟩)
    (ciSup_le fun m => ?_)
  have h1 : (v (AddMonoidAlgebra.coeff g (m : ι →₀ ℕ))).toNNReal ≤ (v (AddMonoidAlgebra.coeff g k)).toNNReal := by
    rw [← hkeq]; exact Finset.le_sup (f := fun m => (v (AddMonoidAlgebra.coeff g m)).toNNReal) m.2
  have h2 := (Real.toNNReal_le_toNNReal_iff (apply_nonneg _ _)).1 h1
  exact h2

end GlobalTheory.HSChoice.BaseChange
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockAct2DiagonalOne
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

namespace GlobalTheory.VacuumWeight

theorem diagonal_eq_sum_Eab {r s : ℕ} (D : Ix r s → ℂ) :
    Matrix.diagonal D = ∑ c, D c • Eab c c := by
  ext i j
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, Eab, Matrix.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Matrix.diagonal_apply]
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg h]; symm
    exact Finset.sum_eq_zero fun c _ => if_neg fun hc => h (hc.1.symm.trans hc.2)

theorem sum_lineSign {p q r s : ℕ} (c : Ix r s) :
    ∑ a : Ix p q, lineSign a c = ((p : ℂ) - q) * Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1) c := by
  rcases c with c | c <;> simp [Fintype.sum_sum_type, lineSign] <;> ring

theorem fockAct2_diagonal_one (p q r s : ℕ) (D : Ix r s → ℂ) :
    fockAct2 p q r s (Matrix.diagonal D) (1 : Formalism.BasicNotions.TH.Pol p q r s) =
    ((((p : ℂ) - q) / 2) * ∑ c, D c * Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1) c) • (1 : Formalism.BasicNotions.TH.Pol p q r s) := by
  have h1 : (1 : Formalism.BasicNotions.TH.Pol p q r s) = MvPolynomial.monomial 0 1 := rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [diagonal_eq_sum_Eab, map_sum, LinearMap.sum_apply, Finset.mul_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_smul, LinearMap.smul_apply, h1, cartan2, smul_smul]
  congr 1
  simp only [Finsupp.coe_zero, Pi.zero_apply, Nat.cast_zero, zero_add]
  rw [← Finset.sum_mul, sum_lineSign]
  ring

end GlobalTheory.VacuumWeight
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AuxiliaryVectorUniformizerExponent
open MeasureTheory ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.OriginBox
open GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx

variable {k : Type*} [Field k]

def auxiliaryVectorUniformizerExponent (a a' : ℤ) (c : ℕ) {n : Type*} : n ⊕ Fin c → ℤ
  | .inl _ => 0
  | .inr p => a * ((c : ℤ) - p) - a' * ((p : ℤ) + 1)

def vtxExp (a a' : ℤ) (c t x : ℕ) : ℤ :=
  if t ≤ x then a * ((c : ℤ) - ((x - t : ℕ) : ℤ)) - a' * (((x - t : ℕ) : ℤ) + 1) else 0

variable (G : Grid k)

def colDiag (ϖ : kˣ) (a a' : ℤ) (j : ℕ) : GL (Fin (G.rank (G.m, j))) k :=
  diagGL fun x => ϖ ^ vtxExp a a' (G.m - 1 - j) (topRank G j) x

def boxExp (a a' : ℤ) (j : Fin (G.m - 1))
    (v : StepVar (Fin (topRank G ((j : ℕ) + 1))) (G.m - 2 - j) (Fin (topRank G j))) : ℤ :=
  a - auxiliaryVectorUniformizerExponent a a' (G.m - 2 - j + 1) v.1.2 + auxiliaryVectorUniformizerExponent a a' (G.m - 2 - j) v.1.1

variable [ValuativeRel k]

def box (ϖ : kˣ) (a a' : ℤ) : Set (Vars G) :=
  Set.univ.pi fun j => Set.univ.pi fun v => {x : k | valuation k x ≤ valuation k ((ϖ ^ boxExp G a a' j v : kˣ) : k)}

variable {G}


omit [ValuativeRel k] in
theorem vtxExp_frame (a a' : ℤ) {t c b : ℕ} (h : t + c = b) (y : Fin t ⊕ Fin c) :
    vtxExp a a' c t (frame h y) = auxiliaryVectorUniformizerExponent a a' c y := by
  rcases y with x | p
  · simp [vtxExp, auxiliaryVectorUniformizerExponent, frame, finSumFinEquiv_apply_left, x.2]
  · simp [vtxExp, auxiliaryVectorUniformizerExponent, frame, finSumFinEquiv_apply_right]

end GlobalTheory.OriginBox
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeCoordinateRatioBoundedStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeCoordinateRatioBounded
namespace GlobalTheory

theorem cone_ratio_bounded (a : ℕ) (t : ℝ) (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : Fin a → ℝ, (∀ i, 0 < r i) →
      (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) →
      ∀ p q : Fin a, p ≤ q → r q / r p ≤ C := by
  have hM : (1 : ℝ) ≤ max 1 t⁻¹ := le_max_left _ _
  have hM0 : (0 : ℝ) ≤ max 1 t⁻¹ := le_trans zero_le_one hM
  refine ⟨(max 1 t⁻¹) ^ a, pow_nonneg hM0 _, fun r hr hstep p q hpq => ?_⟩
  have key : ∀ (n : ℕ) (h : (p : ℕ) + n < a), r ⟨p + n, h⟩ ≤ (max 1 t⁻¹) ^ n * r p := by
    intro n
    induction n with
    | zero => intro h; simp
    | succ n ih =>
      intro h
      have h' : (p : ℕ) + n < a := by omega
      have h1 := hstep ⟨p + n, h'⟩ ⟨p + (n + 1), h⟩ (by simp [add_assoc])
      have h2 : r ⟨p + (n + 1), h⟩ ≤ t⁻¹ * r ⟨p + n, h'⟩ := by
        rw [inv_mul_eq_div, le_div_iff₀ ht, mul_comm]; exact h1
      calc r ⟨p + (n + 1), h⟩ ≤ t⁻¹ * r ⟨p + n, h'⟩ := h2
        _ ≤ max 1 t⁻¹ * r ⟨p + n, h'⟩ :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (hr _).le
        _ ≤ max 1 t⁻¹ * ((max 1 t⁻¹) ^ n * r p) := mul_le_mul_of_nonneg_left (ih h') hM0
        _ = (max 1 t⁻¹) ^ (n + 1) * r p := by ring
  have hpq' : (p : ℕ) ≤ q := hpq
  have hlt : (p : ℕ) + (q - p) < a := by have := q.2; omega
  have hq : (⟨p + (q - p), hlt⟩ : Fin a) = q := Fin.ext (by simp only; omega)
  have h3 := key (q - p) hlt
  rw [hq] at h3
  rw [div_le_iff₀ (hr p)]
  refine h3.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hM ?_) (hr p).le)
  have := q.2; omega

end GlobalTheory
end

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cone_coordinate_ratio_bounded : ∀ (a : ℕ) (t : ℝ), 0 < t → ∃ C : ℝ, 0 ≤ C ∧ ∀ r : Fin a → ℝ, (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → ∀ p q : Fin a, p ≤ q → r q / r p ≤ C := by
  first | exact @GlobalTheory.cone_ratio_bounded | exact GlobalTheory.cone_ratio_bounded | (intros; apply GlobalTheory.cone_ratio_bounded <;> assumption)
end
