module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NatCastMemPlaceAt
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeValueIntegrality
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSupportedAtSplitPlaceUnitaryMatrixEq

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCDVRFractionFieldReadingInCpFiniteExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCDVRFractionFieldReadingInCpFiniteExtension
open NumberField IsDedekindDomain Formalism.L2.Pj GlobalTheory.GeoTie GlobalTheory.GoodPts

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GeoTie.ReadExt

section Val

open Classical

variable {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
  [IsFractionRing V K]

theorem vV_unit' (u : Vˣ) : vV V (algebraMap V K u) = 0 := by
  have : valV V (algebraMap V K u) = 1 := by
    rw [valV, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    exact fun h => (IsLocalRing.mem_maximalIdeal _).1 h u.isUnit
  simp [vV, this]

theorem vV_irr' {a : V} (ha : Irreducible a) : vV V (algebraMap V K a) = 1 := by
  have : valV V (algebraMap V K a) = WithZero.exp (-1 : ℤ) := by
    rw [valV, HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_singleton _ ha.ne_zero ha.maximalIdeal_eq
  simp [vV, this]

theorem vV_pow' {x : K} (n : ℕ) : vV V (x ^ n) = n * vV V x := by
  simp [vV]


variable (V K) in
def absOfVal (c : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1) : AbsoluteValue K ℝ where
  toFun x := if x = 0 then 0 else c ^ (vV V x)
  map_mul' x y := by
    by_cases hx : x = 0
    · simp [hx]
    by_cases hy : y = 0
    · simp [hy]
    simp [hx, hy, vV_mul hx hy, zpow_add₀ hc0.ne']
  nonneg' x := by
    show 0 ≤ (if x = 0 then 0 else c ^ (vV V x))
    split_ifs
    · exact le_rfl
    · positivity
  eq_zero' x := by
    show (if x = 0 then 0 else c ^ (vV V x)) = 0 ↔ x = 0
    split_ifs with h
    · simp [h]
    · simp [h, zpow_ne_zero _ hc0.ne']
  add_le' x y := by
    show (if x + y = 0 then 0 else c ^ (vV V (x + y))) ≤
      (if x = 0 then 0 else c ^ (vV V x)) + (if y = 0 then 0 else c ^ (vV V y))
    by_cases hx : x = 0
    · subst hx; simp
    by_cases hy : y = 0
    · subst hy; simp
    have px := zpow_pos hc0 (vV V x)
    have py := zpow_pos hc0 (vV V y)
    by_cases hxy : x + y = 0
    · simp only [hxy, hx, hy, if_true, if_false]; positivity
    simp only [hxy, hx, hy, if_false]
    rcases min_le_iff.1 (min_le_vV_add (V := V) hx hy hxy) with h | h
    · have := zpow_le_zpow_right_of_le_one₀ hc0 hc1 h
      linarith
    · have := zpow_le_zpow_right_of_le_one₀ hc0 hc1 h
      linarith

theorem absOfVal_of_ne (c : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1) {x : K} (hx : x ≠ 0) :
    absOfVal V K c hc0 hc1 x = c ^ (vV V x) := by
  show (if x = 0 then 0 else c ^ (vV V x)) = _
  simp [hx]

end Val

theorem norm_eq_zpow (T : CDVR) {C : Type} [NormedField C] (k : T.Fr →+* C)
    (hball : ∀ x, ‖k x‖ ≤ 1 ↔ InV T x) {π : T.V} (hπ : Irreducible π) (x : T.Fr) (hx : x ≠ 0) :
    ‖k x‖ = ‖k (algebraMap T.V T.Fr π)‖ ^ vV T.V x := by
  have hu : ∀ u : T.Vˣ, ‖k (algebraMap T.V T.Fr u)‖ = 1 := by
    intro u
    have h1 := (hball (algebraMap T.V T.Fr u)).2 ⟨u, rfl⟩
    have h2 := (hball (algebraMap T.V T.Fr (u⁻¹ : T.Vˣ))).2 ⟨_, rfl⟩
    have h3 : ‖k (algebraMap T.V T.Fr u)‖ * ‖k (algebraMap T.V T.Fr (u⁻¹ : T.Vˣ))‖ = 1 := by
      rw [← norm_mul, ← map_mul, ← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one, map_one,
        norm_one]
    nlinarith [norm_nonneg (k (algebraMap T.V T.Fr u)), norm_nonneg (k (algebraMap T.V T.Fr (u⁻¹ : T.Vˣ)))]
  have hπ0 : algebraMap T.V T.Fr π ≠ 0 := by
    simpa using hπ.ne_zero
  have hρ0 : ‖k (algebraMap T.V T.Fr π)‖ ≠ 0 := by
    simpa using hπ0
  have key : ∀ a : T.V, a ≠ 0 →
      ‖k (algebraMap T.V T.Fr a)‖ = ‖k (algebraMap T.V T.Fr π)‖ ^ vV T.V (algebraMap T.V T.Fr a) := by
    intro a ha
    obtain ⟨s, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
    have hu0 : algebraMap T.V T.Fr u ≠ 0 := by simp
    rw [map_mul, map_pow, vV_mul hu0 (pow_ne_zero _ hπ0), vV_pow', vV_unit', vV_irr' hπ, map_mul, norm_mul, hu,
      map_pow, norm_pow]
    simp
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := T.V) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hb1 : algebraMap T.V T.Fr b ≠ 0 := by simpa using hb0
  have ha0 : a ≠ 0 := by rintro rfl; simp at hx
  have hv := vV_mul (V := T.V) hx hb1
  rw [div_mul_cancel₀ _ hb1] at hv
  rw [map_div₀, norm_div, key a ha0, key b hb0, ← zpow_sub₀ hρ0, hv]
  congr 1
  ring

theorem isReading_ext : ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F] (φ : F →+* ℂ_[p]) (T : CDVR)
    (io : F →+* T.Fr) (k : T.Fr →+* ℂ_[p]), IsReading φ T io k → ∀ (T' : CDVR) (i : T.Fr →+* T'.Fr),
    GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.IsFinExt T T' i → ∀ j : T'.Fr →+* ℂ_[p], j.comp i = k → IsReading φ T' (i.comp io) j := by
  intro p _ F _ _ φ T io k hk T' i hi j hj
  have hji : ∀ y, j (i y) = k y := fun y => by rw [← hj]; rfl
  refine ⟨fun a => by rw [RingHom.comp_apply, hji]; exact hk.comp a, fun x => ?_⟩
  obtain ⟨hfin, r, hr, hv⟩ := hi
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible T.V
  have hπ0 : algebraMap T.V T.Fr π ≠ 0 := by simpa using hπ.ne_zero
  set ρ := ‖k (algebraMap T.V T.Fr π)‖ with hρ
  have hρ0 : 0 < ρ := norm_pos_iff.2 ((map_ne_zero k).2 hπ0)
  have hρ1 : ρ < 1 := by
    by_contra hc
    push_neg at hc
    have h1 : ‖k (algebraMap T.V T.Fr π)⁻¹‖ ≤ 1 := by
      rw [map_inv₀, norm_inv]
      exact inv_le_one_of_one_le₀ hc
    obtain ⟨v, hv'⟩ := (hk.int _).1 h1
    apply hπ.not_isUnit
    refine IsUnit.of_mul_eq_one v ?_
    apply IsFractionRing.injective T.V T.Fr
    rw [map_mul, hv', map_one, mul_inv_cancel₀ hπ0]
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  set c : ℝ := ρ ^ ((1 : ℝ) / r) with hc
  have hc0 : 0 < c := Real.rpow_pos_of_pos hρ0 _
  have hc1 : c < 1 := Real.rpow_lt_one hρ0.le hρ1 (by positivity)
  have hcr : c ^ r = ρ := by
    rw [hc, ← Real.rpow_natCast, ← Real.rpow_mul hρ0.le, one_div, inv_mul_cancel₀ hr0.ne', Real.rpow_one]
  letI NF : NontriviallyNormedField T.Fr :=
    { NormedField.induced T.Fr ℂ_[p] k k.injective with
      non_trivial := ⟨(algebraMap T.V T.Fr π)⁻¹, by
        show 1 < ‖k (algebraMap T.V T.Fr π)⁻¹‖
        rw [map_inv₀, norm_inv]
        exact (one_lt_inv₀ hρ0).2 hρ1⟩ }
  have hnk : ∀ y : T.Fr, ‖y‖ = ‖k y‖ := fun y => rfl
  haveI : IsUltrametricDist T.Fr :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y => by
      rw [hnk, hnk, hnk, map_add (f := _)]
      exact IsUltrametricDist.norm_add_le_max _ _
  haveI : CompleteSpace T.Fr := Formalism.MainNotions.ExistsIdealDenominator.complete_of_adic (O := T.V) (K := T.Fr) (fun y => hk.int y) inferInstance
  letI := i.toAlgebra
  haveI : FiniteDimensional T.Fr T'.Fr := hfin
  have e1 := spectralNorm_unique_field_norm_ext (K := T.Fr) (L := T'.Fr)
    (f := (NormedField.toAbsoluteValue ℂ_[p]).comp j.injective) (fun y => by
      show ‖j (i y)‖ = ‖y‖
      rw [hji, hnk]) x
  have e2 := spectralNorm_unique_field_norm_ext (K := T.Fr) (L := T'.Fr)
    (f := absOfVal T'.V T'.Fr c hc0 hc1.le) (fun y => by
      show absOfVal T'.V T'.Fr c hc0 hc1.le (i y) = ‖y‖
      by_cases hy : y = 0
      · subst hy; simp
      rw [absOfVal_of_ne _ _ _ ((map_ne_zero i).2 hy), hv, zpow_mul, zpow_natCast, hcr, hnk,
        norm_eq_zpow T k hk.int hπ y hy]) x
  have hx : ‖j x‖ = absOfVal T'.V T'.Fr c hc0 hc1.le x := e1.trans e2.symm
  rw [hx]
  by_cases hx0 : x = 0
  · subst hx0
    simp only [map_zero, zero_le_one, true_iff]
    exact ⟨0, map_zero _⟩
  rw [absOfVal_of_ne _ _ _ hx0]
  change _ ↔ ∃ a : T'.V, algebraMap T'.V T'.Fr a = x
  rw [GlobalTheory.CompleteValExt.exists_algebraMap_eq_iff]
  constructor
  · intro h
    by_contra hn
    push_neg at hn
    have := one_lt_zpow_of_neg₀ hc0 hc1 hn
    linarith
  · intro h
    exact zpow_le_one₀ hc0 hc1.le h

end GlobalTheory.GeoTie.ReadExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCDVRFractionFieldReadingInCpFiniteExtensionStatement
open NumberField IsDedekindDomain Formalism.L2.Pj GlobalTheory.GeoTie GlobalTheory.GoodPts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCDVRFractionFieldReadingInCp_finite_extension : ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F] (φ : F →+* ℂ_[p]) (T : CDVR) (io : F →+* T.Fr) (k : T.Fr →+* ℂ_[p]), IsReading φ T io k → ∀ (T' : CDVR) (i : T.Fr →+* T'.Fr), GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.IsFinExt T T' i → ∀ j : T'.Fr →+* ℂ_[p], j.comp i = k → IsReading φ T' (i.comp io) j := by
  first | exact @GlobalTheory.GeoTie.ReadExt.isReading_ext | exact GlobalTheory.GeoTie.ReadExt.isReading_ext | (intros; apply GlobalTheory.GeoTie.ReadExt.isReading_ext <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableLevelDecomposition
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.Published

noncomputable section

namespace GlobalTheory.LevelTypeProj

theorem span_eval_eq_top {X M : Type*} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    (ev : X → Module.Dual ℂ M) (hev : ∀ v, (∀ x, ev x v = 0) → v = 0) :
    Submodule.span ℂ (Set.range ev) = ⊤ := by
  have hbot : (Submodule.span ℂ (Set.range ev)).dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_dualCoannihilator] at hv
    exact (Submodule.mem_bot ℂ).2 (hev v fun x => hv (ev x) (Submodule.subset_span ⟨x, rfl⟩))
  rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span ℂ (Set.range ev)), hbot,
    Submodule.dualAnnihilator_bot]

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}

theorem finRep_cptRep (l : GL (Fin N) (Af E)) (k : Kinf E N) (φ : Sm E N) :
    finRep E N l (cptRep E N k φ) = cptRep E N k (finRep E N l φ) := by
  simp only [finRep, cptRep, MonoidHom.comp_apply]
  rw [← Module.End.mul_apply, ← map_mul, ← infGL_comm, map_mul, Module.End.mul_apply]

def orbitSpan (L : Subgroup (GL (Fin N) (Af E))) (ψ : Sm E N) : Submodule ℂ (Sm E N) :=
  Submodule.span ℂ {v | ∃ l ∈ L, ∃ k, v = finRep E N l (cptRep E N k ψ)}

theorem mem_orbitSpan_self (L : Subgroup (GL (Fin N) (Af E))) (ψ : Sm E N) : ψ ∈ orbitSpan L ψ :=
  Submodule.subset_span ⟨1, L.one_mem, 1, by rw [map_one, map_one, Module.End.one_apply, Module.End.one_apply]⟩

theorem orbitSpan_le {J : Submodule ℂ (Sm E N)} (hJ : _root_.GlobalTheory.CuspRep.IsStable J) (L : Subgroup (GL (Fin N) (Af E)))
    {ψ : Sm E N} (hψ : ψ ∈ J) : orbitSpan L ψ ≤ J :=
  Submodule.span_le.2 (by rintro _ ⟨l, -, k, rfl⟩; exact hJ (.fin l) _ (hJ (.cpt k) _ hψ))

theorem finRep_mem_orbitSpan {L : Subgroup (GL (Fin N) (Af E))} {ψ : Sm E N} {l' : GL (Fin N) (Af E)}
    (hl' : l' ∈ L) {v : Sm E N} (hv : v ∈ orbitSpan L ψ) : finRep E N l' v ∈ orbitSpan L ψ := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, k, rfl⟩ := hx
    apply Submodule.subset_span
    refine ⟨l' * l, L.mul_mem hl' hl, k, ?_⟩
    rw [map_mul (finRep E N), Module.End.mul_apply]
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem cptRep_mem_orbitSpan {L : Subgroup (GL (Fin N) (Af E))} {ψ : Sm E N} (k' : Kinf E N)
    {v : Sm E N} (hv : v ∈ orbitSpan L ψ) : cptRep E N k' v ∈ orbitSpan L ψ := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, k, rfl⟩ := hx
    apply Submodule.subset_span
    refine ⟨l, hl, k' * k, ?_⟩
    rw [map_mul (cptRep E N), Module.End.mul_apply, finRep_cptRep l k' (cptRep E N k ψ)]
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem orbitSpan_finiteDimensional (L : Subgroup (GL (Fin N) (Af E))) (hL : IsCompact (L : Set (GL (Fin N) (Af E))))
    (ψ : Sm E N) (hψ : IsAutForm ψ) : FiniteDimensional ℂ (orbitSpan L ψ) := by
  classical
  obtain ⟨t, ht⟩ := hL.elim_finite_subcover (fun l : GL (Fin N) (Af E) => {m | finRep E N (l⁻¹ * m) ψ = ψ})
    (fun l => hψ.level.preimage (continuous_const_mul l⁻¹))
    (fun m _ => Set.mem_iUnion.2 ⟨m, by simp only [Set.mem_setOf_eq, inv_mul_cancel, map_one]; rfl⟩)
  have := hψ.kfin
  refine Submodule.finiteDimensional_of_le
    (S₂ := t.sup fun l => (Submodule.span ℂ (Set.range fun k => cptRep E N k ψ)).map (finRep E N l))
    (Submodule.span_le.2 ?_)
  rintro _ ⟨m, hm, k, rfl⟩
  obtain ⟨l, hl, hlm⟩ := Set.mem_iUnion₂.1 (ht hm)
  have e : finRep E N m ψ = finRep E N l ψ := by
    calc finRep E N m ψ = finRep E N l (finRep E N (l⁻¹ * m) ψ) := by
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
      _ = finRep E N l ψ := by rw [show finRep E N (l⁻¹ * m) ψ = ψ from hlm]
  refine Finset.le_sup (f := fun l => (Submodule.span ℂ (Set.range fun k => cptRep E N k ψ)).map (finRep E N l)) hl ?_
  refine ⟨cptRep E N k ψ, Submodule.subset_span ⟨k, rfl⟩, ?_⟩
  change finRep E N l (cptRep E N k ψ) = finRep E N m (cptRep E N k ψ)
  rw [finRep_cptRep, finRep_cptRep, e]

def typePart (L : Subgroup (GL (Fin N) (Af E))) {U : Type} [AddCommGroup U] [Module ℂ U]
    (ρ : Representation ℂ (Kinf E N) U) : Submodule ℂ (Sm E N) where
  carrier := {φ | (∀ k ∈ L, finRep E N k φ = φ) ∧
    ∀ g : GA E N, (fun k : Kinf E N => (cptRep E N k φ).1 g) ∈ AutFin.coeffSpan ρ}
  add_mem' := fun hx hy => ⟨fun k hk => by rw [map_add (f := _), hx.1 k hk, hy.1 k hk],
    fun g => add_mem (hx.2 g) (hy.2 g)⟩
  zero_mem' := ⟨fun _ _ => map_zero _, fun _ => by
    simp only [map_zero, ZeroMemClass.coe_zero, Pi.zero_apply]
    exact zero_mem _⟩
  smul_mem' := fun c _ hx => ⟨fun k hk => by rw [map_smul, hx.1 k hk],
    fun g => Submodule.smul_mem _ c (hx.2 g)⟩

theorem exists_proj {μ : Measure (GA E N)} [μ.IsHaarMeasure] {W : Submodule ℂ (Sm E N)}
    (h : ∀ φ ∈ W, MemL2Quotient (latticeGL E N) μ φ.1) (hF : Function.Injective (toL2ₗ μ W h))
    (S : Submodule ℂ (Sm E N)) (hSW : S ≤ W) [FiniteDimensional ℂ S] :
    ∃ p : W →ₗ[ℂ] W, (∀ x, (p x).1 ∈ S) ∧
      ∀ x y : W, y.1 ∈ S → inner ℂ (toL2ₗ μ W h x - toL2ₗ μ W h (p x)) (toL2ₗ μ W h y) = 0 := by
  haveI : FiniteDimensional ℂ (S.comap W.subtype) :=
    (Submodule.comapSubtypeEquivOfLe hSW).symm.finiteDimensional
  let e := Submodule.equivMapOfInjective (toL2ₗ μ W h) hF (S.comap W.subtype)
  haveI : FiniteDimensional ℂ ((S.comap W.subtype).map (toL2ₗ μ W h)) := e.finiteDimensional
  have e1 : ∀ z, toL2ₗ μ W h ((e.symm z : S.comap W.subtype) : W) = (z : L2 (latticeGL E N) μ) := fun z => by
    have := Submodule.coe_equivMapOfInjective_apply (toL2ₗ μ W h) hF (S.comap W.subtype) (e.symm z)
    rw [LinearEquiv.apply_symm_apply] at this
    exact this.symm
  refine ⟨(S.comap W.subtype).subtype ∘ₗ e.symm.toLinearMap ∘ₗ
    ((S.comap W.subtype).map (toL2ₗ μ W h)).orthogonalProjectionOnto.toLinearMap ∘ₗ toL2ₗ μ W h,
    fun x => (e.symm _).2, fun x y hy => ?_⟩
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.subtype_apply, ContinuousLinearMap.coe_coe]
  rw [e1]
  exact Submodule.starProjection_inner_eq_zero _ _ ⟨y, hy, rfl⟩

theorem proj_unique {μ : Measure (GA E N)} [μ.IsHaarMeasure] {W : Submodule ℂ (Sm E N)}
    (h : ∀ φ ∈ W, MemL2Quotient (latticeGL E N) μ φ.1) (hF : Function.Injective (toL2ₗ μ W h))
    {S : Submodule ℂ (Sm E N)} {x a b : W} (ha : a.1 ∈ S) (hb : b.1 ∈ S)
    (hxa : ∀ y : W, y.1 ∈ S → inner ℂ (toL2ₗ μ W h x - toL2ₗ μ W h a) (toL2ₗ μ W h y) = 0)
    (hxb : ∀ y : W, y.1 ∈ S → inner ℂ (toL2ₗ μ W h x - toL2ₗ μ W h b) (toL2ₗ μ W h y) = 0) : a = b := by
  have hm : (b - a).1 ∈ S := S.sub_mem hb ha
  have key : toL2ₗ μ W h (b - a) = (toL2ₗ μ W h x - toL2ₗ μ W h a) - (toL2ₗ μ W h x - toL2ₗ μ W h b) := by
    rw [map_sub]; abel
  have h0 : inner ℂ (toL2ₗ μ W h (b - a)) (toL2ₗ μ W h (b - a)) = 0 := by
    calc inner ℂ (toL2ₗ μ W h (b - a)) (toL2ₗ μ W h (b - a))
        = inner ℂ ((toL2ₗ μ W h x - toL2ₗ μ W h a) - (toL2ₗ μ W h x - toL2ₗ μ W h b)) (toL2ₗ μ W h (b - a)) := by
          rw [← key]
      _ = 0 := by rw [inner_sub_left, hxa _ hm, hxb _ hm, sub_zero]
  exact (sub_eq_zero.1 (hF ((inner_self_eq_zero.1 h0).trans (map_zero _).symm))).symm

theorem proj_rt {μ : Measure (GA E N)} [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {W : Submodule ℂ (Sm E N)}
    (h : ∀ φ ∈ W, MemL2Quotient (latticeGL E N) μ φ.1) (hF : Function.Injective (toL2ₗ μ W h))
    {S : Submodule ℂ (Sm E N)} (hSW : S ≤ W) (p : W →ₗ[ℂ] W) (hpS : ∀ x, (p x).1 ∈ S)
    (hp : ∀ x y : W, y.1 ∈ S → inner ℂ (toL2ₗ μ W h x - toL2ₗ μ W h (p x)) (toL2ₗ μ W h y) = 0)
    (g : GA E N) (hgW : ∀ x ∈ W, rt E N g x ∈ W) (hgS : ∀ x ∈ S, rt E N g x ∈ S)
    (hgS' : ∀ x ∈ S, rt E N g⁻¹ x ∈ S) (x : W) :
    p ⟨rt E N g x.1, hgW _ x.2⟩ = ⟨rt E N g (p x).1, hgW _ (p x).2⟩ := by
  refine proj_unique h hF (hpS _) (hgS _ (hpS x)) (hp _) fun y hy => ?_
  have hy' : rt E N g⁻¹ y.1 ∈ W := hSW (hgS' _ hy)
  have ey : y = ⟨rt E N g (rt E N g⁻¹ y.1), hgW _ hy'⟩ := Subtype.ext (by
    show y.1 = rt E N g (rt E N g⁻¹ y.1)
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply])
  rw [ey, ← R_toL2ₗ h x (hgW _ x.2), ← R_toL2ₗ h (p x) (hgW _ (p x).2), ← R_toL2ₗ h ⟨_, hy'⟩ (hgW _ hy'),
    ← map_sub]
  let Ui : L2 (latticeGL E N) μ →ₗᵢ[ℂ] L2 (latticeGL E N) μ := ⟨(R (latticeGL E N) μ g).toLinearMap, norm_R g⟩
  change inner ℂ (Ui _) (Ui _) = 0
  rw [Ui.inner_map_map]
  exact hp x ⟨_, hy'⟩ (hgS' _ hy)

theorem exists_levelType_part : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ) (μ : Measure (GA E N)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (W J : Submodule ℂ (Sm E N)) (h : ∀ φ ∈ W, MemL2Quotient (latticeGL E N) μ φ.1), _root_.GlobalTheory.CuspRep.IsStable W → (∀ φ ∈ W, IsAutForm φ) → _root_.GlobalTheory.CuspRep.IsStable J → J ≤ W → ∀ (L : Subgroup (GL (Fin N) (Af E))), IsOpen (L : Set (GL (Fin N) (Af E))) → IsCompact (L : Set (GL (Fin N) (Af E))) → ∀ (U : Type) [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U] (ρ : Representation ℂ (Kinf E N) U), AutFin.IsContRep ρ → ∀ ψ : W, ψ.1 ∈ J → ∃ ψ' : W, ψ'.1 ∈ J ∧ (∀ k ∈ L, finRep E N k ψ'.1 = ψ'.1) ∧ (∀ g : GA E N, (fun k : Kinf E N => (cptRep E N k ψ'.1).1 g) ∈ AutFin.coeffSpan ρ) ∧ ∀ φ : W, (∀ k ∈ L, finRep E N k φ.1 = φ.1) → (∀ g : GA E N, (fun k : Kinf E N => (cptRep E N k φ.1).1 g) ∈ AutFin.coeffSpan ρ) → inner ℂ (toL2ₗ μ W h φ) (toL2ₗ μ W h ψ) = inner ℂ (toL2ₗ μ W h φ) (toL2ₗ μ W h ψ') := by
  intro E _ _ _ N μ _ _ W J h hW hA hJ hJW L _ hLc U _ _ _ ρ _ ψ hψ
  have hF := toL2ₗ_injective h fun φ hφ => ContAut.continuous_of_isOpen_stab E N φ (hA φ hφ).level
  have hSJ : orbitSpan L ψ.1 ≤ J := orbitSpan_le hJ L hψ
  have hSW := hSJ.trans hJW
  haveI := orbitSpan_finiteDimensional L hLc ψ.1 (hA _ ψ.2)
  haveI : FiniteDimensional ℂ (orbitSpan L ψ.1 ⊓ typePart L ρ : Submodule ℂ (Sm E N)) :=
    Submodule.finiteDimensional_of_le inf_le_left
  obtain ⟨p, hpS, hp⟩ := exists_proj h hF (orbitSpan L ψ.1) hSW
  obtain ⟨q, hqQ, hq⟩ := exists_proj h hF (orbitSpan L ψ.1 ⊓ typePart L ρ) (inf_le_left.trans hSW)
  refine ⟨q ψ, hSJ (hqQ ψ).1, (hqQ ψ).2.1, (hqQ ψ).2.2, fun φ hφL hφK => ?_⟩
  have hpT : (p φ).1 ∈ typePart L ρ := by
    refine ⟨fun k hk => ?_, fun g => ?_⟩
    · have hc := proj_rt h hF hSW p hpS hp (finGL E N k) (fun x hx => hW (.fin k) x hx)
        (fun x hx => finRep_mem_orbitSpan hk hx)
        (fun x hx => by rw [← map_inv]; exact finRep_mem_orbitSpan (L.inv_mem hk) hx) φ
      exact (congrArg Subtype.val hc).symm.trans (congrArg (fun x => (p x).1) (Subtype.ext (hφL k hk)))
    · have hcomm : ∀ k : Kinf E N, cptRep E N k (p φ).1 = (p ⟨cptRep E N k φ.1, hW (.cpt k) _ φ.2⟩).1 := fun k =>
        (congrArg Subtype.val (proj_rt h hF hSW p hpS hp (infGL E N (Unitary.toUnits k))
          (fun x hx => hW (.cpt k) x hx) (fun x hx => cptRep_mem_orbitSpan k hx)
          (fun x hx => by rw [← map_inv, ← map_inv]; exact cptRep_mem_orbitSpan k⁻¹ hx) φ)).symm
      have := (hA φ φ.2).kfin
      have hVW : Submodule.span ℂ (Set.range fun k => cptRep E N k φ.1) ≤ W :=
        Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact hW (.cpt k) _ φ.2)
      let V := Submodule.span ℂ (Set.range fun k => cptRep E N k φ.1)
      let Λ : Module.Dual ℂ V →ₗ[ℂ] (Kinf E N → ℂ) :=
        { toFun := fun ℓ k => ℓ ⟨cptRep E N k φ.1, Submodule.subset_span ⟨k, rfl⟩⟩
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      let ev : GA E N → Module.Dual ℂ V := fun x => (LinearMap.proj x).comp ((Sm E N).subtype.comp V.subtype)
      have htop := span_eval_eq_top ev fun v hv => Subtype.ext (Subtype.ext (funext hv))
      have hle : Submodule.span ℂ (Set.range ev) ≤ (AutFin.coeffSpan ρ).comap Λ :=
        Submodule.span_le.2 (by rintro _ ⟨x, rfl⟩; exact hφK x)
      let ℓ : Module.Dual ℂ V :=
        (LinearMap.proj g).comp ((Sm E N).subtype.comp (W.subtype.comp (p.comp (Submodule.inclusion hVW))))
      have hℓ : Λ ℓ ∈ AutFin.coeffSpan ρ := hle (htop ▸ Submodule.mem_top)
      convert hℓ using 1
      funext k
      rw [hcomm k]
      rfl
  have hψS : ψ.1 ∈ orbitSpan L ψ.1 := mem_orbitSpan_self L ψ.1
  have hr : (ψ - q ψ).1 ∈ orbitSpan L ψ.1 := (orbitSpan L ψ.1).sub_mem hψS (hqQ ψ).1
  have h1 : inner ℂ (toL2ₗ μ W h φ) (toL2ₗ μ W h (ψ - q ψ)) =
      inner ℂ (toL2ₗ μ W h (p φ)) (toL2ₗ μ W h (ψ - q ψ)) := by
    have := hp φ (ψ - q ψ) hr
    rwa [inner_sub_left, sub_eq_zero] at this
  have h2 : inner ℂ (toL2ₗ μ W h (p φ)) (toL2ₗ μ W h (ψ - q ψ)) = 0 := by
    have := hq ψ (p φ) ⟨hpS φ, hpT⟩
    rw [map_sub, ← inner_conj_symm, this, map_zero]
  rw [← sub_eq_zero, ← inner_sub_right, ← map_sub, h1, h2]

end GlobalTheory.LevelTypeProj

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchwartzBruhatConjHalfLocallyConstantCompactSupp
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchwartzBruhatConjHalfLocallyConstantCompactSupp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef

noncomputable section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.DownLift.SplitCoef

variable {D : D7}

theorem isHalf_sub' {m n : ℕ} {e : AE D} {u v : Mx D m n} (hu : IsHalf e u) (hv : IsHalf e v) : IsHalf e (u - v) :=
  fun i j => by rw [Matrix.sub_apply, mul_sub, hu i j, hv i j]

theorem isHalf_nsmul'' {m n : ℕ} {e : AE D} {u : Mx D m n} (hu : IsHalf e u) (k : ℕ) : IsHalf e (k • u) :=
  fun i j => by rw [Matrix.smul_apply, mul_smul_comm, hu i j]

theorem frMapAdj_nsmul (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D))
    (n : ℕ) (x : WO S T) : frMapAdj S T βS βT (n • x) = n • frMapAdj S T βS βT x :=
  (AddMonoidHom.mk' (frMapAdj S T βS βT) (GlobalTheory.PlaceVec.frMapAdj_add S T βS βT)).map_nsmul n x

theorem rdAdj_add (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D))
    {v : HeightOneSpectrum (𝓞 D.host.F)} (φ : Formalism.IndefR.Lev.EAf D →+* Fv D.host.F v) (x y : WO S T) :
    rdAdj S T βS βT φ (x + y) = rdAdj S T βS βT φ x + rdAdj S T βS βT φ y := by
  ext i j
  simp only [rdAdj, GlobalTheory.PlaceVec.frMapAdj_add, Matrix.map_apply, Matrix.add_apply, map_add (f := _)]

theorem rdAdj_nsmul (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D))
    {v : HeightOneSpectrum (𝓞 D.host.F)} (φ : Formalism.IndefR.Lev.EAf D →+* Fv D.host.F v) (n : ℕ) (x : WO S T) :
    rdAdj S T βS βT φ (n • x) = n • rdAdj S T βS βT φ x :=
  (AddMonoidHom.mk' (rdAdj S T βS βT φ) (rdAdj_add S T βS βT φ)).map_nsmul n x

theorem rdAdj_sub (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D))
    {v : HeightOneSpectrum (𝓞 D.host.F)} (φ : Formalism.IndefR.Lev.EAf D →+* Fv D.host.F v) (x y : WO S T) :
    rdAdj S T βS βT φ (x - y) = rdAdj S T βS βT φ x - rdAdj S T βS βT φ y :=
  (AddMonoidHom.mk' (rdAdj S T βS βT φ) (rdAdj_add S T βS βT φ)).map_sub x y

theorem exists_natCast_dvd_pow (v : HeightOneSpectrum (𝓞 D.host.F)) {ϖ : GlobalTheory.SplitHecke.Ov D v} (hϖ : Irreducible ϖ)
    (m : ℕ) (hm : 0 < m) : ∃ N : ℕ, (m : GlobalTheory.SplitHecke.Ov D v) ∣ ϖ ^ N := by
  have hne : (m : GlobalTheory.SplitHecke.Ov D v) ≠ 0 := by
    intro h
    have h1 := congrArg (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)) h
    rw [map_natCast, map_zero, ← map_natCast (algebraMap D.host.F (Fv D.host.F v))] at h1
    have h2 := (algebraMap D.host.F (Fv D.host.F v)).injective (h1.trans (map_zero _).symm)
    exact hm.ne' (by exact_mod_cast h2)
  obtain ⟨N, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hne hϖ
  exact ⟨N, (u : GlobalTheory.SplitHecke.Ov D v), hu.symm⟩

end GlobalTheory.DownLift.SplitCoef

namespace GlobalTheory.DownLift.SplitCoef

theorem sbHalf_locConst_cptSupp : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D)) (e : AE D) (PP : Pl D.host.E) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : Formalism.IndefR.Lev.EAf D →+* Fv D.host.F v) (ι : kP PP ≃+* IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v)), Formalism.L2.NTheta.IsIdemAt e PP → LevChart e PP v φ ι → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), Submodule.IsFullLattice D.host.E ΛS → Submodule.IsFullLattice D.host.E ΛT → ∀ Φ : WO S T → ℂ, IsSBHalf (cA D e) (latH S T ΛS ΛT) Φ → ∀ ϖ : (GlobalTheory.SplitHecke.Ov D v), Irreducible ϖ → ∃ N : ℕ, (∀ x x' : WO S T, IsHalf (cA D e) x → IsHalf (cA D e) x' → ∀ z : Matrix (Fin S.rank) (Fin T.rank) (GlobalTheory.SplitHecke.Ov D v), rdAdj S T βS βT φ x' = rdAdj S T βS βT φ x + (ϖ ^ N • z).map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)) → Φ x' = Φ x) ∧ ∀ x : WO S T, Φ x ≠ 0 → ∃ z : Matrix (Fin S.rank) (Fin T.rank) (GlobalTheory.SplitHecke.Ov D v), algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v) (ϖ ^ N) • rdAdj S T βS βT φ x = z.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)) := by
  intro D S T βS βT e PP v φ ι he hL ΛS ΛT hS hT Φ hΦ ϖ hϖ
  obtain ⟨hsurj, hinj, hint, -⟩ := GlobalTheory.T.frameAdjoint_chart_bijective_conjugateHalf D S T βS βT e PP v φ ι he hL
  obtain ⟨hsupp, k, hk, hinv, hkΛ⟩ := hΦ
  obtain ⟨K1, hK1, hdown⟩ := GlobalTheory.PlaceVec.frMapAdj_down S T βS βT
  obtain ⟨K2, hK2, hmem⟩ := GlobalTheory.PlaceVec.exists_nsmul_int_mem_latO hS hT
  obtain ⟨L1, hL1, hlat⟩ := GlobalTheory.PlaceVec.exists_nsmul_latO_int (S := S) (T := T) hS.fg hT.fg
  obtain ⟨L2, hL2, hup⟩ := GlobalTheory.PlaceVec.frMapAdj_up S T βS βT
  have hce : infPart D (cA D e) = 0 := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.SplitScalar.infPart_splitIdem he.1)
  obtain ⟨N, hN⟩ := exists_natCast_dvd_pow v hϖ (k * (K2 * K1) * (L2 * (L1 * k)))
    (by positivity)
  have hA : ((k * (K2 * K1) : ℕ) : GlobalTheory.SplitHecke.Ov D v) ∣ ϖ ^ N :=
    (Nat.cast_dvd_cast (Dvd.intro _ rfl)).trans hN
  have hM : ((L2 * (L1 * k) : ℕ) : GlobalTheory.SplitHecke.Ov D v) ∣ ϖ ^ N :=
    (Nat.cast_dvd_cast (Dvd.intro_left _ rfl)).trans hN
  refine ⟨N, ?_, ?_⟩
  · intro x x' hx hx' z hxz
    obtain ⟨w, hw⟩ := hA
    obtain ⟨t, ht, hrt⟩ := hsurj ((w • z).map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)))
    have htI : IsIntM (frMapAdj S T βS βT t) := (hint t ht).2 ⟨w • z, hrt⟩
    have h1 := hdown t htI
    rw [← GlobalTheory.PlaceVec.map_toEAf_nsmul] at h1
    have h0 : (K1 • t).map (infPart D) = 0 := by
      ext i j
      rw [Matrix.map_apply, Matrix.smul_apply, map_nsmul, ← ht i j, map_mul, hce, zero_mul, smul_zero, Matrix.zero_apply]
    have h2 := hmem _ h0 h1
    have hu : IsHalf (cA D e) (K2 • K1 • t) := isHalf_nsmul'' (isHalf_nsmul'' ht _) _
    have key : x' - x = k • (K2 • K1 • t) := by
      refine hinj _ _ (isHalf_sub' hx' hx) (isHalf_nsmul'' hu _) ?_
      rw [rdAdj_sub, hxz, add_sub_cancel_left, rdAdj_nsmul, rdAdj_nsmul, rdAdj_nsmul, hrt, hw]
      ext i j
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul, map_mul, map_natCast]
      push_cast
      ring
    have : x' = x + k • (K2 • K1 • t) := by rw [← key]; abel
    rw [this, hinv _ h2 hu x]
  · intro x hx
    have hhalf := hsupp x hx
    have h1 := hlat _ (hkΛ x hx)
    rw [← GlobalTheory.PlaceVec.map_toEAf_nsmul] at h1
    have h2 := hup _ h1
    rw [← frMapAdj_nsmul] at h2
    obtain ⟨z0, hz0⟩ := (hint _ (isHalf_nsmul'' (isHalf_nsmul'' (isHalf_nsmul'' hhalf k) L1) L2)).1 h2
    rw [rdAdj_nsmul, rdAdj_nsmul, rdAdj_nsmul] at hz0
    obtain ⟨w', hw'⟩ := hM
    refine ⟨w' • z0, ?_⟩
    ext i j
    have hij := congrFun (congrFun hz0 i) j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul] at hij ⊢
    rw [hw', map_mul, map_mul, ← hij, map_natCast]
    push_cast
    ring

end GlobalTheory.DownLift.SplitCoef

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchwartzBruhatConjHalfLocallyConstantCompactSuppStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhat_conjHalf_locallyConstant_compactSupport : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D)) (e : AE D) (PP : Pl D.host.E) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : Formalism.IndefR.Lev.EAf D →+* Fv D.host.F v) (ι : kP PP ≃+* IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v)), Formalism.L2.NTheta.IsIdemAt e PP → LevChart e PP v φ ι → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), Submodule.IsFullLattice D.host.E ΛS → Submodule.IsFullLattice D.host.E ΛT → ∀ Φ : WO S T → ℂ, IsSBHalf (cA D e) (latH S T ΛS ΛT) Φ → ∀ ϖ : (GlobalTheory.SplitHecke.Ov D v), Irreducible ϖ → ∃ N : ℕ, (∀ x x' : WO S T, IsHalf (cA D e) x → IsHalf (cA D e) x' → ∀ z : Matrix (Fin S.rank) (Fin T.rank) (GlobalTheory.SplitHecke.Ov D v), rdAdj S T βS βT φ x' = rdAdj S T βS βT φ x + (ϖ ^ N • z).map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)) → Φ x' = Φ x) ∧ ∀ x : WO S T, Φ x ≠ 0 → ∃ z : Matrix (Fin S.rank) (Fin T.rank) (GlobalTheory.SplitHecke.Ov D v), algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v) (ϖ ^ N) • rdAdj S T βS βT φ x = z.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)) := by
  exact @_root_.GlobalTheory.DownLift.SplitCoef.sbHalf_locConst_cptSupp
end
end
