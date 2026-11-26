module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TatePairingLatticeQuotientsNondegenerate
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWachLatticeMatricesGammaPhi

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTorsionPairingEqInvUniformizer
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTorsionPairingEqInvUniformizer
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)

noncomputable section

namespace GlobalTheory.LocDualInt

theorem linK_smul {O : Type} [CommRing O] [IsDomain O] {V : Type} [AddCommGroup V] [Module O V]
    [Module (FractionRing O) V] [IsScalarTower O (FractionRing O) V]
    (φ : V →ₗ[O] FractionRing O) (c : FractionRing O) (v : V) : φ (c • v) = c * φ v :=
  (LinearMap.extendScalarsOfIsLocalization (nonZeroDivisors O) (FractionRing O) φ).map_smul c v

theorem exists_pairKO_eq_inv_unif : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [TopologicalSpace (FractionRing O)] [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)] {VT VT' : Type} [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT] [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT'] [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT'] {G : Type} [Group G] [TopologicalSpace G] (D : LatData O G VT VT'), ∀ ϖ : O, Irreducible ϖ → ∀ (n : ℕ) (f : ↥D.T'), f ∉ powSub (M := ↥D.T') ϖ n → ∃ x : VT ⧸ D.T, ϖ ^ n • x = 0 ∧ pairKO D.bT D.T x f = toKO O ((algebraMap O (FractionRing O) ϖ)⁻¹) := by
  intro O _ _ _ _ _ _ _ VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ G _ _ D ϖ hϖ n f hf
  set π : (FractionRing O) := algebraMap O (FractionRing O) ϖ with hπ
  have hπ0 : π ≠ 0 := by
    rw [hπ]; exact (map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).2 hϖ.ne_zero
  have hpn : ∀ y : VT', ϖ ^ n • y = π ^ n • y := fun y => by
    rw [← algebraMap_smul (FractionRing O) (ϖ ^ n) y, map_pow]
  have hpnT : ∀ y : VT, ϖ ^ n • y = π ^ n • y := fun y => by
    rw [← algebraMap_smul (FractionRing O) (ϖ ^ n) y, map_pow]
  set f' : VT' := (π ^ n)⁻¹ • (f : VT') with hf'
  have hff' : ϖ ^ n • f' = f := by
    rw [hpn, hf', smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hπ0), one_smul]
  clear_value f' π
  have hnot : f' ∉ D.T' := by
    intro h
    apply hf
    refine mem_powSub.2 ⟨⟨f', h⟩, ?_⟩
    ext
    simp [hff']
  have hnot' : ¬ ∀ x ∈ D.T, D.bT x f' ∈ (1 : Submodule O (FractionRing O)) := hnot
  push_neg at hnot'
  obtain ⟨v, hvT, hu⟩ := hnot'
  set u := D.bT v f' with hu_def
  have hu0 : u ≠ 0 := by
    intro h; apply hu; rw [h]; exact Submodule.zero_mem _
  have hnotint : ¬ IsLocalization.IsInteger O u := by
    rintro ⟨o, ho⟩; exact hu (Submodule.mem_one.2 ⟨o, ho⟩)
  obtain ⟨w, hw⟩ : IsLocalization.IsInteger O u⁻¹ :=
    (ValuationRing.isInteger_or_isInteger O u).resolve_left hnotint
  have hwnu : w ∉ nonunits O → False := by
    intro h
    rw [mem_nonunits_iff, not_not] at h
    obtain ⟨w', hw'⟩ := h
    apply hnotint
    refine ⟨(w'⁻¹ : Oˣ), ?_⟩
    have : algebraMap O (FractionRing O) (w' : O) * u = 1 := by
      rw [hw', hw, inv_mul_cancel₀ hu0]
    have h2 : algebraMap O (FractionRing O) ((w'⁻¹ : Oˣ) : O) * algebraMap O (FractionRing O) (w' : O) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    calc algebraMap O (FractionRing O) ((w'⁻¹ : Oˣ) : O) = algebraMap O (FractionRing O) ((w'⁻¹ : Oˣ) : O) * (algebraMap O (FractionRing O) (w' : O) * u) := by rw [this, mul_one]
      _ = u := by rw [← mul_assoc, h2, one_mul]
  have hwm : w ∈ IsLocalRing.maximalIdeal O := by
    by_contra h
    exact hwnu h
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.mem_span_singleton'] at hwm
  obtain ⟨o, ho⟩ := hwm
  have hkey : D.bT (o • v) f' = π⁻¹ := by
    rw [D.bT.map_smul o v, LinearMap.smul_apply, Algebra.smul_def, ← hu_def]
    have h1 : algebraMap O (FractionRing O) o * π = u⁻¹ := by rw [hπ, ← map_mul, ho, hw]
    have : algebraMap O (FractionRing O) o = u⁻¹ * π⁻¹ := by
      rw [← h1, mul_assoc, mul_inv_cancel₀ hπ0, mul_one]
    rw [this, mul_comm u⁻¹, mul_assoc, inv_mul_cancel₀ hu0, mul_one]
  refine ⟨Submodule.Quotient.mk ((π ^ n)⁻¹ • (o • v)), ?_, ?_⟩
  · rw [← Submodule.Quotient.mk_smul, hpnT, smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hπ0), one_smul,
      Submodule.Quotient.mk_eq_zero]
    exact D.T.smul_mem o hvT
  · rw [pairKO_mk, ← hkey]
    congr 1
    have e1 : D.bT ((π ^ n)⁻¹ • (o • v)) f = (π ^ n)⁻¹ * D.bT (o • v) f :=
      linK_smul (D.bT.flip (f : VT')) ((π ^ n)⁻¹) (o • v)
    have e2 : D.bT (o • v) ((π ^ n)⁻¹ • (f : VT')) = (π ^ n)⁻¹ * D.bT (o • v) f :=
      linK_smul (D.bT (o • v)) ((π ^ n)⁻¹) (f : VT')
    rw [e1, hf', e2]

end GlobalTheory.LocDualInt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTorsionPairingEqInvUniformizerStatement
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torsion_pairing_eq_inv_uniformizer : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [TopologicalSpace (FractionRing O)] [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)] {VT VT' : Type} [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT] [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT'] [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT'] {G : Type} [Group G] [TopologicalSpace G] (D : LatData O G VT VT'), ∀ ϖ : O, Irreducible ϖ → ∀ (n : ℕ) (f : ↥D.T'), f ∉ powSub (M := ↥D.T') ϖ n → ∃ x : VT ⧸ D.T, ϖ ^ n • x = 0 ∧ pairKO D.bT D.T x f = toKO O ((algebraMap O (FractionRing O) ϖ)⁻¹) := by
  first | exact @GlobalTheory.LocDualInt.exists_pairKO_eq_inv_unif | exact GlobalTheory.LocDualInt.exists_pairKO_eq_inv_unif | (intros; apply GlobalTheory.LocDualInt.exists_pairKO_eq_inv_unif <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinitePowSmulTorsionLatticeQuotient
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinitePowSmulTorsionLatticeQuotient
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)

noncomputable section

namespace GlobalTheory.LatTorsFinite

theorem finite_quot_of_isOpen {O : Type} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] (I : Ideal O) (hI : IsOpen (I : Set O)) : Finite (O ⧸ I) := by
  have hU : ∀ x : O, IsOpen ((fun y => y - x) ⁻¹' (I : Set O)) := fun x =>
    hI.preimage (continuous_id.sub continuous_const)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : O => (fun y => y - x) ⁻¹' (I : Set O))
    hU (fun y _ => Set.mem_iUnion.2 ⟨y, by simp [I.zero_mem]⟩)
  refine Finite.of_surjective (fun x : t => Ideal.Quotient.mk I (x : O)) ?_
  intro q
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
  refine ⟨⟨x, hx⟩, ?_⟩
  exact (Ideal.Quotient.eq.2 hyx).symm

theorem finite_quot_pow {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] (hO : IsTopologicalRing O) (hc : CompactSpace O)
    (hA : IsAdic (IsLocalRing.maximalIdeal O)) {ϖ : O} (hϖ : Irreducible ϖ) (n : ℕ) :
    Finite (O ⧸ Ideal.span {ϖ ^ n}) := by
  have hm : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  have hopen : IsOpen (((IsLocalRing.maximalIdeal O) ^ n : Ideal O) : Set O) :=
    (isAdic_iff.1 hA).1 n
  rw [hm, Ideal.span_singleton_pow] at hopen
  exact finite_quot_of_isOpen _ hopen

theorem finite_ker_pow_smul {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] {V : Type} [AddCommGroup V] [Module O V] [Module (FractionRing O) V]
    [IsScalarTower O (FractionRing O) V] (T : Submodule O V) (hO : IsTopologicalRing O)
    (hc : CompactSpace O) (hA : IsAdic (IsLocalRing.maximalIdeal O)) (hT : IsLatticeIn T)
    (ϖ : O) (hϖ : Irreducible ϖ) (n : ℕ) :
    Finite ↥(LinearMap.ker (LinearMap.lsmul O (V ⧸ T) (ϖ ^ n))) := by
  haveI := finite_quot_pow hO hc hA hϖ n
  haveI : Module.Finite O T := Module.Finite.iff_fg.2 hT.1
  haveI : Module.Finite (O ⧸ Ideal.span {ϖ ^ n})
      (T ⧸ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O T)) :=
    Module.Finite.of_restrictScalars_finite O _ _
  haveI : Finite (T ⧸ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O T)) :=
    Module.finite_of_finite (O ⧸ Ideal.span {ϖ ^ n})

  let rep : V ⧸ T → V := fun q => Classical.choose (Submodule.Quotient.mk_surjective T q)
  have hrep : ∀ q, Submodule.Quotient.mk (p := T) (rep q) = q := fun q =>
    Classical.choose_spec (Submodule.Quotient.mk_surjective T q)
  have hmem : ∀ x : LinearMap.ker (LinearMap.lsmul O (V ⧸ T) (ϖ ^ n)),
      ϖ ^ n • rep (x : V ⧸ T) ∈ T := by
    intro x
    have hx : (ϖ ^ n) • (x : V ⧸ T) = 0 := x.2
    rw [← hrep (x : V ⧸ T), ← Submodule.Quotient.mk_smul] at hx
    exact (Submodule.Quotient.mk_eq_zero T).1 hx

  have hinj : ∀ v w : V, ϖ ^ n • v = ϖ ^ n • w → v = w := by
    intro v w h
    have h0 : algebraMap O (FractionRing O) (ϖ ^ n) ≠ 0 := by
      rw [Ne, IsFractionRing.to_map_eq_zero_iff]; exact pow_ne_zero _ hϖ.ne_zero
    rw [← algebraMap_smul (FractionRing O) (ϖ ^ n) v,
      ← algebraMap_smul (FractionRing O) (ϖ ^ n) w] at h
    exact smul_right_injective V h0 h
  let f : LinearMap.ker (LinearMap.lsmul O (V ⧸ T) (ϖ ^ n)) →
      T ⧸ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O T) :=
    fun x => Submodule.Quotient.mk ⟨ϖ ^ n • rep (x : V ⧸ T), hmem x⟩
  refine Finite.of_injective f ?_
  intro x y hxy
  rw [Submodule.Quotient.eq, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists] at hxy
  obtain ⟨t, -, ht⟩ := hxy
  have ht' : ϖ ^ n • (t : V) = ϖ ^ n • (rep (x : V ⧸ T) - rep (y : V ⧸ T)) := by
    rw [smul_sub]
    exact congrArg Subtype.val ht
  have hd := hinj _ _ ht'
  apply Subtype.ext
  rw [← hrep (x : V ⧸ T), ← hrep (y : V ⧸ T), Submodule.Quotient.eq, ← hd]
  exact t.2

end GlobalTheory.LatTorsFinite
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinitePowSmulTorsionLatticeQuotientStatement
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_pow_smul_torsion_lattice_quotient : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] {V : Type} [AddCommGroup V] [Module O V] [Module (FractionRing O) V] [IsScalarTower O (FractionRing O) V] (T : Submodule O V), IsTopologicalRing O → CompactSpace O → IsAdic (IsLocalRing.maximalIdeal O) → IsLatticeIn T → ∀ ϖ : O, Irreducible ϖ → ∀ n : ℕ, Finite ↥(LinearMap.ker (LinearMap.lsmul O (V ⧸ T) (ϖ ^ n))) := by
  first | exact @GlobalTheory.LatTorsFinite.finite_ker_pow_smul | exact GlobalTheory.LatTorsFinite.finite_ker_pow_smul | (intros; apply GlobalTheory.LatTorsFinite.finite_ker_pow_smul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPadicIntRingHomCongrToZModPow
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPadicIntRingHomCongrToZModPow
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)

namespace GlobalTheory.ZpHomAdic

open IsLocalRing Filter Topology

theorem isPrecomplete_of_compact {O : Type} [CommRing O] [IsLocalRing O] [TopologicalSpace O]
    [IsTopologicalRing O] [CompactSpace O] (hA : IsAdic (maximalIdeal O)) :
    IsPrecomplete (maximalIdeal O) O := by
  refine ⟨fun f hf => ?_⟩
  obtain ⟨L, -, hL⟩ := (isCompact_univ (X := O)).exists_clusterPt (f := Filter.map f atTop)
    (le_principal_iff.2 univ_mem)
  refine ⟨L, fun n => ?_⟩
  have hopen : IsOpen ((maximalIdeal O ^ n : Ideal O) : Set O) := (isAdic_iff.1 hA).1 n
  have hclosed : IsClosed ((maximalIdeal O ^ n : Ideal O) : Set O) :=
    AddSubgroup.isClosed_of_isOpen ((maximalIdeal O ^ n).toAddSubgroup) hopen
  have hS : IsClosed {y : O | f n - y ∈ maximalIdeal O ^ n} :=
    hclosed.preimage (continuous_const.sub continuous_id)
  have hmem : {y : O | f n - y ∈ maximalIdeal O ^ n} ∈ Filter.map f atTop := by
    refine Filter.mem_map.2 (Filter.mem_atTop_sets.2 ⟨n, fun k hk => ?_⟩)
    have := hf hk
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this
    exact this
  have hL' : L ∈ closure {y : O | f n - y ∈ maximalIdeal O ^ n} :=
    mem_closure_iff_clusterPt.2 (hL.mono (le_principal_iff.2 hmem))
  rw [hS.closure_eq] at hL'
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
  exact hL'

theorem isHausdorff_dvr {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] :
    IsHausdorff (maximalIdeal O) O := by
  refine ⟨fun x hx => ?_⟩
  rw [← Ideal.mem_bot, ← Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal O)
    (maximalIdeal.isMaximal O).ne_top, Ideal.mem_iInf]
  intro n
  have := hx n
  rwa [SModEq.zero, smul_eq_mul, Ideal.mul_top] at this

theorem ringHom_zmod_apply {N : ℕ} [NeZero N] {R : Type*} [Ring R] (ψ : ZMod N →+* R) (z : ZMod N) :
    ψ z = ((z.val : ℕ) : R) := by
  conv_lhs => rw [← ZMod.natCast_zmod_val z]
  exact map_natCast ψ _

theorem val_toZModPow_sub_mem {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] {m n : ℕ} (h : m ≤ n)
    (x : ℤ_[p]) :
    ((PadicInt.toZModPow n x).val : O) - ((PadicInt.toZModPow m x).val : O) ∈
      Ideal.span {(p : O) ^ m} := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  haveI : NeZero (p ^ m) := ⟨pow_ne_zero _ hp⟩
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ hp⟩
  have h1 : (((PadicInt.toZModPow n x).val : ℕ) : ZMod (p ^ m)) =
      (((PadicInt.toZModPow m x).val : ℕ) : ZMod (p ^ m)) := by
    rw [ZMod.natCast_val, ZMod.natCast_zmod_val, PadicInt.cast_toZModPow m n h]
  rw [ZMod.natCast_eq_natCast_iff] at h1
  obtain ⟨c, hc⟩ := (Nat.modEq_iff_dvd.1 h1.symm)
  rw [Ideal.mem_span_singleton]
  refine ⟨(c : O), ?_⟩
  have := congrArg (fun t : ℤ => (t : O)) hc
  push_cast at this
  exact this

end GlobalTheory.ZpHomAdic

namespace GlobalTheory.ZpHomAdic
open IsLocalRing

noncomputable def zmodToQuot (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsLocalRing O]
    (hp : (p : O) ∈ maximalIdeal O) (n : ℕ) : ZMod (p ^ n) →+* O ⧸ maximalIdeal O ^ n :=
  (Ideal.Quotient.lift (Ideal.span {((p ^ n : ℕ) : ℤ)}) (Int.castRingHom _) (fun a ha => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, map_natCast, Nat.cast_pow, ← map_natCast (Ideal.Quotient.mk (maximalIdeal O ^ n)) p,
      ← map_pow, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_pow hp n), mul_zero])).comp
    (Int.quotientSpanNatEquivZMod (p ^ n)).symm.toRingHom

theorem exists_ringHom_padicInt {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [TopologicalSpace O] (hT : IsTopologicalRing O)
    (_hC : CompactSpace O) (_hH : T2Space O) (hA : IsAdic (maximalIdeal O))
    (hp : (p : O) ∈ maximalIdeal O) :
    ∃ ι : ℤ_[p] →+* O, ∀ (x : ℤ_[p]) (k : ℕ),
      ι x - ((PadicInt.toZModPow k x).val : O) ∈ Ideal.span {(p : O) ^ k} := by
  haveI := hT
  haveI : IsAdicComplete (maximalIdeal O) O :=
    { toIsHausdorff := isHausdorff_dvr, toIsPrecomplete := isPrecomplete_of_compact hA }
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  haveI hNZ : ∀ n, NeZero (p ^ n) := fun n => ⟨pow_ne_zero _ hp0⟩
  let f : (n : ℕ) → ℤ_[p] →+* O ⧸ maximalIdeal O ^ n := fun n =>
    (zmodToQuot p O hp n).comp (PadicInt.toZModPow n)
  have hfx : ∀ n x, f n x = Ideal.Quotient.mk _ ((PadicInt.toZModPow n x).val : O) := by
    intro n x
    show zmodToQuot p O hp n _ = _
    rw [ringHom_zmod_apply, map_natCast]
  have hf : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorPow (maximalIdeal O) hle).comp (f n) = f m := by
    intro m n hle
    ext x
    rw [RingHom.comp_apply, hfx, hfx, Ideal.Quotient.factor_mk, Ideal.Quotient.eq]
    exact Ideal.span_singleton_le_iff_mem _ |>.2 (Ideal.pow_mem_pow hp m)
      (val_toZModPow_sub_mem hle x)
  refine ⟨IsAdicComplete.liftRingHom (maximalIdeal O) f hf, fun x k => ?_⟩
  set ι := IsAdicComplete.liftRingHom (maximalIdeal O) f hf
  have hι : ∀ n, ι x - ((PadicInt.toZModPow n x).val : O) ∈ maximalIdeal O ^ n := by
    intro n
    rw [← Ideal.Quotient.eq, IsAdicComplete.mk_liftRingHom, hfx]
  set J : Ideal O := Ideal.span {(p : O) ^ k}
  rw [← Submodule.Quotient.mk_eq_zero (p := J), ← Submodule.mem_bot O,
    ← Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := O ⧸ J) (maximalIdeal O)
      (maximalIdeal.isMaximal O).ne_top, Submodule.mem_iInf]
  intro n
  have hle : maximalIdeal O ^ max n k • (⊤ : Submodule O (O ⧸ J)) ≤ maximalIdeal O ^ n • ⊤ :=
    Submodule.smul_mono_left (Ideal.pow_le_pow_right (le_max_left n k))
  refine hle ?_
  have hsplit : ι x - ((PadicInt.toZModPow k x).val : O) =
      (ι x - ((PadicInt.toZModPow (max n k) x).val : O)) +
      (((PadicInt.toZModPow (max n k) x).val : O) - ((PadicInt.toZModPow k x).val : O)) := by ring
  rw [hsplit, Submodule.Quotient.mk_add,
    (Submodule.Quotient.mk_eq_zero J).2 (val_toZModPow_sub_mem (le_max_right n k) x), add_zero,
    ← mul_one (ι x - _), ← smul_eq_mul, Submodule.Quotient.mk_smul]
  exact Submodule.smul_mem_smul (hι _) Submodule.mem_top

theorem zp_ringHom : ∀ {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O], IsTopologicalRing O → CompactSpace O → T2Space O → IsAdic (IsLocalRing.maximalIdeal O) → (p : O) ∈ IsLocalRing.maximalIdeal O → ∃ ι : ℤ_[p] →+* O, ∀ (x : ℤ_[p]) (k : ℕ), ι x - ((PadicInt.toZModPow k x).val : O) ∈ Ideal.span {(p : O) ^ k} :=
  fun hT hC hH hA hp => exists_ringHom_padicInt hT hC hH hA hp

end GlobalTheory.ZpHomAdic
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPadicIntRingHomCongrToZModPowStatement
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_padicInt_ringHom_congr_toZModPow : ∀ {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O], IsTopologicalRing O → CompactSpace O → T2Space O → IsAdic (IsLocalRing.maximalIdeal O) → (p : O) ∈ IsLocalRing.maximalIdeal O → ∃ ι : ℤ_[p] →+* O, ∀ (x : ℤ_[p]) (k : ℕ), ι x - ((PadicInt.toZModPow k x).val : O) ∈ Ideal.span {(p : O) ^ k} := by
  first | exact @GlobalTheory.ZpHomAdic.zp_ringHom | exact GlobalTheory.ZpHomAdic.zp_ringHom | (intros; apply GlobalTheory.ZpHomAdic.zp_ringHom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDualLatticePairingEqInvUniformizer
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDualLatticePairingEqInvUniformizer
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)

noncomputable section

namespace GlobalTheory.LocDualInt

section PerfL

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {V : Type} [AddCommGroup V] [Module O V] [Module (FractionRing O) V]
  [IsScalarTower O (FractionRing O) V]

theorem exists_form_of_not_mem {T : Submodule O V} (hT : IsLatticeIn T) {v : V} (hv : v ∉ T) :
    ∃ ψ : V →ₗ[FractionRing O] FractionRing O,
      (∀ t ∈ T, ψ t ∈ (1 : Submodule O (FractionRing O))) ∧
        ψ v ∉ (1 : Submodule O (FractionRing O)) := by
  classical
  haveI : Module.Finite O T := Module.Finite.iff_fg.2 hT.1
  haveI : Module.IsTorsionFree O T := Module.IsTorsionFree.of_smul_eq_zero fun r m h => by
    have h1 : (algebraMap O (FractionRing O) r) • (m : V) = 0 := by
      rw [algebraMap_smul]
      exact congrArg Subtype.val h
    rcases smul_eq_zero.1 h1 with h2 | h2
    · left
      exact (IsFractionRing.injective O (FractionRing O)) (by rw [h2, map_zero])
    · right
      exact Subtype.ext h2
  haveI : Module.Free O T := Module.free_of_finite_type_torsion_free'
  let e := Module.Free.chooseBasis O T
  let w : Module.Free.ChooseBasisIndex O T → V := fun i => (e i : V)
  have hliO : LinearIndependent O w := e.linearIndependent.map' T.subtype (Submodule.ker_subtype T)
  have hli : LinearIndependent (FractionRing O) w :=
    (LinearIndependent.iff_fractionRing O (FractionRing O)).1 hliO
  have hspO : Submodule.span O (Set.range w) = T := by
    have h := congrArg (Submodule.map T.subtype) e.span_eq
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at h
    exact h
  have hsp : ⊤ ≤ Submodule.span (FractionRing O) (Set.range w) := by
    rw [← hT.2]
    apply Submodule.span_le.2
    intro t ht
    rw [← hspO] at ht
    exact Submodule.span_subset_span O (FractionRing O) (Set.range w) ht
  let bK := Module.Basis.mk hli hsp
  have hbK : ∀ i, bK i = w i := fun i => Module.Basis.mk_apply hli hsp i

  have hint : ∀ t ∈ T, ∀ j, bK.repr t j ∈ (1 : Submodule O (FractionRing O)) := by
    intro t ht
    rw [← hspO] at ht
    induction ht using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      intro j
      rw [← hbK, bK.repr_self, Finsupp.single_apply]
      split_ifs
      · exact Submodule.mem_one.2 ⟨1, map_one _⟩
      · exact Submodule.zero_mem _
    | zero => intro j; simp
    | add x y _ _ hx hy => intro j; rw [map_add (f := _), Finsupp.add_apply]; exact Submodule.add_mem _ (hx j) (hy j)
    | smul a x _ hx =>
      intro j
      rw [← algebraMap_smul (FractionRing O) a x, map_smul, Finsupp.smul_apply, algebraMap_smul]
      exact Submodule.smul_mem _ a (hx j)
  have hex : ∃ j, bK.repr v j ∉ (1 : Submodule O (FractionRing O)) := by
    by_contra hne
    push Not at hne
    apply hv
    rw [← bK.linearCombination_repr v, Finsupp.linearCombination_apply, Finsupp.sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    obtain ⟨a, ha⟩ := Submodule.mem_one.1 (hne j)
    rw [← ha, algebraMap_smul, hbK]
    exact Submodule.smul_mem _ a (e j).2
  obtain ⟨j, hj⟩ := hex
  exact ⟨bK.coord j, fun t ht => hint t ht j, hj⟩

theorem exists_mul_eq_inv_unif {ϖ : O} (hϖ : Irreducible ϖ) {u : FractionRing O}
    (hu : u ∉ (1 : Submodule O (FractionRing O))) :
    ∃ o : O, algebraMap O (FractionRing O) o * u = (algebraMap O (FractionRing O) ϖ)⁻¹ := by
  have hu0 : u ≠ 0 := fun h => hu (h ▸ Submodule.zero_mem _)
  rcases ValuationRing.isInteger_or_isInteger O u with h | ⟨w, hw⟩
  · exact absurd (Submodule.mem_one.2 h) hu
  have hwu : ¬ IsUnit w := by
    intro hw'
    apply hu
    refine Submodule.mem_one.2 ⟨((hw'.unit⁻¹ : Oˣ) : O), ?_⟩
    have h1 : algebraMap O (FractionRing O) ((hw'.unit⁻¹ : Oˣ) : O) * u⁻¹ = 1 := by
      rw [← hw, ← map_mul, IsUnit.val_inv_mul, map_one]
    calc algebraMap O (FractionRing O) ((hw'.unit⁻¹ : Oˣ) : O)
        = algebraMap O (FractionRing O) ((hw'.unit⁻¹ : Oˣ) : O) * (u⁻¹ * u) := by
          rw [inv_mul_cancel₀ hu0, mul_one]
      _ = u := by rw [← mul_assoc, h1, one_mul]
  have hwm : w ∈ IsLocalRing.maximalIdeal O := hwu
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hwm
  obtain ⟨o, rfl⟩ := hwm
  refine ⟨o, ?_⟩
  rw [map_mul] at hw
  symm
  apply inv_eq_of_mul_eq_one_right
  calc algebraMap O (FractionRing O) ϖ * (algebraMap O (FractionRing O) o * u)
      = (algebraMap O (FractionRing O) ϖ * algebraMap O (FractionRing O) o) * u := by ring
    _ = 1 := by rw [hw, inv_mul_cancel₀ hu0]

end PerfL

section Main

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
  [TopologicalSpace (FractionRing O)] [IsTopologicalAddGroup (FractionRing O)]
  [ContinuousSMul O (FractionRing O)] {VT VT' : Type} [AddCommGroup VT] [Module O VT]
  [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT]
  [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT] [AddCommGroup VT']
  [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT']
  {G : Type} [Group G] [TopologicalSpace G]

theorem exists_dual_pairKO_eq_inv_unif (D : LatData O G VT VT') (hT : IsLatticeIn D.T)
    (hP : PerfectRight D.bT) (ϖ : O) (hϖ : Irreducible ϖ) (x : VT ⧸ D.T) (hx : x ≠ 0) :
    ∃ f : ↥D.T', pairKO D.bT D.T x f = toKO O ((algebraMap O (FractionRing O) ϖ)⁻¹) := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective D.T x
  have hv : v ∉ D.T := fun h => hx ((Submodule.Quotient.mk_eq_zero _).2 h)
  obtain ⟨ψ, hψT, hψv⟩ := exists_form_of_not_mem hT hv
  obtain ⟨f, hf, -⟩ := hP ψ
  have hfT : f ∈ D.T' := fun t ht => by rw [hf]; exact hψT t ht
  obtain ⟨o, ho⟩ := exists_mul_eq_inv_unif hϖ (u := D.bT v f) (by rw [hf]; exact hψv)
  refine ⟨⟨o • f, D.T'.smul_mem o hfT⟩, ?_⟩
  rw [pairKO_mk]
  congr 1
  show D.bT v (o • f) = _
  rw [map_smul, Algebra.smul_def, ho]

end Main

end GlobalTheory.LocDualInt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDualLatticePairingEqInvUniformizerStatement
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dualLattice_pairing_eq_inv_uniformizer : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [TopologicalSpace (FractionRing O)] [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)] {VT VT' : Type} [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT] [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT'] {G : Type} [Group G] [TopologicalSpace G] (D : LatData O G VT VT'), IsLatticeIn D.T → PerfectRight D.bT → ∀ ϖ : O, Irreducible ϖ → ∀ x : VT ⧸ D.T, x ≠ 0 → ∃ f : ↥D.T', pairKO D.bT D.T x f = toKO O ((algebraMap O (FractionRing O) ϖ)⁻¹) := by
  first | exact @GlobalTheory.LocDualInt.exists_dual_pairKO_eq_inv_unif | exact GlobalTheory.LocDualInt.exists_dual_pairKO_eq_inv_unif | (intros; apply GlobalTheory.LocDualInt.exists_dual_pairKO_eq_inv_unif <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCocycleCupNotCoboundaryFiniteLevel
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)

noncomputable section

namespace GlobalTheory.LocDualFin

theorem ko_torsion : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ), (p : O) ∈ IsLocalRing.maximalIdeal O → ∀ a : KO O, ∃ r : ℕ, (p : O) ^ r • a = 0 := by
  intro O _ _ _ p hp a
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨o, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := O) x
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero hs) hϖ
  obtain ⟨t, ht⟩ : ϖ ∣ (p : O) := Ideal.mem_span_singleton.1 (hϖ.maximalIdeal_eq ▸ hp)
  have hinj := IsFractionRing.injective O (FractionRing O)
  have hπ : algebraMap O (FractionRing O) ϖ ≠ 0 := (map_ne_zero_iff _ hinj).2 hϖ.ne_zero
  have hu0 : algebraMap O (FractionRing O) (u : O) ≠ 0 := (map_ne_zero_iff _ hinj).2 u.ne_zero
  refine ⟨m, ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_one]
  refine ⟨o * t ^ m * ((u⁻¹ : Oˣ) : O), ?_⟩
  rw [Algebra.smul_def, hu, ht]
  simp only [map_mul, map_pow]
  have hui : algebraMap O (FractionRing O) ((u⁻¹ : Oˣ) : O) = (algebraMap O (FractionRing O) (u : O))⁻¹ := by
    exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])
  rw [hui]
  field_simp
  ring


open GlobalTheory.TateFin GlobalTheory.TateTop GlobalTheory.Cyc.TwistLift ReciprocityTheory.Neutral.Bridge in
theorem exists_cocycle_cup_not_cob : Formalism.GaloisCohomology.LocalTateDualityK → ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [TopologicalSpace (FractionRing O)] [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)] {VT VT' : Type} [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT] [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT'] [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT'] {G : Type} [Group G] [TopologicalSpace G], FiniteDimensional ℚ_[p] K → IsTopologicalRing O → CompactSpace O → T2Space O → IsAdic (IsLocalRing.maximalIdeal O) → (p : O) ∈ IsLocalRing.maximalIdeal O → (p : O) ≠ 0 → Topology.IsOpenEmbedding (algebraMap O (FractionRing O)) → ∀ (i : G ≃ₜ* Formalism.GaloisCohomology.GK p K) (D : LatData O G VT VT'), (∀ (g : G) (n : ℕ) (ζ : PadicAlgCl p), ζ ^ (p ^ n) = 1 → ∃ a : ℕ, (i g) ζ = ζ ^ a ∧ ((D.ε g : Oˣ) : O) - (a : O) ∈ Ideal.span {(p : O) ^ n}) → IsLatticeIn D.T → PerfectRight D.bT → ContAction D.ρT → IsOpen (D.T : Set VT) → T2Space VT → T2Space VT' → ContinuousConstSMul (FractionRing O) VT → ContinuousConstSMul (FractionRing O) VT' → ∀ ϖ : O, Irreducible ϖ → ∀ c ∈ Z1 D.ρA, c ∉ B1 D.ρA → ∀ r : ℕ, (∀ g, ϖ ^ r • c g = 0) → ∀ n : ℕ, r ≤ n → ∃ z ∈ Z1 (quotRep D.ρTl' ϖ n), cupMod D c ϖ n z ∉ B2 (twist D.ε (KO O)) := by
  intro hTate p _ K O _ _ _ _ _ _ _ VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ G _ _ hK hOr hOc hOt hOa hpm hp0
    hemb i D hcyc hlat hperf hcontT hTo hT2 hT2' hcs hcs' ϖ hϖ c hc hcB r hr n hrn
  by_contra H
  push_neg at H
  apply hcB
  haveI : CompactSpace G := i.toHomeomorph.symm.compactSpace
  haveI : ContinuousMul G := ⟨by
    have h := i.symm.continuous.comp
      ((i.continuous.comp continuous_fst).mul (i.continuous.comp continuous_snd))
    refine h.congr fun q => ?_
    show i.symm (i q.1 * i q.2) = q.1 * q.2
    rw [← map_mul, ContinuousMulEquiv.symm_apply_apply]⟩
  let χ : G →* ℤ_[p]ˣ := ((cyclotomicCharacter (PadicAlgCl p) p).comp
    (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK p K) (PadicAlgCl p))).comp (i : G →* Formalism.GaloisCohomology.GK p K)
  have hχ : Continuous fun g => (χ g : ℤ_[p]) :=
    Units.continuous_val.comp ((cyclotomicCharacter.continuous p K (PadicAlgCl p)).comp i.continuous)
  have hT' : ∀ (k : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (p ^ (k + 1))) M] [Finite M]
      [TopologicalSpace M] [DiscreteTopology M] (rho : Representation (ZMod (p ^ (k + 1))) G M)
      (hrho : ContAction rho), DualityFor (redChar χ (k + 1)) rho hrho := by
    intro k M _ _ _ _ _ rho hrho
    refine DualityFor.of_comp i.symm _ hrho ?_
    have h1 : (redChar χ (k + 1)).comp (i.symm : Formalism.GaloisCohomology.GK p K →* G) = Formalism.GaloisCohomology.cycK p K (k + 1) :=
      MonoidHom.ext fun g => congrArg (Formalism.GaloisCohomology.cycK p K (k + 1)) (i.apply_symm_apply g)
    rw [h1]
    exact hTate p K hK (k + 1) M _ (Nat.succ_pos _) (contAction_comp i.symm hrho)
  obtain ⟨ι, hι⟩ := GlobalTheory.T.exists_padicInt_ringHom_congr_toZModPow hOr hOc hOt hOa hpm
  have hspan : Ideal.span {(p : O)} ≠ ⊤ := fun h =>
    (IsLocalRing.mem_maximalIdeal _).1 hpm (Ideal.span_singleton_eq_top.1 h)
  have hkrull : ∀ a b : O, (∀ k : ℕ, a - b ∈ Ideal.span {(p : O) ^ k}) → a = b := by
    intro a b h
    have h0 := Ideal.iInf_pow_eq_bot_of_isLocalRing (Ideal.span {(p : O)}) hspan
    have h1 : a - b ∈ ⨅ k, Ideal.span {(p : O)} ^ k :=
      Ideal.mem_iInf.2 fun k => by rw [Ideal.span_singleton_pow]; exact h k
    rw [h0, Ideal.mem_bot, sub_eq_zero] at h1
    exact h1
  have hιε : ∀ g, ι (χ g : ℤ_[p]) = (D.ε g : O) := by
    intro g
    refine hkrull _ _ fun k => ?_
    obtain ⟨ζ, hζ, hζa⟩ := GlobalTheory.T.cyclotomicCharacter_congr_root_of_unity_pow K (i g) k
    obtain ⟨a, ha, hεa⟩ := hcyc g k ζ hζ
    have e1 : (a : ZMod (p ^ k)) = PadicInt.toZModPow k (χ g : ℤ_[p]) := hζa a ha
    have e2 := hι (χ g : ℤ_[p]) k
    rw [← e1, ZMod.val_natCast] at e2
    have e3 : ((a : ℕ) : O) - ((a % p ^ k : ℕ) : O) ∈ Ideal.span {(p : O) ^ k} := by
      have h : ((a : ℕ) : O) = ((a / p ^ k : ℕ) : O) * (p : O) ^ k + ((a % p ^ k : ℕ) : O) := by
        have h' := congrArg (Nat.cast : ℕ → O) (Nat.div_add_mod' a (p ^ k)).symm
        push_cast at h'
        exact h'
      exact Ideal.mem_span_singleton'.2 ⟨((a / p ^ k : ℕ) : O), by rw [h]; ring⟩
    have e4 : ι (χ g : ℤ_[p]) - (D.ε g : O) = (ι (χ g : ℤ_[p]) - ((a % p ^ k : ℕ) : O)) -
        (((a : ℕ) : O) - ((a % p ^ k : ℕ) : O)) - ((D.ε g : O) - (a : O)) := by ring
    rw [e4]
    exact sub_mem (sub_mem e2 e3) hεa
  letI : Module ℤ_[p] (KO O) := Module.compHom (KO O) ι
  have hsmul : ∀ (u : ℤ_[p]) (y : KO O), u • y = ι u • y := fun _ _ => rfl
  have htor : ∀ a : KO O, ∃ r : ℕ, (p : ℤ_[p]) ^ r • a = 0 := fun a => by
    obtain ⟨r, hr⟩ := ko_torsion p hpm a
    exact ⟨r, by rw [hsmul, map_pow, map_natCast]; exact hr⟩
  have hKOd : DiscreteTopology (KO O) :=
    QuotientAddGroup.discreteTopology (N := (1 : Submodule O (FractionRing O)).toAddSubgroup) (by
      have : ((1 : Submodule O (FractionRing O)).toAddSubgroup : Set (FractionRing O)) =
          Set.range (algebraMap O (FractionRing O)) := by
        ext x; simp [Submodule.mem_one, eq_comm]
      rw [this]; exact hemb.isOpen_range)
  have hVd : DiscreteTopology (VT ⧸ D.T) :=
    QuotientAddGroup.discreteTopology (N := D.T.toAddSubgroup) hTo
  have hclc : IsLocallyConstant c := (IsLocallyConstant.iff_continuous c).2 hc.1
  set X := LinearMap.ker (LinearMap.lsmul O (VT ⧸ D.T) (ϖ ^ n)) with hXdef
  have memX : ∀ x : VT ⧸ D.T, x ∈ X ↔ ϖ ^ n • x = 0 := fun x => by
    rw [hXdef, LinearMap.mem_ker, LinearMap.lsmul_apply]
  haveI : Finite X := GlobalTheory.T.finite_pow_smul_torsion_lattice_quotient D.T hOr hOc hOa hlat ϖ hϖ n
  obtain ⟨hcT', hopen, -⟩ := GlobalTheory.T.dualLattice_compact_powSmul_nhds_basis D hOc hemb hlat hperf hT2' ϖ hϖ
  haveI : CompactSpace ↥D.T' := hcT'
  haveI : Finite (↥D.T' ⧸ powSub (M := ↥D.T') ϖ n) :=
    AddSubgroup.quotient_finite_of_isOpen (powSub (M := ↥D.T') ϖ n).toAddSubgroup (hopen n)
  haveI hNd : DiscreteTopology (↥D.T' ⧸ powSub (M := ↥D.T') ϖ n) :=
    QuotientAddGroup.discreteTopology (N := (powSub (M := ↥D.T') ϖ n).toAddSubgroup) (hopen n)
  obtain ⟨t, ht⟩ : ϖ ∣ (p : O) := Ideal.mem_span_singleton.1 (hϖ.maximalIdeal_eq ▸ hpm)
  have hpow : ∀ {M : Type} [AddCommGroup M] [Module O M] (y : M), p ^ n • y = t ^ n • ϖ ^ n • y :=
    fun y => by rw [← Nat.cast_smul_eq_nsmul O, Nat.cast_pow, ht, mul_pow, mul_comm, mul_smul]
  have hX : ∀ x : X, p ^ n • x = 0 := fun x => Subtype.ext (by
    rw [AddSubmonoidClass.coe_nsmul, hpow, (memX _).1 x.2, smul_zero]; rfl)
  have hN : ∀ y : ↥D.T' ⧸ powSub (M := ↥D.T') ϖ n, p ^ n • y = 0 := fun y => by
    obtain ⟨t0, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [hpow, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
      smul_comm]
    exact smul_mem_powSub ϖ n _
  let a : G → X → X := fun g x => ⟨D.ρA g x, by rw [memX, ← map_smul, (memX _).1 x.2, map_zero]⟩
  let a' : G → (↥D.T' ⧸ powSub (M := ↥D.T') ϖ n) →+ (↥D.T' ⧸ powSub (M := ↥D.T') ϖ n) :=
    fun g => (quotRep D.ρTl' ϖ n g).toAddMonoidHom
  have h1 : ∀ y, a' 1 y = y := fun y => by
    show quotRep D.ρTl' ϖ n 1 y = y
    rw [map_one]; rfl
  have hm : ∀ g h y, a' (g * h) y = a' g (a' h y) := fun g h y => by
    show quotRep D.ρTl' ϖ n (g * h) y = quotRep D.ρTl' ϖ n g (quotRep D.ρTl' ϖ n h y)
    rw [map_mul]; rfl
  have hlc : ∀ y, IsLocallyConstant fun g => a' g y := fun y => by
    obtain ⟨t0, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [IsLocallyConstant.iff_continuous]
    show Continuous fun g => (Submodule.Quotient.mk (D.ρTl' g t0) : ↥D.T' ⧸ powSub (M := ↥D.T') ϖ n)
    exact continuous_quot_mk.comp ((sub_contAction D.contT' D.T' D.stT').comp
      (continuous_id.prodMk continuous_const))
  let βf : X → (↥D.T' ⧸ powSub (M := ↥D.T') ϖ n) →+ KO O := fun x =>
    ((powSub (M := ↥D.T') ϖ n).liftQ (pairKO D.bT D.T (x : VT ⧸ D.T)) (fun t0 ht0 => by
      rw [LinearMap.mem_ker]; exact pairKO_eq_zero_of_mem D ((memX _).1 x.2) ht0)).toAddMonoidHom
  let β : X →+ (↥D.T' ⧸ powSub (M := ↥D.T') ϖ n) →+ KO O := AddMonoidHom.mk' βf (fun x x' => by
    ext y
    obtain ⟨t0, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    show pairKO D.bT D.T ((x + x' : X) : VT ⧸ D.T) t0 =
      pairKO D.bT D.T (x : VT ⧸ D.T) t0 + pairKO D.bT D.T (x' : VT ⧸ D.T) t0
    rw [Submodule.coe_add, map_add (f := _), LinearMap.add_apply])
  have he : ∀ g x y, β (a g x) (a' g y) = (χ g : ℤ_[p]) • β x y := fun g x y => by
    obtain ⟨t0, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    show pairKO D.bT D.T (D.ρA g x) (D.ρTl' g t0) = ι (χ g : ℤ_[p]) • pairKO D.bT D.T (x : VT ⧸ D.T) t0
    rw [D.pairKO_equiv, twist_apply, hιε]
  have hs : toKO O ((algebraMap O (FractionRing O) ϖ)⁻¹) ≠ 0 := by
    intro h0
    rw [toKO, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_one] at h0
    obtain ⟨o, ho⟩ := h0
    apply hϖ.not_isUnit
    have hinj := IsFractionRing.injective O (FractionRing O)
    have hπ : algebraMap O (FractionRing O) ϖ ≠ 0 := (map_ne_zero_iff _ hinj).2 hϖ.ne_zero
    refine IsUnit.of_mul_eq_one (b := o) (hinj ?_)
    rw [map_mul, ho, map_one, mul_inv_cancel₀ hπ]
  have hβ1 : ∀ x : X, x ≠ 0 → ∃ y, β x y = toKO O ((algebraMap O (FractionRing O) ϖ)⁻¹) := by
    intro x hx
    obtain ⟨f, hf⟩ := GlobalTheory.T.exists_dualLattice_pairing_eq_inv_uniformizer D hlat hperf ϖ hϖ (x : VT ⧸ D.T) (fun h => hx (Subtype.ext h))
    exact ⟨Submodule.Quotient.mk f, hf⟩
  have hβ2 : ∀ y, y ≠ 0 → ∃ x : X, β x y = toKO O ((algebraMap O (FractionRing O) ϖ)⁻¹) := by
    intro y hy
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have hf : f ∉ powSub (M := ↥D.T') ϖ n := fun h => hy ((Submodule.Quotient.mk_eq_zero _).2 h)
    obtain ⟨x, hx1, hx2⟩ := GlobalTheory.T.exists_torsion_pairing_eq_inv_uniformizer D ϖ hϖ n f hf
    exact ⟨⟨x, (memX x).2 hx1⟩, hx2⟩
  have hcX : ∀ g, c g ∈ X := fun g => (memX _).2 (by
    rw [← Nat.sub_add_cancel hrn, pow_add, mul_smul, hr, smul_zero])
  let c₀ : G → X := fun g => ⟨c g, hcX g⟩
  obtain ⟨x, hx⟩ := (nondeg_torsion hχ hT' htor hX hN a a' h1 hm hlc β he hs hβ1 hβ2).1 c₀
    (IsLocallyConstant.desc _ Subtype.val hclc Subtype.val_injective)
    (fun g h => Subtype.ext (hc.2 g h)) (by
      intro c' hc'l hc'c
      obtain ⟨b, hbc, hbe⟩ := (separated_dvr_second_cohomology_mem _ _).1 (H c' ⟨hc'l.continuous, fun g h => hc'c g h⟩)
      refine ⟨b, (IsLocallyConstant.iff_continuous b).2 hbc, fun q => ?_⟩
      obtain ⟨g, h⟩ := q
      have e := congrFun hbe (g, h)
      have e2 : β (c₀ g) (a' g (c' h)) = cupMod D c ϖ n c' (g, h) := by
        conv_lhs => rw [← mk_qlift (c' h)]
        rfl
      rw [e2, ← e]
      show _ = ι (χ g : ℤ_[p]) • b h - b (g * h) + b g
      rw [hιε]
      rfl)
  exact (mem_coboundaries1 _ _).2 ⟨x, fun g => congrArg Subtype.val (hx g)⟩

end GlobalTheory.LocDualFin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCocycleCupNotCoboundaryFiniteLevelStatement
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cocycle_cup_not_coboundary_finiteLevel : Formalism.GaloisCohomology.LocalTateDualityK → ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [TopologicalSpace (FractionRing O)] [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)] {VT VT' : Type} [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT] [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT'] [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT'] {G : Type} [Group G] [TopologicalSpace G], FiniteDimensional ℚ_[p] K → IsTopologicalRing O → CompactSpace O → T2Space O → IsAdic (IsLocalRing.maximalIdeal O) → (p : O) ∈ IsLocalRing.maximalIdeal O → (p : O) ≠ 0 → Topology.IsOpenEmbedding (algebraMap O (FractionRing O)) → ∀ (i : G ≃ₜ* Formalism.GaloisCohomology.GK p K) (D : LatData O G VT VT'), (∀ (g : G) (n : ℕ) (ζ : PadicAlgCl p), ζ ^ (p ^ n) = 1 → ∃ a : ℕ, (i g) ζ = ζ ^ a ∧ ((D.ε g : Oˣ) : O) - (a : O) ∈ Ideal.span {(p : O) ^ n}) → IsLatticeIn D.T → PerfectRight D.bT → ContAction D.ρT → IsOpen (D.T : Set VT) → T2Space VT → T2Space VT' → ContinuousConstSMul (FractionRing O) VT → ContinuousConstSMul (FractionRing O) VT' → ∀ ϖ : O, Irreducible ϖ → ∀ c ∈ Z1 D.ρA, c ∉ B1 D.ρA → ∀ r : ℕ, (∀ g, ϖ ^ r • c g = 0) → ∀ n : ℕ, r ≤ n → ∃ z ∈ Z1 (quotRep D.ρTl' ϖ n), cupMod D c ϖ n z ∉ B2 (twist D.ε (KO O)) := by
  first | exact @GlobalTheory.LocDualFin.exists_cocycle_cup_not_cob | exact GlobalTheory.LocDualFin.exists_cocycle_cup_not_cob | (intros; apply GlobalTheory.LocDualFin.exists_cocycle_cup_not_cob <;> assumption)
end
