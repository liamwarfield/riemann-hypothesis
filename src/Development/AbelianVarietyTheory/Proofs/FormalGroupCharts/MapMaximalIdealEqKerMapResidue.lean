module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.MvPowerSeriesExistsPolynomialTotalDegreeLeSubMem

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IsWeaklyRegularMvPowerSeriesOfFiniteColength
section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IsWeaklyRegularMvPowerSeriesOfFiniteColength
open IsLocalRing TensorProduct

namespace GlobalTheory

theorem isWeaklyRegular_mvPowerSeries_of_pow_le :
    ∀ (k : Type) [Field k] (σ : Type) [Finite σ] (n : ℕ) (e : Fin n ≃ σ)
      (f : σ → MvPowerSeries σ k), (∀ j, MvPowerSeries.constantCoeff (f j) = 0) →
      (∃ M : ℕ, Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ k)) ^ M ≤
        Ideal.span (Set.range f)) →
      RingTheory.Sequence.IsWeaklyRegular (MvPowerSeries σ k) (List.ofFn fun i => f (e i)) := by
  rintro k _ σ _ n e f h0 ⟨M, hM⟩
  have := FormalIsogeny.isRegularLocalRing_mvPowerSeries k σ
  refine (isRegular_of_radical_eq_maximalIdeal ?_ ?_).1
  · have h1 : Ideal.ofList (List.ofFn fun i => f (e i)) = Ideal.span (Set.range f) := by
      rw [ofList_ofFn_eq_span_range]
      exact congrArg Ideal.span (e.surjective.range_comp f)
    rw [h1]
    refine le_antisymm ((maximalIdeal.isMaximal _).isPrime.radical_le_iff.2 ?_) fun g hg => ?_
    · rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.2 (by simp [h0])
    · have h2 : MvPowerSeries.constantCoeff g = 0 := by
        simpa [maximalIdeal_eq_bot] using FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.1 hg
      have h3 : g ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ k)) := by
        rw [← germIdeal_eq_span]
        exact h2
      exact ⟨M, hM (Ideal.pow_mem_pow h3 M)⟩
  · rw [FormalIsogeny.ringKrullDim_mvPowerSeries, ringKrullDim_eq_zero_of_field, zero_add,
      List.length_ofFn, ← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fin]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IsWeaklyRegularMvPowerSeriesOfFiniteColengthStatement
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isWeaklyRegular_mvPowerSeries_of_finite_colength : ∀ (k : Type) [Field k] (σ : Type) [Finite σ] (n : ℕ) (e : Fin n ≃ σ) (f : σ → MvPowerSeries σ k), (∀ j, MvPowerSeries.constantCoeff (f j) = 0) → (∃ M : ℕ, Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ k)) ^ M ≤ Ideal.span (Set.range f)) → RingTheory.Sequence.IsWeaklyRegular (MvPowerSeries σ k) (List.ofFn fun i => f (e i)) := by
  first | exact @GlobalTheory.isWeaklyRegular_mvPowerSeries_of_pow_le | exact GlobalTheory.isWeaklyRegular_mvPowerSeries_of_pow_le | (intros; apply GlobalTheory.isWeaklyRegular_mvPowerSeries_of_pow_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FlatMvPowerSeriesOfIsNoetherianRing
section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FlatMvPowerSeries
open MvPowerSeries IsLocalRing
open scoped TensorProduct

namespace GlobalTheory.PowerSeriesFlat

theorem flat_pi (T : Type*) [CommRing T] [IsNoetherianRing T] (ι : Type*) :
    Module.Flat T (ι → T) := by
  apply Module.Flat.of_forall_isTrivialRelation
  intro l f x h
  let φ : (Fin l → T) →ₗ[T] T := Fintype.linearCombination T f
  have hφ : ∀ v : Fin l → T, φ v = ∑ i, f i * v i := by
    intro v
    simp [φ, Fintype.linearCombination_apply, mul_comm]
  have hfg : (LinearMap.ker φ).FG := IsNoetherian.noetherian _
  obtain ⟨k, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hfg
  have hx : ∀ t : ι, ∃ c : Fin k → T, ∑ j, c j • s j = fun i => x i t := by
    intro t
    have hm : (fun i => x i t) ∈ LinearMap.ker φ := by
      rw [LinearMap.mem_ker, hφ]
      have := congrFun h t
      simpa [Finset.sum_apply] using this
    rw [← hs] at hm
    exact (Submodule.mem_span_range_iff_exists_fun T).1 hm
  choose c hc using hx
  refine ⟨k, fun i j => s j i, fun j t => c t j, ?_, ?_⟩
  · intro i
    funext t
    have := congrFun (hc t) i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    rw [← this]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  · intro j
    have hm : s j ∈ LinearMap.ker φ := by
      rw [← hs]
      exact Submodule.subset_span ⟨j, rfl⟩
    rwa [LinearMap.mem_ker, hφ] at hm

theorem flat_mvPowerSeries :
    ∀ (T : Type) [CommRing T] [IsNoetherianRing T] (σ : Type),
      Module.Flat T (MvPowerSeries σ T) :=
  fun T _ _ σ => flat_pi T (σ →₀ ℕ)

end GlobalTheory.PowerSeriesFlat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FlatMvPowerSeriesOfIsNoetherianRing
open IsLocalRing TensorProduct

namespace GlobalTheory.FiniteHeight

theorem flat_mvPowerSeries_of_isNoetherianRing :
    ∀ (T : Type) [CommRing T] [IsNoetherianRing T] (σ : Type),
      Module.Flat T (MvPowerSeries σ T) :=
  GlobalTheory.PowerSeriesFlat.flat_mvPowerSeries

end GlobalTheory.FiniteHeight
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FlatMvPowerSeriesOfIsNoetherianRingStatement
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.module_flat_mvPowerSeries_of_isNoetherianRing : ∀ (T : Type) [CommRing T] [IsNoetherianRing T] (σ : Type), Module.Flat T (MvPowerSeries σ T) := by
  first | exact @GlobalTheory.FiniteHeight.flat_mvPowerSeries_of_isNoetherianRing | exact GlobalTheory.FiniteHeight.flat_mvPowerSeries_of_isNoetherianRing | (intros; apply GlobalTheory.FiniteHeight.flat_mvPowerSeries_of_isNoetherianRing <;> assumption)
end
end

open IsLocalRing TensorProduct

namespace GlobalTheory.FiniteColength

theorem map_maximalIdeal_eq_ker_map_residue (T : Type) [CommRing T] [IsLocalRing T]
    [IsNoetherianRing T] (σ : Type) :
    (maximalIdeal T).map (algebraMap T (MvPowerSeries σ T)) =
      RingHom.ker (MvPowerSeries.map (σ := σ) (residue T)) := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change MvPowerSeries.map (residue T) (MvPowerSeries.C r) = 0
    rw [MvPowerSeries.map_C, (residue_eq_zero_iff r).2 hr, map_zero]
  · intro g hg
    refine GlobalTheory.FormalIsogeny.mem_map_C_of_coeff_mem (IsNoetherian.noetherian _) fun d => ?_
    rw [← residue_eq_zero_iff, ← MvPowerSeries.coeff_map, RingHom.mem_ker.1 hg, map_zero]

theorem free_finite_quotient : ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsNoetherianRing T], IsAdicComplete (maximalIdeal T) T → ∀ (σ : Type) [Finite σ] (n : ℕ) (e : Fin n ≃ σ) (f : Fin n → MvPowerSeries σ T), (∀ j, MvPowerSeries.constantCoeff (f j) = 0) → (∃ M : ℕ, Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ (ResidueField T))) ^ M ≤ Ideal.span (Set.range fun j => MvPowerSeries.map (residue T) (f j))) → Module.Free T (MvPowerSeries σ T ⧸ Ideal.span (Set.range f)) ∧ Module.Finite T (MvPowerSeries σ T ⧸ Ideal.span (Set.range f)) := by
  intro T _ _ _ hc σ _ n e f h0 hM
  have hfin : Module.Finite T (MvPowerSeries σ T ⧸ Ideal.span (Set.range f)) :=
    (GlobalTheory.FormalIsogeny.finiteReduction_iff.2 hM).finite_quotient
  refine ⟨?_, hfin⟩
  haveI : Module.Flat T (MvPowerSeries σ T) := GlobalTheory.T.module_flat_mvPowerSeries_of_isNoetherianRing T σ
  haveI : IsLocalHom (algebraMap T (MvPowerSeries σ T)) := ⟨fun r hr => by
    have := MvPowerSeries.isUnit_iff_constantCoeff.1 hr
    exact this⟩
  have hreg := GlobalTheory.T.isWeaklyRegular_mvPowerSeries_of_finite_colength (ResidueField T) σ n e
    (fun s => MvPowerSeries.map (residue T) (f (e.symm s)))
    (fun s => by rw [MvPowerSeries.constantCoeff_map, h0, map_zero])
    (by
      have : (Set.range fun s => MvPowerSeries.map (σ := σ) (residue T) (f (e.symm s))) =
          Set.range fun j => MvPowerSeries.map (σ := σ) (residue T) (f j) :=
        e.symm.surjective.range_comp fun j => MvPowerSeries.map (σ := σ) (residue T) (f j)
      rw [this]; exact hM)
  simp only [Equiv.symm_apply_apply] at hreg
  let φ : (MvPowerSeries σ T ⧸ (maximalIdeal T).map (algebraMap T (MvPowerSeries σ T))) ≃+*
      MvPowerSeries σ (ResidueField T) :=
    (Ideal.quotEquivOfEq (map_maximalIdeal_eq_ker_map_residue T σ)).trans
      (RingHom.quotientKerEquivOfSurjective
        (GlobalTheory.FormalIsogeny.map_surjective_of_surjective (σ := σ) (residue_surjective (R := T))))
  have hφ : ∀ g, φ (Ideal.Quotient.mk _ g) = MvPowerSeries.map (residue T) g := fun g => rfl
  have hreg' : RingTheory.Sequence.IsWeaklyRegular
      (MvPowerSeries σ T ⧸ (maximalIdeal T).map (algebraMap T (MvPowerSeries σ T)))
      (List.ofFn f) := by
    refine (AddEquiv.isWeaklyRegular_congr (e := φ.toAddEquiv) ?_).2 hreg
    have : (List.ofFn fun i => MvPowerSeries.map (σ := σ) (residue T) (f i)) =
        (List.ofFn f).map (MvPowerSeries.map (σ := σ) (residue T)) := by
      rw [List.map_ofFn]; rfl
    rw [this, List.forall₂_map_right_iff, List.forall₂_same]
    intro r _ x
    change φ (Ideal.Quotient.mk _ r * x) = _ * φ x
    rw [map_mul, hφ]
  have hflat := GlobalTheory.T.flat_quotient_weakly_regular T (MvPowerSeries σ T) (List.ofFn f) (fun r hr => by
    obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hr
    rw [mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff, h0]
    exact not_isUnit_zero) hreg'
  have hI : Ideal.ofList (List.ofFn f) = Ideal.span (Set.range f) := by
    unfold Ideal.ofList
    congr 1
    ext r
    exact List.mem_ofFn' _ _
  rw [hI] at hflat
  exact Module.free_of_flat_of_isLocalRing

end GlobalTheory.FiniteColength
