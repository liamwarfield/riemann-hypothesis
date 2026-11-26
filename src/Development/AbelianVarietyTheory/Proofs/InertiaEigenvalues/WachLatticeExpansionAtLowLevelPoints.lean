module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralWittLatticeBasis
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeEqFiltrationSumAtLevel
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachWeierstrassTestAndDensity

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExpansionsLowAndPullbackRecord
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExpansionsLowAndPullback
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

namespace GlobalTheory.NL.LowLevel

section Series

variable {LL M : Type} [Field LL] [AddCommGroup M] [Module LL M]

theorem conv_one (f : ℤ → M) : conv (1 : PowerSeries LL) f = f := by
  funext k
  unfold conv
  rw [finsum_eq_single _ 0]
  · simp
  · intro j hj
    simp [PowerSeries.coeff_one, hj]

theorem mem_latSpan {ι : Type} (e : ι → ℤ → M) (x : ι) : e x ∈ latSpan (LL := LL) e :=
  Submodule.subset_span ⟨1, x, (conv_one _).symm⟩

theorem neg_eq_zero {ι : Type} {e : ι → ℤ → M} {D : Submodule LL M} (h : Std D (latSpan e))
    (x : ι) (k : ℤ) (hk : k < 0) : e x k = 0 :=
  ((h _).1 (mem_latSpan e x)).2 k hk

theorem span_const {ι : Type} {e : ι → ℤ → M} {D : Submodule LL M} (h : Std D (latSpan e)) :
    Submodule.span LL (Set.range fun x => e x 0) = D := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact ((h _).1 (mem_latSpan e x)).1 0
  · intro d hd
    have key : ∀ f ∈ latSpan (LL := LL) e, f 0 ∈ Submodule.span LL (Set.range fun x => e x 0) := by
      intro f hf
      induction hf using Submodule.span_induction with
      | mem f hf =>
        obtain ⟨a, x, rfl⟩ := hf
        unfold conv
        rw [finsum_eq_single _ 0]
        · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, ?_⟩)
          simp
        · intro j hj
          rw [neg_eq_zero h x _ (by omega), smul_zero]
      | zero => exact Submodule.zero_mem _
      | add f g _ _ hf hg => exact Submodule.add_mem _ hf hg
      | smul c f _ hf => exact Submodule.smul_mem _ c hf
    have hmem : (Pi.single (0 : ℤ) d : ℤ → M) ∈ latSpan (LL := LL) e := by
      refine (h _).2 ⟨fun k => ?_, fun k hk => Pi.single_eq_of_ne hk.ne _⟩
      by_cases hk : k = 0
      · subst hk
        simpa using hd
      · rw [Pi.single_eq_of_ne hk]
        exact D.zero_mem
    simpa using key _ hmem

theorem span_const_map {M' ι : Type} [AddCommGroup M'] [Module LL M'] {e : ι → ℤ → M}
    {D : Submodule LL M} (h : Std D (latSpan e)) (L : M →ₗ[LL] M') (g : ι → M')
    (hg : ∀ x, g x = L (e x 0)) : Submodule.span LL (Set.range g) = D.map L := by
  rw [← span_const h, Submodule.map_span, ← Set.range_comp]
  congr 2
  funext x
  exact hg x

theorem conv_low (w : PowerSeries LL) (k : ℕ) (f : ℤ → M) (hf : ∀ j < 0, f j = 0) (j : ℤ)
    (hj : j < k) : conv ((PowerSeries.X * w) ^ k) f j = 0 := by
  unfold conv
  apply finsum_eq_zero_of_forall_eq_zero
  intro m
  by_cases hm : m < k
  · rw [mul_pow, PowerSeries.coeff_X_pow_mul', if_neg (by omega), zero_smul]
  · rw [hf _ (by omega), smul_zero]

theorem conv_lead (w : PowerSeries LL) (k : ℕ) (f : ℤ → M) (hf : ∀ j < 0, f j = 0) :
    conv ((PowerSeries.X * w) ^ k) f k = PowerSeries.constantCoeff w ^ k • f 0 := by
  unfold conv
  rw [finsum_eq_single _ k]
  · rw [mul_pow, PowerSeries.coeff_X_pow_mul', if_pos le_rfl]
    simp
  · intro m hmk
    by_cases hm : m < k
    · rw [mul_pow, PowerSeries.coeff_X_pow_mul', if_neg (by omega), zero_smul]
    · rw [hf _ (by omega), smul_zero]

theorem pullback_span {M' ι : Type} [AddCommGroup M'] [Module LL M'] {P : ι → ℕ → Prop}
    (y : ∀ x k, P x k → ι) (lN : ι → ℤ → M') (e e' : ι → ℤ → M) {D D' : Submodule LL M}
    (L : M →ₗ[LL] M') (φ : M →ₗ[LL] M) (c : LL) (q : PowerSeries LL)
    (hq : ∃ w, IsUnit w ∧ q = PowerSeries.X * w)
    (hN : ∀ x k, lN x k = L (e x k)) (hmem : ∀ x k, e x k ∈ D) (hS : Std D' (latSpan e'))
    (hφ : ∀ x k hk j, e (y x k hk) j = conv (q ^ k) (fun j => c ^ j • φ (e' x j)) j)
    (hsurj : Set.SurjOn φ D' D) (hex : ∀ x, ∃ k, P x k) :
    (∀ x k hk (j : ℤ), lN (y x k hk) j ∈ D.map L ∧ (j < k → lN (y x k hk) j = 0)) ∧
      Submodule.span LL {z | ∃ x k hk, z = lN (y x k hk) (k : ℕ)} = D.map L := by
  obtain ⟨w, hw, rfl⟩ := hq
  have hm : ∀ x k, lN x k ∈ D.map L := fun x k => by
    rw [hN]
    exact Submodule.mem_map_of_mem (hmem x k)
  have hg0 : ∀ x, ∀ j < (0 : ℤ), c ^ j • φ (e' x j) = 0 := by
    intro x j hj
    rw [neg_eq_zero hS x j hj, map_zero, smul_zero]
  have hc : PowerSeries.constantCoeff w ≠ 0 := (hw.map PowerSeries.constantCoeff).ne_zero
  refine ⟨fun x k hk j => ⟨hm _ _, fun hj => ?_⟩, le_antisymm ?_ ?_⟩
  · rw [hN, hφ, conv_low w k _ (hg0 x) j hj, map_zero]
  · rw [Submodule.span_le]
    rintro _ ⟨x, k, hk, rfl⟩
    exact hm _ _
  · rintro _ ⟨d, hd, rfl⟩
    obtain ⟨d', hd', rfl⟩ := hsurj hd
    have hd'' : d' ∈ Submodule.span LL (Set.range fun x => e' x 0) := by
      rw [span_const hS]
      exact hd'
    clear hd hd'
    induction hd'' using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨x, rfl⟩ := hz
      obtain ⟨k, hk⟩ := hex x
      have h2 : L (φ (e' x 0)) = (PowerSeries.constantCoeff w ^ k)⁻¹ • lN (y x k hk) k := by
        rw [hN, hφ, conv_lead w k _ (hg0 x), map_smul, inv_smul_smul₀ (pow_ne_zero _ hc)]
        simp only [zpow_zero, one_smul]
      rw [h2]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, k, hk, rfl⟩)
    | zero => simp
    | add a b _ _ ha hb =>
      rw [map_add (f := _), map_add (f := _)]
      exact Submodule.add_mem _ ha hb
    | smul c a _ ha =>
      rw [map_smul, map_smul]
      exact Submodule.smul_mem _ c ha

theorem low_span {M' ι : Type} [AddCommGroup M'] [Module LL M'] (a : ι → ι) (lN : ι → ℤ → M')
    (e : ι → ℤ → M) {D : Submodule LL M} (L : M →ₗ[LL] M') (q : PowerSeries LL) (hq : q = 1)
    (ha : ∀ x k, lN (a x) k = conv q (lN x) k)
    (hN : ∀ x k, lN x k = L (e x k)) (hS : Std D (latSpan e)) :
    (∀ x (k : ℤ), lN (a x) k ∈ D.map L ∧ (k < 0 → lN x k = 0)) ∧
      Submodule.span LL (Set.range fun x => lN (a x) 0) = D.map L := by
  subst hq
  simp only [conv_one] at ha
  refine ⟨fun x k => ⟨?_, fun hk => ?_⟩, span_const_map hS L _ fun x => by rw [ha, hN]⟩
  · rw [hN]
    exact Submodule.mem_map_of_mem (((hS _).1 (mem_latSpan e _)).1 k)
  · rw [hN, neg_eq_zero hS x k hk, map_zero]

end Series

theorem exists_primitive {L : Type} [Field L] {l : ℕ} (hl : l.Prime) {ζ : L} {m : ℕ}
    (h : ζ ^ (l ^ m) = 1) : ∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j) := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hl).1 (orderOf_dvd_of_pow_eq_one h)
  exact ⟨j, hj ▸ IsPrimitiveRoot.orderOf ζ⟩

theorem pow_pow_pred {L : Type} [Field L] {l s : ℕ} (hs : 1 ≤ s) {ζ : L}
    (h : IsPrimitiveRoot ζ (l ^ s)) : (ζ ^ l) ^ (l ^ (s - 1)) = 1 := by
  rw [← pow_mul, ← pow_succ', Nat.sub_add_cancel hs]
  exact h.pow_eq_one


set_option maxHeartbeats 1000000 in
theorem expansions_low_and_pullback : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → (∀ (i : Let K) (ζ : ↥LL.1), (∃ m : ℕ, ζ ^ (((D.loc l).PD K).p ^ m) = 1) → PowerSeries.constantCoeff (W.lev i ζ W.X) = 0 → (∀ (x : ↥(W.N T)) (k : ℤ), W.levN T i ζ ((letE i : AA K LL) • x) k ∈ (Di (HW l) h T i).map (ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V)) ∧ (k < 0 → W.levN T i ζ x k = 0)) ∧ Submodule.span ↥LL.1 (Set.range fun x : ↥(W.N T) => W.levN T i ζ ((letE i : AA K LL) • x) 0) = (Di (HW l) h T i).map (ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V))) ∧ ∀ (i : Let K) (ζ : ↥LL.1) τ, Pt (HW l) h i ζ τ → (∀ (x : ↥(W.N T)) (k : ℕ) (hk : W.Q ^ k • W.φD T x ∈ W.N T) (j : ℤ), W.levN T i ζ ⟨_, hk⟩ j ∈ (Di (HW l) h T i).map (ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V)) ∧ (j < k → W.levN T i ζ ⟨_, hk⟩ j = 0)) ∧ Submodule.span ↥LL.1 {w | ∃ (x : ↥(W.N T)) (k : ℕ) (hk : W.Q ^ k • W.φD T x ∈ W.N T), w = W.levN T i ζ ⟨_, hk⟩ k} = (Di (HW l) h T i).map (ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V)) := by
  intro D HW F Cm l _ K s LL h W E C T hT
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hstd : ∀ (i : Let K) (ζ : ↥LL.1), ζ ^ (l ^ (s - 1)) = 1 →
      Std (Di (HW l) h T i) (latSpan (ex C h T i ζ)) := GlobalTheory.T.wachLattice_expansions_std_below_level D HW F Cm l K s LL h T hT
  refine ⟨fun i ζ hζ hX => ?_, fun i ζ τ hτ => ?_⟩
  · have hm : ζ ^ (l ^ hζ.choose) = 1 := by
      have := hζ.choose_spec
      rwa [show ((D.loc l).PD K).p ^ hζ.choose = l ^ hζ.choose from congrArg (· ^ _) hp] at this
    have hl := GlobalTheory.NL.lev_at_root_of_unity D HW l K s LL h i ζ (exists_primitive Fact.out hm)
    exact low_span (fun x => (letE i : AA K LL) • x) (W.levN T i ζ) (ex C h T i ζ) _
      (W.lev i ζ (letE i)) hl.2.1 (W.levN_smul T i ζ (letE i))
      ((C.C K s LL h).tie.levN_eq T i ζ) (hstd i ζ (hl.2.2.2.2.1.1 hX))
  · have hprim : IsPrimitiveRoot ζ (l ^ s) :=
      ((GlobalTheory.NL.Points.points D HW l K s LL h).2.1 i ζ τ hτ).1
    have hl := GlobalTheory.NL.lev_at_root_of_unity D HW l K s LL h i ζ ⟨s, hprim⟩
    have hφ : ∀ (x : ↥(W.N T)) (k : ℕ) (hk : W.Q ^ k • W.φD T x ∈ W.N T) (j : ℤ),
        ex C h T i ζ ⟨_, hk⟩ j = conv ((W.lev i ζ W.Q) ^ k) (fun j => (l : ↥LL.1) ^ j •
          φVB ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) (ex C h T (i - 1) (ζ ^ l) x j)) j := by
      intro x k hk j
      have h1 := (C.C K s LL h).tie.levB_φ T hT i ζ ⟨s, by rw [hp]; exact hprim⟩ x k hk j
      rw [map_pow, hp] at h1
      exact h1
    exact pullback_span (P := fun (x : ↥(W.N T)) k => W.Q ^ k • W.φD T x ∈ W.N T)
      (fun _ _ hk => ⟨_, hk⟩) (W.levN T i ζ) (ex C h T i ζ) (ex C h T (i - 1) (ζ ^ l)) _ _ _ _
      (hl.2.2.2.1 hprim).1 ((C.C K s LL h).tie.levN_eq T i ζ) ((C.C K s LL h).tie.levB_mem T i ζ)
      (hstd (i - 1) (ζ ^ l) (pow_pow_pred h.1 hprim)) hφ
      ((GlobalTheory.T.crystallineFrobenius_bijOn_letters_directSum D HW l K s LL h T hT).1 i).surjOn (fun x => W.N_φ T x x.2)

end GlobalTheory.NL.LowLevel
end

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.LowLevel


set_option maxHeartbeats 1000000 in
theorem expansions_low_and_pullback_record : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → (∀ (i : Let K) (ζ : ↥LL.1), (∃ m : ℕ, ζ ^ (((D.loc l).PD K).p ^ m) = 1) → PowerSeries.constantCoeff (W.lev i ζ W.X) = 0 → (∀ (x : ↥(W.N T)) (k : ℤ), W.levN T i ζ ((letE i : AA K LL) • x) k ∈ ιDi W T i ∧ (k < 0 → W.levN T i ζ x k = 0)) ∧ Submodule.span ↥LL.1 (Set.range fun x : ↥(W.N T) => W.levN T i ζ ((letE i : AA K LL) • x) 0) = ιDi W T i) ∧ ∀ (i : Let K) (ζ : ↥LL.1) τ, ptK D.loc HW h i ζ τ → (∀ (x : ↥(W.N T)) (k : ℕ) (hk : W.Q ^ k • W.φD T x ∈ W.N T) (j : ℤ), W.levN T i ζ ⟨_, hk⟩ j ∈ ιDi W T i ∧ (j < k → W.levN T i ζ ⟨_, hk⟩ j = 0)) ∧ Submodule.span ↥LL.1 {w | ∃ (x : ↥(W.N T)) (k : ℕ) (hk : W.Q ^ k • W.φD T x ∈ W.N T), w = W.levN T i ζ ⟨_, hk⟩ k} = ιDi W T i :=
  expansions_low_and_pullback

end GlobalTheory.NL.LowLevel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeExpansionAtLowLevelPoints
noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.LatLevel

section Series

variable {LL M : Type} [Field LL] [AddCommGroup M] [Module LL M]

theorem conv_smul (c : LL) (e : PowerSeries LL) (f : ℤ → M) : conv (c • e) f = c • conv e f := by
  funext k
  unfold conv
  simp only [Pi.smul_apply, map_smul, smul_eq_mul, mul_smul]
  rw [smul_finsum]

theorem conv_congr (e e' : PowerSeries LL) (f : ℤ → M) (a m : ℕ)
    (hf : ∀ r : ℤ, r < -(a : ℤ) → f r = 0) (hd : PowerSeries.X ^ m ∣ e - e') (r : ℤ)
    (hr : r < (m : ℤ) - a) : conv e f r = conv e' f r := by
  by_cases h : r < -(a : ℤ)
  · rw [LatFil.conv_vanish e f _ hf r h, LatFil.conv_vanish e' f _ hf r h]
  · obtain ⟨q, rfl⟩ : ∃ q : ℕ, r = (q : ℤ) - a := ⟨(r + a).toNat, by omega⟩
    rw [LatFil.conv_eq_sum e f a hf, LatFil.conv_eq_sum e' f a hf]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j < m := by have := Finset.mem_range.1 hj; omega
    have := (PowerSeries.X_pow_dvd_iff.1 hd) j hj'
    rw [map_sub, sub_eq_zero] at this
    rw [this]

theorem approx_step (bb c cc : LL) (e q : PowerSeries LL) (f : ℤ → M) (a m : ℕ)
    (hf : ∀ r : ℤ, r < -(a : ℤ) → f r = 0) (hd : PowerSeries.X ^ m ∣ PowerSeries.C c * q - e)
    (hcc : bb * c = cc) (r : ℤ) (hr : r < (m : ℤ) - a) : bb • conv e f r = conv (PowerSeries.C cc * q) f r := by
  subst hcc
  have h1 : bb • conv e f r = conv (PowerSeries.C bb * e) f r := by
    rw [← PowerSeries.smul_eq_C_mul, conv_smul]
    rfl
  rw [h1]
  refine conv_congr _ _ f a m hf ?_ r hr
  have h2 : PowerSeries.C bb * e - PowerSeries.C (bb * c) * q = -(PowerSeries.C bb * (PowerSeries.C c * q - e)) := by
    rw [map_mul]
    ring
  rw [h2, dvd_neg]
  exact Dvd.dvd.mul_left hd _

end Series

end GlobalTheory.NL.LatLevel

namespace GlobalTheory.NL.LatLevel


set_option maxHeartbeats 20000000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem lattice_at_level : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F), P4 D HW F Cm := by
  intro D HW F Cm l _ K s LL h T hT
  have hP4a := GlobalTheory.NL.LowLevel.expansions_low_and_pullback_record D HW F Cm l K s LL h T hT
  unfold p4
  refine ⟨hP4a.1, fun i ζ τ hpt => ⟨hP4a.2 i ζ τ hpt, ?_, ?_⟩⟩
  · intro x k
    have hmem : ex (Cm l) h T i ζ ((letE i : AA K LL) • x) ∈ Lat (Cm l) h T i ζ :=
      Submodule.subset_span ⟨1, _, (LowLevel.conv_one _).symm⟩
    have hk := ((LatFil.lat_eq_fil D HW F Cm l K s LL h T hT i ζ τ hpt _).1 hmem).2 k
    rw [((Cm l).C K s LL h).tie.levN_eq]
    exact ⟨Submodule.mem_map_of_mem hk.1, hk.2⟩
  · intro k w hw
    obtain ⟨hprim, hτ, ι, hcomp⟩ := (GlobalTheory.NL.Points.points D HW l K s LL h).2.1 i ζ τ hpt
    have hC := GlobalTheory.NL.CompD.component D HW l K s LL h T hT i ζ τ ι hcomp hτ
    have hw' : w ∈ DdRE ((D.loc l).PD K) T.ρ τ ⊓ FilV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) (-k) := hw
    obtain ⟨d, hd, hdw⟩ := hC.2.2.1 w (Submodule.mem_inf.1 hw').1
    have hdF : ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) d ∈ FilAt ((D.loc l).PD K) T τ (-k) := by
      have e1 : ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) d =
          w + (ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) d - w) := by abel
      rw [e1]
      exact Submodule.add_mem_sup hw hdw
    have hlat := LatFil.lat_eq_fil D HW F Cm l K s LL h T hT i ζ τ hpt
    have hsingle : (Pi.single k d : ℤ → T.V ⊗[ℚ_[l]] (D.loc l).R.B) ∈ Lat (Cm l) h T i ζ := by
      refine (hlat _).2 ⟨⟨k, fun r hr => Pi.single_eq_of_ne hr.ne _⟩, fun r => ?_⟩
      by_cases hr : r = k
      · subst hr
        simp only [Pi.single_eq_same]
        exact ⟨hd, hdF⟩
      · rw [Pi.single_eq_of_ne hr, map_zero]
        exact ⟨zero_mem _, zero_mem _⟩
    have hfull := GlobalTheory.T.wach_expansions_span_full_lattice D HW F Cm l K s LL h T hT i ζ hprim
    obtain ⟨nb⟩ := @GlobalTheory.NL.N_basis D HW F l _ K s LL h T hT
    have hli := GlobalTheory.T.wachExpansion_basis_divisibility D HW F Cm l K s LL h T hT i ζ ⟨s, hprim⟩ hfull
    obtain ⟨e, he⟩ := (hli.2 _ nb).2.1 _ hsingle
    obtain ⟨a₀, ha₀⟩ : ∃ a₀ : ℕ, ∀ j, ∀ r : ℤ, r < -(a₀ : ℤ) → ex (Cm l) h T i ζ (nb j) r = 0 := by
      choose m hm using fun j => ((Cm l).C K s LL h).tie.levB_supp T i ζ (nb j)
      refine ⟨∑ j, (-m j).toNat, fun j r hr => hm _ _ ?_⟩
      have := Finset.single_le_sum (f := fun j => (-m j).toNat) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ j)
      omega
    obtain ⟨m, hm⟩ : ∃ m : ℕ, k < (m : ℤ) - a₀ := ⟨(k + a₀ + 1).toNat, by omega⟩
    have hwd := (GlobalTheory.NL.WDiv.weierstrass_dense D HW l K s LL h).2.2.2 i ζ hprim
    choose a c hc0 hca _ using fun j => hwd (e j) m
    have t1 : ∀ j, c j • ((HW l).W K s LL h).lev i ζ (a j) =
        PowerSeries.C (c j) * ((HW l).W K s LL h).lev i ζ (a j) := fun j => PowerSeries.smul_eq_C_mul _ _
    have hca' : ∀ j, PowerSeries.X ^ m ∣ PowerSeries.C (c j) * ((HW l).W K s LL h).lev i ζ (a j) - e j :=
      fun j => by rw [← t1 j]; exact hca j
    haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
    haveI : IsFractionRing ↥(OL LL) ↥LL.1 :=
      integralClosure.isFractionRing_of_finite_extension ℚ_[l] ↥LL.1
    obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors ↥(OL LL))
      (Finset.univ : Finset (Fin _)) c
    choose o ho using fun j => hb j (Finset.mem_univ j)
    have ho' : ∀ j, algebraMap ↥(OL LL) ↥LL.1 (b : ↥(OL LL)) * c j = algebraMap ↥(OL LL) ↥LL.1 (o j) :=
      fun j => (Algebra.smul_def _ _).symm.trans (ho j).symm
    have hb0 : algebraMap ↥(OL LL) ↥LL.1 (b : ↥(OL LL)) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
    let x : ↥(((HW l).W K s LL h).N T) := ∑ j, (algebraMap ↥(OL LL) (AA K LL) (o j) * a j) • nb j
    have hx : ∀ r, ex (Cm l) h T i ζ x r =
        ∑ j, conv (((HW l).W K s LL h).lev i ζ (algebraMap ↥(OL LL) (AA K LL) (o j) * a j)) (ex (Cm l) h T i ζ (nb j)) r := by
      intro r
      show ((Cm l).C K s LL h).tie.levB T i ζ (∑ j, (algebraMap ↥(OL LL) (AA K LL) (o j) * a j) • nb j) r = _
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      exact congrFun (hli.1 _ _) r
    have hkey : ∀ r : ℤ, r < (m : ℤ) - a₀ →
        algebraMap ↥(OL LL) ↥LL.1 (b : ↥(OL LL)) • (Pi.single k d : ℤ → T.V ⊗[ℚ_[l]] (D.loc l).R.B) r =
          ex (Cm l) h T i ζ x r := by
      intro r hr
      rw [he, hx, Finset.sum_apply]
      refine Finset.smul_sum.trans (Finset.sum_congr rfl fun j _ => ?_)
      have hlev : ((HW l).W K s LL h).lev i ζ (algebraMap ↥(OL LL) (AA K LL) (o j) * a j) =
          PowerSeries.C (algebraMap ↥(OL LL) ↥LL.1 (o j)) * ((HW l).W K s LL h).lev i ζ (a j) := by
        letI : Algebra ↥(OL LL) (PowerSeries ↥LL.1) := MvPowerSeries.instAlgebra
        have hcom := (((HW l).W K s LL h).lev i ζ).commutes (o j)
        rw [map_mul, hcom, PowerSeries.algebraMap_apply]
      exact (approx_step (algebraMap ↥(OL LL) ↥LL.1 (b : ↥(OL LL))) (c j) _ (e j)
        (((HW l).W K s LL h).lev i ζ (a j)) (ex (Cm l) h T i ζ (nb j)) a₀ m (ha₀ j) (hca' j) (ho' j) r hr).trans
        (congrArg (fun p => conv p (ex (Cm l) h T i ζ (nb j)) r) hlev.symm)
    have hl1 := (GlobalTheory.NL.lev_at_root_of_unity D HW l K s LL h i ζ ⟨s, hprim⟩).2.1
    have hN1 : ∀ j, ((HW l).W K s LL h).levN T i ζ ((letE i : AA K LL) • x) j =
        ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) (ex (Cm l) h T i ζ x j) := by
      intro j
      rw [((HW l).W K s LL h).levN_smul, hl1]
      exact (congrFun (LowLevel.conv_one (((HW l).W K s LL h).levN T i ζ x)) j).trans
        (((Cm l).C K s LL h).tie.levN_eq T i ζ x j)
    have hc : ∀ j, j ≤ k → (algebraMap ↥(OL LL) ↥LL.1 (b : ↥(OL LL)))⁻¹ •
        ((HW l).W K s LL h).levN T i ζ ((letE i : AA K LL) • x) j =
          ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V)
            ((Pi.single k d : ℤ → T.V ⊗[ℚ_[l]] (D.loc l).R.B) j) := by
      intro j hj
      rw [hN1, ← map_smul, ← hkey j (by omega), inv_smul_smul₀ hb0]
    refine ⟨x, (algebraMap ↥(OL LL) ↥LL.1 (b : ↥(OL LL)))⁻¹, inv_ne_zero hb0, fun j hj => ?_, ?_⟩
    · rw [hc j hj.le, Pi.single_eq_of_ne hj.ne, map_zero]
      exact zero_mem _
    · rw [hc k le_rfl, Pi.single_eq_same]
      exact Submodule.mem_sup_right hdw

end GlobalTheory.NL.LatLevel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeExpansionAtLowLevelPointsStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wach_lattice_expansion_at_low_level_points : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), P4 D HW F Cm := by
  first | exact @GlobalTheory.NL.LatLevel.lattice_at_level | exact GlobalTheory.NL.LatLevel.lattice_at_level | (intros; apply GlobalTheory.NL.LatLevel.lattice_at_level <;> assumption)
end
