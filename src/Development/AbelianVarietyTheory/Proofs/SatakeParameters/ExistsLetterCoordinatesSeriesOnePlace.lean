module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdjointSubstLogarithmsIntoParametersOfLogExponen
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrobeniusMapSubstPair
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DifferentiableSumU

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SubstSumCMul
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU GlobalTheory.OnePlace Classical

noncomputable section

namespace GlobalTheory.OnePlace.Ident

open MvPowerSeries

variable {p : ℕ} [Fact p.Prime]

theorem pow_wToC (σ : ℂ_[p] →+* ℂ_[p]) (hσ : ∀ w : FormalGroupSystem.WW p, σ (Formalism.L2.G.Pend.wToC p w) = Formalism.L2.G.Pend.wToC p (sigW p w))
    (k : ℕ) (w : FormalGroupSystem.WW p) : (σ ^ k) (Formalism.L2.G.Pend.wToC p w) = Formalism.L2.G.Pend.wToC p ((sigW p)^[k] w) := by
  have h : Function.Semiconj (Formalism.L2.G.Pend.wToC p) (sigW p) σ := fun w => (hσ w).symm
  rw [RingHom.coe_pow]
  exact (h.iterate_right k w).symm

theorem comb {κ ι ρ : Type} [Fintype ρ] (S : Finset ι) (a : ι → ℂ_[p]) (b : ι → ρ → ℂ_[p])
    (L : ρ → MvPowerSeries κ ℂ_[p]) (r : ρ) (h : ∀ r', ∑ i ∈ S, a i * b i r' = if r' = r then 1 else 0) :
    ∑ i ∈ S, C (a i) * ∑ r', C (b i r') * L r' = L r := by
  simp_rw [Finset.mul_sum, ← mul_assoc, ← map_mul]
  rw [Finset.sum_comm]
  set_option synthInstance.maxHeartbeats 100000 in
    simp_rw [← Finset.sum_mul, ← map_sum, h]
  simp

theorem sum_even {M : Type} [AddCommMonoid M] {n' : ℕ} (he : Even n') (g : ℕ → M) :
    ∑ s ∈ Finset.univ.filter (fun s : Fin n' => ¬ IsOddPos s), g s.val = ∑ i ∈ Finset.range (n' / 2), g (2 * i) := by
  obtain ⟨m, rfl⟩ := he
  refine Finset.sum_bij' (fun s _ => s.val / 2) (fun i hi => ⟨2 * i, by simp at hi; omega⟩) ?_ ?_ ?_ ?_ ?_
  · intro s hs; simp [IsOddPos] at hs ⊢; omega
  · intro i hi; simp [IsOddPos]
  · intro s hs; simp [IsOddPos] at hs; ext; simp; omega
  · intro i hi; simp
  · intro s hs; simp [IsOddPos] at hs; congr 1; omega

theorem sum_odd {M : Type} [AddCommMonoid M] {n' : ℕ} (he : Even n') (g : ℕ → M) :
    ∑ s ∈ Finset.univ.filter (fun s : Fin n' => IsOddPos s), g s.val = ∑ i ∈ Finset.range (n' / 2), g (2 * i + 1) := by
  obtain ⟨m, rfl⟩ := he
  have hm : (m + m) / 2 = m := by omega
  refine Finset.sum_bij' (fun s _ => s.val / 2) (fun i hi => ⟨2 * i + 1, by rw [Finset.mem_range, hm] at hi; omega⟩)
    ?_ ?_ ?_ ?_ ?_
  · intro s hs; have := s.isLt; rw [Finset.mem_range, hm]; omega
  · intro i hi; refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩; show (2 * i + 1) % 2 = 1; omega
  · intro s hs; have h2 : s.val % 2 = 1 := (Finset.mem_filter.mp hs).2; ext; show 2 * (s.val / 2) + 1 = s.val; omega
  · intro i hi; show (2 * i + 1) / 2 = i; omega
  · intro s hs; have h2 : s.val % 2 = 1 := (Finset.mem_filter.mp hs).2; congr 1; omega

end GlobalTheory.OnePlace.Ident

namespace GlobalTheory.OnePlace.Ident

open MvPowerSeries

variable {p : ℕ} [Fact p.Prime]

theorem eq_subst_subst {n' : ℕ} [NeZero n'] (t : ZMod n' → MvPowerSeries (Fin (n' / 2) ⊕ Fin (n' / 2)) ℂ_[p])
    (x : Fin (n' / 2) ⊕ Fin (n' / 2) → MvPowerSeries (ZMod n') ℂ_[p]) (ht0 : ∀ s, constantCoeff (t s) = 0)
    (hx0 : ∀ r, constantCoeff (x r) = 0) (hxt : ∀ s, subst x (t s) = X s) (f : MvPowerSeries (ZMod n') ℂ_[p]) :
    f = subst x (subst t f) := by
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero ht0) (hasSubst_of_constantCoeff_zero hx0),
    show (fun s => subst x (t s)) = X from funext hxt, subst_self]
  rfl

theorem subst_sum_C_mul {κ τ ι : Type} (x : κ → MvPowerSeries τ ℂ_[p]) (hx : HasSubst x) (S : Finset ι)
    (c : ι → ℂ_[p]) (f : ι → MvPowerSeries κ ℂ_[p]) :
    subst x (∑ i ∈ S, C (c i) * f i) = ∑ i ∈ S, C (c i) * subst x (f i) := by
  rw [← coe_substAlgHom hx]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, coe_substAlgHom, subst_C]

theorem subst_lg {κ τ : Type} [Finite κ] (x : κ → MvPowerSeries τ ℂ_[p]) (hx0 : ∀ r, constantCoeff (x r) = 0) (k : κ) :
    subst x (GlobalTheory.ThBe0.lg (l := p) k) = PowerSeries.subst (x k) (Formalism.MainNotions.GL3Theta.logF p) := by
  have hx := hasSubst_of_constantCoeff_zero hx0
  rw [GlobalTheory.ThBe0.lg, GlobalTheory.BeProps.subst_psubst hx (constantCoeff_X k), subst_X hx]

theorem hasSubst_jetZ (n' r0 r1 : ℕ) [NeZero n'] : HasSubst (jetZ p n' r0 r1) :=
  hasSubst_of_constantCoeff_zero fun z => by
    rw [jetZ, ← GlobalTheory.BiextInhab.bridge]
    exact GlobalTheory.BeProps.constantCoeff_laAt _ _

theorem hasSubst_copy {n' r0 r1 : ℕ} [NeZero n'] (a : Fin r0) (b : Fin r1) :
    HasSubst (fun u : ZMod n' => (X (u, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p])) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

theorem subst_jetZ_lin {n' r0 r1 : ℕ} [NeZero n'] (S : Finset (Fin n')) (c : Fin n' → ℂ_[p]) (a : Fin r0) (b : Fin r1) :
    subst (jetZ p n' r0 r1) (∑ s ∈ S, C (c s) * (X (s, a, b) : MvPowerSeries (Zidx n' r0 r1) ℂ_[p])) =
      subst (fun u : ZMod n' => (X (u, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p]))
        (∑ s ∈ S, C (c s) * GlobalTheory.ThStr.laS p n' ((s.val : ℕ) : ZMod n')) := by
  rw [subst_sum_C_mul _ (hasSubst_jetZ n' r0 r1), subst_sum_C_mul _ (hasSubst_copy a b)]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [subst_X (hasSubst_jetZ n' r0 r1), jetZ, ← GlobalTheory.BiextInhab.bridge]
  rfl

end GlobalTheory.OnePlace.Ident

namespace GlobalTheory.OnePlace.Ident

open MvPowerSeries

theorem zOm_even (p : ℕ) [Fact p.Prime] (σ : ℂ_[p] →+* ℂ_[p]) {n' : ℕ} {ρ : Type} [Fintype ρ] (om om' : ρ → ℂ_[p])
    (k : ℕ) (hk : k < n') (he : Even k) :
    GlobalTheory.ThBe0.zOm σ (d := n') om om' ((k : ℕ) : ZMod n') =
      ∑ r, C ((σ ^ k) (om r)) * GlobalTheory.ThBe0.lg (l := p) (Sum.inl r : ρ ⊕ ρ) := by
  have hv : ((k : ℕ) : ZMod n').val = k := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hk]
  rw [GlobalTheory.ThBe0.zOm, hv, if_pos he]

theorem zOm_odd (p : ℕ) [Fact p.Prime] (σ : ℂ_[p] →+* ℂ_[p]) {n' : ℕ} {ρ : Type} [Fintype ρ] (om om' : ρ → ℂ_[p])
    (k : ℕ) (hk : k < n') (he : ¬ Even k) :
    GlobalTheory.ThBe0.zOm σ (d := n') om om' ((k : ℕ) : ZMod n') =
      ∑ r, C ((σ ^ k) (om' r)) * GlobalTheory.ThBe0.lg (l := p) (Sum.inr r : ρ ⊕ ρ) := by
  have hv : ((k : ℕ) : ZMod n').val = k := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hk]
  rw [GlobalTheory.ThBe0.zOm, hv, if_neg he]

theorem coordZ_jetZ : ∀ {p : ℕ} [Fact p.Prime] (σ : ℂ_[p] →+* ℂ_[p]), (∀ w : FormalGroupSystem.WW p, σ (Formalism.L2.G.Pend.wToC p w) = Formalism.L2.G.Pend.wToC p (sigW p w)) → ∀ {n' : ℕ} [NeZero n'], Even n' → ∀ (B : OmBasis p n'), GlobalTheory.ThBe0.DualOm σ n' (fun r => Formalism.L2.G.Pend.wToC p (B.om r)) (fun r => Formalism.L2.G.Pend.wToC p (B.omS r)) → ∀ (t : ZMod n' → MvPowerSeries (Fin (n' / 2) ⊕ Fin (n' / 2)) ℂ_[p]) (x : Fin (n' / 2) ⊕ Fin (n' / 2) → MvPowerSeries (ZMod n') ℂ_[p]), (∀ s, MvPowerSeries.constantCoeff (t s) = 0) → (∀ r, MvPowerSeries.constantCoeff (x r) = 0) → (∀ s, MvPowerSeries.subst t (GlobalTheory.ThStr.laS p n' s) = GlobalTheory.ThBe0.zOm σ (fun r => Formalism.L2.G.Pend.wToC p (B.om r)) (fun r => Formalism.L2.G.Pend.wToC p (B.omS r)) s) → (∀ s, MvPowerSeries.subst x (t s) = MvPowerSeries.X s) → ∀ (r0 r1 : ℕ) (i : Eidx n' r0 r1 ⊕ Eidx n' r0 r1), MvPowerSeries.subst (jetZ p n' r0 r1) (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (coordZ B (FormalGroupSystem.K0 p) 1 i)) = PowerSeries.subst (xiE x i) (Formalism.MainNotions.GL3Theta.logF p) := by
  intro p _ σ hσ n' _ he B hD t x ht0 hx0 ht hxt r0 r1 i
  have hx : HasSubst x := hasSubst_of_constantCoeff_zero hx0
  have key : ∀ s : ZMod n', GlobalTheory.ThStr.laS p n' s = subst x (GlobalTheory.ThBe0.zOm σ (fun r => Formalism.L2.G.Pend.wToC p (B.om r))
      (fun r => Formalism.L2.G.Pend.wToC p (B.omS r)) s) := fun s => by
    rw [← ht s]; exact eq_subst_subst t x ht0 hx0 hxt _
  rcases i with ⟨r, a, b⟩ | ⟨r, a, b⟩
  · have hm : MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (coordZ B (FormalGroupSystem.K0 p) 1 (Sum.inl (r, a, b))) =
        ∑ s ∈ Finset.univ.filter (fun s : Fin n' => ¬ IsOddPos s),
          C ((σ ^ s.val) (Formalism.L2.G.Pend.wToC p (B.omS r))) * (X (s, a, b) : MvPowerSeries (Zidx n' r0 r1) ℂ_[p]) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [coordZ, map_sum, map_mul, map_C, map_X, one_mul, Algebra.algebraMap_self, RingHom.id_apply, Formalism.L2.G.Pend.witt_fraction_to_Cp_algebraMap,
        pow_wToC σ hσ]
    rw [hm, subst_jetZ_lin]
    have hin : ∑ s ∈ Finset.univ.filter (fun s : Fin n' => ¬ IsOddPos s),
        C ((σ ^ s.val) (Formalism.L2.G.Pend.wToC p (B.omS r))) * GlobalTheory.ThStr.laS p n' ((s.val : ℕ) : ZMod n') =
        PowerSeries.subst (x (Sum.inl r)) (Formalism.MainNotions.GL3Theta.logF p) := by
      have e1 : ∀ s ∈ Finset.univ.filter (fun s : Fin n' => ¬ IsOddPos s),
          GlobalTheory.ThStr.laS p n' ((s.val : ℕ) : ZMod n') = ∑ r', C ((σ ^ s.val) (Formalism.L2.G.Pend.wToC p (B.om r'))) *
            PowerSeries.subst (x (Sum.inl r')) (Formalism.MainNotions.GL3Theta.logF p) := by
        intro s hs
        have hs2 : ¬ s.val % 2 = 1 := (Finset.mem_filter.mp hs).2
        rw [key, zOm_even p σ _ _ s.val s.isLt (Nat.even_iff.mpr (by omega)), subst_sum_C_mul _ hx]
        simp only [subst_lg x hx0]
      rw [Finset.sum_congr rfl fun s hs => by rw [e1 s hs]]
      refine comb _ _ _ _ r fun r' => ?_
      rw [sum_even he (fun k => (σ ^ k) (Formalism.L2.G.Pend.wToC p (B.omS r)) * (σ ^ k) (Formalism.L2.G.Pend.wToC p (B.om r')))]
      have hk : ∀ k : ℕ, (σ ^ k) (Formalism.L2.G.Pend.wToC p (B.omS r)) * (σ ^ k) (Formalism.L2.G.Pend.wToC p (B.om r')) =
          (σ ^ k) (Formalism.L2.G.Pend.wToC p (B.om r') * Formalism.L2.G.Pend.wToC p (B.omS r)) := fun k => by
        rw [map_mul, mul_comm]
      simp only [hk]
      rw [hD.dual r' r]
      by_cases h : r' = r <;> simp [h]
    rw [hin, GlobalTheory.BeProps.subst_psubst (hasSubst_copy a b) (hx0 _)]
    rfl
  · have hm : MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (coordZ B (FormalGroupSystem.K0 p) 1 (Sum.inr (r, a, b))) =
        ∑ s ∈ Finset.univ.filter (fun s : Fin n' => IsOddPos s),
          C ((σ ^ s.val) (Formalism.L2.G.Pend.wToC p (B.om r))) * (X (s, a, b) : MvPowerSeries (Zidx n' r0 r1) ℂ_[p]) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [coordZ, map_sum, map_mul, map_C, map_X, one_mul, Algebra.algebraMap_self, RingHom.id_apply, Formalism.L2.G.Pend.witt_fraction_to_Cp_algebraMap,
        pow_wToC σ hσ]
    rw [hm, subst_jetZ_lin]
    have hin : ∑ s ∈ Finset.univ.filter (fun s : Fin n' => IsOddPos s),
        C ((σ ^ s.val) (Formalism.L2.G.Pend.wToC p (B.om r))) * GlobalTheory.ThStr.laS p n' ((s.val : ℕ) : ZMod n') =
        PowerSeries.subst (x (Sum.inr r)) (Formalism.MainNotions.GL3Theta.logF p) := by
      have e1 : ∀ s ∈ Finset.univ.filter (fun s : Fin n' => IsOddPos s),
          GlobalTheory.ThStr.laS p n' ((s.val : ℕ) : ZMod n') = ∑ r', C ((σ ^ s.val) (Formalism.L2.G.Pend.wToC p (B.omS r'))) *
            PowerSeries.subst (x (Sum.inr r')) (Formalism.MainNotions.GL3Theta.logF p) := by
        intro s hs
        have hs2 : s.val % 2 = 1 := (Finset.mem_filter.mp hs).2
        rw [key, zOm_odd p σ _ _ s.val s.isLt (Nat.not_even_iff.mpr hs2), subst_sum_C_mul _ hx]
        simp only [subst_lg x hx0]
      rw [Finset.sum_congr rfl fun s hs => by rw [e1 s hs]]
      refine comb _ _ _ _ r fun r' => ?_
      rw [sum_odd he (fun k => (σ ^ k) (Formalism.L2.G.Pend.wToC p (B.om r)) * (σ ^ k) (Formalism.L2.G.Pend.wToC p (B.omS r')))]
      have hk : ∀ k : ℕ, (σ ^ (2 * k + 1)) (Formalism.L2.G.Pend.wToC p (B.om r)) * (σ ^ (2 * k + 1)) (Formalism.L2.G.Pend.wToC p (B.omS r')) =
          σ ((σ ^ (2 * k)) (Formalism.L2.G.Pend.wToC p (B.om r) * Formalism.L2.G.Pend.wToC p (B.omS r'))) := fun k => by
        rw [← map_mul, pow_succ']; rfl
      simp only [hk]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_sum, hD.dual r r']
      by_cases h : r = r' <;> simp [h, eq_comm]
    rw [hin, GlobalTheory.BeProps.subst_psubst (hasSubst_copy a b) (hx0 _)]
    rfl

end GlobalTheory.OnePlace.Ident
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoeffsWpSubst
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU GlobalTheory.OnePlace Classical

namespace GlobalTheory.OnePlace

open MvPowerSeries Formalism.MainNotions.GL3Theta

theorem coeffsWp_mul {τ : Type} {p : ℕ} [Fact p.Prime] {f g : MvPowerSeries τ ℂ_[p]}
    (hf : ∀ m, coeff m f ∈ Wp p) (hg : ∀ m, coeff m g ∈ Wp p) : ∀ m, coeff m (f * g) ∈ Wp p := by
  intro m
  rw [coeff_mul]
  exact Subring.sum_mem _ fun x _ => Subring.mul_mem _ (hf _) (hg _)

theorem coeffsWp_one {τ : Type} {p : ℕ} [Fact p.Prime] : ∀ m, coeff m (1 : MvPowerSeries τ ℂ_[p]) ∈ Wp p := by
  intro m
  rw [coeff_one]
  split_ifs
  · exact Subring.one_mem _
  · exact Subring.zero_mem _

theorem coeffsWp_pow {τ : Type} {p : ℕ} [Fact p.Prime] {f : MvPowerSeries τ ℂ_[p]}
    (hf : ∀ m, coeff m f ∈ Wp p) (k : ℕ) : ∀ m, coeff m (f ^ k) ∈ Wp p := by
  induction k with
  | zero => simpa using coeffsWp_one
  | succ k ih => rw [pow_succ]; exact coeffsWp_mul ih hf

theorem coeffsWp_subst {σ τ : Type} {p : ℕ} [Fact p.Prime] {a : σ → MvPowerSeries τ ℂ_[p]} (ha : HasSubst a)
    (hA : ∀ i m, coeff m (a i) ∈ Wp p) {f : MvPowerSeries σ ℂ_[p]} (hf : ∀ m, coeff m f ∈ Wp p) :
    ∀ m, coeff m (subst a f) ∈ Wp p := by
  intro e
  rw [coeff_subst ha]
  refine finsum_induction (fun w => w ∈ Wp p) (Subring.zero_mem _) (fun x y hx hy => Subring.add_mem _ hx hy) ?_
  intro d
  refine Subring.mul_mem _ (hf d) ?_
  have hP : ∀ m, coeff m (d.prod fun s k => a s ^ k) ∈ Wp p := by
    unfold Finsupp.prod
    induction d.support using Finset.induction_on with
    | empty => simpa using coeffsWp_one
    | insert i S hi ih => rw [Finset.prod_insert hi]; exact coeffsWp_mul (coeffsWp_pow (hA i) _) ih
  exact hP e

theorem coeffsWp_X {τ : Type} {p : ℕ} [Fact p.Prime] (t : τ) : ∀ m, coeff m (X t : MvPowerSeries τ ℂ_[p]) ∈ Wp p := by
  intro m
  rw [coeff_X]
  split_ifs
  · exact Subring.one_mem _
  · exact Subring.zero_mem _

theorem hasSubst_copy {p : ℕ} [Fact p.Prime] {n' r0 r1 : ℕ} (a : Fin r0) (b : Fin r1) :
    HasSubst (fun s : ZMod n' => (X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p])) := by
  have hinj : Function.Injective (fun s : ZMod n' => ((s, a, b) : ZMod n' × Fin r0 × Fin r1)) := by
    intro s t h
    simpa using h
  haveI : Filter.TendstoCofinite (fun s : ZMod n' => ((s, a, b) : ZMod n' × Fin r0 × Fin r1)) := ⟨hinj.tendsto_cofinite⟩
  exact HasSubst.X_comp (fun s : ZMod n' => ((s, a, b) : ZMod n' × Fin r0 × Fin r1))

theorem xiE_props {p : ℕ} [Fact p.Prime] {n' r0 r1 : ℕ} (x : Fin (n' / 2) ⊕ Fin (n' / 2) → MvPowerSeries (ZMod n') ℂ_[p])
    (hx : ∀ r, IntegralW (x r) ∧ constantCoeff (x r) = 0) (i : Eidx n' r0 r1 ⊕ Eidx n' r0 r1) :
    constantCoeff (xiE x i) = 0 ∧ ∀ m, coeff m (xiE x i) ∈ Wp p := by
  rcases i with ⟨r, a, b⟩ | ⟨r, a, b⟩
  · exact ⟨constantCoeff_subst_eq_zero (hasSubst_copy a b) (fun _ => constantCoeff_X _) (hx _).2,
      coeffsWp_subst (hasSubst_copy a b) (fun _ => coeffsWp_X _) (hx _).1⟩
  · exact ⟨constantCoeff_subst_eq_zero (hasSubst_copy a b) (fun _ => constantCoeff_X _) (hx _).2,
      coeffsWp_subst (hasSubst_copy a b) (fun _ => coeffsWp_X _) (hx _).1⟩

theorem xiE_integral : ∀ {p : ℕ} [Fact p.Prime] {n' r0 r1 : ℕ} (x : Fin (n' / 2) ⊕ Fin (n' / 2) → MvPowerSeries (ZMod n') ℂ_[p]), (∀ r, Formalism.MainNotions.GL3Theta.IntegralW (x r) ∧ MvPowerSeries.constantCoeff (x r) = 0) → (∀ i : Eidx n' r0 r1 ⊕ Eidx n' r0 r1, MvPowerSeries.constantCoeff (xiE x i) = 0) ∧ ∀ F : MvPowerSeries (Eidx n' r0 r1 ⊕ Eidx n' r0 r1) (FormalGroupSystem.K0 p), IntS p F → ∀ m, ‖MvPowerSeries.coeff m (MvPowerSeries.subst (xiE x) (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) F))‖ ≤ 1 := by
  intro p _ n' r0 r1 x hx
  have hP := xiE_props (r0 := r0) (r1 := r1) x hx
  refine ⟨fun i => (hP i).1, ?_⟩
  intro F hF m
  obtain ⟨g, rfl⟩ := hF
  have hs : HasSubst (xiE x : Eidx n' r0 r1 ⊕ Eidx n' r0 r1 → _) :=
    hasSubst_of_constantCoeff_zero fun i => (hP i).1
  have hG : ∀ d, coeff d (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p)
      (MvPowerSeries.map (algebraMap (FormalGroupSystem.WW p) (FormalGroupSystem.K0 p)) g)) ∈ Wp p := by
    intro d
    rw [coeff_map, coeff_map]
    rw [Formalism.L2.G.Pend.witt_fraction_to_Cp_algebraMap]
    exact Formalism.L2.G.Pend.wToC_mem_Wp p _
  exact GlobalTheory.BeProps.norm_le_one_of_mem_Wp (coeffsWp_subst hs (fun i => (hP i).2) hG m)

end GlobalTheory.OnePlace
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SubstInLettersJetLogG
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU GlobalTheory.OnePlace Classical

noncomputable section
namespace GlobalTheory.OnePlace.Letters

theorem constantCoeff_jetLogG (p : ℕ) [Fact p.Prime] (n' : ℕ) {β : Type} (v : ZMod n' × β) :
    MvPowerSeries.constantCoeff (jetLogG p n' v) = 0 := by
  show jetLogG p n' v 0 = 0
  unfold jetLogG
  refine Finset.sum_eq_zero fun e _ => ?_
  rw [if_neg]
  intro h
  have h2 := congrArg (fun m : ZMod n' × β →₀ ℕ => m (v.1 - 2 * (e : ZMod n'), v.2)) h
  simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.single_eq_same] at h2
  exact (pow_ne_zero e (pow_ne_zero 2 (Fact.out : p.Prime).ne_zero)) h2.symm

def posEquiv (n r0 r1 : ℕ) [NeZero n] : Zidx n r0 r1 ≃ ZMod n × Fin r0 × Fin r1 where
  toFun z := (((z.1 : ℕ) : ZMod n), z.2)
  invFun v := (toFin v.1, v.2)
  left_inv z := by
    ext <;> simp [toFin, ZMod.val_natCast, Nat.mod_eq_of_lt z.1.2]
  right_inv v := by
    ext <;> simp [toFin, ZMod.natCast_zmod_val]

theorem coeff_inLetters {n r0 r1 : ℕ} [NeZero n] {R : Type} [Semiring R] (f : MvPowerSeries (Zidx n r0 r1) R)
    (m : ZMod n × Fin r0 × Fin r1 →₀ ℕ) :
    MvPowerSeries.coeff m (inLetters f) = MvPowerSeries.coeff (Finsupp.mapDomain (posEquiv n r0 r1).symm m) f := rfl

theorem inLetters_eq_rename {n r0 r1 : ℕ} [NeZero n] {R : Type} [CommRing R] (f : MvPowerSeries (Zidx n r0 r1) R) :
    inLetters f = MvPowerSeries.rename (posEquiv n r0 r1) f := by
  ext m
  have hm : m = Finsupp.mapDomain (posEquiv n r0 r1) (Finsupp.mapDomain (posEquiv n r0 r1).symm m) := by
    rw [← Finsupp.mapDomain_comp, Equiv.self_comp_symm, Finsupp.mapDomain_id]
  have h1 := MvPowerSeries.coeff_embDomain_rename (posEquiv n r0 r1).toEmbedding f
    (Finsupp.mapDomain (posEquiv n r0 r1).symm m)
  rw [Finsupp.embDomain_eq_mapDomain] at h1
  rw [coeff_inLetters]
  conv_rhs => rw [hm]
  exact h1.symm

theorem map_inLetters {n r0 r1 : ℕ} [NeZero n] {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)
    (f : MvPowerSeries (Zidx n r0 r1) R) :
    MvPowerSeries.map φ (inLetters f) = inLetters (MvPowerSeries.map φ f) := by
  ext m
  rw [MvPowerSeries.coeff_map, coeff_inLetters, coeff_inLetters, MvPowerSeries.coeff_map]

theorem subst_inLetters_jetLogG {p : ℕ} [Fact p.Prime] {n' r0 r1 : ℕ} [NeZero n'] (F : MvPowerSeries (Zidx n' r0 r1) (FormalGroupSystem.K0 p)) :
    (∀ z, MvPowerSeries.constantCoeff (jetZ p n' r0 r1 z) = 0) ∧
    MvPowerSeries.subst (fun v : ZMod n' × Fin r0 × Fin r1 => MvPowerSeries.C (1 : ℂ_[p]) * jetLogG p n' v)
      (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (inLetters F)) =
    MvPowerSeries.subst (jetZ p n' r0 r1) (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) F) := by
  refine ⟨fun z => constantCoeff_jetLogG p n' _, ?_⟩
  have ha : MvPowerSeries.HasSubst
      (fun v : ZMod n' × Fin r0 × Fin r1 => MvPowerSeries.C (1 : ℂ_[p]) * jetLogG p n' v) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun v => by
      rw [map_mul, constantCoeff_jetLogG, mul_zero]
  rw [map_inLetters, inLetters_eq_rename, MvPowerSeries.rename_eq_subst,
    MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.HasSubst.X_comp _) ha]
  congr 1
  funext z
  rw [Function.comp_apply, MvPowerSeries.subst_X ha, map_one, one_mul]
  rfl

end GlobalTheory.OnePlace.Letters
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConstantCoeffBivariateSeriesSubstPair
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU GlobalTheory.OnePlace Classical

noncomputable section

namespace GlobalTheory.OnePlacePairs

open MvPowerSeries

variable {p : ℕ} [Fact p.Prime]

theorem expS_zero {κ : Type} : product_zeroth_first_parts.expS ℂ_[p] (0 : MvPowerSeries κ ℂ_[p]) = 1 := by
  have h := ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_add (k := ℂ_[p]) (a := (0 : MvPowerSeries κ ℂ_[p])) (b := 0)
    (by simp) (by simp)
  rw [add_zero] at h
  have hu : IsUnit (PowerSeries.subst (0 : MvPowerSeries κ ℂ_[p]) (PowerSeries.exp ℂ_[p])) := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff, ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.constantCoeff_exp (by simp)]
    exact isUnit_one
  unfold product_zeroth_first_parts.expS
  exact hu.mul_left_cancel (h.symm.trans (mul_one _).symm)

theorem expS_add {κ : Type} {f g : MvPowerSeries κ ℂ_[p]} (hf : constantCoeff f = 0) (hg : constantCoeff g = 0) :
    product_zeroth_first_parts.expS ℂ_[p] (f + g) = product_zeroth_first_parts.expS ℂ_[p] f * product_zeroth_first_parts.expS ℂ_[p] g :=
  ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_add hf hg

theorem expS_sum {κ ι : Type} (s : Finset ι) (f : ι → MvPowerSeries κ ℂ_[p]) (hf : ∀ i, constantCoeff (f i) = 0) :
    product_zeroth_first_parts.expS ℂ_[p] (∑ i ∈ s, f i) = ∏ i ∈ s, product_zeroth_first_parts.expS ℂ_[p] (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [expS_zero]
  | insert i s hi ih =>
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_insert hi, Finset.prod_insert hi, expS_add (hf i) (by rw [map_sum]; exact Finset.sum_eq_zero fun j _ => hf j), ih]

theorem padicExpSeries_doubleSum {κ α β : Type} [Fintype α] [Fintype β] (f : α → β → MvPowerSeries κ ℂ_[p])
    (hf : ∀ a b, constantCoeff (f a b) = 0) :
    product_zeroth_first_parts.expS ℂ_[p] (∑ a, ∑ b, f a b) = ∏ a, ∏ b, product_zeroth_first_parts.expS ℂ_[p] (f a b) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [expS_sum _ _ (fun a => by rw [map_sum]; exact Finset.sum_eq_zero fun b _ => hf a b)]
  exact Finset.prod_congr rfl fun a _ => expS_sum _ _ (hf a)

theorem cc_logF : PowerSeries.constantCoeff (Formalism.MainNotions.GL3Theta.logF p) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Formalism.MainNotions.GL3Theta.logF, PowerSeries.coeff_mk]
  simp

theorem cc_plog {κ : Type} {u : MvPowerSeries κ ℂ_[p]} (hu : constantCoeff u = 0) :
    constantCoeff (PowerSeries.subst u (Formalism.MainNotions.GL3Theta.logF p)) = 0 := by
  rw [ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.constantCoeff_psubst hu, cc_logF]

theorem constantCoeff_bivariateSeriesSubstPair {κ : Type} {b0 : MvPowerSeries (Fin 2) ℂ_[p]} (hb0 : constantCoeff b0 = 0)
    {u v : MvPowerSeries κ ℂ_[p]} (hu : constantCoeff u = 0) (hv : constantCoeff v = 0) :
    constantCoeff (GlobalTheory.ThBe0.at2 b0 u v) = 0 := by
  have h : ∀ i : Fin 2, constantCoeff (if i = 0 then u else v) = 0 := fun i => by split_ifs <;> assumption
  exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero h) h hb0

theorem subst_powerSeriesEvalTwoGroups {κ κ' : Type} {φ : κ → MvPowerSeries κ' ℂ_[p]} (hφ : HasSubst φ) (b0 : MvPowerSeries (Fin 2) ℂ_[p])
    {u v : MvPowerSeries κ ℂ_[p]} (hu : constantCoeff u = 0) (hv : constantCoeff v = 0) :
    subst φ (GlobalTheory.ThBe0.at2 b0 u v) = GlobalTheory.ThBe0.at2 b0 (subst φ u) (subst φ v) := by
  have h : ∀ i : Fin 2, constantCoeff (if i = 0 then u else v) = 0 := fun i => by split_ifs <;> assumption
  unfold GlobalTheory.ThBe0.at2
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero h) hφ]
  congr 1
  funext i
  split_ifs <;> rfl

variable {n' : ℕ} [NeZero n']

theorem hasSubst_pair {r0 r1 : ℕ} (a : Fin r0) (b : Fin r1) :
    HasSubst (fun s : ZMod n' => (X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p])) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

theorem cc_jet {r0 r1 : ℕ} (v : ZMod n' × Fin r0 × Fin r1) : constantCoeff (jetLogG p n' v) = 0 := by
  rw [← GlobalTheory.BiextInhab.bridge p n' v.2 v.1]
  exact GlobalTheory.BeProps.constantCoeff_laAt _ _

theorem hasSubst_jet' {r0 r1 : ℕ} : HasSubst (jetLogG p n' (β := Fin r0 × Fin r1)) :=
  hasSubst_of_constantCoeff_zero cc_jet

theorem pair_eq {r0 r1 : ℕ} (b0 : MvPowerSeries (Fin 2) ℂ_[p]) (bv : MvPowerSeries (ZMod n') ℂ_[p])
    (x : Fin (n' / 2) ⊕ Fin (n' / 2) → MvPowerSeries (ZMod n') ℂ_[p]) (V : MvPowerSeries (ZMod n') ℂ_[p])
    (hb0 : constantCoeff b0 = 0) (hbv : constantCoeff bv = 0) (hx : ∀ r, constantCoeff (x r) = 0)
    (H : product_zeroth_first_parts.expS ℂ_[p] (-(∑ r : Fin (n' / 2), GlobalTheory.ThBe0.at2 b0 (PowerSeries.subst (x (Sum.inl r)) (Formalism.MainNotions.GL3Theta.logF p))
      (PowerSeries.subst (x (Sum.inr r)) (Formalism.MainNotions.GL3Theta.logF p)))) = V * product_zeroth_first_parts.expS ℂ_[p] (-(subst (GlobalTheory.ThStr.laS p n') bv)))
    (a : Fin r0) (b : Fin r1) :
    product_zeroth_first_parts.expS ℂ_[p] (-(∑ r : Fin (n' / 2), GlobalTheory.ThBe0.at2 b0
                               (PowerSeries.subst (xiE x (Sum.inl ((r, a, b) : Eidx n' r0 r1))) (Formalism.MainNotions.GL3Theta.logF p))
                               (PowerSeries.subst (xiE x (Sum.inr ((r, a, b) : Eidx n' r0 r1))) (Formalism.MainNotions.GL3Theta.logF p)))) =
      subst (fun s : ZMod n' => (X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p])) V *
        product_zeroth_first_parts.expS ℂ_[p] (-(subst (fun s : ZMod n' => jetLogG p n' (s, a, b)) bv)) := by
  have hψ := hasSubst_pair (p := p) (n' := n') a b
  have hcL : constantCoeff (-(∑ r : Fin (n' / 2), GlobalTheory.ThBe0.at2 b0 (PowerSeries.subst (x (Sum.inl r)) (Formalism.MainNotions.GL3Theta.logF p))
      (PowerSeries.subst (x (Sum.inr r)) (Formalism.MainNotions.GL3Theta.logF p)))) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_neg, map_sum, Finset.sum_eq_zero fun r _ => constantCoeff_bivariateSeriesSubstPair hb0 (cc_plog (hx _)) (cc_plog (hx _)), neg_zero]
  have hLa : HasSubst (GlobalTheory.ThStr.laS p n') := hasSubst_of_constantCoeff_zero GlobalTheory.BeProps.constantCoeff_laS
  have hcR : constantCoeff (-(subst (GlobalTheory.ThStr.laS p n') bv)) = 0 := by
    rw [map_neg, constantCoeff_subst_eq_zero hLa GlobalTheory.BeProps.constantCoeff_laS hbv, neg_zero]
  have e1 : subst (fun s : ZMod n' => (X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p]))
      (product_zeroth_first_parts.expS ℂ_[p] (-(∑ r : Fin (n' / 2), GlobalTheory.ThBe0.at2 b0 (PowerSeries.subst (x (Sum.inl r)) (Formalism.MainNotions.GL3Theta.logF p))
        (PowerSeries.subst (x (Sum.inr r)) (Formalism.MainNotions.GL3Theta.logF p))))) =
      product_zeroth_first_parts.expS ℂ_[p] (-(∑ r : Fin (n' / 2), GlobalTheory.ThBe0.at2 b0
        (PowerSeries.subst (xiE x (Sum.inl ((r, a, b) : Eidx n' r0 r1))) (Formalism.MainNotions.GL3Theta.logF p))
        (PowerSeries.subst (xiE x (Sum.inr ((r, a, b) : Eidx n' r0 r1))) (Formalism.MainNotions.GL3Theta.logF p)))) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [product_zeroth_first_parts.expS, product_zeroth_first_parts.expS, GlobalTheory.BeProps.subst_psubst hψ hcL, ← substAlgHom_apply hψ, map_neg, map_sum]
    congr 2
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [substAlgHom_apply, subst_powerSeriesEvalTwoGroups hψ b0 (cc_plog (hx _)) (cc_plog (hx _)),
      GlobalTheory.BeProps.subst_psubst hψ (hx _), GlobalTheory.BeProps.subst_psubst hψ (hx _)]
    rfl
  have e2 : subst (fun s : ZMod n' => (X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p]))
      (V * product_zeroth_first_parts.expS ℂ_[p] (-(subst (GlobalTheory.ThStr.laS p n') bv))) =
      subst (fun s : ZMod n' => (X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p])) V *
        product_zeroth_first_parts.expS ℂ_[p] (-(subst (fun s : ZMod n' => jetLogG p n' (s, a, b)) bv)) := by
    have hn : subst (fun s : ZMod n' => (X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p]))
        (-(subst (GlobalTheory.ThStr.laS p n') bv)) = -(subst (fun s : ZMod n' => jetLogG p n' (s, a, b)) bv) := by
      rw [← substAlgHom_apply hψ, map_neg, substAlgHom_apply, subst_comp_subst_apply hLa hψ]
      congr 2
      funext s
      exact GlobalTheory.BiextInhab.bridge p n' (a, b) s
    rw [product_zeroth_first_parts.expS, product_zeroth_first_parts.expS, ← substAlgHom_apply hψ, map_mul]
    simp only [substAlgHom_apply]
    rw [GlobalTheory.BeProps.subst_psubst hψ hcR, hn]
  rw [← e1, ← e2, H]

theorem integralW_pair {r0 r1 : ℕ} (a : Fin r0) (b : Fin r1) {V : MvPowerSeries (ZMod n') ℂ_[p]}
    (hV : Formalism.MainNotions.GL3Theta.IntegralW V) :
    Formalism.MainNotions.GL3Theta.IntegralW (subst (fun s : ZMod n' => (X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p])) V) := by
  let e : ZMod n' ↪ ZMod n' × Fin r0 × Fin r1 := ⟨fun s => (s, a, b), fun x y h => (Prod.mk.inj h).1⟩
  have he : subst (fun s : ZMod n' => (X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p])) V =
      rename e V := by
    rw [rename_eq_subst]; rfl
  rw [he]
  intro m
  by_cases hm : m ∈ Set.range (Finsupp.mapDomain (e : ZMod n' → ZMod n' × Fin r0 × Fin r1))
  · obtain ⟨n, rfl⟩ := hm
    rw [← Finsupp.embDomain_eq_mapDomain, coeff_embDomain_rename]
    exact hV n
  · rw [coeff_rename_eq_zero _ _ hm]
    exact zero_mem _

theorem cc_xiE {r0 r1 : ℕ} {x : Fin (n' / 2) ⊕ Fin (n' / 2) → MvPowerSeries (ZMod n') ℂ_[p]}
    (hx : ∀ r, constantCoeff (x r) = 0) (e : Eidx n' r0 r1 ⊕ Eidx n' r0 r1) : constantCoeff (xiE x e) = 0 := by
  rcases e with ⟨r, a, b⟩ | ⟨r, a, b⟩
  · exact constantCoeff_subst_eq_zero (hasSubst_pair a b) (fun _ => constantCoeff_X _) (hx _)
  · exact constantCoeff_subst_eq_zero (hasSubst_pair a b) (fun _ => constantCoeff_X _) (hx _)

theorem sum_reorder {r0 r1 : ℕ} {M : Type*} [AddCommMonoid M] (f : Eidx n' r0 r1 → M) :
    ∑ e, f e = ∑ a : Fin r0, ∑ b : Fin r1, ∑ r : Fin (n' / 2), f (r, a, b) := by
  rw [Fintype.sum_prod_type, Finset.sum_comm, Fintype.sum_prod_type]

theorem neg_doubleSum_eq_doubleSum_neg {α β M : Type*} [Fintype α] [Fintype β] [AddCommGroup M] (g : α → β → M) :
    -(∑ a, ∑ b, g a b) = ∑ a, ∑ b, -g a b := by
  simp [Finset.sum_neg_distrib]

theorem rhs_eq {r0 r1 : ℕ} (bv : MvPowerSeries (ZMod n') ℂ_[p]) (hbv : constantCoeff bv = 0) :
    subst (jetLogG p n' (β := Fin r0 × Fin r1)) (product_zeroth_first_parts.expS ℂ_[p] ((-1 : ℂ_[p]) • ∑ a : Fin r0, ∑ b : Fin r1,
      subst (fun s : ZMod n' => (X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p])) bv)) =
      ∏ a : Fin r0, ∏ b : Fin r1, product_zeroth_first_parts.expS ℂ_[p] (-(subst (fun s : ZMod n' => jetLogG p n' (s, a, b)) bv)) := by
  have hJ := hasSubst_jet' (p := p) (n' := n') (r0 := r0) (r1 := r1)
  have hc : constantCoeff (-(∑ a : Fin r0, ∑ b : Fin r1,
      subst (fun s : ZMod n' => (X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p])) bv)) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_neg, map_sum, Finset.sum_eq_zero fun a _ => ?_, neg_zero]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_eq_zero fun b _ => constantCoeff_subst_eq_zero (hasSubst_pair a b) (fun _ => constantCoeff_X _) hbv
  have e : subst (jetLogG p n' (β := Fin r0 × Fin r1)) (-(∑ a : Fin r0, ∑ b : Fin r1,
      subst (fun s : ZMod n' => (X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p])) bv)) =
      ∑ a : Fin r0, ∑ b : Fin r1, -(subst (fun s : ZMod n' => jetLogG p n' (s, a, b)) bv) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← substAlgHom_apply hJ, map_neg, map_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [substAlgHom_apply, subst_comp_subst_apply (hasSubst_pair a b) hJ]
    congr 2
    funext s
    rw [subst_X hJ]
  rw [neg_one_smul, product_zeroth_first_parts.expS, GlobalTheory.BeProps.subst_psubst hJ hc, e]
  exact padicExpSeries_doubleSum _ fun a b => by
    rw [map_neg, constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun s => cc_jet _) (fun s => cc_jet _) hbv,
      neg_zero]

end GlobalTheory.OnePlacePairs

namespace GlobalTheory.OnePlacePairs

open MvPowerSeries

theorem pairs_all : ∀ {p : ℕ} [Fact p.Prime] {n' : ℕ} [NeZero n'] (b0 : MvPowerSeries (Fin 2) ℂ_[p]) (bv : MvPowerSeries (ZMod n') ℂ_[p]) (x : Fin (n' / 2) ⊕ Fin (n' / 2) → MvPowerSeries (ZMod n') ℂ_[p]) (V : MvPowerSeries (ZMod n') ℂ_[p]), MvPowerSeries.constantCoeff b0 = 0 → MvPowerSeries.constantCoeff bv = 0 → (∀ r, MvPowerSeries.constantCoeff (x r) = 0) → Formalism.MainNotions.GL3Theta.IntegralW V → product_zeroth_first_parts.expS ℂ_[p] (-(∑ r : Fin (n' / 2), GlobalTheory.ThBe0.at2 b0 (PowerSeries.subst (x (Sum.inl r)) (Formalism.MainNotions.GL3Theta.logF p)) (PowerSeries.subst (x (Sum.inr r)) (Formalism.MainNotions.GL3Theta.logF p)))) = V * product_zeroth_first_parts.expS ℂ_[p] (-(MvPowerSeries.subst (GlobalTheory.ThStr.laS p n') bv)) → ∀ (r0 r1 : ℕ), ∃ U2 : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p], (∀ m, ‖MvPowerSeries.coeff m U2‖ ≤ 1) ∧ product_zeroth_first_parts.expS ℂ_[p] (-(∑ e : Eidx n' r0 r1, GlobalTheory.ThBe0.at2 b0 (PowerSeries.subst (xiE x (Sum.inl e)) (Formalism.MainNotions.GL3Theta.logF p)) (PowerSeries.subst (xiE x (Sum.inr e)) (Formalism.MainNotions.GL3Theta.logF p)))) = U2 * MvPowerSeries.subst (jetLogG p n' (β := Fin r0 × Fin r1)) (product_zeroth_first_parts.expS ℂ_[p] ((-1 : ℂ_[p]) • ∑ a : Fin r0, ∑ b : Fin r1, MvPowerSeries.subst (fun s : ZMod n' => (MvPowerSeries.X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p])) bv)) := by
  intro p _ n' _ b0 bv x V hb0 hbv hx hV H r0 r1
  refine ⟨∏ a : Fin r0, ∏ b : Fin r1,
    subst (fun s : ZMod n' => (X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p])) V, fun m => ?_, ?_⟩
  · have hmem : (∏ a : Fin r0, ∏ b : Fin r1,
        subst (fun s : ZMod n' => (X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p])) V) ∈
        GlobalTheory.BiextInhab.serW p (ZMod n' × Fin r0 × Fin r1) :=
      Subring.prod_mem _ fun a _ => Subring.prod_mem _ fun b _ => GlobalTheory.BiextInhab.mem_serW.2 (integralW_pair a b hV)
    exact GlobalTheory.BeProps.norm_le_one_of_mem_Wp (GlobalTheory.BiextInhab.mem_serW.1 hmem m)
  · rw [rhs_eq bv hbv, ← Finset.prod_mul_distrib]
    simp only [← Finset.prod_mul_distrib]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [sum_reorder, neg_doubleSum_eq_doubleSum_neg, padicExpSeries_doubleSum _ fun a b => by
      rw [map_neg, map_sum, Finset.sum_eq_zero fun r _ => constantCoeff_bivariateSeriesSubstPair hb0 (cc_plog (cc_xiE hx _)) (cc_plog (cc_xiE hx _)),
        neg_zero]]
    exact Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun b _ => pair_eq b0 bv x V hb0 hbv hx H a b

end GlobalTheory.OnePlacePairs
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIsFrobWToC
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCoeEqOfPowEqOne
noncomputable section

namespace GlobalTheory.ThBe0

open Formalism.MainNotions.GL3Theta IsLocalRing Polynomial

theorem exists_coe_eq_of_pow_eq_one (l : ℕ) [Fact l.Prime] (ζ : ℂ_[l]) (n : ℕ) (hn : 0 < n)
    (h : ζ ^ n = 1) : ∃ a : PadicAlgCl l, (a : ℂ_[l]) = ζ ∧ a ^ n = 1 := by
  have hs : (X ^ n - C 1 : (PadicAlgCl l)[X]).Splits := IsAlgClosed.splits _
  have hne : (X ^ n - C 1 : (PadicAlgCl l)[X]) ≠ 0 := X_pow_sub_C_ne_zero hn 1
  have hr : ((X ^ n - C 1 : (PadicAlgCl l)[X]).map (algebraMap (PadicAlgCl l) ℂ_[l])).IsRoot ζ := by
    simp [h]
  obtain ⟨a, ha⟩ := hs.mem_range_of_isRoot hne hr
  refine ⟨a, ha, (algebraMap (PadicAlgCl l) ℂ_[l]).injective ?_⟩
  rw [map_pow, ha, h, map_one]

theorem exists_gal_pow (l : ℕ) [Fact l.Prime] :
    ∃ g : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l,
      ∀ (x : PadicAlgCl l) (m : ℕ), Nat.Coprime m l → x ^ m = 1 → g x = x ^ l := by
  have e : (ℤ_[l] ⧸ maximalIdeal ℤ_[l]) ≃+* ZMod l := PadicInt.residueField
  have hl : l.Prime := Fact.out
  have : NeZero l := ⟨hl.ne_zero⟩
  have hcard : Nat.card (ℤ_[l] ⧸ maximalIdeal ℤ_[l]) = l := by
    rw [Nat.card_congr e.toEquiv, Nat.card_zmod]
  obtain ⟨φ, hφ⟩ := GlobalTheory.MemLoc.exists_algEquiv_rootOfUnity_eq_pow ℤ_[l] ℚ_[l]
    (Finite.of_equiv _ e.symm.toEquiv) (PadicAlgCl l)
  rw [hcard] at hφ
  refine ⟨φ, fun x m hm hx => hφ x m (fun h => ?_) hx⟩
  rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_natCast, ZMod.natCast_eq_zero_iff] at h
  exact (hl.coprime_iff_not_dvd.1 hm.symm) h

theorem isFrob_of_rootOfUnity {l : ℕ} [Fact l.Prime] (σ : ℂ_[l] →+* ℂ_[l]) (hσ : ∀ x, ‖σ x‖ = ‖x‖)
    (hζ : ∀ (ζ : ℂ_[l]) (n : ℕ), 0 < n → Nat.Coprime n l → ζ ^ n = 1 → σ ζ = ζ ^ l) : IsFrob σ := by
  have hl : l.Prime := Fact.out
  have hl0 : (l : ℂ_[l]) ≠ 0 := Nat.cast_ne_zero.2 hl.ne_zero
  have hc : Continuous σ := (AddMonoidHomClass.isometry_of_norm σ hσ).continuous
  refine ⟨hσ, fun x hx => ?_⟩
  have hcl : IsClosed (Wp l : Set ℂ_[l]) := Subring.isClosed_topologicalClosure _
  have hA : ∀ x ∈ Subring.closure {ζ : ℂ_[l] | ∃ n : ℕ, 0 < n ∧ Nat.Coprime n l ∧ ζ ^ n = 1},
      ∃ y ∈ Wp l, σ x = x ^ l + (l : ℂ_[l]) * y := by
    intro x hx
    have hW : ∀ {x}, x ∈ Subring.closure
        {ζ : ℂ_[l] | ∃ n : ℕ, 0 < n ∧ Nat.Coprime n l ∧ ζ ^ n = 1} → x ∈ Wp l :=
      fun h => Subring.le_topologicalClosure _ h
    induction hx using Subring.closure_induction with
    | mem x hx =>
      obtain ⟨n, hn, hnl, h⟩ := hx
      exact ⟨0, zero_mem _, by simp [hζ x n hn hnl h]⟩
    | zero => exact ⟨0, zero_mem _, by simp [hl.ne_zero]⟩
    | one => exact ⟨0, zero_mem _, by simp⟩
    | add x y hx hy ihx ihy =>
      obtain ⟨a, ha, ea⟩ := ihx
      obtain ⟨b, hb, eb⟩ := ihy
      obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hl (⟨x, hW hx⟩ : Wp l) ⟨y, hW hy⟩
      have hr' := congrArg Subtype.val hr
      push_cast at hr'
      refine ⟨a + b - x * y * r, sub_mem (add_mem ha hb)
        (mul_mem (mul_mem (hW hx) (hW hy)) r.2), ?_⟩
      rw [map_add (f := _), ea, eb, hr']
      ring
    | neg x hx ihx =>
      obtain ⟨a, ha, ea⟩ := ihx
      rcases hl.eq_two_or_odd' with h2 | ho
      · refine ⟨-a - x ^ l, sub_mem (neg_mem ha) (pow_mem (hW hx) _), ?_⟩
        have he : Even l := h2 ▸ even_two
        have h2' : (l : ℂ_[l]) = 2 := by exact_mod_cast h2
        rw [map_neg, ea, he.neg_pow]
        linear_combination (x ^ l) * h2'
      · refine ⟨-a, neg_mem ha, ?_⟩
        rw [map_neg, ea, ho.neg_pow]
        ring
    | mul x y hx hy ihx ihy =>
      obtain ⟨a, ha, ea⟩ := ihx
      obtain ⟨b, hb, eb⟩ := ihy
      refine ⟨a * y ^ l + x ^ l * b + l * (a * b), add_mem (add_mem (mul_mem ha (pow_mem (hW hy) _))
        (mul_mem (pow_mem (hW hx) _) hb)) (mul_mem (natCast_mem _ _) (mul_mem ha hb)), ?_⟩
      rw [map_mul, ea, eb, mul_pow]
      ring
  have hf : Continuous fun x : ℂ_[l] => (σ x - x ^ l) * (l : ℂ_[l])⁻¹ := by fun_prop
  have hx' : x ∈ (fun x : ℂ_[l] => (σ x - x ^ l) * (l : ℂ_[l])⁻¹) ⁻¹' (Wp l : Set ℂ_[l]) := by
    refine closure_minimal (fun z hz => ?_) (hcl.preimage hf) hx
    obtain ⟨y, hy, e⟩ := hA z hz
    have : (σ z - z ^ l) * (l : ℂ_[l])⁻¹ = y := by
      rw [e]; field_simp; ring
    simpa [this] using hy
  refine ⟨_, hx', ?_⟩
  field_simp
  ring

end GlobalTheory.ThBe0
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

noncomputable section

namespace GlobalTheory.TwU

theorem wHom_ext (p : ℕ) [Fact p.Prime] (f g : Formalism.L2.G.Pend.WW p →+* ℂ_[p])
    (hf : ∀ x, ‖f x‖ ≤ 1) (hg : ∀ x, ‖g x‖ ≤ 1)
    (ht : ∀ y, f (WittVector.teichmuller p y) = g (WittVector.teichmuller p y)) (x : Formalism.L2.G.Pend.WW p) :
    f x = g x := by
  refine Formalism.L2.G.Pend.eq_of_close p fun N => ?_
  obtain ⟨c, hc⟩ := WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff x N
  set S := ∑ i ∈ Finset.Iic N, (WittVector.teichmuller p
        (((_root_.frobeniusEquiv (Formalism.L2.G.Pend.kb p) p).symm ^ i) (x.coeff i)) * (p : Formalism.L2.G.Pend.WW p) ^ i) with hS
  have hfS : f S = g S := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hS, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast, ht]
  have hx : x = S + (p : Formalism.L2.G.Pend.WW p) ^ (N + 1) * c := by rw [← hc]; ring
  have hpC : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := Formalism.L2.G.Pend.norm_p_C p
  have e : f x - g x = (p : ℂ_[p]) ^ (N + 1) * (f c - g c) := by
    rw [hx, map_add (f := _), map_add (f := _), hfS, map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast]; ring
  rw [e, norm_mul, norm_pow, hpC]
  have h1 : ‖f c - g c‖ ≤ 1 := Formalism.L2.G.Pend.nsub p (hf c) (hg c)
  calc ((p : ℝ)⁻¹) ^ (N + 1) * ‖f c - g c‖ ≤ ((p : ℝ)⁻¹) ^ (N + 1) * 1 :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = ((p : ℝ)⁻¹) ^ N * (p : ℝ)⁻¹ := by rw [mul_one, pow_succ]
    _ ≤ ((p : ℝ)⁻¹) ^ N * 1 := mul_le_mul_of_nonneg_left (Formalism.L2.G.Pend.r_lt_one p).le (by positivity)
    _ = ((p : ℝ)⁻¹) ^ N := mul_one _

theorem wToC_frob (p : ℕ) [Fact p.Prime] (σ : ℂ_[p] →+* ℂ_[p]) (hσ : ∀ x, ‖σ x‖ = ‖x‖)
    (hζ : ∀ (ζ : ℂ_[p]) (n : ℕ), 0 < n → Nat.Coprime n p → ζ ^ n = 1 → σ ζ = ζ ^ p) (x : FormalGroupSystem.WW p) :
    σ (Formalism.L2.G.Pend.wToC p x) = Formalism.L2.G.Pend.wToC p (sigW p x) := by
  have := wHom_ext p (σ.comp (Formalism.L2.G.Pend.wToC p)) ((Formalism.L2.G.Pend.wToC p).comp (sigW p))
    (fun y => by rw [RingHom.comp_apply, hσ]; exact Formalism.L2.G.Pend.norm_wToC_le p y)
    (fun y => Formalism.L2.G.Pend.norm_wToC_le p _) (fun y => ?_) x
  · exact this
  · rw [RingHom.comp_apply, RingHom.comp_apply]
    have hs : sigW p (WittVector.teichmuller p y) = WittVector.teichmuller p (y ^ p) := by
      show WittVector.frobenius (WittVector.teichmuller p y) = _
      rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def]
    rw [hs, map_pow (WittVector.teichmuller p), map_pow (Formalism.L2.G.Pend.wToC p)]
    by_cases hy : y = 0
    · subst hy
      rw [WittVector.teichmuller_zero, map_zero, map_zero, zero_pow (Fact.out : p.Prime).ne_zero]
    · obtain ⟨m, hm, hc, h1⟩ := Formalism.L2.G.Pend.exists_coprime_pow_eq_one p hy
      exact hζ _ m hm hc (by rw [← map_pow, ← map_pow, h1, map_one, map_one])

theorem exists_isFrob_wToC : ∀ (p : ℕ) [Fact p.Prime], ∃ σ : ℂ_[p] →+* ℂ_[p], GlobalTheory.ThBe0.IsFrob σ ∧
    ∀ x : FormalGroupSystem.WW p, σ (Formalism.L2.G.Pend.wToC p x) = Formalism.L2.G.Pend.wToC p (sigW p x) := by
  intro p _
  obtain ⟨g, hg⟩ := GlobalTheory.ThBe0.exists_gal_pow p
  have hζ : ∀ (ζ : ℂ_[p]) (n : ℕ), 0 < n → Nat.Coprime n p → ζ ^ n = 1 → Formalism.Per.σC g ζ = ζ ^ p := by
    intro ζ n hn hnl h
    obtain ⟨a, rfl, ha⟩ := GlobalTheory.ThBe0.exists_coe_eq_of_pow_eq_one p ζ n hn h
    rw [GlobalTheory.RingBasics.σC_coe, hg a n hnl ha]
    exact map_pow (algebraMap (PadicAlgCl p) ℂ_[p]) a p
  exact ⟨Formalism.Per.σC g, GlobalTheory.ThBe0.isFrob_of_rootOfUnity _ (GlobalTheory.RingBasics.norm_σC g) hζ,
    wToC_frob p _ (GlobalTheory.RingBasics.norm_σC g) hζ⟩

end GlobalTheory.TwU
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.WToCPowComm
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

noncomputable section

namespace GlobalTheory.TwU

theorem wToC_pow_comm {p : ℕ} [Fact p.Prime] (σ : ℂ_[p] →+* ℂ_[p])
    (hσ : ∀ x : FormalGroupSystem.WW p, σ (Formalism.L2.G.Pend.wToC p x) = Formalism.L2.G.Pend.wToC p (sigW p x)) :
    ∀ (k : ℕ) (x : FormalGroupSystem.WW p), (σ ^ k) (Formalism.L2.G.Pend.wToC p x) = Formalism.L2.G.Pend.wToC p ((sigW p)^[k] x) := by
  intro k
  induction k with
  | zero => intro x; simp
  | succ k ih =>
    intro x
    rw [pow_succ', RingHom.coe_mul, Function.comp_apply, ih, hσ, Function.iterate_succ_apply']

theorem dualOm_wToC : ∀ (p : ℕ) [Fact p.Prime] (σ : ℂ_[p] →+* ℂ_[p]), (∀ x : FormalGroupSystem.WW p, σ (Formalism.L2.G.Pend.wToC p x) = Formalism.L2.G.Pend.wToC p (sigW p x)) → ∀ (n' : ℕ), Even n' → ∀ B : OmBasis p n', GlobalTheory.ThBe0.DualOm σ n' (fun r => Formalism.L2.G.Pend.wToC p (B.om r)) (fun r => Formalism.L2.G.Pend.wToC p (B.omS r)) := by
  intro p _ σ hσ n' hn B
  have hk := wToC_pow_comm σ hσ
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Fintype.card_fin]
    exact Nat.two_mul_div_two_of_even hn
  · intro r
    exact ⟨Formalism.L2.G.Pend.wToC_mem_Wp p _, Formalism.L2.G.Pend.wToC_mem_Wp p _⟩
  · intro r
    refine ⟨?_, ?_⟩
    · rw [hk, B.fix r]
    · rw [hk, B.fixS r]
  · intro r r'
    have h := congrArg (Formalism.L2.G.Pend.wToC p) (B.dual r r')
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at h
    rw [← Fin.sum_univ_eq_sum_range (fun i => (σ ^ (2 * i)) (Formalism.L2.G.Pend.wToC p (B.om r) * Formalism.L2.G.Pend.wToC p (B.omS r')))]
    simp only [← map_mul, hk]
    rw [h]
    split_ifs <;> simp

end GlobalTheory.TwU
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLetterCoordinatesSeriesOnePlace
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU GlobalTheory.OnePlace Classical

namespace GlobalTheory.OnePlace

theorem exists_letterCoordinates_series_onePlace : ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ (n' : ℕ) [NeZero n'], Even n' → ∀ (B : OmBasis p n') (be : MvPowerSeries (Fin 2) (FormalGroupSystem.K0 p)), BeProp p be → ∃ bv : MvPowerSeries (ZMod n') ℂ_[p], product_zeroth_first_parts.B1 p n' bv ∧ product_zeroth_first_parts.B2 p n' bv ∧ product_zeroth_first_parts.B3 p n' bv ∧ product_zeroth_first_parts.B4 p n' bv ∧ ∀ (r0 r1 : ℕ) (U : MvPowerSeries (Eidx n' r0 r1 ⊕ Eidx n' r0 r1) (FormalGroupSystem.K0 p)), IntS p (inParam p U) → ∃ U' : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p], (∀ m, ‖MvPowerSeries.coeff m U'‖ ≤ 1) ∧ MvPowerSeries.subst (fun v : ZMod n' × Fin r0 × Fin r1 => MvPowerSeries.C (1 : ℂ_[p]) * jetLogG p n' v) (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (inLetters (thOne B be U))) = U' * MvPowerSeries.subst (jetLogG p n' (β := Fin r0 × Fin r1)) (product_zeroth_first_parts.expS ℂ_[p] ((-1 : ℂ_[p]) • ∑ a : Fin r0, ∑ b : Fin r1, MvPowerSeries.subst (fun s : ZMod n' => (MvPowerSeries.X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p])) bv)) := by
  intro p _ h5 n' _ hev B be hbe
  obtain ⟨σ, hσ, hσw⟩ := GlobalTheory.TwU.exists_isFrob_wToC p
  have hb0 := GlobalTheory.BeRead.isBe0_map p σ hσ hσw be hbe
  have hb00 : MvPowerSeries.constantCoeff (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) be) = 0 := by
    by_contra h
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply] at h
    exact (hb0.axes 0 h).1 rfl
  have hD := GlobalTheory.TwU.dualOm_wToC p σ hσw n' hev B
  obtain ⟨bv, t, x, ⟨h1, h2, h3, h4⟩, hcc, hsim, ht, hx, htla, hxt⟩ :=
    Unr.exists_coords_and_series h5 hσ hb0 n' hev _ _ hD
  refine ⟨bv, h1, h2, h3, h4, fun r0 r1 U hU => ?_⟩
  obtain ⟨V, hV, hVeq⟩ := GlobalTheory.OrbitPair.expS_neg_sum_bivariate_pair_integral σ _ _ _ bv t x hb00 hcc ht hx htla hxt hsim
  obtain ⟨U2, hU2, hU2eq⟩ := GlobalTheory.OnePlacePairs.pairs_all _ bv x V hb00 hcc (fun r => (hx r).2) hV hVeq r0 r1
  obtain ⟨hξ0, hξint⟩ := GlobalTheory.OnePlace.xiE_integral (r0 := r0) (r1 := r1) x hx
  obtain ⟨hJ0, hJ⟩ := GlobalTheory.OnePlace.Letters.subst_inLetters_jetLogG (p := p) (r0 := r0) (r1 := r1) (thOne B be U)
  refine ⟨U2 * MvPowerSeries.subst (xiE x) (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (inParam p U)), ?_, ?_⟩
  · intro m
    rw [MvPowerSeries.coeff_mul]
    refine (IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun q _ => ?_)
    rw [norm_mul]
    exact mul_le_one₀ (hU2 _) (norm_nonneg _) (hξint _ hU _)
  · rw [hJ, GlobalTheory.OnePlaceRead.read_thOne B be hbe U _ (xiE x) hJ0 hξ0 (GlobalTheory.OnePlace.Ident.coordZ_jetZ σ hσw hev B hD t x ht (fun r => (hx r).2) htla hxt r0 r1), hU2eq]
    ring

end GlobalTheory.OnePlace

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLetterCoordinatesSeriesOnePlaceStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_letterCoordinates_series_onePlace_alt : ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ (n' : ℕ) [NeZero n'], Even n' → ∀ (B : OmBasis p n') (be : MvPowerSeries (Fin 2) (FormalGroupSystem.K0 p)), BeProp p be → ∃ bv : MvPowerSeries (ZMod n') ℂ_[p], product_zeroth_first_parts.B1 p n' bv ∧ product_zeroth_first_parts.B2 p n' bv ∧ product_zeroth_first_parts.B3 p n' bv ∧ product_zeroth_first_parts.B4 p n' bv ∧ ∀ (r0 r1 : ℕ) (U : MvPowerSeries (Eidx n' r0 r1 ⊕ Eidx n' r0 r1) (FormalGroupSystem.K0 p)), IntS p (inParam p U) → ∃ U' : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p], (∀ m, ‖MvPowerSeries.coeff m U'‖ ≤ 1) ∧ MvPowerSeries.subst (fun v : ZMod n' × Fin r0 × Fin r1 => MvPowerSeries.C (1 : ℂ_[p]) * jetLogG p n' v) (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (inLetters (thOne B be U))) = U' * MvPowerSeries.subst (jetLogG p n' (β := Fin r0 × Fin r1)) (product_zeroth_first_parts.expS ℂ_[p] ((-1 : ℂ_[p]) • ∑ a : Fin r0, ∑ b : Fin r1, MvPowerSeries.subst (fun s : ZMod n' => (MvPowerSeries.X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p])) bv)) := by
  first | exact @GlobalTheory.OnePlace.exists_letterCoordinates_series_onePlace | exact GlobalTheory.OnePlace.exists_letterCoordinates_series_onePlace | (intros; apply GlobalTheory.OnePlace.exists_letterCoordinates_series_onePlace <;> assumption)
end
