module

public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.ReadWHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.GlueHoldsVar
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.DXEqDerivative
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.SubstMem

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.InvSerSub
namespace PI

def InvSerSub : Prop :=
  ∀ (K : Type) [Field K] (S : Subring K) (l ex : PowerSeries K),
    (∀ n, PowerSeries.coeff n l ∈ S) → PowerSeries.constantCoeff l = 0 → PowerSeries.coeff 1 l = 1 →
    PowerSeries.constantCoeff ex = 0 → PowerSeries.subst ex l = PowerSeries.X → ∀ n, PowerSeries.coeff n ex ∈ S

def WfLogL : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]),
    W.a₁ ∈ Wp p → W.a₂ ∈ Wp p → W.a₃ ∈ Wp p → W.a₄ ∈ Wp p → W.a₆ ∈ Wp p → AddIntG.IsWq W wq →
    CoefWf (AddIntG.flog W wq)

def WfLog : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq ex : PowerSeries ℂ_[p]),
    W.a₁ ∈ Wp p → W.a₂ ∈ Wp p → W.a₃ ∈ Wp p → W.a₄ ∈ Wp p → W.a₆ ∈ Wp p → AddIntG.IsWq W wq →
    PowerSeries.constantCoeff ex = 0 → PowerSeries.subst ex (AddIntG.flog W wq) = PowerSeries.X →
    CoefWf (AddIntG.flog W wq) ∧ CoefWf ex

end PI
end

section -- merged from Formalism.PeriodIntegrals.WfSubst
namespace PI

def SubstSub : Prop :=
  ∀ (A : Type) [CommRing A] (S : Subring A) (σ : Type) (f : PowerSeries A) (a : MvPowerSeries σ A),
    (∀ n, PowerSeries.coeff n f ∈ S) → (∀ n, MvPowerSeries.coeff n a ∈ S) →
    MvPowerSeries.constantCoeff a = 0 → ∀ n, MvPowerSeries.coeff n (PowerSeries.subst a f) ∈ S

def WfSubst : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (f : PowerSeries ℂ_[p]) (a : MvPowerSeries σ ℂ_[p]),
    CoefWf f → CoefWf a → MvPowerSeries.constantCoeff a = 0 → CoefWf (PowerSeries.subst a f)

end PI
end

section -- merged from Formalism.PeriodIntegrals.WfRing
namespace PI

def WfRing : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (f g : MvPowerSeries σ ℂ_[p]), CoefWf f → CoefWf g →
    CoefWf (f + g) ∧ CoefWf (f - g) ∧ CoefWf (f * g) ∧ ∀ c : ℂ_[p], InWf c → CoefWf (MvPowerSeries.C c * f)

end PI
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WittLogarithm
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittLogarithm.CoefWfIff
noncomputable section

namespace PI.WfLogWork

open PI.ExpIntWProof

theorem coefWf_iff {p : ℕ} [Fact p.Prime] (f : PowerSeries ℂ_[p]) :
    CoefWf (f : MvPowerSeries Unit ℂ_[p]) ↔ ∀ n, PowerSeries.coeff n f ∈ Wf p := by
  constructor
  · intro h n
    exact h (Finsupp.single () n)
  · intro h n
    have hn : n = Finsupp.single () (n ()) := by
      first
        | exact Finsupp.unique_single n
        | (ext; simp)
    rw [hn]
    exact h (n ())

theorem Wp_le_Wf {p : ℕ} [Fact p.Prime] {x : ℂ_[p]} (h : x ∈ Wp p) : x ∈ Wf p := by
  show PI.InWf x
  unfold PI.InWf
  exact ⟨0, by rw [pow_zero, one_mul]; exact h⟩

end PI.WfLogWork
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittLogarithm.WfLogOf
noncomputable section

namespace PI.WfLogWork

open PI.ExpIntWProof

theorem wfLog_of (hI : PI.InvSerSub) (hL : PI.WfLogL) : PI.WfLog := by
  intro p _ W wq ex h1 h2 h3 h4 h6 hq hex hsub
  have hfl : CoefWf (AddIntG.flog W wq) := hL p W wq h1 h2 h3 h4 h6 hq
  refine ⟨hfl, ?_⟩
  have hw0 : PowerSeries.constantCoeff wq = 1 := by
    simp only [AddIntG.IsWq] at hq
    have h := congrArg PowerSeries.constantCoeff hq
    simpa using h
  have hc0 : PowerSeries.constantCoeff (AddIntG.flog W wq) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, AddIntG.flog, PowerSeries.coeff_mk]
    simp
  have hc1 : PowerSeries.coeff 1 (AddIntG.flog W wq) = 1 := by
    clear hI hL h1 h2 h3 h4 h6 hex hsub hfl hc0 hq
    rw [AddIntG.flog, PowerSeries.coeff_mk]
    simp only [one_ne_zero, if_false, Nat.sub_self, Nat.cast_one, div_one,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, AddIntG.omegaW]
    rw [map_mul, PowerSeries.constantCoeff_inv]
    simp [hw0]
    rw [map_ofNat]
    norm_num
  let S : Subring ℂ_[p] :=
    { carrier := {x | InWf x}
      mul_mem' := by
        rintro a b ⟨k, hk⟩ ⟨k', hk'⟩
        refine ⟨k + k', ?_⟩
        have e : (p : ℂ_[p]) ^ (k + k') * (a * b) = ((p : ℂ_[p]) ^ k * a) * ((p : ℂ_[p]) ^ k' * b) := by
          ring
        rw [e]
        exact (Wp p).mul_mem hk hk'
      one_mem' := ⟨0, by simpa using (Wp p).one_mem⟩
      add_mem' := by
        rintro a b ⟨k, hk⟩ ⟨k', hk'⟩
        refine ⟨k + k', ?_⟩
        have e : (p : ℂ_[p]) ^ (k + k') * (a + b) =
            (p : ℂ_[p]) ^ k' * ((p : ℂ_[p]) ^ k * a) + (p : ℂ_[p]) ^ k * ((p : ℂ_[p]) ^ k' * b) := by
          ring
        rw [e]
        exact (Wp p).add_mem ((Wp p).mul_mem ((Wp p).pow_mem (natCast_mem (Wp p) p) _) hk)
          ((Wp p).mul_mem ((Wp p).pow_mem (natCast_mem (Wp p) p) _) hk')
      zero_mem' := ⟨0, by simpa using (Wp p).zero_mem⟩
      neg_mem' := by
        rintro a ⟨k, hk⟩
        exact ⟨k, by rw [mul_neg]; exact (Wp p).neg_mem hk⟩ }
  have hres := hI ℂ_[p] S (AddIntG.flog W wq) ex (fun n => hfl (Finsupp.single () n)) hc0 hc1 hex hsub
  intro n
  have hn : n = Finsupp.single () (n ()) := by
    ext
    simp
  rw [hn]
  exact hres (n ())

end PI.WfLogWork
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittLogarithm.FormalLogarithmHolds
noncomputable section

namespace PI.WfLogWork

open PI.ExpIntWProof PI.AddIntG.Wk

theorem mem_SerS_iff {K : Type*} [CommRing K] (S : Subring K) (f : PowerSeries K) :
    (f : MvPowerSeries Unit K) ∈ SerS S Unit ↔ ∀ n, PowerSeries.coeff n f ∈ S := by
  rw [mem_SerS]
  constructor
  · intro h n
    exact h _
  · intro h e
    have he : e = Finsupp.single () (e ()) := by
      ext u
      simp
    rw [he]
    exact h (e ())

variable {p : ℕ} [Fact p.Prime]

theorem C_memS {S : Subring ℂ_[p]} {a : ℂ_[p]} (ha : a ∈ S) :
    ((algebraMap ℂ_[p] (PowerSeries ℂ_[p]) a : PowerSeries ℂ_[p]) : MvPowerSeries Unit ℂ_[p]) ∈ SerS S Unit := by
  rw [mem_SerS_iff]
  intro n
  rw [Algebra.algebraMap_eq_smul_one, map_smul, PowerSeries.coeff_one, smul_eq_mul]
  split_ifs <;> simp [ha]

theorem X_memS (S : Subring ℂ_[p]) :
    ((PowerSeries.X : PowerSeries ℂ_[p]) : MvPowerSeries Unit ℂ_[p]) ∈ SerS S Unit := by
  rw [mem_SerS_iff]
  intro n
  rw [PowerSeries.coeff_X]
  split_ifs <;> simp

theorem Gv_memS {S : Subring ℂ_[p]} {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]}
    (h1 : W.a₁ ∈ S) (h2 : W.a₂ ∈ S) (h3 : W.a₃ ∈ S) (h4 : W.a₄ ∈ S) (h6 : W.a₆ ∈ S) (hW : AddIntG.IsWq W wq) :
    ((Gv W (PowerSeries.X : PowerSeries ℂ_[p]) (wser wq) : PowerSeries ℂ_[p]) : MvPowerSeries Unit ℂ_[p]) ∈
      SerS S Unit := by
  have hC : ∀ {a : ℂ_[p]}, a ∈ S →
      ((algebraMap ℂ_[p] (PowerSeries ℂ_[p]) a : PowerSeries ℂ_[p]) : MvPowerSeries Unit ℂ_[p]) ∈
        SerS S Unit := fun ha => C_memS ha
  have hX := X_memS (p := p) S
  have hw : (wq : MvPowerSeries Unit ℂ_[p]) ∈ SerS S Unit :=
    (mem_SerS_iff S wq).2 (wq_mem h1 h2 h3 h4 h6 hW)
  have h2m : (2 : MvPowerSeries Unit ℂ_[p]) ∈ SerS S Unit := by
    simpa using natCast_mem (SerS S Unit) 2
  have h3m : (3 : MvPowerSeries Unit ℂ_[p]) ∈ SerS S Unit := by
    simpa using natCast_mem (SerS S Unit) 3
  have hv := mul_mem (pow_mem hX 3) hw
  simp only [Gv, wser]
  exact sub_mem (add_mem (add_mem (add_mem (add_mem (mul_mem (hC h1) hX)
    (mul_mem (hC h2) (pow_mem hX 2))) (mul_mem (mul_mem h2m (hC h3)) hv))
    (mul_mem (mul_mem (mul_mem h2m (hC h4)) hX) hv))
    (mul_mem (mul_mem h3m (hC h6)) (pow_mem hv 2))) (one_mem _)

theorem omega_eq {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (hW : AddIntG.IsWq W wq) :
    AddIntG.omegaW W wq = (-Gv W (PowerSeries.X : PowerSeries ℂ_[p]) (wser wq))⁻¹ := by
  have h := omega_mul_Gv hW
  have hc : PowerSeries.constantCoeff (-Gv W (PowerSeries.X : PowerSeries ℂ_[p]) (wser wq)) ≠ 0 := by
    intro h0
    have e := congrArg PowerSeries.constantCoeff h
    rw [map_mul, map_neg, map_one] at e
    rw [map_neg, neg_eq_zero] at h0
    rw [h0, mul_zero] at e
    exact one_ne_zero (neg_eq_zero.1 e.symm)
  rw [PowerSeries.eq_inv_iff_mul_eq_one hc, mul_neg, h, neg_neg]

theorem omega_coeff_mem {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]}
    (h1 : W.a₁ ∈ Wp p) (h2 : W.a₂ ∈ Wp p) (h3 : W.a₃ ∈ Wp p) (h4 : W.a₄ ∈ Wp p) (h6 : W.a₆ ∈ Wp p)
    (hW : AddIntG.IsWq W wq) (n : ℕ) : PowerSeries.coeff n (AddIntG.omegaW W wq) ∈ Wp p := by
  have hG := Gv_memS h1 h2 h3 h4 h6 hW
  have hc : PowerSeries.constantCoeff (-Gv W (PowerSeries.X : PowerSeries ℂ_[p]) (wser wq)) = 1 := by
    simp [Gv, wser]
  have hinv := inv_mem_SerS (Wp p)
    (f := ((-Gv W (PowerSeries.X : PowerSeries ℂ_[p]) (wser wq) : PowerSeries ℂ_[p]) :
      MvPowerSeries Unit ℂ_[p])) hc (neg_mem hG)
  rw [omega_eq hW]
  exact (mem_SerS_iff (Wp p) _).1 hinv n

theorem formal_logarithm_holds : PI.WfLogL := by
  intro p _ W wq h1 h2 h3 h4 h6 hW
  rw [coefWf_iff]
  intro n
  rw [AddIntG.flog, PowerSeries.coeff_mk]
  split_ifs with hn
  · exact zero_mem _
  · rw [div_eq_mul_inv]
    exact mul_mem (Wp_le_Wf (omega_coeff_mem h1 h2 h3 h4 h6 hW (n - 1))) (inv_nat_mem_Wf p n hn)

end PI.WfLogWork
end
end

private lemma inv_series_sub : PI.InvSerSub := by
  intro K _ S l ex hl hl0 hl1 hex0 hsub n
  obtain ⟨c, hc⟩ := PowerSeries.X_dvd_iff.2 hex0
  have hpow : ∀ d m, PowerSeries.coeff m (ex ^ d) =
      if d ≤ m then PowerSeries.coeff (m - d) (c ^ d) else 0 := by
    intro d m
    rw [hc, mul_pow, PowerSeries.coeff_X_pow_mul']
  have hcoef : ∀ j, PowerSeries.coeff j c = PowerSeries.coeff (j + 1) ex := by
    intro j
    rw [hc, PowerSeries.coeff_succ_X_mul]
  have hHS : PowerSeries.HasSubst ex := by
    first
    | exact PowerSeries.HasSubst.of_constantCoeff_zero hex0
    | exact PowerSeries.HasSubst.of_constantCoeff_zero' hex0
    | exact PowerSeries.HasSubst.of_constantCoeff_nilpotent (by rw [hex0]; exact IsNilpotent.zero)
  have key : ∀ m, PowerSeries.coeff m (PowerSeries.X : PowerSeries K) =
      ∑ d ∈ Finset.range (m + 1), PowerSeries.coeff d l * PowerSeries.coeff m (ex ^ d) := by
    intro m
    have hfin : (∑ᶠ d, PowerSeries.coeff d l • PowerSeries.coeff m (ex ^ d)) =
        ∑ d ∈ Finset.range (m + 1), PowerSeries.coeff d l • PowerSeries.coeff m (ex ^ d) := by
      apply finsum_eq_sum_of_support_subset
      intro d hd
      simp only [Function.mem_support] at hd
      simp only [Finset.coe_range, Set.mem_Iio]
      by_contra h
      apply hd
      rw [hpow, if_neg (by omega), smul_zero]
    rw [← hsub, PowerSeries.coeff_subst' hHS, hfin]
    simp only [smul_eq_mul]

  have hB : ∀ N, (∀ j ≤ N, PowerSeries.coeff j c ∈ S) →
      ∀ d, ∀ i ≤ N, PowerSeries.coeff i (c ^ d) ∈ S := by
    intro N hN d
    induction d with
    | zero =>
      intro i _
      rw [pow_zero, PowerSeries.coeff_one]
      split_ifs
      · exact S.one_mem
      · exact S.zero_mem
    | succ d ihd =>
      intro i hi
      rw [pow_succ, PowerSeries.coeff_mul]
      apply Subring.sum_mem
      intro p hp
      have h : p.1 + p.2 = i := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
      exact S.mul_mem (ihd _ (by omega)) (hN _ (by omega))
  have hl0' : PowerSeries.coeff 0 l = 0 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hl0]
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hex0]
      exact S.zero_mem
    · have k := key (n + 1)
      rw [Finset.sum_range_succ', Finset.sum_range_succ'] at k
      simp only [zero_add, pow_one, hl1, one_mul, hl0', zero_mul, add_zero] at k
      have he : PowerSeries.coeff (n + 1) ex = PowerSeries.coeff (n + 1) (PowerSeries.X : PowerSeries K) -
          ∑ i ∈ Finset.range n, PowerSeries.coeff (i + 1 + 1) l *
            PowerSeries.coeff (n + 1) (ex ^ (i + 1 + 1)) := by
        rw [k]
        ring
      rw [he]
      apply S.sub_mem
      · rw [PowerSeries.coeff_X]
        split_ifs
        · exact S.one_mem
        · exact S.zero_mem
      · apply Subring.sum_mem
        intro i hi
        rw [Finset.mem_range] at hi
        apply S.mul_mem (hl _)
        rw [hpow]
        split_ifs with hle
        · apply hB (n - 1) _ (i + 1 + 1) _ (by omega)
          intro j hj
          rw [hcoef]
          exact ih _ (by omega)
        · exact S.zero_mem

theorem witt_logarithm : PI.WfLog :=
  PI.WfLogWork.wfLog_of inv_series_sub PI.WfLogWork.formal_logarithm_holds
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WfSubst
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittSubstitution.CoeffMapMem
noncomputable section

namespace PI.WfSubstProof

theorem exists_lift {A : Type} [CommRing A] (S : Subring A) {σ : Type} (f : MvPowerSeries σ A)
    (h : ∀ e, MvPowerSeries.coeff e f ∈ S) :
    ∃ g : MvPowerSeries σ S, MvPowerSeries.map S.subtype g = f := by
  let g : MvPowerSeries σ S := fun e => ⟨MvPowerSeries.coeff e f, h e⟩
  refine ⟨g, ?_⟩
  ext e
  rw [MvPowerSeries.coeff_map]
  rfl

theorem coeff_map_mem {A : Type} [CommRing A] (S : Subring A) {σ : Type} (g : MvPowerSeries σ S)
    (e : σ →₀ ℕ) : MvPowerSeries.coeff e (MvPowerSeries.map S.subtype g) ∈ S := by
  rw [MvPowerSeries.coeff_map]
  exact (MvPowerSeries.coeff e g).2

theorem substSub : PI.SubstSub := by
  intro A _ S σ f a hf ha ha0 n
  have hf' : ∀ e : Unit →₀ ℕ, MvPowerSeries.coeff e f ∈ S := fun e => by
    have he : e = Finsupp.single () (e ()) := by
      ext
      simp
    rw [he]
    exact hf (e ())
  obtain ⟨fS, rfl⟩ := exists_lift S f hf'
  obtain ⟨aS, rfl⟩ := exists_lift S a ha
  have haS0 : MvPowerSeries.constantCoeff aS = 0 := by
    have h0 := ha0
    rw [MvPowerSeries.constantCoeff_map] at h0
    exact Subtype.val_injective h0
  have hsub : PowerSeries.HasSubst aS := PowerSeries.HasSubst.of_constantCoeff_zero haS0
  have key : PowerSeries.subst (MvPowerSeries.map S.subtype aS) (MvPowerSeries.map S.subtype fS : PowerSeries A) =
      MvPowerSeries.map S.subtype (PowerSeries.subst aS fS) :=
    (PowerSeries.map_subst hsub fS).symm
  rw [key]
  exact coeff_map_mem S _ n

theorem wfSubst : PI.WfSubst := by
  intro p _ σ f a hf ha ha0 n
  have h := substSub ℂ_[p] (ExpIntWProof.Wf p) σ f a (fun m => ExpIntWProof.mem_Wf.2 (hf _))
    (fun m => ExpIntWProof.mem_Wf.2 (ha m)) ha0
  exact ExpIntWProof.mem_Wf.1 (h n)

end PI.WfSubstProof
end
end

theorem witt_substitution : PI.WfSubst := PI.WfSubstProof.wfSubst
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WfRing
private theorem exists_pow_mul_add_mem_subring {R : Type*} [CommRing R] (S : Subring R) (q : R) (hq : q ∈ S) {a b : R}
    (ha : ∃ k : ℕ, q ^ k * a ∈ S) (hb : ∃ k : ℕ, q ^ k * b ∈ S) : ∃ k : ℕ, q ^ k * (a + b) ∈ S := by
  obtain ⟨i, hi⟩ := ha
  obtain ⟨j, hj⟩ := hb
  refine ⟨i + j, ?_⟩
  have e : q ^ (i + j) * (a + b) = q ^ j * (q ^ i * a) + q ^ i * (q ^ j * b) := by ring
  rw [e]
  exact S.add_mem (S.mul_mem (S.pow_mem hq _) hi) (S.mul_mem (S.pow_mem hq _) hj)

private theorem exists_pow_mul_sub_mem_subring {R : Type*} [CommRing R] (S : Subring R) (q : R) (hq : q ∈ S) {a b : R}
    (ha : ∃ k : ℕ, q ^ k * a ∈ S) (hb : ∃ k : ℕ, q ^ k * b ∈ S) : ∃ k : ℕ, q ^ k * (a - b) ∈ S := by
  obtain ⟨i, hi⟩ := ha
  obtain ⟨j, hj⟩ := hb
  refine ⟨i + j, ?_⟩
  have e : q ^ (i + j) * (a - b) = q ^ j * (q ^ i * a) - q ^ i * (q ^ j * b) := by ring
  rw [e]
  exact S.sub_mem (S.mul_mem (S.pow_mem hq _) hi) (S.mul_mem (S.pow_mem hq _) hj)

private theorem exists_pow_mul_mul_mem_subring {R : Type*} [CommRing R] (S : Subring R) {q a b : R}
    (ha : ∃ k : ℕ, q ^ k * a ∈ S) (hb : ∃ k : ℕ, q ^ k * b ∈ S) : ∃ k : ℕ, q ^ k * (a * b) ∈ S := by
  obtain ⟨i, hi⟩ := ha
  obtain ⟨j, hj⟩ := hb
  refine ⟨i + j, ?_⟩
  have e : q ^ (i + j) * (a * b) = (q ^ i * a) * (q ^ j * b) := by ring
  rw [e]
  exact S.mul_mem hi hj

private theorem exists_pow_mul_finset_sum_mem_subring {R : Type*} [CommRing R] (S : Subring R) (q : R) (hq : q ∈ S) {ι : Type*}
    (s : Finset ι) (f : ι → R) (h : ∀ i ∈ s, ∃ k : ℕ, q ^ k * f i ∈ S) :
    ∃ k : ℕ, q ^ k * ∑ i ∈ s, f i ∈ S := by
  classical
  revert h
  refine Finset.induction_on s (fun _ => ⟨0, by simp⟩) ?_
  intro a s ha ih h
  rw [Finset.sum_insert ha]
  exact exists_pow_mul_add_mem_subring S q hq (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem witt_ring_structure : PI.WfRing := by
  classical
  intro p _ σ f g hf hg
  delta PI.CoefWf PI.InWf at hf hg ⊢
  have hq : (p : ℂ_[p]) ∈ PI.Wp p := natCast_mem (PI.Wp p) p
  refine ⟨fun n => ?_, fun n => ?_, fun n => ?_, fun c hc n => ?_⟩
  · rw [map_add (f := _)]
    exact exists_pow_mul_add_mem_subring _ _ hq (hf n) (hg n)
  · rw [map_sub]
    exact exists_pow_mul_sub_mem_subring _ _ hq (hf n) (hg n)
  · rw [MvPowerSeries.coeff_mul]
    exact exists_pow_mul_finset_sum_mem_subring _ _ hq _ _ fun x _ => exists_pow_mul_mul_mem_subring _ (hf x.1) (hg x.2)
  · rw [MvPowerSeries.coeff_C_mul]
    exact exists_pow_mul_mul_mem_subring _ hc (hf n)
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WittFrobeniusEnd
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittEndomorphism.WfEndOfLog
section -- merged from Formalism.PeriodIntegrals.W2pair
noncomputable section

namespace PI

def WfEndDefs.W2pair (p : ℕ) [Fact p.Prime] : Set (ℂ_[p] × ℂ_[p]) :=
  closure (Subring.closure {x : ℂ_[p] × ℂ_[p] | ∃ ζ : ℂ_[p], ζ ^ (p ^ 2 - 1) = 1 ∧ x = (ζ, ζ ^ p)} :
    Set (ℂ_[p] × ℂ_[p]))

def mulBy {p : ℕ} [Fact p.Prime] {σ : Type*} (l ex : PowerSeries ℂ_[p]) (c : ℂ_[p]) (a : MvPowerSeries σ ℂ_[p]) :
    MvPowerSeries σ ℂ_[p] :=
  PowerSeries.subst (MvPowerSeries.C c * PowerSeries.subst a l) ex

def PairW : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], ∀ α ∈ WfEndDefs.W2pair p, α.1 ∈ Wp p

def WfEnd : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq ex : PowerSeries ℂ_[p]),
    W.a₁ ∈ Wp p → W.a₂ ∈ Wp p → W.a₃ ∈ Wp p → W.a₄ ∈ Wp p → W.a₆ ∈ Wp p → AddIntG.IsWq W wq →
    PowerSeries.constantCoeff ex = 0 → PowerSeries.subst ex (AddIntG.flog W wq) = PowerSeries.X →
    ∀ c : ℂ_[p], InWf c →
      IntegralMv (mulBy (AddIntG.flog W wq) ex c (MvPowerSeries.X ()) : MvPowerSeries Unit ℂ_[p]) →
      IntegralW (mulBy (AddIntG.flog W wq) ex c (MvPowerSeries.X ()) : MvPowerSeries Unit ℂ_[p])

end PI

end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittEndomorphism.FlogConstantCoeff
noncomputable section

namespace PI.WfEndProof

open PI

theorem flog_constantCoeff' {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    PowerSeries.constantCoeff (AddIntG.flog W wq) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, AddIntG.flog, PowerSeries.coeff_mk]
  simp

theorem coefWf_X (p : ℕ) [Fact p.Prime] : CoefWf (MvPowerSeries.X () : MvPowerSeries Unit ℂ_[p]) := by
  intro n
  refine ⟨0, ?_⟩
  rw [pow_zero, one_mul, MvPowerSeries.coeff_X]
  split_ifs
  · exact (Wp p).one_mem
  · exact (Wp p).zero_mem

theorem wfEnd_of (hR : WfRing) (hS : WfSubst) (hL : WfLog) : WfEnd := by
  intro p _ W wq ex h1 h2 h3 h4 h6 hW hex hsub c hc hI n
  obtain ⟨hl, hx⟩ := hL p W wq ex h1 h2 h3 h4 h6 hW hex hsub
  have hX : CoefWf (MvPowerSeries.X () : MvPowerSeries Unit ℂ_[p]) := coefWf_X p
  have hX0 : MvPowerSeries.constantCoeff (MvPowerSeries.X () : MvPowerSeries Unit ℂ_[p]) = 0 := by simp
  have hA := hS p Unit (AddIntG.flog W wq) (MvPowerSeries.X ()) hl hX hX0
  have hB := (hR p Unit _ _ hA hA).2.2.2 c hc
  have hB0 : MvPowerSeries.constantCoeff (MvPowerSeries.C c *
      PowerSeries.subst (MvPowerSeries.X () : MvPowerSeries Unit ℂ_[p]) (AddIntG.flog W wq)) = 0 := by
    rw [map_mul, PowerSeries.constantCoeff_subst_eq_zero hX0 _ (flog_constantCoeff' W wq), mul_zero]
  have hM := hS p Unit ex _ hx hB hB0
  exact PI.ExpIntWProof.stepIII_of_key PI.ExpIntWProof.keyW p _ (hM n) (hI n)

theorem coprime_sq_sub_one (p : ℕ) [hp : Fact p.Prime] : Nat.Coprime (p ^ 2 - 1) p := by
  have hp' := hp.out
  refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp').2 ?_)
  intro h
  have h2 : p ∣ p ^ 2 := dvd_pow_self p two_ne_zero
  have h3 : p ∣ p ^ 2 - (p ^ 2 - 1) := Nat.dvd_sub h2 h
  have h4 : p ^ 2 - (p ^ 2 - 1) = 1 := by
    have : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp'.pos
    omega
  rw [h4] at h3
  exact hp'.one_lt.ne' (Nat.dvd_one.1 h3)

theorem pairW : PairW := by
  intro p _ α hα
  have hpos : 0 < p ^ 2 - 1 := by
    have := (Fact.out : p.Prime).two_le
    have : 4 ≤ p ^ 2 := by nlinarith
    omega
  have hle : Subring.closure {x : ℂ_[p] × ℂ_[p] | ∃ ζ : ℂ_[p], ζ ^ (p ^ 2 - 1) = 1 ∧ x = (ζ, ζ ^ p)} ≤
      (Wp p).comap (RingHom.fst ℂ_[p] ℂ_[p]) := by
    rw [Subring.closure_le]
    rintro _ ⟨ζ, hζ, rfl⟩
    show ζ ∈ (Subring.closure {ζ : ℂ_[p] | ∃ n : ℕ, 0 < n ∧ Nat.Coprime n p ∧ ζ ^ n = 1}).topologicalClosure
    exact Subring.le_topologicalClosure _ (Subring.subset_closure ⟨_, hpos, coprime_sq_sub_one p, hζ⟩)
  have hclosed : IsClosed (Prod.fst ⁻¹' (Wp p : Set ℂ_[p])) :=
    IsClosed.preimage (continuous_fst : Continuous (Prod.fst : ℂ_[p] × ℂ_[p] → ℂ_[p])) (show IsClosed (Wp p : Set ℂ_[p]) from Subring.isClosed_topologicalClosure _)
  exact closure_minimal (fun x hx => hle hx) hclosed hα

end PI.WfEndProof

end
end

namespace PI.WfEndProof

theorem wfEnd_of_log (hL : WfLog) : WfEnd := wfEnd_of witt_ring_structure witt_substitution hL

end PI.WfEndProof
end

theorem witt_pairing : PI.PairW := PI.WfEndProof.pairW

theorem witt_frobenius_end : PI.WfEnd := PI.WfEndProof.wfEnd_of_log witt_logarithm

theorem wfEnd_of : PI.WfRing → PI.WfSubst → PI.WfLog → PI.WfEnd := PI.WfEndProof.wfEnd_of
end

namespace Formalism.MainNotions.Ext

theorem substWf_holds : SubstWf :=
  fun p _ σ f a hf ha h0 => witt_substitution p σ f a hf (fun n => ⟨0, by rw [pow_zero, one_mul]; exact ha n⟩) h0

theorem coefWfRing_holds : CoefWfRing := witt_ring_structure

theorem endIntWG_holds : EndIntWG :=
  fun p _ g hOk hW α hα hI =>
    witt_frobenius_end p g.W g.wq g.ex hW.1 hW.2.1 hW.2.2.1 hW.2.2.2.1 hW.2.2.2.2 hOk.2.1 hOk.2.2.1 hOk.2.2.2 α.1
      ⟨0, by simpa using witt_pairing p α hα⟩ hI

end Formalism.MainNotions.Ext
