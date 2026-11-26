module

public import Mathlib

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianSemidefiniteNullRadical
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianSemidefiniteNullRadical
open Matrix

namespace GlobalTheory.CompanionTheory.Herm

theorem apply_eq_zero_of_isotropic {V : Type} [AddCommGroup V] [Module ℂ V]
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (hs : ∀ v w, B w v = starRingEnd ℂ (B v w))
    (hp : ∀ v, 0 ≤ (B v v).re) (x : V) (hx : (B x x).re = 0) (w : V) : B x w = 0 := by
  obtain ⟨c, hc⟩ : ∃ c, c = B x w := ⟨_, rfl⟩
  have hwx : B w x = starRingEnd ℂ c := by rw [hc]; exact hs x w
  have key : ∀ t : ℝ, 0 ≤ -2 * t * Complex.normSq c
      + t ^ 2 * Complex.normSq c * (B w w).re := by
    intro t
    have h := hp (x - ((t : ℂ) * c) • w)
    have e : B (x - ((t : ℂ) * c) • w) (x - ((t : ℂ) * c) • w)
        = B x x - starRingEnd ℂ ((t : ℂ) * c) * c - ((t : ℂ) * c) * starRingEnd ℂ c
          + ((t : ℂ) * c) * starRingEnd ℂ ((t : ℂ) * c) * B w w := by
      simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.map_smulₛₗ, smul_eq_mul, ← hc, hwx]
      ring
    have e1 : starRingEnd ℂ ((t : ℂ) * c) * c = ((t * Complex.normSq c : ℝ) : ℂ) := by
      rw [map_mul, Complex.conj_ofReal, mul_assoc, mul_comm (starRingEnd ℂ c) c,
        Complex.mul_conj]
      push_cast; ring
    have e2 : ((t : ℂ) * c) * starRingEnd ℂ c = ((t * Complex.normSq c : ℝ) : ℂ) := by
      rw [mul_assoc, Complex.mul_conj]
      push_cast; ring
    have e3 : ((t : ℂ) * c) * starRingEnd ℂ ((t : ℂ) * c)
        = ((t ^ 2 * Complex.normSq c : ℝ) : ℂ) := by
      rw [Complex.mul_conj, Complex.normSq_mul, Complex.normSq_ofReal]
      push_cast; ring
    rw [e, e1, e2, e3] at h
    simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.re_ofReal_mul, hx] at h
    linarith
  by_contra hne
  have hc0 : c ≠ 0 := by rw [hc]; exact hne
  have hN : 0 < Complex.normSq c := Complex.normSq_pos.mpr hc0
  have hr : 0 ≤ (B w w).re := hp w
  obtain ⟨r, hrdef⟩ : ∃ r, r = (B w w).re := ⟨_, rfl⟩
  rw [← hrdef] at hr
  have hk := key (1 / (r + 1))
  rw [← hrdef] at hk
  have hr1 : 0 < r + 1 := by linarith
  have hid : -2 * (1 / (r + 1)) * Complex.normSq c
      + (1 / (r + 1)) ^ 2 * Complex.normSq c * r
      = -(Complex.normSq c * (r + 2)) / (r + 1) ^ 2 := by
    field_simp
    ring
  rw [hid] at hk
  have : -(Complex.normSq c * (r + 2)) / (r + 1) ^ 2 < 0 :=
    div_neg_of_neg_of_pos (by nlinarith) (by positivity)
  linarith

end GlobalTheory.CompanionTheory.Herm
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianSemidefiniteNullRadicalStatement
open Matrix
alias GlobalTheory.T.hermitian_semidefinite_null_radical := GlobalTheory.CompanionTheory.Herm.apply_eq_zero_of_isotropic
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCompactOpenSubgroupMem
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCompactOpenSubgroupMem
open Matrix ValuativeRel

namespace GlobalTheory.CompanionTheory.LatticePoint

theorem isOpen_valBall {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (γ : ValueGroupWithZero k) (hγ : γ ≠ 0) :
    IsOpen {x : k | valuation k x ≤ γ} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  change valuation k x ≤ γ at hx
  rw [IsValuativeTopology.mem_nhds_iff']
  refine ⟨Units.mk0 γ hγ, fun y hy => ?_⟩
  change valuation k (y - x) < ((Units.mk0 γ hγ : (ValueGroupWithZero k)ˣ) : ValueGroupWithZero k) at hy
  rw [Units.val_mk0] at hy
  show valuation k y ≤ γ
  calc valuation k y = valuation k ((y - x) + x) := by rw [sub_add_cancel]
    _ ≤ max (valuation k (y - x)) (valuation k x) := Valuation.map_add _ _ _
    _ ≤ γ := max_le hy.le hx

theorem exists_compact_open_addSubgroup_mem :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (n : ℕ) (x : Fin n → k),
      ∃ A : AddSubgroup (Fin n → k), IsCompact (A : Set (Fin n → k)) ∧
        IsOpen (A : Set (Fin n → k)) ∧ x ∈ A := by
  intro k _ _ _ _ n x
  let γ : ValueGroupWithZero k := Finset.univ.sup (fun i => valuation k (x i)) ⊔ 1
  have hγ : γ ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one le_sup_right)
  let S : AddSubgroup k :=
    { carrier := {y | valuation k y ≤ γ}
      add_mem' := fun {a b} ha hb => by
        change valuation k a ≤ γ at ha
        change valuation k b ≤ γ at hb
        show valuation k (a + b) ≤ γ
        exact (Valuation.map_add _ _ _).trans (max_le ha hb)
      zero_mem' := by
        show valuation k 0 ≤ γ
        simp
      neg_mem' := fun {a} ha => by
        change valuation k a ≤ γ at ha
        show valuation k (-a) ≤ γ
        rwa [Valuation.map_neg] }
  have hS : (S : Set k) = {y | valuation k y ≤ γ} := rfl
  refine ⟨AddSubgroup.pi Set.univ (fun _ => S), ?_, ?_, ?_⟩
  · rw [AddSubgroup.coe_pi, hS]
    exact isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k γ
  · rw [AddSubgroup.coe_pi, hS]
    exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_valBall γ hγ
  · rw [AddSubgroup.mem_pi]
    intro i _
    show valuation k (x i) ≤ γ
    exact le_sup_of_le_left (Finset.le_sup (f := fun i => valuation k (x i)) (Finset.mem_univ i))

end GlobalTheory.CompanionTheory.LatticePoint
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCompactOpenSubgroupMemStatement
open Matrix
alias GlobalTheory.T.exists_compact_open_subgroup_mem := GlobalTheory.CompanionTheory.LatticePoint.exists_compact_open_addSubgroup_mem
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EventuallyHaarDetEqOneNearOne
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DistribHaarCharEqOneOfValuationEqOne
open ValuativeRel MeasureTheory Matrix
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.LocalModule

theorem distribHaarChar_eq_one_of_valuation_eq_one :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (u : kˣ), valuation k (u : k) = 1 → distribHaarChar k u = 1 := by
  intro k _ _ _ _ u hu
  borelize k
  have hsc : IsCompact {x : k | valuation k x ≤ 1} :=
    IsNonarchimedeanLocalField.isCompact_closedBall k 1
  have hso : IsOpen {x : k | valuation k x ≤ 1} :=
    Valuation.isOpen_integer (v := valuation k)
  have hus : u • {x : k | valuation k x ≤ 1} = {x : k | valuation k x ≤ 1} := by
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    simp only [Set.mem_ofPred_eq, Units.smul_def, smul_eq_mul, map_mul, Units.val_inv_eq_inv_val,
      map_inv₀, hu, inv_one, one_mul]
  have h0 : (Measure.addHaar : Measure k) {x : k | valuation k x ≤ 1} ≠ 0 :=
    (hso.measure_pos Measure.addHaar ⟨0, by simp⟩).ne'
  have hfin : (Measure.addHaar : Measure k) {x : k | valuation k x ≤ 1} ≠ ⊤ := hsc.measure_lt_top.ne
  exact distribHaarChar_eq_of_measure_smul_eq_mul h0 hfin (by rw [hus, ENNReal.coe_one, one_mul])

end GlobalTheory.CompanionTheory.LocalModule
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EventuallyHaarDetEqOneNearOne
open Matrix ValuativeRel MeasureTheory
open scoped Topology

namespace GlobalTheory.CompanionTheory.LocalModule

theorem distribHaarChar_det_eventually_eq_one :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (n : ℕ), ∀ᶠ g in nhds (1 : GL (Fin n) k),
        MeasureTheory.distribHaarChar k (Matrix.GeneralLinearGroup.det g) = 1 := by
  intro k _ _ _ _ n
  have hc : Continuous fun g : GL (Fin n) k => ((Matrix.GeneralLinearGroup.det g : kˣ) : k) := by
    have : (fun g : GL (Fin n) k => ((Matrix.GeneralLinearGroup.det g : kˣ) : k)) =
        fun g : GL (Fin n) k => (g : Matrix (Fin n) (Fin n) k).det := rfl
    rw [this]
    exact Continuous.matrix_det Units.continuous_val
  have hO : IsOpen {x : k | valuation k (x - 1) < 1} := by
    have h : IsOpen {z : k | valuation k z < 1} := by simpa using (valuation k).isOpen_ball 1
    exact h.preimage (continuous_id.sub continuous_const)
  have hm : ∀ᶠ g in nhds (1 : GL (Fin n) k),
      ((Matrix.GeneralLinearGroup.det g : kˣ) : k) ∈ {x : k | valuation k (x - 1) < 1} := by
    refine hc.continuousAt.eventually (hO.mem_nhds ?_)
    simp
  filter_upwards [hm] with g hg
  refine distribHaarChar_eq_one_of_valuation_eq_one k _ ?_
  have hv : valuation k (((Matrix.GeneralLinearGroup.det g : kˣ) : k) - 1) < 1 := hg
  have h1 := Valuation.map_one_add_of_lt (valuation k) hv
  rwa [add_sub_cancel] at h1

end GlobalTheory.CompanionTheory.LocalModule
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EventuallyHaarDetEqOneNearOneStatement
open Matrix
open scoped Topology
alias GlobalTheory.T.eventually_haar_det_eq_one_near_one := GlobalTheory.CompanionTheory.LocalModule.distribHaarChar_det_eventually_eq_one
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsOpenCompactLatticeContaining
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsOpenCompactLatticeContaining
open Matrix
open scoped Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.LocalLattice

open ValuativeRel

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def ballSubgroup (k : Type) [Field k] [ValuativeRel k] (n : ℕ) (γ : ValueGroupWithZero k) :
    AddSubgroup (Fin n → k) where
  carrier := {x | ∀ i, valuation k (x i) ≤ γ}
  zero_mem' := fun i => by simp
  add_mem' := fun {a b} ha hb i =>
    (Valuation.map_add _ _ _).trans (max_le (ha i) (hb i))
  neg_mem' := fun {a} ha i => by simpa using ha i

theorem coe_ballSubgroup (n : ℕ) (γ : ValueGroupWithZero k) :
    (ballSubgroup k n γ : Set (Fin n → k)) =
      Set.univ.pi fun _ => {x : k | valuation k x ≤ γ} := by
  ext x
  simp only [Set.mem_univ_pi, Set.mem_setOf_eq]
  rfl

theorem isCompact_ballSubgroup (n : ℕ) (γ : ValueGroupWithZero k) :
    IsCompact (ballSubgroup k n γ : Set (Fin n → k)) := by
  rw [coe_ballSubgroup]
  exact isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k γ

theorem isOpen_ballSubgroup (n : ℕ) {γ : ValueGroupWithZero k} (hγ : γ ≠ 0) :
    IsOpen (ballSubgroup k n γ : Set (Fin n → k)) := by
  refine AddSubgroup.isOpen_of_mem_nhds (g := 0) _ ?_
  rw [GlobalTheory.CompanionTheory.LocalLattice.coe_ballSubgroup]
  refine set_pi_mem_nhds Set.finite_univ fun i _ => ?_
  exact (IsValuativeTopology.mem_nhds_zero_iff _).2
    ⟨Units.mk0 γ hγ, fun x (hx : valuation k x < γ) => hx.le⟩

theorem exists_compact_open_addSubgroup (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (K : Set (Fin n → k)) (hK : IsCompact K) :
    ∃ A : AddSubgroup (Fin n → k), IsCompact (A : Set (Fin n → k)) ∧
      IsOpen (A : Set (Fin n → k)) ∧ K ⊆ A := by
  have hne : ∀ γ : ValueGroupWithZero k, max γ 1 ≠ 0 :=
    fun γ => ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_right γ 1))
  have hmono : Monotone fun γ : ValueGroupWithZero k =>
      (GlobalTheory.CompanionTheory.LocalLattice.ballSubgroup k n (max γ 1) : Set (Fin n → k)) :=
    fun γ δ hγδ x hx i => (hx i).trans (max_le_max hγδ le_rfl)
  have hcover : K ⊆ ⋃ γ : ValueGroupWithZero k, (GlobalTheory.CompanionTheory.LocalLattice.ballSubgroup k n (max γ 1) : Set (Fin n → k)) := by
    intro x _
    obtain ⟨γ, hγ⟩ := Finite.exists_le fun i => valuation k (x i)
    exact Set.mem_iUnion.2 ⟨γ, fun i => (hγ i).trans (le_max_left γ 1)⟩
  obtain ⟨γ, hγ⟩ := hK.elim_directed_cover _
    (fun γ => GlobalTheory.CompanionTheory.LocalLattice.isOpen_ballSubgroup n (hne γ)) hcover hmono.directed_le
  exact ⟨_, GlobalTheory.CompanionTheory.LocalLattice.isCompact_ballSubgroup n _, GlobalTheory.CompanionTheory.LocalLattice.isOpen_ballSubgroup n (hne γ), hγ⟩

end GlobalTheory.CompanionTheory.LocalLattice
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsOpenCompactLatticeContainingStatement
open Matrix
open scoped Topology
alias GlobalTheory.T.exists_open_compact_lattice_containing := GlobalTheory.CompanionTheory.LocalLattice.exists_compact_open_addSubgroup
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLiftOfSurjKer
namespace GlobalTheory.CompanionTheory.ColimLift

variable {G : ℕ → Type} [∀ n, CommRing (G n)] (f : ∀ n, G n →+* G (n + 1))
  {L : Type} [CommRing L] (ι : ∀ n, G n →+* L)
  (t : ∀ n k, G n → G (n + k))

theorem apply_iter {T : Type} (y : ∀ n, G n → T)
    (t0 : ∀ n x, t n 0 x = x) (tS : ∀ n k x, t n (k + 1) x = f (n + k) (t n k x))
    (hy : ∀ n x, y (n + 1) (f n x) = y n x) (n k : ℕ) (x : G n) :
    y (n + k) (t n k x) = y n x := by
  induction k with
  | zero => exact congrArg (y n) (t0 n x)
  | succ k ih =>
    have h : y (n + (k + 1)) (t n (k + 1) x) = y (n + k + 1) (f (n + k) (t n k x)) :=
      congrArg (y (n + k + 1)) (tS n k x)
    rw [h, hy, ih]

theorem eq_of_same_stage {T : Type} [CommRing T] (y : ∀ n, G n →+* T)
    (t0 : ∀ n x, t n 0 x = x) (tS : ∀ n k x, t n (k + 1) x = f (n + k) (t n k x))
    (ker : ∀ n x, ι n x = 0 → ∃ k, t n k x = 0)
    (hy : ∀ n x, y (n + 1) (f n x) = y n x) (n : ℕ) (a b : G n) (h : ι n a = ι n b) :
    y n a = y n b := by
  obtain ⟨k, hk⟩ := ker n (a - b) (by rw [map_sub, h, sub_self])
  have h1 := apply_iter f t (fun n => (y n : G n → T)) t0 tS hy n k (a - b)
  simp only [hk, map_zero, map_sub] at h1
  exact sub_eq_zero.mp h1.symm

theorem eq_of_iota_eq {T : Type} [CommRing T] (y : ∀ n, G n →+* T)
    (hι : ∀ n x, ι (n + 1) (f n x) = ι n x)
    (t0 : ∀ n x, t n 0 x = x) (tS : ∀ n k x, t n (k + 1) x = f (n + k) (t n k x))
    (ker : ∀ n x, ι n x = 0 → ∃ k, t n k x = 0)
    (hy : ∀ n x, y (n + 1) (f n x) = y n x) (n m : ℕ) (a : G n) (b : G m)
    (h : ι n a = ι m b) : y n a = y m b := by
  have up : ∀ (n m : ℕ), n ≤ m → ∀ a : G n, ∃ a' : G m, ι m a' = ι n a ∧ y m a' = y n a := by
    intro n m hnm a
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
    exact ⟨t n k a, apply_iter f t (fun n => (ι n : G n → L)) t0 tS hι n k a,
      apply_iter f t (fun n => (y n : G n → T)) t0 tS hy n k a⟩
  obtain ⟨a', ha, hya⟩ := up n (max n m) (le_max_left _ _) a
  obtain ⟨b', hb, hyb⟩ := up m (max n m) (le_max_right _ _) b
  rw [← hya, ← hyb]
  exact eq_of_same_stage f ι t y t0 tS ker hy _ a' b' (by rw [ha, hb, h])

theorem exists_lift_of_surj_ker
    (hι : ∀ n x, ι (n + 1) (f n x) = ι n x)
    (t0 : ∀ n x, t n 0 x = x) (tS : ∀ n k x, t n (k + 1) x = f (n + k) (t n k x))
    (surj : ∀ (m : ℕ) (v : Fin m → L), ∃ n, ∃ w : Fin m → G n, ∀ i, ι n (w i) = v i)
    (ker : ∀ n x, ι n x = 0 → ∃ k, t n k x = 0)
    {T : Type} [CommRing T] (y : ∀ n, G n →+* T) (hy : ∀ n x, y (n + 1) (f n x) = y n x) :
    ∃ z : L →+* T, ∀ n x, z (ι n x) = y n x := by
  classical
  have key := eq_of_iota_eq f ι t y hι t0 tS ker hy
  have rep : ∀ l : L, ∃ n, ∃ a : G n, ι n a = l := fun l => by
    obtain ⟨n, w, hw⟩ := surj 1 (fun _ => l)
    exact ⟨n, w 0, hw 0⟩
  choose r s hs using rep
  let z : L → T := fun l => y (r l) (s l)
  have hz : ∀ n x, z (ι n x) = y n x := fun n x => key _ _ _ _ (hs _)
  have two : ∀ l₁ l₂ : L, ∃ n, ∃ a b : G n, ι n a = l₁ ∧ ι n b = l₂ := fun l₁ l₂ => by
    obtain ⟨n, w, hw⟩ := surj 2 ![l₁, l₂]
    exact ⟨n, w 0, w 1, hw 0, hw 1⟩
  refine ⟨{ toFun := z, map_one' := ?_, map_zero' := ?_, map_mul' := ?_, map_add' := ?_ }, hz⟩
  · have := hz 0 1
    simpa using this
  · intro l₁ l₂
    obtain ⟨n, a, b, rfl, rfl⟩ := two l₁ l₂
    rw [← map_mul, hz, hz, hz, map_mul]
  · have := hz 0 0
    simpa using this
  · intro l₁ l₂
    obtain ⟨n, a, b, rfl, rfl⟩ := two l₁ l₂
    rw [← map_add (f := _), hz, hz, hz, map_add (f := _)]

end GlobalTheory.CompanionTheory.ColimLift
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsIntegrallyClosedOfReducedQuotientLocalization
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsIntegrallyClosedOfReducedQuotientLocalization
namespace GlobalTheory.CompanionTheory.IntClosedAway

open Polynomial

theorem mem_span_of_eq_mul_integral {A K : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] (t a : A) (hred : IsReduced (A ⧸ Ideal.span {t})) (z : K)
    (hz : IsIntegral A z) (h : algebraMap A K a = algebraMap A K t * z) :
    a ∈ Ideal.span {t} := by
  obtain ⟨p, hp, hpz⟩ := hz
  have hinj := IsFractionRing.injective A K
  have h1 : (p.scaleRoots t).eval a = 0 := by
    apply hinj
    rw [map_zero, ← Polynomial.eval₂_at_apply, h, Polynomial.scaleRoots_eval₂_mul, hpz, mul_zero]
  have h2 : (p.scaleRoots t).map (Ideal.Quotient.mk (Ideal.span {t})) = X ^ p.natDegree := by
    have ht0 : Ideal.Quotient.mk (Ideal.span {t}) t = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self t)
    ext i
    rw [coeff_map, coeff_scaleRoots, coeff_X_pow, map_mul, map_pow, ht0]
    rcases lt_trichotomy i p.natDegree with hi | hi | hi
    · rw [if_neg hi.ne, zero_pow (by omega), mul_zero]
    · subst hi
      simp [hp.coeff_natDegree]
    · rw [if_neg hi.ne', coeff_eq_zero_of_natDegree_lt hi, map_zero, zero_mul]
  have h3 : Ideal.Quotient.mk (Ideal.span {t}) a ^ p.natDegree = 0 := by
    have h4 := congrArg (Ideal.Quotient.mk (Ideal.span {t})) h1
    rw [map_zero, ← Polynomial.eval₂_at_apply, ← Polynomial.eval_map, h2] at h4
    simpa using h4
  exact Ideal.Quotient.eq_zero_iff_mem.mp (IsReduced.eq_zero _ ⟨_, h3⟩)

theorem isIntegrallyClosed_of_away :
    ∀ (A : Type) [CommRing A] [IsDomain A] (t : A), t ≠ 0 → IsReduced (A ⧸ Ideal.span {t}) →
      IsIntegrallyClosed (Localization.Away t) → IsIntegrallyClosed A := by
  intro A _ _ t ht hred hcl
  have hle : Submonoid.powers t ≤ nonZeroDivisors A := powers_le_nonZeroDivisors_of_noZeroDivisors ht
  haveI : IsDomain (Localization.Away t) := IsLocalization.isDomain_localization hle
  let K := FractionRing A
  letI : Algebra (Localization.Away t) K :=
    (IsLocalization.lift (M := Submonoid.powers t) (g := algebraMap A K)
      (fun y => IsLocalization.map_units K (⟨y, hle y.2⟩ : nonZeroDivisors A))).toAlgebra
  haveI : IsScalarTower A (Localization.Away t) K :=
    IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.lift_eq _ x).symm
  haveI : IsFractionRing (Localization.Away t) K :=
    IsFractionRing.isFractionRing_of_isLocalization (Submonoid.powers t) (Localization.Away t) K hle
  rw [isIntegrallyClosed_iff K]
  intro x hx
  have hxB : IsIntegral (Localization.Away t) x := hx.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hxB
  obtain ⟨n, a, hna⟩ := IsLocalization.Away.surj t y
  have hxa : algebraMap A K a = x * algebraMap A K t ^ n := by
    have h5 := congrArg (algebraMap (Localization.Away t) K) hna
    rw [map_mul, map_pow, hy, ← IsScalarTower.algebraMap_apply A (Localization.Away t) K,
      ← IsScalarTower.algebraMap_apply A (Localization.Away t) K] at h5
    exact h5.symm
  have ht' : algebraMap A K t ≠ 0 := by
    exact (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr ht
  clear hna
  induction n generalizing a with
  | zero => exact ⟨a, by simpa using hxa⟩
  | succ n ih =>
    have hz : IsIntegral A (x * algebraMap A K t ^ n) := hx.mul (isIntegral_algebraMap.pow n)
    have hmem : a ∈ Ideal.span {t} :=
      mem_span_of_eq_mul_integral t a hred _ hz (by rw [hxa]; ring)
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp hmem
    refine ih b (mul_left_injective₀ ht' ?_)
    simp only [map_mul] at hxa
    simp only [hxa]
    ring

end GlobalTheory.CompanionTheory.IntClosedAway
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsIntegrallyClosedOfReducedQuotientLocalizationStatement
alias GlobalTheory.T.isIntegrallyClosed_of_reduced_quotient_localization := GlobalTheory.CompanionTheory.IntClosedAway.isIntegrallyClosed_of_away
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenAdditiveCharacterKernel
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenAdditiveCharacterKernel
open Matrix Filter Topology ValuativeRel

namespace GlobalTheory.CompanionTheory.LocalFieldChar

theorem circle_eq_one_of_forall_re_pow_pos (z : Circle)
    (h : ∀ n : ℕ, 0 < ((z ^ n : Circle) : ℂ).re) : z = 1 := by
  have hsq : ∀ w : Circle, (w : ℂ).re ^ 2 + (w : ℂ).im ^ 2 = 1 := by
    intro w
    have := Circle.normSq_coe w
    rw [Complex.normSq_apply] at this
    nlinarith
  by_contra hz
  have ha0 : (z : ℂ).re < 1 := by
    by_contra hge
    push_neg at hge
    have h2 := hsq z
    have him : (z : ℂ).im = 0 := by nlinarith [sq_nonneg (z : ℂ).im, sq_nonneg ((z : ℂ).re - 1)]
    have hre : (z : ℂ).re = 1 := by
      rw [him] at h2
      nlinarith
    exact hz (Circle.ext (Complex.ext (by simpa using hre) (by simpa using him)))
  set a : ℕ → ℝ := fun j => ((z ^ (2 ^ j) : Circle) : ℂ).re with ha
  have hstep : ∀ j, a (j + 1) = 2 * a j ^ 2 - 1 := by
    intro j
    have h2 := hsq (z ^ (2 ^ j))
    have hp : z ^ (2 ^ (j + 1)) = z ^ (2 ^ j) * z ^ (2 ^ j) := by
      rw [pow_succ, pow_mul, sq]
    simp only [ha]
    rw [hp, Circle.coe_mul, Complex.mul_re]
    nlinarith
  have hlow : ∀ j, (2 : ℝ) ^ j * (1 - (z : ℂ).re) ≤ 1 - a j := by
    intro j
    induction j with
    | zero => simp [ha]
    | succ j ih =>
      have hpos : 0 < a j := h _
      have hle : a j ≤ 1 := by
        have := hsq (z ^ (2 ^ j))
        have h3 : a j ^ 2 ≤ 1 := by
          simp only [ha]
          nlinarith [sq_nonneg ((z ^ (2 ^ j) : Circle) : ℂ).im]
        nlinarith
      rw [hstep, pow_succ]
      nlinarith
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (1 / (1 - (z : ℂ).re)) (by norm_num : (1 : ℝ) < 2)
  have hd : 0 < 1 - (z : ℂ).re := by linarith
  rw [div_lt_iff₀ hd] at hj
  have := hlow j
  have hpos : 0 < a j := h _
  linarith

theorem isOpen_addChar_ker : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ →
    IsOpen {x : k | ψ x = 1} := by
  intro k _ _ _ _ ψ hψ
  let H : AddSubgroup k :=
    { carrier := {x | ψ x = 1}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [AddChar.map_add_eq_mul, ha, hb, one_mul]
      zero_mem' := by simp
      neg_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [AddChar.map_neg_eq_inv, ha, inv_one] }
  have hV : IsOpen {z : Circle | 0 < (z : ℂ).re} :=
    isOpen_lt continuous_const (Complex.continuous_re.comp continuous_induced_dom)
  have hU : ψ ⁻¹' {z : Circle | 0 < (z : ℂ).re} ∈ 𝓝 (0 : k) :=
    (hV.preimage hψ).mem_nhds (by simp)
  obtain ⟨γ, hγ, hball⟩ := (IsValuativeTopology.hasBasis_nhds_zero' k).mem_iff.1 hU
  have hsmul : ∀ x : k, valuation k x < γ → ∀ n : ℕ, valuation k (n • x) < γ := by
    intro x hx n
    induction n with
    | zero => simpa using zero_lt_iff.2 hγ
    | succ n ih =>
      rw [succ_nsmul]
      exact Valuation.map_add_lt _ ih hx
  have hone : ∀ x : k, valuation k x < γ → x ∈ H := by
    intro x hx
    refine circle_eq_one_of_forall_re_pow_pos (ψ x) fun n => ?_
    have h1 : 0 < ((ψ (n • x) : Circle) : ℂ).re := hball (hsmul x hx n)
    rwa [AddChar.map_nsmul_eq_pow] at h1
  have hnh : (H : Set k) ∈ 𝓝 (0 : k) :=
    (IsValuativeTopology.hasBasis_nhds_zero' k).mem_iff.2 ⟨γ, hγ, fun x hx => hone x hx⟩
  exact H.isOpen_of_mem_nhds hnh

end GlobalTheory.CompanionTheory.LocalFieldChar
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenAdditiveCharacterKernelStatement
open Matrix
alias GlobalTheory.T.isOpen_additive_character_kernel := GlobalTheory.CompanionTheory.LocalFieldChar.isOpen_addChar_ker
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SemistableModelRingIsDomain
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SemistableModelRingIsDomain
namespace GlobalTheory.CompanionTheory.SemistableLocal


open MvPolynomial in
theorem irreducible_prod_X_sub_C (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (ϖ : O) (hϖ : Irreducible ϖ) (m' r : ℕ) (hr : 1 ≤ r) :
    Irreducible ((∏ i ∈ Finset.univ.filter (fun i : Fin (m' + 1) => (i : ℕ) < r), X i) - C ϖ :
      MvPolynomial (Fin (m' + 1)) O) := by
  set g : MvPolynomial (Fin m') O :=
    ∏ j ∈ Finset.univ.filter (fun j : Fin m' => (j : ℕ) + 1 < r), MvPolynomial.X j with hgdef
  have hprod : (∏ i ∈ Finset.univ.filter (fun i : Fin (m' + 1) => (i : ℕ) < r),
      (MvPolynomial.X i : MvPolynomial (Fin (m' + 1)) O))
      = MvPolynomial.X 0 * ∏ j ∈ Finset.univ.filter (fun j : Fin m' => (j : ℕ) + 1 < r),
          (MvPolynomial.X (Fin.succ j) : MvPolynomial (Fin (m' + 1)) O) := by
    rw [Finset.prod_filter, Finset.prod_filter, Fin.prod_univ_succ]
    have h0 : 0 < r := by omega
    simp [Fin.val_succ, h0]
  have hC : MvPolynomial.finSuccEquiv O m' (MvPolynomial.C ϖ) =
      Polynomial.C (MvPolynomial.C ϖ) := by
    have h := (MvPolynomial.finSuccEquiv O m').commutes ϖ
    rw [MvPolynomial.algebraMap_eq, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq] at h
    exact h
  have hϖ0 : (MvPolynomial.C ϖ : MvPolynomial (Fin m') O) ≠ 0 := by
    rw [Ne, MvPolynomial.C_eq_zero]; exact hϖ.ne_zero
  have hg0 : g ≠ 0 := by
    intro h
    have h1 := congrArg (MvPolynomial.eval (fun _ : Fin m' => (1 : O))) h
    simp [hgdef] at h1
  have hcop : ∀ a : MvPolynomial (Fin m') O, a ∣ g → a ∣ MvPolynomial.C ϖ → IsUnit a := by
    intro a hag hac
    obtain ⟨s, hs⟩ := hac
    have ha0 : a ≠ 0 := by rintro rfl; rw [zero_mul] at hs; exact hϖ0 hs
    have hs0 : s ≠ 0 := by rintro rfl; rw [mul_zero] at hs; exact hϖ0 hs
    have hdeg := MvPolynomial.totalDegree_mul_of_isDomain ha0 hs0
    rw [← hs, MvPolynomial.totalDegree_C] at hdeg
    have hda : a.totalDegree = 0 := by omega
    rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C] at hda
    rw [hda] at hag ⊢
    refine IsUnit.map MvPolynomial.C (isUnit_of_dvd_one ?_)
    have h1 := map_dvd (MvPolynomial.eval (fun _ : Fin m' => (1 : O))) hag
    simpa [hgdef] using h1
  have hirr : Irreducible (Polynomial.C g * Polynomial.X + Polynomial.C (-MvPolynomial.C ϖ) :
      Polynomial (MvPolynomial (Fin m') O)) := by
    have hdeg : (Polynomial.C g * Polynomial.X + Polynomial.C (-MvPolynomial.C ϖ) :
        Polynomial (MvPolynomial (Fin m') O)).natDegree = 1 := Polynomial.natDegree_linear hg0
    have key2 : ∀ c d : Polynomial (MvPolynomial (Fin m') O),
        Polynomial.C g * Polynomial.X + Polynomial.C (-MvPolynomial.C ϖ) = c * d →
          c.natDegree = 0 → IsUnit c := by
      intro c d hcd hc
      have hc' := Polynomial.eq_C_of_natDegree_eq_zero hc
      have hdvd : Polynomial.C (c.coeff 0) ∣
          Polynomial.C g * Polynomial.X + Polynomial.C (-MvPolynomial.C ϖ) := by
        rw [← hc']; exact ⟨d, hcd⟩
      rw [Polynomial.C_dvd_iff_dvd_coeff] at hdvd
      rw [hc']
      refine IsUnit.map Polynomial.C (hcop _ ?_ ?_)
      · simpa [Polynomial.coeff_C_mul_X, Polynomial.coeff_C] using hdvd 1
      · simpa [Polynomial.coeff_C_mul_X, Polynomial.coeff_C] using hdvd 0
    refine irreducible_iff.mpr ⟨?_, ?_⟩
    · intro hu
      have h0 := Polynomial.natDegree_eq_zero_of_isUnit hu
      omega
    · intro a b hab
      have ha0 : a ≠ 0 := by
        rintro rfl; rw [zero_mul] at hab; rw [hab] at hdeg; simp at hdeg
      have hb0 : b ≠ 0 := by
        rintro rfl; rw [mul_zero] at hab; rw [hab] at hdeg; simp at hdeg
      have hsum := Polynomial.natDegree_mul ha0 hb0
      rw [← hab, hdeg] at hsum
      rcases Nat.eq_zero_or_pos a.natDegree with h | h
      · exact Or.inl (key2 a b hab h)
      · exact Or.inr (key2 b a (by rw [hab, mul_comm]) (by omega))
  refine (MulEquiv.irreducible_iff (MvPolynomial.finSuccEquiv O m')).mp ?_
  rw [hprod, map_sub, map_mul, map_prod, MvPolynomial.finSuccEquiv_X_zero, hC]
  simp only [MvPolynomial.finSuccEquiv_X_succ]
  convert hirr using 1
  rw [hgdef, map_prod, map_neg]
  ring

theorem isDomain_quotient_prod_X_sub_C :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
      ∀ (m r : ℕ), 1 ≤ r → r ≤ m →
        IsDomain (MvPolynomial (Fin m) O ⧸ Ideal.span
          {(∏ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < r), MvPolynomial.X i) -
            MvPolynomial.C ϖ}) := by
  intro O _ _ _ ϖ hϖ m r hr hrm
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hirr := irreducible_prod_X_sub_C O ϖ hϖ m' r hr
  haveI : UniqueFactorizationMonoid (MvPolynomial (Fin (m' + 1)) O) :=
    MvPolynomial.uniqueFactorizationMonoid _
  have hp := UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr
  haveI := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
  exact Ideal.Quotient.isDomain _

end GlobalTheory.CompanionTheory.SemistableLocal
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SemistableModelRingIsDomainStatement
alias GlobalTheory.T.semistable_model_ring_isDomain := GlobalTheory.CompanionTheory.SemistableLocal.isDomain_quotient_prod_X_sub_C
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalContinuousSectionVecMulOrbit
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalContinuousSectionVecMulOrbit
open Matrix
open scoped Topology

namespace GlobalTheory.CompanionTheory.OrbitSection

section Shear

variable {k : Type} [Field k] {n : ℕ}

noncomputable def shear (j : Fin n) (c : k) (ζ ξ : Fin n → k) : Matrix (Fin n) (Fin n) k :=
  1 + c • vecMulVec (Pi.single j 1) (ξ - ζ)

theorem shear_mul_shear (j : Fin n) (ζ ξ : Fin n → k) (h0 : ζ j ≠ 0) (h1 : ξ j ≠ 0) :
    shear j (ζ j)⁻¹ ζ ξ * shear j (-(ξ j)⁻¹) ζ ξ = 1 := by
  have hE : vecMulVec (Pi.single j (1 : k)) (ξ - ζ) * vecMulVec (Pi.single j 1) (ξ - ζ)
      = (ξ j - ζ j) • vecMulVec (Pi.single j (1 : k)) (ξ - ζ) := by
    rw [vecMulVec_mul_vecMulVec, vecMulVec_smul]
    simp
  have hc : (ζ j)⁻¹ + -(ξ j)⁻¹ + (ζ j)⁻¹ * -(ξ j)⁻¹ * (ξ j - ζ j) = 0 := by
    field_simp
    ring
  have key : ∀ E : Matrix (Fin n) (Fin n) k, E * E = (ξ j - ζ j) • E →
      (1 + (ζ j)⁻¹ • E) * (1 + (-(ξ j)⁻¹) • E) = 1 := by
    intro E hEE
    have : (1 + (ζ j)⁻¹ • E) * (1 + (-(ξ j)⁻¹) • E)
        = 1 + ((ζ j)⁻¹ + -(ξ j)⁻¹ + (ζ j)⁻¹ * -(ξ j)⁻¹ * (ξ j - ζ j)) • E := by
      simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, hEE]
      module
    rw [this, hc, zero_smul, add_zero]
  exact key _ hE

theorem vecMul_shear (j : Fin n) (ζ ξ : Fin n → k) (h0 : ζ j ≠ 0) :
    ζ ᵥ* shear j (ζ j)⁻¹ ζ ξ = ξ := by
  have : ζ ᵥ* vecMulVec (Pi.single j (1 : k)) (ξ - ζ) = (ζ j) • (ξ - ζ) := by
    rw [vecMul_vecMulVec]
    simp
  rw [shear, vecMul_add, vecMul_one, vecMul_smul, this, smul_smul, inv_mul_cancel₀ h0, one_smul]
  abel

theorem shear_self (j : Fin n) (c : k) (ζ : Fin n → k) : shear j c ζ ζ = 1 := by
  simp [shear]


open scoped Classical in
open Classical in
noncomputable def orbitSection (j : Fin n) (ζ ξ : Fin n → k) : GL (Fin n) k :=
  if h : ζ j ≠ 0 ∧ ξ j ≠ 0 then
    ⟨shear j (ζ j)⁻¹ ζ ξ, shear j (-(ξ j)⁻¹) ζ ξ, shear_mul_shear j ζ ξ h.1 h.2,
      mul_eq_one_comm.mp (shear_mul_shear j ζ ξ h.1 h.2)⟩
  else 1

theorem coe_orbitSection (j : Fin n) (ζ ξ : Fin n → k) (h0 : ζ j ≠ 0) (h1 : ξ j ≠ 0) :
    (orbitSection j ζ ξ : Matrix (Fin n) (Fin n) k) = shear j (ζ j)⁻¹ ζ ξ := by
  rw [orbitSection, dite_eq_left ⟨h0, h1⟩]

theorem coe_orbitSection_inv (j : Fin n) (ζ ξ : Fin n → k) (h0 : ζ j ≠ 0) (h1 : ξ j ≠ 0) :
    ((orbitSection j ζ ξ)⁻¹ : (Matrix (Fin n) (Fin n) k)ˣ).val = shear j (-(ξ j)⁻¹) ζ ξ := by
  rw [orbitSection, dite_eq_left ⟨h0, h1⟩]
  rfl

end Shear

section Top

variable {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalDivisionRing k] {n : ℕ}

theorem continuousOn_shear (j : Fin n) (ζ : Fin n → k) {N : Set (Fin n → k)} {c : (Fin n → k) → k}
    (hc : ContinuousOn c N) : ContinuousOn (fun ξ => shear j (c ξ) ζ ξ) N := by
  refine continuousOn_pi.2 fun a => continuousOn_pi.2 fun b => ?_
  simp only [shear, Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, Pi.sub_apply, smul_eq_mul]
  refine continuousOn_const.add (hc.mul (continuousOn_const.mul ?_))
  exact ((continuous_apply b).sub continuous_const).continuousOn

theorem continuousOn_orbitSection (j : Fin n) (ζ : Fin n → k) (h0 : ζ j ≠ 0) :
    ContinuousOn (orbitSection j ζ) {ξ | ξ j ≠ 0} := by
  have hinv : ContinuousOn (fun ξ : Fin n → k => -(ξ j)⁻¹) {ξ | ξ j ≠ 0} :=
    (((continuous_apply j).continuousOn).inv₀ fun ξ h => h).neg
  rw [continuousOn_iff_continuous_restrict, Units.continuous_iff]
  refine ⟨(continuousOn_iff_continuous_restrict.1
      (continuousOn_shear j ζ (c := fun _ => (ζ j)⁻¹) continuousOn_const)).congr fun ξ => ?_,
    (continuousOn_iff_continuous_restrict.1 (continuousOn_shear j ζ hinv)).congr fun ξ => ?_⟩
  · exact (coe_orbitSection j ζ ξ.1 h0 ξ.2).symm
  · exact (coe_orbitSection_inv j ζ ξ.1 h0 ξ.2).symm

end Top

theorem exists_local_section : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ζ : Fin n → k), ζ ≠ 0 → ∃ N : Set (Fin n → k), IsOpen N ∧ ζ ∈ N ∧ ∃ f : (Fin n → k) → GL (Fin n) k, ContinuousOn f N ∧ f ζ = 1 ∧ ∀ ξ ∈ N, ζ ᵥ* (f ξ : Matrix (Fin n) (Fin n) k) = ξ := by
  intro k _ _ _ _ n ζ hζ
  haveI : T2Space k := by
    letI := IsTopologicalAddGroup.rightUniformSpace k
    haveI := isUniformAddGroup_of_addCommGroup (G := k)
    infer_instance
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hζ
  have hj' : ζ j ≠ 0 := hj
  refine ⟨{ξ | ξ j ≠ 0}, isOpen_ne.preimage (continuous_apply j), hj', orbitSection j ζ,
    continuousOn_orbitSection j ζ hj', ?_, fun ξ hξ => ?_⟩
  · apply Units.ext
    rw [coe_orbitSection j ζ ζ hj' hj', shear_self]
    rfl
  · rw [coe_orbitSection j ζ ξ hj' hξ, vecMul_shear j ζ ξ hj']

end GlobalTheory.CompanionTheory.OrbitSection
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalContinuousSectionVecMulOrbitStatement
open Matrix
open scoped Topology
alias GlobalTheory.T.local_continuous_section_vecMul_orbit := GlobalTheory.CompanionTheory.OrbitSection.exists_local_section
end
end
