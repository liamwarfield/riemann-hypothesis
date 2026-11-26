module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylLatticeSubstIncreasingMapStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridInvarianceOfRankOneTwo
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsIsoMorphismRestrictOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylRestrictionLatticeTensorOfSubstitutionSt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylLeviProjectionDenominatorsOfHypotheses

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointActionEndomorphismWeightBound
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointActionEndomorphismWeightBound
open GlobalTheory.LeviCut

namespace GlobalTheory.LeviCut

theorem adj_sub_of_adjBdd {A : Type} [Ring A] [Algebra ℚ A] (x y : A) : adj (x - y) = adj x - adj y := by
  ext T
  simp only [adj, LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
  noncomm_ring

theorem adj_zero_of_adjBdd {A : Type} [Ring A] [Algebra ℚ A] : adj (0 : A) = 0 := by
  ext T
  simp [adj]

theorem adj_commutator_of_adjBdd {A : Type} [Ring A] [Algebra ℚ A] (x y : A) :
    adj x * adj y - adj y * adj x = adj (x * y - y * x) := by
  ext T
  simp only [adj, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
    map_sub]
  noncomm_ring

theorem adjBdd_holds : AdjBdd := by
  intro V _ _ N K e hrel hbdd hspan
  constructor
  · intro a b c d ha hb hc hd
    rw [adj_commutator_of_adjBdd, hrel a b c d ha hb hc hd, adj_sub_of_adjBdd]
    split_ifs <;> simp [adj_zero_of_adjBdd]
  · intro a ha b hb n T hT hn
    have hw : ∀ x ∈ {x : V | ∃ μ : ℕ → ℤ, IsWt N e μ x}, T x = (0 : Module.End ℚ V) x := by
      rintro x ⟨μ, hμ⟩
      simp only [LinearMap.zero_apply]
      by_cases hx : x = 0
      · simp [hx]
      have h1 : μ b - μ a ≤ K := by
        by_contra hlt
        push_neg at hlt
        apply hx
        apply hbdd b hb a ha (μ b - μ a) x _ hlt
        rw [hμ b hb, hμ a ha]
        push_cast
        rw [sub_smul]
      apply hbdd a ha b hb (μ a - μ b + n) (T x) _ (by push_cast at hn h1 ⊢; omega)
      have eq := LinearMap.congr_fun hT x
      simp only [adj, LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
        Module.End.mul_apply, LinearMap.smul_apply, hμ a ha, hμ b hb, map_smul] at eq
      push_cast
      rw [add_smul, sub_smul, ← eq]
      abel
    exact LinearMap.ext_on hspan hw

end GlobalTheory.LeviCut
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointActionEndomorphismWeightBoundStatement
open GlobalTheory.LeviCut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjoint_action_endomorphism_weight_bound : GlobalTheory.LeviCut.AdjBdd := by
  first | exact @GlobalTheory.LeviCut.adjBdd_holds | exact GlobalTheory.LeviCut.adjBdd_holds | (intros; apply GlobalTheory.LeviCut.adjBdd_holds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectorGridScalarOfProjectorScalar
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectorGridScalarOfProjectorScalar
open GlobalTheory.LeviCut

noncomputable section

namespace GlobalTheory.LeviCut.GridScalarProof

variable {V : Type} [AddCommGroup V] [Module ℚ V]

def vanSub (N : ℕ) (e : ℕ → ℕ → Module.End ℚ V) (lam : ℕ → ℤ) (s : Finset ℕ) :
    Submodule ℚ (Module.End ℚ V) where
  carrier := {U | ∀ (μ : ℕ → ℤ) (x : V), IsWt N e μ x → ∑ c ∈ s, μ c < ∑ c ∈ s, lam c → U x = 0}
  add_mem' := by
    intro U W hU hW μ x hx hlt
    simp [hU μ x hx hlt, hW μ x hx hlt]
  zero_mem' := by
    intro μ x _ _
    simp
  smul_mem' := by
    intro r U hU μ x hx hlt
    simp [hU μ x hx hlt]

theorem mem_vanSub {N : ℕ} {e : ℕ → ℕ → Module.End ℚ V} {lam : ℕ → ℤ} {s : Finset ℕ} {U : Module.End ℚ V} :
    U ∈ vanSub N e lam s ↔ ∀ (μ : ℕ → ℤ) (x : V), IsWt N e μ x → ∑ c ∈ s, μ c < ∑ c ∈ s, lam c → U x = 0 :=
  Iff.rfl

theorem isWt_shift {N : ℕ} {e : ℕ → ℕ → Module.End ℚ V} (he : GlRel N e) {c d : ℕ} (hc : c < N) (hd : d < N)
    {μ : ℕ → ℤ} {x : V} (hx : IsWt N e μ x) :
    IsWt N e (fun k => μ k + ((if k = c then 1 else 0) - (if k = d then 1 else 0))) (e c d x) := by
  intro k hk
  have h := congrArg (fun f : Module.End ℚ V => f x) (he k k c d hk hk hc hd)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  rw [sub_eq_iff_eq_add] at h
  rw [h, hx k hk, map_smul]
  by_cases hkc : k = c <;> by_cases hkd : k = d
  · subst hkc; subst hkd; simp
  · subst hkc; simp [hkd, Ne.symm hkd]; module
  · subst hkd; simp [hkc]; module
  · simp [hkc, hkd, Ne.symm hkd]

theorem sum_shift (s : Finset ℕ) (μ : ℕ → ℤ) (c d : ℕ) :
    ∑ k ∈ s, (μ k + ((if k = c then 1 else 0) - (if k = d then 1 else 0))) =
      ∑ k ∈ s, μ k + ((if c ∈ s then 1 else 0) - (if d ∈ s then 1 else 0)) := by
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']

theorem adj_mem_vanSub {N : ℕ} {e : ℕ → ℕ → Module.End ℚ V} {lam : ℕ → ℤ} {s : Finset ℕ} (he : GlRel N e)
    {c d : ℕ} (hc : c < N) (hd : d < N) (hs : c ∈ s ↔ d ∈ s) {U : Module.End ℚ V}
    (hU : U ∈ vanSub N e lam s) : adj (e c d) U ∈ vanSub N e lam s := by
  rw [mem_vanSub] at hU ⊢
  intro μ x hx hlt
  have h2 : ∑ k ∈ s, (μ k + ((if k = c then 1 else 0) - (if k = d then 1 else 0))) < ∑ k ∈ s, lam k := by
    rw [sum_shift]
    by_cases h : c ∈ s
    · simp [h, hs.mp h, hlt]
    · simp [h, mt hs.mpr h, hlt]
  simp only [adj, LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply, Module.End.mul_apply]
  rw [hU μ x hx hlt, map_zero, hU _ _ (isWt_shift he hc hd hx) h2, sub_zero]

theorem pow_mem_of {M : Type} [AddCommGroup M] [Module ℚ M] {S : Submodule ℚ M} {P : Module.End ℚ M}
    (hP : ∀ U ∈ S, P U ∈ S) (k : ℕ) : ∀ U ∈ S, (P ^ k) U ∈ S := by
  induction k with
  | zero => intro U hU; simpa using hU
  | succ k ih => intro U hU; rw [pow_succ, Module.End.mul_apply]; exact ih _ (hP U hU)

theorem proj_mem {M : Type} [AddCommGroup M] [Module ℚ M] {S : Submodule ℚ M} {P Q : Module.End ℚ M}
    (hP : ∀ U ∈ S, P U ∈ S) (hQ : ∀ U ∈ S, Q U ∈ S) (K j : ℕ) : ∀ U ∈ S, proj K j P Q U ∈ S := by
  intro U hU
  simp only [proj, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (pow_mem_of hQ k _ (pow_mem_of hP k U hU))

theorem listProd_mem {M : Type} [AddCommGroup M] [Module ℚ M] {S : Submodule ℚ M} (L : List (Module.End ℚ M))
    (hL : ∀ f ∈ L, ∀ U ∈ S, f U ∈ S) : ∀ U ∈ S, L.prod U ∈ S := by
  induction L with
  | nil => intro U hU; simpa using hU
  | cons f L ih =>
    intro U hU
    rw [List.prod_cons, Module.End.mul_apply]
    exact hL f (by simp) _ (ih (fun g hg => hL g (by simp [hg])) U hU)

theorem rootP_mem {N : ℕ} {e : ℕ → ℕ → Module.End ℚ V} {lam : ℕ → ℤ} {s : Finset ℕ} (he : GlRel N e)
    {i j : ℕ} (hi : i < N) (hj : j < N) (hs : i ∈ s ↔ j ∈ s) (K : ℕ) :
    ∀ U ∈ vanSub N e lam s, rootP (fun c d => adj (e c d)) K i j U ∈ vanSub N e lam s :=
  proj_mem (fun U hU => adj_mem_vanSub he hi hj hs hU) (fun U hU => adj_mem_vanSub he hj hi hs.symm hU) _ _

theorem rowP_mem {N : ℕ} {e : ℕ → ℕ → Module.End ℚ V} {lam : ℕ → ℤ} {t : Finset ℕ} (he : GlRel N e)
    {i s n : ℕ} (hi : i < N) (hsn : s + n ≤ N) (hS : ∀ j, s ≤ j → j < s + n → (i ∈ t ↔ j ∈ t)) (K : ℕ) :
    ∀ U ∈ vanSub N e lam t, rowP (fun c d => adj (e c d)) K i s n U ∈ vanSub N e lam t := by
  unfold rowP
  apply listProd_mem
  intro f hf
  rw [List.mem_map] at hf
  obtain ⟨j, hj, rfl⟩ := hf
  rw [List.mem_range'_1] at hj
  exact rootP_mem he hi (by omega) (hS j hj.1 hj.2) K

theorem isWt_pow {N : ℕ} {e : ℕ → ℕ → Module.End ℚ V} (he : GlRel N e) {c d : ℕ} (hc : c < N) (hd : d < N)
    {μ : ℕ → ℤ} {x : V} (hx : IsWt N e μ x) (k : ℕ) :
    IsWt N e (fun m => μ m + (k : ℤ) * ((if m = c then 1 else 0) - (if m = d then 1 else 0))) ((e c d ^ k) x) := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    have h := isWt_shift he hc hd ih
    have hf : (fun m => μ m + ((k + 1 : ℕ) : ℤ) * ((if m = c then 1 else 0) - (if m = d then 1 else 0))) =
        (fun m => (μ m + (k : ℤ) * ((if m = c then 1 else 0) - (if m = d then 1 else 0))) +
          ((if m = c then 1 else 0) - (if m = d then 1 else 0))) := by
      funext m; push_cast; ring
    rw [hf]; exact h

theorem kill_pow {N : ℕ} {e : ℕ → ℕ → Module.End ℚ V} {lam : ℕ → ℤ} {s : Finset ℕ} (he : GlRel N e)
    {i j : ℕ} (hi : i < N) (hj : j < N) (his : i ∈ s) (hjs : j ∉ s) {v : V} (hv : IsWt N e lam v)
    {U : Module.End ℚ V} (hU : U ∈ vanSub N e lam s) (k : ℕ) (hk : 0 < k) : U ((e j i ^ k) v) = 0 := by
  refine hU _ _ (isWt_pow he hj hi hv k) ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [his, hjs, if_true, if_false]
  have : (0 : ℤ) < k := by exact_mod_cast hk
  linarith

theorem step (hS : StepScalar) {N K : ℕ} {e : ℕ → ℕ → Module.End ℚ V} {lam : ℕ → ℤ} {v : V} {φ : V →ₗ[ℚ] ℚ}
    (he : GlRel N e) {i j : ℕ} (hij : i < j) (hj : j < N) (hv : IsWt N e lam v) (hE : e i j v = 0)
    (hφ : ∀ x, φ (e j i x) = 0) (hl1 : lam j ≤ lam i) (hl2 : lam i ≤ lam j + K) {U : Module.End ℚ V}
    (hU : ∀ k : ℕ, 0 < k → U ((e j i ^ k) v) = 0) :
    φ (rootP (fun c d => adj (e c d)) K i j U v) * (((lam i - lam j + (j : ℤ) - (i : ℤ) : ℤ)) : ℚ) = φ (U v) := by
  have hi : i < N := by omega
  have h1 : e i j * e j i - e j i * e i j = e i i - e j j := by
    have := he i j j i hi hj hj hi
    rw [if_pos rfl, if_pos rfl] at this
    exact this
  have h2 : (e i i - e j j) * e j i - e j i * (e i i - e j j) = -(e j i + e j i) := by
    have a1 := he i i j i hi hi hj hi
    have a2 := he j j j i hj hj hj hi
    rw [if_neg hij.ne, if_pos rfl] at a1
    rw [if_pos rfl, if_neg hij.ne] at a2
    calc (e i i - e j j) * e j i - e j i * (e i i - e j j)
        = (e i i * e j i - e j i * e i i) - (e j j * e j i - e j i * e j j) := by noncomm_ring
      _ = -(e j i + e j i) := by rw [a1, a2]; abel
  have hn : (((lam i - lam j).toNat : ℕ) : ℤ) = lam i - lam j := Int.toNat_of_nonneg (by omega)
  have hnq : (((lam i - lam j).toNat : ℕ) : ℚ) = ((lam i : ℚ) - (lam j : ℚ)) := by
    have : (((lam i - lam j).toNat : ℕ) : ℚ) = ((((lam i - lam j).toNat : ℕ) : ℤ) : ℚ) := by norm_cast
    rw [this, hn]; push_cast; ring
  have hH : (e i i - e j j) v = (((lam i - lam j).toNat : ℕ) : ℚ) • v := by
    rw [LinearMap.sub_apply, hv i hi, hv j hj, ← sub_smul, hnq]
  have hK : (lam i - lam j).toNat ≤ K := by omega
  have key := hS V (e i j) (e j i) (e i i - e j j) U v φ (lam i - lam j).toNat K (j - i - 1) h1 h2 hE hH hK hφ hU
  have hc : (((lam i - lam j).toNat : ℕ) : ℚ) + ((j - i - 1 : ℕ) : ℚ) + 1 =
      (((lam i - lam j + (j : ℤ) - (i : ℤ) : ℤ)) : ℚ) := by
    have : ((((lam i - lam j).toNat : ℕ) : ℤ) + ((j - i - 1 : ℕ) : ℤ) + 1 : ℤ) = lam i - lam j + (j : ℤ) - (i : ℤ) := by
      omega
    exact_mod_cast this
  rw [← hc]
  exact key

theorem van_Ico_of_range {a b : ℕ} {e : ℕ → ℕ → Module.End ℚ V} {lam : ℕ → ℤ} (hD : Dom (a + b) e lam)
    {T : Module.End ℚ V} (hT : T ∈ vanSub (a + b) e lam (Finset.range a)) {i : ℕ} (hi : i ≤ a) :
    T ∈ vanSub (a + b) e lam (Finset.Ico i a) := by
  intro μ x hx hlt
  by_cases hx0 : x = 0
  · simp [hx0]
  obtain ⟨h1, -⟩ := hD μ x hx hx0
  have hi' := h1 i (by omega)
  apply hT μ x hx
  rw [← Finset.sum_range_add_sum_Ico _ hi, ← Finset.sum_range_add_sum_Ico _ hi]
  linarith

theorem van_union {a b : ℕ} {e : ℕ → ℕ → Module.End ℚ V} {lam : ℕ → ℤ} (hD : Dom (a + b) e lam)
    {i s : ℕ} (hs1 : a ≤ s) (hs2 : s ≤ a + b) {U : Module.End ℚ V} (hU : U ∈ vanSub (a + b) e lam (Finset.Ico i a)) :
    U ∈ vanSub (a + b) e lam (Finset.Ico i a ∪ Finset.Ico s (a + b)) := by
  intro μ x hx hlt
  by_cases hx0 : x = 0
  · simp [hx0]
  obtain ⟨h1, h2⟩ := hD μ x hx hx0
  have hs := h1 s hs2
  have hdisj : Disjoint (Finset.Ico i a) (Finset.Ico s (a + b)) := by
    rw [Finset.disjoint_left]; intro y hy1 hy2; simp only [Finset.mem_Ico] at hy1 hy2; omega
  rw [Finset.sum_union hdisj, Finset.sum_union hdisj] at hlt
  rw [← Finset.sum_range_add_sum_Ico _ hs2, ← Finset.sum_range_add_sum_Ico _ hs2] at h2
  apply hU μ x hx
  linarith

theorem row_scalar (hS : StepScalar) {a b K : ℕ} {e : ℕ → ℕ → Module.End ℚ V} {lam : ℕ → ℤ} {v : V}
    {φ : V →ₗ[ℚ] ℚ} (he : GlRel (a + b) e) (hD : Dom (a + b) e lam) (hv : IsWt (a + b) e lam v)
    (hij : ∀ i j : ℕ, i < j → j < a + b → e i j v = 0 ∧ (∀ x, φ (e j i x) = 0) ∧ lam j ≤ lam i ∧ lam i ≤ lam j + K)
    {i : ℕ} (hia : i < a) {U : Module.End ℚ V} (hU : U ∈ vanSub (a + b) e lam (Finset.Ico i a)) :
    ∀ n s, s + n = a + b → a ≤ s →
      φ (rowP (fun c d => adj (e c d)) K i s n U v) *
        ∏ j ∈ Finset.Ico s (a + b), (((lam i - lam j + (j : ℤ) - (i : ℤ) : ℤ)) : ℚ) = φ (U v) := by
  intro n
  induction n with
  | zero =>
    intro s hs _
    have : s = a + b := by omega
    subst this
    simp [rowP]
  | succ n ih =>
    intro s hs has
    have hsN : s < a + b := by omega
    have hWmem : rowP (fun c d => adj (e c d)) K i (s + 1) n U ∈
        vanSub (a + b) e lam (Finset.Ico i a ∪ Finset.Ico (s + 1) (a + b)) := by
      refine rowP_mem he (by omega) (by omega) ?_ K U (van_union hD (by omega) (by omega) hU)
      intro j h1 h2
      simp only [Finset.mem_union, Finset.mem_Ico]
      omega
    have hrow : rowP (fun c d => adj (e c d)) K i s (n + 1) U =
        rootP (fun c d => adj (e c d)) K i s (rowP (fun c d => adj (e c d)) K i (s + 1) n U) := by
      simp only [rowP, List.range'_succ, List.map_cons, List.prod_cons, Module.End.mul_apply]
    obtain ⟨hE, hφ, hl1, hl2⟩ := hij i s (by omega) hsN
    have hst := step hS he (by omega : i < s) hsN hv hE hφ hl1 hl2
      (kill_pow he (by omega) hsN (by simp only [Finset.mem_union, Finset.mem_Ico]; omega)
        (by simp only [Finset.mem_union, Finset.mem_Ico]; omega) hv hWmem)
    rw [hrow, Finset.prod_eq_prod_Ico_succ_bot hsN, ← mul_assoc, hst]
    exact ih (s + 1) (by omega) (by omega)

theorem gridP_succ {M : Type} [AddCommGroup M] [Module ℚ M] (D : ℕ → ℕ → Module.End ℚ M) (K a b t : ℕ) :
    gridP D K a b (t + 1) = rowP D K t a b * gridP D K a b t := by
  simp only [gridP, List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
    List.map_cons, List.prod_cons]

theorem grid_van {a b K : ℕ} {e : ℕ → ℕ → Module.End ℚ V} {lam : ℕ → ℤ} (he : GlRel (a + b) e)
    (hD : Dom (a + b) e lam) {T : Module.End ℚ V} (hT : T ∈ vanSub (a + b) e lam (Finset.range a)) :
    ∀ t i, t ≤ i → i ≤ a → gridP (fun c d => adj (e c d)) K a b t T ∈ vanSub (a + b) e lam (Finset.Ico i a) := by
  intro t
  induction t with
  | zero => intro i _ hi; simpa [gridP] using van_Ico_of_range hD hT hi
  | succ t ih =>
    intro i hti hi
    rw [gridP_succ, Module.End.mul_apply]
    refine rowP_mem he (by omega) (by omega) ?_ K _ (ih i (by omega) hi)
    intro j h1 h2
    simp only [Finset.mem_Ico]
    omega

theorem grid_scalar (hS : StepScalar) {a b K : ℕ} {e : ℕ → ℕ → Module.End ℚ V} {lam : ℕ → ℤ} {v : V}
    {φ : V →ₗ[ℚ] ℚ} (he : GlRel (a + b) e) (hD : Dom (a + b) e lam) (hv : IsWt (a + b) e lam v)
    (hij : ∀ i j : ℕ, i < j → j < a + b → e i j v = 0 ∧ (∀ x, φ (e j i x) = 0) ∧ lam j ≤ lam i ∧ lam i ≤ lam j + K)
    {T : Module.End ℚ V} (hT : T ∈ vanSub (a + b) e lam (Finset.range a)) :
    ∀ t, t ≤ a → φ (gridP (fun c d => adj (e c d)) K a b t T v) *
      ∏ i ∈ Finset.range t, ∏ j ∈ Finset.Ico a (a + b), (((lam i - lam j + (j : ℤ) - (i : ℤ) : ℤ)) : ℚ) = φ (T v) := by
  intro t
  induction t with
  | zero => intro _; simp [gridP]
  | succ t ih =>
    intro ht
    rw [gridP_succ, Module.End.mul_apply, Finset.prod_range_succ, mul_comm (Finset.prod _ _) _, ← mul_assoc,
      row_scalar hS he hD hv hij (by omega : t < a) (grid_van he hD hT t t le_rfl (by omega)) b a (by omega) le_rfl]
    exact ih (by omega)

end GlobalTheory.LeviCut.GridScalarProof

namespace GlobalTheory.LeviCut


open GridScalarProof in
theorem gridScalar_of_stepScalar : StepScalar → GridScalar := by
  intro hS V _ _ a b K e lam v φ T he hD hv hij hT
  have hT' : T ∈ vanSub (a + b) e lam (Finset.range a) := hT
  have key := grid_scalar hS he hD hv hij hT' a le_rfl
  rw [Int.cast_prod]
  simp_rw [Int.cast_prod]
  exact key

end GlobalTheory.LeviCut
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectorGridScalarOfProjectorScalarStatement
open GlobalTheory.LeviCut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projectorGridScalar_of_projectorScalar : GlobalTheory.LeviCut.StepScalar → GlobalTheory.LeviCut.GridScalar := by
  first | exact @GlobalTheory.LeviCut.gridScalar_of_stepScalar | exact GlobalTheory.LeviCut.gridScalar_of_stepScalar | (intros; apply GlobalTheory.LeviCut.gridScalar_of_stepScalar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BetaIntegralDenominatorBound
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BetaIntegralDenominatorBound
open GlobalTheory.LeviCut

namespace GlobalTheory.BetaDenProof

theorem dvd_lam_of_le {l w t : ℕ} (hl : l.Prime) (ht : 1 ≤ t) (htw : t ≤ w) :
    t ∣ (∏ s ∈ Finset.Icc 1 w, ordCompl[l] s) * l ^ Nat.log l w := by
  have ht0 : t ≠ 0 := by omega
  conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self t l]
  rw [mul_comm (ordProj[l] t)]
  apply Nat.mul_dvd_mul
  · exact Finset.dvd_prod_of_mem _ (Finset.mem_Icc.mpr ⟨ht, htw⟩)
  · apply Nat.pow_dvd_pow
    apply Nat.le_log_of_pow_le hl.one_lt
    exact (Nat.ordProj_le l ht0).trans htw

theorem beta_dvd {Λ w : ℕ} (h : ∀ t, 1 ≤ t → t ≤ w → t ∣ Λ) :
    ∀ k j : ℕ, j + k + 1 ≤ w → (j + k + 1).factorial ∣ Λ * (j.factorial * k.factorial) := by
  intro k
  induction k with
  | zero =>
    intro j hj
    simp only [Nat.add_zero, Nat.factorial_zero, mul_one, Nat.factorial_succ]
    exact Nat.mul_dvd_mul (h (j + 1) (by omega) (by omega)) dvd_rfl
  | succ k ih =>
    intro j hj
    have h1 := ih j (by omega)
    have h2 := ih (j + 1) (by omega)
    have e : Λ * (j.factorial * (k + 1).factorial) + Λ * ((j + 1).factorial * k.factorial)
        = (j + k + 2) * (Λ * (j.factorial * k.factorial)) := by
      rw [Nat.factorial_succ k, Nat.factorial_succ j]; ring
    have hA : (j + (k + 1) + 1).factorial ∣ (j + k + 2) * (Λ * (j.factorial * k.factorial)) := by
      have : (j + (k + 1) + 1).factorial = (j + k + 2) * (j + k + 1).factorial := by
        rw [show j + (k + 1) + 1 = (j + k + 1) + 1 by omega, Nat.factorial_succ]
      rw [this]; exact Nat.mul_dvd_mul dvd_rfl h1
    have hB : (j + (k + 1) + 1).factorial ∣ Λ * ((j + 1).factorial * k.factorial) := by
      rw [show j + (k + 1) + 1 = j + 1 + k + 1 by omega]; exact h2
    rw [← e] at hA
    exact (Nat.dvd_add_left hB).mp hA

end GlobalTheory.BetaDenProof

theorem GlobalTheory.LeviCut.betaDen : GlobalTheory.LeviCut.BetaDen := by
  intro l w hl
  refine ⟨∏ s ∈ Finset.Icc 1 w, ordCompl[l] s, ?_, ?_⟩
  · intro hd
    obtain ⟨s, hs, hds⟩ := (Prime.dvd_finsetProd_iff hl.prime _).mp hd
    have : s ≠ 0 := by have := (Finset.mem_Icc.mp hs).1; omega
    exact Nat.not_dvd_ordCompl hl this hds
  · intro j k hjk
    exact GlobalTheory.BetaDenProof.beta_dvd (fun t ht htw => GlobalTheory.BetaDenProof.dvd_lam_of_le hl ht htw) k j hjk
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BetaIntegralDenominatorBoundStatement
open GlobalTheory.LeviCut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.beta_integral_denominator_bound : GlobalTheory.LeviCut.BetaDen := by
  first | exact @GlobalTheory.LeviCut.betaDen | exact GlobalTheory.LeviCut.betaDen | (intros; apply GlobalTheory.LeviCut.betaDen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectorValueHighestWeightVector
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectorValueHighestWeightVector
open GlobalTheory.LeviCut

namespace GlobalTheory.LeviCut.StepScalarProof

variable {V : Type} [AddCommGroup V] [Module ℚ V]

theorem adj_apply' (x S : Module.End ℚ V) : adj x S = x * S - S * x := by
  simp [adj]

theorem H_pow (F H : Module.End ℚ V) (v : V) (n : ℕ)
    (hHF : H * F - F * H = -(F + F)) (hv : H v = (n : ℚ) • v) :
    ∀ i : ℕ, H ((F ^ i) v) = ((n : ℚ) - 2 * i) • (F ^ i) v := by
  have h1 : H * F = F * H - (F + F) := by
    calc H * F = (H * F - F * H) + F * H := by abel
      _ = F * H - (F + F) := by rw [hHF]; abel
  intro i
  induction i with
  | zero => simp [hv]
  | succ i ih =>
    rw [pow_succ', Module.End.mul_apply, ← Module.End.mul_apply (f := H), h1]
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply, ih, map_smul]
    push_cast
    module

theorem E_pow (E F H : Module.End ℚ V) (v : V) (n : ℕ)
    (hEF : E * F - F * E = H) (hHF : H * F - F * H = -(F + F)) (hE : E v = 0) (hv : H v = (n : ℚ) • v) :
    ∀ i : ℕ, E ((F ^ (i + 1)) v) = (((i : ℚ) + 1) * ((n : ℚ) - i)) • (F ^ i) v := by
  have h1 : E * F = F * E + H := by
    calc E * F = (E * F - F * E) + F * E := by abel
      _ = F * E + H := by rw [hEF]; abel
  have hH := H_pow F H v n hHF hv
  intro i
  induction i with
  | zero =>
    rw [pow_one, ← Module.End.mul_apply (f := E), h1]
    simp [hE, hv]
  | succ i ih =>
    rw [pow_succ', Module.End.mul_apply, ← Module.End.mul_apply (f := E), h1]
    simp only [LinearMap.add_apply, Module.End.mul_apply, ih, map_smul, hH]
    rw [← Module.End.mul_apply (f := F), ← pow_succ']
    push_cast
    module

theorem adjE_pow (E F H T : Module.End ℚ V) (v : V) (n : ℕ)
    (hEF : E * F - F * E = H) (hHF : H * F - F * H = -(F + F)) (hE : E v = 0) (hv : H v = (n : ℚ) • v)
    (hT : ∀ k : ℕ, 0 < k → T ((F ^ k) v) = 0) :
    ∀ k : ℕ, (∀ i, k < i → (((adj E) ^ k) T) ((F ^ i) v) = 0) ∧
      (((adj E) ^ k) T) ((F ^ k) v) =
        ((-1 : ℚ) ^ k * (k.factorial : ℚ) * ∏ t ∈ Finset.range k, ((n : ℚ) - t)) • T v := by
  have hEp := E_pow E F H v n hEF hHF hE hv
  intro k
  induction k with
  | zero =>
    refine ⟨fun i hi => ?_, by simp⟩
    simpa using hT i hi
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hstep : ∀ y, (((adj E) ^ (k + 1)) T) y = E ((((adj E) ^ k) T) y) - (((adj E) ^ k) T) (E y) := by
      intro y
      rw [pow_succ', Module.End.mul_apply, adj_apply']
      simp [Module.End.mul_apply]
    refine ⟨fun i hi => ?_, ?_⟩
    · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      rw [hstep, hEp, map_smul, ih1 i' (by omega), ih1 (i' + 1) (by omega)]
      simp
    · rw [hstep, hEp, map_smul, ih1 (k + 1) (by omega), ih2, smul_smul, Finset.prod_range_succ,
        Nat.factorial_succ]
      simp only [map_zero, zero_sub]
      rw [← neg_smul]
      congr 1
      push_cast
      ring

theorem phi_adjF_pow (F : Module.End ℚ V) (φ : V →ₗ[ℚ] ℚ) (hφ : ∀ x, φ (F x) = 0) :
    ∀ (k : ℕ) (S : Module.End ℚ V) (y : V), φ ((((adj F) ^ k) S) y) = (-1 : ℚ) ^ k * φ (S ((F ^ k) y)) := by
  intro k
  induction k with
  | zero => intro S y; simp
  | succ k ih =>
    intro S y
    rw [pow_succ, Module.End.mul_apply, ih, adj_apply']
    simp only [LinearMap.sub_apply, Module.End.mul_apply, map_sub, hφ, zero_sub]
    rw [← Module.End.mul_apply (f := F), ← pow_succ', pow_succ]
    ring

theorem partial_sum (n j : ℕ) :
    ∀ K : ℕ, ((n : ℚ) + j + 1) * ∑ k ∈ Finset.range (K + 1),
        (-1 : ℚ) ^ k * (j.factorial : ℚ) * (∏ t ∈ Finset.range k, ((n : ℚ) - t)) / ((k + j + 1).factorial : ℚ) =
      1 + (-1 : ℚ) ^ K * (j.factorial : ℚ) * (∏ t ∈ Finset.range (K + 1), ((n : ℚ) - t)) /
        ((K + j + 1).factorial : ℚ) := by
  intro K
  induction K with
  | zero =>
    simp only [zero_add, Finset.sum_range_one, pow_zero, Finset.prod_range_zero, one_mul, Finset.prod_range_one,
      Nat.cast_zero, sub_zero]
    rw [Nat.factorial_succ j]
    have h : (j.factorial : ℚ) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  | succ K ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have e1 : K + 1 + j + 1 = (K + j + 1) + 1 := by ring
    rw [e1, Nat.factorial_succ (K + j + 1), Finset.prod_range_succ _ (K + 1)]
    have h : ((K + j + 1).factorial : ℚ) ≠ 0 := by positivity
    push_cast
    generalize ((K + j + 1).factorial : ℚ) = f at h ⊢
    generalize (∏ t ∈ Finset.range (K + 1), ((n : ℚ) - t)) = P
    field_simp
    ring

theorem stepScalar : StepScalar := by
  intro V _ _ E F H T v φ n K j hEF hHF hE hv hnK hφ hT
  have hA := adjE_pow E F H T v n hEF hHF hE hv hT
  have hB := phi_adjF_pow F φ hφ
  have hterm : ∀ k : ℕ, φ ((((adj F) ^ k * (adj E) ^ k) T) v) =
      (k.factorial : ℚ) * (∏ t ∈ Finset.range k, ((n : ℚ) - t)) * φ (T v) := by
    intro k
    rw [Module.End.mul_apply, hB, (hA k).2, map_smul, smul_eq_mul]
    rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
    simp
  have hP : ∏ t ∈ Finset.range (K + 1), ((n : ℚ) - t) = 0 :=
    Finset.prod_eq_zero (i := n) (Finset.mem_range.2 (by omega)) (sub_self _)
  have hS := partial_sum n j K
  simp only [hP, mul_zero, zero_div, add_zero] at hS
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [proj, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, smul_eq_mul,
    hterm]
  have hc : ∀ k : ℕ, coef j k * ((k.factorial : ℚ) * (∏ t ∈ Finset.range k, ((n : ℚ) - t)) * φ (T v)) =
      (-1 : ℚ) ^ k * (j.factorial : ℚ) * (∏ t ∈ Finset.range k, ((n : ℚ) - t)) / ((k + j + 1).factorial : ℚ) *
        φ (T v) := by
    intro k
    have h1 : (k.factorial : ℚ) ≠ 0 := by positivity
    have h2 : ((k + j + 1).factorial : ℚ) ≠ 0 := by positivity
    simp only [coef]
    field_simp
  simp only [hc, ← Finset.sum_mul]
  rw [mul_comm, ← mul_assoc, hS, one_mul]

end GlobalTheory.LeviCut.StepScalarProof
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectorValueHighestWeightVectorStatement
open GlobalTheory.LeviCut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projector_value_highest_weight_vector : GlobalTheory.LeviCut.StepScalar := by
  first | exact @GlobalTheory.LeviCut.StepScalarProof.stepScalar | exact GlobalTheory.LeviCut.StepScalarProof.stepScalar | (intros; apply GlobalTheory.LeviCut.StepScalarProof.stepScalar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOneProjectorWeightZeroInvariance
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOneProjectorWeightZeroInvariance
open GlobalTheory.LeviCut

namespace GlobalTheory.LeviCut

namespace RankOnePf

variable {W : Type} [AddCommGroup W] [Module ℚ W]

theorem rankOne_H_X_pow (X H : Module.End ℚ W) (hHX : ∀ w, H (X w) = X (H w) + (2 : ℚ) • X w)
    (k : ℕ) (w : W) : H ((X ^ k) w) = (X ^ k) (H w) + ((2 * k : ℕ) : ℚ) • (X ^ k) w := by
  induction k generalizing w with
  | zero => simp
  | succ k ih =>
    simp only [pow_succ, Module.End.mul_apply]
    rw [ih, hHX, map_add (f := _), map_smul]
    push_cast
    module

theorem rankOne_H_Y_pow (Y H : Module.End ℚ W) (hHY : ∀ w, H (Y w) = Y (H w) - (2 : ℚ) • Y w)
    (k : ℕ) (w : W) : H ((Y ^ k) w) = (Y ^ k) (H w) - ((2 * k : ℕ) : ℚ) • (Y ^ k) w := by
  induction k generalizing w with
  | zero => simp
  | succ k ih =>
    simp only [pow_succ, Module.End.mul_apply]
    rw [ih, hHY, map_sub, map_smul]
    push_cast
    module

theorem rankOne_X_Y_pow (X Y H : Module.End ℚ W) (hXY : ∀ w, X (Y w) = Y (X w) + H w)
    (hHY : ∀ w, H (Y w) = Y (H w) - (2 : ℚ) • Y w) (k : ℕ) (w : W) :
    X ((Y ^ (k + 1)) w) = (Y ^ (k + 1)) (X w) + ((k + 1 : ℕ) : ℚ) • (Y ^ k) (H w)
      - (((k + 1) * k : ℕ) : ℚ) • (Y ^ k) w := by
  induction k generalizing w with
  | zero => simp [hXY]
  | succ k ih =>
    have h1 : (Y ^ (k + 1 + 1)) w = (Y ^ (k + 1)) (Y w) := by
      rw [pow_succ Y (k + 1), Module.End.mul_apply]
    rw [h1, ih, hXY, hHY]
    simp only [map_add (f := _), map_sub, map_smul, pow_succ, Module.End.mul_apply]
    push_cast
    module

theorem rankOne_coef_succ (n : ℕ) :
    coef 0 (n + 1) * (((n + 1) * (n + 1 + 1) : ℕ) : ℚ) = - coef 0 n := by
  have h1 : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  simp only [coef, Nat.factorial_succ, add_zero, Nat.factorial_zero]
  push_cast
  field_simp
  ring

end RankOnePf

end GlobalTheory.LeviCut

namespace GlobalTheory.LeviCut


open RankOnePf in
theorem rankOne : RankOne := by
  intro W _ _ N K D hG hB o q ho hq hoq T hoT hqT
  have hqo : q ≠ o := Ne.symm hoq
  have hH : ∀ x, (D o o - D q q) x = D o o x - D q q x := fun x => rfl
  have hHT : (D o o - D q q) T = 0 := by rw [hH, hoT, hqT, sub_zero]
  have hXY : ∀ w, D o q (D q o w) = D q o (D o q w) + (D o o - D q q) w := by
    intro w
    have e := LinearMap.congr_fun (hG o q q o ho hq hq ho) w
    rw [if_pos (rfl : q = q), if_pos (rfl : o = o)] at e
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at e
    rw [hH]
    exact sub_eq_iff_eq_add'.mp e
  have hHX : ∀ w, (D o o - D q q) (D o q w) = D o q ((D o o - D q q) w) + (2 : ℚ) • D o q w := by
    intro w
    have e1 := LinearMap.congr_fun (hG o o o q ho ho ho hq) w
    rw [if_pos (rfl : o = o), if_neg hqo] at e1
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.zero_apply, sub_zero] at e1
    have e2 := LinearMap.congr_fun (hG q q o q hq hq ho hq) w
    rw [if_neg hqo, if_pos (rfl : q = q)] at e2
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.zero_apply, zero_sub, LinearMap.neg_apply] at e2
    rw [hH, hH, map_sub, sub_eq_iff_eq_add'.mp e1, sub_eq_iff_eq_add'.mp e2]
    module
  have hHY : ∀ w, (D o o - D q q) (D q o w) = D q o ((D o o - D q q) w) - (2 : ℚ) • D q o w := by
    intro w
    have e1 := LinearMap.congr_fun (hG o o q o ho ho hq ho) w
    rw [if_neg hoq, if_pos (rfl : o = o)] at e1
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.zero_apply, zero_sub, LinearMap.neg_apply] at e1
    have e2 := LinearMap.congr_fun (hG q q q o hq hq hq ho) w
    rw [if_pos (rfl : q = q), if_neg hoq] at e2
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.zero_apply, sub_zero] at e2
    rw [hH, hH, map_sub, sub_eq_iff_eq_add'.mp e1, sub_eq_iff_eq_add'.mp e2]
    module
  constructor
  ·
    have hterm : ∀ m : ℕ, D o q ((D q o ^ (m + 1)) ((D o q ^ (m + 1)) T)) =
        (D q o ^ (m + 1)) ((D o q ^ (m + 1 + 1)) T) +
          (((m + 1) * (m + 1 + 1) : ℕ) : ℚ) • (D q o ^ m) ((D o q ^ (m + 1)) T) := by
      intro m
      have hx : D o q ((D o q ^ (m + 1)) T) = (D o q ^ (m + 1 + 1)) T := by
        rw [pow_succ' (D o q) (m + 1), Module.End.mul_apply]
      rw [rankOne_X_Y_pow _ _ _ hXY hHY, rankOne_H_X_pow _ _ hHX, hHT, map_zero, zero_add, hx,
        map_smul]
      push_cast
      module
    have hsum : ∀ n : ℕ, D o q (∑ k ∈ Finset.range (n + 1), coef 0 k • (D q o ^ k) ((D o q ^ k) T)) =
        coef 0 n • (D q o ^ n) ((D o q ^ (n + 1)) T) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Finset.sum_range_succ, map_add (f := _), ih, map_smul, hterm n]
        have hc := rankOne_coef_succ n
        rw [show coef 0 n = -(coef 0 (n + 1) * (((n + 1) * (n + 1 + 1) : ℕ) : ℚ)) by rw [hc, neg_neg]]
        module
    have hXK : (D o q ^ (K + 1)) T = 0 := by
      refine hB o ho q hq ((2 * (K + 1) : ℕ) : ℤ) _ ?_ (by push_cast; omega)
      have h := rankOne_H_X_pow _ _ hHX (K + 1) T
      rw [hHT, map_zero, zero_add, hH] at h
      rw [Int.cast_natCast]
      exact h
    have hp : proj K 0 (D o q) (D q o) T =
        ∑ k ∈ Finset.range (K + 1), coef 0 k • (D q o ^ k) ((D o q ^ k) T) := by
      simp only [proj, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply]
    rw [hp, hsum K, hXK, map_zero, smul_zero]
  ·
    intro hXT
    have hYterm : ∀ k : ℕ, D o q ((D q o ^ (k + 1)) T) = -((((k + 1) * k : ℕ) : ℚ)) • (D q o ^ k) T := by
      intro k
      rw [rankOne_X_Y_pow _ _ _ hXY hHY, hXT, hHT, map_zero, map_zero, smul_zero, add_zero, zero_sub,
        neg_smul]
    have hYK : (D q o ^ (K + 1)) T = 0 := by
      refine hB q hq o ho ((2 * (K + 1) : ℕ) : ℤ) _ ?_ (by push_cast; omega)
      have h := rankOne_H_Y_pow _ _ hHY (K + 1) T
      rw [hHT, map_zero, zero_sub, hH] at h
      rw [Int.cast_natCast, ← neg_sub, h, neg_neg]
    have hdesc : ∀ d i : ℕ, i + d = K → (D q o ^ (i + 1)) T = 0 := by
      intro d
      induction d with
      | zero =>
        intro i hi
        rw [add_zero] at hi
        subst hi
        exact hYK
      | succ d ih =>
        intro i hi
        have h2 := ih (i + 1) (by omega)
        have h3 := hYterm (i + 1)
        rw [h2, map_zero] at h3
        rcases smul_eq_zero.mp h3.symm with h | h
        · exfalso
          have : ((((i + 1 + 1) * (i + 1) : ℕ) : ℚ)) ≠ 0 := by positivity
          exact this (neg_eq_zero.mp h)
        · exact h
    have := hdesc K 0 (by omega)
    simpa using this

end GlobalTheory.LeviCut
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOneProjectorWeightZeroInvarianceStatement
open GlobalTheory.LeviCut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_one_projector_weight_zero_invariance : GlobalTheory.LeviCut.RankOne := by
  first | exact @GlobalTheory.LeviCut.rankOne | exact GlobalTheory.LeviCut.rankOne | (intros; apply GlobalTheory.LeviCut.rankOne <;> assumption)
end
end

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LA

noncomputable section

namespace GlobalTheory.LeviCut

theorem eV_coe {N : ℕ} (ν : Fin N → ℕ) (a b : Fin N) (x : dualWeyl ℚ N N ν) :
    (eV N ν a b x : MvPolynomial (Fin N × Fin N) ℚ) = LR.der N N a b x := by
  unfold eV
  rw [dite_eq_left ⟨a.2, b.2⟩]
  rfl

theorem cut_incl (hG : GridInv) (hA : AdjBdd) (hS : GridScalar) (hI : GridInt) (hN : NablaGl) (hB : NablaBdd)
    (hSch : NablaSchur) (hL : LeviProj) (p q : ℕ) (ν : Fin (p + q) → ℕ) (hν : Antitone ν) (c₁ c₂ K w Λ : ℕ)
    (h₁ : ∀ x ∈ dualWeyl ℤ p p (fun i => ν (Fin.castAdd q i)),
      (c₁ : ℤ) • x ∈ weyl ℤ p p le_rfl (fun i => ν (Fin.castAdd q i)))
    (h₂ : ∀ x ∈ dualWeyl ℤ q q (fun j => ν (Fin.natAdd p j)),
      (c₂ : ℤ) • x ∈ weyl ℤ q q le_rfl (fun j => ν (Fin.natAdd p j)))
    (hK : ∀ i j, ν i ≤ ν j + K) (hw' : K + (p + q) ≤ w + 1)
    (hΛ : ∀ j k : ℕ, j + k + 1 ≤ w → (j + k + 1).factorial ∣ Λ * (j.factorial * k.factorial)) :
    ∀ x ∈ dualWeyl ℤ (p + q) (p + q) ν, ((c₁ * c₂ * Λ ^ (p * q) : ℕ) : ℤ) • x ∈ weyl ℤ (p + q) (p + q) le_rfl ν := by
  obtain ⟨T, hT1, hT2, hT3, hT4⟩ := hL p q ν hν c₁ c₂ h₁ h₂
  obtain ⟨hrel, hspan, hdom, hst1, hst2⟩ := hN (p + q) ν hν
  obtain ⟨hrel', hbdd'⟩ := hA _ (p + q) K _ hrel (hB (p + q) ν hν K hK) hspan
  set e := eV (p + q) ν with he
  set S₀ := gridP (fun c d => adj (e c d)) K p q p T with hS₀
  have hinv : ∀ c < p + q, ∀ d < p + q, adj (e c d) S₀ = 0 :=
    hG _ p q K _ hrel' hbdd' T (fun c hc d hd hcd => by
      simp only [adj, LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
      rw [hT1 c hc d hd hcd, sub_self])
  let v : dualWeyl ℚ (p + q) (p + q) ν := ⟨hw ℚ le_rfl ν, hwMem ℚ _ _ le_rfl ν hν⟩
  let φ : dualWeyl ℚ (p + q) (p + q) ν →ₗ[ℚ] ℚ :=
    { toFun := fun x => fockQ (hw ℚ le_rfl ν) (x : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ)
      map_add' := fun x y => LR.fock_add_right _ _ _
      map_smul' := fun c x => LR.fock_smul_right _ _ _ }
  have hwz : ∀ c : Fin (p + q), wtZ ν c = ν c := fun c => by simp [wtZ]
  have hv : IsWt (p + q) e (wtZ ν) v := by
    intro c hc
    apply Subtype.ext
    have h1 := eV_coe ν ⟨c, hc⟩ ⟨c, hc⟩ v
    have h2 := (LR.der_diag_iff _ _).1 (LR.hw_rowHom ν hν) ⟨c, hc⟩
    have h3 := hwz ⟨c, hc⟩
    simp only at h1 h3
    rw [he, h1, h3]
    simpa using h2
  have hsc := hS _ p q K e (wtZ ν) v φ T hrel hdom hv (fun i j hij hj => by
    have hi : i < p + q := hij.trans hj
    have hr := LR.der_hw_raise ν ⟨i, hi⟩ ⟨j, hj⟩ hij
    have h3 := hwz ⟨i, hi⟩
    have h4 := hwz ⟨j, hj⟩
    simp only at h3 h4
    refine ⟨Subtype.ext ?_, fun x => ?_, ?_, ?_⟩
    · exact (eV_coe ν ⟨i, hi⟩ ⟨j, hj⟩ v).trans hr
    · have h1 := eV_coe ν ⟨j, hj⟩ ⟨i, hi⟩ x
      change fockQ _ (eV (p + q) ν j i x : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ) = 0
      simp only at h1
      rw [h1, ← LR.fock_der, hr]
      simpa using LR.fock_smul_left (0 : ℚ) 0 (x : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ)
    · rw [h3, h4]; exact_mod_cast hν (show (⟨i, hi⟩ : Fin (p + q)) ≤ ⟨j, hj⟩ from hij.le)
    · rw [h3, h4]; exact_mod_cast hK _ _) hT3
  set z : ℤ := ∏ i ∈ Finset.range p, ∏ j ∈ Finset.Ico p (p + q), (wtZ ν i - wtZ ν j + (j : ℤ) - (i : ℤ)) with hz
  have hone : (z : ℚ) • S₀ = 1 := by
    refine hSch (p + q) ν hν _ (fun c hc d hd => ?_) ?_
    · have := hinv c hc d hd
      simp only [adj, LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply, sub_eq_zero] at this
      rw [mul_smul_comm, smul_mul_assoc, ← he, this]
    · change φ (((z : ℚ) • S₀) v) = _
      rw [LinearMap.smul_apply, map_smul, smul_eq_mul, mul_comm, hsc]
      exact hT4
  intro x hx
  let x' : dualWeyl ℚ (p + q) (p + q) ν := ⟨intQ _ _ x, (dualWeylIntRat _ _ ν x).1 hx⟩
  have hx' : x' ∈ latV (p + q) ν (dualWeyl ℤ (p + q) (p + q) ν) := ⟨x, hx, rfl⟩
  have h5 := Submodule.smul_mem _ z (hI _ p q K w Λ e _ _ hst1 hst2 hw' hΛ (c₁ * c₂) T hT2 x' hx')
  rw [smul_comm, ← hS₀] at h5
  have h6 : z • S₀ x' = x' := by
    rw [← Int.cast_smul_eq_zsmul ℚ, ← LinearMap.smul_apply, hone]; rfl
  rw [h6] at h5
  obtain ⟨y, hy, hyx⟩ := h5
  have h7 : y = ((c₁ * c₂ * Λ ^ (p * q) : ℕ) : ℤ) • x := by
    apply map_injective (Int.castRingHom ℚ) (fun a b h => by simpa using h)
    change intQ _ _ y = intQ _ _ _
    rw [hyx, map_smul, map_smul]
    rfl
  exact h7 ▸ hy

theorem ExCut₂ (hG : GridInv) (hA : AdjBdd) (hS : GridScalar) (hI : GridInt) (hN : NablaGl) (hB : NablaBdd)
    (hSch : NablaSchur) (hL : LeviProj) (hD : BetaDen) : Formalism.CohomologicalDescent.E.ExCut := by
  intro N lam hlam l hl lo w hU a ha
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le ha
  have hcast : ∀ c, c = b → exZ c c le_rfl (LD.res c (fun i => lam (a + i))) l =
      exZ b b le_rfl (LD.res b (fun i => lam (a + i))) l := by rintro c rfl; rfl
  rw [hcast (a + b - a) (by omega), Nat.add_sub_cancel_left]
  have hA1 : Antitone (LD.res a lam) := fun i j hij =>
    hlam (show (Fin.castAdd b i) ≤ Fin.castAdd b j from hij)
  have hA2 : Antitone (LD.res b (fun i => lam (a + i))) := fun i j hij =>
    hlam (show (Fin.natAdd a i) ≤ Fin.natAdd a j by rw [Fin.le_def] at hij ⊢; simpa using hij)
  obtain ⟨m₁, hm₁, h₁⟩ := exact_z_specialization a a le_rfl _ hA1 l hl
  obtain ⟨m₂, hm₂, h₂⟩ := exact_z_specialization b b le_rfl _ hA2 l hl
  obtain ⟨m, hm, hden⟩ := hD l w hl
  have hsp : ∀ i j : Fin (a + b), i ≤ j → lam i + j ≤ lam j + w + i := fun i j _ => by
    have h1 := (hU i i.2).2
    have h2 := (hU j j.2).1
    simp only [UnitNormBounds.UN] at h1 h2
    omega
  have hK : ∀ i j : Fin (a + b), LD.res (a + b) lam i ≤ LD.res (a + b) lam j + (w + 1 - (a + b)) := fun i j => by
    have hpos : 0 < a + b := lt_of_le_of_lt (Nat.zero_le _) i.2
    have h1 := hsp ⟨0, hpos⟩ ⟨a + b - 1, by omega⟩ (by simp [Fin.le_def])
    have h2 := hlam (show (⟨0, hpos⟩ : Fin (a + b)) ≤ i by simp [Fin.le_def])
    have h3 := hlam (show j ≤ (⟨a + b - 1, by omega⟩ : Fin (a + b)) by rw [Fin.le_def]; have := j.2; simp only; omega)
    simp only [LD.res] at h1 h2 h3 ⊢
    omega
  have hw' : (w + 1 - (a + b)) + (a + b) ≤ w + 1 := by
    rcases Nat.eq_zero_or_pos (a + b) with h0 | hpos
    · omega
    · have h1 := hsp ⟨0, hpos⟩ ⟨a + b - 1, by omega⟩ (by simp [Fin.le_def])
      have h2 := hlam (show (⟨0, hpos⟩ : Fin (a + b)) ≤ ⟨a + b - 1, by omega⟩ by simp [Fin.le_def])
      simp only [LD.res] at h1 h2
      omega
  have key := cut_incl hG hA hS hI hN hB hSch hL a b (LD.res (a + b) lam) hlam _ _ _ w _ h₁ h₂ hK hw' hden
  refine Nat.sInf_le ⟨m₁ * m₂ * m ^ (a * b), ?_, fun x hx => ?_⟩
  · intro h
    rcases (Nat.Prime.dvd_mul hl).1 h with h | h
    · rcases (Nat.Prime.dvd_mul hl).1 h with h | h
      · exact hm₁ h
      · exact hm₂ h
    · exact hm (hl.dvd_of_dvd_pow h)
  · convert key x hx using 3
    rw [pow_add, pow_add, mul_pow, ← pow_mul, mul_comm (Nat.log l w)]
    ring

theorem exCut : Formalism.CohomologicalDescent.E.ExCut :=
  ExCut₂ (GlobalTheory.T.grid_invariance_of_rank_one_two GlobalTheory.T.rank_one_projector_weight_zero_invariance GlobalTheory.T.rank_two_consecutive_projector_invariance) GlobalTheory.T.adjoint_action_endomorphism_weight_bound (GlobalTheory.T.projectorGridScalar_of_projectorScalar GlobalTheory.T.projector_value_highest_weight_vector) GlobalTheory.T.projector_grid_denominator_bound
    GlobalTheory.T.dualWeylModuleStructureGl_proof GlobalTheory.T.dualWeylWeightSpreadBound_proof GlobalTheory.T.dualWeyl_schur_endomorphism
    (GlobalTheory.T.dualWeylLeviProjectionDenominators_of_hypotheses (GlobalTheory.T.dualWeylRestrictionLatticeTensor_of_substitutionStable GlobalTheory.T.dualWeylLattice_subst_increasing_map_stable) GlobalTheory.T.dualWeyl_highest_weight_restriction_blockDiagonal GlobalTheory.T.dualWeyl_restriction_rowOperators) GlobalTheory.T.beta_integral_denominator_bound

end GlobalTheory.LeviCut
