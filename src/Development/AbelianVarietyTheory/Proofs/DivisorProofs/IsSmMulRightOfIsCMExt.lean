module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ContinuesConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentedBundleSectionsRationalFunctionsDict
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoprimeScalarForEmbedding
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoSelfIntersectionPowTensorDivPow
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ArFormExists
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InducedSectionZFinite

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmMulRightOfIsCMExt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th GlobalTheory.UAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped NNReal Matrix Topology ContDiff
open GlobalTheory.AdelicU GlobalTheory.SiegelSet

namespace GlobalTheory.UAut.RightTranslate

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem isRealLine_conj (h : IsCMExt F E σ) {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) (a : GAd σ J) :
    IsRealLine σ J fun t => a⁻¹ * γ t * a := _root_.GlobalTheory.EisCont.CentreFinite.isRealLine_conj (γ := γ) h hγ a

end GlobalTheory.UAut.RightTranslate


open GlobalTheory.UAut.RightTranslate in
theorem GlobalTheory.UAut.isSm_mul_right_of_isCMExt : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E), IsCMExt F E σ → ∀ (f : GlobalTheory.AdelicU.GAd σ J → ℂ) (a : GlobalTheory.AdelicU.GAd σ J), GlobalTheory.UAut.IsSm σ J f → GlobalTheory.UAut.IsSm σ J (fun x => f (x * a)) := by
  intro F E _ _ _ _ _ σ n J h f a hf
  intro k γ hγ g
  have hc : ∀ l : List (GAd σ J), (l.map fun x => a⁻¹ * x * a).prod = a⁻¹ * l.prod * a := fun l => by
    induction l with
    | nil => simp
    | cons x l ih => rw [List.map_cons, List.prod_cons, List.prod_cons, ih]; simp [mul_assoc]
  have e : (fun t : Fin k → ℝ => f (g * (List.ofFn fun i => γ i (t i)).prod * a)) =
      fun t => f (g * a * (List.ofFn fun i => a⁻¹ * γ i (t i) * a).prod) := funext fun t => by
    rw [show (List.ofFn fun i => a⁻¹ * γ i (t i) * a) = (List.ofFn fun i => γ i (t i)).map fun x => a⁻¹ * x * a from by
      rw [List.map_ofFn]; rfl, hc]
    simp [mul_assoc]
  show ContDiff ℝ ∞ fun t : Fin k → ℝ => f (g * (List.ofFn fun i => γ i (t i)).prod * a)
  rw [e]
  exact hf k (fun i t => a⁻¹ * γ i t * a) (fun i => isRealLine_conj h (hγ i) a) (g * a)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrowthOfTame
noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory
open scoped ContDiff

namespace GlobalTheory.AutGrowth

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


variable (E a) in
def growth : Submodule ℂ (GA E a → ℂ) where
  carrier := {f | ∀ g, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖f (g * infGL E a y)‖ ≤ C * height y ^ N}
  zero_mem' g := ⟨0, 0, fun y => by simp⟩
  add_mem' {f f'} h h' g := by
    obtain ⟨C, N, hC⟩ := h g
    obtain ⟨C', N', hC'⟩ := h' g
    refine ⟨|C| + |C'|, N + N', fun y => ?_⟩
    have h1 := one_le_height y
    have p1 : height y ^ N ≤ height y ^ (N + N') := pow_le_pow_right₀ h1 (by omega)
    have p2 : height y ^ N' ≤ height y ^ (N + N') := pow_le_pow_right₀ h1 (by omega)
    have q1 : 0 ≤ height y ^ N := le_trans zero_le_one (one_le_pow₀ h1)
    have q2 : 0 ≤ height y ^ N' := le_trans zero_le_one (one_le_pow₀ h1)
    calc ‖(f + f') (g * infGL E a y)‖ ≤ ‖f (g * infGL E a y)‖ + ‖f' (g * infGL E a y)‖ := norm_add_le _ _
      _ ≤ C * height y ^ N + C' * height y ^ N' := add_le_add (hC y) (hC' y)
      _ ≤ |C| * height y ^ (N + N') + |C'| * height y ^ (N + N') := by
        refine add_le_add ?_ ?_
        · exact (mul_le_mul_of_nonneg_right (le_abs_self C) q1).trans
            (mul_le_mul_of_nonneg_left p1 (abs_nonneg C))
        · exact (mul_le_mul_of_nonneg_right (le_abs_self C') q2).trans
            (mul_le_mul_of_nonneg_left p2 (abs_nonneg C'))
      _ = (|C| + |C'|) * height y ^ (N + N') := by ring
  smul_mem' c f h g := by
    obtain ⟨C, N, hC⟩ := h g
    refine ⟨‖c‖ * C, N, fun y => ?_⟩
    rw [Pi.smul_apply, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC y) (norm_nonneg c)


variable (E a) in
def tame : Submodule ℂ (Sm E a) where
  carrier := {ψ | ∀ l : List (Lie E a), ((l.map (lie E a)).prod ψ).1 ∈ growth E a}
  zero_mem' l := by simp
  add_mem' {ψ ψ'} h h' l := by
    rw [map_add (f := _), Submodule.coe_add]
    exact add_mem (h l) (h' l)
  smul_mem' c ψ h l := by
    rw [map_smul, Submodule.coe_smul]
    exact Submodule.smul_mem _ c (h l)

theorem growth_of_tame {ψ : Sm E a} (h : ψ ∈ tame E a) : ψ.1 ∈ growth E a := by
  simpa using h []

theorem lie_mem_tame (X : Lie E a) {ψ : Sm E a} (h : ψ ∈ tame E a) : lie E a X ψ ∈ tame E a := by
  intro l
  have e : (l.map (lie E a)).prod (lie E a X ψ) = ((l ++ [X]).map (lie E a)).prod ψ := by
    simp [List.map_append, List.prod_append, Module.End.mul_apply]
  rw [e]
  exact h _

def dens (X : Lie E a) (α : Lie E a → ℂ) (x : Lie E a) : ℂ :=
  -(fderiv ℝ α x (lmul X x) + (LinearMap.trace ℝ (Lie E a) (lmul X).toLinearMap : ℂ) * α x)

def KInv (α : Lie E a → ℂ) : Prop :=
  ∀ (k : Kinf E a) (x : Lie E a),
    α (toL ((k : Matrix (Fin a) (Fin a) (Cinf E)) * Matrix.of x * ((star k : Kinf E a) : Matrix (Fin a) (Fin a) (Cinf E)))) = α x

def maps (L : Subgroup (GL (Fin a) (Af E))) (W : Submodule ℂ (Sm E a))
    (hW : ∀ k, ∀ w ∈ W, cptRep E a k w ∈ W) : Submodule ℂ (W →ₗ[ℂ] Sm E a) where
  carrier := {T | (∀ k w, T (GlobalTheory.PRep.sub (cptRep E a) W hW k w) = cptRep E a k (T w)) ∧
    ∀ w, T w ∈ tame E a ∧ (∀ γ g, (T w).1 (ratGL E a γ * g) = (T w).1 g) ∧ ∀ k ∈ L, finRep E a k (T w) = T w}
  zero_mem' := ⟨fun k w => by simp, fun w => ⟨by simp, fun _ _ => rfl, fun k _ => by simp⟩⟩
  add_mem' {T T'} h h' := ⟨fun k w => by simp [h.1 k w, h'.1 k w], fun w =>
    ⟨by simpa using add_mem (h.2 w).1 (h'.2 w).1,
     fun γ g => by simp [(h.2 w).2.1 γ g, (h'.2 w).2.1 γ g],
     fun k hk => by simp [(h.2 w).2.2 k hk, (h'.2 w).2.2 k hk]⟩⟩
  smul_mem' c T h := ⟨fun k w => by simp [h.1 k w], fun w =>
    ⟨by simpa using Submodule.smul_mem _ c (h.2 w).1,
     fun γ g => by simp [(h.2 w).2.1 γ g],
     fun k hk => by simp [(h.2 w).2.2 k hk]⟩⟩

theorem isTest_dens (X : Lie E a) {α : Lie E a → ℂ} (h : GlobalTheory.CuspQuot.IsTest (invSet E a) α) :
    GlobalTheory.CuspQuot.IsTest (invSet E a) (dens X α) := by
  have hs : Function.support (dens X α) ⊆ tsupport α := by
    intro x hx
    by_contra hn
    apply hx
    have h1 : α x = 0 := image_eq_zero_of_notMem_tsupport hn
    have h2 : fderiv ℝ α x = 0 := fderiv_of_notMem_tsupport ℝ hn
    simp [dens, h1, h2]
  have ht : tsupport (dens X α) ⊆ tsupport α := closure_minimal hs (isClosed_tsupport α)
  refine ⟨?_, h.2.1.mono' hs, ht.trans h.2.2⟩
  refine (((h.1.fderiv_right (m := ∞) (by simp)).clm_apply (lmul X).contDiff).add
    (contDiff_const.mul h.1)).neg

end GlobalTheory.AutGrowth
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceMemOfQdetMem
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory

noncomputable section

namespace GlobalTheory.CapTrace

variable {A : Type} [Ring A] [Algebra ℂ A]

def dprod (L : List (ℂ × A)) : ℂ := (L.map Prod.fst).prod

def sub1 (L : List (ℂ × A)) : A := List.rec 0 (fun p L s => dprod L • p.2 + p.1 • s) L

theorem sub1_nil : sub1 ([] : List (ℂ × A)) = 0 := rfl

theorem sub1_cons (p : ℂ × A) (L : List (ℂ × A)) : sub1 (p :: L) = dprod L • p.2 + p.1 • sub1 L := rfl

theorem prod_affine (L : List (ℂ × A)) : ∃ c : ℕ → A, (∀ k, L.length < k → c k = 0) ∧
    (∀ u : ℂ, (L.map fun p => (u * p.1) • (1 : A) + p.2).prod =
      ∑ k ∈ Finset.range (L.length + 1), u ^ k • c k) ∧
    c L.length = dprod L • (1 : A) ∧ (∀ j, j + 1 = L.length → c j = sub1 L) := by
  induction L with
  | nil => exact ⟨fun k => if k = 0 then 1 else 0, fun k hk => by simp at hk; simp [Nat.pos_iff_ne_zero.1 hk],
      fun u => by simp, by simp [dprod], fun j hj => by simp at hj⟩
  | cons p L ih =>
    obtain ⟨c, hc0, hcu, hctop, hcsub⟩ := ih
    refine ⟨fun k => (if k = 0 then 0 else p.1 • c (k - 1)) + p.2 * c k, ?_, ?_, ?_, ?_⟩
    · intro k hk
      simp only [List.length_cons] at hk
      have h1 : k ≠ 0 := by omega
      simp only [h1, if_false, hc0 k (by omega), hc0 (k - 1) (by omega), smul_zero, mul_zero, add_zero]
    · intro u
      have hS1 : ∑ k ∈ Finset.range (L.length + 1 + 1), u ^ k • (if k = 0 then (0:A) else p.1 • c (k - 1)) =
          ∑ k ∈ Finset.range (L.length + 1), (u * p.1) • (u ^ k • c k) := by
        rw [Finset.sum_range_succ']
        simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel, if_true, smul_zero, add_zero]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [smul_smul, smul_smul, pow_succ]; ring_nf
      have hS2 : ∑ k ∈ Finset.range (L.length + 1 + 1), u ^ k • (p.2 * c k) =
          ∑ k ∈ Finset.range (L.length + 1), p.2 * (u ^ k • c k) := by
        rw [Finset.sum_range_succ, hc0 (L.length + 1) (by omega)]
        simp [mul_smul_comm]
      simp only [List.map_cons, List.prod_cons, hcu, List.length_cons, smul_add, Finset.sum_add_distrib, hS1, hS2,
        add_mul, Finset.mul_sum, smul_mul_assoc, one_mul]
    · simp only [List.length_cons, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel, hctop,
        hc0 (L.length + 1) (by omega), mul_zero, add_zero, dprod, List.map_cons, List.prod_cons, smul_smul]
    · intro j hj
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hj
      subst hj
      beta_reduce
      rw [hctop, sub1_cons]
      rcases Nat.eq_zero_or_pos L.length with h | h
      · rw [if_pos h]
        have : L = [] := List.length_eq_zero_iff.1 h
        subst this
        simp [sub1_nil, dprod]
      · rw [if_neg (by omega), hcsub _ (by omega), mul_smul_comm, mul_one, add_comm]

end GlobalTheory.CapTrace

namespace GlobalTheory.CapTrace

variable {A : Type} [Ring A] [Algebra ℂ A]

theorem coeff_mem (S : Submodule ℂ A) (n : ℕ) (c : ℕ → A)
    (h : ∀ u : ℂ, ∑ k ∈ Finset.range (n + 1), u ^ k • c k ∈ S) (m : ℕ) (hm : m ≤ n) : c m ∈ S := by
  let v : Fin (n + 1) → ℂ := fun j => ((j : ℕ) : ℂ)
  have hv : Function.Injective v := fun i j hij => Fin.ext (by simpa [v] using hij)
  have hdet : IsUnit (Matrix.vandermonde v).det :=
    isUnit_iff_ne_zero.2 (Matrix.det_vandermonde_ne_zero_iff.2 hv)
  have hW : (Matrix.vandermonde v)⁻¹ * Matrix.vandermonde v = 1 := Matrix.nonsing_inv_mul _ hdet
  set W := (Matrix.vandermonde v)⁻¹
  let m' : Fin (n + 1) := ⟨m, by omega⟩
  have key : c m = ∑ j, W m' j • ∑ k ∈ Finset.range (n + 1), v j ^ k • c k := by
    calc c m = ∑ k : Fin (n + 1), (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) m' k • c k := by
          rw [Finset.sum_eq_single m']
          · simp [m']
          · intro k _ hk; rw [Matrix.one_apply_ne (Ne.symm hk), zero_smul]
          · simp
      _ = ∑ k : Fin (n + 1), (W * Matrix.vandermonde v) m' k • c k := by rw [hW]
      _ = ∑ j, W m' j • ∑ k : Fin (n + 1), v j ^ (k : ℕ) • c k := by
          simp only [Matrix.mul_apply, Matrix.vandermonde_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
          exact Finset.sum_comm
      _ = _ := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_range (fun k => v j ^ k • c k)]
  rw [key]
  exact S.sum_mem fun j _ => S.smul_mem _ (h _)

theorem sub1_ones (L : List (ℂ × A)) (h : ∀ p ∈ L, p.1 = 1) : sub1 L = (L.map Prod.snd).sum ∧ dprod L = 1 := by
  induction L with
  | nil => simp [sub1_nil, dprod]
  | cons p L ih =>
    obtain ⟨h1, h2⟩ := ih fun q hq => h q (List.mem_cons_of_mem _ hq)
    have hp := h p List.mem_cons_self
    refine ⟨?_, ?_⟩
    · rw [sub1_cons, h1, h2, hp]; simp
    · simp only [dprod, List.map_cons, List.prod_cons, hp, one_mul]; exact h2

theorem dprod_eq_zero (L : List (ℂ × A)) (p : ℂ × A) (hp : p ∈ L) (h : p.1 = 0) : dprod L = 0 :=
  List.prod_eq_zero (List.mem_map.2 ⟨p, hp, h⟩)

theorem sub1_ofFn_eq_zero : ∀ (n : ℕ) (d : Fin n → ℂ) (B : Fin n → A) (k₀ k₁ : Fin n), k₀ ≠ k₁ → d k₀ = 0 →
    d k₁ = 0 → sub1 (List.ofFn fun k => (d k, B k)) = 0 := by
  intro n
  induction n with
  | zero => intro d B k₀; exact k₀.elim0
  | succ n ih =>
    intro d B k₀ k₁ hne h₀ h₁
    rw [List.ofFn_succ, sub1_cons]
    have hmem : ∀ j : Fin n, d j.succ = 0 → dprod (List.ofFn fun k : Fin n => (d k.succ, B k.succ)) = 0 :=
      fun j hj => dprod_eq_zero _ (d j.succ, B j.succ) (List.mem_ofFn.2 ⟨j, rfl⟩) hj
    induction k₀ using Fin.cases with
    | zero =>
      induction k₁ using Fin.cases with
      | zero => exact absurd rfl hne
      | succ j₁ => simp [h₀, hmem j₁ h₁]
    | succ j₀ =>
      induction k₁ using Fin.cases with
      | zero => simp [h₁, hmem j₀ h₀]
      | succ j₁ =>
        rw [ih (fun k => d k.succ) (fun k => B k.succ) j₀ j₁ (fun e => hne (by rw [e])) h₀ h₁, hmem j₀ h₀]
        simp

end GlobalTheory.CapTrace

namespace GlobalTheory.CapTrace

variable {A : Type} [Ring A] [Algebra ℂ A]

theorem trace_mem_of_qdet_mem {n : ℕ} (X : Fin n → Fin n → A) (S : Subalgebra ℂ A)
    (h : ∀ u : ℂ, Formalism.REAL.qdet X u ∈ S) : ∑ i, X i i ∈ S := by
  classical
  let d : Equiv.Perm (Fin n) → Fin n → ℂ := fun σ k => if σ k = k then 1 else 0
  let B : Equiv.Perm (Fin n) → Fin n → A := fun σ k =>
    (if σ k = k then algebraMap ℂ A (-((k : ℕ) : ℂ)) else 0) + X (σ k) k
  let L : Equiv.Perm (Fin n) → List (ℂ × A) := fun σ => List.ofFn fun k => (d σ k, B σ k)
  have hlen : ∀ σ, (L σ).length = n := fun σ => List.length_ofFn
  choose c hc0 hcu hctop hcsub using fun σ => prod_affine (L σ)
  have hfac : ∀ σ (u : ℂ), (List.ofFn fun k : Fin n => Formalism.REAL.Tm X (u - ((k : ℕ) : ℂ)) (id (σ k)) (id k)).prod =
      ((L σ).map fun p => (u * p.1) • (1 : A) + p.2).prod := by
    intro σ u
    simp only [L, List.map_ofFn]
    congr 1
    refine List.ofFn_inj.2 (funext fun k => ?_)
    simp only [Function.comp_apply, Formalism.REAL.Tm, id, d, B]
    split_ifs
    · rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, mul_one, sub_eq_add_neg, add_smul]; abel
    · simp
  let C : ℕ → A := fun k => ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : A) * c σ k
  have hC : ∀ u : ℂ, Formalism.REAL.qdet X u = ∑ k ∈ Finset.range (n + 1), u ^ k • C k := by
    intro u
    simp only [Formalism.REAL.qdet, Formalism.REAL.qminor, hfac, hcu, hlen, C, Finset.mul_sum, Finset.smul_sum, mul_smul_comm]
    exact Finset.sum_comm
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  have hmem : C (n - 1) ∈ S := coeff_mem (Subalgebra.toSubmodule S) n C (fun u => by
    rw [← hC]; exact h u) (n - 1) (by omega)
  have hsub : ∀ σ, c σ (n - 1) = sub1 (L σ) := fun σ => hcsub σ _ (by rw [hlen]; omega)
  have hCeq : C (n - 1) = ∑ k : Fin n, B 1 k := by
    simp only [C, hsub]
    rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
    · rw [(sub1_ones (L 1) ?_).1]
      · simp [L, List.map_ofFn, List.sum_ofFn]
      · intro p hp
        obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hp
        simp [d]
    · intro σ _ hσ
      obtain ⟨k₀, hk₀⟩ : ∃ k, σ k ≠ k := by
        by_contra hc; exact hσ (Equiv.ext fun k => not_not.1 fun hk => hc ⟨k, hk⟩)
      have hk₁ : σ (σ k₀) ≠ σ k₀ := fun e => hk₀ (σ.injective e)
      rw [sub1_ofFn_eq_zero n (d σ) (B σ) k₀ (σ k₀) (Ne.symm hk₀) (by simp [d, hk₀]) (by simp [d, hk₁]), mul_zero]
    · simp
  have hB : ∀ k : Fin n, B 1 k = algebraMap ℂ A (-((k : ℕ) : ℂ)) + X k k := fun k => by simp [B]
  simp only [hCeq, hB, Finset.sum_add_distrib] at hmem
  have hs : ∑ k : Fin n, algebraMap ℂ A (-((k : ℕ) : ℂ)) ∈ S := S.sum_mem fun k _ => S.algebraMap_mem _
  simpa using S.sub_mem hmem hs

end GlobalTheory.CapTrace

namespace GlobalTheory.CuspRep

theorem Eop_add_Eop_conj {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (τ : E →+* ℂ)
    (i : Fin a) : Eop τ i i + Eop (ComplexEmbedding.conjugate τ) i i = lieS E a i i (atEmb τ 1) := by
  have e : atEmb τ (-Complex.I) = -atEmb τ Complex.I := by
    rw [atEmb_eq]; simp
  simp only [Eop, atEmb_conj, map_one, Complex.conj_I, e, map_neg, smul_neg, sub_neg_eq_add]
  rw [← smul_add]
  module

end GlobalTheory.CuspRep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearModelFixesUnitSectionAbelian
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearModelFixesUnitSectionAbelian
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.SemilinearModel

theorem unit_section_semilinear : ∀ (W K' : Type) [CommRing W] [IsDomain W] [Field K'] [Algebra W K'] [IsFractionRing W K'] (G : Over (Sp W)) [GrpObj G], IsAbelianScheme G → ∀ (σ : K' →+* K') (τ : W →+* W) (φ : G.left ⟶ G.left) (ρ : pullback G.hom (spMap (algebraMap W K')) ⟶ pullback G.hom (spMap (algebraMap W K'))), (∀ x : W, σ (algebraMap W K' x) = algebraMap W K' (τ x)) → φ ≫ G.hom = G.hom ≫ spMap τ → pullback.fst G.hom (spMap (algebraMap W K')) ≫ φ = ρ ≫ pullback.fst G.hom (spMap (algebraMap W K')) → ∀ (e₀ : Sp W ⟶ G.left), e₀ ≫ G.hom = 𝟙 _ → ∀ x : Sp K' ⟶ pullback G.hom (spMap (algebraMap W K')), x ≫ pullback.fst G.hom (spMap (algebraMap W K')) = spMap (algebraMap W K') ≫ e₀ → x ≫ ρ = spMap σ ≫ x → e₀ ≫ φ = spMap τ ≫ e₀ := by
  intro W K' _ _ _ _ _ G _ hG σ τ φ ρ hστ hφ hρ e₀ he x hx hxρ
  haveI := hG.proper
  have hj : spMap σ ≫ spMap (algebraMap W K') = spMap (algebraMap W K') ≫ spMap τ := by
    unfold spMap
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext y
    simp [hστ]
  haveI : IsDominant (spMap (algebraMap W K')) := by
    refine ⟨?_⟩
    have := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap W K')).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective W K')]; exact bot_le)
    exact this
  refine ext_of_isDominant_of_isSeparated G.hom ?_ (spMap (algebraMap W K')) ?_
  · rw [Category.assoc, hφ, ← Category.assoc, he, Category.assoc, he]; simp
  · rw [← Category.assoc, ← hx, Category.assoc, hρ, ← Category.assoc, hxρ, Category.assoc, hx, ← Category.assoc, hj, Category.assoc]
end GlobalTheory.SemilinearModel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearModelFixesUnitSectionAbelianStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semilinearModel_fixes_unit_section_abelian : ∀ (W K' : Type) [CommRing W] [IsDomain W] [Field K'] [Algebra W K'] [IsFractionRing W K'] (G : Over (Sp W)) [GrpObj G], IsAbelianScheme G → ∀ (σ : K' →+* K') (τ : W →+* W) (φ : G.left ⟶ G.left) (ρ : pullback G.hom (spMap (algebraMap W K')) ⟶ pullback G.hom (spMap (algebraMap W K'))), (∀ x : W, σ (algebraMap W K' x) = algebraMap W K' (τ x)) → φ ≫ G.hom = G.hom ≫ spMap τ → pullback.fst G.hom (spMap (algebraMap W K')) ≫ φ = ρ ≫ pullback.fst G.hom (spMap (algebraMap W K')) → ∀ (e₀ : Sp W ⟶ G.left), e₀ ≫ G.hom = 𝟙 _ → ∀ x : Sp K' ⟶ pullback G.hom (spMap (algebraMap W K')), x ≫ pullback.fst G.hom (spMap (algebraMap W K')) = spMap (algebraMap W K') ≫ e₀ → x ≫ ρ = spMap σ ≫ x → e₀ ≫ φ = spMap τ ≫ e₀ := by
  first | exact @GlobalTheory.SemilinearModel.unit_section_semilinear | exact GlobalTheory.SemilinearModel.unit_section_semilinear | (intros; apply GlobalTheory.SemilinearModel.unit_section_semilinear <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullActLev
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

noncomputable section

open CategoryTheory

namespace GlobalTheory.LevPullEquiv


set_option maxHeartbeats 1000000 in
theorem pull_actLev : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (d : DeltaDat Xo c 0), 1 ≤ Dw.p + Dw.q → d.IsLev → d.l₂.A = 1 → (∀ h : KA l ≤ KA d.l₂, d.r ≫ Xo.s = d.Xo₂.s ≫ ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (IntermediateField.inclusion h).toRingHom) → ∀ (G G₂ : Type) [Group G] [Group G₂] (lev : G → Dw.La →ₗ[𝓞 D.host.E] Dw.La) (lev₂ : G₂ → Dw.La →ₗ[𝓞 D.host.E] Dw.La), ActLev (Xo := Xo) c (fun g => (lev g, (LinearMap.id : Dw.La →ₗ[𝓞 D.host.E] Dw.La))) → ActLev (Xo := d.Xo₂) d.c₂ (fun g => (lev₂ g, (LinearMap.id : Dw.La →ₗ[𝓞 D.host.E] Dw.La))) → ∀ (g : G) (g₂ : G₂), CongMod l.Mb (lev₂ g₂) (lev g) → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, ∀ f₂ ∈ sec d.Xo₂ d.c₂ a n, Pull d f f₂ → Pull d (actLev c (fun g => (lev g, (LinearMap.id : Dw.La →ₗ[𝓞 D.host.E] Dw.La))) g f) (actLev d.c₂ (fun g => (lev₂ g, (LinearMap.id : Dw.La →ₗ[𝓞 D.host.E] Dw.La))) g₂ f₂) := by
  intro D j H Dw l Xo c d hpq hlev hA2 hbase G G₂ _ _ lev lev₂ hact hact₂ g g₂ hcong a n f hf f₂ hf₂ hpull
  intro k _ _ _ _ hk y₂ y hov
  have e1 : evR Xo c (actLev c (fun g => (lev g, (LinearMap.id : Dw.La →ₗ[𝓞 D.host.E] Dw.La))) g f) y =
      evR Xo c f (mvPt _ _ g y) :=
    evalAt_actL hact (GlobalTheory.TransferCompare.evalWD_framed _ _) frMap_trans_id g hf.1 y
  have e2 : evR d.Xo₂ d.c₂ (actLev d.c₂ (fun g => (lev₂ g, (LinearMap.id : Dw.La →ₗ[𝓞 D.host.E] Dw.La))) g₂ f₂) y₂ =
      evR d.Xo₂ d.c₂ f₂ (mvPt _ _ g₂ y₂) :=
    evalAt_actL hact₂ (GlobalTheory.TransferCompare.evalWD_framed _ _) frMap_trans_id g₂ hf₂.1 y₂
  rw [e1, e2]
  obtain ⟨ρ, ν, hi, hmv, hfm⟩ := mvPt_spec hact.total g y
  obtain ⟨ρ₂, ν₂, hi₂, hmv₂, hfm₂⟩ := mvPt_spec hact₂.total g₂ y₂
  obtain ⟨hd, hM, -, -, -, hE, hlift, -, -⟩ := id hlev
  obtain ⟨r', m', hsq₁, hsq₂, hE'⟩ := GlobalTheory.exists_conj_levelMap D.host.E H Dw l Xo c 0 d hE ρ ν (asIso ρ₂) ν₂
    (lev g) LinearMap.id (lev₂ g₂) LinearMap.id hmv hmv₂ hcong (fun x => ⟨0, by simp⟩)
  have hov' := GlobalTheory.frOver_of_square_of_frMove D.host.E H Dw l Xo c 0 d ρ ν ρ₂ ν₂ r' m' hsq₁ hsq₂ k y _ y₂ _ hov hfm hfm₂
  obtain ⟨z₂, hz₂⟩ := hlift k hk _
  have hL : ReciprocityTheory.ChartRestriction.G.Out.Laws := GlobalTheory.T.abelianScheme_laws_unconditional.1
  have hN := GlobalTheory.levelMaps_closed hL D.host.E H Dw hpq
  obtain ⟨g', ρ', ν', hg', -, hmv', hfm'⟩ :=
    GlobalTheory.exists_levMove_of_frOver hL D.host.E H Dw l Xo c 0 d hN hd hM hE r' m' hE' k hk _ z₂ _ hz₂ hov'
  obtain ⟨e₁, e₂⟩ := GlobalTheory.levMove_comm_levelMap_of_trivial_mod D.host.E H Dw l Xo c 0 d hpq hlev hA2 hbase ρ'.hom ν'
    (g'.f d.l₂.M) (g'.f d.l₂.A) inferInstance hmv' (fun x => GlobalTheory.LevelFibre.sub_mem_of_inGam hd hg' x)
  obtain ⟨⟨ι, hι, hone⟩, -, -⟩ := GlobalTheory.T.framedPointMove_calculus D.host.E H Dw l Xo c
  have hfin := GlobalTheory.frOver_of_square_of_frMove D.host.E H Dw l Xo c 0 d (𝟙 _) ι ρ'.hom ν' d.r d.m
    (by rw [e₁, Category.comp_id]) (by rw [e₂, hι, Category.comp_id]) k _ _ z₂ _ hz₂ (hone k _) hfm'
  exact hpull k hk _ _ hfin

end GlobalTheory.LevPullEquiv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarMeasureUniqueSigmaCompactNormalisedCompactOp
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarMeasureUniqueSigmaCompactNormalisedCompactOp
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG GlobalTheory.WeylCell.WeylUnipotentShell

namespace GlobalTheory

theorem haar_unique_of_sigmaCompact_normalised :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [MeasurableSpace G]
    [BorelSpace G] (μ ν : Measure G) [μ.IsHaarMeasure] [ν.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts ν]
    (K : ℕ → Set G), (∀ j, IsCompact (K j) ∧ MeasurableSet (K j)) → (⋃ j, K j) = Set.univ →
    ∀ (s : Set G) (c : ENNReal), IsOpen s → IsCompact s → s.Nonempty → ν s = c * μ s → ν = c • μ := by
  intro G _ _ _ _ _ _ μ ν _ _ _ K hK hcov s c hso hsc hsn hνs
  have key : ∀ A : Set G, IsCompact (closure A) →
      ν A = (Measure.haarScalarFactor ν μ : ENNReal) * μ A := fun A hA => by
    have := Measure.measure_isMulInvariant_eq_smul_of_isCompact_closure ν μ hA
    rw [this, ENNReal.smul_def, smul_eq_mul]
  have hs0 : μ s ≠ 0 := (hso.measure_pos μ hsn).ne'
  have hstop : μ s ≠ ⊤ := hsc.measure_lt_top.ne
  have hc : c = (Measure.haarScalarFactor ν μ : ENNReal) := by
    have h1 := key s (hsc.closure_of_subset subset_rfl)
    rw [hνs] at h1
    exact (ENNReal.mul_left_inj hs0 hstop).mp h1
  subst hc
  ext A hA
  let B : ℕ → Set G := fun j => A ∩ Set.accumulate K j
  have hBmono : Monotone B := fun i j hij => Set.inter_subset_inter_right _ (Set.monotone_accumulate hij)
  have hBcl : ∀ j, IsCompact (closure (B j)) := fun j =>
    (isCompact_accumulate (fun i => (hK i).1) j).closure_of_subset Set.inter_subset_right
  have hBU : (⋃ j, B j) = A := by
    simp only [B, ← Set.inter_iUnion, Set.iUnion_accumulate, hcov, Set.inter_univ]
  rw [← hBU, hBmono.measure_iUnion, hBmono.measure_iUnion]
  simp only [Measure.smul_apply, smul_eq_mul]
  exact iSup_congr fun j => key _ (hBcl j)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarMeasureUniqueSigmaCompactNormalisedCompactOpStatement
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG GlobalTheory.WeylCell.WeylUnipotentShell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haarMeasure_unique_sigmaCompact_normalised_compactOpen : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [MeasurableSpace G]
    [BorelSpace G] (μ ν : Measure G) [μ.IsHaarMeasure] [ν.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts ν]
    (K : ℕ → Set G), (∀ j, IsCompact (K j) ∧ MeasurableSet (K j)) → (⋃ j, K j) = Set.univ →
    ∀ (s : Set G) (c : ENNReal), IsOpen s → IsCompact s → s.Nonempty → ν s = c * μ s → ν = c • μ := by
  first | exact @GlobalTheory.haar_unique_of_sigmaCompact_normalised | exact GlobalTheory.haar_unique_of_sigmaCompact_normalised | (intros; apply GlobalTheory.haar_unique_of_sigmaCompact_normalised <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolyFunMemSmoothVectors
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolyFunMemSmoothVectors
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CentralOps
open scoped TensorProduct ContDiff

namespace GlobalTheory.CentralOps

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

variable {D : D7}

def algEntry (V : HSp D) (τ : D.what₂.Tau) (m j : Fin V.rank) : AlgInf V →ₗ[ℝ] ℂ where
  toFun u := (u : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) τ m j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem contDiff_expEntry (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V : HSp D}
    (R : RealPoints θ V) (τ : D.what₂.Tau) (m j : Fin V.rank) :
    ContDiff ℝ ∞ fun X : LieN V => algEntry V τ m j (NormedSpace.exp (jInf V X)) := by
  haveI : CompleteSpace (AlgInf V) := FiniteDimensional.complete ℝ (AlgInf V)
  haveI : FiniteDimensional ℝ (LieN V) := FiniteDimensional.of_injective (jInf V) (isLieData R).inj
  have h1 : ContDiff ℝ ∞ (NormedSpace.exp : AlgInf V → AlgInf V) :=
    contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
  exact (LinearMap.toContinuousLinearMap (algEntry V τ m j)).contDiff.comp
    (h1.comp (LinearMap.toContinuousLinearMap (jInf V)).contDiff)

theorem realEntries_mul_exp (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V : HSp D}
    (R : RealPoints θ V) (g : GA D V) (X : LieN V) (p : D.what₂.Tau × Fin V.rank × Fin V.rank) :
    realEntries θ V (g * expMap (jInf V) (secInf θ V) X) p =
      ∑ m, infMat D.sp.cm.sig V.gram (θ p.1) g p.2.1 m * algEntry V p.1 m p.2.2 (NormedSpace.exp (jInf V X)) := by
  have h2 := (isExpFam_expInf R X).2 p.1
  change infMat D.sp.cm.sig V.gram (θ p.1) (g * expInf θ V X) p.2.1 p.2.2 = _
  rw [R.2.2.2.1, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  change infMat D.sp.cm.sig V.gram (θ p.1) (expInf θ V X) m p.2.2 = (NormedSpace.exp (jInf V X) : AlgInf V) p.1 m p.2.2
  rw [exp_algInf, h2]
  rfl

theorem polyFun_mem_smF : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D),
    RealPoints θ V → ∀ P : PolyE V, polyFun θ V P ∈ SmF θ V := by
  intro D θ V R P g
  have hc : ∀ p : D.what₂.Tau × Fin V.rank × Fin V.rank,
      ContDiff ℝ ∞ fun X : LieN V => realEntries θ V (g * expMap (jInf V) (secInf θ V) X) p := by
    intro p
    simp only [realEntries_mul_exp θ R]
    exact ContDiff.sum fun m _ => contDiff_const.mul (contDiff_expEntry θ R p.1 m p.2.2)
  change ContDiff ℝ ∞ fun X : LieN V => MvPolynomial.eval (realEntries θ V (g * expMap (jInf V) (secInf θ V) X)) P
  induction P using MvPolynomial.induction_on with
  | C a => simpa using contDiff_const
  | add p q hp hq => simpa only [map_add (f := _)] using hp.add hq
  | mul_X p n hp => simpa only [map_mul, MvPolynomial.eval_X] using hp.mul (hc n)

end GlobalTheory.CentralOps

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolyFunMemSmoothVectorsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CentralOps
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polyFun_mem_smooth_vectors : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D), RealPoints θ V → ∀ P : PolyE V, polyFun θ V P ∈ SmF θ V := by
  first | exact @GlobalTheory.CentralOps.polyFun_mem_smF | exact GlobalTheory.CentralOps.polyFun_mem_smF | (intros; apply GlobalTheory.CentralOps.polyFun_mem_smF <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoHermLineBundleGeometricDegreePowTensDivPo
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoHermLineBundleGeometricDegreePowTensDivPo
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

noncomputable section

namespace GlobalTheory.DegGrowth

open MvPolynomial

theorem expand (Ψ : MvPolynomial (Fin 2) ℝ →ₗ[ℝ] ℝ) (D : ℕ) (t : ℝ) :
    Ψ ((X 0 + C t * X 1) ^ D) = ∑ m ∈ Finset.range (D + 1),
      t ^ (D - m) * Ψ (X 0 ^ m * X 1 ^ (D - m) * (D.choose m : MvPolynomial (Fin 2) ℝ)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [add_pow, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [mul_pow, ← map_pow, ← smul_eq_mul (a := t ^ _), ← map_smul, MvPolynomial.smul_eq_C_mul]
  congr 1
  ring

theorem main : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ L A : HermLB p, Tendsto (fun n : ℕ => gdeg ((L.pow n).tens A) D / (n : ℝ) ^ D) atTop (𝓝 (gdeg L D)) := by
  intro hC k _ Y _ p D hX L A
  obtain ⟨Ψ, hΨ⟩ := ((hC.arExists k Y p D hX).2 (Fin 2) ![L, A]).2
  have hlin (n : ℕ) : (lin fun i => (((![(n : ℤ), 1] : Fin 2 → ℤ) i : ℤ) : ℝ)) = C (n : ℝ) * X 0 + C 1 * X 1 := by
    simp [lin, Fin.sum_univ_two]
  have hiso (n : ℕ) : (comb ![L, A] ![(n : ℤ), 1]).Isometric ((L.pow n).tens A) := by
    refine HermLB.icls_eq_iff.1 ?_
    simp [icls_comb, HermLB.icls_tens, HermLB.icls_pow, Fin.sum_univ_two, natCast_zsmul]
  have hiso0 : (comb ![L, A] ![1, 0]).Isometric L := by
    refine HermLB.icls_eq_iff.1 ?_
    simp [icls_comb, Fin.sum_univ_two]
  have hlin0 : (lin fun i => (((![1, 0] : Fin 2 → ℤ) i : ℤ) : ℝ)) = (X 0 : MvPolynomial (Fin 2) ℝ) := by
    simp [lin, Fin.sum_univ_two]
  have h0 : Ψ (X 0 ^ D) = gdeg L D := by
    rw [← hlin0, hΨ.1, hiso0.gdeg_eq]
  have hn_eq (n : ℕ) : gdeg ((L.pow n).tens A) D = Ψ ((C (n : ℝ) * X 0 + C 1 * X 1) ^ D) := by
    rw [← (hiso n).gdeg_eq, ← hΨ.1, hlin]
  set f : ℝ → ℝ := fun t => Ψ ((X 0 + C t * X 1) ^ D) with hf
  have hfc : Continuous f := by
    have : f = fun t => ∑ m ∈ Finset.range (D + 1),
      t ^ (D - m) * Ψ (X 0 ^ m * X 1 ^ (D - m) * (D.choose m : MvPolynomial (Fin 2) ℝ)) :=
      funext fun t => expand Ψ D t
    rw [this]
    fun_prop
  have hf0 : f 0 = gdeg L D := by simp [hf, h0]
  have hev : ∀ᶠ n : ℕ in atTop, f (1 / (n : ℝ)) = gdeg ((L.pow n).tens A) D / (n : ℝ) ^ D := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hn)
    have e : C (n : ℝ) * X 0 + C 1 * X 1 = C (n : ℝ) * (X 0 + C (1 / (n : ℝ)) * X 1 : MvPolynomial (Fin 2) ℝ) := by
      rw [mul_add, ← mul_assoc, ← map_mul, mul_one_div_cancel hn']
    rw [hn_eq, e, mul_pow, ← map_pow, ← MvPolynomial.smul_eq_C_mul, map_smul, smul_eq_mul,
      mul_div_cancel_left₀ _ (pow_ne_zero _ hn')]
  have ht := (hfc.tendsto 0).comp tendsto_one_div_atTop_nhds_zero_nat
  rw [hf0] at ht
  exact ht.congr' hev

end GlobalTheory.DegGrowth
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoHermLineBundleGeometricDegreePowTensDivPoStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_hermLineBundleGeometricDegree_pow_tens_div_pow : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ L A : HermLB p, Tendsto (fun n : ℕ => gdeg ((L.pow n).tens A) D / (n : ℝ) ^ D) atTop (𝓝 (gdeg L D)) := by
  first | exact @GlobalTheory.DegGrowth.main | exact GlobalTheory.DegGrowth.main | (intros; apply GlobalTheory.DegGrowth.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralTwistedComparisonAtFixedSection
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralTwistedComparisonAtFixedSection
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SectionLattice

theorem mem_pull_chart_iff {X Y : Scheme.{0}} (L : LB X) (f : Y ⟶ X) (j : (L.pull f).ι) (y : Y) :
    y ∈ (L.pull f).U j ↔ f.base y ∈ L.U (j PUnit.unit) :=
  ⟨fun h => Set.mem_iInter.1 h PUnit.unit, fun h => Set.mem_iInter.2 fun _ => h⟩

theorem exists_chart_of_isLocalRing {R : Type} [CommRing R] [IsLocalRing R] {X : Scheme.{0}}
    (L : LB X) (hL : L.IsLB) (e : Spec (CommRingCat.of R) ⟶ X) : ∃ m : L.ι, ⊤ ≤ e ⁻¹ᵁ L.U m := by
  have h : e.base (IsLocalRing.closedPoint R) ∈ (⨆ i, L.U i) := by rw [hL.cover]; trivial
  obtain ⟨m, hm⟩ := TopologicalSpace.Opens.mem_iSup.1 h
  refine ⟨m, ?_⟩
  have := (IsLocalRing.closedPoint_mem_iff (R := R) (e ⁻¹ᵁ L.U m)).1 hm
  exact this.ge

theorem integralAtSection_of_conj : ∀ (W K' : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] (G : Over (Sp W)) (σ : K' ≃+* K') (τ : W →+* W), (∀ l : K', l ≠ 0 → ∃ a : W, σ l = algebraMap W K' a * l) → ∀ (φ : G.left ⟶ G.left) (e₀ : Sp W ⟶ G.left), e₀ ≫ G.hom = 𝟙 _ → e₀ ≫ φ = spMap τ ≫ e₀ → ∀ (ρ : pullback G.hom (spMap (algebraMap W K')) ⟶ pullback G.hom (spMap (algebraMap W K'))) (x : Sp K' ⟶ pullback G.hom (spMap (algebraMap W K'))), x ≫ pullback.fst G.hom (spMap (algebraMap W K')) = spMap (algebraMap W K') ≫ e₀ → x ≫ pullback.snd G.hom (spMap (algebraMap W K')) = 𝟙 _ → x ≫ ρ = spMap (σ : K' →+* K') ≫ x → ∀ (M : LB G.left) (N : LB (pullback G.hom (spMap (algebraMap W K')))), M.IsLB → N.IsLB → ∀ (w : LB.Iso (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))) N) (w₁ : LB.Iso ((M.pull φ).pull (pullback.fst G.hom (spMap (algebraMap W K')))) N), (∀ (n : N.ι) (i : ((M.pull φ).pull (pullback.fst G.hom (spMap (algebraMap W K')))).ι) (h : ⊤ ≤ x ⁻¹ᵁ (N.U n ⊓ ((M.pull φ).pull (pullback.fst G.hom (spMap (algebraMap W K')))).U i)) (h' : ⊤ ≤ x ⁻¹ᵁ (N.U n ⊓ (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => i PUnit.unit PUnit.unit))), (Scheme.ΓSpecIso (CommRingCat.of K')).hom.hom ((x.appLE _ ⊤ h).hom (w₁.s (n, i)).val) = σ ((Scheme.ΓSpecIso (CommRingCat.of K')).hom.hom ((x.appLE _ ⊤ h').hom (w.s (n, fun _ => i PUnit.unit PUnit.unit)).val))) → GlobalTheory.SectionLattice.IntegralAtSection G.hom w w₁ := by
  intro W K' _ _ _ _ _ _ G σ τ hσ φ e₀ he₀ hφ ρ x hx₁ hx₂ _ M N hM hN w w₁ H
  obtain ⟨m, hm⟩ := exists_chart_of_isLocalRing M hM e₀
  obtain ⟨n, hn⟩ := exists_chart_of_isLocalRing N hN x
  have hi : ⊤ ≤ e₀ ⁻¹ᵁ (M.pull φ).U (fun _ => m) := by
    intro y _
    change e₀.base y ∈ (M.pull φ).U (fun _ => m)
    refine (mem_pull_chart_iff _ _ _ _).2 ?_
    have h1 : φ.base (e₀.base y) = e₀.base ((spMap τ).base y) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hφ]
    rw [h1]
    exact hm (TopologicalSpace.Opens.mem_top _)
  have key : ∀ (P : LB G.left) (i : P.ι), ⊤ ≤ e₀ ⁻¹ᵁ P.U i →
      ⊤ ≤ x ⁻¹ᵁ (N.U n ⊓ (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => i)) := by
    intro P i hP y hy
    refine ⟨hn hy, ?_⟩
    change x.base y ∈ (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => i)
    refine (mem_pull_chart_iff _ _ _ _).2 ?_
    have h1 : (pullback.fst G.hom (spMap (algebraMap W K'))).base (x.base y) =
        e₀.base ((spMap (algebraMap W K')).base y) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hx₁]
    rw [h1]
    exact hP (TopologicalSpace.Opens.mem_top _)
  have h₁ := key (M.pull φ) (fun _ => m) hi
  have h₂ := key M m hm
  have hw := H n (fun _ _ => m) h₁ h₂
  have hu : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of K')).hom.hom
      ((x.appLE _ ⊤ h₂).hom (w.s (n, fun _ => m)).val)) :=
    ((Units.isUnit _).map _).map _
  obtain ⟨a, ha⟩ := hσ _ hu.ne_zero
  exact ⟨e₀, he₀, x, hx₁, hx₂, fun _ => m, m, n, hi, hm, h₁, h₂, a, hw.trans ha⟩

end GlobalTheory.SectionLattice
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralTwistedComparisonAtFixedSectionStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_twisted_comparison_at_fixed_section : ∀ (W K' : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] (G : Over (Sp W)) (σ : K' ≃+* K') (τ : W →+* W), (∀ l : K', l ≠ 0 → ∃ a : W, σ l = algebraMap W K' a * l) → ∀ (φ : G.left ⟶ G.left) (e₀ : Sp W ⟶ G.left), e₀ ≫ G.hom = 𝟙 _ → e₀ ≫ φ = spMap τ ≫ e₀ → ∀ (ρ : pullback G.hom (spMap (algebraMap W K')) ⟶ pullback G.hom (spMap (algebraMap W K'))) (x : Sp K' ⟶ pullback G.hom (spMap (algebraMap W K'))), x ≫ pullback.fst G.hom (spMap (algebraMap W K')) = spMap (algebraMap W K') ≫ e₀ → x ≫ pullback.snd G.hom (spMap (algebraMap W K')) = 𝟙 _ → x ≫ ρ = spMap (σ : K' →+* K') ≫ x → ∀ (M : LB G.left) (N : LB (pullback G.hom (spMap (algebraMap W K')))), M.IsLB → N.IsLB → ∀ (w : LB.Iso (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))) N) (w₁ : LB.Iso ((M.pull φ).pull (pullback.fst G.hom (spMap (algebraMap W K')))) N), (∀ (n : N.ι) (i : ((M.pull φ).pull (pullback.fst G.hom (spMap (algebraMap W K')))).ι) (h : ⊤ ≤ x ⁻¹ᵁ (N.U n ⊓ ((M.pull φ).pull (pullback.fst G.hom (spMap (algebraMap W K')))).U i)) (h' : ⊤ ≤ x ⁻¹ᵁ (N.U n ⊓ (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => i PUnit.unit PUnit.unit))), (Scheme.ΓSpecIso (CommRingCat.of K')).hom.hom ((x.appLE _ ⊤ h).hom (w₁.s (n, i)).val) = σ ((Scheme.ΓSpecIso (CommRingCat.of K')).hom.hom ((x.appLE _ ⊤ h').hom (w.s (n, fun _ => i PUnit.unit PUnit.unit)).val))) → GlobalTheory.SectionLattice.IntegralAtSection G.hom w w₁ := by
  first | exact @GlobalTheory.SectionLattice.integralAtSection_of_conj | exact GlobalTheory.SectionLattice.integralAtSection_of_conj | (intros; apply GlobalTheory.SectionLattice.integralAtSection_of_conj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHeightsAndFormsOfIntersectionAndInductive
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHeightsAndFormsOfIntersectionAndInductive
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts

namespace GlobalTheory.Published

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ}

theorem ArFormExists.exists_isArithHeight (H : ArFormExists) (hX : IsArithVar p D) (L : HermLB p) :
    ∃ h, L.IsArithHeight h := by
  obtain ⟨Φ, hΦ⟩ := H k X p D hX Unit fun _ => L
  obtain ⟨h, hh, -⟩ := hΦ.1 (Pi.single () 1)
  exact ⟨h, (isometric_comb_single (fun _ : Unit => L) ()).isArithHeight hX hh⟩

theorem ArMix.fnB_of_height (H : ArMix) (hX : IsArithVar p D) {ι : Type} [Fintype ι] {L : ι → HermLB p}
    {u : ∀ σ : k →+* ℂ, CxPts p σ → ℝ} {hu : ∀ σ y, CInfAt (u σ) y}
    {hc : ∀ σ σ', (Weight.ofFun (u σ)).IsConj (Weight.ofFun (u σ'))} {Φ : MvPolynomial (Option ι) ℝ →ₗ[ℝ] ℝ}
    (hΦ : IsArFun (fun o : Option ι => o.elim (ArInt.fnB u hu hc) L) D Φ) (n : ι → ℤ) {h : X → ℝ}
    (hh : (comb L n).IsArithHeight h) :
    Φ (MvPolynomial.X none * rename some (lin fun i => (n i : ℝ)) ^ D) = 1 / 2 * chInt (comb L n) D u := by
  have := hX.isLocallyNoetherian
  have hr : IsRatSec (ArInt.fnB u hu hc).B fun _ => 1 := fun a b h =>
    (map_one _).symm.trans (mul_one _).symm
  have he (z : X) : ((ArInt.fnB u hu hc).div hr).IsEqn z 1 :=
    (presents_divOfRatSec _ hr).isEqn PUnit.unit z trivial
  have h₁ (z : X) : ((ArInt.fnB u hu hc).div hr).mult z = 0 := (he z).mult_eq.trans (unitAt_one z).ord_eq_zero
  have h₂ (σ) : offSupp p σ ((ArInt.fnB u hu hc).div hr) = Set.univ :=
    Set.eq_univ_of_forall fun y => mem_offSupp.2 fun hy => (he _).mem_supp_iff.1 hy (unitAt_one _)
  have h₃ (σ) : logNorm ((ArInt.fnB u hu hc).φ σ) (fun _ => 1) = fun y => -(1 / 2) * u σ y := funext fun y => by
    have e := ratVal_fnOf (y := y) mem_ptsIn_top trivial 1
    rw [map_one, ev_one mem_ptsIn_top] at e
    rw [logNorm, Units.val_one, e, norm_one, Real.log_one]
    change 0 - u σ y / 2 = _
    ring
  rw [(H k X p D hX ι _ L Φ hΦ n h hh _ hr).2, HermLB.archInt, chInt]
  simp only [h₁, h₂, h₃, Weight.chernInt_const_mul, Int.cast_zero, zero_mul, finsum_zero, ← mul_finsum]
  ring

theorem arExists_of_form_of_mix : ArFormExists → ArMix → ArExists := by
  intro HF HM k _ X _ p D hX
  refine ⟨HF.exists_isArithHeight hX, fun ι _ L => ⟨HF k X p D hX ι L, ?_⟩⟩
  have hu (σ : k →+* ℂ) (y : CxPts p σ) : CInfAt (fun _ => (2 : ℝ)) y := cInfAt_const _ y
  have hc (σ σ' : k →+* ℂ) : (Weight.ofFun (p := p) (σ := σ) fun _ => (2 : ℝ)).IsConj
      (Weight.ofFun (σ := σ') fun _ => (2 : ℝ)) := fun _ _ _ _ _ => rfl
  obtain ⟨Φ, hΦ⟩ := HF k X p D hX _ fun o : Option ι => o.elim (ArInt.fnB (fun _ _ => 2) hu hc) L
  refine ⟨Φ ∘ₗ LinearMap.mulLeft ℝ (MvPolynomial.X none) ∘ₗ (rename (R := ℝ) (some : ι → Option ι)).toLinearMap,
    fun n => ?_, fun P d hd hP => ?_⟩
  · obtain ⟨h, hh⟩ := HF.exists_isArithHeight hX (comb L n)
    rw [LinearMap.comp_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_pow, LinearMap.mulLeft_apply,
      HM.fnB_of_height hX hΦ n hh, gdeg, chInt, chInt, mul_finsum]
    refine finsum_congr fun σ => ?_
    rw [← Weight.chernInt_const_mul]
    norm_num
  · rw [LinearMap.comp_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearMap.mulLeft_apply]
    exact hΦ.2 _ (1 + d) (by omega) ((isHomogeneous_X ℝ none).mul hP.rename_isHomogeneous)

end GlobalTheory.Published
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHeightsAndFormsOfIntersectionAndInductiveStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithHeightsAndForms_of_intersection_and_inductive : GlobalTheory.Published.ArFormExists → GlobalTheory.Published.ArMix → GlobalTheory.Published.ArExists := by
  first | exact @GlobalTheory.Published.arExists_of_form_of_mix | exact GlobalTheory.Published.arExists_of_form_of_mix | (intros; apply GlobalTheory.Published.arExists_of_form_of_mix <;> assumption)
end
end
