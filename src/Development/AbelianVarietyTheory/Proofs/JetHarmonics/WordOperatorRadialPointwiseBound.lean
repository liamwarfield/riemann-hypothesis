module

public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PointwiseBoundedOfMemBoundedFactorsMonoid
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.RadialMultipliersSatisfyNormalFormRelations
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WordOperatorColumnMemNormalFormProductSpan

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.PlusHatsTaylorCoeffLeibnizRule
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.PlusHatsTaylorCoeffLeibnizRule
namespace GlobalTheory.HatTaylorPlus

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF Polynomial

noncomputable section

variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ}

def ev (f : ℕ → A) (P : A[X]) : A := P.sum fun j a => f j * a

omit [Algebra ℂ A] in
theorem ev_add (f : ℕ → A) (P Q : A[X]) : ev f (P + Q) = ev f P + ev f Q :=
  Polynomial.sum_add_index _ _ _ (by simp) (by simp [mul_add])

omit [Algebra ℂ A] in
theorem ev_monomial (f : ℕ → A) (n : ℕ) (a : A) : ev f (monomial n a) = f n * a :=
  Polynomial.sum_monomial_index _ _ (by simp)

omit [Algebra ℂ A] in
theorem ev_mul (f g : ℕ → A) (P Q : A[X]) (z : A) (h : ∀ j, z * g j = ev (fun i => f (j + i)) P) :
    z * ev g Q = ev f (P * Q) := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq => rw [ev_add, mul_add, mul_add, ev_add, hp, hq]
  | monomial n b =>
    rw [ev_monomial, ← mul_assoc, h]
    clear h
    induction P using Polynomial.induction_on' with
    | add p q hp hq => rw [ev_add, add_mul, add_mul, ev_add, hp, hq]
    | monomial k a => rw [monomial_mul_monomial, ev_monomial, ev_monomial, mul_assoc, add_comm]

omit [Algebra ℂ A] in
theorem ev_eq_sum (f : ℕ → A) (P : A[X]) (n : ℕ) (h : P.natDegree < n) :
    ev f P = ∑ j ∈ Finset.range n, f j * P.coeff j :=
  Polynomial.sum_over_range' _ (by simp) n h

omit [Algebra ℂ A] in
theorem mul_ev (z : A) (f : ℕ → A) (P : A[X]) : z * ev f P = ev (fun i => z * f i) P := by
  simp [ev, Polynomial.sum, Finset.mul_sum, mul_assoc]

def Deg (L : LevelData A r) (Y : ℂ) (D : ℕ) (Z : ℂ → A) : Prop :=
  ∃ P : A[X], P.natDegree ≤ D ∧ (∀ s : ℂ, Z (Y + s) = ev (fun j => algebraMap ℂ A (s ^ j)) P) ∧
    ∀ m : ℕ → A, MulRel L m → ∀ q, Z Y * m q = ev (fun j => m (q + j)) P

variable {L : LevelData A r} {Y : ℂ}

theorem Deg.mono {D E : ℕ} {Z : ℂ → A} (h : Deg L Y D Z) (hDE : D ≤ E) : Deg L Y E Z := by
  obtain ⟨P, h1, h2⟩ := h
  exact ⟨P, h1.trans hDE, h2⟩

theorem Deg.add {D : ℕ} {Z W : ℂ → A} (h : Deg L Y D Z) (h' : Deg L Y D W) :
    Deg L Y D (fun y => Z y + W y) := by
  obtain ⟨P, h1, h2, h3⟩ := h
  obtain ⟨Q, k1, k2, k3⟩ := h'
  refine ⟨P + Q, (natDegree_add_le _ _).trans (max_le h1 k1), fun s => ?_, fun m hm q => ?_⟩
  · rw [ev_add, ← h2, ← k2]
  · rw [ev_add, ← h3 m hm, ← k3 m hm, add_mul]

theorem Deg.mul {D E : ℕ} {Z W : ℂ → A} (h : Deg L Y D Z) (h' : Deg L Y E W) :
    Deg L Y (D + E) (fun y => Z y * W y) := by
  obtain ⟨P, h1, h2, h3⟩ := h
  obtain ⟨Q, k1, k2, k3⟩ := h'
  refine ⟨P * Q, natDegree_mul_le.trans (add_le_add h1 k1), fun s => ?_, fun m hm q => ?_⟩
  · show Z (Y + s) * W (Y + s) = _
    rw [k2]
    refine ev_mul _ _ _ _ _ fun j => ?_
    rw [← Algebra.commutes, h2, mul_ev]
    simp only [pow_add, map_mul]
  · show Z Y * W Y * m q = _
    rw [mul_assoc, k3 m hm]
    refine ev_mul _ _ _ _ _ fun j => ?_
    rw [h3 m hm]
    simp only [add_assoc]

theorem deg_const (a : A) (ha : ∀ m : ℕ → A, MulRel L m → ∀ q, a * m q = m q * a) :
    Deg L Y 0 (fun _ => a) := by
  refine ⟨monomial 0 a, natDegree_monomial_le _, fun s => ?_, fun m hm q => ?_⟩
  · rw [ev_monomial]; simp
  · rw [ev_monomial, ha m hm]; rfl

theorem deg_fn {a : A} (ha : a ∈ L.fns) : Deg L Y 0 (fun _ => a) :=
  deg_const a fun _ hm q => ((hm q).1 a ha).eq

theorem deg_lin (Z : ℂ → A) (b : A) (h1 : ∀ s, Z (Y + s) = Z Y + algebraMap ℂ A s * b)
    (h2 : ∀ m : ℕ → A, MulRel L m → ∀ q, Z Y * m q = m q * Z Y + m (q + 1) * b) : Deg L Y 1 Z := by
  refine ⟨monomial 0 (Z Y) + monomial 1 b, (natDegree_add_le _ _).trans
    (max_le ((natDegree_monomial_le _).trans zero_le_one) (natDegree_monomial_le _)), fun s => ?_,
    fun m hm q => ?_⟩
  · rw [ev_add, ev_monomial, ev_monomial, h1]; simp
  · rw [ev_add, ev_monomial, ev_monomial, h2 m hm]; rfl

theorem deg_list (l : List A) (hl : ∀ a ∈ l, a ∈ L.fns) : Deg L Y 0 (fun _ => l.prod) := by
  induction l with
  | nil => exact deg_const _ (by simp)
  | cons a l ih =>
    simpa using (deg_fn (hl a (by simp))).mul (ih fun b hb => hl b (by simp [hb]))

theorem deg_Tl (l : Fin r) (i j : Fin 2) : Deg L Y 1 (fun y => L.Tl y l i j) := by
  have hc : L.c l ∈ L.fns := by simp [LevelData.fns]
  have hci : L.ci l ∈ L.fns := by simp [LevelData.fns]
  fin_cases i <;> fin_cases j <;> simp only [LevelData.Tl]
  · refine deg_lin _ 1 (fun s => ?_) fun m hm q => ?_
    · simp [add_right_comm]
    · simp [add_mul, mul_add, (hm q).2.1 l, Algebra.commutes, add_assoc]
  · refine (deg_const _ fun m hm q => ?_).mono zero_le_one
    exact ((hm q).1 _ hc).neg_left.eq
  · refine (deg_const _ fun m hm q => ?_).mono zero_le_one
    simpa using ((hm q).1 _ hci).eq
  · refine (deg_const _ fun m hm q => ?_).mono zero_le_one
    exact (Commute.zero_left (m q)).eq

theorem deg_prod (l : List (Fin r)) (i j : Fin 2) :
    Deg L Y l.length (fun y => (l.map (L.Tl y)).prod i j) := by
  induction l generalizing i j with
  | nil =>
    refine deg_const ((1 : Matrix (Fin 2) (Fin 2) A) i j) fun m _ q => ?_
    rw [Matrix.one_apply]; split_ifs <;> simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, Matrix.mul_apply, Fin.sum_univ_two, List.length_cons]
    rw [add_comm l.length 1]
    exact ((deg_Tl a i 0).mul (ih 0 j)).add ((deg_Tl a i 1).mul (ih 1 j))

theorem deg_Tprod (i j : Fin 2) : Deg L Y r (fun y => L.Tprod y i j) := by
  have h := deg_prod (L := L) (Y := Y) (List.finRange r).reverse i j
  simp only [List.length_reverse, List.length_finRange] at h
  simpa only [LevelData.Tprod, List.ofFn_eq_map, List.map_reverse] using h

theorem forwardTaylorDegree_one_leftLetter : Deg L Y 1 L.l0 := by
  refine deg_lin _ (-(L.ζb * L.GGi)) (fun s => ?_) fun m hm q => ?_
  · simp only [LevelData.l0, add_right_comm Y s, map_add (algebraMap ℂ A) (Y + 1 / 2) s]
    noncomm_ring
  · have c1 : ∀ q, Commute (L.ζb * L.GGi) (m q) := fun q =>
      ((hm q).1 _ (by simp [LevelData.fns])).mul_left ((hm q).1 _ (by simp [LevelData.fns]))
    have c2 : Commute (algebraMap ℂ A (Y + 1 / 2) * (L.ζb * L.GGi)) (m q) :=
      (Algebra.commute_algebraMap_left _ _).mul_left (c1 q)
    rw [LevelData.l0, sub_mul, neg_mul, (hm q).2.2.2.1, c2.eq, (c1 (q + 1)).eq]
    noncomm_ring

theorem deg_Ahat : Deg L Y r L.Ahat := by
  have h := (deg_list (L := L) (Y := Y) (List.ofFn L.c) (by
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha
    simp [LevelData.fns])).mul (deg_Tprod 0 0)
  rw [zero_add] at h
  exact h

theorem forwardTaylorDegree_plusHatR : Deg L Y (r + 1) L.R0 := by
  have h := ((deg_list (L := L) (Y := Y) (List.ofFn L.cb) (by
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha
    simp [LevelData.fns])).mul (deg_fn (a := L.GG) (by simp [LevelData.fns]))).mul
    ((forwardTaylorDegree_one_leftLetter.mul (deg_Tprod 0 0)).add ((deg_Tprod 1 0).mono (Nat.le_add_left _ _)))
  rw [zero_add, zero_add, add_comm 1 r] at h
  exact h

theorem taylor_plus : ∀ (A : Type) [Ring A] [Algebra ℂ A] (r : ℕ) (L : LevelData A r), ∀ Y : ℂ, ∃ Xa Xr : ℕ → A, (∀ s : ℂ, L.Ahat (Y + s) = ∑ j ∈ Finset.range (r + 2), s ^ j • Xa j) ∧ (∀ s : ℂ, L.R0 (Y + s) = ∑ j ∈ Finset.range (r + 2), s ^ j • Xr j) ∧ ∀ m : ℕ → A, MulRel L m → ∀ q, L.Ahat Y * m q = ∑ j ∈ Finset.range (r + 2), m (q + j) * Xa j ∧ L.R0 Y * m q = ∑ j ∈ Finset.range (r + 2), m (q + j) * Xr j := by
  intro A _ _ r L Y
  obtain ⟨P, h1, h2, h3⟩ := deg_Ahat (L := L) (Y := Y)
  obtain ⟨Q, k1, k2, k3⟩ := forwardTaylorDegree_plusHatR (L := L) (Y := Y)
  have hP : P.natDegree < r + 2 := by omega
  have hQ : Q.natDegree < r + 2 := by omega
  refine ⟨P.coeff, Q.coeff, fun s => ?_, fun s => ?_, fun m hm q => ⟨?_, ?_⟩⟩
  · rw [h2, ev_eq_sum _ _ _ hP]; simp only [Algebra.smul_def]
  · rw [k2, ev_eq_sum _ _ _ hQ]; simp only [Algebra.smul_def]
  · rw [h3 m hm, ev_eq_sum _ _ _ hP]
  · rw [k3 m hm, ev_eq_sum _ _ _ hQ]

end

end GlobalTheory.HatTaylorPlus
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.PlusHatsTaylorCoeffLeibnizRuleStatement
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.plusHats_taylorCoeff_leibniz_rule : ∀ (A : Type) [Ring A] [Algebra ℂ A] (r : ℕ) (L : LevelData A r), ∀ Y : ℂ, ∃ Xa Xr : ℕ → A, (∀ s : ℂ, L.Ahat (Y + s) = ∑ j ∈ Finset.range (r + 2), s ^ j • Xa j) ∧ (∀ s : ℂ, L.R0 (Y + s) = ∑ j ∈ Finset.range (r + 2), s ^ j • Xr j) ∧ ∀ m : ℕ → A, MulRel L m → ∀ q, L.Ahat Y * m q = ∑ j ∈ Finset.range (r + 2), m (q + j) * Xa j ∧ L.R0 Y * m q = ∑ j ∈ Finset.range (r + 2), m (q + j) * Xr j := by
  first | exact @GlobalTheory.HatTaylorPlus.taylor_plus | exact GlobalTheory.HatTaylorPlus.taylor_plus | (intros; apply GlobalTheory.HatTaylorPlus.taylor_plus <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.VecPolyMemSpanValuesStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.VecPolyMemSpanValues
namespace GlobalTheory

theorem vecPoly_mem_span_values (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (Z : ℂ → V)
    (X : ℕ → V) (ν : Fin n → ℂ) (hν : Function.Injective ν)
    (hZ : ∀ s : ℂ, Z s = ∑ j ∈ Finset.range n, s ^ j • X j) :
    (∀ j, j < n → X j ∈ Submodule.span ℂ (Set.range fun i => Z (ν i))) ∧
      ∀ s : ℂ, Z s ∈ Submodule.span ℂ (Set.range fun i => Z (ν i)) := by
  classical
  set W := Submodule.span ℂ (Set.range fun i => Z (ν i)) with hW
  set M : Matrix (Fin n) (Fin n) ℂ := Matrix.vandermonde ν with hM
  have hunit : IsUnit M.det := isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hν)
  have hinv : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hunit
  have hZν : ∀ i, Z (ν i) = ∑ l : Fin n, M i l • X l := by
    intro i
    rw [hZ, ← Fin.sum_univ_eq_sum_range (fun j => ν i ^ j • X j) n]
    simp [hM, Matrix.vandermonde_apply]
  have hX : ∀ k : Fin n, X k ∈ W := by
    intro k
    have key : ∀ l, ∑ i, M⁻¹ k i * M i l = (1 : Matrix (Fin n) (Fin n) ℂ) k l := fun l => by
      rw [← hinv, Matrix.mul_apply]
    have hsum : ∑ i : Fin n, M⁻¹ k i • Z (ν i) = X k := by
      simp_rw [hZν, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_smul, key, Matrix.one_apply, ite_smul, one_smul, zero_smul]
      simp
    rw [← hsum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  refine ⟨fun j hj => hX ⟨j, hj⟩, fun s => ?_⟩
  rw [hZ]
  exact Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ (hX ⟨j, Finset.mem_range.mp hj⟩)

end GlobalTheory
end

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_span_values_of_vector_polynomial : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (Z : ℂ → V) (X : ℕ → V) (ν : Fin n → ℂ), Function.Injective ν → (∀ s : ℂ, Z s = ∑ j ∈ Finset.range n, s ^ j • X j) → (∀ j, j < n → X j ∈ Submodule.span ℂ (Set.range fun i => Z (ν i))) ∧ ∀ s : ℂ, Z s ∈ Submodule.span ℂ (Set.range fun i => Z (ν i)) := by
  first | exact @GlobalTheory.vecPoly_mem_span_values | exact GlobalTheory.vecPoly_mem_span_values | (intros; apply GlobalTheory.vecPoly_mem_span_values <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ListProdHatLettersMemNormalFormProductSpan
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ListProdHatLettersMemNormalFormProductSpan
namespace GlobalTheory.HatNF

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

theorem hats_prod_mem_nfSpan : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ (T : Set A) (a : ℕ), (∀ X ∈ hats d.L, X ∈ nfSpan d T 0 a 1) → ∀ H : List A, (∀ h ∈ H, h ∈ hats d.L) → H.prod ∈ nfSpan d T 0 (a * H.length) H.length := by
  intro P A _ _ _ _ d hd T a ha H
  induction H with
  | nil =>
    intro _
    refine Submodule.subset_span ⟨1, (bmon d).one_mem, [], rfl, by simp, ?_⟩
    simp
  | cons X H ih =>
    intro hH
    have h1 := ih (fun h hh => hH h (List.mem_cons_of_mem _ hh))
    have h2 := (GlobalTheory.T.normalFormProductSpan_left_mul_closed P A d hd T).2 a ha 0 (a * H.length) H.length X
      (hH X List.mem_cons_self) _ h1
    rw [List.prod_cons, List.length_cons, Nat.mul_succ]
    exact h2

end GlobalTheory.HatNF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ListProdHatLettersMemNormalFormProductSpanStatement
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.list_prod_hatLetters_mem_normalFormProductSpan : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ (T : Set A) (a : ℕ), (∀ X ∈ hats d.L, X ∈ nfSpan d T 0 a 1) → ∀ H : List A, (∀ h ∈ H, h ∈ hats d.L) → H.prod ∈ nfSpan d T 0 (a * H.length) H.length := by
  first | exact @GlobalTheory.HatNF.hats_prod_mem_nfSpan | exact GlobalTheory.HatNF.hats_prod_mem_nfSpan | (intros; apply GlobalTheory.HatNF.hats_prod_mem_nfSpan <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HatLettersMemNormalFormProductSpan
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.R0MemNfSpanOfHatHyp
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.R0MemNfSpanOfHatHyp
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF.HatCommutators

section lists
variable {A : Type} [Ring A]

theorem comm_ofFn {n : ℕ} (f : Fin n → A) (a : A) (h : ∀ l, Commute a (f l)) :
    Commute a (List.ofFn f).prod := by
  apply Commute.list_prod_right
  intro x hx
  rw [List.mem_ofFn] at hx
  obtain ⟨l, rfl⟩ := hx
  exact h l

theorem ofFn_mul_inv : ∀ {n : ℕ} (f g : Fin n → A), (∀ l, f l * g l = 1) → (∀ l m, Commute (g l) (f m)) →
    (List.ofFn f).prod * (List.ofFn g).prod = 1
  | 0, _, _, _, _ => by simp
  | n + 1, f, g, h, hc => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons]
    have ih := ofFn_mul_inv (n := n) (fun i => f i.succ) (fun i => g i.succ)
      (fun l => h l.succ) (fun l m => hc l.succ m.succ)
    have hc' := comm_ofFn (fun i : Fin n => f i.succ) (g 0) (fun l => hc 0 l.succ)
    rw [mul_assoc, ← mul_assoc _ (g 0), ← hc'.eq, mul_assoc, ih, mul_one, h]

theorem star_ofFn [StarRing A] : ∀ {n : ℕ} (f g : Fin n → A), (∀ l, star (f l) = g l) →
    (∀ l m, Commute (g l) (g m)) → star (List.ofFn f).prod = (List.ofFn g).prod
  | 0, _, _, _, _ => by simp
  | n + 1, f, g, h, hc => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, star_mul]
    have ih := star_ofFn (n := n) (fun i => f i.succ) (fun i => g i.succ)
      (fun l => h l.succ) (fun l m => hc l.succ m.succ)
    have hc' := comm_ofFn (fun i : Fin n => g i.succ) (g 0) (fun l => hc 0 l.succ)
    rw [ih, h, hc'.eq]

end lists

variable {A : Type} [Ring A] [Algebra ℂ A]

section level
variable {r : ℕ} (L : LevelData A r)

theorem c_mem (l : Fin r) : L.c l ∈ L.fns := by simp [LevelData.fns]
theorem ci_mem (l : Fin r) : L.ci l ∈ L.fns := by simp [LevelData.fns]
theorem cb_mem (l : Fin r) : L.cb l ∈ L.fns := by simp [LevelData.fns]
theorem cbi_mem (l : Fin r) : L.cbi l ∈ L.fns := by simp [LevelData.fns]
theorem GG_mem : L.GG ∈ L.fns := by simp [LevelData.fns]

theorem fcomm {x y : A} (hx : x ∈ L.fns) (hy : y ∈ L.fns) : Commute x y := L.fns_comm x hx y hy

theorem comm_Dr {a : A} (h : ∀ g ∈ L.fns, Commute a g) : Commute a L.Dr :=
  comm_ofFn _ _ fun l => h _ (c_mem L l)
theorem comm_Drb {a : A} (h : ∀ g ∈ L.fns, Commute a g) : Commute a L.Drb :=
  comm_ofFn _ _ fun l => h _ (cb_mem L l)

theorem Dri_Dr : L.Dri * L.Dr = 1 :=
  ofFn_mul_inv _ _ L.ci_c fun l m => fcomm L (c_mem L l) (ci_mem L m)
theorem Drbi_Drb : L.Drbi * L.Drb = 1 :=
  ofFn_mul_inv _ _ L.cbi_cb fun l m => fcomm L (cb_mem L l) (cbi_mem L m)
theorem Dr_Drb : Commute L.Dr L.Drb :=
  comm_ofFn _ _ fun l => (comm_Dr L fun _ hg => fcomm L (cb_mem L l) hg).symm

end level

variable [StarRing A] {P : M.Par} (d : Q.NFData P A)

theorem mem_span {b h : A} (hb : b ∈ bmon d) (hh : h ∈ basics d) : b * h ∈ nfSpan d (basics d) 0 0 1 :=
  Submodule.subset_span ⟨b, hb, [h], rfl, by simpa using hh, by simp⟩

theorem kap_mem (f : M.Ty P → ℂ) : d.κ f ∈ bmon d :=
  Submonoid.subset_closure (Or.inl (Or.inl (Or.inr ⟨f, rfl⟩)))

theorem ssn_mem {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) : ssn d l ∈ bmon d :=
  Submonoid.subset_closure (Or.inl (Or.inr ⟨l, by simpa using hl, rfl⟩))

theorem star_ssn_mem {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) : star (ssn d l) ∈ bmon d :=
  Submonoid.subset_closure (Or.inr ⟨l, by simpa using hl, rfl⟩)

theorem rh_eq (hR : d.Rel) (y : ℂ) :
    rh d y = d.x y * d.L.R0 y +
      ∑ l ∈ Finset.Icc 1 (P.k - 1), ssn d l * (d.κ fun ρ => M.xEx P {l} ρ y) * d.L.Ahat y := by
  obtain ⟨-, hκ, hS, -⟩ := hR
  have hκ' : ∀ f, ∀ g ∈ d.L.fns, Commute (d.κ f) g := fun f g hg => hκ f g (Or.inl hg)
  have hS' : ∀ l, ∀ g ∈ d.L.fns, Commute (d.SS l) g := fun l g hg => hS l g (Or.inl (Or.inl hg))
  have h1 : d.L.Drb * (d.L.GG * d.x y) = d.x y * (d.L.Drb * d.L.GG) := by
    have := ((comm_Drb d.L (hκ' fun ρ => M.xC P ρ y)).mul_right (hκ' _ _ (GG_mem d.L))).eq
    rw [← mul_assoc]; exact this.symm
  have h2 : ∀ l, ssn d l * (d.κ fun ρ => M.xEx P {l} ρ y) * d.L.Ahat y =
      d.L.Drb * (d.SS l * (d.κ fun ρ => M.xEx P {l} ρ y)) * d.L.Ar y := by
    intro l
    have hc := ((comm_Dr d.L (hS' l)).mul_left (comm_Dr d.L (hκ' fun ρ => M.xEx P {l} ρ y))).eq
    calc _ = d.L.Drb * d.L.Dri * ((d.SS l * (d.κ fun ρ => M.xEx P {l} ρ y)) * d.L.Dr) * d.L.Ar y := by
          simp only [ssn, LevelData.Ahat, mul_assoc]
      _ = d.L.Drb * (d.L.Dri * d.L.Dr) * (d.SS l * (d.κ fun ρ => M.xEx P {l} ρ y)) * d.L.Ar y := by
          rw [hc]; simp only [mul_assoc]
      _ = _ := by rw [Dri_Dr, mul_one]
  simp only [h2]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  change d.L.Drb * ((d.L.GG * d.x y * d.L.l0 y + d.weightedSumBis y) * d.L.Ar y + d.L.GG * d.x y * d.L.Br y) =
    d.x y * (d.L.Drb * d.L.GG * (d.L.l0 y * d.L.Ar y + d.L.Br y)) + d.L.Drb * d.weightedSumBis y * d.L.Ar y
  rw [← mul_assoc (d.x y), ← h1]
  noncomm_ring

theorem rhv_eq (hR : d.Rel) (hc : ∀ l, star (d.L.c l) = d.L.cb l) (hci : ∀ l, star (d.L.ci l) = d.L.cbi l)
    (y : ℂ) :
    rhv d y = d.x y * d.L.R0v y +
      ∑ l ∈ Finset.Icc 1 (P.k - 1), (d.κ fun ρ => M.xEx P {l} ρ y) * star (ssn d l) * d.L.Ahatv y := by
  obtain ⟨-, hκ, hS, -⟩ := hR
  have hκ' : ∀ f, ∀ g ∈ d.L.fns, Commute (d.κ f) g := fun f g hg => hκ f g (Or.inl hg)
  have hS' : ∀ l, ∀ g ∈ d.L.fns, Commute (d.SS l) g := fun l g hg => hS l g (Or.inl (Or.inl hg))
  have h1 : d.L.Dr * (d.L.GG * d.x y) = d.x y * (d.L.Dr * d.L.GG) := by
    have := ((comm_Dr d.L (hκ' fun ρ => M.xC P ρ y)).mul_right (hκ' _ _ (GG_mem d.L))).eq
    rw [← mul_assoc]; exact this.symm
  have s1 : star d.L.Drb = d.L.Dr :=
    star_ofFn _ _ (fun l => by rw [← hc, star_star]) fun l m => fcomm d.L (c_mem _ l) (c_mem _ m)
  have s2 : star d.L.Dri = d.L.Drbi :=
    star_ofFn _ _ hci fun l m => fcomm d.L (cbi_mem _ l) (cbi_mem _ m)
  have h2 : ∀ l, (d.κ fun ρ => M.xEx P {l} ρ y) * star (ssn d l) * d.L.Ahatv y =
      d.L.Dr * ((d.κ fun ρ => M.xEx P {l} ρ y) * star (d.SS l)) * d.L.Avr y := by
    intro l
    have hs : Commute (star (d.SS l)) d.L.Dr := by
      rw [← s1]; exact (comm_Drb d.L (hS' l)).star_star
    have hc := ((comm_Dr d.L (hκ' fun ρ => M.xEx P {l} ρ y)).mul_left hs).eq
    calc _ = (d.κ fun ρ => M.xEx P {l} ρ y) * star (d.SS l) * (d.L.Drbi * (d.L.Dr * d.L.Drb)) * d.L.Avr y := by
          simp only [ssn, LevelData.Ahatv, star_mul, s1, s2, mul_assoc]
      _ = (d.κ fun ρ => M.xEx P {l} ρ y) * star (d.SS l) * d.L.Dr * d.L.Avr y := by
          rw [(Dr_Drb d.L).eq, ← mul_assoc d.L.Drbi, Drbi_Drb, one_mul]
      _ = _ := by rw [hc]
  simp only [h2]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  change d.L.Dr * ((d.L.GG * d.x y * d.L.m0 y + d.S12 y) * d.L.Avr y + d.L.GG * d.x y * d.L.Bvr y) =
    d.x y * (d.L.Dr * d.L.GG * (d.L.m0 y * d.L.Avr y + d.L.Bvr y)) + d.L.Dr * d.S12 y * d.L.Avr y
  rw [← mul_assoc (d.x y), ← h1]
  noncomm_ring

theorem xinv_mul (y : ℂ) (hy : ∀ ρ : M.Ty P, M.xC P ρ y ≠ 0) :
    (d.κ fun ρ => (M.xC P ρ y)⁻¹) * d.x y = 1 := by
  rw [Q.NFData.x, ← map_mul, ← map_one d.κ]
  congr 1
  funext ρ
  exact inv_mul_cancel₀ (hy ρ)

end GlobalTheory.HatNF.HatCommutators

namespace GlobalTheory.HatNF

open HatCommutators

theorem r0_mem_nfSpan_basics : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ y : ℝ, (∀ ρ : M.Ty P, M.xC P ρ (y : ℂ) ≠ 0 ∧ M.xC P ρ ((y : ℂ) - 1) ≠ 0 ∧ M.xC P ρ ((y : ℂ) + 1) ≠ 0) → d.L.R0 y ∈ nfSpan d (basics d) 0 0 1 ∧ d.L.R0v y ∈ nfSpan d (basics d) 0 0 1 := by
  intro P A _ _ _ _ d hd y hy
  obtain ⟨-, -, hR, -, hc, hci, -⟩ := hd
  have hx := xinv_mul d (y : ℂ) fun ρ => (hy ρ).1
  have hk := kap_mem d fun ρ => (M.xC P ρ (y : ℂ))⁻¹
  set k := d.κ fun ρ => (M.xC P ρ (y : ℂ))⁻¹
  constructor
  · have e : d.L.R0 y = k * rh d y - ∑ l ∈ Finset.Icc 1 (P.k - 1),
        (k * ssn d l * (d.κ fun ρ => M.xEx P {l} ρ y)) * d.L.Ahat y := by
      rw [rh_eq d hR, mul_add, ← mul_assoc, hx, one_mul, Finset.mul_sum]
      simp only [mul_assoc, add_sub_cancel_right]
    rw [e]
    refine Submodule.sub_mem _ (mem_span d hk ⟨y, hy, by simp⟩) (Submodule.sum_mem _ fun l hl => ?_)
    exact mem_span d (mul_mem (mul_mem hk (ssn_mem d hl)) (kap_mem d _)) ⟨y, hy, by simp⟩
  · have e : d.L.R0v y = k * rhv d y - ∑ l ∈ Finset.Icc 1 (P.k - 1),
        (k * (d.κ fun ρ => M.xEx P {l} ρ y) * star (ssn d l)) * d.L.Ahatv y := by
      rw [rhv_eq d hR hc hci, mul_add, ← mul_assoc, hx, one_mul, Finset.mul_sum]
      simp only [mul_assoc, add_sub_cancel_right]
    rw [e]
    refine Submodule.sub_mem _ (mem_span d hk ⟨y, hy, by simp⟩) (Submodule.sum_mem _ fun l hl => ?_)
    exact mem_span d (mul_mem (mul_mem hk (kap_mem d _)) (star_ssn_mem d hl)) ⟨y, hy, by simp⟩

end GlobalTheory.HatNF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.R0MemNfSpanOfHatHypStatement
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.R0_and_R0v_mem_nfSpan_basics_of_xC_ne_zero : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ y : ℝ, (∀ ρ : M.Ty P, M.xC P ρ (y : ℂ) ≠ 0 ∧ M.xC P ρ ((y : ℂ) - 1) ≠ 0 ∧ M.xC P ρ ((y : ℂ) + 1) ≠ 0) → d.L.R0 y ∈ nfSpan d (basics d) 0 0 1 ∧ d.L.R0v y ∈ nfSpan d (basics d) 0 0 1 := by
  first | exact @GlobalTheory.HatNF.r0_mem_nfSpan_basics | exact GlobalTheory.HatNF.r0_mem_nfSpan_basics | (intros; apply GlobalTheory.HatNF.r0_mem_nfSpan_basics <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HatLettersMemNormalFormProductSpan
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF

theorem hatExp_exists_bound (P : M.Par) :
    ∃ C : ℝ, ∀ t : ℝ, C ≤ t → ∀ ρ : M.Ty P, M.xC P ρ (t : ℂ) ≠ 0 := by
  obtain ⟨C, hC⟩ := (Set.toFinite
    ((fun x : M.Ty P × ℕ => -M.rho P x.1 x.2) ''
      ((Finset.univ ×ˢ Finset.Icc 1 (P.k - 1) : Finset (M.Ty P × ℕ)) : Set (M.Ty P × ℕ)))).bddAbove
  refine ⟨C + 1, fun t ht ρ => ?_⟩
  unfold M.xC
  refine Finset.prod_ne_zero_iff.2 fun i hi => ?_
  have h1 : -M.rho P ρ i ≤ C :=
    hC ⟨(ρ, i), Finset.mem_coe.2 (Finset.mem_product.2 ⟨Finset.mem_univ _, hi⟩), rfl⟩
  have h2 : t + M.rho P ρ i ≠ 0 := (show 0 < t + M.rho P ρ i by linarith).ne'
  exact_mod_cast h2

theorem hatExp_exists_nodes (P : M.Par) (n : ℕ) :
    ∃ y : Fin n → ℝ, Function.Injective y ∧ ∀ i, ∀ ρ : M.Ty P,
      M.xC P ρ (y i : ℂ) ≠ 0 ∧ M.xC P ρ ((y i : ℂ) - 1) ≠ 0 ∧ M.xC P ρ ((y i : ℂ) + 1) ≠ 0 := by
  obtain ⟨C, hC⟩ := hatExp_exists_bound P
  refine ⟨fun i => C + 1 + (i : ℕ), fun i j h => ?_, fun i ρ => ?_⟩
  · have h' : ((i : ℕ) : ℝ) = (j : ℕ) := by simpa using h
    exact Fin.ext (by exact_mod_cast h')
  · have h0 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
    refine ⟨hC _ (by linarith) ρ, ?_, ?_⟩
    · have := hC (C + 1 + (i : ℕ) - 1) (by linarith) ρ
      rwa [Complex.ofReal_sub, Complex.ofReal_one] at this
    · have := hC (C + 1 + (i : ℕ) + 1) (by linarith) ρ
      rwa [Complex.ofReal_add _ 1, Complex.ofReal_one] at this

theorem hats_mem_nfSpan : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ (T : Set A) (a : ℕ), (∀ x ∈ basics d, x ∈ nfSpan d T 0 a 1) → ∀ X ∈ hats d.L, X ∈ nfSpan d T 0 a 1 := by
  intro P A _ _ _ _ d hd T a hT
  have hle : nfSpan d (basics d) 0 0 1 ≤ nfSpan d T 0 a 1 := by
    unfold nfSpan
    refine Submodule.span_le.2 ?_
    rintro x ⟨b, hb, H, hH, hHT, rfl⟩
    obtain ⟨h, rfl⟩ := List.length_eq_one_iff.1 hH
    have h1 := ((GlobalTheory.T.normalFormProductSpan_left_mul_closed P A d hd T).1 0 a 1 h (hT h (hHT h (List.mem_singleton_self h)))).1 b hb
    simpa [nfSpan] using h1
  obtain ⟨y, hy, hreg⟩ := hatExp_exists_nodes P (P.r + 2)
  have hyc : Function.Injective fun i => (y i : ℂ) := fun i j h => hy (Complex.ofReal_injective h)
  have hyn : Function.Injective fun i => -(y i : ℂ) := fun i j h => hyc (neg_injective h)
  have key : ∀ (Z : ℂ → A) (X : ℕ → A) (ν : Fin (P.r + 2) → ℂ), Function.Injective ν →
      (∀ s : ℂ, Z s = ∑ j ∈ Finset.range (P.r + 2), s ^ j • X j) →
      (∀ i, Z (ν i) ∈ nfSpan d T 0 a 1) → ∀ s, Z s ∈ nfSpan d T 0 a 1 := by
    intro Z X ν hν hZ hi s
    refine (Submodule.span_le.2 ?_) ((GlobalTheory.T.mem_span_values_of_vector_polynomial A (P.r + 2) Z X ν hν hZ).2 s)
    rintro _ ⟨i, rfl⟩
    exact hi i
  obtain ⟨Xa, Xr, hXa, hXr, -⟩ := GlobalTheory.T.plusHats_taylorCoeff_leibniz_rule A P.r d.L 0
  obtain ⟨Va, Vr, hVa, hVr, -⟩ := GlobalTheory.T.minusHats_taylorCoeff_leibniz_rule A P.r d.L 0
  rintro X (((⟨s, rfl⟩ | ⟨s, rfl⟩) | ⟨s, rfl⟩) | ⟨s, rfl⟩)
  · have := key (fun s => d.L.Ahat (0 + s)) Xa _ hyc hXa
      (fun i => by simpa using hT _ ⟨y i, hreg i, Or.inl rfl⟩) s
    simpa using this
  · have := key (fun s => d.L.R0 (0 + s)) Xr _ hyc hXr
      (fun i => by simpa using hle (GlobalTheory.T.R0_and_R0v_mem_nfSpan_basics_of_xC_ne_zero P A d hd (y i) (hreg i)).1) s
    simpa using this
  · have := key (fun s => d.L.Ahatv (0 - s)) Va _ hyn hVa
      (fun i => by simpa using hT _ ⟨y i, hreg i, Or.inr (Or.inl rfl)⟩) (-s)
    simpa using this
  · have := key (fun s => d.L.R0v (0 - s)) Vr _ hyn hVr
      (fun i => by simpa using hle (GlobalTheory.T.R0_and_R0v_mem_nfSpan_basics_of_xC_ne_zero P A d hd (y i) (hreg i)).2) (-s)
    simpa using this

end GlobalTheory.HatNF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HatLettersMemNormalFormProductSpanStatement
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hatLetters_mem_normalFormProductSpan : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ (T : Set A) (a : ℕ), (∀ x ∈ basics d, x ∈ nfSpan d T 0 a 1) → ∀ X ∈ hats d.L, X ∈ nfSpan d T 0 a 1 := by
  first | exact @GlobalTheory.HatNF.hats_mem_nfSpan | exact GlobalTheory.HatNF.hats_mem_nfSpan | (intros; apply GlobalTheory.HatNF.hats_mem_nfSpan <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HatLettersProdMulMultiplierLeibniz
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HatLettersProdMulMultiplierLeibniz
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF

private theorem exists_hat_mul_m_eq_double_sum {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ}
    (L : _root_.Formalism.FourierDecayAlt.R.LevelData A r) (h : A) (Z : ℂ → A) (Xc : ℕ → A)
    (hZ : ∀ s : ℂ, Z s = ∑ j ∈ Finset.range (r + 2), s ^ j • Xc j)
    (hrule : ∀ m : ℕ → A, _root_.GlobalTheory.HatNF.MulRel L m → ∀ q,
      h * m q = ∑ j ∈ Finset.range (r + 2), m (q + j) * Xc j)
    (hmem : ∀ s, Z s ∈ _root_.GlobalTheory.HatNF.hats L) :
    ∃ (d : Fin (r + 2) → Fin (r + 2) → ℂ) (g : Fin (r + 2) → A),
      (∀ i, g i ∈ _root_.GlobalTheory.HatNF.hats L) ∧ ∀ m : ℕ → A, _root_.GlobalTheory.HatNF.MulRel L m → ∀ q,
        h * m q = ∑ j : Fin (r + 2), ∑ i : Fin (r + 2), d j i • (m (q + j) * g i) := by
  have hν : Function.Injective (fun i : Fin (r + 2) => ((i : ℕ) : ℂ)) :=
    fun i j hij => Fin.ext (by simpa using hij)
  have hspan := (_root_.GlobalTheory.vecPoly_mem_span_values A (r + 2) Z Xc _ hν hZ).1
  have hcoef : ∀ j : Fin (r + 2), ∃ c : Fin (r + 2) → ℂ,
      ∑ i, c i • Z ((i : ℕ) : ℂ) = Xc j :=
    fun j => (Submodule.mem_span_range_iff_exists_fun ℂ).mp (hspan j j.2)
  choose d hd using hcoef
  refine ⟨d, fun i => Z ((i : ℕ) : ℂ), fun i => hmem _, fun m hm q => ?_⟩
  rw [hrule m hm q, Finset.sum_range (fun j => m (q + j) * Xc j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← hd j, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_smul_comm]

private theorem exists_hat_mul_multiplier_expansion {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ}
    (L : _root_.Formalism.FourierDecayAlt.R.LevelData A r) {h : A} (hh : h ∈ _root_.GlobalTheory.HatNF.hats L) :
    ∃ (d : Fin (r + 2) → Fin (r + 2) → ℂ) (g : Fin (r + 2) → A),
      (∀ i, g i ∈ _root_.GlobalTheory.HatNF.hats L) ∧ ∀ m : ℕ → A, _root_.GlobalTheory.HatNF.MulRel L m → ∀ q,
        h * m q = ∑ j : Fin (r + 2), ∑ i : Fin (r + 2), d j i • (m (q + j) * g i) := by
  unfold _root_.GlobalTheory.HatNF.hats at hh
  rcases hh with ((⟨Y, rfl⟩ | ⟨Y, rfl⟩) | ⟨Y, rfl⟩) | ⟨Y, rfl⟩
  · obtain ⟨Xa, Xr, hXa, hXr, hrel⟩ := _root_.GlobalTheory.HatTaylorPlus.taylor_plus A r L Y
    exact exists_hat_mul_m_eq_double_sum L _ (fun s => L.Ahat (Y + s)) Xa hXa
      (fun m hm q => (hrel m hm q).1)
      (fun s => by unfold _root_.GlobalTheory.HatNF.hats; exact Or.inl (Or.inl (Or.inl ⟨_, rfl⟩)))
  · obtain ⟨Xa, Xr, hXa, hXr, hrel⟩ := _root_.GlobalTheory.HatTaylorPlus.taylor_plus A r L Y
    exact exists_hat_mul_m_eq_double_sum L _ (fun s => L.R0 (Y + s)) Xr hXr
      (fun m hm q => (hrel m hm q).2)
      (fun s => by unfold _root_.GlobalTheory.HatNF.hats; exact Or.inl (Or.inl (Or.inr ⟨_, rfl⟩)))
  · obtain ⟨Xa, Xr, hXa, hXr, hrel⟩ := _root_.GlobalTheory.HatNF.TaylorMinus.taylor_minus A r L Y
    exact exists_hat_mul_m_eq_double_sum L _ (fun s => L.Ahatv (Y - s)) Xa hXa
      (fun m hm q => (hrel m hm q).1)
      (fun s => by unfold _root_.GlobalTheory.HatNF.hats; exact Or.inl (Or.inr ⟨_, rfl⟩))
  · obtain ⟨Xa, Xr, hXa, hXr, hrel⟩ := _root_.GlobalTheory.HatNF.TaylorMinus.taylor_minus A r L Y
    exact exists_hat_mul_m_eq_double_sum L _ (fun s => L.R0v (Y - s)) Xr hXr
      (fun m hm q => (hrel m hm q).2)
      (fun s => by unfold _root_.GlobalTheory.HatNF.hats; exact Or.inr ⟨_, rfl⟩)

private theorem exists_hatWord_mul_multiplier_expansion {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ}
    (L : _root_.Formalism.FourierDecayAlt.R.LevelData A r) (H : List A) (hH : ∀ h ∈ H, h ∈ _root_.GlobalTheory.HatNF.hats L) :
    ∃ (ι : Type) (_ : Fintype ι) (a : ι → ℕ) (c : ι → ℂ) (P : ι → List A),
      (∀ i, a i ≤ H.length * (r + 1) ∧ (P i).length = H.length ∧
        ∀ h ∈ P i, h ∈ _root_.GlobalTheory.HatNF.hats L) ∧
      ∀ m : ℕ → A, _root_.GlobalTheory.HatNF.MulRel L m → ∀ q,
        H.prod * m q = ∑ i, c i • (m (q + a i) * (P i).prod) := by
  induction H with
  | nil =>
    exact ⟨Unit, inferInstance, fun _ => 0, fun _ => 1, fun _ => [],
      fun _ => ⟨by simp, rfl, by simp⟩, fun m _ q => by simp⟩
  | cons h H ih =>
    obtain ⟨ι, _, a, c, P, hP, hrep⟩ := ih fun x hx => hH x (List.mem_cons_of_mem _ hx)
    obtain ⟨d, g, hg, hrel⟩ := exists_hat_mul_multiplier_expansion L (hH h List.mem_cons_self)
    refine ⟨ι × Fin (r + 2) × Fin (r + 2), inferInstance, fun x => a x.1 + x.2.1,
      fun x => c x.1 * d x.2.1 x.2.2, fun x => g x.2.2 :: P x.1, fun x => ⟨?_, ?_, ?_⟩,
      fun m hm q => ?_⟩
    · have h1 := (hP x.1).1
      have h2 : (x.2.1 : ℕ) ≤ r + 1 := Nat.lt_succ_iff.mp x.2.1.isLt
      rw [List.length_cons, Nat.succ_mul]
      linarith
    · simp [(hP x.1).2.1]
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hg _
      · exact (hP x.1).2.2 y hy
    · rw [List.prod_cons, mul_assoc, hrep m hm q, Finset.mul_sum, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Fintype.sum_prod_type, mul_smul_comm, ← mul_assoc, hrel m hm (q + a i), Finset.sum_mul,
        Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_mul, Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [List.prod_cons, smul_mul_assoc, smul_smul, add_assoc, mul_assoc]

theorem _root_.GlobalTheory.HatNF.prod_hats_mul_multiplier : ∀ (A : Type) [Ring A] [Algebra ℂ A] (r : ℕ) (L : _root_.Formalism.FourierDecayAlt.R.LevelData A r), ∀ H : List A, (∀ h ∈ H, h ∈ _root_.GlobalTheory.HatNF.hats L) → ∃ ts : List (ℕ × ℂ × List A), (∀ t ∈ ts, t.1 ≤ H.length * (r + 1) ∧ t.2.2.length = H.length ∧ ∀ h ∈ t.2.2, h ∈ _root_.GlobalTheory.HatNF.hats L) ∧ ∀ m : ℕ → A, _root_.GlobalTheory.HatNF.MulRel L m → ∀ q, H.prod * m q = (ts.map fun t => t.2.1 • (m (q + t.1) * t.2.2.prod)).sum := by
  intro A _ _ r L H hH
  obtain ⟨ι, _, a, c, P, hP, hrep⟩ := exists_hatWord_mul_multiplier_expansion L H hH
  refine ⟨(Finset.univ : Finset ι).toList.map fun i => (a i, c i, P i), ?_, fun m hm q => ?_⟩
  · intro t ht
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp ht
    exact hP i
  · rw [hrep m hm q, List.map_map, Finset.sum_map_toList]
    rfl

end GlobalTheory.HatNF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HatLettersProdMulMultiplierLeibnizStatement
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hatLetters_prod_mul_multiplier_leibniz : ∀ (A : Type) [Ring A] [Algebra ℂ A] (r : ℕ) (L : LevelData A r), ∀ H : List A, (∀ h ∈ H, h ∈ hats L) → ∃ ts : List (ℕ × ℂ × List A), (∀ t ∈ ts, t.1 ≤ H.length * (r + 1) ∧ t.2.2.length = H.length ∧ ∀ h ∈ t.2.2, h ∈ hats L) ∧ ∀ m : ℕ → A, MulRel L m → ∀ q, H.prod * m q = (ts.map fun t => t.2.1 • (m (q + t.1) * t.2.2.prod)).sum := by
  first | exact @GlobalTheory.HatNF.prod_hats_mul_multiplier | exact GlobalTheory.HatNF.prod_hats_mul_multiplier | (intros; apply GlobalTheory.HatNF.prod_hats_mul_multiplier <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WordOperatorRadialPointwiseBound
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF.RadBound

section abstract

variable {ι α : Type}

def Bd (p : ι → Prop) (ok : α → Prop) (val : α → ι → ℝ) (wt f : ι → ℝ) : Prop :=
  ∃ (C : ℝ) (Ts : List α), 0 ≤ C ∧ (∀ H ∈ Ts, ok H) ∧
    ∀ i, p i → f i ≤ C * wt i * (Ts.map fun H => val H i).sum

variable {p : ι → Prop} {ok : α → Prop} {val : α → ι → ℝ}

theorem sum_val_nonneg (hv : ∀ H i, 0 ≤ val H i) (Ts : List α) (i : ι) :
    0 ≤ (Ts.map fun H => val H i).sum :=
  List.sum_nonneg (by
    intro y hy
    obtain ⟨H, -, rfl⟩ := List.mem_map.1 hy
    exact hv H i)

theorem Bd.zero {wt : ι → ℝ} : Bd p ok val wt (fun _ => 0) :=
  ⟨0, [], le_rfl, by simp, by simp⟩

theorem Bd.add (hv : ∀ H i, 0 ≤ val H i) {wt f g : ι → ℝ} (hw : ∀ i, p i → 0 ≤ wt i)
    (hf : Bd p ok val wt f) (hg : Bd p ok val wt g) : Bd p ok val wt (fun i => f i + g i) := by
  obtain ⟨C, Ts, hC, hT, h⟩ := hf
  obtain ⟨C', Ts', hC', hT', h'⟩ := hg
  refine ⟨C + C', Ts ++ Ts', add_nonneg hC hC', ?_, fun i hi => ?_⟩
  · intro H hH
    rcases List.mem_append.1 hH with h1 | h1
    · exact hT H h1
    · exact hT' H h1
  · rw [List.map_append, List.sum_append]
    have h1 := h i hi
    have h2 := h' i hi
    have s1 := sum_val_nonneg hv Ts i
    have s2 := sum_val_nonneg hv Ts' i
    have w := hw i hi
    have e1 := mul_nonneg (mul_nonneg hC w) s2
    have e2 := mul_nonneg (mul_nonneg hC' w) s1
    nlinarith

theorem Bd.mono {wt wt' f g u : ι → ℝ} {K : ℝ} (hK : 0 ≤ K) (hu : ∀ i, p i → 0 ≤ u i)
    (hg : Bd p ok val wt g) (hfg : ∀ i, p i → f i ≤ K * u i * g i) (hw : ∀ i, p i → wt' i = u i * wt i) :
    Bd p ok val wt' f := by
  obtain ⟨C, Ts, hC, hT, h⟩ := hg
  refine ⟨K * C, Ts, mul_nonneg hK hC, hT, fun i hi => (hfg i hi).trans ?_⟩
  have := mul_le_mul_of_nonneg_left (h i hi) (mul_nonneg hK (hu i hi))
  rw [hw i hi]
  refine this.trans (le_of_eq ?_)
  ring

theorem Bd.listSum {β : Type} (hv : ∀ H i, 0 ≤ val H i) {wt : ι → ℝ} (hw : ∀ i, p i → 0 ≤ wt i)
    (g : β → ι → ℝ) (l : List β) (h : ∀ t ∈ l, Bd p ok val wt (g t)) :
    Bd p ok val wt (fun i => (l.map fun t => g t i).sum) := by
  induction l with
  | nil => simpa using Bd.zero
  | cons t l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Bd.add hv hw (h t (by simp)) (ih fun t' ht' => h t' (by simp [ht']))

end abstract

section actual

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
  {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq}

theorem nv_nonneg (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (x : (Fin P.r → ℂ) × Q.Mx P.k P.r) :
    0 ≤ nv Φ x := norm_nonneg _

theorem nv_add (Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (x : (Fin P.r → ℂ) × Q.Mx P.k P.r) :
    nv (Φ + Ψ) x ≤ nv Φ x + nv Ψ x := by
  have h : ∀ A A' : Wq →L[ℂ] Wp, B.hsVec (A + A') = B.hsVec A + B.hsVec A' := fun _ _ => rfl
  unfold nv
  rw [Submodule.coe_add, Pi.add_apply, Pi.add_apply, h]
  exact norm_add_le _ _

theorem nv_smul (c : ℂ) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (x : (Fin P.r → ℂ) × Q.Mx P.k P.r) :
    nv (c • Φ) x = ‖c‖ * nv Φ x := by
  have h : ∀ (c : ℂ) (A : Wq →L[ℂ] Wp), B.hsVec (c • A) = c • B.hsVec A := fun _ _ => rfl
  unfold nv
  rw [Submodule.coe_smul, Pi.smul_apply, Pi.smul_apply, h, norm_smul]

theorem nv_zero (x : (Fin P.r → ℂ) × Q.Mx P.k P.r) :
    nv (0 : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') x = 0 := by
  have := nv_smul (0 : ℂ) (0 : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') x
  simpa using this

theorem nv_mulOp {W : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')}
    {m : (Fin P.r → ℂ) → Q.Mx P.k P.r → ℂ} (hW : P5.multiplicationOperator W m)
    (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (x : (Fin P.r → ℂ) × Q.Mx P.k P.r) :
    nv (W Φ) x = ‖m x.1 x.2‖ * nv Φ x := by
  have h : ∀ (c : ℂ) (A : Wq →L[ℂ] Wp), B.hsVec (c • A) = c • B.hsVec A := fun _ _ => rfl
  unfold nv
  rw [hW, h, norm_smul]

theorem fst_mul (a b : RA P Bs) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
    (a * b).1 Φ = a.1 (b.1 Φ) := rfl

theorem fst_add (a b : RA P Bs) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
    (a + b).1 Φ = a.1 Φ + b.1 Φ := rfl

theorem fst_zero (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : (0 : RA P Bs).1 Φ = 0 := rfl

theorem fst_one (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : (1 : RA P Bs).1 Φ = Φ := rfl

theorem fst_smul (c : ℂ) (a : RA P Bs) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
    (c • a).1 Φ = c • a.1 Φ := rfl

theorem nv_pow {y : RA P Bs} {x : (Fin P.r → ℂ) × Q.Mx P.k P.r} {t : ℝ}
    (h : ∀ Φ, nv (y.1 Φ) x = t * nv Φ x) (n : ℕ) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
    nv ((y ^ n).1 Φ) x = t ^ n * nv Φ x := by
  induction n with
  | zero => rw [pow_zero, pow_zero, fst_one, one_mul]
  | succ n ih => rw [pow_succ', fst_mul, h, ih, pow_succ']; ring

theorem nv_listSum {β : Type} (g : β → RA P Bs) (l : List β) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')
    (x : (Fin P.r → ℂ) × Q.Mx P.k P.r) :
    nv ((l.map g).sum.1 Φ) x ≤ (l.map fun t => nv ((g t).1 Φ) x).sum := by
  induction l with
  | nil => simp only [List.map_nil, List.sum_nil, fst_zero, nv_zero, le_refl]
  | cons t l ih =>
    simp only [List.map_cons, List.sum_cons, fst_add]
    exact (nv_add _ _ _).trans (by linarith)

theorem span_bd {X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π'} {μ : Measure (Mt P.k P.r)}
    {L : LevelData (RA P Bs) P.r} {st : Start (RA P Bs)} {l0 : ℕ} {d : Q.NFData P (RA P Bs)}
    (hD : P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0) (hN : IsNF X d) (T : Set (RA P Bs)) (i j n : ℕ)
    (y : RA P Bs) (hy : y ∈ nfSpan d T i j n) :
    Bd (fun q : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' × ((Fin P.r → ℂ) × Q.Mx P.k P.r) =>
        q.2 ∈ Q.DomR P.k P.r Bs.z Bs.z')
      (fun H : List (RA P Bs) => H.length = n ∧ ∀ h ∈ H, h ∈ T) (fun H q => nv (H.prod.1 q.1) q.2)
      (fun q => (dR P Bs q.2.1 q.2.2)⁻¹ ^ i * (gR P Bs q.2.1 q.2.2)⁻¹ ^ j) (fun q => nv (y.1 q.1) q.2) := by
  have hb := (GlobalTheory.T.pointwise_bounded_radial_ops_closure_and_functions Wp Wq P Bs X μ L st l0 d hD hN).2.2.2.2.2.2.2
  have hw : ∀ q : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' × ((Fin P.r → ℂ) × Q.Mx P.k P.r),
      q.2 ∈ Q.DomR P.k P.r Bs.z Bs.z' →
      0 ≤ (dR P Bs q.2.1 q.2.2)⁻¹ ^ i * (gR P Bs q.2.1 q.2.2)⁻¹ ^ j := by
    intro q hq
    have h1 := (hb q.1 q.2 hq).1
    have h2 := (hb q.1 q.2 hq).2.1
    positivity
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, hbm, H, hl, hH, rfl⟩ := hy
    obtain ⟨C, hC, hCb⟩ := GlobalTheory.T.pointwiseBounded_of_mem_boundedFactors_monoid Wp Wq P Bs X μ L st l0 d hD hN b hbm
    refine ⟨C, [H], hC, by simpa using ⟨hl, hH⟩, fun q hq => ?_⟩
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, fst_mul]
    refine (hCb _ _ hq).trans (le_of_eq ?_)
    rw [nv_pow (fun Φ => (hb Φ q.2 hq).2.2.1), nv_pow (fun Φ => (hb Φ q.2 hq).2.2.2)]
    ring
  | zero => simpa only [fst_zero, nv_zero] using Bd.zero
  | add y z _ _ hy hz =>
    refine Bd.mono (K := 1) (u := fun _ => 1) zero_le_one (fun _ _ => zero_le_one)
      (Bd.add (fun _ _ => nv_nonneg _ _) hw hy hz) (fun q _ => ?_) (fun _ _ => (one_mul _).symm)
    rw [fst_add, one_mul, one_mul]
    exact nv_add _ _ _
  | smul c y _ hy =>
    refine Bd.mono (K := ‖c‖) (u := fun _ => 1) (norm_nonneg _) (fun _ _ => zero_le_one)
      hy (fun q _ => ?_) (fun _ _ => (one_mul _).symm)
    rw [fst_smul, nv_smul, mul_one]

end actual

theorem word_bound : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ (S : Type) [Fintype S] [DecidableEq S], ∀ (T : Set (RA P Bs)) (a : ℕ), (∀ x ∈ basics d, x ∈ nfSpan d T 0 a 1) → ∀ w : List (Letter ℂ S), admitted st w → ∃ (C : ℝ) (J : ℕ) (Ts : List (List (RA P Bs))), 0 ≤ C ∧ (∀ H ∈ Ts, H.length = w.length ∧ ∀ h ∈ H, h ∈ T) ∧ ∀ (φ : ℝ → ℝ) (W : ℕ → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')), LE.SmoothLog φ → IsMulG P Bs φ W → ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (e : Ix S), ∀ x ∈ Q.DomR P.k P.r Bs.z Bs.z', nv ((((ofWord L st w).F * TL.bTA L w) e e1).1 (W 0 Φ)) x ≤ C * ((dR P Bs x.1 x.2)⁻¹ ^ w.length * (gR P Bs x.1 x.2)⁻¹ ^ (a * w.length)) * (∑ j ∈ Finset.range (J + 1), |LE.ld j φ (gR P Bs x.1 x.2)|) * (Ts.map fun H => nv (H.prod.1 Φ) x).sum := by
  intro Wp Wq _ _ _ _ _ _ P Bs X μ L st l0 d hD hN S _ _ T a hT w hw
  obtain ⟨hH, hTie⟩ := GlobalTheory.T.normalForm_actualOperators_algebraicHypotheses Wp Wq P Bs X μ L st l0 d hD hN
  have hb := (GlobalTheory.T.pointwise_bounded_radial_ops_closure_and_functions Wp Wq P Bs X μ L st l0 d hD hN).2.2.2.2.2.2.2
  have hhat := GlobalTheory.T.hatLetters_mem_normalFormProductSpan P _ d hH T a hT
  set N := w.length with hNdef
  let ι : Type := (ℝ → ℝ) × (ℕ → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) ×
    Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' × ((Fin P.r → ℂ) × Q.Mx P.k P.r)
  let p : ι → Prop := fun q => LE.SmoothLog q.1 ∧ IsMulG P Bs q.1 q.2.1 ∧ q.2.2.2 ∈ Q.DomR P.k P.r Bs.z Bs.z'
  let ok : List (RA P Bs) → Prop := fun H => H.length = N ∧ ∀ h ∈ H, h ∈ T
  let val : List (RA P Bs) → ι → ℝ := fun H q => nv (H.prod.1 q.2.2.1) q.2.2.2
  let G : ι → ℝ := fun q => (gR P Bs q.2.2.2.1 q.2.2.2.2)⁻¹ ^ (a * N)
  let Dd : ι → ℝ := fun q => (dR P Bs q.2.2.2.1 q.2.2.2.2)⁻¹ ^ N
  let Sg : ι → ℝ := fun q => ∑ j ∈ Finset.range (N * (P.r + 1) + 1), |LE.ld j q.1 (gR P Bs q.2.2.2.1 q.2.2.2.2)|
  have hv : ∀ H q, 0 ≤ val H q := fun _ _ => nv_nonneg _ _
  have hG : ∀ q, p q → 0 ≤ G q := fun q hq => by
    have h2 := (hb q.2.2.1 q.2.2.2 hq.2.2).2.1
    positivity
  have hDd : ∀ q, p q → 0 ≤ Dd q := fun q hq => by
    have h2 := (hb q.2.2.1 q.2.2.2 hq.2.2).1
    positivity
  have hS : ∀ q, p q → 0 ≤ Sg q := fun q _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have h1 : ∀ H : List (RA P Bs), H.length = N → (∀ h ∈ H, h ∈ hats d.L) →
      Bd p ok val G (fun q => nv (H.prod.1 q.2.2.1) q.2.2.2) := by
    intro H hl hh
    have hm := GlobalTheory.T.list_prod_hatLetters_mem_normalFormProductSpan P _ d hH T a hhat H hh
    rw [hl] at hm
    obtain ⟨C, Ts, hC, hTs, h⟩ := span_bd hD hN T 0 (a * N) N _ hm
    refine ⟨C, Ts, hC, hTs, fun q hq => ?_⟩
    have := h q.2.2 hq.2.2
    simpa only [pow_zero, one_mul] using this
  have h2 : ∀ H : List (RA P Bs), H.length = N → (∀ h ∈ H, h ∈ hats d.L) →
      Bd p ok val (fun q => Sg q * G q) (fun q => nv (H.prod.1 (q.2.1 0 q.2.2.1)) q.2.2.2) := by
    intro H hl hh
    obtain ⟨ts, hts, hmul⟩ := GlobalTheory.T.hatLetters_prod_mul_multiplier_leibniz _ P.r d.L H hh
    have h3 : ∀ t ∈ ts, Bd p ok val (fun q => Sg q * G q)
        (fun q => nv ((t.2.1 • (Q.mkP (q.2.1 (0 + t.1)) (q.2.1 (0 + t.1)) * t.2.2.prod : RA P Bs)).1 q.2.2.1)
          q.2.2.2) := by
      intro t ht
      obtain ⟨hj, hl', hh'⟩ := hts t ht
      refine Bd.mono (K := ‖t.2.1‖) (u := Sg) (norm_nonneg _) hS (h1 t.2.2 (hl'.trans hl) hh')
        (fun q hq => ?_) (fun _ _ => rfl)
      rw [fst_smul, nv_smul, fst_mul, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      change nv (q.2.1 (0 + t.1) _) _ ≤ _
      rw [nv_mulOp (hq.2.1 _), Complex.norm_real, Real.norm_eq_abs, zero_add]
      refine mul_le_mul_of_nonneg_right ?_ (nv_nonneg _ _)
      refine Finset.single_le_sum (f := fun j => |LE.ld j q.1 (gR P Bs q.2.2.2.1 q.2.2.2.2)|)
        (fun _ _ => abs_nonneg _) (Finset.mem_range.2 ?_)
      rw [hl] at hj
      omega
    refine Bd.mono (K := 1) (u := fun _ => 1) zero_le_one (fun _ _ => zero_le_one)
      (Bd.listSum hv (fun q hq => mul_nonneg (hS q hq) (hG q hq)) _ ts h3) (fun q hq => ?_)
      (fun _ _ => (one_mul _).symm)
    have hr := hmul _ (GlobalTheory.T.radialMultipliers_satisfy_normalForm_relations Wp Wq P Bs X μ L st l0 d hD hN q.1 q.2.1 hq.1 hq.2.1) 0
    rw [one_mul, one_mul]
    have e : H.prod.1 (q.2.1 0 q.2.2.1) = (H.prod * (Q.mkP (q.2.1 0) (q.2.1 0) : RA P Bs)).1 q.2.2.1 := rfl
    rw [e, hr]
    exact nv_listSum _ _ _ _
  have h4 : ∀ e : Ix S, Bd p ok val (fun q => Dd q * (Sg q * G q))
      (fun q => nv ((((ofWord L st w).F * TL.bTA L w) e e1).1 (q.2.1 0 q.2.2.1)) q.2.2.2) := by
    intro e
    obtain ⟨C, Hs, hC, hHs, h⟩ := span_bd hD hN _ _ _ _ _ (GlobalTheory.T.wordOperator_column_mem_normalFormProductSpan P _ d hH L st _ hTie S w hw e)
    refine Bd.mono (K := C) (u := Dd) hC hDd
      (Bd.listSum hv (fun q hq => mul_nonneg (hS q hq) (hG q hq)) _ Hs
        (fun H hH' => h2 H (hHs H hH').1 (hHs H hH').2)) (fun q hq => ?_) (fun _ _ => rfl)
    have := h (q.2.1 0 q.2.2.1, q.2.2.2) hq.2.2
    simpa only [pow_zero, mul_one] using this
  obtain ⟨C, Ts, hC, hTs, h⟩ := Bd.listSum hv (fun q hq => mul_nonneg (hDd q hq) (mul_nonneg (hS q hq) (hG q hq)))
    _ (Finset.univ : Finset (Ix S)).toList (fun e _ => h4 e)
  refine ⟨C, N * (P.r + 1), Ts, hC, hTs, fun φ W hφ hW Φ e x hx => ?_⟩
  have h5 := h (φ, W, Φ, x) ⟨hφ, hW, hx⟩
  beta_reduce at h5
  rw [Finset.sum_map_toList] at h5
  refine (Finset.single_le_sum (f := fun e : Ix S => nv ((((ofWord L st w).F * TL.bTA L w) e e1).1 (W 0 Φ)) x)
    (fun _ _ => nv_nonneg _ _) (Finset.mem_univ e)).trans (h5.trans (le_of_eq ?_))
  simp only [Dd, Sg, G, val]
  ring

end GlobalTheory.HatNF.RadBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WordOperatorRadialPointwiseBoundStatement
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wordOperator_radial_pointwise_bound : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ (S : Type) [Fintype S] [DecidableEq S], ∀ (T : Set (RA P Bs)) (a : ℕ), (∀ x ∈ basics d, x ∈ nfSpan d T 0 a 1) → ∀ w : List (Letter ℂ S), admitted st w → ∃ (C : ℝ) (J : ℕ) (Ts : List (List (RA P Bs))), 0 ≤ C ∧ (∀ H ∈ Ts, H.length = w.length ∧ ∀ h ∈ H, h ∈ T) ∧ ∀ (φ : ℝ → ℝ) (W : ℕ → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')), LE.SmoothLog φ → IsMulG P Bs φ W → ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (e : Ix S), ∀ x ∈ Q.DomR P.k P.r Bs.z Bs.z', nv ((((ofWord L st w).F * TL.bTA L w) e e1).1 (W 0 Φ)) x ≤ C * ((dR P Bs x.1 x.2)⁻¹ ^ w.length * (gR P Bs x.1 x.2)⁻¹ ^ (a * w.length)) * (∑ j ∈ Finset.range (J + 1), |LE.ld j φ (gR P Bs x.1 x.2)|) * (Ts.map fun H => nv (H.prod.1 Φ) x).sum := by
  first | exact @GlobalTheory.HatNF.RadBound.word_bound | exact GlobalTheory.HatNF.RadBound.word_bound | (intros; apply GlobalTheory.HatNF.RadBound.word_bound <;> assumption)
end
