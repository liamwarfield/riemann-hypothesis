module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UdlApply
namespace GlobalTheory.UnipotentDecomposition

open Matrix

theorem udl_apply {O : Type} [CommRing O] {m : ℕ} (A B : Matrix (Fin m) (Fin m) O) (d : Fin m → O) (i j : Fin m) :
    (A * Matrix.diagonal d * B) i j = ∑ k, A i k * d k * B k j := by
  rw [Matrix.mul_apply]; simp_rw [Matrix.mul_diagonal]

theorem key {O : Type} [CommRing O] [IsLocalRing O] {α β : O} (hab : ¬ IsUnit (α * β)) :
    ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) O),
      (∀ i j, (i < j → α ∣ g i j) ∧ (j < i → β ∣ g i j)) → (∀ i, IsUnit (g i i)) →
      ∃ (u : Matrix (Fin n) (Fin n) O) (d : Fin n → Oˣ) (l : Matrix (Fin n) (Fin n) O),
        (∀ i j, (j < i → u i j = 0) ∧ (i = j → u i j = 1) ∧ (i < j → α ∣ u i j)) ∧
        (∀ i j, (i < j → l i j = 0) ∧ (i = j → l i j = 1) ∧ (j < i → β ∣ l i j)) ∧
        g = (u * Matrix.diagonal fun i => (d i : O)) * l ∧ ∀ i, α * β ∣ (d i : O) - g i i := by
  intro n
  induction n with
  | zero =>
    intro g _ _
    refine ⟨1, fun i => i.elim0, 1, fun i => i.elim0, fun i => i.elim0, ?_, fun i => i.elim0⟩
    ext i; exact i.elim0
  | succ n ih =>
    intro g hg hu
    set a : Oˣ := (hu (Fin.last n)).unit with ha
    have haa : (a : O) = g (Fin.last n) (Fin.last n) := IsUnit.unit_spec _
    have hinv : (↑a⁻¹ : O) * ↑a = 1 := Units.inv_mul a
    set r : Fin n → O := fun i => g i.castSucc (Fin.last n) with hr_def
    set c : Fin n → O := fun j => g (Fin.last n) j.castSucc with hc_def
    set G : Matrix (Fin n) (Fin n) O := fun i j => g i.castSucc j.castSucc - r i * ↑a⁻¹ * c j with hG_def
    have hr : ∀ i, α ∣ r i := fun i => (hg i.castSucc (Fin.last n)).1 (Fin.castSucc_lt_last i)
    have hc : ∀ j, β ∣ c j := fun j => (hg (Fin.last n) j.castSucc).2 (Fin.castSucc_lt_last j)
    have hG : ∀ i j, (i < j → α ∣ G i j) ∧ (j < i → β ∣ G i j) := by
      intro i j
      constructor
      · intro h
        exact dvd_sub ((hg _ _).1 (Fin.castSucc_lt_castSucc_iff.2 h))
          (Dvd.dvd.mul_right (Dvd.dvd.mul_right (hr i) _) _)
      · intro h
        exact dvd_sub ((hg _ _).2 (Fin.castSucc_lt_castSucc_iff.2 h)) (Dvd.dvd.mul_left (hc j) _)
    have hrc : ∀ i, α * β ∣ r i * ↑a⁻¹ * c i := by
      intro i
      rw [show r i * ↑a⁻¹ * c i = r i * c i * ↑a⁻¹ by ring]
      exact Dvd.dvd.mul_right (mul_dvd_mul (hr i) (hc i)) _
    have hGu : ∀ i, IsUnit (G i i) := by
      intro i
      by_contra h
      have h1 : r i * ↑a⁻¹ * c i ∈ nonunits O := fun hu' => hab (isUnit_of_dvd_unit (hrc i) hu')
      have h2 := IsLocalRing.nonunits_add (show G i i ∈ nonunits O from h) h1
      have h3 : G i i + r i * ↑a⁻¹ * c i = g i.castSucc i.castSucc := sub_add_cancel _ _
      rw [h3] at h2
      exact h2 (hu _)
    obtain ⟨U, D, L, hU, hL, hUDL, hD⟩ := ih G hG hGu
    refine ⟨Matrix.of fun i j => Fin.lastCases (motive := fun _ => O)
              (Fin.lastCases (motive := fun _ => O) 1 (fun _ => 0) j)
              (fun i' => Fin.lastCases (motive := fun _ => O) (r i' * ↑a⁻¹) (fun j' => U i' j') j) i,
            fun i => Fin.lastCases (motive := fun _ => Oˣ) a D i,
            Matrix.of fun i j => Fin.lastCases (motive := fun _ => O)
              (Fin.lastCases (motive := fun _ => O) 1 (fun j' => ↑a⁻¹ * c j') j)
              (fun i' => Fin.lastCases (motive := fun _ => O) 0 (fun j' => L i' j') j) i,
            ?_, ?_, ?_, ?_⟩
    · intro i j
      refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
      · simp
      · simp [Fin.castSucc_lt_last, (Fin.castSucc_lt_last j).ne', not_lt_of_gt (Fin.castSucc_lt_last j)]
      · simp [Fin.castSucc_lt_last, (Fin.castSucc_lt_last i).ne, not_lt_of_gt (Fin.castSucc_lt_last i)]
        first | exact hr i | exact (hr i).mul_right _
      · simpa using hU i j
    · intro i j
      refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
      · simp
      · simp [Fin.castSucc_lt_last, (Fin.castSucc_lt_last j).ne', not_lt_of_gt (Fin.castSucc_lt_last j)]
        first | exact hc j | exact (hc j).mul_left _
      · simp [Fin.castSucc_lt_last, (Fin.castSucc_lt_last i).ne, not_lt_of_gt (Fin.castSucc_lt_last i)]
      · simpa using hL i j
    · ext i j
      rw [udl_apply, Fin.sum_univ_castSucc]
      refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
      · simp [haa]
      · simp [c]
        done
      · simp [r]
        done
      · have e := congrFun (congrFun hUDL i) j
        rw [udl_apply] at e
        simp only [Matrix.of_apply, Fin.lastCases_castSucc, Fin.lastCases_last, mul_zero, add_zero, mul_one]
        rw [← e]
        simp only [G]
        linear_combination (-(r i * ↑a⁻¹ * c j)) * hinv
    · intro i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simp [haa]
      · have e : ((D i : O)) - g i.castSucc i.castSucc = ((D i : O) - G i i) - r i * ↑a⁻¹ * c i := by
          simp [G]; ring
        simpa [e] using dvd_sub (hD i) (hrc i)

theorem main : (let d1 : {O : Type} → [CommRing O] → {n : ℕ} → O → Matrix (Fin n) (Fin n) O → Prop := @(fun {O : Type} [CommRing O] {n : ℕ} (β : O) (l : Matrix (Fin n) (Fin n) O) ↦ ∀ (i j : Fin n), (i < j → l i j = (0 : O)) ∧ (i = j → l i j = (1 : O)) ∧ (j < i → β ∣ l i j)); let d2 : {O : Type} → [CommRing O] → {n : ℕ} → O → O → Matrix (Fin n) (Fin n) O → Prop := @(fun {O : Type} [CommRing O] {n : ℕ} (α β : O) (g : Matrix (Fin n) (Fin n) O) ↦ ∀ (i j : Fin n), (i < j → α ∣ g i j) ∧ (j < i → β ∣ g i j)); let d3 : {O : Type} → [CommRing O] → {n : ℕ} → O → Matrix (Fin n) (Fin n) O → Prop := @(fun {O : Type} [CommRing O] {n : ℕ} (α : O) (u : Matrix (Fin n) (Fin n) O) ↦ ∀ (i j : Fin n), (j < i → u i j = (0 : O)) ∧ (i = j → u i j = (1 : O)) ∧ (i < j → α ∣ u i j)); ∀ {O : Type} [inst : CommRing O] [IsLocalRing O] {α β : O}, ¬IsUnit (α * β) → ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) O), d2 α β g → (∀ (i : Fin n), IsUnit (g i i)) → ∃ (u : Matrix (Fin n) (Fin n) O) (d : Fin n → Oˣ) (l : Matrix (Fin n) (Fin n) O), d3 α u ∧ d1 β l ∧ g = (u * Matrix.diagonal fun (i : Fin n) ↦ (↑(d i) : O)) * l ∧ ∀ (i : Fin n), α * β ∣ (↑(d i) : O) - g i i) := by
  intro d1 d2 d3 O _ _ α β hab n g hg hu
  exact key hab n g hg hu

end GlobalTheory.UnipotentDecomposition
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IwahoriFactorisation
namespace GlobalTheory.UnipotentBorder

open Matrix

variable {O : Type} [CommRing O]

def IsUU {m : ℕ} (U : Matrix (Fin m) (Fin m) O) : Prop :=
  ∀ i j, (j < i → U i j = 0) ∧ (i = j → U i j = 1)

def IsLU {m : ℕ} (L : Matrix (Fin m) (Fin m) O) : Prop :=
  ∀ i j, (i < j → L i j = 0) ∧ (i = j → L i j = 1)

theorem udl_apply {m : ℕ} (U L : Matrix (Fin m) (Fin m) O) (d : Fin m → O) (i j : Fin m) :
    (U * diagonal d * L) i j = ∑ k, U i k * d k * L k j := by
  rw [Matrix.mul_apply]
  simp only [mul_diagonal]

theorem last_row {n : ℕ} {U L : Matrix (Fin (n+1)) (Fin (n+1)) O} (hU : IsUU U)
    (D : Fin (n+1) → Oˣ) (j : Fin (n+1)) :
    (U * diagonal (fun k => (D k : O)) * L) (Fin.last n) j
      = (D (Fin.last n) : O) * L (Fin.last n) j := by
  simp only [udl_apply]
  rw [Finset.sum_eq_single (Fin.last n)]
  · rw [(hU _ _).2 rfl, one_mul]
  · intro k _ hk
    rw [(hU (Fin.last n) k).1 (lt_of_le_of_ne (Fin.le_last k) hk), zero_mul, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem last_col {n : ℕ} {U L : Matrix (Fin (n+1)) (Fin (n+1)) O} (hL : IsLU L)
    (D : Fin (n+1) → Oˣ) (i : Fin (n+1)) :
    (U * diagonal (fun k => (D k : O)) * L) i (Fin.last n)
      = U i (Fin.last n) * (D (Fin.last n) : O) := by
  simp only [udl_apply]
  rw [Finset.sum_eq_single (Fin.last n)]
  · rw [(hL _ _).2 rfl, mul_one]
  · intro k _ hk
    rw [(hL k (Fin.last n)).1 (lt_of_le_of_ne (Fin.le_last k) hk), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem top_block {n : ℕ} (U L : Matrix (Fin (n+1)) (Fin (n+1)) O)
    (D : Fin (n+1) → Oˣ) (i j : Fin n) :
    (U * diagonal (fun k => (D k : O)) * L) i.castSucc j.castSucc =
      (U.submatrix Fin.castSucc Fin.castSucc * diagonal (fun k : Fin n => (D k.castSucc : O)) *
        L.submatrix Fin.castSucc Fin.castSucc) i j
      + U i.castSucc (Fin.last n) * (D (Fin.last n) : O) * L (Fin.last n) j.castSucc := by
  simp only [udl_apply, Fin.sum_univ_castSucc, submatrix_apply]

theorem IsUU.top {n : ℕ} {U : Matrix (Fin (n+1)) (Fin (n+1)) O} (hU : IsUU U) :
    IsUU (U.submatrix Fin.castSucc Fin.castSucc) := fun _ _ ↦
  ⟨fun h ↦ (hU _ _).1 (Fin.castSucc_lt_castSucc_iff.2 h), fun h ↦ (hU _ _).2 (congrArg _ h)⟩

theorem IsLU.top {n : ℕ} {L : Matrix (Fin (n+1)) (Fin (n+1)) O} (hL : IsLU L) :
    IsLU (L.submatrix Fin.castSucc Fin.castSucc) := fun _ _ ↦
  ⟨fun h ↦ (hL _ _).1 (Fin.castSucc_lt_castSucc_iff.2 h), fun h ↦ (hL _ _).2 (congrArg _ h)⟩

theorem udl_unique : ∀ (n : ℕ) (U U' L L' : Matrix (Fin n) (Fin n) O) (D D' : Fin n → Oˣ),
    IsUU U → IsUU U' → IsLU L → IsLU L' →
    U * diagonal (fun i => (D i : O)) * L = U' * diagonal (fun i => (D' i : O)) * L' →
    U = U' ∧ D = D' ∧ L = L' := by
  intro n
  induction n with
  | zero =>
    intro U U' L L' D D' _ _ _ _ _
    exact ⟨Matrix.ext fun i _ ↦ i.elim0, funext fun i ↦ i.elim0, Matrix.ext fun i _ ↦ i.elim0⟩
  | succ n ih =>
    intro U U' L L' D D' hU hU' hL hL' h

    have hrow : ∀ j, (D (Fin.last n) : O) * L (Fin.last n) j = (D' (Fin.last n) : O) * L' (Fin.last n) j :=
      fun j ↦ (last_row hU D (L := L) j).symm.trans
        ((congrFun (congrFun h _) j).trans (last_row hU' D' (L := L') j))
    have hcol : ∀ i, U i (Fin.last n) * (D (Fin.last n) : O) = U' i (Fin.last n) * (D' (Fin.last n) : O) :=
      fun i ↦ (last_col hL D (U := U) i).symm.trans
        ((congrFun (congrFun h i) _).trans (last_col hL' D' (U := U') i))
    have hDl : D (Fin.last n) = D' (Fin.last n) := by
      have e := hrow (Fin.last n)
      rw [(hL _ _).2 rfl, (hL' _ _).2 rfl, mul_one, mul_one] at e
      exact Units.ext e
    have hLl : ∀ j, L (Fin.last n) j = L' (Fin.last n) j := fun j ↦ by
      have e := hrow j
      rw [hDl] at e
      exact (Units.mul_right_inj (D' (Fin.last n))).1 e
    have hUl : ∀ i, U i (Fin.last n) = U' i (Fin.last n) := fun i ↦ by
      have e := hcol i
      rw [hDl] at e
      exact (Units.mul_left_inj (D' (Fin.last n))).1 e

    have htop : U.submatrix Fin.castSucc Fin.castSucc * diagonal (fun k : Fin n ↦ ((D ∘ Fin.castSucc) k : O)) *
        L.submatrix Fin.castSucc Fin.castSucc =
        U'.submatrix Fin.castSucc Fin.castSucc * diagonal (fun k : Fin n ↦ ((D' ∘ Fin.castSucc) k : O)) *
        L'.submatrix Fin.castSucc Fin.castSucc := by
      ext i j
      have e1 := top_block U L D i j
      have e2 := top_block U' L' D' i j
      rw [h, e2, hUl, hDl, hLl] at e1
      exact (add_right_cancel e1).symm
    obtain ⟨hU0, hD0, hL0⟩ := ih _ _ _ _ (D ∘ Fin.castSucc) (D' ∘ Fin.castSucc)
      hU.top hU'.top hL.top hL'.top htop
    refine ⟨?_, ?_, ?_⟩
    · ext i j
      rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
      · rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
        · exact congrFun (congrFun hU0 i) j
        · exact hUl _
      · rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
        · rw [(hU _ _).1 (Fin.castSucc_lt_last j), (hU' _ _).1 (Fin.castSucc_lt_last j)]
        · rw [(hU _ _).2 rfl, (hU' _ _).2 rfl]
    · funext k
      rcases Fin.eq_castSucc_or_eq_last k with ⟨k, rfl⟩ | rfl
      · exact congrFun hD0 k
      · exact hDl
    · ext i j
      rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
      · rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
        · exact congrFun (congrFun hL0 i) j
        · rw [(hL _ _).1 (Fin.castSucc_lt_last i), (hL' _ _).1 (Fin.castSucc_lt_last i)]
      · exact hLl j

def border {n : ℕ} (A : Matrix (Fin n) (Fin n) O) (col row : Fin n → O) (x : O) :
    Matrix (Fin (n+1)) (Fin (n+1)) O := fun i j =>
  Fin.lastCases (motive := fun _ => O) (Fin.lastCases (motive := fun _ => O) x row j)
    (fun i' => Fin.lastCases (motive := fun _ => O) (col i') (A i') j) i

section
variable {n : ℕ} (A : Matrix (Fin n) (Fin n) O) (col row : Fin n → O) (x : O)
omit [CommRing O]

theorem border_ll : border A col row x (Fin.last n) (Fin.last n) = x := by simp [border]
theorem border_lc (j : Fin n) : border A col row x (Fin.last n) j.castSucc = row j := by simp [border]
theorem border_cl (i : Fin n) : border A col row x i.castSucc (Fin.last n) = col i := by simp [border]
theorem border_cc (i j : Fin n) : border A col row x i.castSucc j.castSucc = A i j := by simp [border]
theorem border_top : (border A col row x).submatrix Fin.castSucc Fin.castSucc = A :=
  Matrix.ext fun i j ↦ border_cc A col row x i j
end

theorem unit_sub [IsLocalRing O] {β : O} (hβ : ¬IsUnit β) {a y : O} (ha : IsUnit a)
    (hy : β ∣ y) (z : O) : IsUnit (a - z * y) := by
  have hm : z * y ∈ IsLocalRing.maximalIdeal O := by
    obtain ⟨t, rfl⟩ := hy
    exact Ideal.mul_mem_left _ z
      (Ideal.mul_mem_right _ _ ((IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 hβ)))
  by_contra h
  have h2 : a - z * y ∈ IsLocalRing.maximalIdeal O :=
    (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 h)
  have h3 : a ∈ IsLocalRing.maximalIdeal O := by simpa using Ideal.add_mem _ h2 hm
  exact mem_nonunits_iff.1 ((IsLocalRing.mem_maximalIdeal _).1 h3) ha

theorem diag_unit [IsLocalRing O] {β : O} (hβ : ¬IsUnit β) {n : ℕ}
    (g : Matrix (Fin n) (Fin n) O) (hg : IsUnit g.det) (hlow : ∀ i j, j < i → β ∣ g i j)
    (i : Fin n) : IsUnit (g i i) := by

  have hres : ∀ x : O, IsLocalRing.residue O x = 0 ↔ ¬IsUnit x := fun x ↦ by
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have htri : (g.map (IsLocalRing.residue O)).BlockTriangular id := by
    intro a b hab
    simp only [map_apply]
    obtain ⟨t, ht⟩ := hlow a b hab
    rw [hres, ht]
    exact fun hu ↦ hβ (isUnit_of_mul_isUnit_left hu)
  have hmap : IsLocalRing.residue O g.det = (g.map (IsLocalRing.residue O)).det :=
    RingHom.map_det _ _
  have hdet : (g.map (IsLocalRing.residue O)).det ≠ 0 := by
    rw [← hmap]
    exact (hg.map _).ne_zero
  rw [det_of_upperTriangular htri, Finset.prod_ne_zero_iff] at hdet
  have hi := hdet i (Finset.mem_univ _)
  simp only [map_apply] at hi
  by_contra hu
  exact hi ((hres _).2 hu)

theorem udl_exists [IsLocalRing O] {α β : O} (hβ : ¬IsUnit β) :
    ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) O),
    (∀ i j, (i < j → α ∣ g i j) ∧ (j < i → β ∣ g i j)) → (∀ i, IsUnit (g i i)) →
    ∃ (U : Matrix (Fin n) (Fin n) O) (D : Fin n → Oˣ) (L : Matrix (Fin n) (Fin n) O),
      (∀ i j, (j < i → U i j = 0) ∧ (i = j → U i j = 1) ∧ (i < j → α ∣ U i j)) ∧
      (∀ i j, (i < j → L i j = 0) ∧ (i = j → L i j = 1) ∧ (j < i → β ∣ L i j)) ∧
      g = U * diagonal (fun i => (D i : O)) * L := by
  intro n
  induction n with
  | zero =>
    intro g _ _
    exact ⟨0, fun i ↦ i.elim0, 0, fun i ↦ i.elim0, fun i ↦ i.elim0, Matrix.ext fun i _ ↦ i.elim0⟩
  | succ n ih =>
    intro g hg hd
    obtain ⟨u, hu⟩ := hd (Fin.last n)
    have hui : (↑u⁻¹ : O) * ↑u = 1 := Units.inv_mul u

    let g' : Matrix (Fin n) (Fin n) O := fun i j ↦
      g i.castSucc j.castSucc - (g i.castSucc (Fin.last n) * ↑u⁻¹) * g (Fin.last n) j.castSucc
    have hg' : ∀ i j, (i < j → α ∣ g' i j) ∧ (j < i → β ∣ g' i j) := by
      intro i j
      refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
      · exact dvd_sub ((hg _ _).1 (Fin.castSucc_lt_castSucc_iff.2 h))
          (Dvd.dvd.mul_right (Dvd.dvd.mul_right ((hg _ _).1 (Fin.castSucc_lt_last i)) _) _)
      · exact dvd_sub ((hg _ _).2 (Fin.castSucc_lt_castSucc_iff.2 h))
          (Dvd.dvd.mul_left ((hg _ _).2 (Fin.castSucc_lt_last j)) _)
    have hd' : ∀ i, IsUnit (g' i i) := fun i ↦
      unit_sub hβ (hd i.castSucc) ((hg _ _).2 (Fin.castSucc_lt_last i)) _
    obtain ⟨U0, D0, L0, hU0, hL0, hg0⟩ := ih g' hg' hd'
    let U := border U0 (fun i ↦ g i.castSucc (Fin.last n) * ↑u⁻¹) 0 1
    let L := border L0 0 (fun j ↦ ↑u⁻¹ * g (Fin.last n) j.castSucc) 1
    let D : Fin (n + 1) → Oˣ := Fin.lastCases u D0
    have hU : ∀ i j, (j < i → U i j = 0) ∧ (i = j → U i j = 1) ∧ (i < j → α ∣ U i j) := by
      intro i j
      rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
      · rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
        · simp only [U, border_cc, Fin.castSucc_lt_castSucc_iff, Fin.castSucc_inj]
          exact hU0 i j
        · simp only [U, border_cl]
          exact ⟨fun h ↦ absurd h (not_lt.2 (Fin.castSucc_lt_last i).le),
            fun h ↦ absurd h (Fin.castSucc_lt_last i).ne,
            fun _ ↦ Dvd.dvd.mul_right ((hg _ _).1 (Fin.castSucc_lt_last i)) _⟩
      · rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
        · simp only [U, border_lc, Pi.zero_apply]
          exact ⟨fun _ ↦ trivial, fun h ↦ absurd h (Fin.castSucc_lt_last j).ne',
            fun h ↦ absurd h (not_lt.2 (Fin.castSucc_lt_last j).le)⟩
        · simp [U, border_ll]
    have hL : ∀ i j, (i < j → L i j = 0) ∧ (i = j → L i j = 1) ∧ (j < i → β ∣ L i j) := by
      intro i j
      rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
      · rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
        · simp only [L, border_cc, Fin.castSucc_lt_castSucc_iff, Fin.castSucc_inj]
          exact hL0 i j
        · simp only [L, border_cl, Pi.zero_apply]
          exact ⟨fun _ ↦ trivial, fun h ↦ absurd h (Fin.castSucc_lt_last i).ne,
            fun h ↦ absurd h (not_lt.2 (Fin.castSucc_lt_last i).le)⟩
      · rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
        · simp only [L, border_lc]
          exact ⟨fun h ↦ absurd h (not_lt.2 (Fin.castSucc_lt_last j).le),
            fun h ↦ absurd h (Fin.castSucc_lt_last j).ne',
            fun _ ↦ Dvd.dvd.mul_left ((hg _ _).2 (Fin.castSucc_lt_last j)) _⟩
        · simp [L, border_ll]
    have hUU : IsUU U := fun i j ↦ ⟨(hU i j).1, (hU i j).2.1⟩
    have hLU : IsLU L := fun i j ↦ ⟨(hL i j).1, (hL i j).2.1⟩
    refine ⟨U, D, L, hU, hL, ?_⟩
    ext i j
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
    · rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
      · rw [top_block]
        simp only [U, L, D, border_top, Fin.lastCases_castSucc, Fin.lastCases_last, border_cl, border_lc]
        rw [← hg0]
        simp only [g']
        linear_combination (-(g i.castSucc (Fin.last n) * ↑u⁻¹ * g (Fin.last n) j.castSucc)) * hui
      · rw [last_col hLU]
        simp only [U, D, border_cl, Fin.lastCases_last]
        linear_combination (-(g i.castSucc (Fin.last n))) * hui
    · rw [last_row hUU]
      rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
      · simp only [L, D, border_lc, Fin.lastCases_last]
        rw [← mul_assoc, Units.mul_inv, one_mul]
      · simp only [L, D, border_ll, Fin.lastCases_last, mul_one]
        exact hu.symm

theorem iwahori_factorisation : (let d1 : {O : Type} → [CommRing O] → {n : ℕ} → O → Matrix (Fin n) (Fin n) O → Prop := @(fun {O : Type} [CommRing O] {n : ℕ} (β : O) (l : Matrix (Fin n) (Fin n) O) ↦ ∀ (i j : Fin n), (i < j → l i j = (0 : O)) ∧ (i = j → l i j = (1 : O)) ∧ (j < i → β ∣ l i j)); let d2 : {O : Type} → [CommRing O] → {n : ℕ} → O → O → Matrix (Fin n) (Fin n) O → Prop := @(fun {O : Type} [CommRing O] {n : ℕ} (α β : O) (g : Matrix (Fin n) (Fin n) O) ↦ ∀ (i j : Fin n), (i < j → α ∣ g i j) ∧ (j < i → β ∣ g i j)); let d3 : {O : Type} → [CommRing O] → {n : ℕ} → O → Matrix (Fin n) (Fin n) O → Prop := @(fun {O : Type} [CommRing O] {n : ℕ} (α : O) (u : Matrix (Fin n) (Fin n) O) ↦ ∀ (i j : Fin n), (j < i → u i j = (0 : O)) ∧ (i = j → u i j = (1 : O)) ∧ (i < j → α ∣ u i j)); ∀ {O : Type} [inst : CommRing O] {n : ℕ} [IsLocalRing O] {α β : O}, ¬IsUnit β → ∀ (g : GL (Fin n) O), d2 α β (↑g : Matrix (Fin n) (Fin n) O) → ∃! p : Matrix (Fin n) (Fin n) O × (Fin n → Oˣ) × Matrix (Fin n) (Fin n) O, d3 α (Prod.fst p) ∧ d1 β (Prod.snd (Prod.snd p)) ∧ (↑g : Matrix (Fin n) (Fin n) O) = (Prod.fst p * Matrix.diagonal fun (i : Fin n) ↦ (↑(Prod.fst (Prod.snd p) i) : O)) * Prod.snd (Prod.snd p)) := by
  dsimp only
  intro O _ n _ α β hβ g hg
  obtain ⟨U, D, L, hU, hL, hgeq⟩ := udl_exists hβ n (↑g : Matrix (Fin n) (Fin n) O) hg
    (fun i ↦ diag_unit hβ (↑g : Matrix (Fin n) (Fin n) O) (Matrix.isUnits_det_units g)
      (fun i j h ↦ (hg i j).2 h) i)
  refine ⟨(U, D, L), ⟨hU, hL, hgeq⟩, ?_⟩
  rintro ⟨U', D', L'⟩ ⟨hU', hL', hg'⟩
  obtain ⟨h1, h2, h3⟩ := udl_unique n U' U L' L D' D
    (fun i j ↦ ⟨(hU' i j).1, (hU' i j).2.1⟩) (fun i j ↦ ⟨(hU i j).1, (hU i j).2.1⟩)
    (fun i j ↦ ⟨(hL' i j).1, (hL' i j).2.1⟩) (fun i j ↦ ⟨(hL i j).1, (hL i j).2.1⟩)
    (hg'.symm.trans hgeq)
  rw [h1, h2, h3]

end GlobalTheory.UnipotentBorder
end

open Polynomial

namespace GlobalTheory.IwahoriFactor

section General

variable {O : Type} [CommRing O] {n : ℕ}

def Shape (α β : O) (g : Matrix (Fin n) (Fin n) O) : Prop :=
  ∀ i j, (i < j → α ∣ g i j) ∧ (j < i → β ∣ g i j)

def UpperUnip (α : O) (u : Matrix (Fin n) (Fin n) O) : Prop :=
  ∀ i j, (j < i → u i j = 0) ∧ (i = j → u i j = 1) ∧ (i < j → α ∣ u i j)

def LowerUnip (β : O) (l : Matrix (Fin n) (Fin n) O) : Prop :=
  ∀ i j, (i < j → l i j = 0) ∧ (i = j → l i j = 1) ∧ (j < i → β ∣ l i j)

theorem Shape.mul {α β : O} {x y : Matrix (Fin n) (Fin n) O} (hx : Shape α β x)
    (hy : Shape α β y) : Shape α β (x * y) := by
  intro i j
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.dvd_sum fun k _ => ?_
    rcases lt_or_ge i k with hk | hk
    · exact ((hx i k).1 hk).mul_right _
    · exact ((hy k j).1 (hk.trans_lt h)).mul_left _
  · rw [Matrix.mul_apply]
    refine Finset.dvd_sum fun k _ => ?_
    rcases lt_or_ge k i with hk | hk
    · exact ((hx i k).2 hk).mul_right _
    · exact ((hy k j).2 (h.trans_le hk)).mul_left _

theorem dvd_inv_of_blockTriangular {ι : Type} [LinearOrder ι] (b : Fin n → ι) (γ : O)
    (g : GL (Fin n) O) (hg : ∀ i j, b j < b i → γ ∣ (g : Matrix (Fin n) (Fin n) O) i j) :
    ∀ i j, b j < b i → γ ∣ ((g⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) i j := by
  let f := Ideal.Quotient.mk (Ideal.span {γ})
  have hf : ∀ x, f x = 0 ↔ γ ∣ x := fun x => by
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  have h1 : ((g : Matrix (Fin n) (Fin n) O).map f) *
      (((g⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O).map f) = 1 := by
    rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.map_one _ (map_zero f) (map_one f)]
  letI := invertibleOfRightInverse _ _ h1
  have h2 : ((g : Matrix (Fin n) (Fin n) O).map f).BlockTriangular b :=
    fun i j h => (hf _).2 (hg i j h)
  have h3 := Matrix.blockTriangular_inv_of_blockTriangular h2
  rw [Matrix.inv_eq_right_inv h1] at h3
  intro i j h
  exact (hf _).1 (h3 h)

theorem Shape.inv {α β : O} {g : GL (Fin n) O} (hg : Shape α β (g : Matrix (Fin n) (Fin n) O)) :
    Shape α β ((g⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) := by
  intro i j
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact dvd_inv_of_blockTriangular (ι := (Fin n)ᵒᵈ) OrderDual.toDual α g
      (fun i j h => (hg i j).1 h) i j h
  · exact dvd_inv_of_blockTriangular id β g (fun i j h => (hg i j).2 h) i j h

theorem UpperUnip.shape {α : O} (β : O) {u : Matrix (Fin n) (Fin n) O} (hu : UpperUnip α u) :
    Shape α β u := fun i j =>
  ⟨(hu i j).2.2, fun h => by rw [(hu i j).1 h]; exact dvd_zero _⟩

theorem LowerUnip.shape (α : O) {β : O} {l : Matrix (Fin n) (Fin n) O} (hl : LowerUnip β l) :
    Shape α β l := fun i j =>
  ⟨fun h => by rw [(hl i j).1 h]; exact dvd_zero _, (hl i j).2.2⟩

theorem Shape.diagonal (α β : O) (d : Fin n → O) : Shape α β (Matrix.diagonal d) := fun i j =>
  ⟨fun h => by rw [Matrix.diagonal_apply_ne _ h.ne]; exact dvd_zero _,
    fun h => by rw [Matrix.diagonal_apply_ne _ h.ne']; exact dvd_zero _⟩

theorem UpperUnip.det {α : O} {u : Matrix (Fin n) (Fin n) O} (hu : UpperUnip α u) :
    u.det = 1 := by
  rw [Matrix.det_of_upperTriangular (fun i j h => (hu i j).1 h)]
  exact Finset.prod_eq_one fun i _ => (hu i i).2.1 rfl

theorem LowerUnip.det {β : O} {l : Matrix (Fin n) (Fin n) O} (hl : LowerUnip β l) :
    l.det = 1 := by
  rw [Matrix.det_of_lowerTriangular l (fun i j h => (hl i j).1 h)]
  exact Finset.prod_eq_one fun i _ => (hl i i).2.1 rfl

theorem factor_unique {α β α' β' : O} {u u' l l' : Matrix (Fin n) (Fin n) O} {d d' : Fin n → Oˣ}
    (hu : UpperUnip α u) (hu' : UpperUnip α' u') (hl : LowerUnip β l) (hl' : LowerUnip β' l')
    (h : u * Matrix.diagonal (fun i => (d i : O)) * l =
      u' * Matrix.diagonal (fun i => (d' i : O)) * l') :
    u = u' ∧ d = d' ∧ l = l' := by
  have iu' : IsUnit u'.det := by rw [hu'.det]; exact isUnit_one
  have il : IsUnit l.det := by rw [hl.det]; exact isUnit_one
  letI := u'.invertibleOfIsUnitDet iu'
  letI := l.invertibleOfIsUnitDet il
  have tu : u.BlockTriangular id := fun i j h => (hu i j).1 h
  have tu' : u'.BlockTriangular id := fun i j h => (hu' i j).1 h
  have tl : l.BlockTriangular OrderDual.toDual := fun i j h => (hl i j).1 h
  have tl' : l'.BlockTriangular OrderDual.toDual := fun i j h => (hl' i j).1 h
  set X := u'⁻¹ * (u * Matrix.diagonal (fun i => (d i : O))) with hX
  have e1 : u' * X = u * Matrix.diagonal (fun i => (d i : O)) := by
    rw [hX, Matrix.mul_nonsing_inv_cancel_left _ _ iu']
  have e2 : X * l = Matrix.diagonal (fun i => (d' i : O)) * l' := by
    rw [hX, Matrix.mul_assoc, h, Matrix.mul_assoc u', Matrix.nonsing_inv_mul_cancel_left _ _ iu']
  have e3 : X = Matrix.diagonal (fun i => (d' i : O)) * l' * l⁻¹ := by
    rw [← e2, Matrix.mul_nonsing_inv_cancel_right _ _ il]
  have tX : X.BlockTriangular id :=
    (Matrix.blockTriangular_inv_of_blockTriangular tu').mul
      (tu.mul (Matrix.blockTriangular_diagonal _))
  have tX' : X.BlockTriangular OrderDual.toDual := by
    rw [e3]
    exact ((Matrix.blockTriangular_diagonal _).mul tl').mul
      (Matrix.blockTriangular_inv_of_blockTriangular tl)
  have hd : X = Matrix.diagonal (fun i => X i i) := by
    ext i j
    rcases lt_trichotomy i j with h | rfl | h
    · rw [Matrix.diagonal_apply_ne _ h.ne]; exact tX' h
    · rw [Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ h.ne']; exact tX h
  rw [hd] at e1 e2
  have f1 : ∀ i j, u' i j * X j j = u i j * d j := fun i j => by
    simpa [Matrix.mul_diagonal] using congrFun (congrFun e1 i) j
  have f2 : ∀ i j, X i i * l i j = d' i * l' i j := fun i j => by
    simpa [Matrix.diagonal_mul] using congrFun (congrFun e2 i) j
  have g1 : ∀ i, X i i = d i := fun i => by
    simpa [(hu i i).2.1 rfl, (hu' i i).2.1 rfl] using f1 i i
  have g2 : ∀ i, X i i = d' i := fun i => by
    simpa [(hl i i).2.1 rfl, (hl' i i).2.1 rfl] using f2 i i
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    have := f1 i j
    rw [g1] at this
    exact ((Units.mul_left_inj _).1 this).symm
  · funext i
    exact Units.ext ((g1 i).symm.trans (g2 i))
  · ext i j
    have := f2 i j
    rw [g2] at this
    exact (Units.mul_right_inj _).1 this

theorem exists_factor [IsLocalRing O] {α β : O} (hαβ : ¬ IsUnit (α * β)) :
    ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) O), Shape α β g → (∀ i, IsUnit (g i i)) →
      ∃ (u : Matrix (Fin n) (Fin n) O) (d : Fin n → Oˣ) (l : Matrix (Fin n) (Fin n) O),
        UpperUnip α u ∧ LowerUnip β l ∧ g = u * Matrix.diagonal (fun i => (d i : O)) * l ∧
          ∀ i, α * β ∣ (d i : O) - g i i := by
  apply _root_.GlobalTheory.UnipotentDecomposition.main <;> assumption

theorem isUnit_diag [IsLocalRing O] {α β : O} (hβ : ¬ IsUnit β) {g : Matrix (Fin n) (Fin n) O}
    (hdet : IsUnit g.det) (hg : Shape α β g) (i : Fin n) : IsUnit (g i i) := by
  let f := IsLocalRing.residue O
  have h0 : ∀ x, f x = 0 ↔ ¬ IsUnit x := fun x => by
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have h1 : (g.map f).BlockTriangular id := fun i j h =>
    (h0 _).2 fun hu => hβ (isUnit_of_dvd_unit ((hg i j).2 h) hu)
  have h2 : f g.det = ∏ k, f (g k k) := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.det_of_upperTriangular h1]
    rfl
  by_contra hi
  have h3 : f g.det = 0 := by
    rw [h2]; exact Finset.prod_eq_zero (Finset.mem_univ i) ((h0 _).2 hi)
  exact (h0 _).1 h3 hdet

def flip (g : Matrix (Fin n) (Fin n) O) : Matrix (Fin n) (Fin n) O :=
  g.submatrix Fin.revPerm Fin.revPerm

theorem flip_apply (g : Matrix (Fin n) (Fin n) O) (i j : Fin n) :
    flip g i j = g i.rev j.rev := rfl

theorem flip_flip (g : Matrix (Fin n) (Fin n) O) : flip (flip g) = g := by
  ext i j; simp [flip_apply]

theorem flip_triple (u l : Matrix (Fin n) (Fin n) O) (d : Fin n → O) :
    flip (u * Matrix.diagonal d * l) =
      flip u * Matrix.diagonal (fun i => d i.rev) * flip l := by
  unfold flip
  rw [← Matrix.submatrix_mul_equiv _ _ _ Fin.revPerm, ← Matrix.submatrix_mul_equiv _ _ _ Fin.revPerm,
    Matrix.submatrix_diagonal_equiv]
  rfl

theorem Shape.flip {α β : O} {g : Matrix (Fin n) (Fin n) O} (hg : Shape α β g) :
    Shape β α (flip g) := fun i j =>
  ⟨fun h => (hg _ _).2 (Fin.rev_lt_rev.2 h), fun h => (hg _ _).1 (Fin.rev_lt_rev.2 h)⟩

theorem UpperUnip.flip {α : O} {u : Matrix (Fin n) (Fin n) O} (hu : UpperUnip α u) :
    LowerUnip α (flip u) := fun i j =>
  ⟨fun h => (hu _ _).1 (Fin.rev_lt_rev.2 h), fun h => (hu _ _).2.1 (congrArg Fin.rev h),
    fun h => (hu _ _).2.2 (Fin.rev_lt_rev.2 h)⟩

theorem LowerUnip.flip {β : O} {l : Matrix (Fin n) (Fin n) O} (hl : LowerUnip β l) :
    UpperUnip β (flip l) := fun i j =>
  ⟨fun h => (hl _ _).1 (Fin.rev_lt_rev.2 h), fun h => (hl _ _).2.1 (congrArg Fin.rev h),
    fun h => (hl _ _).2.2 (Fin.rev_lt_rev.2 h)⟩

theorem not_isUnit_mul {α β : O} (hβ : ¬ IsUnit β) : ¬ IsUnit (α * β) :=
  fun h => hβ (isUnit_of_mul_isUnit_right h)

theorem existsUnique_factor [IsLocalRing O] {α β : O} (hβ : ¬ IsUnit β) (g : GL (Fin n) O)
    (hg : Shape α β (g : Matrix (Fin n) (Fin n) O)) :
    ∃! p : Matrix (Fin n) (Fin n) O × (Fin n → Oˣ) × Matrix (Fin n) (Fin n) O,
      UpperUnip α p.1 ∧ LowerUnip β p.2.2 ∧
        (g : Matrix (Fin n) (Fin n) O) = p.1 * Matrix.diagonal (fun i => (p.2.1 i : O)) * p.2.2 := by
  apply _root_.GlobalTheory.UnipotentBorder.iwahori_factorisation <;> assumption

theorem existsUnique_factor_opp [IsLocalRing O] {α β : O} (hβ : ¬ IsUnit β) (g : GL (Fin n) O)
    (hg : Shape α β (g : Matrix (Fin n) (Fin n) O)) :
    ∃! p : Matrix (Fin n) (Fin n) O × (Fin n → Oˣ) × Matrix (Fin n) (Fin n) O,
      LowerUnip β p.1 ∧ UpperUnip α p.2.2 ∧
        (g : Matrix (Fin n) (Fin n) O) = p.1 * Matrix.diagonal (fun i => (p.2.1 i : O)) * p.2.2 := by
  obtain ⟨u, d, l, hu, hl, hfac, -⟩ :=
    exists_factor (α := β) (β := α) (by rw [mul_comm]; exact not_isUnit_mul hβ) n _ hg.flip
      (fun i => isUnit_diag hβ (Matrix.isUnits_det_units g) hg i.rev)
  have hfac2 := congrArg flip hfac
  rw [flip_flip, flip_triple] at hfac2
  refine ⟨(flip u, fun i => d i.rev, flip l), ⟨hu.flip, hl.flip, hfac2⟩, ?_⟩
  rintro ⟨l', d', u'⟩ ⟨hl', hu', hfac'⟩
  have hfac3 := congrArg flip hfac'
  rw [flip_triple] at hfac3
  obtain ⟨h1, h2, h3⟩ := factor_unique (d' := fun i => d' i.rev) hu hl'.flip hl hu'.flip
    (hfac.symm.trans hfac3)
  subst h1 h2 h3
  simp [flip_flip]

end General

end GlobalTheory.IwahoriFactor
