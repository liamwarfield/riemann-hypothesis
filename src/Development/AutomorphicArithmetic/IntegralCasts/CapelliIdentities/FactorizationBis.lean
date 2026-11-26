module

public import Mathlib

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FactorizationBis
theorem UpperTheory.Reformulated.B.TriangularFactorizationNearIdentity.factor :
    ∀ {L : Type} [inst : NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (r : ℝ),
      (0 : ℝ) ≤ r →
        r < (1 : ℝ) →
          ∀ (A : Matrix (Fin n) (Fin n) L),
            (∀ (i j : Fin n), ‖(A - (1 : Matrix (Fin n) (Fin n) L)) i j‖ ≤ r) →
              ∃ (U : Matrix (Fin n) (Fin n) L) (W : Matrix (Fin n) (Fin n) L),
                (∀ (i j : Fin n), j < i → U i j = (0 : L)) ∧
                  (∀ (i j : Fin n), i < j → W i j = (0 : L)) ∧
                    (∀ (i j : Fin n), ‖(U - (1 : Matrix (Fin n) (Fin n) L)) i j‖ ≤ r) ∧
                      (∀ (i j : Fin n), ‖(W - (1 : Matrix (Fin n) (Fin n) L)) i j‖ ≤ r) ∧ A = U * W := by
  intro L _ _ n r h0 h1
  induction n with
  | zero =>
    intro A _
    exact ⟨1, 1, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
      Subsingleton.elim _ _⟩
  | succ n ih =>
    intro A hA
    have hlc : ∀ i : Fin n, Fin.last n ≠ i.castSucc := fun i => (Fin.castSucc_lt_last i).ne'
    have hcl : ∀ i : Fin n, i.castSucc ≠ Fin.last n := fun i => (Fin.castSucc_lt_last i).ne
    have hd1 : ‖A (Fin.last n) (Fin.last n) - 1‖ ≤ r := by
      simpa using hA (Fin.last n) (Fin.last n)
    have hd : ‖A (Fin.last n) (Fin.last n)‖ = 1 := by
      have hne : ‖A (Fin.last n) (Fin.last n) - 1‖ ≠ ‖(1 : L)‖ := by
        rw [norm_one]; exact (hd1.trans_lt h1).ne
      have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne
      rw [sub_add_cancel, norm_one] at this
      rw [this]
      exact max_eq_right (hd1.trans h1.le)
    have hd0 : A (Fin.last n) (Fin.last n) ≠ 0 := by
      intro h; rw [h, norm_zero] at hd; exact zero_ne_one hd
    have hb : ∀ i : Fin n, ‖A i.castSucc (Fin.last n)‖ ≤ r := fun i => by
      simpa [Matrix.one_apply_ne (hcl i)] using hA i.castSucc (Fin.last n)
    have hc : ∀ i : Fin n, ‖A (Fin.last n) i.castSucc‖ ≤ r := fun i => by
      simpa [Matrix.one_apply_ne (hlc i)] using hA (Fin.last n) i.castSucc
    have hu : ∀ i : Fin n, ‖A i.castSucc (Fin.last n) / A (Fin.last n) (Fin.last n)‖ ≤ r :=
      fun i => by rw [norm_div, hd, div_one]; exact hb i
    have hone : ∀ i j : Fin n, (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) L) i.castSucc j.castSucc
        = (1 : Matrix (Fin n) (Fin n) L) i j := fun i j => by
      simp [Matrix.one_apply]
    obtain ⟨U, W, hU, hW, hU1, hW1, hUW⟩ := ih
      (Matrix.of fun i j : Fin n => A i.castSucc j.castSucc -
        A i.castSucc (Fin.last n) / A (Fin.last n) (Fin.last n) * A (Fin.last n) j.castSucc)
      (fun i j => by
        have h2 := hA i.castSucc j.castSucc
        rw [Matrix.sub_apply, hone] at h2
        rw [Matrix.sub_apply, Matrix.of_apply, sub_right_comm, sub_eq_add_neg]
        refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h2 ?_)
        rw [norm_neg, norm_mul]
        calc _ ≤ r * 1 := mul_le_mul (hu i) ((hc j).trans h1.le) (norm_nonneg _) h0
          _ = r := mul_one r)
    refine ⟨Matrix.of fun i j => Fin.lastCases (motive := fun _ => L)
        (Fin.lastCases (motive := fun _ => L) 1 (fun _ => 0) j)
        (fun i' => Fin.lastCases (motive := fun _ => L)
          (A i'.castSucc (Fin.last n) / A (Fin.last n) (Fin.last n)) (fun j' => U i' j') j) i,
      Matrix.of fun i j => Fin.lastCases (motive := fun _ => L)
        (A (Fin.last n) j)
        (fun i' => Fin.lastCases (motive := fun _ => L) 0 (fun j' => W i' j') j) i,
      ?_, ?_, ?_, ?_, ?_⟩
    · intro i j hij
      induction i using Fin.lastCases <;> induction j using Fin.lastCases
      · exact absurd hij (lt_irrefl _)
      · simp
      · exact absurd hij (Fin.le_last _).not_gt
      · simpa using hU _ _ (by simpa using hij)
    · intro i j hij
      induction i using Fin.lastCases <;> induction j using Fin.lastCases
      · exact absurd hij (lt_irrefl _)
      · exact absurd hij (Fin.le_last _).not_gt
      · simp
      · simpa using hW _ _ (by simpa using hij)
    · intro i j
      induction i using Fin.lastCases <;> induction j using Fin.lastCases
      · simpa using h0
      · simpa [Matrix.one_apply_ne (hlc _)] using h0
      · simpa [Matrix.one_apply_ne (hcl _), hd] using hb _
      · rw [Matrix.sub_apply, hone]
        simpa using hU1 _ _
    · intro i j
      induction i using Fin.lastCases <;> induction j using Fin.lastCases
      · simpa using hd1
      · simpa [Matrix.one_apply_ne (hlc _)] using hc _
      · simpa [Matrix.one_apply_ne (hcl _)] using h0
      · rw [Matrix.sub_apply, hone]
        simpa using hW1 _ _
    · ext i j
      rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
      induction i using Fin.lastCases <;> induction j using Fin.lastCases
      · simp
      · simp
      · simp [hd0]
      · rename_i i j
        have := congrFun (congrFun hUW i) j
        rw [Matrix.of_apply, Matrix.mul_apply] at this
        simp only [Matrix.of_apply, Fin.lastCases_castSucc, Fin.lastCases_last]
        rw [← this, sub_add_cancel]
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.RepsProd
open scoped Classical

noncomputable def UpperTheory.Reformulated.B.P9.IsReps.{u_1} :
    {V : Type u_1} → [inst : AddCommGroup V] → AddSubgroup V → AddSubgroup V → Finset V → Prop :=
    fun {V : Type u_1} [AddCommGroup V] (Λ₁ Λ₂ : AddSubgroup V) (S : Finset V) ↦
      (∀ x ∈ S, x ∈ Λ₂) ∧ (∀ x ∈ S, ∀ y ∈ S, x - y ∈ Λ₁ → x = y) ∧ ∀ y ∈ Λ₂, ∃ x ∈ S, y - x ∈ Λ₁

theorem UpperTheory.Reformulated.B.P9.aux2 :
    ∀ {V : Type} [inst : AddCommGroup V] (p : V →+ V) (Λ : AddSubgroup V) {a b : V},
      a ∈ {x : V | x ∈ Λ ∧ (p : V → V) x = x} →
        b ∈ {x : V | x ∈ Λ ∧ (p : V → V) x = x} → a + b ∈ Λ ∧ (p : V → V) (a + b) = a + b := by
  intro V _ p Λ a b ha hb
  exact ⟨Λ.add_mem ha.1 hb.1, by rw [map_add (f := _), ha.2, hb.2]⟩

theorem UpperTheory.Reformulated.B.P9.aux3 :
    ∀ {V : Type} [inst : AddCommGroup V] (p : V →+ V) (Λ : AddSubgroup V), (0 : V) ∈ Λ ∧ (p : V → V) (0 : V) = (0 : V) := by
  intro V _ p Λ
  exact ⟨Λ.zero_mem, map_zero p⟩

theorem UpperTheory.Reformulated.B.P9.aux4 :
    ∀ {V : Type} [inst : AddCommGroup V] (p : V →+ V) (Λ : AddSubgroup V) {a : V},
      a ∈ {x : V | x ∈ Λ ∧ (p : V → V) x = x} → -a ∈ Λ ∧ (p : V → V) (-a) = -a := by
  intro V _ p Λ a ha
  exact ⟨Λ.neg_mem ha.1, by rw [map_neg, ha.2]⟩

noncomputable def UpperTheory.Reformulated.B.P9.partP :
    {V : Type} → [inst : AddCommGroup V] → (V →+ V) → AddSubgroup V → AddSubgroup V :=
    fun {V : Type} [inst : AddCommGroup V] (p : V →+ V) (Λ : AddSubgroup V) ↦
      { carrier := {x : V | x ∈ Λ ∧ (p : V → V) x = x}, add_mem' := @UpperTheory.Reformulated.B.P9.aux2 V inst p Λ,
        zero_mem' := UpperTheory.Reformulated.B.P9.aux3 p Λ, neg_mem' := @UpperTheory.Reformulated.B.P9.aux4 V inst p Λ : AddSubgroup V }

theorem UpperTheory.Reformulated.B.P9.aux6 :
    ∀ {V : Type} [inst : AddCommGroup V] (p : V →+ V) (Λ : AddSubgroup V) {a b : V},
      a ∈ {x : V | x ∈ Λ ∧ (p : V → V) x = (0 : V)} →
        b ∈ {x : V | x ∈ Λ ∧ (p : V → V) x = (0 : V)} → a + b ∈ Λ ∧ (p : V → V) (a + b) = (0 : V) := by
  intro V _ p Λ a b ha hb
  exact ⟨Λ.add_mem ha.1 hb.1, by rw [map_add (f := _), ha.2, hb.2, add_zero]⟩

theorem UpperTheory.Reformulated.B.P9.aux7 :
    ∀ {V : Type} [inst : AddCommGroup V] (p : V →+ V) (Λ : AddSubgroup V), (0 : V) ∈ Λ ∧ (p : V → V) (0 : V) = (0 : V) := by
  intro V _ p Λ
  exact ⟨Λ.zero_mem, map_zero p⟩

theorem UpperTheory.Reformulated.B.P9.aux8 :
    ∀ {V : Type} [inst : AddCommGroup V] (p : V →+ V) (Λ : AddSubgroup V) {a : V},
      a ∈ {x : V | x ∈ Λ ∧ (p : V → V) x = (0 : V)} → -a ∈ Λ ∧ (p : V → V) (-a) = (0 : V) := by
  intro V _ p Λ a ha
  exact ⟨Λ.neg_mem ha.1, by rw [map_neg, ha.2, neg_zero]⟩

noncomputable def UpperTheory.Reformulated.B.P9.partQ :
    {V : Type} → [inst : AddCommGroup V] → (V →+ V) → AddSubgroup V → AddSubgroup V :=
    fun {V : Type} [inst : AddCommGroup V] (p : V →+ V) (Λ : AddSubgroup V) ↦
      { carrier := {x : V | x ∈ Λ ∧ (p : V → V) x = (0 : V)}, add_mem' := @UpperTheory.Reformulated.B.P9.aux6 V inst p Λ,
        zero_mem' := UpperTheory.Reformulated.B.P9.aux7 p Λ, neg_mem' := @UpperTheory.Reformulated.B.P9.aux8 V inst p Λ : AddSubgroup V }

theorem UpperTheory.Reformulated.B.P9.reps_prod :
    ∀ {V : Type} [inst : AddCommGroup V] [_root_.Module ℂ V] {M Λ : AddSubgroup V} (p : V →+ V),
      (∀ (x : V), (p : V → V) ((p : V → V) x) = (p : V → V) x) →
        (∀ x ∈ Λ, (p : V → V) x ∈ Λ) →
          (∀ x ∈ M, (p : V → V) x ∈ M) →
            ∀ {A B : Finset V},
              UpperTheory.Reformulated.B.P9.IsReps M (UpperTheory.Reformulated.B.P9.partP p Λ) A →
                UpperTheory.Reformulated.B.P9.IsReps M (UpperTheory.Reformulated.B.P9.partQ p Λ) B →
                  UpperTheory.Reformulated.B.P9.IsReps M Λ (Finset.image (fun (w : V × V) ↦ w.1 + w.2) (A ×ˢ B)) := by
  intro V _ _ M Λ p hpp hΛ hM A B hA hB
  obtain ⟨hA1, hA2, hA3⟩ := hA
  obtain ⟨hB1, hB2, hB3⟩ := hB
  have hA1' : ∀ x ∈ A, x ∈ Λ ∧ p x = x := hA1
  have hB1' : ∀ x ∈ B, x ∈ Λ ∧ p x = 0 := hB1
  have hA3' : ∀ y, (y ∈ Λ ∧ p y = y) → ∃ x ∈ A, y - x ∈ M := hA3
  have hB3' : ∀ y, (y ∈ Λ ∧ p y = 0) → ∃ x ∈ B, y - x ∈ M := hB3
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨⟨a, b⟩, hw, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨ha, hb⟩ := Finset.mem_product.1 hw
    exact Λ.add_mem (hA1' a ha).1 (hB1' b hb).1
  · intro x hx y hy hxy
    obtain ⟨⟨a, b⟩, hw, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨ha, hb⟩ := Finset.mem_product.1 hw
    obtain ⟨⟨a', b'⟩, hw', rfl⟩ := Finset.mem_image.1 hy
    obtain ⟨ha', hb'⟩ := Finset.mem_product.1 hw'
    change a + b - (a' + b') ∈ M at hxy
    change a + b = a' + b'
    have h1 : p (a + b - (a' + b')) = a - a' := by
      rw [map_sub, map_add (f := _), map_add (f := _), (hA1' a ha).2, (hA1' a' ha').2, (hB1' b hb).2,
        (hB1' b' hb').2, add_zero, add_zero]
    have h2 : a = a' := hA2 a ha a' ha' (h1 ▸ hM _ hxy)
    have h3 : b = b' := by
      refine hB2 b hb b' hb' ?_
      rwa [h2, add_sub_add_left_eq_sub] at hxy
    rw [h2, h3]
  · intro y hy
    obtain ⟨a, ha, hya⟩ := hA3' (p y) ⟨hΛ y hy, hpp y⟩
    obtain ⟨b, hb, hyb⟩ := hB3' (y - p y)
      ⟨Λ.sub_mem hy (hΛ y hy), by rw [map_sub, hpp, sub_self]⟩
    refine ⟨a + b, Finset.mem_image.2 ⟨(a, b), Finset.mem_product.2 ⟨ha, hb⟩, rfl⟩, ?_⟩
    have h : y - (a + b) = (p y - a) + (y - p y - b) := by abel
    rw [h]
    exact M.add_mem hya hyb
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CocycleMultiplicative
noncomputable def UpperTheory.Reformulated.B.CocycleMultiplicative.cT :
    {A : Type} → [inst : CommRing A] → (A →+* A) → {m p : Type} → Matrix m p A → Matrix p m A :=
    fun {A : Type} [CommRing A] (σ : A →+* A) {m p : Type} (M : Matrix m p A) ↦ (M.map (⇑σ : A → A)).transpose

private theorem UpperTheory.Reformulated.B.CocycleMultiplicative.cT_mul {A : Type} [CommRing A] (σ : A →+* A) {n : Type} [Fintype n]
    (P Q : Matrix n n A) :
    UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ (P * Q) = UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ Q * UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ P := by
  unfold UpperTheory.Reformulated.B.CocycleMultiplicative.cT
  rw [Matrix.map_mul, Matrix.transpose_mul]

private theorem UpperTheory.Reformulated.B.CocycleMultiplicative.cT_one {A : Type} [CommRing A] (σ : A →+* A) {n : Type} [Fintype n]
    [DecidableEq n] : UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ (1 : Matrix n n A) = 1 := by
  unfold UpperTheory.Reformulated.B.CocycleMultiplicative.cT
  rw [Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.transpose_one]

theorem UpperTheory.Reformulated.B.CocycleMultiplicative.aux2 :
    ∀ {A : Type} [inst : CommRing A] {n : Type} [inst_1 : Fintype n] [inst_2 : DecidableEq n] (σ : A →+* A)
      (J : Matrix n n A) {a b : GL n A},
      a ∈ {g : GL n A | UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ (↑g : Matrix n n A) * J * (↑g : Matrix n n A) = J} →
        b ∈ {g : GL n A | UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ (↑g : Matrix n n A) * J * (↑g : Matrix n n A) = J} →
          a * b ∈ {g : GL n A | UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ (↑g : Matrix n n A) * J * (↑g : Matrix n n A) = J} := by
  intro A _ n _ _ σ J a b ha hb
  simp only [Set.mem_setOf_eq] at ha hb ⊢
  rw [Units.val_mul, UpperTheory.Reformulated.B.CocycleMultiplicative.cT_mul]
  calc _ = UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ (↑b : Matrix n n A) *
        (UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ (↑a : Matrix n n A) * J * (↑a : Matrix n n A)) * (↑b : Matrix n n A) := by
        simp only [Matrix.mul_assoc]
    _ = J := by rw [ha, hb]

theorem UpperTheory.Reformulated.B.CocycleMultiplicative.aux3 :
    ∀ {A : Type} [inst : CommRing A] {n : Type} [inst_1 : Fintype n] [inst_2 : DecidableEq n] (σ : A →+* A)
      (J : Matrix n n A), UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ (↑(1 : GL n A) : Matrix n n A) * J * (↑(1 : GL n A) : Matrix n n A) = J := by
  intro A _ n _ _ σ J
  rw [Units.val_one, UpperTheory.Reformulated.B.CocycleMultiplicative.cT_one, Matrix.one_mul, Matrix.mul_one]

theorem UpperTheory.Reformulated.B.CocycleMultiplicative.aux4 :
    ∀ {A : Type} [inst : CommRing A] {n : Type} [inst_1 : Fintype n] [inst_2 : DecidableEq n] (σ : A →+* A)
      (J : Matrix n n A) {g : GL n A},
      g ∈ {g : GL n A | UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ (↑g : Matrix n n A) * J * (↑g : Matrix n n A) = J} →
        g⁻¹ ∈ {g : GL n A | UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ (↑g : Matrix n n A) * J * (↑g : Matrix n n A) = J} := by
  intro A _ n _ _ σ J g hg
  simp only [Set.mem_setOf_eq] at hg ⊢
  have h1 : (↑g : Matrix n n A) * (↑(g⁻¹) : Matrix n n A) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h2 : UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ (↑(g⁻¹) : Matrix n n A) * UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ (↑g : Matrix n n A) = 1 := by
    rw [← UpperTheory.Reformulated.B.CocycleMultiplicative.cT_mul, h1, UpperTheory.Reformulated.B.CocycleMultiplicative.cT_one]
  calc _ = UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ (↑(g⁻¹) : Matrix n n A) *
        (UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ (↑g : Matrix n n A) * J * (↑g : Matrix n n A)) * (↑(g⁻¹) : Matrix n n A) := by
        rw [hg]
    _ = (UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ (↑(g⁻¹) : Matrix n n A) * UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ (↑g : Matrix n n A)) * J *
        ((↑g : Matrix n n A) * (↑(g⁻¹) : Matrix n n A)) := by
        simp only [Matrix.mul_assoc]
    _ = J := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

noncomputable def UpperTheory.Reformulated.B.CocycleMultiplicative.UJ :
    {A : Type} →
      [inst : CommRing A] →
        {n : Type} → [inst_1 : Fintype n] → [inst_2 : DecidableEq n] → (A →+* A) → Matrix n n A → Subgroup (GL n A) :=
    fun {A : Type} [inst : CommRing A] {n : Type} [inst_1 : Fintype n] [inst_2 : DecidableEq n] (σ : A →+* A)
        (J : Matrix n n A) ↦
      { carrier := {g : GL n A | UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ (↑g : Matrix n n A) * J * (↑g : Matrix n n A) = J},
        mul_mem' := @UpperTheory.Reformulated.B.CocycleMultiplicative.aux2 A inst n inst_1 inst_2 σ J, one_mem' := UpperTheory.Reformulated.B.CocycleMultiplicative.aux3 σ J,
        inv_mem' := @UpperTheory.Reformulated.B.CocycleMultiplicative.aux4 A inst n inst_1 inst_2 σ J : Subgroup (GL n A) }

noncomputable def UpperTheory.Reformulated.B.CocycleMultiplicative.UE :
    (E : Type) → [inst : Field E] → [inst_1 : NumberField E] → [NumberField.IsCMField E] → (n : ℕ) → Subgroup (GL (Fin n) E) :=
    fun (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (n : ℕ) ↦
      UpperTheory.Reformulated.B.CocycleMultiplicative.UJ (NumberField.IsCMField.complexConj E).toRingEquiv.toRingHom (1 : Matrix (Fin n) (Fin n) E)

open scoped Matrix.Norms.L2Operator in
private theorem UpperTheory.Reformulated.B.CocycleMultiplicative.norm_of_mem_spectrum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (h : star A * A = 1) {z : ℂ} (hz : z ∈ spectrum ℂ A) : ‖z‖ = (1 : ℝ) := by
  have hu : A ∈ unitary (Matrix (Fin n) (Fin n) ℂ) :=
    ⟨h, mul_eq_one_comm.mp h⟩
  rcases subsingleton_or_nontrivial (Matrix (Fin n) (Fin n) ℂ) with hs | hn
  · exact absurd hz (by simp [spectrum.of_subsingleton])
  · simpa using spectrum.subset_circle_of_unitary hu hz

theorem UpperTheory.Reformulated.B.CocycleMultiplicative.norm_eq_one_of_root :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : NumberField.IsCMField E] {n : ℕ}
      (γ : ↥(UpperTheory.Reformulated.B.CocycleMultiplicative.UE E n)) (τ : E →+* ℂ),
      ∀ z ∈ (Polynomial.map τ (↑(↑γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly).roots, ‖z‖ = (1 : ℝ) := by
  intro E _ _ _ n γ τ z hz
  have hγ := γ.2
  obtain ⟨g, hg⟩ := γ
  simp only at hz
  have hg' : UpperTheory.Reformulated.B.CocycleMultiplicative.cT (NumberField.IsCMField.complexConj E).toRingEquiv.toRingHom
      (↑g : Matrix (Fin n) (Fin n) E) * 1 * (↑g : Matrix (Fin n) (Fin n) E) = 1 := hg
  rw [Matrix.mul_one] at hg'
  have hroot : ((↑g : Matrix (Fin n) (Fin n) E).map τ).charpoly.IsRoot z := by
    rw [Matrix.charpoly_map]
    exact (Polynomial.mem_roots'.mp hz).2
  have hstar : star ((↑g : Matrix (Fin n) (Fin n) E).map τ) =
      (UpperTheory.Reformulated.B.CocycleMultiplicative.cT (NumberField.IsCMField.complexConj E).toRingEquiv.toRingHom
        (↑g : Matrix (Fin n) (Fin n) E)).map τ := by
    ext i j
    simp [UpperTheory.Reformulated.B.CocycleMultiplicative.cT, Matrix.star_apply]
  have hU : star ((↑g : Matrix (Fin n) (Fin n) E).map τ) * (↑g : Matrix (Fin n) (Fin n) E).map τ = 1 := by
    rw [hstar, ← Matrix.map_mul, hg', Matrix.map_one _ (map_zero τ) (map_one τ)]
  exact UpperTheory.Reformulated.B.CocycleMultiplicative.norm_of_mem_spectrum _ hU (Matrix.mem_spectrum_of_isRoot_charpoly hroot)
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsSmooth
noncomputable def UpperTheory.Reformulated.B.DYka2.IsSmooth :
    {k G V : Type} →
      [inst : Field k] →
        [inst_1 : Group G] →
          [inst_2 : AddCommGroup V] → [inst_3 : _root_.Module k V] → [TopologicalSpace G] → Representation k G V → Prop :=
    fun {k G V : Type} [Field k] [Group G] [AddCommGroup V] [_root_.Module k V] [TopologicalSpace G]
        (ρ : Representation k G V) ↦
      ∀ (v : V), IsOpen {g : G | ((ρ : G → V →ₗ[k] V) g : V → V) v = v}

theorem UpperTheory.Reformulated.B.DYka2.main :
    ∀ {Γ V W : Type} [inst : Group Γ] [inst_1 : TopologicalSpace Γ] [IsTopologicalGroup Γ] [inst_3 : AddCommGroup V]
      [inst_4 : _root_.Module ℂ V] [inst_5 : AddCommGroup W] [inst_6 : _root_.Module ℂ W] {ρ : Representation ℂ Γ V}
      {σ : Representation ℂ Γ W},
      UpperTheory.Reformulated.B.DYka2.IsSmooth ρ →
        ∀ (f : ρ.IntertwiningMap σ) {L : Subgroup Γ},
          IsCompact (↑L : Set Γ) →
            ∀ (χ : Γ → ℂ) (u : V),
              (f : V → W) u ≠ (0 : W) →
                (∀ g ∈ L, ((σ : Γ → W →ₗ[ℂ] W) g : W → W) ((f : V → W) u) = χ g • (f : V → W) u) →
                  ∃ (v : V), v ≠ (0 : V) ∧ ∀ g ∈ L, ((ρ : Γ → V →ₗ[ℂ] V) g : V → V) v = χ g • v := by
  intro Γ V W _ _ _ _ _ _ _ ρ σ hρ f L hL χ u hu hχ
  haveI : CompactSpace L := isCompact_iff_compactSpace.mp hL
  have hint : ∀ (g : Γ) (v : V), f (ρ g v) = σ g (f v) := fun g v => Representation.IntertwiningMap.isIntertwining ρ σ f g v
  have hmul : ∀ g ∈ L, ∀ h ∈ L, χ (g * h) = χ g * χ h := by
    intro g hg h hh
    have key : χ (g * h) • f u = (χ g * χ h) • f u := by
      rw [← hχ (g * h) (L.mul_mem hg hh), map_mul, Module.End.mul_apply, hχ h hh, map_smul,
        hχ g hg, smul_smul, mul_comm]
    exact smul_left_injective ℂ hu key
  have h1 : χ 1 = 1 := by
    have key : χ 1 • f u = (1 : ℂ) • f u := by
      rw [← hχ 1 L.one_mem, map_one, one_smul]; rfl
    exact smul_left_injective ℂ hu key
  have hne : ∀ g ∈ L, χ g ≠ 0 := by
    intro g hg h0
    have := hmul g hg g⁻¹ (L.inv_mem hg)
    rw [mul_inv_cancel, h1, h0, zero_mul] at this
    exact one_ne_zero this
  let H : Subgroup L :=
    { carrier := {g | ρ (g : Γ) u = u}
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, hb, ha]
      one_mem' := by simp
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        have : ρ ((a : Γ)⁻¹) (ρ (a : Γ) u) = u := by
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl
        rw [ha] at this
        simpa using this }
  have hHopen : IsOpen (H : Set L) := (hρ u).preimage continuous_subtype_val
  haveI : Finite (L ⧸ H) := Subgroup.quotient_finite_of_isOpen H hHopen
  haveI : Fintype (L ⧸ H) := Fintype.ofFinite _
  have hχH : ∀ h : L, h ∈ H → χ (h : Γ) = 1 := by
    intro h hh
    have e : ρ (h : Γ) u = u := hh
    have key : χ (h : Γ) • f u = (1 : ℂ) • f u := by
      rw [← hχ h h.2, ← hint, e, one_smul]
    exact smul_left_injective ℂ hu key
  let φ : L → V := fun g => (χ (g : Γ))⁻¹ • ρ (g : Γ) u
  have hφ : ∀ a b : L, QuotientGroup.leftRel H a b → φ a = φ b := by
    intro a b hab
    rw [QuotientGroup.leftRel_apply] at hab
    have hb : (b : Γ) = a * ((a⁻¹ * b : L) : Γ) := by simp
    have e : ρ ((a⁻¹ * b : L) : Γ) u = u := hab
    have c := hχH _ hab
    simp only [φ]
    rw [hb, hmul _ a.2 _ (a⁻¹ * b).2, c, mul_one, map_mul, Module.End.mul_apply, e]
  let ψ : L ⧸ H → V := Quotient.lift φ hφ
  have hψ : ∀ g : L, ψ (g : L ⧸ H) = φ g := fun g => rfl
  have hfψ : ∀ q : L ⧸ H, f (ψ q) = f u := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H g =>
      rw [hψ]
      simp only [φ]
      rw [map_smul, hint, hχ g g.2, smul_smul, inv_mul_cancel₀ (hne g g.2), one_smul]
  have hact : ∀ (l : L) (q : L ⧸ H), ρ (l : Γ) (ψ q) = χ (l : Γ) • ψ (l • q) := by
    intro l q
    induction q using QuotientGroup.induction_on with
    | H g =>
      have : l • (g : L ⧸ H) = ((l * g : L) : L ⧸ H) := rfl
      rw [this, hψ, hψ]
      simp only [φ]
      rw [map_smul, Subgroup.coe_mul, hmul _ l.2 _ g.2, map_mul, Module.End.mul_apply, smul_smul,
        mul_inv, ← mul_assoc, mul_inv_cancel₀ (hne l l.2), one_mul]
  refine ⟨∑ q : L ⧸ H, ψ q, ?_, ?_⟩
  · intro h0
    have e : f (∑ q : L ⧸ H, ψ q) = (Fintype.card (L ⧸ H) : ℂ) • f u := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp only [hfψ]
      rw [Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
    rw [h0, map_zero] at e
    have hc : (Fintype.card (L ⧸ H) : ℂ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    exact (smul_ne_zero hc hu) e.symm
  · intro g hg
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.smul_sum]
    simp only [hact ⟨g, hg⟩]
    exact (Equiv.sum_comp (MulAction.toPerm (⟨g, hg⟩ : L)) (fun q => χ g • ψ q))
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsClosedEmbeddingToM
noncomputable def UpperTheory.Reformulated.B.Qk16.Jm :
    {n : ℕ} → (Fin n → Bool) → Matrix (Fin n) (Fin n) ℂ :=
    fun {n : ℕ} (ε : Fin n → Bool) ↦ Matrix.diagonal fun (a : Fin n) ↦ if ε a = Bool.true then (1 : ℂ) else (-1 : ℂ)

noncomputable def UpperTheory.Reformulated.B.Qk16.inUJ :
    {n : ℕ} → (Fin n → Bool) → Matrix (Fin n) (Fin n) ℂ → Prop :=
    fun {n : ℕ} (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) ↦
      g.conjTranspose * UpperTheory.Reformulated.B.Qk16.Jm ε * g = UpperTheory.Reformulated.B.Qk16.Jm ε

theorem UpperTheory.Reformulated.B.Qk16.aux3 :
    ∀ {n : ℕ} (ε : Fin n → Bool) {g h : (Matrix (Fin n) (Fin n) ℂ)ˣ},
      g ∈ {g : (Matrix (Fin n) (Fin n) ℂ)ˣ | UpperTheory.Reformulated.B.Qk16.inUJ ε (↑g : Matrix (Fin n) (Fin n) ℂ)} →
        h ∈ {g : (Matrix (Fin n) (Fin n) ℂ)ˣ | UpperTheory.Reformulated.B.Qk16.inUJ ε (↑g : Matrix (Fin n) (Fin n) ℂ)} →
          g * h ∈ {g : (Matrix (Fin n) (Fin n) ℂ)ˣ | UpperTheory.Reformulated.B.Qk16.inUJ ε (↑g : Matrix (Fin n) (Fin n) ℂ)} := by
  intro n ε g h hg hh
  simp only [Set.mem_setOf_eq, UpperTheory.Reformulated.B.Qk16.inUJ] at hg hh ⊢
  rw [Units.val_mul, Matrix.conjTranspose_mul]
  calc (h : Matrix (Fin n) (Fin n) ℂ).conjTranspose * (g : Matrix (Fin n) (Fin n) ℂ).conjTranspose *
        UpperTheory.Reformulated.B.Qk16.Jm ε * ((g : Matrix (Fin n) (Fin n) ℂ) * (h : Matrix (Fin n) (Fin n) ℂ))
      = (h : Matrix (Fin n) (Fin n) ℂ).conjTranspose * ((g : Matrix (Fin n) (Fin n) ℂ).conjTranspose *
        UpperTheory.Reformulated.B.Qk16.Jm ε * (g : Matrix (Fin n) (Fin n) ℂ)) * (h : Matrix (Fin n) (Fin n) ℂ) := by
        simp only [Matrix.mul_assoc]
    _ = UpperTheory.Reformulated.B.Qk16.Jm ε := by rw [hg, hh]

theorem UpperTheory.Reformulated.B.Qk16.aux4 :
    ∀ {n : ℕ} (ε : Fin n → Bool),
      (↑(1 : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ).conjTranspose * UpperTheory.Reformulated.B.Qk16.Jm ε *
          (↑(1 : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) =
        UpperTheory.Reformulated.B.Qk16.Jm ε := by
  intro n ε
  simp

theorem UpperTheory.Reformulated.B.Qk16.aux5 :
    ∀ {n : ℕ} (ε : Fin n → Bool) {g : (Matrix (Fin n) (Fin n) ℂ)ˣ},
      g ∈ {g : (Matrix (Fin n) (Fin n) ℂ)ˣ | UpperTheory.Reformulated.B.Qk16.inUJ ε (↑g : Matrix (Fin n) (Fin n) ℂ)} →
        g⁻¹ ∈ {g : (Matrix (Fin n) (Fin n) ℂ)ˣ | UpperTheory.Reformulated.B.Qk16.inUJ ε (↑g : Matrix (Fin n) (Fin n) ℂ)} := by
  intro n ε g hg
  simp only [Set.mem_setOf_eq, UpperTheory.Reformulated.B.Qk16.inUJ] at hg ⊢
  have h1 : (g : Matrix (Fin n) (Fin n) ℂ) * ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = 1 :=
    Units.mul_inv g
  generalize ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = B at h1 ⊢
  generalize (g : Matrix (Fin n) (Fin n) ℂ) = A at h1 hg
  calc B.conjTranspose * UpperTheory.Reformulated.B.Qk16.Jm ε * B
      = B.conjTranspose * (A.conjTranspose * UpperTheory.Reformulated.B.Qk16.Jm ε * A) * B := by rw [hg]
    _ = (A * B).conjTranspose * UpperTheory.Reformulated.B.Qk16.Jm ε * (A * B) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = UpperTheory.Reformulated.B.Qk16.Jm ε := by rw [h1]; simp

noncomputable def UpperTheory.Reformulated.B.Qk16.UJ :
    {n : ℕ} → (Fin n → Bool) → Subgroup (Matrix (Fin n) (Fin n) ℂ)ˣ :=
    fun {n : ℕ} (ε : Fin n → Bool) ↦
      { carrier := {g : (Matrix (Fin n) (Fin n) ℂ)ˣ | UpperTheory.Reformulated.B.Qk16.inUJ ε (↑g : Matrix (Fin n) (Fin n) ℂ)},
        mul_mem' := @UpperTheory.Reformulated.B.Qk16.aux3 n ε, one_mem' := UpperTheory.Reformulated.B.Qk16.aux4 ε,
        inv_mem' := @UpperTheory.Reformulated.B.Qk16.aux5 n ε : Subgroup (Matrix (Fin n) (Fin n) ℂ)ˣ }

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qk16.toM :
    {n : ℕ} → {ε : Fin n → Bool} → ↥(UpperTheory.Reformulated.B.Qk16.UJ ε) → Matrix (Fin n) (Fin n) ℂ :=
    fun {n : ℕ} {ε : Fin n → Bool} (g : ↥(UpperTheory.Reformulated.B.Qk16.UJ ε)) ↦
      (↑(↑g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)

private theorem UpperTheory.Reformulated.B.Qk16.Jm_mul_Jm {n : ℕ} (ε : Fin n → Bool) :
    UpperTheory.Reformulated.B.Qk16.Jm ε * UpperTheory.Reformulated.B.Qk16.Jm ε = 1 := by
  unfold UpperTheory.Reformulated.B.Qk16.Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> simp

private theorem UpperTheory.Reformulated.B.Qk16.left_inv {n : ℕ} (ε : Fin n → Bool) {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : UpperTheory.Reformulated.B.Qk16.inUJ ε A) :
    UpperTheory.Reformulated.B.Qk16.Jm ε * A.conjTranspose * UpperTheory.Reformulated.B.Qk16.Jm ε * A = 1 := by
  have h : A.conjTranspose * UpperTheory.Reformulated.B.Qk16.Jm ε * A = UpperTheory.Reformulated.B.Qk16.Jm ε := hA
  calc UpperTheory.Reformulated.B.Qk16.Jm ε * A.conjTranspose * UpperTheory.Reformulated.B.Qk16.Jm ε * A
      = UpperTheory.Reformulated.B.Qk16.Jm ε * (A.conjTranspose * UpperTheory.Reformulated.B.Qk16.Jm ε * A) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h, UpperTheory.Reformulated.B.Qk16.Jm_mul_Jm]

theorem UpperTheory.Reformulated.B.Qk16.isClosedEmbedding_toM :
    ∀ {n : ℕ} (ε : Fin n → Bool), Topology.IsClosedEmbedding fun (g : ↥(UpperTheory.Reformulated.B.Qk16.UJ ε)) ↦ UpperTheory.Reformulated.B.Qk16.toM g := by
  intro n ε
  have hc : Continuous fun (g : ↥(UpperTheory.Reformulated.B.Qk16.UJ ε)) ↦ UpperTheory.Reformulated.B.Qk16.toM g :=
    Units.continuous_val.comp continuous_subtype_val
  refine ⟨?_, ?_⟩
  · let F : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ × (Matrix (Fin n) (Fin n) ℂ)ᵐᵒᵖ :=
      fun A ↦ (A, MulOpposite.op (UpperTheory.Reformulated.B.Qk16.Jm ε * A.conjTranspose * UpperTheory.Reformulated.B.Qk16.Jm ε))
    have hF : Continuous F :=
      continuous_id.prodMk (MulOpposite.continuous_op.comp
        ((continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const))
    refine Topology.IsEmbedding.of_comp hc hF ?_
    have he : Topology.IsEmbedding
        ((Units.embedProduct (Matrix (Fin n) (Fin n) ℂ)) ∘
          (Subtype.val : ↥(UpperTheory.Reformulated.B.Qk16.UJ ε) → (Matrix (Fin n) (Fin n) ℂ)ˣ)) :=
      Units.isEmbedding_embedProduct.comp Topology.IsEmbedding.subtypeVal
    have heq : (F ∘ fun (g : ↥(UpperTheory.Reformulated.B.Qk16.UJ ε)) ↦ UpperTheory.Reformulated.B.Qk16.toM g) =
        ((Units.embedProduct (Matrix (Fin n) (Fin n) ℂ)) ∘
          (Subtype.val : ↥(UpperTheory.Reformulated.B.Qk16.UJ ε) → (Matrix (Fin n) (Fin n) ℂ)ˣ)) := by
      funext g
      have hg : UpperTheory.Reformulated.B.Qk16.inUJ ε (g.1 : Matrix (Fin n) (Fin n) ℂ) := g.2
      have h := Units.inv_eq_of_mul_eq_one_left (UpperTheory.Reformulated.B.Qk16.left_inv ε hg)
      rw [Function.comp_apply, Function.comp_apply, Units.embedProduct_apply, h]
    rw [heq]
    exact he
  · have hr : Set.range (fun (g : ↥(UpperTheory.Reformulated.B.Qk16.UJ ε)) ↦ UpperTheory.Reformulated.B.Qk16.toM g) =
        {A | A.conjTranspose * UpperTheory.Reformulated.B.Qk16.Jm ε * A = UpperTheory.Reformulated.B.Qk16.Jm ε} := by
      ext A
      constructor
      · rintro ⟨g, rfl⟩
        exact g.2
      · intro hA
        have h := UpperTheory.Reformulated.B.Qk16.left_inv ε (A := A) hA
        exact ⟨⟨⟨A, _, mul_eq_one_comm.mp h, h⟩, hA⟩, rfl⟩
    rw [hr]
    exact isClosed_eq
      ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
      continuous_const
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NoetherNormalizationChart
universe u

namespace UpperTheory.NoetherNormalizationChart

open MvPolynomial

variable {A : Type u} [CommRing A] {n : ℕ}

private noncomputable def shear (b : ℕ) (c : A) :
    MvPolynomial (Fin (n + 1)) A →ₐ[A] MvPolynomial (Fin (n + 1)) A :=
  aeval (Fin.cases (X 0) (fun i : Fin n => X i.succ + C c * X 0 ^ (b ^ (i.succ : ℕ))))

private lemma shear_zero (b : ℕ) (c : A) : shear (n := n) b c (X 0) = X 0 := by
  simp [shear]

private lemma shear_succ (b : ℕ) (c : A) (i : Fin n) :
    shear (n := n) b c (X i.succ) = X i.succ + C c * X 0 ^ (b ^ (i.succ : ℕ)) := by
  simp [shear]

private lemma shear_comp (b : ℕ) (c d : A) (h : c + d = 0) :
    (shear (n := n) b c).comp (shear b d) = AlgHom.id _ _ := by
  refine MvPolynomial.algHom_ext fun i => ?_
  cases i using Fin.cases with
  | zero => simp [shear_zero]
  | succ i =>
    rw [AlgHom.comp_apply, shear_succ, map_add (f := _), map_mul, map_pow, shear_zero, shear_succ,
      algHom_C, algebraMap_eq, add_assoc, ← add_mul, ← C_add, h]
    simp

private noncomputable def chart (A : Type u) [CommRing A] (n b : ℕ) :
    MvPolynomial (Fin (n + 1)) A ≃ₐ[A] Polynomial (MvPolynomial (Fin n) A) :=
  (AlgEquiv.ofAlgHom (shear b 1) (shear b (-1)) (shear_comp b 1 (-1) (by simp))
    (shear_comp b (-1) 1 (by simp))).trans (finSuccEquiv A n)

private lemma chart_X [Nontrivial A] {b : ℕ} (hb : b ≠ 0) (i : Fin (n + 1)) :
    (chart A n b (X i)).IsMonicOfDegree (b ^ (i : ℕ)) := by
  cases i using Fin.cases with
  | zero =>
    have : chart A n b (X 0) = Polynomial.X := by
      simp [chart, shear_zero, finSuccEquiv_X_zero]
    rw [this]
    exact ⟨by simp, Polynomial.monic_X⟩
  | succ i =>
    have : chart A n b (X i.succ)
        = Polynomial.X ^ (b ^ (i.succ : ℕ)) + Polynomial.C (X i) := by
      simp [chart, shear_succ, finSuccEquiv_X_zero, finSuccEquiv_X_succ, add_comm]
    rw [this]
    exact ⟨Polynomial.natDegree_X_pow_add_C, Polynomial.monic_X_pow_add_C _ (pow_ne_zero _ hb)⟩

private lemma chart_C (b : ℕ) (a : A) : chart A n b (C a) = Polynomial.C (C a) :=
  (chart A n b).commutes a

private lemma chart_monomial [Nontrivial A] {b : ℕ} (hb : b ≠ 0) (v : Fin (n + 1) →₀ ℕ) :
    (chart A n b (monomial v 1)).IsMonicOfDegree (∑ i, v i * b ^ (i : ℕ)) := by
  have h : chart A n b (monomial v 1) = ∏ i, chart A n b (X i) ^ v i := by
    rw [monomial_eq, Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
    simp
  have hm : ∀ i ∈ Finset.univ, (chart A n b (X i) ^ v i).Monic :=
    fun i _ => (chart_X hb i).monic.pow _
  rw [h]
  refine ⟨?_, Polynomial.monic_prod_of_monic _ _ hm⟩
  rw [Polynomial.natDegree_prod_of_monic _ _ hm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(chart_X hb i).monic.natDegree_pow, (chart_X hb i).natDegree_eq]

private lemma weight_inj {m b : ℕ} (v w : Fin m → ℕ) (hv : ∀ i, v i < b) (hw : ∀ i, w i < b)
    (h : ∑ i, v i * b ^ (i : ℕ) = ∑ i, w i * b ^ (i : ℕ)) : v = w := by
  have key : (fun i => (⟨v i, hv i⟩ : Fin b)) = fun i => ⟨w i, hw i⟩ := by
    apply finFunctionFinEquiv.injective
    apply Fin.ext
    rw [finFunctionFinEquiv_apply, finFunctionFinEquiv_apply]
    exact h
  funext i
  exact congrArg Fin.val (congrFun key i)

end UpperTheory.NoetherNormalizationChart

open UpperTheory.NoetherNormalizationChart in
theorem UpperTheory.exists_monic_change_of_variables :
    ∀ (A : Type u) [CommRing A] [IsDomain A] (n : ℕ) (f : MvPolynomial (Fin (n + 1)) A), f ≠ 0 → ∃ (e : MvPolynomial (Fin (n + 1)) A ≃ₐ[A] Polynomial (MvPolynomial (Fin n) A)) (a : A), a ≠ 0 ∧ (e f).leadingCoeff = MvPolynomial.C a := by
  intro A _ _ n f hf
  classical
  set b := f.totalDegree + 1 with hbdef
  have hb : b ≠ 0 := Nat.succ_ne_zero _
  let wt : (Fin (n + 1) →₀ ℕ) → ℕ := fun v => ∑ i, v i * b ^ (i : ℕ)
  have hlt : ∀ v ∈ f.support, ∀ i, v i < b := fun v hv i =>
    Nat.lt_succ_of_le ((MvPolynomial.monomial_le_degreeOf i hv).trans
      (MvPolynomial.degreeOf_le_totalDegree f i))
  obtain ⟨v, hv, hmax⟩ := Finset.exists_max_image f.support wt (MvPolynomial.support_nonempty.mpr hf)
  have ha : f.coeff v ≠ 0 := MvPolynomial.mem_support_iff.mp hv
  have hsum : chart A n b f = ∑ w ∈ f.support,
      Polynomial.C (MvPolynomial.C (f.coeff w)) * chart A n b (MvPolynomial.monomial w 1) := by
    set_option synthInstance.maxHeartbeats 100000 in
      conv_lhs => rw [← f.support_sum_monomial_coeff, map_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [← chart_C b, ← map_mul, MvPolynomial.C_mul_monomial, mul_one]
  have hdeg : (chart A n b f).natDegree ≤ wt v := by
    rw [hsum]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun w hw => ?_
    refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
    rw [(chart_monomial hb w).natDegree_eq]
    exact hmax w hw
  have hcoeff : (chart A n b f).coeff (wt v) = MvPolynomial.C (f.coeff v) := by
    rw [hsum, Polynomial.finsetSum_coeff, Finset.sum_eq_single_of_mem v hv]
    · have h1 := (chart_monomial (A := A) hb v).monic.coeff_natDegree
      rw [(chart_monomial hb v).natDegree_eq] at h1
      rw [Polynomial.coeff_C_mul, h1, mul_one]
    · intro w hw hne
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_eq_zero_of_natDegree_lt, mul_zero]
      rw [(chart_monomial hb w).natDegree_eq]
      refine lt_of_le_of_ne (hmax w hw) fun h => hne ?_
      exact DFunLike.coe_injective (weight_inj w v (hlt w hw) (hlt v hv) h)
  refine ⟨chart A n b, f.coeff v, ha, ?_⟩
  have hne : (chart A n b f).coeff (wt v) ≠ 0 := by
    rw [hcoeff]
    simpa using ha
  rw [Polynomial.leadingCoeff, Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hdeg hne, hcoeff]
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.TendstoCut
open scoped Classical

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qi11.Af :
    (F : Type) → [inst : Field F] → [NumberField F] → Type :=
    fun (F : Type) [Field F] [NumberField F] ↦ IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F

theorem UpperTheory.Reformulated.B.Qi11.aux2 :
    ∀ {F : Type} [inst : Field F] [inst_1 : NumberField F]
      (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
      (a : IsDedekindDomain.HeightOneSpectrum.adicCompletion F v),
      ∀ᶠ (x : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) in Filter.cofinite,
        Pi.single v a x ∈
          (↑(IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F x) :
            Set (IsDedekindDomain.HeightOneSpectrum.adicCompletion F x)) := by
  intro F _ _ v a
  refine (Set.finite_singleton v).subset fun x hx => ?_
  by_contra h
  apply hx
  have hne : x ≠ v := h
  simp only [Set.mem_setOf_eq, Pi.single_eq_of_ne hne]
  exact zero_mem _

noncomputable def UpperTheory.Reformulated.B.Qi11.sglV :
    {F : Type} →
      [inst : Field F] →
        [inst_1 : NumberField F] →
          (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) →
            IsDedekindDomain.HeightOneSpectrum.adicCompletion F v → UpperTheory.Reformulated.B.Qi11.Af F :=
    fun {F : Type} [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
        (a : IsDedekindDomain.HeightOneSpectrum.adicCompletion F v) ↦
      (⟨Pi.single v a, UpperTheory.Reformulated.B.Qi11.aux2 v a⟩ :
        { x :
          (i : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) →
            (fun (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) ↦
                IsDedekindDomain.HeightOneSpectrum.adicCompletion F v)
              i //
          ∀ᶠ (i : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) in Filter.cofinite,
            x i ∈
              (fun (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) ↦
                  (↑(IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F v) :
                    Set (IsDedekindDomain.HeightOneSpectrum.adicCompletion F v)))
                i })

noncomputable def UpperTheory.Reformulated.B.Qi11.sglS :
    {F : Type} →
      [inst : Field F] →
        [inst_1 : NumberField F] →
          Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) → UpperTheory.Reformulated.B.Qi11.Af F :=
    fun {F : Type} [Field F] [NumberField F]
        (A : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) ↦
      ∑ v ∈ A, UpperTheory.Reformulated.B.Qi11.sglV v (1 : IsDedekindDomain.HeightOneSpectrum.adicCompletion F v)

private theorem UpperTheory.Reformulated.B.Qi11.tendsto_cut {ι : Type*} {R : ι → Type*} [∀ i, Zero (R i)]
    [∀ i, TopologicalSpace (R i)] {A : (i : ι) → Set (R i)} (h0 : ∀ i, (0 : R i) ∈ A i)
    (y z : RestrictedProduct R A Filter.cofinite) (hz : ∀ i, z i = 0)
    (f : Finset ι → RestrictedProduct R A Filter.cofinite)
    (hf : ∀ B i, f B i = if i ∈ B then 0 else y i) :
    Filter.Tendsto f Filter.atTop (nhds z) := by
  have hS : Filter.cofinite ≤ Filter.principal {i | y i ∈ A i} := Filter.le_principal_iff.2 y.2
  let g : Finset ι → RestrictedProduct R A (Filter.principal {i | y i ∈ A i}) := fun B =>
    ⟨fun i => if i ∈ B then 0 else y i, fun i hi => by
      show (if i ∈ B then 0 else y i) ∈ A i
      split_ifs
      · exact h0 i
      · exact hi⟩
  let o : RestrictedProduct R A (Filter.principal {i | y i ∈ A i}) := ⟨fun _ => 0, fun i _ => h0 i⟩
  have hg : Filter.Tendsto g Filter.atTop (nhds o) := by
    rw [RestrictedProduct.isEmbedding_coe_of_principal.tendsto_nhds_iff, tendsto_pi_nhds]
    intro i
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop ({i} : Finset ι)] with B hB
    have hi : i ∈ B := hB (Finset.mem_singleton_self i)
    show (0 : R i) = if i ∈ B then 0 else y i
    rw [if_pos hi]
  have h1 : f = RestrictedProduct.inclusion R A hS ∘ g :=
    funext fun B => RestrictedProduct.ext _ _ fun i => hf B i
  have h2 : z = RestrictedProduct.inclusion R A hS o := RestrictedProduct.ext _ _ fun i => hz i
  rw [h1, h2]
  exact ((RestrictedProduct.continuous_inclusion hS).tendsto o).comp hg

private theorem UpperTheory.Reformulated.B.Qi11.sglS_apply {F : Type} [Field F] [NumberField F]
    (A : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)))
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    UpperTheory.Reformulated.B.Qi11.sglS A w = if w ∈ A then 1 else 0 := by
  induction A using Finset.induction_on with
  | empty => rfl
  | insert v A hv ih =>
    have h : UpperTheory.Reformulated.B.Qi11.sglS (insert v A) =
        UpperTheory.Reformulated.B.Qi11.sglV v 1 + UpperTheory.Reformulated.B.Qi11.sglS A := Finset.sum_insert hv
    have h' : UpperTheory.Reformulated.B.Qi11.sglS (insert v A) w =
        (Pi.single v 1 : ∀ u, IsDedekindDomain.HeightOneSpectrum.adicCompletion F u) w +
          UpperTheory.Reformulated.B.Qi11.sglS A w := by
      rw [h]
      rfl
    rw [h', ih]
    by_cases hw : w = v
    · subst hw
      simp [hv]
    · simp [hw]

theorem UpperTheory.Reformulated.B.Qi11.tendsto_fin :
    ∀ {F : Type} [inst : Field F] [inst_1 : NumberField F] (y : UpperTheory.Reformulated.B.Qi11.Af F),
      Filter.Tendsto
        (fun (A : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) ↦
          ((1 : UpperTheory.Reformulated.B.Qi11.Af F) - UpperTheory.Reformulated.B.Qi11.sglS A) * y)
        Filter.atTop (nhds (0 : UpperTheory.Reformulated.B.Qi11.Af F)) := by
  intro F _ _ y
  have key := UpperTheory.Reformulated.B.Qi11.tendsto_cut
    (R := fun v => IsDedekindDomain.HeightOneSpectrum.adicCompletion F v)
    (A := fun v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) =>
      SetLike.coe (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F v))
    (fun v => zero_mem _)
  refine key y (0 : UpperTheory.Reformulated.B.Qi11.Af F) (fun w => ?_)
    (fun B => ((1 - UpperTheory.Reformulated.B.Qi11.sglS B) * y : UpperTheory.Reformulated.B.Qi11.Af F)) fun B w => ?_
  · rfl
  · show (1 - UpperTheory.Reformulated.B.Qi11.sglS B w) * y w = if w ∈ B then 0 else y w
    rw [UpperTheory.Reformulated.B.Qi11.sglS_apply]
    split_ifs <;> simp
end
