module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedEmbeddingToM
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.ColAnti

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiExistsStatement
noncomputable section

open Finset MeasureTheory Matrix
open scoped ContDiff

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def cpart1 (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (1 / 2 : ℂ) • (Z - Jm ε * Zᴴ * Jm ε)

def cpart2 (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (1 / (2 * Complex.I)) • (Z + Jm ε * Zᴴ * Jm ε)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def SmoothOnGV (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) ℂ → E) : Prop :=
  ∀ g₀, inUJ ε g₀ → ∃ (U : Set (Matrix (Fin n) (Fin n) ℂ)) (F : Matrix (Fin n) (Fin n) ℂ → E),
    IsOpen U ∧ g₀ ∈ U ∧ ContDiffOn ℝ ∞ F U ∧ ∀ g ∈ U, inUJ ε g → f g = F g

def RdV (X : Matrix (Fin n) (Fin n) ℂ) (f : Matrix (Fin n) (Fin n) ℂ → E) :
    Matrix (Fin n) (Fin n) ℂ → E :=
  fun g => deriv (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) 0

def EcV (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) (f : Matrix (Fin n) (Fin n) ℂ → E) :
    Matrix (Fin n) (Fin n) ℂ → E :=
  fun g => RdV (cpart1 ε Z) f g + Complex.I • RdV (cpart2 ε Z) f g

def EabV (ε : Fin n → Bool) (a b : Fin n) (f : Matrix (Fin n) (Fin n) ℂ → E) :
    Matrix (Fin n) (Fin n) ℂ → E :=
  EcV ε (Matrix.single a b 1) f

def casimirV (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) ℂ → E) : Matrix (Fin n) (Fin n) ℂ → E :=
  fun g => ∑ a, ∑ b, EabV ε a b (EabV ε b a f) g

def q0 (ε : Fin n → Bool) : ℕ := min (pOf ε) (qOf ε)

def IsHCParam (lam : Fin n → ℝ) : Prop :=
  StrictAnti lam ∧ ∀ a, ∃ m : ℤ, lam a - ((n : ℝ) - 1) / 2 = (m : ℝ)

structure KType (ε : Fin n → Bool) (Λ : Fin n → ℝ) where
  V : Type
  [instNACG : NormedAddCommGroup V]
  [instIPS : InnerProductSpace ℂ V]
  [instFD : FiniteDimensional ℂ V]
  [instCS : CompleteSpace V]
  τ : KG ε →* unitary (V →L[ℂ] V)
  cont : Continuous τ
  irred : ∀ W : Submodule ℂ V,
    (∀ k : KG ε, ∀ v ∈ W, ((τ k : unitary (V →L[ℂ] V)) : V →L[ℂ] V) v ∈ W) → W = ⊥ ∨ W = ⊤
  dτ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (V →L[ℂ] V)
  hasDeriv : ∀ X, inK ε X → ∀ γ : ℝ → KG ε,
    (∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
      HasDerivAt (fun t => ((τ (γ t) : unitary (V →L[ℂ] V)) : V →L[ℂ] V)) (dτ X) 0
  w : V
  w_norm : ‖w‖ = 1
  w_wt : ∀ a, dτ (Matrix.single a a 1) w = ((Λ a : ℝ) : ℂ) • w
  w_hw : ∀ a b, a < b → ε a = ε b → dτ (Matrix.single a b 1) w = 0

attribute [instance] KType.instNACG KType.instIPS KType.instFD KType.instCS

abbrev KType.op {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (k : KG ε) : T.V →L[ℂ] T.V :=
  ((T.τ k : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V)

def PsiExistsStatement (n : ℕ) : Prop :=
  ∀ (ε : Fin n → Bool) (lam : Fin n → ℝ) (h : ℝ) (T : KType ε (lowK ε lam)),
    IsHCParam lam → GapAtLeast ε lam h → 1 ≤ q0 ε →
    ∃ Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V),
      (∀ (k₁ k₂ : KG ε) (g : Matrix (Fin n) (Fin n) ℂ), inUJ ε g →
        Ψ (toMK k₁ * g * toMK k₂) = T.op k₁ * Ψ g * T.op k₂) ∧
      Ψ 1 = 1 ∧
      SmoothOnGV ε Ψ ∧
      (∀ g, inUJ ε g → casimirV ε Ψ g = ((casVal lam : ℝ) : ℂ) • Ψ g) ∧
      (∀ (k : KG ε) (X : Matrix (Fin n) (Fin n) ℂ), inP ε X →
        ‖Ψ (toMK k * NormedSpace.exp X)‖ ≤
          Real.exp (-(h / 8) * min (hs X) (Real.sqrt (hs X) / Real.sqrt (2 * q0 ε)))) ∧
      (∀ μ : Measure (UJ ε), μ.IsHaarMeasure →
        (16 * (n : ℝ) * q0 ε < h → Integrable (fun g : UJ ε => Ψ (toM g)) μ) ∧
        (8 * (n : ℝ) * q0 ε < h → MemLp (fun g : UJ ε => Ψ (toM g)) 2 μ) ∧
        (∀ s : ℝ, 0 ≤ s → 8 * (n : ℝ) * q0 ε + 4 * s * Real.sqrt (2 * q0 ε) < h →
          Integrable (fun g : UJ ε => ‖Ψ (toM g)‖ ^ 2 * hs (toM g) ^ (s / 2)) μ))

def trivialKType (ε : Fin n → Bool) : KType ε 0 where
  V := ℂ
  τ := 1
  cont := continuous_const
  irred := fun W _ => Ideal.eq_bot_or_top W
  dτ := 0
  hasDeriv := fun _ _ _ _ => by simpa using hasDerivAt_const (0 : ℝ) (1 : ℂ →L[ℂ] ℂ)
  w := 1
  w_norm := by simp
  w_wt := fun a => by simp
  w_hw := fun _ _ _ _ => by simp

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ProdOfFnSmul
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.S7.CapAd

open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli

variable {𝒰 : Type*} [Ring 𝒰] [Algebra ℂ 𝒰] {n : ℕ}

lemma prod_ofFn_sum {α : Type*} [Fintype α] : ∀ {p : ℕ} (f : Fin p → α → 𝒰),
    (List.ofFn fun j => ∑ a, f j a).prod = ∑ γ : Fin p → α, (List.ofFn fun j => f j (γ j)).prod
  | 0, f => by simp
  | p + 1, f => by
    rw [List.ofFn_succ, List.prod_cons, prod_ofFn_sum (fun j => f j.succ), Finset.sum_mul_sum,
      ← (Fin.consEquiv fun _ : Fin (p + 1) => α).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun γ _ => ?_
    show _ = (List.ofFn fun j => f j (Fin.cons (α := fun _ => α) a γ j)).prod
    simp only [List.ofFn_succ, List.prod_cons, Fin.cons_zero, Fin.cons_succ]

lemma prod_ofFn_smul : ∀ {p : ℕ} (s : Fin p → ℂ) (a : Fin p → 𝒰),
    (List.ofFn fun j => s j • a j).prod = (∏ j, s j) • (List.ofFn a).prod
  | 0, s, a => by simp
  | p + 1, s, a => by
    simp only [List.ofFn_succ, List.prod_cons]
    rw [prod_ofFn_smul (fun j => s j.succ) (fun j => a j.succ), Fin.prod_univ_succ, smul_mul_smul_comm]

lemma capEntry_ad (E : Fin n → Fin n → 𝒰) (P Q : Matrix (Fin n) (Fin n) ℂ) (hQP : Q * P = 1) (x : ℂ)
    (a b : Fin n) :
    capEntry (fun a b => ∑ c, ∑ d, (P c a * Q b d) • E c d) x a b =
      ∑ c, ∑ d, (P c a * Q b d) • capEntry E x c d := by
  simp only [capEntry, smul_add, Finset.sum_add_distrib]
  congr 1
  simp only [smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [← Finset.sum_smul]
  have h : ∑ c, P c a * Q b c = (Q * P) b a := by
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl (fun c _ => mul_comm _ _)
  rw [h, hQP, Matrix.one_apply]
  by_cases hab : a = b
  · subst hab; simp
  · rw [if_neg (Ne.symm hab), if_neg hab, zero_smul]

lemma coef_det (P : Matrix (Fin n) (Fin n) ℂ) (c : Fin n → Fin n) :
    ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤˣ) : ℤ) • ∏ j, P (c j) (σ j) = (P.submatrix c id).det := by
  rw [← Matrix.det_transpose, Matrix.det_apply]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [Units.smul_def]
  rfl

lemma sum_fun_perm {M : Type*} [AddCommMonoid M] (f : (Fin n → Fin n) → M)
    (hf : ∀ c, ¬ Function.Injective c → f c = 0) : ∑ c, f c = ∑ τ : Equiv.Perm (Fin n), f τ := by
  classical
  have himg : ∑ τ : Equiv.Perm (Fin n), f τ =
      ∑ c ∈ Finset.univ.image (fun τ : Equiv.Perm (Fin n) => (τ : Fin n → Fin n)), f c := by
    rw [Finset.sum_image]
    intro a _ b _ h
    exact Equiv.ext (congrFun h)
  rw [himg]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro c _ hc
  apply hf
  intro hinj
  apply hc
  rw [Finset.mem_image]
  exact ⟨Equiv.ofBijective c (Finite.injective_iff_bijective.1 hinj), Finset.mem_univ _, rfl⟩

theorem capelliC_ad (E : Fin n → Fin n → 𝒰) (hE : GlRelR E) (P Q : Matrix (Fin n) (Fin n) ℂ)
    (hQP : Q * P = 1) (hPQ : P * Q = 1) (x : ℂ) :
    capelliC (fun a b => ∑ c, ∑ d, (P c a * Q b d) • E c d) x = capelliC E x := by
  classical
  have hstep : ∀ σ : Equiv.Perm (Fin n),
      (List.ofFn fun j : Fin n =>
        capEntry (fun a b => ∑ c, ∑ d, (P c a * Q b d) • E c d) (x - ((j : ℕ) : ℂ)) (σ j) j).prod =
        ∑ γ : Fin n → Fin n × Fin n, (∏ j, (P (γ j).1 (σ j) * Q j (γ j).2)) •
          (List.ofFn fun j : Fin n => capEntry E (x - ((j : ℕ) : ℂ)) (γ j).1 (γ j).2).prod := by
    intro σ
    have h1 : ∀ j : Fin n, capEntry (fun a b => ∑ c, ∑ d, (P c a * Q b d) • E c d) (x - ((j : ℕ) : ℂ)) (σ j) j =
        ∑ cd : Fin n × Fin n, (P cd.1 (σ j) * Q j cd.2) • capEntry E (x - ((j : ℕ) : ℂ)) cd.1 cd.2 := by
      intro j
      rw [capEntry_ad E P Q hQP, Fintype.sum_prod_type]
    simp_rw [h1]
    rw [prod_ofFn_sum]
    exact Finset.sum_congr rfl (fun γ _ => prod_ofFn_smul _ _)
  have hdet : ∀ c : Fin n → Fin n, ¬ Function.Injective c → (P.submatrix c id).det = 0 := by
    intro c hc
    obtain ⟨i, j, hij, hne⟩ : ∃ i j, c i = c j ∧ i ≠ j := by
      by_contra h
      push_neg at h
      exact hc (fun i j hij => h i j hij)
    exact Matrix.det_zero_of_row_eq hne (by ext k; simp [hij])
  have hS : ∀ d : Fin n → Fin n,
      ∑ c : Fin n → Fin n, (P.submatrix c id).det •
        (List.ofFn fun j : Fin n => capEntry E (x - ((j : ℕ) : ℂ)) (c j) (d j)).prod =
        P.det • cminor E id d x := by
    intro d
    rw [sum_fun_perm _ (fun c hc => by rw [hdet c hc, zero_smul])]
    unfold cminor
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    rw [Matrix.det_permute, mul_comm, mul_smul, ← Int.cast_smul_eq_zsmul ℂ]
    simp only [id]
  have hQ : ∑ ρ : Equiv.Perm (Fin n), ((Equiv.Perm.sign ρ : ℤˣ) : ℤ) • ∏ j, Q j (ρ j) = Q.det := by
    have := coef_det Q id
    simpa using this
  calc capelliC (fun a b => ∑ c, ∑ d, (P c a * Q b d) • E c d) x
      = ∑ γ : Fin n → Fin n × Fin n,
          ((P.submatrix (fun j => (γ j).1) id).det * ∏ j, Q j (γ j).2) •
          (List.ofFn fun j : Fin n => capEntry E (x - ((j : ℕ) : ℂ)) (γ j).1 (γ j).2).prod := by
        unfold capelliC cminor
        simp only [id]
        simp_rw [hstep, Finset.smul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun γ _ => ?_)
        rw [← coef_det P (fun j => (γ j).1), Finset.sum_mul, Finset.sum_smul]
        refine Finset.sum_congr rfl (fun σ _ => ?_)
        rw [Finset.prod_mul_distrib, smul_mul_assoc, smul_assoc]
    _ = ∑ d : Fin n → Fin n, ∑ c : Fin n → Fin n,
          ((P.submatrix c id).det * ∏ j, Q j (d j)) •
          (List.ofFn fun j : Fin n => capEntry E (x - ((j : ℕ) : ℂ)) (c j) (d j)).prod := by
        let e : (Fin n → Fin n) × (Fin n → Fin n) ≃ (Fin n → Fin n × Fin n) :=
          ⟨fun cd j => (cd.1 j, cd.2 j), fun γ => (fun j => (γ j).1, fun j => (γ j).2),
            fun _ => rfl, fun _ => rfl⟩
        rw [← e.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
        rfl
    _ = ∑ d : Fin n → Fin n, (∏ j, Q j (d j)) • (P.det • cminor E id d x) := by
        refine Finset.sum_congr rfl (fun d _ => ?_)
        rw [← hS d, Finset.smul_sum]
        refine Finset.sum_congr rfl (fun c _ => ?_)
        rw [smul_smul, mul_comm]
    _ = ∑ ρ : Equiv.Perm (Fin n), (∏ j, Q j (ρ j)) • (P.det • cminor E id ρ x) := by
        apply sum_fun_perm
        intro d hd
        rw [cminor_cols_not_inj E hE id d x hd, smul_zero, smul_zero]
    _ = (P.det * Q.det) • capelliC E x := by
        rw [← hQ, Finset.mul_sum, Finset.sum_smul]
        refine Finset.sum_congr rfl (fun ρ _ => ?_)
        have hc := cminor_perm_cols E hE id id ρ x
        unfold capelliC
        rw [show (id : Fin n → Fin n) ∘ ρ = ρ from rfl] at hc
        rw [hc, smul_smul, ← Int.cast_smul_eq_zsmul ℂ, smul_smul]
        congr 1
        rw [zsmul_eq_mul]
        ring
    _ = capelliC E x := by
        rw [← Matrix.det_mul, hPQ, Matrix.det_one, one_smul]

end ReciprocityTheory.ChartRestriction.DS.S7.CapAd
end
end
