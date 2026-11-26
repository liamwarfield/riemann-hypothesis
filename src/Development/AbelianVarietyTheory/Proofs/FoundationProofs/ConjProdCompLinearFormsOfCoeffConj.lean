module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTraceCompatibleTorusEmbeddingStandardTorus
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalCoefficientChangeCompare

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConjProdCompLinearFormsOfCoeffConj
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConjProdCompLinearFormsOfCoeffConj
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ThetaConj.ProdLin

def CjN (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (x y : ℂ) : Prop := x ∈ M ∧ y = cj M ρ x

theorem CjN.add {M : IntermediateField ℚ ℂ} {ρ : M →ₐ[ℚ] ℂ} {x y x' y' : ℂ} (h : CjN M ρ x x')
    (h' : CjN M ρ y y') : CjN M ρ (x + y) (x' + y') :=
  ⟨add_mem h.1 h'.1, by rw [cj_add ρ h.1 h'.1, h.2, h'.2]⟩

theorem CjN.mul {M : IntermediateField ℚ ℂ} {ρ : M →ₐ[ℚ] ℂ} {x y x' y' : ℂ} (h : CjN M ρ x x')
    (h' : CjN M ρ y y') : CjN M ρ (x * y) (x' * y') :=
  ⟨mul_mem h.1 h'.1, by rw [cj_mul ρ h.1 h'.1, h.2, h'.2]⟩

theorem CjN.rat (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (q : ℚ) : CjN M ρ (q : ℂ) (q : ℂ) := by
  have h : (q : ℂ) ∈ M := SubfieldClass.ratCast_mem M q
  refine ⟨h, ?_⟩
  rw [cj_mem ρ h]
  have : (⟨(q : ℂ), h⟩ : M) = (q : M) := by apply Subtype.ext; simp
  rw [this, map_ratCast]

inductive Rel {E I : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (v : I → E)
    (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) : (E → ℂ) → (E → ℂ) → Prop
  | const (c c' : ℂ) : CjN M ρ c c' → Rel v M ρ (fun _ => c) (fun _ => c')
  | base (g g' : ℂ → ℂ) (L L' : E →L[ℂ] ℂ) : Differentiable ℂ g → Differentiable ℂ g' →
      (∀ n, CjN M ρ (iteratedDeriv n g 0) (iteratedDeriv n g' 0)) →
      (∀ k, CjN M ρ (L (v k)) (L' (v k))) → Rel v M ρ (fun z => g (L z)) (fun z => g' (L' z))
  | add (F F' G G' : E → ℂ) : Rel v M ρ F F' → Rel v M ρ G G' →
      Rel v M ρ (fun z => F z + G z) (fun z => F' z + G' z)
  | mul (F F' G G' : E → ℂ) : Rel v M ρ F F' → Rel v M ρ G G' →
      Rel v M ρ (fun z => F z * G z) (fun z => F' z * G' z)

variable {E I : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {v : I → E}
  {M : IntermediateField ℚ ℂ} {ρ : M →ₐ[ℚ] ℂ}

theorem Rel.contDiff {F F' : E → ℂ} (h : Rel v M ρ F F') :
    ContDiff ℂ ⊤ F ∧ ContDiff ℂ ⊤ F' := by
  induction h with
  | const c c' _ => exact ⟨contDiff_const, contDiff_const⟩
  | base g g' L L' hg hg' _ _ => exact ⟨hg.contDiff.comp L.contDiff, hg'.contDiff.comp L'.contDiff⟩
  | add F F' G G' _ _ h1 h2 => exact ⟨h1.1.add h2.1, h1.2.add h2.2⟩
  | mul F F' G G' _ _ h1 h2 => exact ⟨h1.1.mul h2.1, h1.2.mul h2.2⟩

theorem Rel.diff {F F' : E → ℂ} (h : Rel v M ρ F F') :
    Differentiable ℂ F ∧ Differentiable ℂ F' :=
  ⟨h.contDiff.1.differentiable (by simp), h.contDiff.2.differentiable (by simp)⟩

theorem Rel.at_zero {F F' : E → ℂ} (h : Rel v M ρ F F') : CjN M ρ (F 0) (F' 0) := by
  induction h with
  | const c c' h => exact h
  | base g g' L L' _ _ h _ => simpa using h 0
  | add F F' G G' _ _ h1 h2 => exact h1.add h2
  | mul F F' G G' _ _ h1 h2 => exact h1.mul h2

theorem fderiv_base {g : ℂ → ℂ} (hg : Differentiable ℂ g) (L : E →L[ℂ] ℂ) (w : E) :
    (fun z => fderiv ℂ (fun z => g (L z)) z w) = fun z => L w * deriv g (L z) := by
  funext z
  have := ((hg (L z)).hasDerivAt.comp_hasFDerivAt z L.hasFDerivAt).fderiv
  change fderiv ℂ (g ∘ L) z w = _
  rw [this]; simp [mul_comm]

theorem fderiv_add' {F G : E → ℂ} (hF : Differentiable ℂ F) (hG : Differentiable ℂ G) (w : E) :
    (fun z => fderiv ℂ (fun z => F z + G z) z w) = fun z => fderiv ℂ F z w + fderiv ℂ G z w := by
  funext z
  rw [fderiv_fun_add (hF z) (hG z)]; simp

theorem fderiv_mul' {F G : E → ℂ} (hF : Differentiable ℂ F) (hG : Differentiable ℂ G) (w : E) :
    (fun z => fderiv ℂ (fun z => F z * G z) z w) =
      fun z => F z * fderiv ℂ G z w + G z * fderiv ℂ F z w := by
  funext z
  rw [fderiv_fun_mul (hF z) (hG z)]; simp

theorem Rel.fderiv {F F' : E → ℂ} (h : Rel v M ρ F F') (k : I) :
    Rel v M ρ (fun z => fderiv ℂ F z (v k)) (fun z => fderiv ℂ F' z (v k)) := by
  induction h with
  | const c c' h =>
    have := Rel.const (v := v) _ _ (CjN.rat M ρ 0)
    simpa using this
  | base g g' L L' hg hg' h hL =>
    rw [fderiv_base hg, fderiv_base hg']
    refine Rel.mul _ _ _ _ (Rel.const _ _ (hL k))
      (Rel.base (deriv g) (deriv g') L L' hg.deriv hg'.deriv (fun n => ?_) hL)
    rw [← iteratedDeriv_succ', ← iteratedDeriv_succ']
    exact h (n + 1)
  | add F F' G G' hF hG h1 h2 =>
    rw [fderiv_add' hF.diff.1 hG.diff.1, fderiv_add' hF.diff.2 hG.diff.2]
    exact Rel.add _ _ _ _ h1 h2
  | mul F F' G G' hF hG h1 h2 =>
    rw [fderiv_mul' hF.diff.1 hG.diff.1, fderiv_mul' hF.diff.2 hG.diff.2]
    exact Rel.add _ _ _ _ (Rel.mul _ _ _ _ hF h2) (Rel.mul _ _ _ _ hG h1)

theorem iteratedFDeriv_step {F : E → ℂ} (hF : ContDiff ℂ ⊤ F) (n : ℕ) (m : Fin (n + 1) → E) :
    iteratedFDeriv ℂ (n + 1) F 0 m =
      iteratedFDeriv ℂ n (fun z => fderiv ℂ F z (m (Fin.last n))) 0 (Fin.init m) := by
  rw [iteratedFDeriv_succ_apply_right,
    iteratedFDeriv_clm_apply_const_apply (n := ⊤) (hF.fderiv_right (m := ⊤) le_top) le_top]

theorem Rel.iterated (n : ℕ) : ∀ {F F' : E → ℂ}, Rel v M ρ F F' → ∀ k : Fin n → I,
    CjN M ρ (iteratedFDeriv ℂ n F 0 fun i => v (k i)) (iteratedFDeriv ℂ n F' 0 fun i => v (k i)) := by
  induction n with
  | zero => intro F F' h k; simpa using h.at_zero
  | succ n ih =>
    intro F F' h k
    rw [iteratedFDeriv_step h.contDiff.1, iteratedFDeriv_step h.contDiff.2]
    exact ih (h.fderiv (k (Fin.last n))) (Fin.init k)

theorem Rel.prod {ι : Type} (s : Finset ι) {F F' : ι → E → ℂ} (h : ∀ i, Rel v M ρ (F i) (F' i)) :
    Rel v M ρ (fun z => ∏ i ∈ s, F i z) (fun z => ∏ i ∈ s, F' i z) := by
  induction s using Finset.induction_on with
  | empty =>
    have := Rel.const (v := v) _ _ (CjN.rat M ρ 1)
    simpa using this
  | insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact Rel.mul _ _ _ _ (h i) ih

theorem Rel.cjF {D : D7} {N N' : ℕ} {F F' : VC D N N' → ℂ} (h : Rel (coordV D) M ρ F F') :
    CjF D M ρ F F' := by
  refine ⟨h.diff.1, h.diff.2, fun α => ?_⟩
  have h1 := (Rel.iterated _ h (fun i : Fin (Multiset.card α.toMultiset) =>
    α.toMultiset.toList.get ⟨i, by rw [Multiset.length_toList]; exact i.2⟩)).mul
      (CjN.rat M ρ (α.prod fun _ n => (n.factorial : ℚ))⁻¹)
  have h2 : (((α.prod fun _ n => (n.factorial : ℚ))⁻¹ : ℚ) : ℂ) =
      (α.prod fun _ n => (n.factorial : ℂ))⁻¹ := by
    simp [Finsupp.prod]
  rw [h2] at h1
  unfold taylor
  simp only [div_eq_mul_inv]
  exact h1

def linF (D : D7) {N N' : ℕ} (l : VC D N N') : VC D N N' →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => ∑ τ, ∑ a, ∑ c, z τ a c * l τ a c
      map_add' := fun x y => by simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun c x => by simp [Finset.mul_sum, mul_assoc] }

theorem linF_apply (D : D7) {N N' : ℕ} (l z : VC D N N') :
    linF D l z = ∑ τ, ∑ a, ∑ c, z τ a c * l τ a c := rfl

theorem linF_coordV (D : D7) {N N' : ℕ} (l : VC D N N') (k : D.what₂.Tau × Fin N' × Fin N) :
    linF D l (coordV D k) = l k.1 k.2.1 k.2.2 := by
  rw [linF_apply]
  simp [coordV, ite_and]

theorem cjF_prod : ∀ (D : D7) (N N' r : ℕ) (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ)
    (g g' : Fin r → ℂ → ℂ) (l l' : Fin r → VC D N N'), (∀ j, Differentiable ℂ (g j)) →
    (∀ j, Differentiable ℂ (g' j)) →
    (∀ j n, coef1 (g j) n ∈ M ∧ coef1 (g' j) n = cj M ρ (coef1 (g j) n)) →
    (∀ j τ a c, l j τ a c ∈ M ∧ l' j τ a c = cj M ρ (l j τ a c)) →
    CjF D M ρ (fun z : VC D N N' => ∏ j, g j (∑ τ, ∑ a, ∑ c, z τ a c * l j τ a c))
      (fun z : VC D N N' => ∏ j, g' j (∑ τ, ∑ a, ∑ c, z τ a c * l' j τ a c)) := by
  intro D N N' r M ρ g g' l l' hg hg' hc hl
  refine Rel.cjF (Rel.prod Finset.univ fun j =>
    Rel.base (g j) (g' j) (linF D (l j)) (linF D (l' j)) (hg j) (hg' j) (fun n => ?_) fun k => ?_)
  · have h1 := CjN.mul (hc j n) (CjN.rat M ρ (n.factorial : ℚ))
    have h0 : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    simpa only [coef1, Rat.cast_natCast, div_mul_cancel₀ _ h0] using h1
  · rw [linF_coordV, linF_coordV]; exact hl j _ _ _

end GlobalTheory.ThetaConj.ProdLin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConjProdCompLinearFormsOfCoeffConjStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_prod_comp_linearForms_of_coeff_conj : ∀ (D : D7) (N N' r : ℕ) (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (g g' : Fin r → ℂ → ℂ) (l l' : Fin r → VC D N N'), (∀ j, Differentiable ℂ (g j)) → (∀ j, Differentiable ℂ (g' j)) → (∀ j n, coef1 (g j) n ∈ M ∧ coef1 (g' j) n = cj M ρ (coef1 (g j) n)) → (∀ j τ a c, l j τ a c ∈ M ∧ l' j τ a c = cj M ρ (l j τ a c)) → CjF D M ρ (fun z : VC D N N' => ∏ j, g j (∑ τ, ∑ a, ∑ c, z τ a c * l j τ a c)) (fun z : VC D N N' => ∏ j, g' j (∑ τ, ∑ a, ∑ c, z τ a c * l' j τ a c)) := by
  first | exact @GlobalTheory.ThetaConj.ProdLin.cjF_prod | exact GlobalTheory.ThetaConj.ProdLin.cjF_prod | (intros; apply GlobalTheory.ThetaConj.ProdLin.cjF_prod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KTypesUnitaryLowestWeightInCone
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KTypesUnitaryLowestWeightInCone
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.LowestCone

variable {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

lemma mem_wt {act : Mat p q →ₗ[ℂ] Module.End ℂ V} {μ : Ix p q → ℚ} {v : V} :
    v ∈ wtSub act μ ↔ ∀ a, act (Eab a a) v = ((μ a : ℚ) : ℂ) • v := by
  simp [wtSub, Submodule.mem_iInf, sub_eq_zero]

lemma mem_hw {act : Mat p q →ₗ[ℂ] Module.End ℂ V} {μ : Ix p q → ℚ} {v : V} :
    v ∈ hwSub act μ ↔ v ∈ wtSub act μ ∧ ∀ a b, posC a b → act (Eab a b) v = 0 := by
  simp [hwSub, Submodule.mem_iInf]

lemma Eab_mul (a b c d : Ix p q) :
    (Eab a b : Mat p q) * Eab c d = (if b = c then (1 : ℂ) else 0) • Eab a d := by
  split_ifs with h
  · subst h; simp [Eab]
  · simp [Eab, Matrix.single_mul_single_of_ne, h]

lemma lie_Eab {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (hL : IsLieAct act) (a b c d : Ix p q) (y : V) :
    act (Eab a b) (act (Eab c d) y) = act (Eab c d) (act (Eab a b) y) +
      ((if b = c then (1 : ℂ) else 0) • act (Eab a d) y -
        (if d = a then (1 : ℂ) else 0) • act (Eab c b) y) := by
  have := congrArg (fun f => f y) (hL (Eab a b) (Eab c d))
  simp only [Eab_mul, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.mul_apply] at this
  rw [this]; abel

lemma wt_shift {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (hL : IsLieAct act) (a b : Ix p q)
    {ν : Ix p q → ℚ} {y : V} (hy : y ∈ wtSub act ν) :
    act (Eab a b) y ∈ wtSub act
      (fun c => ν c + ((if c = a then 1 else 0) - (if c = b then 1 else 0))) := by
  rw [mem_wt] at hy ⊢
  intro c
  rw [lie_Eab hL, hy, map_smul]
  by_cases h1 : c = a <;> by_cases h2 : c = b
  · subst h1; subst h2; simp
  · subst h1; simp [h2, Ne.symm h2, add_smul]
  · subst h2; simp [h1, sub_eq_add_neg, add_smul]
  · simp [h1, h2, Ne.symm h2]

def InCone (ν μ : Ix p q → ℚ) : Prop :=
  ∃ m : Ix p q → Ix p q → ℕ, (∀ a b, m a b ≠ 0 → ∃ i j, a = Sum.inl i ∧ b = Sum.inr j) ∧
    μ = fun c => ν c + ∑ a, ∑ b, (m a b : ℚ) * ((if c = a then 1 else 0) - (if c = b then 1 else 0))

lemma inCone_self (μ : Ix p q → ℚ) : InCone μ μ :=
  ⟨fun _ _ => 0, by simp, by simp⟩

lemma inCone_step {ν μ : Ix p q → ℚ} (h : InCone ν μ) (i : Fin p) (j : Fin q) :
    InCone (fun c => ν c + ((if c = Sum.inr j then 1 else 0) - (if c = Sum.inl i then 1 else 0))) μ := by
  obtain ⟨m, hm, rfl⟩ := h
  refine ⟨fun a b => m a b + if a = Sum.inl i then (if b = Sum.inr j then 1 else 0) else 0, ?_, ?_⟩
  · intro a b hab
    by_cases h0 : m a b = 0
    · by_cases h1 : a = Sum.inl i
      · by_cases h2 : b = Sum.inr j
        · exact ⟨i, j, h1, h2⟩
        · simp [h0, h2] at hab
      · simp [h0, h1] at hab
    · exact hm a b h0
  · funext c
    have key : ∑ a : Ix p q, ∑ b : Ix p q,
        (((if a = Sum.inl i then (if b = Sum.inr j then 1 else 0) else 0 : ℕ)) : ℚ) *
          ((if c = a then 1 else 0) - (if c = b then 1 else 0)) =
        (if c = Sum.inl i then 1 else 0) - (if c = Sum.inr j then 1 else 0) := by
      rw [Finset.sum_eq_single (Sum.inl i), Finset.sum_eq_single (Sum.inr j)]
      · simp
      · intro b _ hb; simp [hb]
      · simp
      · intro b _ hb; simp [hb]
      · simp
    simp only [Nat.cast_add, add_mul, Finset.sum_add_distrib, key]
    ring

lemma act_mem {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (N : Submodule ℂ V) (y : V)
    (h : ∀ a b, act (Eab a b) y ∈ N) (Z : Mat p q) : act Z y ∈ N := by
  rw [Matrix.matrix_eq_sum_single Z]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.sum_apply]
  refine N.sum_mem fun a _ => N.sum_mem fun b _ => ?_
  have : (Matrix.single a b (Z a b) : Mat p q) = Z a b • Eab a b := by
    rw [Eab, Matrix.smul_single, smul_eq_mul, mul_one]
  rw [this, map_smul, LinearMap.smul_apply]
  exact N.smul_mem _ (h a b)

lemma exists_down {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (hL : IsLieAct act) {μ : Ix p q → ℚ} {v : V}
    (hv : v ∈ hwSub act μ) : ∃ D : Submodule ℂ V, v ∈ D ∧
      (∀ i j, ∀ x ∈ D, act (Eab (Sum.inr j) (Sum.inl i)) x ∈ D) ∧
      (∀ a b, posC a b → ∀ x ∈ D, act (Eab a b) x ∈ D) ∧
      D ≤ ⨆ ν : {ν // InCone ν μ}, wtSub act ν.1 := by
  rw [mem_hw] at hv
  set S : Set (Submodule ℂ V) :=
    {N | v ∈ N ∧ ∀ i j, ∀ x ∈ N, act (Eab (Sum.inr j) (Sum.inl i)) x ∈ N} with hS
  have hG : sInf S ∈ S := by
    refine ⟨Submodule.mem_sInf.2 fun M hM => hM.1, fun a b y hy => ?_⟩
    exact Submodule.mem_sInf.2 fun M hM => hM.2 a b y (Submodule.mem_sInf.1 hy M hM)
  refine ⟨sInf S, hG.1, hG.2, fun a b hab x hx => ?_, sInf_le ⟨?_, fun i j x hx => ?_⟩⟩
  · have hG' : (sInf S ⊓ (sInf S).comap (act (Eab a b))) ∈ S := by
      refine ⟨⟨hG.1, ?_⟩, fun i j y hy => ⟨hG.2 i j y hy.1, ?_⟩⟩
      · show act (Eab a b) v ∈ sInf S
        rw [hv.2 a b hab]; exact Submodule.zero_mem _
      · show act (Eab a b) (act _ y) ∈ sInf S
        rw [lie_Eab hL]
        refine Submodule.add_mem _ (hG.2 i j _ hy.2) ?_
        rcases a with a | a <;> rcases b with b | b
        · refine Submodule.sub_mem _ (by simp) (Submodule.smul_mem _ _ (hG.2 _ _ _ hy.1))
        · exact absurd hab (by simp [posC])
        · exact absurd hab (by simp [posC])
        · refine Submodule.sub_mem _ (Submodule.smul_mem _ _ (hG.2 _ _ _ hy.1)) (by simp)
    exact (sInf_le hG' hx).2
  · exact Submodule.mem_iSup_of_mem (⟨μ, inCone_self μ⟩ : {ν // InCone ν μ}) hv.1
  · refine Submodule.iSup_induction _ (motive := fun x => act (Eab (Sum.inr j) (Sum.inl i)) x ∈
      ⨆ ν : {ν // InCone ν μ}, wtSub act ν.1) hx ?_ (by simp) ?_
    · intro ν y hy
      exact Submodule.mem_iSup_of_mem (⟨_, inCone_step ν.2 i j⟩ : {ν // InCone ν μ})
        (wt_shift hL _ _ hy)
    · intro y z hy hz
      rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz

lemma wt_orth {act : Mat p q →ₗ[ℂ] Module.End ℂ V} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (E : V →ₗ[ℂ] H)
    (hadj : ∀ Z x y, inner ℂ (E (act Z x)) (E y) = inner ℂ (E x) (E (act (adjZ Z) y)))
    {ν Λ : Ix p q → ℚ} (hne : ν ≠ Λ) {x e : V} (hx : x ∈ wtSub act ν) (he : e ∈ wtSub act Λ) :
    inner ℂ (E x) (E e) = 0 := by
  obtain ⟨c, hc⟩ := Function.ne_iff.1 hne
  have h := hadj (Eab c c) x e
  rw [GlobalTheory.FockTensor.adjZ_Eab, GlobalTheory.FockTensor.sgnIx_mul_self, one_smul, mem_wt.1 hx, mem_wt.1 he,
    map_smul, map_smul, inner_smul_left, inner_smul_right, map_ratCast, ← sub_eq_zero,
    ← sub_mul] at h
  refine (mul_eq_zero.1 h).resolve_left fun h0 => hc ?_
  exact_mod_cast sub_eq_zero.1 h0

theorem cone : ∀ (p q : ℕ) (M : GKMod p q) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (E : M.V →ₗ[ℂ] H), Function.Injective E → (∀ Z x y, inner ℂ (E (M.act Z x)) (E y) = inner ℂ (E x) (E (M.act (adjZ Z) y))) → ∀ (Λ : Ix p q → ℚ) (e : M.V), e ∈ hwSub M.act Λ → KilledByLower M.act e → genSub M.act {e} = ⊤ → ∀ (μ : Ix p q → ℚ) (v : M.V), IsHW M.act μ v → ∃ m : Ix p q → Ix p q → ℕ, (∀ a b, m a b ≠ 0 → ∃ i j, a = Sum.inl i ∧ b = Sum.inr j) ∧ μ = fun c => Λ c + ∑ a, ∑ b, (m a b : ℚ) * ((if c = a then 1 else 0) - (if c = b then 1 else 0)) := by
  intro p q M H _ _ E hE hadj Λ e he hlow hgen μ v hv
  by_contra hcone
  change ¬ InCone Λ μ at hcone
  obtain ⟨D, hvD, hDm, hDp, hDle⟩ := exists_down M.lie hv.2
  rw [mem_hw] at he
  let C : Submodule ℂ M.V := ((D.map E)ᗮ).comap E
  have hC : ∀ x, x ∈ C ↔ ∀ d ∈ D, inner ℂ (E d) (E x) = 0 := by
    intro x
    simp only [C, Submodule.mem_comap, Submodule.mem_orthogonal]
    constructor
    · intro h d hd; exact h _ ⟨d, hd, rfl⟩
    · rintro h _ ⟨d, hd, rfl⟩; exact h d hd
  have hstab : ∀ a b, (∀ d ∈ D, M.act (Eab a b) d ∈ D) → ∀ x ∈ C, M.act (Eab b a) x ∈ C := by
    intro a b h x hx
    rw [hC] at hx ⊢
    intro d hd
    have := hadj (adjZ (Eab b a)) d x
    rw [GlobalTheory.FockTensor.adjZ_adjZ] at this
    rw [← this, GlobalTheory.FockTensor.adjZ_Eab, map_smul, LinearMap.smul_apply]
    exact hx _ (D.smul_mem _ (h d hd))
  have heC : e ∈ C := by
    rw [hC]
    intro d hd
    refine Submodule.iSup_induction _ (motive := fun x => inner ℂ (E x) (E e) = 0) (hDle hd) ?_
      (by simp) ?_
    · intro ν y hy
      exact wt_orth E hadj (fun h : ν.1 = Λ => hcone (h ▸ ν.2)) hy he.1
    · intro y z hy hz
      rw [map_add (f := _), inner_add_left, hy, hz, add_zero]
  let r : Ix p q → ℕ := Sum.elim (fun i => q + i.1) (fun j => j.1)
  have hr : Function.Injective r := by
    rintro (a | a) (b | b) h <;> simp only [r, Sum.elim_inl, Sum.elim_inr] at h
    · congr 1; ext; omega
    · have := b.2; omega
    · have := a.2; omega
    · congr 1; ext; omega
  have hcase : ∀ a b, r a < r b → posC a b ∨ ∃ i j, a = Sum.inr j ∧ b = Sum.inl i := by
    rintro (a | a) (b | b) h <;> simp only [r, Sum.elim_inl, Sum.elim_inr] at h
    · left; show a < b; rw [Fin.lt_def]; omega
    · have := b.2; omega
    · exact Or.inr ⟨_, _, rfl, rfl⟩
    · left; exact h
  obtain ⟨U, heU, hU, hUmin, -⟩ := GlobalTheory.ExtremalGen.exists_generated p q M.V M.act M.lie (fun _ _ => True)
    ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩ r hr Λ e he.1 (by
      intro a b _ h
      rcases hcase a b h with h | ⟨i, j, rfl, rfl⟩
      · exact he.2 a b h
      · exact hlow i j)
  have hUC : U ≤ C := hUmin C heC (by
    intro a b _ h
    refine hstab a b ?_
    rcases hcase a b h with h | ⟨i, j, rfl, rfl⟩
    · exact hDp a b h
    · exact hDm i j)
  have hgU : genSub M.act {e} ≤ U :=
    sInf_le ⟨by simpa using heU, fun Z y hy => act_mem U y (fun a b => hU a b trivial y hy) Z⟩
  have hvC : v ∈ C := hUC (hgU (hgen ▸ Submodule.mem_top))
  have h0 := (hC v).1 hvC v hvD
  rw [inner_self_eq_zero] at h0
  exact hv.1 (hE (by rw [h0, map_zero]))

end GlobalTheory.LowestCone
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KTypesUnitaryLowestWeightInConeStatement
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kTypes_unitary_lowestWeight_in_cone : ∀ (p q : ℕ) (M : GKMod p q) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (E : M.V →ₗ[ℂ] H), Function.Injective E → (∀ Z x y, inner ℂ (E (M.act Z x)) (E y) = inner ℂ (E x) (E (M.act (adjZ Z) y))) → ∀ (Λ : Ix p q → ℚ) (e : M.V), e ∈ hwSub M.act Λ → KilledByLower M.act e → genSub M.act {e} = ⊤ → ∀ (μ : Ix p q → ℚ) (v : M.V), IsHW M.act μ v → ∃ m : Ix p q → Ix p q → ℕ, (∀ a b, m a b ≠ 0 → ∃ i j, a = Sum.inl i ∧ b = Sum.inr j) ∧ μ = fun c => Λ c + ∑ a, ∑ b, (m a b : ℚ) * ((if c = a then 1 else 0) - (if c = b then 1 else 0)) := by
  first | exact @GlobalTheory.LowestCone.cone | exact GlobalTheory.LowestCone.cone | (intros; apply GlobalTheory.LowestCone.cone <;> assumption)
end
end
