module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EquivariantMapCarriesGelfandInvariantToFunction

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JointHighestProportional
noncomputable section

open MvPolynomial GlobalTheory.Capelli GlobalTheory.Harm GlobalTheory.Harm.HighestUnique

namespace GlobalTheory.DefLift.Joint

theorem X_mul_pderiv_mem {σ : Type} (u v : σ) (N : ℕ) (Q : MvPolynomial σ ℂ)
    (hQ : Q ∈ restrictTotalDegree σ ℂ N) : X u * pderiv v Q ∈ restrictTotalDegree σ ℂ N := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Q.as_sum, map_sum, Finset.mul_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  rw [mem_restrictTotalDegree] at hQ ⊢
  have hd : (m.sum fun _ e => e) ≤ N := (le_totalDegree hm).trans hQ
  rw [pderiv_monomial]
  by_cases h : m v = 0
  · simp [h]
  · rw [X, monomial_mul]
    refine (totalDegree_monomial_le _ _).trans (le_trans (le_of_eq ?_) hd)
    have h1 : Finsupp.single v 1 ≤ m := by
      rw [Finsupp.single_le_iff]; omega
    have h2 : m = Finsupp.single v 1 + (m - Finsupp.single v 1) := (add_tsub_cancel_of_le h1).symm
    conv_rhs => rw [h2]
    rw [Finsupp.sum_add_index' (by simp) (by simp), Finsupp.sum_add_index' (by simp) (by simp)]
    simp
    rfl

theorem antitone_rowOp {σ J : Type} [Fintype σ] [Fintype J] {p : ℕ} (z : Fin p × J → σ)
    (hz : Function.Injective z) {P : MvPolynomial σ ℂ} (hP : P ≠ 0) (μ : Fin p → ℤ)
    (hup : ∀ a b, a < b → ∑ k, X (z (a, k)) * pderiv (z (b, k)) P = 0)
    (hwt : ∀ a, ∑ k, X (z (a, k)) * pderiv (z (a, k)) P = (μ a : ℂ) • P) : Antitone μ :=
  highest_weight_antitone (rowOp ℂ z) (rowOp_lie z hz) (restrictTotalDegree σ ℂ P.totalDegree)
    (fun i j w hw => by
      rw [rowOp_apply]
      exact Submodule.sum_mem _ fun _ _ => X_mul_pderiv_mem _ _ _ _ hw)
    P ((mem_restrictTotalDegree _ _ _).2 le_rfl) hP μ
    (fun a b h => (rowOp_apply _ _ _ _).trans (hup a b h))
    (fun a => (rowOp_apply _ _ _ _).trans (hwt a))

theorem degree_of_mem_support {σ J : Type} [Fintype J] (z : J → σ) {P : MvPolynomial σ ℂ} {w : ℤ}
    (h : ∑ k, X (z k) * pderiv (z k) P = (w : ℂ) • P) {m : σ →₀ ℕ} (hm : m ∈ P.support) :
    ((∑ k, m (z k) : ℕ) : ℤ) = w := by
  have := congrArg (AddMonoidAlgebra.coeff · m) h
  rw [coeff_sum, coeff_smul] at this
  simp only [coeff_X_mul_pderiv, ← Finset.sum_mul, smul_eq_mul] at this
  have h2 := mul_right_cancel₀ (mem_support_iff.1 hm) this
  exact_mod_cast h2

theorem exists_eq_smul_base {T : Type} [Fintype T] {p n : ℕ} (h : p + 0 ≤ n)
    {P : Poly ℂ T p 0 (Fin n)} (hP : P ≠ 0) (κ : T → Fin n → ℤ) (μ : T → Fin p → ℤ)
    (hup : ∀ t k l, k < l → ∑ a, X (xVar t a k) * pderiv (xVar t a l) P = 0)
    (hwt : ∀ t k, ∑ a, X (xVar t a k) * pderiv (xVar t a k) P = (κ t k : ℂ) • P)
    (hup' : ∀ t a b, a < b → ∑ k, X (xVar t a k) * pderiv (xVar t b k) P = 0)
    (hwt' : ∀ t a, ∑ k, X (xVar t a k) * pderiv (xVar t a k) P = (μ t a : ℂ) • P) :
    ∃ r : ℂ, P = r • basePoly ℂ h (fun t => diffOf fun a : Fin p => (κ t (Fin.castLE (n := p) h a)).toNat)
      (fun _ _ => 0) := by
  classical
  let z : T → Fin p × Fin n → Var T p 0 (Fin n) := fun t w => xVar t w.1 w.2
  let y : T → Fin 0 × Fin n → Var T p 0 (Fin n) := fun t w => yVar t w.1 w.2
  have hz : ∀ t, Function.Injective (z t) := fun t u w e => by simpa [z, Prod.ext_iff] using e
  have hy : ∀ t, Function.Injective (y t) := fun t u w e => u.1.elim0
  have hzy : ∀ t u w, z t u ≠ y t w := fun t u w => w.1.elim0
  have hμ : ∀ t, Antitone (μ t) := fun t => antitone_rowOp (z t) (hz t) hP _ (hup' t) (hwt' t)
  have hκ : ∀ t, Antitone (κ t) := fun t =>
    antitone_rowOp (fun w : Fin n × Fin p => z t w.swap) ((hz t).comp Prod.swap_injective) hP _
      (hup t) (hwt t)
  let a : T → Fin p → ℕ := fun t i => (μ t i).toNat
  have ha : ∀ t, Antitone (a t) := fun t i j hij => Int.toNat_le_toNat (hμ t hij)
  have hdeg : ∀ t i, ∀ m ∈ P.support, ∑ k, m (xVar t i k) = a t i := fun t i m hm => by
    have := degree_of_mem_support (fun k => xVar t i k) (hwt' t i) hm
    simp only [a]
    omega
  have hinv : ∀ t (i j : Fin p), i < j → ∀ s : ℂ,
      bind₁ (fun v => X v + ∑ k, if v = z t (j, k) then C s * X (z t (i, k)) else 0) P = P :=
    fun t i j hij => ((rowAdd_invariant_iff (fun k => z t (i, k)) (fun k => z t (j, k))
      (fun k l e => by simpa using hz t e)
      (fun k l e => hij.ne (congrArg Prod.fst (hz t e))) P).out 3 2).1 (hup' t i j hij)
  have hw : ∀ t, κ t = mixedWeight n (a t) (fun _ : Fin 0 => 0) := fun t =>
    weight_eq_mixedWeight h (z t) (hz t) (y t) (hy t) (hzy t) (a t) _ (ha t) (fun i => i.elim0)
      (hdeg t) (fun i => i.elim0) (hinv t) (fun i => i.elim0) (fun _ i => i.elim0) (κ t) (hκ t)
      (fun k l hkl => by rw [mixedOp_apply]; simpa using hup t k l hkl)
      (fun k => by rw [mixedOp_apply]; simpa using hwt t k) hP
  have e : (fun t => diffOf fun i : Fin p => (κ t (Fin.castLE (n := p) h i)).toNat) = fun t => diffOf (a t) := by
    funext t
    congr 1
    funext i
    rw [hw t, mixedWeight_apply]
    simp
  rw [e]
  refine exists_eq_smul_basePoly h _ _ ?_ κ hκ (fun t k l hkl => by simpa using hup t k l hkl)
    fun t k => by simpa using hwt t k
  refine mem_rowHighest_iff_of_charZero.2 ⟨fun _ _ b => b.elim0, fun t i m hm => ?_,
    fun _ b => b.elim0, fun t i j hij s => ?_, fun _ b => b.elim0⟩
  · rw [partOf_diffOf (ha t)]; exact hdeg t i m hm
  · rw [rowAddX_eq_bind₁]; exact hinv t i j hij s

end GlobalTheory.DefLift.Joint

namespace GlobalTheory.DefLift

theorem joint_highest_proportional (ι : Type) [Fintype ι] (m n : ℕ) (hnm : n ≤ m) (P Q : Pol ι m n)
    (κ : ι → Fin m → ℤ) (μ μ' : ι → Fin n → ℤ) (hP : P ≠ 0)
    (h1 : ∀ τ k l, k < l → rowLie n τ k l P = 0 ∧ rowLie n τ k l Q = 0)
    (h2 : ∀ τ k, rowLie n τ k k P = (κ τ k : ℂ) • P ∧ rowLie n τ k k Q = (κ τ k : ℂ) • Q)
    (h3 : ∀ τ k l, k < l → colLie m τ k l P = 0 ∧ colLie m τ k l Q = 0)
    (h4 : ∀ τ k, colLie m τ k k P = (μ τ k : ℂ) • P ∧ colLie m τ k k Q = (μ' τ k : ℂ) • Q) :
    ∃ r : ℂ, Q = r • P := by
  by_cases hQ : Q = 0
  · exact ⟨0, by simp [hQ]⟩
  let f : ι × Fin m × Fin n → Var ι n 0 (Fin m) := fun v => xVar v.1 v.2.2 v.2.1
  have hf : Function.Injective f := fun u w e => by
    simp only [f, Prod.ext_iff, Sum.inl.injEq] at e
    exact Prod.ext e.1 (Prod.ext e.2.2 e.2.1)
  have hr : ∀ τ k l (R : Pol ι m n), rename f (rowLie n τ k l R) =
      ∑ a, X (xVar τ a k) * pderiv (xVar τ a l) (rename f R) := fun τ k l R => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [rowLie_apply, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_mul, rename_X, ← pderiv_rename hf]
  have hc : ∀ τ k l (R : Pol ι m n), rename f (colLie m τ k l R) =
      ∑ a, X (xVar τ k a) * pderiv (xVar τ l a) (rename f R) := fun τ k l R => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [colLie_apply, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_mul, rename_X, ← pderiv_rename hf]
  have hi := rename_injective (R := ℂ) f hf
  obtain ⟨r, er⟩ := Joint.exists_eq_smul_base (show n + 0 ≤ m from hnm)
    ((map_ne_zero_iff _ hi).2 hP) κ μ
    (fun t k l h => by rw [← hr, (h1 t k l h).1, map_zero])
    (fun t k => by rw [← hr, (h2 t k).1, map_smul])
    (fun t k l h => by rw [← hc, (h3 t k l h).1, map_zero])
    (fun t k => by rw [← hc, (h4 t k).1, map_smul])
  obtain ⟨s, es⟩ := Joint.exists_eq_smul_base (show n + 0 ≤ m from hnm)
    ((map_ne_zero_iff _ hi).2 hQ) κ μ'
    (fun t k l h => by rw [← hr, (h1 t k l h).2, map_zero])
    (fun t k => by rw [← hr, (h2 t k).2, map_smul])
    (fun t k l h => by rw [← hc, (h3 t k l h).2, map_zero])
    (fun t k => by rw [← hc, (h4 t k).2, map_smul])
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hP (hi (by rw [er, zero_smul, map_zero]))
  refine ⟨s / r, hi ?_⟩
  rw [map_smul, er, es, smul_smul, div_mul_cancel₀ _ hr0]

end GlobalTheory.DefLift

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnHighestRowIntertwinersProportional
noncomputable section

open MvPolynomial

namespace GlobalTheory.DefLift

variable {ι : Type} {m n : ℕ}

def rowDer (n : ℕ) (τ : ι) (k l : Fin m) : Derivation ℂ (Pol ι m n) (Pol ι m n) :=
  ∑ c : Fin n, (X (τ, k, c) : Pol ι m n) • pderiv (τ, l, c)

theorem rowDer_apply (τ : ι) (k l : Fin m) (P : Pol ι m n) :
    rowDer n τ k l P = rowLie n τ k l P := by
  rw [rowLie_apply, rowDer]
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Derivation.add_apply, ih]; simp

open Classical in
theorem rowLie_X (τ : ι) (k l : Fin m) (v : ι × Fin m × Fin n) :
    rowLie n τ k l (X v) = if v.1 = τ ∧ v.2.1 = l then X (τ, k, v.2.2) else 0 := by
  obtain ⟨t, i, c⟩ := v
  rw [rowLie_apply, Finset.sum_eq_single c]
  · by_cases h : t = τ ∧ i = l
    · obtain ⟨rfl, rfl⟩ := h
      simp
    · rw [pderiv_X_of_ne (by simpa using h)]
      simp [h]
  · intro b _ hb
    rw [pderiv_X_of_ne (by simp [hb.symm]), mul_zero]
  · simp


open Classical in
theorem rowLie_diag_comm (t t' : ι) (i k l : Fin m) :
    rowLie n t i i * rowLie n t' k l - rowLie n t' k l * rowLie n t i i =
      (if t = t' then ((if i = k then 1 else 0) - (if i = l then 1 else 0) : ℂ) else 0) •
        rowLie n t' k l := by
  have h : ⁅rowDer n t i i, rowDer n t' k l⁆ =
      (if t = t' then ((if i = k then 1 else 0) - (if i = l then 1 else 0) : ℂ) else 0) •
        rowDer n t' k l := by
    refine derivation_ext fun v => ?_
    obtain ⟨s, j, c⟩ := v
    simp only [Derivation.commutator_apply, Derivation.smul_apply, rowDer_apply, rowLie_X,
      apply_ite (rowLie n t i i), apply_ite (rowLie n t' k l), map_zero]
    by_cases h1 : t = t' <;> by_cases h2 : s = t' <;> by_cases h3 : j = l <;>
      by_cases h4 : i = k <;> by_cases h5 : i = l <;> simp_all [eq_comm]
  refine LinearMap.ext fun P => ?_
  have := DFunLike.congr_fun h P
  simp only [Derivation.commutator_apply, Derivation.smul_apply, rowDer_apply] at this
  exact this

theorem iSup_iInf_eigenspace_rowLie :
    ⨆ κ : ι → Fin m → ℤ, (⨅ t, ⨅ i,
      Module.End.eigenspace (rowLie n t i i : Module.End ℂ (Pol ι m n)) (κ t i : ℂ)) = ⊤ := by
  rw [eq_top_iff]
  rintro P -
  induction P using MvPolynomial.induction_on' with
  | add P Q hP hQ => exact add_mem hP hQ
  | monomial s a =>
    refine Submodule.mem_iSup_of_mem (fun t i => ∑ c, (s (t, i, c) : ℤ)) ?_
    simp only [Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
    intro t i
    rw [rowLie_apply]
    simp only [X_mul_pderiv_monomial]
    push_cast
    rw [Finset.sum_smul]
    simp only [Nat.cast_smul_eq_nsmul]

theorem exists_totalDegree_le_of_finiteDimensional {X : Type} [AddCommGroup X] [Module ℂ X]
    [FiniteDimensional ℂ X] (Φ : X →ₗ[ℂ] Pol ι m n) : ∃ d, ∀ x, (Φ x).totalDegree ≤ d := by
  let b := Module.finBasis ℂ X
  refine ⟨Finset.univ.sup fun j => (Φ (b j)).totalDegree, fun x => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← b.sum_repr x, map_sum]
  refine totalDegree_finsetSum_le fun j _ => ?_
  rw [map_smul]
  exact (totalDegree_smul_le _ _).trans
    (Finset.le_sup (f := fun j => (Φ (b j)).totalDegree) (Finset.mem_univ j))

theorem colHighest_intertwiner_proportional :
    ∀ (ι : Type) [Fintype ι] (m n : ℕ), n ≤ m → ∀ (X : Type) [AddCommGroup X] [Module ℂ X]
      [FiniteDimensional ℂ X] (π : ι → Matrix.unitaryGroup (Fin m) ℂ → Module.End ℂ X), IrrFam π →
      ∀ (Φ Ψ : X →ₗ[ℂ] Pol ι m n) (μ μ' : ι → Fin n → ℤ), Φ ≠ 0 →
      (∀ τ u x, Φ (π τ u x) = rowSub n τ u (Φ x) ∧ Ψ (π τ u x) = rowSub n τ u (Ψ x)) →
      (∀ τ k l, k < l → colLie m τ k l ∘ₗ Φ = 0 ∧ colLie m τ k l ∘ₗ Ψ = 0) →
      (∀ τ k, colLie m τ k k ∘ₗ Φ = (μ τ k : ℂ) • Φ ∧ colLie m τ k k ∘ₗ Ψ = (μ' τ k : ℂ) • Ψ) →
      ∃ r : ℂ, Ψ = r • Φ := by
  classical
  intro ι _ m n hnm X _ _ _ π hπ Φ Ψ μ μ' hΦ heq hup hwt
  have hker : LinearMap.ker Φ = ⊥ := by
    refine (hπ _ fun τ u x hx => ?_).resolve_right fun h => hΦ (LinearMap.ker_eq_top.1 h)
    rw [LinearMap.mem_ker] at hx ⊢
    rw [(heq τ u x).1, hx, map_zero]
  have hinj : Function.Injective Φ := LinearMap.ker_eq_bot.1 hker
  obtain ⟨d₁, hd₁⟩ := exists_totalDegree_le_of_finiteDimensional Φ
  obtain ⟨d₂, hd₂⟩ := exists_totalDegree_le_of_finiteDimensional Ψ
  have hA : ∀ τ k l x, ∃ y, Φ y = rowLie n τ k l (Φ x) ∧ Ψ y = rowLie n τ k l (Ψ x) := by
    intro τ k l x
    obtain ⟨s, c, hc⟩ := GlobalTheory.DefLift.exists_sum_rowSub_eq_rowLie ι m n (max d₁ d₂) τ k l
    refine ⟨∑ u ∈ s, c u • π τ u x, ?_, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      · rw [← hc _ ((hd₁ x).trans (le_max_left _ _)), map_sum]
        exact Finset.sum_congr rfl fun u _ => by rw [map_smul, (heq τ u x).1]
    set_option synthInstance.maxHeartbeats 100000 in
      · rw [← hc _ ((hd₂ x).trans (le_max_right _ _)), map_sum]
        exact Finset.sum_congr rfl fun u _ => by rw [map_smul, (heq τ u x).2]
  obtain ⟨_, ⟨x, rfl⟩, hx0, hhi, κ, hκ⟩ := GlobalTheory.exists_highest_vector
    (fun τ k l => (rowLie n τ k l : Module.End ℂ (Pol ι m n)))
    (fun t t' i k l => by convert rowLie_diag_comm (n := n) t t' i k l)
    iSup_iInf_eigenspace_rowLie (LinearMap.range Φ)
    (by
      rintro τ k l _ ⟨x, rfl⟩
      obtain ⟨y, hy, -⟩ := hA τ k l x
      exact ⟨y, hy⟩)
    (fun h => hΦ (LinearMap.range_eq_bot.1 h))
  obtain ⟨r, hr⟩ := GlobalTheory.DefLift.joint_highest_proportional ι m n hnm (Φ x) (Ψ x) κ μ μ' hx0
    (fun τ k l hkl => ⟨hhi τ k l hkl, by
      obtain ⟨y, hy, hy'⟩ := hA τ k l x
      have : y = 0 := hinj (by rw [hy, map_zero]; exact hhi τ k l hkl)
      rw [← hy', this, map_zero]⟩)
    (fun τ k => ⟨hκ τ k, by
      obtain ⟨y, hy, hy'⟩ := hA τ k k x
      have : y = (κ τ k : ℂ) • x := hinj (by rw [hy, map_smul]; exact hκ τ k)
      rw [← hy', this, map_smul]⟩)
    (fun τ k l hkl => ⟨LinearMap.congr_fun (hup τ k l hkl).1 x,
      LinearMap.congr_fun (hup τ k l hkl).2 x⟩)
    (fun τ k => ⟨LinearMap.congr_fun (hwt τ k).1 x, LinearMap.congr_fun (hwt τ k).2 x⟩)
  refine ⟨r, sub_eq_zero.1 (LinearMap.ker_eq_top.1 ((hπ _ fun τ u y hy => ?_).resolve_left
    fun h => hx0 ?_))⟩
  · rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, sub_eq_zero] at hy ⊢
    rw [(heq τ u y).1, (heq τ u y).2, hy, map_smul]
  · have : x ∈ LinearMap.ker (Ψ - r • Φ) := by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, hr, sub_self]
    rw [h, Submodule.mem_bot] at this
    rw [this, map_zero]

end GlobalTheory.DefLift

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnHighestRowIntertwinersProportionalStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory GlobalTheory.DefLift GlobalTheory.Chain
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnHighest_rowIntertwiners_proportional : ∀ (ι : Type) [Fintype ι] (m n : ℕ), n ≤ m → ∀ (X : Type) [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X] (π : ι → Matrix.unitaryGroup (Fin m) ℂ → Module.End ℂ X), IrrFam π → ∀ (Φ Ψ : X →ₗ[ℂ] Pol ι m n) (μ μ' : ι → Fin n → ℤ), Φ ≠ 0 → (∀ τ u x, Φ (π τ u x) = rowSub n τ u (Φ x) ∧ Ψ (π τ u x) = rowSub n τ u (Ψ x)) → (∀ τ k l, k < l → colLie m τ k l ∘ₗ Φ = 0 ∧ colLie m τ k l ∘ₗ Ψ = 0) → (∀ τ k, colLie m τ k k ∘ₗ Φ = (μ τ k : ℂ) • Φ ∧ colLie m τ k k ∘ₗ Ψ = (μ' τ k : ℂ) • Ψ) → ∃ r : ℂ, Ψ = r • Φ := by
  first | exact @GlobalTheory.DefLift.colHighest_intertwiner_proportional | exact GlobalTheory.DefLift.colHighest_intertwiner_proportional | (intros; apply GlobalTheory.DefLift.colHighest_intertwiner_proportional <;> assumption)
end
