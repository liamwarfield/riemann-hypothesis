module

public import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinIndMapRangeField

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuesMemOfLocal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalIdealEqJointEigen
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormEigenvalueLeOneOfIntegralMatrixUltrametric
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormEigenvalueLeOneOfIntegralMatrixUltrametric
namespace GlobalTheory

theorem norm_eigenvalue_le_one_of_integral_matrix (O K : Type) [CommRing O] [NormedField K]
    [IsUltrametricDist K] (emb : O →+* K) (hemb : ∀ c, ‖emb c‖ ≤ 1) (n : ℕ)
    (M : Matrix (Fin n) (Fin n) O) (μ : K) (c : Fin n → K) (hc : c ≠ 0)
    (hM : (M.map emb).mulVec c = μ • c) : ‖μ‖ ≤ 1 := by
  obtain ⟨j₀, hj₀⟩ : ∃ j, c j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hc (funext h)
  obtain ⟨k, -, hk⟩ := Finset.exists_max_image Finset.univ (fun j => ‖c j‖) ⟨j₀, Finset.mem_univ _⟩
  have hpos : 0 < ‖c k‖ :=
    lt_of_lt_of_le (norm_pos_iff.2 hj₀) (hk j₀ (Finset.mem_univ _))
  have hrow : (M.map emb).mulVec c k = μ * c k := by
    rw [hM]; simp
  have hsum : ‖(M.map emb).mulVec c k‖ ≤ ‖c k‖ := by
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun j _ => ?_
    rw [norm_mul]
    calc ‖emb (M k j)‖ * ‖c j‖ ≤ 1 * ‖c k‖ :=
          mul_le_mul (hemb _) (hk j (Finset.mem_univ _)) (norm_nonneg _) zero_le_one
      _ = ‖c k‖ := one_mul _
  rw [hrow, norm_mul] at hsum
  have : ‖μ‖ * ‖c k‖ ≤ 1 * ‖c k‖ := by rwa [one_mul]
  exact le_of_mul_le_mul_right this hpos

theorem eigenvalue_integral_matrix_norm_le_one :
    ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] (emb : O →+* K),
      (∀ c, ‖emb c‖ ≤ 1) → ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) O) (μ : K) (c : Fin n → K),
      c ≠ 0 → (M.map emb).mulVec c = μ • c → ‖μ‖ ≤ 1 :=
  fun O K _ _ _ emb hemb n M μ c hc hM =>
    norm_eigenvalue_le_one_of_integral_matrix O K emb hemb n M μ c hc hM

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormEigenvalueLeOneOfIntegralMatrixUltrametricStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_eigenvalue_le_one_of_integral_matrix_ultrametric : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] (emb : O →+* K), (∀ c, ‖emb c‖ ≤ 1) → ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) O) (μ : K) (c : Fin n → K), c ≠ 0 → (M.map emb).mulVec c = μ • c → ‖μ‖ ≤ 1 := by
  first | exact @GlobalTheory.eigenvalue_integral_matrix_norm_le_one | exact GlobalTheory.eigenvalue_integral_matrix_norm_le_one | (intros; apply GlobalTheory.eigenvalue_integral_matrix_norm_le_one <;> assumption)
end
end

open MvPolynomial Matrix

namespace GlobalTheory.MaxIdealJointEigen

theorem iSupIndep_of_joint_eigen {K E I : Type} [Field K] [AddCommGroup E] [Module K E]
    (h : I → Module.End K E) (V : (I → K) → Submodule K E)
    (hV : ∀ x, ∀ v ∈ V x, ∀ i, h i v = x i • v) : iSupIndep V := by
  classical
  have stab : ∀ (s : Finset (I → K)) (i : I), ∀ u ∈ ⨆ y ∈ s, V y, h i u ∈ ⨆ y ∈ s, V y := by
    intro s i
    have : (⨆ y ∈ s, V y) ≤ (⨆ y ∈ s, V y).comap (h i) := by
      refine iSup₂_le fun y hy v hv => ?_
      rw [Submodule.mem_comap, hV y v hv i]
      exact Submodule.smul_mem _ _ ((le_iSup₂_of_le (f := fun y (_ : y ∈ s) => V y) y hy le_rfl) hv)
    exact fun u hu => this hu
  have key : ∀ (x : I → K) (s : Finset (I → K)), x ∉ s → ∀ v ∈ V x, v ∈ (⨆ y ∈ s, V y) → v = 0 := by
    intro x s
    induction s using Finset.induction_on with
    | empty => intro _ v _ hv; simpa using hv
    | insert y s hy ih =>
      intro hx v hvx hv
      rw [Finset.mem_insert, not_or] at hx
      rw [Finset.iSup_insert, Submodule.mem_sup] at hv
      obtain ⟨w, hw, u, hu, hsum⟩ := hv
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hx.1
      have e : (x i - y i) • v = h i u - y i • u := by
        rw [sub_smul, ← hV x v hvx i, ← hsum, map_add (f := _), hV y w hw i, smul_add]; abel
      have h0 := ih hx.2 ((x i - y i) • v) (Submodule.smul_mem _ _ hvx)
        (e ▸ Submodule.sub_mem _ (stab s i u hu) (Submodule.smul_mem _ _ hu))
      exact (smul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hi)
  intro x
  rw [Submodule.disjoint_def]
  intro v hvx hv
  replace hv : v ∈ ⨆ y : {y : I → K // y ≠ x}, V y.1 := by rwa [iSup_subtype]
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.mp hv
  refine key x (s.image Subtype.val) ?_ v hvx ?_
  · intro hx
    obtain ⟨⟨y, hy⟩, -, e⟩ := Finset.mem_image.mp hx
    exact hy e
  · refine (iSup₂_le fun y hy => ?_ : (⨆ y ∈ s, V y.1) ≤ _) hs
    exact le_iSup₂_of_le (f := fun y (_ : y ∈ s.image Subtype.val) => V y) y.1
      (Finset.mem_image_of_mem _ hy) le_rfl

theorem finite_joint_eigen {K I : Type} [Field K] {n : ℕ} (T : I → Matrix (Fin n) (Fin n) K) :
    {θ : I → K | ∃ c : Fin n → K, c ≠ 0 ∧ ∀ i, (T i).mulVec c = θ i • c}.Finite := by
  classical
  let V : (I → K) → Submodule K (Fin n → K) := fun θ =>
    ⨅ i, Module.End.eigenspace (Matrix.toLin' (T i)) (θ i)
  have hV : ∀ x, ∀ v ∈ V x, ∀ i, Matrix.toLin' (T i) v = x i • v := by
    intro x v hv i
    have := (Submodule.mem_iInf _).mp hv i
    exact Module.End.mem_eigenspace_iff.mp this
  have hind := iSupIndep_of_joint_eigen (fun i => Matrix.toLin' (T i)) V hV
  have hfin : Finite {θ // V θ ≠ ⊥} := by
    haveI := hind.fintypeNeBotOfFiniteDimensional
    infer_instance
  refine (Set.finite_coe_iff (s := {θ | V θ ≠ ⊥})).mp hfin |>.subset ?_
  rintro θ ⟨c, hc0, hc⟩
  show V θ ≠ ⊥
  rw [Submodule.ne_bot_iff]
  refine ⟨c, (Submodule.mem_iInf _).mpr fun i => ?_, hc0⟩
  rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
  exact hc i

theorem mulVec_eval₂ {O K I : Type} [CommRing O] [Field K] (emb : O →+* K) {n : ℕ}
    (ρ : MvPolynomial I O →ₐ[O] Matrix (Fin n) (Fin n) O) (θ : I → K) (c : Fin n → K)
    (hc : ∀ i, ((ρ (X i)).map emb).mulVec c = θ i • c) (p : MvPolynomial I O) :
    ((ρ p).map emb).mulVec c = eval₂ emb θ p • c := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, Matrix.algebraMap_eq_diagonal]
    ext j
    simp [Matrix.mulVec_diagonal]
  | add p q hp hq =>
    rw [map_add (f := _), Matrix.map_add _ (map_add emb), Matrix.add_mulVec, hp, hq, eval₂_add, add_smul]
  | mul_X p i hp =>
    rw [map_mul, Matrix.map_mul, ← Matrix.mulVec_mulVec, hc, Matrix.mulVec_smul, hp, eval₂_mul,
      eval₂_X, smul_smul, mul_comm]

end GlobalTheory.MaxIdealJointEigen

namespace GlobalTheory

open MvPolynomial Matrix GlobalTheory.MaxIdealJointEigen

theorem maximal_ideal_eq_joint_eigen : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O]
    (emb : O →+* PadicAlgCl l), (∀ c, ‖emb c‖ ≤ 1) → (∀ c, ‖emb c‖ = 1 → IsUnit c) →
    ∀ (I : Type) (n : ℕ) (ρ : MvPolynomial I O →ₐ[O] Matrix (Fin n) (Fin n) O)
    (m : Ideal (MvPolynomial I O)), m.IsMaximal → RingHom.ker ρ ≤ m →
    ∃ θ : I → PadicAlgCl l, (∀ i, ‖θ i‖ ≤ 1) ∧ (∀ p, p ∈ m ↔ ‖MvPolynomial.eval₂ emb θ p‖ < 1) ∧
      ∃ c : Fin n → PadicAlgCl l, c ≠ 0 ∧
        ∀ i, ((ρ (MvPolynomial.X i)).map emb).mulVec c = θ i • c := by
  intro l _ O _ emb h1 hu I n ρ m hm hker
  classical
  set K := PadicAlgCl l
  let T : I → Matrix (Fin n) (Fin n) K := fun i => (ρ (X i)).map emb
  let Θ : Set (I → K) := {θ | ∃ c : Fin n → K, c ≠ 0 ∧ ∀ i, (T i).mulVec c = θ i • c}
  have hfin : Θ.Finite := finite_joint_eigen T
  have hint : ∀ θ ∈ Θ, ∀ p, ‖eval₂ emb θ p‖ ≤ 1 := by
    rintro θ ⟨c, hc0, hc⟩ p
    exact GlobalTheory.T.norm_eigenvalue_le_one_of_integral_matrix_ultrametric O K emb h1 n (ρ p) _ c hc0 (mulVec_eval₂ emb ρ θ c hc p)

  let J : (I → K) → Ideal (MvPolynomial I O) := fun θ =>
    { carrier := {p | ∀ r, ‖eval₂ emb θ (r * p)‖ < 1}
      add_mem' := by
        intro a b ha hb r
        simp only [Set.mem_setOf_eq, mul_add, eval₂_add] at *
        exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt (ha r) (hb r))
      zero_mem' := by intro r; simp
      smul_mem' := by
        intro a b hb r
        simp only [Set.mem_setOf_eq, smul_eq_mul, ← mul_assoc] at *
        exact hb (r * a) }
  have hJmem : ∀ θ ∈ Θ, ∀ p, p ∈ J θ ↔ ‖eval₂ emb θ p‖ < 1 := by
    intro θ hθ p
    constructor
    · intro h; simpa using h 1
    · intro h r
      show ‖eval₂ emb θ (r * p)‖ < 1
      rw [eval₂_mul, norm_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (hint θ hθ r)) h
  have hJprime : ∀ θ ∈ Θ, (J θ).IsPrime := by
    intro θ hθ
    refine ⟨?_, ?_⟩
    · intro htop
      have := (hJmem θ hθ 1).mp (htop ▸ Submodule.mem_top)
      simp at this
    · intro a b hab
      rw [hJmem θ hθ, eval₂_mul, norm_mul] at hab
      rw [hJmem θ hθ, hJmem θ hθ]
      by_contra hc
      push_neg at hc
      have := mul_le_mul hc.1 hc.2 zero_le_one (norm_nonneg _)
      linarith
  by_cases hex : ∃ θ ∈ Θ, m ≤ J θ
  · obtain ⟨θ, hθ, hle⟩ := hex
    have heq : m = J θ := hm.eq_of_le (hJprime θ hθ).ne_top hle
    obtain ⟨c, hc0, hc⟩ := hθ
    refine ⟨θ, fun i => ?_, fun p => ?_, c, hc0, hc⟩
    · simpa using hint θ ⟨c, hc0, hc⟩ (X i)
    · rw [heq]; exact hJmem θ ⟨c, hc0, hc⟩ p
  · exfalso
    push_neg at hex
    have hnot : ¬ ((m : Set (MvPolynomial I O)) ⊆ ⋃ θ ∈ (hfin.toFinset : Set (I → K)), (J θ : Set _)) := by
      rw [Ideal.subset_union_prime (0 : I → K) (0 : I → K)
        (fun θ hθ _ _ => hJprime θ (by simpa using hθ))]
      rintro ⟨θ, hθ, hle⟩
      exact hex θ (by simpa using hθ) hle
    obtain ⟨q, hqm, hq⟩ := Set.not_subset.mp hnot
    have hq1 : ∀ θ ∈ Θ, ‖eval₂ emb θ q‖ = 1 := by
      intro θ hθ
      refine le_antisymm (hint θ hθ q) (not_lt.mp fun h => hq ?_)
      exact Set.mem_biUnion (x := θ) (by simpa using hθ) ((hJmem θ hθ q).mpr h)
    let B : Matrix (Fin n) (Fin n) K := (ρ q).map emb
    have hcomm : ∀ p p', ((ρ p).map emb) * ((ρ p').map emb) = ((ρ p').map emb) * ((ρ p).map emb) := by
      intro p p'
      rw [← Matrix.map_mul, ← Matrix.map_mul, ← map_mul, ← map_mul, mul_comm]
    have hroot : ∀ μ ∈ B.charpoly.roots, ‖μ‖ = 1 := by
      intro μ hμ
      have hdet0 : (Matrix.scalar (Fin n) μ - B).det = 0 := by
        rw [← Matrix.eval_charpoly]
        exact (Polynomial.mem_roots'.mp hμ).2
      obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet0
      have hsc : ∀ w : Fin n → K, (Matrix.scalar (Fin n) μ) *ᵥ w = μ • w := by
        intro w; ext j; simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
      have hBv : B *ᵥ v = μ • v := by
        rw [Matrix.sub_mulVec, sub_eq_zero, hsc] at hv
        exact hv.symm
      let W : Submodule K (Fin n → K) := Module.End.eigenspace (Matrix.toLin' B) μ
      have hW0 : W ≠ ⊥ := by
        rw [Submodule.ne_bot_iff]
        refine ⟨v, ?_, hv0⟩
        rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
        exact hBv
      have hWs : ∀ i, ∀ w ∈ W, Matrix.toLin' (T i) w ∈ W := by
        intro i w hw
        rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hw ⊢
        rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec]
        change ((ρ q).map emb * (ρ (X i)).map emb) *ᵥ w = μ • ((ρ (X i)).map emb *ᵥ w)
        rw [hcomm, ← Matrix.mulVec_mulVec]
        change (ρ (X i)).map emb *ᵥ (B *ᵥ w) = _
        rw [hw, Matrix.mulVec_smul]
      obtain ⟨c, hcW, hc0, hc⟩ := GlobalTheory.exists_common_eigenvector_mem
        (fun i => Matrix.toLin' (T i))
        (fun i j w => by
          simp only [Matrix.toLin'_apply, Matrix.mulVec_mulVec]
          exact congrArg (· *ᵥ w) (hcomm (X i) (X j))) W hW0 hWs
      choose θ hθ using hc
      have hθ' : ∀ i, (T i) *ᵥ c = θ i • c := fun i => by simpa [Matrix.toLin'_apply] using hθ i
      have hθΘ : θ ∈ Θ := ⟨c, hc0, hθ'⟩
      have h2 := mulVec_eval₂ emb ρ θ c hθ' q
      have h3 : B *ᵥ c = μ • c := by
        have := Module.End.mem_eigenspace_iff.mp hcW
        rwa [Matrix.toLin'_apply] at this
      have hμ : μ = eval₂ emb θ q := by
        have e : (μ - eval₂ emb θ q) • c = 0 := by
          rw [sub_smul, ← h3, ← h2]
          exact sub_self _
        exact sub_eq_zero.mp ((smul_eq_zero.mp e).resolve_right hc0)
      rw [hμ]
      exact hq1 θ hθΘ
    have hdetB : ‖emb (ρ q).det‖ = 1 := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.det_eq_prod_roots_charpoly]
      exact Multiset.prod_induction (fun x => ‖x‖ = 1) _
        (fun a b ha hb => by rw [norm_mul, ha, hb, one_mul]) norm_one hroot
    have hunit : IsUnit (ρ q).det := hu _ hdetB
    set P := (ρ q).charpoly with hPdef
    have hP : Polynomial.aeval q P ∈ m := by
      apply hker
      rw [RingHom.mem_ker]
      rw [← Polynomial.aeval_algHom_apply, Matrix.aeval_self_charpoly]
    have hC : MvPolynomial.C (P.coeff 0) ∈ m := by
      rw [← Ideal.Quotient.eq_zero_iff_mem] at hP ⊢
      have hq0 : Ideal.Quotient.mkₐ O m q = 0 := by
        rw [Ideal.Quotient.mkₐ_eq_mk]; exact Ideal.Quotient.eq_zero_iff_mem.mpr hqm
      have e := Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ O m) q P
      rw [hq0, ← Polynomial.coeff_zero_eq_aeval_zero'] at e
      calc Ideal.Quotient.mk m (C (P.coeff 0))
          = algebraMap O (MvPolynomial I O ⧸ m) (P.coeff 0) := by
            rw [← MvPolynomial.algebraMap_eq]
            first
              | exact Ideal.Quotient.mk_algebraMap _ _ _
              | rfl
        _ = Ideal.Quotient.mkₐ O m (Polynomial.aeval q P) := e
        _ = 0 := by rw [Ideal.Quotient.mkₐ_eq_mk]; exact hP
    have hu0 : IsUnit (P.coeff 0) := by
      rw [Matrix.det_eq_sign_charpoly_coeff] at hunit
      exact isUnit_of_mul_isUnit_right hunit
    exact hm.ne_top (Ideal.eq_top_of_isUnit_mem _ hC (hu0.map MvPolynomial.C))

end GlobalTheory
end

set_option autoImplicit false
noncomputable section
open MvPolynomial

namespace GlobalTheory.ExpCover

def transOp {L G W : Type} [CommRing L] [Mul G] [AddCommGroup W] [Module L W] (a : L) (t : Finset G) : (G → W) →ₗ[L] (G → W) where
  toFun v g := a • ∑ s ∈ t, v (g * s)
  map_add' v v' := by funext g; simp [Finset.sum_add_distrib, smul_add]
  map_smul' c v := by funext g; simp [Finset.smul_sum, smul_comm c]

set_option autoImplicit false in
private lemma coeffs_eq_zero_of_linearIndependent_of_injective {O K X : Type} [CommRing O] [IsDomain O] [Field K]
    (emb : O →+* K) (hemb : Function.Injective emb) :
    ∀ (n : ℕ) (α : Fin n → X → O), LinearIndependent O α →
      ∀ c : Fin n → K, (∀ x, ∑ j, c j * emb (α j x) = 0) → c = 0 := by
  intro n
  induction n with
  | zero => intro α _ c _; funext j; exact j.elim0
  | succ n ih =>
    intro α hα c hc
    have h0 : α 0 ≠ 0 := hα.ne_zero 0
    obtain ⟨x0, hx0⟩ : ∃ x0, α 0 x0 ≠ 0 := by
      by_contra h
      push_neg at h
      exact h0 (funext h)
    have hea : emb (α 0 x0) ≠ 0 := fun h => hx0 (hemb (by rw [h, map_zero]))
    let β : Fin n → X → O := fun j x => α 0 x0 * α j.succ x - α j.succ x0 * α 0 x
    have hβ : LinearIndependent O β := by
      rw [Fintype.linearIndependent_iff] at hα ⊢
      intro d hd j
      have hd' : ∀ x, ∑ k, d k * β k x = 0 := fun x => by
        simpa [Finset.sum_apply] using congrFun hd x
      have key := hα (Fin.cons (-(∑ k, d k * α k.succ x0)) (fun k => d k * α 0 x0)) (by
        funext x
        have e1 : ∑ k, d k * β k x =
            α 0 x0 * ∑ k, d k * α k.succ x - (∑ k, d k * α k.succ x0) * α 0 x := by
          rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun k _ => by simp only [β]; ring
        have e2 : ∑ k, d k * α 0 x0 * α k.succ x = α 0 x0 * ∑ k, d k * α k.succ x := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
        have h3 := hd' x
        rw [e1] at h3
        simp only [Fin.sum_univ_succ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.cons_zero,
          Fin.cons_succ, Pi.zero_apply]
        rw [e2]
        linear_combination h3)
      have := key j.succ
      simp only [Fin.cons_succ] at this
      exact (mul_eq_zero.1 this).resolve_right hx0
    have hS : ∀ x, c 0 * emb (α 0 x) + ∑ j : Fin n, c j.succ * emb (α j.succ x) = 0 := fun x => by
      simpa [Fin.sum_univ_succ] using hc x
    have hrel : ∀ x, ∑ j, c j.succ * emb (β j x) = 0 := by
      intro x
      have e : ∑ j, c j.succ * emb (β j x) = emb (α 0 x0) * ∑ j : Fin n, c j.succ * emb (α j.succ x)
          - (∑ j : Fin n, c j.succ * emb (α j.succ x0)) * emb (α 0 x) := by
        rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun k _ => by simp only [β, map_sub, map_mul]; ring
      rw [e]
      linear_combination emb (α 0 x0) * hS x - emb (α 0 x) * hS x0
    have htail := ih β hβ (fun j => c j.succ) hrel
    have htail' : ∀ j : Fin n, c j.succ = 0 := fun j => congrFun htail j
    have hc0 : c 0 = 0 := by
      have := hS x0
      simp only [htail', zero_mul, Finset.sum_const_zero, add_zero] at this
      exact (mul_eq_zero.1 this).resolve_right hea
    funext j
    refine Fin.cases ?_ (fun k => ?_) j
    · exact hc0
    · exact htail' k


set_option autoImplicit false in
open MvPolynomial in
theorem _root_.GlobalTheory.ExpCover.values_mem_of_local {l : ℕ} [Fact l.Prime] {O I G V W : Type} [CommRing O]
    [IsDomain O] [IsPrincipalIdealRing O] [Mul G]
    [AddCommGroup V] [Module O V] [Module.Finite O V] [AddCommGroup W] [Module (PadicAlgCl l) W]
    (M : Submodule O (G → V)) [hm : Module (MvPolynomial I O) M] [@IsScalarTower O (MvPolynomial I O) M _ hm.toSMul _]
    [Module.Finite O M]
    (emb : O →+* PadicAlgCl l) (hemb : Function.Injective emb)
    (h1 : ∀ c, ‖emb c‖ ≤ 1) (hu : ∀ c, ‖emb c‖ = 1 → IsUnit c) (b : V →ₛₗ[emb] W) (hb : Function.Injective b)
    (hli : ∀ (n : ℕ) (y : Fin n → V), LinearIndependent O y → LinearIndependent (PadicAlgCl l) fun j => b (y j))
    (tr : I → Finset G) (cst : I → O)
    (hX : ∀ i (f : M) g, (((X i : MvPolynomial I O) • f : M) : G → V) g = cst i • ∑ s ∈ tr i, (f : G → V) (g * s))
    (U : Submodule O V) (S : Submodule (PadicAlgCl l) (G → W))
    (hS : ∀ i, ∀ u ∈ S, _root_.GlobalTheory.ExpCover.transOp (emb (cst i)) (tr i) u ∈ S)
    (x : M) (hx : (fun g => b ((x : G → V) g)) ∈ S) (a : O) (J : ℕ) (D : Set M) (hD : ∀ y ∈ D, ∀ g, (y : G → V) g ∈ U)
    (hloc : ∀ (m : Ideal (MvPolynomial I O)) (hmax : m.IsMaximal) (θ : I → PadicAlgCl l), (∀ i, ‖θ i‖ ≤ 1) →
      (∀ p, p ∈ m ↔ ‖eval₂ emb θ p‖ < 1) →
      (∃ v ∈ S, v ≠ 0 ∧ ∀ i g, emb (cst i) • ∑ s ∈ tr i, v (g * s) = θ i • v g) →
      ∀ y : LocalizedModule (haveI := hmax.isPrime; m.primeCompl) M,
        ∃ x' ∈ D, ∃ s : (haveI := hmax.isPrime; m.primeCompl),
          LocalizedModule.mk x' s = (algebraMap O (MvPolynomial I O) a) ^ J • y) :
    ∀ g, ((a ^ J • x : M) : G → V) g ∈ U := by
  classical
  let N : Submodule (MvPolynomial I O) M :=
    { carrier := {y | ∀ g, (y : G → V) g ∈ U}
      add_mem' := fun {y z} hy hz g => by
        simpa using U.add_mem (hy g) (hz g)
      zero_mem' := fun g => by simp
      smul_mem' := fun p y hy => by
        induction p using MvPolynomial.induction_on with
        | C c =>
          intro g
          have h : (C c : MvPolynomial I O) • y = c • y := by
            rw [← MvPolynomial.algebraMap_eq, algebraMap_smul]
          rw [h, Submodule.coe_smul, Pi.smul_apply]
          exact U.smul_mem c (hy g)
        | add p q hp hq =>
          intro g
          rw [add_smul]
          simpa using U.add_mem (hp g) (hq g)
        | mul_X p i hp =>
          intro g
          rw [mul_comm, mul_smul, hX i (p • y) g]
          exact U.smul_mem _ (U.sum_mem fun s _ => hp (g * s)) }
  set z : M := a ^ J • x with hz_def
  let A : Ideal (MvPolynomial I O) := N.comap (LinearMap.toSpanSingleton (MvPolynomial I O) M z)
  have hA : ∀ p, p ∈ A ↔ p • z ∈ N := fun p => Iff.rfl
  show z ∈ N
  by_contra hzN
  have hAtop : A ≠ ⊤ := by
    intro h
    apply hzN
    have h1' : (1 : MvPolynomial I O) ∈ A := h ▸ Submodule.mem_top
    simpa using (hA 1).1 h1'
  obtain ⟨m, hmax, hAm⟩ := Ideal.exists_le_maximal A hAtop
  have key : ∃ θ : I → PadicAlgCl l, (∀ i, ‖θ i‖ ≤ 1) ∧ (∀ p, p ∈ m ↔ ‖eval₂ emb θ p‖ < 1) ∧
      (∃ v ∈ S, v ≠ 0 ∧ ∀ i g, emb (cst i) • ∑ s ∈ tr i, v (g * s) = θ i • v g) := by
    haveI : Module.IsTorsionFree O V := Module.IsTorsionFree.of_smul_eq_zero fun r w h => by
      have h' : emb r • b w = 0 := by rw [← map_smulₛₗ, h, map_zero]
      rcases smul_eq_zero.1 h' with h'' | h''
      · exact Or.inl (hemb (by rw [h'', map_zero]))
      · exact Or.inr (hb (by rw [h'', map_zero]))
    let Z : Submodule (MvPolynomial I O) M := Submodule.span (MvPolynomial I O) {x}
    let ι : Z →ₗ[O] (G → V) := M.subtype ∘ₗ (Z.subtype.restrictScalars O)
    have hι : Function.Injective ι := Subtype.val_injective.comp Subtype.val_injective
    haveI : Module.IsTorsionFree O Z := hι.moduleIsTorsionFree _ (by simp)
    haveI : Module.Finite O Z :=
      Module.Finite.of_injective (Z.subtype.restrictScalars O) Subtype.val_injective
    haveI : Module.Free O Z := Module.free_of_finite_type_torsion_free'
    let B := Module.finBasis O Z
    let φ : MvPolynomial I O →ₐ[O] Module.End O Z := Algebra.lsmul O O Z
    let ρ : MvPolynomial I O →ₐ[O] Matrix (Fin (Module.finrank O Z)) (Fin (Module.finrank O Z)) O :=
      (LinearMap.toMatrixAlgEquiv B).toAlgHom.comp φ
    have hxZ : x ∈ Z := Submodule.subset_span rfl
    have hker : ∀ p ∈ RingHom.ker ρ, p • x = 0 := by
      intro p hp
      have h0 : φ p = 0 := by
        have : ρ p = 0 := hp
        exact (LinearMap.toMatrixAlgEquiv B).injective (by simpa [ρ] using this)
      have := congrArg Subtype.val (LinearMap.congr_fun h0 ⟨x, hxZ⟩)
      simpa [φ] using this
    obtain ⟨θ, hθ1, hθm, c, hc0, hc⟩ := _root_.GlobalTheory.maximal_ideal_eq_joint_eigen l O emb h1 hu I
      (Module.finrank O Z) ρ m hmax (fun p hp => hAm ((hA p).2 (by
        rw [hz_def, smul_comm, hker p hp, smul_zero]; exact N.zero_mem)))
    have hpS : ∀ p : MvPolynomial I O, (fun g => b (((p • x : M) : G → V) g)) ∈ S := by
      intro p
      induction p using MvPolynomial.induction_on with
      | C r =>
        have e : (fun g => b ((((C r : MvPolynomial I O) • x : M) : G → V) g)) =
            emb r • fun g => b ((x : G → V) g) := by
          funext g
          rw [← MvPolynomial.algebraMap_eq, algebraMap_smul]
          simp [map_smulₛₗ]
        rw [e]; exact S.smul_mem _ hx
      | add p q hp hq =>
        have e : (fun g => b ((((p + q) • x : M) : G → V) g)) =
            (fun g => b (((p • x : M) : G → V) g)) + fun g => b (((q • x : M) : G → V) g) := by
          funext g; simp [add_smul]
        rw [e]; exact S.add_mem hp hq
      | mul_X p i hp =>
        have e : (fun g => b ((((p * X i) • x : M) : G → V) g)) =
            _root_.GlobalTheory.ExpCover.transOp (emb (cst i)) (tr i)
              (fun g => b (((p • x : M) : G → V) g)) := by
          funext g
          rw [mul_comm, mul_smul, hX]
          set_option synthInstance.maxHeartbeats 100000 in
            simp [_root_.GlobalTheory.ExpCover.transOp, map_sum, map_smulₛₗ]
        rw [e]; exact hS i _ hp
    have hZS : ∀ z ∈ Z, (fun g => b ((z : G → V) g)) ∈ S := by
      intro z hz
      obtain ⟨p, rfl⟩ := Submodule.mem_span_singleton.1 hz
      exact hpS p
    let f : Fin (Module.finrank O Z) → G → W := fun j g => b ((((B j : Z) : M) : G → V) g)
    have hind : LinearIndependent (PadicAlgCl l) f := by
      haveI : Module.Free O V := Module.free_of_finite_type_torsion_free'
      let w := Module.finBasis O V
      have hw := hli _ w w.linearIndependent
      let L : Z →ₗ[O] (G × Fin (Module.finrank O V) → O) :=
        LinearMap.pi fun p => (Finsupp.lapply p.2 ∘ₗ w.repr.toLinearMap) ∘ₗ (LinearMap.proj p.1 ∘ₗ ι)
      have hL : Function.Injective L := by
        rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
        intro z hz
        apply hι
        funext g
        apply w.repr.injective
        ext k
        have := congrFun hz (g, k)
        simpa [L] using this
      have hα := B.linearIndependent.map' L (LinearMap.ker_eq_bot.2 hL)
      rw [Fintype.linearIndependent_iff]
      intro c' hc'
      have hfk : ∀ j g, f j g = ∑ k, emb ((L ∘ B) j (g, k)) • b (w k) := by
        intro j g
        have e := congrArg b (w.sum_repr ((((B j : Z) : M) : G → V) g))
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum] at e
        simp only [map_smulₛₗ] at e
        show b ((((B j : Z) : M) : G → V) g) = _
        rw [← e]
        rfl
      have hzero : c' = 0 := coeffs_eq_zero_of_linearIndependent_of_injective emb hemb _ _ hα c' fun p => by
        have hg : ∑ j, c' j • f j p.1 = 0 := by simpa [Finset.sum_apply] using congrFun hc' p.1
        have hsum : ∑ k, (∑ j, c' j * emb ((L ∘ B) j (p.1, k))) • b (w k) = 0 := by
          have e : ∑ k, (∑ j, c' j * emb ((L ∘ B) j (p.1, k))) • b (w k) = ∑ j, c' j • f j p.1 := by
            simp only [hfk, Finset.smul_sum, Finset.sum_smul, smul_smul]
            exact Finset.sum_comm
          rw [e, hg]
        exact (Fintype.linearIndependent_iff.1 hw) _ hsum p.2
      exact fun j => congrFun hzero j
    let v : G → W := ∑ j, c j • f j
    have hv_apply : ∀ h, v h = ∑ j, c j • f j h := by intro h; simp [v, Finset.sum_apply]
    refine ⟨θ, hθ1, hθm, v, S.sum_mem fun j _ => S.smul_mem _ (hZS _ (B j).2), ?_, ?_⟩
    · intro hv0
      exact hc0 (funext (Fintype.linearIndependent_iff.1 hind c hv0))
    · intro i g
      have hXB : ∀ j, emb (cst i) • ∑ s ∈ tr i, f j (g * s) = ∑ k, emb (ρ (X i) k j) • f k g := by
        intro j
        have e1 : (X i : MvPolynomial I O) • B j = ∑ k, ρ (X i) k j • B k := by
          conv_lhs => rw [← B.sum_repr ((X i : MvPolynomial I O) • B j)]
          simp [ρ, φ, LinearMap.toMatrixAlgEquiv_apply]
        calc emb (cst i) • ∑ s ∈ tr i, f j (g * s)
            = b ((((X i : MvPolynomial I O) • ((B j : Z) : M) : M) : G → V) g) := by
              set_option synthInstance.maxHeartbeats 100000 in
                rw [hX]; simp [f, map_sum, map_smulₛₗ]
          _ = b (((((X i : MvPolynomial I O) • B j : Z) : M) : G → V) g) := rfl
          _ = b ((((∑ k, ρ (X i) k j • B k : Z) : M) : G → V) g) := by rw [e1]
          _ = ∑ k, emb (ρ (X i) k j) • f k g := by
              set_option synthInstance.maxHeartbeats 100000 in
                simp [f, map_sum, map_smulₛₗ, Submodule.coe_sum, Finset.sum_apply]
      calc emb (cst i) • ∑ s ∈ tr i, v (g * s)
          = ∑ j, c j • (emb (cst i) • ∑ s ∈ tr i, f j (g * s)) := by
            simp only [hv_apply, Finset.smul_sum]
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun s _ => smul_comm _ _ _
        _ = ∑ j, c j • ∑ k, emb (ρ (X i) k j) • f k g :=
            Finset.sum_congr rfl fun j _ => by rw [hXB]
        _ = ∑ k, (∑ j, emb (ρ (X i) k j) * c j) • f k g := by
            simp only [Finset.smul_sum, Finset.sum_smul, smul_smul]
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by rw [mul_comm]
        _ = ∑ k, (θ i * c k) • f k g := by
            refine Finset.sum_congr rfl fun k _ => ?_
            congr 1
            have := congrFun (hc i) k
            simpa [Matrix.mulVec, dotProduct] using this
        _ = θ i • v g := by
            rw [hv_apply, Finset.smul_sum]
            exact Finset.sum_congr rfl fun k _ => by rw [smul_smul]
  obtain ⟨θ, hθ1, hθm, hv⟩ := key
  obtain ⟨x', hx'D, s, hs⟩ := hloc m hmax θ hθ1 hθm hv (LocalizedModule.mk x 1)
  rw [LocalizedModule.smul'_mk, LocalizedModule.mk_eq] at hs
  obtain ⟨u, hu⟩ := hs
  have hpow : (algebraMap O (MvPolynomial I O) a) ^ J • x = z := by
    rw [← map_pow, algebraMap_smul]
  rw [hpow, one_smul] at hu
  have hmem : ((u : MvPolynomial I O) * (s : MvPolynomial I O)) • z ∈ N := by
    rw [mul_smul]
    change (u : MvPolynomial I O) • (s : MvPolynomial I O) • z ∈ N
    rw [← Submonoid.smul_def, ← Submonoid.smul_def, ← hu, Submonoid.smul_def]
    exact N.smul_mem _ (hD x' hx'D)
  have hus := hAm ((hA _).2 hmem)
  haveI := hmax.isPrime
  rcases hmax.isPrime.mem_or_mem hus with h | h
  · exact u.2 h
  · exact s.2 h

end GlobalTheory.ExpCover
end
end

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

namespace GlobalTheory.ExpCover

private theorem latD_of {l : ℕ} [Fact l.Prime] {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (F : Frame l ι N)
    (lam : ι → ℕ → ℕ) (y : NablaT (PadicAlgCl l) N lam)
    (h : ∃ x ∈ tensSub (deltaIn F.O N lam), GlobalTheory.LatBC.bc F.emb N lam x = y) : y ∈ F.latD lam := by
  obtain ⟨x, ⟨z, rfl⟩, rfl⟩ := h
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    rw [LinearMap.map_smul, PiTensorProduct.map_tprod, LinearMap.map_smulₛₗ, GlobalTheory.LatBC.bc_tprod]
    exact AddSubgroup.subset_closure ⟨r, fun τ => GlobalTheory.LatBC.dwMap F.emb N _ (m τ),
      fun τ => ⟨((m τ : Formalism.GradedWeylDivisibility.dualWeyl F.O N N (res N (lam τ))) : MvPolynomial (Fin N × Fin N) F.O), (m τ).2, rfl⟩, rfl⟩
  | add a b ha hb =>
    rw [map_add (f := _), map_add (f := _)]
    exact add_mem ha hb

end GlobalTheory.ExpCover

namespace GlobalTheory.ExpCover

section Glue

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G0 : Type} [Group G0] [Fintype G0] {Pl0 : Type}
  (B : BlockDat K G0 Pl0) (ℓ : Lvl K G0) (Z : Submodule K B.S.Forms)

private theorem toF_coe (z : Fin (B.dZ ℓ Z) → K) :
    ((B.toF ℓ Z z : B.S.Forms) : B.S.Cl → B.S.V) = B.S.I ((B.fE ℓ Z).mulVec z) := by
  simp [BlockDat.toF, BlockDat.fE, CSD.I, Matrix.mulVec_mulVec]

private theorem toF_mem (z : Fin (B.dZ ℓ Z) → K) : B.toF ℓ Z z ∈ Z := by
  have h1 : (B.zE ℓ Z).mulVec z ∈ B.Z0 ℓ Z := by
    rw [BlockDat.zE, subE_mulVec]; exact Submodule.coe_mem _
  have h2 : (B.vE ℓ).mulVec ((B.zE ℓ Z).mulVec z) ∈ B.coord Z := h1
  obtain ⟨f, hf, hfe⟩ := Submodule.mem_map.1 h2
  have : B.toF ℓ Z z = f := by
    simp only [BlockDat.toF, LinearMap.coe_comp, Function.comp_apply, Matrix.mulVecLin_apply]
    rw [← hfe]; simp
  rw [this]; exact hf

private theorem mem_cutZ (z : Fin (B.dZ ℓ Z) → K) :
    z ∈ B.cutZ ℓ Z ↔ ∀ c, ((B.toF ℓ Z z : B.S.Forms) : B.S.Cl → B.S.V) c ∈ B.S.Nab c := by
  rw [toF_coe]
  simp [BlockDat.cutZ, Formalism.DivisionValues.cutLat, CSD.nabLat, Formalism.DivisionValues.valLatF, Submodule.mem_pi]

private theorem mem_delZ (z : Fin (B.dZ ℓ Z) → K) :
    z ∈ B.delZ ℓ Z ↔ ∀ c, ((B.toF ℓ Z z : B.S.Forms) : B.S.Cl → B.S.V) c ∈ B.S.Del c := by
  rw [toF_coe]
  simp [BlockDat.delZ, Formalism.DivisionValues.cutLat, CSD.delLat, Formalism.DivisionValues.valLatF, Submodule.mem_pi]

private theorem final_step (w : HeightOneSpectrum (𝓞 K)) (L : 𝓞 K) (z : Fin (B.dZ ℓ Z) → K)
    (h : ∃ s : 𝓞 K, s ∉ w.asIdeal ∧
      ∀ c, s • (((algebraMap (𝓞 K) K L) • B.toF ℓ Z z : B.S.Forms) : B.S.Cl → B.S.V) c ∈ B.S.Del c) :
    L • z ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (B.delZ ℓ Z) := by
  obtain ⟨s, hs, hc⟩ := h
  refine ⟨s, hs, ?_⟩
  rw [mem_delZ]
  intro c
  have e : B.toF ℓ Z (s • L • z) = (algebraMap (𝓞 K) K s) • (algebraMap (𝓞 K) K L) • B.toF ℓ Z z := by
    rw [← map_smul, ← map_smul, algebraMap_smul, algebraMap_smul]
  rw [e]
  simpa [algebraMap_smul] using hc c

end Glue

end GlobalTheory.ExpCover

namespace GlobalTheory.ExpCover

private theorem isForm_of_span {l : ℕ} [Fact l.Prime] {ι : Type} [DecidableEq ι] {N : ℕ} (F : Frame l ι N) (lam : ι → ℕ → ℕ)
    (A : Set (F.G → NablaT (PadicAlgCl l) N lam)) (hA : ∀ f ∈ A, F.IsForm lam f) :
    ∀ f ∈ Submodule.span (PadicAlgCl l) A, F.IsForm lam f := by
  intro f hf
  induction hf using Submodule.span_induction with
  | mem f hf => exact hA f hf
  | zero => exact ⟨fun _ _ _ => rfl, fun κ g => by rw [Pi.zero_apply, Pi.zero_apply, map_zero, smul_zero]⟩
  | add f f' _ _ h h' =>
    refine ⟨fun γ hγ g => by rw [Pi.add_apply, Pi.add_apply, h.1 γ hγ, h'.1 γ hγ], fun κ g => ?_⟩
    rw [Pi.add_apply, Pi.add_apply, map_add (f := _), smul_add, h.2, h'.2]
  | smul a f _ h =>
    refine ⟨fun γ hγ g => by rw [Pi.smul_apply, Pi.smul_apply, h.1 γ hγ], fun κ g => ?_⟩
    rw [Pi.smul_apply, Pi.smul_apply, map_smul, smul_comm, h.2]

private theorem span_stable {l : ℕ} [Fact l.Prime] {ι : Type} [DecidableEq ι] {N : ℕ} {F : Frame l ι N} {lam : ι → ℕ → ℕ}
    {K : Type} [Field K] [NumberField K] [StarRing K] {G0 : Type} [Group G0] [Fintype G0] {Pl0 : Type} {B : BlockDat K G0 Pl0}
    {w : HeightOneSpectrum (𝓞 K)} (R : Reads F lam B w) (Z : Submodule K B.S.Forms) (hZ : ∀ i, Z ≤ Z.comap (B.op i)) (i : F.I) :
    ∀ u ∈ Submodule.span (PadicAlgCl l) (R.rd '' Z),
      transOp (F.emb (F.cst i)) (F.tr i) u ∈ Submodule.span (PadicAlgCl l) (R.rd '' Z) := by
  intro u hu
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨f, hf, rfl⟩ := hu
    exact Submodule.subset_span ⟨B.op (R.ix i) f, hZ (R.ix i) hf, funext fun g => R.hecke i f g⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add _ _ _ _ h h' => rw [map_add (f := _)]; exact Submodule.add_mem _ h h'
  | smul a _ _ h => rw [map_smul]; exact Submodule.smul_mem _ a h

private theorem forms_fin : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (F : Frame l ι N) (lam : ι → ℕ → ℕ)
    (jK : F.K →* alg F.O N lam), F.Ok → Module.Finite F.O (Forms F.O (A := alg F.O N lam) F.Γ jK (NablaT F.O N lam)) := by
  intro l _ ι _ _ N F lam jK hF
  haveI : Module.Finite F.O (NablaT F.O N lam) := GlobalTheory.NablaFin.nablaT_finite F.O N ι lam
  obtain ⟨S, hS⟩ := hF.classes
  haveI : Finite (Formalism.UG.ClassSet F.Γ F.K) := by
    refine Finite.of_surjective (fun s : S => (DoubleCoset.mk F.Γ F.K (s : F.G) : Formalism.UG.ClassSet F.Γ F.K)) ?_
    intro c
    obtain ⟨γ, hγ, s, hs, κ, hκ, e⟩ := hS (Quotient.out c)
    refine ⟨⟨s, hs⟩, ?_⟩
    show DoubleCoset.mk F.Γ F.K s = c
    rw [← DoubleCoset.out_eq' c]
    exact (@DoubleCoset.eq _ _ F.Γ F.K s _).2 ⟨γ, hγ, κ, hκ, e⟩
  exact Formalism.UG.P.automorphic_forms_level_finite_holds F.G F.Γ F.K F.O (NablaT F.O N lam) _ ‹_›

private theorem emb_norm : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) (N : ℕ) (F : Frame l ι N), F.Ok →
    (∀ c, ‖F.emb c‖ ≤ 1) ∧ ∀ c, ‖F.emb c‖ = 1 → IsUnit c := by
  intro l _ ι N F hF
  obtain ⟨hinj, L, _, hL⟩ := hF.ring
  have hmem : ∀ c, F.emb c ∈ L ∧ ‖F.emb c‖ ≤ 1 := by
    intro c
    have : F.emb c ∈ Set.range F.emb := ⟨c, rfl⟩
    rw [hL] at this
    exact this
  refine ⟨fun c => (hmem c).2, fun c hc => ?_⟩
  have hne : F.emb c ≠ 0 := by
    intro h; rw [h, norm_zero] at hc; exact zero_ne_one hc
  have hinvL : (F.emb c)⁻¹ ∈ L := inv_mem (hmem c).1
  have hinvn : ‖(F.emb c)⁻¹‖ ≤ 1 := by rw [norm_inv, hc, inv_one]
  have : (F.emb c)⁻¹ ∈ Set.range F.emb := by rw [hL]; exact ⟨hinvL, hinvn⟩
  obtain ⟨d, hd⟩ := this
  have hcd : c * d = 1 := hinj (by rw [map_mul, map_one, hd, mul_inv_cancel₀ hne])
  exact IsUnit.of_mul_eq_one d hcd

private theorem form_lift : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (F : Frame l ι N) (lam : ι → ℕ → ℕ) (jK : F.K →* alg F.O N lam) (b : NablaT F.O N lam →ₛₗ[F.emb] NablaT (PadicAlgCl l) N lam), Function.Injective b → (∀ g x, b (grp F.O N lam g x) = grp (PadicAlgCl l) N lam (fun τ => Matrix.GeneralLinearGroup.map F.emb (g τ)) (b x)) → F.IsJ lam jK → ∀ f : F.G → NablaT (PadicAlgCl l) N lam, F.IsForm lam f → (∀ g, ∃ y, b y = f g) → ∃ x : Forms F.O (A := alg F.O N lam) F.Γ jK (NablaT F.O N lam), ∀ g, b ((x : F.G → NablaT F.O N lam) g) = f g := by
  intro l _ ι _ _ N F lam jK b hb hgrp hJ f hf hex
  choose x hx using hex
  refine ⟨⟨x, ?_⟩, hx⟩
  intro γ g κ
  apply hb
  rw [hx]
  change f _ = b ((jK κ⁻¹ : alg F.O N lam) • x g)
  have e1 : (jK κ⁻¹ : alg F.O N lam) • x g = ((F.chi κ⁻¹ : F.Oˣ) : F.O) • grp F.O N lam (F.kap κ⁻¹) (x g) := by
    rw [hJ κ⁻¹, smul_assoc]
    rfl
  rw [e1, LinearMap.map_smulₛₗ, hgrp, hx]
  have h2 := hf.2 κ⁻¹ (g * κ)
  simp only [Subgroup.coe_inv, mul_inv_cancel_right] at h2
  rw [h2, mul_assoc, hf.1 γ γ.2]

end GlobalTheory.ExpCover


open GlobalTheory.ExpCover in
set_option maxHeartbeats 600000 in
theorem _root_.GlobalTheory.T.maximalIdeals_meeting_subspace_cover : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (G0 : Type) [Group G0] [Fintype G0] (Pl0 : Type) (B : BlockDat K G0 Pl0) (w : HeightOneSpectrum (𝓞 K)) [Fact (Formalism.EigenvalueLevelCeiling.plc w).Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (F : Frame (Formalism.EigenvalueLevelCeiling.plc w) ι N) (lam : ι → ℕ → ℕ) (jK : F.K →* alg F.O N lam) [hm : Module F.T (Forms F.O (A := alg F.O N lam) F.Γ jK (NablaT F.O N lam))] [@IsScalarTower F.O F.T (Forms F.O (A := alg F.O N lam) F.Γ jK (NablaT F.O N lam)) _ hm.toSMul _], F.Ok → F.IsJ lam jK → F.IsHecke lam jK (NablaT F.O N lam) → ∀ (R : Reads F lam B w) (ℓ : Lvl K G0) (Z : Submodule K B.S.Forms), (∀ i, Z ≤ Z.comap (B.op i)) → Covers B ℓ Z w fun m : {m : MaximalSpectrum F.T // ∃ θ, R.Occurs Z θ ∧ F.Over θ m.asIdeal} => haveI := m.1.isMaximal.isPrime; F.setting lam jK m.1.asIdeal := by
  intro K _ _ _ G0 _ _ Pl0 B w _ ι _ _ N F lam jK hm hst hOk hJ hH R ℓ Z hZ J hInc z hz
  have hfZ : B.toF ℓ Z z ∈ Z := toF_mem B ℓ Z z
  have hfN := (mem_cutZ B ℓ Z z).1 hz
  apply final_step
  apply R.del
  obtain ⟨hbinj, hbli, -⟩ := GlobalTheory.LatBC.bc_props F.emb N lam hOk.ring.1
  have hnorm := emb_norm _ ι N F hOk
  obtain ⟨x, hx⟩ := form_lift _ ι N F lam jK (GlobalTheory.LatBC.bc F.emb N lam) hbinj (GlobalTheory.LatBC.bc_grp F.emb N lam) hJ
    (R.rd (B.toF ℓ Z z)) (R.form _) (fun g => (GlobalTheory.LatBC.latN_iff F lam _).1 (R.nab _ hfN g))
  have hfin := forms_fin _ ι N F lam jK hOk
  have hfinV : Module.Finite F.O (NablaT F.O N lam) := GlobalTheory.NablaFin.nablaT_finite F.O N ι lam
  have hxS : (fun g => GlobalTheory.LatBC.bc F.emb N lam ((x : F.G → NablaT F.O N lam) g)) ∈
      Submodule.span (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)) (R.rd '' Z) := by
    have e : (fun g => GlobalTheory.LatBC.bc F.emb N lam ((x : F.G → NablaT F.O N lam) g)) = R.rd (B.toF ℓ Z z) := funext hx
    rw [e]
    exact Submodule.subset_span (Set.mem_image_of_mem _ hfZ)
  have hloc : ∀ (m : Ideal (MvPolynomial F.I F.O)) (hmax : m.IsMaximal) (θ : F.I → PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)), (∀ i, ‖θ i‖ ≤ 1) →
      (∀ p, p ∈ m ↔ ‖MvPolynomial.eval₂ F.emb θ p‖ < 1) →
      (∃ v ∈ Submodule.span (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)) (R.rd '' Z), v ≠ 0 ∧
        ∀ i g, F.emb (F.cst i) • ∑ s ∈ F.tr i, v (g * s) = θ i • v g) →
      (haveI := hmax.isPrime; F.setting lam jK m).Incl (Formalism.EigenvalueLevelCeiling.plc w) J := by
    rintro m hmax θ h1 h2 ⟨v, hvS, hv0, hv⟩
    have h5 := hInc ⟨⟨m, hmax⟩, θ,
      ⟨v, hvS, hv0, isForm_of_span F lam _ (by rintro _ ⟨f, -, rfl⟩; exact R.form f) v hvS, hv⟩, h1, h2⟩
    exact h5
  have k1 := @values_mem_of_local (Formalism.EigenvalueLevelCeiling.plc w) _ F.O F.I F.G (NablaT F.O N lam) (NablaT (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)) N lam)
    _ _ _ _ _ _ hfinV _ _ (Forms F.O (A := alg F.O N lam) F.Γ jK (NablaT F.O N lam))
  have k1b := @k1 hm
  have k2 := @k1b hst hfin F.emb hOk.ring.1 hnorm.1 hnorm.2 (GlobalTheory.LatBC.bc F.emb N lam) hbinj hbli F.tr F.cst
  have k3 := k2 hH.2
  have k3b := k3 (tensSub (deltaIn F.O N lam)) (Submodule.span _ (R.rd '' Z)) (span_stable R Z hZ) x hxS ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : F.O) J
  have k4 := k3b {y | ∀ g, (y : F.G → NablaT F.O N lam) g ∈ tensSub (deltaIn F.O N lam)} (fun _ hy => hy)
  clear k1 k1b k2 k3 k3b
  have k5 := k4 (fun m hmax θ h1 h2 h3 y => by
    have h7 := hloc m hmax θ h1 h2 h3
    unfold HidaSetting.Incl TopIncl locSet at h7
    obtain ⟨x', hx', s, hs⟩ := h7 y
    exact ⟨x', fun g => (Submodule.mem_pi.1 (Submodule.mem_inf.1 hx').2) g (Set.mem_univ _), s, hs⟩)
  have key : ∀ g, ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : F.O) ^ J • (x : F.G → NablaT F.O N lam) g ∈ tensSub (deltaIn F.O N lam) := by
    intro g
    have h7 := k5 g
    rw [Submodule.coe_smul, Pi.smul_apply] at h7
    exact h7
  intro g
  apply latD_of F lam
  refine ⟨_, key g, ?_⟩
  rw [LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, hx, Pi.smul_apply]
  simp only [map_pow, map_natCast]

end
