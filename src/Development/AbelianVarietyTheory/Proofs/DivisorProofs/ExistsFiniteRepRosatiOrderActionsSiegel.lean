module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointActionsOrderFiniteUnramifiedScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorOrderFaithfulLattice

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjugateGramSymm
namespace GlobalTheory.CasimirOrder

open Matrix

variable {O : Type} [Ring O]

def form (s : O →+ O) (φ : O →+ ℤ) : LinearMap.BilinForm ℤ O :=
  LinearMap.mk₂ ℤ (fun u v => φ (s u * v))
    (fun u₁ u₂ v => by simp [map_add (f := _), add_mul])
    (fun c u v => by rw [map_zsmul, smul_mul_assoc, map_zsmul])
    (fun u v₁ v₂ => by simp [mul_add, map_add (f := _)])
    (fun c u v => by rw [mul_smul_comm, map_zsmul])

@[simp] theorem form_apply (s : O →+ O) (φ : O →+ ℤ) (u v : O) : form s φ u v = φ (s u * v) := rfl

variable {r : ℕ}

def gram (x : Fin r → O) (s : O →+ O) (φ : O →+ ℤ) : Matrix (Fin r) (Fin r) ℤ :=
  Matrix.of fun i j => φ (s (x i) * x j)

def casimir (x : Fin r → O) (s : O →+ O) (φ : O →+ ℤ) : O :=
  ∑ i, ∑ j, (gram x s φ).adjugate i j • (s (x i) * x j)

theorem det_smul_eq_sum (x : Module.Basis (Fin r) ℤ O) (b : LinearMap.BilinForm ℤ O)
    (hb : ∀ u v, b u v = b v u) (v : O) :
    (Matrix.of fun i j => b (x i) (x j)).det • v =
      ∑ i, ∑ j, ((Matrix.of fun i j => b (x i) (x j)).adjugate i j * b (x i) v) • x j := by
  classical
  set G : Matrix (Fin r) (Fin r) ℤ := Matrix.of fun i j => b (x i) (x j) with hG
  have hGt : Gᵀ = G := by ext i j; simp [hG, hb]
  have hA : ∀ i j, G.adjugate i j = G.adjugate j i := by
    intro i j
    have h := congrArg (fun M : Matrix (Fin r) (Fin r) ℤ => M i j) (adjugate_transpose G)
    rw [hGt] at h
    simpa using h.symm
  have hv : v = ∑ k, x.repr v k • x k := (x.sum_repr v).symm
  have hb' : ∀ i, b (x i) v = ∑ k, G i k * x.repr v k := by
    intro i; conv_lhs => rw [hv]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [LinearMap.map_smul, smul_eq_mul, mul_comm]; rfl
  have key : ∀ j, ∑ i, G.adjugate i j * b (x i) v = G.det * x.repr v j := by
    intro j
    have e : ∑ i, G.adjugate i j * b (x i) v = ∑ k, (G.adjugate * G) j k * x.repr v k := by
      simp_rw [hb', Finset.mul_sum, Matrix.mul_apply, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
      rw [hA]; ring
    rw [e, adjugate_mul]
    simp [Matrix.smul_apply, Matrix.one_apply]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, key]
  conv_lhs => rw [hv]
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [smul_smul]


open scoped MatrixOrder in
theorem trace_mul_pos_real {n : ℕ} {P H : Matrix (Fin n) (Fin n) ℝ} (hP : P.PosDef) (hH : H.PosSemidef)
    (h0 : H ≠ 0) : 0 < (P * H).trace := by
  obtain ⟨C, hC, rfl⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp hP.isStrictlyPositive
  have e : (star C * C * H).trace = (C * H * Cᴴ).trace := by
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm]; rfl
  have hs := hH.mul_mul_conjTranspose_same C
  rw [e]
  refine hs.trace_nonneg.lt_of_ne fun h => h0 ?_
  have h1 := hs.trace_eq_zero_iff.1 h.symm
  rwa [show Cᴴ = star C from rfl, hC.star.mul_left_eq_zero, hC.mul_right_eq_zero] at h1

theorem posDef_of_int {n : ℕ} (G : Matrix (Fin n) (Fin n) ℤ) (hs : Gᵀ = G)
    (hp : ∀ v : Fin n → ℤ, v ≠ 0 → 0 < v ⬝ᵥ G *ᵥ v) : (G.map (Int.cast : ℤ → ℝ)).PosDef := by
  classical
  have hsym : ∀ y z, Matrix.toBilin' G y z = Matrix.toBilin' G z y := by
    intro y z
    rw [Matrix.toBilin'_apply', Matrix.toBilin'_apply', Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hs,
      dotProduct_comm]
  have hnn : ∀ y, 0 ≤ Matrix.toBilin' G y y := by
    intro y
    by_cases hy : y = 0
    · simp [hy]
    · rw [Matrix.toBilin'_apply']; exact (hp y hy).le
  have hpsd : (G.map (Int.cast : ℤ → ℝ)).PosSemidef := by
    have h := GlobalTheory.gram_posSemidef_of_int_form (Matrix.toBilin' G) hsym hnn (fun u => Pi.single u 1)
    convert h using 1
    ext u v
    simp [Matrix.toBilin'_apply']
  rw [hpsd.posDef_iff_isUnit, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, ← Int.cast_det]
  intro h
  obtain ⟨z, hz, hGz⟩ := Matrix.exists_mulVec_eq_zero_iff.2 (by exact_mod_cast h)
  have h1 := hp z hz
  rw [hGz, dotProduct_zero] at h1
  exact lt_irrefl _ h1

theorem adjugate_posDef {n : ℕ} {P : Matrix (Fin n) (Fin n) ℝ} (hP : P.PosDef) : P.adjugate.PosDef := by
  have hd := hP.det_pos
  have e : P.adjugate = P.det • P⁻¹ := by
    rw [Matrix.inv_def, smul_smul, Ring.inverse_eq_inv', mul_inv_cancel₀ hd.ne', one_smul]
  rw [e]
  exact hP.inv.smul hd

theorem form_symm {s : O →+ O} {φ : O →+ ℤ} (hs : ∀ a b, s (a * b) = s b * s a) (hss : ∀ a, s (s a) = a)
    (hφs : ∀ a, φ (s a) = φ a) (u v : O) : form s φ u v = form s φ v u := by
  simp only [form_apply]
  rw [← hφs (s u * v), hs, hss]

theorem gram_eq (x : Fin r → O) (s : O →+ O) (φ : O →+ ℤ) :
    gram x s φ = Matrix.of fun i j => form s φ (x i) (x j) := rfl

theorem gram_transpose {x : Fin r → O} {s : O →+ O} {φ : O →+ ℤ} (hs : ∀ a b, s (a * b) = s b * s a)
    (hss : ∀ a, s (s a) = a) (hφs : ∀ a, φ (s a) = φ a) : (gram x s φ)ᵀ = gram x s φ := by
  ext i j
  simp only [transpose_apply, gram_eq, of_apply]
  exact form_symm hs hss hφs _ _

theorem adjugate_gram_symm {x : Fin r → O} {s : O →+ O} {φ : O →+ ℤ} (hs : ∀ a b, s (a * b) = s b * s a)
    (hss : ∀ a, s (s a) = a) (hφs : ∀ a, φ (s a) = φ a) (i j : Fin r) :
    (gram x s φ).adjugate i j = (gram x s φ).adjugate j i := by
  have h := congrArg (fun M : Matrix (Fin r) (Fin r) ℤ => M i j) (adjugate_transpose (gram x s φ))
  rw [gram_transpose hs hss hφs] at h
  simpa using h.symm

theorem casimir_star {x : Fin r → O} {s : O →+ O} {φ : O →+ ℤ} (hs : ∀ a b, s (a * b) = s b * s a)
    (hss : ∀ a, s (s a) = a) (hφs : ∀ a, φ (s a) = φ a) : s (casimir x s φ) = casimir x s φ := by
  unfold casimir
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_zsmul, hs, hss]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    rw [adjugate_gram_symm hs hss hφs]

theorem quad_eq (x : Fin r → O) (b : LinearMap.BilinForm ℤ O) (v : Fin r → ℤ) :
    v ⬝ᵥ (Matrix.of fun i j => b (x i) (x j)) *ᵥ v = b (∑ i, v i • x i) (∑ j, v j • x j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dotProduct, mulVec, of_apply, map_sum, LinearMap.sum_apply, LinearMap.map_smul,
    LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem posDef_gram (x : Module.Basis (Fin r) ℤ O) (b : LinearMap.BilinForm ℤ O) (hb : ∀ u v, b u v = b v u)
    (hpos : ∀ w, w ≠ 0 → 0 < b w w) :
    ((Matrix.of fun i j => b (x i) (x j)).map (Int.cast : ℤ → ℝ)).PosDef := by
  refine posDef_of_int _ (by ext i j; simp [hb]) fun v hv => ?_
  rw [quad_eq]
  refine hpos _ fun h => hv ?_
  have := (Fintype.linearIndependent_iff.1 x.linearIndependent) v h
  exact funext this

end GlobalTheory.CasimirOrder
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpanningPosDefRelationHarrisTaylorOrder
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceCompPosOfAdjoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.UPel.HT

theorem trace_comp_pos_of_adjoint {V : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hs : ∀ u v, g u v = g v u) (hp : ∀ u, u ≠ 0 → 0 < g u u)
    (T T' : V →ₗ[ℝ] V) (hadj : ∀ u v, g (T u) v = g u (T' v)) (hT' : T' ≠ 0) :
    0 < LinearMap.trace ℝ V (T ∘ₗ T') := by
  letI core : InnerProductSpace.Core ℝ V :=
    { inner := fun x y => g x y
      conj_inner_symm := fun x y => by simpa using hs y x
      re_inner_nonneg := fun x => by
        by_cases h : x = 0
        · simp [h]
        · simpa using (hp x h).le
      add_left := fun x y z => by simp
      smul_left := fun x y r => by simp
      definite := fun x hx => by
        by_contra h
        exact (hp x h).ne' hx }
  letI : NormedAddCommGroup V := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)
  letI : InnerProductSpace ℝ V := InnerProductSpace.ofCore core.toCore
  let b := stdOrthonormalBasis ℝ V
  rw [LinearMap.trace_eq_sum_inner _ b]
  have key : ∀ i, ⟪b i, (T ∘ₗ T') (b i)⟫_ℝ = g (T' (b i)) (T' (b i)) := by
    intro i
    show g (b i) (T (T' (b i))) = _
    rw [hs, hadj]
  simp only [key]
  have hnn : ∀ i, 0 ≤ g (T' (b i)) (T' (b i)) := fun i => by
    by_cases h : T' (b i) = 0
    · simp [h]
    · exact (hp _ h).le
  obtain ⟨i, hi⟩ : ∃ i, T' (b i) ≠ 0 := by
    by_contra h
    push_neg at h
    apply hT'
    exact b.toBasis.ext (fun i => by simpa using h i)
  exact Finset.sum_pos' (fun i _ => hnn i) ⟨i, Finset.mem_univ _, hp _ hi⟩

theorem trace_mul_star_pos : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (x : D.O), x ≠ 0 →
    0 < LinearMap.trace ℤ D.La (DistribSMul.toLinearMap ℤ D.La (x * (D.star x).unop)) := by
  intro p _ D x hx
  haveI := D.freeLa
  haveI := D.finLa
  obtain ⟨J, hJJ, hJinv, hpos, hcomm, -⟩ := D.dom
  let A : D.O → (ℝ ⊗[ℤ] D.La →ₗ[ℝ] ℝ ⊗[ℤ] D.La) := fun b =>
    (DistribSMul.toLinearMap ℤ D.La b).baseChange ℝ
  have hcomp : A x ∘ₗ A (D.star x).unop =
      (DistribSMul.toLinearMap ℤ D.La (x * (D.star x).unop)).baseChange ℝ := by
    clear hcomm hpos hJinv hJJ
    simp only [A]
    rw [← LinearMap.baseChange_comp]
    congr 1
    ext y
    show x • ((D.star x).unop • y) = (x * (D.star x).unop) • y
    rw [mul_smul]
  have hA : ∀ b (r : ℝ) (y : D.La), A b (r ⊗ₜ y) = r ⊗ₜ (b • y) := fun _ _ _ => rfl
  have hAJ : ∀ b, J ∘ₗ A b = A b ∘ₗ J := fun b => hcomm b (A b) (fun y => rfl)
  have hEF : ∀ y z : D.La, D.EF y z = - D.EF z y := by
    intro y z
    have h := D.alt (y + z)
    simp only [map_add (f := _), LinearMap.add_apply, D.alt y, D.alt z, zero_add, add_zero] at h
    omega
  have hanti : ∀ u v, D.EF.baseChange ℝ u v = - D.EF.baseChange ℝ v u := by
    intro u v
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul r y =>
      induction v using TensorProduct.induction_on with
      | zero => simp
      | tmul s z =>
        rw [LinearMap.BilinForm.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul, hEF y z]
        simp only [zsmul_eq_mul, Int.cast_neg]
        ring
      | add v w hv hw =>
        simp only [map_add (f := _), LinearMap.add_apply]
        rw [hv, hw]
        ring
    | add u w hu hw =>
      simp only [map_add (f := _), LinearMap.add_apply]
      rw [hu, hw]
      ring
  have hadjB : ∀ b u v, D.EF.baseChange ℝ (A b u) v = D.EF.baseChange ℝ u (A (D.star b).unop v) := by
    intro b u v
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul r y =>
      induction v using TensorProduct.induction_on with
      | zero => simp
      | tmul s z =>
        rw [hA, hA, LinearMap.BilinForm.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul, D.adj]
      | add v w hv hw => simp only [map_add (f := _), LinearMap.add_apply, hv, hw]
    | add u w hu hw => simp only [map_add (f := _), LinearMap.add_apply, hu, hw]
  have hsym : ∀ u v, D.EF.baseChange ℝ (J u) v = D.EF.baseChange ℝ (J v) u := by
    intro u v
    rw [← hJinv (J v) u, hJJ, map_neg, LinearMap.neg_apply, hanti v (J u), neg_neg]
  have hadjg : ∀ u v, (D.EF.baseChange ℝ ∘ₗ J) (A x u) v =
      (D.EF.baseChange ℝ ∘ₗ J) u (A (D.star x).unop v) := by
    intro u v
    simp only [LinearMap.comp_apply]
    rw [← LinearMap.comp_apply J (A x), hAJ, LinearMap.comp_apply, hadjB]
  have hinj : ∀ y : D.La, (1 : ℝ) ⊗ₜ[ℤ] y = 0 → y = 0 := by
    intro y hy
    refine (Module.forall_dual_apply_eq_zero_iff ℤ y).1 fun φ => ?_
    have h := congrArg (fun t => TensorProduct.rid ℤ ℝ (LinearMap.baseChange ℝ φ t)) hy
    simp only [LinearMap.baseChange_tmul, TensorProduct.rid_tmul, map_zero] at h
    simpa using h
  have hT' : A (D.star x).unop ≠ 0 := by
    intro h0
    apply hx
    have hz : ∀ y : D.La, (D.star x).unop • y = 0 := fun y => hinj _ (by
      have := LinearMap.congr_fun h0 ((1 : ℝ) ⊗ₜ y)
      rwa [hA, LinearMap.zero_apply] at this)
    have h1 := GlobalTheory.T.harrisTaylor_order_faithful_lattice p D _ hz
    rw [← D.star_star x, h1]
    simp
  have htr := trace_comp_pos_of_adjoint (D.EF.baseChange ℝ ∘ₗ J)
    (fun u v => by simp only [LinearMap.comp_apply]; exact hsym u v)
    (fun u hu => by simpa only [LinearMap.comp_apply] using hpos u hu)
    (A x) (A (D.star x).unop) hadjg hT'
  rw [hcomp, LinearMap.trace_baseChange] at htr
  simpa using htr

end GlobalTheory.UPel.HT
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCasimirElementCentral
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCasimirElementCentral
open GlobalTheory.CasimirOrder

namespace GlobalTheory.CasimirOrder

open Matrix

theorem casimir_central : ∀ {O : Type} [Ring O] {r : ℕ} (x : Module.Basis (Fin r) ℤ O) (s : O →+ O) (φ : O →+ ℤ),
    (∀ a b, s (a * b) = s b * s a) → (∀ a, s (s a) = a) → (∀ a b, φ (a * b) = φ (b * a)) →
    (∀ a, φ (s a) = φ a) → (∀ a, a ≠ 0 → 0 < φ (s a * a)) →
    ∀ a, a * casimir (⇑x) s φ = casimir (⇑x) s φ * a := by
  intro O _ r x s φ hs hss hφc hφs hpos a
  classical
  set b := form s φ with hbdef
  have hb : ∀ u v, b u v = b v u := form_symm hs hss hφs
  set G := gram (⇑x) s φ with hGdef
  have hA : ∀ i j, G.adjugate i j = G.adjugate j i := adjugate_gram_symm hs hss hφs
  have hds : ∀ v, G.det • v = ∑ i, ∑ j, (G.adjugate i j * b (x i) v) • x j :=
    det_smul_eq_sum x b hb
  have hδ : G.det ≠ 0 := by
    have h := (posDef_gram x b hb (fun w hw => hpos w hw)).det_pos
    rw [← Int.cast_det] at h
    exact_mod_cast h.ne'
  haveI : Module.Free ℤ O := Module.Free.of_basis x
  have htf : Function.Injective (fun v : O => G.det • v) := smul_right_injective O hδ
  have hbid : ∀ u v, b u (v * s a) = b v (u * a) := by
    intro u v
    rw [hb v]
    simp only [hbdef, form_apply]
    rw [hs, ← mul_assoc, hφc, ← mul_assoc]
  set A := G.adjugate with hAdef
  set F : Fin r → Fin r → Fin r → Fin r → O :=
    fun i j k l => (A i j * (A k l * b (x k) (x i * s a))) • (s (x l) * x j) with hF
  have key1 : ∀ i j, G.det • (A i j • (a * (s (x i) * x j))) = ∑ k, ∑ l, F i j k l := by
    intro i j
    have e : a * (s (x i) * x j) = s (x i * s a) * x j := by rw [hs, hss, mul_assoc]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e, smul_comm, show G.det • (s (x i * s a) * x j) = s (G.det • (x i * s a)) * x j by
      rw [map_zsmul, smul_mul_assoc], hds, map_sum, Finset.sum_mul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_mul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_zsmul, smul_mul_assoc, smul_smul]
  have key2 : ∀ p q, G.det • (A p q • (s (x p) * x q * a)) = ∑ i, ∑ j, F i j q p := by
    intro p q
    rw [smul_comm, mul_assoc, ← mul_smul_comm, hds, Finset.mul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_smul_comm, smul_smul, hF, hA p q, ← hbid]
    ring_nf
  apply htf
  simp only
  have L : G.det • (a * casimir (⇑x) s φ) = ∑ i, ∑ j, ∑ k, ∑ l, F i j k l := by
    unfold casimir
    rw [← hGdef, ← hAdef, Finset.mul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_smul_comm, key1]
  have R : G.det • (casimir (⇑x) s φ * a) = ∑ l, ∑ k, ∑ i, ∑ j, F i j k l := by
    unfold casimir
    rw [← hGdef, ← hAdef, Finset.sum_mul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_mul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [smul_mul_assoc, key2]
  rw [L, R]
  calc ∑ i, ∑ j, ∑ k, ∑ l, F i j k l = ∑ i, ∑ k, ∑ j, ∑ l, F i j k l :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ i, ∑ k, ∑ l, ∑ j, F i j k l :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ l, ∑ j, F i j k l := Finset.sum_comm
    _ = ∑ k, ∑ l, ∑ i, ∑ j, F i j k l := Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ l, ∑ k, ∑ i, ∑ j, F i j k l := Finset.sum_comm

end GlobalTheory.CasimirOrder
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCasimirElementCentralStatement
open GlobalTheory.CasimirOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralCasimirElement_central : ∀ {O : Type} [Ring O] {r : ℕ} (x : Module.Basis (Fin r) ℤ O) (s : O →+ O) (φ : O →+ ℤ), (∀ a b, s (a * b) = s b * s a) → (∀ a, s (s a) = a) → (∀ a b, φ (a * b) = φ (b * a)) → (∀ a, φ (s a) = φ a) → (∀ a, a ≠ 0 → 0 < φ (s a * a)) → ∀ a, a * casimir (⇑x) s φ = casimir (⇑x) s φ * a := by
  first | (exact @GlobalTheory.CasimirOrder.casimir_central) | (exact GlobalTheory.CasimirOrder.casimir_central) | (intros; apply GlobalTheory.CasimirOrder.casimir_central  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCasimirElementMulPos
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCasimirElementMulPos
open GlobalTheory.CasimirOrder

namespace GlobalTheory.CasimirOrder

open Matrix

theorem casimir_mul_pos {O : Type} [Ring O] {r : ℕ} (x : Module.Basis (Fin r) ℤ O) (s : O →+ O)
    (φ : O →+ ℤ) (hs : ∀ a b, s (a * b) = s b * s a) (hss : ∀ a, s (s a) = a)
    (_hφc : ∀ a b, φ (a * b) = φ (b * a)) (hφs : ∀ a, φ (s a) = φ a)
    (hp : ∀ a, a ≠ 0 → 0 < φ (s a * a)) :
    ∀ u, u ≠ 0 → 0 < φ (s (casimir (⇑x) s φ * u) * u) := by
  intro u hu
  classical
  set A := (gram (⇑x) s φ).adjugate with hA
  set y : Fin r → O := fun i => x i * u with hy
  set H : Matrix (Fin r) (Fin r) ℝ := Matrix.of fun i j => ((form s φ (y i) (y j) : ℤ) : ℝ) with hHdef
  have key : φ (s (casimir (⇑x) s φ * u) * u) = ∑ i, ∑ j, A i j * form s φ (y j) (y i) := by
    rw [hs]
    unfold casimir
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_zsmul, hs, hss, Finset.mul_sum, Finset.sum_mul, mul_smul_comm,
      smul_mul_assoc, form_apply, hy, smul_eq_mul, hA]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [mul_assoc]
  have hnn : ∀ w, 0 ≤ form s φ w w := by
    intro w
    by_cases hw : w = 0
    · simp [hw]
    · exact (hp w hw).le
  have hHpsd : H.PosSemidef := GlobalTheory.gram_posSemidef_of_int_form (form s φ) (form_symm hs hss hφs) hnn y
  have hP : (A.map (Int.cast : ℤ → ℝ)).PosDef := by
    have h1 := posDef_gram x (form s φ) (form_symm hs hss hφs) (fun w hw => by simpa using hp w hw)
    have e : A.map (Int.cast : ℤ → ℝ) = ((Matrix.of fun i j : Fin r => form s φ (x i) (x j)).map (Int.cast : ℤ → ℝ)).adjugate := by
      rw [hA, gram_eq]
      exact (RingHom.map_adjugate (Int.castRingHom ℝ) (Matrix.of fun i j : Fin r => form s φ (x i) (x j)))
    rw [e]
    exact adjugate_posDef h1
  have hy0 : ∃ i, y i ≠ 0 := by
    by_contra h
    push_neg at h
    apply hu
    calc u = (∑ i, x.repr 1 i • x i) * u := by rw [x.sum_repr, one_mul]
      _ = ∑ i, x.repr 1 i • y i := by rw [Finset.sum_mul]; simp only [hy, smul_mul_assoc]
      _ = 0 := by simp [h]
  have hH0 : H ≠ 0 := by
    obtain ⟨i, hi⟩ := hy0
    intro h
    have h3 := hp _ hi
    have h2 := congrFun (congrFun h i) i
    rw [hHdef] at h2
    simp only [of_apply, form_apply, Matrix.zero_apply, Int.cast_eq_zero] at h2
    omega
  have ht := trace_mul_pos_real hP hHpsd hH0
  have e : (A.map (Int.cast : ℤ → ℝ) * H).trace = ((∑ i, ∑ j, A i j * form s φ (y j) (y i) : ℤ) : ℝ) := by
    simp [Matrix.trace, Matrix.mul_apply, hHdef]
  rw [e] at ht
  rw [key]
  exact_mod_cast ht

end GlobalTheory.CasimirOrder
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCasimirElementMulPosStatement
open GlobalTheory.CasimirOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralCasimirElement_mul_pos : ∀ {O : Type} [Ring O] {r : ℕ} (x : Module.Basis (Fin r) ℤ O) (s : O →+ O) (φ : O →+ ℤ), (∀ a b, s (a * b) = s b * s a) → (∀ a, s (s a) = a) → (∀ a b, φ (a * b) = φ (b * a)) → (∀ a, φ (s a) = φ a) → (∀ a, a ≠ 0 → 0 < φ (s a * a)) → ∀ u, u ≠ 0 → 0 < φ (s (casimir (⇑x) s φ * u) * u) := by
  first | (exact @GlobalTheory.CasimirOrder.casimir_mul_pos) | (exact GlobalTheory.CasimirOrder.casimir_mul_pos) | (intros; apply GlobalTheory.CasimirOrder.casimir_mul_pos  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpanningPosDefRelationHarrisTaylorOrder
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

namespace GlobalTheory.CasimirOrder

open Matrix

variable {O : Type} [Ring O] {r : ℕ}

theorem exists_W_of_casimir (x : Module.Basis (Fin r) ℤ O) (s : O →+ O) (φ : O →+ ℤ)
    (hs : ∀ a b, s (a * b) = s b * s a) (hss : ∀ a, s (s a) = a) (hφs : ∀ a, φ (s a) = φ a)
    (hp : ∀ a, a ≠ 0 → 0 < φ (s a * a))
    (hcen : ∀ a, a * casimir x s φ = casimir x s φ * a)
    (hpos : ∀ u, u ≠ 0 → 0 < φ (s (casimir x s φ * u) * u)) :
    ∃ (W : Matrix (Fin r) (Fin r) ℤ) (d : ℕ), ((W + Wᵀ).map (Int.cast : ℤ → ℝ)).PosDef ∧ 0 < d ∧
      ∑ i, ∑ j, W i j • (s (x i) * x j) = (d : O) := by
  classical
  set C := casimir x s φ with hC
  have sC : s C = C := casimir_star hs hss hφs
  set s' : O →+ O := s.comp (AddMonoidHom.mulLeft C) with hs'
  have hs'a : ∀ u, s' u = s u * C := fun u => by simp [hs', hs, sC]
  have b'symm : ∀ u v, form s' φ u v = form s' φ v u := by
    intro u v
    simp only [form_apply, hs'a]
    rw [← hφs (s u * C * v), hs, hs, hss, sC, ← _root_.mul_assoc]
  have bsymm := form_symm hs hss hφs
  set G := gram (⇑x) s φ with hG
  set G' := gram (⇑x) s' φ with hG'
  have hGpd : (G.map (Int.cast : ℤ → ℝ)).PosDef :=
    posDef_gram x (form s φ) bsymm fun w hw => by simpa using hp w hw
  have hG'pd : (G'.map (Int.cast : ℤ → ℝ)).PosDef := by
    refine posDef_gram x (form s' φ) b'symm fun w hw => ?_
    have h := hpos w hw
    simp only [form_apply, hs'a]
    rwa [hs, sC] at h
  have hδ : 0 < G.det := by
    have := hGpd.det_pos
    rw [← Int.cast_det] at this
    exact_mod_cast this
  have hδ' : 0 < G'.det := by
    have := hG'pd.det_pos
    rw [← Int.cast_det] at this
    exact_mod_cast this
  set A := G.adjugate with hA
  set A' := G'.adjugate with hA'
  have hAs : ∀ i j, A i j = A j i := adjugate_gram_symm hs hss hφs
  have hG't : G'ᵀ = G' := by
    ext i j
    simp only [transpose_apply, hG', gram_eq, of_apply]
    exact b'symm _ _
  have hA's : ∀ i j, A' i j = A' j i := by
    intro i j
    have h := congrArg (fun M : Matrix (Fin r) (Fin r) ℤ => M i j) (adjugate_transpose G')
    rw [hG't] at h
    simpa using h.symm
  have L1' : ∀ v, G'.det • v = ∑ i, ∑ j, (A' i j * φ (s (x i) * C * v)) • x j := by
    intro v
    have h := det_smul_eq_sum x (form s' φ) b'symm v
    rw [← gram_eq] at h
    simpa only [form_apply, hs'a] using h
  have L1 : ∀ v, G.det • v = ∑ i, ∑ j, (A i j * φ (s (x i) * v)) • x j := by
    intro v
    have h := det_smul_eq_sum x (form s φ) bsymm v
    rw [← gram_eq] at h
    simpa only [form_apply] using h
  set C₁ : O := ∑ i, ∑ j, A' i j • (s (x i) * x j) with hC₁
  have lhs : G'.det • C = ∑ k, ∑ l, ∑ i, ∑ j,
      (A k l * (A' i j * φ (s (x i) * C * x l))) • (s (x k) * x j) := by
    conv_lhs => rw [hC, casimir]
    simp only [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [smul_comm, ← mul_smul_comm, L1' (x l), Finset.mul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_smul_comm, smul_smul]
  have rhs : C * (G.det • C₁) = ∑ i, ∑ j, ∑ a, ∑ b,
      (A' i j * (A a b * φ (s (x a) * (C * x i)))) • (s (x b) * x j) := by
    rw [hC₁, Finset.smul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.smul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have e : C * (G.det • (A' i j • (s (x i) * x j))) = A' i j • (s (G.det • (C * x i)) * x j) := by
      rw [mul_smul_comm, mul_smul_comm, map_zsmul, smul_mul_assoc, hs, sC, smul_comm, ← _root_.mul_assoc,
        ← hcen]
    rw [e, L1 (C * x i)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_zsmul, Finset.sum_mul, smul_mul_assoc, Finset.smul_sum, smul_smul]
  have swap4 : ∀ f : Fin r → Fin r → Fin r → Fin r → O,
      ∑ k, ∑ l, ∑ i, ∑ j, f k l i j = ∑ i, ∑ j, ∑ l, ∑ k, f k l i j := by
    intro f
    calc ∑ k, ∑ l, ∑ i, ∑ j, f k l i j = ∑ k, ∑ i, ∑ l, ∑ j, f k l i j :=
          Finset.sum_congr rfl fun k _ => Finset.sum_comm
      _ = ∑ k, ∑ i, ∑ j, ∑ l, f k l i j :=
          Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ i, ∑ k, ∑ j, ∑ l, f k l i j := Finset.sum_comm
      _ = ∑ i, ∑ j, ∑ k, ∑ l, f k l i j := Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ i, ∑ j, ∑ l, ∑ k, f k l i j :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm
  have key : G'.det • C = C * (G.det • C₁) := by
    rw [lhs, rhs, swap4]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
    have hb := b'symm (x i) (x l)
    simp only [form_apply, hs'a] at hb
    rw [hAs l k, ← _root_.mul_assoc (s (x l)), hb]
    ring_nf
  have hC1 : G.det • C₁ = ((G'.det : ℤ) : O) := by
    by_contra hne
    have hw : ((G'.det : ℤ) : O) - G.det • C₁ ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
    have h := hpos _ hw
    have h0 : C * (((G'.det : ℤ) : O) - G.det • C₁) = 0 := by
      rw [mul_sub, ← key, ← Int.cast_comm, ← zsmul_eq_mul, sub_self]
    rw [h0, map_zero, zero_mul, map_zero] at h
    exact lt_irrefl _ h
  refine ⟨G.det • A', G'.det.toNat, ?_, by omega, ?_⟩
  · have hadj : (G'.map (Int.cast : ℤ → ℝ)).adjugate = A'.map Int.cast := by
      rw [hA']; exact ((Int.castRingHom ℝ).map_adjugate G').symm
    have e : ((G.det • A' + (G.det • A')ᵀ).map (Int.cast : ℤ → ℝ)) =
        ((2 * G.det : ℤ) : ℝ) • (G'.map (Int.cast : ℤ → ℝ)).adjugate := by
      rw [hadj]
      ext i j
      simp only [Matrix.map_apply, Matrix.add_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul,
        hA's j i]
      push_cast; ring
    rw [e]
    exact (adjugate_posDef hG'pd).smul (by exact_mod_cast (by omega : (0 : ℤ) < 2 * G.det))
  · have e : ∑ i, ∑ j, (G.det • A') i j • (s (x i) * x j) = G.det • C₁ := by
      rw [hC₁, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [Matrix.smul_apply, smul_eq_mul, mul_smul]
    rw [e, hC1, ← Int.cast_natCast, Int.toNat_of_nonneg hδ'.le]

end GlobalTheory.CasimirOrder

namespace GlobalTheory.CasimirOrder

variable {p : ℕ} [Fact p.Prime]

def htStar (D : Datum p) : D.O →+ D.O :=
  (MulOpposite.opAddEquiv.symm.toAddMonoidHom).comp D.star.toAddMonoidHom

noncomputable def htTrace (D : Datum p) : D.O →+ ℤ where
  toFun a := LinearMap.trace ℤ D.La (DistribSMul.toLinearMap ℤ D.La a)
  map_zero' := by
    have : DistribSMul.toLinearMap ℤ D.La (0 : D.O) = 0 := by ext y; exact zero_smul _ _
    rw [this, map_zero]
  map_add' a b := by
    have : DistribSMul.toLinearMap ℤ D.La (a + b) =
        DistribSMul.toLinearMap ℤ D.La a + DistribSMul.toLinearMap ℤ D.La b := by
      ext y; exact add_smul _ _ _
    rw [this, map_add (f := _)]

theorem htTrace_mul_comm (D : Datum p) (a b : D.O) : htTrace D (a * b) = htTrace D (b * a) := by
  haveI := D.freeLa; haveI := D.finLa
  have hm : ∀ a b : D.O, DistribSMul.toLinearMap ℤ D.La (a * b) =
      DistribSMul.toLinearMap ℤ D.La a * DistribSMul.toLinearMap ℤ D.La b := by
    intro a b; ext y; exact mul_smul _ _ _
  show LinearMap.trace ℤ D.La _ = LinearMap.trace ℤ D.La _
  rw [hm, hm, LinearMap.trace_mul_comm]

noncomputable def htForm (D : Datum p) : D.O →+ ℤ := htTrace D + (htTrace D).comp (htStar D)

theorem htStar_mul (D : Datum p) (a b : D.O) : htStar D (a * b) = htStar D b * htStar D a := by
  change (D.star (a * b)).unop = (D.star b).unop * (D.star a).unop
  rw [map_mul, MulOpposite.unop_mul]

theorem htStar_star (D : Datum p) (a : D.O) : htStar D (htStar D a) = a := by
  exact D.star_star a

open scoped TensorProduct in
theorem exists_W_datum (D : Datum p) : ∃ (r : ℕ) (x : Module.Basis (Fin r) ℤ D.O) (W : Matrix (Fin r) (Fin r) ℤ)
    (d : ℕ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef ∧ 0 < d ∧
      ∑ i, ∑ j, W i j • (htStar D (x i) * x j) = (d : D.O) := by
  haveI := D.freeO; haveI := D.finO
  have hs := htStar_mul D
  have hss := htStar_star D
  have hφs : ∀ a, htForm D (htStar D a) = htForm D a := by
    intro a; simp only [htForm, AddMonoidHom.add_apply, AddMonoidHom.comp_apply, hss, add_comm]
  have hφc : ∀ a b, htForm D (a * b) = htForm D (b * a) := by
    intro a b
    simp only [htForm, AddMonoidHom.add_apply, AddMonoidHom.comp_apply, hs]
    rw [htTrace_mul_comm D a b, htTrace_mul_comm D (htStar D b)]
  have hp : ∀ a, a ≠ 0 → 0 < htForm D (htStar D a * a) := by
    have trace_pos (x : D.O) (hx : x ≠ 0) :
        0 < LinearMap.trace ℤ D.La (DistribSMul.toLinearMap ℤ D.La (x * (D.star x).unop)) := by
      have := D.freeLa
      have := D.finLa
      obtain ⟨J, hJJ, hJinv, hpos, hcomm, -⟩ := D.dom
      let A : D.O → (ℝ ⊗[ℤ] D.La →ₗ[ℝ] ℝ ⊗[ℤ] D.La) := fun b =>
        (DistribSMul.toLinearMap ℤ D.La b).baseChange ℝ
      have hcomp : A x ∘ₗ A (D.star x).unop =
          (DistribSMul.toLinearMap ℤ D.La (x * (D.star x).unop)).baseChange ℝ := by
        clear hcomm hpos hJinv hJJ
        simp only [A]
        rw [← LinearMap.baseChange_comp]
        congr 1
        ext y
        show x • ((D.star x).unop • y) = (x * (D.star x).unop) • y
        rw [mul_smul]
      have hA : ∀ b (r : ℝ) (y : D.La), A b (r ⊗ₜ y) = r ⊗ₜ (b • y) := fun _ _ _ => rfl
      have hAJ : ∀ b, J ∘ₗ A b = A b ∘ₗ J := fun b => hcomm b (A b) (fun y => rfl)
      have hEF : ∀ y z : D.La, D.EF y z = - D.EF z y := by
        intro y z
        have h := D.alt (y + z)
        simp only [map_add (f := _), LinearMap.add_apply, D.alt y, D.alt z, zero_add, add_zero] at h
        omega
      have hanti : ∀ u v, D.EF.baseChange ℝ u v = - D.EF.baseChange ℝ v u := by
        intro u v
        induction u using TensorProduct.inductionOn with
        | tmul r y =>
          induction v using TensorProduct.inductionOn with
          | tmul s z =>
            rw [LinearMap.BilinForm.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul, hEF y z]
            simp only [zsmul_eq_mul, Int.cast_neg]
            ring
          | add v w hv hw =>
            simp only [map_add (f := _), LinearMap.add_apply]
            rw [hv, hw]
            ring
        | add u w hu hw =>
          simp only [map_add (f := _), LinearMap.add_apply]
          rw [hu, hw]
          ring
      have hadjB : ∀ b u v, D.EF.baseChange ℝ (A b u) v = D.EF.baseChange ℝ u (A (D.star b).unop v) := by
        intro b u v
        induction u using TensorProduct.inductionOn with
        | tmul r y =>
          induction v using TensorProduct.inductionOn with
          | tmul s z =>
            rw [hA, hA, LinearMap.BilinForm.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul, D.adj]
          | add v w hv hw => simp only [map_add (f := _), hv, hw]
        | add u w hu hw => simp only [map_add (f := _), LinearMap.add_apply, hu, hw]
      have hsym : ∀ u v, D.EF.baseChange ℝ (J u) v = D.EF.baseChange ℝ (J v) u := by
        intro u v
        rw [← hJinv (J v) u, hJJ, map_neg, LinearMap.neg_apply, hanti v (J u), neg_neg]
      have hadjg : ∀ u v, (D.EF.baseChange ℝ ∘ₗ J) (A x u) v =
          (D.EF.baseChange ℝ ∘ₗ J) u (A (D.star x).unop v) := by
        intro u v
        simp only [LinearMap.comp_apply]
        rw [← LinearMap.comp_apply J (A x), hAJ, LinearMap.comp_apply, hadjB]
      have hinj : ∀ y : D.La, (1 : ℝ) ⊗ₜ[ℤ] y = 0 → y = 0 := by
        intro y hy
        refine (Module.forall_dual_apply_eq_zero_iff ℤ y).1 fun φ => ?_
        have h := congrArg (fun t => TensorProduct.rid ℤ ℝ (LinearMap.baseChange ℝ φ t)) hy
        simp only [LinearMap.baseChange_tmul, TensorProduct.rid_tmul, map_zero] at h
        simpa using h
      have hT' : A (D.star x).unop ≠ 0 := by
        intro h0
        apply hx
        have hz : ∀ y : D.La, (D.star x).unop • y = 0 := fun y => hinj _ (by
          have := LinearMap.congr_fun h0 ((1 : ℝ) ⊗ₜ y)
          rwa [hA, LinearMap.zero_apply] at this)
        have h1 := GlobalTheory.T.harrisTaylor_order_faithful_lattice p D _ hz
        rw [← D.star_star x, h1]
        simp
      have htr := trace_comp_pos_of_adjoint (D.EF.baseChange ℝ ∘ₗ J)
        (fun u v => by simp only [LinearMap.comp_apply]; exact hsym u v)
        (fun u hu => by simpa only [LinearMap.comp_apply] using hpos u hu)
        (A x) (A (D.star x).unop) hadjg hT'
      rw [hcomp, LinearMap.trace_baseChange] at htr
      simpa using htr
    intro a ha
    simp only [htForm, AddMonoidHom.add_apply, AddMonoidHom.comp_apply, hs, hss]
    have h' : htTrace D (htStar D a * a) = htTrace D (a * htStar D a) := htTrace_mul_comm D _ _
    have h'' : 0 < htTrace D (a * htStar D a) := trace_pos a ha
    omega
  exact ⟨_, Module.finBasis ℤ D.O, exists_W_of_casimir (Module.finBasis ℤ D.O) (htStar D) (htForm D) hs hss hφs hp
    (GlobalTheory.T.integralCasimirElement_central _ _ _ hs hss hφc hφs hp) (GlobalTheory.T.integralCasimirElement_mul_pos _ _ _ hs hss hφc hφs hp)⟩

end GlobalTheory.CasimirOrder

theorem GlobalTheory.CasimirOrder.exists_posdef_relation : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p), ∃ (r : ℕ) (e : Fin r → D.Oᵐᵒᵖ) (W : Matrix (Fin r) (Fin r) ℤ) (d : ℕ), Submodule.span ℤ (Set.range e) = ⊤ ∧ ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef ∧ 0 < d ∧ ∑ i, ∑ j, W i j • (e j * MulOpposite.op ((D.star (e i).unop).unop)) = (d : D.Oᵐᵒᵖ) := by
  intro p _ D
  obtain ⟨r, x, W, d, hW, hd, hsum⟩ := GlobalTheory.CasimirOrder.exists_W_datum D
  refine ⟨_, fun i => MulOpposite.op (x i), W, d, ?_, hW, hd, ?_⟩
  · have h := x.mulOpposite.span_eq
    convert h using 3
    all_goals first
      | exact Subsingleton.elim _ _
      | (funext i; simp)
  · rw [← MulOpposite.op_natCast, ← hsum, Finset.op_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.op_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [MulOpposite.op_smul, MulOpposite.op_mul]
    rfl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpanningPosDefRelationHarrisTaylorOrderStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_spanning_posDef_relation_harrisTaylorOrder : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p), ∃ (r : ℕ) (e : Fin r → D.Oᵐᵒᵖ) (W : Matrix (Fin r) (Fin r) ℤ) (d : ℕ), Submodule.span ℤ (Set.range e) = ⊤ ∧ ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef ∧ 0 < d ∧ ∑ i, ∑ j, W i j • (e j * MulOpposite.op ((D.star (e i).unop).unop)) = (d : D.Oᵐᵒᵖ) := by
  first | (exact @GlobalTheory.CasimirOrder.exists_posdef_relation) | (exact GlobalTheory.CasimirOrder.exists_posdef_relation) | (intros; apply GlobalTheory.CasimirOrder.exists_posdef_relation  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteRepRosatiOrderActionsSiegel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

noncomputable section

namespace GlobalTheory.UPel.HT

open GlobalTheory.EndLoc

variable {p : ℕ} [Fact p.Prime] {S : Scheme.{0}}

def opBar (D : Datum p) (a : D.Oᵐᵒᵖ) : D.Oᵐᵒᵖ := MulOpposite.op ((D.star a.unop).unop)

theorem opBar_add (D : Datum p) (a b : D.Oᵐᵒᵖ) : opBar D (a + b) = opBar D a + opBar D b := by
  simp [opBar]

theorem isRAct_of_oActN (D : Datum p) {A : Over S} [GrpObj A] (act : OActN D.O A) :
    IsRAct A (fun a : D.Oᵐᵒᵖ => act.act a.unop) :=
  ⟨fun _ => act.hom _, act.one, fun a b => act.mul b.unop a.unop, fun a b => act.add _ _⟩

theorem adj_of_rosatiFor (D : Datum p) {A : Over S} [GrpObj A] (act : OActN D.O A) (P : LB (G2 A).left)
    (h : RosatiFor D act P) : Adj A P (opBar D) (fun a : D.Oᵐᵒᵖ => act.act a.unop) :=
  fun a => h a.unop

def oActNOfIsRAct (D : Datum p) {A : Over S} [GrpObj A] {act : D.Oᵐᵒᵖ → (A ⟶ A)} (h : IsRAct A act) :
    OActN D.O A where
  act c := act (MulOpposite.op c)
  hom c := h.1 _
  one := h.2.1
  mul b c := h.2.2.1 (MulOpposite.op c) (MulOpposite.op b)
  add b c := h.2.2.2 _ _

theorem rosatiFor_of_adj (D : Datum p) {A : Over S} [GrpObj A] {act : D.Oᵐᵒᵖ → (A ⟶ A)} (h : IsRAct A act)
    (P : LB (G2 A).left) (ha : Adj A P (opBar D) act) : RosatiFor D (oActNOfIsRAct D h) P :=
  fun c => ha (MulOpposite.op c)

theorem exists_finite_rep_oActN_rosati : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (h M : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Scheme.{0}) [IsLocallyNoetherian S] (s₁ : S ⟶ Sp B) (c : SiegPre h M ζ s₁), Out.RelAmple c.A c.diag → ∃ (H : Scheme.{0}) (πH : H ⟶ S) (AH : Over H) (_ : GrpObj AH) (_ : IsCommMonObj AH) (φH : AH.left ⟶ c.A.left) (φ₂H : (G2 AH).left ⟶ (G2 c.A).left) (actH : OActN D.O AH), IsFinite πH ∧ IsAbelianScheme AH ∧ IsGrpPullback AH c.A πH φH ∧ IsSquare φH φ₂H ∧ RosatiFor D actH (c.P.pull φ₂H) ∧ ∀ (T : Scheme.{0}) (g : T ⟶ S) (AT : Over T) [GrpObj AT] (φ : AT.left ⟶ c.A.left) (φ₂ : (G2 AT).left ⟶ (G2 c.A).left) (act : OActN D.O AT), IsGrpPullback AT c.A g φ → IsSquare φ φ₂ → RosatiFor D act (c.P.pull φ₂) → ∃! z : T ⟶ H, z ≫ πH = g ∧ ∃ ψ : AT.left ⟶ AH.left, IsGrpPullback AT AH z ψ ∧ ψ ≫ φH = φ ∧ ∀ a : D.O, (act.act a).left ≫ ψ = ψ ≫ (actH.act a).left := by
  intro p _ D h M B _ ζ S _ s₁ c hample
  obtain ⟨r, e, W, d, hspan, hpos, hd, hsum⟩ := GlobalTheory.T.exists_spanning_posDef_relation_harrisTaylorOrder p D
  obtain ⟨R, hfin, -⟩ := GlobalTheory.T.adjointActions_order_finite_unramified_scheme S c.A c.P c.ab c.isLB c.rig₁ c.rig₂ c.symm hample D.Oᵐᵒᵖ (opBar D) r e W d
    (opBar_add D) hspan hpos hd hsum
  have hcomm : IsCommMonObj R.AH := GlobalTheory.PolPull.isCommMonObj_of_isGrpPullback R.pb
  refine ⟨R.H, R.π, R.AH, R.grp, hcomm, R.φ, R.φ₂, oActNOfIsRAct D R.isAct, hfin,
    GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback c.ab R.pb, R.pb, R.sq, rosatiFor_of_adj D R.isAct _ R.adj, ?_⟩
  intro T g AT _ φ φ₂ act hpb hsq hros
  obtain ⟨z, ⟨hz, ψ, hψ, hψφ, hψa⟩, huniq⟩ :=
    R.rep T g AT φ φ₂ _ hpb hsq (isRAct_of_oActN D act) (adj_of_rosatiFor D act _ hros)
  refine ⟨z, ⟨hz, ψ, hψ, hψφ, fun a => hψa (MulOpposite.op a)⟩, ?_⟩
  rintro z' ⟨hz', ψ', hψ', hψφ', hψa'⟩
  exact huniq z' ⟨hz', ψ', hψ', hψφ', fun a => hψa' a.unop⟩

end GlobalTheory.UPel.HT
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteRepRosatiOrderActionsSiegelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_rep_rosati_orderActions_siegel : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (h M : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Scheme.{0}) [IsLocallyNoetherian S] (s₁ : S ⟶ Sp B) (c : SiegPre h M ζ s₁), Out.RelAmple c.A c.diag → ∃ (H : Scheme.{0}) (πH : H ⟶ S) (AH : Over H) (_ : GrpObj AH) (_ : IsCommMonObj AH) (φH : AH.left ⟶ c.A.left) (φ₂H : (G2 AH).left ⟶ (G2 c.A).left) (actH : OActN D.O AH), IsFinite πH ∧ IsAbelianScheme AH ∧ IsGrpPullback AH c.A πH φH ∧ IsSquare φH φ₂H ∧ RosatiFor D actH (c.P.pull φ₂H) ∧ ∀ (T : Scheme.{0}) (g : T ⟶ S) (AT : Over T) [GrpObj AT] (φ : AT.left ⟶ c.A.left) (φ₂ : (G2 AT).left ⟶ (G2 c.A).left) (act : OActN D.O AT), IsGrpPullback AT c.A g φ → IsSquare φ φ₂ → RosatiFor D act (c.P.pull φ₂) → ∃! z : T ⟶ H, z ≫ πH = g ∧ ∃ ψ : AT.left ⟶ AH.left, IsGrpPullback AT AH z ψ ∧ ψ ≫ φH = φ ∧ ∀ a : D.O, (act.act a).left ≫ ψ = ψ ≫ (actH.act a).left := by
  first | (exact @GlobalTheory.UPel.HT.exists_finite_rep_oActN_rosati) | (exact GlobalTheory.UPel.HT.exists_finite_rep_oActN_rosati) | (intros; apply GlobalTheory.UPel.HT.exists_finite_rep_oActN_rosati  <;> assumption)
end
