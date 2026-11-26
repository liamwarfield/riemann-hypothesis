module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernPolyTopDensityBoundedDomainInvariant
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointClassDensityHodgeUniformisationEqModel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockSymApply
set_option autoImplicit false

noncomputable section

open MvPolynomial

namespace GlobalTheory.DomainDens

def blockSym {ι : Type} {p q n : ℕ} [Fintype ι] (h : Fintype.card (ι × Fin p × Fin q) = n) (τ : ι) :
    Matrix (Fin p) (Fin p) (MvPolynomial (Fin n × Fin n) ℂ) :=
  Matrix.of fun i j => ∑ b : Fin q,
    X (Fintype.equivFinOfCardEq h (τ, i, b), Fintype.equivFinOfCardEq h (τ, j, b))

theorem blockSym_apply {ι : Type} {p q n : ℕ} [Fintype ι] (h : Fintype.card (ι × Fin p × Fin q) = n) (τ : ι)
    (i j : Fin p) : blockSym h τ i j =
      ∑ b : Fin q, X (Fintype.equivFinOfCardEq h (τ, i, b), Fintype.equivFinOfCardEq h (τ, j, b)) := rfl

end GlobalTheory.DomainDens
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockGraph
set_option autoImplicit false

noncomputable section

open MvPolynomial

namespace GlobalTheory.CayleyBlock

def dList {σ : Type} [DecidableEq σ] (l : List σ) : Module.End ℂ (MvPolynomial σ ℂ) :=
  (l.map fun v => ((pderiv v : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ)) :
    MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ)).prod

def smallList {p q : ℕ} (τ : Fin q → Equiv.Perm (Fin p)) : List (Fin p × Fin p) :=
  (List.finRange q).flatMap fun b => (List.finRange p).map fun j => (τ b j, j)

def bigList {p q : ℕ} (τ : Fin q → Equiv.Perm (Fin p)) : List (Fin q × Fin p × Fin p) :=
  (List.finRange q).flatMap fun b => (List.finRange p).map fun j => (b, τ b j, j)

def blockGraph {p q : ℕ} (τ : Fin q → Equiv.Perm (Fin p)) : Fin q × Fin p × Fin p →₀ ℕ :=
  ∑ b, ∑ j, Finsupp.single (b, τ b j, j) 1

def sumMap (p q : ℕ) : MvPolynomial (Fin p × Fin p) ℂ →ₐ[ℂ] MvPolynomial (Fin q × Fin p × Fin p) ℂ :=
  aeval fun x => ∑ b, X (b, x.1, x.2)

def blockEmb {p q : ℕ} (h1 : Fintype.card (Unit × Fin p × Fin q) = p * q) :
    Fin q × Fin p × Fin p → Fin (p * q) × Fin (p * q) :=
  fun x => (Fintype.equivFinOfCardEq h1 ((), x.2.1, x.1), Fintype.equivFinOfCardEq h1 ((), x.2.2, x.1))

def sgnProd {p q : ℕ} (τ : Fin q → Equiv.Perm (Fin p)) : ℤ := ((∏ b, Equiv.Perm.sign (τ b) : ℤˣ) : ℤ)

end GlobalTheory.CayleyBlock
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernTopDensityModelMetricOrigin
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopDegreeFormCoeffBlockSymbolDetPowCayley
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeffComposedPartialDerivListOfNodup
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeffComposedPartialDerivListOfNodup
set_option autoImplicit false

open MvPolynomial ReciprocityTheory.PGsh GlobalTheory.CayleyBlock

namespace GlobalTheory.CayleyBlock

theorem coeff_dList_of_nodup {σ : Type} [DecidableEq σ] (l : List σ) (hl : l.Nodup) (m : σ →₀ ℕ)
    (hm : ∀ v ∈ l, m v = 0) (G : MvPolynomial σ ℂ) :
    AddMonoidAlgebra.coeff (dList l G) m = AddMonoidAlgebra.coeff G (m + (l.map fun v => Finsupp.single v 1).sum) := by
  induction l generalizing m with
  | nil => simp [dList]
  | cons v l ih =>
    have hc : dList (v :: l) G = pderiv v (dList l G) := by
      simp [dList]
    rw [List.nodup_cons] at hl
    have h0 : m v = 0 := hm v (List.mem_cons_self ..)
    have h1 : ∀ w ∈ l, (m + Finsupp.single v 1 : σ →₀ ℕ) w = 0 := by
      intro w hw
      have hne : w ≠ v := fun h => hl.1 (h ▸ hw)
      rw [Finsupp.add_apply, hm w (List.mem_cons_of_mem _ hw), Finsupp.single_eq_of_ne hne, add_zero]
    rw [hc, MvPolynomial.coeff_pderiv, ih hl.2 _ h1, h0, List.map_cons, List.sum_cons, add_assoc]
    simp

end GlobalTheory.CayleyBlock
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeffComposedPartialDerivListOfNodupStatement
open MvPolynomial ReciprocityTheory.PGsh GlobalTheory.CayleyBlock
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_composedPartialDerivList_of_nodup : ∀ {σ : Type} [DecidableEq σ] (l : List σ), l.Nodup → ∀ (m : σ →₀ ℕ), (∀ v ∈ l, m v = 0) → ∀ (G : MvPolynomial σ ℂ), AddMonoidAlgebra.coeff (dList l G) m = AddMonoidAlgebra.coeff G (m + (l.map fun v => Finsupp.single v 1).sum) := by
  first | exact @GlobalTheory.CayleyBlock.coeff_dList_of_nodup | exact GlobalTheory.CayleyBlock.coeff_dList_of_nodup | (intros; apply GlobalTheory.CayleyBlock.coeff_dList_of_nodup <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopDegreeFormCoeffRenameCayleyBlockSymbolEmbeddi
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopDegreeFormCoeffRenameCayleyBlockSymbolEmbeddi
set_option autoImplicit false

noncomputable section

open MvPolynomial ReciprocityTheory.PGsh GlobalTheory.CayleyBlock

namespace GlobalTheory.CayleyBlock

namespace TopRename

variable {p q : ℕ} (hc : Fintype.card (Unit × Fin p × Fin q) = p * q)

def idx : Fin p × Fin q ≃ Fin (p * q) :=
  (Equiv.punitProd (Fin p × Fin q)).symm.trans (Fintype.equivFinOfCardEq hc)

theorem blockEmb_eq (x : Fin q × Fin p × Fin p) :
    blockEmb hc x = (idx hc (x.2.1, x.1), idx hc (x.2.2, x.1)) := rfl

theorem blockEmb_injective : Function.Injective (blockEmb hc) := by
  rintro ⟨b, i, j⟩ ⟨b', i', j'⟩ h
  simp only [blockEmb_eq, Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h
  obtain ⟨⟨e1, e2⟩, ⟨e3, -⟩⟩ := h
  subst e1 e2 e3
  rfl

def permOf (τ : Fin q → Equiv.Perm (Fin p)) : Equiv.Perm (Fin (p * q)) :=
  (idx hc).permCongr (Equiv.prodCongrLeft fun b => (τ b)⁻¹)

theorem permOf_apply' (τ : Fin q → Equiv.Perm (Fin p)) (j : Fin p) (b : Fin q) :
    permOf hc τ (idx hc (j, b)) = idx hc ((τ b)⁻¹ j, b) := by
  simp [permOf, Equiv.permCongr_apply]

theorem permOf_apply (τ : Fin q → Equiv.Perm (Fin p)) (i : Fin p) (b : Fin q) :
    permOf hc τ (idx hc (τ b i, b)) = idx hc (i, b) := by
  rw [permOf_apply']
  simp

theorem sign_permOf (τ : Fin q → Equiv.Perm (Fin p)) :
    ((Equiv.Perm.sign (permOf hc τ) : ℤˣ) : ℤ) = sgnProd τ := by
  simp [permOf, Equiv.Perm.sign_permCongr, Equiv.Perm.sign_prodCongrLeft, sgnProd]

theorem permOf_injective : Function.Injective (permOf hc) := by
  intro τ τ' e
  funext b
  have h : ∀ j, (τ b)⁻¹ j = (τ' b)⁻¹ j := by
    intro j
    have := congrArg (fun w : Equiv.Perm (Fin (p * q)) => w (idx hc (j, b))) e
    simp only [permOf_apply'] at this
    exact congrArg Prod.fst ((idx hc).injective this)
  exact inv_inj.mp (Equiv.ext h)

theorem graph_apply' {n : ℕ} (g : Fin n → Fin n) (x y : Fin n) :
    (∑ a, Finsupp.single (a, g a) 1 : Fin n × Fin n →₀ ℕ) (x, y) = if g x = y then 1 else 0 := by
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single x (fun c _ hc => by simp [Finsupp.single_apply, hc]) (by simp)]
  simp [Finsupp.single_apply]

theorem graph_permOf (τ : Fin q → Equiv.Perm (Fin p)) :
    (∑ a, Finsupp.single (a, permOf hc τ a) 1 : Fin (p * q) × Fin (p * q) →₀ ℕ) =
      (blockGraph τ).mapDomain (blockEmb hc) := by
  rw [blockGraph, Finsupp.mapDomain_finsetSum]
  simp_rw [Finsupp.mapDomain_finsetSum, Finsupp.mapDomain_single, blockEmb_eq]
  rw [← (idx hc).sum_comp, ← (Equiv.prodCongrLeft fun b => τ b).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun j _ => ?_
  simp [permOf_apply]

theorem mem_range_of_graph (w : Equiv.Perm (Fin (p * q))) (u : Fin q × Fin p × Fin p →₀ ℕ)
    (h : u.mapDomain (blockEmb hc) = ∑ a, Finsupp.single (a, w a) 1) : ∃ τ, permOf hc τ = w := by
  have hr : ∀ x : Fin p × Fin q, ((idx hc).symm (w (idx hc x))).2 = x.2 := by
    intro x
    have h0 : (∑ a, Finsupp.single (a, w a) 1 : Fin (p * q) × Fin (p * q) →₀ ℕ) (idx hc x, w (idx hc x)) ≠ 0 := by
      rw [graph_apply' (fun a => w a)]
      simp
    rw [← h] at h0
    by_contra hne
    apply h0
    apply Finsupp.mapDomain_notin_range
    rintro ⟨⟨b, i, j⟩, hy⟩
    rw [blockEmb_eq, Prod.mk.injEq] at hy
    apply hne
    have hx : x = (i, b) := ((idx hc).injective hy.1).symm
    rw [← hy.2, Equiv.symm_apply_apply, hx]
  let f : Fin q → Fin p → Fin p := fun b i => ((idx hc).symm (w (idx hc (i, b)))).1
  have hf : ∀ b, Function.Injective (f b) := by
    intro b i i' e
    have : (idx hc).symm (w (idx hc (i, b))) = (idx hc).symm (w (idx hc (i', b))) :=
      Prod.ext e ((hr (i, b)).trans (hr (i', b)).symm)
    simpa using this
  let σ : Fin q → Equiv.Perm (Fin p) := fun b => Equiv.ofBijective (f b) (Finite.injective_iff_bijective.mp (hf b))
  refine ⟨fun b => (σ b)⁻¹, ?_⟩
  ext1 a
  obtain ⟨⟨i, b⟩, rfl⟩ := (idx hc).surjective a
  rw [permOf_apply', inv_inv, ← (idx hc).apply_symm_apply (w (idx hc (i, b)))]
  congr 1
  exact Prod.ext rfl (hr (i, b)).symm

end TopRename


open TopRename in
theorem topCoeff_rename_blockEmb : ∀ {p q : ℕ} (h1 : Fintype.card (Unit × Fin p × Fin q) = p * q)
    (G : MvPolynomial (Fin q × Fin p × Fin p) ℂ), GlobalTheory.GoodMetric.topCoeff (rename (blockEmb h1) G) =
      ∑ τ : Fin q → Equiv.Perm (Fin p), (sgnProd τ : ℂ) * AddMonoidAlgebra.coeff G (blockGraph τ) := by
  intro p q h1 G
  rw [GlobalTheory.GoodMetric.topCoeff]
  symm
  refine Fintype.sum_of_injective (permOf h1) (permOf_injective h1) _ _ ?_ ?_
  · intro w hw
    rw [coeff_rename_eq_zero, mul_zero]
    intro u hu
    obtain ⟨τ, rfl⟩ := mem_range_of_graph h1 w u hu
    exact absurd ⟨τ, rfl⟩ hw
  · intro τ
    rw [graph_permOf, coeff_rename_mapDomain _ (blockEmb_injective h1), ← sign_permOf h1]

end GlobalTheory.CayleyBlock
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopDegreeFormCoeffRenameCayleyBlockSymbolEmbeddiStatement
open MvPolynomial ReciprocityTheory.PGsh GlobalTheory.CayleyBlock
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topDegreeFormCoeff_rename_cayleyBlockSymbolEmbedding : ∀ {p q : ℕ} (h1 : Fintype.card (Unit × Fin p × Fin q) = p * q) (G : MvPolynomial (Fin q × Fin p × Fin p) ℂ), GlobalTheory.GoodMetric.topCoeff (rename (blockEmb h1) G) = ∑ τ : Fin q → Equiv.Perm (Fin p), (sgnProd τ : ℂ) * AddMonoidAlgebra.coeff G (blockGraph τ) := by
  first | exact @GlobalTheory.CayleyBlock.topCoeff_rename_blockEmb | exact GlobalTheory.CayleyBlock.topCoeff_rename_blockEmb | (intros; apply GlobalTheory.CayleyBlock.topCoeff_rename_blockEmb <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CayleyOperatorPowEqSignedSumPartialDerivs
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CayleyOperatorPowEqSignedSumPartialDerivs
open MvPolynomial ReciprocityTheory.PGsh GlobalTheory.CayleyBlock

set_option autoImplicit false

namespace GlobalTheory.CayleyBlock

theorem dList_append' {σ : Type} [DecidableEq σ] (l₁ l₂ : List σ) :
    dList (l₁ ++ l₂) = dList l₁ * dList l₂ := by
  simp [dList, List.map_append, List.prod_append]

theorem smallList_cons' {p q : ℕ} (σ : Equiv.Perm (Fin p)) (τ : Fin q → Equiv.Perm (Fin p)) :
    smallList (Fin.cons σ τ : Fin (q + 1) → Equiv.Perm (Fin p)) =
      (List.finRange p).map (fun j => (σ j, j)) ++ smallList τ := by
  simp [smallList, List.finRange_succ, List.flatMap_cons, List.flatMap_map]

theorem sgnProd_cons' {p q : ℕ} (σ : Equiv.Perm (Fin p)) (τ : Fin q → Equiv.Perm (Fin p)) :
    sgnProd (Fin.cons σ τ : Fin (q + 1) → Equiv.Perm (Fin p)) =
      (Equiv.Perm.sign σ : ℤ) * sgnProd τ := by
  simp [sgnProd, Fin.prod_univ_succ]

theorem cayMono_eq_dList' {p : ℕ} (σ : Equiv.Perm (Fin p)) :
    cayMono p ℂ σ = dList ((List.finRange p).map fun j => (σ j, j)) := by
  simp [cayMono, dList, List.map_map]
  rfl

theorem cayOp_pow_eq_sum (p q : ℕ) :
    cayOp p ℂ ^ q = ∑ τ : Fin q → Equiv.Perm (Fin p), sgnProd τ • dList (smallList τ) := by
  induction q with
  | zero => simp [smallList, sgnProd, dList]
  | succ q ih =>
    rw [pow_succ', ih, cayOp, Finset.sum_mul_sum,
      ← (Fin.consEquiv (fun _ => Equiv.Perm (Fin p))).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => ?_
    change _ = sgnProd (Fin.cons σ τ : Fin (q + 1) → Equiv.Perm (Fin p)) •
      dList (smallList (Fin.cons σ τ : Fin (q + 1) → Equiv.Perm (Fin p)))
    rw [smallList_cons', sgnProd_cons', dList_append', cayMono_eq_dList', smul_mul_smul, mul_smul]

end GlobalTheory.CayleyBlock
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CayleyOperatorPowEqSignedSumPartialDerivsStatement
open MvPolynomial ReciprocityTheory.PGsh GlobalTheory.CayleyBlock
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cayleyOperator_pow_eq_signed_sum_partialDerivs : ∀ (p q : ℕ), cayOp p ℂ ^ q = ∑ τ : Fin q → Equiv.Perm (Fin p), sgnProd τ • dList (smallList τ) := by
  first | exact @GlobalTheory.CayleyBlock.cayOp_pow_eq_sum | exact GlobalTheory.CayleyBlock.cayOp_pow_eq_sum | (intros; apply GlobalTheory.CayleyBlock.cayOp_pow_eq_sum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConstantCoeffCayleyOperatorPowDeterminantPow
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConstantCoeffCayleyOperatorPowDeterminantPow
open MvPolynomial ReciprocityTheory.PGsh GlobalTheory.CayleyBlock

namespace GlobalTheory

theorem cayOp_pow_cayDet_pow (p s k : ℕ) :
    (cayOp p ℂ ^ k) (cayDet p ℂ ^ (s + k)) =
      (∏ t ∈ Finset.range k, ∏ j ∈ Finset.range p, (s + 1 + t + j)) • cayDet p ℂ ^ s := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, ← add_assoc, cayley p ℂ (s + k + 1), Nat.add_sub_cancel,
      map_nsmul, ih, smul_smul, Finset.prod_range_succ]
    congr 1
    rw [mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    ring

theorem prod_succ_mul_factorial (j q : ℕ) :
    (∏ t ∈ Finset.range q, (1 + t + j)) * j.factorial = (q + j).factorial := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Finset.prod_range_succ, mul_right_comm, ih, show q + 1 + j = (q + j) + 1 by ring,
      Nat.factorial_succ]
    ring

theorem constantCoeff_cayOp_pow_cayDet_pow : ∀ (p q : ℕ),
    constantCoeff ((cayOp p ℂ ^ q) (cayDet p ℂ ^ q)) =
      ∏ i ∈ Finset.range p, (((q + i).factorial : ℂ) / i.factorial) := by
  intro p q
  have h := cayOp_pow_cayDet_pow p 0 q
  rw [zero_add] at h
  rw [h, pow_zero, map_nsmul, map_one, nsmul_eq_mul, mul_one, Finset.prod_comm]
  push_cast
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [eq_div_iff (by exact_mod_cast (Nat.factorial_pos j).ne')]
  have := prod_succ_mul_factorial j q
  simp only [zero_add] at *
  exact_mod_cast this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConstantCoeffCayleyOperatorPowDeterminantPowStatement
open MvPolynomial ReciprocityTheory.PGsh GlobalTheory.CayleyBlock
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constantCoeff_cayleyOperator_pow_determinant_pow : ∀ (p q : ℕ), constantCoeff ((cayOp p ℂ ^ q) (cayDet p ℂ ^ q)) = ∏ i ∈ Finset.range p, (((q + i).factorial : ℂ) / i.factorial) := by
  first | exact @GlobalTheory.constantCoeff_cayOp_pow_cayDet_pow | exact GlobalTheory.constantCoeff_cayOp_pow_cayDet_pow | (intros; apply GlobalTheory.constantCoeff_cayOp_pow_cayDet_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopDegreeFormCoeffBlockSymbolDetPowCayley
set_option autoImplicit false

noncomputable section

open MvPolynomial ReciprocityTheory.PGsh

namespace GlobalTheory.CayleyBlock

theorem det_pow_eq {p q : ℕ} (h1 : Fintype.card (Unit × Fin p × Fin q) = p * q) :
    (GlobalTheory.DomainDens.blockSym h1 ()).det ^ q = rename (blockEmb h1) (sumMap p q (cayDet p ℂ ^ q)) := by
  rw [map_pow, map_pow, cayDet, AlgHom.map_det, AlgHom.map_det]
  congr 2
  ext i j
  simp [GlobalTheory.DomainDens.blockSym_apply, sumMap, blockEmb, Matrix.mvPolynomialX]

theorem bigList_nodup {p q : ℕ} (τ : Fin q → Equiv.Perm (Fin p)) : (bigList τ).Nodup := by
  rw [bigList, List.nodup_flatMap]
  refine ⟨fun b _ => (List.nodup_finRange p).map fun j k h => by simpa using congrArg (fun x => x.2.2) h, ?_⟩
  refine (List.nodup_finRange q).imp fun {a b} hab => ?_
  show List.Disjoint _ _
  rw [List.disjoint_left]
  intro x hx hy
  simp only [List.mem_map, List.mem_finRange, true_and] at hx hy
  obtain ⟨j, rfl⟩ := hx
  obtain ⟨k, hk⟩ := hy
  exact hab (congrArg Prod.fst hk).symm

theorem bigList_sum {p q : ℕ} (τ : Fin q → Equiv.Perm (Fin p)) :
    ((bigList τ).map fun v => Finsupp.single v 1).sum = blockGraph τ := by
  simp [bigList, blockGraph, List.map_flatMap, Fin.sum_univ_def, List.map_map, Function.comp_def]
  simp [List.flatMap, List.sum_flatten, List.map_map, Function.comp_def]

theorem pderiv_sumMap {p q : ℕ} (v : Fin q × Fin p × Fin p) (P : MvPolynomial (Fin p × Fin p) ℂ) :
    pderiv v (sumMap p q P) = sumMap p q (pderiv v.2 P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [sumMap]
  | add f g hf hg => simp only [map_add (f := _), hf, hg]
  | mul_X f w hf =>
    simp only [map_mul, Derivation.leibniz, hf, smul_eq_mul, map_add (f := _)]
    congr 1
    simp [sumMap, pderiv_X, Pi.single_apply, Prod.ext_iff]
    by_cases h : w.1 = v.2.1 ∧ w.2 = v.2.2 <;> simp [h, Finset.filter_eq']

theorem dList_sumMap {p q : ℕ} (l : List (Fin q × Fin p × Fin p)) (P : MvPolynomial (Fin p × Fin p) ℂ) :
    dList l (sumMap p q P) = sumMap p q (dList (l.map fun v => v.2) P) := by
  induction l with
  | nil => simp [dList]
  | cons v l ih =>
    simp only [dList, List.map_cons, List.prod_cons, Module.End.mul_apply] at ih ⊢
    rw [ih]
    exact pderiv_sumMap v _

theorem bigList_map {p q : ℕ} (τ : Fin q → Equiv.Perm (Fin p)) : (bigList τ).map (fun v => v.2) = smallList τ := by
  simp [bigList, smallList, List.map_flatMap, List.map_map, Function.comp_def]

theorem constantCoeff_sumMap (p q : ℕ) (P : MvPolynomial (Fin p × Fin p) ℂ) :
    constantCoeff (sumMap p q P) = constantCoeff P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [sumMap]
  | add f g hf hg => simp only [map_add (f := _), hf, hg]
  | mul_X f w hf => simp [sumMap, constantCoeff_X]

end GlobalTheory.CayleyBlock


open GlobalTheory.CayleyBlock ReciprocityTheory.PGsh MvPolynomial in
theorem GlobalTheory.topCoeff_blockSym_det_pow : ∀ (p q : ℕ) (h1 : Fintype.card (Unit × Fin p × Fin q) = p * q),
    GlobalTheory.GoodMetric.topCoeff ((GlobalTheory.DomainDens.blockSym h1 ()).det ^ q) =
      ∏ i ∈ Finset.range p, (((q + i).factorial : ℂ) / i.factorial) := by
  intro p q h1
  rw [det_pow_eq, GlobalTheory.T.topDegreeFormCoeff_rename_cayleyBlockSymbolEmbedding, ← GlobalTheory.T.constantCoeff_cayleyOperator_pow_determinant_pow, GlobalTheory.T.cayleyOperator_pow_eq_signed_sum_partialDerivs, LinearMap.sum_apply]
  have key : ∀ τ : Fin q → Equiv.Perm (Fin p), (sgnProd τ : ℂ) * AddMonoidAlgebra.coeff (sumMap p q (cayDet p ℂ ^ q)) (blockGraph τ) =
      constantCoeff (sgnProd τ • dList (smallList τ) (cayDet p ℂ ^ q)) := by
    intro τ
    rw [← bigList_sum, ← zero_add ((bigList τ).map _).sum, ← GlobalTheory.T.coeff_composedPartialDerivList_of_nodup _ (bigList_nodup τ) 0 (fun _ _ => rfl),
      dList_sumMap, bigList_map, ← constantCoeff_sumMap p q, map_zsmul, zsmul_eq_mul,
      ← map_intCast (C : ℂ →+* MvPolynomial (Fin q × Fin p × Fin p) ℂ), map_mul, constantCoeff_C, constantCoeff_eq]
  set_option synthInstance.maxHeartbeats 100000 in
    simp_rw [LinearMap.smul_apply, key, map_sum]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopDegreeFormCoeffBlockSymbolDetPowCayleyStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topDegreeFormCoeff_blockSymbolDet_pow_cayley : ∀ (p q : ℕ) (h1 : Fintype.card (Unit × Fin p × Fin q) = p * q), GlobalTheory.GoodMetric.topCoeff ((GlobalTheory.DomainDens.blockSym h1 ()).det ^ q) = ∏ i ∈ Finset.range p, (((q + i).factorial : ℂ) / i.factorial) := by
  first | exact @GlobalTheory.topCoeff_blockSym_det_pow | exact GlobalTheory.topCoeff_blockSym_det_pow | (intros; apply GlobalTheory.topCoeff_blockSym_det_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopDegreeFormCoeffProdBlockSymbolDetPow
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopDegreeFormCoeffProdBlockSymbolDetPow
set_option autoImplicit false

noncomputable section

open MvPolynomial

namespace GlobalTheory.BlockTop

section General

variable {α : Type} [Fintype α] [DecidableEq α]

def graph (w : Equiv.Perm α) : α × α →₀ ℕ := ∑ a, Finsupp.single (a, w a) 1

def tc (P : MvPolynomial (α × α) ℂ) : ℂ :=
  ∑ w : Equiv.Perm α, ((Equiv.Perm.sign w : ℤ) : ℂ) * AddMonoidAlgebra.coeff P (graph w)

theorem topCoeff_eq_tc {n : ℕ} (P : MvPolynomial (Fin n × Fin n) ℂ) : GlobalTheory.GoodMetric.topCoeff P = tc P := rfl

theorem tc_sum {κ : Type} (s : Finset κ) (f : κ → MvPolynomial (α × α) ℂ) :
    tc (∑ i ∈ s, f i) = ∑ i ∈ s, tc (f i) := by
  simp only [tc, coeff_sum, Finset.mul_sum]
  exact Finset.sum_comm

theorem tc_monomial (u : α × α →₀ ℕ) (c : ℂ) : tc (monomial u c) = c * tc (monomial u 1) := by
  simp only [tc, coeff_monomial, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  split_ifs <;> ring

theorem graph_apply (w : Equiv.Perm α) (a b : α) : graph w (a, b) = if w a = b then 1 else 0 := by
  rw [graph, Finsupp.finsetSum_apply, Finset.sum_eq_single a (fun c _ hc => by simp [Finsupp.single_apply, hc]) (by simp)]
  simp [Finsupp.single_apply]

theorem tc_rename_equiv {β : Type} [Fintype β] [DecidableEq β] (e : α ≃ β) (P : MvPolynomial (α × α) ℂ) :
    tc (rename (Prod.map e e) P) = tc P := by
  unfold tc
  rw [← (Equiv.permCongr e).sum_comp]
  refine Finset.sum_congr rfl fun v _ => ?_
  have hg : graph (e.permCongr v) = Finsupp.mapDomain (Prod.map e e) (graph v) := by
    unfold graph
    rw [Finsupp.mapDomain_finsetSum]
    simp only [Finsupp.mapDomain_single]
    rw [← e.sum_comp]
    simp [Equiv.permCongr_apply]
  have hinj : Function.Injective (Prod.map e e) := fun x y h => by
    simp only [Prod.map, Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h
    exact Prod.ext h.1 h.2
  rw [hg, coeff_rename_mapDomain _ hinj, Equiv.Perm.sign_permCongr]

theorem prod_monomial' {κ : Type} (s : Finset κ) (f : κ → α × α →₀ ℕ) (c : κ → ℂ) :
    ∏ i ∈ s, (monomial (f i) (c i) : MvPolynomial (α × α) ℂ) = monomial (∑ i ∈ s, f i) (∏ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, ih, monomial_mul, Finset.sum_insert ha, Finset.prod_insert ha]

end General

section Blocks

variable {ι γ : Type} [Fintype ι] [DecidableEq ι] [Fintype γ] [DecidableEq γ]

def emb (τ : ι) (v : γ × γ) : (ι × γ) × (ι × γ) := ((τ, v.1), (τ, v.2))

theorem emb_injective (τ : ι) : Function.Injective (emb (γ := γ) τ) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [emb, Prod.mk.injEq, true_and] at h
  simp [h]

def glue (D : ι → (γ × γ →₀ ℕ)) : (ι × γ) × (ι × γ) →₀ ℕ := ∑ τ, (D τ).mapDomain (emb τ)

theorem glue_emb (D : ι → (γ × γ →₀ ℕ)) (τ : ι) (v : γ × γ) : glue D (emb τ v) = D τ v := by
  unfold glue
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single τ]
  · exact Finsupp.mapDomain_apply_of_injective (emb_injective τ) _ _
  · intro τ' _ hτ'
    apply Finsupp.mapDomain_notin_range
    rintro ⟨u, hu⟩
    simp only [emb, Prod.mk.injEq] at hu
    exact hτ' hu.1.1
  · simp

theorem glue_off (D : ι → (γ × γ →₀ ℕ)) (a b : ι × γ) (h : a.1 ≠ b.1) : glue D (a, b) = 0 := by
  unfold glue
  rw [Finsupp.finsetSum_apply]
  refine Finset.sum_eq_zero fun τ _ => Finsupp.mapDomain_notin_range _ _ ?_
  rintro ⟨u, hu⟩
  simp only [emb, Prod.mk.injEq] at hu
  exact h (by rw [← hu.1, ← hu.2])

theorem glue_injective : Function.Injective (glue (ι := ι) (γ := γ)) := by
  intro D D' h
  funext τ
  ext v
  rw [← glue_emb, h, glue_emb]

theorem graph_prodCongrRight (σ : ι → Equiv.Perm γ) :
    graph (Equiv.prodCongrRight σ) = glue fun τ => graph (σ τ) := by
  unfold glue graph
  simp only [Finsupp.mapDomain_finsetSum, Finsupp.mapDomain_single]
  rw [Fintype.sum_prod_type]
  simp only [Finsupp.mapDomain_finsetSum, Finsupp.mapDomain_single, emb, Equiv.prodCongrRight_apply]

theorem exists_prodCongrRight (w : Equiv.Perm (ι × γ)) (hw : ∀ a, (w a).1 = a.1) :
    ∃ σ : ι → Equiv.Perm γ, Equiv.prodCongrRight σ = w := by
  have hw' : ∀ b, (w.symm b).1 = b.1 := fun b => by
    have := hw (w.symm b)
    rw [Equiv.apply_symm_apply] at this
    exact this.symm
  have li : ∀ τ x, (w.symm (τ, (w (τ, x)).2)).2 = x := fun τ x => by
    have e1 : (τ, (w (τ, x)).2) = w (τ, x) := Prod.ext (hw (τ, x)).symm rfl
    rw [e1, Equiv.symm_apply_apply]
  have ri : ∀ τ x, (w (τ, (w.symm (τ, x)).2)).2 = x := fun τ x => by
    have e1 : (τ, (w.symm (τ, x)).2) = w.symm (τ, x) := Prod.ext (hw' (τ, x)).symm rfl
    rw [e1, Equiv.apply_symm_apply]
  refine ⟨fun τ => Equiv.mk (fun x => (w (τ, x)).2) (fun x => (w.symm (τ, x)).2) (li τ) (ri τ), ?_⟩
  ext ⟨τ, x⟩
  · simp [hw]
  · simp

theorem prodCongrRight_injective :
    Function.Injective (fun σ : ι → Equiv.Perm γ => (Equiv.prodCongrRight σ : Equiv.Perm (ι × γ))) := by
  intro σ σ' h
  funext τ
  ext x
  have := congrArg (fun w : Equiv.Perm (ι × γ) => (w (τ, x)).2) h
  simpa using this

theorem tc_monomial_glue (D : ι → (γ × γ →₀ ℕ)) :
    tc (monomial (glue D) (1 : ℂ)) = ∏ τ, tc (monomial (D τ) (1 : ℂ)) := by
  simp only [tc, coeff_monomial]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  set F : Equiv.Perm (ι × γ) → ℂ := fun w => ((Equiv.Perm.sign w : ℤ) : ℂ) * if glue D = graph w then 1 else 0 with hF
  have h1 : ∑ w, F w = ∑ w ∈ Finset.univ.image (fun σ : ι → Equiv.Perm γ => Equiv.prodCongrRight σ), F w := by
    refine (Finset.sum_subset (Finset.subset_univ _) fun w _ hw => ?_).symm
    simp only [hF]
    rw [if_neg, mul_zero]
    intro hg
    apply hw
    have hb : ∀ a, (w a).1 = a.1 := by
      intro a
      by_contra hne
      have e1 := glue_off D a (w a) (Ne.symm hne)
      rw [hg, graph_apply, if_pos rfl] at e1
      exact one_ne_zero e1
    obtain ⟨σ, hσ⟩ := exists_prodCongrRight w hb
    exact Finset.mem_image.mpr ⟨σ, Finset.mem_univ _, hσ⟩
  rw [h1, Finset.sum_image fun x _ y _ h => prodCongrRight_injective h]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [hF, graph_prodCongrRight, glue_injective.eq_iff, Equiv.Perm.sign_prodCongrRight]
  rw [Finset.prod_mul_distrib]
  push_cast
  congr 1
  by_cases hD : D = fun τ => graph (σ τ)
  · rw [if_pos hD]
    symm
    exact Finset.prod_eq_one fun τ _ => if_pos (congrFun hD τ)
  · rw [if_neg hD]
    obtain ⟨τ, hτ⟩ : ∃ τ, D τ ≠ graph (σ τ) := by
      by_contra hall
      push_neg at hall
      exact hD (funext hall)
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ τ) (if_neg hτ)

theorem tc_prod_rename (f : ι → MvPolynomial (γ × γ) ℂ) :
    tc (∏ τ, rename (emb τ) (f τ)) = ∏ τ, tc (f τ) := by
  have hL : ∏ τ, rename (emb τ) (f τ) = ∑ x ∈ Fintype.piFinset fun τ => (f τ).support,
      monomial (glue x) (∏ τ, AddMonoidAlgebra.coeff (f τ) (x τ)) := by
    calc ∏ τ, rename (emb τ) (f τ)
        = ∏ τ, ∑ d ∈ (f τ).support, monomial (d.mapDomain (emb τ)) (AddMonoidAlgebra.coeff (f τ) d) := by
          refine Finset.prod_congr rfl fun τ _ => ?_
          conv_lhs => rw [(f τ).as_sum]
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_sum]
          simp only [rename_monomial]
      _ = _ := by
          rw [Finset.prod_univ_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [prod_monomial']
          rfl
  have hR : ∀ τ, tc (f τ) = ∑ d ∈ (f τ).support, AddMonoidAlgebra.coeff (f τ) d * tc (monomial d (1 : ℂ)) := by
    intro τ
    conv_lhs => rw [(f τ).as_sum]
    rw [tc_sum]
    exact Finset.sum_congr rfl fun d _ => tc_monomial _ _
  rw [hL, tc_sum]
  simp_rw [hR]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [tc_monomial, tc_monomial_glue, Finset.prod_mul_distrib]

end Blocks

end GlobalTheory.BlockTop

namespace GlobalTheory.BlockTop

def symMat (p q : ℕ) : Matrix (Fin p) (Fin p) (MvPolynomial ((Fin p × Fin q) × (Fin p × Fin q)) ℂ) :=
  Matrix.of fun i j => ∑ b : Fin q, X ((i, b), (j, b))

theorem det_map_rename {σ' : Type} (p q : ℕ) (g : (Fin p × Fin q) × (Fin p × Fin q) → σ') :
    ((symMat p q).map (rename (R := ℂ) g)).det = rename g (symMat p q).det :=
  (AlgHom.map_det (rename g) _).symm

theorem blockSym_eq {ι : Type} [Fintype ι] {p q n : ℕ} (h : Fintype.card (ι × Fin p × Fin q) = n) (τ : ι) :
    GlobalTheory.DomainDens.blockSym h τ = (symMat p q).map
      (rename (Prod.map (Fintype.equivFinOfCardEq h) (Fintype.equivFinOfCardEq h) ∘ emb τ)) := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp [GlobalTheory.DomainDens.blockSym, symMat, map_sum, rename_X, emb]

end GlobalTheory.BlockTop


open GlobalTheory.BlockTop in
theorem GlobalTheory.DomainDens.topCoeff_prod_blockSym_det_pow : ∀ (ι : Type) [Fintype ι] (p q n : ℕ)
    (h : Fintype.card (ι × Fin p × Fin q) = n) (h1 : Fintype.card (Unit × Fin p × Fin q) = p * q),
    GlobalTheory.GoodMetric.topCoeff (∏ τ, (GlobalTheory.DomainDens.blockSym h τ).det ^ q) =
      GlobalTheory.GoodMetric.topCoeff ((GlobalTheory.DomainDens.blockSym h1 ()).det ^ q) ^ Fintype.card ι := by
  intro ι _ p q n h h1
  classical
  set e := Fintype.equivFinOfCardEq h
  set e1 := Fintype.equivFinOfCardEq h1
  have hL : ∏ τ, (GlobalTheory.DomainDens.blockSym h τ).det ^ q =
      rename (Prod.map e e) (∏ τ, rename (emb τ) ((symMat p q).det ^ q)) := by
    rw [map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [blockSym_eq, det_map_rename, rename_rename, map_pow]
  set e' : Fin p × Fin q ≃ Fin (p * q) := (Equiv.punitProd (Fin p × Fin q)).symm.trans e1
  have hR : (GlobalTheory.DomainDens.blockSym h1 ()).det ^ q = rename (Prod.map e' e') ((symMat p q).det ^ q) := by
    rw [blockSym_eq, det_map_rename, map_pow]
    rfl
  rw [hL, hR, topCoeff_eq_tc, topCoeff_eq_tc, tc_rename_equiv, tc_rename_equiv, tc_prod_rename,
    Finset.prod_const, Finset.card_univ]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopDegreeFormCoeffProdBlockSymbolDetPowStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topDegreeFormCoeff_prod_blockSymbol_det_pow : ∀ (ι : Type) [Fintype ι] (p q n : ℕ) (h : Fintype.card (ι × Fin p × Fin q) = n) (h1 : Fintype.card (Unit × Fin p × Fin q) = p * q), GlobalTheory.GoodMetric.topCoeff (∏ τ, (GlobalTheory.DomainDens.blockSym h τ).det ^ q) = GlobalTheory.GoodMetric.topCoeff ((GlobalTheory.DomainDens.blockSym h1 ()).det ^ q) ^ Fintype.card ι := by
  first | exact @GlobalTheory.DomainDens.topCoeff_prod_blockSym_det_pow | exact GlobalTheory.DomainDens.topCoeff_prod_blockSym_det_pow | (intros; apply GlobalTheory.DomainDens.topCoeff_prod_blockSym_det_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CurvatureFormMatrixBoundedDomainModelMetricAtZer
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CurvatureFormMatrixBoundedDomainModelMetricAtZer
set_option autoImplicit false

noncomputable section

open Matrix MvPolynomial Filter Topology ComplexConjugate
open GlobalTheory.HermFrame

namespace GlobalTheory.DomainDens

variable {ι : Type} [Fintype ι] {p q n : ℕ} (h : Fintype.card (ι × Fin p × Fin q) = n) (τ : ι)

def flatCoordinateMatrixBlock (u : ReciprocityTheory.L2DbarEstimates.V n) : Matrix (Fin p) (Fin q) ℂ :=
  Formalism.DegreeFormula.unflat (GlobalTheory.UnifDens.flatL h u) τ

theorem block_reshape_apply (u : ReciprocityTheory.L2DbarEstimates.V n) (i : Fin p) (b : Fin q) :
    flatCoordinateMatrixBlock h τ u i b = u (Fintype.equivFinOfCardEq h (τ, i, b)) := rfl

theorem flatCoordinateMatrixBlock_entry_eq_proj (i : Fin p) (b : Fin q) :
    (fun u => flatCoordinateMatrixBlock h τ u i b) = fun u => EuclideanSpace.proj (𝕜 := ℂ) (Fintype.equivFinOfCardEq h (τ, i, b)) u :=
  rfl

theorem flatCoordinateMatrixBlock_at_zero : flatCoordinateMatrixBlock h τ 0 = 0 := by
  ext i b; simp [block_reshape_apply]

theorem matrixHolomorphicPartialDeriv_flatCoordinateMatrixBlock (x ξ : ReciprocityTheory.L2DbarEstimates.V n) : mdel (flatCoordinateMatrixBlock h τ) x ξ = flatCoordinateMatrixBlock h τ ξ := by
  ext i b
  rw [mdel_apply, flatCoordinateMatrixBlock_entry_eq_proj, del_eq_fderiv (ContinuousLinearMap.differentiableAt _),
    ContinuousLinearMap.fderiv]
  rfl

theorem matrixAntiholomorphicPartialDeriv_flatCoordinateMatrixBlock (x η : ReciprocityTheory.L2DbarEstimates.V n) : mdbar (flatCoordinateMatrixBlock h τ) x η = 0 := by
  ext i b
  rw [mdbar_apply, flatCoordinateMatrixBlock_entry_eq_proj, dbar_eq_zero (ContinuousLinearMap.differentiableAt _)]
  rfl

theorem matrixEntriesContDiffAt_flatCoordinateMatrixBlock {k : WithTop ℕ∞} (x : ReciprocityTheory.L2DbarEstimates.V n) : MContDiffAt k (flatCoordinateMatrixBlock h τ) x :=
  fun i b => by
    rw [flatCoordinateMatrixBlock_entry_eq_proj]
    exact (ContinuousLinearMap.contDiff (𝕜 := ℂ) (n := k)
      (EuclideanSpace.proj (𝕜 := ℂ) (ι := Fin n) (Fintype.equivFinOfCardEq h (τ, i, b)) : ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] ℂ)).restrict_scalars ℝ |>.contDiffAt

theorem mContDiffAt_hP {k : WithTop ℕ∞} (x : ReciprocityTheory.L2DbarEstimates.V n) :
    MContDiffAt k (fun u => Formalism.DegreeFormula.hP (flatCoordinateMatrixBlock h τ u)) x := by
  unfold Formalism.DegreeFormula.hP
  exact (mContDiffAt_const 1).sub ((matrixEntriesContDiffAt_flatCoordinateMatrixBlock h τ x).mul (matrixEntriesContDiffAt_flatCoordinateMatrixBlock h τ x).conjTranspose)

theorem mdel_hP (x ξ : ReciprocityTheory.L2DbarEstimates.V n) :
    mdel (fun u => Formalism.DegreeFormula.hP (flatCoordinateMatrixBlock h τ u)) x ξ = -(flatCoordinateMatrixBlock h τ ξ * (flatCoordinateMatrixBlock h τ x)ᴴ) := by
  have hz : MContDiffAt 1 (flatCoordinateMatrixBlock h τ) x := matrixEntriesContDiffAt_flatCoordinateMatrixBlock h τ x
  have e : (fun u => Formalism.DegreeFormula.hP (flatCoordinateMatrixBlock h τ u)) =
      fun u => (fun _ => (1 : Matrix (Fin p) (Fin p) ℂ)) u + -(flatCoordinateMatrixBlock h τ u * (flatCoordinateMatrixBlock h τ u)ᴴ) := by
    funext u; simp [Formalism.DegreeFormula.hP, sub_eq_add_neg]
  rw [e, mdel_add (mContDiffAt_const _) (hz.mul hz.conjTranspose).neg, mdel_const, mdel_neg,
    mdel_mul hz hz.conjTranspose, mdel_conjTranspose, matrixAntiholomorphicPartialDeriv_flatCoordinateMatrixBlock, matrixHolomorphicPartialDeriv_flatCoordinateMatrixBlock]
  simp

theorem hP_zero : Formalism.DegreeFormula.hP (flatCoordinateMatrixBlock h τ 0) = 1 := by simp [Formalism.DegreeFormula.hP, flatCoordinateMatrixBlock_at_zero]

theorem conn_model (x ξ : ReciprocityTheory.L2DbarEstimates.V n) (hu : IsUnit (Formalism.DegreeFormula.hP (flatCoordinateMatrixBlock h τ x)).det) :
    conn (fun u => ((Formalism.DegreeFormula.hP (flatCoordinateMatrixBlock h τ u))⁻¹)ᵀ) x ξ =
      flatCoordinateMatrixBlock h τ ξ * (flatCoordinateMatrixBlock h τ x)ᴴ * (Formalism.DegreeFormula.hP (flatCoordinateMatrixBlock h τ x))⁻¹ := by
  rw [conn, transpose_transpose, mdel_transpose (fun u => (Formalism.DegreeFormula.hP (flatCoordinateMatrixBlock h τ u))⁻¹), transpose_transpose,
    mdel_inv (mContDiffAt_hP h τ x) hu, nonsing_inv_nonsing_inv _ hu, mdel_hP]
  simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, ← Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.one_mul]

theorem curv_model (ξ η : ReciprocityTheory.L2DbarEstimates.V n) :
    curv (fun u => ((Formalism.DegreeFormula.hP (flatCoordinateMatrixBlock h τ u))⁻¹)ᵀ) 0 ξ η = -(flatCoordinateMatrixBlock h τ ξ * (flatCoordinateMatrixBlock h τ η)ᴴ) := by
  have hu0 : IsUnit (Formalism.DegreeFormula.hP (flatCoordinateMatrixBlock h τ 0)).det := by simp [hP_zero]
  have hev := (mContDiffAt_hP (k := 1) h τ 0).eventually_isUnit hu0
  have hz : MContDiffAt 1 (flatCoordinateMatrixBlock h τ) 0 := matrixEntriesContDiffAt_flatCoordinateMatrixBlock h τ 0
  rw [curv, mdbar_congr (hev.mono fun x hx => conn_model h τ x ξ hx),
    mdbar_mul ((mContDiffAt_const _).mul hz.conjTranspose) ((mContDiffAt_hP h τ 0).inv hu0),
    mdbar_mul (mContDiffAt_const _) hz.conjTranspose, mdbar_conjTranspose, matrixHolomorphicPartialDeriv_flatCoordinateMatrixBlock, mdbar_const, hP_zero,
    flatCoordinateMatrixBlock_at_zero]
  simp

theorem curvPoly_model_zero : ∀ (ι : Type) [Fintype ι] (p q n : ℕ) (h : Fintype.card (ι × Fin p × Fin q) = n) (τ : ι),
    GlobalTheory.GoodMetric.curvPoly
      (fun u => Matrix.transpose (Formalism.DegreeFormula.hP (Formalism.DegreeFormula.unflat (GlobalTheory.UnifDens.flatL h u) τ))⁻¹) 0 =
      -GlobalTheory.DomainDens.blockSym h τ := by
  intro ι _ p q n h τ
  have e2 : ∀ (a c : Fin n) (i j : Fin p),
      curv (fun u => Matrix.transpose (Formalism.DegreeFormula.hP (Formalism.DegreeFormula.unflat (GlobalTheory.UnifDens.flatL h u) τ))⁻¹)
        0 (GlobalTheory.GoodMetric.coordVec a) (GlobalTheory.GoodMetric.coordVec c) i j =
      -∑ b : Fin q, (if Fintype.equivFinOfCardEq h (τ, i, b) = a then 1 else 0) *
        (if Fintype.equivFinOfCardEq h (τ, j, b) = c then 1 else 0) := by
    intro a c i j
    change curv (fun u => ((Formalism.DegreeFormula.hP (flatCoordinateMatrixBlock h τ u))⁻¹)ᵀ) 0 _ _ i j = _
    rw [curv_model h τ, Matrix.neg_apply, Matrix.mul_apply]
    simp [block_reshape_apply, PiLp.single_apply]
  refine Matrix.ext fun i j => ?_
  simp only [GlobalTheory.GoodMetric.curvPoly, of_apply, e2, Matrix.neg_apply, blockSym_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_neg, neg_mul, Finset.sum_neg_distrib, neg_inj, map_sum, Finset.sum_mul, mul_ite, ite_mul, one_mul,
    zero_mul, mul_zero, apply_ite (C : ℂ → MvPolynomial (Fin n × Fin n) ℂ), map_one, map_zero]
  rw [Finset.sum_congr rfl fun _ _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp [Finset.sum_ite_eq]

end GlobalTheory.DomainDens
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CurvatureFormMatrixBoundedDomainModelMetricAtZerStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.curvatureFormMatrix_boundedDomainModelMetric_at_zero : ∀ (ι : Type) [Fintype ι] (p q n : ℕ) (h : Fintype.card (ι × Fin p × Fin q) = n) (τ : ι), GlobalTheory.GoodMetric.curvPoly (fun u => Matrix.transpose (Formalism.DegreeFormula.hP (Formalism.DegreeFormula.unflat (GlobalTheory.UnifDens.flatL h u) τ))⁻¹) 0 = -GlobalTheory.DomainDens.blockSym h τ := by
  first | exact @GlobalTheory.DomainDens.curvPoly_model_zero | exact GlobalTheory.DomainDens.curvPoly_model_zero | (intros; apply GlobalTheory.DomainDens.curvPoly_model_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernTopDensityModelMetricOrigin
set_option autoImplicit false

open Formalism.DegreeFormula MvPolynomial GlobalTheory.GoodMetric GlobalTheory.DomainDens

noncomputable section

namespace GlobalTheory.DomainDens

theorem coeff_charpolyRev_card {R : Type} [CommRing R] [Nontrivial R] {p : ℕ} (M : Matrix (Fin p) (Fin p) R) :
    M.charpolyRev.coeff p = (-1) ^ p * M.det := by
  rw [← Matrix.reverse_charpoly, Polynomial.coeff_reverse, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin,
    Polynomial.revAt_le le_rfl, Nat.sub_self, Matrix.det_eq_sign_charpoly_coeff, Fintype.card_fin, ← mul_assoc,
    ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]

theorem chernTop_model_origin : ∀ (ι : Type) [Fintype ι] (p q n : ℕ) (h : Fintype.card (ι × Fin p × Fin q) = n), GlobalTheory.GoodMetric.chernTop (m := fun _ : ι => p) (∏ τ : ι, (MvPolynomial.C ((-1 : ℝ) ^ p) * MvPolynomial.X (τ, p)) ^ q) (fun u τ => Matrix.transpose (hP (unflat (GlobalTheory.UnifDens.flatL h u) τ))⁻¹) 0 = GlobalTheory.TrueCx.grassConst p q ^ Fintype.card ι := by
  intro ι _ p q n h
  have hc : ∀ τ : ι, chernPoly (fun u => Matrix.transpose (hP (unflat (GlobalTheory.UnifDens.flatL h u) τ))⁻¹) 0 p =
      C ((-1 : ℂ) ^ p) * (blockSym h τ).det := by
    intro τ
    rw [chernPoly, GlobalTheory.T.curvatureFormMatrix_boundedDomainModelMetric_at_zero ι p q n h τ, neg_neg, coeff_charpolyRev_card, map_pow, map_neg, map_one]
  have hs : (algebraMap ℝ ℂ ((-1 : ℝ) ^ p)) * (-1 : ℂ) ^ p = 1 := by
    rw [map_pow, map_neg, map_one, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  have ha : aeval (fun x : ι × ℕ => chernPoly (fun u => Matrix.transpose (hP (unflat (GlobalTheory.UnifDens.flatL h u) x.1))⁻¹) 0 x.2)
      (∏ τ : ι, (MvPolynomial.C ((-1 : ℝ) ^ p) * MvPolynomial.X (τ, p)) ^ q) = ∏ τ, (blockSym h τ).det ^ q := by
    rw [map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_pow, map_mul, aeval_X, aeval_C, hc τ, ← mul_assoc, MvPolynomial.algebraMap_apply, ← C_mul, hs, C_1,
      one_mul]
  have hn : n = Fintype.card ι * (p * q) := by
    rw [← h]; simp [Fintype.card_prod, Fintype.card_fin]
  have h1 : Fintype.card (Unit × Fin p × Fin q) = p * q := by simp [Fintype.card_prod, Fintype.card_fin]
  have e : (∏ i ∈ Finset.range p, (((q + i).factorial : ℂ) / i.factorial)) =
      ((∏ i ∈ Finset.range p, (((q + i).factorial : ℝ) / i.factorial) : ℝ) : ℂ) := by push_cast; rfl
  simp only [chernTop]
  rw [ha, GlobalTheory.T.topDegreeFormCoeff_prod_blockSymbol_det_pow ι p q n h h1, GlobalTheory.T.topDegreeFormCoeff_blockSymbolDet_pow_cayley p q h1, e, ← Complex.ofReal_pow, Complex.ofReal_re, GlobalTheory.TrueCx.grassConst,
    div_pow, hn, pow_mul', div_eq_inv_mul]

end GlobalTheory.DomainDens
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernTopDensityModelMetricOriginStatement
open Formalism.DegreeFormula

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernTop_density_model_metric_origin : ∀ (ι : Type) [Fintype ι] (p q n : ℕ) (h : Fintype.card (ι × Fin p × Fin q) = n), GlobalTheory.GoodMetric.chernTop (m := fun _ : ι => p) (∏ τ : ι, (MvPolynomial.C ((-1 : ℝ) ^ p) * MvPolynomial.X (τ, p)) ^ q) (fun u τ => Matrix.transpose (hP (unflat (GlobalTheory.UnifDens.flatL h u) τ))⁻¹) 0 = GlobalTheory.TrueCx.grassConst p q ^ Fintype.card ι := by
  first | exact @GlobalTheory.DomainDens.chernTop_model_origin | exact GlobalTheory.DomainDens.chernTop_model_origin | (intros; apply GlobalTheory.DomainDens.chernTop_model_origin <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointClassDensityHodgeMetricBoundedDomain
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx

namespace GlobalTheory.UnifDens

theorem chernTop_domain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) → ∀ (h : Fintype.card ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p)) = X.dim) (v : ReciprocityTheory.L2DbarEstimates.V X.dim), GlobalTheory.UnifDens.flatL h v ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) → ∀ A ∈ Eb.S (under (ψ (GlobalTheory.UnifDens.flatL h v))), chernTop (pointPoly H Dw) (fun u => lieGram e U hj f₀ A₀ A (ψ (GlobalTheory.UnifDens.flatL h u))) v = grassConst Dw.p (Dw.p + Dw.q - Dw.p) ^ Fintype.card (U.X k).Ψ * ∏ i, ((hQ (unflat (GlobalTheory.UnifDens.flatL h v) i)).det.re) ^ (-((Dw.p + (Dw.p + Dw.q - Dw.p) : ℕ) : ℤ)) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ h v hv A hA
  rw [GlobalTheory.T.pointClass_density_hodge_uniformisation_eq_model E H Dw l Xo c O β Y T F e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ h v hv A hA,
    GlobalTheory.T.chernPolyTopDensity_bounded_domain_invariant _ _ _ _ h v hv, GlobalTheory.T.chernTop_density_model_metric_origin]

end GlobalTheory.UnifDens
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointClassDensityHodgeMetricBoundedDomainStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointClassDensity_hodgeMetric_boundedDomain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) → ∀ (h : Fintype.card ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p)) = X.dim) (v : ReciprocityTheory.L2DbarEstimates.V X.dim), GlobalTheory.UnifDens.flatL h v ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) → ∀ A ∈ Eb.S (under (ψ (GlobalTheory.UnifDens.flatL h v))), chernTop (pointPoly H Dw) (fun u => lieGram e U hj f₀ A₀ A (ψ (GlobalTheory.UnifDens.flatL h u))) v = grassConst Dw.p (Dw.p + Dw.q - Dw.p) ^ Fintype.card (U.X k).Ψ * ∏ i, ((hQ (unflat (GlobalTheory.UnifDens.flatL h v) i)).det.re) ^ (-((Dw.p + (Dw.p + Dw.q - Dw.p) : ℕ) : ℤ)) := by
  first | exact @GlobalTheory.UnifDens.chernTop_domain | exact GlobalTheory.UnifDens.chernTop_domain | (intros; apply GlobalTheory.UnifDens.chernTop_domain <;> assumption)
end
