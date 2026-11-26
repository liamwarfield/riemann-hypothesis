module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RuleSectionNowhereVanishingReal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeterssonLevelCoverPullbackProbability

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefHomGenHomMonomial
set_option autoImplicit false

noncomputable section

open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.HighWt

namespace GlobalTheory.HighWtEmb

variable (O : Type) [CommRing O] (N : ℕ)

def genHom : MvPolynomial (Fin N × Fin N) O →ₐ[O] MvPolynomial (Fin N × Fin N) (MvPolynomial (Fin N × Fin N) O) :=
  aeval (fun v : Fin N × Fin N => ∑ b : Fin N, X (v.1, b) * C (X (b, v.2)))

theorem genHom_X (v : Fin N × Fin N) : genHom O N (X v) = ∑ b : Fin N, X (v.1, b) * C (X (b, v.2)) := aeval_X _ _

theorem genHom_C (c : O) : genHom O N (C c) = C (C c) := by
  rw [MvPolynomial.algHom_C]; rfl

section Weights

variable {O N} {M : Type} [AddCommMonoid M] (wx u : Fin N × Fin N → M)

def CoefHom (G : MvPolynomial (Fin N × Fin N) (MvPolynomial (Fin N × Fin N) O)) (e : M) : Prop :=
  ∀ m, IsWeightedHomogeneous wx (AddMonoidAlgebra.coeff G m) (Finsupp.weight u m + e)

theorem CoefHom.mul {G G' : MvPolynomial (Fin N × Fin N) (MvPolynomial (Fin N × Fin N) O)} {e e' : M}
    (h : CoefHom wx u G e) (h' : CoefHom wx u G' e') : CoefHom wx u (G * G') (e + e') := by
  intro m
  rw [coeff_mul]
  refine IsWeightedHomogeneous.sum _ _ _ fun p hp => ?_
  have hp' : p.1 + p.2 = m := by simpa using hp
  rw [← hp', map_add (f := _), add_add_add_comm]
  exact (h p.1).mul (h' p.2)

theorem coefHom_monomial (d : Fin N × Fin N →₀ ℕ) (g : MvPolynomial (Fin N × Fin N) O) (e : M)
    (hg : IsWeightedHomogeneous wx g (Finsupp.weight u d + e)) : CoefHom wx u (monomial d g) e := by
  intro m
  rw [coeff_monomial]
  split_ifs with h
  · exact h ▸ hg
  · exact isWeightedHomogeneous_zero _ _ _

theorem coefHom_genHom_monomial (wf : Fin N × Fin N → M) (h : ∀ a b s, wx (b, s) = u (a, b) + wf (a, s))
    (d : Fin N × Fin N →₀ ℕ) (c : O) : CoefHom wx u (genHom O N (monomial d c)) (Finsupp.weight wf d) := by
  have hX : ∀ v, CoefHom wx u (genHom O N (X v)) (wf v) := by
    intro v m
    rw [genHom_X, coeff_sum]
    refine IsWeightedHomogeneous.sum _ _ _ fun b _ => ?_
    rw [mul_comm, C_mul_X_eq_monomial]
    refine coefHom_monomial wx u _ _ _ ?_ m
    rw [Finsupp.weight_single, one_smul, ← h]
    exact isWeightedHomogeneous_X _ _ _
  induction d using Finsupp.induction_linear generalizing c with
  | zero =>
    rw [monomial_zero', genHom_C, map_zero]
    refine coefHom_monomial wx u 0 _ _ ?_
    rw [map_zero, add_zero]
    exact isWeightedHomogeneous_C _ _
  | add f g hf hg =>
    rw [← mul_one c, ← monomial_mul, map_mul, map_add (f := _)]
    exact (hf c).mul wx u (hg 1)
  | single v n =>
    induction n generalizing c with
    | zero =>
      rw [Finsupp.single_zero, monomial_zero', genHom_C, map_zero]
      refine coefHom_monomial wx u 0 _ _ ?_
      rw [map_zero, add_zero]
      exact isWeightedHomogeneous_C _ _
    | succ n ih =>
      rw [Finsupp.single_add, ← mul_one c, ← monomial_mul, map_mul, map_add (f := _)]
      refine (ih c).mul wx u ?_
      rw [Finsupp.weight_single, one_smul]
      exact hX v

theorem coefHom_genHom (wf : Fin N × Fin N → M) (h : ∀ a b s, wx (b, s) = u (a, b) + wf (a, s))
    (f : MvPolynomial (Fin N × Fin N) O) (e : M) (hf : IsWeightedHomogeneous wf f e) : CoefHom wx u (genHom O N f) e := by
  intro m
  set_option synthInstance.maxHeartbeats 100000 in
    rw [f.as_sum, map_sum, coeff_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_
  rw [← hf (mem_support_iff.1 hd)]
  exact coefHom_genHom_monomial wx u wf h d _ m

end Weights

theorem coeff_genHom_row (f : MvPolynomial (Fin N × Fin N) O) (m : Fin N × Fin N →₀ ℕ) :
    IsWeightedHomogeneous (rowW N N) (AddMonoidAlgebra.coeff (genHom O N f) m) (Finsupp.weight (colW N N) m) := by
  have := coefHom_genHom (rowW N N) (colW N N) 0 (fun a b s => by simp [rowW, colW]) f 0
    (fun d _ => by simp [Finsupp.weight_apply]) m
  rwa [add_zero] at this

theorem coeff_genHom_col (f : MvPolynomial (Fin N × Fin N) O) (ν : Fin N → ℕ) (hf : IsWeightedHomogeneous (colW N N) f ν)
    (m : Fin N × Fin N →₀ ℕ) : IsWeightedHomogeneous (colW N N) (AddMonoidAlgebra.coeff (genHom O N f) m) ν := by
  have := coefHom_genHom (colW N N) 0 (colW N N) (fun a b s => by simp [colW]) f ν hf m
  simpa [Finsupp.weight_apply] using this

theorem coeff_genHom_mem (ν : Fin N → ℕ) (f : MvPolynomial (Fin N × Fin N) O) (hf : f ∈ dualWeyl O N N ν)
    (m : Fin N × Fin N →₀ ℕ) : AddMonoidAlgebra.coeff (genHom O N f) m ∈ dualWeyl O N N ν := by
  rw [rowst_mem_dualWeyl_iff] at hf ⊢
  refine ⟨coeff_genHom_col O N f ν hf.1 m, fun l j hlj => ?_⟩
  let Φ : MvPolynomial (Option (Fin N × Fin N)) O →+* MvPolynomial (Fin N × Fin N) (MvPolynomial (Option (Fin N × Fin N)) O) :=
    eval₂Hom (C.comp C) fun o => Option.elim o (C (X none)) fun v => ∑ b : Fin N, X (v.1, b) * C (X (some (b, v.2)))
  have h1 : (map (colAddGen O (r := N) l j).toRingHom).comp (genHom O N).toRingHom = Φ.comp (colAddGen O l j).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp [Φ, genHom_C]
    · intro v
      by_cases h : v.2 = j
      · simp [Φ, genHom_X, colAddGen, h, mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_left_comm]
      · simp [Φ, genHom_X, colAddGen, h]
  have h2 : (map (rename (R := O) (some : Fin N × Fin N → Option (Fin N × Fin N))).toRingHom).comp (genHom O N).toRingHom =
      Φ.comp (rename some).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp [Φ, genHom_C]
    · intro v; simp [Φ, genHom_X]
  have h3 := congrArg (AddMonoidAlgebra.coeff · m) (RingHom.congr_fun h1 f)
  have h4 := congrArg (AddMonoidAlgebra.coeff · m) (RingHom.congr_fun h2 f)
  simp only [RingHom.comp_apply, coeff_map, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h3 h4
  rw [h3, h4, hf.2 l j hlj]

theorem genHom_component (v : Fin N → ℕ) (f : MvPolynomial (Fin N × Fin N) O) :
    genHom O N (weightedHomogeneousComponent (rowW N N) v f) = weightedHomogeneousComponent (rowW N N) v (genHom O N f) := by
  classical
  let Φ : MvPolynomial (Fin N × Fin N) (MvPolynomial (Fin N × Fin N) O) →ₐ[MvPolynomial (Fin N × Fin N) O]
      MvPolynomial (Fin N × Fin N) (MvPolynomial (Fin N × Fin N) O) :=
    aeval (fun v : Fin N × Fin N => ∑ b : Fin N, X (v.1, b) * C (X (b, v.2)))
  have h1 : Φ.toRingHom.comp (map C) = (genHom O N).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp [Φ, genHom_C]
    · intro v; simp [Φ, genHom_X]
  have h2 : ∀ g, genHom O N g = Φ (map C g) := fun g => (RingHom.congr_fun h1 g).symm
  rw [h2, h2, ← algHom_weightedHomogeneousComponent Φ (rowW N N) (rowW N N)]
  · congr 1
    ext m
    simp only [coeff_map, coeff_weightedHomogeneousComponent]
    split_ifs <;> simp
  · intro u
    simp only [Φ, aeval_X]
    refine IsWeightedHomogeneous.sum _ _ _ fun b _ => ?_
    rw [mul_comm]
    exact (isWeightedHomogeneous_X _ (rowW N N) (u.1, b)).C_mul _

theorem sum_mul_weight_rowW (c : Fin N → ℕ) (m : Fin N × Fin N →₀ ℕ) :
    ∑ a, c a * Finsupp.weight (rowW N N) m a = ∑ v, c v.1 * m v := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp only [Finset.sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp [rowW, Pi.single_apply]

theorem sum_mul_weight_colW (c : Fin N → ℕ) (m : Fin N × Fin N →₀ ℕ) :
    ∑ a, c a * Finsupp.weight (colW N N) m a = ∑ v, c v.2 * m v := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp only [Finset.sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp [colW, Pi.single_apply]

def expSet (ν : Fin N → ℕ) : Finset (Fin N × Fin N →₀ ℕ) := Finset.finsuppAntidiag Finset.univ (∑ a, ν a)

theorem support_genHom (ν : Fin N → ℕ) (f : MvPolynomial (Fin N × Fin N) O) (hf : f ∈ dualWeyl O N N ν) :
    (genHom O N f).support ⊆ expSet N ν := by
  intro m hm
  obtain ⟨d, hd⟩ := ne_zero_iff.1 (mem_support_iff.1 hm)
  have h1 := coeff_genHom_row O N f m hd
  have h2 := coeff_genHom_col O N f ν (rowst_mem_dualWeyl_iff.1 hf).1 m hd
  have h3 := sum_mul_weight_rowW N (fun _ => 1) d
  have h4 := sum_mul_weight_colW N (fun _ => 1) d
  have h5 := sum_mul_weight_colW N (fun _ => 1) m
  simp only [one_mul, h1, h2] at h3 h4 h5
  simp only [expSet, Finset.mem_finsuppAntidiag, Finset.subset_univ, and_true]
  rw [← h5, h3, h4]

theorem genHom_eq_sum (ν : Fin N → ℕ) (f : MvPolynomial (Fin N × Fin N) O) (hf : f ∈ dualWeyl O N N ν) :
    genHom O N f = ∑ m ∈ expSet N ν, monomial m (AddMonoidAlgebra.coeff (genHom O N f) m) := by
  conv_lhs => rw [(genHom O N f).as_sum]
  refine Finset.sum_subset (support_genHom O N ν f hf) fun m _ hm => ?_
  rw [notMem_support_iff.1 hm, map_zero]

def extHom {Z : Type} (β : MvPolynomial (Fin N × Fin N) O →ₐ[O] MvPolynomial Z O) :
    MvPolynomial (Fin N × Fin N) (MvPolynomial (Fin N × Fin N) O) →+* MvPolynomial Z (MvPolynomial (Fin N × Fin N) O) :=
  eval₂Hom C fun v => map C (β (X v))

theorem extHom_monomial {Z : Type} (β : MvPolynomial (Fin N × Fin N) O →ₐ[O] MvPolynomial Z O) (m : Fin N × Fin N →₀ ℕ)
    (g : MvPolynomial (Fin N × Fin N) O) : extHom O N β (monomial m g) = map C (β (monomial m 1)) * C g := by
  rw [extHom, eval₂Hom_monomial, monomial_eq, mul_comm, C_1, one_mul]
  simp only [Finsupp.prod, map_prod, map_pow]

theorem extHom_genHom {Z : Type} (β : MvPolynomial (Fin N × Fin N) O →ₐ[O] MvPolynomial Z O) (ν : Fin N → ℕ)
    (f : MvPolynomial (Fin N × Fin N) O) (hf : f ∈ dualWeyl O N N ν) :
    extHom O N β (genHom O N f) = ∑ m ∈ expSet N ν, map C (β (monomial m 1)) * C (AddMonoidAlgebra.coeff (genHom O N f) m) := by
  conv_lhs => rw [genHom_eq_sum O N ν f hf]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, extHom_monomial]

theorem extHom_id (G : MvPolynomial (Fin N × Fin N) (MvPolynomial (Fin N × Fin N) O)) : extHom O N (AlgHom.id O _) G = G := by
  have : extHom O N (AlgHom.id O _) = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext <;> intro c <;> simp [extHom]
  rw [this]; rfl

theorem genHom_rowAct (A : Matrix (Fin N) (Fin N) O) (f : MvPolynomial (Fin N × Fin N) O) :
    genHom O N (rowAct O A f) = extHom O N (rowAct O A) (genHom O N f) := by
  have : (genHom O N).toRingHom.comp (rowAct O A).toRingHom = (extHom O N (rowAct O A)).comp (genHom O N).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp [extHom, genHom_C]
    · intro v
      simp [extHom, genHom_X, genHom_C, rowAct, Finset.mul_sum, Finset.sum_mul, mul_assoc]
      exact Finset.sum_comm
  exact RingHom.congr_fun this f

def unitHom (Z : Type) : MvPolynomial (Fin N × Fin N) O →ₐ[O] MvPolynomial Z O := aeval fun v => if v.1 = v.2 then 1 else 0

theorem extHom_unit (Z : Type) (f : MvPolynomial (Fin N × Fin N) O) : extHom O N (unitHom O N Z) (genHom O N f) = C f := by
  have : (extHom O N (unitHom O N Z)).comp (genHom O N).toRingHom = C := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp [extHom, genHom_C]
    · intro v
      simp [extHom, genHom_X, unitHom, apply_ite]
  exact RingHom.congr_fun this f

def elemHom (l j : Fin N) : MvPolynomial (Fin N × Fin N) O →ₐ[O] MvPolynomial (Option (Fin N × Fin N)) O :=
  aeval fun v => (if v.1 = v.2 then 1 else 0) + if v = (l, j) then X none else 0

theorem extHom_colAddGen (l j : Fin N) (ν : Fin N → ℕ) (f : MvPolynomial (Fin N × Fin N) O) (hf : f ∈ dualWeyl O N N ν) :
    extHom O N (colAddGen O l j) (genHom O N f) = ∑ p ∈ expSet N ν ×ˢ expSet N ν,
      map C (rename some (monomial p.1 1) * elemHom O N l j (monomial p.2 1)) * C (AddMonoidAlgebra.coeff (genHom O N (AddMonoidAlgebra.coeff (genHom O N f) p.1)) p.2) := by
  let Θ : MvPolynomial (Fin N × Fin N) (MvPolynomial (Fin N × Fin N) O) →+*
      MvPolynomial (Option (Fin N × Fin N)) (MvPolynomial (Fin N × Fin N) O) :=
    eval₂Hom ((extHom O N (elemHom O N l j)).comp (genHom O N).toRingHom) fun v => X (some v)
  have : (extHom O N (colAddGen O l j)).comp (genHom O N).toRingHom = Θ.comp (genHom O N).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp [extHom, genHom_C, Θ]
    · intro v
      have e1 : ∀ b, extHom O N (elemHom O N l j) (genHom O N (X (b, v.2))) =
          C (X (b, v.2)) + if b = l then X none * C (X (j, v.2)) else 0 := by
        intro b
        simp [extHom, genHom_X, elemHom, apply_ite (map C), add_mul, Finset.sum_add_distrib, ite_and]
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [genHom_X]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sum, map_mul, Θ, eval₂Hom_X', eval₂Hom_C, e1]
      have e2 : ∀ b, extHom O N (colAddGen O l j) (X (v.1, b)) =
          X (some (v.1, b)) + if b = j then X none * X (some (v.1, l)) else 0 := by
        intro b
        by_cases h : b = j <;> simp [extHom, colAddGen, h]
      simp only [e2]
      simp [extHom, mul_add, add_mul, Finset.sum_add_distrib]
      ring
  refine (RingHom.congr_fun this f).trans ?_
  show Θ (genHom O N f) = _
  conv_lhs => rw [genHom_eq_sum O N ν f hf]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_product]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [Θ, eval₂Hom_monomial, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [extHom_genHom O N _ ν _ (coeff_genHom_mem O N ν f hf m), Finset.sum_mul]
  refine Finset.sum_congr rfl fun m' _ => ?_
  have : map (C : O →+* MvPolynomial (Fin N × Fin N) O) (rename (some : Fin N × Fin N → _) (monomial m 1)) =
      m.prod fun i k => X (some i) ^ k := by
    rw [monomial_eq, C_1, one_mul]; simp only [Finsupp.prod, map_prod, map_pow, rename_X, map_X]
  rw [map_mul, this]
  ring

end GlobalTheory.HighWtEmb

end
end

set_option autoImplicit false

noncomputable section

open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.HighWt GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD
open scoped TensorProduct

namespace GlobalTheory.HighWtEmb

section AtFactor

variable {O : Type} [CommRing O] {ι : Type} [DecidableEq ι] {Nb : ι → Type} [∀ τ, AddCommGroup (Nb τ)] [∀ τ, Module O (Nb τ)]

theorem atFactor_tprod' (τ : ι) (p : Nb τ →ₗ[O] Nb τ) (x : ∀ τ, Nb τ) :
    atFactor τ p (PiTensorProduct.tprod O x) = PiTensorProduct.tprod O (Function.update x τ (p (x τ))) := by
  unfold atFactor
  rw [PiTensorProduct.map_tprod]
  congr 1
  funext σ
  by_cases h : σ = τ
  · subst h; simp
  · simp [Function.update_of_ne h]

def atHom (τ : ι) : Module.End O (Nb τ) →ₐ[O] Module.End O (⨂[O] τ, Nb τ) :=
  AlgHom.ofLinearMap
    { toFun := atFactor τ
      map_add' := fun p q => by ext x; simp [atFactor_tprod']
      map_smul' := fun c p => by ext x; simp [atFactor_tprod'] }
    (by ext x; simp [atFactor_tprod']) (fun p q => by ext x; simp [atFactor_tprod'])

theorem atHom_tprod (τ : ι) (p : Module.End O (Nb τ)) (x : ∀ τ, Nb τ) :
    atHom τ p (PiTensorProduct.tprod O x) = PiTensorProduct.tprod O (Function.update x τ (p (x τ))) := atFactor_tprod' τ p x

theorem atHom_comm {τ σ : ι} (h : τ ≠ σ) (p : Module.End O (Nb τ)) (q : Module.End O (Nb σ)) :
    atHom τ p * atHom σ q = atHom σ q * atHom τ p := by
  ext x
  simp [atHom_tprod, Function.update_of_ne h, Function.update_of_ne h.symm, Function.update_comm h]

end AtFactor

variable (O : Type) [CommRing O] (N : ℕ)

def coefEnd (ν : Fin N → ℕ) (m : Fin N × Fin N →₀ ℕ) : Module.End O (dualWeyl O N N ν) :=
  (((lcoeff (MvPolynomial (Fin N × Fin N) O) m).restrictScalars O) ∘ₗ (genHom O N).toLinearMap).restrict
    (fun x hx => coeff_genHom_mem O N ν x hx m)

theorem coe_coefEnd (ν : Fin N → ℕ) (m : Fin N × Fin N →₀ ℕ) (f : dualWeyl O N N ν) :
    (coefEnd O N ν m f : MvPolynomial (Fin N × Fin N) O) = AddMonoidAlgebra.coeff (genHom O N f) m := rfl

theorem coe_rowProj (ν v : Fin N → ℕ) (f : dualWeyl O N N ν) :
    (rowProj O N ν v f : MvPolynomial (Fin N × Fin N) O) = weightedHomogeneousComponent (rowW N N) v f := rfl

theorem coefEnd_mul_rowProj (ν v : Fin N → ℕ) (m : Fin N × Fin N →₀ ℕ) :
    coefEnd O N ν m * rowProj O N ν v = if Finsupp.weight (rowW N N) m = v then coefEnd O N ν m else 0 := by
  ext1 f
  apply Subtype.ext
  rw [Module.End.mul_apply, coe_coefEnd, coe_rowProj, genHom_component, coeff_weightedHomogeneousComponent]
  split_ifs <;> rfl

theorem rowProj_mul_coefEnd (ν v : Fin N → ℕ) (m : Fin N × Fin N →₀ ℕ) :
    rowProj O N ν v * coefEnd O N ν m = if Finsupp.weight (colW N N) m = v then coefEnd O N ν m else 0 := by
  ext1 f
  apply Subtype.ext
  rw [Module.End.mul_apply, coe_rowProj, coe_coefEnd, weightedHomogeneousComponent_of_mem (coeff_genHom_row O N f m)]
  by_cases h : Finsupp.weight (colW N N) m = v
  · rw [if_pos h, if_pos h.symm]; rfl
  · rw [if_neg h, if_neg (Ne.symm h)]; rfl

theorem rowProj_mul_self (ν v : Fin N → ℕ) : rowProj O N ν v * rowProj O N ν v = rowProj O N ν v := by
  ext1 f
  apply Subtype.ext
  rw [Module.End.mul_apply, coe_rowProj, coe_rowProj,
    weightedHomogeneousComponent_of_mem (weightedHomogeneousComponent_isWeightedHomogeneous v _), if_pos rfl]

variable {ι : Type} [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ)

abbrev atN (τ : ι) : Module.End O (dualWeyl O N N (res N (lam τ))) →ₐ[O] Module.End O (NablaT O N lam) :=
  atHom (Nb := fun τ => dualWeyl O N N (res N (lam τ))) τ

theorem isProj_iff (τ : ι) (v : Fin N → ℕ) (a : Module.End O (NablaT O N lam)) :
    IsProj O N lam τ v a ↔ a = atN O N lam τ (rowProj O N _ v) := by
  constructor
  · intro h
    ext x
    exact (h x _ rfl).trans (atHom_tprod τ _ x).symm
  · rintro rfl x y hy
    rw [atHom_tprod, show y = rowProj O N _ v (x τ) from Subtype.ext hy]

theorem eq_of_isCoef (τ : ι) (m : Fin N × Fin N →₀ ℕ) (a : Module.End O (NablaT O N lam)) (h : IsCoef O N lam τ m a) :
    a = atN O N lam τ (coefEnd O N _ m) := by
  ext x
  exact (h x _ rfl).trans (atHom_tprod τ _ x).symm

theorem grp_mulSingle (τ : ι) (h : GL (Fin N) O) :
    grp O N lam (Pi.mulSingle τ h) = atN O N lam τ (Formalism.UG.dualWeylRep O N N (res N (lam τ)) h) := by
  ext x
  simp only [LinearMap.compMultilinearMap_apply]
  rw [grp_tprod, atHom_tprod]
  congr 1
  funext σ
  by_cases hσ : σ = τ
  · subst hσ; simp
  · simp [Function.update_of_ne hσ, Pi.mulSingle_eq_of_ne hσ]

def projA (τ : ι) (v : Fin N → ℕ) : alg O N lam :=
  ⟨atN O N lam τ (rowProj O N _ v), Algebra.subset_adjoin (Or.inr ⟨τ, v, (isProj_iff O N lam τ v _).2 rfl⟩)⟩

theorem isProj_projA (τ : ι) (v : Fin N → ℕ) : IsProj O N lam τ v (projA O N lam τ v) := (isProj_iff O N lam τ v _).2 rfl

theorem eq_projA {τ : ι} {v : Fin N → ℕ} {a : alg O N lam} (h : IsProj O N lam τ v a) : a = projA O N lam τ v :=
  Subtype.ext ((isProj_iff O N lam τ v _).1 h)

variable {O N lam} {Gm : Type} [AddCommGroup Gm] [Module (alg O N lam) Gm] {R : Type} [CommRing R] [Algebra O R]

theorem sum_expand {Z I : Type} (θ : MvPolynomial Z O →ₐ[O] R) (ψ : Gm →+ R)
    (hψ : ∀ (c : O) z, ψ (algebraMap O (alg O N lam) c • z) = algebraMap O R c * ψ z) (s : Finset I) (p : I → MvPolynomial Z O)
    (a : I → alg O N lam) (U : Finset (Z →₀ ℕ)) (hU : ∀ i ∈ s, (p i).support ⊆ U) (z : Gm) :
    ∑ i ∈ s, θ (p i) * ψ (a i • z) = ∑ μ ∈ U, θ (monomial μ 1) * ψ ((∑ i ∈ s, AddMonoidAlgebra.coeff (p i) μ • a i) • z) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finset.sum_smul, map_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => ?_
  have : p i = ∑ μ ∈ U, AddMonoidAlgebra.coeff (p i) μ • monomial μ 1 := by
    conv_lhs => rw [(p i).as_sum]
    simp only [smul_monomial, smul_eq_mul, mul_one]
    exact Finset.sum_subset (hU i hi) fun m _ hm => by rw [notMem_support_iff.1 hm, map_zero]
  conv_lhs => rw [this]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Algebra.smul_def (A := alg O N lam), mul_smul, hψ, map_smul, Algebra.smul_def]
  ring

theorem transfer {Z I J : Type} (θ : MvPolynomial Z O →ₐ[O] R) (ψ : Gm →+ R)
    (hψ : ∀ (c : O) z, ψ (algebraMap O (alg O N lam) c • z) = algebraMap O R c * ψ z) (τ : ι) (s : Finset I) (t : Finset J)
    (p : I → MvPolynomial Z O) (q : J → MvPolynomial Z O) (a : I → alg O N lam) (a' : J → alg O N lam)
    (b : I → Module.End O (dualWeyl O N N (res N (lam τ)))) (b' : J → Module.End O (dualWeyl O N N (res N (lam τ))))
    (hb : ∀ i, (a i : Module.End O (NablaT O N lam)) = atN O N lam τ (b i))
    (hb' : ∀ j, (a' j : Module.End O (NablaT O N lam)) = atN O N lam τ (b' j))
    (H : ∀ f : dualWeyl O N N (res N (lam τ)), ∑ i ∈ s, map C (p i) * C (b i f : MvPolynomial (Fin N × Fin N) O) =
      ∑ j ∈ t, map C (q j) * C (b' j f : MvPolynomial (Fin N × Fin N) O)) (z : Gm) :
    ∑ i ∈ s, θ (p i) * ψ (a i • z) = ∑ j ∈ t, θ (q j) * ψ (a' j • z) := by
  classical
  let U := s.biUnion (fun i => (p i).support) ∪ t.biUnion fun j => (q j).support
  rw [sum_expand θ ψ hψ s p a U (fun i hi => (Finset.subset_biUnion_of_mem (fun i => (p i).support) hi).trans Finset.subset_union_left),
    sum_expand θ ψ hψ t q a' U (fun i hi => (Finset.subset_biUnion_of_mem (fun i => (q i).support) hi).trans Finset.subset_union_right)]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have h1 : ∑ i ∈ s, AddMonoidAlgebra.coeff (p i) μ • b i = ∑ j ∈ t, AddMonoidAlgebra.coeff (q j) μ • b' j := by
    ext1 f
    apply Subtype.ext
    have := congrArg (AddMonoidAlgebra.coeff · μ) (H f)
    simp only [coeff_sum, mul_comm _ (C _), coeff_C_mul, coeff_map] at this
    simpa [smul_eq_C_mul, mul_comm] using this
  have h2 : ∑ i ∈ s, AddMonoidAlgebra.coeff (p i) μ • a i = ∑ j ∈ t, AddMonoidAlgebra.coeff (q j) μ • a' j := by
    apply Subtype.ext
    have := congrArg (atN O N lam τ) h1
    simpa [hb, hb'] using this
  rw [h2]

variable (c : ι → (Fin N × Fin N →₀ ℕ) → alg O N lam)
  (hc : ∀ τ m, (c τ m : Module.End O (NablaT O N lam)) = atN O N lam τ (coefEnd O N _ m))
  (ψ : Gm →+ R) (hψ : ∀ (c : O) z, ψ (algebraMap O (alg O N lam) c • z) = algebraMap O R c * ψ z)
include hc

theorem coef_mul_proj (τ : ι) (m : Fin N × Fin N →₀ ℕ) (v : Fin N → ℕ) :
    c τ m * projA O N lam τ v = if Finsupp.weight (rowW N N) m = v then c τ m else 0 := by
  apply Subtype.ext
  have := congrArg (atN O N lam τ) (coefEnd_mul_rowProj O N _ v m)
  rw [map_mul] at this
  split_ifs at this ⊢
  · simpa [hc, projA] using this
  · simpa [hc, projA] using this

theorem proj_mul_coef (τ : ι) (m : Fin N × Fin N →₀ ℕ) (v : Fin N → ℕ) :
    projA O N lam τ v * c τ m = if Finsupp.weight (colW N N) m = v then c τ m else 0 := by
  apply Subtype.ext
  have := congrArg (atN O N lam τ) (rowProj_mul_coefEnd O N _ v m)
  rw [map_mul] at this
  split_ifs at this ⊢
  · simpa [hc, projA] using this
  · simpa [hc, projA] using this

theorem coef_comm {τ σ : ι} (h : τ ≠ σ) (m m' : Fin N × Fin N →₀ ℕ) : c τ m * c σ m' = c σ m' * c τ m := by
  apply Subtype.ext
  simp only [MulMemClass.coe_mul, hc]
  exact atHom_comm h _ _

theorem coef_proj_comm {τ σ : ι} (h : τ ≠ σ) (m : Fin N × Fin N →₀ ℕ) (v : Fin N → ℕ) :
    c τ m * projA O N lam σ v = projA O N lam σ v * c τ m := by
  apply Subtype.ext
  simp only [MulMemClass.coe_mul, hc]
  exact atHom_comm h _ _

omit hc in
theorem proj_comm {τ σ : ι} (h : τ ≠ σ) (u v : Fin N → ℕ) :
    projA O N lam τ u * projA O N lam σ v = projA O N lam σ v * projA O N lam τ u :=
  Subtype.ext (atHom_comm h _ _)

omit hc in
theorem proj_mul_self (τ : ι) (v : Fin N → ℕ) : projA O N lam τ v * projA O N lam τ v = projA O N lam τ v :=
  Subtype.ext (by
    show atN O N lam τ _ * atN O N lam τ _ = atN O N lam τ _
    rw [← map_mul, rowProj_mul_self])

include hψ

theorem sum_unit {Z : Type} (θ : MvPolynomial Z O →ₐ[O] R) (τ : ι) (z : Gm) :
    ∑ m ∈ expSet N (res N (lam τ)), θ (unitHom O N Z (monomial m 1)) * ψ (c τ m • z) = ψ z := by
  have := transfer θ ψ hψ τ (expSet N (res N (lam τ))) {()} (fun m => unitHom O N Z (monomial m 1)) (fun _ => 1) (c τ) (fun _ => 1)
    _ (fun _ => 1) (hc τ) (fun _ => by simp) (fun f => by
      simp only [coe_coefEnd]
      rw [← extHom_genHom O N _ _ _ f.2, extHom_unit]
      simp) z
  simpa using this

theorem sum_grp (θ : MvPolynomial (Fin N × Fin N) O →ₐ[O] R) (τ : ι) (h : GL (Fin N) O) (z : Gm) :
    ∑ m ∈ expSet N (res N (lam τ)), θ (monomial m 1) * ψ (c τ m • grpA O N lam (Pi.mulSingle τ h) • z) =
      ∑ m ∈ expSet N (res N (lam τ)), θ (rowAct O ((h⁻¹ : GL (Fin N) O) : Matrix (Fin N) (Fin N) O) (monomial m 1)) * ψ (c τ m • z) := by
  simp only [smul_smul]
  refine transfer θ ψ hψ τ _ _ _ _ (fun m => c τ m * grpA O N lam (Pi.mulSingle τ h)) (c τ)
    (fun m => coefEnd O N _ m * Formalism.UG.dualWeylRep O N N (res N (lam τ)) h) _
    (fun m => by rw [map_mul, ← hc, ← grp_mulSingle]; rfl) (hc τ) (fun f => ?_) z
  simp only [coe_coefEnd, Module.End.mul_apply]
  rw [← extHom_genHom O N _ _ _ f.2, ← genHom_rowAct]
  have := extHom_genHom O N (AlgHom.id O _) _ _ (Formalism.UG.dualWeylRep O N N (res N (lam τ)) h f).2
  rw [extHom_id] at this
  exact this.symm

theorem sum_col (θ : MvPolynomial (Option (Fin N × Fin N)) O →ₐ[O] R) (τ : ι) (l j : Fin N) (z : Gm) :
    ∑ m ∈ expSet N (res N (lam τ)), θ (colAddGen O l j (monomial m 1)) * ψ (c τ m • z) =
      ∑ m ∈ expSet N (res N (lam τ)), θ (rename some (monomial m 1)) *
        ∑ m' ∈ expSet N (res N (lam τ)), θ (elemHom O N l j (monomial m' 1)) * ψ (c τ m' • c τ m • z) := by
  rw [transfer θ ψ hψ τ _ (expSet N (res N (lam τ)) ×ˢ expSet N (res N (lam τ))) _
    (fun p => rename some (monomial p.1 1) * elemHom O N l j (monomial p.2 1)) (c τ) (fun p => c τ p.2 * c τ p.1)
    _ (fun p => coefEnd O N _ p.2 * coefEnd O N _ p.1) (hc τ) (fun m => by rw [map_mul, ← hc, ← hc]; rfl) (fun f => ?_) z]
  · rw [Finset.sum_product]
    simp only [Finset.mul_sum, map_mul, mul_smul, mul_assoc]
  · simp only [coe_coefEnd, Module.End.mul_apply]
    rw [← extHom_genHom O N _ _ _ f.2, extHom_colAddGen O N l j _ _ f.2]

omit hψ in
theorem apply_coef_eq_zero_of_col (τ : ι) (w : Fin N → ℕ) (h0 : ∀ v, v ≠ w → ∀ z, ψ (projA O N lam τ v • z) = 0)
    (m : Fin N × Fin N →₀ ℕ) (hm : Finsupp.weight (colW N N) m ≠ w) (z : Gm) : ψ (c τ m • z) = 0 := by
  have := proj_mul_coef c hc τ m (Finsupp.weight (colW N N) m)
  rw [if_pos rfl] at this
  rw [← this, mul_smul, h0 _ hm]

theorem apply_proj (τ : ι) (w : Fin N → ℕ) (h0 : ∀ v, v ≠ w → ∀ z, ψ (projA O N lam τ v • z) = 0) (z : Gm) :
    ψ (projA O N lam τ w • z) = ψ z := by
  let θ : MvPolynomial Empty O →ₐ[O] R := aeval fun _ => 0
  have h1 := sum_unit c hc (ψ.comp (DistribSMul.toAddMonoidHom Gm (projA O N lam τ w))) (fun r z => by
    simp only [AddMonoidHom.comp_apply, DistribSMul.toAddMonoidHom_apply]
    rw [smul_smul, ← Algebra.commutes, mul_smul, hψ]) θ τ z
  refine h1.symm.trans ((Finset.sum_congr rfl fun m _ => ?_).trans (sum_unit c hc ψ hψ θ τ z))
  refine congrArg (_ * ·) ?_
  simp only [AddMonoidHom.comp_apply, DistribSMul.toAddMonoidHom_apply]
  rw [smul_smul, proj_mul_coef c hc]
  split_ifs with h
  · rfl
  · rw [zero_smul, map_zero, apply_coef_eq_zero_of_col c hc ψ τ w h0 m h]

theorem apply_coef_eq_zero_of_lt (w : ι → Fin N → ℕ) (hmax : ∀ w' : ι → Fin N → ℕ, JointWt O N lam Gm w' → pot N w' ≤ pot N w)
    (h0 : ∀ τ v, v ≠ w τ → ∀ z, ψ (projA O N lam τ v • z) = 0) (τ : ι) (m : Fin N × Fin N →₀ ℕ)
    (hm : ∑ v : Fin N × Fin N, (N - (v.2 : ℕ)) * m v < ∑ v : Fin N × Fin N, (N - (v.1 : ℕ)) * m v) (z : Gm) : ψ (c τ m • z) = 0 := by
  by_cases hcol : Finsupp.weight (colW N N) m = w τ
  swap
  · exact apply_coef_eq_zero_of_col c hc ψ τ _ (h0 τ) m hcol z
  set w' := Function.update w τ (Finsupp.weight (rowW N N) m) with hw'
  have key : ∀ s : Finset ι, ∃ z' : Gm, ψ (c τ m • z) = ψ (c τ m • z') ∧ ∀ σ ∈ s, projA O N lam σ (w' σ) • z' = z' := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨z, rfl, by simp⟩
    | insert σ s hσ ih =>
      obtain ⟨z', h1, h2⟩ := ih
      refine ⟨projA O N lam σ (w' σ) • z', h1.trans ?_, fun ρ hρ => ?_⟩
      · by_cases h : σ = τ
        · subst h
          rw [smul_smul, coef_mul_proj c hc, if_pos (by simp [hw'])]
        · rw [smul_smul, coef_proj_comm c hc (Ne.symm h), mul_smul, hw', Function.update_of_ne h, apply_proj c hc ψ hψ σ _ (h0 σ)]
      · rcases Finset.mem_insert.1 hρ with rfl | hρ'
        · rw [smul_smul, proj_mul_self]
        · rw [smul_smul, proj_comm (by rintro rfl; exact hσ hρ'), mul_smul, h2 ρ hρ']
  obtain ⟨z', h1, h2⟩ := key Finset.univ
  by_cases hz : z' = 0
  · rw [h1, hz, smul_zero, map_zero]
  exfalso
  have h3 := hmax w' ⟨z', hz, fun σ a ha => by rw [eq_projA O N lam ha]; exact h2 σ (Finset.mem_univ _)⟩
  refine absurd h3 (not_le.2 ?_)
  unfold pot
  apply Finset.sum_lt_sum
  · intro i _
    by_cases hi : i = τ
    · subst hi
      rw [hw', Function.update_self, ← hcol, sum_mul_weight_rowW N (fun a => N - (a : ℕ)), sum_mul_weight_colW N (fun a => N - (a : ℕ))]
      exact hm.le
    · rw [hw', Function.update_of_ne hi]
  · refine ⟨τ, Finset.mem_univ _, ?_⟩
    rw [hw', Function.update_self, ← hcol, sum_mul_weight_rowW N (fun a => N - (a : ℕ)), sum_mul_weight_colW N (fun a => N - (a : ℕ))]
    exact hm

omit hc hψ in
theorem elemHom_eq_or_lt (l j : Fin N) (hlj : l < j) (m : Fin N × Fin N →₀ ℕ) :
    elemHom O N l j (monomial m 1) = unitHom O N _ (monomial m 1) ∨
      ∑ v : Fin N × Fin N, (N - (v.2 : ℕ)) * m v < ∑ v : Fin N × Fin N, (N - (v.1 : ℕ)) * m v := by
  by_cases h1 : m (l, j) = 0
  · left
    simp only [elemHom, unitHom, aeval_monomial, Finsupp.prod]
    congr 1
    refine Finset.prod_congr rfl fun v hv => ?_
    rw [if_neg (show ¬ v = (l, j) by rintro rfl; exact Finsupp.mem_support_iff.1 hv h1), add_zero]
  by_cases h2 : ∃ v ∈ m.support, v.1 ≠ v.2 ∧ v ≠ (l, j)
  · left
    obtain ⟨v, hv, hv1, hv2⟩ := h2
    simp only [elemHom, unitHom, aeval_monomial, Finsupp.prod]
    rw [Finset.prod_eq_zero hv, Finset.prod_eq_zero hv] <;> simp [hv1, hv2, Finsupp.mem_support_iff.1 hv]
  right
  push_neg at h2
  have hl : N - (j : ℕ) < N - (l : ℕ) := by have := j.isLt; have : (l : ℕ) < j := hlj; omega
  apply Finset.sum_lt_sum
  · intro v _
    by_cases hv : m v = 0
    · simp [hv]
    by_cases h : v.1 = v.2
    · rw [h]
    · rw [h2 v (Finsupp.mem_support_iff.2 hv) h]
      exact Nat.mul_le_mul_right _ hl.le
  · exact ⟨(l, j), Finset.mem_univ _, Nat.mul_lt_mul_of_pos_right hl (Nat.pos_of_ne_zero h1)⟩

theorem sum_col_eq (θ : MvPolynomial (Option (Fin N × Fin N)) O →ₐ[O] R) (τ : ι) (l j : Fin N) (hlj : l < j)
    (h0 : ∀ m : Fin N × Fin N →₀ ℕ, ∑ v : Fin N × Fin N, (N - (v.2 : ℕ)) * m v < ∑ v : Fin N × Fin N, (N - (v.1 : ℕ)) * m v →
      ∀ z, ψ (c τ m • z) = 0) (z : Gm) :
    ∑ m ∈ expSet N (res N (lam τ)), θ (colAddGen O l j (monomial m 1)) * ψ (c τ m • z) =
      ∑ m ∈ expSet N (res N (lam τ)), θ (rename some (monomial m 1)) * ψ (c τ m • z) := by
  rw [sum_col c hc ψ hψ]
  refine Finset.sum_congr rfl fun m _ => ?_
  refine congrArg (_ * ·) (Eq.trans ?_ (sum_unit c hc ψ hψ θ τ (c τ m • z)))
  refine Finset.sum_congr rfl fun m' _ => ?_
  rcases elemHom_eq_or_lt (O := O) l j hlj m' with h | h
  · rw [h]
  · rw [h0 m' h, mul_zero, mul_zero]

end GlobalTheory.HighWtEmb

end
