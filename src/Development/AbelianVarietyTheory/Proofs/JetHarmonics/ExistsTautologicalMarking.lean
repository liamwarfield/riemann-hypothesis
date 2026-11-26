module

public import Development.AbelianVarietyTheory.BlockTheory.JetGauges.ThetaSpanAdjoint

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsTautologicalMarking
set_option autoImplicit false

open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.Jets.TautMarking

theorem exists_tautological_marking :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n Q : ℕ) (Λ : GenLat E n), 0 < Q → Λ.Unimod → Λ.TrivAt Q → ∃ κ : Λ.La →ₗ[𝓞 E] GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass.StdMod E n Q, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass.IsMarking Q Λ κ ∧ ∀ (v : Λ.La) (x : Fin n → 𝓞 E), (∀ j, κ v j = Ideal.Quotient.mk _ (x j)) → GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass.CongrAt Q (v : Fin n → E) fun j => (x j : E) := by
  intro E _ _ _ n Q Λ _ hU ⟨k, hk, h1, h2⟩
  obtain ⟨a, b, hab⟩ : IsCoprime (k : 𝓞 E) (Q : 𝓞 E) := Nat.Coprime.cast hk
  have habE : (a : E) * (k : E) + (b : E) * (Q : E) = 1 := by
    have := congrArg (algebraMap (𝓞 E) E) hab
    simpa using this
  have hf : ∀ (v : Λ.La) (j : Fin n), ∃ s : 𝓞 E, (s : E) = (k : E) * (v : Fin n → E) j := by
    intro v j
    have := h1 (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self (k : 𝓞 E)) v.2) j (Set.mem_univ j)
    obtain ⟨s, hs⟩ := Submodule.mem_one.mp this
    refine ⟨s, ?_⟩
    simpa [Algebra.smul_def] using hs
  choose f hf using hf
  have hg : ∀ x : Fin n → 𝓞 E, (fun j => (k : E) * (x j : E)) ∈ Λ.La := by
    intro x
    have hx : (fun j => (x j : E)) ∈ stdLat E n := fun j _ => Submodule.mem_one.mpr ⟨x j, rfl⟩
    have := h2 (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self (k : 𝓞 E)) hx)
    convert this using 1
    ext j
    simp [Algebra.smul_def]
  have inj : Function.Injective (fun s : 𝓞 E => (s : E)) := RingOfIntegers.coe_injective
  let F : Λ.La →ₗ[𝓞 E] (Fin n → 𝓞 E) :=
    { toFun := f
      map_add' := fun v w => funext fun j => inj (by simp [hf, mul_add])
      map_smul' := fun c v => funext fun j => inj (by
        simp [hf, Algebra.smul_def]; ring) }
  let κ : Λ.La →ₗ[𝓞 E] GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass.StdMod E n Q :=
    LinearMap.pi fun j => (Ideal.span {(Q : 𝓞 E)}).mkQ ∘ₗ (a • (LinearMap.proj j ∘ₗ F))
  have hκ : ∀ v j, κ v j = Ideal.Quotient.mk _ (a * f v j) := fun v j => rfl
  have key : ∀ (v : Λ.La) (j : Fin n) (x : 𝓞 E), κ v j = Ideal.Quotient.mk _ x →
      ∃ t : 𝓞 E, (a : E) * ((k : E) * (v : Fin n → E) j) - (x : E) = (Q : E) * (t : E) := by
    intro v j x h
    rw [hκ, Ideal.Quotient.eq, Ideal.mem_span_singleton] at h
    obtain ⟨t, ht⟩ := h
    refine ⟨t, ?_⟩
    have := congrArg (algebraMap (𝓞 E) E) ht
    rw [← hf]
    simpa using this
  have key2 : ∀ (v : Λ.La) (j : Fin n) (x : 𝓞 E), κ v j = Ideal.Quotient.mk _ x →
      ∃ s : 𝓞 E, (k : E) * ((v : Fin n → E) j - (x : E)) = (Q : E) * (s : E) := by
    intro v j x h
    obtain ⟨t, ht⟩ := key v j x h
    refine ⟨b * f v j + k * t, ?_⟩
    have e : ((b * f v j + k * t : 𝓞 E) : E) = (b : E) * ((k : E) * (v : Fin n → E) j) + (k : E) * (t : E) := by
      rw [← hf]; simp
    rw [e]
    linear_combination (k : E) * ht - (k : E) * (v : Fin n → E) j * habE
  refine ⟨κ, ⟨?_, ?_, ?_⟩, fun v x h => ⟨k, hk, fun j => key2 v j (x j) (h j)⟩⟩
  · intro z
    choose x hx using fun j => Ideal.Quotient.mk_surjective (z j)
    refine ⟨⟨_, hg fun j => a * x j⟩, funext fun j => ?_⟩
    have e : f ⟨_, hg fun j => a * x j⟩ j = k * (k * (a * x j)) := inj (by simp [hf])
    rw [hκ, e, ← hx, Ideal.Quotient.eq, Ideal.mem_span_singleton]
    exact ⟨-b * (a * k + 1) * x j, by linear_combination (a * k + 1) * x j * hab⟩
  · intro v
    constructor
    · intro h
      choose t ht using fun j => key v j 0 (by rw [h]; simp)
      refine ⟨a • (⟨_, hg t⟩ : Λ.La) + (a * b * k + b) • v, Subtype.ext (funext fun j => ?_)⟩
      have := ht j
      simp [Algebra.smul_def] at this ⊢
      linear_combination (a : E) * (k : E) * this - ((a : E) * k + 1) * (v : Fin n → E) j * habE
    · rintro ⟨u, rfl⟩
      funext j
      rw [map_nsmul, Pi.smul_apply, hκ, Pi.zero_apply, ← map_nsmul, Ideal.Quotient.eq_zero_iff_mem,
        Ideal.mem_span_singleton, nsmul_eq_mul]
      exact dvd_mul_right _ _
  · intro v w x y hx hy
    choose s hs using fun j => key2 v j (x j) (hx j)
    choose t ht using fun j => key2 w j (y j) (hy j)
    obtain ⟨d, hd⟩ := (hU v).mp v.2 w w.2
    set c := IsCMField.ringOfIntegersComplexConj E with hc
    have hcc : ∀ z : 𝓞 E, ((c z : 𝓞 E) : E) = IsCMField.complexConj E (z : E) :=
      fun z => IsCMField.coe_ringOfIntegersComplexConj E z
    have hs' : ∀ j, (k : E) * (IsCMField.complexConj E ((v : Fin n → E) j) - IsCMField.complexConj E (x j : E)) =
        (Q : E) * IsCMField.complexConj E (s j : E) := fun j => by
      simpa using congrArg (IsCMField.complexConj E) (hs j)
    let e : 𝓞 E := ∑ j, (c (s j) * k * y j + k * c (x j) * t j + Q * c (s j) * t j)
    let d' : 𝓞 E := d - ∑ j, c (x j) * y j
    have hd' : (d' : E) = ∑ j, IsCMField.complexConj E ((v : Fin n → E) j) * (w : Fin n → E) j -
        ∑ j, IsCMField.complexConj E (x j : E) * (y j : E) := by
      rw [← hd]
      simp [d', ← hcc]
    have he : (k : E) ^ 2 * (d' : E) = (Q : E) * (e : E) := by
      have e1 : (e : E) = ∑ j, (IsCMField.complexConj E (s j : E) * k * (y j : E) +
          k * IsCMField.complexConj E (x j : E) * (t j : E) + Q * IsCMField.complexConj E (s j : E) * (t j : E)) := by
        simp [e, ← hcc]
      rw [hd', e1, ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      linear_combination ((k : E) * (w : Fin n → E) j) * hs' j +
        ((k : E) * IsCMField.complexConj E (x j : E) + Q * IsCMField.complexConj E (s j : E)) * ht j
    refine ⟨a ^ 2 * e + (2 * a * k * b + b ^ 2 * Q) * d', ?_⟩
    rw [← hd']
    have e2 : ((a ^ 2 * e + (2 * a * k * b + b ^ 2 * Q) * d' : 𝓞 E) : E) =
        (a : E) ^ 2 * (e : E) + (2 * (a : E) * k * b + (b : E) ^ 2 * Q) * (d' : E) := by
      simp only [RingOfIntegers.coe_eq_algebraMap, map_add (f := _), map_mul, map_pow, map_natCast, map_ofNat]
    rw [e2]
    linear_combination (a : E) ^ 2 * he - ((a : E) * k + b * Q + 1) * (d' : E) * habE

end GlobalTheory.Jets.TautMarking
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.PushMemHarmK
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PushHarm

open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (c : Coeff l) {n : ℕ}

theorem push_X (γ : Matrix (Fin n) (Fin n) E) (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) (j : Fin n) :
    push c γ (X (⟨σ, i, j⟩ : LtN Dw n)) =
      ∑ k, C (embF c σ (γ k j)) * X (⟨σ, i, k⟩ : LtN Dw n) := by
  simp [push, letB]

open Classical in
theorem pderiv_push_X (γ : Matrix (Fin n) (Fin n) E) (τ : E →+* ℂ) (a : Fin (Dw.mult τ)) (b : Fin n)
    (ℓ : LtN Dw n) :
    pderiv (⟨τ, a, b⟩ : LtN Dw n) (push c γ (X ℓ)) =
      ∑ j, embF c τ (γ b j) • push c γ (pderiv (⟨τ, a, j⟩ : LtN Dw n) (X ℓ)) := by
  obtain ⟨σ, i, j⟩ := ℓ
  set_option synthInstance.maxHeartbeats 100000 in
    rw [push_X, map_sum]
  simp only [pderiv_C_mul, pderiv_X]
  by_cases hσ : σ = τ
  · subst hσ
    by_cases hi : i = a
    · subst hi
      rw [Finset.sum_eq_single b, Finset.sum_eq_single j]
      · simp [smul_eq_C_mul]
      · intro k _ hk
        rw [Pi.single_eq_of_ne]
        · simp
        · simpa using hk.symm
      · simp
      · intro k _ hk
        rw [Pi.single_eq_of_ne]
        · simp
        · simpa using hk
      · simp
    · rw [Finset.sum_eq_zero, Finset.sum_eq_zero]
      · intro k _
        rw [Pi.single_eq_of_ne]
        · simp
        · simp [hi]
      · intro k _
        rw [Pi.single_eq_of_ne]
        · simp
        · simp [hi]
  · rw [Finset.sum_eq_zero, Finset.sum_eq_zero]
    · intro k _
      rw [Pi.single_eq_of_ne]
      · simp
      · exact fun h => hσ (congrArg Sigma.fst h)
    · intro k _
      rw [Pi.single_eq_of_ne]
      · simp
      · exact fun h => hσ (congrArg Sigma.fst h)

theorem pderiv_push (γ : Matrix (Fin n) (Fin n) E) (τ : E →+* ℂ) (a : Fin (Dw.mult τ)) (b : Fin n)
    (P : MvPolynomial (LtN Dw n) c.F) :
    pderiv (⟨τ, a, b⟩ : LtN Dw n) (push c γ P) =
      ∑ j, embF c τ (γ b j) • push c γ (pderiv (⟨τ, a, j⟩ : LtN Dw n) P) := by
  induction P using MvPolynomial.induction_on with
  | C x => simp [push]
  | add p q hp hq => simp [hp, hq, Finset.sum_add_distrib]
  | mul_X p ℓ hp =>
    rw [map_mul, Derivation.leibniz, hp, pderiv_push_X]
    simp only [Derivation.leibniz, smul_eq_mul, map_add (f := _), map_mul, smul_add, Finset.sum_add_distrib,
      Finset.mul_sum, mul_smul_comm]

theorem lap_one_apply {T : Type} {r : T → ℕ} {k : Type} [Field k] (τ τ' : T) (a : Fin (r τ))
    (a' : Fin (r τ')) (P : MvPolynomial (Letter T r n) k) :
    lap r n k 1 τ τ' a a' P =
      ∑ b, pderiv (⟨τ, a, b⟩ : Letter T r n) (pderiv (⟨τ', a', b⟩ : Letter T r n) P) := by
  simp [lap, Matrix.one_apply, LinearMap.sum_apply, ite_smul]

theorem lap_push (γ : Matrix (Fin n) (Fin n) E) (hγ : IsUnitary γ) (τ : E →+* ℂ) (a : Fin (Dw.mult τ))
    (a' : Fin (Dw.mult (ComplexEmbedding.conjugate τ))) (P : MvPolynomial (LtN Dw n) c.F) :
    lap Dw.mult n c.F 1 τ (ComplexEmbedding.conjugate τ) a a' (push c γ P) =
      push c γ (lap Dw.mult n c.F 1 τ (ComplexEmbedding.conjugate τ) a a' P) := by
  have hc : ∀ x : E, embF c (ComplexEmbedding.conjugate τ) x = embF c τ (IsCMField.complexConj E x) :=
    fun x => Subtype.ext (IsCMField.complexEmbedding_complexConj E τ x).symm
  have hu : ∀ j' j : Fin n, ∑ b, embF c (ComplexEmbedding.conjugate τ) (γ b j') * embF c τ (γ b j) =
      if j' = j then 1 else 0 := by
    intro j' j
    have h := congrArg (embF c τ) (congrFun (congrFun hγ j') j)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul,
      Matrix.one_apply, apply_ite (embF c τ), map_one, map_zero] at h
    simpa only [hc] using h
  set_option synthInstance.maxHeartbeats 100000 in
    rw [lap_one_apply, lap_one_apply, map_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [pderiv_push, map_sum, Derivation.map_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j' _ => ?_
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, hu, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]

theorem push_mem_harmK : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (c : Coeff l) (n : ℕ) (γ : Matrix (Fin n) (Fin n) E) (P : MvPolynomial (LtN Dw n) c.F),
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass.IsUnitary γ →
    P ∈ harmK Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun _ => 1) →
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass.push (Dw := Dw) c γ P ∈
      harmK Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun _ => 1) := by
  intro E _ _ _ H Dw l c n γ P hγ hP
  simp only [harmK, Submodule.mem_iInf, LinearMap.mem_ker] at hP ⊢
  intro τ hτ a a'
  rw [lap_push c γ hγ, hP τ hτ a a', map_zero]

end GlobalTheory.PushHarm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ColumnMapShift
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Proof.ColumnMapShift

open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

theorem aeval_weightedHomogeneous {K σ τ : Type} [CommRing K] {w : σ → ℕ} {w' : τ → ℕ}
    {φ : MvPolynomial σ K} {m : ℕ} (hφ : IsWeightedHomogeneous w φ m)
    (v : σ → MvPolynomial τ K) (hv : ∀ i, IsWeightedHomogeneous w' (v i) (w i)) :
    IsWeightedHomogeneous w' (aeval v φ) m := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [φ.as_sum, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_
  rw [aeval_monomial]
  have hdeg : (Finsupp.weight w) d = m := hφ (mem_support_iff.mp hd)
  have h1 : IsWeightedHomogeneous w' (d.prod fun i k => v i ^ k) (∑ i ∈ d.support, d i • w i) :=
    IsWeightedHomogeneous.prod _ _ _ fun i _ => (hv i).pow (d i)
  have h2 : (∑ i ∈ d.support, d i • w i) = m := by
    rw [← hdeg, Finsupp.weight_apply, Finsupp.sum]
  rw [h2] at h1
  have h3 := (isWeightedHomogeneous_C w' (AddMonoidAlgebra.coeff φ d)).mul h1
  rw [zero_add] at h3
  rw [MvPolynomial.algebraMap_eq]
  exact h3

section Col

variable {T : Type} {r : T → ℕ} {n : ℕ} {k : Type} [Field k]

def colMap (r : T → ℕ) (g : T → Fin n → Fin n → k) :
    MvPolynomial (Letter T r n) k →ₐ[k] MvPolynomial (Letter T r n) k :=
  aeval fun ℓ : Letter T r n => ∑ b, C (g ℓ.1 b ℓ.2.2) * X (⟨ℓ.1, ℓ.2.1, b⟩ : Letter T r n)

theorem rowShift_X_self (σ : T) (i i' : Fin (r σ)) (t : k) (b : Fin n) :
    rowShift r n k σ i i' t (X ⟨σ, i, b⟩) = X ⟨σ, i, b⟩ + C t * X ⟨σ, i', b⟩ := by
  rw [rowShift, aeval_X, if_pos ⟨b, rfl⟩]

theorem rowShift_X_ne (σ : T) (i i' : Fin (r σ)) (t : k) (τ : T) (j : Fin (r τ))
    (h : (⟨τ, j⟩ : Σ s, Fin (r s)) ≠ ⟨σ, i⟩) (b : Fin n) :
    rowShift r n k σ i i' t (X ⟨τ, j, b⟩) = X ⟨τ, j, b⟩ := by
  rw [rowShift, aeval_X, if_neg]
  rintro ⟨b', hb⟩
  apply h
  exact congrArg (fun ℓ : Letter T r n => (⟨ℓ.1, ℓ.2.1⟩ : Σ s, Fin (r s))) hb

theorem colMap_X (g : T → Fin n → Fin n → k) (τ : T) (j : Fin (r τ)) (b : Fin n) :
    colMap r g (X ⟨τ, j, b⟩) = ∑ b', C (g τ b' b) * X (⟨τ, j, b'⟩ : Letter T r n) := by
  rw [colMap, aeval_X]

theorem rowShift_colMap (g : T → Fin n → Fin n → k) (σ : T) (i i' : Fin (r σ)) (t : k)
    (P : MvPolynomial (Letter T r n) k) :
    rowShift r n k σ i i' t (colMap r g P) = colMap r g (rowShift r n k σ i i' t P) := by
  have h : (rowShift r n k σ i i' t).comp (colMap r g) = (colMap r g).comp (rowShift r n k σ i i' t) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨τ, j, b⟩
    simp only [AlgHom.comp_apply]
    by_cases h : (⟨τ, j⟩ : Σ s, Fin (r s)) = ⟨σ, i⟩
    · cases h
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [rowShift_X_self, colMap_X, map_sum, map_mul, map_add (f := _), algHom_C, algebraMap_eq,
        Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    set_option synthInstance.maxHeartbeats 100000 in
      · simp only [rowShift_X_ne σ i i' t τ j h, colMap_X, map_sum, map_mul, algHom_C, algebraMap_eq]
  exact DFunLike.congr_fun h P

theorem rowInv_colMap (g : T → Fin n → Fin n → k) {P : MvPolynomial (Letter T r n) k}
    (hP : RowInv r n k P) : RowInv r n k (colMap r g P) := by
  intro σ i i' hi t
  rw [rowShift_colMap, hP σ i i' hi t]


open Classical in
def rowWt (n : ℕ) (σ : T) (i : Fin (r σ)) (ℓ : Letter T r n) : ℕ :=
  if (⟨ℓ.1, ℓ.2.1⟩ : Σ s, Fin (r s)) = ⟨σ, i⟩ then 1 else 0

theorem weight_rowWt [Fintype T] (σ : T) (i : Fin (r σ)) (m : Letter T r n →₀ ℕ) :
    Finsupp.weight (rowWt n σ i) m = ∑ b : Fin n, m ⟨σ, i, b⟩ := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sigma,
    Finset.sum_eq_single σ, Fintype.sum_prod_type, Finset.sum_eq_single i]
  · simp [rowWt]
  · intro j _ hj
    simp [rowWt, hj]
  · simp
  · intro σ' _ hσ
    simp [rowWt, hσ]
  · simp

theorem rowDeg_colMap [Fintype T] (g : T → Fin n → Fin n → k) {a : T → ℕ → ℕ}
    {P : MvPolynomial (Letter T r n) k} (hP : RowDeg r n k a P) : RowDeg r n k a (colMap r g P) := by
  intro m hm σ i
  have h1 : IsWeightedHomogeneous (rowWt n σ i) P (a σ i) := by
    intro d hd
    rw [weight_rowWt]
    exact hP d (mem_support_iff.2 hd) σ i
  have h2 : IsWeightedHomogeneous (rowWt n σ i) (colMap r g P) (a σ i) := by
    refine aeval_weightedHomogeneous h1 _ fun ℓ => ?_
    refine IsWeightedHomogeneous.sum _ _ _ fun b _ => ?_
    exact IsWeightedHomogeneous.C_mul (isWeightedHomogeneous_X k (rowWt n σ i) ⟨ℓ.1, ℓ.2.1, b⟩) _
  rw [← weight_rowWt]
  exact h2 (mem_support_iff.1 hm)

end Col

theorem push_rows : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (n : ℕ) (γ : Matrix (Fin n) (Fin n) E) (P : MvPolynomial (LtN Dw n) c.F), ∀ (a : (E →+* ℂ) → ℕ → ℕ), (RowInv Dw.mult n c.F P → RowInv Dw.mult n c.F (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass.push (Dw := Dw) c γ P)) ∧ (RowDeg Dw.mult n c.F a P → RowDeg Dw.mult n c.F a (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass.push (Dw := Dw) c γ P)) := by
  intro E _ _ _ H Dw l c n γ P a
  have e : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass.push (Dw := Dw) c γ = colMap Dw.mult fun σ b j => embF c σ (γ b j) := rfl
  rw [e]
  exact ⟨rowInv_colMap _, rowDeg_colMap _⟩

end GlobalTheory.Proof.ColumnMapShift
end
end
