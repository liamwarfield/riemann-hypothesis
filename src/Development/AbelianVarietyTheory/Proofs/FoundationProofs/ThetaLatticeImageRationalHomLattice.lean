module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
public import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.PeriodLatticeAgreement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RationalPointsIntegralPointsMembership
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardFiniteSubgroupGLIntDvd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCmIdempotentsSelectConjugatePrimes

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaLatticeImageRationalHomLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaLatticeImageRationalHomLattice
noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

namespace GlobalTheory.ThetaLatImage

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ}

theorem pt_apply (z : Matrix (Fin N') (Fin N) D.host.E) (τ : D.what₂.Tau) (i : Fin N') (j : Fin N) :
    pt D (tor0 D cc δ) δ z τ i j = δ * embT D τ (z i j) := rfl

theorem pt_zero : pt D (tor0 D cc δ) δ (0 : Matrix (Fin N') (Fin N) D.host.E) = 0 := by
  funext τ i j
  simp [pt_apply]

theorem pt_add (z w : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ (z + w) = pt D (tor0 D cc δ) δ z + pt D (tor0 D cc δ) δ w := by
  funext τ i j
  simp [pt_apply, mul_add]

theorem pt_neg (z : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ (-z) = -pt D (tor0 D cc δ) δ z := by
  funext τ i j
  simp [pt_apply]

theorem pt_smulK (c : D.host.K) (A : Matrix (Fin N') (Fin N) D.host.E) :
    (δ * D.host.φ₀ (c : D.host.E)) • embV D (tor0 D cc δ) A =
      pt D (tor0 D cc δ) δ ((c : D.host.E) • A) := by
  funext τ i j
  change (δ * D.host.φ₀ (c : D.host.E)) * embT D τ (A i j) = δ * embT D τ ((c : D.host.E) * A i j)
  rw [map_mul, (GlobalTheory.InducedType.induced_type D).1.1 τ c, mul_assoc]

theorem pt_injective (hδ : δ ≠ 0) :
    Function.Injective (pt D (tor0 D cc δ) δ : Matrix (Fin N') (Fin N) D.host.E → VC D N N') := by
  obtain ⟨τ⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm ⟨1, by simp⟩⟩
  intro z w h
  refine Matrix.ext fun i j => ?_
  have h1 := congrFun (congrFun (congrFun h τ) i) j
  rw [pt_apply, pt_apply] at h1
  exact (embT D τ).injective (mul_left_cancel₀ hδ h1)

theorem mem_homL {L : Lat D N} {L' : Lat D N'} {A : Matrix (Fin N') (Fin N) D.host.E} :
    A ∈ homL D L L' ↔ ∀ x ∈ L, A.mulVec x ∈ L' := by
  refine ⟨fun h => ?_, fun h => Submodule.subset_span h⟩
  induction h using Submodule.span_induction with
  | mem A hA => exact hA
  | zero => intro x _; rw [Matrix.zero_mulVec]; exact L'.zero_mem
  | add A B _ _ hA hB => intro x hx; rw [Matrix.add_mulVec]; exact L'.add_mem (hA x hx) (hB x hx)
  | smul o A _ hA => intro x hx; rw [Matrix.smul_mulVec]; exact L'.smul_mem o (hA x hx)

theorem mem_stdL {x : Fin N → D.host.E} : x ∈ stdL D N ↔ ∀ i, IntE D (x i) := by
  simp only [stdL, Submodule.mem_pi, Set.mem_univ, true_imp_iff, Submodule.mem_one, IntE, RingHom.mem_range]

theorem smul_mem_RL {L : Lat D N} {L' : Lat D N'} {c : 𝓞 D.host.K} (hc : c ∈ cc)
    {A : Matrix (Fin N') (Fin N) D.host.E} (hA : A ∈ YYl D L L') :
    ((c : D.host.K) : D.host.E) • A ∈ RL D cc L L' := by
  induction hA using Submodule.span_induction with
  | mem A hA =>
    obtain ⟨a, ha, B, hB, rfl⟩ := hA
    exact Submodule.subset_span ⟨_, Submodule.subset_span ⟨c, hc, a, ha, rfl⟩, B, hB, smul_smul _ _ _⟩
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add A B _ _ hA hB => rw [smul_add]; exact Submodule.add_mem _ hA hB
  | smul o A _ hA => rw [smul_comm]; exact Submodule.smul_mem _ o hA

theorem La_sub {L : Lat D N} {L' : Lat D N'} {x : VC D N N'} (hx : x ∈ La D (tor0 D cc δ) L L') :
    ∃ z ∈ RL D cc L L', x = pt D (tor0 D cc δ) δ z := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, hw, A, hA, rfl⟩ := hx
    change w ∈ lamOf D cc δ at hw
    induction hw using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨c, hc, rfl⟩ := hw
      exact ⟨_, smul_mem_RL hc hA, pt_smulK _ _⟩
    | zero => exact ⟨0, Submodule.zero_mem _, by rw [zero_smul, pt_zero]⟩
    | add w w' _ _ h h' =>
      obtain ⟨z, hz, e⟩ := h
      obtain ⟨z', hz', e'⟩ := h'
      exact ⟨z + z', Submodule.add_mem _ hz hz', by rw [add_smul, e, e', pt_add]⟩
    | neg w _ h =>
      obtain ⟨z, hz, e⟩ := h
      exact ⟨-z, Submodule.neg_mem _ hz, by rw [neg_smul, e, pt_neg]⟩
  | zero => exact ⟨0, Submodule.zero_mem _, pt_zero.symm⟩
  | add w w' _ _ h h' =>
    obtain ⟨z, hz, e⟩ := h
    obtain ⟨z', hz', e'⟩ := h'
    exact ⟨z + z', Submodule.add_mem _ hz hz', by rw [e, e', pt_add]⟩
  | neg w _ h =>
    obtain ⟨z, hz, e⟩ := h
    exact ⟨-z, Submodule.neg_mem _ hz, by rw [e, pt_neg]⟩

theorem pt_mem_La {L : Lat D N} {L' : Lat D N'} {z : Matrix (Fin N') (Fin N) D.host.E}
    (hz : z ∈ RL D cc L L') (o : 𝓞 D.host.E) :
    pt D (tor0 D cc δ) δ (o • z) ∈ La D (tor0 D cc δ) L L' := by
  induction hz using Submodule.span_induction generalizing o with
  | mem z hz =>
    obtain ⟨t, ht, A, hA, rfl⟩ := hz
    induction ht using Submodule.span_induction generalizing o with
    | mem t ht =>
      obtain ⟨c, hc, a, ha, rfl⟩ := ht
      rw [mul_smul, smul_comm, ← pt_smulK]
      exact AddSubgroup.subset_closure ⟨_, AddSubgroup.subset_closure ⟨c, hc, rfl⟩, _,
        Submodule.smul_mem _ o (Submodule.subset_span ⟨a, ha, A, hA, rfl⟩), rfl⟩
    | zero => rw [zero_smul, smul_zero, pt_zero]; exact zero_mem _
    | add t t' _ _ h h' => rw [add_smul, smul_add, pt_add]; exact add_mem (h o) (h' o)
    | smul o' t _ h => rw [smul_assoc, smul_smul]; exact h _
  | zero => rw [smul_zero, pt_zero]; exact zero_mem _
  | add t t' _ _ h h' => rw [smul_add, pt_add]; exact add_mem (h o) (h' o)
  | smul o' t _ h => rw [smul_smul]; exact h _

def colM (D : D7) {N N' : ℕ} (j : Fin N) :
    (Fin N' → D.host.E) →ₗ[D.host.E] Matrix (Fin N') (Fin N) D.host.E where
  toFun v := Matrix.of fun i k => if k = j then v i else 0
  map_add' v w := by ext i k; by_cases h : k = j <;> simp [h]
  map_smul' a v := by ext i k; by_cases h : k = j <;> simp [h]

def rowM (D : D7) {N N' : ℕ} (i : Fin N') :
    (Fin N → D.host.E) →ₗ[D.host.E] Matrix (Fin N') (Fin N) D.host.E where
  toFun v := Matrix.of fun k j => if k = i then v j else 0
  map_add' v w := by ext k j; by_cases h : k = i <;> simp [h]
  map_smul' a v := by ext k j; by_cases h : k = i <;> simp [h]

theorem map_span_mem {M M' : Type} [AddCommGroup M] [Module D.host.E M] [Module (𝓞 D.host.E) M]
    [IsScalarTower (𝓞 D.host.E) D.host.E M] [AddCommGroup M'] [Module D.host.E M']
    [Module (𝓞 D.host.E) M'] [IsScalarTower (𝓞 D.host.E) D.host.E M'] (f : M →ₗ[D.host.E] M')
    {S : Set M} {S' : Set M'} (h : ∀ x ∈ S, f x ∈ S') {x : M}
    (hx : x ∈ Submodule.span (𝓞 D.host.E) S) : f x ∈ Submodule.span (𝓞 D.host.E) S' := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span (h x hx)
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul o x _ hx => rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ o hx

theorem mem_RL_cols (L' : Lat D N') (z : Matrix (Fin N') (Fin N) D.host.E) :
    z ∈ RL D cc (stdL D N) L' ↔ ∀ j, (fun i => z i j) ∈
      Submodule.span (𝓞 D.host.E) {v | ∃ t ∈ Iid D cc, ∃ y ∈ L', v = t • y} := by
  constructor
  · intro hz j
    let f : Matrix (Fin N') (Fin N) D.host.E →ₗ[D.host.E] (Fin N' → D.host.E) :=
      { toFun := fun z i => z i j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    refine map_span_mem f ?_ hz
    rintro _ ⟨t, ht, A, hA, rfl⟩
    refine ⟨t, ht, f A, ?_, map_smul _ _ _⟩
    have h1 : (Pi.single j 1 : Fin N → D.host.E) ∈ stdL D N := by
      refine mem_stdL.2 fun i => ?_
      by_cases h : i = j
      · subst h; rw [Pi.single_eq_same]; exact one_mem _
      · rw [Pi.single_eq_of_ne h]; exact zero_mem _
    have h2 := mem_homL.1 hA _ h1
    rw [Matrix.mulVec_single_one] at h2
    exact h2
  · intro h
    have e : z = ∑ j, colM D j (fun i => z i j) := by
      ext i k
      simp [colM, Matrix.sum_apply]
    rw [e]
    refine Submodule.sum_mem _ fun j _ => map_span_mem (colM D j) ?_ (h j)
    rintro _ ⟨t, ht, y, hy, rfl⟩
    refine ⟨t, ht, colM D j y, mem_homL.2 fun x hx => ?_, map_smul _ _ _⟩
    obtain ⟨o, ho⟩ := mem_stdL.1 hx j
    have : (colM D j y).mulVec x = o • y := by
      funext i
      simp [colM, Matrix.mulVec, dotProduct, ← ho, Algebra.smul_def, mul_comm]
    rw [this]
    exact L'.smul_mem o hy

theorem mem_RL_rows (L : Lat D N) (hL : SD D L) (z : Matrix (Fin N') (Fin N) D.host.E) :
    z ∈ RL D cc L (stdL D N') ↔ ∀ i, z i ∈ Submodule.span (𝓞 D.host.E)
      {v | ∃ t ∈ Iid D cc, ∃ y ∈ L, v = t • fun j => D.host.conj (y j)} := by
  have hs := ((sd_iff D L).1 hL).2.2
  constructor
  · intro hz i
    let f : Matrix (Fin N') (Fin N) D.host.E →ₗ[D.host.E] (Fin N → D.host.E) :=
      { toFun := fun z => z i, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    refine map_span_mem f ?_ hz
    rintro _ ⟨t, ht, A, hA, rfl⟩
    refine ⟨t, ht, fun j => D.host.conj (A i j), (hs _).2 fun x hx => ?_, ?_⟩
    · have h2 := (mem_stdL.1 (mem_homL.1 hA x hx) i).conj
      have e : hE D (fun j => D.host.conj (A i j)) x = D.host.conj (A.mulVec x i) := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [hE, Matrix.mulVec, dotProduct, map_sum, map_mul]
      rw [e]; exact h2
    · simp only [conj_conj]; rfl
  · intro h
    have e : z = ∑ i, rowM D i (z i) := by
      ext i k
      simp [rowM, Matrix.sum_apply]
    rw [e]
    refine Submodule.sum_mem _ fun i _ => map_span_mem (rowM D i) ?_ (h i)
    rintro _ ⟨t, ht, y, hy, rfl⟩
    refine ⟨t, ht, rowM D i _, mem_homL.2 fun x hx => mem_stdL.2 fun k => ?_, map_smul _ _ _⟩
    by_cases hk : k = i
    · have e : (rowM D i fun j => D.host.conj (y j)).mulVec x k = hE D x y := by
        simp [rowM, Matrix.mulVec, dotProduct, hk, hE, mul_comm]
      rw [e]; exact (hs x).1 hx y hy
    · have e : (rowM D i fun j => D.host.conj (y j)).mulVec x k = 0 := by
        simp [rowM, Matrix.mulVec, dotProduct, hk]
      rw [e]; exact zero_mem _

theorem theta_lattice_image : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), δ ≠ 0 → ∀ (N N' : ℕ), Function.Injective (pt D (tor0 D cc δ) δ : Matrix (Fin N') (Fin N) D.host.E → VC D N N') ∧ (∀ (L : Lat D N) (L' : Lat D N') (x : VC D N N'), x ∈ La D (tor0 D cc δ) L L' ↔ ∃ z ∈ RL D cc L L', x = pt D (tor0 D cc δ) δ z) ∧ (∀ (L' : Lat D N') (z : Matrix (Fin N') (Fin N) D.host.E), z ∈ RL D cc (stdL D N) L' ↔ ∀ j, (fun i => z i j) ∈ Submodule.span (𝓞 D.host.E) {v | ∃ t ∈ Iid D cc, ∃ y ∈ L', v = t • y}) ∧ ∀ (L : Lat D N), SD D L → ∀ (z : Matrix (Fin N') (Fin N) D.host.E), z ∈ RL D cc L (stdL D N') ↔ ∀ i, z i ∈ Submodule.span (𝓞 D.host.E) {v | ∃ t ∈ Iid D cc, ∃ y ∈ L, v = t • fun j => D.host.conj (y j)} := by
  intro D cc δ hδ N N'
  refine ⟨pt_injective hδ, fun L L' x => ⟨La_sub, ?_⟩, mem_RL_cols, mem_RL_rows⟩
  rintro ⟨z, hz, rfl⟩
  simpa using pt_mem_La (δ := δ) hz 1

end GlobalTheory.ThetaLatImage
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaLatticeImageRationalHomLatticeStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLattice_image_rationalHomLattice : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), δ ≠ 0 → ∀ (N N' : ℕ), Function.Injective (pt D (tor0 D cc δ) δ : Matrix (Fin N') (Fin N) D.host.E → VC D N N') ∧ (∀ (L : Lat D N) (L' : Lat D N') (x : VC D N N'), x ∈ La D (tor0 D cc δ) L L' ↔ ∃ z ∈ RL D cc L L', x = pt D (tor0 D cc δ) δ z) ∧ (∀ (L' : Lat D N') (z : Matrix (Fin N') (Fin N) D.host.E), z ∈ RL D cc (stdL D N) L' ↔ ∀ j, (fun i => z i j) ∈ Submodule.span (𝓞 D.host.E) {v | ∃ t ∈ Iid D cc, ∃ y ∈ L', v = t • y}) ∧ ∀ (L : Lat D N), SD D L → ∀ (z : Matrix (Fin N') (Fin N) D.host.E), z ∈ RL D cc L (stdL D N') ↔ ∀ i, z i ∈ Submodule.span (𝓞 D.host.E) {v | ∃ t ∈ Iid D cc, ∃ y ∈ L, v = t • fun j => D.host.conj (y j)} := by
  first | exact @GlobalTheory.ThetaLatImage.theta_lattice_image | exact GlobalTheory.ThetaLatImage.theta_lattice_image | (intros; apply GlobalTheory.ThetaLatImage.theta_lattice_image <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GenusMassSignature
noncomputable section

namespace GlobalTheory.Proof.GenusMassSignature

open NumberField Formalism.BasicNotions Matrix
open scoped ComplexOrder MatrixOrder

theorem denseRange_of_not_isReal {K : Type} [Field K] (σ : K →+* ℂ)
    (h : ¬ ComplexEmbedding.IsReal σ) : DenseRange σ := by
  have hc : IsClosed (σ.fieldRange.topologicalClosure : Set ℂ) :=
    Subfield.isClosed_topologicalClosure _
  rcases Complex.subfield_eq_of_closed hc with h1 | h1
  · exfalso
    apply h
    rw [ComplexEmbedding.isReal_iff]
    ext x
    have hx : σ x ∈ σ.fieldRange.topologicalClosure := Subfield.le_topologicalClosure _ ⟨x, rfl⟩
    rw [h1] at hx
    obtain ⟨r, hr⟩ := hx
    rw [ComplexEmbedding.conjugate_coe_eq, ← hr]
    exact Complex.conj_ofReal r
  · have : closure (Set.range σ) = Set.univ := by
      have := congrArg (fun S : Subfield ℂ => (S : Set ℂ)) h1
      exact this
    exact dense_iff_closure_eq.2 this

theorem hasSignature_of_posDef {n : ℕ} {J : Matrix (Fin n) (Fin n) ℂ} (h : J.PosDef) :
    Formalism.UG.HasSignature J n 0 := by
  let e : Fin n ≃ Fin n ⊕ Fin 0 := (Equiv.sumEmpty (Fin n) (Fin 0)).symm
  have h1 : (J.reindex e e).PosDef := by
    simpa using h.submatrix (e := e.symm) e.symm.injective
  have hJ : Formalism.UG.Jpq n 0 = 1 := by
    ext i j
    rcases i with i | i
    · rcases j with j | j
      · simp [Formalism.UG.Jpq, Matrix.one_apply]
      · exact j.elim0
    · exact i.elim0
  set A := J.reindex e e with hA
  have hS : star (CFC.sqrt A) = CFC.sqrt A := (CFC.sqrt_nonneg A).isSelfAdjoint
  have hSS : CFC.sqrt A * CFC.sqrt A = A := CFC.sqrt_mul_sqrt_self A h1.posSemidef.nonneg
  have hu : IsUnit (CFC.sqrt A) := by
    have := h1.isUnit
    rw [← hSS] at this
    exact isUnit_of_mul_isUnit_left this
  obtain ⟨U, hU⟩ := hu
  refine ⟨e, U⁻¹, ?_⟩
  have hc : Formalism.UG.cT (starRingEnd ℂ) ((U⁻¹ : GL (Fin n ⊕ Fin 0) ℂ) : Matrix _ _ ℂ) =
      star ((U⁻¹ : GL (Fin n ⊕ Fin 0) ℂ) : Matrix (Fin n ⊕ Fin 0) (Fin n ⊕ Fin 0) ℂ) := by
    ext i j; rfl
  have hA2 : A = star (U : Matrix (Fin n ⊕ Fin 0) (Fin n ⊕ Fin 0) ℂ) * U := by
    rw [hU, hS, hSS]
  rw [hJ, hc, ← hA, hA2, ← mul_assoc, ← star_mul, mul_assoc, Units.mul_inv, star_one, one_mul]

section Field

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem emb_form (hst : ∀ (φ : E →+* ℂ) (a : E), φ (star a) = starRingEnd ℂ (φ a))
    (W : HSpace E) (τ : E →+* ℂ) (x : W.V) :
    τ (W.hD x x) = star (fun i => τ (W.frame.repr x i)) ⬝ᵥ
        (W.gram.map τ).mulVec (fun i => τ (W.frame.repr x i)) := by
  unfold HSpace.hD
  conv_lhs => rw [← W.frame.sum_repr x]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
    smul_eq_mul, map_mul, RingHom.id_apply, starRingEnd_apply, hst, dotProduct, Matrix.mulVec,
    Matrix.map_apply, HSpace.gram, Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem gram_isHermitian (hst : ∀ (φ : E →+* ℂ) (a : E), φ (star a) = starRingEnd ℂ (φ a))
    (W : HSpace E) (τ : E →+* ℂ) : (W.gram.map τ).IsHermitian := by
  ext i k
  rw [conjTranspose_apply, Matrix.map_apply, Matrix.map_apply, HSpace.gram, HSpace.gram,
    ← W.herm.eq (W.frame k) (W.frame i), starRingEnd_apply, hst]
  rfl

theorem pos_iff_posDef (htc : IsTotallyComplex E)
    (hst : ∀ (φ : E →+* ℂ) (a : E), φ (star a) = starRingEnd ℂ (φ a))
    (W : HSpace E) (τ : E →+* ℂ) :
    (∀ x : W.V, x ≠ 0 → 0 < (τ (W.hD x x)).re) ↔ (W.gram.map τ).PosDef := by
  constructor
  · intro h
    have hH := gram_isHermitian hst W τ
    have hd : DenseRange τ :=
      denseRange_of_not_isReal τ (IsTotallyComplex.complexEmbedding_not_isReal τ)
    have hdn : DenseRange fun (l : Fin W.rank → E) => (fun i => τ (l i)) :=
      DenseRange.piMap (fun _ : Fin W.rank => hd)
    have hco : ∀ l : Fin W.rank → E, τ (W.hD (W.frame.equivFun.symm l) (W.frame.equivFun.symm l)) =
        star (fun i => τ (l i)) ⬝ᵥ (W.gram.map τ).mulVec (fun i => τ (l i)) := by
      intro l
      rw [emb_form hst]
      have : ∀ i, W.frame.repr (W.frame.equivFun.symm l) i = l i := fun i =>
        congrFun (W.frame.equivFun.apply_symm_apply l) i
      simp only [this]
    have hne : ∀ l : Fin W.rank → E, l ≠ 0 → W.frame.equivFun.symm l ≠ 0 := fun l hl h0 =>
      hl (W.frame.equivFun.symm.injective (by rw [h0, map_zero]))
    have hpsd : (W.gram.map τ).PosSemidef := by
      refine PosSemidef.of_dotProduct_mulVec_nonneg hH fun x => ?_
      rw [Complex.nonneg_iff]
      refine ⟨?_, (hH.im_star_dotProduct_mulVec_self x).symm⟩
      refine hdn.induction_on (p := fun y => 0 ≤ (star y ⬝ᵥ ((W.gram.map τ) *ᵥ y)).re) x ?_ ?_
      · exact isClosed_le continuous_const (by fun_prop)
      · intro l
        by_cases hl : l = 0
        · subst hl
          simp [dotProduct]
        · have := h _ (hne l hl)
          rw [hco] at this
          exact this.le
    rw [hpsd.posDef_iff_isUnit, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    intro h0
    have h1 : W.gram.det = 0 := by
      apply τ.injective
      rw [RingHom.map_det, map_zero]
      exact h0
    obtain ⟨l, hl, hl0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h1
    have h2 : (W.gram.map τ).mulVec (fun i => τ (l i)) = 0 := by
      funext i
      have := congrArg τ (congrFun hl0 i)
      simpa [Matrix.mulVec, dotProduct] using this
    have := h _ (hne l hl)
    rw [hco, h2] at this
    simp at this
  · intro h x hx
    have hv : (fun i => τ (W.frame.repr x i)) ≠ 0 := by
      intro h
      apply hx
      apply W.frame.repr.injective
      ext i
      simpa using congrFun h i
    rw [emb_form hst]
    exact h.re_dotProduct_pos hv

end Field

end GlobalTheory.Proof.GenusMassSignature
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryRationalConjIntersectionCardDvdInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryRationalConjIntersectionCardDvdInvariant
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators nonZeroDivisors

namespace GlobalTheory.StabOrder

section General

variable {E : Type} [Field E] [NumberField E] {N : ℕ}

theorem loc_int : IsLocalization (Algebra.algebraMapSubmonoid (𝓞 E) ℤ⁰) E :=
  IsIntegralClosure.isLocalization ℤ ℚ E (𝓞 E)

theorem exists_int_smul_mem (L : Submodule (𝓞 E) (Fin N → E))
    (hs : Submodule.span E (L : Set (Fin N → E)) = ⊤) (x : Fin N → E) :
    ∃ n : ℤ, n ≠ 0 ∧ n • x ∈ L := by
  haveI := loc_int (E := E)
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span
    (Algebra.algebraMapSubmonoid (𝓞 E) ℤ⁰) E (L : Set (Fin N → E)) x (hs ▸ Submodule.mem_top)
  obtain ⟨t, n, hn, rfl⟩ := t
  refine ⟨n, nonZeroDivisors.ne_zero hn, ?_⟩
  rw [Submodule.span_eq] at ht
  simpa [Submonoid.smul_def, Int.cast_smul_eq_zsmul] using ht

theorem exists_int_denominator (L : Submodule (𝓞 E) (Fin N → E)) (hf : L.FG) :
    ∃ n : ℤ, n ≠ 0 ∧ ∀ x ∈ L, ∀ i, IsIntegral ℤ ((n : E) * x i) := by
  haveI := loc_int (E := E)
  obtain ⟨s, rfl⟩ := hf
  obtain ⟨⟨t, n, hn, rfl⟩, ht⟩ := IsLocalization.exist_integer_multiples_of_finite
    (Algebra.algebraMapSubmonoid (𝓞 E) ℤ⁰) (fun p : s × Fin N => (p.1 : Fin N → E) p.2)
  refine ⟨n, nonZeroDivisors.ne_zero hn, ?_⟩
  intro x hx i
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy⟩ := ht (⟨x, hx⟩, i)
    have : (n : E) * x i = algebraMap (𝓞 E) E y := by
      rw [hy]; simp [Algebra.smul_def]
    rw [this]; exact y.isIntegral_coe
  | zero => simpa using isIntegral_zero
  | add x y _ _ hx hy => simpa [mul_add] using hx.add hy
  | smul a x _ hx =>
    have : (n : E) * (a • x) i = (a : E) * ((n : E) * x i) := by
      simp [Algebra.smul_def]; ring
    rw [this]; exact a.isIntegral_coe.mul hx

theorem norm_entry_le (c : E → E) (hc : ∀ (φ : E →+* ℂ) x, φ (c x) = starRingEnd ℂ (φ x))
    (γ : Matrix (Fin N) (Fin N) E) (h : γ * (γ.map c).transpose = 1) (φ : E →+* ℂ) (i j : Fin N) :
    ‖φ (γ i j)‖ ≤ 1 := by
  have h1 := congrArg φ (congrFun (congrFun h i) i)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, hc,
    Matrix.one_apply_eq, map_one, Complex.mul_conj'] at h1
  have h2 : ∑ k, ‖φ (γ i k)‖ ^ 2 = 1 := by exact_mod_cast h1
  have h3 : ‖φ (γ i j)‖ ^ 2 ≤ 1 := by
    rw [← h2]
    exact Finset.single_le_sum (f := fun k => ‖φ (γ i k)‖ ^ 2) (fun k _ => by positivity) (Finset.mem_univ j)
  nlinarith [norm_nonneg (φ (γ i j))]

theorem finite_stab (c : E → E) (hc : ∀ (φ : E →+* ℂ) x, φ (c x) = starRingEnd ℂ (φ x))
    (L : Submodule (𝓞 E) (Fin N → E)) (hf : L.FG)
    (hs : Submodule.span E (L : Set (Fin N → E)) = ⊤) :
    {γ : Matrix (Fin N) (Fin N) E | γ * (γ.map c).transpose = 1 ∧ ∀ x ∈ L, γ.mulVec x ∈ L}.Finite := by
  obtain ⟨b, hb, hbL⟩ := exists_int_denominator L hf
  choose a ha haL using fun j : Fin N => exists_int_smul_mem L hs (Pi.single j 1)
  have hS : ∀ j, {x : E | IsIntegral ℤ (((b * a j : ℤ) : E) * x) ∧ ∀ φ : E →+* ℂ, ‖φ x‖ ≤ 1}.Finite := by
    intro j
    have hne : ((b * a j : ℤ) : E) ≠ 0 := by exact_mod_cast mul_ne_zero hb (ha j)
    refine Set.Finite.of_finite_image (f := fun x => ((b * a j : ℤ) : E) * x) ?_
      (mul_right_injective₀ hne).injOn
    refine (Embeddings.finite_of_norm_le E ℂ ‖((b * a j : ℤ) : ℂ)‖).subset ?_
    rintro _ ⟨x, ⟨h1, h2⟩, rfl⟩
    refine ⟨h1, fun φ => ?_⟩
    rw [map_mul, map_intCast, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (h2 φ)
  refine (Set.Finite.pi' (fun _ : Fin N => Set.Finite.pi' hS)).subset ?_
  rintro (γ : Matrix (Fin N) (Fin N) E) ⟨h1, h2⟩ i j
  refine ⟨?_, fun φ => norm_entry_le c hc γ h1 φ i j⟩
  have := hbL _ (h2 _ (haL j)) i
  convert this using 1
  have h3 := Matrix.mulVec_smul γ (a j) (Pi.single j (1 : E))
  rw [h3]
  simp [mul_assoc]

theorem exists_faithful (L : Submodule (𝓞 E) (Fin N → E)) (hf : L.FG)
    (hs : Submodule.span E (L : Set (Fin N → E)) = ⊤) {H : Type} [Group H]
    (ρ : H →* Matrix (Fin N) (Fin N) E) (hρ : Function.Injective ρ)
    (hL : ∀ h, ∀ x ∈ L, (ρ h).mulVec x ∈ L) :
    ∃ ψ : H →* GL (Fin (Module.finrank ℚ E * N)) ℤ, Function.Injective ψ := by
  let L' : Submodule ℤ (Fin N → E) := L.restrictScalars ℤ
  have hf' : L'.FG := by
    haveI : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.mpr hf
    haveI : Module.Finite ℤ L := Module.Finite.trans (𝓞 E) L
    exact Module.Finite.iff_fg.mp (inferInstanceAs (Module.Finite ℤ L))
  haveI : Submodule.IsLattice ℚ L' := Submodule.IsLattice.of_fg ℚ hf'
  haveI hlat : Submodule.IsFullLattice ℚ L' := by
    refine ⟨?_⟩
    rw [eq_top_iff]
    intro x _
    obtain ⟨n, hn, hx⟩ := exists_int_smul_mem L hs x
    have : x = (n : ℚ)⁻¹ • (n • x) := by
      rw [← Int.cast_smul_eq_zsmul ℚ, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hn), one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hx)
  haveI : Module.Finite ℤ L' := Module.Finite.iff_fg.mpr hf'
  have hr : Module.finrank ℤ L' = Module.finrank ℚ E * N := by
    have h1 : Module.finrank ℤ L' = Module.finrank ℚ (Fin N → E) := by
      unfold Module.finrank
      rw [Submodule.IsLattice.rank' ℚ L']
    rw [h1, Module.finrank_pi_fintype]
    simp [mul_comm]
  let b := Module.finBasisOfFinrankEq ℤ L' hr
  let θ : H →* Module.End ℤ L' :=
    { toFun := fun h => ((Matrix.toLin' (ρ h)).restrictScalars ℤ).restrict (p := L') (q := L')
        (fun x hx => hL h x hx)
      map_one' := by ext x i; simp
      map_mul' := by
        intro g h
        ext x i
        show Matrix.toLin' (ρ (g * h)) x i = Matrix.toLin' (ρ g) (Matrix.toLin' (ρ h) x) i
        simp }
  have hθ : Function.Injective θ := by
    intro g h hgh
    apply hρ
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro x
    obtain ⟨n, hn, hx⟩ := exists_int_smul_mem L hs x
    have h1 : Matrix.toLin' (ρ g) (n • x) = Matrix.toLin' (ρ h) (n • x) :=
      congrArg Subtype.val (LinearMap.congr_fun hgh ⟨n • x, hx⟩)
    rw [map_zsmul, map_zsmul] at h1
    exact smul_right_injective _ hn h1
  refine ⟨(((LinearMap.toMatrixAlgEquiv b).toMonoidHom).comp θ).toHomUnits, ?_⟩
  intro g h hgh
  apply hθ
  apply (LinearMap.toMatrixAlgEquiv b).injective
  exact congrArg Units.val hgh

end General

theorem finrank_host (D : D7) : Module.finrank ℚ D.host.E = 2 * fF D := by
  have h := D.host.finrank_cmField
  rw [show Module.finrank ℚ D.host.E = _ from h]
  simp only [fF, Ranks.f, Ranks.n]
  ring

theorem gam_ne_zero_dvd_invariant : ∀ (D : D7) (N : ℕ) (J : Subgroup (GA D N)), J ≤ intG D N → ∀ g, gam D J g ≠ 0 ∧ gam D J g ∣ 8 ^ (2 * fF D * N) * (2 * (2 * fF D * N)).factorial ∧ ∀ γ ∈ ratG D N, ∀ j ∈ J, gam D J (γ * g * j) = gam D J g := by
  intro D N J hJ g
  obtain ⟨hrat, -, -, huni, hinc⟩ := GlobalTheory.NormSum.mem_ratG_intG D N
  obtain ⟨Lt, hSD, -, hEq, hmv, -⟩ := GlobalTheory.T.Lt_eq_iff_inv_mul_mem_intG_and_transport D N
  let H : Subgroup (GA D N) := ratG D N ⊓ J.comap (MulAut.conj g⁻¹).toMonoidHom
  have hH : ∀ x, x ∈ H ↔ x ∈ ratG D N ∧ g⁻¹ * x * g ∈ J := by
    intro x; simp [H]
  have hcard : gam D J g = Nat.card H :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => (hH x).symm)
  choose r hr using fun h : H => (hrat h).1 ((hH h).1 h.2).1
  have hmap : Function.Injective (fun M : Matrix (Fin N) (Fin N) D.host.E => M.map (inc D)) :=
    Matrix.map_injective hinc
  let ρ : H →* Matrix (Fin N) (Fin N) D.host.E :=
    { toFun := r
      map_one' := by
        apply hmap
        have := hr 1
        unfold IsRat at this
        simp only [← this]
        simp
      map_mul' := by
        intro x y
        apply hmap
        have h1 := hr x
        have h2 := hr y
        have h3 := hr (x * y)
        unfold IsRat at h1 h2 h3
        simp only [Matrix.map_mul, ← h1, ← h2, ← h3]
        simp }
  have hρ : Function.Injective ρ := by
    intro x y hxy
    have h1 := hr x
    have h2 := hr y
    unfold IsRat at h1 h2
    have h3 : r x = r y := hxy
    rw [h3, ← h2] at h1
    exact Subtype.ext (Subtype.ext (Units.ext h1))
  have hL : ∀ h : H, ∀ x ∈ Lt g, (ρ h).mulVec x ∈ Lt g := by
    intro h x hx
    have h1 : Lt g = Lt (h * g) := (hEq _ _).2 (by
      rw [← mul_assoc]; exact hJ ((hH h).1 h.2).2)
    have := (hmv h g (r h) (hr h) x).1 hx
    rwa [← h1] at this
  obtain ⟨hfg, hspan, -⟩ := (hSD g).2
  have hfin : Finite H := by
    have := (finite_stab D.host.conj
      (fun φ x => D.host.conjE_apply φ x) (Lt g) hfg hspan).to_subtype
    exact Finite.of_injective (β := {γ : Matrix (Fin N) (Fin N) D.host.E |
        γ * (γ.map D.host.conj).transpose = 1 ∧ ∀ x ∈ Lt g, γ.mulVec x ∈ Lt g})
      (fun h => ⟨ρ h, huni h _ (hr h), hL h⟩) (fun x y hxy => hρ (congrArg Subtype.val hxy))
  refine ⟨?_, ?_, ?_⟩
  · rw [hcard]; exact Nat.card_pos.ne'
  · obtain ⟨ψ, hψ⟩ := exists_faithful (Lt g) hfg hspan ρ hρ hL
    have e := (MonoidHom.ofInjective hψ).toEquiv
    have := GlobalTheory.card_finite_subgroup_GL_int_dvd _ ψ.range (Finite.of_equiv _ e)
    rw [← Nat.card_congr e, finrank_host] at this
    rw [hcard]; exact this
  · intro γ hγ j hj
    unfold gam
    refine Nat.card_congr ((MulAut.conj γ⁻¹).toEquiv.subtypeEquiv fun x => ?_)
    have e1 : (MulAut.conj γ⁻¹).toEquiv x = γ⁻¹ * x * γ := by simp
    rw [e1]
    have e2 : (γ * g * j)⁻¹ * x * (γ * g * j) = j⁻¹ * (g⁻¹ * (γ⁻¹ * x * γ) * g) * j := by group
    rw [e2, Subgroup.mul_mem_cancel_right _ hj, Subgroup.mul_mem_cancel_left _ (J.inv_mem hj),
      Subgroup.mul_mem_cancel_right _ hγ, Subgroup.mul_mem_cancel_left _ ((ratG D N).inv_mem hγ)]

end GlobalTheory.StabOrder
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryRationalConjIntersectionCardDvdInvariantStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryRationalConjIntersectionCard_dvd_invariant : ∀ (D : D7) (N : ℕ) (J : Subgroup (GA D N)), J ≤ intG D N → ∀ g, gam D J g ≠ 0 ∧ gam D J g ∣ 8 ^ (2 * fF D * N) * (2 * (2 * fF D * N)).factorial ∧ ∀ γ ∈ ratG D N, ∀ j ∈ J, gam D J (γ * g * j) = gam D J g := by
  first | exact @GlobalTheory.StabOrder.gam_ne_zero_dvd_invariant | exact GlobalTheory.StabOrder.gam_ne_zero_dvd_invariant | (intros; apply GlobalTheory.StabOrder.gam_ne_zero_dvd_invariant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdxEqRelIndex
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.InertParity

variable {D : D7}

def Ev (D : D7) (n : ℕ) : Prop := ∀ q : ℕ, q.Prime → InertQ D q → Even (n.factorization q)

def hlf (D : D7) (n : ℕ) : ℕ := ∑ q ∈ n.primeFactors.filter (InertQ D), n.factorization q / 2

def sgn (D : D7) (n : ℕ) : ℂ := (-1) ^ hlf D n

def idx (D : D7) {n : ℕ} (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : ℕ :=
  Nat.card (stdL D n ⧸ Submodule.comap (stdL D n).subtype L)

def scal (D : D7) (N N' : ℕ) (b : D.host.E) : VC D N N' →ₗ[ℂ] VC D N N' :=
  GlobalTheory.RatEqui.mulV D (b • (1 : Matrix (Fin N') (Fin N') D.host.E)) 1

theorem scal_apply {N N' : ℕ} (b : D.host.E) (z : VC D N N') (τ i j) :
    scal D N N' b z τ i j = embT D τ b * z τ i j := by
  have e : (b • (1 : Matrix (Fin N') (Fin N') D.host.E)).map (embT D τ) =
      embT D τ b • (1 : Matrix (Fin N') (Fin N') ℂ) := by
    ext i j
    by_cases h : i = j <;> simp [h]
  rw [scal, GlobalTheory.RatEqui.mulV_apply, e, Matrix.map_one _ (map_zero _) (map_one _)]
  simp

theorem idx_eq_relIndex {n : ℕ} (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) :
    idx D L = L.toAddSubgroup.relIndex (stdL D n).toAddSubgroup := rfl

theorem idx_std (n : ℕ) : idx D (stdL D n) = 1 := by
  rw [idx_eq_relIndex, AddSubgroup.relIndex_self]

theorem hlf_eq_sum {n : ℕ} {s : Finset ℕ} (hs : n.primeFactors ⊆ s) :
    hlf D n = ∑ q ∈ s.filter (InertQ D), n.factorization q / 2 := by
  refine Finset.sum_subset (Finset.filter_subset_filter _ hs) fun q hq hq' => ?_
  have : q ∉ n.factorization.support := fun h =>
    hq' (Finset.mem_filter.2 ⟨by simpa using h, (Finset.mem_filter.1 hq).2⟩)
  rw [Finsupp.notMem_support_iff.1 this, Nat.zero_div]

theorem Ev.one : Ev D 1 := fun q _ _ => by simp

theorem sgn_one : sgn D 1 = 1 := by simp [sgn, hlf]

theorem sgn_mul_self (n : ℕ) : sgn D n * sgn D n = 1 := by
  rw [sgn, ← mul_pow]; simp

theorem sgn_pow_even (n : ℕ) {k : ℕ} (hk : Even k) : sgn D n ^ k = 1 := by
  obtain ⟨j, rfl⟩ := hk
  rw [pow_add, ← mul_pow, sgn_mul_self, one_pow]

theorem Ev.mul {a b : ℕ} (ha : Ev D a) (hb : Ev D b) (ha0 : a ≠ 0) (hb0 : b ≠ 0) : Ev D (a * b) := fun q hq hi => by
  rw [Nat.factorization_mul ha0 hb0]
  exact (ha q hq hi).add (hb q hq hi)

theorem Ev.of_mul {a b : ℕ} (hab : Ev D (a * b)) (hb : Ev D b) (ha0 : a ≠ 0) (hb0 : b ≠ 0) : Ev D a :=
  fun q hq hi => by
    have := hab q hq hi
    rw [Nat.factorization_mul ha0 hb0, Finsupp.add_apply, Nat.even_add] at this
    exact this.2 (hb q hq hi)

theorem Ev.pow {a : ℕ} (ha : Ev D a) (k : ℕ) : Ev D (a ^ k) := fun q hq hi => by
  rw [Nat.factorization_pow]
  exact (ha q hq hi).mul_left k

theorem sgn_mul {a b : ℕ} (ha : Ev D a) (hb : Ev D b) (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
    sgn D (a * b) = sgn D a * sgn D b := by
  have h : (a * b).primeFactors = a.primeFactors ∪ b.primeFactors := Nat.primeFactors_mul ha0 hb0
  rw [sgn, sgn, sgn, ← pow_add, hlf_eq_sum (n := a) (s := (a * b).primeFactors) (h ▸ Finset.subset_union_left),
    hlf_eq_sum (n := b) (s := (a * b).primeFactors) (h ▸ Finset.subset_union_right), hlf, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun q hq => ?_
  obtain ⟨hq1, hi⟩ := Finset.mem_filter.1 hq
  have hp := Nat.prime_of_mem_primeFactors hq1
  obtain ⟨i, hi'⟩ := ha q hp hi
  obtain ⟨j, hj⟩ := hb q hp hi
  rw [Nat.factorization_mul ha0 hb0, Finsupp.add_apply]
  omega

theorem sgn_pow {a : ℕ} (ha : Ev D a) (ha0 : a ≠ 0) (k : ℕ) : sgn D (a ^ k) = sgn D a ^ k := by
  induction k with
  | zero => simp [sgn_one]
  | succ k ih => rw [pow_succ, sgn_mul (ha.pow k) ha (pow_ne_zero _ ha0) ha0, ih, pow_succ]

theorem sgn_congr {a b : ℕ} (h : ∀ q : ℕ, q.Prime → InertQ D q → a.factorization q = b.factorization q) :
    sgn D a = sgn D b := by
  rw [sgn, sgn, hlf_eq_sum (n := a) (s := a.primeFactors ∪ b.primeFactors) Finset.subset_union_left,
    hlf_eq_sum (n := b) (s := a.primeFactors ∪ b.primeFactors) Finset.subset_union_right]
  congr 1
  refine Finset.sum_congr rfl fun q hq => ?_
  obtain ⟨hq1, hi⟩ := Finset.mem_filter.1 hq
  have hp : q.Prime := by
    rcases Finset.mem_union.1 hq1 with h | h <;> exact Nat.prime_of_mem_primeFactors h
  rw [h q hp hi]

theorem sgn_of_eq {n a b c k : ℕ} (h : n * a ^ k = b ^ k * c ^ k) (ha : Ev D a) (hb : Ev D b) (hc : Ev D c)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hc0 : c ≠ 0) : sgn D n = sgn D b ^ k * (sgn D c * sgn D a) ^ k := by
  have h0 : b ^ k * c ^ k ≠ 0 := mul_ne_zero (pow_ne_zero _ hb0) (pow_ne_zero _ hc0)
  have hn0 : n ≠ 0 := left_ne_zero_of_mul (h ▸ h0)
  have hn : Ev D n := Ev.of_mul (h ▸ (hb.pow k).mul (hc.pow k) (pow_ne_zero _ hb0) (pow_ne_zero _ hc0)) (ha.pow k) hn0
    (pow_ne_zero _ ha0)
  have e := congrArg (sgn D) h
  rw [sgn_mul hn (ha.pow k) hn0 (pow_ne_zero _ ha0),
    sgn_mul (hb.pow k) (hc.pow k) (pow_ne_zero _ hb0) (pow_ne_zero _ hc0), sgn_pow ha ha0, sgn_pow hb hb0,
    sgn_pow hc hc0] at e
  rw [mul_pow, ← mul_assoc, ← e, mul_assoc, ← mul_pow, sgn_mul_self, one_pow, mul_one]

end GlobalTheory.InertParity
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGoodIndexNormalizationNegativeInert
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGoodIndexNormalizationNegativeInert
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators Pointwise

namespace GlobalTheory.FinWeil

noncomputable def ofPrimeValues (u : ℕ → ℂ) : ℕ →* ℂ where
  toFun n := if n = 0 then 0 else n.factorization.prod fun q k => u q ^ k
  map_one' := by simp
  map_mul' a b := by
    by_cases ha : a = 0
    · simp [ha]
    by_cases hb : b = 0
    · simp [hb]
    rw [if_neg (mul_ne_zero ha hb), if_neg ha, if_neg hb, Nat.factorization_mul ha hb,
      Finsupp.prod_add_index' (by simp) (fun q k l => pow_add _ _ _)]

theorem ofPrimeValues_prime (u : ℕ → ℂ) {q : ℕ} (hq : q.Prime) : ofPrimeValues u q = u q := by
  show (if q = 0 then 0 else q.factorization.prod fun q k => u q ^ k) = u q
  rw [if_neg hq.ne_zero, hq.factorization, Finsupp.prod_single_index (by simp), pow_one]

theorem sqrt_pow_nat (q f : ℕ) : ((Real.sqrt q : ℝ) : ℂ) ^ f = (Real.sqrt ((q ^ f : ℕ) : ℝ) : ℂ) := by
  induction f with
  | zero => simp
  | succ f ih =>
    rw [pow_succ, ih, pow_succ, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), Complex.ofReal_mul]

theorem exists_lam (S : ℕ → Prop) (f : ℕ → ℕ) :
    ∃ lam : ℕ →* ℂ, (∀ n, n ≠ 0 → lam n ≠ 0) ∧
      (∀ q, q.Prime → f q ≠ 0 → S q → lam (q ^ f q) = -(Real.sqrt ((q ^ f q : ℕ) : ℝ) : ℂ)) ∧
      ∀ n : ℕ, n ≠ 0 → (∀ q : ℕ, q.Prime → S q → ¬ q ∣ n) → lam n = (Real.sqrt n : ℂ) := by
  let u : ℕ → ℂ := fun q =>
    (Real.sqrt q : ℂ) * if S q then Complex.exp (Real.pi * Complex.I / f q) else 1
  refine ⟨ofPrimeValues u, fun n => ?_, fun q hq hf hS => ?_, fun n => ?_⟩
  · induction n using Nat.recOnMul with
    | zero => simp
    | one => simp
    | prime q hq =>
      intro _
      rw [ofPrimeValues_prime u hq]
      refine mul_ne_zero ?_ ?_
      · exact_mod_cast (Real.sqrt_pos.2 (by exact_mod_cast hq.pos)).ne'
      · split_ifs
        · exact Complex.exp_ne_zero _
        · exact one_ne_zero
    | mul a b ha hb =>
      intro h
      rw [map_mul]
      exact mul_ne_zero (ha (left_ne_zero_of_mul h)) (hb (right_ne_zero_of_mul h))
  · rw [map_pow, ofPrimeValues_prime u hq]
    simp only [u, if_pos hS]
    have hf' : (f q : ℂ) ≠ 0 := by exact_mod_cast hf
    rw [mul_pow, sqrt_pow_nat, ← Complex.exp_nat_mul, mul_div_cancel₀ _ hf', Complex.exp_pi_mul_I]
    ring
  · induction n using Nat.recOnMul with
    | zero => simp
    | one => simp
    | prime q hq =>
      intro _ h
      have hS : ¬ S q := fun hS => h q hq hS dvd_rfl
      rw [ofPrimeValues_prime u hq]
      simp only [u, if_neg hS, mul_one]
    | mul a b ha hb =>
      intro h h'
      rw [map_mul, ha (left_ne_zero_of_mul h) fun q hq hS hd => h' q hq hS (hd.mul_right _),
        hb (right_ne_zero_of_mul h) fun q hq hS hd => h' q hq hS (hd.mul_left _), Nat.cast_mul,
        Real.sqrt_mul (Nat.cast_nonneg _), Complex.ofReal_mul]

theorem exists_card_eq_pow {E : Type} [Field E] [NumberField E] [IsGalois ℚ E] (P : Ideal (𝓞 E))
    (hP : P.IsMaximal) : ∃ q : ℕ, q.Prime ∧ (q : 𝓞 E) ∈ P ∧
      (Ideal.span {(q : ℤ)}).inertiaDegIn (𝓞 E) ≠ 0 ∧
      Nat.card (𝓞 E ⧸ P) = q ^ (Ideal.span {(q : ℤ)}).inertiaDegIn (𝓞 E) := by
  have hP0 : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _)
  obtain ⟨p, hp, hPp⟩ :=
    (Ideal.isPrime_int_iff.mp (Ideal.IsPrime.under ℤ P)).resolve_left (Ideal.under_ne_bot ℤ hP0)
  have hlo : P.LiesOver (Ideal.span {(p : ℤ)}) := ⟨hPp.symm⟩
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hp).irreducible
  have h1 := Ideal.inertiaDegIn_eq_inertiaDeg (Ideal.span {(p : ℤ)}) P (E ≃ₐ[ℚ] E)
  refine ⟨p, hp, ?_, ?_, ?_⟩
  · have : (p : ℤ) ∈ P.under ℤ := hPp ▸ Ideal.mem_span_singleton_self _
    simpa [Ideal.under, Ideal.mem_comap] using this
  · rw [h1]; exact (Ideal.inertiaDeg_pos P ℤ).ne'
  · rw [h1, Ideal.pow_inertiaDeg p P, Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem exists_goodNorm : ∀ D : D7, ∃ lam : ℕ →* ℂ, GoodNorm (sgO D) lam ∧ ∀ n : ℕ, n ≠ 0 → (∀ q : ℕ, q.Prime → InertQ D q → ¬ q ∣ n) → lam n = (Real.sqrt n : ℂ) := by
  intro D
  have : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  have hcomm : ∀ σ τ : D.host.E ≃ₐ[ℚ] D.host.E, σ * τ = τ * σ := fun σ τ =>
    D.host.galE_injective (by
      rw [D.host.galE_mul,
        D.host.galE_mul, mul_comm])
  obtain ⟨lam, h0, h1, h2⟩ := exists_lam (InertQ D)
    fun q => (Ideal.span {(q : ℤ)}).inertiaDegIn (𝓞 D.host.E)
  refine ⟨lam, ⟨h0, fun P hP _ => ?_⟩, h2⟩
  have hP0 : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _)
  obtain ⟨q, hq, hqP, hf, hc⟩ := exists_card_eq_pow P hP
  have hsq : ∀ n : ℕ, ((Real.sqrt n : ℝ) : ℂ) ^ 2 = n := fun n => by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]
  refine ⟨?_, fun h => ⟨?_, ?_⟩⟩
  · rw [hc]
    by_cases hI : InertQ D q
    · rw [h1 q hq hf hI, neg_sq, hsq]
    · rw [h2 _ (pow_ne_zero _ hq.ne_zero) fun p hp hIp hd => hI
        ((Nat.prime_dvd_prime_iff_eq hp hq).1 (hp.dvd_of_dvd_pow hd) ▸ hIp), hsq]
  · have hfix : D.host.conj • P = P := by
      have hP' : (D.host.conj • P).IsMaximal := by
        rcases Ideal.map_eq_top_or_isMaximal_of_surjective (sgO D)
          (MulAction.surjective D.host.conj) hP with h | h
        · exact absurd h (Ideal.IsPrime.smul (H := hP.isPrime) D.host.conj).ne_top
        · exact h
      exact hP'.eq_of_le hP.ne_top (Ideal.map_le_iff_le_comap.2 fun r hr => h r hr)
    have hI : InertQ D q := fun Q hQ _ hqQ =>
      GlobalTheory.SelectIdem.smul_eq_of_abelian hcomm _ hq P Q hP.isPrime hQ hqP hqQ hfix
    rw [hc]
    exact h1 q hq hf hI
  · have := D.host.der.unramEF P hP.isPrime hP0
    push Not at this
    exact this

end GlobalTheory.FinWeil
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGoodIndexNormalizationNegativeInertStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_goodIndexNormalization_negative_inert : ∀ D : D7, ∃ lam : ℕ →* ℂ, GoodNorm (sgO D) lam ∧ ∀ n : ℕ, n ≠ 0 → (∀ q : ℕ, q.Prime → InertQ D q → ¬ q ∣ n) → lam n = (Real.sqrt n : ℂ) := by
  first | exact @GlobalTheory.FinWeil.exists_goodNorm | exact GlobalTheory.FinWeil.exists_goodNorm | (intros; apply GlobalTheory.FinWeil.exists_goodNorm <;> assumption)
end
end
