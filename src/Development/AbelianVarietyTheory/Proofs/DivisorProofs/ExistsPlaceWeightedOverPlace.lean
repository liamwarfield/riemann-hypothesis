module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightedMonomialValuationOfParameters
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularLocalModelGraphOfPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalRingGraphGenericPointOfInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackIsoBaseChangeOverReducedClosedFibre

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPlaceWeightedOverPlace
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

namespace GlobalTheory.FieldPair

theorem isTranscendenceBasis_one_tmul {k K F W ι : Type} [Field k] [Field K] [Field F] [Field W]
    [Algebra k K] [Algebra k F] [Algebra K W] [Algebra (K ⊗[k] F) W]
    [IsScalarTower K (K ⊗[k] F) W] [IsFractionRing (K ⊗[k] F) W] {x : ι → F}
    (hx : IsTranscendenceBasis k x) :
    IsTranscendenceBasis K fun i => algebraMap (K ⊗[k] F) W (1 ⊗ₜ x i) := by
  let ψ : K ⊗[k] F →ₐ[K] W := IsScalarTower.toAlgHom K (K ⊗[k] F) W
  have hψ : Function.Injective ψ := IsFractionRing.injective (K ⊗[k] F) W
  have hy : AlgebraicIndependent K fun i => ψ (1 ⊗ₜ x i) := by
    rw [algebraicIndependent_iff_injective_aeval]
    have h1 : Function.Injective
        (Algebra.TensorProduct.map (AlgHom.id K K) (MvPolynomial.aeval (R := k) x)) :=
      Module.Flat.lTensor_preserves_injective_linearMap (M := K)
        (MvPolynomial.aeval (R := k) x).toLinearMap
        (algebraicIndependent_iff_injective_aeval.1 hx.1)
    have e : (MvPolynomial.aeval (R := K) fun i => ψ (1 ⊗ₜ x i)) =
        (ψ.comp (Algebra.TensorProduct.map (AlgHom.id K K) (MvPolynomial.aeval (R := k) x))).comp
          (MvPolynomial.algebraTensorAlgEquiv (σ := ι) k K).symm.toAlgHom := by
      ext i
      simp
    rw [e]
    exact (hψ.comp h1).comp (MvPolynomial.algebraTensorAlgEquiv (σ := ι) k K).symm.injective
  change IsTranscendenceBasis K fun i => ψ (1 ⊗ₜ x i)
  rw [hy.isTranscendenceBasis_iff_isAlgebraic, ← IntermediateField.isAlgebraic_adjoin_iff_top]
  let E := IntermediateField.adjoin K (Set.range fun i => ψ (1 ⊗ₜ x i))
  let φ : F →+* W := (ψ : K ⊗[k] F →+* W).comp
    (Algebra.TensorProduct.includeRight (R := k) (A := K) (B := F)).toRingHom
  have hm : ∀ a ∈ Algebra.adjoin k (Set.range x), φ a ∈ E := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem a ha =>
      obtain ⟨i, rfl⟩ := ha
      exact IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩
    | algebraMap r =>
      have : φ (algebraMap k F r) = algebraMap K W (algebraMap k K r) := by
        rw [← ψ.commutes]
        change ψ (1 ⊗ₜ algebraMap k F r) = ψ (algebraMap k K r ⊗ₜ 1)
        rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
          TensorProduct.smul_tmul]
      rw [this]
      exact E.algebraMap_mem _
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
  let g : Algebra.adjoin k (Set.range x) →+* E :=
    (φ.comp (Algebra.adjoin k (Set.range x)).val.toRingHom).codRestrict E fun a => hm a a.2
  have hg : Function.Injective g := fun a b h =>
    Subtype.ext (φ.injective (congrArg Subtype.val h))
  have hT : ∀ a, ψ a ∈ algebraicClosure E W := by
    intro a
    induction a using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact zero_mem _
    | add a b ha hb => rw [map_add]; exact add_mem ha hb
    | tmul l f =>
      have : l ⊗ₜ[k] f = algebraMap K _ l * ((1 : K) ⊗ₜ[k] f) := by simp
      rw [this, map_mul, ψ.commutes]
      refine mul_mem ((algebraicClosure E W).algebraMap_mem (algebraMap K E l)) ?_
      rw [mem_algebraicClosure_iff]
      exact (hx.isAlgebraic.isAlgebraic f).ringHom_of_comp_eq g φ hg rfl
  refine ⟨fun z => ?_⟩
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := K ⊗[k] F) z
  exact mem_algebraicClosure_iff.1 (div_mem (hT a) (hT b))

theorem trBasis_append_tmul {k K F W : Type} [Field k] [Field K] [Field F] [Field W]
    [Algebra k K] [Algebra k F] [Algebra k W] [Algebra (K ⊗[k] F) W]
    [IsScalarTower k (K ⊗[k] F) W] [IsFractionRing (K ⊗[k] F) W] {n m : ℕ} {x : Fin n → K}
    {y : Fin m → F} (hx : TrBasis (algebraMap k K) x) (hy : TrBasis (algebraMap k F) y) :
    TrBasis (algebraMap k W) (Fin.append (fun i => algebraMap (K ⊗[k] F) W (1 ⊗ₜ y i))
      (fun i => algebraMap (K ⊗[k] F) W (x i ⊗ₜ 1))) := by
  have key : ∀ {A : Type} [Field A] [inst : Algebra k A] {l : ℕ} (u : Fin l → A),
      TrBasis (algebraMap k A) u ↔ IsTranscendenceBasis k u := by
    intro A _ inst l u
    have e : (algebraMap k A).toAlgebra = inst := Algebra.algebra_ext _ _ fun _ => rfl
    unfold TrBasis
    rw [e]
  rw [key] at hx hy ⊢
  letI : Algebra K W := ((algebraMap (K ⊗[k] F) W).comp (algebraMap K (K ⊗[k] F))).toAlgebra
  haveI : IsScalarTower K (K ⊗[k] F) W := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower k K W := IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply k (K ⊗[k] F) W,
      IsScalarTower.algebraMap_apply k K (K ⊗[k] F), ← IsScalarTower.algebraMap_apply]
  have h := hx.sumElim_comp (isTranscendenceBasis_one_tmul (K := K) (W := W) hy)
  rw [← isTranscendenceBasis_equiv finSumFinEquiv]
  convert h using 1
  funext i
  rcases i with i | i
  · simp
  · simp
    rfl

theorem Place.le_ord_iff_div_mem {k K : Type} [Field k] [Field K] {c : k →+* K} (V : Place c)
    {f t : K} (hf : f ≠ 0) (ht : t ≠ 0) : V.ord t ≤ V.ord f ↔ f / t ∈ V.ring := by
  rw [← V.ord_nonneg_iff (div_ne_zero hf ht), div_eq_mul_inv, V.ord_mul hf (inv_ne_zero ht),
    V.ord_inv]
  omega

theorem exists_place_weighted_over_place : ∀ {K κ κ' L : Type} [Field K] [Field κ] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ] [Algebra ℂ κ'] [Algebra ℂ L]
    [Algebra (K ⊗[ℂ] κ') L] [IsScalarTower ℂ (K ⊗[ℂ] κ') L] [IsFractionRing (K ⊗[ℂ] κ') L]
    (n k k' : ℕ) (x : Fin n → K) (τ' : Fin k' → κ') (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ'),
  TrBasis (algebraMap ℂ K) x → TrBasis (algebraMap ℂ κ') τ' → (∃ O' : Subring κ', IsLocModel (algebraMap ℂ κ') O') → (∃ z : Fin k → κ, TrBasis (algebraMap ℂ κ) z) →
  (∀ a (h : algebraMap ℂ K a ∈ R), π ⟨algebraMap ℂ K a, h⟩ = algebraMap ℂ κ a) →
  (∀ a, algebraMap ℂ K a ∈ R) →
  (∀ f : κ, ∃ a b : R, π b ≠ 0 ∧ f * π b = π a) →
  ∀ (E : Place (algebraMap ℂ K)), E.Contains R → (∀ r : R, (r : K) ≠ 0 → (π r = 0 ↔ 0 < E.ord r)) →
  ∀ M : ℕ, 1 ≤ k → 1 ≤ M → ∃ V : Place (algebraMap ℂ L),
    (∀ r : R, algebraMap (K ⊗[ℂ] κ') L ((r : K) ⊗ₜ 1) ∈ V.ring) ∧
    (∀ b : κ', b ≠ 0 → V.ord (algebraMap (K ⊗[ℂ] κ') L (1 ⊗ₜ b)) = 0) ∧
    (∀ g : K, g ≠ 0 → V.ord (algebraMap (K ⊗[ℂ] κ') L (g ⊗ₜ 1)) = M * E.ord g) ∧
    (∀ (l : ℕ) (a : Fin l → R) (b : Fin l → κ'), ∑ i, ρ (π (a i)) * b i ≠ 0 →
      (fun (l : ℕ) (a : Fin l → R) (b : Fin l → κ') => ∑ i, algebraMap (K ⊗[ℂ] κ') L ((a i : K) ⊗ₜ b i)) l a b ≠ 0 ∧ V.ord ((fun (l : ℕ) (a : Fin l → R) (b : Fin l → κ') => ∑ i, algebraMap (K ⊗[ℂ] κ') L ((a i : K) ⊗ₜ b i)) l a b) = 0) ∧
    (∀ (l : ℕ) (a : Fin l → R) (b : Fin l → κ'), (fun (l : ℕ) (a : Fin l → R) (b : Fin l → κ') => ∑ i, algebraMap (K ⊗[ℂ] κ') L ((a i : K) ⊗ₜ b i)) l a b ≠ 0 →
      ∑ i, π (a i) ⊗ₜ[ℂ] b i ∈ (RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ'))) ^ M → (M : ℤ) ≤ V.ord ((fun (l : ℕ) (a : Fin l → R) (b : Fin l → κ') => ∑ i, algebraMap (K ⊗[ℂ] κ') L ((a i : K) ⊗ₜ b i)) l a b)) ∧
    (fun ω => @dite ℤ (∃ a, V.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (dForm (algebraMap ℂ L) (Fin.append (fun i => algebraMap (K ⊗[ℂ] κ') L (1 ⊗ₜ τ' i))
      (fun i => algebraMap (K ⊗[ℂ] κ') L (x i ⊗ₜ 1)))) + 1 ≤ M * ((fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (dForm (algebraMap ℂ K) x) + 1) + k := by
  intro K κ κ' L _ _ _ _ _ _ _ _ _ _ _ n k k' x τ' R π ρ hx hτ hO hz hc hR hπ E hER hE M hk hM
  obtain ⟨Q, hQ, z, hm, hdim, hEQ, hg, hb, hu, hJ, y, q, hy, hq, hform⟩ :=
    GlobalTheory.T.exists_regular_localModel_graph_of_place (L := L) n k k' x τ' R π ρ hx hτ hO hz hc hR hπ E hER hE
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hw := trBasis_append_tmul (W := L) hx hτ
  let σ : Equiv.Perm (Fin (k + 1 + 1)) := Equiv.swap 0 1
  let wt : Fin (k + 1 + 1) → ℕ := fun i => if i = 1 then M else 1
  obtain ⟨V, hVQ, hV0, hVz, hVd, hVf⟩ := GlobalTheory.T.exists_weighted_monomial_valuation_of_parameters (algebraMap ℂ L) Q hQ (k + 1) (k' + n)
    (z ∘ σ) wt (by rw [σ.surjective.range_comp]; exact hm) hdim (by simp [wt])
    (fun i => by simp only [wt]; split_ifs <;> omega) ⟨_, hw⟩
  have hz0 : V.ord (z 0) = M := by simpa [σ, wt] using hVz 1
  have hz0' : (z 0 : L) ≠ 0 := by
    intro h
    rw [h, Place.ord, map_zero, WithZero.log_zero] at hz0
    omega
  have hne : ∀ p : Q, IsUnit p → (p : L) ≠ 0 := fun p hp => (hp.map Q.subtype).ne_zero
  have hmul : ∀ (p : Q) (a : ℤ), IsUnit p → V.ord ((p : L) * (z 0 : L) ^ a) = M * a := by
    intro p a hp
    rw [V.ord_mul (hne p hp) (zpow_ne_zero _ hz0'), hV0 p hp, V.ord_zpow, hz0]
    ring
  refine ⟨V, fun r => hVQ _ (hEQ _ (hER _ r.2)), fun b hb0 => ?_, fun g hg0 => ?_,
    fun l a b h => ?_, fun l a b h0 h => ?_, ?_⟩
  · obtain ⟨p, hp, e⟩ := hb b hb0
    rw [← e, hV0 p hp]
  · obtain ⟨p, hp, e⟩ := hg g hg0
    rw [e, hmul p _ hp]
  · obtain ⟨p, hp, e⟩ := hu l a b h
    rw [← e]
    exact ⟨hne p hp, hV0 p hp⟩
  · obtain ⟨p, e, hp⟩ := hJ M l a b h
    rw [← e] at h0 ⊢
    obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.1 hp
    obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.1 ht
    rw [← hz0, V.le_ord_iff_div_mem h0 hz0']
    push_cast
    rw [add_div, mul_div_cancel_right₀ _ hz0']
    refine add_mem ?_ (hVQ _ u.2)
    by_cases hs0 : (s : L) = 0
    · rw [hs0, zero_div]
      exact zero_mem _
    · rw [← V.le_ord_iff_div_mem hs0 hz0', hz0]
      exact hVd M s hs0 hs
  · have hd : dForm (algebraMap ℂ L) (fun i => (y i : L)) ≠ 0 := by
      intro h
      have h1 := (isFreeGen_dForm_of_trBasis _ hw).1 (a₁ := 1) (a₂ := 0)
        (by simp only [hform, h, smul_zero])
      exact one_ne_zero h1
    have hs : ∑ i, (wt i : ℤ) = M + (k + 1) := by
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
      have : ∀ i : Fin k, wt i.succ.succ = 1 := fun i =>
        if_neg (fun h => Fin.succ_ne_zero i (Fin.succ_injective _ h))
      simp [this, wt]
      ring
    have h1 := hVf y hy
    change V.formOrd _ + 1 ≤ M * (E.formOrd _ + 1) + (k + 1)
    rw [hform, V.formOrd_smul hw hd (mul_ne_zero (hne q hq) (zpow_ne_zero _ hz0')), hmul q _ hq]
    rw [hs] at h1
    push_cast
    linarith

end GlobalTheory.FieldPair
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTrBasis
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair.GraphPlace

section Gen

variable {K L F W : Type} [Field K] [Field L] [Field F] [Field W] [Algebra K L] [Algebra K F] [Algebra L W]
  [Algebra K W] [IsScalarTower K L W]


omit [Algebra K W] [IsScalarTower K L W] in
theorem indep_of_lift {ι : Type} (ψ : L ⊗[K] F →ₐ[L] W) (hψ : Function.Injective ψ) {x : ι → F}
    (hx : AlgebraicIndependent K x) : AlgebraicIndependent L fun i => ψ (1 ⊗ₜ x i) := by
  rw [algebraicIndependent_iff_injective_aeval]
  have h1 : Function.Injective (Algebra.TensorProduct.map (AlgHom.id L L) (MvPolynomial.aeval (R := K) x)) :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := L) (MvPolynomial.aeval (R := K) x).toLinearMap
      (algebraicIndependent_iff_injective_aeval.1 hx)
  have e : (MvPolynomial.aeval (R := L) fun i => ψ (1 ⊗ₜ x i)) =
      (ψ.comp (Algebra.TensorProduct.map (AlgHom.id L L) (MvPolynomial.aeval (R := K) x))).comp
        (MvPolynomial.algebraTensorAlgEquiv (σ := ι) K L).symm.toAlgHom := by
    ext i
    simp
  rw [e]
  exact (hψ.comp h1).comp (MvPolynomial.algebraTensorAlgEquiv (σ := ι) K L).symm.injective

set_option synthInstance.maxHeartbeats 200000 in
theorem trdeg_of_lift (ψ : L ⊗[K] F →ₐ[L] W) (hψ : Function.Injective ψ) (M : IntermediateField L W)
    (h1 : ∀ f, ψ (1 ⊗ₜ f) ∈ M) (h2 : M ≤ IntermediateField.adjoin L (Set.range fun f => ψ (1 ⊗ₜ f))) :
    Algebra.trdeg L M = Algebra.trdeg K F := by
  obtain ⟨ι, x, hx⟩ := exists_isTranscendenceBasis' K F
  have hy := indep_of_lift ψ hψ hx.1
  rw [← hx.cardinalMk_eq_trdeg]
  apply le_antisymm
  · let E := IntermediateField.adjoin L (Set.range fun i => ψ (1 ⊗ₜ x i))
    let A := (algebraicClosure E W).restrictScalars L
    have hA : M ≤ A := by
      refine h2.trans (IntermediateField.adjoin_le_iff.2 ?_)
      rintro _ ⟨f, rfl⟩
      show ψ (1 ⊗ₜ f) ∈ algebraicClosure E W
      rw [mem_algebraicClosure_iff]
      let φ : F →ₐ[K] W := (ψ.restrictScalars K).comp Algebra.TensorProduct.includeRight
      have hf : IsAlgebraic (Algebra.adjoin K (Set.range x)) f := hx.isAlgebraic.isAlgebraic f
      have hm : ∀ a ∈ Algebra.adjoin K (Set.range x), φ a ∈ E := by
        intro a ha
        have : Algebra.adjoin K (Set.range x) ≤ ((E.restrictScalars K).toSubalgebra).comap φ := by
          refine Algebra.adjoin_le ?_
          rintro _ ⟨i, rfl⟩
          exact IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩
        exact this ha
      let g : Algebra.adjoin K (Set.range x) →+* E :=
        (φ.toRingHom.comp (Algebra.adjoin K (Set.range x)).val.toRingHom).codRestrict E fun a => hm a a.2
      have hg : Function.Injective g := fun a b h =>
        Subtype.ext (φ.toRingHom.injective (congrArg Subtype.val h))
      exact hf.ringHom_of_comp_eq g φ.toRingHom hg rfl
    have hE : Algebra.trdeg L E ≤ Cardinal.mk ι := by
      have : Algebra.IsAlgebraic (Algebra.adjoin L (Set.range fun i => (⟨ψ (1 ⊗ₜ x i),
          IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩⟩ : E))) E := by
        rw [← IntermediateField.isAlgebraic_adjoin_iff_top]
        have htop : IntermediateField.adjoin L (Set.range fun i => (⟨ψ (1 ⊗ₜ x i),
          IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩⟩ : E)) = ⊤ := by
          apply IntermediateField.lift_injective
          rw [IntermediateField.lift_adjoin, IntermediateField.lift_top, ← Set.range_comp]
          rfl
        rw [htop]
        infer_instance
      exact (Algebra.IsAlgebraic.trdeg_le_cardinalMk L _ (alg := this)).trans Cardinal.mk_range_le
    calc Algebra.trdeg L M ≤ Algebra.trdeg L A :=
          trdeg_le_of_injective (IntermediateField.inclusion hA) (IntermediateField.inclusion_injective hA)
      _ = Algebra.trdeg L (algebraicClosure E W) := rfl
      _ = Algebra.trdeg L E := by
          haveI : FaithfulSMul E (algebraicClosure E W) :=
            (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap E (algebraicClosure E W)).injective
          rw [← trdeg_add_eq L E (A := algebraicClosure E W), trdeg_eq_zero (R := E) (A := algebraicClosure E W), add_zero]
      _ ≤ _ := hE
  · have : AlgebraicIndependent L fun i => (⟨ψ (1 ⊗ₜ x i), h1 _⟩ : M) :=
      AlgebraicIndependent.of_comp M.val hy
    exact this.cardinalMk_le_trdeg

end Gen

theorem exists_trBasis {K κ' L : Type} [Field K] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ']
    [Algebra ℂ L] [Algebra (K ⊗[ℂ] κ') L] [IsScalarTower ℂ (K ⊗[ℂ] κ') L]
    [IsFractionRing (K ⊗[ℂ] κ') L] {n k' : ℕ} {x : Fin n → K} {τ' : Fin k' → κ'}
    (hx : TrBasis (algebraMap ℂ K) x) (hτ : TrBasis (algebraMap ℂ κ') τ') :
    ∃ w : Fin (k' + n) → L, TrBasis (algebraMap ℂ L) w := by
  have e1 : (algebraMap ℂ K).toAlgebra = (inferInstance : Algebra ℂ K) :=
    Algebra.algebra_ext _ _ fun _ => rfl
  have e2 : (algebraMap ℂ κ').toAlgebra = (inferInstance : Algebra ℂ κ') :=
    Algebra.algebra_ext _ _ fun _ => rfl
  have e3 : (algebraMap ℂ L).toAlgebra = (inferInstance : Algebra ℂ L) :=
    Algebra.algebra_ext _ _ fun _ => rfl
  unfold TrBasis at *
  rw [e1] at hx
  rw [e2] at hτ
  rw [e3]
  letI : Algebra K L := ((algebraMap (K ⊗[ℂ] κ') L).comp (algebraMap K (K ⊗[ℂ] κ'))).toAlgebra
  haveI : IsScalarTower K (K ⊗[ℂ] κ') L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower ℂ K L := IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply ℂ (K ⊗[ℂ] κ') L,
      IsScalarTower.algebraMap_apply ℂ K (K ⊗[ℂ] κ')]
    rfl
  have h1 : Algebra.trdeg K L = Algebra.trdeg ℂ κ' := by
    let ψ := IsScalarTower.toAlgHom K (K ⊗[ℂ] κ') L
    rw [← trdeg_of_lift ψ (IsFractionRing.injective _ _) ⊤ (fun _ => trivial) ?_]
    · exact (IntermediateField.topEquiv (F := K) (E := L)).trdeg_eq.symm
    · intro z _
      have hm : ∀ a, ψ a ∈ IntermediateField.adjoin K (Set.range fun f => ψ (1 ⊗ₜ f)) := by
        intro a
        induction a using TensorProduct.induction_on with
        | zero => rw [map_zero]; exact zero_mem _
        | add a b ha hb => rw [map_add]; exact add_mem ha hb
        | tmul l f =>
          have : l ⊗ₜ[ℂ] f = l • ((1 : K) ⊗ₜ[ℂ] f) := by simp [TensorProduct.smul_tmul']
          rw [this, map_smul]
          exact IntermediateField.smul_mem _
            (IntermediateField.subset_adjoin K _ (Set.mem_range_self f))
      obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := K ⊗[ℂ] κ') z
      exact div_mem (hm a) (hm b)
  haveI : FaithfulSMul K L := (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap K L).injective
  have h2 := trdeg_add_eq ℂ K (A := L)
  rw [h1, ← hx.cardinalMk_eq_trdeg, ← hτ.cardinalMk_eq_trdeg] at h2
  obtain ⟨ι, w, hw⟩ := exists_isTranscendenceBasis' ℂ L
  have h3 : Cardinal.mk (Fin (k' + n)) = Cardinal.mk ι := by
    rw [hw.cardinalMk_eq_trdeg, ← h2]
    simp [add_comm]
  obtain ⟨e⟩ := Cardinal.eq.1 h3
  exact ⟨w ∘ e, hw.comp_equiv e⟩

theorem exists_place : ∀ {K κ κ' L : Type} [Field K] [Field κ] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ] [Algebra ℂ κ'] [Algebra ℂ L]
    [Algebra (K ⊗[ℂ] κ') L] [IsScalarTower ℂ (K ⊗[ℂ] κ') L] [IsFractionRing (K ⊗[ℂ] κ') L]
    (n k k' : ℕ) (x : Fin n → K) (τ' : Fin k' → κ') (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ'),
  TrBasis (algebraMap ℂ K) x → TrBasis (algebraMap ℂ κ') τ' → (∃ O' : Subring κ', IsLocModel (algebraMap ℂ κ') O') → (∃ z : Fin k → κ, TrBasis (algebraMap ℂ κ) z) →
  (∀ a (h : algebraMap ℂ K a ∈ R), π ⟨algebraMap ℂ K a, h⟩ = algebraMap ℂ κ a) →
  (∀ f : κ, ∃ a b : R, π b ≠ 0 ∧ f * π b = π a) →
  IsLocModel (algebraMap ℂ K) R → Function.Injective π → (∀ g : K, ∃ a b : R, (b : K) ≠ 0 ∧ g * b = a) →
  ∀ M : ℕ, 1 ≤ k → 1 ≤ M → ∃ V : Place (algebraMap ℂ L),
    (∀ g : K, algebraMap (K ⊗[ℂ] κ') L (g ⊗ₜ 1) ∈ V.ring) ∧
    (∀ b : κ', b ≠ 0 → V.ord (algebraMap (K ⊗[ℂ] κ') L (1 ⊗ₜ b)) = 0) ∧
    (∀ g : K, g ≠ 0 → V.ord (algebraMap (K ⊗[ℂ] κ') L (g ⊗ₜ 1)) = 0) ∧
    (∀ (l : ℕ) (a : Fin l → R) (b : Fin l → κ'), ∑ i, ρ (π (a i)) * b i ≠ 0 →
      (fun (l : ℕ) (a : Fin l → R) (b : Fin l → κ') => ∑ i, algebraMap (K ⊗[ℂ] κ') L ((a i : K) ⊗ₜ b i)) l a b ≠ 0 ∧ V.ord ((fun (l : ℕ) (a : Fin l → R) (b : Fin l → κ') => ∑ i, algebraMap (K ⊗[ℂ] κ') L ((a i : K) ⊗ₜ b i)) l a b) = 0) ∧
    (∀ (l : ℕ) (a : Fin l → R) (b : Fin l → κ'), (fun (l : ℕ) (a : Fin l → R) (b : Fin l → κ') => ∑ i, algebraMap (K ⊗[ℂ] κ') L ((a i : K) ⊗ₜ b i)) l a b ≠ 0 →
      ∑ i, π (a i) ⊗ₜ[ℂ] b i ∈ (RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ'))) ^ M → (M : ℤ) ≤ V.ord ((fun (l : ℕ) (a : Fin l → R) (b : Fin l → κ') => ∑ i, algebraMap (K ⊗[ℂ] κ') L ((a i : K) ⊗ₜ b i)) l a b)) ∧
    (fun ω => @dite ℤ (∃ a, V.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (dForm (algebraMap ℂ L) (Fin.append (fun i => algebraMap (K ⊗[ℂ] κ') L (1 ⊗ₜ τ' i))
      (fun i => algebraMap (K ⊗[ℂ] κ') L (x i ⊗ₜ 1)))) + 1 ≤ k := by
  intro K κ κ' L _ _ _ _ _ _ _ _ _ _ _ n k k' x τ' R π ρ hx hτ hO hz hc hπ hR hinj hfr M hk _
  obtain ⟨Q, hQ, z, hm, hdim, hg, hb, hu, hJ, y, q, hy, hq, hform⟩ :=
    GlobalTheory.T.localRing_graph_generic_point_of_injective (L := L) n k k' x τ' R π ρ hx hτ hz hc hπ hinj hfr hR hO hk
  obtain ⟨r, rfl⟩ : ∃ r, k = r + 1 := ⟨k - 1, by omega⟩
  obtain ⟨w, hw⟩ := exists_trBasis (L := L) hx hτ
  obtain ⟨V, hV, hunit, -, hpow, hfo⟩ := GlobalTheory.T.exists_weighted_monomial_valuation_of_parameters (algebraMap ℂ L) Q hQ r (k' + n) z (fun _ => 1)
    hm (by rw [hdim]; push_cast; rfl) rfl (fun _ => le_rfl) ⟨w, hw⟩
  have hne : ∀ q : Q, IsUnit q → (q : L) ≠ 0 := fun q hq => (hq.map Q.subtype).ne_zero
  refine ⟨V, fun g => ?_, fun b h => ?_, fun g h => ?_, fun l a b h => ?_, fun l a b h0 h => ?_, ?_⟩
  · by_cases h : g = 0
    · subst h
      rw [TensorProduct.zero_tmul, map_zero]
      exact zero_mem _
    · obtain ⟨q, -, e⟩ := hg g h
      exact e ▸ hV _ q.2
  · obtain ⟨q, hq, e⟩ := hb b h
    exact e ▸ hunit q hq
  · obtain ⟨q, hq, e⟩ := hg g h
    exact e ▸ hunit q hq
  · obtain ⟨q, hq, e⟩ := hu l a b h
    exact e ▸ ⟨hne q hq, hunit q hq⟩
  · obtain ⟨q, e, hq⟩ := hJ M l a b h
    rw [← e] at h0 ⊢
    exact hpow M q h0 hq
  · have h := hfo y hy
    have hs : V.formOrd ((q : L) • dForm (algebraMap ℂ L) (fun i => (y i : L))) =
        V.formOrd (dForm (algebraMap ℂ L) (fun i => (y i : L))) := by
      by_cases h0 : dForm (algebraMap ℂ L) (fun i => (y i : L)) = 0
      · rw [h0, smul_zero]
      · rw [V.formOrd_smul hw h0 (hne q hq), hunit q hq, zero_add]
    rw [hform]
    change V.formOrd ((q : L) • dForm (algebraMap ℂ L) (fun i => (y i : L))) + 1 ≤ _
    rw [hs]
    simpa using h

end GlobalTheory.FieldPair.GraphPlace
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SteinFibreClosedFibrePointSubsetOpenPart
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbeddedPartPointsOverClosedProjPointClosed
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbeddedPartPointsOverClosedProjPointClosed
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.FibClosed

theorem closed_in_preimage {F X P B : Scheme.{0}} (p : F ⟶ B) (q : B ⟶ P) (φ : F ⟶ X) (g : X ⟶ P) [IsProper p]
    [IsPreimmersion q] [IsSeparated g] (h : φ ≫ g = p ≫ q) :
    ∃ C : Set X, IsClosed C ∧ C ∩ g ⁻¹' Set.range q = Set.range φ := by
  let m : F ⟶ pullback g q := pullback.lift φ p h
  have hm : m ≫ pullback.snd g q = p := pullback.lift_snd _ _ _
  have : IsProper (m ≫ pullback.snd g q) := by rw [hm]; infer_instance
  have : IsProper m := IsProper.of_comp m (pullback.snd g q)
  have hcl : IsClosed (Set.range m) := m.isClosedMap.isClosed_range
  have hemb : Topology.IsEmbedding (pullback.fst g q) := (pullback.fst g q).isEmbedding
  obtain ⟨C, hC, hCe⟩ := hemb.isInducing.isClosed_iff.1 hcl
  refine ⟨C, hC, ?_⟩
  rw [← Scheme.Pullback.range_fst, ← Set.image_preimage_eq_inter_range, hCe, ← Set.range_comp]
  congr 1
  ext x
  show (m ≫ pullback.fst g q) x = φ x
  rw [pullback.lift_fst]

end GlobalTheory.Mum.FibClosed

namespace GlobalTheory.Mum.FibClosed

theorem exists_redFibre (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (S : Scheme.{0}) (π : S ⟶ Sp R)
    [IsProper π] : ∃ (T : Scheme.{0}) (t : T ⟶ S) (k : T ⟶ Sp (ResidueField R)), IsLocallyNoetherian T ∧ IsReduced T ∧
      IsProper k ∧ t ≫ π = k ≫ spMap (residue R) ∧ Set.range t = π ⁻¹' {closedPoint R} := by
  have hcp : IsClosed ({closedPoint R} : Set (Sp R)) := isClosed_singleton_closedPoint R
  let Z : TopologicalSpace.Closeds S := ⟨π ⁻¹' {closedPoint R}, hcp.preimage π.continuous⟩
  let Z₀ : TopologicalSpace.Closeds (Sp R) := ⟨{closedPoint R}, hcp⟩
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  let t := I.subschemeι
  have hrt : Set.range t = π ⁻¹' {closedPoint R} := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]; rfl
  have : IsReduced I.subscheme := GlobalTheory.ReducedSubgroup.isReduced_subscheme_vanishingIdeal Z
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian π
  have : IsLocallyNoetherian I.subscheme := LocallyOfFiniteType.isLocallyNoetherian t
  have : IsClosedImmersion (spMap (residue R)) := IsClosedImmersion.spec_of_surjective _ residue_surjective
  have hr : Set.range (t ≫ π) ⊆ (Z₀ : Set (Sp R)) := by
    rintro _ ⟨x, rfl⟩
    have : t x ∈ Set.range t := ⟨x, rfl⟩
    rw [hrt] at this
    exact this
  have h1 : Scheme.IdealSheafData.vanishingIdeal Z₀ ≤ (t ≫ π).ker :=
    GlobalTheory.ReducedSubgroup.vanishingIdeal_le_ker (t ≫ π) Z₀ hr
  have h2 : (spMap (residue R)).ker ≤ Scheme.IdealSheafData.vanishingIdeal Z₀ := by
    rw [← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal]
    intro x hx
    have hx' : x = closedPoint R := hx
    rw [← SetLike.mem_coe, Scheme.Hom.support_ker]
    refine subset_closure ⟨closedPoint (ResidueField R), ?_⟩
    rw [hx']
    exact IsLocalRing.comap_closedPoint (residue R)
  let k := IsClosedImmersion.lift (spMap (residue R)) (t ≫ π) (h2.trans h1)
  have hk : k ≫ spMap (residue R) = t ≫ π := IsClosedImmersion.lift_fac _ _ _
  have : IsProper (k ≫ spMap (residue R)) := by rw [hk]; infer_instance
  have : IsProper k := IsProper.of_comp k (spMap (residue R))
  exact ⟨I.subscheme, t, k, inferInstance, inferInstance, inferInstance, hk.symm, hrt⟩

end GlobalTheory.Mum.FibClosed

namespace GlobalTheory.Mum.FibClosed

theorem ap {A B : Scheme.{0}} {f f' : A ⟶ B} (h : f = f') (x : A) : f x = f' x := h ▸ rfl

theorem range_inter_fibre_closed : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → ∀ (G' : Over S) [GrpObj G'], Smooth G'.hom → ∀ (E : Emb π G') (H' : E.H.toScheme.Opens) (X : Scheme.{0}) (o : H'.toScheme ⟶ X) (g : X ⟶ PSpace R E.N), IsSeparated g → o ≫ g = H'.ι ≫ E.f → (∀ z : E.H.toScheme, π (G'.hom (E.H.ι z)) = closedPoint R → z ∈ H') → ∀ w : PSpace R E.N, PSpace.str R E.N w = closedPoint R → ∃ C : Set X, IsClosed C ∧ C ∩ g ⁻¹' {w} = Set.range o ∩ g ⁻¹' {w} := by
  intro R _ _ _ S π hπ G' _ hG E H' X o g hg hog hH' w hw
  haveI := hπ
  haveI := hg
  obtain ⟨T, t, k, hTn, hTr, hk, htk, hrt⟩ := exists_redFibre R S π
  obtain ⟨e, l, -, hl, hlf⟩ := GlobalTheory.T.pullback_iso_baseChange_over_reduced_closedFibre R S π G' hG E T t k hTn hTr htk
  have hover : ∀ p, π (G'.hom (E.H.ι (l p))) = closedPoint R := by
    intro p
    have h1 : E.H.ι (l p) = pullback.fst G'.hom t p := by
      rw [← ap hl p, Scheme.Hom.comp_apply]
    have h2 : G'.hom (pullback.fst G'.hom t p) = t (pullback.snd G'.hom t p) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
    have h3 : t (pullback.snd G'.hom t p) ∈ Set.range t := ⟨_, rfl⟩
    rw [hrt] at h3
    rw [h1, h2]; exact h3
  have hrl : Set.range l ⊆ Set.range H'.ι := by
    rintro _ ⟨p, rfl⟩; rw [Scheme.Opens.range_ι]; exact hH' _ (hover p)
  let l' := IsOpenImmersion.lift H'.ι l hrl
  have hl' : l' ≫ H'.ι = l := IsOpenImmersion.lift_fac _ _ _
  have key : ∀ z : H'.toScheme, g (o z) = w →
      ∃ p, l' p = z ∧ E.j (pullback.fst E.Y.hom k (e.hom p)) = w := by
    intro z hz
    have hfz : E.f (H'.ι z) = w := by
      rw [← hz, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hog]
    have hcl : π (G'.hom (E.H.ι (H'.ι z))) = closedPoint R := by
      have := ap E.f_over (H'.ι z)
      simp only [Scheme.Hom.comp_apply] at this
      rw [← this, hfz, hw]
    obtain ⟨p, hp⟩ : E.H.ι (H'.ι z) ∈ Set.range (pullback.fst G'.hom t) := by
      rw [Scheme.Pullback.range_fst]
      show G'.hom _ ∈ Set.range t
      rw [hrt]; exact hcl
    have hlp : l p = H'.ι z := E.H.ι.isOpenEmbedding.injective (by
      rw [← hp, ← ap hl p, Scheme.Hom.comp_apply])
    refine ⟨p, H'.ι.isOpenEmbedding.injective (by rw [← hlp, ← ap hl' p, Scheme.Hom.comp_apply]), ?_⟩
    rw [← hfz, ← hlp]
    have h := ap hlf p
    simp only [Scheme.Hom.comp_apply] at h
    exact h.symm
  by_cases hy : ∃ y, E.j y = w
  · obtain ⟨y, rfl⟩ := hy
    haveI := E.imm
    let F := pullback (pullback.fst E.Y.hom k) (E.Y.left.fromSpecResidueField y)
    let φ : F ⟶ X := pullback.fst _ _ ≫ e.inv ≫ l' ≫ o
    have hφ : φ ≫ g = pullback.snd _ _ ≫ (E.Y.left.fromSpecResidueField y ≫ E.j) := by
      simp only [φ, Category.assoc, hog]
      rw [reassoc_of% hl', hlf, Iso.inv_hom_id_assoc, pullback.condition_assoc]
    obtain ⟨C, hC, hCe⟩ := closed_in_preimage (pullback.snd (pullback.fst E.Y.hom k)
      (E.Y.left.fromSpecResidueField y)) _ φ g hφ
    have hrange : Set.range (E.Y.left.fromSpecResidueField y ≫ E.j) = {E.j y} := by
      ext x
      simp only [Set.mem_range, Set.mem_singleton_iff, Scheme.Hom.comp_apply]
      constructor
      · rintro ⟨a, rfl⟩
        have : E.Y.left.fromSpecResidueField y a ∈ Set.range (E.Y.left.fromSpecResidueField y) := ⟨a, rfl⟩
        rw [Scheme.range_fromSpecResidueField] at this
        rw [this]
      · rintro rfl
        have : y ∈ Set.range (E.Y.left.fromSpecResidueField y) := by
          rw [Scheme.range_fromSpecResidueField]; rfl
        obtain ⟨a, ha⟩ := this
        exact ⟨a, by rw [ha]⟩
    refine ⟨C, hC, ?_⟩
    rw [← hrange, hCe]
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      refine ⟨⟨(pullback.fst _ _ ≫ e.inv ≫ l') a, ?_⟩, ?_⟩
      · show o _ = φ a
        simp only [φ, Scheme.Hom.comp_apply]
      · rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, hφ]
        exact ⟨pullback.snd (pullback.fst E.Y.hom k) (E.Y.left.fromSpecResidueField y) a,
          (Scheme.Hom.comp_apply _ _ _).symm⟩
    · rintro ⟨⟨z, rfl⟩, hz⟩
      rw [hrange] at hz
      obtain ⟨p, hp, hpj⟩ := key z hz
      have hyp : pullback.fst E.Y.hom k (e.hom p) = y := E.j.isEmbedding.injective hpj
      obtain ⟨a, ha⟩ : e.hom p ∈ Set.range (pullback.fst (pullback.fst E.Y.hom k)
          (E.Y.left.fromSpecResidueField y)) := by
        rw [Scheme.Pullback.range_fst, Scheme.range_fromSpecResidueField]
        exact hyp
      refine ⟨a, ?_⟩
      simp only [φ, Scheme.Hom.comp_apply]
      have h := ap e.hom_inv_id p
      simp only [Scheme.Hom.comp_apply] at h
      rw [ha, h]
      exact congrArg o hp
  · refine ⟨∅, isClosed_empty, ?_⟩
    ext x
    simp only [Set.empty_inter, Set.mem_empty_iff_false, Set.mem_inter_iff, Set.mem_range, Set.mem_preimage,
      Set.mem_singleton_iff, false_iff, not_and]
    rintro ⟨z, rfl⟩ hz
    obtain ⟨p, -, hpj⟩ := key z hz
    exact hy ⟨_, hpj⟩

end GlobalTheory.Mum.FibClosed
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbeddedPartPointsOverClosedProjPointClosedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.embeddedPart_points_over_closedProjPoint_closed : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → ∀ (G' : Over S) [GrpObj G'], Smooth G'.hom → ∀ (E : Emb π G') (H' : E.H.toScheme.Opens) (X : Scheme.{0}) (o : H'.toScheme ⟶ X) (g : X ⟶ PSpace R E.N), IsSeparated g → o ≫ g = H'.ι ≫ E.f → (∀ z : E.H.toScheme, π (G'.hom (E.H.ι z)) = closedPoint R → z ∈ H') → ∀ w : PSpace R E.N, PSpace.str R E.N w = closedPoint R → ∃ C : Set X, IsClosed C ∧ C ∩ g ⁻¹' {w} = Set.range o ∩ g ⁻¹' {w} := by
  first | exact @GlobalTheory.Mum.FibClosed.range_inter_fibre_closed | exact GlobalTheory.Mum.FibClosed.range_inter_fibre_closed | (intros; apply GlobalTheory.Mum.FibClosed.range_inter_fibre_closed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SteinFibreClosedFibrePointSubsetOpenPart
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem steinFibre_subset_range : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ E : Emb M.π G', ∀ (H' : E.H.toScheme.Opens) (X'' : Scheme.{0}) (ν : X'' ⟶ pullback (PSpace.str R E.N) M.π) (i : H'.toScheme ⟶ X'') (P'' : Scheme.{0}) (a'' : X'' ⟶ P'') (b'' : P'' ⟶ PSpace R E.N), IsFinite ν → IsOpenImmersion i → i ≫ ν = H'.ι ≫ pullback.lift E.f (E.H.ι ≫ G'.hom) E.f_over → a'' ≫ b'' = ν ≫ pullback.fst (PSpace.str R E.N) M.π → IsFinite b'' → IsProper a'' → (∀ y : P'', _root_.IsPreconnected {x : X'' | a'' x = y}) → (∀ h : E.H.toScheme, M.π (G'.hom (E.H.ι h)) = closedPoint R → h ∈ H') → ∀ z : H'.toScheme, M.π (G'.hom (E.H.ι (H'.ι z))) = closedPoint R → ∀ w : X'', a'' w = a'' (i z) → w ∈ Set.range i := by
  intro R _ _ _ hR M G' _ _ hG E H' X'' ν i P'' a'' b'' hν hi hcomm hab hb ha hconn hH0 z hz w hw
  haveI := hν; haveI := hb; haveI := ha; haveI := hi
  have hsep : IsSeparated (a'' ≫ b'') := inferInstance
  have hR' : IsNoetherianRing R := hR.1
  have hog : i ≫ a'' ≫ b'' = H'.ι ≫ E.f := by
    rw [hab, ← Category.assoc, hcomm, Category.assoc]
    exact congrArg (H'.ι ≫ ·) (pullback.lift_fst _ _ _)
  have hy : PSpace.str R E.N (b'' (a'' (i z))) = closedPoint R := by
    have h1 : i ≫ a'' ≫ b'' ≫ PSpace.str R E.N = H'.ι ≫ E.H.ι ≫ G'.hom ≫ M.π := by
      rw [reassoc_of% hog, E.f_over]
    have h2 := congrArg (fun f => f.base z) h1
    simp only [Scheme.Hom.comp_base, ContinuousMap.comp_apply] at h2
    exact h2.trans hz
  obtain ⟨C, hC, hCeq⟩ := GlobalTheory.T.embeddedPart_points_over_closedProjPoint_closed R M.S M.π M.proper G' hG.smooth E H' X'' i (a'' ≫ b'') hsep hog hH0
    (b'' (a'' (i z))) hy
  have hfib : ∀ p : X'', a'' p = a'' (i z) → p ∈ (a'' ≫ b'') ⁻¹' {b'' (a'' (i z))} := by
    intro p hp
    show b'' (a'' p) = b'' (a'' (i z))
    rw [hp]
  have key : ∀ p : X'', a'' p = a'' (i z) → p ∈ C → p ∈ Set.range i := fun p hp hpC =>
    (show p ∈ Set.range i ∩ (a'' ≫ b'') ⁻¹' {b'' (a'' (i z))} from hCeq ▸ ⟨hpC, hfib p hp⟩).1
  by_contra hwi
  have hU : IsOpen (Set.range i) := i.isOpenEmbedding.isOpen_range
  obtain ⟨p, hpF, hpU, hpC⟩ := hconn (a'' (i z)) (Set.range i) Cᶜ hU hC.isOpen_compl
    (fun p hp => by
      by_cases h : p ∈ C
      · exact Or.inl (key p hp h)
      · exact Or.inr h)
    ⟨i z, rfl, z, rfl⟩ ⟨w, hw, fun h => hwi (key w hw h)⟩
  exact hpC (show p ∈ C ∩ (a'' ≫ b'') ⁻¹' {b'' (a'' (i z))} from hCeq.symm ▸ ⟨hpU, hfib p hpF⟩).1

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SteinFibreClosedFibrePointSubsetOpenPartStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.steinFibre_closedFibre_point_subset_open_part : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ E : Emb M.π G', ∀ (H' : E.H.toScheme.Opens) (X'' : Scheme.{0}) (ν : X'' ⟶ pullback (PSpace.str R E.N) M.π) (i : H'.toScheme ⟶ X'') (P'' : Scheme.{0}) (a'' : X'' ⟶ P'') (b'' : P'' ⟶ PSpace R E.N), IsFinite ν → IsOpenImmersion i → i ≫ ν = H'.ι ≫ pullback.lift E.f (E.H.ι ≫ G'.hom) E.f_over → a'' ≫ b'' = ν ≫ pullback.fst (PSpace.str R E.N) M.π → IsFinite b'' → IsProper a'' → (∀ y : P'', _root_.IsPreconnected {x : X'' | a'' x = y}) → (∀ h : E.H.toScheme, M.π (G'.hom (E.H.ι h)) = closedPoint R → h ∈ H') → ∀ z : H'.toScheme, M.π (G'.hom (E.H.ι (H'.ι z))) = closedPoint R → ∀ w : X'', a'' w = a'' (i z) → w ∈ Set.range i := by
  first | exact @GlobalTheory.Mum.steinFibre_subset_range | exact GlobalTheory.Mum.steinFibre_subset_range | (intros; apply GlobalTheory.Mum.steinFibre_subset_range <;> assumption)
end
end
