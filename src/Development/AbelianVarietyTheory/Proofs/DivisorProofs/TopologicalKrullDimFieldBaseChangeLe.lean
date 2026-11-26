module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvUAbsU
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShiftedCapelliDeterminantSubleadingCoeffTrace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeSpannedByGLColumnsEqIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiDiagonalEpsilonGramMulVec

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimFieldBaseChangeLe
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimFieldBaseChangeLe
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic
open GlobalTheory.ThickeningDetermines (secIdeal)
open scoped TensorProduct

namespace GlobalTheory.FieldExtDim

theorem ringKrullDim_le_of_isIntegral (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] : ringKrullDim S ≤ ringKrullDim R :=
  Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S))
    fun I J h => Ideal.IsIntegral.comap_lt_comap (I := I.asIdeal) (J := J.asIdeal) h

theorem ringKrullDim_tensor_le (k K A : Type) [Field k] [Field K] [Algebra k K] [CommRing A]
    [Algebra k A] [Algebra.FiniteType k A] : ringKrullDim (K ⊗[k] A) ≤ ringKrullDim A := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · have : Subsingleton (K ⊗[k] A) := by
      refine ⟨fun x y => ?_⟩
      have h0 : (1 : K ⊗[k] A) = 0 := by
        rw [Algebra.TensorProduct.one_def, Subsingleton.elim (1 : A) 0, TensorProduct.tmul_zero]
      rw [← mul_one x, ← mul_one y, h0, mul_zero, mul_zero]
    rw [ringKrullDim_eq_bot_of_subsingleton]
    exact bot_le
  obtain ⟨s, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k A
  let P := MvPolynomial (Fin s) k
  letI : Algebra P A := g.toRingHom.toAlgebra
  have hiA : Algebra.IsIntegral P A := ⟨hfin.to_isIntegral⟩
  have : FaithfulSMul P A := (faithfulSMul_iff_algebraMap_injective P A).2 hinj
  have hdA : ringKrullDim A = s := by
    rw [GlobalTheory.ringKrullDim_eq_of_isIntegral P A, MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
      ringKrullDim_eq_zero_of_field, zero_add, Nat.card_eq_fintype_card, Fintype.card_fin]
  let B := K ⊗[k] P
  have hdB : ringKrullDim B = s := by
    rw [ringKrullDim_eq_of_ringEquiv (MvPolynomial.scalarRTensorAlgEquiv (R := k) (N := K)
      (σ := Fin s)).toRingEquiv, MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
      ringKrullDim_eq_zero_of_field, zero_add, Nat.card_eq_fintype_card, Fintype.card_fin]
  let φ : B →ₐ[K] K ⊗[k] A := Algebra.TensorProduct.map (AlgHom.id K K) g
  letI : Algebra B (K ⊗[k] A) := φ.toRingHom.toAlgebra
  have hcomp : (algebraMap B (K ⊗[k] A)).comp
      (Algebra.TensorProduct.includeRight : P →ₐ[k] B).toRingHom =
      (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A).toRingHom.comp (algebraMap P A) := by
    refine RingHom.ext fun p => ?_
    change φ ((1 : K) ⊗ₜ[k] p) = (1 : K) ⊗ₜ[k] g p
    rw [Algebra.TensorProduct.map_tmul]
    rfl
  have hint : Algebra.IsIntegral B (K ⊗[k] A) := ⟨fun x => by
    induction x using TensorProduct.induction_on with
    | zero => exact isIntegral_zero
    | tmul c a =>
      have h1 : IsIntegral B ((Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A) a) :=
        IsIntegral.map_of_comp_eq _ _ hcomp (Algebra.IsIntegral.isIntegral a)
      have h2 : IsIntegral B (algebraMap B (K ⊗[k] A) (c ⊗ₜ 1)) := isIntegral_algebraMap
      have he : c ⊗ₜ[k] a = algebraMap B (K ⊗[k] A) (c ⊗ₜ 1) *
          (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A) a := by
        change c ⊗ₜ[k] a = φ (c ⊗ₜ[k] (1 : P)) * ((1 : K) ⊗ₜ[k] a)
        rw [Algebra.TensorProduct.map_tmul, map_one, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
          one_mul]
        rfl
      rw [he]
      exact h2.mul h1
    | add x y hx hy => exact hx.add hy⟩
  calc ringKrullDim (K ⊗[k] A) ≤ ringKrullDim B := ringKrullDim_le_of_isIntegral B _
    _ = ringKrullDim A := hdB.trans hdA.symm

theorem topologicalKrullDim_baseChange_le :
    ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (X X' : Scheme.{0}) (f : X ⟶ Sp k)
      [LocallyOfFiniteType f] (f' : X' ⟶ Sp K) (π : X' ⟶ X),
      IsPullback π f' f (spMap (algebraMap k K)) → topologicalKrullDim X' ≤ topologicalKrullDim X := by
  intro k K _ _ _ X X' f _ f' π H
  refine topologicalKrullDim_le_of_forall_exists_isOpen fun x' => ?_
  obtain ⟨A, _, _, j, _, q, hq, hj⟩ := exists_affine_chart_over f (π x')
  obtain ⟨j₀, _, H₀⟩ := exists_affine_chart_of_isPullback H j hj
  have hft : Algebra.FiniteType k A := by
    have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k A))) := by
      rw [← hj]; infer_instance
    exact RingHom.finiteType_algebraMap.mp
      ((HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp this)
  have hs : Function.Surjective H₀.isoPullback.hom := H₀.isoPullback.hom.homeomorph.surjective
  have hrange : Set.range j₀ = π ⁻¹' Set.range j := by
    rw [← H₀.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      hs.range_eq, Set.image_univ, Scheme.Pullback.range_fst]
  refine ⟨Set.range j₀, j₀.isOpenEmbedding.isOpen_range, hrange ▸ ⟨q, hq⟩, ?_⟩
  rw [topologicalKrullDim_eq_of_isEmbedding j₀.isOpenEmbedding.isEmbedding rfl]
  calc topologicalKrullDim (Spec (.of (K ⊗[k] A))) = ringKrullDim (K ⊗[k] A) :=
        PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _
    _ ≤ ringKrullDim A := ringKrullDim_tensor_le k K A
    _ = topologicalKrullDim (Set.range j) :=
        ((topologicalKrullDim_eq_of_isEmbedding j.isOpenEmbedding.isEmbedding rfl).trans
          (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A)).symm
    _ ≤ topologicalKrullDim X := topologicalKrullDim_subspace_le _ _

end GlobalTheory.FieldExtDim
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimFieldBaseChangeLeStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic
open GlobalTheory.ThickeningDetermines (secIdeal)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topologicalKrullDim_fieldBaseChange_le : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (X X' : Scheme.{0}) (f : X ⟶ Sp k) [LocallyOfFiniteType f] (f' : X' ⟶ Sp K) (π : X' ⟶ X), IsPullback π f' f (spMap (algebraMap k K)) → topologicalKrullDim X' ≤ topologicalKrullDim X := by
  first | exact @GlobalTheory.FieldExtDim.topologicalKrullDim_baseChange_le | exact GlobalTheory.FieldExtDim.topologicalKrullDim_baseChange_le | (intros; apply GlobalTheory.FieldExtDim.topologicalKrullDim_baseChange_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusConjugationWeylCell
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG

noncomputable section

namespace GlobalTheory

namespace WeylCell

section DiagConj

variable {L : Type} [Field L] {n : ℕ}

theorem gl_eq_diagonal_of_offdiag {D : GL (Fin n) L}
    (hD : ∀ i j, i ≠ j → (D : Matrix (Fin n) (Fin n) L) i j = 0) :
    (D : Matrix (Fin n) (Fin n) L) = Matrix.diagonal fun i => (D : Matrix (Fin n) (Fin n) L) i i := by
  ext i j
  by_cases h : i = j
  · subst h; simp
  · rw [Matrix.diagonal_apply_ne _ h, hD i j h]

theorem gl_diag_ne_zero_of_offdiag {D : GL (Fin n) L}
    (hD : ∀ i j, i ≠ j → (D : Matrix (Fin n) (Fin n) L) i j = 0) (i : Fin n) :
    (D : Matrix (Fin n) (Fin n) L) i i ≠ 0 := by
  intro h0
  have h := congrFun (congrFun (Units.mul_inv D) i) i
  rw [gl_eq_diagonal_of_offdiag hD, Matrix.diagonal_mul, h0, zero_mul, Matrix.one_apply_eq] at h
  exact zero_ne_one h

theorem gl_inv_eq_diagonal_of_offdiag {D : GL (Fin n) L}
    (hD : ∀ i j, i ≠ j → (D : Matrix (Fin n) (Fin n) L) i j = 0) :
    ((D⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      Matrix.diagonal fun i => ((D : Matrix (Fin n) (Fin n) L) i i)⁻¹ := by
  have hne := gl_diag_ne_zero_of_offdiag hD
  rw [Matrix.coe_units_inv]
  apply Matrix.inv_eq_left_inv
  calc Matrix.diagonal (fun i => ((D : Matrix (Fin n) (Fin n) L) i i)⁻¹) * (D : Matrix (Fin n) (Fin n) L)
      = Matrix.diagonal (fun i => ((D : Matrix (Fin n) (Fin n) L) i i)⁻¹) *
          Matrix.diagonal (fun i => (D : Matrix (Fin n) (Fin n) L) i i) :=
        congrArg _ (gl_eq_diagonal_of_offdiag hD)
    _ = 1 := by
        rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
        congr 1
        funext i
        exact inv_mul_cancel₀ (hne i)

theorem gl_conj_apply_of_offdiag {D : GL (Fin n) L}
    (hD : ∀ i j, i ≠ j → (D : Matrix (Fin n) (Fin n) L) i j = 0) (g : GL (Fin n) L) (i j : Fin n) :
    ((D⁻¹ * g * D : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j =
      ((D : Matrix (Fin n) (Fin n) L) i i)⁻¹ * (g : Matrix (Fin n) (Fin n) L) i j *
        (D : Matrix (Fin n) (Fin n) L) j j := by
  rw [Units.val_mul, Units.val_mul, gl_inv_eq_diagonal_of_offdiag hD]
  conv_lhs => rw [gl_eq_diagonal_of_offdiag hD]
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.diagonal_apply_eq]

theorem conj_mem_unipB_of_offdiag {D : GL (Fin n) L}
    (hD : ∀ i j, i ≠ j → (D : Matrix (Fin n) (Fin n) L) i j = 0) {g : GL (Fin n) L}
    (hg : g ∈ unipB L (Fin n)) : D⁻¹ * g * D ∈ unipB L (Fin n) := by
  rw [mem_unipB] at hg ⊢
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [gl_conj_apply_of_offdiag hD, hg.1 i j hij, mul_zero, zero_mul]
  · rw [gl_conj_apply_of_offdiag hD, hg.2 i, mul_one, inv_mul_cancel₀ (gl_diag_ne_zero_of_offdiag hD i)]

theorem conj_mem_unipBLower_of_offdiag {D : GL (Fin n) L}
    (hD : ∀ i j, i ≠ j → (D : Matrix (Fin n) (Fin n) L) i j = 0) {g : GL (Fin n) L}
    (hg : g ∈ unipBLower L (Fin n)) : D⁻¹ * g * D ∈ unipBLower L (Fin n) := by
  rw [mem_unipBLower] at hg ⊢
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [gl_conj_apply_of_offdiag hD, hg.1 i j hij, mul_zero, zero_mul]
  · rw [gl_conj_apply_of_offdiag hD, hg.2 i, mul_one, inv_mul_cancel₀ (gl_diag_ne_zero_of_offdiag hD i)]

theorem weylRep_conj_offdiag {w : Equiv.Perm (Fin n)} {y t : GL (Fin n) L} (hy : IsWeylRep w y)
    (ht : ∀ i j, i ≠ j → (t : Matrix (Fin n) (Fin n) L) i j = 0) :
    ∀ i j, i ≠ j → ((y⁻¹ * t * y : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0 := by
  intro i j hij
  have hyi := hy.inv
  rw [Units.val_mul, Units.val_mul, gl_eq_diagonal_of_offdiag ht, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : l = w j
  · subst hl
    rw [Matrix.mul_diagonal, hyi i (w j) (by simpa using hij), zero_mul, zero_mul]
  · rw [hy l j hl, mul_zero]

end DiagConj

end WeylCell

end GlobalTheory

end

theorem GlobalTheory.WeylCell.diagConjU : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n : ℕ)
    (y : GU σ n) (w : Equiv.Perm (Fin n)), IsWeylRep w (y : GL (Fin n) L) → ∀ (t : GU σ n),
    (∀ i j, i ≠ j → ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0) →
    IsBorelU (y⁻¹ * t * y) ∧ ∀ u ∈ cellU y, t⁻¹ * u * t ∈ cellU y := by
  intro L _ _ σ n y w hy t ht
  have hD := weylRep_conj_offdiag hy ht
  refine ⟨fun i j hij => ?_, fun u hu => ?_⟩
  · exact hD i j (ne_of_gt hij)
  · rw [cellU, Subgroup.mem_subgroupOf, mem_cell] at hu ⊢
    have e1 : (((t⁻¹ * u * t : GU σ n)) : GL (Fin n) L) =
        ((t : GL (Fin n) L))⁻¹ * (u : GL (Fin n) L) * (t : GL (Fin n) L) := rfl
    rw [e1]
    refine ⟨conj_mem_unipB_of_offdiag ht hu.1, ?_⟩
    have e2 : ((y : GL (Fin n) L))⁻¹ * (((t : GL (Fin n) L))⁻¹ * (u : GL (Fin n) L) * (t : GL (Fin n) L)) *
        (y : GL (Fin n) L) =
        ((y : GL (Fin n) L)⁻¹ * t * y)⁻¹ * ((y : GL (Fin n) L)⁻¹ * u * y) * ((y : GL (Fin n) L)⁻¹ * t * y) := by
      group
    rw [e2]
    exact conj_mem_unipBLower_of_offdiag hD hu.2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsOpenSubgroupAdicUnitsNoRootsOfUnity
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsOpenSubgroupAdicUnitsNoRootsOfUnity
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RootOpen


open Classical in
theorem finite_roots (E : Type) [Field E] [NumberField E] :
    {t : Eˣ | ∃ n : ℕ, 0 < n ∧ t ^ n = 1}.Finite := by
  have hF : Finite (NumberField.Units.torsion E) := inferInstance
  have hT : ((NumberField.Units.torsion E : Set (𝓞 E)ˣ)).Finite := Set.finite_coe_iff.1 hF
  refine (hT.image (Units.map (algebraMap (𝓞 E) E).toMonoidHom)).subset ?_
  rintro t ⟨n, hn, ht⟩
  have h1 : IsIntegral ℤ (t : E) := IsIntegral.of_pow hn (by rw [← Units.val_pow_eq_pow_val, ht]; exact isIntegral_one)
  have h2 : IsIntegral ℤ ((t⁻¹ : Eˣ) : E) :=
    IsIntegral.of_pow hn (by rw [← Units.val_pow_eq_pow_val, inv_pow, ht, inv_one]; exact isIntegral_one)
  let u : (𝓞 E)ˣ := ⟨⟨t, h1⟩, ⟨(t⁻¹ : Eˣ), h2⟩,
    NumberField.RingOfIntegers.ext (show (t : E) * ((t⁻¹ : Eˣ) : E) = 1 by simp),
    NumberField.RingOfIntegers.ext (show ((t⁻¹ : Eˣ) : E) * (t : E) = 1 by simp)⟩
  refine ⟨u, ?_, ?_⟩
  · show u ∈ CommGroup.torsion (𝓞 E)ˣ
    refine (CommGroup.mem_torsion _).2 (isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, ?_⟩)
    ext
    show ((t ^ n : Eˣ) : E) = 1
    simp [ht]
  · ext; rfl

variable {E : Type} [Field E] [NumberField E]

theorem val_eq_one_of_lt (w : HeightOneSpectrum (𝓞 E)) {z : w.adicCompletion E} (hz : Valued.v (z - 1) < 1) :
    Valued.v z = 1 := by
  have := Valuation.map_add_eq_of_lt_left (Valued.v) (x := (1 : w.adicCompletion E)) (y := z - 1) (by simpa using hz)
  simpa using this

def congOne (w : HeightOneSpectrum (𝓞 E)) (m : ℤ) (hm : m < 0) : Subgroup (w.adicCompletion E)ˣ where
  carrier := {z | Valued.v ((z : w.adicCompletion E) - 1) ≤ WithZero.exp m}
  one_mem' := by simp
  mul_mem' := by
    intro z u hz hu
    have hz' : Valued.v ((z : w.adicCompletion E) - 1) ≤ WithZero.exp m := hz
    have hu' : Valued.v ((u : w.adicCompletion E) - 1) ≤ WithZero.exp m := hu
    have hlt : WithZero.exp m < 1 := by
      rw [← WithZero.exp_zero]; exact WithZero.exp_lt_exp.2 hm
    have h1 := val_eq_one_of_lt w (hz'.trans_lt hlt)
    show Valued.v (((z * u : (w.adicCompletion E)ˣ) : w.adicCompletion E) - 1) ≤ WithZero.exp m
    have e : ((z * u : (w.adicCompletion E)ˣ) : w.adicCompletion E) - 1 =
        (z : w.adicCompletion E) * ((u : w.adicCompletion E) - 1) + ((z : w.adicCompletion E) - 1) := by
      rw [Units.val_mul]; ring
    rw [e]
    refine Valuation.map_add_le _ ?_ hz'
    rw [map_mul, h1, one_mul]; exact hu'
  inv_mem' := by
    intro z hz
    have hz' : Valued.v ((z : w.adicCompletion E) - 1) ≤ WithZero.exp m := hz
    have hlt : WithZero.exp m < 1 := by
      rw [← WithZero.exp_zero]; exact WithZero.exp_lt_exp.2 hm
    have h1 := val_eq_one_of_lt w (hz'.trans_lt hlt)
    show Valued.v (((z⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) - 1) ≤ WithZero.exp m
    have e : ((z⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) - 1 =
        ((z⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) * (1 - (z : w.adicCompletion E)) := by
      rw [mul_sub, mul_one, Units.inv_mul]
    rw [e, map_mul, Valuation.map_sub_swap, Units.val_inv_eq_inv_val, map_inv₀, h1, inv_one, one_mul]
    exact hz'

theorem isOpen_congOne (w : HeightOneSpectrum (𝓞 E)) (m : ℤ) (hm : m < 0) :
    IsOpen (congOne w m hm : Set (w.adicCompletion E)ˣ) :=
  (GlobalTheory.Mem.UnitOpen.isOpen_val_le w m).preimage (Units.continuous_val.sub continuous_const)

end GlobalTheory.RootOpen

namespace GlobalTheory.RootOpen

theorem exists_open_subgroup_no_roots : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)), ∃ V : Subgroup (w.adicCompletion E)ˣ,
    IsOpen (V : Set (w.adicCompletion E)ˣ) ∧ ∀ t : Eˣ, (∃ n : ℕ, 0 < n ∧ t ^ n = 1) →
      Units.map (algebraMap E (w.adicCompletion E)).toMonoidHom t ∈ V → t = 1 := by
  intro E _ _ w
  set S := {t : Eˣ | ∃ n : ℕ, 0 < n ∧ t ^ n = 1}
  have hL : ((fun t : Eˣ => WithZero.log (Valued.v ((algebraMap E (w.adicCompletion E) (t : E)) - 1))) ''
      (S \ {1})).Finite := ((finite_roots E).diff).image _
  obtain ⟨b, hb⟩ := hL.bddBelow
  refine ⟨congOne w (min b 0 - 1) (by omega), isOpen_congOne w _ _, fun t ht hV => ?_⟩
  by_contra h1
  have hmem := hb ⟨t, ⟨ht, h1⟩, rfl⟩
  have hne : Valued.v ((algebraMap E (w.adicCompletion E) (t : E)) - 1) ≠ 0 := by
    rw [Ne, map_eq_zero, sub_eq_zero, ← map_one (algebraMap E (w.adicCompletion E))]
    intro e
    exact h1 (Units.ext ((algebraMap E (w.adicCompletion E)).injective e))
  have hV' : Valued.v ((algebraMap E (w.adicCompletion E) (t : E)) - 1) ≤ WithZero.exp (min b 0 - 1) := hV
  rw [← WithZero.exp_log hne, WithZero.exp_le_exp] at hV'
  simp only at hmem
  omega

end GlobalTheory.RootOpen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsOpenSubgroupAdicUnitsNoRootsOfUnityStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isOpen_subgroup_adicUnits_no_rootsOfUnity : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)), ∃ V : Subgroup (w.adicCompletion E)ˣ,
    IsOpen (V : Set (w.adicCompletion E)ˣ) ∧ ∀ t : Eˣ, (∃ n : ℕ, 0 < n ∧ t ^ n = 1) →
      Units.map (algebraMap E (w.adicCompletion E)).toMonoidHom t ∈ V → t = 1 := by
  first | exact @GlobalTheory.RootOpen.exists_open_subgroup_no_roots | exact GlobalTheory.RootOpen.exists_open_subgroup_no_roots | (intros; apply GlobalTheory.RootOpen.exists_open_subgroup_no_roots <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisDescentIntegralStructure
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueHomExtensionAbelianDvr
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbHomExtDvr

theorem existsUnique_hom_extension_abelian_dvr :
    ∀ (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (G G' : Over (Sp W)) [GrpObj G] [GrpObj G'], IsAbelianScheme G → IsAbelianScheme G' → ∀ f : (Over.pullback (spMap (algebraMap W L))).obj G ⟶ (Over.pullback (spMap (algebraMap W L))).obj G', IsMonHom f → ∃! F : G ⟶ G', (Over.pullback (spMap (algebraMap W L))).map F = f := by
  intro W L _ _ _ _ _ _ G G' _ _ hG hG' f hf
  have hsm : GlobalTheory.SS.SmConn G := ⟨hG.comm, hG.smooth, by have := hG.proper; infer_instance,
    by have := hG.proper; infer_instance, hG.geomConnected⟩
  obtain ⟨F, ⟨-, hF⟩, -⟩ := GlobalTheory.existsUnique_hom_extension_smConn_semiAbelian_dvr W L G G' hsm
    (GlobalTheory.isSemiAbelian_of_isAbelianScheme G' hG') f hf
  have := hG.smooth
  have := hG'.proper
  have : Flat G.hom := inferInstance
  refine ⟨F, hF, fun F' hF' => ?_⟩
  exact GlobalTheory.KernelNoTorsion.eq_of_generic W L (hF'.trans hF.symm)

end GlobalTheory.AbHomExtDvr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisDescentIntegralStructure
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SemilinTwist

variable {W K' : Type} [CommRing W] [CommRing K'] [Algebra W K']

noncomputable def restrictFun (σ : K' →+* K')
    (h : ∀ x : W, ∃ y : W, σ (algebraMap W K' x) = algebraMap W K' y) (x : W) : W :=
  Classical.choose (h x)

theorem algebraMap_restrictFun (σ : K' →+* K')
    (h : ∀ x : W, ∃ y : W, σ (algebraMap W K' x) = algebraMap W K' y) (x : W) :
    algebraMap W K' (restrictFun σ h x) = σ (algebraMap W K' x) :=
  (Classical.choose_spec (h x)).symm

noncomputable def restrictHom (hinj : Function.Injective (algebraMap W K')) (σ : K' →+* K')
    (h : ∀ x : W, ∃ y : W, σ (algebraMap W K' x) = algebraMap W K' y) : W →+* W where
  toFun := restrictFun σ h
  map_one' := hinj (by simp only [algebraMap_restrictFun, map_one])
  map_mul' x y := hinj (by simp only [algebraMap_restrictFun, map_mul])
  map_zero' := hinj (by simp only [algebraMap_restrictFun, map_zero])
  map_add' x y := hinj (by simp only [algebraMap_restrictFun, map_add (f := _)])

theorem algebraMap_restrictHom (hinj : Function.Injective (algebraMap W K')) (σ : K' →+* K')
    (h : ∀ x : W, ∃ y : W, σ (algebraMap W K' x) = algebraMap W K' y) (x : W) :
    σ (algebraMap W K' x) = algebraMap W K' (restrictHom hinj σ h x) :=
  (algebraMap_restrictFun σ h x).symm

theorem exists_semilinear_twist : ∀ (R K W K' : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] [Algebra R W] [Algebra K K'] [Algebra R K'] [IsScalarTower R W K'] [IsScalarTower R K K'] (σ : K' ≃ₐ[K] K'), (∀ x : W, ∃ y : W, σ (algebraMap W K' x) = algebraMap W K' y) → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (G : Over (Sp W)) [GrpObj G], IsAbelianScheme G → ∀ e : (Over.pullback (spMap (algebraMap W K'))).obj G ≅ (Over.pullback (spMap (algebraMap K K'))).obj A, IsMonHom e.hom → ∃ (τ : W →+* W) (φ : G.left ⟶ G.left), (∀ x : W, σ (algebraMap W K' x) = algebraMap W K' (τ x)) ∧ φ ≫ G.hom = G.hom ≫ spMap τ ∧ pullback.fst G.hom (spMap (algebraMap W K')) ≫ φ = (e.hom.left ≫ pullback.map A.hom (spMap (algebraMap K K')) A.hom (spMap (algebraMap K K')) (𝟙 _) (spMap (σ : K' →+* K')) (𝟙 _) (by simp) (by rw [Category.comp_id, ← Spec.map_comp]; congr 1; ext x; exact (σ.commutes x).symm) ≫ e.inv.left) ≫ pullback.fst G.hom (spMap (algebraMap W K')) := by
  intro R K W K' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ σ hσ A _ _ hA G _ hG e he
  have hinj : Function.Injective (algebraMap W K') := IsFractionRing.injective W K'
  let τ : W →+* W := restrictHom hinj (σ : K' →+* K') hσ
  have hτ : ∀ x : W, σ (algebraMap W K' x) = algebraMap W K' (τ x) :=
    algebraMap_restrictHom hinj (σ : K' →+* K') hσ
  have hsq : spMap (σ : K' →+* K') ≫ spMap (algebraMap W K') = spMap (algebraMap W K') ≫ spMap τ := by
    rw [← Spec.map_comp, ← Spec.map_comp]; congr 1; ext x; simpa using hτ x
  have hK : spMap (algebraMap K K') = spMap (σ : K' →+* K') ≫ spMap (algebraMap K K') := by
    rw [← Spec.map_comp]; congr 1; ext x; exact (σ.commutes x).symm
  let s := pullback.map A.hom (spMap (algebraMap K K')) A.hom (spMap (algebraMap K K')) (𝟙 _)
    (spMap (σ : K' →+* K')) (𝟙 _) (by simp)
    (by rw [Category.comp_id, ← Spec.map_comp]; congr 1; ext x; exact (σ.commutes x).symm)
  have hs1 : s ≫ pullback.fst A.hom (spMap (algebraMap K K')) = pullback.fst A.hom (spMap (algebraMap K K')) :=
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have hs2 : s ≫ pullback.snd A.hom (spMap (algebraMap K K')) =
      pullback.snd A.hom (spMap (algebraMap K K')) ≫ spMap (σ : K' →+* K') :=
    pullback.lift_snd _ _ _
  have hA1 := isGrpPullback_pullback A (spMap (algebraMap K K'))
  have hAs : IsGrpPullback ((Over.pullback (spMap (algebraMap K K'))).obj A)
      ((Over.pullback (spMap (algebraMap K K'))).obj A) (spMap (σ : K' →+* K')) s :=
    IsGrpPullback.cancel hA1 (hA1.congr hK hs1.symm) hs2
  haveI : IsMonHom e.hom := he
  have he1 := isGrpPullback_of_iso e
  haveI : IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)
  have he2 := isGrpPullback_of_iso e.symm
  have hG1 := isGrpPullback_pullback G (spMap (algebraMap W K'))
  have h1 := (((he1.comp hAs).comp he2).comp hG1).congr
    (by rw [Category.id_comp, Category.comp_id, hsq]) rfl
  have hGτ := isGrpPullback_pullback G (spMap τ)
  have hGτK := isGrpPullback_pullback ((Over.pullback (spMap τ)).obj G) (spMap (algebraMap W K'))
  obtain ⟨e', he', he'φ⟩ := grpPullback_iso h1 (hGτK.comp hGτ)
  obtain ⟨F, hF, -⟩ := GlobalTheory.AbHomExtDvr.existsUnique_hom_extension_abelian_dvr W K' G
    ((Over.pullback (spMap τ)).obj G) hG (isAbelianScheme_pullback_obj _ G hG) e'.hom he'
  refine ⟨τ, F.left ≫ pullback.fst G.hom (spMap τ), hτ, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (· ≫ spMap τ) (Over.w F)
  · have hFl : ((Over.pullback (spMap (algebraMap W K'))).map F).left ≫
        pullback.fst ((Over.pullback (spMap τ)).obj G).hom (spMap (algebraMap W K')) =
        pullback.fst G.hom (spMap (algebraMap W K')) ≫ F.left := pullback.lift_fst _ _ _
    rw [hF] at hFl
    rw [← Category.assoc, ← hFl, Category.assoc, he'φ]
    simp only [Category.assoc, Iso.symm_hom]
    rfl

end GlobalTheory.SemilinTwist
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisDescentIntegralStructureStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_descent_integral_structure : ∀ (R K W K' : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] [Algebra R W] [Algebra K K'] [Algebra R K'] [IsScalarTower R W K'] [IsScalarTower R K K'] (σ : K' ≃ₐ[K] K'), (∀ x : W, ∃ y : W, σ (algebraMap W K' x) = algebraMap W K' y) → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (G : Over (Sp W)) [GrpObj G], IsAbelianScheme G → ∀ e : (Over.pullback (spMap (algebraMap W K'))).obj G ≅ (Over.pullback (spMap (algebraMap K K'))).obj A, IsMonHom e.hom → ∃ (τ : W →+* W) (φ : G.left ⟶ G.left), (∀ x : W, σ (algebraMap W K' x) = algebraMap W K' (τ x)) ∧ φ ≫ G.hom = G.hom ≫ spMap τ ∧ pullback.fst G.hom (spMap (algebraMap W K')) ≫ φ = (e.hom.left ≫ pullback.map A.hom (spMap (algebraMap K K')) A.hom (spMap (algebraMap K K')) (𝟙 _) (spMap (σ : K' →+* K')) (𝟙 _) (by simp) (by rw [Category.comp_id, ← Spec.map_comp]; congr 1; ext x; exact (σ.commutes x).symm) ≫ e.inv.left) ≫ pullback.fst G.hom (spMap (algebraMap W K')) := by
  first | exact @GlobalTheory.SemilinTwist.exists_semilinear_twist | exact GlobalTheory.SemilinTwist.exists_semilinear_twist | (intros; apply GlobalTheory.SemilinTwist.exists_semilinear_twist <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemWeylCellUnitaryGroupLongSimpleReflectionIff
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemWeylCellUnitaryGroupLongSimpleReflectionIff
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG

noncomputable section

namespace GlobalTheory

namespace WeylCellRankOne

variable {L : Type} [Field L] {n : ℕ}

theorem conj_apply {s : Equiv.Perm (Fin n)} {y : GL (Fin n) L} (hy : IsWeylRep s y)
    (M : Matrix (Fin n) (Fin n) L) (i j : Fin n) :
    ((y⁻¹ : GL (Fin n) L) * M * (y : Matrix (Fin n) (Fin n) L)) i j =
      ((y⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i (s i) * M (s i) (s j) *
        (y : Matrix (Fin n) (Fin n) L) (s j) j := by
  have hi := hy.inv
  rw [Matrix.mul_apply, Finset.sum_eq_single (s j)]
  · rw [Matrix.mul_apply, Finset.sum_eq_single (s i)]
    · intro b _ hb
      rw [hi i b (by intro h; apply hb; rw [h]; simp), zero_mul]
    · simp
  · intro b _ hb; rw [hy b j hb, mul_zero]
  · simp

theorem diag_mul_eq_one {s : Equiv.Perm (Fin n)} {y : GL (Fin n) L} (hy : IsWeylRep s y) (i : Fin n) :
    ((y⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i (s i) *
        (y : Matrix (Fin n) (Fin n) L) (s i) i = 1 := by
  have h := conj_apply hy 1 i i
  rw [Matrix.mul_one, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_apply_eq,
    Matrix.one_apply_eq, mul_one] at h
  exact h.symm

theorem swap_lt {a b p q : Fin n} (hab : b.val = a.val + 1) (hpq : p < q) (hne : ¬ (p = a ∧ q = b)) :
    Equiv.swap a b p < Equiv.swap a b q := by
  rw [Fin.lt_def] at hpq ⊢
  have ha : ∀ x : Fin n, x = a ↔ x.val = a.val := fun x => Fin.ext_iff
  have hb : ∀ x : Fin n, x = b ↔ x.val = b.val := fun x => Fin.ext_iff
  simp only [Equiv.swap_apply_def]
  rw [ha, hb] at hne
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 <;> simp only [ha, hb] at * <;> omega

theorem mem_cell_swap {a b : Fin n} (hab : b.val = a.val + 1) {y : GL (Fin n) L}
    (hy : IsWeylRep (Equiv.swap a b) y) (u : GL (Fin n) L) :
    u ∈ cell y ↔ ∀ i j, ¬ (i = a ∧ j = b) →
      (u : Matrix (Fin n) (Fin n) L) i j = (1 : Matrix (Fin n) (Fin n) L) i j := by
  set s := Equiv.swap a b with hs
  have hd := diag_mul_eq_one hy
  have hne1 : ∀ i, ((y⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i (s i) ≠ 0 :=
    fun i h => by have := hd i; rw [h, zero_mul] at this; exact zero_ne_one this
  have hne2 : ∀ i, (y : Matrix (Fin n) (Fin n) L) (s i) i ≠ 0 :=
    fun i h => by have := hd i; rw [h, mul_zero] at this; exact zero_ne_one this
  have hconj : ∀ i j, ((y⁻¹ * u * y : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j =
      ((y⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i (s i) * (u : Matrix (Fin n) (Fin n) L) (s i) (s j) *
        (y : Matrix (Fin n) (Fin n) L) (s j) j := by
    intro i j; rw [Units.val_mul, Units.val_mul]; exact conj_apply hy _ i j
  have hss : ∀ x, s (s x) = x := fun x => Equiv.swap_apply_self a b x
  have hlt : a < b := by rw [Fin.lt_def]; omega
  rw [mem_cell, mem_unipB, mem_unipBLower]
  constructor
  · rintro ⟨⟨hup, hdiag⟩, hlow, -⟩ i j hij
    rcases lt_trichotomy i j with h | rfl | h
    · rw [Matrix.one_apply_ne h.ne]
      have h2 := hlow (s i) (s j) (swap_lt hab h hij)
      rw [hconj] at h2
      rcases mul_eq_zero.1 h2 with h3 | h3
      · rcases mul_eq_zero.1 h3 with h4 | h4
        · exact absurd h4 (hne1 _)
        · rwa [hss, hss] at h4
      · exact absurd h3 (hne2 _)
    · rw [Matrix.one_apply_eq]; exact hdiag i
    · rw [Matrix.one_apply_ne h.ne']; exact hup i j h
  · intro h
    have hdiag : ∀ i, (u : Matrix (Fin n) (Fin n) L) i i = 1 := fun i => by
      rw [h i i (fun hh => by rw [← hh.1, ← hh.2] at hlt; exact lt_irrefl _ hlt), Matrix.one_apply_eq]
    refine ⟨⟨fun i j hji => ?_, hdiag⟩, fun i j hij => ?_, fun i => ?_⟩
    · rw [h i j (fun hh => by rw [hh.1, hh.2] at hji; exact lt_asymm hji hlt), Matrix.one_apply_ne hji.ne']
    · rw [hconj, h (s i) (s j), Matrix.one_apply_ne, mul_zero, zero_mul]
      · intro he; exact hij.ne (s.injective he)
      · rintro ⟨h1, h2⟩
        have e1 : i = b := by rw [← hss i, h1]; exact Equiv.swap_apply_left a b
        have e2 : j = a := by rw [← hss j, h2]; exact Equiv.swap_apply_right a b
        rw [e1, e2] at hij; exact lt_asymm hij hlt
    · rw [hconj, hdiag, mul_one]; exact hd i

end WeylCellRankOne

open WeylCellRankOne in
theorem cellU_rankOne_shape : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n : ℕ)
    (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 → Even n → ∀ (y : GU σ n),
    IsWeylRep (simpleU k) (y : GL (Fin n) L) → ∀ (u : GU σ n),
    u ∈ cellU y ↔ ∀ i j, ¬ (i = lo k ∧ j = (lo k).rev) →
      ((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = (1 : Matrix (Fin n) (Fin n) L) i j := by
  intro L _ _ σ n k hk he y hy u
  have hs : simpleU k = Equiv.swap (lo k) (lo k).rev := by simp [simpleU, hk]
  rw [hs] at hy
  have hab : ((lo k).rev).val = (lo k).val + 1 := by
    obtain ⟨m, rfl⟩ := he
    have hk2 := k.isLt
    simp only [Fin.val_rev, lo, Fin.coe_castLE]
    omega
  rw [cellU, Subgroup.mem_subgroupOf]
  exact mem_cell_swap hab hy (u : GL (Fin n) L)

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemWeylCellUnitaryGroupLongSimpleReflectionIffStatement
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_weylCellUnitaryGroup_longSimpleReflection_iff : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n : ℕ)
    (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 → Even n → ∀ (y : GU σ n),
    IsWeylRep (simpleU k) (y : GL (Fin n) L) → ∀ (u : GU σ n),
    u ∈ cellU y ↔ ∀ i j, ¬ (i = lo k ∧ j = (lo k).rev) →
      ((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = (1 : Matrix (Fin n) (Fin n) L) i j := by
  first | exact @GlobalTheory.cellU_rankOne_shape | exact GlobalTheory.cellU_rankOne_shape | (intros; apply GlobalTheory.cellU_rankOne_shape <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedMatrixIntegralCompLinearEquivDet
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicCompletionDistribHaarCharEqAbsHalfSq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicCompletionDistribHaarCharEqAbsHalfSq
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ModAbs

theorem ordL_eq_ord {E : Type} [Field E] [NumberField E] (w : Pl E) {x : w.adicCompletion E} (hx : x ≠ 0) :
    ordL x = GroundTheory.LocalField.ord x := by
  have h2 := GroundTheory.Global.valued_eq_exp_neg_ord hx
  have hv : Valued.v x ≠ 0 := (Valued.v).ne_zero_iff.2 hx
  unfold ordL
  rw [dite_eq_right hv]
  have : WithZero.unzero hv = Multiplicative.ofAdd (-GroundTheory.LocalField.ord x) := by
    apply WithZero.coe_injective
    rw [WithZero.coe_unzero, h2]
    rfl
  rw [this, toAdd_ofAdd, neg_neg]

theorem haar_eq_absHalf_sq : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (x : w.adicCompletion E) (hx : x ≠ 0), (((MeasureTheory.distribHaarChar (w.adicCompletion E) (Units.mk0 x hx) : NNReal) : ℝ) : ℂ) = absHalf w x ^ 2 := by
  intro E _ _ w x hx
  have h1 := GroundTheory.LocalField.distribHaarChar_eq_modulus (K := w.adicCompletion E) (Units.mk0 x hx)
  have h3 : (GroundTheory.LocalField.residueCard (w.adicCompletion E)) = Ideal.absNorm w.asIdeal :=
    GroundTheory.Global.residueCard_adicCompletion
  rw [h1, Units.val_mk0, GroundTheory.LocalField.modulus_of_ne_zero hx, h3]
  unfold absHalf
  rw [ordL_eq_ord w hx]
  have hq : (0 : ℝ) ≤ ((qV E w : ℕ) : ℝ) ^ (-GroundTheory.LocalField.ord x) := zpow_nonneg (Nat.cast_nonneg _) _
  rw [← Complex.ofReal_pow, Real.sq_sqrt hq]
  simp [qV]

end GlobalTheory.ModAbs
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicCompletionDistribHaarCharEqAbsHalfSqStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adicCompletion_distribHaarChar_eq_absHalf_sq : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (x : w.adicCompletion E) (hx : x ≠ 0), (((MeasureTheory.distribHaarChar (w.adicCompletion E) (Units.mk0 x hx) : NNReal) : ℝ) : ℂ) = absHalf w x ^ 2 := by
  first | exact @GlobalTheory.ModAbs.haar_eq_absHalf_sq | exact GlobalTheory.ModAbs.haar_eq_absHalf_sq | (intros; apply GlobalTheory.ModAbs.haar_eq_absHalf_sq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompLinearAutLocallyConstantCompactSupportMatrix
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompLinearAutLocallyConstantCompactSupportMatrix
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LeviDesc

theorem comp_linearAut_smooth_compact : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (a b : ℕ) (L : Matrix (Fin a) (Fin b) (w.adicCompletion E) →ₗ[w.adicCompletion E] Matrix (Fin a) (Fin b) (w.adicCompletion E)) (φ : Matrix (Fin a) (Fin b) (w.adicCompletion E) → ℂ), LinearMap.det L ≠ 0 → (∃ U : AddSubgroup (Matrix (Fin a) (Fin b) (w.adicCompletion E)), IsOpen (U : Set (Matrix (Fin a) (Fin b) (w.adicCompletion E))) ∧ ∀ x, ∀ y ∈ U, φ (x + y) = φ x) → HasCompactSupport φ → (∃ U : AddSubgroup (Matrix (Fin a) (Fin b) (w.adicCompletion E)), IsOpen (U : Set (Matrix (Fin a) (Fin b) (w.adicCompletion E))) ∧ ∀ x, ∀ y ∈ U, φ (L (x + y)) = φ (L x)) ∧ HasCompactSupport (fun x => φ (L x)) ∧ LocallyCompactSpace (Matrix (Fin a) (Fin b) (w.adicCompletion E)) := by
  intro E _ _ w a b L φ hdet hlc hcs
  haveI hMT : IsModuleTopology (w.adicCompletion E) (Matrix (Fin a) (Fin b) (w.adicCompletion E)) :=
    inferInstanceAs (IsModuleTopology (w.adicCompletion E) (Fin a → Fin b → w.adicCompletion E))
  haveI hLC : LocallyCompactSpace (Matrix (Fin a) (Fin b) (w.adicCompletion E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin a → Fin b → w.adicCompletion E))
  let e := LinearMap.equivOfDetNeZero L hdet
  have he : ∀ x, e x = L x := fun x => rfl
  have hc : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have hc' : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  let h : Matrix (Fin a) (Fin b) (w.adicCompletion E) ≃ₜ Matrix (Fin a) (Fin b) (w.adicCompletion E) :=
    { toEquiv := e.toEquiv, continuous_toFun := hc, continuous_invFun := hc' }
  obtain ⟨U, hUo, hU⟩ := hlc
  refine ⟨⟨U.comap L.toAddMonoidHom, ?_, ?_⟩, ?_, hLC⟩
  · exact hUo.preimage (IsModuleTopology.continuous_of_linearMap L)
  · intro x y hy
    rw [map_add (f := _)]
    exact hU (L x) (L y) hy
  · exact hcs.comp_homeomorph h

end GlobalTheory.LeviDesc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompLinearAutLocallyConstantCompactSupportMatrixStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comp_linearAut_locallyConstant_compactSupport_matrix : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (a b : ℕ) (L : Matrix (Fin a) (Fin b) (w.adicCompletion E) →ₗ[w.adicCompletion E] Matrix (Fin a) (Fin b) (w.adicCompletion E)) (φ : Matrix (Fin a) (Fin b) (w.adicCompletion E) → ℂ), LinearMap.det L ≠ 0 → (∃ U : AddSubgroup (Matrix (Fin a) (Fin b) (w.adicCompletion E)), IsOpen (U : Set (Matrix (Fin a) (Fin b) (w.adicCompletion E))) ∧ ∀ x, ∀ y ∈ U, φ (x + y) = φ x) → HasCompactSupport φ → (∃ U : AddSubgroup (Matrix (Fin a) (Fin b) (w.adicCompletion E)), IsOpen (U : Set (Matrix (Fin a) (Fin b) (w.adicCompletion E))) ∧ ∀ x, ∀ y ∈ U, φ (L (x + y)) = φ (L x)) ∧ HasCompactSupport (fun x => φ (L x)) ∧ LocallyCompactSpace (Matrix (Fin a) (Fin b) (w.adicCompletion E)) := by
  first | exact @GlobalTheory.LeviDesc.comp_linearAut_smooth_compact | exact GlobalTheory.LeviDesc.comp_linearAut_smooth_compact | (intros; apply GlobalTheory.LeviDesc.comp_linearAut_smooth_compact <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedMatrixIntegralCompLinearEquivDet
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open MeasureTheory

theorem GlobalTheory.LeviDesc.hint_comp_linear : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (a b : ℕ) (L : Matrix (Fin a) (Fin b) (w.adicCompletion E) →ₗ[w.adicCompletion E] Matrix (Fin a) (Fin b) (w.adicCompletion E)) (φ : Matrix (Fin a) (Fin b) (w.adicCompletion E) → ℂ), LinearMap.det L ≠ 0 → (∃ U : AddSubgroup (Matrix (Fin a) (Fin b) (w.adicCompletion E)), IsOpen (U : Set (Matrix (Fin a) (Fin b) (w.adicCompletion E))) ∧ ∀ x, ∀ y ∈ U, φ (x + y) = φ x) → HasCompactSupport φ → hint (intMat a b w) (fun X => φ (L (Multiplicative.toAdd X))) = (absHalf w (LinearMap.det L) ^ 2)⁻¹ * hint (intMat a b w) (fun X => φ (Multiplicative.toAdd X)) := by
  intro E _ _ w a b L φ hL hU hc
  obtain ⟨Λ, hΛo, hΛc, hΛ⟩ := GlobalTheory.T.exists_open_compact_integralMatrixAddSubgroup E w a b
  obtain ⟨hU', hc', hlc⟩ := GlobalTheory.T.comp_linearAut_locallyConstant_compactSupport_matrix E w a b L φ hL hU hc
  letI : MeasurableSpace (Matrix (Fin a) (Fin b) (w.adicCompletion E)) := borel _
  haveI : BorelSpace (Matrix (Fin a) (Fin b) (w.adicCompletion E)) := ⟨rfl⟩
  let μ : Measure (Matrix (Fin a) (Fin b) (w.adicCompletion E)) := Measure.addHaar
  have hμ : μ.IsAddHaarMeasure := inferInstance
  rw [hΛ, GlobalTheory.T.haarIntegralNormalizedOpenCompact_eq_integral_div _ μ hμ Λ hΛo hΛc _ hU' hc', GlobalTheory.T.haarIntegralNormalizedOpenCompact_eq_integral_div _ μ hμ Λ hΛo hΛc _ hU hc,
    GlobalTheory.T.integral_comp_linearMap_matrix_nonarchLocalField _ a b L hL φ μ hμ, GlobalTheory.T.adicCompletion_distribHaarChar_eq_absHalf_sq E w _ hL]
  ring
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedMatrixIntegralCompLinearEquivDetStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalisedMatrixIntegral_comp_linearEquiv_det : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (a b : ℕ) (L : Matrix (Fin a) (Fin b) (w.adicCompletion E) →ₗ[w.adicCompletion E] Matrix (Fin a) (Fin b) (w.adicCompletion E)) (φ : Matrix (Fin a) (Fin b) (w.adicCompletion E) → ℂ), LinearMap.det L ≠ 0 → (∃ U : AddSubgroup (Matrix (Fin a) (Fin b) (w.adicCompletion E)), IsOpen (U : Set (Matrix (Fin a) (Fin b) (w.adicCompletion E))) ∧ ∀ x, ∀ y ∈ U, φ (x + y) = φ x) → HasCompactSupport φ → hint (intMat a b w) (fun X => φ (L (Multiplicative.toAdd X))) = (absHalf w (LinearMap.det L) ^ 2)⁻¹ * hint (intMat a b w) (fun X => φ (Multiplicative.toAdd X)) := by
  first | exact @GlobalTheory.LeviDesc.hint_comp_linear | exact GlobalTheory.LeviDesc.hint_comp_linear | (intros; apply GlobalTheory.LeviDesc.hint_comp_linear <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousReadOnAffineOpenRingHoms
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousReadOnAffineOpenRingHoms
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

namespace GlobalTheory.ContRead

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {U : X.Opens}

theorem val_eq_of_evHom_eq (hU : IsAffineOpen U) {σ τ : k →+* ℂ} {y : CxPts p σ} {z : CxPts p τ}
    (hy : y ∈ ptsIn p σ U) (hz : z ∈ ptsIn p τ U) (e : evHom hy = evHom hz) : y.1 = z.1 := by
  have e₁ : y.1.appLE U ⊤ hy = z.1.appLE U ⊤ hz := by
    rw [← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom]
    exact CommRingCat.hom_ext e
  have a := IsAffineOpen.SpecMap_appLE_fromSpec y.1 hU (isAffineOpen_top (Sp ℂ)) hy
  have a' := IsAffineOpen.SpecMap_appLE_fromSpec z.1 hU (isAffineOpen_top (Sp ℂ)) hz
  rw [e₁, a', IsAffineOpen.fromSpec_top] at a
  exact ((cancel_epi _).1 a).symm

theorem eq_of_val_eq (u : ∀ σ : k →+* ℂ, CxPts p σ → ℝ) {σ τ : k →+* ℂ} (e : σ = τ)
    (y : CxPts p σ) (z : CxPts p τ) (h : y.1 = z.1) : u σ y = u τ z := by
  subst e
  rw [Subtype.ext h]

theorem evHom_ofHom (hU : IsAffineOpen U) {σ : k →+* ℂ} (φ : Γ(X, U) →+* ℂ)
    (h : ∀ a, φ (algX p U a) = σ a) : evHom (ofHom_mem hU φ h) = φ :=
  RingHom.ext fun f => (ev_eq _ f).symm.trans (ev_ofHom hU φ h f)

theorem evHom_comp_algX {σ : k →+* ℂ} {y : CxPts p σ} (hy : y ∈ ptsIn p σ U) :
    (evHom hy).comp (algX p U) = σ :=
  RingHom.ext fun a => (ev_eq hy _).symm.trans (ev_algX hy a)

theorem exists_continuous_read : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (U : X.Opens) (hU : IsAffineOpen U) (u : ∀ σ : k →+* ℂ, CxPts p σ → ℝ), (∀ σ, ContinuousOn (u σ) (ptsIn p σ U)) → (letI : TopologicalSpace (Γ(X, U) →+* ℂ) := TopologicalSpace.induced (fun x : Γ(X, U) →+* ℂ => (x : Γ(X, U) → ℂ)) inferInstance; ∃ ψ : (Γ(X, U) →+* ℂ) → ℝ, Continuous ψ ∧ (∀ (σ : k →+* ℂ) (y : CxPts p σ) (hy : y ∈ ptsIn p σ U), ψ (evHom hy) = u σ y) ∧ (∀ x : Γ(X, U) →+* ℂ, ∃ (σ : k →+* ℂ) (y : CxPts p σ) (hy : y ∈ ptsIn p σ U), evHom hy = x) ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ) (hy : y ∈ ptsIn p σ U) (W : Set (Γ(X, U) →+* ℂ)), W ∈ 𝓝 (evHom hy) → {z : CxPts p σ | ∃ hz : z ∈ ptsIn p σ U, evHom hz ∈ W} ∈ 𝓝 y) := by
  intro k _ X _ p D hX U hU u hu
  letI : TopologicalSpace (Γ(X, U) →+* ℂ) :=
    TopologicalSpace.induced (fun x : Γ(X, U) →+* ℂ => (x : Γ(X, U) → ℂ)) inferInstance
  have hcf : ∀ f : Γ(X, U), Continuous fun x : Γ(X, U) →+* ℂ => x f := fun f =>
    (continuous_apply f).comp continuous_induced_dom
  refine ⟨fun x => u (x.comp (algX p U)) (ofHom hU x fun _ => rfl), ?_, ?_, ?_, ?_⟩
  · have := hX.finite_emb
    classical
    rw [continuous_iff_continuousAt]
    intro x₀
    obtain ⟨σ₀, hσ₀⟩ : ∃ σ₀, x₀.comp (algX p U) = σ₀ := ⟨_, rfl⟩
    have hN : {x : Γ(X, U) →+* ℂ | x.comp (algX p U) = σ₀} ∈ 𝓝 x₀ := by
      have hex : ∀ τ : k →+* ℂ, τ ≠ σ₀ → ∃ a, τ a ≠ σ₀ a := fun τ h => by
        by_contra hc
        push_neg at hc
        exact h (RingHom.ext hc)
      choose! a ha using hex
      have hopen : ∀ τ : k →+* ℂ,
          {x : Γ(X, U) →+* ℂ | τ ≠ σ₀ → x (algX p U (a τ)) ≠ τ (a τ)} ∈ 𝓝 x₀ := by
        intro τ
        by_cases hτ : τ = σ₀
        · exact Filter.Eventually.of_forall fun x h => (h hτ).elim
        · have ho : IsOpen {x : Γ(X, U) →+* ℂ | x (algX p U (a τ)) ≠ τ (a τ)} :=
            isOpen_ne_fun (hcf _) continuous_const
          filter_upwards [ho.mem_nhds (show x₀ (algX p U (a τ)) ≠ τ (a τ) from
            fun h => ha τ hτ (h.symm.trans (RingHom.congr_fun hσ₀ (a τ))))] with x hx _ using hx
      filter_upwards [(Filter.iInter_mem (f := 𝓝 x₀)).2 hopen] with x hx
      by_contra hne
      exact (Set.mem_iInter.1 hx _) hne rfl
    let F : (Γ(X, U) →+* ℂ) → CxPts p σ₀ := fun x =>
      if h : x.comp (algX p U) = σ₀ then ofHom hU x (fun a => RingHom.congr_fun h a)
      else ofHom hU x₀ (fun a => RingHom.congr_fun hσ₀ a)
    have hF0 : F x₀ = ofHom hU x₀ (fun a => RingHom.congr_fun hσ₀ a) := dif_pos hσ₀
    have hFmem : ∀ x, F x ∈ ptsIn p σ₀ U := fun x => by
      by_cases h : x.comp (algX p U) = σ₀
      · simp only [F, dif_pos h]; exact ofHom_mem _ _ _
      · simp only [F, dif_neg h]; exact ofHom_mem _ _ _
    have hF : ContinuousAt F x₀ := by
      refine tendsto_subtype_rng.2 ?_
      rw [hF0]
      refine GlobalTheory.Points.tendsto_of_isAffineOpen hU (ofHom_mem hU x₀ _) (Filter.Eventually.of_forall hFmem)
        fun f => ?_
      have e : ∀ᶠ x in 𝓝 x₀, x f = valR (F x).1 U f := by
        filter_upwards [hN] with x hx
        simp only [F, dif_pos hx]
        exact (ev_ofHom hU x _ f).symm
      rw [show valR (ofHom hU x₀ (fun a => RingHom.congr_fun hσ₀ a)).1 U f = x₀ f from
        ev_ofHom hU x₀ _ f]
      exact ((hcf f).tendsto x₀).congr' e
    have hu0 : ContinuousAt (u σ₀) (F x₀) :=
      (hu σ₀).continuousAt ((isOpen_ptsIn U).mem_nhds (hFmem x₀))
    refine (hu0.comp hF).congr_of_eventuallyEq ?_
    filter_upwards [hN] with x hx
    simp only [Function.comp_apply, F, dif_pos hx]
    exact eq_of_val_eq u hx _ _ rfl
  · intro σ y hy
    exact eq_of_val_eq u (evHom_comp_algX hy) _ _
      (val_eq_of_evHom_eq hU (ofHom_mem hU _ _) hy (evHom_ofHom hU _ _))
  · intro x
    exact ⟨x.comp (algX p U), ofHom hU x (fun _ => rfl), ofHom_mem hU x _, evHom_ofHom hU x _⟩
  · intro σ y hy W hW
    rw [nhds_induced] at hW
    obtain ⟨t, ht, hsub⟩ := mem_comap.1 hW
    have hc : ContinuousAt (fun z : CxPts p σ => fun f : Γ(X, U) => ev p σ U f z) y :=
      continuousAt_pi.2 fun f => (continuousOn_ev f).continuousAt ((isOpen_ptsIn U).mem_nhds hy)
    have hval : (fun f : Γ(X, U) => ev p σ U f y) = ⇑(evHom hy) := funext fun f => ev_eq hy f
    rw [← hval] at ht
    filter_upwards [hc.preimage_mem_nhds ht, (isOpen_ptsIn U).mem_nhds hy] with z hz hzU
    refine ⟨hzU, hsub ?_⟩
    have hv : (fun f : Γ(X, U) => ev p σ U f z) = ⇑(evHom hzU) := funext fun f => ev_eq hzU f
    show ⇑(evHom hzU) ∈ t
    rw [← hv]
    exact hz

end GlobalTheory.ContRead
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousReadOnAffineOpenRingHomsStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_read_on_affineOpen_ringHoms : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (U : X.Opens) (hU : IsAffineOpen U) (u : ∀ σ : k →+* ℂ, CxPts p σ → ℝ), (∀ σ, ContinuousOn (u σ) (ptsIn p σ U)) → (letI : TopologicalSpace (Γ(X, U) →+* ℂ) := TopologicalSpace.induced (fun x : Γ(X, U) →+* ℂ => (x : Γ(X, U) → ℂ)) inferInstance; ∃ ψ : (Γ(X, U) →+* ℂ) → ℝ, Continuous ψ ∧ (∀ (σ : k →+* ℂ) (y : CxPts p σ) (hy : y ∈ ptsIn p σ U), ψ (evHom hy) = u σ y) ∧ (∀ x : Γ(X, U) →+* ℂ, ∃ (σ : k →+* ℂ) (y : CxPts p σ) (hy : y ∈ ptsIn p σ U), evHom hy = x) ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ) (hy : y ∈ ptsIn p σ U) (W : Set (Γ(X, U) →+* ℂ)), W ∈ 𝓝 (evHom hy) → {z : CxPts p σ | ∃ hz : z ∈ ptsIn p σ U, evHom hz ∈ W} ∈ 𝓝 y) := by
  first | exact @GlobalTheory.ContRead.exists_continuous_read | exact GlobalTheory.ContRead.exists_continuous_read | (intros; apply GlobalTheory.ContRead.exists_continuous_read <;> assumption)
end
end
