module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfLocalLevelsUnitaryIsOpenIsCompactIsLeve
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EmbFColZeroMemMram
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.NormComparisonConstants
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowCharPowEqSelf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralLiftCoprimeDerivative
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterThetaInvariantExponent
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
public import CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohTopEuler
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsPrimeMemAsIdeal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarIntegralNormalizedIntegralMatricesTwoSidedMu
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarIntegralNormalizedIntegralMatricesTwoSidedMu
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.HintInv

theorem rStab_comp_equiv {H : Type} [Group H] (φ : H ≃* H) (u : H → ℂ) :
    rStab (u ∘ φ) = (rStab u).comap (φ : H →* H) := by
  ext k
  simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom]
  show (∀ x, u (φ (x * k)) = u (φ x)) ↔ ∀ x, u (x * φ k) = u x
  constructor
  · intro h x
    have := h (φ.symm x)
    simpa using this
  · intro h x
    rw [map_mul]; exact h _

theorem hint_comp_equiv {H : Type} [Group H] (K : Subgroup H) (φ : H ≃* H) (hK : K.map (φ : H →* H) = K)
    (u : H → ℂ) : hint K (u ∘ φ) = hint K u := by
  set S := rStab u ⊓ K with hS
  have hS' : rStab (u ∘ φ) ⊓ K = S.comap (φ : H →* H) := by
    rw [rStab_comp_equiv, hS, Subgroup.comap_inf]
    congr 1
    have h1 : (K.map (φ : H →* H)).comap (φ : H →* H) = K :=
      Subgroup.comap_map_eq_self_of_injective φ.injective K
    rw [hK] at h1
    exact h1.symm
  unfold hint
  rw [hS', Subgroup.relIndex_comap, hK]
  congr 1
  let e : H ⧸ S.comap (φ : H →* H) ≃ H ⧸ S :=
    Quotient.congr φ.toEquiv (fun a b => by
      simp only [QuotientGroup.leftRel_apply, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, map_mul, map_inv]
      rfl)
  rw [← finsum_comp_equiv e]
  refine finsum_congr fun q => ?_
  obtain ⟨s, hs⟩ := QuotientGroup.mk_out_eq_mul S (φ q.out)
  have he : e q = ((φ q.out : H) : H ⧸ S) := by
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  rw [he, hs]
  exact ((Subgroup.mem_inf.1 s.2).1 _).symm

section Integral

variable {L : Type} [Field L] {a b : ℕ}

theorem entries_of_mem_GLint {O : Subring L} {A : GL (Fin a) L} (hA : A ∈ GLint (Fin a) O) (i j : Fin a) :
    A.val i j ∈ O ∧ (A⁻¹).val i j ∈ O := by
  obtain ⟨y, rfl⟩ := hA
  rw [← map_inv]
  exact ⟨(y.val i j).2, ((y⁻¹).val i j).2⟩

theorem mul_mul_mem {O : Subring L} {P : Matrix (Fin a) (Fin a) L} {X : Matrix (Fin a) (Fin b) L}
    {Q : Matrix (Fin b) (Fin b) L} (hP : ∀ i j, P i j ∈ O) (hX : ∀ i j, X i j ∈ O) (hQ : ∀ i j, Q i j ∈ O)
    (i : Fin a) (j : Fin b) : (P * X * Q) i j ∈ O := by
  rw [Matrix.mul_apply]
  refine Subring.sum_mem _ fun l _ => Subring.mul_mem _ ?_ (hQ l j)
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hP i k) (hX k l)

def lrEquiv (A : GL (Fin a) L) (B : GL (Fin b) L) : Matrix (Fin a) (Fin b) L ≃+ Matrix (Fin a) (Fin b) L where
  toFun X := A.val * X * B.val
  invFun X := (A⁻¹).val * X * (B⁻¹).val
  left_inv X := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc A.val X, ← Matrix.mul_assoc (A⁻¹).val, ← Matrix.mul_assoc (A⁻¹).val]
    rw [Units.inv_mul, Matrix.one_mul, Units.mul_inv, Matrix.mul_one]
  right_inv X := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (A⁻¹).val X, ← Matrix.mul_assoc A.val, ← Matrix.mul_assoc A.val]
    rw [Units.mul_inv, Matrix.one_mul, Units.inv_mul, Matrix.mul_one]
  map_add' X Y := by simp only [Matrix.mul_add, Matrix.add_mul]

end Integral

theorem map_intMat {E : Type} [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (A : GLw a w) (B : GLw b w)
    (hA : A ∈ GlobalTheory.LFun.KGL w (n := a)) (hB : B ∈ GlobalTheory.LFun.KGL w (n := b)) :
    (intMat a b w).map ((lrEquiv A B).toMultiplicative : _ →* _) = intMat a b w := by
  have hint' : ∀ X : Matrix (Fin a) (Fin b) (w.adicCompletion E),
      (∀ i j, Valued.v (X i j) ≤ 1) ↔ ∀ i j, X i j ∈ Ov E w := fun X =>
    forall_congr' fun i => forall_congr' fun j => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).symm
  have hA1 := fun i j => (entries_of_mem_GLint hA i j).1
  have hA2 := fun i j => (entries_of_mem_GLint hA i j).2
  have hB1 := fun i j => (entries_of_mem_GLint hB i j).1
  have hB2 := fun i j => (entries_of_mem_GLint hB i j).2
  have key : ∀ (P : GLw a w) (Q : GLw b w), (∀ i j, P.val i j ∈ Ov E w) → (∀ i j, Q.val i j ∈ Ov E w) →
      (intMat a b w).map ((lrEquiv P Q).toMultiplicative : _ →* _) ≤ intMat a b w := by
    intro P Q hP hQ
    rw [intMat, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨X, hX, rfl⟩
    refine Subgroup.subset_closure ?_
    show ∀ i j, Valued.v ((P.val * Multiplicative.toAdd X * Q.val) i j) ≤ 1
    rw [hint']
    exact mul_mul_mem hP ((hint' _).1 hX) hQ
  refine le_antisymm (key A B hA1 hB1) ?_
  have h2 := key A⁻¹ B⁻¹ hA2 hB2
  intro X hX
  refine ⟨(lrEquiv A⁻¹ B⁻¹).toMultiplicative X, h2 ⟨X, hX, rfl⟩, ?_⟩
  show Multiplicative.ofAdd (A.val * ((A⁻¹).val * Multiplicative.toAdd X * (B⁻¹).val) * B.val) = X
  rw [show A.val * ((A⁻¹).val * Multiplicative.toAdd X * (B⁻¹).val) * B.val = Multiplicative.toAdd X from
    (lrEquiv A B).right_inv _]
  rfl

theorem hint_intMat_mul_mul :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E)
    (u : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) → ℂ) (A : GLw a w) (B : GLw b w),
    A ∈ GlobalTheory.LFun.KGL w (n := a) → B ∈ GlobalTheory.LFun.KGL w (n := b) →
    hint (intMat a b w) (fun X => u (Multiplicative.ofAdd (A.val * Multiplicative.toAdd X * B.val))) =
      hint (intMat a b w) u := by
  intro E _ _ _ a b w u A B hA hB
  exact hint_comp_equiv (intMat a b w) (lrEquiv A B).toMultiplicative (map_intMat a b w A B hA hB) u

end GlobalTheory.BCT.HintInv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarIntegralNormalizedIntegralMatricesTwoSidedMuStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haarIntegralNormalized_integralMatrices_twoSidedMul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E)
    (u : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) → ℂ) (A : GLw a w) (B : GLw b w),
    A ∈ GlobalTheory.LFun.KGL w (n := a) → B ∈ GlobalTheory.LFun.KGL w (n := b) →
    hint (intMat a b w) (fun X => u (Multiplicative.ofAdd (A.val * Multiplicative.toAdd X * B.val))) =
      hint (intMat a b w) u := by
  first | exact @GlobalTheory.BCT.HintInv.hint_intMat_mul_mul | exact GlobalTheory.BCT.HintInv.hint_intMat_mul_mul | (intros; apply GlobalTheory.BCT.HintInv.hint_intMat_mul_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportTwistedConstantTermSplitPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportTwistedConstantTermSplitPlace
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.CtLevel

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_ne_zero_of_hint_ne_zero {H : Type} [Group H] (K : Subgroup H) (u : H → ℂ) (hu : hint K u ≠ 0) :
    ∃ x, u x ≠ 0 := by
  by_contra hc
  push_neg at hc
  exact hu (by simp [hint, hc])

theorem exists_ne_zero_of_avg_ne_zero {H : Type} [Group H] (u : H → ℂ) (hu : avg u ≠ 0) : ∃ x, u x ≠ 0 := by
  by_contra hc
  push_neg at hc
  exact hu (by simp [avg, hc])

theorem blk_inv {n a b : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w)
    (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    (blk h w m X)⁻¹ = blk h w m⁻¹ (-(m.1.val * X * (m.2⁻¹).val)) := by
  refine inv_eq_of_mul_eq_one_right (Units.ext ?_)
  rw [Units.val_mul, blk_val, blk_val, Units.val_one, reindex_apply, reindex_apply, submatrix_mul_equiv,
    fromBlocks_multiply]
  have e1 : m.1.val * (m.1⁻¹).val = 1 := Units.mul_inv _
  have e2 : m.2.val * (m.2⁻¹).val = 1 := Units.mul_inv _
  simp only [Prod.fst_inv, Prod.snd_inv, Matrix.mul_zero, add_zero, Matrix.zero_mul, zero_add]
  rw [e1, e2, ← Matrix.mul_assoc, e1, Matrix.one_mul, Matrix.mul_assoc m.1.val, add_comm]
  simp [fromBlocks_one]
  exact submatrix_one_equiv (blkEq h).symm

end GlobalTheory.BCT.CtLevel

open scoped Pointwise

namespace GlobalTheory.BCT.CtLevel

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def blkTL {R : Type} {a b n : ℕ} (h : a + b = n) (g : Matrix (Fin n) (Fin n) R) : Matrix (Fin a) (Fin a) R :=
  (reindex (blkEq h).symm (blkEq h).symm g).toBlocks₁₁

def blkBR {R : Type} {a b n : ℕ} (h : a + b = n) (g : Matrix (Fin n) (Fin n) R) : Matrix (Fin b) (Fin b) R :=
  (reindex (blkEq h).symm (blkEq h).symm g).toBlocks₂₂

theorem blkTL_blk {n a b : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w)
    (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) : blkTL h (blk h w m X).val = m.1.val := by
  rw [blkTL, blk_val, ← reindex_symm, Equiv.symm_apply_apply, toBlocks_fromBlocks₁₁]

theorem blkBR_blk {n a b : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w)
    (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) : blkBR h (blk h w m X).val = m.2.val := by
  rw [blkBR, blk_val, ← reindex_symm, Equiv.symm_apply_apply, toBlocks_fromBlocks₂₂]

theorem continuous_blkTL {R : Type} [TopologicalSpace R] {a b n : ℕ} (h : a + b = n) :
    Continuous (blkTL (R := R) h) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [blkTL, toBlocks₁₁, reindex_apply, submatrix_apply, of_apply]
  exact (continuous_apply _).comp (continuous_apply _)

theorem continuous_blkBR {R : Type} [TopologicalSpace R] {a b n : ℕ} (h : a + b = n) :
    Continuous (blkBR (R := R) h) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [blkBR, toBlocks₂₂, reindex_apply, submatrix_apply, of_apply]
  exact (continuous_apply _).comp (continuous_apply _)

theorem hasCompactSupport_ctMu_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b n : ℕ) (h : a + b = n) (w : Pl E)
    (μ : (w.adicCompletion E)ˣ →* ℂˣ) (f : UL n w → ℂ), IsSplitAt w → HasCompactSupport f →
    HasCompactSupport (ctMu h w μ f) := by
  intro E _ _ _ a b n h w μ f hw hf
  have hUL : ∀ y : GLw n w, y ∈ UL n w := fun y => by rw [UL, if_pos hw]; trivial
  set S : Set (GLw n w) := Subtype.val '' tsupport f with hSdef
  have hS : IsCompact S := hf.image continuous_subtype_val
  have hK := (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).2
  set C : Set (GLw n w) := (GlobalTheory.LFun.KGL w (n := n) : Set (GLw n w)) * S * (GlobalTheory.LFun.KGL w (n := n) : Set (GLw n w)) with hCdef
  have hC : IsCompact C := (hK.mul hS).mul hK
  have hmem : ∀ m, ctMu h w μ f m ≠ 0 → ∃ X, blk h w m X ∈ C := by
    intro m hm
    have h1 := right_ne_zero_of_mul (right_ne_zero_of_mul hm)
    obtain ⟨X, hX⟩ := exists_ne_zero_of_hint_ne_zero _ _ h1
    obtain ⟨k, hk⟩ := exists_ne_zero_of_avg_ne_zero _ hX
    refine ⟨Multiplicative.toAdd X, ?_⟩
    set y := (k : GLw n w)⁻¹ * blk h w m (Multiplicative.toAdd X) * k with hy
    have hyS : y ∈ S := by
      refine ⟨⟨y, hUL y⟩, subset_tsupport _ ?_, rfl⟩
      have : toSub (UL n w) y = ⟨y, hUL y⟩ := by rw [toSub, dite_eq_left (hUL y)]
      simpa [this] using hk
    have e : blk h w m (Multiplicative.toAdd X) = (k : GLw n w) * y * (k : GLw n w)⁻¹ := by
      rw [hy]; group
    rw [e]
    exact Set.mul_mem_mul (Set.mul_mem_mul k.2 hyS) (inv_mem k.2)
  let ψ : GLw n w → ((Matrix (Fin a) (Fin a) (w.adicCompletion E) × (Matrix (Fin a) (Fin a) (w.adicCompletion E))ᵐᵒᵖ) ×
      (Matrix (Fin b) (Fin b) (w.adicCompletion E) × (Matrix (Fin b) (Fin b) (w.adicCompletion E))ᵐᵒᵖ)) :=
    fun g => ((blkTL h g.val, MulOpposite.op (blkTL h (g⁻¹).val)), (blkBR h g.val, MulOpposite.op (blkBR h (g⁻¹).val)))
  have hψ : Continuous ψ := by
    refine ((((continuous_blkTL h).comp Units.continuous_val).prodMk
      (MulOpposite.continuous_op.comp ((continuous_blkTL h).comp Units.continuous_coe_inv))).prodMk
      (((continuous_blkBR h).comp Units.continuous_val).prodMk
      (MulOpposite.continuous_op.comp ((continuous_blkBR h).comp Units.continuous_coe_inv))))
  let ι : GLw a w × GLw b w → _ := Prod.map (Units.embedProduct (Matrix (Fin a) (Fin a) (w.adicCompletion E)))
    (Units.embedProduct (Matrix (Fin b) (Fin b) (w.adicCompletion E)))
  have hι : Topology.IsClosedEmbedding ι :=
    Units.isClosedEmbedding_embedProduct.prodMap Units.isClosedEmbedding_embedProduct
  have hιψ : ∀ m X, ι m = ψ (blk h w m X) := by
    intro m X
    simp only [ι, ψ, Prod.map, Units.embedProduct_apply, blk_inv, blkTL_blk, blkBR_blk, Prod.fst_inv, Prod.snd_inv]
  have hT : IsCompact (ψ '' C) := hC.image hψ
  refine HasCompactSupport.intro' (hι.isCompact_preimage hT) (hT.isClosed.preimage hι.continuous) ?_
  intro m hm
  by_contra hne
  obtain ⟨X, hX⟩ := hmem m hne
  exact hm ⟨blk h w m X, hX, (hιψ m X).symm⟩

end GlobalTheory.BCT.CtLevel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportTwistedConstantTermSplitPlaceStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasCompactSupport_twistedConstantTermSplitPlace : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b n : ℕ) (h : a + b = n) (w : Pl E)
    (μ : (w.adicCompletion E)ˣ →* ℂˣ) (f : UL n w → ℂ), IsSplitAt w → HasCompactSupport f →
    HasCompactSupport (ctMu h w μ f) := by
  first | exact @GlobalTheory.BCT.CtLevel.hasCompactSupport_ctMu_split | exact GlobalTheory.BCT.CtLevel.hasCompactSupport_ctMu_split | (intros; apply GlobalTheory.BCT.CtLevel.hasCompactSupport_ctMu_split <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularOfRegularAtCodimOne
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits GlobalTheory.Cartier

namespace GlobalTheory.Hartogs

theorem regAt_of_forall_dvr : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X],
    (∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) →
    ∀ (φ : X.functionField) (x : X),
      (∀ z : X, z ⤳ x → IsDiscreteValuationRing (X.presheaf.stalk z) → RegAt z φ) → RegAt x φ := by
  intro X _ _ hN f x hreg
  by_contra hf
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  haveI : Nonempty U := ⟨⟨x, hx⟩⟩
  haveI := isIntegrallyClosed_sections_of_stalks hN hU
  haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  haveI := functionField_isFractionRing_of_isAffineOpen X U hU
  have key : ∀ y : U, RegAt (y : X) f ↔ ∃ s c : Γ(X, U), algebraMap _ X.functionField s * f =
      algebraMap _ X.functionField c ∧ s ∉ (hU.primeIdealOf y).asIdeal := fun y =>
    haveI := hU.isLocalization_stalk y
    GlobalTheory.NormalPole.mem_range_iff (B := X.presheaf.stalk (y : X)) (hU.primeIdealOf y).asIdeal f
  obtain ⟨p, hp, hpQ, h1, hpf⟩ := GlobalTheory.NormalPole.exists_height_one f (hU.primeIdealOf ⟨x, hx⟩).asIdeal
    fun s c e => by_contra fun hs => hf ((key ⟨x, hx⟩).2 ⟨s, c, e, hs⟩)
  let P : PrimeSpectrum Γ(X, U) := ⟨p, hp⟩
  have hz : hU.fromSpec P ∈ U := by
    have : hU.fromSpec P ∈ Set.range hU.fromSpec := ⟨P, rfl⟩
    rwa [hU.range_fromSpec] at this
  let z : U := ⟨hU.fromSpec P, hz⟩
  have hP : hU.primeIdealOf z = P :=
    hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf z)
  have hzx : (z : X) ⤳ x := by
    have h := ((PrimeSpectrum.le_iff_specializes P (hU.primeIdealOf ⟨x, hx⟩)).mp hpQ).map
      hU.fromSpec.continuous
    rwa [hU.fromSpec_primeIdealOf ⟨x, hx⟩] at h
  have hfz : ¬ RegAt (z : X) f := fun h => by
    obtain ⟨s, c, e, hs⟩ := (key z).1 h
    rw [hP] at hs
    exact hs (hpf s c e)
  clear_value z
  haveI := hU.isLocalization_stalk z
  haveI : IsDiscreteValuationRing (X.presheaf.stalk (z : X)) :=
    isDiscreteValuationRing_of_height_eq_one (hU.primeIdealOf z).asIdeal (by rw [hP]; exact h1) _
  exact hfz (hreg z hzx inferInstance)

end GlobalTheory.Hartogs
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTwistPlacesAboveK
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BigOn.Inhab

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.Mem.Chr
open Formalism.L2.Host hiding aboveF OverP
open scoped Pointwise

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem isConjPl_iff_conjPl {w w' : HeightOneSpectrum (𝓞 D.host.E)} :
    Lev.IsConjPl w w' ↔ ConjPl D.host.conj.toRingEquiv w w' := by
  rw [conjPl_iff_smul]
  constructor
  · intro hc
    have hle : D.host.conj • w.asIdeal ≤ w'.asIdeal := by
      intro y hy
      rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hy
      obtain ⟨z, hz, hzv⟩ := hc _ hy
      have e : z = y := RingOfIntegers.ext
        ((hzv.trans (bridge_star_holds D.R D.host _)).trans (D.host.conj.apply_symm_apply (y : D.host.E)))
      exact e ▸ hz
    obtain ⟨v, hv, -⟩ := existsUnique_conjPl D.host.conj.toRingEquiv w
    have hv' := (conjPl_iff_smul D.host.conj w v).1 hv
    have hvw : v = w' := HeightOneSpectrum.ext (v.isMaximal.eq_of_le w'.isPrime.ne_top (hv' ▸ hle))
    exact hvw ▸ hv'
  · intro h c hc
    exact ⟨D.host.conj • c, h ▸ Ideal.smul_mem_pointwise_smul _ _ _ hc, (bridge_star_holds D.R D.host _).symm⟩

theorem mem_aboveK {P : HeightOneSpectrum (𝓞 D.host.K)} {w : HeightOneSpectrum (𝓞 D.host.E)} :
    w ∈ aboveF (L := D.host.E) D.host.K P ↔ w.under (𝓞 D.host.K) = P := by
  simp [aboveF]

theorem overP_of_under {p : ℕ} {P : HeightOneSpectrum (𝓞 D.host.K)} (hP : ((p : ℕ) : 𝓞 D.host.K) ∈ P.asIdeal)
    {w : HeightOneSpectrum (𝓞 D.host.E)} (h : w.under (𝓞 D.host.K) = P) : OverP D.host p w := by
  subst h
  have h2 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((p : ℕ) : 𝓞 D.host.K) ∈ w.asIdeal := hP
  rwa [map_natCast] at h2

section One

variable {p : ℕ} (hp : p.Prime) (hs : SplitsC D.host.E p) {P : HeightOneSpectrum (𝓞 D.host.K)}
  (hP : ((p : ℕ) : 𝓞 D.host.K) ∈ P.asIdeal)
include hp hs hP

theorem overP_iff (w : HeightOneSpectrum (𝓞 D.host.E)) : OverP D.host p w ↔
    w ∈ aboveF (L := D.host.E) D.host.K P ∨ ∃ w' ∈ aboveF (L := D.host.E) D.host.K P, Lev.IsConjPl w' w := by
  constructor
  · intro hw
    by_cases h : w.under (𝓞 D.host.K) = P
    · exact Or.inl (mem_aboveK.2 h)
    · obtain ⟨w', hw', -⟩ := existsUnique_conjPl D.host.conj.toRingEquiv.symm w
      have hc : ConjPl D.host.conj.toRingEquiv w' w := fun x => by
        have := hw' (D.host.conj.toRingEquiv x)
        rw [RingEquiv.symm_apply_apply] at this
        exact this.symm
      have ho : OverP D.host p w' := ((conjPl_iff_mem _ w' w).1 hc _ _ (by simp)).2 hw
      exact Or.inr ⟨w', mem_aboveK.2 (((splitsC_main D.R D.host p hp hs w' ho).2.2.2 P hP w hc).2.2 h),
        isConjPl_iff_conjPl.2 hc⟩
  · rintro (h | ⟨w', h, hc⟩)
    · exact overP_of_under hP (mem_aboveK.1 h)
    · exact ((splitsC_main D.R D.host p hp hs w' (overP_of_under hP (mem_aboveK.1 h))).2.2.2 P hP w
        (isConjPl_iff_conjPl.1 hc)).1

end One

end GlobalTheory.BigOn.Inhab

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoordsBaseChange
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField Set MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX isPushout_sections)
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.ChowHt GlobalTheory.Vanishing GlobalTheory.TopForm GlobalTheory.ChartGlue

namespace GlobalTheory

section BaseChange

variable {k k' : Type} [CommRing k] [CommRing k'] {ρ : k →+* k'} {Y Y' : Scheme.{0}} {p : Y ⟶ Sp k}
  {p' : Y' ⟶ Sp k'} {r : Y' ⟶ Y} {σ : k →+* ℂ} {τ : k' →+* ℂ} {D : ℕ} {m : CxPts p' τ → CxPts p σ}

theorem CxPts.ev_appLE_of_comp (hm : ∀ z, (m z).1 = z.1 ≫ r) {U : Y.Opens} {W : Y'.Opens} (h : W ≤ r ⁻¹ᵁ U)
    (g : Γ(Y, U)) {z : CxPts p' τ} (hz : z ∈ ptsIn p' τ W) :
    ev p' τ W ((r.appLE U W h).hom g) z = ev p σ U g (m z) :=
  (ev_res h hz _).trans (ev_of_comp hm U g z).symm

def CxPts.bcMap (w : r ≫ p = p' ≫ spMap ρ) (τ : k' →+* ℂ) (z : CxPts p' τ) : CxPts p (τ.comp ρ) :=
  ⟨z.1 ≫ r, by
    rw [Category.assoc, w, ← Category.assoc, z.2, spMap, spMap, spMap, ← Spec.map_comp]
    rfl⟩

theorem CxPts.bijective_bcMap (H : IsPullback r p' p (spMap ρ)) (τ : k' →+* ℂ) :
    Function.Bijective (bcMap H.w τ) := by
  refine ⟨fun z z' h => Subtype.ext (H.hom_ext (congrArg Subtype.val h) (z.2.trans z'.2.symm)), fun y => ?_⟩
  have e : y.1 ≫ p = spMap τ ≫ spMap ρ := by
    rw [y.2, spMap, spMap, spMap, ← Spec.map_comp]
    rfl
  exact ⟨⟨H.lift y.1 (spMap τ) e, H.lift_snd _ _ _⟩, Subtype.ext (H.lift_fst _ _ _)⟩

theorem etale_coords_baseChange (H : IsPullback r p' p (spMap ρ)) {U : Y.Opens} (hU : IsAffineOpen U)
    {x : Fin D → Γ(Y, U)} (hx : (MvPolynomial.eval₂Hom (algX p U) x).Etale) :
    (MvPolynomial.eval₂Hom (algX p' (r ⁻¹ᵁ U ⊓ p' ⁻¹ᵁ ⊤))
      fun a => (r.appLE U _ inf_le_left).hom (x a)).Etale := by
  letI := ρ.toAlgebra
  letI := MvPolynomial.algebraMvPolynomial (R := k) (S := k') (σ := Fin D)
  have h₁ := (CommRingCat.isPushout_of_isPushout k k' (MvPolynomial (Fin D) k) (MvPolynomial (Fin D) k')).flip
  have h₂ := isPushout_sections p p' r H U hU
  have e₁ : CommRingCat.ofHom (algX p U) = CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin D) k)) ≫
      CommRingCat.ofHom (MvPolynomial.eval₂Hom (algX p U) x) := by
    ext a
    exact (MvPolynomial.eval₂Hom_C _ _ a).symm
  have e₂ : CommRingCat.ofHom (algX p' (r ⁻¹ᵁ U ⊓ p' ⁻¹ᵁ ⊤)) =
      CommRingCat.ofHom (algebraMap k' (MvPolynomial (Fin D) k')) ≫
      CommRingCat.ofHom (MvPolynomial.eval₂Hom (algX p' (r ⁻¹ᵁ U ⊓ p' ⁻¹ᵁ ⊤))
        fun a => (r.appLE U _ inf_le_left).hom (x a)) := by
    ext a
    exact (MvPolynomial.eval₂Hom_C _ _ a).symm
  rw [e₁, e₂] at h₂
  have h₃ := h₂.of_left (CommRingCat.hom_ext (MvPolynomial.ringHom_ext (fun a => ?_) fun a => ?_)) h₁
  · have := RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.2 RingHom.Etale.isStableUnderBaseChange
    exact MorphismProperty.of_isPushout (P := RingHom.toMorphismProperty RingHom.Etale) h₃.flip hx
  · change (r.appLE U _ _).hom (MvPolynomial.eval₂Hom _ _ (MvPolynomial.C a)) =
      MvPolynomial.eval₂Hom _ _ (MvPolynomial.map ρ (MvPolynomial.C a))
    rw [MvPolynomial.map_C, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C]
    exact RingHom.congr_fun (appLE_comp_algX H.w (inf_le_left : r ⁻¹ᵁ U ⊓ p' ⁻¹ᵁ ⊤ ≤ _)) a
  · change (r.appLE U _ _).hom (MvPolynomial.eval₂Hom _ _ (MvPolynomial.X a)) =
      MvPolynomial.eval₂Hom _ _ (MvPolynomial.map ρ (MvPolynomial.X a))
    rw [MvPolynomial.map_X, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']

theorem AlgChart.exists_baseChange (H : IsPullback r p' p (spMap ρ)) (hm : ∀ z, (m z).1 = z.1 ≫ r)
    (c : AlgChart p σ D) {z : CxPts p' τ} (hz : m z ∈ c.e.source) :
    ∃ c' : AlgChart p' τ D, z ∈ c'.e.source ∧ ∃ h : c'.U ≤ r ⁻¹ᵁ c.U,
      ∀ a, c'.x a = (r.appLE c.U c'.U h).hom (c.x a) := by
  have hU : IsAffineOpen (r ⁻¹ᵁ c.U ⊓ p' ⁻¹ᵁ ⊤) := by
    rw [show r ⁻¹ᵁ c.U ⊓ p' ⁻¹ᵁ ⊤ = r ⁻¹ᵁ c.U from inf_top_eq _]
    exact isAffineOpen_preimage_of_isPullback H c.affine
  obtain ⟨⟨e, U, hU', x, hx, h₁, h₂, h₃⟩, hy, hU', hx'⟩ := AlgChart.exists_of_etale hU _
    (etale_coords_baseChange H c.affine c.etale)
    (mem_ptsIn_inf.2 ⟨(mem_ptsIn_preimage hm).2 (c.source_subset hz), mem_ptsIn_top⟩ : z ∈ ptsIn p' τ _)
  dsimp only at hU'
  subst hU'
  dsimp only at hx'
  subst hx'
  exact ⟨_, hy, inf_le_left, fun _ => rfl⟩

variable [SmoothOfRelativeDimension D p] [SmoothOfRelativeDimension D p']

variable {B : LB Y} {B' : LB Y'}


omit [SmoothOfRelativeDimension D p] [SmoothOfRelativeDimension D p'] in
theorem Vanishing.cval_pullChart (hm : ∀ z, (m z).1 = z.1 ≫ r) (b : ChartPull B' B r) (w : r ≫ p = p' ≫ spMap ρ)
    (f : H0 p B ⊤) {i : B'.ι} {z : CxPts p' τ} (hz : z ∈ ptsIn p' τ (B'.U i)) :
    cval τ (pullChart (W := ⊤) b w le_top f) i z = cval σ f (b.idx i) (m z) :=
  ev_appLE_of_comp hm (inf_le_inf le_top (b.le i)) _ (mem_ptsIn_inf.2 ⟨mem_ptsIn_top, hz⟩)

end BaseChange

variable {F : Type} [Field F] [NumberField F] (E : Type) [Field E] [NumberField E] [Algebra F E]

namespace HilbertSamuel

end HilbertSamuel

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistDiscreteCsd
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.TwistDisc

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem pow_val_apply (χ : HChar E) (k : ℕ) (x : _) : (χ ^ k).1 x = χ.1 x ^ k := rfl

theorem chiInf_pow (χ : HChar E) (k : ℕ) (z : (Cinf E)ˣ) : chiInf (χ ^ k) z = chiInf χ z ^ k := rfl

theorem dchi_pow (χ : HChar E) (k : ℕ) : dchi (χ ^ k) = (k : ℝ) • dchi χ := by
  obtain ⟨L, hL⟩ := exists_lin _ (continuous_chiInf χ)
  have h1 : dchi χ = L := fderiv_extZero (continuous_chiInf χ) hL
  have h2 : dchi (χ ^ k) = (k : ℝ) • L := fderiv_extZero (continuous_chiInf (χ ^ k)) fun z => by
    rw [chiInf_pow, Units.val_pow_eq_pow_val, hL, ← Complex.exp_nat_mul]
    simp
  rw [h1, h2]

theorem expo_pow (χ : HChar E) (k : ℕ) (τ : E →+* ℂ) : expo (χ ^ k) τ = k * expo χ τ := by
  simp only [expo, dchi_pow, ContinuousLinearMap.smul_apply, Complex.real_smul, Complex.ofReal_natCast]
  ring

theorem chiDet_splitCentre {μ : HChar E} {e : InfinitePlace E → ℤ}
    (h : ∀ z : (Cinf E)ˣ, (chiInf μ z : ℂ) = ∏ v, (z.1 v / (‖z.1 v‖ : ℂ)) ^ e v) (t : ℝ) :
    chiDet a μ (splitCentre E a t) = 1 := by
  unfold splitCentre
  rw [chiDet, MonoidHom.comp_apply, det_infGL]
  change chiInf μ _ = 1
  apply Units.ext
  rw [h, Units.val_one]
  refine Finset.prod_eq_one fun v _ => ?_
  have hz : ((GeneralLinearGroup.det (Units.map (Matrix.scalar (Fin a)).toMonoidHom
      (expU fun _ : InfinitePlace E => (t : ℂ))) : (Cinf E)ˣ) : Cinf E) v = ((Real.exp t ^ a : ℝ) : ℂ) := by
    simp [Matrix.scalar_apply, Matrix.det_diagonal, expU, Complex.ofReal_exp]
  rw [hz, Complex.norm_real, Real.norm_of_nonneg (by positivity), div_self (by exact_mod_cast (by positivity : Real.exp t ^ a ≠ 0)), _root_.one_zpow]

theorem isSqInt_mulChi {χ : HChar E} (hu : χ.IsUnitary) (hs : ∀ t, chiDet a χ (splitCentre E a t) = 1) {φ : Sm E a}
    (h : IsSqInt φ.1) : IsSqInt (mulChi a χ φ).1 := by
  obtain ⟨h1, μ, 𝓕, hμ, hF, hI⟩ := h
  refine ⟨fun t g => ?_, μ, 𝓕, hμ, hF, ?_⟩
  · simp only [mulChi_apply, map_mul, hs, one_mul, h1]
  · have e : ∀ g, ‖(mulChi a χ φ).1 g‖ₑ = ‖φ.1 g‖ₑ := fun g => by
      have h2 : ‖((chiDet a χ g : ℂˣ) : ℂ)‖ₑ = 1 := by
        rw [← ofReal_norm_eq_enorm, show ‖((chiDet a χ g : ℂˣ) : ℂ)‖ = 1 from hu _, ENNReal.ofReal_one]
      rw [mulChi_apply, enorm_mul, h2, mul_one]
    simp only [e]
    exact hI

theorem isDiscrete_map {χ : HChar E} (hu : χ.IsUnitary) (hs : ∀ t, chiDet a χ (splitCentre E a t) = 1)
    {V : Submodule ℂ (Sm E a)} (hV : IsDiscrete V) : IsDiscrete (V.map (mulChi a χ).toLinearMap) := by
  refine { aut := ?_, sqInt := ?_, stable := ?_, ne_bot := ?_, irred := ?_ }
  · rintro _ ⟨φ, hφ, rfl⟩
    have h := hV.aut φ hφ
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro γ g
      simp [h.left, chiDet_ratGL]
    · exact isOpen_stab_of_mem_nhds _ _ <| Filter.mem_of_superset
        ((h.level.inter (isOpen_ker_chiDet χ)).mem_nhds ⟨by simp, by simp⟩) fun k hk => by
          have h1 : rt E a (finGL E a k) φ = φ := hk.1
          have h2 : chiDet a χ (finGL E a k) = 1 := hk.2
          change rt E a (finGL E a k) (CuspRep.mulChi a χ φ) = CuspRep.mulChi a χ φ
          rw [rt_mulChi, h1, h2, Units.val_one, one_smul]
    · have := h.kfin
      refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k => cptRep E a k φ)).map
        (CuspRep.mulChi a χ).toLinearMap) (Submodule.span_le.2 ?_)
      rintro _ ⟨k, rfl⟩
      exact ⟨_, Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩), (rt_mulChi χ _ φ).symm⟩
    · have := h.zfin
      refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) ''
        Zalg E a)).map (CuspRep.mulChi a χ).toLinearMap) (Submodule.span_le.2 ?_)
      rintro _ ⟨z, hz, rfl⟩
      obtain ⟨z', h1, h2⟩ := Zalg_mulChi χ hz
      exact ⟨_, Submodule.subset_span ⟨z', h1, rfl⟩, (h2 φ).symm⟩
    · intro g
      obtain ⟨C, N, h1⟩ := h.growth g
      obtain ⟨C', N', h2⟩ := chiDet_growth (a := a) χ
      refine ⟨C * (‖((chiDet a χ g : ℂˣ) : ℂ)‖ * C'), N + N', fun y => ?_⟩
      change ‖(CuspRep.mulChi a χ φ).1 (g * infGL E a y)‖ ≤ _
      rw [mulChi_apply, map_mul, Units.val_mul, norm_mul, norm_mul]
      refine (mul_le_mul (h1 y) (mul_le_mul_of_nonneg_left (h2 y) (norm_nonneg _)) (by positivity)
        ((norm_nonneg _).trans (h1 y))).trans_eq ?_
      ring
  · rintro _ ⟨φ, hφ, rfl⟩
    exact isSqInt_mulChi hu hs (hV.sqInt φ hφ)
  · rintro o _ ⟨φ, hφ, rfl⟩
    exact ⟨_, add_mem (V.smul_mem _ (hV.stable o φ hφ)) (V.smul_mem _ hφ), (act_mulChi χ o φ).symm⟩
  · intro h
    exact hV.ne_bot ((Submodule.map_eq_bot_iff (e := mulChi a χ)).1 h)
  · intro W hW hW'
    have h := hV.irred (W.comap (mulChi a χ).toLinearMap) (fun φ hφ => by
      obtain ⟨ψ, h1, h2⟩ := hW hφ
      rwa [← (mulChi a χ).injective h2]) fun o φ hφ => by
      have h1 : _ ∈ W.comap (mulChi a χ).toLinearMap := (act_mulChi χ o φ) ▸ hW' o _ hφ
      exact (Submodule.smul_mem_iff _ (Units.ne_zero (opMul χ o))).1
        ((Submodule.add_mem_iff_left _ (Submodule.smul_mem _ _ hφ)).1 h1)
    have e := Submodule.map_comap_eq_of_surjective (f := (mulChi a χ).toLinearMap) (mulChi a χ).surjective W
    exact h.imp (fun h => by rw [← e, h, Submodule.map_bot]) fun h => by rw [← e, h]

theorem isLocCompGL_map (χ : HChar E) {V : Submodule ℂ (Sm E a)} {w : HeightOneSpectrum (𝓞 E)}
    {σ : SmIrr (GL (Fin a) (w.adicCompletion E))} (h : IsLocCompGL V w σ) :
    IsLocCompGL (V.map (mulChi a χ).toLinearMap) w
      (σ.twist (CuspSub.locDet a χ w) (CuspSub.isOpen_ker_locDet χ w)) := by
  obtain ⟨f, h0, hV, hf⟩ := h
  refine ⟨(mulChi a χ).toLinearMap ∘ₗ f, fun h => h0 (LinearMap.ext fun v => (mulChi a χ).injective ?_),
    fun v => ⟨f v, hV v, rfl⟩, fun g v => ?_⟩
  · rw [LinearMap.zero_apply, map_zero]; exact LinearMap.congr_fun h v
  · change mulChi a χ (f (((CuspSub.locDet a χ w g : ℂˣ) : ℂ) • σ.ρ g v)) =
      rt E a (finGL E a (locGL E a w g)) (mulChi a χ (f v))
    rw [map_smul f, hf g v, rt_mulChi, CuspSub.chiDet_locGL]
    simp only [map_smul]
    rfl

theorem hasInfCharGL_map {V : Submodule ℂ (Sm E a)} {τ : E →+* ℂ} {m : Multiset ℂ} (h : HasInfCharGL V τ m)
    (χ : HChar E) : HasInfCharGL (V.map (mulChi a χ).toLinearMap) τ (m.map (· + expo χ τ)) := by
  refine ⟨by rw [Multiset.card_map, h.1], ?_⟩
  rintro u _ ⟨φ, hφ, rfl⟩
  change cap τ u (mulChi a χ φ) = _ • mulChi a χ φ
  rw [cap_mulChi, h.2 _ φ hφ, map_smul, Multiset.map_map]
  congr 3
  ext x
  simp [add_assoc, add_comm, add_left_comm]

end GlobalTheory.BCT.TwistDisc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffMemSubmoduleOfComplexPolyValuesMem
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffMemSubmoduleOfComplexPolyValuesMem
namespace GlobalTheory

theorem coeff_mem_of_poly_values_mem : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (S : Submodule ℂ V) (N : ℕ) (c : ℕ → V), (∀ u : ℂ, ∑ k ∈ Finset.range N, u ^ k • c k ∈ S) → ∀ k < N, c k ∈ S := by
  intro V _ _ S N c h k hk
  rw [← Submodule.Quotient.mk_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro f
  set p : Polynomial ℂ := ∑ j ∈ Finset.range N,
    Polynomial.C (f (Submodule.Quotient.mk (c j))) * Polynomial.X ^ j with hpdef
  have hp : p = 0 := by
    apply Polynomial.funext
    intro u
    have h1 : S.mkQ (∑ k ∈ Finset.range N, u ^ k • c k) = 0 :=
      (Submodule.Quotient.mk_eq_zero S).mpr (h u)
    have h0 := congrArg f h1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Submodule.mkQ_apply, smul_eq_mul, map_zero] at h0
    simp only [hpdef, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_zero]
    rw [← h0]
    exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  have hc := congrArg (fun q : Polynomial ℂ => q.coeff k) hp
  simp only [hpdef, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_zero, mul_ite, mul_one, mul_zero] at hc
  rw [Finset.sum_ite_eq] at hc
  simpa [Finset.mem_range.mpr hk] using hc

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffMemSubmoduleOfComplexPolyValuesMemStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_mem_submodule_of_complex_poly_values_mem : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (S : Submodule ℂ V) (N : ℕ) (c : ℕ → V), (∀ u : ℂ, ∑ k ∈ Finset.range N, u ^ k • c k ∈ S) → ∀ k < N, c k ∈ S := by
  first | exact @GlobalTheory.coeff_mem_of_poly_values_mem | exact GlobalTheory.coeff_mem_of_poly_values_mem | (intros; apply GlobalTheory.coeff_mem_of_poly_values_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieDerivativeL2InnerProduct
open NumberField MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section

namespace GlobalTheory.ExpDeriv

open Filter Topology GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def expGL (X : Lie E a) (t : ℝ) : GL (Fin a) (Cinf E) :=
  (Matrix.isUnit_exp (t • Matrix.of X)).unit

theorem expGL_val (X : Lie E a) (t : ℝ) :
    ((expGL X t : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E)) = NormedSpace.exp (t • Matrix.of X) := rfl

theorem expGL_zero (X : Lie E a) : expGL X 0 = 1 :=
  Units.ext (by rw [expGL_val, zero_smul, NormedSpace.exp_zero]; rfl)

theorem expGL_add (X : Lie E a) (s t : ℝ) : expGL X (s + t) = expGL X s * expGL X t := by
  apply Units.ext
  rw [Units.val_mul, expGL_val, expGL_val, expGL_val, add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl (Matrix.of X)).smul_left s).smul_right t)

theorem hasDerivAt_expGL (X : Lie E a) : HasDerivAt (fun t => toL (expGL X t).val) X 0 := by
  letI : NormedRing (Matrix (Fin a) (Fin a) (Cinf E)) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin a) (Fin a) (Cinf E)) := Matrix.linftyOpNormedAlgebra
  haveI : CompleteSpace (Matrix (Fin a) (Fin a) (Cinf E)) := FiniteDimensional.complete ℝ _
  let T : Matrix (Fin a) (Fin a) (Cinf E) →L[ℝ] Lie E a :=
    LinearMap.toContinuousLinearMap (LinearMap.id : Lie E a →ₗ[ℝ] Lie E a)
  have h := hasDerivAt_exp_smul_const' (𝕂 := ℝ) (Matrix.of X) (0 : ℝ)
  rw [zero_smul, NormedSpace.exp_zero, mul_one] at h
  exact T.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h

theorem hasDerivAt_along (X : Lie E a) (ψ : Sm E a) (g : GA E a) (t : ℝ) :
    HasDerivAt (fun s => ψ.1 (g * infGL E a (expGL X s)))
      ((lie E a X ψ).1 (g * infGL E a (expGL X t))) t := by
  have h := hasDerivAt_curve ψ (g * infGL E a (expGL X t)) (expGL X) X (expGL_zero X) (hasDerivAt_expGL X)
  have h2 := HasDerivAt.comp_sub_const t t (by rw [sub_self]; exact h)
  have e : (fun s => ψ.1 (g * infGL E a (expGL X s))) =
      fun x => ψ.1 (g * infGL E a (expGL X t) * infGL E a (expGL X (x - t))) := by
    funext s
    rw [mul_assoc, ← map_mul, ← expGL_add, add_sub_cancel]
  rw [e]
  exact h2

end GlobalTheory.ExpDeriv

namespace GlobalTheory.ExpDeriv

open Filter Topology GlobalTheory.CuspRep

end GlobalTheory.ExpDeriv

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockLevelsEqIntegralGLOfUnramified
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockLevelsEqIntegralGLOfUnramified
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.CtLevel

theorem blockDiagonalMatrixOfAddEq_entries_mem_subring {R : Type} [CommRing R] (O : Subring R) {a b n : ℕ} (h : a + b = n)
    (A : Matrix (Fin a) (Fin a) R) (D : Matrix (Fin b) (Fin b) R)
    (hA : ∀ i j, A i j ∈ O) (hD : ∀ i j, D i j ∈ O) (i j : Fin n) : dgMat h A D i j ∈ O := by
  simp only [dgMat, reindex_apply, submatrix_apply]
  rcases (blkEq h).symm i with i' | i' <;> rcases (blkEq h).symm j with j' | j' <;>
    simp [fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, hA, hD, O.zero_mem]

theorem det_mem_subring_of_entries_mem_fin {R : Type} [CommRing R] (O : Subring R) {m : ℕ} (A : Matrix (Fin m) (Fin m) R)
    (hA : ∀ i j, A i j ∈ O) : A.det ∈ O := by
  rw [Matrix.det_apply']
  exact O.sum_mem fun σ _ => O.mul_mem (intCast_mem O _) (O.prod_mem fun i _ => hA _ _)

theorem one_matrix_apply_mem_subring {R : Type} [CommRing R] (O : Subring R) {m : ℕ} (i j : Fin m) :
    (1 : Matrix (Fin m) (Fin m) R) i j ∈ O := by
  rw [Matrix.one_apply]; split_ifs
  · exact O.one_mem
  · exact O.zero_mem

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem character_det_integralGL_eq_one_of_unramified (w : Pl E) (μ : (w.adicCompletion E)ˣ →* ℂˣ)
    (hμ : ∀ u ∈ GlobalTheory.LFun.KGL w (n := 1), μ (GeneralLinearGroup.det u) = 1) {m : ℕ} (k : GLw m w)
    (hk : k ∈ GlobalTheory.LFun.KGL w (n := m)) : μ (GeneralLinearGroup.det k) = 1 := by
  set d := GeneralLinearGroup.det k
  let u : GL (Fin 1) (w.adicCompletion E) := Units.map (Matrix.scalar (Fin 1)).toMonoidHom d
  have hu : GeneralLinearGroup.det u = d := by
    ext; simp [u]
  rw [← hu]
  apply hμ
  obtain ⟨h1, h2⟩ := GlobalTheory.AdelicU.mem_GLint_iff.1 hk
  refine GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩
  · have : (u : Matrix (Fin 1) (Fin 1) _) i j = (k.val).det := by
      simp [u, d, Subsingleton.elim i j]
    rw [this]; exact det_mem_subring_of_entries_mem_fin _ _ h1
  · have : (u⁻¹ : GL (Fin 1) _).val i j = (k⁻¹ : GLw m w).val.det := by
      simp [u, d, Subsingleton.elim i j, ← map_inv]
    rw [this]; exact det_mem_subring_of_entries_mem_fin _ _ h2

end GlobalTheory.BCT.CtLevel

namespace GlobalTheory.BCT.CtLevel

theorem lev_KGL_of_unram : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b n : ℕ) (h : a + b = n)
    (w : Pl E) (μ : (w.adicCompletion E)ˣ →* ℂˣ), (∀ u ∈ GlobalTheory.LFun.KGL w (n := 1), μ (GeneralLinearGroup.det u) = 1) →
    lev₁ h w (GlobalTheory.LFun.KGL w (n := n)) μ = GlobalTheory.LFun.KGL w (n := a) ∧ lev₂ h w (GlobalTheory.LFun.KGL w (n := n)) μ = GlobalTheory.LFun.KGL w (n := b) := by
  intro E _ _ _ a b n h w μ hμ
  constructor
  · refine le_antisymm (fun x hx => hx.1.1) fun k hk => ⟨⟨hk, ?_⟩, character_det_integralGL_eq_one_of_unramified w μ hμ k hk⟩
    obtain ⟨h1, h2⟩ := GlobalTheory.AdelicU.mem_GLint_iff.1 hk
    show dgM h w (k, 1) ∈ GlobalTheory.LFun.KGL w (n := n)
    refine GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [dgM_val]
      exact blockDiagonalMatrixOfAddEq_entries_mem_subring _ h _ _ h1 (one_matrix_apply_mem_subring _) i j
    · rw [← map_inv, dgM_val]
      exact blockDiagonalMatrixOfAddEq_entries_mem_subring _ h _ _ h2 (fun i j => by simpa using one_matrix_apply_mem_subring (Ov E w) i j) i j
  · refine le_antisymm (fun x hx => hx.1.1) fun k hk => ⟨⟨hk, ?_⟩, character_det_integralGL_eq_one_of_unramified w μ hμ k hk⟩
    obtain ⟨h1, h2⟩ := GlobalTheory.AdelicU.mem_GLint_iff.1 hk
    show dgM h w (1, k) ∈ GlobalTheory.LFun.KGL w (n := n)
    refine GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [dgM_val]
      exact blockDiagonalMatrixOfAddEq_entries_mem_subring _ h _ _ (one_matrix_apply_mem_subring _) h1 i j
    · rw [← map_inv, dgM_val]
      exact blockDiagonalMatrixOfAddEq_entries_mem_subring _ h _ _ (fun i j => by simpa using one_matrix_apply_mem_subring (Ov E w) i j) h2 i j

end GlobalTheory.BCT.CtLevel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockLevelsEqIntegralGLOfUnramifiedStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockLevels_eq_integralGL_of_unramified : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b n : ℕ) (h : a + b = n) (w : Pl E)
    (μ : (w.adicCompletion E)ˣ →* ℂˣ), (∀ u ∈ GlobalTheory.LFun.KGL w (n := 1), μ (GeneralLinearGroup.det u) = 1) →
    lev₁ h w (GlobalTheory.LFun.KGL w (n := n)) μ = GlobalTheory.LFun.KGL w (n := a) ∧ lev₂ h w (GlobalTheory.LFun.KGL w (n := n)) μ = GlobalTheory.LFun.KGL w (n := b) := by
  first | exact @GlobalTheory.BCT.CtLevel.lev_KGL_of_unram | exact GlobalTheory.BCT.CtLevel.lev_KGL_of_unram | (intros; apply GlobalTheory.BCT.CtLevel.lev_KGL_of_unram <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenScal
noncomputable section

namespace GlobalTheory.LevModel

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

def Moved (X₂ X : Data E r) (δ : GL (Fin r) E) (x : Frame X₂.Ψ r) (x' : Frame X.Ψ r) : Prop :=
  ∀ (τ : E →+* ℂ) (h₂ : τ ∈ X₂.Ψ) (h₁ : τ ∈ X.Ψ),
    mat x' ⟨τ, h₁⟩ = (δ : Matrix (Fin r) (Fin r) E).map τ * mat x ⟨τ, h₂⟩


open Classical in
def genScal {S : Type} [CommRing S] (t : Sˣ) : Ix Dw → Sˣ := fun i => if i = none then t else 1

def Over (d : DeltaDat Xo c 0) (σ₂ : d.c₂.F →+* ℂ) (U : Unf Xo c (σ₂.comp (d.eF : c.F →+* d.c₂.F)) r)
    (U₂ : Unf d.Xo₂ d.c₂ σ₂ r) (k₂ : U₂.Comp) (k : U.Comp) (δ : GL (Fin r) E) : Prop :=
  ∀ (x : Frame (U₂.X k₂).Ψ r) (hx : x ∈ (U₂.X k₂).dom) (x' : Frame (U.X k).Ψ r), Moved (U₂.X k₂) (U.X k) δ x x' →
    ∃ hx' : x' ∈ (U.X k).dom, ∃ t : ℂˣ, ((∀ τ i, ‖dmin (U₂.X k₂).Gm x τ i‖ = 1) → ‖(t : ℂ)‖ = 1) ∧
      letI : Algebra c.F (CAt σ₂) := (σ₂.comp (d.eF : c.F →+* d.c₂.F)).toAlgebra
      ∃ y : FrPt Xo c (CAt σ₂),
        FrBor (S := CAt σ₂) (genScal (Dw := Dw) (S := CAt σ₂) t) (U.un k ⟨x', hx'⟩) y ∧
        FrOver d (U₂.un k₂ ⟨x, hx⟩) y

end GlobalTheory.LevModel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LoceulerHolds
namespace GlobalTheory.Laid

theorem loceuler_holds : ReciprocityTheory.Gal.LocalEulerChar := GlobalTheory.CompanionTheory.Hypotheses₂.LocalEuler.localEulerChar_holds

end GlobalTheory.Laid
end
