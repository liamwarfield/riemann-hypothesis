module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaussSumNeZeroOfRamified
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SelfDualVectorPairsIntegralFrameColumns
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIsIntegralInCompletedTensorBasisMulExp
public import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoreArithmeticGroupContainsPrincipalCongruence
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.WeightFloorInequalities
public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticBlockGeneratorsLagrangianNormalF
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticBlockGeneratorsLagrangianNormalF
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicSvN
open scoped Matrix

namespace GlobalTheory.AdelicSvN.LagrangianNormalForm

variable {F : Type} [Field F] {κ : Type} [Fintype κ] [DecidableEq κ]

theorem exists_ginv_form (X : Matrix κ κ F) :
    ∃ G C : Matrix κ κ F, X * G * X = X ∧ Cᵀ = C ∧ ∀ v, (Xᵀ * C * X) *ᵥ v = 0 → X *ᵥ v = 0 := by
  obtain ⟨L, L', d, h⟩ := Matrix.Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal X
  set P := (L.map Matrix.TransvectionStruct.toMatrix).prod with hP
  set Q := (L'.map Matrix.TransvectionStruct.toMatrix).prod with hQ
  have dP : IsUnit P.det := by rw [hP, Matrix.TransvectionStruct.det_toMatrix_prod]; exact isUnit_one
  have dQ : IsUnit Q.det := by rw [hQ, Matrix.TransvectionStruct.det_toMatrix_prod]; exact isUnit_one
  have hX : X = P⁻¹ * Matrix.diagonal d * Q⁻¹ := by
    rw [← h]
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ dQ, Matrix.mul_one,
      Matrix.nonsing_inv_mul_cancel_left _ _ dP]
  have hPX : P * X = Matrix.diagonal d * Q⁻¹ := by
    rw [← h]; simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ dQ, Matrix.mul_one]
  refine ⟨Q * Matrix.diagonal (fun i => (d i)⁻¹) * P, Pᵀ * P, ?_, ?_, ?_⟩
  · have e : Matrix.diagonal d * (Matrix.diagonal (fun i => (d i)⁻¹) * Matrix.diagonal d) = Matrix.diagonal d := by
      rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      congr 1; funext i
      by_cases hi : d i = 0
      · simp [hi]
      · simp [hi]
    conv_lhs => rw [hX]
    conv_rhs => rw [hX, ← e]
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ dQ,
      Matrix.mul_nonsing_inv_cancel_left _ _ dP]
  · rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  · intro v hv
    have e : Xᵀ * (Pᵀ * P) * X = (Q⁻¹)ᵀ * (Matrix.diagonal d * (Matrix.diagonal d * Q⁻¹)) := by
      have : Xᵀ * (Pᵀ * P) * X = (P * X)ᵀ * (P * X) := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      rw [this, hPX, Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc]
    rw [e] at hv
    have h2 := congrArg (fun w => Qᵀ *ᵥ w) hv
    simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at h2
    rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ dQ, Matrix.transpose_one,
      Matrix.one_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at h2
    have h3 : Matrix.diagonal d *ᵥ (Q⁻¹ *ᵥ v) = 0 := by
      funext i
      have := congrFun h2 i
      simp only [Matrix.mulVec_diagonal, Pi.zero_apply] at this ⊢
      rcases mul_eq_zero.mp this with h0 | h0
      · simp [h0]
      · exact h0
    rw [hX, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h3, Matrix.mulVec_zero]

theorem exists_symm_isUnit (X Y : Matrix κ κ F) (hs : Xᵀ * Y = Yᵀ * X)
    (hi : ∀ v, X *ᵥ v = 0 → Y *ᵥ v = 0 → v = 0) :
    ∃ C : Matrix κ κ F, Cᵀ = C ∧ IsUnit (Y + C * X).det := by
  obtain ⟨G, C, hG, hC, hv⟩ := exists_ginv_form X
  refine ⟨C - Gᵀ * (Xᵀ * Y) * G, ?_, ?_⟩
  · rw [Matrix.transpose_sub, hC]
    congr 1
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Yᵀ, ← hs, Matrix.mul_assoc]
  · have e : Xᵀ * (Y + (C - Gᵀ * (Xᵀ * Y) * G) * X) = Xᵀ * C * X := by
      have e1 : Xᵀ * (Gᵀ * (Xᵀ * Y) * G * X) = Xᵀ * Y := by
        have : Xᵀ * (Gᵀ * (Xᵀ * Y) * G * X) = (X * G * X)ᵀ * Y * G * X := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
        rw [this, hG, hs, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc X, hG]
      rw [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, e1, Matrix.mul_assoc]
      abel
    rw [isUnit_iff_ne_zero]
    intro h0
    obtain ⟨v, hv0, hv1⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    have hX : X *ᵥ v = 0 := by
      apply hv
      rw [← e, ← Matrix.mulVec_mulVec, hv1, Matrix.mulVec_zero]
    apply hv0
    apply hi v hX
    rwa [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hX, Matrix.mulVec_zero, add_zero] at hv1

theorem upper_mem (S : Matrix κ κ F) (hS : Sᵀ = S) :
    Matrix.fromBlocks 1 S 0 1 ∈ Submonoid.closure (gens F κ) := by
  have hJ : Matrix.fromBlocks (0 : Matrix κ κ F) (1 : Matrix κ κ F) (-1 : Matrix κ κ F) (0 : Matrix κ κ F)
      ∈ Submonoid.closure (gens F κ) := Submonoid.subset_closure (Or.inr rfl)
  have hn : Matrix.fromBlocks (1 : Matrix κ κ F) (0 : Matrix κ κ F) (-S) (1 : Matrix κ κ F)
      ∈ Submonoid.closure (gens F κ) := Submonoid.subset_closure (Or.inl (Or.inr ⟨S, hS, rfl⟩))
  have := mul_mem (mul_mem (mul_mem (mul_mem hJ hn) hJ) hJ) hJ
  simpa [Matrix.fromBlocks_multiply] using this

theorem exists_mem_closure (F : Type) [Field F] (κ : Type) [Fintype κ] [DecidableEq κ]
    (L : Submodule F ((κ → F) × (κ → F)))
    (hL : ∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) (hd : Module.finrank F L = Fintype.card κ) :
    ∃ g ∈ Submonoid.closure (gens F κ), ∀ y : κ → F,
      ((g *ᵥ Sum.elim 0 y) ∘ Sum.inl, (g *ᵥ Sum.elim 0 y) ∘ Sum.inr) ∈ L := by
  let b : Module.Basis κ F L := (Module.finBasisOfFinrankEq F L hd).reindex (Fintype.equivFin κ).symm
  let X : Matrix κ κ F := Matrix.of fun i j => (b j).1.1 i
  let Y : Matrix κ κ F := Matrix.of fun i j => (b j).1.2 i
  have key : ∀ v : κ → F, (X *ᵥ v, Y *ᵥ v) = ((∑ j, v j • b j : L) : (κ → F) × (κ → F)) := by
    intro v
    ext i
    · simp [X, Matrix.mulVec, dotProduct, Prod.fst_sum, mul_comm]
    · simp [Y, Matrix.mulVec, dotProduct, Prod.snd_sum, mul_comm]
  have hs : Xᵀ * Y = Yᵀ * X := by
    ext i j
    have := hL _ (b i).2 _ (b j).2
    simp only [dotProduct] at this
    simp only [Matrix.mul_apply, X, Y, Matrix.transpose_apply, Matrix.of_apply]
    rw [this]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have hi : ∀ v, X *ᵥ v = 0 → Y *ᵥ v = 0 → v = 0 := by
    intro v h1 h2
    have h3 := key v
    rw [h1, h2] at h3
    have h4 : ∑ j, v j • b j = 0 := Subtype.ext h3.symm
    funext j
    exact Fintype.linearIndependent_iff.mp b.linearIndependent v h4 j
  obtain ⟨C, hC, hM⟩ := exists_symm_isUnit X Y hs hi
  set M := Y + C * X with hMdef
  have hXM : Xᵀ * M = Mᵀ * X := by
    rw [hMdef, Matrix.transpose_add, Matrix.transpose_mul, hC, Matrix.mul_add, Matrix.add_mul, hs,
      Matrix.mul_assoc]
  have hS : (X * M⁻¹)ᵀ = X * M⁻¹ := by
    have h1 : (M⁻¹)ᵀ * Mᵀ = 1 := by
      rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hM, Matrix.transpose_one]
    calc (X * M⁻¹)ᵀ = (M⁻¹)ᵀ * (Xᵀ * M) * M⁻¹ := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hM, Matrix.mul_one]
      _ = X * M⁻¹ := by rw [hXM, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hn : Matrix.fromBlocks (1 : Matrix κ κ F) (0 : Matrix κ κ F) (-C) (1 : Matrix κ κ F)
      ∈ Submonoid.closure (gens F κ) := Submonoid.subset_closure (Or.inl (Or.inr ⟨C, hC, rfl⟩))
  refine ⟨_, mul_mem hn (upper_mem _ hS), fun y => ?_⟩
  have hy : Y *ᵥ (M⁻¹ *ᵥ y) = -(C *ᵥ (X *ᵥ (M⁻¹ *ᵥ y))) + y := by
    have : M *ᵥ (M⁻¹ *ᵥ y) = y := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hM, Matrix.one_mulVec]
    generalize M⁻¹ *ᵥ y = v at this ⊢
    rw [← this, hMdef, Matrix.add_mulVec, ← Matrix.mulVec_mulVec]
    abel
  have hmem : (X *ᵥ (M⁻¹ *ᵥ y), Y *ᵥ (M⁻¹ *ᵥ y)) ∈ L := by rw [key]; exact Subtype.property _
  rw [hy] at hmem
  simpa [← Matrix.mulVec_mulVec, Matrix.fromBlocks_mulVec, Matrix.neg_mulVec] using hmem

end GlobalTheory.AdelicSvN.LagrangianNormalForm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticBlockGeneratorsLagrangianNormalFStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicSvN
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symplecticBlockGenerators_lagrangian_normal_form : ∀ (F : Type) [Field F] (κ : Type) [Fintype κ] [DecidableEq κ] (L : Submodule F ((κ → F) × (κ → F))),
    (∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) → Module.finrank F L = Fintype.card κ →
    ∃ g ∈ Submonoid.closure (gens F κ), ∀ y : κ → F,
      ((g *ᵥ Sum.elim 0 y) ∘ Sum.inl, (g *ᵥ Sum.elim 0 y) ∘ Sum.inr) ∈ L := by
  first | exact @GlobalTheory.AdelicSvN.LagrangianNormalForm.exists_mem_closure | exact GlobalTheory.AdelicSvN.LagrangianNormalForm.exists_mem_closure | (intros; apply GlobalTheory.AdelicSvN.LagrangianNormalForm.exists_mem_closure <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ApplyIdeleMapInfIdeleNegOne
open NumberField IsDedekindDomain

noncomputable section

open Formalism.L2.Host GlobalTheory.UnitaryBC GlobalTheory.CuspRep ReciprocityTheory.Neutral.Bridge.HCFR

namespace GlobalTheory.PolChar

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

omit [IsCMField E] in
theorem continuous_infAdeleMap (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] :
    Continuous (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap K L) :=
  continuous_fst.comp ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.continuous_adeleMap K L).comp
    (Continuous.prodMk_left (0 : FiniteAdeleRing (𝓞 K) K)))

omit [IsCMField E] in
theorem continuous_finAdeleMap (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] :
    Continuous (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteAdeleMap K L) :=
  continuous_snd.comp ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.continuous_adeleMap K L).comp
    (Continuous.prodMk_right (0 : InfiniteAdeleRing K)))

end GlobalTheory.PolChar

namespace GlobalTheory.PolChar

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

open Classical in
theorem pInf_ideleMap_infIdele (v : InfinitePlace (maximalRealSubfield E)) (w : InfinitePlace E) :
    pInf E (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E (infIdele _ v (-1)) : Ad E) w =
      if w.comap (algebraMap (maximalRealSubfield E) E) = v then -1 else 1 := by
  show (InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w))
    (AbsoluteValue.Completion.map (w.comap (algebraMap (maximalRealSubfield E) E)).1 w.1
      (Pi.mulSingle v ((-1 : (v.Completion)ˣ) : v.Completion) (w.comap (algebraMap (maximalRealSubfield E) E)))) = _
  split_ifs with h
  · subst h
    rw [Pi.mulSingle_eq_same]
    simp
  · rw [Pi.mulSingle_eq_of_ne h]
    simp

theorem pFin_ideleMap_infIdele (v : InfinitePlace (maximalRealSubfield E)) :
    pFin E (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E (infIdele _ v (-1)) : Ad E) = 1 :=
  map_one (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteAdeleMap (maximalRealSubfield E) E)

end GlobalTheory.PolChar

namespace GlobalTheory.PolChar

variable {E : Type} [Field E] [NumberField E] [IsCMField E]


open Classical in
def iAt (v : InfinitePlace (maximalRealSubfield E)) : (Cinf E)ˣ where
  val w := if w.comap (algebraMap (maximalRealSubfield E) E) = v then Complex.I else 1
  inv w := if w.comap (algebraMap (maximalRealSubfield E) E) = v then -Complex.I else 1
  val_inv := by
    funext w
    simp only [Pi.mul_apply, Pi.one_apply]
    split_ifs <;> simp
  inv_val := by
    funext w
    simp only [Pi.mul_apply, Pi.one_apply]
    split_ifs <;> simp

theorem apply_ideleMap_infIdele_neg_one (χ : HChar E)
    (hc : ∀ x : (AdeleRing (𝓞 E) E)ˣ, χ.1 (Units.map (conjAd E).toMonoidHom x) = χ.1 x)
    (v : InfinitePlace (maximalRealSubfield E)) :
    χ.1 (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E (infIdele _ v (-1))) = 1 := by
  classical
  have h1 : pInf E (infId E (iAt v)).val = (iAt v).val := by
    change (infEq E).symm (1 - infEq E 1 + infEq E (iAt v).val) = _
    simp
  have h2 : pFin E (infId E (iAt v)).val = 1 := by
    change (1 : Af E) - 0 + 0 = 1
    simp
  have key : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E (infIdele _ v (-1)) =
      infId E (iAt v) * (Units.map (conjAd E).toMonoidHom (infId E (iAt v)))⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq]
    refine Units.ext (ad_ext ?_ ?_)
    · funext w
      change pInf E ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E (infIdele _ v (-1))).val *
        conjAd E (infId E (iAt v)).val) w = pInf E (infId E (iAt v)).val w
      rw [map_mul, Pi.mul_apply, GlobalTheory.ThetaPull.pInf_conjAd, h1, pInf_ideleMap_infIdele]
      change _ * starRingEnd ℂ ((iAt v).val w) = (iAt v).val w
      simp only [iAt]
      split_ifs <;> simp
    · change pFin E ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E (infIdele _ v (-1))).val *
        conjAd E (infId E (iAt v)).val) = pFin E (infId E (iAt v)).val
      rw [map_mul, GlobalTheory.ThetaPull.pFin_conjAd, h2,
        pFin_ideleMap_infIdele, map_one, one_mul]
  rw [key, map_mul, map_inv, hc, mul_inv_cancel]

end GlobalTheory.PolChar

namespace GlobalTheory.PolChar

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem apply_conjAd_of_isAbsPow {χ : HChar E} {u : ℝ} (h : χ.IsAbsPow u) (x : (AdeleRing (𝓞 E) E)ˣ) :
    χ.1 (Units.map (conjAd E).toMonoidHom x) = χ.1 x := by
  have e : χ * GlobalTheory.ThetaPull.thetaChar χ = 1 := GlobalTheory.HeckeUnrTrivial.eq_one_of_val_eq_one _ fun v _ => by
    have h2 := (GlobalTheory.ThetaPull.isAbsPow_thetaChar h).2.1 v
    have h0 : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.2 fun h0 => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    refine Units.ext ?_
    rw [HChar.val_mul, Units.val_mul, h.2.1 v, h2, Units.val_one, ← Complex.cpow_add _ _ h0]
    simp
  have h3 := congrArg (fun c : HChar E => c.1 x) e
  change χ.1 x * (χ.1 (Units.map (conjAd E).toMonoidHom x))⁻¹ = 1 at h3
  exact (mul_inv_eq_one.1 h3).symm

theorem adeleMap_conj_eq (x : AdeleRing (𝓞 E) E) :
    @GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap E E _ _ _ _
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj (maximalRealSubfield E) E).toRingEquiv.toRingHom.toAlgebra x = conjAd E x := by
  letI : Algebra E E := (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj (maximalRealSubfield E) E).toRingEquiv.toRingHom.toAlgebra
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_infiniteAdeleRing_of_numberField_field E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField E
  have key : ∀ k : E, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap E E (algebraMap E (AdeleRing (𝓞 E) E) k) =
      conjAd E (algebraMap E (AdeleRing (𝓞 E) E) k) := by
    intro k
    rw [conjAd_algebraMap]
    exact GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap_algebraMap E E k
  have hsymm : Continuous (infEq E).symm := continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)
  refine Prod.ext ?_ ?_
  · exact congrFun ((InfiniteAdeleRing.denseRange_algebraMap E).equalizer (continuous_infAdeleMap E E)
      ((continuous_infEq E).comp (continuous_star.comp hsymm))
      (funext fun k => congrArg Prod.fst (key k))) x.1
  · exact congrFun ((GlobalTheory.AdeleCharTwist.denseRange_fin (F := E)).equalizer
      (continuous_finAdeleMap E E) (continuous_conjFin _)
      (funext fun k => congrArg Prod.snd (key k))) x.2

theorem ideleConj_eq (x : (AdeleRing (𝓞 E) E)ˣ) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj (maximalRealSubfield E) E x = Units.map (conjAd E).toMonoidHom x :=
  Units.ext (adeleMap_conj_eq x.val)

end GlobalTheory.PolChar

namespace GlobalTheory.PolChar

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def resReal (χ : HChar E) : HChar (maximalRealSubfield E) :=
  ⟨χ.1.comp (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E),
    χ.2.1.comp (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.continuous_ideleMap _ E), fun k =>
      (congrArg χ.1 (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap_principalIdele _ E k)).trans (χ.2.2 _)⟩

theorem resReal_apply (χ : HChar E) (x : (AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E))ˣ) :
    (resReal χ).1 x = χ.1 (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E x) := rfl

theorem resReal_locInf_neg_one {χ : HChar E} {u : ℝ} (h : χ.IsAbsPow u) (v : InfinitePlace (maximalRealSubfield E)) :
    (resReal χ).locInf v (-1) = 1 :=
  apply_ideleMap_infIdele_neg_one χ (apply_conjAd_of_isAbsPow h) v

end GlobalTheory.PolChar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelPlaceDatumOverNumberField
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelPlaceDatumOverNumberField
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LevelDatum

variable {D : D7}

def rowP (W : HSp D) (β : GL (Fin W.rank) (EAf D)) (e : AE D) (x : Fin W.rank → D.host.E) (a : Fin W.rank) : EAf D :=
  toEAf D e * ∑ k, eToEAf D (∑ l, D.sp.cm.sig (x l) * W.gram l k) * β.val k a

theorem rowPairing_add (W : HSp D) (β : GL (Fin W.rank) (EAf D)) (e : AE D) (x y : Fin W.rank → D.host.E) (a : Fin W.rank) :
    rowP W β e (x + y) a = rowP W β e x a + rowP W β e y a := by
  simp only [rowP, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib, mul_add]

theorem rowPairing_zero (W : HSp D) (β : GL (Fin W.rank) (EAf D)) (e : AE D) (a : Fin W.rank) :
    rowP W β e 0 a = 0 := by
  simp only [rowP, Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero, mul_zero]

theorem rowPairing_smul (W : HSp D) (β : GL (Fin W.rank) (EAf D)) (e : AE D) (c : D.host.E) (x : Fin W.rank → D.host.E)
    (a : Fin W.rank) : rowP W β e (c • x) a = eToEAf D (D.sp.cm.sig c) * rowP W β e x a := by
  simp only [rowP, Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc, ← Finset.mul_sum]
  ring

theorem uMat_eq (V W : HSp D) (hV : V.gram = 1) (βV : GL (Fin V.rank) (EAf D)) (β : GL (Fin W.rank) (EAf D)) (e : AE D)
    (X : Fin V.rank → Fin W.rank → D.host.E) (b : Fin V.rank) (a : Fin W.rank) :
    FWT.uMat V W βV β e X b a = ∑ b', (βV⁻¹).val b b' * rowP W β e (X b') a := by
  simp only [FWT.uMat, rowP, hV, inv_one, Matrix.one_mul, Matrix.mul_assoc]
  simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem eToEAf_int (c : 𝓞 D.host.E) : eToEAf D (c : D.host.E) = (oToS D.host.F D.host.E c : Formalism.L2.Herm.intAf D.host.F D.host.E) := rfl

theorem exists_sig (c : 𝓞 D.host.E) : ∃ c' : 𝓞 D.host.E, (c' : D.host.E) = D.sp.cm.sig (c : D.host.E) :=
  ⟨⟨_, (RingOfIntegers.isIntegral_coe c).map (D.sp.cm.sig : D.host.E →+* D.host.E).toIntAlgHom⟩, rfl⟩

theorem rowP_int (W : HSp D) (β : GL (Fin W.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E))
    (hβ : IsSDFrame W β Λ 1) (e : AE D) (P : Finset (Pl D.host.E)) (he : IsIdemSum e P)
    (hP : ∀ PP ∈ P, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal)
    (x : Fin W.rank → D.host.E) (hx : x ∈ latG W 1) (a : Fin W.rank) :
    rowP W β e x a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc, v, hv, rfl⟩ := hx
    rw [rowPairing_smul, rowP, ← mul_assoc, mul_comm _ (toEAf D e)]
    exact mul_mem (GlobalTheory.IdemIntegral.conj_mem_intAf D e P he hP c hc) (GlobalTheory.PairIntegral.pair_mem_intAf D W β Λ hβ v hv a)
  | zero => rw [rowPairing_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [rowPairing_add]; exact add_mem hx hy
  | smul c x _ hx =>
    obtain ⟨c', hc'⟩ := exists_sig c
    rw [show c • x = (c : D.host.E) • x from rfl, rowPairing_smul, ← hc', eToEAf_int]
    exact mul_mem (Subtype.prop _) hx

theorem residue_rowPairing_eq_zero (W : HSp D) (β : GL (Fin W.rank) (EAf D)) (e : AE D) {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    (ι : La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) (a : Fin W.rank)
    (hi : ∀ x, rowP W β e (ι x) a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (J : Ideal (𝓞 D.host.E)) (PP : Pl D.host.E)
    (hJ : ∀ c ∈ J, ∃ c' ∈ PP.asIdeal, (c' : D.host.E) = D.sp.cm.sig (c : D.host.E))
    (x : La) (hx : x ∈ J • (⊤ : Submodule (𝓞 D.host.E) La)) : resS D.host.F PP ⟨_, hi x⟩ = 0 := by
  refine Submodule.smul_induction_on (p := fun x => resS D.host.F PP ⟨_, hi x⟩ = 0) hx (fun c hc y _ => ?_) (fun x y hx hy => ?_)
  · obtain ⟨c', hc', e'⟩ := hJ c hc
    have : (⟨_, hi (c • y)⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = oToS D.host.F D.host.E c' * ⟨_, hi y⟩ := by
      refine Subtype.ext ?_
      change rowP W β e (ι (c • y)) a = eToEAf D (c' : D.host.E) * rowP W β e (ι y) a
      rw [map_smul, show c • ι y = (c : D.host.E) • ι y from rfl, rowPairing_smul, e']
    rw [this, map_mul, resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 hc', zero_mul]
  · have : (⟨_, hi (x + y)⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = ⟨_, hi x⟩ + ⟨_, hi y⟩ := by
      refine Subtype.ext ?_
      change rowP W β e (ι (x + y)) a = rowP W β e (ι x) a + rowP W β e (ι y) a
      rw [map_add (f := _), rowPairing_add]
    rw [this, RingHom.map_add, hx, hy, add_zero]

theorem redM_uMat (V W : HSp D) (hV : V.gram = 1) (βV : GL (Fin V.rank) (EAf D)) (hβ : IsIntM (βV⁻¹).val)
    (β : GL (Fin W.rank) (EAf D)) (e : AE D) (X : Fin V.rank → Fin W.rank → D.host.E)
    (hi : ∀ b a, rowP W β e (X b) a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    IsIntM (FWT.uMat V W βV β e X) ∧ ∀ PP b a, redM PP (FWT.uMat V W βV β e X) b a =
      ∑ b', resS D.host.F PP ⟨_, hβ b b'⟩ * resS D.host.F PP ⟨_, hi b' a⟩ := by
  have h : IsIntM (FWT.uMat V W βV β e X) := fun b a => by
    rw [uMat_eq V W hV]
    exact sum_mem fun b' _ => mul_mem (hβ b b') (hi b' a)
  refine ⟨h, fun PP b a => ?_⟩
  rw [redM, dite_eq_left (h b a)]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [← map_mul, ← map_sum]
  congr 1
  refine Subtype.ext ?_
  rw [AddSubmonoidClass.coe_finsetSum]
  exact uMat_eq V W hV βV β e X b a

theorem omega_congr {a b : ℕ} (Pg Q : Finset (Pl D.host.E)) (r : ℕ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (k : ℤ)
    (y y' : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) (h : ∀ PP, PP ∈ Pg ∨ PP ∈ Q → y PP = y' PP) :
    omegaK Pg y * omegaQ Q r ξ k y = omegaK Pg y' * omegaQ Q r ξ k y' := by
  classical
  have h1 : omegaK Pg y = omegaK Pg y' := by
    unfold omegaK
    refine if_congr (forall₂_congr fun PP hPP => by rw [h PP (Or.inl hPP)]) rfl rfl
  have h2 : omegaQ Q r ξ k y = omegaQ Q r ξ k y' := by
    have e : (∀ PP ∈ Q, LowZero r (y PP) ∧ IsUnit (topL r (y PP)).det) ↔
        ∀ PP ∈ Q, LowZero r (y' PP) ∧ IsUnit (topL r (y' PP)).det :=
      forall₂_congr fun PP hPP => by rw [h PP (Or.inr hPP)]
    unfold omegaQ
    by_cases c : ∀ PP ∈ Q, LowZero r (y PP) ∧ IsUnit (topL r (y PP)).det
    · rw [dite_eq_left c, dite_eq_left (e.1 c)]
      refine Finset.prod_congr rfl fun PP _ => ?_
      have : (c PP.1 PP.2).2.unit = (e.1 c PP.1 PP.2).2.unit := Units.ext (by
        rw [IsUnit.unit_spec, IsUnit.unit_spec, h PP.1 (Or.inr PP.2)])
      rw [this]
    · rw [dite_eq_right c, dite_eq_right (fun c' => c (e.2 c'))]
  rw [h1, h2]

theorem exists_omega_field (Pg Q : Finset (Pl D.host.E)) : ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧
    ∀ {a b : ℕ} (r : ℕ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (k : ℤ)
      (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)), omegaK Pg y * omegaQ Q r ξ k y ∈ M := by
  have hf : ∀ PP : Pl D.host.E, 0 < Nat.card (kP PP)ˣ := fun PP => by
    have : Finite (kP PP) := Ideal.finiteQuotientOfFreeOfNeBot _ PP.ne_bot
    exact Nat.card_pos
  obtain ⟨M, hM, h⟩ := GlobalTheory.Mem.FrameVal.exists_roots (∏ PP ∈ Q, Nat.card (kP PP)ˣ) (Finset.prod_pos fun PP _ => hf PP)
  refine ⟨M, hM, fun r ξ k y => mul_mem ?_ ?_⟩
  · unfold omegaK
    split_ifs
    exacts [one_mem _, zero_mem _]
  · unfold omegaQ
    split_ifs
    · refine prod_mem fun PP _ => zpow_mem (h _ ?_) _
      obtain ⟨u, hu⟩ := Finset.dvd_prod_of_mem (fun PP : Pl D.host.E => Nat.card (kP PP)ˣ) PP.2
      rw [hu, pow_mul, ← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one, one_pow]
    · exact zero_mem _


set_option maxHeartbeats 800000 in
theorem exists_datum (V W : HSp D) (hV : V.gram = 1) (βV : GL (Fin V.rank) (EAf D)) (hβ : IsIntM (βV⁻¹).val)
    (β : GL (Fin W.rank) (EAf D)) (e : AE D) {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    (ι : La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E))
    (hi : ∀ x a, rowP W β e (ι x) a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (J : Ideal (𝓞 D.host.E)) (PP : Pl D.host.E)
    (hJ : ∀ c ∈ J, ∃ c' ∈ PP.asIdeal, (c' : D.host.E) = D.sp.cm.sig (c : D.host.E))
    (x z : Fin V.rank → La) (h : ∀ b, z b - x b ∈ J • (⊤ : Submodule (𝓞 D.host.E) La)) :
    redM PP (FWT.uMat V W βV β e fun b => ι (z b)) = redM PP (FWT.uMat V W βV β e fun b => ι (x b)) := by
  have key : ∀ b' a, resS D.host.F PP ⟨_, hi (z b') a⟩ = resS D.host.F PP ⟨_, hi (x b') a⟩ := fun b' a => by
    have h2 := residue_rowPairing_eq_zero W β e ι a (fun x => hi x a) J PP hJ _ (h b')
    have : (⟨_, hi (z b') a⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = ⟨_, hi (z b' - x b') a⟩ + ⟨_, hi (x b') a⟩ := by
      refine Subtype.ext ?_
      change rowP W β e (ι (z b')) a = rowP W β e (ι (z b' - x b')) a + rowP W β e (ι (x b')) a
      rw [← rowPairing_add, ← LinearMap.map_add (f := _), sub_add_cancel]
    rw [this, RingHom.map_add (f := _), h2, zero_add]
  funext b a
  exact ((redM_uMat V W hV βV hβ β e (fun b => ι (z b)) fun b a => hi (z b) a).2 PP b a).trans
    ((Finset.sum_congr rfl fun b' _ => congrArg _ (key b' a)).trans
      ((redM_uMat V W hV βV hβ β e (fun b => ι (x b)) fun b a => hi (x b) a).2 PP b a).symm)


set_option maxHeartbeats 1000000 in
theorem exists_phi : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.thP_vP → ∀ (i : Fin D.R.m), VStd D i → ∀ (t : T0) (La : Type) [AddCommGroup La] [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)), LatEmb (Wc D i) ι → ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ ∀ M' : IntermediateField ℚ ℂ, M ≤ M' → (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ J : Ideal (𝓞 D.host.E), (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ∀ c ∈ J, ∃ c' ∈ PP.asIdeal, (c' : D.host.E) = D.sp.cm.sig (c : D.host.E)) → ∃ φ : (Fin (Vc D i).rank → La ⧸ (J • ⊤ : Submodule (𝓞 D.host.E) La)) → M', PhiIs R i M'.val.toRingHom t ι (J • ⊤) φ := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hlev hvP i hV t La _ _ ι hι
  obtain ⟨M, hM, hv⟩ := exists_omega_field R.Pg (R.Q t)
  refine ⟨M, hM, fun M' hle hP J hJ => ?_⟩
  obtain ⟨-, e, he, -⟩ := hvP i t
  have hβ := GlobalTheory.StdFrameInv.isIntM_inv D i _ _ hV (hlev.βV i)
  have hi : ∀ x a, rowP (Wc D i) (R.βW i) e (ι x) a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := fun x a =>
    rowP_int _ _ _ (hlev.βW i) e _ he (fun PP h => hP PP (by simpa using h)) _
      (hι.2.le (LinearMap.mem_range_self ι x)) a
  refine ⟨fun q => ⟨_, hle (hv (Wc D i).rank (R.xiR t) (-1) fun PP => redM PP
    (FWT.uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e fun b => ι (q b).out))⟩, e, he, fun x =>
    ⟨(redM_uMat (Vc D i) (Wc D i) hV.1 _ hβ (R.βW i) e (fun b => ι (x b)) fun b a => hi (x b) a).1, ?_⟩⟩
  exact omega_congr _ _ _ _ _ _ _ fun PP hPP => exists_datum (Vc D i) (Wc D i) hV.1 _ hβ (R.βW i) e ι hi J PP (hJ PP hPP) x _
    fun b => (Submodule.Quotient.eq _).1 (Quotient.out_eq _)

end GlobalTheory.LevelDatum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelPlaceDatumOverNumberFieldStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_level_place_datum_over_number_field : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.thP_vP → ∀ (i : Fin D.R.m), VStd D i → ∀ (t : T0) (La : Type) [AddCommGroup La] [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)), LatEmb (Wc D i) ι → ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ ∀ M' : IntermediateField ℚ ℂ, M ≤ M' → (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ J : Ideal (𝓞 D.host.E), (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ∀ c ∈ J, ∃ c' ∈ PP.asIdeal, (c' : D.host.E) = D.sp.cm.sig (c : D.host.E)) → ∃ φ : (Fin (Vc D i).rank → La ⧸ (J • ⊤ : Submodule (𝓞 D.host.E) La)) → M', PhiIs R i M'.val.toRingHom t ι (J • ⊤) φ := by
  first | exact @GlobalTheory.LevelDatum.exists_phi | exact GlobalTheory.LevelDatum.exists_phi | (intros; apply GlobalTheory.LevelDatum.exists_phi <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulVecMemLatGHat
set_option autoImplicit false

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevelUnique

theorem mem_map_prod {O S : Type} [CommRing O] [IsDedekindDomain O] [CommRing S] (f : O →+* S)
    (T : Finset (HeightOneSpectrum O)) {s : S} (h : ∀ P ∈ T, s ∈ P.asIdeal.map f) :
    s ∈ (∏ P ∈ T, P.asIdeal).map f := by
  have e : (∏ P ∈ T, P.asIdeal).map f = ∏ P ∈ T, P.asIdeal.map f := map_prod (Ideal.mapHom f) _ _
  rw [e, Ideal.prod_eq_iInf_of_pairwise_isCoprime (J := fun P : HeightOneSpectrum O => P.asIdeal.map f) fun P _ Q _ hne =>
    (HeightOneSpectrum.isCoprime_of_ne P Q hne).map (Ideal.mapHom f)]
  exact Ideal.mem_iInf.2 fun P => Ideal.mem_iInf.2 fun hP => h P hP

section Res

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem sub_mem_idS {P : Pl E} {s t : Formalism.L2.Herm.intAf F E} (h : resS F P s = resS F P t) : s - t ∈ idS F P.asIdeal :=
  Ideal.Quotient.eq.1 ((RingEquiv.ofBijective (cmpS F P.asIdeal) (cmpS_bij (F := F) P.asIdeal P.ne_bot)).symm.injective h)

theorem exists_matrix (T : Finset (Pl E)) {J : Ideal (𝓞 E)} {M : ℕ}
    (hJ : (∏ P ∈ T, P.asIdeal) * J = Ideal.span {(M : 𝓞 E)}) {y y' : GL (Fin n) (Formalism.L2.Herm.intAf F E)}
    (h : ∀ P ∈ T, Formalism.UG.bc (resS F P) y = Formalism.UG.bc (resS F P) y') {b : 𝓞 E} (hb : b ∈ J) :
    ∃ s : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E), oToS F E b • (y.1 - y'.1) = M • s := by
  have key : ∀ i j, ∃ c, oToS F E b * (y.1 i j - y'.1 i j) = M • c := by
    intro i j
    have h1 : y.1 i j - y'.1 i j ∈ (∏ P ∈ T, P.asIdeal).map (oToS F E) :=
      mem_map_prod _ T fun P hP => sub_mem_idS (congrArg (fun g : GL (Fin n) (kP P) => g.1 i j) (h P hP))
    have h2 := Ideal.mul_mem_mul h1 (Ideal.mem_map_of_mem (oToS F E) hb)
    rw [← Ideal.map_mul, hJ, Ideal.map_span, Set.image_singleton, map_natCast, Ideal.mem_span_singleton'] at h2
    obtain ⟨c, hc⟩ := h2
    exact ⟨c, by rw [mul_comm, ← hc, nsmul_eq_mul, mul_comm]⟩
  choose c hc using key
  exact ⟨Matrix.of c, Matrix.ext fun i j => hc i j⟩

end Res

theorem conj_mulVec_mem {R : Type} [CommRing R] {n : ℕ} (S : Subring R) (β : GL (Fin n) R) (s : Matrix (Fin n) (Fin n) S)
    (z : Fin n → R) (hz : ∀ j, ((β⁻¹).1 *ᵥ z) j ∈ S) (i : Fin n) :
    ((β⁻¹).1 *ᵥ ((β.1 * s.map S.subtype * (β⁻¹).1) *ᵥ z)) i ∈ S := by
  rw [Matrix.mulVec_mulVec, ← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul, ← Matrix.mulVec_mulVec]
  generalize (β⁻¹).1 *ᵥ z = w at hz
  exact Subring.sum_mem S (t := Finset.univ) (f := fun j => (s i j : R) * w j) fun j _ => mul_mem (s i j).2 (hz j)

theorem conj_smul_sub {R : Type} [CommRing R] {n : ℕ} (S : Subring R) (β : GL (Fin n) R) {y y' : GL (Fin n) S}
    {s : Matrix (Fin n) (Fin n) S} {b : S} {M : ℕ} (h : b • (y.1 - y'.1) = M • s) :
    (b : R) • ((β * Formalism.UG.bc S.subtype y * β⁻¹).1 - (β * Formalism.UG.bc S.subtype y' * β⁻¹).1) =
      M • (β.1 * s.map S.subtype * (β⁻¹).1) := by
  have e : (b : R) • ((Formalism.UG.bc S.subtype y).1 - (Formalism.UG.bc S.subtype y').1) = M • s.map S.subtype := by
    ext i j
    have := congrArg (fun m : Matrix (Fin n) (Fin n) S => S.subtype (m i j)) h
    simp only [Matrix.smul_apply, map_nsmul, smul_eq_mul, map_mul, Matrix.sub_apply, map_sub] at this
    exact this
  rw [Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul, ← sub_mul, ← mul_sub, ← smul_mul_assoc, ← mul_smul_comm, e,
    mul_smul_comm, smul_mul_assoc]

theorem exists_matrix_hat {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    {β : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} {Λ : Submodule (𝓞 E) (Fin n → E)} (hfr : IsFrame β Λ)
    (T : Finset (Pl E)) {J : Ideal (𝓞 E)} {M : ℕ} (hJ : (∏ P ∈ T, P.asIdeal) * J = Ideal.span {(M : 𝓞 E)})
    {x x' : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} (hx : x ∈ St β) (hx' : x' ∈ St β)
    (h : ∀ P ∈ T, redFn β P x = redFn β P x') {b : 𝓞 E} (hb : b ∈ J)
    {K K' : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F ⊗[F] E)}
    (hK : ∀ i j, x.1 i j = Algebra.TensorProduct.comm F _ E (K i j))
    (hK' : ∀ i j, x'.1 i j = Algebra.TensorProduct.comm F _ E (K' i j)) :
    ∃ N : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F ⊗[F] E),
      (∀ z ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)), N *ᵥ z ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E))) ∧
        ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (b : E)) • (K - K') = M • N := by
  obtain ⟨y, rfl⟩ := hx
  obtain ⟨y', rfl⟩ := hx'
  simp only [redFn_frGL] at h
  obtain ⟨s, hs⟩ := exists_matrix T hJ h hb
  have e := conj_smul_sub _ β hs
  have hN := fun z hz => (hfr _).2 (conj_mulVec_mem _ β s z ((hfr z).1 hz))
  generalize β.1 * s.map (Formalism.L2.Herm.intAf F E).subtype * (β⁻¹).1 = N at e hN
  refine ⟨N.map (Algebra.TensorProduct.comm F _ E).symm, fun z hz => ?_, Matrix.ext fun i j => ?_⟩
  · have h4 := GlobalTheory.PrincInLevel.swap_symm_mem_hat Λ _ (hN _ (GlobalTheory.PrincInLevel.swap_mem_hatL Λ z hz))
    convert h4 using 1
    ext i
    simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  · apply (Algebra.TensorProduct.comm F _ E).injective
    rw [Matrix.smul_apply, Matrix.smul_apply, map_nsmul, Matrix.map_apply, AlgEquiv.apply_symm_apply, smul_eq_mul, map_mul,
      Matrix.sub_apply, map_sub, ← hK, ← hK']
    exact congrFun (congrFun e i) j

variable {D : D7}

theorem mulVec_mem_latGHat {V : HSp D} (N : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E))
    (h : ∀ z ∈ latHat V, N *ᵥ z ∈ latHat V) : ∀ z ∈ latGHat V 1, N *ᵥ z ∈ latGHat V 1 := by
  intro z hz
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨a, ha, _, ⟨z, hz, rfl⟩, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨a, ha, _, ⟨_, h z hz, rfl⟩, ?_⟩
    rw [GlobalTheory.Member.LatMove.fin_one, GlobalTheory.Member.LatMove.fin_one]
    exact Matrix.mulVec_smul N ((1 : Af D.host.F) ⊗ₜ[D.host.F] a) z
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.mulVec_neg]; exact neg_mem hx

theorem exists_cong {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hβ : IsSDFrame V β Λ 1) (T : Finset (Pl D.host.E)) {J : Ideal (𝓞 D.host.E)} {M : ℕ}
    (hJ : (∏ P ∈ T, P.asIdeal) * J = Ideal.span {(M : 𝓞 D.host.E)}) {k k' : GA D V}
    (hk : Lev.finE V k ∈ St β) (hk' : Lev.finE V k' ∈ St β)
    (h : ∀ P ∈ T, redFn β P (Lev.finE V k) = redFn β P (Lev.finE V k')) {b : 𝓞 D.host.E} (hb : b ∈ J) :
    ∀ z ∈ latGHat V 1, ∃ w ∈ latGHat V 1,
      ((1 : Af D.host.F) ⊗ₜ[D.host.F] (b : D.host.E)) • ((finHom V k).1 *ᵥ z - (finHom V k').1 *ᵥ z) = M • w := by
  have hl : latHat V = GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E)) := by
    rw [GlobalTheory.PrincInLevel.eq_latC hβ]; exact (GlobalTheory.Member.latHat_eq_hat_and_gram D V).1
  obtain ⟨c, hfr, -⟩ := hβ
  obtain ⟨N, hN, e⟩ := exists_matrix_hat hfr T hJ hk hk' h hb (K := (finHom V k).1) (K' := (finHom V k').1)
    (fun _ _ => rfl) (fun _ _ => rfl)
  rw [← hl] at hN
  intro z hz
  refine ⟨_, mulVec_mem_latGHat _ hN z hz, ?_⟩
  rw [← Matrix.sub_mulVec, ← Matrix.smul_mulVec, e, Matrix.smul_mulVec]

theorem redFn_eq_of_lift {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank} (hr : V.rank = L.r)
    {g : G0 L.Pg L.r} {k k' : GA D V} (hk : Lev.IsLevelLift V β L g k) (hk' : Lev.IsLevelLift V β L g k') :
    ∀ P ∈ L.Pg, redFn β P (Lev.finE V k) = redFn β P (Lev.finE V k') := by
  intro P hP
  have e : upperLeftBlock L.hr (redFn β P (Lev.finE V k)) = upperLeftBlock L.hr (redFn β P (Lev.finE V k')) :=
    congrFun (hk.2.2.trans hk'.2.2.symm) ⟨P, hP⟩
  have e' := congrArg Units.val e
  rw [upper_block_val_submatrix _ (blockTri_blkOf_le _ _ (parLev_g hk.2.1 hP)),
    upper_block_val_submatrix _ (blockTri_blkOf_le _ _ (parLev_g hk'.2.1 hP))] at e'
  exact Units.ext (Matrix.ext fun i j => congrFun (congrFun e' (Fin.cast hr i)) (Fin.cast hr j))

theorem sub_eq_nsmul {R : Type} [CommRing R] {n : ℕ} {K K' : Matrix (Fin n) (Fin n) R} {t : R} {x x' z w₁ w₂ w₃ : Fin n → R}
    {M : ℕ} (e₁ : x - K *ᵥ (t • z) = M • w₁) (e₂ : x' - K' *ᵥ (t • z) = M • w₂) (e₃ : t • (K *ᵥ z - K' *ᵥ z) = M • w₃) :
    x - x' = M • (w₁ - w₂ + w₃) := by
  rw [smul_add, smul_sub M, ← e₁, ← e₂, ← e₃, Matrix.mulVec_smul, Matrix.mulVec_smul, smul_sub]
  abel

theorem sub_mem_of_approx {V : HSp D} {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    {ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)} (hι : LatEmb V ι) {I J : Ideal (𝓞 D.host.E)} {M : ℕ} (hM : 0 < M)
    (hI : (M : 𝓞 D.host.E) ∈ I) (hIJ : I ⊔ J = ⊤)
    {K K' : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)}
    (h : ∀ b ∈ J, ∀ z ∈ latGHat V 1, ∃ w ∈ latGHat V 1,
      ((1 : Af D.host.F) ⊗ₜ[D.host.F] ((b : 𝓞 D.host.E) : D.host.E)) • (K *ᵥ z - K' *ᵥ z) = M • w)
    {f f' : La →ₗ[𝓞 D.host.E] La}
    (hf : ∀ a ∈ J • (⊤ : Submodule (𝓞 D.host.E) La), ∃ w ∈ latGHat V 1,
      finVec V (ι (f a)) - K *ᵥ finVec V (ι a) = M • w)
    (hf' : ∀ a ∈ J • (⊤ : Submodule (𝓞 D.host.E) La), ∃ w ∈ latGHat V 1,
      finVec V (ι (f' a)) - K' *ᵥ finVec V (ι a) = M • w) (a : La) :
    f a - f' a ∈ I • (⊤ : Submodule (𝓞 D.host.E) La) := by
  have hm : ∀ a, ι a ∈ latG V 1 := fun a => hι.2 ▸ LinearMap.mem_range_self ι a
  have h5 := (GlobalTheory.Member.latG_lattice_and_completion D V 1).2.2.2.2.1
  obtain ⟨u, hu, b, hb, hub⟩ := Submodule.mem_sup.1 (hIJ ▸ Submodule.mem_top : (1 : 𝓞 D.host.E) ∈ I ⊔ J)
  rw [← one_smul (𝓞 D.host.E) (f a - f' a), ← hub, add_smul]
  refine add_mem (Submodule.smul_mem_smul hu Submodule.mem_top) ?_
  obtain ⟨w₁, hw₁, e₁⟩ := hf (b • a) (Submodule.smul_mem_smul hb Submodule.mem_top)
  obtain ⟨w₂, hw₂, e₂⟩ := hf' (b • a) (Submodule.smul_mem_smul hb Submodule.mem_top)
  obtain ⟨w₃, hw₃, e₃⟩ := h b hb _ ((GlobalTheory.Member.LatMove.mem_lat_iff V 1 _).1 (hm a))
  have e₀ : finVec V (ι (b • a)) = ((1 : Af D.host.F) ⊗ₜ[D.host.F] (b : D.host.E)) • finVec V (ι a) := by
    rw [map_smul]; exact GlobalTheory.AdLat.Tower.fv_smul b (ι a)
  have e₄ : finVec V (ι (b • (f a - f' a))) = finVec V (ι (f (b • a))) - finVec V (ι (f' (b • a))) := by
    rw [smul_sub, ← map_smul f, ← map_smul f', map_sub]; exact GlobalTheory.AdLat.Tower.fv_sub _ _
  have e₅ : finVec V (ι (b • (f a - f' a))) = M • (w₁ - w₂ + w₃) := by
    rw [e₀] at e₁ e₂
    exact e₄.trans (sub_eq_nsmul e₁ e₂ e₃)
  obtain ⟨⟨v, hv⟩, ev⟩ := GlobalTheory.AdLat.Tower.exists_div (F := D.host.F) (M := latG V 1)
    (fun v => h5 ▸ (GlobalTheory.Member.LatMove.mem_lat_iff V 1 v).symm) hM ⟨_, hm (b • (f a - f' a))⟩
    (h5 ▸ add_mem (sub_mem hw₁ hw₂) hw₃) e₅
  obtain ⟨c, rfl⟩ : v ∈ LinearMap.range ι := hι.2 ▸ hv
  have e₆ : b • (f a - f' a) = (M : 𝓞 D.host.E) • c := by
    apply hι.1
    rw [Nat.cast_smul_eq_nsmul, map_nsmul]
    exact congrArg Subtype.val ev
  rw [e₆]
  exact Submodule.smul_mem_smul hI Submodule.mem_top

theorem levUnique (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (hL : R.toLevCh.Is A.μ0) (hT : LawsJ T)
    (hM : T.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal) (i : Fin D.R.m) : GlobalTheory.OneMapAllCompare.LevUnique T R i := by
  intro lev lev' h h' g a
  obtain ⟨k, hk, hf⟩ := h g
  obtain ⟨k', hk', hf'⟩ := h' g
  have hp : T.Q.l.Mb * Mfr T.Q.l = Ideal.span {((T.Q.l.M : ℕ) : 𝓞 D.host.E)} := T.Q.l.prod
  have hp' : (∏ PP ∈ R.Pg, PP.asIdeal) * Mfr T.Q.l = Ideal.span {((T.Q.l.M : ℕ) : 𝓞 D.host.E)} := by rw [← hM]; exact hp
  have hI : ((T.Q.l.M : ℕ) : 𝓞 D.host.E) ∈ T.Q.l.Mb :=
    (hp.ge.trans (Ideal.mul_le_inf.trans inf_le_left)) (Ideal.mem_span_singleton_self _)
  have hc : T.Q.l.Mb ⊔ Mfr T.Q.l = ⊤ := T.Q.l.coprime
  have hr := redFn_eq_of_lift (L := R.datWp i R.triv) (rank_Wc i) hk hk'
  have hcong := fun b hb => exists_cong (b := b) (hL.βW i) R.Pg hp' (parLev_St hk.2.1) (parLev_St hk'.2.1) hr hb
  exact sub_mem_of_approx (GlobalTheory.LevelAction.latEmb_iotaW T hT i) (lt_of_lt_of_le (by norm_num) T.Q.l.three_le) hI hc hcong hf hf' a

end GlobalTheory.LevelUnique
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemGroupOfCongruent
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PrincCore


set_option maxHeartbeats 1000000 in
theorem mem_group_of_congruent : ∀ (D : D7) (T : Core D), LawsM T → ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → ∀ k (γ : GL (Fin D.R.r) D.host.E), ReciprocityTheory.ChartRestriction.G.FD.IsUStab ((T.U j σ).X k).Gm ((T.U j σ).X k).Λ γ → (∀ v ∈ ((T.U j σ).X k).Λ, ∃ u ∈ ((T.U j σ).X k).Λ, Matrix.mulVec (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) v = v + T.Q.l.M • u) → γ ∈ ((T.U j σ).X k).Γ := by
  intro D T h j hj σ hσ k γ hγ hc0
  have hc : ∀ x ∈ ((T.U j σ).X k).Λ, ∃ y ∈ ((T.U j σ).X k).Λ,
      Matrix.mulVec (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) x - x = (T.Q.l.M : D.host.E) • y := by
    intro x hx
    obtain ⟨y, hy, e⟩ := hc0 x hx
    exact ⟨y, hy, by rw [e, add_sub_cancel_left, Nat.cast_smul_eq_nsmul]⟩
  obtain ⟨hgood, hA, -, -, -, -, hnum⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q h.pins
  have hr : 0 < D.R.r := (hnum j hj).2.1
  have hM : 3 ≤ T.Q.l.M := le_trans (hgood 2 Nat.prime_two) (Nat.div_le_self _ _)
  obtain ⟨γ', hγ', u, n, hn, hu, he⟩ := GlobalTheory.unf_group_contains_congruence_upto_rootsOfUnity _ _ _ _ _ _ σ _
    (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) (h.unf j hj σ hσ) hA hr k γ hγ hc
  obtain ⟨th, hrk, hth, hD⟩ := h.dictU j hj σ hσ
  have hK := h.levelK j hj σ hσ
  rw [← h.pins.2.1.1] at hK
  have h1 := root_eq_one (T.V j σ) hrk hr (T.U j σ).X (T.dict j σ) (T.mu j σ) (T.Kf j σ) th hth hD
    (h.muUnit j hj σ hσ) _ hM hK k γ γ' hγ' hc u n hn hu he
  rw [h1, one_smul] at he
  exact Units.ext he ▸ hγ'

end GlobalTheory.PrincCore
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LastPosWtAOfPins
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory


set_option maxHeartbeats 1000000 in
theorem lastPos_wtA_of_pins : ∀ (D : D7) (Q : Par D), Q.Pins → ∀ j, InR D j → ∀ w : WeightFamilies.Wt D j,
    w.LastPos → Formalism.L2.Pj.LastPos (Q.Dw j) (wtA w) := by
  intro D Q h j hj w hw τ hτ hm
  obtain ⟨t, rfl⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.exists_tau_of_inPsi Q h.1 τ hτ
  have hmult : (Q.Dw j).mult (DV.tauEmb D t) = (D.R.sigW j).1 := by
    unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.mult
    have hτ' : (DV.tauEmb D t) (Q.H.rt : D.host.E) = Q.H.rt0 := hτ
    rw [if_pos hτ']
    exact (h.2.2.2 j hj).1
  rw [hmult] at hm ⊢
  have h1 : 1 ≤ w.aP t ⟨(D.R.sigW j).1 - 1, by omega⟩ :=
    hw t _ (by show (D.R.sigW j).1 - 1 + 1 = _; omega)
  have h2 : ext0 (w.aP t) ((D.R.sigW j).1 - 1) = w.aP t ⟨(D.R.sigW j).1 - 1, by omega⟩ := by
    unfold ext0
    rw [dite_eq_left (by omega)]
  unfold wtA
  classical
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ t))
  simp only [if_true]
  omega

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageIdealEqConeIdealOfGeneric
set_option autoImplicit false

namespace GlobalTheory.CompHt

open MvPolynomial NumberField Module GlobalTheory.ChowHt GlobalTheory.CompHt
open AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G GlobalTheory.Twist GlobalTheory.Adelic
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

theorem form_eq_zero_of_generic {K : Type} [Field K] (S : LinSys K) [IsReduced S.Y] {η : S.Y}
    (hη : IsGenericPoint η Set.univ) {d : ℕ} {g : MvPolynomial (Fin S.N) K} (hg : g.IsHomogeneous d)
    (h : η ∉ nonzeroLocus (S.form hg)) : S.form hg = 0 := by
  refine zglobal_ext fun i => ?_
  rw [zfun_zero, ← basicOpen_eq_bot_iff, basicOpen_zfun, eq_bot_iff]
  intro y hy
  exact (h ((hη.mem_open_set_iff (nonzeroLocus (S.form hg)).isOpen).2 ⟨y, trivial, hy.2⟩)).elim


attribute [local instance] MvPolynomial.gradedAlgebra in
theorem imageIdeal_eq_coneIdeal_of_generic (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (S : LinSys K)
    [IsIntegral S.Y] (x : S.Pt Ω) (hx : IsGenericPoint (ptOf x.1) Set.univ) (a : Ω) (y : Fin S.N → Ω) (ha : a ≠ 0)
    (h : S.coords x.1 = a • y) : S.imageIdeal = coneIdeal K y := by
  rw [← coneIdeal_smul ha y, ← h]
  have key : ∀ {d : ℕ} {g : MvPolynomial (Fin S.N) K} (_ : g.IsHomogeneous d),
      g ∈ S.imageIdeal ↔ g ∈ coneIdeal K (S.coords x.1) := fun {d g} hg => by
    rw [mem_coneIdeal_of_isHomogeneous _ hg, aeval_def,
      ← congrArg (fun φ => eval₂ φ (S.coords x.1) g) (LinSys.baseHom_ptOver x)]
    refine ⟨S.eval₂_coords_eq_zero x.1, fun h0 => (S.mem_imageIdeal_iff hg).2
      (form_eq_zero_of_generic S hx hg fun hm => ?_)⟩
    exact (S.powVal_ne_zero_iff x.1 _).2 hm ((S.powVal_form x.1 hg).trans h0)
  ext g
  rw [S.isHomogeneous_imageIdeal.mem_iff, (isHomogeneous_coneIdeal (K := K) (S.coords x.1)).mem_iff]
  exact forall_congr' fun d => key (DirectSum.decompose (homogeneousSubmodule (Fin S.N) K) g d).2

end GlobalTheory.CompHt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EncardComplexPointsFiniteEtaleFreeEqRank
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EncardComplexPointsFiniteEtaleFreeEqRank
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Points
open scoped TensorProduct

namespace GlobalTheory.EtaleComplexPoints

theorem encard_complexPoints_eq_rank : ∀ {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (δ : ℕ), f.Etale → f.Finite → (letI := f.toAlgebra; Module.Free A B ∧ Module.finrank A B = δ) → ∀ φ : A →+* ℂ, {ψ : B →+* ℂ | ψ.comp f = φ}.encard = (δ : ℕ∞) := by
  intro A B _ _ f δ hf hfin hfree φ
  letI := f.toAlgebra
  letI := φ.toAlgebra
  obtain ⟨hF, hrk⟩ := hfree
  have hEt : Algebra.Etale A B := RingHom.etale_algebraMap.1 hf
  have hMF : Module.Finite A B := hfin
  have hFE : Algebra.FormallyEtale ℂ (ℂ ⊗[A] B) := inferInstance
  have hcard := GlobalTheory.natCard_algHom_eq_finrank_of_etale_baseChange A B ℂ
  have hto (ψ : {ψ : B →+* ℂ | ψ.comp f = φ}) (a : A) : ψ.1 (algebraMap A B a) = algebraMap A ℂ a := by
    have := congrArg (fun g : A →+* ℂ => g a) ψ.2
    simpa [RingHom.algebraMap_toAlgebra] using this
  have hinv (g : B →ₐ[A] ℂ) : (g : B →+* ℂ).comp f = φ := by
    ext a
    simpa [RingHom.algebraMap_toAlgebra] using g.commutes a
  let e : {ψ : B →+* ℂ | ψ.comp f = φ} ≃ (B →ₐ[A] ℂ) :=
    { toFun := fun ψ => { ψ.1 with commutes' := hto ψ }
      invFun := fun g => ⟨g.toRingHom, hinv g⟩
      left_inv := fun ψ => rfl
      right_inv := fun g => rfl }
  have hfinite : Finite (B →ₐ[A] ℂ) :=
    Finite.of_equiv _ (AlgHom.liftEquiv A ℂ B ℂ).symm
  rw [Set.encard, ENat.card_congr e, ENat.card_eq_coe_natCard, hcard, hrk]

end GlobalTheory.EtaleComplexPoints
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EncardComplexPointsFiniteEtaleFreeEqRankStatement
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Points
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.encard_complexPoints_finiteEtaleFree_eq_rank : ∀ {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (δ : ℕ), f.Etale → f.Finite → (letI := f.toAlgebra; Module.Free A B ∧ Module.finrank A B = δ) → ∀ φ : A →+* ℂ, {ψ : B →+* ℂ | ψ.comp f = φ}.encard = (δ : ℕ∞) := by
  first | exact @GlobalTheory.EtaleComplexPoints.encard_complexPoints_eq_rank | exact GlobalTheory.EtaleComplexPoints.encard_complexPoints_eq_rank | (intros; apply GlobalTheory.EtaleComplexPoints.encard_complexPoints_eq_rank <;> assumption)
end
end
