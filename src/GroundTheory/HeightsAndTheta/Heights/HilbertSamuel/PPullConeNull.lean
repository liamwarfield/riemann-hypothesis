module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenNear
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwoBlockCycleExpand
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ExistsMPrimeFiltration
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.CechHcSubsingletonOfBij

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullConeNull
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Cardinal

noncomputable section

theorem exists_ringHom_complex_ker_eq_of_isPrime {σ : Type} [Finite σ] (P : Ideal (MvPolynomial σ ℚ))
    [P.IsPrime] : ∃ φ : MvPolynomial σ ℚ →+* ℂ, ∀ f, φ f = 0 ↔ f ∈ P := by
  let Q := MvPolynomial σ ℚ ⧸ P
  let F := FractionRing Q
  have : CharZero F := charZero_of_injective_algebraMap (R := ℚ) (algebraMap ℚ F).injective
  have hcard : #F ≤ 𝔠 := by
    rw [Cardinal.mk_fractionRing]
    refine (Cardinal.mk_le_of_surjective (Ideal.Quotient.mk_surjective (I := P))).trans ?_
    refine MvPolynomial.cardinalMk_le_max.trans ?_
    exact max_le (max_le (Cardinal.mk_le_aleph0.trans aleph0_le_continuum)
      (Cardinal.mk_le_aleph0.trans aleph0_le_continuum)) aleph0_le_continuum
  obtain ⟨ψ⟩ := exists_ringHom_complex_of_charZero F hcard
  refine ⟨(ψ.comp (algebraMap Q F)).comp (Ideal.Quotient.mk P), fun f => ?_⟩
  have hi : Function.Injective (ψ.comp (algebraMap Q F)) :=
    ψ.injective.comp (IsFractionRing.injective Q F)
  rw [RingHom.comp_apply, map_eq_zero_iff _ hi, Ideal.Quotient.eq_zero_iff_mem]

theorem PullConeNull.proof : PullConeNull.Statement := by
  classical
  intro K _ ι _ Ω _ y D L hL
  set I := coneNullIdeal y L

  have hrad : ∀ c : ∀ k, ι k, (∏ k, (X ⟨k, c k⟩ : MvPolynomial (Σ k, ι k) ℚ)) ∈ I.radical := by
    intro c
    rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
    rintro (P : Ideal (MvPolynomial (Σ k, ι k) ℚ)) ⟨hIP, hP⟩
    obtain ⟨φ, hker⟩ := exists_ringHom_complex_ker_eq_of_isPrime P
    let z : (Σ k, ι k) → ℂ := fun p => φ (X p)
    have hev : ∀ f : MRing ι, eval z (map (Int.castRingHom ℂ) f) = φ (map (Int.castRingHom ℚ) f) := by
      intro f
      have h : (eval z).comp (map (Int.castRingHom ℂ)) = φ.comp (map (Int.castRingHom ℚ)) := by
        refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
        · exact RingHom.congr_fun (RingHom.ext_int (((eval z).comp (map (Int.castRingHom ℂ))).comp C)
            ((φ.comp (map (Int.castRingHom ℚ))).comp C)) r
        · simp [z]
      exact RingHom.congr_fun h f
    by_contra hc
    have hz : z ∈ mcPts (mCoordIdeal y) := by
      refine ⟨fun k => ⟨c k, fun h0 => hc ?_⟩, fun f hf => ?_⟩
      · rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
        exact Ideal.mul_mem_right _ P ((hker _).mp h0)
      · rw [hev, hker]
        exact hIP (Ideal.subset_span (Or.inl ⟨f, hf, rfl⟩))
    obtain ⟨j, hj⟩ := hL z hz
    apply hj
    rw [hev, hker]
    exact hIP (Ideal.subset_span (Or.inr ⟨j, rfl⟩))
  choose n hn using fun c => Ideal.mem_radical_iff.mp (hrad c)
  refine ⟨Finset.univ.sup n, fun c => ?_⟩
  have hle : n c ≤ Finset.univ.sup n := Finset.le_sup (Finset.mem_univ c)
  rw [← Nat.add_sub_cancel' hle, pow_add]
  exact I.mul_mem_right _ (hn c)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullFormsGeneric
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial

noncomputable section

namespace PullFormsGeneric

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem aeval_mem (F : IntermediateField ℚ Ω) (w : (Σ k, ι k) → Ω) (hw : ∀ p, w p ∈ F) (f : MRing ι) :
    aeval w f ∈ F := by
  induction f using MvPolynomial.induction_on with
  | C a => rw [aeval_C, algebraMap_int_eq, eq_intCast]; exact intCast_mem F a
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p q hp => rw [map_mul, aeval_X]; exact mul_mem hp (hw q)


omit [CharZero Ω] in
theorem aeval_scale {g : MRing ι} {d : K → ℕ} (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g d) (y : (Σ k, ι k) → Ω) (t : K → Ω) :
    aeval (fun p => y p * t p.1) g = aeval y g * ∏ k, t k ^ d k := by
  have h := congrArg (MvPolynomial.eval t) (ProjLine.mConeMap_eq_of_isMultiHomog y hg)
  rw [map_mul, eval_C, map_prod] at h
  simp only [map_pow, eval_X] at h
  rw [← h, mConeMap, aeval_def, aeval_def, eval₂_comp_left]
  congr 1
  · exact RingHom.ext_int _ _
  · funext p
    simp

theorem blockFnField_eq_top {y : (Σ k, ι k) → Ω} (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (hB : Birational y) : blockFnField y = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨d, g, h, hg, hh, hh0, hgh⟩ := hB x
  set t : K → Ω := fun k => (y ⟨k, c k⟩)⁻¹
  have ht : ∏ k, t k ^ d k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (inv_ne_zero (hc k))
  have hw : ∀ p, y p * t p.1 ∈ blockFnField y := fun p =>
    IntermediateField.subset_adjoin _ _ ⟨p, ⟨p.1, c p.1⟩, rfl, by simp [t, div_eq_mul_inv]⟩
  have hx : x = aeval (fun p => y p * t p.1) g / aeval (fun p => y p * t p.1) h := by
    rw [aeval_scale hg, aeval_scale hh, hgh, mul_div_mul_right _ _ ht, mul_div_cancel_right₀ _ hh0]
  rw [hx]
  exact div_mem (aeval_mem _ _ hw g) (aeval_mem _ _ hw h)

theorem trdeg_eq {y : (Σ k, ι k) → Ω} {D : ℕ} (hA : IsArithVar (mCoordIdeal y) (D + 1))
    (hB : Birational y) : Algebra.trdeg ℚ Ω = D := by
  obtain ⟨_, ⟨_, _, hrel⟩, _, hdim⟩ := hA
  obtain ⟨c, hc⟩ := CoordArithOfFnField.nonzero_of_relevant y hrel
  rw [CoordArithOfFnField.dim_eq y c hc] at hdim
  have h1 : (Algebra.trdeg ℤ (blockFnField y)).toENat = D := by
    generalize (Algebra.trdeg ℤ (blockFnField y)).toENat = n at hdim ⊢
    induction n using ENat.recTopCoe with
    | top =>
      exfalso
      simp only [top_add] at hdim
      norm_cast at hdim
    | coe n =>
      norm_cast at hdim ⊢
      omega
  rw [Cardinal.toENat_eq_natCast] at h1
  have hE : blockFnField y ≃ₐ[ℤ] Ω :=
    ((IntermediateField.equivOfEq (blockFnField_eq_top c hc hB)).trans
      IntermediateField.topEquiv).toRingEquiv.toIntAlgEquiv
  have h2 : Algebra.trdeg ℤ Ω = D := by rw [← hE.trdeg_eq]; convert h1
  have : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic _ (nonZeroDivisors ℤ)
  rw [← h2, ← trdeg_add_eq ℤ ℚ (A := Ω), trdeg_eq_zero (R := ℤ) (A := ℚ), zero_add]


omit [CharZero Ω] in
theorem exists_ne_zero {y : (Σ k, ι k) → Ω} {D : ℕ} {e : K → ℕ} {L : Fin (D + 1) → MRing ι}
    (hA : IsArithVar (mCoordIdeal y) (D + 1)) (hL : ∀ j, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (L j) e)
    (hz : ∀ z ∈ mcPts (mCoordIdeal y), ∃ j, eval z (map (Int.castRingHom ℂ) (L j)) ≠ 0) :
    ∃ j, aeval y (L j) ≠ 0 := by
  have hne : ¬ (⊤ : Ideal (MRing ι)) ≤ mCoordIdeal y := fun h =>
    (RingHom.ker_isPrime (mConeMap y)).ne_top (top_le_iff.mp h)
  obtain ⟨z, hzP, -⟩ := exists_mcPts_not_mem_mcPts hA hne
  obtain ⟨j, hj⟩ := hz z hzP
  refine ⟨j, fun h0 => hj (hzP.2 _ ?_)⟩
  change mConeMap y (L j) = 0
  rw [ProjLine.mConeMap_eq_of_isMultiHomog y (hL j), h0, map_zero, zero_mul]

def dehom {D : ℕ} (j₀ : Fin (D + 1)) (F : MvPolynomial (Fin (D + 1)) ℚ) : MvPolynomial {i // i ≠ j₀} ℚ :=
  bind₁ (fun i => if h : i = j₀ then 1 else X ⟨i, h⟩) F

omit [Field Ω] [CharZero Ω] in
theorem aeval_dehom {A : Type} [CommRing A] [Algebra ℚ A] {D : ℕ} (j₀ : Fin (D + 1))
    (F : MvPolynomial (Fin (D + 1)) ℚ) (u : {i // i ≠ j₀} → A) :
    aeval u (dehom j₀ F) = aeval (fun i => if h : i = j₀ then 1 else u ⟨i, h⟩) F := by
  rw [dehom, aeval_bind₁]
  refine congrArg (fun f => aeval f F) (funext fun i => ?_)
  split_ifs <;> simp

end PullFormsGeneric


open PullFormsGeneric in
theorem PullFormsGeneric.proof (hR : PullRatiosAlgebraic.Statement) : PullFormsGeneric.Statement := by
  intro K _ ι _ Ω _ _ y D e L hA hB he hL hz d F hF h0
  classical
  obtain ⟨j₀, hj₀⟩ := exists_ne_zero hA hL hz
  set a := aeval y (L j₀)
  set r : {i // i ≠ j₀} → Ω := fun i => aeval y (L i.1) / a

  have hP : pullField y L = IntermediateField.adjoin ℚ (Set.range r) := by
    have hw : ∀ i, aeval y (L i) / a ∈ IntermediateField.adjoin ℚ (Set.range r) := by
      intro i
      by_cases h : i = j₀
      · subst h; rw [div_self hj₀]; exact one_mem _
      · exact IntermediateField.subset_adjoin _ _ ⟨⟨i, h⟩, rfl⟩
    apply le_antisymm
    · rw [pullField, IntermediateField.adjoin_le_iff]
      rintro _ ⟨i, j, hj, rfl⟩
      rw [← div_div_div_cancel_right₀ hj₀]
      exact div_mem (hw i) (hw j)
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨i, rfl⟩
      exact IntermediateField.subset_adjoin _ _ ⟨i.1, j₀, hj₀, rfl⟩

  obtain ⟨_, ⟨_, _, hrel⟩, _, _⟩ := hA
  obtain ⟨c, hc⟩ := CoordArithOfFnField.nonzero_of_relevant y hrel
  have hrel' : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := fun k => ⟨c k, hc k⟩
  have halg : Algebra.IsAlgebraic (Algebra.adjoin ℚ (Set.range r)) Ω := by
    refine ⟨fun x => IntermediateField.isAlgebraic_adjoin_iff.mp ?_⟩
    have hle : blockFnField y ≤
        (algebraicClosure (IntermediateField.adjoin ℚ (Set.range r)) Ω).restrictScalars ℚ := by
      rw [blockFnField, IntermediateField.adjoin_le_iff]
      rintro _ ⟨p, q, hpq, rfl⟩
      refine (IntermediateField.mem_restrictScalars _).mpr (mem_algebraicClosure_iff.mpr ?_)
      have := hR K ι Ω y D e L hrel' he hL hz p q hpq
      rwa [hP] at this
    have hx := hle ((blockFnField_eq_top c hc hB).symm ▸ IntermediateField.mem_top : x ∈ blockFnField y)
    exact mem_algebraicClosure_iff.mp ((IntermediateField.mem_restrictScalars _).mp hx)

  have hcard : Cardinal.mk {i : Fin (D + 1) // i ≠ j₀} ≤ Algebra.trdeg ℚ Ω := by
    rw [trdeg_eq ⟨‹_›, ⟨‹_›, ‹_›, hrel⟩, ‹_›, ‹_›⟩ hB, Cardinal.mk_fintype]
    norm_cast
    simp [Fintype.card_subtype_compl]
  have hind : AlgebraicIndependent ℚ r :=
    (Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite ℚ r hcard).1

  have hw : (fun i => if h : i = j₀ then (1 : Ω) else r ⟨i, h⟩) = fun i => aeval y (L i) / a := by
    funext i
    split_ifs with h
    · subst h; exact (div_self hj₀).symm
    · rfl
  have hr0 : aeval r (dehom j₀ F) = 0 := by
    rw [aeval_dehom, hw]
    have h1 := FibreNormCharpoly.aeval_mul_of_isHomogeneous hF a (fun i => aeval y (L i) / a)
    simp only [mul_div_cancel₀ _ hj₀] at h1
    rw [h0] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_left (pow_ne_zero _ hj₀)
  have hG : dehom j₀ F = 0 := hind.eq_zero_of_aeval_eq_zero _ hr0

  have hFX : F * X j₀ = 0 := by
    refine MvPolynomial.funext fun x => ?_
    rw [map_mul, eval_X, map_zero]
    by_cases hx : x j₀ = 0
    · rw [hx, mul_zero]
    · have h1 := FibreNormCharpoly.aeval_mul_of_isHomogeneous (Ω := ℚ) hF (x j₀) (fun i => x i / x j₀)
      have h2 := aeval_dehom j₀ F (fun i => x i.1 / x j₀)
      have hw' : (fun i => if h : i = j₀ then (1 : ℚ) else x i / x j₀) = fun i => x i / x j₀ := by
        funext i
        split_ifs with h
        · subst h; exact (div_self hx).symm
        · rfl
      rw [hG, map_zero, hw'] at h2
      have e1 : eval x F = x j₀ ^ d * eval (fun i => x i / x j₀) F := by
        have hs : (fun j => x j₀ * (x j / x j₀)) = x := funext fun j => mul_div_cancel₀ _ hx
        rw [hs] at h1
        rw [← coe_aeval_eq_eval, ← coe_aeval_eq_eval]
        exact h1
      have e2 : eval (fun i => x i / x j₀) F = 0 := by
        rw [← coe_aeval_eq_eval]
        exact h2.symm
      rw [e1, e2, mul_zero, zero_mul]
  exact (mul_eq_zero.mp hFX).resolve_right (X_ne_zero _)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsProjFrameFibrePt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

def ProjFrameFibrePt.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω) (e : Fin (D + 1) → Ix κ),
    IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) → IsProjFrame x e →
    ∀ G : GenFibre (inrV (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))))
        (graphIdeal (coordIdeal ℤ x) (ReciprocityTheory.ChartRestriction.G.AI.I4.linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e))),
      IsProjVarF (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal (Sum.inr : Unit → Unit ⊕ Unit) G) 0

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGradedSubmodules
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def GradedSubmodules.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
    (𝓜 : (K → ℤ) → Submodule S M),
    KH.IsMGraded S ι 𝓜 →
    IsMultiHomogIdeal (Module.annihilator (MRingOver S ι) M) ∧
      ∀ P : Ideal (MRingOver S ι), IsMultiHomogIdeal P →
        KH.IsMGraded S ι (subGrading 𝓜 (P • ⊤ : Submodule (MRingOver S ι) M)) ∧
          KH.IsMGraded S ι (quotGrading 𝓜 (P • ⊤ : Submodule (MRingOver S ι) M))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFibreNormBadPrimesFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

section Defs

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

def HasCommonZeroModP (y : (Σ k, ι k) → Ω) {D : ℕ} (L : Fin (D + 1) → MRing ι) (p : ℕ) (hp : p.Prime) : Prop :=
  letI : Fact p.Prime := ⟨hp⟩
  ∃ z : (Σ k, ι k) → AlgebraicClosure (ZMod p), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) ∧
    (∀ f ∈ mCoordIdeal y, eval z (map (Int.castRingHom (AlgebraicClosure (ZMod p))) f) = 0) ∧
    ∀ j, eval z (map (Int.castRingHom (AlgebraicClosure (ZMod p))) (L j)) = 0

end Defs

def FibreNormBadPrimesFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (e : K → ℕ) (L : Fin (D + 1) → MRing ι),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    (∀ k, 1 ≤ e k) → (∀ j, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (L j) e) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∃ j, eval z (map (Int.castRingHom ℂ) (L j)) ≠ 0) →
    {p : ℕ | ∃ hp : p.Prime, HasCommonZeroModP y L p hp}.Finite

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNefPlusAmpleDegree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1

noncomputable section

namespace NefPlusAmpleDegree

theorem genDeg_one_pos (hA : GenDegAmple.Statement) {K : Type} [Fintype K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {W : Ideal (MRing ι)} {d : ℕ} (hW : IsArithVar W (d + 1)) :
    0 < genDeg W d 1 := by
  have : W.IsPrime := hW.2.1.1
  have hEq := CurvePointsFinite.mCoordIdeal_genericPt W hW.2.1.2.1
  have hV : IsArithVar (mCoordIdeal (CurvePointsFinite.genericPt W)) (d + 1) := by rw [hEq]; exact hW
  have h := hA K ι _ (CurvePointsFinite.genericPt W) d 1 hV fun _ => le_rfl
  rwa [hEq] at h


open Classical in
theorem nefOnF_of_nefOnGenericDeg {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} {b : K → ℤ} (hb : NefOnGenericDeg P b) :
    KH.NefOnF (fun V _ L => NumbersDVR.intNum ℚ V L) (P.map (MvPolynomial.map (Int.castRingHom ℚ))) b := by
  intro W hW hle
  obtain ⟨hWar, hWmap⟩ := NefAmpleGeneric.isArithVar_comap_of_isProjVarF hW
  have hPW : P ≤ W.comap (MvPolynomial.map (Int.castRingHom ℚ)) := Ideal.map_le_iff_le_comap.mp hle
  have h := hb _ hWar hPW
  rw [genDeg, hWmap] at h
  have hL : (fun _ : Fin 1 => b) = ![b] := by
    funext j
    fin_cases j
    rfl
  rw [hL] at h
  exact h

end NefPlusAmpleDegree

theorem NefPlusAmpleDegree.proof (hK : KH.KleimanNefFStatement) (hA : GenDegAmple.Statement) :
    NefPlusAmpleDegree.Statement := by
  classical
  intro K _ ι _ P D a hP hnef q
  have : Nonempty K := hP.1
  set Q := P.map (MvPolynomial.map (Int.castRingHom ℚ)) with hQ
  obtain ⟨hprime, hdimq⟩ := ShiftDegreePolynomial.genericFibre hP
  have hd : FieldNumbers.relDim Q = D := by
    rw [FieldNumbers.relDim_of_ringKrullDim_eq _ _ hdimq]
    simp only [Nat.cast_add, add_sub_cancel_right]
    rfl
  let f : (Fin D → K → ℤ) → ℤ := fun bs => NumbersDVR.intNum ℚ Q bs
  have hadd : ∀ (bs : Fin D → K → ℤ) (j : Fin D) (x y : K → ℤ),
      f (Function.update bs j (x + y)) = f (Function.update bs j x) + f (Function.update bs j y) :=
    fun bs j x y => FieldNumbers.IntNumAdd.full ℚ K ι Q hprime.multiHomog hprime.relevant D hd bs j x y
  let I : IFamily ℚ ι := fun V _ L => NumbersDVR.intNum ℚ V L
  have hI : IsFieldIntersection I := NumbersDVR.IntNumIsFieldIntersection.full ℚ K ι
  have hPV : IsProjVarF Q D := isProjVarF_map_of_isArithVar hP
  have hnefA : KH.NefOnF I Q a := NefPlusAmpleDegree.nefOnF_of_nefOnGenericDeg hnef
  have hnefH : KH.NefOnF I Q 1 := NefPlusAmpleDegree.nefOnF_of_nefOnGenericDeg fun W hW _ =>
    (NefPlusAmpleDegree.genDeg_one_pos hA hW).le
  have hterm : ∀ s : Finset (Fin D), 0 ≤ f (s.piecewise (fun _ => a) (fun _ => 1)) := by
    intro s
    refine hK ℚ K ι I Q D _ hI hPV fun i => ?_
    by_cases hi : i ∈ s
    · simpa [Finset.piecewise, hi] using hnefA
    · simpa [Finset.piecewise, hi] using hnefH
  have hg : genDeg P D ((q : ℤ) • a + 1) = f (fun _ => (q : ℤ) • a + 1) := rfl
  rw [hg, ShiftDegreePolynomial.expand f hadd (q : ℤ) a 1]
  refine Finset.sum_pos' (fun s _ => mul_nonneg (pow_nonneg (Int.natCast_nonneg q) _) (hterm s))
    ⟨∅, Finset.mem_univ _, ?_⟩
  rw [Finset.card_empty, pow_zero, one_mul, Finset.piecewise_empty]
  exact NefPlusAmpleDegree.genDeg_one_pos hA hP

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullGradedAlgebraic
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

namespace PullGradedAlgebraic

variable {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)]

def blockDeg (m : (Σ k, ι k) →₀ ℕ) (k : K) : ℕ := ∑ i, m ⟨k, i⟩

theorem blockDeg_add (m m' : (Σ k, ι k) →₀ ℕ) (k : K) :
    blockDeg (m + m') k = blockDeg m k + blockDeg m' k := by
  simp [blockDeg, Finset.sum_add_distrib]

theorem blockDeg_sum {α : Type} (s : Finset α) (f : α → (Σ k, ι k) →₀ ℕ) (k : K) :
    blockDeg (∑ a ∈ s, f a) k = ∑ a ∈ s, blockDeg (f a) k := by
  simp only [blockDeg, Finsupp.finsetSum_apply]
  exact Finset.sum_comm

theorem blockDeg_single [DecidableEq K] (s : Σ k, ι k) (a : ℕ) (k' : K) :
    blockDeg (Finsupp.single s a) k' = if k' = s.1 then a else 0 := by
  classical
  obtain ⟨k0, i0⟩ := s
  simp only [blockDeg]
  split_ifs with h
  · subst h
    rw [Finset.sum_eq_single i0]
    · simp
    · intro i _ hi
      rw [Finsupp.single_apply, if_neg]
      intro h'
      exact hi (eq_of_heq (Sigma.mk.inj_iff.mp h').2).symm
    · simp
  · apply Finset.sum_eq_zero
    intro i _
    rw [Finsupp.single_apply, if_neg]
    intro h'
    exact h (congrArg Sigma.fst h').symm

theorem isMultiHomog_monomial {m : (Σ k, ι k) →₀ ℕ} {b : K → ℕ} (h : ∀ k, blockDeg m k = b k) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (monomial m (1 : ℚ)) b := by
  intro m' hm' k
  rw [support_monomial, if_neg one_ne_zero, Finset.mem_singleton] at hm'
  subst hm'
  exact h k

theorem le_of_blockDeg {m : (Σ k, ι k) →₀ ℕ} {b : K → ℕ} (h : ∀ k, blockDeg m k = b k)
    (v : Σ k, ι k) : m v ≤ b v.1 := by
  rw [← h v.1, blockDeg]
  exact Finset.single_le_sum (f := fun i => m ⟨v.1, i⟩) (fun _ _ => Nat.zero_le _) (Finset.mem_univ v.2)

def diagMono [Fintype K] (c : ∀ k, ι k) (b : K → ℕ) : (Σ k, ι k) →₀ ℕ := ∑ k, Finsupp.single ⟨k, c k⟩ (b k)

theorem blockDeg_diagMono [Fintype K] (c : ∀ k, ι k) (b : K → ℕ) (k : K) : blockDeg (diagMono c b) k = b k := by
  classical
  rw [diagMono, blockDeg_sum, Finset.sum_eq_single k]
  · rw [blockDeg_single, if_pos rfl]
  · intro k' _ hk'
    rw [blockDeg_single, if_neg (Ne.symm hk')]
  · simp

omit [∀ k, Fintype (ι k)] in
theorem aeval_diagMono_ne_zero [Fintype K] {Ω : Type} [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (b : K → ℕ) : aeval y (monomial (diagMono c b) (1 : ℚ)) ≠ 0 := by
  classical
  rw [diagMono, monomial_sum_one, map_prod]
  exact Finset.prod_ne_zero_iff.mpr fun k _ => by
    rw [← X_pow_eq_monomial, map_pow, aeval_X]
    exact pow_ne_zero _ (hc k)

end PullGradedAlgebraic


open PullGradedAlgebraic in
theorem PullGradedAlgebraic.proof : PullGradedAlgebraic.Statement := by
  intro K _ ι _ Ω _ _ y D e L d₀ hy he hL hgr p q hpq
  classical
  choose c hc using hy
  obtain ⟨j₀, hw⟩ : ∃ j₀, aeval y (L j₀) ≠ 0 := by
    obtain ⟨a, -, ha⟩ := hgr d₀ (monomial (diagMono c d₀) 1)
      (isMultiHomog_monomial (blockDeg_diagMono c d₀)) (fun _ => le_rfl)
    by_contra h
    simp only [not_exists, not_not] at h
    rw [Finset.sum_eq_zero (fun j _ => by rw [h j, mul_zero])] at ha
    exact aeval_diagMono_ne_zero y c hc d₀ ha
  set F := pullField y L
  set w := aeval y (L j₀)
  set n₀ := ∑ k, d₀ k
  set T : Set Ω := {x | ∃ n ≤ n₀, ∃ m : (Σ k, ι k) →₀ ℕ, (∀ k, blockDeg m k = n * e k) ∧
    x = aeval y (monomial m (1 : ℚ)) / w ^ n} with hT
  set W : Submodule F Ω := Submodule.span F T with hW
  have hratio : ∀ j, aeval y (L j) / w ∈ F := fun j =>
    IntermediateField.subset_adjoin _ _ ⟨j, j₀, hw, rfl⟩
  have claim : ∀ n (g : MvPolynomial (Σ k, ι k) ℚ), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g (fun k => n * e k) →
      aeval y g / w ^ n ∈ W := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro g hg
    by_cases hn : n ≤ n₀
    · set_option synthInstance.maxHeartbeats 100000 in
      rw [g.as_sum, map_sum, Finset.sum_div]
      refine Submodule.sum_mem _ fun m hm => ?_
      have hmono : monomial m (AddMonoidAlgebra.coeff g m) = AddMonoidAlgebra.coeff g m • monomial m (1 : ℚ) := by
        rw [smul_monomial, smul_eq_mul, mul_one]
      rw [hmono, map_smul, smul_div_assoc]
      exact Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨n, hn, m, fun k => hg m hm k, rfl⟩)
    · replace hn := Nat.lt_of_not_le hn
      obtain ⟨a, ha, hga⟩ := hgr (fun k => n * e k) g hg (fun k => by
        have h1 : d₀ k ≤ n₀ := Finset.single_le_sum (f := d₀) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
        have h2 := Nat.mul_le_mul_left n (he k)
        omega)
      have hdeg : (fun k => n * e k) - e = fun k => (n - 1) * e k := by
        funext k
        show n * e k - e k = (n - 1) * e k
        rw [Nat.sub_one_mul]
      rw [hga, Finset.sum_div]
      refine Submodule.sum_mem _ fun j _ => ?_
      have h1 := ih (n - 1) (by omega) (a j) (by rw [← hdeg]; exact ha j)
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      have hj : aeval y (a j) * aeval y (L j) / w ^ (n' + 1) =
          (⟨aeval y (L j) / w, hratio j⟩ : F) • (aeval y (a j) / w ^ (n' + 1 - 1)) := by
        rw [Algebra.smul_def, IntermediateField.algebraMap_apply, Nat.add_sub_cancel]
        field_simp
        ring
      rw [hj]
      exact W.smul_mem _ h1
  have hTfin : T.Finite := by
    let B : (Σ k, ι k) →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun v => n₀ * e v.1)
    refine (((Set.finite_Iic n₀).prod (Set.finite_Iic B)).image
      (fun nm : ℕ × ((Σ k, ι k) →₀ ℕ) => aeval y (monomial nm.2 (1 : ℚ)) / w ^ nm.1)).subset ?_
    rintro x ⟨n, hn, m, hm, rfl⟩
    refine ⟨(n, m), ⟨hn, fun v => ?_⟩, rfl⟩
    show m v ≤ n₀ * e v.1
    exact (le_of_blockDeg hm v).trans (Nat.mul_le_mul_right _ hn)
  have hWfg : W.FG := ⟨hTfin.toFinset, by rw [Set.Finite.coe_toFinset]⟩
  have hW0 : W ≠ ⊥ := by
    intro h
    have h1 : (1 : Ω) ∈ W := Submodule.subset_span ⟨0, Nat.zero_le _, 0, fun k => by simp [blockDeg], by simp⟩
    rw [h, Submodule.mem_bot] at h1
    exact one_ne_zero h1
  have hint : ∀ n (m : (Σ k, ι k) →₀ ℕ), (∀ k, blockDeg m k = n * e k) →
      IsIntegral F (aeval y (monomial m (1 : ℚ)) / w ^ n) := by
    intro n m hm
    refine isIntegral_of_smul_mem_submodule W hW0 hWfg _ fun z hz => ?_
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨n', -, m', hm', rfl⟩ := hx
      have hmul : monomial (m + m') (1 : ℚ) = monomial m 1 * monomial m' 1 := by
        rw [monomial_mul, one_mul]
      have hx : (aeval y (monomial m (1 : ℚ)) / w ^ n) • (aeval y (monomial m' (1 : ℚ)) / w ^ n') =
          aeval y (monomial (m + m') (1 : ℚ)) / w ^ (n + n') := by
        rw [smul_eq_mul, hmul, map_mul, pow_add]
        field_simp
      rw [hx]
      exact claim _ _ (isMultiHomog_monomial fun k => by rw [blockDeg_add, hm, hm', add_mul])
    | zero => simp
    | add x x' _ _ hx hx' => rw [smul_add]; exact W.add_mem hx hx'
    | smul a x _ hx => rw [smul_comm]; exact W.smul_mem a hx
  set n := n₀ + 1
  set μ := diagMono c (fun k' => n * e k' - if k' = p.1 then 1 else 0)
  have hdeg : ∀ s : Σ k, ι k, s.1 = p.1 → ∀ k', blockDeg (Finsupp.single s 1 + μ) k' = n * e k' := by
    intro s hs k'
    rw [blockDeg_add, blockDeg_diagMono, blockDeg_single, hs]
    have h1 := Nat.mul_le_mul (show 1 ≤ n by omega) (he k')
    generalize n * e k' = t at *
    split_ifs <;> omega
  have hval : ∀ s : Σ k, ι k, aeval y (monomial (Finsupp.single s 1 + μ) (1 : ℚ)) =
      y s * aeval y (monomial μ (1 : ℚ)) := by
    intro s
    rw [monomial_single_add, pow_one, map_mul, aeval_X]
  have hμ0 : aeval y (monomial μ (1 : ℚ)) ≠ 0 := aeval_diagMono_ne_zero y c hc _
  have hr : ∀ s : Σ k, ι k, s.1 = p.1 →
      y s * aeval y (monomial μ (1 : ℚ)) / w ^ n ∈ algebraicClosure F Ω := fun s hs => by
    rw [mem_algebraicClosure_iff, ← hval s]
    exact (hint n _ (hdeg s hs)).isAlgebraic
  have key : y p * aeval y (monomial μ (1 : ℚ)) / w ^ n / (y q * aeval y (monomial μ (1 : ℚ)) / w ^ n) =
      y p / y q := by
    rw [div_div_div_cancel_right₀ (pow_ne_zero _ hw), mul_div_mul_right _ _ hμ0]
  rw [← key, ← mem_algebraicClosure_iff]
  exact (algebraicClosure F Ω).div_mem (hr p rfl) (hr q hpq.symm)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsVeroneseChiParts
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory MeasureTheory

noncomputable section

open Veronese

def VeroneseMonoBasis.Statement : Prop :=
  ∀ D n : ℕ, ∃ b : Fin (Finset.Nat.antidiagonalTuple (D + 1) (2 * n)).card → MvPolynomial (Ix (Idx D)) ℚ,
    IsSecBasis (Veronese.x D) n b ∧
      ∀ k, aeval (Veronese.x D) (b k) = ∏ i, Veronese.t D i ^ adtEnum D (2 * n) k i

def VeroneseGramMono.Statement : Prop :=
  ∀ (D n r : ℕ) (b : Fin r → MvPolynomial (Ix (Idx D)) ℚ)
    (A : Matrix (Fin r) (Fin (Finset.Nat.antidiagonalTuple (D + 1) (2 * n)).card) ℤ),
    (∀ k, aeval (Veronese.x D) (b k) =
      ∑ l, (A k l : Veronese.Fld D) * ∏ i, Veronese.t D i ^ adtEnum D (2 * n) l i) →
    Veronese.gram D n b = A.map (Int.cast : ℤ → ℝ) *
      Matrix.diagonal (fun l => monoNormSq (adtEnum D (2 * n) l)) * (A.map (Int.cast : ℤ → ℝ)).transpose

theorem adtEnum_zero_eq (D : ℕ) (l : Fin (Finset.Nat.antidiagonalTuple (D + 1) 0).card) :
    adtEnum D 0 l = 0 := by
  have h := Finset.Nat.mem_antidiagonalTuple.mp
    (((Finset.Nat.antidiagonalTuple (D + 1) 0).equivFin.symm l).2)
  funext i
  exact (Finset.sum_eq_zero_iff.mp h) i (Finset.mem_univ i)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PProjFSMass
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

theorem ProjFSMass.proof : ProjFSMass.Statement := by
  intro D Ω _ _ κ _ x e m hfr hFS
  exact ⟨gbPsi e, gb_isGoodProj hfr, gb_ptsIntegralAt hfr hFS⟩

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRatioFieldDeg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def RatioFieldDeg.Statement : Prop :=
  ∀ (ι : Type) (E₁ E₂ : Type) [Field E₁] [CharZero E₁] [Field E₂] [CharZero E₂] (u : ι → E₁) (v : ι → E₂)
    (D : ℕ) (e : Fin (D + 1) → ι), coordIdeal ℤ u = coordIdeal ℤ v → projDeg u e = projDeg v e

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsZeroCocycleSection
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def ZeroCocycleSection.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (a : K → ℤ),
    ∀ v ∈ KH.cechZc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a 0,
      ∃ s ∈ chartLat y a 1, GenOnFibres.secCoch y ℤ s a = v

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTranscRatioDeg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def TranscRatioDeg.Statement : Prop :=
  ∀ (ι : Type) (E : Type) [Field E] [CharZero E] (u : ι → E) (D : ℕ) (e : Fin (D + 1) → ι) (w : Fin (D + 1) → E)
    (i₀ : ι) (Φ : Type) [Field Φ] [Algebra Φ E],
    u i₀ ≠ 0 → (∀ k, u (e k) ≠ 0) → (∀ k, w k * u (e 0) = w 0 * u (e k)) →
    Transcendental (Algebra.adjoin ℤ (Set.range u)) (w 0) →
    (algebraMap Φ E).fieldRange = Subfield.closure (Set.range w) →
    Module.finrank Φ (IntermediateField.adjoin Φ (Set.range fun i => u i / u i₀)) = projDeg u e

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenNearMul
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def GenNearMul.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
    (𝓜 : (K → ℤ) → Submodule S M) (W : Ideal (MRingOver S ι)) (d n : K → ℤ) (f g : MRingOver S ι) (δ γ : K → ℕ),
    KH.IsMGraded S ι 𝓜 → W ≤ Module.annihilator (MRingOver S ι) M → ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f δ → ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g γ →
    GenNear S ι 𝓜 d f δ → GenNear S ι (KH.quotPart S W) n g γ → GenNear S ι 𝓜 (d + n) (f * g) (δ + γ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsClosedPtChartUnit
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def ClosedPtChartUnit.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRingOver S ι)), IsClosedMultiPt P →
    ∀ I : ∀ k, Finset (ι k), (∀ k, (I k).Nonempty) → (∀ k, ∀ i ∈ I k, (X ⟨k, i⟩ : MRingOver S ι) ∉ P) →
    ∀ (f : MRingOver S ι) (a : K → ℕ), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a → f ∉ P →
      ∃ t ∈ KH.cellMon S I, ∃ (g : MRingOver S ι) (b : K → ℕ),
        ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog t (a + b) ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g b ∧ t - g * f ∈ P

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsProjFrameFibreDeg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

def ProjFrameFibreDeg.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω) (e : Fin (D + 1) → Ix κ),
    IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) → IsProjFrame x e →
    ∀ (G : GenFibre (inrV (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))))
        (graphIdeal (coordIdeal ℤ x) (ReciprocityTheory.ChartRestriction.G.AI.I4.linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e))))
      (i : (k : FibreBlock (Sum.inr : Unit → Unit ⊕ Unit)) → fibreIdx (Sum.elim (GlobalTheory κ) (GlobalTheory (Fin (D + 1)))) Sum.inr k),
      IsChart (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal (Sum.inr : Unit → Unit ⊕ Unit) G) i →
      ptDeg (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal (Sum.inr : Unit → Unit ⊕ Unit) G) i = projDeg x e

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsClosedPtSkyscraper
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def ClosedPtSkyscraper.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (N : Type) [AddCommGroup N] [Module (MRingOver S ι) N] [Module S N] [IsScalarTower S (MRingOver S ι) N]
    (𝓝 : (K → ℤ) → Submodule S N) (P : Ideal (MRingOver S ι)) (d : K → ℤ),
    KH.IsMGraded S ι 𝓝 → IsClosedMultiPt P → (∀ p ∈ P, ∀ n : N, p • n = 0) →
    ∀ I : KH.Cell K ι 0, (∀ k, ∀ i ∈ I.1 k, (X ⟨k, i⟩ : MRingOver S ι) ∉ P) →
    ∀ y ∈ KH.locPart ι 𝓝 (KH.cellMon S I.1) d, ∃ z ∈ KH.cechZc ι 𝓝 d 0, z I = y

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPullConeDegree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def PullConeDegree.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (e : K → ℕ) (L : Fin (D + 1) → MRing ι) (N : ℕ),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → (∀ j, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (L j) e) →
    (∀ c : ∀ k, ι k, (∏ k, (X ⟨k, c k⟩ : MvPolynomial (Σ k, ι k) ℚ)) ^ N ∈ coneNullIdeal y L) →
    ∀ (d : K → ℕ) (g : MvPolynomial (Σ k, ι k) ℚ), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g d →
      (∀ k, e k + N * Fintype.card (ι k) ≤ d k) →
      ∃ a : Fin (D + 1) → MvPolynomial (Σ k, ι k) ℚ, (∀ j, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (a j) (d - e)) ∧
        aeval y g = ∑ j, aeval y (a j) * aeval y (L j)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
