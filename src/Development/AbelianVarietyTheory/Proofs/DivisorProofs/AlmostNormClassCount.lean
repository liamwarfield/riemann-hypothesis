module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RuleBaseChangeSectionValuesSemilinear
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRestrictionExtendByZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddHaarLeftRightMulAdelicMatricesModule
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionHeightLowerBound
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ReadingLinearIndependentAndInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAE
public import Formalism.LocalToGlobal.UnitaryNorms.CharProd
public import Formalism.LocalToGlobal.NumberFieldFamilies.IdTransSM
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurConstantsExistOnChainOfCuspRapidDecay
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrdSubConjEqNeg

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlmostNormClassCount
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.QuadSymbol.SignCount

theorem card_prod_eq_mul_two {ι : Type} [Fintype ι] [Nonempty ι] (c : ℤˣ) :
    Nat.card {s : ι → ℤˣ // c * ∏ i, s i = 1} * 2 = 2 ^ Fintype.card ι := by
  classical
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  let m : ι → ℤˣ := Pi.mulSingle i₀ (-1)
  have hm : ∏ i, m i = -1 := by simp [m, Finset.prod_pi_mulSingle']
  have hmm : m * m = 1 := by
    ext i
    by_cases h : i = i₀
    · subst h; simp [m]
    · simp [m, Pi.mulSingle_eq_of_ne h]
  have key : ∀ s : ι → ℤˣ, (c * ∏ i, (s * m) i = 1) ↔ ¬ (c * ∏ i, s i = 1) := by
    intro s
    simp only [Pi.mul_apply, Finset.prod_mul_distrib, hm]
    rcases Int.units_eq_one_or (c * ∏ i, s i) with h | h
    · rw [← mul_assoc, h]; decide
    · rw [← mul_assoc, h]; decide
  let e : {s : ι → ℤˣ // c * ∏ i, s i = 1} ≃ {s : ι → ℤˣ // ¬ (c * ∏ i, s i = 1)} :=
    { toFun := fun s => ⟨s.1 * m, fun h => (key s.1).1 h s.2⟩
      invFun := fun s => ⟨s.1 * m, by
        have := (key s.1).2 s.2
        exact this⟩
      left_inv := fun s => Subtype.ext (by simp [mul_assoc, hmm])
      right_inv := fun s => Subtype.ext (by simp [mul_assoc, hmm]) }
  have htot := Fintype.card_subtype_compl (fun s : ι → ℤˣ => c * ∏ i, s i = 1)
  rw [Nat.card_eq_fintype_card, mul_two]
  nth_rewrite 2 [Fintype.card_congr e]
  have hle := Fintype.card_subtype_le (fun s : ι → ℤˣ => c * ∏ i, s i = 1)
  rw [htot, Fintype.card_pi, Finset.prod_const, Fintype.card_units_int, Finset.card_univ] at *
  omega

end GlobalTheory.QuadSymbol.SignCount

namespace GlobalTheory.QuadSymbol.SignCount

theorem neg_one_not_mem_normGroup {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [Algebra.IsQuadraticExtension K L] (hL : NumberField.IsTotallyComplex L)
    {w : InfinitePlace K} (hw : w.IsReal) : (-1 : (w.Completion)ˣ) ∉ normGroup K L w.Completion := by
  obtain ⟨δ, b, -, h0, h1⟩ := AlmostNorm.exists_basis_sq K L
  have hneg : InfinitePlace.embedding_of_isReal hw δ < 0 := by
    by_contra hc
    obtain ⟨r, hr⟩ := Real.isSquare_iff.2 (not_lt.1 hc)
    let τ : L →+* ℂ := ComplexEmbedding.lift L w.embedding
    have hτ : ∀ x : K, τ (algebraMap K L x) = InfinitePlace.embedding_of_isReal hw x := fun x => by
      rw [InfinitePlace.embedding_of_isReal_apply]
      exact ComplexEmbedding.lift_algebraMap_apply L w.embedding x
    have h2 : τ (b 1) * τ (b 1) = (r : ℂ) * r := by rw [← map_mul, h1, hτ, hr]; push_cast; rfl
    have h3 : starRingEnd ℂ (τ (b 1)) = τ (b 1) := by
      rcases mul_self_eq_mul_self_iff.1 h2 with h | h <;> rw [h] <;> simp
    refine InfinitePlace.not_isReal_iff_isComplex.2 (hL.isComplex (InfinitePlace.mk τ))
      (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => ?_)))
    change starRingEnd ℂ (τ x) = τ x
    rw [← b.sum_repr x, Fin.sum_univ_two, h0, Algebra.smul_def, Algebra.smul_def]
    simp only [map_add (f := _), map_mul, map_one, hτ, h3, Complex.conj_ofReal]
  rw [mem_normGroup_iff_form b h0 h1]
  rintro ⟨x, y, hxy⟩
  let f := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  have hf : f (algebraMap K w.Completion δ) = InfinitePlace.embedding_of_isReal hw δ := by
    rw [InfinitePlace.Completion.algebraMap_apply]
    simpa [f, InfinitePlace.Completion.instCoe] using
      InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hw ((WithAbs.equiv _).symm δ)
  have := congrArg f hxy
  simp only [Units.val_neg, Units.val_one, map_neg, map_one, map_sub, map_mul, map_pow, hf] at this
  nlinarith [sq_nonneg (f x), sq_nonneg (f y)]

end GlobalTheory.QuadSymbol.SignCount

namespace GlobalTheory.QuadSymbol.SignCount

def infSigns (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L] (t : Kˣ) :
    InfinitePlace K → ℤˣ :=
  fun w => eta K L w.Completion (infDiag K t w)

theorem infSigns_eq_of_mem {K L : Type} [Field K] [NumberField K] [Field L] [Algebra K L]
    [FiniteDimensional K L] {t t' : Kˣ} (h : t⁻¹ * t' ∈ globalNorms K L) :
    infSigns K L t' = infSigns K L t := by
  funext w
  refine eta_eq_of_div_mem ?_
  have := toUnits_mem_normGroup (K := K) (L := L) w.Completion h
  rw [← div_eq_inv_mul, _root_.map_div] at this
  exact this

theorem infSigns_out {K L : Type} [Field K] [NumberField K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (t : Kˣ) :
    infSigns K L (Quotient.out (QuotientGroup.mk t : Kˣ ⧸ globalNorms K L)) = infSigns K L t :=
  infSigns_eq_of_mem (QuotientGroup.eq.1 (QuotientGroup.out_eq' _).symm)

theorem card_classes_mul_two : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [Algebra.IsQuadraticExtension K L], NumberField.IsTotallyReal K → NumberField.IsTotallyComplex L → ∀ x : GlobalTheory.QuadSymbol.FinFam K, GlobalTheory.QuadSymbol.AlmostNorm K L x → Nat.card {q : Kˣ ⧸ GlobalTheory.QuadSymbol.globalNorms K L // ∃ t : Kˣ, q = QuotientGroup.mk t ∧ ∀ u, x u / GlobalTheory.QuadSymbol.finDiag K t u ∈ GlobalTheory.QuadSymbol.normGroup K L (u.adicCompletion K)} * 2 = 2 ^ Fintype.card (InfinitePlace K) := by
  intro K L _ _ _ _ _ _ hK hL x hx
  have hfd : FiniteDimensional K L := Module.finite_of_finrank_eq_succ (Algebra.IsQuadraticExtension.finrank_eq_two K L)
  obtain ⟨-, hnorm, hseq, -⟩ := exactSequence K L
  obtain ⟨-, hc2⟩ := localCharacters K L
  set c : ℤˣ := ∏ᶠ v : HeightOneSpectrum (𝓞 K), eta K L (v.adicCompletion K) (x v) with hc
  rw [← card_prod_eq_mul_two c]
  congr 1
  have hprod : ∀ t : Kˣ, (∀ u, x u / finDiag K t u ∈ normGroup K L (u.adicCompletion K)) →
      c * ∏ w, infSigns K L t w = 1 := by
    intro t ht
    have := (hseq x (infDiag K t) hx).1 ⟨t, fun u => ht u, fun w => by simp [one_mem]⟩
    exact this
  refine Nat.card_congr (Equiv.ofBijective (fun q => ⟨infSigns K L (Quotient.out q.1), ?_⟩) ⟨?_, ?_⟩)
  · obtain ⟨t, hq, ht⟩ := q.2
    rw [hq, infSigns_out]
    exact hprod t ht
  · rintro ⟨q₁, t₁, rfl, h₁⟩ ⟨q₂, t₂, rfl, h₂⟩ he
    have he' : infSigns K L t₁ = infSigns K L t₂ := by
      have := congrArg Subtype.val he
      simpa only [infSigns_out] using this
    refine Subtype.ext (QuotientGroup.eq.2 ((hnorm (t₁⁻¹ * t₂)).1 ⟨fun u => ?_, fun w => ?_⟩))
    · have hm := div_mem (h₁ u) (h₂ u)
      rwa [div_div_div_cancel_left, finDiag, finDiag, ← _root_.map_div, div_eq_inv_mul] at hm
    · have hm := Converse.div_mem_normGroup (hc2 w) (congrFun he' w)
      rwa [infDiag, infDiag, ← _root_.map_div, div_eq_inv_mul] at hm
  · rintro ⟨s, hs⟩
    let y : InfFam K := fun w => if s w = 1 then 1 else -1
    have hy : ∀ w, eta K L w.Completion (y w) = s w := by
      intro w
      rcases Int.units_eq_one_or (s w) with h | h
      · simp only [y, h, if_true]
        exact eta_eq_one_iff.2 (one_mem _)
      · simp only [y, h, show (-1 : ℤˣ) ≠ 1 by decide, if_false]
        exact eta_eq_neg_one_iff.2 (neg_one_not_mem_normGroup hL (hK.isReal w))
    have hy1 : etaProd K L x y = 1 := by
      unfold etaProd
      rw [Finset.prod_congr rfl fun w _ => hy w]
      exact hs
    obtain ⟨t, ht1, ht2⟩ := (hseq x y hx).2 hy1
    refine ⟨⟨QuotientGroup.mk t, t, rfl, fun u => ht1 u⟩, Subtype.ext ?_⟩
    simp only [infSigns_out]
    funext w
    rw [← hy w]
    exact (eta_eq_of_div_mem (ht2 w)).symm

end GlobalTheory.QuadSymbol.SignCount
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareCoordinateLengthMemIccAndPos
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareCoordinateLengthMemIccAndPos
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem poinWt_mem_Icc_and_pos : ∀ {n : ℕ} (S : Finset (Fin n)) (v : V n), (∀ a ∈ S, ‖v a‖ ≤ 1 / 2) →
    (∀ a, 0 ≤ poinWt S v a ∧ poinWt S v a ≤ 1) ∧ ((∀ a ∈ S, v a ≠ 0) → ∀ a, 0 < poinWt S v a) := by
  intro n S v hS
  refine ⟨fun a => ?_, fun hne a => ?_⟩
  · unfold poinWt
    split_ifs with ha
    · refine ⟨mul_nonneg (norm_nonneg _) (abs_nonneg _), ?_⟩
      rcases (norm_nonneg (v a)).eq_or_lt with h0 | hpos
      · rw [← h0]; simp
      · have h1 : ‖v a‖ ≤ 1 := (hS a ha).trans (by norm_num)
        have := Real.abs_log_mul_self_lt _ hpos h1
        rw [abs_mul, abs_of_pos hpos] at this
        linarith
    · exact ⟨zero_le_one, le_rfl⟩
  · unfold poinWt
    split_ifs with ha
    · have hpos : 0 < ‖v a‖ := norm_pos_iff.mpr (hne a ha)
      have hlt : ‖v a‖ < 1 := (hS a ha).trans_lt (by norm_num)
      have hlog : Real.log ‖v a‖ < 0 := Real.log_neg hpos hlt
      exact mul_pos hpos (abs_pos.mpr hlog.ne)
    · exact zero_lt_one

end GlobalTheory.GoodTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareCoordinateLengthMemIccAndPosStatement
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poincareCoordinateLength_mem_Icc_and_pos : ∀ {n : ℕ} (S : Finset (Fin n)) (v : V n), (∀ a ∈ S, ‖v a‖ ≤ 1 / 2) → (∀ a, 0 ≤ poinWt S v a ∧ poinWt S v a ≤ 1) ∧ ((∀ a ∈ S, v a ≠ 0) → ∀ a, 0 < poinWt S v a) := by
  first | exact @GlobalTheory.GoodTop.poinWt_mem_Icc_and_pos | exact GlobalTheory.GoodTop.poinWt_mem_Icc_and_pos | (intros; apply GlobalTheory.GoodTop.poinWt_mem_Icc_and_pos <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapRow0OfRowsSmul
noncomputable section

open NumberField
open scoped TensorProduct

namespace GlobalTheory.OneMapBase

open Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links
  Formalism.IndefR.Mult Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Scale

variable {C : Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}
  (O : OMDat C R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1))

end Scale

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)
  (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
  (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
  (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (i : Fin D.R.m)

theorem oneMapRow0_of_rows (cc : (T.U ((i : ℕ) + 1) (O i).s0).Comp → ℂ) (ph : ℂ)
    (hpins : OMPins T R κ v₀ O i)
    (hequiv : (O i).EquivAt (κ i) cc)
    (hid : OneMapRow (T.Q.Xo ((i : ℕ) + 1)) (O i).c' (Wc D i)
      (unfBC (O i).hle (T.U ((i : ℕ) + 1)) (inC (O i).c')) (O i).dict (O i).mu (xiR D) (wtA (κ i))
      (actLev (O i).c' (O i).lev2) (O i).dδ (O i).Cl' (O i).w (O i).La (O i).Nc (O i).gam (O i).vol (O i).ep (O i).io
      (O i).thAd (O i).Plc D.what₂.embLL.toRatAlgHom.fieldRange
      (cusp (T.Q.Xo ((i : ℕ) + 1)) (O i).c' (unfBC (O i).hle (T.U ((i : ℕ) + 1))) (wtA (κ i)) (Vc D i).rank) cc ph)
    (hrat : (O i).PhRat (κ i) (v₀ i (sg0 D A)) cc ph) :
    OneMapRow0 T R κ v₀ O i :=
  ⟨cc, ph, hequiv, ⟨hpins.1.ge, (GlobalTheory.FieldBC.secBC_and_cuspBC _ _ _ _ _ _ _ (O i).hle).2 _ _,
    (GlobalTheory.FieldBC.actLev_and_actBC _ _ _ _ _ _ _ (O i).hle _ _ hpins.2.act.1).2, hid⟩, hrat⟩

end GlobalTheory.OneMapBase
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarCharMulConjEqAbs
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.LeviModulus
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ImaginaryModulus

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sig_sig {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem exists_anti {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : ∃ δ : E, δ ≠ 0 ∧ σ δ = -δ := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  by_cases hx : ∃ x, σ x ≠ x
  · obtain ⟨x, hx⟩ := hx
    refine ⟨x - σ x, sub_ne_zero.2 (Ne.symm hx), ?_⟩
    rw [map_sub, sig_sig h]; ring
  · push_neg at hx
    exfalso
    have hr : ComplexEmbedding.IsReal τ := by
      rw [ComplexEmbedding.isReal_iff]
      ext x
      rw [ComplexEmbedding.conjugate_coe_eq]
      have := h.2.2.2 τ x
      rw [hx x] at this
      exact this.symm
    exact InfinitePlace.isComplex_mk_iff.1 (h.2.1.isComplex _) hr

theorem cA_inclR (σ : E →ₐ[F] E) (e : E) : cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
  simp [cA, inclR]

theorem cA_eq_sigR (σ : E →ₐ[F] E) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) : cA σ z = sigR (AF F) σ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a x => simp [cA, sigR]

section Iso

variable (σ : E →ₐ[F] E) [IsTopologicalRing (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))]

end Iso


end GlobalTheory.ImaginaryModulus
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCharPolyCoeffBounded
open NumberField IsDedekindDomain Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC
open scoped Classical TensorProduct
open GlobalTheory.BCT

namespace GlobalTheory.BCT.GeoFin

theorem nrmL_mem_KGL {E : Type} [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E)
    (hL : IsLevel (thL n w) (GlobalTheory.LFun.KGL w (n := n)) (GlobalTheory.LFun.KGL w (n := n))) {y : GLw n w}
    (hy : y ∈ GlobalTheory.LFun.KGL w (n := n)) : nrmL n w y ∈ GlobalTheory.LFun.KGL w (n := n) := by
  have ht := hL.2.2 y hy
  unfold nrmL
  unfold thL at ht
  split_ifs with hs
  · exact hy
  · rw [if_neg hs] at ht
    exact mul_mem hy ht

theorem charpoly_coeff_of_mem_KGL {E : Type} [Field E] [NumberField E] (n : ℕ) (w : Pl E)
    {z : GL (Fin n) (w.adicCompletion E)} (hz : z ∈ GlobalTheory.LFun.KGL w (n := n)) :
    (∀ i, Valued.v (z.val.charpoly.coeff i) ≤ 1) ∧ 1 ≤ Valued.v (z.val.charpoly.coeff 0) := by
  obtain ⟨g, rfl⟩ := hz
  set f := (Ov E w).subtype
  have hcp : (Formalism.UG.bc f g).val.charpoly = g.val.charpoly.map f := by
    rw [← Matrix.charpoly_map]
    rfl
  have hint : ∀ a : Ov E w, Valued.v (f a) ≤ 1 := fun a => a.2
  refine ⟨fun i => ?_, ?_⟩
  · rw [hcp, Polynomial.coeff_map]
    exact hint _
  · rw [hcp, Polynomial.coeff_map]
    have hdet : IsUnit (g.val.charpoly.coeff 0) := by
      have h1 : IsUnit g.val.det := (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
      rw [Matrix.det_eq_sign_charpoly_coeff] at h1
      exact isUnit_of_mul_isUnit_right h1
    obtain ⟨u, hu⟩ := hdet
    have hmul : f (u : Ov E w) * f ((u⁻¹ : (Ov E w)ˣ) : Ov E w) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have h2 : Valued.v (f (u : Ov E w)) * Valued.v (f ((u⁻¹ : (Ov E w)ˣ) : Ov E w)) = 1 := by
      rw [← map_mul, hmul, map_one]
    rw [← hu]
    calc (1 : _) = Valued.v (f (u : Ov E w)) * Valued.v (f ((u⁻¹ : (Ov E w)ˣ) : Ov E w)) := h2.symm
      _ ≤ Valued.v (f (u : Ov E w)) * 1 := mul_le_mul' le_rfl (hint _)
      _ = Valued.v (f (u : Ov E w)) := mul_one _

theorem charpoly_nrmL_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E),
    IsLevel (thL n w) (GlobalTheory.LFun.KGL w (n := n)) (GlobalTheory.LFun.KGL w (n := n)) → ∀ y ∈ GlobalTheory.LFun.KGL w (n := n),
      (∀ i, Valued.v ((nrmL n w y).val.charpoly.coeff i) ≤ 1) ∧ 1 ≤ Valued.v ((nrmL n w y).val.charpoly.coeff 0) :=
  fun _ _ _ _ n w hL y hy => charpoly_coeff_of_mem_KGL n w (nrmL_mem_KGL n w hL hy)

end GlobalTheory.BCT.GeoFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTraceFormLattice
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke.LatticeBasisLifts GlobalTheory.GeoLevel
open GlobalTheory.Member (FinCong IotaOK)
open GlobalTheory.LevelCusp (IsMatch)
open GlobalTheory.Dict (castFr)
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GeoLevel

theorem latEmb_model_of_eq (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (j : ℕ) (hj : InR D j)
    (hrt : (H.rt : D.host.E) = D.host.sqrtMinusD) (hrt0 : H.rt0 = D.host.φ₀ D.host.sqrtMinusD)
    (hp : Dw.p = (D.R.sigW j).1) (hq : Dw.q = (D.R.sigW j).2) (V : HSp D) (hV : V = D.sp.W j) (r : ℕ)
    (hr : V.rank = r) (ι₀ : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E))
    (hL : LatEmb V (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ ι₀))
    (hI : LatIsom V Dw.EF (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ ι₀)) :
    Function.Injective ι₀ ∧ Submodule.span D.host.E (Set.range ι₀) = ⊤ ∧
      ∀ x y, ((Dw.EF x y : ℤ) : ℚ) = Algebra.trace ℚ D.host.E (-(-D.host.xi0) *
        herm (GlobalTheory.RecDict.gmW V hr) (ι₀ x) (ι₀ y)) := by
  subst hV
  subst hr
  have hL' : LatEmb (D.sp.W j) ι₀ := hL
  obtain ⟨ε, hε⟩ : LatIsom (D.sp.W j) Dw.EF ι₀ := hI
  have hsp : Submodule.span D.host.E (Set.range ι₀) = ⊤ := by
    rw [← LinearMap.coe_range, hL'.2]
    exact (GlobalTheory.Member.latG_lattice_and_completion D (D.sp.W j) 1).2.1
  let f := ((D.sp.W j).frame.equivFun.symm.restrictScalars (𝓞 D.host.E)).toLinearMap
  have hsp' : Submodule.span D.host.E (Set.range (f ∘ₗ ι₀)) = ⊤ := by
    have : Set.range (f ∘ₗ ι₀) = (D.sp.W j).frame.equivFun.symm.toLinearMap '' Set.range ι₀ := by
      rw [← Set.range_comp]
      rfl
    rw [this, Submodule.span_image, hsp, Submodule.map_top, LinearEquiv.range]
  have h1 : ε = 1 := GlobalTheory.Member.sign_eq_one D H Dw j hj hrt hrt0 hp hq (f ∘ₗ ι₀) ε
    ((D.sp.W j).frame.equivFun.symm.injective.comp hL'.1) hsp' hε
  subst h1
  refine ⟨hL'.1, hsp, (GlobalTheory.Member.isom_iff_model Dw (D.sp.W j) rfl ι₀).1 fun x y => ?_⟩
  rw [hε x y, Units.val_one, Int.cast_one, _root_.one_mul]


set_option maxHeartbeats 2000000 in
theorem model_space_of_lawsJ : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → ∀ k : (T.U j σ).Comp, (∀ τ : D.host.E →+* ℂ, τ (T.Q.H.rt : D.host.E) = T.Q.H.rt0 → (τ ((T.U j σ).X k).ξ0).im < 0) ∧ ∃ φD : (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E), Function.Injective φD ∧ Submodule.span D.host.E (Set.range φD) = ⊤ ∧ ∀ x y, (((T.Q.Dw j).EF x y : ℤ) : ℚ) = Algebra.trace ℚ D.host.E (-((T.U j σ).X k).ξ0 * herm ((T.U j σ).X k).Gm (φD x) (φD y)) := by
  intro D T h j hj σ hσ k
  obtain ⟨hr, hW⟩ := h.modelW j hj σ hσ
  obtain ⟨-, hrt, hrt0, -⟩ := h.pins.1
  obtain ⟨hp, hq, -⟩ := h.pins.2.2.2 j hj
  obtain ⟨hr', -, -, -, -, -, -, hL, hI, -⟩ := h.adPin j hj σ hσ
  refine ⟨fun τ hτ => ?_, T.iota j, ?_⟩
  · rw [(hW k).2]
    exact GlobalTheory.Member.hostCMType_neg_constant_im_neg D τ (by rw [← hrt0, ← hrt, hτ])
  · rw [(hW k).1, (hW k).2]
    exact latEmb_model_of_eq D T.Q.H (T.Q.Dw j) j hj hrt hrt0 hp hq (T.V j σ) (h.spaceW j hj σ hσ) D.R.r hr
      (T.iota j) hL hI

end GlobalTheory.GeoLevel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHomActionRealCoordinatesEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHomActionRealCoordinatesEq
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

namespace GlobalTheory.RealWeilF

theorem actOF_iotaVF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → ∀ θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ),
      IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ → ∀ ι : (InfinitePlace F → ℂ) →+ AEF F E, IsChartF θ ι →
      ∀ (g : GAF σ JS) (h : GAF σ JT) (v : IxF F nS nT → ℂ),
        actOF σ JS JT g h (iotaVF ι v) = iotaVF ι (mMF σ JS JT θ (g, h) *ᵥ v) := by
  intro F E _ _ _ _ _ σ B _ nS nT JS JT _ _ ξ₀ _ _ θ _ ι hι g h v
  have hfin : ∀ u : IxF F nS nT → ℂ, (iotaVF ι u).map (finPartF F E) = 0 := fun u => real_iotaVF hι u
  have hL : (actOF σ JS JT g h (iotaVF ι v)).map (finPartF F E) = 0 := by
    unfold actOF
    rw [Matrix.map_mul, Matrix.map_mul, hfin, Matrix.mul_zero, Matrix.zero_mul]
  have hcpt : ∀ (u : IxF F nS nT → ℂ) w, compAtF θ w (iotaVF ι u) = GlobalTheory.RealWeil.cpt u w := by
    intro u w
    ext i j
    exact hι.comp _ w
  have hC : ∀ w, compAtF θ w (actOF σ JS JT g h (iotaVF ι v)) =
      compAtF θ w (iotaVF ι (mMF σ JS JT θ (g, h) *ᵥ v)) := by
    intro w
    have e : compAtF θ w (actOF σ JS JT g h (iotaVF ι v)) =
        compAtF θ w (mtF σ JT h) * compAtF θ w (iotaVF ι v) * compAtF θ w (mtF σ JS g⁻¹) := by
      unfold actOF compAtF
      rw [Matrix.map_mul, Matrix.map_mul]
    rw [e, hcpt, hcpt, mMF_apply, GlobalTheory.RealWeil.cpt_blk]
  ext i j
  rw [← sub_eq_zero]
  refine hι.ext _ ?_ fun w => ?_
  · have h1 : finPartF F E (actOF σ JS JT g h (iotaVF ι v) i j) = 0 := congrFun (congrFun hL i) j
    have h2 : finPartF F E (iotaVF ι (mMF σ JS JT θ (g, h) *ᵥ v) i j) = 0 := congrFun (congrFun (hfin _) i) j
    rw [RingHom.map_sub, h1, h2, sub_zero]
  · have h3 := congrFun (congrFun (hC w) i) j
    simp only [compAtF, Matrix.map_apply, RingHom.comp_apply] at h3
    rw [RingHom.map_sub, RingHom.map_sub, h3, sub_self]

end GlobalTheory.RealWeilF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHomActionRealCoordinatesEqStatement
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicHomAction_realCoordinates_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → ∀ θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ),
      IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ → ∀ ι : (InfinitePlace F → ℂ) →+ AEF F E, IsChartF θ ι →
      ∀ (g : GAF σ JS) (h : GAF σ JT) (v : IxF F nS nT → ℂ),
        actOF σ JS JT g h (iotaVF ι v) = iotaVF ι (mMF σ JS JT θ (g, h) *ᵥ v) := by
  first | exact @GlobalTheory.RealWeilF.actOF_iotaVF | exact GlobalTheory.RealWeilF.actOF_iotaVF | (intros; apply GlobalTheory.RealWeilF.actOF_iotaVF <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfinitesimalCharacterQuantumDet
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WignerGL GlobalTheory.WigAlg Formalism.REAL
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.WigCap

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def keep (π : CuspSub E a) : Subalgebra ℂ (Module.End ℂ (Sm E a)) where
  carrier := {z | ∀ φ ∈ π.V, z φ ∈ π.V}
  mul_mem' := fun hx hy φ h => hx _ (hy φ h)
  add_mem' := fun hx hy φ h => π.V.add_mem (hx φ h) (hy φ h)
  algebraMap_mem' := fun c φ h => π.V.smul_mem c h

def res (π : CuspSub E a) : keep π →ₐ[ℂ] Module.End ℂ π.V where
  toFun z := z.1.restrict z.2
  map_one' := LinearMap.ext fun φ => Subtype.ext rfl
  map_mul' _ _ := LinearMap.ext fun φ => Subtype.ext rfl
  map_zero' := LinearMap.ext fun φ => Subtype.ext rfl
  map_add' _ _ := LinearMap.ext fun φ => Subtype.ext rfl
  commutes' _ := LinearMap.ext fun φ => Subtype.ext rfl

theorem Eop_mem (π : CuspSub E a) (τ : E →+* ℂ) (i j : Fin a) : Eop τ i j ∈ keep π := by
  have h : ∀ X, lie E a X ∈ keep π := fun X φ hφ => π.stable (.lie X) φ hφ
  exact (keep π).smul_mem ((keep π).sub_mem (h _) ((keep π).smul_mem (h _) _)) _

theorem res_Eop (π : CuspSub E a) (τ : E →+* ℂ) (i j : Fin a) :
    res π ⟨Eop τ i j, Eop_mem π τ i j⟩ = cx τ (lieOp π) i j := by
  refine LinearMap.ext fun φ => Subtype.ext ?_
  rfl

end GlobalTheory.WigCap


open GlobalTheory.WigCap in
theorem GlobalTheory.capelli_cuspSub : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (τ : E →+* ℂ) (χ : Fin a → ℂ), π.HasInfChar τ (Multiset.map χ Finset.univ.val) → GlRel (cx τ (lieOp π)) ∧ ∀ u : ℂ, qdet (cx τ (lieOp π)) (u + ((a : ℂ) - 1) / 2) = algebraMap ℂ _ (∏ s, (u + χ s)) := by
  intro E _ _ _ a π τ χ hχ
  let X : Fin a → Fin a → keep π := fun i j => ⟨Eop τ i j, Eop_mem π τ i j⟩
  have hX : (fun i j => res π (X i j)) = cx τ (lieOp π) := funext fun i => funext fun j => res_Eop π τ i j
  have hval : (fun i j => (keep π).val (X i j)) = Eop τ := rfl
  constructor
  · intro i j k l
    have h := glRel_Eop (a := a) τ i j k l
    rw [← hX]
    simp only
    have h2 : X i j * X k l - X k l * X i j = (if j = k then X i l else 0) - (if l = i then X k j else 0) := by
      apply Subtype.ext
      simp only [Subalgebra.coe_sub, Subalgebra.coe_mul]
      rw [h]
      split_ifs <;> rfl
    rw [← map_mul, ← map_mul, ← map_sub, h2, map_sub]
    split_ifs <;> simp
  · intro u
    rw [← hX, ← map_qdet]
    refine LinearMap.ext fun φ => Subtype.ext ?_
    have e1 : ((keep π).val (qdet X (u + ((a : ℂ) - 1) / 2))) = cap τ u := by
      rw [map_qdet, hval]; rfl
    change ((keep π).val (qdet X (u + ((a : ℂ) - 1) / 2))) φ.1 = _
    rw [e1, hχ.2 u φ.1 φ.2, Multiset.map_map, Finset.prod_eq_multiset_prod]
    simp [Algebra.algebraMap_eq_smul_one]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharFinprodLocKMulInfEqOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharFinprodLocKMulInfEqOne
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.HCharUnit

theorem locK_eq_one {E : Type} [Field E] [NumberField E] (χ : HChar E) (k : Eˣ) (v : HeightOneSpectrum (𝓞 E))
    (hu : χ.UnrAt v) (ho : ordF v k = 0) : χ.locK v k = 1 := by
  apply hu
  show Valued.v (((k : E) : v.adicCompletion E)) = 1
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  have h0 : v.valuation E (k : E) ≠ 0 := by simp
  have hl : WithZero.log (v.valuation E (k : E)) = 0 := by
    unfold ordF at ho; omega
  rw [← WithZero.exp_log h0, hl, WithZero.exp_zero]

theorem finprod_locK_mul_inf : ∀ (E : Type) [Field E] [NumberField E] (χ : HChar E) (k : Eˣ),
    (Function.mulSupport fun w : Pl E => χ.locK w k).Finite ∧ (∏ᶠ w : Pl E, χ.locK w k) * χ.inf k = 1 := by
  intro E _ _ χ k
  have hT : ({v | ¬ χ.UnrAt v} ∪ {v : HeightOneSpectrum (𝓞 E) | ordF v k ≠ 0}).Finite :=
    Set.Finite.union (Filter.eventually_cofinite.mp (Formalism.L2.Fam.IdTrans.unrAe χ)) (GlobalTheory.HeckeProduct.finite_ordF k)
  set S := hT.toFinset with hSdef
  have hsub : (Function.mulSupport fun w : Pl E => χ.locK w k) ⊆ (S : Set (HeightOneSpectrum (𝓞 E))) := by
    intro v hv
    rw [hSdef, Set.Finite.coe_toFinset]
    by_contra h
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at h
    exact hv (locK_eq_one χ k v h.1 h.2)
  refine ⟨S.finite_toSet.subset hsub, ?_⟩
  have hS : ∀ v, v ∉ S → χ.UnrAt v := by
    intro v hv
    by_contra h
    exact hv (by rw [hSdef, Set.Finite.mem_toFinset]; exact Or.inl h)
  have hpr := Formalism.L2.Host.HChar.productRule χ S hS k
  have hrest : (∏ᶠ (v : HeightOneSpectrum (𝓞 E)) (_ : v ∉ S), χ.val v ^ ordF v k) = 1 := by
    apply finprod_eq_one_of_forall_eq_one
    intro v
    rw [finprod_eq_if]
    split_ifs with hv
    · rfl
    have : ordF v k = 0 := by
      by_contra h
      exact hv (by rw [hSdef, Set.Finite.mem_toFinset]; exact Or.inr h)
    rw [this, zpow_zero]
  rw [hrest, mul_one] at hpr
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub, mul_comm]
  exact hpr

end GlobalTheory.HCharUnit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharFinprodLocKMulInfEqOneStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChar_finprod_locK_mul_inf_eq_one : ∀ (E : Type) [Field E] [NumberField E] (χ : HChar E) (k : Eˣ), (Function.mulSupport fun w : Pl E => χ.locK w k).Finite ∧ (∏ᶠ w : Pl E, χ.locK w k) * χ.inf k = 1 := by
  first | exact @GlobalTheory.HCharUnit.finprod_locK_mul_inf | exact GlobalTheory.HCharUnit.finprod_locK_mul_inf | (intros; apply GlobalTheory.HCharUnit.finprod_locK_mul_inf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCentralizerLocalUnitaryCommOfSeparable
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCentralizerLocalUnitaryCommOfSeparable
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.CentComm

theorem commute_of_commute_separable_of_isAlgClosed {L : Type} [Field L] [IsAlgClosed L] {n : ℕ}
    {A g h : Matrix (Fin n) (Fin n) L} (hA : A.charpoly.Separable) (hg : Commute A g) (hh : Commute A h) :
    Commute g h := by
  set f := Matrix.toLin' A
  have hc : f.charpoly = A.charpoly := Matrix.charpoly_toLin' A
  have hfg : Commute f (Matrix.toLin' g) := hg.map Matrix.toLinAlgEquiv'
  have hfh : Commute f (Matrix.toLin' h) := hh.map Matrix.toLinAlgEquiv'
  have key : ∀ μ, Module.End.maxGenEigenspace f μ ≤
      LinearMap.ker (Matrix.toLin' g * Matrix.toLin' h - Matrix.toLin' h * Matrix.toLin' g) := fun μ v hv => by
    have h1 : Module.finrank L (Module.End.maxGenEigenspace f μ) ≤ 1 := by
      rw [LinearMap.finrank_maxGenEigenspace_eq, hc]; exact Polynomial.rootMultiplicity_le_one_of_separable hA μ
    by_cases h0 : v = 0
    · simp [h0]
    have hs : ∀ w ∈ Module.End.maxGenEigenspace f μ, ∃ c : L, c • v = w := fun w hw => by
      have h2 : Module.finrank L (Module.End.maxGenEigenspace f μ) = 1 := le_antisymm h1
        (Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨v, hv⟩, fun h => h0 (congrArg Subtype.val h)⟩)
      obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨v, hv⟩ : Module.End.maxGenEigenspace f μ)
        fun h => h0 (congrArg Subtype.val h)).1 h2 ⟨w, hw⟩
      exact ⟨c, congrArg Subtype.val hc⟩
    obtain ⟨c, hc⟩ := hs _ (Module.End.mapsTo_maxGenEigenspace_of_comm hfg μ hv)
    obtain ⟨d, hd⟩ := hs _ (Module.End.mapsTo_maxGenEigenspace_of_comm hfh μ hv)
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, ← hc, ← hd, map_smul,
      map_smul, ← hc, ← hd, smul_comm, sub_self]
  have h3 := iSup_le key
  rw [Module.End.iSup_maxGenEigenspace_eq_top, top_le_iff, LinearMap.ker_eq_top, sub_eq_zero] at h3
  exact Matrix.toLinAlgEquiv'.injective (by rw [map_mul, map_mul]; exact h3)

theorem commute_of_commute_separable {K : Type} [Field K] {n : ℕ} {A g h : Matrix (Fin n) (Fin n) K}
    (hA : A.charpoly.Separable) (hg : Commute A g) (hh : Commute A h) : Commute g h := by
  set φ := algebraMap K (AlgebraicClosure K)
  have hA' : (A.map φ).charpoly.Separable := by
    rw [Matrix.charpoly_map]; exact hA.map
  have hg' : Commute (A.map φ) (g.map φ) := by
    unfold Commute SemiconjBy; rw [← Matrix.map_mul, ← Matrix.map_mul, hg.eq]
  have hh' : Commute (A.map φ) (h.map φ) := by
    unfold Commute SemiconjBy; rw [← Matrix.map_mul, ← Matrix.map_mul, hh.eq]
  have := commute_of_commute_separable_of_isAlgClosed hA' hg' hh'
  unfold Commute SemiconjBy at this ⊢
  rw [← Matrix.map_mul, ← Matrix.map_mul] at this
  exact Matrix.map_injective φ.injective this

end GlobalTheory.BCT.CentComm

namespace GlobalTheory.BCT

theorem centComm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ (w : Pl E) (y : UL n w),
    y.1.val.charpoly.Separable → ∀ a ∈ twCent (MonoidHom.id (UL n w)) y, ∀ b ∈ twCent (MonoidHom.id (UL n w)) y,
      a * b = b * a := by
  intro E _ _ _ _ n w y hy a ha b hb
  have ha' : a.1.val * y.1.val = y.1.val * a.1.val := congrArg (fun z : UL n w => z.1.val) ha
  have hb' : b.1.val * y.1.val = y.1.val * b.1.val := congrArg (fun z : UL n w => z.1.val) hb
  have := CentComm.commute_of_commute_separable hy ha'.symm hb'.symm
  exact Subtype.ext (Units.ext this.eq)

end GlobalTheory.BCT
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCentralizerLocalUnitaryCommOfSeparableStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedCentralizer_localUnitary_comm_of_separable : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ (w : Pl E) (y : UL n w), y.1.val.charpoly.Separable → ∀ a ∈ twCent (MonoidHom.id (UL n w)) y, ∀ b ∈ twCent (MonoidHom.id (UL n w)) y, a * b = b * a := by
  first | exact @GlobalTheory.BCT.centComm | exact GlobalTheory.BCT.centComm | (intros; apply GlobalTheory.BCT.centComm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormRealCoordinateMatrixHermitianDetNeZ
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormRealCoordinateMatrixHermitianDetNeZ
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

namespace GlobalTheory.RealWeilF

theorem map_conjTranspose_of_herm {n : ℕ} (σ : E →ₐ[F] E) (hcm : ∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x))
    {J : Matrix (Fin n) (Fin n) E} (hJ : ∀ i j, σ (J j i) = J i j) (τ : E →+* ℂ) : (J.map τ)ᴴ = J.map τ := by
  ext i j
  simp only [conjTranspose_apply, map_apply]
  rw [← hcm, hJ]

theorem im_ne_zero_of_skew (σ : E →ₐ[F] E) (hcm : ∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x))
    {ξ₀ : E} (h0 : ξ₀ ≠ 0) (hσ : σ ξ₀ = -ξ₀) (τ : E →+* ℂ) : (τ ξ₀).im ≠ 0 := by
  intro him
  have h1 : star (τ ξ₀) = -τ ξ₀ := by rw [← hcm, hσ, map_neg]
  have hre : (τ ξ₀).re = 0 := by
    have := congrArg Complex.re h1
    simp only [Complex.star_def, Complex.conj_re, Complex.neg_re] at this
    linarith
  have : τ ξ₀ = 0 := Complex.ext hre him
  exact h0 ((map_eq_zero τ).1 this)

theorem hermitianFormRealCoordinateBlock_hermitian_det {nS nT : ℕ} (σ : E →ₐ[F] E) (hcm : ∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x))
    (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)
    (hS : IsHermND σ JS) (hT : IsHermND σ JT) (ξ₀ : E) (h0 : ξ₀ ≠ 0) (hσ : σ ξ₀ = -ξ₀)
    (tau : InfinitePlace F → (E →+* ℂ)) :
    (HMF JS JT ξ₀ tau)ᴴ = HMF JS JT ξ₀ tau ∧ (HMF JS JT ξ₀ tau).det ≠ 0 := by
  classical
  have hdS : ∀ w, IsUnit (JS.map (tau w)).det := fun w => by
    have e := RingHom.map_det (tau w) JS
    rw [RingHom.mapMatrix_apply] at e
    rw [← e]; exact (isUnit_iff_ne_zero.2 ((map_ne_zero (tau w)).2 hS.2))
  have hdT : ∀ w, IsUnit (JT.map (tau w)).det := fun w => by
    have e := RingHom.map_det (tau w) JT
    rw [RingHom.mapMatrix_apply] at e
    rw [← e]; exact (isUnit_iff_ne_zero.2 ((map_ne_zero (tau w)).2 hT.2))
  have hc : ∀ w, ((2 * (tau w ξ₀).im : ℝ) : ℂ) ≠ 0 := fun w => by
    have := im_ne_zero_of_skew σ hcm h0 hσ (tau w)
    exact_mod_cast mul_ne_zero two_ne_zero this
  constructor
  · unfold HMF
    rw [GlobalTheory.RealWeil.blk_conjTranspose]
    congr 1 <;> funext w
    · rw [conjTranspose_smul, map_conjTranspose_of_herm σ hcm hT.1]
      simp
    · rw [conjTranspose_nonsing_inv, map_conjTranspose_of_herm σ hcm hS.1]
  · have : HMF JS JT ξ₀ tau * GlobalTheory.RealWeil.blk (fun w => ((2 * (tau w ξ₀).im : ℝ) : ℂ)⁻¹ • (JT.map (tau w))⁻¹)
        (fun w => JS.map (tau w)) = 1 := by
      unfold HMF
      rw [GlobalTheory.RealWeil.blk_mul, ← GlobalTheory.RealWeil.blk_one]
      congr 1 <;> funext w
      · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ (hc w), one_smul,
          mul_nonsing_inv _ (hdT w)]
      · rw [mul_nonsing_inv _ (hdS w)]
    exact (isUnit_det_of_right_inverse this).ne_zero

end GlobalTheory.RealWeilF

theorem GlobalTheory.RealWeilF.HMF_herm_det : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      (HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1))ᴴ = HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1) ∧ (HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1)).det ≠ 0 := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ h0 hσ
  exact GlobalTheory.RealWeilF.hermitianFormRealCoordinateBlock_hermitian_det σ hB.cm.2.2.2 JS JT hS hT ξ₀ h0 hσ _
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormRealCoordinateMatrixHermitianDetNeZStatement
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianFormRealCoordinateMatrix_hermitian_det_ne_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      (HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1))ᴴ = HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1) ∧ (HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1)).det ≠ 0 := by
  first | exact @GlobalTheory.RealWeilF.HMF_herm_det | exact GlobalTheory.RealWeilF.HMF_herm_det | (intros; apply GlobalTheory.RealWeilF.HMF_herm_det <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIntersectionNumberEqGenericRankMul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIntersectionNumberEqGenericRankMul
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj

namespace GlobalTheory.VB

theorem lt_of_add_one_le_natCast {a : WithBot ℕ∞} {n : ℕ} (h : a + 1 ≤ (n : WithBot ℕ∞)) :
    a < (n : WithBot ℕ∞) := by
  induction a using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe m =>
    induction m using ENat.recTopCoe with
    | top =>
      exfalso
      rw [← WithBot.coe_one, ← WithBot.coe_add, top_add, ← WithBot.coe_natCast, WithBot.coe_le_coe] at h
      exact absurd h (not_le.mpr (ENat.coe_lt_top n))
    | coe m =>
      have h' : ((m + 1 : ℕ) : WithBot ℕ∞) ≤ (n : WithBot ℕ∞) := by exact_mod_cast h
      have : m + 1 ≤ n := by exact_mod_cast h'
      exact_mod_cast (show m < n by omega)

variable {Z : Scheme.{0}} [IsIntegral Z]

theorem suppDim_lt_of_genRank_eq_zero {n : ℕ} (hd : topologicalKrullDim Z ≤ (n : WithBot ℕ∞))
    {F : Z.Modules} [QCoh.IsFiniteQC F] (h : genRank F = 0) : QCoh.suppDim F < (n : WithBot ℕ∞) := by
  have := topologicalKrullDim_add_one_le (QCoh.isClosed_support F) isClosed_univ
    fun x _ => ⟨genericPoint Z, trivial, genRank_eq_zero_iff.1 h, genericPoint_specializes x⟩
  have e : topologicalKrullDim (Set.univ : Set Z) = topologicalKrullDim Z := by
    rw [← QCoh.suppDim_structureModule, QCoh.suppDim, QCoh.support_structureModule]
  rw [e] at this
  exact lt_of_add_one_le_natCast (this.trans hd)

variable {κ : Type} [Field κ] [Algebra κ Γ(Z, ⊤)]

theorem interNum_of_genRank_eq (hp : IsProjOver (strHom κ (X := Z))) {ι : Type} [Fintype ι]
    (hd : topologicalKrullDim Z ≤ (Fintype.card ι : ℕ)) {P : ι → LB Z} (hP : ∀ i, (P i).IsLB)
    (r : ℕ) : ∀ (G : Z.Modules) [QCoh.IsFiniteQC G], genRank G = r →
      interNum κ G P = r * interNum κ (structureModule Z) P := by
  have hf := algebraMap_eq_strHom κ Z
  have h1 : ∀ {F : Z.Modules} [QCoh.IsFiniteQC F], FiniteCohTwists κ F :=
    fun {F} _ => finiteCohTwists_of_isProjOver hf F hp
  obtain ⟨_, A, hA⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hp
  induction r with
  | zero =>
    intro G _ h
    rw [interNum_eq_zero_of_isProjOver hf G hp (suppDim_lt_of_genRank_eq_zero hd h) hP]
    simp
  | succ r ih =>
    intro G _ h
    obtain ⟨n, hn⟩ := (hA.eventually_isGloballyGenerated_twist G).exists
    have hM := isLB_lbPow hA.isLB n
    have := Twist.isFiniteQC_twist (F := G) hM
    have hr : genRank (twist G (lbPow A n)) = r + 1 := (genRank_twist hM).trans h
    obtain ⟨s, hs⟩ := exists_germ_ne_zero hn (by omega)
    have := mono_sectionHom s hs
    have e₁ : interNum κ (twist G (lbPow A n)) P = interNum κ G P :=
      (diffVanish_chiPic_of_isProjOver (d := Fintype.card ι) hf G hp
        ((QCoh.suppDim_le G).trans hd)).interNum_twist le_rfl hP hM
    have e₂ := interNum_cokernel (k := κ) (QCoh.sectionHom s) hP h1 h1
    have e₃ := genRank_cokernel (QCoh.sectionHom s)
    rw [(isVB_structureModule Z).genRank_eq, hr] at e₃
    rw [ih _ (by omega)] at e₂
    push_cast
    linarith

end GlobalTheory.VB

theorem GlobalTheory.VB.interNum_eq_genRank_mul_of_isProjOver : ∀ (κ : Type) [Field κ] (Z : Scheme.{0})
    [IsIntegral Z] [Algebra κ Γ(Z, ⊤)], IsProjOver (strHom κ (X := Z)) → ∀ (ι : Type) [Fintype ι],
    topologicalKrullDim Z ≤ (Fintype.card ι : ℕ) → ∀ (G : Z.Modules) [GlobalTheory.QCoh.IsFiniteQC G]
    (P : ι → LB Z), (∀ i, (P i).IsLB) →
    interNum κ G P = (GlobalTheory.VB.genRank G : ℤ) * interNum κ (structureModule Z) P :=
  fun _ _ _ _ _ hp _ _ hd G _ _ hP => GlobalTheory.VB.interNum_of_genRank_eq hp hd hP _ G rfl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIntersectionNumberEqGenericRankMulStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleIntersectionNumber_eq_genericRank_mul : ∀ (κ : Type) [Field κ] (Z : Scheme.{0}) [IsIntegral Z] [Algebra κ Γ(Z, ⊤)], IsProjOver (strHom κ (X := Z)) → ∀ (ι : Type) [Fintype ι], topologicalKrullDim Z ≤ (Fintype.card ι : ℕ) → ∀ (G : Z.Modules) [GlobalTheory.QCoh.IsFiniteQC G] (P : ι → LB Z), (∀ i, (P i).IsLB) → interNum κ G P = (GlobalTheory.VB.genRank G : ℤ) * interNum κ (structureModule Z) P := by
  first | exact @GlobalTheory.VB.interNum_eq_genRank_mul_of_isProjOver | exact GlobalTheory.VB.interNum_eq_genRank_mul_of_isProjOver | (intros; apply GlobalTheory.VB.interNum_eq_genRank_mul_of_isProjOver <;> assumption)
end
end
