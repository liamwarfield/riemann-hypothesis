module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergArchimedeanDiffOperatorHasDerivAtFamil
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurableLevelIndicatorCoefficientTestFunction
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurableLevelIndicatorCoefficientTestFunction
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SepPer.CoefMeas

theorem measurable_coef : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (Λ : Lat V) (𝔪 : Ideal (𝓞 D.host.E)), IsSelfDualC V Λ → 𝔪 ≠ ⊥ → ∀ (v a : ∀ τ, M.H τ), Measurable (coef θ M (congLev D.sp.cm V.gram Λ 𝔪) v a) := by
  intro D θ hθ V S M Λ 𝔪 hΛ h𝔪 v a
  classical
  have h1 := GlobalTheory.SepPer.CoefCont.continuous_coefR D θ hθ V S M v a
  have hfull : Submodule.IsFullLattice D.host.E Λ := by
    haveI : Submodule.IsLattice D.host.E Λ := hΛ.1
    refine ⟨?_⟩
    obtain ⟨s, hs⟩ := hΛ.1.fg
    apply eq_top_iff.mpr
    intro y _
    let f : (Fin V.rank → D.host.E) → D.host.E := fun x =>
      ∑ i, ∑ j, star (x i) * V.gram i j * y j
    obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 D.host.E)) s f
    have ha0 : (algebraMap (𝓞 D.host.E) D.host.E a) ≠ 0 := by
      exact (FaithfulSMul.algebraMap_injective _ _).ne (mem_nonZeroDivisors_iff_ne_zero.mp a.2)
    let P : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) := {
      carrier := {x | ∃ b : 𝓞 D.host.E, (b : D.host.E) = (algebraMap (𝓞 D.host.E) D.host.E a) * f x}
      zero_mem' := by refine ⟨0, ?_⟩; simp [f]
      add_mem' := by
        rintro x z ⟨b, hb⟩ ⟨c, hc⟩
        refine ⟨b + c, ?_⟩
        change (b : D.host.E) + c = _
        rw [hb, hc]
        simp [f, map_add, add_mul, Finset.sum_add_distrib, mul_add]
      smul_mem' := by
        rintro c x ⟨b, hb⟩
        refine ⟨RingOfIntegers.mapRingHom (starRingEnd D.host.E) c * b, ?_⟩
        simp only [map_mul, hb, f, Pi.smul_apply, Algebra.smul_def, map_mul, RingOfIntegers.mapRingHom_apply, star_mul]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        change star (c : D.host.E) * _ = _
        ring }
    have hsP : (s : Set (Fin V.rank → D.host.E)) ⊆ P := by
      intro x hx
      obtain ⟨b, hb⟩ := ha x hx
      exact ⟨b, by simpa [Algebra.smul_def] using hb⟩
    have hy : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Λ := by
      apply (hΛ.2 _).2
      intro x hx
      have hxP : x ∈ P := (hs ▸ Submodule.span_le.mpr hsP) hx
      obtain ⟨b, hb⟩ := hxP
      refine ⟨b, ?_⟩
      rw [hb]
      dsimp only [f, Pi.smul_apply]
      simp only [smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hy' : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) :=
      Submodule.subset_span hy
    have := (Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E))).smul_mem
      (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ hy' 
    change (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ •
      ((algebraMap (𝓞 D.host.E) D.host.E a) • y) ∈ _ at this
    rw [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ ha0, one_smul] at this
    exact this
  have h2 := (congLev_open_compact V hfull h𝔪).1
  unfold coef
  exact Measurable.ite h2.measurableSet h1.measurable measurable_const

end GlobalTheory.SepPer.CoefMeas
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurableLevelIndicatorCoefficientTestFunctionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurable_level_indicator_coefficient_test_function : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (Λ : Lat V) (𝔪 : Ideal (𝓞 D.host.E)), IsSelfDualC V Λ → 𝔪 ≠ ⊥ → ∀ (v a : ∀ τ, M.H τ), Measurable (coef θ M (congLev D.sp.cm V.gram Λ 𝔪) v a) := by
  first | exact @GlobalTheory.SepPer.CoefMeas.measurable_coef | exact GlobalTheory.SepPer.CoefMeas.measurable_coef | (intros; apply GlobalTheory.SepPer.CoefMeas.measurable_coef <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalFullRankBesselBasePoint
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalFullRankBesselBasePoint
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.Asc.FBx

open GlobalTheory.Unf.FB (mul_mul_mul_of_gram selFirst lastE ell_succ_eq)

variable {D : D7} {σ : ℕ}

def xRat (B : BesL D σ) : Matrix (Fin B.V.rank) (Fin (σ + 1)) D.host.E :=
  B.d.e * selFirst D σ + B.d.i₀ * vecMulVec (vecB B.o B.ζ) (lastE D σ)

theorem zEll_eq_rat (B : BesL D σ) : zEll B.L (σ + 1) B.ζ = rat (vecMulVec B.ζ (lastE D σ)) := by
  funext i j
  simp [zEll, rat, ratV, vecMulVec, ell_succ_eq]

theorem rat_xRat (B : BesL D σ) : rat (xRat B) = xLast B.d (vecB B.o B.ζ) := by
  have hne : ∀ x : Fin σ, (Fin.last σ = x.castSucc) ↔ False := fun x => iff_false_intro (Fin.castSucc_lt_last x).ne'
  funext k j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp [xRat, xLast, rat, selFirst, lastE, Matrix.mul_apply, vecMulVec, HypDec.j0, mulVec, dotProduct, ratV,
      vecB, hne]
  · simp [xRat, xLast, rat, selFirst, lastE, Matrix.mul_apply, vecMulVec, HypDec.jX, mulVec, dotProduct, ratV,
      vecB]

theorem gram_xRat (B : BesL D σ) :
    (xRat B)ᴴ * B.V.gram * xRat B =
      (vecMulVec B.ζ (lastE D σ))ᴴ * B.L.gram * vecMulVec B.ζ (lastE D σ) := by
  have hXX := mul_mul_mul_of_gram (n := Fin (σ + 1)) B.d.ee
  have h0X := mul_mul_mul_of_gram (n := Fin (σ + 1)) B.d.i₀e
  have hX0 : B.d.eᴴ * B.V.gram * B.d.i₀ = 0 := by
    have := congrArg conjTranspose B.d.i₀e
    rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, gram_conjTranspose, conjTranspose_zero,
      ← Matrix.mul_assoc] at this
  have hX0' := mul_mul_mul_of_gram (n := Fin (σ + 1)) hX0
  have h00 := mul_mul_mul_of_gram (n := Fin (σ + 1)) B.d.iso
  have hBB := mul_mul_mul_of_gram (n := Fin (σ + 1)) B.o.isoB
  have hz : vecMulVec (vecB B.o B.ζ) (lastE D σ) = B.o.iB * vecMulVec B.ζ (lastE D σ) := by
    rw [vecB, mul_vecMulVec]
  rw [xRat, hz]
  simp only [conjTranspose_add, conjTranspose_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, hXX, h0X, hX0',
    h00, hBB, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]

theorem gramSkew_xRat (B : BesL D σ) :
    GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew B.V (rat (xRat B) : Mx D B.V.rank (σ + 1)) =
      GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew B.L (zEll B.L (σ + 1) B.ζ) := by
  rw [zEll_eq_rat, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew, gram_rat _ (gram_xRat B), gram_rat B.L rfl]

theorem linearIndependent_xRat (B : BesL D σ) : LinearIndependent D.host.E (xRat B).transpose := by
  refine Fintype.linearIndependent_iff.2 ?_
  intro g hg
  have hv : xRat B *ᵥ g = 0 := by
    funext k
    have := congrFun hg k
    simpa [Finset.sum_apply, mulVec, dotProduct, mul_comm] using this
  have h0 : B.d.e'ᴴ * B.V.gram * B.d.i₀ = 0 := by
    have := congrArg conjTranspose B.d.i₀e'
    rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, gram_conjTranspose, conjTranspose_zero,
      ← Matrix.mul_assoc] at this
  have hq : (B.d.e'ᴴ * B.V.gram) * xRat B = selFirst D σ := by
    rw [xRat, Matrix.mul_add, ← Matrix.mul_assoc, B.d.e'e, Matrix.one_mul, ← Matrix.mul_assoc, h0, Matrix.zero_mul,
      add_zero]
  have h1 : selFirst D σ *ᵥ g = 0 := by rw [← hq, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  have h2 : ((vecMulVec B.ζ (lastE D σ))ᴴ * B.L.gram * vecMulVec B.ζ (lastE D σ)) *ᵥ g = 0 := by
    rw [← gram_xRat B, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  intro i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · have h3 := congrFun h2 (Fin.last σ)
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, vecMulVec_mulVec, conjTranspose_vecMulVec, vecMulVec_mulVec]
      at h3
    simp [lastE, mulVec_smul] at h3
    rcases h3 with h3 | h3
    · exact h3
    · exact absurd h3 B.line.2
  · have := congrFun h1 i
    simpa [selFirst, mulVec, dotProduct] using this

theorem exists_rat_eq_xLast : ∀ (D : D7) (σ : ℕ) (B : BesL D σ), ∃ x ∈ {x : Matrix (Fin B.V.rank) (Fin (σ + 1)) D.host.E |
    LinearIndependent D.host.E x.transpose ∧ GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew B.V (rat x : Mx D B.V.rank (σ + 1)) =
      GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew B.L (zEll B.L (σ + 1) B.ζ)}, (rat x : Mx D B.V.rank (σ + 1)) = xLast B.d (vecB B.o B.ζ) :=
  fun _ _ B => ⟨xRat B, ⟨linearIndependent_xRat B, gramSkew_xRat B⟩, rat_xRat B⟩

end GlobalTheory.Asc.FBx

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalFullRankBesselBasePointStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_fullRank_besselBasePoint : ∀ (D : D7) (σ : ℕ) (B : BesL D σ), ∃ x ∈ {x : Matrix (Fin B.V.rank) (Fin (σ + 1)) D.host.E | LinearIndependent D.host.E x.transpose ∧ GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew B.V (rat x : Mx D B.V.rank (σ + 1)) = GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew B.L (zEll B.L (σ + 1) B.ζ)}, (rat x : Mx D B.V.rank (σ + 1)) = xLast B.d (vecB B.o B.ζ) := by
  first | exact @GlobalTheory.Asc.FBx.exists_rat_eq_xLast | exact GlobalTheory.Asc.FBx.exists_rat_eq_xLast | (intros; apply GlobalTheory.Asc.FBx.exists_rat_eq_xLast <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsConjugateInverseStaircaseModulusIdeal
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsConjugateInverseStaircaseModulusIdeal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.ConjIdeal

variable {E : Type} [Field E] [NumberField E]

theorem map_mem_mul (c : E →+* E) {A A' B B' : FractionalIdeal (𝓞 E)⁰ E}
    (hA : ∀ x ∈ A', c x ∈ A) (hB : ∀ x ∈ B', c x ∈ B) : ∀ x ∈ A' * B', c x ∈ A * B := by
  intro x hx
  refine FractionalIdeal.mul_induction_on hx (fun i hi j hj => ?_) (fun y z hy hz => ?_)
  · rw [map_mul]; exact FractionalIdeal.mul_mem_mul (hA i hi) (hB j hj)
  · rw [map_add (f := _)]
    exact FractionalIdeal.mem_coe.1 (Submodule.add_mem _ (FractionalIdeal.mem_coe.2 hy) (FractionalIdeal.mem_coe.2 hz))

theorem conj_symm (c : E →+* E) (hc : ∀ x, c (c x) = x) {I I' : FractionalIdeal (𝓞 E)⁰ E}
    (h : ∀ x, x ∈ I' ↔ c x ∈ I) : ∀ x, x ∈ I ↔ c x ∈ I' := fun x => by rw [h, hc]

theorem conj_mul (c : E →+* E) (hc : ∀ x, c (c x) = x) {A A' B B' : FractionalIdeal (𝓞 E)⁰ E}
    (hA : ∀ x, x ∈ A' ↔ c x ∈ A) (hB : ∀ x, x ∈ B' ↔ c x ∈ B) : ∀ x, x ∈ A' * B' ↔ c x ∈ A * B := by
  intro x
  refine ⟨map_mem_mul c (fun y hy => (hA y).1 hy) (fun y hy => (hB y).1 hy) x, fun h => ?_⟩
  have := map_mem_mul c (fun y hy => (conj_symm c hc hA y).1 hy) (fun y hy => (conj_symm c hc hB y).1 hy) _ h
  rwa [hc] at this

theorem conj_pow (c : E →+* E) (hc : ∀ x, c (c x) = x) (h1 : ∀ x, x ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) ↔ c x ∈ (1 : FractionalIdeal (𝓞 E)⁰ E))
    {A A' : FractionalIdeal (𝓞 E)⁰ E} (hA : ∀ x, x ∈ A' ↔ c x ∈ A) (n : ℕ) : ∀ x, x ∈ A' ^ n ↔ c x ∈ A ^ n := by
  induction n with
  | zero => simp only [pow_zero]; exact h1
  | succ n ih => simpa only [pow_succ] using conj_mul c hc ih hA

theorem conj_ne_zero (c : E →+* E) (hc : ∀ x, c (c x) = x) {B B' : FractionalIdeal (𝓞 E)⁰ E}
    (hB : ∀ x, x ∈ B' ↔ c x ∈ B) (h0 : B ≠ 0) : B' ≠ 0 := by
  intro h
  apply h0
  rw [FractionalIdeal.eq_zero_iff] at h ⊢
  intro x hx
  have := h (c x) ((hB (c x)).2 (by rwa [hc]))
  rw [← hc x, this, map_zero]

theorem conj_inv (c : E →+* E) (hc : ∀ x, c (c x) = x) (h1 : ∀ x, x ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) ↔ c x ∈ (1 : FractionalIdeal (𝓞 E)⁰ E))
    {B B' : FractionalIdeal (𝓞 E)⁰ E} (hB : ∀ x, x ∈ B' ↔ c x ∈ B) (h0 : B ≠ 0) :
    ∀ x, x ∈ B'⁻¹ ↔ c x ∈ B⁻¹ := by
  intro x
  have := GlobalTheory.ChiGrid.StairConj.mem_mul_inv_iff c hc (map_mul c) h0 (conj_ne_zero c hc hB h0) h1 hB x
  simpa only [one_mul] using this

end GlobalTheory.ConjIdeal

namespace GlobalTheory.ConjIdeal

theorem stA_modul_conj_inv : ∀ {D : D7} {T : Type} {L : LevCh D T} (P : Places L) (sc : Consts) (a b : ℕ), ∃ I' : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E, P.stA sc ^ a * (P.stAbar sc ^ a)⁻¹ * (((P.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ^ b * (((P.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ^ b)⁻¹) * I' = 1 ∧ ∀ x : D.host.E, x ∈ I' ↔ star x ∈ P.stA sc ^ a * (P.stAbar sc ^ a)⁻¹ * (((P.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ^ b * (((P.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ^ b)⁻¹) := by
  intro D T L P sc a b
  have hs : ∀ x : D.host.E, star x = D.host.conj x := bridge_star_holds D.R D.host
  let c : D.host.E →+* D.host.E := (D.host.conj : D.host.E ≃ₐ[ℚ] D.host.E).toRingEquiv.toRingHom
  have hcx : ∀ x, c x = D.host.conj x := fun _ => rfl
  have hc : ∀ x, c (c x) = x := fun x => Formalism.L2.Pj.conj_conj D x
  have h1 : ∀ x, x ∈ (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ↔ c x ∈ (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
    have k : ∀ x, x ∈ (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) → c x ∈ (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
      intro x hx
      obtain ⟨z, rfl⟩ := (FractionalIdeal.mem_one_iff (𝓞 D.host.E)⁰).1 hx
      exact (FractionalIdeal.mem_one_iff (𝓞 D.host.E)⁰).2 ⟨D.host.conj • z, Formalism.L2.Pj.algebraMap_gal_smul D _ z⟩
    exact fun x => ⟨k x, fun h => by simpa only [hc] using k _ h⟩
  obtain ⟨hA0, hA⟩ := (GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).2 T L P sc
  have hA' : ∀ x, x ∈ P.stAbar sc ↔ c x ∈ P.stA sc := fun x => by rw [hcx, ← hs]; exact hA x
  set M : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E := ((P.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) with hMdef
  set Mb : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E := ((P.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) with hMbdef
  have hM : ∀ x, x ∈ M ↔ c x ∈ Mb := fun x => GlobalTheory.ChiGrid.StairConj.mem_coe_iff D _ x
  have hM0 : M ≠ 0 := by rw [hMdef, Ne, FractionalIdeal.coeIdeal_eq_zero]; exact P.modul_ne_bot sc
  have hMb0 : Mb ≠ 0 := conj_ne_zero c hc (conj_symm c hc hM) hM0
  have hAb0 : P.stAbar sc ≠ 0 := conj_ne_zero c hc hA' hA0
  refine ⟨P.stAbar sc ^ a * (P.stA sc ^ a)⁻¹ * (Mb ^ b * (M ^ b)⁻¹), ?_, ?_⟩
  · have e1 : P.stA sc ^ a ≠ 0 := pow_ne_zero _ hA0
    have e2 : P.stAbar sc ^ a ≠ 0 := pow_ne_zero _ hAb0
    have e3 : M ^ b ≠ 0 := pow_ne_zero _ hM0
    have e4 : Mb ^ b ≠ 0 := pow_ne_zero _ hMb0
    calc P.stA sc ^ a * (P.stAbar sc ^ a)⁻¹ * (M ^ b * (Mb ^ b)⁻¹) *
          (P.stAbar sc ^ a * (P.stA sc ^ a)⁻¹ * (Mb ^ b * (M ^ b)⁻¹))
        = (P.stA sc ^ a * (P.stA sc ^ a)⁻¹) * (P.stAbar sc ^ a * (P.stAbar sc ^ a)⁻¹) *
          ((M ^ b * (M ^ b)⁻¹) * (Mb ^ b * (Mb ^ b)⁻¹)) := by ac_rfl
      _ = 1 := by rw [mul_inv_cancel₀ e1, mul_inv_cancel₀ e2, mul_inv_cancel₀ e3, mul_inv_cancel₀ e4]; simp
  · intro x
    rw [hs]
    exact conj_mul c hc (conj_mul c hc (conj_pow c hc h1 hA' a) (conj_inv c hc h1 (conj_pow c hc h1 (conj_symm c hc hA') a) (pow_ne_zero _ hAb0)))
      (conj_mul c hc (conj_pow c hc h1 (conj_symm c hc hM) b) (conj_inv c hc h1 (conj_pow c hc h1 hM b) (pow_ne_zero _ hMb0))) x

end GlobalTheory.ConjIdeal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsConjugateInverseStaircaseModulusIdealStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conjugate_inverse_staircase_modulus_ideal : ∀ {D : D7} {T : Type} {L : LevCh D T} (P : Places L) (sc : Consts) (a b : ℕ), ∃ I' : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E, P.stA sc ^ a * (P.stAbar sc ^ a)⁻¹ * (((P.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ^ b * (((P.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ^ b)⁻¹) * I' = 1 ∧ ∀ x : D.host.E, x ∈ I' ↔ star x ∈ P.stA sc ^ a * (P.stAbar sc ^ a)⁻¹ * (((P.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ^ b * (((P.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ^ b)⁻¹) := by
  first | exact @GlobalTheory.ConjIdeal.stA_modul_conj_inv | exact GlobalTheory.ConjIdeal.stA_modul_conj_inv | (intros; apply GlobalTheory.ConjIdeal.stA_modul_conj_inv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SetIntegralPreimageEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SetIntegralPreimageEqZero
open MeasureTheory
open scoped NNReal ENNReal

noncomputable section

namespace GlobalTheory.FourierPush

theorem real_case {Y : Type} [MeasurableSpace Y] (m : Measure Y) (G : Y → ℝ) (hG : Integrable G m)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (p : Y → E) (hp : Measurable p)
    (h : ∀ l : E →L[ℝ] ℝ, ∫ y, Complex.exp ((l (p y) : ℂ) * Complex.I) * ((G y : ℝ) : ℂ) ∂m = 0)
    (s : Set E) (hs : MeasurableSet s) : ∫ y in p ⁻¹' s, G y ∂m = 0 := by
  let P := m.withDensity fun y => ENNReal.ofReal (G y)
  let P' := m.withDensity fun y => ENNReal.ofReal (-G y)
  haveI : IsFiniteMeasure P := isFiniteMeasure_withDensity_ofReal hG.2
  haveI : IsFiniteMeasure P' := isFiniteMeasure_withDensity_ofReal hG.neg.2
  have hcont : ∀ l : E →L[ℝ] ℝ, Continuous fun x : E => Complex.exp ((l x : ℂ) * Complex.I) :=
    fun l => by fun_prop
  have hbd : ∀ (l : E →L[ℝ] ℝ) (y : Y), ‖Complex.exp ((l (p y) : ℂ) * Complex.I)‖ ≤ 1 :=
    fun l y => (Complex.norm_exp_ofReal_mul_I _).le
  have hmeas : ∀ l : E →L[ℝ] ℝ,
      AEStronglyMeasurable (fun y => Complex.exp ((l (p y) : ℂ) * Complex.I)) m :=
    fun l => ((hcont l).measurable.comp hp).aestronglyMeasurable
  have e1 : ∀ l : E →L[ℝ] ℝ, charFunDual (P.map p) l
      = ∫ y, ((G y).toNNReal : ℝ) • Complex.exp ((l (p y) : ℂ) * Complex.I) ∂m := by
    intro l
    rw [charFunDual_apply, integral_map hp.aemeasurable (hcont l).aestronglyMeasurable]
    exact integral_withDensity_eq_integral_smul₀ hG.aemeasurable.real_toNNReal _
  have e2 : ∀ l : E →L[ℝ] ℝ, charFunDual (P'.map p) l
      = ∫ y, ((-G y).toNNReal : ℝ) • Complex.exp ((l (p y) : ℂ) * Complex.I) ∂m := by
    intro l
    rw [charFunDual_apply, integral_map hp.aemeasurable (hcont l).aestronglyMeasurable]
    exact integral_withDensity_eq_integral_smul₀ hG.neg.aemeasurable.real_toNNReal _
  have hmap : P.map p = P'.map p := by
    refine Measure.ext_of_charFunDual (funext fun l => ?_)
    rw [e1, e2, ← sub_eq_zero]
    have i1 : Integrable (fun y => ((G y).toNNReal : ℝ) • Complex.exp ((l (p y) : ℂ) * Complex.I)) m :=
      hG.real_toNNReal.smul_of_top_left
        (memLp_top_of_bound (hmeas l) 1 (Filter.Eventually.of_forall (hbd l)))
    have i2 : Integrable (fun y => ((-G y).toNNReal : ℝ) • Complex.exp ((l (p y) : ℂ) * Complex.I)) m :=
      hG.neg.real_toNNReal.smul_of_top_left
        (memLp_top_of_bound (hmeas l) 1 (Filter.Eventually.of_forall (hbd l)))
    rw [← integral_sub i1 i2, ← h l]
    congr 1; funext y
    rw [← sub_smul, Complex.real_smul, mul_comm]
    congr 2
    simp only [Real.coe_toNNReal']
    rcases le_total 0 (G y) with h' | h'
    · rw [max_eq_left h', max_eq_right (by linarith)]; simp
    · rw [max_eq_right h', max_eq_left (by linarith)]; simp
  have hval : ∀ f : Y → ℝ, ∫⁻ y in p ⁻¹' s, ENNReal.ofReal (f y) ∂m
      = (m.withDensity fun y => ENNReal.ofReal (f y)).map p s := fun f => by
    rw [Measure.map_apply hp hs, withDensity_apply _ (hp hs)]
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hG.integrableOn, hval G,
    hval (fun y => -G y)]
  change (P.map p s).toReal - (P'.map p s).toReal = 0
  rw [hmap, sub_self]

theorem setIntegral_preimage_eq_zero (Y : Type) [MeasurableSpace Y] (m : Measure Y) (F : Y → ℂ)
    (hF : Integrable F m) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (p : Y → E) (hp : Measurable p)
    (h : ∀ l : E →L[ℝ] ℝ, ∫ y, Complex.exp ((l (p y) : ℂ) * Complex.I) * F y ∂m = 0)
    (s : Set E) (hs : MeasurableSet s) : ∫ y in p ⁻¹' s, F y ∂m = 0 := by
  have hcont : ∀ l : E →L[ℝ] ℝ, Continuous fun x : E => Complex.exp ((l x : ℂ) * Complex.I) :=
    fun l => by fun_prop
  have hI : ∀ l : E →L[ℝ] ℝ, Integrable (fun y => Complex.exp ((l (p y) : ℂ) * Complex.I) * F y) m :=
    fun l => hF.bdd_mul ((hcont l).measurable.comp hp).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => (Complex.norm_exp_ofReal_mul_I _).le)
  have hic : Integrable (fun y => (starRingEnd ℂ) (F y)) m := by
    refine ⟨hF.1.star, ?_⟩
    simpa [HasFiniteIntegral] using hF.2
  have hI' : ∀ l : E →L[ℝ] ℝ,
      Integrable (fun y => Complex.exp ((l (p y) : ℂ) * Complex.I) * (starRingEnd ℂ) (F y)) m :=
    fun l => hic.bdd_mul ((hcont l).measurable.comp hp).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => (Complex.norm_exp_ofReal_mul_I _).le)
  have hconj : ∀ (l : E →L[ℝ] ℝ) (x : E),
      (starRingEnd ℂ) (Complex.exp ((((-l) x : ℝ) : ℂ) * Complex.I)) = Complex.exp (((l x : ℝ) : ℂ) * Complex.I) := by
    intro l x
    rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
    congr 1
    simp
  have hc' : ∀ l : E →L[ℝ] ℝ, ∫ y, Complex.exp ((l (p y) : ℂ) * Complex.I) * (starRingEnd ℂ) (F y) ∂m = 0 := by
    intro l
    have := congrArg (starRingEnd ℂ) (h (-l))
    rw [← integral_conj, map_zero] at this
    simpa only [map_mul, hconj] using this
  have hre : ∀ l : E →L[ℝ] ℝ,
      ∫ y, Complex.exp ((l (p y) : ℂ) * Complex.I) * (((F y).re : ℝ) : ℂ) ∂m = 0 := fun l => by
    simp only [Complex.re_eq_add_conj, mul_div_assoc', mul_add]
    rw [integral_div, integral_add (hI l) (hI' l), h l, hc' l]; simp
  have him : ∀ l : E →L[ℝ] ℝ,
      ∫ y, Complex.exp ((l (p y) : ℂ) * Complex.I) * (((F y).im : ℝ) : ℂ) ∂m = 0 := fun l => by
    simp only [Complex.im_eq_sub_conj, mul_div_assoc', mul_sub]
    rw [integral_div, integral_sub (hI l) (hI' l), h l, hc' l]; simp
  have h1 := real_case m (fun y => (F y).re) hF.re p hp hre s hs
  have h2 := real_case m (fun y => (F y).im) hF.im p hp him s hs
  apply Complex.ext
  · rw [Complex.zero_re, ← h1]
    exact (integral_re hF.integrableOn).symm
  · rw [Complex.zero_im, ← h2]
    exact (integral_im hF.integrableOn).symm

end GlobalTheory.FourierPush

end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SetIntegralPreimageEqZeroStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.setIntegral_preimage_eq_zero_of_fourier_eq_zero : ∀ (Y : Type) [MeasurableSpace Y] (m : Measure Y) (F : Y → ℂ), Integrable F m → ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (p : Y → E), Measurable p → (∀ l : E →L[ℝ] ℝ, ∫ y, Complex.exp ((l (p y) : ℂ) * Complex.I) * F y ∂m = 0) → ∀ s : Set E, MeasurableSet s → ∫ y in p ⁻¹' s, F y ∂m = 0 := by
  first | exact @GlobalTheory.FourierPush.setIntegral_preimage_eq_zero | exact GlobalTheory.FourierPush.setIntegral_preimage_eq_zero | (intros; apply GlobalTheory.FourierPush.setIntegral_preimage_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianSkewAdjointMemAdjointHomLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianSkewAdjointMemAdjointHomLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.AdjLatO

variable {D : D7}

theorem incA_mul_tmul' (g e : D.host.E) (x : AF D.host.F) :
    incA D g * (x ⊗ₜ[D.host.F] e) = x ⊗ₜ[D.host.F] (g * e) := by
  change ((1 : AF D.host.F) ⊗ₜ[D.host.F] g) * _ = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem tmul_mul_incA' (g e : D.host.E) (x : AF D.host.F) :
    (x ⊗ₜ[D.host.F] e) * incA D g = x ⊗ₜ[D.host.F] (e * g) := by
  change _ * ((1 : AF D.host.F) ⊗ₜ[D.host.F] g) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]

def tensM (x : AF D.host.F) {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) : Mx D m n :=
  M.map fun e => x ⊗ₜ[D.host.F] e

theorem rat_mul_tensM (x : AF D.host.F) {l m n : ℕ} (G : Matrix (Fin l) (Fin m) D.host.E)
    (M : Matrix (Fin m) (Fin n) D.host.E) : rat G ⬝ tensM x M = tensM x (G * M) := by
  ext i j
  simp only [tensM, rat, Matrix.mul_apply, Matrix.map_apply, incA_mul_tmul', TensorProduct.tmul_sum]

theorem tensM_mul_rat (x : AF D.host.F) {l m n : ℕ} (M : Matrix (Fin l) (Fin m) D.host.E)
    (G : Matrix (Fin m) (Fin n) D.host.E) : tensM x M ⬝ rat G = tensM x (M * G) := by
  ext i j
  simp only [tensM, rat, Matrix.mul_apply, Matrix.map_apply, tmul_mul_incA', TensorProduct.tmul_sum]

theorem adj_tensM (x : AF D.host.F) {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) :
    adj (tensM x M) = tensM x Mᴴ := by
  ext i j; rfl

theorem xi0_inv_smul_starAdj (S T : HSp D) (x : WO S T) :
    incA D D.host.xi0⁻¹ • GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj S T x = giA S ⬝ (adj x ⬝ gA T) := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj, smul_smul, ← map_mul, inv_mul_cancel₀ GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero, map_one, one_smul]

def genT (T : HSp D) {n : ℕ} (x : AF D.host.F) (t : Fin T.rank → D.host.E) (u : Fin n → D.host.E) :
    Matrix (Fin n) (Fin T.rank) (AE D) :=
  Matrix.of fun p q => x ⊗ₜ[D.host.F] (u p * ∑ i, star (t i) * T.gram i q)

theorem genT_add (T : HSp D) {n : ℕ} (x : AF D.host.F) (t : Fin T.rank → D.host.E) (u v : Fin n → D.host.E) :
    genT T x t (u + v) = genT T x t u + genT T x t v := by
  ext p q
  simp only [genT, Matrix.of_apply, Matrix.add_apply, Pi.add_apply, add_mul, TensorProduct.tmul_add]

theorem genT_zero (T : HSp D) {n : ℕ} (x : AF D.host.F) (t : Fin T.rank → D.host.E) :
    genT T x t (0 : Fin n → D.host.E) = 0 := by
  ext p q
  simp only [genT, Matrix.of_apply, Pi.zero_apply, zero_mul, TensorProduct.tmul_zero, Matrix.zero_apply]

theorem starAdj_gen (S T : HSp D) (x : AF D.host.F) (a : D.host.E) (s : Fin S.rank → D.host.E)
    (t : Fin T.rank → D.host.E) :
    incA D D.host.xi0⁻¹ • GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj S T
        (Matrix.of fun i j => x ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j)) =
      genT T x t (star a • s) := by
  have e : (Matrix.of fun i j => x ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) : WO S T) =
      tensM x ((Matrix.of fun i k => a * t i * star (s k)) * S.gram) := by
    ext i j
    simp only [tensM, Matrix.map_apply, Matrix.mul_apply, Matrix.of_apply, Finset.mul_sum, mul_assoc]
  rw [xi0_inv_smul_starAdj, e, adj_tensM, Matrix.conjTranspose_mul, gram_conjTranspose, gA, tensM_mul_rat, giA,
    rat_mul_tensM, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (gram_isUnit_det S), Matrix.one_mul]
  ext p q
  simp only [tensM, genT, Matrix.map_apply, Matrix.mul_apply, Matrix.of_apply, Matrix.conjTranspose_apply,
    Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [star_mul', star_star]
  ring

theorem genT_mem_of_mem_span (S T : HSp D) (LS' : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (P : GlobalTheory.FinPl.Pl D → Prop)
    (α : Af D.host.F) (hα : α ∈ intAf D.host.F) (hP : ∀ v, ¬ P v → evalV D.host.F v α = 0)
    (t : Fin T.rank → D.host.E) (ht : t ∈ LT) (u : Fin S.rank → D.host.E)
    (hu : u ∈ Submodule.span (𝓞 D.host.E) {y | ∃ a' ∈ D.host.AA, ∃ s' ∈ LS', y = a' • s'}) :
    genT T (pairA D.host.F 0 α) t u ∈ latO T S (LT : Set _) (LS' : Set _) P := by
  suffices h : ∀ c : 𝓞 D.host.E, genT T (pairA D.host.F 0 α) t (c • u) ∈ latO T S (LT : Set _) (LS' : Set _) P by
    simpa using h 1
  induction hu using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a', ha', s', hs', rfl⟩ := hy
    intro c
    apply AddSubgroup.subset_closure
    refine ⟨α, hα, hP, a', ha', t, ht, c • s', LS'.smul_mem c hs', ?_⟩
    ext p q
    simp only [genT, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
    congr 1
    rw [Algebra.smul_def, Algebra.smul_def]
    ring
  | zero => intro c; rw [smul_zero, genT_zero]; exact zero_mem _
  | add y z _ _ hy hz => intro c; rw [smul_add, genT_add]; exact add_mem (hy c) (hz c)
  | smul r y _ hy => intro c; rw [smul_smul]; exact hy (c * r)

theorem incA_inv_xi0_smul_starAdj_mem_latO : ∀ (D : D7) (S T : HSp D) (LS LS' : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (P : GlobalTheory.FinPl.Pl D → Prop), (∀ a ∈ D.host.AA, ∀ s ∈ LS, star a • s ∈ Submodule.span (𝓞 D.host.E) {y | ∃ a' ∈ D.host.AA, ∃ s' ∈ LS', y = a' • s'}) → ∀ x ∈ latO S T (LS : Set _) (LT : Set _) P, incA D D.host.xi0⁻¹ • GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj S T x ∈ latO T S (LT : Set _) (LS' : Set _) P := by
  intro D S T LS LS' LT P hA x hx
  induction hx using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩ := hw
    rw [starAdj_gen]
    exact genT_mem_of_mem_span S T LS' LT P α hα hP t ht _ (hA a ha s hs)
  | zero =>
    rw [xi0_inv_smul_starAdj, adj_zero, Matrix.zero_mul, Matrix.mul_zero]; exact zero_mem _
  | add y z _ _ hy hz =>
    rw [xi0_inv_smul_starAdj] at hy hz ⊢
    rw [adj_add, Matrix.add_mul, Matrix.mul_add]; exact add_mem hy hz
  | neg y _ hy =>
    rw [xi0_inv_smul_starAdj] at hy ⊢
    rw [adj_neg, Matrix.neg_mul, Matrix.mul_neg]; exact neg_mem hy

end GlobalTheory.AdjLatO
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianSkewAdjointMemAdjointHomLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianSkewAdjoint_mem_adjoint_homLattice : ∀ (D : D7) (S T : HSp D) (LS LS' : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (P : GlobalTheory.FinPl.Pl D → Prop), (∀ a ∈ D.host.AA, ∀ s ∈ LS, star a • s ∈ Submodule.span (𝓞 D.host.E) {y | ∃ a' ∈ D.host.AA, ∃ s' ∈ LS', y = a' • s'}) → ∀ x ∈ latO S T (LS : Set _) (LT : Set _) P, incA D D.host.xi0⁻¹ • GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj S T x ∈ latO T S (LT : Set _) (LS' : Set _) P := by
  first | exact @GlobalTheory.AdjLatO.incA_inv_xi0_smul_starAdj_mem_latO | exact GlobalTheory.AdjLatO.incA_inv_xi0_smul_starAdj_mem_latO | (intros; apply GlobalTheory.AdjLatO.incA_inv_xi0_smul_starAdj_mem_latO <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualFractionalIdealSmulLatticeOfNormOne
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualFractionalIdealSmulLatticeOfNormOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.IdLatDual

variable {D : D7}

def hp (S : HSp D) (x y : Fin S.rank → D.host.E) : D.host.E :=
  ∑ i, ∑ j, star (x i) * S.gram i j * y j

def IsO (z : D.host.E) : Prop := ∃ b : 𝓞 D.host.E, (b : D.host.E) = z

lemma isO_zero : IsO (0 : D.host.E) := ⟨0, by simp⟩
lemma isO_add {z w : D.host.E} (hz : IsO z) (hw : IsO w) : IsO (z + w) := by
  obtain ⟨b, rfl⟩ := hz; obtain ⟨c, rfl⟩ := hw; exact ⟨b + c, by push_cast; rfl⟩
lemma isO_mul {z w : D.host.E} (hz : IsO z) (hw : IsO w) : IsO (z * w) := by
  obtain ⟨b, rfl⟩ := hz; obtain ⟨c, rfl⟩ := hw; exact ⟨b * c, by push_cast; rfl⟩
lemma isO_coe (a : 𝓞 D.host.E) : IsO (a : D.host.E) := ⟨a, rfl⟩
lemma isO_star (a : 𝓞 D.host.E) : IsO (star (a : D.host.E)) := by
  refine ⟨⟨star (a : D.host.E), ?_⟩, rfl⟩
  exact (RingOfIntegers.isIntegral_coe a).map (starRingEnd D.host.E).toIntAlgHom
lemma isO_of_mem_one {z : D.host.E} (h : z ∈ (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)) : IsO z := by
  obtain ⟨b, hb⟩ := (FractionalIdeal.mem_one_iff _).1 h
  exact ⟨b, by rw [RingOfIntegers.coe_eq_algebraMap]; exact hb⟩

lemma osmul {n : ℕ} (a : 𝓞 D.host.E) (x : Fin n → D.host.E) : a • x = (a : D.host.E) • x := by
  ext i; simp [Algebra.smul_def, RingOfIntegers.coe_eq_algebraMap]

variable (S : HSp D)

lemma hp_add_left (x x' y) : hp S (x + x') y = hp S x y + hp S x' y := by
  simp only [hp, Pi.add_apply, star_add, add_mul, Finset.sum_add_distrib]
lemma hp_add_right (x y y') : hp S x (y + y') = hp S x y + hp S x y' := by
  simp only [hp, Pi.add_apply, mul_add, Finset.sum_add_distrib]
lemma hp_zero_left (y) : hp S 0 y = 0 := by simp [hp]
lemma hp_zero_right (x) : hp S x 0 = 0 := by simp [hp]
lemma hp_smul_left (s : D.host.E) (x y) : hp S (s • x) y = star s * hp S x y := by
  simp only [hp, Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
lemma hp_smul_right (t : D.host.E) (x y) : hp S x (t • y) = t * hp S x y := by
  simp only [hp, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end GlobalTheory.IdLatDual

open GlobalTheory.IdLatDual in
lemma GlobalTheory.IdLatDual.idLat_fg {D : D7} {n : ℕ} (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (hΛ : Λ.FG)
    (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : (idLat I Λ).FG := by
  obtain ⟨a, ha, hint⟩ := I.isFractional
  let f : (Fin n → D.host.E) →ₗ[𝓞 D.host.E] (Fin n → D.host.E) := LinearMap.lsmul (𝓞 D.host.E) (Fin n → D.host.E) a
  have hle : (idLat I Λ).map f ≤ Λ := by
    rw [Submodule.map_le_iff_le_comap]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨s, hs, y, hy, rfl⟩
    obtain ⟨r, hr⟩ := hint s hs
    show a • (s • y) ∈ Λ
    rw [← smul_assoc, ← hr, algebraMap_smul]
    exact Submodule.smul_mem _ _ hy
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  have hinj : Function.Injective f := by
    intro x x' h
    have h' : a • x = a • x' := h
    rw [osmul, osmul] at h'
    have : (a : D.host.E) ≠ 0 := fun h0 => ha0 (RingOfIntegers.coe_eq_zero_iff.1 h0)
    exact smul_right_injective _ this h'
  have hfg : ((idLat I Λ).map f).FG := Submodule.FG.of_le hΛ hle
  exact Submodule.fg_of_fg_map_injective f hinj hfg


open GlobalTheory.IdLatDual in
theorem GlobalTheory.idLat_isSelfDualC : ∀ {D : D7} (S : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (I I' : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E), IsSelfDualC S Λ → I * I' = 1 →
    (∀ x : D.host.E, x ∈ I' ↔ star x ∈ I) → IsSelfDualC S (idLat I Λ) := by
  intro D S Λ I I' hΛ hII' hconj
  obtain ⟨hlat, hdual⟩ := hΛ
  have intL : ∀ x ∈ Λ, ∀ y ∈ Λ, IsO (hp S x y) := fun x hx y hy => (hdual y).1 hy x hx
  have gen : ∀ s ∈ I, ∀ y ∈ Λ, s • y ∈ idLat I Λ := fun s hs y hy =>
    Submodule.subset_span ⟨s, hs, y, hy, rfl⟩
  have one_mem : (1 : D.host.E) ∈ I * I' := by rw [hII']; exact FractionalIdeal.one_mem_one _

  have hspan : ∀ y ∈ Λ, y ∈ Submodule.span D.host.E (idLat I Λ : Set (Fin S.rank → D.host.E)) := by
    intro y hy
    have key : ∀ z ∈ I * I', z • y ∈ Submodule.span D.host.E (idLat I Λ : Set (Fin S.rank → D.host.E)) := by
      intro z hz
      refine FractionalIdeal.mul_induction_on hz (fun i hi c _ => ?_) (fun a b ha hb => ?_)
      · rw [mul_comm, mul_smul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (gen i hi y hy))
      · rw [add_smul]; exact Submodule.add_mem _ ha hb
    simpa using key 1 one_mem
  have hfg : (idLat I Λ).FG := idLat_fg Λ hlat.fg I
  refine ⟨Submodule.IsLattice.of_fg D.host.E hfg, fun y => ⟨fun hy => ?_, fun hy => ?_⟩⟩
  ·
    have stepA : ∀ s ∈ I, ∀ x₀ ∈ Λ, ∀ y ∈ idLat I Λ, IsO (hp S (s • x₀) y) := by
      intro s hs x₀ hx₀ y hy
      induction hy using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨t, ht, y₀, hy₀, rfl⟩ := hz
        rw [hp_smul_left, hp_smul_right, ← mul_assoc]
        refine isO_mul (isO_of_mem_one ?_) (intL x₀ hx₀ y₀ hy₀)
        rw [← hII', mul_comm I]
        exact FractionalIdeal.mul_mem_mul ((hconj _).2 (by rwa [star_star])) ht
      | zero => rw [hp_zero_right]; exact isO_zero
      | add a b _ _ ha hb => rw [hp_add_right]; exact isO_add ha hb
      | smul c z _ hz => rw [osmul, hp_smul_right]; exact isO_mul (isO_coe c) hz
    intro x hx
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨s, hs, x₀, hx₀, rfl⟩ := hz
      obtain ⟨b, hb⟩ := stepA s hs x₀ hx₀ y hy
      exact ⟨b, hb⟩
    | zero => exact ⟨0, by rw [← hp, hp_zero_left]; simp⟩
    | add a b _ _ ha hb =>
      have h : IsO (hp S a y + hp S b y) := isO_add ha hb
      rw [← hp_add_left] at h
      exact h
    | smul c z _ hz =>
      obtain ⟨u, hu⟩ := isO_mul (isO_star c) hz
      exact ⟨u, by rw [← hp, osmul, hp_smul_left]; exact hu⟩
  · have hint : ∀ x ∈ idLat I Λ, IsO (hp S x y) := fun x hx => hy x hx
    have key : ∀ z ∈ I * I', z • y ∈ idLat I Λ := by
      intro z hz
      refine FractionalIdeal.mul_induction_on hz (fun i hi c hc => ?_) (fun a b ha hb => ?_)
      · rw [mul_smul]
        refine gen i hi _ ((hdual _).2 fun x' hx' => ?_)
        have hsc : star c ∈ I := (hconj c).1 hc
        obtain ⟨b, hb⟩ := hint _ (gen _ hsc x' hx')
        refine ⟨b, ?_⟩
        rw [hb]
        show hp S (star c • x') y = hp S x' (c • y)
        rw [hp_smul_left, hp_smul_right, star_star]
      · rw [add_smul]; exact Submodule.add_mem _ ha hb
    simpa using key 1 one_mem
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualFractionalIdealSmulLatticeOfNormOneStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSelfDual_fractionalIdealSmulLattice_of_norm_one : ∀ {D : D7} (S : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (I I' : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E), IsSelfDualC S Λ → I * I' = 1 → (∀ x : D.host.E, x ∈ I' ↔ star x ∈ I) → IsSelfDualC S (idLat I Λ) := by
  first | exact @GlobalTheory.idLat_isSelfDualC | exact GlobalTheory.idLat_isSelfDualC | (intros; apply GlobalTheory.idLat_isSelfDualC <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralLocalBasisConjugatesOfKeepsLatticeAtPlac
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralLocalBasisConjugatesOfKeepsLatticeAtPlac
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.IntKeepConj

theorem mulVec_conj_col {R S : Type} [CommRing R] [CommRing S] {d : ℕ} (π : R →+* S)
    (b : GL (Fin d) S) (A : Matrix (Fin d) (Fin d) R) (z : Fin d → R) (k : Fin d)
    (hz : (fun j => π (z j)) = (b : Matrix (Fin d) (Fin d) S) *ᵥ Pi.single k 1) :
    (((b⁻¹ : GL (Fin d) S) : Matrix (Fin d) (Fin d) S) *ᵥ fun j => π ((A *ᵥ z) j)) =
      fun i => (((b⁻¹ : GL (Fin d) S) : Matrix (Fin d) (Fin d) S) * A.map π *
        (b : Matrix (Fin d) (Fin d) S)) i k := by
  have h1 : (fun j => π ((A *ᵥ z) j)) = A.map π *ᵥ (fun j => π (z j)) := by
    funext j; exact RingHom.map_mulVec π A z j
  rw [h1, hz, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  funext i
  simp [Matrix.mulVec_single]

theorem single_mem {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) {d : ℕ} (k i : Fin d) :
    (Pi.single k (1 : Fv F v) : Fin d → Fv F v) i ∈ v.adicCompletionIntegers F := by
  by_cases h : i = k
  · subst h; simp only [Pi.single_eq_same]; exact (v.adicCompletionIntegers F).one_mem
  · rw [Pi.single_eq_of_ne h]; exact (v.adicCompletionIntegers F).zero_mem

end GlobalTheory.IntKeepConj

open GlobalTheory.IntKeepConj in
theorem GlobalTheory.IntKeepConj.conj_integral : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) (π₁ π₂ : AE F E →+* Fv F v) (b₁ b₂ : GL (Fin d) (Fv F v)),
  (∀ z : Fin d → AE F E, z ∈ GlobalTheory.InertSph.latAt W v ↔ At (evFin F v) z ∧
      (∀ i, (((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => π₁ (z j)) i ∈
        v.adicCompletionIntegers F) ∧
      (∀ i, (((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => π₂ (z j)) i ∈
        v.adicCompletionIntegers F)) → (∀ x₁ x₂ : Fv F v, ∃ z : AE F E, At (evFin F v) z ∧ π₁ z = x₁ ∧ π₂ z = x₂) →
  ∀ A : Matrix (Fin d) (Fin d) (AE F E), (∀ z ∈ GlobalTheory.InertSph.latAt W v, A *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) → (∀ i j, (((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (A).map π₁ * (b₁ : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F) ∧ (∀ i j, (((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (A).map π₂ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F) := by
  intro F E _ _ _ _ _ d W v π₁ π₂ b₁ b₂ hchar hsurj A hA
  constructor
  · intro i k
    choose z hzA hz1 hz2 using fun j => hsurj (((b₁ : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ Pi.single k 1) j) 0
    have hzL : z ∈ GlobalTheory.InertSph.latAt W v := by
      rw [hchar]
      refine ⟨?_, ?_, ?_⟩
      · intro u hu; funext j; exact hzA j u hu
      · intro i'
        have e : (fun j => π₁ (z j)) = (b₁ : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ Pi.single k 1 := funext hz1
        rw [e, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
        exact single_mem v k i'
      · intro i'
        have e : (fun j => π₂ (z j)) = 0 := funext hz2
        rw [e, Matrix.mulVec_zero]; exact (v.adicCompletionIntegers F).zero_mem
    have h := ((hchar _).1 (hA z hzL)).2.1 i
    rw [mulVec_conj_col π₁ b₁ A z k (funext hz1)] at h
    exact h
  · intro i k
    choose z hzA hz1 hz2 using fun j => hsurj 0 (((b₂ : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ Pi.single k 1) j)
    have hzL : z ∈ GlobalTheory.InertSph.latAt W v := by
      rw [hchar]
      refine ⟨?_, ?_, ?_⟩
      · intro u hu; funext j; exact hzA j u hu
      · intro i'
        have e : (fun j => π₁ (z j)) = 0 := funext hz1
        rw [e, Matrix.mulVec_zero]; exact (v.adicCompletionIntegers F).zero_mem
      · intro i'
        have e : (fun j => π₂ (z j)) = (b₂ : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ Pi.single k 1 := funext hz2
        rw [e, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
        exact single_mem v k i'
    have h := ((hchar _).1 (hA z hzL)).2.2 i
    rw [mulVec_conj_col π₂ b₂ A z k (funext hz2)] at h
    exact h
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralLocalBasisConjugatesOfKeepsLatticeAtPlacStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_localBasisConjugates_of_keepsLatticeAtPlace : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) (π₁ π₂ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →+* Fv F v) (b₁ b₂ : GL (Fin d) (Fv F v)),
  (∀ z : Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), z ∈ GlobalTheory.InertSph.latAt W v ↔ At (evFin F v) z ∧
      (∀ i, (((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => π₁ (z j)) i ∈
        v.adicCompletionIntegers F) ∧
      (∀ i, (((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => π₂ (z j)) i ∈
        v.adicCompletionIntegers F)) → (∀ x₁ x₂ : Fv F v, ∃ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ∧ π₁ z = x₁ ∧ π₂ z = x₂) →
  ∀ A : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), (∀ z ∈ GlobalTheory.InertSph.latAt W v, A *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) → (∀ i j, (((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (A).map π₁ * (b₁ : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F) ∧ (∀ i j, (((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (A).map π₂ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F) := by
  first | exact @GlobalTheory.IntKeepConj.conj_integral | exact GlobalTheory.IntKeepConj.conj_integral | (intros; apply GlobalTheory.IntKeepConj.conj_integral <;> assumption)
end
end
