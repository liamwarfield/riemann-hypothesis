module

public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsCuspRestrictComp
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.NoCommonZeroIffOfSec
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TestPointValueEqConstMulReading

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.CompSplitRecord
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.Reg


set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem compSplit_record : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j)
    (hG : GenFrEx (T.Q.Xo j) T.Q.c), CompSplitSt h j hG := by
  intro D T h j hj hG Z w g
  obtain ⟨hL, -, -, hA⟩ := evLaws_genFr_atlas _ _ _ _ (T.Q.Xo j) T.Q.c
  have hg : (g : T.R j) ∈ T.C j w := cutR_le T.C j w g.2
  obtain ⟨g', hg', h1, h0⟩ := exists_cusp_restrict_comp _ _ _ _ (T.Q.Xo j) T.Q.c hL hG (hA hG) _
    (fun σ => Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) (fun σ hσ => h.unf j hj σ hσ) Z (wtA w) w.n (g : T.R j) hg
  have hm : g' ∈ cutR T.C j w := by
    rw [cutR_eq T.C hj]; exact hg'
  exact ⟨⟨g', hm⟩, h1, h0⟩

end GlobalTheory.Reg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.CuspEqZeroOfGenericValues
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.Reg

theorem cusp_eq_zero_of_generic_values {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) {r : ℕ}
    (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (hG : GenFrEx Xo c) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (g : Rul Xo c) (hg : g ∈ cusp Xo c U a n) (h0 : ∀ Z, evC hG Z g = 0) : g = 0 := by
  obtain ⟨hL, -, -, hA⟩ := evLaws_genFr_atlas E H Dw l Xo c
  exact sec_eq_zero_of_generic_values E H Dw l Xo c hL hG (hA hG) a n g (cusp_le_sec Xo c U a n hg) h0


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem genValInj_record : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c), GenValInjSt h j hG := by
  intro D T h j _ hG w g h0
  have hg : (g : T.R j) ∈ cusp (T.Q.Xo j) T.Q.c (T.U j) (wtA w) w.n := cutR_le T.C j w g.2
  exact Subtype.ext (cusp_eq_zero_of_generic_values (T.Q.Xo j) T.Q.c (T.U j) hG (wtA w) w.n _ hg h0)

end GlobalTheory.Reg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameNormConjugatePointsEqPointwise
section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameNormConjugatePointsEqPointwise
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameNorm GlobalTheory.Reg

namespace GlobalTheory.FrameNorm

theorem fnConj_valAtCx_nrmC_eq_ptNorm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → ∀ (xR : ℝ) (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ), 0 < xR → FnPin U xR fn → ∀ (h : GenFrEx Xo c) (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P))), (∀ Z, CBase h Z (yP Z)) → FnConj Xo c fn yP ∧ ValAtCx h yP ∧ ∀ (Z : Comp Xo c) (P : Om Z →+* ℂ) a n, ∀ f ∈ sec Xo c a n, nrmC fn (yP Z) (wtZ a n) (valC h a n f Z) P = ptNorm (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (sgOf P) (fn (sgOf P)) (ex Dw a n) f (yP Z P) := by
  intro E _ _ _ H Dw l Xo c r U _ xR fn _ hpin h yP hcb
  have hWD := GlobalTheory.TransferCompare.evalWD_framed Xo c
  have hgt : GenFromTest Xo c h := (GlobalTheory.Reg.genFrEx_and_genFromTest E H Dw l Xo c).2 h
  have hcx : ValAtCx h yP := by
    intro Z P a n f hf
    have hT1 := hgt Z
    have hm := hcb Z P
    have hT2 : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (yP Z P) := by
      obtain ⟨p, ψ, y', hy'⟩ := hT1
      exact ⟨p, (PAlg P).comp ψ, y', frMap_trans (Xo := Xo) (c := c) _ _ _ ψ (PAlg P) y' _ _ hy' hm⟩
    have key : evR Xo c f (yP Z P) = PAlg P (evR Xo c f (genFr h Z)) := by
      unfold evR evalAt
      rw [dite_eq_left hT2, dite_eq_left hT1]
      exact hWD f hf.1 _ _ _ _ _ _ _ (yP Z P) hT2.choose_spec.choose_spec.choose_spec
        (frMap_trans (Xo := Xo) (c := c) _ _ _ _ (PAlg P) _ _ _ hT1.choose_spec.choose_spec.choose_spec hm)
    rw [key]
    rfl
  refine ⟨?_, hcx, ?_⟩
  · intro Z G x P
    have hm : FrMap (conjAlg (sgOf P)) (yP Z P) (yP Z ((starRingEnd ℂ).comp P)) :=
      frMap_cancel (Xo := Xo) (c := c) _ _ _ (PAlg P) (conjAlg (sgOf P)) (genFr h Z) _ _ (hcb Z P)
        (hcb Z ((starRingEnd ℂ).comp P))
    unfold nrmC
    congr 1
    · exact Complex.norm_conj _
    · refine Finset.prod_congr rfl fun i _ => ?_
      exact congrArg (fun t : ℝ => t ^ (-exZ Dw G i)) (hpin.2 (sgOf P) (yP Z P) _ hm i)
  · intro Z P a n f hf
    show nrmC fn (yP Z) (wtZ a n) (AddMonoidAlgebra.single (wtZ a n) (evC h Z f)) P = _
    rw [nrmC_single, hcx Z P a n f hf]
    unfold ptNorm
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    have e : exZ Dw (wtZ a n) i = (ex Dw a n i : ℤ) := by cases i <;> rfl
    rw [e, zpow_neg, zpow_natCast, inv_pow]

end GlobalTheory.FrameNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameNormConjugatePointsEqPointwiseStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameNorm GlobalTheory.Reg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameNorm_conjugate_points_eq_pointwise : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → ∀ (xR : ℝ) (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ), 0 < xR → FnPin U xR fn → ∀ (h : GenFrEx Xo c) (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P))), (∀ Z, CBase h Z (yP Z)) → FnConj Xo c fn yP ∧ ValAtCx h yP ∧ ∀ (Z : Comp Xo c) (P : Om Z →+* ℂ) a n, ∀ f ∈ sec Xo c a n, nrmC fn (yP Z) (wtZ a n) (valC h a n f Z) P = ptNorm (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (sgOf P) (fn (sgOf P)) (ex Dw a n) f (yP Z P) := by
  first | exact @GlobalTheory.FrameNorm.fnConj_valAtCx_nrmC_eq_ptNorm | exact GlobalTheory.FrameNorm.fnConj_valAtCx_nrmC_eq_ptNorm | (intros; apply GlobalTheory.FrameNorm.fnConj_valAtCx_nrmC_eq_ptNorm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsCuspRestrictCompInt
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameNorm GlobalTheory.Reg

namespace GlobalTheory.Reg

theorem exists_cusp_restrict_comp_int : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → ∀ (h : GenFrEx Xo c) (Z : Comp Xo c) a n, ∀ g ∈ Formalism.L2.PjFree.cusp Xo c U a n, ∃ g' ∈ Formalism.L2.PjFree.cusp Xo c U a n, evC h Z g' = evC h Z g ∧ (∀ Z', Z' ≠ Z → evC h Z' g' = 0) ∧ ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), evI y g' = evI y g ∨ evI y g' = 0 := by
  intro E _ _ _ H Dw l Xo c r U hU h Z a n g hg
  obtain ⟨hL, -, -, hA⟩ := GlobalTheory.T.evaluation_laws_generic_frames_atlas_hold E H Dw l Xo c
  obtain ⟨χ, hχ, hidem, h1, h0⟩ := exists_idem_section E H Dw l Xo c hL h (hA h) Z

  have hm : ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (f f' : Rul Xo c),
      evR Xo c (f * f') y = evR Xo c f y * evR Xo c f' y := by
    intro S _ _ y f f'
    unfold evR
    exact evalAt_mul _ _ f f' y
  refine ⟨χ * g, GlobalTheory.Reg.IdemCusp.idem_mul_mem_cusp E H Dw l Xo c r U hU χ hχ hidem a n g hg, ?_, ?_, ?_⟩
  · unfold evC at h1 ⊢
    rw [hm, h1, one_mul]
  · intro Z' hZ'
    have h0' := h0 Z' hZ'
    unfold evC at h0' ⊢
    rw [hm, h0', zero_mul]
  · intro T io y
    letI := io.toAlgebra
    unfold evI

    have hy : IsIdempotentElem (evR Xo c χ y.1) := by
      unfold IsIdempotentElem
      rw [← hm, hidem]
    rcases IsIdempotentElem.iff_eq_zero_or_one.mp hy with h' | h'
    · right
      rw [hm, h', zero_mul]
    · left
      rw [hm, h', one_mul]

end GlobalTheory.Reg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsHolomorphicFactorGeneratorThetaSection
section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsHolomorphicFactorGeneratorThetaSection
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open Formalism.L2.PjFree hiding gxFst gxSnd toC
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif GlobalTheory.FrameNorm
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.GenFactor

open GlobalTheory.HolGen

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l}

theorem exists_factor (hT : Out.SecTwistSt) {Z : Type} (x u : Sp ℂ ⟶ Xo.X) (hxu : x = u) (s : LB.Sec (PPx x))
    (hs : SecGen x s) (e : Z → (Over.mk u ⟶ Xo.univ.t.G)) (θ : Z → ℂ) (fr : Xo.univ.t.PP.L.ι → Z → ℂ)
    (hθ : ∃ z, θ z ≠ 0) (hfr : ∀ j z, ⊤ ≤ (e z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j z ≠ 0)
    (t : (Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom u)).Sec)
    (ht : ∀ j z (p : Sp ℂ ⟶ pullback Xo.univ.t.G.hom u), p ≫ pullback.fst _ _ = (e z).left →
      p ≫ pullback.snd _ _ = 𝟙 _ → ⊤ ≤ (e z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' p ((Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom u)).U (fun _ => j)) (t.f (fun _ => j)) =
        θ z * fr j z) :
    ∃ κ : ℂ, κ ≠ 0 ∧ ∀ j z (pt : Sp ℂ ⟶ Gx x), pt ≫ gxFst x = (e z).left → pt ≫ gxSnd x = 𝟙 (Sp ℂ) →
      ⊤ ≤ (e z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' pt ((PPx x).U (fun _ => j)) (s.f (fun _ => j)) = κ * θ z * fr j z := by
  subst hxu
  obtain ⟨s', hs'⟩ := GlobalTheory.FibreSection.exists_sec_same_values E H Dw l Xo x t
  obtain ⟨a, ha, -⟩ := hs s'
  have key : ∀ j z (pt : Sp ℂ ⟶ Gx x), pt ≫ gxFst x = (e z).left → pt ≫ gxSnd x = 𝟙 (Sp ℂ) →
      ⊤ ≤ (e z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      a * valAt' pt ((PPx x).U (fun _ => j)) (s.f (fun _ => j)) = θ z * fr j z := by
    intro j z pt e₁ e₂ hj
    have hw : (e z).left ≫ Xo.univ.t.G.hom = 𝟙 _ ≫ x := (Over.w (e z)).trans (Category.id_comp _).symm
    have p₁ := pullback.lift_fst (f := Xo.univ.t.G.hom) (g := x) (e z).left (𝟙 _) hw
    have p₂ := pullback.lift_snd (f := Xo.univ.t.G.hom) (g := x) (e z).left (𝟙 _) hw
    refine ((sec_values_complex_fibre hT E H Dw l Xo x s).1 a (fun _ => j) pt e₂).symm.trans ?_
    refine (congrArg (valAt' pt ((PPx x).U (fun _ => j))) (ha (fun _ => j))).symm.trans ?_
    exact (hs' j pt _ (p₁.trans e₁.symm) p₂ e₂).trans (ht j z _ p₁ p₂ hj)
  obtain ⟨z₀, hz₀⟩ := hθ
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.ThetaPtChg.exists_chart_point Xo.univ.t.PP.isLB (e z₀).left
  obtain ⟨pt₀, e₁, e₂⟩ := exists_pt (R := ℂ) x (𝟙 _) (e z₀).left
    ((Category.id_comp _).trans (Over.w (e z₀)).symm)
  have ha0 : a ≠ 0 := by
    rintro rfl
    have := key j₀ z₀ pt₀ e₁ e₂ hj₀
    rw [zero_mul] at this
    exact mul_ne_zero hz₀ (hfr j₀ z₀ hj₀) this.symm
  refine ⟨a⁻¹, inv_ne_zero ha0, fun j z pt e₁ e₂ hj => ?_⟩
  rw [mul_assoc, ← key j z pt e₁ e₂ hj, inv_mul_cancel_left₀ ha0]

end

theorem exists_holomorphic_factor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (σ' : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ' ty) (k : Fin F.n) (A : Type) [CommRing A] [Algebra c.F A] (yA : FrPt Xo c A) (m : ℕ) (B : Set (Fin m → ℂ)) (φ : (Fin m → ℂ) → (A →ₐ[c.F] CAt σ)) (y : (Fin m → ℂ) → FrPt Xo c (CAt σ)) (P : (Fin m → ℂ) → ((F.Di k).La →+ (Fin g → ℂ))) (θ : (Fin m → ℂ) → (Fin g → ℂ) → ℂ), IsOpen B → (∀ a, DifferentiableOn ℂ (fun b => toC (φ b a)) B) → (∀ b ∈ B, FrMap (φ b) yA (y b)) → IsHolPeriods (F.Di k) ty B P → (∀ b ∈ B, (y b).x = F.u k (P b)) → (∀ z, DifferentiableOn ℂ (fun b => θ b z) B) → (∀ b ∈ B, ∃ z, θ b z ≠ 0) → IsThetaFrame Xo.univ.t.PP B (fun b => F.u k (P b)) (fun b z => (F.ex k (P b) z).left) θ → ∃ (fr : Xo.univ.t.PP.L.ι → (Fin m → ℂ) × (Fin g → ℂ) → ℂ) (κ : (Fin m → ℂ) → ℂ), RigFrame F k B P fr ∧ DifferentiableOn ℂ κ B ∧ ∀ b ∈ B, κ b ≠ 0 ∧ SecVal F k (P b) (y b).x (y b).s (fun z => κ b * θ b z) (fun j z => fr j (b, z)) := by
  intro E _ _ _ H Dw l Xo c σ σ' g ty F k A _ _ yA m B ψ y P θ hB hψ hb hP hxu hθ hθ0 hfr
  have hT : Out.SecTwistSt := GlobalTheory.abelianSchemeLaws_all.2.secTwist
  obtain ⟨fr, f₁, f₂, f₃, f₄, f₅⟩ := hfr
  have hκ₁ : ∀ b, ∃ κ : ℂ, b ∈ B → κ ≠ 0 ∧
      SecVal F k (P b) (y b).x (y b).s (fun z => κ * θ b z) (fun j z => fr j (b, z)) := fun b => by
    by_cases h : b ∈ B
    · obtain ⟨t, ht⟩ := f₅ b h
      obtain ⟨κ, h₁, h₂⟩ := exists_factor hT (y b).x (F.u k (P b)) (hxu b h) (y b).s (y b).gen (F.ex k (P b)) (θ b)
        (fun j z => fr j (b, z)) (hθ0 b h) (fun j z hz => f₂ j b z h hz) t ht
      exact ⟨κ, fun _ => ⟨h₁, h₂⟩⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose κ hκ using hκ₁
  refine ⟨fr, κ, ⟨f₁, f₂, f₃, f₄⟩, fun b₀ hb₀ => ?_, hκ⟩
  let φ : (Fin m → ℂ) → (A →+* ℂ) := fun b => (ψ b).toRingHom
  have hux : ∀ b ∈ B, F.u k (P b) = (y b).x := fun b h => (hxu b h).symm
  obtain ⟨pm₀, p₁, p₂, p₃⟩ := (hb b₀ hb₀).2.2
  obtain ⟨e₀, j, hne⟩ := exists_val_ne hT (φ b₀) yA.x (y b₀).x _ (hux b₀ hb₀) yA.s (y b₀).s pm₀ p₁ p₂ p₃ (y b₀).gen
  obtain ⟨w₀, rfl⟩ := F.ex_onto k _ (hP.1 b₀ hb₀) e₀
  have hq₁ : ∀ b ∈ B, ∃ q : Sp ℂ ⟶ Gx yA.x, q ≫ gxFst yA.x = (F.ex k (P b) w₀).left ∧
      q ≫ gxSnd yA.x = spMap (φ b) := fun b h =>
    exists_pt _ _ _ (((hb b h).1.symm.trans (hux b h).symm).trans (Over.w (F.ex k (P b) w₀)).symm)
  have hq₂ : ∀ b, ∃ q : Sp ℂ ⟶ Gx yA.x, b ∈ B → q ≫ gxFst yA.x = (F.ex k (P b) w₀).left ∧
      q ≫ gxSnd yA.x = spMap (φ b) := fun b => by
    by_cases h : b ∈ B
    · exact (hq₁ b h).imp fun _ h' _ => h'
    · exact ⟨(hq₁ b₀ hb₀).choose, fun h' => absurd h' h⟩
  choose q hq using hq₂
  have hι : Differentiable ℂ (fun b : Fin m → ℂ => ((b, w₀) : (Fin m → ℂ) × (Fin g → ℂ))) := by fun_prop
  have hol : IsHolTo B q := by
    refine HolPullback.isHolTo_of_components _ B _ _ _ _ (gxSnd yA.x) (gxFst yA.x) yA.x Xo.univ.t.G.hom q
      (IsPullback.of_hasPullback yA.x Xo.univ.t.G.hom) hB ?_ ?_
    · exact LocLift.isHolTo_congr (ThetaValueCont.isHolTo_spMap hB φ hψ) fun b h => (hq b h).2
    · exact LocLift.isHolTo_congr (LocLift.isHolTo_comp (F.hol k _ B _ hB hP).2 hB hι.differentiableOn
        fun b h => ⟨h, trivial⟩) fun b h => (hq b h).1
  have hW := (hol ((Gx yA.x).basicOpen (yA.s.f (fun _ => j))) 0).1
  set W := {b ∈ B | ⊤ ≤ q b ⁻¹ᵁ (Gx yA.x).basicOpen (yA.s.f (fun _ => j))} with hWd
  have hb₀W : b₀ ∈ W := ⟨hb₀, (top_le_preimage_basicOpen_iff _ _ _).2 (hne _ (hq b₀ hb₀).1 (hq b₀ hb₀).2)⟩
  have vnz : ∀ b ∈ W, valAt' (q b) ((PPx yA.x).U (fun _ => j)) (yA.s.f (fun _ => j)) ≠ 0 := fun b h =>
    (top_le_preimage_basicOpen_iff _ _ _).1 h.2
  have m₁ : ∀ b ∈ W, ⊤ ≤ q b ⁻¹ᵁ (PPx yA.x).U (fun _ => j) := fun b h =>
    top_le_preimage_of_valAt'_ne_zero _ (vnz b h)
  have m₂ : ∀ b ∈ W, ⊤ ≤ (F.ex k (P b) w₀).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun b h => by
    rw [← (hq b h.1).1]
    exact (chart_iff _ _ _).1 (m₁ b h)
  have d₁ : DifferentiableOn ℂ (fun b => θ b w₀) W := (hθ w₀).mono fun b h => h.1
  have d₂ : DifferentiableOn ℂ (fun b => fr j (b, w₀)) W :=
    DifferentiableOn.comp (f := fun b : Fin m → ℂ => ((b, w₀) : (Fin m → ℂ) × (Fin g → ℂ))) (g := fr j)
      (f₁ j) hι.differentiableOn fun b h => ⟨h.1, m₂ b h⟩
  have d₃ : DifferentiableOn ℂ (fun b => valAt' (q b) ((PPx yA.x).U (fun _ => j)) (yA.s.f (fun _ => j))) W :=
    (hol _ _).2.mono fun b h => ⟨h.1, m₁ b h⟩
  have key : ∀ b ∈ W, valAt' (q b) ((PPx yA.x).U (fun _ => j)) (yA.s.f (fun _ => j)) =
      κ b * (θ b w₀ * fr j (b, w₀)) := fun b h => by
    obtain ⟨-, -, pm, p₁, p₂, p₃⟩ := hb b h.1
    obtain ⟨pt, e₁, e₂⟩ := exists_pt (R := ℂ) (y b).x (𝟙 _) (F.ex k (P b) w₀).left
      (((Category.id_comp _).trans (hxu b h.1)).trans (Over.w (F.ex k (P b) w₀)).symm)
    rw [← mul_assoc]
    refine Eq.trans ?_ ((hκ b h.1).2 j w₀ pt e₁ e₂ (m₂ b h))
    refine (val_pull (φ b) yA.x (y b).x yA.s (y b).s pm p₁ p₂ p₃ _ pt (q b)
      ((hq b h.1).1.trans e₁.symm) e₂ (hq b h.1).2 ((chart_iff _ _ _).2 ?_)).symm
    rw [e₁]
    exact m₂ b h
  have nz : ∀ b ∈ W, θ b w₀ * fr j (b, w₀) ≠ 0 := fun b h =>
    right_ne_zero_of_mul (key b h ▸ vnz b h)
  have d : DifferentiableOn ℂ κ W := (d₃.mul ((d₁.mul d₂).inv nz)).congr fun b h =>
    ((mul_inv_eq_iff_eq_mul₀ (nz b h)).2 (key b h)).symm
  exact (d.differentiableAt (hW.mem_nhds hb₀W)).differentiableWithinAt

end GlobalTheory.GenFactor
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsHolomorphicFactorGeneratorThetaSectionStatement
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open Formalism.L2.PjFree hiding gxFst gxSnd toC
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif GlobalTheory.FrameNorm
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_holomorphicFactor_generator_thetaSection : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (σ' : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ' ty) (k : Fin F.n) (A : Type) [CommRing A] [Algebra c.F A] (yA : FrPt Xo c A) (m : ℕ) (B : Set (Fin m → ℂ)) (φ : (Fin m → ℂ) → (A →ₐ[c.F] CAt σ)) (y : (Fin m → ℂ) → FrPt Xo c (CAt σ)) (P : (Fin m → ℂ) → ((F.Di k).La →+ (Fin g → ℂ))) (θ : (Fin m → ℂ) → (Fin g → ℂ) → ℂ), IsOpen B → (∀ a, DifferentiableOn ℂ (fun b => toC (φ b a)) B) → (∀ b ∈ B, FrMap (φ b) yA (y b)) → IsHolPeriods (F.Di k) ty B P → (∀ b ∈ B, (y b).x = F.u k (P b)) → (∀ z, DifferentiableOn ℂ (fun b => θ b z) B) → (∀ b ∈ B, ∃ z, θ b z ≠ 0) → IsThetaFrame Xo.univ.t.PP B (fun b => F.u k (P b)) (fun b z => (F.ex k (P b) z).left) θ → ∃ (fr : Xo.univ.t.PP.L.ι → (Fin m → ℂ) × (Fin g → ℂ) → ℂ) (κ : (Fin m → ℂ) → ℂ), RigFrame F k B P fr ∧ DifferentiableOn ℂ κ B ∧ ∀ b ∈ B, κ b ≠ 0 ∧ SecVal F k (P b) (y b).x (y b).s (fun z => κ b * θ b z) (fun j z => fr j (b, z)) := by
  first | exact @GlobalTheory.GenFactor.exists_holomorphic_factor | exact GlobalTheory.GenFactor.exists_holomorphic_factor | (intros; apply GlobalTheory.GenFactor.exists_holomorphic_factor <;> assumption)
end
end
