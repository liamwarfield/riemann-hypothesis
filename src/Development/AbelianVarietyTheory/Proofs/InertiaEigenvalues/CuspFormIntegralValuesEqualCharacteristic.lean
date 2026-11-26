module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormBoundGoodPointsExtendsAllPoints
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupSetFinitelyGenerated

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormIntegralArcSectionEqualChar
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormIntegralArcSectionEqualChar
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GoodPts GlobalTheory.GoodTransfer

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GoodTransfer

open scoped LaurentSeries

theorem inV_of_arc_of_extIn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (Y : Model Xo c (la.valuation c.F).valuationSubring.subtype), PushInvertible Y.t.G Y.t.PP.L → IsOpen (abLocus Y.t.G) → Y.N4 → ∀ (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), Dom a' n → f ∈ cusp Xo c U a' n → (∀ (T₁ : CDVR) (io₁ : c.F →+* T₁.Fr), (∀ k : c.F, io₁ k ∈ (algebraMap T₁.V T₁.Fr).range) → ∀ y₁ : IntFr Xo c T₁ io₁, (letI := io₁.toAlgebra; ExtIn Y (abLocus Y.t.G) T₁ io₁ y₁.1.x) → evI y₁ f ∈ (algebraMap T₁.V T₁.Fr).range) → ∀ (T : CDVR) (io : c.F →+* T.Fr), (∀ k : c.F, io k ∈ (algebraMap T.V T.Fr).range) → (∃ κ : T.Fr →+* ℂ, κ.comp io = c.F.val.toRingHom) → ∀ (b : (la.valuation c.F).valuationSubring →+* T.V), (algebraMap T.V T.Fr).comp b = io.comp (la.valuation c.F).valuationSubring.subtype → ∀ (ϖ : T.V), Irreducible ϖ → ∀ (a : ArcIn Dw l (la.valuation c.F).valuationSubring.subtype T.V b) (y' : Sp T.V ⟶ Y.X), y' ≫ Y.s = spMap b → Y.HasArcData a (Ideal.span {ϖ}) (RingHom.id T.V) ϖ y' → ∀ (y : IntFr Xo c T io) (z : Sp T.Fr ⟶ Xo.XF c), (letI := io.toAlgebra; z ≫ pullback.fst _ _ = y.1.x) → z ≫ pullback.snd _ _ = spMap io → z ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ y' → evI y f ∈ (algebraMap T.V T.Fr).range := by
  intro E _ _ _ H Dw l Xo c r U hU la Y hP hop h4 a' n f hd hf hext T io hioI hκex b hb ϖ hϖ a y' hy' hA y z hz₁ hz₂ hz₃
  let _ := io.toAlgebra
  obtain ⟨h1, h2, -, hL4, hL5⟩ := GlobalTheory.firstFiveLaws
  have hE := GlobalTheory.Frames.allTest_of_secBaseChange h1.secBaseChange E H Dw l Xo c
  have hY : Mono Y.j := GlobalTheory.ThetaShiftProofs.mono_j Y (mono_spMap_subtype _)
  have hcpl : IsAdicComplete (Ideal.span {ϖ}) T.V := hϖ.maximalIdeal_eq ▸ T.cpl
  obtain ⟨χ, hχ, hsp⟩ := h4 T.V b ϖ a (Or.inr ⟨inferInstance, hϖ, hcpl⟩)
  obtain ⟨hover, hab, hopen, hW⟩ := (hχ χ).1 rfl
  obtain ⟨W⟩ := (Y.hasArcData_iff a _ _ _ χ).1 hW
  obtain ⟨-, -, ev, hevC, hevX, -⟩ := GlobalTheory.UniformiserEval.dvr_admissibleBase_and_powerSeries_evalUniformiser T.V ϖ hϖ T.cpl
  have hχy : spMap ev ≫ χ = y' := hsp hϖ y' ev hy' (by
    rintro _ ⟨x, rfl⟩
    exact ⟨z x, by rw [← Scheme.Hom.comp_apply, hz₃]⟩) hA hevC hevX
  obtain ⟨ρ, e, th, y₀, t, he, hth, htan, hρ, hy₀, ht⟩ := GlobalTheory.T.exists_constant_integral_arc_frames E H Dw l Xo c _ Y T io b a χ W ev z hP hb hover
    hevC hz₂ (by rw [hz₃, ← hχy, ← Category.assoc, sp_comp]) y.1 hz₁
  obtain ⟨h, N, hval⟩ := exists_value Y T io b a χ W ϖ hϖ hP hb hover hab ρ e th he hth hρ hf.1

  have hX : PowerSeries.X ^ N ∣ h := by
    obtain ⟨κ, hκ⟩ := hκex
    let κ₀ : T.V →+* ℂ := κ.comp (algebraMap T.V T.Fr)
    have hκ₀ : Function.Injective κ₀ := κ.injective.comp (IsFractionRing.injective T.V T.Fr)
    have hb' : c.F.val.toRingHom.comp (la.valuation c.F).valuationSubring.subtype = κ₀.comp b := by
      rw [RingHom.comp_assoc, hb, ← RingHom.comp_assoc, hκ]
    obtain ⟨⟨a₁, p, hp⟩, hbc⟩ := GlobalTheory.ArcQBC.baseChanges h1 h2 hL4.unifBaseChange hL5 E H Dw l Xo c _ _ Y T.V ℂ b a κ₀
      hκ₀ _ hb'
    obtain ⟨hW₁, hlet, htn, hthx, hnz⟩ := hbc a₁ p hp
    obtain ⟨W₁, hW₁⟩ := hW₁ χ W
    choose e₁ he₁ using fun τ k => (hlet (e τ k)).exists
    obtain ⟨th₁, hth₁⟩ := (hthx th).exists
    let cL : ℂ →+* ℂ⸨X⸩ := (HahnSeries.ofPowerSeries ℤ ℂ).comp (PowerSeries.C (R := ℂ))
    let _ : Algebra c.F ℂ⸨X⸩ := (cL.comp c.F.val.toRingHom).toAlgebra
    have hϖ0 : κ₀ ϖ ≠ 0 := fun h0 => hϖ.ne_zero (hκ₀ (h0.trans (map_zero _).symm))
    obtain ⟨yC, hyC, hv⟩ := hval ℂ⸨X⸩ ((HahnSeries.ofPowerSeries ℤ ℂ).comp (PowerSeries.map κ₀)) (cL.comp κ) (by
        rw [isUnit_iff_ne_zero, RingHom.comp_apply, map_ne_zero_iff _ HahnSeries.ofPowerSeries_injective, map_mul,
          PowerSeries.map_C, PowerSeries.map_X]
        exact mul_ne_zero (fun h => hϖ0 (PowerSeries.C_injective (h.trans (map_zero _).symm))) PowerSeries.X_ne_zero)
      (fun x => by simp [cL, κ₀]) (fun x => congrArg cL (RingHom.congr_fun hκ x).symm)
    have hyC₁ := GlobalTheory.ArcQ.isArcFr_witBC h1 h2 E H Dw l Xo c _ _ Y T.V b a χ W ℂ _ a₁ κ₀ p W₁ hY hp hW₁ e e₁ th th₁ he₁
      hth₁ _ _ yC hyC
    refine X_pow_dvd κ₀ hκ₀ _ (coeff_neg_eq_zero (fun σ => Formalism.L2.PjFree.Unf.ofPj (U σ)) hU c.F.val.toRingHom rfl Y a₁ _
      W₁ hP ?_ (fun x hx => ?_) e₁ th₁ (hnz _ _ hth₁ hth) (fun τ k => htn _ _ (he₁ τ k) (htan τ k)) (fun _ => rfl) yC
      hyC₁ hd hf) ϖ h N hv
    · rw [Category.assoc, hover, sp_comp, sp_comp, sp_comp, hb']
      exact congrArg spMap (RingHom.ext fun x => PowerSeries.map_C κ₀ (b x))
    · rw [Scheme.Hom.comp_apply]
      refine hopen _ fun hm => ?_
      have hm' : PowerSeries.map κ₀ (PowerSeries.C ϖ * PowerSeries.X) ∈ x.asIdeal := hm
      rw [map_mul, PowerSeries.map_C, PowerSeries.map_X] at hm'
      exact hx ((Ideal.unit_mul_mem_iff_mem _ ((IsUnit.mk0 _ hϖ0).map _)).1 hm')
  obtain ⟨h₁, rfl⟩ := hX

  have hG : PowerSeries.C ϖ ^ N ∣ h₁ := by
    obtain ⟨T', ω, i, hω, hωX, hωd, hi, -⟩ := GlobalTheory.T.exists_gaussPoint' T ϖ hϖ
    have hinj := IsFractionRing.injective T'.V T'.Fr
    have hω0 : ω (PowerSeries.C ϖ) ≠ 0 := fun h0 =>
      hϖ.ne_zero (PowerSeries.C_injective ((hω (h0.trans (map_zero _).symm)).trans (map_zero _).symm))
    let _ := (i.comp io).toAlgebra
    obtain ⟨yG, hyG, hv⟩ := hval T'.Fr ((algebraMap T'.V T'.Fr).comp ω) i (by
        rw [isUnit_iff_ne_zero, RingHom.comp_apply, map_ne_zero_iff _ hinj, map_mul]
        exact mul_ne_zero hω0 hωX.ne_zero) hi (fun _ => rfl)
    have hint := GlobalTheory.ArcQ.integral_of_isArcFr h1 h2 E H Dw l Xo c _ _ Y T.V b a χ W ρ e th he hth hP T' (i.comp io) ω
      (hω.comp PowerSeries.C_injective) (fun τ x => (congrArg i (hρ τ x)).trans (hi _)) yG hyG
    obtain ⟨zG, -, -, -, -, k₁, k₂, -⟩ := id hyG
    have hcoef : ∀ k : c.F, (i.comp io) k ∈ (algebraMap T'.V T'.Fr).range := fun k => by
      obtain ⟨a₀, ha₀⟩ := hioI k
      exact ⟨ω (PowerSeries.C a₀), by rw [RingHom.comp_apply, ← ha₀, hi]⟩
    obtain ⟨x, hx⟩ := hext T' (i.comp io) hcoef ⟨yG, hE _ yG, hint⟩
      ⟨spMap ω ≫ χ, zG, k₂, snd_eq Y zG _ (by
        rw [← Category.assoc, k₁, Category.assoc, hover, sp_comp, sp_comp, RingHom.comp_assoc _ io, ← hb]
        exact congrArg spMap (RingHom.ext fun x => (hi _).symm)),
       by rw [k₁, ← Category.assoc, sp_comp], by
        rintro _ ⟨x, rfl⟩
        rw [Scheme.Hom.comp_apply, hab]
        exact fun hx => x.isPrime.ne_top
          (Ideal.eq_top_of_isUnit_mem _ (show ω PowerSeries.X ∈ x.asIdeal from hx) hωX)⟩
    have hx' : algebraMap T'.V T'.Fr x = evR Xo c f yG := hx
    rw [← hx', RingHom.comp_apply, RingHom.comp_apply, ← map_mul] at hv
    have hv₁ := hinj hv
    refine pow_dvd_of_map ω hω0 hωd N h₁ ⟨x, mul_left_cancel₀ (pow_ne_zero N hωX.ne_zero) ?_⟩
    simp only [map_mul, map_pow, mul_pow] at hv₁
    rw [← hv₁]; ring
  obtain ⟨h₂, rfl⟩ := hG

  have hinj := IsFractionRing.injective T.V T.Fr
  have hne : (algebraMap T.V T.Fr).comp ev (PowerSeries.C ϖ * PowerSeries.X) ≠ 0 := by
    rw [RingHom.comp_apply, map_ne_zero_iff _ hinj, map_mul, hevC, hevX]
    exact mul_ne_zero hϖ.ne_zero hϖ.ne_zero
  obtain ⟨y₁, hy₁, hv⟩ := hval T.Fr ((algebraMap T.V T.Fr).comp ev) (RingHom.id _) (isUnit_iff_ne_zero.2 hne)
    (fun x => by rw [RingHom.comp_apply, hevC]; rfl) (fun _ => rfl)
  obtain rfl : y₁ = y₀ := (GlobalTheory.ArcQ.isArcFr_unique_baseChange h1 h2 E H Dw l Xo c _ _ Y T.V b a χ W e th hth _ _ y₀
    hy₀).1 hY y₁ hy₁
  have hint := GlobalTheory.ArcQ.integral_of_isArcFr h1 h2 E H Dw l Xo c _ _ Y T.V b a χ W ρ e th he hth hP T io ev
    (fun x x' hx => (hevC x).symm.trans (hx.trans (hevC x'))) (fun τ x => by rw [hevC]; exact hρ τ x) y₁ hy₁
  show InV T (evI y f)
  rw [← inV_of_frBor hf.1 ⟨y₁, hE _ y₁, hint⟩ y t ht]
  refine ⟨ev h₂, mul_right_cancel₀ (pow_ne_zero N hne) ?_⟩
  rw [← map_pow]
  refine Eq.trans ?_ hv.symm
  simp only [RingHom.comp_apply, map_mul, map_pow, mul_pow]
  ring

end GlobalTheory.GoodTransfer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormIntegralArcSectionEqualCharStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GoodPts GlobalTheory.GoodTransfer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_integral_arc_section_equalChar : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (Y : Model Xo c (la.valuation c.F).valuationSubring.subtype), PushInvertible Y.t.G Y.t.PP.L → IsOpen (abLocus Y.t.G) → Y.N4 → ∀ (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), Dom a' n → f ∈ cusp Xo c U a' n → (∀ (T₁ : CDVR) (io₁ : c.F →+* T₁.Fr), (∀ k : c.F, io₁ k ∈ (algebraMap T₁.V T₁.Fr).range) → ∀ y₁ : IntFr Xo c T₁ io₁, (letI := io₁.toAlgebra; ExtIn Y (abLocus Y.t.G) T₁ io₁ y₁.1.x) → evI y₁ f ∈ (algebraMap T₁.V T₁.Fr).range) → ∀ (T : CDVR) (io : c.F →+* T.Fr), (∀ k : c.F, io k ∈ (algebraMap T.V T.Fr).range) → (∃ κ : T.Fr →+* ℂ, κ.comp io = c.F.val.toRingHom) → ∀ (b : (la.valuation c.F).valuationSubring →+* T.V), (algebraMap T.V T.Fr).comp b = io.comp (la.valuation c.F).valuationSubring.subtype → ∀ (ϖ : T.V), Irreducible ϖ → ∀ (a : ArcIn Dw l (la.valuation c.F).valuationSubring.subtype T.V b) (y' : Sp T.V ⟶ Y.X), y' ≫ Y.s = spMap b → Y.HasArcData a (Ideal.span {ϖ}) (RingHom.id T.V) ϖ y' → ∀ (y : IntFr Xo c T io) (z : Sp T.Fr ⟶ Xo.XF c), (letI := io.toAlgebra; z ≫ pullback.fst _ _ = y.1.x) → z ≫ pullback.snd _ _ = spMap io → z ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ y' → evI y f ∈ (algebraMap T.V T.Fr).range := by
  first | exact @GlobalTheory.GoodTransfer.inV_of_arc_of_extIn | exact GlobalTheory.GoodTransfer.inV_of_arc_of_extIn | (intros; apply GlobalTheory.GoodTransfer.inV_of_arc_of_extIn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SectionIntegralEqualCharAbelianLocus
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SectionIntegralEqualCharAbelianLocus
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GoodPts GlobalTheory.GoodTransfer

namespace GlobalTheory.EqCharGood

theorem existsUnique_mulVec_of_inCell {V K : Type} [CommRing V] [CommRing K] (φ : V →+* K)
    (hφ : Function.Injective φ) {n r : ℕ} (ix : Fin r ↪ Fin n) (u : Matrix (Fin n) (Fin r) V)
    (hc : GlobalTheory.Reg.InCell ix u) (cv : Fin n → V) (aK : Fin r → K)
    (h : (u.map φ).mulVec aK = fun i => φ (cv i)) : ∃! a, u.mulVec a = cv := by
  let A : Matrix (Fin r) (Fin r) V := u.submatrix ix id
  have hlow : A.BlockTriangular OrderDual.toDual := fun i j hij => hc.1 i j hij
  have hdet : A.det = 1 := by
    rw [Matrix.det_of_lowerTriangular A hlow]
    exact Finset.prod_eq_one fun i _ => hc.2 i
  have hAu : IsUnit A.det := hdet ▸ isUnit_one
  have hAK : IsUnit (A.map φ).det := by
    have e : (A.map φ).det = φ A.det := (RingHom.map_det φ A).symm
    rw [e, hdet, map_one]; exact isUnit_one
  have hinjA : ∀ v w : Fin r → V, A.mulVec v = A.mulVec w → v = w := fun v w hvw => by
    have := congrArg (A⁻¹).mulVec hvw
    rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hAu, Matrix.one_mulVec,
      Matrix.one_mulVec] at this
  have hinjAK : ∀ v w : Fin r → K, (A.map φ).mulVec v = (A.map φ).mulVec w → v = w := fun v w hvw => by
    have := congrArg ((A.map φ)⁻¹).mulVec hvw
    rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hAK, Matrix.one_mulVec,
      Matrix.one_mulVec] at this
  have hrow : ∀ (v : Fin r → V), A.mulVec v = fun i => u.mulVec v (ix i) := fun v => rfl
  let a : Fin r → V := A⁻¹.mulVec (fun i => cv (ix i))
  have ha : A.mulVec a = fun i => cv (ix i) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hAu, Matrix.one_mulVec]
  have hmap : ∀ (M : Matrix (Fin n) (Fin r) V) (v : Fin r → V),
      (M.map φ).mulVec (fun i => φ (v i)) = fun i => φ (M.mulVec v i) := fun M v => by
    funext i
    exact (RingHom.map_mulVec φ M v i).symm
  have haK : (fun i => φ (a i)) = aK := by
    refine hinjAK _ _ ?_
    have e1 : (A.map φ).mulVec (fun i => φ (a i)) = fun i => φ (cv (ix i)) := by
      funext i
      exact (congrFun (hmap u a) (ix i)).trans (congrArg φ (congrFun ha i))
    rw [e1]
    funext i
    exact (congrFun h (ix i)).symm
  refine ⟨a, ?_, fun a' ha' => hinjA _ _ ((hrow a').trans ((funext fun i => congrFun ha' (ix i)).trans ha.symm))⟩
  funext i
  apply hφ
  have := congrFun (hmap u a) i
  rw [haK, h] at this
  exact this.symm

end GlobalTheory.EqCharGood

namespace GlobalTheory.EqCharGood


set_option maxHeartbeats 2000000 in
theorem inV_of_extIn_eqChar : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), f ∈ sec Xo c a n → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (Y : Model Xo c (la.valuation c.F).valuationSubring.subtype), PushInvertible Y.t.G Y.t.PP.L → ∀ (T : CDVR) (io : c.F →+* T.Fr), (∀ k : c.F, io k ∈ (algebraMap T.V T.Fr).range) → ∀ y : IntFr Xo c T io, (letI := io.toAlgebra; ExtIn Y (abLocus Y.t.G) T io y.1.x) → evI y f ∈ (algebraMap T.V T.Fr).range := by
  intro E _ _ _ H Dw l Xo c a n f hf la Y hP T io hio y hy
  classical
  obtain ⟨hE, -, -⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  have hS := GlobalTheory.abelianSchemeLaws_all.2.secTwist
  have hinj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective T.V T.Fr
  obtain ⟨k, hk⟩ := exists_factor T io hio
  obtain ⟨y', z, h1, h2, h3, h4⟩ := hy
  have hs : y' ≫ Y.s = spMap (k.comp (la.valuation c.F).valuationSubring.subtype) := by
    have e1 : spMap (algebraMap T.V T.Fr) ≫ (y' ≫ Y.s) =
        spMap (algebraMap T.V T.Fr) ≫ spMap (k.comp (la.valuation c.F).valuationSubring.subtype) := by
      rw [← Category.assoc, ← h3, Category.assoc, GlobalTheory.TraitDataIntrinsic.j_s, ← Category.assoc, h2, sp_comp,
        sp_comp, ← RingHom.comp_assoc, hk]
    obtain ⟨φ, hφ⟩ : ∃ φ : (la.valuation c.F).valuationSubring →+* T.V, y' ≫ Y.s = spMap φ :=
      ⟨(Spec.preimage (y' ≫ Y.s)).hom, by simp [spMap]⟩
    rw [hφ, sp_comp, sp_comp] at e1
    rw [hφ]
    congr 1
    have e2 := CommRingCat.hom_ext_iff.1 (Spec.map_injective e1)
    exact RingHom.ext fun x => hinj (RingHom.congr_fun e2 x)
  let _ : Algebra c.F T.V := k.toAlgebra
  let _ : Algebra c.F T.Fr := io.toAlgebra
  obtain ⟨zV, hzV1, hzV2⟩ := exists_lift Y y' k hs h4
  obtain ⟨J, _, M, hM⟩ := GlobalTheory.Reg.exists_finite_mchart_cover E H Dw l Xo c (la.valuation c.F).valuationSubring _ Y hP
  obtain ⟨j, hj⟩ := hM (y' (IsLocalRing.closedPoint T.V))
  obtain ⟨-, -, h3'⟩ := GlobalTheory.ModelPoints.model_points_charts E H Dw l Xo c _ _ Y
  obtain ⟨-, -, -, h4'⟩ := h3' (M j).U (M j).hU
  obtain ⟨f₀, hf₀, -⟩ := h4' T.V y' hj
  obtain ⟨ΛV⟩ := GlobalTheory.Reg.MChart.nonempty_lift E H Dw l Xo c _ _ Y (M j) T.V f₀ zV hzV2 (hzV1.trans hf₀.symm)
  have hzj : z ≫ Y.j = spMap ((algebraMap T.V T.Fr).comp f₀) ≫ (M j).hU.fromSpec := by
    rw [h3, ← hf₀, ← Category.assoc, sp_comp]
  have hK := GlobalTheory.Reg.MChart.nonempty_lift E H Dw l Xo c _ _ Y (M j) T.Fr _ z h2 hzj
  rw [h1] at hK
  obtain ⟨ΛK⟩ := hK
  obtain ⟨g, hg, hgi⟩ := GlobalTheory.Reg.MChart.Lift.exists_coordinates E H Dw l Xo c _ _ Y (M j) T.Fr _ y.1 ΛK
  let W : ValuationSubring T.Fr := (valV T.V).valuationSubring
  have hW : ∀ x, x ∈ W → InV T x := fun x h => IsDiscreteValuationRing.exists_lift_of_le_one (A := T.V) (K := T.Fr) h
  choose ix u b huW hu0 hu1 hbt hbd hgub using
    fun τ => GlobalTheory.exists_integral_pivot_decomposition T.Fr W _ _ (g τ) (hgi τ)
  choose u₀' hu₀' using fun τ i j => hW _ (huW τ i j)
  let u₀ : ∀ τ : E →+* ℂ, Matrix (Fin (M j).n) (Fin (Dw.mult τ)) T.V := fun τ => Matrix.of fun i j' => u₀' τ i j'
  have hu₀ : ∀ τ i j', algebraMap T.V T.Fr (u₀ τ i j') = u τ i j' := hu₀'
  have hcell : ∀ τ, GlobalTheory.Reg.InCell (ix τ) (u₀ τ) := fun τ =>
    ⟨fun i j hij => hinj (by rw [hu₀, map_zero]; exact hu0 τ i j hij),
     fun i => hinj (by rw [hu₀, map_one]; exact hu1 τ i)⟩

  have heigMap : ∀ τ (cv : Fin (M j).n → T.V),
      (M j).Eig ((algebraMap T.V T.Fr).comp f₀) τ (fun i => algebraMap T.V T.Fr (cv i)) ↔ (M j).Eig f₀ τ cv := by
    intro τ cv
    refine forall_congr' fun a' => ?_
    have key : ∀ i, algebraMap T.V T.Fr ((((M j).ρ a').map f₀).mulVec cv i) =
        ((((M j).ρ a').map ((algebraMap T.V T.Fr).comp f₀)).mulVec (fun i => algebraMap T.V T.Fr (cv i))) i :=
      fun i => by rw [RingHom.map_mulVec]; rfl
    have key2 : ∀ i, algebraMap T.V T.Fr ((algebraMap c.F T.V (embK c τ a') • cv) i) =
        (algebraMap c.F T.Fr (embK c τ a') • fun i => algebraMap T.V T.Fr (cv i)) i := fun i => by
      simp only [Pi.smul_apply, smul_eq_mul, map_mul]
      exact congrArg (· * _) (RingHom.congr_fun hk _)
    constructor
    · intro h
      funext i
      apply hinj
      rw [key, key2]
      exact congrFun h i
    · intro h
      funext i
      rw [← key, ← key2, h]
  have humap : ∀ τ, (u₀ τ).map (algebraMap T.V T.Fr) = u τ := fun τ => Matrix.ext fun i j' => hu₀ τ i j'
  have heigK : ∀ τ i, (M j).Eig ((algebraMap T.V T.Fr).comp f₀) τ (fun j' => u τ j' i) := by
    intro τ i a'
    have hgc : ∀ i, (M j).Eig ((algebraMap T.V T.Fr).comp f₀) τ (fun j' => g τ j' i) := fun i =>
      (GlobalTheory.Reg.isEigAt_iff_eig E H Dw l Xo c _ _ Y (M j) T.Fr _ y.1.x ΛK τ _ _ (hg τ i)).mp (y.1.eig τ i)
    have hG := (GlobalTheory.Reg.CellChart.mul_eq_smul_iff_cols (((M j).ρ a').map ((algebraMap T.V T.Fr).comp f₀))
      (algebraMap c.F T.Fr (embK c τ a')) (g τ)).mpr fun i => hgc i a'
    have hd : IsUnit (b τ).det := by
      rw [Matrix.det_of_upperTriangular (hbt τ)]
      exact (Finset.prod_ne_zero_iff.mpr fun i _ => hbd τ i).isUnit
    have hU : ((M j).ρ a').map ((algebraMap T.V T.Fr).comp f₀) * u τ = algebraMap c.F T.Fr (embK c τ a') • u τ := by
      have e : u τ = g τ * (b τ)⁻¹ := by rw [hgub τ, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
      rw [e, ← Matrix.mul_assoc, hG, Matrix.smul_mul]
    exact (GlobalTheory.Reg.CellChart.mul_eq_smul_iff_cols _ _ _).mp hU i
  have heigV : ∀ τ i, (M j).Eig f₀ τ (fun j' => u₀ τ j' i) := fun τ i =>
    (heigMap τ _).mp (by simpa only [hu₀] using heigK τ i)
  obtain ⟨hv1, hv2, hv3⟩ := GlobalTheory.Reg.vec_bijective E H Dw l Xo c _ _ Y (M j) T.Fr _ y.1.x ΛK
  have hbasis : ∀ τ cv, (M j).Eig f₀ τ cv → ∃! a, (u₀ τ).mulVec a = cv := by
    intro τ cv hcv
    have hcvK := (heigMap τ cv).mpr hcv
    obtain ⟨w, hw, -⟩ := hv1 (fun i => algebraMap T.V T.Fr (cv i))
    have htan := hv2 _ _ hw
    have heig := (GlobalTheory.Reg.isEigAt_iff_eig E H Dw l Xo c _ _ Y (M j) T.Fr _ y.1.x ΛK τ _ _ hw).mpr hcvK
    obtain ⟨a0, ha0, -⟩ := y.1.basis τ w htan heig
    have hv := (GlobalTheory.T.isCombAt_iff_coordinate_combination E H Dw l Xo c _ _ Y (M j) T.Fr _ y.1.x ΛK _ (fun i j' => g τ j' i) (y.1.u τ) a0 w
      (hg τ)).mp ha0
    have heq : (∑ i, a0 i • fun j' => g τ j' i) = fun i => algebraMap T.V T.Fr (cv i) := (hv3 w htan).unique hv hw
    refine GlobalTheory.EqCharGood.existsUnique_mulVec_of_inCell (algebraMap T.V T.Fr) hinj (ix τ) (u₀ τ) (hcell τ) cv
      ((b τ).mulVec a0) ?_
    rw [humap, Matrix.mulVec_mulVec, ← hgub τ, ← heq]
    funext j'
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  obtain ⟨yV, -, hyV⟩ := GlobalTheory.Reg.exists_frPt_tie hS E H Dw l Xo c _ _ Y (M j) T.V f₀ _ ΛV u₀ heigV hbasis
  let φ : T.V →ₐ[c.F] T.Fr := ⟨algebraMap T.V T.Fr, fun x => RingHom.congr_fun hk x⟩
  obtain ⟨zK, hzK⟩ := hE.bc _ _ φ yV
  have htK := GlobalTheory.Reg.MChart.tie_baseChange E H Dw l Xo c _ _ Y (M j) T.V T.Fr f₀ φ u₀ yV zK hyV hzK
  have hint : Integral T io zK := GlobalTheory.Reg.tie_integral hS E H Dw l Xo c _ _ Y (M j) hP T io f₀ ix u₀ hcell zK
    (GlobalTheory.Reg.CellChart.tie_congr htK (fun _ => rfl) (fun _ _ _ => rfl))
  have htu : (M j).Comparison₂ ((algebraMap T.V T.Fr).comp f₀) u zK :=
    GlobalTheory.Reg.CellChart.tie_congr htK (fun _ => rfl) (fun τ i j' => hu₀ τ i j')
  obtain ⟨t, ht⟩ := GlobalTheory.Reg.frBor_of_tie E H Dw l Xo c _ _ Y (M j) T.Fr _ y.1 zK ΛK u b
    (GlobalTheory.Reg.CellChart.lift_point_unique htu.choose ΛK) (fun τ => ⟨hbt τ, hbd τ⟩)
    (by rw [show (fun τ => u τ * b τ) = g from funext fun τ => (hgub τ).symm]; exact hg) htu
  show InV T (evI y f)
  rw [inV_of_frBor hf y ⟨zK, hE.test _ zK, hint⟩ t ht]
  show InV T (evR Xo c f zK)
  rw [(GlobalTheory.ArcQ.evR_natural_weight_scaling E H Dw l Xo c hE a n f hf T.V).1 T.Fr φ yV zK hzK]
  exact ⟨_, rfl⟩

end GlobalTheory.EqCharGood
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SectionIntegralEqualCharAbelianLocusStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GoodPts GlobalTheory.GoodTransfer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_integral_equalChar_abelianLocus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), f ∈ sec Xo c a n → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (Y : Model Xo c (la.valuation c.F).valuationSubring.subtype), PushInvertible Y.t.G Y.t.PP.L → ∀ (T : CDVR) (io : c.F →+* T.Fr), (∀ k : c.F, io k ∈ (algebraMap T.V T.Fr).range) → ∀ y : IntFr Xo c T io, (letI := io.toAlgebra; ExtIn Y (abLocus Y.t.G) T io y.1.x) → evI y f ∈ (algebraMap T.V T.Fr).range := by
  first | exact @GlobalTheory.EqCharGood.inV_of_extIn_eqChar | exact GlobalTheory.EqCharGood.inV_of_extIn_eqChar | (intros; apply GlobalTheory.EqCharGood.inV_of_extIn_eqChar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsComplexEmbeddingFractionFieldFiniteOverCdv
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsComplexEmbeddingFractionFieldFiniteOverCdv
open NumberField Formalism.L2.Pj

namespace GlobalTheory.ComplexEmbedding

open Cardinal IsLocalRing

theorem exists_digits_of_dvr (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (ϖ : V) (hϖ : Irreducible ϖ) (s : ResidueField V → V) (hs : ∀ r, residue V (s r) = r) :
    ∀ (n : ℕ) (x : V), ∃ f : Fin n → ResidueField V,
      x - ∑ i : Fin n, s (f i) * ϖ ^ (i : ℕ) ∈ maximalIdeal V ^ n := by
  intro n
  induction n with
  | zero => intro x; exact ⟨Fin.elim0, by simp⟩
  | succ n ih =>
    intro x
    obtain ⟨f, hf⟩ := ih x
    have hm : maximalIdeal V = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
    have hf' := hf
    rw [hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hf'
    obtain ⟨y, hy⟩ := hf'
    refine ⟨Fin.snoc f (residue V y), ?_⟩
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.coe_castSucc, Fin.val_last]
    have hxy : x - (∑ i : Fin n, s (f i) * ϖ ^ (i : ℕ) + s (residue V y) * ϖ ^ n) =
        ϖ ^ n * (y - s (residue V y)) := by
      rw [← sub_sub, hy]; ring
    rw [hxy, pow_succ]
    have hϖm : ϖ ∈ maximalIdeal V := (mem_maximalIdeal _).2 hϖ.not_isUnit
    have hym : y - s (residue V y) ∈ maximalIdeal V := by
      rw [← residue_eq_zero_iff, map_sub, hs, sub_self]
    exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hϖm n) hym

theorem countable_quotient_pow_of_dvr (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Countable (ResidueField V)] (n : ℕ) : Countable (V ⧸ maximalIdeal V ^ n) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  let s : ResidueField V → V := Function.surjInv (residue_surjective (R := V))
  have hs : ∀ r, residue V (s r) = r := Function.surjInv_eq _
  have hsurj : Function.Surjective (fun f : Fin n → ResidueField V =>
      Ideal.Quotient.mk (maximalIdeal V ^ n) (∑ i : Fin n, s (f i) * ϖ ^ (i : ℕ))) := by
    intro q
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨f, hf⟩ := exists_digits_of_dvr V ϖ hϖ s hs n x
    exact ⟨f, (Ideal.Quotient.eq.2 hf).symm⟩
  exact hsurj.countable

theorem mk_le_continuum_of_countable_residueField (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [Countable (ResidueField V)] : #V ≤ 𝔠 := by
  let f : V → ∀ n : ℕ, V ⧸ maximalIdeal V ^ n := fun x n => Ideal.Quotient.mk _ x
  have hinj : Function.Injective f := by
    intro x y hxy
    have : x - y ∈ ⨅ n : ℕ, maximalIdeal V ^ n :=
      Ideal.mem_iInf.2 fun n => Ideal.Quotient.eq.1 (congrFun hxy n)
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal V).ne_top] at this
    exact sub_eq_zero.1 this
  refine (mk_le_of_injective hinj).trans ?_
  rw [mk_pi]
  refine (prod_le_prod _ (fun _ => ℵ₀) fun n =>
    haveI := countable_quotient_pow_of_dvr V n; mk_le_aleph0).trans ?_
  simp

theorem exists_embedding_fractionField_of_finite :
    ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (T T' : CDVR) (g : T.V →+* T'.V),
      Function.Injective g → g.Finite → Countable (IsLocalRing.ResidueField T.V) →
      ∀ io : K →+* T'.Fr, ∃ ι : T'.Fr →+* ℂ, ι.comp io = σ := by
  intro K _ _ σ T T' g _ hfin hc io
  have hV : #T.V ≤ 𝔠 := mk_le_continuum_of_countable_residueField T.V
  letI : Algebra T.V T'.V := g.toAlgebra
  haveI : Module.Finite T.V T'.V := hfin
  obtain ⟨d, φ, hφ⟩ := Module.Finite.exists_fin' T.V T'.V
  have hV' : #T'.V ≤ 𝔠 := by
    refine (mk_le_of_surjective hφ).trans ?_
    rw [mk_arrow, mk_fin, lift_id, lift_natCast]
    refine (power_le_power_right hV).trans ?_
    exact power_nat_le aleph0_le_continuum
  have hF : #T'.Fr ≤ 𝔠 := by
    rw [show #T'.Fr = #T'.V from IsFractionRing.cardinalMk T'.V T'.Fr]
    exact hV'
  exact @exists_embedding_of_mk_le_continuum K T'.Fr _ _ _ io.toAlgebra hF σ

end GlobalTheory.ComplexEmbedding
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsComplexEmbeddingFractionFieldFiniteOverCdvStatement
open NumberField Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complex_embedding_fractionField_finite_over_cdvr : ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (T T' : CDVR) (g : T.V →+* T'.V), Function.Injective g → g.Finite → Countable (IsLocalRing.ResidueField T.V) → ∀ io : K →+* T'.Fr, ∃ ι : T'.Fr →+* ℂ, ι.comp io = σ := by
  first | exact @GlobalTheory.ComplexEmbedding.exists_embedding_fractionField_of_finite | exact GlobalTheory.ComplexEmbedding.exists_embedding_fractionField_of_finite | (intros; apply GlobalTheory.ComplexEmbedding.exists_embedding_fractionField_of_finite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormIntegralValuesEqualCharacteristic
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EqCharCusp

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GoodPts GlobalTheory.GoodTransfer

theorem exists_goodAt {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (l : Level H) :
    ∃ p : ℕ, p.Prime ∧ l.GoodAt p := by
  obtain ⟨p, hle, hp⟩ := Nat.exists_infinite_primes (l.M + 1)
  refine ⟨p, hp, ?_⟩
  have h3 := l.three_le
  have hM : ¬ p ∣ l.M := fun hd => by have := Nat.le_of_dvd (by omega) hd; omega
  unfold Level.GoodAt
  rw [Nat.factorization_eq_zero_of_not_dvd hM]
  simpa using h3

theorem exists_place (K : Type) [Field K] [NumberField K] (p : ℕ) (hp : p.Prime) :
    ∃ la : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ la.asIdeal := by
  have hP : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).2 (Nat.prime_iff_prime_int.mp hp)
  obtain ⟨Q, -, hQ, hQl⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 K) (Ideal.span {(p : ℤ)}) ⊥
    (by rw [(show Ideal.under _ ⊥ = ⊥ from Ideal.comap_bot_of_injective _ (algebraMap ℤ (𝓞 K)).injective_int)]; exact bot_le)
  have hpQ : (p : 𝓞 K) ∈ Q := by
    have : ((p : ℤ)) ∈ Ideal.under ℤ Q := by
      rw [hQl]
      exact Ideal.mem_span_singleton_self _
    simpa using this
  refine ⟨⟨Q, hQ, fun h => ?_⟩, hpQ⟩
  rw [h] at hQl
  change Ideal.comap (algebraMap ℤ (𝓞 K)) ⊥ = _ at hQl
  rw [Ideal.comap_bot_of_injective _ (algebraMap ℤ (𝓞 K)).injective_int] at hQl
  have : ((p : ℤ)) ∈ (⊥ : Ideal ℤ) := hQl ▸ Ideal.mem_span_singleton_self _
  exact hp.ne_zero (by exact_mod_cast (Ideal.mem_bot.1 this))

theorem integral_of_eqChar : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), Dom a n → f ∈ cusp Xo c U a n → ∀ (T : CDVR), Countable (IsLocalRing.ResidueField T.V) → ∀ (io : c.F →+* T.Fr), (∀ k : c.F, io k ∈ (algebraMap T.V T.Fr).range) → ∀ y : IntFr Xo c T io, evI y f ∈ (algebraMap T.V T.Fr).range := by
  intro E _ _ _ H Dw l Xo c r U hU a n f hd hf T hcnt io hint y
  obtain ⟨p, hp, hg⟩ := exists_goodAt l
  obtain ⟨la, hpl⟩ := exists_place c.F p hp
  let _ := io.toAlgebra
  obtain ⟨b, hb⟩ := exists_factor T (io.comp (la.valuation c.F).valuationSubring.subtype) (fun x => hint _)
  let z : Sp T.Fr ⟶ Xo.XF c := pullback.lift y.1.x (spMap io) (y.1.x_over.trans (sp_comp _ _).symm)
  have hz₁ : z ≫ pullback.fst _ _ = y.1.x := pullback.lift_fst _ _ _
  have hz₂ : z ≫ pullback.snd _ _ = spMap io := pullback.lift_snd _ _ _
  have hA : ∀ Y : Model Xo c (la.valuation c.F).valuationSubring.subtype, PushInvertible Y.t.G Y.t.PP.L →
      ∀ y' : Sp T.V ⟶ Y.X, z ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ y' → Set.range y' ⊆ abLocus Y.t.G →
      evI y f ∈ (algebraMap T.V T.Fr).range := fun Y hP y' h3 hr =>
    GlobalTheory.T.section_integral_equalChar_abelianLocus E H Dw l Xo c a n f hf.1 la Y hP T io hint y ⟨y', z, hz₁, hz₂, h3, hr⟩
  rcases Nat.eq_zero_or_pos (Dw.p + Dw.q) with hD | hD
  · obtain ⟨Y, hP⟩ := GlobalTheory.SupFinite.exists_model_rank_zero Xo c hD (la.valuation c.F).valuationSubring.subtype
    obtain ⟨⟨y', ⟨-, hz₃⟩, -⟩, -⟩ :=
      GlobalTheory.ValuativeExtension.valuation_extension E H Dw l Xo c _ _ Y T.V T.Fr b io z hb hz₂
    refine hA Y hP y' hz₃.symm ?_
    rw [GlobalTheory.DefiniteAbelian.abLocus_eq_univ (by omega) _ Y]
    exact Set.subset_univ _
  obtain ⟨Y, hP, hop, hS, h3, h4⟩ := exists_model (by omega) Xo c la p hp hpl hg
  obtain ⟨⟨y', ⟨hy', hz₃⟩, -⟩, -⟩ :=
    GlobalTheory.ValuativeExtension.valuation_extension E H Dw l Xo c _ _ Y T.V T.Fr b io z hb hz₂
  by_cases hr : Set.range y' ⊆ abLocus Y.t.G
  · exact hA Y hP y' hz₃.symm hr
  obtain ⟨T', g, ϖ, a₀, hg₁, hg₂, hϖ, hA'⟩ := GlobalTheory.T.exists_arcData_of_badReduction_finiteExtension E H Dw l Xo c _ Y h3 hS T io b y' z hb hy' hz₂ hz₃.symm hr
  obtain ⟨i, ρ, hρ, hi, hv, -⟩ := GlobalTheory.EtaVal.finite_extension_ramification_embedding T T' g hg₁ hg₂
  obtain ⟨y₁, φ, hφ, hy₁⟩ := GlobalTheory.IntFrBaseChange.exists_intFr_baseChange E H Dw l Xo c T T' io y i ρ hρ
    (fun x _ => hv x)
  let _ := (i.comp io).toAlgebra
  have e₁ : (algebraMap T'.V T'.Fr).comp g = i.comp (algebraMap T.V T.Fr) := RingHom.ext fun x => (hi x).symm
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.exists_complex_embedding_fractionField_finite_over_cdvr c.F c.F.val.toRingHom T T' g hg₁ hg₂ hcnt (i.comp io)
  have hint' : ∀ k : c.F, (i.comp io) k ∈ (algebraMap T'.V T'.Fr).range := fun k => by
    obtain ⟨v, hv'⟩ := hint k
    exact ⟨g v, by rw [RingHom.comp_apply, ← hv', hi]⟩
  have key := GlobalTheory.T.cuspForm_integral_arc_section_equalChar E H Dw l Xo c r U hU la Y hP hop h4 a n f hd hf
    (fun T₁ io₁ h₁ y₂ hy₂ => GlobalTheory.T.section_integral_equalChar_abelianLocus E H Dw l Xo c a n f hf.1 la Y hP T₁ io₁ h₁ y₂ hy₂)
    T' (i.comp io) hint' ⟨κ, hκ⟩ (g.comp b)
    (by rw [← RingHom.comp_assoc, e₁, RingHom.comp_assoc, hb]; rfl) ϖ hϖ a₀ (spMap g ≫ y')
    (by rw [Category.assoc, hy', sp_comp]) hA' y₁ (spMap i ≫ z)
    (by rw [Category.assoc, hz₁, hy₁.1, hφ]) (by rw [Category.assoc, hz₂, sp_comp])
    (by rw [Category.assoc, ← hz₃, ← Category.assoc, ← Category.assoc, sp_comp, sp_comp, e₁])
  have hE : GlobalTheory.Reg.EvLaws Xo c := by
    have hB : Out.SecBaseChangeSt := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
    obtain ⟨-, -, hwd, hwt, hint, -⟩ := GlobalTheory.T.framedModuli_algebraicLaws_chart_weight_integrality hB E H Dw l Xo c
    have hbc : GlobalTheory.Reg.FrBC Xo c := fun S T _ _ _ _ φ y =>
      GlobalTheory.Frames.FramedBaseChange.exists_frMap hB E H Dw l Xo c S T φ y
    exact ⟨hwd, GlobalTheory.T.framedPoint_reduced_from_testRing hB E H Dw l Xo c, hwt, hbc⟩
  have e₂ : evI y₁ f = φ (evI y f) :=
    (GlobalTheory.ArcQ.evR_natural_weight_scaling E H Dw l Xo c hE a n f hf.1 T.Fr).1 _ φ _ _ hy₁
  have e₃ : φ (evI y f) = i (evI y f) := RingHom.congr_fun hφ _
  have key' : InV T' (i (evI y f)) := by rw [← e₃, ← e₂]; exact key
  rw [inV_iff, hv] at key'
  show InV T (evI y f)
  rw [inV_iff]
  exact nonneg_of_mul_nonneg_right key' (by exact_mod_cast hρ)

end GlobalTheory.EqCharCusp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormIntegralValuesEqualCharacteristicStatement
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_integral_values_equal_characteristic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), Dom a n → f ∈ cusp Xo c U a n → ∀ (T : CDVR), Countable (IsLocalRing.ResidueField T.V) → ∀ (io : c.F →+* T.Fr), (∀ k : c.F, io k ∈ (algebraMap T.V T.Fr).range) → ∀ y : IntFr Xo c T io, evI y f ∈ (algebraMap T.V T.Fr).range := by
  first | exact @GlobalTheory.EqCharCusp.integral_of_eqChar | exact GlobalTheory.EqCharCusp.integral_of_eqChar | (intros; apply GlobalTheory.EqCharCusp.integral_of_eqChar <;> assumption)
end
