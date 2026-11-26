module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModuliConsequenceOfAbelianSchemeLaws
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TestPointValueEqConstMulReading
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralFrameAfterExtIffAnd
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SelfDualLatticeOccurs
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasseNormTheoremQuadraticExtension
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsThetaPtStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CompNonemptyFiniteGenFrTrdeg
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

theorem GlobalTheory.Exist.comp_nonempty_finite_genFr_trdeg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → Nonempty (Comp Xo c) ∧ Finite (Comp Xo c) ∧ ∃ h : GenFrEx Xo c, GenFromTest Xo c h ∧ (∀ Z, evC h Z 1 = 1) ∧ ∀ Z : Comp Xo c, Algebra.trdeg c.F (kap Z) = Dw.dim := by
  intro E _ _ _ H Dw l Xo c h1
  have hB : Out.SecBaseChangeSt := GlobalTheory.allSixLaws.1.secBaseChange
  have hT : Out.SecTwistSt := GlobalTheory.allSixLaws.2.1.secTwist
  have hA : AllTest Xo c := GlobalTheory.Frames.allTest_of_secBaseChange hB E H Dw l Xo c
  have h : GenFrEx Xo c := genFrEx_of hT
  have hg : GenFromTest Xo c h := fun Z => hA _ _
  obtain ⟨x⟩ := (GlobalTheory.PeriodExists.typeFn_period_exist E H Dw).2.2 GlobalTheory.closing_of_abelianSchemeLaws h1 l Xo c
  exact ⟨⟨⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩⟩,
    CompFin.finite_comp Xo c, h, hg, fun Z => evalAt_one _ _ _ (hg Z),
    (GlobalTheory.Reg.kap_fg_trdeg E H Dw l Xo c).2⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NormalisedFramedPointArithmeticGroupInvariantSig
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NormalisedFramedPointArithmeticGroupInvariantSig
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.PjFree
open Formalism.L2.Pj hiding Unf GoodEmb toC relab rdU laU IsUnf ModelsOf
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.FrameUnif

theorem wchar_ex_sign {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dw : Datum H) {S : Type} [CommRing S] (t : Ix Dw → Sˣ) (h0 : (t none : S) ^ 2 = 1)
    (h1 : ∀ p, t (some p) = 1) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hn : Even n) : wchar (ex Dw a n) t = 1 := by
  obtain ⟨m, rfl⟩ := hn
  unfold wchar
  rw [Fintype.prod_option]
  simp only [h1, Units.val_one, one_pow, Finset.prod_const_one, mul_one]
  show (t none : S) ^ (m + m) = 1
  rw [← two_mul, pow_mul, h0, one_pow]

theorem normUn_gamma : Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ)) (k : Fin F.n) (T : ThetaData e F M k), GoodEmb c σ → ModelBase M → NegXi M → IsNormUn T (un k) → ∀ γ ∈ (M.X k).Γ, ∀ (x : (M.X k).dom) (h : lact γ x.1 ∈ (M.X k).dom), ∃ t : Ix Dw → (CAt σ)ˣ, FrBor t (un k x) (un k ⟨_, h⟩) ∧ ∀ a n, Dom a n → toC (wchar (ex Dw a n) t) = 1 := by
  intro hS E _ _ _ H Dw l Xo c σ g e F r M un k T hσ hM hN hun γ hγ x h
  obtain ⟨gam, hgam, hP⟩ := GlobalTheory.per_gam E H Dw l Xo c σ g e F r M hσ hM hN k T.Pf T.per γ hγ
  obtain ⟨κ, hκ, hy⟩ := hun x
  obtain ⟨κ', hκ', hy'⟩ := hun ⟨_, h⟩
  have hb : T.co.symm x.1 ∈ T.co ⁻¹' (M.X k).dom := by
    show T.co (T.co.symm x.1) ∈ (M.X k).dom
    rw [T.co.apply_symm_apply]; exact x.2
  have hb' : T.co.symm (lact γ x.1) ∈ T.co ⁻¹' (M.X k).dom := by
    show T.co (T.co.symm (lact γ x.1)) ∈ (M.X k).dom
    rw [T.co.apply_symm_apply]; exact h
  obtain ⟨hx, hd, t₀, hsec, ht⟩ := GlobalTheory.T.thetaPoints_change_levelIsometry_linearMap hS E H Dw l Xo c σ g e F r M k T _ hb _ hb' κ κ' (un k x)
    (un k ⟨_, h⟩) gam 1 hy hy' hgam (fun a => by
      rw [T.co.apply_symm_apply, T.co.apply_symm_apply, Matrix.one_mulVec]; exact hP x.1 x.2 a)
  have hu : ∀ τ i, (un k ⟨_, h⟩).u τ i = (un k x).u τ i := fun τ i => by
    have h1 := hd τ i
    rw [inv_one, Matrix.one_mulVec] at h1
    exact ((GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F k _ (T.isPer _ hb)).2.1 _).unique h1 (hy.2.1 τ i)
  have hC : (normConst (fun j => relab c σ (e j).1) (M.X k).ξ0 : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    refine (Real.sqrt_pos.2 (div_pos (by positivity) (Finset.prod_pos fun j _ => ?_))).ne'
    have : relab c σ (e j).1 (M.X k).ξ0 ≠ 0 := (map_ne_zero _).2 (M.X k).ξ0_ne
    positivity
  have ht2 : toC (t₀ : CAt σ) ^ 2 = 1 := by
    have d1 := (T.norm _ hb).1.ne_zero
    have d2 := (T.norm _ hb').1.ne_zero
    rw [hκ, hκ', Matrix.det_one, mul_one] at ht
    refine mul_right_cancel₀ (mul_ne_zero (mul_ne_zero hC d1) d2) ?_
    rw [ht]; ring
  refine ⟨fun i => i.elim t₀ fun _ => 1, ?_, fun a n hn => ?_⟩
  · refine (frBor_iff_frChg _ _ _).2 ⟨fun _ => 1, fun τ i j hij => Matrix.one_apply_ne hij.ne,
      fun τ i => Matrix.one_apply_eq i, hx, fun τ i => ?_, hsec⟩
    rw [hu]
    exact (GlobalTheory.T.frameChangeByMatrices_refl_and_comp E H Dw l Xo c (CAt σ) (un k x) (un k x) (un k x)).1.2.1 τ i
  · exact wchar_ex_sign Dw _ ht2 (fun _ => rfl) a n hn.2

end GlobalTheory.FrameUnif
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NormalisedFramedPointArithmeticGroupInvariantSigStatement
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.PjFree
open Formalism.L2.Pj hiding Unf GoodEmb toC relab rdU laU IsUnf ModelsOf
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalisedFramedPoint_arithmeticGroup_invariant_sign : Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ)) (k : Fin F.n) (T : ThetaData e F M k), GoodEmb c σ → ModelBase M → NegXi M → IsNormUn T (un k) → ∀ γ ∈ (M.X k).Γ, ∀ (x : (M.X k).dom) (h : lact γ x.1 ∈ (M.X k).dom), ∃ t : Ix Dw → (CAt σ)ˣ, FrBor t (un k x) (un k ⟨_, h⟩) ∧ ∀ a n, Dom a n → toC (wchar (ex Dw a n) t) = 1 := by
  first | exact @GlobalTheory.FrameUnif.normUn_gamma | exact GlobalTheory.FrameUnif.normUn_gamma | (intros; apply GlobalTheory.FrameUnif.normUn_gamma <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifferentiableOnReadingsNormalisedThetaPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifferentiableOnReadingsNormalisedThetaPoints
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.PjFree
open Formalism.L2.Pj hiding Unf GoodEmb toC relab rdU laU IsUnf ModelsOf
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

noncomputable section

namespace GlobalTheory.FrameUnif.NormUnHol

theorem differentiableOn_det {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {g : ℕ} {s : Set V}
    {h : V → Matrix (Fin g) (Fin g) ℂ} (hh : ∀ i j, DifferentiableOn ℂ (fun b => h b i j) s) :
    DifferentiableOn ℂ (fun b => (h b).det) s := by
  simp_rw [Matrix.det_apply']
  refine DifferentiableOn.fun_sum fun π _ => ?_
  have key : DifferentiableOn ℂ (∏ i, fun b => h b (π i) i) s :=
    Finset.prod_induction _ (fun f => DifferentiableOn ℂ f s) (fun _ _ ha hb => ha.mul hb)
      (differentiableOn_const (1 : ℂ)) (fun i _ => hh _ _)
  have e : (∏ i, fun b => h b (π i) i) = fun b => ∏ i, h b (π i) i := by
    funext b; simp [Finset.prod_apply]
  exact (differentiableOn_const _).mul (e ▸ key)

theorem normConst_ne_zero {E : Type} [Field E] {g : ℕ} (ty : Fin g → (E →+* ℂ)) {ξ : E} (hξ : ξ ≠ 0) :
    Real.sqrt (2 ^ g / ∏ j, (2 * ‖ty j ξ‖)) ≠ 0 := by
  have hpos : ∀ j, 0 < 2 * ‖ty j ξ‖ := fun j => by
    have : ty j ξ ≠ 0 := (map_ne_zero (ty j)).mpr hξ
    positivity
  exact (Real.sqrt_pos.mpr (div_pos (by positivity) (Finset.prod_pos fun j _ => hpos j))).ne'

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ}

theorem wchar_gen {S : Type} [CommRing S] (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (t₀ : Sˣ) :
    wchar (ex Dw a n) (fun i => Option.elim i t₀ (fun _ => 1)) = (t₀ : S) ^ n := by
  unfold wchar ex
  simp [Fintype.prod_option]

theorem differentiableOn_thetaPt (hbc : Out.SecBaseChangeSt) (htw : Out.SecTwistSt) {g : ℕ}
    {e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)}
    {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)}
    {r : ℕ} {M : ModelsOf F r} {k : Fin F.n} (T : ThetaData e F M k)
    (y : (Fin T.m → ℂ) → FrPt Xo c (CAt σ)) (hy : ∀ b ∈ T.co ⁻¹' (M.X k).dom, IsThetaPt T b 1 (y b))
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c) (hf : f ∈ sec Xo c a n) :
    DifferentiableOn ℂ (fun b => toC (evR Xo c f (y b))) (T.co ⁻¹' (M.X k).dom) := by
  intro b₀ hb₀
  obtain ⟨p, y₀, B, ψ, hBo, hb₀B, hBd, hψu, hψd⟩ :=
    GlobalTheory.T.exists_chart_holomorphic_coordinates_near_frame hbc E H Dw l Xo c σ g e F r M k T b₀ hb₀
  choose z hz using fun b =>
    GlobalTheory.Frames.FramedBaseChange.exists_frMap hbc E H Dw l Xo c p.R (CAt σ) (ψ b) y₀
  have hx : ∀ b ∈ B, (y b).x = (z b).x := by
    intro b hb
    rw [(hy b (hBd hb)).1, hψu b hb]
    exact ((hz b).1).symm
  have hch : ∀ b, ∃ (gch : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (CAt σ))
      (sch : CAt σ), b ∈ B → FrChg gch sch (z b) (y b) := by
    intro b
    by_cases hb : b ∈ B
    · obtain ⟨gch, u, -, hc⟩ :=
        (GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c (CAt σ) (z b) (y b)).1 (hx b hb)
      exact ⟨gch, u, fun _ => hc⟩
    · exact ⟨fun _ => 0, 0, fun h => absurd h hb⟩
  choose gch sch hgs using hch
  have hall : ∀ b ∈ B, FrMap (ψ b) y₀ (z b) ∧ FrChg (gch b) (sch b) (z b) (y b) ∧
      IsThetaPt T b 1 (y b) := fun b hb => ⟨hz b, hgs b hb, hy b (hBd hb)⟩
  have hG := GlobalTheory.T.differentiableOn_exponential_frame_matrix E H Dw l Xo c σ g e F r M k T p.R y₀ B ψ (fun _ => 1) z y gch sch
    hBo hBd hψd hall
  have hS := GlobalTheory.T.differentiableOn_theta_algebraic_generator_factor htw E H Dw l Xo c σ g e F r M k T p.R y₀ B ψ (fun _ => 1) z y gch sch
    hBo hBd hψd hall (differentiableOn_const 1)
  have hB := GlobalTheory.T.differentiableOn_natural_rule_holomorphic_frames hbc E H Dw l Xo c σ (Fin T.m → ℂ) B p y₀ ψ z y gch sch
    (fun b hb => ⟨hz b, hgs b hb⟩) hψd hG hS a n f hf
  exact (hB.differentiableAt (hBo.mem_nhds hb₀B)).differentiableWithinAt

theorem differentiableOn_rdU : Out.SecBaseChangeSt → Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ)) (k : Fin F.n) (T : ThetaData e F M k), IsNormUn T (un k) → ∀ a n, Dom a n → ∀ f ∈ sec Xo c a n, DifferentiableOn ℂ (rdU (unfOf e F M un) f k) (M.X k).dom := by
  intro hbc htw E _ _ _ H Dw l Xo c σ g e F r M un k T hT a n hD f hf
  obtain ⟨m, hm⟩ := hD.2
  rcases Set.eq_empty_or_nonempty (M.X k).dom with h0 | ⟨x₀, hx₀⟩
  · rw [h0]
    exact differentiableOn_empty
  have hx₀' : T.co.symm x₀ ∈ T.co ⁻¹' (M.X k).dom := by simpa using hx₀
  obtain ⟨y₀, -⟩ := GlobalTheory.T.exists_isThetaPt' htw E H Dw l Xo c σ g e F r M k T _ hx₀' 1 one_ne_zero
  have hy1 : ∀ b, ∃ y : FrPt Xo c (CAt σ), b ∈ T.co ⁻¹' (M.X k).dom → IsThetaPt T b 1 y := by
    intro b
    by_cases hb : b ∈ T.co ⁻¹' (M.X k).dom
    · obtain ⟨y, hy⟩ := GlobalTheory.T.exists_isThetaPt' htw E H Dw l Xo c σ g e F r M k T b hb 1 one_ne_zero
      exact ⟨y, fun _ => hy⟩
    · exact ⟨y₀, fun h => absurd h hb⟩
  choose y hy using hy1
  have hth := differentiableOn_thetaPt hbc htw T y hy a n f hf
  have key : ∀ x (hx : x ∈ (M.X k).dom),
      toC (evR Xo c f (un k ⟨x, hx⟩)) =
        ((normConst (fun j => relab c σ (e j).1) (M.X k).ξ0 : ℂ) * (T.h (T.co.symm x)).det) ^ m *
          toC (evR Xo c f (y (T.co.symm x))) := by
    intro x hx
    have hb : T.co.symm x ∈ T.co ⁻¹' (M.X k).dom := by simpa using hx
    obtain ⟨κ, hκ2, hθ⟩ := hT ⟨x, hx⟩
    have hN : (normConst (fun j => relab c σ (e j).1) (M.X k).ξ0 : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (normConst_ne_zero _ (M.X k).ξ0_ne)
    have hdet : (T.h (T.co.symm x)).det ≠ 0 := (T.norm _ hb).1.ne_zero
    have hκ : κ ≠ 0 := by
      intro h0
      apply mul_ne_zero hN hdet
      rw [← hκ2, h0]
      ring
    let t₀ : (CAt σ)ˣ := ⟨(κ : ℂ), (κ⁻¹ : ℂ), mul_inv_cancel₀ hκ, inv_mul_cancel₀ hκ⟩
    have hθ' : IsThetaPt T (T.co.symm x) (toC (t₀ : CAt σ) * 1) (un k ⟨x, hx⟩) := by
      have h1 : toC (t₀ : CAt σ) * 1 = κ := by
        show κ * 1 = κ
        ring
      rw [h1]
      exact hθ
    have hbor := GlobalTheory.T.thetaPoints_frame_ratio htw E H Dw l Xo c σ g e F r M k T (T.co.symm x) hb 1 t₀ _ _
      (hy _ hb) hθ'
    have hred : IsReduced (CAt σ) := by
      show IsReduced ℂ
      infer_instance
    have hev := (GlobalTheory.T.framedModuli_algebraicLaws_chart_weight_integrality hbc E H Dw l Xo c).2.2.2.2.2.2 (CAt σ) hred a n f hf _ _ _ hbor
    rw [hev, wchar_gen]
    have e1 : toC ((t₀ : CAt σ) ^ n * evR Xo c f (y (T.co.symm x))) =
        κ ^ n * toC (evR Xo c f (y (T.co.symm x))) := rfl
    rw [e1, hm, ← two_mul, pow_mul, hκ2]
  have hΦ : DifferentiableOn ℂ (fun b => ((normConst (fun j => relab c σ (e j).1) (M.X k).ξ0 : ℂ) *
      (T.h b).det) ^ m * toC (evR Xo c f (y b))) (T.co ⁻¹' (M.X k).dom) :=
    (((differentiableOn_const _).mul (differentiableOn_det fun i j => (T.hol i j).1)).pow m).mul hth
  have hcomp := hΦ.comp T.co.symm.differentiableOn (fun x hx => by simpa using hx)
  refine hcomp.congr fun x hx => ?_
  unfold rdU unfOf
  simp only [LinearMap.coe_mk, AddHom.coe_mk, dif_pos hx]
  exact key x hx

end GlobalTheory.FrameUnif.NormUnHol
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifferentiableOnReadingsNormalisedThetaPointsStatement
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.PjFree
open Formalism.L2.Pj hiding Unf GoodEmb toC relab rdU laU IsUnf ModelsOf
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.differentiableOn_readings_normalised_theta_points : Out.SecBaseChangeSt → Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ)) (k : Fin F.n) (T : ThetaData e F M k), IsNormUn T (un k) → ∀ a n, Dom a n → ∀ f ∈ sec Xo c a n, DifferentiableOn ℂ (rdU (unfOf e F M un) f k) (M.X k).dom := by
  first | exact @GlobalTheory.FrameUnif.NormUnHol.differentiableOn_rdU | exact GlobalTheory.FrameUnif.NormUnHol.differentiableOn_rdU | (intros; apply GlobalTheory.FrameUnif.NormUnHol.differentiableOn_rdU <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsComponentLatticeMarkingAdelic
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsComponentLatticeMarkingAdelic
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member.Occ

open GlobalTheory.AdLat GlobalTheory.AdLat.Half
open scoped nonZeroDivisors

theorem form_congr {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E)
    (J : FractionalIdeal (𝓞 E)⁰ E) (g : Matrix (Fin n) (Fin n) (RA F E))
    (hL : ∀ x ∈ L, ∀ y ∈ L, (∑ a, ∑ b, x a * G a b * c (y b)) ∈ J)
    (hg : ∀ x y, hermA c G (g *ᵥ x) (g *ᵥ y) = hermA c G x y) {N : ℕ} (hN : 0 < N)
    {x y x' y' : Fin n → E} (hx : x ∈ L) (hy : y ∈ L) {w w' : Fin n → RA F E}
    (hw : w ∈ hat F (L : Set (Fin n → E))) (hw' : w' ∈ hat F (L : Set (Fin n → E)))
    (ex : fv F x' = g *ᵥ (fv F x + N • w)) (ey : fv F y' = g *ᵥ (fv F y + N • w')) :
    ∃ z ∈ J, (∑ a, ∑ b, x' a * G a b * c (y' b)) - (∑ a, ∑ b, x a * G a b * c (y b)) = N * z := by
  have back : ∀ w ∈ hat F (L : Set (Fin n → E)), ∀ y ∈ L,
      hermA c G w (fv F y) ∈ hat1 F (J : Set E) := by
    intro w hw y hy
    induction hw using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨t, ht, x, hx, rfl⟩ := hw
      rw [hermA_tmul_fv]
      exact AddSubgroup.subset_closure ⟨t, ht, _, hL x hx y hy, rfl⟩
    | zero =>
      have : hermA c G 0 (fv F y) = 0 := by simp [hermA]
      rw [this]; exact zero_mem _
    | add w w' _ _ h h' => rw [hermA_add_left]; exact add_mem h h'
    | neg w _ h => rw [hermA_neg_left]; exact neg_mem h
  have both : ∀ u ∈ hat F (L : Set (Fin n → E)), ∀ v ∈ hat F (L : Set (Fin n → E)),
      hermA c G u v ∈ hat1 F (J : Set E) := fun u hu v hv => herm_mem_of_fv c G _ _ _ (back u hu) v hv
  have hMs : ∀ x : Fin n → RA F E, N • x = (N : RA F E) • x := fun x =>
    (Nat.cast_smul_eq_nsmul _ _ _).symm
  have hsM : sg (FiniteAdeleRing (𝓞 F) F) c (N : RA F E) = N := map_natCast _ N
  have hfx := fv_mem_hat' (F := F) (L : Set (Fin n → E)) x hx
  have hfy := fv_mem_hat' (F := F) (L : Set (Fin n → E)) y hy
  have hu : hermA c G w (fv F y + N • w') + hermA c G (fv F x) w' ∈ hat1 F (J : Set E) :=
    add_mem (both _ hw _ (add_mem hfy (nsmul_mem hw' N))) (both _ hfx _ hw')
  have e1 : hermA c G (fv F x') (fv F y') - hermA c G (fv F x) (fv F y) =
      (N : RA F E) * (hermA c G w (fv F y + N • w') + hermA c G (fv F x) w') := by
    rw [ex, ey, hg, Half.herm_add_left, hMs w, Half.herm_smul_left, Half.herm_add_right c G (fv F x), hMs w',
      Half.herm_smul_right, hsM]
    ring
  have e2 : ∀ x y : Fin n → E, hermA c G (fv F x) (fv F y) =
      (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (∑ a, ∑ b, x a * G a b * c (y b)) :=
    fun x y => hermA_tmul_fv c G 1 x y
  rw [e2, e2, ← TensorProduct.tmul_sub] at e1
  set d := (∑ a, ∑ b, x' a * G a b * c (y' b)) - (∑ a, ∑ b, x a * G a b * c (y b)) with hd
  have hN' : (N : E) ≠ 0 := by exact_mod_cast hN.ne'
  have hNt : (N : RA F E) = (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (N : E) :=
    (map_natCast (Algebra.TensorProduct.includeRight :
      E →ₐ[F] FiniteAdeleRing (𝓞 F) F ⊗[F] E) N).symm
  refine ⟨(N : E)⁻¹ * d, ((adelicCompletion_fractionalIdeal_properties F E).2.1 J _).1 ?_, by rw [← mul_assoc, mul_inv_cancel₀ hN', one_mul]⟩
  have e3 : ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] ((N : E)⁻¹ * d) : RA F E) =
      ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (N : E)⁻¹) * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] d) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [e3, e1, hNt, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul, inv_mul_cancel₀ hN',
    ← Algebra.TensorProduct.one_def, one_mul]
  exact hu

theorem herm_neg' {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (G : Matrix (Fin n) (Fin n) E)
    (x y : Fin n → E) : herm (-G) x y = -∑ a, ∑ b, x a * G a b * cc (y b) := by
  simp [herm]

theorem trace_swap {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (G : Matrix (Fin n) (Fin n) E)
    (hG : ∀ a b, cc (G a b) = G b a) (ξ : E) (hξ : cc ξ = -ξ) (x y : Fin n → E) :
    Algebra.trace ℚ E (ξ * -herm G y x) = Algebra.trace ℚ E (ξ * herm G x y) := by
  have h1 : cc (herm G x y) = herm G y x := by
    unfold herm
    unfold cc at *
    rw [Finset.sum_comm]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, hG, IsCMField.complexConj_apply_apply]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have h2 := Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) (ξ * herm G x y)
  rw [← h2, ← h1]
  congr 1
  unfold cc at *
  change _ = IsCMField.complexConj E _
  rw [map_mul, hξ]
  ring

theorem mark_congr {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) (RA F E)) {N : ℕ} {x x' t w : Fin n → E} {w' : Fin n → RA F E}
    (e : A *ᵥ fv F x' = fv F (t + N • w)) (e' : fv F x' = B *ᵥ (fv F x + N • w')) :
    fv F t - (A * B) *ᵥ fv F x = N • ((A * B) *ᵥ w' - fv F w) := by
  rw [e', Matrix.mulVec_mulVec, Tower.fv_add, Tower.fv_nsmul, Matrix.mulVec_add, Tower.mulVec_nsmul] at e
  rw [smul_sub, sub_eq_sub_iff_add_eq_add, ← e, add_comm]

end GlobalTheory.Member.Occ


open GlobalTheory.Member.Occ GlobalTheory.AdLat in
theorem GlobalTheory.Member.exists_mark : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∀ h : GA D V, ∃ k γ, C.Mark h k γ := by
  intro D H Dw l Xo c σ V r C hC h
  obtain ⟨hr, g, e, F, M, ι, θ, x₀⟩ := C
  subst hr
  obtain ⟨⟨-, -, ⟨hinj, hrange⟩, hisom⟩, -, hA, hgood, hbase, hW, -, -⟩ := hC
  dsimp only at hinj hrange hisom hbase hW
  obtain ⟨-, hfv, -, -, -, hcc, -, hGc, hGdet, hT, -⟩ := GlobalTheory.T.completedLattice_eq_adelicCompletion_and_gram D V
  obtain ⟨hfg1, hsp1, -⟩ := GlobalTheory.T.adelicElementLattice_full_and_completion D V 1
  obtain ⟨hfg, hsp, hlat, -⟩ := GlobalTheory.T.adelicElementLattice_full_and_completion D V h
  obtain ⟨hJ, hsd1, -⟩ := GlobalTheory.T.adelicUnitaryLattice_selfDual_traceForm D V 1 _ rfl
  obtain ⟨-, -, hsd⟩ := GlobalTheory.T.adelicUnitaryLattice_selfDual_traceForm D V h _ rfl
  obtain ⟨f, hf1, hf2, hf3⟩ := GlobalTheory.AdLat.exists_linear_approx_tower D.host.F D.host.E V.rank (latG V 1)
    (finHom V h) (latG V h) hfg1 hsp1 hlat
  let ε : Dw.La ≃ₗ[𝓞 D.host.E] latG V 1 :=
    (LinearEquiv.ofInjective ι hinj).trans (LinearEquiv.ofEq _ _ hrange)
  have hε : ∀ a, (ε a : Fin V.rank → D.host.E) = ι a := fun a => rfl
  have hk : ∀ k, (M.X k).Gm = -V.gramᵀ ∧ (M.X k).ξ0 = -D.host.xi0 := fun k => by
    obtain ⟨h1, h2⟩ := hW k
    exact ⟨by rw [h1]; rfl, h2⟩
  have hξ : cc D.host.xi0 = -D.host.xi0 := by
    have h := (M.X ⟨0, F.n_pos⟩).ξ0_im
    rw [(hk _).2] at h
    unfold cc at h ⊢
    rw [map_neg] at h
    exact neg_injective h
  have hG' : ∀ a b, cc ((-V.gramᵀ) a b) = (-V.gramᵀ) b a := fun a b => by
    rw [← hcc, Matrix.neg_apply, Matrix.neg_apply, map_neg, hGc]
  have hEF : ∀ x y, ((Dw.EF x y : ℤ) : ℚ) =
      Algebra.trace ℚ D.host.E (-(-D.host.xi0) * herm (-V.gramᵀ) (ι x) (ι y)) := fun x y => by
    rw [hisom, hT, trace_swap _ hG' _ hξ, neg_neg]
  obtain ⟨k, γ', hu, hl, hm⟩ := GlobalTheory.selfDual_lattice_occurs GlobalTheory.QNorm.hasseNormSt D.host.E H Dw l Xo _ g _ F V.rank M
    (-D.host.xi0) (-V.gramᵀ) ι (latG V h) (fun N => f N ∘ₗ ε.toLinearMap) hA hgood
    ((GlobalTheory.Relab.relab_good D.host.E H l c σ hgood).2.2.2 Dw g e) hbase hk
    ⟨hinj, by rw [← LinearMap.coe_range, hrange]; exact hsp1, hG', by
      rw [Matrix.det_neg]; exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hGdet, hEF⟩ hfg hsp hsd
    (fun n m hn hm a => hf2 n m hn hm (ε a))
    (fun n hn => ⟨fun a => ((hf3 n hn).1 (ε a)).trans
      ⟨fun ⟨v, hv⟩ => ⟨ε.symm v, ε.injective (by rw [hv, map_nsmul, ε.apply_symm_apply])⟩,
        fun ⟨v, hv⟩ => ⟨ε v, by rw [hv, map_nsmul]⟩⟩, fun a' => by
      obtain ⟨a, v, hv⟩ := (hf3 n hn).2 a'
      exact ⟨ε.symm a, v, by simpa using hv⟩⟩)
    (fun n hn a a' => by
      obtain ⟨w, hw, ew⟩ := hf1 n hn (ε a)
      obtain ⟨w', hw', ew'⟩ := hf1 n hn (ε a')
      obtain ⟨z, hz, ez⟩ := form_congr (latG V 1) (cF D) V.gramᵀ _ _
        (fun x hx => (hsd1 x).2 hx) (GlobalTheory.T.finitePart_preserves_form_det_norm_one D V h).1 hn (ε a).2 (ε a').2 hw hw' ew ew'
      obtain ⟨t, ht⟩ := (hJ z).1 hz 1
      refine ⟨-t, ?_⟩
      simp only [hcc, hε] at ez
      rw [hEF, ← map_sub, ← mul_sub, herm_neg', herm_neg', neg_sub_neg, ← neg_sub]
      erw [ez]
      have : -(-D.host.xi0) * -((n : D.host.E) * z) =
          (-(n : ℚ)) • (D.host.xi0 * (((1 : 𝓞 D.host.E) : D.host.E) * z)) := by
        simp [Algebra.smul_def]; ring
      rw [this, map_smul, ht]
      simp)
  obtain ⟨hQ, -, hex, -, hfin⟩ := GlobalTheory.T.rational_points_adelicUnitary_eq_unitary D V
  obtain ⟨γ, hγ⟩ := hex γ' hu
  obtain ⟨hmv, -⟩ := (GlobalTheory.T.adelicUnitaryLattice_rationalTranslate_invariance D V).1 γ γ' h hγ
  obtain ⟨-, -, -, hhat1, hhat2, -⟩ := GlobalTheory.T.adelicElementLattice_full_and_completion D V (γ * h)
  have hΛ : ∀ v, v ∈ (M.X k).Λ ↔ v ∈ latG V (γ * h) := fun v => by
    have e : v = γ'.val *ᵥ ((γ'⁻¹).val *ᵥ v) := by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    rw [e, ← hl, ← hmv]
  refine ⟨k, γ, (hQ γ).2 ⟨γ', hγ⟩, ?_, fun a ha => ?_⟩
  · ext v
    constructor
    · intro hv
      exact ⟨v, (hΛ v).1 hv, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact (hΛ v).2 hv
  · obtain ⟨w, hw, ew⟩ := hm a ha
    obtain ⟨w', hw', ew'⟩ := hf1 l.M (lt_of_lt_of_le (by norm_num) l.three_le) (ε a)
    have m1 : (finHom V (γ * h)).1 *ᵥ w' ∈ latGHat V (γ * h) := by
      rw [← SetLike.mem_coe, hhat1]
      exact ⟨w', hw', rfl⟩
    have m2 : fv D.host.F w ∈ latGHat V (γ * h) := by
      rw [hhat2]
      exact Half.fv_mem_hat' _ _ ((hΛ w).1 hw)
    refine ⟨_, sub_mem m1 m2, ?_⟩
    have e1 := (hfin γ γ' hγ).1 (f l.M (ε a))
    have ew2 : γ'.val *ᵥ (f l.M (ε a) : Fin V.rank → D.host.E) =
        (M.φ k (F.t k a) : Fin V.rank → D.host.E) + l.M • w := ew
    rw [ew2] at e1
    have e2 := mark_congr (finHom V γ).1 (finHom V h).1 e1 ew'
    rw [← Units.val_mul, ← map_mul] at e2
    exact e2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsComponentLatticeMarkingAdelicStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_component_lattice_marking_adelic : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∀ h : GA D V, ∃ k γ, C.Mark h k γ := by
  first | exact @GlobalTheory.Member.exists_mark | exact GlobalTheory.Member.exists_mark | (intros; apply GlobalTheory.Member.exists_mark <;> assumption)
end
end
