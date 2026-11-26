module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.Definitions.Foundations.ThetaExponentIdentities
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassesAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearModelCompactEquivariance
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatCompAffineMatrix
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsCoordAtPoints

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LengthUnitSizeBounds
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

namespace GlobalTheory.RefSum.SizeTZ

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem nCol_le (Dw : Datum H) :
    nCol Dw ≤ (2 * (Dw.p + Dw.q) + 8) * (Module.finrank ℚ E * (Dw.p + Dw.q)) + 8 := by
  have h1 : ∑ f : Lt1 Dw, 2 * GlobalTheory.FactorDepth.rk f ≤ Fintype.card (Lt1 Dw) * (2 * (Dw.p + Dw.q)) := by
    rw [← Finset.card_univ, ← smul_eq_mul]
    refine Finset.sum_le_card_nsmul _ _ _ fun f _ => ?_
    have h := GlobalTheory.FactorDepth.rk_le f
    have h' : Dw.mult f.1 ≤ Dw.p + Dw.q := by
      rw [Datum.mult]; split_ifs <;> omega
    omega
  have h2 : Fintype.card (Lt1 Dw) ≤ Module.finrank ℚ E * (Dw.p + Dw.q) := card_Lt1_le_finrank_mul
  have h3 := Nat.mul_le_mul_right (2 * (Dw.p + Dw.q)) h2
  have h4 := Nat.mul_div_le (∑ f : Lt1 Dw, 2 * GlobalTheory.FactorDepth.rk f) 8
  unfold nCol
  nlinarith

end Free

variable {D : D7}

theorem two_le_f (D : D7) : 2 ≤ D.R.f := by
  have : 0 < D.R.ord := D.R.ord_pos
  show 2 ≤ 2 * D.R.ord
  omega

theorem six_le_r (D : D7) : 6 ≤ D.R.r := by
  have h1 := D.R.two_le_m
  have h2 := D.R.m_add_three_le_k
  unfold Ranks.r; omega

theorem one_le_scL (L : SizeData₂ D) : 1 ≤ L.sc.L :=
  Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le

theorem one_le_zBase (L : SizeData₂ D) : 1 ≤ zBase L := by
  have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast (by have := two_le_f D; omega : 1 ≤ D.R.f)
  have hr : (1 : ℝ) ≤ D.R.r := by exact_mod_cast (by have := six_le_r D; omega : 1 ≤ D.R.r)
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hf hr) (one_le_scL L)

variable {L : SizeData₂ D} {P : ParameterChoice' D L}

theorem pow_le_PP (T : ParamsT D L P) : zBase L ^ 12 ≤ T.PP := by
  have hZ := one_le_zBase L
  have h1 : zBase L ^ 12 ≤ zBase L ^ T.eP := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hZ (by exact_mod_cast T.eP_ge)
  rw [T.PP_eq]
  exact h1.trans (le_mul_of_one_le_left (by positivity) T.one_le_CP)

theorem ceil_le_TO (T : ParamsT D L P) :
    ⌈T.PP ^ 2 * (T.Dp : ℝ) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ)⌉₊ ≤ T.TO := by
  refine Nat.ceil_le.2 (le_trans ?_ T.TO_ge)
  have hPP : 1 ≤ T.PP := (one_le_pow₀ (one_le_zBase L)).trans (pow_le_PP T)
  have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast (by have := two_le_f D; omega : 1 ≤ D.R.f)
  have hD : (1 : ℝ) ≤ T.Dp := by
    have h1 : 0 < D.R.r.choose 2 := Nat.choose_pos (by have := six_le_r D; omega)
    have h2 : 0 < T.Dp := by rw [T.Dp_eq]; exact Nat.mul_pos (by have := two_le_f D; omega) h1
    exact_mod_cast h2
  have hx : 1 ≤ L.sc.x ^ T.Cp := Real.one_le_rpow L.sc.one_lt_alt.le T.Cp_nonneg
  have hm : (0 : ℝ) < D.R.m := by exact_mod_cast (by have := D.R.two_le_m; omega : 0 < D.R.m)
  have hd := L.thickDensity_pos
  refine div_le_div₀ (by positivity) ?_ (by positivity) (mul_le_of_le_one_right hm.le L.thickDensity_le_one)
  have e : T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k * D.R.f * L.sc.x ^ T.Cp =
      T.PP ^ 2 * (T.Dp : ℝ) ^ 2 * (D.R.k : ℝ) * (T.PP ^ 2 * T.Dp * D.R.f * L.sc.x ^ T.Cp) := by ring
  rw [e]
  exact le_mul_of_one_le_right (by positivity) (one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hPP) hD) hf) hx)

theorem ceil_mul_le_b (T : ParamsT D L P) :
    (⌈T.PP ^ 2 * (T.Dp : ℝ) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ)⌉₊ : ℝ) * zBase L ^ 12 ≤ L.sc.b := by
  have hb : 1 ≤ L.sc.b := Real.one_le_exp (zero_le_one.trans (one_le_scL L))
  have hZ := one_le_zBase L
  have h1 : (⌈T.PP ^ 2 * (T.Dp : ℝ) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ)⌉₊ : ℝ) ≤ T.TO := by exact_mod_cast ceil_le_TO T
  refine (mul_le_mul h1 (pow_le_PP T) (by positivity) (by positivity)).trans (T.TO_PP'.trans ?_)
  exact (Real.rpow_le_rpow_of_exponent_le hb (by norm_num : (1 / 2 : ℝ) ≤ 1)).trans (Real.rpow_one _).le

theorem lrd_le (P : ParameterChoice' D L) : lrd D.host.E ≤ 3 * L.sc.L := by
  have h := log_rdE_le_scL P
  have e : lrd D.host.E = Real.log D.host.rdE := by
    rw [lrd, rootDiscr_def, Formalism.BasicNotions.Host.rdE, one_div, Int.cast_abs]
  have := one_le_scL L
  rw [e]; linarith

theorem nCol_le_of_pins {T : Par D} (h : T.Pins) {j : ℕ} (hj : InR D j) :
    (nCol (T.Dw j) : ℝ) ≤ 20 * D.R.f * (D.R.r : ℝ) ^ 2 := by
  have hfr : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    rw [D.host.finrank_cmField]
    unfold Ranks.f Ranks.n
    ring
  have h1 := nCol_le (T.Dw j)
  rw [hfr, (GlobalTheory.SlopeRec.sig_eq h hj).2.2] at h1
  have hf := two_le_f D
  have hr := six_le_r D
  have h2 : nCol (T.Dw j) ≤ 20 * D.R.f * D.R.r ^ 2 := by
    refine h1.trans ?_
    generalize D.R.f = f at *
    generalize D.R.r = r at *
    have a1 : f * r * 6 ≤ f * r * r := Nat.mul_le_mul_left _ hr
    have a2 : 2 * 6 ≤ f * r := Nat.mul_le_mul hf hr
    nlinarith
  exact_mod_cast h2

theorem lenT_mul_le_b {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
    (T : ParamsT D L P) :
    (lenT p i T.PP : ℝ) * zBase L ^ 12 ≤ L.sc.b ∧ (nCol (dat p i) : ℝ) ≤ 20 * D.R.f * (D.R.r : ℝ) ^ 2 := by
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hpin : p.T.Q.Pins := p.fw.laws.pins
  have hD : GlobalTheory.CompHt.dimFlag (dat p i) = T.Dp := by
    rw [T.Dp_eq]
    refine (GlobalTheory.SlopeRec.dimFlag_eq hpin hj).trans ?_
    simp only [placeRankTwoOne.dimY, Nat.choose_two_right]
  refine ⟨?_, nCol_le_of_pins hpin hj⟩
  rw [lenT, hD]
  exact ceil_mul_le_b T

end GlobalTheory.RefSum.SizeTZ

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormRatiosGenerateAtFlagSpaceGenericPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormRatiosGenerateAtFlagSpaceGenericPoint
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Vanishing.H0

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HSApp

theorem stalkClosedPointTo_ger {V : Type} [CommRing V] [IsLocalRing V] {Y : Scheme.{0}} (x : Sp V ⟶ Y) (W : Y.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ W) (g : Γ(Y, W)) (hy : x (IsLocalRing.closedPoint V) ∈ W) :
    (Scheme.stalkClosedPointTo (R := CommRingCat.of V) x).hom (ger _ hy g) = GlobalTheory.TangentOrigin.evalPt x W h g := by
  have key := Scheme.germ_stalkClosedPointTo (R := CommRingCat.of V) x W hy
  have := congrArg (fun φ => φ.hom g) key
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  refine this.trans ?_
  simp only [GlobalTheory.TangentOrigin.evalPt, Scheme.Hom.appLE, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom,
    CommRingCat.hom_comp, RingHom.comp_apply, Category.assoc]
  congr!

theorem val_eq_lift_residue {k K : Type} [CommRing k] [Field K] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {B : LB Y} {O : Y.Opens}
    (x : Sp K ⟶ Y) (i : B.ι) (hO : ⊤ ≤ x ⁻¹ᵁ O) (hi : ⊤ ≤ x ⁻¹ᵁ B.U i) (hy : ptOf x ∈ O) (hj : ptOf x ∈ B.U i)
    (f : H0 p B O) :
    haveI : IsLocalHom (Scheme.stalkClosedPointTo (R := CommRingCat.of K) x).hom :=
      Scheme.isLocalHom_stalkClosedPointTo' (R := K) x
    H0.val x i hO hi f = IsLocalRing.ResidueField.lift (Scheme.stalkClosedPointTo (R := CommRingCat.of K) x).hom
      ((Y.residue (ptOf x)).hom (germ i (ptOf x) hy hj f)) := by
  haveI : IsLocalHom (Scheme.stalkClosedPointTo (R := CommRingCat.of K) x).hom :=
    Scheme.isLocalHom_stalkClosedPointTo' (R := K) x
  rw [H0.val_apply, H0.germ_apply]
  exact (stalkClosedPointTo_ger x _ _ _ (memInf hy hj)).symm.trans
    (IsLocalRing.ResidueField.lift_residue_apply _ _).symm

open GlobalTheory.CompHt (genVal)
open GlobalTheory.AllWt (exOf secZ)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem ratGen_of_birOn : ∀ {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c) {r : ℕ}
    (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (la : AllWt.Weight Dw),
    Nonempty (Modif (str₀ X Z) (U₀ X Z) (dimFlag Dw)) → GlobalTheory.DegVal.BirOn U Z (wtOf Dw la 0) → RatGen X Z U la := by
  intro Y X Z r U la ⟨M⟩ hB
  have h : GenFrEx Xo c := (Reg.genFrEx_and_genFromTest E H Dw l Xo c).1
  obtain ⟨z, hz, hO⟩ := exists_lift_genFr M h
  have hgen := isGenericPoint_of_lift M h hz hO
  have hU : ⊤ ≤ (z ≫ M.σ) ⁻¹ᵁ U₀ X Z := by
    intro s _
    have := hO (Set.mem_univ s)
    rw [M.off_eq] at this
    exact this
  have hη : ptOf (z ≫ M.σ) ∈ U₀ X Z := (le_iff_ptOf_mem _ _).1 hU
  have hdense : closure (M.σ '' Set.univ) = Set.univ := by
    refine Set.eq_univ_of_univ_subset ?_
    rw [← (dense_U₀ X Z).closure_eq]
    refine closure_mono fun u hu => ?_
    have hu' : ⊤ ≤ resPt u ⁻¹ᵁ U₀ X Z := (le_iff_ptOf_mem _ _).2 ((ptOf_resPt u).symm ▸ hu)
    obtain ⟨w, hw, -⟩ := M.existsUnique_lift (resPt u) hu'
    refine ⟨ptOf w, trivial, ?_⟩
    rw [← ptOf_comp, hw, ptOf_resPt]
  have hgen' : IsGenericPoint (ptOf (z ≫ M.σ)) Set.univ := by
    have := hgen.image M.σ.continuous
    rwa [hdense] at this
  refine ⟨ptOf (z ≫ M.σ), hη, hgen', ?_⟩
  haveI : IsLocalHom (Scheme.stalkClosedPointTo (R := CommRingCat.of (Om Z)) (z ≫ M.σ)).hom :=
    Scheme.isLocalHom_stalkClosedPointTo' (R := Om Z) (z ≫ M.σ)
  set ψ := IsLocalRing.ResidueField.lift (Scheme.stalkClosedPointTo (R := CommRingCat.of (Om Z)) (z ≫ M.σ)).hom
    with hψ
  have e₁ : (z ≫ M.σ) ≫ inc₀ X Z = X.pt (genFr h Z) ≫ X.inc := by
    rw [Category.assoc, X.pt_inc]; exact hz
  have hO₂ : ⊤ ≤ ((z ≫ M.σ) ≫ inc₀ X Z) ⁻¹ᵁ flagOpen X := hU
  have key : ∀ (i : (L₀ X Z la).ι) (hi : ptOf (z ≫ M.σ) ∈ (L₀ X Z la).U i), ∃ T : Om Z, T ≠ 0 ∧
      ∀ g : Cusp Z U la, ψ (((Y₀ X Z).residue (ptOf (z ≫ M.σ))).hom
        (germ i (ptOf (z ≫ M.σ)) hη hi (cuspSec X Z U la g))) = T * genVal Z g.1 := by
    intro i hi
    have hi' : ⊤ ≤ (z ≫ M.σ) ⁻¹ᵁ (L₀ X Z la).U i := (le_iff_ptOf_mem _ _).2 hi
    have hk₂ : ⊤ ≤ ((z ≫ M.σ) ≫ inc₀ X Z) ⁻¹ᵁ X.F.U (i PUnit.unit) := (le_iff_ptOf_mem _ _).2 (mem_pull.1 hi)
    have hk₁ : ⊤ ≤ (X.pt (genFr h Z) ≫ X.inc) ⁻¹ᵁ X.F.U (i PUnit.unit) := e₁ ▸ hk₂
    obtain ⟨Q, t, hQ, ht⟩ := X.exists_chartFr_frBor (genFr h Z) (i PUnit.unit) hk₁
    have hQ₂ : X.F.ChartFr (i PUnit.unit) ((z ≫ M.σ) ≫ inc₀ X Z) hk₂ Q := chartFr_congr e₁.symm hQ
    refine ⟨((∏ ix, t ix ^ exOf Dw la 0 ix : (Om Z)ˣ) : Om Z)⁻¹, inv_ne_zero (Units.ne_zero _), fun g => ?_⟩
    have v₈ := evR_eq_val_secOf ⟨g.1, cusp_le_secZ Z U la g.2⟩ hO₂ hQ₂ ht
    have v₅ : H0.val (z ≫ M.σ) i hU hi' (cuspSec X Z U la g) = H0.val (B := X.LL (exOf Dw la 0))
        ((z ≫ M.σ) ≫ inc₀ X Z) (i PUnit.unit) hO₂ hk₂ (secOf X _ ⟨g.1, cusp_le_secZ Z U la g.2⟩) :=
      H0.val_pull (inc₀ X Z) le_rfl (z ≫ M.σ) i hU hi' hO₂ hk₂ _
    have v₆ : genVal Z g.1 = evR Xo c g.1 (genFr h Z) := rfl
    rw [← val_eq_lift_residue (z ≫ M.σ) i hU hi' hη hi, v₅, v₆, v₈, inv_mul_cancel_left₀ (Units.ne_zero _)]
  have hmap : ∀ v w : Cusp Z U la, ∃ q ∈ ratField (Set.range (cuspSec X Z U la)) (ptOf (z ≫ M.σ)) hη,
      ψ q = genVal Z v.1 / genVal Z w.1 := by
    intro v w
    obtain ⟨i, hi⟩ := exists_chart (isLB_L₀ X Z la) (ptOf (z ≫ M.σ))
    obtain ⟨T, hT, hv⟩ := key i hi
    refine ⟨_, Subfield.subset_closure ⟨i, hi, _, _, ⟨v, rfl⟩, ⟨w, rfl⟩, rfl⟩, ?_⟩
    refine (map_div₀ ψ _ _).trans ?_
    rw [hv, hv, mul_div_mul_left _ _ hT]
  obtain ⟨v₀, hv₀⟩ : ∃ v₀ : Cusp Z U la, genVal Z v₀.1 ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hB.1 (LinearMap.ext fun v => hc v)
  have hsub : (⊤ : IntermediateField c.F (Om Z)).toSubfield ≤
      (ratField (Set.range (cuspSec X Z U la)) (ptOf (z ≫ M.σ)) hη).map ψ := by
    rw [← hB.2, GlobalTheory.DegVal.ratioField, IntermediateField.adjoin_toSubfield]
    refine Subfield.closure_le.2 (Set.union_subset ?_ ?_)
    · rintro _ ⟨a, rfl⟩
      obtain ⟨q, hq, e⟩ := hmap ⟨a • v₀.1, Submodule.smul_mem _ a v₀.2⟩ v₀
      refine ⟨q, hq, e.trans ?_⟩
      show genVal Z (a • v₀.1) / genVal Z v₀.1 = _
      rw [map_smul, Algebra.smul_def, mul_div_cancel_right₀ _ hv₀]
    · rintro _ ⟨v, w, rfl⟩
      exact hmap v w
  refine eq_top_iff.2 fun q _ => ?_
  obtain ⟨q', hq', e⟩ := hsub (show ψ q ∈ (⊤ : IntermediateField c.F (Om Z)).toSubfield from trivial)
  exact (ψ.injective e) ▸ hq'

end GlobalTheory.HSApp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormRatiosGenerateAtFlagSpaceGenericPointStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Vanishing.H0
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_ratios_generate_at_flagSpace_genericPoint : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (la : AllWt.Weight Dw), Nonempty (Modif (str₀ X Z) (U₀ X Z) (dimFlag Dw)) → GlobalTheory.DegVal.BirOn U Z (wtOf Dw la 0) → RatGen X Z U la := by
  first | exact @GlobalTheory.HSApp.ratGen_of_birOn | exact GlobalTheory.HSApp.ratGen_of_birOn | (intros; apply GlobalTheory.HSApp.ratGen_of_birOn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSamuelMapBirationalOfCuspFormsGenerate
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSamuelMapBirationalOfCuspFormsGenerate
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Vanishing.H0

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSApp

theorem modif_genericPoint {k : Type} [Field k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {U : Y.Opens} {D : ℕ}
    (M : Modif p U D) [IsIntegral M.X] {η : Y} (hη : η ∈ U) (hg : IsGenericPoint η Set.univ) :
    M.σ (genericPoint M.X) = η ∧ genericPoint M.X ∈ M.opn ∧ IsIso (M.σ.stalkMap (genericPoint M.X)) := by
  have := M.iso
  have hne : (M.opn : Set M.X).Nonempty := M.dense.nonempty
  have hmem : genericPoint M.X ∈ M.opn :=
    ((genericPoint_spec M.X).mem_open_set_iff M.opn.isOpen).2 (by simpa using hne)
  obtain ⟨z, hz⟩ := (M.σ ∣_ U).surjective ⟨η, hη⟩
  have hz' : M.σ z.1 = η := by rw [← morphismRestrict_base_coe, hz]
  have hsp : M.σ (genericPoint M.X) ⤳ η :=
    hz' ▸ ((genericPoint_spec M.X).specializes (Set.mem_univ z.1)).map M.σ.continuous
  have he : M.σ (genericPoint M.X) = η := (hsp.antisymm (hg.specializes (Set.mem_univ _))).eq
  refine ⟨he, hmem, ?_⟩
  let z0 : (M.σ ⁻¹ᵁ U).toScheme := ⟨genericPoint M.X, hmem⟩
  have h1 : IsIso ((M.σ ∣_ U ≫ U.ι).stalkMap z0) := by
    rw [Scheme.Hom.stalkMap_comp]
    have a := (IsOpenImmersion.iff_isIso_stalkMap.1 (inferInstance : IsOpenImmersion U.ι)).2 ((M.σ ∣_ U) z0)
    have b := (IsOpenImmersion.iff_isIso_stalkMap.1 (inferInstance : IsOpenImmersion (M.σ ∣_ U))).2 z0
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ a b
  rw [morphismRestrict_ι, Scheme.Hom.stalkMap_comp] at h1
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _
    ((IsOpenImmersion.iff_isIso_stalkMap.1 (inferInstance : IsOpenImmersion (M.σ ⁻¹ᵁ U).ι)).2 z0) h1

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem birational_of_ratGen {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c) {r : ℕ}
    (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (P : WtPar Dw) (R : Choice X Z U P) (ω : CanId R.toModif) (x : ℝ) {D : D7}
    (V : (c.F →+* ℂ) → TH.HSp D) (dict : ∀ σ, Formalism.L2.Theta.GA D (V σ) → Σ k, FD.Frame ((U σ).X k).Ψ r)
    (h : Ready R ω x V dict) (f₁ : CuspFrame Z U x V dict P.u₁) (f₂ : CuspFrame Z U x V dict P.u₂) (th : R.L.Sec)
    (k : Consts) (hR : RatGen X Z U P.u₁) : (h.geo f₁ f₂ th k).Birational := by
  obtain ⟨η, hη, hgen, hrat⟩ := hR
  haveI : IsIntegral R.X := HilbertSamuel.Geo.isIntegral (h.geo f₁ f₂ th k)
  obtain ⟨he, hmem, hiso⟩ := modif_genericPoint R.toModif hη hgen
  subst he
  set G := h.geo f₁ f₂ th k with hG
  set η' := genericPoint R.X with hη'
  refine ⟨η', genericPoint_spec _, ?_⟩
  set xp : Sp (R.X.residueField η') ⟶ G.Y := resPt η' with hxp
  set cc := G.chartAt (ptOf xp) with hcc
  have hc : η' ∈ R.Δ₁.moving.U cc := (ptOf_resPt η') ▸ G.mem_chartAt (ptOf xp)
  have hi0 : R.σ η' ∈ (L₀ X Z P.u₁).U (cc.1 PUnit.unit) := mem_pull.1 hc.1
  set φ := (R.σ.residueFieldMap η').hom with hφdef
  have hφ : ∀ a, φ (((Y₀ X Z).residue (R.σ η')).hom a) = (R.X.residue η').hom ((R.σ.stalkMap η').hom a) := fun a => by
    have := congrArg (fun g => g.hom a) (Scheme.residue_residueFieldMap R.σ η')
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using this

  let Vf : Cusp Z U P.u₁ → R.X.residueField η' := fun f => G.val xp (toSec (R.Δ₁.lift (h.ext₁.equiv f)))
  have hA : ∀ f, Vf f = ∑ j, G.baseHom xp (f₁.b.equivFun f j) * G.coords xp j := by
    intro f
    have e := R.toModif.ofSec_comb R.Δ₁ h.ext₁.equiv f₁ k.abelian₂ (f₁.b.equivFun f)
    rw [LinearEquiv.symm_apply_apply] at e
    have e2 : toSec (R.Δ₁.lift (h.ext₁.equiv f)) = G.comb (f₁.b.equivFun f) := by
      apply (bijective_ofSec_top (p := R.str) (B := R.Δ₁.moving)).1
      rw [ofSec_toSec]
      exact e.symm
    exact (congrArg (G.val xp) e2).trans (G.val_comb xp _)
  have hV : ∀ f, Vf f = (R.X.residue η').hom (germ cc η' (memTop η') hc (R.Δ₁.lift (h.ext₁.equiv f))) := by
    intro f
    show valR xp _ _ = _
    refine (projSys.valR_resPt η' _ hc _).trans ?_
    refine (congrArg (fun g => (ConcreteCategory.hom g) ((toSec (R.Δ₁.lift (h.ext₁.equiv f))).f cc))
      (Scheme.germ_residue R.X η' hc).symm).trans ?_
    exact congrArg (R.X.residue η').hom (ger_toSec _ cc η' hc)
  set τ := (R.X.residue η').hom (ger η' hc.2 (R.Δ₁.t.f cc.2)) with hτdef
  have hB : ∀ f, τ * Vf f = φ (((Y₀ X Z).residue (R.σ η')).hom
      (germ (cc.1 PUnit.unit) (R.σ η') hη hi0 (cuspSec X Z U P.u₁ f))) := by
    intro f
    have e1 := R.Δ₁.germ_lift (h.ext₁.equiv f) cc η' hc
    have e2 := germ_pull R.σ le_top cc.1 η' (memTop η') hc.1 (h.ext₁.equiv f).1
    have e3 := hφ (germ (cc.1 PUnit.unit) (R.σ η') (memTop _) hi0 (h.ext₁.equiv f).1)
    have e4 : germ (cc.1 PUnit.unit) (R.σ η') hη hi0 (cuspSec X Z U P.u₁ f) =
        germ (cc.1 PUnit.unit) (R.σ η') (memTop _) hi0 (h.ext₁.equiv f).1 := by
      rw [← h.ext₁.restr_equiv f, germ_restr]
    rw [hV, e4, e3, ← e2, ← e1]
    exact (map_mul _ _ _).symm
  have hτ : τ ≠ 0 := by
    have hu : IsUnit (ger η' hc.2 (R.Δ₁.t.f cc.2)) :=
      (isUnit_ger_iff _ hc.2).2 ((R.Δ₁.mem_nonzeroLocus η').2 (R.notMem_support h.free₁ η' (R.off_eq.ge hmem)))
    exact (hu.map (R.X.residue η').hom).ne_zero
  obtain ⟨j₀, hj₀⟩ : ∃ j, G.coords xp j ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact G.geom.alg.bpf.coords_ne_zero xp (funext hn)
  have hmemV : ∀ f f', Vf f / Vf f' ∈ G.ratioField xp := by
    intro f f'
    have key : ∀ g, Vf g = G.coords xp j₀ *
        ∑ j, G.baseHom xp (f₁.b.equivFun g j) * (G.coords xp j / G.coords xp j₀) := by
      intro g
      rw [hA, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      field_simp
    have hs : ∀ g, ∑ j, G.baseHom xp (f₁.b.equivFun g j) * (G.coords xp j / G.coords xp j₀) ∈ G.ratioField xp :=
      fun g => Subfield.sum_mem _ fun j _ => Subfield.mul_mem _ (Subfield.subset_closure (Or.inl ⟨_, rfl⟩))
        (Subfield.subset_closure (Or.inr ⟨j, j₀, rfl⟩))
    rw [key, key, mul_div_mul_left _ _ hj₀]
    exact Subfield.div_mem _ (hs f) (hs f')
  have hgen' : ratField (Set.range (cuspSec X Z U P.u₁)) (R.σ η') hη ≤ (G.ratioField xp).comap φ := by
    refine Subfield.closure_le.2 ?_
    rintro _ ⟨i, hi, _, _, ⟨f, rfl⟩, ⟨f', rfl⟩, rfl⟩
    have htr : ((Y₀ X Z).residue (R.σ η')).hom (tr (L₀ X Z P.u₁) (R.σ η') i (cc.1 PUnit.unit) : _) ≠ 0 :=
      ((Units.isUnit _).map _).ne_zero
    show φ (_ / _) ∈ G.ratioField xp
    rw [germ_change i (cc.1 PUnit.unit) _ hη hi hi0, germ_change i (cc.1 PUnit.unit) _ hη hi hi0, map_mul, map_mul,
      mul_div_mul_left _ _ htr, map_div₀, ← hB f, ← hB f', mul_div_mul_left _ _ hτ]
    exact hmemV f f'
  refine eq_top_iff.2 fun y _ => ?_
  obtain ⟨a', rfl⟩ := R.X.residue_surjective η' y
  obtain ⟨a, rfl⟩ := ((ConcreteCategory.isIso_iff_bijective _).1 hiso).2 a'
  rw [← hφ]
  exact hgen' (hrat.ge trivial)

end GlobalTheory.HSApp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSamuelMapBirationalOfCuspFormsGenerateStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Vanishing.H0
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertSamuel_map_birational_of_cuspForms_generate : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (P : WtPar Dw) (R : Choice X Z U P) (ω : CanId R.toModif) (x : ℝ) {D : D7} (V : (c.F →+* ℂ) → TH.HSp D) (dict : ∀ σ, Formalism.L2.Theta.GA D (V σ) → Σ k, FD.Frame ((U σ).X k).Ψ r) (h : Ready R ω x V dict) (f₁ : CuspFrame Z U x V dict P.u₁) (f₂ : CuspFrame Z U x V dict P.u₂) (th : R.L.Sec) (k : Consts), RatGen X Z U P.u₁ → (h.geo f₁ f₂ th k).Birational := by
  first | exact @GlobalTheory.HSApp.birational_of_ratGen | exact GlobalTheory.HSApp.birational_of_ratGen | (intros; apply GlobalTheory.HSApp.birational_of_ratGen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistingSectionPreservesHermitianLatticesRanks
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistingSectionPreservesHermitianLatticesRanks
set_option synthInstance.maxHeartbeats 400000

open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

noncomputable section

namespace GlobalTheory.FlatTw.Good

open scoped nonZeroDivisors

theorem exists_vAdd_ge {K : Type} [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K))) (B : ℕ) :
    ∃ a : K, a ≠ 0 ∧ (∀ w : HeightOneSpectrum (𝓞 K), 0 ≤ vAdd w a) ∧ ∀ w ∈ S, (B : ℤ) ≤ vAdd w a := by
  classical
  let I : Ideal (𝓞 K) := ∏ w ∈ S, w.asIdeal ^ B
  have hI : I ≠ ⊥ := by
    rw [← Ideal.zero_eq_bot]
    exact Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact w.ne_bot)
  obtain ⟨r, hrI, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  have ha0 : algebraMap (𝓞 K) K r ≠ 0 := by
    rwa [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K)]
  have hmem : algebraMap (𝓞 K) K r ∈
      (∏ w ∈ S, (((Equiv.refl (HeightOneSpectrum (𝓞 K))) w).asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^
        (-((fun _ => -(B : ℤ)) w))) := by
    have e : (∏ w ∈ S, (((Equiv.refl (HeightOneSpectrum (𝓞 K))) w).asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^
        (-((fun _ => -(B : ℤ)) w))) = ((I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
      simp only [Equiv.refl_apply, neg_neg, zpow_natCast, I]
      rw [← FractionalIdeal.coeIdealHom_apply, map_prod]
      simp [FractionalIdeal.coeIdealHom_apply, FractionalIdeal.coeIdeal_pow]
    rw [e]
    exact (FractionalIdeal.mem_coeIdeal _).2 ⟨r, hrI, rfl⟩
  refine ⟨_, ha0, fun w => ?_, fun w hw => ?_⟩
  · have h := (GlobalTheory.Core.Int.ProdPrimePow.vAdd_ge_of_mem_prod_zpow K _ (Equiv.refl _) S
      (fun _ => -(B : ℤ)) _ hmem w).resolve_left ha0
    simp only [Equiv.refl_apply, neg_neg] at h
    split_ifs at h
    · exact le_trans (by positivity) h
    · exact h
  · have h := (GlobalTheory.Core.Int.ProdPrimePow.vAdd_ge_of_mem_prod_zpow K _ (Equiv.refl _) S
      (fun _ => -(B : ℤ)) _ hmem w).resolve_left ha0
    simp only [Equiv.refl_apply, neg_neg, if_pos hw] at h
    exact h

end GlobalTheory.FlatTw.Good

namespace GlobalTheory.FlatTw.Good

theorem exists_twist_scalar {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}
    {Z : Comp Xo c} {G₀ : WTZ E} (s : TwSec U x Z G₀) :
    ∃ a : c.F, a ≠ 0 ∧ (∀ w, 0 ≤ (vAdd w a : ℝ) + s.lo w) ∧ ∀ w, s.hi w ≤ (vAdd w a : ℝ) := by
  classical
  let S : Finset (HeightOneSpectrum (𝓞 c.F)) := s.finite_lo.toFinset ∪ s.finite_hi.toFinset
  let B : ℕ := ⌈∑ w ∈ S, (|s.lo w| + |s.hi w|)⌉₊
  have hB : ∀ w ∈ S, |s.lo w| + |s.hi w| ≤ B := fun w hw =>
    (Finset.single_le_sum (f := fun w => |s.lo w| + |s.hi w|)
      (fun _ _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) hw).trans (Nat.le_ceil _)
  obtain ⟨a, ha0, hpos, hS⟩ := exists_vAdd_ge S B
  refine ⟨a, ha0, fun w => ?_, fun w => ?_⟩
  · by_cases hw : w ∈ S
    · have h1 := hB w hw
      have h2 : ((B : ℤ) : ℝ) ≤ (vAdd w a : ℝ) := by exact_mod_cast hS w hw
      have h3 := neg_abs_le (s.lo w)
      push_cast at h2
      linarith [abs_nonneg (s.hi w)]
    · have : s.lo w = 0 := by
        by_contra h
        exact hw (Finset.mem_union_left _ (s.finite_lo.mem_toFinset.2 h))
      rw [this, add_zero]; exact_mod_cast hpos w
  · by_cases hw : w ∈ S
    · have h1 := hB w hw
      have h2 : ((B : ℤ) : ℝ) ≤ (vAdd w a : ℝ) := by exact_mod_cast hS w hw
      have h3 := le_abs_self (s.hi w)
      push_cast at h2
      linarith [abs_nonneg (s.lo w)]
    · have : s.hi w = 0 := by
        by_contra h
        exact hw (Finset.mem_union_right _ (s.finite_hi.mem_toFinset.2 h))
      rw [this]; exact_mod_cast hpos w

theorem cnorm_smul {ι : Type} [Fintype ι] (k : ℂ) (u : ι → ℂ) : Formalism.HermitianLatticesTheory.cnorm (k • u) = ‖k‖ * Formalism.HermitianLatticesTheory.cnorm u := by
  unfold Formalism.HermitianLatticesTheory.cnorm
  have : ∑ i, ‖(k • u) i‖ ^ 2 = ‖k‖ ^ 2 * ∑ i, ‖u i‖ ^ 2 := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
  rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

end GlobalTheory.FlatTw.Good

namespace GlobalTheory.FlatTw.Good

section Abstract

variable {K : Type} [Field K] [NumberField K] {V W : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]

theorem lattice_transfer (φ : V ≃ₗ[K] W) (L : Submodule (𝓞 K) V) (L' : Submodule (𝓞 K) W) (a : K) (ha : a ≠ 0)
    (hin : ∀ f ∈ L, a • φ f ∈ L') (hout : ∀ g ∈ L', a • φ.symm g ∈ L) (hFG : L.FG)
    (hspan : Submodule.span K (L : Set V) = ⊤) :
    L'.FG ∧ Submodule.span K (L' : Set W) = ⊤ ∧ Formalism.HN.rkK L' = Formalism.HN.rkK L := by
  let ψ : V →ₗ[𝓞 K] W :=
    { toFun := fun f => a⁻¹ • φ f
      map_add' := fun f f' => by rw [map_add (f := _), smul_add]
      map_smul' := fun m f => by
        rw [RingHom.id_apply, ← algebraMap_smul K m f, map_smul, ← algebraMap_smul K m (a⁻¹ • φ f),
          smul_smul, smul_smul, mul_comm] }
  have hle : L' ≤ L.map ψ := fun g hg => by
    refine ⟨a • φ.symm g, hout g hg, ?_⟩
    show a⁻¹ • φ (a • φ.symm g) = g
    rw [map_smul, φ.apply_symm_apply, smul_smul, inv_mul_cancel₀ ha, one_smul]
  have hFG' : L'.FG := by
    have := isNoetherian_of_fg_of_noetherian _ (hFG.map ψ)
    exact isNoetherian_submodule.mp this _ hle
  have hspan' : Submodule.span K (L' : Set W) = ⊤ := by
    have hsub : Submodule.span K (L : Set V) ≤ (Submodule.span K (L' : Set W)).comap (φ : V →ₗ[K] W) := by
      refine Submodule.span_le.2 fun f hf => Submodule.mem_comap.2 ?_
      have h2 := Submodule.smul_mem (Submodule.span K (L' : Set W)) a⁻¹ (Submodule.subset_span (R := K) (hin f hf))
      rw [smul_smul, inv_mul_cancel₀ ha, one_smul] at h2
      exact h2
    rw [eq_top_iff]
    intro g _
    have h := hsub (show φ.symm g ∈ Submodule.span K (L : Set V) by rw [hspan]; trivial)
    simpa using h
  refine ⟨hFG', hspan', ?_⟩
  unfold Formalism.HN.rkK
  rw [hspan, hspan', finrank_top, finrank_top]
  exact φ.symm.finrank_eq


omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] in
theorem hasGram_transfer (φ : V ≃ₗ[K] W) (N : (K →+* ℂ) → V → ℝ) (N' : (K →+* ℂ) → W → ℝ) (t : (K →+* ℂ) → ℝ)
    (ht : ∀ σ, 0 < t σ) (h : ∀ σ f, N' σ (φ f) = t σ * N σ f) (hN : HasGram N) : HasGram N' := by
  obtain ⟨⟨n, ⟨b, X⟩, hX⟩⟩ := hN
  refine ⟨⟨n, ⟨(b.map φ, fun v => ((t v.embedding : ℂ)⁻¹) • X v), fun v => ?_⟩⟩⟩
  have hk : ((t v.embedding : ℂ)⁻¹) ≠ 0 := inv_ne_zero (Complex.ofReal_ne_zero.2 (ht _).ne')
  have hdet := (hX v).1
  refine ⟨?_, fun y => ?_⟩
  · show IsUnit ((((t v.embedding : ℂ)⁻¹) • X v).det)
    rw [Matrix.det_smul]
    exact (IsUnit.pow _ (Ne.isUnit hk)).mul hdet
  · show Formalism.HermitianLatticesTheory.normAt (b.map φ) (fun v => ((t v.embedding : ℂ)⁻¹) • X v) v y = N' v.embedding y
    have := invertibleOfNonzero hk
    rw [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.fcoord, Matrix.inv_smul _ _ hdet, invOf_eq_inv]
    have hvec : Formalism.HermitianLatticesTheory.vecAt (b.map φ) v y = Formalism.HermitianLatticesTheory.vecAt b v (φ.symm y) := by
      funext i; simp [Formalism.HermitianLatticesTheory.vecAt, Module.Basis.map_repr]
    rw [hvec, Matrix.smul_mulVec, cnorm_smul, ← Formalism.HermitianLatticesTheory.fcoord, ← Formalism.HermitianLatticesTheory.normAt, (hX v).2,
      ← φ.apply_symm_apply y, h, φ.apply_symm_apply]
    rw [inv_inv, Complex.norm_real, Real.norm_of_nonneg (ht _).le]

end Abstract

end GlobalTheory.FlatTw.Good

namespace GlobalTheory.FlatTw.Good

theorem twist_goodOn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (D : D7) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r) (Z : Comp Xo c) (G₀ : WTZ E) (_s : TwSec U x Z G₀) (G : WTZ E), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → Even G.2 → GoodOn U x V dict Z G → GoodOn U x V dict Z (G + G₀) ∧ rankOn U Z (G + G₀) = rankOn U Z G := by
  intro E _ _ _ H Dw l Xo c r U x D V dict Z G₀ s G _hU hG hgood
  obtain ⟨hGram, hFG, hspan⟩ := hgood
  obtain ⟨φ, hφ, -, hA, hB⟩ := Mul.twSec_mulEquiv_integral E H Dw l Xo c r U x Z G₀ s G hG
  obtain ⟨a, ha0, hlo, hhi⟩ := exists_twist_scalar s
  obtain ⟨hFG', hspan', hrk⟩ := lattice_transfer φ (latOn U Z G) (latOn U Z (G + G₀)) a ha0
    (fun f hf => hA a ha0 hlo f hf _ (Submodule.coe_smul _ _))
    (fun g hg => hB a ha0 hhi g hg _ (Submodule.coe_smul _ _)) hFG hspan
  refine ⟨⟨hasGram_transfer φ _ _ s.cInf s.cInf_pos (fun σ f => ?_) hGram, hFG', hspan'⟩, hrk⟩
  show petOn U x V dict Z (G + G₀) σ (φ f : Rul Xo c) = s.cInf σ * petOn U x V dict Z G σ (f : Rul Xo c)
  rw [hφ, petOn, petOn, GlobalTheory.T.petersson_norm_mul_twistingSection_eq_const_mul E H Dw l Xo c r U x Z G₀ s G hG _ f.2.2]

end GlobalTheory.FlatTw.Good
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistingSectionPreservesHermitianLatticesRanksStatement
open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistingSection_preserves_hermitianLattices_ranks : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (D : D7) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r) (Z : Comp Xo c) (G₀ : WTZ E) (_s : TwSec U x Z G₀) (G : WTZ E), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → Even G.2 → GoodOn U x V dict Z G → GoodOn U x V dict Z (G + G₀) ∧ rankOn U Z (G + G₀) = rankOn U Z G := by
  first | exact @GlobalTheory.FlatTw.Good.twist_goodOn | exact GlobalTheory.FlatTw.Good.twist_goodOn | (intros; apply GlobalTheory.FlatTw.Good.twist_goodOn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegBoundOfClaimNumbers
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSamuelDegreeRatioLowerBoundRearrangedStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSamuelDegreeRatioLowerBoundRearranged
namespace GlobalTheory.CovNum

open Formalism.NormVectorIdentities.Items

theorem hsLogRho_bounds (D : ℕ) (n Λ δ h l₀ : ℝ) (hD : 1 ≤ D) (hn : 1 ≤ n) (hΛ : 1 ≤ Λ)
    (hδ : 1 ≤ δ)
    (hl : Real.log Λ + 26 * Real.log (n * D * δ * (1 + Real.log Λ)) ≤ l₀) :
    0 ≤ hsLogRho 26 n D 1 Λ δ h ∧
      hsLogRho 26 n D 1 Λ δ h ≤ l₀ + 26 * Real.log (2 + |h|) := by
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hL : 0 ≤ Real.log Λ := Real.log_nonneg hΛ
  have hh : 0 ≤ |h| := abs_nonneg h
  have h1 : 1 ≤ n * D * δ :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hn hD') hδ
  have h2 : 1 ≤ n * D * δ * (2 + |h| + Real.log Λ) :=
    one_le_mul_of_one_le_of_one_le h1 (by linarith)
  have h3 : n * D * δ * (2 + |h| + Real.log Λ)
      ≤ (n * D * δ * (1 + Real.log Λ)) * (2 + |h|) := by
    rw [mul_assoc (n * D * δ)]
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    nlinarith [mul_nonneg hL hh]
  have h4 : Real.log (n * D * δ * (2 + |h| + Real.log Λ))
      ≤ Real.log (n * D * δ * (1 + Real.log Λ)) + Real.log (2 + |h|) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    exact Real.log_le_log (by linarith) h3
  have h5 := Real.log_nonneg h2
  unfold hsLogRho
  rw [mul_one]
  constructor <;> linarith

theorem deg_lower_of_claim : ∀ (T D : ℕ) (n Λ β ΛD ΛT J δ h d deg z l₀ : ℝ), 1 ≤ T → 1 ≤ D → 1 ≤ n → 1 ≤ Λ → 1 ≤ β → 1 ≤ ΛD → 1 ≤ ΛT → 1 ≤ δ → 0 < d → 0 ≤ z → z ≤ 1 / 2 → (1 - z) * d ≤ ((T - 1).choose D : ℕ) * δ → Real.log Λ + 26 * Real.log (n * D * δ * (1 + Real.log Λ)) ≤ l₀ → Formalism.NormVectorIdentities.Items.HSClaimS 26 T D n 1 Λ β ΛD ΛT J δ h d deg → ((T - 1).choose D : ℕ) * δ * (T * h - 3 * (D + 1) * |h| - 26 * (26 * D ^ 2 + 2 * z * T) * Real.log (2 + |h|) - (J + 26 * D ^ 2 * (l₀ + Real.log T) + (T + D + 1) * Real.log β + (T + D ^ 2) * (Formalism.NormVectorIdentities.Items.hsG D n + 2) + 2 * z * (T * (Real.log 2 + l₀ + Real.log β / 2) + Real.log ΛD + Real.log ΛT))) ≤ deg := by
  intro T D n Λ β ΛD ΛT J δ h d deg z l₀ hT hD hn hΛ hβ hΛD hΛT hδ hd hz hz2 hP hl hc
  obtain ⟨hρ0, hρ⟩ := hsLogRho_bounds D n Λ δ h l₀ hD hn hΛ hδ hl
  obtain ⟨-, -, hc⟩ := hc
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hβ0 : 0 < β := by linarith
  have e1 : Real.log (Real.exp (hsLogRho 26 n D 1 Λ δ h) * T)
      = hsLogRho 26 n D 1 Λ δ h + Real.log T := by
    rw [Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp]
  have e2 : Real.log (2 * Real.exp (hsLogRho 26 n D 1 Λ δ h) * Real.sqrt β)
      = Real.log 2 + hsLogRho 26 n D 1 Λ δ h + Real.log β / 2 := by
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp, Real.log_sqrt hβ0.le]
  rw [e1, e2, le_div_iff₀ hd] at hc
  unfold hsZ hsR at hc
  generalize hsLogRho 26 n D 1 Λ δ h = ρ at hρ0 hρ hc
  generalize ((Nat.choose (T - 1) D : ℕ) : ℝ) * δ = P at hP hc ⊢
  generalize hsG D n = g at hc ⊢
  have hb := Real.log_nonneg hβ
  have hLD := Real.log_nonneg hΛD
  have hLT := Real.log_nonneg hΛT
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  generalize Real.log (2 + |h|) = L at hρ ⊢
  have hdP : d ≤ 2 * P := by nlinarith
  have hP0 : 0 ≤ P := by linarith
  have hdef : d - P ≤ 2 * z * P := by nlinarith
  set A := (T : ℝ) * h - 3 * ((D : ℝ) + 1) * |h| - J - 26 * (D : ℝ) ^ 2 * (ρ + Real.log T)
    - ((T : ℝ) + D + 1) * Real.log β - ((T : ℝ) + (D : ℝ) ^ 2) * (g + 2) with hA
  set B := (T : ℝ) * (Real.log 2 + ρ + Real.log β / 2) + Real.log ΛD + Real.log ΛT with hB
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have e3 : ((1 - (1 - P / d)) * A - (1 - P / d) * B) * d = P * A - (d - P) * B := by
    field_simp
    ring
  rw [e3] at hc
  have h6 : (d - P) * B ≤ 2 * z * P * B := mul_le_mul_of_nonneg_right hdef hB0
  have h7 : 0 ≤ (26 * (D : ℝ) ^ 2 + 2 * z * T) * (l₀ + 26 * L - ρ) :=
    mul_nonneg (by positivity) (by linarith)
  have h8 : P * (A - 2 * z * B - (26 * (D : ℝ) ^ 2 + 2 * z * T) * (l₀ + 26 * L - ρ))
      ≤ P * (A - 2 * z * B) := mul_le_mul_of_nonneg_left (by linarith) hP0
  refine le_trans (le_of_eq ?_) (h8.trans (by linarith))
  rw [hA, hB]
  ring

end GlobalTheory.CovNum
end

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertSamuel_degree_ratio_lower_bound_rearranged : ∀ (T D : ℕ) (n Λ β ΛD ΛT J δ h d deg z l₀ : ℝ), 1 ≤ T → 1 ≤ D → 1 ≤ n → 1 ≤ Λ → 1 ≤ β → 1 ≤ ΛD → 1 ≤ ΛT → 1 ≤ δ → 0 < d → 0 ≤ z → z ≤ 1 / 2 → (1 - z) * d ≤ ((T - 1).choose D : ℕ) * δ → Real.log Λ + 26 * Real.log (n * D * δ * (1 + Real.log Λ)) ≤ l₀ → Formalism.NormVectorIdentities.Items.HSClaimS 26 T D n 1 Λ β ΛD ΛT J δ h d deg → ((T - 1).choose D : ℕ) * δ * (T * h - 3 * (D + 1) * |h| - 26 * (26 * D ^ 2 + 2 * z * T) * Real.log (2 + |h|) - (J + 26 * D ^ 2 * (l₀ + Real.log T) + (T + D + 1) * Real.log β + (T + D ^ 2) * (Formalism.NormVectorIdentities.Items.hsG D n + 2) + 2 * z * (T * (Real.log 2 + l₀ + Real.log β / 2) + Real.log ΛD + Real.log ΛT))) ≤ deg := by
  first | exact @GlobalTheory.CovNum.deg_lower_of_claim | exact GlobalTheory.CovNum.deg_lower_of_claim | (intros; apply GlobalTheory.CovNum.deg_lower_of_claim <;> assumption)
end

namespace GlobalTheory.CovHSNum


set_option maxHeartbeats 1000000 in
theorem deg_bound_of_claim_numbers : ∀ (T D : ℕ) (PP kap b z ρ n Λ β ΛD ΛT J δ h d deg degM c : ℝ), 1 ≤ D → 3 * D + 5 ≤ T → 1 ≤ PP → 1 ≤ b → Real.log b ≤ PP → (T : ℝ) * PP ≤ Real.sqrt b → z = 7 * ((D : ℝ) ^ 2 / T + D * ρ) → 0 ≤ ρ → z ≤ 1 / 2 → z * (PP * kap) ≤ b → 0 ≤ kap → 1 ≤ n → 1 ≤ Λ → 1 ≤ β → 1 ≤ ΛD → 1 ≤ ΛT → 1 ≤ δ → 0 < d → Real.log n ≤ PP → Real.log β ≤ PP → Real.log δ ≤ PP → Real.log Λ ≤ PP * (kap / T + 1) → Real.log ΛD ≤ PP * kap → Real.log ΛT ≤ PP * kap → J ≤ 4 * (D * PP * (kap / T + 1) + T * PP) + 2 * PP * (kap / T) * D → (1 - z) * d ≤ ((T - 1).choose D : ℕ) * δ → Formalism.NormVectorIdentities.Items.HSClaimS 26 T D n 1 Λ β ΛD ΛT J δ h d deg → 0 ≤ c → deg - d * c ≤ degM → ((T - 1).choose D : ℕ) * δ * ((T : ℝ) * h - 3 * ((D : ℝ) + 1) * |h| - 26 * (26 * (D : ℝ) ^ 2 + 2 * z * T) * Real.log (2 + |h|) - (4000 * b + 2 * c)) ≤ degM := by
  intro T D PP kap b z ρ n Λ β ΛD ΛT J δ h d deg degM c hD1 hDT hPP hb hlogb hTPP hz hρ hz2 hzk hkap hn hΛ hβ hΛD hΛT hδ hd hlogn hlogβ hlogδ hlogΛ hlogΛD hlogΛT hJ hcmp hclaim hc hdeg
  have hT8 : (8:ℝ) ≤ T := by exact_mod_cast (by omega : 8 ≤ T)
  have hD1r : (1:ℝ) ≤ D := by exact_mod_cast hD1
  have hDTr : (D:ℝ) + 1 ≤ T := by exact_mod_cast (by omega : D + 1 ≤ T)
  have hTpos : (0:ℝ) < T := by linarith
  have hT0 : (T:ℝ) ≠ 0 := hTpos.ne'

  have hs0 : 0 ≤ Real.sqrt b := Real.sqrt_nonneg b
  have hs2 : Real.sqrt b ^ 2 = b := Real.sq_sqrt (by linarith)
  have hs1 : 1 ≤ Real.sqrt b := by
    have := Real.sqrt_le_sqrt (show (1:ℝ) ≤ b from hb)
    rwa [Real.sqrt_one] at this
  have hsb : Real.sqrt b ≤ b := by nlinarith [mul_le_mul_of_nonneg_left hs1 hs0]
  have hTPPb : (T:ℝ) * PP ≤ b := le_trans hTPP hsb
  have hTPP0 : 0 ≤ (T:ℝ) * PP := by positivity
  have hTPP2 : ((T:ℝ) * PP) ^ 2 ≤ b := by
    calc ((T:ℝ) * PP) ^ 2 ≤ (Real.sqrt b) ^ 2 := pow_le_pow_left₀ hTPP0 hTPP 2
      _ = b := hs2
  have hTs : (T:ℝ) ≤ Real.sqrt b := le_trans (by nlinarith) hTPP
  have hlogT : Real.log T ≤ PP / 2 := by
    have := Real.log_le_log hTpos hTs
    rw [Real.log_sqrt (by linarith)] at this
    linarith
  have hlogD : Real.log D ≤ Real.log T := Real.log_le_log (by linarith) (by linarith)
  have hlogΛ0 : 0 ≤ Real.log Λ := Real.log_nonneg hΛ
  have hlogβ0 : 0 ≤ Real.log β := Real.log_nonneg hβ
  have hlogn0 : 0 ≤ Real.log n := Real.log_nonneg hn
  have hlog1 : Real.log (1 + Real.log Λ) ≤ Real.log Λ := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + Real.log Λ by linarith)
    linarith
  have hprod : Real.log (n * D * δ * (1 + Real.log Λ)) =
      Real.log n + Real.log D + Real.log δ + Real.log (1 + Real.log Λ) := by
    have h1 : (0:ℝ) < n := by linarith
    have h2 : (0:ℝ) < D := by linarith
    have h3 : (0:ℝ) < δ := by linarith
    have h4 : (0:ℝ) < 1 + Real.log Λ := by linarith
    rw [Real.log_mul (mul_pos (mul_pos h1 h2) h3).ne' h4.ne',
      Real.log_mul (mul_pos h1 h2).ne' h3.ne', Real.log_mul h1.ne' h2.ne']

  have hD2T0 : 0 ≤ (D:ℝ) ^ 2 / T := by positivity
  have hDρ : 0 ≤ (D:ℝ) * ρ := mul_nonneg (by positivity) hρ
  have hz0 : 0 ≤ z := by rw [hz]; linarith
  have hD2z : (D:ℝ) ^ 2 ≤ z * T / 7 := by
    have e : z * T / 7 = (D:ℝ) ^ 2 + D * ρ * T := by rw [hz]; field_simp
    rw [e]; have := mul_nonneg hDρ hTpos.le; linarith
  have hD2T : (D:ℝ) ^ 2 ≤ T / 14 := by nlinarith [mul_le_mul_of_nonneg_right hz2 hTpos.le]

  have hq0 : 0 ≤ kap / T := div_nonneg hkap hTpos.le
  obtain ⟨q, hq⟩ : ∃ q : ℝ, kap / T = q := ⟨_, rfl⟩
  have hkq : kap = q * T := by rw [← hq]; field_simp
  rw [hq] at hlogΛ hJ hq0
  rw [hkq] at hzk hlogΛD hlogΛT
  clear hq hkq hkap
  have hl0 : Real.log Λ + 26 * Real.log (n * D * δ * (1 + Real.log Λ)) ≤
      27 * (PP * (q + 1)) + 65 * PP := by
    rw [hprod]; linarith
  have key := GlobalTheory.T.hilbertSamuel_degree_ratio_lower_bound_rearranged T D n Λ β ΛD ΛT J δ h d deg z (27 * (PP * (q + 1)) + 65 * PP)
    (by omega) hD1 hn hΛ hβ hΛD hΛT hδ hd hz0 hz2 hcmp hl0 hclaim

  have hPPq : 0 ≤ PP * q := mul_nonneg (by linarith) hq0
  have F1 : (D:ℝ) ^ 2 * (PP * q) ≤ b / 7 := by
    linarith [mul_le_mul_of_nonneg_right hD2z hPPq]
  have F2 : (D:ℝ) ^ 2 * PP ≤ b / 14 := by
    linarith [mul_le_mul_of_nonneg_right hD2T (show (0:ℝ) ≤ PP by linarith)]
  have hDD2 : (D:ℝ) ≤ (D:ℝ) ^ 2 := by nlinarith
  have hDPPq : (D:ℝ) * (PP * q) ≤ b / 7 := by
    linarith [mul_le_mul_of_nonneg_right hDD2 hPPq]
  have hDPP : (D:ℝ) * PP ≤ b := by
    linarith [mul_le_mul_of_nonneg_right (show (D:ℝ) ≤ T by linarith) (show (0:ℝ) ≤ PP by linarith)]
  have t1 : J ≤ 9 * b := by linarith
  have hDlogT : (D:ℝ) ^ 2 * Real.log T ≤ (D:ℝ) ^ 2 * (PP / 2) :=
    mul_le_mul_of_nonneg_left hlogT (sq_nonneg _)
  have t2 : 26 * (D:ℝ) ^ 2 * ((27 * (PP * (q + 1)) + 65 * PP) + Real.log T) ≤ 300 * b := by
    linarith
  have t3 : ((T:ℝ) + D + 1) * Real.log β ≤ 2 * b := by
    have := mul_le_mul (show (T:ℝ) + D + 1 ≤ 2 * T by linarith) hlogβ hlogβ0 (by linarith)
    linarith
  have hG : Formalism.NormVectorIdentities.Items.hsG D n + 2 ≤ 5 * D * PP := by
    unfold Formalism.NormVectorIdentities.Items.hsG
    have a1 := mul_le_mul_of_nonneg_left hlogn (show (0:ℝ) ≤ D + 1 by linarith)
    have a2 := mul_le_mul_of_nonneg_left hPP (show (0:ℝ) ≤ D by linarith)
    have a3 := mul_le_mul_of_nonneg_right hD1r (show (0:ℝ) ≤ PP by linarith)
    nlinarith
  have hG0 : 0 ≤ Formalism.NormVectorIdentities.Items.hsG D n + 2 := by
    unfold Formalism.NormVectorIdentities.Items.hsG; positivity
  have hTDPP : (T:ℝ) * D * PP ≤ b := by
    have e1 : (T:ℝ) * D * PP ≤ T * T * PP := by
      have := mul_le_mul_of_nonneg_left (show (D:ℝ) ≤ T by linarith) hTPP0
      linarith
    have e2 : (T:ℝ) * T * PP ≤ T * T * PP * PP := by
      have := mul_le_mul_of_nonneg_left hPP (mul_nonneg hTPP0 hTpos.le)
      linarith
    linarith only [e1, e2, hTPP2]
  have t4 : ((T:ℝ) + D ^ 2) * (Formalism.NormVectorIdentities.Items.hsG D n + 2) ≤ 10 * b := by
    have := mul_le_mul (show (T:ℝ) + D ^ 2 ≤ 2 * T by linarith) hG hG0 (by linarith)
    linarith
  have hl2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  have hl20 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have p1 := mul_le_mul_of_nonneg_left hlogΛD hz0
  have p2 := mul_le_mul_of_nonneg_left hlogΛT hz0
  have p3 : z * ((T:ℝ) * Real.log β) ≤ (1/2) * ((T:ℝ) * PP) :=
    mul_le_mul hz2 (mul_le_mul_of_nonneg_left hlogβ hTpos.le) (mul_nonneg hTpos.le hlogβ0) (by norm_num)
  have p4 : z * ((T:ℝ) * Real.log 2) ≤ (1/2) * ((T:ℝ) * 1) :=
    mul_le_mul hz2 (mul_le_mul_of_nonneg_left hl2.le hTpos.le) (mul_nonneg hTpos.le hl20) (by norm_num)
  have p5 : z * ((T:ℝ) * PP) ≤ (1/2) * ((T:ℝ) * PP) :=
    mul_le_mul_of_nonneg_right hz2 hTPP0
  have t5 : 2 * z * ((T:ℝ) * (Real.log 2 + (27 * (PP * (q + 1)) + 65 * PP) + Real.log β / 2) +
      Real.log ΛD + Real.log ΛT) ≤ 200 * b := by
    linarith

  set B : ℝ := (((T - 1).choose D : ℕ) : ℝ) * δ with hB
  have hB0 : 0 ≤ B := by positivity
  have hR : J + 26 * (D:ℝ) ^ 2 * ((27 * (PP * (q + 1)) + 65 * PP) + Real.log T) + ((T:ℝ) + D + 1) * Real.log β +
      ((T:ℝ) + D ^ 2) * (Formalism.NormVectorIdentities.Items.hsG D n + 2) + 2 * z * ((T:ℝ) * (Real.log 2 + (27 * (PP * (q + 1)) + 65 * PP) + Real.log β / 2) +
      Real.log ΛD + Real.log ΛT) ≤ 4000 * b := by linarith
  have hd2 : d ≤ 2 * B := by linarith [mul_le_mul_of_nonneg_right hz2 hd.le]
  have hdc := mul_le_mul_of_nonneg_right hd2 hc
  have hBR := mul_le_mul_of_nonneg_left hR hB0
  linarith

end GlobalTheory.CovHSNum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelHalfSplit
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SplitLevel

theorem level_halfSplit : ∀ (D : D7) (T : Core D), LawsM T → ∀ (_ : ErrX D), ∃ π π' : 𝓞 D.host.E, HalfSplit T.Q.l (D.host.g 0) (D.host.g 1) π π' := by
  intro D T h EX
  have hp : ∀ i, piOf T EX i * T.Q.H.bar (piOf T EX i) = ((D.host.g i : ℕ) : 𝓞 D.host.E) := fun i => by
    rw [bar_core]; exact piOf_mul_barE T EX i
  have hM : T.Q.l.Mb = Ideal.span {piOf T EX 0 * piOf T EX 1} := by
    rw [← Ideal.span_singleton_mul_span_singleton, span_piOf T h, span_piOf T h, Mb_eq T h]
  exact ⟨piOf T EX 0, piOf T EX 1, D.host.g_prime 0, D.host.g_prime 1, D.host.g_ne,
    by rw [level_M T h, mul_comm], hp 0, hp 1, hM,
    GlobalTheory.LevelSplit.splitsIn_level_prime D 0, GlobalTheory.LevelSplit.splitsIn_level_prime D 1⟩

end GlobalTheory.SplitLevel
end
