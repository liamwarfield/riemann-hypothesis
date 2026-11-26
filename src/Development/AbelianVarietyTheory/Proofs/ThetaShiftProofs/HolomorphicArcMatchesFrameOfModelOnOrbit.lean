module

public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicArcAgreesAnalyticDictionary
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsFramedPointOfArcBaseChange
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRingHomLift
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsTauCanonicalTrivialisationIffNormalisedArc

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicArcMatchesFrameOfModelOnOrbit
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicArcMatchesFrameOfModelOnOrbit
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj hiding Unf GoodEmb
open Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArcCM

theorem tieC_of_onOrbit : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (Uw : UnfWit U) (k : U.Comp) (ξ' : Fin r → E) (x : Frame (U.X k).Ψ r) (aC : ArcIn Dw l (RingHom.id c.F) ℂ σ) (Λ : GtAn₀ aC) (ξC : Module.Dual ℤ aC.D₀.X), GoodEmb c σ → IsUnf U → (U.X k).IsIso ξ' → x ∈ (U.X k).dom → l.A = 1 → letI := H.starRing; ∀ (gam : (Uw.F.Di (Uw.ik k)).La ≃ₗ[𝓞 E] Λ.A.La) (ξ : Module.Dual ℤ Λ.A.X), OnOrbit Uw k ξ' x Λ.A gam ξ → (∀ y, ξC (Λ.eX y) = ξ y) → (∀ v, Λ.Lifts (aC.eta v) (gam (Uw.F.t (Uw.ik k) v))) → ∀ (O : Type) [CommRing O] (β : O →+* c.F), TieC Uw (aC.restrict β) ξC k ξ' x := by
  intro hK E _ _ _ H Dw l Xo c _ _ σ r U Uw k ξ' x aC Λ ξC hσ hU hξ hx hA gam ξ hO hξC hL O _ β Y χ W Ha
  let := H.starRing
  let Λ' : GtAn₀ (aC.restrict β) := ⟨Λ.toGtDict, Λ.be_eq⟩
  obtain ⟨g₁, h₁, e1, e2, e3, e4⟩ := GlobalTheory.T.holomorphicArc_agrees_analyticDictionary hK E H Dw l Xo c σ O β Y (aC.restrict β) χ W Uw.g _ Uw.F Ha Λ'
  obtain ⟨o1, ⟨t', o2, o3⟩, T₀, o4⟩ := hO
  have hw : max Ha.T T₀ < (((max Ha.T T₀ + 1 : ℝ) : ℂ) * Complex.I).im := by simp
  generalize (((max Ha.T T₀ + 1 : ℝ) : ℂ) * Complex.I) = w at hw
  obtain ⟨hw1, hw2⟩ := max_lt_iff.1 hw
  obtain ⟨s, hs, h, hh⟩ := o4 w hw2
  let gm : (Uw.F.Di Ha.i).La ≃ₗ[𝓞 E] (Uw.F.Di (Uw.ik k)).La := g₁.trans gam.symm
  let L : (Fin Uw.g → ℂ) ≃ₗ[ℂ] (Fin Uw.g → ℂ) := h₁.trans h.symm
  have hgm : ∀ u, gam (gm u) = g₁ u := fun u => gam.apply_symm_apply _
  have hEF : ∀ u v, (Uw.F.Di (Uw.ik k)).EF (gm u) (gm v) = (Uw.F.Di Ha.i).EF u v := fun u v => by
    rw [← o1, hgm, hgm]; exact e4 u v
  have hP : ∀ u, Uw.Pm k ⟨_, hs⟩ (gm u) = L (Ha.Pw w u) := fun u => by
    apply h.injective
    rw [hh, hgm]
    exact (e3 w u).symm.trans (h.apply_symm_apply _).symm
  have hpq : 1 ≤ Dw.p + Dw.q := by
    rw [← hU.1]
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · exact absurd (Subsingleton.elim _ _) hξ.2.2
    · exact hr
  have hty := (GlobalTheory.Relab.relab_good E H l c σ hσ).2.2.2 Dw Uw.g Uw.e
  have hlev : ∀ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La),
      ∃ e, gm (Uw.F.t Ha.i v) = Uw.F.t (Uw.ik k) v + l.M • e := by
    intro v hv
    obtain ⟨q, q1, q2, q3⟩ := Ha.levelM v hv
    have hq : q = Λ.toGtDict.qk l.M (g₁ (Uw.F.t Ha.i v)) := by
      refine TorusExt.qk_ext (q1.trans (e2 _).symm) (q2.trans ?_)
      have h0 : h₁ (Ha.P₀ (Uw.F.t Ha.i v)) = Λ.A.P0 (g₁ (Uw.F.t Ha.i v)) := by
        have := e3 0 (Uw.F.t Ha.i v)
        rw [Ha.Pw_eq, zero_smul, add_zero] at this
        exact this.trans (by rw [AnArc.Pw_apply, zero_smul, add_zero])
      rw [← e1, map_smul, h0]
      rfl
    have l1 : Λ.Lifts (aC.eta v) (g₁ (Uw.F.t Ha.i v)) := fun q' hq' => hq ▸ q3 q' hq'
    obtain ⟨la, hla⟩ := Λ.exists_lifts (aC.eta v)
    obtain ⟨m₁, hm₁⟩ := (hla _).1 l1
    obtain ⟨m₂, hm₂⟩ := (hla _).1 (hL v)
    refine ⟨gam.symm (m₁ - m₂), gam.injective ?_⟩
    rw [hgm, map_add (f := _), map_nsmul, gam.apply_symm_apply, hm₂, nsmul_sub]
    exact hm₁.trans (by abel)
  obtain ⟨p1, p2⟩ := GlobalTheory.ArcCM.point_exp_eq_of_isometry hK E H Dw l Xo _ Uw.g _ Uw.F Ha.i (Uw.ik k) (Ha.Pw w) (Uw.Pm k ⟨_, hs⟩) gm L hpq hσ hty hA
    (Ha.period w hw1) (Uw.period k _) hEF hlev hP
  refine ⟨w, s, hs, L, gm.symm t', t', hw1, fun v' => ?_, o2, ?_, p1, p2⟩
  · rw [← hEF, gm.apply_symm_apply, o3, ← hξC, hgm, ← e2]
    rfl
  · rw [← hP, gm.apply_symm_apply]

end GlobalTheory.ArcCM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicArcMatchesFrameOfModelOnOrbitStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj hiding Unf GoodEmb
open Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphicArc_matches_frame_of_model_on_orbit : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (Uw : UnfWit U) (k : U.Comp) (ξ' : Fin r → E) (x : Frame (U.X k).Ψ r) (aC : ArcIn Dw l (RingHom.id c.F) ℂ σ) (Λ : GtAn₀ aC) (ξC : Module.Dual ℤ aC.D₀.X), GoodEmb c σ → IsUnf U → (U.X k).IsIso ξ' → x ∈ (U.X k).dom → l.A = 1 → letI := H.starRing; ∀ (gam : (Uw.F.Di (Uw.ik k)).La ≃ₗ[𝓞 E] Λ.A.La) (ξ : Module.Dual ℤ Λ.A.X), OnOrbit Uw k ξ' x Λ.A gam ξ → (∀ y, ξC (Λ.eX y) = ξ y) → (∀ v, Λ.Lifts (aC.eta v) (gam (Uw.F.t (Uw.ik k) v))) → ∀ (O : Type) [CommRing O] (β : O →+* c.F), TieC Uw (aC.restrict β) ξC k ξ' x := by
  first | exact @GlobalTheory.ArcCM.tieC_of_onOrbit | exact GlobalTheory.ArcCM.tieC_of_onOrbit | (intros; apply GlobalTheory.ArcCM.tieC_of_onOrbit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NormalisedTrivialisationNormOneComplexReading
section -- merged from Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.NonemptyOfFrameValues
noncomputable section
namespace GlobalTheory.ArcDictModel
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HostModel

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l)
  (bF : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ]

end

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {c : Coeff l}
  {O : Type} [CommRing O] {β : O →+* c.F} [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ]
  {b : O →+* ℂ} {a : ArcIn D l β ℂ b} (Λ : GtAn₀ a)

end

section Bridge
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {c : Coeff l}
  {O : Type} [CommRing O] {β : O →+* c.F} [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ]
  {b : O →+* ℂ} {a : ArcIn D l β ℂ b}

theorem nonempty_of_frameValues (Λ : letI := H.starRing; ArcPts.GtAn a) : Nonempty (GtAn a) := by
  letI := H.starRing
  have h := fun (j : ℕ) (hj : NeZero j) (α : Λ.A.X) =>
    TwistedTheta.sections_equiv_anArc_theta Λ.A a.D₀ Λ.u _ Λ.lam (fun _ _ e => congrArg Λ.A.chi (Subtype.ext e)) Λ.ah j
      (Nat.one_le_iff_ne_zero.2 hj.out) (fun θ hθ => ((Λ.pow j).2 θ hθ).exists) (Λ.ε α) α (Λ.ct α)
  choose e _ he using h
  refine ⟨⟨⟨GtAnModel.toDict Λ, fun x y => (Λ.be_eq x y).symm⟩, ⟨fun j hj α => (e j hj α).toEquiv, ?_⟩⟩⟩
  intro j hj α s z i hi
  refine (he j hj α s z i hi).trans (congrArg (_ * ·) ?_)
  refine Eq.trans ?_ (Fin.prod_univ_four _).symm
  exact congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) rfl (zpow_one _).symm) (zpow_neg_one _).symm)
    (zpow_one _).symm

end Bridge

section Determined
variable {O : Type} [CommRing O] [StarRing O] [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ]
  {D₀ : Out.DegPre ℂ} [Module O D₀.X] {oa : D₀.OAct O} (d : GtDict D₀ oa)

end Determined

end GlobalTheory.ArcDictModel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NormalisedTrivialisationNormOneComplexReading
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj hiding Unf GoodEmb
open Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.ArcNormOne

section An

variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)

theorem map_real_eq_zero (φ : A.V →ₗ[ℝ] ℝ) (w : ℂ) (h : ∀ n, φ (A.Pw w (AnArc.La.mk 0 n 0)) = 0)
    (r : A.X →+ ℂ) (hr : ∀ x, (r x).im = 0) : φ (r, 0) = 0 := by
  classical
  let b := Module.Free.chooseBasis ℤ A.X
  have e : ((r, 0) : A.V) =
      ∑ i, (r (b i)).re • A.Pw w (AnArc.La.mk 0 (b.coord i).toAddMonoidHom 0) := by
    refine Prod.ext (AddMonoidHom.ext fun x => ?_) ?_
    · rw [Prod.fst_sum, AddMonoidHom.finsetSum_apply]
      conv_lhs => rw [← b.sum_repr x]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_zsmul]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h1 : r (b i) = ((r (b i)).re : ℂ) := Complex.ext (by simp) (by simp [hr])
      change _ = (r (b i)).re • (A.Pw w (AnArc.La.mk 0 (b.coord i).toAddMonoidHom 0)).1 x
      rw [AnArc.Pw_fst_apply, Complex.real_smul, ← h1]
      simp [mul_comm]
    · rw [Prod.snd_sum]
      simp
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, map_sum]
  simp [h]

def abLift : (Fin A.gB → ℂ) →ₗ[ℝ] A.V where
  toFun z :=
    ({ toFun := fun x => -(A.H (A.ct x) z / (2 * Complex.I))
       map_zero' := by simp
       map_add' := fun x x' => by simp only [map_add (f := _), AnArc.H_add_left]; ring }, z)
  map_add' z z' := by
    refine Prod.ext (AddMonoidHom.ext fun x => ?_) rfl
    change -(A.H (A.ct x) (z + z') / (2 * Complex.I)) =
      -(A.H (A.ct x) z / (2 * Complex.I)) + -(A.H (A.ct x) z' / (2 * Complex.I))
    rw [AnArc.H_add_right]; ring
  map_smul' t z := by
    refine Prod.ext (AddMonoidHom.ext fun x => ?_) rfl
    change -(A.H (A.ct x) (t • z) / (2 * Complex.I)) = t • -(A.H (A.ct x) z / (2 * Complex.I))
    rw [← Complex.coe_smul, AnArc.H_smul_right, Complex.conj_ofReal, Complex.real_smul]; ring

theorem map_abLift_eq_zero (φ : A.V →ₗ[ℝ] ℝ) (w : ℂ) (h : ∀ m, φ (A.Pw w (AnArc.La.mk 0 0 m)) = 0)
    (z : Fin A.gB → ℂ) : φ (abLift A z) = 0 := by
  have e : φ ∘ₗ abLift A = 0 := by
    refine LinearMap.ext_on A.full fun m hm => ?_
    rw [LinearMap.zero_apply, ← h ⟨m, hm⟩, LinearMap.comp_apply]
    congr 1
    refine Prod.ext (AddMonoidHom.ext fun x => ?_) (by simp [abLift])
    rw [AnArc.Pw_fst_apply]
    simp [abLift]
  exact LinearMap.congr_fun e z

theorem map_I_smul_N (φ : A.V →ₗ[ℝ] ℝ) (w : ℂ) (v : A.La) (h : ∀ la, φ (A.Pw w la) = -(A.be v.y la.y : ℝ))
    (hn : ∀ x, (A.T v.y x).im = (A.H (A.ct v.y) (A.ct x)).re / 2) :
    φ (Complex.I • A.N v) * w.im = -(A.be v.y v.y : ℝ) := by
  set u : A.V := A.Pw w (AnArc.La.mk v.y 0 0) - abLift A (A.ct v.y) - w.im • Complex.I • A.N v with hu
  have hN : (A.N v).2 = 0 := rfl
  have h2 : u = (u.1, 0) := Prod.ext rfl (by simp [hu, abLift, hN])
  have h3 : φ u = 0 := by
    rw [h2]
    refine map_real_eq_zero A φ w (fun n => by simp [h]) _ fun x => ?_
    change ((A.Pw w (AnArc.La.mk v.y 0 0)).1 x - -(A.H (A.ct x) (A.ct v.y) / (2 * Complex.I)) -
      w.im • Complex.I • (A.N v).1 x).im = 0
    have h4 : A.H (A.ct x) (A.ct v.y) / (2 * Complex.I) = -Complex.I * A.H (A.ct x) (A.ct v.y) / 2 := by
      field_simp
      simp
    have h5 : (A.H (A.ct x) (A.ct v.y)).re = (A.H (A.ct v.y) (A.ct x)).re := by
      rw [← A.H_conj, Complex.conj_re]
    rw [h4, AnArc.Pw_fst_apply, AnArc.N_fst_apply]
    simp [hn, h5]
    ring
  rw [hu, map_sub, map_sub, map_smul, h, map_abLift_eq_zero A φ w (fun m => by simp [h])] at h3
  simp only [AnArc.La.mk_y, smul_eq_mul] at h3
  linarith

theorem im_T_eq {n : ℕ} (hn : 0 < n) (y x : A.X)
    (h : eTwoPi (A.T (n • y) (n • x)) * Complex.exp (Real.pi * A.H (n • A.ct y) (n • A.ct x)) = 1) :
    (A.T y x).im = (A.H (A.ct y) (A.ct x)).re / 2 := by
  rw [eTwoPi, ← Complex.exp_add] at h
  have h1 := congrArg norm h
  rw [Complex.norm_exp, norm_one, Real.exp_eq_one_iff, ← Nat.cast_smul_eq_nsmul ℂ n (A.ct y),
    ← Nat.cast_smul_eq_nsmul ℂ n (A.ct x), AnArc.H_smul_left, AnArc.H_smul_right] at h1
  simp only [map_nsmul, AddMonoidHom.nsmul_apply, nsmul_eq_mul] at h1
  simp at h1
  have h2 : (Real.pi * n * n) * ((A.H (A.ct y) (A.ct x)).re - 2 * (A.T y x).im) = 0 := by linarith
  have h3 : (Real.pi * n * n) ≠ 0 := by positivity
  have := (mul_eq_zero.1 h2).resolve_left h3
  linarith

end An

def imForm {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z₀ : Fin g → ℂ) : (Fin g → ℂ) →ₗ[ℝ] ℝ where
  toFun z := (hermForm Hm z₀ z).im
  map_add' z z' := by simp [hermForm, Matrix.mulVec_add, dotProduct_add]
  map_smul' t z := by simp [hermForm, Matrix.mulVec_smul, dotProduct_smul]

theorem imForm_I_smul {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z₀ z : Fin g → ℂ) :
    imForm Hm z₀ (Complex.I • z) = -(hermForm Hm z₀ z).re := by
  simp [imForm, hermForm, Matrix.mulVec_smul, dotProduct_smul, Matrix.mulVec_neg]

theorem normOne_of_tauCan : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (σ : c.F →+* ℂ) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) (n : ℕ), 0 < n → TauCan a.D₀ n → NormOne Ha := by
  intro K E _ _ _ H Dw l Xo c _ _ σ O _ β Y a χ W g ty Fu Ha n hn htau w _ Hm hH v
  letI := H.starRing
  obtain ⟨Λ'⟩ := GlobalTheory.ArcModel.nonempty_gtAn K.laws K.laws2 K.theta E H Dw l c O β _ a
  obtain ⟨Λ''⟩ := GlobalTheory.ArcDictModel.nonempty_of_frameValues Λ'
  let Λ := Λ''.toGtAn₀
  obtain ⟨gam, h, -, hy, hP, hE⟩ := GlobalTheory.T.holomorphicArc_agrees_analyticDictionary K E H Dw l Xo c σ O β Y a χ W g ty Fu Ha Λ
  have hN := ((GlobalTheory.T.isTauCanonicalTrivialisation_iff_normalised_arc E H Dw l c O β _ a Λ n).1 htau).2
  have hNv : h (Ha.N v) = Λ.A.N (gam v) := by
    have h0 := hP 0 v
    have h1 := hP 1 v
    rw [Ha.Pw_eq, AnArc.Pw_apply] at h0 h1
    simp only [zero_smul, add_zero, one_smul, map_add (f := _)] at h0 h1
    rw [h0] at h1
    exact add_left_cancel h1
  have hNP : Ha.N v = Ha.Pw w (gam.symm (Λ.A.nn (gam v))) := by
    apply h.injective
    rw [hNv, hP, LinearEquiv.apply_symm_apply, Λ.A.degeneratingTori_periodMap_eq_base_of_y_eq_zero w rfl, AnArc.degeneratingTori_basePeriodMap_nilpotentMap]
  have key := map_I_smul_N Λ.A (imForm Hm (Ha.N v) ∘ₗ (h.symm.toLinearMap.restrictScalars ℝ)) w (gam v)
    (fun la => by
      obtain ⟨v', rfl⟩ := gam.surjective la
      change (hermForm Hm (Ha.N v) (h.symm (Λ.A.Pw w (gam v')))).im = _
      rw [← hP, LinearEquiv.symm_apply_apply, hNP, hH.2.2, ← hE, LinearEquiv.apply_symm_apply, AnArc.nn_apply,
        AnArc.EF_n_left]
      simp)
    (fun x => im_T_eq Λ.A hn _ _ (hN _ _))
  change imForm Hm (Ha.N v) (h.symm (Complex.I • Λ.A.N (gam v))) * w.im = _ at key
  rw [← hNv, ← map_smul, LinearEquiv.symm_apply_apply, imForm_I_smul, ← Λ.be_eq, ← Λ.y_apply, hy] at key
  linarith

end GlobalTheory.ArcNormOne
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NormalisedTrivialisationNormOneComplexReadingStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj hiding Unf GoodEmb
open Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalisedTrivialisation_normOne_complexReading : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (σ : c.F →+* ℂ) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) (n : ℕ), 0 < n → TauCan a.D₀ n → NormOne Ha := by
  first | exact @GlobalTheory.ArcNormOne.normOne_of_tauCan | exact GlobalTheory.ArcNormOne.normOne_of_tauCan | (intros; apply GlobalTheory.ArcNormOne.normOne_of_tauCan <;> assumption)
end
end
