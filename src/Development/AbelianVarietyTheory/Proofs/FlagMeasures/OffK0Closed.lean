module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TheoremSConclusion
public import Formalism.LocalToGlobal.SiegelLatticeTheory.WeightedGaugeFactors.FactsCC
public import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.MultiplicityOneUnitaryBranchingOfGapHyp
public import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.RealObjInInfinityXJsz
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LinkSFinalP
public import Formalism.LocalToGlobal.SiegelLatticeTheory.WeightedGaugeFactors.FactsFD
public import Formalism.LocalToGlobal.SiegelLatticeTheory.WeightedGaugeFactors.FactsGV
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermRepUnram
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.KFinDenseMain
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RhsWLimOfLeaves
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSETopFinal
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TransferSmoothAtBuiltPlace
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PolyTopOf
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BoundOnEarlierRegion
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GermRateLowerBound
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ThresholdsPositive
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftLocalBuiltPlaces

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.MinorCellOfPartsAlt
open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.Qx5 Formalism.FourierDecayAlt.P.Qx2 Formalism.FourierDecayAlt.P.PBN Formalism.FourierDecayAlt.P.PBN.MC

theorem minor_cell_of_parts : PBN.MinorCellOfParts := by
  intro hRR hLR hTC hGP k r Wp Wq _ _ _ _ _ _ Bs F y hF x hx
  set D := OmPlus k r Bs.z Bs.z' with hDdef
  have hD : IsOpen D := Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet.isOpen_OmPlus Bs.z Bs.z'
  obtain ⟨ε, hε, hn⟩ := Formalism.FourierDecayAlt.P.TLB.nice_of_cpt hF
  obtain ⟨hf, hLf, hRf, -⟩ := Formalism.FourierDecayAlt.P.bessel_function_finite_class k r Wp Wq Bs F ε hε hn
  have h1N : (1 : Mx k r) ∈ Nlev k r 0 :=
    ⟨(Formalism.QuantumDeterminants.unipotent_subgroup_holds k r).1, by simp [Glev, UH]⟩
  have hN : ∀ g ∈ Glev k r 0 ∩ D, ∀ n ∈ Nlev k r 0, n * g ∈ D := by
    intro g hg n hn
    have hDom := Formalism.FourierDecayAlt.P.JCx2.rma_isDom_omPlus (k := k) (r := r) Bs.z_mem Bs.z'_mem
    have := hDom.2 g hg n ⟨1, Formalism.FourierDecayAlt.P.Qx8.uw_one Bs.z, n, hn, (one_mul n).symm⟩ 1
      ⟨1, Formalism.FourierDecayAlt.P.Qx8.uw_one Bs.z', 1, h1N, (one_mul 1).symm⟩
    rwa [Matrix.mul_one] at this
  set v₀ : VS k r 0 D (Wq →L[ℂ] Wp) := ⟨cut k r 0 D (B.JF Bs F), cut_mem hD hf⟩ with hv₀
  have hcellB : ∀ c ∈ OmX r, wCell k r (Fin.last r) c * x.2 ∈ C6.bigPos Bs := fun c hc =>
    (Formalism.FourierDecayAlt.P.big_cell_values k r Wp Wq Bs (c, x.2) ⟨hc, hx.2.1, hx.2.2⟩).1
  have hcell : ∀ c ∈ OmX r, wCell k r (Fin.last r) c * x.2 ∈ Glev k r 0 ∩ D := by
    intro c hc
    have h := hcellB c hc
    exact ⟨Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 h.1, fun l _ => h.2.2 l (by simp), h.2.1⟩
  have hdiff : ∀ x' : SA (E := Wq →L[ℂ] Wp) hD, ∀ c ∈ OmX r, DifferentiableAt ℝ
      (fun c' => ((x' : Module.End ℂ (VS k r 0 D (Wq →L[ℂ] Wp))) v₀ : Mx k r → (Wq →L[ℂ] Wp))
        (wCell k r (Fin.last r) c' * x.2)) c :=
    fun x' c hc => cell_diff Bs ((x' : Module.End ℂ (VS k r 0 D (Wq →L[ℂ] Wp))) v₀).2.1 hx.2.1 hx.2.2 hc
  have hWS : ∀ x' : SA (E := Wq →L[ℂ] Wp) hD,
      resW ((x' : Module.End ℂ (VS k r 0 D (Wq →L[ℂ] Wp))) v₀ : Mx k r → (Wq →L[ℂ] Wp)) x.2 ∈ WSm r (Wq →L[ℂ] Wp) :=
    fun x' => resG_wsm Bs ((x' : Module.End ℂ (VS k r 0 D (Wq →L[ℂ] Wp))) v₀).2.1 hx.2.1 hx.2.2
  have hcl := claim hD v₀ x.2 y hRR hLR hTC hGP Bs.z Bs.z' Bs.z_mem Bs.z'_mem hN hf hLf hRf rfl hx.2.1 hcell hdiff hWS
    r le_rfl 1 (Subalgebra.one_mem _) x.1 hx.1
  rw [mul_one] at hcl

  have eR : Q.crd (Q.vAB r y r).1 (Q.resG k r (Fin.last r) (B.JF Bs F)) x.1 x.2 =
      (Q.vAB r y r).1 (fun c' => Q.resG k r (Fin.last r)
        (((1 : SA (E := Wq →L[ℂ] Wp) hD) : Module.End ℂ (VS k r 0 D (Wq →L[ℂ] Wp))) v₀ : Mx k r → (Wq →L[ℂ] Wp)) c' x.2) x.1 := by
    have hloc : ∀ (i : ℕ) (f₁ f₂ : (Fin r → ℂ) → (Wq →L[ℂ] Wp)),
        (∀ c ∈ OmX r, f₁ c = f₂ c) → ∀ c ∈ OmX r,
        (Q.vAB r y i).1 f₁ c = (Q.vAB r y i).1 f₂ c ∧
        (Q.vAB r y i).2 f₁ c = (Q.vAB r y i).2 f₂ c := by
      intro i
      induction i with
      | zero => intro f₁ f₂ h c hc; exact ⟨h c hc, rfl⟩
      | succ i ih =>
        intro f₁ f₂ h c hc
        have hih := ih f₁ f₂ h
        by_cases hi : i < r
        · simp only [Q.vAB, dif_pos hi]
          refine ⟨?_, ?_⟩
          · simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, cOp]
            have hev : (Q.vAB r y i).1 f₁ =ᶠ[nhds c] (Q.vAB r y i).1 f₂ := by
              filter_upwards [(Formalism.FourierDecayAlt.P.Qx3.isOpen_OmX r).mem_nhds hc] with c' hc' using (hih c' hc').1
            simp only [pOp, wirt, if_pos hc, hev.fderiv_eq, (hih c hc).1, (hih c hc).2]
          · simp only [ciOp, (hih c hc).1]
        · simp only [Q.vAB, dif_neg hi]
          exact hih c hc
    refine (hloc r _ _ (fun c' hc' => ?_) x.1 hx.1).1
    rw [resG_last, resG_last]
    congr 1
    exact (cut_of_mem _ (hcell c' hc')).symm
  rw [eR, ← hcl, resG_last, resG_last]
  congr 1

  have hγ := hcell x.1 hx.1
  have e1 : ((qminor (EA (E := Wq →L[ℂ] Wp) hD) (C3.xR k r r le_rfl) (C3.xR k r r le_rfl)
      (y + ((2 * r + k : ℕ) : ℂ) / 2) : SA (E := Wq →L[ℂ] Wp) hD) : Module.End ℂ (VS k r 0 D (Wq →L[ℂ] Wp))) =
      qminor (Eh (E := Wq →L[ℂ] Wp) (i := 0) hD) (cI ∘ C3.xR k r r le_rfl) (cI ∘ C3.xR k r r le_rfl)
        (y + ((2 * r + k : ℕ) : ℂ) / 2) := by
    have := map_qminor (SA (E := Wq →L[ℂ] Wp) hD).val (EA hD) (C3.xR k r r le_rfl) (C3.xR k r r le_rfl)
      (y + ((2 * r + k : ℕ) : ℂ) / 2)
    rw [Subalgebra.coe_val] at this
    rw [this]
    exact qminor_reindex (Eh hD) cI cI_inj _ _ _
  rw [e1, rep_qminor hD _ _ _ v₀ _ hγ]
  have hpos : posL k r 0 ∘ (cI ∘ C3.xR k r r le_rfl) = C3.xR k r r le_rfl := funext fun l => posL_cI _
  have hloc := (good_qminor (E := Wq →L[ℂ] Wp) hD (cI ∘ C3.xR k r r le_rfl) (cI ∘ C3.xR k r r le_rfl)
    (y + ((2 * r + k : ℕ) : ℂ) / 2)).loc (cut k r 0 D (B.JF Bs F)) (B.JF Bs F) (fun x' hx' => cut_of_mem _ hx')
    _ hγ
  rw [hpos] at hloc
  rw [hpos]
  exact hloc.symm

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.GaugeNormPower
open MeasureTheory Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBN

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.R

def lstN (K m : ℕ) (y : Fin K → ℝ) : List ℝ :=
  List.ofFn fun b : Fin m => if hb : m - 1 - b < K then y ⟨m - 1 - b, hb⟩ else 0

theorem lstN_succ (K : ℕ) (a : Fin K) (y : Fin K → ℝ) (t : ℝ) :
    lstN K ((a : ℕ) + 1) (Function.update y a t) = t :: lstN K a y := by
  unfold lstN
  rw [List.ofFn_succ]
  congr 1
  · rw [dite_eq_left (by omega)]
    have e : (⟨(a : ℕ) + 1 - 1 - ((0 : Fin ((a : ℕ) + 1)) : ℕ), by omega⟩ : Fin K) = a := Fin.ext (by simp)
    rw [e, Function.update_self]
  · congr 1
    funext i
    have hi := i.isLt
    rw [dite_eq_left (by simp; omega), dite_eq_left (by omega)]
    have e : (⟨(a : ℕ) + 1 - 1 - (i.succ : ℕ), by simp; omega⟩ : Fin K) = ⟨(a : ℕ) - 1 - i, by omega⟩ :=
      Fin.ext (by simp; omega)
    rw [e, Function.update_of_ne]
    intro h'
    have := congrArg Fin.val h'
    simp at this
    omega

theorem lstN_full (K : ℕ) (z : Fin K → ℝ) : lstN K K z = List.ofFn fun b => z (Fin.rev b) := by
  unfold lstN
  congr 1
  funext b
  rw [dite_eq_left (by omega)]
  congr 1
  ext
  simp [Fin.val_rev]
  omega

theorem cutWord_plusW {P : M.Par} {l0 : ℕ} {w : List C.Letter} :
    ∀ ys : List ℝ, KB.CutWord P l0 (KB.plusW ys w) → KB.CutWord P l0 w
  | [], h => h
  | _ :: ys, h => cutWord_plusW ys (cutWord_tail h)

section deg

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def aaIter {k r : ℕ} (Bs : B.RealPlaceData k r Wp Wq) (F0 : B.Mat k r → (Wq →L[ℂ] Wp)) :
    List ℝ → B.Mat k r → (Wq →L[ℂ] Wp)
  | [] => F0
  | y :: ys => aaTop Bs y (aaIter Bs F0 ys)

def aPIter {V : Type} [AddCommGroup V] [Module ℂ V] {r : ℕ} (L : R.LevelData (Q.Pr V) r) : List ℝ → V → V
  | [], Ψ => Ψ
  | y :: ys, Ψ => (TL.aP L (y : ℂ)).1 (aPIter L ys Ψ)

theorem aaIter_rad (hRA : RadAATop) (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) P.r)
    (st : Fr.Start (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))) (l0 : ℕ)
    (hD : P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0) {F0 : B.Mat P.k P.r → (Wq →L[ℂ] Wp)}
    (hF0 : KB.CptCoef Bs F0) {Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'} (hΨ : Top.IsRadOf P Bs Ψ F0) :
    ∀ ys : List ℝ, KB.CptCoef Bs (aaIter Bs F0 ys) ∧ Top.IsRadOf P Bs (aPIter L ys Ψ) (aaIter Bs F0 ys) := by
  intro ys
  induction ys with
  | nil => exact ⟨hF0, hΨ⟩
  | cons y ys ih =>
    obtain ⟨h1, h2⟩ := ih
    obtain ⟨h3, h4⟩ := hRA Wp Wq P Bs X μ L st l0 y hD _ h1
    exact ⟨h3, h4 _ h2⟩

theorem rad_plusW (hWS : TL.WordStep) (P : M.Par) (p : KB.Pl P Wp Wq)
    (X : Q.ActualOps P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Q.Pr (Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π')) P.r)
    (st : Fr.Start (Q.Pr (Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π')))
    (hD : P5.IsData P p.T.base.z p.T.base.z' p.T.base.π p.T.base.π' X μ L st p.l0) (w : List C.Letter)
    (Φ : Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π') (e : Ix (Fin w.length)) :
    ∀ ys : List ℝ, KB.CutWord P p.l0 (KB.plusW ys w) →
      P5.act ((Fr.ofWord L st (D.positionted (KB.plusW ys w))).F * P5.bTall L (D.positionted (KB.plusW ys w)))
          (Top.firstStateVector Φ) (KB.firstSt ys e) =
        aPIter L ys (P5.act ((Fr.ofWord L st (D.positionted w)).F * P5.bTall L (D.positionted w)) (Top.firstStateVector Φ) e) := by
  intro ys
  induction ys with
  | nil => intro; rfl
  | cons y ys ih =>
    intro hc
    have h1 := rad_plus hWS P p X μ L st hD (KB.plusW ys w) y hc Φ (KB.firstSt ys e)
    exact h1.trans (congrArg (fun Ψ => (TL.aP L (y : ℂ)).1 Ψ) (ih (cutWord_tail hc)))

end deg

end Formalism.FourierDecayAlt.P.PBN

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.PBN

theorem degree_top_of_parts : PBN.DegTopOfParts := by
  intro hWS hRA hPT hDC Wp Wq _ _ _ _ _ _ P p F s w h t K grid e Cb hCb hs hloc hF hgrid hcut
  obtain ⟨X, μ, L, st, hD, hTL⟩ := p.hΘ
  have hcw : KB.CutWord P p.l0 w := cutWord_plusW _ (hcut fun _ => 0)
  obtain ⟨F0, hF0, hF0eq, hV0⟩ := Formalism.FourierDecayAlt.P.theta_compact_support Wp Wq P p F w e Cb hCb hF hcw
  obtain ⟨Φ, hΦ⟩ := radExists p hF
  have hΨ := isRadOf_congr p.T.base (hTL w hcw F hF Φ hΦ e) hF0eq
  have hIt := aaIter_rad hRA P p.T.base X μ L st p.l0 hD hF0 hΨ

  have hVit : ∀ ys : List ℝ, KB.CutWord P p.l0 (KB.plusW ys w) →
      p.V (aaIter p.T.base F0 ys) (h ++ [(s, t)]) =
        p.V (p.Θ.Θ (KB.plusW ys w) (KB.firstSt ys e) F) (h ++ [(s, t)]) := by
    intro ys hc
    obtain ⟨Fn, hFn, hFneq, hVn⟩ := Formalism.FourierDecayAlt.P.theta_compact_support Wp Wq P p F (KB.plusW ys w) (KB.firstSt ys e) Cb hCb hF hc
    rw [hVn]
    have hrad := isRadOf_congr p.T.base (hTL (KB.plusW ys w) hc F hF Φ hΦ (KB.firstSt ys e)) hFneq
    rw [rad_plusW hWS P p X μ L st hD w Φ e ys hc] at hrad
    exact vecV_eq_of_rad hDC p (hIt ys).1 hFn (hIt ys).2 hrad _
  set W : ℕ → (Fin K → ℝ) → (Wq →L[ℂ] Wp) := fun m y => p.V (aaIter p.T.base F0 (lstN K m y)) (h ++ [(s, t)])
    with hW
  have hPS : F7.PolyStep K (D.ptSize h) (fun _ => ((-1) ^ (s - 1) / t : ℂ)) W := by
    intro a y
    obtain ⟨c, hc, hpoly⟩ := hPT Wp Wq P p (aaIter p.T.base F0 (lstN K a y)) s h t hs hloc (hIt _).1
    refine ⟨c, hc, fun t' => ?_⟩
    simp only [hW]
    rw [lstN_succ]
    exact hpoly t'
  have hinj : ∀ a, Function.Injective (fun i => grid (Fin.rev a) i) := fun a => hgrid _
  have hE := Formalism.FourierDecayAlt.P.extract_K_bound (Wq →L[ℂ] Wp) K (D.ptSize h) (fun _ => ((-1) ^ (s - 1) / t : ℂ)) W
    (fun a => grid (Fin.rev a)) hPS hinj (fun _ => 0)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hE
  have hW0 : W 0 (fun _ => 0) = p.V (p.Θ.Θ w e F) (h ++ [(s, t)]) := by
    simp only [hW, lstN, List.ofFn_zero, aaIter]
    rw [hV0]
  rw [hW0] at hE
  rw [hE]
  refine Fintype.sum_equiv ((Fin.revPerm).arrowCongr (Equiv.refl _)) _ _ (fun n => ?_)
  simp only [hW]
  rw [lstN_full]
  have e1 : (fun b : Fin K => grid (Fin.rev (Fin.rev b)) (n (Fin.rev b))) =
      fun b => grid b ((Fin.revPerm.arrowCongr (Equiv.refl (Fin (D.ptSize h + 1)))) n b) := by
    funext b
    simp [Equiv.arrowCongr_apply, Fin.revPerm]
  have e2 : (∏ a : Fin K, F7.lagCo (grid (Fin.rev a)) (n a)) =
      ∏ a : Fin K, F7.lagCo (grid a) ((Fin.revPerm.arrowCongr (Equiv.refl (Fin (D.ptSize h + 1)))) n a) := by
    refine Fintype.prod_equiv Fin.revPerm _ _ (fun a => ?_)
    simp [Equiv.arrowCongr_apply, Fin.revPerm]
  rw [e1, e2, hVit _ (hcut _)]

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.PbTopFirstOf
namespace Formalism.FourierDecayAlt.P

theorem pb_degTop_of (hRA : PBN.RadAATop) (hPT : PBN.PolyTop) : Formalism.FourierDecayAlt.KB.DegTop :=
  degree_top_of_parts word_recursion hRA hPT density_constant

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.PbDegTopOfPolyTop
namespace Formalism.FourierDecayAlt.P

theorem minor_cell : PBN.MinorCell :=
  minor_cell_of_parts right_rule_derivative left_rule_cell torus_cell gauge_positivity

theorem radial_raising_top : PBN.RadAATop :=
  radial_raising_top_of_parts jacquet_raising_operator raising_cell minor_cell radial_side_raising raising_compact_support

theorem pb_degTop_of_polyTop (hPT : PBN.PolyTop) : Formalism.FourierDecayAlt.KB.DegTop := pb_degTop_of radial_raising_top hPT

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.RaisingLoweringRelations
noncomputable section

namespace Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

theorem raising_lowering_relations : KrAA := by
  intro k r Wp Wq _ _ _ _ _ _ Bs F hF u x hx
  obtain ⟨hs, ⟨R, hR⟩, -⟩ := hF
  exact (PBG.kr_AA_cpt Bs hs (Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le k r R)
    (fun g hg hgC => by
      by_contra hne
      exact hgC (hR g hg hne)) r le_rfl u 0 hx).1

end Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral

namespace Formalism.FourierDecayAlt.P

theorem polynomial_top : PBN.PolyTop := VandermondePolynomialIntegral.polyTop_of VandermondePolynomialIntegral.raising_lowering_relations

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.DegreeTop
namespace Formalism.FourierDecayAlt.P

theorem degree_top : Formalism.FourierDecayAlt.KB.DegTop := pb_degTop_of_polyTop polynomial_top

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.BlockKWaveC
namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

section C2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
  {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
  {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}

theorem blockK_waveC (hA : P5.ThmPActualCpt) (hPSC : StandardPairingDecay.PStdC) (hDW : KB.DegWave) (hSS : KB.SizeStdCpt)
    (hVI : KB.VIsoCpt) (hFP : FormPosCpt) (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (hF : ∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) (v : Fin S.f) (ε : ℝ) (hε : 0 < ε) (j : ℕ)
    (hj : j ≤ S.G.r) (a : List C.Letter) (ha : D.AdmAt S v a) (haN : a.length ≤ S.Ntop)
    (hwa : KB.CutWord (D.parOf S v) (S.l + 1) a) (K : ℕ) (grid : Fin K → Fin (2 * j + 1) → ℝ)
    (hinj : ∀ b, Function.Injective (grid b))
    (hnodes : ∀ n : Fin K → Fin (2 * j + 1),
        D.AdmAt S v (KB.plusW (List.ofFn fun b => grid b (n b)) a) ∧
        D.AdmAt S v (KB.minusW (List.ofFn fun b => grid b (n b)) a) ∧
        KB.CutWord (D.parOf S v) (S.l + 1) (KB.plusW (List.ofFn fun b => grid b (n b)) a) ∧
        KB.CutWord (D.parOf S v) (S.l + 1) (KB.minusW (List.ofFn fun b => grid b (n b)) a) ∧
        (List.ofFn fun b => grid b (n b)).Pairwise (fun y y' => 2 < |y - y'|) ∧
        ∀ y ∈ (List.ofFn fun b => grid b (n b)), NodeOK S v a (decide (j = 0)) y)
    (Xc : ℝ) (hXc0 : 0 ≤ Xc)
    (hXc : (∏ b, ∑ i, |F7.lagCo (grid b) i|) * (((S.g : ℝ) * lamS S j) / (2 * Real.pi)) ^ K *
      (Real.exp 1 * J.supA S.G S.de S.de' S.T S.T' S.l (decide (j = 0)) (S.pl v)) ^ K ≤ Xc ^ K)
    (l : ℂ) (Y : Finset C.LPt) (hY : ∀ h ∈ Y, D.ptSize h = j) :
    KB.BlockPSD Y Y
      (fun p' q' => ((Xc ^ K : ℝ) : ℂ) * ∑ n : Fin K → Fin (2 * j + 1), (F7.thGrid grid n : ℂ) *
        KB.gN (setC S p F) v ε j (KB.plusW (List.ofFn fun b => grid b (n b)) a) p' q')
      (fun p' q' => Complex.I ^ K * l ^ K * KB.hatB (setC S p F) v ε (j + 1) 1 a l p' q')
      (fun p' q' => ((Xc ^ K : ℝ) : ℂ) * ∑ n : Fin K → Fin (2 * j + 1), (F7.thGrid grid n : ℂ) *
        KB.gN (setC S p F) v ε j (KB.minusW (List.ofFn fun b => grid b (n b)) a) p' q') := by
  have hB' := hB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hGo, -, -, -, -, hv⟩ := hB'
  obtain ⟨hl0, -, -, -, -⟩ := hv v
  have hgpos := g_pos_of_built hB
  have hlam := lamS_pos S hgpos j
  have hΓ := gam_pos hB j
  have hsa := sizeAt_pos S hGo v a ha
  set T : ℝ := ((S.g : ℝ) * lamS S j) / (2 * Real.pi) with hT
  have hT0 : 0 < T := by positivity
  set t : ℝ := 2 * Real.pi / ((S.g : ℝ) * lamS S j) with ht
  have htT : t * T = 1 := by rw [ht, hT]; field_simp
  set s := sW S j l with hs
  set c0 : ℝ := 1 / (ΓS S j * S.sizeAt v a) with hc0
  set ys : (Fin K → Fin (2 * j + 1)) → List ℝ := fun n => List.ofFn fun b => grid b (n b) with hys
  set Λ : ℝ := ∏ b, ∑ i, |F7.lagCo (grid b) i| with hΛ
  set θ : (Fin K → Fin (2 * j + 1)) → ℝ := fun n => F7.thGrid grid n with hθ
  set lag : (Fin K → Fin (2 * j + 1)) → ℝ := fun n => ∏ b, F7.lagCo (grid b) (n b) with hlag
  set S' := setC S p F with hS'

  set Pn : (Fin K → Fin (2 * j + 1)) → C.LPt → C.LPt → ℂ := fun n p' q' =>
    (((lag n / θ n) * T ^ K * c0 : ℝ) : ℂ) * KB.pairJ ((p v).form j hj a) (ys n)
      (KB.waveG ((p v).T.bs j) s _ (uY S p F v ε j hj (KB.plusW (ys n) a) Y p'))
      (uY S p F v ε j hj (KB.minusW (ys n) a) Y q') with hPn
  have hCS : ∀ n (c d : C.LPt → ℂ), ‖∑ p' ∈ Y, ∑ q' ∈ Y, c p' * conj (d q') * Pn n p' q'‖ ^ 2 ≤
      (Xc ^ K) ^ 2 * ((∑ p' ∈ Y, ∑ p'' ∈ Y, c p' * conj (c p'') * KB.gN S' v ε j (KB.plusW (ys n) a) p' p'').re *
        (∑ q' ∈ Y, ∑ q'' ∈ Y, d q' * conj (d q'') * KB.gN S' v ε j (KB.minusW (ys n) a) q' q'').re) := by
    intro n c d
    obtain ⟨hAp, hAm, hCp, hCm, hpw, hnd⟩ := hnodes n
    have hCp' : KB.CutWord (D.parOf S v) (p v).l0 (KB.plusW (ys n) a) := by rw [hl0]; exact hCp
    have hCm' : KB.CutWord (D.parOf S v) (p v).l0 (KB.minusW (ys n) a) := by rw [hl0]; exact hCm
    obtain ⟨hqpos, hcs⟩ := hSS hA (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (p v) j hj a (ys n) hCp' hCm' hpw
    set qv : ℝ → ℝ := fun y => (Wd.qw (M.qC (D.parOf S v)) (D.positionted a) (y : ℂ)).re with hqv
    set Q : ℝ := ((ys n).map qv).prod with hQd
    have hQ : 0 < Q := List.prod_pos fun x hx => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      exact hqpos y hy
    have hsp := sizeAt_pos S hGo v _ hAp
    have hsm := sizeAt_pos S hGo v _ hAm
    set cp : ℝ := 1 / (ΓS S j * S.sizeAt v (KB.plusW (ys n) a)) with hcp
    set cm : ℝ := 1 / (ΓS S j * S.sizeAt v (KB.minusW (ys n) a)) with hcm
    have hcp0 : 0 < cp := by positivity
    have hcm0 : 0 < cm := by positivity
    set κ : ℂ := (((lag n / θ n) * T ^ K * c0 : ℝ) : ℂ) with hκ
    have hc := cs_choice (CV ((p v).T.bs j) (S := Fin (KB.plusW (ys n) a).length))
      (CV ((p v).T.bs j) (S := Fin (KB.minusW (ys n) a).length))
      ((p v).form j hj (KB.plusW (ys n) a)) ((p v).form j hj (KB.minusW (ys n) a))
      (KB.pairJ ((p v).form j hj a) (ys n))
      cv_zero (fun x y hx hy => cv_add hx hy) (fun c x hx => cv_smul c hx)
      cv_zero (fun x y hx hy => cv_add hx hy) (fun c x hx => cv_smul c hx)
      (fun x₁ x₂ y c h₁ h₂ hy => form_slC (p v) j hj _ x₁ x₂ y c h₁ h₂ hy)
      (fun x y₁ y₂ c hx h₁ h₂ => form_srC (p v) j hj _ x y₁ y₂ c hx h₁ h₂)
      (fun x₁ x₂ y c h₁ h₂ hy => form_slC (p v) j hj _ x₁ x₂ y c h₁ h₂ hy)
      (fun x y₁ y₂ c hx h₁ h₂ => form_srC (p v) j hj _ x y₁ y₂ c hx h₁ h₂)
      (fun x₁ x₂ y c h₁ h₂ hy => pj_slC (p v) j hj a (ys n) x₁ x₂ y c h₁ h₂ hy)
      (fun x y₁ y₂ c hx h₁ h₂ => pj_srC (p v) j hj a (ys n) x y₁ y₂ c hx h₁ h₂)
      (KB.waveG ((p v).T.bs j) s (KB.plusW (ys n) a))
      (fun x hx => (hVI hA _ _ (D.parOf S v) (p v) j hj _ hCp' s x x hx hx).1)
      (fun x y c _ _ => PBG.waveG_add_smul _ s _ x y c)
      (fun x y hx hy => (hVI hA _ _ (D.parOf S v) (p v) j hj _ hCp' s x y hx hy).2)
      Q hQ (fun x y hx hy => hcs x y hx hy) Y (uY S p F v ε j hj (KB.plusW (ys n) a) Y)
      (uY S p F v ε j hj (KB.minusW (ys n) a) Y) (fun h => uY_cv hB F hF v ε hε j hj _ Y h)
      (fun h => uY_cv hB F hF v ε hε j hj _ Y h) κ cp cm hcp0 hcm0 c d

    have eA : ∑ p' ∈ Y, ∑ p'' ∈ Y, c p' * conj (c p'') * KB.gN S' v ε j (KB.plusW (ys n) a) p' p'' =
        ∑ p' ∈ Y, ∑ p'' ∈ Y, c p' * conj (c p'') * ((cp : ℂ) * (p v).form j hj (KB.plusW (ys n) a)
          (uY S p F v ε j hj (KB.plusW (ys n) a) Y p') (uY S p F v ε j hj (KB.plusW (ys n) a) Y p'')) := by
      refine Finset.sum_congr rfl fun p' hp' => Finset.sum_congr rfl fun p'' hp'' => ?_
      rw [uY_mem S p F v ε j hj _ Y p' hp', uY_mem S p F v ε j hj _ Y p'' hp'', gN_uB hB F hF v ε hε j hj _ p' p'']
    have eB : ∑ q' ∈ Y, ∑ q'' ∈ Y, d q' * conj (d q'') * KB.gN S' v ε j (KB.minusW (ys n) a) q' q'' =
        ∑ q' ∈ Y, ∑ q'' ∈ Y, d q' * conj (d q'') * ((cm : ℂ) * (p v).form j hj (KB.minusW (ys n) a)
          (uY S p F v ε j hj (KB.minusW (ys n) a) Y q') (uY S p F v ε j hj (KB.minusW (ys n) a) Y q'')) := by
      refine Finset.sum_congr rfl fun p' hp' => Finset.sum_congr rfl fun p'' hp'' => ?_
      rw [uY_mem S p F v ε j hj _ Y p' hp', uY_mem S p F v ε j hj _ Y p'' hp'', gN_uB hB F hF v ε hε j hj _ p' p'']
    have hnnA := quad_nonneg (gN_psdC hA hFP hB F hF v ε hε j hj _ hCp Y) c
    have hnnB := quad_nonneg (gN_psdC hA hFP hB F hF v ε hε j hj _ hCm Y) d
    rw [eA] at hnnA ⊢
    rw [eB] at hnnB ⊢
    refine hc.trans (mul_le_mul_of_nonneg_right ?_ (mul_nonneg hnnA hnnB))

    have hg1 := hB.1
    have hg2 := hB.2.1
    have hGg : 0 < S.G.g := by unfold Sz.Glob.g; exact_mod_cast Nat.mul_pos hg1 hg2
    have hGk : 0 < S.G.ka := by
      unfold Sz.Glob.ka; rw [S.hv]; have := PBD.rd_pos' E; positivity
    have hsA := supA_nonneg S hGg hGk v (decide (j = 0))
    have hmem : ∀ b, grid b (n b) ∈ ys n := fun b => List.mem_ofFn.2 ⟨b, rfl⟩
    have hPne : ∀ b, S.P v (grid b (n b)) ≠ 0 ∧ S.P v (grid b (n b) + 1) ≠ 0 := by
      intro b
      have hgr : (∃ a', grid b (n b) ∈ S.grid v a') ∨ grid b (n b) ∈ S.grid1 v := by
        rcases hnd _ (hmem b) with ⟨-, a', -, -, h⟩ | ⟨-, h, -⟩
        · exact Or.inl ⟨a', h⟩
        · exact Or.inr h
      obtain ⟨-, -, h1, h2⟩ := (hGo v).2.2.2.2.2 _ hgr
      exact ⟨h1, h2⟩
    have hnorm : ‖κ‖ = Λ * T ^ K * (1 / (ΓS S j * S.sizeAt v a)) := by
      rw [hκ, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul, abs_div, abs_of_pos (lam_div_theta grid hinj n).1,
        (lam_div_theta grid hinj n).2, abs_of_nonneg (pow_nonneg hT0.le K), abs_of_nonneg (by positivity : (0:ℝ) ≤ c0)]
    rw [hnorm, hQd, hcp, hcm, sizeAt_plusW, sizeAt_minusW, prod_ofFn_map, prod_ofFn_map, prod_ofFn_map]
    exact ratio_bound (fun b => grid b (n b)) (S.P v) qv Λ T (ΓS S j) (S.sizeAt v a)
      (Real.exp 1 * J.supA S.G S.de S.de' S.T S.T' S.l (decide (j = 0)) (S.pl v)) Xc hΓ hsa
      (fun b => hqpos _ (hmem b)) (fun b => (hPne b).1) (fun b => (hPne b).2)
      (fun b => (node_bound hB v a ha haN _ _ (hnd _ (hmem b))).2)
      (Finset.prod_nonneg fun b _ => Finset.sum_nonneg fun i _ => abs_nonneg _) hT0.le
      (mul_nonneg (Real.exp_pos 1).le hsA) hXc
  have hblock := block_of_choices Y (fun n => KB.gN S' v ε j (KB.plusW (ys n) a))
    (fun n => KB.gN S' v ε j (KB.minusW (ys n) a)) Pn θ (Xc ^ K) (Xc ^ K)
    (fun n => (lam_div_theta grid hinj n).1.le)
    (fun n => gN_psdC hA hFP hB F hF v ε hε j hj _ (hnodes n).2.2.1 Y)
    (fun n => gN_psdC hA hFP hB F hF v ε hε j hj _ (hnodes n).2.2.2.1 Y)
    (pow_nonneg hXc0 K) le_rfl hCS
  refine blockPSD_congr (fun _ _ _ _ => rfl) (fun p' hp' q' hq' => ?_) (fun _ _ _ _ => rfl) hblock

  show ∑ n, (θ n : ℂ) * Pn n p' q' = Complex.I ^ K * l ^ K * KB.hatB S' v ε (j + 1) 1 a l p' q'
  rw [hatB_uB_C hPSC hB F hF v ε hε j hj a hwa l p' q' (hY p' hp') (hY q' hq')]
  have hdeg := deg_uB hDW hB F hF v ε hε j hj a K grid hinj s p' q'
  have hIl : Complex.I ^ K * l ^ K = ((T ^ K : ℝ) : ℂ) * s ^ K := by
    rw [hs, sW_eq, mul_pow, mul_pow, ← mul_assoc, ← mul_assoc]
    have : ((T ^ K : ℝ) : ℂ) * (t : ℂ) ^ K = 1 := by
      rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, ← mul_pow, mul_comm T t, htT, one_pow, Complex.ofReal_one]
    linear_combination (Complex.I ^ K * l ^ K) * this.symm
  have e1 : Complex.I ^ K * l ^ K * ((c0 : ℂ) * (p v).form j hj a
      (KB.waveG ((p v).T.bs j) s a (uB S p F v ε j hj a p')) (uB S p F v ε j hj a q')) =
      ((T ^ K * c0 : ℝ) : ℂ) * (s ^ K * (p v).form j hj a
      (KB.waveG ((p v).T.bs j) s a (uB S p F v ε j hj a p')) (uB S p F v ε j hj a q')) := by
    rw [hIl]; push_cast; ring
  rw [show (((1 / (ΓS S j * S.sizeAt v a)) : ℝ) : ℂ) = (c0 : ℂ) from rfl, e1, hdeg, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hth := (lam_div_theta grid hinj n).1
  have hθ0 : ((F7.thGrid grid n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hth.ne'
  simp only [hPn, uY_mem S p F v ε j hj _ Y p' hp', uY_mem S p F v ε j hj _ Y q' hq', hlag, hθ]
  push_cast
  field_simp
  ring

end C2

end

end Formalism.FourierDecayAlt.P.PBL
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.WaveLocalPositiveCompactSupport
namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt NumberField

def WaveLocBC : Prop :=
  P5.ThmPActualCpt → StandardPairingDecay.PStdC → KB.DegWave → KB.SizeStdCpt → KB.VIsoCpt → FormPosCpt →
  ∀ (Cb Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ) (A₀ : ℝ),
    28 * Real.exp 1 ≤ Cc → KB.IsLeadingFormSetting Cb Cc S p f χ A₀ →
    ∃ X : ℕ → Fin S.f → ℝ, JC.HidaCurvatureBarriers S X ∧
      ∀ F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)),
        (∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) → ∀ v, KB.WaveLoc (setC S p F) v fun i => X i v

def WaveLocBPCpt : Prop :=
  P5.ThmPActualCpt → StandardPairingDecay.PStdC →
  ∀ (Cb Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ) (A₀ : ℝ),
    28 * Real.exp 1 ≤ Cc → KB.IsLeadingFormSetting Cb Cc S p f χ A₀ →
    ∃ X : ℕ → Fin S.f → ℝ, JC.HidaCurvatureBarriers S X ∧
      ∀ F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)),
        (∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) → ∀ v, KB.WaveLoc (setC S p F) v fun i => X i v

end Formalism.FourierDecayAlt.P.PBL


open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.PBL in
theorem Formalism.FourierDecayAlt.P.wave_local_compact_support_route : Formalism.FourierDecayAlt.P.PBL.WaveLocBC := by
  intro hA hPSC hDW hSS hVI hFP Cb Cc E _ _ _ Wp Wq _ _ _ _ _ _ S p f χ A₀ hCc hB
  refine ⟨fun i v => Xw S i v, thr_wave hCc hB, fun F hF v => ?_⟩
  intro i hi1 hir a ha haK
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have hir' : j + 1 ≤ S.G.r + 1 := hir
  have hj : j ≤ S.G.r := by omega
  have haK' : a.length + C.Kst ≤ S.Ntop := haK
  have ha' : D.AdmAt S v a := ha
  have haN : a.length ≤ S.Ntop := by omega
  have hB' := hB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hGo, hGr, -⟩ := hB'
  have hCI := Formalism.FourierDecayAlt.P.PBCut.cutInside_of_built hB
  obtain ⟨grid, hinj, hl1, hnodes, hlp, hlm⟩ := nodes_level hB v a ha' C.Kst haK' j hj
  have hwa : KB.CutWord (D.parOf S v) (S.l + 1) a :=
    (Formalism.FourierDecayAlt.P.new_letters_admissible E Wp Wq S hGo hGr hCI v a C.Kst 0 ha' haK' (by omega)).1
  refine ⟨PBD.pushU grid (fun ys => KB.plusW ys a), PBD.pushTh grid (fun ys => KB.plusW ys a),
    PBD.pushU grid (fun ys => KB.minusW ys a), PBD.pushTh grid (fun ys => KB.minusW ys a), hlp, hlm,
    fun ε hε l Y hY => ⟨?_, Complex.I ^ C.Kst, by simp, ?_⟩⟩
  · have hY' : ∀ h ∈ Y, D.ptSize h = j := fun h hh => by have := hY h hh; omega
    have h0 := block0C hA hPSC hVI hFP hB F hF v ε hε j hj a hwa l Y hY'
    rw [Nat.add_sub_cancel]
    exact h0
  · have hY' : ∀ h ∈ Y, D.ptSize h = j := fun h hh => by have := hY h hh; omega
    have hK := blockK_waveC hA hPSC hDW hSS hVI hFP hB F hF v ε hε j hj a ha' haN hwa C.Kst grid hinj hnodes
      (Xw S (j + 1) v) (xw_nonneg hB _ v) (xw_K hB v j C.Kst grid hl1) l Y hY'
    refine blockPSD_congr (fun p' _ q' _ => ?_) (fun _ _ _ _ => rfl) (fun p' _ q' _ => ?_) hK
    · show ((Xw S (j + 1) v ^ C.Kst : ℝ) : ℂ) * ∑ n, (F7.thGrid grid n : ℂ) *
          KB.gN (setC S p F) v ε j (KB.plusW (List.ofFn fun b => grid b (n b)) a) p' q' =
        ((Xw S (j + 1) v ^ C.Kst : ℝ) : ℂ) * KB.mix (setC S p F) v ε (j + 1 - 1)
          (PBD.pushU grid fun ys => KB.plusW ys a) (PBD.pushTh grid fun ys => KB.plusW ys a) p' q'
      rw [Nat.add_sub_cancel, mix_push]
    · show ((Xw S (j + 1) v ^ C.Kst : ℝ) : ℂ) * ∑ n, (F7.thGrid grid n : ℂ) *
          KB.gN (setC S p F) v ε j (KB.minusW (List.ofFn fun b => grid b (n b)) a) p' q' =
        ((Xw S (j + 1) v ^ C.Kst : ℝ) : ℂ) * KB.mix (setC S p F) v ε (j + 1 - 1)
          (PBD.pushU grid fun ys => KB.minusW ys a) (PBD.pushTh grid fun ys => KB.minusW ys a) p' q'
      rw [Nat.add_sub_cancel, mix_push]

theorem Formalism.FourierDecayAlt.P.wave_local_positive_compact_support : Formalism.FourierDecayAlt.P.PBL.WaveLocBPCpt := fun hA hPSC =>
  Formalism.FourierDecayAlt.P.wave_local_compact_support_route hA hPSC Formalism.FourierDecayAlt.P.degree_of_plane_wave Formalism.FourierDecayAlt.P.size_standard_compact
    Formalism.FourierDecayAlt.P.vector_isomorphism_compact_support Formalism.FourierDecayAlt.P.module_form_pos_compact_support
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftLocalPositiveCompactSupport
namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField Formalism.FourierDecayAlt.P.LiftDegreeLemmas
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

section blockLC

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
  {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
  {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}

theorem blockK_liftC (hA : P5.ThmPActualCpt) (hDL : KB.DegLift) (hSS : KB.SizeStdCpt) (hFP : FormPosCpt)
    (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (hF : ∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) (v : Fin S.f) (ε : ℝ) (hε : 0 < ε) (j : ℕ)
    (hj : j ≤ S.G.r) (b s : ℕ) (hb : 1 ≤ b)
    (a : List C.Letter) (ha : D.AdmAt S v a) (haN : a.length ≤ S.Ntop) (K : ℕ)
    (grid : Fin K → Fin (2 * (j - s) + s + 1) → ℝ) (hinj : ∀ c, Function.Injective (grid c))
    (hnodes : ∀ n : Fin K → Fin (2 * (j - s) + s + 1),
        D.AdmAt S v (KB.plusW (List.ofFn fun c => grid c (n c)) a) ∧
        D.AdmAt S v (KB.minusW (List.ofFn fun c => grid c (n c)) a) ∧
        KB.CutWord (D.parOf S v) (S.l + 1) (KB.plusW (List.ofFn fun c => grid c (n c)) a) ∧
        KB.CutWord (D.parOf S v) (S.l + 1) (KB.minusW (List.ofFn fun c => grid c (n c)) a) ∧
        (List.ofFn fun c => grid c (n c)).Pairwise (fun y y' => 2 < |y - y'|) ∧
        ∀ y ∈ (List.ofFn fun c => grid c (n c)), NodeOK S v a false y)
    (Xc : ℝ) (hXc0 : 0 ≤ Xc)
    (hXc : (∏ c, ∑ i, |F7.lagCo (grid c) i|) * ‖lamB S b s‖ ^ K *
      (Real.exp 1 * J.supA S.G S.de S.de' S.T S.T' S.l false (S.pl v)) ^ K ≤ Xc ^ K)
    (t t' : ℂ) (Y : Finset C.LPt) (hY : ∀ h ∈ Y, D.ptSize h = b - 1) :
    KB.BlockPSD Y Y
      (fun p' q' => ((Xc ^ K : ℝ) : ℂ) * ∑ n : Fin K → Fin (2 * (j - s) + s + 1), (F7.thGrid grid n : ℂ) *
        KB.gN (setC S p F) v ε j (KB.plusW (List.ofFn fun c => grid c (n c)) a) (p' ++ [(s, t)]) (q' ++ [(s, t)]))
      (fun p' q' => (((‖lamB S b s‖ : ℝ) : ℂ) * (-1) ^ (s - 1) * (lamB S b s)⁻¹) ^ K * (t⁻¹ - t'⁻¹) ^ K *
        KB.gN (setC S p F) v ε j a (p' ++ [(s, t)]) (q' ++ [(s, t')]))
      (fun p' q' => ((Xc ^ K : ℝ) : ℂ) * ∑ n : Fin K → Fin (2 * (j - s) + s + 1), (F7.thGrid grid n : ℂ) *
        KB.gN (setC S p F) v ε j (KB.minusW (List.ofFn fun c => grid c (n c)) a) (p' ++ [(s, t')])
          (q' ++ [(s, t')])) := by
  have hB' := hB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hGo, -, -, -, -, hv⟩ := hB'
  obtain ⟨hl0, -, -, -, -⟩ := hv v
  have hgpos := g_pos_of_built hB
  have hΓ := gam_pos hB j
  have hsa := sizeAt_pos S hGo v a ha
  set T : ℝ := ‖lamB S b s‖ with hT
  have hT0 : 0 < T := norm_pos_iff.2 (lamB_ne S hgpos b s)
  set c0 : ℝ := 1 / (ΓS S j * S.sizeAt v a) with hc0
  set ys : (Fin K → Fin (2 * (j - s) + s + 1)) → List ℝ := fun n => List.ofFn fun c => grid c (n c) with hys
  set Λ : ℝ := ∏ c, ∑ i, |F7.lagCo (grid c) i| with hΛ
  set θ : (Fin K → Fin (2 * (j - s) + s + 1)) → ℝ := fun n => F7.thGrid grid n with hθ
  set lag : (Fin K → Fin (2 * (j - s) + s + 1)) → ℝ := fun n => ∏ c, F7.lagCo (grid c) (n c) with hlag
  set S' := setC S p F with hS'
  set Pn : (Fin K → Fin (2 * (j - s) + s + 1)) → C.LPt → C.LPt → ℂ := fun n p' q' =>
    (((lag n / θ n) * T ^ K * c0 : ℝ) : ℂ) * KB.pairJ ((p v).form j hj a) (ys n)
      (uS S p F v ε j hj (KB.plusW (ys n) a) Y (s, t) p') (uS S p F v ε j hj (KB.minusW (ys n) a) Y (s, t') q')
    with hPn
  have hCS : ∀ n (c d : C.LPt → ℂ), ‖∑ p' ∈ Y, ∑ q' ∈ Y, c p' * conj (d q') * Pn n p' q'‖ ^ 2 ≤
      (Xc ^ K) ^ 2 * ((∑ p' ∈ Y, ∑ p'' ∈ Y, c p' * conj (c p'') *
          KB.gN S' v ε j (KB.plusW (ys n) a) (p' ++ [(s, t)]) (p'' ++ [(s, t)])).re *
        (∑ q' ∈ Y, ∑ q'' ∈ Y, d q' * conj (d q'') *
          KB.gN S' v ε j (KB.minusW (ys n) a) (q' ++ [(s, t')]) (q'' ++ [(s, t')])).re) := by
    intro n c d
    obtain ⟨hAp, hAm, hCp, hCm, hpw, hnd⟩ := hnodes n
    have hCp' : KB.CutWord (D.parOf S v) (p v).l0 (KB.plusW (ys n) a) := by rw [hl0]; exact hCp
    have hCm' : KB.CutWord (D.parOf S v) (p v).l0 (KB.minusW (ys n) a) := by rw [hl0]; exact hCm
    obtain ⟨hqpos, hcs⟩ := hSS hA (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (p v) j hj a (ys n) hCp' hCm' hpw
    set qv : ℝ → ℝ := fun y => (Wd.qw (M.qC (D.parOf S v)) (D.positionted a) (y : ℂ)).re with hqv
    set Q : ℝ := ((ys n).map qv).prod with hQd
    have hQ : 0 < Q := List.prod_pos fun x hx => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      exact hqpos y hy
    have hsp := sizeAt_pos S hGo v _ hAp
    have hsm := sizeAt_pos S hGo v _ hAm
    set cp : ℝ := 1 / (ΓS S j * S.sizeAt v (KB.plusW (ys n) a)) with hcp
    set cm : ℝ := 1 / (ΓS S j * S.sizeAt v (KB.minusW (ys n) a)) with hcm
    have hcp0 : 0 < cp := by positivity
    have hcm0 : 0 < cm := by positivity
    set κ : ℂ := (((lag n / θ n) * T ^ K * c0 : ℝ) : ℂ) with hκ
    have hc := cs_choice (CV ((p v).T.bs j) (S := Fin (KB.plusW (ys n) a).length))
      (CV ((p v).T.bs j) (S := Fin (KB.minusW (ys n) a).length))
      ((p v).form j hj (KB.plusW (ys n) a)) ((p v).form j hj (KB.minusW (ys n) a))
      (KB.pairJ ((p v).form j hj a) (ys n))
      cv_zero (fun x y hx hy => cv_add hx hy) (fun c x hx => cv_smul c hx)
      cv_zero (fun x y hx hy => cv_add hx hy) (fun c x hx => cv_smul c hx)
      (fun x₁ x₂ y c h₁ h₂ hy => form_slC (p v) j hj _ x₁ x₂ y c h₁ h₂ hy)
      (fun x y₁ y₂ c hx h₁ h₂ => form_srC (p v) j hj _ x y₁ y₂ c hx h₁ h₂)
      (fun x₁ x₂ y c h₁ h₂ hy => form_slC (p v) j hj _ x₁ x₂ y c h₁ h₂ hy)
      (fun x y₁ y₂ c hx h₁ h₂ => form_srC (p v) j hj _ x y₁ y₂ c hx h₁ h₂)
      (fun x₁ x₂ y c h₁ h₂ hy => pj_slC (p v) j hj a (ys n) x₁ x₂ y c h₁ h₂ hy)
      (fun x y₁ y₂ c hx h₁ h₂ => pj_srC (p v) j hj a (ys n) x y₁ y₂ c hx h₁ h₂)
      id (fun x hx => hx) (fun x y c _ _ => rfl) (fun x y _ _ => rfl)
      Q hQ (fun x y hx hy => hcs x y hx hy) Y (uS S p F v ε j hj (KB.plusW (ys n) a) Y (s, t))
      (uS S p F v ε j hj (KB.minusW (ys n) a) Y (s, t')) (fun h => uY_cv hB F hF v ε hε j hj _ _ _)
      (fun h => uY_cv hB F hF v ε hε j hj _ _ _) κ cp cm hcp0 hcm0 c d
    have eA : ∑ p' ∈ Y, ∑ p'' ∈ Y, c p' * conj (c p'') *
        KB.gN S' v ε j (KB.plusW (ys n) a) (p' ++ [(s, t)]) (p'' ++ [(s, t)]) =
        ∑ p' ∈ Y, ∑ p'' ∈ Y, c p' * conj (c p'') * ((cp : ℂ) * (p v).form j hj (KB.plusW (ys n) a)
          (uS S p F v ε j hj (KB.plusW (ys n) a) Y (s, t) p') (uS S p F v ε j hj (KB.plusW (ys n) a) Y (s, t) p'')) := by
      refine Finset.sum_congr rfl fun p' hp' => Finset.sum_congr rfl fun p'' hp'' => ?_
      rw [uS_mem S p F v ε j hj _ Y _ p' hp', uS_mem S p F v ε j hj _ Y _ p'' hp'', gN_uB hB F hF v ε hε j hj _ _ _]
    have eB : ∑ q' ∈ Y, ∑ q'' ∈ Y, d q' * conj (d q'') *
        KB.gN S' v ε j (KB.minusW (ys n) a) (q' ++ [(s, t')]) (q'' ++ [(s, t')]) =
        ∑ q' ∈ Y, ∑ q'' ∈ Y, d q' * conj (d q'') * ((cm : ℂ) * (p v).form j hj (KB.minusW (ys n) a)
          (uS S p F v ε j hj (KB.minusW (ys n) a) Y (s, t') q')
          (uS S p F v ε j hj (KB.minusW (ys n) a) Y (s, t') q'')) := by
      refine Finset.sum_congr rfl fun p' hp' => Finset.sum_congr rfl fun p'' hp'' => ?_
      rw [uS_mem S p F v ε j hj _ Y _ p' hp', uS_mem S p F v ε j hj _ Y _ p'' hp'', gN_uB hB F hF v ε hε j hj _ _ _]
    have hnnA : 0 ≤ (∑ p' ∈ Y, ∑ p'' ∈ Y, c p' * conj (c p'') *
        KB.gN S' v ε j (KB.plusW (ys n) a) (p' ++ [(s, t)]) (p'' ++ [(s, t)])).re :=
      quad_nonneg (psd_shift (s, t) (gN_psdC hA hFP hB F hF v ε hε j hj _ hCp _)) c
    have hnnB : 0 ≤ (∑ q' ∈ Y, ∑ q'' ∈ Y, d q' * conj (d q'') *
        KB.gN S' v ε j (KB.minusW (ys n) a) (q' ++ [(s, t')]) (q'' ++ [(s, t')])).re :=
      quad_nonneg (psd_shift (s, t') (gN_psdC hA hFP hB F hF v ε hε j hj _ hCm _)) d
    rw [eA] at hnnA ⊢
    rw [eB] at hnnB ⊢
    refine hc.trans (mul_le_mul_of_nonneg_right ?_ (mul_nonneg hnnA hnnB))

    have hth := lam_div_theta grid hinj n
    have hκn : ‖κ‖ = Λ * T ^ K * c0 := by
      rw [hκ, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul, abs_div, abs_of_pos hth.1,
        abs_of_pos (pow_pos hT0 K), abs_of_pos (by positivity : (0 : ℝ) < c0)]
      rw [hth.2]
    have hPp : ∀ c, S.P v (grid c (n c)) ≠ 0 := by
      have h1 := hsp
      rw [sizeAt_plusW, prod_ofFn_map'] at h1
      have h2 := (pos_of_mul_pos_left h1 hsa.le).ne'
      intro c hc0'
      exact h2 (Finset.prod_eq_zero (Finset.mem_univ c) (by rw [hc0', abs_zero]))
    have hPm : ∀ c, S.P v (grid c (n c) + 1) ≠ 0 := by
      have h1 := hsm
      rw [sizeAt_minusW, prod_ofFn_map'] at h1
      have h2 := (pos_of_mul_pos_left h1 hsa.le).ne'
      intro c hc0'
      exact h2 (Finset.prod_eq_zero (Finset.mem_univ c) (by rw [hc0', abs_zero]))
    have hrb := ratio_bound (fun c => grid c (n c)) (S.P v) qv Λ T (ΓS S j) (S.sizeAt v a)
      (Real.exp 1 * J.supA S.G S.de S.de' S.T S.T' S.l false (S.pl v)) Xc hΓ hsa
      (fun c => hqpos _ (List.mem_ofFn.2 ⟨c, rfl⟩)) hPp hPm
      (fun c => (node_bound hB v a ha haN _ false (hnd _ (List.mem_ofFn.2 ⟨c, rfl⟩))).2)
      (Finset.prod_nonneg fun c _ => Finset.sum_nonneg fun i _ => abs_nonneg _) hT0.le
      (mul_nonneg (Real.exp_pos 1).le (supA_nonneg S (glob_pos' hB).1 (glob_pos' hB).2 v false)) hXc
    have eQ : Q = ∏ c, qv (grid c (n c)) := prod_ofFn_map' _ _
    have ecp : cp = 1 / (ΓS S j * ((∏ c, |S.P v (grid c (n c))|) * S.sizeAt v a)) := by
      rw [hcp, sizeAt_plusW, prod_ofFn_map']
    have ecm : cm = 1 / (ΓS S j * ((∏ c, |S.P v (grid c (n c) + 1)|) * S.sizeAt v a)) := by
      rw [hcm, sizeAt_minusW, prod_ofFn_map']
    rw [hκn, eQ, ecp, ecm]
    exact hrb
  have hblock := block_of_choices Y
    (fun n p' q' => KB.gN S' v ε j (KB.plusW (ys n) a) (p' ++ [(s, t)]) (q' ++ [(s, t)]))
    (fun n p' q' => KB.gN S' v ε j (KB.minusW (ys n) a) (p' ++ [(s, t')]) (q' ++ [(s, t')])) Pn θ (Xc ^ K) (Xc ^ K)
    (fun n => (lam_div_theta grid hinj n).1.le)
    (fun n => psd_shift (s, t) (gN_psdC hA hFP hB F hF v ε hε j hj _ (hnodes n).2.2.1 _))
    (fun n => psd_shift (s, t') (gN_psdC hA hFP hB F hF v ε hε j hj _ (hnodes n).2.2.2.1 _))
    (pow_nonneg hXc0 K) le_rfl hCS
  refine blockPSD_congr (fun _ _ _ _ => rfl) (fun p' hp' q' hq' => ?_) (fun _ _ _ _ => rfl) hblock
  show ∑ n, (θ n : ℂ) * Pn n p' q' =
    ((T : ℂ) * (-1) ^ (s - 1) * (lamB S b s)⁻¹) ^ K * (t⁻¹ - t'⁻¹) ^ K * KB.gN S' v ε j a (p' ++ [(s, t)]) (q' ++ [(s, t')])
  rw [gN_uB hB F hF v ε hε j hj a _ _, show (((1 / (ΓS S j * S.sizeAt v a)) : ℝ) : ℂ) = (c0 : ℂ) from rfl]
  have hdeg := deg_uB_lift hDL hB F hF v ε hε j hj b s hb a K grid hinj p' q' (hY p' hp') (hY q' hq') t t'
  have hlm : (lamB S b s * t)⁻¹ - (lamB S b s * t')⁻¹ = (lamB S b s)⁻¹ * (t⁻¹ - t'⁻¹) := by
    rw [mul_inv, mul_inv]; ring
  rw [hlm] at hdeg
  have eR : ((T : ℂ) * (-1) ^ (s - 1) * (lamB S b s)⁻¹) ^ K * (t⁻¹ - t'⁻¹) ^ K *
      ((c0 : ℂ) * (p v).form j hj a (uB S p F v ε j hj a (p' ++ [(s, t)])) (uB S p F v ε j hj a (q' ++ [(s, t')]))) =
      ((T : ℂ) ^ K * c0) * (((-1) ^ (s - 1) * ((lamB S b s)⁻¹ * (t⁻¹ - t'⁻¹))) ^ K *
        (p v).form j hj a (uB S p F v ε j hj a (p' ++ [(s, t)])) (uB S p F v ε j hj a (q' ++ [(s, t')]))) := by
    simp only [mul_pow]; ring
  rw [eR, hdeg, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hth := (lam_div_theta grid hinj n).1
  have hθ0 : ((F7.thGrid grid n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hth.ne'
  simp only [hPn, uS_mem S p F v ε j hj _ Y _ p' hp', uS_mem S p F v ε j hj _ Y _ q' hq', hlag, hθ]
  push_cast
  field_simp
  ring

end blockLC

def LiftLocBC : Prop :=
  P5.ThmPActualCpt → KB.SizeStdCpt → KB.DegLift → Formalism.FourierDecayAlt.P.PBL.FormPosCpt →
  ∀ (Cb Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ) (A₀ : ℝ),
    28 * Real.exp 1 ≤ Cc → KB.IsLeadingFormSetting Cb Cc S p f χ A₀ →
    ∃ Λ : ℕ → ℕ → Fin S.f → ℝ,
      (∀ b s, 1 ≤ b → 1 ≤ s → b + s ≤ S.G.r + 1 → ∀ v, 0 ≤ Λ b s v ∧ Λ b s v ≤ S.base.szL b s v) ∧
      ∀ F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)),
        (∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) → ∀ v, KB.LiftLoc (setC S p F) v fun b s => Λ b s v

def LiftLocBPCpt : Prop :=
  P5.ThmPActualCpt → KB.DegLift →
  ∀ (Cb Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ) (A₀ : ℝ),
    28 * Real.exp 1 ≤ Cc → KB.IsLeadingFormSetting Cb Cc S p f χ A₀ →
    ∃ Λ : ℕ → ℕ → Fin S.f → ℝ,
      (∀ b s, 1 ≤ b → 1 ≤ s → b + s ≤ S.G.r + 1 → ∀ v, 0 ≤ Λ b s v ∧ Λ b s v ≤ S.base.szL b s v) ∧
      ∀ F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)),
        (∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) → ∀ v, KB.LiftLoc (setC S p F) v fun b s => Λ b s v

end

end Formalism.FourierDecayAlt.P.PBL


open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.PBL Formalism.FourierDecayAlt.P.LiftDegreeLemmas in
theorem Formalism.FourierDecayAlt.P.lift_local_compact_support_route : Formalism.FourierDecayAlt.P.PBL.LiftLocBC := by
  intro hA hSS hDL hFP Cb Cc E _ _ _ Wp Wq _ _ _ _ _ _ S p f χ A₀ hCc hB
  refine ⟨fun b s v => lamLift S b s v, fun b s hb hs hbs v => thr_lift hCc hB b s hb hs hbs v, fun F hF v => ?_⟩
  intro b s hb hs hbs a ha haK
  have hbs' : b + s ≤ S.G.r + 1 := hbs
  have haK' : a.length + C.Kst ≤ S.Ntop := haK
  have ha' : D.AdmAt S v a := ha
  have haN : a.length ≤ S.Ntop := by omega
  have hgpos := g_pos_of_built hB
  have hj : b + s - 1 ≤ S.G.r := by omega
  have hB' := hB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hGo, hGr, -⟩ := hB'
  have hCI := Formalism.FourierDecayAlt.P.PBCut.cutInside_of_built hB
  obtain ⟨-, grid, hinj, hl1, hmem, hall, hlp, hlm⟩ :=
    Formalism.FourierDecayAlt.P.new_letters_admissible E Wp Wq S hGo hGr hCI v a C.Kst (2 * (b + s - 1 - s) + s) ha' haK' (by omega)
  have hnodes : ∀ n : Fin C.Kst → Fin (2 * (b + s - 1 - s) + s + 1),
      D.AdmAt S v (KB.plusW (List.ofFn fun c => grid c (n c)) a) ∧
      D.AdmAt S v (KB.minusW (List.ofFn fun c => grid c (n c)) a) ∧
      KB.CutWord (D.parOf S v) (S.l + 1) (KB.plusW (List.ofFn fun c => grid c (n c)) a) ∧
      KB.CutWord (D.parOf S v) (S.l + 1) (KB.minusW (List.ofFn fun c => grid c (n c)) a) ∧
      (List.ofFn fun c => grid c (n c)).Pairwise (fun y y' => 2 < |y - y'|) ∧
      ∀ y ∈ (List.ofFn fun c => grid c (n c)), NodeOK S v a false y := fun n => by
    obtain ⟨h1, h2, h3, h4, h5⟩ := hall n
    refine ⟨h1, h2, h3, h4, h5.imp fun h => by linarith, fun y hy => Or.inl ⟨rfl, ?_⟩⟩
    obtain ⟨c, rfl⟩ := List.mem_ofFn.1 hy
    exact ⟨a.length + C.Kst - c, by omega, by omega, hmem c (n c)⟩
  refine ⟨PBD.pushU grid (fun ys => KB.plusW ys a), PBD.pushTh grid (fun ys => KB.plusW ys a),
    PBD.pushU grid (fun ys => KB.minusW ys a), PBD.pushTh grid (fun ys => KB.minusW ys a), hlp, hlm,
    fun ε hε t t' Y _ _ hY => ⟨((((‖lamB S b s‖ : ℝ) : ℂ) * (-1) ^ (s - 1) * (lamB S b s)⁻¹) ^ C.Kst),
      norm_u S hgpos b s C.Kst, ?_⟩⟩
  have hK := blockK_liftC hA hDL hSS hFP hB F hF v ε hε (b + s - 1) hj b s hb a ha' haN C.Kst grid hinj hnodes
    (lamLift S b s v) (lamLift_nonneg hB b s v) (lift_K hB v b s (b + s - 1) C.Kst (by omega) grid hl1) t t' Y hY
  refine blockPSD_congr (fun p' _ q' _ => ?_) (fun _ _ _ _ => rfl) (fun p' _ q' _ => ?_) hK
  · show ((lamLift S b s v ^ C.Kst : ℝ) : ℂ) * ∑ n, (F7.thGrid grid n : ℂ) *
        KB.gN (setC S p F) v ε (b + s - 1) (KB.plusW (List.ofFn fun c => grid c (n c)) a) (p' ++ [(s, t)])
          (q' ++ [(s, t)]) =
      ((lamLift S b s v ^ C.Kst : ℝ) : ℂ) * KB.mix (setC S p F) v ε (b + s - 1)
        (PBD.pushU grid fun ys => KB.plusW ys a) (PBD.pushTh grid fun ys => KB.plusW ys a) (p' ++ [(s, t)])
          (q' ++ [(s, t)])
    rw [mix_push]
  · show ((lamLift S b s v ^ C.Kst : ℝ) : ℂ) * ∑ n, (F7.thGrid grid n : ℂ) *
        KB.gN (setC S p F) v ε (b + s - 1) (KB.minusW (List.ofFn fun c => grid c (n c)) a) (p' ++ [(s, t')])
          (q' ++ [(s, t')]) =
      ((lamLift S b s v ^ C.Kst : ℝ) : ℂ) * KB.mix (setC S p F) v ε (b + s - 1)
        (PBD.pushU grid fun ys => KB.minusW ys a) (PBD.pushTh grid fun ys => KB.minusW ys a) (p' ++ [(s, t')])
          (q' ++ [(s, t')])
    rw [mix_push]

theorem Formalism.FourierDecayAlt.P.lift_local_positive_compact_support : Formalism.FourierDecayAlt.P.PBL.LiftLocBPCpt := fun hA hDL =>
  Formalism.FourierDecayAlt.P.lift_local_compact_support_route hA Formalism.FourierDecayAlt.P.size_standard_compact hDL Formalism.FourierDecayAlt.P.module_form_pos_compact_support
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.BuiltBoundsCompactOfLeaves
namespace Formalism.FourierDecayAlt.P.PBASM

open Formalism.FourierDecayAlt NumberField

noncomputable section

theorem waveLocB_of_cpt (hPSC : P5.ThmPActualCpt → StandardPairingDecay.PStdC) : P5.ThmPActualCpt → WaveLocB := by
  intro hA Cb
  refine ⟨28 * Real.exp 1, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S p f χ A₀ hB
  exact wave_local_positive_compact_support hA (hPSC hA) Cb _ E Wp Wq S p f χ A₀ le_rfl hB

theorem liftLocB_of_cpt (hDL : KB.DegLift) : P5.ThmPActualCpt → LiftLocB := by
  intro hA Cb
  refine ⟨28 * Real.exp 1, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S p f χ A₀ hB
  obtain ⟨Λ0, hΛ0, hl⟩ := lift_local_positive_compact_support hA hDL Cb _ E Wp Wq S p f χ A₀ le_rfl hB
  refine ⟨fun b s v => if 1 ≤ b ∧ 1 ≤ s ∧ b + s ≤ S.G.r + 1 then Λ0 b s v else 0, ?_, ?_, ?_⟩
  · intro b s v
    beta_reduce
    by_cases h : 1 ≤ b ∧ 1 ≤ s ∧ b + s ≤ S.G.r + 1
    · rw [if_pos h]; exact (hΛ0 b s h.1 h.2.1 h.2.2 v).1
    · rw [if_neg h]
  · intro b s hb hs hbs v
    beta_reduce
    rw [if_pos ⟨hb, hs, hbs⟩]; exact (hΛ0 b s hb hs hbs v).2
  · intro F hF v b s hb hs hbs
    have h : (if 1 ≤ b ∧ 1 ≤ s ∧ b + s ≤ S.G.r + 1 then Λ0 b s v else 0) = Λ0 b s v := if_pos ⟨hb, hs, hbs⟩
    simp only [h]
    exact hl F hF v b s hb hs hbs

end

def BuiltBounds2CptOfLeaves : Prop :=
  KB.RadHead → KB.HeadTop → KB.DegLift → PBL.TopLocB → KB.DegTop → PBL.TopRatio → GermPartsC →
  (P5.ThmPActualCpt → DecayUnif) → KB.BuiltBounds2Cpt

theorem builtBounds2CptOfLeaves : BuiltBounds2CptOfLeaves := by
  intro hRH hHT hDL hTL hDT hTR hGP hD
  have hPSC : P5.ThmPActualCpt → StandardPairingDecay.PStdC := fun hA => StandardPairingDecay.pStdC_of hA hRH hHT
  have hI : P5.ThmPActualCpt → IntB := fun hA => integral_bound_of_parts (hPSC hA) (hD hA)
  exact builtBounds2CptOfParts (waveLocB_of_cpt hPSC) (liftLocB_of_cpt hDL) hTL (fun _ => hDT)
    (fun _ => vector_valued_types) (fun _ => hTR) (fun hA => germLocB_of (hI hA) hGP) positivity_bound hI hD
    (fun _ => thrPos)

end Formalism.FourierDecayAlt.P.PBASM

namespace Formalism.FourierDecayAlt.P

theorem built_bounds_compact_of_leaves : PBASM.BuiltBounds2CptOfLeaves := PBASM.builtBounds2CptOfLeaves

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.UniformDecayOfPlace
namespace Formalism.FourierDecayAlt.P.StandardPairingDecay

open Formalism.FourierDecayAlt NumberField MeasureTheory Filter Topology Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.PBD Formalism.FourierDecayAlt.P.PBL
open scoped ComplexConjugate

noncomputable section

theorem thr_plus3 (c0 Cc R X N A : ℝ) (hc : max (4 * c0) 0 ≤ Cc) (hR : 0 ≤ R) (hX : 1 ≤ X) (hN : 0 ≤ N)
    (hA : Cc * R * (N * X ^ 2 + X ^ 3) ≤ A) : c0 * R * ((N + 3) * X ^ 2 + X ^ 3) ≤ A := by
  have hX2 : X ^ 2 ≤ X ^ 3 := by nlinarith
  have hY : 0 ≤ N * X ^ 2 + X ^ 3 := by positivity
  have hle : (N + 3) * X ^ 2 + X ^ 3 ≤ 4 * (N * X ^ 2 + X ^ 3) := by nlinarith
  have hY' : 0 ≤ (N + 3) * X ^ 2 + X ^ 3 := by positivity
  have h0 : 0 ≤ Cc := le_trans (le_max_right _ _) hc
  have h4 : 4 * c0 ≤ Cc := le_trans (le_max_left _ _) hc
  refine le_trans ?_ hA
  rcases le_or_gt c0 0 with hc0 | hc0
  · have : c0 * R * ((N + 3) * X ^ 2 + X ^ 3) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hc0 hR) hY'
    exact le_trans this (by positivity)
  · calc c0 * R * ((N + 3) * X ^ 2 + X ^ 3) ≤ c0 * R * (4 * (N * X ^ 2 + X ^ 3)) :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = (4 * c0) * R * (N * X ^ 2 + X ^ 3) := by ring
      _ ≤ Cc * R * (N * X ^ 2 + X ^ 3) := by gcongr

theorem bound_absorb (K C M y a b : ℝ) (_hM : 0 ≤ M) (hy : 0 ≤ y) (_hb : 0 ≤ b) (hK : 0 ≤ K)
    (ha : a ≤ C * y) (hyM : y ≤ M * b) : K * a ≤ (K * |C| * M) * b := by
  have h1 : C * y ≤ |C| * (M * b) := le_trans (mul_le_mul_of_nonneg_right (le_abs_self C) hy)
    (mul_le_mul_of_nonneg_left hyM (abs_nonneg C))
  calc K * a ≤ K * (|C| * (M * b)) := mul_le_mul_of_nonneg_left (le_trans ha h1) hK
    _ = (K * |C| * M) * b := by ring

def DecayUnifOfPlace : Prop :=
  P5.ThmPActualCpt → KB.RadHead → KB.HeadTop → Formalism.FourierDecayAlt.P.PBO.DecayUnif → Formalism.FourierDecayAlt.P.PBASM.DecayUnif

theorem decayUnif_of_place (hP : P5.ThmPActualCpt) (hRH : KB.RadHead) (hHT : KB.HeadTop)
    (hD : Formalism.FourierDecayAlt.P.PBO.DecayUnif) : Formalism.FourierDecayAlt.P.PBASM.DecayUnif := by
  have hPS : PStdC := pStdC_of hP hRH hHT
  intro Cb
  obtain ⟨c0, hc0⟩ := hD hP Cb
  obtain ⟨c1, hc1⟩ := Formalism.FourierDecayAlt.P.limit_of_module_forms Cb
  refine ⟨max (max (4 * c0) 0) c1, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S p f χ A₀ hB v ε hε i hi1 hir a ha h h' hsz hsz'
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have hj : j ≤ S.G.r := by omega
  simp only [Nat.add_sub_cancel] at hsz hsz'
  have hgpos := g_pos_of_built hB
  have hB' := hB
  obtain ⟨-, -, -, hcut, -, -, -, -, -, -, hGo, -, -, -, hA, hv⟩ := hB'
  obtain ⟨hl0, hInD, -, hCk, hCC⟩ := hv v
  have hCI : KB.CutInside S := Formalism.FourierDecayAlt.P.PBCut.cutInside_of_built hB
  obtain ⟨w, rfl⟩ := ha
  have hw : KB.CutWord (D.parOf S v) (S.l + 1) (w.1 v) := cutWord_of_adm S hGo hCI w v
  have hlen : (w.1 v).length ≤ S.Ntop := le_trans (Formalism.FourierDecayAlt.P.PBB.len_le_cnt S w v) w.2.2
  have hR : (0 : ℝ) ≤ ((S.G.r : ℝ) + 1) ^ 4 := by positivity
  have hX : (1 : ℝ) ≤ 2 * (S.G.r : ℝ) + S.G.k + 1 := by
    have : (0 : ℝ) ≤ S.G.r := Nat.cast_nonneg _
    have : (0 : ℝ) ≤ S.G.k := Nat.cast_nonneg _
    linarith
  have hNn : (0 : ℝ) ≤ S.Ntop := Nat.cast_nonneg _

  have hcpt : ∀ n, KB.CptCoef (p v).T.base (Formalism.FourierDecayAlt.P.PBASM.cutSeq S p f χ n v ε) := by
    intro n
    refine ((hc1 (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (p v) (f v) χ ε A₀ S.Ntop Formalism.FourierDecayAlt.P.PBASM.cutN
      (by rw [hl0]; exact hInD) hcut hε hCk hCC (le_trans ?_ hA) (fun n g => rfl)).1 n)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hR) (by positivity)
  by_cases hloc : D.IsLocPt h j ∧ D.IsLocPt h' j
  · have hH : D.IsLocPt (stdS S h) j := (isLocPt_toStd_iff _ _ hgpos h 1 j).2 hloc.1
    have hH' : D.IsLocPt (stdS S h') j := (isLocPt_toStd_iff _ _ hgpos h' 1 j).2 hloc.2
    have hroom : 10 * ((S.Ntop : ℝ) + 3 * (2 * (S.G.r : ℝ) + 1) + 1) ≤ S.cutHi v - S.cutLo v := by
      have hN : (S.Ntop : ℝ) = 20 * ((S.G.r : ℝ) + 1) := by
        unfold C.HidaSetting.Ntop C.Kst; push_cast; ring
      have h6 := (hGo v).1
      have hr : (0 : ℝ) ≤ S.G.r := Nat.cast_nonneg _
      have hN20 : (20 : ℝ) ≤ S.Ntop := by rw [hN]; linarith
      have hsq : (400 : ℝ) ≤ (S.Ntop : ℝ) ^ 2 := by nlinarith
      have hN3 : (400 : ℝ) * S.Ntop ≤ (S.Ntop : ℝ) ^ 3 := by
        calc (400 : ℝ) * S.Ntop ≤ (S.Ntop : ℝ) ^ 2 * S.Ntop := mul_le_mul_of_nonneg_right hsq hNn
          _ = (S.Ntop : ℝ) ^ 3 := by ring
      nlinarith
    obtain ⟨C, hC⟩ := hc0 (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (p v) (f v) χ ε A₀ S.Ntop
      Formalism.FourierDecayAlt.P.PBASM.cutN (S.cutLo v) (S.cutHi v) (by rw [hl0]; exact hInD) hcut hε hCk hCC
      (by
        have := thr_plus3 c0 (max (max (4 * c0) 0) c1) (((S.G.r : ℝ) + 1) ^ 4) (2 * (S.G.r : ℝ) + S.G.k + 1)
          S.Ntop A₀ (le_max_left _ _) hR hX hNn (by simpa [mul_assoc] using hA)
        push_cast
        linarith [this])
      (fun n g => rfl) (fun Y h1 h2 => by rw [hl0]; exact hCI v Y ⟨h1, h2⟩) (by push_cast; linarith [hroom])
      j hj (w.1 v) (by rw [hl0]; exact hw) hlen (stdS S h) (stdS S h') hH hH'
    set lam := lamS S j with hlam
    have hlam_pos : 0 < lam := lamS_pos S hgpos j
    set tw : ℝ := 2 * Real.pi / ((S.g : ℝ) * lam) with htw
    have htw_pos : 0 < tw := by rw [htw]; positivity
    have hsW : ∀ l : ℂ, ‖sW S j l‖ = tw * ‖l‖ := by
      intro l
      unfold sW
      rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_of_nonneg htw_pos.le, one_mul]
    set K1 : ℝ := |Kg S j h h'| with hK1
    set K2 : ℝ := abs (Kg S j h h' * |(lamS S j ^ 2)⁻¹|) with hK2
    refine ⟨K1 * |C| * (max 1 lam⁻¹) ^ 3 + K2 * |C| * (max 1 tw⁻¹) ^ 3, fun n => ⟨fun c hc => ?_, fun l => ?_⟩⟩
    · have hb : 0 ≤ ((1 + ‖c‖) ^ 3)⁻¹ := by positivity
      have hlc : (lam : ℂ) * c ≠ 0 := mul_ne_zero (by exact_mod_cast hlam_pos.ne') hc
      have hb1 := (hC n).1 _ hlc
      rw [gramLoc_setC_app hB _ v ε j hj (w.1 v) h h' hsz hsz' c hc, mul_assoc, norm_mul, Complex.norm_real,
        Real.norm_eq_abs]
      have hnl : ‖(lam : ℂ) * c‖ = lam * ‖c‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hlam_pos.le]
      rw [hnl] at hb1
      have := bound_absorb K1 C ((max 1 lam⁻¹) ^ 3) (((1 + lam * ‖c‖) ^ 3)⁻¹) _ _ (by positivity) (by positivity)
        hb (abs_nonneg _) hb1 (decay_scale lam ‖c‖ hlam_pos (norm_nonneg _))
      have h2 : 0 ≤ K2 * |C| * (max 1 tw⁻¹) ^ 3 * ((1 + ‖c‖) ^ 3)⁻¹ := by positivity
      calc K1 * _ ≤ (K1 * |C| * (max 1 lam⁻¹) ^ 3) * ((1 + ‖c‖) ^ 3)⁻¹ := this
        _ ≤ _ := by nlinarith
    · have hb : 0 ≤ ((1 + ‖l‖) ^ 3)⁻¹ := by positivity
      have hb1 := (hC n).2 (sW S j l)
      rw [hsW l] at hb1
      rw [int_gramLoc_setC hPS hB _ v ε (hcpt n) j hj (w.1 v) hw l h h' hloc.1 hloc.2, norm_mul,
        Complex.norm_real, Real.norm_eq_abs]
      have := bound_absorb K2 C ((max 1 tw⁻¹) ^ 3) (((1 + tw * ‖l‖) ^ 3)⁻¹) _ _ (by positivity) (by positivity)
        hb (abs_nonneg _) hb1 (decay_scale tw ‖l‖ htw_pos (norm_nonneg _))
      have h2 : 0 ≤ K1 * |C| * (max 1 lam⁻¹) ^ 3 * ((1 + ‖l‖) ^ 3)⁻¹ := by positivity
      calc K2 * _ ≤ (K2 * |C| * (max 1 tw⁻¹) ^ 3) * ((1 + ‖l‖) ^ 3)⁻¹ := this
        _ ≤ _ := by nlinarith
  · have hz : ∀ (n : ℕ) (c : ℂ), (setC S p (Formalism.FourierDecayAlt.P.PBASM.cutSeq S p f χ n)).gramLoc v ε (j + 1) (w.1 v)
        (h ++ [(1, c)]) (h' ++ [(1, c)]) = 0 := by
      intro n c
      rw [gramLoc_setC hB, rr_zero_of_not, mul_zero]
      unfold stdS
      rw [isLocPt_toStd_iff _ _ hgpos, isLocPt_toStd_iff _ _ hgpos]
      rintro ⟨h1, h2⟩
      exact hloc ⟨⟨fun b hb => h1.1 b (List.mem_append_left _ hb), hsz⟩,
        ⟨fun b hb => h2.1 b (List.mem_append_left _ hb), hsz'⟩⟩
    refine ⟨0, fun n => ⟨fun c _ => ?_, fun l => ?_⟩⟩
    · rw [hz n c]; simp
    · simp [hz n]

end

end Formalism.FourierDecayAlt.P.StandardPairingDecay

theorem Formalism.FourierDecayAlt.P.uniform_decay_of_place : Formalism.FourierDecayAlt.P.StandardPairingDecay.DecayUnifOfPlace :=
  fun hP hRH hHT hD => Formalism.FourierDecayAlt.P.StandardPairingDecay.decayUnif_of_place hP hRH hHT hD
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.FormWaveMDiff
open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBO

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd
open scoped ComplexConjugate

theorem fsv_mul_fsv (a b t : ℂ) : P5.fsv a t * P5.fsv b t = P5.fsv (a + b) t := by
  unfold P5.fsv
  rw [← Complex.exp_add]
  congr 1
  simp only [map_add (f := _)]
  ring

section wave

variable {k ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem uInv_cons_apply (s : ℂ) (l : C.Letter) (w : List C.Letter)
    (x : Wd.Ix (Fin (w.length + 1)) → B.Mat k ρ → (Wq →L[ℂ] Wp)) (e : Wd.Ix (Fin (w.length + 1))) :
    KB.uInv s (l :: w) x e =
      if e 0 = 0 then KB.uInv s w (fun e' => x (Fin.cons (0 : Fin 2) e')) (fun a => e a.succ)
      else KB.uInv s w (fun e' => x (Fin.cons (1 : Fin 2) e')) (fun a => e a.succ) +
        (if l.1 then s else conj s) • KB.uInv s w (fun e' => x (Fin.cons (0 : Fin 2) e')) (fun a => e a.succ) :=
  rfl

theorem uInv_cons0 (s : ℂ) (l : C.Letter) (w : List C.Letter)
    (x : Wd.Ix (Fin (w.length + 1)) → B.Mat k ρ → (Wq →L[ℂ] Wp)) :
    (fun e' => KB.uInv s (l :: w) x (Fin.cons (0 : Fin 2) e')) = KB.uInv s w (fun e' => x (Fin.cons 0 e')) := by
  funext e'
  rw [uInv_cons_apply, ite_eq_left (by simp)]
  simp

theorem uInv_cons1 (s : ℂ) (l : C.Letter) (w : List C.Letter)
    (x : Wd.Ix (Fin (w.length + 1)) → B.Mat k ρ → (Wq →L[ℂ] Wp)) :
    (fun e' => KB.uInv s (l :: w) x (Fin.cons (1 : Fin 2) e')) =
      KB.uInv s w (fun e' => x (Fin.cons 1 e')) + (if l.1 then s else conj s) • KB.uInv s w (fun e' => x (Fin.cons 0 e')) := by
  funext e'
  rw [uInv_cons_apply, ite_eq_right (by simp)]
  simp only [Fin.cons_succ, Pi.add_apply, Pi.smul_apply]

theorem uInv_comp (s σ : ℂ) : ∀ (w : List C.Letter) (x : Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp)),
    KB.uInv s w (KB.uInv σ w x) = KB.uInv (s + σ) w x
  | [], x => rfl
  | l :: w, x => by
    have hlinear : ∀ (v : List C.Letter)
        (a b : Wd.Ix (Fin v.length) → B.Mat k ρ → (Wq →L[ℂ] Wp)) (c : ℂ),
        KB.uInv s v (a + c • b) = KB.uInv s v a + c • KB.uInv s v b := by
      intro v
      induction v with
      | nil => intros; rfl
      | cons m v ih =>
        intro a b c
        funext e
        have htail (j : Fin 2) :
            KB.uInv s v (fun i => a (Fin.cons j i) + c • b (Fin.cons j i)) (fun i => e i.succ) =
              KB.uInv s v (fun i => a (Fin.cons j i)) (fun i => e i.succ) +
                c • KB.uInv s v (fun i => b (Fin.cons j i)) (fun i => e i.succ) :=
          congrFun (ih (fun i => a (Fin.cons j i)) (fun i => b (Fin.cons j i)) c) (fun i => e i.succ)
        by_cases h : e 0 = 0
        · simpa only [uInv_cons_apply, ite_eq_left h, Pi.add_apply, Pi.smul_apply] using htail 0
        · simp only [uInv_cons_apply, ite_eq_right h, Pi.add_apply, Pi.smul_apply, htail 0, htail 1,
            smul_add, smul_smul, mul_comm c]
          abel
    funext e
    rw [uInv_cons_apply, uInv_cons0, uInv_cons1, uInv_cons_apply (s + σ), hlinear,
      uInv_comp s σ w, uInv_comp s σ w]
    split_ifs with h0 hl
    · rfl
    · simp only [Pi.add_apply, Pi.smul_apply]
      rw [add_assoc, ← add_smul, add_comm σ s]
    · simp only [Pi.add_apply, Pi.smul_apply, map_add (f := _)]
      rw [add_assoc, ← add_smul, add_comm (conj σ) (conj s)]

theorem uInv_smulFun (s : ℂ) (φ : B.Mat k ρ → ℂ) : ∀ (w : List C.Letter)
    (x : Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp)),
    KB.uInv s w (fun e g => φ g • x e g) = fun e g => φ g • KB.uInv s w x e g
  | [], x => rfl
  | l :: w, x => by
    funext e g
    have ih0 := congrFun (congrFun (uInv_smulFun s φ w (fun i => x (Fin.cons 0 i))) (fun a => e a.succ)) g
    have ih1 := congrFun (congrFun (uInv_smulFun s φ w (fun i => x (Fin.cons 1 i))) (fun a => e a.succ)) g
    by_cases h : e 0 = 0
    · simpa only [uInv_cons_apply, ite_eq_left h] using ih0
    · simp only [uInv_cons_apply, ite_eq_right h, Pi.add_apply, Pi.smul_apply, ih0, ih1, smul_add]
      rw [smul_comm (φ g)]

theorem waveG_comp (Bs : B.RealPlaceData k ρ Wp Wq) (s σ : ℂ) (w : List C.Letter)
    (x : Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp)) :
    KB.waveG Bs s w (KB.waveG Bs σ w x) = KB.waveG Bs (s + σ) w x := by
  have e : KB.waveG Bs σ w x = fun e g => P5.fsv σ (Dmin k ρ Bs.z Bs.z' g ⟨1, by omega⟩) • KB.uInv σ w x e g := rfl
  funext e' g
  rw [e]
  show P5.fsv s (Dmin k ρ Bs.z Bs.z' g ⟨1, by omega⟩) •
      KB.uInv s w (fun e g => P5.fsv σ (Dmin k ρ Bs.z Bs.z' g ⟨1, by omega⟩) • KB.uInv σ w x e g) e' g =
    P5.fsv (s + σ) (Dmin k ρ Bs.z Bs.z' g ⟨1, by omega⟩) • KB.uInv (s + σ) w x e' g
  rw [uInv_smulFun, uInv_comp, smul_smul, fsv_mul_fsv]

theorem onOld_eq_self {w : List C.Letter}
    (M : (Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp)) → Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp))
    (hM : ∀ x, M x = x) :
    ∀ (ys : List ℝ) (x : Wd.Ix (Fin (KB.plusW ys w).length) → B.Mat k ρ → (Wq →L[ℂ] Wp)), KB.onOld M ys x = x
  | [], x => hM x
  | _ :: ys, x => by
    funext e
    show KB.onOld M ys (fun e' => x (Fin.cons (e (0 : Fin ((KB.plusW ys w).length + 1))) e')) (fun a => e a.succ) = x e
    rw [onOld_eq_self M hM ys]
    exact congrArg x (Fin.cons_self_tail e)

theorem mDiff_eq (Bs : B.RealPlaceData k ρ Wp Wq) (σ : ℂ) (w : List C.Letter)
    (x : Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp)) :
    mDiff Bs σ w x = KB.waveG Bs (3 * σ) w x - (3 : ℂ) • KB.waveG Bs (2 * σ) w x +
      (3 : ℂ) • KB.waveG Bs σ w x - x := by
  have hV : ∀ y, waveL Bs σ w y = KB.waveG Bs σ w y := fun _ => rfl
  have e2 : KB.waveG Bs σ w (KB.waveG Bs σ w x) = KB.waveG Bs (2 * σ) w x := by
    rw [waveG_comp]; congr 1; ring
  have e3 : KB.waveG Bs σ w (KB.waveG Bs (2 * σ) w x) = KB.waveG Bs (3 * σ) w x := by
    rw [waveG_comp]; congr 1; ring
  simp only [mDiff, pow_succ, pow_zero, one_mul, mul_apply_eq_comp, LinearMap.sub_apply, one_apply_eq_self,
    map_sub, hV]
  rw [e2, e3]
  module

end wave

section forms

variable {k ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem mDiff_apply_eq (Bs : B.RealPlaceData k ρ Wp Wq) (σ : ℂ) (w : List C.Letter)
    (x : Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp)) (e : Wd.Ix (Fin w.length)) :
    mDiff Bs σ w x e = KB.waveG Bs (3 * σ) w x e + (-3 : ℂ) • KB.waveG Bs (2 * σ) w x e +
      (3 : ℂ) • KB.waveG Bs σ w x e + (-1 : ℂ) • x e := by
  rw [mDiff_eq]
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply]
  module

theorem mDiff_nice (Bs : B.RealPlaceData k ρ Wp Wq) (σ : ℂ) (w : List C.Letter) (ε : ℝ)
    (x : Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp)) (hx : ∀ e, JC.NiceCoef Bs ε (x e)) :
    ∀ e, JC.NiceCoef Bs ε (mDiff Bs σ w x e) := by
  intro e
  rw [mDiff_apply_eq]
  have hw : ∀ t, JC.NiceCoef Bs ε (KB.waveG Bs t w x e) := fun t => Formalism.FourierDecayAlt.P.PBFV.waveG_nice Bs ε t w x hx e
  exact Formalism.FourierDecayAlt.P.JCx2.mn_nice_add (Formalism.FourierDecayAlt.P.JCx2.mn_nice_add (Formalism.FourierDecayAlt.P.JCx2.mn_nice_add (hw _)
    (Formalism.FourierDecayAlt.P.JCx2.mn_nice_smul _ (hw _))) (Formalism.FourierDecayAlt.P.JCx2.mn_nice_smul _ (hw _)))
    (Formalism.FourierDecayAlt.P.JCx2.mn_nice_smul _ (hx e))

end forms

section place

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem mDiff_cpt (hP : P5.ThmPActualCpt) (P : M.Par) (p : KB.Pl P Wp Wq) (j : ℕ) (hj : j ≤ P.r)
    (w : List C.Letter) (hw : KB.CutWord P p.l0 w) (σ : ℂ)
    (x : Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) (hx : ∀ e, KB.CptCoef (p.T.bs j) (x e)) :
    ∀ e, KB.CptCoef (p.T.bs j) (mDiff (p.T.bs j) σ w x e) := by
  have hc : ∀ t e, KB.CptCoef (p.T.bs j) (KB.waveG (p.T.bs j) t w x e) := fun t =>
    (Formalism.FourierDecayAlt.P.vector_isomorphism_compact_support hP Wp Wq P p j hj w hw t x x hx hx).1
  intro e
  rw [mDiff_apply_eq]
  exact Formalism.FourierDecayAlt.P.PBG.cpt_add_smul _ _ (Formalism.FourierDecayAlt.P.PBG.cpt_add_smul _ _
    (Formalism.FourierDecayAlt.P.PBG.cpt_add_smul _ _ (hc _ e) (hc _ e)) (hc _ e)) (hx e)

theorem form_wave_mDiff (P : M.Par) (p : KB.Pl P Wp Wq) (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter)
    (x y : Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp))
    (hx : ∀ e, KB.CptCoef (p.T.bs j) (x e)) (hy : ∀ e, KB.CptCoef (p.T.bs j) (y e)) (s σ : ℂ) :
    p.form j hj w (KB.waveG (p.T.bs j) s w (mDiff (p.T.bs j) σ w x)) y =
      p.form j hj w (KB.waveG (p.T.bs j) (s + 3 * σ) w x) y - 3 * p.form j hj w (KB.waveG (p.T.bs j) (s + 2 * σ) w x) y +
        3 * p.form j hj w (KB.waveG (p.T.bs j) (s + σ) w x) y - p.form j hj w (KB.waveG (p.T.bs j) s w x) y := by
  obtain ⟨ε, hε, hxn⟩ := nice_common (p.T.bs j) hx
  obtain ⟨ε', hε', hyn⟩ := nice_common (p.T.bs j) hy
  have hd : ∀ t, Formalism.FourierDecayAlt.P.PBG.DecV (KB.waveG (p.T.bs j) t w x) := fun t =>
    Formalism.FourierDecayAlt.P.PBG.decV_of_nice (Formalism.FourierDecayAlt.P.PBFV.waveG_nice (p.T.bs j) ε t w x hxn)
  have hdy : Formalism.FourierDecayAlt.P.PBG.DecV y := Formalism.FourierDecayAlt.P.PBG.decV_of_nice hyn
  have hV : ∀ z, waveL (p.T.bs j) s w z = KB.waveG (p.T.bs j) s w z := fun _ => rfl
  have hW : KB.waveG (p.T.bs j) s w (mDiff (p.T.bs j) σ w x) =
      KB.waveG (p.T.bs j) (s + 3 * σ) w x + (-3 : ℂ) • KB.waveG (p.T.bs j) (s + 2 * σ) w x +
        (3 : ℂ) • KB.waveG (p.T.bs j) (s + σ) w x + (-1 : ℂ) • KB.waveG (p.T.bs j) s w x := by
    rw [mDiff_eq]
    calc KB.waveG (p.T.bs j) s w (KB.waveG (p.T.bs j) (3 * σ) w x - (3 : ℂ) • KB.waveG (p.T.bs j) (2 * σ) w x +
          (3 : ℂ) • KB.waveG (p.T.bs j) σ w x - x)
        = waveL (p.T.bs j) s w (KB.waveG (p.T.bs j) (3 * σ) w x - (3 : ℂ) • KB.waveG (p.T.bs j) (2 * σ) w x +
          (3 : ℂ) • KB.waveG (p.T.bs j) σ w x - x) := rfl
      _ = waveL (p.T.bs j) s w (KB.waveG (p.T.bs j) (3 * σ) w x) -
            (3 : ℂ) • waveL (p.T.bs j) s w (KB.waveG (p.T.bs j) (2 * σ) w x) +
            (3 : ℂ) • waveL (p.T.bs j) s w (KB.waveG (p.T.bs j) σ w x) - waveL (p.T.bs j) s w x := by
          simp only [map_sub, map_add (f := _), map_smul]
      _ = _ := by
          simp only [hV, waveG_comp]
          module
  rw [hW]
  unfold KB.Pl.form
  set A3 := KB.waveG (p.T.bs j) (s + 3 * σ) w x
  set A2 := KB.waveG (p.T.bs j) (s + 2 * σ) w x
  set A1 := KB.waveG (p.T.bs j) (s + σ) w x
  set A0 := KB.waveG (p.T.bs j) s w x
  have d32 := Formalism.FourierDecayAlt.P.PBG.decV_add (hd (s + 3 * σ)) (Formalism.FourierDecayAlt.P.PBG.decV_smul (-3 : ℂ) (hd (s + 2 * σ)))
  have d321 := Formalism.FourierDecayAlt.P.PBG.decV_add d32 (Formalism.FourierDecayAlt.P.PBG.decV_smul (3 : ℂ) (hd (s + σ)))
  rw [Formalism.FourierDecayAlt.P.PBG.form_sesq_left P p.T (M.sgn P p.l0) ⟨j, by omega⟩ w (A3 + (-3 : ℂ) • A2 + (3 : ℂ) • A1) A0 y
      (-1) d321 (hd s) hdy,
    Formalism.FourierDecayAlt.P.PBG.form_sesq_left P p.T (M.sgn P p.l0) ⟨j, by omega⟩ w (A3 + (-3 : ℂ) • A2) A1 y 3 d32
      (hd (s + σ)) hdy,
    Formalism.FourierDecayAlt.P.PBG.form_sesq_left P p.T (M.sgn P p.l0) ⟨j, by omega⟩ w A3 A2 y (-3) (hd (s + 3 * σ))
      (hd (s + 2 * σ)) hdy]
  ring

end place

end Formalism.FourierDecayAlt.P.PBO
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.XiBound
open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBO

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.P5

theorem xi_bound (hP : P5.ThmPActualCpt) {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (hF : KB.CptCoef p.T.base F)
    (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter) (hw : KB.CutWord P p.l0 w) (h h' : C.LPt) (hh : D.IsLocPt h j)
    (hh' : D.IsLocPt h' j)
    (grid : Fin 3 → Fin (2 * j + 1) → ℝ) (hinj : ∀ a, Function.Injective (grid a))
    (hgr : ∀ n : Fin 3 → Fin (2 * j + 1), KB.CutWord P p.l0 (KB.plusW (List.ofFn fun a => grid a (n a)) w) ∧
        KB.CutWord P p.l0 (KB.minusW (List.ofFn fun a => grid a (n a)) w) ∧
        (List.ofFn fun a => grid a (n a)).Pairwise (fun y y' => 2 < |y - y'|))
    (Mo : (Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) →ₗ[ℂ]
      (Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)))
    (hMo : ∀ ε x, (∀ e, JC.NiceCoef (p.T.bs j) ε (x e)) → ∀ e, JC.NiceCoef (p.T.bs j) ε (Mo x e))
    (hMoC : ∀ x, (∀ e, KB.CptCoef (p.T.bs j) (x e)) → ∀ e, KB.CptCoef (p.T.bs j) (Mo x e)) (a b : ℝ)
    (hA0 : ‖p.form j hj w (Mo (KB.slv p.T F j hj w h hh.2)) (Mo (KB.slv p.T F j hj w h hh.2))‖ ≤ a)
    (hB0 : ‖p.form j hj w (KB.slv p.T F j hj w h' hh'.2) (KB.slv p.T F j hj w h' hh'.2)‖ ≤ b)
    (hA : ∀ n : Fin 3 → Fin (2 * j + 1), ‖p.form j hj (KB.plusW (List.ofFn fun a => grid a (n a)) w)
        (KB.onOld Mo _ (KB.slv p.T F j hj (KB.plusW (List.ofFn fun a => grid a (n a)) w) h hh.2))
        (KB.onOld Mo _ (KB.slv p.T F j hj (KB.plusW (List.ofFn fun a => grid a (n a)) w) h hh.2))‖ ≤ a)
    (hB : ∀ n : Fin 3 → Fin (2 * j + 1), ‖p.form j hj (KB.minusW (List.ofFn fun a => grid a (n a)) w)
        (KB.slv p.T F j hj (KB.minusW (List.ofFn fun a => grid a (n a)) w) h' hh'.2)
        (KB.slv p.T F j hj (KB.minusW (List.ofFn fun a => grid a (n a)) w) h' hh'.2)‖ ≤ b) (s : ℂ) :
    ‖p.form j hj w (KB.waveG (p.T.bs j) s w (Mo (KB.slv p.T F j hj w h hh.2))) (KB.slv p.T F j hj w h' hh'.2)‖ ≤
      8 * (1 + ∑ n : Fin 3 → Fin (2 * j + 1), |∏ a, F7.lagCo (grid a) (n a)| /
        Real.sqrt (((List.ofFn fun a => grid a (n a)).map fun y : ℝ => (Wd.qw (M.qC P) (D.positionted w) y).re).prod)) *
        Real.sqrt (a * b) * ((1 + ‖s‖) ^ 3)⁻¹ := by
  have ha : 0 ≤ a := (norm_nonneg _).trans hA0
  have hb : 0 ≤ b := (norm_nonneg _).trans hB0
  set x := KB.slv p.T F j hj w h hh.2 with hxdef
  set y := KB.slv p.T F j hj w h' hh'.2 with hydef
  have hxc : ∀ e, KB.CptCoef (p.T.bs j) (x e) := fun e =>
    Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F j hj w h hh hF e
  have hyc : ∀ e, KB.CptCoef (p.T.bs j) (y e) := fun e =>
    Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F j hj w h' hh' hF e
  set R := Real.sqrt (a * b) with hRdef
  have hR : 0 ≤ R := Real.sqrt_nonneg _

  have hCS : ‖p.form j hj w (KB.waveG (p.T.bs j) s w (Mo x)) y‖ ≤ R := by
    obtain ⟨-, hss⟩ := Formalism.FourierDecayAlt.P.size_standard_compact hP Wp Wq P p j hj w [] hw hw List.Pairwise.nil
    obtain ⟨hWc, hiso⟩ := Formalism.FourierDecayAlt.P.vector_isomorphism_compact_support hP Wp Wq P p j hj w hw s (Mo x) (Mo x) (hMoC x hxc)
      (hMoC x hxc)
    have key := hss (KB.waveG (p.T.bs j) s w (Mo x)) y hWc hyc
    simp only [List.map_nil, List.prod_nil, mul_one] at key
    change ‖p.form j hj w (KB.waveG (p.T.bs j) s w (Mo x)) y‖ ^ 2 ≤
      (p.form j hj w (KB.waveG (p.T.bs j) s w (Mo x)) (KB.waveG (p.T.bs j) s w (Mo x))).re *
        (p.form j hj w y y).re at key
    rw [hiso] at key
    have h1 := Complex.abs_re_le_norm (p.form j hj w (Mo x) (Mo x))
    have h2 := Complex.abs_re_le_norm (p.form j hj w y y)
    have hab : (p.form j hj w (Mo x) (Mo x)).re * (p.form j hj w y y).re ≤ a * b := by
      calc (p.form j hj w (Mo x) (Mo x)).re * (p.form j hj w y y).re
          ≤ |(p.form j hj w (Mo x) (Mo x)).re * (p.form j hj w y y).re| := le_abs_self _
        _ = |(p.form j hj w (Mo x) (Mo x)).re| * |(p.form j hj w y y).re| := abs_mul _ _
        _ ≤ a * b := mul_le_mul (h1.trans hA0) (h2.trans hB0) (abs_nonneg _) ha
    have habs := Real.abs_le_sqrt (key.trans hab)
    rwa [abs_of_nonneg (norm_nonneg _)] at habs

  set K := ∑ n : Fin 3 → Fin (2 * j + 1), |∏ a, F7.lagCo (grid a) (n a)| /
        Real.sqrt (((List.ofFn fun a => grid a (n a)).map fun y : ℝ => (Wd.qw (M.qC P) (D.positionted w) y).re).prod)
    with hKdef
  have hK : 0 ≤ K := Finset.sum_nonneg fun n _ => div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  have hT : ‖s‖ ^ 3 * ‖p.form j hj w (KB.waveG (p.T.bs j) s w (Mo x)) y‖ ≤ K * R := by
    refine (wave_bound3 hP P p F hF j hj w h h' hh hh' grid hinj hgr Mo hMo hMoC s).trans ?_
    rw [hKdef, Finset.sum_mul]
    refine Finset.sum_le_sum fun n _ => ?_
    obtain ⟨hc1, hc2, hpw⟩ := hgr n
    obtain ⟨hq, -⟩ := Formalism.FourierDecayAlt.P.size_standard_compact hP Wp Wq P p j hj w _ hc1 hc2 hpw
    have hqpos : 0 < ((List.ofFn fun a => grid a (n a)).map fun y : ℝ => (Wd.qw (M.qC P) (D.positionted w) y).re).prod := by
      refine List.prod_pos fun c hc => ?_
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hc
      exact hq y hy
    rw [show ∀ u v x : ℝ, u / v * x = u * (x / v) from fun u v x => by ring]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg (∏ a, F7.lagCo (grid a) (n a)))
    rw [← Real.sqrt_div' _ hqpos.le]
    refine Real.sqrt_le_sqrt (div_le_div_of_nonneg_right ?_ hqpos.le)
    have h1 := Complex.abs_re_le_norm (p.form j hj (KB.plusW (List.ofFn fun a => grid a (n a)) w)
        (KB.onOld Mo _ (KB.slv p.T F j hj (KB.plusW (List.ofFn fun a => grid a (n a)) w) h hh.2))
        (KB.onOld Mo _ (KB.slv p.T F j hj (KB.plusW (List.ofFn fun a => grid a (n a)) w) h hh.2)))
    have h2 := Complex.abs_re_le_norm (p.form j hj (KB.minusW (List.ofFn fun a => grid a (n a)) w)
        (KB.slv p.T F j hj (KB.minusW (List.ofFn fun a => grid a (n a)) w) h' hh'.2)
        (KB.slv p.T F j hj (KB.minusW (List.ofFn fun a => grid a (n a)) w) h' hh'.2))
    exact (le_abs_self _).trans ((abs_mul _ _).le.trans
      (mul_le_mul (h1.trans (hA n)) (h2.trans (hB n)) (abs_nonneg _) ha))

  have hu : 0 < 1 + ‖s‖ := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ (pow_pos hu 3)]
  by_cases hs : ‖s‖ ≤ 1
  · have hu8 : (1 + ‖s‖) ^ 3 ≤ 8 := by
      calc (1 + ‖s‖) ^ 3 ≤ 2 ^ 3 := pow_le_pow_left₀ hu.le (by linarith) 3
        _ = 8 := by norm_num
    calc ‖p.form j hj w (KB.waveG (p.T.bs j) s w (Mo x)) y‖ * (1 + ‖s‖) ^ 3 ≤ R * 8 :=
          mul_le_mul hCS hu8 (by positivity) hR
      _ ≤ 8 * (1 + K) * R := by nlinarith
  · push Not at hs
    have hu8 : (1 + ‖s‖) ^ 3 ≤ 8 * ‖s‖ ^ 3 := by
      calc (1 + ‖s‖) ^ 3 ≤ (2 * ‖s‖) ^ 3 := pow_le_pow_left₀ hu.le (by linarith) 3
        _ = 8 * ‖s‖ ^ 3 := by ring
    calc ‖p.form j hj w (KB.waveG (p.T.bs j) s w (Mo x)) y‖ * (1 + ‖s‖) ^ 3
        ≤ ‖p.form j hj w (KB.waveG (p.T.bs j) s w (Mo x)) y‖ * (8 * ‖s‖ ^ 3) :=
          mul_le_mul_of_nonneg_left hu8 (norm_nonneg _)
      _ = 8 * (‖s‖ ^ 3 * ‖p.form j hj w (KB.waveG (p.T.bs j) s w (Mo x)) y‖) := by ring
      _ ≤ 8 * (K * R) := by linarith
      _ ≤ 8 * (1 + K) * R := by nlinarith

end Formalism.FourierDecayAlt.P.PBO
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.NormFsvSubOnePow
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBO

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.P5

theorem transform_diff3 {φ : ℂ → ℂ} (hφ : Continuous φ) (hi : Integrable φ) (σ s : ℂ) :
    ∫ t, fsv s t * ((fsv σ t - 1) ^ 3 * φ t) =
      (∫ t, fsv (s + 3 * σ) t * φ t) - 3 * (∫ t, fsv (s + 2 * σ) t * φ t) + 3 * (∫ t, fsv (s + σ) t * φ t) -
        ∫ t, fsv s t * φ t := by
  have e : ∀ t, fsv s t * ((fsv σ t - 1) ^ 3 * φ t) =
      fsv (s + 3 * σ) t * φ t - 3 * (fsv (s + 2 * σ) t * φ t) + 3 * (fsv (s + σ) t * φ t) - fsv s t * φ t := by
    intro t
    have e1 : fsv (s + σ) t = fsv s t * fsv σ t := (fsv_mul_fsv s σ t).symm
    have e2 : fsv (s + 2 * σ) t = fsv s t * fsv σ t * fsv σ t := by
      rw [fsv_mul_fsv, fsv_mul_fsv]; congr 1; ring
    have e3 : fsv (s + 3 * σ) t = fsv s t * fsv σ t * fsv σ t * fsv σ t := by
      rw [fsv_mul_fsv, fsv_mul_fsv, fsv_mul_fsv]; congr 1; ring
    rw [e1, e2, e3]; ring
  simp only [e]
  have i0 := integrable_fsv_mul hφ hi s
  have i1 := integrable_fsv_mul hφ hi (s + σ)
  have i2 := integrable_fsv_mul hφ hi (s + 2 * σ)
  have i3 := integrable_fsv_mul hφ hi (s + 3 * σ)
  have j1 : Integrable (fun t => fsv (s + 3 * σ) t * φ t - 3 * (fsv (s + 2 * σ) t * φ t)) := i3.sub (i2.const_mul 3)
  have j2 : Integrable (fun t => fsv (s + 3 * σ) t * φ t - 3 * (fsv (s + 2 * σ) t * φ t) +
      3 * (fsv (s + σ) t * φ t)) := j1.add (i1.const_mul 3)
  rw [integral_sub j2 i0, integral_add j1 (i1.const_mul 3), integral_sub i3 (i2.const_mul 3),
    integral_const_mul, integral_const_mul]

theorem norm_fsv_sub_one_pow (σ t : ℂ) : ‖(fsv σ t - 1) ^ 3‖ ≤ 8 := by
  rw [norm_pow]
  have : ‖fsv σ t - 1‖ ≤ 2 := (norm_sub_le _ _).trans (by rw [norm_fsv, norm_one]; norm_num)
  calc ‖fsv σ t - 1‖ ^ 3 ≤ 2 ^ 3 := pow_le_pow_left₀ (norm_nonneg _) this 3
    _ = 8 := by norm_num


set_option maxHeartbeats 1600000 in
theorem decayUnif_of (hRH : KB.RadHead) (hHT : KB.HeadTop) (hWDF : WaveDiffForm) : DecayUnif := by
  intro hP Cb
  obtain ⟨CcF, hFL⟩ := Formalism.FourierDecayAlt.P.limit_of_module_forms Cb
  obtain ⟨CcW, hWD⟩ := hWDF hP Cb
  refine ⟨max CcF CcW, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f χ ε A N cut lo hi hθ hχ hε hf hfA hthr hcut hon hroom j hj w hw hN h h' hh hh'
  have hX : 0 ≤ ((P.r : ℝ) + 1) ^ 4 * (((N + 3 : ℕ) : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 +
      (2 * (P.r : ℝ) + P.k + 1) ^ 3) := by positivity
  have hthrF : CcF * ((P.r : ℝ) + 1) ^ 4 * (((N + 3 : ℕ) : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 +
      (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A := by
    have := mul_le_mul_of_nonneg_right (le_max_left CcF CcW) hX
    nlinarith
  have hthrW : CcW * ((P.r : ℝ) + 1) ^ 4 * (((N + 3 : ℕ) : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 +
      (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A := by
    have := mul_le_mul_of_nonneg_right (le_max_right CcF CcW) hX
    nlinarith
  obtain ⟨hcpt, hlim⟩ := hFL Wp Wq P p f χ ε A (N + 3) cut hθ hχ hε hf hfA hthrF hcut
  have hWDa := hWD Wp Wq P p f χ ε A N cut hθ hχ hε hf hfA hthrW hcut j hj w hw hN h hh

  obtain ⟨grid, hinj, hgr⟩ := grid_exists P p.l0 lo hi hon w hw j (by
    have h1 : (w.length : ℝ) ≤ N := by exact_mod_cast hN
    have h2 : (j : ℝ) ≤ P.r := by exact_mod_cast hj
    nlinarith)
  have hlp : ∀ n : Fin 3 → Fin (2 * j + 1), (KB.plusW (List.ofFn fun a => grid a (n a)) w).length ≤ N + 3 := by
    intro n; rw [Formalism.FourierDecayAlt.P.PBD.plusW_eq]; simp; omega
  have hlm : ∀ n : Fin 3 → Fin (2 * j + 1), (KB.minusW (List.ofFn fun a => grid a (n a)) w).length ≤ N + 3 := by
    intro n; rw [Formalism.FourierDecayAlt.P.PBD.minusW_eq]; simp; omega

  have bnd : ∀ (w' : List C.Letter), KB.CutWord P p.l0 w' → w'.length ≤ N + 3 → ∀ a : C.LPt,
      ∃ B, 0 ≤ B ∧ ∀ n, ‖p.RR (fun g => cut n g • D.cutF p.T.base χ f ε g) j w' a a‖ ≤ B :=
    fun w' hw' hl a => bdd_of_tendsto (hlim j w' hw' hl a a)
  choose Bp hBp0 hBp using fun n => bnd _ (hgr n).1 (hlp n) h
  choose Bm hBm0 hBm using fun n => bnd _ (hgr n).2.1 (hlm n) h'
  obtain ⟨Bh, hBh0, hBh⟩ := bnd w hw (by omega) h
  obtain ⟨Bh', hBh'0, hBh'⟩ := bnd w hw (by omega) h'
  set B := Bh + Bh' + ∑ n, (Bp n + Bm n) with hBdef
  have hS0 : 0 ≤ ∑ n, (Bp n + Bm n) := Finset.sum_nonneg fun n _ => add_nonneg (hBp0 n) (hBm0 n)
  have hB0 : 0 ≤ B := by positivity
  have hBpB : ∀ n, Bp n ≤ B := fun n => by
    have := Finset.single_le_sum (f := fun n => Bp n + Bm n) (fun n _ => add_nonneg (hBp0 n) (hBm0 n))
      (Finset.mem_univ n)
    linarith [hBm0 n]
  have hBmB : ∀ n, Bm n ≤ B := fun n => by
    have := Finset.single_le_sum (f := fun n => Bp n + Bm n) (fun n _ => add_nonneg (hBp0 n) (hBm0 n))
      (Finset.mem_univ n)
    linarith [hBp0 n]
  have hBhB : Bh ≤ B := by linarith
  have hBh'B : Bh' ≤ B := by linarith

  choose Cw hCw using fun n : Fin 3 → Fin (2 * j + 1) => hWDa (List.ofFn fun a => grid a (n a)) (by simp)
    (hgr n).1
  obtain ⟨C0, hC0⟩ := hWDa [] (by simp) hw
  set CW := |C0| + ∑ n, |Cw n| with hCWdef
  have hCW0 : 0 ≤ CW := by positivity
  have hCwW : ∀ n, Cw n ≤ CW := fun n => by
    have := Finset.single_le_sum (f := fun n => |Cw n|) (fun n _ => abs_nonneg _) (Finset.mem_univ n)
    linarith [le_abs_self (Cw n), abs_nonneg C0]
  have hC0W : C0 ≤ CW := by
    linarith [le_abs_self C0, Finset.sum_nonneg (fun n (_ : n ∈ Finset.univ) => abs_nonneg (Cw n))]

  set K := ∑ n : Fin 3 → Fin (2 * j + 1), |∏ a, F7.lagCo (grid a) (n a)| /
        Real.sqrt (((List.ofFn fun a => grid a (n a)).map fun y : ℝ => (Wd.qw (M.qC P) (D.positionted w) y).re).prod)
    with hKdef
  have hK : 0 ≤ K := Finset.sum_nonneg fun n _ => div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  set T1 := 8 * (1 + K) * Real.sqrt (B * B) with hT1
  have hT10 : 0 ≤ T1 := by positivity
  have hxi : ∀ m s, ‖p.form j hj w (KB.waveG (p.T.bs j) s w (KB.slv p.T (fun g => cut m g • D.cutF p.T.base χ f ε g) j hj w h hh.2))
      (KB.slv p.T (fun g => cut m g • D.cutF p.T.base χ f ε g) j hj w h' hh'.2)‖ ≤ T1 * ((1 + ‖s‖) ^ 3)⁻¹ := by
    intro m s
    refine xi_bound hP P p (fun g => cut m g • D.cutF p.T.base χ f ε g) (hcpt m) j hj w hw h h' hh hh' grid hinj hgr LinearMap.id
      (fun ε x hx => hx) (fun x hx => hx) B B ?_ ?_ ?_ ?_ s
    · show ‖p.form j hj w (KB.slv p.T (fun g => cut m g • D.cutF p.T.base χ f ε g) j hj w h hh.2) (KB.slv p.T (fun g => cut m g • D.cutF p.T.base χ f ε g) j hj w h hh.2)‖ ≤ B
      rw [← rr_eq_form p (fun g => cut m g • D.cutF p.T.base χ f ε g) j hj w h hh]; exact (hBh m).trans hBhB
    · rw [← rr_eq_form p (fun g => cut m g • D.cutF p.T.base χ f ε g) j hj w h' hh']; exact (hBh' m).trans hBh'B
    · intro n
      rw [onOld_eq_self (w := w) (⇑(LinearMap.id (R := ℂ)
        (M := Wd.Ix (Fin w.length) → FourierDecayAlt.B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)))) (fun x => rfl), ← rr_eq_form p (fun g => cut m g • D.cutF p.T.base χ f ε g) j hj _ h hh]
      exact (hBp n m).trans (hBpB n)
    · intro n
      rw [← rr_eq_form p (fun g => cut m g • D.cutF p.T.base χ f ε g) j hj _ h' hh']
      exact (hBm n m).trans (hBmB n)
  set I3 := ∫ s : ℂ, ((1 + ‖s‖) ^ 3)⁻¹ with hI3
  have hI30 : 0 ≤ I3 := integral_nonneg fun s => by positivity
  set C := T1 + 8 * T1 * I3 + (1 + K) * Real.sqrt (CW * B) * I3 * Real.pi ^ 3 with hCdef
  have hX3 : 0 ≤ (1 + K) * Real.sqrt (CW * B) * I3 * Real.pi ^ 3 := by positivity
  have hT8 : 0 ≤ 8 * T1 * I3 := mul_nonneg (mul_nonneg (by norm_num) hT10) hI30
  have hC1 : T1 ≤ C := by rw [hCdef]; linarith only [hX3, hT8]
  clear_value C I3 T1 K CW B
  refine ⟨C, fun m => ⟨fun c hc => ?_, fun s => ?_⟩⟩
  swap
  · have hs0 : (0 : ℝ) ≤ ((1 + ‖s‖) ^ 3)⁻¹ := inv_nonneg.2 (pow_nonneg (by positivity) 3)
    exact (hxi m s).trans (mul_le_mul_of_nonneg_right hC1 hs0)
  obtain ⟨φ, hφc, hφi, hφeq, hφs⟩ := pStdCpt_of_heads hP hRH hHT Wp Wq P p (fun g => cut m g • D.cutF p.T.base χ f ε g) j hj w h h' hh hh' Cb hθ
    (hcpt m) hw
  rw [← hφeq c hc]
  have hΞ : ∀ s, ‖∫ t, fsv s t * φ t‖ ≤ T1 * ((1 + ‖s‖) ^ 3)⁻¹ := fun s => by rw [hφs s]; exact hxi m s
  obtain ⟨hΞi, hΞI⟩ := integral_norm_le_decay (continuous_transform hφc hφi) hΞ
  have hφle := norm_le_integral_fsv φ hφc hφi hΞi c
  have hu : 0 < 1 + ‖c‖ := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ (pow_pos hu 3)]
  by_cases hc1 : ‖c‖ ≤ 1
  · have hu8 : (1 + ‖c‖) ^ 3 ≤ 8 := by
      calc (1 + ‖c‖) ^ 3 ≤ 2 ^ 3 := pow_le_pow_left₀ hu.le (by linarith) 3
        _ = 8 := by norm_num
    have h1 : ‖φ c‖ ≤ T1 * I3 := hφle.trans (by rw [hI3]; exact hΞI)
    have hTI : 0 ≤ T1 * I3 := mul_nonneg hT10 hI30
    calc ‖φ c‖ * (1 + ‖c‖) ^ 3 ≤ (T1 * I3) * 8 := mul_le_mul h1 hu8 (pow_nonneg hu.le 3) hTI
      _ = 8 * T1 * I3 := by ring
      _ ≤ C := by rw [hCdef]; linarith only [hX3, hT10]
  · push Not at hc1
    obtain ⟨hfσ, hσn⟩ := fsv_sigma hc
    set σ := Complex.I * (Real.pi : ℂ) / (2 * c) with hσdef
    have hc0 : 0 < ‖c‖ := by linarith
    have hσ2 : ‖σ‖ ≤ 2 := by
      rw [hσn, div_le_iff₀ (by linarith only [hc0])]
      linarith only [Real.pi_le_four, hc1]
    clear_value σ
    have hxc : ∀ e, KB.CptCoef (p.T.bs j) ((KB.slv p.T (fun g => cut m g • D.cutF p.T.base χ f ε g) j hj w h hh.2) e) := fun e =>
      Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p _ j hj w h hh (hcpt m) e
    have hyc : ∀ e, KB.CptCoef (p.T.bs j) ((KB.slv p.T (fun g => cut m g • D.cutF p.T.base χ f ε g) j hj w h' hh'.2) e) := fun e =>
      Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p _ j hj w h' hh' (hcpt m) e
    have hfc : Continuous (fun t => (fsv σ t - 1) ^ 3) :=
      ((continuous_fsv₂.comp (continuous_const.prodMk continuous_id)).sub continuous_const).pow 3
    have hψc : Continuous (fun t => (fsv σ t - 1) ^ 3 * φ t) := hfc.mul hφc
    have hψi : Integrable (fun t => (fsv σ t - 1) ^ 3 * φ t) :=
      hφi.bdd_mul (c := 8) hfc.aestronglyMeasurable
        (Filter.Eventually.of_forall fun t => norm_fsv_sub_one_pow σ t)
    have hσ6 : 0 ≤ ‖σ‖ ^ 6 := pow_nonneg (norm_nonneg _) 6
    have hΨb : ∀ s, ‖∫ t, fsv s t * ((fsv σ t - 1) ^ 3 * φ t)‖ ≤
        (8 * (1 + K) * Real.sqrt (CW * ‖σ‖ ^ 6 * B)) * ((1 + ‖s‖) ^ 3)⁻¹ := by
      intro s
      rw [transform_diff3 hφc hφi σ s, hφs, hφs, hφs, hφs, ← form_wave_mDiff P p j hj w _ _ hxc hyc s σ]
      have hA0 : ‖p.form j hj w (mDiff (p.T.bs j) σ w (KB.slv p.T (fun g => cut m g • D.cutF p.T.base χ f ε g) j hj w h hh.2)) (mDiff (p.T.bs j) σ w (KB.slv p.T (fun g => cut m g • D.cutF p.T.base χ f ε g) j hj w h hh.2))‖ ≤ CW * ‖σ‖ ^ 6 :=
        (hC0 m σ hσ2).trans (mul_le_mul_of_nonneg_right hC0W hσ6)
      have hB0' : ‖p.form j hj w (KB.slv p.T (fun g => cut m g • D.cutF p.T.base χ f ε g) j hj w h' hh'.2) (KB.slv p.T (fun g => cut m g • D.cutF p.T.base χ f ε g) j hj w h' hh'.2)‖ ≤ B := by
        rw [← rr_eq_form p _ j hj w h' hh']; exact (hBh' m).trans hBh'B
      have key := xi_bound hP P p _ (hcpt m) j hj w hw h h' hh hh' grid hinj hgr (mDiff (p.T.bs j) σ w)
        (fun ε x hx => mDiff_nice _ σ w ε x hx) (fun x hx => mDiff_cpt hP P p j hj w hw σ x hx)
        (CW * ‖σ‖ ^ 6) B hA0 hB0'
        (fun n => (hCw n m σ hσ2).trans (mul_le_mul_of_nonneg_right (hCwW n) hσ6))
        (fun n => by rw [← rr_eq_form p _ j hj _ h' hh']; exact (hBm n m).trans (hBmB n)) s
      rw [← hKdef] at key
      exact key
    obtain ⟨hΨi, hΨI⟩ := integral_norm_le_decay (continuous_transform hψc hψi) hΨb
    have hψle := norm_le_integral_fsv _ hψc hψi hΨi c
    have hψc' : ‖(fsv σ c - 1) ^ 3 * φ c‖ = 8 * ‖φ c‖ := by
      rw [hfσ, norm_mul]; norm_num
    have hsq : Real.sqrt (CW * ‖σ‖ ^ 6 * B) = ‖σ‖ ^ 3 * Real.sqrt (CW * B) := by
      rw [show CW * ‖σ‖ ^ 6 * B = (‖σ‖ ^ 3) ^ 2 * (CW * B) by ring, Real.sqrt_mul (pow_nonneg (pow_nonneg (norm_nonneg _) 3) 2),
        Real.sqrt_sq (pow_nonneg (norm_nonneg _) 3)]
    have h1 : 8 * ‖φ c‖ ≤ 8 * (1 + K) * (‖σ‖ ^ 3 * Real.sqrt (CW * B)) * I3 := by
      rw [← hψc', ← hsq, hI3]; exact hψle.trans hΨI
    have h2 : ‖φ c‖ ≤ (1 + K) * Real.sqrt (CW * B) * ‖σ‖ ^ 3 * I3 := by linarith only [h1]
    have hu8 : (1 + ‖c‖) ^ 3 ≤ 8 * ‖c‖ ^ 3 := by
      calc (1 + ‖c‖) ^ 3 ≤ (2 * ‖c‖) ^ 3 := pow_le_pow_left₀ hu.le (by linarith only [hc1]) 3
        _ = 8 * ‖c‖ ^ 3 := by ring
    have hπ : ‖σ‖ ^ 3 * (8 * ‖c‖ ^ 3) = Real.pi ^ 3 := by
      have hc3 : (2 : ℝ) ^ 3 * ‖c‖ ^ 3 ≠ 0 := (mul_pos (by norm_num) (pow_pos hc0 3)).ne'
      rw [hσn, div_pow, mul_pow, div_mul_eq_mul_div, mul_div_assoc,
        show (8 : ℝ) * ‖c‖ ^ 3 / (2 ^ 3 * ‖c‖ ^ 3) = 1 by rw [div_eq_one_iff_eq hc3]; norm_num, mul_one]
    have hK1 : (0 : ℝ) ≤ 1 + K := by linarith only [hK]
    have hs3 : (0 : ℝ) ≤ ‖σ‖ ^ 3 := pow_nonneg (norm_nonneg σ) 3
    have hQ4 : 0 ≤ (1 + K) * Real.sqrt (CW * B) * ‖σ‖ ^ 3 * I3 :=
      mul_nonneg (mul_nonneg (mul_nonneg hK1 (Real.sqrt_nonneg (CW * B))) hs3) hI30
    calc ‖φ c‖ * (1 + ‖c‖) ^ 3 ≤ ((1 + K) * Real.sqrt (CW * B) * ‖σ‖ ^ 3 * I3) * (8 * ‖c‖ ^ 3) :=
          mul_le_mul h2 hu8 (pow_nonneg hu.le 3) hQ4
      _ = (1 + K) * Real.sqrt (CW * B) * I3 * (‖σ‖ ^ 3 * (8 * ‖c‖ ^ 3)) := by ring
      _ = (1 + K) * Real.sqrt (CW * B) * I3 * Real.pi ^ 3 := by rw [hπ]
      _ ≤ C := by rw [hCdef]; linarith only [hT10, hT8]

end Formalism.FourierDecayAlt.P.PBO
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.WaveDifferenceForm
theorem Formalism.FourierDecayAlt.P.wave_difference_form : Formalism.FourierDecayAlt.P.PBO.WaveDiffForm :=
  Formalism.FourierDecayAlt.P.StandardPairingDecay.waveDiffForm_of Formalism.FourierDecayAlt.P.StandardPairingDecay.bound_on_earlier_region
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.UniformDecayOfParts
noncomputable section

namespace Formalism.FourierDecayAlt.P.PBO

open Formalism.FourierDecayAlt

def DecayUnifOfHeads : Prop := KB.RadHead → KB.HeadTop → DecayUnif

theorem decayUnifOfHeads : DecayUnifOfHeads := fun hRH hHT =>
  decayUnif_of hRH hHT Formalism.FourierDecayAlt.P.wave_difference_form

end Formalism.FourierDecayAlt.P.PBO

theorem Formalism.FourierDecayAlt.P.uniform_decay_of_heads : Formalism.FourierDecayAlt.P.PBO.DecayUnifOfHeads := Formalism.FourierDecayAlt.P.PBO.decayUnifOfHeads
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.GermRateBound
theorem Formalism.FourierDecayAlt.P.germ_rate_bound : Formalism.FourierDecayAlt.P.GermFibreKernels.GermRateB :=
  Formalism.FourierDecayAlt.P.germ_rate_bound_of_split Formalism.FourierDecayAlt.P.germ_rate_lower_bound Formalism.FourierDecayAlt.P.germ_rate_top_bound
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CWConsPlus
namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Wd
open scoped ComplexConjugate

noncomputable section

section cs

variable {n : ℕ}

theorem xs_upL (x0 : ℂ → ℂ) : ∀ (L : List (Letter ℂ (Fin n))) (E : Ix (Fin (n + 1))) (Y : ℂ),
    Fr.xs x0 (L.map PBF.upL) E Y = Fr.xs x0 L (fun a => E a.succ) Y
  | [], _, _ => rfl
  | l :: L, E, Y => by
    simp only [List.map_cons, Fr.xs]
    rw [xs_upL x0 L E Y]
    rfl

theorem cs_upL (x0 q0 : ℂ → ℂ) : ∀ (L : List (Letter ℂ (Fin n))) (E : Ix (Fin (n + 1))),
    Fr.cs x0 q0 (L.map PBF.upL) E = Fr.cs x0 q0 L (fun a => E a.succ)
  | [], _ => rfl
  | l :: L, E => by
    simp only [List.map_cons, Fr.cs]
    simp only [cs_upL, xs_upL,
      show qw q0 (L.map PBF.upL) = qw q0 L from funext fun Y => PBF.qw_map_reindex q0 Fin.succ L Y]
    rfl

theorem cW_cons_plus (P : M.Par) (l0 : ℕ) (y : ℝ) (w : List C.Letter) (E : Ix (Fin (w.length + 1))) (ρ : M.Ty P) :
    Top.cW P l0 ((true, y) :: w) E ρ = Top.cW P l0 w (fun a => E a.succ) ρ *
      (if E 0 = 0 then qw (M.qC P) (D.positionted w) (y : ℂ) /
          Fr.xs (fun Y => M.sgn P l0 * M.xC P ρ Y) (D.positionted w) (fun a => E a.succ) ((y : ℂ) + 1)
        else Fr.xs (fun Y => M.sgn P l0 * M.xC P ρ Y) (D.positionted w) (fun a => E a.succ) (y : ℂ)) := by
  unfold Top.cW
  rw [PBF.positioned_cons]
  simp only [Fr.cs, if_true]
  simp only [cs_upL, xs_upL, show qw (M.qC P) ((D.positionted w).map PBF.upL) = qw (M.qC P) (D.positionted w) from
    funext fun Y => PBF.qw_map_reindex _ Fin.succ _ Y]

def topRprod {P : M.Par} (l0 : ℕ) (a : List C.Letter) (e : Ix (Fin a.length)) (ρ : M.Ty P) : List ℝ → ℂ
  | [] => 1
  | y :: ys => topRprod l0 a e ρ ys * topR l0 (KB.plusW ys a) (KB.firstSt ys e) ρ y

theorem cW_plusW (P : M.Par) (l0 : ℕ) (a : List C.Letter) (e : Ix (Fin a.length)) (ρ : M.Ty P) :
    ∀ ys : List ℝ, Top.cW P l0 (KB.plusW ys a) (KB.firstSt ys e) ρ = Top.cW P l0 a e ρ * topRprod l0 a e ρ ys
  | [] => by simp [topRprod, KB.plusW, KB.firstSt]
  | y :: ys => by
    have h := cW_cons_plus P l0 y (KB.plusW ys a) (Fin.cons (0 : Fin 2) (KB.firstSt ys e)) ρ
    simp only [Fin.cons_zero, Fin.cons_succ, if_true] at h
    show Top.cW P l0 ((true, y) :: KB.plusW ys a) (Fin.cons (0 : Fin 2) (KB.firstSt ys e)) ρ = _
    rw [h, cW_plusW P l0 a e ρ ys]
    simp only [topRprod, topR]
    ring

end cs

end

end Formalism.FourierDecayAlt.P.PBL
end


section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.LenEqLenI
namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

section thr

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
  {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
  {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}

theorem ntop_eq_N'' (S : C.HidaSetting E Wp Wq) : (S.Ntop : ℝ) = S.G.N := by
  simp only [C.HidaSetting.Ntop, Sz.Glob.N, C.Kst]; push_cast; ring

theorem len_eq_lenI' (S : C.HidaSetting E Wp Wq) (v : Fin S.f) : S.cutHi v - S.cutLo v = S.G.lenI := by
  simp only [C.HidaSetting.cutHi, C.HidaSetting.cutLo, Sz.Glob.lenI, Sz.Glob.place]; ring

theorem glob_posT (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) : 0 < S.G.g ∧ 0 < S.G.ka := by
  obtain ⟨hg1, hg2, -⟩ := hB
  refine ⟨by unfold Sz.Glob.g; exact_mod_cast Nat.mul_pos hg1 hg2, ?_⟩
  unfold Sz.Glob.ka; rw [S.hv]; exact div_pos Real.pi_pos (by linarith [PBD.rd_pos' E])

theorem lenI_posT (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (hS : 0 < S.f) : 0 < S.G.lenI := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hG, -⟩ := hB
  obtain ⟨hlen, -⟩ := hG ⟨0, hS⟩
  rw [len_eq_lenI'] at hlen
  have hN : (0 : ℝ) ≤ S.Ntop := Nat.cast_nonneg _
  have hN1 : (1 : ℝ) ≤ S.Ntop := by
    have : 1 ≤ S.Ntop := by unfold C.HidaSetting.Ntop C.Kst; omega
    exact_mod_cast this
  have h6 : (0 : ℝ) < 6 * (S.Ntop : ℝ) ^ 3 + 6 * S.Ntop := by positivity
  linarith

theorem lamTop_thr (hC : 28 * Real.exp 1 ≤ Cc) (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (s : ℕ) (hs2 : 2 ≤ s)
    (hsr : s ≤ S.G.r + 1) (v : Fin S.f) :
    0 ≤ lamTop S (S.G.r + 2 - s) v ∧ 2 * lamTop S (S.G.r + 2 - s) v ≤ S.base.szL (S.G.r + 2 - s) s v := by
  refine ⟨Real.sqrt_nonneg _, ?_⟩
  have hB' := hB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hCA, -⟩ := hB'
  obtain ⟨hg, hk⟩ := glob_posT hB
  have hlen := lenI_posT hB (Fin.pos v)
  have hsz : S.base.szL (S.G.r + 2 - s) s v = 2 * J.thrP S.G S.CA S.de S.de' S.T S.T' S.l (S.G.r + 2 - s) (S.pl v) := by
    show (if S.G.r + 2 - s + s ≤ S.G.r + 1 then _ else _) = _
    rw [if_neg (by omega)]
  rw [hsz]
  have hsA : ∀ one, 0 ≤ J.supA S.G S.de S.de' S.T S.T' S.l one (S.pl v) := fun one => supA_nonneg S hg hk v one
  have hFT := (Formalism.FourierDecayAlt.P.frame_threshold_bound_holds (InfinitePlace E) S.G S.CA S.de S.de' S.T S.T' S.l (S.pl v) hg hlen
    (hC.trans hCA) hsA).2 (S.G.r + 2 - s) (Real.exp 1) ((28 * S.G.N / S.G.lenI) ^ (2 * (S.G.r + 2 - s - 1)))
    (by omega) (Real.exp_pos 1).le le_rfl (pow_nonneg (div_nonneg (by unfold Sz.Glob.N; positivity) hlen.le) _) le_rfl
  unfold lamTop
  have e : ((S.G.r : ℤ) + 2 - ((S.G.r + 2 - s : ℕ) : ℤ)) = ((S.G.r : ℤ) + 2 - ((S.G.r + 2 - s : ℕ) : ℤ)) := rfl
  linarith [hFT]

end thr

end

end Formalism.FourierDecayAlt.P.PBL
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.SecondDefectPlusWordLe
namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

section wts

variable {P : M.Par} (l0 : ℕ) (a : List C.Letter) (e : Wd.Ix (Fin a.length)) (ρ : M.Ty P) (Pv : ℝ → ℝ) (C : ℝ)

def RHyp : List ℝ → Prop
  | [] => True
  | y :: ys => (0 < (topR l0 (KB.plusW ys a) (KB.firstSt ys e) ρ y).re ∧
      (topR l0 (KB.plusW ys a) (KB.firstSt ys e) ρ y).im = 0 ∧
      |Pv y| ≤ C * (topR l0 (KB.plusW ys a) (KB.firstSt ys e) ρ y).re) ∧ RHyp ys

theorem prodR_props (hC : 0 ≤ C) : ∀ ys : List ℝ, RHyp l0 a e ρ Pv C ys →
    (topRprod l0 a e ρ ys).im = 0 ∧ 0 < (topRprod l0 a e ρ ys).re ∧
      (ys.map fun y => |Pv y|).prod ≤ C ^ ys.length * (topRprod l0 a e ρ ys).re := by
  intro ys
  induction ys with
  | nil => simp [topRprod]
  | cons y ys ih =>
    intro h
    rw [RHyp] at h
    obtain ⟨⟨h1, h2, h3⟩, hr⟩ := h
    obtain ⟨i1, i2, i3⟩ := ih hr
    simp only [topRprod, Complex.mul_im, Complex.mul_re, List.map_cons, List.prod_cons, List.length_cons]
    refine ⟨by rw [i1, h2]; ring, by rw [i1, h2]; simp only [mul_zero, sub_zero]; positivity, ?_⟩
    rw [i1, h2]
    simp only [mul_zero, sub_zero]
    have hp : 0 ≤ (ys.map fun y => |Pv y|).prod := List.prod_nonneg fun x hx => by
      obtain ⟨z, -, rfl⟩ := List.mem_map.1 hx; exact abs_nonneg _
    calc |Pv y| * (ys.map fun y => |Pv y|).prod ≤ (C * (topR l0 (KB.plusW ys a) (KB.firstSt ys e) ρ y).re) *
          (C ^ ys.length * (topRprod l0 a e ρ ys).re) := mul_le_mul h3 i3 hp (by positivity)
      _ = C ^ (ys.length + 1) * ((topRprod l0 a e ρ ys).re * (topR l0 (KB.plusW ys a) (KB.firstSt ys e) ρ y).re) := by
          ring

end wts

section wts2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

theorem second_defect_plus_word_le (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))) (v : Fin S.f)
    (a : List C.Letter) (e : Wd.Ix (Fin a.length)) (ρ : M.Ty (D.parOf S v)) (C : ℝ) (hC : 0 ≤ C) (ys : List ℝ)
    (hR : RHyp (p v).l0 a e ρ (S.P v) C ys) :
    del2 S p v a e ρ * (ys.map fun y => |S.P v y|).prod ≤
      C ^ ys.length * del2 S p v (KB.plusW ys a) (KB.firstSt ys e) ρ := by
  obtain ⟨i1, i2, i3⟩ := prodR_props (p v).l0 a e ρ (S.P v) C hC ys hR
  have hd : del2 S p v (KB.plusW ys a) (KB.firstSt ys e) ρ = del2 S p v a e ρ * (topRprod (p v).l0 a e ρ ys).re := by
    unfold del2
    rw [cW_plusW, Complex.mul_re, i1, mul_zero, sub_zero, Real.sqrt_mul' _ i2.le]
    rw [show √(Top.cW (D.parOf S v) (p v).l0 a e ρ).re * √(topRprod (p v).l0 a e ρ ys).re *
        (√(Top.cW (D.parOf S v) (p v).l0 a e ρ).re * √(topRprod (p v).l0 a e ρ ys).re) =
        √(Top.cW (D.parOf S v) (p v).l0 a e ρ).re * √(Top.cW (D.parOf S v) (p v).l0 a e ρ).re *
          (√(topRprod (p v).l0 a e ρ ys).re * √(topRprod (p v).l0 a e ρ ys).re) by ring,
      Real.mul_self_sqrt i2.le]
  rw [hd]
  have h0 := second_defect_nonneg S p v a e ρ
  calc del2 S p v a e ρ * (ys.map fun y => |S.P v y|).prod ≤
        del2 S p v a e ρ * (C ^ ys.length * (topRprod (p v).l0 a e ρ ys).re) := mul_le_mul_of_nonneg_left i3 h0
    _ = _ := by ring

end wts2

end

end Formalism.FourierDecayAlt.P.PBL
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.OfFnSplit
namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

section helpers

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

theorem mix_pushT (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (ε : ℝ) (i : ℕ) {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ)
    (mk : List ℝ → List C.Letter) (P Q : C.LPt) :
    KB.mix S v ε i (PBD.pushU grid mk) (PBD.pushTh grid mk) P Q =
      ∑ n : Fin K → Fin (d + 1), ((F7.thGrid grid n : ℝ) : ℂ) * KB.gN S v ε i (mk (List.ofFn fun b => grid b (n b))) P Q := by
  unfold KB.mix PBD.pushTh
  simp only [Complex.ofReal_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hmem : mk (List.ofFn fun b => grid b (n b)) ∈ PBD.pushU grid mk :=
    Finset.mem_image_of_mem _ (Finset.mem_univ n)
  simp only [apply_ite, Complex.ofReal_zero, zero_mul, ite_mul]
  rw [Finset.sum_ite_eq, if_pos hmem]

end helpers

section lists

theorem ofFn_split {K : ℕ} (f : Fin K → ℝ) (ys₁ : List ℝ) (y : ℝ) (ys₂ : List ℝ)
    (h : List.ofFn f = ys₁ ++ y :: ys₂) :
    ∃ b₀ : Fin K, b₀.val = ys₁.length ∧ y = f b₀ ∧ ys₁.length + 1 + ys₂.length = K ∧
      ∀ y' ∈ ys₂, ∃ b' : Fin K, b₀ < b' ∧ y' = f b' := by
  have hlen : K = ys₁.length + 1 + ys₂.length := by
    have := congrArg List.length h
    simp only [List.length_ofFn, List.length_append, List.length_cons] at this
    omega
  have hb : ys₁.length < K := by omega
  refine ⟨⟨ys₁.length, hb⟩, rfl, ?_, hlen.symm, ?_⟩
  · have h1 : (List.ofFn f)[ys₁.length]'(by simp; omega) = (ys₁ ++ y :: ys₂)[ys₁.length]'(by simp) := by
      simp only [h]
    rw [List.getElem_ofFn, List.getElem_append_right (by omega)] at h1
    simp only [Nat.sub_self, List.getElem_cons_zero] at h1
    exact h1.symm
  · intro y' hy'
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy'
    refine ⟨⟨ys₁.length + (i + 1), by omega⟩, by simp only [Fin.lt_def]; omega, ?_⟩
    have h1 : (List.ofFn f)[ys₁.length + (i + 1)]'(by simp; omega) =
        (ys₁ ++ y :: ys₂)[ys₁.length + (i + 1)]'(by simp; omega) := by simp only [h]
    rw [List.getElem_ofFn] at h1
    simp only [List.getElem_append, Nat.add_sub_cancel_left, List.getElem_cons_succ,
      show ¬ (ys₁.length + (i + 1) < ys₁.length) by omega, dite_false] at h1
    exact h1.symm

theorem rhyp_of {P : M.Par} (l0 : ℕ) (a : List C.Letter) (e : Wd.Ix (Fin a.length)) (ρ : M.Ty P) (Pv : ℝ → ℝ)
    (C : ℝ) : ∀ ys : List ℝ, (∀ ys₁ y ys₂, ys = ys₁ ++ y :: ys₂ →
      0 < (topR l0 (KB.plusW ys₂ a) (KB.firstSt ys₂ e) ρ y).re ∧
      (topR l0 (KB.plusW ys₂ a) (KB.firstSt ys₂ e) ρ y).im = 0 ∧
      |Pv y| ≤ C * (topR l0 (KB.plusW ys₂ a) (KB.firstSt ys₂ e) ρ y).re) → RHyp l0 a e ρ Pv C ys
  | [], _ => trivial
  | y :: ys, H => ⟨H [] y ys rfl, rhyp_of l0 a e ρ Pv C ys fun ys₁ y' ys₂ h => H (y :: ys₁) y' ys₂ (by rw [h]; rfl)⟩

end lists

end

end Formalism.FourierDecayAlt.P.PBL
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.LoeSubStates
namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Finset
open scoped ComplexConjugate ComplexOrder InnerProductSpace

noncomputable section

open Classical

section abstract

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {α : Type}

theorem psd_wsum {ι : Type} [Fintype ι] (Y : Finset α) (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i) (V : ι → α → H) :
    TB.PSDOn Y (fun P Q => ∑ i, (d i : ℂ) * gramH (V i) P Q) := by
  have h := loe_sum (Finset.univ : Finset ι) (Y := Y) (A := fun _ _ _ => (0 : ℂ))
    (B := fun i P Q => (d i : ℂ) * gramH (V i) P Q) fun i _ => by
      have := loe_smul (d i) (hd i) (loe_zero_of_psd (psd_gramH Y (V i)))
      refine loe_congr (fun x _ y _ => by ring) (fun x _ y _ => rfl) this
  exact psd_of_loe_zero (loe_congr (fun x _ y _ => by simp) (fun x _ y _ => rfl) h)

theorem loe_sub_states {ι ι' : Type} [Fintype ι] [Fintype ι'] (Y : Finset α) (g : ι → ι') (hg : Function.Injective g)
    (K : ι' → α → α → ℂ) (hK : ∀ j, TB.PSDOn Y (K j)) :
    Loe Y (fun x y => ∑ i, K (g i) x y) (fun x y => ∑ j, K j x y) := by
  have e : ∀ x y, ∑ j, K j x y = ∑ j ∈ Finset.univ.image g, K j x y +
      ∑ j ∈ Finset.univ \ Finset.univ.image g, K j x y := by
    intro x y
    rw [← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset (Finset.subset_univ _)]
  have e2 : ∀ x y, ∑ j ∈ Finset.univ.image g, K j x y = ∑ i, K (g i) x y := by
    intro x y
    rw [Finset.sum_image fun i _ i' _ h => hg h]
  have h1 := loe_sum (Finset.univ \ Finset.univ.image g) (Y := Y) (A := fun _ _ _ => (0 : ℂ)) (B := K)
    fun j _ => loe_zero_of_psd (hK j)
  have h2 := loe_add (loe_refl Y (fun x y => ∑ i, K (g i) x y)) h1
  refine loe_congr (fun x _ y _ => by simp) (fun x _ y _ => ?_) h2
  rw [e, e2]

theorem top_kernel {Ea R N : Type} {Ew : N → Type} [Fintype Ea] [∀ n, Fintype (Ew n)] [Fintype R] [Fintype N]
    (Y : Finset α) (g : ∀ n, Ea → Ew n) (hg : ∀ n, Function.Injective (g n)) (Va : Ea → R → α → H)
    (Vn : ∀ n, Ew n → R → α → H) (da : Ea → R → ℝ) (dn : ∀ n, Ew n → R → ℝ) (hda : ∀ e ρ, 0 ≤ da e ρ)
    (hdn : ∀ n e ρ, 0 ≤ dn n e ρ)
    (lam : N → ℝ) (Pn : N → ℝ) (hPn : ∀ n, 0 < Pn n) (c : ℂ) (C0 : ℝ) (K : ℕ) (hC0 : 0 ≤ C0)
    (hdeg : ∀ P ∈ Y, ∀ e ρ, Va e ρ P = c • ∑ n, (lam n : ℂ) • Vn n (g n e) ρ P)
    (hwt : ∀ n e ρ, da e ρ * Pn n ≤ C0 ^ K * dn n (g n e) ρ) :
    Loe Y (fun P Q => ∑ e, ∑ ρ, (da e ρ : ℂ) * gramH (Va e ρ) P Q)
      (fun P Q => ((‖c‖ ^ 2 * (∑ n, |lam n|) * C0 ^ K : ℝ) : ℂ) *
        ∑ n, ((|lam n| / Pn n : ℝ) : ℂ) * ∑ e', ∑ ρ, (dn n e' ρ : ℂ) * gramH (Vn n e' ρ) P Q) := by
  set Λ : ℝ := ∑ n, |lam n| with hΛ

  have s1 : ∀ e ρ, Loe Y (fun P Q => (da e ρ : ℂ) * gramH (Va e ρ) P Q)
      (fun P Q => (da e ρ : ℂ) * ((‖c‖ ^ 2 : ℝ) : ℂ) * (((∑ n, ‖(lam n : ℂ)‖ : ℝ) : ℂ) *
        ∑ n, ((‖(lam n : ℂ)‖ : ℝ) : ℂ) * gramH (Vn n (g n e) ρ) P Q)) := by
    intro e ρ
    have hc := loe_convex Y (fun n => (lam n : ℂ)) (fun n P => Vn n (g n e) ρ P)
    have hc2 := loe_smul (da e ρ * ‖c‖ ^ 2) (mul_nonneg (hda e ρ) (sq_nonneg _)) hc
    refine loe_congr (fun P hP Q hQ => ?_) (fun P _ Q _ => by push_cast; ring) hc2
    have : gramH (Va e ρ) P Q = gramH (fun P => c • ∑ n, (lam n : ℂ) • Vn n (g n e) ρ P) P Q := by
      unfold gramH; rw [hdeg P hP e ρ, hdeg Q hQ e ρ]
    rw [this, gramH_smul]
    push_cast; ring
  have hnorm : ∀ n, ‖(lam n : ℂ)‖ = |lam n| := fun n => by rw [Complex.norm_real, Real.norm_eq_abs]
  simp only [hnorm] at s1

  have s2 : ∀ e ρ n, Loe Y (fun P Q => (da e ρ : ℂ) * gramH (Vn n (g n e) ρ) P Q)
      (fun P Q => ((C0 ^ K / Pn n : ℝ) : ℂ) * ((dn n (g n e) ρ : ℂ) * gramH (Vn n (g n e) ρ) P Q)) := by
    intro e ρ n
    have h := loe_scale (psd_gramH Y (Vn n (g n e) ρ)) (r := da e ρ) (r' := C0 ^ K / Pn n * dn n (g n e) ρ) (by
      have := hwt n e ρ
      rw [sub_nonneg, div_mul_eq_mul_div, le_div_iff₀ (hPn n)]
      linarith)
    refine loe_congr (fun _ _ _ _ => rfl) (fun P _ Q _ => by push_cast; ring) h

  have s3 : ∀ n, Loe Y (fun P Q => ∑ e, ∑ ρ, (dn n (g n e) ρ : ℂ) * gramH (Vn n (g n e) ρ) P Q)
      (fun P Q => ∑ e', ∑ ρ, (dn n e' ρ : ℂ) * gramH (Vn n e' ρ) P Q) :=
    fun n => loe_sub_states Y (g n) (hg n) (fun e' P Q => ∑ ρ, (dn n e' ρ : ℂ) * gramH (Vn n e' ρ) P Q)
      fun e' => psd_wsum Y (fun ρ => dn n e' ρ) (fun ρ => hdn n e' ρ) (fun ρ => Vn n e' ρ)

  have c1 := loe_sum (Finset.univ : Finset Ea) fun e _ => loe_sum (Finset.univ : Finset R) fun ρ _ => s1 e ρ
  refine loe_trans c1 ?_

  have c2 : ∀ e ρ, Loe Y (fun P Q => (da e ρ : ℂ) * ((‖c‖ ^ 2 : ℝ) : ℂ) * ((Λ : ℂ) *
        ∑ n, ((|lam n| : ℝ) : ℂ) * gramH (Vn n (g n e) ρ) P Q))
      (fun P Q => ((‖c‖ ^ 2 * Λ : ℝ) : ℂ) * ∑ n, ((|lam n| : ℝ) : ℂ) *
        (((C0 ^ K / Pn n : ℝ) : ℂ) * ((dn n (g n e) ρ : ℂ) * gramH (Vn n (g n e) ρ) P Q))) := by
    intro e ρ
    have h := loe_smul (‖c‖ ^ 2 * Λ) (mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun n _ => abs_nonneg _))
      (loe_sum (Finset.univ : Finset N) fun n _ => loe_smul (|lam n|) (abs_nonneg _) (s2 e ρ n))
    refine loe_congr (fun P _ Q _ => ?_) (fun _ _ _ _ => rfl) h
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    push_cast; ring
  have c3 := loe_sum (Finset.univ : Finset Ea) fun e _ => loe_sum (Finset.univ : Finset R) fun ρ _ => c2 e ρ
  refine loe_trans (loe_congr (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) c3) ?_
  have c4 := loe_smul (‖c‖ ^ 2 * Λ) (mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun n _ => abs_nonneg _))
    (loe_sum (Finset.univ : Finset N) fun n _ => loe_smul (|lam n| * (C0 ^ K / Pn n))
      (mul_nonneg (abs_nonneg _) (div_nonneg (pow_nonneg hC0 _) (hPn n).le)) (s3 n))
  refine loe_congr (fun P _ Q _ => ?_) (fun P _ Q _ => ?_) c4
  · simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => ?_
    refine Finset.sum_congr rfl fun ρ _ => ?_
    push_cast; ring
  · simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun e' _ => Finset.sum_congr rfl fun ρ _ => ?_
    push_cast; ring

end abstract

end

end Formalism.FourierDecayAlt.P.PBL
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.RhypNodes
namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

section asm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
  {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
  {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}

theorem rhyp_nodes (hTR : TopRatio) (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (hC : 28 * Real.exp 1 ≤ Cc) (v : Fin S.f) (a : List C.Letter)
    (ha : D.AdmAt S v a) {K d : ℕ} (haN : a.length + K ≤ S.Ntop) (grid : Fin K → Fin (d + 1) → ℝ)
    (hmem : ∀ (b : Fin K) j, grid b j ∈ S.grid v (a.length + K - (b : ℕ)))
    (n : Fin K → Fin (d + 1))
    (hcut : KB.CutWord (D.parOf S v) (S.l + 1) (KB.plusW (List.ofFn fun b => grid b (n b)) a))
    (e : Wd.Ix (Fin a.length)) (ρ : M.Ty (D.parOf S v)) :
    RHyp (p v).l0 a e ρ (S.P v) (Real.exp 1 * J.supA S.G S.de S.de' S.T S.T' S.l false (S.pl v) *
      (Real.sqrt (S.T * S.T'))⁻¹) (List.ofFn fun b => grid b (n b)) := by
  have hB' := hB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hGo, -, -, -, -, hv⟩ := hB'
  obtain ⟨hl0, -⟩ := hv v
  rw [hl0]
  refine rhyp_of _ a e ρ _ _ _ fun ys₁ y ys₂ hsplit => ?_
  obtain ⟨b₀, hb₀, rfl, hlen, hlater⟩ := ofFn_split (fun b => grid b (n b)) ys₁ y ys₂ hsplit

  have hc : KB.CutWord (D.parOf S v) (S.l + 1) ((true, grid b₀ (n b₀)) :: KB.plusW ys₂ a) := by
    rw [PBD.cutWord_iff] at hcut ⊢
    rw [PBF.plusW_eq, hsplit] at hcut
    have hsub : ((true, grid b₀ (n b₀)) :: KB.plusW ys₂ a).Sublist
        ((ys₁ ++ grid b₀ (n b₀) :: ys₂).map (fun y => (true, y)) ++ a) := by
      rw [PBF.plusW_eq, List.map_append, List.map_cons, List.append_assoc, List.cons_append]
      exact List.sublist_append_right _ _
    exact ⟨fun x hx => hcut.1 x (hsub.subset hx), hcut.2.sublist hsub⟩
  have hgr : ∃ m, grid b₀ (n b₀) ∈ S.grid v m := ⟨_, hmem b₀ (n b₀)⟩
  have hl : (KB.plusW ys₂ a).length < S.Ntop := by
    rw [PBF.plusW_eq, List.length_append, List.length_map]; omega
  have hfar : ∀ x ∈ KB.plusW ys₂ a, (S.Ntop : ℝ) ^ 2 + 1 ≤ |grid b₀ (n b₀) - x.2| ∧
      (x.1 = false → (S.Ntop : ℝ) ^ 2 + 1 ≤ |grid b₀ (n b₀) - (x.2 - 1)|) := by
    intro x hx
    rw [PBF.plusW_eq, List.mem_append] at hx
    rcases hx with hx | hx
    · obtain ⟨y', hy', rfl⟩ := List.mem_map.1 hx
      obtain ⟨b', hb', rfl⟩ := hlater y' hy'
      refine ⟨?_, fun h => absurd h (by simp)⟩
      have := PBD.sep_grid S hGo v (hmem b₀ (n b₀)) (hmem b' (n b')) (by
        have : (b₀ : ℕ) < b' := hb'
        have hb'K := b'.isLt
        omega) (e := 0) (e' := 0) (by simp) (by simp)
      simpa using this
    · have hy : (false = false ∧ ∃ a', a.length < a' ∧ a' ≤ S.Ntop ∧ grid b₀ (n b₀) ∈ S.grid v a') ∨
          (false = true ∧ grid b₀ (n b₀) ∈ S.grid1 v ∧ ∀ x ∈ a, PBD.Sep (true, grid b₀ (n b₀)) x) :=
        Or.inl ⟨rfl, a.length + K - (b₀ : ℕ), by have := b₀.isLt; omega, by omega, hmem b₀ (n b₀)⟩
      obtain ⟨h1, h2⟩ := node_far hB v a ha (grid b₀ (n b₀)) false hy x hx
      simp only [Bool.false_eq_true, if_false] at h1 h2
      unfold PBD.nodeOf at h1 h2
      by_cases hx1 : x.1 = true
      · rw [if_pos hx1] at h1
        exact ⟨h1, fun h => absurd h (by simp [hx1])⟩
      · rw [if_neg hx1] at h1 h2
        rw [sub_add_cancel] at h2
        exact ⟨h2, fun _ => h1⟩
  have := hTR Cb Cc E Wp Wq S p f χ A₀ hB hC v (KB.plusW ys₂ a) (grid b₀ (n b₀)) hc hgr hl hfar
    (KB.firstSt ys₂ e) ρ
  exact this

end asm

end

end Formalism.FourierDecayAlt.P.PBL
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.LamSumPos
namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

theorem firstSt_inj {w : List C.Letter} : ∀ ys : List ℝ, Function.Injective (KB.firstSt (w := w) ys)
  | [] => fun _ _ h => h
  | _ :: ys => fun e e' h => firstSt_inj ys (Fin.cons_right_injective (α := fun _ => Fin 2) (0 : Fin 2) h)

theorem lam_sum_eq {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) :
    ∑ n : Fin K → Fin (d + 1), |∏ b, F7.lagCo (grid b) (n b)| = ∏ b, ∑ i, |F7.lagCo (grid b) i| := by
  rw [Fintype.prod_sum]
  exact Finset.sum_congr rfl fun n _ => Finset.abs_prod _ _

theorem lam_sum_pos {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) (hinj : ∀ b, Function.Injective (grid b)) :
    0 < ∑ n : Fin K → Fin (d + 1), |∏ b, F7.lagCo (grid b) (n b)| := by
  rw [lam_sum_eq]
  refine Finset.prod_pos fun b _ => ?_
  exact lt_of_lt_of_le (abs_pos.2 (PBD.lagCo_ne_zero _ (hinj b) 0))
    (Finset.single_le_sum (f := fun i => |F7.lagCo (grid b) i|) (fun i _ => abs_nonneg _) (Finset.mem_univ 0))

theorem thGrid_eq {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) (n : Fin K → Fin (d + 1)) :
    F7.thGrid grid n = |∏ b, F7.lagCo (grid b) (n b)| / ∑ m : Fin K → Fin (d + 1), |∏ b, F7.lagCo (grid b) (m b)| := by
  unfold F7.thGrid
  rw [Finset.prod_div_distrib, lam_sum_eq, Finset.abs_prod]

theorem lam_sum_le {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) (B : ℝ)
    (hb : ∀ b, ∑ i, |F7.lagCo (grid b) i| ≤ B) :
    ∑ n : Fin K → Fin (d + 1), |∏ b, F7.lagCo (grid b) (n b)| ≤ B ^ K := by
  rw [lam_sum_eq]
  calc ∏ b, ∑ i, |F7.lagCo (grid b) i| ≤ ∏ _b : Fin K, B :=
        Finset.prod_le_prod₀ (fun b _ => Finset.sum_nonneg fun i _ => abs_nonneg _) fun b _ => hb b
    _ = B ^ K := by simp

theorem zpow_sq_eq (x : ℝ) (hx : 0 < x) (ν : ℤ) : (x ^ ν) ^ 2 = x⁻¹ ^ (-(2 * ν)) := by
  rw [inv_zpow', neg_neg, ← zpow_natCast, ← zpow_mul, mul_comm]
  norm_num

section psd

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {α : Type}

theorem psd_dsum {Ea R : Type} [Fintype Ea] [Fintype R] (Y : Finset α) (d : Ea → R → ℝ) (hd : ∀ e ρ, 0 ≤ d e ρ)
    (V : Ea → R → α → H) : TB.PSDOn Y (fun P Q => ∑ e, ∑ ρ, (d e ρ : ℂ) * gramH (V e ρ) P Q) := by
  have h := loe_sum (Finset.univ : Finset Ea) (Y := Y) (A := fun _ _ _ => (0 : ℂ))
    (B := fun e P Q => ∑ ρ, (d e ρ : ℂ) * gramH (V e ρ) P Q) fun e _ => by
      have := loe_sum (Finset.univ : Finset R) (Y := Y) (A := fun _ _ _ => (0 : ℂ))
        (B := fun ρ P Q => (d e ρ : ℂ) * gramH (V e ρ) P Q) fun ρ _ => by
          have := loe_smul (d e ρ) (hd e ρ) (loe_zero_of_psd (psd_gramH Y (V e ρ)))
          exact loe_congr (fun x _ y _ => by ring) (fun x _ y _ => rfl) this
      exact loe_congr (fun x _ y _ => by simp) (fun x _ y _ => rfl) this
  exact psd_of_loe_zero (loe_congr (fun x _ y _ => by simp) (fun x _ y _ => rfl) h)

theorem psd_mixω {N : Type} [Fintype N] (Y : Finset α) (ω : α → ℝ) (θ κ : N → ℝ) (hθ : ∀ n, 0 ≤ θ n)
    (hκ : ∀ n, 0 ≤ κ n) (Kn : N → α → α → ℂ) (hK : ∀ n, TB.PSDOn Y (Kn n)) :
    TB.PSDOn Y (fun P Q => ∑ n, (θ n : ℂ) * ((ω P : ℂ) * (ω Q : ℂ) * ((κ n : ℂ) * Kn n P Q))) := by
  have h := loe_sum (Finset.univ : Finset N) (Y := Y) (A := fun _ _ _ => (0 : ℂ))
    (B := fun n P Q => (θ n : ℂ) * ((ω P : ℂ) * (ω Q : ℂ) * ((κ n : ℂ) * Kn n P Q))) fun n _ => by
      have h1 := loe_diag ω (loe_smul (θ n * κ n) (mul_nonneg (hθ n) (hκ n)) (loe_zero_of_psd (hK n)))
      exact loe_congr (fun x _ y _ => by simp) (fun x _ y _ => by push_cast; ring) h1
  exact psd_of_loe_zero (loe_congr (fun x _ y _ => by simp) (fun x _ y _ => rfl) h)

end psd

theorem mix_alg {N : Type} [Fintype N] (ω1 ω2 ka X L : ℝ) (lam Pn : N → ℝ) (Kn : N → ℂ) (hL : L ≠ 0)
    (hP : ∀ n, Pn n ≠ 0) :
    (ω1 : ℂ) * (ω2 : ℂ) * ((ka : ℂ) * ((X : ℂ) * ∑ n, ((|lam n| / Pn n : ℝ) : ℂ) * Kn n)) =
      ((X * L : ℝ) : ℂ) * ∑ n, ((|lam n| / L : ℝ) : ℂ) * ((ω1 : ℂ) * (ω2 : ℂ) * (((ka / Pn n : ℝ) : ℂ) * Kn n)) := by
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  have h1 := hP n
  push_cast
  field_simp

end

end Formalism.FourierDecayAlt.P.PBL
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.TopLocalBuiltPlaces
namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

theorem topLocB : TopLocB := by
  intro hDT hVT hTR Cb Cc E _ _ _ Wp Wq _ _ _ _ _ _ S p f χ A₀ hC hB
  refine ⟨fun s hs2 hsr v => lamTop_thr hC hB s hs2 hsr v, fun F hF (v : Fin S.f) => ?_⟩
  have hB' := hB
  obtain ⟨hg1, hg2, -, -, -, -, -, -, -, -, hGo, hGr, -, -, -, hv⟩ := hB'
  obtain ⟨hl0, -⟩ := hv v
  have hCI := PBCut.cutInside_of_built hB
  intro s hs2 hsr a ha haN
  have hsr' : s ≤ S.G.r + 1 := hsr
  have ha' : D.AdmAt S v a := ha
  have haN' : a.length + C.Kst ≤ S.Ntop := haN
  set d := S.G.r + 1 - s with hd
  have hds : d + s = S.G.r + 1 := by omega
  have hd2 : d ≤ 2 * S.G.r := by omega
  obtain ⟨-, grid, hinj, hbnd, hmem, hwords, hprob, -⟩ :=
    Formalism.FourierDecayAlt.P.new_letters_admissible E Wp Wq S hGo hGr hCI v a C.Kst d ha' haN' hd2
  refine ⟨PBD.pushU grid (fun ys => KB.plusW ys a), PBD.pushTh grid (fun ys => KB.plusW ys a), hprob, ?_⟩
  intro ε hε t Y ht hY
  have hY' : ∀ P ∈ Y, D.ptSize P = d := fun P hP => by rw [hd]; exact hY P hP
  set Λ : ℝ := ∑ n : Fin C.Kst → Fin (d + 1), |∏ b, F7.lagCo (grid b) (n b)| with hΛ
  set C0 : ℝ := Real.exp 1 * J.supA S.G S.de S.de' S.T S.T' S.l false (S.pl v) * (Real.sqrt (S.T * S.T'))⁻¹
    with hC0
  set τ : ℂ := ((((S.g : ℝ) / (2 * Real.pi)) ^ S6.nuBlock S.G.r ((1 + d : ℕ) : ℤ) (s : ℤ) : ℝ) : ℂ) *
    Complex.I ^ (s - 1) * t with hτ
  set c : ℂ := (((-1 : ℂ) ^ (s - 1) / τ) ^ C.Kst)⁻¹ with hc
  obtain ⟨hg, hk⟩ := glob_posT hB
  have hC0nn : 0 ≤ C0 := mul_nonneg (mul_nonneg (Real.exp_pos 1).le (supA_nonneg S hg hk v false))
    (inv_nonneg.2 (Real.sqrt_nonneg _))
  have hPn : ∀ n : Fin C.Kst → Fin (d + 1), 0 < ((List.ofFn fun b => grid b (n b)).map fun y => |S.P v y|).prod := by
    intro n
    refine List.prod_pos fun x hx => ?_
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    obtain ⟨b, rfl⟩ := List.mem_ofFn.1 hy
    exact abs_pos.2 ((hGo v).2.2.2.2.2 _ (Or.inl ⟨_, hmem b (n b)⟩)).2.2.1

  have hK1 := top_kernel (H := HV S v) (α := C.LPt) (Ea := Wd.Ix (Fin a.length)) (R := M.Ty (D.parOf S v))
    (N := Fin C.Kst → Fin (d + 1)) (Ew := fun n => Wd.Ix (Fin (KB.plusW (List.ofFn fun b => grid b (n b)) a).length))
    Y (fun n => KB.firstSt (List.ofFn fun b => grid b (n b))) (fun n => firstSt_inj _)
    (fun e ρ => vecT S p F v ε s t a e ρ)
    (fun n e' ρ => vecT S p F v ε s t (KB.plusW (List.ofFn fun b => grid b (n b)) a) e' ρ)
    (fun e ρ => del2 S p v a e ρ) (fun n e' ρ => del2 S p v (KB.plusW (List.ofFn fun b => grid b (n b)) a) e' ρ)
    (fun e ρ => second_defect_nonneg S p v a e ρ) (fun n e' ρ => second_defect_nonneg S p v _ e' ρ)
    (fun n => ∏ b, F7.lagCo (grid b) (n b))
    (fun n => ((List.ofFn fun b => grid b (n b)).map fun y => |S.P v y|).prod) hPn c C0 C.Kst hC0nn
    (fun P hP e ρ => vecT_deg hDT hB F v ε (hF v ε hε) s hs2 t ht d hds a e ρ grid hinj
      (fun n => (hwords n).2.2.1) P (hY' P hP))
    (fun n e ρ => by
      have h := second_defect_plus_word_le S p v a e ρ C0 hC0nn (List.ofFn fun b => grid b (n b))
        (rhyp_nodes hTR hB hC v a ha' haN' grid hmem n (hwords n).2.2.1 e ρ)
      rwa [List.length_ofFn] at h)

  change Loe Y (fun P Q => KB.gN (setC S p F) v ε (S.G.r + 1) a (P ++ [(s, t)]) (Q ++ [(s, t)]))
    (fun P Q => (((‖t‖ * lamTop S (S.G.r + 2 - s) v) ^ (2 * C.Kst) : ℝ) : ℂ) *
      KB.mix (setC S p F) v ε (S.G.r + 1) (PBD.pushU grid fun ys => KB.plusW ys a)
        (PBD.pushTh grid fun ys => KB.plusW ys a) (P ++ [(s, t)]) (Q ++ [(s, t)]))
  have hsz : ∀ P ∈ Y, D.ptSize P + s = S.G.r + 1 := fun P hP => by rw [hY' P hP]; omega
  have hgpos := g_pos_of_built hB
  have hrd := PBD.rd_pos' E
  have hΓ : 0 < ΓS S (S.G.r + 1) := PBD.gamLev_pos _ _ _ _ (by unfold D.kapG; positivity) (by unfold D.deG; positivity) _
  have hsa : 0 < S.sizeAt v a := sizeAt_pos S hGo v a ha'
  set ka : ℝ := 1 / (ΓS S (S.G.r + 1) * S.sizeAt v a) with hka
  have hka0 : 0 ≤ ka := by positivity
  have hΛpos : 0 < Λ := lam_sum_pos grid hinj

  have h1 := loe_diag (omT S s t) (loe_smul ka hka0 hK1)
  have h1' : Loe Y (fun P Q => KB.gN (setC S p F) v ε (S.G.r + 1) a (P ++ [(s, t)]) (Q ++ [(s, t)]))
      (fun P Q => (((‖c‖ ^ 2 * Λ * C0 ^ C.Kst) * Λ : ℝ) : ℂ) * ∑ n : Fin C.Kst → Fin (d + 1),
        ((|∏ b, F7.lagCo (grid b) (n b)| / Λ : ℝ) : ℂ) * ((omT S s t P : ℂ) * (omT S s t Q : ℂ) *
          (((ka / ((List.ofFn fun b => grid b (n b)).map fun y => |S.P v y|).prod : ℝ) : ℂ) *
            ∑ e', ∑ ρ, (del2 S p v (KB.plusW (List.ofFn fun b => grid b (n b)) a) e' ρ : ℂ) *
              gramH (vecT S p F v ε s t (KB.plusW (List.ofFn fun b => grid b (n b)) a) e' ρ) P Q))) := by
    refine loe_congr (fun P hP Q hQ => ?_) (fun P _ Q _ => ?_) h1
    · rw [gN_top hVT hB F v ε s hs2 t a P Q (hsz P hP) (hsz Q hQ)]
      ring
    · exact mix_alg _ _ _ _ _ _ _ _ hΛpos.ne' fun n => (hPn n).ne'

  have hmixY : ∀ P ∈ Y, ∀ Q ∈ Y, KB.mix (setC S p F) v ε (S.G.r + 1) (PBD.pushU grid fun ys => KB.plusW ys a)
      (PBD.pushTh grid fun ys => KB.plusW ys a) (P ++ [(s, t)]) (Q ++ [(s, t)]) =
      ∑ n : Fin C.Kst → Fin (d + 1),
        ((|∏ b, F7.lagCo (grid b) (n b)| / Λ : ℝ) : ℂ) * ((omT S s t P : ℂ) * (omT S s t Q : ℂ) *
          (((ka / ((List.ofFn fun b => grid b (n b)).map fun y => |S.P v y|).prod : ℝ) : ℂ) *
            ∑ e', ∑ ρ, (del2 S p v (KB.plusW (List.ofFn fun b => grid b (n b)) a) e' ρ : ℂ) *
              gramH (vecT S p F v ε s t (KB.plusW (List.ofFn fun b => grid b (n b)) a) e' ρ) P Q)) := by
    intro P hP Q hQ
    refine (mix_pushT (setC S p F) v ε (S.G.r + 1) grid (fun ys => KB.plusW ys a) _ _).trans ?_
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [thGrid_eq, ← hΛ, gN_top hVT hB F v ε s hs2 t _ P Q (hsz P hP) (hsz Q hQ), sizeAt_plusW]
    have hk : 1 / (ΓS S (S.G.r + 1) * (((List.ofFn fun b => grid b (n b)).map fun y => |S.P v y|).prod *
        S.sizeAt v a)) = ka / ((List.ofFn fun b => grid b (n b)).map fun y => |S.P v y|).prod := by
      rw [hka]; have := (hPn n).ne'; field_simp
    rw [hk]
    ring
  have hpsdY := psd_mixω Y (omT S s t) (fun n : Fin C.Kst → Fin (d + 1) => |∏ b, F7.lagCo (grid b) (n b)| / Λ)
    (fun n => ka / ((List.ofFn fun b => grid b (n b)).map fun y => |S.P v y|).prod)
    (fun n => div_nonneg (abs_nonneg _) hΛpos.le) (fun n => div_nonneg hka0 (hPn n).le)
    (fun n P Q => ∑ e', ∑ ρ, (del2 S p v (KB.plusW (List.ofFn fun b => grid b (n b)) a) e' ρ : ℂ) *
      gramH (vecT S p F v ε s t (KB.plusW (List.ofFn fun b => grid b (n b)) a) e' ρ) P Q)
    (fun n => psd_dsum Y _ (fun e' ρ => second_defect_nonneg S p v _ e' ρ) _)
  have hX : 0 ≤ (‖t‖ * lamTop S (S.G.r + 2 - s) v) ^ (2 * C.Kst) - ‖c‖ ^ 2 * Λ * C0 ^ C.Kst * Λ := by
    have hlv : 0 < ((S.g : ℝ) / (2 * Real.pi)) ^ S6.nuBlock S.G.r ((1 + d : ℕ) : ℤ) (s : ℤ) :=
      zpow_pos (by positivity) _
    set lv : ℝ := ((S.g : ℝ) / (2 * Real.pi)) ^ S6.nuBlock S.G.r ((1 + d : ℕ) : ℤ) (s : ℤ) with hlvdef
    have hτn : ‖τ‖ = lv * ‖t‖ := by
      rw [hτ, norm_mul, norm_mul, norm_pow, Complex.norm_I, one_pow, mul_one, Complex.norm_real,
        Real.norm_of_nonneg hlv.le]
    have hcn : ‖c‖ = ‖τ‖ ^ C.Kst := by
      rw [hc, norm_inv, norm_pow, norm_div, norm_pow, norm_neg, norm_one, one_pow, one_div, inv_pow, inv_inv]
    set B : ℝ := (28 * (S.Ntop : ℝ) / (S.cutHi v - S.cutLo v)) ^ d with hBdef
    have hΛB : Λ ≤ B ^ C.Kst := lam_sum_le grid B hbnd
    have hlenpos := lenI_posT hB (Fin.pos v)
    have hB0 : 0 ≤ B := by
      rw [hBdef, len_eq_lenI']; exact pow_nonneg (div_nonneg (by positivity) hlenpos.le) _

    have hA0 : 0 ≤ (2 * Real.pi / S.G.g) ^ (-(2 * S6.nuBlock S.G.r ((S.G.r + 2 - s : ℕ) : ℤ)
        ((S.G.r : ℤ) + 2 - ((S.G.r + 2 - s : ℕ) : ℤ)))) * Real.exp 1 *
        (28 * S.G.N / S.G.lenI) ^ (2 * (S.G.r + 2 - s - 1)) * J.supA S.G S.de S.de' S.T S.T' S.l false (S.pl v) *
        (√(S.T * S.T'))⁻¹ := by
      have : 0 ≤ S.G.N := by unfold Sz.Glob.N; positivity
      have := supA_nonneg S hg hk v false
      positivity
    have hlam2 : lamTop S (S.G.r + 2 - s) v ^ 2 = lv ^ 2 * B ^ 2 * C0 := by
      unfold lamTop
      rw [Real.sq_sqrt hA0]
      have e1 : ((S.G.r + 2 - s : ℕ) : ℤ) = ((1 + d : ℕ) : ℤ) := by rw [hd]; push_cast; omega
      have e2 : (S.G.r : ℤ) + 2 - ((S.G.r + 2 - s : ℕ) : ℤ) = (s : ℤ) := by push_cast; omega
      have e3 : (S.g : ℝ) = S.G.g := by unfold C.HidaSetting.g Sz.Glob.g; push_cast; ring
      have e4 : S.G.r + 2 - s - 1 = d := by omega
      rw [e2, e1, e4, hlvdef, zpow_sq_eq _ (by positivity), inv_div, e3, hBdef, ← pow_mul, ntop_eq_N'',
        len_eq_lenI', hC0, mul_comm d 2]
      ring
    have hfin : ‖c‖ ^ 2 * Λ * C0 ^ C.Kst * Λ ≤ (‖t‖ * lamTop S (S.G.r + 2 - s) v) ^ (2 * C.Kst) := by
      have e5 : (‖t‖ * lamTop S (S.G.r + 2 - s) v) ^ (2 * C.Kst) = (‖t‖ ^ 2 * (lv ^ 2 * B ^ 2 * C0)) ^ C.Kst := by
        rw [pow_mul, mul_pow (‖t‖) (lamTop S (S.G.r + 2 - s) v) 2, hlam2]
      rw [e5, hcn, hτn]
      have hΛ0 : 0 ≤ Λ := hΛpos.le
      have hsq : Λ * Λ ≤ B ^ C.Kst * B ^ C.Kst := mul_le_mul hΛB hΛB hΛ0 (pow_nonneg hB0 _)
      calc ((lv * ‖t‖) ^ C.Kst) ^ 2 * Λ * C0 ^ C.Kst * Λ = ((lv * ‖t‖) ^ C.Kst) ^ 2 * C0 ^ C.Kst * (Λ * Λ) := by ring
        _ ≤ ((lv * ‖t‖) ^ C.Kst) ^ 2 * C0 ^ C.Kst * (B ^ C.Kst * B ^ C.Kst) :=
            mul_le_mul_of_nonneg_left hsq (by positivity)
        _ = (‖t‖ ^ 2 * (lv ^ 2 * B ^ 2 * C0)) ^ C.Kst := by ring
    linarith
  have h3 := loe_scale hpsdY hX
  exact loe_trans h1' (loe_congr (fun _ _ _ _ => rfl) (fun P hP Q hQ => by rw [hmixY P hP Q hQ]) h3)

end

end Formalism.FourierDecayAlt.P.PBL

theorem Formalism.FourierDecayAlt.P.top_local_built_places : Formalism.FourierDecayAlt.P.PBL.TopLocB := Formalism.FourierDecayAlt.P.PBL.topLocB
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.OneAddPowLeExp
namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt NumberField Finset

noncomputable section

open Classical

section real

theorem pratio (s : Finset ℕ) (lam : ℕ → ℝ) (α β y : ℝ) (hI : 3 ≤ β - α)
    (hroot : ∀ t ∈ s, -lam t < α ∨ β < -lam t) (hy1 : α + (β - α) / 3 ≤ y) (hy2 : y + 1 ≤ β - (β - α) / 3) :
    |∏ t ∈ s, (y + lam t)| ≤ (1 + 3 / (β - α)) ^ s.card * |∏ t ∈ s, (y + 1 + lam t)| := by
  rw [Finset.abs_prod, Finset.abs_prod, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun t _ => abs_nonneg _) fun t ht => ?_
  have hI0 : 0 < β - α := by linarith
  have h3 : 0 ≤ 3 / (β - α) := by positivity
  rcases hroot t ht with h | h
  · have a1 : 0 < y + lam t := by linarith
    rw [abs_of_pos a1, abs_of_pos (by linarith : 0 < y + 1 + lam t)]
    nlinarith
  · have a2 : y + 1 + lam t < 0 := by linarith
    have hd : (β - α) / 3 ≤ -(y + 1 + lam t) := by linarith
    rw [abs_of_neg (by linarith : y + lam t < 0), abs_of_neg a2]
    have : 1 ≤ 3 / (β - α) * -(y + 1 + lam t) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hI0]; linarith
    nlinarith

theorem long_bound (k r N Cc I : ℝ) (hk : 1 ≤ k) (hr : 0 ≤ r) (hN : 20 ≤ N) (hCc : 1 ≤ Cc)
    (h : Cc * (k * N * (r + 1) ^ 2 + N ^ 2 * (r + 1) ^ 2 + N ^ 3) ≤ I) : 6 * (k + 2 * r + 1) ≤ I := by
  have hb : 0 ≤ k * N * (r + 1) ^ 2 + N ^ 2 * (r + 1) ^ 2 + N ^ 3 := by positivity
  have h1 : k * N * (r + 1) ^ 2 + N ^ 2 * (r + 1) ^ 2 + N ^ 3 ≤ I := by nlinarith
  have h2 : 6 * k ≤ k * N * (r + 1) ^ 2 := by
    have : 20 ≤ N * (r + 1) ^ 2 := by nlinarith
    nlinarith
  have h3 : 6 * (2 * r + 1) ≤ N ^ 2 * (r + 1) ^ 2 := by
    have : 400 ≤ N ^ 2 := by nlinarith
    nlinarith
  have h4 : 0 ≤ N ^ 3 := by positivity
  linarith

theorem three_le_len (N I : ℝ) (hN : 20 ≤ N) (h : 6 * N ^ 3 + 6 * N ≤ I) : 3 ≤ I := by
  have : 0 ≤ 6 * N ^ 3 := by positivity
  linarith

theorem two_N_bound (N : ℝ) (hN : 20 ≤ N) : 0 < N ^ 2 - 1 ∧ ((2 : ℕ) : ℝ) * (N / (N ^ 2 - 1)) ≤ 1 / 2 := by
  have hpos : 0 < N ^ 2 - 1 := by nlinarith
  refine ⟨hpos, ?_⟩
  rw [Nat.cast_ofNat, mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem final_cmp (Pa x0 F q TT sA E1 qw : ℝ) (hPa : 0 ≤ Pa) (hx0 : 0 < x0) (hF0 : 0 < F) (hq : 0 < q) (hTT : 0 < TT)
    (hsA : 0 ≤ sA) (hE1 : 0 < E1) (hE1sq : E1 ^ 2 = Real.exp 1) (hP2 : Pa ^ 2 ≤ E1 * (sA ^ 2 * q))
    (hx : x0 ^ 2 ≤ q / TT) (hF : F ^ 2 ≤ E1) (hqw : E1⁻¹ * q ≤ qw) :
    Pa ≤ Real.exp 1 * sA * (√TT)⁻¹ * (qw / (x0 * F)) := by
  have hsq : (√TT)⁻¹ ^ 2 = TT⁻¹ := by rw [inv_pow, Real.sq_sqrt hTT.le]
  have hsq0 : 0 < (√TT)⁻¹ := inv_pos.2 (Real.sqrt_pos.2 hTT)
  have hmain : Pa * (x0 * F) ≤ E1 * sA * (√TT)⁻¹ * q := by
    have hl0 : 0 ≤ Pa * (x0 * F) := mul_nonneg hPa (mul_pos hx0 hF0).le
    have hr0 : 0 ≤ E1 * sA * (√TT)⁻¹ * q := mul_nonneg (mul_nonneg (mul_nonneg hE1.le hsA) hsq0.le) hq.le
    rw [← pow_le_pow_iff_left₀ hl0 hr0 two_ne_zero]
    have eL : (Pa * (x0 * F)) ^ 2 = Pa ^ 2 * x0 ^ 2 * F ^ 2 := by ring
    have eR : (E1 * sA * (√TT)⁻¹ * q) ^ 2 = E1 * (sA ^ 2 * q) * (q / TT) * E1 := by
      rw [mul_pow, mul_pow, mul_pow, hsq]; field_simp
    rw [eL, eR]
    have hx2 : 0 ≤ x0 ^ 2 := sq_nonneg _
    have hF2 : 0 ≤ F ^ 2 := sq_nonneg _
    have hA : 0 ≤ E1 * (sA ^ 2 * q) := by positivity
    have hB : 0 ≤ q / TT := by positivity
    calc Pa ^ 2 * x0 ^ 2 * F ^ 2 ≤ E1 * (sA ^ 2 * q) * x0 ^ 2 * F ^ 2 := by gcongr
      _ ≤ E1 * (sA ^ 2 * q) * (q / TT) * F ^ 2 := by gcongr
      _ ≤ E1 * (sA ^ 2 * q) * (q / TT) * E1 := by gcongr
  have hC : Real.exp 1 * sA * (√TT)⁻¹ * (E1⁻¹ * q) = E1 * sA * (√TT)⁻¹ * q := by
    rw [← hE1sq]; field_simp
  have hfin : Pa * (x0 * F) ≤ Real.exp 1 * sA * (√TT)⁻¹ * qw := by
    rw [← hC] at hmain
    refine hmain.trans (mul_le_mul_of_nonneg_left hqw ?_)
    positivity
  rw [← mul_div_assoc, le_div_iff₀ (mul_pos hx0 hF0)]
  exact hfin

theorem one_add_pow_le_exp (x : ℝ) (hx : 0 ≤ x) (n : ℕ) : (1 + x) ^ n ≤ Real.exp (n * x) := by
  rw [Real.exp_nat_mul]
  exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp x]) n

end real

section xs

theorem xs_eq_prod {S : Type} [Fintype S] [DecidableEq S] (x0 : ℂ → ℂ) :
    ∀ (L : List (Wd.Letter ℂ S)) (e : Wd.Ix S) (Y : ℂ),
      Fr.xs x0 L e Y = x0 Y * (L.map fun l => if e l.intersection_update_fsHerm_neg_one = 0 then Fr.phiL l Y else 1).prod
  | [], _, _ => by simp [Fr.xs]
  | l :: L, e, Y => by
    simp only [Fr.xs, List.map_cons, List.prod_cons]
    rw [xs_eq_prod x0 L e Y]
    ring

theorem phiL_bound (b : Bool) (pt y D : ℝ) (hD : 2 ≤ D) (hd : D + 2 ≤ |y - pt|) :
    0 < (if b then (y + 1 - pt) / (y - pt) else (pt - y - 1) / (pt - y - 2)) ∧
      (if b then (y + 1 - pt) / (y - pt) else (pt - y - 1) / (pt - y - 2)) ≤ 1 + 1 / D := by
  have hD0 : 0 < D := by linarith
  cases b
  · simp only [Bool.false_eq_true, if_false]
    rcases le_or_gt 0 (y - pt) with h | h
    · rw [abs_of_nonneg h] at hd
      have h1 : pt - y - 2 < 0 := by linarith
      have h2 : pt - y - 1 < 0 := by linarith
      constructor
      · exact div_pos_of_neg_of_neg h2 h1
      · rw [div_le_iff_of_neg h1]
        have : 0 < 1 / D := by positivity
        nlinarith
    · rw [abs_of_neg h] at hd
      have h1 : 0 < pt - y - 2 := by linarith
      constructor
      · exact div_pos (by linarith) h1
      · rw [div_le_iff₀ h1]
        have e1 : (1 + 1 / D) * (pt - y - 2) = pt - y - 2 + (pt - y - 2) / D := by ring
        rw [e1]
        have : 1 ≤ (pt - y - 2) / D := by rw [le_div_iff₀ hD0]; linarith
        linarith
  · simp only [if_true]
    rcases le_or_gt 0 (y - pt) with h | h
    · rw [abs_of_nonneg h] at hd
      have h1 : 0 < y - pt := by linarith
      constructor
      · exact div_pos (by linarith) h1
      · rw [div_le_iff₀ h1]
        have e1 : (1 + 1 / D) * (y - pt) = y - pt + (y - pt) / D := by ring
        rw [e1]
        have : 1 ≤ (y - pt) / D := by rw [le_div_iff₀ hD0]; linarith
        linarith
    · rw [abs_of_neg h] at hd
      have h2 : y + 1 - pt < 0 := by linarith
      constructor
      · exact div_pos_of_neg_of_neg h2 h
      · rw [div_le_iff_of_neg h]
        have : 0 < 1 / D := by positivity
        nlinarith

end xs

end

end Formalism.FourierDecayAlt.P.PBL
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.TopRatioAlt
namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt NumberField Finset

noncomputable section

open Classical

theorem topRatio : TopRatio := by
  intro Cb Cc E _ _ _ Wp Wq _ _ _ _ _ _ S p f χ A₀ hB hC v w y hcut hgr hlen hfar e ρ
  have hB' := hB
  obtain ⟨hg1, hg2, -, -, hOkp, hw, hw', hl1, hlk, hne, hGo, -, hLC, hCA, -, hv⟩ := hB'
  have hOK : (D.parOf S v).OK := (p v).hP.1
  have hN20 : (20 : ℝ) ≤ S.Ntop := PBD.ntop_ge S
  set N : ℝ := (S.Ntop : ℝ) with hNdef
  set α := S.cutLo v with hα
  set β := S.cutHi v with hβ

  have hycut : I.OnCut (D.parOf S v).u (D.parOf S v).u' (S.l + 1) y := PBF.cutWord_mem (D.parOf S v) hcut (List.mem_cons_self)
  obtain ⟨m, hm⟩ := hgr
  obtain ⟨hlenI, hpos, -, -, -, hlast⟩ := hGo v
  obtain ⟨hm1, hmN, hgl, hgu⟩ := hpos m y hm
  obtain ⟨hyI, hy1I, hPy, hPy1⟩ := hlast y (Or.inl ⟨m, hm⟩)
  have hI0 : 0 < β - α := by
    have : (0 : ℝ) < 6 * N ^ 3 + 6 * N := by positivity
    linarith
  have hmid1 : α + (β - α) / 3 ≤ y := by
    unfold C.gridL at hgl
    have : 0 ≤ (2 * (m : ℝ) - 2) * ((β - α) / (6 * S.Ntop)) := by
      have hm1' : (1 : ℝ) ≤ m := by exact_mod_cast hm1
      exact mul_nonneg (by linarith) (by positivity)
    linarith
  have hmid2 : y + 1 ≤ β - (β - α) / 3 := by
    unfold C.gridL at hgu
    have hmN' : (m : ℝ) ≤ S.Ntop := by exact_mod_cast hmN
    have hN0 : (0 : ℝ) < S.Ntop := by linarith
    have h6 : (2 * (m : ℝ) - 2) * ((β - α) / (6 * S.Ntop)) + (β - α) / (6 * S.Ntop) ≤ (β - α) / 3 := by
      have hX : 0 ≤ (β - α) / (6 * S.Ntop) := by positivity
      have e2 : (2 * (S.Ntop : ℝ)) * ((β - α) / (6 * S.Ntop)) = (β - α) / 3 := by field_simp; ring
      have := mul_le_mul_of_nonneg_right (show 2 * (m : ℝ) - 1 ≤ 2 * S.Ntop by linarith) hX
      nlinarith
    linarith

  have hyIcc : y ∈ Set.Icc α β := by rw [hα, hβ, ← cutI_eq]; exact hyI
  have hqy : 0 < (M.qC (D.parOf S v) (y : ℂ)).re := q_pos_cut hB v y hyIcc
  set q' : ℝ → ℝ := fun t => (M.qC (D.parOf S v) (t : ℂ)).re with hq'
  set wr : List (Wd.Letter ℝ (Fin w.length)) :=
    (D.positionted w).map fun l => (⟨l.plus, l.intersection_update_fsHerm_neg_one, l.pt.re⟩ : Wd.Letter ℝ (Fin w.length)) with hwr
  have hQ : Wd.qw (M.qC (D.parOf S v)) (D.positionted w) (y : ℂ) = ((Wd.qw q' wr y : ℝ) : ℂ) :=
    weighted_quadratic_of_real (Fin w.length) (M.qC (D.parOf S v)) (D.positionted w) y
      (by rw [PBF.qC_ofReal, Complex.ofReal_im])
      (by intro l hl; unfold D.positionted at hl; obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hl; simp)
  have hLQ : Real.exp (-(1 / 2)) ≤ Wd.qw q' wr y / q' y := by
    have h4 : 4 ≤ S.Ntop := by exact_mod_cast (by linarith : (4 : ℝ) ≤ S.Ntop)
    have hlen' : wr.length ≤ S.Ntop := by simp [hwr, D.positionted]; omega
    refine (lemma_Q_estimate (Fin w.length) q' wr S.Ntop ((S.Ntop : ℝ) ^ 2 + 1) y h4 hlen' le_rfl ?_ hqy.ne').1
    intro l hl
    obtain ⟨l0, hl0, rfl⟩ := List.mem_map.1 hl
    unfold D.positionted at hl0
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hl0
    have hz := hfar (w.get j) (List.get_mem _ _)
    simp only [Complex.ofReal_re]
    by_cases h1 : (w.get j).1 = true
    · rw [if_pos h1]; exact hz.1
    · rw [if_neg h1]; exact ⟨hz.1, hz.2 (by simpa using h1)⟩
  have hqw : 0 < Wd.qw q' wr y := by
    have := (le_div_iff₀ hqy).1 hLQ
    have : 0 < Real.exp (-(1 / 2)) * q' y := mul_pos (Real.exp_pos _) hqy
    linarith

  set rf : Fin w.length → ℝ := fun j => if e j = 0 then
      (if (w.get j).1 then (y + 1 - (w.get j).2) / (y - (w.get j).2)
        else ((w.get j).2 - y - 1) / ((w.get j).2 - y - 2)) else 1 with hrf
  have hxs : Fr.xs (fun Y => M.sgn (D.parOf S v) (S.l + 1) * M.xC (D.parOf S v) ρ Y) (D.positionted w) e ((y : ℂ) + 1) =
      (M.sgn (D.parOf S v) (S.l + 1) * M.xC (D.parOf S v) ρ ((y : ℂ) + 1)) * ((∏ j, rf j : ℝ) : ℂ) := by
    rw [xs_eq_prod]
    congr 1
    unfold D.positionted
    rw [List.map_ofFn, List.prod_ofFn]
    push_cast
    refine Finset.prod_congr rfl fun j _ => ?_
    simp only [Function.comp_apply, hrf]
    by_cases he : e j = 0
    · simp only [he, if_true]
      unfold Fr.phiL
      by_cases hb : (w.get j).1 = true
      · simp only [hb, if_true]; push_cast; ring
      · simp only [hb, Bool.false_eq_true, if_false]; push_cast; ring
    · simp only [he, if_false, Complex.ofReal_one]
  set x0r : ℝ := (-1 : ℝ) ^ (S.G.k - (S.l + 1)) * I.xpoly S.G.k (M.rho (D.parOf S v) ρ) (y + 1) with hx0r
  have hx0 : M.sgn (D.parOf S v) (S.l + 1) * M.xC (D.parOf S v) ρ ((y : ℂ) + 1) = ((x0r : ℝ) : ℂ) := by
    simp only [hx0r, M.sgn, M.xC, I.xpoly, D.parOf]
    push_cast
    rfl
  have hinter := Formalism.FourierDecayAlt.P.types_interlace (D.parOf S v) hOK ρ
  have hx0pos : 0 < x0r := Formalism.FourierDecayAlt.P.interlacing_sign S.G.k (D.parOf S v).u (D.parOf S v).u' (M.rho (D.parOf S v) ρ) (S.l + 1) y (by omega)
    (by omega) hinter hycut 1 (by simp)
  have hD2 : (2 : ℝ) ≤ (S.Ntop : ℝ) ^ 2 - 1 := by nlinarith
  have hrf : ∀ j, 0 < rf j ∧ rf j ≤ 1 + 1 / ((S.Ntop : ℝ) ^ 2 - 1) := by
    intro j
    simp only [hrf]
    by_cases he : e j = 0
    · simp only [he, if_true]
      exact phiL_bound (w.get j).1 (w.get j).2 y _ hD2 (by linarith [(hfar (w.get j) (List.get_mem _ _)).1])
    · simp only [he, if_false]
      exact ⟨one_pos, by have : (0 : ℝ) ≤ 1 / ((S.Ntop : ℝ) ^ 2 - 1) := by positivity
                         linarith⟩
  have hF0 : 0 < ∏ j, rf j := Finset.prod_pos fun j _ => (hrf j).1
  have hF1 : ∏ j, rf j ≤ Real.exp ((S.Ntop : ℝ) / ((S.Ntop : ℝ) ^ 2 - 1)) := by
    calc ∏ j, rf j ≤ ∏ _j : Fin w.length, (1 + 1 / ((S.Ntop : ℝ) ^ 2 - 1)) :=
          Finset.prod_le_prod₀ (fun j _ => (hrf j).1.le) fun j _ => (hrf j).2
      _ = (1 + 1 / ((S.Ntop : ℝ) ^ 2 - 1)) ^ w.length := by simp
      _ ≤ Real.exp (w.length * (1 / ((S.Ntop : ℝ) ^ 2 - 1))) := one_add_pow_le_exp _ (by positivity) _
      _ ≤ Real.exp ((S.Ntop : ℝ) / ((S.Ntop : ℝ) ^ 2 - 1)) := by
          apply Real.exp_le_exp.2
          rw [mul_one_div]
          apply div_le_div_of_nonneg_right _ (by linarith)
          exact_mod_cast hlen.le

  have hR : topR (S.l + 1) w e ρ y = ((Wd.qw q' wr y / (x0r * ∏ j, rf j) : ℝ) : ℂ) := by
    unfold topR
    rw [hQ, hxs, hx0]
    push_cast
    ring
  rw [hR, Complex.ofReal_re, Complex.ofReal_im]
  refine ⟨div_pos hqw (mul_pos hx0pos hF0), rfl, ?_⟩
  set C0 := Real.exp 1 * J.supA S.G S.de S.de' S.T S.T' S.l false (S.pl v) * (√(S.T * S.T'))⁻¹ with hC0
  set F := ∏ j, rf j with hFdef
  set Cf := S.G.place (S.pl v) with hCf
  have hT : 0 < S.T := hOK.T_pos
  have hT' : 0 < S.T' := hOK.T'_pos
  have hTT : 0 < S.T * S.T' := mul_pos hT hT'
  obtain ⟨hg, hk⟩ := glob_posT hB
  have hsA := supA_nonneg S hg hk v false

  have hIR := Formalism.FourierDecayAlt.P.interlacing_ratio S.G.k (D.parOf S v).u (D.parOf S v).u' (M.rho (D.parOf S v) ρ)
    (S.l + 1) y (by omega) (by omega) hinter hycut
  have hul : 1 ≤ |y + 1 / 2 + (D.parOf S v).u (S.l + 1)| * |y + 1 / 2 + (D.parOf S v).u' (S.l + 1)| := by
    rcases hycut with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [abs_of_neg (by linarith), abs_of_pos (by linarith)]; nlinarith
    · rw [abs_of_pos (by linarith), abs_of_neg (by linarith)]; nlinarith
  have hqprod : q' y = -(S.T * S.T') * ((∏ i ∈ Icc 1 S.G.k, (y + 1 / 2 + (D.parOf S v).u i)) *
      ∏ i ∈ Icc 1 S.G.k, (y + 1 / 2 + (D.parOf S v).u' i)) := by
    simp only [hq']
    rw [PBF.qC_ofReal, Complex.ofReal_re, ← Finset.prod_mul_distrib]
  have hx0sq : x0r ^ 2 ≤ q' y / (S.T * S.T') := by
    have e1 : x0r ^ 2 = I.xpoly S.G.k (M.rho (D.parOf S v) ρ) (y + 1) ^ 2 := by
      rw [hx0r, mul_pow, ← pow_mul, mul_comm (S.G.k - (S.l + 1)) 2, pow_mul, neg_one_sq, one_pow, one_mul]
    have hq := hqy
    change 0 < q' y at hq
    rw [hqprod] at hq
    rw [e1, le_div_iff₀ hTT, hqprod]
    generalize (∏ i ∈ Icc 1 S.G.k, (y + 1 / 2 + (D.parOf S v).u i)) = A at hq hIR ⊢
    generalize (∏ i ∈ Icc 1 S.G.k, (y + 1 / 2 + (D.parOf S v).u' i)) = B at hq hIR ⊢
    generalize I.xpoly S.G.k (M.rho (D.parOf S v) ρ) (y + 1) = X at hIR ⊢
    generalize |y + 1 / 2 + (D.parOf S v).u (S.l + 1)| * |y + 1 / 2 + (D.parOf S v).u' (S.l + 1)| = U at hIR hul
    have hAB : A * B < 0 := by
      by_contra h
      push_neg at h
      have h3 := mul_nonneg hTT.le h
      have h4 : -(S.T * S.T') * (A * B) = -(S.T * S.T' * (A * B)) := by ring
      linarith
    rw [abs_of_neg hAB] at hIR
    have hX2 : 0 ≤ X ^ 2 := sq_nonneg X
    have h1 : X ^ 2 ≤ -(A * B) :=
      calc X ^ 2 = X ^ 2 * 1 := (mul_one _).symm
        _ ≤ X ^ 2 * U := mul_le_mul_of_nonneg_left hul hX2
        _ ≤ -(A * B) := hIR
    have h5 := mul_le_mul_of_nonneg_left h1 hTT.le
    have h6 : -(S.T * S.T') * (A * B) = S.T * S.T' * -(A * B) := by ring
    rw [h6, mul_comm (X ^ 2)]
    exact h5

  have hroot : ∀ t ∈ Icc 1 (Cf.k + Cf.m - 1), -Cf.lam t < α ∨ β < -Cf.lam t := by
    intro t ht
    by_contra hcon
    push_neg at hcon
    have hmem : -Cf.lam t ∈ Cf.cutI S.l := by rw [hCf, cutI_eq]; exact ⟨hcon.1, hcon.2⟩
    have hfac := (Formalism.FourierDecayAlt.P.betaFactorisation Cf S.de S.de' S.G.ka S.T S.T' (-Cf.lam t) S.l (hOkp v)
      hw hw' hT hT' hl1 hlk hne hmem).2.1
    apply hfac
    unfold Sz.Cfg.P
    exact Finset.prod_eq_zero ht (by ring)
  have hI3 : 3 ≤ β - α := three_le_len _ _ hN20 hlenI
  have hPr := pratio (Icc 1 (Cf.k + Cf.m - 1)) Cf.lam α β y hI3 hroot hmid1 hmid2
  have hPy : S.P v y = ∏ t ∈ Icc 1 (Cf.k + Cf.m - 1), (y + Cf.lam t) := rfl
  have hPy1 : S.P v (y + 1) = ∏ t ∈ Icc 1 (Cf.k + Cf.m - 1), (y + 1 + Cf.lam t) := rfl
  rw [← hPy, ← hPy1, Nat.card_Icc] at hPr
  have hn6 : 6 * ((Cf.k + Cf.m - 1 + 1 - 1 : ℕ) : ℝ) ≤ β - α := by
    have hLv := hLC v
    have hCc1 : 1 ≤ Cc := by linarith [Real.add_one_le_exp 1]
    have hm : Cf.m = 2 * S.G.r + 2 := rfl
    have hkk : Cf.k = S.G.k := rfl
    rw [hm, hkk]
    have hk1 : 1 ≤ S.G.k := by omega
    push_cast [show S.G.k + (2 * S.G.r + 2) - 1 + 1 - 1 = S.G.k + 2 * S.G.r + 1 by omega]
    have hr0 : (0 : ℝ) ≤ S.G.r := Nat.cast_nonneg _
    have hkR : (1 : ℝ) ≤ S.G.k := by exact_mod_cast hk1
    have := long_bound (S.G.k : ℝ) (S.G.r : ℝ) (S.Ntop : ℝ) Cc (β - α) hkR hr0 hN20 hCc1 hLv
    linarith

  set n := Cf.k + Cf.m - 1 + 1 - 1 with hn
  set E1 := Real.exp (1 / 2) with hE1
  have hE1pos : 0 < E1 := Real.exp_pos _
  have hE1sq : E1 ^ 2 = Real.exp 1 := by rw [hE1, ← Real.exp_nat_mul]; norm_num
  have hEinv : Real.exp (-(1 / 2)) = E1⁻¹ := by rw [hE1, Real.exp_neg]
  have hρP : (1 + 3 / (β - α)) ^ n ≤ E1 := by
    refine (one_add_pow_le_exp _ (by positivity) n).trans (Real.exp_le_exp.2 ?_)
    rw [mul_div_assoc', div_le_iff₀ (by linarith)]
    linarith
  have hF2 : F ^ 2 ≤ E1 := by
    have hN20' : (20 : ℝ) ≤ S.Ntop := hN20
    have h1 : F ^ 2 ≤ Real.exp ((S.Ntop : ℝ) / ((S.Ntop : ℝ) ^ 2 - 1)) ^ 2 := pow_le_pow_left₀ hF0.le hF1 2
    refine h1.trans ?_
    rw [← Real.exp_nat_mul, hE1]
    exact Real.exp_le_exp.2 (two_N_bound _ hN20').2

  have hyI' : y ∈ Cf.cutI S.l := hyI
  have hcore := core_le_supA hB v false y (by simpa using hyI')
  have hqeq : Cf.q S.de S.de' S.T S.T' y = q' y := (qC_re S v y).symm
  have hcore2 : |S.P v y * S.P v (y + 1)| = Cf.core S.de S.de' S.T S.T' y ^ 2 * q' y := by
    unfold Sz.Cfg.core
    rw [Real.sq_sqrt (abs_nonneg _), hqeq, abs_div, abs_of_pos hqy]
    have hPP : S.P v y * S.P v (y + 1) = Cf.P y * Cf.P (y + 1) := rfl
    rw [hPP, div_mul_cancel₀ _ hqy.ne']
  have hcore0 : 0 ≤ Cf.core S.de S.de' S.T S.T' y := Real.sqrt_nonneg _
  have hP2 : S.P v y ^ 2 ≤ E1 * (J.supA S.G S.de S.de' S.T S.T' S.l false (S.pl v) ^ 2 * q' y) := by
    have h1 : S.P v y ^ 2 = |S.P v y| * |S.P v y| := by rw [sq, abs_mul_abs_self]
    have h2 : |S.P v y| * |S.P v y| ≤ |S.P v y| * ((1 + 3 / (β - α)) ^ n * |S.P v (y + 1)|) :=
      mul_le_mul_of_nonneg_left hPr (abs_nonneg _)
    have h3 : |S.P v y| * ((1 + 3 / (β - α)) ^ n * |S.P v (y + 1)|) =
        (1 + 3 / (β - α)) ^ n * (Cf.core S.de S.de' S.T S.T' y ^ 2 * q' y) := by
      rw [← hcore2, abs_mul]; ring
    have h4 : Cf.core S.de S.de' S.T S.T' y ^ 2 ≤ J.supA S.G S.de S.de' S.T S.T' S.l false (S.pl v) ^ 2 :=
      pow_le_pow_left₀ hcore0 hcore 2
    have h5 : (1 + 3 / (β - α)) ^ n * (Cf.core S.de S.de' S.T S.T' y ^ 2 * q' y) ≤
        E1 * (J.supA S.G S.de S.de' S.T S.T' S.l false (S.pl v) ^ 2 * q' y) := by
      exact mul_le_mul hρP (mul_le_mul_of_nonneg_right h4 hqy.le) (mul_nonneg (pow_nonneg hcore0 2) hqy.le) hE1pos.le
    calc S.P v y ^ 2 = |S.P v y| * |S.P v y| := h1
      _ ≤ _ := h2
      _ = _ := h3
      _ ≤ _ := h5
  have hqw2 : E1⁻¹ * q' y ≤ Wd.qw q' wr y := by rw [← hEinv]; exact (le_div_iff₀ hqy).1 hLQ
  exact final_cmp |S.P v y| x0r F (q' y) (S.T * S.T') _ E1 (Wd.qw q' wr y) (abs_nonneg _) hx0pos hF0 hqy hTT
    hsA hE1pos hE1sq (by rw [sq_abs]; exact hP2) hx0sq hF2 hqw2

end

end Formalism.FourierDecayAlt.P.PBL

theorem Formalism.FourierDecayAlt.P.top_ratio : Formalism.FourierDecayAlt.P.PBL.TopRatio := Formalism.FourierDecayAlt.P.PBL.topRatio
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.BuiltBoundsCompactOfHeadTop
namespace Formalism.FourierDecayAlt.P

theorem built_bounds_compact_of_head_top (hH : Formalism.FourierDecayAlt.KB.HeadTop) : Formalism.FourierDecayAlt.KB.BuiltBounds2Cpt := fun hA =>
  built_bounds_compact_of_leaves radial_head hH degree_of_lift_pairing top_local_built_places degree_top
    top_ratio (germ_parts_compact_support kernel_continuity_built germ_rate_bound hA)
    (fun hA' => uniform_decay_of_place hA' radial_head hH
      (uniform_decay_of_heads radial_head hH)) hA

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.PbBuiltBounds2CptOfMkTop
namespace Formalism.FourierDecayAlt.P

theorem pb_builtBounds2Cpt_of_mkTop (hM : CutEX.MkTop) : Formalism.FourierDecayAlt.KB.BuiltBounds2Cpt :=
  built_bounds_compact_of_head_top (pb_headTop_of_mkTop hM)

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.BuiltBoundsCompact
namespace Formalism.FourierDecayAlt.P

theorem built_bounds_compact : Formalism.FourierDecayAlt.KB.BuiltBounds2Cpt := pb_builtBounds2Cpt_of_mkTop top_truncation_of_averages

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.JcRadialModuleFormOfParts
namespace Formalism.FourierDecayAlt.Final

theorem pb_builtBounds2Cpt : Formalism.FourierDecayAlt.KB.BuiltBounds2Cpt := Formalism.FourierDecayAlt.P.built_bounds_compact

end Formalism.FourierDecayAlt.Final
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CarrierNeedsFromD
namespace GlobalTheory

theorem carrierNeedsFromD :
    Formalism.FourierDecayAlt.P5.ThmPActualCpt ∧ Formalism.FourierDecayAlt.JCT.ModelPlaceBuilt2 ∧ Formalism.FourierDecayAlt.KB.BuiltBounds2Cpt :=
  ⟨Formalism.FourierDecayAlt.P.CutSE.actual_compact_theorem, Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity.model_place_built_holds,
    Formalism.FourierDecayAlt.Final.pb_builtBounds2Cpt⟩

end GlobalTheory
end

set_option linter.unusedVariables false

noncomputable section

section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.CarrierT

open MeasureTheory Matrix
open scoped InnerProductSpace

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.L2.SG.AmpOrbPf

namespace GlobalTheory.CarrierGap
theorem ampVec_genG (hJ : CompanionTheory.Lime.BM.UniqGap) (hI : CompanionTheory.D.Upq.BesselFunctionalConstruction.Inputs) (hAt : CompanionTheory.Lime.BM.AtFormAdmOne) (hAKF : Formalism.MainNotions.S.Pv.AmpDD.BM.AmpKF)
    (hCC : Formalism.MainNotions.S.Pv.AmpDD.CellConv) {D : D7} {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT C0 Cn : ℝ}
    (hGap : Formalism.MainNotions.S.Pv.AmpDD.GapOfHyp0 D large₂ C' Cl Cg cb Cu cT CT C0 Cn)
    (hNV : Formalism.MainNotions.S.Pv.AmpDD.NVHyp D large₂ C' Cl Cg cb Cu cT CT C0 Cn)
    (hH : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) (τ : D.what₂.Tau) (w w' : D.what₂.Word) (hTT : HypTT D w w')
    (θ : ℝ) (W : LocW D.R.k D.R.rS) (hW : GoodW D τ w w' θ W) (lam' : Fin (2 * D.R.rS + D.R.k + 1) → ℝ)
    (hl : l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3) (A : LocS W) (hA : GoodS D lam' A)
    (hT : 0 < Tr D w) (hT' : 0 < Tr D w') (a b : A.H) (ξ : W.Wp) (ξ' : W.Wq)
    (hka : PI.UpqRep.IsKFinHpk (k := D.R.k) (r := D.R.rS) A.σ a)
    (hkb : PI.UpqRep.IsKFinHpk (k := D.R.k) (r := D.R.rS) A.σ b)
    (hn : ⟪A.B a, ξ⟫_ℂ * ⟪ξ', A.B' b⟫_ℂ ≠ 0) :
    ∃ κ : ℂ, κ ≠ 0 ∧ ∀ (γ : MatKR D.R.k D.R.rS) (μR νR : Measure (Mt D.R.k D.R.rS)) (ν : Measure (PairSp D.R.k D.R.rS)),
      Formalism.MainNotions.S.Pv.AmpDD.CellData (toBessel D τ w w' θ W lam' A hW hA hT hT') W.μG γ μR νR ν →
      OrbInt (toBessel D τ w w' θ W lam' A hW hA hT hT')
        (Formalism.MainNotions.S.Pv.AmpDD.coefF (toBessel D τ w w' θ W lam' A hW hA hT hT') a b ξ ξ') γ ν = κ • A.J νR γ := by
  obtain ⟨h, hg, hok, hcell⟩ := hGap hH τ lam' hl
  set L := toBessel D τ w w' θ W lam' A hW hA hT hT' with hL
  set w0 : A.H := (((‖A.v0‖⁻¹ : ℝ) : ℂ) • A.v0) with hw0def
  obtain ⟨l, l', hl1, hl1', hOP⟩ := Formalism.L2.SG.AmpOrbPf.BM.ls_pair hI hAt hW hA hT hT' hg hok
  have hw0 : PI.UpqRep.IsLowUnitH D.R.k D.R.rS (epsSH D.R) lam' A.σ w0 := lowest_K_type_unit hA
  have hKS : PI.KFinSmooth := hI.2.2.1
  have hG : IsHaarOn (UH (Hpk D.R.k D.R.rS)) W.μG := hW.2.2.2.2.2.2.1
  have hDDs : ∀ x ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp A.σ w0, x ∈ PI.UpqRep.smoothVecs (k := D.R.k) (r := D.R.rS) A.σ :=
    Formalism.FourierDecayAlt.P.DDSmoothness.DD_smooth hKS hA.1 hA.2.1 hw0
  obtain ⟨⟨x, hx, y, hy, hxy⟩, ⟨x', hx', y', hy', hxy'⟩⟩ :=
    hNV hH τ w w' hTT θ W hW lam' hl A hA hT hT' w0 hw0
  have hlx : l x ≠ 0 := by
    intro h0; apply hxy
    have e : Formalism.FourierDecayAlt.ThreeDimData.be W.z L.c W.π A.σ W.μW L.μN x y = (innerSL ℂ (l y)).smulRight (l x) :=
      hOP.1.2.2.2.2.2.1 x hx y hy
    rw [e, h0]; ext; simp
  have hlx' : l' x' ≠ 0 := by
    intro h0; apply hxy'
    have e : Formalism.FourierDecayAlt.ThreeDimData.be W.z' L.c W.π' A.σ W.μW' L.μN x' y' = (innerSL ℂ (l' y')).smulRight (l' x') :=
      hOP.1.2.2.2.2.2.2 x' hx' y' hy'
    rw [e, h0]; ext; simp
  have hB : PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z
      (PI.BesselMapUniq.psiGen D.R.k D.R.rS W.z (fun _ => L.c)) A.σ W.π A.B := by
    rw [psiGen_const]; exact (Formalism.MainNotions.BridgeCS3d.isBesselMapSm_iff _ _ _ _ _).1 hA.2.2.1
  have hB' : PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z'
      (PI.BesselMapUniq.psiGen D.R.k D.R.rS W.z' (fun _ => L.c)) A.σ W.π' A.B' := by
    rw [psiGen_const]; exact (Formalism.MainNotions.BridgeCS3d.isBesselMapSm_iff _ _ _ _ _).1 hA.2.2.2.1
  have hlG : PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z
      (PI.BesselMapUniq.psiGen D.R.k D.R.rS W.z (fun _ => L.c)) A.σ W.π l := by
    rw [psiGen_const]; exact hl1
  have hlG' : PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z'
      (PI.BesselMapUniq.psiGen D.R.k D.R.rS W.z' (fun _ => L.c)) A.σ W.π' l' := by
    rw [psiGen_const]; exact hl1'
  obtain ⟨c0, hc0⟩ := CompanionTheory.Lime.BM.aIsL hJ hg hok hA.1 hA.2.1 L.hz.1 L.hz.2 (fun _ => c_ne_zero D) L.hπ hB hlG
    ⟨x, hDDs x hx, hlx⟩
  obtain ⟨c0', hc0'⟩ := CompanionTheory.Lime.BM.aIsL hJ hg hok hA.1 hA.2.1 L.hz'.1 L.hz'.2 (fun _ => c_ne_zero D) L.hπ' hB' hlG'
    ⟨x', hDDs x' hx', hlx'⟩
  have has : a ∈ PI.UpqRep.smoothVecs (k := D.R.k) (r := D.R.rS) A.σ := hKS _ _ _ _ _ A.σ hA.1 hA.2.1 a hka
  have hbs : b ∈ PI.UpqRep.smoothVecs (k := D.R.k) (r := D.R.rS) A.σ := hKS _ _ _ _ _ A.σ hA.1 hA.2.1 b hkb
  have hBa : A.B a = c0 • l a := hc0 a has
  have hBb : A.B' b = c0' • l' b := hc0' b hbs
  rw [hBa, hBb, inner_smul_left, inner_smul_right] at hn
  have hc0ne : c0 ≠ 0 := by
    intro h0; apply hn; rw [h0]; simp
  have hc0ne' : c0' ≠ 0 := by
    intro h0; apply hn; rw [h0]; simp
  set s : ℂ := ⟪l a, ξ⟫_ℂ * ⟪ξ', l' b⟫_ℂ with hs
  have hs0 : s ≠ 0 := by
    intro h0; apply hn
    have : (starRingEnd ℂ) c0 * ⟪l a, ξ⟫_ℂ * (c0' * ⟪ξ', l' b⟫_ℂ) = (starRingEnd ℂ) c0 * c0' * s := by
      rw [hs]; ring
    rw [this, h0, mul_zero]
  set t : ℂ := ((‖A.v0‖ : ℝ) : ℂ) with ht
  have hv0ne : A.v0 ≠ 0 := hA.2.2.2.2.2.1
  have hv0 : A.v0 = t • w0 := by
    rw [hw0def, ht, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv0ne),
      Complex.ofReal_one, one_smul]
  have hw0s : w0 ∈ PI.UpqRep.smoothVecs (k := D.R.k) (r := D.R.rS) A.σ :=
    Formalism.FourierDecayAlt.P.DDSmoothness.smooth_smul _ hA.2.2.2.2.1
  have hΦ : ∀ g ∈ UH (Hpk D.R.k D.R.rS), A.Φ g = (c0 * t) • l (A.σ g w0) := by
    intro g hg'
    show A.B (A.σ g A.v0) = _
    rw [hv0]
    exact orbit_mul hA.2.1 c0 hc0 hl1.2.1 hw0s t hg'
  have hΦ' : ∀ g ∈ UH (Hpk D.R.k D.R.rS), A.Φ' g = (c0' * t) • l' (A.σ g w0) := by
    intro g hg'
    show A.B' (A.σ g A.v0) = _
    rw [hv0]
    exact orbit_mul hA.2.1 c0' hc0' hl1'.2.1 hw0s t hg'
  have ht0 : t ≠ 0 := by
    rw [ht]; exact_mod_cast (norm_ne_zero_iff.mpr hv0ne)
  have hcN : (A.cN : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hA.2.2.2.2.2.2.2.1)
  set K1 : ℂ := ((A.cN : ℂ)⁻¹) * (c0 * t) * (starRingEnd ℂ) (c0' * t) with hK1
  have hK10 : K1 ≠ 0 := by
    rw [hK1]
    refine mul_ne_zero (mul_ne_zero (inv_ne_zero hcN) (mul_ne_zero hc0ne ht0)) ?_
    exact (map_ne_zero _).mpr (mul_ne_zero hc0ne' ht0)
  have hw1 : ‖w0‖ = 1 := by
    rw [hw0def, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv0ne)
  set dg : ℂ := (PI.BesselPeriodGGP.fdegH W.μG A.σ w0 : ℂ) with hdg
  have hdg0 : dg ≠ 0 := by
    rw [hdg]
    exact_mod_cast (ne_of_gt (Formalism.L2.S.Pv.AmpOrbCoef.fdegH_pos hA.1 hA.2.1 hG hw1))
  refine ⟨dg * s * K1⁻¹, mul_ne_zero (mul_ne_zero hdg0 hs0) (inv_ne_zero hK10), ?_⟩
  intro γ μR νR ν hCD
  obtain ⟨hγ, hGf, hMono, hRel, hRH, hOQ, hqR⟩ := hCD
  have hCD' : Formalism.MainNotions.S.Pv.AmpDD.CellData L W.μG γ μR νR ν := ⟨hγ, hGf, hMono, hRel, hRH, hOQ, hqR⟩
  obtain ⟨bb, hb0, hbm, hbi⟩ := hCC _ _ L h W.μG γ μR νR ν ENNReal.ofReal_ne_top hok hcell hCD' hMono
  have hAmp := hAKF hI _ _ L h W.μG w0 l l' hOP γ μR νR ν hCD' bb hb0 hbm hbi a b hka hkb ξ ξ'
  have hae := ae_UH_conj hγ hG hRH hqR
  have hJ1 : A.J νR γ = K1 • ampJ νR 1 (fun g => l (A.σ g w0)) (fun g => l' (A.σ g w0)) γ :=
    ampJ_mul νR A.cN A.Φ _ A.Φ' _ (c0 * t) (c0' * t) γ hγ hΦ hΦ' hae
  have hAmp' : s • ampJ νR 1 (fun g => l (A.σ g w0)) (fun g => l' (A.σ g w0)) γ =
      dg⁻¹ • OrbInt L (Formalism.MainNotions.S.Pv.AmpDD.coefF L a b ξ ξ') γ ν := hAmp
  have e1 : OrbInt L (Formalism.MainNotions.S.Pv.AmpDD.coefF L a b ξ ξ') γ ν =
      dg • (s • ampJ νR 1 (fun g => l (A.σ g w0)) (fun g => l' (A.σ g w0)) γ) := by
    rw [hAmp']; exact (smul_inv_smul₀ hdg0 _).symm
  have e2 : ampJ νR 1 (fun g => l (A.σ g w0)) (fun g => l' (A.σ g w0)) γ = K1⁻¹ • A.J νR γ := by
    rw [hJ1, smul_smul, inv_mul_cancel₀ hK10, one_smul]
  rw [e1, e2]
  simp only [smul_smul, mul_assoc]
  rfl

variable [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] [Fact Formalism.L2.SG.LitS.PfNVG.BesselNVG] in
theorem ampVec_carrierG (hJ : CompanionTheory.Lime.BM.UniqGap) {D : D7} (large₂ : SizeData₂ D) {C' Cl Cg cb Cu cT CT C0 : ℝ}
    (hCl : 1000 ≤ Cl) (hH : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0)
    {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {θ : ℝ} {C : Formalism.L2.SG.LocWSOf.Choice X θ} (hB : Formalism.L2.SG.LocWSOf.WuBessel C)
    (u u' : D.what₂.Word) (τ : D.what₂.Tau) (hTT : HypTT D u u')
    (hW : GoodW D τ u u' θ (Formalism.L2.SG.LocWSOf.locW C u u' τ))
    (hA : GoodS D (lamD D τ) (Formalism.L2.SG.LocWSOf.locS hB u u' τ)) (hT : 0 < Tr D u) (hT' : 0 < Tr D u')
    (a b : X.B.H (Formalism.L2.SG.LocWSOf.vOf X τ)) (ξ : X.Vloc u (Formalism.L2.SG.LocWSOf.vOf X τ))
    (ξ' : X.Vloc u' (Formalism.L2.SG.LocWSOf.vOf X τ)) (c : ℂ) (hpin : CoefPin hB u u' τ a b ξ ξ' c)
    (hscl : Formalism.L2.SG.LocWSOf.sclOf hB u u' τ ≠ 0) :
    ∃ κ : ℂ, κ ≠ 0 ∧ ∀ (γ : MatKR D.R.k D.R.rS) (μR νR : Measure (Mt D.R.k D.R.rS)) (ν : Measure (PairSp D.R.k D.R.rS)),
      Formalism.MainNotions.S.Pv.AmpDD.CellData (toBessel D τ u u' θ (Formalism.L2.SG.LocWSOf.locW C u u' τ) (lamD D τ)
        (Formalism.L2.SG.LocWSOf.locS hB u u' τ) hW hA hT hT') (Formalism.L2.SG.LocWSOf.locW C u u' τ).μG γ μR νR ν →
      OrbInt (toBessel D τ u u' θ (Formalism.L2.SG.LocWSOf.locW C u u' τ) (lamD D τ) (Formalism.L2.SG.LocWSOf.locS hB u u' τ)
          hW hA hT hT')
        (Formalism.MainNotions.S.Pv.BetaCut.coefM (Formalism.L2.SG.LocWSOf.sigB X (C.Q τ) (C.Qi τ) τ) a b ξ ξ') γ ν =
        κ • (Formalism.L2.SG.LocWSOf.locS hB u u' τ).J νR γ := by
  obtain ⟨hka, hkb, hn1, -⟩ := hpin
  have hn : ⟪(Formalism.L2.SG.LocWSOf.locS hB u u' τ).B a, ξ⟫_ℂ * ⟪ξ', (Formalism.L2.SG.LocWSOf.locS hB u u' τ).B' b⟫_ℂ ≠ 0 := by
    show ⟪Formalism.L2.SG.LocWSOf.bOf hB u τ a, ξ⟫_ℂ *
      ⟪ξ', Formalism.L2.SG.LocWSOf.sclOf hB u u' τ • Formalism.L2.SG.LocWSOf.bOf hB u' τ b⟫_ℂ ≠ 0
    rw [inner_smul_right]
    have e : ⟪Formalism.L2.SG.LocWSOf.bOf hB u τ a, ξ⟫_ℂ *
        (Formalism.L2.SG.LocWSOf.sclOf hB u u' τ * ⟪ξ', Formalism.L2.SG.LocWSOf.bOf hB u' τ b⟫_ℂ) =
        Formalism.L2.SG.LocWSOf.sclOf hB u u' τ *
          (⟪Formalism.L2.SG.LocWSOf.bOf hB u τ a, ξ⟫_ℂ * ⟪ξ', Formalism.L2.SG.LocWSOf.bOf hB u' τ b⟫_ℂ) := by ring
    rw [e, hn1, mul_one]
    exact hscl
  have hl : l1dist (lamD D τ) (lamD D τ) ≤ (0 : ℝ) * D.R.k * (D.R.m : ℝ) ^ 3 := by
    simp [l1dist]
  exact ampVec_genG hJ CompanionTheory.Lime.BM.inputs (CompanionTheory.Lime.BM.atFormAdmOne hJ)
    Formalism.MainNotions.S.Pv.AmpDDPf.BM.amplitude_K_finite Formalism.MainNotions.S.Pv.AmpDDPf.cell_convergence
    (Formalism.MainNotions.S.Pv.AmpDDPf.gap_of_hypotheses D large₂ C' Cl Cg cb Cu cT CT C0 0 hCl (by linarith))
    (Formalism.L2.S.Pv.NonVacuity.nvHyp0 D large₂ C' Cl Cg cb Cu cT CT C0 (by linarith)) hH τ u u' hTT θ _ hW (lamD D τ) hl _ hA
    hT hT' a b ξ ξ' hka hkb hn

end GlobalTheory.CarrierGap
end

section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.Carrier.CarPinTor

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.FrameBoundFromBesselTorus Formalism.L2.S.Pv.AmpNZTie
open Formalism.BasicNotions Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.RealObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {θ : ℝ} (C : Choice X θ) (hB : WuBessel C)

namespace GlobalTheory.CarrierGap
open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.CarrierT Formalism.L2.SG.Pf.BaseOf in
variable [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] [Fact Formalism.L2.SG.LitS.PfNVG.BesselNVG] in
def ccOneG (hJ : CompanionTheory.Lime.BM.UniqGap) (large₂ : SizeData₂ D) {C' Cl Cg cb Cu cT CT C0 : ℝ}
    (hCl : 1000 ≤ Cl) (hH0 : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) (u u' : D.what₂.Word) (τ : D.what₂.Tau)
    (hTT : HypTT D u u') (hW : GoodW D τ u u' θ (locW C u u' τ)) (hA : GoodS D (lamD D τ) (locS hB u u' τ))
    (hT : 0 < Tr D u) (hT' : 0 < Tr D u') (a b : X.B.H (vOf X τ)) (ξ : X.Vloc u (vOf X τ)) (ξ' : X.Vloc u' (vOf X τ))
    (hpin1 : CoefPin hB u u' τ a b ξ ξ' 1) (hscl : sclOf hB u u' τ ≠ 0) : ℂ :=
  lamPl (cOf hB u τ) (sclOf hB u u' τ)
    (ampVec_carrierG hJ large₂ hCl hH0 hB u u' τ hTT hW hA hT hT' a b ξ ξ' 1 hpin1 hscl).choose D θ
    (muN_eq_haarLie D.R.k D.R.rS).choose

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.CarrierT Formalism.L2.SG.Pf.BaseOf in
variable [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] [Fact Formalism.L2.SG.LitS.PfNVG.BesselNVG] in
theorem ccOne_neG (hJ : CompanionTheory.Lime.BM.UniqGap) (large₂ : SizeData₂ D) {C' Cl Cg cb Cu cT CT C0 : ℝ}
    (hCl : 1000 ≤ Cl) (hH0 : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) (u u' : D.what₂.Word) (τ : D.what₂.Tau)
    (hTT : HypTT D u u') (hW : GoodW D τ u u' θ (locW C u u' τ)) (hA : GoodS D (lamD D τ) (locS hB u u' τ))
    (hT : 0 < Tr D u) (hT' : 0 < Tr D u') (a b : X.B.H (vOf X τ)) (ξ : X.Vloc u (vOf X τ)) (ξ' : X.Vloc u' (vOf X τ))
    (hpin1 : CoefPin hB u u' τ a b ξ ξ' 1) (hscl : sclOf hB u u' τ ≠ 0) (hcO : cOf hB u τ ≠ 0) :
    ccOneG C hB hJ large₂ hCl hH0 u u' τ hTT hW hA hT hT' a b ξ ξ' hpin1 hscl ≠ 0 := by
  obtain ⟨h0, h1, -⟩ := (muN_eq_haarLie D.R.k D.R.rS).choose_spec
  exact lamPl_ne _ _ _ D θ _ hcO hscl
    (ampVec_carrierG hJ large₂ hCl hH0 hB u u' τ hTT hW hA hT hT' a b ξ ξ' 1 hpin1 hscl).choose_spec.1 h0 h1
    (Formalism.L2.SG.AmpOrbPf.kapN_ne_zero hW)

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.CarrierT Formalism.L2.SG.Pf.BaseOf in
variable [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] [Fact Formalism.L2.SG.LitS.PfNVG.BesselNVG] in
theorem pinAt_oneG (hJ : CompanionTheory.Lime.BM.UniqGap) (large₂ : SizeData₂ D) {C' Cl Cg cb Cu cT CT C0 : ℝ}
    (hCl : 1000 ≤ Cl) (hH0 : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) (u u' : D.what₂.Word) (τ : D.what₂.Tau)
    (hTT : HypTT D u u') (hW : GoodW D τ u u' θ (locW C u u' τ)) (hA : GoodS D (lamD D τ) (locS hB u u' τ))
    (hT : 0 < Tr D u) (hT' : 0 < Tr D u') (a b : X.B.H (vOf X τ)) (ξ : X.Vloc u (vOf X τ)) (ξ' : X.Vloc u' (vOf X τ))
    (hpin1 : CoefPin hB u u' τ a b ξ ξ' 1) (hscl : sclOf hB u u' τ ≠ 0) (hcO : cOf hB u τ ≠ 0) (A₀ : ℝ)
    (hA₀ : Formalism.FourierDecayAlt.P.orbital_integral_converges.choose * ((D.R.rS : ℝ) + 1) ^ 2 *
      ((D.R.rS : ℝ) * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) + 1) ≤ A₀)
    (hCC : Formalism.FourierDecayAlt.B.InCC A₀ 1
      (fcAt C u u' τ a b ξ ξ' (ccOneG C hB hJ large₂ hCl hH0 u u' τ hTT hW hA hT hT' a b ξ ξ' hpin1 hscl)))
    (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) (μRv ν : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ))))
    (hP : PinHypAt C u u' τ γ μRv ν) :
    (haveI := FiniteDimensional.complete ℂ (X.Vloc u (vOf X τ));
      Jv ν (X.Wloc u (vOf X τ)) (X.Wloc u' (vOf X τ)) γ) =
      Formalism.FourierDecayAlt.D.orbJ (baseOf X C u u' (vOf X τ)) (trG (Qc X C (vOf X τ)) (Qic X C (vOf X τ)) γ)
        (μRv.map (fun x => Matrix.of.symm (trG (Qc X C (vOf X τ)) (Qic X C (vOf X τ)) x)))
        (fcAt C u u' τ a b ξ ξ' (ccOneG C hB hJ large₂ hCl hH0 u u' τ hTT hW hA hT hT' a b ξ ξ' hpin1 hscl)) := by
  set cc := ccOneG C hB hJ large₂ hCl hH0 u u' τ hTT hW hA hT hT' a b ξ ξ' hpin1 hscl with hcc
  have hc0 : cc ≠ 0 := ccOne_neG C hB hJ large₂ hCl hH0 u u' τ hTT hW hA hT hT' a b ξ ξ' hpin1 hscl hcO
  have hκ := (ampVec_carrierG hJ large₂ hCl hH0 hB u u' τ hTT hW hA hT hT' a b ξ ξ' 1 hpin1 hscl).choose_spec
  obtain ⟨h0, h1, hN⟩ := (muN_eq_haarLie D.R.k D.R.rS).choose_spec
  have hCut := cutAt_holds C u u' τ a b ξ ξ' cc A₀ hA₀ hCC
  obtain ⟨hGv, hMono, hRel, hH, hQ⟩ := id hP
  have hLz := (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT').hz
  have hLz' := (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT').hz'
  have hWc := muWc_eq C u τ hLz.1 hLz.2
  have hWc' := muWc_eq C u' τ hLz'.1 hLz'.2
  have hH' := haarTr_holds C u u' τ γ μRv hH
  obtain ⟨νB, hq⟩ := orbQuot_exists (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT')
    (gB_mem C u τ γ) hH'
  have hcell : Formalism.MainNotions.S.Pv.AmpDD.CellData
      (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT')
      (locW C u u' τ).μG (gB C τ γ) (muRB C τ μRv) (ν.map (Formalism.L2.SG.Pf.LocJEq.Smap C τ γ)) νB :=
    ⟨gB_mem C u τ γ, gf_B C u u' τ γ hGv, mono_B C u u' τ γ hMono,
      relStab_of_relevant C hB u u' τ hW hA hT hT' γ hRel, hH', hq, quotTr_holds C u u' τ γ μRv ν hH hQ⟩
  have hpinAt := pinAt C hB u u' τ hW hA hT hT' a b ξ ξ' cc hc0 _ hκ.1 hκ.2 _ h0 h1 hN hWc hWc' hcO hscl γ μRv ν νB
    hcell (Formalism.L2.SG.Pf.LocJEq.integrand_aesm C hB u u' τ γ ν) (hCut γ μRv ν hP)
  rw [hpinAt]
  have e : lamPl (cOf hB u τ) (sclOf hB u u' τ)
      (ampVec_carrierG hJ large₂ hCl hH0 hB u u' τ hTT hW hA hT hT' a b ξ ξ' 1 hpin1 hscl).choose D θ
      (muN_eq_haarLie D.R.k D.R.rS).choose * cc⁻¹ = 1 := by
    rw [hcc]; exact mul_inv_cancel₀ hc0
  rw [e, one_smul]

end GlobalTheory.CarrierGap
end

section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.Carrier.CarPinTor

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.FrameBoundFromBesselTorus Formalism.L2.S.Pv.AmpNZTie
open Formalism.BasicNotions Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.RealObj
open scoped Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {θ : ℝ} (C : Choice X θ) (hB : WuBessel C)

namespace GlobalTheory.CarrierGap
open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.CarrierT Formalism.L2.SG.Pf.BaseOf in
variable [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] [Fact Formalism.L2.SG.LitS.PfNVG.BesselNVG] in
theorem pinCov_ccOneG (hJ : CompanionTheory.Lime.BM.UniqGap) (large₂ : SizeData₂ D) {C' Cl Cg cb Cu cT CT C0 : ℝ}
    (hCl : 1000 ≤ Cl) (hH0 : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0)
    (u u' : D.what₂.Word) (e : NumberField.InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ)
    (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (a b : ∀ j : Fin (nfE D), X.B.H (tauE X e j)) (ξ : ∀ j : Fin (nfE D), X.Vloc u (tauE X e j))
    (ξ' : ∀ j : Fin (nfE D), X.Vloc u' (tauE X e j))
    (hTT : HypTT D u u')
    (hW : ∀ j, GoodW D (e (plE D j)) u u' θ (locW C u u' (e (plE D j))))
    (hA : ∀ j, GoodS D (lamD D (e (plE D j))) (locS hB u u' (e (plE D j))))
    (hT : 0 < Tr D u) (hT' : 0 < Tr D u')
    (hpin1 : ∀ j, CoefPin hB u u' (e (plE D j)) (a j) (b j) (ξ j) (ξ' j) 1)
    (hscl : ∀ j, sclOf hB u u' (e (plE D j)) ≠ 0) (hcO : ∀ j, cOf hB u (e (plE D j)) ≠ 0)
    (c : Formalism.FourierDecayAlt.LE.Cut) (ν' : Fin (nfE D) → Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
    (m₀ : Fin (nfE D) → Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS)
    (Θ : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TopLift D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (TP : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TypeProj (parE e u u' de de' j)
      (towersOf X C u u' e j).base.π (towersOf X C u u' e j).base.z (m₀ j *ᵥ ν' j)) (A₀ : ℝ)
    (Mo : ModelsFor (sOf (carrierInTc X C u u' e he hv CA de de' l grid grid1 a b ξ ξ'
      (fun j => ccOneG C hB hJ large₂ hCl hH0 u u' (e (plE D j)) hTT (hW j) (hA j) hT hT' (a j) (b j) (ξ j) (ξ' j)
        (hpin1 j) (hscl j)) c ν' m₀ Θ TP A₀)))
    (Ac : ℝ) (hAc : Formalism.FourierDecayAlt.P.orbital_integral_converges.choose * ((D.R.rS : ℝ) + 1) ^ 2 *
      ((D.R.rS : ℝ) * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) + 1) ≤ Ac)
    (hCC : ∀ j, Formalism.FourierDecayAlt.B.InCC Ac 1 (fcAt C u u' (e (plE D j)) (a j) (b j) (ξ j) (ξ' j)
      (ccOneG C hB hJ large₂ hCl hH0 u u' (e (plE D j)) hTT (hW j) (hA j) hT hT' (a j) (b j) (ξ j) (ξ' j) (hpin1 j) (hscl j)))) :
    JointPin.PinCov (CarrierOf (carrierInTc X C u u' e he hv CA de de' l grid grid1 a b ξ ξ'
      (fun j => ccOneG C hB hJ large₂ hCl hH0 u u' (e (plE D j)) hTT (hW j) (hA j) hT hT' (a j) (b j) (ξ j) (ξ' j)
        (hpin1 j) (hscl j)) c ν' m₀ Θ TP A₀) Mo) := by
  refine pinCov_carrierInTc X C u u' e he hv CA de de' l grid grid1 a b ξ ξ' _ c ν' m₀ Θ TP A₀ Mo ?_
  intro j γ μRv ν hH
  have hP := pinHyp_at X C u u' e he hv CA de de' l grid grid1 a b ξ ξ' _ c ν' m₀ Θ TP A₀ Mo j γ μRv ν hH
  exact pinAt_oneG C hB hJ large₂ hCl hH0 u u' (e (plE D j)) hTT (hW j) (hA j) hT hT' (a j) (b j) (ξ j) (ξ' j) (hpin1 j)
    (hscl j) (hcO j) Ac hAc (hCC j) γ μRv ν hP

end GlobalTheory.CarrierGap
end

section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.CarrierXAll

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped Matrix

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.Pf.Built Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.CarrierT Formalism.L2.SG.RealObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CarrierGap
set_option maxHeartbeats 4000000 in
variable [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] [Fact Formalism.L2.SG.LitS.PfNVG.BesselNVG] in
theorem xLeafAt_of_pinsG {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) {θ : ℝ} (C : Choice X θ) (hB : WuBessel C)
    (hJ : CompanionTheory.Lime.BM.UniqGap) (large₂ : SizeData₂ D) {C' Cl Cg cb Cu cT CT C0 : ℝ}
    (hCl : 1000 ≤ Cl) (hH0 : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0)
    (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ)
    (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (sc : ℝ) (FdN FdN' : Set X.B.I.Ginf)
    (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (jn : ℝ)
    (a b : ∀ j : Fin (nfE D), X.B.H (tauE X e j)) (ξ : ∀ j : Fin (nfE D), X.Vloc u (tauE X e j))
    (ξ' : ∀ j : Fin (nfE D), X.Vloc u' (tauE X e j))
    (hTT : HypTT D u u')
    (hW : ∀ j, GoodW D (e (plE D j)) u u' θ (locW C u u' (e (plE D j))))
    (hA : ∀ j, GoodS D (lamD D (e (plE D j))) (locS hB u u' (e (plE D j))))
    (hT : 0 < Tr D u) (hT' : 0 < Tr D u')
    (hpin1 : ∀ j, CoefPin hB u u' (e (plE D j)) (a j) (b j) (ξ j) (ξ' j) 1)
    (hscl : ∀ j, sclOf hB u u' (e (plE D j)) ≠ 0) (hcO : ∀ j, cOf hB u (e (plE D j)) ≠ 0)
    (h : Fin (nfE D) → ℝ) (hlam : ∀ j, Formalism.QuantumDeterminants.IsHCParam (lamD D (e (plE D j))))
    (hgap : ∀ j, Formalism.QuantumDeterminants.GapAtLeast (epsSH D.R) (lamD D (e (plE D j))) (h j))
    (hok : ∀ j, Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS (h j))
    (Ac : ℝ) (hAc : Formalism.FourierDecayAlt.P.orbital_integral_converges.choose * ((D.R.rS : ℝ) + 1) ^ 2 *
      ((D.R.rS : ℝ) * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) + 1) ≤ Ac)
    (hAc0 : 0 ≤ Ac) (hAch : ∀ j, Ac ≤ h j / 2)
    (cc : Fin (nfE D) → ℂ)
    (hcc : cc = fun j => ccOneG C hB hJ large₂ hCl hH0 u u' (e (plE D j)) hTT (hW j) (hA j)
      hT hT' (a j) (b j) (ξ j) (ξ' j) (hpin1 j) (hscl j)) :
    XLeafAt X C u u' e he hv CA de de' l i0 i0' sc FdN FdN' νq jn a b ξ ξ' cc := by
  subst hcc
  refine ⟨fun j => (hpin1 j).1, fun j => (hpin1 j).2.1, fun Θ TP A₀ => ?_⟩
  exact pinCov_ccOneG C hB hJ large₂ hCl hH0 u u' e he hv CA de de' l (gridT e l) (grid1T e l)
    a b ξ ξ' hTT hW hA hT hT' hpin1 hscl hcO cutStd (nuE X C u' e i0') (m0E X C u u' e) Θ TP A₀ (modelsOf _) Ac hAc
    (fun j => Formalism.L2.SG.Pf.CoefCCT.fcT_inCC C e u u' a b ξ ξ'
      (fun j => ccOneG C hB hJ large₂ hCl hH0 u u' (e (plE D j)) hTT (hW j) (hA j)
        hT hT' (a j) (b j) (ξ j) (ξ' j) (hpin1 j) (hscl j)) h hlam hgap hok hAc0 hAch (fun j => (hpin1 j).1) (fun j => (hpin1 j).2.1) j 1)

end GlobalTheory.CarrierGap
end

section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.CarrierXAll

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped Matrix InnerProductSpace

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.Pf.Built Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.CarrierT Formalism.L2.SG.RealObj
open Formalism.FourierDecayAlt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups
open Formalism.L2.SG.AdBridge Formalism.L2.SG.DataInst Formalism.L2.SG.SpectralTiesReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

namespace GlobalTheory.CarrierGap
variable [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] [Fact Formalism.L2.SG.LitS.PfNVG.BesselNVG] in
theorem xLeavesP_of_pinsPG (hJ : CompanionTheory.Lime.BM.UniqGap) (hP : XPinsP) : XLeavesP := by
  intro CA C0 CG CDel cT Cb' Cg cb Cw cTf CT C0f C' Cl D L T u u' e τ Cp Th' i0 i0' νq X0 sd C Th F0 what₂ vR Q hne hcb hcT hTies hC' hClp
    hk18 hH0 hPl hSz hi hPt hNu
  obtain ⟨θ, Ch, hB, a, b, ξ, ξ', hTT, hT, hT', hW, hA, hpin1, hscl, hcO⟩ :=
    hP CA C0 CG CDel cT Cb' Cg cb Cw cTf CT C0f C' Cl D L T u u' e τ Cp Th' i0 i0' νq hne hcb hcT hTies hC' hClp hk18 hH0 hPl hSz
      hi hPt hNu
  have hCl : (1000 : ℝ) ≤ Cl := by have := abs_nonneg (Formalism.FourierDecayAlt.P.orbital_integral_converges.choose); linarith
  have hS0 := hH0.1
  have hrS : 2 * D.R.rS + 2 = D.R.m := Ranks.rS_two D.R
  have hr : D.R.r = 2 * D.R.rS + D.R.k + 1 := by unfold Ranks.r; omega
  have hkL := Formalism.MainNotions.BridgeLemma.szh_k_le hS0 (by linarith) τ
  have hk5 : (5 : ℝ) ≤ (D.R.k : ℝ) := by exact_mod_cast Formalism.MainNotions.BridgeLemma.five_le_k D
  have hL : (1 / 2 : ℝ) ≤ L.sc.L := by
    by_contra hcn
    push Not at hcn
    have h1 : Real.exp (2 * L.sc.L) < Real.exp 1 := Real.exp_lt_exp.mpr (by linarith)
    have h2 : Real.exp 1 < 3 := by have := Real.exp_one_lt_d9; linarith
    linarith
  have hf : 2 ≤ D.R.f := le_trans D.R.two_le_m D.R.m_le_f
  have hfR : (2 : ℝ) ≤ (D.R.f : ℝ) := by exact_mod_cast hf
  have hf5 : (32 : ℝ) ≤ (D.R.f : ℝ) ^ 5 := by
    have : (2 : ℝ) ^ 5 ≤ (D.R.f : ℝ) ^ 5 := pow_le_pow_left₀ (by norm_num) hfR 5
    norm_num at this; linarith
  have hrr : ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) = (D.R.r : ℝ) := by rw [hr]
  have hn1 : (1 : ℝ) ≤ (D.R.r : ℝ) := by rw [hr]; push_cast; have : (0 : ℝ) ≤ (D.R.rS : ℝ) := Nat.cast_nonneg _; linarith
  have hn19 : 0 ≤ (D.R.r : ℝ) ^ 19 := by positivity
  have hh16 : 16 * Cl * (D.R.r : ℝ) ^ 19 ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L.sc.L := by
    have e1 : Cl * (D.R.r : ℝ) ^ 19 * 32 ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 :=
      mul_le_mul_of_nonneg_left hf5 (by positivity)
    have e2 : Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * (1 / 2) ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L.sc.L :=
      mul_le_mul_of_nonneg_left hL (by positivity)
    linarith
  have hn1801 : 1801 ≤ 2 * D.R.rS + D.R.k + 1 := by omega
  have hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS (Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L.sc.L) := by
    refine gapOK_mono (Formalism.L2.SG.Pf.WuDec.gapOK_of_big D.R.k D.R.rS (by omega) hn1801) ?_
    rw [hrr]
    have h1 : 1 * (D.R.r : ℝ) ^ 19 ≤ Cl * (D.R.r : ℝ) ^ 19 := mul_le_mul_of_nonneg_right (by linarith) hn19
    linarith
  have hAch := le_of_le_of_eq (ac_le (Formalism.FourierDecayAlt.P.orbital_integral_converges.choose) Cl L.sc.L D.R.rS D.R.k D.R.f hClp hf hL) (by rw [hrr])
  refine ⟨θ, Ch, a, b, ξ, ξ', fun j => ccOneG Ch hB hJ L hCl hH0 u u' (e (plE D j)) hTT (hW j)
    (hA j) hT hT' (a j) (b j) (ξ j) (ξ' j) (hpin1 j) (hscl j), ?_⟩
  exact xLeafAt_of_pinsG T.X Ch hB hJ L hCl hH0 u u' e hPl (host_v D) CA (deOf D τ u) (deOf D τ u')
    (lOf D (deOf D τ u) (deOf D τ u')) i0 i0' 1 (T.Y.FN u) (T.Y.FN u') νq _ a b ξ ξ' hTT hW hA hT hT' hpin1 hscl hcO
    (fun _ => Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L.sc.L) (fun j => Formalism.MainNotions.S.Inh.amp_isHCParam_lamD D _)
    (fun j => Formalism.MainNotions.BridgeLemma.szh_gap hS0 _) (fun _ => hok) _ (le_max_left _ _) (le_max_right _ _) (fun _ => hAch) _ rfl

variable [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] in
theorem xPinsP_ofG (hJ : CompanionTheory.Lime.BM.UniqGap) (hNZ : KFinNZ) : XPinsP := by
  intro CA C0 CG CDel cT Cb' Cg cb Cw cTf CT C0f C' Cl D L T u u' e τ Cp Th' i0 i0' νq hne hcb hcT hTies hC' hClp hk18
    hH0 hPl hSz hi hPt hNu
  haveI : Nonempty D.what₂.Word := ⟨u⟩
  have hCl : (1000 : ℝ) ≤ Cl := by have := abs_nonneg (Formalism.FourierDecayAlt.P.orbital_integral_converges.choose); linarith
  have hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D :=
    Formalism.L2.SG.ThmSOwn.gap_hypothesis_of_hypotheses hH0.1 (by linarith) hC'
  obtain ⟨Ch⟩ := Formalism.L2.SG.Pf.choiceExists T.X 1 one_pos
  have hB : WuBessel Ch := Formalism.L2.SG.Pf.wuBesselOfLoc_all Ch hG Formalism.MainNotions.BridgeCS3dBOW.besselOfW_holds (Formalism.L2.SG.Pf.LocF.locFactor_holds hG Ch) (fun τ => Formalism.L2.SG.Pf.dsTr Ch τ) (fun τ => Formalism.L2.SG.Pf.haarTr Ch τ) (fun u τ => Formalism.L2.SG.Pf.colsTypeTr Ch u τ)
  have hLF := Formalism.L2.SG.Pf.LocF.locFactor_holds hG Ch
  have hc : ∀ (w : D.what₂.Word) (t : D.what₂.Tau), 0 < cOf hB w t := fun w t =>
    Formalism.L2.SG.Pf.AmpWin.cOf_pos hB (Formalism.L2.SG.Pf.GoodS.l2SG_phiOf_ne_zero_and_lt_infty Ch hLF hB w t).1 (Formalism.L2.SG.Pf.GoodS.l2SG_phiOf_ne_zero_and_lt_infty Ch hLF hB w t).2
  have hscl : ∀ t, sclOf hB u u' t ≠ 0 := by
    intro t
    have h1 := Formalism.L2.SG.Pf.GoodS.l2SG_phiOf_ne_zero_and_lt_infty Ch hLF hB u' t
    have hl : 0 < (l2SG (Ch.nuS u' t) (phiOf hB u' t)).toReal := ENNReal.toReal_pos h1.1 h1.2.ne
    have hd : 0 < Module.finrank ℂ (T.X.Vloc u' (vOf T.X t)) := by
      rcases Nat.eq_zero_or_pos (Module.finrank ℂ (T.X.Vloc u' (vOf T.X t))) with h | h
      · exfalso
        have : Subsingleton (T.X.Vloc u' (vOf T.X t)) := Module.finrank_zero_iff.1 h
        apply h1.1
        unfold l2SG
        simp [Subsingleton.elim (phiOf hB u' t _) 0]
      · exact h
    unfold sclOf
    have hpos : 0 < cOf hB u t * (Module.finrank ℂ (T.X.Vloc u' (vOf T.X t)) : ℝ) /
        (l2SG (Ch.nuS u' t) (phiOf hB u' t)).toReal := div_pos (mul_pos (hc u t) (by exact_mod_cast hd)) hl
    exact_mod_cast (Real.sqrt_pos.mpr hpos).ne'
  have ha : ∀ j : Fin (nfE D), ∃ a : T.X.B.H (vOf T.X (e (plE D j))),
      PI.UpqRep.IsKFinHpk (k := D.R.k) (r := D.R.rS) (sigB T.X (Ch.Q (e (plE D j))) (Ch.Qi (e (plE D j))) (e (plE D j))) a ∧
      bOf hB u (e (plE D j)) a ≠ 0 := fun j => hNZ D T.X 1 Ch hB u (e (plE D j)) hG
  have hb : ∀ j : Fin (nfE D), ∃ b : T.X.B.H (vOf T.X (e (plE D j))),
      PI.UpqRep.IsKFinHpk (k := D.R.k) (r := D.R.rS) (sigB T.X (Ch.Q (e (plE D j))) (Ch.Qi (e (plE D j))) (e (plE D j))) b ∧
      bOf hB u' (e (plE D j)) b ≠ 0 := fun j => hNZ D T.X 1 Ch hB u' (e (plE D j)) hG
  choose a ha using ha
  choose b hb using hb
  refine ⟨1, Ch, hB, a, b, fun j => (((‖bOf hB u (e (plE D j)) (a j)‖ ^ 2 : ℝ) : ℂ))⁻¹ • bOf hB u (e (plE D j)) (a j),
    fun j => (((‖bOf hB u' (e (plE D j)) (b j)‖ ^ 2 : ℝ) : ℂ))⁻¹ • bOf hB u' (e (plE D j)) (b j),
    Formalism.MainNotions.SchurRelationsDiscreteSeries.hypTT_all u u', Nat.cast_pos.2 (D.mem u).A.T_prime.pos, Nat.cast_pos.2 (D.mem u').A.T_prime.pos,
    fun j => Formalism.L2.SG.Pf.AmpWinRX.goodW_all Ch u u' (e (plE D j)),
    fun j => goodS_of hB u u' (e (plE D j)) (Formalism.L2.SG.Pf.goodSRest_all hG hTies.dsig_tie hB u u' (e (plE D j))),
    fun j => ⟨(ha j).1, (hb j).1, ?_, one_ne_zero⟩, fun j => hscl _, fun j => (hc u _).ne'⟩
  rw [inner_normalize_right (ha j).2, inner_normalize_left (hb j).2, one_mul]

end GlobalTheory.CarrierGap
end

section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.CarrierXAll

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped Matrix InnerProductSpace

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.Pf.Built Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.CarrierT Formalism.L2.SG.RealObj
open Formalism.FourierDecayAlt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups
open Formalism.L2.SG.AdBridge Formalism.L2.SG.DataInst Formalism.L2.SG.SpectralTiesReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

namespace GlobalTheory.CarrierGap
variable [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] [Fact Formalism.L2.SG.LitS.PfNVG.BesselNVG] [Fact Formalism.L2.SG.Pf.CarrierT.CoefCapAll] [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] in
theorem vIndepAtAllP_ofG (hJ : CompanionTheory.Lime.BM.UniqGap) (hNZ : KFinNZ) : Formalism.L2.SG.PoincareAmplitudeLowerBounds.VIndepAtAllP := by
  intro Cg cb Cw cTf CT C0f hcb hcT
  refine ⟨29, 1000 + |Formalism.FourierDecayAlt.P.orbital_integral_converges.choose|, ?_⟩
  intro C' Cl hC' hClp D L T u u' i0 i0' νq hTies hne hSt hCT hi hNu hPt hH0
  haveI : Nonempty D.what₂.Word := ⟨u⟩
  have hCl : (1000 : ℝ) ≤ Cl := by have := abs_nonneg (Formalism.FourierDecayAlt.P.orbital_integral_converges.choose); linarith
  have hS0 := hH0.1
  have hk18 := rootLatticeThresholds_k_of_fact hS0 hC'
  have hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D := Formalism.L2.SG.ThmSOwn.gap_hypothesis_of_hypotheses hS0 (by linarith) hC'
  obtain ⟨Ch⟩ := Formalism.L2.SG.Pf.choiceExists T.X 1 one_pos
  have hB : WuBessel Ch := Formalism.L2.SG.Pf.wuBesselOfLoc_all Ch hG Formalism.MainNotions.BridgeCS3dBOW.besselOfW_holds (Formalism.L2.SG.Pf.LocF.locFactor_holds hG Ch) (fun τ => Formalism.L2.SG.Pf.dsTr Ch τ) (fun τ => Formalism.L2.SG.Pf.haarTr Ch τ) (fun u τ => Formalism.L2.SG.Pf.colsTypeTr Ch u τ)
  have hLF := Formalism.L2.SG.Pf.LocF.locFactor_holds hG Ch
  set e : InfinitePlace D.host.E ≃ D.what₂.Tau := (Formalism.L2.Geo.Rec.StarEmbeddingNorm.ePl D).symm with he_def
  have he : PlaceTie T.X e := fun x => Formalism.L2.SG.Pf.Carrier.placeTie_ePl T.X x
  have hc : ∀ (w : D.what₂.Word) (t : D.what₂.Tau), 0 < cOf hB w t := fun w t =>
    Formalism.L2.SG.Pf.AmpWin.cOf_pos hB (Formalism.L2.SG.Pf.GoodS.l2SG_phiOf_ne_zero_and_lt_infty Ch hLF hB w t).1 (Formalism.L2.SG.Pf.GoodS.l2SG_phiOf_ne_zero_and_lt_infty Ch hLF hB w t).2
  have hscl : ∀ t, sclOf hB u u' t ≠ 0 := by
    intro t
    have h1 := Formalism.L2.SG.Pf.GoodS.l2SG_phiOf_ne_zero_and_lt_infty Ch hLF hB u' t
    have hl : 0 < (l2SG (Ch.nuS u' t) (phiOf hB u' t)).toReal := ENNReal.toReal_pos h1.1 h1.2.ne
    have hd : 0 < Module.finrank ℂ (T.X.Vloc u' (vOf T.X t)) := by
      rcases Nat.eq_zero_or_pos (Module.finrank ℂ (T.X.Vloc u' (vOf T.X t))) with h | h
      · exfalso
        have : Subsingleton (T.X.Vloc u' (vOf T.X t)) := Module.finrank_zero_iff.1 h
        apply h1.1
        unfold l2SG
        simp [Subsingleton.elim (phiOf hB u' t _) 0]
      · exact h
    unfold sclOf
    have hpos : 0 < cOf hB u t * (Module.finrank ℂ (T.X.Vloc u' (vOf T.X t)) : ℝ) /
        (l2SG (Ch.nuS u' t) (phiOf hB u' t)).toReal := div_pos (mul_pos (hc u t) (by exact_mod_cast hd)) hl
    exact_mod_cast (Real.sqrt_pos.mpr hpos).ne'
  have ha : ∀ j : Fin (nfE D), ∃ a : T.X.B.H (vOf T.X (e (plE D j))),
      PI.UpqRep.IsKFinHpk (k := D.R.k) (r := D.R.rS) (sigB T.X (Ch.Q (e (plE D j))) (Ch.Qi (e (plE D j))) (e (plE D j))) a ∧
      bOf hB u (e (plE D j)) a ≠ 0 := fun j => hNZ D T.X 1 Ch hB u (e (plE D j)) hG
  have hb : ∀ j : Fin (nfE D), ∃ b : T.X.B.H (vOf T.X (e (plE D j))),
      PI.UpqRep.IsKFinHpk (k := D.R.k) (r := D.R.rS) (sigB T.X (Ch.Q (e (plE D j))) (Ch.Qi (e (plE D j))) (e (plE D j))) b ∧
      bOf hB u' (e (plE D j)) b ≠ 0 := fun j => hNZ D T.X 1 Ch hB u' (e (plE D j)) hG
  choose a ha using ha
  choose b hb using hb
  set ξ : ∀ j : Fin (nfE D), T.X.Vloc u (tauE T.X e j) :=
    fun j => (((‖bOf hB u (e (plE D j)) (a j)‖ ^ 2 : ℝ) : ℂ))⁻¹ • bOf hB u (e (plE D j)) (a j) with hξ
  set ξ' : ∀ j : Fin (nfE D), T.X.Vloc u' (tauE T.X e j) :=
    fun j => (((‖bOf hB u' (e (plE D j)) (b j)‖ ^ 2 : ℝ) : ℂ))⁻¹ • bOf hB u' (e (plE D j)) (b j) with hξ'
  have hpin1 : ∀ j, CoefPin hB u u' (e (plE D j)) (a j) (b j) (ξ j) (ξ' j) 1 := fun j =>
    ⟨(ha j).1, (hb j).1, by rw [hξ, hξ']; simp only []; rw [inner_normalize_right (ha j).2, inner_normalize_left (hb j).2, one_mul],
      one_ne_zero⟩
  have hTT := Formalism.MainNotions.SchurRelationsDiscreteSeries.hypTT_all (D := D) u u'
  have hT : 0 < Tr D u := Nat.cast_pos.2 (D.mem u).A.T_prime.pos
  have hT' : 0 < Tr D u' := Nat.cast_pos.2 (D.mem u').A.T_prime.pos
  have hW := fun j => Formalism.L2.SG.Pf.AmpWinRX.goodW_all Ch u u' (e (plE D j))
  have hA := fun j => goodS_of hB u u' (e (plE D j)) (Formalism.L2.SG.Pf.goodSRest_all hG hTies.dsig_tie hB u u' (e (plE D j)))
  have hcO : ∀ j, cOf hB u (e (plE D j)) ≠ 0 := fun j => (hc u _).ne'
  have hf : 2 ≤ D.R.f := le_trans D.R.two_le_m D.R.m_le_f
  have hfpos : 0 < D.R.f := lt_of_lt_of_le (by decide) hf
  haveI : Nonempty D.what₂.Tau := Fintype.card_pos_iff.1 (by rw [Formalism.MainNotions.BridgeLemma.szf_card_Tau]; exact hfpos)
  obtain ⟨τ⟩ := (inferInstance : Nonempty D.what₂.Tau)
  have hrS : 2 * D.R.rS + 2 = D.R.m := Ranks.rS_two D.R
  have hr : D.R.r = 2 * D.R.rS + D.R.k + 1 := by unfold Ranks.r; omega
  have hkL := Formalism.MainNotions.BridgeLemma.szh_k_le hS0 (by linarith) τ
  have hk5 : (5 : ℝ) ≤ (D.R.k : ℝ) := by exact_mod_cast Formalism.MainNotions.BridgeLemma.five_le_k D
  have hL : (1 / 2 : ℝ) ≤ L.sc.L := by
    by_contra hcn
    push Not at hcn
    have h1 : Real.exp (2 * L.sc.L) < Real.exp 1 := Real.exp_lt_exp.mpr (by linarith)
    have h2 : Real.exp 1 < 3 := by have := Real.exp_one_lt_d9; linarith
    linarith
  have hfR : (2 : ℝ) ≤ (D.R.f : ℝ) := by exact_mod_cast hf
  have hf5 : (32 : ℝ) ≤ (D.R.f : ℝ) ^ 5 := by
    have : (2 : ℝ) ^ 5 ≤ (D.R.f : ℝ) ^ 5 := pow_le_pow_left₀ (by norm_num) hfR 5
    norm_num at this; linarith
  have hrr : ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) = (D.R.r : ℝ) := by rw [hr]
  have hn1 : (1 : ℝ) ≤ (D.R.r : ℝ) := by rw [hr]; push_cast; have : (0 : ℝ) ≤ (D.R.rS : ℝ) := Nat.cast_nonneg _; linarith
  have hn19 : 0 ≤ (D.R.r : ℝ) ^ 19 := by positivity
  have hh16 : 16 * Cl * (D.R.r : ℝ) ^ 19 ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L.sc.L := by
    have e1 : Cl * (D.R.r : ℝ) ^ 19 * 32 ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 :=
      mul_le_mul_of_nonneg_left hf5 (by positivity)
    have e2 : Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * (1 / 2) ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L.sc.L :=
      mul_le_mul_of_nonneg_left hL (by positivity)
    linarith
  have hn1801 : 1801 ≤ 2 * D.R.rS + D.R.k + 1 := by omega
  have hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS (Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L.sc.L) := by
    refine gapOK_mono (Formalism.L2.SG.Pf.WuDec.gapOK_of_big D.R.k D.R.rS (by omega) hn1801) ?_
    rw [hrr]
    have h1 : 1 * (D.R.r : ℝ) ^ 19 ≤ Cl * (D.R.r : ℝ) ^ 19 := mul_le_mul_of_nonneg_right (by linarith) hn19
    linarith
  have hAch := le_of_le_of_eq (ac_le (Formalism.FourierDecayAlt.P.orbital_integral_converges.choose) Cl L.sc.L D.R.rS D.R.k D.R.f hClp hf hL) (by rw [hrr])
  have h5 := Formalism.MainNotions.BridgeLemma.last_shifted_parameter_eq hH0.2.1
  have hDel : (D.s.Del : ℝ) ≠ 0 := by
    have := (Formalism.MainNotions.BridgeLemma.cfg_ok hH0.2.1 hS0 τ).hDel
    exact ne_of_gt (lt_of_lt_of_le one_pos this)
  set de := deOf D τ u with hde_def
  set de' := deOf D τ u' with hde'_def
  have hde := Formalism.L2.SG.Pf.SzHypOf.deOf_eq D h5 hDel τ u
  have hde' := Formalism.L2.SG.Pf.SzHypOf.deOf_eq D h5 hDel τ u'
  have hN := parNumsE_of (D := D) u u' e de de' h5 hde hde'
  have hty := typesE_of T.X Ch capacity_from_hermitian_char u u' e de de' h5 hde hde'
  set TP := tpOf T.X Ch Formalism.FourierDecayAlt.P.type_projectors_exist u u' e de de' i0' hN hty with hTPdef
  set Θ0 : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TopLift D.R.k D.R.rS (T.X.Vloc u (tauE T.X e j)) (T.X.Vloc u' (tauE T.X e j)) :=
    fun _ => liftId with hΘ0
  set cc : Fin (nfE D) → ℂ := fun j => ccOneG Ch hB hJ L hCl hH0 u u' (e (plE D j)) hTT
    (hW j) (hA j) hT hT' (a j) (b j) (ξ j) (ξ' j) (hpin1 j) (hscl (e (plE D j))) with hcc_def
  have hleaf := xLeafAt_of_pinsG T.X Ch hB hJ L hCl hH0 u u' e he (host_v D) 0 de de' 0 i0 i0' 1 ∅ ∅ νq 0 a b ξ ξ' hTT hW hA
    hT hT' hpin1 (fun j => hscl (e (plE D j))) hcO (fun _ => Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L.sc.L)
    (fun j => Formalism.MainNotions.S.Inh.amp_isHCParam_lamD D _) (fun j => Formalism.MainNotions.BridgeLemma.szh_gap hS0 _) (fun _ => hok) _
    (le_max_left _ _) (le_max_right _ _) (fun _ => hAch) cc rfl
  have hpin := hleaf.2.2 Θ0 TP 0
  have hh0 : (0 : ℝ) ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L.sc.L / 2 := by
    have : (0 : ℝ) ≤ L.sc.L := by linarith
    positivity
  have hcc : CoefCC (ITc T.X Ch u u' e he (host_v D) 0 de de' 0 (gridT e 0) (grid1T e 0) (fcT T.X Ch e u u' a b ξ ξ' cc) cutStd i0' Θ0 TP 0) :=
    Formalism.L2.SG.Pf.CoefCCT.coefCC_carrierInTc Ch u u' e he (host_v D) 0 de de' 0 (gridT e 0) (grid1T e 0) a b ξ ξ' cc cutStd
      (nuE T.X Ch u' e i0') (m0E T.X Ch u u' e) Θ0 TP 0 (fun _ => Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L.sc.L)
      (fun _ => Formalism.MainNotions.S.Inh.amp_isHCParam_lamD D _) (fun j => Formalism.MainNotions.BridgeLemma.szh_gap hS0 _) (fun _ => hok) le_rfl
      (fun _ => hh0) (fun j => (ha j).1) (fun j => (hb j).1)
  have hcap := coefCap_ITc T.X Ch hS0 hCl hk18 u u' e he (host_v D) 0 de de' 0 (gridT e 0) (grid1T e 0) a b ξ ξ' cc cutStd
    i0' Θ0 TP 0 (fun j => (hb j).1)
  have hBuilt := isBuilt_carrierInT T.X Ch u u' e he (host_v D) 0 de de' 0 (gridT e 0) (grid1T e 0)
    (fcT T.X Ch e u u' a b ξ ξ' cc) cutStd (nuE T.X Ch u' e i0') (m0E T.X Ch u u' e) Θ0 TP 0 hN hty
    (frames_carrierInT T.X Ch u u' e he (host_v D) 0 de de' 0 (gridT e 0) (grid1T e 0) (fcT T.X Ch e u u' a b ξ ξ' cc) cutStd
      i0' Θ0 TP 0) hcc hcap
  have hJT := jointTensor_compact_test T.X Ch u u' e he (host_v D) 0 de de' 0 (gridT e 0) (grid1T e 0)
    (fcT T.X Ch e u u' a b ξ ξ' cc) cutStd i0 i0' hi Θ0 TP 0 1 νq hNu hpin one_pos hBuilt
  exact vIndepAt_of_tensorAt T.X u u' _ _ _ _ _ _ _ _ 1 i0 i0' νq hJT

end GlobalTheory.CarrierGap
end

section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.TheoremSConclusion

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.FourierDecayAlt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2
open Formalism.L2.SG.SpectralTiesReal Formalism.L2.SG.PoincareAmplitudeLowerBounds

namespace GlobalTheory.CarrierGap
variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] [Fact Formalism.L2.SG.SplitPrimeNormLemmas.BesselNVGap] [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] [Fact Formalism.L2.SG.Pf.CarrierXAll.KFinDense] [Fact PI.AprimeInfW.GaugeVolUD] [Fact Formalism.L2.SG.Pf.WB.RhsWLim] [Fact Formalism.L2.SG.LitS.PfNVG.BesselNVG] [Fact Formalism.L2.SG.Pf.CarrierT.CoefCapAll] in
theorem theoremS_leaves_of_carrierG
    (hCar : CarrierP)
    (hNG : Formalism.L2.SG.RowsPos.RowNGP)
    (hRFD : Formalism.L2.SG.RowsDef.RowsFinDim) (wMU : CompanionTheory.Lime.BM.UniqGap)
    (bSW : _root_.PI.VolStabS.MassDataS.SWXS) :
    TheoremSClosedHypotheses := by
  have hFC : FormulaC := Formalism.L2.SG.Pf.Cnt.formulaCT_holds
  have kD := Formalism.L2.SG.Pf.CarrierXAll.kFinDense_holds
  have rVA : VIndepAtAllP :=
    vIndepAtAllP_ofG wMU (Formalism.L2.SG.Pf.CarrierXAll.kFinNZ_of kD)
  have rVP : Formalism.L2.SG.VolPin.VolumeOddGeneric := Formalism.L2.SG.Closed.volume_determined
  have hWu : Formalism.L2.SG.Pf.WuDecayOfGap := Formalism.L2.SG.Pf.wuDecayOfGap_of_uniqGap wMU
  have hDI := Formalism.L2.SG.Pf.Cnt.densInputT_holds
  have hLM : ∀ D : D7, Formalism.L2.SG.DataInst.LocalModelAt D := Formalism.L2.SG.Pf.localModelAt_holds
  exact ⟨hLM, hDI, fun D => rowsInputP_of_dataCut (Formalism.L2.SG.DataCut.rowsInputP_of_normProd (Formalism.L2.SG.Closed.NormProd_holds D)
    (Formalism.L2.SG.Pf.Coef.rowsDatumP_of_deep (Formalism.L2.SG.Closed.CutLeavesDeep_outright D))),
    hNG,
    Formalism.L2.SG.Closed.KppOffC_holds, hCar, kExpTiedS_holds,
    Formalism.L2.SG.Closed.FoldOKC_outright, Formalism.L2.SG.Closed.OOIntAllC_outright, Formalism.L2.SG.Closed.AbsConvC_outright,
    Formalism.L2.SG.Pf.finXC_of hWu hRFD, hWu, choicesC_holds,
    hFC, rowsSum_of_formula_volume hFC rVP, rowFormAllP_of hFC rVP rVA (Formalism.L2.SG.Pf.NcAllC.normalizing_constants_all Formalism.L2.SG.Closed.CovolRef_outright bSW), massDataInputsAll_of
      (massDataPosAll_of Formalism.L2.SG.Pf.ProdConvCut2.prodConvAll_holds bSW (fun X v => Formalism.L2.SG.Pf.MassDataX.dvPosC_holds X v) Formalism.L2.SG.Pf.MassDataX.densNonnegAll_holds)
      (Formalism.L2.SG.Pf.MassDataX.massDataVolAll_of bSW) Formalism.L2.SG.Pf.ProdConvCut2.prodConvAll_holds Formalism.L2.SG.Pf.MassDataX.typedAll_holds
      (fun _ hg X u u' => Formalism.L2.SG.RealObj.EnergyConvJ.BM.realObj_inInfinityX_jsz wMU hg X u u' 1 one_pos) _root_.locFramePrim, linkAll_holds, splitAll_holds⟩

end GlobalTheory.CarrierGap
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.ThmSOwn
namespace GlobalTheory.CarrierGap

theorem carrierP : Formalism.L2.SG.PoincareAmplitudeLowerBounds.CarrierP := by
  obtain ⟨hPA, hMP, hBB⟩ := GlobalTheory.carrierNeedsFromD
  obtain ⟨Cb, hL⟩ := Formalism.L2.SG.Pf.CarrierXAll.liftAt3_exists
  exact Formalism.L2.SG.SpectralTiesReal.carrierP_of_compact_model hPA Formalism.FourierDecayAlt.P.lemma_model hMP hBB Cb
    (Formalism.L2.SG.Pf.CarrierXAll.carrierXSideP_of_leaves Cb hL (xLeavesP_of_pinsPG CompanionTheory.Lime.BM.uniqGap_holds
      (xPinsP_ofG CompanionTheory.Lime.BM.uniqGap_holds
        (Formalism.L2.SG.Pf.CarrierXAll.kFinNZ_of Formalism.L2.SG.Pf.CarrierXAll.kFinDense_holds))))

theorem offDiag : PI.VolStabS.MassDataS.SWXS → Formalism.L2.SG.RowsPos.RowNGP → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (𝒞 : FamClass) (sel : SSel 𝒞), (∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm) x (hx : Fm.x1 < x) (h0 : (sel Fm hc).1 ≤ x) (i : Fm.Ix x), Formalism.L2.SG.Pf.LocCP.LocTied (Fm.D x i)) → Formalism.L2.SG.Pf.SzHypFam.RanksRow 3 𝒞 → LoopRowS 3 𝒞 sel → Closed 𝒞 fun Fm _ => ∀ hc : 𝒞 Fm, TheoremSSelected Fm 3 (sel Fm hc) := by
  intro hSW hNG hRF 𝒞 sel hLoc hRk hLp
  have hWu : Formalism.L2.SG.Pf.WuDecayOfGap := CompanionTheory.Lime.BM.wuDecayOfGap_holds'
  have hTF := Formalism.L2.SG.Pf.SzHypFam.hTF_of_ranks 3 hRk
  have hOK := selOK_of 3 (Formalism.L2.SG.Pf.finXC_of hWu hRF) hWu sel hLoc hTF
  have hS : TheoremSDistinctWords := theoremS_distinct_of_closed (Formalism.L2.SG.TheoremSConclusion.theoremS_of_conj
    (theoremS_leaves_of_carrierG carrierP hNG hRF CompanionTheory.Lime.BM.uniqGap_holds hSW))
  exact offDiagonalK0_of_rows 3 hS (by norm_num) sel hOK
    (Formalism.L2.SG.Pf.SzHypOf.sizesRowS_of 3 sel (Formalism.L2.SG.Pf.SzHypFam.hRw_of_ranks 3 hRk)
      (Formalism.L2.SG.Pf.ThresholdLevels.thrRow_holds 3))
    (Formalism.L2.SG.Pf.SzHypFam.aSz 3) (Formalism.L2.SG.Pf.SzHypFam.hA_of_ranks 3 (by norm_num) hRk) hLp absConvTied_holds

end GlobalTheory.CarrierGap
end
