module

public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TxFrameTranslate

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorsionPointPrimitiveComponentValuationZer
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorsionPointPrimitiveComponentValuationZer
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

noncomputable section
namespace GlobalTheory.OneBasis.UnitTerm
open TWM TWO

theorem exists_torsion_isUnit (hL : Laws) {S : Scheme.{0}} (P : PolAV S) {K : Type} [Field K] [IsAlgClosed K]
    (t : Spec (CommRingCat.of K) ⟶ S) {I : Type} [Fintype I] {φ : I → ((Over.mk t ⊗ P.A).left ⟶ P.A.left)}
    {ε : I → ℤ} (σ : LB.Sec (LB.LinComb P.L φ ε)) (hσ : ¬ ∀ j, σ.f j = 0) {l : ℕ} (hl : 2 ≤ l) (hK : (l : K) ≠ 0) :
    ∃ (x : Over.mk t ⟶ P.A) (j : ℕ), x ^ l ^ j = 1 ∧
      ∀ z J, Good P.L z J → IsUnit (sval σ (lift (𝟙 (Over.mk t)) x).left z J) := by
  obtain ⟨j, hj⟩ := not_forall.1 hσ
  have hsm := P.isAb.smooth
  let p : (Over.mk t ⊗ P.A).left ⟶ Spec (CommRingCat.of K) := (fst (Over.mk t) P.A).left
  have hp : Smooth p := inferInstanceAs (Smooth (pullback.fst t P.A.hom))
  have : IsReduced (Over.mk t ⊗ P.A).left := GlobalTheory.isReduced_of_smooth_of_isReduced p
  obtain ⟨P', g, hg, -, hmul, -⟩ := hL.polBaseChange _ _ t P
  let e : P'.A.left ≅ (Over.mk t ⊗ P.A).left := hg.flip.isoPullback
  let W := (Over.mk t ⊗ P.A).left.basicOpen (σ.f j)
  have hW : (W : Set (Over.mk t ⊗ P.A).left).Nonempty := Set.nonempty_iff_ne_empty.2 fun h =>
    hj ((basicOpen_eq_bot_iff _).1 (SetLike.coe_injective h))
  obtain ⟨y, hy⟩ := hW
  obtain ⟨_, hq, hq'⟩ := (PrimePowerTorsion.dense_torsion hL.ample hL.kerPow hL.irred K P' l hl
    hK).inter_open_nonempty (e.hom ⁻¹ᵁ W) (e.hom ⁻¹ᵁ W).isOpen ⟨e.inv y, by
      show e.hom (e.inv y) ∈ W
      rw [← Scheme.Hom.comp_apply, e.inv_hom_id]; exact hy⟩
  obtain ⟨x, ⟨m, hx⟩, q, rfl⟩ := Set.mem_iUnion₂.1 hq'
  let Φ : (𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ P'.A) →* (Over.mk (𝟙 _ ≫ t) ⟶ P.A) :=
    MonoidHom.mk' (fun x => toBase hg.w x) (hmul _)
  let ρ : Over.mk t ⟶ Over.mk (𝟙 _ ≫ t) := Over.homMk (𝟙 _) ((Category.id_comp _).trans (Category.id_comp _))
  have er : (lift (𝟙 (Over.mk t)) (ρ ≫ Φ x)).left = x.left ≫ e.hom := by
    refine pullback.hom_ext ?_ ?_
    · refine (congrArg (fun q => q.left) (lift_fst (𝟙 (Over.mk t)) (ρ ≫ Φ x))).trans ?_
      exact ((Category.assoc _ _ _).trans ((congrArg (x.left ≫ ·) hg.flip.isoPullback_hom_fst).trans (Over.w x))).symm
    · refine (congrArg (fun q => q.left) (lift_snd (𝟙 (Over.mk t)) (ρ ≫ Φ x))).trans ?_
      exact (Category.id_comp _).trans
        ((Category.assoc _ _ _).trans (congrArg (x.left ≫ ·) hg.flip.isoPullback_hom_snd)).symm
  refine ⟨ρ ≫ Φ x, m, by rw [← MonObj.comp_pow, ← map_pow, hx, map_one, MonObj.comp_one], fun z J hJ => ?_⟩
  obtain rfl : z = q := H1.SquareUnits.spec_pt_eq z q
  have hz : (lift (𝟙 (Over.mk t)) (ρ ≫ Φ x)).left z ∈ W := by rw [er]; exact hq
  exact H1.SectionArithmetic.isUnit_sval σ _ z hJ j hz

theorem exists_sec_lin {Y : Scheme.{0}} {M : LB Y} {n : ℕ} (b : Fin n → Γ(Y, ⊤)) (t : Fin n → LB.Sec M) :
    ∃ s : LB.Sec M, ∀ j, s.f j = ∑ i, resTop _ (b i) * (t i).f j :=
  ⟨⟨fun j => ∑ i, (SecOps.secScale (b i) (t i)).f j, fun i j => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, (SecOps.secScale _ _).compat, Finset.mul_sum]⟩, fun _ => rfl⟩

theorem exists_torsion_sum (hL : Laws) {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {k : ℕ} {α : D.X} {m : ℕ}
    (b : Fin m → D.SecB k α) {K : Type} [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R))
    (hb : IsSecBasis (T := Over.mk t) (A := D.P.A) _
      (fun i => DVR.pullSec D.P.L (D.famφB α) (DegPre.famε k) (b i) (snd (Over.mk t) D.P.A).left))
    (a : Fin m → K) (ha : ∃ i, a i ≠ 0) {l : ℕ} (hl : 2 ≤ l) (hK : (l : K) ≠ 0) :
    ∃ (x : Over.mk t ⟶ D.P.A) (j : ℕ), x ^ l ^ j = 1 ∧ ∀ (z : Spec (CommRingCat.of K)) J, Good D.P.L z J →
      IsUnit (∑ i, gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (a i)) * sval (Z := Spec (CommRingCat.of K)) (b i) x.left z J) := by
  obtain ⟨σ, hσ⟩ := exists_sec_lin
    (fun i => (fst (Over.mk t) D.P.A).left.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (a i)))
    (fun i => DVR.pullSec D.P.L (D.famφB α) (DegPre.famε k) (b i) (snd (Over.mk t) D.P.A).left)
  obtain ⟨x, j, hx, hu⟩ := exists_torsion_isUnit hL D.P t σ (fun h => by
    obtain ⟨i, hi⟩ := ha
    have e := (hb σ).unique (y₁ := fun i => (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (a i)) (y₂ := 0) hσ
      (fun j => (h j).trans (Finset.sum_eq_zero fun i _ => by
        rw [Pi.zero_apply, map_zero, map_zero, MulZeroClass.zero_mul]).symm)
    exact hi ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).1
      ((congrFun e i).trans (map_zero _).symm))) hl hK
  refine ⟨x, j, hx, fun z J hJ => ?_⟩
  have q := hu z J hJ
  rw [SectionScalarValuation.sval_lin _ _ hσ _ z hJ] at q
  refine (congrArg IsUnit (Finset.sum_congr rfl fun i _ => ?_)).mp q
  rw [SectionScalarValuation.sval_pullSec _ _ _ _ _ z hJ, IntegralCoord.gs_appTop, ← Over.comp_left, ← Over.comp_left, lift_fst, lift_snd]
  rfl

section
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
  {D : DegData V (maximalIdeal V)}
  {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v)

theorem genV_torsion {N : ℕ} (hN : N ≠ 0) (g : GtPtF D.toPre F)
    (hg : letI := TorusExt.gtGroup D.toPre F; N • g = 0) (χ : D.toPre.X) : GenV hϖ hv (g.s χ) 0 := by
  letI := TorusExt.gtGroup D.toPre F
  choose l hl hu using fun g : GtPtF D.toPre F => CoefVal.exists_gtV (hϖ := hϖ) (hv := hv) g
  let L : GtPtF D.toPre F →+ (D.toPre.X →+ ℚ) := AddMonoidHom.mk' l fun g g' =>
    (hu (g + g') (l g + l g') (CoefVal.gtV_add ((TorusExt.isAdd_iff_eq _ _ _).2 rfl) (hl g) (hl g'))).symm
  have e : N • l g = 0 := by
    show N • L g = 0
    rw [← map_nsmul, hg, map_zero]
  have e' : l g χ = 0 := by
    have := DFunLike.congr_fun e χ
    simpa [hN] using this
  rw [← e']
  exact hl g χ

theorem exists_value_unit {k : ℕ} {α : D.toPre.X} {m : ℕ} (b : Fin m → D.toPre.SecB k α) (a : Fin m → Ov v)
    (x : TO hϖ hv ⟶ D.toPre.P.A)
    (hu : ∀ (z : Spec (CommRingCat.of (ResidueField (Ov v)))) J, Good D.toPre.P.L z J →
      IsUnit (∑ i, gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (ResidueField (Ov v)))).inv.hom (residue _ (a i))) *
        sval (b i) (Spec.map (CommRingCat.ofHom (residue (Ov v))) ≫ x.left) z J)) :
    ∃ G₀ : LB.Gen (LB.LinComb D.toPre.P.L (fun i => x.left ≫ DegPre.famφB D.toPre α i) (DegPre.famε k)), G₀.IsGen ∧
      ∃ c : F, v c = 0 ∧ ∀ (z : (TF (R := V) F).left) J, Good D.toPre.P.L z J →
        ∑ i, GlobalTheory.UT.cst F z (a i) * sval (b i) (ιS hϖ hv ≫ x).left z J =
          GlobalTheory.UT.cst F z c * (val G₀ (ιS hϖ hv).left z J).val := by
  have hL := D.toPre.P.isLB
  obtain ⟨G₀, hG₀⟩ := exists_gen_of_local (V := Ov v) D.toPre.P.L hL
    (fun i => x.left ≫ DegPre.famφB D.toPre α i) (DegPre.famε k)
  choose y hy using fun i => TwistUnit.exists_ratio_local (R := Ov v) hL (H1.SectionArithmetic.pullSec (b i) x.left) G₀ hG₀
  have key : ∀ {E : Type} [CommRing E] (φ : Ov v →+* E) (z : Spec (CommRingCat.of E)) J, Good D.toPre.P.L z J →
      ∑ i, gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of E)).inv.hom (φ (a i))) *
        sval (b i) (Spec.map (CommRingCat.ofHom φ) ≫ x.left) z J =
      gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of E)).inv.hom
        (φ (∑ i, a i * (Scheme.ΓSpecIso (CommRingCat.of (Ov v))).hom.hom (y i)))) *
        (val G₀ (Spec.map (CommRingCat.ofHom φ)) z J).val := fun φ z J hJ => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum, SectionScalarValuation.gs_sum _ z ⊤ trivial, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e := gs_pull (𝟙 _) (Spec.map (CommRingCat.ofHom φ)) z ⊤ trivial (y i)
    rw [Category.id_comp] at e
    have e' := e.symm.trans (congrArg (gs (𝟙 _) z ⊤) (appTop_specMap (CommRingCat.ofHom φ) (y i)))
    have q := (H1.SectionArithmetic.sval_pullSec (b i) x.left _ z hJ).symm.trans (hy i _ (Spec.map (CommRingCat.ofHom φ)) z J hJ)
    rw [map_mul, map_mul, gs_mul _ z ⊤ trivial, _root_.mul_assoc]
    exact congrArg (_ * ·) (q.trans (congrArg (· * _) e'))
  have hc : IsUnit (∑ i, a i * (Scheme.ΓSpecIso (CommRingCat.of (Ov v))).hom.hom (y i)) := by
    let z₀ : Spec (CommRingCat.of (ResidueField (Ov v))) := closedPoint _
    obtain ⟨J, hJ⟩ := CoefBasic.exists_good' hL z₀
    have h₁ := isUnit_of_mul_isUnit_left ((congrArg IsUnit (key (residue _) z₀ J hJ)).mp (hu z₀ J hJ))
    refine isUnit_of_map_unit (residue _) _ (IsUnit.mk0 _ fun h0 => ?_)
    rw [h0, map_zero, gs_eq _ _ ⊤ trivial, map_zero, map_zero] at h₁
    exact not_isUnit_zero h₁
  exact ⟨G₀, hG₀, _, v_unit v hc.unit, fun z J hJ => key (algebraMap (Ov v) F) z J hJ⟩

theorem exists_coord {k : ℕ} {α : D.toPre.X} {m : ℕ} (b : Fin m → D.toPre.SecB k α)
    (hb : IsSecBasis (T := TO hϖ hv) (A := D.toPre.P.A) _ (fun i => DVR.pullSec D.toPre.P.L (D.toPre.famφB α)
      (DegPre.famε k) (b i) (snd (TO hϖ hv) D.toPre.P.A).left))
    {s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k))} (hs : VGe D F v k α s 0) :
    ∃ a : Fin m → Ov v, (∀ q : ℚ, (∀ i, (q : WithTop ℚ) ≤ v (a i)) → VGe D F v k α s q) ∧
      ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (J), Good D.toPre.P.L z J →
        sval s ρ z J = ∑ i, gs ρ z ⊤ (gF D.toPre F (a i)) * sval (b i) (ρ ≫ (DegPre.prB D.toPre F).left) z J := by
  have hL := D.toPre.P.isLB
  obtain ⟨n, c, σ, σF, hσ, hc, hsum⟩ := hs
  let c₀ : Fin n → Γ(Spec (CommRingCat.of (Ov v)), ⊤) := fun l =>
    (Scheme.ΓSpecIso (CommRingCat.of (Ov v))).inv.hom ⟨c l, hc l⟩
  have ec : ∀ l, ιr (v := v) (c₀ l) = c l := fun l =>
    congrArg (algebraMap (Ov v) F) (Iso.inv_hom_id_apply (Scheme.ΓSpecIso (CommRingCat.of (Ov v))) ⟨c l, hc l⟩)
  obtain ⟨t, ht⟩ := exists_sec_lin (fun l => (fst (TO hϖ hv) D.toPre.P.A).left.appTop.hom (c₀ l))
    (fun l => DVR.pullSec D.toPre.P.L (D.toPre.famφB α) (DegPre.famε k) (σ l) (snd (TO hϖ hv) D.toPre.P.A).left)
  obtain ⟨r, hr, -⟩ := hb t
  have key : ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (J), Good D.toPre.P.L z J →
      sval s ρ z J = ∑ i, gs ρ z ⊤ (gF D.toPre F (ιr (v := v) (r i))) *
        sval (b i) (ρ ≫ (DegPre.prB D.toPre F).left) z J := fun Z ρ z J hJ => by
    have e₁ := SectionScalarValuation.sval_lin _ _ ht (ρ ≫ (jO hϖ hv).left) z hJ
    have e₂ := SectionScalarValuation.sval_lin (fun i => (fst (TO hϖ hv) D.toPre.P.A).left.appTop.hom (r i)) _ hr
      (ρ ≫ (jO hϖ hv).left) z hJ
    simp only [SectionScalarValuation.sval_pullSec _ _ _ _ _ z hJ, gs_jO, ec, Category.assoc, jO_snd] at e₁ e₂
    rw [SectionScalarValuation.sval_lin (fun i => gF D.toPre F (c i)) σF (fun j => hsum j) ρ z hJ, ← e₂, e₁]
    exact Finset.sum_congr rfl fun l _ => by rw [SectionScalarValuation.secScal_sval (hσ l) ρ z hJ]
  refine ⟨fun i => (Scheme.ΓSpecIso (CommRingCat.of (Ov v))).hom.hom (r i), fun q hq => ?_, key⟩
  have hF : FormEq (fun i => (DegPre.prB D.toPre F).left ≫ D.toPre.famφB α i) (DegPre.famε k)
      (DegPre.famφ D.toPre F α) (DegPre.famε k) := fun U _ g =>
    Finset.prod_congr rfl fun i _ => by rw [GC.famφ_eq]
  choose bF hbF using fun i => exists_sec hL hF (pullSec D.toPre.P.L _ _ (b i) (DegPre.prB D.toPre F).left)
  have hb' := fun i y J hJ => (hbF i _ (𝟙 _) y J hJ).trans (SectionScalarValuation.sval_pullSec _ _ _ _ _ y hJ)
  refine ⟨m, _, b, bF, fun i => SectionScalarValuation.secScal_of_sval hL fun y J hJ => (hb' i y J hJ).symm, hq,
    IntegralCoord.lin_of_sval hL (fun i => gF D.toPre F (ιr (v := v) (r i))) bF fun y J hJ => ?_⟩
  rw [key _ _ y J hJ]
  exact Finset.sum_congr rfl fun i _ => congrArg (_ * ·) (hb' i y J hJ).symm

end

theorem exists_eq_zero {n : ℕ} (c : Fin n → WithTop ℚ) (h₀ : ∀ i, 0 ≤ c i)
    (h : ∀ q : ℚ, 0 < q → ¬ ∀ i, (q : WithTop ℚ) ≤ c i) : ∃ i, c i = 0 := by
  by_contra hc
  have h₁ : (0 : WithTop ℚ) < Finset.univ.inf c := (Finset.lt_inf_iff (WithTop.coe_lt_top 0)).2 fun i _ =>
    lt_of_le_of_ne (h₀ i) fun e => hc ⟨i, e.symm⟩
  obtain ⟨q, hq, hq'⟩ := WithTop.lt_iff_exists_coe_btwn.1 h₁
  exact h q (WithTop.coe_lt_coe.1 hq) fun i => hq'.le.trans (Finset.inf_le (Finset.mem_univ i))

theorem exists_torsion_coef_val_zero : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllDV fun {V} _ _ _ {ϖ} hϖ D Q {F} _ _ {v} hv => ∀ k n : ℕ, 4 ≤ k → n.Prime → IsUnit (n : V) → ∀ (s : Fam D.toPre F k) (α : D.toPre.X), VGe D F v k α (s.s α) 0 → (∀ q : ℚ, 0 < q → ¬ VGe D F v k α (s.s α) q) → ∃ (i : ℕ) (g o : GtPtF D.toPre F), o.IsZero ∧ GtPtF.IsNsmul (n ^ i) g o ∧ ∀ w : Frm D.toPre F k g.b, w.IsGen → GenV hϖ hv w 0 → v (coef s g w α) = 0 := by
  intro hL _ _ _ _ V _ _ _ _ _ ϖ hϖ D Q hQ F _ _ _ v hv k n hk hn hnV s α hs hs'
  have hM := D.toPre.P.isLB
  have hT : TwistBaseChangeStatement := GlobalTheory.twistBaseChange_of_finrank_sections_one fun K _ _ P =>
    (hL.1.globalSectionsRank K P 1 le_rfl).trans (one_pow _)
  obtain ⟨m, b, -, hb⟩ := hT V D.toPre k (by omega) α
  have hb₁ : ∀ (R' : Type) [CommRing R'] (f : V →+* R') (t : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of V)),
      t = Spec.map (CommRingCat.ofHom f) → IsSecBasis (T := Over.mk t) (A := D.toPre.P.A) _
        (fun i => DVR.pullSec D.toPre.P.L (D.toPre.famφB α) (DegPre.famε k) (b i) (snd (Over.mk t) D.toPre.P.A).left) := by
    intro R' _ f t ht
    subst ht
    exact hb R' f _ (fun i j => rfl)
  obtain ⟨a, ha, hsa⟩ := exists_coord hϖ hv b (hb₁ _ _ _ rfl) hs
  obtain ⟨i₀, hi₀⟩ := exists_eq_zero (fun i => v (a i)) (fun i => (a i).2) fun q hq h => hs' q hq (ha q h)
  have hres : residue (Ov v) (a i₀) ≠ 0 := by
    rw [residue_ne_zero_iff_isUnit, ValuationSubring.valuation_eq_one_iff]
    exact (valuation_eq_one_iff (fun _ => Iff.rfl) _).2 hi₀
  have : IsAlgClosed (ResidueField (Ov v)) := isAlgClosed_residueField_of_valuationRing_of_isAlgClosed (Ov v) F
  have hK : (n : ResidueField (Ov v)) ≠ 0 := by
    have := (hnV.map ((residue (Ov v)).comp (fO v hϖ hv))).ne_zero
    rwa [map_natCast] at this
  obtain ⟨x₀, j, hx₀, hu⟩ := exists_torsion_sum hL.1 D.toPre b
    (Spec.map (CommRingCat.ofHom (residue (Ov v))) ≫ (TO hϖ hv).hom)
    (hb₁ _ ((residue (Ov v)).comp (fO v hϖ hv)) _ (Spec.map_comp _ _).symm) (fun i => residue _ (a i)) ⟨i₀, hres⟩
    hn.two_le hK
  have hN : n ^ j ≠ 0 := pow_ne_zero _ hn.ne_zero
  obtain ⟨hfin, hflat, -⟩ := hL.1.mulN _ D.toPre.P (n ^ j) (by omega)
  obtain ⟨x, hx, ex⟩ : ∃ x : TO hϖ hv ⟶ D.toPre.P.A, x ^ n ^ j = 1 ∧
      Spec.map (CommRingCat.ofHom (residue (Ov v))) ≫ x.left = x₀.left :=
    ExactTerm.exists_torsion_lift (Ov v) D.toPre.P.A (n ^ j) (TO hϖ hv).hom x₀ hx₀
  obtain ⟨G₀, hG₀, c, hc, hval⟩ := exists_value_unit hϖ hv b a x (fun z J hJ => by rw [ex]; exact hu z J hJ)
  letI := TorusExt.gtGroup D.toPre F
  obtain ⟨g, hg₁, hg₂⟩ := TorusExt.exists_nsmul_eq_of_pow_eq hN (0 : GtPtF D.toPre F)
    (b := ιS hϖ hv ≫ x) (by rw [← MonObj.comp_pow, hx, MonObj.comp_one, TorusExt.zero_b])
  refine ⟨j, g, 0, (TorusExt.isZero_iff_eq _).2 rfl, (TorusExt.isNsmul_iff_eq _ _ _).2 hg₂.symm, fun w _ hω => ?_⟩
  obtain ⟨d, hd, vd⟩ := CoefUnit.v_of_isCoef hϖ hv (genV_torsion hϖ hv hN g hg₂ α) hω x hg₁.symm (s.s α) G₀ hG₀ c
    (fun z J hJ => by
      rw [hsa _ _ z J hJ, ← hval z J hJ, ← Over.comp_left, lift_snd, hg₁]
      refine Finset.sum_congr rfl fun i _ => congrArg (· * _) ?_
      refine (gs_pull _ (fst (TF (R := V) F) D.toPre.P.A).left z ⊤ trivial _).trans ?_
      rw [← Over.comp_left, lift_fst]; rfl)
  rw [CoefBasic.coef_eq hd, vd, hc]
  simp

end GlobalTheory.OneBasis.UnitTerm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorsionPointPrimitiveComponentValuationZerStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torsion_point_primitive_component_valuation_zero : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllDV fun {V} _ _ _ {ϖ} hϖ D Q {F} _ _ {v} hv => ∀ k n : ℕ, 4 ≤ k → n.Prime → IsUnit (n : V) → ∀ (s : Fam D.toPre F k) (α : D.toPre.X), VGe D F v k α (s.s α) 0 → (∀ q : ℚ, 0 < q → ¬ VGe D F v k α (s.s α) q) → ∃ (i : ℕ) (g o : GtPtF D.toPre F), o.IsZero ∧ GtPtF.IsNsmul (n ^ i) g o ∧ ∀ w : Frm D.toPre F k g.b, w.IsGen → GenV hϖ hv w 0 → v (coef s g w α) = 0 := by
  first | exact @GlobalTheory.OneBasis.UnitTerm.exists_torsion_coef_val_zero | exact GlobalTheory.OneBasis.UnitTerm.exists_torsion_coef_val_zero | (intros; apply GlobalTheory.OneBasis.UnitTerm.exists_torsion_coef_val_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorsionPointUnitValuePrimitiveIntegralFami
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

noncomputable section
namespace GlobalTheory.OneBasis.UnitValue
open GlobalTheory.TorusExt GlobalTheory.UT.WeightValue GlobalTheory.UT.CoefBasic

theorem not_all_ne_zero {F : Type} [Field F] [IsAlgClosed F] [CharZero F] {v : AddValuation F (WithTop ℚ)} {X : Type}
    [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] {n : ℕ} (hn : 2 ≤ n) (hvn : v (n : F) = 0) {a : X → F}
    (ha : NullV v a) (h0 : ∀ χ, 0 ≤ v (a χ)) {α : X} (hα : v (a α) = 0)
    (H : ∀ t : Multiplicative X →* Fˣ, (∃ k, t ^ n ^ k = 1) →
      ∃ S, SumV v (fun χ => (t (Multiplicative.ofAdd χ)).val * a χ) S ∧ v S ≠ 0) : False := by
  classical
  choose! S hS hS0 using H
  have hroot : ∀ (t : Multiplicative X →* Fˣ) (k : ℕ), t ^ n ^ k = 1 → ∀ χ, v (t χ).val = 0 ∧ v ((t χ)⁻¹).val = 0 := by
    intro t k ht χ
    have e : t χ ^ n ^ k = 1 := by rw [← MonoidHom.pow_apply, ht, MonoidHom.one_apply]
    have hN : 0 < n ^ k := pow_pos (by omega) k
    exact ⟨GlobalTheory.TorsRecov.val_eq_zero_of_pow v _ _ hN (by rw [← Units.val_pow_eq_pow_val, e, Units.val_one]),
      GlobalTheory.TorsRecov.val_eq_zero_of_pow v _ _ hN (by rw [← Units.val_pow_eq_pow_val, inv_pow, e, inv_one, Units.val_one])⟩
  have hpos : ∀ (t : Multiplicative X →* Fˣ) (k : ℕ), t ^ n ^ k = 1 → 0 < v (S t) := fun t k ht =>
    lt_of_le_of_ne (le_of_sumV (q := 0) (hS t ⟨k, ht⟩) fun χ => by
      rw [v.map_mul, (hroot t k ht _).1, zero_add]; exact h0 χ) (hS0 t ⟨k, ht⟩).symm
  obtain ⟨k, hk⟩ := GlobalTheory.coeff_recovery_by_torsion_averages F v X n hn hvn a ha S hS (fun _ => α)
    (fun _ => ⟨0, by simp⟩) (a α) (Or.inl ⟨α, fun _ => ⟨0, by simp⟩, rfl⟩) 1
  have h1 := hk k le_rfl
  have hN : 0 < n ^ k := pow_pos (by omega) k
  haveI : Finite {t : Multiplicative X →* Fˣ // t ^ n ^ k = 1} :=
    Nat.finite_of_card_ne_zero (by
      rw [GlobalTheory.TorsRecov.card_tors F X _ hN]; exact pow_ne_zero _ hN.ne')
  letI := Fintype.ofFinite {t : Multiplicative X →* Fˣ // t ^ n ^ k = 1}
  rw [finsum_eq_sum_of_fintype] at h1
  have h2 : 0 < v (((n : F) ^ (k * Module.finrank ℤ X))⁻¹ * ∑ t : {t : Multiplicative X →* Fˣ // t ^ n ^ k = 1},
      ((t.1 (Multiplicative.ofAdd α))⁻¹).val * S t.1) := by
    rw [v.map_mul, GlobalTheory.TorsRecov.val_inv_pow v _ _ hvn, zero_add]
    refine v.map_lt_sum WithTop.zero_ne_top fun t _ => ?_
    rw [v.map_mul, (hroot t.1 k t.2 _).2, zero_add]
    exact hpos t.1 k t.2
  have h3 := v.map_lt_add (lt_of_lt_of_le (by exact_mod_cast (zero_lt_one : (0 : ℚ) < 1)) h1) h2
  rw [sub_add_cancel, hα] at h3
  exact lt_irrefl _ h3

section
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} {hϖ : Irreducible ϖ}
  {D : DegData V (maximalIdeal V)}
  {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)} {hv : ValOver ϖ F v}

theorem exists_frm_zero (k : ℕ) (g : GtPtF D.toPre F) : ∃ w : Frm D.toPre F k g.b, w.IsGen ∧ GenV hϖ hv w 0 := by
  obtain ⟨w, hw⟩ := (coef_basic V D.toPre F k g).1
  obtain ⟨r, φ₀, hφ, t₀, ht₀, x, hx, e⟩ := CoefVal.exists_genV_frm (hϖ := hϖ) (hv := hv) hw
  have hx0 : x ≠ 0 := v.ne_top_iff.1 (by rw [hx]; exact WithTop.coe_ne_top)
  obtain ⟨w', hw', e'⟩ := TorsionValue.exists_frm_scale w hw (inv_ne_zero hx0)
  refine ⟨w', hw', φ₀, hφ, t₀, ht₀, 1, v.map_one, fun z J hJ => ?_⟩
  rw [e' z J hJ, e z J hJ, ← _root_.mul_assoc, cst_eq, cst_eq, cst_eq, ← map_mul, inv_mul_cancel₀ hx0]

theorem exists_frm_cast {k : ℕ} {b b' : TF (R := V) F ⟶ D.toPre.P.A} (hb : b' = b) (w : Frm D.toPre F k b) (hw : w.IsGen)
    (h0 : GenV hϖ hv w 0) : ∃ w' : Frm D.toPre F k b', w'.IsGen ∧ GenV hϖ hv w' 0 ∧
      ∀ z J, Good D.toPre.P.L z J → val w' (𝟙 _) z J = val w (𝟙 _) z J := by
  subst hb
  exact ⟨w, hw, h0, fun _ _ _ => rfl⟩

end


attribute [local instance] gtGroup in
theorem exists_unit_value : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ k n : ℕ, 4 ≤ k → n.Prime → IsUnit (n : V) → ∀ (t : SecA A F k) (s : Fam D.toPre F k) (α : D.toPre.X), U.ExpandsF F k w₀ t s → IntGe D v s 0 → (∀ q : ℚ, 0 < q → ¬ VGe D F v k α (s.s α) q) → ∃ (j : ℕ) (x : TFK (R := V) F ⟶ A.A), 2 ≤ j ∧ FromGt U.toUnifPre (n ^ j) x ∧ ∀ e (c : F), IsTorsFrame A ρ (n ^ j) x e → ValAt t x e c → v c = 0 := by
  intro hL hT hVR hTW hUU V _ _ _ _ hcpl ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U w₀ ρ hN k n hk hn hnV t s α hts hint hprim
  by_contra hcon
  have hk1 : 1 ≤ k := by omega
  have hA : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hcpl⟩
  have : CharZero (FractionRing V) := IsFractionRing.charZero V
  have : CharZero F := (algebraMap (FractionRing V) F).charZero_iff (algebraMap (FractionRing V) F).injective |>.1 this
  obtain ⟨i, g, o, ho, hgo, hg⟩ := GlobalTheory.T.exists_torsion_point_primitive_component_valuation_zero hL hT hVR hTW hUU V hcpl ϖ hϖ D Q hQ F v hv k n hk hn hnV s α
    (hint α) hprim
  have hgi : n ^ i • g = 0 := ((isNsmul_iff_eq _ _ _).1 hgo).symm.trans ((isZero_iff_eq _).1 ho)
  obtain ⟨w, hw, hw0⟩ := exists_frm_zero (hϖ := hϖ) (hv := hv) k g
  have hB := D.tau_bimult
  have hiota0 : ∀ (h : GtPtF D.toPre F), h.IsZero → h.IsIota 0 := by
    intro h hh
    obtain ⟨hb, hv⟩ := (isZero_iff h).1 hh
    refine (isIota_iff 0 h).2 ⟨hb.trans (cPoint_zero _).symm, fun χ y J hJ => ?_⟩
    have face : ∀ x z, th D.toPre (T := TF (R := V) F) y J 1 x z = 1 := by
      intro x z
      have e := val_corr hJ (D.toPre.cub.face 0) (lift x z).left
      rw [val_one] at e
      refine Eq.trans ?_ e
      refine Eq.trans ?_ (val_cub D.toPre.cub (lift x z) hJ (pzero _ _) (x2 _ 0) (x2 _ 1)).symm
      congr 1 <;> simp [x2, pzero, Hom.one_def]
    have tt := tau_mul (𝟙 (TF (R := V) F)) hJ hB 0 0 χ
    rw [add_zero, cPoint_zero, face, _root_.mul_one] at tt
    exact (hv χ y J hJ).trans (mul_eq_left.1 tt.symm).symm
  let qkMk (g : GtPtF D.toPre F) {k : ℕ} (h : k • g = 0) : QkPt D.toPre F k :=
    ⟨0, g, k • g, (isNsmul_iff_eq _ _ _).2 rfl, hiota0 _ ((isZero_iff_eq _).2 h)⟩
  have hgV : ∀ χ, GenV hϖ hv (g.s χ) 0 := fun χ => by
    have e := CoefVal.gtV_qk (hϖ := hϖ) (hv := hv) hVR hQ (Nat.one_le_pow i n hn.pos)
      (qkMk g hgi) χ
    simpa only [qkMk, bOf_zero_left hϖ hQ, Int.cast_zero, zero_div] using e
  have hvn : v (n : F) = 0 := by
    have e := GC.v_alg_unit hv hnV.unit
    rwa [IsUnit.unit_spec, map_natCast, map_natCast] at e
  refine not_all_ne_zero (v := v) (a := coef s g w) (α := α) hn.two_le hvn
    (((CoefVal.main hL hT hVR hTW hUU V hcpl ϖ hϖ D Q hQ F v hv g).2.2.2.2.2.2 k hk1 w s hw).1)
    (fun χ => by simpa using CoefVal.le_v_coef hw (hint χ) (hgV χ) hw0) (hg w hw hw0) ?_
  rintro τ ⟨m, hm⟩
  have hj : 1 ≤ n ^ (i + m + 2) := Nat.one_le_pow _ n hn.pos
  let p : QkPt D.toPre F (n ^ (i + m + 2)) := qkMk (g + torusPt D.toPre F (Additive.ofMul τ)) (by
    have e₁ : n ^ (i + m + 2) • g = 0 := by rw [add_assoc, pow_add, mul_comm, mul_smul, hgi, smul_zero]
    have e₂ : τ ^ n ^ (i + m + 2) = 1 := by
      rw [show i + m + 2 = m + (i + 2) by ring, pow_add, pow_mul, hm, one_pow]
    rw [smul_add, e₁, ← map_nsmul, ← ofMul_pow, e₂, ofMul_one, map_zero, add_zero])
  obtain ⟨f, hf, -⟩ := GlobalTheory.T.uniformisation_torsion_identification_with_pairing hL V (maximalIdeal V) hA D A G hG U F _ hj
  have hx : QkToAkU U.toUnifPre F _ p (f p) := (hf p _).2 rfl
  have hex : ∃ e c, IsTorsFrame A ρ (n ^ (i + m + 2)) (f p) e ∧ ValAt t (f p) e c ∧ v c ≠ 0 := by
    by_contra h
    refine hcon ⟨i + m + 2, f p, by omega, ⟨p, rfl, hx⟩, fun e c he hc => ?_⟩
    by_contra h'
    exact h ⟨e, c, he, hc, h'⟩
  obtain ⟨e, c, he, hc, hc0⟩ := hex
  obtain ⟨w₁, hw₁, hv₁, hsum⟩ := GlobalTheory.T.section_value_at_torsionPoint_eq_sum_terms hL hT hVR hTW hUU V hcpl ϖ hϖ D Q hQ F v hv A G hG U w₀ ρ hN _ hj p _ hx e he
  have hv₁ : GenV hϖ hv w₁ 0 := by
    have e0 : ((Q p.y : ℚ) / ((n ^ (i + m + 2) : ℕ) : ℚ) ^ 2) = 0 := by
      rw [show p.y = 0 from by simp only [p, qkMk], QForm.Q_zero hϖ D hQ]; simp
    rwa [e0] at hv₁
  obtain ⟨w₂, hw₂, hwv⟩ := exists_pow k (line_exp k) w₁ hw₁
  have hw₂0 : GenV hϖ hv w₂ 0 := genV_pow k (line_exp k) hv₁ fun z J _ => hwv _ _ z J
  have hS : SumV v (coef s p.g w₂) c := hsum k hk1 w₂ ⟨hw₂, fun z J _ => hwv _ _ z J⟩ t s c hts hc
  have hb : p.g.b = g.b := by
    simp only [p, qkMk, add_b, torusPt_b, _root_.mul_one]
  obtain ⟨w', hw', hw'0, hww⟩ := exists_frm_cast hb w hw hw0
  obtain ⟨u, hu, huv, huc⟩ := ((coef_basic V D.toPre F k p.g).2.2 w₂ hw₂).2.2.1 w' hw'
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 (v.ne_top_iff.2 hu)
  have r0 : r = 0 := by
    have := CoefVal.sep D
    exact CoefVal.genV_unique D.toPre.P.isLB (genV_smul hw₂0 hr.symm huv) hw'0
  have hu0 : v u = 0 := by rw [← hr, r0]; rfl
  have htr := ((coef_basic V D.toPre F k g).2.2 w hw).2.2.2 τ _ p.g w'
    ((isTor_iff _ _).2 (isTorusPtF_torusPt τ)) ((isAdd_iff_eq _ _ _).2 (by simp only [p, qkMk])) hww s
  refine ⟨u * c, ?_, by rwa [v.map_mul, hu0, zero_add]⟩
  have := sumV_mul hS hu0
  simpa only [← huc, htr] using this

end GlobalTheory.OneBasis.UnitValue
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorsionPointUnitValuePrimitiveIntegralFamiStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torsionPoint_unit_value_primitive_integral_family : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ k n : ℕ, 4 ≤ k → n.Prime → IsUnit (n : V) → ∀ (t : SecA A F k) (s : Fam D.toPre F k) (α : D.toPre.X), U.ExpandsF F k w₀ t s → IntGe D v s 0 → (∀ q : ℚ, 0 < q → ¬ VGe D F v k α (s.s α) q) → ∃ (j : ℕ) (x : TFK (R := V) F ⟶ A.A), 2 ≤ j ∧ FromGt U.toUnifPre (n ^ j) x ∧ ∀ e (c : F), IsTorsFrame A ρ (n ^ j) x e → ValAt t x e c → v c = 0 := by
  first | exact @GlobalTheory.OneBasis.UnitValue.exists_unit_value | exact GlobalTheory.OneBasis.UnitValue.exists_unit_value | (intros; apply GlobalTheory.OneBasis.UnitValue.exists_unit_value <;> assumption)
end
