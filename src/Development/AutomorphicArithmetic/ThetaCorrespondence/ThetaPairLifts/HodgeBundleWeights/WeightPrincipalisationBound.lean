module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPositivityPrincipalisation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPositivityPrincipalisationDeep
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToroidalFlagNonempty
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.LogCanonicalCriterionBoundary
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.IntegralFramePointStalkCompat
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.HodgeBundleAmpleOnRegularLocus

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CuspRatioFieldEqTopOfToroidalCompactification
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CuspGermTransferOfBoundary
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Vanishing.H0
open GlobalTheory.Vanishing.H0
namespace GlobalTheory.CuspTransfer
theorem exists_cusp_germ_transfer : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), FnAlgClosed (Xo := Xo) (c := c) → ∀ (M : Modif (str₀ TF.X Z) (U₀ TF.X Z) (dimFlag Dw)) (ω : CanId M) (b s : AllWt.Weight Dw), FlagTan.kap Dw + b = s → vanBd TF.X Z s ≤ space TF.X Z U s → ∃ F : H0 M.str (tens M.K.bundle ((L₀ TF.X Z b).pull M.σ)) ⊤ → Cusp Z U s, ∀ (z : M.X) (hz : z ∈ M.off) (j : (tens M.K.bundle ((L₀ TF.X Z b).pull M.σ)).ι) (hj : z ∈ (tens M.K.bundle ((L₀ TF.X Z b).pull M.σ)).U j) (i : (L₀ TF.X Z s).ι) (hi : M.σ z ∈ (L₀ TF.X Z s).U i), ∃ u : (M.X.presheaf.stalk z)ˣ, ∀ g : H0 M.str (tens M.K.bundle ((L₀ TF.X Z b).pull M.σ)) ⊤, germ j z (memTop z) hj g = u.val * (M.σ.stalkMap z).hom (germ i (M.σ z) (M.off_eq.le hz) hi (cuspSec TF.X Z U s (F g))) := by
  intro hP hG E _ _ _ H Dw l Xo c TF Z r U hF M ω b s hs hvs
  set C := ((common₀ TF.X Z).pull M.σ).canChart M.K.isLB hs with hC
  have key : ∀ g : H0 M.str (tens M.K.bundle ((L₀ TF.X Z b).pull M.σ)) ⊤, ∃ f : Cusp Z U s,
      C.mul ω.ω (M.pullOff (cuspSec TF.X Z U s f)) = H0.restr le_top g := by
    intro g
    obtain ⟨m, hm⟩ := (M.bijective_pullOff (isLB_L₀ TF.X Z s)).2 ((C.mulEquiv ω.unit).symm (H0.restr le_top g))
    have hm' : C.mul ω.ω (M.pullOff m) = H0.restr le_top g := by
      rw [hm, ← ProdChart.mulEquiv_apply C ω.unit, LinearEquiv.apply_symm_apply]
    obtain ⟨g', hv, hr⟩ := (_root_.GlobalTheory.T.log_canonical_criterion_boundary hP hG E H Dw l Xo c TF Z hF M ω b s hs m).2 ⟨g, hm'.symm⟩
    refine ⟨ofSpace TF.X Z U s ⟨g', hvs hv⟩, ?_⟩
    rw [cuspSec_ofSpace]
    exact (congrArg (fun x => C.mul ω.ω (M.pullOff x)) hr).trans hm'
  refine ⟨fun g => (key g).choose, ?_⟩
  intro z hz j hj i hi
  obtain ⟨t, ha, hb, hc⟩ := C.cover z
  have hω : IsUnit (H0.germ (C.a t) z hz ha ω.ω) := ω.unit z hz (C.a t) ha
  refine ⟨tr _ z j (C.c t) * hω.unit *
      Units.map (M.σ.stalkMap z).hom.toMonoidHom (tr (L₀ TF.X Z s) (M.σ z) (C.b t PUnit.unit) i), ?_⟩
  intro g
  have hg := (key g).choose_spec
  rw [H0.germ_change j (C.c t) z (memTop z) hj hc g, ← H0.germ_restr le_top (C.c t) z hz hc g, ← hg,
    C.germ_mul ω.ω _ t z hz ha hb hc]
  change _ = _ * (M.σ.stalkMap z).hom _
  have e2 := H0.germ_pull M.σ M.off_eq.le (C.b t) z hz hb (cuspSec TF.X Z U s (key g).choose)
  change _ * (_ * H0.germ (C.b t) z hz hb (H0.pull M.σ M.off_eq.le (cuspSec TF.X Z U s (key g).choose))) = _
  rw [e2]
  erw [H0.germ_change (B := L₀ TF.X Z s) (C.b t PUnit.unit) i (M.σ z) (M.off_eq.le hz) _ hi, map_mul]
  simp only [Units.val_mul, IsUnit.unit_spec, Units.coe_map]
  simp only [mul_assoc]
  rfl
end GlobalTheory.CuspTransfer
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Vanishing.H0
open GlobalTheory.Vanishing.H0
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_germ_transfer_of_boundary : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), FnAlgClosed (Xo := Xo) (c := c) → ∀ (M : Modif (str₀ TF.X Z) (U₀ TF.X Z) (dimFlag Dw)) (ω : CanId M) (b s : AllWt.Weight Dw), FlagTan.kap Dw + b = s → vanBd TF.X Z s ≤ space TF.X Z U s → ∃ F : H0 M.str (tens M.K.bundle ((L₀ TF.X Z b).pull M.σ)) ⊤ → Cusp Z U s, ∀ (z : M.X) (hz : z ∈ M.off) (j : (tens M.K.bundle ((L₀ TF.X Z b).pull M.σ)).ι) (hj : z ∈ (tens M.K.bundle ((L₀ TF.X Z b).pull M.σ)).U j) (i : (L₀ TF.X Z s).ι) (hi : M.σ z ∈ (L₀ TF.X Z s).U i), ∃ u : (M.X.presheaf.stalk z)ˣ, ∀ g : H0 M.str (tens M.K.bundle ((L₀ TF.X Z b).pull M.σ)) ⊤, germ j z (memTop z) hj g = u.val * (M.σ.stalkMap z).hom (germ i (M.σ z) (M.off_eq.le hz) hi (cuspSec TF.X Z U s (F g))) := by
  first | exact @_root_.GlobalTheory.CuspTransfer.exists_cusp_germ_transfer | exact _root_.GlobalTheory.CuspTransfer.exists_cusp_germ_transfer | (intros; apply _root_.GlobalTheory.CuspTransfer.exists_cusp_germ_transfer <;> assumption)
end
end

section
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.SepCusp
section Geometry
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory _root_.Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn exOf secZ)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Vanishing.H0
open GlobalTheory.CompHt (genVal genPoint)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
private def commonRestr' {Y : Scheme.{0}} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) (s : Λ) : LB Y where
  ι := C.J
  U j := (B s).U (C.idx s j)
  g j j' := (B s).g (C.idx s j) (C.idx s j')
private theorem isLB_commonRestr' {Y : Scheme.{0}} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) (s : Λ) :
    (commonRestr' C s).IsLB := {
  cover := by
    refine eq_top_iff.2 fun y _ => ?_
    obtain ⟨j, hj⟩ := C.cover y
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, (C.mem s j y).2 hj⟩
  g_self j := (C.isLB s).g_self (C.idx s j)
  cocycle i j k := (C.isLB s).cocycle (C.idx s i) (C.idx s j) (C.idx s k) }
private theorem commonRestr_iso' {Y : Scheme.{0}} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) (s : Λ) :
    LBIso (commonRestr' C s) (B s) :=
  iso_of_chart (C.isLB s)
    { idx := C.idx s
      le := fun _ _ h => h
      g := fun _ _ _ _ _ => rfl }
private theorem commonRestr_iso_tens' {Y : Scheme.{0}} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) (a b : Λ) :
    LBIso (commonRestr' C (a + b)) (tens (B a) (B b)) :=
  iso_of_chart (isLB_tens (C.isLB a) (C.isLB b))
    { idx := fun j => (C.idx a j, C.idx b j)
      le := fun j y h => by
        have h' : y ∈ C.U j := (C.mem (a + b) j y).1 h
        exact ⟨(C.mem a j y).2 h', (C.mem b j y).2 h'⟩
      g := fun y j j' hj hj' => by
        have h₁ : y ∈ C.U j := (C.mem (a + b) j y).1 hj
        have h₂ : y ∈ C.U j' := (C.mem (a + b) j' y).1 hj'
        refine (C.add a b y j j' h₁ h₂).trans ?_
        exact (tr_tens (B a) (B b) y (a := (C.idx a j, C.idx b j)) (b := (C.idx a j', C.idx b j'))
          ⟨(C.mem a j y).2 h₁, (C.mem b j y).2 h₁⟩ ⟨(C.mem a j' y).2 h₂, (C.mem b j' y).2 h₂⟩).symm }
private theorem cls_common_add {Y : Scheme.{0}} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) (a b : Λ) :
    cls (B (a + b)) (C.isLB (a + b)) = cls (B a) (C.isLB a) + cls (B b) (C.isLB b) := by
  have e₁ := (cls_eq_iff (isLB_commonRestr' C (a + b)) (C.isLB (a + b))).2 (commonRestr_iso' C (a + b))
  have e₂ := (cls_eq_iff (isLB_commonRestr' C (a + b)) (isLB_tens (C.isLB a) (C.isLB b))).2
    (commonRestr_iso_tens' C a b)
  rw [← e₁, e₂, cls_tens (C.isLB a) (C.isLB b)]
theorem cuspRatioField_eq_top_of_toroidalCompactification (hP : _root_.GlobalTheory.CovTop.Hypotheses'') (hG : GlobalTheory.Published.GrothendieckDeformation) (hN : GlobalTheory.Published.NefNumerics)
    (hSi : GlobalTheory.Published.SiegelToroidalIntegral) (hCh : GlobalTheory.Published.ToroidalChartsForFan)
    (hLie : GlobalTheory.Published.SemiAbelianLieSeminegative) (hS : GlobalTheory.Published.PointSeparationPair) (TF : TorFlag Xo c)
    (Z : Comp Xo c) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (hF : FnAlgClosed (Xo := Xo) (c := c)) (hD : 1 ≤ dimFlag Dw)
    (hpq : 1 ≤ Dw.p + Dw.q) (la : AllWt.Weight Dw)
    (hg : GapGe (((dimFlag Dw + 2).choose 2 : ℕ) : ℤ) (la - FlagTan.kap Dw))
    (hv : vanBd TF.X Z la ≤ space TF.X Z U la) :
    GlobalTheory.DegVal.ratioField (genPoint Z (cuspOn U Z (wtOf Dw la 0))) = ⊤ := by
  set L := GlobalTheory.DegVal.ratioField (genPoint Z (cuspOn U Z (wtOf Dw la 0))) with hL
  haveI := c.fin
  haveI : Countable c.F := (Module.finBasis ℚ c.F).equivFun.injective.countable
  haveI : Countable (Om Z) := TwoPoint.countable_of_fg c.F (Om Z) ((FlagDim.fnFG_fnTrdeg E H Dw l Xo c).1 Z)
  refine eq_top_iff.2 fun a _ => by_contra fun ha => ?_
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap c.F L).injective
  obtain ⟨i₁, i₂, hi, hne⟩ := TwoPoint.exists_two_embeddings L (Om Z) a (by rintro ⟨b, rfl⟩; exact ha b.2)
  have hag : ∀ b ∈ L, i₁ b = i₂ b := fun b hb => RingHom.congr_fun hi ⟨b, hb⟩
  have hV := GlobalTheory.VarFlag.isVariety₀_flag E H Dw l Xo c TF Z hF
  let M : Modif (str₀ TF.X Z) (U₀ TF.X Z) (dimFlag Dw) := Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)
  haveI : IsAffineHom M.σ := inferInstanceAs (IsAffineHom (𝟙 (Y₀ TF.X Z)))
  have hconn : GeometricallyConnected M.str := by
    have e : M.str = str₀ TF.X Z := Category.id_comp (str₀ TF.X Z)
    rw [e]
    exact hV.2.2
  obtain ⟨ω⟩ := GlobalTheory.CompHS.canId_nonempty hP.p5 E H Dw l Xo c TF.Y TF.X Z M
    (fun K _ _ y => _root_.GlobalTheory.FlagTan.kodaira_spencer_iso_flag_tangent_psi_set hP hG E H Dw l Xo c K y hpq)
  obtain ⟨F, hFg⟩ := _root_.GlobalTheory.T.cusp_germ_transfer_of_boundary hP hG E H Dw l Xo c TF Z r U hF M ω (la - FlagTan.kap Dw) la (by abel) hv
  have h : GenFrEx Xo c := (Reg.genFrEx_and_genFromTest E H Dw l Xo c).1
  obtain ⟨z, hz, hO⟩ := exists_lift_genFr M h
  have hzo : ptOf z ∈ M.off := (le_iff_ptOf_mem _ _).1 hO
  have hη : M.σ (ptOf z) ∈ U₀ TF.X Z := M.off_eq.le hzo
  have hU : ⊤ ≤ (z ≫ M.σ) ⁻¹ᵁ U₀ TF.X Z := (le_iff_ptOf_mem _ _).2 hη
  have hB := LB.isLB_pull (isLB_L₀ TF.X Z (la - FlagTan.kap Dw)) M.σ
  obtain ⟨j, hj⟩ := exists_chart (isLB_tens M.K.isLB hB) (ptOf z)
  have hj' := (le_iff_ptOf_mem z _).2 hj
  obtain ⟨i, hi₀⟩ := exists_chart (isLB_L₀ TF.X Z la) (M.σ (ptOf z))
  have hi' : ⊤ ≤ (z ≫ M.σ) ⁻¹ᵁ (L₀ TF.X Z la).U i := (le_iff_ptOf_mem _ _).2 hi₀
  obtain ⟨u, hu⟩ := hFg (ptOf z) hzo j hj i hi₀
  obtain ⟨T, hT, hTv⟩ := exists_val_cuspSec TF.X Z U la h (z ≫ M.σ) (by rw [Category.assoc]; exact hz) hU i hi'
  obtain ⟨T', hT', hval⟩ : ∃ T' : Om Z, T' ≠ 0 ∧ ∀ g, H0.val z j le_top hj' g = T' * genVal Z (F g).1 := by
    refine ⟨(Scheme.stalkClosedPointTo (R := CommRingCat.of (Om Z)) z).hom u.val * T,
      mul_ne_zero (u.isUnit.map _).ne_zero hT, fun g => ?_⟩
    rw [val_eq_stalk z j le_top hj' (memTop _) hj, hu, mul_assoc, ← hTv,
      val_eq_stalk (z ≫ M.σ) i hU hi' hη hi₀, Scheme.stalkClosedPointTo_comp]
    exact map_mul (Scheme.stalkClosedPointTo (R := CommRingCat.of (Om Z)) z).hom _ _
  let σ : c.F →+* ℂ := i₁.comp (algebraMap c.F (Om Z))
  have hσ : i₂.comp (algebraMap c.F (Om Z)) = σ := RingHom.ext fun k => (hag _ (L.algebraMap_mem k)).symm
  let ι : Fin 2 → (Om Z →+* ℂ) := ![i₁, i₂]
  have hι : ∀ n, (ι n).comp (algebraMap c.F (Om Z)) = σ := Fin.forall_fin_two.2 ⟨rfl, hσ⟩
  have hstr : z ≫ M.str = spMap (algebraMap c.F (Om Z)) := by
    show z ≫ (toFlag M ≫ flagStr TF.X) = _
    rw [← Category.assoc, hz, ptY_str]
  have hzz : spMap (ι 0) ≫ z ≠ spMap (ι 1) ≫ z := fun e => by
    letI : Algebra c.F ℂ := σ.toAlgebra
    have := eq_of_ptY_eq TF.X h Z (K := ℂ) ⟨i₁, RingHom.congr_fun (hι 0)⟩ ⟨i₂, RingHom.congr_fun (hι 1)⟩ (by
      rw [← hz, ← Category.assoc, ← Category.assoc]
      exact congrArg (· ≫ toFlag M) e)
    exact hne (congrArg AlgHom.toRingHom this)
  set std : AllWt.Weight Dw := GlobalTheory.CompHt.stdWt (Psi H) (Dw.p + Dw.q)
  set m : ℕ := (dimFlag Dw + 2).choose 2
  have hstd : GapGe 1 std := gapGe_std Dw
  have nef : ∀ w : AllWt.Weight Dw, GapGe 0 w → letI := algebraΓOfHom M.str; IsNef c.F ((L₀ TF.X Z w).pull M.σ) :=
    fun w hw => TwoPoint.nef_pull hN _ M.str M.σ hV.2.1 M.proj _ (_root_.GlobalTheory.NefWt.weight_line_bundle_isNef hP hN hLie E H Dw l Xo c TF Z hF w hw)
  obtain ⟨mu, hmu0, m', hm', hA⟩ := _root_.GlobalTheory.HSApp.hodge_bundle_ample_at_regular_point hP hN hSi hCh E H Dw l Xo c TF Z hF std hstd _ hη
  have C := (common₀ TF.X Z).pull M.σ
  have e₁ := cls_common_add C (m' • std - mu) mu
  rw [sub_add_cancel] at e₁
  replace e₁ := (cls_nsmul C m' std).symm.trans e₁
  have e₂ := cls_common_add C (m • std) (la - FlagTan.kap Dw - m • std)
  rw [add_sub_cancel] at e₂
  replace e₂ := e₂.trans (congrArg (· + _) (cls_nsmul C m std))
  have hk : ∀ n, ⊤ ≤ (spMap (ι n) ≫ z) ⁻¹ᵁ (tens M.K.bundle ((L₀ TF.X Z (la - FlagTan.kap Dw)).pull M.σ)).U j :=
    fun n => (le_iff_ptOf_mem _ _).2 (by rw [ptOf_spMap_comp]; exact hj)
  have main := fun (a : Fin 2 → ℂ) (ha : ∀ n, a n ≠ 0) =>
    TwoPoint.separate_two (TwoPoint.separatesOnSmooth_of_pair hS) hN c.F σ M.X M.str (dimFlag Dw) M.proj hconn hD M.K
      _ _ _ _ _ _ _ _ _ _ m' m (nef std (hstd.mono zero_le_one)) (nef _ (gapGe_sub_std m _ hg)) (nef mu hmu0) le_rfl hm'
      e₁ e₂ (fun n => spMap (ι n) ≫ z) hzz
      (fun n => by rw [Category.assoc, hstr, spMap_comp_ring, hι])
      (fun n s => by
        have e : (spMap (ι n) ≫ z) s = ptOf z := congrArg z (Subsingleton.elim (α := PrimeSpectrum (Om Z)) _ _)
        rw [e]
        exact AmplePull.ampleAt_pull _ _ M.σ _ (isLB_L₀ TF.X Z _) _ hA)
      (fun _ => j) hk a ha
  have hvι : ∀ n g, H0.val (spMap (ι n) ≫ z) j le_top (hk n) g = ι n (T' * genVal Z (F g).1) := fun n g => by
    rw [← hval]
    exact GlobalTheory.CuspOnTor.val_spMap (ι n) z j le_top hj' le_top (hk n) g
  by_cases h0 : ∃ g₀, genVal Z (F g₀).1 ≠ 0
  · obtain ⟨g₀, hg₀⟩ := h0
    have hn : ∀ n, ι n (T' * genVal Z (F g₀).1) ≠ 0 := fun n => (map_ne_zero _).2 (mul_ne_zero hT' hg₀)
    refine main ![(i₁ (T' * genVal Z (F g₀).1))⁻¹, -(i₂ (T' * genVal Z (F g₀).1))⁻¹]
      (Fin.forall_fin_two.2 ⟨inv_ne_zero (hn 0), neg_ne_zero.2 (inv_ne_zero (hn 1))⟩) fun g => ?_
    have e := hag (genVal Z (F g).1 / genVal Z (F g₀).1) (IntermediateField.subset_adjoin _ _ ⟨F g, F g₀, rfl⟩)
    rw [← mul_div_mul_left _ _ hT', map_div₀, map_div₀] at e
    rw [Fin.sum_univ_two, hvι, hvι]
    show (i₁ _)⁻¹ * i₁ _ + -(i₂ _)⁻¹ * i₂ _ = 0
    rw [neg_mul, ← div_eq_inv_mul, ← div_eq_inv_mul, e, add_neg_cancel]
  · push_neg at h0
    refine main (fun _ => 1) (fun _ => one_ne_zero) fun g => ?_
    simp [hvι, h0]
end Geometry
open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp GlobalTheory.DegVal GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD _root_.Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH _root_.Formalism.L2.Theta
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem cusp_values_separate_general_points : GlobalTheory.CovTop.HypothesesX → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.NadelVanishingAndNonKltDivisor → GlobalTheory.Published.Principalisation → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)), (∀ τ (a b : Fin ((T.Q.Dw j).p + (T.Q.Dw j).q)), (b : ℕ) = a + 1 → (((dimFlag (T.Q.Dw j) + 3) ^ 2 + 2 * ((T.Q.Dw j).p + (T.Q.Dw j).q) : ℕ) : ℤ) ≤ u τ a - u τ b) → ∀ Z : Comp Y.d.Xo₂ Y.d.c₂, ∃ (σ : Y.d.c₂.F →+* ℂ) (A B : Subalgebra Y.d.c₂.F (Om Z)), A.FG ∧ B.FG ∧ B ≤ A ∧ (∀ b ∈ B, b ∈ ratioField (genPoint Z (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)))) ∧ IntermediateField.adjoin Y.d.c₂.F (A : Set (Om Z)) = ⊤ ∧ (∀ b ∈ B, b ≠ 0 → ∃ x : A →+* ℂ, (∀ k : Y.d.c₂.F, x (@algebraMap Y.d.c₂.F A _ _ A.algebra k) = σ k) ∧ (∀ hb : b ∈ A, x ⟨b, hb⟩ ≠ 0) ∧ ∀ y : A →+* ℂ, (∀ k : Y.d.c₂.F, y (@algebraMap Y.d.c₂.F A _ _ A.algebra k) = σ k) → (∀ a : A, (a : Om Z) ∈ B → y a = x a) → y = x) := by
  intro hX hG hQ hSi hP _ _ D T _ j hp hq Y e o hY u hu Z
  have hf : 2 < Module.finrank ℚ D.host.E / 2 := by
    have := D.eight_le_f
    rw [D.host.finrank_E']
    omega
  have hD : 1 ≤ FlagTan.dimFlag (T.Q.Dw j) := Nat.mul_pos (by omega) (Nat.choose_pos (by omega))
  obtain ⟨TF⟩ := _root_.GlobalTheory.CompHS.TorFlagEx.nonempty_torFlag_alt hP _ _ _ _ Y.d.Xo₂ Y.d.c₂ hD
  have htop := _root_.GlobalTheory.SepCusp.cuspRatioField_eq_top_of_toroidalCompactification hP hG hQ.nef hSi hX.ks.toroidalChartsForFan hX.lie hX.sep TF Z Y.U hY.geo hD (by omega) u (gapGe_sub_kap u hu)
    (GlobalTheory.HSApp.vanBd_le_space D T.toCore j Y e o hY hf Z TF u)
  have := Y.d.c₂.fin
  have : Countable Y.d.c₂.F := (Module.finBasis ℚ Y.d.c₂.F).equivFun.injective.countable
  exact exists_fg_complexPoint _ _ ((FlagDim.fnFG_fnTrdeg _ _ _ _ Y.d.Xo₂ Y.d.c₂).1 Z) _ htop
end GlobalTheory.SepCusp
end
end

section
open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp GlobalTheory.DegVal GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_values_separate_generic_points : GlobalTheory.CovTop.HypothesesX → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.NadelVanishingAndNonKltDivisor → GlobalTheory.Published.Principalisation → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)), (∀ τ (a b : Fin ((T.Q.Dw j).p + (T.Q.Dw j).q)), (b : ℕ) = a + 1 → (((dimFlag (T.Q.Dw j) + 3) ^ 2 + 2 * ((T.Q.Dw j).p + (T.Q.Dw j).q) : ℕ) : ℤ) ≤ u τ a - u τ b) → ∀ Z : Comp Y.d.Xo₂ Y.d.c₂, ∃ (σ : Y.d.c₂.F →+* ℂ) (A B : Subalgebra Y.d.c₂.F (Om Z)), A.FG ∧ B.FG ∧ B ≤ A ∧ (∀ b ∈ B, b ∈ ratioField (genPoint Z (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)))) ∧ IntermediateField.adjoin Y.d.c₂.F (A : Set (Om Z)) = ⊤ ∧ (∀ b ∈ B, b ≠ 0 → ∃ x : A →+* ℂ, (∀ k : Y.d.c₂.F, x (@algebraMap Y.d.c₂.F A _ _ A.algebra k) = σ k) ∧ (∀ hb : b ∈ A, x ⟨b, hb⟩ ≠ 0) ∧ ∀ y : A →+* ℂ, (∀ k : Y.d.c₂.F, y (@algebraMap Y.d.c₂.F A _ _ A.algebra k) = σ k) → (∀ a : A, (a : Om Z) ∈ B → y a = x a) → y = x) := by
  first | exact @_root_.GlobalTheory.SepCusp.cusp_values_separate_general_points | exact _root_.GlobalTheory.SepCusp.cusp_values_separate_general_points | (intros; apply _root_.GlobalTheory.SepCusp.cusp_values_separate_general_points <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsCentreCuspGenericValueNeZero
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace GlobalTheory.CentreCusp
open NumberField IsDedekindDomain Module Formalism.BasicNotions _root_.Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine
  GlobalTheory.CompHt GlobalTheory.FlatCore
section Zeros
open Filter Topology
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
end Zeros
section Cancel
open Filter Topology
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}
  {Z : Comp Xo c} {G : WTZ E} {f : Rul Xo c}
end Cancel
section SlopeTestRemainingChoices
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}
end SlopeTestRemainingChoices
section General
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}
end General
section Cover
open GlobalTheory.CovTop GlobalTheory.PrincCore Formalism.MainNotions Formalism.BasicNotions.TH _root_.Formalism.L2.Theta
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {T : CoreJ D} {j : ℕ} {Y : Deep T.toCore j} {e : ℕ} {o : ℝ}
end Cover
end GlobalTheory.CentreCusp
open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp GlobalTheory.DegVal GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped ENNReal NNReal
namespace GlobalTheory.CentreCusp
theorem exists_cusp_with_generic_value_ne_zero : GlobalTheory.CovTop.HypothesesX → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.NadelVanishingAndNonKltDivisor → GlobalTheory.Published.Principalisation → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)), (∀ τ (a b : Fin ((T.Q.Dw j).p + (T.Q.Dw j).q)), (b : ℕ) = a + 1 → (((dimFlag (T.Q.Dw j) + 3) ^ 2 + 2 * ((T.Q.Dw j).p + (T.Q.Dw j).q) : ℕ) : ℤ) ≤ u τ a - u τ b) → ∀ Z : Comp Y.d.Xo₂ Y.d.c₂, ∃ f ∈ cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0), genVal Z f ≠ 0 :=
  fun _ _ _ _ _ _ _ D T hT j hp hq Y e o hY u hu Z => exists_cusp_genVal_ne_zero' D T hT j hp hq Y e o hY u hu Z
end GlobalTheory.CentreCusp
end
end

section
open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp GlobalTheory.DegVal GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_centre_cusp_generic_value_ne_zero : GlobalTheory.CovTop.HypothesesX → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.NadelVanishingAndNonKltDivisor → GlobalTheory.Published.Principalisation → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)), (∀ τ (a b : Fin ((T.Q.Dw j).p + (T.Q.Dw j).q)), (b : ℕ) = a + 1 → (((dimFlag (T.Q.Dw j) + 3) ^ 2 + 2 * ((T.Q.Dw j).p + (T.Q.Dw j).q) : ℕ) : ℤ) ≤ u τ a - u τ b) → ∀ Z : Comp Y.d.Xo₂ Y.d.c₂, ∃ f ∈ cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0), genVal Z f ≠ 0 := by
  first | exact @_root_.GlobalTheory.CentreCusp.exists_cusp_with_generic_value_ne_zero | exact _root_.GlobalTheory.CentreCusp.exists_cusp_with_generic_value_ne_zero | (intros; apply _root_.GlobalTheory.CentreCusp.exists_cusp_with_generic_value_ne_zero <;> assumption)
end
end

section
open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp GlobalTheory.DegVal GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped ENNReal NNReal
set_option autoImplicit false
namespace GlobalTheory.DegVal
private theorem exists_ne_zero_forall_complexPoint_separate'
    (B A F : Type) [CommRing B] [IsDomain B] [IsNoetherianRing B] [CommRing A] [Algebra B A]
    [Algebra.FiniteType B A] [Field F] (j₁ j₂ : A →+* F)
    (h : j₁.comp (algebraMap B A) = j₂.comp (algebraMap B A))
    (hinj : Function.Injective (j₁.comp (algebraMap B A))) (a : A) (ha : j₁ a ≠ j₂ a) :
    ∃ q : B, q ≠ 0 ∧ ∀ φ : B →+* ℂ, φ q ≠ 0 → ∃ y₁ y₂ : A →+* ℂ,
      y₁.comp (algebraMap B A) = φ ∧ y₂.comp (algebraMap B A) = φ ∧ y₁ a ≠ y₂ a := by
  classical
  letI : Algebra B F := (j₁.comp (algebraMap B A)).toAlgebra
  let J₁ : A →ₐ[B] F := { j₁ with commutes' := fun _ => rfl }
  let J₂ : A →ₐ[B] F := { j₂ with commutes' := fun b => (RingHom.congr_fun h b).symm }
  let u : F := (j₁ a - j₂ a)⁻¹
  let D : Subalgebra B F := (Subalgebra.map J₁ ⊤ ⊔ Subalgebra.map J₂ ⊤) ⊔
    Algebra.adjoin B (({u} : Finset F) : Set F)
  have hA : (⊤ : Subalgebra B A).FG := Algebra.FiniteType.out
  have hD : D.FG := ((hA.map J₁).sup (hA.map J₂)).sup (Subalgebra.fg_adjoin_finset _)
  haveI : Algebra.FiniteType B D := (Subalgebra.fg_iff_finiteType D).1 hD
  have h1 : ∀ x, J₁ x ∈ D := fun x =>
    (le_sup_left.trans le_sup_left : Subalgebra.map J₁ ⊤ ≤ D) ⟨x, trivial, rfl⟩
  have h2 : ∀ x, J₂ x ∈ D := fun x =>
    (le_sup_right.trans le_sup_left : Subalgebra.map J₂ ⊤ ≤ D) ⟨x, trivial, rfl⟩
  have hu : u ∈ D := (le_sup_right : _ ≤ D) (Algebra.subset_adjoin (by simp))
  have hBD : Function.Injective (algebraMap B D) := fun x y hxy =>
    hinj (congrArg Subtype.val hxy)
  obtain ⟨q, hq, H⟩ := GlobalTheory.exists_ne_zero_forall_complexPoint_extend B D hBD
  refine ⟨q, hq, fun φ hφ => ?_⟩
  obtain ⟨ψ, hψ⟩ := H φ hφ
  let K₁ : A →ₐ[B] D := J₁.codRestrict D h1
  let K₂ : A →ₐ[B] D := J₂.codRestrict D h2
  refine ⟨ψ.comp (K₁ : A →+* D), ψ.comp (K₂ : A →+* D), ?_, ?_, ?_⟩
  · rw [RingHom.comp_assoc, AlgHom.comp_algebraMap, hψ]
  · rw [RingHom.comp_assoc, AlgHom.comp_algebraMap, hψ]
  · intro heq
    have hone : (⟨u, hu⟩ : D) * (K₁ a - K₂ a) = 1 :=
      Subtype.ext (inv_mul_cancel₀ (sub_ne_zero.2 ha))
    have h3 := congrArg ψ hone
    have heq' : ψ (K₁ a) = ψ (K₂ a) := heq
    rw [map_mul, map_sub, heq', sub_self, mul_zero, map_one] at h3
    exact zero_ne_one h3

private theorem exists_mul_eq_of_generic_unique_complexPoint' : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (σ : K →+* ℂ) (A B : Subalgebra K Ω), A.FG → B.FG → B ≤ A → (∀ b ∈ B, b ≠ 0 → ∃ x : A →+* ℂ, (∀ k : K, x (algebraMap K A k) = σ k) ∧ (∀ hb : b ∈ A, x ⟨b, hb⟩ ≠ 0) ∧ ∀ y : A →+* ℂ, (∀ k : K, y (algebraMap K A k) = σ k) → (∀ a : A, (a : Ω) ∈ B → y a = x a) → y = x) → ∀ a ∈ A, ∃ p ∈ B, ∃ q ∈ B, q ≠ 0 ∧ a * q = p := by
  intro K Ω _ _ _ σ A B hA hB hBA H a haA
  by_contra hne
  haveI : CharZero K := ⟨fun m n h => Nat.cast_injective (R := ℂ) (by simpa using congrArg σ h)⟩
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  let L := IntermediateField.adjoin K (B : Set Ω)
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  have haL : a ∉ Set.range (algebraMap L Ω) := by
    rintro ⟨l, hl⟩
    have hmem : a ∈ L := hl ▸ l.2
    obtain ⟨r, hr, s, hs, rfl⟩ := IntermediateField.mem_adjoin_iff_div.1 hmem
    rw [Algebra.adjoin_eq] at hr hs
    apply hne
    by_cases hs0 : s = 0
    · exact ⟨0, B.zero_mem, 1, B.one_mem, one_ne_zero, by simp [hs0]⟩
    · exact ⟨r, hr, s, hs, hs0, div_mul_cancel₀ r hs0⟩
  obtain ⟨F, _, i₁, i₂, hi, hne2⟩ := GlobalTheory.T.exists_ringHom_pair_eq_on_subfield_ne_of_not_mem_range L Ω a haL
  letI : Algebra B A := (Subalgebra.inclusion hBA).toRingHom.toAlgebra
  haveI : IsScalarTower K B A := IsScalarTower.of_algebraMap_eq fun k => rfl
  haveI : Algebra.FiniteType K A := (Subalgebra.fg_iff_finiteType A).1 hA
  haveI : Algebra.FiniteType K B := (Subalgebra.fg_iff_finiteType B).1 hB
  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing K B
  haveI : Algebra.FiniteType B A := Algebra.FiniteType.of_restrictScalars_finiteType K B A
  let j₁ : A →+* F := i₁.comp A.val.toRingHom
  let j₂ : A →+* F := i₂.comp A.val.toRingHom
  have hBL : ∀ b : B, (b : Ω) = algebraMap L Ω ⟨b, IntermediateField.subset_adjoin K _ b.2⟩ := fun b => rfl
  have hj : j₁.comp (algebraMap B A) = j₂.comp (algebraMap B A) := by
    ext b
    change i₁ (b : Ω) = i₂ (b : Ω)
    rw [hBL b]
    exact congrArg (fun f : L →+* F => f _) hi
  have hinj : Function.Injective (j₁.comp (algebraMap B A)) := by
    intro b c h
    exact Subtype.ext (i₁.injective h)
  obtain ⟨q, hq, Hq⟩ := exists_ne_zero_forall_complexPoint_separate' B A F j₁ j₂ hj hinj ⟨a, haA⟩ hne2
  obtain ⟨x, hxσ, hxq, hxu⟩ := H q q.2 (fun h => hq (Subtype.ext h))
  let φ : B →+* ℂ := x.comp (algebraMap B A)
  have hφq : φ q ≠ 0 := hxq (hBA q.2)
  obtain ⟨y₁, y₂, h₁, h₂, hy⟩ := Hq φ hφq
  have key : ∀ y : A →+* ℂ, y.comp (algebraMap B A) = φ → y = x := by
    intro y hy
    refine hxu y (fun k => ?_) (fun a' ha' => ?_)
    · have e1 : algebraMap K A k = algebraMap B A (algebraMap K B k) := rfl
      rw [e1, ← hxσ k, e1]
      exact congrArg (fun f : B →+* ℂ => f (algebraMap K B k)) hy
    · have e1 : a' = algebraMap B A ⟨a', ha'⟩ := rfl
      rw [e1]
      exact congrArg (fun f : B →+* ℂ => f ⟨a', ha'⟩) hy
  exact hy (by rw [key y₁ h₁, key y₂ h₂])

theorem birOn_of_weight_gaps_large : GlobalTheory.CovTop.HypothesesX → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.NadelVanishingAndNonKltDivisor → GlobalTheory.Published.Principalisation → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)), (∀ τ (a b : Fin ((T.Q.Dw j).p + (T.Q.Dw j).q)), (b : ℕ) = a + 1 → (((dimFlag (T.Q.Dw j) + 3) ^ 2 + 2 * ((T.Q.Dw j).p + (T.Q.Dw j).q) : ℕ) : ℤ) ≤ u τ a - u τ b) → ∀ Z : Comp Y.d.Xo₂ Y.d.c₂, BirOn Y.U Z (wtOf (T.Q.Dw j) u 0) := by
  intro hX hG hQ hS hP hN hPr D T hT j hp hq Y e o hY u hu Z
  obtain ⟨f₀, hf₀, hne⟩ := _root_.GlobalTheory.T.exists_centre_cusp_generic_value_ne_zero hX hG hQ hS hP hN hPr D T hT j hp hq Y e o hY u hu Z
  obtain ⟨σ, A, B, hA, hB, hBA, hBr, hAtop, hsep⟩ := _root_.GlobalTheory.T.cusp_values_separate_generic_points hX hG hQ hS hP hN hPr D T hT j hp hq Y e o hY u hu Z
  have key := exists_mul_eq_of_generic_unique_complexPoint' _ _ σ A B hA hB hBA hsep
  refine ⟨fun h => hne ?_, eq_top_iff.2 ?_⟩
  · have := LinearMap.congr_fun h ⟨f₀, hf₀⟩
    simpa [genPoint] using this
  · rw [← hAtop, IntermediateField.adjoin_le_iff]
    intro a ha
    obtain ⟨p, hp', q, hq', hq0, hpq⟩ := key a ha
    rw [eq_div_of_mul_eq hq0 hpq]
    exact IntermediateField.div_mem _ (hBr p hp') (hBr q hq')
end GlobalTheory.DegVal
end

section
open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp GlobalTheory.DegVal GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.birOn_wtOf_of_consecutive_gap_bound : GlobalTheory.CovTop.HypothesesX → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.NadelVanishingAndNonKltDivisor → GlobalTheory.Published.Principalisation → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)), (∀ τ (a b : Fin ((T.Q.Dw j).p + (T.Q.Dw j).q)), (b : ℕ) = a + 1 → (((dimFlag (T.Q.Dw j) + 3) ^ 2 + 2 * ((T.Q.Dw j).p + (T.Q.Dw j).q) : ℕ) : ℤ) ≤ u τ a - u τ b) → ∀ Z : Comp Y.d.Xo₂ Y.d.c₂, BirOn Y.U Z (wtOf (T.Q.Dw j) u 0) := by
  first | exact @_root_.GlobalTheory.DegVal.birOn_of_weight_gaps_large | exact _root_.GlobalTheory.DegVal.birOn_of_weight_gaps_large | (intros; apply _root_.GlobalTheory.DegVal.birOn_of_weight_gaps_large <;> assumption)
end
