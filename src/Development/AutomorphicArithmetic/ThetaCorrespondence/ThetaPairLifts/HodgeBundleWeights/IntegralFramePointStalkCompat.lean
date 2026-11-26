module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleTensorOfNefFibresAmple
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.IsNefHodgeBundleUnitWeight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeadWeightLineNef
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroSectionWeightBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CentredPointPhiPositive

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.IntegralFramePointStalkCompat
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.FlatValZero
section Gen
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD _root_.Formalism.L2.Pj Formalism.BasicNotions
  GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.FlatCore GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}
theorem twisted_section_flat_valuation (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) (hL : Laws U x) (hFE : FlatExists U x) (Z : Comp Xo c)
    (w : Psi H → ℤ) : ∃ t : TwSec U x Z (wtOf Dw (parWt Dw w) 0), ∀ (T : CDVR) (io : c.F →+* T.Fr)
      (y : IntFr Xo c T io), (∀ a, a ≠ 0 → vV T.V (io a) = 0) → evI y (idem Z) ≠ 0 → vV T.V (evI y t.sig) = 0 := by
  have hp : HasPts U Z := GlobalTheory.FlatLine.hasPts U hL.pos hL.good hL.unf Z
  let sF : ∀ τ, FlatSec U x Z τ := fun τ => (hFE.nonempty Z τ).some
  have hK := nonempty_keySec hL
  let s := FlatSec.shift hp sF w
  have hδ := GlobalTheory.FlatTwisting.finite_sum_flDefect (Dw := Dw) (c := c) w
  refine ⟨TwSec.ofConst s (by convert hδ) (GlobalTheory.FlatTwisting.mul_sig_mem_cuspOn hK hL.unf hL.pos s) fun G hG f hf => ?_,
    fun T io y hio hZ => ?_⟩
  · have h := GlobalTheory.FlatTwisting.mul_sig_mem_cuspOn hK hL.unf hL.pos (w := -w) (s.symm.copy rfl rfl)
      (G + wtOf Dw (parWt Dw w) 0) (Even.add hG (even_wtOf _ _)) f hf
    rw [GlobalTheory.FlatTwisting.wtOf_parWt_neg, add_neg_cancel_right] at h
    exact h
  letI := io.toAlgebra
  have hLies : LiesOn Z y.1 := by
    by_contra hn
    exact hZ ((idem_mem_suppOn Z) T.Fr y.1 ((liesOff_iff Z y.1).2 hn))
  have hid : evI y (idem Z) = 1 := by
    have e := evI_mul y (idem Z) (idem Z)
    rw [idem_mul_idem] at e
    exact mul_left_cancel₀ hZ (by rw [mul_one]; exact e.symm)
  let ev : Rul Xo c →* T.Fr :=
    ⟨⟨evI y, by rw [← mul_one (evI y 1), ← hid, ← evI_mul, one_mul]⟩, evI_mul y⟩
  have hsig : ∀ τ, ev (sF τ).sig ∈ unitsV T := fun τ => by
    have hn := _root_.GlobalTheory.FlatCore.Bdry.nval_evI_eq_zero_alt hP hP.q2 E H Dw l Xo c r U x hL Z τ
      (ArchSec.ofConst (sF τ)) T io y hio hLies
    have hev0 : evI y (sF τ).sig ≠ 0 := by
      intro h0
      rw [show (ArchSec.ofConst (sF τ)).sig = (sF τ).sig from rfl, h0, nval_zero] at hn
      exact EReal.top_ne_zero hn
    refine ⟨hev0, ?_⟩
    rw [show (ArchSec.ofConst (sF τ)).sig = (sF τ).sig from rfl, nval_of_ne hev0] at hn
    have : ((vV T.V (evI y (sF τ).sig) : ℝ) / ((1 : ℕ) : ℝ) : ℝ) = 0 := by exact_mod_cast hn
    show vV T.V (evI y (sF τ).sig) = 0
    simpa using this
  have hinv : ∀ τ, ev (sF τ).inv ∈ unitsV T := fun τ => by
    have e : ev (sF τ).sig * ev (sF τ).inv = 1 := by
      rw [← map_mul, (sF τ).mul_inv]; exact hid
    have h2 : ev (sF τ).inv ≠ 0 := right_ne_zero_of_mul_eq_one e
    refine ⟨h2, ?_⟩
    have h3 := vV_mul (V := T.V) (hsig τ).1 h2
    rw [e, (hsig τ).2, zero_add, show vV T.V (1 : T.Fr) = 0 by simp [vV]] at h3
    exact h3.symm
  have hprod : ev s.sig ∈ unitsV T := by
    rw [(FlatSec.shift_spec hp sF w).1, map_mul, map_prod]
    refine (unitsV T).mul_mem (by rw [show ev (idem Z) = 1 from hid]; exact (unitsV T).one_mem)
      ((unitsV T).prod_mem fun τ _ => ?_)
    rw [(ConstSec.zpow_spec (sF τ) (-w τ)).1, map_mul, map_mul, map_pow, map_pow]
    exact (unitsV T).mul_mem (by rw [show ev (idem Z) = 1 from hid]; exact (unitsV T).one_mem)
      ((unitsV T).mul_mem ((unitsV T).pow_mem (hsig τ) _) ((unitsV T).pow_mem (hinv τ) _))
  exact hprod.2
end Gen
end GlobalTheory.FlatValZero
open GlobalTheory.FlatValZero
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.BaseWeightLineBundleIsNef
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.IsNefHodgeBundleTailWeight
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi)
open GlobalTheory.HSApp
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.NefStep
theorem isNef_hodgeBundle_tailWeight : GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.NefNumerics → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → ∀ (τ : Psi H) (k : ℕ), Dw.p ≤ k → k + 1 < Dw.p + Dw.q → letI := algebraΓOfHom (str₀ TF.X Z); IsNef c.F (L₀ TF.X Z (GlobalTheory.NefWt.tailWt τ k)) := by
  intro h _ hN E _ _ _ H Dw l Xo c TF Z _ τ k hk _
  letI := algebraΓOfHom (str₀ TF.X Z)
  rw [L₀_tailWt TF.X Z τ k hk]
  have hq := FlagMod.mult_conj (Dw := Dw) τ
  exact isNef_pull_LL_stepEx TF.X.F h hN.1 c.F (inc₀ TF.X Z) _ (by omega)
end GlobalTheory.NefStep
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeBundle_tailWeight_nef : GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.NefNumerics → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → ∀ (τ : Psi H) (k : ℕ), Dw.p ≤ k → k + 1 < Dw.p + Dw.q → letI := algebraΓOfHom (str₀ TF.X Z); IsNef c.F (L₀ TF.X Z (GlobalTheory.NefWt.tailWt τ k)) := by
  first | exact @_root_.GlobalTheory.NefStep.isNef_hodgeBundle_tailWeight | exact _root_.GlobalTheory.NefStep.isNef_hodgeBundle_tailWeight | (intros; apply _root_.GlobalTheory.NefStep.isNef_hodgeBundle_tailWeight <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.IsNefHodgeBundleHeadWeight
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi)
open GlobalTheory.HSApp
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.NefHodge
section Step
open GlobalTheory.FlagMod GlobalTheory.Reg GlobalTheory.VB GlobalTheory.LieVB
open GlobalTheory.Twist (resM)
open GlobalTheory.QCoh (pullbackSections)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {Z C : Scheme.{0}} {π : Z ⟶ Y.X} (F : Frames Y π) (g : C ⟶ Z) (σ : E →+* ℂ)
  (f : ∀ M : MChart Y, Fin M.n → Γ(Lie Y.t.G, M.U))
end Step
theorem isNef_hodgeBundle_headWeight : GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.NefNumerics → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → ∀ (τ : Psi H) (k : ℕ), k < Dw.p → letI := algebraΓOfHom (str₀ TF.X Z); IsNef c.F (L₀ TF.X Z (GlobalTheory.NefWt.headWt τ k)) := by
  intro hS _ hN E _ _ _ H Dw l Xo c TF Z _ τ k hk
  rw [NefStep.L₀_headWt TF.X Z τ k hk]
  exact isNef_stepEx hS hN.1 TF.X Z τ.1 (by rw [FlagMod.mult_of_mem τ]; exact hk)
end GlobalTheory.NefHodge
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeBundle_headWeight_nef : GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.NefNumerics → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → ∀ (τ : Psi H) (k : ℕ), k < Dw.p → letI := algebraΓOfHom (str₀ TF.X Z); IsNef c.F (L₀ TF.X Z (GlobalTheory.NefWt.headWt τ k)) := by
  first | exact @_root_.GlobalTheory.NefHodge.isNef_hodgeBundle_headWeight | exact _root_.GlobalTheory.NefHodge.isNef_hodgeBundle_headWeight | (intros; apply _root_.GlobalTheory.NefHodge.isNef_hodgeBundle_headWeight <;> assumption)
end
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
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.NefWt
private def commonRestr {Y : Scheme.{0}} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) (s : Λ) : LB Y where
  ι := C.J
  U j := (B s).U (C.idx s j)
  g j j' := (B s).g (C.idx s j) (C.idx s j')
private theorem isLB_commonRestr {Y : Scheme.{0}} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) (s : Λ) :
    (commonRestr C s).IsLB := {
  cover := by
    refine eq_top_iff.2 fun y _ => ?_
    obtain ⟨j, hj⟩ := C.cover y
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, (C.mem s j y).2 hj⟩
  g_self j := (C.isLB s).g_self (C.idx s j)
  cocycle i j k := (C.isLB s).cocycle (C.idx s i) (C.idx s j) (C.idx s k) }
private theorem commonRestr_iso {Y : Scheme.{0}} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) (s : Λ) :
    LBIso (commonRestr C s) (B s) :=
  iso_of_chart (C.isLB s)
    { idx := C.idx s
      le := fun _ _ h => h
      g := fun _ _ _ _ _ => rfl }
private theorem commonRestr_iso_tens {Y : Scheme.{0}} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) (a b : Λ) :
    LBIso (commonRestr C (a + b)) (tens (B a) (B b)) :=
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
  have e₁ := (cls_eq_iff (isLB_commonRestr C (a + b)) (C.isLB (a + b))).2 (commonRestr_iso C (a + b))
  have e₂ := (cls_eq_iff (isLB_commonRestr C (a + b)) (isLB_tens (C.isLB a) (C.isLB b))).2
    (commonRestr_iso_tens C a b)
  rw [← e₁, e₂, cls_tens (C.isLB a) (C.isLB b)]
theorem weight_line_bundle_isNef : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.NefNumerics → GlobalTheory.Published.SemiAbelianLieSeminegative → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → ∀ la : AllWt.Weight Dw, GapGe 0 la → letI := algebraΓOfHom (str₀ TF.X Z); IsNef c.F (L₀ TF.X Z la) := by
  intro hPr hNN hSA E _ _ _ H Dw l Xo c TF Z hF la hla
  letI := algebraΓOfHom (str₀ TF.X Z)
  classical
  obtain ⟨-, hproj, -⟩ := GlobalTheory.T.flagSpace_component_smooth_projective_connected E H Dw l Xo c TF Z hF
  obtain ⟨A, hA⟩ := exists_isAmpleLB_of_isProjOver hproj
  let C := common₀ TF.X Z
  let φ := AddMonoidHom.mk' (fun a => cls (L₀ TF.X Z a) (C.isLB a)) (cls_common_add C)
  have hφ : ∀ a, cls (L₀ TF.X Z a) (C.isLB a) = φ a := fun _ => rfl
  have nef0 : ∀ a, φ a = 0 → IsNef c.F (L₀ TF.X Z a) := fun a h =>
    (isNef_triv c.F _).of_cls_eq (C.isLB a) (by rw [hφ, h]; rfl)
  by_cases hN : 0 < Dw.p + Dw.q
  swap
  · refine nef0 la ?_
    have : la = 0 := funext fun τ => funext fun i => absurd i.2 (by omega)
    rw [this, map_zero]
  have key : la = _ := decomp la hla hN
  let cτ : Psi H → ℤ := fun τ => la τ ⟨Dw.p + Dw.q - 1, by omega⟩ +
      ∑ k ∈ Finset.range (Dw.p + Dw.q - 1), if Dw.p ≤ k then gap (la τ) k else 0
  let W : (Psi H × ℕ) ⊕ (Psi H × Bool) → AllWt.Weight Dw := Sum.elim (fun y : Psi H × ℕ => piece Dw y.1 y.2)
    (fun y : Psi H × Bool => unitWt y.1 (if y.2 then 1 else -1))
  have hP : ∀ x, IsNef c.F (L₀ TF.X Z (W x)) := by
    rintro (⟨τ, k⟩ | ⟨τ, b⟩)
    · show IsNef c.F (L₀ TF.X Z (piece Dw τ k))
      unfold piece
      split_ifs with h1 h2
      · exact _root_.GlobalTheory.T.hodgeBundle_headWeight_nef hSA hPr hNN E H Dw l Xo c TF Z hF τ k h2
      · exact _root_.GlobalTheory.T.hodgeBundle_tailWeight_nef hSA hPr hNN E H Dw l Xo c TF Z hF τ k (not_lt.1 h2) h1
      · exact nef0 0 (map_zero φ)
    · cases b
      · exact (_root_.GlobalTheory.T.hodgeBundle_unitWeight_nef hPr hNN E H Dw l Xo c TF Z hF τ).2
      · exact (_root_.GlobalTheory.T.hodgeBundle_unitWeight_nef hPr hNN E H Dw l Xo c TF Z hF τ).1
  refine IsNef.of_cls_eq_sum ((Finset.univ ×ˢ Finset.range (Dw.p + Dw.q - 1)).disjSum Finset.univ) hP
    (Sum.elim (fun y : Psi H × ℕ => (gap (la y.1) y.2).toNat)
      (fun y : Psi H × Bool => if y.2 then (cτ y.1).toNat else (-cτ y.1).toNat)) hA (C.isLB la) ?_
  rw [hφ]
  conv_lhs => rw [key]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_nsmul]
  rcases x with ⟨τ, k⟩ | ⟨τ, b⟩ <;> rfl
end GlobalTheory.NefWt
end
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_weight_line_bundle_is_nef : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.NefNumerics → GlobalTheory.Published.SemiAbelianLieSeminegative → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → ∀ la : AllWt.Weight Dw, GapGe 0 la → letI := algebraΓOfHom (str₀ TF.X Z); IsNef c.F (L₀ TF.X Z la) := by
  first | exact @_root_.GlobalTheory.NefWt.weight_line_bundle_isNef | exact _root_.GlobalTheory.NefWt.weight_line_bundle_isNef | (intros; apply _root_.GlobalTheory.NefWt.weight_line_bundle_isNef <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsNonzeroSectionWeightBound
section
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ThetaSteep
section Tau
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR _root_.Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open GlobalTheory.ThetaConst
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
end Tau
section Key
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor _root_.Formalism.L2.Pj GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyIntegralVal GlobalTheory.ShFam
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
end Key
section Geometry
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory _root_.Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.HSApp
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}
open GlobalTheory.ThetaConst GlobalTheory.FlatLine GlobalTheory.FlatCore GlobalTheory.AllWt in
theorem exists_theta_multiplication_rule (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ} (hL : Laws U x) (hM : 5 ^ 4 ∣ l.M)
    (Z : Comp Xo c) (s : ∀ τ, FlatSec U x Z τ) :
    ∃ f : secZ Xo c (exOf Dw ((8 * ((Dw.p + Dw.q : ℕ) : ℤ)) • GlobalTheory.CompHt.hodgeWt Dw) 0), f.1 ∈ suppOn Z ∧ f ≠ 0 ∧
      ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (φ : ℝ), (∀ a, io a ∈ (algebraMap T.V T.Fr).range) →
        (letI := io.toAlgebra; LiesOn Z y.1) → GlobalTheory.SlopeRec.HasPhi y φ → evI y f.1 ≠ 0 →
          8 * φ / 625 ≤ (vV T.V (evI y f.1) : ℝ) := by
  obtain ⟨K, hK, hKv⟩ := exists_key Xo c hL.pos hL.good
  have h : HasPts U Z := hasPts U hL.pos hL.good hL.unf Z
  have h5 : Odd 5 := by decide
  obtain ⟨x₀, hx₀⟩ := exists_isAdm Dw (R := 5) (by norm_num)
  obtain ⟨u, f, hf, hfZ⟩ := exists_isGenRule_nonzeroOn (Xo := Xo) (c := c) h5 (by norm_num) hM x₀ Z
  refine ⟨⟨thetaOn h s K f, thetaOn_mem_secZ h s hK (IsTauRule.mem_sec h5 hf)⟩, thetaOn_mem_suppOn h s K f,
    fun h0 => ((nonzeroOn_thetaOn_iff h s K f).2 hfZ).ne_zero (congrArg Subtype.val h0), fun T io y φ hio hZ hφ hne => ?_⟩
  letI := io.toAlgebra
  have hid : evI y (idem Z) = 1 := evR_idem hZ y.2.1
  let ev : Rul Xo c →* T.Fr :=
    ⟨⟨evI y, by rw [← mul_one (evI y 1), ← hid, ← evI_mul, one_mul]⟩, evI_mul y⟩
  have hio0 : ∀ a, a ≠ 0 → vV T.V (io a) = 0 := fun a ha => by
    have h1 := (mem_range_iff T _).1 (hio a)
    have h2 := (mem_range_iff T _).1 (hio a⁻¹)
    have h3 := vV_mul (V := T.V) ((map_ne_zero io).2 ha) ((map_ne_zero io).2 (inv_ne_zero ha))
    rw [← map_mul, mul_inv_cancel₀ ha, map_one, show vV T.V (1 : T.Fr) = 0 by simp [vV]] at h3
    omega
  have hs : ∀ τ, ev (s τ).sig ∈ (algebraMap T.V T.Fr).range := fun τ => by
    have h1 := _root_.GlobalTheory.T.archimedean_section_integral_frame_of_laws hP hP.q2 E H Dw l Xo c r U x hL Z τ (ArchSec.ofConst (s τ)) T io y hio0 hZ
    change nval T.V 1 (ev (s τ).sig) = 0 at h1
    by_cases h0 : ev (s τ).sig = 0
    · exact h0 ▸ zero_mem _
    rw [nval_of_ne h0, Nat.cast_one, div_one, EReal.coe_eq_zero, Int.cast_eq_zero] at h1
    exact (mem_range_iff T _).2 h1.ge
  have e : evI y (thetaOn h s K f) = evI y f ^ 8 * (ev K ^ (Dw.p + Dw.q) * ∏ τ, ev (s τ).sig ^ (4 * (Dw.p + Dw.q))) := by
    change ev _ = ev f ^ 8 * _
    rw [thetaOn, shift_sig]
    simp only [map_mul, map_pow, map_prod]
    rw [show ev (idem Z) = 1 from hid, one_mul, mul_assoc]
  have hB : ev K ^ (Dw.p + Dw.q) * ∏ τ, ev (s τ).sig ^ (4 * (Dw.p + Dw.q)) ∈ (algebraMap T.V T.Fr).range :=
    mul_mem (pow_mem (hKv T io y hio) _) (prod_mem fun τ _ => pow_mem (hs τ) _)
  change evI y (thetaOn h s K f) ≠ 0 at hne
  change _ ≤ (vV T.V (evI y (thetaOn h s K f)) : ℝ)
  rw [e] at hne ⊢
  have hf0 : evI y f ≠ 0 := fun h0 => hne (by rw [h0]; simp)
  have b1 := tau_bound y hφ h5 (by norm_num) (fun _ => hx₀.spans (by norm_num) u) hf hf0
  have b2 : (0 : ℝ) ≤ vV T.V (ev K ^ (Dw.p + Dw.q) * ∏ τ, ev (s τ).sig ^ (4 * (Dw.p + Dw.q))) := by
    exact_mod_cast (mem_range_iff T _).1 hB
  rw [vV_mul (left_ne_zero_of_mul hne) (right_ne_zero_of_mul hne),
    show vV T.V (evI y f ^ 8) = 8 * vV T.V (evI y f) by simp [vV]]
  push_cast at b1 ⊢
  linarith
variable {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c)
variable {X} in
set_option maxHeartbeats 1000000 in
theorem exists_section_of_theta_datum (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ} (hL : FlatCore.Laws U x)
    (hM : 5 ^ 4 ∣ l.M) (TF : TorFlag Xo c) (s : ∀ τ, FlatLine.FlatSec U x Z τ)
    (hdeg : ∀ y ∈ (U₀ TF.X Z : Set (Y₀ TF.X Z))ᶜ, ∀ ν, Centred y ν → ∃ φ : ℝ, 0 < φ ∧ PhiAt TF.X Z y ν φ) :
    ∃ θ : H0 (str₀ TF.X Z) (L₀ TF.X Z ((8 * ((Dw.p + Dw.q : ℕ) : ℤ)) • GlobalTheory.CompHt.hodgeWt Dw)) ⊤, θ ≠ 0 ∧
      ∀ (y : Y₀ TF.X Z) ν, Centred y ν → ∀ φ : ℝ, PhiAt TF.X Z y ν φ → ∀ j hj (m : ℤ),
        ν (H0.germ j y (memTop y) hj θ) = ((Multiplicative.ofAdd (-m) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) →
          8 * φ / 625 ≤ (m : ℝ) := by
  obtain ⟨f, hfZ, hf0, hf⟩ := _root_.GlobalTheory.ThetaSteep.exists_theta_multiplication_rule hP hL hM Z s
  obtain ⟨hs, -, hc⟩ := GlobalTheory.VarFlag.isVariety₀_flag _ _ _ _ _ _ TF Z hL.geo
  haveI := hs
  haveI := hc
  haveI : Smooth (str₀ TF.X Z) := SmoothOfRelativeDimension.smooth (FlagTan.dimFlag Dw) _
  haveI := GlobalTheory.isIntegral_of_smooth_of_geometricallyConnected (str₀ TF.X Z)
  haveI : IsLocallyNoetherian (Y₀ TF.X Z) := LocallyOfFiniteType.isLocallyNoetherian (str₀ TF.X Z)
  have hN : Geo.Tor.IsNormalScheme (Y₀ TF.X Z) := fun y => by
    obtain ⟨_, _⟩ := TF.X.normal (inc₀ TF.X Z y)
    let e := (asIso ((inc₀ TF.X Z).stalkMap y)).commRingCatIsoToRingEquiv
    exact ⟨e.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e⟩
  obtain ⟨θ, hθ⟩ := exists_extension hN (isLB_L₀ TF.X Z _) (dense_U₀ TF.X Z).nonempty (sec₀ TF.X Z _ f)
    fun y hy _ j hj => by
      obtain ⟨ν, hν⟩ := exists_centred y
      obtain ⟨_, -, T, io, y', g, ρ, φT, hρ, hφT, -, hpt, hval⟩ := hdeg y hy ν hν
      obtain ⟨g1, g2⟩ := local_injective_of_centred hν T g ρ hρ hval
      refine ⟨T, g, g1, g2, fun hO hi => ?_⟩
      obtain ⟨a1, a2, -, a4⟩ := through_point TF.X Z y T io y' g hpt
      obtain ⟨u, hu⟩ := a4 _ f j hj hO hi
      rw [hu]
      refine mul_mem ⟨_, rfl⟩ ?_
      by_cases h0 : evI y' f.1 = 0
      · exact h0 ▸ zero_mem _
      have b1 := hf T io y' φT a1 a2 hφT h0
      have b2 := hφT.nonneg
      refine (mem_range_iff T _).2 ?_
      have : (0 : ℝ) ≤ vV T.V (evI y' f.1) := by linarith
      exact_mod_cast this
  refine ⟨θ, fun h0 => hf0 (eq_zero_of_sec₀ TF.X Z hfZ (by rw [← hθ, h0, map_zero])), fun y ν hν φ hφ j hj m hm => ?_⟩
  obtain ⟨T, io, y', g, ρ, φT, hρ, hφT, rfl, hpt, hval⟩ := hφ
  obtain ⟨-, g2⟩ := local_injective_of_centred hν T g ρ hρ hval
  obtain ⟨a1, a2, a3, a4⟩ := through_point TF.X Z y T io y' g hpt
  have hi := top_le_stalkPt y ((algebraMap T.V T.Fr).comp g) _ hj
  obtain ⟨u, hu⟩ := a4 _ f j hj a3 hi
  rw [← hθ, val_restr_pt le_top _ j (top_le_stalkPt y _ ⊤ (memTop y)), val_stalkPt y j (memTop y) hj,
    RingHom.comp_apply] at hu
  have hne : ν (H0.germ j y (memTop y) hj θ) ≠ 0 := hm ▸ WithZero.coe_ne_zero
  have hg0 : algebraMap T.V T.Fr (g (H0.germ j y (memTop y) hj θ)) ≠ 0 := fun h => hne (by
    rw [(injective_iff_map_eq_zero _).1 g2 _ ((injective_iff_map_eq_zero _).1 (IsFractionRing.injective T.V T.Fr) _ h),
      map_zero])
  have hv := hval _ hne
  rw [hu] at hg0 hv
  rw [hm, vV_mul (left_ne_zero_of_mul hg0) (right_ne_zero_of_mul hg0), vV_unit, zero_add,
    show WithZero.log ((Multiplicative.ofAdd (-m) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) = -m from rfl] at hv
  have b1 := mul_le_mul_of_nonneg_left (hf T io y' φT a1 a2 hφT (right_ne_zero_of_mul hg0)) hρ.le
  push_cast at hv
  linarith
end Geometry
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory _root_.Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
end GlobalTheory.ThetaSteep
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
end
end
