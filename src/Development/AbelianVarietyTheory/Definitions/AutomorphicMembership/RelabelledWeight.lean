module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TwArgs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtOfFrameEqOfPointEq

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RelabelledWeight
noncomputable section

namespace GlobalTheory.Mem.SRe

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV
  Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.MainNotions Formalism.L2.Forms NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.Top.Bl

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section PiLocalization₂

variable {B : Base} {C : Cols B} (a : Late B C) (Z : New a.D)


set_option maxHeartbeats 4000000 in
def setV : DivStage B C a.W where
  div := ((reD a.D Z).div)
  div_good := (a.V.div_good)
  jEE := (a.V.jEE)
  jEE_basis := (a.V.jEE_basis)
  jN := (a.V.jN)
  jN_basis := (a.V.jN_basis)
  Dall_eq := (a.V.Dall_eq)
  delP_eq := (a.V.delP_eq)
  nuIn := (a.V.nuIn)
  nuIn_inj := (a.V.nuIn_inj)
  nuIn_range := (a.V.nuIn_range)
  nuIn_jN := (a.V.nuIn_jN)
  nuIn_norm := (a.V.nuIn_norm)
  jEE_norm := (a.V.jEE_norm)

def reL : Late B C := ⟨a.W, setV a Z, (reStage a.st Z.Z), a.N, a.G⟩


set_option maxHeartbeats 4000000 in
def XL (X : HidaSetting a.D) : HidaSetting (reL a Z).D := (reX Z X)


set_option maxHeartbeats 4000000 in
theorem hL {X : HidaSetting a.D} (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf a.D) :
    (XL a Z X).B.I = Formalism.L2.SG.InstExistsPf.instOf (reL a Z).D := (h)


set_option maxHeartbeats 4000000 in
def gdL {X : HidaSetting a.D} (G : GoodOp X) : GoodOp (XL a Z X) := ⟨(G.Rg), (G.Rg_spec)⟩


set_option maxHeartbeats 4000000 in
def tL (t : GA a.D (a.D.sp.Y 0)) : GA (reL a Z).D ((reL a Z).D.sp.Y 0) := (t)


set_option maxHeartbeats 4000000 in
def jL {X : HidaSetting a.D} {G : GoodOp X} (j : a.D.what₂.EE ≃ₗᵢ[ℂ] EEC X G) :
    (reL a Z).D.what₂.EE ≃ₗᵢ[ℂ] EEC (XL a Z X) (gdL a Z G) := (j)


set_option maxHeartbeats 4000000 in
def SameL (F₀ : ∀ u, Forms0 a.D u) (F₁ : ∀ u, Forms0 (reL a Z).D u) : Prop := SameForms0LevelsAndValues Z F₀ ((F₁))

variable {G' : Type} [Group G'] [Fintype G'] {Pl0 T : Type} {A : FamIn a.D.what₂.LL G' Pl0 T a.D.R.m} {Ks : Type} [Field Ks]
  [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL]


set_option maxHeartbeats 4000000 in
def eL (R : RealDat a.D A Ks) (eE : a.D.what₂.EE →ₗ[ℂ] R.HE.H) :
    letI := alg (reL a Z) iK; (reL a Z).D.what₂.EE →ₗ[ℂ] (real (reL a Z) R).HE.H := (eE)


set_option maxHeartbeats 4000000 in
def SAtL (R : RealDat a.D A Ks) (F : Face a.D A) (eE : a.D.what₂.EE →ₗ[ℂ] R.HE.H) (F₁ : ∀ u, Forms0 (reL a Z).D u) : Type 1 :=
  letI := alg (reL a Z) iK; SAt (real (reL a Z) R) (face (reL a Z) F) (eL a Z R eE) F₁


set_option maxHeartbeats 4000000 in
def SAtL.pt {R : RealDat a.D A Ks} {F : Face a.D A} {eE : a.D.what₂.EE →ₗ[ℂ] R.HE.H} {F₁ : ∀ u, Forms0 (reL a Z).D u}
    (s : SAtL a Z R F eE F₁) : GA (reL a Z).D ((reL a Z).D.sp.Y 0) := letI := alg (reL a Z) iK; SAt.t s

end PiLocalization₂


set_option maxHeartbeats 4000000 in
def MvSee : Prop := ∀ {B : Base} {C : Cols B} (a : Late B C) (Z : New a.D) {G' : Type} [Group G'] [Fintype G'] {Pl0 T : Type}
    {A : FamIn a.D.what₂.LL G' Pl0 T a.D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL]
    (R : RealDat a.D A Ks) (F : Face a.D A) (X : HidaSetting a.D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf a.D)
    (t : GA a.D (a.D.sp.Y 0)), SeeAt R F X h t →
    letI := alg (reL a Z) iK; SeeAt (real (reL a Z) R) (face (reL a Z) F) (XL a Z X) (hL a Z h) (tL a Z t)


set_option maxHeartbeats 4000000 in
def MvEv : Prop := ∀ {B : Base} {C : Cols B} (a : Late B C) (Z : New a.D) {G' : Type} [Group G'] [Fintype G'] {Pl0 T : Type}
    {A : FamIn a.D.what₂.LL G' Pl0 T a.D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL]
    (R : RealDat a.D A Ks) (F : Face a.D A) (X : HidaSetting a.D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf a.D)
    (G : GoodOp X) (t : GA a.D (a.D.sp.Y 0)) (c : ℝ), EvalTieT (MP R) R.ν0 R.fd0 (EP R F) X G (iotaX X h).toMulEquiv t c →
    letI := alg (reL a Z) iK
    EvalTieT (MP (real (reL a Z) R)) (real (reL a Z) R).ν0 (real (reL a Z) R).fd0 (EP (real (reL a Z) R) (face (reL a Z) F)) (XL a Z X)
      (gdL a Z G) (iotaX (XL a Z X) (hL a Z h)).toMulEquiv (tL a Z t) c


set_option maxHeartbeats 4000000 in
def MvRowJ : Prop := ∀ {B : Base} {C : Cols B} (a : Late B C) (Z : New a.D) {G' : Type} [Group G'] [Fintype G'] {Pl0 T : Type}
    {A : FamIn a.D.what₂.LL G' Pl0 T a.D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL]
    (R : RealDat a.D A Ks) (X : HidaSetting a.D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf a.D)
    (G : GoodOp X) (t : GA a.D (a.D.sp.Y 0)) (eE : a.D.what₂.EE →ₗ[ℂ] R.HE.H) (j : a.D.what₂.EE ≃ₗᵢ[ℂ] EEC X G), RowJ R eE X h G t j →
    letI := alg (reL a Z) iK; RowJ (real (reL a Z) R) (eL a Z R eE) (XL a Z X) (hL a Z h) (gdL a Z G) (tL a Z t) (jL a Z j)

end GlobalTheory.Mem.SRe

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LinearIndependentVecC
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix
open TopologicalSpace
open Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo Formalism.L2.PjFree
open Formalism.L2.Pj (FrPt CAt embK)
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.PullbackSections
open GlobalTheory.HodgeDomain GlobalTheory.LieMet GlobalTheory.CxPts
open GlobalTheory.AllWt (Psi ptF framesOn LiesOn)
open scoped ComplexOrder

namespace GlobalTheory.TrueCx

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r j : ℕ} {Tau : Type}

section Std

variable (X : Data E r) (hj : j ≤ r) (κ : Tau ≃ X.Ψ)

def stdMat (z : Pt Tau j (r - j)) : Frame X.Ψ r := fun τ =>
  (mat (x0F X) τ * reindex (idx hj).symm (idx hj).symm (fromBlocks 1 (z (κ.symm τ)) 0 1) : Matrix (Fin r) (Fin r) ℂ)

theorem frameCo_stdMat (z : Pt Tau j (r - j)) (τ : X.Ψ) :
    frameCo X hj (stdMat X hj κ z) τ = fromBlocks 1 (z (κ.symm τ)) 0 1 := by
  show reindex _ _ (_ * (mat (x0F X) τ * _)) = _
  rw [nonsing_inv_mul_cancel_left _ _ (det_x0F X τ).isUnit]
  simp

theorem domPt_stdMat (z : Pt Tau j (r - j)) : domPt X hj κ (stdMat X hj κ z) = z := by
  funext t
  simp [domPt, frameCo_stdMat, moeb_zero]

theorem stdMat_mem (hp : X.p0 = r - j) {z : Pt Tau j (r - j)} (hz : z ∈ DomI Tau j (r - j)) :
    stdMat X hj κ z ∈ X.dom := by
  refine ExF.mem_dom_of_gramPos X fun τ => ⟨?_, ?_⟩
  · show (mat (x0F X) τ * _).det ≠ 0
    rw [det_mul, det_reindex_self, det_fromBlocks_zero₂₁]
    simpa using det_x0F X τ
  have h0 := congrArg transpose (isOrth_x0F X τ)
  rw [gram_eq_mul, diagonal_transpose, hp] at h0
  set N : Matrix (Fin j ⊕ Fin (r - j)) (Fin j ⊕ Fin (r - j)) ℂ := fromBlocks 1 (z (κ.symm τ)) 0 1 with hN
  have h1 : reindex (idx hj) (idx hj) (gram τ.1 X.Gm (mat (stdMat X hj κ z) τ))ᵀ = Nᴴ * -Jpq j (r - j) * N := by
    rw [gram_eq_mul, ← reindex_sgn hj, ← h0]
    show reindex _ _ ((mat (x0F X) τ * reindex _ _ N)ᴴ * _ * (mat (x0F X) τ * reindex _ _ N)) = _
    simp only [conjTranspose_mul, reindex_apply, conjTranspose_submatrix, ← submatrix_mul_equiv _ _ _ (idx hj).symm,
      submatrix_submatrix, Equiv.symm_symm, Equiv.self_comp_symm, submatrix_id_id, Matrix.mul_assoc]
  have h2 : (Nᴴ * -Jpq j (r - j) * N).toBlocks₂₂ = hQ (z (κ.symm τ)) := by
    simp [hN, Jpq, fromBlocks_conjTranspose, fromBlocks_neg, fromBlocks_multiply, hQ, sub_eq_neg_add]
  have h3 : X.gramPos (stdMat X hj κ z) τ = ((hQ (z (κ.symm τ))).submatrix (finCongr hp) (finCongr hp))ᵀ := by
    ext a b
    have e : ∀ a : Fin X.p0, (idx hj).symm (Sum.inr (finCongr hp a)) = Fin.castLE X.p0_le a :=
      fun a => Fin.ext (idx_symm_inr hj _)
    rw [← h2, ← h1]
    simp only [transpose_apply, submatrix_apply, toBlocks₂₂, of_apply, reindex_apply, e, Data.gramPos]
  rw [h3]
  exact (PosDef.submatrix (hz (κ.symm τ)) (finCongr hp).injective).transpose


open Classical in
def stdFrame (hp : X.p0 = r - j) (z : Pt Tau j (r - j)) : X.dom :=
  if h : z ∈ DomI Tau j (r - j) then ⟨stdMat X hj κ z, stdMat_mem X hj κ hp h⟩
  else ⟨stdMat X hj κ 0, stdMat_mem X hj κ hp fun _ => zero_mem_hcDom _ _⟩

theorem stdFrame_val (hp : X.p0 = r - j) {z : Pt Tau j (r - j)} (hz : z ∈ DomI Tau j (r - j)) :
    (stdFrame X hj κ hp z).1 = stdMat X hj κ z := by rw [stdFrame, dite_eq_left hz]

theorem domPt_stdFrame (hp : X.p0 = r - j) {z : Pt Tau j (r - j)} (hz : z ∈ DomI Tau j (r - j)) :
    domPt X hj κ (stdFrame X hj κ hp z).1 = z := by rw [stdFrame_val X hj κ hp hz, domPt_stdMat]

end Std

section Tor

variable {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  (Y : Model Xo c (RingHom.id c.F)) (σ : c.F →+* ℂ)

abbrev torC : Scheme.{0} := pullback Y.s (spMap σ)

abbrev torStr : torC Y σ ⟶ Sp ℂ := pullback.snd Y.s (spMap σ)

abbrev torPr : torC Y σ ⟶ Y.X := pullback.fst Y.s (spMap σ)

abbrev TorPts : Type := CxPts (torStr Y σ) (RingHom.id ℂ)

variable {Y σ}

variable (Y)

def ptC (y : FrPt Xo c (CAt σ)) : Sp ℂ ⟶ Xo.XF c := ptF (S := CAt σ) y

def xC (y : FrPt Xo c (CAt σ)) : Sp ℂ ⟶ Xo.X := y.x

theorem ptC_fst (y : FrPt Xo c (CAt σ)) : ptC y ≫ pullback.fst _ _ = xC y := pullback.lift_fst _ _ _

theorem ptC_snd (y : FrPt Xo c (CAt σ)) : ptC y ≫ pullback.snd _ _ = spMap σ := pullback.lift_snd _ _ _

def torPt (y : FrPt Xo c (CAt σ)) : TorPts Y σ :=
  ⟨pullback.lift (ptC y ≫ Y.j) (spMap (RingHom.id ℂ)) (by
      rw [Model.j, Category.assoc, Category.assoc, pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over,
        ← Category.assoc, ptC_snd, ← Spec.map_comp, ← Spec.map_comp]
      rfl), pullback.lift_snd _ _ _⟩

theorem torPt_pr (y : FrPt Xo c (CAt σ)) : (torPt Y y).1 ≫ torPr Y σ = ptC y ≫ Y.j := pullback.lift_fst _ _ _

abbrev LieAt (y : TorPts Y σ) : Type := TanM (y.1 ≫ torPr Y σ) Y.t.G


variable (σ) in
abbrev LieForm : Type := ∀ y : TorPts Y σ, LieAt Y y →ₗ[ℂ] LieAt Y y →ₗ⋆[ℂ] ℂ

def lieEquiv (y : FrPt Xo c (CAt σ)) : TanM (xC y) Xo.univ.t.G ≃ₗ[ℂ] LieAt Y (torPt Y y) :=
  (pushE Y.m0.toSABMap (ptC y) (ptC_fst y)).symm.trans (pushE Y.m (ptC y) (torPt_pr Y y).symm)

end Tor

section Bd

variable {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  (Y : Model Xo c (RingHom.id c.F)) {σ : c.F →+* ℂ}

variable (U : Unf Xo c σ r) (hU : IsUnf U) (e : Dw.p = j) (hσ : GoodEmb c σ) (T : Tau ≃ Psi H)


def letter (t : Tau) : Psi H := (letterAt hσ).symm (T t)


variable [Fintype Tau]


variable (B : ∀ k, BdData Tau j (r - j) (gammaU (U.X k) (le_of_isUnf U hU e) (cmEquiv U hU T k)))

variable {Y U hU e hσ T B}

end Bd

section Flat

open GlobalTheory.FlatLine GlobalTheory.AllWt

variable {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) {x : ℝ}
  (sig : ∀ (Z : Formalism.L2.Pj.Comp Xo c) (τ : Psi H), FlatSec (fun σ => (U σ).toPj) x Z τ)
  {σ : c.F →+* ℂ} (hU : IsUnf (U σ)) (hσ : GoodEmb c σ) (T : Tau ≃ Psi H)

variable {U sig hU hσ T}

end Flat

end GlobalTheory.TrueCx
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsUniqueIsCrd
noncomputable section

namespace GlobalTheory.Mem.Top.Bl.TieModel

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mem GlobalTheory.Mem.Col2 NumberField IsDedekindDomain _root_.Formalism.L2.DIV _root_.Formalism.L2.Col

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Forms

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (hX : X.Ok)
  (P : LevFam X.E X.K R.r Pr.vGs)

def frm (y : Fin ((MtildeKCSD W Ch sel mu (mtildeKOk W Ch sel mu hX)).lvlDim (g0Act W Ch sel mu (mtildeKOk W Ch sel mu hX)) P.grp P.chr) → X.K) :
    (MtildeKCSD W Ch sel mu (mtildeKOk W Ch sel mu hX)).Forms :=
  (MtildeKCSD W Ch sel mu (mtildeKOk W Ch sel mu hX)).basis.equivFun.symm
    (((MtildeKCSD W Ch sel mu (mtildeKOk W Ch sel mu hX)).lvlE (g0Act W Ch sel mu (mtildeKOk W Ch sel mu hX)) P.grp P.chr).mulVec y)

theorem isFormOf_unique {V : Type} {y : V} {x x' : MtildeV W Ch sel mu P} (h : IsFormOf W Ch sel mu hX P x y)
    (h' : IsFormOf W Ch sel mu hX P x' y) : x = x' := by
  obtain ⟨F, hF, e, rfl⟩ := h
  obtain ⟨F', hF', e', rfl⟩ := h'
  have := ((mtildeKGSD W Ch sel mu).res (mtildeKOk W Ch sel mu hX)).injective (eq_of_heq (e.trans e'.symm))
  subst this
  rfl

end Forms

section Cols

attribute [local instance] GlobalTheory.Mem.Col2.starE

variable (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (hX : X.B.fields.Ok)

end Cols

section Core

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)}

end Core

section Standard

open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links



end Standard

end GlobalTheory.Mem.Top.Bl.TieModel

end
end
