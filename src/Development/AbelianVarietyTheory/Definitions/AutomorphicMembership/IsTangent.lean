module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameDegreeZeroFormsSelf
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftMatrixComputesLiftRational
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanGoodEqMj

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTangent
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter MeasureTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.ProjVar Formalism.BasicNotions

namespace GlobalTheory.TrueGeo

variable {F : Type} [Field F] [NumberField F] (Y : Var F) (E : Type) [Field E] [NumberField E] [Algebra F E] {n : ℕ}
  (w : Fin n → Y.Fn) (c : Fin Y.dim → Fin n → 𝓞 E)

def GeomPt : Type :=
  {y : Sp (AlgebraicClosure E) ⟶ Y.X // y ≫ Y.str = spMap ((algebraMap E (AlgebraicClosure E)).comp (algebraMap F E))}

def GenAt (x : Y.X) (k : Fin n) : Prop := w k ≠ 0 ∧ ∀ l, RegAt x (w l / w k)

def coef (i : Fin Y.dim) (l : Fin n) : AlgebraicClosure E := algebraMap E _ (c i l : E)

def cutSet : Set (GeomPt Y E) :=
  {y | ∀ k, GenAt Y w (below y.1) k → ∀ i, ∑ l, coef Y E c i l * valAt y.1 (w l / w k) = 0}

def IsTangent (y : GeomPt Y E) (δ : Y.X.presheaf.stalk (below y.1) →+ AlgebraicClosure E) : Prop :=
  (∀ a b, δ (a * b) = (Scheme.stalkClosedPointTo y.1).hom a * δ b + (Scheme.stalkClosedPointTo y.1).hom b * δ a) ∧
    ∀ (a : Y.X.presheaf.stalk (below y.1)) (t : F), algebraMap _ Y.Fn a = algebraMap F Y.Fn t → δ a = 0

def ReducedAt (y : GeomPt Y E) : Prop :=
  ∀ k, GenAt Y w (below y.1) k → ∀ u : Fin n → Y.X.presheaf.stalk (below y.1),
    (∀ l, algebraMap _ Y.Fn (u l) = w l / w k) → ∀ δ, IsTangent Y E y δ →
      (∀ i, ∑ l, coef Y E c i l * δ (u l) = 0) → δ = 0

def cutGood (bd : Y.Cl) : Prop :=
  (∀ x, ∃ k, GenAt Y w x k) ∧ (cutSet Y E w c).Finite ∧
    ∀ y ∈ cutSet Y E w c, ReducedAt Y E w c y ∧ below y.1 ∉ bd

def cutHt {C : CxSt F} (A : Adl C Y) : ℝ := ∑ᶠ y ∈ cutSet Y E w c, A.ht (below y.1)

def cutOrd (Δ : Y.Dv) (f : Y.Fn) : ℕ :=
  sSup {a : ℕ | ∀ y ∈ cutSet Y E w c, ∃ b ∈ IsLocalRing.maximalIdeal (Y.X.presheaf.stalk (below y.1)) ^ a,
    algebraMap _ Y.Fn b = f * (eqn Δ (below y.1) : Y.Fn)}

def cutSt [StarRing F] (C : CxSt F) : CutSt C where
  cutGood := fun Y bd E _ _ _ _ w c => cutGood Y E w c bd
  cutHt := fun Y A E _ _ _ _ w c => cutHt Y E w c A
  cutOrd := fun Y E _ _ _ _ w c Δ f => cutOrd Y E w c Δ f

end GlobalTheory.TrueGeo
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MSmoothOfWeightIffIsCInf
section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CxStage
set_option autoImplicit false

noncomputable section

open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.ProjVar.Var

namespace GlobalTheory.ProjVar

def cxStage (F : Type) [Field F] [NumberField F] : TrueGeo.CxSt F where
  borel _ _ := inferInstance
  vol := vol
  FnC := FnC
  cx := cx
  cx_smul := cx_smul
  Met := Met
  mAdd Y σ Δ Δ' := mAdd Y σ Δ Δ'
  mPow Y σ Δ := mPow Y σ Δ
  fsMet Y σ Δ := fsMet Y σ Δ
  pn Y σ Δ := pn Y σ Δ
  pnK Y σ Δ := pnK Y σ Δ
  mSmooth Y σ Δ := mSmooth Y σ Δ
  mPsh Y σ Δ := mPsh Y σ Δ
  redZero Y σ Δ := redZero Y σ Δ
  agreeOn Y σ Δ := agreeOn Y σ Δ
  resNorm Y σ Δ := Var.resNorm Y σ Δ
  regOn Y σ Δ := regOn Y σ Δ
  ofWeight Y σ Δ L r := Var.ofWeight Y σ Δ L r
  pn_ofWeight Y σ Δ L r h φ f y i hi _ := by rw [Var.pn_ofWeight h φ (mem_ptsIn.2 hi), fval_cx]
  pn_mAdd Y σ Δ Δ' m m' f f' y h h' := by
    rw [map_mul, Var.pn_mAdd (secReg_cx_iff.2 h) (secReg_cx_iff.2 h')]
  pn_mPow Y σ Δ k m f y h := by rw [map_pow, Var.pn_mPow (secReg_cx_iff.2 h.regularAt)]
  pn_mul Y σ Δ m a f y ha h := by
    rw [map_mul, Var.pn_mul (regC_cx_iff.2 ha) (secReg_cx_iff.2 h), val_cx]
  pn_fs Y σ Δ ι κ _ _ b X f y g hg hb _ _ := by
    have e (k) := hasVal_sum_smul (y := y) hg (fun i => secReg_cx_of_mem (hb i) y) fun i => X i k
    rw [pn_fsMet (fun k => (secReg_iff hg).2 (e k).regC) hg, fval_cx]
    simp only [fval, fun k => (e k).val_eq, ← map_mul, val_cx]

end GlobalTheory.ProjVar
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.Cartier.CartierDiv GlobalTheory.ProjVar GlobalTheory.ProjVar.Var GlobalTheory.CxPts Formalism.BasicNotions

namespace GlobalTheory.ProjVar.Var

variable {F : Type} [Field F] {Y : Var F} {σ : F →+* ℂ} {Δ : Y.Dv}

end GlobalTheory.ProjVar.Var

namespace GlobalTheory.TrueGeo

def cxSt (F : Type) [Field F] [NumberField F] : CxSt F := ProjVar.cxStage F

variable {F : Type} [Field F] [NumberField F]

variable {Y : Var F} {σ : F →+* ℂ} {Δ Δ' : Y.Dv}

end GlobalTheory.TrueGeo
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AevalDualModel
set_option autoImplicit false
noncomputable section
open MvPolynomial GlobalTheory.FlagBundle
open scoped Matrix
namespace GlobalTheory.GoodMetric.PolyRep
variable {ι : Type} {m : ι → ℕ}


set_option autoImplicit false in
theorem _root_.GlobalTheory.GoodMetric.PolyRep.lie_proj_model [Fintype ι] (τ : ι) {R : Type} [CommRing R] (A : _root_.GlobalTheory.FlagBundle.Mat m R) : (_root_.GlobalTheory.GoodMetric.PolyRep.proj m τ).lie A = A τ := by
  classical
  ext i j
  simp [_root_.GlobalTheory.GoodMetric.PolyRep.lie, _root_.GlobalTheory.GoodMetric.PolyRep.proj, pderiv_X, Pi.single_apply]
  rfl

set_option autoImplicit false in
private lemma aeval_dualNumber_inl_add_inr {σ : Type} [Fintype σ] {R : Type} [CommRing R]
    (x y : σ → R) (p : MvPolynomial σ ℤ) :
    aeval (fun v => (TrivSqZeroExt.inl (x v) + TrivSqZeroExt.inr (y v) : DualNumber R)) p
      = TrivSqZeroExt.inl (aeval x p) + TrivSqZeroExt.inr (∑ v, aeval x (pderiv v p) * y v) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => ext <;> simp
  | add p q hp hq =>
    rw [map_add (f := _), hp, hq]
    ext <;> simp [Finset.sum_add_distrib, add_mul]
  | mul_X p v hp =>
    rw [map_mul, hp, aeval_X]
    ext
    · simp
    · simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add,
        TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr,
        Derivation.leibniz, pderiv_X, smul_eq_mul, map_add, map_mul, aeval_X, add_mul,
        Finset.sum_add_distrib]
      simp [Pi.single_apply, Finset.mul_sum, Finset.sum_mul, mul_comm, mul_left_comm, add_comm]


set_option autoImplicit false in
theorem _root_.GlobalTheory.GoodMetric.PolyRep.ev_dual_model [Fintype ι] (ρ : _root_.GlobalTheory.GoodMetric.PolyRep m) {R : Type} [CommRing R] (A : _root_.GlobalTheory.FlagBundle.Mat m R) (i j : Fin ρ.M) :
    ρ.ev (R := DualNumber R) (fun τ => Matrix.of fun a b =>
        TrivSqZeroExt.inl ((1 : _root_.GlobalTheory.FlagBundle.Mat m R) τ a b) + TrivSqZeroExt.inr (A τ a b)) i j
      = TrivSqZeroExt.inl ((1 : Matrix (Fin ρ.M) (Fin ρ.M) R) i j) + TrivSqZeroExt.inr (ρ.lie A i j) := by
  have h1 := congrFun (congrFun (ρ.one R) i) j
  simp only [_root_.GlobalTheory.GoodMetric.evEnt, Matrix.map_apply] at h1
  simp only [_root_.GlobalTheory.GoodMetric.PolyRep.ev, _root_.GlobalTheory.GoodMetric.evEnt, Matrix.map_apply, Matrix.of_apply,
    _root_.GlobalTheory.GoodMetric.PolyRep.lie]
  refine (aeval_dualNumber_inl_add_inr (fun v : _root_.GlobalTheory.GoodMetric.EntIx m => (1 : _root_.GlobalTheory.FlagBundle.Mat m R) v.1 v.2.1 v.2.2)
    (fun v : _root_.GlobalTheory.GoodMetric.EntIx m => A v.1 v.2.1 v.2.2) _).trans ?_
  rw [h1]

end GlobalTheory.GoodMetric.PolyRep
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ClosureImageSpan
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3.MjCoord

theorem closure_image_span {K : Type} [Field K] [NumberField K] {σ : K →+* ℂ} {V H : Type} [AddCommGroup V]
    [Module (𝓞 K) V] [AddCommGroup H] [Module ℂ H] (f : V →+ H) (hfs : ∀ (b : 𝓞 K) (x : V), f (b • x) = σ (b : K) • f x)
    (X : Set V) :
    AddSubgroup.closure {y | ∃ a : 𝓞 K, ∃ x ∈ f '' X, y = σ (a : K) • x} =
      AddSubgroup.closure {y | ∃ a : 𝓞 K, ∃ x ∈ f '' (Submodule.span (𝓞 K) X : Set V), y = σ (a : K) • x} := by
  set C := AddSubgroup.closure {y | ∃ a : 𝓞 K, ∃ x ∈ f '' X, y = σ (a : K) • x}
  have stab : ∀ (b : 𝓞 K), ∀ z ∈ C, σ (b : K) • z ∈ C := by
    intro b z hz
    induction hz using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, x, hx, rfl⟩ := hy
      exact AddSubgroup.subset_closure ⟨b * a, x, hx, by rw [smul_smul, ← map_mul]; norm_cast⟩
    | zero => rw [smul_zero]; exact C.zero_mem
    | add _ _ _ _ h1 h2 => rw [smul_add]; exact C.add_mem h1 h2
    | neg _ _ h1 => rw [smul_neg]; exact C.neg_mem h1
  have key : ∀ x ∈ Submodule.span (𝓞 K) X, f x ∈ C := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact AddSubgroup.subset_closure ⟨1, f x, ⟨x, hx, rfl⟩, by simp⟩
    | zero => rw [map_zero]; exact C.zero_mem
    | add _ _ _ _ h1 h2 => rw [map_add (f := _)]; exact C.add_mem h1 h2
    | smul b x _ h => rw [hfs]; exact stab b _ h
  apply le_antisymm
  · refine AddSubgroup.closure_mono ?_
    rintro _ ⟨a, _, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨a, _, ⟨x, Submodule.subset_span hx, rfl⟩, rfl⟩
  · rw [AddSubgroup.closure_le]
    rintro _ ⟨a, _, ⟨x, hx, rfl⟩, rfl⟩
    rw [← hfs]
    exact key _ (Submodule.smul_mem _ a hx)

theorem majAt_self {K : Type} [Field K] [NumberField K] {n : ℕ} (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ)
    (v : InfinitePlace K) (x : Fin n → K) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X v x x =
      ((Formalism.HermitianLatticesTheory.cnorm (Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K (Fin n)) X v x) ^ 2 : ℝ) : ℂ) := by
  rw [Formalism.HermitianLatticesTheory.cnorm, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), Formalism.HermitianLatticesTheory.majAt]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul']

theorem norm_w0C_sq {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A) (b : Bool)
    (hk : X.KForm b) (he : X.EWnorm b) (j : Bs.J) (x : Fin (X.dW b j) → K) :
    ‖X.w0C b j (cpt Bs.v0.embedding x)‖ ^ 2 =
      X.nP b * Formalism.HermitianLatticesTheory.cnorm (Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K _) (X.XW b j) Bs.v0 x) ^ 2 := by
  have h1 := majAt_gram (X.XW b j) Bs.v0 (X.bW b j Bs.v0) (hk j Bs.v0).1 rfl x x
  have h2 := he j (lin (X.bW b j Bs.v0) (cpt Bs.v0.embedding x)) (lin (X.bW b j Bs.v0) (cpt Bs.v0.embedding x))
  rw [← h1, majAt_self, inner_self_eq_norm_sq_to_K] at h2
  have h3 : ((‖X.w0C b j (cpt Bs.v0.embedding x)‖ ^ 2 : ℝ) : ℂ) =
      ((X.nP b * Formalism.HermitianLatticesTheory.cnorm (Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K _) (X.XW b j) Bs.v0 x) ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_mul, ← h2, Complex.ofReal_pow]
    rfl
  exact Complex.ofReal_injective h3

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3}
  {cG : G0 R.Pg D.R.r ≃* G0g D.nd} {X0 : BaseLevelRowSide D} {Y : Read (A3 := A3) R.toRealDat F.lv2 X0}


set_option maxHeartbeats 1000000 in
theorem eW_jW_eq (Z : ReadL R F X0 Y) (i : Fin D.R.m) (y) :
    Y.mj.eW i (Z.jW i y) = GlobalTheory.Mem.LiftTheta.goodForm R.toRealDat F.lv2 false i y :=
  (Z.jW_read i y).trans (congrArg ((R.FW i).j (sg0 D A3.A)) (Fintype.linearCombination_apply _ _ _))

theorem eW_inj (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (i : Fin D.R.m) : Function.Injective (Y.mj.eW i) :=
  GlobalTheory.Mem.LiftForms.inj_of_norm_sq _ (RealDat.nP_pos (F := F.lv2) false) (Y.mj.eW_norm i)

theorem jW_basis (Z : ReadL R F X0 Y) (hH : Holds R F) (i : Fin D.R.m) :
    LinearIndependent ℂ (fun k => Z.jW i (Pi.single k 1)) ∧
      Submodule.span ℂ (Set.range fun k => Z.jW i (Pi.single k 1)) = ⊤ := by
  have he := eW_inj Y i
  have hc : (Y.mj.eW i ∘ fun k => Z.jW i (Pi.single k 1)) = fun k =>
      GlobalTheory.Mem.LiftTheta.goodForm R.toRealDat F.lv2 false i (Pi.single k 1) :=
    funext fun k => eW_jW_eq Z i _
  refine ⟨LinearIndependent.of_comp (Y.mj.eW i) ?_, ?_⟩
  · rw [hc]; exact GlobalTheory.Mem.LiftTheta.goodForm_li R.toRealDat F.lv2 hH.prim.unif false i
  · apply Submodule.map_injective_of_injective he
    rw [Submodule.map_top, Submodule.map_span, ← Set.range_comp, hc]
    exact (GlobalTheory.Mem.LiftTheta.goodForm_span R.toRealDat F.lv2 false i).trans
      ((hH.aux.levelW false i _).trans (Y.mj.eW_range i).symm)

theorem chiKs (hP : Pins R F cG) (i : Fin D.R.m) : (R.FW i).ChiKs := by
  intro g
  have hL := hP.char.base.lev
  have h : ((Formalism.IndefR.FWT.chiC R.toRealDat i g : ℂˣ) : ℂ) ∈ (D.what₂.embLL.comp (algebraMap Ks D.what₂.LL)).fieldRange := by
    unfold Formalism.IndefR.FWT.chiC
    rw [Units.coe_prod]
    refine prod_mem fun PP _ => ?_
    refine GlobalTheory.ChiDetValues.res_mem _ _ _ (hL.mu0 i) (fun x hx => ?_) _ _ (hL.chi i _ PP.2) _
    obtain ⟨y, hy⟩ := hP.keep.valKs i x hx
    exact ⟨y, hy.symm⟩
  obtain ⟨y, hy⟩ := h
  exact ⟨y, D.what₂.embLL.injective (hy.trans ((Units.coe_prod _ _).trans (hP.char.base.grp.chiW i g).symm))⟩


set_option maxHeartbeats 1000000 in
theorem jW_lat (Z : ReadL R F X0 Y) (hP : Pins R F cG) (hH : Holds R F) (i : Fin D.R.m) :
    OLatTie D.what₂.embLL (D.what₂.MjLat ((i : ℕ) + 1)) (Z.jW i) ((s0Of R F).M i) := by
  have he := eW_inj Y i
  have hli := (jW_basis Z hH i).1
  have hej := eW_jW_eq Z i
  have hI := hH.aux.integral i
  have hspan := GlobalTheory.GoodLatDescent.span_MK_good (R.FW i) hI.1 (fun g f => (hI.2.2 g f).1)
    (chiKs hP i) F.P0 F.ψ0⁻¹ (fun g => (idemOf A3.A.X).coeff g)
    (fun p => ?_) hP.keep.levKs.2
  swap
  · obtain ⟨y, hy⟩ := hP.keep.levKs.1 p
    exact ⟨y⁻¹, by rw [map_inv₀, hy, MonoidHom.inv_apply, Units.val_inv_eq_inv_val]; rfl⟩
  have hsg : sg0 D A3.A = D.what₂.embLL := RingHom.ext fun a => by rw [sg0, sgAt_mk _ R.hv0]
  have himg : Y.mj.eW i '' (D.what₂.MjLat ((i : ℕ) + 1)).carrier =
      (R.FW i).j (sg0 D A3.A) '' {y | y ∈ (R.FW i).MK ∧ y ∈ (R.FW i).Wgood F.P0 F.ψ0⁻¹ (fun g => (idemOf A3.A.X).coeff g)} := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨y, hy1, hy2, e⟩ := (Y.mj.eW_lat i x).1 hx
      exact ⟨y, ⟨hy1, hy2⟩, e.symm⟩
    · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
      have hyM : y ∈ (R.FW i).Mj F.P0 F.ψ0⁻¹ (fun g => (idemOf A3.A.X).coeff g) := by
        rw [← hspan]; exact Submodule.subset_span ⟨hy1, hy2⟩
      obtain ⟨c, -, hcy⟩ := (GlobalTheory.Mem.LiftTheta.mem_image_iff R.toRealDat F.lv2 false i _).1 ⟨y, hyM, rfl⟩
      exact ⟨Z.jW i c, (Y.mj.eW_lat i _).2 ⟨y, hy1, hy2, (hej c).trans hcy⟩, (hej c).trans hcy⟩
  refine GlobalTheory.Mem.LiftTheta.oLatTie_of_closure (fun a => ⟨⟨D.what₂.OtoLL a, D.O_int a⟩, rfl⟩) _ (Y.mj.eW i) he (Z.jW i)
    (GlobalTheory.Mem.LiftTheta.semi_injective _ hli) _
    ((R.FW i).j (sg0 D A3.A) '' ((R.FW i).Mj F.P0 F.ψ0⁻¹ (fun g => (idemOf A3.A.X).coeff g) : Set _)) (fun y => ?_) ?_
  · refine (GlobalTheory.Mem.LiftTheta.mem_image_iff R.toRealDat F.lv2 false i y).trans ?_
    exact ⟨fun ⟨x, hx, h⟩ => ⟨x, hx, (hej x).trans h⟩, fun ⟨x, hx, h⟩ => ⟨x, hx, (hej x).symm.trans h⟩⟩
  · rw [himg, ← hspan]
    exact closure_image_span (σ := D.what₂.embLL) ((R.FW i).j (sg0 D A3.A)).toAddMonoidHom
      (fun b x => by
        rw [← hsg]
        show (R.FW i).j _ (b • x) = _
        rw [← algebraMap_smul D.what₂.LL b x, map_smulₛₗ]
        rfl) _


set_option maxHeartbeats 1000000 in
theorem jW_norm (Z : ReadL R F X0 Y) (hH : Holds R F) (i : Fin D.R.m) (x : Fin ((s0Of R F).dW i) → D.what₂.LL) :
    Formalism.HermitianLatticesTheory.cnorm (Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun D.what₂.LL _) ((s0Of R F).XW i) (InfinitePlace.mk D.what₂.embLL) x) =
      ‖Z.jW i x‖ := by
  have h1 := norm_w0C_sq (R.toCx3 F) false (RealDat3.kForm_of hH.prim.unif false) (RealDat3.ewNorm false) i x
  have h2 : (R.toCx3 F).w0C false i (cpt A3.A.v0.embedding x) =
      Tw.mk (twAt D.what₂.embLL A3.A.v0) (GlobalTheory.Mem.LiftTheta.goodForm R.toRealDat F.lv2 false i x) :=
    GlobalTheory.Mem.LiftTheta.liftWeight_complexPoint_eq_twist R.toRealDat F.lv2 false i x
  have h3 : ‖(R.toCx3 F).w0C false i (cpt A3.A.v0.embedding x)‖ = ‖Y.mj.eW i (Z.jW i x)‖ :=
    (congrArg norm h2).trans (congrArg norm (eW_jW_eq Z i x)).symm
  have h4 := Y.mj.eW_norm i (Z.jW i x)
  have h5 : RealDat.nP F.lv2 false *
      Formalism.HermitianLatticesTheory.cnorm (Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun D.what₂.LL _) ((s0Of R F).XW i) A3.A.v0 x) ^ 2 =
        RealDat.nP F.lv2 false * ‖Z.jW i x‖ ^ 2 := by
    rw [← h4, ← h3]
    exact h1.symm
  rw [← R.hv0]
  exact (sq_eq_sq₀ (Real.sqrt_nonneg _) (norm_nonneg _)).1
    (mul_left_cancel₀ (RealDat.nP_pos (F := F.lv2) false).ne' h5)

end GlobalTheory.Mem.R3.MjCoord

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EHHre
noncomputable section

namespace GlobalTheory.Mem.SRe

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.Forms Formalism.L2.SG.TermOp Formalism.L2.SG.Full

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (Z : New D)


set_option maxHeartbeats 4000000 in
def reTR {X : HidaSetting D} (T : TypedRed X) : TypedRed (reX Z X) := { T with }


set_option maxHeartbeats 4000000 in
def reCS {X : HidaSetting D} {u : D.what₂.Word} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (c : ColSys X u what₂) :
    ColSys (reX Z X) u what₂ := { c with }


set_option maxHeartbeats 4000000 in
def eHHre (X : HidaSetting D) : HHX X ≃ₗᵢ[ℂ] HHX (reX Z X) := LinearIsometryEquiv.refl ℂ (HHX X)

end GlobalTheory.Mem.SRe

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ColDictLReTr
noncomputable section

namespace GlobalTheory.Mem.SRe

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.Forms Formalism.L2.SG.TermOp Formalism.L2.SG.Full

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (Z : New D)


set_option maxHeartbeats 4000000 in
def reTr {X : HidaSetting D} {u : D.what₂.Word} {F : Forms0 D u} {F' : Forms0 (reD D Z) u} (T : Transport X u F)
    (hy : F'.cls0.y = F.cls0.y) (he : F'.val0.eY = F.val0.eY) : Transport (reX Z X) u F' where
  wt := T.wt
  wt_isom := T.wt_isom
  wt_e := T.wt_e
  wt_f := T.wt_f
  weight_z := T.weight_z
  ιA := T.ιA
  ιA_rat := T.ιA_rat
  ιA_int := T.ιA_int
  h0 := T.h0
  hc := T.hc
  hc_rep := fun c => by rw [hy]; exact T.hc_rep c
  J := T.J
  J_eqv := T.J_eqv
  J_val := T.J_val
  J_isom := fun c ξ η => by rw [he]; exact T.J_isom c ξ η


set_option maxHeartbeats 4000000 in
theorem colDictL_reTr {X : HidaSetting D} {u : D.what₂.Word} {F : Forms0 D u} {F' : Forms0 (reD D Z) u} (T : Transport X u F)
    (hy : F'.cls0.y = F.cls0.y) (he : F'.val0.eY = F.val0.eY) (hK : X.LevelSubgroupCharacter) (x : Cu X u hK) :
    colDictL (reX Z X) (reTr Z T hy he) hK x = colDictL X T hK x := by
  funext c z
  show T.J (shP X u x.1 (T.hc c)) (F'.val0.eY z) = T.J (shP X u x.1 (T.hc c)) (F.val0.eY z)
  rw [he]
  rfl

end GlobalTheory.Mem.SRe

end
end
