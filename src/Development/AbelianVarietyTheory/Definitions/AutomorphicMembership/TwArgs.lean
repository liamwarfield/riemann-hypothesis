module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmHostRootComplexEqPmSqrt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayFieldLeAndExistsBase
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFormsWeightEqParameterSubRho

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TwArgs
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
  {L : SizeData₂ (w.st Z).toD7} {hT : GatTies (w.st Z).toD7} {Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L} {Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7}
  {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (w.st Z).toD7} {cX : ExtraC} (ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX)

abbrev famT {p0 : BaseLevelRowSide (w.D Z)} (t : RowsT K w Z Wt p0) := famR (w.st Z) w.I t.hX (usedOf w.I T Wt) t.r.z.Xg t.r.z.tr


set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option maxHeartbeats 4000000 in
structure TwArgs (t : RowsT K w Z Wt ex.p0) : Type 1 where
  Dc : ∀ Zs : DefSub (famT t).fam3.amb3, DefCols ((famT t).side3 t.r.z.F.P1 t.r.z.F.ψ1 Zs)
  Sp : ∀ Zs, SPer (Dc Zs)
  Zsc : DefSub (famT t).fam3.amb3 → IndefScale (famT t).fam3.base3
  lam : type_of% t.r.z.R.lam3
  err : type_of% t.r.z.R.err0
  lam_eq : ∀ i s p v, t.r.z.R.EEp3 p ≠ ⊥ → lam i s p v = t.r.z.R.lam3 i s p v
  x : TwIn ex
  pack : (⟨x.G, x.grp, x.fin, x.Pl0, x.I0, x.T, x.A3, x.core, x.alg, x.R, x.F, x.cG⟩ :
      Σ' (G : Type) (_ : Group G) (_ : Fintype G) (Pl0 I0 T0 : Type)
        (A3 : FamIn3 (w.st Z).toD7.what₂.LL G Pl0 I0 (List ℕ) T0 (w.st Z).toD7.R.m) (C : Formalism.L2.Pj.CoreJ (w.st Z).toD7)
        (_ : Algebra C.Q.c.F (w.st Z).toD7.what₂.LL) (R : RealDat3 (w.st Z).toD7 A3 C.Q.c.F) (_ : Face3 (w.st Z).toD7 A3),
        G0 R.Pg (w.st Z).toD7.R.r ≃* G0g (w.st Z).toD7.nd) =
    ⟨_, _, _, _, _, _, famT t, t.r.z.core, t.r.z.alg, (t.r.z.R.updS t.r.z.R.kap lam).withErr err, reFace t.r.z.F Dc Sp Zsc,
      (t.r.z.cG)⟩
  intersectionNumber_baseChange : Holds x.R x.F
  κ : HEq x.geo.κ t.r.z.geo.κ
  v₀ : HEq x.geo.v₀ t.r.z.geo.v₀
  fw : HEq x.geo.fw.e t.r.z.geo.fw.e
  tup : HEq x.Y.tup t.r.Y.tup
  tupT : HEq x.Y.tupT t.r.Y.tupT
  jA : HEq x.Y.jA t.r.Y.jA
  jA0 : HEq x.Y.jA0 t.r.Y.jA0
  eMt : HEq x.Y.eMt t.r.Y.eMt
  PY : HEq x.Y.PY t.r.Y.PY
  PW : HEq x.Y.PW t.r.Y.PW
  eFT : HEq x.Y.eFT t.r.Y.eFT
  IL : HEq x.Y.IL t.r.Y.IL
  eE : HEq x.Y.eE t.r.Y.eE
  eW : HEq x.Y.mj.eW t.r.Y.mj.eW
  jW : HEq x.Z.jW t.r.Z.jW
  eRR : HEq x.Z.eRR t.r.Z.eRR

end GlobalTheory.Mem.R3

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier

namespace GlobalTheory.ShFam

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

structure EigFrame (Z : Model Xo c β) {R : Type} [CommRing R] (φ : c.F →+* R) (x : Sp R ⟶ Z.X) : Type where
  v : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber R) ⟶ Z.t.G.left)
  tan : ∀ τ i, IsTanAtG Z.t x (v τ i)
  eig : ∀ τ i (a : 𝓞 E), v τ i ≫ (Z.t.act.act a).left = spMap (epsMul (φ (embK c τ a))) ≫ v τ i
  basis : ∀ τ w, IsTanAtG Z.t x w → (∀ a : 𝓞 E, w ≫ (Z.t.act.act a).left = spMap (epsMul (φ (embK c τ a))) ≫ w) →
    ∃! a : Fin (Dw.mult τ) → R, IsCombAtG Z.t x (v τ) a w

def EigFrame.Tri {Z : Model Xo c β} {R R' : Type} [CommRing R] [CommRing R'] {φ : c.F →+* R} {φ' : c.F →+* R'}
    {x : Sp R ⟶ Z.X} {x' : Sp R' ⟶ Z.X} (f : EigFrame Z φ x) (ψ : R →+* R') (g : EigFrame Z φ' x')
    (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → R'ˣ) : Prop :=
  x' = spMap ψ ≫ x ∧ φ' = ψ.comp φ ∧ ∀ τ i, ∃ cf : Fin (Dw.mult τ) → R', cf i = t τ i ∧ (∀ k, i < k → cf k = 0) ∧
    IsCombAtG Z.t x' (fun k => spMap (dualMap ψ) ≫ f.v τ k) cf (g.v τ i)


attribute [local instance] Over.cartesianMonoidalCategory in
open MonObj in
theorem isCombAtG_single {X0 : Scheme.{0}} (t : SAB H X0) {R : Type} [CommRing R] (x : Sp R ⟶ X0) {m : ℕ}
    {v : Fin m → (Sp (DualNumber R) ⟶ t.G.left)} (hv : ∀ j, IsTanAtG t x (v j)) (j : Fin m) :
    IsCombAtG t x v (Pi.single j 1) (v j) := by
  have hb : ∀ a : R, spMap (epsMul a) ≫ spMap (algebraMap R (DualNumber R)) = spMap (algebraMap R (DualNumber R)) :=
    fun a => by
      rw [← Spec.map_comp]
      congr 1
      ext r <;> simp [epsMul]
  have h1 : spMap (epsMul (1 : R)) = 𝟙 _ := by
    rw [← Spec.map_id]
    congr 1
    ext r <;> simp [epsMul]
  have h0 : spMap (epsMul (0 : R)) =
      spMap (algebraMap R (DualNumber R)) ≫ spMap (TrivSqZeroExt.fstHom R R R).toRingHom := by
    have e : epsMul (0 : R) = (algebraMap R (DualNumber R)).comp (TrivSqZeroExt.fstHom R R R).toRingHom :=
      RingHom.ext fun z => by ext <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]
    rw [← Spec.map_comp, e]
    rfl
  let u : Fin m → (tEpsG x ⟶ t.G) := fun i =>
    Over.homMk (spMap (epsMul ((Pi.single j 1 : Fin m → R) i)) ≫ v i) (by
      rw [Category.assoc, (hv i).1, ← Category.assoc, hb]; rfl)
  have hu : ∀ i, i ≠ j → u i = 1 := fun i hi => by
    let p : tEpsG x ⟶ Over.mk x := Over.homMk (spMap (algebraMap R (DualNumber R))) rfl
    rw [← MonObj.comp_one p]
    ext
    show spMap (epsMul ((Pi.single j 1 : Fin m → R) i)) ≫ v i = _
    rw [Pi.single_eq_of_ne hi, h0, Category.assoc, (hv i).2]
    rfl
  refine ⟨u, fun i => rfl, ?_⟩
  have : (List.ofFn u).prod = u j := by
    rw [List.ofFn_eq_map, List.prod_map_eq_pow_single j u fun i hi _ => hu i hi,
      List.count_eq_one_of_mem (List.nodup_finRange m) (List.mem_finRange j), pow_one]
  rw [this]
  show spMap (epsMul ((Pi.single j 1 : Fin m → R) j)) ≫ v j = _
  rw [Pi.single_eq_same, h1, Category.id_comp]

theorem EigFrame.tri_refl {Z : Model Xo c β} {R : Type} [CommRing R] {φ : c.F →+* R} {x : Sp R ⟶ Z.X}
    (f : EigFrame Z φ x) : f.Tri (RingHom.id R) f 1 := by
  have h1 : spMap (dualMap (RingHom.id R)) = 𝟙 _ := by
    rw [← Spec.map_id]
    congr 1
    ext r <;> simp [dualMap]
  have h2 : spMap (RingHom.id R) = 𝟙 _ := Spec.map_id _
  refine ⟨by rw [h2, Category.id_comp], rfl, fun τ i => ⟨Pi.single i 1, by simp,
    fun k hk => Pi.single_eq_of_ne hk.ne' _, ?_⟩⟩
  simp only [h1, Category.id_comp]
  exact isCombAtG_single Z.t x (f.tan τ) i

variable {F : Type} [Field F]

def constF (e : F ≃+* c.F) (Y : GlobalTheory.ProjVar.Var F) : c.F →+* Y.Fn := (algebraMap F Y.Fn).comp e.symm.toRingHom

def stalkPt (Y : GlobalTheory.ProjVar.Var F) (y : Y.X) : Sp (Y.X.presheaf.stalk y) ⟶ Y.X := Y.X.fromSpecStalk y

def genericPt (Y : GlobalTheory.ProjVar.Var F) : Sp Y.Fn ⟶ Y.X := Y.X.fromSpecStalk (genericPoint Y.X)

structure FlagCpt (Z : Model Xo c β) (e : F ≃+* c.F) : Type where
  Y : GlobalTheory.ProjVar.Var F
  π : Y.X ⟶ gen Z
  π_str : π ≫ genStr Z ≫ spMap e.toRingHom = Y.str

  y0 : letI := (constF e Y).toAlgebra; FrPt Xo c Y.Fn

  f0 : EigFrame Z (constF e Y) (genericPt Y ≫ π ≫ genι Z)
  y0_x : (letI := (constF e Y).toAlgebra; GlobalTheory.AllWt.ptF y0) ≫ Z.jQ = genericPt Y ≫ π

  flagComponentFramedPoint_frame : letI := (constF e Y).toAlgebra; ∀ τ i, ∃ w : Sp (DualNumber Y.Fn) ⟶ Z.oF.t.G.left,
    w ≫ Z.oF.t.G.hom = spMap (algebraMap Y.Fn (DualNumber Y.Fn)) ≫ GlobalTheory.AllWt.ptF y0 ∧
    w ≫ Z.m0.toSABMap.φ = y0.u τ i ∧ w ≫ Z.m.φ = f0.v τ i

  gr : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Y.Dv

  gr_spec : ∀ y : Y.X, ∃ (φ : c.F →+* Y.X.presheaf.stalk y) (f : EigFrame Z φ (stalkPt Y y ≫ π ≫ genι Z))
    (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Y.Fnˣ),
    f.Tri (algebraMap (Y.X.presheaf.stalk y) Y.X.functionField) f0 t ∧ ∀ τ i, (gr τ i).IsEqn y (t τ i)

  bd : Y.Dv
  bd_eff : Y.Eff bd
  bd_supp : ∀ y : Y.X, y ∈ Y.supp bd ↔ π y ∈ genBd Z
  bd_red : ∀ (y : Y.X) (g : Y.Fnˣ), bd.IsEqn y g → ∀ (f : Y.Fn) (n : ℕ), RegAt y f → RegAt y (f ^ n / g) → RegAt y (f / g)

namespace FlagCpt

variable {Z : Model Xo c β} {e : F ≃+* c.F} (C : FlagCpt Z e)

def Carries {k : Type} [Field k] {φ : c.F →+* k} {x : Sp k ⟶ Z.X} (p : Sp k ⟶ C.Y.X) (g : EigFrame Z φ x) : Prop :=
  ∃ (y : C.Y.X) (ψ : C.Y.X.presheaf.stalk y →+* k) (φ₁ : c.F →+* C.Y.X.presheaf.stalk y)
    (f : EigFrame Z φ₁ (stalkPt C.Y y ≫ C.π ≫ genι Z)) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ)
    (t' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ),
    p = spMap ψ ≫ stalkPt C.Y y ∧ f.Tri (algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField) C.f0 t ∧ f.Tri ψ g t'

def Ybd : C.Y.Cl := C.Y.supp C.bd

def LEx : (Ix Dw → ℤ) →+ C.Y.Dv where
  toFun ex := -∑ x : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), ex (some x) • C.gr x.1 x.2
  map_zero' := by simp
  map_add' a b := by simp [add_smul, Finset.sum_add_distrib, add_comm]

def Lw (la : GlobalTheory.AllWt.Weight Dw) : C.Y.Dv := C.LEx (GlobalTheory.AllWt.exOf Dw la 0)


end FlagCpt

structure FlagTor (Z : Model Xo c β) (e : F ≃+* c.F) {σ : c.F →+* ℂ} {N : ℕ} (U : Formalism.L2.PjFree.Unf Xo c σ N) : Type where
  C : U.Comp → FlagCpt Z e
  dim_eq : ∀ k, (C k).Y.dim = Module.finrank ℚ E / 2 * (N * (N - 1) / 2)
  lifts : ∀ (k : Type) [Field k] [IsAlgClosed k] (φ : c.F →+* k) (x : Sp k ⟶ gen Z), x ≫ genStr Z = spMap φ →
    ∀ g : EigFrame Z φ (x ≫ genι Z), ∃! p : Σ i : U.Comp, (Sp k ⟶ (C i).Y.X), p.2 ≫ (C p.1).π = x ∧ (C p.1).Carries p.2 g
  label : ∀ (i : U.Comp) (x : (U.X i).dom) (s : Sp (CAt σ)),
    (GlobalTheory.AllWt.ptF (U.un i x) ≫ Z.jQ) s ∈ Set.range (C i).π

def keyEx (Dw : Datum H) : Ix Dw → ℤ
  | none => -2
  | some _ => 1

structure KeySec (Xo : Moduli Dw l) (c : Coeff l) : Type where
  ρ : (Rul Xo c)ˣ
  mem : (ρ : Rul Xo c) ∈ GlobalTheory.AllWt.secZ Xo c (keyEx Dw)

def exKey (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Ix Dw → ℤ :=
  fun i => (ex Dw a n i : ℤ) + ((n / 2 : ℕ) : ℤ) * keyEx Dw i

theorem exKey_two_mul (a : (E →+* ℂ) × ℕ → ℕ) (m : ℕ) :
    exKey Dw a (2 * m) = GlobalTheory.AllWt.exOf Dw (GlobalTheory.AllWt.weightOf Dw (fun x => (a x : ℤ)) m) 0 := by
  have h : GlobalTheory.AllWt.weightOf Dw (fun x => (a x : ℤ)) (m : ℤ) =
      GlobalTheory.AllWt.weightOf Dw (fun x => (a x : ℤ) + (m : ℤ)) 0 := by
    funext τ j
    simp only [GlobalTheory.AllWt.weightOf]
    split_ifs <;> ring
  rw [h, GlobalTheory.AllWt.exOf_weightOf]
  funext i
  cases i <;> simp [exKey, keyEx, ex, exZ]
  ring

theorem KeySec.pow_mem (κ : KeySec Xo c) (m : ℕ) :
    (κ.ρ : Rul Xo c) ^ m ∈ GlobalTheory.AllWt.secZ Xo c (fun i => (m : ℤ) * keyEx Dw i) := by
  induction m with
  | zero =>
    have h : (fun i => ((0 : ℕ) : ℤ) * keyEx Dw i) = 0 := by funext i; simp
    rw [pow_zero, h]; exact GlobalTheory.AllWt.one_mem_secZ
  | succ m ih =>
    have h : (fun i => ((m + 1 : ℕ) : ℤ) * keyEx Dw i) = (fun i => (m : ℤ) * keyEx Dw i) + keyEx Dw := by
      funext i; simp only [Pi.add_apply]; push_cast; ring
    rw [pow_succ, h]; exact GlobalTheory.AllWt.mul_mem_secZ ih κ.mem

end Free

abbrev FinalTheorems.Flag {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} (s : FinalTheorems S κ) : Type :=
  FlagTor s.T.Z κ.e (s.U κ.σ₀)

end GlobalTheory.ShFam
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MovedReadingSameMapsBaseReadingAgrees
noncomputable section

namespace GlobalTheory.Mem.Top.Bl

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.GroupRetwisting NumberField IsDedekindDomain
  Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section General

variable (D : D7) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} (A : FamIn D.what₂.LL G Pl0 T D.R.m)
  (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (P1 : Subgroup G) (ψ1 : P1 →* D.what₂.LLˣ) (X0 : BaseLevelRowSide D) (tp : D.what₂.Tup → T)
  (eG : G ≃* G0g D.nd)


set_option genInjectivity false in
set_option genSizeOfSpec false in
structure AllT : Type where
  jA : ∀ μ, (Fin (rDim D A P1 ψ1 (tp μ)) → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Amb μ
  jA0 : ∀ μ, (Fin (rDim D A P0 ψ0 (tp μ)) → D.what₂.LL) →ₛₗ[D.what₂.embLL] X0.s.Amb μ
  eMt : ∀ (i : Fin D.R.m) μ, (Fin (lDim D A P0 ψ0 i (tp μ)) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL μ ((i : ℕ) + 1)
  formsA : ∀ μ, FormsTie D.what₂.embLL (jA μ) (rH D A P1 ψ1 (tp μ)) (rE D A P1 ψ1 (tp μ)) (D.what₂.eOp μ)
  latA : ∀ μ, OLatTie D.what₂.embLL (D.what₂.Mtilde μ) (jA μ) (rNab D A P1 ψ1 (tp μ))
  formsAtBottomLevel : ∀ μ, FormsTie D.what₂.embLL (jA0 μ) (rH D A P0 ψ0 (tp μ)) (rE D A P0 ψ0 (tp μ)) (X0.s.eOp μ)
  latA0 : ∀ μ, OLatTie D.what₂.embLL (X0.s.Mtilde μ) (jA0 μ) (rNab D A P0 ψ0 (tp μ))
  formsL : ∀ (i : Fin D.R.m) μ, FormsTie D.what₂.embLL ((D.what₂.jMt μ ((i : ℕ) + 1)).comp (eMt i μ).toLinearMap)
    (lH D A P0 ψ0 i (tp μ)) (lE D A P0 ψ0 i (tp μ)) (D.what₂.eMt μ ((i : ℕ) + 1))
  latL : ∀ (i : Fin D.R.m) μ, OLatTie D.what₂.embLL (D.what₂.MtLat μ ((i : ℕ) + 1))
    ((D.what₂.jMt μ ((i : ℕ) + 1)).comp (eMt i μ).toLinearMap) (lNab D A P0 ψ0 i (tp μ))
  cen : ∀ μ (z : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))) (a : MonoidAlgebra D.what₂.LL G),
    (∀ g : G, D.what₂.embLL (a.coeff g) = (z : MonoidAlgebra ℂ (G0g D.nd)).coeff (eG g)) →
    (∀ x, (RowSide.sharp D).cen μ z (jA μ x) = jA μ ((Formalism.L2.Rows.rOp D A P1 ψ1 (tp μ) a).mulVec x)) ∧
    (∀ x, X0.s.cen μ z (jA0 μ x) = jA0 μ ((Formalism.L2.Rows.rOp D A P0 ψ0 (tp μ) a).mulVec x)) ∧
    ∀ (i : Fin D.R.m) x, D.ntypes.cenMt μ ((i : ℕ) + 1) z (D.what₂.jMt μ ((i : ℕ) + 1) (eMt i μ x)) =
      D.what₂.jMt μ ((i : ℕ) + 1) (eMt i μ (((A.fam.L i (tp μ)).S.lvlOp (A.fam.L i (tp μ)).r (A.fam.lvlA P0 ψ0).P
        (A.fam.lvlA P0 ψ0).ψ a).mulVec x))

def SameOn {K : Type} {n n' : ℕ} {V : Type} (j : (Fin n → K) → V) (j' : (Fin n' → K) → V) : Prop :=
  n = n' ∧ ∀ x x', (∀ (a : Fin n) (a' : Fin n'), (a : ℕ) = a' → x a = x' a') → j x = j' x'

end General

section Cols

attribute [local instance] GlobalTheory.Mem.Col2.starE

variable {B : Base} {px : PreX B.toPre} (I : ColIn B px)

def tAll (a : I.ι) : R3.TupU I Set.univ := ⟨I.tup a, Or.inr ((R3.tup_mem_tuOf I).2 (Set.mem_univ a))⟩

end Cols

section Forms

open _root_.Formalism.L2.Col

def IsFormOf {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (hX : X.Ok)
    (P : LevFam X.E X.K R.r Pr.vGs) (x : MtildeV W Ch sel mu P) {V : Type} (y : V) : Prop :=
  ∃ (F : (mtildeKGSD W Ch sel mu).EqFun) (h : F.1 ∈ (mtildeGSD W Ch sel mu P).EqFun),
    HEq ((mtildeKGSD W Ch sel mu).res (mtildeKOk W Ch sel mu hX) F) y ∧ x = ⟨F.1, h⟩

end Forms

section Crd

attribute [local instance] GlobalTheory.Mem.Col2.starE

def IsCrd {B : Base} {px : PreX B.toPre} (I : ColIn B px) (hX : B.fields.Ok) (a : I.ι) {V M : Type} [AddCommGroup M] [Module ℂ M]
    (e : Df.MtCx I a ≃ₗ[ℂ] M) (y : V) (v : M) : Prop :=
  ∃ x : Formalism.L2.Col.MtildeV (Pr := B.primes px) B.wts I.Ch I.sel (I.tup a) (TC.Ps I),
    IsFormOf (Pr := B.primes px) B.wts I.Ch I.sel (I.tup a) hX (TC.Ps I) x y ∧ v = e (Df.toCx I hX a x)

end Crd

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B}

abbrev famAll {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)} (t : RowsT K w Z Wt p0) :=
  (R3.famR (w.st Z) w.I t.hX Set.univ t.r.z.Xg t.r.z.tr).A


set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option maxHeartbeats 1000000 in
structure RXs {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)} (t : RowsT K w Z Wt p0) : Type 1 where
  all : AllT (w.st Z).toD7 (famAll t) (R3.lev0 w.I) (R3.chr0 w.I) (R3.lev1 w.I) (R3.chr1 w.I) p0 (tAll w.I)
    (t.r.z.R.eG.trans t.r.z.cG)
  jA_use : ∀ s, SameOn (all.jA (t.r.Y.tup s)) (t.r.Y.jA s)
  movedReadingSameMaps_baseReading_agrees : ∀ s, SameOn (all.jA0 (t.r.Y.tup s)) (t.r.Y.jA0 s)
  eMt_use : ∀ i s, SameOn (all.eMt i (t.r.Y.tup s)) (t.r.Y.eMt i s)
  e : ∀ a : w.C.Tup, Df.MtCx w.I a ≃ₗ[ℂ] Z.W.Amb a
  eMt0 : ∀ u F, Df.SameForm w.I w.l u w.I.mu0 F ((Z.W.eMt0 u).symm (e w.C.mu0 F))
  eMtTw : ∀ u (a : w.C.Tup) F, Df.SameForm w.I w.l u a F ((Z.W.eMtTw u a).symm (e a F))
  crd : ∀ (a : w.C.Tup) y, IsCrd w.I t.hX a (e a)
    (R3.rowForm (D := (w.st Z).toD7) (famAll t) (R3.lev1 w.I) (R3.chr1 w.I) (tAll w.I a) y) (all.jA a y)
  io : ∀ μ j, ¬ Formalism.IndefR.RecTie.Used0 (w.D Z) μ → Z.W.io μ j = 0 ∧ p0.s.io μ j = 0
  sha : GlobalTheory.MemN.ShaOK B.toPre Z.W.shaLen
  laws : Formalism.L2.Pj.LawsCore t.r.z.core.toCore
  canon : t.r.z.core.Q.Canon
  rank : ∀ j, 1 ≤ (t.r.z.core.Q.Dw j).p + (t.r.z.core.Q.Dw j).q
  pb : t.r.z.core.pb = f.P.pb
  std : t.r.z.Std

def RX : RPosition := fun _ _ _ _ _ _ _ _ t => RXs t

end GlobalTheory.Mem.Top.Bl

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.DIV.Cons (SCF intO)

namespace GlobalTheory.LocM

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}

abbrev Vecs (Dw : Datum H) {X : Scheme.{0}} (t : SAB H X) (R : Type) [CommRing R] : Type :=
  ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber R) ⟶ t.G.left)

def IsFrame {l : Level H} {c : Coeff l} {X : Scheme.{0}} (t : SAB H X) {R : Type} [CommRing R] (f : c.F →+* R)
    (x : Sp R ⟶ X) (u : Vecs Dw t R) : Prop :=
  (∀ τ i, IsTanAtG t x (u τ i) ∧
    ∀ a : 𝓞 E, u τ i ≫ (t.act.act a).left = spMap (epsMul (f (embK c τ a))) ≫ u τ i) ∧
  ∀ τ w, IsTanAtG t x w → (∀ a : 𝓞 E, w ≫ (t.act.act a).left = spMap (epsMul (f (embK c τ a))) ≫ w) →
    ∃! a : Fin (Dw.mult τ) → R, IsCombAtG t x (u τ) a w

def SameFlag (ty : (E →+* ℂ) → Finset ℕ) {X : Scheme.{0}} (t : SAB H X) {R : Type} [CommRing R] (x : Sp R ⟶ X)
    (u u' : Vecs Dw t R) : Prop :=
  ∀ τ, ∀ k ∈ ty τ, ∀ i : Fin (Dw.mult τ), (i : ℕ) < k →
    ∃ cf : Fin (Dw.mult τ) → R, (∀ j : Fin (Dw.mult τ), k ≤ (j : ℕ) → cf j = 0) ∧ IsCombAtG t x (u τ) cf (u' τ i)

def ProperLE (Dw : Datum H) (ty' ty : (E →+* ℂ) → Finset ℕ) : Prop :=
  ∀ σ, ∀ k ∈ ty' σ, 0 < k → k < Dw.mult σ → k ∈ ty σ

def Vecs.bc {X : Scheme.{0}} {t : SAB H X} {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (u : Vecs Dw t R) :
    Vecs Dw t S := fun τ i => spMap (dualMap φ) ≫ u τ i

variable {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ}

structure Pre (Y : LocalSystem Xo p W) (i₀ : Idx H p) : Type where

  i : Idx H p

  dvd : i₀.l.Dvd i.l

  le : i₀.c.F ≤ i.c.F

  n : ℕ

  I : (PSpace (i.c.V W) n).IdealSheafData

  π : I.subscheme ⟶ (Y i).X

  ty : (E →+* ℂ) → Finset ℕ

  m : ℕ

  U : Fin m → I.subscheme.affineOpens

  alg : ∀ a, i.c.F →+* Γ(I.subscheme, (U a).1)

  fr : ∀ a, Vecs Dw (Y i).t Γ(I.subscheme, (U a).1)

variable {Y : LocalSystem Xo p W} {i₀ : Idx H p}

namespace Pre

variable (Z : Pre Y i₀)

abbrev X : Scheme.{0} := Z.I.subscheme

def s : Z.X ⟶ Sp (Z.i.c.V W) := Z.I.subschemeι ≫ PSpace.str _ Z.n

def chart (a : Fin Z.m) : Sp Γ(Z.X, (Z.U a).1) ⟶ Z.X := (Z.U a).2.fromSpec

def opn : Set Z.X := Z.π ⁻¹' Set.range (Y Z.i).j

def FlagAt {k : Type} [Field k] (w : Sp k ⟶ Z.X) (u : Vecs Dw (Y Z.i).t k) : Prop :=
  ∃ (a : Fin Z.m) (φ : Γ(Z.X, (Z.U a).1) →+* k), spMap φ ≫ Z.chart a = w ∧
    IsFrame (Y Z.i).t (φ.comp (Z.alg a)) (w ≫ Z.π) u ∧ SameFlag Z.ty (Y Z.i).t (w ≫ Z.π) ((Z.fr a).bc φ) u

end Pre

structure Mdl (Y : LocalSystem Xo p W) (i₀ : Idx H p) : Type extends Pre Y i₀ where

  π_s : π ≫ (Y i).s = toPre.s

  normal : IsNormalScheme toPre.X

  flat : Flat toPre.s

  dense : Dense toPre.opn

  cover : ⋃ a, ((U a).1 : Set toPre.X) = toPre.opn

  alg_s : ∀ a, toPre.chart a ≫ toPre.s = spMap ((alg a).comp (i.c.V W).subtype)

  smooth : ∀ a, Smooth (toPre.chart a ≫ π)

  frame : ∀ a, IsFrame (Y i).t (alg a) (toPre.chart a ≫ π) (fr a)

  glue : ∀ (k : Type) [Field k] (a a' : Fin m) (φ : Γ(toPre.X, (U a).1) →+* k) (φ' : Γ(toPre.X, (U a').1) →+* k),
    spMap φ ≫ toPre.chart a = spMap φ' ≫ toPre.chart a' →
      SameFlag ty (Y i).t (spMap φ ≫ toPre.chart a ≫ π) ((fr a).bc φ) ((fr a').bc φ')

  bij : ∀ (k : Type) [Field k] (f : i.c.F →+* k) (y : Sp k ⟶ (Xo i.l).XF i.c), y ≫ pullback.snd _ _ = spMap f →
    ∀ u, IsFrame (Y i).t f (y ≫ (Y i).j) u → ∃! w : Sp k ⟶ toPre.X, w ≫ π = y ≫ (Y i).j ∧ toPre.FlagAt w u

namespace Mdl

variable (Z : Mdl Y i₀)

def t : SAB H Z.X := (exists_sab Z.π (Y Z.i).t).choose

def tMap : SABMap Z.t (Y Z.i).t Z.π := (exists_sab Z.π (Y Z.i).t).choose_spec.some

structure Pt : Type where

  C : SCF p

  P : PointsOfFlagModel.PtC (Y Z.i) C

  z : Sp ↥(intO ↥C.S) ⟶ Z.X

  z_π : z ≫ Z.π = P.yt

def Pt.fld {Z : Mdl Y i₀} (y : Z.Pt) : Formalism.MainNotions.ModuliIntegralCharts.CF p := y.C.toCF

def Pt.gen {Z : Mdl Y i₀} (y : Z.Pt) : Sp ↥y.C.S ⟶ Z.X := spMap (intO ↥y.C.S).subtype ≫ y.z

def inQ (x : Z.X) : Prop := CharZero (Z.X.residueField x)

def abP (x : Z.X) : Prop := Z.π x ∈ abLocus (Y Z.i).t.G

def isGenP (x : Z.X) : Prop := ∀ x' : Z.X, x' ⤳ x → x' = x

def Gen : Type := {x : Z.X // ¬ Z.inQ x ∧ ∀ x' : Z.X, ¬ Z.inQ x' → x' ⤳ x → x' = x}

def free (a m : ℕ) : Z.X.Modules :=
  GlobalTheory.twist (GlobalTheory.QCoh.freeModule Z.X (Fin m)) ((GlobalTheory.ProjSpace.On (Z.i.c.V W) Z.n (-(a : ℤ))).pull Z.I.subschemeι)

structure Sh : Type where

  a : ℕ

  m : ℕ

  a' : ℕ

  m' : ℕ

  φ : Z.free a' m' ⟶ Z.free a m

def Sh.toMod {Z : Mdl Y i₀} (F : Z.Sh) : Z.X.Modules := cokernel F.φ


open Classical in
def ofMod (F : Z.X.Modules) : Z.Sh :=
  if h : ∃ S : Z.Sh, Nonempty (S.toMod ≅ F) then h.choose else ⟨0, 0, 0, 0, 0⟩

def Idl : Type := {J : Z.X.IdealSheafData // ∀ x ∈ J.support, x ∉ Z.opn}

def powP (J : Z.Idl) : Prop := ∃ k : ℕ, ∀ U : Z.X.affineOpens, ((p : Γ(Z.X, U.1)) ^ k) ∈ J.1.ideal U

end Mdl

def IsTrans (i i₂ : Idx H p) (τ : (Y i₂).X ⟶ (Y i).X) (mu : SABMap (Y i₂).t (Y i).t τ) : Prop :=
  ∃ (b : i.c.V W →+* i₂.c.V W) (π' : (Y i₂).X ⟶ pullback (Y i).s (spMap b))
    (r : (Xo i₂.l).XF i₂.c ⟶ (Xo i.l).XF i.c), IsIncl b ∧
    π' ≫ pullback.fst _ _ = τ ∧ π' ≫ pullback.snd _ _ = (Y i₂).s ∧ IsFinite π' ∧ (Y i₂).j ≫ τ = r ≫ (Y i).j ∧
    (∀ a, ((Y i₂).oF.eta a ^ (i₂.l.M / i.l.M)).left ≫ (Y i₂).m.φ ≫ mu.φ = r ≫ ((Y i).oF.eta a).left ≫ (Y i).m.φ) ∧
    (∀ a, ((Y i₂).oF.etaA a ^ (i₂.l.A / i.l.A)).left ≫ (Y i₂).m.φ ≫ mu.φ = r ≫ ((Y i).oF.etaA a).left ≫ (Y i).m.φ)

def NatImg (Z₁ Z₂ : Mdl Y i₀) {k : Type} [Field k] (w₁ : Sp k ⟶ Z₁.X) (w₂ : Sp k ⟶ Z₂.X) : Prop :=
  ∃ (τ : (Y Z₁.i).X ⟶ (Y Z₂.i).X) (mu : SABMap (Y Z₁.i).t (Y Z₂.i).t τ) (u : Vecs Dw (Y Z₁.i).t k),
    IsTrans Z₂.i Z₁.i τ mu ∧ w₂ ≫ Z₂.π = w₁ ≫ Z₁.π ≫ τ ∧ Z₁.FlagAt w₁ u ∧ Z₂.FlagAt w₂ (fun σ i => u σ i ≫ mu.φ)

def NatCorr (Z₁ Z₂ : Mdl Y i₀) : Prop := Z₂.i.l.Dvd Z₁.i.l ∧ Z₂.i.c.F ≤ Z₁.i.c.F ∧ ProperLE Dw Z₂.ty Z₁.ty

def IsNatMap (Z₁ Z₂ : Mdl Y i₀) (f : Z₁.X ⟶ Z₂.X) : Prop :=
  NatCorr Z₁ Z₂ ∧ ∀ (k : Type) [Field k] (w : Sp k ⟶ Z₁.X), Set.range w ⊆ Z₁.opn → NatImg Z₁ Z₂ w (w ≫ f)

def Corr (Z₁ Z₂ : Mdl Y i₀) : Prop := Z₂.i.l.Dvd Z₁.i.l ∧ Z₂.i.c.F ≤ Z₁.i.c.F ∧ ∀ σ, Z₂.ty σ ⊆ Z₁.ty σ

def IsMap (Z₁ Z₂ : Mdl Y i₀) (f : Z₁.X ⟶ Z₂.X) : Prop :=
  Corr Z₁ Z₂ ∧ ∀ (k : Type) [Field k] (w : Sp k ⟶ Z₁.X), Set.range w ⊆ Z₁.opn → NatImg Z₁ Z₂ w (w ≫ f)

def IsNBlow (Z : Mdl Y i₀) (J : Z.Idl) (Z' : Mdl Y i₀) : Prop :=
  Z'.i = Z.i ∧ Z'.ty = Z.ty ∧ ∃ (X' : Scheme.{0}) (b : X' ⟶ Z.X) (ν : Z'.X ⟶ X'),
    ReciprocityTheory.AnForm.R.FinalTheorems.Blowup b J.1 ∧ IsFinite ν ∧ IsMap Z' Z (ν ≫ b)

def IsNatDiag (Z₁ Z₂ Z' : Mdl Y i₀) : Prop :=
  Z'.i = Z₁.i ∧ Z'.ty = Z₁.ty ∧ ∃ (f₁ : Z'.X ⟶ Z₁.X) (f₂ : Z'.X ⟶ Z₂.X), IsMap Z' Z₁ f₁ ∧ IsNatMap Z' Z₂ f₂ ∧
    IsFinite (prod.lift f₁ f₂)

def IsDiag (Z₁ Z₂ Z' : Mdl Y i₀) : Prop :=
  Z'.i = Z₁.i ∧ Z'.ty = Z₁.ty ∧ ∃ (f₁ : Z'.X ⟶ Z₁.X) (f₂ : Z'.X ⟶ Z₂.X), IsMap Z' Z₁ f₁ ∧ IsMap Z' Z₂ f₂ ∧
    IsFinite (prod.lift f₁ f₂)


open Classical in
def blowUp (Z : Mdl Y i₀) (J : Z.Idl) : Mdl Y i₀ := if h : ∃ Z', IsNBlow Z J Z' then h.choose else Z


open Classical in
def natDiagCl (Z₁ Z₂ : Mdl Y i₀) : Mdl Y i₀ := if h : ∃ Z', IsNatDiag Z₁ Z₂ Z' then h.choose else Z₁


open Classical in
def diagCl (Z₁ Z₂ : Mdl Y i₀) : Mdl Y i₀ := if h : ∃ Z', IsDiag Z₁ Z₂ Z' then h.choose else Z₁

theorem NatCorr.refl (Z : Mdl Y i₀) : NatCorr Z Z := ⟨⟨dvd_rfl, le_rfl, dvd_rfl⟩, le_rfl, fun _ _ hk _ _ => hk⟩

def IsLvl (i₀ i : Idx H p) : Option ℕ → Prop
  | none => i = i₀
  | some n => i.l.M = i₀.l.M ∧ i.l.Mb = i₀.l.Mb ∧ i.l.A = i₀.l.A * p ^ n ∧
      i.c.F = i₀.c.F ⊔ IntermediateField.adjoin ℚ {zeta i.l.M'}

structure Bases (Y : LocalSystem Xo p W) (i₀ : Idx H p) : Type where

  X : Option ℕ → Mdl Y i₀

  lvl : ∀ b, IsLvl i₀ (X b).i b

  iso : ∀ b, IsIso (X b).π

  ty : ∀ b σ, (X b).ty σ = ∅

end GlobalTheory.LocM
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemNonzeroPlacesOfResidueChar
noncomputable section

namespace GlobalTheory.Mem.Top.Bl.Model3

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.GroupRetwisting NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)}

theorem fk_zero (t : RowsT K w Z Wt p0) (v : B.places.Pl) (hv : v ∉ Wt) (j : Fin B.R.m) :
    FK K.s (w.D Z) (j.1 + 1) (B.places.resChar v) = 0 := by
  by_contra h
  apply hv
  rw [t.exact]
  refine ⟨j, _, Or.inl rfl, Or.inr (Or.inr ?_)⟩
  have e : (w.D Z).plEq.symm ((w.D Z).plEq v) = v := Equiv.symm_apply_apply _ _
  show FK K.s (w.D Z) (j.1 + 1) ((w.D Z).what₂.places.resChar ((w.D Z).plEq.symm ((w.D Z).plEq v))) ≠ 0
  rw [e]
  exact h

section Idx

open Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T' : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T' D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
  {Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0}

end Idx

theorem fTypeG_ne {D : D7} (h : DV.KapDef D) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) : FTypeG D j ≠ 0 := by
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hf : 0 < Fintype.card D.what₂.Tau := by rw [D.what₂.card_Tau]; exact GaloisStage.f_pos D.R
  obtain ⟨τ⟩ := Fintype.card_pos_iff.1 hf
  have hs : (D.R.sigW j).1 = D.R.k + j - 1 := rfl
  let i : Fin (D.R.sigW j).1 := ⟨D.R.k + j - 1 - 1, by rw [hs]; omega⟩
  have e := (h j h1 h2 τ).1 i
  have l := DV.aPlusQ_last D j h1 h2 τ
  have p : (1 : ℤ) ≤ D.what₂.kaBig j τ i := by
    have : (1 : ℚ) ≤ (D.what₂.kaBig j τ i : ℚ) := e ▸ l
    exact_mod_cast this
  have q : 0 < fockDeg D j := by
    unfold fockDeg
    refine Finset.sum_pos' (fun t _ => add_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)
      (Finset.sum_nonneg fun _ _ => abs_nonneg _)) ⟨τ, Finset.mem_univ _, ?_⟩
    refine add_pos_of_pos_of_nonneg (Finset.sum_pos' (fun _ _ => abs_nonneg _) ⟨i, Finset.mem_univ _, ?_⟩)
      (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    exact abs_pos.2 (by omega)
  unfold FTypeG
  have : (0 : ℝ) < (fockDeg D j : ℝ) := by exact_mod_cast q
  linarith

theorem type_mem (t : RowsT K w Z Wt p0) (v : B.places.Pl) (i : Fin 2) (hv : B.places.resChar v = B.host.g i) : v ∈ Wt := by
  by_contra h
  have hm : 0 < B.R.m := by have := B.R.two_le_m; omega
  have z := fk_zero t v h ⟨0, hm⟩
  unfold FK at z
  rw [if_pos ⟨i, hv⟩] at z
  exact fTypeG_ne t.r.Y.kap 1 le_rfl hm z

end GlobalTheory.Mem.Top.Bl.Model3

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.See
noncomputable section

namespace GlobalTheory.Mem.Top.Bl

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV
  Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.MainNotions Formalism.L2.Forms NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure SAt {D : D7} {G' : Type} [Group G'] [Fintype G'] {Pl0 T : Type} {A : FamIn D.what₂.LL G' Pl0 T D.R.m} {Ks : Type} [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (eE : D.what₂.EE →ₗ[ℂ] R.HE.H)
    (F0 : ∀ u, Forms0 D u) : Type 1 where
  P : SPack D F0
  S : SRest P
  t : GA D (D.sp.Y 0)
  c : ℝ
  c_pos : 0 < c
  see : SeeAt R F P.X P.inst t
  ev : EvalTieT (MP R) R.ν0 R.fd0 (EP R F) P.X P.G (iotaX P.X P.inst).toMulEquiv t c
  rowJ : RowJ R eE P.X P.inst P.G t S.j

def SX : SPosition := fun _ _ _ _ w Z _ _ r col =>
  SAt (D := (w.st Z).toD7) r.r.z.R.toRealDat r.r.z.F.lv2 r.r.Y.eE fun u => (col.C.forms u).to0

end GlobalTheory.Mem.Top.Bl

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RatInEig
noncomputable section

namespace GlobalTheory.Mem.Top.Bl

open Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2 _root_.Formalism.L2.Host _root_.Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.NX ReciprocityTheory.Gal
  NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.HeightCounting

attribute [local instance] Formalism.BasicNotions.Host.cmStar


set_option maxHeartbeats 1000000 in
def ratL {D : D7} (L : LocAll (lay0 D)) (S : RatDat D.ntw) : RatDat (withLoc L).ntw := { S with }


set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option maxHeartbeats 1000000 in
structure NAt (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (cf : CharFrame D) (nch : NChoice D) (tp : TupTied D cf nch) :
    Type 1 where
  nt : NTrue hL D cf nch tp
  all : NAllC D nch
  chr_eq : (⟨all.cf, all.tp⟩ : Σ c : CharFrame D, TupTied D c nch) = ⟨cf, tp⟩
  host : HostTied D
  frameN : ∀ x, all.gal.fr.jE x = host.fr.j x
  chrN : NCharTied D cf nch tp
  chrGal : NGalChrTied D cf nch tp
  Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host
  Pq_over : ∀ v, NG.OverPl (Pq v) v
  pq : ∀ i j b k Q ψ (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (hadm : NX.AdmTw D i k Q ψ),
    (all.exp.mtV i j b k Q ψ h1 h2 hadm).QP = qpOf D Pq Q ∧ (all.exp.mtV i j b k Q ψ h1 h2 hadm).DP = qpOf D Pq (D.ntw.pD i)
  jE_eq : HEq nt.jE all.gal.fr.jE
  mt_eq : HEq (mtL nt.L nt.M) all.gal.mt
  Pq_eq : HEq nt.Pq Pq
  low : 2 ∈ nt.low ∧ AbsolutelyIrreducibleSpan.q0 D ∈ nt.low ∧ (NumberField.discr D.host.E).natAbs.primeFactors ⊆ nt.low ∧
    (Ideal.absNorm D.host.ccK).primeFactors ⊆ nt.low
  split : GlobalTheory.SplitCoef.OSplit D
  ratIn : RatIn nt.D nt.S
  ratIn_hL : ratIn.hL = nt.hL
  ratIn_eig : ratIn.eig = nt.eig
  ratIn_θ : ratIn.θ = nt.θ
  depth : RowDepth nt.D nt.rep

section Rows

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]


set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option maxHeartbeats 1000000 in
structure NRow {hL : GlobalTheory.Published.LocalLanglandsGL} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch}
    (a : NAt hL D cf nch tp) (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) {X0 : BaseLevelRowSide D}
    (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) : Type 1 where
  kKs : Ks →+* ↥D.LL0
  hk : ∀ x : Ks, ((kKs x : ↥D.LL0) : D.what₂.LL) = algebraMap Ks D.what₂.LL x
  nexp : NExpRealS R cG (ratDatR R cG kKs hk)
  hecke : NExpRealH R cG (ratDatR R cG kKs hk) nexp
  grp : GrpTie D A3.A F.P0 F.ψ0 F.P1 F.ψ1 (R.eG.trans cG)
  rowLoc : principalLevelFrame.RowLocPin a.all.gal.lp R.θ Y.PY (R.MY 0) (fun b => levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b)))
    (fun b => levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b))) (fun _ => R.e0) Y.eFT
  S_eq : HEq (ratL a.nt.L a.nt.S) (ratDatR R cG kKs hk)
  hL_eq : HEq a.nt.hL hecke.hL
  rep_eq : HEq a.nt.rep fun σ : D.what₂.FT => principalLevelFrame.rowRepR R.θ (Y.eFT σ)

end Rows

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B}

structure NCore (hL : GlobalTheory.Published.LocalLanglandsGL) {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)}
    (t : RowsT K w Z Wt p0) {nch : NChoice (w.D Z)} (n : NchT w Z Wt nch) : Type 1 where
  a : NAt hL (w.D Z) (TC.cf w.I w.l Z) nch n.tp
  row : NRow (D := (w.st Z).toD7) a t.r.z.R t.r.z.F t.r.z.cG t.r.Y
  sel : Set.range a.Pq = Set.range w.I.sel

abbrev NExt (hL : GlobalTheory.Published.LocalLanglandsGL) : Type 2 :=
  ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl)
    (p0 : BaseLevelRowSide (w.D Z)) (t : RowsT K w Z Wt p0) (nch : NChoice (w.D Z)) (n : NchT w Z Wt nch) (_ : ThData (w.D Z)),
    NCore hL t n → Type 1

def NX (hL : GlobalTheory.Published.LocalLanglandsGL) (E : NExt hL) : NCondition := fun K B f T w Z Wt p0 t nch n xd =>
  Σ c : NCore hL t n, E K B f T w Z Wt p0 t nch n xd c

end GlobalTheory.Mem.Top.Bl

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DsigEq
noncomputable section

namespace GlobalTheory.Mem.Top.Bl

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.GroupRetwisting NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure GoodO (D : D7) (nch : NChoice D) (xd : ThData D) : Prop where
  tw : ∃ I : TwIn D, I.E = twEOf xd ∧ DQ.GoodAllAt D nch I ∧ GlobalTheory.HeightCounting.GoodCl D nch I
  sep : ∀ v v', D.what₂.muAt v ≠ D.what₂.mu0 → D.what₂.muAt v' ≠ D.what₂.mu0 → nch.twI v ≠ nch.twI v' → Disjoint (nch.Q v) (nch.Q v')

variable {B : Base} {f : Fr B.toPre} {T : TwDat B}

structure Wit (𝒮 : Slots) (K : Ctx) (w : ColW B f T) (Z : w.Lt) (O : Obj2 (w.D Z)) : Type 1 where
  isOver : K.Over B.toPre
  forced : Forced K B T
  Wt : Set B.places.Pl
  pin : ColPin w
  coh : Coh B T
  vol : Formalism.L2.Theta.VolTieG (w.D Z)
  col : ColumnDataSplitPrimes K w Z
  what₂ : RowsT K w Z Wt O.p0
  rx : 𝒮.Rx K B f T w Z Wt O.p0 what₂
  lev : O.lev = col.full.1.base.lev0
  errX : O.errX = Formalism.L2.Herm.toErrXS col.full.1
  n : NchT w Z Wt O.nch
  nx : 𝒮.Nx K B f T w Z Wt O.p0 what₂ O.nch n O.xd
  sx : 𝒮.Sx K B f T w Z Wt O.p0 what₂ col.toColT
  ker0 : KerFam (w.D Z) col.Gt col.cmp (w.tw Z) O.Gy
  ker_eq : (⟨O.gatT, O.cmp, O.tw, O.ker⟩ : Σ (Gt : GatTies (w.D Z)) (cmp : LatCmp (w.D Z)) (tw : TwForms (w.D Z)),
    KerFam (w.D Z) Gt cmp tw O.Gy) = ⟨col.Gt, col.cmp, w.tw Z, ker0⟩
  ker : KerT col.toColT O.X O.Gy ker0
  div : DivT n O.X
  th : ThT n O.th
  obj : ObjT O what₂
  ox : 𝒮.Ox K B f T w Z Wt O what₂
  real : Formalism.L2.Theta.RealTied (w.D Z)
  dsig_eq : ∀ τ, Z.S.dsig τ = Vol.trueDsig B.R (B.hc τ)
  gauge : O.gauge.IsGauge
  good : GoodO (w.D Z) O.nch O.xd

def Built.wit {𝒮 : Slots} {K : Ctx} {w : ColW B f T} {Z : w.Lt} {c : V4.Core K (w.st Z) f T} (b : Built 𝒮 K w Z c)
    (h : GoodO (w.D Z) c.O.nch c.O.xd) : Wit 𝒮 K w Z c.O :=
  { b with isOver := c.isOver, forced := c.forced, Wt := c.Wt, vol := (b.g Z.W Z.V Z.S Z.N).1, real := c.real, dsig_eq := c.dsig_eq,
           gauge := c.gauge_def, good := h }

structure WPt (𝒮 : Slots) (K : Ctx) : Type 1 where
  B : Base
  f : Fr B.toPre
  T : TwDat B
  w : ColW B f T
  Z : w.Lt
  O : Obj (w.D Z)
  x : Wit 𝒮 K w Z (ofObj O)

def WPt.Is {𝒮 : Slots} {K : Ctx} (p : WPt 𝒮 K) (D : D7) (O : Obj D) : Prop := (⟨D, O⟩ : Σ D : D7, Obj D) = ⟨p.w.D p.Z, p.O⟩

abbrev PinT (𝒮 : Slots) (Bd : GlobalTheory.Fc.BdT) : Type 1 := ∀ (K : Ctx) (p : WPt 𝒮 K) (c : ℝ), Bd (p.w.D p.Z) p.O c → Prop

def linkOf {𝒮 : Slots} {Bd : GlobalTheory.Fc.BdT} (P : PinT 𝒮 Bd) : GlobalTheory.Fc.LkT Bd := fun K β c b =>
  ∃ (p : WPt 𝒮 K) (b' : Bd (p.w.D p.Z) p.O c), P K p c b' ∧
    (⟨β.D, β.O, b⟩ : Σ (D : D7) (O : Obj D), Bd D O c) = ⟨p.w.D p.Z, p.O, b'⟩

end GlobalTheory.Mem.Top.Bl

end
end
