module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LargeFor
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferModels

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OverIx
noncomputable section

namespace GlobalTheory.Mem.Top.Bl

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab _root_.Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.GroupRetwisting NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

abbrev GeoP : Type 1 := ∀ D : D7, Formalism.L2.Pj.Core D → DivX D → Prop

def anyGeometry : GeoP := fun _ _ _ => True

section Reading

open _root_.Formalism.L2.DIV _root_.Formalism.L2.Indef _root_.Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
  {Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0}

def OverIx (Z : R3.ReadL R F X0 Y) (σ : D.what₂.FT) (c : A3.fam3.base3.Ix) : Prop :=
  ∀ i : Fin D.R.m, D.what₂.isot ((i : ℕ) + 1) σ ≤
    Submodule.span ℂ ((Z.jW i) '' ((R3.s0Of R F).Wp i c : Set (Fin ((R3.s0Of R F).dW i) → D.what₂.LL)))

def LamAre (Z : R3.ReadL R F X0 Y) (Xd : DivX D) : Prop :=
  ∃ lab : D.what₂.FT → A3.fam3.base3.Ix, (∀ σ, (∃ c, OverIx Z σ c) → OverIx Z σ (lab σ)) ∧
    ∀ (i : Fin D.R.m) (σ : D.what₂.FT) (e : D.what₂.LL →+* ℂ), e ≠ D.what₂.embLL →
      (D.what₂.isot ((i : ℕ) + 1) σ ≠ ⊥ →
        Xd.logLam ((i : ℕ) + 1) σ e = Real.log ((R3.s0Of R F).lam i A3.A.μ0 (lab σ) (InfinitePlace.mk e))) ∧
      (D.what₂.isot ((i : ℕ) + 1) σ = ⊥ → Xd.logLam ((i : ℕ) + 1) σ e = 0)

end Reading

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B}

structure OAt (Γ : GeoP) {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)} (t : RowsT K w Z Wt p0)
    (X : DivX (w.D Z)) : Type 1 where
  geo : Γ (w.st Z).toD7 t.r.z.core.toCore X
  lam : LamAre t.r.Z X

def OX (Γ : GeoP) : OComponent₂ := fun _ _ _ _ _ _ _ O t => OAt Γ t O.X

end GlobalTheory.Mem.Top.Bl

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemSupportBDIff
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.ChernReg
open scoped TensorProduct

namespace GlobalTheory.ShFam

section Pull

variable {X Z : Scheme.{0}} [IsIntegral X] (B : EffCartierData Z) (f : X ⟶ Z)
  (h : f (genericPoint X) ∉ B.idealSheaf.support)

def pullEqn (i : B.ι) {y : X} (hy : f y ∈ B.U i) : X.functionFieldˣ :=
  have hg : genericPoint X ∈ f ⁻¹ᵁ B.U i := gen_mem (x := y) hy
  Units.mk0 (fnOf (f ⁻¹ᵁ B.U i) hg (f.app _ (B.f i))) (UnitAt.ne_zero ((unitAt_fnOf_iff hg _ _).2 (by
    rw [← Scheme.preimage_basicOpen]
    exact not_not.1 (mt (B.mem_support_iff i hg).2 h))))

theorem germOf_pullEqn {i i' : B.ι} {y : X} (hi : f y ∈ B.U i) (hi' : f y ∈ B.U i') :
    germOf y (pullEqn B f h i hi) = germOf y (pullEqn B f h i' hi') := by
  obtain ⟨u, hu⟩ := ((B.associated_germ i i' _ hi hi').map (f.stalkMap y).hom)
  rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.germ_stalkMap_apply] at hu
  have e := congrArg (algebraMap _ X.functionField) hu
  rw [map_mul, algebraMap_germ (U := f ⁻¹ᵁ B.U i) hi, algebraMap_germ (U := f ⁻¹ᵁ B.U i') hi'] at e
  exact germOf_eq_iff.2 ⟨u, u.isUnit, (eq_div_iff (Units.ne_zero _)).2 ((mul_comm _ _).trans e)⟩

def pullDiv : CartierDiv X :=
  show cartierGroup X from ⟨fun y => germOf y (pullEqn B f h _ (B.exists_mem (f y)).choose_spec), fun y =>
    ⟨f ⁻¹ᵁ B.U _, (B.exists_mem (f y)).choose_spec, pullEqn B f h _ (B.exists_mem (f y)).choose_spec,
      fun _ hz => germOf_pullEqn B f h _ hz⟩⟩

end Pull

section Comb

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

def qDiv {C : CxSt F} (A : Adl C Y) : ℚ ⊗[ℤ] Y.Dv := ((A.n : ℕ) : ℚ)⁻¹ ⊗ₜ A.D



omit [NumberField F] in
def curvMet {σ : F →+* ℂ} {Δ : Y.Dv} (m : Var.Met Y σ Δ) : ChartForm Y.str σ Y.dim :=
  fun c y => ddcForm (m.wt (Var.eqn Δ y)) c y

variable {ι : Type} [Fintype ι] (ρ : ι → Adl (cxSt F) Y) (t : ι → ℚ) (g : ∀ σ, Pts Y σ → ℝ)

def combDen : ℕ+ := ⟨∏ i, (t i / ((ρ i).n : ℕ)).den, Finset.prod_pos fun _ _ => Rat.den_pos _⟩

def combNum (i : ι) : ℤ := ((combDen ρ t : ℕ) * (t i / ((ρ i).n : ℕ))).num

theorem combNum_mul (i : ι) : (combNum ρ t i : ℚ) * ((ρ i).n : ℕ) = (combDen ρ t : ℕ) * t i := by
  obtain ⟨c, hc⟩ : (t i / ((ρ i).n : ℕ)).den ∣ (combDen ρ t : ℕ) := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  have e : ((combDen ρ t : ℕ) : ℚ) * (t i / ((ρ i).n : ℕ)) = ((c * (t i / ((ρ i).n : ℕ)).num : ℤ) : ℚ) := by
    rw [hc, Nat.cast_mul, mul_right_comm, Rat.den_mul_eq_num, mul_comm, Int.cast_mul, Int.cast_natCast]
  rw [combNum, e, Rat.num_intCast, ← e, mul_assoc, div_mul_cancel₀ _ (Nat.cast_ne_zero.2 (ρ i).n.ne_zero)]

def combEqn (x : Y.X) : Y.Fnˣ := ∏ i, eqn (ρ i).D x ^ combNum ρ t i

def comb : Adl (cxSt F) Y where
  D := ∑ i, combNum ρ t i • (ρ i).D
  n := combDen ρ t
  m σ := show Var.Met Y σ _ from
    { h := fun e y => ‖Var.tv e (combEqn ρ t (under y)) y‖ ^ 2 *
        Real.exp (2 * (∑ i, combNum ρ t i * lnAdl (ρ i) σ y - (combDen ρ t : ℕ) * g σ y))
      nonneg := fun _ _ => by positivity
      trans := fun e e' y he he' => by rw [← mul_assoc, ← mul_pow, ← norm_mul, Var.tv_mul he he'] }
  ci := 0
  lg v e y := Real.log (e.w (valAt y.1 (combEqn ρ t (below y.1) /
    eqn (∑ i, combNum ρ t i • (ρ i).D) (below y.1) : Y.Fn))) + ∑ i, combNum ρ t i * (ρ i).lg v e y

theorem qDiv_comb : qDiv (comb ρ t g) = ∑ i, t i • qDiv (ρ i) := by
  simp only [qDiv, comb, TensorProduct.tmul_sum, ← TensorProduct.smul_tmul, TensorProduct.smul_tmul', zsmul_eq_mul,
    smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => congrArg (· ⊗ₜ _) ?_
  have h₁ : ((combDen ρ t : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (combDen ρ t).ne_zero
  have h₂ : (((ρ i).n : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (ρ i).n.ne_zero
  field_simp
  rw [combNum_mul]

end Comb

section Weights

variable {T : Type} {N : ℕ}

def varpi (j : ℕ) (i : Fin N) : ℚ := if (i : ℕ) < j then 0 else -1


open Classical in
def fund (τ : T) (i : Fin N) : T → Fin N → ℝ := fun τ' a => if τ' = τ ∧ a ≤ i then 1 else 0

def coef (u : T → Fin N → ℝ) (τ : T) (i : Fin N) : ℝ := if h : (i : ℕ) + 1 < N then u τ i - u τ ⟨i + 1, h⟩ else u τ i

def ratOf (r : ℝ) : ℚ := Classical.epsilon fun q : ℚ => r = q

end Weights

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ} (Φ : s.Flag)

theorem mem_support_BD_iff (k : s.Comp) (y : (Φ.C k).Y.X) :
    ((Φ.C k).π ≫ genι s.T.Z) y ∈ s.T.BD.idealSheaf.support ↔ (Φ.C k).π y ∈ genBd s.T.Z :=
  ⟨fun h => mem_genBd_iff.2 (s.T.BD_supp _ h), s.T.BD_pos _⟩

def bdPull (k : s.Comp) : (Φ.C k).Y.Dv :=
  pullDiv s.T.BD ((Φ.C k).π ≫ genι s.T.Z) fun h => CartierDiv.genericPoint_notMem_supp (Φ.C k).bd
    (((Φ.C k).bd_supp _).2 ((mem_support_BD_iff Φ k _).1 h))


variable (S) in
abbrev rootExp (x : DV.Rt D.what₂.Tau N) : Letter S.Dw → ℤ := rootEx S.Dw (DV.tauEmb D x.1) x.2

def qL (k : s.Comp) (u : D.what₂.Tau → Fin N → ℚ) : ℚ ⊗[ℤ] (Φ.C k).Y.Dv :=
  -∑ x : DV.Rt D.what₂.Tau N, u x.1 x.2 ⊗ₜ divOf (Φ.C k) (rootExp S x)

abbrev RefMets : Type :=
  ∀ k σ (n : Letter S.Dw → ℤ), (cxSt D.what₂.LL).Met (Φ.C k).Y σ (divOf (Φ.C k) n)

def offBd (k : s.Comp) (σ : D.what₂.LL →+* ℂ) : Set (Pts (Φ.C k).Y σ) := {y | (Φ.C k).π (under y) ∉ genBd s.T.Z}


open Classical in
def extBd {k : s.Comp} {σ : D.what₂.LL →+* ℂ} (f : Pts (Φ.C k).Y σ → ℝ) (y : Pts (Φ.C k).Y σ) : ℝ :=
  if y ∈ offBd Φ k σ then f y else limsup f (𝓝[offBd Φ k σ] y)

variable {Φ} (hm : ∀ k, Mets (Φ.C k) (cxSt D.what₂.LL)) (h0 : RefMets Φ)

def phW (k : s.Comp) (σ : D.what₂.LL →+* ℂ) (u : D.what₂.Tau → Fin N → ℝ) (y : Pts (Φ.C k).Y σ) : ℝ :=
  2 * ∑ x : DV.Rt D.what₂.Tau N, u x.1 x.2 * lnRatio (hm k none σ (rootExp S x)) (h0 k σ (rootExp S x)) y

def thW (k : s.Comp) (σ : D.what₂.LL →+* ℂ) (u : D.what₂.Tau → Fin N → ℝ) : ChartForm (Φ.C k).Y.str σ (Φ.C k).Y.dim :=
  fun c y ξ => -∑ x : DV.Rt D.what₂.Tau N, u x.1 x.2 * curvMet (h0 k σ (rootExp S x)) c y ξ

def CommonConst (om : ∀ k σ, ChartForm (Φ.C k).Y.str σ (Φ.C k).Y.dim) (E : ∀ k σ, ChartMap (Φ.C k).Y.str σ (Φ.C k).Y.dim)
    (a K δ : ℝ) : Prop :=
  0 ≤ a ∧ 0 ≤ K ∧ 0 < δ ∧ ∀ k σ τ (i : Fin N), (i : ℕ) + 1 < N →
    IsRegConst (om k σ) (thW h0 k σ (fund τ i)) (rho (om k σ) (E k σ) (phW hm h0 k σ (fund τ i))) a K δ


variable (s) in
def dirOf (b : ℕ) (η : ℚ) (μ : Fin N → ℤ) : D.what₂.Tau → Fin N → ℚ :=
  fun _ i => (2 * b * s.T.m0 : ℕ) * varpi j i + η * μ i


variable (s Φ) in
structure PolDat : Type where

  b : ℕ
  b_pos : 0 < b

  η : ℚ
  η_pos : 0 < η

  μ : Fin N → ℤ
  μ_anti : StrictAnti μ

  ab : ∀ k, Adl (cxSt D.what₂.LL) (Φ.C k).Y
  ab_div : ∀ k, qDiv (ab k) = qL Φ k (dirOf s b η μ) - 1 ⊗ₜ (b • bdPull Φ k)
  ab_ample : ∀ k, (Φ.C k).Y.ample (ab k).D
  ab_model : ∀ k, ∃ (M : TrueGeo.Model (Φ.C k).Y) (L : HermLB M.p) (q : ℕ+), (ab k).Induced M L q 0 ∧ ArInt.NefFib L
  ab_smooth : ∀ k σ, (cxSt D.what₂.LL).mSmooth _ σ _ ((ab k).m σ)

  om : ∀ k σ, ChartForm (Φ.C k).Y.str σ (Φ.C k).Y.dim
  om_kaehler : ∀ k σ, IsKaehlerForm ((Φ.C k).Y.an σ) (om k σ)
  om_conj : ∀ k σ σ' (ι : Pts (Φ.C k).Y σ' → Pts (Φ.C k).Y σ), IsConjMap ι → ∀ W φ,
    IsPotential ((Φ.C k).Y.an σ) (om k σ) W φ → IsPotential ((Φ.C k).Y.an σ') (om k σ') (ι ⁻¹' W) (φ ∘ ι)

  c₀ : ℝ
  c₀_pos : 0 < c₀
  curv_ge : ∀ k σ (c : AlgChart (Φ.C k).Y.str σ (Φ.C k).Y.dim), ∀ y ∈ c.e.source, ∀ ξ,
    c₀ * om k σ c y ξ ≤ curvMet ((ab k).m σ) c y ξ / ((ab k).n : ℕ)

  exph : ∀ k σ, ChartMap (Φ.C k).Y.str σ (Φ.C k).Y.dim
  exph_is : ∀ k σ, IsExph (om k σ) (exph k σ)
  exph_conj : ∀ k σ σ' (ι : Pts (Φ.C k).Y σ' → Pts (Φ.C k).Y σ), IsConjMap ι → ConjComm ι (exph k σ) (exph k σ')

  a : ℝ

  K : ℝ

  δ : ℝ
  const : (∃ a' K' δ', CommonConst hm h0 om exph a' K' δ') → CommonConst hm h0 om exph a K δ

namespace PolDat

variable {hm h0} (P : PolDat s Φ hm h0)

def m : ℕ := 2 * P.b * s.T.m0

def bd (k : s.Comp) : (Φ.C k).Y.Dv := P.b • bdPull Φ k

def dirQ : D.what₂.Tau → Fin N → ℚ := dirOf s P.b P.η P.μ

def dir : D.what₂.Tau → Fin N → ℝ := fun τ i => P.dirQ τ i

def regFund (k : s.Comp) (σ : D.what₂.LL →+* ℂ) (τ : D.what₂.Tau) (i : Fin N) (t : ℝ) (y : Pts (Φ.C k).Y σ) : ℝ :=
  if (i : ℕ) + 1 < N then rho (P.om k σ) (P.exph k σ) (phW hm h0 k σ (fund τ i)) y t + P.K * t ^ 2
  else extBd Φ (phW hm h0 k σ (fund τ i)) y

def reg (k : s.Comp) (σ : D.what₂.LL →+* ℂ) (u : D.what₂.Tau → Fin N → ℝ) (t : ℝ) (y : Pts (Φ.C k).Y σ) : ℝ :=
  ∑ τ, ∑ i, coef u τ i * P.regFund k σ τ i t y

variable (k : s.Comp) (σ : D.what₂.LL →+* ℂ)

def gens (B : ℝ) : Option (DV.Rt D.what₂.Tau N) → Adl (cxSt D.what₂.LL) (Φ.C k).Y := fun o => o.elim (P.ab k) fun x =>
  adlOf (Φ.C k) (fun _ => h0 k) (rootSym S.Dw (ArIn.ind (setB κ B)) none (DV.tauEmb D x.1) x.2)

def mbarQ (B : ℝ) (u : D.what₂.Tau → Fin N → ℚ) (r : ℚ) : Adl (cxSt D.what₂.LL) (Φ.C k).Y :=
  comb (P.gens k B) (fun o => o.elim r fun x => -(u x.1 x.2 - r * P.dirQ x.1 x.2))
    fun σ y => P.reg k σ (fun τ i => u τ i - r * P.dir τ i) (Real.exp (-((r : ℝ) ^ 2)⁻¹)) y / 2

end PolDat

variable {hm h0}


open Classical in
def mbarOf (P : PolDat s Φ hm h0) (B : ℝ) (u : D.what₂.Tau → Fin N → ℝ) (r : ℚ) (k : s.Comp) :
    Adl (cxSt D.what₂.LL) (Φ.C k).Y :=
  if (∀ τ i, ∃ q : ℚ, u τ i = q) ∧ 0 < r then P.mbarQ k B (fun τ i => ratOf (u τ i)) r else Adl.triv _ _

end GlobalTheory.ShFam
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsExtendResidue
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField TopologicalSpace IsLocalRing
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EigenSplit GlobalTheory.HTLat GlobalTheory.ShFam GlobalTheory.TotalFrame GlobalTheory.FlagPts Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts
open Formalism.MainNotions.DIV.Cons (SCF intO)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LocM

section Family

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

variable {P : ∀ B : Mdl Y i₀, Lat B → Prop}


open Classical in
def FlagFam.lat {Z : Mdl Y i₀} (s : FlagFam P Z) : Lat Z := if h : ∃ L : Lat Z, s.1 = allSteps L then h.choose else Lat.top Z


def Mdl.inclV (Z : Mdl Y i₀) : i₀.c.V W →+* Z.i.c.V W :=
  ((IntermediateField.inclusion Z.le).toRingHom.comp (i₀.c.V W).subtype).codRestrict _ fun a => a.2

end Family

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ}

namespace At

variable (ct : At S κ p)

section Reduction

abbrev V₀ : Type := κ.c.V ct.W

abbrev kbar : Type := AlgebraicClosure (ResidueField ct.V₀)

def ρ₀ : ct.V₀ →+* ct.kbar := (algebraMap (ResidueField ct.V₀) ct.kbar).comp (residue ct.V₀)

abbrev LaBar : Type := ct.kbar ⊗[ℤ] S.Dw.La

def eigLat (σ : D.host.E →+* ℂ) : Submodule ct.V₀ (ct.V₀ ⊗[ℤ] S.Dw.La) :=
  eigenSub (baseChangeAction ct.V₀ (Module.toModuleEnd ℤ S.Dw.La : 𝓞 D.host.E →+* _)) (embV κ.c ct.W σ)

def redLa : ct.V₀ ⊗[ℤ] S.Dw.La →ₗ[ℤ] ct.LaBar := ct.ρ₀.toIntAlgHom.toLinearMap.rTensor S.Dw.La

def eigBar (τ : PsiT D) : Submodule ct.kbar ct.LaBar := Submodule.span ct.kbar (ct.redLa '' ct.eigLat (embOf D τ))

instance : FiniteDimensional ct.kbar ct.LaBar :=
  have := S.Dw.fin
  have : Module.Finite ℤ S.Dw.La := .trans (𝓞 D.host.E) _
  Module.Finite.base_change ℤ _ _

abbrev FlP : Type := Flags ct.kbar fun τ : PsiT D => ↥(ct.eigBar τ)

def FlP.sub {ct : At S κ p} (F : ct.FlP) (τ : PsiT D) (i : ℕ) : Submodule ct.kbar ct.LaBar :=
  (F.step τ i).map (ct.eigBar τ).subtype

abbrev LaP (_ct : At S κ p) : Type :=
  S.Dw.La ⧸ (Ideal.span {(p : 𝓞 D.host.E)} • ⊤ : Submodule (𝓞 D.host.E) S.Dw.La)

def Sum1 : Type := {l : Submodule (𝓞 D.host.E) ct.LaP // (∃ l', IsCompl l l') ∧
  Nonempty (l ≃ₗ[𝓞 D.host.E] (𝓞 D.host.E ⧸ Ideal.span {(p : 𝓞 D.host.E)}))}

def Sum1.bar {ct : At S κ p} (l : ct.Sum1) : Submodule ct.kbar ct.LaBar :=
  Submodule.span ct.kbar {s | ∃ a : S.Dw.La, Submodule.Quotient.mk a ∈ l.1 ∧ s = 1 ⊗ₜ a}

def psiBar : LinearMap.BilinForm ct.kbar ct.LaBar := S.Dw.EF.baseChange ct.kbar

def locus (l : ct.Sum1) : Closeds ct.FlP :=
  between j (fun τ => l.bar.submoduleOf (ct.eigBar τ)) fun τ => (ct.psiBar.orthogonal l.bar).submoduleOf (ct.eigBar τ)

end Reduction

section Point

variable {Z : ct.Mdl} (y : ct.Pt Z)

def lieStep (σ : D.host.E →+* ℂ) (r : ℕ) :
    letI : Fact p.Prime := ⟨ct.hp⟩; letI := A.H.starRing; Submodule ↥y.C.S (ct.htPt y).V :=
  letI : Fact p.Prime := ⟨ct.hp⟩
  letI := A.H.starRing
  Submodule.span ↥y.C.S {w | ∃ (x : LieG (ct.htPt y).Gt) (u : Vecs S.Dw (ct.Y Z.i).t ↥y.C.S) (i : Fin (S.Dw.mult σ)),
    Z.FlagAt y.gen u ∧ (i : ℕ) < r ∧
    u σ i = spMap (dualMap (intO ↥y.C.S).subtype) ≫ ((ct.htPt y).lieCmp x).1.left ≫ htToModel (ct.dat y) ∧
    w = (ct.htPt y).bLie x}

def htStep (τ : PsiT D) (i : ℕ) :
    letI : Fact p.Prime := ⟨ct.hp⟩; letI := A.H.starRing; Submodule ↥y.C.S (ct.htPt y).V :=
  letI : Fact p.Prime := ⟨ct.hp⟩
  letI := A.H.starRing
  if i ≤ j then ct.lieStep y (embOf D τ) i
  else (ct.htPt y).eigV (embInt y.P (embOf D τ)) ⊓
    (ct.htPt y).pairV.orthogonal (ct.lieStep y (conjEmb (embOf D τ)) (N - i))

def LevelMatch (t : (htpTrue ct).Tp y) (a : S.Dw.La) : Prop :=
  letI : Fact p.Prime := ⟨ct.hp⟩
  (Tate.lev t 1).left ≫ abVarι y.P = y.P.y ≫ ((ct.Y Z.i).oF.etaA a ^ (Z.i.l.A / p)).left

def redGraph (ρ : ↥(intO ↥y.C.S) →+* ct.kbar) : AddSubgroup ((htpTrue ct).TC y × ct.LaBar) :=
  AddSubgroup.closure {q | ∃ (c : ↥(intO ↥y.C.S)) (t : (htpTrue ct).Tp y) (a : S.Dw.La), ct.LevelMatch y t a ∧
    q = ((show (ct.fld y).C from c.1) • (htpTrue ct).iT y t, ρ c ⊗ₜ a)}

def redSub (ρ : ↥(intO ↥y.C.S) →+* ct.kbar) (F : Submodule (ct.fld y).C ((htpTrue ct).TC y)) :
    Submodule ct.kbar ct.LaBar := Submodule.span ct.kbar {s | ∃ w ∈ F, (w, s) ∈ ct.redGraph y ρ}

end Point

def SpPt (Z : ct.Mdl) : Type :=
  {x : Sp ct.kbar ⟶ Z.X // x ≫ Z.s ≫ spMap Z.inclV = spMap ct.ρ₀}

def IsRedFlag {Z : ct.Mdl} (x : ct.SpPt Z) (F : ct.FlP) : Prop :=
  p ∣ Z.i.l.A ∧ ∃ (y : ct.Pt Z) (ρ : ↥(intO ↥y.C.S) →+* ct.kbar), spMap ρ ≫ y.z = x.1 ∧
    ∀ τ i, F.sub τ i = ct.redSub y ρ (ct.htStep y τ i)


open Classical in
def redFlag {Z : ct.Mdl} (x : ct.SpPt Z) : ct.FlP :=
  if h : ∃ F, ct.IsRedFlag x F then h.choose else Classical.arbitrary _


open Classical in
def diffExpo (_ct : At S κ p) (l : PsiT D → ℕ → ℤ) (σ : D.host.E →+* ℂ) : ℤ :=
  ∑ t : D.what₂.Tau, if σ = DV.tauEmb D t then ∑ i ∈ Finset.Icc (j + 1) N, l (D.eTau t) i else 0

def degLatPiece {Z B : ct.Mdl} (L : Lat B) {k : Type} [Field k] (c : Curve k Z.X) (τ : PsiT D) (i : ℕ) : ℤ :=
  c.degLat L (-ct.expo (indWt τ i))

end At

def crhOf (ct : At S κ p) (P : ∀ B : ct.Mdl, Lat B → Prop) (hf : ∀ Z, FlagFam P Z) : CrHSt ct (flgOf ct P) where
  nefHT Z l := ∀ c : Curve ct.Fbar (ct.flagCl Z (hf Z).1).X,
    0 ≤ -∑ᶠ τ, ∑ i ∈ Finset.Icc 1 N, l τ i * (ct.degLatPiece (hf Z).lat c τ i : ℝ)
  descK Z l := Descends (ct.flagCl Z (hf Z).1) (hf Z).lat κ.l (ct.expo l) (ct.diffExpo l)
  bdryLoci Z := ∃ s : Set ct.Sum1, s.Finite ∧
    (∀ x : ct.SpPt (ct.flagCl Z (hf Z).1), (∃ z, ¬ Mdl.abP _ (x.1 z)) → ∃ l ∈ s, ct.redFlag x ∈ ct.locus l) ∧
    ∀ l ∈ s, dim (ct.locus l) + D.R.f * (N - 1) = D.R.f * (N * (N - 1) / 2)
  htFlags := hf
  YsP Z := ct.SpPt (ct.flagCl Z (hf Z).1)
  ysBd x := ∃ z, ¬ Mdl.abP _ (x.1 z)
  FlP := ct.FlP
  hFl x := ct.redFlag x
  FlCl := Closeds ct.FlP
  flMem F s := F ∈ s
  flDim := dim
  Sum1 := ct.Sum1
  locus := ct.locus
  bdryLoci_def _ := Iff.rfl
  CrvS Z := Curve ct.Fbar (ct.flagCl Z (hf Z).1).X
  degGr c := ct.degLatPiece (hf _).lat c
  nefHT_def _ _ := Iff.rfl

end GlobalTheory.LocM
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RSideA
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl

namespace GlobalTheory.Mem.R3.Rw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL]
  {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}


set_option maxHeartbeats 4000000 in
def RSideA (z : Dat (w.st Z) w.I hX T Wt) (Wt' : Set B'.places.Pl)
    (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks) : Prop :=
  HEq R'.ψ z.R.ψ ∧ HEq R'.θ z.R.θ ∧ HEq R'.βW z.R.βW ∧ HEq R'.βY z.R.βY ∧ HEq R'.ΛY z.R.ΛY ∧ HEq R'.βV z.R.βV ∧
  HEq R'.ΛV z.R.ΛV ∧ HEq R'.ΛW z.R.ΛW ∧ HEq R'.Pg z.R.Pg ∧ HEq R'.eG z.R.eG ∧ HEq R'.Sb z.R.Sb ∧
  (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
    HEq (R'.cV i').W (z.R.cV i).W ∧ HEq (R'.cV i').ρ (z.R.cV i).ρ ∧ HEq (R'.cV i').nW (z.R.cV i).nW ∧
    HEq (R'.cV i').iW (z.R.cV i).iW) ∧
  ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
    ∀ (ok : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((i : ℕ) + 1)).Ok)
      (ok' : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))).1 ((i' : ℕ) + 1)).Ok)
      (φ : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((i : ℕ) + 1)).EqFun)
      (φ' : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))).1 ((i' : ℕ) + 1)).EqFun),
      (∀ d d', HEq d' d → HEq (MvPolynomial.map (B'.embLL : B'.fields.K →+* ℂ) (φ'.1 d').1)
        (MvPolynomial.map (B.embLL : B.fields.K →+* ℂ) (φ.1 d).1)) →
      HEq (R'.B.jL i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))) ((by with_unfolding_all exact ((Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))).1 ((i' : ℕ) + 1)).res ok' φ' :))))
        (z.R.B.jL i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))) ((by with_unfolding_all exact ((Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((i : ℕ) + 1)).res ok φ :))))


variable (w' Z' hX' T') in
def Kept (Wt' : Set B'.places.Pl) (R : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks)
    (cG : G0 R.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd) : Prop :=
  LevOf (w'.st Z') w'.I (usedOf w'.I T' Wt') R.toLevCh ∧ IsPlacewiseIdentity (w'.st Z') (px := w'.px) R.eG ∧
    GoodSet (w'.st Z') (px := w'.px) (R.eG.trans cG) Xg ∧ MuOf (w'.st Z') w'.I T' Wt' R.mu R.twPl ∧
    IdemClass (D := (w'.st Z').toD7) (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr).A ∧
    R.toRealDat.Pre0 (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr).lv2 ∧ R.IsInert ∧ R.IsTup ∧ R.AllPlaces ∧
    Keep R.toRealDat (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr).lv2 cG ∧
    BrgStd (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr R.toRealDat

end GlobalTheory.Mem.R3.Rw

end
end
