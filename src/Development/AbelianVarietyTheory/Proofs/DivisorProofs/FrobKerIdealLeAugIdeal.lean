module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CubeTheorem.CubeTheoremHolds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightParameterSizeBounds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightParamCoeffSumBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightParamCoeffSumLeAtIndex
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealEqSpanMonomialOfOrdersAlongCompleteDVR
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedSectionExponentShift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSemiAbelianUniformisationOfFiniteExtTrans
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefiningDegenerationDataTauCoordinateUnit

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
set_option autoImplicit false

noncomputable section

open Coalgebra Bialgebra

namespace GlobalTheory.PDiv

def frobKerIdeal (p : ℕ) (R H : Type) [CommRing R] [CommRing H] [Bialgebra R H] : Ideal H :=
  Ideal.span ((fun a : H => a ^ p) '' (augIdeal R H : Set H))

theorem pow_mem_frobKerIdeal {p : ℕ} {R H : Type} [CommRing R] [CommRing H] [Bialgebra R H] {a : H}
    (ha : a ∈ augIdeal R H) : a ^ p ∈ frobKerIdeal p R H :=
  Ideal.subset_span ⟨a, ha, rfl⟩

theorem frobKerIdeal_le_augIdeal {p : ℕ} (hp : p ≠ 0) (R H : Type) [CommRing R] [CommRing H]
    [Bialgebra R H] : frobKerIdeal p R H ≤ augIdeal R H :=
  Ideal.span_le.2 fun _ ⟨a, ha, e⟩ => e ▸ Ideal.pow_mem_of_mem _ ha p (Nat.pos_of_ne_zero hp)

end GlobalTheory.PDiv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TheoremOfCubeAbelianSchemeOverArbitraryBase
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TheoremOfCubeAbelianSchemeOverArbitraryBase
theorem GlobalTheory.CubeTop.cubeTheorem : GlobalTheory.Published.CubeTheorem := GlobalTheory.SpreadingModels.cubeTheorem_holds
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TheoremOfCubeAbelianSchemeOverArbitraryBaseStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theoremOfCubeAbelianScheme_over_arbitrary_base : GlobalTheory.Published.CubeTheorem := by
  first | exact @GlobalTheory.CubeTop.cubeTheorem | exact GlobalTheory.CubeTop.cubeTheorem | (intros; apply GlobalTheory.CubeTop.cubeTheorem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SizeBoundsForFamily
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CovTop.CovSz

theorem pow_five_add_one_lt {y : ℝ} (hy : 16 ≤ y) : y ^ (5 : ℕ) + 1 < y ^ (6 : ℕ) := by
  have h1 : (1 : ℝ) ≤ y ^ (5 : ℕ) := one_le_pow₀ (by linarith)
  have h2 := mul_le_mul_of_nonneg_right hy (zero_le_one.trans h1)
  have e : y ^ (6 : ℕ) = y * y ^ (5 : ℕ) := by ring
  rw [e]
  linarith

end GlobalTheory.CovTop.CovSz

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsModelOf
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.CompHt GlobalTheory.ChowHt
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

namespace GlobalTheory.ImageModel

variable {K V Ω : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω]

structure IsModelOf (Nm : (K →+* ℂ) → V → ℝ) (W : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (D : ℕ)
    {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (L : HermLB p) (ψ : Ω →+* X.functionField)
    (s : W → L.B.Sec) : Prop where

  arith : IsArithVar p D

  normal : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X

  bij : Function.Bijective ψ

  base : ∀ a : 𝓞 K, ψ (algebraMap K Ω (a : K)) = fnOf ⊤ (TopologicalSpace.Opens.mem_top _) (algX p ⊤ a)

  ratio : ∀ (w w' : W) (i : L.B.ι) (h : genericPoint X ∈ L.B.U i),
    ψ (ev w) * fnOf _ h ((s w').f i) = ψ (ev w') * fnOf _ h ((s w).f i)

  bpf : ⨆ w, nonzeroLocus (s w) = ⊤

  fs : ∃ (N n : ℕ) (b : Module.Basis (Fin N) K V) (g : Matrix (Fin N) (Fin n) K)
      (A : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ) (c : Matrix (Fin n) (Fin N) K) (gw : Fin n → W),
      IsFrame Nm W b g A ∧ (∀ k, (gw k : V) = ∑ j, g j k • b j) ∧ (∀ j, b j = ∑ k, c k j • (gw k : V)) ∧
      ∀ (σ : K →+* ℂ) (i : L.B.ι) (y : CxPts p (σ.comp (algebraMap (𝓞 K) K))),
        (L.φ (σ.comp (algebraMap (𝓞 K) K))).φ i y =
        Real.log (∑ a, ‖∑ k, (∑ m, σ (c k m) * A σ m a) * valR y.1 (L.B.U i) ((s (gw k)).f i)‖ ^ 2)

end GlobalTheory.ImageModel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameDenominatorDominantWeightCm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameDenominatorDominantWeightCm
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.GeometryOfNumbersTheory TopologicalSpace Limits
open GlobalTheory.HSApp
open GlobalTheory.LamT (CMPt)
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic

namespace GlobalTheory.LatFull.CMInt

theorem exists_frame_denom_dominant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La → ∀ y : FrPt Xo c z.K, y.x = z.x → 1 ≤ (Dw).p → 1 ≤ (Dw).q → ∀ la : GlobalTheory.AllWt.Weight (Dw), (∀ τ, Antitone (la τ)) → (∀ τ, 1 ≤ gap (la τ) ((Dw).p - 1)) → ∃ N : z.K, N ≠ 0 ∧ ∀ F ∈ GlobalTheory.AllWt.secZ Xo c (GlobalTheory.AllWt.exOf Dw la 0), (∀ v, ∀ w ∈ valSet Xo c (algCls Xo c) v, 0 ≤ w F) → IsIntegral ℤ (N * evR Xo c F y) := by
  intro E _ _ _ H Dw l Xo c _ z f La hz y hy _hp _hq la _hanti _hgap
  classical
  set e : Formalism.L2.Pj.Ix Dw → ℤ := GlobalTheory.AllWt.exOf Dw la 0 with he
  have he0 : e none = 0 := by
    simp [he, GlobalTheory.AllWt.exOf, GlobalTheory.AllWt.wtOf, exZ]
  let k : (E →+* ℂ) → ℕ := fun b => ∑ i : Fin (Dw.mult b), (-(e (some ⟨b, i⟩))).toNat
  let a : ∀ b : E →+* ℂ, Fin (Dw.mult b) → ℕ := fun b i => (e (some ⟨b, i⟩) + (k b : ℤ)).toNat
  have hak : ∀ (b : E →+* ℂ) (i : Fin (Dw.mult b)), e (some ⟨b, i⟩) + (k b : ℤ) = (a b i : ℤ) := by
    intro b i
    have h1 : (-(e (some ⟨b, i⟩))).toNat ≤ k b :=
      Finset.single_le_sum (f := fun i : Fin (Dw.mult b) => (-(e (some ⟨b, i⟩))).toNat)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    simp only [a]
    omega
  obtain ⟨t, ht0, ht⟩ := GlobalTheory.T.exists_commonDenom_framePolynomials_cmPoint E H Dw l Xo c z f La hz e k he0
  obtain ⟨g, s, hg, hgs⟩ := (GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c z.K z.y y).1 (hy.trans hz.2.2.2.1.symm)
  let Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) z.K := fun b => (g b).transpose
  have hYd : ∀ b, (Y b).det ≠ 0 := fun b => by
    simp only [Y, Matrix.det_transpose]; exact (hg b).ne_zero
  have hgY : (fun b => (Y b).transpose) = g := funext fun b => Matrix.transpose_transpose _
  have htK : (t : z.K) ≠ 0 := fun h => ht0 (RingOfIntegers.coe_eq_zero_iff.1 h)
  obtain ⟨N₀, hN₀, hint⟩ := GlobalTheory.LatFull.CMInt.exists_denom_eval
    (fun _ : Formalism.L2.LamCM.FrVar Dw.mult →₀ ℕ => FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 z.K)) ((t : z.K)⁻¹))
    (fun v : Formalism.L2.LamCM.FrVar Dw.mult => Y v.1 v.2.2 v.2.1) (∑ b, ∑ i, a b i)
  refine ⟨N₀ * ∏ b, (Y b).det ^ k b, mul_ne_zero hN₀ (Finset.prod_ne_zero_iff.2 fun b _ => pow_ne_zero _ (hYd b)),
    fun F hF hv => ?_⟩
  obtain ⟨G, hGh, hG⟩ := GlobalTheory.FieldPolyZ.exists_isHomogeneous_secZ E H Dw l Xo c z.K z.y e k a he0 hak F hF
  have h1 := hG y Y s hYd (by rw [hgY]; exact hgs)
  have h2 : N₀ * (∏ b, (Y b).det ^ k b) * evR Xo c F y = N₀ * Formalism.L2.LamCM.evalFr G Y := by
    rw [mul_assoc, h1]
  rw [h2]
  refine hint G hGh fun μ => ?_
  rw [FractionalIdeal.mem_spanSingleton]
  refine ⟨⟨_, ht F hF hv G (fun y' Y' s' hY' h' => hG y' Y' s' hY' h') μ⟩, ?_⟩
  change (t : z.K) * AddMonoidAlgebra.coeff G μ * (t : z.K)⁻¹ = _
  field_simp

end GlobalTheory.LatFull.CMInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameDenominatorDominantWeightCmStatement
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.GeometryOfNumbersTheory TopologicalSpace Limits
open GlobalTheory.HSApp
open GlobalTheory.LamT (CMPt)
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frame_denominator_dominant_weight_cm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La → ∀ y : FrPt Xo c z.K, y.x = z.x → 1 ≤ (Dw).p → 1 ≤ (Dw).q → ∀ la : GlobalTheory.AllWt.Weight (Dw), (∀ τ, Antitone (la τ)) → (∀ τ, 1 ≤ gap (la τ) ((Dw).p - 1)) → ∃ N : z.K, N ≠ 0 ∧ ∀ F ∈ GlobalTheory.AllWt.secZ Xo c (GlobalTheory.AllWt.exOf Dw la 0), (∀ v, ∀ w ∈ valSet Xo c (algCls Xo c) v, 0 ≤ w F) → IsIntegral ℤ (N * evR Xo c F y) := by
  first | exact @GlobalTheory.LatFull.CMInt.exists_frame_denom_dominant | exact GlobalTheory.LatFull.CMInt.exists_frame_denom_dominant | (intros; apply GlobalTheory.LatFull.CMInt.exists_frame_denom_dominant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.Mean4O
open scoped NNReal

namespace GlobalTheory.VertForm

section Algebra

universe u

variable {E : Type u} [AddCommGroup E] [Module ℝ E] {D : ℕ}


variable (E D) in
abbrev Form : Type u := (Π _ : Fin (D + 1), E) →ₘₗ[ℝ] ℝ

variable {num : Form E D} {G : Set E}

end Algebra

section Bundles

variable {k : Type} [CommRing k] {X X' : Scheme.{0}} {p : X ⟶ Sp k} {q : X' ⟶ Sp k}



def NefOver (L : HermLB p) (l : ℕ) : Prop :=
  ∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] (κ : Type)
    [Field κ] [Finite κ] [CharP κ l] [Algebra κ Γ(Z, ⊤)], topologicalKrullDim Z = 1 → 0 ≤ topSelfIntersection κ (L.B.pull i) 1

theorem nefFib_iff (L : HermLB p) : NefFib L ↔ ∀ l : ℕ, l.Prime → NefOver L l :=
  ⟨fun h _ _ Z i _ _ κ _ _ _ _ hZ => h Z i κ hZ, fun h Z i _ _ κ _ _ _ hZ =>
    h (ringChar κ) (CharP.char_is_prime κ _) Z i κ hZ⟩

end Bundles

section Covers

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

def Lies (V' V : Cover Y) (π : V'.X ⟶ V.X) : Prop := ∃ g : V'.G ⟶ V.G, g ≫ V.j = V'.j ≫ π ∧ g ≫ V.π = V'.π

end Covers

end GlobalTheory.VertForm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc

def USame {o Ω o' Ω' : Type} [CommRing o] [Field Ω] [Algebra o Ω] [CommRing o'] [Field Ω'] [Algebra o' Ω']
    {S : ThetaSys o Ω} {S' : ThetaSys o' Ω'} (ρ : S.Real) (ρ' : S'.Real) (lab : S.Gam → S'.Gam) (φ : Ω →+* Ω') : Prop :=
  ∃ (P₀ : PolAV (Sp Ω')) (a : P₀.A.left ⟶ ρ.P.A.left) (a' : P₀.A.left ⟶ ρ'.P.A.left),
    IsGrpPullback P₀.A ρ.P.A (spMap (φ.comp S.R.val.toRingHom)) a ∧ IsGrpPullback P₀.A ρ'.P.A (spMap S'.R.val.toRingHom) a' ∧
    LBIso P₀.L (ρ.P.L.pull a) ∧ LBIso P₀.L (ρ'.P.L.pull a') ∧
    ∀ x, ∃ w : Sp Ω' ⟶ P₀.A.left, w ≫ a = spMap (φ.comp S.R.val.toRingHom) ≫ (ρ.pt x).left ∧
      w ≫ a' = spMap S'.R.val.toRingHom ≫ (ρ'.pt (lab x)).left

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli D l} {cf : Coeff l} {C : UCompact Xo cf}

def UIsLab (X : USetup C) {p : ℕ} [Fact p.Prime] {z : X.M.Z} (ct : UCTrait X p z)
    (yy : X.S.Gam →+ ModN (X.S.r * X.S.N) ct.T.P.D.toPre.X) : Prop :=
  ∃ (c₀ : X.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X.o₁ X.Ω₁) (fg : R'.FG) (frac : ∀ x : X.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b)
    (hth : ∀ x, c₀ * X.S.th x ∈ R') (hev : ∀ x k, c₀ * X.S.ev x k ∈ R')
    (ρ' : (X.S.rechart c₀ hc R' fg frac hth hev).Real) (u' : Sp (ratHull R') ⟶ Xo.XF cf),
    USame X.ρ ρ' (fun x => x) (RingHom.id _) ∧ ρ'.i₀ = X.ρ.i₀ ∧ spMap (ratHull R').val.toRingHom ≫ u' = X.uΩ ∧
    R' ≤ X.M.O ((gPt p ≫ ct.y) (closedPoint (PadicAlgCl p))) ∧
    ∃ (G : Over (Sp (ratHull R'))) (_ : GrpObj G) (α : G.left ⟶ ρ'.P.A.left) (β : G.left ⟶ Xo.univ.t.G.left),
      IsGrpPullback G ρ'.P.A (spMap (toRat R')) α ∧ IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β ∧
      LBIso (ρ'.P.L.pull α) (Xo.univ.t.PP.L.pull β) ∧
      ∃ y₀ : R' →+* PadicAlgCl p, (∀ a : R', y₀ a = X.M.val (gPt p ≫ ct.y) a) ∧
        ∃ (u : ρ'.UTest p y₀) (lb : u.Lab) (j : u.D.toPre.X ≃+ ct.T.P.D.toPre.X),
          (∀ χ, lb.q χ = ct.sc * (ct.T.be (j χ) (j χ) : ℝ) / 2) ∧
          (∀ a χ, lb.yy a = QuotientAddGroup.mk χ → yy a = QuotientAddGroup.mk (j χ)) ∧
          ∀ (m : ℕ) (a : 𝓞 E) (pk pk' : QkPt u.D.toPre (PadicAlgCl p) m) (x x' : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)
            (w w' : Sp (PadicAlgCl p) ⟶ G.left), 1 ≤ m → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x →
            QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk' x' → w ≫ α = x.left ≫ u.φ → w' ≫ α = x'.left ≫ u.φ →
            w' ≫ β = w ≫ β ≫ (Xo.univ.t.act.act a).left → CongMod m (j pk'.y) (a • j pk.y)

structure UDeep (X₁ : USetup C) where

  X : USetup C
  [alg : Algebra X₁.Ω₁ X.Ω₁]
  fd : FiniteDimensional X₁.Ω₁ X.Ω₁
  gal : IsGalois X₁.Ω₁ X.Ω₁

  pt : X.uΩ = spMap (algebraMap X₁.Ω₁ X.Ω₁) ≫ X₁.uΩ

  q : X.M.Z ⟶ X₁.M.Z
  fin : IsFinite q
  gen : X.M.pt ≫ q = spMap (algebraMap X₁.Ω₁ X.Ω₁) ≫ X₁.M.pt
  comp : q ≫ X₁.π = X.π

  m : ℕ
  sq : X.S.N = m ^ 2
  dvd : X₁.S.r * X₁.S.N ∣ m

  lab : X₁.S.Gam →+ X.S.Gam
  same : USame X₁.ρ X.ρ lab (algebraMap X₁.Ω₁ X.Ω₁)
  lab_range : ∀ x : X.S.Gam, ∃ a, lab a = (X.S.r * X.S.N / (X₁.S.r * X₁.S.N)) • x

attribute [instance] UDeep.alg

namespace UDeep

variable {X₁ : USetup C} (D : UDeep X₁)

@[reducible] def lift {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z} (ct : UCTrait X₁ p z₁) (y : Sp (OO p) ⟶ D.X.M.Z)
    (h : y ≫ D.q = ct.y) : UCTrait D.X p (y (cPt p)) where
  y := y
  cen := rfl
  T := ct.T
  ι := ct.ι
  int := ct.int
  comm := by rw [← D.comp, ← Category.assoc y, h, ct.comm]

def Compat {Y : Type} [AddCommGroup Y] (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) Y)
    (yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) Y) : Prop :=
  ∀ a μ, yy₁ a = QuotientAddGroup.mk μ →
    yy (D.lab a) = QuotientAddGroup.mk ((D.X.S.r * D.X.S.N / (X₁.S.r * X₁.S.N)) • μ)

end UDeep

end GlobalTheory.UPoinc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinHomIffLinEnd
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MumFam

def GAdj {S : Scheme.{0}} {G₁ G₂ : Over S} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂]
    (L₁ : LB G₁.left) (L₂ : LB G₂.left) (u : G₁ ⟶ G₂) (u' : G₂ ⟶ G₁) : Prop :=
  LBIso (cubeLB G₂ ![fst G₁ G₂ ≫ u, snd G₁ G₂] L₂) (cubeLB G₁ ![fst G₁ G₂, snd G₁ G₂ ≫ u'] L₁)

def adjVal {S : Scheme.{0}} {T G₁ G₂ : Over S} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂]
    {L₁ : LB G₁.left} {L₂ : LB G₂.left} {x₁ : Fin 2 → (T ⟶ G₁)} {x₂ : Fin 2 → (T ⟶ G₂)}
    (w : LB.Iso (cubeLB G₂ x₂ L₂) (cubeLB G₁ x₁ L₁)) {Z : Scheme.{0}} (p : Z ⟶ T.left) (z : Z)
    (J₁ : (Z ⟶ G₁.left) → L₁.ι) (J₂ : (Z ⟶ G₂.left) → L₂.ι) : (Z.presheaf.stalk z)ˣ :=
  gm p z _ (w.s (fun I => J₁ (p ≫ (psum G₁ x₁ I.down).left), fun I => J₂ (p ≫ (psum G₂ x₂ I.down).left)))

variable {R : Type} [CommRing R] [IsDomain R] {R' : Type} [CommRing R'] [IsDomain R']

def Adj (Q₁ Q₂ : Data R) (a : Q₁.B ⟶ Q₂.B) (a' : Q₂.B ⟶ Q₁.B) (h : Q₁.X →+ Q₂.X) (h' : Q₂.X →+ Q₁.X) : Prop :=
  IsMonHom a ∧ IsMonHom a' ∧ (∀ y, Q₂.c (h y) = Q₁.c y ≫ a) ∧ (∀ z, Q₁.c (h' z) = Q₂.c z ≫ a') ∧
  ∃ w : LB.Iso (cubeLB Q₂.B ![fst Q₁.B Q₂.B ≫ a, snd Q₁.B Q₂.B] Q₂.M.L)
      (cubeLB Q₁.B ![fst Q₁.B Q₂.B, snd Q₁.B Q₂.B ≫ a'] Q₁.M.L), w.IsGen ∧
    ∀ y y' z J₁ J₂, Good Q₁.M.L z J₁ → Good Q₂.M.L z J₂ →
      val (Q₂.tau (h y) y') (𝟙 _) z J₂ =
        adjVal w (lift (toUnit (TK R) ≫ Q₁.c y) (toUnit (TK R) ≫ Q₂.c y')).left z J₁ J₂ * val (Q₁.tau y (h' y')) (𝟙 _) z J₁

abbrev pol {I : Ideal R} (D : DegData R I) : Data R := Wit.ofDeg D.toPre D.tau_bimult

def RefAt (Q : Data R) (ρ : R →+* R') (D : DegPre R') (e : D.X ≃+ Q.X) (β : D.P.A.left ⟶ Q.B.left) : Prop :=
  letI := D.P.isAb.comm
  ∃ (β₂ : (G2 D.P.A).left ⟶ (G2 Q.B).left) (w : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ Q.B Q.M.L).pull β₂)),
    IsGrpPullback D.P.A Q.B (spMap ρ) β ∧ IsSquare β β₂ ∧ w.IsGen ∧
    (∀ a, (D.c a).left ≫ β = spMap ρ ≫ (Q.c (e a)).left) ∧
    ∀ κ : (TK R').left ⟶ (TK R).left, κ ≫ jK R = jK R' ≫ spMap ρ → ∀ a b z J J', Good Q.M.L z J → Good D.P.L z J' →
      val (D.tau a b) (𝟙 _) z J' =
        lamVal w (lift (toUnit (TK R') ≫ D.c a) (toUnit (TK R') ≫ D.c b)).left z J J' * val (Q.tau (e a) (e b)) κ z J

def IsTens (Q : Data R) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (D'.P.A ⟶ Q.B))
    (xe : D'.X ≃+ (Fin r → Q.X)) : Prop :=
  (∀ i, IsMonHom (pr i)) ∧ Nonempty (IsLimit (Fan.mk D'.P.A pr)) ∧ (∀ z i, D'.c z ≫ pr i = Q.c (xe z i)) ∧
  ∃ w : LB.Iso D'.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W)), w.IsGen ∧
    ∀ y z J J', Good Q.M.L z J → Good D'.P.L z J' →
      val (D'.psi y) (𝟙 _) z J' = gm (D'.xK y) z _ (w.s (fun k => J (D'.xK y ≫ tensφ pr k), J' (D'.xK y))) *
        ∏ i, ∏ j, val (Q.tau (xe y i) (xe y j)) (𝟙 _) z J ^ W i j

def TorusHomOf {S : Scheme.{0}} {X₁ X₂ : Type} [AddCommGroup X₁] [AddCommGroup X₂] (h : X₂ → X₁)
    (t : splitTorus S X₁ ⟶ splitTorus S X₂) : Prop :=
  ∀ χ : X₂, res (fun x _ => show t.left.base x ∈ (⊤ : TopologicalSpace.Opens _) from trivial)
      (pullU t.left ⊤ (charUnit S X₂ χ)) = charUnit S X₁ (h χ)

variable {I : Ideal R} {D₁ D₂ D₃ : DegData R I} {A₁ A₂ A₃ : PolAV (Sp (FractionRing R))} {G₁ G₂ G₃ : Over (Sp R)}
  [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] [GrpObj G₃] [IsCommMonObj G₃]

def LinHom (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (a : D₁.toPre.P.A ⟶ D₂.toPre.P.A)
    (h' : D₂.toPre.X →+ D₁.toPre.X) (g : G₁ ⟶ G₂) : Prop :=
  IsMonHom g ∧ (∀ e, (Over.pullback (thick R I e)).map g ≫ (U₂.gt e).q = (U₁.gt e).q ≫ (Over.pullback (thick R I e)).map a) ∧
    ∀ e, ∃ t : splitTorus (Sp (R ⧸ I ^ (e + 1))) D₁.toPre.X ⟶ splitTorus (Sp (R ⧸ I ^ (e + 1))) D₂.toPre.X,
      TorusHomOf h' t ∧ (U₁.gt e).i ≫ (Over.pullback (thick R I e)).map g = t ≫ (U₂.gt e).i

theorem TorusHomOf.comp {S : Scheme.{0}} {X₁ X₂ X₃ : Type} [AddCommGroup X₁] [AddCommGroup X₂] [AddCommGroup X₃]
    {h : X₂ → X₁} {k : X₃ → X₂} {t : splitTorus S X₁ ⟶ splitTorus S X₂} {s : splitTorus S X₂ ⟶ splitTorus S X₃}
    (ht : TorusHomOf h t) (hs : TorusHomOf k s) : TorusHomOf (fun χ => h (k χ)) (t ≫ s) := fun χ => by
  rw [← ht (k χ), ← hs χ]
  refine unit_ext fun z _ => ?_
  refine ((gm_res (𝟙 _) z (V := ⊤) _ trivial _).trans (gm_pull (𝟙 _) _ z ⊤ trivial _)).trans ?_
  refine Eq.symm (((gm_res (𝟙 _) z (V := ⊤) _ trivial _).trans (gm_pull (𝟙 _) _ z ⊤ trivial _)).trans ?_)
  refine ((gm_res _ z (V := ⊤) _ trivial _).trans (gm_pull _ _ z ⊤ trivial _)).trans ?_
  rfl

theorem TorusHomOf.id {S : Scheme.{0}} (X : Type) [AddCommGroup X] : TorusHomOf (fun χ : X => χ) (𝟙 (splitTorus S X)) :=
  fun χ => unit_ext fun z _ =>
    ((gm_res (𝟙 _) z (V := ⊤) _ trivial _).trans (gm_pull (𝟙 _) _ z ⊤ trivial _)).trans rfl

theorem LinHom.id (U : UnifPre I D₁ A₁ G₁) : LinHom U U (𝟙 _) (AddMonoidHom.id _) (𝟙 G₁) :=
  ⟨inferInstance, fun e => by simp, fun e => ⟨𝟙 _, TorusHomOf.id _, by simp⟩⟩

theorem LinHom.comp {U₁ : UnifPre I D₁ A₁ G₁} {U₂ : UnifPre I D₂ A₂ G₂} {U₃ : UnifPre I D₃ A₃ G₃} {a h' g b k' f}
    (hg : LinHom U₁ U₂ a h' g) (hf : LinHom U₂ U₃ b k' f) : LinHom U₁ U₃ (a ≫ b) (h'.comp k') (g ≫ f) := by
  obtain ⟨g₁, g₂, g₃⟩ := hg
  obtain ⟨f₁, f₂, f₃⟩ := hf
  refine ⟨inferInstance, fun e => ?_, fun e => ?_⟩
  · rw [Functor.map_comp, Functor.map_comp, Category.assoc, f₂, ← Category.assoc, g₂, Category.assoc]
  · obtain ⟨t, ht, hi⟩ := g₃ e
    obtain ⟨s, hs, hj⟩ := f₃ e
    refine ⟨t ≫ s, ht.comp hs, ?_⟩
    rw [Functor.map_comp, ← Category.assoc, hi, Category.assoc, hj, Category.assoc]

theorem linHom_iff_linEnd {U : UnifPre I D₁ A₁ G₁} {a h' g} : LinHom U U a h' g ↔ LinEnd U a h' g := by
  refine ⟨fun ⟨h₁, h₂, h₃⟩ => ⟨h₁, fun e => inferInstance, fun e => ?_, h₂, h₃⟩, fun ⟨h₁, _, _, h₂, h₃⟩ => ⟨h₁, h₂, h₃⟩⟩
  apply pullback.hom_ext
  · simp only [thickMap, Over.pullback_map_left, Category.assoc, pullback.map]
    erw [pullback.lift_fst, pullback.lift_fst, pullback.lift_fst_assoc, Category.comp_id, pullback.lift_fst]
  · simp only [thickMap, Over.pullback_map_left, Category.assoc, pullback.map]
    erw [pullback.lift_snd, pullback.lift_snd, pullback.lift_snd_assoc]

end GlobalTheory.MumFam
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecRatioEqRefl
noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory.Mum

variable {X Y : Scheme.{0}} (L : LB X) {k k' : ℕ}

abbrev secChart (i : Fin 1 → L.ι) : X.Opens := LB.wchart L (fun _ : Fin 1 => 𝟙 X) i

def SecRatioEq (u v : Y ⟶ X) (s₁ s₂ : H0 L k) (t₁ t₂ : H0 L k') : Prop :=
  ∀ i i' : Fin 1 → L.ι,
    (Y.presheaf.map (homOfLE (inf_le_left : u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' ≤ u ⁻¹ᵁ secChart L i)).op).hom
        ((u.app (secChart L i)).hom (s₁.f i)) *
      (Y.presheaf.map (homOfLE (inf_le_right : u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' ≤ v ⁻¹ᵁ secChart L i')).op).hom
        ((v.app (secChart L i')).hom (t₂.f i')) =
    (Y.presheaf.map (homOfLE (inf_le_left : u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' ≤ u ⁻¹ᵁ secChart L i)).op).hom
        ((u.app (secChart L i)).hom (s₂.f i)) *
      (Y.presheaf.map (homOfLE (inf_le_right : u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' ≤ v ⁻¹ᵁ secChart L i')).op).hom
        ((v.app (secChart L i')).hom (t₁.f i'))

def SecCoNonzero (u v : Y ⟶ X) (s : H0 L k) (t : H0 L k') : Prop :=
  ∃ (y : Y) (i i' : Fin 1 → L.ι), y ∈ Y.basicOpen ((u.app (secChart L i)).hom (s.f i)) ∧
    y ∈ Y.basicOpen ((v.app (secChart L i')).hom (t.f i'))

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NearIsIsoOfIsProperOfFinitePresentation
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbDual

section Fibre

open GlobalTheory.NearFibreIso

theorem near_isIso_of_isProper_of_finitePresentation {R : Type} [CommRing R] {Y X : Scheme.{0}} (s : X ⟶ Sp R)
    (f : Y ⟶ X) (K : Type) [Field K] [Algebra R K] [IsProper f]
    [LocallyOfFinitePresentation s] [LocallyOfFinitePresentation (f ≫ s)] [Flat (f ≫ s)]
    [IsIso (pullback.snd f (pullback.fst s (spMap (algebraMap R K))))]
    (x : X) (hx : RingHom.ker (algebraMap R K) = (s x).asIdeal) :
    Near f (MorphismProperty.isomorphisms _) x := by
  obtain ⟨T, T', g, g', f', H, _, ⟨y, rfl⟩, hQ⟩ := near_isFinite s f K x hx
  have := isIso_fibre_of_pullback s f (spMap (algebraMap R K)) H
  obtain ⟨U, U', k, k', f'', H', _, ⟨z, rfl⟩, hQ'⟩ :=
    near_isClosedImmersion (g ≫ s) f' K y (by rw [Scheme.Hom.comp_apply]; exact hx)
  have H'' := H'.paste_vert H
  have := isIso_fibre_of_pullback s f (spMap (algebraMap R K)) H''
  have : IsOpenImmersion (k' ≫ g') :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) H'' inferInstance
  have : Flat (f'' ≫ (k ≫ g) ≫ s) := by
    rw [H''.w_assoc]; infer_instance
  have : LocallyOfFinitePresentation (f'' ≫ (k ≫ g) ≫ s) := by
    rw [H''.w_assoc]; infer_instance
  have h := GlobalTheory.AbMonoIsoAny.near_isIso_of_finitePresentation ((k ≫ g) ≫ s) f'' K z
    (by rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]; exact hx)
  have h' := Near.of_pullback f H'' h
  rwa [Scheme.Hom.comp_apply] at h'

theorem isIso_of_geometric_fibres {S X Y : Scheme.{0}} (p : X ⟶ S) (f : Y ⟶ X) [IsProper f]
    [LocallyOfFinitePresentation p] [LocallyOfFinitePresentation (f ≫ p)] [Flat (f ≫ p)]
    (h : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ S), IsIso (pullback.snd f (pullback.fst p t))) :
    IsIso f := by
  have hn : ∀ y : X, Near f (MorphismProperty.isomorphisms _) y := by
    intro y
    obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (p y)) isOpen_univ
    replace hU : IsAffineOpen U := hU
    let j : Sp Γ(S, U) ⟶ S := hU.fromSpec
    obtain ⟨z, hz⟩ : p y ∈ Set.range j := by rw [hU.range_fromSpec]; exact hyU
    let gX := pullback.fst p j
    let s := pullback.snd p j
    let f' := pullback.snd f gX
    have HX := IsPullback.of_hasPullback p j
    have HY := IsPullback.of_hasPullback f gX
    have HYS := HY.paste_vert HX
    obtain ⟨y', hy', hy's⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := j) y z hz.symm
    have : Flat (f' ≫ s) := MorphismProperty.of_isPullback HYS ‹_›
    have : LocallyOfFinitePresentation (f' ≫ s) := MorphismProperty.of_isPullback HYS ‹_›
    have : IsProper f' := MorphismProperty.of_isPullback HY (inferInstanceAs (IsProper f))
    have : (s y').asIdeal.IsPrime := (s y').isPrime
    let K := AlgebraicClosure (s y').asIdeal.ResidueField
    have hK : RingHom.ker (algebraMap Γ(S, U) K) = (s y').asIdeal := by
      rw [IsScalarTower.algebraMap_eq Γ(S, U) (s y').asIdeal.ResidueField K, ← RingHom.comap_ker,
        (RingHom.injective_iff_ker_eq_bot _).1 (algebraMap (s y').asIdeal.ResidueField K).injective,
        ← RingHom.ker_eq_comap_bot, Ideal.ker_algebraMap_residueField]
    let t : Sp K ⟶ Sp Γ(S, U) := spMap (algebraMap Γ(S, U) K)
    have hi := h K (t ≫ j)
    have : IsIso (pullback.snd f' (pullback.fst s t)) := by
      have H := (IsPullback.of_hasPullback f' (pullback.fst s t)).flip.paste_vert HY.flip
      have H₀ := (IsPullback.of_hasPullback f (pullback.fst p (t ≫ j))).flip
      have hu : (pullback.fst s t ≫ gX) ≫ p = pullback.snd s t ≫ t ≫ j := by
        rw [Category.assoc, HX.w, pullback.condition_assoc]
      have e : pullback.lift _ _ hu ≫ pullback.fst p (t ≫ j) = pullback.fst s t ≫ gX := pullback.lift_fst _ _ _
      have H₁ := IsPullback.of_bot' (h₁₁ := pullback.snd f' (pullback.fst s t)) (v₁₂ := pullback.lift _ _ hu)
        (by rw [e]; exact H) H₀
      exact (MorphismProperty.isomorphisms Scheme.{0}).of_isPullback H₁.flip hi
    have h := near_isIso_of_isProper_of_finitePresentation s f' K y' hK
    have h' := Near.of_pullback f HY.flip h
    rwa [hy'] at h'
  have h := isIso_of_near f (𝟙 _) (fun y => by simpa using hn y)
  have e : f = inv (pullback.fst f (𝟙 X)) ≫ pullback.snd f (𝟙 X) := by
    rw [IsIso.eq_inv_comp, pullback.condition, Category.comp_id]
  rw [e]
  infer_instance

end Fibre

variable {S : Scheme.{0}} {A B D : Over S} [GrpObj A] [GrpObj B] [GrpObj D]

theorem isIso_of_isIso_pullback (hB : IsAbelianScheme B) (hD : IsAbelianScheme D) (x : B ⟶ D)
    (h : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ S), IsIso ((Over.pullback t).map x)) : IsIso x := by
  have := hB.proper
  have := hB.smooth
  have := hD.proper
  have := hD.smooth
  have : IsProper (x.left ≫ D.hom) := by rw [Over.w]; infer_instance
  have : IsProper x.left := IsProper.of_comp x.left D.hom
  have : Flat (x.left ≫ D.hom) := by rw [Over.w]; infer_instance
  have : LocallyOfFinitePresentation (x.left ≫ D.hom) := by rw [Over.w]; infer_instance
  have : IsIso x.left := isIso_of_geometric_fibres D.hom x.left fun Ω _ _ t ↦ by
    have := h Ω t
    have hi : IsIso ((Over.pullback t).map x).left :=
      (Over.forget _).map_isIso ((Over.pullback t).map x)
    have H : IsPullback (pullback.fst B.hom t) ((Over.pullback t).map x).left x.left (pullback.fst D.hom t) := by
      refine IsPullback.of_bot (h₃₁ := t) (v₂₁ := pullback.snd D.hom t) (v₂₂ := D.hom) ?_ ?_
        (IsPullback.of_hasPullback D.hom t)
      · have e : ((Over.pullback t).map x).left ≫ pullback.snd D.hom t = pullback.snd B.hom t :=
          Over.w ((Over.pullback t).map x)
        rw [e, Over.w]
        exact IsPullback.of_hasPullback B.hom t
      · exact (pullback.lift_fst _ _ _).symm
    rw [← H.isoPullback_inv_snd]
    infer_instance
  have : IsIso ((Over.forget _).map x) := ‹_›
  exact isIso_of_reflects_iso x (Over.forget _)

theorem additive_of_cube (hC : GlobalTheory.Published.CubeTheorem) (hA : IsAbelianScheme A) (hB : IsAbelianScheme B)
    {P : LB (A ⊗ B).left} (hP : P.IsLB) (h₁ : Triv (ev P (1 : B ⟶ A) (𝟙 B)))
    (h₂ : Triv (ev P (𝟙 A) (1 : A ⟶ B))) : IsAdditive P ∧ IsAdditive (swap P) := by
  have key : ∀ (T : Over S) (a b c : T ⟶ A ⊗ B),
      evc hP ((a * b * c) ≫ fst A B) ((a * b * c) ≫ snd A B) - evc hP ((a * b) ≫ fst A B) ((a * b) ≫ snd A B) -
        evc hP ((a * c) ≫ fst A B) ((a * c) ≫ snd A B) - evc hP ((b * c) ≫ fst A B) ((b * c) ≫ snd A B) +
        evc hP (a ≫ fst A B) (a ≫ snd A B) + evc hP (b ≫ fst A B) (b ≫ snd A B) +
        evc hP (c ≫ fst A B) (c ≫ snd A B) - evc hP ((1 : T ⟶ A ⊗ B) ≫ fst A B) ((1 : T ⟶ A ⊗ B) ≫ snd A B) = 0 := by
    intro T a b c
    have h := hC S (A ⊗ B) (AbelianSchemeGerms.isAbelianScheme_tensor A B hA hB) P hP T a b c
    have hl := LB.isLB_linComb hP (fun k : Fin 8 ↦ (![a * b * c, a * b, a * c, b * c, a, b, c, 1] k).left)
      ![1, -1, -1, -1, 1, 1, 1, -1]
    have e := (cls_eq_zero_iff hl).2 h
    rw [cls_linComb hP _ _ hl, Fin.sum_univ_eight] at e
    simp only [Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul] at e
    simp only [evc, lift_comp_fst_snd]
    rw [← e]
    abel
  refine ⟨(isAdditive_iff hP).2 fun Y a a' t ↦ ?_, (BirigidLift.isAdditive_swap_iff hP).2 fun Y a t t' ↦ ?_⟩
  · have e := key Y (lift a 1) (lift a' 1) (lift 1 t)
    simp only [MonObj.mul_comp, MonObj.one_comp, lift_fst, lift_snd, _root_.mul_one, _root_.one_mul,
      evc_one_left hP h₁, evc_one_right hP h₂] at e
    rw [← sub_eq_zero, ← e]
    abel
  · have e := key Y (lift 1 t) (lift 1 t') (lift a 1)
    simp only [MonObj.mul_comp, MonObj.one_comp, lift_fst, lift_snd, _root_.mul_one, _root_.one_mul,
      evc_one_left hP h₁, evc_one_right hP h₂] at e
    rw [← sub_eq_zero, ← e]
    abel

theorem IsDual.isIso_of_cls {P : LB (A ⊗ B).left} {Q : LB (A ⊗ D).left} (hP : IsDual A B P) (hQ : IsDual A D Q)
    {x : B ⟶ D} (e : cls P hP.isLB = evc hQ.isLB (fst A B) (snd A B ≫ x)) : IsIso x := by
  obtain ⟨y, hy, -⟩ := hP.univ D Q hQ.isLB hQ.additive
  have e' : cls Q hQ.isLB = evc hP.isLB (fst A D) (snd A D ≫ y) := (cls_eq_iff hQ.isLB (pull_isLB hP.isLB _)).2 hy
  refine ⟨y, BirigidLift.dual_ext hP ?_, BirigidLift.dual_ext hQ ?_⟩
  · rw [← Category.assoc, ← BirigidLift.evc_of_cls hP.isLB hQ.isLB e', ← BirigidLift.evc_of_cls hQ.isLB hP.isLB e,
      Category.comp_id]
  · rw [← Category.assoc, ← BirigidLift.evc_of_cls hQ.isLB hP.isLB e, ← BirigidLift.evc_of_cls hP.isLB hQ.isLB e',
      Category.comp_id]

theorem principalPol_selfDual : GlobalTheory.Published.DualAbelianScheme → GlobalTheory.Published.CubeTheorem →
    ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A →
      ∀ c : GlobalTheory.CechPic.Pic (A ⊗ A).left, GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.IsPrincipalPol A c →
        ∃ (P : LB (A ⊗ A).left) (hP : P.IsLB), GlobalTheory.CechPic.cls P hP = c ∧ GlobalTheory.AbDual.IsDual A A P := by
  intro hD hC S A _ hA c hc
  obtain ⟨P, hP, rfl⟩ := cls_surj c
  refine ⟨P, hP, rfl, ?_⟩
  obtain ⟨a₁, a₂⟩ := additive_of_cube hC hA hA hP ((triv_ev_iff hP _ _).2 hc.1) ((triv_ev_iff hP _ _).2 hc.2.1)
  obtain ⟨D, _, Q, hD', -, q, q'⟩ := hD S A hA
  obtain ⟨x, hx, e⟩ := BirigidLift.exists_hom q q'.additive hP a₁ a₂
  have ix : IsIso x := isIso_of_isIso_pullback hA hD' x fun Ω _ _ s ↦ by
    obtain ⟨L, hL, -, hK, hc'⟩ := hc.2.2 Ω s
    have f := isGrpPullback_pullback A s
    have d := isGrpPullback_pullback D s
    have hA₀ := PolPull.isAbelianScheme_of_isGrpPullback hA f
    have := hA₀.comm
    obtain ⟨g, hg⟩ := AbelianDim.exists_relDim Ω _ hA₀
    have p₀ := PerfectDual.isDual_of_isPerfect hD _ _ hA₀ hA₀ hg hg (isPerfect_lam hL hK)
    obtain ⟨m, m₁, m₂⟩ := exists_prod_pullback f d
    have hQ := pull_isLB q.isLB m
    have q₀ := q.baseChange f d m₁ m₂ hQ ((cls_eq_iff hQ hQ).1 rfl)
    refine p₀.isIso_of_cls q₀ ?_
    have l₁ : IndefiniteRowSideFullHecke.ZeroSectionBase.sqToBase A s ≫ (fst A A).left = (fst _ _ : _ ⟶ (Over.pullback s).obj A).left ≫
        pullback.fst A.hom s :=
      congrArg (fun z ↦ z.left) (lift_fst (IndefiniteRowSideFullHecke.ZeroSectionBase.toBase A s (fst _ _)) (IndefiniteRowSideFullHecke.ZeroSectionBase.toBase A s (snd _ _)))
    have l₂ : IndefiniteRowSideFullHecke.ZeroSectionBase.sqToBase A s ≫ (snd A A).left = (snd _ _ : _ ⟶ (Over.pullback s).obj A).left ≫
        pullback.fst A.hom s :=
      congrArg (fun z ↦ z.left) (lift_snd (IndefiniteRowSideFullHecke.ZeroSectionBase.toBase A s (fst _ _)) (IndefiniteRowSideFullHecke.ZeroSectionBase.toBase A s (snd _ _)))
    rw [← BirigidLift.pull_evc_eq l₁ l₂ m₁ m₂ q.isLB hQ (x := x) (pullback.lift_fst _ _ _).symm, ← e, hc']
    exact cls_cube_two hL _ _ _
  exact isDual_of_iso S A A D P Q q hP x ix hx ((cls_eq_iff hP (pull_isLB q.isLB _)).1 e)

end GlobalTheory.AbDual
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTranspose
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

abbrev SymUnit (r : ℕ) : Type :=
  {b : (Matrix (Fin r) (Fin r) ℤ)ˣ // (b : Matrix (Fin r) (Fin r) ℤ).transpose = b}

def TensO {r : ℕ} (_ : SymUnit r) : Type := Matrix (Fin r) (Fin r) ℤ

namespace TensO

variable {r : ℕ} (s : SymUnit r)

instance : Ring (TensO s) := inferInstanceAs (Ring (Matrix (Fin r) (Fin r) ℤ))

def mat (a : TensO s) : Matrix (Fin r) (Fin r) ℤ := a

def ofMat (a : Matrix (Fin r) (Fin r) ℤ) : TensO s := a

theorem inv_transpose : ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ).transpose =
    ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) := by
  have h1 : ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) * (s.1 : Matrix (Fin r) (Fin r) ℤ) = 1 :=
    Units.inv_mul s.1
  have h2 : (s.1 : Matrix (Fin r) (Fin r) ℤ) * ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) = 1 :=
    Units.mul_inv s.1
  have h3 := congrArg Matrix.transpose h1
  rw [Matrix.transpose_mul, s.2, Matrix.transpose_one] at h3
  calc _ = (((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) * (s.1 : Matrix (Fin r) (Fin r) ℤ)) *
        ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ).transpose := by rw [h1, Matrix.one_mul]
    _ = _ := by rw [Matrix.mul_assoc, h3, Matrix.mul_one]

instance : StarRing (TensO s) where
  star a := ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) * (mat s a).transpose *
    (s.1 : Matrix (Fin r) (Fin r) ℤ)
  star_involutive a := by
    show ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) *
      (((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) * (mat s a).transpose *
        (s.1 : Matrix (Fin r) (Fin r) ℤ)).transpose * (s.1 : Matrix (Fin r) (Fin r) ℤ) = a
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, s.2, inv_transpose]
    have h1 : ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) * (s.1 : Matrix (Fin r) (Fin r) ℤ) = 1 :=
      Units.inv_mul s.1
    simp only [Matrix.mul_assoc]
    rw [h1, Matrix.mul_one, ← Matrix.mul_assoc, h1, Matrix.one_mul]
    rfl
  star_mul a b := by
    show ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) * (mat s a * mat s b).transpose *
        (s.1 : Matrix (Fin r) (Fin r) ℤ) =
      (((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) * (mat s b).transpose *
        (s.1 : Matrix (Fin r) (Fin r) ℤ)) *
      (((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) * (mat s a).transpose *
        (s.1 : Matrix (Fin r) (Fin r) ℤ))
    rw [Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (s.1 : Matrix (Fin r) (Fin r) ℤ), Units.mul_inv, Matrix.one_mul]
  star_add a b := by
    show ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) * (mat s a + mat s b).transpose *
        (s.1 : Matrix (Fin r) (Fin r) ℤ) = _
    rw [Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]
    rfl

theorem star_def (a : TensO s) : star a = ofMat s (((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) *
    (mat s a).transpose * (s.1 : Matrix (Fin r) (Fin r) ℤ)) := rfl

@[simp] theorem mat_one : mat s (1 : TensO s) = 1 := rfl

end TensO

def symUnitOf {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (h : IsUnit (W + W.transpose).det) : SymUnit r :=
  ⟨((Matrix.isUnit_iff_isUnit_det _).2 h).unit, by
    show (W + W.transpose).transpose = W + W.transpose
    rw [Matrix.transpose_add, Matrix.transpose_transpose, add_comm]⟩

end GlobalTheory.Mum

namespace GlobalTheory.Mum

section

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}

def Tens.smulF (T : Tens D D' W) (s : SymUnit r) (a : TensO s) (z : D'.X) : D'.X :=
  T.xe.symm (fun i => ∑ j, TensO.mat s a i j • T.xe z j)

theorem Tens.xe_smulF (T : Tens D D' W) (s : SymUnit r) (a : TensO s) (z : D'.X) (i : Fin r) :
    T.xe (T.smulF s a z) i = ∑ j, TensO.mat s a i j • T.xe z j := by
  simp [Tens.smulF]

def Tens.mod (T : Tens D D' W) (s : SymUnit r) : Module (TensO s) D'.X where
  smul := T.smulF s
  one_smul z := by
    show T.smulF s 1 z = z
    apply T.xe.injective
    funext i
    rw [Tens.xe_smulF]
    simp [TensO.mat_one, Matrix.one_apply, ite_smul]
  mul_smul a b z := by
    show T.smulF s (a * b) z = T.smulF s a (T.smulF s b z)
    apply T.xe.injective
    funext i
    have hmat : TensO.mat s (a * b) = TensO.mat s a * TensO.mat s b := rfl
    simp only [Tens.xe_smulF, hmat, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, mul_smul]
    exact Finset.sum_comm
  smul_zero a := by
    show T.smulF s a 0 = 0
    apply T.xe.injective
    funext i
    simp [Tens.xe_smulF]
  smul_add a z z' := by
    show T.smulF s a (z + z') = T.smulF s a z + T.smulF s a z'
    apply T.xe.injective
    funext i
    simp [Tens.xe_smulF, smul_add, Finset.sum_add_distrib]
  add_smul a b z := by
    show T.smulF s (a + b) z = T.smulF s a z + T.smulF s b z
    apply T.xe.injective
    funext i
    have hmat : TensO.mat s (a + b) = TensO.mat s a + TensO.mat s b := rfl
    simp [Tens.xe_smulF, hmat, Matrix.add_apply, add_smul, Finset.sum_add_distrib]
  zero_smul z := by
    show T.smulF s 0 z = 0
    apply T.xe.injective
    funext i
    rw [Tens.xe_smulF, map_zero]
    exact Finset.sum_eq_zero fun j _ => by
      show (0 : Matrix (Fin r) (Fin r) ℤ) i j • T.xe z j = 0
      simp

theorem Tens.xe_smul (T : Tens D D' W) (s : SymUnit r) (a : TensO s) (z : D'.X) (i : Fin r) :
    letI := T.mod s
    T.xe (a • z) i = ∑ j, TensO.mat s a i j • T.xe z j :=
  T.xe_smulF s a z i

def Tens.act (T : Tens D D' W) (a : Matrix (Fin r) (Fin r) ℤ) : D'.P.A ⟶ D'.P.A :=
  T.lim.lift (Fan.mk D'.P.A fun i => ∏ j, T.pr j ^ a i j)

theorem Tens.act_pr (T : Tens D D' W) (a : Matrix (Fin r) (Fin r) ℤ) (i : Fin r) :
    T.act a ≫ T.pr i = ∏ j, T.pr j ^ a i j :=
  T.lim.fac _ ⟨i⟩

def Tens.inc (T : Tens D D' W) (i₀ : Fin r) : D.P.A ⟶ D'.P.A :=
  T.lim.lift (Fan.mk D.P.A fun i => if i = i₀ then 𝟙 _ else 1)

theorem Tens.inc_pr' (T : Tens D D' W) (i₀ i : Fin r) :
    T.inc i₀ ≫ T.pr i = if i = i₀ then 𝟙 _ else 1 :=
  T.lim.fac _ ⟨i⟩

def Tens.xi (T : Tens D D' W) (i₀ : Fin r) : D.X →+ D'.X :=
  T.xe.symm.toAddMonoidHom.comp (AddMonoidHom.single (fun _ => D.X) i₀)

def Tens.xp (T : Tens D D' W) (i₀ : Fin r) : D'.X →+ D.X :=
  (Pi.evalAddMonoidHom (fun _ => D.X) i₀).comp T.xe.toAddMonoidHom

end

def TensO.idem {r : ℕ} (s : SymUnit r) (i₀ : Fin r) : TensO s := TensO.ofMat s (Matrix.single i₀ i₀ 1)

theorem TensO.idem_mul_idem {r : ℕ} (s : SymUnit r) (i₀ : Fin r) : TensO.idem s i₀ * TensO.idem s i₀ = TensO.idem s i₀ := by
  have h : (Matrix.single i₀ i₀ (1 : ℤ) : Matrix (Fin r) (Fin r) ℤ) * Matrix.single i₀ i₀ 1 = Matrix.single i₀ i₀ 1 := by
    simp
  exact h

def TensO.binv {r : ℕ} (s : SymUnit r) : TensO s := TensO.ofMat s ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ)

end GlobalTheory.Mum
end
end
