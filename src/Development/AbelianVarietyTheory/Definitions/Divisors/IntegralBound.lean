module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationVacuumCosetVectorsGrid
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiagValExtTraceNonneg
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoQuotToImOmegaLieOfSplit
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase
public import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MatchOfMatchOffTEmpty

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers

open scoped ComplexOrder

namespace GlobalTheory.HSCore

section Lattice

variable {K : Type} [Field K] [NumberField K]

def vecHt {n : ℕ} (a : Fin n → K) (c : (K →+* ℂ) → ℝ) : ℝ :=
  ((∑ᶠ v : FinitePlace K, Real.log (⨆ k, v (a k))) + ∑ τ : K →+* ℂ, Real.log (c τ)) / (Module.finrank ℚ K : ℝ)

end Lattice

section Geometry

variable {K : Type} [Field K] [NumberField K] (X : Data K) (s : Fin X.D → Fin X.N → K)

def filV (a : ℕ) : Submodule K (X.V X.T) := (Fil (X.ideal s) a (spaceV X s)).comap (X.V X.T).subtype

variable {X s}

def symV {hs : X.IsGood s} {δ : ℕ} (Co : Coord X.toGeo hs δ) (a : ℕ) :
    filV X s a →ₗ[K] (MonoDeg (Fin X.D) a × Fin δ → K) :=
  if h : a ≤ X.T then
    (LinearMap.pi fun q : MonoDeg (Fin X.D) a × Fin δ =>
      (LinearMap.proj q.2 : (Fin δ → K) →ₗ[K] K) ∘ₗ (Co.ev (X.T - a)).toLinearMap ∘ₗ LinearMap.proj q.1) ∘ₗ
      hs.sym (Nat.sub_add_cancel h) (spaceV X s) ∘ₗ (X.V X.T).subtype.restrict fun _ hx => hx
  else 0

def Coord.gen {G : Geo K} {s : Fin G.D → Fin G.N → K} {hs : G.IsGood s} {δ : ℕ} (Co : Coord G hs δ) (k : Fin G.n) (p : Fin δ) : K :=
  ∑ j, G.w j k * Co.y p j

def Coord.c₁ {G : Geo K} {s : Fin G.D → Fin G.N → K} {hs : G.IsGood s} {δ : ℕ} (Co : Coord G hs δ) (σ : K →+* ℂ) (p : Fin δ) : ℝ :=
  archSize (G.A σ) fun k => σ (Co.y p k)


end Geometry

def RegSeq {Y : Scheme.{0}} {L : LB Y} (hL : L.IsLB) (F : Y.Modules) (t : List L.Sec) : Prop :=
  List.rec (motive := fun _ => Y.Modules → Prop) (fun _ => True)
    (fun a _ ih G => Mono (GlobalTheory.cutHom G hL a) ∧ ih (GlobalTheory.cut G hL a)) t F

theorem regSeq_cons {Y : Scheme.{0}} {L : LB Y} (hL : L.IsLB) (F : Y.Modules) (a : L.Sec) (r : List L.Sec) :
    RegSeq hL F (a :: r) ↔ Mono (GlobalTheory.cutHom F hL a) ∧ RegSeq hL (GlobalTheory.cut F hL a) r := Iff.rfl

def VanishFrom {Y : Scheme.{0}} (L : LB Y) (F : Y.Modules) (j₀ : ℤ) : Prop :=
  ∀ j : ℤ, j₀ ≤ j → ∀ q : ℕ, 0 < q → Subsingleton (coh (GlobalTheory.twistZ F L j) q)

end GlobalTheory.HSCore
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct

namespace GlobalTheory.FunObj

open GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

abbrev routeBig (t : T) (i j : ℕ) : Path T (.grid i (j + 1)) (.grid (i + 1) j) :=
  .snoc (.down t (i + 1) j) (Path.one (.right i (j + 1)))

abbrev routeSmall (t : T) (i j : ℕ) : Path T (.grid i (j + 1)) (.grid (i + 1) j) :=
  .snoc (.right i j) (Path.one (.down t i j))

section Kernels

variable (W : G.Weil) {t : T} {i j : ℕ}

def kerBig (τ : TotT G (routeBig t i j)) (g : GA D (G.V (.grid i (j + 1)))) (g₁ : GA D (G.V (.grid (i + 1) j))) :
    Fn G (.grid (i + 1) (j + 1)) := fun u =>
  τ.sum fun d c => c * (W.kerA (.right i (j + 1)) d.1.2 g u * W.kerA (.down t (i + 1) j) d.2 u g₁)

def kerSmall (τ : TotT G (routeSmall t i j)) (g : GA D (G.V (.grid i (j + 1)))) (g₁ : GA D (G.V (.grid (i + 1) j))) :
    Fn G (.grid i j) := fun u =>
  τ.sum fun d c => c * (W.kerA (.down t i j) d.1.2 g u * W.kerA (.right i j) d.2 u g₁)

end Kernels

def translates {H : Type} [Mul H] (z : H →₀ ℂ) (φ : H → ℂ) : H → ℂ := fun u => z.sum fun k c => c * φ (u * k)

def zdeg {H : Type} (z : H →₀ ℂ) : ℂ := z.sum fun _ c => c


variable (G) in
abbrev PolRoute (X M Y : Node) : Type := PolF D (G.V X).rank (G.V M).rank ⊗[ℂ] PolF D (G.V M).rank (G.V Y).rank

def toTens {P Q : Type} [AddCommGroup P] [Module ℂ P] [AddCommGroup Q] [Module ℂ Q] :
    ((Unit × P) × Q →₀ ℂ) →ₗ[ℂ] P ⊗[ℂ] Q := Finsupp.linearCombination ℂ fun d => d.1.2 ⊗ₜ d.2

theorem toTens_surjective {P Q : Type} [AddCommGroup P] [Module ℂ P] [AddCommGroup Q] [Module ℂ Q] :
    Function.Surjective (toTens (P := P) (Q := Q)) := fun x => by
  induction x with
  | tmul p q => exact ⟨Finsupp.single (((), p), q) 1, by simp [toTens]⟩
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, map_add _ _ _⟩

structure RealMatch (W : G.Weil) where

  vX : ∀ i j, Sch G (.right i j)

  vT : ∀ i j, WO (G.V (.grid i j)) (G.V (.grid i (j + 1))) → ℂ

  vX_is : ∀ i j, i < D.R.m → j ≤ D.R.m → W.IsVac (.chi i j) (vX i j)

  vT_is : ∀ t i j, i ≤ D.R.m → j < D.R.m → W.IsVac (.mu t i j) (vT i j)

  vX_row : ∀ i, vX i 0 = W.vac i

  rel : ∀ i j, Submodule ℂ (PolRoute G (.grid i (j + 1)) (.grid (i + 1) (j + 1)) (.grid (i + 1) j) ×
    PolRoute G (.grid i (j + 1)) (.grid i j) (.grid (i + 1) j))

  onto_big : ∀ i j a, ∃ b, (a, b) ∈ rel i j

  onto_small : ∀ i j b, ∃ a, (a, b) ∈ rel i j

  proper : ∀ i j, rel i j ≠ ⊤

namespace RealMatch

variable {W : G.Weil} (ρ : RealMatch W)

def Matched {t : T} {i j : ℕ} (a : PolT G (routeBig t i j) →₀ ℂ) (b : PolT G (routeSmall t i j) →₀ ℂ) : Prop :=
  (toTens a, toTens b) ∈ ρ.rel i j

theorem exists_matched (i j : ℕ) (b : (Unit × PolF D (G.V (.grid i (j + 1))).rank (G.V (.grid i j)).rank) ×
    PolF D (G.V (.grid i j)).rank (G.V (.grid (i + 1) j)).rank →₀ ℂ) :
    ∃ a : (Unit × PolF D (G.V (.grid i (j + 1))).rank (G.V (.grid (i + 1) (j + 1))).rank) ×
      PolF D (G.V (.grid (i + 1) (j + 1))).rank (G.V (.grid (i + 1) j)).rank →₀ ℂ, ∀ t : T, ρ.Matched (t := t) (i := i) (j := j) a b := by
  obtain ⟨x, hx⟩ := ρ.onto_small i j (toTens b)
  obtain ⟨a, rfl⟩ := toTens_surjective x
  exact ⟨a, fun _ => hx⟩

end RealMatch

def RealMatch.Over {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    {G : GridData R.toLevCh sc} {W : G.Weil} (ρ : RealMatch W) : Prop :=
  (∀ k, k + 1 < D.R.m → HEq (ρ.vT 0 k) (R.vac k)) ∧ ∀ k, k + 1 = D.R.m → HEq (ρ.vT 0 k) R.vacX

theorem exists_isVac (W : G.Weil) {μ₀ : T} (hL : L.Is μ₀) {p : Pair T} (hp : p.InRange D.R.m) : ∃ f, W.IsVac p f := by
  have a := node_isV G hL hp
  have b := node_isV G hL hp.small
  have ca := W.cart_is _ hp
  have cb := W.cart_is _ hp.small
  cases p
  all_goals first
    | exact GlobalTheory.VacuumO.vacExists D _ _ W.ψ_std W.θ_is _ _ _ _ b.sigOK a.sigOK cb ca _ _ b.sd a.sd
    | exact GlobalTheory.VacuumO.vacExists D _ _ W.ψ_std W.θ_is _ _ _ _ (GlobalTheory.GridWeil.sigOK_neg a.sigOK) b.sigOK
        (fun τ => isCartanInv_neg (ca τ)) cb _ _ (isSelfDualC_neg a.sd) b.sd

theorem exists_rel (X M M' Y : Node) : ∃ R : Submodule ℂ (PolRoute G X M Y × PolRoute G X M' Y),
    (∀ a, ∃ b, (a, b) ∈ R) ∧ (∀ b, ∃ a, (a, b) ∈ R) ∧ R ≠ ⊤ := by
  have H : ∀ M, ∃ (f : PolRoute G X M Y →ₗ[ℂ] ℂ) (x : PolRoute G X M Y), f x = 1 := fun M =>
    ⟨LinearMap.mul' ℂ ℂ ∘ₗ TensorProduct.map (MvPolynomial.lcoeff ℂ 0) (MvPolynomial.lcoeff ℂ 0), 1 ⊗ₜ 1, by simp⟩
  obtain ⟨f, x, hx⟩ := H M
  obtain ⟨g, y, hy⟩ := H M'
  refine ⟨LinearMap.eqLocus (f ∘ₗ LinearMap.fst _ _ _) (g ∘ₗ LinearMap.snd _ _ _), fun a => ⟨f a • y, by simp [hy]⟩,
    fun b => ⟨g b • x, by simp [hx]⟩, fun h => ?_⟩
  simpa [hx] using h.ge (Submodule.mem_top (x := (x, 0)))

theorem nonempty_realMatch (W : G.Weil) {μ₀ : T} (hL : L.Is μ₀) : Nonempty (RealMatch W) := by
  have h1 : ∀ i j, ∃ f : Sch G (.right i j), (i < D.R.m → j ≤ D.R.m → W.IsVac (.chi i j) f) ∧
      ∀ h : j = 0, f = (by subst h; exact W.vac i) := fun i j => by
    rcases j with _ | j
    · exact ⟨W.vac i, fun hi _ => W.vac_is i hi, fun _ => rfl⟩
    · by_cases h : i < D.R.m ∧ j + 1 ≤ D.R.m
      · obtain ⟨f, hf⟩ := exists_isVac W hL (p := .chi i (j + 1)) h
        exact ⟨f, fun _ _ => hf, fun h => by omega⟩
      · exact ⟨0, fun a b => absurd ⟨a, b⟩ h, fun h => by omega⟩
  have h2 : ∀ i j, ∃ f : Sch G (.down μ₀ i j), i ≤ D.R.m → j < D.R.m → W.IsVac (.mu μ₀ i j) f := fun i j => by
    by_cases h : i ≤ D.R.m ∧ j < D.R.m
    · obtain ⟨f, hf⟩ := exists_isVac W hL (p := .mu μ₀ i j) h
      exact ⟨f, fun _ _ => hf⟩
    · exact ⟨0, fun a b => absurd ⟨a, b⟩ h⟩
  choose vX h1 using h1
  choose vT h2 using h2
  choose rel h3 using fun i j : ℕ => exists_rel (G := G) (.grid i (j + 1)) (.grid (i + 1) (j + 1)) (.grid i j) (.grid (i + 1) j)
  exact ⟨⟨vX, vT, fun i j => (h1 i j).1, fun _ => h2, fun i => (h1 i 0).2 rfl, rel, fun i j => (h3 i j).1,
    fun i j => (h3 i j).2.1, fun i j => (h3 i j).2.2⟩⟩

section Finite

variable (W : G.Weil) (B : Frames G) (t : T)

def IsLocVec (p : Pair T) (e : AE D) (f₀ φ f : WO (G.pS p) (G.pT p) → ℂ) : Prop :=
  IsSBHalf e (latO (G.pS p) (G.pT p) (G.latS p : Set _) (G.latT p : Set _) fun _ => True) φ ∧
    IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) e
      (latO (G.pS p) (G.pT p) (G.latS p : Set _) (G.latT p : Set _) fun _ => True) 1 f₀ φ f

def HasLocal (e : AE D) {X M Y : ℕ × ℕ} (hX : X.1 ≤ D.R.m ∧ X.2 ≤ D.R.m) (hM : M.1 ≤ D.R.m ∧ M.2 ≤ D.R.m)
    (hY : Y.1 ≤ D.R.m ∧ Y.2 ≤ D.R.m)
    (P₁ : (φ f : Mx D (G.V (.grid X.1 X.2)).rank (G.V (.grid M.1 M.2)).rank → ℂ) → Prop)
    (P₂ : (φ f : Mx D (G.V (.grid M.1 M.2)).rank (G.V (.grid Y.1 Y.2)).rank → ℂ) → Prop)
    (τ : (Unit × (Mx D (G.V (.grid X.1 X.2)).rank (G.V (.grid M.1 M.2)).rank → ℂ)) ×
      (Mx D (G.V (.grid M.1 M.2)).rank (G.V (.grid Y.1 Y.2)).rank → ℂ) →₀ ℂ)
    (Φ : ∀ w, Matrix (Fin ((locGrid G t w).rank M)) (Fin ((locGrid G t w).rank X) ⊕ Fin ((locGrid G t w).rank Y)) (Kw w) → ℂ) :
    Prop :=
  ∃ (φ₁ : _ → _) (φ₂ : _ → _), (∀ d ∈ τ.support, P₁ (φ₁ d) d.1.2 ∧ P₂ (φ₂ d) d.2) ∧
    ∀ x₁ x₂, IsHalf e x₁ → IsHalf e x₂ → (τ.sum fun d c => c * (φ₁ d x₁ * φ₂ d x₂)) =
      ∏ w ∈ locPl G t, Φ w (fromCols (B.coord t w hX hM (x₁.map fun a => cpt w (toEAf D a)))
        (B.coord t w hM hY (x₂.map fun a => cpt w (toEAf D a)))ᵀ)

def flipAt (i j : ℕ) (w : Pl D.host.E) (n : ℕ)
    (Φ : Matrix (Fin ((locGrid G t w).rank (i, j))) ((locGrid G t w).Cols i j) (Kw w) → ℂ) :
    Matrix (Fin ((locGrid G t w).rank (i + 1, j + 1))) ((locGrid G t w).Cols i j) (Kw w) → ℂ :=
  squareFlip (haarVol ((givenLevel G t w (i, j)).map invT)) (stdSplit ((locGrid G t w).rank_square i j)) (psiAt W w)
    ((locGrid G t w).nu i j) (unifAt w) n (Assignment.one.block _ _) Φ

theorem flipTensor_eq (i j : ℕ) (w : Pl D.host.E) (n : ℕ) (S : (locGrid G t w).Args → ℂ) (x : (locGrid G t w).Args) :
    (locGrid G t w).flipTensor .one (psiAt W w) (unifAt w) n i j (givenLevel G t w) S x =
      flipAt W t i j w n ((locGrid G t w).sliceB i j S x) ((locGrid G t w).joinA i j x) := rfl

variable {W} (ρ : RealMatch W) (i j : Fin D.R.m)

def HasFlip (n : Pl D.host.E → ℕ)
    (Φ : ∀ w, Matrix (Fin ((locGrid G t w).rank (i, j))) ((locGrid G t w).Cols i j) (Kw w) → ℂ)
    (τ : TotT G (routeBig t i j)) (τ' : TotT G (routeSmall t i j)) : Prop :=
  ∃ e, IsIdemSum e (locPl G t) ∧
    HasLocal B t e (X := (i, j + 1)) (M := (i, j)) (Y := (i + 1, j)) ⟨i.2.le, j.2⟩ ⟨i.2.le, j.2.le⟩ ⟨i.2, j.2.le⟩
      (IsLocVec W (.mu t i j) e (ρ.vT i j)) (IsLocVec W (.chi i j) e (ρ.vX i j)) τ' Φ ∧
    HasLocal B t e (X := (i, j + 1)) (M := (i + 1, j + 1)) (Y := (i + 1, j)) ⟨i.2.le, j.2⟩ ⟨i.2, j.2⟩ ⟨i.2, j.2.le⟩
      (IsLocVec W (.chi i (j + 1)) e (ρ.vX i (j + 1))) (IsLocVec W (.mu t (i + 1) j) e (ρ.vT (i + 1) j)) τ
      fun w => flipAt W t i j w (n w) (Φ w)

def IsMatched (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) : Prop :=
  ∃ a b τ τ' n Φ, ρ.Matched a b ∧ (∀ w ∈ locPl G t, depthAt G w ≤ n w ∧ IsNatDatum (unifAt w) (n w) (Φ w)) ∧
    HasFlip B t ρ i j n Φ τ τ' ∧ Θ = tensT W a τ ∧ Θ' = tensT W b τ'

end Finite

variable (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m)


variable {t} in
def SquareConv {i j : ℕ} (M : Vol G) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j))
    (z : GA D (G.V (.grid i j)) →₀ ℂ) (g : GA D (G.V (.grid i (j + 1)))) (g₁ : GA D (G.V (.grid (i + 1) j))) : Prop :=
  IntegrableOn (kerBig W Θ g g₁) (M.fd _) (M.ν _) ∧ IntegrableOn (translates z (kerSmall W Θ' g g₁)) (M.fd _) (M.ν _)

def IsSquareConst (c : ℂ) : Prop :=
  ∀ M : Vol G, M.Is t → ∀ Θ Θ', IsMatched B t ρ i j Θ Θ' → ∀ z g g₁, SquareConv W M Θ Θ' z g g₁ →
    zdeg z * ∫ u in M.fd _, kerBig W Θ g g₁ u ∂M.ν _ = c * ∫ u in M.fd _, translates z (kerSmall W Θ' g g₁) u ∂M.ν _

def SquareNonzero : Prop :=
  ∃ M : Vol G, M.Is t ∧ ∃ Θ Θ', IsMatched B t ρ i j Θ Θ' ∧ ∃ z g g₁, SquareConv W M Θ Θ' z g g₁ ∧
    ∫ u in M.fd _, translates z (kerSmall W Θ' g g₁) u ∂M.ν _ ≠ 0

def CommutesWith (c : ℂ) : Prop :=
  ∀ M : Vol G, M.Is t → ∀ Θ Θ', IsMatched B t ρ i j Θ Θ' → ∀ F : Fn G (.grid i (j + 1)),
    IsAutFunSm W.θ _ F → IsCuspFun _ F → G.IsListed W.θ _ F → TotConv W M _ Θ F → TotConv W M _ Θ' F →
      liftT W M (routeBig t i j) Θ F = c • liftT W M (routeSmall t i j) Θ' F

variable {W B ρ t i j}

theorem IsSquareConst.unique (h : SquareNonzero W B ρ t i j) {c c' : ℂ} (hc : IsSquareConst W B ρ t i j c)
    (hc' : IsSquareConst W B ρ t i j c') : c = c' := by
  obtain ⟨M, hM, Θ, Θ', hΘ, z, g, g₁, hz, h0⟩ := h
  exact mul_right_cancel₀ h0 ((hc M hM Θ Θ' hΘ z g g₁ hz).symm.trans (hc' M hM Θ Θ' hΘ z g g₁ hz))

end GlobalTheory.FunObj

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame
open GlobalTheory.LB (resG_resG resG_self toMod)
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)
open GlobalTheory.QCoh (pullbackSections)
open GlobalTheory.VBExt (AdaptedChart)
open ReciprocityTheory.L2DbarEstimates (V)
open Limits (pullback biprod)
open MonoidalCategory CartesianMonoidalCategory
open GlobalTheory.Cartier
open GlobalTheory.CechPic (Pic cls lam)
open GlobalTheory.LieVB (omega unitSec dUnit)
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase)
open scoped ContDiff ComplexOrder CategoryTheory.Obj

namespace GlobalTheory

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {σ σ' : k →+* ℂ}

structure IsRegSurf (p : X ⟶ Sp k) : Prop extends IsArithVar p 1 where

  regular : ∀ x, IsRegularLocalRing (X.presheaf.stalk x)

structure RegCover (p : X ⟶ Sp k) [IsIntegral X] where

  Y : Scheme.{0}

  ρ : Y ⟶ X

  reg : IsRegSurf (ρ ≫ p)

  generic : haveI := reg.isIntegral; ρ (genericPoint Y) = genericPoint X

  finite : haveI := reg.isIntegral; ρ.residueDegree (genericPoint Y) ≠ 0

namespace RegCover

variable [IsIntegral X] (C : RegCover p)

end RegCover

namespace HermLB

variable [IsIntegral X] [IsLocallyNoetherian X] (L M : HermLB p)

variable {L M}

end HermLB

section Sum

variable {E₁ E₂ : X.Modules} {r s : ℕ}

end Sum

namespace VMetric

variable [IsIntegral X] {E : X.Modules} {r : ℕ} {h : VMetric p E r} {a b : ℝ}




end VMetric





def sqMap {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} {f : S' ⟶ S} {φ : A'.left ⟶ A.left}
    (w : φ ≫ A.hom = A'.hom ≫ f) : (A' ⊗ A').left ⟶ (A ⊗ A).left :=
  pullback.map A'.hom A'.hom A.hom A.hom φ φ f w.symm w.symm

structure PPAS (S : Scheme.{0}) where

  A : Over S

  [grp : GrpObj A]

  isAb : IsAbelianScheme A

  g : ℕ

  smoothDim : SmoothOfRelativeDimension g A.hom

  c : Pic (A ⊗ A).left

  isPol : IsPrincipalPol A c

namespace PPAS

attribute [instance] grp smoothDim

variable {S S' : Scheme.{0}} (P : PPAS S)

def ofPolAV (Q : Out.PolAV S) : PPAS S where
  A := Q.A
  isAb := Q.isAb
  g := Q.g
  smoothDim := Q.smoothDim
  c := _
  isPol := IndefiniteRowSideFullHecke.ZeroSectionBase.isPrincipalPol_of_polAV Q

structure RiemannData (y : Sp ℂ ⟶ S) where

  B : Over (Sp ℂ)

  [grp : GrpObj B]

  φ : B.left ⟶ P.A.left

  isPull : IsGrpPullback B P.A y φ

  L : LB B.left

  isLB : L.IsLB

  pol : CechPic.pull (sqMap isPull.1.w) P.c = lam (cls L isLB) (fst B B) (snd B B)

  u : HolUnif B L P.g

  H : Matrix (Fin P.g) (Fin P.g) ℂ

  χ : u.Λ → ℂ

  isAH : u.IsAH H χ

namespace RiemannData

attribute [instance] grp

variable {P} {y : Sp ℂ ⟶ S} (d : P.RiemannData y)

end RiemannData

theorem pull_sqMap_lam {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S}
    {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A f φ) (c : Pic A.left) :
    CechPic.pull (sqMap h.1.w) (lam c (fst A A) (snd A A)) =
      lam (CechPic.pull φ c) (fst A' A') (snd A' A') := by
  let m : Over.mk ((A' ⊗ A').hom ≫ f) ⟶ A ⊗ A := Over.homMk (sqMap h.1.w) (by
    change sqMap h.1.w ≫ pullback.fst _ _ ≫ A.hom = (pullback.fst _ _ ≫ A'.hom) ≫ f
    rw [sqMap, pullback.lift_fst_assoc, Category.assoc, Category.assoc, h.1.w])
  rw [CechPic.lam_pull_of_isGrpPullback h]
  refine (CechPic.pull_lam m c _ _).trans ?_
  congr 1 <;> refine Over.OverMorphism.ext ?_
  exacts [pullback.lift_fst _ _ _, pullback.lift_snd _ _ _]

theorem nonempty_riemannData (Q : Out.PolAV S) (y : Sp ℂ ⟶ S) :
    Nonempty ((ofPolAV Q).RiemannData y) := by
  have h := isGrpPullback_pullback Q.A y
  have hL := pull_isLB Q.isLB (pullback.fst Q.A.hom y)
  obtain ⟨w, hw⟩ := (CechPic.cls_eq_iff hL hL).1 rfl
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (X := S)
    (x := y (IsLocalRing.closedPoint ℂ)) (U := ⊤) trivial
  let Q' : Out.PolAV (Sp ℂ) := ⟨(Over.pullback y).obj Q.A,
    PolPull.isAbelianScheme_of_isGrpPullback Q.isAb h, Q.g,
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 Q.smoothDim, _, hL,
    PolBaseChange.rigidified_pull h Q.rigid, PolBaseChange.sym_pull h Q.sym,
    relAmple_pull h.1 Q.isLB hL ((isGen_iff w).1 hw) U hU
      (fun z => by rwa [Subsingleton.elim z (IsLocalRing.closedPoint ℂ)]) Q.ample,
    kTriv_pull h Q.isLB hL ((isGen_iff w).1 hw) Q.ktriv⟩
  obtain ⟨rig, hr⟩ := Q'.rigid
  obtain ⟨u, H, χ, -, hH, -⟩ := thetaUnifAV_all Q' rig hr
  exact ⟨⟨Q'.A, _, h, Q'.L, hL, (pull_sqMap_lam h _).trans
    (congrArg (lam · _ _) (CechPic.cls_pull Q.isLB _ hL).symm), u, H, χ, hH⟩⟩

variable (P : PPAS X)

variable {P} {t : ℝ} {h h' : VMetric p (omega P.A) P.g}

variable (P p) [IsIntegral X]


variable {P p} {a b : ℝ}

end PPAS

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.CechPic GlobalTheory.TangentOrigin GlobalTheory.Vanishing GlobalTheory.Vanishing.H0 GlobalTheory.HermTools GlobalTheory.HilbertSamuel
open GlobalTheory.AllWt (Psi secZ exOf wtOf cuspOn latOn normOn petOn GoodOn suppOn LiesOn LiesOff)
open GlobalTheory.FlagMod (FlagCover FlagModel Frames frX ev)
open GlobalTheory.FlagTan (dimFlag psiSet TIx IsTanFrame)
open GlobalTheory.CompHt (hodgeWt uPrime)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

section Data

variable {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c)

def tanOrd (Dw : Datum H) : Fin (dimFlag Dw) ≃ TIx Dw (psiSet H) := by
  classical exact (Fintype.equivFinOfCardEq (FlagTan.card_TIx (FlagTan.isHalf_psiSet H))).symm

variable {X Z} (M : Modif (str₀ X Z) (U₀ X Z) (dimFlag Dw))

abbrev toFlag : M.X ⟶ X.YY := M.σ ≫ inc₀ X Z

abbrev flagIdx (la : AllWt.Weight Dw) (k : X.F.J) : ((L₀ X Z la).pull M.σ).ι := ((common₀ X Z).pull M.σ).idx la k


open Classical in
def IsKS (ω : H0 M.str (LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)) M.off) : Prop :=
  ∀ (K : Type) [Field K] [Algebra c.F K] (P Q : FrPt Xo c K) (t : Ix Dw → Kˣ)
    (v : TIx Dw (psiSet H) → FrPt Xo c (DualNumber K)) (z : Sp K ⟶ M.X)
    (zv : TIx Dw (psiSet H) → (Sp (DualNumber K) ⟶ M.X)) (i : M.K.bundle.ι) (k : X.F.J) (O : M.X.Opens)
    (hO : O ≤ M.K.bundle.U i) (g : Fin (dimFlag Dw) → Γ(M.X, O)) (hz : ⊤ ≤ z ⁻¹ᵁ O) (hzv : ∀ b, ⊤ ≤ zv b ⁻¹ᵁ O)
    (hk : ⊤ ≤ (z ≫ toFlag M) ⁻¹ᵁ X.F.U k) (ho : ⊤ ≤ z ⁻¹ᵁ M.off)
    (hi : ⊤ ≤ z ⁻¹ᵁ (LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)).U (i, flagIdx M _ k)),
    X.F.ChartFr k (z ≫ toFlag M) hk Q → FrBor t Q P → IsTanFrame (psiSet H) P v →
    (∀ b, zv b ≫ toFlag M = X.ptY (v b)) →
    H0.val (B := LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)) z (i, flagIdx M _ k) ho hi ω *
        (Matrix.of fun a b => (evalPt (zv (tanOrd Dw b)) O (hzv _) (g a)).snd).det =
      (∏ ix, t ix ^ exOf Dw (FlagTan.kap Dw) 0 ix).val * evalPt z O hz (M.K.jacobian i hO g)

structure CanId where

  ω : H0 M.str (LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)) M.off

  unit : NowhereZero ω

  isKS : IsKS M ω

variable {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (P : WtPar Dw)


variable (Z) in
instance (priority := high) cuspAddCommGroup (la : AllWt.Weight Dw) : AddCommGroup (Cusp Z U la) :=
  Submodule.addCommGroup _


variable (Z) in
instance (priority := high) cuspModule (la : AllWt.Weight Dw) : Module c.F (Cusp Z U la) := Submodule.module _


variable (X Z) in
abbrev Choice : Type 1 :=
  Resol (common₀ X Z) (U₀ X Z) (dimFlag Dw) (space X Z U P.u₁) (space X Z U P.u₂)

variable {U P} (R : Choice X Z U P) (ω : CanId R.toModif)

def adjSec (h₁ : FreeOnOpen X Z U P.u₁) (j : ℕ) : Cusp Z U (P.wt j) →ₗ[c.F] H0 R.str (R.adj j) R.off :=
  (R.adjEquiv ω.ω ω.unit h₁ j (P.kap_add j)).toLinearMap ∘ₗ R.pullOff ∘ₗ cuspSec X Z U (P.wt j)

theorem adjSec_injective (h₁ : FreeOnOpen X Z U P.u₁) (j : ℕ) : Function.Injective (adjSec R ω h₁ j) :=
  (R.adjEquiv ω.ω ω.unit h₁ j (P.kap_add j)).injective.comp
    ((R.bijective_pullOff (isLB_L₀ X Z _)).1.comp (cuspSec_injective X Z U _))

theorem mulPole_adjSec (h₁ : FreeOnOpen X Z U P.u₁) (j : ℕ) (f : Cusp Z U (P.wt j)) :
    R.mulPole j R.off (adjSec R ω h₁ j f) = R.mulCan ω.ω (P.kap_add j) (R.pullOff (cuspSec X Z U _ f)) :=
  R.mulPole_adjEquiv _ ω.unit h₁ _ _ _

def adjGlobal (j : ℕ) : Submodule c.F (H0 R.str (R.adj j) R.off) := LinearMap.range (restr le_top)

variable (x : ℝ) {D : Formalism.BasicNotions.D7} (V : (c.F →+* ℂ) → Formalism.BasicNotions.TH.HSp D)
  (dict : ∀ σ, Formalism.L2.Theta.GA D (V σ) → Σ k, FD.Frame ((U σ).X k).Ψ r)


variable (Z U) in
abbrev CuspFrame (la : AllWt.Weight Dw) : Type :=
  LatFrame (normOn U x V dict Z (wtOf Dw la 0)) (latOn U Z (wtOf Dw la 0))


variable {x V dict} in
theorem nonempty_cuspFrame {la : AllWt.Weight Dw} (h : GoodOn U x V dict Z (wtOf Dw la 0)) :
    Nonempty (CuspFrame Z U x V dict la) :=
  let ⟨N, n, b, w, A, hf⟩ := CompHt.exists_isFrame CompHt.conj_comp_ne
    (fun σ f => CompHt.petOn_conj U x V dict Z _ σ f.1) h.1 h.2.1 h.2.2
  ⟨⟨N, n, b, w, A, hf⟩⟩

structure Ready : Prop where

  conn : GeometricallyConnected R.str

  one_le : 1 ≤ dimFlag Dw

  le_T : dimFlag Dw + 1 ≤ P.T

  ext₁ : Extends X Z U P.u₁

  ext₂ : Extends X Z U P.u₂

  free₁ : FreeOnOpen X Z U P.u₁

  free₂ : FreeOnOpen X Z U P.u₂

  good : ∀ j ≤ P.T, GoodOn U x V dict Z (wtOf Dw (P.wt j) 0)

  global_le : ∀ j ≤ P.T, adjGlobal R j ≤ LinearMap.range (adjSec R ω free₁ j)

  le_global : LinearMap.range (adjSec R ω free₁ 0) ≤ adjGlobal R 0

variable {R ω x V dict} (h : Ready R ω x V dict) (f₁ : CuspFrame Z U x V dict P.u₁) (f₂ : CuspFrame Z U x V dict P.u₂)
  (th : R.L.Sec) (k : Consts)

def Ready.geo : Geo c.F :=
  R.geo (dense_U₀ X Z) h.conn h.one_le h.free₁ h.free₂ h.ext₁.equiv h.ext₂.equiv f₁ f₂ th k.abelian₂

def Ready.data : Data c.F :=
  dataOf (S := fun j => Cusp Z U (P.wt j)) (Nm := fun j => normOn U x V dict Z (wtOf Dw (P.wt j) 0))
    (M := fun j => latOn U Z (wtOf Dw (P.wt j) 0)) (h.geo f₁ f₂ th k) P.T h.le_T (adjSec R ω h.free₁) (adjSec_injective R ω h.free₁)
    (fun j hj => nonempty_cuspFrame (h.good j hj)) h.global_le h.le_global k

namespace Ready

theorem data_numbers : (h.data f₁ f₂ th k).D = dimFlag Dw ∧ (h.data f₁ f₂ th k).T = P.T ∧ (h.data f₁ f₂ th k).j₀ = 1 ∧
    (h.data f₁ f₂ th k).n = f₁.n ∧ (h.data f₁ f₂ th k).abelian₂ = k.abelian₂ ∧ (h.data f₁ f₂ th k).beta = k.beta ∧
    (h.data f₁ f₂ th k).LamD = k.LamD ∧ (h.data f₁ f₂ th k).LamT = k.LamT ∧ (h.data f₁ f₂ th k).J = k.J :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def equivV {j : ℕ} (hj : j ≤ P.T) : Cusp Z U (P.wt j) ≃ₗ[c.F] (h.data f₁ f₂ th k).V j :=
  dataEquiv (S := fun j => Cusp Z U (P.wt j)) (Nm := fun j => normOn U x V dict Z (wtOf Dw (P.wt j) 0))
    (M := fun j => latOn U Z (wtOf Dw (P.wt j) 0)) (h.geo f₁ f₂ th k) P.T h.le_T (adjSec R ω h.free₁) (adjSec_injective R ω h.free₁)
    (fun j hj => nonempty_cuspFrame (h.good j hj)) h.global_le h.le_global k hj

theorem coe_equivV {j : ℕ} (hj : j ≤ P.T) (f : Cusp Z U (P.wt j)) :
    (h.equivV f₁ f₂ th k hj f).1 = adjSec R ω h.free₁ j f :=
  coe_dataEquiv (S := fun j => Cusp Z U (P.wt j)) (Nm := fun j => normOn U x V dict Z (wtOf Dw (P.wt j) 0))
    (M := fun j => latOn U Z (wtOf Dw (P.wt j) 0)) (h.geo f₁ f₂ th k) P.T h.le_T (adjSec R ω h.free₁)
    (adjSec_injective R ω h.free₁) (fun j hj => nonempty_cuspFrame (h.good j hj)) h.global_le h.le_global k hj f

theorem equivV_mem {j : ℕ} (hj : j ≤ P.T) (f : Cusp Z U (P.wt j)) :
    h.equivV f₁ f₂ th k hj f ∈ (h.data f₁ f₂ th k).M j ↔ f ∈ latOn U Z (wtOf Dw (P.wt j) 0) :=
  dataEquiv_mem (S := fun j => Cusp Z U (P.wt j)) (Nm := fun j => normOn U x V dict Z (wtOf Dw (P.wt j) 0))
    (M := fun j => latOn U Z (wtOf Dw (P.wt j) 0)) (h.geo f₁ f₂ th k) P.T h.le_T (adjSec R ω h.free₁)
    (adjSec_injective R ω h.free₁) (fun j hj => nonempty_cuspFrame (h.good j hj)) h.global_le h.le_global k hj f

theorem nrm_equivV {j : ℕ} (hj : j ≤ P.T) (σ : c.F →+* ℂ) (f : Cusp Z U (P.wt j)) :
    ((h.data f₁ f₂ th k).nm j).nrm σ (h.equivV f₁ f₂ th k hj f) = petOn U x V dict Z (wtOf Dw (P.wt j) 0) σ f :=
  nrm_dataEquiv (S := fun j => Cusp Z U (P.wt j)) (Nm := fun j => normOn U x V dict Z (wtOf Dw (P.wt j) 0))
    (M := fun j => latOn U Z (wtOf Dw (P.wt j) 0)) (h.geo f₁ f₂ th k) P.T h.le_T (adjSec R ω h.free₁)
    (adjSec_injective R ω h.free₁) (fun j hj => nonempty_cuspFrame (h.good j hj)) h.global_le h.le_global k hj σ f

theorem ofSec_comb (w : Cusp Z U P.u₁) : H0.ofSec R.str ⊤ ((h.data f₁ f₂ th k).comb (f₁.b.equivFun w)) =
    R.Δ₁.lift (h.ext₁.equiv w) :=
  (R.ofSec_comb R.Δ₁ h.ext₁.equiv f₁ k.abelian₂ _).trans (by rw [LinearEquiv.symm_apply_apply])

theorem mem_lattice (w : Cusp Z U P.u₁) :
    f₁.b.equivFun w ∈ (h.data f₁ f₂ th k).lattice ↔ w ∈ latOn U Z (wtOf Dw P.u₁ 0) := f₁.mem_span_iff w

theorem normAt_eq (σ : c.F →+* ℂ) (w : Cusp Z U P.u₁) :
    (h.data f₁ f₂ th k).normAt σ (f₁.b.equivFun w) = petOn U x V dict Z (wtOf Dw P.u₁ 0) σ w := f₁.isFrame.norm σ w

theorem d_eq : (h.data f₁ f₂ th k).d = Module.finrank c.F (Cusp Z U (P.wt P.T)) :=
  (h.data f₁ f₂ th k).d_eq_finrank.trans (h.equivV f₁ f₂ th k le_rfl).finrank_eq.symm

theorem mulW_adjSec (j : ℕ) (w : Cusp Z U P.u₁) (f : Cusp Z U (P.wt j)) (g : Cusp Z U (P.wt (j + 1)))
    (hg : g.1 = w.1 * f.1) :
    (h.data f₁ f₂ th k).mulW j (f₁.b.equivFun w) (adjSec R ω h.free₁ j f) = adjSec R ω h.free₁ (j + 1) g := by
  have e₀ : cuspSec X Z U _ g = ((common₀ X Z).addChart (P.u₁_add_wt j)).mul (cuspSec X Z U _ w) (cuspSec X Z U _ f) :=
    sec₀_mul X Z ((exOf_add_zero _ _).symm.trans (congrArg (exOf Dw · 0) (P.u₁_add_wt j))) _ _ _ hg
  have e₁ : R.pullOff (cuspSec X Z U _ w) = restr le_top (H0.pull R.σ le_top (h.ext₁.equiv w).1) :=
    (congrArg R.pullOff (h.ext₁.restr_equiv w).symm).trans
      ((pull_restr _ _ _ _).trans (restr_pull (isLB_L₀ X Z _) _ _ _ _).symm)
  have e₂ : R.pullOff (cuspSec X Z U _ g) = (R.com.addChart (P.u₁_add_wt j)).mul (R.pullOff (cuspSec X Z U _ w))
      (R.pullOff (cuspSec X Z U _ f)) :=
    (congrArg R.pullOff e₀).trans (((common₀ X Z).addChart (P.u₁_add_wt j)).pull_mul R.σ R.off_eq.le _ _)
  have e₃ := R.adjEquiv_mul ω.ω ω.unit h.free₁ j (P.kap_add j) (P.kap_add (j + 1)) (P.u₁_add_wt j) (h.ext₁.equiv w)
    (R.pullOff (cuspSec X Z U _ f))
  have e₄ : restr le_top (R.Δ₁.lift (h.ext₁.equiv w)) =
      H0.ofSec R.str R.off ((h.data f₁ f₂ th k).comb (f₁.b.equivFun w)) :=
    (congrArg (restr le_top) (h.ofSec_comb f₁ f₂ th k w).symm).trans (restr_ofSec _ _)
  rw [← e₁, ← e₂, e₄] at e₃
  exact (LinearMap.congr_fun ((h.geo f₁ f₂ th k).mulW_apply j _) _).trans e₃.symm

end Ready

end Data

def be (N : OT.Num) : ℝ := Real.exp N.lbe

def Consts.ofTable (N : OT.Num) (h : 0 ≤ N.lbe) (lam lamD lamT J : ℝ) (hD : 0 ≤ lamD) (hT : 0 ≤ lamT) : Consts :=
  ⟨Real.exp lam, be N, Real.exp lamD, Real.exp lamT, J, Real.one_le_exp h, Real.one_le_exp hD, Real.one_le_exp hT⟩

end GlobalTheory.CompHS
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.JoinCastSucc
set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.ChowHt GlobalTheory.Adelic
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

namespace GlobalTheory.HSChoice

def join {R : Type} {D N : ℕ} (u : Fin D → Fin N → R) (ξ : Fin N → R) : Fin (D + 1) × Fin N → R :=
  fun p => Fin.lastCases (motive := fun _ => R) (ξ p.2) (fun i => u i p.2) p.1

def spec {F E : Type} [CommRing F] [CommRing E] [Algebra F E] {D N : ℕ} (s : Fin D → Fin N → E)
    (f : MvPolynomial (Fin (D + 1) × Fin N) F) : MvPolynomial (Fin 1 × Fin N) E :=
  aeval (join (fun i j => C (s i j)) fun j => X (0, j)) f

def lin {K : Type} [CommRing K] {N : ℕ} (y : Fin N → K) : MvPolynomial (Fin 1 × Fin N) K := ∑ j, X ((0 : Fin 1), j) * C (y j)

def finPart {K ι : Type} [Field K] [NumberField K] (g : MvPolynomial ι K) : ℝ :=
  (∑ᶠ v : FinitePlace K, Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs v g)) / (Module.finrank ℚ K : ℝ)

def mean (K : Type) [Field K] [NumberField K] (a : (K →+* ℂ) → ℝ) : ℝ := (∑ τ, a τ) / (Module.finrank ℚ K : ℝ)

structure ShortLat {F : Type} [Field F] [NumberField F] {N n : ℕ} (w : Matrix (Fin N) (Fin n) F)
    (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ) (Λ : ℝ) : Prop where
  pos : 0 < N
  spans : Submodule.span F (Set.range w.col) = ⊤
  int : ∀ u ∈ Submodule.span (𝓞 F) (Set.range w.col), u ∈ Submodule.span ℤ (Set.range w.col)
  det : ∀ σ, (A σ).det ≠ 0
  conj : ConjCompat A
  le : ∀ k σ, frameNorm (A σ) (fun j => σ (w j k)) ≤ Λ
  one_le : 1 ≤ Λ

def NoSquare {K : Type} [Field K] {N : ℕ} (g : MvPolynomial (Fin 1 × Fin N) K) : Prop :=
  g ≠ 0 ∧ ∀ y : Fin N → K, y ≠ 0 → ¬ lin y ^ 2 ∣ g

theorem join_last {R : Type} {D N : ℕ} (u : Fin D → Fin N → R) (ξ : Fin N → R) (j : Fin N) : join u ξ (Fin.last D, j) = ξ j := by
  simp [join]

theorem join_castSucc {R : Type} {D N : ℕ} (u : Fin D → Fin N → R) (ξ : Fin N → R) (i : Fin D) (j : Fin N) :
    join u ξ (i.castSucc, j) = u i j := by
  simp [join]

namespace Check

theorem lin_ne {K : Type} [Field K] {N : ℕ} {y : Fin N → K} (hy : y ≠ 0) : lin y ≠ 0 := by
  intro h
  apply hy
  funext j
  have := congrArg (eval (fun p : Fin 1 × Fin N => if p.2 = j then (1:K) else 0)) h
  simpa [lin] using this

end Check

end GlobalTheory.HSChoice
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.IsIntegralOpW
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong Formalism.UG

namespace GlobalTheory.CongW

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {l : ℕ} [Fact l.Prime] {a : ℕ}

def wtSize (lam : (E →+* ℂ) → DomWeight a) : ℕ :=
  ∑ τ : E →+* ℂ, ∑ k : Fin a, ((lam τ).w k).natAbs

def IntMat (u : HeightOneSpectrum (𝓞 E)) (x : Matrix (Fin a) (Fin a) (u.adicCompletion E)) : Prop :=
  ∀ i j, x i j ∈ u.adicCompletionIntegers E

def IsIntegralOpW (ι : Qbar l ≃+* ℂ) (lam : (E →+* ℂ) → DomWeight a) (w₀ : HeightOneSpectrum (𝓞 E))
    (f : UA E a →₀ ℂ) : Prop :=
  ∀ g ∈ f.support, g ∈ finU (E := E) (n := a) ∧ (∀ u, ¬ Apart u w₀ → cLoc u g = 1) ∧
    ∃ d : ℕ, (∀ u : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ u.asIdeal →
        IntMat u (((l : u.adicCompletion E) ^ d) • ((cLoc u g : GL (Fin a) (u.adicCompletion E)) :
          Matrix (Fin a) (Fin a) (u.adicCompletion E))) ∧
        IntMat u (((l : u.adicCompletion E) ^ d) • (((cLoc u g)⁻¹ : GL (Fin a) (u.adicCompletion E)) :
          Matrix (Fin a) (Fin a) (u.adicCompletion E)))) ∧
      ‖ι.symm (f g)‖ ≤ ((l : ℝ)⁻¹) ^ (a * d * wtSize lam)

def HasTypeVec (w₀ : HeightOneSpectrum (𝓞 E)) (K : Subgroup (UA E a)) (J : Subgroup (GL (Fin a) (w₀.adicCompletion E)))
    {A : Type} [Group A] (θ : J →* A) (χ : A →* ℂˣ) (U : Submodule ℂ (UA E a → ℂ)) : Prop :=
  ∃ φ ∈ U, φ ≠ 0 ∧ (∀ x ∈ K, RU E a x φ = φ) ∧
    ∀ x ∈ locU a w₀, ∀ h : cLoc w₀ x ∈ J, RU E a x φ = ((χ (θ ⟨cLoc w₀ x, h⟩) : ℂˣ) : ℂ) • φ

end GlobalTheory.CongW
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.MoveArgsOneTranspose
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct nonZeroDivisors Pointwise

namespace GlobalTheory.FunObj.LocTest

open GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem intM_of_stepFn (t : T) (w : Pl D.host.E) (j : ℕ) {x} (h : stepFn L t w j x ≠ 0) : IntM x := by
  unfold stepFn at h
  split_ifs at h
  · intro i l
    simpa using TypeDatum.intM_of_Phi_ne_zero _ _ h ((ixSucc _ _ j).symm i) l
  · obtain ⟨⟨g, hg, e⟩, h21, h12, h22⟩ := (parPhi_ne_zero_iff _).1 h
    rintro (i | i) (l | l)
    · have := intM_of_mem_KO hg i l
      rwa [e] at this
    · exact h12 i l
    · exact (h21 i l).le
    · exact h22 i l
  · by_contra hx
    exact h (Set.indicator_of_notMem (s := {x | IntM x}) hx _)

end GlobalTheory.FunObj.LocTest

end
end
