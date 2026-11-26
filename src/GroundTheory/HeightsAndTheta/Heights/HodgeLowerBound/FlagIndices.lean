module

public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.CpRegPhRegOfNonneg
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHoloInjDerivInj
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsFlagGrassPush
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Assembly

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def AmpleOnGenericFibre (P : Ideal (MRing ι)) (A : HermLine ι) : Prop :=
  ∀ (W : Ideal (MRing ι)) (d : ℕ), 1 ≤ d → IsArithVar W (d + 1) → P ≤ W → 0 < geomDeg W A d

def OffBoundary (Bd : Set ((Σ k, ι k) → ℂ)) (W : Ideal (MRing ι)) : Prop :=
  ∀ z ∈ mcPts W, z ∉ Bd

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]

structure ComponentSetting (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] where

  H : HodgeData D

  Cd : CuspData D O Lt

  M : XModel D

  S : LogLogRegularisationSetting M D.Xo (muLine H)

  S_tied : S.IsTied

  S' : BoundedRegularisationSetting M D.Xo H.aMu (cuspCorr H Cd)

  S'_tied : S'.IsTied

  rd : ℝ

  Lval : ℝ

namespace ComponentSetting

variable {D : ComponentData II Ψ K ι Ω E} {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt]
  (X : ComponentSetting D O Lt)

abbrev MUq (B p q : ℕ) (t' : ℝ) : HermLine ι := MUc X.H X.S' B p q t'

def La (B : ℕ) : ℝ := abelian₂ B X.rd X.Lval

end ComponentSetting

variable {D : ComponentData II Ψ K ι Ω E} {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt]

def CuspBundlePos (X : ComponentSetting D O Lt) : Prop :=
  ∀ B p q : ℕ, 4 * D.f + 2 ≤ B → 1 ≤ p → p ≤ q → ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t' : ℝ, 0 < t' → t' ≤ t₀ →
    IsSemipositiveH (mCoordIdeal D.y) (X.MUq B p q t') ∧
      NefOnFibres (mCoordIdeal D.y) (X.MUq B p q t').a ∧
      AmpleOnGenericFibre (mCoordIdeal D.y) (X.MUq B p q t')

def HtInterior (Ch : ℝ) (X : ComponentSetting D O Lt) : Prop :=
  ∀ B p q : ℕ, 4 * D.f * D.N ^ 2 ≤ B → 1 ≤ p → p ≤ q → ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t' : ℝ, 0 < t' → t' ≤ t₀ →
    ∀ W : Ideal (MRing ι), IsArithVar W 1 → mCoordIdeal D.y ≤ W → OffBoundary D.Bd W →
      -(Ch * D.f * D.j' * X.La B) - (p : ℝ) / q * D.KA ≤ htMUc X.H X.S' B p q t' W

def HtBoundary (Ch : ℝ) (X : ComponentSetting D O Lt) : Prop :=
  ∀ B p q : ℕ, 4 * D.f * D.N ^ 2 ≤ B → 1 ≤ p → p ≤ q → ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t' : ℝ, 0 < t' → t' ≤ t₀ →
    ∀ W : Ideal (MRing ι), IsArithVar W 1 → mCoordIdeal D.y ≤ W → ¬ OffBoundary D.Bd W →
      -(Ch * D.f * D.j' * X.La B) - (p : ℝ) / q * D.KA ≤ htMUc X.H X.S' B p q t' W

def CuspMean (Cu : ℝ) (X : ComponentSetting D O Lt) : Prop :=
  1 ≤ D.j' → 3 * D.j' + 1 ≤ D.N → ∀ B : ℕ, 4 * D.f * D.N ^ 2 ≤ B →
    meanU X.H X.Cd ≤ Cu * D.f * D.j' * X.La B

def StokesLimit.Hyp (X : ComponentSetting D O Lt) (B : ℕ) (a : ℝ) : Prop :=
  ∀ p q : ℕ, 1 ≤ p → p ≤ q → ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t' : ℝ, 0 < t' → t' ≤ t₀ →
    ((D.n + 1 : ℕ) : ℝ) * (a - (p : ℝ) / q * D.KA) * geomDegMUc X.H X.S' B p q t' ≤
      topMUc X.H X.S' B p q t'

def StokesLimit.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt) (B : ℕ) (a : ℝ),
    IsIntersectionSystem II → 4 * D.f + 2 ≤ B → ArLimExists X.H X.S B → StokesLimit.Hyp X B a →
      ((D.n + 1 : ℕ) : ℝ) * (a - meanU X.H X.Cd / 2) * degMu X.H ≤ arLim X.H X.S B

def GrassmannianHeightZTwo.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (cf : ℚ) (e : ℝ),
    IsIntersectionSystem II → 2 ≤ N → 1 ≤ j → j ≤ N - 1 → 0 < Jint Ψ N j cf →
    (∀ Z : Matrix (Fin (N - j)) (Fin j) ℂ, (∀ a b, ‖Z a b‖ = 1) →
      1 / 2 * Real.log (1 + Z * Z.conjTranspose).det.re ≤ e) →
    -hFl Ψ N II (FA Ψ N j cf) ≤
      ((dimN Ψ N j + 1 : ℕ) : ℝ) * (Jint Ψ N j cf : ℝ) * (Fintype.card Ψ : ℝ) * e

def MUConjInvariant (X : ComponentSetting D O Lt) : Prop :=
  ∀ B p q : ℕ, 4 * D.f + 2 ≤ B → 1 ≤ p → p ≤ q → ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t' : ℝ, 0 < t' → t' ≤ t₀ →
    IsConjInvariantH (X.MUq B p q t')

def slX (X : ComponentSetting D O Lt) (B : ℕ) : ℝ :=
  arLim X.H X.S B / (((D.n + 1 : ℕ) : ℝ) * degMu X.H)

namespace Line

variable (II : IntersectionSystem)
  (hII : ∀ W : Ideal (MRing (PBlk 2)), IsArithVar W 1 → 0 ≤ II Unit (PBlk 2) W 1 ![fsLine 2])

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsFlagGrassSteps
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

def plToIncr {j m N s : ℕ} (hs : s = j) (hN : j + m = N) (I : PlIdx j m) : PlueckerData.Incr s N :=
  ⟨fun a => Fin.cast hN (I.1.orderEmbOfFin I.2 (Fin.cast hs a)), fun a b hab => by
    rw [Fin.lt_def] at hab ⊢
    simp only [Fin.val_cast]
    exact (I.1.orderEmbOfFin I.2).strictMono (by rw [Fin.lt_def]; simpa using hab)⟩

section Block

variable (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ)

def grFlKappa (hj : 1 ≤ j) (hjN : j ≤ N - 1) : Fin (Fintype.card Ψ) → FlBlock Ψ N :=
  fun t => ((Fintype.equivFin Ψ).symm t, ⟨j - 1, by omega⟩)

def grFlV (hj : 1 ≤ j) (hjN : j ≤ N - 1) :
    (Σ _ : Fin (Fintype.card Ψ), PlIdx j (N - j)) → (Σ q : FlBlock Ψ N, FlIdx Ψ N q) :=
  fun p => ⟨grFlKappa Ψ N j hj hjN p.1, plToIncr (by simp only [grFlKappa]; omega) (by omega) p.2⟩

end Block

section Lines

variable (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ)

def linForm (ℓ : Ψ × Fin N → ℤ) : RootPoly Ψ N := ∑ p, (ℓ p : ℚ) • X p

def linDeg (ℓ : Ψ × Fin N → ℤ) : FlBlock Ψ N → ℤ := fun q => ∑ p, ℓ p * xDeg Ψ N p q

def linLine (ℓ : Ψ × Fin N → ℤ) : HermLine (FlIdx Ψ N) := fsHerm (ι := FlIdx Ψ N) (linDeg Ψ N ℓ)

variable (j : ℕ)

def muForm : Ψ × Fin N → ℤ := fun p => if (p.2 : ℕ) < j then 0 else 1

abbrev VandPair : Type :=
  {t : Ψ × Fin N × Fin N // t.2.1 < t.2.2 ∧ ((t.2.1 : ℕ) < j ↔ (t.2.2 : ℕ) < j)}

def vandForm (t : VandPair Ψ N j) : Ψ × Fin N → ℤ := fun p =>
  (if p = (t.1.1, t.1.2.1) then 1 else 0) - (if p = (t.1.1, t.1.2.2) then 1 else 0)

def vandCount : ℕ := Fintype.card (VandPair Ψ N j)

def vandLine (i : Fin (vandCount Ψ N j)) : HermLine (FlIdx Ψ N) :=
  linLine Ψ N (vandForm Ψ N j ((Fintype.equivFin (VandPair Ψ N j)).symm i))

end Lines

def FlagArithVar.Statement : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] [Nonempty Ψ] (N : ℕ), 2 ≤ N →
    IsArithVar (PFl Ψ N) (dimFl Ψ N + 1)

def FlagImageGrass.Statement : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (hj : 1 ≤ j) (hjN : j ≤ N - 1),
    imageZ (grFlV Ψ N j hj hjN) (PFl Ψ N) = grassIdeal (Fintype.card Ψ) j (N - j)

def VandCount.Statement : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ), j ≤ N → dimN Ψ N j + vandCount Ψ N j = dimFl Ψ N

def HFlProdLinear.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] [Nonempty Ψ] (N d : ℕ) (c : ℚ)
    (ℓ : Fin d → Ψ × Fin N → ℤ),
    IsIntersectionSystem II → 2 ≤ N → d = dimFl Ψ N + 1 →
    hFl Ψ N II (C c * ∏ i, linForm Ψ N (ℓ i)) =
      (c : ℝ) * II (FlBlock Ψ N) (FlIdx Ψ N) (PFl Ψ N) d (fun i => linLine Ψ N (ℓ i))

def FsInvPow.Statement : Prop :=
  ∀ (II : IntersectionSystem) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι))
    (d : ℕ), IsIntersectionSystem II → IsArithVar P d →
    II K ι P d (fun _ => fsHerm (ι := ι) (fun _ => -1)) = (-1) ^ d * II K ι P d (fun _ => GroundTheory.Heights₂.Heights.fsMulti ι)

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.RegWeightLevi
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open Filter Topology Metric ReciprocityTheory.ChartRestriction.G.Geo
open ReciprocityTheory.AnForm (levi)

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P : Ideal (MRing ι)} {d : ℕ} {M : CxModel P d} {Xo : Set ((Σ k, ι k) → ℂ)} {A : HermLine ι}

theorem LogLogRegularisationSetting.eventually_closedBall_subset (S : LogLogRegularisationSetting M Xo A) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ j, ∀ x ∈ closure (S.R.mid j),
      closedBall (S.R.chart j x) t ⊆ (S.R.chart j).target := by
  refine Filter.eventually_all.2 fun j => ?_
  have hc : IsCompact (closure (S.R.mid j)) := isClosed_closure.isCompact
  have himg : IsCompact (S.R.chart j '' closure (S.R.mid j)) :=
    hc.image_of_continuousOn ((S.R.chart j).continuousOn.mono (S.R.closure_mid j))
  have hsub : S.R.chart j '' closure (S.R.mid j) ⊆ (S.R.chart j).target := by
    rintro _ ⟨x, hx, rfl⟩
    exact (S.R.chart j).map_source (S.R.closure_mid j hx)
  obtain ⟨δ, hδ, hδs⟩ := himg.exists_cthickening_subset_open (S.R.chart j).open_target hsub
  filter_upwards [Ioo_mem_nhdsGT hδ] with t ht x hx
  exact (closedBall_subset_cthickening (Set.mem_image_of_mem _ hx) t).trans
    ((cthickening_mono ht.2.le _).trans hδs)

theorem LogLogRegularisationSetting.eventually_chartLevi (S : LogLogRegularisationSetting M Xo A) (hS : S.IsTied) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), M.atlas.Smooth (S.regWeight t) ∧
      ∀ k : Fin S.R.N, ∀ x ∈ S.R.mid k, ∀ w : Fin d → ℂ,
        -(4 * S.Cη * S.e1 t) * ‖w‖ ^ 2 ≤
          levi (S.R.chartFun (S.regWeight t) k) (S.R.chart k x) w := by
  filter_upwards [self_mem_nhdsWithin, S.eventually_closedBall_subset, hS.compare] with t ht hball hcmp
  have hε : 0 < S.e1 t := lt_of_lt_of_le ht (S.e1_ge t ht)
  exact GroundTheory.Heights₂.Heights.Regular.GlueRegularised.full M.Xc d M.atlas S.R S.ρ S.η S.Cη (S.K t) t (S.e1 t)
    S.cutoff ht hε hball hcmp

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsHodgeFlagNeZero
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def HodgeFlagNeZero.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (Pl : PlueckerData D) (H : HodgeData D)
    (B : AdaptedBasis H) (τ : Ψ) (i : Fin (D.N - 1)), ∃ m, Pl.pluecker0 B τ i m ≠ 0

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsHodgeFlagRatioTrdeg
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def HodgeFlagRatioTrdeg.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (Pl : PlueckerData D) (H : HodgeData D)
    (B : AdaptedBasis H) (c : ∀ k, Pl.ιY k), (∀ k, Pl.flagGenericPoint B ⟨k, c k⟩ ≠ 0) →
    Algebra.trdeg ℤ (Subfield.closure (coneRatios (Pl.flagGenericPoint B) c)) = ((D.n + D.flagDim0 : ℕ) : Cardinal)

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end
