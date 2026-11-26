module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPolyDivDet
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.SupTrace
public import ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.Statement
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffineOpenAndIsPushout
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.FockWeightWedgeLowerModes

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DegVal

open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp
open scoped NNReal

section Generic

variable {K V Ω : Type} [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]

def ratioField (ev : V →ₗ[K] Ω) : IntermediateField K Ω :=
  IntermediateField.adjoin K {a | ∃ v w, a = ev v / ev w}

def GenRatios (ev : V →ₗ[K] Ω) : Prop := ev ≠ 0 ∧ ratioField ev = ⊤

def ValBound (ev : V →ₗ[K] Ω) (τ : ℕ) (t : Ω) : Prop :=
  ∀ ν : Valuation Ω ℝ≥0, (∀ a : K, a ≠ 0 → ν (algebraMap K Ω a) = 1) → ∃ v, ν t ≤ ν (ev v) ^ τ

end Generic

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

set_option synthInstance.maxHeartbeats 100000 in
def BirOn (Z : Comp Xo c) (G : WTZ E) : Prop := GenRatios (genPoint Z (cuspOn U Z G))

set_option synthInstance.maxHeartbeats 100000 in
def ValMult (Z : Comp Xo c) (G G' : WTZ E) : Prop :=
  ∃ (a : ℕ) (θ : Rul Xo c), 1 ≤ a ∧ genVal Z θ ≠ 0 ∧ ∀ (k : ℕ), 1 ≤ k → ∀ f ∈ cuspOn U Z ((a * k) • G'),
    θ ^ k * f ∈ cuspOn U Z ((a * k) • G) ∧ ValBound (genPoint Z (cuspOn U Z G)) (a * k) (genVal Z (θ ^ k * f))

end GlobalTheory.DegVal
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.FrameEval

namespace GlobalTheory.FlagTan

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

section Local

variable {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]

theorem exists_frMap (φ : S →ₐ[c.F] T) (y : FrPt Xo c S) : ∃ z, FrMap φ y z :=
  GlobalTheory.T.exists_framedPoint_baseChange_algebraMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c S T φ y

theorem frMap_unique {φ : S →ₐ[c.F] T} {y : FrPt Xo c S} {z z' : FrPt Xo c T} (h : FrMap φ y z) (h' : FrMap φ y z') :
    z = z' := (frMap_unique_refl_iff E H Dw l Xo c S T φ y).1 z z' h h'

theorem frMap_id (y : FrPt Xo c S) : FrMap (AlgHom.id c.F S) y y :=
  (frMap_unique_refl_iff E H Dw l Xo c S S (AlgHom.id c.F S) y).2.1

theorem frMap_comp {U : Type} [CommRing U] [Algebra c.F U] {φ : S →ₐ[c.F] T} {ψ : T →ₐ[c.F] U} {χ : S →ₐ[c.F] U}
    {y : FrPt Xo c S} {z : FrPt Xo c T} {w : FrPt Xo c U} (h : FrMap φ y z) (h' : FrMap ψ z w)
    (e : ∀ a, ψ (φ a) = χ a) : FrMap χ y w := by
  obtain rfl : ψ.comp φ = χ := AlgHom.ext e
  exact frMap_trans (Xo := Xo) (c := c) _ _ _ φ ψ y z w h h'

theorem frMap_of_comp {U : Type} [CommRing U] [Algebra c.F U] {φ : S →ₐ[c.F] T} {ψ : T →ₐ[c.F] U}
    {χ : S →ₐ[c.F] U} {y : FrPt Xo c S} {z : FrPt Xo c T} {w : FrPt Xo c U} (h : FrMap φ y z) (h' : FrMap χ y w)
    (e : ∀ a, ψ (φ a) = χ a) : FrMap ψ z w := by
  obtain ⟨w', hw⟩ := exists_frMap ψ z
  rwa [frMap_unique h' (frMap_comp h hw e)]

theorem frMap_iff_frChg {φ : S →ₐ[c.F] T} {g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S} {a : S}
    {y y' : FrPt Xo c S} {z z' : FrPt Xo c T} (h : FrChg g a y y') (hz : FrMap φ y z) :
    FrMap φ y' z' ↔ FrChg (fun τ => (g τ).map φ) (φ a) z z' :=
  (frChg_calculus E H Dw l Xo c S).2.2.1 T φ g a y y' z z' h hz

theorem exists_chart [IsLocalRing S] (w w' : FrPt Xo c S) (hw : w'.x = w.x) :
    ∃ (p A : TRing c.F) (j : Sp p.R ⟶ Xo.XF c) (y₀ : FrPt Xo c p.R) (π : p.R →ₐ[c.F] A.R)
      (X : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) A.R) (s : (A.R)ˣ) (u : FrPt Xo c A.R)
      (a a' : A.R →ₐ[c.F] S), OpenChart j y₀ ∧ UnivFrame y₀ π X s u ∧ FrMap a u w ∧ FrMap a' u w' := by
  have hS : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  obtain ⟨xF, h1, h2⟩ := Frames.ChartCover.exists_lift w
  obtain ⟨p, j, y₀, hj, hp⟩ := GlobalTheory.T.exists_openChart_framedPoint_testRing hS E H Dw l Xo c (xF (IsLocalRing.closedPoint S))
  obtain ⟨A, π, X, s, u, hu⟩ := GlobalTheory.T.exists_universalFrame_testRing hS E H Dw l Xo c p y₀
  have key : ∀ z : FrPt Xo c S, z.x = w.x → ∃ a : A.R →ₐ[c.F] S, FrMap a u z := fun z hz => by
    obtain ⟨g, hg, hT⟩ := Frames.ChartCover.near hS hj hu z xF (h1.trans hz.symm) h2 _ hp
    obtain ⟨z', a, h, ha⟩ := hT S (AlgHom.id _ _) (IsLocalRing.notMem_maximalIdeal.1 hg)
    exact ⟨a, frMap_unique h (frMap_id z) ▸ ha⟩
  obtain ⟨a, ha⟩ := key w rfl
  obtain ⟨a', ha'⟩ := key w' hw
  exact ⟨p, A, j, y₀, π, X, s, u, a, a', hj, hu, ha, ha'⟩

theorem fromTest_of_isLocalRing [IsLocalRing S] (w : FrPt Xo c S) :
    FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) w := by
  obtain ⟨-, A, -, -, -, -, -, u, a, -, -, -, ha, -⟩ := exists_chart w w rfl
  exact ⟨A, a, u, ha⟩

theorem evR_eq {f : Rul Xo c}
    (hf : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f) {p : TRing c.F}
    {φ : p.R →ₐ[c.F] S} {u : FrPt Xo c p.R} {w : FrPt Xo c S} (h : FrMap φ u w) : evR Xo c f w = φ (f p u) := by
  have hT : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) w := ⟨p, φ, u, h⟩
  unfold evR evalAt
  rw [dite_eq_left hT]
  exact evalWD_fr (frChartF_of (Frames.chartCoverF_of_secBaseChange GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c)) f hf S
    _ _ _ _ _ _ w hT.choose_spec.choose_spec.choose_spec h

theorem evR_frMap [IsLocalRing S] {f : Rul Xo c}
    (hf : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f) {φ : S →ₐ[c.F] T}
    {y : FrPt Xo c S} {z : FrPt Xo c T} (h : FrMap φ y z) : evR Xo c f z = φ (evR Xo c f y) := by
  obtain ⟨p, a, u, hu⟩ := fromTest_of_isLocalRing y
  rw [evR_eq hf hu, evR_eq hf (frMap_comp (χ := φ.comp a) hu h fun _ => rfl)]
  rfl

theorem evR_frBor [IsLocalRing S] {e : Ix Dw → ℤ} {f : Rul Xo c} (hf : f ∈ secZ Xo c e) {t : Ix Dw → Sˣ}
    {y y' : FrPt Xo c S} (h : FrBor t y y') :
    evR Xo c f y' = ((∏ i, t i ^ e i : Sˣ) : S) * evR Xo c f y := by
  obtain ⟨p, A, j, y₀, π, X, s, u, a, a', hj, hu, ha, ha'⟩ := exists_chart y y' h.1
  obtain ⟨B, uB, uB', tB, q, q', hq, hq', hB, hU⟩ :=
    Frames.univFrame_borelPairs GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c p A j y₀ π X s u hj hu
  obtain ⟨b, e1, e2, e3⟩ := hU S a a' y y' t ha ha' h
  have k : FrMap b uB y := frMap_of_comp hq ha fun x => DFunLike.congr_fun e1 x
  have k' : FrMap b uB' y' := frMap_of_comp hq' ha' fun x => DFunLike.congr_fun e2 x
  have ht : t = fun i => Units.map (b : B.R →* S) (tB i) := funext fun i => Units.ext (e3 i).symm
  rw [evR_eq hf.1 k, evR_eq hf.1 k', hf.2 B tB uB uB' hB, map_mul, ht]
  congr 1
  simp only [← map_zpow, ← map_prod]
  rfl

theorem exists_frPt [IsLocalRing S] (x : Sp S ⟶ Xo.X) (hx : x ≫ Xo.s = sOf c S) : ∃ z : FrPt Xo c S, z.x = x := by
  have hS : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  obtain ⟨xF, h1, h2⟩ : ∃ xF : Sp S ⟶ Xo.XF c, xF ≫ pullback.fst _ _ = x ∧
      xF ≫ pullback.snd _ _ = spMap (algebraMap c.F S) := by
    refine ⟨pullback.lift x (spMap (algebraMap c.F S)) ?_, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    rw [hx, sOf, ← Spec.map_comp]; rfl
  obtain ⟨p, j, y₀, hj, hp⟩ := GlobalTheory.T.exists_openChart_framedPoint_testRing hS E H Dw l Xo c (xF (IsLocalRing.closedPoint S))
  obtain ⟨g, hg, hT⟩ := openChart_factor_near_prime E H Dw l Xo c _ j y₀ hj S xF h2 _ hp
  obtain ⟨ψ, hψ⟩ := hT S (AlgHom.id _ _) (IsLocalRing.notMem_maximalIdeal.1 hg)
  obtain ⟨z, hz⟩ := exists_frMap ψ y₀
  refine ⟨z, ?_⟩
  have hid : spMap (AlgHom.id c.F S).toRingHom = 𝟙 _ := Spec.map_id _
  rw [hz.1, ← hj.2.1, ← Category.assoc, ← hψ, hid, Category.id_comp, h1]

end Local

section Coef

variable (Xo c) (K₀ : Type) [CommRing K₀] [Algebra c.F K₀]

abbrev RulK : Type := K₀ ⊗[c.F] Rul Xo c

def secK (e : Ix Dw → ℤ) : Submodule K₀ (RulK Xo c K₀) := (secZ Xo c e).baseChange K₀

variable {Xo c K₀} {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]

def val (φ : K₀ →ₐ[c.F] S) (y : FrPt Xo c S) : RulK Xo c K₀ →ₗ[c.F] S :=
  TensorProduct.lift ((LinearMap.mul c.F S).compl₁₂ φ.toLinearMap
    (evalL (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y))

@[simp] theorem val_tmul (φ : K₀ →ₐ[c.F] S) (y : FrPt Xo c S) (a : K₀) (f : Rul Xo c) :
    val φ y (a ⊗ₜ f) = φ a * evR Xo c f y := rfl

theorem secK_induction {e : Ix Dw → ℤ} {P : RulK Xo c K₀ → Prop} (h0 : P 0)
    (h1 : ∀ a f, f ∈ secZ Xo c e → P (a ⊗ₜ f)) (h2 : ∀ s s', P s → P s' → P (s + s')) {s : RulK Xo c K₀}
    (hs : s ∈ secK Xo c K₀ e) : P s := by
  obtain ⟨z, rfl⟩ : ∃ z, (secZ Xo c e).subtype.baseChange K₀ z = s := hs
  induction z with
  | add s s' h h' => rw [map_add (f := _)]; exact h2 _ _ h h'
  | tmul a f => exact h1 a f.1 f.2

theorem val_frMap [IsLocalRing S] {e : Ix Dw → ℤ} {s : RulK Xo c K₀} (hs : s ∈ secK Xo c K₀ e)
    {φ : K₀ →ₐ[c.F] S} {ψ : S →ₐ[c.F] T} {χ : K₀ →ₐ[c.F] T} (hχ : ∀ a, ψ (φ a) = χ a) {y : FrPt Xo c S}
    {z : FrPt Xo c T} (h : FrMap ψ y z) : val χ z s = ψ (val φ y s) := by
  refine secK_induction (P := fun s => val χ z s = ψ (val φ y s)) (by simp) (fun a f hf => ?_)
    (fun s s' k k' => ?_) hs
  · simp only [val_tmul, map_mul, hχ, evR_frMap hf.1 h]
  · simp only [map_add (f := _), k, k']

theorem val_frBor [IsLocalRing S] {e : Ix Dw → ℤ} {s : RulK Xo c K₀} (hs : s ∈ secK Xo c K₀ e)
    (φ : K₀ →ₐ[c.F] S) {t : Ix Dw → Sˣ} {y y' : FrPt Xo c S} (h : FrBor t y y') :
    val φ y' s = ((∏ i, t i ^ e i : Sˣ) : S) * val φ y s := by
  refine secK_induction (P := fun s => val φ y' s = ((∏ i, t i ^ e i : Sˣ) : S) * val φ y s) (by simp)
    (fun a f hf => ?_) (fun s s' k k' => ?_) hs
  · simp only [val_tmul, evR_frBor hf h]; ring
  · simp only [map_add (f := _), k, k', mul_add]

end Coef

section Thick

open TrivSqZeroExt hiding map lift

variable {K : Type} [Field K]

instance isLocalRing_trivSqZeroExt {M : Type} [AddCommGroup M] [Module K M] [Module Kᵐᵒᵖ M] [IsCentralScalar K M] :
    IsLocalRing (TrivSqZeroExt K M) :=
  haveI : Nontrivial (TrivSqZeroExt K M) := inl_injective.nontrivial
  .of_isUnit_or_isUnit_one_sub_self fun a => by
    simp only [isUnit_iff_isUnit_fst, fst_sub, fst_one]
    exact IsLocalRing.isUnit_or_isUnit_one_sub_self _


variable (Dw) in
abbrev FIx : Type := Option (Σ σ : E →+* ℂ, Fin (Dw.mult σ) × Fin (Dw.mult σ))

section

variable (K) {M : Type} [AddCommGroup M]

def unip (N : FIx Dw → M) (σ : E →+* ℂ) : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) (TrivSqZeroExt K M) :=
  Matrix.of fun i j => inl ((1 : Matrix _ _ K) i j) + inr (N (some ⟨σ, i, j⟩))

def unip₀ (N : FIx Dw → M) : TrivSqZeroExt K M := inl 1 + inr (N none)

variable {K} [Module K M] [Module Kᵐᵒᵖ M] [IsCentralScalar K M]

theorem isUnit_det_unip (N : FIx Dw → M) (σ : E →+* ℂ) : IsUnit (unip K N σ).det := by
  have e : (fstHom K K M).toRingHom.mapMatrix (unip K N σ) = 1 := by
    ext i j; simp [unip]
  rw [isUnit_iff_isUnit_fst]
  show IsUnit ((fstHom K K M).toRingHom _)
  rw [RingHom.map_det, e, Matrix.det_one]
  exact isUnit_one

theorem isUnit_unip₀ (N : FIx Dw → M) : IsUnit (unip₀ K N) := by
  simp [isUnit_iff_isUnit_fst, unip₀]

end

variable [Algebra c.F K]


variable (c K) in
abbrev red : DualNumber K →ₐ[c.F] K := fstHom c.F K K


variable (c K) in
abbrev cst : K →ₐ[c.F] DualNumber K := inlAlgHom c.F K K


variable (c) in
def dir {ι : Type} [Fintype ι] (m : ι → K) : TrivSqZeroExt K (ι → K) →ₐ[c.F] DualNumber K :=
  (TrivSqZeroExt.map (Fintype.linearCombination K m)).restrictScalars c.F

@[simp] theorem fst_dir {ι : Type} [Fintype ι] (m : ι → K) (z : TrivSqZeroExt K (ι → K)) :
    (dir c m z).fst = z.fst := fst_map _ z

@[simp] theorem snd_dir {ι : Type} [Fintype ι] (m : ι → K) (z : TrivSqZeroExt K (ι → K)) :
    (dir c m z).snd = ∑ k, z.snd k * m k := (snd_map _ z).trans (Fintype.linearCombination_apply _ _ _)

theorem exists_lift {ι : Type} (y : FrPt Xo c K) (X : Sp (TrivSqZeroExt K (ι → K)) ⟶ Xo.X)
    (hX : X ≫ Xo.s = sOf c _) (hy : spMap (fstHom c.F K (ι → K)).toRingHom ≫ X = y.x) :
    ∃ W : FrPt Xo c (TrivSqZeroExt K (ι → K)), W.x = X ∧ FrMap (fstHom c.F K (ι → K)) W y := by
  obtain ⟨z, rfl⟩ := exists_frPt X hX
  obtain ⟨z₀, h₀⟩ := exists_frMap (fstHom c.F K (ι → K)) z
  obtain ⟨g, a, hg, hc⟩ := (frChg_exists_unique E H Dw l Xo c K z₀ y).1 (hy.symm.trans h₀.1.symm)
  obtain ⟨W, hW, -⟩ := existsUnique_frChg E H Dw l Xo c _ z (fun τ => (g τ).map (inlAlgHom c.F K (ι → K)))
    (Units.map (inlAlgHom c.F K (ι → K)).toRingHom.toMonoidHom a) fun τ => by
      have := (hg τ).map (inlAlgHom c.F K (ι → K)).toRingHom
      rwa [RingHom.map_det] at this
  refine ⟨W, hW.1, (frMap_iff_frChg hW h₀).2 ?_⟩
  convert hc using 2 with τ
  · ext i j; simp
  · rfl

end Thick

end GlobalTheory.FlagTan
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid Matrix
open scoped TensorProduct Topology

namespace GlobalTheory.FunObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem natCast_smul_mem_hatL {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (Λ : Submodule (𝓞 E) (Fin n → E)) {𝔪 : Ideal (𝓞 E)} {N : ℕ} (hN : (N : 𝓞 E) ∈ 𝔪) {z : Fin n → E ⊗[F] Formalism.L2.Herm.Af F}
    (hz : z ∈ Formalism.L2.Herm.hatL (F := F) Λ) : N • z ∈ Formalism.L2.Herm.hatL (F := F) (𝔪 • Λ) := by
  unfold Formalism.L2.Herm.hatL Formalism.UG.latS at hz ⊢
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    refine Submodule.subset_span ⟨(N : 𝓞 E) • l, Submodule.smul_mem_smul hN hl, ?_⟩
    funext i
    simp [Nat.cast_smul_eq_nsmul, ← nsmul_eq_mul, TensorProduct.smul_tmul']
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ a hx

theorem eventually_cong_mat {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] Af F)) {N : ℕ} (hN : N ≠ 0) {X : Type} [TopologicalSpace X] {x₀ : X}
    {φ : X → GL (Fin n) (Af F ⊗[F] E)} (hf : Continuous φ) (h₀ : φ x₀ = 1) :
    ∀ᶠ κ in 𝓝 x₀, ∃ z : Matrix (Fin n) (Fin n) (E ⊗[F] Af F), (∀ i j, z i j ∈ Formalism.L2.Herm.intAf F E) ∧
      (β⁻¹ * Formalism.UG.bc (GlobalTheory.Mass.swapTens F E (Af F) : _ →+* _) (φ κ) * β).1 - 1 = N • z := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Af F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Af F) _
  have ho := (GlobalTheory.Mass.intTens_open_compact F E).1
  set s := GlobalTheory.Mass.swapTens F E (Af F)
  let β' : GL (Fin n) (Af F ⊗[F] E) := Formalism.UG.bc (s.symm : _ →+* _) β
  have hβ : Formalism.UG.bc (s : _ →+* _) β' = β := Units.ext (Matrix.ext fun i j => s.apply_symm_apply _)
  let m : X → GL (Fin n) (Af F ⊗[F] E) := fun κ => β'⁻¹ * φ κ * β'
  have hm : Continuous m := (continuous_const.mul hf).mul continuous_const
  have hm1 : m x₀ = 1 := by simp only [m, h₀, mul_one, inv_mul_cancel]
  have hs : ∀ κ, β⁻¹ * Formalism.UG.bc (s : _ →+* _) (φ κ) * β = Formalism.UG.bc (s : _ →+* _) (m κ) := fun κ => by
    simp only [m, map_mul, map_inv, hβ]
  let c : Af F ⊗[F] E := algebraMap F _ (N : F)⁻¹
  have hc : (N : Af F ⊗[F] E) * c = 1 := by
    rw [← map_natCast (algebraMap F (Af F ⊗[F] E)), ← map_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hN), map_one]
  have e3 : ∀ᶠ κ in 𝓝 x₀, ∀ i j, c * ((m κ).1 i j - (1 : Matrix (Fin n) (Fin n) _) i j) ∈ GlobalTheory.Mass.intTens F E := by
    simp only [Filter.eventually_all]
    intro i j
    have h : Continuous fun κ => c * ((m κ).1 i j - (1 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) i j) :=
      continuous_const.mul (((Units.continuous_val.comp hm).matrix_elem i j).sub continuous_const)
    refine (ho.preimage h).mem_nhds ?_
    rw [Set.mem_preimage, hm1, Units.val_one, sub_self, mul_zero]
    exact (GlobalTheory.Mass.intTens F E).zero_mem
  filter_upwards [e3] with κ h3
  refine ⟨Matrix.of fun i j => s (c * ((m κ).1 i j - (1 : Matrix (Fin n) (Fin n) _) i j)), h3, Matrix.ext fun i j => ?_⟩
  rw [hs, Matrix.smul_apply, Matrix.of_apply, ← map_nsmul, nsmul_eq_mul, ← mul_assoc, hc, one_mul, Matrix.sub_apply, map_sub]
  congr 1
  simp only [Matrix.one_apply]; split_ifs <;> simp

theorem mem_congLev_of_cong {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}
    {hc : CMData F E} {J : Matrix (Fin n) (Fin n) E} {Λ : Submodule (𝓞 E) (Fin n → E)} {𝔪 : Ideal (𝓞 E)} {N : ℕ}
    (hN : (N : 𝓞 E) ∈ 𝔪) {β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (hβ : IsFrame β Λ) (h1 : x ∈ UA hc J) (h2 : x ∈ St β)
    {z : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (hz : ∀ i j, z i j ∈ Formalism.L2.Herm.intAf F E)
    (e : (β⁻¹ * x * β).1 - 1 = N • z) : x ∈ congLev hc J Λ 𝔪 := by
  have h3 := (GlobalTheory.LevSplit.mem_St_iff β Λ hβ _).1 h2
  refine ⟨h1, fun y => ⟨h3.1 y, fun hy => ?_⟩, fun y hy => ?_⟩
  · have := h3.2 _ hy
    rwa [mulVec_mulVec, Units.inv_mul, one_mulVec] at this
  · have e1 : x.1 *ᵥ y - y = N • (β.1 *ᵥ (z *ᵥ ((β⁻¹).1 *ᵥ y))) := by
      rw [← mulVec_smul, ← smul_mulVec, ← e, mulVec_mulVec, mulVec_mulVec, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
        Units.mul_inv, ← Units.val_mul, ← Units.val_mul, sub_mulVec, one_mulVec]
      congr 3
      group
    rw [e1]
    refine natCast_smul_mem_hatL Λ hN ((hβ _).2 fun i => ?_)
    rw [mulVec_mulVec, Units.inv_mul, one_mulVec]
    show ∑ j : Fin n, _ * _ ∈ _
    exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hz i j) ((hβ y).1 hy j)

variable {D : D7}

theorem congLev_open_compact (V : HSp D) {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hΛ : Submodule.IsFullLattice D.host.E Λ) {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) :
    IsOpen (((congLev D.sp.cm V.gram Λ 𝔪).comap (finE V) : Subgroup (GA D V)) : Set (GA D V)) ∧
      IsCompact ((levA V (congLev D.sp.cm V.gram Λ 𝔪) : Subgroup (GA D V)) : Set (GA D V)) := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  obtain ⟨β, hβ⟩ := frame_exists_alt D.host.F D.host.E V.rank Λ hΛ
  have ho : IsOpen (((congLev D.sp.cm V.gram Λ 𝔪).comap (finE V) : Subgroup (GA D V)) : Set (GA D V)) := by
    obtain ⟨π, hπ, -⟩ := GlobalTheory.Mass.existsUnique_isFinProj D.sp.cm.sig V.gram
    have hf : Continuous (finHom V) := (continuous_subtype_val.comp hπ.continuous).congr fun κ => hπ κ
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
    filter_upwards [GlobalTheory.ThetaIntegrand.eventually_princ V β ∅,
      eventually_cong_mat β (Ideal.absNorm_eq_zero_iff.not.2 h𝔪) hf (map_one _)] with κ ⟨h1, h2, _⟩ ⟨z, hz, e⟩
    exact mem_congLev_of_cong (Ideal.absNorm_mem 𝔪) hβ h1 h2 hz e
  refine ⟨ho, ?_⟩
  obtain ⟨C, hC, hCm⟩ := GlobalTheory.ParahoricCompact.exists_compact V β
  exact hC.of_isClosed_subset ((GlobalTheory.Ker.CongTop.isClosed_GfC V).inter (Subgroup.isClosed_of_isOpen _ ho))
    fun k hk => hCm k hk.1 ((GlobalTheory.LevSplit.mem_St_iff β Λ hβ _).2
      ⟨fun y => (hk.2.2.1 y).1, fun y => (Subgroup.inv_mem _ hk.2.2.1 y).1⟩)

theorem exists_meas (V : HSp D) (hV : V.SigOK) {q : ℕ} (hq : ∀ τ, (V.sig τ).2 = q) (K : Subgroup (GL (Fin V.rank) (EAf D)))
    (hK : IsOpen ((K.comap (finE V) : Subgroup (GA D V)) : Set (GA D V)) ∧
      IsCompact ((levA V K : Subgroup (GA D V)) : Set (GA D V))) :
    ∃ μ 𝓕, if q = 0 then IsMeasDef V K μ 𝓕 else IsMeasFD V K μ 𝓕 := by
  split_ifs with h
  · choose ν hν hg using fun ρ : D.what₂.Tau =>
      GlobalTheory.Mem.DefiniteMeasure.exists_probHaar (V.sig (tauE D ρ)).1 _ (Or.inr ((hq (tauE D ρ)).trans h))
    obtain ⟨μ, hμ⟩ := GlobalTheory.LevelMeasure.exists_isMeasLevW D V hV K hK.1 hK.2
      (fun _ m => m.IsHaarMeasure ∧ IsProbabilityMeasure m) ν hν (fun ρ => (hg ρ _).2 rfl) fun ρ _ => (hg ρ _).1
    obtain ⟨𝓕, h𝓕⟩ := GlobalTheory.FundDomDiscrete.exists_fundDom D V μ hμ.1
    exact ⟨μ, 𝓕, hμ, h𝓕⟩
  · choose m hm using GlobalTheory.MinfMeasure.exists_isMinf
    obtain ⟨μ, hμ⟩ := GlobalTheory.LevelMeasure.exists_isMeasLevW D V hV K hK.1 hK.2 (fun _ m => IsMinf m) (fun _ => m _ _)
      (fun _ => (hm _ _).1) (fun _ => hm _ _) fun _ _ h => GlobalTheory.LevelMeasure.isMinf_unique (hm _ _) h
    obtain ⟨𝓕, h𝓕⟩ := GlobalTheory.FundDomDiscrete.exists_fundDom D V μ hμ.1
    exact ⟨μ, 𝓕, hμ, h𝓕⟩

end GlobalTheory.FunObj

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.VdmSplit
noncomputable section

open MeasureTheory ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap GlobalTheory.Orb GlobalTheory.OpTrace GlobalTheory.AutomorphicL2Unitary
open Formalism.REAL (UJ KG toM toMK muK)
open GlobalTheory.PsCo.Pc1 (Mat Poly ev blockAlg detbP OmP dMode)
open GlobalTheory.HCChar (dsChar)
open scoped ComplexConjugate InnerProductSpace

namespace GlobalTheory.PsCo.PcEG

open GlobalTheory.PsCo.PcEF

variable {n : ℕ}

def OmDet : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool), ∃ Q : Poly n, ∀ k ∈ Formalism.REAL.Kset ε, ev k Q * ev k (OmP ε).det = physDet ε k

def ClassFn : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (k k' : KG ε), physDet ε (toMK (k'⁻¹ * k * k')) = physDet ε (toMK k) ∧
    ∀ (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
      (T : Mat n → (W →L[ℂ] W)), Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) T →
      trK T (toMK (k'⁻¹ * k * k')) = trK T (toMK k)

def GaInt : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
    ∃ Λ m : Fin n → ℤ, gaW ε lam = (fun a => (Λ a : ℝ)) ∧ (∀ a b, a < b → ε a = ε b → Λ b ≤ Λ a) ∧
      (∀ a, lam a + ((n : ℝ) - 1) / 2 = m a) ∧
      ∀ a, (Λ + ReciprocityTheory.ChartRestriction.TR.Weyl.rhoK ε) a = m a - if ε a then 0 else (pOf ε : ℤ)

def ToKType : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (γ : Fin n → ℝ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [FiniteDimensional ℂ W] (T : Mat n → (W →L[ℂ] W)), IsKIrr ε γ T →
    (∀ v w : W, PolyOnK ε fun k => ⟪w, T k v⟫_ℂ) →
    ∃ T₀ : S7.KType ε γ, ∀ k : S7.KG ε, ReciprocityTheory.ChartRestriction.TR.Weyl.kChar T₀ k = trK T (S7.toMK k)

def VdmSplit : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (t : Fin n → ℂ),
    (∏ a, ∏ b ∈ Finset.Ioi a, (t a - t b)) = ReciprocityTheory.ChartRestriction.TR.Weyl.wdenK ε t * ((-1) ^ sDeg ε *
      ∏ x : GlobalTheory.PsCo.Pc1.Mode ε, (t x.1.1 - t x.1.2))

def PhysTor : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (θ : Fin n → ℝ),
    physDet ε (Matrix.diagonal (tor θ)) = (-1) ^ (pOf ε * qOf ε) * (∏ x : GlobalTheory.PsCo.Pc1.Mode ε, (tor θ x.1.1 - tor θ x.1.2)) *
      ∏ a, tor θ a ^ (-(if ε a then 0 else (pOf ε : ℤ))) ∧
    physDet ε (Matrix.diagonal (tor θ)) * conj (physDet ε (Matrix.diagonal (tor θ))) = (dMode ε θ : ℂ)

def NumShift : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (m : Fin n → ℤ) (c : Bool → ℤ) (t : Fin n → ℂ), (∀ a, t a ≠ 0) →
    ReciprocityTheory.ChartRestriction.TR.Weyl.numK ε (fun a => m a - c (ε a)) t =
      (∑ w ∈ Finset.univ.filter (fun w : Equiv.Perm (Fin n) => ε ∘ w = ε),
        ((Equiv.Perm.sign w : ℤ) : ℂ) * ∏ a, t a ^ m (w.symm a)) * ∏ a, t a ^ (-c (ε a))

def RangeFD : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mat n → (H →L[ℂ] H)) (hσ : IsURepOn (UJset ε) σ), Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) σ → ∀ d : ℕ,
    ∃ L : Submodule ℂ (smD ε σ), FiniteDimensional ℂ L ∧
      (∀ (k : Mat n) (hk : k ∈ Kset ε), ∀ x ∈ L, sigD (isDerivedOn_smE hσ) hk x ∈ L) ∧
      ∀ P : Poly n, P.totalDegree ≤ d → ∀ u : H,
        ∫ k : KG ε, ev (toMK k) P • σ (toMK k) u ∂(muK ε) ∈ L.map (smD ε σ).subtype

def BuildY : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat n → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D),
    IsURepOn (UJset ε) σ → ∀ (hD : IsDerivedOn ε σ D E) (c : ℂ), (∀ v : D, casimir E v = c • v) →
    ∀ L : Submodule ℂ D, FiniteDimensional ℂ L → (∀ (k : Mat n) (hk : k ∈ Kset ε), ∀ x ∈ L, sigD hD hk x ∈ L) →
    ∃ Y : Submodule ℂ (TensorProduct ℂ D (Fock n)), FiniteDimensional ℂ Y ∧ tensFock L ⊓ physicalSubspace ε ≤ Y ∧
      Y ≤ physicalSubspace ε ∧ (∀ y ∈ Y, dD ε E y ∈ Y) ∧ (∀ y ∈ Y, gradT y ∈ Y) ∧
      ∀ (k : Mat n) (hk : k ∈ Kset ε), ∀ y ∈ Y, wK hD hk y ∈ Y

def StrKer : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat n → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D),
    IsURepOn (UJset ε) σ → ∀ (hD : IsDerivedOn ε σ D E) (Y : Submodule ℂ (TensorProduct ℂ D (Fock n)))
      [FiniteDimensional ℂ Y], (∀ y ∈ Y, dD ε E y ∈ Y) → ∀ (hG : ∀ y ∈ Y, gradT y ∈ Y)
      (hK : ∀ (k : Mat n) (hk : k ∈ Kset ε), ∀ y ∈ Y, wK hD hk y ∈ Y),
    ∃ (Z : Submodule ℂ (TensorProduct ℂ D (Fock n))) (_ : FiniteDimensional ℂ Z)
      (hZK : ∀ (k : Mat n) (hk : k ∈ Kset ε), ∀ y ∈ Z, wK hD hk y ∈ Z) (Γ : TSub Z →ₗ[ℂ] TSub Z),
      Z ≤ Y ∧ (∀ y ∈ Z, dD ε E y = 0) ∧ ∀ (k : Mat n) (hk : k ∈ Kset ε),
        LinearMap.trace ℂ Y ((gradT ∘ₗ wK hD hk).restrict (fun y hy => hG _ (hK k hk y hy))) =
          LinearMap.trace ℂ (TSub Z) (Γ ∘ₗ (tOp hD hZK k : TSub Z →ₗ[ℂ] TSub Z))

def StrIdx : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (P : Poly n), ∃ d : ℕ,
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mat n → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D),
    IsURepOn (UJset ε) σ → ∀ (hD : IsDerivedOn ε σ D E) (L : Submodule ℂ D) [FiniteDimensional ℂ L],
    (∀ (k : Mat n) (hk : k ∈ Kset ε), ∀ x ∈ L, sigD hD hk x ∈ L) →
    (∀ Q : Poly n, Q.totalDegree ≤ d → ∀ u : H,
      ∫ k : KG ε, ev (toMK k) Q • σ (toMK k) u ∂(muK ε) ∈ L.map D.subtype) →
    ∀ (Y : Submodule ℂ (TensorProduct ℂ D (Fock n))) [FiniteDimensional ℂ Y], tensFock L ⊓ physicalSubspace ε ≤ Y →
      Y ≤ physicalSubspace ε → ∀ (hG : ∀ y ∈ Y, gradT y ∈ Y)
      (hK : ∀ (k : Mat n) (hk : k ∈ Kset ε), ∀ y ∈ Y, wK hD hk y ∈ Y) (B : H →L[ℂ] H),
      (∀ w, B w = ∫ k : KG ε, (ev (toMK k) P * physDet ε (toMK k)) • σ (toMK k) w ∂(muK ε)) →
      ∃ hB : ∀ x, (B : H →ₗ[ℂ] H) x ∈ L.map D.subtype,
        LinearMap.trace ℂ (L.map D.subtype) ((B : H →ₗ[ℂ] H).restrict fun x _ => hB x) =
          ∫ k : KG ε, ev (toMK k) P * LinearMap.trace ℂ Y ((gradT ∘ₗ wK hD (k := toMK k) k.2).restrict
            (fun y hy => hG _ (hK _ k.2 y hy))) ∂(muK ε)

def HWVec : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat n → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D),
    IsURepOn (UJset ε) σ → ∀ (hD : IsDerivedOn ε σ D E) (Z : Submodule ℂ (TensorProduct ℂ D (Fock n)))
      [FiniteDimensional ℂ Z] (hZK : ∀ (k : Mat n) (hk : k ∈ Kset ε), ∀ y ∈ Z, wK hD hk y ∈ Z)
      (γ : Fin n → ℝ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
      (T : Mat n → (W →L[ℂ] W)), IsKIrr ε γ T → ∀ Φ : W →ₗ[ℂ] TSub Z, Φ ≠ 0 →
      (∀ k ∈ Formalism.REAL.Kset ε, ∀ v, Φ (T k v) = tOp hD hZK k (Φ v)) →
      ∃ z ∈ Z, z ≠ 0 ∧ IsKHWVec ε (diagE ε (eT E) cpT cmT) γ z

def CoordFD : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M]
    (E : Fin n → Fin n → Module.End ℂ M) (Z : Submodule ℂ (TensorProduct ℂ M (Fock n))), FiniteDimensional ℂ Z →
    IsKStableSub ε (diagE ε (eT E) cpT cmT) Z →
    FiniteDimensional ℂ (coordSpan Z) ∧ IsKStableSub ε E (coordSpan Z)

def CasCoord : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M]
    (E : Fin n → Fin n → Module.End ℂ M), IsGlRep E → ∀ z : TensorProduct ℂ M (Fock n),
    IsKHWVec ε (diagE ε (eT E) cpT cmT) (gaW ε lam) z → dD ε E z = 0 →
    ∀ s, casimir E (tco s z) = (casVal lam : ℂ) • tco s z

def AlgDatum : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Gap3 ε lam →
    ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (E : Fin n → Fin n → Module.End ℂ M),
    IsGlRep E → IsInfUnitary ε E → ∀ z : TensorProduct ℂ M (Fock n), z ≠ 0 → z ∈ physicalSubspace ε →
    IsKHWVec ε (diagE ε (eT E) cpT cmT) (gaW ε lam) z →
    (∀ s, casimir E (tco s z) = (casVal lam : ℂ) • tco s z) →
    ∀ S : Submodule ℂ M, FiniteDimensional ℂ S → IsKStableSub ε E S → (∀ s, tco s z ∈ S) →
    ∃ V : Submodule ℂ M, IsKIrrHW ε E (lowK ε lam) V ∧ V ≠ ⊥ ∧ ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v

def CptCase : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), pOf ε = 0 ∨ qOf ε = 0 →
    (∀ k, physDet ε k = 1) ∧ sDeg ε = 0 ∧
    ∀ (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] (D : Mat n → (X →L[ℂ] X)), Formalism.MainNotions.S.IsDS ε lam D →
      FiniteDimensional ℂ X ∧ IsKIrr ε (gaW ε lam) D

def TorusId : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (Λ m : Fin n → ℤ), (∀ a, lam a + ((n : ℝ) - 1) / 2 = m a) →
    (∀ a, (Λ + ReciprocityTheory.ChartRestriction.TR.Weyl.rhoK ε) a = m a - if ε a then 0 else (pOf ε : ℤ)) →
    ∀ θ : Fin n → ℝ, Function.Injective (tor θ) → ∀ x : ℂ,
      ReciprocityTheory.ChartRestriction.TR.Weyl.wdenK ε (tor θ) * x = ReciprocityTheory.ChartRestriction.TR.Weyl.numK ε (Λ + ReciprocityTheory.ChartRestriction.TR.Weyl.rhoK ε) (tor θ) →
      (-1) ^ sDeg ε * x = dsChar ε lam θ * physDet ε (Matrix.diagonal (tor θ))

end GlobalTheory.PsCo.PcEG
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.IsEquivariantToBidual
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits MonoidalCategory
  CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (resG_resG resG_self)
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)
open GlobalTheory.QCoh (IsFiniteQC pullbackSections)
open GlobalTheory.DualPull (adj adj_app pull_ext appLE_resG resG_appLE theta toCut ofCut cutEquiv)
open GlobalTheory.VB GlobalTheory.Conormal

namespace GlobalTheory.LieVB

section Eigen

variable {X Y : Scheme.{0}} {F G : X.Modules} {O : Type} [CommRing O] {ρ : O →+* End F}
  {ρ' : O →+* End G} (σ : O →+* Γ(X, ⊤))

theorem isEquivariant_inv {φ : F ≅ G} (h : IsEquivariant ρ ρ' φ.hom) :
    IsEquivariant ρ' ρ φ.inv := fun a => by
  rw [Iso.comp_inv_eq, Category.assoc, h a, Iso.inv_hom_id_assoc]

variable (ρ)

theorem smul_eq_smulHom_comp (a : Γ(X, ⊤)) (φ : F ⟶ G) : a • φ = smulHom F a ≫ φ :=
  (smul_hom_def a φ).trans (smulHom_comp a φ).symm

theorem dualMap_smul (a : Γ(X, ⊤)) (φ : F ⟶ G) : dualMap (a • φ) = a • dualMap φ := by
  rw [smul_eq_smulHom_comp, dualMap_comp, dualMap_smulHom]
  rfl

def dualQuotHom : dual (eigenQuot ρ σ) ⟶ eigen (dualAct ρ) σ :=
  eigenLift (ρ := dualAct ρ) (σ := σ) (dualMap (eigenπ ρ σ)) fun a => by
    rw [act_dualAct, ← dualMap_comp, act_eigenπ, dualMap_smul]

instance isIso_dualQuotHom : IsIso (dualQuotHom ρ σ) := by
  refine Twist.isIso_of_bijective _ fun V => ⟨Function.Injective.of_comp
    (f := (eigenι (dualAct ρ) σ).app V) (QCoh.injective_app_of_mono (dualMap (eigenπ ρ σ)) V),
    fun s => ?_⟩
  let l := (eigenι (dualAct ρ) σ).app V s
  have hl (a : O) : act ρ a ≫ toCut l = σ a • toCut l := by
    ext W t
    apply (cutEquiv V W).injective
    have := congrArg (fun m => dualApp m (DualPull.cutO_le' V W) (resM F (DualPull.cutO_le V W) t))
      (mem_eigenSub_iff.1 ((eigenSub (dualAct ρ) σ).incl_app_mem s) a)
    refine ((DualPull.toCut_app l W _).trans ?_).trans (DualPull.cutEquiv_smul V W _ _).symm
    refine (congrArg _ (app_resM (act ρ a) _ t).symm).trans (this.trans ?_)
    rw [dualApp_smul, resG_resG]
    exact congrArg₂ (fun x y : Γ(X, DualPull.cutO V W) => x * y) (resG_resG _ _ _).symm rfl
  refine ⟨ofCut (eigenDesc _ hl), (eigenSub (dualAct ρ) σ).incl_app_injective V
    (dual_ext fun W h t => ?_)⟩
  refine (DualPull.dualApp_ofCut _ h ((eigenπ ρ σ).app W t)).trans ?_
  rw [show (eigenDesc _ hl).app W ((eigenπ ρ σ).app W t) = (toCut l).app W t from
    congr(($(eigenπ_desc ρ σ _ hl)).app W t), DualPull.toCut_app, ← dualApp_resM, resM_resM,
    resM_self]
  rfl

def dualQuotIso : dual (eigenQuot ρ σ) ≅ eigen (dualAct ρ) σ := asIso (dualQuotHom ρ σ)

theorem dualQuotIso_hom_ι :
    (dualQuotIso ρ σ).hom ≫ eigenι _ _ =
      dualMap (eigenπ ρ σ) := by
  simp only [dualQuotIso, asIso_hom, dualQuotHom, eigenLift_ι]

def pullbackQuotIso (f : Y ⟶ X) : eigenQuot (pullAct ρ f) (f.appTop.hom.comp σ) ≅
    (Scheme.Modules.pullback f).obj (eigenQuot ρ σ) where
  hom := eigenDesc ((Scheme.Modules.pullback f).map (eigenπ ρ σ)) fun a => by
    rw [act_pullAct, ← Functor.map_comp, act_eigenπ, pullback_map_smul]; rfl
  inv := adj f (eigenDesc ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
    (eigenπ (pullAct ρ f) (f.appTop.hom.comp σ))) fun a => by
      rw [← Adjunction.homEquiv_naturality_left, smul_eq_smulHom_comp,
        ← Adjunction.homEquiv_naturality_left, pullback_map_smulHom, ← smul_eq_smulHom_comp]
      exact congrArg _ (act_eigenπ (pullAct ρ f) _ a))
  hom_inv_id := by
    rw [← cancel_epi (eigenπ _ _), eigenπ_desc_assoc, Category.comp_id, adj,
      ← Adjunction.homEquiv_naturality_left_symm, eigenπ_desc, Equiv.symm_apply_apply]
  inv_hom_id := by
    rw [← cancel_epi ((Scheme.Modules.pullback f).map (eigenπ ρ σ)), ← Category.assoc, adj,
      ← Adjunction.homEquiv_naturality_left_symm, eigenπ_desc, Equiv.symm_apply_apply, eigenπ_desc,
      Category.comp_id]

theorem hom_ext_of_isFrame {κ : Type} [Fintype κ] {e : κ → Γ(F, ⊤)} (he : IsFrame e)
    {φ ψ : F ⟶ G} (h : ∀ i, φ.app ⊤ (e i) = ψ.app ⊤ (e i)) : φ = ψ := by
  ext V s
  refine congr($((he.basis le_top).ext (f₁ := QCoh.appLinear φ V) (f₂ := QCoh.appLinear ψ V)
    fun i => ?_) s)
  rw [IsFrame.basis_apply]
  exact (app_resM φ _ _).trans ((congrArg _ (h i)).trans (app_resM ψ _ _).symm)

end Eigen

theorem isFrame_d_Spec {R A : CommRingCat.{0}} [Algebra R A] (ε : A →ₐ[R] R)
    {π : Spec A ⟶ Spec R} {e : Spec R ⟶ Spec A} (he : e ≫ π = 𝟙 _)
    (hπ : π = Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (hε : e = Spec.map (CommRingCat.ofHom ε.toRingHom)) {κ : Type} [Fintype κ]
    (b : Module.Basis κ R (AugCot ε)) (a : κ → A) (hb : ∀ i, b i = AugCot.d ε (a i)) :
    IsFrame fun i => d he (W := ⊤) (V := ⊤) le_top ((Scheme.ΓSpecIso A).inv (a i)) := by
  subst hπ hε
  exact IsChart.isFrame_d he ⟨isAffineOpen_top _, isAffineOpen_top _, le_top, le_top⟩ ε
    (Scheme.ΓSpecIso R).inv.hom (Scheme.ΓSpecIso A).inv.hom
    (IsPushout.of_vert_isIso (g := (Scheme.ΓSpecIso R).inv) (inl := (Scheme.ΓSpecIso A).inv)
      ⟨Scheme.ΓSpecIso_inv_naturality _⟩)
    (fun x => congr($(Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ε.toRingHom)) x).symm)
    b a hb

end GlobalTheory.LieVB
end
end
