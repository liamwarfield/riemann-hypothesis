module

public import Formalism.LocalToGlobal.ProjectiveLattices.CrudeVal
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjEmbRtOfNe
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.DegreeGenericOfDegree
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SignedConvergenceStatementHolds
public import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.Imports
public import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.BigLineBundleMoriwaki
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.RingKrullDimLocalizationInt
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PSmallGenHeightsNonneg
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PProjAvoidingForm
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PAvoidFormFinite
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFibreNormMax
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PtsIntegralCurveConst

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Statements.GeometryStatements.ExistsAlgPtOff
section -- merged from Development.AutomorphicSpectrum.Statements.GeometryStatements.ReadsRootsFinZero
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Small

open MvPolynomial NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj (Rul Ix ex sec ramOverZ)
open GlobalTheory.CompanionTheory.Ar.Ref (pjSys UnifAll)

def htExp (p : ℕ) : ℝ := if p = 2 then 2 else 1 / ((p : ℝ) - 1)

def latExp (E : Type) [Field E] [NumberField E] (S : Finset ℕ) (p : ℕ) : ℝ :=
  if p ∈ S then htExp p + (padicValInt p (discr E) : ℝ) / Module.finrank ℚ E else 0

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {RM : Top.RootModel (CMType H) (D.p + D.q)}
  {Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))} {Fx : FixedData Y Sys}
  {Or : RootOrigin Y S RM Fx}

def ReadsRootsFin (Or : RootOrigin Y S RM Fx) {p : ℕ} [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p)
    (t : Ix D → ℝ) (θ : ℝ) : Prop :=
  ∀ ρ : RootIx D, ∃ w : PadicAlgCl p, HasVal RM.y (RM.xdeg ρ) (Or.e ρ)⁻¹ z w ∧ w ≠ 0 ∧
    |Real.log (supMet (RM.xdeg ρ) z) - Real.log (‖w‖ / t (rootFrameIx D ρ) ^ HodgeCpt.rootSgn D ρ)| ≤
      θ * Real.log p

theorem htExp_pos {p : ℕ} (hp : p.Prime) : 0 < htExp p := by
  unfold htExp
  split_ifs
  · norm_num
  · have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    exact one_div_pos.2 (by linarith)

theorem latExp_nonneg (E : Type) [Field E] [NumberField E] (S : Finset ℕ) {p : ℕ} (hp : p.Prime) :
    0 ≤ latExp E S p := by
  unfold latExp
  split_ifs
  · have := htExp_pos hp
    positivity
  · exact le_rfl


end GlobalTheory.CompanionTheory.Ar.Small
end
end

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Small.ReadFinTest

open MvPolynomial NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj (Rul Ix ex sec ramOverZ)
open GlobalTheory.CompanionTheory.Ar.Ref (pjSys UnifAll)

section Pts

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem aeval_inst {σ R : Type} [CommRing R] (A B : Algebra ℤ R) (x : σ → R) (f : MvPolynomial σ ℤ) :
    (letI := A; aeval x f) = (letI := B; aeval x f) := by
  rw [Subsingleton.elim A B]

theorem mConeMap_form (y : (Σ k, ι k) → Ω) {g : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d) :
    mConeMap y g = (∏ k, X k ^ d k) * C (aeval y g) := by
  have h := aeval_blockScale hg (fun k => (X k : MvPolynomial K Ω)) (fun p => C (y p))
  have h2 : ∀ f : MRing ι, eval₂ (Int.castRingHom _) (fun p => (C (y p) : MvPolynomial K Ω)) f = C (aeval y f) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => rw [eval₂_C]; simp
    | add f f' h h' => rw [eval₂_add, h, h', map_add (f := _), map_add (f := _)]
    | mul_X f p h => rw [eval₂_mul, h, eval₂_X, map_mul, map_mul, aeval_X]
  rw [← h2]
  refine Eq.trans ?_ (h.trans ?_)
  · unfold mConeMap
    simp only [mul_comm]
    exact aeval_inst _ _ _ _
  · rfl

theorem hasVal_unique {y : (Σ k, ι k) → Ω} {a : K → ℤ} {s : Ω} {𝕜 : Type} [Field 𝕜] {z : (Σ k, ι k) → 𝕜}
    (hz : z ∈ ptsOver 𝕜 (mCoordIdeal y)) {w w' : 𝕜} (h : HasVal y a s z w) (h' : HasVal y a s z w') : w = w' := by
  obtain ⟨dg, dh, g, h, hg, hh, hd, e, hz0, ez⟩ := h
  obtain ⟨dg', dh', g', h', hg', hh', hd', e', hz0', ez'⟩ := h'
  have hm : g * h' - g' * h ∈ mCoordIdeal y := by
    show mConeMap y _ = 0
    rw [map_sub, map_mul, map_mul, mConeMap_form y hg, mConeMap_form y hh, mConeMap_form y hg',
      mConeMap_form y hh', e, e']
    have : (∏ k, (X k : MvPolynomial K Ω) ^ dg k) * ∏ k, X k ^ dh' k = (∏ k, X k ^ dg' k) * ∏ k, X k ^ dh k := by
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← pow_add, ← pow_add]
      congr 1
      have := hd k; have := hd' k; omega
    simp only [map_mul]
    linear_combination (C s * C (aeval y h) * C (aeval y h')) * this
  have := hz.2 _ hm
  rw [map_sub, map_mul, map_mul, ez, ez'] at this
  have h3 : (w - w') * (aeval z h * aeval z h') = 0 := by linear_combination this
  exact sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_right (mul_ne_zero hz0 hz0'))

end Pts

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {RM : Top.RootModel (CMType H) (D.p + D.q)}
  {Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))} {Fx : FixedData Y Sys}


end GlobalTheory.CompanionTheory.Ar.Small.ReadFinTest
end
end

section -- merged from Development.AutomorphicSpectrum.Statements.GeometryStatements.ExistsRingHomComplex
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ProvConj

open MeasureTheory _root_.Metric Filter Topology
open ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.M
open GroundTheory.Heights₂.Heights.Regular hiding le_tmax tmax_le
open GroundTheory.Heights₂.Heights.LowerBoundFree ReciprocityTheory.ChartRestriction.G.Geo

section Ext

variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X}

variable (B : BoundedPshData A) (j : Fin B.N) (V U : Set X) (hV : IsOpen V) (hU : IsOpen U) (hUV : closure U ⊆ V)
    (hVj : V ⊆ B.mid j)

end Ext

section HidaSetting

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {d : ℕ} {M : CxModel P d}
  {Xo : Set ((Σ k, ι k) → ℂ)} {a : K → ℤ} {w : ((Σ k, ι k) → ℂ) → ℝ}

end HidaSetting

section Main

open MvPolynomial

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
  {D : ComponentData II Ψ K ι Ω E} {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt]




end Main

section Points

open MvPolynomial GroundTheory.Heights₂.Heights.Targets.LiftGraphPoints

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem aeval_scaled_eq_zero (y : (Σ k, ι k) → Ω) (T : K → Ω) {f : MRing ι} (hf : f ∈ mCoordIdeal y) :
    aeval (fun p : Σ k, ι k => y p * T p.1) f = 0 := by
  have h0 : mConeMap y f = 0 := hf
  have h : ∀ f : MRing ι, aeval (fun p : Σ k, ι k => y p * T p.1) f = eval T (mConeMap y f) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp [hp, hq]
    | mul_X p i hp => rw [map_mul, map_mul, map_mul, hp]; simp [mConeMap]
  rw [h, h0, map_zero]

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem y_ne_of_X_notMem (y : (Σ k, ι k) → Ω) {p : Σ k, ι k} (h : (X p : MRing ι) ∉ mCoordIdeal y) : y p ≠ 0 := by
  intro h0
  apply h
  rw [mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0, C_0, zero_mul]

theorem exists_bound (F : MRing ι) : ∃ M : ℕ, ∀ M', M ≤ M' → ∀ m ∈ F.support, ∀ k, ∑ i, m ⟨k, i⟩ ≤ M' := by
  classical
  refine ⟨∑ m ∈ F.support, ∑ p, m p, fun M' hM' m hm k => le_trans ?_ hM'⟩
  calc ∑ i, m ⟨k, i⟩ ≤ ∑ k, ∑ i, m ⟨k, i⟩ :=
        Finset.single_le_sum (f := fun k => ∑ i, m ⟨k, i⟩) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    _ = ∑ p, m p := (Fintype.sum_sigma _).symm
    _ ≤ _ := Finset.single_le_sum (f := fun m : (Σ k, ι k) →₀ ℕ => ∑ p, m p) (fun _ _ => Nat.zero_le _) hm

theorem valAt_ne_zero {y : (Σ k, ι k) → Ω} {p : ℕ} (hp : p ≠ 0) {b : K → ℤ} {f g : MRing ι}
    (h : IsVerticalDivisorAt (mCoordIdeal y) p b f g) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y))
    (c : ∀ k, ι k) (hc : ∀ k, z ⟨k, c k⟩ ≠ 0) (hP : IsMultiHomogIdeal (mCoordIdeal y)) :
    valAt y (aeval y f / aeval y g * chartMono y c (-b)) z ≠ 0 := by
  classical
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => y_ne_of_X_notMem y fun hX => hc k (by simpa using hz.2 _ hX)
  set z' : (Σ k, ι k) → ℂ := fun q => (z ⟨q.1, c q.1⟩)⁻¹ * z q with hz'
  set y' : (Σ k, ι k) → Ω := fun q => y q * (y ⟨q.1, c q.1⟩)⁻¹ with hy'
  have hz'P : z' ∈ mcPts (mCoordIdeal y) :=
    mcPts_smul hP (fun k => (z ⟨k, c k⟩)⁻¹) (fun k => inv_ne_zero (hc k)) hz
  have hz1 : ∀ k, z' ⟨k, c k⟩ = 1 := fun k => inv_mul_cancel₀ (hc k)
  have hy1 : ∀ k, y' ⟨k, c k⟩ = 1 := fun k => mul_inv_cancel₀ (hyc k)
  obtain ⟨u, v, hu, hv, huv⟩ := h.unit_off_fibre (RingHom.ker (aeval z' : MRing ι →ₐ[ℤ] ℂ)) (RingHom.ker_isPrime _)
    (fun a ha => by rw [RingHom.mem_ker, ← eval_map_int]; exact hz'P.2 a ha)
    (fun k => ⟨c k, by simp [RingHom.mem_ker, hz1]⟩) (by simpa [RingHom.mem_ker] using hp)
  rw [RingHom.mem_ker] at hu hv
  obtain ⟨Mu, hMu⟩ := exists_bound u
  obtain ⟨Mv, hMv⟩ := exists_bound v
  have hU := homogAt_isMultiHomog c (Mu + Mv) u (hMu _ (by omega))
  have hV := homogAt_isMultiHomog c (Mu + Mv) v (hMv _ (by omega))
  have sy : ∀ q : Σ k, ι k, y q = y ⟨q.1, c q.1⟩ * y' q := fun q => by
    simp only [hy']; field_simp [hyc q.1]
  have sz : ∀ q : Σ k, ι k, z q = z ⟨q.1, c q.1⟩ * z' q := fun q => by
    simp only [hz']; field_simp [hc q.1]
  have eU := aeval_scale hU (fun k => z ⟨k, c k⟩) z' z sz
  have eV := aeval_scale hV (fun k => z ⟨k, c k⟩) z' z sz
  have eU' := aeval_scale hU (fun k => y ⟨k, c k⟩) y' y sy
  have eV' := aeval_scale hV (fun k => y ⟨k, c k⟩) y' y sy
  rw [aeval_homogAt c _ _ _ hz1] at eU eV
  rw [aeval_homogAt c _ _ _ hy1] at eU' eV'
  have hzp : (∏ k, z ⟨k, c k⟩ ^ (Mu + Mv)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)
  have hUz : aeval z (homogAt c (Mu + Mv) u) ≠ 0 := by rw [eU]; exact mul_ne_zero hzp hu
  have hVz : aeval z (homogAt c (Mu + Mv) v) ≠ 0 := by rw [eV]; exact mul_ne_zero hzp hv
  have hUy : aeval y (homogAt c (Mu + Mv) u) ≠ 0 := fun h0 =>
    hUz (by rw [← eval_map_int]; exact hz.2 _ (mem_mCoordIdeal_of_aeval_eq_zero y hU h0))
  obtain ⟨bf, bg, hf, hg, hb⟩ := h.degrees
  have hgy : aeval y g ≠ 0 := fun h0 => h.den_not_mem (mem_mCoordIdeal_of_aeval_eq_zero y hg h0)
  have ef := aeval_scale hf (fun k => y ⟨k, c k⟩) y' y sy
  have eg := aeval_scale hg (fun k => y ⟨k, c k⟩) y' y sy
  have e0 : aeval y' (u * f - v * g) = 0 := aeval_scaled_eq_zero y (fun k => (y ⟨k, c k⟩)⁻¹) huv
  rw [map_sub, map_mul, map_mul] at e0
  have hm : chartMono y c (-b) * ∏ k, y ⟨k, c k⟩ ^ bf k = ∏ k, y ⟨k, c k⟩ ^ bg k := by
    rw [chartMono, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hyc k), ← hb]
    congr 1
    simp
  have hval : IsValueAt y (aeval y f / aeval y g * chartMono y c (-b)) z
      (eval z (map (Int.castRingHom ℂ) (homogAt c (Mu + Mv) v)) /
        eval z (map (Int.castRingHom ℂ) (homogAt c (Mu + Mv) u))) := by
    refine ⟨_, _, _, hV, hU, hUy, ?_, by rwa [eval_map_int], rfl⟩
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, eq_div_iff hgy, eU', eV', ef, eg, ← hm]
    linear_combination (-(∏ k, y ⟨k, c k⟩ ^ (Mu + Mv)) * chartMono y c (-b) * ∏ k, y ⟨k, c k⟩ ^ bf k) * e0
  rw [valAt_eq hz hval, eval_map_int, eval_map_int]
  exact div_ne_zero hVz hUz

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]

end Points

section Final

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

end Final

end GlobalTheory.CompanionTheory.Ar.ProvConj

namespace GlobalTheory.CompanionTheory.Ar.ProvParts

section An

open MeasureTheory _root_.Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff
open GlobalTheory.CompanionTheory.Ar.Giv

section PullTop

variable {e : ℕ} {X : Type} [TopologicalSpace X]

end PullTop

end An

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

end GlobalTheory.CompanionTheory.Ar.ProvParts
end
end
