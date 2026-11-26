module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSmoothCuspFormFrechetModerateGrowthRep
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignedUnitaryGroupCompat
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverOfIsIso
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormClassesIffConjUnitaryTorusEllipticElements
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiCongrLeftUpdate
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeCompressionFormulaOfStrictLowestKType
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeDecayGapOfCompressionFormulaGap
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodProjectorSmallestSpaceForms

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SobolevFormEqZeroOnSmoothOfKFiniteDiscreteSeries
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SobolevFormEqZeroOnSmoothOfKFiniteDiscreteSeries
open Classical Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KFiniteDense

open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.TypeSum

section WordCurve

variable {n : ℕ}

theorem dRep_fsum {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : Mx n → (H →L[ℂ] H)} (h : Std ε σ) {Z : Mx n} (hZ : Z ∈ lieSet ε) {ι : Type} (s : Finset ι)
    (c : ι → ℂ) (w : ι → H) (hw : ∀ j, Sm ε σ (w j)) :
    dRep σ Z (∑ j ∈ s, c j • w j) = ∑ j ∈ s, c j • dRep σ Z (w j) := by
  classical
  have hl : ∀ Y ∈ [Z], Y ∈ lieSet ε := by simpa using hZ
  have hsm : ∀ t : Finset ι, Sm ε σ (∑ j ∈ t, c j • w j) := fun t =>
    (GlobalTheory.LowTypeDetermined.smooth (Jm ε) σ).sum_mem fun j _ =>
      (GlobalTheory.LowTypeDetermined.smooth (Jm ε) σ).smul_mem _ (hw j)
  induction s using Finset.induction_on with
  | empty =>
    have := Dw_smul h.1 hl (0 : ℂ) (x := (0 : H)) (GlobalTheory.LowTypeDetermined.smooth (Jm ε) σ).zero_mem
    simp only [zero_smul, Dw, List.foldr_cons, List.foldr_nil] at this
    simpa using this
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have e1 := Dw_add h.1 hl ((GlobalTheory.LowTypeDetermined.smooth (Jm ε) σ).smul_mem (c a) (hw a)) (hsm s)
    have e2 := Dw_smul h.1 hl (c a) (hw a)
    simp only [Dw, List.foldr_cons, List.foldr_nil] at e1 e2
    rw [e1, e2, ih]

theorem exists_coord (ε : Fin n → Bool) : ∃ (d : ℕ) (B : Fin d → Mx n) (φ : Fin d → (Mx n →ₗ[ℝ] ℝ)),
    (∀ i, B i ∈ lieSet ε) ∧ ∀ Y ∈ lieSet ε, Y = ∑ i, φ i Y • B i := by
  let b := Module.finBasis ℝ (GlobalTheory.LowTypeDetermined.lie (Jm ε))
  choose g hg using fun i => LinearMap.exists_extend (b.coord i)
  refine ⟨_, fun i => b i, g, fun i => (b i).2, fun Y hY => ?_⟩
  have e := congrArg Subtype.val (b.sum_repr ⟨Y, hY⟩)
  simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] at e
  conv_lhs => rw [← e]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := LinearMap.congr_fun (hg i) ⟨Y, hY⟩
  simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
  rw [this]
  rfl

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem analyticAt_coord (X Y : Mx n) (φ : Mx n →ₗ[ℝ] ℝ) :
    AnalyticAt ℝ (fun t : ℝ => ((φ (NormedSpace.exp (-(t • X)) * Y * NormedSpace.exp (t • X)) : ℝ) : ℂ)) 0 := by
  have h1 : AnalyticAt ℝ (fun t : ℝ => NormedSpace.exp (t • X)) 0 :=
    AnalyticAt.comp (NormedSpace.exp_analytic (𝕂 := ℝ) _) (analyticAt_id.smul analyticAt_const)
  have h2 : AnalyticAt ℝ (fun t : ℝ => NormedSpace.exp (-(t • X))) 0 :=
    AnalyticAt.comp (NormedSpace.exp_analytic (𝕂 := ℝ) _) (analyticAt_id.smul analyticAt_const).neg
  have h3 : AnalyticAt ℝ (fun t : ℝ => NormedSpace.exp (-(t • X)) * Y * NormedSpace.exp (t • X)) 0 :=
    (h2.fun_mul analyticAt_const).fun_mul h1
  have h4 := ((LinearMap.toContinuousLinearMap φ).analyticAt _).comp h3
  exact (Complex.ofRealCLM.analyticAt _).comp h4

end

theorem wordCurve : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), GlobalTheory.TypeSum.Std ε σ → ∀ X : Matrix (Fin n) (Fin n) ℂ, X ∈ GlobalTheory.SmoothGlob.lieSet ε → ∀ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ Y ∈ l, Y ∈ GlobalTheory.SmoothGlob.lieSet ε) → ∀ v : H, Formalism.MainNotions.S.IsKFin ε σ v → ∃ (m : ℕ) (c : Fin m → ℝ → ℂ) (w : Fin m → H), (∀ j, AnalyticAt ℝ (c j) 0) ∧ (∀ j, Formalism.MainNotions.S.IsKFin ε σ (w j)) ∧ ∀ t : ℝ, List.foldr (Formalism.L2.Theta.dRep σ) v (l.map fun Y => NormedSpace.exp (-(t • X)) * Y * NormedSpace.exp (t • X)) = ∑ j, c j t • w j := by
  intro n ε H _ _ _ σ h X hX l hl v hv
  obtain ⟨d, B, φ, hB, hφ⟩ := exists_coord (n := n) ε
  induction l with
  | nil => exact ⟨1, fun _ _ => 1, fun _ => v, fun _ => analyticAt_const, fun _ => hv, fun t => by simp⟩
  | cons Y l ih =>
    obtain ⟨m, c, w, hc, hw, he⟩ := ih (fun Z hZ => hl Z (List.mem_cons_of_mem _ hZ))
    have hY := hl Y List.mem_cons_self
    let A : ℝ → Mx n := fun t => NormedSpace.exp (-(t • X)) * Y * NormedSpace.exp (t • X)
    have hA : ∀ t, A t ∈ lieSet ε := fun t => by
      show NormedSpace.exp (-(t • X)) * Y * NormedSpace.exp (t • X) ∈ lieSet ε
      rw [Matrix.exp_neg]
      exact GlobalTheory.LowTypeDetermined.conj_mem_lie (isUnit_Jm ε) (exp_mem_UJ hX t) hY
    let e := (finProdFinEquiv (m := m) (n := d)).symm
    refine ⟨m * d, fun k t => c (e k).1 t * ((φ (e k).2 (A t) : ℝ) : ℂ),
      fun k => dRep σ (B (e k).2) (w (e k).1), fun k => (hc _).fun_mul (analyticAt_coord X Y _),
      fun k => isKFin_dRep n ε H σ h _ (hw _) _ (hB _), fun t => ?_⟩
    rw [List.map_cons, List.foldr_cons, he t]
    change dRep σ (A t) _ = _
    rw [dRep_fsum h (hA t) Finset.univ _ w (fun j => h.2.2.1 _ (hw j))]
    have hs : ∀ j, dRep σ (A t) (w j) = ∑ i, ((φ i (A t) : ℝ) : ℂ) • dRep σ (B i) (w j) := fun j => by
      conv_lhs => rw [hφ _ (hA t)]
      exact h.dRep_sum hB (h.2.2.1 _ (hw j)) _
    simp only [hs, Finset.smul_sum, smul_smul]
    rw [← Fintype.sum_prod_type']
    exact (Fintype.sum_equiv e _ _ fun k => rfl).symm

end WordCurve

theorem eq_zero_of_iteratedDeriv_eq_zero : ∀ f : ℝ → ℂ, AnalyticOnNhd ℝ f Set.univ → (∀ m : ℕ, iteratedDeriv m f 0 = 0) → ∀ t, f t = 0 := by
  intro f hf h0 t
  obtain ⟨p, r, hp⟩ := hf 0 trivial
  have hc : ∀ m (y : ℝ), p m (fun _ => y) = 0 := by
    intro m y
    have e1 := hp.factorial_smul 1 m
    rw [← iteratedDeriv_eq_iteratedFDeriv, h0 m] at e1
    have e2 : p m (fun _ => (1 : ℝ)) = 0 := by
      exact (smul_eq_zero.1 e1).resolve_left (Nat.factorial_ne_zero m)
    have e3 := (p m).map_smul_univ (fun _ => y) (fun _ => (1 : ℝ))
    simp only [smul_eq_mul, mul_one] at e3
    rw [e3, e2, smul_zero]
  have hev : f =ᶠ[nhds 0] 0 := by
    have hb : Metric.eball (0 : ℝ) r ∈ nhds 0 := Metric.eball_mem_nhds 0 hp.r_pos
    filter_upwards [hb] with y hy
    have := hp.hasSum (y := y) (by simpa using hy)
    simp only [hc, zero_add] at this
    exact (this.unique hasSum_zero).symm ▸ rfl
  exact hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ trivial hev trivial

section Coef

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Mx n → (H →L[ℂ] H)}

theorem analyticAt_coef (hHC : GlobalTheory.Published.HarishChandraModules) (h : Std ε σ) {ℓ : H →ₗ[ℂ] ℂ}
    (hℓ : Sobolev₂ (lieSet ε) σ ℓ) {v : H} (hv : IsKFin ε σ v) {X : Mx n} (hX : X ∈ lieSet ε) :
    AnalyticAt ℝ (fun t : ℝ => ℓ (σ (NormedSpace.exp (t • X)) v)) 0 := by
  obtain ⟨m, S, Λ, hS, hΛ⟩ := GlobalTheory.LowTypeDetermined.exists_factor (isUnit_Jm ε) h.1 hℓ
  have hsm : Sm ε σ v := h.2.2.1 v hv
  choose N c w hc hw he using fun i => wordCurve n ε H σ h X hX (S i) (hS i) v hv
  have key : ∀ t : ℝ, ℓ (σ (NormedSpace.exp (t • X)) v) =
      ∑ i, ∑ j, c i j t * Λ i (σ (NormedSpace.exp (t • X)) (w i j)) := by
    intro t
    have hg := exp_mem_UJ hX t
    rw [hΛ _ (hsm.translate h.1 hg)]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e1 := Dw_translate h.1 hg hsm (hS i)
    have e2 : (NormedSpace.exp (t • X))⁻¹ = NormedSpace.exp (-(t • X)) := (Matrix.exp_neg _).symm
    simp only [Dw] at e1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e1, e2, he i t, map_sum, map_sum]
    simp only [map_smul, smul_eq_mul]
  have ha : ∀ i j, AnalyticAt ℝ (fun t : ℝ => Λ i (σ (NormedSpace.exp (t • X)) (w i j))) 0 := by
    intro i j
    have := ((hHC.analytic h.1 h.2.1 (hw i j)).clm ((Λ i).restrictScalars ℝ)).analytic_exp (g := 1)
      (one_mem_UJ ε) hX 0
    simpa only [one_mul, ContinuousLinearMap.coe_restrictScalars'] using this
  have hsum : AnalyticAt ℝ (fun t : ℝ => ∑ i, ∑ j, c i j t * Λ i (σ (NormedSpace.exp (t • X)) (w i j))) 0 := by
    exact Finset.analyticAt_fun_sum _ fun i _ => Finset.analyticAt_fun_sum _ fun j _ => (hc i j).fun_mul (ha i j)
  exact hsum.congr (Filter.Eventually.of_forall fun t => (key t).symm)

theorem analyticOnNhd_coef (hHC : GlobalTheory.Published.HarishChandraModules) (h : Std ε σ) {ℓ : H →ₗ[ℂ] ℂ}
    (hℓ : Sobolev₂ (lieSet ε) σ ℓ) {v : H} (hv : IsKFin ε σ v) {X : Mx n} (hX : X ∈ lieSet ε) :
    AnalyticOnNhd ℝ (fun t : ℝ => ℓ (σ (NormedSpace.exp (t • X)) v)) Set.univ := by
  intro t₀ _
  have hg := exp_mem_UJ hX t₀
  have h1 := analyticAt_coef hHC h (sobCont_translate h.1 hℓ hg) hv hX
  have h2 : AnalyticAt ℝ (fun t : ℝ => t - t₀) t₀ := analyticAt_id.sub analyticAt_const
  have h3 := h1.comp_of_eq h2 (sub_self t₀)
  refine h3.congr (Filter.Eventually.of_forall fun t => ?_)
  simp only [Function.comp_def, LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
  rw [← sigma_mul h.1 hg (exp_mem_UJ hX _), ← exp_add_smul, add_sub_cancel]

theorem hasDerivAt_coef1 (h : Std ε σ) {ℓ : H →ₗ[ℂ] ℂ} (hℓ : Sobolev₂ (lieSet ε) σ ℓ) {u : H} (hu : Sm ε σ u)
    {X : Mx n} (hX : X ∈ lieSet ε) (s : ℝ) :
    HasDerivAt (fun t : ℝ => ℓ (σ (NormedSpace.exp (t • X)) u)) (ℓ (σ (NormedSpace.exp (s • X)) (dRep σ X u))) s := by
  have hs := exp_mem_UJ hX s
  have h1 := h.hasDerivAt_sobFun ((sobFun_of_sobCont hℓ).translate h.1 hs) hu hX
  have h2 := HasDerivAt.comp_sub_const s s (by rw [sub_self]; exact h1)
  refine HasDerivAt.congr_of_eventuallyEq h2 (Filter.Eventually.of_forall fun t => ?_)
  show _ = ℓ (σ _ (σ _ u))
  rw [← sigma_mul h.1 hs (exp_mem_UJ hX _), ← exp_add_smul, add_sub_cancel]

theorem isKFin_iterate (h : Std ε σ) {X : Mx n} (hX : X ∈ lieSet ε) (m : ℕ) {u : H} (hu : IsKFin ε σ u) :
    IsKFin ε σ ((dRep σ X)^[m] u) := by
  induction m with
  | zero => exact hu
  | succ m ih => rw [Function.iterate_succ_apply']; exact isKFin_dRep n ε H σ h _ ih X hX

theorem iteratedDeriv_coef (h : Std ε σ) {ℓ : H →ₗ[ℂ] ℂ} (hℓ : Sobolev₂ (lieSet ε) σ ℓ) {X : Mx n}
    (hX : X ∈ lieSet ε) (m : ℕ) : ∀ u : H, IsKFin ε σ u →
    iteratedDeriv m (fun t : ℝ => ℓ (σ (NormedSpace.exp (t • X)) u)) =
      fun t => ℓ (σ (NormedSpace.exp (t • X)) ((dRep σ X)^[m] u)) := by
  induction m with
  | zero => intro u _; simp
  | succ m ih =>
    intro u hu
    have hd : deriv (fun t : ℝ => ℓ (σ (NormedSpace.exp (t • X)) u)) =
        fun t => ℓ (σ (NormedSpace.exp (t • X)) (dRep σ X u)) :=
      funext fun t => (hasDerivAt_coef1 h hℓ (h.2.2.1 u hu) hX t).deriv
    rw [iteratedDeriv_succ', hd, ih _ (isKFin_dRep n ε H σ h u hu X hX)]
    funext t
    rw [Function.iterate_succ_apply]

theorem coef_eq_zero (hHC : GlobalTheory.Published.HarishChandraModules) (h : Std ε σ) {ℓ : H →ₗ[ℂ] ℂ}
    (hℓ : Sobolev₂ (lieSet ε) σ ℓ) (h0 : ∀ u, IsKFin ε σ u → ℓ u = 0) {v : H} (hv : IsKFin ε σ v) {X : Mx n}
    (hX : X ∈ lieSet ε) (t : ℝ) : ℓ (σ (NormedSpace.exp (t • X)) v) = 0 := by
  refine eq_zero_of_iteratedDeriv_eq_zero _ (analyticOnNhd_coef hHC h hℓ hv hX) (fun m => ?_) t
  rw [iteratedDeriv_coef h hℓ hX m v hv]
  simp only [zero_smul, NormedSpace.exp_zero, sigma_one h.1]
  exact h0 _ (isKFin_iterate h hX m hv)

theorem orbit_eq_zero (hHC : GlobalTheory.Published.HarishChandraModules) (h : Std ε σ) {ℓ : H →ₗ[ℂ] ℂ}
    (hℓ : Sobolev₂ (lieSet ε) σ ℓ) (h0 : ∀ u, IsKFin ε σ u → ℓ u = 0) {v : H} (hv : IsKFin ε σ v) {g : Mx n}
    (hg : g ∈ UJset ε) : ℓ (σ g v) = 0 := by
  have hk := mul_exp_neg_polarLog_mem_compact (ε := ε) hg
  have hL' : polarLog g ∈ lieSet ε := (polarLog_mem_hermitian_part (ε := ε) hg).1
  have e : g = (g * NormedSpace.exp (-polarLog g)) * NormedSpace.exp ((1 : ℝ) • polarLog g) := by
    rw [one_smul]; exact polar_decomposition_eq
  rw [e, sigma_mul h.1 (K_le_UJ hk) (exp_mem_UJ hL' 1)]
  exact coef_eq_zero (ℓ := ℓ ∘ₗ (σ (g * NormedSpace.exp (-polarLog g)) : H →ₗ[ℂ] H)) hHC h
    (sobCont_translate h.1 hℓ (K_le_UJ hk)) (fun u hu => h0 _ (isKFin_translate hu hk)) hv hL' 1

end Coef

theorem eq_zero_of_kFin : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau) (ℓ : M.H τ →ₗ[ℂ] ℂ), Sobolev₂ (lieAt V τ) (M.rep τ) ℓ → (∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, ℓ w = 0) → ∀ w ∈ M.sm τ, ℓ w = 0 := by
  intro hHC D V S M τ ℓ hℓ h0 w hw
  haveI : CompleteSpace (M.H τ) := (M.ds τ).1
  have h := std_of_isDS hHC (M.ds τ)
  have hℓ' : Sobolev₂ (lieSet (M.ε τ)) (M.σ τ) ℓ :=
    GlobalTheory.SmoothCyclic.sobCont_transport (M.fr_unit τ) (M.fr_gram τ) hℓ
  obtain ⟨a, ha, ha0⟩ := (Submodule.ne_bot_iff _).1 (GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin_ne_bot M τ)
  have hw' : Sm (M.ε τ) (M.σ τ) w := (GlobalTheory.SmoothCyclic.sm_eq M τ).le hw
  exact h.eq_zero_of_orbit hℓ' (h.2.2.1 a ha) ha0
    (fun g hg => orbit_eq_zero hHC h hℓ' (fun u hu => h0 u hu) ha hg) hw'

end GlobalTheory.KFiniteDense
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SobolevFormEqZeroOnSmoothOfKFiniteDiscreteSeriesStatement
open Classical Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sobolevForm_eq_zero_on_smooth_of_kFinite_discreteSeries : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau) (ℓ : M.H τ →ₗ[ℂ] ℂ), Sobolev₂ (lieAt V τ) (M.rep τ) ℓ → (∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, ℓ w = 0) → ∀ w ∈ M.sm τ, ℓ w = 0 := by
  first | exact @GlobalTheory.KFiniteDense.eq_zero_of_kFin | exact GlobalTheory.KFiniteDense.eq_zero_of_kFin | (intros; apply GlobalTheory.KFiniteDense.eq_zero_of_kFin <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralFrameExtensionOfRankZeroSignature
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralFrameExtensionOfRankZeroSignature
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

namespace GlobalTheory.RankZeroFrames

open GlobalTheory.Models GlobalTheory.Models.RankZero

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem exists_model_int (hD : Dw.p + Dw.q = 0) (Xo : Moduli Dw l) (c : Coeff l) :
    ∃ Y : Model Xo c (Int.castRingHom c.F), PushInvertible Y.t.G Y.t.PP.L := by
  obtain ⟨h₁, h₂⟩ := isIso_moduli GlobalTheory.card_torsion_abelianVariety hD Xo
  let k := spMap (IntermediateField.inclusion c.le).toRingHom
  let β := Int.castRingHom c.F
  have hk : IsIso (pullback.snd Xo.s k) := inferInstance
  let j : Xo.XF c ⟶ pullback (𝟙 (Sp ℤ)) (spMap β) := pullback.snd Xo.s k ≫ inv (pullback.snd _ _)
  have hj : IsIso j := inferInstance
  have hs : Function.Surjective j := (inferInstance : Surjective j).1
  refine ⟨{ X := Sp ℤ, s := 𝟙 _, normal := ZJ.isNormalScheme_sp ℤ, proj := Inhab.isProjOver_id ℤ
            flat := inferInstance, jQ := j, jQ_over := (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (IsIso.inv_hom_id _)).trans (Category.comp_id _))
            jQ_open := inferInstance
            jQ_dense := hs.denseRange, t := Inhab.zeroTriple H _, oF := zeroObj hD l _
            m0 := (nonempty_objMap (isIso_zeroTriple _) h₂ _).some
            m := (nonempty_sabMap (isIso_zeroTriple _) (isIso_zeroTriple _) _).some
            ab_gen := by
              rw [hs.range_eq, Inhab.abLocus_eq_univ _ (Inhab.isProper_zeroTriple _), Set.preimage_univ] }, ?_⟩
  exact PushInv.pushInvertible_any GlobalTheory.allSixLaws.2.1.secBaseChangeAny GlobalTheory.allSixLaws.1.globalSectionsRank _
    (Out.Inh.zeroPolAV (Sp ℤ))

theorem intFrExt_of_rank_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), Dw.p + Dw.q = 0 → IntFrExt Xo c := by
  intro E _ _ _ H Dw l Xo c hD T io hfin x hx
  have hL := GlobalTheory.lawsFieldsSeparately
  have hB : Out.SecBaseChangeSt := hL.2.1
  have hT : Out.SecTwistSt := hL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨Y, hPI⟩ := exists_model_int hD Xo c
  have hIF := GlobalTheory.intFrames_of_laws hB hT E H Dw l Xo c
  let _ := io.toAlgebra
  obtain ⟨y₀, -, h0, -, -⟩ := gfp_frPt_gen (Xo := Xo) (c := c) (L := T.Fr) (L' := T.Fr) hT (fun _ => rfl) x hx
    (fun _ i j => if i = j then 1 else 0) (fun _ _ => if_pos rfl) (fun _ _ _ h => if_neg h.ne')
  obtain ⟨y, t, hbor⟩ := intFr_of_model hIF T io Y hPI (Int.castRingHom T.V) (RingHom.ext_int _ _) y₀
  refine ⟨T, RingHom.id _, 1, one_pos, fun z => by simp, hfin, y, ?_⟩
  have h1 : y.1.x = y₀.x := hbor.1
  have h2 : spMap (RingHom.id T.Fr) = 𝟙 _ := Spec.map_id _
  show y.1.x = _
  rw [h2, Category.id_comp, h1, h0]

end GlobalTheory.RankZeroFrames
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralFrameExtensionOfRankZeroSignatureStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralFrameExtension_of_rank_zero_signature : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), Dw.p + Dw.q = 0 → IntFrExt Xo c := by
  first | exact @GlobalTheory.RankZeroFrames.intFrExt_of_rank_zero | exact GlobalTheory.RankZeroFrames.intFrExt_of_rank_zero | (intros; apply GlobalTheory.RankZeroFrames.intFrExt_of_rank_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalStableOrbitalIntegralsWellDefined
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalStableOrbitalIntegralsWellDefined
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section
namespace GlobalTheory.TrPhiOK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {r n : ℕ}
  {P : PPol σ r} {J : Matrix (Fin n) (Fin n) E}

theorem phiOK_of (hσ : IsCMExt F E σ) (hJ : IsHermND σ J) (k : Type) [Field k] [Algebra F k] [TopologicalSpace k]
    [IsTopologicalRing k] [T2Space k] [LocallyCompactSpace (HA k σ J)] [SecondCountableTopology (HA k σ J)]
    [T2Space (HA k σ J)] (hfin : Finite (Cls P k))
    (hU : ∀ μ : Measure (HA k σ J), μ.IsHaarMeasure → μ.IsMulRightInvariant)
    (hpr : ∀ g : HA k σ J, IsRegSS (matHom k σ J g).1 → IsProperOrbit (cent g) g)
    (μ : Measure (HA k σ J)) (dt : Measure (Tor P k)) (f : HA k σ J → ℂ) [hμ : μ.IsHaarMeasure]
    [hdt : dt.IsHaarMeasure] (hf : Continuous f) (hc : HasCompactSupport f) : PhiOK (J := J) μ dt f := by
  refine ⟨Set.toFinite _, fun x φ h => ?_⟩
  haveI := hU μ hμ
  set q : XSet P k J := ⟨QuotientGroup.mk x, x, φ, rfl, h⟩ with hq
  obtain ⟨hx0, h0⟩ := q.2.choose_spec.choose_spec
  set x0 := q.2.choose
  set φ0 := q.2.choose_spec.choose
  change HasOrbInt μ (gam h) (centMeas h dt) f (orbInt μ (gam h0) (centMeas h0 dt) f)

  have halg0 := GlobalTheory.T.torusElement_charpoly_regular_centralizer F E σ hσ r n P J hJ k x0 φ0 h0
  obtain ⟨e0, he0, hm0⟩ := GlobalTheory.T.unitaryTorus_equiv_centralizer_with_measure F E σ hσ r n P J hJ k x0 φ0 h0
  obtain ⟨e, he, hm⟩ := GlobalTheory.T.unitaryTorus_equiv_centralizer_with_measure F E σ hσ r n P J hJ k x φ h
  haveI : (centMeas h0 dt).IsHaarMeasure := by rw [hm0]; exact e0.isHaarMeasure_map dt
  haveI : (centMeas h0 dt).IsMulRightInvariant :=
    isMulRightInvariant_cent (isMulCommutative_cent_HA halg0.2.1) _
  have H0 : HasOrbInt μ (gam h0) (centMeas h0 dt) f (orbInt μ (gam h0) (centMeas h0 dt) f) :=
    (hpr _ halg0.2.1).hasOrbInt hf hc

  obtain ⟨g, hg⟩ := (GlobalTheory.T.normClasses_iff_conj_unitaryTorusEllipticElements F E σ hσ r n P J hJ k x0 φ0 h0 x φ h).1 (by rw [hx0])
  have hgam : g * gam h0 * g⁻¹ = gam h := (hg _).symm
  have hmeas : centMeas h dt = (centMeas h0 dt).map (centEquiv (conjEquiv g) (gam h0) hgam) := by
    rw [hm, hm0, Measure.map_map (map_continuous _).measurable (map_continuous _).measurable]
    congr 1
    funext t
    apply Subtype.ext
    change (e t).1 = g * (e0 t).1 * g⁻¹
    rw [he, he0, hg]
  rw [hmeas]
  exact ((hasOrbInt_conj (dh := μ) (dt := centMeas h0 dt) g hgam f _).1).2 H0

end GlobalTheory.TrPhiOK


open GlobalTheory.TrPhiOK in
theorem GlobalTheory.TrPhiOK.phiOK_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r n : ℕ) (P : PPol σ r) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → (∀ (v : HeightOneSpectrum (𝓞 F)) (μ : Measure (GLoc σ J v)) (dt : Measure (Tor P (Fv F v))) (f : GLoc σ J v → ℂ), μ.IsHaarMeasure → dt.IsHaarMeasure → Continuous f → HasCompactSupport f → PhiOK (J := J) μ dt f) ∧ ∀ (w : InfinitePlace F) (μ : Measure (GArch σ J w)) (dt : Measure (Tor P w.Completion)) (f : GArch σ J w → ℂ), μ.IsHaarMeasure → dt.IsHaarMeasure → Continuous f → HasCompactSupport f → PhiOK (J := J) μ dt f := by
  intro F E _ _ _ _ _ σ hσ r n P J hJ
  have hfin := GlobalTheory.T.finite_unitaryTorusNormClasses_at_all_places F E σ hσ r P
  refine ⟨fun v μ dt f hμ hdt hf hc => ?_, fun w μ dt f hμ hdt hf hc => ?_⟩
  · have hU := (GlobalTheory.LocalUnitaryUnimod.unimodularOver_adicCompletion F E σ hσ n J hJ v).1
    exact phiOK_of hσ hJ (Fv F v) (hfin.1 v) hU.2.2.2.2.2.2 (fun g hg => isProperOrbit_GLoc hσ hJ hg) μ dt f hf hc
  · haveI : SecondCountableTopology w.Completion :=
      (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
    have hU := (GlobalTheory.ArchUnitaryUnimod.unimodularOver_of_artinian (σ := σ) w.Completion hσ hJ).1
    exact phiOK_of hσ hJ w.Completion (hfin.2 w) hU.2.2.2.2.2.2 (fun g hg => isProperOrbit_GArch hσ hJ hg) μ dt f hf hc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalStableOrbitalIntegralsWellDefinedStatement
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_stable_orbital_integrals_well_defined : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r n : ℕ) (P : PPol σ r) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → (∀ (v : HeightOneSpectrum (𝓞 F)) (μ : Measure (GLoc σ J v)) (dt : Measure (Tor P (Fv F v))) (f : GLoc σ J v → ℂ), μ.IsHaarMeasure → dt.IsHaarMeasure → Continuous f → HasCompactSupport f → PhiOK (J := J) μ dt f) ∧ ∀ (w : InfinitePlace F) (μ : Measure (GArch σ J w)) (dt : Measure (Tor P w.Completion)) (f : GArch σ J w → ℂ), μ.IsHaarMeasure → dt.IsHaarMeasure → Continuous f → HasCompactSupport f → PhiOK (J := J) μ dt f := by
  first | exact @GlobalTheory.TrPhiOK.phiOK_local | exact GlobalTheory.TrPhiOK.phiOK_local | (intros; apply GlobalTheory.TrPhiOK.phiOK_local <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsRigIsoOfBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsRigIsoOfBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

noncomputable section

namespace GlobalTheory.RigIsoDescent

section General

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A}

theorem exists_isRigIso_of_gen {Y : Scheme.{0}} {x x' : Y ⟶ S} {Ψ : (Over.mk x ⊗ A).left ⟶ (Over.mk x' ⊗ A).left}
    {k : ℤ} (hΨ : IsPointed A Ψ) (t : LB.Gen (isoLB A L Ψ k)) (ht : t.IsGen) : ∃ β, IsRigIso A L Ψ k β := by
  obtain ⟨β, hβ, hc⟩ := DVR.exists_normalized_to L.isLB _ _ t ht (fst (Over.mk x) A).left
    (ptSecT A (1 : Over.mk x ⟶ A)).left ThetaReal.NormMul.ptSec_fst _ _
    (LB.mulGen L.L (Y := Y) _ _ _ _ (rigT A L.L L.rig (Over.mk x) k) (rigT A L.L L.rig (Over.mk x') (-1)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (ThetaReal.NormMul.rigT_isGen L.rigGen _) (ThetaReal.NormMul.rigT_isGen L.rigGen _))
    (by
      rw [DVR.fsum_sumElim, DVR.fsum, DVR.fsum, DVR.fsum, Fin.sum_univ_two, Fin.sum_univ_one, Fin.sum_univ_one]
      refine congrArg₂ (· + ·) (congrArg (Finsupp.single · k) ThetaReal.NormMul.ptSec_snd)
        (congrArg (Finsupp.single · (-1 : ℤ)) ?_)
      refine (Category.assoc _ _ _).symm.trans ?_
      rw [hΨ.2]
      exact ThetaReal.NormMul.ptSec_snd)
  exact ⟨β, hΨ, hβ, hc⟩

theorem exists_gen_of_field (hA : IsAbelianScheme A) {K K' : Type} [Field K] [Field K'] (φ : K →+* K')
    {x x' : Sp K ⟶ S} {w w' : Sp K' ⟶ S} {Ψ : (Over.mk x ⊗ A).left ⟶ (Over.mk x' ⊗ A).left}
    {Ψ' : (Over.mk w ⊗ A).left ⟶ (Over.mk w' ⊗ A).left} {k : ℤ} (hw : w = spMap φ ≫ x)
    (π : (Over.mk w ⊗ A).left ⟶ (Over.mk x ⊗ A).left)
    (h₁ : π ≫ (fst (Over.mk x) A).left = (fst (Over.mk w) A).left ≫ spMap φ)
    (h₂ : π ≫ (snd (Over.mk x) A).left = (snd (Over.mk w) A).left)
    (h₃ : π ≫ Ψ ≫ (snd (Over.mk x') A).left = Ψ' ≫ (snd (Over.mk w') A).left)
    (t : LB.Gen (isoLB A L Ψ' k)) (ht : t.IsGen) : ∃ u : LB.Gen (isoLB A L Ψ k), u.IsGen := by
  have := hA.proper
  have := forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ A.hom hA.smooth hA.geomConnected
  let p : (Over.mk x ⊗ A).left ⟶ Sp K := (fst (Over.mk x) A).left
  have H₀ : IsPullback (snd (Over.mk x) A).left p A.hom x := (IsPullback.of_hasPullback x A.hom).flip
  have H₁ : IsPullback (snd (Over.mk w) A).left (fst (Over.mk w) A).left A.hom w :=
    (IsPullback.of_hasPullback w A.hom).flip
  have : IsProper p := MorphismProperty.of_isPullback (P := @IsProper) H₀ inferInstance
  have : GeometricallyIntegral p := MorphismProperty.of_isPullback (P := @GeometricallyIntegral) H₀ inferInstance
  have H : IsPullback π (fst (Over.mk w) A).left p (spMap φ) :=
    IsPullback.of_right (by rw [h₂, ← hw]; exact H₁) h₁ H₀
  obtain ⟨c, hc⟩ := gen_chartPull (chartPullOut L.L (isoφ A Ψ) ![k, -1] π (isoφ A Ψ') fun i => by
    fin_cases i
    exacts [h₂.symm, h₃.symm]) t ht
  exact FieldTriv.exists_gen_of_isPullback φ p π _ H (LB.isLB_linComb L.isLB _ _) c hc

end General

theorem eSec_fst {B B' : Scheme.{0}} (u : B' ⟶ B) (A : Over B) [GrpObj A] :
    eSec ((Over.pullback u).obj A) ≫ pullback.fst A.hom u = u ≫ eSec A := by
  rw [eSec, eSec, Functor.obj.η_def, Over.comp_left, Over.ε_pullback_left, Category.assoc, IsIso.inv_comp_eq,
    ← pullback.condition_assoc]
  exact (pullback.lift_fst _ _ _).trans (by simp)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}

theorem ptSec_swap {K : Type} [CommRing K] (x : Sp K ⟶ Xo.X) :
    (ptSecT Xo.univ.t.G (1 : Over.mk x ⟶ Xo.univ.t.G)).left ≫ (swap x).hom = eSec (Fib Xo x) := by
  refine pullback.hom_ext ?_ ?_
  · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (swap_hom_fst x)).trans
      (ThetaReal.NormMul.ptSec_snd.trans (eSec_fst x _).symm))
  · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (swap_hom_snd x)).trans
      (ThetaReal.NormMul.ptSec_fst.trans (Over.w η[Fib Xo x]).symm))

theorem isPointed_of_isMonHom {K : Type} [CommRing K] {x x' : Sp K ⟶ Xo.X} (f : Fib Xo x ⟶ Fib Xo x')
    (hf : IsMonHom f) : IsPointed Xo.univ.t.G (conj x x' f.left) := by
  refine ⟨(over_iff _).2 (Over.w f), ?_⟩
  have e : eSec (Fib Xo x) ≫ f.left = eSec (Fib Xo x') := congrArg (fun q => q.left) hf.one_hom
  refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (ptSec_swap x)).trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e).trans ?_)))
  exact (Iso.comp_inv_eq _).2 (ptSec_swap x').symm

theorem exists_isRigIso_of_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K L : Type) [Field K] [Field L] (φ : K →+* L) (x x' : Sp K ⟶ Xo.X) (w w' : Sp L ⟶ Xo.X) (f : Fib Xo x ⟶ Fib Xo x') (g : Fib Xo w ⟶ Fib Xo w') (k : ℤ), IsBC φ f g → IsMonHom f → (∃ β, IsRigIso Xo.univ.t.G Xo.univ.t.PP (conj w w' g.left) k β) → ∃ β, IsRigIso Xo.univ.t.G Xo.univ.t.PP (conj x x' f.left) k β := by
  rintro E _ _ _ H Dw l Xo K L _ _ φ x x' w w' f g k ⟨hw, hw', hbc⟩ hf ⟨β, -, hβ, -⟩
  have mk : ∀ {y : Sp K ⟶ Xo.X} {v : Sp L ⟶ Xo.X}, v = spMap φ ≫ y →
      ∃ π : pullback Xo.univ.t.G.hom v ⟶ pullback Xo.univ.t.G.hom y,
        π ≫ pullback.fst _ _ = pullback.fst _ _ ∧ π ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap φ := fun h =>
    ⟨pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ spMap φ) (by rw [Category.assoc, ← h, pullback.condition]),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  obtain ⟨π, a₁, a₂⟩ := mk hw
  obtain ⟨π', b₁, b₂⟩ := mk hw'
  have e := hbc π π' a₁ a₂ b₁ b₂
  have hp := isPointed_of_isMonHom f hf
  obtain ⟨u, hu⟩ := exists_gen_of_field (L := Xo.univ.t.PP) (Ψ := conj x x' f.left) (UnivPol.pol Xo).isAb φ hw
    ((swap w).hom ≫ π ≫ (swap x).inv)
    (by rw [Category.assoc, Category.assoc, swap_inv_fst, a₂, swap_hom_snd_assoc])
    (by rw [Category.assoc, Category.assoc, swap_inv_snd, a₁, swap_hom_fst])
    (by
      simp only [conj_apply, Category.assoc, Iso.inv_hom_id_assoc, swap_inv_snd]
      rw [← reassoc_of% e, b₁]) β hβ
  exact exists_isRigIso_of_gen hp u hu

end GlobalTheory.RigIsoDescent
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsRigIsoOfBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isRigIso_of_baseChange' : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K L : Type) [Field K] [Field L] (φ : K →+* L) (x x' : Sp K ⟶ Xo.X) (w w' : Sp L ⟶ Xo.X) (f : Fib Xo x ⟶ Fib Xo x') (g : Fib Xo w ⟶ Fib Xo w') (k : ℤ), IsBC φ f g → IsMonHom f → (∃ β, IsRigIso Xo.univ.t.G Xo.univ.t.PP (conj w w' g.left) k β) → ∃ β, IsRigIso Xo.univ.t.G Xo.univ.t.PP (conj x x' f.left) k β := by
  first | exact @GlobalTheory.RigIsoDescent.exists_isRigIso_of_baseChange | exact GlobalTheory.RigIsoDescent.exists_isRigIso_of_baseChange | (intros; apply GlobalTheory.RigIsoDescent.exists_isRigIso_of_baseChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesTestDataLargeGapsIntegrable
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesTestDataLargeGapsIntegrable
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DSGapData

theorem two_mul_rkR_le {n : ℕ} (ε : Fin n → Bool) : 2 * GlobalTheory.Count.rkR ε ≤ n := by
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n))) (fun a => ε a = true)
  simp only [Bool.not_eq_true, Finset.card_univ, Fintype.card_fin] at h
  delta GlobalTheory.Count.rkR
  omega

theorem rank_bound (n q : ℕ) (hq : 2 * q ≤ n) :
    120 * (n : ℝ) * ((q : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ 100 * (n : ℝ) ^ 4 := by
  rcases Nat.eq_zero_or_pos q with h0 | h0
  · subst h0
    rw [Nat.cast_zero, Real.zero_rpow (by norm_num), mul_zero]
    positivity
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast h0
  have hq2 : (2 : ℝ) * q ≤ n := by exact_mod_cast hq
  have hn : (2 : ℝ) ≤ n := by linarith
  have e : ((q : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ (q : ℝ) ^ 2 := by
    have := Real.rpow_le_rpow_of_exponent_le hq1 (show (3 : ℝ) / 2 ≤ 2 by norm_num)
    simpa using this
  have h1 : 4 * (q : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by nlinarith
  have h2 : 120 * (n : ℝ) * ((q : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ 120 * (n : ℝ) * (q : ℝ) ^ 2 := by
    have : (0 : ℝ) ≤ 120 * n := by positivity
    exact mul_le_mul_of_nonneg_left e this
  have h3 : 120 * (n : ℝ) * (q : ℝ) ^ 2 ≤ 30 * (n : ℝ) ^ 3 := by nlinarith
  have h4 : 30 * (n : ℝ) ^ 3 ≤ 100 * (n : ℝ) ^ 4 := by nlinarith [pow_nonneg (show (0 : ℝ) ≤ n by linarith) 3]
  linarith

theorem big_bound (n q : ℕ) (hq : 2 * q ≤ n) :
    40 * (n : ℝ) ^ 2 * Real.sqrt q ≤ 100 * (n : ℝ) ^ 4 := by
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0
    have : q = 0 := by omega
    subst this; simp
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast h0
  have hqn : (q : ℝ) ≤ (n : ℝ) ^ 2 := by
    have : q ≤ n ^ 2 := by nlinarith
    exact_mod_cast this
  have hs : Real.sqrt q ≤ n := Real.sqrt_le_iff.2 ⟨by positivity, hqn⟩
  have h1 : 40 * (n : ℝ) ^ 2 * Real.sqrt q ≤ 40 * (n : ℝ) ^ 2 * n :=
    mul_le_mul_of_nonneg_left hs (by positivity)
  have h2 : 40 * (n : ℝ) ^ 2 * n ≤ 100 * (n : ℝ) ^ 4 := by nlinarith [pow_nonneg (show (0 : ℝ) ≤ n by linarith) 3]
  linarith

theorem gap_numeric' {n : ℕ} (ε : Fin n → Bool) (h : ℝ)
    (hh : 120 * (n : ℝ) * ((GlobalTheory.Count.rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) :
    GlobalTheory.Count.rkR ε = 0 ∨ 8 * Real.sqrt (GlobalTheory.Count.rkR ε) * (0 + 4 * n * GlobalTheory.Count.rkR ε) < h := by
  rcases Nat.eq_zero_or_pos (GlobalTheory.Count.rkR ε) with h0 | h0
  · exact Or.inl h0
  right
  have hq : (0 : ℝ) < GlobalTheory.Count.rkR ε := by exact_mod_cast h0
  have hn : (0 : ℝ) < n := by
    have := two_mul_rkR_le ε
    exact_mod_cast (show 0 < n by omega)
  have e : ((GlobalTheory.Count.rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) = Real.sqrt (GlobalTheory.Count.rkR ε) * GlobalTheory.Count.rkR ε := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add_one hq.ne']
    norm_num
  rw [e] at hh
  have hp : 0 < (n : ℝ) * (Real.sqrt (GlobalTheory.Count.rkR ε) * GlobalTheory.Count.rkR ε) := by positivity
  nlinarith

theorem lamAt_gap {D : D7} (hH : HostHyp D) (τ : D.what₂.Tau) (i : ℕ) :
    ∀ j, i < j → j < D.R.r →
      100 * (D.R.r : ℚ) ^ 4 ≤ Formalism.L2.NTheta.lamAt (D.hc τ) i - Formalism.L2.NTheta.lamAt (D.hc τ) j := by
  intro j
  induction j with
  | zero => intro h; omega
  | succ j ih =>
    intro hij hj
    have g := hH.gapR τ j hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | h
    · have := ih h (by omega)
      have h0 : (0 : ℚ) ≤ 100 * (D.R.r : ℚ) ^ 4 := by positivity
      linarith
    · subst h; exact g

theorem isHCParam_cast {n m : ℕ} (h : n = m) (lam : Fin m → ℝ) (hl : Formalism.QuantumDeterminants.IsHCParam lam) :
    Formalism.QuantumDeterminants.IsHCParam (fun i : Fin n => lam (Fin.cast h i)) := by
  subst h; simpa using hl

theorem dsData_gap_integrable : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D), HostHyp D → GlobalTheory.Count.IsDSData X.B X.dv ∧ GlobalTheory.Dec.LocDec X.B (100 * (D.R.r : ℝ) ^ 4) ∧ GlobalTheory.Dec.HBig X.B 40 (100 * (D.R.r : ℝ) ^ 4) ∧ (∀ v, 120 * (X.B.I.n : ℝ) * ((GlobalTheory.Count.rkR (X.B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ 100 * (D.R.r : ℝ) ^ 4) ∧ Integrable X.ph (Formalism.L2.SG.ProjRows.muInf X.B.I) ∧ ∀ v, Integrable (Formalism.L2.SG.ProjRows.phLoc (ε := X.B.I.ε v) (X.B.σ v) (X.B.w v) (X.dv v)) (Formalism.REAL.muG (X.B.I.ε v)) := by
  intro D X hH
  have hn : (X.B.I.n : ℝ) = (D.R.r : ℝ) := by exact_mod_cast X.n_eq

  have hds : GlobalTheory.Count.IsDSData X.B X.dv := by
    intro v
    have e : X.B.lam v = fun i => Formalism.MainNotions.S.lamS D.R (D.hc (X.pl v)) (Fin.cast X.n_eq i) := funext (X.lam_eq v)
    refine ⟨?_, X.ds v, X.low v, ?_⟩
    · rw [e]
      exact isHCParam_cast X.n_eq _ (Formalism.MainNotions.S.Inh.aut_isHCParam_lamS D.R (D.hc (X.pl v)))
    · obtain ⟨d, hd⟩ := GlobalTheory.Mem.Vol.exists_isFdeg_smul_of_isDS _ _ _ _ _ (X.ds v) 1 one_pos
      rw [ENNReal.coe_one, one_smul] at hd
      have hw : X.B.w v ≠ 0 := by
        intro h0
        have h1 := (X.low v).1
        rw [h0, norm_zero] at h1
        exact zero_ne_one h1
      have e2 : X.dv v = d := Formalism.L2.SG.Pf.RowDictPf.fdegOf_eq hd hw
      rw [e2]
      exact hd

  have hgap : GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) := by
    intro v a b hab
    have hne : (a : ℕ) ≠ (b : ℕ) := fun h => hab (by rw [Fin.ext h])
    have hlam (i : Fin X.B.I.n) :
        X.B.lam v i = (Formalism.L2.NTheta.lamAt (D.hc (X.pl v)) i : ℝ) := by
      rw [X.lam_eq]
      delta Formalism.MainNotions.S.lamS Formalism.L2.NTheta.lamAt
      simp only [Fin.val_cast]
      split_ifs <;> simp
    rw [hlam a, hlam b]
    rcases lt_or_gt_of_ne hne with h | h
    · have g := lamAt_gap hH (X.pl v) a b h (by have := b.2; have := X.n_eq; omega)
      have g' : (100 * (D.R.r : ℝ) ^ 4) ≤ ((Formalism.L2.NTheta.lamAt (D.hc (X.pl v)) a : ℚ) : ℝ) -
          ((Formalism.L2.NTheta.lamAt (D.hc (X.pl v)) b : ℚ) : ℝ) := by exact_mod_cast g
      exact le_abs.2 (Or.inl g')
    · have g := lamAt_gap hH (X.pl v) b a h (by have := a.2; have := X.n_eq; omega)
      have g' : (100 * (D.R.r : ℝ) ^ 4) ≤ ((Formalism.L2.NTheta.lamAt (D.hc (X.pl v)) b : ℚ) : ℝ) -
          ((Formalism.L2.NTheta.lamAt (D.hc (X.pl v)) a : ℚ) : ℝ) := by exact_mod_cast g
      exact le_abs.2 (Or.inr (by linarith))

  have hh : ∀ v, 120 * (X.B.I.n : ℝ) * ((GlobalTheory.Count.rkR (X.B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤
      100 * (D.R.r : ℝ) ^ 4 := by
    intro v
    rw [← hn]
    exact rank_bound _ _ (two_mul_rkR_le _)
  have hbig : GlobalTheory.Dec.HBig X.B 40 (100 * (D.R.r : ℝ) ^ 4) := by
    intro v
    rw [← hn]
    exact big_bound _ _ (two_mul_rkR_le _)

  have hD := GlobalTheory.DecGapBound.decGap_of_formulaGap GlobalTheory.Jet.FormGapFree.formulaGap
  have hloc : GlobalTheory.Dec.LocDec X.B (100 * (D.R.r : ℝ) ^ 4) :=
    GlobalTheory.Dec.locDec_of_decGap_gapGe hD X.B X.dv _ hds hgap hh
  obtain ⟨hc, hle, hint⟩ := GlobalTheory.Dec.PhMajProof.phMaj X.B X.dv _ hds hloc
  have hI := hint 0 le_rfl fun v => gap_numeric' _ _ (hh v)
  have hph : Integrable (GlobalTheory.Count.ph X.B X.dv) (GlobalTheory.Dec.muInf X.B.I) := by
    refine hI.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall fun g => ?_)
    simpa using hle g
  have hph' : Integrable X.ph (Formalism.L2.SG.ProjRows.muInf X.B.I) := hph
  exact ⟨hds, hloc, hbig, hh, hph', GlobalTheory.ProdFactor.integrable_phLoc_of_integrable_ph D X hph'⟩

end GlobalTheory.DSGapData
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesTestDataLargeGapsIntegrableStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discreteSeries_testData_large_gaps_integrable : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D), HostHyp D → GlobalTheory.Count.IsDSData X.B X.dv ∧ GlobalTheory.Dec.LocDec X.B (100 * (D.R.r : ℝ) ^ 4) ∧ GlobalTheory.Dec.HBig X.B 40 (100 * (D.R.r : ℝ) ^ 4) ∧ (∀ v, 120 * (X.B.I.n : ℝ) * ((GlobalTheory.Count.rkR (X.B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ 100 * (D.R.r : ℝ) ^ 4) ∧ Integrable X.ph (Formalism.L2.SG.ProjRows.muInf X.B.I) ∧ ∀ v, Integrable (Formalism.L2.SG.ProjRows.phLoc (ε := X.B.I.ε v) (X.B.σ v) (X.B.w v) (X.dv v)) (Formalism.REAL.muG (X.B.I.ε v)) := by
  first | exact @GlobalTheory.DSGapData.dsData_gap_integrable | exact GlobalTheory.DSGapData.dsData_gap_integrable | (intros; apply GlobalTheory.DSGapData.dsData_gap_integrable <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteEtaleAlgebraPullbackAffine
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteEtaleAlgebraPullbackAffine
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

namespace GlobalTheory.HeckeEx

theorem exists_finiteEtale_algebra_pullback : ∀ (X Y : Scheme.{0}) (π : Y ⟶ X), IsFinite π → Etale π → ∀ (R : Type) [CommRing R] (x : Sp R ⟶ X), ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B) (h : Sp B ⟶ Y), Module.Finite R B ∧ Algebra.Etale R B ∧ h ≫ π = spMap (algebraMap R B) ≫ x ∧ (Surjective π → Function.Surjective (PrimeSpectrum.comap (algebraMap R B))) ∧ ∀ (Ω : Type) [CommRing Ω] (φ : R →+* Ω) (w : Sp Ω ⟶ Y), w ≫ π = spMap φ ≫ x → ∃! χ : B →+* Ω, χ.comp (algebraMap R B) = φ ∧ spMap χ ≫ h = w := by
  intro X Y π hfin het R _ x
  haveI : IsAffine (pullback π x) := isAffine_of_isAffineHom (pullback.snd π x)
  obtain ⟨S, e, -⟩ : ∃ (S : CommRingCat.{0}) (_ : Spec S ≅ pullback π x), True :=
    ⟨_, (pullback π x).isoSpec.symm, trivial⟩
  obtain ⟨f, hf⟩ := Spec.map_surjective (R := CommRingCat.of R) (S := S)
    (e.hom ≫ pullback.snd π x)
  letI : Algebra R S := f.hom.toAlgebra
  have hsp : spMap (algebraMap R S) = e.hom ≫ pullback.snd π x := hf
  refine ⟨S, inferInstance, inferInstance, e.hom ≫ pullback.fst π x, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 : IsFinite (Spec.map f) := by rw [hf]; infer_instance
    exact (IsFinite.SpecMap_iff f).1 h1
  · have h1 : Etale (Spec.map f) := by rw [hf]; infer_instance
    exact RingHom.etale_algebraMap.1 ((HasRingHomProperty.Spec_iff (P := @Etale)).1 h1)
  · rw [hsp, Category.assoc, Category.assoc, pullback.condition]
  · intro hs
    have h1 : Surjective (Spec.map f) := by rw [hf]; infer_instance
    exact h1.surj
  · intro Ω _ φ w hw
    obtain ⟨g, hg⟩ := Spec.map_surjective (R := S) (S := CommRingCat.of Ω)
      (pullback.lift w (spMap φ) hw ≫ e.inv)
    have key : ∀ χ : S →+* Ω, χ.comp (algebraMap R S) = φ ↔
        spMap χ ≫ e.hom ≫ pullback.snd π x = spMap φ := by
      intro χ
      rw [← hsp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      constructor
      · intro h; rw [h]
      · intro h
        exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)
    have hg' : spMap g.hom = pullback.lift w (spMap φ) hw ≫ e.inv := hg
    refine ⟨g.hom, ⟨(key _).2 ?_, ?_⟩, ?_⟩
    · rw [hg', Category.assoc, e.inv_hom_id_assoc, pullback.lift_snd]
    · rw [hg', Category.assoc, e.inv_hom_id_assoc, pullback.lift_fst]
    · rintro χ ⟨h1, h2⟩
      have h3 : spMap χ = spMap g.hom := by
        rw [hg', Iso.eq_comp_inv]
        refine pullback.hom_ext ?_ ?_
        · rw [pullback.lift_fst, Category.assoc]; exact h2
        · rw [pullback.lift_snd, Category.assoc]; exact (key _).1 h1
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective h3)

end GlobalTheory.HeckeEx
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteEtaleAlgebraPullbackAffineStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteEtale_algebra_pullback_affine : ∀ (X Y : Scheme.{0}) (π : Y ⟶ X), IsFinite π → Etale π → ∀ (R : Type) [CommRing R] (x : Sp R ⟶ X), ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B) (h : Sp B ⟶ Y), Module.Finite R B ∧ Algebra.Etale R B ∧ h ≫ π = spMap (algebraMap R B) ≫ x ∧ (Surjective π → Function.Surjective (PrimeSpectrum.comap (algebraMap R B))) ∧ ∀ (Ω : Type) [CommRing Ω] (φ : R →+* Ω) (w : Sp Ω ⟶ Y), w ≫ π = spMap φ ≫ x → ∃! χ : B →+* Ω, χ.comp (algebraMap R B) = φ ∧ spMap χ ≫ h = w := by
  first | exact @GlobalTheory.HeckeEx.exists_finiteEtale_algebra_pullback | exact GlobalTheory.HeckeEx.exists_finiteEtale_algebra_pullback | (intros; apply GlobalTheory.HeckeEx.exists_finiteEtale_algebra_pullback <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsVecOfNe
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.KapRedII

section Defs

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem nP_pos' (F : Face D A) (b : Bool) : 0 < RealDat.nP F b := by
  have hcard : 0 < Nat.card (F.lvl b).P := Nat.card_pos
  unfold RealDat.nP
  exact_mod_cast hcard

end Defs

section Schur

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem isMultiplicityInner_smul_measure {M : DSModel V S} {μ : Measure (GA D V)} {𝓕 : Set (GA D V)} {T T' : MMap M} {c : ℂ} {a : ℝ}
    (ha : 0 ≤ a) (h : IsMultIP M μ 𝓕 T T' c) : IsMultIP M (ENNReal.ofReal a • μ) 𝓕 T T' ((a : ℂ) * c) := by
  intro v v'
  obtain ⟨hint, heq⟩ := h v v'
  refine ⟨?_, ?_⟩
  · unfold IntegrableOn
    rw [Measure.restrict_smul]
    exact hint.smul_measure ENNReal.ofReal_ne_top
  · rw [Measure.restrict_smul, integral_smul_measure, heq, ENNReal.toReal_ofReal ha, Complex.real_smul]
    ring

private theorem isMultIP_const_unique {M : DSModel V S} {μ : Measure (GA D V)} {𝓕 : Set (GA D V)} {T T' : MMap M} {c c' : ℂ}
    (v : M.Vec) (hv : ∏ τ, ⟪(v τ : M.H τ), (v τ : M.H τ)⟫_ℂ ≠ 0)
    (h : IsMultIP M μ 𝓕 T T' c) (h' : IsMultIP M μ 𝓕 T T' c') : c = c' := by
  have e := (h v v).2
  rw [(h' v v).2] at e
  exact (mul_right_cancel₀ hv e).symm

private theorem ipM_eq_of_isMultIP {M : DSModel V S} {μ : Measure (GA D V)} {𝓕 : Set (GA D V)} {T T' : MMap M} {c : ℂ}
    (v : M.Vec) (hv : ∏ τ, ⟪(v τ : M.H τ), (v τ : M.H τ)⟫_ℂ ≠ 0) (h : IsMultIP M μ 𝓕 T T' c) :
    ipM M μ 𝓕 T T' = c := by
  have hex : ∃ c, IsMultIP M μ 𝓕 T T' c := ⟨c, h⟩
  unfold ipM
  rw [dite_eq_left hex]
  exact isMultIP_const_unique v hv hex.choose_spec h

theorem ipM_smul_of_vec (M : DSModel V S) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (T T' : MMap M) {a : ℝ}
    (ha : 0 < a) (v : M.Vec) (hv : ∏ τ, ⟪(v τ : M.H τ), (v τ : M.H τ)⟫_ℂ ≠ 0) :
    ipM M (ENNReal.ofReal a • μ) 𝓕 T T' = (a : ℂ) * ipM M μ 𝓕 T T' := by
  by_cases hex : ∃ c, IsMultIP M μ 𝓕 T T' c
  · obtain ⟨c, hc⟩ := hex
    rw [ipM_eq_of_isMultIP v hv hc, ipM_eq_of_isMultIP v hv (isMultiplicityInner_smul_measure ha.le hc)]
  ·
    have hex' : ¬ ∃ c, IsMultIP M (ENNReal.ofReal a • μ) 𝓕 T T' c := by
      rintro ⟨c', hc'⟩
      have hb := isMultiplicityInner_smul_measure (inv_nonneg.mpr ha.le) hc'
      rw [smul_smul, ← ENNReal.ofReal_mul (inv_nonneg.mpr ha.le), inv_mul_cancel₀ ha.ne', ENNReal.ofReal_one,
        one_smul] at hb
      exact hex ⟨_, hb⟩
    unfold ipM
    rw [dite_eq_right hex, dite_eq_right hex', mul_zero]

theorem exists_vec_of_ne {M : DSModel V S} {T : MMap M} (hT : T ≠ 0) :
    ∃ v : M.Vec, ∏ τ, ⟪(v τ : M.H τ), (v τ : M.H τ)⟫_ℂ ≠ 0 := by
  classical

  obtain ⟨v, hv⟩ : ∃ v : M.Vec, T v ≠ 0 := by
    by_contra hno
    push_neg at hno
    exact hT (MultilinearMap.ext fun x => by simp [hno x])
  refine ⟨v, Finset.prod_ne_zero_iff.mpr fun τ _ => ?_⟩
  have hvt : v τ ≠ 0 := fun h0 => hv (T.map_coord_zero τ h0)
  rw [inner_self_ne_zero, ne_eq, Submodule.coe_eq_zero]
  exact hvt

end Schur

end GlobalTheory.KapRedII
end
end
