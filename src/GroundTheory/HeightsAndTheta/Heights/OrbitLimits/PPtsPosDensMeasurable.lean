module

public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChartZeroSet
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLinearNoetherNormalization
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PResAboveCover
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.CovLog

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsPosDensMeasurable
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo

theorem PtsPosDensMeasurable.proof : PtsPosDensMeasurable.Statement := by
  intro K _ ι _ P e Ψ L g hP hΨ hL hg hdeg
  classical
  have hfin := fibreFinite K ι P e Ψ hP hΨ
  obtain ⟨B, γ, hBo, hlift, hcov⟩ := PtsSumMeasurable.exists_lift_family (P := P) (Ψ := Ψ) hfin

  have hd1 : IsDegZeroSmooth (fun _ : (Σ k, ι k) → ℂ => (1 : ℝ)) := ⟨contDiffOn_const, fun _ _ _ => rfl⟩
  have hind := sheetIndep K ι P e Ψ L _ 1 hP hΨ hL (PtsPosDens.isSmoothHerm_ofWeight hd1)
    (PtsPosDens.isSectionOn_ofWeight_one hP hd1)
  rw [PtsPosDens.logNorm_ofWeight_one hd1] at hind
  simp only [one_mul] at hind
  have hsheet : ∀ m, ∀ y ∈ B m, IsSheet P Ψ y (segre (γ m y)) (γ m) := fun m y hy =>
    ⟨rfl, Filter.eventually_of_mem ((hBo m).mem_nhds hy) fun y' hy' => hlift m y' hy'⟩
  have hγc : ∀ m, ContinuousOn (γ m) (B m) := fun m y hy =>
    (hlift m y hy).1.continuousAt.continuousWithinAt
  have hO : ∀ m, Set.MapsTo (γ m) (B m) {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := fun m y hy =>
    (hlift m y hy).2.1.1
  have hseg : Continuous (segre : ((Σ k, ι k) → ℂ) → ((k : K) → ι k) → ℂ) :=
    continuous_pi fun i => continuous_finsetProd _ fun k _ => continuous_apply _
  set σ : ℕ → (Fin e → ℂ) → ((k : K) → ι k) → ℂ := fun m =>
    (B m).piecewise (fun y => segre (γ m y)) 0 with hσdef
  have hσB : ∀ m, ∀ y ∈ B m, σ m y = segre (γ m y) := fun m y hy =>
    Set.piecewise_eq_of_mem _ _ _ hy
  have hσm : ∀ m, Measurable (σ m) := fun m =>
    (hseg.comp_continuousOn (hγc m)).measurable_piecewise continuousOn_const (hBo m).measurableSet

  set γt : ℕ → (Fin e → ℂ) → (Σ k, ι k) → ℂ := fun m => (B m).piecewise (γ m) 0 with hγtdef
  have hγtm : ∀ m, Measurable (γt m) := fun m =>
    (hγc m).measurable_piecewise continuousOn_const (hBo m).measurableSet
  set dens : ℕ → (Fin e → ℂ) → ℝ := fun m y =>
    max (g (γt m y) * maDensity (fun j y' => pot L j (γ m y')) y) 0 with hddef
  have hdm : ∀ m, Measurable (dens m) := fun m =>
    ((hg.comp (hγtm m)).mul (PtsSumMeasurable.measurable_maDensity _)).max measurable_const
  have hdens : ∀ m, ∀ y ∈ B m,
      dens m y = max (g (γ m y) * maDensity (fun j y' => pot L j (γ m y')) y) 0 := by
    intro m y hy
    simp only [hddef, hγtdef, Set.piecewise_eq_of_mem _ _ _ hy]
  set S : ℕ → Set (Fin e → ℂ) := fun m =>
    {y | y ∈ B m ∧ ∀ m' < m, ¬ (y ∈ B m' ∧ σ m' y = σ m y)} with hSdef
  have hSm : ∀ m, MeasurableSet (S m) := by
    intro m
    have : S m = B m ∩ ⋂ m' ∈ Finset.range m, (B m' ∩ {y | σ m' y = σ m y})ᶜ := by
      ext y
      simp [hSdef, not_and_or, imp_iff_not_or]
    rw [this]
    exact (hBo m).measurableSet.inter (Finset.measurableSet_biInter _ fun m' _ =>
      ((hBo m').measurableSet.inter (measurableSet_eq_fun (hσm m') (hσm m))).compl)
  set f : ℕ → (Fin e → ℂ) → ℝ := fun m => (S m).indicator (dens m) with hfdef
  have hfm : ∀ m, Measurable (f m) := fun m => (hdm m).indicator (hSm m)
  have key : AEStronglyMeasurable (ptsPosDens P Ψ (pot L) g) volume := by
    have hpp : ptsPosDens P Ψ (pot L) g =
        fun y => ∑ᶠ w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y, max (sheetDensity P Ψ (pot L) g y w) 0 := rfl
    rw [hpp]
    refine aestronglyMeasurable_of_tendsto_ae atTop (f := fun N y => ∑ m ∈ Finset.range N, f m y)
      (fun N => (Finset.measurable_sum _ fun m _ => hfm m).aestronglyMeasurable) ?_
    filter_upwards [hind] with y hy
    have hterm : ∀ m, y ∈ S m → f m y = max (sheetDensity P Ψ (pot L) g y (σ m y)) 0 := by
      intro m hm
      have hsh := hsheet m y hm.1
      rw [← hσB m y hm.1] at hsh
      have hex : ∃ γ', IsSheet P Ψ y (σ m y) γ' := ⟨_, hsh⟩
      rw [hfdef]
      simp only
      rw [Set.indicator_of_mem hm, hdens m y hm.1]
      unfold sheetDensity
      rw [dite_eq_left hex, hy _ _ _ hex.choose_spec hsh]

      choose i0 hi0 using hO m hm.1
      have hs : segre (γ m y) = segre (hex.choose y) := by
        rw [hex.choose_spec.1, hσB m y hm.1]
      obtain ⟨hc', hrel⟩ := eq_bsmul_of_segre_eq i0 hi0 hs
      have hgy : g (hex.choose y) = g (γ m y) := by
        rw [hrel]
        exact hdeg _ _ fun k => div_ne_zero (hc' k) (hi0 k)
      rw [hgy]
    have hmemF : ∀ m, y ∈ S m → σ m y ∈ (hfin y).toFinset := by
      intro m hm
      rw [Set.Finite.mem_toFinset, hσB m y hm.1]
      exact ⟨γ m y, (hlift m y hm.1).2.1, rfl, (hlift m y hm.1).2.2⟩
    have hfy : ∀ m, (∑ w ∈ (hfin y).toFinset, if σ m y = w then f m y else 0) = f m y := by
      intro m
      rw [Finset.sum_ite_eq]
      by_cases hm : y ∈ S m
      · rw [if_pos (hmemF m hm)]
      · split_ifs
        · rfl
        · rw [hfdef]
          simp only
          rw [Set.indicator_of_notMem hm]
    have hev : ∀ w ∈ (hfin y).toFinset, ∀ᶠ N in atTop,
        max (sheetDensity P Ψ (pot L) g y w) 0 =
          ∑ m ∈ Finset.range N, if σ m y = w then f m y else 0 := by
      intro w _
      by_cases hex : ∃ γ', IsSheet P Ψ y w γ'
      · obtain ⟨γ', hγ'⟩ := hex
        have hP' : ∃ m, y ∈ B m ∧ σ m y = w := by
          obtain ⟨m, hm, hmw⟩ := hcov y w γ' hγ'
          exact ⟨m, hm, (hσB m y hm).trans hmw⟩
        obtain ⟨hm1B, hm1w⟩ := Nat.find_spec hP'
        have hm1S : y ∈ S (Nat.find hP') :=
          ⟨hm1B, fun m' hm' h => Nat.find_min hP' hm' ⟨h.1, h.2.trans hm1w⟩⟩
        filter_upwards [eventually_gt_atTop (Nat.find hP')] with N hN
        rw [Finset.sum_eq_single_of_mem (Nat.find hP') (Finset.mem_range.2 hN), if_pos hm1w,
          hterm _ hm1S, hm1w]
        intro m _ hne
        split_ifs with hmw
        · by_cases hmS : y ∈ S m
          · exfalso
            have hle : Nat.find hP' ≤ m := Nat.find_min' hP' ⟨hmS.1, hmw⟩
            exact hmS.2 _ (lt_of_le_of_ne hle (Ne.symm hne)) ⟨hm1B, hm1w.trans hmw.symm⟩
          · rw [hfdef]
            simp only
            rw [Set.indicator_of_notMem hmS]
        · rfl
      · have h0 : sheetDensity P Ψ (pot L) g y w = 0 := by
          unfold sheetDensity
          rw [dite_eq_right hex]
        refine Eventually.of_forall fun N => ?_
        rw [h0, max_self]
        refine (Finset.sum_eq_zero fun m _ => ?_).symm
        split_ifs with hmw
        · by_cases hmS : y ∈ S m
          · have hsh := hsheet m y hmS.1
            rw [← hσB m y hmS.1, hmw] at hsh
            exact absurd ⟨_, hsh⟩ hex
          · rw [hfdef]
            simp only
            rw [Set.indicator_of_notMem hmS]
        · rfl
    have hsum : ∑ᶠ w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y, max (sheetDensity P Ψ (pot L) g y w) 0 =
        ∑ w ∈ (hfin y).toFinset, max (sheetDensity P Ψ (pot L) g y w) 0 :=
      finsum_mem_eq_finite_toFinset_sum _ (hfin y)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [(eventually_all_finset _).2 hev] with N hN
    rw [hsum, Finset.sum_congr rfl hN, Finset.sum_comm]
    exact Finset.sum_congr rfl fun m _ => hfy m
  exact key.aemeasurable

end GroundTheory.Heights₂.Heights
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PVarIntGraph
section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StVarIntGraphInt
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory
open GroundTheory.Heights₂.Heights (varInt SmoothNear chartAbsDens)
open GroundTheory.Heights₂.Heights.ComplexSets (zeroSet IsFiniteProjection)

def VarIntGraphInt.Statement : Prop :=
  ∀ (n e : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : MvPolynomial (Fin n) ℂ) (F : (Fin (n + 1) → ℂ) → ℝ)
    (Φ : Fin e → (Fin (n + 1) → ℂ) → ℝ),
    J.IsPrime → SmoothNear (zeroSet (graphIdeal J p)) F → (∀ k, SmoothNear (zeroSet (graphIdeal J p)) (Φ k)) →
    (∀ B : Matrix (Fin e) (Fin (n + 1)) ℂ, IsFiniteProjection (graphIdeal J p) B →
      Integrable (chartAbsDens (graphIdeal J p) B F Φ)) →
      varInt (graphIdeal J p) e F Φ = varInt J e (fun x => F (graphPt p x)) (fun k x => Φ k (graphPt p x))

end GroundTheory.Heights₂.Heights.Targets
end
end

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory Matrix Filter Topology
open GroundTheory.Heights₂.Heights (varInt SmoothNear chartInt chartDens chartAbsDens sheetSum IsSheetAt)
open GroundTheory.Heights₂.Heights.ComplexSets (zeroSet fibre IsFiniteProjection projHom pullback linPoly)

namespace VarIntGraph

variable {n e : ℕ}

def graphProj (A : Matrix (Fin e) (Fin n) ℂ) : Matrix (Fin e) (Fin (n + 1)) ℂ :=
  Matrix.of fun i => Fin.snoc (α := fun _ => ℂ) (A i) 0

theorem graphProj_mulVec (A : Matrix (Fin e) (Fin n) ℂ) (z : Fin (n + 1) → ℂ) :
    graphProj A *ᵥ z = A *ᵥ Fin.init z := by
  funext i
  simp [graphProj, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, Fin.init]

theorem graphProj_mulVec_graphPt (A : Matrix (Fin e) (Fin n) ℂ) (p : MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ) :
    graphProj A *ᵥ graphPt p x = A *ᵥ x := by
  rw [graphProj_mulVec, graphPt_init]

theorem graphPt_injective (p : MvPolynomial (Fin n) ℂ) : Function.Injective (graphPt p) := fun x x' h => by
  rw [← graphPt_init p x, ← graphPt_init p x', h]

theorem differentiable_eval (p : MvPolynomial (Fin n) ℂ) : Differentiable ℂ fun x : Fin n → ℂ => eval x p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    simp only [map_add (f := _)]
    exact hp.add hq
  | mul_X p i hp =>
    simp only [map_mul, eval_X]
    exact hp.mul (differentiable_apply i)

theorem differentiable_graphPt (p : MvPolynomial (Fin n) ℂ) : Differentiable ℂ (graphPt p) := by
  refine differentiable_pi.2 fun i => ?_
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa [graphPt] using differentiable_eval p
  · simpa [graphPt] using differentiable_apply (𝕜 := ℂ) j

theorem differentiable_init : Differentiable ℂ fun z : Fin (n + 1) → ℂ => Fin.init z :=
  differentiable_pi.2 fun i => differentiable_apply (Fin.castSucc i)

theorem graphHom_comp_pullback (A : Matrix (Fin e) (Fin n) ℂ) (p : MvPolynomial (Fin n) ℂ) :
    (graphHom p).comp (pullback (graphProj A)) = pullback A := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [pullback, linPoly, graphProj, Fin.sum_univ_castSucc, graphHom_X_castSucc, MvPolynomial.algebraMap_eq]

theorem exists_quotEquiv (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : MvPolynomial (Fin n) ℂ) :
    ∃ φ : (MvPolynomial (Fin (n + 1)) ℂ ⧸ graphIdeal J p) ≃+* (MvPolynomial (Fin n) ℂ ⧸ J),
      ∀ q, φ (Ideal.Quotient.mk _ q) = Ideal.Quotient.mk J (graphHom p q) := by
  let g : MvPolynomial (Fin (n + 1)) ℂ →+* MvPolynomial (Fin n) ℂ ⧸ J :=
    (Ideal.Quotient.mk J).comp (graphHom p).toRingHom
  have hg : Function.Surjective g := Ideal.Quotient.mk_surjective.comp (graphHom_surjective p)
  have hker : RingHom.ker g = graphIdeal J p := by
    rw [← RingHom.comap_ker, Ideal.mk_ker]
    rfl
  exact ⟨(Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hg), fun q => rfl⟩

theorem isFiniteProjection_graphProj {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin e) (Fin n) ℂ}
    (p : MvPolynomial (Fin n) ℂ) (hA : IsFiniteProjection J A) :
    IsFiniteProjection (graphIdeal J p) (graphProj A) := by
  obtain ⟨φ, hφ⟩ := exists_quotEquiv J p
  have hcomp : ∀ q, φ (projHom (graphIdeal J p) (graphProj A) q) = projHom J A q := by
    intro q
    simp only [projHom, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, hφ]
    rw [← AlgHom.comp_apply, graphHom_comp_pullback]
  have heq : (projHom (graphIdeal J p) (graphProj A)).toRingHom =
      (φ.symm : (MvPolynomial (Fin n) ℂ ⧸ J) →+* _).comp (projHom J A).toRingHom :=
    RingHom.ext fun q => by simp [← hcomp]
  refine ⟨fun a b h => hA.injective (by rw [← hcomp, ← hcomp, h]), ?_⟩
  rw [heq]
  exact (RingHom.Finite.of_surjective _ φ.symm.surjective).comp hA.finite

theorem fibre_graphProj (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin e) (Fin n) ℂ)
    (p : MvPolynomial (Fin n) ℂ) (y : Fin e → ℂ) :
    ComplexSets.fibre (graphIdeal J p) (graphProj A) y = graphPt p '' ComplexSets.fibre J A y := by
  ext z
  constructor
  · rintro ⟨hz, hzy⟩
    refine ⟨Fin.init z, ⟨init_mem_zeroSet p hz, ?_⟩, graphPt_init_of_mem_zeroSet p hz⟩
    rwa [graphProj_mulVec] at hzy
  · rintro ⟨x, ⟨hx, hxy⟩, rfl⟩
    exact ⟨graphPt_mem_zeroSet p hx, by rw [graphProj_mulVec_graphPt]; exact hxy⟩

theorem isSheetAt_graph {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin e) (Fin n) ℂ}
    {p : MvPolynomial (Fin n) ℂ} {x : Fin n → ℂ} {s : (Fin e → ℂ) → Fin n → ℂ} (hs : IsSheetAt J A x s) :
    IsSheetAt (graphIdeal J p) (graphProj A) (graphPt p x) (graphPt p ∘ s) := by
  obtain ⟨U, hU, hxU, hsd, hsx, hsZ, V, hV, hsV⟩ := hs
  refine ⟨U, hU, by rwa [graphProj_mulVec_graphPt], (differentiable_graphPt p).comp_differentiableOn hsd,
    by rw [graphProj_mulVec_graphPt, Function.comp_apply, hsx], fun y hy => ⟨?_, graphPt_mem_zeroSet p (hsZ y hy).2⟩,
    (fun z => Fin.init z) ⁻¹' V, ?_, ?_⟩
  · rw [Function.comp_apply, graphProj_mulVec_graphPt, (hsZ y hy).1]
  · exact differentiable_init.continuous.continuousAt.preimage_mem_nhds (by rwa [graphPt_init])
  · rintro z ⟨hz, hzV⟩ hzU
    rw [graphProj_mulVec] at hzU ⊢
    have h := hsV (Fin.init z) ⟨init_mem_zeroSet p hz, hzV⟩ hzU
    rw [Function.comp_apply, ← h, graphPt_init_of_mem_zeroSet p hz]

theorem isSheetAt_init {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin e) (Fin n) ℂ}
    {p : MvPolynomial (Fin n) ℂ} {x : Fin n → ℂ} {s : (Fin e → ℂ) → Fin (n + 1) → ℂ}
    (hs : IsSheetAt (graphIdeal J p) (graphProj A) (graphPt p x) s) :
    IsSheetAt J A x (fun y => Fin.init (s y)) := by
  obtain ⟨U, hU, hxU, hsd, hsx, hsZ, V, hV, hsV⟩ := hs
  rw [graphProj_mulVec_graphPt] at hxU hsx
  refine ⟨U, hU, hxU, differentiable_init.comp_differentiableOn hsd,
    by show Fin.init (s (A *ᵥ x)) = x; rw [hsx, graphPt_init],
    fun y hy => ⟨?_, init_mem_zeroSet p (hsZ y hy).2⟩, graphPt p ⁻¹' V,
    (differentiable_graphPt p).continuous.continuousAt.preimage_mem_nhds hV, ?_⟩
  · have h := (hsZ y hy).1
    rwa [graphProj_mulVec] at h
  · rintro x' ⟨hx', hx'V⟩ hx'U
    have h := hsV (graphPt p x') ⟨graphPt_mem_zeroSet p hx', hx'V⟩ (by rwa [graphProj_mulVec_graphPt])
    rw [graphProj_mulVec_graphPt] at h
    show x' = Fin.init (s (A *ᵥ x'))
    rw [← h, graphPt_init]

theorem sheet_eventuallyEq {m : ℕ} {K : Ideal (MvPolynomial (Fin m) ℂ)} {B : Matrix (Fin e) (Fin m) ℂ}
    {z : Fin m → ℂ} {s t : (Fin e → ℂ) → Fin m → ℂ} (hs : IsSheetAt K B z s) (ht : IsSheetAt K B z t) :
    s =ᶠ[𝓝 (B *ᵥ z)] t := by
  obtain ⟨U, hU, hzU, hsd, hsz, hsZ, -⟩ := hs
  obtain ⟨U', hU', hzU', -, -, -, V, hV, htV⟩ := ht
  have hc : ContinuousAt s (B *ᵥ z) := (hsd.differentiableAt (hU.mem_nhds hzU)).continuousAt
  have hV' : ∀ᶠ y in 𝓝 (B *ᵥ z), s y ∈ V := hc.preimage_mem_nhds (by rwa [hsz])
  filter_upwards [hU.mem_nhds hzU, hU'.mem_nhds hzU', hV'] with y hy hy' hyV
  obtain ⟨hBy, hZy⟩ := hsZ y hy
  have h := htV (s y) ⟨hZy, hyV⟩ (by rwa [hBy])
  rwa [hBy] at h

theorem maDens_congr_sheet {m : ℕ} (φ : Fin e → (Fin m → ℂ) → ℝ) {s t : (Fin e → ℂ) → Fin m → ℂ}
    {y : Fin e → ℂ} (h : s =ᶠ[𝓝 y] t) :
    ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) y = ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ t) y := by
  have hH : (fun k => ReciprocityTheory.AnForm.hessC (φ k ∘ s) y) = fun k => ReciprocityTheory.AnForm.hessC (φ k ∘ t) y :=
    funext fun k => ReciprocityTheory.AnForm.A.hessC_congr' (h.fun_comp (φ k))
  unfold ReciprocityTheory.AnForm.maDens
  rw [hH]

theorem sheetSum_graphProj (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin e) (Fin n) ℂ)
    (p : MvPolynomial (Fin n) ℂ) (G : ℝ → ℝ) (F : (Fin (n + 1) → ℂ) → ℝ) (Φ : Fin e → (Fin (n + 1) → ℂ) → ℝ)
    (y : Fin e → ℂ) :
    sheetSum (graphIdeal J p) (graphProj A)
        (fun z s => G (F z * ReciprocityTheory.AnForm.maDens (fun k => Φ k ∘ s) y)) y =
      sheetSum J A (fun x s => G (F (graphPt p x) *
        ReciprocityTheory.AnForm.maDens (fun k => (fun x => Φ k (graphPt p x)) ∘ s) y)) y := by
  unfold sheetSum
  rw [fibre_graphProj, finsum_mem_image (graphPt_injective p).injOn]
  refine finsum_mem_congr rfl fun x hx => ?_
  have hiff : (∃ s, IsSheetAt (graphIdeal J p) (graphProj A) (graphPt p x) s) ↔ ∃ s, IsSheetAt J A x s :=
    ⟨fun ⟨_, h⟩ => ⟨_, isSheetAt_init h⟩, fun ⟨_, h⟩ => ⟨_, isSheetAt_graph h⟩⟩
  by_cases h : ∃ s, IsSheetAt J A x s
  · rw [dite_eq_left (hiff.2 h), dite_eq_left h]
    have hE := sheet_eventuallyEq (hiff.2 h).choose_spec (isSheetAt_graph (p := p) h.choose_spec)
    rw [graphProj_mulVec_graphPt, hx.2] at hE
    dsimp only
    rw [maDens_congr_sheet Φ hE]
    rfl
  · rw [dite_eq_right (mt hiff.1 h), dite_eq_right h]

theorem chartDens_graphProj (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin e) (Fin n) ℂ)
    (p : MvPolynomial (Fin n) ℂ) (F : (Fin (n + 1) → ℂ) → ℝ) (Φ : Fin e → (Fin (n + 1) → ℂ) → ℝ) :
    chartDens (graphIdeal J p) (graphProj A) F Φ =
      chartDens J A (fun x => F (graphPt p x)) (fun k x => Φ k (graphPt p x)) :=
  funext fun y => sheetSum_graphProj J A p id F Φ y

theorem chartAbsDens_congr_zeroSet {m : ℕ} {K : Ideal (MvPolynomial (Fin m) ℂ)} {B : Matrix (Fin e) (Fin m) ℂ}
    {f g : (Fin m → ℂ) → ℝ} (h : ∀ x ∈ zeroSet K, f x = g x) (φ : Fin e → (Fin m → ℂ) → ℝ) :
    chartAbsDens K B f φ = chartAbsDens K B g φ := by
  funext y
  unfold chartAbsDens sheetSum
  refine finsum_congr fun x => finsum_congr fun hx => ?_
  simp only [h x hx.1]

end VarIntGraph


open VarIntGraph in
theorem VarIntGraphInt.proof (hI : IntegralIndep.Statement) : VarIntGraphInt.Statement := by
  classical
  intro n e J p F Φ hJ hF hΦ hint
  have hG := graphIdeal_isPrime hJ p
  have hex : (∃ B : Matrix (Fin e) (Fin (n + 1)) ℂ, IsFiniteProjection (graphIdeal J p) B) ↔
      ∃ A : Matrix (Fin e) (Fin n) ℂ, IsFiniteProjection J A := by
    refine ⟨fun ⟨B, hB⟩ => ?_, fun ⟨A, hA⟩ => ⟨_, isFiniteProjection_graphProj p hA⟩⟩
    have hd := VarIntAdd.ringKrullDim_of_isFiniteProjection hB
    rw [ringKrullDim_graphIdeal] at hd
    exact ComplexSets.LinearNoetherNormalization.proof n e J hd
  unfold varInt
  by_cases hJA : ∃ A : Matrix (Fin e) (Fin n) ℂ, IsFiniteProjection J A
  swap
  · rw [dite_eq_right (mt hex.1 hJA), dite_eq_right hJA]
  rw [dite_eq_left (hex.2 hJA), dite_eq_left hJA, chartInt, chartInt, ← chartDens_graphProj]
  have hA := isFiniteProjection_graphProj p hJA.choose_spec
  have hB := (hex.2 hJA).choose_spec
  obtain ⟨U, hU, hZU, hFU⟩ := hF
  have hFF : ∀ z ∈ zeroSet (graphIdeal J p), U.indicator F z = F z := fun z hz => Set.indicator_of_mem (hZU hz) F
  have hFm : Measurable (U.indicator F) := by
    rw [← Set.piecewise_eq_indicator]
    exact hFU.continuousOn.measurable_piecewise continuousOn_const hU.measurableSet
  have hd := VarIntAdd.ringKrullDim_of_isFiniteProjection hB
  have hi : Integrable (chartAbsDens (graphIdeal J p) (graphProj hJA.choose) (U.indicator F) Φ) := by
    rw [chartAbsDens_congr_zeroSet hFF]
    exact hint _ hA
  have h := (hI (n + 1) e (graphIdeal J p) _ _ (U.indicator F) Φ hG hd hA hB hFm hΦ hi).2
  rw [chartInt, chartInt, CutOffDominated.chartDens_congr_zeroSet hFF Φ,
    CutOffDominated.chartDens_congr_zeroSet hFF Φ] at h
  exact h.symm

end GroundTheory.Heights₂.Heights.Targets
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PLelongSectionLimit
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology MeasureTheory

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


omit [∀ k, Fintype (ι k)] in
theorem sheetDensity_finset_sum {e : ℕ} (Q : Ideal (MRing ι))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    {T : Type*} (S : Finset T) (u : T → ((Σ k, ι k) → ℂ) → ℝ) (y : Fin e → ℂ)
    (w : ((k : K) → ι k) → ℂ) :
    sheetDensity Q Ψ φ (fun z => ∑ t ∈ S, u t z) y w = ∑ t ∈ S, sheetDensity Q Ψ φ (u t) y w := by
  unfold sheetDensity
  split_ifs <;> simp [Finset.sum_mul]

theorem integrable_fibreSum_degZero (hInt : PtsIntegrableStatement) {Q : Ideal (MRing ι)} {e : ℕ}
    (hQ : IsArithVar Q (e + 1)) {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} (hΨ : IsGoodProj Q Ψ)
    {L : Fin e → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hL : ∀ j, IsSmoothHerm (L j)) {u : ((Σ k, ι k) → ℂ) → ℝ}
    (hu : IsDegZeroSmooth u) :
    Integrable (fun y => ∑ᶠ w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre Q Ψ y, sheetDensity Q Ψ (pot L) u y w) := by
  have hsm : IsSmoothHerm (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofWeight u hu.2) :=
    Real.contDiff_exp.comp_contDiffOn hu.1.neg
  have h := hInt K ι Q e Ψ L (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofWeight u hu.2) 1 hQ hΨ hL hsm
    (Inter.isSectionOn_one hQ rfl)
  have hlog : logNorm (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofWeight u hu.2) 1 = u := by
    funext z
    simp [logNorm, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofWeight, Real.log_inv, Real.log_exp]
  rwa [hlog] at h

theorem ptsIntegral_finset_sum (hInt : PtsIntegrableStatement) {Q : Ideal (MRing ι)} {e : ℕ}
    (hQ : IsArithVar Q (e + 1)) {L : Fin e → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hL : ∀ j, IsSmoothHerm (L j)) {T : Type*}
    (S : Finset T) {u : T → ((Σ k, ι k) → ℂ) → ℝ} (hu : ∀ t, IsDegZeroSmooth (u t)) :
    ptsIntegral Q (pot L) (fun z => ∑ t ∈ S, u t z) = ∑ t ∈ S, ptsIntegral Q (pot L) (u t) := by
  classical
  by_cases hΨ : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj Q Ψ
  · simp only [ptsIntegral, dif_pos hΨ, ptsIntegralAt]
    rw [← integral_finsetSum S fun t _ =>
      integrable_fibreSum_degZero hInt hQ hΨ.choose_spec hL (hu t)]
    congr 1
    funext y
    have hfin := fibreFinite K ι Q e hΨ.choose hQ hΨ.choose_spec y
    simp only [sheetDensity_finset_sum]
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.sum_comm]
    exact Finset.sum_congr rfl fun t _ => (finsum_mem_eq_finite_toFinset_sum _ hfin).symm
  · simp [ptsIntegral, dif_neg hΨ]

theorem LelongSectionLimit.proof (hInt : PtsIntegrableStatement) (hChart : LelongChartLimit.Statement) :
    LelongSectionLimit.Statement := by
  classical
  intro K _ ι _ P n L A B s hP hL hA hB hBa hs
  obtain ⟨a, ha, hsa, -⟩ := id hs
  have hne : ∀ k, Nonempty (ι k) := fun k => ⟨(hP.2.1.2.2 k).choose⟩
  obtain ⟨δ, hδ, ρ, hρ, hsum, hsupp⟩ := SegrePartition.proof K ι hne
  have hv := isDegZeroSmooth_log hB hBa
  have hg : ∀ i, IsDegZeroSmooth (fun z => ρ i z * Real.log (B.h z)) := fun i => (hρ i).mul hv
  have hvsum : (fun z => Real.log (B.h z)) = fun z => ∑ i, ρ i z * Real.log (B.h z) :=
    funext fun z => by rw [← Finset.sum_mul, hsum, one_mul]

  have hlim := tendsto_finsetSum (Finset.univ : Finset ((k : K) → ι k)) fun i _ =>
    hChart K ι P n L A s _ i δ hP hL hA hs (hg i) hδ fun z hz => by simp [hsupp i z hz]

  have hfin : {W | W ∈ divSupp P s ∧ IsHorizontal W}.Finite := (divSupp_finite P s).subset fun _ h => h.1
  have hsplit : ∀ f : Ideal (MRing ι) → ℝ,
      ∑ᶠ (W) (_ : W ∈ divSupp P s ∧ IsHorizontal W), f W = ∑ W ∈ hfin.toFinset, f W :=
    fun f => finsum_mem_eq_finite_toFinset_sum f hfin
  have hW : ∀ W ∈ hfin.toFinset, ptsIntegral W (pot L) (fun z => Real.log (B.h z)) =
      ∑ i, ptsIntegral W (pot L) (fun z => ρ i z * Real.log (B.h z)) := by
    intro W hW
    rw [Set.Finite.mem_toFinset] at hW
    have hWar : IsArithVar W (n + 1) := (divSuppArith K ι P (n + 1) A s W hP hs hW.1).1 hW.2
    rw [hvsum]
    exact ptsIntegral_finset_sum hInt hWar hL Finset.univ hg
  have hrhs : (∑ i, ∑ᶠ (W) (_ : W ∈ divSupp P s ∧ IsHorizontal W),
        (multAt (P ⊔ Ideal.span {s}) W : ℝ) * ptsIntegral W (pot L) (fun z => ρ i z * Real.log (B.h z))) =
      ∑ᶠ (W) (_ : W ∈ divSupp P s ∧ IsHorizontal W),
        (multAt (P ⊔ Ideal.span {s}) W : ℝ) * ptsIntegral W (pot L) (fun z => Real.log (B.h z)) := by
    simp only [hsplit]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun W hW' => ?_
    rw [hW W hW', Finset.mul_sum]
  rw [hrhs] at hlim

  refine hlim.congr' (eventually_nhdsWithin_of_forall fun ε (hε : 0 < ε) => ?_)
  set M := (regLine A s ε ha hsa).tensor A
  have hM : IsSmoothHerm M := (isSmoothHerm_regLine hA hε ha hsa).mul hA
  have hcongr : ∀ g : ((Σ k, ι k) → ℂ) → ℝ,
      ptsIntegral P
          (Fin.cons (fun z => Real.log (‖eval z (map (Int.castRingHom ℂ) s)‖ ^ 2 + ε * A.h z ^ 2) / 2)
            (pot L)) g = ptsIntegral P (pot (Fin.cons M L)) g := by
    intro g
    rw [Inter.PtsAddFirst.pot_cons]
    refine Inter.DiagRAux.ptsIntegral_congr_mcPts P (fun j => ?_) (fun _ _ => rfl)
    refine Fin.cases ?_ (fun i => ?_) j
    · intro z hz
      simp only [Fin.cons_zero]
      exact (log_regLine_tensor A s hε ha hsa z hz.1).symm
    · intro z _
      simp only [Fin.cons_succ]
  have hML : ∀ j, IsSmoothHerm ((Fin.cons M L : Fin (n + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) j) :=
    fun j => Fin.cases hM (fun i => hL i) j
  simp only [hcongr]
  rw [hvsum]
  exact (ptsIntegral_finset_sum hInt hP hML Finset.univ hg).symm

end GroundTheory.Heights₂.Heights.Targets
end
end
