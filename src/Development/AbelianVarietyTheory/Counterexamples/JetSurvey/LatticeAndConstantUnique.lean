module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelLatIn
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsRankOneCuspLatticeDataOfPrincipal
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoreArithmeticGroupContainsPrincipalCongruence
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsIsChartGOfBasis
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifBijectiveOfParam
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsRetractTensorTriple

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Counterexamples.JetSurvey.LatticeAndConstantUnique
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj

namespace GlobalTheory.ModelLatticeCheck

def Fits {D : D7} (T : Core D) (j : ℕ) (σ : T.Q.c.F →+* ℂ) (k : (T.U j σ).Comp) (Xx : DataX D.host.E D.R.r) : Prop :=
  Xx.toData = (T.U j σ).X k ∧ Xx.g = T.Q.l.M ∧
    Xx.Λ = Submodule.span (𝓞 D.host.E) {v | ∃ a ∈ D.host.AA, ∃ u ∈ Xx.L', v = a • u}

theorem comp_nonempty {D : D7} (T : Core D) (j : ℕ) (σ : T.Q.c.F →+* ℂ) : Nonempty (T.U j σ).Comp :=
  ⟨(T.dict j σ 1).1⟩

theorem le_of_span_le {E : Type} [Field E] [NumberField E] {r : ℕ}
    (A : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hA : A ≠ 0) (L₁ L₂ : Submodule (𝓞 E) (Fin r → E))
    (h : Submodule.span (𝓞 E) {v | ∃ a ∈ A, ∃ u ∈ L₁, v = a • u} ≤
      Submodule.span (𝓞 E) {v | ∃ a ∈ A, ∃ u ∈ L₂, v = a • u}) : L₁ ≤ L₂ := by
  intro u hu
  have key : ∀ b ∈ A⁻¹, ∀ x ∈ Submodule.span (𝓞 E) {v | ∃ a ∈ A, ∃ u ∈ L₂, v = a • u}, b • x ∈ L₂ := by
    intro b hb x hx
    induction hx using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨a, ha, w, hw, rfl⟩ := hv
      have : b * a ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) := by
        rw [← inv_mul_cancel₀ hA]; exact FractionalIdeal.mul_mem_mul hb ha
      obtain ⟨z, hz⟩ := (FractionalIdeal.mem_one_iff _).1 this
      rw [smul_smul, ← hz, algebraMap_smul]
      exact L₂.smul_mem z hw
    | zero => simp
    | add v w _ _ hv hw => rw [smul_add]; exact add_mem hv hw
    | smul c v _ hv => rw [smul_comm]; exact L₂.smul_mem c hv
  have h1 : (1 : E) ∈ A⁻¹ * A := by
    rw [inv_mul_cancel₀ hA]; exact FractionalIdeal.one_mem_one _
  have : ∀ c ∈ A⁻¹ * A, c • u ∈ L₂ := by
    intro c hc
    refine FractionalIdeal.mul_induction_on hc (C := fun c => c • u ∈ L₂) ?_ ?_
    · intro b hb a ha
      rw [mul_smul]
      exact key b hb _ (h (Submodule.subset_span ⟨a, ha, u, hu, rfl⟩))
    · intro x y hx hy
      rw [add_smul]; exact add_mem hx hy
  simpa using this 1 h1

theorem AA_ne_zero (D : D7) : D.host.AA ≠ 0 := by
  intro h
  have h1 := GlobalTheory.LatticeData.absNorm_ccK_mem D
  rw [h, FractionalIdeal.mem_zero_iff] at h1
  exact D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 (by exact_mod_cast h1))

theorem holds_by_value (D : D7) (T : Core D) (h : LawsCore T) (j : ℕ) (hj : InR D j) (σ : T.Q.c.F →+* ℂ)
    (hσ : GoodEmb T.Q.c σ) (k : (T.U j σ).Comp) :
    ∃ X : DataX D.host.E D.R.r, Fits T j σ k X ∧ X.k0 = 2 * xiR D ∧ X.NA = Ideal.absNorm D.host.𝔟 ∧
      X.NC = Ideal.absNorm D.host.ccK := by
  obtain ⟨Xx, h1, h2, h3, h4, -⟩ :=
    GlobalTheory.LatticeData.exists_dataX_of_hasPrinc D T h j hj σ hσ (GlobalTheory.PrincCore.hasPrinc_core D T h j hj σ hσ) k
  refine ⟨{ Xx with
    NA := Ideal.absNorm D.host.𝔟
    NC := Ideal.absNorm D.host.ccK
    NA_pos := Nat.pos_of_ne_zero fun e => GlobalTheory.LatticeData.halfDifferent_ne_bot D (Ideal.absNorm_eq_zero_iff.1 e)
    NC_pos := Nat.pos_of_ne_zero fun e => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 e)
    NA_sub := fun x hx => ?_
    NC_sub := fun x hx => ?_ }, ⟨h1, h2, h3⟩, h4, rfl, rfl⟩
  · rw [h3] at hx
    induction hx using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨a, ha, u, hu, rfl⟩ := hv
      obtain ⟨z, hz⟩ := GlobalTheory.LatticeData.absNorm_mul_mem_one D ha
      rw [smul_smul, ← hz, algebraMap_smul]
      exact Xx.L'.smul_mem z hu
    | zero => simp
    | add v w _ _ hv hw => rw [smul_add]; exact add_mem hv hw
    | smul c v _ hv => rw [smul_comm]; exact Xx.L'.smul_mem c hv
  · rw [h3]
    exact Submodule.subset_span ⟨_, GlobalTheory.LatticeData.absNorm_ccK_mem D, x, hx, rfl⟩

end GlobalTheory.ModelLatticeCheck
end

section -- merged from Development.AbelianVarietyTheory.Counterexamples.JetSurvey.WitnessIsFormalParam
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (FGLaw)
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChartDataChecks

open GlobalTheory.ChartCompare

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0)


set_option maxHeartbeats 800000 in
theorem tanBasis_of_lieBasis {n : ℕ} (v : Fin n → (epsR S ⟶ (Over.pullback x0).obj t.G)) (hB : IsLieBasis v) :
    ∃ tg : Fin n → (Sp (DualNumber S) ⟶ t.G.left), IsTanBasisG t x0 tg := by
  classical
  have hp := isGrpPullback_pullback t.G x0
  let φ := pullback.fst t.G.hom x0
  let up : ∀ w : Sp (DualNumber S) ⟶ t.G.left, w ≫ t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x0 →
      (epsR S ⟶ (Over.pullback x0).obj t.G) := fun w h => Over.homMk (pullback.lift w _ h) (pullback.lift_snd _ _ _)
  have hup : ∀ w h, (up w h).left ≫ φ = w := fun w h => pullback.lift_fst _ _ _
  have inj : ∀ {T : Over (Sp S)} {u v : T ⟶ (Over.pullback x0).obj t.G}, u.left ≫ φ = v.left ≫ φ → u = v := fun h =>
    Over.OverMorphism.ext (pullback.hom_ext h ((Over.w _).trans (Over.w _).symm))
  have one : ∀ T : Over (Sp S), (1 : T ⟶ (Over.pullback x0).obj t.G).left ≫ φ = (1 : Over.mk (T.hom ≫ x0) ⟶ t.G).left :=
    fun T => congrArg (fun q => q.left) (map_one (pushHom hp T))
  have tan : ∀ w : epsR S ⟶ (Over.pullback x0).obj t.G, IsTangent w ↔ IsTanAtG t x0 (w.left ≫ φ) := fun w => by
    have e : (1 : Chart.sp (R₀ := S) S ⟶ (Over.pullback x0).obj t.G).left ≫ φ = (1 : Over.mk x0 ⟶ t.G).left :=
      (one _).trans (congrArg (· ≫ (η[t.G]).left) (show Spec.map (CommRingCat.ofHom (RingHom.id S)) ≫ x0 = x0 by simp))
    rw [← Chart.isTan_iff]
    refine ⟨fun h => ⟨Over.w (pushPt hp.1.w w), ?_⟩, fun h => inj ?_⟩
    · exact (Category.assoc _ _ _).symm.trans ((congrArg (fun q => q.left ≫ φ) h).trans e)
    · exact (Category.assoc _ _ _).trans (h.2.trans e.symm)
  have pr : ∀ {n} (u : Fin n → (epsR S ⟶ (Over.pullback x0).obj t.G)), (List.ofFn u).prod.left ≫ φ =
      (List.ofFn fun i => (pushPt hp.1.w (u i) : tEpsG x0 ⟶ t.G)).prod.left := fun u =>
    congrArg (fun q => q.left) ((map_list_prod (pushHom hp (epsR S)) _).trans (by rw [List.map_ofFn]; rfl))
  have comb : ∀ {n} (c : Fin n → S) (v : Fin n → (epsR S ⟶ (Over.pullback x0).obj t.G)) w,
      IsLieComb c v w ↔ IsCombAtG t x0 (fun i => (v i).left ≫ φ) c (w.left ≫ φ) := fun c v w => by
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨fun i => pushPt hp.1.w (u i), fun i => (congrArg (· ≫ φ) (hu i)).trans (Category.assoc _ _ _), (pr u).symm⟩
    · rintro ⟨u, hu, hw⟩
      refine ⟨fun i => up (u i).left (Over.w _), fun i => pullback.hom_ext ?_ ?_, inj (hw.symm.trans (Eq.trans ?_ (pr _).symm))⟩
      · exact (hup _ _).trans ((hu i).trans (Category.assoc _ _ _).symm)
      · refine (Over.w (up (u i).left (Over.w _))).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
        refine Eq.trans ?_ (congrArg (spMap (epsScaleR (c i)) ≫ ·) (Over.w (v i))).symm
        exact (Over.w (Chart.spMap (Chart.scaleD (c i)))).symm
      · have : u = fun i => (pushPt hp.1.w (up (u i).left (Over.w _)) : tEpsG x0 ⟶ t.G) :=
          funext fun i => Over.OverMorphism.ext (hup (u i).left (Over.w _)).symm
        exact congrArg (fun q : _ → (tEpsG x0 ⟶ t.G) => (List.ofFn q).prod.left) this

  let e := Fintype.equivFin (Fin n)
  let s : Fin (Fintype.card (Fin n)) ≃ Fin n := finCongr (Fintype.card_fin n)
  have hB' : IsLieBasis fun i => v (s i) := by
    have : ∀ (k : ℕ) (hk : k = n), IsLieBasis fun i : Fin k => v (finCongr hk i) := by
      rintro _ rfl; exact hB
    exact this _ _
  refine ⟨fun l => (v (s (e l))).left ≫ φ, fun l => (tan _).1 (hB.1 _), fun w hw => ?_⟩
  obtain ⟨c, hc, hu⟩ := hB'.2 (up w hw.1) ((tan _).2 (by rw [hup]; exact hw))
  refine ⟨fun l => c (e l), ?_, fun a ha => ?_⟩
  · have := (comb _ _ _).1 hc
    rw [hup] at this
    simpa only [e, Equiv.apply_symm_apply] using this
  · have := hu (fun i => a (e.symm i)) ((comb _ _ _).2 (by
      rw [hup]; simpa only [e, Equiv.apply_symm_apply] using ha))
    funext l; rw [← this]; simp

theorem premises_met [IsLocalRing S] :
    ∃ (n : ℕ) (tg : Fin n → (Sp (DualNumber S) ⟶ t.G.left)), IsTanBasisG t x0 tg := by
  have := t.semi.smooth
  have : Smooth ((Over.pullback x0).obj t.G).hom :=
    smooth_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) this
  obtain ⟨n, v, hv⟩ := Chart.exists_isLieBasis _ this
  exact ⟨n, tanBasis_of_lieBasis t x0 v hv⟩

end GlobalTheory.ChartDataChecks
end
end
