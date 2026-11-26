module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrincipalNearBoundary
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.QuotientUniformizationChartAt
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.QuotientUniformizationCharts

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.HeightBoundComplexConjugate
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.QuotUnif Metric

namespace PositivityTheory.Xgn.QuotientUniformizationConjugate

noncomputable def lf {S : Scheme.{0}} {G : Over S} {R : Type} [CommRing R] {x : Sp R ⟶ S} (v : epsAt x ⟶ G) :
    Sp (DualNumber R) ⟶ G.left :=
  v.left

theorem sq_alg {R R' : Type} [CommRing R] [CommRing R'] (e : R →+* R') :
    spMap (dualMap e) ≫ spMap (algebraMap R (DualNumber R)) = spMap (algebraMap R' (DualNumber R')) ≫ spMap e := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine RingHom.ext fun r => ?_
  show dualMap e (algebraMap R (DualNumber R) r) = algebraMap R' (DualNumber R') (e r)
  rw [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.algebraMap_eq_inl]
  ext <;> simp [dualMap]

theorem sq_fst {R R' : Type} [CommRing R] [CommRing R'] (e : R →+* R') :
    spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ spMap (dualMap e) =
      spMap e ≫ spMap (TrivSqZeroExt.fstHom R R R).toRingHom := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine RingHom.ext fun r => ?_
  show (dualMap e r).fst = e r.fst
  simp [dualMap]

theorem one_comp {S T T' : Scheme.{0}} (G : Over S) [GrpObj G] (x : T ⟶ S) (a : T' ⟶ T) :
    a ≫ (1 : Over.mk x ⟶ G).left = (1 : Over.mk (a ≫ x) ⟶ G).left := by
  let k : Over.mk (a ≫ x) ⟶ Over.mk x := Over.homMk a rfl
  have : k ≫ (1 : Over.mk x ⟶ G) = 1 := by
    rw [Hom.one_def, Hom.one_def, ← Category.assoc, comp_toUnit]
  exact congrArg (fun q => q.left) this

theorem exists_bc {S : Scheme.{0}} {G : Over S} [GrpObj G] {R R' : Type} [CommRing R] [CommRing R'] (e : R →+* R')
    (z : Sp R ⟶ S) (z' : Sp R' ⟶ S) (hz : z' = spMap e ≫ z) (v : epsAt z ⟶ G) :
    ∃ v' : epsAt z' ⟶ G, lf v' = spMap (dualMap e) ≫ lf v ∧ (IsTanAt G z v → IsTanAt G z' v') := by
  subst hz
  have hw : lf v ≫ G.hom = spMap (algebraMap R (DualNumber R)) ≫ z := Over.w v
  refine ⟨Over.homMk (spMap (dualMap e) ≫ lf v) ?_, rfl, fun ht => ?_⟩
  · show (spMap (dualMap e) ≫ lf v) ≫ G.hom = spMap (algebraMap R' (DualNumber R')) ≫ spMap e ≫ z
    rw [Category.assoc, hw, ← Category.assoc, sq_alg, Category.assoc]
  · have ht' : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ lf v = (1 : Over.mk z ⟶ G).left := ht
    show spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ spMap (dualMap e) ≫ lf v =
      (1 : Over.mk (spMap e ≫ z) ⟶ G).left
    rw [← Category.assoc, sq_fst, Category.assoc, ht']
    exact one_comp G z (spMap e)

theorem exists_lift {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {R : Type} [CommRing R] (x' : Sp R ⟶ S')
    (u : epsAt (x' ≫ f) ⟶ G) :
    ∃ v : epsAt x' ⟶ G', lf v ≫ φ = lf u ∧ (IsTanAt G (x' ≫ f) u → IsTanAt G' x' v) := by
  obtain ⟨v, rfl⟩ := (LiePull.tanPts h x').surjective u
  exact ⟨v, rfl, (LiePull.isTan_iff h x' v).1⟩

theorem hodge_congr {S : Scheme.{0}} {G : Over S} [GrpObj G] (Lb : LB G.left) {z z' : Sp ℂ ⟶ S} (h : z = z')
    {v w : epsAt z ⟶ G} {v' w' : epsAt z' ⟶ G} (hv : lf v = lf v') (hw : lf w = lf w') {c : ℂ}
    (hc : HodgeIP G Lb z v w c) : HodgeIP G Lb z' v' w' c := by
  subst h
  obtain rfl : v = v' := Over.OverMorphism.ext hv
  obtain rfl : w = w' := Over.OverMorphism.ext hw
  exact hc

end PositivityTheory.Xgn.QuotientUniformizationConjugate

open PositivityTheory.Xgn.QuotientUniformizationConjugate in
theorem PositivityTheory.Xgn.height_bound_complex_conjugate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel t.G ξ Li) (K : Type) (J : K → Type) (y : (Σ k, J k) → Ω) (h : LieMetric M y) (C : ℝ) (z : Sp ℂ ⟶ X), AbBound t h C (spMap (starRingEnd ℂ) ≫ z) → AbBound t h C z := by
  intro E _ _ _ H X t Ω _ ξ Li _ _ M K J y h C z hb P
  obtain ⟨P', mK, mB, c1, c2⟩ := GlobalTheory.T.abelian_part_base_change E H X t ℂ ℂ z P (starRingEnd ℂ)
  obtain ⟨hp, hb'⟩ := hb P'
  refine ⟨(CoverDenseAlt.isPrincipal_iff_of_base_change E H ℂ ℂ (starRingEnd ℂ) P.tB P'.tB mB).1 hp, fun v v₀ c hv hv₀ hc => ?_⟩
  have hid : 𝟙 (Sp ℂ) ≫ spMap (starRingEnd ℂ) = spMap (starRingEnd ℂ) ≫ 𝟙 (Sp ℂ) := by
    rw [Category.id_comp, Category.comp_id]
  obtain ⟨u, hu, hut⟩ := exists_bc (starRingEnd ℂ) (𝟙 (Sp ℂ)) _ hid v
  obtain ⟨v', hv', hvt⟩ := exists_lift mK.cart (𝟙 (Sp ℂ)) u
  obtain ⟨v₀', hv₀', -⟩ := exists_bc (starRingEnd ℂ) z _ rfl v₀
  obtain ⟨a, ha, -⟩ := exists_bc (starRingEnd ℂ) (𝟙 (Sp ℂ)) _ rfl (v ≫ P.τ.q ≫ P.e.hom)
  obtain ⟨b, hb₁, -⟩ := exists_bc (starRingEnd ℂ) (𝟙 (Sp ℂ)) _ hid (v ≫ P.τ.q ≫ P.e.hom)
  have hv'' : lf v' ≫ mK.φ = spMap (dualMap (starRingEnd ℂ)) ≫ lf v := hv'.trans hu
  have hv₀'' : lf v ≫ P.m.φ = lf v₀ := hv₀
  have e₁ : lf v' ≫ P'.m.φ = lf v₀' := by
    rw [← c1, ← Category.assoc, hv'', Category.assoc, hv₀'', hv₀']
  have e₂ : lf (v' ≫ P'.τ.q ≫ P'.e.hom) ≫ mB.φ = lf b := by
    have s₁ : lf (v' ≫ P'.τ.q ≫ P'.e.hom) = lf v' ≫ (P'.τ.q ≫ P'.e.hom).left := rfl
    have s₂ : lf (v ≫ P.τ.q ≫ P.e.hom) = lf v ≫ (P.τ.q ≫ P.e.hom).left := rfl
    rw [hb₁, s₁, s₂, Category.assoc, ← c2, ← Category.assoc, hv'', Category.assoc]
  have h₁ := GlobalTheory.T.hodge_inner_product_conjugate E H (Sp ℂ) P.tB (𝟙 _) _ _ a a c ha ha hc
  have hab : lf a = lf b := ha.trans hb₁.symm
  have h₂ := hodge_congr P.tB.PP.L hid.symm hab hab h₁
  have h₃ := ((GlobalTheory.T.hodge_inner_product_pullback_unique E H (Sp ℂ) (Sp ℂ) P'.tB P.tB (spMap (starRingEnd ℂ)) mB (𝟙 _) _ _ b b e₂ e₂).1 _).2 h₂
  have h₄ := hb' v' v₀' _ (hvt (hut hv)) e₁ h₃
  rw [h.conj z v₀ v₀ v₀' v₀' hv₀' hv₀', Complex.conj_re, Complex.conj_re] at h₄
  exact h₄
end

section -- merged from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.QuotientUniformizationLower
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.QuotUnif Metric

namespace PositivityTheory.Xgn.QuotientUniformizationLower

open scoped ComplexOrder

theorem core_gram {V : Type} [AddCommGroup V] [Module ℂ V] (core : InnerProductSpace.Core ℂ V) {N : ℕ}
    (b : Fin N → V) (Γ : Matrix (Fin N) (Fin N) ℂ) (hΓ : ∀ i j, Γ i j = core.inner (b i) (b j)) :
    (LinearIndependent ℂ b → Γ.PosDef) ∧
      ∀ c : Fin N → ℂ, star c ⬝ᵥ (Γ *ᵥ c) = core.inner (∑ i, c i • b i) (∑ i, c i • b i) := by
  have hzl : ∀ y : V, core.inner 0 y = 0 := fun y => by
    have h := core.smul_left 0 y 0
    simpa using h
  have hsl : ∀ (s : Finset (Fin N)) (f : Fin N → V) (y : V),
      core.inner (∑ i ∈ s, f i) y = ∑ i ∈ s, core.inner (f i) y := by
    intro s f y
    induction s using Finset.induction_on with
    | empty => simpa using hzl y
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, core.add_left, ih]
  have hconj : ∀ x y : V, core.inner x y = starRingEnd ℂ (core.inner y x) := fun x y =>
    (core.conj_inner_symm x y).symm
  have hsr : ∀ (s : Finset (Fin N)) (f : Fin N → V) (x : V),
      core.inner x (∑ i ∈ s, f i) = ∑ i ∈ s, core.inner x (f i) := by
    intro s f x
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hconj, hsl, map_sum]
    exact Finset.sum_congr rfl fun i _ => (hconj x (f i)).symm
  have hsmr : ∀ (x y : V) (r : ℂ), core.inner x (r • y) = r * core.inner x y := by
    intro x y r
    rw [hconj, core.smul_left, map_mul, ← hconj]
    simp
  have hid : ∀ c : Fin N → ℂ, star c ⬝ᵥ (Γ *ᵥ c) = core.inner (∑ i, c i • b i) (∑ i, c i • b i) := by
    intro c
    rw [hsl]
    simp only [dotProduct, mulVec, Pi.star_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [core.smul_left, hsr, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hsmr, hΓ, Complex.star_def]
    ring
  refine ⟨fun hli => ?_, hid⟩
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨Matrix.IsHermitian.ext fun i j => ?_, fun c hc => ?_⟩
  · rw [hΓ, hΓ]
    exact core.conj_inner_symm (b i) (b j)
  · rw [hid]
    set x := ∑ i, c i • b i with hxdef
    have hx : x ≠ 0 := by
      intro h0
      apply hc
      funext i
      exact Fintype.linearIndependent_iff.1 hli c h0 i
    have him : (core.inner x x).im = 0 := by
      have h := congrArg Complex.im (core.conj_inner_symm x x)
      simp at h
      linarith
    have hre : 0 < (core.inner x x).re := by
      have h1 := core.re_inner_nonneg x
      rcases h1.lt_or_eq with h | h
      · exact h
      · exfalso
        apply hx
        apply core.definite
        exact Complex.ext (by simpa using h.symm) (by simpa using him)
    rw [Complex.pos_iff]
    exact ⟨hre, him.symm⟩

private theorem norm_sq_add_norm_sq_sub_eq_complete_square {N : ℕ} (D : Matrix (Fin N) (Fin N) ℂ) (ε : ℝ) (hD : ∀ i j, ‖D i j‖ ≤ ε)
    (hε : 0 ≤ ε) (c : Fin N → ℂ) : ‖star c ⬝ᵥ (D *ᵥ c)‖ ≤ N * N * ε * ‖c‖ ^ 2 := by
  simp only [dotProduct, mulVec, Pi.star_apply]
  calc ‖∑ i, star (c i) * ∑ j, D i j * c j‖ ≤ ∑ i, ‖star (c i) * ∑ j, D i j * c j‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin N, ∑ j : Fin N, ε * ‖c‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_mul]
        refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)).trans ?_
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro j _
        rw [norm_mul, norm_star]
        have h1 := norm_le_pi_norm c i
        have h2 := norm_le_pi_norm c j
        calc ‖c i‖ * (‖D i j‖ * ‖c j‖) ≤ ‖c‖ * (ε * ‖c‖) := by
              gcongr
              exact hD i j
          _ = ε * ‖c‖ ^ 2 := by ring
    _ = N * N * ε * ‖c‖ ^ 2 := by simp [Finset.sum_const]; ring

private theorem exists_pos_mul_norm_sq_le_re_quadratic {N : ℕ} (G : Matrix (Fin N) (Fin N) ℂ)
    (hpos : ∀ c : Fin N → ℂ, c ≠ 0 → 0 < (star c ⬝ᵥ (G *ᵥ c)).re) :
    ∃ δ > 0, ∀ c : Fin N → ℂ, δ * ‖c‖ ^ 2 ≤ (star c ⬝ᵥ (G *ᵥ c)).re := by
  by_cases hN : N = 0
  · subst hN
    refine ⟨1, one_pos, fun c => ?_⟩
    have hc : c = 0 := Subsingleton.elim _ _
    subst hc
    simp
  haveI : Nonempty (Fin N) := ⟨⟨0, Nat.pos_of_ne_zero hN⟩⟩
  have hne : (sphere (0 : Fin N → ℂ) 1).Nonempty := by
    refine ⟨fun _ => 1, ?_⟩
    rw [mem_sphere_zero_iff_norm, pi_norm_const]
    simp
  have hcont : Continuous fun c : Fin N → ℂ => (star c ⬝ᵥ (G *ᵥ c)).re := by
    simp only [dotProduct, mulVec, Pi.star_apply]
    fun_prop
  obtain ⟨c0, hc0, hmin⟩ := (isCompact_sphere (0 : Fin N → ℂ) 1).exists_isMinOn hne hcont.continuousOn
  have hc0n : ‖c0‖ = 1 := mem_sphere_zero_iff_norm.1 hc0
  have hc0z : c0 ≠ 0 := fun h => by rw [h, norm_zero] at hc0n; exact zero_ne_one hc0n
  refine ⟨(star c0 ⬝ᵥ (G *ᵥ c0)).re, hpos c0 hc0z, fun c => ?_⟩
  by_cases hc : c = 0
  · subst hc
    simp
  set t : ℝ := ‖c‖ with ht_def
  have ht : 0 < t := norm_pos_iff.2 hc
  set c' : Fin N → ℂ := ((t⁻¹ : ℝ) : ℂ) • c with hc'_def
  have hc' : c' ∈ sphere (0 : Fin N → ℂ) 1 := by
    rw [mem_sphere_zero_iff_norm, hc'_def, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_inv, abs_of_pos ht, inv_mul_cancel₀ ht.ne']
  have hcc : c = ((t : ℝ) : ℂ) • c' := by
    rw [hc'_def, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ ht.ne', Complex.ofReal_one, one_smul]
  have hq : (star c ⬝ᵥ (G *ᵥ c)).re = t ^ 2 * (star c' ⬝ᵥ (G *ᵥ c')).re := by
    rw [hcc, Matrix.mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul]
    simp only [smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
    rw [← _root_.mul_assoc, ← Complex.ofReal_mul, Complex.re_ofReal_mul]
    ring
  have hm : (star c0 ⬝ᵥ (G *ᵥ c0)).re ≤ (star c' ⬝ᵥ (G *ᵥ c')).re := hmin hc'
  rw [hq, mul_comm]
  exact mul_le_mul_of_nonneg_left hm (sq_nonneg t)

theorem analytic {U : Type} [MetricSpace U] [ProperSpace U] (o : U) {N g : ℕ}
    (b : U → Fin N → Fin g → ℂ) (hb : ∀ i j, ContinuousOn (fun u => b u i j) (ball o 1))
    (Γ : U → Matrix (Fin N) (Fin N) ℂ) (hΓ : ∀ i j, ContinuousOn (fun u => Γ u i j) (ball o 1))
    (hc : ∀ u ∈ ball o 1, ∃ core : InnerProductSpace.Core ℂ (Fin g → ℂ),
      ∀ i j, Γ u i j = core.inner (b u i) (b u j))
    (h0 : LinearIndependent ℂ (b o) ∧ Submodule.span ℂ (Set.range (b o)) = ⊤) :
    ∃ ρ Kc : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ 0 < Kc ∧ ∀ u ∈ ball o ρ, ∀ core : InnerProductSpace.Core ℂ (Fin g → ℂ),
      (∀ i j, Γ u i j = core.inner (b u i) (b u j)) → ∀ x : Fin g → ℂ,
        ∑ i, ‖x i‖ ^ 2 ≤ Kc * (core.inner x x).re := by
  obtain ⟨core0, hcore0⟩ := hc o (mem_ball_self one_pos)
  have hpos0 : ∀ c : Fin N → ℂ, c ≠ 0 → 0 < (star c ⬝ᵥ (Γ o *ᵥ c)).re := by
    intro c hc0
    have hpd := (core_gram core0 (b o) (Γ o) hcore0).1 h0.1
    exact (Complex.pos_iff.1 (hpd.dotProduct_mulVec_pos hc0)).1
  obtain ⟨δ, hδ, hδc⟩ := exists_pos_mul_norm_sq_le_re_quadratic (Γ o) hpos0
  have hNg : Module.finrank ℂ (Fin N → ℂ) = Module.finrank ℂ (Fin g → ℂ) := by
    rw [Module.finrank_fin_fun, Module.finrank_fin_fun]
    have hB := Module.finrank_eq_card_basis (Module.Basis.mk h0.1 h0.2.ge)
    simpa using hB.symm
  set Mb : ℝ := ∑ i, (‖b o i‖ + 1) with hMb_def
  have hMb : 0 ≤ Mb := Finset.sum_nonneg fun i _ => by positivity
  set ε : ℝ := δ / (2 * (N * N + 1)) with hε_def
  have hε : 0 < ε := by positivity
  have hmem : ball o 1 ∈ 𝓝 o := isOpen_ball.mem_nhds (mem_ball_self one_pos)
  have hcont : ∀ᶠ u in 𝓝 o, (∀ i j, ‖Γ u i j - Γ o i j‖ < ε) ∧ (∀ i, ‖b u i‖ < ‖b o i‖ + 1) := by
    refine Filter.Eventually.and ?_ ?_
    · rw [Filter.eventually_all]
      intro i
      rw [Filter.eventually_all]
      intro j
      have hca := (hΓ i j).continuousAt hmem
      exact (hca.eventually (Metric.ball_mem_nhds (Γ o i j) hε)).mono fun u hu => by
        rwa [dist_eq_norm] at hu
    · rw [Filter.eventually_all]
      intro i
      have hcb : ContinuousAt (fun u => b u i) o :=
        continuousAt_pi.2 fun j => (hb i j).continuousAt hmem
      exact hcb.norm.eventually (gt_mem_nhds (lt_add_one ‖b o i‖))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 hcont
  refine ⟨min r 1, (g * Mb ^ 2 + 1) * (2 / δ), lt_min hr one_pos, min_le_right _ _, by positivity, ?_⟩
  intro u hu core hcore x
  have hu' : u ∈ ball o r := ball_subset_ball (min_le_left _ _) hu
  obtain ⟨hΓu, hbu⟩ := hball u hu'
  have hid := (core_gram core (b u) (Γ u) hcore).2
  have h5 : (N : ℝ) * N * ε ≤ δ / 2 := by
    have hN : (0 : ℝ) ≤ N * N := by positivity
    have e1 : (N : ℝ) * N * ε = δ / 2 * ((N * N) / (N * N + 1)) := by
      rw [hε_def]; field_simp
    rw [e1]
    calc δ / 2 * ((N * N) / (N * N + 1)) ≤ δ / 2 * 1 := by
          gcongr
          exact (div_le_one (by positivity)).2 (by linarith)
      _ = δ / 2 := mul_one _
  have hlow : ∀ c : Fin N → ℂ, δ / 2 * ‖c‖ ^ 2 ≤ (star c ⬝ᵥ (Γ u *ᵥ c)).re := by
    intro c
    have h1 := hδc c
    have h2 := norm_sq_add_norm_sq_sub_eq_complete_square (Γ u - Γ o) ε (fun i j => (hΓu i j).le) hε.le c
    have h3 : star c ⬝ᵥ (Γ u *ᵥ c) = star c ⬝ᵥ (Γ o *ᵥ c) + star c ⬝ᵥ ((Γ u - Γ o) *ᵥ c) := by
      rw [Matrix.sub_mulVec, dotProduct_sub]
      ring
    have h4 : |(star c ⬝ᵥ ((Γ u - Γ o) *ᵥ c)).re| ≤ N * N * ε * ‖c‖ ^ 2 :=
      (Complex.abs_re_le_norm _).trans h2
    have h6 := neg_abs_le (star c ⬝ᵥ ((Γ u - Γ o) *ᵥ c)).re
    have h7 := mul_le_mul_of_nonneg_right h5 (sq_nonneg ‖c‖)
    rw [h3, Complex.add_re]
    nlinarith
  have hz : core.inner (0 : Fin g → ℂ) 0 = 0 := by
    have h := core.smul_left 0 0 0
    simpa using h
  let B := Fintype.linearCombination ℂ (b u)
  have hinj : Function.Injective B := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc0
    by_contra hne
    have hcpos : 0 < ‖c‖ := norm_pos_iff.2 hne
    have h1 := hlow c
    have hs : ∑ i, c i • b u i = 0 := by
      rw [Fintype.linearCombination_apply] at hc0
      exact hc0
    rw [hid c, hs, hz, Complex.zero_re] at h1
    have : 0 < δ / 2 * ‖c‖ ^ 2 := by positivity
    linarith
  obtain ⟨c, hcx⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hNg).1 hinj x
  have hcx' : ∑ i, c i • b u i = x := by
    rw [Fintype.linearCombination_apply] at hcx
    exact hcx
  have hxc : ‖x‖ ≤ Mb * ‖c‖ := by
    rw [← hcx']
    calc ‖∑ i, c i • b u i‖ ≤ ∑ i, ‖c i • b u i‖ := norm_sum_le _ _
      _ ≤ ∑ i, ‖c‖ * (‖b o i‖ + 1) := Finset.sum_le_sum fun i _ => by
          rw [norm_smul]
          exact mul_le_mul (norm_le_pi_norm c i) (hbu i).le (norm_nonneg _) (norm_nonneg _)
      _ = Mb * ‖c‖ := by rw [← Finset.mul_sum, hMb_def]; ring
  have hsum : ∑ i, ‖x i‖ ^ 2 ≤ g * ‖x‖ ^ 2 := by
    calc ∑ i, ‖x i‖ ^ 2 ≤ ∑ _i : Fin g, ‖x‖ ^ 2 :=
          Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm x i) 2
      _ = g * ‖x‖ ^ 2 := by simp
  have hre := hlow c
  rw [hid c, hcx'] at hre
  have hg0 : (0 : ℝ) ≤ g := by positivity
  calc ∑ i, ‖x i‖ ^ 2 ≤ g * ‖x‖ ^ 2 := hsum
    _ ≤ g * (Mb * ‖c‖) ^ 2 := by gcongr
    _ ≤ (g * Mb ^ 2 + 1) * ‖c‖ ^ 2 := by nlinarith [sq_nonneg ‖c‖]
    _ = (g * Mb ^ 2 + 1) * (2 / δ) * (δ / 2 * ‖c‖ ^ 2) := by field_simp
    _ ≤ (g * Mb ^ 2 + 1) * (2 / δ) * (core.inner x x).re := by gcongr

end PositivityTheory.Xgn.QuotientUniformizationLower

theorem PositivityTheory.Xgn.quotient_uniformization_lower : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) (C : Flat.BdryChart Xo σ n a) (X : Scheme.{0}) (t : SAB H X) (jj : Sp C.R ⟶ X) (m : SABMap C.t t jj) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) (J : K → Type) (y : (Σ k, J k) → Ω) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel t.G ξ Li) (h : LieMetric M y) (N : ℕ) (s : Fin N → Li) (sc : Fin N → Fin C.g → C.R) (ww : (Fin n → ℂ) → (Σ k, J k) → ℂ), ContinuousOn ww (ball 0 1) → (∀ u ∈ ball (0 : Fin n → ℂ) 1, ∃ Mz : LieModel C.t.G (spMap (C.ψ u)) (Fin C.g → ℂ), ∀ e : Fin C.g → C.R, ((Mz.pt fun i => C.ψ u (e i)).left ≫ (𝟙 _) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.ψ u)) ≫ (C.M.pt e).left)) → (∀ u ∈ ball (0 : Fin n → ℂ) 1, CoordsAt ξ y (spMap (C.ψ u) ≫ jj) (ww u)) → (∀ u ∈ ball (0 : Fin n → ℂ) 1, ∀ i, ∃ v : epsAt (spMap (C.ψ u) ≫ jj) ⟶ t.G, M.ValAt (spMap (C.ψ u) ≫ jj) (s i) v ∧ v.left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.ψ u)) ≫ (C.M.pt (sc i)).left ≫ m.φ) → (∀ (V : Type) [AddCommGroup V] [Module ℂ V] (Mz : LieModel t.G (spMap (C.ψ 0) ≫ jj) V) (b : Fin N → V), (∀ i, M.ValAt (spMap (C.ψ 0) ≫ jj) (s i) (Mz.pt (b i))) → LinearIndependent ℂ b ∧ Submodule.span ℂ (Set.range b) = ⊤) → ∃ ρ Kc : ℝ, 0 < ρ ∧ 0 < Kc ∧ ∀ u ∈ ball (0 : Fin n → ℂ) ρ, ∀ Mz : LieModel C.t.G (spMap (C.ψ u)) (Fin C.g → ℂ), (∀ e : Fin C.g → C.R, ((Mz.pt fun i => C.ψ u (e i)).left ≫ (𝟙 _) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.ψ u)) ≫ (C.M.pt e).left)) → ∀ (x : Fin C.g → ℂ) (v₀ : epsAt (spMap (C.ψ u) ≫ jj) ⟶ t.G), (Mz.pt x).left ≫ m.φ = v₀.left → ∑ i, ‖x i‖ ^ 2 ≤ Kc * (h.ip (spMap (C.ψ u) ≫ jj) v₀ v₀).re := by
  intro E _ _ _ H D l Xo σ n a C X t jj m Ω _ ξ K J y Li _ _ M h N s sc ww hww hMz hco hval hbasis
  classical
  have hcart : IsGrpPullback C.t.G t.G jj m.φ := m.cart
  have hpull : ∀ (u : Fin n → ℂ) (Mz : LieModel C.t.G (spMap (C.ψ u)) (Fin C.g → ℂ)),
      ∃ M' : LieModel t.G (spMap (C.ψ u) ≫ jj) (Fin C.g → ℂ),
        ∀ e, (Mz.pt e).left ≫ m.φ = (M'.pt e).left := fun u Mz =>
    (GlobalTheory.CompanionTheory.Ar.LiePull.lieModel_pullback _ _ _ _ jj m.φ hcart ℂ (spMap (C.ψ u)) (Fin C.g → ℂ)).2 Mz
  let b : (Fin n → ℂ) → Fin N → Fin C.g → ℂ := fun u i k => C.ψ u (sc i k)
  let vv : ∀ u, u ∈ ball (0 : Fin n → ℂ) 1 → Fin N → (epsAt (spMap (C.ψ u) ≫ jj) ⟶ t.G) :=
    fun u hu i => Classical.choose (hval u hu i)
  have hvv : ∀ u hu i, M.ValAt (spMap (C.ψ u) ≫ jj) (s i) (vv u hu i) ∧
      (vv u hu i).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.ψ u)) ≫ (C.M.pt (sc i)).left ≫ m.φ :=
    fun u hu i => Classical.choose_spec (hval u hu i)
  let Γ : (Fin n → ℂ) → Matrix (Fin N) (Fin N) ℂ := fun u i j =>
    if hu : u ∈ ball (0 : Fin n → ℂ) 1 then h.ip _ (vv u hu i) (vv u hu j) else 0
  have hkey : ∀ u (hu : u ∈ ball (0 : Fin n → ℂ) 1)
      (Mz : LieModel C.t.G (spMap (C.ψ u)) (Fin C.g → ℂ)),
      (∀ e : Fin C.g → C.R, ((Mz.pt fun i => C.ψ u (e i)).left ≫ (𝟙 _) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.ψ u)) ≫ (C.M.pt e).left)) →
      ∀ M' : LieModel t.G (spMap (C.ψ u) ≫ jj) (Fin C.g → ℂ),
      (∀ e, (Mz.pt e).left ≫ m.φ = (M'.pt e).left) → ∀ i, M'.pt (b u i) = vv u hu i := by
    intro u hu Mz hl M' hM' i
    apply Over.OverMorphism.ext
    rw [← hM', (hvv u hu i).2]
    have hli := hl (sc i)
    change _ ≫ _ = _ ≫ _ at hli
    rw [Category.comp_id] at hli
    show (Mz.pt (fun k => C.ψ u (sc i k))).left ≫ m.φ = _
    rw [hli, Category.assoc]
  have hcore : ∀ u (hu : u ∈ ball (0 : Fin n → ℂ) 1)
      (Mz : LieModel C.t.G (spMap (C.ψ u)) (Fin C.g → ℂ)),
      (∀ e : Fin C.g → C.R, ((Mz.pt fun i => C.ψ u (e i)).left ≫ (𝟙 _) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.ψ u)) ≫ (C.M.pt e).left)) →
      ∃ core : InnerProductSpace.Core ℂ (Fin C.g → ℂ),
        (∀ i j, Γ u i j = core.inner (b u i) (b u j)) ∧
        ∀ (x : Fin C.g → ℂ) (v₀ : epsAt (spMap (C.ψ u) ≫ jj) ⟶ t.G),
          (Mz.pt x).left ≫ m.φ = v₀.left → h.ip _ v₀ v₀ = core.inner x x := by
    intro u hu Mz hl
    obtain ⟨M', hM'⟩ := hpull u Mz
    obtain ⟨core, hcoreip⟩ := h.herm _ (Fin C.g → ℂ) M'
    refine ⟨core, fun i j => ?_, fun x v₀ hx => ?_⟩
    · simp only [Γ, dif_pos hu]
      rw [hcoreip, hkey u hu Mz hl M' hM' i, hkey u hu Mz hl M' hM' j]
    · have hpt : M'.pt x = v₀ := Over.OverMorphism.ext (by rw [← hM']; exact hx)
      rw [hcoreip, hpt]
  have hΓc : ∀ i j, ContinuousOn (fun u => Γ u i j) (ball 0 1) := by
    intro i j
    obtain ⟨F, hF, hFeq⟩ := h.cont (s i) (s j)
    have heq : ∀ u ∈ ball (0 : Fin n → ℂ) 1, F (ww u) = Γ u i j := by
      intro u hu
      simp only [Γ, dif_pos hu]
      exact hFeq _ (ww u) _ _ (hco u hu) (hvv u hu i).1 (hvv u hu j).1
    refine ContinuousOn.congr (hF.comp hww ?_) (fun u hu => (heq u hu).symm)
    intro u hu
    exact ⟨_, vv u hu i, vv u hu j, hco u hu, (hvv u hu i).1, (hvv u hu j).1⟩
  have hbc : ∀ i k, ContinuousOn (fun u => b u i k) (ball 0 1) := fun i k =>
    (C.hol.2 (sc i k)).continuousOn
  have h01 : (0 : Fin n → ℂ) ∈ ball (0 : Fin n → ℂ) 1 := mem_ball_self one_pos
  obtain ⟨Mz0, hMz0⟩ := hMz 0 h01
  obtain ⟨M0', hM0'⟩ := hpull 0 Mz0
  have h0 : LinearIndependent ℂ (b 0) ∧ Submodule.span ℂ (Set.range (b 0)) = ⊤ :=
    hbasis (Fin C.g → ℂ) M0' (b 0) (fun i => by
      rw [hkey 0 h01 Mz0 hMz0 M0' hM0' i]
      exact (hvv 0 h01 i).1)
  obtain ⟨ρ, Kc, hρ, hρ1, hKc, hbound⟩ :=
    PositivityTheory.Xgn.QuotientUniformizationLower.analytic (0 : Fin n → ℂ) b hbc Γ hΓc
      (fun u hu => by
        obtain ⟨Mz, hl⟩ := hMz u hu
        obtain ⟨core, hc1, -⟩ := hcore u hu Mz hl
        exact ⟨core, hc1⟩) h0
  refine ⟨ρ, Kc, hρ, hKc, fun u hu Mz hl x v₀ hx => ?_⟩
  have hu1 : u ∈ ball (0 : Fin n → ℂ) 1 := ball_subset_ball hρ1 hu
  obtain ⟨core, hc1, hc2⟩ := hcore u hu1 Mz hl
  rw [hc2 x v₀ hx]
  exact hbound u hu core hc1 x
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeComponentHolomorphicCover
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeComponentHolomorphicCover
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.QuotUnif Metric

namespace GlobalTheory.CompanionTheory.Ar.QuotUnif

theorem exists_chart_at_of_polydisc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (n a : ℕ) (w : (Fin n → ℂ) → (Σ k, J k) → ℂ) (N : ℕ) (s : Fin N → 𝔐.Li) (z₀ : Sp ℂ ⟶ 𝔐.X), a ≤ n → DifferentiableOn ℂ w (ball 0 1) → (∀ u ∈ ball (0 : Fin n → ℂ) 1, w u ∈ mcPts (mCoordIdeal y)) → (∀ u ∈ Flat.punct n a 1, ∀ z : Sp ℂ ⟶ 𝔐.X, CoordsAt 𝔐.ξ y z (w u) → 𝔐.Interior z) → CoordsAt 𝔐.ξ y z₀ (w 0) → (∀ i, ∃ v : epsAt z₀ ⟶ 𝔐.t.G, 𝔐.M.ValAt z₀ (s i) v) → ∃ (ρ : ℝ) (τ : c.F →+* ℂ) (C : Flat.BdryChart Xo (τ.comp (IntermediateField.inclusion c.le).toRingHom) n a) (jj : Sp C.R ⟶ 𝔐.X) (m : SABMap C.t 𝔐.t jj) (sc : Fin N → Fin C.g → C.R), 0 < ρ ∧ ρ ≤ 1 ∧ ∀ u ∈ ball (0 : Fin n → ℂ) 1, CoordsAt 𝔐.ξ y (spMap (C.ψ u) ≫ jj) (w ((ρ : ℂ) • u)) ∧ spMap (C.ψ u) ≫ jj ≫ 𝔐.f ≫ Y.s = spMap (τ.comp (algebraMap (𝓞 c.F) c.F)) ∧ ∀ i, ∃ v : epsAt (spMap (C.ψ u) ≫ jj) ⟶ 𝔐.t.G, 𝔐.M.ValAt (spMap (C.ψ u) ≫ jj) (s i) v ∧ v.left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.ψ u)) ≫ (C.M.pt (sc i)).left ≫ m.φ := by
  exact @PositivityTheory.Xgn.quotient_uniformization_chart_at

end GlobalTheory.CompanionTheory.Ar.QuotUnif
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeComponentHolomorphicCoverStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.QuotUnif Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_component_holomorphic_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (n a : ℕ) (w : (Fin n → ℂ) → (Σ k, J k) → ℂ) (N : ℕ) (s : Fin N → 𝔐.Li) (z₀ : Sp ℂ ⟶ 𝔐.X), a ≤ n → DifferentiableOn ℂ w (ball 0 1) → (∀ u ∈ ball (0 : Fin n → ℂ) 1, w u ∈ mcPts (mCoordIdeal y)) → (∀ u ∈ Flat.punct n a 1, ∀ z : Sp ℂ ⟶ 𝔐.X, CoordsAt 𝔐.ξ y z (w u) → 𝔐.Interior z) → CoordsAt 𝔐.ξ y z₀ (w 0) → (∀ i, ∃ v : epsAt z₀ ⟶ 𝔐.t.G, 𝔐.M.ValAt z₀ (s i) v) → ∃ (ρ : ℝ) (τ : c.F →+* ℂ) (C : Flat.BdryChart Xo (τ.comp (IntermediateField.inclusion c.le).toRingHom) n a) (jj : Sp C.R ⟶ 𝔐.X) (m : SABMap C.t 𝔐.t jj) (sc : Fin N → Fin C.g → C.R), 0 < ρ ∧ ρ ≤ 1 ∧ ∀ u ∈ ball (0 : Fin n → ℂ) 1, CoordsAt 𝔐.ξ y (spMap (C.ψ u) ≫ jj) (w ((ρ : ℂ) • u)) ∧ spMap (C.ψ u) ≫ jj ≫ 𝔐.f ≫ Y.s = spMap (τ.comp (algebraMap (𝓞 c.F) c.F)) ∧ ∀ i, ∃ v : epsAt (spMap (C.ψ u) ≫ jj) ⟶ 𝔐.t.G, 𝔐.M.ValAt (spMap (C.ψ u) ≫ jj) (s i) v ∧ v.left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.ψ u)) ≫ (C.M.pt (sc i)).left ≫ m.φ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.QuotUnif.exists_chart_at_of_polydisc | exact GlobalTheory.CompanionTheory.Ar.QuotUnif.exists_chart_at_of_polydisc | (intros; apply GlobalTheory.CompanionTheory.Ar.QuotUnif.exists_chart_at_of_polydisc <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianBoundConjugate
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianBoundConjugate
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.QuotUnif Metric

namespace GlobalTheory.CompanionTheory.Ar.QuotUnif

theorem abBound_of_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel t.G ξ Li) (K : Type) (J : K → Type) (y : (Σ k, J k) → Ω) (h : LieMetric M y) (C : ℝ) (z : Sp ℂ ⟶ X), AbBound t h C (spMap (starRingEnd ℂ) ≫ z) → AbBound t h C z := by
  exact @PositivityTheory.Xgn.height_bound_complex_conjugate

end GlobalTheory.CompanionTheory.Ar.QuotUnif
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianBoundConjugateStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.QuotUnif Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_bound_conjugate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel t.G ξ Li) (K : Type) (J : K → Type) (y : (Σ k, J k) → Ω) (h : LieMetric M y) (C : ℝ) (z : Sp ℂ ⟶ X), AbBound t h C (spMap (starRingEnd ℂ) ≫ z) → AbBound t h C z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.QuotUnif.abBound_of_conj | exact GlobalTheory.CompanionTheory.Ar.QuotUnif.abBound_of_conj | (intros; apply GlobalTheory.CompanionTheory.Ar.QuotUnif.abBound_of_conj <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeComponentFiniteCharts
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeComponentFiniteCharts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.QuotUnif Metric

namespace GlobalTheory.CompanionTheory.Ar.QuotUnif.Charts

theorem exists_halfPolydisc_cover : Geo.ResK.ResKStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y), ∃ (n nc : ℕ) (w : Fin nc → (Fin n → ℂ) → (Σ k, J k) → ℂ) (a : Fin nc → ℕ), (∀ i, a i ≤ n) ∧ (∀ i, AnalyticOnNhd ℂ (w i) (ball 0 1)) ∧ (∀ i, ∀ t ∈ ball (0 : Fin n → ℂ) 1, w i t ∈ mcPts (mCoordIdeal y)) ∧ (∀ i, ∀ t ∈ ball (0 : Fin n → ℂ) 1, (∀ j : Fin n, (j : ℕ) < a i → t j ≠ 0) → ∀ z : Sp ℂ ⟶ 𝔐.X, CoordsAt 𝔐.ξ y z (w i t) → 𝔐.Interior z) ∧ ∀ x ∈ mcPts (mCoordIdeal y), ∃ (i : Fin nc) (t : Fin n → ℂ) (b : K → ℂ), ‖t‖ ≤ 1 / 2 ∧ (∀ k, b k ≠ 0) ∧ x = GroundTheory.Heights₂.Heights.LowerBoundFree.torusSmul b (w i t) :=
  PositivityTheory.Xgn.quotient_uniformization_charts

end GlobalTheory.CompanionTheory.Ar.QuotUnif.Charts
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeComponentFiniteChartsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.QuotUnif Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_component_finite_charts : Geo.ResK.ResKStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y), ∃ (n nc : ℕ) (w : Fin nc → (Fin n → ℂ) → (Σ k, J k) → ℂ) (a : Fin nc → ℕ), (∀ i, a i ≤ n) ∧ (∀ i, AnalyticOnNhd ℂ (w i) (ball 0 1)) ∧ (∀ i, ∀ t ∈ ball (0 : Fin n → ℂ) 1, w i t ∈ mcPts (mCoordIdeal y)) ∧ (∀ i, ∀ t ∈ ball (0 : Fin n → ℂ) 1, (∀ j : Fin n, (j : ℕ) < a i → t j ≠ 0) → ∀ z : Sp ℂ ⟶ 𝔐.X, CoordsAt 𝔐.ξ y z (w i t) → 𝔐.Interior z) ∧ ∀ x ∈ mcPts (mCoordIdeal y), ∃ (i : Fin nc) (t : Fin n → ℂ) (b : K → ℂ), ‖t‖ ≤ 1 / 2 ∧ (∀ k, b k ≠ 0) ∧ x = GroundTheory.Heights₂.Heights.LowerBoundFree.torusSmul b (w i t) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.QuotUnif.Charts.exists_halfPolydisc_cover | exact GlobalTheory.CompanionTheory.Ar.QuotUnif.Charts.exists_halfPolydisc_cover | (intros; apply GlobalTheory.CompanionTheory.Ar.QuotUnif.Charts.exists_halfPolydisc_cover <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFiniteGeneratingValues
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFiniteGeneratingValues
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.QuotUnif Metric

namespace GlobalTheory.CompanionTheory.Ar.QuotUnif


set_option backward.isDefEq.respectTransparency false in
theorem lie_frame_values_basis : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (z₀ : Sp ℂ ⟶ X), IsCptGen ξ → genPt ξ ⤳ centre z₀ → ∃ (N : ℕ) (s : Fin N → Li), (∀ i, ∃ v : epsAt z₀ ⟶ G, M.ValAt z₀ (s i) v) ∧ ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (Mz : LieModel G z₀ V) (b : Fin N → V), (∀ i, M.ValAt z₀ (s i) (Mz.pt (b i))) → LinearIndependent ℂ b ∧ Submodule.span ℂ (Set.range b) = ⊤ := by
  intro X Ω _ ξ G _ _ _ Li _ _ M z₀ hξ h
  obtain ⟨R, _, x, hx, F, _, _, MR, n, b₀, hp⟩ := LieVB.exists_chart G (centre z₀)
  have hq' : (X.fromSpecStalk (centre z₀)) (IsLocalRing.closedPoint (X.presheaf.stalk (centre z₀))) ∈
      x.opensRange := by
    rw [Scheme.fromSpecStalk_closedPoint]
    exact hp
  obtain ⟨ψ, hψ⟩ := LieVB.exists_lift (A := X.presheaf.stalk (centre z₀)) x (X.fromSpecStalk (centre z₀)) hq'
  obtain ⟨EA, _, _, ⟨MA⟩⟩ := lieModel_exists X G (X.presheaf.stalk (centre z₀)) (X.fromSpecStalk (centre z₀))
  obtain ⟨-, BA, -, -⟩ := LieVB.basis_tr (A := X.presheaf.stalk (centre z₀)) ψ x (X.fromSpecStalk (centre z₀))
    hψ MR MA b₀
  obtain ⟨i, hi⟩ := LieVB.exists_tr (A := X.presheaf.stalk (centre z₀)) (X.fromSpecStalk (centre z₀)) ξ
    (genMap ξ ⟨centre z₀, h⟩) (LieTangent.spec_genMap ξ ⟨centre z₀, h⟩) MA M
  have hext : ∀ a, M.Extends ⟨centre z₀, h⟩ (i a) (MA.pt a) := fun a => ⟨MA.tan a, hi a⟩
  refine ⟨n, fun k => i (BA k), fun k => ?_, fun V _ _ Mz b hb => ?_⟩
  · obtain ⟨E₀, _, _, ⟨M₀⟩⟩ := lieModel_exists X G ℂ z₀
    obtain ⟨j, hj⟩ := LieVB.exists_tr (A := X.presheaf.stalk (centre z₀)) (X.fromSpecStalk (centre z₀)) z₀
      (Scheme.stalkClosedPointTo z₀).hom (LieTangent.spec_centre z₀) MA M₀
    exact ⟨M₀.pt (j (BA k)), h, _, hext _, hj _⟩
  · obtain ⟨β, B, hB, hβ⟩ := LieVB.basis_tr (R := X.presheaf.stalk (centre z₀))
      (Scheme.stalkClosedPointTo z₀).hom (X.fromSpecStalk (centre z₀)) z₀ (LieTangent.spec_centre z₀) MA Mz BA
    have hbB : b = B := by
      funext k
      obtain ⟨_, v, hv, hw⟩ := hb k
      have hva : MA.pt (BA k) = v := (hext (BA k)).unique (hξ.inj _) hv
      subst hva
      rw [hB]
      exact LieVB.pt_left_inj Mz (hw.trans (hβ _).symm)
    rw [hbB]
    exact ⟨B.linearIndependent, B.span_eq⟩

end GlobalTheory.CompanionTheory.Ar.QuotUnif
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFiniteGeneratingValuesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.QuotUnif Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_model_finite_generating_values : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (z₀ : Sp ℂ ⟶ X), IsCptGen ξ → genPt ξ ⤳ centre z₀ → ∃ (N : ℕ) (s : Fin N → Li), (∀ i, ∃ v : epsAt z₀ ⟶ G, M.ValAt z₀ (s i) v) ∧ ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (Mz : LieModel G z₀ V) (b : Fin N → V), (∀ i, M.ValAt z₀ (s i) (Mz.pt (b i))) → LinearIndependent ℂ b ∧ Submodule.span ℂ (Set.range b) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.QuotUnif.lie_frame_values_basis | exact GlobalTheory.CompanionTheory.Ar.QuotUnif.lie_frame_values_basis | (intros; apply GlobalTheory.CompanionTheory.Ar.QuotUnif.lie_frame_values_basis <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryChartLieMetricBound
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryChartLieMetricBound
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.QuotUnif Metric

-- Some dependency stubs refer to this doubly qualified name when unfolding `LieModel.Lifts`.
-- Keep it definitionally equal to the actual map.
abbrev GlobalTheory.CompanionTheory.Ar.GlobalTheory.CompanionTheory.Ar.dualMap
    {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') :
    DualNumber R →+* DualNumber R' :=
  _root_.GlobalTheory.CompanionTheory.Ar.dualMap φ

theorem GlobalTheory.CompanionTheory.Ar.QuotUnif.chart_coords_le_metric : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) (C : Flat.BdryChart Xo σ n a) (X : Scheme.{0}) (t : SAB H X) (jj : Sp C.R ⟶ X) (m : SABMap C.t t jj) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) (J : K → Type) (y : (Σ k, J k) → Ω) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel t.G ξ Li) (h : LieMetric M y) (N : ℕ) (s : Fin N → Li) (sc : Fin N → Fin C.g → C.R) (ww : (Fin n → ℂ) → (Σ k, J k) → ℂ), ContinuousOn ww (ball 0 1) → (∀ u ∈ ball (0 : Fin n → ℂ) 1, ∃ Mz : LieModel C.t.G (spMap (C.ψ u)) (Fin C.g → ℂ), ∀ e : Fin C.g → C.R, ((Mz.pt fun i => C.ψ u (e i)).left ≫ (𝟙 _) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.GlobalTheory.CompanionTheory.Ar.dualMap (C.ψ u)) ≫ (C.M.pt e).left)) → (∀ u ∈ ball (0 : Fin n → ℂ) 1, CoordsAt ξ y (spMap (C.ψ u) ≫ jj) (ww u)) → (∀ u ∈ ball (0 : Fin n → ℂ) 1, ∀ i, ∃ v : epsAt (spMap (C.ψ u) ≫ jj) ⟶ t.G, M.ValAt (spMap (C.ψ u) ≫ jj) (s i) v ∧ v.left = spMap (_root_.GlobalTheory.CompanionTheory.Ar.dualMap (C.ψ u)) ≫ (C.M.pt (sc i)).left ≫ m.φ) → (∀ (V : Type) [AddCommGroup V] [Module ℂ V] (Mz : LieModel t.G (spMap (C.ψ 0) ≫ jj) V) (b : Fin N → V), (∀ i, M.ValAt (spMap (C.ψ 0) ≫ jj) (s i) (Mz.pt (b i))) → LinearIndependent ℂ b ∧ Submodule.span ℂ (Set.range b) = ⊤) → ∃ ρ Kc : ℝ, 0 < ρ ∧ 0 < Kc ∧ ∀ u ∈ ball (0 : Fin n → ℂ) ρ, ∀ Mz : LieModel C.t.G (spMap (C.ψ u)) (Fin C.g → ℂ), (∀ e : Fin C.g → C.R, ((Mz.pt fun i => C.ψ u (e i)).left ≫ (𝟙 _) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.GlobalTheory.CompanionTheory.Ar.dualMap (C.ψ u)) ≫ (C.M.pt e).left)) → ∀ (x : Fin C.g → ℂ) (v₀ : epsAt (spMap (C.ψ u) ≫ jj) ⟶ t.G), (Mz.pt x).left ≫ m.φ = v₀.left → ∑ i, ‖x i‖ ^ 2 ≤ Kc * (h.ip (spMap (C.ψ u) ≫ jj) v₀ v₀).re :=
  @PositivityTheory.Xgn.quotient_uniformization_lower
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryChartLieMetricBoundStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.QuotUnif Metric

-- Older dependency stubs reference this name without exporting the alias.
set_option linter.dupNamespace false in
open Lean Elab Command in
run_cmd do
  let aliasName := `GlobalTheory.CompanionTheory.Ar.GlobalTheory.CompanionTheory.Ar.dualMap
  unless (← getEnv).contains aliasName do
    elabCommand (← `(command|
      abbrev $(mkIdent aliasName) {R R' : Type} [CommRing R] [CommRing R']
          (φ : R →+* R') : DualNumber R →+* DualNumber R' :=
        _root_.GlobalTheory.CompanionTheory.Ar.dualMap φ))

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundary_chart_lie_metric_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) (C : Flat.BdryChart Xo σ n a) (X : Scheme.{0}) (t : SAB H X) (jj : Sp C.R ⟶ X) (m : SABMap C.t t jj) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) (J : K → Type) (y : (Σ k, J k) → Ω) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel t.G ξ Li) (h : LieMetric M y) (N : ℕ) (s : Fin N → Li) (sc : Fin N → Fin C.g → C.R) (ww : (Fin n → ℂ) → (Σ k, J k) → ℂ), ContinuousOn ww (ball 0 1) → (∀ u ∈ ball (0 : Fin n → ℂ) 1, ∃ Mz : LieModel C.t.G (spMap (C.ψ u)) (Fin C.g → ℂ), ∀ e : Fin C.g → C.R, ((Mz.pt fun i => C.ψ u (e i)).left ≫ (𝟙 _) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.GlobalTheory.CompanionTheory.Ar.dualMap (C.ψ u)) ≫ (C.M.pt e).left)) → (∀ u ∈ ball (0 : Fin n → ℂ) 1, CoordsAt ξ y (spMap (C.ψ u) ≫ jj) (ww u)) → (∀ u ∈ ball (0 : Fin n → ℂ) 1, ∀ i, ∃ v : epsAt (spMap (C.ψ u) ≫ jj) ⟶ t.G, M.ValAt (spMap (C.ψ u) ≫ jj) (s i) v ∧ v.left = spMap (_root_.GlobalTheory.CompanionTheory.Ar.dualMap (C.ψ u)) ≫ (C.M.pt (sc i)).left ≫ m.φ) → (∀ (V : Type) [AddCommGroup V] [Module ℂ V] (Mz : LieModel t.G (spMap (C.ψ 0) ≫ jj) V) (b : Fin N → V), (∀ i, M.ValAt (spMap (C.ψ 0) ≫ jj) (s i) (Mz.pt (b i))) → LinearIndependent ℂ b ∧ Submodule.span ℂ (Set.range b) = ⊤) → ∃ ρ Kc : ℝ, 0 < ρ ∧ 0 < Kc ∧ ∀ u ∈ ball (0 : Fin n → ℂ) ρ, ∀ Mz : LieModel C.t.G (spMap (C.ψ u)) (Fin C.g → ℂ), (∀ e : Fin C.g → C.R, ((Mz.pt fun i => C.ψ u (e i)).left ≫ (𝟙 _) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.GlobalTheory.CompanionTheory.Ar.dualMap (C.ψ u)) ≫ (C.M.pt e).left)) → ∀ (x : Fin C.g → ℂ) (v₀ : epsAt (spMap (C.ψ u) ≫ jj) ⟶ t.G), (Mz.pt x).left ≫ m.φ = v₀.left → ∑ i, ‖x i‖ ^ 2 ≤ Kc * (h.ip (spMap (C.ψ u) ≫ jj) v₀ v₀).re := by
  exact @GlobalTheory.CompanionTheory.Ar.QuotUnif.chart_coords_le_metric
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GoodPointOrConjugate
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GoodPointOrConjugate
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.QuotUnif Metric

namespace GlobalTheory.CompanionTheory.Ar.QuotUnif.Dich

theorem ringOfIntegers_hom_injective {F : Type} [Field F] [NumberField F] (r : 𝓞 F →+* ℂ) :
    Function.Injective r := by
  rw [RingHom.injective_iff_ker_eq_bot]
  refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_
  rw [eq_bot_iff]
  intro n hn
  have h0 : r (algebraMap ℤ (𝓞 F) n) = 0 := hn
  have : (n : ℂ) = 0 := by simpa using h0
  simpa using this

theorem exists_extension_to_field {F : Type} [Field F] [NumberField F] (r : 𝓞 F →+* ℂ) :
    ∃ r' : F →+* ℂ, r'.comp (algebraMap (𝓞 F) F) = r :=
  ⟨IsFractionRing.lift (K := F) (ringOfIntegers_hom_injective r), RingHom.ext fun a => by
    simp only [RingHom.comp_apply]
    exact IsFractionRing.lift_algebraMap (K := F) (ringOfIntegers_hom_injective r) a⟩

theorem conj_eq_neg_of_sq_eq_neg_natCast {x : ℂ} {d : ℕ} (h : x ^ 2 = -(d : ℂ)) :
    starRingEnd ℂ x = -x := by
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [sq, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re,
    Complex.natCast_im, neg_zero] at hre him
  have h0 : x.re = 0 := by
    by_contra hne
    have : x.im = 0 := by
      have : x.re * x.im = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left hne
    rw [this] at hre
    nlinarith [mul_self_pos.2 hne]
  apply Complex.ext <;> simp [h0]

theorem goodPt_or_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (z : Sp ℂ ⟶ 𝔐.X), GoodPt 𝔐 z ∨ GoodPt 𝔐 (spMap (starRingEnd ℂ) ≫ z) := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J y 𝔐 z
  haveI : NumberField c.F := { to_charZero := inferInstance, to_finiteDimensional := c.fin }
  let r : 𝓞 c.F →+* ℂ := (Spec.preimage (z ≫ 𝔐.f ≫ Y.s)).hom
  have hr : z ≫ 𝔐.f ≫ Y.s = spMap r := by
    simp [r, spMap]
  obtain ⟨τ, hτ⟩ := exists_extension_to_field r
  have h1 := congrArg (τ.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ_sq
  have h2 : ((τ.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ) ^ 2 = H.rt0 ^ 2 := by
    rw [← map_pow, h1, H.sqrt_neg_disc_sq, map_neg, map_natCast]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h | h
  · exact Or.inl ⟨τ, by rw [hr, hτ], h⟩
  · refine Or.inr ⟨(starRingEnd ℂ).comp τ, ?_, ?_⟩
    · rw [Category.assoc, hr, ← hτ]
      simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, RingHom.comp_assoc]
    · rw [RingHom.comp_assoc, RingHom.comp_apply, h, map_neg,
        conj_eq_neg_of_sq_eq_neg_natCast H.sqrt_neg_disc_sq, neg_neg]

end GlobalTheory.CompanionTheory.Ar.QuotUnif.Dich
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GoodPointOrConjugateStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.QuotUnif Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_point_or_conjugate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (z : Sp ℂ ⟶ 𝔐.X), GoodPt 𝔐 z ∨ GoodPt 𝔐 (spMap (starRingEnd ℂ) ≫ z) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.QuotUnif.Dich.goodPt_or_conj | exact GlobalTheory.CompanionTheory.Ar.QuotUnif.Dich.goodPt_or_conj | (intros; apply GlobalTheory.CompanionTheory.Ar.QuotUnif.Dich.goodPt_or_conj <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieMetricHeightBound
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.QuotUnif
open _root_.Metric

theorem exists_recentre {n : ℕ} (a : ℕ) {t₀ : Fin n → ℂ} (ht₀ : t₀ ∈ ball (0 : Fin n → ℂ) 1) :
    ∃ (a₀ : ℕ) (π : Equiv.Perm (Fin n)) (ρ₀ : ℝ), a₀ ≤ n ∧ 0 < ρ₀ ∧ ρ₀ ≤ 1 ∧ ∀ u ∈ ball (0 : Fin n → ℂ) 1,
      HodgeMetric.recentre t₀ ρ₀ π u ∈ ball (0 : Fin n → ℂ) 1 ∧
      (u ∈ Flat.punct n a₀ 1 → ∀ j : Fin n, (j : ℕ) < a → HodgeMetric.recentre t₀ ρ₀ π u j ≠ 0) := by
  classical
  let A : Finset (Fin n) := Finset.univ.filter (fun i => (i : ℕ) < a ∧ t₀ i = 0)
  have hA : ∀ i, i ∈ A ↔ (i : ℕ) < a ∧ t₀ i = 0 := fun i => by simp [A]
  obtain ⟨π, hπ⟩ := ChartGeo.exists_perm_prefix A
  have e2 : ∀ᶠ t : Fin n → ℂ in 𝓝 t₀, ∀ i : Fin n, t₀ i ≠ 0 → t i ≠ 0 := by
    refine Filter.eventually_all.2 fun i => ?_
    by_cases hi : t₀ i = 0
    · exact Filter.Eventually.of_forall fun t h => absurd hi h
    · filter_upwards [(continuous_apply i).continuousAt.eventually_ne hi] with t ht _ using ht
  have e3 : ∀ᶠ t in 𝓝 t₀, t ∈ ball (0 : Fin n → ℂ) 1 := isOpen_ball.mem_nhds ht₀
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 (e2.and e3)
  have hle : A.card ≤ n := by simpa using A.card_le_univ
  refine ⟨A.card, π, min ε 1, hle, lt_min hε one_pos, min_le_right _ _, fun u hu => ?_⟩
  have hρ : 0 < min ε 1 := lt_min hε one_pos
  obtain ⟨hne, hb⟩ := hball _ (ChartGeo.recentre_mem_ball hρ (min_le_left _ _) π hu)
  refine ⟨hb, ?_⟩
  rintro ⟨-, hu'⟩ j hj h0
  have hρc : ((min ε 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  by_cases hti : t₀ j = 0
  · have hm : j ∈ A := (hA j).2 ⟨hj, hti⟩
    have := hu' (π j) ((hπ j).2 hm)
    rw [ChartGeo.recentre_apply, hti, zero_add] at h0
    exact (mul_ne_zero hρc this) h0
  · exact hne j hti h0

theorem exists_preimage {n : ℕ} {t₀ t : Fin n → ℂ} (π : Equiv.Perm (Fin n)) {ρ₀ ρ₁ r : ℝ} (h₀ : 0 < ρ₀) (h₁ : 0 < ρ₁)
    (hr : 0 < r) (ht : t ∈ ball t₀ (ρ₀ * ρ₁ * r)) :
    ∃ u ∈ ball (0 : Fin n → ℂ) r, HodgeMetric.recentre t₀ ρ₀ π ((ρ₁ : ℂ) • u) = t := by
  have hp : 0 < ρ₀ * ρ₁ := mul_pos h₀ h₁
  have hpc : ((ρ₀ : ℂ) * (ρ₁ : ℂ)) ≠ 0 := by
    have : ((ρ₀ * ρ₁ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
    simpa using this
  refine ⟨fun j => ((ρ₀ : ℂ) * ρ₁)⁻¹ * (t (π.symm j) - t₀ (π.symm j)), ?_, ?_⟩
  · rw [mem_ball_zero_iff, pi_norm_lt_iff hr]
    intro j
    have h1 : ‖t (π.symm j) - t₀ (π.symm j)‖ < ρ₀ * ρ₁ * r := by
      have := lt_of_le_of_lt (norm_le_pi_norm (t - t₀) (π.symm j)) (mem_ball_iff_norm.1 ht)
      simpa using this
    have h2 : ‖((ρ₀ : ℂ) * ρ₁)⁻¹‖ = (ρ₀ * ρ₁)⁻¹ := by
      rw [norm_inv, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg h₀.le,
        Real.norm_of_nonneg h₁.le]
    rw [norm_mul, h2, inv_mul_lt_iff₀ hp]
    exact h1
  · funext i
    rw [ChartGeo.recentre_apply]
    simp only [Pi.smul_apply, smul_eq_mul, Equiv.symm_apply_apply]
    have c0 : (ρ₀ : ℂ) ≠ 0 := by exact_mod_cast h₀.ne'
    have c1 : (ρ₁ : ℂ) ≠ 0 := by exact_mod_cast h₁.ne'
    field_simp
    ring

theorem smul_mem_ball {n : ℕ} {ρ : ℝ} (h0 : 0 < ρ) (h1 : ρ ≤ 1) {u : Fin n → ℂ}
    (hu : u ∈ ball (0 : Fin n → ℂ) 1) : (ρ : ℂ) • u ∈ ball (0 : Fin n → ℂ) 1 := by
  rw [mem_ball_zero_iff] at hu ⊢
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg h0.le]
  nlinarith [norm_nonneg u]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K]
  {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}

theorem exists_tan {S : Scheme.{0}} (t : SAB H S) (z : Sp ℂ ⟶ S) {tK : SAB H (Sp ℂ)} (mK : SABMap tK t z) {V : Type}
    [AddCommGroup V] [Module ℂ V] (Mz : LieModel t.G z V) (v : epsAt (𝟙 (Sp ℂ)) ⟶ tK.G) (hv : IsTanAt _ _ v) :
    ∃ x : V, v.left ≫ mK.φ = (Mz.pt x).left := by
  have key : ∀ (z' : Sp ℂ ⟶ S) (_ : 𝟙 (Sp ℂ) ≫ z = z') (Mz' : LieModel t.G z' V),
      ∃ x : V, v.left ≫ mK.φ = (Mz'.pt x).left := by
    rintro z' rfl Mz'
    obtain ⟨Mk, hMk⟩ := (LiePull.lieModel_pullback S (Sp ℂ) t.G tK.G z mK.φ mK.cart ℂ (𝟙 _) V).1 Mz'
    obtain ⟨x, rfl⟩ := Mk.onto v hv
    exact ⟨x, hMk x⟩
  exact key z (Category.id_comp z) Mz

theorem local_bound (𝔐 : HodgeCpt Y S y) (h : LieMetric 𝔐.M y) (hpq : 1 ≤ D.p + D.q) {n a : ℕ}
    (w : (Fin n → ℂ) → (Σ k, J k) → ℂ) (hw : AnalyticOnNhd ℂ w (ball 0 1))
    (hm : ∀ t ∈ ball (0 : Fin n → ℂ) 1, w t ∈ mcPts (mCoordIdeal y))
    (hi : ∀ t ∈ ball (0 : Fin n → ℂ) 1, (∀ j : Fin n, (j : ℕ) < a → t j ≠ 0) → ∀ z : Sp ℂ ⟶ 𝔐.X,
      CoordsAt 𝔐.ξ y z (w t) → 𝔐.Interior z) {t₀ : Fin n → ℂ} (ht₀ : t₀ ∈ ball (0 : Fin n → ℂ) 1) :
    ∃ ε Kc : ℝ, 0 < ε ∧ 1 ≤ Kc ∧ ∀ K', Kc ≤ K' → ∀ t ∈ ball t₀ ε, ∀ z : Sp ℂ ⟶ 𝔐.X, CoordsAt 𝔐.ξ y z (w t) →
      GoodPt 𝔐 z → AbBound 𝔐.t h K' z := by
  classical
  obtain ⟨a₀, π, ρ₀, ha₀, hρ₀, hρ₀', hrc⟩ := exists_recentre a ht₀
  set w' : (Fin n → ℂ) → (Σ k, J k) → ℂ := fun u => w (HodgeMetric.recentre t₀ ρ₀ π u) with hw'
  have hrd : Differentiable ℂ (HodgeMetric.recentre t₀ ρ₀ π) := by
    unfold HodgeMetric.recentre
    exact (differentiable_const _).add (differentiable_pi.2 fun i => by
      simpa using (differentiable_apply (π i) : Differentiable ℂ fun u : Fin n → ℂ => u (π i)).const_mul (ρ₀ : ℂ))
  have hw'd : DifferentiableOn ℂ w' (ball 0 1) :=
    hw.differentiableOn.comp hrd.differentiableOn fun u hu => (hrc u hu).1
  have hall := 𝔐.all
  have htie := 𝔐.tie
  obtain ⟨z₀, hz₀g, hz₀⟩ := (GlobalTheory.T.complex_points_iff_centres 𝔐.X Ω 𝔐.ξ K J y htie (w t₀)).1 (hm _ ht₀)
  haveI : Smooth 𝔐.t.G.hom := 𝔐.t.semi.smooth
  obtain ⟨N, s, hs, hfr⟩ := GlobalTheory.T.lie_model_finite_generating_values 𝔐.X Ω 𝔐.ξ 𝔐.t.G 𝔐.Li 𝔐.M z₀ htie.gen hz₀g
  have hw0 : w' 0 = w t₀ := by simp only [hw', HodgeMetric.recentre_zero]
  obtain ⟨ρ₁, τ, C, jj, m, sc, hρ₁, hρ₁', hC⟩ := GlobalTheory.T.hodge_component_holomorphic_cover E H D l Xo c Y S Ω K J y 𝔐 n a₀ w' N s z₀ ha₀ hw'd
    (fun u hu => hm _ (hrc u hu).1) (fun u hu z hz => hi _ (hrc u hu.1).1 ((hrc u hu.1).2 hu) z hz)
    (by rw [hw0]; exact hz₀) hs
  have huniq : ∀ (z z' : Sp ℂ ⟶ 𝔐.X) (w₁ : (Σ k, J k) → ℂ), CoordsAt 𝔐.ξ y z w₁ → CoordsAt 𝔐.ξ y z' w₁ → z = z' :=
    fun z z' w₁ h₁ h₂ => by
      obtain ⟨e1, -, e3⟩ := GlobalTheory.T.local_ring_points_existsUnique 𝔐.X Ω 𝔐.ξ K J y htie ℂ
      exact (e1 w₁ h₁.1 (e3 z w₁ (hall _) h₁).1).unique ⟨hall _, h₁⟩ ⟨hall _, h₂⟩
  have hsm : ∀ {r : ℝ}, r ≤ 1 → ∀ u ∈ ball (0 : Fin n → ℂ) r, u ∈ ball (0 : Fin n → ℂ) 1 := fun hr u hu =>
    ball_subset_ball hr hu
  have hpt : ∀ {r : ℝ}, 0 < r → r ≤ 1 → ∀ t ∈ ball t₀ (ρ₀ * ρ₁ * r), ∀ z : Sp ℂ ⟶ 𝔐.X, CoordsAt 𝔐.ξ y z (w t) →
      ∃ u ∈ ball (0 : Fin n → ℂ) r, z = spMap (C.ψ u) ≫ jj := fun {r} hr hr1 t ht z hz => by
    obtain ⟨u, hu, e⟩ := exists_preimage π hρ₀ hρ₁ hr ht
    refine ⟨u, hu, huniq _ _ (w t) hz ?_⟩
    have := (hC u (hsm hr1 u hu)).1
    simp only [hw', e] at this
    exact this
  by_cases hgood : (τ.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ = H.rt0
  · obtain ⟨ρ₂, K₂, hρ₂, hρ₂', hQ⟩ := GlobalTheory.T.principal_near_boundary E H D l Xo _ n a₀ C hpq hgood
    have hz0 : spMap (C.ψ 0) ≫ jj = z₀ :=
      huniq _ _ (w t₀) (by
        have := (hC 0 (by simp)).1
        rw [smul_zero, hw0] at this
        exact this) hz₀
    subst hz0
    have hcont : ContinuousOn (fun u : Fin n → ℂ => w' ((ρ₁ : ℂ) • u)) (ball 0 1) := by
      refine hw'd.continuousOn.comp (continuous_const_smul _).continuousOn fun u hu => ?_
      exact smul_mem_ball hρ₁ hρ₁' hu
    obtain ⟨ρ₃, K₃, hρ₃, hK₃, hL⟩ := GlobalTheory.T.boundary_chart_lie_metric_bound E H D l Xo _ n a₀ C 𝔐.X 𝔐.t jj m Ω 𝔐.ξ K J y 𝔐.Li 𝔐.M h N s sc _ hcont
      (fun u _ => GlobalTheory.T.boundary_chart_lie_model_exists E H D l Xo _ n a₀ C u) (fun u hu => (hC u hu).1) (fun u hu i => (hC u hu).2.2 i) hfr
    have hr : 0 < min 1 (min ρ₂ ρ₃) := lt_min one_pos (lt_min hρ₂ hρ₃)
    refine ⟨ρ₀ * ρ₁ * min 1 (min ρ₂ ρ₃), max 1 (|K₂| * K₃), mul_pos (mul_pos hρ₀ hρ₁) hr, le_max_left _ _,
      fun K' hK' t ht z hz _ => ?_⟩
    obtain ⟨u, hu, rfl⟩ := hpt hr (min_le_left _ _) t ht z hz
    have hu₂ : u ∈ ball (0 : Fin n → ℂ) ρ₂ :=
      ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) hu
    have hu₃ : u ∈ ball (0 : Fin n → ℂ) ρ₃ :=
      ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _)) hu
    intro P
    obtain ⟨mK, hmK⟩ := GlobalTheory.ObjMaps.exists_sab_cancel m P.m
    let P' : AbPart C.t (spMap (C.ψ u)) := ⟨P.tK, mK, P.τ, P.tB, P.e, P.e_hom, P.act, P.pp⟩
    obtain ⟨Mz, hMz⟩ := GlobalTheory.T.boundary_chart_lie_model_exists E H D l Xo _ n a₀ C u
    have hsingle : ∀ i, (Mz.pt (Pi.single i 1)).left ≫ (𝟙 _) = spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.ψ u)) ≫ (C.M.pt (Pi.single i 1)).left := fun i => by
      have := hMz (Pi.single i 1)
      have e : (fun j => C.ψ u ((Pi.single i 1 : Fin C.g → C.R) j)) = Pi.single i 1 := by
        funext j
        by_cases hj : j = i
        · subst hj; simp
        · simp [Pi.single_eq_of_ne hj]
      rwa [e] at this
    obtain ⟨hpr, hb⟩ := hQ u hu₂ P'
    refine ⟨hpr, fun v v₀ c' hv hvv hH => ?_⟩
    obtain ⟨x, hx⟩ := exists_tan C.t (spMap (C.ψ u)) mK Mz v hv
    have h1 : c'.re ≤ K₂ * ∑ i, ‖x i‖ ^ 2 := hb Mz hsingle x v c' hx hH
    have h2 : ∑ i, ‖x i‖ ^ 2 ≤ K₃ * (h.ip _ v₀ v₀).re := hL u hu₃ Mz hMz x v₀ (by
      rw [← hx, Category.assoc, ← hmK, hvv])
    have h3 : 0 ≤ ∑ i, ‖x i‖ ^ 2 := Finset.sum_nonneg fun i _ => by positivity
    have h4 : 0 ≤ (h.ip _ v₀ v₀).re := by
      by_contra hn
      push_neg at hn
      nlinarith
    calc c'.re ≤ K₂ * ∑ i, ‖x i‖ ^ 2 := h1
      _ ≤ |K₂| * ∑ i, ‖x i‖ ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self _) h3
      _ ≤ |K₂| * (K₃ * (h.ip _ v₀ v₀).re) := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
      _ = (|K₂| * K₃) * (h.ip _ v₀ v₀).re := by ring
      _ ≤ K' * (h.ip _ v₀ v₀).re := mul_le_mul_of_nonneg_right ((le_max_right _ _).trans hK') h4
  · refine ⟨ρ₀ * ρ₁ * 1, 1, mul_pos (mul_pos hρ₀ hρ₁) one_pos, le_rfl, fun K' _ t ht z hz hG => ?_⟩
    obtain ⟨u, hu, rfl⟩ := hpt one_pos le_rfl t ht z hz
    obtain ⟨τ', e1, e2⟩ := hG
    exfalso
    apply hgood
    haveI : FiniteDimensional ℚ c.F := c.fin
    haveI : NumberField c.F := ⟨⟩
    have e3 := (hC u hu).2.1
    rw [Category.assoc] at e1
    rw [e1] at e3
    have e4 : τ'.comp (algebraMap (𝓞 c.F) c.F) = τ.comp (algebraMap (𝓞 c.F) c.F) := by
      have := Spec.map_injective e3
      exact congrArg CommRingCat.Hom.hom this
    have e5 : τ' = τ := IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F)) e4
    rw [← e5]
    exact e2

end GlobalTheory.CompanionTheory.Ar.QuotUnif


open GlobalTheory.CompanionTheory.Ar.QuotUnif in
theorem GlobalTheory.CompanionTheory.Ar.QuotUnif.main : Geo.ResK.ResKStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (h : LieMetric 𝔐.M y), 1 ≤ D.p + D.q → ∃ K : ℝ, 1 ≤ K ∧ ∀ (z : Sp ℂ ⟶ 𝔐.X) (P : AbPart 𝔐.t z), IsPrincipal P.tB ∧ ∀ (v : epsAt (𝟙 (Sp ℂ)) ⟶ P.tK.G) (v₀ : epsAt z ⟶ 𝔐.t.G) (c : ℂ), IsTanAt _ _ v → v.left ≫ P.m.φ = v₀.left → HodgeIP P.tB.G P.tB.PP.L (𝟙 _) (v ≫ P.τ.q ≫ P.e.hom) (v ≫ P.τ.q ≫ P.e.hom) c → c.re ≤ K * (h.ip z v₀ v₀).re := by
  intro hR E _ _ _ H D l Xo c Y S Ω _ K _ J _ y 𝔐 h hpq
  obtain ⟨n, nc, w, a, -, hw, hm, hi, hcov⟩ := GlobalTheory.T.hodge_component_finite_charts hR E H D l Xo c Y S Ω K J y 𝔐
  have hcpt : ∀ i, ∃ Kc : ℝ, 1 ≤ Kc ∧ ∀ K', Kc ≤ K' → ∀ t ∈ Metric.closedBall (0 : Fin n → ℂ) (1 / 2),
      ∀ z : Sp ℂ ⟶ 𝔐.X, CoordsAt 𝔐.ξ y z (w i t) → GoodPt 𝔐 z → AbBound 𝔐.t h K' z := by
    intro i
    refine (isCompact_closedBall (0 : Fin n → ℂ) (1 / 2)).induction_on
      (p := fun A => ∃ Kc : ℝ, 1 ≤ Kc ∧ ∀ K', Kc ≤ K' → ∀ t ∈ A,
        ∀ z : Sp ℂ ⟶ 𝔐.X, CoordsAt 𝔐.ξ y z (w i t) → GoodPt 𝔐 z → AbBound 𝔐.t h K' z) ?_ ?_ ?_ ?_
    · exact ⟨1, le_rfl, fun _ _ t ht => absurd ht (Set.notMem_empty t)⟩
    · rintro A B hAB ⟨Kc, h1, h2⟩
      exact ⟨Kc, h1, fun K' hK t ht => h2 K' hK t (hAB ht)⟩
    · rintro A B ⟨K₁, h1, h2⟩ ⟨K₂, h3, h4⟩
      refine ⟨max K₁ K₂, h1.trans (le_max_left _ _), fun K' hK t ht => ?_⟩
      rcases ht with ht | ht
      · exact h2 K' ((le_max_left _ _).trans hK) t ht
      · exact h4 K' ((le_max_right _ _).trans hK) t ht
    · intro t₀ ht₀
      have ht₀' : t₀ ∈ Metric.ball (0 : Fin n → ℂ) 1 :=
        Metric.closedBall_subset_ball (by norm_num) ht₀
      obtain ⟨ε, Kc, hε, h1, h2⟩ := local_bound 𝔐 h hpq (a := a i) (w i) (hw i) (hm i) (hi i) ht₀'
      exact ⟨Metric.ball t₀ ε, mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds _ hε), Kc, h1, h2⟩
  choose Kf hKf1 hKf using hcpt
  have hle : ∀ i, Kf i ≤ 1 + ∑ j, Kf j := fun i => by
    have : Kf i ≤ ∑ j, Kf j :=
      Finset.single_le_sum (f := Kf) (fun j _ => by have := hKf1 j; linarith) (Finset.mem_univ i)
    linarith
  have hB : ∀ z : Sp ℂ ⟶ 𝔐.X, GoodPt 𝔐 z → AbBound 𝔐.t h (1 + ∑ j, Kf j) z := by
    intro z hz
    obtain ⟨-, e2, e3⟩ := GlobalTheory.T.local_ring_points_existsUnique 𝔐.X Ω 𝔐.ξ K J y 𝔐.tie ℂ
    obtain ⟨x, hx⟩ := e2 z (𝔐.all _)
    have hxm := (GlobalTheory.T.complex_points_iff_centres 𝔐.X Ω 𝔐.ξ K J y 𝔐.tie x).2 ⟨z, 𝔐.all _, hx⟩
    obtain ⟨i, t, b, ht, hb, rfl⟩ := hcov x hxm
    have hc : CoordsAt 𝔐.ξ y z (w i t) := by
      refine ((e3 z _ (𝔐.all _) hx).2 _).2 ⟨fun k => (Units.mk0 (b k) (hb k))⁻¹, ?_⟩
      funext p
      simp [GroundTheory.Heights₂.Heights.LowerBoundFree.torusSmul, hb p.1]
    exact hKf i _ (hle i) t (by simpa using ht) z hc hz
  have h1 : (1 : ℝ) ≤ 1 + ∑ j, Kf j := by
    have : 0 ≤ ∑ j, Kf j := Finset.sum_nonneg fun j _ => by have := hKf1 j; linarith
    linarith
  refine ⟨1 + ∑ j, Kf j, h1, fun z => ?_⟩
  rcases GlobalTheory.T.good_point_or_conjugate E H D l Xo c Y S Ω K J y 𝔐 z with hg | hg
  · exact hB z hg
  · exact GlobalTheory.T.abelian_bound_conjugate E H 𝔐.X 𝔐.t Ω 𝔐.ξ 𝔐.Li 𝔐.M K J y h _ z (hB _ hg)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieMetricHeightBoundStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_metric_height_bound : Geo.ResK.ResKStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (h : LieMetric 𝔐.M y), 1 ≤ D.p + D.q → ∃ K : ℝ, 1 ≤ K ∧ ∀ (z : Sp ℂ ⟶ 𝔐.X) (P : AbPart 𝔐.t z), IsPrincipal P.tB ∧ ∀ (v : epsAt (𝟙 (Sp ℂ)) ⟶ P.tK.G) (v₀ : epsAt z ⟶ 𝔐.t.G) (c : ℂ), IsTanAt _ _ v → v.left ≫ P.m.φ = v₀.left → HodgeIP P.tB.G P.tB.PP.L (𝟙 _) (v ≫ P.τ.q ≫ P.e.hom) (v ≫ P.τ.q ≫ P.e.hom) c → c.re ≤ K * (h.ip z v₀ v₀).re := by
  first | exact @GlobalTheory.CompanionTheory.Ar.QuotUnif.main | exact GlobalTheory.CompanionTheory.Ar.QuotUnif.main | (intros; apply GlobalTheory.CompanionTheory.Ar.QuotUnif.main <;> assumption)
end
