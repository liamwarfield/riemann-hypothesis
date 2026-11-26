module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLogPeriodFamily
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyExponentialConjugate

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjugateRootZeroThird
theorem UpperTheory.Reformulated.B.StarRingEndRootEqNeg.rt0_conj_neg_ne_zero :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : NumberField.IsCMField E]
      (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E), (starRingEnd ℂ : ℂ → ℂ) H.rt0 = -H.rt0 := by
  intro E _ _ _ H
  have hd : (0 : ℝ) < (H.d : ℝ) := by exact_mod_cast H.d_prime.pos
  have h := H.sqrt_neg_disc_sq
  have hre : H.rt0.re * H.rt0.re - H.rt0.im * H.rt0.im = -(H.d : ℝ) := by
    simpa [pow_two, Complex.mul_re] using congrArg Complex.re h
  have him : H.rt0.re * H.rt0.im + H.rt0.im * H.rt0.re = 0 := by
    simpa [pow_two, Complex.mul_im] using congrArg Complex.im h
  have ha : H.rt0.re = 0 := by
    by_contra ha
    have hm : H.rt0.re * H.rt0.im = 0 := by linarith
    have hb : H.rt0.im = 0 := (mul_eq_zero.mp hm).resolve_left ha
    rw [hb] at hre
    nlinarith [mul_self_nonneg H.rt0.re]
  apply Complex.ext
  · simp [ha]
  · simp
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeGramComplexConjugate
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeGramComplexConjugate
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.GramConj

open GlobalTheory.ArchMetricCompare (cj cjPt cjUnif cj_isAH cj_val isIso_of_cj carry carry_isAH)

attribute [local instance] Over.cartesianMonoidalCategory

theorem dualConj_dualConj :
    spMap (dualMap (starRingEnd ℂ)) ≫ spMap (dualMap (starRingEnd ℂ)) = 𝟙 (Sp (DualNumber ℂ)) := by
  have h : (dualMap (starRingEnd ℂ)).comp (dualMap (starRingEnd ℂ)) = RingHom.id (DualNumber ℂ) := by
    ext c <;> simp [dualMap]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, h]
  exact Spec.map_id _

theorem fderiv_conj {g : ℕ} (F : (Fin g → ℂ) → ℂ) (w : Fin g → ℂ) :
    fderiv ℂ (star ∘ F ∘ star) 0 (star w) = star (fderiv ℂ F 0 w) := by
  by_cases h : DifferentiableAt ℂ F 0
  · have d := h.hasFDerivAt.star_star
    rw [star_zero] at d
    rw [d.fderiv]
    simp
  · have h' : ¬ DifferentiableAt ℂ (star ∘ F ∘ star) 0 := fun h' => h (by
      have := h'.star_star
      have e : star ∘ (star ∘ F ∘ star) ∘ star = F := by
        ext z
        simp
      rw [star_zero, e] at this
      exact this)
    rw [fderiv_zero_of_not_differentiableAt h, fderiv_zero_of_not_differentiableAt h']
    simp

variable {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A'] {ψ : A'.left ⟶ A.left} {M : LB A.left} {M' : LB A'.left} {g : ℕ}

theorem isDiff_conj (h : IsGrpPullback A' A cj ψ) (u : HolUnif A M g) (u' : HolUnif A' M' g)
    (hex : ∀ z, u'.ex z = cjPt h (u.ex (star z))) {t : epsR ℂ ⟶ A} {t' : epsR ℂ ⟶ A'}
    (e : t'.left ≫ ψ = spMap (dualMap (starRingEnd ℂ)) ≫ t.left) {w : Fin g → ℂ} (hd : u.IsDiff w t) :
    u'.IsDiff (star w) t' := by
  haveI := isIso_of_cj h
  intro U hU f
  have e2 : t'.left = spMap (dualMap (starRingEnd ℂ)) ≫ (show Sp (DualNumber ℂ) ⟶ _ from t.left) ≫ inv ψ := by
    rw [← Category.assoc]
    exact (IsIso.eq_comp_inv ψ).2 e
  have e4 : (show Sp (DualNumber ℂ) ⟶ _ from t.left) ≫ inv ψ = spMap (dualMap (starRingEnd ℂ)) ≫ t'.left := by
    rw [e2, ← Category.assoc, dualConj_dualConj, Category.id_comp]
  have h2 : ⊤ ≤ t.left ⁻¹ᵁ (inv ψ ⁻¹ᵁ U) := fun p _ => by
    have q : ((show Sp (DualNumber ℂ) ⟶ _ from t.left) ≫ inv ψ) p ∈ U := by
      rw [e4]
      exact hU (show spMap (dualMap (starRingEnd ℂ)) p ∈ (⊤ : (Sp (DualNumber ℂ)).Opens) from trivial)
    exact q
  have e1 : (fun z => valAt' (u'.ex z).left U f) =
      star ∘ (fun z => valAt' (u.ex z).left (inv ψ ⁻¹ᵁ U) (((inv ψ).app U).hom f)) ∘ star :=
    funext fun z => by
      simp only [hex]
      exact cj_val h _ U f
  rw [e1, fderiv_conj]
  have k : ∀ (y : Sp (DualNumber ℂ) ⟶ A'.left) (hy : ⊤ ≤ y ⁻¹ᵁ U),
      y = spMap (dualMap (starRingEnd ℂ)) ≫ (show Sp (DualNumber ℂ) ⟶ _ from t.left) ≫ inv ψ →
      TangentOrigin.evalPt y U hy f = dualMap (starRingEnd ℂ)
        (TangentOrigin.evalPt (R := DualNumber ℂ) t.left _ h2 (((inv ψ).app U).hom f)) := by
    rintro _ hy rfl
    rw [TangentOrigin.evalPt_spMap_comp _ _ U h2]
    congr 1
  refine (congrArg TrivSqZeroExt.snd (k _ hU e2)).trans ?_
  have e3 := hd _ h2 (((inv ψ).app U).hom f)
  simp only [dualMap, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl,
    TrivSqZeroExt.snd_inr, zero_add]
  exact congrArg (starRingEnd ℂ) e3

theorem exists_conjUnif (h : IsGrpPullback A' A cj ψ) (hM : M.IsLB) (u : HolUnif A M g)
    {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ} (hA : u.IsAH Hm χ) :
    ∃ (u' : HolUnif A' (M.pull ψ) g) (χ' : u'.Λ → ℂ), u'.IsAH (Hm.map star) χ' ∧
      ∀ z, u'.ex z = cjPt h (u.ex (star z)) := by
  have hM1 : (M.pull (𝟙 A.left)).IsLB := pull_isLB hM _
  obtain ⟨w, hw⟩ : LBIso M (M.pull (𝟙 A.left)) :=
    LBIso.chartPull (chartPullId M) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull M (𝟙 _) (𝟙 _) rfl) (PolBaseChange.lbIso_refl hM)
  have key : ∀ f, f = ψ ≫ 𝟙 A.left → ∃ (u' : HolUnif A' (M.pull f) g) (χ' : u'.Λ → ℂ),
      u'.IsAH (Hm.map star) χ' ∧ ∀ z, u'.ex z = cjPt h (u.ex (star z)) := by
    rintro _ rfl
    exact ⟨cjUnif h (carry u hM hM1 hw), _, cj_isAH h _ (carry_isAH hM hM1 hw hA), fun _ => rfl⟩
  exact key _ (Category.comp_id _).symm

theorem isHodgeGram_conj : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (x x' : Spec (CommRingCat.of ℂ) ⟶ S) (n : ℕ) (v : Fin n → (epsAt x ⟶ G)) (v' : Fin n → (epsAt x' ⟶ G)) (Γ : Matrix (Fin n) (Fin n) ℂ), x' = spMap (starRingEnd ℂ) ≫ x → (∀ i, (v' i).left = spMap (dualMap (starRingEnd ℂ)) ≫ (v i).left) → Fl.IsHodgeGram G L x v Γ → Fl.IsHodgeGram G L x' v' (Γ.map (starRingEnd ℂ)) := by
  rintro S G _ L x x' n v v' Γ rfl hv' ⟨Q, ψ, vo, u, Hm, χ, W, hP, hLB, hAH, hvo, hΓ⟩
  have hc := isGrpPullback_pullback Q.A cj
  haveI := (Out.TLinPf.isAb_pullback cj Q.A Q.isAb).comm
  obtain ⟨u', χ', hAH', hex⟩ := exists_conjUnif hc Q.isLB u hAH
  have sq : ∀ i, (spMap (dualMap (starRingEnd ℂ)) ≫ (vo i).left) ≫ Q.A.hom = (epsR ℂ).hom ≫ cj := fun i => by
    rw [Category.assoc, Over.w]
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  let t : ∀ i, epsR ℂ ⟶ (Over.pullback cj).obj Q.A := fun i => Over.homMk (hc.1.lift _ _ (sq i)) (hc.1.lift_snd _ _ _)
  have et : ∀ i, (t i).left ≫ pullback.fst Q.A.hom cj = spMap (dualMap (starRingEnd ℂ)) ≫ (vo i).left :=
    fun i => hc.1.lift_fst _ _ _
  refine ⟨GlobalTheory.TorsionTauCompare.polOfPullback Q _ hc, pullback.fst Q.A.hom cj ≫ ψ, t, u', Hm.map star, χ',
    fun i => star (W i), hc.comp hP, ?_, hAH', fun i => ⟨?_, isDiff_conj hc u u' hex (et i) (hvo i).2⟩, fun i j => ?_⟩
  · exact LBIso.symm (Cusp.FibreMove.lbIso_pull (LBIso.symm hLB) _)
  · exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ ψ) (et i))).trans
      (((Category.assoc _ _ _).trans (congrArg _ (hvo i).1)).trans (hv' i).symm)
  · rw [Matrix.map_apply, hΓ, map_mul, Complex.conj_ofReal]
    congr 1
    refine Eq.trans ?_ (GlobalTheory.ArchMetricCompare.star_form Hm (star (W i)) (star (W j)))
    rw [star_star (W i), star_star (W j)]
    rfl

end GlobalTheory.CompanionTheory.Ar.GramConj
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeGramComplexConjugateStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_gram_complex_conjugate : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (x x' : Spec (CommRingCat.of ℂ) ⟶ S) (n : ℕ) (v : Fin n → (epsAt x ⟶ G)) (v' : Fin n → (epsAt x' ⟶ G)) (Γ : Matrix (Fin n) (Fin n) ℂ), x' = spMap (starRingEnd ℂ) ≫ x → (∀ i, (v' i).left = spMap (dualMap (starRingEnd ℂ)) ≫ (v i).left) → Fl.IsHodgeGram G L x v Γ → Fl.IsHodgeGram G L x' v' (Γ.map (starRingEnd ℂ)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GramConj.isHodgeGram_conj | exact GlobalTheory.CompanionTheory.Ar.GramConj.isHodgeGram_conj | (intros; apply GlobalTheory.CompanionTheory.Ar.GramConj.isHodgeGram_conj <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodsConjugateExists
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodsConjugateExists
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.LogPer

open GroundTheory.Heights₂.Heights.Regular

variable {n a g : ℕ} {Λ : Type} [AddCommGroup Λ]

theorem add_single_mem_logCover (h : a ≤ n) {w : Fin n → ℂ} (hw : w ∈ logCover h) (i : Fin a) :
    w + Pi.single (Fin.castLE h i) (2 * Real.pi * Complex.I) ∈ logCover h := by
  refine ⟨fun j => ?_, fun k hk => ?_⟩
  · by_cases hj : Fin.castLE h j = Fin.castLE h i
    · simpa [hj, Pi.single_apply] using (by simpa [hj] using hw.1 j)
    · simpa [Pi.single_apply, hj] using hw.1 j
  · have hki : k ≠ Fin.castLE h i := by
      rintro rfl
      simp at hk
      omega
    simpa [Pi.single_apply, hki] using hw.2 k hk

theorem expCover_add_single (h : a ≤ n) (w : Fin n → ℂ) (i : Fin a) :
    expCover a (w + Pi.single (Fin.castLE h i) (2 * Real.pi * Complex.I)) = expCover a w := by
  funext k
  by_cases hk : k = Fin.castLE h i
  · subst hk
    have hi : (Fin.castLE h i).val < a := i.2
    simp only [expCover, Pi.add_apply, Pi.single_eq_same, if_pos hi, Complex.exp_add,
      Complex.exp_two_pi_mul_I]
    exact mul_one _
  · simp [expCover, Pi.single_apply, hk]

theorem exists_mem_logCover (h : a ≤ n) : ∃ w : Fin n → ℂ, w ∈ logCover h := by
  refine ⟨fun k => if k.val < a then -1 else 0, fun i => ?_, fun k hk => ?_⟩
  · have hi : (Fin.castLE h i).val < a := i.2
    simp only [if_pos hi]
    simp
  · simp [not_lt.2 hk]

theorem monodromy_preserves_form (L : Flat.LogPeriods n a g Λ) (i : Fin a) (x y : Λ) :
    L.E (L.T i x) (L.T i y) = L.E x y := by
  obtain ⟨w, hw⟩ := exists_mem_logCover L.a_le
  have h1 := L.im _ (add_single_mem_logCover L.a_le hw i) x y
  rw [L.mono i w hw, L.mono i w hw, expCover_add_single, L.im w hw] at h1
  exact_mod_cast h1

theorem T_bijective (L : Flat.LogPeriods n a g Λ) (i : Fin a) : Function.Bijective (L.T i) := by
  haveI := L.fin
  let e : Λ ≃ₗ[ℤ] Module.Dual ℤ Λ := LinearEquiv.ofBijective L.E L.unimod
  let S : Λ →ₗ[ℤ] Λ := e.symm.toLinearMap ∘ₗ (L.T i).dualMap ∘ₗ e.toLinearMap
  have hE : ∀ x y, L.E (S x) y = L.E x (L.T i y) := by
    intro x y
    have h1 : e (S x) = (L.T i).dualMap (e x) := by simp [S]
    exact congrArg (fun f : Module.Dual ℤ Λ => f y) h1
  have hST : ∀ x, S (L.T i x) = x := fun x =>
    L.unimod.1 (LinearMap.ext fun y => by rw [hE, monodromy_preserves_form])
  have hSs : Function.Surjective S := fun x => ⟨_, hST x⟩
  have hSi : Function.Injective S := OrzechProperty.injective_of_surjective_endomorphism S hSs
  exact ⟨fun x y h => by rw [← hST x, ← hST y, h], fun y => ⟨S y, hSi (hST (S y))⟩⟩

theorem exists_conj_logPeriods : ∀ (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] (L' : Flat.LogPeriods n a g Λ),
    ∃ L : Flat.LogPeriods n a g Λ, (∀ w x, L.P w x = star (L'.P (star w) x)) ∧
      ∀ z, L.H z = (L'.H (star z)).map (starRingEnd ℂ) := by
  intro n a g Λ _ L'
  exact ⟨ConjPeriods.conj L' (T_bijective L'), fun _ _ => rfl, fun _ => rfl⟩

end GlobalTheory.CompanionTheory.Ar.Flat.LogPer
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodsConjugateExistsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_periods_conjugate_exists : ∀ (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] (L' : Flat.LogPeriods n a g Λ), ∃ L : Flat.LogPeriods n a g Λ, (∀ w x, L.P w x = star (L'.P (star w) x)) ∧ ∀ z, L.H z = (L'.H (star z)).map (starRingEnd ℂ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.LogPer.exists_conj_logPeriods | exact GlobalTheory.CompanionTheory.Ar.Flat.LogPer.exists_conj_logPeriods | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.LogPer.exists_conj_logPeriods <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyExponentialConjugateStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.family_exponential_conjugate : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] (g n : ℕ) (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) (ρ : ℝ) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e' : Flat.FamExp G M (Metric.ball 0 ρ) (Flat.Conj.conjPts ψ)), ∃ e : Flat.FamExp G M (Metric.ball 0 ρ) ψ, ∀ b p, p ∈ e.per b ↔ star p ∈ e'.per (star b) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.ConjExp.exists_famExp_of_conj | exact GlobalTheory.CompanionTheory.Ar.Flat.ConjExp.exists_famExp_of_conj | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.ConjExp.exists_famExp_of_conj <;> assumption)
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryChartLogPeriodFamily
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.Conj

open GroundTheory.Heights₂.Heights.Regular GlobalTheory.CompanionTheory.Ar.Flat.Link

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show Spec.map (CommRingCat.ofHom (g.comp f)) = Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f)
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

theorem dualMap_conj_over :
    spMap (dualMap (starRingEnd ℂ)) ≫ spMap (algebraMap ℂ (DualNumber ℂ)) =
      spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap (starRingEnd ℂ) := by
  have h : (dualMap (starRingEnd ℂ)).comp (algebraMap ℂ (DualNumber ℂ)) =
      (algebraMap ℂ (DualNumber ℂ)).comp (starRingEnd ℂ) := by
    ext c
    · simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
    · simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  rw [← spMap_comp', ← spMap_comp', h]

theorem dualMap_comp_ring {R : Type} [CommRing R] (f : R →+* ℂ) :
    spMap (dualMap ((starRingEnd ℂ).comp f)) = spMap (dualMap (starRingEnd ℂ)) ≫ spMap (dualMap f) := by
  have h : dualMap ((starRingEnd ℂ).comp f) = (dualMap (starRingEnd ℂ)).comp (dualMap f) := by
    ext c <;> simp [dualMap]
  rw [h, spMap_comp']

theorem spMap_dualMap_conj_conj :
    spMap (dualMap (starRingEnd ℂ)) ≫ spMap (dualMap (starRingEnd ℂ)) = 𝟙 _ := by
  have h : (dualMap (starRingEnd ℂ)).comp (dualMap (starRingEnd ℂ)) = RingHom.id (DualNumber ℂ) := by
    ext c <;> simp [dualMap]
  rw [← spMap_comp', h]
  exact Spec.map_id _

theorem spMap_conj_conj : spMap (starRingEnd ℂ) ≫ spMap (starRingEnd ℂ) = 𝟙 (Sp ℂ) := by
  have h : (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ := by
    ext c
    simp
  rw [← spMap_comp', h]
  exact Spec.map_id _

def conjTan {S : Scheme.{0}} {G : Over S} {x x' : Sp ℂ ⟶ S} (h : x' = spMap (starRingEnd ℂ) ≫ x)
    (v : epsAt x ⟶ G) : epsAt x' ⟶ G :=
  Over.homMk (spMap (dualMap (starRingEnd ℂ)) ≫ v.left) (by
    subst h
    have hv := Over.w v
    simp only [Over.mk_hom] at hv ⊢
    rw [Category.assoc, hv, ← Category.assoc]
    have := dualMap_conj_over
    simp only [spMap] at this
    rw [this, Category.assoc])

theorem conj_hermForm' {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) :
    hermForm (Hm.map (starRingEnd ℂ)) a b = (starRingEnd ℂ) (hermForm Hm (star a) (star b)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [hermForm, dotProduct, Matrix.mulVec, map_sum, map_mul]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem isRiem_of_chart {Xo : Moduli D l} {σ : KA l →+* ℂ} {n a : ℕ} (C : BdryChart Xo σ n a) (z : Fin n → ℂ)
    (Hm : Matrix (Fin C.g) (Fin C.g) ℂ) (h : (chart C).IsRiem (star z) Hm) :
    C.IsRiem z (Hm.map (starRingEnd ℂ)) := by
  intro m u v Γ hv
  have hψ : conjPts C.ψ (star z) = (starRingEnd ℂ).comp (C.ψ z) := by simp [conjPts]
  have hx : spMap (conjPts C.ψ (star z)) = spMap (starRingEnd ℂ) ≫ spMap (C.ψ z) := by
    rw [hψ, spMap_comp']
  have hx' : spMap (C.ψ z) = spMap (starRingEnd ℂ) ≫ spMap (conjPts C.ψ (star z)) := by
    rw [hx, ← Category.assoc, spMap_conj_conj, Category.id_comp]
  let v' : Fin m → (epsAt (spMap (conjPts C.ψ (star z))) ⟶ C.t.G) := fun i => conjTan hx (v i)
  have hv' : (chart C).IsVal (star z) u v' := by
    intro i
    show spMap (dualMap (starRingEnd ℂ)) ≫ (v i).left = spMap (dualMap (conjPts C.ψ (star z))) ≫ (C.M.pt (u i)).left
    rw [hv i, hψ, dualMap_comp_ring, Category.assoc]
  have hback : ∀ i, (v i).left = spMap (dualMap (starRingEnd ℂ)) ≫ (v' i).left := fun i => by
    show (v i).left = spMap (dualMap (starRingEnd ℂ)) ≫ spMap (dualMap (starRingEnd ℂ)) ≫ (v i).left
    rw [← Category.assoc, spMap_dualMap_conj_conj, Category.id_comp]
  have hform : ∀ i j, hermForm Hm (fun b => conjPts C.ψ (star z) (u i b)) (fun b => conjPts C.ψ (star z) (u j b)) =
      (starRingEnd ℂ) (hermForm (Hm.map (starRingEnd ℂ)) (fun b => C.ψ z (u i b)) (fun b => C.ψ z (u j b))) := by
    intro i j
    rw [conj_hermForm', Complex.conj_conj, hψ]
    rfl
  have hform' : ∀ i j, (Real.pi : ℂ) * hermForm Hm (fun b => conjPts C.ψ (star z) (u i b))
      (fun b => conjPts C.ψ (star z) (u j b)) = (starRingEnd ℂ) ((Real.pi : ℂ) *
        hermForm (Hm.map (starRingEnd ℂ)) (fun b => C.ψ z (u i b)) (fun b => C.ψ z (u j b))) := by
    intro i j
    rw [hform, map_mul, Complex.conj_ofReal]
  have key := h m u v' (Γ.map (starRingEnd ℂ)) hv'
  constructor
  · intro hG i j
    have h1 := key.1 (GlobalTheory.T.hodge_gram_complex_conjugate _ _ _ _ _ _ _ _ _ hx (fun _ => rfl) hG) i j
    have h2 : (starRingEnd ℂ) (Γ i j) = _ := h1.trans (hform' i j)
    have h3 := congrArg (starRingEnd ℂ) h2
    simpa only [Complex.conj_conj] using h3
  · intro hE
    have h1 : Fl.IsHodgeGram C.t.G C.t.PP.L (spMap (conjPts C.ψ (star z))) v' (Γ.map (starRingEnd ℂ)) := by
      refine key.2 fun i j => ?_
      exact (congrArg (starRingEnd ℂ) (hE i j)).trans (hform' i j).symm
    have h2 := GlobalTheory.T.hodge_gram_complex_conjugate _ _ _ _ _ _ _ _ _ hx' hback h1
    have h3 : (Γ.map (starRingEnd ℂ)).map (starRingEnd ℂ) = Γ := by
      ext i j
      simp
    rwa [h3] at h2

theorem exists_log_periods_of_root : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) (C : Flat.BdryChart Xo σ n a), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → ∃ (ρ : ℝ) (Λ : Type) (_ : AddCommGroup Λ) (L : Flat.LogPeriods n a C.g Λ) (e : Flat.FamExp C.t.G C.M (Metric.ball 0 ρ) C.ψ), 0 < ρ ∧ ρ ≤ 1 ∧ (∀ w ∈ GroundTheory.Heights₂.Heights.Regular.logCover L.a_le, ∀ p, p ∈ e.per ((ρ : ℂ) • GroundTheory.Heights₂.Heights.Regular.expCover a w) ↔ ∃ x, L.P w x = p) ∧ ∀ z ∈ Flat.punct n a 1, C.IsRiem ((ρ : ℂ) • z) (L.H z) := by
  intro E _ _ _ H D l Xo σ n a C hpq hσ
  obtain ⟨g', ty, hty⟩ := GlobalTheory.AllClasses.exists_isTypeFn H D.p D.q
  obtain ⟨FU⟩ := GlobalTheory.familyUnif_of_laws GlobalTheory.abelianSchemeLaws_all.1 E H D l Xo σ g' ty hpq hσ hty
  have hsemi : IsSemiAbelian C.t.G := C.t.semi
  obtain ⟨ε, hε, hεB, ⟨e₀⟩⟩ := GlobalTheory.T.exists_family_exponential_locally C.R C.t.G C.g n C.M (Metric.ball 0 1) C.ψ hsemi.smooth C.hol 0
    (Metric.mem_ball_self one_pos)
  have h0ε : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) ε := Metric.mem_ball_self hε
  obtain ⟨Γ₀, hΓ₀, -, hfin, hfree⟩ := GlobalTheory.T.period_lattice_discrete_free C.R C.t.G C.g n C.M _ C.ψ e₀ 0 h0ε
  let Q : (Fin n → ℂ) → AddSubgroup (Fin C.g → ℂ) := fun b => AddSubgroup.closure (e₀.per b)
  have hQ : ∀ b ∈ Metric.ball (0 : Fin n → ℂ) ε, ∀ p, p ∈ Q b ↔ p ∈ e₀.per b := fun b hb p =>
    mem_closure_per e₀ hb p
  have hsp : ∀ x : Γ₀, ∃ (ε' : ℝ) (s : (Fin n → ℂ) → (Fin C.g → ℂ)), 0 < ε' ∧
      DifferentiableOn ℂ s (Metric.ball 0 ε') ∧ s 0 = x ∧ ∀ b ∈ Metric.ball (0 : Fin n → ℂ) ε', s b ∈ Q b := by
    intro x
    obtain ⟨ε', s, h0, hsub, hd, hs0, hs⟩ := GlobalTheory.T.period_holomorphic_continuation C.R C.t.G C.g n C.M _ C.ψ e₀ Metric.isOpen_ball 0 h0ε x
      (by rw [← hΓ₀]; exact x.2)
    exact ⟨ε', s, h0, hd, hs0, fun b hb => (hQ b (hsub hb) _).2 (hs b hb)⟩
  obtain ⟨ρ, hρ0, hρc, S, hSd, hS0, hSa, hSq⟩ := exists_additive_sections Γ₀ Q (min 1 ε) (lt_min one_pos hε) hsp
  have hρ1 : ρ ≤ 1 := hρc.trans (min_le_left _ _)
  have hball : Metric.ball (0 : Fin n → ℂ) ρ ⊆ Metric.ball 0 ε :=
    Metric.ball_subset_ball (hρc.trans (min_le_right _ _))
  have hball1 : Metric.ball (0 : Fin n → ℂ) ρ ⊆ Metric.ball 0 1 := Metric.ball_subset_ball hρ1
  have h0ρ : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) ρ := Metric.mem_ball_self hρ0
  let e : FamExp C.t.G C.M (Metric.ball 0 ρ) C.ψ := restrict e₀ Metric.isOpen_ball hball
  have hQ' : ∀ b ∈ Metric.ball (0 : Fin n → ℂ) ρ, ∀ p, p ∈ Q b ↔ p ∈ e.per b := fun b hb p => hQ b (hball hb) p
  have hΓ₀' : (Γ₀ : Set (Fin C.g → ℂ)) = e.per 0 := hΓ₀
  have hSp : ∀ x, ∀ b ∈ Metric.ball (0 : Fin n → ℂ) ρ, S x b ∈ e.per b := fun x b hb =>
    (hQ' b hb _).1 (hSq x b hb)
  obtain ⟨i, Hf, hrank, hopen, hloc⟩ := GlobalTheory.T.boundary_chart_hodge_matrix E H D l Xo σ n a C g' ty FU ρ e hρ0 hρ1
  obtain ⟨hfreeL, hfinL, -⟩ := GlobalTheory.Coisotropic.lattice_rank E H (FU.Di i)
  have hU : ∀ z ∈ punct n a 1, (ρ : ℂ) • z ∈ punct n a ρ := fun z hz => (smul_mem_punct hρ0).2 hz
  have hsm : Differentiable ℂ (fun z : Fin n → ℂ => (ρ : ℂ) • z) := differentiable_id.fun_const_smul _
  have key : ∃ L : Flat.LogPeriods n a C.g (FU.Di i).La, L.H = (fun z => Hf ((ρ : ℂ) • z)) ∧
      ∀ w ∈ logCover L.a_le, (L.P w).range = Q ((ρ : ℂ) • expCover a w) := by
    refine GlobalTheory.T.period_lattice_on_punctured_disc n a C.g C.a_le (FU.Di i).La (FU.Di i).EF (fun z => Q ((ρ : ℂ) • z))
      (fun z => Hf ((ρ : ℂ) • z)) (punct n a 1) Γ₀ (fun x z => S x ((ρ : ℂ) • z)) rfl hrank (FU.Di i).alt
      (FU.Di i).unimod ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact fun z hz => ⟨(hopen _ (hU z hz)).1, fun x hx => (hopen _ (hU z hz)).2.1 x hx⟩
    · intro z₀ hz₀
      obtain ⟨N, hNo, hzN, hNp, P, hPd, hP⟩ := hloc _ (hU z₀ hz₀)
      refine ⟨(fun z => (ρ : ℂ) • z) ⁻¹' N, hNo.preimage hsm.continuous, hzN,
        fun z hz => (smul_mem_punct hρ0).1 (hNp hz), fun z => P ((ρ : ℂ) • z), fun x => ?_, fun z hz => ?_⟩
      · exact (hPd x).comp hsm.differentiableOn (fun z hz => hz)
      · obtain ⟨h1, h2, h3⟩ := hP _ hz
        refine ⟨h1, ?_, h3⟩
        ext p
        have h4 : p ∈ (P ((ρ : ℂ) • z)).range ↔ p ∈ e.per ((ρ : ℂ) • z) := by
          rw [← SetLike.mem_coe, h2]
        rw [h4]
        exact (hQ' _ (punct_subset_ball (hNp hz)) p).symm
    · intro x
      refine ⟨(hSd x).comp hsm.differentiableOn (fun z hz => smul_mem_ball hρ0 hz), ?_,
        fun z hz => hSq x _ (smul_mem_ball hρ0 hz.1)⟩
      show S x ((ρ : ℂ) • 0) = x
      rw [smul_zero]
      exact hS0 x
    · exact fun x y z => hSa x y _
    · intro s hs hsU
      obtain ⟨u, hu, huU⟩ := exists_seq_punct (n := n) (a := a)
      have hρc' : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ0.ne'
      have htend : Tendsto (fun k => (ρ : ℂ) • u k) atTop (𝓝 0) := by
        have h := hu.const_smul (ρ : ℂ)
        rwa [smul_zero] at h
      have hcl := GlobalTheory.T.period_set_closed C.R C.t.G C.g n C.M (Metric.ball 0 ρ) C.ψ e hsemi.separated
        ⟨Metric.isOpen_ball, fun r => (C.hol.2 r).mono hball1⟩ 0 h0ρ (fun b => s ((ρ : ℂ)⁻¹ • b))
        (ContinuousAt.comp_of_eq hs (continuous_const_smul _).continuousAt (smul_zero _))
        (htend.frequently (Eventually.frequently (Eventually.of_forall fun k => by
          refine ⟨punct_subset_ball (hU _ (huU k)), ?_⟩
          show s ((ρ : ℂ)⁻¹ • (ρ : ℂ) • u k) ∈ e.per ((ρ : ℂ) • u k)
          rw [smul_smul, inv_mul_cancel₀ hρc', _root_.one_smul]
          exact (hQ' _ (punct_subset_ball (hU _ (huU k))) _).1 (hsU _ (huU k)))))
      have h0 : s 0 ∈ e.per 0 := by simpa using hcl
      rw [← hΓ₀'] at h0
      exact h0
    · rw [hΓ₀']
      exact GlobalTheory.T.period_lattice_spans C.R C.t.G C.g n C.M _ C.ψ e hsemi 0 h0ρ
    · intro N hN
      obtain ⟨T, hT, hTw⟩ := GlobalTheory.T.torsion_periods_finite_quotient E H C.R C.t C.g n C.M (Metric.ball 0 ρ) C.ψ e C.dim 0 h0ρ Γ₀ hΓ₀' N hN
      refine ⟨T, hT, fun x y hx z hz => ?_⟩
      have hb := hU z hz
      have hbm := punct_subset_ball hb
      have hc := cubWeil_carry e hρ0 N hN (S x) (S y) (hSd x) (hSd y) (hSp x) (hSp y) 1 (by
        rw [hS0 x, hS0 y]
        have h1 : unitOn (1 : ℂˣ) = 1 := map_one _
        rw [h1]
        exact hTw x y hx) _ hbm
      have hz' := (hopen _ hb).2.2.2 N 1 hN _ (hSp x _ hbm) _ (hSp y _ hbm) hc
      exact exists_int_of_exp_eq_one hN hz'
  obtain ⟨L, hLH, hLr⟩ := key
  refine ⟨ρ, (FU.Di i).La, inferInstance, L, e, hρ0, hρ1, fun w hw p => ?_, fun z hz => ?_⟩
  · have hzρ := hU _ (expCover_mem_punct L.a_le hw)
    have hzb := punct_subset_ball hzρ
    constructor
    · intro hp
      have h : p ∈ (L.P w).range := by
        rw [hLr w hw]
        exact (hQ' _ hzb _).2 hp
      exact h
    · rintro ⟨x, rfl⟩
      have h : L.P w x ∈ (L.P w).range := ⟨x, rfl⟩
      rw [hLr w hw] at h
      exact (hQ' _ hzb _).1 h
  · rw [hLH]
    exact (hopen _ (hU z hz)).2.2.1

theorem rt0_conj_neg_ne_zero (H : Host E) : (starRingEnd ℂ) H.rt0 = -H.rt0 :=
  _root_.UpperTheory.Reformulated.B.StarRingEndRootEqNeg.rt0_conj_neg_ne_zero H

theorem exists_logPeriods_famExp_isRiem : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) (C : Flat.BdryChart Xo σ n a), 1 ≤ D.p + D.q → ∃ (ρ : ℝ) (Λ : Type) (_ : AddCommGroup Λ) (L : Flat.LogPeriods n a C.g Λ) (e : Flat.FamExp C.t.G C.M (Metric.ball 0 ρ) C.ψ), 0 < ρ ∧ ρ ≤ 1 ∧ (∀ w ∈ GroundTheory.Heights₂.Heights.Regular.logCover L.a_le, ∀ p, p ∈ e.per ((ρ : ℂ) • GroundTheory.Heights₂.Heights.Regular.expCover a w) ↔ ∃ x, L.P w x = p) ∧ ∀ z ∈ Flat.punct n a 1, C.IsRiem ((ρ : ℂ) • z) (L.H z) := by
  intro E _ _ _ H D l Xo σ n a C hpq
  have h1 : (σ (baseKA l).ρ) ^ 2 = -(H.d : ℂ) := by
    rw [← map_pow, (baseKA l).ρ_sq]
    simp
  have h2 : (σ (baseKA l).ρ - H.rt0) * (σ (baseKA l).ρ + H.rt0) = 0 := by
    have := H.sqrt_neg_disc_sq
    linear_combination h1 - this
  rcases mul_eq_zero.1 h2 with h | h
  · exact exists_log_periods_of_root E H D l Xo σ n a C hpq (sub_eq_zero.1 h)
  have hσ' : ((starRingEnd ℂ).comp σ) (baseKA l).ρ = H.rt0 := by
    have h3 : σ (baseKA l).ρ = -H.rt0 := eq_neg_of_add_eq_zero_left h
    show (starRingEnd ℂ) (σ (baseKA l).ρ) = H.rt0
    rw [h3, map_neg, rt0_conj_neg_ne_zero, neg_neg]
  obtain ⟨ρ, Λ, iΛ, L', e', hρ0, hρ1, hper, hriem⟩ :=
    exists_log_periods_of_root E H D l Xo ((starRingEnd ℂ).comp σ) n a (chart C) hpq hσ'
  obtain ⟨L, hLP, hLH⟩ := GlobalTheory.T.log_periods_conjugate_exists n a C.g Λ L'
  obtain ⟨e, hper'⟩ := GlobalTheory.T.family_exponential_conjugate C.R C.t.G C.g n C.M ρ C.ψ e'
  refine ⟨ρ, Λ, iΛ, L, e, hρ0, hρ1, fun w hw p => ?_, fun z hz => ?_⟩
  · have hw' : star w ∈ logCover L'.a_le := (star_mem_logCover _).2 hw
    rw [hper', star_real_smul, star_expCover]
    have h4 := hper (star w) hw' (star p)
    refine h4.trans ?_
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x, (hLP w x).trans ((congrArg star hx).trans (star_star p))⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x, ((congrArg star (hLP w x)).trans (star_star _)).symm⟩
  · have h := hriem (star z) (star_mem_punct.2 hz)
    rw [hLH]
    refine isRiem_of_chart C _ _ ?_
    rw [star_real_smul]
    exact h

end GlobalTheory.CompanionTheory.Ar.Flat.Conj
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryChartLogPeriodFamilyStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundary_chart_log_period_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) (C : Flat.BdryChart Xo σ n a), 1 ≤ D.p + D.q → ∃ (ρ : ℝ) (Λ : Type) (_ : AddCommGroup Λ) (L : Flat.LogPeriods n a C.g Λ) (e : Flat.FamExp C.t.G C.M (Metric.ball 0 ρ) C.ψ), 0 < ρ ∧ ρ ≤ 1 ∧ (∀ w ∈ GroundTheory.Heights₂.Heights.Regular.logCover L.a_le, ∀ p, p ∈ e.per ((ρ : ℂ) • GroundTheory.Heights₂.Heights.Regular.expCover a w) ↔ ∃ x, L.P w x = p) ∧ ∀ z ∈ Flat.punct n a 1, C.IsRiem ((ρ : ℂ) • z) (L.H z) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.Conj.exists_logPeriods_famExp_isRiem | exact GlobalTheory.CompanionTheory.Ar.Flat.Conj.exists_logPeriods_famExp_isRiem | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.Conj.exists_logPeriods_famExp_isRiem <;> assumption)
end
