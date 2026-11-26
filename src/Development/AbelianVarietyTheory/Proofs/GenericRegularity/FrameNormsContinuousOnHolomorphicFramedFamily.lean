module

public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsHolomorphicPeriodsAdapted
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.UnitFramesGeneratorRatioModulusOne
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NormalisedPointsSatisfySingleFrame
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CompSplitRecord

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.AppellHumbertMeanSquareEqOfProportionalSections
section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.AppellHumbertMeanSquareEqOfProportionalSections
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open Formalism.L2.PjFree hiding gxFst gxSnd toC
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif GlobalTheory.FrameNorm
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.FrameNorm


open GlobalTheory.UnitFrameGen MeasureTheory in
theorem ahMean_eq_of_secBC : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (σ' : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ' ty) (k : Fin F.n) (P P' : (F.Di k).La →+ (Fin g → ℂ)) (h₀ : Matrix (Fin g) (Fin g) ℂ) (x x' : Sp ℂ ⟶ Xo.X) (s : LB.Sec (PPx x)) (s' : LB.Sec (PPx x')) (a : ℂ) (m m' : ℝ), IsPeriod (F.Di k) ty P → IsPeriod (F.Di k) ty P' → (∀ v, P v = h₀ *ᵥ P' v) → x = F.u k P → x' = x → SecBC (RingHom.id ℂ) a x x' s s' → AHMean F k P x s m → AHMean F k P' x' s' m' → m' = ‖a‖ ^ 2 * m := by
  intro E _ _ _ H Dw l Xo σ' g ty F i P' P h x' x s' s a m' m hp' hp hg hu' hxx hbc hA' hA
  obtain ⟨Hm, χ, fr, θ, Fd, hH, -, him, hd, hn, hc, h0, ha, hv, hF, hI⟩ := hA
  obtain ⟨Hm', χ', fr', θ', Fd', hH', -, him', hd', hn', hc', h0', ha', hv', hF', hI'⟩ := hA'
  obtain ⟨hdet, huu, hex⟩ := GlobalTheory.FamRigid.ex_eq_of_level_group GlobalTheory.latMinkowski E H Dw l Xo _ g _ F i
    P P' (LinearEquiv.refl _ _) h hp hp' (fun _ _ => rfl) (fun _ _ => ⟨0, by simp⟩) (fun _ => ⟨0, by simp⟩) hg
  have hspan : Submodule.span ℝ (P.range : Set (Fin g → ℂ)) = ⊤ := by
    rw [AddMonoidHom.coe_range]; exact hp.2.2.2.1
  have hHH : ∀ z w, hermForm Hm' (h *ᵥ z) (h *ᵥ w) = hermForm Hm z w :=
    hermForm_eq_of_im _ hspan Hm Hm' h (by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      rw [← hg, ← hg, him, him'])
  have hexp : ∀ a ∈ P.range, ∀ z, F.ex i P (z + a) = F.ex i P z := fun a ha z => by
    rw [F.ex_add i P hp, (F.ex_ker i P hp a).2 ha]
    exact @_root_.mul_one _ (CategoryTheory.Hom.monoid).toMulOneClass _
  have hcov : ∀ z, ∃ j, ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun z =>
    GlobalTheory.ThetaPtChg.exists_chart_point Xo.univ.t.PP.isLB _
  have tr : ∀ j z, ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      ⊤ ≤ (F.ex i P' (h *ᵥ z)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun j z hz => by rw [hex]; exact hz
  have hm : ∀ j, ∀ a ∈ P.range, ∀ z, ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → ‖fr j z‖ =
      Real.exp (Real.pi * (hermForm Hm z a).re + Real.pi / 2 * (hermForm Hm a a).re) * ‖fr j (z + a)‖ := by
    rintro j _ ⟨a, rfl⟩ z hz
    exact norm_factor Hm _ _ _ _ _ (ha a j z).1 ((ha a j z).2 hz)
  have dl : Differentiable ℂ (fun z' : Fin g → ℂ => h *ᵥ z') :=
    (LinearMap.toContinuousLinearMap (Matrix.mulVecLin h)).differentiable
  have hfr : ∀ j z, ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr' j (h *ᵥ z) = fr j z :=
    frames_eq P.range hspan (fun j => {z | ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j})
      (fun j => GlobalTheory.FamilyUnif_isOpen_ex F i P hp _) hcov
      (fun j a ha z hz => by rw [Set.mem_setOf_eq, hexp a ha]; exact hz)
      fr (fun j z => fr' j (h *ᵥ z))
      (fun j j' z => valAt' (F.ex i P z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j')
        (Xo.univ.t.PP.L.g j j').val)
      (fun a z => Real.exp (Real.pi * (hermForm Hm z a).re + Real.pi / 2 * (hermForm Hm a a).re))
      hd (fun j => (hd' j).comp dl.differentiableOn fun z hz => tr j z hz) hn
      (fun j j' z h1 h2 => hc j j' z ((top_le_preimage_inf _ _ _).2 ⟨h1, h2⟩))
      (fun j j' z h1 h2 => by
        have e2 := hc' j j' (h *ᵥ z) ((top_le_preimage_inf _ _ _).2 ⟨tr _ _ h1, tr _ _ h2⟩)
        rw [hex] at e2
        exact e2)
      (fun j hz => by
        have t0 := tr j 0 hz
        simp only [Matrix.mulVec_zero] at t0 ⊢
        rw [h0 j hz, h0' j t0, hxx])
      hm (by
        rintro j _ ⟨a, rfl⟩ z hz
        have := norm_factor Hm' _ _ _ _ _ (ha' a j (h *ᵥ z)).1 ((ha' a j (h *ᵥ z)).2 (tr j z hz))
        rw [hg, hHH, hHH, ← Matrix.mulVec_add] at this
        exact this)
  have hS : Out.SecTwistSt := GlobalTheory.abelianSchemeLaws_all.2.secTwist
  have hw0 : ∀ z, (F.ex i P z).left ≫ Xo.univ.t.G.hom = x' := fun z => by
    rw [← hex z]
    exact (Over.w (F.ex i P' (h *ᵥ z))).trans hu'.symm
  have hθ : ∀ z, θ z = a * θ' (h *ᵥ z) := fun z => by
    obtain ⟨j, hj⟩ := hcov z
    have hval := GlobalTheory.ThetaPtChg.val_of_secBC hS (Xo := Xo) _ _ hxx _ _ _ hbc
      (Over.homMk (F.ex i P z).left (hw0 z)) j _ _
      (fun pt h1 h2 => hv' j (h *ᵥ z) pt (h1.trans (hex z).symm) h2 (tr j z hj))
      (fun pt h1 h2 => hv j z pt h1 h2 hj)
    rw [hfr j z hj, ← mul_assoc] at hval
    exact mul_right_cancel₀ (hn j z hj) hval
  have hθp : ∀ b ∈ P.range, ∀ z, ‖θ' (h *ᵥ (z + b))‖ ^ 2 *
      Real.exp (-Real.pi * (hermForm Hm (z + b) (z + b)).re) =
      ‖θ' (h *ᵥ z)‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re) := fun b hb z => by
    obtain ⟨j, hj⟩ := hcov z
    have hj' : ⊤ ≤ (F.ex i P (z + b)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := by rw [hexp b hb]; exact hj
    let p : Over.mk x' ⟶ Xo.univ.t.G := Over.homMk (F.ex i P z).left (hw0 z)
    have e1 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_snd (𝟙 _) p)
    have e2 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_fst (𝟙 _) p)
    have v1 := hv' j (h *ᵥ z) _ (by rw [hex]; exact e1) e2 (tr j z hj)
    have v2 := hv' j (h *ᵥ (z + b)) _ (by rw [hex, hexp b hb]; exact e1) e2 (tr j _ hj')
    rw [hfr j _ hj] at v1
    rw [hfr j _ hj'] at v2
    exact normSq_periodic hH _ _ _ _ z b (hn j _ hj') (v2.symm.trans v1) (hm j b hb z hj)
  haveI : Countable P.range := by
    haveI := hp.2.2.1
    exact TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hinj : Function.Injective (fun z : Fin g → ℂ => h *ᵥ z) :=
    Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det h).2 hdet)
  have hmean := mean_comp_eq P.range P'.range h hdet (fun z => ⟨?_, ?_⟩) Fd Fd' hF hF'
    (fun z => ‖θ' z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm' z z).re))
    (fun b hb z => by simp only [hHH, hθp b hb z])
  · rw [← hI, ← hI', ← hmean, ← mul_div_assoc, ← integral_const_mul]
    congr 2
    funext z
    rw [hθ, hHH, norm_mul, mul_pow, mul_assoc]
  · rintro ⟨b, hb⟩
    refine ⟨b, hinj ?_⟩
    simp only
    rw [← hg, hb]
  · rintro ⟨b, rfl⟩
    exact ⟨b, hg b⟩

end GlobalTheory.FrameNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.AppellHumbertMeanSquareEqOfProportionalSectionsStatement
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open Formalism.L2.PjFree hiding gxFst gxSnd toC
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif GlobalTheory.FrameNorm
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.appellHumbertMeanSquare_eq_of_proportional_sections : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (σ' : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ' ty) (k : Fin F.n) (P P' : (F.Di k).La →+ (Fin g → ℂ)) (h₀ : Matrix (Fin g) (Fin g) ℂ) (x x' : Sp ℂ ⟶ Xo.X) (s : LB.Sec (PPx x)) (s' : LB.Sec (PPx x')) (a : ℂ) (m m' : ℝ), IsPeriod (F.Di k) ty P → IsPeriod (F.Di k) ty P' → (∀ v, P v = h₀ *ᵥ P' v) → x = F.u k P → x' = x → SecBC (RingHom.id ℂ) a x x' s s' → AHMean F k P x s m → AHMean F k P' x' s' m' → m' = ‖a‖ ^ 2 * m := by
  first | exact @GlobalTheory.FrameNorm.ahMean_eq_of_secBC | exact GlobalTheory.FrameNorm.ahMean_eq_of_secBC | (intros; apply GlobalTheory.FrameNorm.ahMean_eq_of_secBC <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.MeanSquareMultipleThetaSectionFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.MeanSquareMultipleThetaSectionFamily
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open Formalism.L2.PjFree hiding gxFst gxSnd toC
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif GlobalTheory.FrameNorm
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.FrameNorm


open GlobalTheory.NormFrame in
set_option maxHeartbeats 1600000 in
theorem ahMean_of_secVal_thetaChar : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (σ' : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ' ty) (k : Fin F.n) (m : ℕ) (B : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → ((F.Di k).La →+ (Fin g → ℂ))) (fr : Xo.univ.t.PP.L.ι → (Fin m → ℂ) × (Fin g → ℂ) → ℂ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (F.Di k).La) (b : Fin m → ℂ) (h τ : Matrix (Fin g) (Fin g) ℂ) (c₁ c₂ : Fin g → ℂ) (x : Sp ℂ ⟶ Xo.X) (s : LB.Sec (PPx x)) (κ : ℂ), b ∈ B → IsPeriod (F.Di k) ty (P b) → (∀ v w, (F.Di k).EF (bas v) (bas w) = -omegaStd v w) → IsUnit h.det → τ.IsSymm → (τ.map Complex.im).PosDef → (∀ i, h *ᵥ P b (bas (Pi.single (Sum.inl i) 1)) = Pi.single i 1 ∧ h *ᵥ P b (bas (Pi.single (Sum.inr i) 1)) = τ *ᵥ Pi.single i 1) → (∀ i, c₁ i = 0 ∨ c₁ i = 1 / 2) → (∀ i, c₂ i = 0 ∨ c₂ i = 1 / 2) → RigFrame F k B P fr → x = F.u k (P b) → κ ≠ 0 → SecVal F k (P b) x s (fun z => κ * thetaChar τ c₁ c₂ (h *ᵥ z)) (fun j z => fr j (b, z)) → AHMean F k (P b) x s (‖κ‖ ^ 2 * (Real.sqrt (2 ^ g * (τ.map Complex.im).det))⁻¹) := by
  intro E _ _ _ H Dw l Xo σ' g ty F k m B P fr bas b h τ c₁ c₂ x s κ hbd hper hsympl hdet hsym hpos hn half₁ half₂
    ⟨fr_hol, fr_ne, fr_coc, fr_rig⟩ hx hκ0 hs
  obtain ⟨Hm, hH1, hH2, hH3⟩ := hper.2.2.2.2
  obtain ⟨hHm, -⟩ := GlobalTheory.RiemannForm.herm_eq_of_normalised E H _ g _ bas _ h τ Hm hsympl hper hn
    ⟨hsym, hpos⟩ hH3
  obtain ⟨q, hq⟩ : ∃ q : (Fin g → ℂ) → ℂ, ∀ z, q z = Real.pi / 2 * ((h *ᵥ z) ⬝ᵥ
      (((τ.map Complex.im)⁻¹).map (fun x : ℝ => (x : ℂ)) *ᵥ (h *ᵥ z))) := ⟨_, fun _ => rfl⟩
  have hlin : Differentiable ℂ (fun z : Fin g → ℂ => h *ᵥ z) :=
    (Matrix.mulVecLin h).toContinuousLinearMap.differentiable
  have hqd : Differentiable ℂ q := by
    rw [funext hq]
    simp only [dotProduct, Matrix.mulVec]
    fun_prop
  have hq0 : q 0 = 0 := by simp [hq]
  obtain ⟨hA1, hA2⟩ := GlobalTheory.ThetaAH.exp_mul_thetaChar_automorphy g τ h Hm c₁ c₂ q hsym hpos
    half₁ half₂ hHm hq
  have hlat : ∀ lam, lam ∈ (P b).range ↔ ∃ m n : Fin g → ℤ,
      h *ᵥ lam = (fun i => (m i : ℂ)) + τ *ᵥ (fun i => (n i : ℂ)) := by
    intro lam
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨v, rfl⟩ := bas.surjective a
      exact ⟨_, _, period_bas bas _ _ _ hn v⟩
    · rintro ⟨m, n, hmn⟩
      refine ⟨bas (Sum.elim m n), ?_⟩
      apply Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 hdet)
      rw [hmn]
      exact period_bas bas _ _ _ hn _
  obtain ⟨Fd, hFd, hint⟩ := GlobalTheory.ThetaMean.exists_fundamentalDomain_mean_norm_sq_thetaChar g τ h
    c₁ c₂ _ hsym hpos hdet half₁ half₂ hlat
  obtain ⟨hθd, w0, hw0⟩ := (GlobalTheory.ThetaHalf.thetaChar_holomorphic_ne_zero g c₁ c₂ half₁ half₂).1 _ hsym hpos
  have hχ : ∀ lam : Fin g → ℂ, ∃ χ : ℂ, lam ∈ (P b).range → ‖χ‖ = 1 ∧ ∀ z,
      Complex.exp (q (z + lam)) * thetaChar τ c₁ c₂ (h *ᵥ (z + lam)) =
        χ * Complex.exp (Real.pi * hermForm Hm z lam + Real.pi / 2 * hermForm Hm lam lam) *
          (Complex.exp (q z) * thetaChar τ c₁ c₂ (h *ᵥ z)) := by
    intro lam
    by_cases hl : lam ∈ (P b).range
    · obtain ⟨m, n, hmn⟩ := (hlat lam).1 hl
      obtain ⟨χ, hχ⟩ := hA2 lam m n hmn
      exact ⟨χ, fun _ => hχ⟩
    · exact ⟨1, fun h => absurd h hl⟩
  choose χl hχl using hχ
  have hfrd : ∀ j, DifferentiableOn ℂ (fun z => fr j (b, z) * Complex.exp (-q z))
      {z | ⊤ ≤ (F.ex k (P b) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j} := by
    intro j
    refine DifferentiableOn.mul ?_ (by fun_prop)
    exact (fr_hol j).comp (f := fun z => (b, z)) (by fun_prop) fun z hz => ⟨hbd, hz⟩
  have hval : ∀ j z (pt : Sp ℂ ⟶ Gx x),
      pt ≫ gxFst x = (F.ex k (P b) z).left → pt ≫ gxSnd x = 𝟙 (Sp ℂ) →
      ⊤ ≤ (F.ex k (P b) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' pt ((PPx x).U (fun _ => j)) (s.f (fun _ => j)) =
        (κ * (Complex.exp (q z) * thetaChar τ c₁ c₂ (h *ᵥ z))) *
          (fr j (b, z) * Complex.exp (-q z)) := by
    intro j z pt h1 h2 h3
    rw [hs j z pt h1 h2 h3, Complex.exp_neg]
    have := Complex.exp_ne_zero (q z)
    field_simp
  refine ⟨Hm, χl, fun j z => fr j (b, z) * Complex.exp (-q z),
    fun z => κ * (Complex.exp (q z) * thetaChar τ c₁ c₂ (h *ᵥ z)), Fd, hH1, hH2, hH3, hfrd,
    fun j z hz => mul_ne_zero (fr_ne j b z hbd hz) (Complex.exp_ne_zero _),
    fun j j' z hz => ?_, fun j hz => ?_, fun a j z => ⟨(hχl _ ⟨a, rfl⟩).1, ?_⟩, hval, hFd, ?_⟩
  · beta_reduce
    rw [fr_coc j j' b z hbd hz, mul_assoc]
  · beta_reduce
    rw [hq0, neg_zero, Complex.exp_zero, mul_one, fr_rig j b hbd hz, hx]
  · have hex : ∀ z, F.ex k (P b) (z + P b a) = F.ex k (P b) z :=
      ex_add_period F k _ hper a
    have hO : IsOpen {z | ⊤ ≤ (F.ex k (P b) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j} := by
      have h1 := ((F.hol k 0 Set.univ (fun _ => P b) isOpen_univ
        ⟨fun _ _ => hper, fun _ => differentiableOn_const _⟩).2 (Xo.univ.t.PP.L.U j) 0).1
      have h2 := h1.preimage (f := fun z : Fin g → ℂ => ((0 : Fin 0 → ℂ), z)) (by fun_prop)
      convert h2 using 1
      ext z
      simp
    refine cancel_entire (θ := fun z => Complex.exp (q z) * thetaChar τ c₁ c₂ (h *ᵥ z))
      (f := fun z => fr j (b, z) * Complex.exp (-q z))
      (f' := fun z => χl (P b a) * Complex.exp (Real.pi * hermForm Hm z (P b a) +
        Real.pi / 2 * hermForm Hm (P b a) (P b a)) *
        (fr j (b, z + P b a) * Complex.exp (-q (z + P b a))))
      ((hqd.cexp).mul (hθd.comp hlin)) ?_ hO (hfrd j).continuousOn ?_ ?_ z
    · obtain ⟨w, hw⟩ := Matrix.mulVec_surjective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 hdet) w0
      exact ⟨w, mul_ne_zero (Complex.exp_ne_zero _) (by rw [hw]; exact hw0)⟩
    · refine ContinuousOn.mul (Continuous.continuousOn ?_) ?_
      · simp only [hermForm, dotProduct]
        fun_prop
      · refine (hfrd j).continuousOn.comp (f := fun z => z + P b a) (by fun_prop) fun z hz => ?_
        rw [Set.mem_ofPred_eq, hex]
        exact hz
    · intro z hz
      have hw : 𝟙 _ ≫ x = (F.ex k (P b) z).left ≫ Xo.univ.t.G.hom := by
        rw [Category.id_comp, hx]
        exact (Over.w (F.ex k (P b) z)).symm
      obtain ⟨pt, e₁, e₂⟩ : ∃ pt : Sp ℂ ⟶ Gx x, pt ≫ gxFst x = (F.ex k (P b) z).left ∧ pt ≫ gxSnd x = 𝟙 _ :=
        ⟨pullback.lift (f := x) (g := Xo.univ.t.G.hom) _ _ hw, pullback.lift_snd _ _ _, pullback.lift_fst _ _ _⟩
      have h1 := hval j z pt e₁ e₂ hz
      have h2 := hval j (z + P b a) pt (by rw [hex]; exact e₁) e₂ (by rw [hex]; exact hz)
      have h3 := h1.symm.trans h2
      rw [(hχl _ ⟨a, rfl⟩).2 z] at h3
      apply mul_left_cancel₀ hκ0
      linear_combination h3
  · rw [← hint, ← mul_div_assoc, ← MeasureTheory.integral_const_mul]
    congr 2
    ext z
    rw [← hA1 z, norm_mul, norm_mul]
    ring

end GlobalTheory.FrameNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.MeanSquareMultipleThetaSectionFamilyStatement
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open Formalism.L2.PjFree hiding gxFst gxSnd toC
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif GlobalTheory.FrameNorm
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.meanSquare_multiple_thetaSection_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (σ' : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ' ty) (k : Fin F.n) (m : ℕ) (B : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → ((F.Di k).La →+ (Fin g → ℂ))) (fr : Xo.univ.t.PP.L.ι → (Fin m → ℂ) × (Fin g → ℂ) → ℂ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (F.Di k).La) (b : Fin m → ℂ) (h τ : Matrix (Fin g) (Fin g) ℂ) (c₁ c₂ : Fin g → ℂ) (x : Sp ℂ ⟶ Xo.X) (s : LB.Sec (PPx x)) (κ : ℂ), b ∈ B → IsPeriod (F.Di k) ty (P b) → (∀ v w, (F.Di k).EF (bas v) (bas w) = -omegaStd v w) → IsUnit h.det → τ.IsSymm → (τ.map Complex.im).PosDef → (∀ i, h *ᵥ P b (bas (Pi.single (Sum.inl i) 1)) = Pi.single i 1 ∧ h *ᵥ P b (bas (Pi.single (Sum.inr i) 1)) = τ *ᵥ Pi.single i 1) → (∀ i, c₁ i = 0 ∨ c₁ i = 1 / 2) → (∀ i, c₂ i = 0 ∨ c₂ i = 1 / 2) → RigFrame F k B P fr → x = F.u k (P b) → κ ≠ 0 → SecVal F k (P b) x s (fun z => κ * thetaChar τ c₁ c₂ (h *ᵥ z)) (fun j z => fr j (b, z)) → AHMean F k (P b) x s (‖κ‖ ^ 2 * (Real.sqrt (2 ^ g * (τ.map Complex.im).det))⁻¹) := by
  first | exact @GlobalTheory.FrameNorm.ahMean_of_secVal_thetaChar | exact GlobalTheory.FrameNorm.ahMean_of_secVal_thetaChar | (intros; apply GlobalTheory.FrameNorm.ahMean_of_secVal_thetaChar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ContinuousOnNormDiagOfTriangularSqrt
section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ContinuousOnNormDiagOfTriangularSqrt
open scoped Matrix

namespace GlobalTheory.TriSqrt

lemma det_eq_prod_diag {n α : Type*} [Fintype n] [DecidableEq n] [Fintype α] (t : n → α) (w : n → ℕ)
    (hinj : ∀ j j', t j = t j' → w j = w j' → j = j')
    (h : Matrix n n ℂ) (hs : ∀ j j', h j j' ≠ 0 → t j = t j' ∧ w j ≤ w j') :
    h.det = ∏ j, h j j := by
  have hi : Function.Injective (fun j => toLex (Fintype.equivFin α (t j), w j)) := by
    intro k l hkl
    have h' := toLex.injective hkl
    rw [Prod.mk.injEq] at h'
    exact hinj _ _ ((Fintype.equivFin α).injective h'.1) h'.2
  letI : LinearOrder n := LinearOrder.lift' _ hi
  refine Matrix.det_of_upperTriangular fun k l hkl => ?_
  by_contra hne
  obtain ⟨h1, h2⟩ := hs k l hne
  have hkl' : toLex (Fintype.equivFin α (t l), w l) < toLex (Fintype.equivFin α (t k), w k) := hkl
  simp only [h1, Prod.Lex.toLex_lt_toLex, lt_self_iff_false, true_and, false_or] at hkl'
  omega

lemma det_minor {n α : Type*} [Fintype n] [DecidableEq n] [Fintype α] (t : n → α) (w : n → ℕ)
    (hinj : ∀ j j', t j = t j' → w j = w j' → j = j') (d : n → ℝ)
    (S : Matrix n n ℂ) (hs : ∀ j j', S j j' ≠ 0 → t j = t j' ∧ w j ≤ w j')
    (p : n → Prop) [DecidablePred p] (hp : ∀ c a, S c a ≠ 0 → p a → p c) :
    ((Sᵀ * ((Matrix.diagonal fun j => ((d j : ℝ) : ℂ)) * S.map (starRingEnd ℂ))).submatrix
      (Subtype.val : {x // p x} → n) Subtype.val).det
      = ((∏ c ∈ Finset.univ.filter p, ‖S c c‖ ^ 2 * d c : ℝ) : ℂ) := by
  set T : Matrix {x // p x} {x // p x} ℂ := S.submatrix Subtype.val Subtype.val with hT
  have e : (Sᵀ * ((Matrix.diagonal fun j => ((d j : ℝ) : ℂ)) * S.map (starRingEnd ℂ))).submatrix
      (Subtype.val : {x // p x} → n) Subtype.val
      = Tᵀ * ((Matrix.diagonal fun j => ((d j.1 : ℝ) : ℂ)) * T.map (starRingEnd ℂ)) := by
    ext a a'
    simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply, hT,
      Matrix.diagonal_apply, Matrix.map_apply, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    rw [← Finset.sum_subtype (Finset.univ.filter p) (by simp)
      (fun c => S c a * ((d c : ℂ) * (starRingEnd ℂ) (S c a')))]
    symm
    refine Finset.sum_subset (Finset.subset_univ _) fun c _ hc => ?_
    have : S c a = 0 := by
      by_contra hne
      exact hc (by simpa using hp c a hne a.2)
    rw [this, zero_mul]
  have hdT : T.det = ∏ c, T c c :=
    det_eq_prod_diag (fun c => t c.1) (fun c => w c.1)
      (fun c c' h1 h2 => Subtype.ext (hinj _ _ h1 h2)) T fun c c' hne => hs _ _ hne
  have hdT' : (T.map (starRingEnd ℂ)).det = (starRingEnd ℂ) T.det := by
    rw [RingHom.map_det]; rfl
  rw [e, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal, hdT', hdT,
    map_prod, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
    Finset.prod_subtype (p := p) (Finset.univ.filter p) (by simp), Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  have := Complex.mul_conj' (S c c)
  simp only [hT, Matrix.submatrix_apply]
  push_cast
  rw [← this]
  ring

end GlobalTheory.TriSqrt

theorem GlobalTheory.continuousOn_norm_diag_of_triangular_sqrt : ∀ (g : ℕ) (α : Type) [Fintype α] (V : Type) [TopologicalSpace V] (t : Fin g → α) (w : Fin g → ℕ) (d : Fin g → ℝ) (B : Set V) (S Hm : V → Matrix (Fin g) (Fin g) ℂ), (∀ j j', t j = t j' → w j = w j' → j = j') → (∀ j, 0 < d j) → (∀ j j', ContinuousOn (fun b => Hm b j j') B) → (∀ b ∈ B, IsUnit (S b).det ∧ (∀ j j', S b j j' ≠ 0 → t j = t j' ∧ w j ≤ w j') ∧ Hm b = (S b)ᵀ * ((Matrix.diagonal fun j => ((d j : ℝ) : ℂ)) * (S b).map (starRingEnd ℂ))) → ∀ j, ContinuousOn (fun b => ‖S b j j‖) B := by
  intro g α _ V _ t w d B S Hm hinj hd hc hS j
  classical
  have hH : ContinuousOn Hm B := continuousOn_pi.2 fun k => continuousOn_pi.2 fun l => hc k l
  have hP : ∀ n : ℕ, ContinuousOn (fun b =>
      ∏ c ∈ Finset.univ.filter (fun c => t c = t j ∧ w c < n), ‖S b c c‖ ^ 2 * d c) B := by
    intro n
    have h1 : Continuous fun M : Matrix (Fin g) (Fin g) ℂ =>
        ((M.submatrix (Subtype.val : {c // t c = t j ∧ w c < n} → Fin g) Subtype.val).det).re :=
      Complex.continuous_re.comp (continuous_id.matrix_submatrix _ _).matrix_det
    refine (h1.comp_continuousOn hH).congr fun b hb => ?_
    obtain ⟨-, h2, h3⟩ := hS b hb
    simp only [Function.comp_apply]
    rw [h3, GlobalTheory.TriSqrt.det_minor t w hinj d (S b) h2 (fun c => t c = t j ∧ w c < n), Complex.ofReal_re]
    intro c a hne ha
    obtain ⟨h4, h5⟩ := h2 c a hne
    exact ⟨h4.trans ha.1, by omega⟩
  have hne : ∀ b ∈ B, ∀ c, S b c c ≠ 0 := by
    intro b hb c
    obtain ⟨h1, h2, -⟩ := hS b hb
    rw [GlobalTheory.TriSqrt.det_eq_prod_diag t w hinj _ h2, isUnit_iff_ne_zero] at h1
    exact Finset.prod_ne_zero_iff.1 h1 c (Finset.mem_univ _)
  have hne' : ∀ b ∈ B, (∏ c ∈ Finset.univ.filter (fun c => t c = t j ∧ w c < w j),
      ‖S b c c‖ ^ 2 * d c) * d j ≠ 0 := fun b hb =>
    mul_ne_zero (Finset.prod_ne_zero_iff.2 fun c _ =>
      mul_ne_zero (pow_ne_zero _ (norm_ne_zero_iff.2 (hne b hb c))) (hd c).ne') (hd j).ne'
  have hins : Finset.univ.filter (fun c => t c = t j ∧ w c < w j + 1)
      = insert j (Finset.univ.filter (fun c => t c = t j ∧ w c < w j)) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases h3 : w c = w j
      · exact Or.inl (hinj _ _ h1 h3)
      · exact Or.inr ⟨h1, by omega⟩
    · rintro (rfl | ⟨h1, h2⟩)
      · exact ⟨rfl, by omega⟩
      · exact ⟨h1, by omega⟩
  refine (((hP (w j + 1)).div ((hP (w j)).mul continuousOn_const) hne').sqrt).congr fun b hb => ?_
  have h0 := hne' b hb
  simp only [Pi.div_apply, Pi.mul_apply]
  rw [hins, Finset.prod_insert (by simp), mul_assoc, mul_comm (d j), mul_div_assoc, div_self h0, mul_one,
    Real.sqrt_sq (norm_nonneg _)]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ContinuousOnNormDiagOfTriangularSqrtStatement
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuousOn_norm_diag_of_triangular_factor : ∀ (g : ℕ) (α : Type) [Fintype α] (V : Type) [TopologicalSpace V] (t : Fin g → α) (w : Fin g → ℕ) (d : Fin g → ℝ) (B : Set V) (S Hm : V → Matrix (Fin g) (Fin g) ℂ), (∀ j j', t j = t j' → w j = w j' → j = j') → (∀ j, 0 < d j) → (∀ j j', ContinuousOn (fun b => Hm b j j') B) → (∀ b ∈ B, IsUnit (S b).det ∧ (∀ j j', S b j j' ≠ 0 → t j = t j' ∧ w j ≤ w j') ∧ Hm b = (S b)ᵀ * ((Matrix.diagonal fun j => ((d j : ℝ) : ℂ)) * (S b).map (starRingEnd ℂ))) → ∀ j, ContinuousOn (fun b => ‖S b j j‖) B := by
  first | exact @GlobalTheory.continuousOn_norm_diag_of_triangular_sqrt | exact GlobalTheory.continuousOn_norm_diag_of_triangular_sqrt | (intros; apply GlobalTheory.continuousOn_norm_diag_of_triangular_sqrt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameNormsContinuousOnHolomorphicFramedFamily
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open Formalism.L2.PjFree hiding gxFst gxSnd toC
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif GlobalTheory.FrameNorm
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.FrameNorm.Hol

theorem continuousOn_form {V : Type} [TopologicalSpace V] {g : ℕ} {B : Set V} (h τ : V → Matrix (Fin g) (Fin g) ℂ)
    (hh : ∀ i j, ContinuousOn (fun b => h b i j) B) (hτ : ∀ i j, ContinuousOn (fun b => τ b i j) B)
    (hp : ∀ b ∈ B, ((τ b).map Complex.im).PosDef) :
    ContinuousOn (fun b => ((τ b).map Complex.im).det) B ∧ ∀ i j, ContinuousOn (fun b =>
      ((h b)ᵀ * (((τ b).map Complex.im)⁻¹).map (fun x : ℝ => (x : ℂ)) * (h b).map (starRingEnd ℂ)) i j) B := by
  simp only [continuousOn_iff_continuous_restrict] at hh hτ ⊢
  have h1 : Continuous fun b : B => h b := continuous_matrix hh
  have h2 : Continuous fun b : B => (τ b).map Complex.im :=
    (continuous_matrix hτ : Continuous fun b : B => τ b).matrix_map Complex.continuous_im
  have h3 : Continuous fun b : B => ((τ b).map Complex.im)⁻¹ := by
    simp only [Matrix.inv_def, Ring.inverse_eq_inv']
    exact (h2.matrix_det.inv₀ fun b => (hp b b.2).det_pos.ne').smul h2.matrix_adjugate
  refine ⟨h2.matrix_det, fun i j => ?_⟩
  exact ((h1.matrix_transpose.matrix_mul (h3.matrix_map Complex.continuous_ofReal)).matrix_mul
    (h1.matrix_map Complex.continuous_conj)).matrix_elem i j

theorem exists_continuous_form_mean {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
    {σ : c.F →+* ℂ} {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ' ty) (k : Fin F.n)
    (hty : IsTypeFn H Dw.p Dw.q ty) {A : Type} [CommRing A] [Algebra c.F A] (yA : FrPt Xo c A) {m : ℕ}
    {B : Set (Fin m → ℂ)} (φ : (Fin m → ℂ) → (A →ₐ[c.F] CAt σ)) (y : (Fin m → ℂ) → FrPt Xo c (CAt σ))
    (P : (Fin m → ℂ) → ((F.Di k).La →+ (Fin g → ℂ))) (hB : IsOpen B)
    (hφ : ∀ a, DifferentiableOn ℂ (fun b => toC (φ b a)) B) (hy : ∀ b ∈ B, FrMap (φ b) yA (y b))
    (hP : IsHolPeriods (F.Di k) ty B P) (hx : ∀ b ∈ B, (y b).x = F.u k (P b)) {b₀ : Fin m → ℂ} (hb₀ : b₀ ∈ B) :
    ∃ (B' : Set (Fin m → ℂ)) (Hm : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ) (μ : (Fin m → ℂ) → ℝ),
      IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ (∀ i j, ContinuousOn (fun b => Hm b i j) B') ∧ ContinuousOn μ B' ∧
      ∀ b ∈ B', (∀ v w, (hermForm (Hm b) (P b v) (P b w)).im = (F.Di k).EF v w) ∧
        AHMean F k (P b) (y b).x (y b).s (μ b) := by
  obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.1 hB b₀ hb₀
  obtain ⟨hg, -⟩ := (GlobalTheory.PeriodExists.typeFn_period_exist E H (F.Di k)).2.1 g ty
    (by rw [(F.sig k).1, (F.sig k).2]; exact hty)
  obtain ⟨bas, hbas, -⟩ := GlobalTheory.exists_symplectic_basis_adapted_mod_eight E H (F.Di k) g hg
  obtain ⟨hR1, hR2⟩ := GlobalTheory.RiemannRel.riemann_relations E H (F.Di k) g ty bas hbas
  have hP' : IsHolPeriods (F.Di k) ty (Metric.ball b₀ ε) P :=
    ⟨fun b hb => hP.1 b (hsub hb), fun v => (hP.2 v).mono hsub⟩
  choose! h τ hn hdet hsym hpos _ using fun b hb => hR1 _ (hP'.1 b hb)
  have hhol := hR2 m _ P h τ hP' hn
  obtain ⟨c₁, c₂, hc₁, hc₂, hθ⟩ := F.theta k m _ P bas (-1) h τ Metric.isOpen_ball
    (convex_ball b₀ ε).isPreconnected hP' (fun a b => by rw [hbas]; simp) (fun b hb => ⟨hpos b hb, hn b hb⟩)
  obtain ⟨t1, t2⟩ := GlobalTheory.ThetaHalf.thetaChar_holomorphic_ne_zero g c₁ c₂ hc₁ hc₂
  have t3 := t2 m _ h τ Metric.isOpen_ball (fun b hb => ⟨hsym b hb, hpos b hb⟩) hhol
  obtain ⟨fr, κ, hfr, hκ, hval⟩ := GlobalTheory.T.exists_holomorphicFactor_generator_thetaSection E H Dw l Xo c σ σ' g ty F k A yA m _ φ y P
    (fun b z => thetaChar (τ b) c₁ c₂ (h b *ᵥ z)) Metric.isOpen_ball
    (fun a => (hφ a).mono hsub) (fun b hb => hy b (hsub hb)) hP' (fun b hb => hx b (hsub hb))
    (fun z => DifferentiableOn.comp (f := fun b : Fin m → ℂ => ((b, z) : (Fin m → ℂ) × (Fin g → ℂ)))
      (g := fun bz : (Fin m → ℂ) × (Fin g → ℂ) => thetaChar (τ bz.1) c₁ c₂ (h bz.1 *ᵥ bz.2))
      t3 (by fun_prop) fun b hb => ⟨hb, trivial⟩)
    (fun b hb => by
      obtain ⟨-, w, hw⟩ := t1 _ (hsym b hb) (hpos b hb)
      obtain ⟨z, hz⟩ := Matrix.mulVec_surjective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 (hdet b hb)) w
      exact ⟨z, by rw [hz]; exact hw⟩) hθ
  obtain ⟨c1, c2⟩ := continuousOn_form h τ (fun i j => (hhol i j).1.continuousOn)
    (fun i j => (hhol i j).2.continuousOn) hpos
  refine ⟨Metric.ball b₀ ε, _, fun b => ‖κ b‖ ^ 2 * (Real.sqrt (2 ^ g * ((τ b).map Complex.im).det))⁻¹,
    Metric.isOpen_ball, Metric.mem_ball_self hε, hsub, c2, ?_, fun b hb => ⟨?_, ?_⟩⟩
  · refine (hκ.continuousOn.norm.pow 2).mul (ContinuousOn.inv₀ (continuousOn_const.mul c1).sqrt fun b hb => ?_)
    have := (hpos b hb).det_pos
    positivity
  · obtain ⟨Hm, -, -, hH⟩ := (hP'.1 b hb).2.2.2.2
    rw [← (GlobalTheory.RiemannForm.herm_eq_of_normalised E H _ g _ bas _ (h b) (τ b) Hm hbas (hP'.1 b hb) (hn b hb)
      ⟨hsym b hb, hpos b hb⟩ hH).1]
    exact hH
  · exact GlobalTheory.T.meanSquare_multiple_thetaSection_family E H Dw l Xo σ' g ty F k m _ P fr bas b (h b) (τ b) c₁ c₂ _ _ (κ b) hb (hP'.1 b hb) hbas (hdet b hb)
      (hsym b hb) (hpos b hb) (hn b hb) hc₁ hc₂ hfr (hx b (hsub hb)) (hval b hb).1 (hval b hb).2

end GlobalTheory.FrameNorm.Hol

theorem GlobalTheory.FrameNorm.fn_continuousOn_hol : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → ∀ (xR : ℝ) (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ), 0 < xR → FnPin U xR fn → ∀ σ, Formalism.L2.PjFree.GoodEmb c σ → ∀ (A : Type) [CommRing A] [Algebra c.F A] (yA : FrPt Xo c A) (m : ℕ) (B : Set (Fin m → ℂ)) (φ : (Fin m → ℂ) → (A →ₐ[c.F] CAt σ)) (y : (Fin m → ℂ) → FrPt Xo c (CAt σ)), IsOpen B → (∀ a, DifferentiableOn ℂ (fun b => Formalism.L2.PjFree.toC (φ b a)) B) → (∀ b ∈ B, FrMap (φ b) yA (y b)) → ∀ i, ContinuousOn (fun b => |fn σ (y b) i|) B := by
  intro E _ _ _ H Dw l Xo c r U hU xR fn _ hpin σ hσ A _ _ yA m B φ y hB hφ hy i b₀ hb₀
  obtain ⟨hr, hty, hcov, -, -, g, e, F, ik, ψ, hef, hun⟩ := hU σ hσ
  obtain ⟨B₁, k, P, hB₁, hb₁, hs₁, hP, hyP⟩ := GlobalTheory.T.exists_holomorphic_periods_adapted E H Dw l Xo c σ g e F A yA m B φ y hB hφ hy b₀ hb₀
  obtain ⟨k₀, x₁, t₁, ht₁⟩ := hcov (y b₀)
  obtain ⟨P₁, hP₁, hP₁', hx₁, -⟩ := hun k₀ x₁
  obtain rfl : ik k₀ = k := F.disj _ _ _ _ hP₁' (hP.1 b₀ hb₁) (hx₁.symm.trans (ht₁.1.symm.trans (hyP b₀ hb₁).1))
  obtain ⟨d, hd, horth⟩ := GlobalTheory.T.period_eq_triangular_orthonormal_alt E H Dw l c σ g e _ r ((U σ).X k₀) (ψ k₀) hσ (F.sig _).1 (F.sig _).2 hr
    (hty k₀).1 (hty k₀).2 (hef k₀)
    (GlobalTheory.T.im_neg_of_frame_period_vector E H Dw l c σ g e _ r ((U σ).X k₀) (ψ k₀) hσ hr (hty k₀).1 (hty k₀).2 (hef k₀) x₁.1 x₁.2 P₁ hP₁ hP₁')
  obtain ⟨B₂, Hm, μ, hB₂, hb₂, hs₂, hHm, hμ, hAH⟩ := GlobalTheory.FrameNorm.Hol.exists_continuous_form_mean F (ik k₀)
    ((GlobalTheory.Relab.relab_good E H l c σ hσ).2.2.2 Dw g e) yA φ y P hB₁ (fun a => (hφ a).mono hs₁)
    (fun b hb => hy b (hs₁ hb)) hP (fun b hb => (hyP b hb).1) hb₁
  have key : ∀ b ∈ B₂, ∃ S : Matrix (Fin g) (Fin g) ℂ, (IsUnit S.det ∧
      (∀ j j', S j j' ≠ 0 → (e j).1 = (e j').1 ∧ ((e j).2 : ℕ) ≤ (e j').2) ∧
      Hm b = Sᵀ * ((Matrix.diagonal fun j => ((d j : ℝ) : ℂ)) * S.map (starRingEnd ℂ))) ∧
      (∀ j, |fn σ (y b) (some (e j))| = ‖S j j‖ * Real.sqrt (2 * Real.pi * xR)) ∧
      |fn σ (y b) none| = Real.sqrt (μ b) := by
    intro b hb
    have hp := hP.1 b (hs₂ hb)
    obtain ⟨x₀, hx₀, hunit, S, hS, hsupp, hper, hform⟩ := horth _ hp
    obtain ⟨P₀, hP₀, hP₀', hux, hud, hmean⟩ := hun k₀ ⟨x₀, hx₀⟩
    have hPS : ∀ a, P₀ a = S *ᵥ P b a := fun a => funext fun j => (hP₀ a j).trans (hper a j).symm
    obtain ⟨t, ht, htS⟩ := GlobalTheory.T.triangular_frame_change_of_triangular_period E H Dw l Xo c σ g e F _ (P b) P₀ S (y b) ((U σ).un k₀ ⟨x₀, hx₀⟩) hp hP₀' hPS hsupp
      (hyP b (hs₂ hb)).1 hux (hyP b (hs₂ hb)).2 hud
    have hfn := hpin.1 σ hσ k₀ ⟨x₀, hx₀⟩ hunit t (y b) ht
    refine ⟨S, ⟨hS, hsupp, ?_⟩, fun j => ?_, ?_⟩
    · refine GlobalTheory.UnitDet.eq_of_im_hermForm_eq _ hp.2.2.2.1 _ _ ?_
      rintro _ ⟨v, rfl⟩ _ ⟨w, rfl⟩
      rw [← GlobalTheory.UnitDet.hermForm_mulVec, hform, (hAH b hb).1]
    · rw [hfn, ← htS j]
      rfl
    · obtain ⟨hxx, -, pm, p1, p2, p3⟩ := ht
      have hbc : SecBC (RingHom.id ℂ) (toC (t none : CAt σ)) ((U σ).un k₀ ⟨x₀, hx₀⟩).x (y b).x
          ((U σ).un k₀ ⟨x₀, hx₀⟩).s (y b).s := ⟨pm, p1, p2.trans (by rw [GlobalTheory.Frames.SecCalc.spMap_id']; exact (Category.comp_id _).symm), p3⟩
      have h1 := GlobalTheory.T.appellHumbertMeanSquare_eq_of_proportional_sections E H Dw l Xo _ g _ F _ P₀ (P b) S _ _ _ _ _ 1 (μ b) hP₀' hp hPS hux hxx hbc (hmean hunit)
        (hAH b hb).2
      rw [hfn, h1, mul_one, Real.sqrt_sq (norm_nonneg _)]
      exact mul_one _
  choose! S hS hlie hgen using key
  refine ContinuousAt.continuousWithinAt (ContinuousOn.continuousAt (s := B₂) ?_ (hB₂.mem_nhds hb₂))
  cases i with
  | none => exact hμ.sqrt.congr hgen
  | some s =>
    obtain ⟨j, rfl⟩ := e.surjective s
    refine ((GlobalTheory.T.continuousOn_norm_diag_of_triangular_factor g (E →+* ℂ) _ (fun j => (e j).1) (fun j => (e j).2) d B₂ S Hm (fun j j' h1 h2 => ?_) hd hHm hS
      j).mul continuousOn_const).congr fun b hb => hlie b hb j
    exact e.injective (Sigma.ext h1 ((Fin.heq_ext_iff (by rw [h1])).2 h2))
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameNormsContinuousOnHolomorphicFramedFamilyStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameNorm GlobalTheory.Reg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameNorms_continuousOn_holomorphic_framedFamily : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → ∀ (xR : ℝ) (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ), 0 < xR → FnPin U xR fn → ∀ σ, Formalism.L2.PjFree.GoodEmb c σ → ∀ (A : Type) [CommRing A] [Algebra c.F A] (yA : FrPt Xo c A) (m : ℕ) (B : Set (Fin m → ℂ)) (φ : (Fin m → ℂ) → (A →ₐ[c.F] CAt σ)) (y : (Fin m → ℂ) → FrPt Xo c (CAt σ)), IsOpen B → (∀ a, DifferentiableOn ℂ (fun b => Formalism.L2.PjFree.toC (φ b a)) B) → (∀ b ∈ B, FrMap (φ b) yA (y b)) → ∀ i, ContinuousOn (fun b => |fn σ (y b) i|) B := by
  first | exact @GlobalTheory.FrameNorm.fn_continuousOn_hol | exact GlobalTheory.FrameNorm.fn_continuousOn_hol | (intros; apply GlobalTheory.FrameNorm.fn_continuousOn_hol <;> assumption)
end
