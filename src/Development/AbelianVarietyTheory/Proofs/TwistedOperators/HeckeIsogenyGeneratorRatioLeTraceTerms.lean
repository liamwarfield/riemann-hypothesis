module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeThetaValueIdentityUnitFrames

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeIsogenyGeneratorRatioPointwiseBound
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeIsogenyGeneratorRatioPointwiseBound
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
open GlobalTheory.HkFam (admitted)

noncomputable section

namespace GlobalTheory.HeckeGenBound

theorem norm_le_of_valueId {g n : ℕ} (Hm Hm' : Matrix (Fin g) (Fin g) ℂ) (hH' : Hm'.IsHermitian)
    (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (p : ℕ)
    (hHH : ∀ z w, hermForm Hm' (h z) (h w) = ((p : ℂ) ^ 2) * hermForm Hm z w)
    (θ θ' f : (Fin g → ℂ) → ℂ) (T : ℂ) (wm : Fin n → (Fin g → ℂ)) (w : Fin g → ℂ)
    (hf : f (h w) ≠ 0)
    (hfa : ∀ m, ‖f (h w)‖ = Real.exp (Real.pi * (hermForm Hm' (h w) (h (wm m))).re +
      Real.pi / 2 * (hermForm Hm' (h (wm m)) (h (wm m))).re) * ‖f (h w + h (wm m))‖)
    (hid : T * θ' (h w) * f (h w) = ∑ m, θ ((p : ℂ) • (w + wm m)) * f (h w + h (wm m))) :
    ‖T‖ * (‖θ' (h w)‖ * Real.exp (-(Real.pi / 2) * (hermForm Hm' (h w) (h w)).re)) ≤
      ∑ m, ‖θ ((p : ℂ) • w + (p : ℂ) • wm m)‖ * Real.exp (-(Real.pi / 2) *
        (hermForm Hm ((p : ℂ) • w + (p : ℂ) • wm m) ((p : ℂ) • w + (p : ℂ) • wm m)).re) := by
  have hF : 0 < ‖f (h w)‖ := norm_pos_iff.2 hf
  have hs : star (p : ℂ) = p := by simp
  have key : ∀ m, ‖f (h w + h (wm m))‖ * Real.exp (-(Real.pi / 2) * (hermForm Hm' (h w) (h w)).re) =
      ‖f (h w)‖ * Real.exp (-(Real.pi / 2) *
        (hermForm Hm ((p : ℂ) • w + (p : ℂ) • wm m) ((p : ℂ) • w + (p : ℂ) • wm m)).re) := by
    intro m
    have e1 : hermForm Hm ((p : ℂ) • w + (p : ℂ) • wm m) ((p : ℂ) • w + (p : ℂ) • wm m) =
        hermForm Hm' (h w + h (wm m)) (h w + h (wm m)) := by
      rw [← map_add (f := _), hHH, ← smul_add, GlobalTheory.UnitFrameGen.hermForm_smul_left,
        GlobalTheory.UnitFrameGen.hermForm_smul_right, hs]
      ring
    rw [e1, hfa m, GlobalTheory.UnitFrameGen.hermForm_add_left, GlobalTheory.UnitFrameGen.hermForm_add_right,
      GlobalTheory.UnitFrameGen.hermForm_add_right]
    simp only [Complex.add_re, GlobalTheory.UnitFrameGen.hermForm_swap_re hH' (h (wm m)) (h w)]
    rw [mul_comm (Real.exp _) ‖_‖, _root_.mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have h1 : ‖T‖ * ‖θ' (h w)‖ * ‖f (h w)‖ ≤
      ∑ m, ‖θ ((p : ℂ) • (w + wm m))‖ * ‖f (h w + h (wm m))‖ := by
    rw [← norm_mul, ← norm_mul, hid]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    simp only [norm_mul]
  refine le_of_mul_le_mul_right ?_ hF
  calc ‖T‖ * (‖θ' (h w)‖ * Real.exp (-(Real.pi / 2) * (hermForm Hm' (h w) (h w)).re)) * ‖f (h w)‖
      = (‖T‖ * ‖θ' (h w)‖ * ‖f (h w)‖) * Real.exp (-(Real.pi / 2) * (hermForm Hm' (h w) (h w)).re) := by ring
    _ ≤ (∑ m, ‖θ ((p : ℂ) • (w + wm m))‖ * ‖f (h w + h (wm m))‖) *
        Real.exp (-(Real.pi / 2) * (hermForm Hm' (h w) (h w)).re) :=
      mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = ∑ m, ‖θ ((p : ℂ) • w + (p : ℂ) • wm m)‖ * (‖f (h w + h (wm m))‖ *
        Real.exp (-(Real.pi / 2) * (hermForm Hm' (h w) (h w)).re)) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [smul_add]; ring
    _ = _ := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [key m]; ring

theorem exists_pointwise_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (P : Ideal (𝓞 E)) (p i : ℕ) (k k' : U.Comp) (x : (U.X k).dom) (x' : (U.X k').dom) (C : Subgroup (Over.mk (U.un k x).x ⟶ Xo.univ.t.G)) (z : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ), admitted l P p → Xo.univ.t.HeckeKer (Over.mk (U.un k x).x) Dw P p i C → HkPtC p (U.un k x) C z → FrBor t (U.un k' x') z → IsUnitFr (U.X k) x.1 → IsUnitFr (U.X k') x'.1 → ∃ (g : ℕ) (Λ Λ' : AddSubgroup (Fin g → ℂ)) (Fd Fd' : Set (Fin g → ℂ)) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (u u' : (Fin g → ℂ) → ℝ) (v : Fin (Ideal.absNorm P ^ i) → (Fin g → ℂ)), Countable Λ ∧ Countable Λ' ∧ MeasureTheory.IsAddFundamentalDomain Λ Fd MeasureTheory.volume ∧ MeasureTheory.IsAddFundamentalDomain Λ' Fd' MeasureTheory.volume ∧ (∀ a ∈ Λ, h a ∈ Λ') ∧ (∀ z, 0 ≤ u z) ∧ (∀ z, 0 ≤ u' z) ∧ (∀ a ∈ Λ, ∀ z, u (z + a) = u z) ∧ (∀ a ∈ Λ', ∀ z, u' (z + a) = u' z) ∧ (∫ z in Fd, u z ^ 2) / (MeasureTheory.volume Fd).toReal = 1 ∧ (∫ z in Fd', u' z ^ 2) / (MeasureTheory.volume Fd').toReal = 1 ∧ ∀ w, cabs (t none : CAt σ) * u' (h w) ≤ ∑ m, u ((p : ℂ) • w + v m) := by
  intro E _ _ _ H Dw l Xo c σ r U hG hU P p i k k' x x' C z t hAd hK hHk hb hx hx'
  have hU0 := hU
  obtain ⟨-, -, -, -, -, g, e, F, ik, φ, -, hP⟩ := hU
  obtain ⟨Pm, -, hp, hu, -, hA⟩ := hP k x
  obtain ⟨Pm', -, hp', hu', -, hA'⟩ := hP k' x'
  obtain ⟨Hm, χ, fr, θ, Fd, hH, hpos, him, hd, hn, hc, h0, ha, hv, hF, hI⟩ := hA hx
  obtain ⟨Hm', χ', fr', θ', Fd', hH', hpos', him', hd', hn', hc', h0', ha', hv', hF', hI'⟩ := hA' hx'
  obtain ⟨h, wm, hlat, hHH, hwm, hid⟩ := GlobalTheory.T.hecke_theta_value_identity_unitFrames E H Dw l Xo c σ r U hG hU0 P p i k k' x x' C z t hAd hK hHk hb
    g e F ik Pm Pm' hp hp' hu hu' Hm χ fr θ hH hpos him hd hn hc h0 ha hv Hm' χ' fr' θ' hH' hpos' him' hd' hn' hc'
    h0' ha' hv'
  clear hP

  have per : ∀ (kk : U.Comp) (xx : (U.X kk).dom) (Q : (F.Di (ik kk)).La →+ (Fin g → ℂ))
      (Hq : Matrix (Fin g) (Fin g) ℂ) (χq : (Fin g → ℂ) → ℂ) (frq : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ)
      (θq : (Fin g → ℂ) → ℂ),
      IsPeriod (F.Di (ik kk)) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) Q → (U.un kk xx).x = F.u (ik kk) Q →
      Hq.IsHermitian →
      (∀ j z, ⊤ ≤ (F.ex (ik kk) Q z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → frq j z ≠ 0) →
      (∀ a j z, ‖χq (Q a)‖ = 1 ∧ (⊤ ≤ (F.ex (ik kk) Q z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
        frq j z = χq (Q a) * Complex.exp (Real.pi * hermForm Hq z (Q a) +
          Real.pi / 2 * hermForm Hq (Q a) (Q a)) * frq j (z + Q a))) →
      (∀ j z (pt : Sp ℂ ⟶ Gx (U.un kk xx).x),
        pt ≫ Formalism.L2.PjFree.gxFst (U.un kk xx).x = (F.ex (ik kk) Q z).left →
        pt ≫ Formalism.L2.PjFree.gxSnd (U.un kk xx).x = 𝟙 (Sp ℂ) →
        ⊤ ≤ (F.ex (ik kk) Q z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
        valAt' pt ((PPx (U.un kk xx).x).U (fun _ => j)) ((U.un kk xx).s.f (fun _ => j)) = θq z * frq j z) →
      ∀ a ∈ Q.range, ∀ z, ‖θq (z + a)‖ * Real.exp (-(Real.pi / 2) * (hermForm Hq (z + a) (z + a)).re) =
        ‖θq z‖ * Real.exp (-(Real.pi / 2) * (hermForm Hq z z).re) := by
    intro kk xx Q Hq χq frq θq hQ hQu hHq hnq haq hvq
    have hexp : ∀ a ∈ Q.range, ∀ z, F.ex (ik kk) Q (z + a) = F.ex (ik kk) Q z := fun a ha z => by
      rw [F.ex_add (ik kk) Q hQ, (F.ex_ker (ik kk) Q hQ a).2 ha]
      exact @_root_.mul_one _ (CategoryTheory.Hom.monoid).toMulOneClass _
    have hw0 : ∀ z, (F.ex (ik kk) Q z).left ≫ Xo.univ.t.G.hom = ((U.un kk xx).x : Sp ℂ ⟶ Xo.X) := fun z =>
      (Over.w (F.ex (ik kk) Q z)).trans hQu.symm
    intro a ha z
    obtain ⟨j, hj⟩ := GlobalTheory.ThetaPtChg.exists_chart_point Xo.univ.t.PP.isLB (F.ex (ik kk) Q z).left
    have hj' : ⊤ ≤ (F.ex (ik kk) Q (z + a)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := by rw [hexp a ha]; exact hj
    let q : Over.mk ((U.un kk xx).x : Sp ℂ ⟶ Xo.X) ⟶ Xo.univ.t.G := Over.homMk (F.ex (ik kk) Q z).left (hw0 z)
    have e1 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_snd (𝟙 _) q)
    have e2 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_fst (𝟙 _) q)
    have v1 := hvq j z _ e1 e2 hj
    have v2 := hvq j (z + a) _ (by rw [hexp a ha]; exact e1) e2 hj'
    have hm : ‖frq j z‖ = Real.exp (Real.pi * (hermForm Hq z a).re + Real.pi / 2 * (hermForm Hq a a).re) *
        ‖frq j (z + a)‖ := by
      obtain ⟨b, rfl⟩ := ha
      exact GlobalTheory.UnitFrameGen.norm_factor Hq _ _ _ _ _ (haq b j z).1 ((haq b j z).2 hj)
    have hsq := GlobalTheory.UnitFrameGen.normSq_periodic hHq _ _ _ _ z a (hnq j _ hj') (v2.symm.trans v1) hm
    have hsq' : ∀ w : Fin g → ℂ, (‖θq w‖ * Real.exp (-(Real.pi / 2) * (hermForm Hq w w).re)) ^ 2 =
        ‖θq w‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hq w w).re) := fun w => by
      rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
    refine (pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).1 ?_
    rw [hsq', hsq', hsq]
  have hsq' : ∀ (Hq : Matrix (Fin g) (Fin g) ℂ) (θq : (Fin g → ℂ) → ℂ) (w : Fin g → ℂ),
      (‖θq w‖ * Real.exp (-(Real.pi / 2) * (hermForm Hq w w).re)) ^ 2 =
        ‖θq w‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hq w w).re) := fun Hq θq w => by
    rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
  refine ⟨g, Pm.range, Pm'.range, Fd, Fd', h, fun z => ‖θ z‖ * Real.exp (-(Real.pi / 2) * (hermForm Hm z z).re),
    fun z => ‖θ' z‖ * Real.exp (-(Real.pi / 2) * (hermForm Hm' z z).re), fun m => (p : ℂ) • wm m,
    ?_, ?_, hF, hF', ?_, fun z => by positivity, fun z => by positivity, ?_, ?_, ?_, ?_, ?_⟩
  · haveI := hp.2.2.1
    exact TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  · haveI := hp'.2.2.1
    exact TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  · rintro _ ⟨a, rfl⟩
    obtain ⟨b, hb'⟩ := hlat a
    exact ⟨b, hb'.symm⟩
  · intro a ha0 z
    exact per k x Pm Hm χ fr θ hp hu hH hn ha hv a ha0 z
  · intro a ha0 z
    exact per k' x' Pm' Hm' χ' fr' θ' hp' hu' hH' hn' ha' hv' a ha0 z
  · simp only [hsq']
    exact hI
  · simp only [hsq']
    exact hI'
  · intro w
    obtain ⟨j, hj, hval⟩ := hid w
    have hfa : ∀ m, ‖fr' j (h w)‖ = Real.exp (Real.pi * (hermForm Hm' (h w) (h (wm m))).re +
        Real.pi / 2 * (hermForm Hm' (h (wm m)) (h (wm m))).re) * ‖fr' j (h w + h (wm m))‖ := fun m => by
      obtain ⟨b, hb'⟩ := hwm m
      rw [hb']
      exact GlobalTheory.UnitFrameGen.norm_factor Hm' _ _ _ _ _ (ha' b j (h w)).1 ((ha' b j (h w)).2 hj)
    have := norm_le_of_valueId Hm Hm' hH' h p hHH θ θ' (fr' j) (Formalism.L2.PjFree.toC (t none : CAt σ)) wm w
      (hn' j _ hj) hfa hval
    exact this

end GlobalTheory.HeckeGenBound
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeIsogenyGeneratorRatioPointwiseBoundStatement
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
open GlobalTheory.HkFam (admitted)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeIsogeny_generatorRatio_pointwise_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (P : Ideal (𝓞 E)) (p i : ℕ) (k k' : U.Comp) (x : (U.X k).dom) (x' : (U.X k').dom) (C : Subgroup (Over.mk (U.un k x).x ⟶ Xo.univ.t.G)) (z : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ), admitted l P p → Xo.univ.t.HeckeKer (Over.mk (U.un k x).x) Dw P p i C → HkPtC p (U.un k x) C z → FrBor t (U.un k' x') z → IsUnitFr (U.X k) x.1 → IsUnitFr (U.X k') x'.1 → ∃ (g : ℕ) (Λ Λ' : AddSubgroup (Fin g → ℂ)) (Fd Fd' : Set (Fin g → ℂ)) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (u u' : (Fin g → ℂ) → ℝ) (v : Fin (Ideal.absNorm P ^ i) → (Fin g → ℂ)), Countable Λ ∧ Countable Λ' ∧ MeasureTheory.IsAddFundamentalDomain Λ Fd MeasureTheory.volume ∧ MeasureTheory.IsAddFundamentalDomain Λ' Fd' MeasureTheory.volume ∧ (∀ a ∈ Λ, h a ∈ Λ') ∧ (∀ z, 0 ≤ u z) ∧ (∀ z, 0 ≤ u' z) ∧ (∀ a ∈ Λ, ∀ z, u (z + a) = u z) ∧ (∀ a ∈ Λ', ∀ z, u' (z + a) = u' z) ∧ (∫ z in Fd, u z ^ 2) / (MeasureTheory.volume Fd).toReal = 1 ∧ (∫ z in Fd', u' z ^ 2) / (MeasureTheory.volume Fd').toReal = 1 ∧ ∀ w, cabs (t none : CAt σ) * u' (h w) ≤ ∑ m, u ((p : ℂ) • w + v m) := by
  first | exact @GlobalTheory.HeckeGenBound.exists_pointwise_bound | exact GlobalTheory.HeckeGenBound.exists_pointwise_bound | (intros; apply GlobalTheory.HeckeGenBound.exists_pointwise_bound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodicThetaNormMeanFactorLe
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AffineChangeFundamentalDomainMeanPeriodic
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AffineChangeFundamentalDomainMeanPeriodic
open MeasureTheory

noncomputable section

namespace GlobalTheory.AffineMean

theorem affine_fundamentalDomain_mean :
    ∀ (g : ℕ) (Λ' Λ₁ : AddSubgroup (Fin g → ℂ)) (Fd' : Set (Fin g → ℂ)) (L : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ))
      (c : Fin g → ℂ) (f : (Fin g → ℂ) → ℝ), Countable Λ' → (∀ z, L z ∈ Λ' ↔ z ∈ Λ₁) →
      IsAddFundamentalDomain Λ' Fd' volume → (∀ a ∈ Λ', ∀ z, f (z + a) = f z) →
      (∫ z in Fd', f z) / (volume Fd').toReal = 1 →
      IsAddFundamentalDomain Λ₁ ((fun z => L z + c) ⁻¹' Fd') volume ∧
        (∫ z in (fun z => L z + c) ⁻¹' Fd', f (L z + c)) / (volume ((fun z => L z + c) ⁻¹' Fd')).toReal = 1 := by
  intro g Λ' Λ₁ Fd' L c f hcount hΛ hF' _ hmean
  let L' : (Fin g → ℂ) ≃ₗ[ℝ] (Fin g → ℂ) := L.restrictScalars ℝ
  have hL : ∀ z, L' z = L z := fun z => rfl
  let e : (Fin g → ℂ) ≃ᵐ (Fin g → ℂ) :=
    (L'.toContinuousLinearEquiv.toHomeomorph.trans (Homeomorph.addRight c)).toMeasurableEquiv
  have he : ∀ z, e z = L z + c := fun z => rfl
  have hpre : (fun z => L z + c) ⁻¹' Fd' = e ⁻¹' Fd' := rfl
  have hd : LinearMap.det (L' : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ)) ≠ 0 := (LinearEquiv.isUnit_det' L').ne_zero
  have hmapL : Measure.map L' volume =
      ENNReal.ofReal |(LinearMap.det (L' : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ)))⁻¹| • volume :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume hd
  have hc : 0 < |(LinearMap.det (L' : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ)))⁻¹| := abs_pos.2 (inv_ne_zero hd)
  generalize |(LinearMap.det (L' : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ)))⁻¹| = k at hmapL hc
  have hmap : Measure.map e volume = ENNReal.ofReal k • volume := by
    have h1 : (e : (Fin g → ℂ) → (Fin g → ℂ)) = (fun z => z + c) ∘ (L' : (Fin g → ℂ) → (Fin g → ℂ)) := rfl
    have hLm : Measurable (L' : (Fin g → ℂ) → (Fin g → ℂ)) :=
      L'.toContinuousLinearEquiv.continuous.measurable
    rw [h1, ← Measure.map_map (measurable_add_const c) hLm, hmapL, Measure.map_smul, map_add_right_eq_self]
    exact (measurable_add_const c).aemeasurable
  have hq : Measure.QuasiMeasurePreserving e volume volume :=
    ⟨e.measurable.aemeasurable, by rw [hmap]; exact Measure.smul_absolutelyContinuous⟩
  let ε : Λ' → Λ₁ := fun a => ⟨L.symm a, (hΛ _).1 (by rw [L.apply_symm_apply]; exact a.2)⟩
  have hε : Function.Bijective ε :=
    ⟨fun a b hab => Subtype.ext (L.symm.injective (congrArg Subtype.val hab)),
      fun a => ⟨⟨L a, (hΛ _).2 a.2⟩, Subtype.ext (L.symm_apply_apply _)⟩⟩
  have hF2 : IsAddFundamentalDomain Λ₁ (e ⁻¹' Fd') volume :=
    hF'.preimage_of_equiv hq hε fun a z => by
      change L (L.symm (a : Fin g → ℂ) + z) + c = (a : Fin g → ℂ) + (L z + c)
      rw [map_add (f := _), L.apply_symm_apply, add_assoc]
  have i2 : ∫ z in e ⁻¹' Fd', f (e z) = k * ∫ z in Fd', f z := by
    have := setIntegral_map_equiv (μ := volume) e f Fd'
    rw [hmap, Measure.restrict_smul, integral_smul_measure, ENNReal.toReal_ofReal hc.le, smul_eq_mul] at this
    exact this.symm
  have i3 : (volume (e ⁻¹' Fd')).toReal = k * (volume Fd').toReal := by
    rw [← e.map_apply, hmap, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc.le]
  refine ⟨hpre ▸ hF2, ?_⟩
  rw [hpre]
  have i2' : ∫ z in e ⁻¹' Fd', f (L z + c) = k * ∫ z in Fd', f z := i2
  rw [i2', i3, mul_div_mul_left _ _ hc.ne', hmean]

end GlobalTheory.AffineMean
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AffineChangeFundamentalDomainMeanPeriodicStatement
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affine_change_fundamentalDomain_mean_periodic : ∀ (g : ℕ) (Λ' Λ₁ : AddSubgroup (Fin g → ℂ)) (Fd' : Set (Fin g → ℂ)) (L : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (c : Fin g → ℂ) (f : (Fin g → ℂ) → ℝ), Countable Λ' → (∀ z, L z ∈ Λ' ↔ z ∈ Λ₁) → IsAddFundamentalDomain Λ' Fd' volume → (∀ a ∈ Λ', ∀ z, f (z + a) = f z) → (∫ z in Fd', f z) / (volume Fd').toReal = 1 → IsAddFundamentalDomain Λ₁ ((fun z => L z + c) ⁻¹' Fd') volume ∧ (∫ z in (fun z => L z + c) ⁻¹' Fd', f (L z + c)) / (volume ((fun z => L z + c) ⁻¹' Fd')).toReal = 1 := by
  first | exact @GlobalTheory.AffineMean.affine_fundamentalDomain_mean | exact GlobalTheory.AffineMean.affine_fundamentalDomain_mean | (intros; apply GlobalTheory.AffineMean.affine_fundamentalDomain_mean <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeanFundamentalDomainOfLe
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeanFundamentalDomainOfLe
open MeasureTheory
open scoped Pointwise

namespace GlobalTheory

theorem mean_fundamentalDomain_of_le : ∀ (g : ℕ) (Λ Λ₁ : AddSubgroup (Fin g → ℂ)) (Fd D₁ : Set (Fin g → ℂ)) (f : (Fin g → ℂ) → ℝ), Countable Λ₁ → Λ ≤ Λ₁ → IsAddFundamentalDomain Λ Fd volume → IsAddFundamentalDomain Λ₁ D₁ volume → volume Fd ≠ ⊤ → (∀ a ∈ Λ₁, ∀ z, f (z + a) = f z) → (∫ z in D₁, f z) / (volume D₁).toReal = 1 → IntegrableOn f Fd volume ∧ (∫ z in Fd, f z) / (volume Fd).toReal = 1 := by
  intro g Λ Λ₁ Fd D₁ f hc hle hFd hD₁ hfin hper hmean
  have hb : (volume D₁).toReal ≠ 0 := by
    intro h; rw [h, div_zero] at hmean; exact zero_ne_one hmean
  have hab : ∫ z in D₁, f z = (volume D₁).toReal := (div_eq_one_iff_eq hb).1 hmean
  have hint : IntegrableOn f D₁ volume := by
    by_contra h
    rw [integral_undef h] at hab; exact hb hab.symm
  have hD0 : volume D₁ ≠ 0 := fun h => hb (by simp [h])
  have hinv₁ : ∀ (γ : Λ₁) (x : Fin g → ℂ), f (γ +ᵥ x) = f x := fun γ x => by
    show f ((γ : Fin g → ℂ) + x) = f x
    rw [add_comm]; exact hper _ γ.2 x
  have hinv : ∀ (l : Λ) (x : Fin g → ℂ), f (l +ᵥ x) = f x := fun l x => by
    show f ((l : Fin g → ℂ) + x) = f x
    rw [add_comm]; exact hper _ (hle l.2) x
  let Q := Λ₁ ⧸ Λ.addSubgroupOf Λ₁
  haveI : Countable Λ := (AddSubgroup.inclusion_injective hle).countable
  haveI : Countable Q := (QuotientAddGroup.mk_surjective (s := Λ.addSubgroupOf Λ₁)).countable
  let rep : Q → Λ₁ := fun q => q.out
  have hrep : ∀ q : Q, (QuotientAddGroup.mk (rep q) : Q) = q := fun q => QuotientAddGroup.out_eq' q
  have hrepinj : Function.Injective rep := fun q q' h => by rw [← hrep q, ← hrep q', h]
  let s : Q → Set (Fin g → ℂ) := fun q => ((rep q : Λ₁) : Fin g → ℂ) +ᵥ D₁
  have hs : ∀ q, IsAddFundamentalDomain Λ₁ (s q) volume := fun q => hD₁.vadd_of_comm _
  have hsd : Pairwise (Function.onFun (AEDisjoint volume) s) := fun q q' hne => hD₁.aedisjoint (hrepinj.ne hne)
  let E := ⋃ q, s q
  have key : ∀ (l : Λ) (q : Q), l +ᵥ s q =
      ((⟨(l : Fin g → ℂ) + rep q, Λ₁.add_mem (hle l.2) (rep q).2⟩ : Λ₁) +ᵥ D₁) := by
    intro l q; ext x
    simp only [s, Set.mem_vadd_set]
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      refine ⟨z, hz, ?_⟩
      show ((l : Fin g → ℂ) + rep q) + z = (l : Fin g → ℂ) + ((rep q : Fin g → ℂ) + z)
      abel
    · rintro ⟨z, hz, rfl⟩
      refine ⟨(rep q : Fin g → ℂ) +ᵥ z, ⟨z, hz, rfl⟩, ?_⟩
      show (l : Fin g → ℂ) + ((rep q : Fin g → ℂ) + z) = ((l : Fin g → ℂ) + rep q) + z
      abel
  have hE : IsAddFundamentalDomain Λ E volume := by
    refine ⟨NullMeasurableSet.iUnion fun q => (hs q).nullMeasurableSet, ?_, ?_⟩
    · filter_upwards [hD₁.ae_covers] with x ⟨γ, hγ⟩
      have h1 : (QuotientAddGroup.mk (-γ) : Q) = QuotientAddGroup.mk (rep (QuotientAddGroup.mk (-γ))) :=
        (hrep _).symm
      rw [QuotientAddGroup.eq, neg_neg, AddSubgroup.mem_addSubgroupOf] at h1
      refine ⟨⟨_, h1⟩, Set.mem_iUnion.2 ⟨QuotientAddGroup.mk (-γ), ?_⟩⟩
      refine Set.mem_vadd_set.2 ⟨γ +ᵥ x, hγ, ?_⟩
      show (rep (QuotientAddGroup.mk (-γ)) : Fin g → ℂ) + ((γ : Fin g → ℂ) + x) =
        ((γ + rep (QuotientAddGroup.mk (-γ)) : Λ₁) : Fin g → ℂ) + x
      push_cast; abel
    · intro l l' hne
      simp only [Function.onFun, E, Set.vadd_set_iUnion]
      rw [AEDisjoint.iUnion_left_iff]; intro q
      rw [AEDisjoint.iUnion_right_iff]; intro q'
      rw [key, key]
      apply hD₁.aedisjoint
      intro heq
      have hv : (l : Fin g → ℂ) + rep q = l' + rep q' := congrArg Subtype.val heq
      have hqq : q = q' := by
        rw [← hrep q, ← hrep q', QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
        have : ((-rep q + rep q' : Λ₁) : Fin g → ℂ) = (l : Fin g → ℂ) - l' := by
          push_cast
          calc -(rep q : Fin g → ℂ) + rep q' = -(rep q : Fin g → ℂ) + rep q' + ((l : Fin g → ℂ) + rep q - (l' + rep q')) := by
                rw [hv, sub_self, add_zero]
            _ = (l : Fin g → ℂ) - l' := by abel
        rw [this]; exact Λ.sub_mem l.2 l'.2
      subst hqq
      exact hne (Subtype.ext (add_right_cancel hv))
  have hvol : ∀ q, volume (s q) = volume D₁ := fun q => (hs q).measure_eq hD₁
  have hvolE : volume E = ∑' _ : Q, volume D₁ := by
    show volume (⋃ q, s q) = _
    rw [measure_iUnion₀ hsd fun q => (hs q).nullMeasurableSet]
    simp only [hvol]
  have hEFd : volume E = volume Fd := hE.measure_eq hFd
  haveI : Finite Q := by
    by_contra hinf
    rw [not_finite_iff_infinite] at hinf
    exact hfin (by rw [← hEFd, hvolE]; exact ENNReal.tsum_const_eq_top_of_ne_zero hD0)
  haveI := Fintype.ofFinite Q
  have hn : (Fintype.card Q : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hintE : IntegrableOn f E volume :=
    integrableOn_finite_iUnion.2 fun q => ((hs q).integrableOn_iff hD₁ hinv₁).2 hint
  have hsi : ∀ q, ∫ z in s q, f z = ∫ z in D₁, f z := fun q => (hs q).setIntegral_eq hD₁ hinv₁
  have hIE : ∫ z in E, f z = Fintype.card Q * ∫ z in D₁, f z := by
    show ∫ z in ⋃ q, s q, f z = _
    rw [integral_iUnion_ae (fun q => (hs q).nullMeasurableSet) hsd hintE, tsum_fintype]
    simp only [hsi, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  refine ⟨(hFd.integrableOn_iff hE hinv).2 hintE, ?_⟩
  rw [hFd.setIntegral_eq hE hinv, ← hEFd, hIE, hvolE, tsum_fintype, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast, hab]
  field_simp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeanFundamentalDomainOfLeStatement
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mean_fundamentalDomain_eq_one_of_le : ∀ (g : ℕ) (Λ Λ₁ : AddSubgroup (Fin g → ℂ)) (Fd D₁ : Set (Fin g → ℂ)) (f : (Fin g → ℂ) → ℝ), Countable Λ₁ → Λ ≤ Λ₁ → IsAddFundamentalDomain Λ Fd volume → IsAddFundamentalDomain Λ₁ D₁ volume → volume Fd ≠ ⊤ → (∀ a ∈ Λ₁, ∀ z, f (z + a) = f z) → (∫ z in D₁, f z) / (volume D₁).toReal = 1 → IntegrableOn f Fd volume ∧ (∫ z in Fd, f z) / (volume Fd).toReal = 1 := by
  first | exact @GlobalTheory.mean_fundamentalDomain_of_le | exact GlobalTheory.mean_fundamentalDomain_of_le | (intros; apply GlobalTheory.mean_fundamentalDomain_of_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodicThetaNormMeanFactorLe
open MeasureTheory

namespace GlobalTheory.PeriodicMean

theorem mean_factor_le : ∀ (g : ℕ) (Λ Λ' : AddSubgroup (Fin g → ℂ)) (Fd Fd' : Set (Fin g → ℂ)) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (u u' : (Fin g → ℂ) → ℝ) (p n : ℕ) (v : Fin n → (Fin g → ℂ)) (T : ℝ), Countable Λ → Countable Λ' → MeasureTheory.IsAddFundamentalDomain Λ Fd MeasureTheory.volume → MeasureTheory.IsAddFundamentalDomain Λ' Fd' MeasureTheory.volume → 0 < p → (∀ a ∈ Λ, h a ∈ Λ') → (∀ z, 0 ≤ u z) → (∀ z, 0 ≤ u' z) → (∀ a ∈ Λ, ∀ z, u (z + a) = u z) → (∀ a ∈ Λ', ∀ z, u' (z + a) = u' z) → (∫ z in Fd, u z ^ 2) / (MeasureTheory.volume Fd).toReal = 1 → (∫ z in Fd', u' z ^ 2) / (MeasureTheory.volume Fd').toReal = 1 → (∀ z, T * u' (h z) ≤ ∑ m, u ((p : ℂ) • z + v m)) → T ≤ n := by
  intro g Λ Λ' Fd Fd' h u u' p n v T hΛc hΛ'c hF hF' hp hh hu hu' hpu hpu' hm hm' hT

  have hV : 0 < (volume Fd).toReal := by
    rcases (ENNReal.toReal_nonneg (a := volume Fd)).lt_or_eq with h0 | h0
    · exact h0
    · rw [← h0, div_zero] at hm; exact absurd hm zero_ne_one
  have hVt : volume Fd ≠ ⊤ := fun h0 => by simp [h0] at hV

  have hA1 : IntegrableOn (fun z => u' (h z) ^ 2) Fd volume ∧
      (∫ z in Fd, u' (h z) ^ 2) / (volume Fd).toReal = 1 := by
    let Λ₁ : AddSubgroup (Fin g → ℂ) := Λ'.comap (h.toLinearMap.toAddMonoidHom)
    have hc : Countable Λ₁ := by
      have : Function.Injective (fun x : Λ₁ => (⟨h x, x.2⟩ : Λ')) := fun x y hxy =>
        Subtype.ext (h.injective (congrArg Subtype.val hxy))
      exact this.countable
    obtain ⟨hD, hmD⟩ := GlobalTheory.T.affine_change_fundamentalDomain_mean_periodic g Λ' Λ₁ Fd' h 0 (fun z => u' z ^ 2) hΛ'c (fun z => Iff.rfl) hF'
      (fun a ha z => by simp only [hpu' a ha z]) hm'
    exact GlobalTheory.T.mean_fundamentalDomain_eq_one_of_le g Λ Λ₁ Fd _ (fun z => u' (h z) ^ 2) hc (fun a ha => hh a ha) hF hD hVt
      (fun a ha z => by
        have : h (z + a) = h z + h a := map_add h z a
        rw [this, hpu' (h a) ha]) (by simpa using hmD)

  have hA2 : ∀ m, IntegrableOn (fun z => u ((p : ℂ) • z + v m) ^ 2) Fd volume ∧
      (∫ z in Fd, u ((p : ℂ) • z + v m) ^ 2) / (volume Fd).toReal = 1 := by
    intro m
    have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
    let L : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) := LinearEquiv.smulOfNeZero ℂ (Fin g → ℂ) (p : ℂ) hp0
    let Λ₁ : AddSubgroup (Fin g → ℂ) := Λ.comap (L.toLinearMap.toAddMonoidHom)
    have hc : Countable Λ₁ := by
      have : Function.Injective (fun x : Λ₁ => (⟨L x, x.2⟩ : Λ)) := fun x y hxy =>
        Subtype.ext (L.injective (congrArg Subtype.val hxy))
      exact this.countable
    obtain ⟨hD, hmD⟩ := GlobalTheory.T.affine_change_fundamentalDomain_mean_periodic g Λ Λ₁ Fd L (v m) (fun z => u z ^ 2) hΛc (fun z => Iff.rfl) hF
      (fun a ha z => by simp only [hpu a ha z]) hm
    refine GlobalTheory.T.mean_fundamentalDomain_eq_one_of_le g Λ Λ₁ Fd _ (fun z => u ((p : ℂ) • z + v m) ^ 2) hc ?_ hF hD hVt ?_ hmD
    · intro a ha
      change (p : ℂ) • a ∈ Λ
      have : (p : ℂ) • a = p • a := by rw [Nat.cast_smul_eq_nsmul]
      rw [this]; exact Λ.nsmul_mem ha p
    · intro a ha z
      have ha' : (p : ℂ) • a ∈ Λ := ha
      have : (p : ℂ) • (z + a) + v m = ((p : ℂ) • z + v m) + (p : ℂ) • a := by rw [smul_add]; abel
      simp only [this, hpu _ ha']
  obtain ⟨hI1, hM1⟩ := hA1
  have hE1 : ∫ z in Fd, u' (h z) ^ 2 = (volume Fd).toReal := by
    field_simp at hM1; linarith
  have hE2 : ∀ m, ∫ z in Fd, u ((p : ℂ) • z + v m) ^ 2 = (volume Fd).toReal := fun m => by
    have := (hA2 m).2; field_simp at this; linarith
  rcases le_or_gt T 0 with hT0 | hT0
  · exact hT0.trans (Nat.cast_nonneg n)

  have hpt : ∀ z, T ^ 2 * u' (h z) ^ 2 ≤ (n : ℝ) * ∑ m, u ((p : ℂ) • z + v m) ^ 2 := by
    intro z
    have h0 : 0 ≤ T * u' (h z) := mul_nonneg hT0.le (hu' _)
    calc T ^ 2 * u' (h z) ^ 2 = (T * u' (h z)) ^ 2 := by ring
      _ ≤ (∑ m, u ((p : ℂ) • z + v m)) ^ 2 := pow_le_pow_left₀ h0 (hT z) 2
      _ ≤ (Finset.univ : Finset (Fin n)).card * ∑ m, u ((p : ℂ) • z + v m) ^ 2 := sq_sum_le_card_mul_sum_sq
      _ = (n : ℝ) * ∑ m, u ((p : ℂ) • z + v m) ^ 2 := by simp
  have hint : ∫ z in Fd, T ^ 2 * u' (h z) ^ 2 ≤ ∫ z in Fd, (n : ℝ) * ∑ m, u ((p : ℂ) • z + v m) ^ 2 := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => by positivity) ?_
      (Filter.Eventually.of_forall hpt)
    exact (integrable_finsetSum _ fun m _ => (hA2 m).1).const_mul _
  rw [integral_const_mul, integral_const_mul, integral_finsetSum _ fun m _ => (hA2 m).1, hE1] at hint
  simp only [hE2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hint
  have hT2 : T ^ 2 ≤ (n : ℝ) ^ 2 := by nlinarith
  exact abs_le_of_sq_le_sq' hT2 (Nat.cast_nonneg n) |>.2 |> fun h => h

end GlobalTheory.PeriodicMean
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodicThetaNormMeanFactorLeStatement
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodic_theta_norm_mean_factor_le : ∀ (g : ℕ) (Λ Λ' : AddSubgroup (Fin g → ℂ)) (Fd Fd' : Set (Fin g → ℂ)) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (u u' : (Fin g → ℂ) → ℝ) (p n : ℕ) (v : Fin n → (Fin g → ℂ)) (T : ℝ), Countable Λ → Countable Λ' → MeasureTheory.IsAddFundamentalDomain Λ Fd MeasureTheory.volume → MeasureTheory.IsAddFundamentalDomain Λ' Fd' MeasureTheory.volume → 0 < p → (∀ a ∈ Λ, h a ∈ Λ') → (∀ z, 0 ≤ u z) → (∀ z, 0 ≤ u' z) → (∀ a ∈ Λ, ∀ z, u (z + a) = u z) → (∀ a ∈ Λ', ∀ z, u' (z + a) = u' z) → (∫ z in Fd, u z ^ 2) / (MeasureTheory.volume Fd).toReal = 1 → (∫ z in Fd', u' z ^ 2) / (MeasureTheory.volume Fd').toReal = 1 → (∀ z, T * u' (h z) ≤ ∑ m, u ((p : ℂ) • z + v m)) → T ≤ n := by
  first | exact @GlobalTheory.PeriodicMean.mean_factor_le | exact GlobalTheory.PeriodicMean.mean_factor_le | (intros; apply GlobalTheory.PeriodicMean.mean_factor_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeIsogenyGeneratorRatioLeTraceTerms
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
open GlobalTheory.HkFam (admitted)

namespace GlobalTheory.HeckeEx

theorem cabs_gen_le_of_hkPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (P : Ideal (𝓞 E)) (p i : ℕ) (k k' : U.Comp) (x : (U.X k).dom) (x' : (U.X k').dom) (C : Subgroup (Over.mk (U.un k x).x ⟶ Xo.univ.t.G)) (z : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ), admitted l P p → Xo.univ.t.HeckeKer (Over.mk (U.un k x).x) Dw P p i C → HkPtC p (U.un k x) C z → FrBor t (U.un k' x') z → IsUnitFr (U.X k) x.1 → IsUnitFr (U.X k') x'.1 → cabs (t none : CAt σ) ≤ (Ideal.absNorm P : ℝ) ^ i := by
  intro E _ _ _ H Dw l Xo c σ r U hσ hU P p i k k' x x' C z t hA hC hz hb hx hx'
  obtain ⟨g, Λ, Λ', Fd, Fd', h, u, u', v, c1, c2, f1, f2, hh, u0, u0', up, up', m1, m1', hpt⟩ :=
    GlobalTheory.T.heckeIsogeny_generatorRatio_pointwise_bound E H Dw l Xo c σ r U hσ hU P p i k k' x x' C z t hA hC hz hb hx hx'
  exact_mod_cast GlobalTheory.T.periodic_theta_norm_mean_factor_le g Λ Λ' Fd Fd' h u u' p _ v _ c1 c2 f1 f2 hA.2.2.1.pos hh u0 u0' up up' m1 m1' hpt

end GlobalTheory.HeckeEx
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeIsogenyGeneratorRatioLeTraceTermsStatement
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
open GlobalTheory.HkFam (admitted)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeIsogeny_generatorRatio_le_traceTerms : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (P : Ideal (𝓞 E)) (p i : ℕ) (k k' : U.Comp) (x : (U.X k).dom) (x' : (U.X k').dom) (C : Subgroup (Over.mk (U.un k x).x ⟶ Xo.univ.t.G)) (z : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ), admitted l P p → Xo.univ.t.HeckeKer (Over.mk (U.un k x).x) Dw P p i C → HkPtC p (U.un k x) C z → FrBor t (U.un k' x') z → IsUnitFr (U.X k) x.1 → IsUnitFr (U.X k') x'.1 → cabs (t none : CAt σ) ≤ (Ideal.absNorm P : ℝ) ^ i := by
  first | exact @GlobalTheory.HeckeEx.cabs_gen_le_of_hkPt | exact GlobalTheory.HeckeEx.cabs_gen_le_of_hkPt | (intros; apply GlobalTheory.HeckeEx.cabs_gen_le_of_hkPt <;> assumption)
end
