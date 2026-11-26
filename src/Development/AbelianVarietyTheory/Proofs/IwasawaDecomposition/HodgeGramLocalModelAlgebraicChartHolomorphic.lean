module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicInvertibleFrameCoordinates
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricGramHolomorphicFrameForm

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAnalyticFlagDomainFrameLiftAlgebraicChart
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodMapMemberEqFramePeriodMapLinearChange
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodMapMemberEqFramePeriodMapLinearChange
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

namespace GlobalTheory.PointLift

open ReciprocityTheory.ChartRestriction.G.FD

theorem pm_lift_pointwise : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r) (W : GlobalTheory.ArcQ.UnfWit U), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → Function.Injective W.ik → ∀ (k : U.Comp) (Q : (W.F.Di (W.ik k)).La →+ (Fin W.g → ℂ)), IsPeriod (W.F.Di (W.ik k)) (fun j => Formalism.L2.PjFree.relab c σ (W.e j).1) Q → ∀ q : FrPt Xo c (Formalism.L2.Pj.CAt σ), W.F.u (W.ik k) Q = q.x → ∃ x' : (U.X k).dom, (U.un k x').x = q.x ∧ ∃ h : (Fin W.g → ℂ) ≃ₗ[ℂ] (Fin W.g → ℂ), ∀ a, Q a = h (W.Pm k x' a) := by
  intro E _ _ _ H Dw l Xo c σ r U W hσ hU hinj k Q hQ q hq
  obtain ⟨k₁, x₁, t, hB⟩ := hU.2.2.1 q
  have hx₁ : (U.un k₁ x₁).x = W.F.u (W.ik k₁) (W.Pm k₁ x₁) := (W.lie k₁ x₁).1
  have hk : k₁ = k := hinj (W.F.disj _ _ _ _ (W.period k₁ x₁) hQ (by rw [← hx₁, ← hB.1, hq]))
  subst hk
  obtain ⟨gam, h, hEF, -, -, hgh⟩ := (W.F.fibre _ Q (W.Pm k₁ x₁) hQ (W.period k₁ x₁)).1
    (by rw [hq, ← hx₁, hB.1])
  let φL : (W.F.Di (W.ik k₁)).La →ₗ[𝓞 E] (Fin r → E) := (U.X k₁).Λ.subtype ∘ₗ (W.φ k₁).toLinearMap
  have hφi : Function.Injective φL := (U.X k₁).Λ.injective_subtype.comp (W.φ k₁).injective
  have hrange : Set.range φL = ((U.X k₁).Λ : Set (Fin r → E)) := by
    ext v
    constructor
    · rintro ⟨a, rfl⟩
      exact (W.φ k₁ a).2
    · intro hv
      exact ⟨(W.φ k₁).symm ⟨v, hv⟩, by simp [φL]⟩
  have hspan : Submodule.span E (Set.range φL) = ⊤ := by rw [hrange]; exact (U.X k₁).Λ_span
  have hcc : cc (-(U.X k₁).ξ0) = -(-(U.X k₁).ξ0) := by
    have h0 := (U.X k₁).ξ0_im
    unfold cc at h0 ⊢
    rw [map_neg, h0]
  have hl : Function.Injective φL ∧ Submodule.span E (Set.range φL) = ⊤ ∧
      (∀ a b, cc ((U.X k₁).Gm a b) = (U.X k₁).Gm b a) ∧ (U.X k₁).Gm.det ≠ 0 ∧
      ∀ x y, (((W.F.Di (W.ik k₁)).EF x y : ℤ) : ℚ) =
        Algebra.trace ℚ E (-(U.X k₁).ξ0 * herm (U.X k₁).Gm (φL x) (φL y)) :=
    ⟨hφi, hspan, (U.X k₁).Gm_herm, (U.X k₁).Gm_det, fun x y => W.iso k₁ x y⟩
  obtain ⟨γ, hγh, hγφ⟩ := GlobalTheory.IsoExt.exists_unitary_of_isometry E H _ _ r (-(U.X k₁).ξ0) (U.X k₁).Gm φL φL gam
    hcc hl hl hEF
  have hinv : ∀ v : Fin r → E, ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ
      ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have hinv' : ∀ v : Fin r → E, (γ : Matrix (Fin r) (Fin r) E) *ᵥ
      (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hγi : IsUStab (U.X k₁).Gm (U.X k₁).Λ γ⁻¹ := by
    refine ⟨fun u v => ?_, fun v => ⟨fun hv => ?_, fun hv => ?_⟩⟩
    · rw [← hγh, hinv', hinv']
    · obtain ⟨b, hb⟩ : v ∈ Set.range φL := by rw [hrange]; exact hv
      have e : ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v = φL (gam.symm b) := by
        rw [← hb, ← LinearEquiv.apply_symm_apply gam b, hγφ, hinv, LinearEquiv.apply_symm_apply]
      rw [e]
      exact (W.φ k₁ (gam.symm b)).2
    · obtain ⟨a, ha⟩ : _ ∈ Set.range φL := by rw [hrange]; exact hv
      have e : v = φL (gam a) := by rw [hγφ, ha, hinv']
      rw [e]
      exact (W.φ k₁ (gam a)).2
  let x' : (U.X k₁).dom := ⟨lact γ⁻¹ x₁.1, GlobalTheory.MajInv.lact_mem_dom _ hγi x₁.2⟩
  have hPm : ∀ a, W.Pm k₁ x' a = W.Pm k₁ x₁ (gam a) := by
    intro a
    funext j
    rw [W.Pm_eq, W.Pm_eq]
    have e : (W.φ k₁ a : Fin r → E) = ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ
        (W.φ k₁ (gam a) : Fin r → E) := by
      change φL a = _ *ᵥ φL (gam a)
      rw [hγφ, hinv]
    rw [e]
    exact GlobalTheory.CongrOrbit.perFr_lact _ _ _ hγi.1 _ _ _
  have hQx : ∀ a, W.Pm k₁ x' a = h (Q a) := fun a => by rw [hPm, hgh]
  have hu : W.F.u (W.ik k₁) Q = W.F.u (W.ik k₁) (W.Pm k₁ x') :=
    (W.F.fibre _ Q (W.Pm k₁ x') hQ (W.period k₁ x')).2
      ⟨LinearEquiv.refl _ _, h, fun a b => rfl, fun a _ => ⟨0, by simp⟩, fun a => ⟨0, by simp⟩,
        fun a => hQx a⟩
  refine ⟨x', by rw [(W.lie k₁ x').1, ← hu, hq], h.symm, fun a => ?_⟩
  rw [hQx, LinearEquiv.symm_apply_apply]

end GlobalTheory.PointLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodMapMemberEqFramePeriodMapLinearChangeStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodMap_member_eq_frame_periodMap_linear_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r) (W : GlobalTheory.ArcQ.UnfWit U), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → Function.Injective W.ik → ∀ (k : U.Comp) (Q : (W.F.Di (W.ik k)).La →+ (Fin W.g → ℂ)), IsPeriod (W.F.Di (W.ik k)) (fun j => Formalism.L2.PjFree.relab c σ (W.e j).1) Q → ∀ q : FrPt Xo c (Formalism.L2.Pj.CAt σ), W.F.u (W.ik k) Q = q.x → ∃ x' : (U.X k).dom, (U.un k x').x = q.x ∧ ∃ h : (Fin W.g → ℂ) ≃ₗ[ℂ] (Fin W.g → ℂ), ∀ a, Q a = h (W.Pm k x' a) := by
  first | exact @GlobalTheory.PointLift.pm_lift_pointwise | exact GlobalTheory.PointLift.pm_lift_pointwise | (intros; apply GlobalTheory.PointLift.pm_lift_pointwise <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAnalyticFrameFamilyOfHolomorphicPeriodMaps
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAnalyticFrameFamilyOfHolomorphicPeriodMaps
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

namespace GlobalTheory.PeriodFamFrame
open ReciprocityTheory.ChartRestriction.G.FD

theorem sep_types {E : Type} [Field E] [NumberField E] {La : Type} [AddCommGroup La] [Module (𝓞 E) La]
    {g : ℕ} (ty : Fin g → (E →+* ℂ)) (G : Fin g → La → ℂ) (τ : E →+* ℂ) (c : Fin g → ℂ) (F : La → ℂ)
    (hG : ∀ j (a : 𝓞 E) v, G j (a • v) = ty j (a : E) * G j v)
    (hF : ∀ (a : 𝓞 E) v, F (a • v) = τ (a : E) * F v)
    (hsum : ∀ v, F v = ∑ j, c j * G j v) :
    ∀ v, F v = ∑ j, (if ty j = τ then c j else 0) * G j v := by
  classical
  intro v
  set H : (E →+* ℂ) → La → ℂ := fun χ w => ∑ j ∈ Finset.univ.filter (fun j => ty j = χ), c j * G j w with hH
  have hHs : ∀ χ (b : 𝓞 E) w, H χ (b • w) = χ (b : E) * H χ w := by
    intro χ b w
    simp only [hH, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [hG, (Finset.mem_filter.1 hj).2]; ring
  have hFH : ∀ w, F w = ∑ χ ∈ Finset.univ.image ty, H χ w := by
    intro w
    rw [hsum w]
    exact (Finset.sum_fiberwise_of_maps_to (fun j _ => Finset.mem_image_of_mem ty (Finset.mem_univ j)) _).symm
  have hres : ∀ χ χ' : E →+* ℂ, (∀ a : 𝓞 E, χ (a : E) = χ' (a : E)) → χ = χ' := fun χ χ' h =>
    IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext h)
  have hli : LinearIndependent ℂ (fun χ : E →+* ℂ => fun a : 𝓞 E => χ (a : E)) :=
    (linearIndependent_monoidHom (𝓞 E) ℂ).comp (fun χ : E →+* ℂ => (χ.comp (algebraMap (𝓞 E) E)).toMonoidHom)
      (fun χ χ' e => hres χ χ' fun a => by simpa using DFunLike.congr_fun e a)
  have hzero : ∀ χ ∈ Finset.univ.image ty, χ ≠ τ → H χ v = 0 := by
    intro χ hχ hne
    obtain ⟨a, ha⟩ : ∃ a : 𝓞 E, χ (a : E) ≠ τ (a : E) := by
      by_contra hc; push_neg at hc; exact hne (hres _ _ hc)
    have key : ∑ χ' ∈ Finset.univ.image ty, ((χ' (a : E) - τ (a : E)) * H χ' v) • (fun b : 𝓞 E => χ' (b : E)) = 0 := by
      funext b
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      have e1 := hF a (b • v)
      rw [hFH, hFH, smul_smul] at e1
      simp only [hHs] at e1
      rw [Finset.mul_sum] at e1
      calc _ = ∑ χ' ∈ Finset.univ.image ty, (χ' ((a * b : 𝓞 E) : E) * H χ' v - τ (a : E) * (χ' (b : E) * H χ' v)) :=
            Finset.sum_congr rfl fun χ' _ => by push_cast; rw [map_mul]; ring
        _ = 0 := by rw [Finset.sum_sub_distrib, e1, sub_self]
    have := linearIndependent_iff'.1 hli _ _ key χ hχ
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 ha)
  rw [hFH v, Finset.sum_eq_single τ]
  · simp only [hH]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  · intro χ hχ hne; exact hzero χ hχ hne
  · intro hτ
    simp only [hH]
    refine Finset.sum_eq_zero fun j hj => ?_
    exact absurd ((Finset.mem_filter.1 hj).2 ▸ Finset.mem_image_of_mem ty (Finset.mem_univ j)) hτ

theorem exists_fam {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    {La : Type} [AddCommGroup La] [Module (𝓞 E) La] (φ : La ≃ₗ[𝓞 E] X.Λ) :
    ∃ (n : ℕ) (a : Fin n → La), ∀ ρ : E →+* ℂ, ∃ L : (Fin n → ℂ) →ₗ[ℂ] (Fin r → ℂ),
      ∀ u : Fin r → ℂ, L (fun k => hermC ρ X.Gm u (Data.emb ρ (φ (a k) : Fin r → E))) = u := by
  obtain ⟨n, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.1 X.Λ_fg
  have hsm : ∀ k, s k ∈ X.Λ := fun k => hs ▸ Submodule.subset_span (Set.mem_range_self k)
  refine ⟨n, fun k => φ.symm ⟨s k, hsm k⟩, fun ρ => ?_⟩
  simp only [LinearEquiv.apply_symm_apply]
  let Φ : (Fin r → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
    { toFun := fun u k => hermC ρ X.Gm u (Data.emb ρ (s k))
      map_add' := fun u u' => funext fun k => hermC_add_left ρ X.Gm u u' _
      map_smul' := fun c u => funext fun k => hermC_smul_left ρ X.Gm c u _ }
  have hΦ : LinearMap.ker Φ = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro u hu
    have h0 : ∀ k, hermC ρ X.Gm u (Data.emb ρ (s k)) = 0 := fun k => congrFun hu k
    have hE : ∀ w : Fin r → E, hermC ρ X.Gm u (Data.emb ρ w) = 0 := by
      intro w
      have hw : w ∈ Submodule.span E (Set.range s) := by
        have h1 : X.Λ ≤ (Submodule.span E (Set.range s)).restrictScalars (𝓞 E) := by
          rw [← hs]; exact Submodule.span_le_restrictScalars (𝓞 E) E (Set.range s)
        have h2 : Submodule.span E (X.Λ : Set (Fin r → E)) ≤ Submodule.span E (Set.range s) :=
          Submodule.span_le.2 h1
        rw [X.Λ_span] at h2
        exact h2 trivial
      induction hw using Submodule.span_induction with
      | mem x hx => obtain ⟨k, rfl⟩ := hx; exact h0 k
      | zero => simp [Data.emb, hermC]
      | add x y _ _ hx hy =>
        rw [show Data.emb ρ (x + y) = Data.emb ρ x + Data.emb ρ y from funext fun _ => by simp [Data.emb],
          hermC_add_right, hx, hy, add_zero]
      | smul c x _ hx =>
        rw [show Data.emb ρ (c • x) = ρ c • Data.emb ρ x from funext fun _ => by simp [Data.emb],
          hermC_smul_right, hx, mul_zero]
    have hdet : (X.Gm.map ρ).det ≠ 0 := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; simpa using X.Gm_det
    apply Matrix.eq_zero_of_vecMul_eq_zero hdet
    funext b
    have := hE (Pi.single b 1)
    simp only [hermC, Data.emb] at this
    simp only [Matrix.vecMul, dotProduct, Matrix.map_apply, Pi.zero_apply]
    rw [← this]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single b]
    · simp
    · intro b' _ hb'; simp [Pi.single_apply, hb']
    · simp
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective Φ hΦ
  exact ⟨L, fun u => LinearMap.congr_fun hL u⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem perFr_smul_int (X : Data E r) (x : Frame X.Ψ r) (a : E) (v : Fin r → E) (τ : E →+* ℂ) (i : ℕ) :
    Formalism.L2.PjFree.perFr X x (a • v) τ i = τ a * Formalism.L2.PjFree.perFr X x v τ i := by
  have hemb : ∀ ρ : E →+* ℂ, Data.emb ρ (a • v) = ρ a • Data.emb ρ v := fun ρ => by
    funext k; simp [Data.emb]
  unfold Formalism.L2.PjFree.perFr
  split_ifs
  · rw [hemb, Matrix.mulVec_smul]; rfl
  · simp
  · rw [hemb, hermC_smul_right]; simp [conjEmb]
  · simp
  · simp

theorem coe_smul_lat (X : Data E r) (a : 𝓞 E) (w : X.Λ) :
    ((a • w : X.Λ) : Fin r → E) = (a : E) • (w : Fin r → E) := by
  funext k; simp [Algebra.smul_def]

theorem hermC_mulVec_left (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (M : Matrix (Fin r) (Fin r) ℂ)
    (w e : Fin r → ℂ) : hermC τ G (M *ᵥ w) e = ∑ k, w k * hermC τ G (col M k) e := by
  simp only [hermC, Matrix.mulVec, dotProduct, col, Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => by ring

theorem sum_fin_ite (n : ℕ) (f : Fin r → ℂ) :
    ∑ k : Fin r, (if (k : ℕ) = n then f k else 0) = if h : n < r then f ⟨n, h⟩ else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨n, h⟩]
    · simp
    · intro b _ hb; rw [if_neg]; intro e; exact hb (Fin.ext e)
    · simp
  · refine Finset.sum_eq_zero fun k _ => ?_
    rw [if_neg]; intro e; exact h (e ▸ k.2)

theorem perFr_conj_type (X : Data E r) (x : Frame X.Ψ r) (ρ : X.Ψ) (w : Fin r → E) (i : ℕ) :
    Formalism.L2.PjFree.perFr X x w (conjEmb ρ.1) i =
      ∑ k : Fin r, (if (k : ℕ) = X.p0 - 1 - i then hermC ρ.1 X.Gm (col (mat x ρ) k) (Data.emb ρ.1 w) else 0) := by
  rw [sum_fin_ite]
  unfold Formalism.L2.PjFree.perFr
  rw [dite_eq_right (ReciprocityTheory.ChartRestriction.G.PullbackSections.UH.conjEmb_not_mem X ρ)]
  have h' : conjEmb (conjEmb ρ.1) ∈ X.Ψ := by rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.UH.conjEmb_conjEmb]; exact ρ.2
  rw [dite_eq_left h']
  suffices ∀ τ' (h' : τ' ∈ X.Ψ), τ' = ρ.1 →
      (if hj : X.p0 - 1 - i < r then hermC τ' X.Gm (col (mat x ⟨τ', h'⟩) ⟨X.p0 - 1 - i, hj⟩) (Data.emb τ' w) else 0) =
      (if hj : X.p0 - 1 - i < r then hermC ρ.1 X.Gm (col (mat x ρ) ⟨X.p0 - 1 - i, hj⟩) (Data.emb ρ.1 w) else 0) from
    this _ h' (ReciprocityTheory.ChartRestriction.G.PullbackSections.UH.conjEmb_conjEmb _)
  rintro τ' h' rfl
  rfl

theorem rep_fwd (X : Data E r) {La : Type} [AddCommGroup La] [Module (𝓞 E) La] (φ : La ≃ₗ[𝓞 E] X.Λ) {g : ℕ}
    (ty : Fin g → (E →+* ℂ)) (idx : Fin g → ℕ) (hidx : ∀ j, ty j ∉ X.Ψ → idx j < X.p0) (x' : Frame X.Ψ r)
    (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (Q : La → Fin g → ℂ)
    (hQ : ∀ (a : 𝓞 E) v j, Q (a • v) j = ty j (a : E) * Q v j)
    (hh : ∀ v, Q v = h (fun j => Formalism.L2.PjFree.perFr X x' (φ v : Fin r → E) (ty j) (idx j)))
    (ρ : X.Ψ) (j : Fin g) (hj : ty j = conjEmb ρ.1) :
    ∃ w : Fin r → ℂ, (∀ k : Fin r, X.p0 ≤ (k : ℕ) → w k = 0) ∧
      ∀ v, Q v j = hermC ρ.1 X.Gm (mat x' ρ *ᵥ w) (Data.emb ρ.1 (φ v : Fin r → E)) := by
  set c : Fin g → ℂ := fun j' => h (fun k => if j' = k then 1 else 0) j with hc
  have hsum : ∀ v, Q v j = ∑ j', c j' * Formalism.L2.PjFree.perFr X x' (φ v : Fin r → E) (ty j') (idx j') := by
    intro v
    rw [hh v, show (h : (Fin g → ℂ) → (Fin g → ℂ)) _ = h.toLinearMap _ from rfl, LinearMap.pi_apply_eq_sum_univ]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hc, LinearEquiv.coe_coe]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have hG : ∀ j' (a : 𝓞 E) v, Formalism.L2.PjFree.perFr X x' (φ (a • v) : Fin r → E) (ty j') (idx j') =
      ty j' (a : E) * Formalism.L2.PjFree.perFr X x' (φ v : Fin r → E) (ty j') (idx j') := by
    intro j' a v
    rw [map_smul, coe_smul_lat, perFr_smul_int]
  have hsep := sep_types ty (fun j' v => Formalism.L2.PjFree.perFr X x' (φ v : Fin r → E) (ty j') (idx j'))
    (conjEmb ρ.1) c (fun v => Q v j) hG (fun a v => by rw [hQ, hj]) hsum
  refine ⟨fun k => ∑ j', if ty j' = conjEmb ρ.1 ∧ (k : ℕ) = X.p0 - 1 - idx j' then c j' else 0, ?_, ?_⟩
  · intro k hk
    refine Finset.sum_eq_zero fun j' _ => ?_
    rw [if_neg]
    rintro ⟨h1, h2⟩
    have := hidx j' (h1 ▸ ReciprocityTheory.ChartRestriction.G.PullbackSections.UH.conjEmb_not_mem X ρ)
    omega
  · intro v
    rw [hsep v, hermC_mulVec_left]
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j' _ => ?_
    by_cases hj' : ty j' = conjEmb ρ.1
    · rw [if_pos hj', hj', perFr_conj_type, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [true_and]
      split_ifs <;> simp
    · rw [if_neg hj', zero_mul]
      refine (Finset.sum_eq_zero fun k _ => ?_).symm
      rw [if_neg (fun hh => hj' hh.1), zero_mul]

theorem rep_bwd (X : Data E r) {La : Type} [AddCommGroup La] [Module (𝓞 E) La] (φ : La ≃ₗ[𝓞 E] X.Λ) {g : ℕ}
    (ty : Fin g → (E →+* ℂ)) (idx : Fin g → ℕ) (x' : Frame X.Ψ r)
    (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (Q : La → Fin g → ℂ)
    (hQ : ∀ (a : 𝓞 E) v j, Q (a • v) j = ty j (a : E) * Q v j)
    (hh : ∀ v, Q v = h (fun j => Formalism.L2.PjFree.perFr X x' (φ v : Fin r → E) (ty j) (idx j)))
    (ρ : X.Ψ) (j0 : Fin g) (hj0 : ty j0 = conjEmb ρ.1) :
    ∃ c : Fin g → ℂ, ∀ v, Formalism.L2.PjFree.perFr X x' (φ v : Fin r → E) (ty j0) (idx j0) =
      ∑ j, (if ty j = conjEmb ρ.1 then c j else 0) * Q v j := by
  set c : Fin g → ℂ := fun j => h.symm (fun k => if j = k then 1 else 0) j0 with hc
  have hsum : ∀ v, Formalism.L2.PjFree.perFr X x' (φ v : Fin r → E) (ty j0) (idx j0) = ∑ j, c j * Q v j := by
    intro v
    have e : (fun j => Formalism.L2.PjFree.perFr X x' (φ v : Fin r → E) (ty j) (idx j)) = h.symm (Q v) := by
      rw [hh v, LinearEquiv.symm_apply_apply]
    rw [show Formalism.L2.PjFree.perFr X x' (φ v : Fin r → E) (ty j0) (idx j0) = h.symm (Q v) j0 from congrFun e j0,
      show (h.symm : (Fin g → ℂ) → (Fin g → ℂ)) _ = h.symm.toLinearMap _ from rfl, LinearMap.pi_apply_eq_sum_univ]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hc, LinearEquiv.coe_coe]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  refine ⟨c, sep_types ty (fun j v => Q v j) (conjEmb ρ.1) c
    (fun v => Formalism.L2.PjFree.perFr X x' (φ v : Fin r → E) (ty j0) (idx j0)) (fun j a v => hQ a v j) ?_ hsum⟩
  intro a v
  show Formalism.L2.PjFree.perFr X x' (φ (a • v) : Fin r → E) (ty j0) (idx j0) = _
  rw [map_smul, coe_smul_lat, perFr_smul_int, hj0]

theorem lift_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (La : Type) [AddCommGroup La] [Module (𝓞 E) La] (φ : La ≃ₗ[𝓞 E] X.Λ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (idx : Fin g → ℕ) (d : ℕ) (B : Set (ReciprocityTheory.L2DbarEstimates.V d)) (P : ReciprocityTheory.L2DbarEstimates.V d → (La →+ (Fin g → ℂ))) (b₀ : ReciprocityTheory.L2DbarEstimates.V d), IsOpen B → b₀ ∈ B → (∀ b ∈ B, ∀ (a : 𝓞 E) (v : La) (j : Fin g), P b (a • v) j = ty j (a : E) * P b v j) → (∀ v, DifferentiableOn ℂ (fun b => P b v) B) → (∀ ρ ∈ X.Ψ, ∀ m < X.p0, ∃ j, ty j = conjEmb ρ ∧ idx j = m) → (∀ j j', ty j = ty j' → idx j = idx j' → j = j') → (∀ j, ty j ∉ X.Ψ → idx j < X.p0) → (∀ b ∈ B, ∃ x' ∈ X.dom, ∃ h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ v, P b v = h (fun j => Formalism.L2.PjFree.perFr X x' (φ v : Fin r → E) (ty j) (idx j))) → ∃ s : ReciprocityTheory.L2DbarEstimates.V d → ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r, AnalyticAt ℂ s b₀ ∧ ∀ᶠ b in 𝓝 b₀, s b ∈ X.dom ∧ ∀ x' ∈ X.dom, (∃ h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ v, P b v = h (fun j => Formalism.L2.PjFree.perFr X x' (φ v : Fin r → E) (ty j) (idx j))) → (∀ (τ : X.Ψ) (a b' : Fin r), X.p0 ≤ (a : ℕ) → (b' : ℕ) < X.p0 → ((ReciprocityTheory.ChartRestriction.G.FD.mat (s b) τ)⁻¹ * ReciprocityTheory.ChartRestriction.G.FD.mat x' τ) a b' = 0) ∧ (∀ (τ : X.Ψ) (a b' : Fin r), X.p0 ≤ (a : ℕ) → (b' : ℕ) < X.p0 → ((ReciprocityTheory.ChartRestriction.G.FD.mat x' τ)⁻¹ * ReciprocityTheory.ChartRestriction.G.FD.mat (s b) τ) a b' = 0) := by
  intro E _ _ _ r X La _ _ φ g ty idx d B P b₀ hBo hb₀ hsl hdiff hcov hinj hidx hper
  obtain ⟨n, a, hL⟩ := exists_fam X φ
  choose L hL using hL
  set yv : ReciprocityTheory.L2DbarEstimates.V d → X.Ψ → Fin g → Fin r → ℂ := fun b ρ j => L ρ.1 (fun k => P b (a k) j) with hyv
  have hrep : ∀ b ∈ B, ∀ x' : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r, ∀ h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ),
      (∀ v, P b v = h (fun j => Formalism.L2.PjFree.perFr X x' (φ v : Fin r → E) (ty j) (idx j))) →
      ∀ (ρ : X.Ψ) (j : Fin g), ty j = conjEmb ρ.1 → ∃ w : Fin r → ℂ,
        (∀ k : Fin r, X.p0 ≤ (k : ℕ) → w k = 0) ∧ yv b ρ j = ReciprocityTheory.ChartRestriction.G.FD.mat x' ρ *ᵥ w ∧
        ∀ v, P b v j = ReciprocityTheory.ChartRestriction.G.FD.hermC ρ.1 X.Gm (yv b ρ j)
          (ReciprocityTheory.ChartRestriction.G.FD.Data.emb ρ.1 (φ v : Fin r → E)) := by
    intro b hb x' h hh ρ j hj
    obtain ⟨w, hw, hv⟩ := rep_fwd X φ ty idx hidx x' h (fun v => P b v) (fun a v j => hsl b hb a v j) hh ρ j hj
    have hy : yv b ρ j = ReciprocityTheory.ChartRestriction.G.FD.mat x' ρ *ᵥ w := by
      rw [hyv]
      dsimp only
      rw [show (fun k => P b (a k) j) = fun k => ReciprocityTheory.ChartRestriction.G.FD.hermC ρ.1 X.Gm
          (ReciprocityTheory.ChartRestriction.G.FD.mat x' ρ *ᵥ w) (ReciprocityTheory.ChartRestriction.G.FD.Data.emb ρ.1 (φ (a k) : Fin r → E)) from
        funext fun k => hv (a k)]
      exact hL ρ.1 _
    exact ⟨w, hw, hy, fun v => by rw [hy]; exact hv v⟩
  obtain ⟨x₀, hx₀, h₀, hh₀⟩ := hper b₀ hb₀
  have hcol : ∀ (ρ : X.Ψ) (m : Fin r), (m : ℕ) < X.p0 → ∃ c : Fin g → ℂ, (∀ j, ty j ≠ conjEmb ρ.1 → c j = 0) ∧
      ReciprocityTheory.ChartRestriction.G.FD.col (ReciprocityTheory.ChartRestriction.G.FD.mat x₀ ρ) m = ∑ j, c j • yv b₀ ρ j := by
    intro ρ m hm
    obtain ⟨j0, hj0, hi0⟩ := hcov ρ.1 ρ.2 (X.p0 - 1 - m) (by omega)
    obtain ⟨c, hc⟩ := rep_bwd X φ ty idx x₀ h₀ (fun v => P b₀ v) (fun a v j => hsl b₀ hb₀ a v j) hh₀ ρ j0 hj0
    refine ⟨fun j => if ty j = conjEmb ρ.1 then c j else 0, fun j hj => if_neg hj, ?_⟩
    have key : ∀ v, ReciprocityTheory.ChartRestriction.G.FD.hermC ρ.1 X.Gm (ReciprocityTheory.ChartRestriction.G.FD.col (ReciprocityTheory.ChartRestriction.G.FD.mat x₀ ρ) m)
        (ReciprocityTheory.ChartRestriction.G.FD.Data.emb ρ.1 (φ v : Fin r → E)) =
        ReciprocityTheory.ChartRestriction.G.FD.hermC ρ.1 X.Gm (∑ j, (if ty j = conjEmb ρ.1 then c j else 0) • yv b₀ ρ j)
          (ReciprocityTheory.ChartRestriction.G.FD.Data.emb ρ.1 (φ v : Fin r → E)) := by
      intro v
      have e1 := hc v
      rw [hj0, hi0, perFr_conj_type] at e1
      have e2 : (∑ k : Fin r, if (k : ℕ) = X.p0 - 1 - (X.p0 - 1 - (m : ℕ)) then
          ReciprocityTheory.ChartRestriction.G.FD.hermC ρ.1 X.Gm (ReciprocityTheory.ChartRestriction.G.FD.col (ReciprocityTheory.ChartRestriction.G.FD.mat x₀ ρ) k)
            (ReciprocityTheory.ChartRestriction.G.FD.Data.emb ρ.1 (φ v : Fin r → E)) else 0) =
          ReciprocityTheory.ChartRestriction.G.FD.hermC ρ.1 X.Gm (ReciprocityTheory.ChartRestriction.G.FD.col (ReciprocityTheory.ChartRestriction.G.FD.mat x₀ ρ) m)
            (ReciprocityTheory.ChartRestriction.G.FD.Data.emb ρ.1 (φ v : Fin r → E)) := by
        rw [Finset.sum_eq_single m]
        · rw [if_pos (by omega)]
        · intro k _ hk; rw [if_neg]; intro e; exact hk (Fin.ext (by omega))
        · simp
      rw [← e2, e1, ReciprocityTheory.ChartRestriction.G.FD.hermC_sum_left]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hj : ty j = conjEmb ρ.1
      · rw [if_pos hj, ReciprocityTheory.ChartRestriction.G.FD.hermC_smul_left]
        obtain ⟨w, -, -, hPv⟩ := hrep b₀ hb₀ x₀ h₀ hh₀ ρ j hj
        rw [hPv v]
      · rw [if_neg hj, zero_mul, zero_smul, ReciprocityTheory.ChartRestriction.G.FD.hermC_zero_left]
    have := congrArg (L ρ.1) (funext fun k => key (a k))
    simpa only [hL] using this
  choose! cc hcc0 hcc using hcol
  let s : ReciprocityTheory.L2DbarEstimates.V d → ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r := fun b ρ k m =>
    if (m : ℕ) < X.p0 then ∑ j, cc ρ m j * yv b ρ j k else x₀ ρ k m
  have hs0 : s b₀ = x₀ := by
    funext ρ k m
    simp only [s]
    split_ifs with hm
    · have := congrFun (hcc ρ m hm) k
      simp only [ReciprocityTheory.ChartRestriction.G.FD.col, ReciprocityTheory.ChartRestriction.G.FD.mat, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul] at this
      exact this.symm
    · rfl
  have hsd : DifferentiableOn ℂ s B := by
    have hv : ∀ (ρ : X.Ψ) j, DifferentiableOn ℂ (fun b => yv b ρ j) B := by
      intro ρ j
      have h1 : DifferentiableOn ℂ (fun b => fun k => P b (a k) j) B :=
        differentiableOn_pi.2 fun k => differentiableOn_pi.1 (hdiff (a k)) j
      exact (LinearMap.toContinuousLinearMap (L ρ.1)).differentiable.comp_differentiableOn h1
    refine differentiableOn_pi.2 fun ρ => differentiableOn_pi.2 fun k => differentiableOn_pi.2 fun m => ?_
    by_cases hm : (m : ℕ) < X.p0
    · simp only [s, if_pos hm]
      exact DifferentiableOn.fun_sum fun j _ => (differentiableOn_const _).mul (differentiableOn_pi.1 (hv ρ j) k)
    · simp only [s, if_neg hm]
      exact differentiableOn_const _
  refine ⟨s, GlobalTheory.SCV.analyticAt_of_differentiableOn hsd (hBo.mem_nhds hb₀), ?_⟩
  have hev : ∀ᶠ b in 𝓝 b₀, s b ∈ X.dom :=
    (hsd.continuousOn.continuousAt (hBo.mem_nhds hb₀)).preimage_mem_nhds
      ((ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain.isOpen_dom X).mem_nhds (hs0 ▸ hx₀))
  filter_upwards [hev, hBo.mem_nhds hb₀] with b hsb hb
  refine ⟨hsb, fun x' hx' hex => ?_⟩
  obtain ⟨h, hh⟩ := hex
  have R2 : ∀ (τ : X.Ψ) (a' b' : Fin r), X.p0 ≤ (a' : ℕ) → (b' : ℕ) < X.p0 →
      ((ReciprocityTheory.ChartRestriction.G.FD.mat x' τ)⁻¹ * ReciprocityTheory.ChartRestriction.G.FD.mat (s b) τ) a' b' = 0 := by
    intro τ a' b' ha hb'
    have hr : ∀ j, ty j = conjEmb τ.1 → ∃ w : Fin r → ℂ, (∀ k : Fin r, X.p0 ≤ (k : ℕ) → w k = 0) ∧
        yv b τ j = ReciprocityTheory.ChartRestriction.G.FD.mat x' τ *ᵥ w := fun j hj => by
      obtain ⟨w, hw, hy, -⟩ := hrep b hb x' h hh τ j hj
      exact ⟨w, hw, hy⟩
    choose! w hw hyw using hr
    set W : Fin r → ℂ := ∑ j, cc τ b' j • w j with hW
    have hcolW : ReciprocityTheory.ChartRestriction.G.FD.col (ReciprocityTheory.ChartRestriction.G.FD.mat (s b) τ) b' = ReciprocityTheory.ChartRestriction.G.FD.mat x' τ *ᵥ W := by
      rw [hW, Matrix.mulVec_sum]
      funext k
      simp only [ReciprocityTheory.ChartRestriction.G.FD.col, ReciprocityTheory.ChartRestriction.G.FD.mat, Matrix.of_apply, s, if_pos hb', Finset.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hj : ty j = conjEmb τ.1
      · have e := hyw j hj
        simp only [ReciprocityTheory.ChartRestriction.G.FD.mat] at e
        simp only [Matrix.mulVec_smul, ← e, Pi.smul_apply, smul_eq_mul]
      · rw [hcc0 τ b' hb' j hj]; simp
    have hdet : IsUnit (ReciprocityTheory.ChartRestriction.G.FD.mat x' τ).det := ((hx' τ).1).isUnit
    have e : ((ReciprocityTheory.ChartRestriction.G.FD.mat x' τ)⁻¹ * ReciprocityTheory.ChartRestriction.G.FD.mat (s b) τ) a' b' =
        ((ReciprocityTheory.ChartRestriction.G.FD.mat x' τ)⁻¹ *ᵥ ReciprocityTheory.ChartRestriction.G.FD.col (ReciprocityTheory.ChartRestriction.G.FD.mat (s b) τ) b') a' := by
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, ReciprocityTheory.ChartRestriction.G.FD.col]
    rw [e, hcolW, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec, hW]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : ty j = conjEmb τ.1
    · rw [hw j hj a' ha, mul_zero]
    · rw [hcc0 τ b' hb' j hj, zero_mul]
  refine ⟨fun τ a' b' ha hb' => ?_, R2⟩
  set M := (ReciprocityTheory.ChartRestriction.G.FD.mat x' τ)⁻¹ * ReciprocityTheory.ChartRestriction.G.FD.mat (s b) τ with hM
  have hdx : IsUnit (ReciprocityTheory.ChartRestriction.G.FD.mat x' τ).det := ((hx' τ).1).isUnit
  have hds : IsUnit (ReciprocityTheory.ChartRestriction.G.FD.mat (s b) τ).det := ((hsb τ).1).isUnit
  have hdM : IsUnit M.det := by
    rw [hM, Matrix.det_mul]; exact (Matrix.isUnit_nonsing_inv_det _ hdx).mul hds
  letI := M.invertibleOfIsUnitDet hdM
  have hbt : M.BlockTriangular (fun i : Fin r => if (i : ℕ) < X.p0 then 0 else 1) := by
    intro i j hij
    dsimp only at hij
    by_cases hi : (i : ℕ) < X.p0
    · rw [if_pos hi] at hij; exact absurd hij (Nat.not_lt_zero _)
    · by_cases hj : (j : ℕ) < X.p0
      · exact R2 τ i j (by omega) hj
      · rw [if_neg hi, if_neg hj] at hij; exact absurd hij (lt_irrefl _)
  have hinv := Matrix.blockTriangular_inv_of_blockTriangular hbt
  have eM : M⁻¹ = (ReciprocityTheory.ChartRestriction.G.FD.mat (s b) τ)⁻¹ * ReciprocityTheory.ChartRestriction.G.FD.mat x' τ := by
    rw [hM, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hdx]
  rw [← eM]
  exact hinv (show (if (b' : ℕ) < X.p0 then 0 else 1) < (if (a' : ℕ) < X.p0 then 0 else 1) by
    rw [if_pos hb', if_neg (by omega)]; exact Nat.zero_lt_one)

end GlobalTheory.PeriodFamFrame
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAnalyticFrameFamilyOfHolomorphicPeriodMapsStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_analytic_frame_family_of_holomorphic_periodMaps : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (La : Type) [AddCommGroup La] [Module (𝓞 E) La] (φ : La ≃ₗ[𝓞 E] X.Λ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (idx : Fin g → ℕ) (d : ℕ) (B : Set (ReciprocityTheory.L2DbarEstimates.V d)) (P : ReciprocityTheory.L2DbarEstimates.V d → (La →+ (Fin g → ℂ))) (b₀ : ReciprocityTheory.L2DbarEstimates.V d), IsOpen B → b₀ ∈ B → (∀ b ∈ B, ∀ (a : 𝓞 E) (v : La) (j : Fin g), P b (a • v) j = ty j (a : E) * P b v j) → (∀ v, DifferentiableOn ℂ (fun b => P b v) B) → (∀ ρ ∈ X.Ψ, ∀ m < X.p0, ∃ j, ty j = conjEmb ρ ∧ idx j = m) → (∀ j j', ty j = ty j' → idx j = idx j' → j = j') → (∀ j, ty j ∉ X.Ψ → idx j < X.p0) → (∀ b ∈ B, ∃ x' ∈ X.dom, ∃ h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ v, P b v = h (fun j => Formalism.L2.PjFree.perFr X x' (φ v : Fin r → E) (ty j) (idx j))) → ∃ s : ReciprocityTheory.L2DbarEstimates.V d → ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r, AnalyticAt ℂ s b₀ ∧ ∀ᶠ b in 𝓝 b₀, s b ∈ X.dom ∧ ∀ x' ∈ X.dom, (∃ h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ v, P b v = h (fun j => Formalism.L2.PjFree.perFr X x' (φ v : Fin r → E) (ty j) (idx j))) → (∀ (τ : X.Ψ) (a b' : Fin r), X.p0 ≤ (a : ℕ) → (b' : ℕ) < X.p0 → ((ReciprocityTheory.ChartRestriction.G.FD.mat (s b) τ)⁻¹ * ReciprocityTheory.ChartRestriction.G.FD.mat x' τ) a b' = 0) ∧ (∀ (τ : X.Ψ) (a b' : Fin r), X.p0 ≤ (a : ℕ) → (b' : ℕ) < X.p0 → ((ReciprocityTheory.ChartRestriction.G.FD.mat x' τ)⁻¹ * ReciprocityTheory.ChartRestriction.G.FD.mat (s b) τ) a b' = 0) := by
  first | exact @GlobalTheory.PeriodFamFrame.lift_frame | exact GlobalTheory.PeriodFamFrame.lift_frame | (intros; apply GlobalTheory.PeriodFamFrame.lift_frame <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicChartLiftHolomorphicPeriodMaps
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicChartLiftHolomorphicPeriodMaps
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

set_option autoImplicit false

theorem GlobalTheory.ShFam.chart_lift_periods_of_openPart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (X : Var F) (j : X.X ⟶ gen T.Z) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsOpenImmersion j → ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ c' : AlgChart X.str (σ.comp e.toRingHom) X.dim, y ∈ c'.e.source → ∃ (i : Fin Fu.n) (B : Set (ReciprocityTheory.L2DbarEstimates.V X.dim)) (P : ReciprocityTheory.L2DbarEstimates.V X.dim → ((Fu.Di i).La →+ (Fin g → ℂ))), IsOpen B ∧ c'.e y ∈ B ∧ B ⊆ c'.e.target ∧ (∀ b ∈ B, IsPeriod (Fu.Di i) ty (P b)) ∧ (∀ x, DifferentiableOn ℂ (fun b => P b x) B) ∧ ∀ b ∈ B, ∃ q : FrPt Xo c (Formalism.L2.Pj.CAt σ), cxPt T.Z q = cxOf e σ hj (c'.e.symm b) ∧ Fu.u i (P b) = q.x := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ g ty Fu X j hj hjo y hy c' hyc
  have := T.Z.jQ_open
  have : IsLocalRing (CAt σ) := inferInstanceAs (IsLocalRing ℂ)
  let L := EuclideanSpace.equiv (Fin X.dim) ℂ
  have hsy := GlobalTheory.TrueCx.TorHolo.isHolTo_symm c'
  have hsj := ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp hsy j
  have hB₀ := (hsj T.Z.jQ.opensRange 0).1
  set B₀ := {b ∈ c'.e.target | ⊤ ≤ ((c'.e.symm b).1 ≫ j) ⁻¹ᵁ T.Z.jQ.opensRange} with hB₀def
  have hb₀ : c'.e y ∈ B₀ := by
    refine ⟨c'.e.map_source hyc, ?_⟩
    rw [c'.e.left_inv hyc]
    intro s _
    have h1 : y.1 s ∈ openPart j := hy (Set.mem_univ s)
    exact not_not.1 h1
  have hw : ∀ b ∈ B₀, ∃ w : Sp ℂ ⟶ Xo.XF c, w ≫ T.Z.jQ = (c'.e.symm b).1 ≫ j := fun b hb =>
    ⟨IsOpenImmersion.lift T.Z.jQ _ (by rintro _ ⟨s, rfl⟩; exact hb.2 (Set.mem_univ s)), IsOpenImmersion.lift_fac _ _ _⟩
  have : Nonempty (Sp ℂ ⟶ Xo.XF c) := ⟨(hw _ hb₀).choose⟩
  choose! w hw using hw
  have hwh : IsHolTo B₀ w := GlobalTheory.TrueCx.TorHolo.isHolTo_of_openImmersion T.Z.jQ
    (LocLift.isHolTo_congr (LocLift.isHolTo_mono hsj hB₀ fun b hb => hb.1) hw)
  have hyh := ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp hwh (Limits.pullback.fst _ _)
  have hsnd : ∀ b ∈ B₀, w b ≫ Limits.pullback.snd _ _ = spMap σ := fun b hb => by
    rw [← T.Z.jQ_over, ← Category.assoc, hw b hb]
    exact (Category.assoc _ _ _).trans (cxOf e σ hj (c'.e.symm b)).2
  have hB₁ : IsOpen (L.symm ⁻¹' B₀) := hB₀.preimage L.symm.continuous
  obtain ⟨B', i, P, hB', hb', hsub, hP, hu⟩ := Fu.lift X.dim (L.symm ⁻¹' B₀) (fun x => w (L.symm x) ≫ Limits.pullback.fst _ _) hB₁
    (fun x hx => by
      rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, hsnd _ hx, ← Spec.map_comp]
      rfl)
    (LocLift.isHolTo_comp hyh hB₁ L.symm.differentiableOn fun x hx => hx) (L (c'.e y))
    (by simpa only [Set.mem_preimage, ContinuousLinearEquiv.symm_apply_apply] using hb₀)
  refine ⟨i, L ⁻¹' B', fun v => P (L v), hB'.preimage L.continuous, hb', fun v hv => ?_, fun v hv => hP.1 _ hv,
    fun x => (hP.2 x).comp L.differentiableOn fun v hv => hv, fun b hb => ?_⟩
  · have := hsub hv
    simp only [Set.mem_preimage, ContinuousLinearEquiv.symm_apply_apply] at this
    exact this.1
  · have hb1 := hsub hb
    simp only [Set.mem_preimage, ContinuousLinearEquiv.symm_apply_apply] at hb1
    have h2 := hu _ hb
    simp only [ContinuousLinearEquiv.symm_apply_apply] at h2
    have ho : (w b ≫ Limits.pullback.fst _ _) ≫ Xo.s = sOf c (CAt σ) := by
      rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, hsnd b hb1]
      exact OpenReg.spMap_comp _ _
    obtain ⟨q, hq⟩ : ∃ q : FrPt Xo c (CAt σ), q.x = w b ≫ Limits.pullback.fst _ _ := GlobalTheory.FlagTan.exists_frPt _ ho
    refine ⟨q, Subtype.ext ?_, h2.trans hq.symm⟩
    have h3 : GlobalTheory.AllWt.ptF (S := CAt σ) q = w b :=
      Limits.pullback.hom_ext ((ptF_fst q).trans hq) ((ptF_snd q).trans (hsnd b hb1).symm)
    exact (congrArg (· ≫ T.Z.jQ) h3).trans (hw b hb1)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicChartLiftHolomorphicPeriodMapsStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraicChart_lift_holomorphic_periodMaps : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (X : Var F) (j : X.X ⟶ gen T.Z) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsOpenImmersion j → ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ c' : AlgChart X.str (σ.comp e.toRingHom) X.dim, y ∈ c'.e.source → ∃ (i : Fin Fu.n) (B : Set (ReciprocityTheory.L2DbarEstimates.V X.dim)) (P : ReciprocityTheory.L2DbarEstimates.V X.dim → ((Fu.Di i).La →+ (Fin g → ℂ))), IsOpen B ∧ c'.e y ∈ B ∧ B ⊆ c'.e.target ∧ (∀ b ∈ B, IsPeriod (Fu.Di i) ty (P b)) ∧ (∀ x, DifferentiableOn ℂ (fun b => P b x) B) ∧ ∀ b ∈ B, ∃ q : FrPt Xo c (Formalism.L2.Pj.CAt σ), cxPt T.Z q = cxOf e σ hj (c'.e.symm b) ∧ Fu.u i (P b) = q.x := by
  first | exact @GlobalTheory.ShFam.chart_lift_periods_of_openPart | exact GlobalTheory.ShFam.chart_lift_periods_of_openPart | (intros; apply GlobalTheory.ShFam.chart_lift_periods_of_openPart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAnalyticFlagDomainFrameLiftAlgebraicChart
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieBase

theorem exists_analytic_frame_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsOpenImmersion j → ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ c' : AlgChart X.str (σ.comp e.toRingHom) X.dim, y ∈ c'.e.source → ∃ (k' : U.Comp) (s : ReciprocityTheory.L2DbarEstimates.V X.dim → ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X k').Ψ (Dw.p + Dw.q)), AnalyticAt ℂ s (c'.e y) ∧ ∀ᶠ w in 𝓝 (c'.e y), ∃ hs : s w ∈ (U.X k').dom, cxPt T.Z (U.un k' ⟨s w, hs⟩) = cxOf e σ hj (c'.e.symm w) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU X j hj hjo y hy c' hyc
  rcases Nat.eq_zero_or_pos (Dw.p + Dw.q) with hr | hr
  · obtain ⟨W⟩ := GlobalTheory.ArcQ.nonempty_unfWit_of_isUnf _ _ _ _ _ _ _ _ U hU
    obtain ⟨i, B, P, hB, hb₀, -, hper, -, hq⟩ := GlobalTheory.T.algebraicChart_lift_holomorphic_periodMaps E H Dw l Xo c O β Y T F e σ W.g _ W.F X j hj hjo y hy c' hyc
    obtain ⟨q₀, hq₀, hu₀⟩ := hq _ hb₀
    have hne : ¬ LiesIn (cxOf e σ hj y) (genBd T.Z) := by
      rw [← c'.e.left_inv hyc, ← hq₀]; exact not_liesIn_cxPt q₀
    obtain ⟨k, x, -, hkx⟩ := GlobalTheory.HodgeSmooth.exists_orth (Z := T.Z) hσ hU hne
    have hg : IsEmpty (Fin W.g) := by
      refine ⟨fun a => ?_⟩
      have := (W.e a).2.2
      simp only [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.mult] at this
      split_ifs at this <;> omega
    refine ⟨k, fun _ => x.1, analyticAt_const, Filter.mem_of_superset (hB.mem_nhds hb₀) fun w hw => ⟨x.2, ?_⟩⟩
    obtain ⟨q, hq1, hq2⟩ := hq w hw
    have hfib : W.F.u i (P (c'.e y)) = W.F.u i (P w) :=
      (W.F.fibre i _ _ (hper _ hb₀) (hper w hw)).2 ⟨LinearEquiv.refl _ _, LinearEquiv.refl _ _, fun _ _ => rfl,
        fun a _ => ⟨0, by simp⟩, fun a => ⟨0, by simp⟩, fun a => funext fun t => (hg.false t).elim⟩
    have e1 : cxPt T.Z q₀ = cxPt T.Z q := cxPt_congr (hu₀.symm.trans (hfib.trans hq2))
    rw [← hq1, ← e1, hq₀, c'.e.left_inv hyc]
    exact hkx
  · obtain ⟨W, hinj⟩ := GlobalTheory.HodgeSmooth.exists_unfWit_inj hσ hU hr
    obtain ⟨i, B, P, hB, hb₀, -, hper, hdiff, hq⟩ := GlobalTheory.T.algebraicChart_lift_holomorphic_periodMaps E H Dw l Xo c O β Y T F e σ W.g _ W.F X j hj hjo y hy c' hyc
    obtain ⟨q₀, -, hu₀⟩ := hq _ hb₀
    obtain ⟨k, x₁, t, hbor⟩ := hU.2.2.1 q₀
    have hk : W.ik k = i := W.F.disj _ _ _ _ (W.period k x₁) (hper _ hb₀)
      (((W.lie k x₁).1.symm.trans hbor.1.symm).trans hu₀.symm)
    subst hk
    obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
    obtain ⟨hp0, hty⟩ := hU.2.1 k
    have hmult : ∀ τ : E →+* ℂ, Formalism.L2.PjFree.relab c σ τ ∉ (U.X k).Ψ → Dw.mult τ = (U.X k).p0 := by
      intro τ hτ
      rw [hp0]
      exact if_neg fun h => hτ ((hty _).2 ((hrt τ).2 h))
    have hrep : ∀ b ∈ B, ∀ q : FrPt Xo c (Formalism.L2.Pj.CAt σ), W.F.u (W.ik k) (P b) = q.x →
        ∃ x' : (U.X k).dom, (U.un k x').x = q.x ∧ ∃ h : (Fin W.g → ℂ) ≃ₗ[ℂ] (Fin W.g → ℂ), ∀ v, P b v =
          h (fun j => Formalism.L2.PjFree.perFr (U.X k) x'.1 (W.φ k v : Fin (Dw.p + Dw.q) → E)
            (Formalism.L2.PjFree.relab c σ (W.e j).1) ((W.e j).2 : ℕ)) := by
      intro b hb q hqu
      obtain ⟨x', hx', h, hh⟩ := GlobalTheory.T.periodMap_member_eq_frame_periodMap_linear_change E H Dw l Xo c σ _ U W hσ hU hinj k (P b) (hper b hb) q hqu
      exact ⟨x', hx', h, fun v => (hh v).trans (congrArg h (funext fun j => W.Pm_eq k x' v j))⟩
    obtain ⟨s, hs, hev⟩ := GlobalTheory.T.exists_analytic_frame_family_of_holomorphic_periodMaps E (Dw.p + Dw.q) (U.X k) _ (W.φ k) W.g (fun j => Formalism.L2.PjFree.relab c σ (W.e j).1)
      (fun j => ((W.e j).2 : ℕ)) X.dim B P (c'.e y) hB hb₀ (fun b hb => (hper b hb).1) hdiff
      (fun ρ hρ m hm => by
        obtain ⟨τ', hτ'⟩ := hbij.2 (conjEmb ρ)
        have hn : Formalism.L2.PjFree.relab c σ τ' ∉ (U.X k).Ψ := by
          rw [hτ']
          exact ((U.X k).cmType ρ).1 hρ
        have hm' : m < Dw.mult τ' := by rw [hmult τ' hn]; exact hm
        exact ⟨W.e.symm ⟨τ', ⟨m, hm'⟩⟩, by rw [Equiv.apply_symm_apply]; exact hτ', by rw [Equiv.apply_symm_apply]⟩)
      (fun j j' h1 h2 => by
        have h1' := hbij.1 h1
        exact W.e.injective (Sigma.ext h1' ((Fin.heq_ext_iff (by rw [h1'])).2 h2)))
      (fun j hj' => by
        exact lt_of_lt_of_eq (W.e j).2.2 (hmult _ hj'))
      (fun b hb => by
        obtain ⟨q, -, hqu⟩ := hq b hb
        obtain ⟨x', -, h, hh⟩ := hrep b hb q hqu
        exact ⟨x'.1, x'.2, h, hh⟩)
    refine ⟨k, s, hs, (hev.and (hB.mem_nhds hb₀)).mono fun w hw => ⟨hw.1.1, ?_⟩⟩
    obtain ⟨q, hq1, hqu⟩ := hq w hw.2
    obtain ⟨x', hx', h, hh⟩ := hrep w hw.2 q hqu
    obtain ⟨h1, h2⟩ := hw.1.2 x'.1 x'.2 ⟨h, hh⟩
    rw [← hq1]
    exact cxPt_congr ((GlobalTheory.TrueCx.PointWell.pt_eq_of_block hU hσ k ⟨s w, hw.1.1⟩ x' h1 h2).trans hx')

end GlobalTheory.LieBase
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAnalyticFlagDomainFrameLiftAlgebraicChartStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_analytic_flagDomain_frame_lift_algebraicChart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsOpenImmersion j → ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ c' : AlgChart X.str (σ.comp e.toRingHom) X.dim, y ∈ c'.e.source → ∃ (k' : U.Comp) (s : ReciprocityTheory.L2DbarEstimates.V X.dim → ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X k').Ψ (Dw.p + Dw.q)), AnalyticAt ℂ s (c'.e y) ∧ ∀ᶠ w in 𝓝 (c'.e y), ∃ hs : s w ∈ (U.X k').dom, cxPt T.Z (U.un k' ⟨s w, hs⟩) = cxOf e σ hj (c'.e.symm w) := by
  first | exact @GlobalTheory.LieBase.exists_analytic_frame_lift | exact GlobalTheory.LieBase.exists_analytic_frame_lift | (intros; apply GlobalTheory.LieBase.exists_analytic_frame_lift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeGramLocalModelAlgebraicChartHolomorphic
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

namespace GlobalTheory.PointChern

theorem lieGram_local_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ c' : AlgChart X.str (σ.comp e.toRingHom) X.dim, y ∈ c'.e.source → ∀ A ∈ Eb.S (under y), ∀ ix : Fin X.dim ≃ GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q, ∃ (φ : ReciprocityTheory.L2DbarEstimates.V X.dim → ReciprocityTheory.L2DbarEstimates.V X.dim) (g : ReciprocityTheory.L2DbarEstimates.V X.dim → Mat Dw.mult ℂ) (cc : (E →+* ℂ) → ℝ), (∀ τ, 0 < cc τ) ∧ AnalyticAt ℂ φ (c'.e y) ∧ (∀ τ i j, AnalyticAt ℂ (fun w => g w τ i j) (c'.e y)) ∧ (∀ τ, IsUnit (g (c'.e y) τ).det) ∧ InDom (coordOf ix (φ (c'.e y))) ∧ ∀ᶠ w in 𝓝 (c'.e y), ∀ τ, lieGram e U hj f₀ A₀ A (c'.e.symm w) τ = (cc τ : ℂ) • (g w τ * modelGram H Dw (coordOf ix (φ w)) τ * (g w τ)ᴴ) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL y hy c' hc' A hA ix
  obtain ⟨hoi, -, hT⟩ := hL
  obtain ⟨k', s, hs, hev⟩ := GlobalTheory.T.exists_analytic_flagDomain_frame_lift_algebraicChart E H Dw l Xo c O β Y T F e σ U hσ hU X j hj hoi y hy c' hc'
  obtain ⟨K, hK, hKu, hKev⟩ :=
    GlobalTheory.T.exists_holomorphic_invertible_frame_coordinates E H Dw l Xo c O β Y T F e σ U hσ hU X j f₀ Eb A₀ hj hoi hT y hy c' hc' A hA k' s hs hev
  obtain ⟨G, z, cc, hcc, hG⟩ := GlobalTheory.T.hodgeMetric_gram_holomorphic_frame_form E H Dw l Xo c O β T.Z σ U hσ hU k'
  obtain ⟨hs0, -⟩ := hev.self_of_nhds
  obtain ⟨hGa, hza, hGu, hzD, -⟩ := hG (s (c'.e y)) hs0
  let φ : ReciprocityTheory.L2DbarEstimates.V X.dim → ReciprocityTheory.L2DbarEstimates.V X.dim := fun w =>
    (EuclideanSpace.equiv (Fin X.dim) ℂ).symm (fun i => z (s w) (ix i).1 (ix i).2.1 (ix i).2.2)
  have hco : ∀ w, coordOf ix (φ w) = z (s w) := fun w => by
    funext τ a b
    simp [φ, coordOf]
  refine ⟨φ, fun w τ => (K w τ)ᵀ * G (s w) τ, cc, hcc, ?_, ?_, ?_, ?_, ?_⟩
  · refine (EuclideanSpace.equiv (Fin X.dim) ℂ).symm.analyticAt _ |>.comp ?_
    refine analyticAt_pi_iff.2 fun i => ?_
    exact (hza (ix i).1 (ix i).2.1 (ix i).2.2).comp hs
  · intro τ a b
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    exact Finset.analyticAt_fun_sum Finset.univ (fun i _ => (hK τ i a).mul ((hGa τ i b).comp hs))
  · intro τ
    rw [Matrix.det_mul, Matrix.det_transpose]
    exact (hKu τ).mul (hGu τ)
  · rw [hco]
    exact hzD
  · filter_upwards [hKev, hev] with w ⟨⟨g0, hg0⟩, hKw⟩ ⟨hsw, _⟩ τ
    have hex : ∃ g, FrameAt e f₀ A₀ A (c'.e.symm w) g := ⟨g0, hg0⟩
    rw [lieGram, dite_eq_left hex]
    show ((hodgeMet T.Z U).gram _ hex.choose τ)ᵀ = _
    rw [hKw hsw _ hex.choose_spec, Matrix.transpose_mul, Matrix.transpose_mul, (hG (s w) hsw).2.2.2.2 τ, hco]
    have hKt : ((K w τ)ᴴ)ᵀ = ((K w τ)ᵀ)ᴴ := by ext; simp
    rw [hKt]
    simp only [Matrix.conjTranspose_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]

end GlobalTheory.PointChern
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeGramLocalModelAlgebraicChartHolomorphicStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeGram_localModel_algebraicChart_holomorphic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ c' : AlgChart X.str (σ.comp e.toRingHom) X.dim, y ∈ c'.e.source → ∀ A ∈ Eb.S (under y), ∀ ix : Fin X.dim ≃ GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q, ∃ (φ : ReciprocityTheory.L2DbarEstimates.V X.dim → ReciprocityTheory.L2DbarEstimates.V X.dim) (g : ReciprocityTheory.L2DbarEstimates.V X.dim → Mat Dw.mult ℂ) (cc : (E →+* ℂ) → ℝ), (∀ τ, 0 < cc τ) ∧ AnalyticAt ℂ φ (c'.e y) ∧ (∀ τ i j, AnalyticAt ℂ (fun w => g w τ i j) (c'.e y)) ∧ (∀ τ, IsUnit (g (c'.e y) τ).det) ∧ InDom (coordOf ix (φ (c'.e y))) ∧ ∀ᶠ w in 𝓝 (c'.e y), ∀ τ, lieGram e U hj f₀ A₀ A (c'.e.symm w) τ = (cc τ : ℂ) • (g w τ * modelGram H Dw (coordOf ix (φ w)) τ * (g w τ)ᴴ) := by
  first | exact @GlobalTheory.PointChern.lieGram_local_model | exact GlobalTheory.PointChern.lieGram_local_model | (intros; apply GlobalTheory.PointChern.lieGram_local_model <;> assumption)
end
