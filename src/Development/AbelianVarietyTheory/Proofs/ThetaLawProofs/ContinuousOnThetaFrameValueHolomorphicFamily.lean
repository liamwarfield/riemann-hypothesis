module

public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaFrameValueIndependentNormalForm
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyInNormalFormAndArchimedeanConstant
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueThetaCharAtPoint
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniformisationOfPoint
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsHolomorphicLieFrame
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HolomorphicMapModuliLiftsLocallyToPeriods
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaFrameOfPreconnected
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsRelativeExpOfParts
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFinsetIsProjOverDescends

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsNormalOfWeil
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsCoordinatesOfRelations
open Filter Set
open scoped Topology

namespace GlobalTheory.ThetaValueCont

open GlobalTheory.ThetaFamily

private theorem exists_differentiableOn_ne_zero_mul_eq {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {O : Set E} (hO : IsOpen O) {θ f : E → ℂ}
    (hnz : ∀ z, ∃ᶠ w in 𝓝 z, θ w ≠ 0)
    (hloc : ∀ z ∈ O, ∃ ρ : E → ℂ, ρ z ≠ 0 ∧
      ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ ρ w ∧ ρ w * θ w = f w) :
    ∃ F : E → ℂ, DifferentiableOn ℂ F O ∧ (∀ z ∈ O, F z ≠ 0) ∧ ∀ z ∈ O, F z * θ z = f z := by
  choose! ρ hρ0 hρ using hloc
  refine ⟨fun z ↦ ρ z z, ?_, hρ0, fun z hz ↦ (hρ z hz).self_of_nhds.2⟩
  have heq : ∀ z ∈ O, (fun w ↦ ρ w w) =ᶠ[𝓝 z] ρ z := by
    intro z hz
    filter_upwards [(hρ z hz).eventually_nhds, hO.mem_nhds hz] with w hw hwO
    have h1 := hρ w hwO
    have hc1 : ContinuousAt (ρ w) w := h1.self_of_nhds.1.continuousAt
    have hc2 : ContinuousAt (ρ z) w := hw.self_of_nhds.1.continuousAt
    refine tendsto_nhds_unique_of_frequently_eq hc1 hc2 ?_
    refine ((hnz w).and_eventually (h1.and hw)).mono fun y hy ↦ ?_
    obtain ⟨hθ, ⟨_, h1y⟩, ⟨_, h2y⟩⟩ := hy
    exact mul_right_cancel₀ hθ (h1y.trans h2y.symm)
  intro z hz
  exact (((hρ z hz).self_of_nhds.1).congr_of_eventuallyEq (heq z hz)).differentiableWithinAt

private theorem eq_of_continuousAt_mul_eq_eventually {E : Type} [TopologicalSpace E] {θ f ρ₁ ρ₂ : E → ℂ} {z : E}
    (hnz : ∃ᶠ w in 𝓝 z, θ w ≠ 0) (h₁ : ContinuousAt ρ₁ z) (h₂ : ContinuousAt ρ₂ z)
    (e₁ : ∀ᶠ w in 𝓝 z, ρ₁ w * θ w = f w) (e₂ : ∀ᶠ w in 𝓝 z, ρ₂ w * θ w = f w) :
    ρ₁ z = ρ₂ z := by
  refine tendsto_nhds_unique_of_frequently_eq h₁ h₂ ?_
  refine (hnz.and_eventually (e₁.and e₂)).mono fun y hy ↦ ?_
  exact mul_right_cancel₀ hy.1 (hy.2.1.trans hy.2.2.symm)

theorem _root_.GlobalTheory.ThetaValueCont.continuousAt_constant {V V' K ι : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    [NormedAddCommGroup V'] [NormedSpace ℂ V'] [FiniteDimensional ℂ V'] {B : Set V} {b₀ : V}
    {W : ι → Set (V × V')} {f : ι → V × V' → ℂ} {θ : K → V × V' → ℂ} {C : Set K} (hC : C.Finite) {κ : V → K}
    {c : V → ℂ} {r : ι → V → ℂ} (hW : ∀ j, IsOpen (W j)) (hWB : ∀ j, ∀ w ∈ W j, w.1 ∈ B)
    (hf : ∀ j, DifferentiableOn ℂ (f j) (W j)) (hθ : ∀ k ∈ C, ∀ j, DifferentiableOn ℂ (θ k) (W j))
    (hnz : ∀ k ∈ C, ∀ b ∈ B, ∀ z, ∃ᶠ w in 𝓝 z, θ k (b, w) ≠ 0) (hκ : ∀ b ∈ B, κ b ∈ C)
    (hq : ∀ j b z, (b, z) ∈ W j → ∃ ρ : V' → ℂ, ρ z ≠ 0 ∧ (z = 0 → ρ 0 = c b * r j b) ∧
      ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ ρ w ∧ ρ w * θ (κ b) (b, w) = f j (b, w))
    (hB : B ∈ 𝓝 b₀) (cov : ∀ z, ∃ j, (b₀, z) ∈ W j)
    (uniq : ∀ k ∈ C, ∀ ρ : V' → ℂ, Differentiable ℂ ρ → (∀ z, ρ z ≠ 0) →
      (∀ z, ρ z * θ (κ b₀) (b₀, z) = θ k (b₀, z)) → k = κ b₀)
    (hr : ∀ j, (b₀, 0) ∈ W j → ContinuousAt (r j) b₀ ∧ r j b₀ ≠ 0) : ContinuousAt c b₀ := by
  classical
  have hb₀B : b₀ ∈ B := mem_of_mem_nhds hB
  have hκ₀ : κ b₀ ∈ C := hκ b₀ hb₀B
  have hslice : ∀ j b, IsOpen {z : V' | (b, z) ∈ W j} := fun j b ↦
    (hW j).preimage (continuous_const.prodMk continuous_id)
  have hF : ∀ j, ∀ b ∈ B, ∃ F : V' → ℂ, DifferentiableOn ℂ F {z | (b, z) ∈ W j} ∧
      (∀ z ∈ {z | (b, z) ∈ W j}, F z ≠ 0) ∧
      ∀ z ∈ {z | (b, z) ∈ W j}, F z * θ (κ b) (b, z) = f j (b, z) := fun j b hb ↦
    exists_differentiableOn_ne_zero_mul_eq (hslice j b) (hnz _ (hκ b hb) b hb)
      (fun z hz ↦ by
        obtain ⟨ρ, h0, -, hρ⟩ := hq j b z hz
        exact ⟨ρ, h0, hρ⟩)
  have hev : ∀ᶠ b in 𝓝 b₀, κ b = κ b₀ := by
    by_contra hne
    rw [not_eventually] at hne
    obtain ⟨k, hk, hfreq⟩ : ∃ k ∈ C, ∃ᶠ b in 𝓝 b₀, b ∈ B ∧ κ b = k ∧ k ≠ κ b₀ := by
      by_contra hall
      have h1 : ∀ k ∈ C, ∀ᶠ b in 𝓝 b₀, ¬ (b ∈ B ∧ κ b = k ∧ k ≠ κ b₀) := fun k hk ↦
        not_frequently.1 (fun h ↦ hall ⟨k, hk, h⟩)
      have h2 := (Filter.eventually_all_finite hC).2 h1
      refine (hne.and_eventually (h2.and hB)).exists.elim fun b hb ↦ ?_
      exact hb.2.1 (κ b) (hκ b hb.2.2) ⟨hb.2.2, rfl, hb.1⟩
    set S : Set V := {b | b ∈ B ∧ κ b = k} with hSdef
    have hS : ∀ j, ∀ b ∈ S, ∃ F : V' → ℂ, DifferentiableOn ℂ F {z | (b, z) ∈ W j} ∧
        (∀ z ∈ {z | (b, z) ∈ W j}, F z ≠ 0) ∧
        ∀ z ∈ {z | (b, z) ∈ W j}, F z * θ k (b, z) = f j (b, z) := by
      intro j b hb
      obtain ⟨F, h1, h2, h3⟩ := hF j b hb.1
      rw [hb.2] at h3
      exact ⟨F, h1, h2, h3⟩
    have hb₀S : b₀ ∈ closure S :=
      mem_closure_iff_frequently.2 (hfreq.mono fun b hb ↦ ⟨hb.1, hb.2.1⟩)
    have hloc : ∀ z, ∃ ρ : V' → ℂ, ρ z ≠ 0 ∧ ∀ᶠ w in 𝓝 z,
        DifferentiableAt ℂ ρ w ∧ ρ w * θ (κ b₀) (b₀, w) = θ k (b₀, w) := by
        intro z
        obtain ⟨j, hj⟩ := cov z
        obtain ⟨ρ, hρz, -, hρ⟩ := hq j b₀ z hj
        have hρne : ∀ᶠ w in 𝓝 z, ρ w ≠ 0 := hρ.self_of_nhds.1.continuousAt.eventually_ne hρz
        have hfnz : ∃ᶠ w in 𝓝 z, f j (b₀, w) ≠ 0 :=
          ((hnz _ hκ₀ b₀ hb₀B z).and_eventually (hρne.and hρ)).mono fun w hw ↦ by
            rw [← hw.2.2.2]
            exact mul_ne_zero hw.2.1 hw.1
        obtain ⟨U₁, G₁, hU₁, hzU₁, -, hG₁, hG₁e⟩ := _root_.GlobalTheory.ThetaFamily.exists_quotient_closure (hW j) (hf j)
          (hθ k hk j) (fun b hb ↦ (hS j b hb).elim fun F hF ↦ ⟨F, hF.1, hF.2.2⟩) hj
          (hnz k hk b₀ hb₀B z)
        obtain ⟨U₂, G₂, hU₂, hzU₂, -, hG₂, hG₂e⟩ := _root_.GlobalTheory.ThetaFamily.exists_quotient_closure (hW j)
          (hθ k hk j) (hf j) (S := S) (fun b hb ↦ (hS j b hb).elim fun F hF ↦
            ⟨F⁻¹, hF.1.inv hF.2.1, fun z hz ↦ by
              rw [← hF.2.2 z hz, Pi.inv_apply, inv_mul_cancel_left₀ (hF.2.1 z hz)]⟩) hj hfnz
        have hcont : Continuous fun w : V' ↦ (b₀, w) := continuous_const.prodMk continuous_id
        have hU₁z : ∀ᶠ w in 𝓝 z, (b₀, w) ∈ U₁ := hcont.continuousAt.preimage_mem_nhds
          (hU₁.mem_nhds hzU₁)
        have hU₂z : ∀ᶠ w in 𝓝 z, (b₀, w) ∈ U₂ := hcont.continuousAt.preimage_mem_nhds
          (hU₂.mem_nhds hzU₂)
        have hG₁c : ContinuousAt (fun w ↦ G₁ (b₀, w)) z :=
          ((hG₁.continuousOn.continuousAt (hU₁.mem_nhds hzU₁))).comp hcont.continuousAt
        have hG₂c : ContinuousAt (fun w ↦ G₂ (b₀, w)) z :=
          ((hG₂.continuousOn.continuousAt (hU₂.mem_nhds hzU₂))).comp hcont.continuousAt
        have hone : G₁ (b₀, z) * G₂ (b₀, z) = 1 := by
          refine tendsto_nhds_unique_of_frequently_eq (hG₁c.mul hG₂c) tendsto_const_nhds ?_
          refine (hfnz.and_eventually (hU₁z.and hU₂z)).mono fun w hw ↦ ?_
          have e₁ := hG₁e _ hw.2.1 hb₀S
          have e₂ := hG₂e _ hw.2.2 hb₀S
          refine mul_right_cancel₀ hw.1 ?_
          show G₁ (b₀, w) * G₂ (b₀, w) * f j (b₀, w) = 1 * f j (b₀, w)
          rw [one_mul, mul_assoc, e₂, e₁]
        refine ⟨fun w ↦ G₂ (b₀, w) * ρ w, mul_ne_zero (right_ne_zero_of_mul_eq_one hone) hρz, ?_⟩
        filter_upwards [hρ, hU₂z] with w hw hw₂
        refine ⟨((hG₂.differentiableAt (hU₂.mem_nhds hw₂)).comp w
          ((differentiableAt_const _).prodMk differentiableAt_id)).mul hw.1, ?_⟩
        rw [mul_assoc, hw.2, hG₂e _ hw₂ hb₀S]
    obtain ⟨ρ, hρd, hρ0, hρ⟩ := _root_.GlobalTheory.ThetaFamily.exists_entire_quotient
      (θ := fun z ↦ θ k (b₀, z)) (θ' := fun z ↦ θ (κ b₀) (b₀, z)) (hnz _ hκ₀ b₀ hb₀B) hloc
    exact (hfreq.exists.elim fun b hb ↦ hb.2.2) (uniq k hk ρ hρd hρ0 hρ)
  obtain ⟨j, hj⟩ := cov 0
  obtain ⟨hrc, hr0⟩ := hr j hj
  obtain ⟨N, hNsub, hNo, hb₀N⟩ := eventually_nhds_iff.1 (hev.and hB)
  choose! Fs hFsd hFs0 hFse using hF j
  set Wst : Set (V × V') := W j ∩ Prod.fst ⁻¹' N with hWst
  have hWo : IsOpen Wst := (hW j).inter (hNo.preimage continuous_fst)
  have hFd : DifferentiableOn ℂ (fun y : V × V' ↦ Fs y.1 y.2) Wst :=
    _root_.GlobalTheory.differentiableOn_quotient_of_differentiableOn_slice V V' Wst (f j) (θ (κ b₀)) _ hWo
      ((hf j).mono inter_subset_left) ((hθ _ hκ₀ j).mono inter_subset_left)
      (fun w hw ↦ by
        obtain ⟨hκw, hBw⟩ := hNsub w.1 hw.2
        have h := hFse w.1 hBw w.2 hw.1
        rw [hκw] at h
        exact h)
      (fun b z hz ↦
        ((hFsd b (hNsub b hz.2).2).mono (s := {z' | (b, z') ∈ Wst}) fun _ hz' ↦ hz'.1) z hz)
      (fun w hw ↦ hnz _ hκ₀ w.1 (hNsub w.1 hw.2).2 w.2)
  have hmem : (b₀, (0 : V')) ∈ Wst := ⟨hj, hb₀N⟩
  have hpair : Continuous fun b : V ↦ (b, (0 : V')) := continuous_id.prodMk continuous_const
  have hFc : ContinuousAt (fun b ↦ Fs b 0) b₀ :=
    ContinuousAt.comp (f := fun b : V ↦ (b, (0 : V'))) (g := fun y : V × V' ↦ Fs y.1 y.2)
      (hFd.continuousOn.continuousAt (hWo.mem_nhds hmem)) hpair.continuousAt
  refine (hFc.div hrc hr0).congr ?_
  have hWz : ∀ᶠ b in 𝓝 b₀, (b, (0 : V')) ∈ Wst :=
    hpair.continuousAt.preimage_mem_nhds (hWo.mem_nhds hmem)
  filter_upwards [hWz, hrc.eventually_ne hr0] with b hb hrb
  obtain ⟨-, hBb⟩ := hNsub b hb.2
  obtain ⟨ρ, -, h0, hρ⟩ := hq j b 0 hb.1
  have hFsc : ContinuousAt (Fs b) 0 :=
    (hFsd b hBb).continuousOn.continuousAt ((hslice j b).mem_nhds hb.1)
  have heq : Fs b 0 = ρ 0 := eq_of_continuousAt_mul_eq_eventually (hnz _ (hκ b hBb) b hBb 0) hFsc
    hρ.self_of_nhds.1.continuousAt
    (by
      filter_upwards [(hslice j b).mem_nhds hb.1] with w hw
      exact hFse b hBb w hw)
    (hρ.mono fun w hw ↦ hw.2)
  show Fs b 0 / r j b = c b
  rw [heq, h0 rfl, mul_div_cancel_right₀ _ hrb]

open scoped Matrix in

open Complex Matrix in
theorem _root_.GlobalTheory.ThetaValueCont.exists_coordinates_of_relations {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) (e f : Fin g → Fin g → ℂ)
    (hee : ∀ i j, (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (e i) (e j)).im = 0) (hff : ∀ i j, (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (f i) (f j)).im = 0)
    (hef : ∀ i j, (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (e i) (f j)).im = if i = j then -1 else 0) :
    ∃ (φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (τ : Matrix (Fin g) (Fin g) ℂ),
      τ.IsSymm ∧ (τ.map Complex.im).PosDef ∧ (∀ k, φ (Pi.single k 1) = e k ∧ φ (τ *ᵥ Pi.single k 1) = f k) ∧
      ∀ z w, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (φ z) (φ w) = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm ((τ.map Complex.im)⁻¹.map fun x : ℝ => (x : ℂ)) z w := by
  classical
  set P : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun a k ↦ e k a with hPdef
  set F : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun a k ↦ f k a with hFdef
  have hPe : ∀ k, P *ᵥ Pi.single k 1 = e k := fun k ↦ by
    rw [Matrix.mulVec_single_one]; rfl
  have hFf : ∀ k, F *ᵥ Pi.single k 1 = f k := fun k ↦ by
    rw [Matrix.mulVec_single_one]; rfl
  set YC : Matrix (Fin g) (Fin g) ℂ := P.transpose * Hm * P.map star with hYCdef
  have hYC : ∀ z w, z ⬝ᵥ YC.mulVec (star w) = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (P *ᵥ z) (P *ᵥ w) := fun z w ↦ by
    rw [hYCdef, ← _root_.GlobalTheory.SiegelNormalForm.form_pull]; rfl
  have hYCe : ∀ i j, YC i j = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (e i) (e j) := fun i j ↦ by
    rw [← _root_.GlobalTheory.SiegelNormalForm.form_single YC i j, hYC, hPe, hPe]
  set Y : Matrix (Fin g) (Fin g) ℝ := YC.map Complex.re with hYdef
  have hYre : Y.map Complex.ofReal = YC := by
    ext i j
    refine Complex.ext (by simp [hYdef]) ?_
    simp only [hYdef, Matrix.map_apply, Complex.ofReal_im]
    rw [hYCe, hee]
  have hPu : IsUnit P := _root_.GlobalTheory.SiegelNormalForm.isUnit_of_lagrangian P Hm f hpos Y hYre.symm
    (fun i j ↦ by rw [hPe]; exact hef i j)
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hPu
  have hPinj : ∀ z, P *ᵥ z = 0 → z = 0 := fun z hz ↦ by
    rw [← Matrix.one_mulVec z, ← Matrix.nonsing_inv_mul P hdet, ← Matrix.mulVec_mulVec, hz,
      Matrix.mulVec_zero]
  have hYpos : Y.PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
    · ext i j
      simp only [Matrix.conjTranspose_apply, star_trivial, hYdef, Matrix.map_apply, hYCe]
      rw [show _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (e j) (e i) = star (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (e i) (e j)) from
        (_root_.GlobalTheory.SiegelNormalForm.form_conj hH _ _).symm]
      simp
    · intro x hx
      set z : Fin g → ℂ := fun i ↦ (x i : ℂ) with hzdef
      have hz : z ≠ 0 := fun h ↦ hx (funext fun i ↦ by
        simpa [hzdef] using congrFun h i)
      have key : ((star x ⬝ᵥ Y *ᵥ x : ℝ) : ℂ) = z ⬝ᵥ YC.mulVec (star z) := by
        rw [← hYre]
        simp [hzdef, dotProduct, Matrix.mulVec, Complex.ofReal_sum, Complex.ofReal_mul]
      have h2 := hpos (P *ᵥ z) (fun h ↦ hz (hPinj z h))
      rw [← Complex.ofReal_re (star x ⬝ᵥ Y *ᵥ x), key, hYC]
      exact h2
  set τ : Matrix (Fin g) (Fin g) ℂ := P⁻¹ * F with hτdef
  have hPτ : ∀ k, P *ᵥ (τ *ᵥ Pi.single k 1) = f k := fun k ↦ by
    rw [Matrix.mulVec_mulVec, hτdef, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv P hdet,
      Matrix.one_mul, hFf]
  obtain ⟨hsymm, hpd, hYI⟩ := _root_.GlobalTheory.SiegelNormalForm.siegel_of_relations Y hYpos τ
    (fun i j ↦ by rw [hYre, hYC, hPe, hPτ]; exact hef i j)
    (fun i j ↦ by rw [hYre, hYC, hPτ, hPτ]; exact hff i j)
  let hPinv : Invertible P := P.invertibleOfIsUnitDet hdet
  refine ⟨Matrix.toLinearEquiv' P hPinv, τ, hsymm, hpd, fun k ↦ ⟨?_, ?_⟩, fun z w ↦ ?_⟩
  · change P *ᵥ Pi.single k 1 = e k
    exact hPe k
  · change P *ᵥ (τ *ᵥ Pi.single k 1) = f k
    exact hPτ k
  · change _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (P *ᵥ z) (P *ᵥ w) = _
    rw [Matrix.inv_eq_left_inv hYI, hYre, ← hYC]
    rfl

end GlobalTheory.ThetaValueCont
end

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Filter Topology Matrix
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaValueCont

open GlobalTheory.KeyPow

theorem exists_normal_of_weil (hT : ThetaUnifAV) (hmul : Out.MulNSt) (x : KeyIn ℂ)
    (e : (Fin x.P.g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ x.P.A)) (hadd : ∀ z w, e (z + w) = e z * e w)
    (hon : Function.Surjective e) (hol : IsHolTo Set.univ fun z => (e z).left) {La : Type} [AddCommGroup La]
    (EF : LinearMap.BilinForm ℤ La) (bs : Module.Basis (Fin x.P.g ⊕ Fin x.P.g) ℤ La)
    (hbs : IsSymplecticBasis (-EF) bs) (P : La →+ (Fin x.P.g → ℂ)) (hker : ∀ z, e z = 1 ↔ z ∈ P.range)
    (hweil : ∀ (k : ℕ) (a a₂ : La) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a a₂ : ℂ) / k) →
      Out.WeilIs x.P.A x.P.L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P a₂)) (unitOn c)) :
    ∃ (u : HolUnif x.P.A x.P.L x.P.g) (k : (Fin x.P.g → ℂ) ≃L[ℂ] (Fin x.P.g → ℂ))
      (τ : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℝ) (c : ℂ) (W : Fin x.P.g → Fin x.P.g → ℂ),
      (∀ z, u.ex z = e (k z)) ∧ τ.IsSymm ∧ (τ.map Complex.im).PosDef ∧
      (∀ i, k (Pi.single i 1) = P (bs (.inl i)) ∧ k (τ *ᵥ Pi.single i 1) = P (bs (.inr i))) ∧
      (∀ i, a i = 0 ∨ a i = 1 / 2) ∧ (∀ i, b i = 0 ∨ b i = 1 / 2) ∧ c ≠ 0 ∧
      (∀ z, z ∈ u.Λ ↔ ∃ m n : Fin x.P.g → ℤ, z = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) ∧
      u.IsRig x.rig ∧ u.IsFn x.th (fun z => c * thetaChar τ (fun i => (a i : ℂ)) (fun i => (b i : ℂ)) z) ∧
      ∀ i, u.IsDiff (W i) (x.v i) := by
  obtain ⟨u, Hm, χ, Ef, hAH, hrig, h₁, -, -, -, hE, -, hW⟩ := hT x.P x.rig x.rig_gen
  have : Countable La := bs.equivFun.injective.countable
  obtain ⟨F, hF⟩ := ThetaPoint.exists_linearEquiv_lift hmul x.P u e hadd hon hol
    ((Set.countable_range P).mono fun z hz => (hker z).1 hz)
  have hFΛ : ∀ z, F z ∈ u.Λ ↔ z ∈ P.range := fun z => by rw [← u.ker, hF, hker]
  have hEF : ∀ a a₂, (hermForm Hm (F (P a)) (F (P a₂))).im = EF a a₂ := fun a a₂ => by
    refine (hE ⟨_, (hFΛ _).2 ⟨a, rfl⟩⟩ ⟨_, (hFΛ _).2 ⟨a₂, rfl⟩⟩).symm.trans (congrArg _ ?_)
    refine ThetaPoint.int_eq_of_exp_div_eq fun k hk => ?_
    have k₁ := hW k ⟨_, (hFΛ _).2 ⟨a, rfl⟩⟩ ⟨_, (hFΛ _).2 ⟨a₂, rfl⟩⟩ (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
    have k₂ := hweil k a a₂ (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
    simp only [← map_smul, hF] at k₁
    exact congrArg Units.val (weilIs_unique_fieldPoint _ x.P.A x.P.L x.P.isLB ℂ (𝟙 _) k _ _ _ _ k₁ k₂)
  obtain ⟨φ, τ, hs, hp, hφ, hH⟩ := exists_coordinates_of_relations hAH.1 hAH.2.1 (fun i => F (P (bs (.inl i))))
    (fun i => F (P (bs (.inr i))))
    (fun i j => by
      have := hbs.left_left i j
      simp only [LinearMap.neg_apply, neg_eq_zero] at this
      rw [hEF, this]; simp)
    (fun i j => by
      have := hbs.right_right i j
      simp only [LinearMap.neg_apply, neg_eq_zero] at this
      rw [hEF, this]; simp)
    (fun i j => by
      have := hbs.left_right i j
      simp only [LinearMap.neg_apply, neg_eq_iff_eq_neg] at this
      rw [hEF, this]; split_ifs <;> simp)
  have hcomb : ∀ m n : Fin x.P.g → ℤ, φ ((fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) =
      F (P (∑ i, m i • bs (.inl i) + ∑ i, n i • bs (.inr i))) := fun m n => by
    have h1 : ∀ m : Fin x.P.g → ℤ, (fun i => (m i : ℂ)) = ∑ i, m i • (Pi.single i 1 : Fin x.P.g → ℂ) := by
      intro m; ext k; simp [Finset.sum_apply, Pi.single_apply]
    rw [h1 m, h1 n]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, map_add (f := _), map_sum, map_zsmul, (hφ _).1, (hφ _).2]
  have hΛ : ∀ z, φ z ∈ u.Λ ↔ ∃ m n : Fin x.P.g → ℤ, z = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ)) := by
    refine fun z => ⟨fun hz => ?_, ?_⟩
    · obtain ⟨l, hl⟩ := (hFΛ (F.symm (φ z))).1 (by rwa [F.apply_symm_apply])
      refine ⟨fun i => bs.repr l (.inl i), fun i => bs.repr l (.inr i), φ.injective ?_⟩
      have := bs.sum_repr l
      rw [Fintype.sum_sum_type] at this
      rw [hcomb, this, hl, F.apply_symm_apply]
    · rintro ⟨m, n, rfl⟩
      rw [hcomb, hFΛ]
      exact ⟨_, rfl⟩
  obtain ⟨θ, hfn⟩ := KeyPow.exists_isFn x.P.isLB u x.th
  obtain ⟨⟨hθd, hθl⟩, hθ0⟩ := isThetaFn_and_ne_zero_of_isFn x u Hm χ θ hAH hfn
  let ψ := φ.toContinuousLinearEquiv
  obtain ⟨a, b, c, ha, hb, hc, hθ⟩ := exists_eq_mul_canonical_theta_of_sign_multiplier x.P.g τ
    (fun m n => χ ⟨φ ((fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))), (hΛ _).2 ⟨m, n, rfl⟩⟩)
    (fun z => θ (φ z)) hs hp (fun m n => semicharacter_sq_eq_one_of_symmetric x.P u Hm χ hAH _)
    (hθd.comp ψ.differentiable)
    (fun h => hθ0 (funext fun z => by simpa using congrFun h (φ.symm z)))
    (fun m n l z hl => by
      subst hl
      have := hθl ⟨_, (hΛ _).2 ⟨m, n, rfl⟩⟩ (φ z)
      rw [pow_one, hH, hH, ← map_add (f := _)] at this
      exact this)
  have hQ : Differentiable ℂ fun z : Fin x.P.g → ℂ =>
      (Real.pi : ℂ) / 2 * (z ⬝ᵥ (CanTh.imInv τ).mulVec z) := by
    simp only [dotProduct, Matrix.mulVec]
    fun_prop
  choose W hW using fun i => (h₁ _ (x.basis.1 i)).exists
  refine ⟨KeyNormalForm.change u ψ _ hQ, (φ.trans F.symm).toContinuousLinearEquiv, τ, a, b, c, fun i => φ.symm (W i),
    fun z => ?_, hs, hp, fun i => ⟨?_, ?_⟩, ha, hb, hc, hΛ, KeyNormalForm.isRig_change u ψ _ hQ (by simp) hrig,
    KeyNormalForm.isFn_change u ψ _ hQ hfn fun z => (hθ z).trans (by rw [_root_.mul_assoc, mul_comm (Complex.exp _)]; rfl),
    fun i => KeyNormalForm.isDiff_change u ψ _ hQ (by have := hW i; rwa [← φ.apply_symm_apply (W i)] at this)⟩
  · change u.ex (φ z) = e (F.symm (φ z))
    rw [← hF, F.apply_symm_apply]
  · change F.symm (φ _) = _
    rw [(hφ i).1, F.symm_apply_apply]
  · change F.symm (φ _) = _
    rw [(hφ i).2, F.symm_apply_apply]

section Values

variable {X Y : Scheme.{0}} {L : LB X} {L' : LB Y} {φ : Y ⟶ X}

theorem valAt'_via (w : LB.Iso L' (L.pull φ)) (s : L.Sec) (s' : L'.Sec)
    (h : ∀ (j : (L.pull φ).ι) (i : L'.ι) (h : (L.pull φ).U j ⊓ L'.U i ≤ φ ⁻¹ᵁ L.U (j PUnit.unit)),
      (φ.appLE _ _ h).hom (s.f (j PUnit.unit)) =
        (show Γ(Y, (L.pull φ).U j ⊓ L'.U i) from (w.s (j, i)).val) * resG _ inf_le_right (s'.f i))
    (p : Sp ℂ ⟶ Y) (j : L.ι) (i : L'.ι) (hp : ⊤ ≤ p ⁻¹ᵁ ((L.pull φ).U (fun _ => j) ⊓ L'.U i)) :
    valAt' (p ≫ φ) (L.U j) (s.f j) =
      valAt' p ((L.pull φ).U (fun _ => j) ⊓ L'.U i) (w.s (fun _ => j, i)).val * valAt' p (L'.U i) (s'.f i) := by
  have e := congrArg (valAt' p _) (h (fun _ => j) i (inf_le_left.trans (LB.wchart_le L (fun _ => φ) _ PUnit.unit)))
  rw [valAt'_appLE _ _ _ _ _ _ hp, valAt'_mul, valAt'_res _ _ _ hp] at e
  exact e

end Values

theorem valAt'_rig {X : Scheme.{0}} {G : Over X} [GrpObj G] [IsCommMonObj G] {G' : Over (Sp ℂ)} [GrpObj G']
    [IsCommMonObj G'] {L : LB G.left} {L' : LB G'.left} {φ : G'.left ⟶ G.left} {y : Sp ℂ ⟶ X}
    (he : eSec G' ≫ φ = y ≫ eSec G) (w : LB.Iso L' (L.pull φ)) (r' : LB.Gen (L'.pull (eSec G')))
    (r : LB.Gen (L.pull (eSec G)))
    (h : LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec G') (fun _ => 1)) r' (rigPullOf φ y he L r))
    (j : L.ι) (i : L'.ι) (hp : ⊤ ≤ (show Sp ℂ ⟶ _ from eSec G') ⁻¹ᵁ ((L.pull φ).U (fun _ => j) ⊓ L'.U i)) :
    valAt' y ((L.pull (eSec G)).U fun _ => j) (r.s fun _ => j).val =
      valAt' (show Sp ℂ ⟶ _ from eSec G') ((L.pull φ).U (fun _ => j) ⊓ L'.U i) (w.s (fun _ => j, i)).val *
        valAt' (𝟙 (Sp ℂ)) ((L'.pull (eSec G')).U fun _ => i) (r'.s fun _ => i).val := by
  have hm : ⊤ ≤ (𝟙 (Sp ℂ) : Sp ℂ ⟶ _) ⁻¹ᵁ (((L.pull φ).pull (eSec G')).U (fun _ _ => j) ⊓
      (L'.pull (eSec G')).U fun _ => i) := fun p hq => ⟨mem_pull.2 (hp hq).1, mem_pull.2 (hp hq).2⟩
  have e := congrArg (fun q => valAt' (𝟙 (Sp ℂ)) _ q.val) (h (fun _ _ => j, fun _ => i))
  have l : valAt' (𝟙 (Sp ℂ)) _ (res (inf_le_left : ((L.pull φ).pull (eSec G')).U (fun _ _ => j) ⊓
      (L'.pull (eSec G')).U (fun _ => i) ≤ _) ((rigPullOf φ y he L r).s fun _ _ => j)).val =
      valAt' y ((L.pull (eSec G)).U fun _ => j) (r.s fun _ => j).val := by
    refine (CubeValues.val_res _ valAt'_rules _ hm _).trans ((CubeValues.val_res _ valAt'_rules _
      (top_le_preimage_mono _ inf_le_left hm) _).trans ((CubeValues.val_pullU _ valAt'_rules _ _ _).trans ?_))
    rw [Category.id_comp]
    rfl
  refine l.symm.trans (e.trans ((valAt'_mul _ _ _ _).trans (congrArg₂ (· * ·) ?_
    (CubeValues.val_res _ valAt'_rules _ hm _))))
  dsimp only [LB.linCombIso, id]
  erw [Fintype.prod_unique, zpow_one]
  refine (CubeValues.val_res _ valAt'_rules _ hm _).trans ((CubeValues.val_pullU (𝟙 (Sp ℂ)) valAt'_rules
    (show Sp ℂ ⟶ _ from eSec G') (((L.pull φ).div L').U (fun _ => j, i)) (w.s (fun _ => j, i))).trans ?_)
  rw [Category.id_comp]
  rfl

theorem exists_push_iff {X : Scheme.{0}} (A : Out.PolAV X) (A' : Out.PolAV (Sp ℂ)) {y : Sp ℂ ⟶ X}
    {φ : A'.A.left ⟶ A.A.left} (h : IsGrpPullback A'.A A.A y φ) (hL : LBIso A'.L (A.L.pull φ)) :
    ∃ Φ : (𝟙_ (Over (Sp ℂ)) ⟶ A'.A) ≃* (Over.mk y ⟶ A.A), (∀ p, (Φ p).left = p.left ≫ φ) ∧
      ∀ (k : ℤ) p q c, Out.WeilIs A'.A A'.L k p q c ↔ Out.WeilIs A.A A.L k (Φ p) (Φ q) c := by
  have := A.isAb.comm
  have key : ∀ t, (𝟙_ (Over (Sp ℂ))).hom ≫ y = t →
      ∃ Φ : (𝟙_ (Over (Sp ℂ)) ⟶ A'.A) ≃* (Over.mk t ⟶ A.A), (∀ p, (Φ p).left = p.left ≫ φ) ∧
      ∀ (k : ℤ) p q c, Out.WeilIs A'.A A'.L k p q c ↔ Out.WeilIs A.A A.L k (Φ p) (Φ q) c := by
    rintro _ rfl
    exact ⟨ObjPull.pushEquiv h _, fun _ => rfl, fun k p q c =>
      weilIs_iff_of_isGrpPullback_comm _ _ A.A A'.A y φ A.L A'.L A.isLB A'.isLB h hL _ k p q _ _ c rfl rfl⟩
  exact key y (Category.id_comp y)

theorem exists_normal_fibre (hT : ThetaUnifAV) (hmul : Out.MulNSt) {S : Type} [CommRing S] (y : KeyIn S)
    (f : S →+* ℂ) (x : KeyIn ℂ) (hx : KeyPB x y f) (e : (Fin y.P.g → ℂ) → (Over.mk (spMap f) ⟶ y.P.A))
    (hadd : ∀ z w, e (z + w) = e z * e w) (hon : Function.Surjective e)
    (hol : IsHolTo Set.univ fun z => (e z).left) {La : Type} [AddCommGroup La]
    (EF : LinearMap.BilinForm ℤ La) (bs : Module.Basis (Fin y.P.g ⊕ Fin y.P.g) ℤ La)
    (hbs : IsSymplecticBasis (-EF) bs) (P : La →+ (Fin y.P.g → ℂ)) (hker : ∀ z, e z = 1 ↔ z ∈ P.range)
    (hweil : ∀ (k : ℕ) (a a₂ : La) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a a₂ : ℂ) / k) →
      Out.WeilIs y.P.A y.P.L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P a₂)) (unitOn c)) :
    ∃ (h τ : Matrix (Fin y.P.g) (Fin y.P.g) ℂ) (ab : (Fin y.P.g → ℝ) × (Fin y.P.g → ℝ)) (c : ℂ)
      (W : Fin y.P.g → Fin y.P.g → ℂ),
      τ.IsSymm ∧ ((τ.map Complex.im).PosDef ∧
        ∀ i, h *ᵥ P (bs (.inl i)) = Pi.single i 1 ∧ h *ᵥ P (bs (.inr i)) = τ *ᵥ Pi.single i 1) ∧
      ((∀ i, ab.1 i = 0 ∨ ab.1 i = 1 / 2) ∧ ∀ i, ab.2 i = 0 ∨ ab.2 i = 1 / 2) ∧ c ≠ 0 ∧
      (∀ j z, ⊤ ≤ (e z).left ⁻¹ᵁ y.P.L.U j → ∃ ρ : (Fin y.P.g → ℂ) → ℂ, ρ z ≠ 0 ∧
        (z = 0 → ρ 0 = c * valAt' (spMap f) ((y.P.L.pull (eSec y.P.A)).U fun _ => j) (y.rig.s fun _ => j).val) ∧
        ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ ρ w ∧
          ρ w * thetaChar τ (fun i => (ab.1 i : ℂ)) (fun i => (ab.2 i : ℂ)) (h *ᵥ w) =
            valAt' (e w).left (y.P.L.U j) (y.th.f j)) ∧
      (∀ i, IsDerivAt0 (fun z => (e z).left) (W i) (spMap (Chart.dualMapR f) ≫ (y.v i).left)) ∧
      ∃ (τ' M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ) (c' : ℂ), charHalf _ a b ∧ c' ≠ 0 ∧
        NormalAt x τ' M a b c' ∧
        (Matrix.of fun i => (2 * Real.pi * Complex.I : ℂ) • h *ᵥ W i).det ^ 4 / c ^ 8 = M.det ^ 4 / c' ^ 8 := by
  obtain ⟨φ, he, w, hg, F, hφ, hw, hrig, hth, hF₁, hF₂, hv⟩ := hx
  obtain rfl : F = Chart.dualMapR f := RingHom.ext fun d => by
    have hd : d = algebraMap S _ d.fst + algebraMap S _ d.snd * DualNumber.eps := by
      ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
    rw [hd, map_add (f := _), map_mul, hF₁, hF₁, hF₂]
    ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  obtain ⟨⟨A, isAb, g, sm, L, isLB, rigid, sym, ample, ktriv⟩, gp, rig, rg, th, tn, v, vb⟩ := y
  obtain rfl : x.P.g = g := hg
  obtain ⟨Φ, hΦ, hΦW⟩ := exists_push_iff _ x.P hφ ⟨w, hw⟩
  have h₁ : ∀ z, (Φ.symm (e z)).left ≫ φ = (e z).left := fun z => by rw [← hΦ, Φ.apply_symm_apply]
  have hol₁ : IsHolTo Set.univ fun z => (Φ.symm (e z)).left :=
    ThetaPoint.isHolTo_fibre hφ.1 _ (fun z => Over.w (Φ.symm (e z))) (by simpa only [h₁] using hol)
  obtain ⟨u, k, τ, a, b, c, W, hu, hs, hp, hk, ha, hb, hc, hΛ, hR, hfn, hW⟩ := exists_normal_of_weil hT hmul x
    (fun z => Φ.symm (e z)) (fun z w => by rw [hadd, map_mul]) (Φ.symm.surjective.comp hon) hol₁ EF bs hbs P
    (fun z => (map_eq_one_iff _ Φ.symm.injective).trans (hker z)) fun k a a₂ c hk hc => by
      rw [hΦW, Φ.apply_symm_apply, Φ.apply_symm_apply]
      exact hweil k a a₂ c hk hc
  let h : Matrix (Fin x.P.g) (Fin x.P.g) ℂ := LinearMap.toMatrix' k.symm.toLinearEquiv.toLinearMap
  have hh : ∀ z, h *ᵥ z = k.symm z := fun z => LinearMap.toMatrix'_mulVec _ z
  have hu' : ∀ z, (u.ex (k.symm z)).left = (Φ.symm (e z)).left := fun z => by rw [hu, k.apply_symm_apply]
  refine ⟨h, τ, (a, b), c, fun i => k (W i), hs, ⟨hp, fun i => ⟨?_, ?_⟩⟩, ⟨ha, hb⟩, hc, fun j z hz => ?_, fun i => ?_,
    τ, _, fun i => a i, fun i => b i, c, ⟨fun i => (ha i).imp (fun h => by simp [h]) (fun h => by simp [h]),
      fun i => (hb i).imp (fun h => by simp [h]) (fun h => by simp [h])⟩, hc,
    ⟨u, hs, hp, hΛ, hR, hfn, fun i => ?_⟩, rfl⟩
  · rw [hh, ← (hk i).1, k.symm_apply_apply]
  · rw [hh, ← (hk i).2, k.symm_apply_apply]
  · obtain ⟨i, hi⟩ := exists_chart x.P.isLB ((Φ.symm (e z)).left (default : PrimeSpectrum ℂ))
    have hO : ⊤ ≤ (Φ.symm (e z)).left ⁻¹ᵁ ((L.pull φ).U (fun _ => j) ⊓ x.P.L.U i) :=
      (top_le_preimage_inf _ _ _).2 ⟨(ThetaPoint.top_le_pull_iff _ _ _ _).2 (by rw [h₁]; exact hz),
        (top_le_preimage_iff_mem _ _).2 hi⟩
    have hi' : ∀ w, ⊤ ≤ (Φ.symm (e w)).left ⁻¹ᵁ ((L.pull φ).U (fun _ => j) ⊓ x.P.L.U i) →
        ⊤ ≤ (u.ex (k.symm w)).left ⁻¹ᵁ x.P.L.U i := fun w hw => by
      rw [hu']
      exact top_le_preimage_mono _ inf_le_right hw
    refine ⟨fun q => valAt' (Φ.symm (e q)).left ((L.pull φ).U (fun _ => j) ⊓ x.P.L.U i) (w.s (fun _ => j, i)).val *
      (c * u.fr i (k.symm q)), mul_ne_zero (valAt'_unit_ne_zero _ hO _) (mul_ne_zero hc (u.fr_ne _ _ (hi' z hO))),
      ?_, ?_⟩
    · rintro rfl
      have e0 : (Φ.symm (e 0)).left = eSec x.P.A := by
        rw [← hu', map_zero]
        exact TangentOrigin.ex_zero_left u
      have := isAb.comm
      have := x.P.isAb.comm
      rw [e0] at hO
      beta_reduce
      rw [valAt'_rig he w x.rig rig hrig j i hO, e0, map_zero,
        hR (fun _ => i) fun p hq => mem_pull.2 (hO hq).2, mul_left_comm]
    · filter_upwards [LocalLift.hol_eventually_mem hol₁ (Set.mem_univ z) hO] with q hq
      refine ⟨(LocalLift.hol_differentiableAt hol₁ (Set.mem_univ q) hq.2 _).mul (DifferentiableAt.const_mul ?_ c), ?_⟩
      · exact ((u.fr_hol i).differentiableAt ((u.hol _ 0).1.mem_nhds (hi' q hq.2))).comp q k.symm.differentiableAt
      · rw [← h₁ q, valAt'_via w th x.th hth _ j i hq.2, ← hu' q, hfn i _ (hi' q hq.2), hh]
        ring
  · have d := FibreDeriv.isDerivAt0_comp (e := fun z => (u.ex z).left)
      ⟨TangentOrigin.tangent_comp (x.basis.1 i), hW i⟩ φ
    simp only [hu, h₁] at d
    have d' := (LocLift.isDerivAt0_comp (e := fun z => (e z).left) k _ _).1 d
    rw [hv i] at d'
    exact d'
  · change u.IsDiff ((2 * Real.pi * Complex.I : ℂ)⁻¹ • (2 * Real.pi * Complex.I : ℂ) • h *ᵥ k (W i)) _
    rw [inv_smul_smul₀ Complex.two_pi_I_ne_zero, hh, k.symm_apply_apply]
    exact hW i

end GlobalTheory.ThetaValueCont
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ContinuousOnThetaFrameValueHolomorphicFamily
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open Filter Topology
open scoped Matrix

namespace GlobalTheory.ThetaValueCont

open GlobalTheory.LocLift GlobalTheory.TangentOrigin

theorem isHolTo_spMap {V A : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CommRing A] {B : Set V} (hB : IsOpen B)
    (ev : V → (A →+* ℂ)) (h : ∀ a, DifferentiableOn ℂ (fun b => ev b a) B) : IsHolTo B fun b => spMap (ev b) := by
  intro U f
  have key : ∀ b₀ ∈ B, ⊤ ≤ spMap (ev b₀) ⁻¹ᵁ U → (∀ᶠ b in 𝓝 b₀, b ∈ B ∧ ⊤ ≤ spMap (ev b) ⁻¹ᵁ U) ∧
      DifferentiableAt ℂ (fun b => valAt' (spMap (ev b)) U f) b₀ := by
    intro b₀ hb₀ h₀
    obtain ⟨r, a, hr, H⟩ := HolLieFrame.exists_fraction (𝟙 (Sp A)) U f (ev b₀) (by rwa [Category.comp_id])
    have d := fun a => (h a).differentiableAt (hB.mem_nhds hb₀)
    have hev : ∀ᶠ b in 𝓝 b₀, ⊤ ≤ spMap (ev b) ⁻¹ᵁ U ∧ valAt' (spMap (ev b)) U f = ev b a * (ev b r)⁻¹ := by
      filter_upwards [(d r).continuousAt.eventually_ne hr] with b hb
      obtain ⟨h₁, h₂⟩ := H ℂ (ev b) hb.isUnit
      rw [← valAt'_eq_evalPt] at h₂
      rw [Category.comp_id] at h₁ h₂
      exact ⟨h₁, (eq_mul_inv_iff_mul_eq₀ hb).2 h₂⟩
    exact ⟨(hev.mono fun b hb => hb.1).and (hB.mem_nhds hb₀) |>.mono fun b hb => ⟨hb.2, hb.1⟩,
      ((d a).mul ((d r).inv hr)).congr_of_eventuallyEq (hev.mono fun b hb => hb.2)⟩
  exact ⟨isOpen_iff_mem_nhds.2 fun b hb => (key b hb.1 hb.2).1,
    fun b hb => (key b hb.1 hb.2).2.differentiableWithinAt⟩

theorem differentiableAt_tangent {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {g m : ℕ}
    {B : Set (Fin m → ℂ)} {b₀ : Fin m → ℂ} (hB : B ∈ 𝓝 b₀) (ev : (Fin m → ℂ) → (R →+* ℂ))
    (hev : ∀ c, DifferentiableAt ℂ (fun b => ev b c) b₀) {e : ∀ b, (Fin g → ℂ) → (Over.mk (spMap (ev b)) ⟶ G)}
    (hol : IsHolTo (B ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (e bz.1 bz.2).left))
    (he : IsExp (spMap (ev b₀)) (e b₀)) (ψ : Sp (DualNumber R) ⟶ G.left) {W : (Fin m → ℂ) → Fin g → ℂ}
    (hW : ∀ b ∈ B, IsDerivAt0 (fun z => (e b z).left) (W b) (spMap (Chart.dualMapR (ev b)) ≫ ψ)) :
    DifferentiableAt ℂ W b₀ := by
  have hb₀ := mem_of_mem_nhds hB
  refine HolLieFrame.differentiableAt_of_forms _ b₀ fun w hw => ?_
  have hw' : ∀ (O : G.left.Opens) (f : Γ(G.left, O)), ⊤ ≤ (e b₀ 0).left ⁻¹ᵁ O →
      fderiv ℂ (fun z => valAt' (e b₀ z).left O f) 0 w = 0 := by
    intro O f hO
    refine hw (fun b => fderiv ℂ (fun z => valAt' (e b z).left O f) 0)
      (HolLieFrame.differentiableAt_fderiv (e := fun b z => (e b z).left) hol hb₀ O f hO) ?_
    obtain ⟨F, hF, hF'⟩ := HolLieFrame.exists_hol_snd ψ ev b₀ hev O f
      ((top_le_preimage_iff _ O).2 (by rw [(hW b₀ hb₀).1]; exact hO))
    refine hF.congr_of_eventuallyEq ?_
    filter_upwards [hF', hB] with b ⟨h, e⟩ hb
    exact ((hW b hb).2 O h f).symm.trans e
  have d₁ := LocalLift.isDerivAt0_const (fun z => (e b₀ z).left) w hw'
  have d₀ := LocalLift.isDerivAt0_const (fun z => (e b₀ z).left) 0 fun _ _ _ => map_zero _
  let v₀ : epsPt (spMap (ev b₀)) ⟶ G :=
    Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ (e b₀ 0).left)
      ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Over.w (e b₀ 0))))
  exact (he.2.2.2.2 v₀ d₁.1).unique d₁ d₀

theorem exists_exp_fibre (hT : ThetaUnifAV) {S : Type} [CommRing S] (y : KeyIn S) (f : S →+* ℂ) (x : KeyIn ℂ)
    (hx : KeyPB x y f) : ∃ (e : (Fin y.P.g → ℂ) → (Over.mk (spMap f) ⟶ y.P.A)) (Λ : Submodule ℤ (Fin y.P.g → ℂ))
      (EF : LinearMap.BilinForm ℤ Λ) (bs : Module.Basis (Fin y.P.g ⊕ Fin y.P.g) ℤ Λ), IsExp (spMap f) e ∧
      IsSymplecticBasis (-EF) bs ∧ Submodule.span ℝ (Λ : Set (Fin y.P.g → ℂ)) = ⊤ ∧ (∀ z, e z = 1 ↔ z ∈ Λ) ∧
      ∀ (k : ℕ) (a a₂ : Λ) (c : ℂˣ), 0 < k →
        (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a a₂ : ℂ) / k) →
        Out.WeilIs y.P.A y.P.L k (e ((k : ℂ)⁻¹ • (a : Fin y.P.g → ℂ))) (e ((k : ℂ)⁻¹ • (a₂ : Fin y.P.g → ℂ)))
          (unitOn c) := by
  obtain ⟨φ, -, w, hg, -, hφ, hw, -⟩ := hx
  obtain ⟨⟨A, isAb, g, sm, L, isLB, rigid, sym, ample, ktriv⟩, gp, rig, rg, th, tn, v, vb⟩ := y
  obtain rfl : x.P.g = g := hg
  obtain ⟨Φ, hΦ, hΦW⟩ := exists_push_iff _ x.P hφ ⟨w, hw⟩
  obtain ⟨u, Hm, χ, Ef, hAH, -, h₁, h₂, -, -, hE, hbij, hW⟩ := hT x.P x.rig x.rig_gen
  have := u.discrete
  have : IsZLattice ℝ u.Λ := ⟨u.full⟩
  have halt : Ef.IsAlt := fun l => by
    have h1 := congrArg Complex.im (SiegelNormalForm.form_conj hAH.1 (l : Fin x.P.g → ℂ) l)
    have h2 := hE l l
    simp only [Complex.star_def, Complex.conj_im] at h1
    rw [hermForm] at h2
    have : (Ef l l : ℝ) = 0 := by linarith
    exact_mod_cast this
  have hrank : Module.finrank ℤ u.Λ = 2 * x.P.g := by
    rw [ZLattice.rank ℝ u.Λ, Module.finrank_pi_fintype]
    simp [mul_comm]
  obtain ⟨bs, hbs⟩ := exists_isSymplecticBasis_of_finrank (B := -Ef) halt.neg (bijective_neg_bilinForm hbij) hrank
  exact ⟨fun z => Φ (u.ex z), u.Λ, Ef, bs, PointUnif.isExp_push hφ u h₁ h₂ Φ hΦ, hbs, u.full,
    fun z => (map_eq_one_iff Φ Φ.injective).trans (u.ker z), fun k a a₂ c hk hc => (hΦW _ _ _ _).1 (hW k a a₂ c hk hc)⟩

theorem continuousAt_frame_constant {X : Scheme.{0}} {G : Over X} [GrpObj G] {L : LB G.left} (hL : L.IsLB)
    (rig : LB.Gen (L.pull (eSec G))) (sec : L.Sec) {g m : ℕ} {C : Set (Fin m → ℂ)} (hCo : IsOpen C) {b₀ : Fin m → ℂ}
    (hC₀ : b₀ ∈ C) {pt : (Fin m → ℂ) → (Sp ℂ ⟶ X)} (hy : IsHolTo C pt)
    {e : (Fin m → ℂ) → (Fin g → ℂ) → (Sp ℂ ⟶ G.left)} (e0 : e b₀ 0 = pt b₀ ≫ eSec G)
    (hol : IsHolTo (C ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => e bz.1 bz.2))
    {p q : Fin g → (Fin m → ℂ) → (Fin g → ℂ)} (hp : ∀ k, DifferentiableOn ℂ (p k) C)
    (hq : ∀ k, DifferentiableOn ℂ (q k) C) {h τ : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ}
    {κ : (Fin m → ℂ) → (Fin g → ℝ) × (Fin g → ℝ)} {c : (Fin m → ℂ) → ℂ} (f₁ : (τ b₀).IsSymm)
    (f₂ : ∀ b ∈ C, ((τ b).map Complex.im).PosDef ∧
      ∀ i, h b *ᵥ p i b = Pi.single i 1 ∧ h b *ᵥ q i b = τ b *ᵥ Pi.single i 1)
    (f₃ : ∀ b ∈ C, (∀ i, (κ b).1 i = 0 ∨ (κ b).1 i = 1 / 2) ∧ ∀ i, (κ b).2 i = 0 ∨ (κ b).2 i = 1 / 2)
    (f₅ : ∀ b ∈ C, ∀ j z, ⊤ ≤ e b z ⁻¹ᵁ L.U j → ∃ ρ : (Fin g → ℂ) → ℂ, ρ z ≠ 0 ∧
      (z = 0 → ρ 0 = c b * valAt' (pt b) ((L.pull (eSec G)).U fun _ => j) (rig.s fun _ => j).val) ∧
      ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ ρ w ∧
        ρ w * thetaChar (τ b) (fun i => ((κ b).1 i : ℂ)) (fun i => ((κ b).2 i : ℂ)) (h b *ᵥ w) =
          valAt' (e b w) (L.U j) (sec.f j)) : ContinuousAt c b₀ := by
  have half : ∀ {a : Fin g → ℝ}, (∀ i, a i = 0 ∨ a i = 1 / 2) → ∀ i, (a i : ℂ) = 0 ∨ (a i : ℂ) = 1 / 2 :=
    fun ha i => (ha i).imp (fun h => by simp [h]) (fun h => by simp [h])
  have fin : (Set.pi Set.univ fun _ : Fin g => ({0, 1 / 2} : Set ℝ)).Finite := Set.Finite.pi fun _ => Set.toFinite _
  have hK : {k : (Fin g → ℝ) × (Fin g → ℝ) |
      (∀ i, k.1 i = 0 ∨ k.1 i = 1 / 2) ∧ ∀ i, k.2 i = 0 ∨ k.2 i = 1 / 2}.Finite :=
    (fin.prod fin).subset fun k hk => ⟨fun i _ => hk.1 i, fun i _ => hk.2 i⟩
  obtain ⟨θ, hθ⟩ : ∃ θ : (Fin g → ℝ) × (Fin g → ℝ) → (Fin m → ℂ) × (Fin g → ℂ) → ℂ, ∀ k, θ k = fun bz =>
    thetaChar (τ bz.1) (fun i => (k.1 i : ℂ)) (fun i => (k.2 i : ℂ)) (h bz.1 *ᵥ bz.2) := ⟨_, fun _ => rfl⟩
  have th := fun (k : (Fin g → ℝ) × (Fin g → ℝ)) (h₁ : ∀ i, k.1 i = 0 ∨ k.1 i = 1 / 2)
    (h₂ : ∀ i, k.2 i = 0 ∨ k.2 i = 1 / 2) => ThetaFamily.thetaChar_family hp hq f₂ (half h₁) (half h₂)
  refine continuousAt_constant (B := C) hK (κ := κ) (θ := θ)
    (W := fun j => {bz ∈ C ×ˢ (Set.univ : Set (Fin g → ℂ)) | ⊤ ≤ e bz.1 bz.2 ⁻¹ᵁ L.U j})
    (f := fun j bz => valAt' (e bz.1 bz.2) (L.U j) (sec.f j))
    (r := fun j b => valAt' (pt b) ((L.pull (eSec G)).U fun _ => j) (rig.s fun _ => j).val)
    (fun j => (hol (L.U j) 0).1) (fun j w hw => hw.1.1) (fun j => (hol (L.U j) (sec.f j)).2)
    (fun k hk j => ?_) (fun k hk => ?_) f₃ (fun j b z hz => ?_) (hCo.mem_nhds hC₀) (fun z => ?_)
    (fun k hk ρ h1 h2 h3 => ?_) fun j hj => ?_
  · rw [hθ]
    exact (th k hk.1 hk.2).1.mono fun w hw => hw.1
  · rw [hθ]
    exact (th k hk.1 hk.2).2
  · rw [hθ]
    exact f₅ b hz.1.1 j z hz.2
  · obtain ⟨j, hj⟩ := exists_chart hL (e b₀ z (default : PrimeSpectrum ℂ))
    exact ⟨j, ⟨hC₀, trivial⟩, (top_le_preimage_iff_mem _ _).2 hj⟩
  · have hinv : h b₀ * Matrix.of (fun i k => p k b₀ i) = 1 := by
      ext i k
      have := congrFun ((f₂ b₀ hC₀).2 k).1 i
      rw [Matrix.one_apply, ← Pi.single_apply k (1 : ℂ) i, ← this]
      rfl
    generalize Matrix.of (fun i k => p k b₀ i) = N at hinv
    have dl : Differentiable ℂ (fun w : Fin g → ℂ => N *ᵥ w) :=
      (LinearMap.toContinuousLinearMap (Matrix.mulVecLin N)).differentiable
    obtain ⟨e₁, e₂⟩ := ThetaPoint.half_char_unique f₁ (f₂ b₀ hC₀).1 (f₃ b₀ hC₀).1 (f₃ b₀ hC₀).2 hk.1 hk.2
      (h1.comp dl) (fun z => h2 _) fun z => by
        have := h3 (N *ᵥ z)
        simp only [hθ, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec, CanTh.thetaChar_eq_theta] at this
        exact this.symm
    exact Prod.ext e₁ e₂
  · have h0 : ⊤ ≤ pt b₀ ⁻¹ᵁ (L.pull (eSec G)).U fun _ => j := by
      have : ⊤ ≤ e b₀ 0 ⁻¹ᵁ L.U j := hj.2
      rw [e0] at this
      exact fun p hp => mem_pull.2 (this hp)
    exact ⟨(LocalLift.hol_differentiableAt hy hC₀ h0 _).continuousAt, valAt'_unit_ne_zero _ h0 _⟩

theorem continuousOn_value : Out.Laws → ThetaUnifAV → Key.Chi.InversionStatement → ∀ (S : Type) [CommRing S] [Algebra ℂ S] [Algebra.FiniteType ℂ S] (y : KeyIn S) (m : ℕ) (B : Set (Fin m → ℂ)) (s : (Fin m → ℂ) → (S →ₐ[ℂ] ℂ)) (t : (Fin m → ℂ) → ℂ), IsOpen B → (∀ a : S, DifferentiableOn ℂ (fun p => s p a) B) → (∀ p ∈ B, ∃ x : KeyIn ℂ, KeyPB x y (s p).toRingHom ∧ (∃ (τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ) (c : ℂ), charHalf _ a b ∧ c ≠ 0 ∧ NormalAt x τ M a b c ∧ t p = M.det ^ 4 / c ^ 8)) → ContinuousOn t B := by
  intro hL hT hI S _ _ _ y m B s t hB hs ht b₀ hb₀
  choose x hx hv using ht
  let ev : (Fin m → ℂ) → (S →+* ℂ) := fun b => (s b).toRingHom
  let pt : (Fin m → ℂ) → (Sp ℂ ⟶ Sp S) := fun b => spMap (ev b)
  have hy : IsHolTo B pt := isHolTo_spMap hB ev hs
  obtain ⟨e₀, Λ, EF, bs, he₀, hbs, hfull, k₀, w₀⟩ := exists_exp_fibre hT y _ _ (hx b₀ hb₀)
  have hft : LocallyOfFiniteType (spMap (algebraMap ℂ S)) :=
    HasRingHomProperty.Spec_iff.2 (RingHom.finiteType_algebraMap.2 inferInstance)
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing ℂ S
  have := y.P.isAb.proper
  obtain ⟨B₁, e, r, hB₁, hb₁, hB₁B, rfl, hr, hol, he, hl⟩ := RelExp.exists_relative_exp ℂ (RingHom.id ℂ) (Sp S)
    (spMap (algebraMap ℂ S)) y.P.A y.P.g m B pt b₀ e₀ hft y.P.isAb y.P.smoothDim hB hb₀ (fun b _ => by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      exact RingHom.ext fun a => (s b).commutes a) hy he₀
  change HasLifts B₁ pt e at hl
  change ∀ b ∈ B₁, IsExp (pt b) (e b) ∧ _ at he
  have := Module.Free.of_basis bs
  have := Module.Finite.of_basis bs
  obtain ⟨P, hP₀, hP⟩ := exists_periods latContinuation hB₁ hb₁ (isHolTo_mono hy hB₁ hB₁B) hr hol he hl
    Λ.subtype.toAddMonoidHom Subtype.val_injective
    (by rw [← hfull]; congr 1; exact Subtype.range_val) (fun z => (k₀ z).trans
      ⟨fun h => ⟨⟨z, h⟩, rfl⟩, fun ⟨l, h⟩ => h ▸ l.2⟩)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hP.and (hB₁.mem_nhds hb₁))
  set C := Metric.ball b₀ ε
  have hCo : IsOpen C := Metric.isOpen_ball
  have hCc : IsPreconnected C := (convex_ball b₀ ε).isPreconnected
  have hC₀ : b₀ ∈ C := Metric.mem_ball_self hε
  have hCn := hCo.mem_nhds hC₀
  have hC₁ : C ⊆ B₁ := fun b hb => (hball b hb).2
  have hCB : C ⊆ B := hC₁.trans hB₁B
  have hPd : ∀ x, DifferentiableOn ℂ (fun b => P b x) C := fun x b hb => ((hball b hb).1.1 x).differentiableWithinAt
  have hk1 : ∀ b ∈ C, ∀ x, e b (P b x) = 1 := fun b hb x => ((hball b hb).1.2.1 _).2 ⟨x, rfl⟩
  have htor : ∀ (k : ℕ) x, IsHolTo C (fun b => (e b ((k : ℂ)⁻¹ • P b x)).left) := fun k x =>
    isHolTo_comp (β := fun b => (b, (k : ℂ)⁻¹ • P b x)) hol hCo
      (differentiableOn_id.prodMk ((hPd x).fun_const_smul _)) fun b hb => ⟨hC₁ hb, trivial⟩
  have hpow : ∀ (k : ℕ), 0 < k → ∀ x, ∀ b ∈ C, e b ((k : ℂ)⁻¹ • P b x) ^ k = 1 := fun k hk x b hb => by
    rw [← hom_nsmul (he b (hC₁ hb)).1.1, ← Nat.cast_smul_eq_nsmul ℂ, smul_inv_smul₀ (Nat.cast_ne_zero.2 hk.ne'),
      hk1 b hb]
  have hwe : ∀ b ∈ C, ∀ (k : ℕ) (a a₂ : Λ) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a a₂ : ℂ) / k) →
      Out.WeilIs y.P.A y.P.L k (e b ((k : ℂ)⁻¹ • P b a)) (e b ((k : ℂ)⁻¹ • P b a₂)) (unitOn c) :=
    fun b hb k a a₂ c hk hc => (torsion_eq_and_weilIs_of_isHolTo hL (Sp S) y.P m k C pt
      (fun b => e b ((k : ℂ)⁻¹ • P b a)) (fun b => e b ((k : ℂ)⁻¹ • P b a₂)) c b₀ hk
      (isUnit_natCast_of_over (spMap (algebraMap ℂ S)) hk) hCo hCc hC₀ (htor k a) (htor k a₂)
      fun b hb => ⟨hpow k hk a b hb, hpow k hk a₂ b hb⟩).2 (by rw [hP₀]; exact w₀ k a a₂ c hk hc) b hb
  have fib := fun b (hb : b ∈ C) => exists_normal_fibre hT hL.mulN y (ev b) _ (hx b (hCB hb)) (e b)
    (he b (hC₁ hb)).1.1 (he b (hC₁ hb)).1.2.1 (he b (hC₁ hb)).1.2.2.1 EF bs hbs (P b) (hball b hb).1.2.1 (hwe b hb)
  choose! h τ κ c W f₁ f₂ f₃ f₄ f₅ f₆ f₇ using fib
  have ht : ∀ b ∈ C, t b = (Matrix.of fun i => (2 * Real.pi * Complex.I : ℂ) • h b *ᵥ W b i).det ^ 4 / c b ^ 8 :=
    fun b hb => _root_.GlobalTheory.NormalUnique.thetaFrame_value_unique hT hI _ _ _ (hv b (hCB hb)) (f₇ b hb)
  have hinv : ∀ b ∈ C, h b * Matrix.of (fun i k => P b (bs (.inl k)) i) = 1 := fun b hb => by
    ext i k
    have := congrFun ((f₂ b hb).2 k).1 i
    rw [Matrix.one_apply, ← Pi.single_apply k (1 : ℂ) i, ← this]
    rfl
  have dh : ∀ i j, DifferentiableOn ℂ (fun b => h b i j) C :=
    ThetaFamily.differentiableOn_left_inverse (fun i k => differentiableOn_pi.1 (hPd _) i) hinv
  have holC := isHolTo_mono hol (hCo.prod isOpen_univ) (Set.prod_mono hC₁ le_rfl)
  have cc : ContinuousAt c b₀ := continuousAt_frame_constant y.P.isLB y.rig y.th hCo hC₀ (isHolTo_mono hy hCo hCB)
    (e := fun b z => (e b z).left) ((congrArg (·.left) (hom_zero (he b₀ hb₁).1.1)).trans (one_left _)) holC
    (p := fun k b => P b (bs (.inl k))) (q := fun k b => P b (bs (.inr k))) (fun k => hPd _) (fun k => hPd _)
    (f₁ b₀ hC₀) f₂ f₃ f₅
  have cW : ∀ i, ContinuousAt (fun b => W b i) b₀ := fun i =>
    (differentiableAt_tangent hCn ev (fun a => (hs a).differentiableAt (hB.mem_nhds hb₀)) holC (he b₀ hb₁).1
      (y.v i).left fun b hb => f₆ b hb i).continuousAt
  have cM : ContinuousAt (fun b => Matrix.of fun i => (2 * Real.pi * Complex.I : ℂ) • h b *ᵥ W b i) b₀ := by
    refine continuousAt_pi.2 fun i => continuousAt_pi.2 fun j => ?_
    simp only [Matrix.of_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
    exact continuousAt_const.mul (tendsto_finsetSum _ fun l _ =>
      ((dh j l).differentiableAt hCn).continuousAt.mul (continuousAt_pi.1 (cW i) l))
  refine ContinuousAt.continuousWithinAt (ContinuousAt.congr ?_ (Filter.eventuallyEq_of_mem hCn ht).symm)
  exact ((continuous_id.matrix_det.continuousAt.comp cM).pow 4).div (cc.pow 8) (pow_ne_zero _ (f₄ b₀ hC₀))

end GlobalTheory.ThetaValueCont
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ContinuousOnThetaFrameValueHolomorphicFamilyStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuousOn_thetaFrameValue_holomorphicFamily : Out.Laws → ThetaUnifAV → Key.Chi.InversionStatement → ∀ (S : Type) [CommRing S] [Algebra ℂ S] [Algebra.FiniteType ℂ S] (y : KeyIn S) (m : ℕ) (B : Set (Fin m → ℂ)) (s : (Fin m → ℂ) → (S →ₐ[ℂ] ℂ)) (t : (Fin m → ℂ) → ℂ), IsOpen B → (∀ a : S, DifferentiableOn ℂ (fun p => s p a) B) → (∀ p ∈ B, ∃ x : KeyIn ℂ, KeyPB x y (s p).toRingHom ∧ (∃ (τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ) (c : ℂ), charHalf _ a b ∧ c ≠ 0 ∧ NormalAt x τ M a b c ∧ t p = M.det ^ 4 / c ^ 8)) → ContinuousOn t B := by
  first | exact @GlobalTheory.ThetaValueCont.continuousOn_value | exact GlobalTheory.ThetaValueCont.continuousOn_value | (intros; apply GlobalTheory.ThetaValueCont.continuousOn_value <;> assumption)
end
