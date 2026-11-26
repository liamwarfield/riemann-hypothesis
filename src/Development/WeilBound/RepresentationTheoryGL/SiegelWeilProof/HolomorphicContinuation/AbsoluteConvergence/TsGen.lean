module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.IteratedDerivOfReal
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.FarRightAlt

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.TsGenOf
noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

set_option maxHeartbeats 1600000 in
theorem tsGen_of (hD : CayleyBlocksInvertible) (hK : KAK) (hM : Mult) (hS : SecZero) (hDF : DerivativeVacuumDilations)
    (hH : HolParam) (hLC : LC) (hT : TSBFacts) : TSGen := by
  intro m n ε c t p q e sL ρ hL G _ _ _ _ _ _ Pp Γ ι s₀ Ht sec I Λ hG _ _ W hWf hWρ ν κ hν hκ hfix hproj gpt y Q hQW hQ
  haveI := hν
  haveI : FiniteDimensional ℂ W := hWf
  obtain ⟨hKc, hmRc, hF0c, hdilex, hdilmat, hext⟩ := hT hD n p q e
  haveI := hKc
  have hc0 : 0 < c := hL.cpos
  have hIsec : ∀ Q1 Q2 : PX m n, (∀ y', sL Q1 y' = sL Q2 y') → I Q1 gpt = I Q2 gpt := by
    intro Q1 Q2 h12
    have hnull : NullSec ε c (Q1 - Q2) :=
      (hS m n ε c t p q e sL ρ hL (Q1 - Q2)).2 (fun y' => by simp [map_sub, h12 y'])
    have h0 := hLC m n ε c hc0 ((LinearMap.proj gpt).comp I)
      (fun a b P => by simpa using hG.Iinv gpt a b P) (Q1 - Q2) hnull
    have h1 : I Q1 gpt - I Q2 gpt = 0 := by simpa [map_sub] using h0
    exact sub_eq_zero.1 h1
  have hπ : ∀ f : GR n → ℂ, Continuous f → (∀ (y g : GR n), (mR y).toBlocks₂₁ = 0 → f (y * g) = F0 p q e y * f g) →
      ∃ Q1 ∈ W, ∀ y', ∫ k, κ k * f (y' * (k : GR n)) ∂ν = sL Q1 y' := by
    intro f hf hlaw
    obtain ⟨Q1, hQ1, h1⟩ := hproj 0 f hf (fun y g hy => by rw [hlaw y g hy]; simp)
    exact ⟨Q1, hQ1, fun y' => by rw [h1 y']; simp⟩
  obtain ⟨k1, k2, a, X, hk1, hk2, ha, rfl⟩ := hK n y
  have hF2 : F0 p q e k2 ≠ 0 := right_ne_zero_of_mul_eq_one (spherical_character_inv_mul hM n p q e k2 hk2)
  have key : ∀ Q' ∈ W, (∀ y', ∫ k, κ k * F0 p q e (y' * (k : GR n) * (k1 * a)) ∂ν = sL Q' y') →
      ∫ k, κ k * I 1 (gpt * ι ((k : GR n) * (k1 * a))) ∂ν = I Q' gpt := by
    intro Q' hQ'W hQ'
    choose af haf using hdilex X
    have ha1 : af 1 = a := by
      apply Subtype.ext
      apply Units.ext
      show mR (af 1) = mR a
      rw [hdilmat X 1 (af 1) (haf 1), hdilmat X 1 a ha]
    obtain ⟨U1, Fid, hU1o, hU1R, hFidc, hFid⟩ := hG.Idil gpt X af haf

    let V : Submodule ℂ (GR n → ℂ) := W.map sL
    obtain ⟨Bm, hBm⟩ := LinearMap.exists_rightInverse_of_surjective (LinearMap.submoduleMap sL W)
      (LinearMap.range_eq_top.2 (LinearMap.submoduleMap_surjective sL W))
    let ℓ : Module.Dual ℂ V := ((LinearMap.proj gpt).comp I).comp (W.subtype.comp Bm)
    have hℓ : ∀ (v : V) (Q1 : PX m n), (∀ y', sL Q1 y' = (v : GR n → ℂ) y') → ℓ v = I Q1 gpt := by
      intro v Q1 h1
      have hv : (LinearMap.submoduleMap sL W) (Bm v) = v := LinearMap.congr_fun hBm v
      have hv' : sL ((Bm v : W) : PX m n) = (v : GR n → ℂ) := by
        have := congrArg (fun w : V => (w : GR n → ℂ)) hv
        simpa [LinearMap.submoduleMap] using this
      show I ((Bm v : W) : PX m n) gpt = I Q1 gpt
      exact hIsec _ _ (fun y' => by rw [hv', h1 y'])
    have hspan := GlobalTheory.dual_mem_span_eval_of_finiteDimensional V ℓ
    obtain ⟨cf, hcf⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hspan
    have hℓeval : ∀ v : V, ℓ v = ∑ y ∈ cf.support, cf y * (v : GR n → ℂ) y := by
      intro v
      rw [← hcf]
      simp [Finsupp.sum, LinearMap.sum_apply]

    set S := cf.support
    let C : Set (GR n) := ⋃ y ∈ S, range (fun k : KR n => y * (k : GR n) * k1)
    have hCc : IsCompact C := S.isCompact_biUnion fun y _ =>
      isCompact_range (cont_KR_mul n y k1)
    have hmemC : ∀ y ∈ S, ∀ k : KR n, y * (k : GR n) * k1 ∈ C := fun y hy k =>
      mem_biUnion hy ⟨k, rfl⟩
    obtain ⟨U2, hU2o, hU2R, hU2c, hU2d⟩ := hext X C hCc
    set U := U1 ∩ U2 with hUdef
    have hUo : IsOpen U := hU1o.inter hU2o
    have hUR : ∀ x : ℝ, (x : ℂ) ∈ U := fun x => ⟨hU1R x, hU2R x⟩
    have hcomp : IsCompact (univ : Set (KR n)) := isCompact_univ
    have hnull : ν (univ : Set (KR n))ᶜ = 0 := by simp

    have hFlc : ContinuousOn (fun yz : KR n × ℂ => κ yz.1 * Fid ((yz.1 : GR n) * k1) yz.2) (univ ×ˢ U) :=
      contOn_Fid k1 U U1 inter_subset_left κ hκ Fid hFidc
    have hFld : ∀ k ∈ (univ : Set (KR n)), DifferentiableOn ℂ (fun z => κ k * Fid ((k : GR n) * k1) z) U := by
      intro k _
      exact (((hFid ((k : GR n) * k1)).1.mono inter_subset_left).const_mul (κ k))
    obtain ⟨hLd, hLr⟩ := hH (KR n) ν univ hcomp hnull U (fun k z => κ k * Fid ((k : GR n) * k1) z) hUo hFlc hFld

    have hFrc : ∀ y ∈ S, ContinuousOn (fun yz : KR n × ℂ => κ yz.1 * twistedScalarSection p q e (mR (y * (yz.1 : GR n) * k1) * aZ X yz.2))
        (univ ×ˢ U) := fun y hy =>
      continuousOn_twisted_section_compact p q e X y k1 U κ hκ C (hmemC y hy) (hU2c.mono (prod_mono subset_rfl inter_subset_right))
    have hFrd : ∀ y ∈ S, ∀ k ∈ (univ : Set (KR n)),
        DifferentiableOn ℂ (fun z => κ k * twistedScalarSection p q e (mR (y * (k : GR n) * k1) * aZ X z)) U := by
      intro y hy k _
      exact (((hU2d _ (hmemC y hy k)).mono inter_subset_right).const_mul (κ k))
    have hRy : ∀ y ∈ S, DifferentiableOn ℂ (fun z => ∫ k, κ k * twistedScalarSection p q e (mR (y * (k : GR n) * k1) * aZ X z) ∂ν) U ∧
        ∀ z ∈ U, ∀ r : ℕ, iteratedDeriv r (fun z => ∫ k, κ k * twistedScalarSection p q e (mR (y * (k : GR n) * k1) * aZ X z) ∂ν) z = ∫ k, iteratedDeriv r (fun z => κ k * twistedScalarSection p q e (mR (y * (k : GR n) * k1) * aZ X z)) z ∂ν :=
      fun y hy => hH (KR n) ν univ hcomp hnull U (fun k z => κ k * twistedScalarSection p q e (mR (y * (k : GR n) * k1) * aZ X z)) hUo (hFrc y hy) (hFrd y hy)
    let Lt : ℂ → ℂ := fun z => ∫ k, κ k * Fid ((k : GR n) * k1) z ∂ν
    let Rt : ℂ → ℂ := fun z => ∑ y ∈ S, cf y * ∫ k, κ k * twistedScalarSection p q e (mR (y * (k : GR n) * k1) * aZ X z) ∂ν
    have hRd : DifferentiableOn ℂ Rt U := by
      have h := DifferentiableOn.sum (u := S)
        (A := fun y z => cf y * ∫ k, κ k * twistedScalarSection p q e (mR (y * (k : GR n) * k1) * aZ X z) ∂ν)
        (fun y hy => (hRy y hy).1.const_mul (cf y))
      have heq : (∑ y ∈ S, fun z => cf y * ∫ k, κ k * twistedScalarSection p q e (mR (y * (k : GR n) * k1) * aZ X z) ∂ν) = Rt := by
        ext z
        simp only [Finset.sum_apply]
        rfl
      rwa [heq] at h
    have h0U : (0 : ℂ) ∈ U := by simpa using hUR 0

    have hder : ∀ r : ℕ, iteratedDeriv r Lt 0 = iteratedDeriv r Rt 0 := by
      intro r
      set Q0 : PX m n := (dil c X ^ r) 1
      obtain ⟨Wr, hWrf, hQ0Wr, hWrρ, hWrc⟩ := hL.kfin Q0
      haveI : FiniteDimensional ℂ Wr := hWrf
      have hinK : ∀ k : KR n, InK (mR ((k : GR n) * k1)) := fun k => inK_mul k k1 hk1

      have hcont_l : ∀ l : PX m n →ₗ[ℂ] ℂ, Continuous (fun k : KR n => κ k * l (ρ ((k : GR n) * k1) Q0)) := by
        intro l
        refine hκ.mul ?_
        have h1 := hWrc Q0 hQ0Wr l
        exact h1.comp_continuous (cont_KR_mul' n k1) (fun k => hinK k)
      obtain ⟨Φ, hΦW, hΦ⟩ := TSC.exists_int_elem ν Wr (fun k : KR n => κ k • ρ ((k : GR n) * k1) Q0)
        (fun k => Wr.smul_mem _ (hWrρ _ (hinK k) Q0 hQ0Wr))
        (fun l => by
          have := (hcont_l l).continuousOn.integrableOn_compact (μ := ν) hcomp
          simpa [map_smul, smul_eq_mul] using integrableOn_univ.1 this)

      obtain ⟨Qr, hQrW, hQr⟩ := hπ (fun y' => sL Q0 (y' * k1)) ((hL.cont Q0).comp (continuous_id.mul continuous_const))
        (fun y g hy => by
          show sL Q0 (y * g * k1) = F0 p q e y * sL Q0 (g * k1)
          rw [mul_assoc, hL.law Q0 y (g * k1) hy])
      have hsecΦ : ∀ y', sL Φ y' = sL Qr y' := by
        intro y'
        have h1 := hΦ ((LinearMap.proj y').comp sL)
        simp only [LinearMap.comp_apply, LinearMap.proj_apply, map_smul, Pi.smul_apply, smul_eq_mul] at h1
        rw [h1, ← hQr y']
        refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
        simp only
        rw [← hL.kact Q0 y' _ (hinK k), mul_assoc]
      have hIΦ : I Φ gpt = ∫ k, κ k * I (ρ ((k : GR n) * k1) Q0) gpt ∂ν := by
        have h1 := hΦ ((LinearMap.proj gpt).comp I)
        simpa [map_smul, smul_eq_mul] using h1

      have hL0 : iteratedDeriv r Lt 0 = I Qr gpt := by
        rw [show iteratedDeriv r Lt 0 = ∫ k, iteratedDeriv r (fun z => κ k * Fid ((k : GR n) * k1) z) 0 ∂ν
          from hLr 0 h0U r]
        have e1 : ∀ k : KR n, iteratedDeriv r (fun z => κ k * Fid ((k : GR n) * k1) z) 0 =
            κ k * I (ρ ((k : GR n) * k1) Q0) gpt := by
          intro k
          rw [iteratedDeriv_const_mul_field, (hFid ((k : GR n) * k1)).2.2 r, hG.Ik _ gpt _ (hinK k)]
        simp_rw [e1]
        rw [← hIΦ]
        exact hIsec _ _ hsecΦ

      have hR0 : iteratedDeriv r Rt 0 = I Qr gpt := by
        have hsum := (TSC.iteratedDeriv_sum_on S hUo (fun y z => cf y * ∫ k, κ k * twistedScalarSection p q e (mR (y * (k : GR n) * k1) * aZ X z) ∂ν)
          (fun y hy => (hRy y hy).1.const_mul (cf y)) r).2 h0U
        beta_reduce at hsum
        rw [show Rt = fun w => ∑ y ∈ S, cf y * ∫ k, κ k * twistedScalarSection p q e (mR (y * (k : GR n) * k1) * aZ X w) ∂ν from rfl, hsum]
        have e2 : ∀ y ∈ S, iteratedDeriv r (fun z => cf y * ∫ k, κ k * twistedScalarSection p q e (mR (y * (k : GR n) * k1) * aZ X z) ∂ν) 0 =
            cf y * sL Qr y := by
          intro y hy
          rw [iteratedDeriv_const_mul_field, (hRy y hy).2 0 h0U r, ← hQr y]
          congr 1
          refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
          simp only
          rw [iteratedDeriv_const_mul_field]
          congr 1
          have hreal := (TSA.iteratedDeriv_ofReal' hU2o (hU2d _ (hmemC y hy k)) hU2R
            (h := fun s : ℝ => F0 p q e (y * (k : GR n) * k1 * af s))
            (fun s => by
              rw [spherical_section_eq_extension, mR_mul (y * (k : GR n) * k1) (af s), hdilmat X s (af s) (haf s)]) r).2 0
          simp only [Complex.ofReal_zero] at hreal
          rw [hreal, (hDF m n ε c t p q e sL ρ hL X af haf (y * (k : GR n) * k1) r).2]
        rw [Finset.sum_congr rfl e2]
        rw [← hℓ ⟨sL Qr, ⟨Qr, hQrW, rfl⟩⟩ Qr (fun _ => rfl), hℓeval]
      rw [hL0, hR0]

    have hLd' : DifferentiableOn ℂ Lt U := hLd
    have hval : Lt 1 = Rt 1 := by
      have h := TSA.eq_of_iteratedDeriv (f := Lt) (g := Rt) hUo hUR hLd' hRd hder 1
      simpa using h
    have hLt1 : Lt 1 = ∫ k, κ k * I 1 (gpt * ι ((k : GR n) * (k1 * a))) ∂ν := by
      show ∫ k, κ k * Fid ((k : GR n) * k1) 1 ∂ν = _
      refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
      simp only
      have := (hFid ((k : GR n) * k1)).2.1 1
      simp only [Complex.ofReal_one] at this
      rw [this, ha1, mul_assoc]
    have hRt1 : Rt 1 = I Q' gpt := by
      have e3 : ∀ y ∈ S, cf y * ∫ k, κ k * twistedScalarSection p q e (mR (y * (k : GR n) * k1) * aZ X 1) ∂ν = cf y * sL Q' y := by
        intro y hy
        rw [← hQ' y]
        congr 1
        refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
        simp only
        have hm : aZ X (1 : ℂ) = mR a := by rw [hdilmat X 1 a ha]; simp
        rw [hm, ← mR_mul, ← spherical_section_eq_extension, mul_assoc (y * (k : GR n)) k1 a]
      show ∑ y ∈ S, cf y * ∫ k, κ k * twistedScalarSection p q e (mR (y * (k : GR n) * k1) * aZ X 1) ∂ν = I Q' gpt
      rw [Finset.sum_congr rfl e3, ← hℓeval ⟨sL Q', ⟨Q', hQ'W, rfl⟩⟩]
      exact hℓ _ Q' (fun _ => rfl)
    rw [← hLt1, hval, hRt1]

  have hQ' : ∀ y', ∫ k, κ k * F0 p q e (y' * (k : GR n) * (k1 * a)) ∂ν = sL ((F0 p q e k2)⁻¹ • Q) y' := by
    intro y'
    rw [map_smul, Pi.smul_apply, smul_eq_mul, ← hQ y', ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only
    rw [show y' * (k : GR n) * (k1 * a * k2) = y' * (k : GR n) * (k1 * a) * k2 by group,
      ((hM n p q e).1 _ k2 hk2).1]
    field_simp
  have hkey := key _ (W.smul_mem _ hQW) hQ'
  have hIk2 : ∀ k : KR n, I 1 (gpt * ι ((k : GR n) * (k1 * a * k2))) =
      F0 p q e k2 * I 1 (gpt * ι ((k : GR n) * (k1 * a))) := by
    intro k
    rw [show (k : GR n) * (k1 * a * k2) = (k : GR n) * (k1 * a) * k2 by group, map_mul, ← mul_assoc,
      hG.Ik 1 _ k2 hk2, hL.kvac k2 hk2, map_smul, Pi.smul_apply, smul_eq_mul]
  calc ∫ k, κ k * I 1 (gpt * ι ((k : GR n) * (k1 * a * k2))) ∂ν
      = ∫ k, F0 p q e k2 * (κ k * I 1 (gpt * ι ((k : GR n) * (k1 * a)))) ∂ν := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
        simp only; rw [hIk2 k]; ring
    _ = F0 p q e k2 * I ((F0 p q e k2)⁻¹ • Q) gpt := by rw [integral_const_mul, hkey]
    _ = I Q gpt := by
        rw [map_smul, Pi.smul_apply, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hF2, one_mul]

end PositivityTheory.Rg.Sw.AbsSt
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.DifferentiableSecondCayleyBlockDilation
noncomputable section

open Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

theorem tsb_mR_cont (n : ℕ) : Continuous (mR : GR n → M2 n) :=
  Units.continuous_val.comp continuous_subtype_val

theorem continuous_lower_left_block_alt (n : ℕ) : Continuous (fun M : M2 n => M.toBlocks₂₁) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Matrix.toBlocks₂₁, Matrix.of_apply]
  exact (continuous_apply _).comp (continuous_apply _)

theorem continuous_lower_right_block_alt (n : ℕ) : Continuous (fun M : M2 n => M.toBlocks₂₂) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Matrix.toBlocks₂₂, Matrix.of_apply]
  exact (continuous_apply _).comp (continuous_apply _)

theorem continuous_first_cayley_block (n : ℕ) : Continuous (fun M : M2 n => u1 M) := by
  unfold u1
  exact ((continuous_lower_left_block_alt n).const_smul Complex.I).add (continuous_lower_right_block_alt n)

theorem continuous_second_cayley_block (n : ℕ) : Continuous (fun M : M2 n => u2 M) := by
  unfold u2
  exact (((continuous_lower_left_block_alt n).const_smul Complex.I).neg).add (continuous_lower_right_block_alt n)

theorem continuousAt_twisted_section {n : ℕ} (p q : ℕ) (e : ℤ) (M : M2 n) (h0 : M.det ≠ 0) (h1 : (u1 M).det ≠ 0)
    (h2 : (u2 M).det ≠ 0) : ContinuousAt (twistedScalarSection p q e) M := by
  unfold twistedScalarSection f0
  refine ContinuousAt.mul (ContinuousAt.zpow₀ (continuous_id.matrix_det).continuousAt e (Or.inl h0))
    (ContinuousAt.mul ?_ ?_)
  · exact ContinuousAt.zpow₀ ((continuous_first_cayley_block n).matrix_det).continuousAt _ (Or.inl h1)
  · exact ContinuousAt.zpow₀ ((continuous_second_cayley_block n).matrix_det).continuousAt _ (Or.inl h2)

theorem tsb_det_ne (n : ℕ) (g : GR n) : (mR g).det ≠ 0 := by
  have h := g.1.isUnit
  exact (Matrix.isUnit_iff_isUnit_det _).mp h |>.ne_zero

theorem continuous_spherical_section (hD : CayleyBlocksInvertible) (n p q : ℕ) (e : ℤ) : Continuous (F0 p q e : GR n → ℂ) := by
  refine continuous_iff_continuousAt.2 fun g => ?_
  have : (F0 p q e : GR n → ℂ) = twistedScalarSection p q e ∘ mR := rfl
  rw [this]
  exact (continuousAt_twisted_section p q e (mR g) (tsb_det_ne n g) (hD n g).1 (hD n g).2).comp (tsb_mR_cont n).continuousAt

def kSet (n : ℕ) : Set (M2 n) := (Matrix.unitaryGroup (Fin n ⊕ Fin n) ℂ : Set (M2 n)) ∩ {M | InG M}

theorem tsb_kSet_compact (n : ℕ) : IsCompact (kSet n) := by
  have hK : IsCompact (Set.pi Set.univ fun _ : Fin n ⊕ Fin n => Set.pi Set.univ fun _ : Fin n ⊕ Fin n =>
      Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  refine IsCompact.of_isClosed_subset hK (IsClosed.inter isClosed_unitary ?_) ?_
  · exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
      continuous_const
  · intro U hU
    exact Set.mem_univ_pi.2 fun i => Set.mem_univ_pi.2 fun j =>
      mem_closedBall_zero_iff.2 (entry_norm_bound_of_unitary hU.1 i j)

theorem tsb_kSet_mem {n : ℕ} {M : M2 n} (h : M ∈ kSet n) : Mᴴ * M = 1 ∧ M * Mᴴ = 1 ∧ InG M := by
  have hu : M ∈ Matrix.unitaryGroup (Fin n ⊕ Fin n) ℂ := h.1
  have h1 := (Matrix.mem_unitaryGroup_iff').1 hu
  have h2 := (Matrix.mem_unitaryGroup_iff).1 hu
  exact ⟨by simpa [Matrix.star_eq_conjTranspose] using h1, by simpa [Matrix.star_eq_conjTranspose] using h2, h.2⟩

def kOf (n : ℕ) (M : kSet n) : KR n :=
  ⟨⟨⟨M.1, M.1ᴴ, (tsb_kSet_mem M.2).2.1, (tsb_kSet_mem M.2).1⟩, (tsb_kSet_mem M.2).2.2⟩,
    ⟨(tsb_kSet_mem M.2).2.2, (tsb_kSet_mem M.2).1⟩⟩

theorem tsb_kOf_cont (n : ℕ) : Continuous (kOf n) := by
  refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
  refine Units.continuous_iff.2 ⟨continuous_subtype_val, ?_⟩
  exact continuous_subtype_val.matrix_conjTranspose

theorem tsb_kOf_surj (n : ℕ) : Function.Surjective (kOf n) := by
  intro k
  have hk := k.2
  have hM : mR (k : GR n) ∈ kSet n := by
    refine ⟨?_, hk.1⟩
    show mR (k : GR n) ∈ Matrix.unitaryGroup (Fin n ⊕ Fin n) ℂ
    rw [Matrix.mem_unitaryGroup_iff']
    simpa [Matrix.star_eq_conjTranspose] using hk.2
  refine ⟨⟨mR (k : GR n), hM⟩, ?_⟩
  apply Subtype.ext; apply Subtype.ext; apply Units.ext
  rfl

theorem tsb_compact (n : ℕ) : CompactSpace (KR n) := by
  have : CompactSpace (kSet n) := isCompact_iff_compactSpace.mp (tsb_kSet_compact n)
  exact ⟨by rw [← (tsb_kOf_surj n).range_eq]; exact isCompact_range (tsb_kOf_cont n)⟩

def dM {n : ℕ} (X : Fin n → ℝ) (t : ℝ) : M2 n :=
  fromBlocks (diagonal fun j => (Real.exp (t * X j) : ℂ)) 0 0 (diagonal fun j => (Real.exp (-(t * X j)) : ℂ))

theorem exp_diagonal_mul_inverse {n : ℕ} (X : Fin n → ℝ) (t : ℝ) :
    (diagonal fun j => (Real.exp (t * X j) : ℂ)) * (diagonal fun j => (Real.exp (-(t * X j)) : ℂ)) = 1 ∧
    (diagonal fun j => (Real.exp (-(t * X j)) : ℂ)) * (diagonal fun j => (Real.exp (t * X j) : ℂ)) = 1 := by
  constructor <;>
  · rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext j
    rw [← Complex.ofReal_mul, ← Real.exp_add]; simp

theorem tsb_dM_mul {n : ℕ} (X : Fin n → ℝ) (t : ℝ) : dM X t * dM X (-t) = 1 := by
  unfold dM
  rw [fromBlocks_multiply]
  have h := exp_diagonal_mul_inverse X t
  have e1 : (fun j => (Real.exp (-t * X j) : ℂ)) = fun j => (Real.exp (-(t * X j)) : ℂ) := by
    funext j; rw [neg_mul]
  have e2 : (fun j => (Real.exp (-(-t * X j)) : ℂ)) = fun j => (Real.exp (t * X j) : ℂ) := by
    funext j; rw [neg_mul, neg_neg]
  rw [e1, e2]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, h.1, h.2, fromBlocks_one]

theorem tsb_dM_star {n : ℕ} (X : Fin n → ℝ) (t : ℝ) : (dM X t)ᴴ = dM X t := by
  unfold dM
  rw [fromBlocks_conjTranspose, diagonal_conjTranspose, diagonal_conjTranspose, conjTranspose_zero]
  congr 2 <;> (funext j; simp only [Pi.star_apply, RCLike.star_def, Complex.conj_ofReal])

theorem tsb_dM_inG {n : ℕ} (X : Fin n → ℝ) (t : ℝ) : InG (dM X t) := by
  unfold InG
  rw [tsb_dM_star]
  unfold dM JJ
  have h := exp_diagonal_mul_inverse X t
  rw [fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul,
    Matrix.one_mul, h.1, h.2, neg_zero]

theorem tsb_dil_exists (n : ℕ) (X : Fin n → ℝ) (t : ℝ) : ∃ a : GR n, IsDil X t a := by
  have h1 := tsb_dM_mul X t
  have h2 : dM X (-t) * dM X t = 1 := by simpa using tsb_dM_mul X (-t)
  exact ⟨⟨⟨dM X t, dM X (-t), h1, h2⟩, tsb_dM_inG X t⟩, rfl⟩

theorem tsb_dil_aZ {n : ℕ} (X : Fin n → ℝ) (t : ℝ) (a : GR n) (h : IsDil X t a) : mR a = aZ X t := by
  rw [h]
  unfold aZ
  congr 2 <;> (funext j; push_cast [Complex.ofReal_exp]; ring_nf)

theorem tsb_aZ_entry {n : ℕ} (X : Fin n → ℝ) (i j : Fin n ⊕ Fin n) :
    (∀ z, aZ X z i j = match i, j with
      | Sum.inl a, Sum.inl b => if a = b then Complex.exp (z * X a) else 0
      | Sum.inr a, Sum.inr b => if a = b then Complex.exp (-(z * X a)) else 0
      | _, _ => 0) := by
  intro z
  rcases i with a | a <;> rcases j with b | b <;> simp [aZ, diagonal_apply]

theorem tsb_aZ_diff {n : ℕ} (X : Fin n → ℝ) (i j : Fin n ⊕ Fin n) : Differentiable ℂ (fun z => aZ X z i j) := by
  have h := tsb_aZ_entry X i j
  simp_rw [h]
  rcases i with a | a <;> rcases j with b | b <;> simp only
  · split_ifs
    · fun_prop
    · exact differentiable_const _
  · exact differentiable_const _
  · exact differentiable_const _
  · split_ifs
    · exact (Complex.differentiable_exp.comp ((differentiable_id.mul (differentiable_const _)).neg))
    · exact differentiable_const _

theorem tsb_aZ_cont {n : ℕ} (X : Fin n → ℝ) : Continuous (fun z => aZ X z) :=
  continuous_pi fun i => continuous_pi fun j => (tsb_aZ_diff X i j).continuous

theorem tsb_det_diffAt {ι : Type} [Fintype ι] [DecidableEq ι] {A : ℂ → Matrix ι ι ℂ} {z : ℂ}
    (h : ∀ i j, DifferentiableAt ℂ (fun w => A w i j) z) : DifferentiableAt ℂ (fun w => (A w).det) z := by
  simp only [Matrix.det_apply]
  refine DifferentiableAt.fun_sum fun σ _ => ?_
  simp only [Units.smul_def, zsmul_eq_mul]
  exact (differentiableAt_const _).mul (DifferentiableAt.fun_finsetProd fun i _ => h _ _)

theorem tsb_mul_diff {n : ℕ} (X : Fin n → ℝ) (M : M2 n) (i j : Fin n ⊕ Fin n) :
    Differentiable ℂ (fun z => (M * aZ X z) i j) := by
  simp only [Matrix.mul_apply]
  exact Differentiable.fun_sum fun k _ => (differentiable_const _).mul (tsb_aZ_diff X k j)

theorem differentiable_first_cayley_block_dilation {n : ℕ} (X : Fin n → ℝ) (M : M2 n) (i j : Fin n) :
    Differentiable ℂ (fun z => u1 (M * aZ X z) i j) := by
  simp only [u1, Matrix.add_apply, Matrix.smul_apply, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.of_apply, smul_eq_mul]
  exact ((differentiable_const _).mul (tsb_mul_diff X M _ _)).add (tsb_mul_diff X M _ _)

theorem differentiable_second_cayley_block_dilation {n : ℕ} (X : Fin n → ℝ) (M : M2 n) (i j : Fin n) :
    Differentiable ℂ (fun z => u2 (M * aZ X z) i j) := by
  simp only [u2, Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂,
    Matrix.of_apply, smul_eq_mul]
  exact (((differentiable_const _).mul (tsb_mul_diff X M _ _)).neg).add (tsb_mul_diff X M _ _)

theorem tsb_det_aZ_ne {n : ℕ} (X : Fin n → ℝ) (z : ℂ) : (aZ X z).det ≠ 0 := by
  unfold aZ
  rw [det_fromBlocks_zero₂₁, det_diagonal, det_diagonal]
  exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun _ _ => Complex.exp_ne_zero _)
    (Finset.prod_ne_zero_iff.2 fun _ _ => Complex.exp_ne_zero _)

theorem tsbFacts : TSBFacts := by
  intro hD n p q e
  refine ⟨tsb_compact n, tsb_mR_cont n, continuous_spherical_section hD n p q e, tsb_dil_exists n, tsb_dil_aZ, ?_⟩
  intro X C hC
  set Φ : GR n × ℂ → M2 n := fun yz => mR yz.1 * aZ X yz.2 with hΦ
  have hΦc : Continuous Φ := ((tsb_mR_cont n).comp continuous_fst).matrix_mul ((tsb_aZ_cont X).comp continuous_snd)
  set O : Set (GR n × ℂ) := {yz | (u1 (Φ yz)).det ≠ 0 ∧ (u2 (Φ yz)).det ≠ 0} with hO
  have hOo : IsOpen O := by
    change IsOpen ({yz : GR n × ℂ | (u1 (Φ yz)).det ≠ 0} ∩
      {yz : GR n × ℂ | (u2 (Φ yz)).det ≠ 0})
    refine IsOpen.inter ?_ ?_
    · exact isOpen_ne_fun (((continuous_first_cayley_block n).comp hΦc).matrix_det) continuous_const
    · exact isOpen_ne_fun (((continuous_second_cayley_block n).comp hΦc).matrix_det) continuous_const
  have hreal : ∀ (y : GR n) (t : ℝ), (y, (t : ℂ)) ∈ O := by
    intro y t
    obtain ⟨a, ha⟩ := tsb_dil_exists n X t
    have : Φ (y, (t : ℂ)) = mR (y * a) := by
      simp only [hΦ]; rw [← tsb_dil_aZ X t a ha]; rfl
    simp only [hO, Set.mem_setOf_eq, this]
    exact hD n (y * a)
  have tube : ∀ t : ℝ, ∃ v : Set ℂ, IsOpen v ∧ (t : ℂ) ∈ v ∧ C ×ˢ v ⊆ O := by
    intro t
    obtain ⟨u, v, -, hv, hCu, htv, huv⟩ := generalized_tube_lemma hC (isCompact_singleton (x := (t : ℂ))) hOo
      (by rintro ⟨y, z⟩ ⟨-, hz⟩; simp only [Set.mem_singleton_iff] at hz; subst hz; exact hreal y t)
    exact ⟨v, hv, htv rfl, fun yz hyz => huv ⟨hCu hyz.1, hyz.2⟩⟩
  choose v hvo hvt hvC using tube
  refine ⟨⋃ t, v t, isOpen_iUnion hvo, fun t => Set.mem_iUnion.2 ⟨t, hvt t⟩, ?_, ?_⟩
  · intro yz hyz
    obtain ⟨hy, hz⟩ := hyz
    obtain ⟨t, ht⟩ := Set.mem_iUnion.1 hz
    have hmem : yz ∈ O := hvC t ⟨hy, ht⟩
    have h0 : (Φ yz).det ≠ 0 := by
      simp only [hΦ]; rw [det_mul]; exact mul_ne_zero (tsb_det_ne n _) (tsb_det_aZ_ne X _)
    exact ((continuousAt_twisted_section p q e (Φ yz) h0 hmem.1 hmem.2).comp hΦc.continuousAt).continuousWithinAt
  · intro y hy z hz
    obtain ⟨t, ht⟩ := Set.mem_iUnion.1 hz
    have hmem : (y, z) ∈ O := hvC t (Set.mk_mem_prod hy ht)
    have h0 : (mR y * aZ X z).det ≠ 0 := by
      rw [det_mul]; exact mul_ne_zero (tsb_det_ne n _) (tsb_det_aZ_ne X _)
    refine DifferentiableAt.differentiableWithinAt ?_
    unfold twistedScalarSection f0
    refine DifferentiableAt.mul ?_ (DifferentiableAt.mul ?_ ?_)
    · exact (tsb_det_diffAt fun i j => (tsb_mul_diff X (mR y) i j).differentiableAt).zpow (Or.inl h0)
    · exact (tsb_det_diffAt fun i j => (differentiable_first_cayley_block_dilation X (mR y) i j).differentiableAt).zpow (Or.inl hmem.1)
    · exact (tsb_det_diffAt fun i j => (differentiable_second_cayley_block_dilation X (mR y) i j).differentiableAt).zpow (Or.inl hmem.2)

end PositivityTheory.Rg.Sw.AbsSt
end
end

namespace PositivityTheory.Rg.Sw.AbsSt

theorem tsGen : Iwa → CayleyBlocksInvertible → KAK → Mult → SecZero → DerivativeVacuumDilations → HolParam → LC → TSGen :=
  fun _ hD hK hM hS hDF hH hLC => tsGen_of hD hK hM hS hDF hH hLC tsbFacts

end PositivityTheory.Rg.Sw.AbsSt
