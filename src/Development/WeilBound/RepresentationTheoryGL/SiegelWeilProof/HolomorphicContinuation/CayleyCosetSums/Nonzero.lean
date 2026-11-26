module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.MapsToUpToSign
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.MatInv

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.IsCompactKSet
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.ConvPhi
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.GRHaar
noncomputable section

open MeasureTheory Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.HSt.GRH

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

theorem continuous_mR : Continuous (mR : GR n → M2 n) :=
  Units.continuous_val.comp continuous_subtype_val

instance m2LC (n : ℕ) : LocallyCompactSpace (M2 n) :=
  inferInstanceAs (LocallyCompactSpace (Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℂ))

instance secondCountableBlockMatrices (n : ℕ) : SecondCountableTopology (M2 n) :=
  inferInstanceAs (SecondCountableTopology (Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℂ))

theorem JJ_mul_self : JJ n * JJ n = -1 := by
  rw [JJ, fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul, add_zero, zero_add, neg_zero]
  rw [← fromBlocks_one, fromBlocks_neg, neg_zero]

theorem isClosed_inG : IsClosed {x : M2 n | InG x} :=
  isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id) continuous_const

theorem inv_left {x : M2 n} (hx : InG x) : (-(JJ n * xᴴ * JJ n)) * x = 1 := by
  unfold InG at hx
  have h : JJ n * xᴴ * JJ n * x = JJ n * (xᴴ * JJ n * x) := by
    simp only [Matrix.mul_assoc]
  rw [Matrix.neg_mul, h, hx, JJ_mul_self, neg_neg]

def toSet : GR n ≃ₜ {x : M2 n | InG x} where
  toFun g := ⟨mR g, g.2⟩
  invFun x := ⟨⟨x.1, -(JJ n * x.1ᴴ * JJ n), mul_eq_one_comm.mp (inv_left x.2), inv_left x.2⟩, x.2⟩
  left_inv g := by
    apply Subtype.ext
    apply Units.ext
    rfl
  right_inv x := rfl
  continuous_toFun := continuous_mR.subtype_mk _
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    refine Units.continuous_iff.2 ⟨continuous_subtype_val, ?_⟩
    exact ((continuous_const.matrix_mul (continuous_subtype_val.matrix_conjTranspose)).matrix_mul continuous_const).neg

theorem isClosedEmbedding_mR : Topology.IsClosedEmbedding (mR : GR n → M2 n) :=
  (isClosed_inG.isClosedEmbedding_subtypeVal).comp toSet.isClosedEmbedding

theorem isCompact_preimage_mR {C : Set (M2 n)} (hC : IsCompact C) : IsCompact ((mR : GR n → M2 n) ⁻¹' C) :=
  isClosedEmbedding_mR.isCompact_preimage hC

instance : LocallyCompactSpace (GR n) := isClosedEmbedding_mR.locallyCompactSpace

instance : MeasurableSpace (GR n) := borel _

instance : BorelSpace (GR n) := ⟨rfl⟩

instance : SecondCountableTopology (GR n) := isClosedEmbedding_mR.isEmbedding.secondCountableTopology

end PositivityTheory.Rg.Sw.HSt.GRH
end
end

noncomputable section

open MeasureTheory Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.HSt.Conv

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.HSt.GRH

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

instance krCpt (n : ℕ) : CompactSpace (KR n) := kRCpt n

def phi (m : ℕ) (e : ℤ) (w : ℂ) (u : GR n) : ℂ := F0 m 0 e u * ((hLoc u : ℝ) : ℂ) ^ w

def tw (m : ℕ) (e : ℤ) (μK : Measure (KR n)) (β : M2 n → ℝ) (X : M2 n) : ℂ :=
  ∫ k : KR n, (F0 m 0 e (k : GR n))⁻¹ * (β ((mR (k : GR n))ᴴ * X) : ℂ) ∂μK

def cw (m : ℕ) (e : ℤ) (ν : Measure (GR n)) (μK : Measure (KR n)) (β : M2 n → ℝ) (w : ℂ) : ℂ :=
  ∫ u : GR n, phi m e w u * tw m e μK β (mR u) ∂ν

theorem mR_mul (g h : GR n) : mR (g * h) = mR g * mR h := rfl

theorem tw_left (m : ℕ) (e : ℤ) (μK : Measure (KR n)) [μK.IsMulLeftInvariant] (β : M2 n → ℝ) (k₀ : KR n) (X : M2 n) :
    tw m e μK β (mR (k₀ : GR n) * X) = (F0 m 0 e (k₀ : GR n))⁻¹ * tw m e μK β X := by
  have h := integral_mul_left_eq_self (μ := μK)
    (fun k : KR n => (F0 m 0 e (k : GR n))⁻¹ * (β ((mR (k : GR n))ᴴ * (mR (k₀ : GR n) * X)) : ℂ)) k₀
  rw [tw, ← h, tw, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun k => ?_)
  have hk0 : (mR (k₀ : GR n))ᴴ * mR (k₀ : GR n) = 1 := k₀.2.2
  have hmul := ((mult n m 0 e).1 (k₀ : GR n) (k : GR n) k.2).1
  simp only [Subgroup.coe_mul, mR_mul]
  rw [hmul, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (mR (k₀ : GR n))ᴴ, hk0, Matrix.one_mul,
    mul_inv]
  ring

theorem conv_phi (m : ℕ) (e : ℤ) (ν : Measure (GR n)) [ν.IsMulLeftInvariant] (μK : Measure (KR n)) [μK.IsMulLeftInvariant]
    (β : M2 n → ℝ) (w : ℂ) (y : GR n) :
    ∫ u : GR n, phi m e w (y * u) * tw m e μK β (mR u) ∂ν = cw m e ν μK β w * phi m e w y := by
  obtain ⟨p, k, hp, hk, rfl⟩ := iwa n y
  have hnn : ∀ g : GR n, 0 ≤ hLoc g := fun g => by unfold hLoc; positivity
  have hphi : ∀ g : GR n, phi m e w (p * g) = phi m e w p * phi m e w g := by
    intro g
    obtain ⟨h1, h2⟩ := (mult n m 0 e).2 p g hp
    simp only [phi, h1, h2, Complex.ofReal_mul]
    rw [Complex.mul_cpow_ofReal_nonneg (hnn p) (hnn g)]
    ring
  have hK : phi m e w (p * k) = phi m e w p * F0 m 0 e k := by
    obtain ⟨h1, h2⟩ := (mult n m 0 e).1 p k hk
    simp only [phi, h1, h2]
    ring
  have hone : F0 m 0 e (1 : GR n) = 1 := by
    have h1 : toBlocks₂₁ (1 : M2 n) = 0 := by
      ext i j; simp [Matrix.toBlocks₂₁, Matrix.one_apply]
    have h2 : toBlocks₂₂ (1 : M2 n) = 1 := by
      ext i j; simp [Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.one_apply]
    simp [F0, mR, f0, u1, u2, h1, h2]
  have hF : F0 m 0 e k * F0 m 0 e k⁻¹ = 1 := by
    rw [← ((mult n m 0 e).1 k k⁻¹ (inv_mem hk)).1, mul_inv_cancel, hone]
  have htw : ∀ u : GR n, tw m e μK β (mR (k⁻¹ * u)) = F0 m 0 e k * tw m e μK β (mR u) := by
    intro u
    rw [mR_mul]
    have h := tw_left m e μK β (⟨k⁻¹, inv_mem hk⟩ : KR n) (mR u)
    simp only at h
    rw [h, inv_eq_of_mul_eq_one_left hF]
  calc ∫ u : GR n, phi m e w (p * k * u) * tw m e μK β (mR u) ∂ν
      = ∫ u : GR n, phi m e w (p * k * (k⁻¹ * u)) * tw m e μK β (mR (k⁻¹ * u)) ∂ν :=
        (integral_mul_left_eq_self (fun u => phi m e w (p * k * u) * tw m e μK β (mR u)) k⁻¹).symm
    _ = ∫ u : GR n, (F0 m 0 e k * phi m e w p) * (phi m e w u * tw m e μK β (mR u)) ∂ν := by
        congr 1
        funext u
        rw [show p * k * (k⁻¹ * u) = p * u by group, hphi, htw]
        ring
    _ = cw m e ν μK β w * phi m e w (p * k) := by
        rw [integral_const_mul, hK]
        unfold cw
        ring

end PositivityTheory.Rg.Sw.HSt.Conv
end
end

noncomputable section

open MeasureTheory Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.HSt.Conv

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.HSt.GRH

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem continuous_kR : Continuous (fun k : KR n => mR (k : GR n)) := continuous_mR.comp continuous_subtype_val

def kSet (S : Set (M2 n)) : Set (M2 n) := (fun p : KR n × M2 n => mR (p.1 : GR n) * p.2) '' (univ ×ˢ S)

theorem isCompact_kSet {S : Set (M2 n)} (hS : IsCompact S) : IsCompact (kSet S) :=
  (isCompact_univ.prod hS).image ((continuous_kR.comp continuous_fst).mul continuous_snd)

theorem tw_eq_zero (m : ℕ) (e : ℤ) (μK : Measure (KR n)) (β : M2 n → ℝ) {X : M2 n} (hX : X ∉ kSet (tsupport β)) :
    tw m e μK β X = 0 := by
  unfold tw
  have hz : ∀ k : KR n, β ((mR (k : GR n))ᴴ * X) = 0 := by
    intro k
    by_contra h
    apply hX
    have hk : InK (mR (k : GR n)) := k.2
    have hkk : mR (k : GR n) * (mR (k : GR n))ᴴ = 1 := mul_eq_one_comm.mp hk.2
    refine ⟨(k, (mR (k : GR n))ᴴ * X), ⟨mem_univ _, subset_tsupport _ h⟩, ?_⟩
    simp only
    rw [← Matrix.mul_assoc, hkk, Matrix.one_mul]
  simp [hz]

theorem tw_support (m : ℕ) (e : ℤ) (μK : Measure (KR n)) {β : M2 n → ℝ} (hβ : HasCompactSupport β) :
    HasCompactSupport (tw m e μK β) := by
  refine HasCompactSupport.intro (isCompact_kSet hβ) fun X hX => tw_eq_zero m e μK β hX

end PositivityTheory.Rg.Sw.HSt.Conv
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Nonzero
noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt.Conv

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.HSt.GRH

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def psi (m : ℕ) (e : ℤ) (μK : Measure (KR n)) (u : GR n) : ℂ :=
  ∫ k : KR n, (F0 m 0 e (k : GR n))⁻¹ * F0 m 0 e ((k : GR n) * u) ∂μK

theorem psi_continuous (m : ℕ) (e : ℤ) (μK : Measure (KR n)) [IsFiniteMeasure μK] : Continuous (psi m e μK) := by
  have hF : Continuous (Function.uncurry fun (u : GR n) (k : KR n) =>
      (F0 m 0 e (k : GR n))⁻¹ * F0 m 0 e ((k : GR n) * u)) := by
    show Continuous fun p : GR n × KR n => (F0 m 0 e (p.2 : GR n))⁻¹ * F0 m 0 e ((p.2 : GR n) * p.1)
    refine Continuous.mul ?_ ?_
    · exact ((Vac.continuous_weight_factor detU1 m 0 e).comp (continuous_subtype_val.comp continuous_snd)).inv₀
        fun p => Vac.spherical_section_ne_zero detU1 m 0 e _
    · exact (Vac.continuous_weight_factor detU1 m 0 e).comp ((continuous_subtype_val.comp continuous_snd).mul continuous_fst)
  have := continuous_parametric_integral_of_continuous (μ := μK) hF isCompact_univ
  have e : psi m e μK = fun u => ∫ k : KR n, (F0 m 0 e (k : GR n))⁻¹ * F0 m 0 e ((k : GR n) * u) ∂μK := rfl
  rw [e]
  simpa [Measure.restrict_univ] using this

theorem psi_one (m : ℕ) (e : ℤ) (μK : Measure (KR n)) : psi m e μK 1 = (μK Set.univ).toReal := by
  unfold psi
  simp only [mul_one]
  have h : ∀ k : KR n, (F0 m 0 e (k : GR n))⁻¹ * F0 m 0 e (k : GR n) = 1 := fun k =>
    inv_mul_cancel₀ (Vac.spherical_section_ne_zero detU1 _ _ _ _)
  simp only [h]
  rw [integral_const]
  simp [Measure.real]

private theorem mR_conjTranspose_eq_mR_inv_of_KR (k : KR n) : (mR (k : GR n))ᴴ = mR ((k : GR n)⁻¹) := by
  have hk : (mR (k : GR n))ᴴ * mR (k : GR n) = 1 := (show InK (mR (k : GR n)) from k.2).2
  have h1 : mR (k : GR n) * mR ((k : GR n)⁻¹) = 1 := by
    rw [← mR_mul, mul_inv_cancel]
    simp [mR]
  calc (mR (k : GR n))ᴴ = (mR (k : GR n))ᴴ * (mR (k : GR n) * mR ((k : GR n)⁻¹)) := by
        rw [h1, Matrix.mul_one]
    _ = mR ((k : GR n)⁻¹) := by rw [← Matrix.mul_assoc, hk, Matrix.one_mul]

theorem cw_zero (m : ℕ) (e : ℤ) (ν : Measure (GR n)) [ν.IsHaarMeasure] (μK : Measure (KR n)) [μK.IsHaarMeasure]
    {β : M2 n → ℝ} (hβc : Continuous β) (hβs : HasCompactSupport β) :
    cw m e ν μK β 0 = ∫ u : GR n, (β (mR u) : ℂ) * psi m e μK u ∂ν := by
  have hF := Vac.continuous_weight_factor (n := n) detU1 m 0 e
  have hFne : ∀ g, F0 (n := n) m 0 e g ≠ 0 := fun g => Vac.spherical_section_ne_zero detU1 m 0 e g
  have hCc : IsCompact (mR ⁻¹' (tsupport β)) := isCompact_preimage_mR hβs.isCompact
  have hk : Continuous (fun p : GR n × KR n => ((p.2 : GR n))) :=
    continuous_subtype_val.comp continuous_snd
  let A : GR n × KR n → ℂ := fun p =>
    F0 m 0 e p.1 * ((F0 m 0 e (p.2 : GR n))⁻¹ * (β (mR ((p.2 : GR n)⁻¹ * p.1)) : ℂ))
  let B : GR n × KR n → ℂ := fun p =>
    (β (mR p.1) : ℂ) * ((F0 m 0 e (p.2 : GR n))⁻¹ * F0 m 0 e ((p.2 : GR n) * p.1))
  have hAc : Continuous A := by
    refine (hF.comp continuous_fst).mul (((hF.comp hk).inv₀ fun p => hFne _).mul ?_)
    exact Complex.continuous_ofReal.comp
      (hβc.comp (continuous_mR.comp (hk.inv.mul continuous_fst)))
  have hBc : Continuous B := by
    refine (Complex.continuous_ofReal.comp (hβc.comp (continuous_mR.comp continuous_fst))).mul
      (((hF.comp hk).inv₀ fun p => hFne _).mul (hF.comp (hk.mul continuous_fst)))
  have hAs : HasCompactSupport A := by
    refine HasCompactSupport.intro
      ((((isCompact_univ (X := KR n)).prod hCc).image
        ((continuous_subtype_val.comp continuous_fst).mul continuous_snd)).prod
        (isCompact_univ (X := KR n))) ?_
    intro p hp
    have hz : β (mR ((p.2 : GR n)⁻¹ * p.1)) = 0 := by
      by_contra hne
      apply hp
      refine ⟨⟨⟨p.2, (p.2 : GR n)⁻¹ * p.1⟩, ⟨Set.mem_univ _, subset_tsupport _ hne⟩, ?_⟩, Set.mem_univ _⟩
      simp
    simp [A, hz]
  have hBs : HasCompactSupport B := by
    refine HasCompactSupport.intro (hCc.prod (isCompact_univ (X := KR n))) ?_
    intro p hp
    have hz : β (mR p.1) = 0 := by
      by_contra hne
      exact hp ⟨subset_tsupport _ hne, Set.mem_univ _⟩
    simp [B, hz]
  have hAi : Integrable A (ν.prod μK) := hAc.integrable_of_hasCompactSupport hAs
  have hBi : Integrable B (ν.prod μK) := hBc.integrable_of_hasCompactSupport hBs
  calc cw m e ν μK β 0 = ∫ u, ∫ k, A (u, k) ∂μK ∂ν := by
        unfold cw
        congr 1
        ext u
        unfold phi tw
        rw [Complex.cpow_zero, mul_one, ← integral_const_mul]
        congr 1
        ext k
        simp only [A]
        rw [mR_conjTranspose_eq_mR_inv_of_KR, ← mR_mul]
    _ = ∫ k, ∫ u, A (u, k) ∂ν ∂μK := integral_integral_swap hAi
    _ = ∫ k, ∫ v, A ((k : GR n) * v, k) ∂ν ∂μK := by
        congr 1
        ext k
        exact (integral_mul_left_eq_self (fun u => A (u, k)) (k : GR n)).symm
    _ = ∫ k, ∫ v, B (v, k) ∂ν ∂μK := by
        congr 1
        ext k
        congr 1
        ext v
        simp only [A, B]
        rw [inv_mul_cancel_left]
        ring
    _ = ∫ v, ∫ k, B (v, k) ∂μK ∂ν := (integral_integral_swap hBi).symm
    _ = ∫ u : GR n, (β (mR u) : ℂ) * psi m e μK u ∂ν := by
        congr 1
        ext v
        simp only [B, psi]
        rw [integral_const_mul]

theorem exists_bump (m : ℕ) (e : ℤ) (ν : Measure (GR n)) [ν.IsHaarMeasure] (μK : Measure (KR n)) [μK.IsHaarMeasure] :
    ∃ β : M2 n → ℝ, ContDiff ℝ ∞ β ∧ HasCompactSupport β ∧ cw m e ν μK β 0 ≠ 0 := by
  have hpc : Continuous (psi m e μK) := psi_continuous m e μK
  have h1 : mR (1 : GR n) = 1 := by simp [mR]
  have hp1 : 0 < (psi m e μK 1).re := by
    rw [psi_one, Complex.ofReal_re]
    exact ENNReal.toReal_pos (isOpen_univ.measure_ne_zero μK Set.univ_nonempty) (measure_ne_top _ _)
  have hO : IsOpen {u : GR n | 0 < (psi m e μK u).re} :=
    isOpen_lt continuous_const (Complex.continuous_re.comp hpc)
  obtain ⟨O, hOo, hOeq⟩ := isClosedEmbedding_mR.isInducing.isOpen_iff.mp hO
  have h1O : (1 : M2 n) ∈ O := by
    have h : (1 : GR n) ∈ mR ⁻¹' O := by
      rw [hOeq]
      exact hp1
    simpa [h1] using h
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hOo 1 h1O
  let b : ContDiffBump (1 : M2 n) := ⟨r / 2, r, by positivity, by linarith⟩
  refine ⟨⇑b, b.contDiff, b.hasCompactSupport, ?_⟩
  rw [cw_zero m e ν μK b.continuous b.hasCompactSupport]
  set g : GR n → ℂ := fun u => (b (mR u) : ℂ) * psi m e μK u with hg
  have hgs : HasCompactSupport g := by
    have h := (b.hasCompactSupport.comp_isClosedEmbedding isClosedEmbedding_mR).comp_left
      (g := Complex.ofReal) Complex.ofReal_zero
    exact h.mul_right
  have hgc : Continuous g :=
    (Complex.continuous_ofReal.comp (b.continuous.comp continuous_mR)).mul hpc
  have hre : ∀ u, (g u).re = b (mR u) * (psi m e μK u).re := fun u => Complex.re_ofReal_mul _ _
  have hpos : 0 < ∫ u, (g u).re ∂ν := by
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1)
      (Complex.continuous_re.comp hgc) (hgs.comp_left Complex.zero_re) ?_ ?_
    · intro u
      show 0 ≤ (g u).re
      rw [hre]
      by_cases hu : b (mR u) = 0
      · simp [hu]
      · have hmem : mR u ∈ Metric.ball (1 : M2 n) r := by
          have hs : mR u ∈ Function.support b := hu
          rwa [b.support_eq] at hs
        have hu' : u ∈ mR ⁻¹' O := hball hmem
        rw [hOeq] at hu'
        exact mul_nonneg b.nonneg (le_of_lt hu')
    · show (g 1).re ≠ 0
      rw [hre, h1, b.one_of_mem_closedBall (Metric.mem_closedBall_self (by positivity)), one_mul]
      exact ne_of_gt hp1
  intro h
  have hz : (∫ u, g u ∂ν).re = 0 := by
    rw [h]
    simp
  have hgi : Integrable g ν := hgc.integrable_of_hasCompactSupport hgs
  have hint := integral_re hgi
  simp only [RCLike.re_to_complex] at hint
  linarith

end PositivityTheory.Rg.Sw.HSt.Conv
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.ContDiffMatrixMul
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.ParamCD
noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt.PCD

variable {F X : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X] [SecondCountableTopology X]

structure Good {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (Ω : Set F) (K : F → X → E) : Prop where
  smooth : ∀ u, ContDiffOn ℝ ∞ (K · u) Ω
  cont : ∀ N : ℕ, ContinuousOn (fun p : F × X => iteratedFDeriv ℝ N (K · p.2) p.1) (Ω ×ˢ univ)
  supp : ∀ x ∈ Ω, ∃ V : Set F, IsOpen V ∧ x ∈ V ∧ ∃ C : Set X, IsCompact C ∧ ∀ x' ∈ V, ∀ u ∉ C, K x' u = 0

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Set F} {K : F → X → E}

theorem Good.continuousOn (hK : Good Ω K) : ContinuousOn (fun p : F × X => K p.1 p.2) (Ω ×ˢ univ) := by
  have h := (continuousMultilinearCurryFin0 ℝ F E).continuous.comp_continuousOn (hK.cont 0)
  refine h.congr fun p _ => ?_
  simp

theorem Good.dK (hΩ : IsOpen Ω) (hK : Good Ω K) : Good Ω (fun x u => fderiv ℝ (K · u) x) := by
  refine ⟨fun u => ((contDiffOn_infty_iff_fderiv_of_isOpen hΩ).1 (hK.smooth u)).2, fun N => ?_, fun x hx => ?_⟩
  · have h : ContinuousOn (fun p : F × X => (continuousMultilinearCurryRightEquiv' ℝ N F E)
        (iteratedFDeriv ℝ (N + 1) (K · p.2) p.1)) (Ω ×ˢ univ) :=
      (LinearIsometryEquiv.continuous _).comp_continuousOn (hK.cont (N + 1))
    refine h.congr fun p _ => ?_
    simp only [Function.comp_apply]
    rw [iteratedFDeriv_succ_eq_comp_right]
    simp
  · obtain ⟨V, hV, hxV, C, hC, hKV⟩ := hK.supp x hx
    refine ⟨V, hV, hxV, C, hC, fun x' hx' u hu => ?_⟩
    have : (K · u) =ᶠ[𝓝 x'] fun _ => 0 := by
      filter_upwards [hV.mem_nhds hx'] with y hy using hKV y hy u hu
    rw [this.fderiv_eq]
    simp

theorem Good.integrable (hK : Good Ω K) (ν : Measure X) [IsFiniteMeasureOnCompacts ν] {x : F} (hx : x ∈ Ω) :
    Integrable (K x) ν := by
  obtain ⟨V, -, hxV, C, hC, hKV⟩ := hK.supp x hx
  have hc : Continuous (K x) := by
    have := hK.continuousOn
    exact this.comp_continuous (Continuous.prodMk continuous_const continuous_id) (fun u => ⟨hx, mem_univ _⟩)
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.intro hC fun u hu => hKV x hxV u hu)

theorem Good.hasFDerivAt [CompleteSpace E] (hΩ : IsOpen Ω) (hK : Good Ω K) (ν : Measure X) [IsFiniteMeasureOnCompacts ν]
    {x₀ : F} (hx₀ : x₀ ∈ Ω) :
    HasFDerivAt (fun x => ∫ u, K x u ∂ν) (∫ u, fderiv ℝ (K · u) x₀ ∂ν) x₀ := by
  obtain ⟨V, hV, hxV, C, hC, hKV⟩ := hK.supp x₀ hx₀
  obtain ⟨ε, hε, hεs⟩ := Metric.isOpen_iff.1 (hΩ.inter hV) x₀ ⟨hx₀, hxV⟩
  have hK' := hK.dK hΩ
  have hc' := hK'.continuousOn
  have hcb : IsCompact (Metric.closedBall x₀ (ε / 2) ×ˢ C) := (isCompact_closedBall _ _).prod hC
  have hsub : Metric.closedBall x₀ (ε / 2) ×ˢ C ⊆ Ω ×ˢ univ := by
    intro p hp
    exact ⟨(hεs (Metric.closedBall_subset_ball (by linarith) hp.1)).1, mem_univ _⟩
  obtain ⟨M, hM⟩ := hcb.exists_bound_of_continuousOn (hc'.mono hsub)
  have hcont_u : ∀ x ∈ Ω, Continuous (K x) := fun x hx =>
    hK.continuousOn.comp_continuous (Continuous.prodMk continuous_const continuous_id) (fun u => ⟨hx, mem_univ _⟩)
  have hcont'_u : ∀ x ∈ Ω, Continuous (fun u => fderiv ℝ (K · u) x) := fun x hx =>
    hc'.comp_continuous (Continuous.prodMk continuous_const continuous_id) (fun u => ⟨hx, mem_univ _⟩)
  have hball : Metric.ball x₀ (ε / 2) ⊆ Ω ∩ V := fun y hy => hεs (Metric.ball_subset_ball (by linarith) hy)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := ν) (F := K) (F' := fun x u => fderiv ℝ (K · u) x)
    (s := Metric.ball x₀ (ε / 2))
    (bound := C.indicator fun _ => M) (Metric.ball_mem_nhds _ (by linarith)) ?_ (hK.integrable ν hx₀)
    (hcont'_u x₀ hx₀).aestronglyMeasurable ?_ ?_ ?_
  · filter_upwards [hΩ.mem_nhds hx₀] with x hx using (hcont_u x hx).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun u x hx => ?_
    by_cases hu : u ∈ C
    · rw [indicator_of_mem hu]
      exact hM (x, u) ⟨Metric.ball_subset_closedBall hx, hu⟩
    · rw [indicator_of_notMem hu]
      have : (K · u) =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [hV.mem_nhds (hball hx).2] with y hy using hKV y hy u hu
      rw [this.fderiv_eq]
      simp
  · exact (integrableOn_const (C := M) hC.measure_lt_top.ne).integrable_indicator hC.isClosed.measurableSet
  · refine Filter.Eventually.of_forall fun u x hx => ?_
    have hxΩ := (hball hx).1
    exact ((hK.smooth u).differentiableOn (by simp) x hxΩ).differentiableAt (hΩ.mem_nhds hxΩ) |>.hasFDerivAt

omit [NormedSpace ℝ E] in
theorem contDiffOn_nat (hΩ : IsOpen Ω) (ν : Measure X) [IsFiniteMeasureOnCompacts ν] (N : ℕ) :
    ∀ (E' : Type) [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E'] (K : F → X → E'), Good Ω K →
      ContDiffOn ℝ N (fun x => ∫ u, K x u ∂ν) Ω := by
  induction N with
  | zero =>
    intro E' _ _ _ K hK
    rw [Nat.cast_zero, contDiffOn_zero]
    exact fun x hx => (hK.hasFDerivAt hΩ ν hx).continuousAt.continuousWithinAt
  | succ N ih =>
    intro E' _ _ _ K hK
    rw [show ((N + 1 : ℕ) : WithTop ℕ∞) = (N : WithTop ℕ∞) + 1 by push_cast; rfl,
      contDiffOn_succ_iff_fderiv_of_isOpen hΩ]
    refine ⟨fun x hx => (hK.hasFDerivAt hΩ ν hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    refine (ih (F →L[ℝ] E') _ (hK.dK hΩ)).congr fun x hx => ?_
    exact (hK.hasFDerivAt hΩ ν hx).fderiv

theorem contDiffOn_integral [CompleteSpace E] (hΩ : IsOpen Ω) (ν : Measure X) [IsFiniteMeasureOnCompacts ν]
    (hK : Good Ω K) : ContDiffOn ℝ ∞ (fun x => ∫ u, K x u ∂ν) Ω :=
  contDiffOn_infty.2 fun N => contDiffOn_nat hΩ ν N E K hK

section Kernel

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] {Ω : Set F}

omit [FiniteDimensional ℝ F] in
theorem slice (hΩ : IsOpen Ω) {k : F × V → E} (hk : ContDiffOn ℝ ∞ k (Ω ×ˢ univ)) (N : ℕ) {x : F} (hx : x ∈ Ω) (w : V) :
    iteratedFDeriv ℝ N (fun x => k (x, w)) x =
      (iteratedFDeriv ℝ N k (x, w)).compContinuousLinearMap (fun _ => ContinuousLinearMap.inl ℝ F V) := by
  set f' : F × V → E := fun p => k (p + (0, w))
  have hS : IsOpen (Ω ×ˢ (univ : Set V)) := hΩ.prod isOpen_univ
  have hf' : ContDiffOn ℝ ∞ f' (Ω ×ˢ univ) := by
    refine hk.comp (contDiffOn_id.add contDiffOn_const) fun p hp => ?_
    exact ⟨by simpa using hp.1, mem_univ _⟩
  have hpre : (ContinuousLinearMap.inl ℝ F V) ⁻¹' (Ω ×ˢ univ) = Ω := by ext y; simp
  have h1 := ContinuousLinearMap.iteratedFDerivWithin_comp_right (ContinuousLinearMap.inl ℝ F V) hf'
    hS.uniqueDiffOn (by rw [hpre]; exact hΩ.uniqueDiffOn) (x := x) (by simpa using hx) (i := N) (by exact_mod_cast le_top)
  rw [hpre, iteratedFDerivWithin_of_isOpen N hΩ hx, iteratedFDerivWithin_of_isOpen N hS (by simpa using hx)] at h1
  have h2 : (f' ∘ ContinuousLinearMap.inl ℝ F V) = fun x => k (x, w) := by
    funext y; simp [f']
  rw [h2] at h1
  rw [h1]
  congr 1
  have h3 := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := k) N ((0 : F), w) (ContinuousLinearMap.inl ℝ F V x)
  simpa using h3

theorem good_of_joint (hΩ : IsOpen Ω) (k : F × V → E) (hk : ContDiffOn ℝ ∞ k (Ω ×ˢ univ)) (v : X → V)
    (hv : Continuous v) (h : X → ℂ) (hh : Continuous h)
    (hsupp : ∀ x ∈ Ω, ∃ W ∈ 𝓝 x, ∃ C : Set X, IsCompact C ∧ ∀ x' ∈ W, ∀ u ∉ C, k (x', v u) = 0) :
    Good Ω (fun x u => h u • k (x, v u)) := by
  have hsl : ∀ u, ContDiffOn ℝ ∞ (fun x => k (x, v u)) Ω := fun u =>
    hk.comp (contDiffOn_id.prodMk contDiffOn_const) fun x hx => ⟨hx, mem_univ _⟩
  refine ⟨fun u => (hsl u).const_smul (h u), fun N => ?_, fun x hx => ?_⟩
  · have hS : IsOpen (Ω ×ˢ (univ : Set V)) := hΩ.prod isOpen_univ
    have hcont : ContinuousOn (fun q : F × V => iteratedFDeriv ℝ N k q) (Ω ×ˢ univ) := by
      have := hk.continuousOn_iteratedFDerivWithin (m := N) (by exact_mod_cast le_top) hS.uniqueDiffOn
      exact this.congr fun q hq => (iteratedFDerivWithin_of_isOpen N hS hq).symm
    let hL := ContinuousMultilinearMap.compContinuousLinearMapL (𝕜 := ℝ) (F := E)
      (fun _ : Fin N => ContinuousLinearMap.inl ℝ F V)
    have hc2 : ContinuousOn (fun p : F × X => h p.2 • (hL (iteratedFDeriv ℝ N k (p.1, v p.2)))) (Ω ×ˢ univ) := by
      refine (hh.comp continuous_snd).continuousOn.smul (hL.continuous.comp_continuousOn ?_)
      exact hcont.comp (continuous_fst.prodMk (hv.comp continuous_snd)).continuousOn fun p hp => ⟨hp.1, mem_univ _⟩
    refine hc2.congr fun p hp => ?_
    have hx : p.1 ∈ Ω := hp.1
    simp only
    rw [iteratedFDeriv_const_smul_apply' ((hsl p.2).contDiffAt (hΩ.mem_nhds hx) |>.of_le (by exact_mod_cast le_top)),
      slice hΩ hk N hx (v p.2)]
    rfl
  · obtain ⟨W, hW, C, hC, hKW⟩ := hsupp x hx
    obtain ⟨W', hW'W, hW'o, hxW'⟩ := mem_nhds_iff.1 hW
    exact ⟨W', hW'o, hxW', C, hC, fun x' hx' u hu => by simp [hKW x' (hW'W hx') u hu]⟩

theorem contDiffOn_integral' (hΩ : IsOpen Ω) (ν : Measure X) [IsFiniteMeasureOnCompacts ν] (k : F × V → E)
    (hk : ContDiffOn ℝ ∞ k (Ω ×ˢ univ)) (v : X → V) (hv : Continuous v) (h : X → ℂ) (hh : Continuous h)
    (hsupp : ∀ x ∈ Ω, ∃ W ∈ 𝓝 x, ∃ C : Set X, IsCompact C ∧ ∀ x' ∈ W, ∀ u ∉ C, k (x', v u) = 0) :
    ContDiffOn ℝ ∞ (fun x => ∫ u, h u • k (x, v u) ∂ν) Ω :=
  contDiffOn_integral hΩ ν (good_of_joint hΩ k hk v hv h hh hsupp)

end Kernel

end PositivityTheory.Rg.Sw.HSt.PCD
end
end

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt.Conv

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.HSt.GRH PositivityTheory.Rg.Sw.HSt.MI

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem contDiff_mul_M2 : ContDiff ℝ ∞ (fun p : M2 n × M2 n => p.1 * p.2) := by
  refine contDiff_of_entries fun a b => ?_
  have : (fun p : M2 n × M2 n => (p.1 * p.2) a b) = fun p => ∑ c, p.1 a c * p.2 c b := by
    funext p; rfl
  rw [this]
  exact ContDiff.sum fun c _ => ((contDiff_entry a c).comp contDiff_fst).mul ((contDiff_entry c b).comp contDiff_snd)

theorem tw_contDiff (m : ℕ) (e : ℤ) (μK : Measure (KR n)) [μK.IsHaarMeasure] {β : M2 n → ℝ}
    (hβ : ContDiff ℝ ∞ β) : ContDiff ℝ ∞ (tw m e μK β) := by
  have hk : ContDiffOn ℝ ∞ (fun p : M2 n × M2 n => ((β (p.2 * p.1) : ℝ) : ℂ)) (univ ×ˢ univ) := by
    have h1 : ContDiff ℝ ∞ (fun p : M2 n × M2 n => p.2 * p.1) := contDiff_mul_M2.comp (contDiff_snd.prodMk contDiff_fst)
    exact (Complex.ofRealCLM.contDiff.comp (hβ.comp h1)).contDiffOn
  have hv : Continuous (fun k : KR n => (mR (k : GR n))ᴴ) := continuous_kR.matrix_conjTranspose
  have hh : Continuous (fun k : KR n => (F0 m 0 e (k : GR n))⁻¹) :=
    ((Vac.continuous_weight_factor detU1 m 0 e).comp continuous_subtype_val).inv₀ fun k => Vac.spherical_section_ne_zero detU1 m 0 e _
  have := PCD.contDiffOn_integral' (F := M2 n) (X := KR n) isOpen_univ μK
    (fun p : M2 n × M2 n => ((β (p.2 * p.1) : ℝ) : ℂ)) hk (fun k : KR n => (mR (k : GR n))ᴴ) hv
    (fun k : KR n => (F0 m 0 e (k : GR n))⁻¹) hh
    (fun x _ => ⟨univ, univ_mem, univ, isCompact_univ, fun _ _ u hu => absurd (mem_univ u) hu⟩)
  rw [contDiffOn_univ] at this
  have e' : tw m e μK β = fun X => ∫ k : KR n, (F0 m 0 e (k : GR n))⁻¹ • ((β ((mR (k : GR n))ᴴ * X) : ℝ) : ℂ) ∂μK := by
    funext X; rfl
  rw [e']
  exact this

def kk (m : ℕ) (e : ℤ) (μK : Measure (KR n)) (β : M2 n → ℝ) (p : M2 n × M2 n) : ℂ := tw m e μK β (p.1⁻¹ * p.2)

theorem kk_contDiffOn (m : ℕ) (e : ℤ) (μK : Measure (KR n)) [μK.IsHaarMeasure] {β : M2 n → ℝ}
    (hβ : ContDiff ℝ ∞ β) : ContDiffOn ℝ ∞ (kk m e μK β) (Inv n ×ˢ univ) := by
  have h1 : ContDiffOn ℝ ∞ (fun p : M2 n × M2 n => (p.1⁻¹, p.2)) (Inv n ×ˢ univ) :=
    (contDiffOn_inv.comp contDiffOn_fst fun (p : M2 n × M2 n) (hp : p ∈ Inv n ×ˢ univ) => hp.1).prodMk contDiffOn_snd
  exact (tw_contDiff m e μK hβ).comp_contDiffOn (contDiff_mul_M2.comp_contDiffOn h1)

theorem kk_supp (m : ℕ) (e : ℤ) (μK : Measure (KR n)) {β : M2 n → ℝ} (hβs : HasCompactSupport β) :
    ∀ x ∈ Inv n, ∃ W ∈ 𝓝 x, ∃ C : Set (GR n), IsCompact C ∧ ∀ x' ∈ W, ∀ u ∉ C, kk m e μK β (x', mR u) = 0 := by
  intro x hx
  obtain ⟨r, hr, hrs⟩ := Metric.isOpen_iff.mp isOpen_Inv x hx
  have hFD : FiniteDimensional ℝ (M2 n) := inferInstanceAs (FiniteDimensional ℝ (Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℂ))
  have hPS : ProperSpace (M2 n) := FiniteDimensional.proper ℝ (M2 n)
  set B := Metric.closedBall x (r / 2)
  have hB : IsCompact B := isCompact_closedBall x (r / 2)
  have hBI : B ⊆ Inv n := fun y hy => hrs (lt_of_le_of_lt (Metric.mem_closedBall.mp hy) (half_lt_self hr))
  set T := (fun p : M2 n × M2 n => p.1 * p.2) '' (B ×ˢ kSet (tsupport β))
  have hT : IsCompact T := (hB.prod (isCompact_kSet hβs)).image contDiff_mul_M2.continuous
  refine ⟨Metric.closedBall x (r / 2), Metric.closedBall_mem_nhds x (half_pos hr), (mR : GR n → M2 n) ⁻¹' T,
    isCompact_preimage_mR hT, fun x' hx' u hu => ?_⟩
  unfold kk
  refine tw_eq_zero m e μK β fun hmem => hu ?_
  refine ⟨(x', x'⁻¹ * mR u), ⟨hx', hmem⟩, ?_⟩
  show x' * (x'⁻¹ * mR u) = mR u
  have hdet : IsUnit x'.det := isUnit_iff_ne_zero.mpr (hBI hx')
  rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mul]

end PositivityTheory.Rg.Sw.HSt.Conv
end
end
