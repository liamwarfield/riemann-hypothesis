module

public import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsThetaFunOOfThetaAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffSetIntegralNat
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSmoothCompactSupportFixLowestKType
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselDatumAuxiliaryVectorOrthogonalImage
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeLeSmoothVectors
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeLeSmoothVectors
noncomputable section

open MeasureTheory Matrix
open scoped ContDiff Topology InnerProductSpace

namespace GlobalTheory.SmoothLowType

open Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.GardingVec

section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem exists_bump (n : ℕ) (ε : Fin n → Bool) (U : Set (UJ ε)) (hU : U ∈ nhds (1 : UJ ε)) :
    ∃ a : Matrix (Fin n) (Fin n) ℂ → ℝ,
      (∀ (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] (f : P → Matrix (Fin n) (Fin n) ℂ),
        (∀ i j, ContDiff ℝ ∞ fun p => f p i j) → ContDiff ℝ ∞ fun p => a (f p)) ∧ (∀ y, 0 ≤ a y) ∧ a 1 ≠ 0 ∧
      HasCompactSupport (fun g : UJ ε => a (umat g)) ∧ (∀ g : UJ ε, a (umat g) ≠ 0 → g ∈ U) ∧
      ∀ k ∈ Kset ε, ∀ y, a (k * y) = a (y * k) := by
  obtain ⟨a, ha, h⟩ := GlobalTheory.exists_conjInvariant_bump n ε U hU
  refine ⟨a, fun P _ _ f hf => ha.comp ?_, h⟩
  exact contDiff_pi.2 fun i => contDiff_pi.2 fun j => hf i j
end

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem contDiff_entry {n : ℕ} (i j : Fin n) : ContDiff ℝ ∞ fun x : Matrix (Fin n) (Fin n) ℂ => x i j := by
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun x => x i j
      map_add' := fun x y => rfl
      map_smul' := fun c x => rfl }
  exact (LinearMap.toContinuousLinearMap L).contDiff

theorem garding_smooth {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsURepOn (UJset ε) σ) {φ : Matrix (Fin n) (Fin n) ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hψc : HasCompactSupport fun g : UJ ε => φ (umat g)) (w : H)
    (k : ℕ) (x : (Fin k → ℝ) → Matrix (Fin n) (Fin n) ℂ) (hx : ContDiff ℝ ∞ x) (hxG : ∀ t, x t ∈ UJset ε) :
    ContDiff ℝ ∞ fun t => σ (x t) (∫ g : UJ ε, φ (umat g) • σ (umat g) w ∂(muG ε)) := by
  obtain ⟨⟨h1, hmul⟩, -, hcont⟩ := hσ
  obtain ⟨hemb, hrange⟩ := Formalism.REAL.isClosedEmbeddingMatrix n ε
  set μ := Formalism.REAL.muG ε
  have hmem : ∀ g : Formalism.REAL.UJ ε, umat g ∈ UJset ε := fun g => g.2
  have hu : Continuous fun g : Formalism.REAL.UJ ε => umat g := hemb.continuous
  have hb : Continuous fun g : Formalism.REAL.UJ ε => σ (umat g) w := (hcont w).comp_continuous hu hmem
  have hψ : Continuous fun g : Formalism.REAL.UJ ε => φ (umat g) := hφ.continuous.comp hu
  have hint : Integrable (fun g : Formalism.REAL.UJ ε => φ (umat g) • σ (umat g) w) μ :=
    (hψ.smul hb).integrable_of_hasCompactSupport hψc.smul_right
  let y : (Fin k → ℝ) → Matrix (Fin n) (Fin n) ℂ := fun t => Formalism.REAL.Jm ε * (x t)ᴴ * Formalism.REAL.Jm ε
  have hy : ContDiff ℝ ∞ y := (contDiff_const.mul (contDiff_conjTranspose.comp hx)).mul contDiff_const
  have hyx : ∀ t, y t * x t = 1 := fun t => by
    have h : (x t)ᴴ * Formalism.REAL.Jm ε * x t = Formalism.REAL.Jm ε := hxG t
    calc y t * x t = Formalism.REAL.Jm ε * ((x t)ᴴ * Formalism.REAL.Jm ε * x t) := by simp only [y, Matrix.mul_assoc]
      _ = 1 := by rw [h, Formalism.REAL.Jm_mul_self]
  have hxy : ∀ t, x t * y t = 1 := fun t => mul_eq_one_comm.1 (hyx t)
  have hz : ∀ t, ∃ z : UJ ε, umat z = x t := fun t => by
    have : x t ∈ Set.range (fun g : Formalism.REAL.UJ ε => umat g) := by
      rw [show Set.range (fun g : Formalism.REAL.UJ ε => umat g) = _ from hrange]; exact hxG t
    exact this
  have hform : ∀ t, σ (x t) (∫ g : Formalism.REAL.UJ ε, φ (umat g) • σ (umat g) w ∂μ)
      = ∫ g : Formalism.REAL.UJ ε, φ (y t * umat g) • σ (umat g) w ∂μ := by
    intro t
    obtain ⟨z, hz'⟩ := hz t
    rw [← ContinuousLinearMap.integral_comp_comm _ hint,
      ← integral_mul_left_eq_self (fun g : Formalism.REAL.UJ ε => φ (y t * umat g) • σ (umat g) w) z]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    have e : umat (z * g) = x t * umat g := by rw [← hz']; rfl
    simp only [e]
    rw [← Matrix.mul_assoc, hyx, Matrix.one_mul, hmul _ (hxG t) _ (hmem g),
      ContinuousLinearMap.map_smul_of_tower]
    rfl
  simp only [hform]
  refine contDiff_iff_contDiffAt.2 fun t₀ => ?_
  have hC : IsCompact (Set.image2 (· * ·) (x '' Metric.closedBall t₀ 1)
      ((fun g : UJ ε => umat g) '' tsupport fun g : UJ ε => φ (umat g))) :=
    ((isCompact_closedBall t₀ 1).image hx.continuous).mul (IsCompact.image hψc hu)
  have hK := hemb.isCompact_preimage hC
  have hs : ContDiff ℝ ∞ fun t => ∫ g in (fun g : Formalism.REAL.UJ ε => umat g) ⁻¹'
      (Set.image2 (· * ·) (x '' Metric.closedBall t₀ 1)
        ((fun g : UJ ε => umat g) '' tsupport fun g : UJ ε => φ (umat g))),
      φ (y t * umat g) • σ (umat g) w ∂μ :=
    contDiff_infty.2 fun m => contDiff_setIntegral_nat μ hK (hu.prodMk hb) m
      (fun z : (Fin k → ℝ) × (Matrix (Fin n) (Fin n) ℂ × H) => φ (y z.1 * z.2.1) • z.2.2)
      ((hφ.comp ((hy.comp contDiff_fst).mul (contDiff_fst.comp contDiff_snd))).smul
        (contDiff_snd.comp contDiff_snd))
  refine hs.contDiffAt.congr_of_eventuallyEq ?_
  filter_upwards [Metric.closedBall_mem_nhds t₀ one_pos] with t ht
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun g hg => ?_).symm
  by_contra hne
  obtain ⟨z, hz'⟩ := hz t
  have e : x t * umat (z⁻¹ * g) = umat g := by
    rw [← hz']
    show umat (z * (z⁻¹ * g)) = _
    rw [mul_inv_cancel_left]
  have e' : umat (z⁻¹ * g) = y t * umat g := by
    rw [← e, ← Matrix.mul_assoc, hyx, Matrix.one_mul]
  refine hg ⟨x t, ⟨t, ht, rfl⟩, umat (z⁻¹ * g), ⟨z⁻¹ * g, subset_tsupport _ fun h => hne ?_, rfl⟩, e⟩
  have h' : φ (umat (z⁻¹ * g)) = 0 := h
  rw [← e', h', zero_smul]

theorem exists_smooth_ktype {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsURepOn (UJset ε) σ) {Λ : Fin n → ℝ} {S : Submodule ℂ H} (hK : IsKTypeOf ε σ Λ S) :
    ∃ S' : Submodule ℂ H, IsKTypeOf ε σ Λ S' ∧ ∀ v ∈ S', ∀ (k : ℕ) (x : (Fin k → ℝ) → Matrix (Fin n) (Fin n) ℂ),
      ContDiff ℝ ∞ x → (∀ t, x t ∈ UJset ε) → ContDiff ℝ ∞ fun t => σ (x t) v := by
  have : (muG ε).IsMulRightInvariant := ⟨fun g => indefinite_unitary_unimodular n ε g⟩
  haveI := hK.1
  obtain ⟨v, hvS, hv0, -⟩ := hK.2.2.2.1
  have humat : Continuous (fun g : UJ ε => umat g) := (isClosedEmbeddingMatrix n ε).1.continuous
  have hcont : ∀ s : H, Continuous (fun g : UJ ε => σ (umat g) s) := fun s =>
    (hσ.2.2 s).comp_continuous humat (fun g => g.2)
  have hre : Continuous (fun g : UJ ε => (⟪v, σ (umat g) v⟫_ℂ).re) :=
    Complex.continuous_re.comp (continuous_const.inner (hcont v))
  have hone : 0 < (⟪v, σ (umat (1 : UJ ε)) v⟫_ℂ).re := by
    have : σ (umat (1 : UJ ε)) = 1 := hσ.1.1
    rw [this]
    exact re_inner_self_pos (𝕜 := ℂ).2 hv0
  obtain ⟨a, ha', ha0, ha1, hac, haU, haK⟩ := exists_bump n ε
    {g | 0 < (⟪v, σ (umat g) v⟫_ℂ).re} ((isOpen_lt continuous_const hre).mem_nhds hone)
  have ha : ContDiff ℝ ∞ a := ha' _ (fun p => p) contDiff_entry
  have hacont : Continuous (fun g : UJ ε => a (umat g)) := ha.continuous.comp humat
  have hacC : Continuous (fun g : UJ ε => (a (umat g) : ℂ)) := Complex.continuous_ofReal.comp hacont
  have hsuppC : HasCompactSupport (fun g : UJ ε => (a (umat g) : ℂ)) :=
    hac.comp_left (g := fun x : ℝ => (x : ℂ)) (by simp)
  have hint : ∀ s : H, Integrable (fun g : UJ ε => (a (umat g) : ℂ) • σ (umat g) s) (muG ε) :=
    fun s => (hacC.smul (hcont s)).integrable_of_hasCompactSupport hsuppC.smul_right
  let T : S →ₗ[ℂ] H :=
    { toFun := fun s => ∫ g : UJ ε, (a (umat g) : ℂ) • σ (umat g) s ∂(muG ε)
      map_add' := by
        intro s t
        rw [← integral_add (hint s) (hint t)]
        simp only [Submodule.coe_add, map_add (f := _), smul_add]
      map_smul' := by
        intro c s
        rw [RingHom.id_apply, ← integral_smul]
        simp only [Submodule.coe_smul, map_smul, smul_comm c] }
  have hT : ∀ (s : S) (u : H), ⟪u, T s⟫_ℂ =
      ∫ g : UJ ε, (a (umat g) : ℂ) * ⟪u, σ (umat g) s⟫_ℂ ∂(muG ε) := by
    intro s u
    show ⟪u, ∫ g : UJ ε, (a (umat g) : ℂ) • σ (umat g) s ∂(muG ε)⟫_ℂ = _
    rw [← integral_inner (hint s)]
    simp only [inner_smul_right]
  refine ⟨_, GlobalTheory.Dec.FormF.rangeType n ε Λ H σ S H σ (LinearMap.toContinuousLinearMap T) hK ?_ ?_, ?_⟩
  · intro k hk s s' hs'
    have hu : k ∈ Set.range (fun g : UJ ε => umat g) := by
      rw [(isClosedEmbeddingMatrix n ε).2]
      exact (maximal_compact_facts n ε).1 k hk
    obtain ⟨κ, rfl⟩ := hu
    show ∫ g : UJ ε, (a (umat g) : ℂ) • σ (umat g) s' ∂(muG ε) =
      σ (umat κ) (∫ g : UJ ε, (a (umat g) : ℂ) • σ (umat g) s ∂(muG ε))
    rw [← ContinuousLinearMap.integral_comp_comm _ (hint s), hs']
    have e1 : ∫ g : UJ ε, (a (umat g) : ℂ) • σ (umat g) (σ (umat κ) s) ∂(muG ε) =
        ∫ g : UJ ε, (a (umat (g * κ⁻¹)) : ℂ) • σ (umat g) s ∂(muG ε) := by
      rw [← integral_mul_right_eq_self
        (fun g : UJ ε => (a (umat (g * κ⁻¹)) : ℂ) • σ (umat g) (s : H)) κ]
      congr 1
      funext g
      have : σ (umat (g * κ)) = _ := hσ.1.2 (umat g) g.2 (umat κ) κ.2
      rw [this, mul_inv_cancel_right]
      rfl
    have e2 : ∫ g : UJ ε, σ (umat κ) ((a (umat g) : ℂ) • σ (umat g) s) ∂(muG ε) =
        ∫ g : UJ ε, (a (umat (κ⁻¹ * g)) : ℂ) • σ (umat g) s ∂(muG ε) := by
      rw [← integral_mul_left_eq_self
        (fun g : UJ ε => (a (umat (κ⁻¹ * g)) : ℂ) • σ (umat g) (s : H)) κ]
      congr 1
      funext g
      have : σ (umat (κ * g)) = _ := hσ.1.2 (umat κ) κ.2 (umat g) g.2
      rw [this, inv_mul_cancel_left, map_smul]
      rfl
    refine e1.trans (Eq.trans ?_ e2.symm)
    congr 1
    funext g
    have hk' : umat κ⁻¹ ∈ Kset ε := (KG ε).inv_mem (x := κ) hk
    have : a (umat (κ⁻¹ * g)) = a (umat (g * κ⁻¹)) := haK _ hk' (umat g)
    rw [this]
  · intro h0
    have hc : T ⟨v, hvS⟩ = 0 := congrArg (fun f : S →L[ℂ] H => f ⟨v, hvS⟩) h0
    have h1 := hT ⟨v, hvS⟩ v
    rw [hc, inner_zero_right] at h1
    have hi : Integrable (fun g : UJ ε => (a (umat g) : ℂ) * ⟪v, σ (umat g) v⟫_ℂ) (muG ε) :=
      (hacC.mul (continuous_const.inner (hcont v))).integrable_of_hasCompactSupport hsuppC.mul_right
    have h2 := congrArg Complex.re h1
    have h3 := integral_re (𝕜 := ℂ) hi
    simp only [RCLike.re_to_complex, Complex.re_ofReal_mul] at h3
    rw [← h3] at h2
    have h4 : 0 < ∫ g : UJ ε, a (umat g) * (⟪v, σ (umat g) v⟫_ℂ).re ∂(muG ε) := by
      refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1)
        (hacont.mul hre) hac.mul_right ?_ (mul_ne_zero ha1 hone.ne')
      intro g
      by_cases h : a (umat g) = 0
      · simp [h]
      · exact mul_nonneg (ha0 _) (le_of_lt (haU g h))
    rw [← h2] at h4
    simp at h4
  · rintro _ ⟨s, rfl⟩ k x hx hxG
    have e : (T s : H) = ∫ g : UJ ε, a (umat g) • σ (umat g) (s : H) ∂(muG ε) := by
      show ∫ g : UJ ε, (a (umat g) : ℂ) • σ (umat g) s ∂(muG ε) = _
      simp only [Complex.coe_smul]
    show ContDiff ℝ ∞ fun t => σ (x t) (T s)
    rw [e]
    exact garding_smooth hσ ha hac s k x hx hxG

theorem exists_smoothVec_ktype {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsURepOn (UJset ε) σ) {Λ : Fin n → ℝ} {S : Submodule ℂ H} (hK : IsKTypeOf ε σ Λ S)
    {P G : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) (h : Pᴴ * Formalism.REAL.Jm ε * P = G) :
    ∃ S' : Submodule ℂ H, IsKTypeOf ε σ Λ S' ∧
      ∀ v ∈ S', Formalism.L2.Theta.SmoothVec {X | Xᴴ * G + G * X = 0} (fun g => σ (P * g * P⁻¹)) v := by
  obtain ⟨S', hS', hs⟩ := exists_smooth_ktype hσ hK
  have hG : IsUnit G := by
    rw [← h]
    exact (((Matrix.isUnit_conjTranspose _).2 hP).mul
      (IsUnit.of_mul_eq_one _ (Formalism.REAL.Jm_mul_self ε))).mul hP
  refine ⟨S', hS', fun v hv k Xs hX =>
    hs v hv k _ ((contDiff_const.mul (contDiff_expProd Xs)).mul contDiff_const) fun t => ?_⟩
  refine conj_mem hP h (list_prod_mem _ fun g hg => ?_)
  obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hg
  exact exp_mem hG (hX i) _

end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_lowK_le_sm : ∀ (D : D7) (V : HSp D) (Sp : D.what₂.Tau → SPar) (M : DSModel V Sp) (τ : D.what₂.Tau),
    ∃ S : Submodule ℂ (M.H τ), IsKTypeOf (M.ε τ) (M.σ τ) (Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ)) S ∧ S ≤ M.sm τ := by
  intro D V Sp M τ
  obtain ⟨h1, h2, h3, -, -, ⟨S, hS⟩, -⟩ := M.ds τ
  obtain ⟨S', hS', hs⟩ := exists_smoothVec_ktype h3 hS (M.fr_unit τ) (M.fr_gram τ)
  exact ⟨S', hS', fun v hv => Submodule.subset_span (hs v hv)⟩

end GlobalTheory.SmoothLowType
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeLeSmoothVectorsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lowestKType_le_smoothVectors : ∀ (D : D7) (V : HSp D) (Sp : D.what₂.Tau → SPar) (M : DSModel V Sp) (τ : D.what₂.Tau), ∃ S : Submodule ℂ (M.H τ), IsKTypeOf (M.ε τ) (M.σ τ) (Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ)) S ∧ S ≤ M.sm τ := by
  first | exact @GlobalTheory.SmoothLowType.exists_lowK_le_sm | exact GlobalTheory.SmoothLowType.exists_lowK_le_sm | (intros; apply GlobalTheory.SmoothLowType.exists_lowK_le_sm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FsubMinorMinus
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.JointHarm.DeltaEig

theorem det_subst {R : Type} [CommRing R] [Algebra ℂ R] {m n s : ℕ} (F : Fin m → Fin n → R)
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ) (e : Fin s → Fin m) (f : Fin s → Fin n)
    (he : Function.Injective e) (hf : Function.Injective f)
    (hA : ∀ a β, A a (e β) ≠ 0 → ∃ γ, e γ = a) (hB : ∀ α b, B (f α) b ≠ 0 → ∃ γ, f γ = b) :
    (Matrix.of fun α β : Fin s => ∑ a, ∑ b, algebraMap ℂ R (A a (e β) * B (f α) b) * F a b).det =
      ((A.submatrix e e).det * (B.submatrix f f).det) • (Matrix.of fun α β : Fin s => F (e β) (f α)).det := by
  have key : (Matrix.of fun α β : Fin s => ∑ a, ∑ b, algebraMap ℂ R (A a (e β) * B (f α) b) * F a b) =
      (algebraMap ℂ R).mapMatrix (B.submatrix f f) * (Matrix.of fun α β : Fin s => F (e β) (f α)) *
        (algebraMap ℂ R).mapMatrix (A.submatrix e e) := by
    ext α β
    simp only [Matrix.mul_apply, Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
      Matrix.submatrix_apply, Finset.sum_mul]
    symm
    refine Fintype.sum_of_injective e he _ _ (fun a ha => ?_) (fun γ => ?_)
    · have : A a (e β) = 0 := by
        by_contra h
        exact ha (hA a β h)
      simp [this]
    · refine Fintype.sum_of_injective f hf _ _ (fun b hb => ?_) (fun δ => ?_)
      · have : B (f α) b = 0 := by
          by_contra h
          exact hb (hB α b h)
        simp [this]
      · rw [map_mul]; ring
  rw [key, Matrix.det_mul, Matrix.det_mul, ← RingHom.map_det, ← RingHom.map_det, Algebra.smul_def, map_mul]
  ring

theorem inv_tri {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (hM : IsUnit M) (w : Fin m → ℤ)
    (h : ∀ a b, M a b ≠ 0 → w a ≤ w b) (a b : Fin m) (hab : M⁻¹ a b ≠ 0) : w a ≤ w b := by
  obtain ⟨_⟩ := hM.nonempty_invertible
  have h1 : M.BlockTriangular w := fun i j hij => by
    by_contra h0
    exact absurd (h i j h0) (not_le.2 hij)
  have h2 := Matrix.blockTriangular_inv_of_blockTriangular h1
  by_contra h3
  exact hab (h2 (not_le.1 h3))

theorem inv_diag {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (hM : IsUnit M) (w : Fin m → ℤ)
    (hw : Function.Injective w) (h : ∀ a b, M a b ≠ 0 → w a ≤ w b) (a : Fin m) : M⁻¹ a a * M a a = 1 := by
  have h1 : (M⁻¹ * M) a a = 1 := by
    rw [Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det M).1 hM)]; simp
  rw [← h1, Matrix.mul_apply]
  symm
  refine Finset.sum_eq_single a (fun b _ hb => ?_) (by simp)
  by_contra h0
  exact hb (hw (le_antisymm (h _ _ (right_ne_zero_of_mul h0)) (inv_tri M hM w h _ _ (left_ne_zero_of_mul h0))))

theorem telescope (x : ℕ → ℂ) (p : ℕ) (ap : ℕ → ℕ) (h : ∀ a b, a ≤ b → b < p → ap b ≤ ap a) :
    ∏ i ∈ Finset.range p, (∏ a ∈ Finset.range (i + 1), x a) ^ (ap i - if i + 1 < p then ap (i + 1) else 0) =
      ∏ a ∈ Finset.range p, x a ^ ap a := by
  have key : ∀ r, r ≤ p → (∏ i ∈ Finset.range r, (∏ a ∈ Finset.range (i + 1), x a) ^
      (ap i - if i + 1 < p then ap (i + 1) else 0)) * (∏ a ∈ Finset.range r, x a) ^ (if r < p then ap r else 0) =
      ∏ a ∈ Finset.range r, x a ^ ap a := by
    intro r
    induction r with
    | zero => simp
    | succ r ih =>
      intro hr
      have hle : (if r + 1 < p then ap (r + 1) else 0) ≤ ap r := by
        split_ifs with h1
        · exact h _ _ (Nat.le_succ r) h1
        · exact Nat.zero_le _
      rw [Finset.prod_range_succ, mul_assoc, ← pow_add, Nat.sub_add_cancel hle, Finset.prod_range_succ x,
        Finset.prod_range_succ (fun a => x a ^ ap a), ← ih (by omega), if_pos (show r < p by omega), mul_pow,
        mul_assoc]
  simpa using key p le_rfl

theorem regroup (K U : ℕ → ℂ) (hU : ∀ j, U j ≠ 0) (p q n : ℕ) (hn : p + q ≤ n) (ap am : ℕ → ℕ) :
    (∏ a ∈ Finset.range p, (K a * (U a)⁻¹) ^ ap a) *
      ∏ a ∈ Finset.range q, ((K (p + a))⁻¹ * U (n - 1 - a)) ^ am a =
    (∏ a ∈ Finset.range (p + q), K a ^ (if a < p then (ap a : ℤ) else -(am (a - p) : ℤ))) *
      ∏ j ∈ Finset.range n, U j ^ (-(if j < p then (ap j : ℤ) else 0) +
        (if n - 1 - j < q then (am (n - 1 - j) : ℤ) else 0) + 0) := by
  have e1 : ∏ a ∈ Finset.range (p + q), K a ^ (if a < p then (ap a : ℤ) else -(am (a - p) : ℤ)) =
      (∏ a ∈ Finset.range p, K a ^ ap a) * ∏ a ∈ Finset.range q, (K (p + a))⁻¹ ^ am a := by
    rw [Finset.prod_range_add]
    congr 1
    · refine Finset.prod_congr rfl fun a ha => ?_
      rw [if_pos (Finset.mem_range.1 ha), zpow_natCast]
    · refine Finset.prod_congr rfl fun a _ => ?_
      rw [if_neg (by omega), Nat.add_sub_cancel_left, _root_.zpow_neg, zpow_natCast, inv_pow]
  have e2 : ∏ j ∈ Finset.range n, U j ^ (-(if j < p then (ap j : ℤ) else 0)) =
      ∏ a ∈ Finset.range p, (U a)⁻¹ ^ ap a := by
    symm
    rw [← Finset.prod_subset (Finset.range_subset_range.2 (show p ≤ n by omega))]
    · refine Finset.prod_congr rfl fun a ha => ?_
      rw [if_pos (Finset.mem_range.1 ha), _root_.zpow_neg, zpow_natCast, inv_pow]
    · intro a _ ha
      rw [if_neg (by simpa using ha)]; simp
  have e3 : ∏ j ∈ Finset.range n, U j ^ (if n - 1 - j < q then (am (n - 1 - j) : ℤ) else 0) =
      ∏ a ∈ Finset.range q, U (n - 1 - a) ^ am a := by
    symm
    rw [← Finset.prod_range_reflect _ n, ← Finset.prod_subset (Finset.range_subset_range.2 (show q ≤ n by omega))]
    · refine Finset.prod_congr rfl fun a ha => ?_
      have ha := Finset.mem_range.1 ha
      rw [show n - 1 - (n - 1 - a) = a by omega, if_pos ha, zpow_natCast]
    · intro a ha' ha
      have ha' := Finset.mem_range.1 ha'
      rw [show n - 1 - (n - 1 - a) = a by omega, if_neg (by simpa using ha)]; simp
  simp only [add_zero, zpow_add₀ (hU _), Finset.prod_mul_distrib, mul_pow, e1, e2, e3]
  ring

noncomputable def dg {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (a : ℕ) : ℂ :=
  if h : a < m then M ⟨a, h⟩ ⟨a, h⟩ else 1

theorem dg_fin {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (a : Fin m) : dg M a = M a a := by
  simp [dg]

theorem lo_tri {n : ℕ} {u : Matrix (Fin n) (Fin n) ℂ} (hu : GlobalTheory.Dec.IsLo u) (a b : Fin n) (h : u a b ≠ 0) :
    -((a : ℕ) : ℤ) ≤ -((b : ℕ) : ℤ) := by
  by_contra h0
  exact h (hu a b (by rw [Fin.lt_def]; omega))

theorem lo_diag {n : ℕ} {u : Matrix (Fin n) (Fin n) ℂ} (hu : IsUnit u ∧ GlobalTheory.Dec.IsLo u) (a : Fin n) :
    u⁻¹ a a * u a a = 1 :=
  inv_diag u hu.1 (fun a => -((a : ℕ) : ℤ)) (fun a b h => Fin.ext (by simpa using h)) (lo_tri hu.2) a

variable {D : D7} {m n : ℕ}

theorem fsub_minorPlus (ε : D.what₂.Tau → Fin m → Bool) (k : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ)
    (u : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (τ : D.what₂.Tau) (p s : ℕ) (hmn : m ≤ n) (hp : p ≤ m) (hs : s ≤ p)
    (hε : ∀ a, ε τ a = decide ((a : ℕ) < p))
    (hk : ∀ a b, k τ a b ≠ 0 → ((b : ℕ) < p → a ≤ b) ∧ (p ≤ (b : ℕ) → b ≤ a))
    (hu : IsUnit (u τ) ∧ GlobalTheory.Dec.IsLo (u τ)) :
    fsub ε k u (minorPlus τ s : PolF D m n) =
      (∏ a ∈ Finset.range s, (dg (k τ) a * (dg (u τ) a)⁻¹)) • (minorPlus τ s : PolF D m n) := by
  have hsm : s ≤ m := by omega
  have hsn : s ≤ n := by omega
  have hv : ∀ α β : Fin s, (varF τ β α : PolF D m n) =
      MvPolynomial.X (τ, Fin.castLE hsm β, Fin.castLE hsn α) := fun α β => by
    rw [varF, dite_eq_left ⟨by omega, by omega⟩]; rfl
  have hui := inv_tri (u τ) hu.1 _ (lo_tri hu.2)
  have key := det_subst (R := PolF D m n) (fun a b => MvPolynomial.X (τ, a, b)) (k τ) (u τ)⁻¹
    (Fin.castLE hsm) (Fin.castLE hsn) (Fin.castLE_injective _) (Fin.castLE_injective _)
    (fun a β h => by
      have := (hk _ _ h).1 (by simp; omega)
      rw [Fin.le_def] at this
      exact ⟨⟨a, by simp at this; omega⟩, rfl⟩)
    (fun α b h => by
      have := hui _ _ h
      exact ⟨⟨b, by simp at this; omega⟩, rfl⟩)
  rw [Matrix.det_of_upperTriangular (M := (k τ).submatrix _ _) (fun i j hij => by
      by_contra h
      have := (hk _ _ h).1 (by simp; omega)
      exact absurd hij (by simpa using this)),
    Matrix.det_of_lowerTriangular (((u τ)⁻¹).submatrix _ _) (fun i j hij => by
      by_contra h
      have := hui _ _ h
      exact absurd hij (by simpa using this)), ← Finset.prod_mul_distrib] at key
  simp only [minorPlus, hv]
  rw [AlgHom.map_det, Finset.prod_range]
  convert key using 2
  · ext1 α β
    have : ε τ (Fin.castLE hsm β) = true := by rw [hε]; simp; omega
    simp [fsub, this]
  · refine Finset.prod_congr rfl fun a _ => ?_
    rw [show dg (k τ) a = _ from dg_fin _ (Fin.castLE hsm a), show dg (u τ) a = _ from dg_fin _ (Fin.castLE hsn a),
      Matrix.submatrix_apply, Matrix.submatrix_apply, eq_inv_of_mul_eq_one_left (lo_diag hu _)]

theorem fsub_minorMinus (ε : D.what₂.Tau → Fin m → Bool) (k : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ)
    (u : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (τ : D.what₂.Tau) (p s : ℕ) (hmn : m ≤ n) (hs : p + s ≤ m)
    (hε : ∀ a, ε τ a = decide ((a : ℕ) < p)) (hk0 : IsUnit (k τ))
    (hk : ∀ a b, k τ a b ≠ 0 → ((b : ℕ) < p → a ≤ b) ∧ (p ≤ (b : ℕ) → b ≤ a))
    (hu : IsUnit (u τ) ∧ GlobalTheory.Dec.IsLo (u τ)) :
    fsub ε k u (minorMinus τ p s : PolF D m n) =
      (∏ a ∈ Finset.range s, ((dg (k τ) (p + a))⁻¹ * dg (u τ) (n - 1 - a))) • (minorMinus τ p s : PolF D m n) := by
  let e : Fin s → Fin m := fun β => ⟨p + β, by omega⟩
  let f : Fin s → Fin n := fun α => ⟨n - s + α, by omega⟩
  have hv : ∀ α β : Fin s, (varF τ (p + β) (n - s + α) : PolF D m n) =
      MvPolynomial.X (τ, e β, f α) := fun α β => by
    rw [varF, dite_eq_left ⟨by omega, by omega⟩]
  let w : Fin m → ℤ := fun a => if (a : ℕ) < p then ((a : ℕ) : ℤ) else 2 * m - ((a : ℕ) : ℤ)
  have hw : Function.Injective w := fun a b h => by
    simp only [w] at h
    apply Fin.ext
    split_ifs at h <;> omega
  have hkw : ∀ a b, k τ a b ≠ 0 → w a ≤ w b := fun a b h => by
    have := hk a b h
    simp only [w, Fin.le_def] at this ⊢
    split_ifs <;> omega
  have hki : ∀ β a, (k τ)⁻¹ (e β) a ≠ 0 → p ≤ a ∧ (a : ℕ) ≤ p + β := fun β a h => by
    have := inv_tri (k τ) hk0 _ hkw _ _ h
    simp only [w, e] at this
    split_ifs at this <;> omega
  have key := det_subst (R := PolF D m n) (fun a b => MvPolynomial.X (τ, a, b)) ((k τ)⁻¹)ᵀ (u τ)ᵀ
    e f (fun a b h => Fin.ext (by simpa [e] using h)) (fun a b h => Fin.ext (by simpa [f] using h))
    (fun a β h => by
      have := hki _ _ h
      exact ⟨⟨a - p, by omega⟩, Fin.ext (by simp only [e]; omega)⟩)
    (fun α b h => by
      have := lo_tri hu.2 _ _ h
      simp only [f] at this
      exact ⟨⟨b - (n - s), by omega⟩, Fin.ext (by simp only [f]; omega)⟩)
  rw [Matrix.det_of_upperTriangular (M := ((k τ)⁻¹)ᵀ.submatrix _ _) (fun i j hij => by
      by_contra h
      have := (hki _ _ h).2
      exact absurd hij (by simpa [e] using this)),
    Matrix.det_of_upperTriangular (M := (u τ)ᵀ.submatrix _ _) (fun i j hij => by
      by_contra h
      have := lo_tri hu.2 _ _ h
      exact absurd hij (by simpa [f] using this))] at key
  simp only [minorMinus, hv]
  rw [AlgHom.map_det, Finset.prod_mul_distrib, ← Finset.prod_range_reflect (fun a => dg (u τ) (n - 1 - a)),
    Finset.prod_range, Finset.prod_range]
  convert key using 2
  · ext1 α β
    have : ε τ (e β) = false := by rw [hε]; simp [e]
    simp [fsub, this]
  · congr 1
    · refine Finset.prod_congr rfl fun a _ => ?_
      rw [show dg (k τ) (p + a) = _ from dg_fin _ (e a), Matrix.submatrix_apply, Matrix.transpose_apply,
        eq_inv_of_mul_eq_one_left (inv_diag _ hk0 w hw hkw _)]
    · refine Finset.prod_congr rfl fun a _ => ?_
      rw [show n - 1 - (s - 1 - a) = n - s + a by omega]
      exact dg_fin _ (f a)

theorem map_prod_pow {R : Type} [CommRing R] [Algebra ℂ R] (φ : R →ₐ[ℂ] R) (S : Finset ℕ) (x : ℕ → R) (c : ℕ → ℂ)
    (d : ℕ → ℕ) (h : ∀ i ∈ S, φ (x i) = c i • x i) :
    φ (∏ i ∈ S, x i ^ d i) = (∏ i ∈ S, c i ^ d i) • ∏ i ∈ S, x i ^ d i := by
  rw [map_prod, ← Finset.prod_smul]
  exact Finset.prod_congr rfl fun i hi => by rw [map_pow, h i hi, smul_pow]

theorem fsub_delta : ∀ (D : D7) (m n : ℕ) (ε : D.what₂.Tau → Fin m → Bool) (p q : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ), m ≤ n → (∀ τ, p τ + q τ = m) → (∀ τ a, ε τ a = decide ((a : ℕ) < p τ)) → (∀ τ a b, a ≤ b → b < p τ → ap τ b ≤ ap τ a) → (∀ τ a b, a ≤ b → b < q τ → am τ b ≤ am τ a) → ∀ (k : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) (u : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ), (∀ τ, k τ ∈ GlobalTheory.Dec.KC (ε τ)) → (∀ τ a b, k τ a b ≠ 0 → ((b : ℕ) < p τ → a ≤ b) ∧ (p τ ≤ (b : ℕ) → b ≤ a)) → (∀ τ, IsUnit (u τ) ∧ GlobalTheory.Dec.IsLo (u τ)) → fsub ε k u (delta p q ap am : PolF D m n) = (∏ τ, (∏ a : Fin m, k τ a a ^ (if (a : ℕ) < p τ then (ap τ a : ℤ) else -(am τ (a - p τ) : ℤ))) * ∏ j : Fin n, u τ j j ^ wtU (p τ) (q τ) (ap τ) (am τ) 0 j) • (delta p q ap am : PolF D m n) := by
  intro D m n ε p q ap am hmn hpq hε hap ham k u hk0 hk hu
  rw [delta, map_prod, ← Finset.prod_smul]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have hm := hpq τ
  rw [deltaAt, map_mul,
    map_prod_pow _ _ (fun i => minorPlus τ (i + 1)) _ _ (fun i hi =>
      fsub_minorPlus ε k u τ (p τ) (i + 1) hmn (by omega) (Finset.mem_range.1 hi) (hε τ) (hk τ) (hu τ)),
    map_prod_pow _ _ (fun i => minorMinus τ (p τ) (i + 1)) _ _ (fun i hi =>
      fsub_minorMinus ε k u τ (p τ) (i + 1) hmn (by have := Finset.mem_range.1 hi; omega) (hε τ) (hk0 τ).1
        (hk τ) (hu τ)),
    smul_mul_smul_comm, telescope _ _ _ (hap τ), telescope _ _ _ (ham τ),
    regroup (dg (k τ)) (dg (u τ)) (fun j => by
      unfold dg
      split_ifs
      · exact right_ne_zero_of_mul_eq_one (lo_diag (hu τ) _)
      · exact one_ne_zero) _ _ n (by omega), hm, Finset.prod_range, Finset.prod_range]
  simp only [dg_fin, wtU]

end GlobalTheory.JointHarm.DeltaEig
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NEqAndIsClosed
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BesselClosed

open GlobalTheory.BesselCompare (mt_mul mt_one hA_coeff closure_prop spanA)

variable {D : D7}

def spanLt (B : HSp D) {ρ : ℕ} (e : Fin ρ → B.V) (k : ℕ) : Submodule (AE D) (Fin B.rank → AE D) where
  carrier := {v | ∃ c : Fin ρ → AE D, (∀ l : Fin ρ, k ≤ l.1 → c l = 0) ∧ v = ∑ l, c l • vecA B (e l)}
  zero_mem' := ⟨0, fun _ _ => rfl, by simp⟩
  add_mem' := by
    rintro _ _ ⟨c, hc, rfl⟩ ⟨c', hc', rfl⟩
    exact ⟨c + c', fun l hl => by simp [hc l hl, hc' l hl], by simp [add_smul, Finset.sum_add_distrib]⟩
  smul_mem' := by
    rintro a _ ⟨c, hc, rfl⟩
    exact ⟨a • c, fun l hl => by simp [hc l hl], by simp [Finset.smul_sum, smul_smul]⟩

variable {B : HSp D} {ρ : ℕ} {e : Fin ρ → B.V}

theorem spanLt_mono {k k' : ℕ} (h : k ≤ k') : spanLt B e k ≤ spanLt B e k' := by
  rintro _ ⟨c, hc, rfl⟩
  exact ⟨c, fun l hl => hc l (h.trans hl), rfl⟩

theorem vec_mem_spanLt {k : ℕ} {l : Fin ρ} (h : l.1 < k) : vecA B (e l) ∈ spanLt B e k := by
  classical
  refine ⟨Pi.single l 1, fun j hj => Pi.single_eq_of_ne (fun e => by subst e; omega) _, ?_⟩
  rw [Finset.sum_eq_single l] <;> simp +contextual

theorem mulVec_mem_spanLt {k : ℕ} (M : Matrix (Fin B.rank) (Fin B.rank) (AE D))
    (hM : ∀ l : Fin ρ, l.1 < k → M.mulVec (vecA B (e l)) - vecA B (e l) ∈ spanLt B e l.1)
    {v} (hv : v ∈ spanLt B e k) : M.mulVec v ∈ spanLt B e k := by
  obtain ⟨c, hc, rfl⟩ := hv
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← Matrix.mulVecLin_apply, map_sum]
  refine Submodule.sum_mem _ fun l _ => ?_
  rcases lt_or_ge l.1 k with hl | hl
  · rw [map_smul]
    refine Submodule.smul_mem _ _ ?_
    have := add_mem (spanLt_mono hl.le (hM l hl)) (vec_mem_spanLt (B := B) (e := e) hl)
    rwa [sub_add_cancel] at this
  · simp [hc l hl]

theorem mem_NS_iff {n : GA D B} : n ∈ GlobalTheory.BesselCompare.NS B e ↔
    (∀ i : Fin ρ, actV B n (e i) - vecA B (e i) ∈ spanLt B e i.1) ∧
      ∀ x : B.V, (∀ i, B.hD x (e i) = 0) → actV B n x - vecA B x ∈ spanLt B e ρ := by
  refine and_congr (forall_congr' fun i => exists_congr fun c => and_congr Iff.rfl sub_eq_iff_eq_add'.symm)
    (forall_congr' fun x => forall_congr' fun _ => exists_congr fun c => ?_)
  rw [sub_eq_iff_eq_add']
  exact ⟨fun h => ⟨fun l hl => absurd l.2 (by omega), h⟩, fun h => h.2⟩

theorem closure_flag (n : GA D B) (hn : n ∈ Subgroup.closure (GlobalTheory.BesselCompare.NS B e)) :
    ∀ i : Fin ρ, actV B n (e i) - vecA B (e i) ∈ spanLt B e i.1 := by
  induction hn using Subgroup.closure_induction'' with
  | one => intro i; simp [actV, mt_one]
  | mem g hg => exact (mem_NS_iff.1 hg).1
  | inv_mem g hg =>
    intro i
    induction i using WellFoundedLT.induction with
    | ind i ih =>
      have h := mulVec_mem_spanLt (mt B g⁻¹) (fun l hl => ih l hl) ((mem_NS_iff.1 hg).1 i)
      rw [Matrix.mulVec_sub, actV, mulVec_inv_cancel] at h
      have := neg_mem h
      rwa [neg_sub] at this
  | mul g h _ _ ihg ihh =>
    intro i
    have := add_mem (mulVec_mem_spanLt (mt B g) (fun l _ => ihg l) (ihh i)) (ihg i)
    rwa [Matrix.mulVec_sub, actV, ← mulVec_mul, actV, sub_add_sub_cancel] at this

theorem closure_NS : (Subgroup.closure (GlobalTheory.BesselCompare.NS B e) : Set (GA D B)) = GlobalTheory.BesselCompare.NS B e := by
  refine subset_antisymm (fun n hn => mem_NS_iff.2 ⟨closure_flag n hn, fun x hx => ?_⟩) Subgroup.subset_closure
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 ((closure_prop B e n hn).2 x hx)
  exact ⟨a, fun l hl => absurd l.2 (by omega), ha.symm⟩

theorem mem_spanLt_iff {f : Fin ρ → B.V} (ef : ∀ i j, B.hD (e i) (f j) = if i = j then 1 else 0) {k : ℕ} {v} :
    v ∈ spanLt B e k ↔ (∀ l : Fin ρ, k ≤ l.1 → hA B v (vecA B (f l)) = 0) ∧
      v = ∑ l, hA B v (vecA B (f l)) • vecA B (e l) := by
  refine ⟨?_, fun h => ⟨_, h⟩⟩
  rintro ⟨c, hc, rfl⟩
  simp only [hA_coeff B e f ef]
  exact ⟨hc, trivial⟩

theorem isClosed_NS {f : Fin ρ → B.V} (ef : ∀ i j, B.hD (e i) (f j) = if i = j then 1 else 0) :
    IsClosed (GlobalTheory.BesselCompare.NS B e) := by
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField D.host.F
  obtain ⟨e0⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E) (AF D.host.F)
  have : T2Space (AE D) := e0.isEmbedding.t2Space
  have : IsTopologicalRing (AE D) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing
  have hm : Continuous (fun k : GA D B => mt B k) := Units.continuous_val.comp continuous_subtype_val
  have hh : ∀ y, Continuous fun v => hA B v y := fun y =>
    continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j)
  have hc : ∀ k, IsClosed (spanLt B e k : Set (Fin B.rank → AE D)) := fun k => by
    have : (spanLt B e k : Set (Fin B.rank → AE D)) =
        (⋂ l : Fin ρ, ⋂ _ : k ≤ l.1, {v | hA B v (vecA B (f l)) = 0}) ∩
          {v | v = ∑ l, hA B v (vecA B (f l)) • vecA B (e l)} := by
      ext v
      simp only [SetLike.mem_coe, mem_spanLt_iff ef, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
    rw [this]
    exact (isClosed_iInter fun l => isClosed_iInter fun _ => isClosed_eq (hh _) continuous_const).inter
      (isClosed_eq continuous_id (continuous_finsetSum _ fun l _ => (hh _).smul continuous_const))
  have : IsTopologicalAddGroup (AE D) := IsTopologicalRing.to_topologicalAddGroup
  have : ContinuousSub (AE D) := IsTopologicalAddGroup.to_continuousSub
  have ha : ∀ x, Continuous fun n : GA D B => actV B n x - vecA B x := fun x =>
    continuous_pi fun j => ((continuous_apply j).comp (hm.matrix_mulVec continuous_const)).sub continuous_const
  have : GlobalTheory.BesselCompare.NS B e =
      (⋂ i : Fin ρ, (fun n => actV B n (e i) - vecA B (e i)) ⁻¹' spanLt B e i.1) ∩
        ⋂ x : B.V, ⋂ _ : ∀ i, B.hD x (e i) = 0, (fun n => actV B n x - vecA B x) ⁻¹' spanLt B e ρ := by
    ext n
    simp only [mem_NS_iff, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
  rw [this]
  exact (isClosed_iInter fun i => (hc _).preimage (ha _)).inter
    (isClosed_iInter fun x => isClosed_iInter fun _ => (hc _).preimage (ha _))

theorem N_eq_and_isClosed : ∀ (D : D7) (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : BesselDatum A B ι), (d.N : Set (GA D B)) = d.NSet ∧ IsClosed (d.N : Set (GA D B)) := by
  intro D A B ι d
  have h : (d.N : Set (GA D B)) = GlobalTheory.BesselCompare.NS B d.e := closure_NS
  exact ⟨h, h ▸ isClosed_NS d.ef⟩

end GlobalTheory.BesselClosed

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AllPositiveModelFiniteDimensionalCompactType
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AllPositiveModelFiniteDimensionalCompactType
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.Chain GlobalTheory.CompactHowe Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompactModel

theorem mem_Kset_of_mem_UJset {k : ℕ} {g : Matrix (Fin k) (Fin k) ℂ} (hg : g ∈ UJset (allPos k)) :
    g ∈ Formalism.REAL.Kset (allPos k) := by
  have hJ : Formalism.REAL.Jm (allPos k) = 1 := by
    simp [Formalism.REAL.Jm, allPos]
  have h : gᴴ * Formalism.REAL.Jm (allPos k) * g = Formalism.REAL.Jm (allPos k) := hg
  rw [hJ, Matrix.mul_one] at h
  refine ⟨Matrix.mem_unitaryGroup_iff'.2 h, ?_⟩
  rw [hJ, Matrix.mul_one, Matrix.one_mul]

theorem list_prod_conj {n : ℕ} {g : Matrix (Fin n) (Fin n) ℂ} (hg : IsUnit g)
    (l : List (Matrix (Fin n) (Fin n) ℂ)) : (l.map fun x => g⁻¹ * x * g).prod = g⁻¹ * l.prod * g := by
  have hd : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det g).1 hg
  induction l with
  | nil => simp [Matrix.nonsing_inv_mul _ hd]
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, List.prod_cons, ih]
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ hd]

theorem smoothVec_stable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsURepOn (UJset ε) σ) {P G : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P)
    (h : Pᴴ * Formalism.REAL.Jm ε * P = G) {u : Matrix (Fin n) (Fin n) ℂ} (hu : u ∈ UJset ε) {w : H}
    (hw : SmoothVec {X | Xᴴ * G + G * X = 0} (fun g => σ (P * g * P⁻¹)) w) :
    SmoothVec {X | Xᴴ * G + G * X = 0} (fun g => σ (P * g * P⁻¹)) (σ u w) := by
  obtain ⟨⟨h1, hmul⟩, -, -⟩ := hσ
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have hJ : IsUnit (Formalism.REAL.Jm ε) := IsUnit.of_mul_eq_one _ (Formalism.REAL.Jm_mul_self ε)
  have hG : IsUnit G := by
    rw [← h]
    exact (((Matrix.isUnit_conjTranspose _).2 hP).mul hJ).mul hP
  have hu' : uᴴ * Formalism.REAL.Jm ε * u = Formalism.REAL.Jm ε := hu
  have huu : IsUnit u := by
    have : IsUnit (uᴴ * Formalism.REAL.Jm ε * u) := by rw [hu']; exact hJ
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_mul] at this
    exact (Matrix.isUnit_iff_isUnit_det u).2 (isUnit_of_mul_isUnit_right this)
  set g : Matrix (Fin n) (Fin n) ℂ := P⁻¹ * u * P with hgdef
  have hPi : IsUnit P⁻¹ := Matrix.isUnit_nonsing_inv_iff.2 hP
  have hg : IsUnit g := (hPi.mul huu).mul hP
  have hgd : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det g).1 hg
  have hPg : P * g = u * P := by
    rw [hgdef, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hd]
  have hug : u = P * g * P⁻¹ := by
    rw [hPg, Matrix.mul_nonsing_inv_cancel_right _ _ hd]
  have hgG : gᴴ * G * g = G := by
    calc gᴴ * G * g = (P * g)ᴴ * Formalism.REAL.Jm ε * (P * g) := by
          rw [← h]; simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = Pᴴ * (uᴴ * Formalism.REAL.Jm ε * u) * P := by
          rw [hPg]; simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = G := by rw [hu', h]
  clear_value g
  intro k Xs hX
  have hY : ∀ i, (g⁻¹ * Xs i * g)ᴴ * G + G * (g⁻¹ * Xs i * g) = 0 := by
    intro i
    have hXi : (Xs i)ᴴ * G + G * Xs i = 0 := hX i
    have e1 : G * g⁻¹ = gᴴ * G := by
      conv_lhs => rw [← hgG]
      rw [Matrix.mul_nonsing_inv_cancel_right _ _ hgd]
    have e2 : (g⁻¹)ᴴ * G = G * g := by
      conv_lhs => rw [← hgG]
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← conjTranspose_mul, Matrix.mul_nonsing_inv _ hgd]
      simp
    calc (g⁻¹ * Xs i * g)ᴴ * G + G * (g⁻¹ * Xs i * g)
        = gᴴ * (Xs i)ᴴ * ((g⁻¹)ᴴ * G) + (G * g⁻¹) * Xs i * g := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = gᴴ * ((Xs i)ᴴ * G + G * Xs i) * g := by
          rw [e1, e2]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = 0 := by rw [hXi]; simp
  have hs := hw k (fun i => g⁻¹ * Xs i * g) hY
  have hs2 := ((σ u).restrictScalars ℝ).contDiff.comp hs
  convert hs2 using 1
  funext t
  have hmem : ∀ Zs : Fin k → Matrix (Fin n) (Fin n) ℂ, (∀ i, (Zs i)ᴴ * G + G * Zs i = 0) →
      P * (List.ofFn fun i => NormedSpace.exp (t i • Zs i)).prod * P⁻¹ ∈ UJset ε := fun Zs hZ => by
    refine GlobalTheory.GardingVec.conj_mem hP h (GlobalTheory.GardingVec.list_prod_mem _ fun a ha => ?_)
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 ha
    exact GlobalTheory.GardingVec.exp_mem hG (hZ i) _
  have e3 : (List.ofFn fun i => NormedSpace.exp (t i • (g⁻¹ * Xs i * g))).prod
      = g⁻¹ * (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod * g := by
    rw [← list_prod_conj hg, List.map_ofFn]
    congr 2
    funext i
    rw [Function.comp_apply, ← Matrix.exp_conj' _ _ hg]
    simp
  have a := hmul _ (hmem Xs hX) _ hu
  have b := hmul _ hu _ (hmem _ hY)
  have e4 : P * (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod * P⁻¹ * u
      = u * (P * (List.ofFn fun i => NormedSpace.exp (t i • (g⁻¹ * Xs i * g))).prod * P⁻¹) := by
    rw [e3, hug]
    simp only [Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul_cancel_left _ _ hd, Matrix.nonsing_inv_mul_cancel_left _ _ hd,
      Matrix.mul_nonsing_inv_cancel_left _ _ hgd]
  rw [e4, b] at a
  exact (congrArg (fun f => f w) a).symm

theorem model_allPos : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau),
    M.ε τ = allPos V.rank → FiniteDimensional ℂ (M.H τ) ∧ M.sm τ = ⊤ ∧
      IsURepOn (UJset (allPos V.rank)) (M.σ τ) ∧
      IsKTypeOf (allPos V.rank) (M.σ τ) (Formalism.QuantumDeterminants.lowK (allPos V.rank) (M.lam τ)) ⊤ := by
  intro D V S M τ hε
  obtain ⟨-, -, hrep, hirr, -, ⟨T, hT⟩, -⟩ := M.ds τ
  have hT' := hT
  rw [hε] at hT'
  have hTtop : T = ⊤ := by
    obtain ⟨hfd, hst, -, ⟨v, hv, hv0, -⟩, -⟩ := hT'
    refine (hirr T T.closed_of_finiteDimensional fun g hg => hst g ?_).resolve_left ?_
    · rw [hε] at hg
      exact mem_Kset_of_mem_UJset hg
    · exact (Submodule.ne_bot_iff _).2 ⟨v, hv, hv0⟩
  subst hTtop
  have hfd : FiniteDimensional ℂ (M.H τ) := by
    have := hT'.1
    exact Module.Finite.equiv Submodule.topEquiv
  refine ⟨hfd, ?_, hε ▸ hrep, hT'⟩
  refine (hirr (M.sm τ) (M.sm τ).closed_of_finiteDimensional fun u hu v hv => ?_).resolve_left
    (GlobalTheory.GardingVec.sm_ne_bot D V S M τ)
  have hle : (M.sm τ).map (M.σ τ u : M.H τ →ₗ[ℂ] M.H τ) ≤ M.sm τ := by
    refine (Submodule.map_span_le _ _ _).2 fun w hw => Submodule.subset_span ?_
    exact smoothVec_stable hrep (M.fr_unit τ) (M.fr_gram τ) hu hw
  exact hle ⟨v, hv, rfl⟩

end GlobalTheory.CompactModel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AllPositiveModelFiniteDimensionalCompactTypeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.Chain GlobalTheory.CompactHowe Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.allPositive_model_finiteDimensional_compactType : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau), M.ε τ = allPos V.rank → FiniteDimensional ℂ (M.H τ) ∧ M.sm τ = ⊤ ∧ IsURepOn (UJset (allPos V.rank)) (M.σ τ) ∧ IsKTypeOf (allPos V.rank) (M.σ τ) (Formalism.QuantumDeterminants.lowK (allPos V.rank) (M.lam τ)) ⊤ := by
  first | exact @GlobalTheory.CompactModel.model_allPos | exact GlobalTheory.CompactModel.model_allPos | (intros; apply GlobalTheory.CompactModel.model_allPos <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PostOnSumMemRange
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GoodProjLift

theorem exists_factor {U H X : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup H] [Module ℂ H]
    [AddCommGroup X] [Module ℂ X] (e : H →ₗ[ℂ] X) (he : Function.Injective e) (f : U →ₗ[ℂ] X)
    (hf : ∀ x, f x ∈ LinearMap.range e) : ∃ g : U →ₗ[ℂ] H, ∀ x, e (g x) = f x := by
  refine ⟨(LinearEquiv.ofInjective e he).symm.toLinearMap ∘ₗ f.codRestrict _ hf, fun x => ?_⟩
  have h := (LinearEquiv.ofInjective e he).apply_symm_apply (f.codRestrict _ hf x)
  exact congrArg Subtype.val h

theorem postOn_sum_smul {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) {G : Type} [Fintype G]
    (c : G → ℂ) (L : G → (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (T : MMap M) :
    postOn M (∑ g, c g • L g) T = ∑ g, c g • postOn M (L g) T := by
  ext v h
  simp [postOn_apply, LinearMap.sum_apply]

theorem postOn_sum_mem_range {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) {G : Type} [Fintype G]
    {H : Type} [AddCommGroup H] [Module ℂ H] (e : H →ₗ[ℂ] MMap M)
    (c : G → ℂ) (L : G → (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (a : G → H →ₗ[ℂ] H)
    (ha : ∀ g y, e (a g y) = postOn M (L g) (e y)) {T : MMap M} (hT : T ∈ LinearMap.range e) :
    postOn M (∑ g, c g • L g) T ∈ LinearMap.range e := by
  obtain ⟨y, rfl⟩ := hT
  refine ⟨∑ g, c g • a g y, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [postOn_sum_smul, map_sum]
  exact Finset.sum_congr rfl fun g _ => by rw [map_smul, ha]

theorem is_inj {X : Type} [AddCommGroup X] [Module ℂ X] {M : HMod X} {V : Submodule ℂ X} {ip : X → X → ℂ}
    (h : M.Is V ip) : Function.Injective M.e := h.1

theorem is_range {X : Type} [AddCommGroup X] [Module ℂ X] {M : HMod X} {V : Submodule ℂ X} {ip : X → X → ℂ}
    (h : M.Is V ip) : LinearMap.range M.e = V := h.2.1

theorem exists_factor_hmod {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {G : Type} [Fintype G]
    {U : Type} [AddCommGroup U] [Module ℂ U] {H : HMod (MMap M)} {W : Submodule ℂ (MMap M)}
    {ip : MMap M → MMap M → ℂ} (hH : H.Is W ip)
    (c : G → ℂ) {L : G → (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)} {a : G → H.H →ₗ[ℂ] H.H}
    (ha : ∀ g y, H.e (a g y) = postOn M (L g) (H.e y)) (f : U →ₗ[ℂ] MMap M) (hf : ∀ x, f x ∈ W) :
    ∃ th : U →ₗ[ℂ] H.H, ∀ x, H.e (th x) = postOn M (∑ g, c g • L g) (f x) :=
  exists_factor _ (is_inj hH) (postOn M (∑ g, c g • L g) ∘ₗ f) fun x =>
    postOn_sum_mem_range M H.e c L a ha (by rw [is_range hH]; exact hf x)


set_option maxHeartbeats 1000000 in
theorem exists_thG : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → R.thP_thF_mem → ∃ th, ({ R with thG := th } : RealDat D A Ks).thP_thG := by
  intro D G _ _ Pl0 T A Ks _ _ _ R _ _ hM hF
  have key : ∀ i t, ∃ th : (R.HV i t).H →ₗ[ℂ] (R.HW i (sg0 D A)).H,
      ∀ x, (R.HW i (sg0 D A)).e (th x) = postOn _ (R.eWf i (sg0 D A)) (R.thF i t x) := fun i t =>
    exists_factor_hmod (hM.HW i (sg0 D A)) (RealDat.eC (A := A) (sg0 D A)) (hM.gW i (sg0 D A)) (R.thF i t) (hF i t)
  choose th hth using key
  exact ⟨th, hth⟩

end GlobalTheory.GoodProjLift
end
