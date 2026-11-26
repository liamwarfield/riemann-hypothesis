module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHomSpaceDualIsotropicMiddleDecomposition
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RedMFrMapAdjZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientHeightLowerBoundShortIsotropicVector
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentApproximation.AddDense

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScalarOfComm
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec KMap maxCpt rep_mem_kFin)
open scoped TensorProduct InnerProductSpace Classical
open GlobalTheory.Chain.IoLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Chain.IoLift.Scal

variable {ι : Type} [Fintype ι] {K : ι → Type} [∀ i, AddCommGroup (K i)] [∀ i, Module ℂ (K i)]

def tform (w : ∀ i, Module.Dual ℂ (K i)) : (⨂[ℂ] i, K i) →ₗ[ℂ] ℂ := GlobalTheory.MultilinearContraction.prodForm w

theorem tform_tprod (w : ∀ i, Module.Dual ℂ (K i)) (v : ∀ i, K i) :
    tform w (PiTensorProduct.tprod ℂ v) = ∏ i, w i (v i) := by
  exact GlobalTheory.MultilinearContraction.prodForm_tprod w v

theorem eq_of_tform {t t' : ⨂[ℂ] i, K i} (h : ∀ w, tform w t = tform w t') : t = t' := by
  let b := fun i => Module.Basis.ofVectorSpace ℂ (K i)
  let B := Basis.piTensorProduct b
  refine B.ext_elem fun p => ?_
  have : B.coord p = tform fun i => (b i).coord (p i) := by
    ext v
    simp [tform_tprod, B, Basis.piTensorProduct_repr_tprod_apply]
  have h2 := h fun i => (b i).coord (p i)
  rw [← this] at h2
  simpa using h2

def ctrM (i : ι) (w : ∀ i, Module.Dual ℂ (K i)) : (Π j, K j) →ₘₗ[ℂ] K i :=
  GlobalTheory.MultilinearContraction.contractMultilinear w i

def ctr (i : ι) (w : ∀ i, Module.Dual ℂ (K i)) : (⨂[ℂ] i, K i) →ₗ[ℂ] K i :=
  PiTensorProduct.lift (ctrM i w)

theorem ctr_tprod (i : ι) (w : ∀ i, Module.Dual ℂ (K i)) (v : ∀ i, K i) :
    ctr i w (PiTensorProduct.tprod ℂ v) = (∏ j ∈ Finset.univ.erase i, w j (v j)) • v i := by
  simp [ctr, ctrM]

theorem ctr_mapFactor (i : ι) (w : ∀ i, Module.Dual ℂ (K i)) (f : Module.End ℂ (K i)) (t : ⨂[ℂ] i, K i) :
    ctr i w (intersection_update_fsHerm_neg_one i f t) = f (ctr i w t) := by
  have : ctr i w ∘ₗ intersection_update_fsHerm_neg_one i f = f ∘ₗ ctr i w := by
    ext v
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, position_tprod, ctr_tprod,
      Function.update_self, map_smul]
    congr 1
    exact Finset.prod_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  exact LinearMap.congr_fun this t

theorem tform_eq (i : ι) (w : ∀ i, Module.Dual ℂ (K i)) (t : ⨂[ℂ] i, K i) :
    tform w t = w i (ctr i w t) := by
  have : tform w = w i ∘ₗ ctr i w := by
    ext v
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, tform_tprod, ctr_tprod,
      map_smul, smul_eq_mul]
    rw [Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  exact LinearMap.congr_fun this t

theorem comm_mapFactor_of_absIrr {G : Type} (i : ι) (a : G → Module.End ℂ (K i)) (ha : AbsIrr a)
    (Φ : Module.End ℂ (⨂[ℂ] i, K i)) (h : ∀ g, Φ ∘ₗ intersection_update_fsHerm_neg_one i (a g) = intersection_update_fsHerm_neg_one i (a g) ∘ₗ Φ)
    (f : Module.End ℂ (K i)) (x : ∀ i, K i) :
    Φ (intersection_update_fsHerm_neg_one i f (PiTensorProduct.tprod ℂ x)) = intersection_update_fsHerm_neg_one i f (Φ (PiTensorProduct.tprod ℂ x)) := by
  refine eq_of_tform fun w => ?_
  rw [tform_eq i, tform_eq i, ctr_mapFactor]
  congr 1
  let T : Module.End ℂ (K i) :=
    ctr i w ∘ₗ Φ ∘ₗ (PiTensorProduct.tprod ℂ (s := K)).toLinearMap x i
  have hT : ∀ z, T z = ctr i w (Φ (PiTensorProduct.tprod ℂ (Function.update x i z))) := fun z => rfl
  obtain ⟨c, hc⟩ := ha.2 T (fun g => by
    ext z
    have := LinearMap.congr_fun (h g) (PiTensorProduct.tprod ℂ (Function.update x i z))
    simp only [LinearMap.comp_apply, position_tprod, Function.update_self, Function.update_idem] at this
    simp only [LinearMap.comp_apply, hT, this, ctr_mapFactor])
  have h1 := hT (x i)
  rw [Function.update_eq_self] at h1
  rw [position_tprod, ← hT, ← h1, hc]
  simp

theorem comm_map (Φ : Module.End ℂ (⨂[ℂ] i, K i))
    (h : ∀ i (f : Module.End ℂ (K i)), Φ ∘ₗ intersection_update_fsHerm_neg_one i f = intersection_update_fsHerm_neg_one i f ∘ₗ Φ) (f : ∀ i, Module.End ℂ (K i)) :
    Φ ∘ₗ PiTensorProduct.map f = PiTensorProduct.map f ∘ₗ Φ := by
  have key : ∀ s : Finset ι,
      Φ ∘ₗ PiTensorProduct.map (fun i => if i ∈ s then f i else LinearMap.id) =
        PiTensorProduct.map (fun i => if i ∈ s then f i else LinearMap.id) ∘ₗ Φ := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      have : PiTensorProduct.map (fun j => if j ∈ insert i s then f j else LinearMap.id) =
          intersection_update_fsHerm_neg_one i (f i) ∘ₗ PiTensorProduct.map (fun i => if i ∈ s then f i else LinearMap.id) := by
        ext v
        simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, PiTensorProduct.map_tprod,
          position_tprod]
        congr 1
        funext j
        by_cases hj : j = i
        · subst hj; simp [hi]
        · simp [hj]
      rw [this, ← LinearMap.comp_assoc, h, LinearMap.comp_assoc, ih, LinearMap.comp_assoc]
  simpa using key Finset.univ

theorem scalar_of_comm (ι : Type) [Fintype ι] (K : ι → Type) [∀ i, AddCommGroup (K i)] [∀ i, Module ℂ (K i)]
    (G : ι → Type) (a : ∀ i, G i → Module.End ℂ (K i)) (ha : ∀ i, AbsIrr (a i))
    (Φ : Module.End ℂ (⨂[ℂ] i, K i)) (h : ∀ i g, Φ ∘ₗ intersection_update_fsHerm_neg_one i (a i g) = intersection_update_fsHerm_neg_one i (a i g) ∘ₗ Φ) :
    ∃ c : ℂ, Φ = c • LinearMap.id := by
  by_cases hn : ∀ i, ∃ e : K i, e ≠ 0
  · choose e he using hn
    have : ∀ i, ∃ w : Module.Dual ℂ (K i), w (e i) = 1 := fun i =>
      Module.Projective.exists_dual_eq_one ℂ (he i)
    choose w hw using this
    refine ⟨tform w (Φ (PiTensorProduct.tprod ℂ e)), ?_⟩
    ext x
    have hc := comm_map Φ (fun i f => by
      ext y
      exact comm_mapFactor_of_absIrr i (a i) (ha i) Φ (h i) f y) (fun i => (w i).smulRight (x i))
    have hm : PiTensorProduct.map (fun i => (w i).smulRight (x i)) =
        (tform w).smulRight (PiTensorProduct.tprod ℂ x) := by
      ext v
      simp [tform_tprod, MultilinearMap.map_smul_univ]
    have := LinearMap.congr_fun hc (PiTensorProduct.tprod ℂ e)
    rw [hm] at this
    simpa [tform_tprod, hw] using this
  · push Not at hn
    obtain ⟨i, hi⟩ := hn
    refine ⟨0, ?_⟩
    ext x
    have : PiTensorProduct.tprod ℂ x = 0 := MultilinearMap.map_coord_zero _ i (hi _)
    simp [this]

end GlobalTheory.Chain.IoLift.Scal

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOnMulRight
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec KMap maxCpt rep_mem_kFin)
open scoped TensorProduct InnerProductSpace Classical
open GlobalTheory.Chain.IoLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.IoLift.AvgLift

private theorem isFundamentalDomain_preimage_mul_right' {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (Γ : Subgroup G) (μ : Measure G) [μ.IsMulRightInvariant] {𝓕 : Set G}
    (h : IsFundamentalDomain Γ 𝓕 μ) (a : G) : IsFundamentalDomain Γ ((fun g => g * a) ⁻¹' 𝓕) μ :=
  h.preimage_of_equiv (measurePreserving_mul_right μ a).quasiMeasurePreserving Function.bijective_id
    (fun γ x => mul_assoc (γ : G) x a)

theorem integrableOn_mul_right {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (Γ : Subgroup G)
    [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] {𝓕 : Set G}
    (h : IsFundamentalDomain Γ 𝓕 μ) {Φ : G → ℂ} (hΦ : ∀ γ ∈ Γ, ∀ g, Φ (γ * g) = Φ g) (hi : IntegrableOn Φ 𝓕 μ)
    (a : G) : IntegrableOn (fun g => Φ (g * a)) 𝓕 μ := by
  have hinv : ∀ (γ : Γ) (x : G), (fun g => Φ (g * a)) (γ • x) = (fun g => Φ (g * a)) x := by
    intro γ x
    show Φ ((γ : G) * x * a) = Φ (x * a)
    rw [mul_assoc]
    exact hΦ γ γ.2 (x * a)
  rw [h.integrableOn_iff (isFundamentalDomain_preimage_mul_right' Γ μ h a) hinv]
  exact ((measurePreserving_mul_right μ a).integrableOn_comp_preimage
    (MeasurableEquiv.mulRight a).measurableEmbedding).mpr hi

private theorem setIntegral_fd_comp_mul_right_of_invariant {G E : Type} [Group G] [MeasurableSpace G] [MeasurableMul G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (Γ : Subgroup G) [Countable Γ] (μ : Measure G)
    [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] {𝓕 : Set G} (h : IsFundamentalDomain Γ 𝓕 μ)
    {Φ : G → E} (hΦ : ∀ γ ∈ Γ, ∀ g, Φ (γ * g) = Φ g) (a : G) :
    ∫ g in 𝓕, Φ (g * a) ∂μ = ∫ g in 𝓕, Φ g ∂μ := by
  have hinv : ∀ (γ : Γ) (x : G), (fun g => Φ (g * a)) (γ • x) = (fun g => Φ (g * a)) x := by
    intro γ x
    show Φ ((γ : G) * x * a) = Φ (x * a)
    rw [mul_assoc]
    exact hΦ γ γ.2 (x * a)
  rw [h.setIntegral_eq (isFundamentalDomain_preimage_mul_right' Γ μ h a) hinv]
  exact (measurePreserving_mul_right μ a).setIntegral_preimage_emb
    (MeasurableEquiv.mulRight a).measurableEmbedding Φ 𝓕

theorem setIntegral_average {G K : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] [SecondCountableTopology G] (Γ : Subgroup G) [Countable Γ]
    (μ : Measure G) [SFinite μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] {𝓕 : Set G}
    (h : IsFundamentalDomain Γ 𝓕 μ) [TopologicalSpace K] [MeasurableSpace K] [OpensMeasurableSpace K]
    (m : Measure K) [IsProbabilityMeasure m] {κ : K → G} (hκ : Continuous κ)
    {Φ : G → ℂ} (hΦ : ∀ γ ∈ Γ, ∀ g, Φ (γ * g) = Φ g) (hc : Continuous Φ) (hi : IntegrableOn Φ 𝓕 μ) :
    ∫ g in 𝓕, ∫ k, Φ (g * κ k) ∂m ∂μ = ∫ g in 𝓕, Φ g ∂μ := by
  have hjoint : Continuous fun p : G × K => Φ (p.1 * κ p.2) :=
    hc.comp (continuous_fst.mul (hκ.comp continuous_snd))
  have hint : Integrable (Function.uncurry fun g k => Φ (g * κ k)) ((μ.restrict 𝓕).prod m) := by
    refine (integrable_prod_iff' hjoint.aestronglyMeasurable).mpr ⟨?_, ?_⟩
    · exact Filter.Eventually.of_forall fun k => integrableOn_mul_right Γ μ h hΦ hi (κ k)
    · have hn : ∀ k, ∫ g in 𝓕, ‖Φ (g * κ k)‖ ∂μ = ∫ g in 𝓕, ‖Φ g‖ ∂μ := fun k =>
        setIntegral_fd_comp_mul_right_of_invariant Γ μ h (Φ := fun g => ‖Φ g‖)
          (fun γ hγ g => by simp only [hΦ γ hγ g]) (κ k)
      show Integrable (fun k => ∫ g in 𝓕, ‖Φ (g * κ k)‖ ∂μ) m
      simp only [hn]
      exact integrable_const _
  rw [integral_integral_swap hint]
  have hs : ∀ k, ∫ g in 𝓕, Φ (g * κ k) ∂μ = ∫ g in 𝓕, Φ g ∂μ := fun k =>
    setIntegral_fd_comp_mul_right_of_invariant Γ μ h hΦ (κ k)
  simp only [hs, integral_const, probReal_univ, one_smul]

variable {D : D7} {T : HSp D} {Sp : D.what₂.Tau → SPar}

theorem frame_mem (M : DSModel T Sp) (τ : D.what₂.Tau) {κ : Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (hκ : κ ∈ Formalism.REAL.Kset (M.ε τ)) : (M.fr τ)⁻¹ * κ * M.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D T τ) := by
  obtain ⟨hu, hcomm⟩ := hκ
  have hdet : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).mp (M.fr_unit τ)
  have h1 : M.fr τ * (M.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have h2 : ((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  have hκu : κᴴ * κ = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.mp hu
    rwa [Matrix.star_eq_conjTranspose] at this
  show ((M.fr τ)⁻¹ * κ * M.fr τ)ᴴ * gramAt D T τ * ((M.fr τ)⁻¹ * κ * M.fr τ) = gramAt D T τ
  rw [← M.fr_gram τ]
  simp only [Matrix.conjTranspose_mul, mul_assoc]
  rw [← mul_assoc ((M.fr τ)⁻¹)ᴴ, h2, one_mul, ← mul_assoc (M.fr τ) (M.fr τ)⁻¹, h1, one_mul,
    ← mul_assoc (Formalism.REAL.Jm (M.ε τ)) κ, ← hcomm, mul_assoc κ, ← mul_assoc κᴴ κ, hκu, one_mul]

theorem continuous_elt {θ : InfFam D} (hθ : IsInfFam θ) (M : DSModel T Sp) (τ : D.what₂.Tau) :
    Continuous fun k : Formalism.REAL.KG (M.ε τ) => GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.elt θ M τ (Formalism.REAL.toMK k) := by
  have hK : ∀ k : Formalism.REAL.KG (M.ε τ), Formalism.REAL.toMK k ∈ Formalism.REAL.Kset (M.ε τ) := fun k =>
    (Formalism.REAL.mem_KG (M.ε τ) k).mp k.2
  have hc : Continuous fun k : Formalism.REAL.KG (M.ε τ) => Formalism.REAL.toMK k :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  show Continuous fun k : Formalism.REAL.KG (M.ε τ) => atTau θ T τ ((M.fr τ)⁻¹ * Formalism.REAL.toMK k * M.fr τ)
  exact (GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ T τ).comp_continuous
    ((continuous_const.matrix_mul hc).matrix_mul continuous_const)
    (fun k => frame_mem M τ (hK k))

theorem liftInt_eq_sum_average : ∀ (D : D7) (V W : HSp D) (S' : D.what₂.Tau → SPar) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)), IsInfFam θ → IsWeilDatumO ψ V W χS χT ω → ν.IsHaarMeasure → IsFundamentalDomain (GQ W) 𝓕 ν → ∀ (τ : D.what₂.Tau) (n : ℕ) (c : Fin n → Formalism.REAL.KG (M'.ε τ) → ℂ) (f : WO V W → ℂ) (fs : Fin n → WO V W → ℂ) (F : GA D W → ℂ) (Fs : Fin n → GA D W → ℂ), (∀ i, Continuous (c i)) → IsThetaFunO ψ V W f → (∀ k, ω (1, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.elt θ M' τ (Formalism.REAL.toMK k)) f = ∑ i, c i k • fs i) → IsAutFun W F → (∀ i h, Fs i h = ∫ k, c i k * F (h * GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.elt θ M' τ (Formalism.REAL.toMK k)) ∂(Formalism.REAL.muK (M'.ε τ))) → ∀ g, IntegrableOn (fun h => thetaKO ω g h f * F h) 𝓕 ν → (∀ i, IntegrableOn (fun h => thetaKO ω g h (fs i) * Fs i h) 𝓕 ν) → Lift.liftInt ν 𝓕 (thetaKO ω) f F g = ∑ i, Lift.liftInt ν 𝓕 (thetaKO ω) (fs i) (Fs i) g := by
  intro D V W S' M' θ ψ χS χT ω ν 𝓕 hθ hW hν h𝓕 τ n c f fs F Fs hc hf hω hF hFs g hi hii
  obtain ⟨hlc, hsc, ht2, hbor, htg, -, hcount⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  obtain ⟨hright, -⟩ := GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D W ν hν
  have hker := GlobalTheory.thetaKO_continuous_and_rat_invariant ψ V W χS χT ω hW f hf
  have hec : Continuous fun k : Formalism.REAL.KG (M'.ε τ) => GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.elt θ M' τ (Formalism.REAL.toMK k) :=
    continuous_elt hθ M' τ
  have hΦinv : ∀ γ ∈ GQ W, ∀ h, thetaKO ω g (γ * h) f * F (γ * h) = thetaKO ω g h f * F h := by
    intro γ hγ h
    have h1 := hker.2 1 (GQ V).one_mem γ hγ g h
    rw [one_mul] at h1
    rw [h1, hF.left γ hγ h]
  have hΦc : Continuous fun h => thetaKO ω g h f * F h :=
    (hker.1.comp (continuous_const.prodMk continuous_id)).mul hF.cont
  have hlin : ∀ (h k : GA D W) (u : WO V W → ℂ), thetaKO ω g (h * k) u = thetaKO ω g h (ω (1, k) u) := by
    intro h k u
    show ω (g, h * k) u 0 = ω (g, h) (ω (1, k) u) 0
    have hp : ((g, h * k) : GA D V × GA D W) = (g, h) * (1, k) := by simp
    rw [hp, map_mul]
    rfl
  have hsum : ∀ (h : GA D W) (k : Formalism.REAL.KG (M'.ε τ)),
      thetaKO ω g h (∑ i, c i k • fs i) = ∑ i, c i k * thetaKO ω g h (fs i) := by
    intro h k
    show ω (g, h) (∑ i, c i k • fs i) 0 = ∑ i, c i k * ω (g, h) (fs i) 0
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hpt : ∀ h, ∫ k, thetaKO ω g (h * GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.elt θ M' τ (Formalism.REAL.toMK k)) f *
      F (h * GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.elt θ M' τ (Formalism.REAL.toMK k)) ∂(Formalism.REAL.muK (M'.ε τ)) =
      ∑ i, thetaKO ω g h (fs i) * Fs i h := by
    intro h
    have hexp : ∀ k, thetaKO ω g (h * GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.elt θ M' τ (Formalism.REAL.toMK k)) f *
        F (h * GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.elt θ M' τ (Formalism.REAL.toMK k)) =
        ∑ i, thetaKO ω g h (fs i) * (c i k * F (h * GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.elt θ M' τ (Formalism.REAL.toMK k))) := by
      intro k
      rw [hlin, hω k, hsum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hFk : Continuous fun k : Formalism.REAL.KG (M'.ε τ) =>
        F (h * GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.elt θ M' τ (Formalism.REAL.toMK k)) :=
      hF.cont.comp (continuous_const.mul hec)
    have hint : ∀ i, Integrable (fun k => thetaKO ω g h (fs i) *
        (c i k * F (h * GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.elt θ M' τ (Formalism.REAL.toMK k)))) (Formalism.REAL.muK (M'.ε τ)) := fun i =>
      integrableOn_univ.mp
        ((continuous_const.mul ((hc i).mul hFk)).continuousOn.integrableOn_compact isCompact_univ)
    simp_rw [hexp]
    rw [integral_finsetSum _ fun i _ => hint i]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul, hFs i h]
  show ∫ h in 𝓕, thetaKO ω g h f * F h ∂ν = ∑ i, ∫ h in 𝓕, thetaKO ω g h (fs i) * Fs i h ∂ν
  refine (setIntegral_average (GQ W) ν h𝓕 (m := Formalism.REAL.muK (M'.ε τ))
    (Φ := fun h => thetaKO ω g h f * F h) hec hΦinv hΦc hi).symm.trans ?_
  rw [← integral_finsetSum _ fun i _ => hii i]
  exact integral_congr_ae (Filter.Eventually.of_forall hpt)

end GlobalTheory.Chain.IoLift.AvgLift

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralHomFundamentalDomainIsotropicSplitCoords
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralHomFundamentalDomainIsotropicSplitCoords
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistHaar

open scoped Pointwise

theorem isAddFundamentalDomain_prod {A B : Type*} [AddGroup A] [AddGroup B] [MeasurableSpace A]
    [MeasurableSpace B] {Γ : AddSubgroup A} {Δ : AddSubgroup B} {μ : Measure A} {ν : Measure B} [SFinite μ]
    [SFinite ν] {s : Set A} {t : Set B} (hs : IsAddFundamentalDomain Γ s μ) (ht : IsAddFundamentalDomain Δ t ν) :
    IsAddFundamentalDomain (Γ.prod Δ) (s ×ˢ t) (μ.prod ν) := by
  refine ⟨hs.nullMeasurableSet.prod ht.nullMeasurableSet, ?_, ?_⟩
  ·
    have h1 := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae hs.ae_covers
    have h2 := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae ht.ae_covers
    filter_upwards [h1, h2] with p hp hq
    obtain ⟨g, hg⟩ := hp
    obtain ⟨h, hh⟩ := hq
    exact ⟨⟨((g : A), (h : B)), AddSubgroup.mem_prod.2 ⟨g.2, h.2⟩⟩, hg, hh⟩
  ·
    intro g h hgh
    change μ.prod ν ((g +ᵥ s ×ˢ t) ∩ (h +ᵥ s ×ˢ t)) = 0
    let g1 : Γ := ⟨(g : A × B).1, (AddSubgroup.mem_prod.1 g.2).1⟩
    let h1 : Γ := ⟨(h : A × B).1, (AddSubgroup.mem_prod.1 h.2).1⟩
    let g2 : Δ := ⟨(g : A × B).2, (AddSubgroup.mem_prod.1 g.2).2⟩
    let h2 : Δ := ⟨(h : A × B).2, (AddSubgroup.mem_prod.1 h.2).2⟩
    by_cases e1 : g1 = h1
    · have e2 : g2 ≠ h2 := fun e2 => hgh (Subtype.ext (Prod.ext (congrArg Subtype.val e1) (congrArg Subtype.val e2)))
      have h0 : ν ((g2 +ᵥ t) ∩ (h2 +ᵥ t)) = 0 := ht.aedisjoint e2
      refine measure_mono_null (t := Set.univ ×ˢ ((g2 +ᵥ t) ∩ (h2 +ᵥ t))) ?_ ?_
      · rintro p ⟨hp1, hp2⟩
        rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hp1 hp2
        refine ⟨Set.mem_univ _, ?_, ?_⟩
        · rw [Set.mem_vadd_set_iff_neg_vadd_mem]; exact hp1.2
        · rw [Set.mem_vadd_set_iff_neg_vadd_mem]; exact hp2.2
      · rw [Measure.prod_prod, h0, mul_zero]
    · have h0 : μ ((g1 +ᵥ s) ∩ (h1 +ᵥ s)) = 0 := hs.aedisjoint e1
      refine measure_mono_null (t := ((g1 +ᵥ s) ∩ (h1 +ᵥ s)) ×ˢ Set.univ) ?_ ?_
      · rintro p ⟨hp1, hp2⟩
        rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hp1 hp2
        refine ⟨⟨?_, ?_⟩, Set.mem_univ _⟩
        · rw [Set.mem_vadd_set_iff_neg_vadd_mem]; exact hp1.1
        · rw [Set.mem_vadd_set_iff_neg_vadd_mem]; exact hp2.1
      · rw [Measure.prod_prod, h0, zero_mul]

end GlobalTheory.TwistHaar

namespace GlobalTheory.TwistHaar

open scoped Pointwise


set_option maxHeartbeats 1000000 in
theorem integral_fundamentalDomain_eq_iterated : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ C' : Matrix (Fin V.rank) (Fin r) D.host.E, adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ (μV : Measure (WO V W)) (𝓕V : Set (WO V W)), μV.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕V μV → ∀ (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)), μ'.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V') 𝓕' μ' → ∃ κ : ℝ, 0 < κ ∧ (∀ H : WO V W → ℂ, Continuous H → (∃ b : ℝ, ∀ w, ‖H w‖ ≤ b) → (∀ γ ∈ ratL W V, ∀ w, H (γ + w) = H w) → ∫ w in 𝓕V, H w ∂μV = κ • ∫ t in 𝓨, ∫ y in 𝓨, ∫ x in 𝓕', H (isoPart V W C' t + isoPart V W C y + midPart V V' W B x) ∂μ' ∂μ ∂μ) := by
  intro D V V' W r C B hs C' h1 h2 h3 μ 𝓨 hY μV 𝓕V hμV hFV μ' 𝓕' hμ' hF'
  obtain ⟨e, he, hrat⟩ := GlobalTheory.T.exists_homSpace_dual_isotropic_middle_decomposition D V V' W r C B hs C' h1 h2 h3
  obtain ⟨a1, a2, a3, a4, a5, -⟩ := GlobalTheory.MixModel.lattice_Mx D W.rank r
  obtain ⟨b1, b2, b3, b4, b5, -⟩ := GlobalTheory.MixModel.lattice_Mx D W.rank V'.rank
  obtain ⟨c1, c2, c3, c4, c5, -⟩ := GlobalTheory.MixModel.lattice_Mx D W.rank V.rank
  have : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  have : BorelSpace (WO V' W) := ⟨rfl⟩
  have : BorelSpace (WO V W) := ⟨rfl⟩
  have : DiscreteTopology (ratMx D W.rank r) := a5
  have : DiscreteTopology (ratL W V') := b5
  have : DiscreteTopology (ratL W V) := c5
  have cA : Countable (ratMx D W.rank r) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have cB : Countable (ratL W V') := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have : μ.IsAddHaarMeasure := hY.1

  set Γ' : AddSubgroup (Mx D W.rank r × Mx D W.rank r × WO V' W) :=
    (ratMx D W.rank r).prod ((ratMx D W.rank r).prod (ratL W V')) with hΓ'
  have hmem : ∀ p, e p ∈ ratL W V ↔ p ∈ Γ' := by
    rintro ⟨t, y, x⟩
    rw [hrat]
    simp [Γ', AddSubgroup.mem_prod]
  have : Countable Γ' := Function.Injective.countable
    (f := fun g : Γ' => ((⟨(g : Mx D W.rank r × Mx D W.rank r × WO V' W).1, (AddSubgroup.mem_prod.1 g.2).1⟩ :
        ratMx D W.rank r),
      (⟨(g : Mx D W.rank r × Mx D W.rank r × WO V' W).2.1, (AddSubgroup.mem_prod.1 (AddSubgroup.mem_prod.1 g.2).2).1⟩ :
        ratMx D W.rank r),
      (⟨(g : Mx D W.rank r × Mx D W.rank r × WO V' W).2.2, (AddSubgroup.mem_prod.1 (AddSubgroup.mem_prod.1 g.2).2).2⟩ :
        ratL W V')))
    fun g h hgh => by
      simp only [Prod.mk.injEq, Subtype.mk.injEq] at hgh
      exact Subtype.ext (Prod.ext hgh.1 (Prod.ext hgh.2.1 hgh.2.2))
  set P : Measure (Mx D W.rank r × Mx D W.rank r × WO V' W) := μ.prod (μ.prod μ') with hP
  have hT : IsAddFundamentalDomain Γ' (𝓨 ×ˢ (𝓨 ×ˢ 𝓕')) P :=
    isAddFundamentalDomain_prod hY.2.1 (isAddFundamentalDomain_prod hY.2.1 hF')
  set m : Measure (WO V W) := P.map e with hm
  have : (μ.prod μ').IsAddHaarMeasure := inferInstance
  have : P.IsAddHaarMeasure := inferInstance
  have : m.IsAddHaarMeasure := e.isAddHaarMeasure_map P
  have : VAddInvariantMeasure Γ' (Mx D W.rank r × Mx D W.rank r × WO V' W) P :=
    ⟨fun g s _ => measure_preimage_add P (g : Mx D W.rank r × Mx D W.rank r × WO V' W) s⟩
  set c : NNReal := μV.addHaarScalarFactor m with hcdef
  have hc : μV = c • m := Measure.isAddLeftInvariant_eq_smul μV m
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hc
    exact (NeZero.ne μV) hc
  have hac : m ≪ μV := fun s hs0 => by
    rw [hc, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at hs0
    exact (mul_eq_zero.1 hs0).resolve_left (by simpa using hc0)
  have hFm : IsAddFundamentalDomain (ratL W V) 𝓕V m := hFV.mono hac
  have hemeas : Measurable e := e.continuous.measurable
  have hpre : IsAddFundamentalDomain Γ' (e ⁻¹' 𝓕V) P := by
    refine hFm.preimage_of_equiv (f := e) (MeasurePreserving.quasiMeasurePreserving ⟨hemeas, rfl⟩)
      (e := fun g => ⟨e.symm g, (hmem _).1 (by simpa using g.2)⟩) ⟨fun g h hgh => ?_, fun g => ?_⟩ fun g x => ?_
    · exact Subtype.ext (e.symm.injective (congrArg Subtype.val hgh))
    · exact ⟨⟨e g, (hmem g).2 g.2⟩, Subtype.ext (by simp)⟩
    · change e (e.symm g + x) = (g : WO V W) + e x
      rw [map_add (f := _), ContinuousAddEquiv.apply_symm_apply]
  have hfin : μ' 𝓕' ≠ ⊤ := (GlobalTheory.Size.measure_dom hμ' hF').2
  have : IsFiniteMeasure (μ.restrict 𝓨) := ⟨by rw [Measure.restrict_apply_univ, hY.2.2]; exact ENNReal.one_lt_top⟩
  have : IsFiniteMeasure (μ'.restrict 𝓕') := ⟨by rw [Measure.restrict_apply_univ]; exact hfin.lt_top⟩
  refine ⟨(c : ℝ), NNReal.coe_pos.2 (pos_iff_ne_zero.2 hc0), fun H hH hb hper => ?_⟩
  obtain ⟨b, hb⟩ := hb
  have hmeasH : Measurable (fun p => H (e p)) := (hH.comp e.continuous).measurable
  have step1 : ∫ w in 𝓕V, H w ∂μV = (c : ℝ) • ∫ w in 𝓕V, H w ∂m := by
    have : μV = (c : ENNReal) • m := by rw [hc]; rfl
    rw [this, Measure.restrict_smul, integral_smul_measure, ENNReal.coe_toReal]
  have step2 : ∫ w in 𝓕V, H w ∂m = ∫ p in e ⁻¹' 𝓕V, H (e p) ∂P :=
    (e.toHomeomorph.toMeasurableEquiv.measurableEmbedding).setIntegral_map H 𝓕V
  have step3 : ∫ p in e ⁻¹' 𝓕V, H (e p) ∂P = ∫ p in 𝓨 ×ˢ (𝓨 ×ˢ 𝓕'), H (e p) ∂P :=
    hpre.setIntegral_eq hT (f := fun p => H (e p)) fun g p => by
      change H (e ((g : Mx D W.rank r × Mx D W.rank r × WO V' W) + p)) = H (e p)
      rw [map_add (f := _)]
      exact hper _ ((hmem g).2 g.2) _
  have r1 : (μ.prod (μ.prod μ')).restrict (𝓨 ×ˢ (𝓨 ×ˢ 𝓕')) =
      (μ.restrict 𝓨).prod ((μ.restrict 𝓨).prod (μ'.restrict 𝓕')) :=
    ((congrArg (Measure.prod (μ.restrict 𝓨)) (Measure.prod_restrict 𝓨 𝓕')).trans
      (Measure.prod_restrict 𝓨 (𝓨 ×ˢ 𝓕'))).symm
  have step4 : ∫ p in 𝓨 ×ˢ (𝓨 ×ˢ 𝓕'), H (e p) ∂P = ∫ t in 𝓨, ∫ y in 𝓨, ∫ x in 𝓕',
      H (isoPart V W C' t + isoPart V W C y + midPart V V' W B x) ∂μ' ∂μ ∂μ := by
    refine (congrArg (fun ν => ∫ p, H (e p) ∂ν) r1).trans ?_
    refine (integral_prod _ (Integrable.of_bound hmeasH.aestronglyMeasurable b
      (Filter.Eventually.of_forall fun p => hb _))).trans ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    refine (integral_prod (fun q => H (e (t, q))) (Integrable.of_bound
      (hmeasH.comp measurable_prodMk_left).aestronglyMeasurable b (Filter.Eventually.of_forall fun p => hb _))).trans ?_
    simp only [he]
  exact step1.trans (congrArg (fun z : ℂ => (c : ℝ) • z) ((step2.trans step3).trans step4))

end GlobalTheory.TwistHaar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralHomFundamentalDomainIsotropicSplitCoordsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_hom_fundamental_domain_isotropic_split_coords : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ C' : Matrix (Fin V.rank) (Fin r) D.host.E, adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ (μV : Measure (WO V W)) (𝓕V : Set (WO V W)), μV.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕V μV → ∀ (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)), μ'.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V') 𝓕' μ' → ∃ κ : ℝ, 0 < κ ∧ (∀ H : WO V W → ℂ, Continuous H → (∃ b : ℝ, ∀ w, ‖H w‖ ≤ b) → (∀ γ ∈ ratL W V, ∀ w, H (γ + w) = H w) → ∫ w in 𝓕V, H w ∂μV = κ • ∫ t in 𝓨, ∫ y in 𝓨, ∫ x in 𝓕', H (isoPart V W C' t + isoPart V W C y + midPart V V' W B x) ∂μ' ∂μ ∂μ) := by
  first | exact @GlobalTheory.TwistHaar.integral_fundamentalDomain_eq_iterated | exact GlobalTheory.TwistHaar.integral_fundamentalDomain_eq_iterated | (intros; apply GlobalTheory.TwistHaar.integral_fundamentalDomain_eq_iterated <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNatMulIntegralMatricesSubsetOpenAddSubgrou
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNatMulIntegralMatricesSubsetOpenAddSubgrou
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OpenSubAdele

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]

theorem exists_small_of_mem_nhds {t : Set (FiniteAdeleRing R K)}
    (ht : t ∈ nhds (0 : FiniteAdeleRing R K)) :
    ∃ r : R, r ≠ 0 ∧ ∀ y : FiniteAdeleRing R K,
      (∀ v : HeightOneSpectrum R, Valued.v (y v) ≤ v.intValuation r) → y ∈ t := by
  classical
  have hAopen : ∀ v : HeightOneSpectrum R,
      IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
    fun v => Valued.isOpen_valuationSubring _
  let z0 : ∀ v : HeightOneSpectrum R, (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
    fun v => ⟨0, (v.adicCompletionIntegers K).zero_mem⟩
  let t' : Set (RestrictedProduct (fun v : HeightOneSpectrum R => v.adicCompletion K)
          (fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K))) Filter.cofinite) := t
  have h1' : t' ∈
      nhds (RestrictedProduct.structureMap (fun v : HeightOneSpectrum R => v.adicCompletion K)
        (fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K))) Filter.cofinite z0) := ht
  rw [RestrictedProduct.nhds_eq_map_structureMap hAopen, Filter.mem_map, nhds_pi,
    Filter.mem_pi'] at h1'
  obtain ⟨I, u, hu, hIu⟩ := h1'
  have hW : ∀ v, ∃ W : Set (v.adicCompletion K), W ∈ nhds (0 : v.adicCompletion K) ∧
      ∀ y : v.adicCompletion K, (hy : y ∈ (v.adicCompletionIntegers K : Set (v.adicCompletion K))) →
        y ∈ W → (⟨y, hy⟩ : (v.adicCompletionIntegers K : Set (v.adicCompletion K))) ∈ u v := by
    intro v
    obtain ⟨W, hW, hWu⟩ := (mem_nhds_subtype _ (z0 v) (u v)).mp (hu v)
    exact ⟨W, hW, fun y hy hyW => hWu hyW⟩
  choose W hW0 hWu using hW
  obtain ⟨r, hr, hsmall⟩ :=
    PI.UnipApproxD.IntegersDenseFiniteAdeles.exists_small_finset (R := R) (K := K) I W (fun v _ => hW0 v)
  refine ⟨r, hr, fun y hy => ?_⟩
  have hint : ∀ v : HeightOneSpectrum R,
      y v ∈ (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
    intro v
    rw [SetLike.mem_coe, mem_adicCompletionIntegers]
    exact (hy v).trans (v.intValuation_le_one r)
  let z : ∀ v : HeightOneSpectrum R, (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
    fun v => ⟨y v, hint v⟩
  have hz : z ∈ Set.pi (↑I) u := fun v hv => hWu v _ (hint v) (hsmall v hv _ (hy v))
  have hmem := hIu hz
  have e : RestrictedProduct.structureMap (fun v : HeightOneSpectrum R => v.adicCompletion K)
        (fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K))) Filter.cofinite z = y := by
    ext v; rfl
  rw [← e]
  exact hmem

end GlobalTheory.OpenSubAdele

namespace GlobalTheory.OpenSubAdele

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

theorem exists_nat_mul_mem_of_mem_nhds {F : Type} [Field F] [NumberField F] {t : Set (Af F)}
    (ht : t ∈ nhds (0 : Af F)) :
    ∃ M₀ : ℕ, 0 < M₀ ∧ ∀ b ∈ GlobalTheory.HolDict.ShortVec.intRing F, (M₀ : Af F) * b ∈ t := by
  obtain ⟨r, hr, h⟩ := exists_small_of_mem_nhds (R := 𝓞 F) (K := F) ht
  have hc := Ideal.comap_ne_bot_of_integral_mem (R := ℤ) (I := Ideal.span {r}) hr
    (Ideal.mem_span_singleton_self r) (Algebra.IsIntegral.isIntegral r)
  obtain ⟨m, hm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc
  rw [Ideal.mem_comap, Ideal.mem_span_singleton] at hm
  have hdvd : r ∣ ((m.natAbs : ℕ) : 𝓞 F) := by
    refine hm.trans ((map_dvd (algebraMap ℤ (𝓞 F)) (Int.dvd_natAbs.mpr dvd_rfl)).trans ?_)
    simp
  obtain ⟨c, hc⟩ := hdvd
  refine ⟨m.natAbs, Int.natAbs_pos.mpr hm0, fun b hb => h _ fun v => ?_⟩
  have hb' : evalV F v b ∈ v.adicCompletionIntegers F := Subring.mem_iInf.mp hb v
  change Valued.v (evalV F v ((m.natAbs : Af F) * b)) ≤ _
  have e : ((m.natAbs : ℕ) : Fv F v) =
      algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (r * c)) := by
    rw [← hc]; simp
  rw [map_mul, map_natCast, e, Valuation.map_mul, PI.UnipApproxD.IntegersDenseFiniteAdeles.val_R, map_mul]
  calc v.intValuation r * v.intValuation c * Valued.v (evalV F v b)
      ≤ v.intValuation r * 1 * 1 :=
        mul_le_mul' (mul_le_mul' le_rfl (v.intValuation_le_one c))
          ((mem_adicCompletionIntegers _ _ _).mp hb')
    _ = v.intValuation r := by simp

end GlobalTheory.OpenSubAdele

namespace GlobalTheory.OpenSubAdele

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

noncomputable def singleEntry (D : D7) (V W : HSp D) (i : Fin W.rank) (j : Fin V.rank)
    (k : Fin (Module.finrank D.host.F D.host.E)) (c : Af D.host.F) : WO V W :=
  Matrix.of fun i' j' => if i = i' then if j = j' then
    pairA D.host.F 0 c ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E k else 0 else 0

theorem continuous_singleEntry (D : D7) (V W : HSp D) (i : Fin W.rank) (j : Fin V.rank)
    (k : Fin (Module.finrank D.host.F D.host.E)) : Continuous (singleEntry D V W i j k) := by
  have hp : Continuous (fun c : Af D.host.F => pairA D.host.F 0 c) := by
    unfold pairA; fun_prop
  have ht : Continuous (fun c : Af D.host.F =>
      (pairA D.host.F 0 c ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E k : AE D)) := by
    have e : (fun c : Af D.host.F =>
        (pairA D.host.F 0 c ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E k : AE D)) =
        fun c => pairA D.host.F 0 c •
          ((1 : AF D.host.F) ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E k : AE D) := by
      funext c; rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [e]
    exact hp.smul (continuous_const (y := ((1 : AF D.host.F) ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E k : AE D)))
  unfold singleEntry
  refine continuous_pi fun i' => continuous_pi fun j' => ?_
  simp only [Matrix.of_apply]
  split_ifs
  · exact ht
  · exact continuous_const
  · exact continuous_const

theorem singleEntry_zero (D : D7) (V W : HSp D) (i : Fin W.rank) (j : Fin V.rank)
    (k : Fin (Module.finrank D.host.F D.host.E)) : singleEntry D V W i j k 0 = 0 := by
  ext i' j'
  have h0 : pairA D.host.F 0 0 = 0 := rfl
  simp [singleEntry, h0]

theorem exists_nat_mul_mem_openAddSubgroup : ∀ (D : D7) (V W : HSp D) (U : AddSubgroup (WO V W)),
    IsOpen (U : Set (WO V W)) → ∃ M₀ : ℕ, 0 < M₀ ∧
      ∀ a : Fin W.rank → Fin V.rank → Fin (Module.finrank D.host.F D.host.E) → Af D.host.F,
        (∀ i j k, a i j k ∈ GlobalTheory.HolDict.ShortVec.intRing D.host.F) →
        (Matrix.of fun i j => ∑ k, pairA D.host.F 0 ((M₀ : Af D.host.F) * a i j k) ⊗ₜ[D.host.F]
          Module.finBasis D.host.F D.host.E k : WO V W) ∈ U := by
  intro D V W U hU
  have hnhds : (⋂ x : Fin W.rank × Fin V.rank × Fin (Module.finrank D.host.F D.host.E),
      singleEntry D V W x.1 x.2.1 x.2.2 ⁻¹' (U : Set (WO V W))) ∈ nhds (0 : Af D.host.F) := by
    refine Filter.iInter_mem.mpr fun x => ?_
    refine (continuous_singleEntry D V W x.1 x.2.1 x.2.2).continuousAt.preimage_mem_nhds ?_
    rw [singleEntry_zero]
    exact hU.mem_nhds U.zero_mem
  obtain ⟨M₀, hM₀, hM⟩ := exists_nat_mul_mem_of_mem_nhds hnhds
  refine ⟨M₀, hM₀, fun a ha => ?_⟩
  have hsum : (Matrix.of fun i j => ∑ k, pairA D.host.F 0 ((M₀ : Af D.host.F) * a i j k) ⊗ₜ[D.host.F]
          Module.finBasis D.host.F D.host.E k : WO V W) =
      ∑ i, ∑ j, ∑ k, singleEntry D V W i j k ((M₀ : Af D.host.F) * a i j k) := by
    ext i' j'
    simp [singleEntry, Matrix.sum_apply]
  rw [hsum]
  refine U.sum_mem fun i _ => U.sum_mem fun j _ => U.sum_mem fun k _ => ?_
  have := hM _ (ha i j k)
  exact Set.mem_iInter.mp this (i, j, k)

end GlobalTheory.OpenSubAdele
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNatMulIntegralMatricesSubsetOpenAddSubgrouStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_natMul_integralMatrices_subset_openAddSubgroup : ∀ (D : D7) (V W : HSp D) (U : AddSubgroup (WO V W)), IsOpen (U : Set (WO V W)) → ∃ M₀ : ℕ, 0 < M₀ ∧ ∀ a : Fin W.rank → Fin V.rank → Fin (Module.finrank D.host.F D.host.E) → Af D.host.F, (∀ i j k, a i j k ∈ GlobalTheory.HolDict.ShortVec.intRing D.host.F) → (Matrix.of fun i j => ∑ k, pairA D.host.F 0 ((M₀ : Af D.host.F) * a i j k) ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E k : WO V W) ∈ U := by
  first | exact @GlobalTheory.OpenSubAdele.exists_nat_mul_mem_openAddSubgroup | exact GlobalTheory.OpenSubAdele.exists_nat_mul_mem_openAddSubgroup | (intros; apply GlobalTheory.OpenSubAdele.exists_nat_mul_mem_openAddSubgroup <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignBlockDeterminantNeZeroOfMemMaxCompact
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec KMap maxCpt rep_mem_kFin)
open scoped TensorProduct InnerProductSpace Classical
open GlobalTheory.Chain.IoLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Chain.IoLift.FockOrbit

open GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators GlobalTheory.PointAtPlaceHom

section General

variable {G σ : Type} [TopologicalSpace G]

def CoefCont (F : G → MvPolynomial σ ℂ) : Prop := ∀ m, Continuous fun k => AddMonoidAlgebra.coeff (F k) m

theorem CoefCont.const (P : MvPolynomial σ ℂ) : CoefCont fun _ : G => P := fun _ => continuous_const

theorem CoefCont.add {F F' : G → MvPolynomial σ ℂ} (h : CoefCont F) (h' : CoefCont F') :
    CoefCont fun k => F k + F' k := fun m => by
  simp only [MvPolynomial.coeff_add]
  exact (h m).add (h' m)

theorem CoefCont.mul {F F' : G → MvPolynomial σ ℂ} (h : CoefCont F) (h' : CoefCont F') :
    CoefCont fun k => F k * F' k := fun m => by
  simp only [MvPolynomial.coeff_mul]
  exact continuous_finsetSum _ fun p _ => (h _).mul (h' _)

theorem CoefCont.smul {s : G → ℂ} {F : G → MvPolynomial σ ℂ} (hs : Continuous s) (h : CoefCont F) :
    CoefCont fun k => s k • F k := fun m => by
  simp only [MvPolynomial.coeff_smul, smul_eq_mul]
  exact hs.mul (h m)

theorem CoefCont.sum {ι : Type} [Fintype ι] {F : ι → G → MvPolynomial σ ℂ} (h : ∀ i, CoefCont (F i)) :
    CoefCont fun k => ∑ i, F i k := fun m => by
  simp only [MvPolynomial.coeff_sum]
  exact continuous_finsetSum _ fun i _ => h i m

theorem CoefCont.aeval {τ : Type} {g : G → τ → MvPolynomial σ ℂ} (h : ∀ v, CoefCont fun k => g k v)
    (P : MvPolynomial τ ℂ) : CoefCont fun k => MvPolynomial.aeval (g k) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using CoefCont.const _
  | add p q hp hq => simpa using hp.add hq
  | mul_X p v hp => simpa using hp.mul (h v)

theorem exists_monomials [Finite σ] (N : ℕ) : ∃ (n : ℕ) (e : Fin n → σ →₀ ℕ), ∀ P : MvPolynomial σ ℂ,
    P.totalDegree ≤ N → P = ∑ i, AddMonoidAlgebra.coeff P (e i) • MvPolynomial.monomial (e i) (1 : ℂ) := by
  let T := (Finsupp.finite_of_degree_le (σ := σ) N).toFinset
  refine ⟨T.card, fun i => (T.equivFin.symm i : σ →₀ ℕ), fun P hP => ?_⟩
  rw [T.equivFin.symm.sum_comp (fun d : T => AddMonoidAlgebra.coeff P (d : σ →₀ ℕ) •
    MvPolynomial.monomial (d : σ →₀ ℕ) (1 : ℂ)),
    Finset.sum_coe_sort T fun d => AddMonoidAlgebra.coeff P d • MvPolynomial.monomial d (1 : ℂ)]
  simp only [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  conv_lhs => rw [P.as_sum]
  refine Finset.sum_subset (fun d hd => ?_) fun d _ hd => ?_
  · simp only [T, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    exact (MvPolynomial.le_totalDegree hd).trans hP
  · rw [MvPolynomial.notMem_support_iff.1 hd, map_zero]

theorem exists_coefFam [Group G] [Finite σ] (ρ : G → Module.End ℂ (MvPolynomial σ ℂ))
    (hm : ∀ a b P, ρ (a * b) P = ρ a (ρ b P)) (hd : ∀ a P, (ρ a P).totalDegree ≤ P.totalDegree)
    (hc : ∀ P, CoefCont fun k => ρ k P) (φ : MvPolynomial σ ℂ) :
    ∃ (n : ℕ) (φs : Fin n → MvPolynomial σ ℂ) (c : Fin n → G → ℂ), IsCoefFam c ∧ ∀ k, ρ k φ = ∑ i, c i k • φs i := by
  obtain ⟨n, e, he⟩ := exists_monomials (σ := σ) φ.totalDegree
  refine ⟨n, fun i => MvPolynomial.monomial (e i) 1, fun i k => AddMonoidAlgebra.coeff (ρ k φ) (e i),
    ⟨fun i => hc φ _, fun k₀ i => ⟨fun j => AddMonoidAlgebra.coeff (ρ k₀ (MvPolynomial.monomial (e j) 1)) (e i),
      fun k => ?_⟩⟩, fun k => he _ (hd k φ)⟩
  beta_reduce
  rw [hm]
  conv_lhs => rw [he _ (hd k φ)]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

end General

theorem signBlockDeterminant_ne_zero_of_mem_maxCompact {n : ℕ} {ε : Fin n → Bool} (e : Bool) {k : Matrix (Fin n) (Fin n) ℂ}
    (hk : k ∈ Formalism.REAL.Kset ε) : signBlockDeterminant ε e k ≠ 0 := by
  have hd : k.det ≠ 0 := (Matrix.isUnit_iff_isUnit_det k).1 (Unitary.isUnit_coe (U := ⟨k, hk.1⟩)) |>.ne_zero
  rw [Matrix.twoBlockTriangular_det k (fun i => ε i = e) (fun i hi j hj => by
    have h := congrFun (congrFun hk.2 i) j
    simp only [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    cases e <;> simp only [Bool.not_eq_true, Bool.not_eq_false] at hi <;> simp [hi, hj] at h <;>
      first | linear_combination (1 / 2 : ℂ) * h | linear_combination (-1 / 2 : ℂ) * h)] at hd
  have := left_ne_zero_of_mul hd
  unfold signBlockDeterminant
  convert this
  rfl

theorem continuous_signBlockDeterminant {n : ℕ} (ε : Fin n → Bool) (e : Bool) : Continuous (signBlockDeterminant ε e) :=
  (continuous_id.matrix_submatrix _ _).matrix_det

theorem continuous_toMK {n : ℕ} (ε : Fin n → Bool) : Continuous fun k : Formalism.REAL.KG ε => Formalism.REAL.toMK k :=
  ((Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isEmbedding.comp Topology.IsEmbedding.subtypeVal).continuous

variable {D : D7}

theorem unframe_mem {W : HSp D} {S' : D.what₂.Tau → SPar} (M' : DSModel W S') (τ : D.what₂.Tau)
    {k : Matrix (Fin W.rank) (Fin W.rank) ℂ} (hk : k ∈ Formalism.REAL.Kset (M'.ε τ)) :
    (M'.fr τ)⁻¹ * k * M'.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D W τ) := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M'.fr_unit τ)
  have hJ : kᴴ * Formalism.REAL.Jm (M'.ε τ) * k = Formalism.REAL.Jm (M'.ε τ) := (Formalism.REAL.maximal_compact_facts _ _).1 k hk
  have hJ' : ∀ A : Matrix (Fin W.rank) (Fin W.rank) ℂ,
      kᴴ * (Formalism.REAL.Jm (M'.ε τ) * (k * A)) = Formalism.REAL.Jm (M'.ε τ) * A := fun A => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hJ]
  have e1 : ((M'.fr τ)⁻¹)ᴴ * (M'.fr τ)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hd]; simp
  have e2 : ∀ A : Matrix (Fin W.rank) (Fin W.rank) ℂ, ((M'.fr τ)⁻¹)ᴴ * ((M'.fr τ)ᴴ * A) = A := fun A => by
    rw [← Matrix.mul_assoc, e1, Matrix.one_mul]
  change ((M'.fr τ)⁻¹ * k * M'.fr τ)ᴴ * gramAt D W τ * ((M'.fr τ)⁻¹ * k * M'.fr τ) = gramAt D W τ
  rw [← M'.fr_gram τ]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc, e2, Matrix.mul_nonsing_inv_cancel_left _ _ hd, hJ']

theorem elt_mul {θ : InfFam D} (hθ : IsInfFam θ) {W : HSp D} {S' : D.what₂.Tau → SPar} (M' : DSModel W S')
    (τ : D.what₂.Tau) {a b : Matrix (Fin W.rank) (Fin W.rank) ℂ} (ha : a ∈ Formalism.REAL.Kset (M'.ε τ))
    (hb : b ∈ Formalism.REAL.Kset (M'.ε τ)) : elt θ M' τ (a * b) = elt θ M' τ a * elt θ M' τ b := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M'.fr_unit τ)
  rw [elt, elt, elt, ← atTau_mul hθ W τ (unframe_mem M' τ ha) (unframe_mem M' τ hb)]
  simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hd]

theorem elt_one' {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)
    (τ : D.what₂.Tau) : elt θ M τ 1 = 1 := by
  rw [elt, Matrix.mul_one, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)), atTau_one hθ]

theorem coefCont_subst {G : Type} [TopologicalSpace G] {a b : ℕ} (τ : D.what₂.Tau) (ε : Fin a → Bool)
    (ε' : Fin b → Bool) (g : Matrix (Fin a) (Fin a) ℂ) {k : G → Matrix (Fin b) (Fin b) ℂ} (hk : Continuous k)
    (P : PolF D b a) : CoefCont fun x => subst τ ε ε' g (k x) P := by
  unfold subst
  refine CoefCont.aeval (fun v => ?_) P
  split_ifs
  all_goals first
    | exact CoefCont.const _
    | refine CoefCont.sum fun l => CoefCont.sum fun m => CoefCont.smul ?_ (CoefCont.const _)
  · exact (hk.matrix_elem _ _).mul continuous_const
  · exact ((hk.matrix_elem _ _).mul continuous_const).star

theorem fock_orbit_coefFam : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f : WO V W → ℂ) (τ : D.what₂.Tau) (aS aT : ℚ), IsInfFam θ → Function.Injective (ptOf ψ θ M M' f) → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.CompactFock ψ θ M M' ω f τ aS aT → ∀ φ : PolF D W.rank V.rank, ∃ (n : ℕ) (φs : Fin n → PolF D W.rank V.rank) (c : Fin n → Formalism.REAL.KG (M'.ε τ) → ℂ), IsCoefFam c ∧ ∀ k, ω (1, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.elt θ M' τ (Formalism.REAL.toMK k)) (ptOf ψ θ M M' f φ) = ptOf ψ θ M M' f (∑ i, c i k • φs i) := by
  intro D V W S S' M M' θ ψ ω f τ aS aT hθ hpt hC φ
  obtain ⟨x, y, -, -, hc⟩ := hC
  let pt : PolF D W.rank V.rank →ₗ[ℂ] (WO V W → ℂ) := pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') f
  have hp : ptOf ψ θ M M' f = pt := rfl
  rw [hp] at hpt hc ⊢
  let s : Formalism.REAL.KG (M'.ε τ) → ℂ := fun k => signBlockDeterminant (M.ε τ) true 1 ^ x true * signBlockDeterminant (M.ε τ) false 1 ^ x false *
    (signBlockDeterminant (M'.ε τ) true (Formalism.REAL.toMK k) ^ y true * signBlockDeterminant (M'.ε τ) false (Formalism.REAL.toMK k) ^ y false)
  let ρ : Formalism.REAL.KG (M'.ε τ) → Module.End ℂ (PolF D W.rank V.rank) := fun k =>
    s k • (subst τ (M.ε τ) (M'.ε τ) ((1 : Matrix (Fin V.rank) (Fin V.rank) ℂ).map (starRingEnd ℂ))
      (Formalism.REAL.toMK k)).toLinearMap
  have key : ∀ k P, ω (1, elt θ M' τ (Formalism.REAL.toMK k)) (pt P) = pt (ρ k P) := fun k P => by
    have := hc 1 ⟨one_mem _, by rw [Matrix.one_mul, Matrix.mul_one]⟩ (Formalism.REAL.toMK k) k.2 P
    rw [elt_one' hθ, ← map_smul] at this
    exact this
  have hz : ∀ e, Continuous fun k : Formalism.REAL.KG (M'.ε τ) => signBlockDeterminant (M'.ε τ) e (Formalism.REAL.toMK k) ^ y e := fun e =>
    ((continuous_signBlockDeterminant _ e).comp (continuous_toMK _)).zpow₀ _ fun k => Or.inl (signBlockDeterminant_ne_zero_of_mem_maxCompact e k.2)
  have hs : Continuous s := continuous_const.mul ((hz true).mul (hz false))
  obtain ⟨n, φs, c, h1, h2⟩ := exists_coefFam ρ (fun a b P => hpt (by
      have e : Formalism.REAL.toMK (a * b) = Formalism.REAL.toMK a * Formalism.REAL.toMK b := rfl
      rw [← key, ← key, ← key, e, elt_mul hθ M' τ a.2 b.2, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk,
        mul_one]))
    (fun a P => (MvPolynomial.totalDegree_smul_le _ _).trans
      (GlobalTheory.Chain.RealIt.SubstDeg.totalDegree_subst_le _ _ _ _ _ _ _ _ _))
    (fun P => CoefCont.smul hs (coefCont_subst τ _ _ _ (continuous_toMK _) P)) φ
  exact ⟨n, φs, c, h1, fun k => by rw [key, h2]⟩

end GlobalTheory.Chain.IoLift.FockOrbit

end
end
