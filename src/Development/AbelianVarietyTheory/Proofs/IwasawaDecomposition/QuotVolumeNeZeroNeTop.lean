module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsArchEquivEq
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NotDvdDiscrHost
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.ActsLinOfSplitLin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsThetaFunOOfThetaAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselDatumAuxiliaryVectorOrthogonalImage
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasModelOfAntitone
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.QuotVolumeNeZeroNeTop
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.QuotVol

theorem quot_volume_ne_zero_ne_top : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)),
    IsQuot V μ 𝓕 → μ 𝓕 ≠ 0 ∧ μ 𝓕 ≠ ⊤ := fun D V μ 𝓕 h =>
  ⟨((GlobalTheory.Mem.Vol.fundamentalDomain_adelicUnitary D.host.F D.host.E D.sp.cm.sig V.rank V.gram μ h.1).2
      𝓕 𝓕 h.2 h.2).2,
    (GlobalTheory.Mem.VolFin.finVol D.host.F D.host.E D.sp.cm.sig (GlobalTheory.Mem.VolExists.isCMExt D.sp.cm) V.rank V.gram
      (GlobalTheory.Mem.VolExists.isHermND D.sp.cm V) μ h.1 𝓕 h.2).ne⟩

end GlobalTheory.Mem.QuotVol
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRealIntertwinerOfCompactGroupIntertwiner
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRealIntertwinerOfCompactGroupIntertwiner
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.Chain GlobalTheory.CompactHowe Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompactIntertwiner

theorem hasDerivAt_dual_of_sep {F Z : Type*} [AddCommGroup F] [Module ℂ F] [FiniteDimensional ℂ F]
    (l : Z → F →ₗ[ℂ] ℂ) (hl : ∀ x, (∀ z, l z x = 0) → x = 0) (c : ℝ → F) (y : F)
    (h : ∀ z, HasDerivAt (fun t => l z (c t)) (l z y) 0) (f : F →ₗ[ℂ] ℂ) :
    HasDerivAt (fun t => f (c t)) (f y) 0 := by
  have hsp : Submodule.span ℂ (Set.range l) = ⊤ := by
    have h1 : (Submodule.span ℂ (Set.range l)).dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Submodule.mem_dualCoannihilator] at hx
      exact hl x fun z => hx _ (Submodule.subset_span ⟨z, rfl⟩)
    have h2 := Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span ℂ (Set.range l))
    rw [h1, Submodule.dualAnnihilator_bot] at h2
    exact h2.symm
  have hf : f ∈ Submodule.span ℂ (Set.range l) := hsp ▸ Submodule.mem_top
  induction hf using Submodule.span_induction with
  | mem g hg => obtain ⟨z, rfl⟩ := hg; exact h z
  | zero => simpa using hasDerivAt_const (0 : ℝ) (0 : ℂ)
  | add g g' _ _ hg hg' => exact hg.fun_add hg'
  | smul a g _ hg => simpa using hg.const_mul a

theorem hasDerivAt_dual_of_sep_sub {E Z : Type*} [AddCommGroup E] [Module ℂ E] (F : Submodule ℂ E)
    [FiniteDimensional ℂ F] (l : Z → E →ₗ[ℂ] ℂ) (hl : ∀ x, (∀ z, l z x = 0) → x = 0) (c : ℝ → E) (y : E)
    (hc : ∀ t, c t ∈ F) (hy : y ∈ F)
    (h : ∀ z, HasDerivAt (fun t => l z (c t)) (l z y) 0) (f : E →ₗ[ℂ] ℂ) :
    HasDerivAt (fun t => f (c t)) (f y) 0 :=
  hasDerivAt_dual_of_sep (F := F) (fun z => l z ∘ₗ F.subtype) (fun x hx => Subtype.ext (hl x hx))
    (fun t => ⟨c t, hc t⟩) ⟨y, hy⟩ h (f ∘ₗ F.subtype)

theorem hasDerivAt_bilin {E G : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup G] [Module ℂ G]
    [FiniteDimensional ℂ G] (B : E →ₗ[ℂ] G →ₗ[ℂ] ℂ) (c : ℝ → E) (c' : E) (x : ℝ → G) (x' : G)
    (hc : ∀ f : E →ₗ[ℂ] ℂ, HasDerivAt (fun t => f (c t)) (f c') 0)
    (hx : ∀ f : G →ₗ[ℂ] ℂ, HasDerivAt (fun t => f (x t)) (f x') 0) :
    HasDerivAt (fun t => B (c t) (x t)) (B c' (x 0) + B (c 0) x') 0 := by
  let b := Module.finBasis ℂ G
  have e : ∀ a u, B a u = ∑ i, B.flip (b i) a * b.coord i u := by
    intro a u
    set_option synthInstance.maxHeartbeats 100000 in
      conv_lhs => rw [← b.sum_repr u, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
    rfl
  have := HasDerivAt.fun_sum (u := Finset.univ) fun i _ => (hc (B.flip (b i))).mul (hx (b.coord i))
  simp only [e]
  rw [← Finset.sum_add_distrib]
  exact this

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem ellT_tprod (M : DSModel V S) (w v : ∀ τ, M.H τ) :
    ellT M w (PiTensorProduct.tprod ℂ v) = ∏ τ, inner ℂ (w τ) (v τ) := by
  simp [ellT]

theorem finite_tensor (M : DSModel V S) (h : ∀ τ, FiniteDimensional ℂ (M.H τ)) :
    FiniteDimensional ℂ (⨂[ℂ] τ, M.H τ) := by
  classical
  exact Module.Finite.of_basis (Basis.piTensorProduct fun τ => Module.finBasis ℂ (M.H τ))

theorem ellT_sep (M : DSModel V S) (h : ∀ τ, FiniteDimensional ℂ (M.H τ)) (x : ⨂[ℂ] τ, M.H τ)
    (hx : ∀ w, ellT M w x = 0) : x = 0 := by
  classical
  let o := fun τ => stdOrthonormalBasis ℂ (M.H τ)
  let b := Basis.piTensorProduct fun τ => (o τ).toBasis
  have key : ∀ i, b.coord i = ellT M fun τ => o τ (i τ) := by
    intro i
    refine PiTensorProduct.ext (MultilinearMap.ext fun v => ?_)
    simp only [LinearMap.compMultilinearMap_apply, ellT_tprod, Module.Basis.coord_apply, b]
    rw [Basis.piTensorProduct_repr_tprod_apply]
    refine Finset.prod_congr rfl fun τ _ => ?_
    simp [OrthonormalBasis.repr_apply_apply]
  refine b.ext_elem fun i => ?_
  have := hx fun τ => o τ (i τ)
  rw [← key] at this
  simpa using this

theorem inclT_bij (M : DSModel V S) (h : ∀ τ, M.sm τ = ⊤) : Function.Bijective (inclT M) := by
  have : inclT M = (PiTensorProduct.congr fun τ => LinearEquiv.ofTop (M.sm τ) (h τ)).toLinearMap := by
    refine PiTensorProduct.ext (MultilinearMap.ext fun v => ?_)
    simp [inclT]
  rw [this]
  exact LinearEquiv.bijective _

theorem isUnit_gram (M : DSModel V S) (τ : D.what₂.Tau) : IsUnit (gramAt D V τ) := by
  rw [← M.fr_gram τ]
  refine ((M.fr_unit τ).star.mul ?_).mul (M.fr_unit τ)
  refine IsUnit.of_mul_eq_one (Formalism.REAL.Jm (M.ε τ)) ?_
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> simp

theorem continuous_tprod (M : DSModel V S) (h : ∀ τ, FiniteDimensional ℂ (M.H τ)) (f : (⨂[ℂ] τ, M.H τ) →ₗ[ℂ] ℂ) :
    Continuous fun v : ∀ τ, M.H τ => f (PiTensorProduct.tprod ℂ v) := by
  classical
  let o := fun τ => Module.finBasis ℂ (M.H τ)
  let b := Basis.piTensorProduct o
  have e : ∀ v : ∀ τ, M.H τ, f (PiTensorProduct.tprod ℂ v) = ∑ i, (∏ τ, (o τ).coord (i τ) (v τ)) * f (b i) := by
    intro v
    set_option synthInstance.maxHeartbeats 100000 in
      conv_lhs => rw [← b.sum_repr (PiTensorProduct.tprod ℂ v), map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, Basis.piTensorProduct_repr_tprod_apply]
    rfl
  simp only [e]
  exact continuous_finsetSum _ fun i _ => (continuous_finsetProd _ fun τ _ =>
    ((o τ).coord (i τ)).continuous_of_finiteDimensional.comp (continuous_apply τ)).mul continuous_const

theorem one_mem_UH {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Formalism.QuantumDeterminants.UH G := by
  simp [Formalism.QuantumDeterminants.UH]

theorem hasDerivAt_pol {σ Z : Type} [Finite σ] (pt : MvPolynomial σ ℂ →ₗ[ℂ] (Z → ℂ)) (hpt : Function.Injective pt)
    (c : ℝ → MvPolynomial σ ℂ) (N : ℕ) (hc : ∀ t, (c t).totalDegree ≤ N) (y : MvPolynomial σ ℂ)
    (h : ∀ z, HasDerivAt (fun t => pt (c t) z) (pt y z) 0) (f : MvPolynomial σ ℂ →ₗ[ℂ] ℂ) :
    HasDerivAt (fun t => f (c t)) (f y) 0 :=
  hasDerivAt_dual_of_sep_sub (MvPolynomial.restrictTotalDegree σ ℂ (max N y.totalDegree))
    (fun z => LinearMap.proj z ∘ₗ pt) (fun x hx => hpt (by rw [map_zero]; exact funext hx)) c y
    (fun t => (MvPolynomial.mem_restrictTotalDegree _ _ _).2 ((hc t).trans (le_max_left _ _)))
    ((MvPolynomial.mem_restrictTotalDegree _ _ _).2 (le_max_right _ _)) h f

theorem exists_isItW : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (θ : InfFam D) (M : DSModel V S) (M' : DSModel W S') (I : PolF D W.rank V.rank →ₗ[ℂ] (⨂[ℂ] τ, M'.H τ) →ₗ[ℂ] ⨂[ℂ] τ, M.H τ) (ρ : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ → PolF D W.rank V.rank → PolF D W.rank V.rank) (ρ' : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ → PolF D W.rank V.rank → PolF D W.rank V.rank), IsInfFam θ → (∀ τ, FiniteDimensional ℂ (M.H τ) ∧ M.sm τ = ⊤) → (∀ τ, FiniteDimensional ℂ (M'.H τ) ∧ M'.sm τ = ⊤) → I ≠ 0 → (∀ τ g φ, (ρ τ g φ).totalDegree ≤ φ.totalDegree) → (∀ τ h φ, (ρ' τ h φ).totalDegree ≤ φ.totalDegree) → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ φ x, I (ρ τ g φ) x = actT M τ g (I φ x)) → (∀ τ, ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D W τ), ∀ φ x, I (ρ' τ h φ) (actT M' τ h x) = I φ x) → ∃ It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M, ∀ (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (pt : PolF D W.rank V.rank →ₗ[ℂ] (WO V W → ℂ)), Function.Injective pt → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ φ, ω (atTau θ V τ g, 1) (pt φ) = pt (ρ τ g φ)) → (∀ τ, ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D W τ), ∀ φ, ω (1, atTau θ W τ h) (pt φ) = pt (ρ' τ h φ)) → IsItW θ M M' ω pt It := by
  intro D V W S S' θ M M' I ρ ρ' hθ hM hM' hI hd hd' hρ hρ'
  have fM := finite_tensor M fun τ => (hM τ).1
  have fM' := finite_tensor M' fun τ => (hM' τ).1
  let e := LinearEquiv.ofBijective (inclT M) (inclT_bij M fun τ => (hM τ).2)
  let e' := LinearEquiv.ofBijective (inclT M') (inclT_bij M' fun τ => (hM' τ).2)
  have he : ∀ x, inclT M (e.symm x) = x := fun x => e.apply_symm_apply x
  have he' : ∀ x, inclT M' (e'.symm x) = x := fun x => e'.apply_symm_apply x
  let It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M := (I.compl₂ (inclT M')).compr₂ e.symm.toLinearMap
  have hIt : ∀ φ v, inclT M (It φ v) = I φ (inclT M' v) := fun φ v => he _
  have hinj : Function.Injective (inclT M) := e.injective
  refine ⟨It, fun ω pt hpt hω hω' => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro h0
    refine hI (LinearMap.ext fun φ => LinearMap.ext fun x => ?_)
    have := hIt φ (e'.symm x)
    rw [he', h0] at this
    simpa using this.symm
  · intro φ w
    haveI := fun τ => (hM' τ).1
    let m : (Π τ, M'.H τ) →ₘₗ[ℂ] ℂ :=
      (ellT M w ∘ₗ I φ).compMultilinearMap (PiTensorProduct.tprod ℂ)
    obtain ⟨c, -, hc⟩ := m.exists_bound_of_continuous (continuous_tprod M' this (ellT M w ∘ₗ I φ))
    refine ⟨c, fun v => ?_⟩
    rw [hIt]
    have := hc fun τ => (v τ : M'.H τ)
    simpa [m, inclT] using this
  · intro τ g hg φ φ' h v
    rw [hω τ g hg] at h
    rw [hpt h, hIt, hIt, hρ τ g hg]
  · intro τ X hX φ φ' h v w
    have hm : ∀ t : ℝ, NormedSpace.exp (t • X) ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) :=
      fun t => GlobalTheory.GardingVec.exp_mem (isUnit_gram M τ) hX t
    simp only [oneP, hω τ _ (hm _)] at h
    have := hasDerivAt_pol pt hpt (fun t : ℝ => ρ τ (NormedSpace.exp (t • X)) φ) _ (fun t => hd τ _ φ) φ' h
      (ellT M w ∘ₗ I.flip (inclT M' v))
    simp only [hIt, ← hρ τ _ (hm _)]
    exact this
  · intro τ g hg φ φ' v v' h h'
    rw [hω' τ g hg] at h
    apply hinj
    rw [hpt h, hIt, hIt, h', hρ' τ g hg]
  · intro τ X hX φ φ' v v' h h'
    have hm : ∀ t : ℝ, NormedSpace.exp (t • X) ∈ Formalism.QuantumDeterminants.UH (gramAt D W τ) :=
      fun t => GlobalTheory.GardingVec.exp_mem (isUnit_gram M' τ) hX t
    simp only [oneP, hω' τ _ (hm _)] at h
    have h1 : ∀ ψ, ρ' τ 1 ψ = ψ := fun ψ => hpt (by
      rw [← hω' τ 1 (one_mem_UH _), GlobalTheory.PointAtPlaceHom.atTau_one hθ]
      exact congrArg (fun f : Module.End ℂ (WO V W → ℂ) => f (pt ψ)) (map_one ω))
    apply hinj
    rw [map_add (f := _), hIt, hIt, map_zero]
    refine ellT_sep M (fun τ => (hM τ).1) _ fun w => ?_
    have hB := hasDerivAt_bilin (I.compr₂ (ellT M w)) (fun t : ℝ => ρ' τ (NormedSpace.exp (t • X)) φ) φ'
      (fun t : ℝ => actT M' τ (NormedSpace.exp (t • X)) (inclT M' v)) (inclT M' v')
      (hasDerivAt_pol pt hpt _ _ (fun t => hd' τ _ φ) φ' h)
      (hasDerivAt_dual_of_sep (ellT M') (ellT_sep M' fun τ => (hM' τ).1) _ _ h')
    simp only [LinearMap.compr₂_apply, hρ' τ _ (hm _), zero_smul, NormedSpace.exp_zero, h1] at hB
    have h2 := hρ' τ 1 (one_mem_UH _) φ' (inclT M' v)
    rw [h1] at h2
    rw [h2] at hB
    rw [map_add (f := _)]
    exact hB.unique (hasDerivAt_const _ _)

end GlobalTheory.CompactIntertwiner

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRealIntertwinerOfCompactGroupIntertwinerStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.Chain GlobalTheory.CompactHowe Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_realIntertwiner_of_compactGroup_intertwiner : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (θ : InfFam D) (M : DSModel V S) (M' : DSModel W S') (I : PolF D W.rank V.rank →ₗ[ℂ] (⨂[ℂ] τ, M'.H τ) →ₗ[ℂ] ⨂[ℂ] τ, M.H τ) (ρ : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ → PolF D W.rank V.rank → PolF D W.rank V.rank) (ρ' : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ → PolF D W.rank V.rank → PolF D W.rank V.rank), IsInfFam θ → (∀ τ, FiniteDimensional ℂ (M.H τ) ∧ M.sm τ = ⊤) → (∀ τ, FiniteDimensional ℂ (M'.H τ) ∧ M'.sm τ = ⊤) → I ≠ 0 → (∀ τ g φ, (ρ τ g φ).totalDegree ≤ φ.totalDegree) → (∀ τ h φ, (ρ' τ h φ).totalDegree ≤ φ.totalDegree) → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ φ x, I (ρ τ g φ) x = actT M τ g (I φ x)) → (∀ τ, ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D W τ), ∀ φ x, I (ρ' τ h φ) (actT M' τ h x) = I φ x) → ∃ It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M, ∀ (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (pt : PolF D W.rank V.rank →ₗ[ℂ] (WO V W → ℂ)), Function.Injective pt → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ φ, ω (atTau θ V τ g, 1) (pt φ) = pt (ρ τ g φ)) → (∀ τ, ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D W τ), ∀ φ, ω (1, atTau θ W τ h) (pt φ) = pt (ρ' τ h φ)) → IsItW θ M M' ω pt It := by
  first | exact @GlobalTheory.CompactIntertwiner.exists_isItW | exact GlobalTheory.CompactIntertwiner.exists_isItW | (intros; apply GlobalTheory.CompactIntertwiner.exists_isItW <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntertwinerOfSameHarishChandraParamUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntertwinerOfSameHarishChandraParamUnitary
open Matrix Finset

noncomputable section

namespace GlobalTheory.UnitaryHighestWeightUnique

open PI.UpqRep GlobalTheory.UnitaryHighestWeight

theorem _root_.GlobalTheory.UnitaryHighestWeightUnique.height_le {n : ℕ} {ε : Fin n → Bool} {μ Λ : Fin n → ℝ}
    (h : _root_.PI.UpqRep.CDom ε μ Λ) :
    ∑ x : Fin n, ((x : ℕ) : ℝ) * Λ x ≤ ∑ x : Fin n, ((x : ℕ) : ℝ) * μ x ∧
      (∑ x : Fin n, ((x : ℕ) : ℝ) * Λ x = ∑ x : Fin n, ((x : ℕ) : ℝ) * μ x → Λ = μ) := by
  unfold _root_.PI.UpqRep.CDom at h
  obtain ⟨c, hc, h⟩ := h
  have key : ∑ x : Fin n, ((x : ℕ) : ℝ) * Λ x - ∑ x : Fin n, ((x : ℕ) : ℝ) * μ x =
      ∑ a, ∑ b, ((c a b : ℕ) : ℝ) * (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) := by
    rw [← Finset.sum_sub_distrib]
    have hx : ∀ x, Λ x - μ x = (Λ - μ) x := fun x => rfl
    simp_rw [← mul_sub, hx, h]
    unfold _root_.PI.UpqRep.root
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, Pi.single_apply, smul_eq_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [mul_sub, Finset.sum_sub_distrib, mul_comm, mul_left_comm]
    ring
  have hterm : ∀ a b : Fin n, ((c a b : ℕ) : ℝ) * (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) ≤ 0 := by
    intro a b
    by_cases h0 : c a b = 0
    · simp [h0]
    · have hab := (hc a b h0).1
      have : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
      exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (by linarith)
  have hrow : ∀ a, ∑ b, ((c a b : ℕ) : ℝ) * (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) ≤ 0 :=
    fun a => Finset.sum_nonpos fun b _ => hterm a b
  have hsum : ∑ a, ∑ b, ((c a b : ℕ) : ℝ) * (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) ≤ 0 :=
    Finset.sum_nonpos fun a _ => hrow a
  refine ⟨by linarith, fun heq => ?_⟩
  have hzero : ∑ a, ∑ b, ((c a b : ℕ) : ℝ) * (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) = 0 := by
    linarith
  have hc0 : ∀ a b, c a b = 0 := by
    intro a b
    by_contra h0
    have hab := (hc a b h0).1
    have hlt : ((c a b : ℕ) : ℝ) * (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) < 0 := by
      have : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
      exact mul_neg_of_pos_of_neg (by exact_mod_cast Nat.pos_of_ne_zero h0) (by linarith)
    have ha := (Finset.sum_eq_zero_iff_of_nonpos fun a _ => hrow a).1 hzero a (Finset.mem_univ a)
    have hb := (Finset.sum_eq_zero_iff_of_nonpos fun b _ => hterm a b).1 ha b (Finset.mem_univ b)
    linarith
  have : Λ - μ = 0 := by simp [h, hc0]
  exact sub_eq_zero.mp this

theorem _root_.GlobalTheory.UnitaryHighestWeightUnique.exists_derived_highest {k : ℕ} {W : Type} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [Nontrivial W]
    {π : Matrix (Fin k) (Fin k) ℂ → (W →L[ℂ] W)} {Λ : Fin k → ℝ}
    (hπ : _root_.PI.UpqRep.IsURepOn (_root_.PI.UpqRep.UJset (_root_.PI.UpqRep.allPos k)) π) (hK : _root_.PI.UpqRep.IsKTypeOf (_root_.PI.UpqRep.allPos k) π Λ ⊤) :
    ∃ E : Fin k → Fin k → Module.End ℂ W, _root_.Formalism.REAL.GlRel E ∧
      (∀ Z : Matrix (Fin k) (Fin k) ℂ, Zᴴ = -Z → ∀ v,
        HasDerivAt (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • Z)) v) (∑ a, ∑ b, Z a b • E a b v) 0) ∧
      (∀ S : Submodule ℂ W, (∀ a b, ∀ x ∈ S, E a b x ∈ S) → S = ⊥ ∨ S = ⊤) ∧
      ∃ x, x ≠ 0 ∧ _root_.Formalism.REAL.IsHW E (fun a => (Λ a : ℂ)) x := by
  obtain ⟨E, hrel, -, hder⟩ := _root_.GlobalTheory.UnitaryDerived.exists_derived_action k W π hπ
  unfold _root_.PI.UpqRep.IsKTypeOf at hK
  obtain ⟨-, -, hirr, ⟨v, -, hv0, hvw⟩, hdom⟩ := hK
  refine ⟨E, hrel, hder, ?_, v, hv0, ?_⟩
  · intro S hS
    have hSπ : _root_.PI.UpqRep.IsKStableOn (_root_.PI.UpqRep.allPos k) π S := by
      unfold _root_.PI.UpqRep.IsKStableOn
      intro g hg w hw
      exact _root_.GlobalTheory.UnitaryHighestWeight.stable_of_derived hπ E hder S
        (by unfold _root_.Formalism.REAL.KStable; exact fun a b _ x hx => hS a b x hx) g
        ((_root_.GlobalTheory.UnitaryHighestWeight.mem_K_iff g).1 hg) w hw
    exact hirr S le_top hSπ
  · have hvE : _root_.Formalism.REAL.IsWeight E Λ v := _root_.GlobalTheory.UnitaryHighestWeight.isWeight_of_isWtOn E hder Λ v hvw
    unfold _root_.Formalism.REAL.IsWeight at hvE
    unfold _root_.Formalism.REAL.IsHW
    refine ⟨fun a => hvE a, fun a b hab => ?_⟩
    by_contra hne
    unfold _root_.Formalism.REAL.GlRel at hrel
    have hw : _root_.Formalism.REAL.IsWeight E (Λ + _root_.PI.UpqRep.root a b) (E a b v) := by
      unfold _root_.Formalism.REAL.IsWeight
      intro c
      have hc := congrArg (fun T : Module.End ℂ W => T v) (hrel c c a b)
      simp only [LinearMap.sub_apply, Module.End.mul_apply] at hc
      have hsplit : E c c (E a b v) = E a b (E c c v) +
          ((if c = a then E c b else 0) - if b = c then E a c else 0) v := by
        rw [LinearMap.sub_apply, ← hc]; abel
      rw [hsplit, hvE c, map_smul]
      unfold _root_.PI.UpqRep.root
      by_cases hca : c = a
      · subst hca
        have hcb : b ≠ c := ne_of_gt hab
        simp [hcb, Ne.symm hcb, add_smul, add_comm]
      · by_cases hcb : b = c
        · subst hcb
          simp [hca, Ne.symm hca, add_smul, sub_eq_add_neg, add_comm]
        · simp [hca, hcb, Ne.symm hcb]
    have ht := _root_.GlobalTheory.UnitaryHighestWeight.isWtOn_of_isWeight hπ E hder _ _ hw
    have hD := hdom _ (E a b v) Submodule.mem_top hne ht
    have hle := (_root_.GlobalTheory.UnitaryHighestWeightUnique.height_le hD).1
    have hcomp : ∑ x : Fin k, ((x : ℕ) : ℝ) * (Λ + _root_.PI.UpqRep.root a b) x =
        ∑ x : Fin k, ((x : ℕ) : ℝ) * Λ x + (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) := by
      unfold _root_.PI.UpqRep.root
      simp [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, Pi.single_apply]
    have : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
    linarith

theorem _root_.GlobalTheory.UnitaryHighestWeightUnique.intertwine_group {W₁ W₂ : Type} [NormedAddCommGroup W₁]
    [InnerProductSpace ℂ W₁] [NormedAddCommGroup W₂] [InnerProductSpace ℂ W₂]
    [FiniteDimensional ℂ W₁] [FiniteDimensional ℂ W₂]
    (U₁ : ℝ → W₁ →L[ℂ] W₁) (A₁ : W₁ →ₗ[ℂ] W₁) (h₁ : ∀ v, U₁ 0 v = v)
    (hadd₁ : ∀ s t v, U₁ (s + t) v = U₁ s (U₁ t v)) (hd₁ : ∀ v, HasDerivAt (fun t => U₁ t v) (A₁ v) 0)
    (U₂ : ℝ → W₂ →L[ℂ] W₂) (A₂ : W₂ →ₗ[ℂ] W₂) (h₂ : ∀ v, U₂ 0 v = v)
    (hadd₂ : ∀ s t v, U₂ (s + t) v = U₂ s (U₂ t v)) (hd₂ : ∀ v, HasDerivAt (fun t => U₂ t v) (A₂ v) 0)
    (T : W₁ →ₗ[ℂ] W₂) (hT : ∀ v, T (A₁ v) = A₂ (T v)) (v : W₁) (t : ℝ) :
    T (U₁ t v) = U₂ t (T v) := by
  let Tc : W₁ →L[ℝ] W₂ := (LinearMap.toContinuousLinearMap T).restrictScalars ℝ
  let Ac : W₂ →L[ℝ] W₂ := (LinearMap.toContinuousLinearMap A₂).restrictScalars ℝ
  have hTc : ∀ x, Tc x = T x := fun x => rfl
  have hAc : ∀ x, Ac x = A₂ x := fun x => rfl
  have hf : ∀ s, HasDerivAt (fun s => T (U₁ s v)) (Ac (T (U₁ s v))) s := by
    intro s
    have h := _root_.GlobalTheory.UnitaryHighestWeight.deriv_left U₁ A₁ hadd₁ hd₁ v s
    have h' := Tc.hasFDerivAt.comp_hasDerivAt s h
    simp only [Function.comp_def, hTc] at h'
    rwa [hAc, ← hT]
  have hg : ∀ s, HasDerivAt (fun s => U₂ s (T v)) (Ac (U₂ s (T v))) s := by
    intro s
    rw [hAc]
    exact _root_.GlobalTheory.UnitaryHighestWeight.deriv_left U₂ A₂ hadd₂ hd₂ (T v) s
  have heq := ODE_solution_unique_univ (v := fun _ => Ac) (s := fun _ => Set.univ)
    (K := ‖Ac‖₊) (t₀ := 0) (fun _ => Ac.lipschitz.lipschitzOnWith)
    (fun s => ⟨hf s, Set.mem_univ _⟩) (fun s => ⟨hg s, Set.mem_univ _⟩) (by simp [h₁, h₂])
  exact congrFun heq t

theorem _root_.GlobalTheory.UnitaryHighestWeightUnique.exists_equiv_of_isHCTypeU : ∀ (k : ℕ) (u : Fin k → ℝ)
    (H₁ : Type) [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (H₂ : Type) [NormedAddCommGroup H₂]
    [InnerProductSpace ℂ H₂] (π₁ : Matrix (Fin k) (Fin k) ℂ → (H₁ →L[ℂ] H₁))
    (π₂ : Matrix (Fin k) (Fin k) ℂ → (H₂ →L[ℂ] H₂)), _root_.Formalism.MainNotions.S.IsHCTypeU k u π₁ → _root_.Formalism.MainNotions.S.IsHCTypeU k u π₂ →
    ∃ A : H₁ ≃ₗ[ℂ] H₂, ∀ g ∈ Matrix.unitaryGroup (Fin k) ℂ, ∀ x, A (π₁ g x) = π₂ g (A x) := by
  intro k u H₁ _ _ H₂ _ _ π₁ π₂ h₁ h₂
  have h₁' : _root_.PI.UpqRep.IsHCTypeU k u π₁ := h₁
  have h₂' : _root_.PI.UpqRep.IsHCTypeU k u π₂ := h₂
  unfold _root_.PI.UpqRep.IsHCTypeU at h₁' h₂'
  obtain ⟨hnt₁, hfd₁, hπ₁, hK₁⟩ := h₁'
  obtain ⟨hnt₂, hfd₂, hπ₂, hK₂⟩ := h₂'
  obtain ⟨E₁, hrel₁, hder₁, hirr₁, x₁, hx₁, hw₁⟩ :=
    _root_.GlobalTheory.UnitaryHighestWeightUnique.exists_derived_highest hπ₁ hK₁
  obtain ⟨E₂, hrel₂, hder₂, hirr₂, x₂, hx₂, hw₂⟩ :=
    _root_.GlobalTheory.UnitaryHighestWeightUnique.exists_derived_highest hπ₂ hK₂
  obtain ⟨T, hT⟩ := _root_.GlobalTheory.exists_linearEquiv_of_irreducible_isHW H₁ H₂ k E₁ E₂ _ x₁ x₂ hrel₁ hrel₂
    hirr₁ hirr₂ hw₁ hw₂ hx₁ hx₂
  refine ⟨T, fun g hg x => ?_⟩
  have hL : _root_.Formalism.REAL.Jm (_root_.PI.UpqRep.allPos k) = 1 := by
    unfold _root_.Formalism.REAL.Jm _root_.PI.UpqRep.allPos
    simp
  have hgL : g ∈ _root_.Formalism.REAL.Kset (_root_.PI.UpqRep.allPos k) := by
    unfold _root_.Formalism.REAL.Kset
    simp only [hL, mul_one, one_mul, and_true]
    exact hg
  obtain ⟨Y, hY, hexp, -⟩ := _root_.Formalism.REAL.compact_exists_log_bounded _ g hgL
  have hskew : Yᴴ = -Y := by
    unfold _root_.Formalism.REAL.inK _root_.Formalism.REAL.inG at hY
    rw [hL] at hY
    simp only [mul_one, one_mul, and_true] at hY
    exact eq_neg_of_add_eq_zero_left hY
  let A₁ : H₁ →ₗ[ℂ] H₁ := ∑ a, ∑ b, Y a b • E₁ a b
  let A₂ : H₂ →ₗ[ℂ] H₂ := ∑ a, ∑ b, Y a b • E₂ a b
  have hA₁ : ∀ v, A₁ v = ∑ a, ∑ b, Y a b • E₁ a b v := by
    intro v; simp [A₁, LinearMap.sum_apply]
  have hA₂ : ∀ v, A₂ v = ∑ a, ∑ b, Y a b • E₂ a b v := by
    intro v; simp [A₂, LinearMap.sum_apply]
  have hTA : ∀ v, T.toLinearMap (A₁ v) = A₂ (T.toLinearMap v) := by
    intro v
    set_option synthInstance.maxHeartbeats 100000 in
      simp [hA₁, hA₂, map_sum, map_smul, hT]
  have key := _root_.GlobalTheory.UnitaryHighestWeightUnique.intertwine_group
    (fun t : ℝ => π₁ (NormedSpace.exp ((t : ℂ) • Y))) A₁
    (fun v => _root_.GlobalTheory.UnitaryHighestWeight.group_zero hπ₁ Y v)
    (fun s t v => _root_.GlobalTheory.UnitaryHighestWeight.group_add hπ₁ hskew s t v)
    (fun v => by rw [hA₁]; exact hder₁ Y hskew v)
    (fun t : ℝ => π₂ (NormedSpace.exp ((t : ℂ) • Y))) A₂
    (fun v => _root_.GlobalTheory.UnitaryHighestWeight.group_zero hπ₂ Y v)
    (fun s t v => _root_.GlobalTheory.UnitaryHighestWeight.group_add hπ₂ hskew s t v)
    (fun v => by rw [hA₂]; exact hder₂ Y hskew v)
    T.toLinearMap hTA x 1
  simpa [hexp] using key

end GlobalTheory.UnitaryHighestWeightUnique
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntertwinerOfSameHarishChandraParamUnitaryStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_intertwiner_of_same_harishChandraParam_unitary : ∀ (k : ℕ) (u : Fin k → ℝ) (H₁ : Type) [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (H₂ : Type) [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] (π₁ : Matrix (Fin k) (Fin k) ℂ → (H₁ →L[ℂ] H₁)) (π₂ : Matrix (Fin k) (Fin k) ℂ → (H₂ →L[ℂ] H₂)), Formalism.MainNotions.S.IsHCTypeU k u π₁ → Formalism.MainNotions.S.IsHCTypeU k u π₂ → ∃ A : H₁ ≃ₗ[ℂ] H₂, ∀ g ∈ Matrix.unitaryGroup (Fin k) ℂ, ∀ x, A (π₁ g x) = π₂ g (A x) := by
  first | exact @GlobalTheory.UnitaryHighestWeightUnique.exists_equiv_of_isHCTypeU | exact GlobalTheory.UnitaryHighestWeightUnique.exists_equiv_of_isHCTypeU | (intros; apply GlobalTheory.UnitaryHighestWeightUnique.exists_equiv_of_isHCTypeU <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChainStepVectorsAndAdjointVectorsAreTheta
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChainStepVectorsAndAdjointVectorsAreTheta
open Formalism.BasicNotions

namespace GlobalTheory.VecTheta

theorem vecThetaSD : ∀ D : D7, Formalism.IndefR.Fin.VecThetaSD D := fun _ =>
  ⟨fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => isThetaFunO_stepVec h,
    fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => isThetaFunO_thPVec h⟩

end GlobalTheory.VecTheta
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChainStepVectorsAndAdjointVectorsAreThetaStatement
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chainStepVectors_and_adjointVectors_areTheta : ∀ D : D7, Formalism.IndefR.Fin.VecThetaSD D := by
  first | exact @GlobalTheory.VecTheta.vecThetaSD | exact GlobalTheory.VecTheta.vecThetaSD | (intros; apply GlobalTheory.VecTheta.vecThetaSD <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompMemGinfC
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.LocWeil
open Formalism.MainNotions.KudlaSiegelWeil (Pl FinF FinE FF Over Split LocW Restr IntV)
open GlobalTheory.IndefiniteRowSideFullHecke.SymplecticTensorMeasures (ConjIsom basConj omTens toHom)
open Formalism.IndefR.Datum (IsHalf IsLatVac)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocWeil.CompactPart

variable {D : D7}

theorem infMat_eq (V : HSp D) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (g : GA D V) :
    infMat D.sp.cm.sig V.gram θ g = (infHom V g).1.map θ := rfl

theorem infMat_of_fin (V : HSp D) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) {k : GA D V} (hk : k ∈ GfC V) :
    infMat D.sp.cm.sig V.gram θ k = 1 := by
  have hk' : infHom V k = 1 := hk
  rw [infMat_eq V, hk', Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

end GlobalTheory.LocWeil.CompactPart

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VolumesAgreeAdelicOfTrueVolume
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VolumesAgreeAdelicOfTrueVolume
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.Vol

theorem volTieG_of_trueVol : ∀ D : D7, letI := D.host.cmStar;
    (∀ W, D.vol W = trueVol D.sp.cm (Formalism.BasicNotions.TH.tauE D) D.cd W) → Formalism.L2.Theta.VolTieG D := by
  intro D
  letI := D.host.cmStar
  intro h
  rw [volTieG_iff]
  intro W hW
  rw [h W]
  exact GlobalTheory.T.unitaryAdelicQuotientVolume_is_volume _ _ D.sp.cm _ _ D.cd W (isCMFam_host _ D.host _ D.eTau) hW

end GlobalTheory.Mem.Vol
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VolumesAgreeAdelicOfTrueVolumeStatement
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.volumesAgreeAdelic_of_trueVolume : ∀ D : D7, letI := D.host.cmStar; (∀ W, D.vol W = trueVol D.sp.cm (Formalism.BasicNotions.TH.tauE D) D.cd W) → Formalism.L2.Theta.VolTieG D := by
  first | exact @GlobalTheory.Mem.Vol.volTieG_of_trueVol | exact GlobalTheory.Mem.Vol.volTieG_of_trueVol | (intros; apply GlobalTheory.Mem.Vol.volTieG_of_trueVol <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHarishChandraTypeDualWeylModuleFockNorm
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHarishChandraTypeDualWeylModuleFockNorm
open MvPolynomial Formalism.BasicNotions Formalism.MainNotions.S GlobalTheory.DualWeyl GlobalTheory.CompactDS
open Formalism.GradedWeylDivisibility (rowAct rowDeg)
open scoped Matrix

noncomputable section

namespace GlobalTheory.NablaType

variable {n : ℕ}

theorem cdom_of_partial_sums (μ ν : Fin n → ℕ)
    (h : ∀ k : ℕ, (∑ a : Fin n with a.val < k, μ a) ≤ ∑ a : Fin n with a.val < k, ν a)
    (he : ∑ a, μ a = ∑ a, ν a) : CDom (allPos n) (fun a => (μ a : ℝ)) (fun a => (ν a : ℝ)) := by
  classical
  let D : ℕ → ℕ := fun k => (∑ a : Fin n with a.val < k, ν a) - ∑ a : Fin n with a.val < k, μ a
  have hD : ∀ k, (D k : ℝ) = ∑ a : Fin n, if a.val < k then ((ν a : ℝ) - μ a) else 0 := by
    intro k
    simp only [D]
    rw [Nat.cast_sub (h k), ← Finset.sum_filter, Finset.sum_sub_distrib]
    push_cast
    rfl
  have hstep : ∀ i : Fin n, (D (i.val + 1) : ℝ) - D i.val = (ν i : ℝ) - μ i := by
    intro i
    rw [hD, hD, ← Finset.sum_sub_distrib, Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      have : b.val ≠ i.val := fun e => hb (Fin.ext e)
      by_cases h1 : b.val < i.val
      · rw [if_pos h1, if_pos (by omega), sub_self]
      · rw [if_neg h1, if_neg (by omega), sub_self]
    · simp
  have h0 : D 0 = 0 := by simp [D]
  have hn : D n = 0 := by simp [D, he]
  refine ⟨fun a b => if b.val = a.val + 1 then D b.val else 0, fun a b hab => ?_, ?_⟩
  · have : b.val = a.val + 1 := by by_contra h'; exact hab (if_neg h')
    exact ⟨Fin.lt_def.2 (by omega), rfl⟩
  · funext i
    have e1 : ∑ b : Fin n, ((if b.val = i.val + 1 then D b.val else 0 : ℕ) : ℝ) = D (i.val + 1) := by
      by_cases hi : i.val + 1 < n
      · rw [Finset.sum_eq_single ⟨i.val + 1, hi⟩]
        · simp
        · intro b _ hb
          rw [if_neg (fun e => hb (Fin.ext e)), Nat.cast_zero]
        · simp
      · rw [Finset.sum_eq_zero, show i.val + 1 = n by omega, hn, Nat.cast_zero]
        intro b _
        rw [if_neg (by omega), Nat.cast_zero]
    have e2 : ∑ a : Fin n, ((if i.val = a.val + 1 then D i.val else 0 : ℕ) : ℝ) = D i.val := by
      by_cases hi : 0 < i.val
      · rw [Finset.sum_eq_single ⟨i.val - 1, by omega⟩]
        · rw [if_pos (by simp only; omega)]
        · intro b _ hb
          rw [if_neg (fun e => hb (Fin.ext (by simp only; omega))), Nat.cast_zero]
        · simp
      · rw [Finset.sum_eq_zero, show i.val = 0 by omega, h0, Nat.cast_zero]
        intro b _
        rw [if_neg (by omega), Nat.cast_zero]
    rw [Pi.sub_apply, ← hstep, ← e1, ← e2]
    simp only [Finset.sum_apply, Pi.smul_apply, Formalism.REAL.root, Pi.sub_apply, smul_eq_mul, mul_sub,
      Finset.sum_sub_distrib, Pi.single_apply, mul_ite, mul_one, mul_zero]
    congr 1
    · rw [Finset.sum_comm]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    · simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem cdom_of_coeff_ne_zero {la : Fin n → ℕ} {f : Pol n ℂ} (hf : f ∈ nabla la ℂ) (m : Fin n × Fin n →₀ ℕ)
    (hm : AddMonoidAlgebra.coeff f m ≠ 0) : CDom (allPos n) (fun a => (rowDeg m a : ℝ)) (fun a => (la a : ℝ)) := by
  unfold nabla at hf
  rw [Formalism.GradedWeylDivisibility.standardMonomialSpanDomain ℂ n n la] at hf
  by_contra hc
  apply hm
  clear hm
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨K, sz, hsz, I, rfl, rfl⟩ := hx
    by_contra h0
    obtain ⟨h1, h2⟩ := Formalism.GradedWeylDivisibility.bidetDominance ℂ n n K sz hsz I m (mem_support_iff.2 h0)
    exact hc (cdom_of_partial_sums _ _ h1 h2)
  | zero => simp
  | add x y _ _ hx hy => rw [MvPolynomial.coeff_add, hx, hy, add_zero]
  | smul c x _ hx => rw [coeff_smul, hx, smul_zero]

def act (lam : DomWeight n) (g : Matrix (Fin n) (Fin n) ℂ) : Space lam.natW →L[ℂ] Space lam.natW :=
  LinearMap.toContinuousLinearMap
    ((g.det ^ lam.detShift) • ((toSpace lam.natW).conj (rho lam.natW ℂ g)))

def incl (lam : DomWeight n) : Space lam.natW →ₗ[ℂ] Pol n ℂ :=
  (nabla lam.natW ℂ).subtype ∘ₗ (toSpace lam.natW).symm.toLinearMap

theorem incl_injective (lam : DomWeight n) : Function.Injective (incl lam) :=
  (nabla lam.natW ℂ).injective_subtype.comp (toSpace lam.natW).symm.injective

theorem incl_mem (lam : DomWeight n) (x : Space lam.natW) : incl lam x ∈ nabla lam.natW ℂ :=
  ((toSpace lam.natW).symm x).2

theorem incl_act (lam : DomWeight n) (g : Matrix (Fin n) (Fin n) ℂ) (x : Space lam.natW) :
    incl lam (act lam g x) = (g.det ^ lam.detShift) • rowAct ℂ gᵀ (incl lam x) := rfl

theorem act_unitary (lam : DomWeight n) (u : UN n) (x : Space lam.natW) :
    act lam u.1 x = (u.1.det ^ lam.detShift) • rhoSpace lam.natW u x := rfl

theorem det_ne_zero {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Matrix.unitaryGroup (Fin n) ℂ) : g.det ≠ 0 :=
  (Matrix.UnitaryGroup.det_isUnit ⟨g, hg⟩).ne_zero

theorem isURepOn_act (lam : DomWeight n) : IsURepOn (UJset (allPos n)) (act lam) := by
  rw [ujset_eq]
  refine ⟨⟨?_, fun a _ b _ => ?_⟩, fun g hg v => ?_, fun v => ?_⟩
  · ext x
    apply incl_injective
    rw [incl_act, Matrix.transpose_one, Formalism.GradedWeylDivisibility.ldlat_rowAct_one]
    simp
  · ext x
    apply incl_injective
    rw [ContinuousLinearMap.comp_apply, incl_act, incl_act, incl_act, Matrix.transpose_mul,
      ← Formalism.GradedWeylDivisibility.rowActMul ℂ n n, Matrix.det_mul, mul_zpow, map_smul, smul_smul]
    rfl
  · have h1 : ‖g.det‖ = 1 := CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary hg)
    rw [act_unitary lam ⟨g, hg⟩, norm_smul, norm_zpow, h1, one_zpow, one_mul, norm_rhoSpace]
  · rw [continuousOn_iff_continuous_restrict]
    have h1 : Continuous fun u : UN n => u.1.det ^ lam.detShift :=
      (continuous_subtype_val.matrix_det).zpow₀ _ fun u => Or.inl (det_ne_zero u.2)
    exact h1.smul (continuous_rhoSpace v)

theorem coeff_torus (lam : DomWeight n) (θ : Fin n → ℝ) (x : Space lam.natW) (m : Fin n × Fin n →₀ ℕ) :
    AddMonoidAlgebra.coeff (incl lam (act lam (torus θ) x)) m =
      chr (fun a => (rowDeg m a : ℝ) + lam.detShift) θ * AddMonoidAlgebra.coeff (incl lam x) m := by
  rw [incl_act, torus, Matrix.diagonal_transpose, coeff_smul, Formalism.GradedWeylDivisibility.ldrow_coeff_rowAct_diag, Matrix.det_diagonal,
    smul_eq_mul, mul_left_comm, mul_comm]
  congr 1
  simp only [← Complex.exp_nat_mul]
  rw [chr, ← Complex.exp_sum, ← Complex.exp_sum, ← Complex.exp_int_mul, ← Complex.exp_add]
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => by ring

theorem natW_add (lam : DomWeight n) (a : Fin n) : (lam.natW a : ℝ) + lam.detShift = lam.w a := by
  exact_mod_cast (factNatW n lam).2.1 a

theorem isKTypeOf_act (lam : DomWeight n) : IsKTypeOf (allPos n) (act lam) (fun a => (lam.w a : ℝ)) ⊤ := by
  have ha := (factNatW n lam).1
  refine ⟨inferInstance, fun _ _ _ _ => trivial, fun S _ hS => ?_, ?_, fun μ v _ hv hw => ?_⟩
  · by_cases h0 : S = ⊥
    · exact Or.inl h0
    right
    have hU : ∀ u ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ f ∈ S.map (incl lam), rowAct ℂ u f ∈ S.map (incl lam) := by
      rintro u hu _ ⟨f, hf, rfl⟩
      have hu' := transpose_mem_unitaryGroup hu
      have h1 : incl lam (act lam uᵀ f) ∈ S.map (incl lam) := ⟨_, hS _ (by rw [kset_eq]; exact hu') f hf, rfl⟩
      rw [incl_act, Matrix.transpose_transpose] at h1
      exact (Submodule.smul_mem_iff _ (zpow_ne_zero _ (det_ne_zero hu'))).1 h1
    have hcl := GlobalTheory.Branching.rowDivClosed_of_rowAct_stable _ (GlobalTheory.Branching.rowAct_mem_of_unitary_stable _ hU)
    have hne : S.map (incl lam) ≠ ⊥ := fun e => h0 (Submodule.map_injective_of_injective (incl_injective lam)
      (e.trans (Submodule.map_bot _).symm))
    have hle := GlobalTheory.Branching.dualWeyl_le_of_rowDivClosed le_rfl lam.natW ha _
      (by rintro _ ⟨f, -, rfl⟩; exact incl_mem lam f) hcl hne
    refine eq_top_iff.2 fun f _ => ?_
    obtain ⟨g, hg, e⟩ := hle (incl_mem lam f)
    rwa [← incl_injective lam e]
  · refine ⟨toSpace _ ⟨_, extremal_mem ha⟩, trivial, fun h => ?_, fun θ _ => ?_⟩
    · exact extremal_ne_zero (congrArg (incl lam) h)
    · apply incl_injective
      ext m
      have h1 := coeff_torus lam θ (toSpace _ ⟨_, extremal_mem ha⟩) m
      refine h1.trans ?_
      rw [map_smul, coeff_smul, smul_eq_mul]
      by_cases hm : AddMonoidAlgebra.coeff (incl lam (toSpace _ ⟨_, extremal_mem ha⟩)) m = 0
      · rw [hm, mul_zero, mul_zero]
      have h2 := Formalism.GradedWeylDivisibility.hwRowWeight ℂ n n le_rfl lam.natW ha hm
      have h3 : (fun a => (rowDeg m a : ℝ) + lam.detShift) = fun a => (lam.w a : ℝ) := by
        funext a
        rw [← natW_add, ← Formalism.GradedWeylDivisibility.ldrow_weight_rowW, h2]
        simp [Formalism.GradedWeylDivisibility.rowNu]
      rw [h3]
      rfl
  · have h0 : incl lam v ≠ 0 := fun e => hv (incl_injective lam (e.trans (map_zero _).symm))
    obtain ⟨m, hm⟩ := ne_zero_iff.1 h0
    have h1 : μ = fun a => (rowDeg m a : ℝ) + lam.detShift := by
      refine chr_inj fun θ => ?_
      have h2 := coeff_torus lam θ v m
      have h3 : act lam (torus θ) v = chr μ θ • v := hw θ (by rw [kset_eq]; exact torus_mem θ)
      rw [h3, map_smul, coeff_smul, smul_eq_mul] at h2
      exact mul_right_cancel₀ hm h2
    have h4 := cdom_add (cdom_of_coeff_ne_zero (incl_mem lam v) m hm)
      (cdom_refl (allPos n) fun _ => (lam.detShift : ℝ))
    rw [h1]
    have h5 : (fun a => (lam.w a : ℝ)) = (fun a => (lam.natW a : ℝ)) + fun _ => (lam.detShift : ℝ) :=
      funext fun a => (natW_add lam a).symm
    rw [h5]
    exact h4

theorem exists_isHCTypeU_nablaSq : ∀ (n : ℕ) (lam : Formalism.BasicNotions.DomWeight n), ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (e : H →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ), Formalism.MainNotions.S.IsHCTypeU n (fun i => (lam.w i : ℝ) + ((Formalism.BasicNotions.rhoVec n i : ℚ) : ℝ)) π ∧ Function.Injective e ∧ (∀ x, e x ∈ Formalism.BasicNotions.nablaSq ℂ n lam) ∧ ∀ g : GL (Fin n) ℂ, (g : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ → ∀ x, e (π (g : Matrix (Fin n) (Fin n) ℂ) x) = Formalism.BasicNotions.sqAct ℂ n lam g (e x) := by
  intro n lam
  have hK := isKTypeOf_act lam
  refine ⟨Space lam.natW, inferInstance, inferInstance, act lam, incl lam,
    ⟨?_, inferInstance, isURepOn_act lam, ?_⟩, incl_injective lam, incl_mem lam, fun g _ x => ?_⟩
  · obtain ⟨v, -, hv, -⟩ := hK.2.2.2.1
    exact ⟨v, 0, hv⟩
  · convert hK using 1
    funext a
    unfold allPos
    rw [GlobalTheory.DefiniteCheck.lowK_const]
    simp [rhoVec]
  · rw [incl_act]
    simp [sqAct, detPow]

end GlobalTheory.NablaType
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHarishChandraTypeDualWeylModuleFockNormStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_harishChandraType_dualWeylModuleFockNorm : ∀ (n : ℕ) (lam : Formalism.BasicNotions.DomWeight n), ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (e : H →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ), Formalism.MainNotions.S.IsHCTypeU n (fun i => (lam.w i : ℝ) + ((Formalism.BasicNotions.rhoVec n i : ℚ) : ℝ)) π ∧ Function.Injective e ∧ (∀ x, e x ∈ Formalism.BasicNotions.nablaSq ℂ n lam) ∧ ∀ g : GL (Fin n) ℂ, (g : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ → ∀ x, e (π (g : Matrix (Fin n) (Fin n) ℂ) x) = Formalism.BasicNotions.sqAct ℂ n lam g (e x) := by
  first | exact @GlobalTheory.NablaType.exists_isHCTypeU_nablaSq | exact GlobalTheory.NablaType.exists_isHCTypeU_nablaSq | (intros; apply GlobalTheory.NablaType.exists_isHCTypeU_nablaSq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColNormExistsImNeZero
open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links NumberField GlobalTheory.Mem.SJ
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SJ

theorem colNorm_exists_im_ne_zero {K : Type} [Field K] [_root_.NumberField.IsTotallyComplex K] (σ : K →+* ℂ) :
    ∃ a, (σ a).im ≠ 0 := by
  by_contra h
  push Not at h
  refine IsTotallyComplex.complexEmbedding_not_isReal σ ?_
  rw [ComplexEmbedding.isReal_iff]
  ext a
  rw [ComplexEmbedding.conjugate_coe_eq]
  exact Complex.conj_eq_iff_im.2 (h a)

theorem colNorm_normAt_column (D : D7) (u : D.what₂.Word) (x : (D.div.Nu u).V) :
    Formalism.HermitianLatticesTheory.normAt (D.div.Nu u).b (D.div.Nu u).X (InfinitePlace.mk D.what₂.embLL) x = ‖D.jN u x‖ := by
  rw [D.nuIn_norm, normAt_sq_eq_majAt_re, (D.fm u).emb_norm, ← D.nuIn_jN, norm_eq_sqrt_re_inner (𝕜 := ℂ), D.eMu_isom]
  rfl

theorem colNorm_of_nuTie : ∀ (D : D7) (Bs : DefBase D.what₂.LL) (A : DefAmb Bs) (X : CxData A) (fc : DefSub A → DefFace Bs) (s : Bool) (R : Read D X fc s) (cr : Crd A fc) (M : Seam R cr), R.NuTie → M.ColNorm := by
  intro D Bs A X fc s R cr M h u
  obtain ⟨L, hL⟩ := h u
  refine ⟨1, one_pos, fun φ => ?_⟩
  rw [one_mul]
  have htw : ∀ a, (InfinitePlace.mk D.what₂.embLL).embedding a = cj s (D.what₂.embLL a) := by
    rw [← R.v0]; exact R.twist
  have := fnorm_cjv_eq_norm D.what₂.LL D.what₂.embLL s htw (colNorm_exists_im_ne_zero _) (D.div.Nu u) _ L _ (R.eNu u) hL
    (D.what₂.Mu u) (D.jN u) (M.cφ u) (colNorm_normAt_column D u) (M.cφ_eq u) φ
  rw [← R.v0] at this
  exact this

end GlobalTheory.Mem.SJ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SobolevContinuousFormSumLieWordInner
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SobolevContinuousFormSumLieWordInner
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmVec

theorem exists_factor_of_bound {V E : Type} [AddCommGroup V] [Module ℂ V] [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Φ : V →ₗ[ℂ] E) (ℓ : V →ₗ[ℂ] ℂ) (C : ℝ) (h : ∀ w, ‖ℓ w‖ ≤ C * ‖Φ w‖) :
    ∃ Λ : E →L[ℂ] ℂ, ∀ w, Λ (Φ w) = ℓ w := by
  have hk : LinearMap.ker Φ ≤ LinearMap.ker ℓ := fun w hw => by
    have := h w
    rw [LinearMap.mem_ker.1 hw, norm_zero, mul_zero] at this
    exact norm_le_zero_iff.1 this
  let f₀ : LinearMap.range Φ →ₗ[ℂ] ℂ := (LinearMap.ker Φ).liftQ ℓ hk ∘ₗ Φ.quotKerEquivRange.symm.toLinearMap
  have hf : ∀ w, f₀ ⟨Φ w, LinearMap.mem_range_self Φ w⟩ = ℓ w := fun w => by
    simp only [f₀, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  have hb : ∀ x, ‖f₀ x‖ ≤ C * ‖x‖ := by
    rintro ⟨_, w, rfl⟩
    exact (congrArg norm (hf w)).le.trans (h w)
  obtain ⟨g, hg, -⟩ := exists_extension_norm_eq (LinearMap.range Φ) (f₀.mkContinuous C hb)
  exact ⟨g, fun w => (hg ⟨Φ w, LinearMap.mem_range_self Φ w⟩).trans (hf w)⟩

theorem exists_inner_of_pi {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {m : ℕ}
    (Λ : (Fin m → H) →L[ℂ] ℂ) : ∃ a : Fin m → H, ∀ x, Λ x = ∑ i, ⟪a i, x i⟫_ℂ := by
  refine ⟨fun i => (InnerProductSpace.toDual ℂ H).symm (Λ.comp (ContinuousLinearMap.single ℂ (fun _ => H) i)),
    fun x => ?_⟩
  simp only [InnerProductSpace.toDual_symm_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.single_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum, Finset.univ_sum_single]

theorem sobCont_repr : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → ∀ ℓ : H →ₗ[ℂ] ℂ, Sobolev₂ (lieG G) (trRep σ P) ℓ → ∃ (m : ℕ) (ls : Fin m → List (Matrix (Fin n) (Fin n) ℂ)) (a : Fin m → H), (∀ i, ∀ X ∈ ls i, X ∈ lieG G) ∧ ∀ w ∈ smSub G (trRep σ P), ℓ w = ∑ i, ⟪a i, word (trRep σ P) (ls i) w⟫_ℂ := by
  intro n ε H _ _ _ σ P G hP h hσ ℓ ⟨S, C, hS, hC⟩
  have hG := gram_unit hP h
  have hπ := isURepOn_trRep hP h hσ
  have hl : ∀ i : Fin S.length, ∀ X ∈ S.get i, X ∈ lieG G := fun i => hS _ (List.get_mem S i)
  let Φ : smSub G (trRep σ P) →ₗ[ℂ] (Fin S.length → H) :=
    { toFun := fun w i => word (trRep σ P) (S.get i) w
      map_add' := fun v w => funext fun i => word_add hG hπ (hl i) v.2 w.2
      map_smul' := fun c w => funext fun i => word_smul hG hπ (hl i) c w.2 }
  have hb : ∀ w, ‖(ℓ ∘ₗ (smSub G (trRep σ P)).subtype) w‖ ≤ (|C| * S.length) * ‖Φ w‖ := fun w => by
    refine (hC w w.2).trans ?_
    have h1 : (S.map fun l => ‖List.foldr (dRep (trRep σ P)) (w : H) l‖).sum ≤ S.length * ‖Φ w‖ := by
      have := List.sum_le_card_nsmul (S.map fun l => ‖List.foldr (dRep (trRep σ P)) (w : H) l‖) ‖Φ w‖ (by
        intro x hx
        obtain ⟨l, hl', rfl⟩ := List.mem_map.1 hx
        obtain ⟨i, rfl⟩ := List.get_of_mem hl'
        exact norm_le_pi_norm (Φ w) i)
      simpa using this
    have h0 : 0 ≤ (S.map fun l => ‖List.foldr (dRep (trRep σ P)) (w : H) l‖).sum :=
      List.sum_nonneg fun x hx => by
        obtain ⟨l, -, rfl⟩ := List.mem_map.1 hx
        exact norm_nonneg _
    rw [mul_assoc]
    exact mul_le_mul (le_abs_self C) h1 h0 (abs_nonneg C)
  obtain ⟨Λ, hΛ⟩ := exists_factor_of_bound Φ _ _ hb
  obtain ⟨a, ha⟩ := exists_inner_of_pi Λ
  exact ⟨S.length, S.get, a, hl, fun w hw => (hΛ ⟨w, hw⟩).symm.trans (ha _)⟩

end GlobalTheory.SmVec
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SobolevContinuousFormSumLieWordInnerStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sobolevContinuousForm_sum_lieWord_inner : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → ∀ ℓ : H →ₗ[ℂ] ℂ, Sobolev₂ (lieG G) (trRep σ P) ℓ → ∃ (m : ℕ) (ls : Fin m → List (Matrix (Fin n) (Fin n) ℂ)) (a : Fin m → H), (∀ i, ∀ X ∈ ls i, X ∈ lieG G) ∧ ∀ w ∈ smSub G (trRep σ P), ℓ w = ∑ i, ⟪a i, word (trRep σ P) (ls i) w⟫_ℂ := by
  first | exact @GlobalTheory.SmVec.sobCont_repr | exact GlobalTheory.SmVec.sobCont_repr | (intros; apply GlobalTheory.SmVec.sobCont_repr <;> assumption)
end
end
