module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.ExistsNatSmulSingle
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiCongrLeftUpdate

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelIteratedIntegralsSwap
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelIteratedIntegralsSwap
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.ThetaSwap

open GlobalTheory.Grow GlobalTheory.Size

variable {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} {f : WO S T → ℂ}

theorem thetaKO_left_fst (hω : IsWeilDatumO ψ S T χS χT om) (hf : IsThetaFunO ψ S T f) :
    ∀ γ ∈ GQ S, ∀ g h, thetaKO om (γ * g) h f = thetaKO om g h f := fun γ hγ g h => by
  have e : ((γ * g, h) : GA D S × GA D T) = (γ, 1) * (g, h) := by simp
  unfold thetaKO
  rw [e, map_mul]
  exact hω.om_aut γ hγ 1 (one_mem _) _ (hω.om_pres _ _ hf)

theorem thetaKO_le_quotHeight {θ : InfFam D} (hθ : IsInfFam θ) (hω : IsWeilDatumO ψ S T χS χT om)
    (hf : IsThetaFunO ψ S T f) :
    ∃ (K : ℝ) (A : ℕ), 0 ≤ K ∧ ∀ g h, ‖thetaKO om g h f‖ ≤ K * (quotHeight S g * quotHeight T h) ^ A := by
  obtain ⟨A, d, H⟩ := GlobalTheory.KernelSeminorm.thetaGrowth D S.rank T.rank
  obtain ⟨U, hU, hl⟩ := isTheta_iff_level.1 hf
  obtain ⟨μ, 𝓕, hμ⟩ := exists_isCovolOne S T
  obtain ⟨C, hC0, hC⟩ := (H S T rfl rfl).real ψ hθ hU
  have hb := (hC χS χT om hω μ 𝓕 hμ f hl).2
  have hK : 0 ≤ C * (sobO ψ θ μ 𝓕 d f).toReal * 4 ^ A := by positivity
  refine ⟨_, A, hK, fun g h => ?_⟩
  obtain ⟨γ, hγ, h1⟩ := exists_height_le_two_mul_quotHeight S g
  obtain ⟨γ', hγ', h2⟩ := exists_height_le_two_mul_quotHeight T h
  rw [← thetaKO_left_fst hω hf γ hγ g h, ← GlobalTheory.Chain.LiftConv.thetaKO_left hω hf (γ * g) γ' hγ' h]
  refine (hb _ _).trans ?_
  have e : C * (sobO ψ θ μ 𝓕 d f).toReal * 4 ^ A * (quotHeight S g * quotHeight T h) ^ A =
      C * (sobO ψ θ μ 𝓕 d f).toReal * (2 * quotHeight S g * (2 * quotHeight T h)) ^ A := by ring
  rw [e]
  refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_pos (height_pos S _) (height_pos T _)).le
    (mul_le_mul h1 h2 (height_pos T _).le (by linarith [quotHeight_pos S g])) A) (by positivity)

end GlobalTheory.ChainOnto.ThetaSwap

namespace GlobalTheory.ChainOnto.ThetaSwap

open GlobalTheory.Grow GlobalTheory.Size

theorem integrable_prod {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hθ : IsInfFam θ) (hω : IsWeilDatumO ψ S T χS χT om)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) {ν : Measure (GA D S)} {X : Set (GA D S)} {ν' : Measure (GA D T)}
    {X' : Set (GA D T)} (hν : ν.IsHaarMeasure) (hX : IsFundamentalDomain (GQ S) X ν) (hν' : ν'.IsHaarMeasure)
    (hX' : IsFundamentalDomain (GQ T) X' ν') {G : GA D S → ℂ} {F : GA D T → ℂ} (hG : RapidDec S G)
    (hF : RapidDec T F) :
    Integrable (Function.uncurry fun (h : GA D T) (g : GA D S) => thetaKO om g h f * F h * conj (G g))
      ((ν'.restrict X').prod (ν.restrict X)) := by
  obtain ⟨-, -, -, hS2, hSB⟩ := Formalism.IndefR.Eqv.ga_facts D S
  obtain ⟨-, -, -, hT2, hTB⟩ := Formalism.IndefR.Eqv.ga_facts D T
  have : IsFiniteMeasure (ν.restrict X) :=
    isFiniteMeasure_restrict.2 (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol S ν X hν hX).ne
  have : IsFiniteMeasure (ν'.restrict X') :=
    isFiniteMeasure_restrict.2 (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol T ν' X' hν' hX').ne
  obtain ⟨K, A, hK, hb⟩ := thetaKO_le_quotHeight hθ hω hf
  obtain ⟨B, hB⟩ := hG.decay A
  obtain ⟨B', hB'⟩ := hF.decay A
  have hc : Continuous (Function.uncurry fun (h : GA D T) (g : GA D S) => thetaKO om g h f * F h * conj (G g)) := by
    have h1 : Continuous fun p : GA D T × GA D S => thetaKO om p.2 p.1 f :=
      (hω.om_cont f hf 0).comp (continuous_snd.prodMk continuous_fst)
    exact (h1.mul (hF.continuous.comp continuous_fst)).mul
      (Complex.continuous_conj.comp (hG.continuous.comp continuous_snd))
  refine Integrable.of_bound hc.aestronglyMeasurable (K * B * B') (.of_forall fun p => ?_)
  obtain ⟨h, g⟩ := p
  have hq := (pow_pos (quotHeight_pos S g) A).le
  have hq' := (pow_pos (quotHeight_pos T h) A).le
  have hB0 : 0 ≤ B := (mul_nonneg (norm_nonneg _) hq).trans (hB g)
  calc ‖Function.uncurry (fun (h : GA D T) (g : GA D S) => thetaKO om g h f * F h * conj (G g)) (h, g)‖
        = ‖thetaKO om g h f‖ * ‖F h‖ * ‖G g‖ := by simp [Function.uncurry, norm_mul]
    _ ≤ K * (quotHeight S g * quotHeight T h) ^ A * ‖F h‖ * ‖G g‖ := by gcongr; exact hb g h
    _ = K * (‖G g‖ * quotHeight S g ^ A) * (‖F h‖ * quotHeight T h ^ A) := by ring
    _ ≤ K * B * B' := by
        gcongr
        · exact hB g
        · exact hB' h

theorem integral_swap : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsInfFam θ →
    IsWeilDatumO ψ S T χS χT om → ∀ f, IsThetaFunO ψ S T f → ∀ (ν : Measure (GA D S)) (X : Set (GA D S))
    (ν' : Measure (GA D T)) (X' : Set (GA D T)), ν.IsHaarMeasure → IsFundamentalDomain (GQ S) X ν →
    ν'.IsHaarMeasure → IsFundamentalDomain (GQ T) X' ν' → ∀ (G : GA D S → ℂ) (F : GA D T → ℂ),
    GlobalTheory.Grow.RapidDec S G → GlobalTheory.Grow.RapidDec T F →
    ∫ h in X', ∫ g in X, thetaKO om g h f * F h * conj (G g) ∂ν ∂ν' =
      ∫ g in X, ∫ h in X', thetaKO om g h f * F h * conj (G g) ∂ν' ∂ν := by
  intro D ψ θ S T χS χT om hθ hω f hf ν X ν' X' hν hX hν' hX' G F hG hF
  have : IsFiniteMeasure (ν.restrict X) :=
    isFiniteMeasure_restrict.2 (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol S ν X hν hX).ne
  have : IsFiniteMeasure (ν'.restrict X') :=
    isFiniteMeasure_restrict.2 (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol T ν' X' hν' hX').ne
  exact integral_integral_swap (integrable_prod hθ hω hf hν hX hν' hX' hG hF)

end GlobalTheory.ChainOnto.ThetaSwap
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelIteratedIntegralsSwapStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaKernel_iterated_integrals_swap : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsInfFam θ → IsWeilDatumO ψ S T χS χT om → ∀ f, IsThetaFunO ψ S T f → ∀ (ν : Measure (GA D S)) (X : Set (GA D S)) (ν' : Measure (GA D T)) (X' : Set (GA D T)), ν.IsHaarMeasure → IsFundamentalDomain (GQ S) X ν → ν'.IsHaarMeasure → IsFundamentalDomain (GQ T) X' ν' → ∀ (G : GA D S → ℂ) (F : GA D T → ℂ), GlobalTheory.Grow.RapidDec S G → GlobalTheory.Grow.RapidDec T F → ∫ h in X', ∫ g in X, thetaKO om g h f * F h * conj (G g) ∂ν ∂ν' = ∫ g in X, ∫ h in X', thetaKO om g h f * F h * conj (G g) ∂ν' ∂ν := by
  first | exact @GlobalTheory.ChainOnto.ThetaSwap.integral_swap | exact GlobalTheory.ChainOnto.ThetaSwap.integral_swap | (intros; apply GlobalTheory.ChainOnto.ThetaSwap.integral_swap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasIwasawaDecompositionDoubledSplitPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasIwasawaDecompositionDoubledSplitPlace
noncomputable section

namespace GlobalTheory.Core.Rk.IwSplit

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling
open Formalism.UG (bc stabGL GLint cT)

section Pure

variable {A : Type} [CommRing A] {m ι : Type} [Fintype m] [Fintype ι] [DecidableEq m] [DecidableEq ι] (e : m ⊕ m ≃ ι)

def shear : GL ι A :=
  ⟨(Matrix.fromBlocks 1 0 1 1).submatrix e.symm e.symm, (Matrix.fromBlocks 1 0 (-1) 1).submatrix e.symm e.symm,
    by rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]; simp,
    by rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]; simp⟩

theorem shear_mulVec (x y : m → A) : (shear e).1 *ᵥ pairVec e x y = pairVec e x (x + y) := by
  simp [mulVec_pairVec, shear]

theorem bc_shear {B : Type} [CommRing B] (f : A →+* B) : bc f (shear e) = shear e :=
  Units.ext (by
    change ((Matrix.fromBlocks 1 0 1 1).submatrix e.symm e.symm).map f =
      (Matrix.fromBlocks 1 0 1 1).submatrix e.symm e.symm
    simp [← Matrix.submatrix_map, Matrix.fromBlocks_map])

omit [DecidableEq m] [DecidableEq ι] in
theorem pair_dblGram (J : Matrix m m A) (x y x' y' : m → A) :
    pairVec e x y ⬝ᵥ dblGram e J *ᵥ pairVec e x' y' = x ⬝ᵥ J *ᵥ x' - y ⬝ᵥ J *ᵥ y' := by
  rw [dblGram, blkMat_mulVec, Matrix.neg_mulVec]
  simp [dotProduct, ← e.sum_comp, sub_eq_add_neg]

theorem keepsDiag_of_pairing {J : Matrix m m A} (hJ : IsUnit J.det) {x : Matrix ι ι A} {y : GL ι A}
    (h : ∀ u' u, (x *ᵥ u') ⬝ᵥ dblGram e J *ᵥ (y.1 *ᵥ u) = u' ⬝ᵥ dblGram e J *ᵥ u) (hy : y ∈ stabGL (diagSub A e)) :
    KeepsDiag e x := by
  refine keepsDiag_of_mulVec fun w hw => ?_
  obtain ⟨a, rfl⟩ := (mem_diagSub e).1 hw
  obtain ⟨s, t, hst⟩ : ∃ s t, x *ᵥ pairVec e a a = pairVec e s t := ⟨_, _, (pairVec_eta e _).symm⟩
  rw [hst, pairVec_mem_diagSub, ← sub_eq_zero]
  have h1 : ∀ b, (s - t) ⬝ᵥ J *ᵥ b = 0 := fun b => by
    obtain ⟨c, hc⟩ := (mem_diagSub e).1 ((inv_mem hy (pairVec e b b)).1 ((pairVec_mem_diagSub e).2 rfl))
    have h2 := h (pairVec e a a) ((y⁻¹).1 *ᵥ pairVec e b b)
    rw [Matrix.mulVec_mulVec _ y.1, Units.mul_inv, Matrix.one_mulVec, hst, hc, pair_dblGram, pair_dblGram,
      sub_self] at h2
    rw [sub_dotProduct, h2]
  funext i
  have h3 := h1 (J⁻¹ *ᵥ Pi.single i 1)
  rwa [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hJ, Matrix.one_mulVec, dotProduct_single, mul_one] at h3

end Pure

theorem iwasawa_diag {V K : Type} [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K]
    [IsFractionRing V K] {n : ℕ} (x : GL (Fin (n + n)) K) : ∃ k : GL (Fin (n + n)) V,
    x * bc (algebraMap V K) k ∈ stabGL (diagSub K (finSumFinEquiv (m := n) (n := n))) := by
  obtain ⟨k, b, hb, h⟩ := GlobalTheory.ValIwasawa.iwasawa V K (n + n) (x⁻¹ * shear finSumFinEquiv)
  refine ⟨k * (shear finSumFinEquiv)⁻¹, inv_mem_iff.1 (mem_stabGL_diagSub.2 (keepsDiag_of_mulVec fun w hw => ?_))⟩
  obtain ⟨a, rfl⟩ := (mem_diagSub _).1 hw
  have h1 : (x * bc (algebraMap V K) (k * (shear finSumFinEquiv)⁻¹))⁻¹ * shear finSumFinEquiv =
      shear finSumFinEquiv * b := by
    rw [map_mul, map_inv, bc_shear, mul_inv_rev, mul_assoc, h, mul_inv_rev, inv_inv, mul_assoc]
    exact congrArg _ (inv_mul_cancel_left _ _)
  have h2 : (b.1.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ = 0 := by
    ext i j
    refine hb ?_
    change (Fin.castAdd n j : ℕ) < Fin.natAdd n i
    simp only [Fin.val_castAdd, Fin.val_natAdd]
    omega
  have h3 : pairVec finSumFinEquiv a a = (shear finSumFinEquiv).1 *ᵥ pairVec finSumFinEquiv a 0 := by
    rw [shear_mulVec, add_zero]
  rw [h3, Matrix.mulVec_mulVec, ← Units.val_mul, h1, Units.val_mul, ← Matrix.mulVec_mulVec,
    mulVec_pairVec _ b.1, h2, shear_mulVec, pairVec_mem_diagSub]
  simp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E} {Q : Matrix (Fin (n + n)) (Fin (n + n)) E} {v : HeightOneSpectrum (𝓞 F)}

theorem mem_siegelH_of_split (h : IsCMExt F E σ) (hQ : Q = dblGram finSumFinEquiv J) (hJ : J.det ≠ 0)
    (τ : E →ₐ[F] Fv F v) {g : GLoc σ Q v} (hg : splitHom σ Q τ g ∈ stabGL (diagSub (Fv F v) finSumFinEquiv)) :
    g ∈ siegelH (Fv F v) σ Q := by
  have e : Q.map τ = dblGram finSumFinEquiv (J.map τ) := by
    rw [hQ, dblGram, blkMat_map _ _ (map_zero _), dblGram, Matrix.map_neg _ (map_neg _)]
  have hu : IsUnit (J.map τ).det := by
    rw [← AlgHom.mapMatrix_apply, ← AlgHom.map_det]; exact ((map_ne_zero τ).2 hJ).isUnit
  have h1 := (keepsDiag_iff _).1 (mem_stabGL_diagSub.1 hg)
  have h2 := (keepsDiag_iff _).1 (keepsDiag_of_pairing finSumFinEquiv hu (x := (splitHom σ Q (τ.comp σ) g).1)
    (fun u' u => e ▸ pairing_splitHom τ g u' u) hg)
  refine mem_siegelOf.2 ((keepsDiag_iff _).2 fun i j => split_ext h τ ?_ ?_)
  · rw [map_add (f := _), map_add (f := _)]; exact h1 i j
  · rw [map_add (f := _), map_add (f := _)]; exact h2 i j

theorem hasIwasawa_of_algHom (h : IsCMExt F E σ) (hQ : Q = dblGram finSumFinEquiv J) (hJ : IsHermND σ J)
    (hQ' : IsHermND σ Q) (τ : E →ₐ[F] Fv F v) (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsFullLattice E L]
    (hL : IsSelfDualAt σ J L v) : HasIwasawa σ Q (KFin σ Q L v) := fun g => by
  obtain ⟨a, ha⟩ := Frames.exists_isLatticeFrame (F := F) L
  have hβ := (isLatticeFrame_dbl ha).isSplitBasis τ h
  rw [bc_blkGL, bc_blkGL] at hβ
  generalize bc (splitProj τ : Fv F v ⊗[F] E →+* Fv F v) (bc (compFin F E v) a) = β at hβ
  have hd : blkGL finSumFinEquiv (β, β) ∈ stabGL (diagSub (Fv F v) finSumFinEquiv) :=
    mem_stabGL_diagSub.2 ((keepsDiag_blkMat _).2 rfl)
  obtain ⟨k, hk⟩ := iwasawa_diag (V := v.adicCompletionIntegers F) (splitEquivIn h hQ' τ (blkGL finSumFinEquiv (β, β)) g)
  obtain ⟨κ, hκ⟩ := (splitEquivIn h hQ' τ (blkGL finSumFinEquiv (β, β))).surjective
    (bc (algebraMap (v.adicCompletionIntegers F) (Fv F v)) k)
  have h1 : κ ∈ KFin σ Q L v :=
    (mem_stabLoc_iff_GLint h hQ' (isSelfDualAt_dbl hQ hL) hβ).2 (hκ ▸ ⟨k, rfl⟩)
  rw [← hκ, ← map_mul, splitEquivIn_apply] at hk
  have h2 := mul_mem (mul_mem hd hk) (inv_mem hd)
  rw [← mul_assoc, mul_inv_cancel_left, mul_inv_cancel_right] at h2
  exact ⟨⟨g * κ, mem_siegelH_of_split h hQ hJ.2 τ h2⟩, κ⁻¹, inv_mem h1, (mul_inv_cancel_right g κ).symm⟩

section Record

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem isSelfDualAt_of_isSelfDualC {D : D7} {A : HSp D} {L : Lat A} (hL : IsSelfDualC A L) (v : FinPl D) :
    IsSelfDualAt D.sp.cm.sig A.gram L v :=
  (SelfDual.forall_isSelfDualAt_iff (σ := D.sp.cm.sig) (GlobalTheory.Doubling.isHermND_gram A).2
    (Formalism.IndefR.Fin.PDA.selfDual_isFullLattice A L hL)).2
    (fun y => hL.2 y) v

theorem hasIwasawa_split : ∀ (D : D7) (A : HSp D) (L : Lat A), IsSelfDualC A L → ∀ v : FinPl D,
    Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v →
    HasIwasawa D.sp.cm.sig (dblSp A).gram (KFin D.sp.cm.sig (dblSp A).gram L v) := by
  intro D A L hL v ⟨P, P', hne, hP, hP'⟩
  obtain ⟨τ, -⟩ := existsUnique_splitPrime_eq (isCMExt_host D) (v := v) hne (HeightOneSpectrum.ext hP)
    (HeightOneSpectrum.ext hP')
  haveI := Formalism.IndefR.Fin.PDA.selfDual_isFullLattice A L hL
  exact hasIwasawa_of_algHom (isCMExt_host D) (gram_hdbl A) (GlobalTheory.Doubling.isHermND_gram A)
    (GlobalTheory.Doubling.isHermND_gram (dblSp A)) τ L (isSelfDualAt_of_isSelfDualC hL v)

end Record

end GlobalTheory.Core.Rk.IwSplit

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasIwasawaDecompositionDoubledSplitPlaceStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasIwasawaDecomposition_doubled_split_place : ∀ (D : D7) (A : HSp D) (L : Lat A), IsSelfDualC A L → ∀ v : FinPl D, Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v → HasIwasawa D.sp.cm.sig (dblSp A).gram (KFin D.sp.cm.sig (dblSp A).gram L v) := by
  first | exact @GlobalTheory.Core.Rk.IwSplit.hasIwasawa_split | exact GlobalTheory.Core.Rk.IwSplit.hasIwasawa_split | (intros; apply GlobalTheory.Core.Rk.IwSplit.hasIwasawa_split <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultTApplyRapidDec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto.MultRapid

theorem multT_apply_rapidDec : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (θ : InfFam D), IsInfFam θ → ∀ (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ F ∈ MultT θ M J χ, ∀ v : SmT M, IsAutFunSm θ V (F v) ∧ IsCuspFun V (F v) ∧ GlobalTheory.Grow.RapidDec V (F v) := by
  intro hP D V S M θ hθ J χ F hF v
  obtain ⟨ha, hc⟩ := GlobalTheory.PairLift.LowAllPf.multT_apply_smooth_cusp θ M J χ F hF v
  exact ⟨ha, hc, GlobalTheory.Grow.rapidDec_of_cuspForm hP hθ ha hc⟩

end GlobalTheory.ChainOnto.MultRapid
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeReductionEqOneOfLocalComponentOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeReductionEqOneOfLocalComponentOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.RedOne

theorem redFn_eq_one : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (g : GA D V) (PP : Pl D.host.E), Lev.finE V g ∈ Formalism.L2.DIV.St β → GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) g = 1 → Formalism.L2.DIV.redFn β PP (Lev.finE V g) = 1 := by
  intro D V β g PP hS h1
  classical
  exact GlobalTheory.FinZeta.LevelOff.redFn_eq_one_of_proj β {(_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)} hS
    (fun v hv => by rw [Finset.mem_singleton] at hv; subst hv; exact h1) (Finset.mem_singleton_self _)

end GlobalTheory.ChainOnto.RedOne
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeReductionEqOneOfLocalComponentOneStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeReduction_eq_one_of_local_component_one : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (g : GA D V) (PP : Pl D.host.E), Lev.finE V g ∈ Formalism.L2.DIV.St β → GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) g = 1 → Formalism.L2.DIV.redFn β PP (Lev.finE V g) = 1 := by
  first | exact @GlobalTheory.ChainOnto.RedOne.redFn_eq_one | exact GlobalTheory.ChainOnto.RedOne.redFn_eq_one | (intros; apply GlobalTheory.ChainOnto.RedOne.redFn_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepPreservesFockDegreeOfCommuteCartan
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepPreservesFockDegreeOfCommuteCartan
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.CartanFockDeg

theorem om_annih_move {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {χS χT : (AE D)ˣ →* Circle} {om : WRep S T} (sS : RealMat S) (sT : RealMat T)
    (hW : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ) (k : GA D S)
    (hk : ∀ τ, compAt θ τ (Formalism.L2.Theta.mt S k) * sS τ = sS τ * compAt θ τ (Formalism.L2.Theta.mt S k))
    (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    om (k, 1) (annih (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) z f) =
      annih (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) (z * compAt θ τ (Formalism.L2.Theta.mt S k⁻¹)) (om (k, 1) f) := by
  have hψ := hW.std
  have hm1 : Formalism.L2.Theta.mt T (1 : GA D T) = 1 := by
    unfold Formalism.L2.Theta.mt
    rw [map_one, Units.val_one]
  have h1 : compAt θ τ (Formalism.L2.Theta.mt T (1 : GA D T)) = 1 := by
    rw [hm1]
    exact Matrix.map_one _ (((θ τ).comp (infPart D)).map_zero) (((θ τ).comp (infPart D)).map_one)
  have hinv : compAt θ τ (Formalism.L2.Theta.mt S k⁻¹) * sS τ = sS τ * compAt θ τ (Formalism.L2.Theta.mt S k⁻¹) := by
    have a := GlobalTheory.OrientedHeis.compAt_mt_mul_inv (θ := θ) τ k
    have b : compAt θ τ (Formalism.L2.Theta.mt S k⁻¹) * compAt θ τ (Formalism.L2.Theta.mt S k) = 1 := by
      have := GlobalTheory.OrientedHeis.compAt_mt_mul_inv (θ := θ) τ k⁻¹
      rwa [inv_inv] at this
    calc compAt θ τ (Formalism.L2.Theta.mt S k⁻¹) * sS τ
        = compAt θ τ (Formalism.L2.Theta.mt S k⁻¹) * sS τ * (compAt θ τ (Formalism.L2.Theta.mt S k) * compAt θ τ (Formalism.L2.Theta.mt S k⁻¹)) := by
          rw [a, Matrix.mul_one]
      _ = compAt θ τ (Formalism.L2.Theta.mt S k⁻¹) * (compAt θ τ (Formalism.L2.Theta.mt S k) * sS τ) * compAt θ τ (Formalism.L2.Theta.mt S k⁻¹) := by
          rw [hk τ]; simp only [Matrix.mul_assoc]
      _ = sS τ * compAt θ τ (Formalism.L2.Theta.mt S k⁻¹) := by
          rw [← Matrix.mul_assoc, b, Matrix.one_mul]
  have hJ : cplxO (sS τ) (sT τ) (z * compAt θ τ (Formalism.L2.Theta.mt S k⁻¹)) =
      cplxO (sS τ) (sT τ) z * compAt θ τ (Formalism.L2.Theta.mt S k⁻¹) := by
    unfold cplxO
    rw [Matrix.smul_mul]
    simp only [Matrix.mul_assoc, hinv]
  have e : ∀ w : Matrix (Fin T.rank) (Fin S.rank) ℂ, compAt θ τ (Formalism.L2.Theta.mt T (1 : GA D T)) * w * compAt θ τ (Formalism.L2.Theta.mt S k⁻¹) =
      w * compAt θ τ (Formalism.L2.Theta.mt S k⁻¹) := fun w => by rw [h1, Matrix.one_mul]
  unfold annih
  rw [map_add (f := _), map_smul, GlobalTheory.OrientedHeis.om_dRho hW hθ k 1 τ z hf, GlobalTheory.OrientedHeis.om_dRho hW hθ k 1 τ _ hf, e, e, hJ]

theorem om_keeps_fockDeg : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : WRep S T) (sS : RealMat S) (sT : RealMat T), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → ∀ k : GA D S, (∀ τ, compAt θ τ (Formalism.L2.Theta.mt S k) * sS τ = sS τ * compAt θ τ (Formalism.L2.Theta.mt S k)) → ∀ (N : ℕ) (f : WO S T → ℂ), IsThetaFunO ψ S T f → (∀ l : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin S.rank) ℂ), l.length = N → l.foldr (fun p f => annih (heisO ψ S T) θ p.1 (cplxO (sS p.1) (sT p.1)) p.2 f) f = 0) → ∀ l : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin S.rank) ℂ), l.length = N → l.foldr (fun p f => annih (heisO ψ S T) θ p.1 (cplxO (sS p.1) (sT p.1)) p.2 f) (om (k, 1) f) = 0 := by
  intro D ψ θ S T χS χT om sS sT hW hθ k hk N f hf hl l hlen
  have hψ := hW.std
  have hth : ∀ (l : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin S.rank) ℂ)) {g : WO S T → ℂ}, IsThetaFunO ψ S T g →
      IsThetaFunO ψ S T (l.foldr (fun p f => annih (heisO ψ S T) θ p.1 (cplxO (sS p.1) (sT p.1)) p.2 f) g) := by
    intro l g hg
    induction l with
    | nil => exact hg
    | cons p l ih => exact GlobalTheory.FockIndep.annih_theta hψ hθ p.1 _ p.2 ih
  have key : ∀ l : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin S.rank) ℂ),
      om (k, 1) (l.foldr (fun p f => annih (heisO ψ S T) θ p.1 (cplxO (sS p.1) (sT p.1)) p.2 f) f) =
        (l.map fun p => (p.1, p.2 * compAt θ p.1 (Formalism.L2.Theta.mt S k⁻¹))).foldr
          (fun p f => annih (heisO ψ S T) θ p.1 (cplxO (sS p.1) (sT p.1)) p.2 f) (om (k, 1) f) := by
    intro l
    induction l with
    | nil => rfl
    | cons p l ih =>
      rw [List.foldr_cons, List.map_cons, List.foldr_cons, om_annih_move sS sT hW hθ k hk p.1 p.2 (hth l hf), ih]
  let l' := l.map fun p => (p.1, p.2 * compAt θ p.1 (Formalism.L2.Theta.mt S k))
  have hl' : l = l'.map fun p => (p.1, p.2 * compAt θ p.1 (Formalism.L2.Theta.mt S k⁻¹)) := by
    simp only [l', List.map_map]
    conv_lhs => rw [← List.map_id l]
    refine List.map_congr_left fun p _ => ?_
    simp only [Function.comp_apply, id_eq, Matrix.mul_assoc, GlobalTheory.OrientedHeis.compAt_mt_mul_inv, Matrix.mul_one]
  rw [hl', ← key, hl l' (by simp [l', hlen]), map_zero]

end GlobalTheory.CartanFockDeg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepPreservesFockDegreeOfCommuteCartanStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRep_preserves_fockDegree_of_commute_cartan : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : WRep S T) (sS : RealMat S) (sT : RealMat T), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → ∀ k : GA D S, (∀ τ, compAt θ τ (Formalism.L2.Theta.mt S k) * sS τ = sS τ * compAt θ τ (Formalism.L2.Theta.mt S k)) → ∀ (N : ℕ) (f : WO S T → ℂ), IsThetaFunO ψ S T f → (∀ l : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin S.rank) ℂ), l.length = N → l.foldr (fun p f => annih (heisO ψ S T) θ p.1 (cplxO (sS p.1) (sT p.1)) p.2 f) f = 0) → ∀ l : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin S.rank) ℂ), l.length = N → l.foldr (fun p f => annih (heisO ψ S T) θ p.1 (cplxO (sS p.1) (sT p.1)) p.2 f) (om (k, 1) f) = 0 := by
  first | exact @GlobalTheory.CartanFockDeg.om_keeps_fockDeg | exact GlobalTheory.CartanFockDeg.om_keeps_fockDeg | (intros; apply GlobalTheory.CartanFockDeg.om_keeps_fockDeg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ModelIdentificationRespectsRealAndFinite
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ModelIdentificationRespectsRealAndFinite
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open Formalism.MainNotions.StandardLattice

namespace GlobalTheory.Core.Mi.SeeReal

variable {D : D7}

theorem isAtTau_atTau (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau)
    (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hg : gᴴ * gramAt D V τ * g = gramAt D V τ) :
    IsAtTau θ V τ g (atTau θ V τ g) := by
  have hex := (Formalism.IndefR.Eqv.atTauExUnique_holds D θ hθ V τ g hg).exists
  unfold atTau
  rw [dite_eq_left hex]
  exact hex.choose_spec

theorem eq_of_conj {n : ℕ} {P A B : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P.det) (e : P * A * P⁻¹ = B) :
    A = P⁻¹ * B * P := by
  rw [← e]
  simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul P hP, Matrix.mul_one, Matrix.nonsing_inv_mul_cancel_left P A hP]

theorem phi_inst (v : InfinitePlace D.host.F) (x : D.host.E) :
    (Formalism.IndefR.RationalEmbedding.inst D).φ v x = embS D ((Formalism.L2.Host.tauPl D).symm v) x := rfl

theorem realSplit_gen {I : Formalism.MainNotions.S.AutInst} (h : I = Formalism.L2.SG.InstExistsPf.instOf D)
    (ιE : I.E ≃+* D.host.E) (hιE : ∀ x : I.E, HEq (ιE x) x) (pl : InfinitePlace I.F ≃ D.what₂.Tau)
    (hφ : ∀ v (x : I.E), I.φ v x = embS D (pl v) (ιE x)) (θ : InfFam D) (hθ : IsInfFam θ) :
    (∀ k : GA D (D.sp.Y 0), k ∈ GfC (D.sp.Y 0) ↔ ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA h.symm) k).1 = 1) ∧
    (∀ k : GA D (D.sp.Y 0), k ∈ GinfC (D.sp.Y 0) ↔ ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA h.symm) k).2 = 1) ∧
    (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ),
      ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA h.symm) (atTau θ (D.sp.Y 0) τ g)).2 = 1 ∧
      (∀ v, v ≠ pl.symm τ → ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA h.symm) (atTau θ (D.sp.Y 0) τ g)).1 v = 1) ∧
      HEq (uMat (((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA h.symm) (atTau θ (D.sp.Y 0) τ g)).1 (pl.symm τ)))
        ((fun Pm : Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.Y 0).rank) ℂ => Pm⁻¹ * g * Pm)
          ((Formalism.L2.SG.InstExistsPf.instOf D).P (Formalism.L2.Host.tauPl D τ)))) ∧
    ∀ τ (y : Formalism.REAL.UJ (I.ε (pl.symm τ))), ∃ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ),
      ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA h.symm) (atTau θ (D.sp.Y 0) τ g)).1 (pl.symm τ) = y := by
  subst h
  obtain rfl := Formalism.IndefR.Eqv.eq_thetaC D hθ
  have hι : ∀ x, ιE x = x := fun x => eq_of_heq (hιE x)
  have key : ∀ τ τ' : D.what₂.Tau, embS D τ = embS D τ' → τ = τ' :=
    fun τ τ' e => D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 e))
  have hpl : pl = (Formalism.L2.Host.tauPl D).symm := Equiv.ext fun v => key _ _ (RingHom.ext fun x => by
    have e := hφ v x
    have e2 : embS D (pl v) (ιE x) = embS D (pl v) x := congrArg _ (hι x)
    exact (e2.symm.trans e.symm).trans (phi_inst v x))
  subst hpl
  have hT : ∀ k, ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA (rfl : Formalism.L2.SG.InstExistsPf.instOf D = _).symm)) k =
      Formalism.IndefR.RationalEmbedding.iota D k := fun _ => rfl
  have hP : ∀ v, IsUnit ((Formalism.IndefR.RationalEmbedding.inst D).P v).det :=
    fun v => (Matrix.isUnit_iff_isUnit_det _).mp ((Formalism.IndefR.RationalEmbedding.inst D).P_unit v)
  refine ⟨fun k => ?_, fun k => ?_, fun τ g hg => ?_, fun τ y => ?_⟩
  · rw [hT]
    have e := Formalism.L2.SG.EvalTIota.brg_mem_GfC_i (Formalism.IndefR.RationalEmbedding.iota D k)
    rwa [ContinuousMulEquiv.symm_apply_apply] at e
  · rw [hT]
    have e := Formalism.L2.SG.EvalTIota.iota_symm_mem_GinfC (Formalism.IndefR.RationalEmbedding.iota D k)
    rwa [ContinuousMulEquiv.symm_apply_apply] at e
  · have hg' : gᴴ * gramAt D (D.sp.Y 0) τ * g = gramAt D (D.sp.Y 0) τ := hg
    have hk := isAtTau_atTau (Formalism.IndefR.Eqv.thetaC D) (Formalism.IndefR.Eqv.isInfFam_thetaC D) _ τ g hg'
    rw [hT]
    generalize atTau (Formalism.IndefR.Eqv.thetaC D) (D.sp.Y 0) τ g = k at hk ⊢
    obtain ⟨x, rfl⟩ := (Formalism.IndefR.RationalEmbedding.iota D).symm.surjective k
    rw [ContinuousMulEquiv.apply_symm_apply]
    have hbr := Formalism.L2.SG.EvalTIota.infMat_brg_i x
    refine ⟨(Formalism.L2.SG.EvalTIota.iota_symm_mem_GinfC x).1 hk.1, fun v hv => ?_, heq_of_eq ?_⟩
    · obtain ⟨ρ, rfl⟩ := (Formalism.L2.Host.tauPl D).surjective v
      have hρ : ρ ≠ τ := fun e => hv (by rw [e]; rfl)
      have e0 : Formalism.L2.SG.EvalTIota.Pi (Formalism.L2.Host.tauPl D ρ) * Formalism.L2.SG.EvalTIota.uM' x (Formalism.L2.Host.tauPl D ρ) *
          (Formalism.L2.SG.EvalTIota.Pi (Formalism.L2.Host.tauPl D ρ))⁻¹ = (1 : Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.Y 0).rank) ℂ) := by
        rw [← hbr ρ, hk.2.2 ρ hρ]
      have e1 := eq_of_conj (hP _) e0
      simp only [Formalism.L2.SG.EvalTIota.Pi, Formalism.L2.SG.EvalTIota.uM'] at e1
      have e2 : uMat (x.1 (Formalism.L2.Host.tauPl D ρ)) = 1 := by
        rw [e1]
        erw [Matrix.mul_one]
        exact Matrix.nonsing_inv_mul _ (hP _)
      exact Subtype.ext (Units.ext e2)
    · exact eq_of_conj (hP _) ((hbr τ).symm.trans hk.2.1)
  · classical
    let x0 : (Formalism.IndefR.RationalEmbedding.inst D).GA :=
      (Pi.mulSingle (M := fun v => Formalism.REAL.UJ ((Formalism.IndefR.RationalEmbedding.inst D).ε v)) (Formalism.L2.Host.tauPl D τ) y, 1)
    have hbr := Formalism.L2.SG.EvalTIota.infMat_brg_i x0
    let g : Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.Y 0).rank) ℂ :=
      (Formalism.IndefR.RationalEmbedding.inst D).P (Formalism.L2.Host.tauPl D τ) * uMat y * ((Formalism.IndefR.RationalEmbedding.inst D).P (Formalism.L2.Host.tauPl D τ))⁻¹
    have hk0 : IsAtTau (Formalism.IndefR.Eqv.thetaC D) (D.sp.Y 0) τ g ((Formalism.IndefR.RationalEmbedding.iota D).symm x0) := by
      refine ⟨(Formalism.L2.SG.EvalTIota.iota_symm_mem_GinfC x0).2 rfl, ?_, fun ρ hρ => ?_⟩
      · rw [hbr τ]
        have hy : x0.1 (Formalism.L2.Host.tauPl D τ) = y :=
          Pi.mulSingle_eq_same (M := fun v => Formalism.REAL.UJ ((Formalism.IndefR.RationalEmbedding.inst D).ε v)) (Formalism.L2.Host.tauPl D τ) y
        have hy' : Formalism.L2.SG.EvalTIota.uM' x0 (Formalism.L2.Host.tauPl D τ) = uMat y := by
          show uMat (x0.1 (Formalism.L2.Host.tauPl D τ)) = uMat y
          rw [hy]
        rw [hy']
        rfl
      · rw [hbr ρ]
        have hne : Formalism.L2.Host.tauPl D ρ ≠ Formalism.L2.Host.tauPl D τ := (Formalism.L2.Host.tauPl D).injective.ne hρ
        have h1 : x0.1 (Formalism.L2.Host.tauPl D ρ) = 1 := Pi.mulSingle_eq_of_ne hne _
        have h1' : Formalism.L2.SG.EvalTIota.uM' x0 (Formalism.L2.Host.tauPl D ρ) = 1 := by
          show uMat (x0.1 (Formalism.L2.Host.tauPl D ρ)) = 1
          rw [h1]
          rfl
        rw [h1']
        erw [Matrix.mul_one]
        exact Matrix.mul_nonsing_inv _ (hP _)
    have hgU : gᴴ * gramAt D (D.sp.Y 0) τ * g = gramAt D (D.sp.Y 0) τ :=
      Formalism.IndefR.Eqv.atTauUnitary_holds D _ (Formalism.IndefR.Eqv.isInfFam_thetaC D) _ τ g _ hk0
    refine ⟨g, hgU, ?_⟩
    have hu := (Formalism.IndefR.Eqv.atTauExUnique_holds D _ (Formalism.IndefR.Eqv.isInfFam_thetaC D) _ τ g hgU).unique
      (isAtTau_atTau _ (Formalism.IndefR.Eqv.isInfFam_thetaC D) _ τ g hgU) hk0
    rw [hT, hu, ContinuousMulEquiv.apply_symm_apply]
    exact Pi.mulSingle_eq_same (M := fun v => Formalism.REAL.UJ ((Formalism.IndefR.RationalEmbedding.inst D).ε v)) _ _

theorem realSplit_of_idE : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (θ : InfFam D), IsInfFam θ → IdE X → RealSplit X h θ :=
  fun _ X h θ hθ hE => realSplit_gen h X.ιE hE X.pl X.φ_eq θ hθ

end GlobalTheory.Core.Mi.SeeReal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ModelIdentificationRespectsRealAndFiniteStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modelIdentification_respects_real_and_finite : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D), IsInfFam θ → GlobalTheory.Core.Mi.IdE X → RealSplit X h θ := by
  first | exact @GlobalTheory.Core.Mi.SeeReal.realSplit_of_idE | exact GlobalTheory.Core.Mi.SeeReal.realSplit_of_idE | (intros; apply GlobalTheory.Core.Mi.SeeReal.realSplit_of_idE <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealTranslationCuspFormMapsEqSmoothLinearMap
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitGramAt
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UnifEvery

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Mult
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem isUnit_gramAt (M : DSModel V S) (τ : D.what₂.Tau) : IsUnit (gramAt D V τ) := by
  rw [← M.fr_gram τ]
  have hJ : IsUnit (Formalism.REAL.Jm (M.ε τ)) := by
    unfold Formalism.REAL.Jm
    rw [Matrix.isUnit_diagonal, Pi.isUnit_iff]
    intro i
    split_ifs <;> simp
  exact (((Matrix.isUnit_conjTranspose _).2 (M.fr_unit τ)).mul hJ).mul (M.fr_unit τ)

theorem rep_mul (M : DSModel V S) (τ : D.what₂.Tau) {a b : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (ha : a ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (hb : b ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (w : M.H τ) :
    M.rep τ (a * b) w = M.rep τ a (M.rep τ b w) := by
  have hu : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have h := (M.ds τ).2.2.1.1.2 _ (GlobalTheory.GardingVec.conj_mem (M.fr_unit τ) (M.fr_gram τ) ha) _
    (GlobalTheory.GardingVec.conj_mem (M.fr_unit τ) (M.fr_gram τ) hb)
  have e : M.fr τ * (a * b) * (M.fr τ)⁻¹ = M.fr τ * a * (M.fr τ)⁻¹ * (M.fr τ * b * (M.fr τ)⁻¹) := by
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hu]
  unfold DSModel.rep
  rw [e, h]
  rfl

theorem prod_mul_eq {G : Type} [Monoid G] (h : G) : ∀ (k : ℕ) (u v : Fin k → G), (∀ i, u i * h = h * v i) →
    (List.ofFn u).prod * h = h * (List.ofFn v).prod
  | 0, _, _, _ => by simp
  | k + 1, u, v, e => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, mul_assoc,
      prod_mul_eq h k _ _ fun i => e i.succ, ← mul_assoc, e, mul_assoc]

theorem rep_mem_sm (M : DSModel V S) (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) {v : M.H τ} (hv : v ∈ M.sm τ) : M.rep τ g v ∈ M.sm τ := by
  have hG := isUnit_gramAt M τ
  have hgu : IsUnit g.det := by
    have h1 : IsUnit (gᴴ * gramAt D V τ * g) := by rw [show gᴴ * gramAt D V τ * g = _ from hg]; exact hG
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_mul] at h1
    exact isUnit_of_mul_isUnit_right h1
  have hab : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hgu
  induction hv using Submodule.span_induction with
  | mem w hw =>
    refine Submodule.subset_span fun k Xs hX => ?_
    have hX' : ∀ i, g⁻¹ * Xs i * g ∈ lieAt V τ := fun i => GlobalTheory.Mem.RealTranslate.skew_conj hg hab (hX i)
    have h1 := ((M.rep τ g).restrictScalars ℝ).contDiff.comp (hw k (fun i => g⁻¹ * Xs i * g) hX')
    have hm : ∀ (Y : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ i, Y i ∈ lieAt V τ) → ∀ t : Fin k → ℝ,
        (List.ofFn fun i => NormedSpace.exp (t i • Y i)).prod ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := fun Y hY t =>
      GlobalTheory.GardingVec.list_prod_mem _ fun x hx => by
        obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
        exact GlobalTheory.GardingVec.exp_mem hG (hY i) (t i)
    convert h1 using 1
    funext t
    show _ = M.rep τ g (M.rep τ _ w)
    rw [← rep_mul M τ (hm Xs hX t) hg, ← rep_mul M τ hg (hm _ hX' t),
      prod_mul_eq g k _ _ fun i => GlobalTheory.Mem.RealTranslate.exp_conj_eq hab (Xs i) (t i)]
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

variable (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))


variable {θ} {M : DSModel V S}

end GlobalTheory.UnifEvery
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealTranslationCuspFormMapsEqSmoothLinearMap
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RealTransSm

open Formalism.MainNotions.StandardLattice

variable {D : D7} {θ : InfFam D} {V : HSp D}

theorem infMat_list_prod (hθ : IsInfFam θ) (u : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (hu : ∀ τ, u τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (ρ : D.what₂.Tau) :
    ∀ l : List D.what₂.Tau, l.Nodup →
      infMat D.sp.cm.sig V.gram (θ ρ) (l.map fun τ => atTau θ V τ (u τ)).prod = if ρ ∈ l then u ρ else 1
  | [], _ => by simpa using GlobalTheory.PointAtPlaceHom.infMat_one V (θ ρ)
  | a :: l, hl => by
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.prod_cons, GlobalTheory.PointAtPlaceHom.infMat_mul, infMat_list_prod hθ u hu ρ l hl.2]
    have hs := GlobalTheory.PointAtPlaceHom.atTau_spec hθ V a (hu a)
    by_cases c : ρ = a
    · subst c
      rw [hs.2.1, ite_eq_right hl.1, ite_eq_left List.mem_cons_self, Matrix.mul_one]
    · rw [hs.2.2 ρ c, Matrix.one_mul]
      by_cases d : ρ ∈ l
      · rw [ite_eq_left d, ite_eq_left (List.mem_cons_of_mem a d)]
      · rw [ite_eq_right d, ite_eq_right]
        simp [c, d]

theorem eq_realElt (hθ : IsInfFam θ) {g : GA D V} (hg : g ∈ GinfC V) :
    g = GlobalTheory.AdelicScalar.realElt θ V (fun τ => infMat D.sp.cm.sig V.gram (θ τ) g) := by
  set u : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ := fun τ => infMat D.sp.cm.sig V.gram (θ τ) g with hu_def
  have hu : ∀ τ, u τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := fun τ =>
    GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V g τ
  set P := GlobalTheory.AdelicScalar.realElt θ V u with hP
  have hPm : P ∈ GinfC V := by
    refine list_prod_mem fun x hx => ?_
    obtain ⟨τ, -, rfl⟩ := List.mem_map.1 hx
    exact GlobalTheory.PointAtPlaceHom.atTau_mem V τ (u τ)
  have e : ∀ ρ, infMat D.sp.cm.sig V.gram (θ ρ) P = infMat D.sp.cm.sig V.gram (θ ρ) g := fun ρ => by
    rw [hP, GlobalTheory.AdelicScalar.realElt, infMat_list_prod hθ u hu ρ _ (Finset.nodup_toList _),
      ite_eq_left (Finset.mem_toList.2 (Finset.mem_univ ρ))]
  refine mul_inv_eq_one.1 (GlobalTheory.PointAtPlace.eq_one_of_mem V _ ((GlobalTheory.SmoothForms.RealPts.glue θ hθ V).1 _ fun ρ => ?_)
    (mul_mem hg (inv_mem hPm)))
  rw [GlobalTheory.PointAtPlaceHom.infMat_mul, ← e, ← GlobalTheory.PointAtPlaceHom.infMat_mul, mul_inv_cancel,
    GlobalTheory.PointAtPlaceHom.infMat_one]

def smAct (hθ : IsInfFam θ) {S : D.what₂.Tau → SPar} (M : DSModel V S) (g : GA D V) (τ : D.what₂.Tau) :
    M.sm τ →ₗ[ℂ] M.sm τ :=
  (M.rep τ (infMat D.sp.cm.sig V.gram (θ τ) g)).toLinearMap.restrict fun _ hw =>
    GlobalTheory.UnifEvery.rep_mem_sm M τ (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V g τ) hw

theorem rTrans_eq_map : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S), IsInfFam θ → ∀ g ∈ GinfC V, ∃ σ : SmT M →ₗ[ℂ] SmT M, ∀ (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ T ∈ MultT θ M J χ, ∀ x, T (σ x) = rTrans g (T x) := by
  intro D θ V S M hθ g hg
  refine ⟨PiTensorProduct.map (smAct hθ M g), fun J χ T hT x => ?_⟩
  have hU : PiTensorProduct.lift.symm T ∈ Mult θ M J χ := (mem_multT θ M J χ T).1 hT
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c v =>
    rw [map_smul, map_smul, PiTensorProduct.map_tprod]
    let u τ := infMat D.sp.cm.sig V.gram (θ τ) g
    let w : M.Vec := fun τ => smAct hθ M g τ (v τ)
    have hu (τ : D.what₂.Tau) : u τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) :=
      GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V g τ
    have hw (τ : D.what₂.Tau) : (w τ : M.H τ) = M.rep τ (u τ) (v τ : M.H τ) := rfl
    have translate (U : MMap M) (hU : U ∈ Mult θ M J χ) :
        U w = rTr V (GlobalTheory.AdelicScalar.realElt θ V u) (U v) := by
      induction hU using Submodule.span_induction with
      | mem U hU =>
        have onList (l : List D.what₂.Tau) (hl : l.Nodup) :
            U (fun τ => if τ ∈ l then w τ else v τ) =
              rTr V (l.map fun τ => atTau θ V τ (u τ)).prod (U v) := by
          induction l with
          | nil =>
            funext h
            simp [rTr]
          | cons a l ih =>
            rw [List.nodup_cons] at hl
            have ha := hU.equiv a (u a) (hu a) (fun τ => if τ ∈ l then w τ else v τ)
              (w a) (by simpa only [ite_eq_right hl.1] using hw a)
            rw [ih hl.2] at ha
            have hupdate : (fun τ => if τ ∈ a :: l then w τ else v τ) =
                Function.update (fun τ => if τ ∈ l then w τ else v τ) a (w a) := by
              funext τ
              by_cases hτ : τ = a
              · subst τ
                simp
              · rw [Function.update_of_ne hτ]
                simp [hτ]
            rw [hupdate, ha]
            funext h
            simp only [rTr, List.map_cons, List.prod_cons, mul_assoc]
        have hall := onList (Finset.univ : Finset D.what₂.Tau).toList (Finset.nodup_toList _)
        simpa [GlobalTheory.AdelicScalar.realElt] using hall
      | zero => funext h; simp [rTr]
      | add U U' _ _ h₁ h₂ =>
        funext h
        simpa only [rTr, add_apply, Pi.add_apply] using
          congrArg₂ (· + ·) (congrFun h₁ h) (congrFun h₂ h)
      | smul a U _ h₁ =>
        funext h
        simpa only [rTr, smul_apply, Pi.smul_apply] using
          congrArg (a • ·) (congrFun h₁ h)
    have key := translate _ hU
    have hreal : GlobalTheory.AdelicScalar.realElt θ V u = g := (eq_realElt hθ hg).symm
    rw [hreal, PiTensorProduct.lift_symm] at key
    simp only [LinearMap.compMultilinearMap_apply] at key
    change c • T (PiTensorProduct.tprod ℂ w) = _
    funext h
    simp only [key, rTr, rTrans, map_smul, Pi.smul_apply]
  | add x y hx hy =>
    rw [map_add (f := _), map_add (f := _), hx, hy]
    funext h
    simp [rTrans]

end GlobalTheory.RealTransSm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealTranslationCuspFormMapsEqSmoothLinearMapStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realTranslation_cuspFormMaps_eq_smooth_linear_map : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S), IsInfFam θ → ∀ g ∈ GinfC V, ∃ σ : SmT M →ₗ[ℂ] SmT M, ∀ (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ T ∈ MultT θ M J χ, ∀ x, T (σ x) = rTrans g (T x) := by
  first | exact @GlobalTheory.RealTransSm.rTrans_eq_map | exact GlobalTheory.RealTransSm.rTrans_eq_map | (intros; apply GlobalTheory.RealTransSm.rTrans_eq_map <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.I0M
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.SBesEx

variable {D : D7}

def cY (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (y : (VS D).V) :
    Fin (D.sp.Y 0).rank → D.host.E :=
  fun k => X.ιE (X.crd y (Fin.cast (rank_eq X h) k))

def scl (t lam : D.host.E) (a : Fin D.R.rS) : D.host.E := t * lam ^ (D.R.rS - (a : ℕ))

def eM (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t lam : D.host.E) :
    Matrix (Fin (D.sp.Y 0).rank) (Fin D.R.rS) D.host.E :=
  fun k a => scl t lam a * cY X h (X.eX a) k

def e'M (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t lam : D.host.E) :
    Matrix (Fin (D.sp.Y 0).rank) (Fin D.R.rS) D.host.E :=
  fun k a => (star (scl t lam a))⁻¹ * cY X h (X.fY a) k

def qM (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) :
    Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.X 0).rank) D.host.E :=
  fun k j => X.ιE (X.crd (Formalism.L2.SG.ColDict.qFr wt (Fin.cast (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) j))
    (Fin.cast (rank_eq X h) k))

def zM (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (t : D.host.E) (L : HSp D) :
    Matrix (Fin (D.sp.Y 0).rank) (Fin L.rank) D.host.E :=
  fun k _ => t * cY X h (X.zu u) k

def i0M (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word)
    (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (t : D.host.E) {V₀ L : HSp D} (o : OrthDec V₀ (D.sp.X 0) L) :
    Matrix (Fin (D.sp.Y 0).rank) (Fin V₀.rank) D.host.E :=
  qM X h wt * o.qA + zM X h u t L * o.qB

def zeta (L : HSp D) : Fin L.rank → D.host.E := fun _ => 1

end GlobalTheory.Core.SBesEx

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HarishChandraNodesFarApartOfCubicNodeGap
open Formalism.BasicNotions

namespace GlobalTheory.Core.Rk.GapOfNodes

theorem harishChandraNodesFarApart_of_cubic_node_gap : ∀ D : D7, D.NodeGap (4 * ((D.R.N D.R.m : ℕ) : ℝ) ^ 3 + 2 * D.R.t + 6) →
    GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.NodeGap D := by
  intro D H
  have hN : D.R.N D.R.m = D.R.rankX' + 1 := factXm D.R
  refine ⟨D.R.N D.R.m, hN.ge, fun τ i hi => ?_⟩
  have h := H D.u₀ τ i.1 hi
  rw [D.hcW_b D.u₀ τ] at h
  simp only [Fin.eta] at h
  have ht : (0 : ℝ) ≤ (D.R.t : ℝ) := by positivity
  have hc : (0 : ℝ) ≤ ((D.R.N D.R.m : ℕ) : ℝ) ^ 3 := by positivity
  have key : (((D.R.t : ℚ) + 2 * ((D.R.N D.R.m : ℕ) : ℚ) ^ 3 + 1 : ℚ) : ℝ) ≤
      (((D.hc τ).b ⟨i.1 + 1, hi⟩ - (D.hc τ).b i : ℚ) : ℝ) := by
    push_cast
    push_cast at h
    linarith
  exact_mod_cast key

end GlobalTheory.Core.Rk.GapOfNodes
end
