module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelIteratedIntegralsSwap
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualProdIff
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDoubledHermitianSpaceRealPlace
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinContinuationOfDoublingMethod
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixSDblDecZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdeleCharacterEqOneIntegralUnitsUnramifiedAdelic

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsDoubledUnitaryChartSplitPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsDoubledUnitaryChartSplitPlace
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

namespace GlobalTheory.LFun.DblSplit

section Pure

variable {A : Type} [CommRing A] {m ι : Type} [Fintype m] [Fintype ι] [DecidableEq m] [DecidableEq ι] (e : m ⊕ m ≃ ι)

theorem blkGL_mem_diag (a : GL m A) : blkGL e (a, a) ∈ Formalism.UG.stabGL (diagSub A e) :=
  mem_stabGL_diagSub.2 ((keepsDiag_blkMat _).2 rfl)

theorem keepsDiag_conj_iff (a : GL m A) (x : GL ι A) :
    KeepsDiag e ((blkGL e (a, a))⁻¹ * x * blkGL e (a, a)).1 ↔ KeepsDiag e x.1 := by
  rw [← mem_stabGL_diagSub, ← mem_stabGL_diagSub, Subgroup.mul_mem_cancel_right _ (blkGL_mem_diag e a),
    Subgroup.mul_mem_cancel_left _ (inv_mem (blkGL_mem_diag e a))]

theorem det_leviMat_conj (a : GL m A) {x : GL ι A} (hx : KeepsDiag e x.1) :
    (leviMat e ((blkGL e (a, a))⁻¹ * x * blkGL e (a, a)).1).det = (leviMat e x.1).det := by
  let p : Formalism.UG.stabGL (diagSub A e) := ⟨_, blkGL_mem_diag e a⟩
  let q : Formalism.UG.stabGL (diagSub A e) := ⟨x, mem_stabGL_diagSub.2 hx⟩
  change (leviGL e (p⁻¹ * q * p)).1.det = (leviGL e q).1.det
  rw [map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul, Matrix.det_units_conj']

theorem det_quotMat_conj (a : GL m A) {x : GL ι A} (hx : KeepsDiag e x.1) :
    (quotMat e ((blkGL e (a, a))⁻¹ * x * blkGL e (a, a)).1).det = (quotMat e x.1).det := by
  have h1 := ((keepsDiag_conj_iff e a x).2 hx).det_eq
  rw [det_leviMat_conj e a hx, Units.val_mul, Units.val_mul, Matrix.det_units_conj', hx.det_eq] at h1
  have hu : IsUnit (leviMat e x.1).det := by
    have := (Matrix.isUnit_iff_isUnit_det _).1 x.isUnit
    rw [hx.det_eq] at this
    exact isUnit_of_mul_isUnit_left this
  exact (hu.mul_left_cancel h1).symm

omit [Fintype m] [Fintype ι] [DecidableEq m] [DecidableEq ι] in
theorem quotMat_map {B : Type} [CommRing B] (f : A →+* B) (M : Matrix ι ι A) :
    quotMat e (M.map f) = (quotMat e M).map f := by
  ext i j; simp [quotMat, Matrix.toBlocks₁₁, Matrix.toBlocks₂₁]

end Pure

theorem ordL_eq_neg_log {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] (x : K) :
    ordL x = -WithZero.log (Valued.v x) := by
  unfold ordL
  split_ifs with h
  · simp [h]
  · conv_rhs => rw [← WithZero.coe_unzero h]
    rfl

theorem isHermND_dbl {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J) : IsHermND σ (dblGram finSumFinEquiv J) := by
  refine ⟨fun i j => ?_, ?_⟩
  · obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨b, rfl⟩ := finSumFinEquiv.surjective j
    simp only [dblGram, blkMat, Matrix.submatrix_apply, Equiv.symm_apply_apply]
    rcases a with a | a <;> rcases b with b | b <;> simp [hJ.1]
  · rw [dblGram, det_blkMat]
    exact mul_ne_zero hJ.2 (by rw [Matrix.det_neg]; exact mul_ne_zero (pow_ne_zero _ (by simp)) hJ.2)

theorem exists_dbl_chart : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (Q : Matrix (Fin (n + n)) (Fin (n + n)) E) (hQ : Q = dblGram finSumFinEquiv J) (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L], ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (h : w.under (𝓞 F) = v), IsSplit (E := E) v → IsSelfDualAt σ J L v → ∀ e : GLoc σ J v ≃* GL (Fin n) (w.adicCompletion E), IsSplitChart σ J L h e → ∃ f : GLoc σ Q v ≃* GL (Fin (n + n)) (w.adicCompletion E), (∀ g, g ∈ KFin σ Q L v ↔ f g ∈ KGL w (n := (n + n))) ∧ (∀ y y', f (ioH _ σ hQ (y, y')) = blkGL finSumFinEquiv (e y, e y')) ∧ (∀ g, g ∈ siegelH (Fv F v) σ Q ↔ KeepsDiag finSumFinEquiv (f g).1) ∧ ∀ p : siegelH (Fv F v) σ Q, toCompl h (aH _ σ Q p).1 = (leviMat finSumFinEquiv (f p).1).det ∧ ∀ (w' : HeightOneSpectrum (𝓞 E)) (h' : w'.under (𝓞 F) = v), w ≠ w' → ordL (toCompl h' (aH _ σ Q p).1) = -ordL (quotMat finSumFinEquiv (f p).1).det := by
  intro F E _ _ _ _ _ σ hc n J hJ Q hQ L _ v w h hv hL e he
  have hQ' : IsHermND σ Q := hQ ▸ isHermND_dbl σ hJ
  obtain ⟨⟨a, ha, ea⟩, -⟩ := id he
  obtain ⟨τ, hτ⟩ := SplitChart.exists_splitPrime_eq hc hv h
  let φ := ConjPlace.complEquiv hc h hτ
  let β := Formalism.UG.bc (φ.symm : w.adicCompletion E →+* Fv F v) (blkGL finSumFinEquiv (a, a))
  have hβ : IsSplitBasis τ (sumLat finSumFinEquiv L L) β := by
    apply (ConjPlace.isFrameAt_iff hc h hτ β).1
    have heq : Formalism.UG.bc (φ : Fv F v →+* w.adicCompletion E) β =
        blkGL finSumFinEquiv (a, a) := by
      apply Units.ext
      exact Matrix.ext fun i j => φ.apply_symm_apply _
    rw [heq]
    exact GlobalTheory.T.isLatticeFrameAtPlace_directSum_blockDiagonal E w n L a ha
  obtain ⟨f₀, ⟨⟨b, hb, e0⟩, hK⟩⟩ :=
    ConjPlace.exists_isSplitChart_of_basis hc hQ' (isSelfDualAt_dbl hQ hL) h hτ hβ
  have hk := hb.inv_mul_mem (GlobalTheory.T.isLatticeFrameAtPlace_directSum_blockDiagonal E w n L a ha)
  have ef : ∀ g, f₀.trans (MulAut.conj (b⁻¹ * blkGL finSumFinEquiv (a, a))⁻¹) g =
      (blkGL finSumFinEquiv (a, a))⁻¹ * locMat σ Q h g * blkGL finSumFinEquiv (a, a) := fun g => by
    rw [MulEquiv.trans_apply, MulAut.conj_apply, e0]; group
  have hP : ∀ p : siegelH (Fv F v) σ Q, KeepsDiag finSumFinEquiv (locMat σ Q h p).1 := fun p =>
    (mem_siegelOf.1 p.2).map _ (toCompl h)
  refine ⟨f₀.trans (MulAut.conj (b⁻¹ * blkGL finSumFinEquiv (a, a))⁻¹), fun g => ?_, fun y y' => ?_, fun g => ?_,
    fun p => ⟨?_, fun w' h' hne => ?_⟩⟩
  · rw [MulEquiv.trans_apply, MulAut.conj_apply, inv_inv, Subgroup.mul_mem_cancel_right _ hk,
      Subgroup.mul_mem_cancel_left _ (inv_mem hk)]
    exact hK g
  · have h1 : locMat σ Q h (ioH _ σ hQ (y, y')) = blkGL finSumFinEquiv (locMat σ J h y, locMat σ J h y') :=
      bc_blkGL finSumFinEquiv (toCompl h) _ _
    rw [ef, h1, ← map_inv, ← map_mul, ← map_mul, ea, ea]
    rfl
  · rw [ef, keepsDiag_conj_iff]
    refine ⟨fun hg => hP ⟨g, hg⟩, fun hg => ?_⟩
    obtain ⟨τ, hτ⟩ := SplitChart.exists_splitPrime_eq hc hv h
    refine GlobalTheory.Core.Rk.IwSplit.mem_siegelH_of_split hc hQ hJ.2 τ (mem_stabGL_diagSub.2 ?_)
    rw [ConjPlace.locMat_eq hc h hτ] at hg
    have h2 := hg.map _ ((ConjPlace.complEquiv hc h hτ).symm : w.adicCompletion E →+* Fv F v)
    convert h2 using 1
    exact Matrix.ext fun i j => ((ConjPlace.complEquiv hc h hτ).symm_apply_apply _).symm
  · rw [ef, det_leviMat_conj _ a (hP p)]
    change toCompl h (leviMat finSumFinEquiv (matHom _ σ Q p).1).det =
      (leviMat finSumFinEquiv ((matHom _ σ Q p).1.map (toCompl h))).det
    rw [leviMat_map, RingHom.map_det, RingHom.mapMatrix_apply]
  · obtain ⟨c, hcv, -, hcc, -⟩ := ConjPlace.exists_conj_chart hc hJ hL hne h h' he
    rw [ef, det_quotMat_conj _ a (hP p)]
    have h1 : (quotMat finSumFinEquiv (locMat σ Q h p).1).det =
        toCompl h (quotMat finSumFinEquiv (matHom _ σ Q p).1).det := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, ← quotMat_map]
      rfl
    have h2 := congrArg (fun y => Valued.v (toCompl h' y)) (sigR_det_quot_mul_aH hQ hJ.2 p)
    simp only [map_mul, map_one, ← hcc, hcv] at h2
    rw [h1, ordL_eq_neg_log, ordL_eq_neg_log, eq_inv_of_mul_eq_one_right h2, WithZero.log_inv]

end GlobalTheory.LFun.DblSplit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsDoubledUnitaryChartSplitPlaceStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_doubled_unitary_chart_split_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (Q : Matrix (Fin (n + n)) (Fin (n + n)) E) (hQ : Q = dblGram finSumFinEquiv J) (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L], ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (h : w.under (𝓞 F) = v), IsSplit (E := E) v → IsSelfDualAt σ J L v → ∀ e : GLoc σ J v ≃* GL (Fin n) (w.adicCompletion E), IsSplitChart σ J L h e → ∃ f : GLoc σ Q v ≃* GL (Fin (n + n)) (w.adicCompletion E), (∀ g, g ∈ KFin σ Q L v ↔ f g ∈ KGL w (n := (n + n))) ∧ (∀ y y', f (ioH _ σ hQ (y, y')) = blkGL finSumFinEquiv (e y, e y')) ∧ (∀ g, g ∈ siegelH (Fv F v) σ Q ↔ KeepsDiag finSumFinEquiv (f g).1) ∧ ∀ p : siegelH (Fv F v) σ Q, toCompl h (aH _ σ Q p).1 = (leviMat finSumFinEquiv (f p).1).det ∧ ∀ (w' : HeightOneSpectrum (𝓞 E)) (h' : w'.under (𝓞 F) = v), w ≠ w' → ordL (toCompl h' (aH _ σ Q p).1) = -ordL (quotMat finSumFinEquiv (f p).1).det := by
  first | exact @GlobalTheory.LFun.DblSplit.exists_dbl_chart | exact GlobalTheory.LFun.DblSplit.exists_dbl_chart | (intros; apply GlobalTheory.LFun.DblSplit.exists_dbl_chart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelMeasurePushforwardEqProductRealMeasures
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelMeasurePushforwardEqProductRealMeasures
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.RealBoxMeasure

variable {D : D7}

theorem exists_realPart (θ : InfFam D) (hθ : IsInfFam θ) (W : HSp D) (hW : W.SigOK) (Fr : Frames W)
    (hFr : IsFrames W Fr) :
    ∃ φ : GA D W → ∀ ρ, Upq W ρ, Continuous φ ∧
      ∀ h ρ, UpqT.mat (φ h ρ) * Fr ρ = Fr ρ * infMat D.sp.cm.sig W.gram (θ ρ) h := by
  have hτ : GlobalTheory.Mem.Vol.IsCMFam (tauE D) := GlobalTheory.Mem.Vol.isCMFam_host _ D.host _ D.eTau
  obtain ⟨hcm, -⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm
  obtain ⟨e1, he1⟩ := GlobalTheory.Mem.InfGroup.real_points D.host.F D.host.E D.sp.cm.sig W.rank W.gram D.what₂.Tau (tauE D) θ
    (fun ρ => (W.sig (tauE D ρ)).1) (fun ρ => (W.sig (tauE D ρ)).2) Fr hcm hτ hθ (fun i => hW (tauE D i)) hFr
  obtain ⟨e0, he0⟩ := GlobalTheory.Mem.VolSplit.exists_adelic_split D.host.F D.host.E D.sp.cm.sig W.rank W.gram
  refine ⟨fun h => e1 (e0 h).1, e1.continuous.comp (continuous_fst.comp e0.continuous), fun h i => ?_⟩
  show UpqT.mat (e1 (e0 h).1 i) * Fr i = _
  rw [he1, (he0 h).2]; rfl

theorem mat_cancel (W : HSp D) (hW : W.SigOK) (Fr : Frames W) (hFr : IsFrames W Fr) (ρ : D.what₂.Tau)
    {b b' : Upq W ρ} (h : UpqT.mat b * Fr ρ = UpqT.mat b' * Fr ρ) : b = b' := by
  obtain ⟨C, h1, -⟩ := (GlobalTheory.Mem.SignatureFactor.exists_factor _ _ _ _ (hW (tauE D ρ))).2.2 (Fr ρ) (hFr ρ)
  apply (GlobalTheory.UpqTopology.upq_lcsc _ _).2.2.2.2.2.injective
  have h5 := congrArg (· * C) h
  simpa only [Matrix.mul_assoc, h1, Matrix.mul_one] using h5

theorem realMat_of (W : HSp D) (Fr : Frames W) (hFr : IsFrames W Fr) (ρ : D.what₂.Tau) (b : Upq W ρ)
    (M : Matrix (Fin W.rank) (Fin W.rank) ℂ) (h : UpqT.mat b * Fr ρ = Fr ρ * M) : realMat W Fr ρ b = M := by
  have hG := GlobalTheory.SmoothForms.RealPts.gramAt_unit W ρ
  unfold realMat conjFrame
  have e : (Fr ρ)ᴴ * Formalism.UG.Jpq (W.sig (tauE D ρ)).1 (W.sig (tauE D ρ)).2 * (Fr ρ * M) = gramAt D W ρ * M := by
    rw [← Matrix.mul_assoc, hFr ρ]
  rw [Matrix.mul_assoc (_ * _), h, e, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hG, Matrix.one_mul]

theorem realMat_mem (W : HSp D) (hW : W.SigOK) (Fr : Frames W) (hFr : IsFrames W Fr) (ρ : D.what₂.Tau) (b : Upq W ρ) :
    realMat W Fr ρ b ∈ Formalism.QuantumDeterminants.UH (gramAt D W ρ) :=
  conjFrame_mem_UH _ _ _ (GlobalTheory.Mem.SignatureFactor.exists_factor _ _ _ _ (hW (tauE D ρ))).1 _ _ (hFr ρ)
    (GlobalTheory.SmoothForms.RealPts.gramAt_unit W ρ) b

theorem infMat_realElt (θ : InfFam D) (hθ : IsInfFam θ) (W : HSp D) (u : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ)
    (hu : ∀ τ, u τ ∈ Formalism.QuantumDeterminants.UH (gramAt D W τ)) (ρ : D.what₂.Tau) :
    infMat D.sp.cm.sig W.gram (θ ρ) (realElt θ W u) = u ρ := by
  rw [realElt, GlobalTheory.RealTransSm.infMat_list_prod hθ u hu ρ _ (Finset.nodup_toList _),
    if_pos (Finset.mem_toList.2 (Finset.mem_univ ρ))]

theorem realElt_mem (θ : InfFam D) (W : HSp D) (u : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) :
    realElt θ W u ∈ GinfC W := by
  refine list_prod_mem fun x hx => ?_
  obtain ⟨τ, -, rfl⟩ := List.mem_map.1 hx
  exact GlobalTheory.PointAtPlaceHom.atTau_mem W τ (u τ)

theorem finE_realElt (θ : InfFam D) (W : HSp D) (u : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) :
    finE W (realElt θ W u) = 1 := by
  rw [Lev.finE_eq, (MonoidHom.mem_ker).1 (realElt_mem θ W u), map_one]

theorem continuous_realElt (θ : InfFam D) (hθ : IsInfFam θ) (W : HSp D) (hW : W.SigOK) (Fr : Frames W)
    (hFr : IsFrames W Fr) :
    Continuous fun b : (∀ ρ, Upq W ρ) => realElt θ W fun ρ => realMat W Fr ρ (b ρ) := by
  haveI : IsTopologicalGroup (GA D W) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  unfold realElt
  refine continuous_list_prod _ fun ρ _ => ?_
  have hκ : Continuous fun b : (∀ ρ, Upq W ρ) => realMat W Fr ρ (b ρ) := by
    unfold realMat conjFrame
    exact continuous_const.matrix_mul (((continuous_const.matrix_mul
      ((GlobalTheory.UpqTopology.upq_lcsc _ _).2.2.2.2.2.continuous.comp (continuous_apply ρ))).matrix_mul continuous_const))
  exact (GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ W ρ).comp_continuous hκ
    fun b => realMat_mem W hW Fr hFr ρ (b ρ)

theorem lintegral_levelSet_eq_pi : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (W : HSp D), W.SigOK → ∀ (K : Subgroup (GL (Fin W.rank) (Lev.EAf D))) (ν : Measure (GA D W)), IsMeasLev W K ν → ∀ Fr : Frames W, IsFrames W Fr → ∀ mR : ∀ ρ, Measure (Upq W ρ), (∀ ρ, Lev.IsMinf (mR ρ)) → ∀ Z : GA D W → ENNReal, Measurable Z → (∀ g, ∀ k ∈ levA W K, Z (g * k) = Z g) → MeasurableSet {h : GA D W | finE W h ∈ K} → ∫⁻ g in {h : GA D W | finE W h ∈ K}, Z g ∂ν = ∫⁻ b, Z (realElt θ W fun ρ => realMat W Fr ρ (b ρ)) ∂(Measure.pi mR) := by
  intro D θ hθ W hW K ν hν Fr hFr mR hmR Z hZ hZK hS
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.2.1
  obtain ⟨-, hsc, hbo, -⟩ := GlobalTheory.TwistAdelicTop.locallyCompact_secondCountable_borel_countable W
  haveI := hsc
  haveI := hbo
  haveI : ∀ ρ, SigmaFinite (mR ρ) := fun ρ => by haveI := (hmR ρ).1; infer_instance
  obtain ⟨φ, hφc, hφ⟩ := exists_realPart θ hθ W hW Fr hFr
  have hφm : Measurable φ := hφc.measurable
  set sec : (∀ ρ, Upq W ρ) → GA D W := fun b => realElt θ W fun ρ => realMat W Fr ρ (b ρ) with hsec
  have hsecm : Measurable (fun b => Z (sec b)) := hZ.comp (continuous_realElt θ hθ W hW Fr hFr).measurable
  obtain ⟨-, -, H⟩ := hν
  obtain ⟨-, H1⟩ := H θ hθ
  obtain ⟨-, H2⟩ := H1 Fr hFr
  have hpi : Measure.pi mR = Measure.map φ (ν.restrict {h : GA D W | finE W h ∈ K}) := by
    refine Measure.pi_eq fun B hB => ?_
    have hm : MeasurableSet (φ ⁻¹' Set.univ.pi B) := hφm (MeasurableSet.univ_pi hB)
    rw [Measure.map_apply hφm (MeasurableSet.univ_pi hB), Measure.restrict_apply hm, ← H2 mR hmR B hB]
    congr 1
    ext h
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_univ_pi, Set.mem_setOf_eq]
    rw [and_comm]
    refine and_congr_right fun _ => forall_congr' fun ρ => ⟨fun hb => ⟨φ h ρ, hb, hφ h ρ⟩, ?_⟩
    rintro ⟨b, hb, hbe⟩
    rwa [mat_cancel W hW Fr hFr ρ (hbe.trans (hφ h ρ).symm)] at hb
  have hfac : ∀ h ∈ {h : GA D W | finE W h ∈ K}, Z h = Z (sec (φ h)) := by
    intro h hh
    have e : ∀ ρ, infMat D.sp.cm.sig W.gram (θ ρ) (sec (φ h)) = infMat D.sp.cm.sig W.gram (θ ρ) h := fun ρ => by
      rw [hsec]
      dsimp only
      rw [infMat_realElt θ hθ W _ (fun τ => realMat_mem W hW Fr hFr τ _) ρ]
      exact realMat_of W Fr hFr ρ _ _ (hφ h ρ)
    have hk : (sec (φ h))⁻¹ * h ∈ levA W K := by
      refine ⟨(GlobalTheory.SmoothForms.RealPts.glue θ hθ W).1 _ fun ρ => ?_, ?_⟩
      · rw [GlobalTheory.PointAtPlaceHom.infMat_mul, ← e ρ, ← GlobalTheory.PointAtPlaceHom.infMat_mul, inv_mul_cancel,
          GlobalTheory.PointAtPlaceHom.infMat_one]
      · show finE W ((sec (φ h))⁻¹ * h) ∈ K
        rw [map_mul, map_inv, hsec]
        dsimp only
        rw [finE_realElt, inv_one, one_mul]
        exact hh
    rw [← hZK (sec (φ h)) _ hk, mul_inv_cancel_left]
  calc ∫⁻ g in {h : GA D W | finE W h ∈ K}, Z g ∂ν
      = ∫⁻ g in {h : GA D W | finE W h ∈ K}, Z (sec (φ g)) ∂ν := setLIntegral_congr_fun hS hfac
    _ = ∫⁻ b, Z (sec b) ∂(Measure.map φ (ν.restrict {h : GA D W | finE W h ∈ K})) :=
        (lintegral_map hsecm hφm).symm
    _ = _ := by rw [← hpi]

end GlobalTheory.RealBoxMeasure
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelMeasurePushforwardEqProductRealMeasuresStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_measure_pushforward_eq_product_real_measures : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (W : HSp D), W.SigOK → ∀ (K : Subgroup (GL (Fin W.rank) (Lev.EAf D))) (ν : Measure (GA D W)), IsMeasLev W K ν → ∀ Fr : Frames W, IsFrames W Fr → ∀ mR : ∀ ρ, Measure (Upq W ρ), (∀ ρ, Lev.IsMinf (mR ρ)) → ∀ Z : GA D W → ENNReal, Measurable Z → (∀ g, ∀ k ∈ levA W K, Z (g * k) = Z g) → MeasurableSet {h : GA D W | finE W h ∈ K} → ∫⁻ g in {h : GA D W | finE W h ∈ K}, Z g ∂ν = ∫⁻ b, Z (realElt θ W fun ρ => realMat W Fr ρ (b ρ)) ∂(Measure.pi mR) := by
  first | exact @GlobalTheory.RealBoxMeasure.lintegral_levelSet_eq_pi | exact GlobalTheory.RealBoxMeasure.lintegral_levelSet_eq_pi | (intros; apply GlobalTheory.RealBoxMeasure.lintegral_levelSet_eq_pi <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaIsotropicColumnsRingIsoComplex
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaIsotropicColumnsRingIsoComplex
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
open GlobalTheory.AdelicU Formalism.UG

open Matrix Formalism.UG

namespace GlobalTheory.Core.Rk.IwArch

section IsoCol

variable {A : Type} [CommRing A]

theorem map_cT_rect (σ : A →+* A) (f : A →+* ℂ) (hσ : ∀ x, f (σ x) = star (f x)) {m p : Type}
    (M : Matrix m p A) : (cT σ M).map f = (M.map f)ᴴ := by
  ext i j
  simp [cT, conjTranspose_apply, hσ]

theorem exists_compact_keep_cols {n r : ℕ} (σ : A →+* A) (f : A →+* ℂ) (hf : Function.Bijective f)
    (hσ : ∀ x, f (σ x) = star (f x)) {J : Matrix (Fin n) (Fin n) A} (b : GL (Fin n) A) (ε : Fin n → Bool)
    (hb : cT σ b.1 * J * b.1 = (Matrix.diagonal fun i => if ε i then 1 else -1))
    (X : Matrix (Fin n) (Fin r) A) (hX : cT σ X * J * X = 0) (g : GL (Fin n) A) (hg : g ∈ UJ σ J) :
    ∃ k ∈ UJ σ J, b⁻¹ * k * b ∈ UJ σ (1 : Matrix (Fin n) (Fin n) A) ∧
      ∃ β : Matrix (Fin r) (Fin r) A, (g * k⁻¹).1 * X = X * β := by
  set F := RingEquiv.ofBijective f hf
  have hfF : ∀ z : ℂ, f (F.symm z) = z := fun z => F.apply_symm_apply z
  have hfinj : ∀ {p q : Type} (M N : Matrix p q A), M.map f = N.map f → M = N := fun M N h =>
    Matrix.ext fun i j => hf.1 (congrFun (congrFun h i) j)
  set D : Matrix (Fin n) (Fin n) A := Matrix.diagonal fun i => if ε i then 1 else -1 with hD
  have hJm : D.map f = Formalism.REAL.Jm ε := by
    ext i j
    by_cases h : i = j
    · subst h; by_cases he : ε i <;> simp [D, Formalism.REAL.Jm, he]
    · simp [D, Formalism.REAL.Jm, h]

  set h0 := b⁻¹ * g * b with hh0def
  have hh0 : h0 ∈ UJ σ D := hb ▸ conj_mem_UJ σ b hg
  have hh0' : Formalism.REAL.inUJ ε (h0.1.map f) := by
    have e : cT σ h0.1 * D * h0.1 = D := hh0
    have := congrArg (fun M => M.map f) e
    simp only [Matrix.map_mul, map_cT_rect σ f hσ, hJm] at this
    exact this
  let g' : Formalism.REAL.UJ ε := ⟨bc f h0, hh0'⟩

  set Y := (b⁻¹).1 * X with hYdef
  set X' := Y.map f with hX'def
  have hY : cT σ Y * D * Y = 0 := by
    rw [← hb, hYdef, cT_mul]
    calc cT σ X * cT σ (b⁻¹).1 * (cT σ b.1 * J * b.1) * ((b⁻¹).1 * X)
        = cT σ X * (cT σ (b⁻¹).1 * (cT σ b.1 * J * b.1) * (b⁻¹).1) * X := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [cT_inv_cancel, hX]
  have hiso0 : X'ᴴ * Formalism.REAL.Jm ε * X' = 0 := by
    have := congrArg (fun M => M.map f) hY
    simp only [Matrix.map_mul, map_cT_rect σ f hσ, hJm, Matrix.map_zero _ (map_zero f)] at this
    exact this
  set W := LinearMap.range X'.mulVecLin with hWdef
  let Wf : Fin 2 → Submodule ℂ (Fin n → ℂ) := ![⊥, W]
  have hflag : GlobalTheory.FlagMeas.IsIsoFlag ε (a := 1) (fun _ => Module.finrank ℂ W) Wf := by
    refine ⟨rfl, ?_, ?_, ?_⟩
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [Wf]
    · intro i
      fin_cases i
      show Module.finrank ℂ W = Module.finrank ℂ (⊥ : Submodule ℂ (Fin n → ℂ)) + Module.finrank ℂ W
      rw [finrank_bot, zero_add]
    · intro x hx y hy
      obtain ⟨u, rfl⟩ := hx
      obtain ⟨v, rfl⟩ := hy
      simp only [Matrix.mulVecLin_apply]
      rw [Matrix.star_mulVec, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
        ← Matrix.mul_assoc, hiso0, Matrix.vecMul_zero, zero_dotProduct]
  obtain ⟨k0, hk0, hk0W⟩ := GlobalTheory.RealIwasawa.exists_stab_mul_compact hflag g'
  have hkeep : ∀ y ∈ W, Formalism.MainNotions.S.uMat (g' * k0⁻¹) *ᵥ y ∈ W := fun y hy => hk0W 1 y hy

  let k1 : GL (Fin n) A := bc (F.symm : ℂ →+* A) (k0 : (Matrix (Fin n) (Fin n) ℂ)ˣ)
  have hbc : ∀ u : (Matrix (Fin n) (Fin n) ℂ)ˣ, (bc (F.symm : ℂ →+* A) u).1.map f = u.1 := by
    intro u; ext i j; simp [bc, hfF]
  have hk1f : k1.1.map f = Formalism.MainNotions.S.uMat k0 := hbc _
  have hk1if : (k1⁻¹).1.map f = Formalism.MainNotions.S.uMat k0⁻¹ := by
    have : k1⁻¹ = bc (F.symm : ℂ →+* A) ((k0⁻¹ : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) := by
      simp [k1, map_inv]
    rw [this]; exact hbc _
  have hk1D : k1 ∈ UJ σ D := by
    show cT σ k1.1 * D * k1.1 = D
    apply hfinj
    rw [Matrix.map_mul, Matrix.map_mul, map_cT_rect σ f hσ, hk1f, hJm]
    exact k0.2
  have hk1one : k1 ∈ UJ σ (1 : Matrix (Fin n) (Fin n) A) := by
    show cT σ k1.1 * 1 * k1.1 = 1
    apply hfinj
    rw [Matrix.map_mul, Matrix.map_mul, map_cT_rect σ f hσ, hk1f, Matrix.map_one _ (map_zero f) (map_one f),
      Matrix.mul_one]
    exact hk0
  refine ⟨b * k1 * b⁻¹, ?_, ?_, ?_⟩
  · have hk1' : k1 ∈ UJ σ (cT σ b.1 * J * b.1) := by rw [hb]; exact hk1D
    have := conj_mem_UJ σ b⁻¹ hk1'
    rw [cT_inv_cancel, inv_inv] at this
    exact this
  · convert hk1one using 1
    group

  set H := (h0 * k1⁻¹).1 with hHdef
  have hHf : H.map f = Formalism.MainNotions.S.uMat (g' * k0⁻¹) := by
    rw [hHdef, Units.val_mul, Matrix.map_mul, hk1if]
    rfl
  have hcol : ∀ c : Fin r, ∃ w : Fin r → ℂ, X' *ᵥ w = H.map f *ᵥ (X' *ᵥ Pi.single c 1) := by
    intro c
    have hm := hkeep _ (LinearMap.mem_range_self X'.mulVecLin (Pi.single c 1))
    rw [← hHf] at hm
    obtain ⟨w, hw⟩ := hm
    exact ⟨w, hw⟩
  choose w hw using hcol
  let β' : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun i c => w c i
  have hHX : H.map f * X' = X' * β' := by
    ext i c
    have h1 := congrFun (hw c) i
    have e1 : (H.map f * X') i c = (H.map f *ᵥ (X' *ᵥ Pi.single c 1)) i := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one]; rfl
    have e2 : (X' * β') i c = (X' *ᵥ w c) i := by
      rw [Matrix.mul_apply, Matrix.mulVec, dotProduct]; rfl
    rw [e1, e2, h1]
  refine ⟨β'.map F.symm, ?_⟩
  have hβf : (β'.map F.symm).map f = β' := by ext i j; simp [hfF]
  have hHY : H * Y = Y * β'.map F.symm := by
    have e1 : (H * Y).map f = H.map f * X' := Matrix.map_mul
    have e2 : (Y * β'.map F.symm).map f = X' * β' := by rw [Matrix.map_mul, hβf]
    apply hfinj
    rw [e1, e2]
    exact hHX
  have hgk : g * (b * k1 * b⁻¹)⁻¹ = b * (h0 * k1⁻¹) * b⁻¹ := by
    rw [hh0def]; group
  rw [hgk, Units.val_mul, Units.val_mul]
  calc b.1 * H * (b⁻¹).1 * X = b.1 * (H * Y) := by rw [hYdef]; simp only [Matrix.mul_assoc]
    _ = b.1 * ((b⁻¹).1 * X * β'.map F.symm) := by rw [hHY]
    _ = X * β'.map F.symm := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]

theorem iw_iso_cols : ∀ {A : Type} [CommRing A] {n r : ℕ} (σ : A →+* A) (f : A →+* ℂ), Function.Bijective f → (∀ x, f (σ x) = star (f x)) → ∀ {J : Matrix (Fin n) (Fin n) A} (b : GL (Fin n) A) (ε : Fin n → Bool), Formalism.UG.cT σ b.1 * J * b.1 = (Matrix.diagonal fun i => if ε i then 1 else -1) → ∀ (X : Matrix (Fin n) (Fin r) A), Formalism.UG.cT σ X * J * X = 0 → ∀ g : GL (Fin n) A, g ∈ UJ σ J → ∃ k ∈ UJ σ J, b⁻¹ * k * b ∈ UJ σ (1 : Matrix (Fin n) (Fin n) A) ∧ ∃ β : Matrix (Fin r) (Fin r) A, (g * k⁻¹).1 * X = X * β  := by
  intro A _ n r σ f hf hσ J b ε hb X hX g hg
  exact exists_compact_keep_cols σ f hf hσ b ε hb X hX g hg

end IsoCol

end GlobalTheory.Core.Rk.IwArch
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaIsotropicColumnsRingIsoComplexStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
open GlobalTheory.AdelicU Formalism.UG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawa_isotropic_columns_ring_iso_complex : ∀ {A : Type} [CommRing A] {n r : ℕ} (σ : A →+* A) (f : A →+* ℂ), Function.Bijective f → (∀ x, f (σ x) = star (f x)) → ∀ {J : Matrix (Fin n) (Fin n) A} (b : GL (Fin n) A) (ε : Fin n → Bool), Formalism.UG.cT σ b.1 * J * b.1 = (Matrix.diagonal fun i => if ε i then 1 else -1) → ∀ (X : Matrix (Fin n) (Fin r) A), Formalism.UG.cT σ X * J * X = 0 → ∀ g : GL (Fin n) A, g ∈ UJ σ J → ∃ k ∈ UJ σ J, b⁻¹ * k * b ∈ UJ σ (1 : Matrix (Fin n) (Fin n) A) ∧ ∃ β : Matrix (Fin r) (Fin r) A, (g * k⁻¹).1 * X = X * β := by
  first | exact @GlobalTheory.Core.Rk.IwArch.iw_iso_cols | exact GlobalTheory.Core.Rk.IwArch.iw_iso_cols | (intros; apply GlobalTheory.Core.Rk.IwArch.iw_iso_cols <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ArchimedeanMajorantStabilisersConjugate
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ArchimedeanMajorantStabilisersConjugate
noncomputable section

namespace GlobalTheory.MajorantConj

section General

open scoped Matrix

abbrev sgnDiag (A : Type) [CommRing A] {n : ℕ} (ε : Fin n → Bool) : Matrix (Fin n) (Fin n) A :=
  Matrix.diagonal fun i => if ε i then 1 else -1

theorem re_form {n : ℕ} (ε : Fin n → Bool) (x : Fin n → ℂ) :
    (star x ⬝ᵥ (sgnDiag ℂ ε *ᵥ x)).re = ∑ i, (if ε i then 1 else -1) * Complex.normSq (x i) := by
  simp only [sgnDiag, Matrix.mulVec_diagonal, dotProduct, Complex.re_sum, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp [Complex.mul_re, Complex.normSq_apply] <;> ring

theorem card_neg_le {n : ℕ} (ε ε' : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ)
    (h : Mᴴ * sgnDiag ℂ ε * M = sgnDiag ℂ ε') :
    Fintype.card {i // ε' i = false} ≤ Fintype.card {i // ε i = false} := by
  have key : ∀ x : Fin n → ℂ,
      star x ⬝ᵥ (sgnDiag ℂ ε' *ᵥ x) = star (M *ᵥ x) ⬝ᵥ (sgnDiag ℂ ε *ᵥ (M *ᵥ x)) := by
    intro x
    rw [← h, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_assoc]
  let T := (LinearMap.funLeft ℂ ℂ (Subtype.val : {i // ε i = false} → Fin n)) ∘ₗ M.mulVecLin ∘ₗ
    (Function.ExtendByZero.linearMap ℂ ℂ (Subtype.val : {i // ε' i = false} → Fin n))
  have hT : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    obtain ⟨x, hx⟩ : ∃ x : Fin n → ℂ, x = Function.extend Subtype.val y 0 := ⟨_, rfl⟩
    have hxt : ∀ i, ε' i = true → x i = 0 := by
      intro i hi
      rw [hx, Function.extend_apply']
      · rfl
      · rintro ⟨j, rfl⟩
        rw [j.2] at hi
        exact Bool.false_ne_true hi
    have hxf : ∀ j : {i // ε' i = false}, x j.1 = y j := fun j => by
      rw [hx]
      exact Subtype.val_injective.extend_apply _ _ _
    have hv : ∀ j : {i // ε i = false}, (M *ᵥ x) j.1 = 0 := fun j => by
      have := congrFun hy j
      rw [hx]
      exact this
    have h1 := congrArg Complex.re (key x)
    rw [re_form, re_form] at h1
    have hL : ∀ i, (if ε' i then (1 : ℝ) else -1) * Complex.normSq (x i) = -Complex.normSq (x i) := by
      intro i
      cases hi : ε' i
      · simp
      · simp [hxt i hi]
    have hR : 0 ≤ ∑ i, (if ε i then (1 : ℝ) else -1) * Complex.normSq ((M *ᵥ x) i) := by
      apply Finset.sum_nonneg
      intro i _
      cases hi : ε i
      · simp [hv ⟨i, hi⟩]
      · simp [Complex.normSq_nonneg]
    simp only [hL, Finset.sum_neg_distrib] at h1
    have hz : ∑ i, Complex.normSq (x i) = 0 :=
      le_antisymm (by linarith) (Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _)
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Complex.normSq_nonneg _)] at hz
    funext j
    rw [← hxf j]
    exact Complex.normSq_eq_zero.mp (hz j.1 (Finset.mem_univ _))
  have := LinearMap.finrank_le_finrank_of_injective hT
  simpa [Module.finrank_fintype_fun_eq_card] using this

theorem exists_perm {n : ℕ} (ε ε' : Fin n → Bool)
    (h : Fintype.card {i // ε' i = false} = Fintype.card {i // ε i = false}) :
    ∃ π : Equiv.Perm (Fin n), ∀ i, ε' (π i) = ε i := by
  classical
  have e0 : {i // ε i = false} ≃ {i // ε' i = false} := Fintype.equivOfCardEq h.symm
  have e1 : {i // ¬ε i = false} ≃ {i // ¬ε' i = false} := Fintype.equivOfCardEq (by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, h])
  refine ⟨(Equiv.sumCompl fun i => ε i = false).symm.trans
    ((e0.sumCongr e1).trans (Equiv.sumCompl fun i => ε' i = false)), fun i => ?_⟩
  by_cases hi : ε i = false
  · simp only [Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_pos (p := fun j => ε j = false) hi, Equiv.sumCongr_apply, Sum.map_inl,
      Equiv.sumCompl_apply_inl]
    rw [hi]
    exact (e0 ⟨i, hi⟩).2
  · simp only [Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_neg (p := fun j => ε j = false) hi, Equiv.sumCongr_apply, Sum.map_inr,
      Equiv.sumCompl_apply_inr]
    have := (e1 ⟨i, hi⟩).2
    simp only [Bool.not_eq_false] at hi this
    rw [hi, this]

variable {A : Type} [CommRing A] (s : A →+* A) {n : ℕ}

theorem cT_mul (M N : Matrix (Fin n) (Fin n) A) : Formalism.UG.cT s (M * N) = Formalism.UG.cT s N * Formalism.UG.cT s M := by
  unfold Formalism.UG.cT
  rw [Matrix.map_mul, Matrix.transpose_mul]

theorem cT_one : Formalism.UG.cT s (1 : Matrix (Fin n) (Fin n) A) = 1 := by
  unfold Formalism.UG.cT
  rw [Matrix.map_one s (map_zero s) (map_one s), Matrix.transpose_one]

theorem congr_inv {J D : Matrix (Fin n) (Fin n) A} (b : GL (Fin n) A) (h : Formalism.UG.cT s b.1 * J * b.1 = D) :
    Formalism.UG.cT s (b⁻¹).1 * D * (b⁻¹).1 = J := by
  rw [← h]
  have h1 : Formalism.UG.cT s (b⁻¹).1 * Formalism.UG.cT s b.1 = 1 := by
    rw [← cT_mul, Units.mul_inv, cT_one]
  calc Formalism.UG.cT s (b⁻¹).1 * (Formalism.UG.cT s b.1 * J * b.1) * (b⁻¹).1
      = (Formalism.UG.cT s (b⁻¹).1 * Formalism.UG.cT s b.1) * J * (b.1 * (b⁻¹).1) := by
        simp only [Matrix.mul_assoc]
    _ = J := by rw [h1, Units.mul_inv, Matrix.one_mul, Matrix.mul_one]

theorem congr_mul {J D D' : Matrix (Fin n) (Fin n) A} (b c : GL (Fin n) A) (h : Formalism.UG.cT s b.1 * J * b.1 = D)
    (h' : Formalism.UG.cT s c.1 * D * c.1 = D') : Formalism.UG.cT s (b * c).1 * J * (b * c).1 = D' := by
  rw [← h', ← h, Units.val_mul, cT_mul]
  simp only [Matrix.mul_assoc]

theorem card_neg_le' (φ : A →+* ℂ) (hφ : ∀ y, starRingEnd ℂ (φ y) = φ (s y)) (ε ε' : Fin n → Bool)
    (M : Matrix (Fin n) (Fin n) A) (h : Formalism.UG.cT s M * sgnDiag A ε * M = sgnDiag A ε') :
    Fintype.card {i // ε' i = false} ≤ Fintype.card {i // ε i = false} := by
  have hc : (Formalism.UG.cT s M).map φ = (M.map φ)ᴴ := by
    ext i j
    show φ (s (M j i)) = star (φ (M j i))
    rw [← hφ]
    rfl
  have hd : ∀ e : Fin n → Bool, (sgnDiag A e).map φ = sgnDiag ℂ e := by
    intro e
    rw [sgnDiag, Matrix.diagonal_map (map_zero φ)]
    congr 1
    funext i
    split_ifs <;> simp
  have h2 := congrArg (fun X => X.map φ) h
  simp only [Matrix.map_mul, hc, hd] at h2
  exact card_neg_le ε ε' (M.map φ) h2

def permGL (π : Equiv.Perm (Fin n)) : GL (Fin n) A where
  val := (1 : Matrix (Fin n) (Fin n) A).submatrix id π
  inv := (1 : Matrix (Fin n) (Fin n) A).submatrix π id
  val_inv := by
    rw [Matrix.submatrix_mul_equiv]
    simp
  inv_val := by
    ext i j
    simp [Matrix.mul_apply, Matrix.one_apply]

theorem permGL_diagonal (π : Equiv.Perm (Fin n)) (d : Fin n → A) :
    Formalism.UG.cT s (permGL (A := A) π).1 * Matrix.diagonal d * (permGL (A := A) π).1 = Matrix.diagonal fun i => d (π i) := by
  have hP : ((permGL (A := A) π).1).map s = (permGL (A := A) π).1 := by
    show ((1 : Matrix (Fin n) (Fin n) A).submatrix id π).map s = (1 : Matrix (Fin n) (Fin n) A).submatrix id π
    rw [← Matrix.submatrix_map, Matrix.map_one s (map_zero s) (map_one s)]
  unfold Formalism.UG.cT
  rw [hP]
  show ((1 : Matrix (Fin n) (Fin n) A).submatrix id π)ᵀ * Matrix.diagonal d *
    (1 : Matrix (Fin n) (Fin n) A).submatrix id π = _
  ext i j
  simp [Matrix.mul_apply, Matrix.one_apply, Matrix.diagonal_apply, Matrix.transpose_apply]
  split_ifs with hij
  · rw [hij]
  · rfl

theorem exists_unitary (φ : A →+* ℂ) (hφ : ∀ y, starRingEnd ℂ (φ y) = φ (s y)) {J : Matrix (Fin n) (Fin n) A}
    {ε ε' : Fin n → Bool} (b b' : GL (Fin n) A) (h : Formalism.UG.cT s b.1 * J * b.1 = sgnDiag A ε)
    (h' : Formalism.UG.cT s b'.1 * J * b'.1 = sgnDiag A ε') :
    ∃ P ∈ Formalism.UG.UJ s (1 : Matrix (Fin n) (Fin n) A), b' * P * b⁻¹ ∈ Formalism.UG.UJ s J := by
  have hle : Fintype.card {i // ε' i = false} ≤ Fintype.card {i // ε i = false} :=
    card_neg_le' s φ hφ ε ε' (b⁻¹ * b').1 (congr_mul s b⁻¹ b' (congr_inv s b h) h')
  have hge : Fintype.card {i // ε i = false} ≤ Fintype.card {i // ε' i = false} :=
    card_neg_le' s φ hφ ε' ε (b'⁻¹ * b).1 (congr_mul s b'⁻¹ b (congr_inv s b' h') h)
  obtain ⟨π, hπ⟩ := exists_perm ε ε' (le_antisymm hle hge)
  refine ⟨permGL π, ?_, ?_⟩
  · show Formalism.UG.cT s (permGL (A := A) π).1 * 1 * (permGL (A := A) π).1 = 1
    have := permGL_diagonal s π (fun _ => (1 : A))
    simpa [Matrix.diagonal_one] using this
  · show Formalism.UG.cT s (b' * permGL π * b⁻¹).1 * J * (b' * permGL π * b⁻¹).1 = J
    have h1 : Formalism.UG.cT s (b' * permGL π).1 * J * (b' * permGL π).1 = sgnDiag A ε := by
      have := congr_mul s b' (permGL π) h' (permGL_diagonal s π (fun i => if ε' i then (1 : A) else -1))
      simpa [sgnDiag, hπ] using this
    exact congr_mul s (b' * permGL π) b⁻¹ h1 (congr_inv s b h)

end General

open scoped NNReal Matrix TensorProduct Topology
open Filter NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.EisCont GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Core.Rk.SWLaw (dblDec zeroSp)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem stabArch_conj : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (a a' : GL (Fin n) (AF F ⊗[F] E)), IsMajorantFrame σ J a → IsMajorantFrame σ J a' → ∀ w : InfinitePlace F, ∃ g : GArch σ J w, ∀ k : GArch σ J w, k ∈ stabArch σ J w (Formalism.UG.bc (compInf F E w) a') ↔ g⁻¹ * k * g ∈ stabArch σ J w (Formalism.UG.bc (compInf F E w) a) := by
  intro F E _ _ _ _ _ σ hcm n J hJ a a' ha ha' w
  obtain ⟨ε, hε⟩ := ha w
  obtain ⟨ε', hε'⟩ := ha' w
  generalize Formalism.UG.bc (compInf F E w) a = b at hε ⊢
  generalize Formalism.UG.bc (compInf F E w) a' = b' at hε' ⊢
  obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
  obtain ⟨P, hP, hg⟩ := exists_unitary (sigR w.Completion σ) (infEmb τ) (fun y => infEmb_sigR hcm τ y) b b' hε hε'
  have key : ∀ m : GL (Fin n) (w.Completion ⊗[F] E),
      b⁻¹ * ((b' * P * b⁻¹)⁻¹ * m * (b' * P * b⁻¹)) * b = P⁻¹ * (b'⁻¹ * m * b') * P := fun m => by group
  refine ⟨(⟨b' * P * b⁻¹, hg⟩ : HR w.Completion σ J), fun k => ?_⟩
  unfold stabArch
  first
  | (show b'⁻¹ * AdelicU.matHom w.Completion σ J k * b'⁻¹⁻¹ ∈ Formalism.UG.UJ (sigR w.Completion σ) 1 ↔
        b⁻¹ * ((b' * P * b⁻¹)⁻¹ * AdelicU.matHom w.Completion σ J k * (b' * P * b⁻¹)) * b⁻¹⁻¹ ∈
          Formalism.UG.UJ (sigR w.Completion σ) 1
     rw [inv_inv, inv_inv, key, mul_mem_cancel_right hP, mul_mem_cancel_left (inv_mem hP)])
  | (simp only [Subgroup.mem_comap, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply]
     simp only [map_mul, map_inv, inv_inv]
     exact (mul_mem_cancel_right hP).symm.trans ((mul_mem_cancel_left (inv_mem hP)).symm.trans
       (by rw [← key]; exact Iff.rfl)))

end GlobalTheory.MajorantConj

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ArchimedeanMajorantStabilisersConjugateStatement
open scoped NNReal Matrix TensorProduct Topology
open Filter NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.EisCont GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Core.Rk.SWLaw (dblDec zeroSp)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_majorant_stabilisers_conjugate : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (a a' : GL (Fin n) (AF F ⊗[F] E)), IsMajorantFrame σ J a → IsMajorantFrame σ J a' → ∀ w : InfinitePlace F, ∃ g : GArch σ J w, ∀ k : GArch σ J w, k ∈ stabArch σ J w (Formalism.UG.bc (compInf F E w) a') ↔ g⁻¹ * k * g ∈ stabArch σ J w (Formalism.UG.bc (compInf F E w) a) := by
  first | exact @GlobalTheory.MajorantConj.stabArch_conj | exact GlobalTheory.MajorantConj.stabArch_conj | (intros; apply GlobalTheory.MajorantConj.stabArch_conj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateEvaluationMapIntertwinesRealPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateEvaluationMapIntertwinesRealPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Core.Mi.ConjEquiv

open GlobalTheory.ConjRowMult Formalism.L2.SG.EvalTOntoRep

theorem conjMap_equiv : GlobalTheory.Published.DiscreteSeriesClassification → ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)) (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), S = parB (Ptw D) 0 → IsInfFam θ → GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) → GlobalTheory.Core.Mi.IdE X → Matches X h J χ t → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ (M.rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : M.Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u))) ψ) → ∀ τ : D.what₂.Tau, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ (v : M.Vec) (w : M.sm τ), (w : M.H τ) = M.rep τ g (v τ) → GlobalTheory.ConjRowMult.conjMap X M c Φ h t (Function.update v τ w) = rTr (D.sp.Y 0) (atTau θ (D.sp.Y 0) τ g) (GlobalTheory.ConjRowMult.conjMap X M c Φ h t v) := by
  intro _hcl D X h θ S M J χ t c _hS hθ _hgap hιE hM hc Φ hΦ hrep τ g hg v w hw
  obtain ⟨hfin, -, hreal, -⟩ := GlobalTheory.T.modelIdentification_respects_real_and_finite D X h θ hθ hιE
  obtain ⟨ha2, ha1, -⟩ := hreal τ g hg
  set a := iotaX X h (atTau θ (D.sp.Y 0) τ g) with ha
  have hvec : vecC X M c (Function.update v τ w) =
      fun p => X.B.σ p (uMat (a.1 p)) (vecC X M c v p) := by
    refine vecC_eq X M c _ _ fun τ' => ?_
    have e1 : vecC X M c v (X.pl.symm τ') = c τ' (v τ' : M.H τ') := by
      unfold vecC
      exact Equiv.piCongrLeft_apply_apply _ _ _ _
    rw [e1]
    by_cases ht : τ' = τ
    · subst ht
      rw [Function.update_self, hw, hc τ' g hg]
    · rw [Function.update_of_ne ht, ha1 (X.pl.symm τ') (fun e => ht (X.pl.symm.injective e))]
      have h1 : X.B.σ (X.pl.symm τ') 1 = 1 := (X.ds (X.pl.symm τ')).2.2.1.1.1
      have h2 : uMat (1 : Formalism.REAL.UJ (X.B.I.ε (X.pl.symm τ'))) = 1 := rfl
      rw [h2, h1]
      rfl
  have htens : X.B.tens (vecC X M c (Function.update v τ w)) = X.B.σs a.1 (X.B.tens (vecC X M c v)) := by
    rw [hvec, X.B.tens_spec.2.1]
  have haeq : ((a.1, 1) : X.B.I.GA) = a := Prod.ext rfl ha2.symm
  obtain ⟨T, hT, hTΦ⟩ := Submodule.mem_map.1 hΦ
  have hΦx : ∀ x, Φ x = X.B.Re (T x) := fun x => by rw [← hTΦ]; rfl
  have hcomm := (GlobalTheory.IdemProj.re_orth_proj X.B).2.1 a.1
  have key : ∀ x, Φ (X.B.σs a.1 x) = X.B.R a (Φ x) := by
    intro x
    rw [hΦx, hΦx, ← haeq]
    have e1 := congrArg (fun L => L x) (hT a.1)
    simp only [ContinuousLinearMap.comp_apply] at e1
    rw [e1]
    exact congrArg (fun L => L (T x)) hcomm
  obtain ⟨ψ, hψ⟩ := hrep v
  have hψ' : IsContRep X (Φ (X.B.tens (vecC X M c (Function.update v τ w)))) (fun x => ψ (x * a)) := by
    rw [htens, key]
    exact contRep_reg X hψ a
  funext y
  rw [conjMap_apply, contRepL_spec X hψ']
  show _ = conjMap X M c Φ h t v (y * atTau θ (D.sp.Y 0) τ g)
  rw [conjMap_apply, contRepL_spec X hψ]
  congr 1
  have hti : (iotaX X h t⁻¹).1 = 1 := by rw [map_inv, Prod.fst_inv, (hfin t).1 hM.1, inv_one]
  rw [map_mul, map_mul, map_mul, ← ha, mul_assoc]
  beta_reduce
  rw [mul_assoc]
  congr 2
  exact Prod.ext (by rw [Prod.fst_mul, Prod.fst_mul, hti, one_mul, mul_one])
    (by rw [Prod.snd_mul, Prod.snd_mul, ha2, one_mul, mul_one])

end GlobalTheory.Core.Mi.ConjEquiv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateEvaluationMapIntertwinesRealPlacesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_evaluation_map_intertwines_real_places : GlobalTheory.Published.DiscreteSeriesClassification → ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)) (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), S = parB (Ptw D) 0 → IsInfFam θ → GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) → GlobalTheory.Core.Mi.IdE X → Matches X h J χ t → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ (M.rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : M.Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u))) ψ) → ∀ τ : D.what₂.Tau, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ (v : M.Vec) (w : M.sm τ), (w : M.H τ) = M.rep τ g (v τ) → GlobalTheory.ConjRowMult.conjMap X M c Φ h t (Function.update v τ w) = rTr (D.sp.Y 0) (atTau θ (D.sp.Y 0) τ g) (GlobalTheory.ConjRowMult.conjMap X M c Φ h t v) := by
  first | exact @GlobalTheory.Core.Mi.ConjEquiv.conjMap_equiv | exact GlobalTheory.Core.Mi.ConjEquiv.conjMap_equiv | (intros; apply GlobalTheory.Core.Mi.ConjEquiv.conjMap_equiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeCharValueInertPlaceAndSegment
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeCharValueInertPlaceAndSegment
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto.InertValue

theorem npow_eq_zpow {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (N : ℕ)
    (hN : Ideal.absNorm w.asIdeal = N ^ 2) (k : ℤ) (z : ℂ) (hz : 2 * z = k) :
    GlobalTheory.LFun.npow w z = (N : ℂ) ^ k := by
  have hlog : (Complex.log (N : ℂ) * ((2 : ℕ) : ℂ)).im = 0 := by
    rw [Complex.mul_im, Complex.log_im, Complex.log_re, ← Complex.ofReal_natCast N,
      Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg _)]
    simp
  rw [GlobalTheory.LFun.npow, hN, Nat.cast_pow, ← Complex.cpow_natCast (N : ℂ) 2,
    ← Complex.cpow_mul (x := (N : ℂ)) (y := ((2 : ℕ) : ℂ)) (z := z) (by rw [hlog]; linarith [Real.pi_pos]) (by rw [hlog]; linarith [Real.pi_pos])]
  rw [show ((2 : ℕ) : ℂ) * z = (k : ℂ) by rw [← hz]; norm_num, Complex.cpow_intCast]

theorem range_reflect (t : ℕ) : (Multiset.range t).map (fun i => t - 1 - i) = Multiset.range t := by
  refine (Multiset.Nodup.ext ?_ (Multiset.nodup_range t)).2 fun a => ?_
  · refine (Multiset.nodup_range t).map_on fun x hx y hy h => ?_
    rw [Multiset.mem_range] at hx hy
    omega
  · simp only [Multiset.mem_map, Multiset.mem_range]
    constructor
    · rintro ⟨b, hb, rfl⟩; omega
    · intro ha; exact ⟨t - 1 - a, by omega, by omega⟩

end GlobalTheory.ChainOnto.InertValue


open GlobalTheory.ChainOnto.InertValue in
theorem GlobalTheory.ChainOnto.val_seg_of_isInertAt : ∀ (D : D7) (χ : (AE D)ˣ →* Circle) (n : ℕ), IsHeckeChar D χ → Formalism.L2.Theta.ResEta D χ n → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) = v → IsInertAt D.host.F D.host.E v w → UnrAt χ w → val (F := D.host.F) χ w = (-1) ^ n ∧ ∀ (qu z : ℂˣ) (t : ℕ), (qu : ℂ) = qV D.host.F v → seg w z t = (GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace.str qu t).map (z * ·) := by
  intro D χ n _ hres v w hwv hw hu
  refine ⟨GlobalTheory.LFun.ResEta.val_of_isInertAt D.sp.cm.deg2 hres hw hu, ?_⟩
  intro qu z t hqu
  have hN : Ideal.absNorm w.asIdeal = qV D.host.F v ^ 2 := GlobalTheory.LFun.InertChart.absNorm_eq D.sp.cm.deg2 hw
  rw [GlobalTheory.LFun.seg, GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace.str, Int.toNat_natCast, Multiset.map_map, Finset.range_val]
  conv_lhs => rw [← range_reflect t, Multiset.map_map]
  refine Multiset.map_congr rfl fun i hi => ?_
  rw [Multiset.mem_range] at hi
  simp only [Function.comp_apply]
  congr 1
  refine Units.ext ?_
  rw [GlobalTheory.LFun.coe_npowU, Units.val_zpow_eq_zpow_val, hqu]
  refine npow_eq_zpow w _ hN _ _ ?_
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast
  ring
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeCharValueInertPlaceAndSegmentStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChar_value_inert_place_and_segment : ∀ (D : D7) (χ : (AE D)ˣ →* Circle) (n : ℕ), IsHeckeChar D χ → Formalism.L2.Theta.ResEta D χ n → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) = v → IsInertAt D.host.F D.host.E v w → UnrAt χ w → val (F := D.host.F) χ w = (-1) ^ n ∧ ∀ (qu z : ℂˣ) (t : ℕ), (qu : ℂ) = qV D.host.F v → seg w z t = (GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace.str qu t).map (z * ·) := by
  first | exact @GlobalTheory.ChainOnto.val_seg_of_isInertAt | exact GlobalTheory.ChainOnto.val_seg_of_isInertAt | (intros; apply GlobalTheory.ChainOnto.val_seg_of_isInertAt <;> assumption)
end
end
