module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSchwartzAOfIsSchwartzBruhat
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiThetaOfVac
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteAdditiveCharNeOneAtEachPrime
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsContinuousLeftInvariantRepConjugateTensor

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GramUnimodular
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn.Unimod

theorem hform_frame {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R) (J B : Matrix (Fin n) (Fin n) R) (x y : Fin n → R) :
    Formalism.UG.hform σ J (B *ᵥ x) (B *ᵥ y) = ∑ i, σ (x i) * ((Formalism.UG.cT σ B * J * B) *ᵥ y) i := by
  have h1 : ∀ (u w : Fin n → R), Formalism.UG.hform σ J u w = (fun i => σ (u i)) ⬝ᵥ (J *ᵥ w) := fun u w => by
    simp only [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have h2 : (fun i => σ ((B *ᵥ x) i)) = (B.map σ) *ᵥ (fun i => σ (x i)) := funext fun i => RingHom.map_mulVec σ B x i
  rw [h1, h2, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Formalism.UG.cT, ← Matrix.vecMul_transpose,
    ← Matrix.dotProduct_mulVec]
  rfl

theorem gram_int {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R) (O : Subring R) (hσ : ∀ z ∈ O, σ z ∈ O)
    (J B C H' : Matrix (Fin n) (Fin n) R) (L : (Fin n → R) → Prop) (hBC : B * C = 1)
    (hH : Formalism.UG.cT σ B * J * B * H' = 1)
    (hf : ∀ y, (∀ i, y i ∈ O) ↔ L (B *ᵥ y)) (hd : ∀ y, L y ↔ ∀ x, L x → Formalism.UG.hform σ J x y ∈ O) :
    (∀ i j, (Formalism.UG.cT σ B * J * B) i j ∈ O) ∧ ∀ i j, H' i j ∈ O := by
  have hs : ∀ i k : Fin n, (Pi.single i 1 : Fin n → R) k ∈ O := fun i k => by
    by_cases h : k = i
    · subst h; simp
    · simp [h]
  constructor
  · intro i j
    have h := (hd _).1 ((hf _).1 (hs j)) _ ((hf _).1 (hs i))
    rw [hform_frame, Finset.sum_eq_single i (fun k _ hk => by simp [hk]) (by simp)] at h
    simpa using h
  · intro i j
    have h : L (B *ᵥ (H' *ᵥ Pi.single j 1)) := by
      refine (hd _).2 fun x hx => ?_
      have e : x = B *ᵥ (C *ᵥ x) := by rw [Matrix.mulVec_mulVec, hBC, Matrix.one_mulVec]
      have hz : ∀ k, (C *ᵥ x) k ∈ O := (hf _).2 (e ▸ hx)
      rw [e, hform_frame]
      refine sum_mem fun k _ => mul_mem (hσ _ (hz k)) ?_
      rw [Matrix.mulVec_mulVec, hH, Matrix.one_mulVec]
      exact hs j k
    simpa using (hf _).2 h i

theorem compFin_cA {D : D7} (v : HeightOneSpectrum (𝓞 D.host.F)) (z : AE D) :
    compFin D.host.F D.host.E v (cA D z) = sigR _ D.sp.cm.sig (compFin D.host.F D.host.E v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem map_gram {D : D7} (A : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (b : Mx D A.rank A.rank) :
    (adj b * gA A * b).map (compFin D.host.F D.host.E v) =
      Formalism.UG.cT (sigR _ D.sp.cm.sig) (b.map (compFin D.host.F D.host.E v)) * JR (Fv D.host.F v) A.gram *
        b.map (compFin D.host.F D.host.E v) := by
  rw [Matrix.map_mul, Matrix.map_mul]
  congr 2
  funext i j; exact compFin_cA v _

theorem gram_unimodular : ∀ (D : D7) (A : HSp D) (b : GL (Fin A.rank) (AE D)), GlobalTheory.AdelicU.IsLatticeFrame (frameLat A) b → ∃ Hm : GL (Fin A.rank) (AE D), Hm.1 = adj b.1 * gA A * b.1 ∧ IntGL Hm := by
  intro D A b hb
  have h1 : adj b.1 * adj (b⁻¹).1 = 1 := by
    rw [← adj_mul, Units.inv_mul, adj_one]
  have h2 : adj (b⁻¹).1 * adj b.1 = 1 := by
    rw [← adj_mul, Units.mul_inv, adj_one]
  let Hm : GL (Fin A.rank) (AE D) :=
    (⟨adj b.1, adj (b⁻¹).1, h1, h2⟩ * ⟨gA A, giA A, gA_mul_giA A, giA_mul_gA A⟩ * b : (Mx D A.rank A.rank)ˣ)
  have hH : Hm.1 = adj b.1 * gA A * b.1 := rfl
  have key := fun v : HeightOneSpectrum (𝓞 D.host.F) =>
    gram_int (sigR _ D.sp.cm.sig) (intLoc D.host.F D.host.E v) (fun z hz => sigR_mem_intLoc _ hz)
      (JR (Fv D.host.F v) A.gram) (b.1.map (compFin D.host.F D.host.E v)) ((b⁻¹).1.map (compFin D.host.F D.host.E v))
      ((Hm⁻¹).1.map (compFin D.host.F D.host.E v)) (fun y => y ∈ latLoc D.host.F (frameLat A) v)
      (by rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)])
      (by rw [← map_gram, ← hH, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)])
      (hb v) (fun y => by
        have := SelfDual.isSelfDualAt_frameLat D A v
        exact (SetLike.ext_iff.1 this) y)
  refine ⟨Hm, hH, fun i j v => ?_, fun i j v => (key v).2 i j⟩
  have := (key v).1 i j
  rw [← map_gram, ← hH] at this
  exact this

end GlobalTheory.StdUnn.Unimod
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLatticeStabilizerIffScaledFrameConj
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLatticeStabilizerIffScaledFrameConj
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StdUnn.StabFin

section General

variable {A R n : Type} [CommRing A] [CommRing R] [Algebra R A] [Fintype n] [DecidableEq n]

theorem mem_stab_conj {L S : Submodule R (n → A)} {b : GL n A} (h : ∀ y, y ∈ S ↔ b.1 *ᵥ y ∈ L) (x : GL n A) :
    x ∈ Formalism.UG.stabGL L ↔ b⁻¹ * x * b ∈ Formalism.UG.stabGL S := by
  have key : ∀ y, (b⁻¹ * x * b).1 *ᵥ y ∈ S ↔ x.1 *ᵥ (b.1 *ᵥ y) ∈ L := fun y => by
    rw [h, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul, ← mul_assoc, ← mul_assoc,
      mul_inv_cancel, one_mul]
  constructor
  · intro hx y
    rw [key, h]
    exact hx _
  · intro hx y
    have h1 := hx ((b⁻¹).1 *ᵥ y)
    rw [key, h, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at h1
    exact h1


omit [CommRing R] [Algebra R A] in
theorem conj_eq_of_smul {m m' : GL n A} {w : A} (h : m.1 = w • m'.1) (z : GL n A) :
    m⁻¹ * z * m = m'⁻¹ * z * m' := by
  have hc : m * m'⁻¹ * z = z * (m * m'⁻¹) := by
    apply Units.ext
    have e : (m * m'⁻¹).1 = w • (1 : Matrix n n A) := by
      rw [Units.val_mul, h, Matrix.smul_mul, Units.mul_inv]
    rw [Units.val_mul _ z, Units.val_mul z, e, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  calc m⁻¹ * z * m = m⁻¹ * (z * (m * m'⁻¹)) * m' := by group
    _ = m⁻¹ * (m * m'⁻¹ * z) * m' := by rw [hc]
    _ = m'⁻¹ * z * m' := by group

end General

theorem mem_stab_std {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    {v : HeightOneSpectrum (𝓞 F)} {m : GL (Fin N) (Fv F v ⊗[F] E)} (h : ∀ i j, m.1 i j ∈ intLoc F E v)
    (h' : ∀ i j, (m⁻¹).1 i j ∈ intLoc F E v) : m ∈ Formalism.UG.stabGL (latLoc F (stdLattice E N) v) := by
  have key : ∀ (M : Matrix (Fin N) (Fin N) (Fv F v ⊗[F] E)), (∀ i j, M i j ∈ intLoc F E v) →
      ∀ y, y ∈ latLoc F (stdLattice E N) v → M *ᵥ y ∈ latLoc F (stdLattice E N) v := fun M hM y hy =>
    mem_latLoc_stdLattice.2 fun i => show ∑ j, M i j * y j ∈ _ from
      sum_mem fun j _ => mul_mem (hM i j) (mem_latLoc_stdLattice.1 hy j)
  intro y
  refine ⟨key _ h y, fun hy => ?_⟩
  have h1 := key _ h' _ hy
  rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at h1

theorem mem_stab_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N : ℕ) (Λ : Submodule (𝓞 E) (Fin N → E)) (b M M' : GL (Fin N) (AF F ⊗[F] E)) (u : (AF F ⊗[F] E)ˣ), GlobalTheory.AdelicU.IsLatticeFrame Λ b → (∀ v i j, compFin F E v (M'.1 i j) ∈ intLoc F E v ∧ compFin F E v ((M'⁻¹).1 i j) ∈ intLoc F E v) → M.1 = (u : AF F ⊗[F] E) • M'.1 → ∀ (v : HeightOneSpectrum (𝓞 F)) (x : GL (Fin N) (Fv F v ⊗[F] E)), x ∈ Formalism.UG.stabGL (latLoc F Λ v) ↔ (Formalism.UG.bc (compFin F E v) (b * M))⁻¹ * x * Formalism.UG.bc (compFin F E v) (b * M) ∈ Formalism.UG.stabGL (latLoc F (stdLattice E N) v) := by
  intro F E _ _ _ _ _ N Λ b M M' u hb hM' hM v x
  have hs : Formalism.UG.bc (compFin F E v) M' ∈ Formalism.UG.stabGL (latLoc F (stdLattice E N) v) := by
    refine mem_stab_std (fun i j => (hM' v i j).1) (fun i j => ?_)
    rw [← map_inv]
    exact (hM' v i j).2
  have he : (Formalism.UG.bc (compFin F E v) M).1 =
      compFin F E v (u : AF F ⊗[F] E) • (Formalism.UG.bc (compFin F E v) M').1 := by
    ext i j
    change compFin F E v (M.1 i j) = compFin F E v (u : AF F ⊗[F] E) * compFin F E v (M'.1 i j)
    rw [hM, ← map_mul]
    rfl
  rw [mem_stab_conj (S := latLoc F (stdLattice E N) v) (b := Formalism.UG.bc (compFin F E v) b)
    (fun y => mem_latLoc_stdLattice.trans (hb v y)) x, map_mul, mul_inv_rev]
  set β := Formalism.UG.bc (compFin F E v) b
  have e : (Formalism.UG.bc (compFin F E v) M)⁻¹ * β⁻¹ * x * (β * Formalism.UG.bc (compFin F E v) M) =
      (Formalism.UG.bc (compFin F E v) M)⁻¹ * (β⁻¹ * x * β) * Formalism.UG.bc (compFin F E v) M := by group
  rw [e, conj_eq_of_smul he, Subgroup.mul_mem_cancel_right _ hs, Subgroup.mul_mem_cancel_left _ (inv_mem hs)]

end GlobalTheory.StdUnn.StabFin

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLatticeStabilizerIffScaledFrameConjStatement
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_latticeStabilizer_iff_scaledFrameConj : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N : ℕ) (Λ : Submodule (𝓞 E) (Fin N → E)) (b M M' : GL (Fin N) (AF F ⊗[F] E)) (u : (AF F ⊗[F] E)ˣ), GlobalTheory.AdelicU.IsLatticeFrame Λ b → (∀ v i j, compFin F E v (M'.1 i j) ∈ intLoc F E v ∧ compFin F E v ((M'⁻¹).1 i j) ∈ intLoc F E v) → M.1 = (u : AF F ⊗[F] E) • M'.1 → ∀ (v : HeightOneSpectrum (𝓞 F)) (x : GL (Fin N) (Fv F v ⊗[F] E)), x ∈ Formalism.UG.stabGL (latLoc F Λ v) ↔ (Formalism.UG.bc (compFin F E v) (b * M))⁻¹ * x * Formalism.UG.bc (compFin F E v) (b * M) ∈ Formalism.UG.stabGL (latLoc F (stdLattice E N) v) := by
  first | exact @GlobalTheory.StdUnn.StabFin.mem_stab_iff | exact GlobalTheory.StdUnn.StabFin.mem_stab_iff | (intros; apply GlobalTheory.StdUnn.StabFin.mem_stab_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOneParamDerivOrthDecJoinedEqSum
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOneParamDerivOrthDecJoinedEqSum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BiJoinDeriv

open GlobalTheory.BiTransfer GlobalTheory.WeilVacMove GlobalTheory.FockCompare

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem dLine_apply' {S T : HSp D} {θ : GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition.InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : Chart θ σ)
    {lam : AF D.host.F →+ ℂ} (hl : Continuous lam) (hlam : ∀ a, sndA D.host.F a = 0 → ψ a = Complex.exp (lam a))
    {L : ℝ →+ WO S T} (hL : Continuous L) (hL0 : ∀ t, (L t).map (finPart D) = 0) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (w : WO S T) :
    dLine ψ S T L f w = phase lam S T (L 1) w * f w +
      fderiv ℝ (fun x => f (w + iotaW σ T S x)) 0 (piW θ T S (L 1)) := by
  have hline := (smooth_iff_sm_and_real_lines D θ σ h T S).2.1 L ⟨hL, hL0⟩
  have hfs := ((smooth_iff_sm_and_real_lines D θ σ h T S).1 f).1 hf.smooth
  have e : (fun t : ℝ => heisO ψ S T (L t) f w) = fun t : ℝ => Complex.exp (t * phase lam S T (L 1) w) *
      f (w + iotaW σ T S (t • piW θ T S (L 1))) := by
    funext t
    rw [heisO, psi_sympl_line hl hlam hL hL0, ← hline t]
  unfold dLine
  rw [e]
  exact (hasDerivAt_exp_mul _ _ f hfs _ w).deriv

theorem dLine_add_line (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {L L' : ℝ →+ WO S T} (hL : Continuous L)
    (hL0 : ∀ t, (L t).map (finPart D) = 0) (hL' : Continuous L') (hL0' : ∀ t, (L' t).map (finPart D) = 0)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    dLine ψ S T (L + L') f = dLine ψ S T L f + dLine ψ S T L' f := by
  obtain ⟨θ, hθ⟩ := hψ.2.1
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨lam, hl, hlam⟩ := exists_log hψ
  have hS : Continuous (L + L') := hL.add hL'
  have hS0 : ∀ t, ((L + L') t).map (finPart D) = 0 := fun t => by
    ext i j
    have h := congrFun (congrFun (hL0 t) i) j
    have h' := congrFun (congrFun (hL0' t) i) j
    simpa [Matrix.map_apply, (finPart D).map_add] using congrArg₂ (· + ·) h h'
  funext w
  rw [Pi.add_apply, dLine_apply' h hl hlam hS hS0 hf, dLine_apply' h hl hlam hL hL0 hf, dLine_apply' h hl hlam hL' hL0' hf,
    AddMonoidHom.add_apply, map_add, ContinuousLinearMap.map_add]
  have e : phase lam S T (L 1 + L' 1) w = phase lam S T (L 1) w + phase lam S T (L' 1) w := by
    show lam (symplOH S T w (L 1 + L' 1)) = lam (symplOH S T w (L 1)) + lam (symplOH S T w (L' 1))
    rw [symplOH_add_right, map_add (f := _)]
  rw [e]
  ring

variable {W A A' : HSp D} (d : OrthDec W A (GlobalTheory.ChiGrid.negSp A')) (S : HSp D)

theorem inl_fst_add_inr_snd (x : WO W S) : inlH d S (fstH d S x) + inrH d S (sndH d S x) = x := by
  rw [inlH_apply, inrH_apply, fstH_apply, sndH_apply, ← map_add (f := _), Prod.mk_add_mk, add_zero, zero_add]
  have : GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S A' (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger A' S (d.resS S x).2) = (d.resS S x).2 :=
    GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger_dagger A' S _
  rw [this, Prod.mk.eta, AddEquiv.symm_apply_apply]

theorem dLine_inlH (G : WO A S → WO S A' → ℂ) (M : ℝ →+ WO A S) :
    dLine ψ W S ((inlH d S).comp M) (join d S G) = join d S (fun u v => dLine ψ A S M (fun u' => G u' v) u) := by
  funext x
  simp only [dLine, join_apply]
  congr 1
  funext t
  simp only [AddMonoidHom.comp_apply, heisO, symplOH_split d, map_add (fstH d S), map_add (sndH d S), fst_inl, snd_inl,
    GlobalTheory.WeilVacMove.symplOH_zero_right, add_zero, join_apply]

theorem dLine_inrH (G : WO A S → WO S A' → ℂ) (M : ℝ →+ WO S A') :
    dLine ψ W S ((inrH d S).comp M) (join d S G) = join d S (fun u v => dLine ψ S A' M (G u) v) := by
  funext x
  simp only [dLine, join_apply]
  congr 1
  funext t
  simp only [AddMonoidHom.comp_apply, heisO, symplOH_split d, map_add (fstH d S), map_add (sndH d S), fst_inr, snd_inr,
    GlobalTheory.WeilVacMove.symplOH_zero_right, zero_add, add_zero, join_apply]

end GlobalTheory.BiJoinDeriv

namespace GlobalTheory.BiJoinDeriv

open GlobalTheory.BiTransfer GlobalTheory.WeilVacMove

theorem dLine_join : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (W A S A' : HSp D) (d : OrthDec W A (GlobalTheory.ChiGrid.negSp A')) (G : WO A S → WO S A' → ℂ), IsBiTheta ψ A S A' G → ∀ M : ℝ →+ WO W S, Continuous M → (∀ s, (M s).map (finPart D) = 0) → (∀ s, (GlobalTheory.BiTransfer.fstH d S (M s)).map (finPart D) = 0) ∧ (∀ s, (GlobalTheory.BiTransfer.sndH d S (M s)).map (finPart D) = 0) ∧ GlobalTheory.WeilVacMove.dLine ψ W S M (GlobalTheory.BiTransfer.join d S G) = GlobalTheory.BiTransfer.join d S fun u v => GlobalTheory.WeilVacMove.dLine ψ A S ((GlobalTheory.BiTransfer.fstH d S).comp M) (fun u' => G u' v) u + GlobalTheory.WeilVacMove.dLine ψ S A' ((GlobalTheory.BiTransfer.sndH d S).comp M) (G u) v := by
  intro D ψ hψ W A S A' d G hG M hM hM0
  have h1 : ∀ s, (fstH d S (M s)).map (finPart D) = 0 := fun s => map_mul_eq_zero_left _ (hM0 s) _
  have h2 : ∀ s, (sndH d S (M s)).map (finPart D) = 0 := fun s => fin_dagger A' S (map_mul_eq_zero_left _ (hM0 s) _)
  refine ⟨h1, h2, ?_⟩
  have hj := isThetaFunO_join d hG
  have eM : M = (inlH d S).comp ((fstH d S).comp M) + (inrH d S).comp ((sndH d S).comp M) := by
    ext1 t
    exact (inl_fst_add_inr_snd d S (M t)).symm
  rw [eM, dLine_add_line hψ ((continuous_inlH d S).comp ((continuous_fstH d S).comp hM)) (fun t => map_inlH d S _ (h1 t))
    ((continuous_inrH d S).comp ((continuous_sndH d S).comp hM)) (fun t => fin_inrH d S (h2 t)) hj,
    dLine_inlH, dLine_inrH, ← eM]
  funext x
  simp only [Pi.add_apply, join_apply]

end GlobalTheory.BiJoinDeriv

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOneParamDerivOrthDecJoinedEqSumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergOneParamDeriv_orthDecJoined_eq_sum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (W A S A' : HSp D) (d : OrthDec W A (GlobalTheory.ChiGrid.negSp A')) (G : WO A S → WO S A' → ℂ), IsBiTheta ψ A S A' G → ∀ M : ℝ →+ WO W S, Continuous M → (∀ s, (M s).map (finPart D) = 0) → (∀ s, (GlobalTheory.BiTransfer.fstH d S (M s)).map (finPart D) = 0) ∧ (∀ s, (GlobalTheory.BiTransfer.sndH d S (M s)).map (finPart D) = 0) ∧ GlobalTheory.WeilVacMove.dLine ψ W S M (GlobalTheory.BiTransfer.join d S G) = GlobalTheory.BiTransfer.join d S fun u v => GlobalTheory.WeilVacMove.dLine ψ A S ((GlobalTheory.BiTransfer.fstH d S).comp M) (fun u' => G u' v) u + GlobalTheory.WeilVacMove.dLine ψ S A' ((GlobalTheory.BiTransfer.sndH d S).comp M) (G u) v := by
  first | exact @GlobalTheory.BiJoinDeriv.dLine_join | exact GlobalTheory.BiJoinDeriv.dLine_join | (intros; apply GlobalTheory.BiJoinDeriv.dLine_join <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergDerivWeilTranslateContinuousCombinatio
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergDerivWeilTranslateContinuousCombinatio
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HeisLineComb

open GlobalTheory.WeilVacMove GlobalTheory.FockCompare

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem actO_actO_inv (g : GA D S) (h : GA D T) (x : WO S T) : actO S T g h (actO S T g⁻¹ h⁻¹ x) = x := by
  unfold actO
  rw [inv_inv]
  calc HMul.hMul (HMul.hMul (mt T h) (HMul.hMul (HMul.hMul (mt T h⁻¹) x) (mt S g))) (mt S g⁻¹)
      = HMul.hMul (HMul.hMul (HMul.hMul (mt T h) (mt T h⁻¹)) x) (HMul.hMul (mt S g) (mt S g⁻¹)) := by
        simp only [Matrix.mul_assoc]
    _ = x := by rw [← GlobalTheory.WeilVacMove.mt_mul, ← GlobalTheory.WeilVacMove.mt_mul, mul_inv_cancel, mul_inv_cancel, GlobalTheory.WeilVacMove.mt_one, GlobalTheory.WeilVacMove.mt_one, Matrix.one_mul, Matrix.mul_one]

theorem dLine_apply {θ : GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition.InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : Chart θ σ)
    {lam : AF D.host.F →+ ℂ} (hl : Continuous lam) (hlam : ∀ a, sndA D.host.F a = 0 → ψ a = Complex.exp (lam a))
    {L : ℝ →+ WO S T} (hL : Continuous L) (hL0 : ∀ t, (L t).map (finPart D) = 0) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (w : WO S T) :
    dLine ψ S T L f w = phase lam S T (L 1) w * f w +
      fderiv ℝ (fun x => f (w + iotaW σ T S x)) 0 (piW θ T S (L 1)) := by
  have hline := (smooth_iff_sm_and_real_lines D θ σ h T S).2.1 L ⟨hL, hL0⟩
  have hfs := ((smooth_iff_sm_and_real_lines D θ σ h T S).1 f).1 hf.smooth
  have e : (fun t : ℝ => heisO ψ S T (L t) f w) = fun t : ℝ => Complex.exp (t * phase lam S T (L 1) w) *
      f (w + iotaW σ T S (t • piW θ T S (L 1))) := by
    funext t
    rw [heisO, psi_sympl_line hl hlam hL hL0, ← hline t]
  unfold dLine
  rw [e]
  exact (hasDerivAt_exp_mul _ _ f hfs _ w).deriv

theorem dLine_eq_sum (hψ : IsStdChar D ψ (-1)) {θ : GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition.InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D}
    (h : Chart θ σ) {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ (RW T S)) {L : ℝ →+ WO S T} (hL : Continuous L)
    (hL0 : ∀ t, (L t).map (finPart D) = 0) (N : ι → ℝ →+ WO S T) (hN : ∀ i, Continuous (N i))
    (hN0 : ∀ i t, (N i t).map (finPart D) = 0) (hN1 : ∀ i, piW θ T S (N i 1) = b i) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) :
    dLine ψ S T L f = ∑ i, ((b.coord i (piW θ T S (L 1)) : ℝ) : ℂ) • dLine ψ S T (N i) f := by
  obtain ⟨lam, hl, hlam⟩ := exists_log hψ
  funext w
  let A : RW T S →+ ℂ := AddMonoidHom.mk' (fun v => lam (symplOH S T w (iotaW σ T S v))) fun u v => by
    rw [map_add (f := _), symplOH_add_right, map_add (f := _)]
  have hA : Continuous A := hl.comp (continuous_symplOH S T continuous_const (h.continuous_iota T S))
  let A' : RW T S →L[ℝ] ℂ := A.toRealLinearMap hA
  let B : RW T S →L[ℝ] ℂ := fderiv ℝ (fun x => f (w + iotaW σ T S x)) 0
  let Φ : RW T S →ₗ[ℝ] ℂ := (LinearMap.mulRight ℝ (f w)).comp A'.toLinearMap + B.toLinearMap
  have key : ∀ (K : ℝ →+ WO S T), Continuous K → (∀ t, (K t).map (finPart D) = 0) →
      dLine ψ S T K f w = Φ (piW θ T S (K 1)) := by
    intro K hK hK0
    rw [dLine_apply h hl hlam hK hK0 hf]
    have e1 : K 1 = iotaW σ T S (piW θ T S (K 1)) := by
      have := (smooth_iff_sm_and_real_lines D θ σ h T S).2.1 K ⟨hK, hK0⟩ 1
      rwa [one_smul] at this
    have e2 : lam (symplOH S T w (K 1)) = A (piW θ T S (K 1)) := by
      show _ = lam (symplOH S T w (iotaW σ T S (piW θ T S (K 1))))
      rw [← e1]
    show lam (symplOH S T w (K 1)) * f w + _ = _
    rw [e2]
    rfl
  rw [Finset.sum_apply, key L hL hL0]
  simp only [Pi.smul_apply, smul_eq_mul]
  simp only [fun i => key (N i) (hN i) (hN0 i), hN1]
  conv_lhs => rw [← b.sum_repr (piW θ T S (L 1))]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Complex.real_smul, Module.Basis.coord_apply]

theorem dLine_om_comb : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ M : ℝ →+ WO S T, Continuous M → (∀ s, (M s).map (finPart D) = 0) → ∃ (m : ℕ) (N : Fin m → ℝ →+ WO S T) (c : Fin m → GA D S × GA D T → ℂ), (∀ i, Continuous (N i)) ∧ (∀ i s, (N i s).map (finPart D) = 0) ∧ (∀ i, Continuous (c i)) ∧ ∀ p f, IsThetaFunO ψ S T f → GlobalTheory.WeilVacMove.dLine ψ S T M (om p f) = ∑ i, c i p • om p (GlobalTheory.WeilVacMove.dLine ψ S T (N i) f) := by
  intro D ψ S T χS χT om hW M hM hM0
  have hψ := hW.std
  obtain ⟨θ, hθ⟩ := hψ.2.1
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  let b := Module.finBasis ℝ (RW T S)
  let N : Fin (Module.finrank ℝ (RW T S)) → ℝ →+ WO S T := fun i =>
    (iotaW σ T S).comp (ContinuousLinearMap.toSpanSingleton ℝ (b i)).toLinearMap.toAddMonoidHom
  have hN : ∀ i, Continuous (N i) := fun i =>
    (h.continuous_iota T S).comp (ContinuousLinearMap.toSpanSingleton ℝ (b i)).continuous
  have hN0 : ∀ i t, (N i t).map (finPart D) = 0 := fun i t => h.real_iota T S _
  have hN1 : ∀ i, piW θ T S (N i 1) = b i := fun i => by
    show piW θ T S (iotaW σ T S ((1 : ℝ) • b i)) = b i
    rw [h.pi_iota, one_smul]
  let Mp : GA D S × GA D T → ℝ →+ WO S T := fun p =>
    AddMonoidHom.mk' (fun s => actO S T p.1⁻¹ p.2⁻¹ (M s)) fun s t => by rw [map_add (f := _), actO_add]
  have hMp : ∀ p, Continuous (Mp p) := fun p =>
    (continuous_const.matrix_mul hM).matrix_mul continuous_const
  have hMp0 : ∀ p t, (Mp p t).map (finPart D) = 0 := fun p t => by
    show (actO S T p.1⁻¹ p.2⁻¹ (M t)).map (finPart D) = 0
    unfold actO
    rw [Matrix.map_mul, Matrix.map_mul, hM0 t, Matrix.mul_zero, Matrix.zero_mul]
  refine ⟨_, N, fun i p => ((b.coord i (piW θ T S (Mp p 1)) : ℝ) : ℂ), hN, hN0, fun i => ?_, fun p f hf => ?_⟩
  · have hc : Continuous fun p : GA D S × GA D T => actO S T p.1⁻¹ p.2⁻¹ (M 1) := by
      unfold actO
      exact (((GlobalTheory.MixModel.continuous_mt T).comp (continuous_snd.inv)).matrix_mul continuous_const).matrix_mul
        ((GlobalTheory.MixModel.continuous_mt S).comp continuous_fst.inv.inv)
    exact Complex.continuous_ofReal.comp ((LinearMap.continuous_of_finiteDimensional (b.coord i)).comp
      ((continuous_pi' hθ T S).comp hc))
  · obtain ⟨g, k⟩ := p
    have e := om_dLine hW g k (hMp (g, k)) (hMp0 (g, k)) hM hM0 (fun t => (actO_actO_inv g k (M t)).symm) hf
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← e, dLine_eq_sum hψ h b (hMp (g, k)) (hMp0 (g, k)) N hN hN0 hN1 hf, map_sum]
    simp only [map_smul]

end GlobalTheory.HeisLineComb

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergDerivWeilTranslateContinuousCombinatioStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergDeriv_weilTranslate_continuous_combination : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ M : ℝ →+ WO S T, Continuous M → (∀ s, (M s).map (finPart D) = 0) → ∃ (m : ℕ) (N : Fin m → ℝ →+ WO S T) (c : Fin m → GA D S × GA D T → ℂ), (∀ i, Continuous (N i)) ∧ (∀ i s, (N i s).map (finPart D) = 0) ∧ (∀ i, Continuous (c i)) ∧ ∀ p f, IsThetaFunO ψ S T f → GlobalTheory.WeilVacMove.dLine ψ S T M (om p f) = ∑ i, c i p • om p (GlobalTheory.WeilVacMove.dLine ψ S T (N i) f) := by
  first | exact @GlobalTheory.HeisLineComb.dLine_om_comb | exact GlobalTheory.HeisLineComb.dLine_om_comb | (intros; apply GlobalTheory.HeisLineComb.dLine_om_comb <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousComplEquivSymm
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW GlobalTheory.Core.Rk.SWQ
open Formalism.UG (IsUnifV qV Ov ordL diagJ)
open GlobalTheory.LFun (KGL toCompl IsSplitChart IsSatVecGL satEig)
open scoped Classical

namespace GlobalTheory.Core.Rk.SplitIota

open GlobalTheory.AdelicU.Supp GlobalTheory.LFun.ConjPlace
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField E] in
theorem sigR_compFin' (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (z : AF F ⊗[F] E) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ (compFin F E v z) = compFin F E v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem continuous_complEquiv_symm {σ : E →ₐ[F] E} {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)}
    (hE : IsCMExt F E σ) (h : w.under (𝓞 F) = v) {τ : E →ₐ[F] Fv F v} (hτ : splitPrime τ = w) :
    Continuous (complEquiv hE h hτ).symm := by
  let _ : Algebra (Fv F v) (w.adicCompletion E) := (GlobalTheory.LFun.complMap h).toAlgebra
  have : ContinuousSMul (Fv F v) (w.adicCompletion E) :=
    continuousSMul_of_algebraMap _ _ (GlobalTheory.LFun.SplitChart.continuous_complMap h)
  let _ : NontriviallyNormedField (Fv F v) := Valued.toNontriviallyNormedField _ _
  let f : Fv F v ≃ₐ[Fv F v] w.adicCompletion E :=
    { complEquiv hE h hτ with commutes' := fun a => rfl }
  have : FiniteDimensional (Fv F v) (w.adicCompletion E) := f.toLinearEquiv.finiteDimensional
  have : IsModuleTopology (Fv F v) (w.adicCompletion E) := isModuleTopologyOfFiniteDimensional
  exact IsModuleTopology.continuous_of_linearMap f.symm.toLinearMap

theorem continuous_compW {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} (h : w.under (𝓞 F) = v) :
    Continuous fun a : AF F ⊗[F] E => GlobalTheory.LFun.toCompl h (compFin F E v a) := by
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  refine IsModuleTopology.continuous_of_ringHom (R := AF F) ((GlobalTheory.LFun.toCompl h).comp (compFin F E v)) ?_
  have e : (((GlobalTheory.LFun.toCompl h).comp (compFin F E v)).comp (algebraMap (AF F) (AF F ⊗[F] E)) :
      AF F → w.adicCompletion E) = fun a => GlobalTheory.LFun.complMap h (evFin F v a) := by
    funext a
    exact (GlobalTheory.LFun.toCompl_tmul h (evFin F v a) (1 : E)).trans (by rw [map_one, mul_one])
  rw [e]
  exact (GlobalTheory.LFun.SplitChart.continuous_complMap h).comp ((RestrictedProduct.continuous_eval v).comp continuous_snd)

theorem exists_iota_gen {σ : E →ₐ[F] E} {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)}
    (hE : IsCMExt F E σ) (h : w.under (𝓞 F) = v) {τ : E →ₐ[F] Fv F v} (hτ : splitPrime τ = w) :
    ∃ ι : w.adicCompletion E →+ AF F ⊗[F] E, Continuous ι ∧
      (∀ x, GlobalTheory.LFun.toCompl h (compFin F E v (ι x)) = x) ∧
      (∀ x, GlobalTheory.LFun.toCompl h (compFin F E v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ (ι x))) = 0) ∧
      (∀ x, algebraMap (AF F) (AF F ⊗[F] E) (pairA F 0 (singleFin v 1)) * ι x = ι x) ∧
      (∀ a x, a * ι x = ι (GlobalTheory.LFun.toCompl h (compFin F E v a) * x)) ∧
      (∀ a, algebraMap (AF F) (AF F ⊗[F] E) (pairA F 0 (singleFin v 1)) * a =
        ι (GlobalTheory.LFun.toCompl h (compFin F E v a)) +
          Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ (ι (GlobalTheory.LFun.toCompl h (compFin F E v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ a))))) ∧
      ι 1 = singleTens E v (splitIdem hE τ) := by
  set c := complEquiv hE h hτ
  have hcw : ∀ y, GlobalTheory.LFun.toCompl h y = c (splitProj τ y) := fun y => toCompl_eq hE h hτ y
  have hcc : Continuous c.symm := continuous_complEquiv_symm hE h hτ
  let s : w.adicCompletion E →+ Fv F v ⊗[F] E :=
    (splitAlgEquiv hE τ).symm.toRingEquiv.toAddEquiv.toAddMonoidHom.comp
      ((AddMonoidHom.inl _ _).comp c.symm.toAddEquiv.toAddMonoidHom)
  have s1 : ∀ x, splitProj τ (s x) = c.symm x := fun x => splitProj_symm hE τ _
  have s2 : ∀ x, splitProj (τ.comp σ) (s x) = 0 := fun x => splitProj_comp_symm hE τ _
  have hs1 : s 1 = splitIdem hE τ := by
    show (splitAlgEquiv hE τ).symm (c.symm 1, 0) = _
    rw [map_one]; rfl
  have hsc : Continuous s :=
    (continuous_splitAlgEquiv_symm hE τ).comp ((continuous_id.prodMk continuous_const).comp hcc)
  clear_value s
  have hst : Continuous (singleTens E v) :=
    GlobalTheory.AutFunCompare.continuous_tensNU (E := E) _ _ (Continuous.prodMk continuous_const (continuous_singleFin v))
  have hpl : algebraMap (AF F) (AF F ⊗[F] E) (pairA F 0 (singleFin v 1)) = singleTens E v 1 := rfl
  refine ⟨(singleTens E v).toAddMonoidHom.comp s, hst.comp hsc, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    show GlobalTheory.LFun.toCompl h (compFin F E v (singleTens E v (s x))) = x
    rw [compFin_singleTens_self, hcw, s1, RingEquiv.apply_symm_apply]
  · intro x
    show GlobalTheory.LFun.toCompl h (compFin F E v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ (singleTens E v (s x)))) = 0
    rw [sigR_singleTens, compFin_singleTens_self, hcw, ← splitProj_comp, s2, map_zero]
  · intro x
    show _ * singleTens E v (s x) = singleTens E v (s x)
    rw [hpl, singleTens_mul, compFin_singleTens_self, one_mul]
  · intro a x
    show a * singleTens E v (s x) = singleTens E v (s _)
    rw [mul_comm, singleTens_mul]
    refine congrArg _ (split_ext hE τ ?_ ?_)
    · rw [map_mul, s1, s1, hcw, map_mul, RingEquiv.symm_apply_apply, mul_comm]
    · rw [map_mul, s2, s2, zero_mul]
  · intro a
    show _ = singleTens E v (s _) + Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ (singleTens E v (s _))
    rw [hpl, singleTens_mul, one_mul, sigR_singleTens, ← map_add (f := _)]
    refine congrArg _ (split_ext hE τ ?_ ?_)
    · rw [map_add (f := _), s1, hcw, RingEquiv.symm_apply_apply, ← splitProj_comp, s2, add_zero]
    · rw [map_add (f := _), s2, zero_add, splitProj_comp_sigR hE, s1, hcw, RingEquiv.symm_apply_apply,
        ← sigR_compFin', splitProj_comp]
  · show singleTens E v (s 1) = _
    rw [hs1]

end GlobalTheory.Core.Rk.SplitIota

open scoped TensorProduct


open GlobalTheory.Core.Rk.SplitIota in
theorem GlobalTheory.Core.Rk.SplitIota.exists_iota : ∀ (D : D7) (q : FinPl D) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = q), Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) q → ∃ ι : w.adicCompletion D.host.E →+ AE D, Continuous ι ∧ (∀ x, cw h (ι x) = x) ∧ (∀ x, cw h (cA D (ι x)) = 0) ∧ (∀ x, algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleFin q 1)) * ι x = ι x) ∧ (∀ a x, a * ι x = ι (cw h a * x)) ∧ (∀ a, algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleFin q 1)) * a = ι (cw h a) + cA D (ι (cw h (cA D a)))) ∧ IsSplitIdem D (ι 1) ∧ Continuous (cw h) := by
  intro D q w h hs
  have hE := isCMExt_host D
  obtain ⟨P, Q, hPQ, hP, hQ⟩ := hs
  have hPu : P.under (𝓞 D.host.F) = q := HeightOneSpectrum.ext hP
  have hQu : Q.under (𝓞 D.host.F) = q := HeightOneSpectrum.ext hQ
  obtain ⟨w', hw', hw'u⟩ : ∃ w' : HeightOneSpectrum (𝓞 D.host.E), w ≠ w' ∧ w'.under (𝓞 D.host.F) = q := by
    by_cases e : w = P
    · exact ⟨Q, e ▸ hPQ, hQu⟩
    · exact ⟨P, e, hPu⟩
  obtain ⟨τ, hτ, -⟩ := GlobalTheory.AdelicU.existsUnique_splitPrime_eq hE hw' h hw'u
  obtain ⟨ι, h1, h2, h3, h4, h5, h6, h7⟩ := exists_iota_gen hE h hτ
  exact ⟨ι, h1, h2, h3, h4, h5, h6, GlobalTheory.AdelicU.Supp.isSplitIdem_iff_exists.2 ⟨q, τ, h7⟩, continuous_compW h⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.QuotientIntegralFinitelyManyCellsWeightedSum
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.QuotientIntegralFinitelyManyCellsWeightedSum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CellInt

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

def dcos (R K : Subgroup G) (q : G) : Set G := {g | ∃ r ∈ R, ∃ k ∈ K, g = r * q * k}

theorem dcos_eq_of_mem {R K : Subgroup G} {q h : G} (hh : h ∈ dcos R K q) : dcos R K h = dcos R K q := by
  obtain ⟨r, hr, k, hk, rfl⟩ := hh
  ext g
  constructor
  · rintro ⟨r', hr', k', hk', rfl⟩
    exact ⟨r' * r, R.mul_mem hr' hr, k * k', K.mul_mem hk hk', by group⟩
  · rintro ⟨r', hr', k', hk', rfl⟩
    exact ⟨r' * r⁻¹, R.mul_mem hr' (R.inv_mem hr), k⁻¹ * k', K.mul_mem (K.inv_mem hk) hk', by group⟩

def cellSet (R K : Subgroup G) (q h : G) : Set R := {r | q⁻¹ * ((r : G) * h) ∈ K}

theorem isOpen_cellSet {R K : Subgroup G} (hK : IsOpen (K : Set G)) (q h : G) : IsOpen (cellSet R K q h) :=
  (continuous_const.mul (continuous_subtype_val.mul continuous_const)).isOpen_preimage _ hK

theorem isCompact_cellSet {R K : Subgroup G} (hR : IsClosed (R : Set G)) (hK : IsCompact (K : Set G)) (q h : G) :
    IsCompact (cellSet R K q h) := by
  have h1 : IsCompact ((fun x : G => q⁻¹ * (x * h)) ⁻¹' (K : Set G)) :=
    ((Homeomorph.mulRight h).trans (Homeomorph.mulLeft q⁻¹)).isCompact_preimage.2 hK
  exact hR.isClosedEmbedding_subtypeVal.isCompact_preimage h1

theorem cellSet_of_mem {R K : Subgroup G} {q h : G} (r0 : R) (k0 : G) (hk0 : k0 ∈ K) (hh : h = r0 * q * k0) :
    cellSet R K q h = (fun r => r * r0) ⁻¹' cellSet R K q q := by
  ext r
  simp only [cellSet, Set.mem_preimage, Set.mem_setOf_eq, Subgroup.coe_mul, hh]
  constructor
  · intro hr
    have := K.mul_mem hr (K.inv_mem hk0)
    convert this using 1; group
  · intro hr
    have := K.mul_mem hr hk0
    convert this using 1; group

theorem cellSet_eq_empty {R K : Subgroup G} {q h : G} (hh : h ∉ dcos R K q) : cellSet R K q h = ∅ :=
  Set.eq_empty_of_forall_notMem fun r hr =>
    hh ⟨(r : G)⁻¹, R.inv_mem r.2, q⁻¹ * ((r : G) * h), hr, by group⟩


open Classical in
theorem isQuotientIntegral_indicator_doubleCoset (R K : Subgroup G) (hR : IsClosed (R : Set G)) (hKc : IsCompact (K : Set G))
    (hKo : IsOpen (K : Set G)) (ρ : Measure R) (μ : Measure G) [ρ.IsHaarMeasure] [ρ.IsInvInvariant]
    [μ.IsHaarMeasure] (q : G) :
    IsQuotIntL1 ρ μ (fun g => if g ∈ dcos R K q then 1 else 0)
      (((μ (K : Set G)).toReal / (ρ (cellSet R K q q)).toReal : ℝ) : ℂ) := by
  classical
  have hRI : ρ.IsMulRightInvariant := by rw [← Measure.inv_eq_self ρ]; infer_instance
  set c : ℂ := ((((ρ (cellSet R K q q)).toReal)⁻¹ : ℝ) : ℂ) with hc
  set A : Set G := (fun x => q⁻¹ * x) ⁻¹' (K : Set G) with hA
  have hAo : IsOpen A := (continuous_const.mul continuous_id).isOpen_preimage _ hKo
  have hAc : IsCompact A := (Homeomorph.mulLeft q⁻¹).isCompact_preimage.2 hKc
  have hAμ : μ A = μ K := measure_preimage_mul μ q⁻¹ _
  have hS0 : ρ (cellSet R K q q) ≠ 0 := (isOpen_cellSet hKo q q).measure_ne_zero ρ ⟨1, by simp [cellSet]⟩
  have hSt : ρ (cellSet R K q q) ≠ ⊤ := ((isCompact_cellSet hR hKc q q).measure_lt_top (μ := ρ)).ne
  have e : ∀ h, (fun r : R => A.indicator (fun _ => c) ((r : G) * h)) = (cellSet R K q h).indicator fun _ => c := by
    intro h; funext r; simp only [Set.indicator_apply, hA, cellSet, Set.mem_preimage, Set.mem_setOf_eq, SetLike.mem_coe]
  refine ⟨A.indicator fun _ => c, ?_, fun h => ?_, fun h => ?_, ?_⟩
  · exact (integrableOn_const hAc.measure_lt_top.ne).integrable_indicator hAo.measurableSet
  · rw [e h]
    exact (integrableOn_const ((isCompact_cellSet hR hKc q h).measure_lt_top (μ := ρ)).ne).integrable_indicator
      (isOpen_cellSet hKo q h).measurableSet
  · rw [e h, integral_indicator (isOpen_cellSet hKo q h).measurableSet, setIntegral_const]
    show (if h ∈ dcos R K q then (1 : ℂ) else 0) = ρ.real (cellSet R K q h) • c
    by_cases hh : h ∈ dcos R K q
    · rw [if_pos hh]
      obtain ⟨r0, hr0, k0, hk0, rfl⟩ := hh
      rw [cellSet_of_mem ⟨r0, hr0⟩ k0 hk0 rfl, measureReal_def, measure_preimage_mul_right, hc, Complex.real_smul,
        ← Complex.ofReal_mul, mul_inv_cancel₀ (ENNReal.toReal_ne_zero.2 ⟨hS0, hSt⟩), Complex.ofReal_one]
    · rw [if_neg hh, cellSet_eq_empty hh]
      simp
  · rw [integral_indicator hAo.measurableSet, setIntegral_const, measureReal_def, hAμ, hc, Complex.real_smul, ← Complex.ofReal_mul, div_eq_mul_inv]

theorem quotient_integral_finset_sum {R : Subgroup G} {ρ : Measure R} {μ : Measure G} {ι : Type} (s : Finset ι)
    (g : ι → G → ℂ) (z : ι → ℂ) (hs : ∀ i ∈ s, IsQuotIntL1 ρ μ (g i) (z i)) :
    IsQuotIntL1 ρ μ (fun h => ∑ i ∈ s, g i h) (∑ i ∈ s, z i) := by
  classical
  revert hs
  refine Finset.induction_on s ?_ ?_
  · intro _
    have e : (fun h => ∑ i ∈ (∅ : Finset ι), g i h) = 0 := by funext h; simp
    rw [e, Finset.sum_empty]
    exact IsQuotIntL1.zero
  · intro a s ha ih hs
    have := (hs a (Finset.mem_insert_self a s)).add (ih fun i hi => hs i (Finset.mem_insert_of_mem hi))
    rw [Finset.sum_insert ha]
    convert this using 1
    funext h
    simp [Finset.sum_insert ha]

end GlobalTheory.CellInt


open GlobalTheory.CellInt in
theorem GlobalTheory.CellInt.quotInt_finiteCells : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (R K : Subgroup G), IsClosed (R : Set G) → IsCompact (K : Set G) → IsOpen (K : Set G) → ∀ (ρ : Measure R) (μ : Measure G), ρ.IsHaarMeasure → ρ.IsInvInvariant → μ.IsHaarMeasure → μ.IsMulRightInvariant → ∀ T : Finset G, ∃ (T' : Finset G) (w : G → ℂ), T' ⊆ T ∧ ∀ f : G → ℂ, (∀ r ∈ R, ∀ g, f (r * g) = f g) → (∀ k ∈ K, ∀ g, f (g * k) = f g) → (∀ g, f g ≠ 0 → ∃ q ∈ T, ∃ r ∈ R, ∃ k ∈ K, g = r * q * k) → IsQuotIntL1 ρ μ f (∑ q ∈ T', w q * f q) := by
  intro G _ _ _ _ _ _ _ _ R K hR hKc hKo ρ μ hρ hρi hμ hμr T
  classical
  obtain ⟨u, hus, hinj, himg⟩ := Finset.exists_subset_injOn_image_eq_of_surjOn (f := dcos R K) (T : Set G)
    (T.image (dcos R K)) (by rw [Finset.coe_image]; exact Set.surjOn_image _ _)
  refine ⟨u, fun q => (((μ (K : Set G)).toReal / (ρ (cellSet R K q q)).toReal : ℝ) : ℂ), Finset.coe_subset.1 hus,
    fun f hfR hfK hsupp => ?_⟩
  have hinv : ∀ q h, h ∈ dcos R K q → f h = f q := by
    rintro q h ⟨r, hr, k, hk, rfl⟩
    rw [mul_assoc, hfR r hr, hfK k hk]
  have key : ∀ h, f h = ∑ q ∈ u, f q * (if h ∈ dcos R K q then 1 else 0) := by
    intro h
    by_cases hex : ∃ q0 ∈ u, h ∈ dcos R K q0
    · obtain ⟨q0, hq0, hh⟩ := hex
      rw [Finset.sum_eq_single q0 (fun q hq hne => ?_) (fun h' => absurd hq0 h'), if_pos hh, mul_one, hinv q0 h hh]
      rw [if_neg, mul_zero]
      intro hq'
      exact hne (hinj hq hq0 ((dcos_eq_of_mem hq').symm.trans (dcos_eq_of_mem hh)))
    · rw [Finset.sum_eq_zero fun q hq => by rw [if_neg fun hh => hex ⟨q, hq, hh⟩, mul_zero]]
      by_contra hne
      obtain ⟨q, hq, r, hr, k, hk, hh⟩ := hsupp h hne
      have hm : dcos R K q ∈ u.image (dcos R K) := himg ▸ Finset.mem_image_of_mem _ hq
      obtain ⟨q', hq', he⟩ := Finset.mem_image.1 hm
      exact hex ⟨q', hq', by rw [he]; exact ⟨r, hr, k, hk, hh⟩⟩
  have hS := quotient_integral_finset_sum u (fun q h => f q * if h ∈ dcos R K q then 1 else 0)
    (fun q => (((μ (K : Set G)).toReal / (ρ (cellSet R K q q)).toReal : ℝ) : ℂ) * f q) fun q _ => by
      have := (isQuotientIntegral_indicator_doubleCoset R K hR hKc hKo ρ μ q).smul (f q)
      convert this using 1
      · ring
  convert hS using 1
  exact funext key
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.QuotientIntegralFinitelyManyCellsWeightedSumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotientIntegral_finitelyManyCells_weightedSum : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (R K : Subgroup G), IsClosed (R : Set G) → IsCompact (K : Set G) → IsOpen (K : Set G) → ∀ (ρ : Measure R) (μ : Measure G), ρ.IsHaarMeasure → ρ.IsInvInvariant → μ.IsHaarMeasure → μ.IsMulRightInvariant → ∀ T : Finset G, ∃ (T' : Finset G) (w : G → ℂ), T' ⊆ T ∧ ∀ f : G → ℂ, (∀ r ∈ R, ∀ g, f (r * g) = f g) → (∀ k ∈ K, ∀ g, f (g * k) = f g) → (∀ g, f g ≠ 0 → ∃ q ∈ T, ∃ r ∈ R, ∃ k ∈ K, g = r * q * k) → IsQuotIntL1 ρ μ f (∑ q ∈ T', w q * f q) := by
  first | exact @GlobalTheory.CellInt.quotInt_finiteCells | exact GlobalTheory.CellInt.quotInt_finiteCells | (intros; apply GlobalTheory.CellInt.quotInt_finiteCells <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedChainStageSoftProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedChainStageSoftProperties
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.ChainTw
variable {D : D7}

theorem t_fd {c : Com D} {w : Twist D} {j : ℕ} {s : PiLocalization₂ D} {hr : D.R.r ≤ s.V.rank}
    (hle : s.CC c ≤ (flat c w j s hr).CC c) (hFD : FiniteDimensional ℂ ((flat c w j s hr).CC c)) :
    FiniteDimensional ℂ (s.CC c) := by
  let ι : s.CC c →ₗ[ℂ] (flat c w j s hr).CC c := Submodule.inclusion hle
  exact @FiniteDimensional.of_injective ℂ _ _ _ _ _ _ _ ι (Submodule.inclusion_injective hle) hFD

theorem t_met {c : Com D} {w : Twist D} {j : ℕ} {s : PiLocalization₂ D} {hr : D.R.r ≤ s.V.rank}
    (hle : s.CC c ≤ (flat c w j s hr).CC c) (h : ∃ ipD ip, IsMet c (flat c w j s hr) ipD ip) :
    ∃ ipD ip, IsMet c s ipD ip := by
  obtain ⟨ipD, ipF, hm⟩ := h
  let ι : s.CC c →ₗ[ℂ] (flat c w j s hr).CC c := Submodule.inclusion hle
  let ip : s.CC c →ₗ[ℂ] s.CC c →ₗ⋆[ℂ] ℂ := (ipF.comp ι).compl₂ ι
  have hι : ∀ x : s.CC c, ι x ≠ 0 ↔ x ≠ 0 := fun x => (Submodule.inclusion_injective hle).ne_iff' (map_zero ι)
  exact ⟨ipD, ip, hm.pure, hm.hermD, hm.posD, fun x y => hm.herm (ι x) (ι y),
      fun x hx => hm.pos (ι x) ((hι x).2 hx), fun x y v v' => hm.integ (ι x) (ι y) v v',
      fun x y v v' => hm.schur (ι x) (ι y) v v'⟩

theorem t_van {c : Com D} {w : Twist D} {j : ℕ} {s : PiLocalization₂ D} {hr : D.R.r ≤ s.V.rank}
    (hle : s.CC c ≤ (flat c w j s hr).CC c)
    (h : ∀ (x : (flat c w j s hr).CC c) v, v ≠ 0 → PiLocalization₂.val x v = 0 → x = 0) :
    ∀ (x : s.CC c) v, v ≠ 0 → PiLocalization₂.val x v = 0 → x = 0 := by
  intro x v hv h0
  let ι : s.CC c →ₗ[ℂ] (flat c w j s hr).CC c := Submodule.inclusion hle
  by_contra hx
  exact (Submodule.inclusion_injective hle).ne_iff' (map_zero ι) |>.2 hx (h (ι x) v hv h0)

theorem t_par {c : Com D} {w : Twist D} {j : ℕ} {s : PiLocalization₂ D} {hr : D.R.r ≤ s.V.rank}
    (hle : s.CC c ≤ (flat c w j s hr).CC c)
    (h : ∀ (x : (flat c w j s hr).CC c) v B, PiLocalization₂.val x v ≠ 0 → ParFun c (flat c w j s hr) (PiLocalization₂.val x v) B → IsPar x B) :
    ∀ (x : s.CC c) v B, PiLocalization₂.val x v ≠ 0 → ParFun c s (PiLocalization₂.val x v) B → IsPar x B := fun x v B hv hP => by
  let ι : s.CC c →ₗ[ℂ] (flat c w j s hr).CC c := Submodule.inclusion hle
  have h' := h (ι x) v B hv hP
  exact ⟨fun h0 => h'.1 (by rw [h0]; exact map_zero ι), fun v' hv' => h'.2 v' hv'⟩

theorem softQ_all : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, SoftQ D := by
  intro hHC hCR D c w hw j hj s hs
  obtain ⟨hr, hL, hf⟩ := hs
  have hle : s.CC c ≤ (flat c w j s hr).CC c := GlobalTheory.T.chain_stage_forms_twisted_level_le_finer_level D c w hw j hj s ⟨hr, hL, hf⟩ hr
  have hMet : MetEx D := GlobalTheory.ChainMetric.metEx hCR D
  have hLev : LevFacts D := LevelFacts.levFacts D
  exact ⟨t_fd hle (finDim_of_levFacts hHC D hLev c hw.com j hj _ hf), t_met hle (hMet c hw.com j hj _ hf),
    t_van hle (val_eq_zero_imp D hMet c hw.com j hj _ hf), t_par hle (GlobalTheory.T.hecke_parameters_of_element_from_one_nonzero_value hCR D hMet hLev c hw.com j hj _ hf)⟩

end GlobalTheory.ChainTw
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedChainStageSoftPropertiesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedChain_stage_soft_properties : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, SoftQ D := by
  first | exact @GlobalTheory.ChainTw.softQ_all | exact GlobalTheory.ChainTw.softQ_all | (intros; apply GlobalTheory.ChainTw.softQ_all <;> assumption)
end
end
