module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LeviNormalizesUnipotentVariant
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HermitianPartLeLevi
public import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCJ
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ArchimedeanIwasawaMinimalParabolic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstTermEqZeroOfFrame
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorNegSpaceFrameChangeConjSubst
public import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.NormInfLeOfEntries

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ContinuousConjBlockEmbedding
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ContinuousConjBlockEmbedding
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section
namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UEmb

open Formalism.L2.Fam.ThC (colM colM_vec frameMat_eq frame_rel perp_rel prM coM embU)
open GlobalTheory.CompanionTheory.LeviGen (prj prX prY ind)
open Formalism.UG (cT)

section Abstract

variable {R : Type} [CommRing R] {a b : ℕ}

theorem lift_of_fix (s : R →+* R) {M : Matrix (Fin a) (Fin b) R} {P : Matrix (Fin b) (Fin a) R}
    {Q G H J : Matrix (Fin a) (Fin a) R} {K : Matrix (Fin b) (Fin b) R}
    (hMP : M * P + Q = 1) (hPM : P * M = 1) (hGQ : G * Q = Q) (hQG : Q * G = Q) (hGH : G * H = 1) (hHG : H * G = 1)
    (hU : cT s G * J * G = J) (hK : cT s M * J * M = K) :
    (P * G * M) * (P * H * M) = 1 ∧ (P * H * M) * (P * G * M) = 1 ∧ M * (P * G * M) = G * M ∧
      cT s (P * G * M) * K * (P * G * M) = K := by
  have eMP : M * P = 1 - Q := eq_sub_of_add_eq hMP
  have hQM : Q * M = 0 := by
    have : (M * P + Q) * M = M := by rw [hMP, Matrix.one_mul]
    rw [Matrix.add_mul, Matrix.mul_assoc, hPM, Matrix.mul_one] at this
    exact left_eq_add.1 this.symm
  have hQH : Q * H = Q := by rw [← hQG, Matrix.mul_assoc, hGH, Matrix.mul_one, hQG]
  have hHQ : H * Q = Q := by rw [← hGQ, ← Matrix.mul_assoc, hHG, Matrix.one_mul, hGQ]
  have hmid : ∀ {A B : Matrix (Fin a) (Fin a) R}, A * B = 1 → Q * B = Q → A * Q = Q →
      (P * A * M) * (P * B * M) = 1 := by
    intro A B hAB hQB hAQ
    calc (P * A * M) * (P * B * M) = P * A * (M * P) * B * M := by simp only [Matrix.mul_assoc]
      _ = P * (A * B) * M - P * (A * Q) * B * M := by
        rw [eMP]; simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]
      _ = 1 := by
        rw [hAB, hAQ, Matrix.mul_one, hPM, Matrix.mul_assoc P Q B, hQB, Matrix.mul_assoc P Q M, hQM, Matrix.mul_zero,
          sub_zero]
  have hMG : M * (P * G * M) = G * M := by
    calc M * (P * G * M) = (M * P) * G * M := by simp only [Matrix.mul_assoc]
      _ = G * M := by
        rw [eMP, Matrix.sub_mul, Matrix.sub_mul, hQG, hQM, Matrix.one_mul, sub_zero]
  refine ⟨hmid hGH hQH hGQ, hmid hHG hQG hHQ, hMG, ?_⟩
  calc cT s (P * G * M) * K * (P * G * M)
      = cT s (M * (P * G * M)) * J * (M * (P * G * M)) := by
        rw [show cT s (M * (P * G * M)) = cT s (P * G * M) * cT s M by rw [Formalism.UG.cT_mul], ← hK]
        simp only [Matrix.mul_assoc]
    _ = cT s M * (cT s G * J * G) * M := by
        rw [hMG, Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
    _ = K := by rw [hU, hK]

end Abstract

section Frame

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}

theorem mul_P {b : Type} [Fintype b] (N : Matrix b (Fin n) E) (I : Set (Fin r)) :
    N * USplit.P σ J X Y I = (N * X * diagonal (ind I : Fin r → E)) * cT (σ : E →+* E) Y * J +
      (N * Y * diagonal (ind I : Fin r → E)) * cT (σ : E →+* E) X * J := by
  simp only [USplit.P, prj, prX, prY, Matrix.mul_add, Matrix.mul_assoc]

theorem cTX_mul_P (hW : IsWittFrame σ J X Y) (I : Set (Fin r)) :
    cT (σ : E →+* E) X * J * USplit.P σ J X Y I = diagonal (ind I : Fin r → E) * (cT (σ : E →+* E) X * J) := by
  rw [mul_P, hW.xx, hW.xy]
  simp [Matrix.mul_assoc]

theorem cTY_mul_P (hCM : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) (I : Set (Fin r)) :
    cT (σ : E →+* E) Y * J * USplit.P σ J X Y I = diagonal (ind I : Fin r → E) * (cT (σ : E →+* E) Y * J) := by
  rw [mul_P, hW.yy, Comm.yJx hCM hJ hW]
  simp [Matrix.mul_assoc]

end Frame

section Space

variable {D : D7}

theorem repr_symm (V : HSp D) (c : Fin V.rank → D.host.E) : ⇑(V.frame.repr (V.frame.equivFun.symm c)) = c :=
  funext fun a => congrFun (V.frame.equivFun.apply_symm_apply c) a

theorem hT_col (V : HSp D) {m : ℕ} (C : Matrix (Fin V.rank) (Fin m) D.host.E) (c : Fin V.rank → D.host.E) (i : Fin m) :
    V.hT (V.frame.equivFun.symm fun j => C j i) (V.frame.equivFun.symm c) =
      ((cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * V.gram) *ᵥ c) i := by
  have h := colM_vec V (fun i => V.frame.equivFun.symm fun j => C j i) (V.frame.equivFun.symm c) i
  have e : colM V (fun i => V.frame.equivFun.symm fun j => C j i) = C :=
    Matrix.ext fun a b => congrFun (repr_symm V fun j => C j b) a
  rw [e, repr_symm] at h
  exact h.symm

theorem mulVec_perp {V V' : HSp D} {ι : V'.V →ₗ[D.host.E] V.V} {c : Fin V.rank → D.host.E}
    (h : ∀ v ∈ LinearMap.range ι, V.hT (V.frame.equivFun.symm c) v = 0) :
    (cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat V V' ι) * V.gram) *ᵥ c = 0 := by
  funext a
  have e := colM_vec V (fun k => ι (V'.frame k)) (V.frame.equivFun.symm c) a
  rw [repr_symm] at e
  rw [frameMat_eq, e, ← V.herm.eq, h _ ⟨_, rfl⟩]
  simp

end Space

section Main

variable {D : D7} {V V' : HSp D} {ι : V'.V →ₗ[D.host.E] V.V} {m : ℕ} {X Y : Matrix (Fin V.rank) (Fin m) D.host.E}
  {T : Finset (Fin m)}

theorem mul_diag_zero {b : Type} [Fintype b] {N : Matrix b (Fin m) D.host.E} {I : Set (Fin m)}
    (h : ∀ a, ∀ i ∈ I, N a i = 0) : N * diagonal (ind I : Fin m → D.host.E) = 0 := by
  classical
  refine Matrix.ext fun a i => ?_
  rw [Matrix.mul_diagonal, GlobalTheory.CompanionTheory.LeviGen.ind_apply]
  by_cases hi : i ∈ I
  · rw [h a i hi, zero_mul]; rfl
  · rw [if_neg hi, mul_zero]; rfl

theorem frame_proj (hCM : IsCMExt D.host.F D.host.E D.sp.cm.sig) (hJ : IsHermND D.sp.cm.sig V.gram)
    (hW : IsWittFrame D.sp.cm.sig V.gram X Y) (hι : HSpace.IsIsomEmb V' V ι)
    (hr : ∀ v : V.V, v ∈ LinearMap.range ι ↔ ∀ i ∈ upTo T, V.hT (V.frame.equivFun.symm fun j => X j i) v = 0 ∧
      V.hT (V.frame.equivFun.symm fun j => Y j i) v = 0) :
    frameMat V V' ι * prM V V' ι = 1 - USplit.P D.sp.cm.sig V.gram X Y (upTo T) := by
  classical
  set M := frameMat V V' ι with hM
  set Pr := prM V V' ι with hPr
  set Q := USplit.P D.sp.cm.sig V.gram X Y (upTo T) with hQ
  have hPM : Pr * M = 1 := by
    rw [hPr, prM, Matrix.mul_assoc, frame_rel hι, Matrix.nonsing_inv_mul _ (gram_det_ne V').isUnit]
  have hX : ∀ a, ∀ i ∈ upTo T, (cT (D.sp.cm.sig : D.host.E →+* D.host.E) M * V.gram * X) a i = 0 := fun a i hi =>
    congrFun (mulVec_perp (ι := ι) (c := fun j => X j i) fun v hv => ((hr v).1 hv i hi).1) a
  have hY : ∀ a, ∀ i ∈ upTo T, (cT (D.sp.cm.sig : D.host.E →+* D.host.E) M * V.gram * Y) a i = 0 := fun a i hi =>
    congrFun (mulVec_perp (ι := ι) (c := fun j => Y j i) fun v hv => ((hr v).1 hv i hi).2) a
  have hMQ : cT (D.sp.cm.sig : D.host.E →+* D.host.E) M * V.gram * Q = 0 := by
    rw [hQ, mul_P, mul_diag_zero hX, mul_diag_zero hY]
    simp
  have hcol : ∀ j, ∃ u, ι u = V.frame.equivFun.symm fun a => (1 - Q) a j := fun j => by
    refine (hr _).2 fun i hi => ?_
    rw [hT_col, hT_col]
    have hi' : (ind (upTo T) : Fin m → D.host.E) i = 1 := by rw [GlobalTheory.CompanionTheory.LeviGen.ind_apply, if_pos hi]
    constructor
    · have e : cT (D.sp.cm.sig : D.host.E →+* D.host.E) X * V.gram * (1 - Q) =
          (1 - diagonal (ind (upTo T) : Fin m → D.host.E)) * (cT (D.sp.cm.sig : D.host.E →+* D.host.E) X * V.gram) := by
        rw [Matrix.mul_sub, Matrix.mul_one, hQ, cTX_mul_P hW, Matrix.sub_mul, Matrix.one_mul]
      have e' := congrFun (congrFun e i) j
      refine e'.trans ?_
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, Matrix.diagonal_mul, hi', one_mul, sub_self]
    · have e : cT (D.sp.cm.sig : D.host.E →+* D.host.E) Y * V.gram * (1 - Q) =
          (1 - diagonal (ind (upTo T) : Fin m → D.host.E)) * (cT (D.sp.cm.sig : D.host.E →+* D.host.E) Y * V.gram) := by
        rw [Matrix.mul_sub, Matrix.mul_one, hQ, cTY_mul_P hCM hJ hW, Matrix.sub_mul, Matrix.one_mul]
      have e' := congrFun (congrFun e i) j
      refine e'.trans ?_
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, Matrix.diagonal_mul, hi', one_mul, sub_self]
  choose u hu using hcol
  have hA : M * Matrix.of (fun b j => V'.frame.repr (u j) b) = 1 - Q := by
    refine Matrix.ext fun a j => ?_
    have e := congrFun (LinearMap.toMatrix_mulVec_repr V'.frame V.frame ι (u j)) a
    rw [hu j, repr_symm] at e
    exact e
  have e1 : M * Pr * (1 - Q) = 1 - Q := by
    rw [← hA, Matrix.mul_assoc M Pr, ← Matrix.mul_assoc Pr, hPM, Matrix.one_mul]
  have e2 : M * Pr * Q = 0 := by
    rw [hPr, prM, Matrix.mul_assoc, Matrix.mul_assoc, hMQ]
    simp
  calc M * Pr = M * Pr * (1 - Q) + M * Pr * Q := by rw [← Matrix.mul_add, sub_add_cancel, Matrix.mul_one]
    _ = 1 - Q := by rw [e1, e2, add_zero]

end Main

section Final

theorem range_embHom : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E),
    GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (T : Finset (Fin m)) (V' : HSp D)
    (ι : V'.V →ₗ[D.host.E] V.V), HSpace.IsIsomEmb V' V ι →
    (∀ v : V.V, v ∈ LinearMap.range ι ↔ ∀ i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T,
      V.hT (V.frame.equivFun.symm fun j => X j i) v = 0 ∧ V.hT (V.frame.equivFun.symm fun j => Y j i) v = 0) →
    ∀ s : GA D V' →* GA D V, (∀ h, EmbRel V V' ι (s h) h) →
    (∀ h, s h ∈ uPart D.sp.cm.sig V.gram X Y T) ∧ (∀ g ∈ uPart D.sp.cm.sig V.gram X Y T, ∃ h, s h = g) ∧
      ∀ h ∈ GfC V', s h ∈ GfC V := by
  intro D V m X Y hW T V' ι hι hr s hs
  obtain ⟨hCM, hJ⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm
  refine ⟨fun h => ?_, fun g hg => ?_, fun h hh => Formalism.L2.Fam.ThC.emb_fin hι hs hh⟩
  · intro y hy
    let S : Submodule (AF D.host.F ⊗[D.host.F] D.host.E) (Fin V.rank → AF D.host.F ⊗[D.host.F] D.host.E) :=
      LinearMap.eqLocus (GlobalTheory.AdelicU.matHom (AF D.host.F) D.sp.cm.sig V.gram (s h)).1.mulVecLin LinearMap.id
    have hle : colSpan D.host.F X (upTo T) ⊔ colSpan D.host.F Y (upTo T) ≤ S := by
      refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
      · rintro _ ⟨i, hi, rfl⟩
        exact (hs h).2 (fun j => X j i) (mulVec_perp fun v hv => ((hr v).1 hv i hi).1)
      · rintro _ ⟨i, hi, rfl⟩
        exact (hs h).2 (fun j => Y j i) (mulVec_perp fun v hv => ((hr v).1 hv i hi).2)
    exact hle hy
  · have hF := frame_proj hCM (hJ V) hW hι hr
    set Q := USplit.P D.sp.cm.sig V.gram X Y (upTo T) with hQ
    have hF' : frameMat V V' ι * prM V V' ι + Q = 1 := by rw [hF, sub_add_cancel]
    have hPM' : prM V V' ι * frameMat V V' ι = 1 := by
      rw [prM, Matrix.mul_assoc, frame_rel hι, Matrix.nonsing_inv_mul _ (gram_det_ne V').isUnit]
    have hMP : (frameMat V V' ι).map (incA D) * (prM V V' ι).map (incA D) + adMat D.host.F Q = 1 := by
      rw [← Matrix.map_mul]
      show (frameMat V V' ι * prM V V' ι).map (incA D) + Q.map (incA D) = 1
      rw [← Matrix.map_add _ (map_add (incA D)), hF', Matrix.map_one _ (map_zero _) (map_one _)]
    have hPM : (prM V V' ι).map (incA D) * (frameMat V V' ι).map (incA D) = 1 := by
      rw [← Matrix.map_mul, hPM', Matrix.map_one _ (map_zero _) (map_one _)]
    have hGQ := USplit.Q_fix_of_uPart hCM (hJ V) hW hg
    have hJu : IsUnit (JR (F := D.host.F) (AF D.host.F) V.gram).det := by
      rw [show JR (F := D.host.F) (AF D.host.F) V.gram = V.gram.map (incA D) from rfl,
        show (V.gram.map (incA D)).det = incA D V.gram.det from (RingHom.map_det (incA D) V.gram).symm]
      exact (isUnit_iff_ne_zero.2 (hJ V).2).map (incA D)
    have hQG := Comm.mul_eq_of_unitary hJu (USplit.matHom_unitary g) (USplit.adMat_P_selfAdjoint hCM (hJ V) _) hGQ
    have hK : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) ((frameMat V V' ι).map (incA D)) *
        JR (F := D.host.F) (AF D.host.F) V.gram * (frameMat V V' ι).map (incA D) =
        JR (F := D.host.F) (AF D.host.F) V'.gram := by
      rw [Comm.cT_map]
      have e := congrArg (fun A => Matrix.map A (incA D)) (frame_rel hι)
      simp only [Matrix.map_mul] at e
      exact e
    obtain ⟨h1, h2, h3, h4⟩ := lift_of_fix (sigR (AF D.host.F) D.sp.cm.sig) hMP hPM hGQ hQG
      (USplit.matHom_mul_inv g) (USplit.matHom_inv_mul g) (USplit.matHom_unitary g) hK
    let h : GA D V' := show HR (AF D.host.F) D.sp.cm.sig V'.gram from ⟨⟨_, _, h1, h2⟩, h4⟩
    refine ⟨h, embU D V V' ι hι _ _ h (hs h) ⟨h3.symm, fun x hx => ?_⟩⟩
    have hPx : prM V V' ι *ᵥ x = 0 := by rw [prM, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]
    have hQx : Q *ᵥ x = x := by
      have e : (frameMat V V' ι * prM V V' ι + Q) *ᵥ x = x := by rw [hF', Matrix.one_mulVec]
      rwa [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hPx, Matrix.mulVec_zero, zero_add] at e
    have hb : adMat D.host.F Q *ᵥ (fun i => incA D (x i)) = fun i => incA D (x i) := by
      funext i
      exact ((incA D).map_mulVec Q x i).symm.trans (congrArg _ (congrFun hQx i))
    show (GlobalTheory.AdelicU.matHom (AF D.host.F) D.sp.cm.sig V.gram g).1 *ᵥ (fun i => incA D (x i)) = _
    rw [← hb, Matrix.mulVec_mulVec, hGQ]

end Final

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UEmb
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ContinuousConjBlockEmbeddingStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthogonal_subspace_unitary_embedding : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (T : Finset (Fin m)) (V' : HSp D) (ι : V'.V →ₗ[D.host.E] V.V), HSpace.IsIsomEmb V' V ι → (∀ v : V.V, v ∈ LinearMap.range ι ↔ ∀ i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T, V.hT (V.frame.equivFun.symm fun j => X j i) v = 0 ∧ V.hT (V.frame.equivFun.symm fun j => Y j i) v = 0) → ∀ s : GA D V' →* GA D V, (∀ h, EmbRel V V' ι (s h) h) → (∀ h, s h ∈ uPart D.sp.cm.sig V.gram X Y T) ∧ (∀ g ∈ uPart D.sp.cm.sig V.gram X Y T, ∃ h, s h = g) ∧ ∀ h ∈ GfC V', s h ∈ GfC V := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UEmb.range_embHom | exact GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UEmb.range_embHom | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UEmb.range_embHom <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.CTFrameMatMulGram
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section
namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice

def IsSliceFrame {D : D7} (V V' : HSp D) (ι : V'.V →ₗ[D.host.E] V.V) {m m' : ℕ}
    (X Y : Matrix (Fin V.rank) (Fin m) D.host.E) (T : Finset (Fin m)) (e : Fin m' → Fin m)
    (X' Y' : Matrix (Fin V'.rank) (Fin m') D.host.E) : Prop :=
  StrictMono e ∧ (∀ i, i ∉ upTo T ↔ i ∈ Set.range e) ∧
    frameMat V V' ι * X' = X.submatrix id e ∧ frameMat V V' ι * Y' = Y.submatrix id e

variable {D : D7} {V V' : HSp D} {ι : V'.V →ₗ[D.host.E] V.V}

abbrev prM (V V' : HSp D) (ι : V'.V →ₗ[D.host.E] V.V) : Matrix (Fin V'.rank) (Fin V.rank) D.host.E :=
  GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.projMat D.sp.cm V' V ι

theorem repr_symm (V : HSp D) (a : Fin V.rank → D.host.E) (i : Fin V.rank) :
    V.frame.repr (V.frame.equivFun.symm a) i = a i := by
  rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]

theorem hT_frame (V : HSp D) (a b : Fin V.rank → D.host.E) :
    V.hT (V.frame.equivFun.symm a) (V.frame.equivFun.symm b) = ∑ i, ∑ j, star (a i) * V.gram i j * b j := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.hT_coord]
  simp only [repr_symm]

theorem prM_mul_frameMat (hι : HSpace.IsIsomEmb V' V ι) : prM V V' ι * frameMat V V' ι = 1 :=
  GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.projMat_embMat D.sp.cm V' V ι hι

theorem cT_frameMat_mul_gram :
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat V V' ι) * V.gram = V'.gram * prM V V' ι :=
  GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_projMat D.sp.cm V' V ι

theorem mat_eq (hι : HSpace.IsIsomEmb V' V ι) {s : GA D V' →* GA D V} (hs : ∀ h, EmbRel V V' ι (s h) h) (b : GA D V') :
    (matHom V (s b)).1 = 1 + HMul.hMul (HMul.hMul (adMat D.host.F (frameMat V V' ι)) ((matHom V' b).1 - 1)) (adMat D.host.F (prM V V' ι)) := by
  rw [(GlobalTheory.AutFunCompare.embRel_iff V V' ι hι (s b) b).1 (hs b)]
  rfl

theorem prM_mulVec_eq_zero {x : Fin V.rank → D.host.E}
    (h : ∀ v' : V'.V, V.hT (V.frame.equivFun.symm x) (ι v') = 0) : prM V V' ι *ᵥ x = 0 := by
  have hJ : IsUnit V'.gram.det := GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit V'
  have h1 : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat V V' ι) * V.gram) *ᵥ x = 0 := by
    funext j
    have h2 : V.hT (ι (V'.frame j)) (V.frame.equivFun.symm x) = 0 :=
      (V.herm.eq (V.frame.equivFun.symm x) (ι (V'.frame j))).symm.trans (by rw [h]; simp)
    rw [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.hT_coord] at h2
    simp only [repr_symm] at h2
    simp only [Pi.zero_apply, Matrix.mulVec, dotProduct, Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Eq.trans (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_) h2
    simp only [Formalism.UG.cT, frameMat, LinearMap.toMatrix_apply, Matrix.transpose_apply, Matrix.map_apply]
    rfl
  rw [cT_frameMat_mul_gram, ← Matrix.mulVec_mulVec] at h1
  exact Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).2 hJ) (h1.trans (Matrix.mulVec_zero _).symm)

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.OrthogonalSubspaceUnitaryEmbedding
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.OrthogonalSubspaceUnitaryEmbedding
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section

namespace GlobalTheory.CompanionTheory.WittCompl

theorem hT_coords {D : D7} (V : HSp D) (a b : Fin V.rank → D.host.E) :
    V.hT (V.frame.equivFun.symm a) (V.frame.equivFun.symm b) =
      ∑ k, ∑ l, star (a k) * V.gram k l * b l := by
  simp only [Module.Basis.equivFun_symm_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul, HSpace.gram,
    starRingEnd_apply, Finset.mul_sum, RingHom.id_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem hT_cols {D : D7} (V : HSp D) {m : ℕ} (A B : Matrix (Fin V.rank) (Fin m) D.host.E) (i j : Fin m) :
    V.hT (V.frame.equivFun.symm fun k => A k i) (V.frame.equivFun.symm fun k => B k j) =
      (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) A * V.gram * B) i j := by
  rw [hT_coords]
  simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

theorem exists_perp {E : Type} [Field E] [NumberField E] [StarRing E] (hst : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x))
    (V : HSpace E) {n : ℕ} (c d : Fin n → V.V) (hcc : ∀ i j, V.hT (c i) (c j) = 0)
    (hcd : ∀ i j, V.hT (c i) (d j) = if i = j then 1 else 0) :
    ∃ (V' : HSpace E) (ι : V'.V →ₗ[E] V.V), HSpace.IsIsomEmb V' V ι ∧
      ∀ v, v ∈ LinearMap.range ι ↔ ∀ i, V.hT (c i) v = 0 ∧ V.hT (d i) v = 0 := by
  classical
  have hs := V.herm
  have hdc : ∀ i j, V.hT (d i) (c j) = if i = j then 1 else 0 := fun i j => by
    rw [← hs.eq (c j) (d i), hcd]
    by_cases h : i = j
    · simp [h]
    · simp [h, Ne.symm h]
  have hc : LinearIndependent E c := Fintype.linearIndependent_iff.2 fun g hg j => by
    have := congrArg (V.hT (d j)) hg
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [map_sum, hdc] using this
  obtain ⟨V', ι, hr, hι, h0⟩ := GlobalTheory.WittLow.exists_lower hst V c hc hcc
  have h0' : ∀ x a, V.hT (c a) (ι x) = 0 := fun x a => by rw [← hs.eq (ι x) (c a), h0, map_zero]
  let p : V.V →ₗ[E] V.V := LinearMap.id - ∑ k, (V.hT (d k)).smulRight (c k)
  have hp : ∀ v, p v = v - ∑ k, V.hT (d k) v • c k := fun v => by simp [p, LinearMap.sum_apply]
  have hcp : ∀ a v, V.hT (c a) (p v) = V.hT (c a) v := fun a v => by simp [hp, map_sum, hcc]
  have hdp : ∀ a v, V.hT (d a) (p v) = 0 := fun a v => by simp [hp, map_sum, hdc]
  have hiso : HSpace.IsIsomEmb V' V (p ∘ₗ ι) := fun x y => by
    rw [← hι x y]
    show V.hT (p (ι x)) (p (ι y)) = V.hT (ι x) (ι y)
    have e1 : V.hT (ι x) (p (ι y)) = V.hT (ι x) (ι y) := by simp [hp, map_sum, h0]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hp (ι x), map_sub, LinearMap.sub_apply, e1, map_sum, LinearMap.sum_apply]
    simp [hcp, h0']
  have hinj : Function.Injective ι := (injective_iff_map_eq_zero ι).2 fun x hx =>
    V'.nondeg.1 x fun y => by rw [← hι x y, hx]; simp
  set P : Submodule E V.V := LinearMap.ker (LinearMap.pi fun j => V.hT (c j)) with hP
  have hdisj : Disjoint (LinearMap.range ι) (Submodule.span E (Set.range c)) := by
    rw [Submodule.disjoint_def]
    rintro _ ⟨x, rfl⟩ hx
    obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hx
    have : x = 0 := V'.nondeg.1 x fun y => by
      rw [← hι x y, ← hg]
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum, LinearMap.sum_apply, h0']
    rw [this, map_zero]
  have hle : LinearMap.range ι ⊔ Submodule.span E (Set.range c) ≤ P :=
    sup_le (by rintro _ ⟨x, rfl⟩; exact funext fun j => h0' x j)
      (Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact funext fun a => hcc a j))
  have heq : LinearMap.range ι ⊔ Submodule.span E (Set.range c) = P := by
    refine Submodule.eq_of_le_of_finrank_eq hle ?_
    have e1 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range ι) (Submodule.span E (Set.range c))
    rw [hdisj.eq_bot, finrank_bot, LinearMap.finrank_range_of_inj hinj, finrank_span_eq_card hc, Fintype.card_fin] at e1
    have e2 := GlobalTheory.WittLow.finrank_orth hs V.nondeg c hc
    have e3 : Module.finrank E V'.V = V'.rank := by first | rfl | simpa using Module.finrank_eq_card_basis V'.frame
    have e4 : Module.finrank E V.V = V.rank := by first | rfl | simpa using Module.finrank_eq_card_basis V.frame
    rw [← hP] at e2
    omega
  refine ⟨V', p ∘ₗ ι, hiso, fun v => ⟨?_, fun hv => ?_⟩⟩
  · rintro ⟨x, rfl⟩ i
    exact ⟨(hcp i _).trans (h0' x i), hdp i _⟩
  · have hvP : v ∈ P := funext fun j => (hv j).1
    rw [← heq] at hvP
    obtain ⟨_, ⟨x, rfl⟩, u, hu, rfl⟩ := Submodule.mem_sup.1 hvP
    obtain ⟨g, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hu
    refine ⟨x, ?_⟩
    have hg : ∀ k, V.hT (d k) (ι x) = -g k := fun k => by
      have := (hv k).2
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum, hdc] at this
      exact eq_neg_of_add_eq_zero_left this
    show p (ι x) = _
    simp [hp, hg, sub_eq_add_neg]

theorem exists_compl : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ T : Finset (Fin m), ∃ (V' : HSp D) (ι : V'.V →ₗ[D.host.E] V.V), HSpace.IsIsomEmb V' V ι ∧ ∀ v : V.V, v ∈ LinearMap.range ι ↔ ∀ i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T, V.hT (V.frame.equivFun.symm fun j => X j i) v = 0 ∧ V.hT (V.frame.equivFun.symm fun j => Y j i) v = 0 := by
  intro D V m X Y h T
  classical
  let e := Fintype.equivFin {i // i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T}
  let c : Fin (Fintype.card {i // i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T}) → V.V :=
    fun k => V.frame.equivFun.symm fun j => X j (e.symm k).1
  let d : Fin (Fintype.card {i // i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T}) → V.V :=
    fun k => V.frame.equivFun.symm fun j => Y j (e.symm k).1
  have hcc : ∀ i j, V.hT (c i) (c j) = 0 := fun i j => by
    simp only [c]
    rw [hT_cols, h.xx]
    rfl
  have hcd : ∀ i j, V.hT (c i) (d j) = if i = j then 1 else 0 := fun i j => by
    simp only [c, d]
    rw [hT_cols, h.xy, Matrix.one_apply]
    simp only [Subtype.val_inj, e.symm.apply_eq_iff_eq]
  obtain ⟨V', ι, hι, hr⟩ := exists_perp Formalism.BasicNotions.Examples₂.star_isIntegral V c d hcc hcd
  refine ⟨V', ι, hι, fun v => ?_⟩
  rw [hr]
  constructor
  · intro hv i hi
    have := hv (e ⟨i, hi⟩)
    simpa [c, d] using this
  · intro hv k
    exact hv _ (e.symm k).2

end GlobalTheory.CompanionTheory.WittCompl

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.OrthogonalSubspaceUnitaryEmbeddingStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orthogonal_hermitian_subspace : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ T : Finset (Fin m), ∃ (V' : HSp D) (ι : V'.V →ₗ[D.host.E] V.V), HSpace.IsIsomEmb V' V ι ∧ ∀ v : V.V, v ∈ LinearMap.range ι ↔ ∀ i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T, V.hT (V.frame.equivFun.symm fun j => X j i) v = 0 ∧ V.hT (V.frame.equivFun.symm fun j => Y j i) v = 0 := by
  first | exact @GlobalTheory.CompanionTheory.WittCompl.exists_compl | exact GlobalTheory.CompanionTheory.WittCompl.exists_compl | (intros; apply GlobalTheory.CompanionTheory.WittCompl.exists_compl <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.UnitaryElementPrescribedBlocks
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.UnitaryElementPrescribedBlocks
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section
namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore

def compHom {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (τ : D.what₂.Tau) :
    AF D.host.F ⊗[D.host.F] D.host.E →+* ℂ := (θ τ).comp (infPart D)

theorem adele_ext {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} (hθ : IsInfFam θ)
    {a b : AF D.host.F ⊗[D.host.F] D.host.E} (hf : finPart D a = finPart D b)
    (hc : ∀ τ, compHom θ τ a = compHom θ τ b) : a = b := by
  obtain ⟨w, -, hw⟩ := Formalism.IndefR.Mi.realPtEx_holds (D := D) θ 1 1 hθ (fun _ _ _ => 0)
  have h0 : ∀ c : AF D.host.F ⊗[D.host.F] D.host.E, finPart D c = 0 → (∀ τ, compHom θ τ c = 0) → c = 0 := by
    intro c h1 h2
    have e1 : (Matrix.of fun _ _ => c : Matrix (Fin 1) (Fin 1) _) = w := hw _ ⟨by
      ext i j
      exact h1, fun τ => by
      ext i j
      exact h2 τ⟩
    have e2 : (0 : Matrix (Fin 1) (Fin 1) (AF D.host.F ⊗[D.host.F] D.host.E)) = w := hw _ ⟨by
      ext i j
      exact map_zero (finPart D), fun τ => by
      ext i j
      exact map_zero (compHom θ τ)⟩
    exact congrFun (congrFun (e1.trans e2.symm) 0) 0
  refine sub_eq_zero.1 (h0 _ ?_ fun τ => ?_)
  · rw [map_sub, hf, sub_self]
  · rw [map_sub, hc, sub_self]

theorem compHom_adMat {D : D7} {a b : ℕ} (τ : D.what₂.Tau) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (hθ : IsInfFam θ) (Y : Matrix (Fin a) (Fin b) D.host.E) :
    (adMat D.host.F Y).map (compHom θ τ) = Y.map (tauE D τ) := by
  ext i j
  have : infPart D ((1 : AF D.host.F) ⊗ₜ[D.host.F] Y i j) = (1 : Ainf D.host.F) ⊗ₜ[D.host.F] Y i j := by
    simp [infPart]
  simp only [Matrix.map_apply, adMat, compHom, RingHom.comp_apply]
  show θ τ (infPart D ((1 : AF D.host.F) ⊗ₜ[D.host.F] Y i j)) = _
  rw [this]
  exact (hθ τ).1 _

theorem map_one_add_of {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) {n a b : ℕ}
    (P : Matrix (Fin n) (Fin a) A) (Q : Matrix (Fin a) (Fin n) A) (R : Matrix (Fin n) (Fin b) A) (S : Matrix (Fin b) (Fin n) A)
    {p : Matrix (Fin n) (Fin a) B} {q : Matrix (Fin a) (Fin n) B} {r : Matrix (Fin n) (Fin b) B} {s : Matrix (Fin b) (Fin n) B}
    (hp : P.map φ = p) (hq : Q.map φ = q) (hr : R.map φ = r) (hs : S.map φ = s) :
    (1 + P * Q + R * S).map φ = 1 + p * q + r * s := by
  subst hp hq hr hs
  rw [Matrix.map_add _ (map_add φ), Matrix.map_add _ (map_add φ), Matrix.map_one _ (map_zero φ) (map_one φ), Matrix.map_mul, Matrix.map_mul]

theorem map_one_add_of_zero {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) {n a b : ℕ}
    (P : Matrix (Fin n) (Fin a) A) (Q : Matrix (Fin a) (Fin n) A) (R : Matrix (Fin n) (Fin b) A) (S : Matrix (Fin b) (Fin n) A)
    (hq : Q.map φ = 0) (hr : R.map φ = 0) : (1 + P * Q + R * S).map φ = 1 := by
  rw [map_one_add_of φ P Q R S rfl hq hr rfl, Matrix.mul_zero, Matrix.zero_mul, add_zero, add_zero]

theorem matrix_ext_parts {D : D7} {n : ℕ} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} (hθ : IsInfFam θ)
    (M N : Matrix (Fin n) (Fin n) (AF D.host.F ⊗[D.host.F] D.host.E))
    (hf : M.map (finPart D) = N.map (finPart D)) (hc : ∀ τ, M.map (compHom θ τ) = N.map (compHom θ τ)) : M = N := by
  ext i j
  exact adele_ext hθ (congrFun (congrFun hf i) j) fun τ => congrFun (congrFun (hc τ) i) j

theorem map_compHom_mul {D : D7} {a b c : ℕ} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (τ : D.what₂.Tau)
    (A : Matrix (Fin a) (Fin b) (AF D.host.F ⊗[D.host.F] D.host.E)) (B : Matrix (Fin b) (Fin c) (AF D.host.F ⊗[D.host.F] D.host.E)) :
    (A * B).map (compHom θ τ) = A.map (compHom θ τ) * B.map (compHom θ τ) := Matrix.map_mul

theorem map_finPart_mul {D : D7} {a b c : ℕ}
    (A : Matrix (Fin a) (Fin b) (AF D.host.F ⊗[D.host.F] D.host.E)) (B : Matrix (Fin b) (Fin c) (AF D.host.F ⊗[D.host.F] D.host.E)) :
    (A * B).map (finPart D) = A.map (finPart D) * B.map (finPart D) := Matrix.map_mul

theorem compHom_adMat_adj {D : D7} {m : ℕ} (τ : D.what₂.Tau) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (hθ : IsInfFam θ) (V : HSp D) (X : Matrix (Fin V.rank) (Fin m) D.host.E) :
    (adMat D.host.F (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X * V.gram)).map (compHom θ τ) =
      (X.map (tauE D τ))ᴴ * gramAt D V τ := by
  rw [compHom_adMat τ θ hθ, Matrix.map_mul]
  congr 1
  ext i j
  exact GlobalTheory.Mem.Isom.tauE_sig D τ (X j i)

theorem exists_adelic_of_real_comps : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) {m : ℕ}
    (X : Matrix (Fin V.rank) (Fin m) D.host.E) (u : D.what₂.Tau → Matrix (Fin m) (Fin V.rank) ℂ)
    (w : D.what₂.Tau → Matrix (Fin V.rank) (Fin m) ℂ),
    (∀ τ, 1 + X.map (tauE D τ) * u τ + w τ * (X.map (tauE D τ))ᴴ * gramAt D V τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) →
    ∃ g : GA D V, (∀ τ, infMat D.sp.cm.sig V.gram (θ τ) g = 1 + X.map (tauE D τ) * u τ + w τ * (X.map (tauE D τ))ᴴ * gramAt D V τ) ∧
      ∃ (U : Matrix (Fin m) (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E))
        (W : Matrix (Fin V.rank) (Fin m) (AF D.host.F ⊗[D.host.F] D.host.E)),
        (∀ i v, (∀ τ, u τ i v = 0) → U i v = 0) ∧ (∀ v i, (∀ τ, w τ v i = 0) → W v i = 0) ∧
        (∀ i j, (∀ τ, (u τ * X.map (tauE D τ)) i j = 0) → (HMul.hMul U (GlobalTheory.SiegelSet.adMat D.host.F X) : Matrix (Fin m) (Fin m) (AF D.host.F ⊗[D.host.F] D.host.E)) i j = 0) ∧
        (matHom V g).1 = 1 + (HMul.hMul (GlobalTheory.SiegelSet.adMat D.host.F X) U : Matrix (Fin V.rank) (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E)) +
          (HMul.hMul W (GlobalTheory.SiegelSet.adMat D.host.F (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X * V.gram)) : Matrix (Fin V.rank) (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E)) := by
  intro D θ hθ V m X u w hU
  obtain ⟨-, h2⟩ := GlobalTheory.SmoothForms.RealPts.glue θ hθ V
  obtain ⟨g, hg, hgτ⟩ := h2 _ hU
  obtain ⟨U, ⟨hUf, hUc⟩, -⟩ := Formalism.IndefR.Mi.realPtEx_holds (D := D) θ m V.rank hθ (fun τ i j => u τ i j)
  obtain ⟨W, ⟨hWf, hWc⟩, -⟩ := Formalism.IndefR.Mi.realPtEx_holds (D := D) θ V.rank m hθ (fun τ i j => w τ i j)
  have hUc' : ∀ τ, U.map (compHom θ τ) = u τ := hUc
  have hWc' : ∀ τ, W.map (compHom θ τ) = w τ := hWc
  have hUf' : U.map (finPart D) = 0 := hUf
  have hWf' : W.map (finPart D) = 0 := hWf
  have hzero : ∀ c : AF D.host.F ⊗[D.host.F] D.host.E, finPart D c = 0 → (∀ τ, compHom θ τ c = 0) → c = 0 :=
    fun c h1 h2 => adele_ext hθ (by rw [h1, map_zero]) fun τ => by rw [h2, map_zero]
  refine ⟨g, hgτ, U, W, fun i v h => ?_, fun v i h => ?_, fun i j h => ?_, ?_⟩
  · refine hzero _ (congrFun (congrFun hUf' i) v) fun τ => ?_
    rw [← h τ, ← hUc' τ]
    rfl
  · refine hzero _ (congrFun (congrFun hWf' v) i) fun τ => ?_
    rw [← h τ, ← hWc' τ]
    rfl
  · refine hzero _ ?_ fun τ => ?_
    · have e := map_finPart_mul U (adMat D.host.F X)
      rw [hUf', Matrix.zero_mul] at e
      exact congrFun (congrFun e i) j
    · have e := map_compHom_mul θ τ U (adMat D.host.F X)
      rw [hUc', compHom_adMat τ θ hθ] at e
      rw [← h τ, ← e]
      rfl
  · have hf : (matHom V g).1.map (finPart D) = 1 := by
      have hg' : finHom V g = 1 := hg
      have e : (finHom V g).1 = (matHom V g).1.map (finPart D) := rfl
      rw [← e, hg', Units.val_one]
    refine matrix_ext_parts hθ _ _ ?_ fun τ => ?_
    · exact hf.trans (map_one_add_of_zero (finPart D) _ _ _ _ hUf' hWf').symm
    · have e := map_one_add_of (compHom θ τ) (adMat D.host.F X) U W
        (adMat D.host.F (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X * V.gram))
        (compHom_adMat τ θ hθ X) (hUc' τ) (hWc' τ) (compHom_adMat_adj τ θ hθ V X)
      refine (hgτ τ).trans (Eq.trans ?_ e.symm)
      rw [Matrix.mul_assoc (w τ)]

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.UnitaryElementPrescribedBlocksStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_unitary_element_lift : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) {m : ℕ}
    (X : Matrix (Fin V.rank) (Fin m) D.host.E) (u : D.what₂.Tau → Matrix (Fin m) (Fin V.rank) ℂ)
    (w : D.what₂.Tau → Matrix (Fin V.rank) (Fin m) ℂ),
    (∀ τ, 1 + X.map (tauE D τ) * u τ + w τ * (X.map (tauE D τ))ᴴ * gramAt D V τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) →
    ∃ g : GA D V, (∀ τ, infMat D.sp.cm.sig V.gram (θ τ) g = 1 + X.map (tauE D τ) * u τ + w τ * (X.map (tauE D τ))ᴴ * gramAt D V τ) ∧
      ∃ (U : Matrix (Fin m) (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E))
        (W : Matrix (Fin V.rank) (Fin m) (AF D.host.F ⊗[D.host.F] D.host.E)),
        (∀ i v, (∀ τ, u τ i v = 0) → U i v = 0) ∧ (∀ v i, (∀ τ, w τ v i = 0) → W v i = 0) ∧
        (∀ i j, (∀ τ, (u τ * X.map (tauE D τ)) i j = 0) → (HMul.hMul U (GlobalTheory.SiegelSet.adMat D.host.F X) : Matrix (Fin m) (Fin m) (AF D.host.F ⊗[D.host.F] D.host.E)) i j = 0) ∧
        (matHom V g).1 = 1 + (HMul.hMul (GlobalTheory.SiegelSet.adMat D.host.F X) U : Matrix (Fin V.rank) (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E)) +
          (HMul.hMul W (GlobalTheory.SiegelSet.adMat D.host.F (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X * V.gram)) : Matrix (Fin V.rank) (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E)) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.exists_adelic_of_real_comps | exact GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.exists_adelic_of_real_comps | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.exists_adelic_of_real_comps <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.SmoothAutomorphicDerivativeGrowth
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.SmoothAutomorphicDerivativeGrowth
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.SliceReg

variable {D : D7}

theorem exists_lie_oneP {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} (hθ : IsInfFam θ) {V V' : HSp D}
    {ι : V'.V →ₗ[D.host.E] V.V} (hι : HSpace.IsIsomEmb V' V ι) {s : GA D V' →* GA D V} (hs : ∀ h, EmbRel V V' ι (s h) h)
    (τ : D.what₂.Tau) {X : Matrix (Fin V'.rank) (Fin V'.rank) ℂ} (hX : X ∈ lieAt V' τ) :
    ∃ Z ∈ lieAt V τ, ∀ t : ℝ, s (oneP θ V' τ X t) = oneP θ V τ Z t := by
  set c := tauE D τ with hc
  set F : Matrix (Fin V.rank) (Fin V'.rank) ℂ := (frameMat V V' ι).map c with hF
  set H := gramAt D V τ with hH
  set H' := gramAt D V' τ with hH'
  have hFH : Fᴴ * H = (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat V V' ι) * V.gram).map c := by
    rw [Matrix.map_mul]
    congr 1
    ext a b
    simp only [F, Matrix.conjTranspose_apply, Matrix.map_apply, Formalism.UG.cT, Matrix.transpose_apply]
    exact (Formalism.IndefR.Eqv.tauE_star D τ _).symm
  have hG := Formalism.L2.GlobalTheoryTheory.VolumeCarry.gram_frameMat D V V' ι hι
  rw [← Formalism.IndefR.Mi.frameMat_eq_global] at hG
  have hFHF : Fᴴ * H * F = H' := by
    rw [hFH, hF, ← Matrix.map_mul, ← hG]; rfl
  have hHu : IsUnit H'.det := GlobalTheory.SmoothAutCheck.gramAt_unit V' τ
  have hHh : H'ᴴ = H' := GlobalTheory.SmoothForms.RealPts.gramAt_herm V' τ
  have hHV : Hᴴ = H := GlobalTheory.SmoothForms.RealPts.gramAt_herm V τ
  have hR1 : H'⁻¹ * H' = 1 := Matrix.nonsing_inv_mul _ hHu
  have hR2 : H' * H'⁻¹ = 1 := Matrix.mul_nonsing_inv _ hHu
  have hRh : (H'⁻¹)ᴴ = H'⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hHh]
  have hXl : Xᴴ * H' + H' * X = 0 := hX
  set Z : Matrix (Fin V.rank) (Fin V.rank) ℂ := F * X * H'⁻¹ * (Fᴴ * H) with hZ
  have hZF : Z * F = F * X := by
    rw [hZ, Matrix.mul_assoc, hFHF, Matrix.mul_assoc, hR1, Matrix.mul_one]
  have hZl : Z ∈ lieAt V τ := by
    change Zᴴ * H + H * Z = 0
    have e1 : Zᴴ * H = H * F * (H'⁻¹ * (Xᴴ * H') * H'⁻¹) * (Fᴴ * H) := by
      rw [hZ]
      simp only [Matrix.conjTranspose_mul, hHV, hRh, Matrix.conjTranspose_conjTranspose]
      have : H'⁻¹ * (Xᴴ * H') * H'⁻¹ = H'⁻¹ * Xᴴ := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, hR2, Matrix.mul_one]
      rw [this]
      simp only [Matrix.mul_assoc]
    have e2 : H * Z = H * F * (H'⁻¹ * (H' * X) * H'⁻¹) * (Fᴴ * H) := by
      have : H'⁻¹ * (H' * X) * H'⁻¹ = X * H'⁻¹ := by
        rw [← Matrix.mul_assoc, hR1, Matrix.one_mul]
      rw [this, hZ]
      simp only [Matrix.mul_assoc]
    rw [e1, e2, ← Matrix.add_mul, ← Matrix.mul_add, ← Matrix.add_mul, ← Matrix.mul_add, hXl]
    simp
  refine ⟨Z, hZl, fun t => ?_⟩
  have h1 : NormedSpace.exp (t • X) ∈ Formalism.QuantumDeterminants.UH H' := GlobalTheory.SmoothAutCheck.exp_mem_UH hHu hX t
  have h2 : NormedSpace.exp (t • Z) ∈ Formalism.QuantumDeterminants.UH H :=
    GlobalTheory.SmoothAutCheck.exp_mem_UH (GlobalTheory.SmoothAutCheck.gramAt_unit V τ) hZl t
  have hE : GlobalTheory.RealBessel.IsEmb H F (NormedSpace.exp (t • Z)) (NormedSpace.exp (t • X)) := by
    refine ⟨GlobalTheory.matrix_exp_smul_mul_eq_mul_exp_smul_of_intertwine _ _ Z F X hZF t, fun x hx => ?_⟩
    have hZx : Z *ᵥ x = 0 := by
      rw [hZ, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]
    let W : Matrix (Fin V.rank) (Fin 1) ℂ := Matrix.of fun i _ => x i
    have hW : Z * W = W * (0 : Matrix (Fin 1) (Fin 1) ℂ) := by
      rw [Matrix.mul_zero]
      ext i j
      have := congrFun hZx i
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, W] using this
    have h3 := GlobalTheory.matrix_exp_smul_mul_eq_mul_exp_smul_of_intertwine _ _ Z W 0 hW t
    rw [smul_zero, NormedSpace.exp_zero, Matrix.mul_one] at h3
    funext i
    have := congrFun (congrFun h3 i) 0
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, W] using this
  exact GlobalTheory.AutFunCounterexample.embRel_unique V V' ι hι (hs _)
    (GlobalTheory.EmbAtPlace.embRel_atTau D θ hθ V' V ι τ _ _ h1 h2 hE)

theorem foldr_Rder_eq {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} (hθ : IsInfFam θ) {V V' : HSp D}
    {ι : V'.V →ₗ[D.host.E] V.V} (hι : HSpace.IsIsomEmb V' V ι) {s : GA D V' →* GA D V} (hs : ∀ h, EmbRel V V' ι (s h) h)
    {y : GA D V} (hy : ∀ h, s h * y = y * s h) (ψ : GA D V → ℂ)
    (l : List (D.what₂.Tau × Matrix (Fin V'.rank) (Fin V'.rank) ℂ)) (hl : ∀ p ∈ l, p.2 ∈ lieAt V' p.1) :
    ∃ l' : List (ℝ → GA D V), (∀ γ ∈ l', IsRealLine D.sp.cm.sig V.gram γ) ∧
      ∀ h, (l.foldr (fun p f => Rder θ V' p.1 p.2 f) (fun h => ψ (s h * y))) h = l'.foldr lineDer ψ (s h * y) := by
  induction l with
  | nil => exact ⟨[], by simp, fun _ => rfl⟩
  | cons p l ih =>
    obtain ⟨l', h1, h2⟩ := ih fun q hq => hl q (List.mem_cons_of_mem _ hq)
    obtain ⟨Z, hZ, e⟩ := exists_lie_oneP hθ hι hs p.1 (hl p List.mem_cons_self)
    refine ⟨oneP θ V p.1 Z :: l', List.forall_mem_cons.2 ⟨GlobalTheory.SphSmooth.isRealLine_oneP hθ V hZ, h1⟩, fun h => ?_⟩
    rw [List.foldr_cons, List.foldr_cons]
    simp only [Rder, lineDer]
    congr 1
    funext t
    rw [h2, map_mul, mul_assoc, hy, ← mul_assoc, e t]

theorem normInf_s_le (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V V' : HSp D}
    {ι : V'.V →ₗ[D.host.E] V.V} (hι : HSpace.IsIsomEmb V' V ι) {s : GA D V' →* GA D V} (hs : ∀ h, EmbRel V V' ι (s h) h)
    (hV : 0 < V'.rank) : ∃ K : ℝ, 0 ≤ K ∧ ∀ g : GA D V', normInf θ V (s g) ≤ K * normInf θ V' g := by
  obtain ⟨C, hC0, hC⟩ := Formalism.IndefR.Mi.s_entry_le θ hι hs
  refine ⟨Fintype.card D.what₂.Tau * (V.rank * (V.rank * (4 * C))), by positivity, fun g => ?_⟩
  have h1 := GlobalTheory.RatCount.one_le_normInf θ hV g
  set b := normInf θ V' g with hb
  have hb0 : 0 ≤ b := by linarith
  have hE : ∀ τ i j, ‖infMat D.sp.cm.sig V'.gram (θ τ) g i j‖ + ‖infMat D.sp.cm.sig V'.gram (θ τ) g⁻¹ i j‖ ≤ b := fun τ i j =>
    (Formalism.IndefR.Mi.entry_le_sum (fun i j => ‖infMat D.sp.cm.sig V'.gram (θ τ) g i j‖ + ‖infMat D.sp.cm.sig V'.gram (θ τ) g⁻¹ i j‖)
      (fun _ _ => by positivity) i j).trans
    (Finset.single_le_sum (f := fun τ => ∑ i, ∑ j, (‖infMat D.sp.cm.sig V'.gram (θ τ) g i j‖ + ‖infMat D.sp.cm.sig V'.gram (θ τ) g⁻¹ i j‖))
      (fun _ _ => by positivity) (Finset.mem_univ τ))
  have a1 : ∀ τ k l, ‖θ τ (Formalism.L2.Theta.infPart D (Formalism.L2.Theta.mt V' g k l))‖ ≤ b := fun τ k l => by
    rw [← Formalism.IndefR.Eqv.infMat_eq]
    linarith [hE τ k l, norm_nonneg (infMat D.sp.cm.sig V'.gram (θ τ) g⁻¹ k l)]
  have a2 : ∀ τ k l, ‖θ τ (Formalism.L2.Theta.infPart D (Formalism.L2.Theta.mt V' g⁻¹ k l))‖ ≤ b := fun τ k l => by
    rw [← Formalism.IndefR.Eqv.infMat_eq]
    linarith [hE τ k l, norm_nonneg (infMat D.sp.cm.sig V'.gram (θ τ) g k l)]
  have hh := Formalism.IndefR.Mi.normInf_le_of_entries θ V (s g) (C * (b + 1)) fun τ i j =>
    ⟨hC g τ b hb0 (a1 τ) i j, by rw [← map_inv]; exact hC g⁻¹ τ b hb0 (a2 τ) i j⟩
  refine hh.trans ?_
  have h4 : C * (b + 1) + C * (b + 1) ≤ 4 * C * b := by nlinarith
  calc (Fintype.card D.what₂.Tau : ℝ) * (V.rank * (V.rank * (C * (b + 1) + C * (b + 1))))
      ≤ (Fintype.card D.what₂.Tau : ℝ) * (V.rank * (V.rank * (4 * C * b))) := by gcongr
    _ = _ := by ring

theorem slice_regular : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V V' : HSp D) (ι : V'.V →ₗ[D.host.E] V.V), HSpace.IsIsomEmb V' V ι → ∀ s : GA D V' →* GA D V, (∀ h, EmbRel V V' ι (s h) h) → ∀ (Γ : Set (GA D V)) (ψ : GA D V → ℂ), IsSmModOn D.sp.cm.sig V.gram Γ ψ → ∀ y : GA D V, (∀ h, s h * y = y * s h) → (∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V'.rank) (Fin V'.rank) ℂ), (∀ i, Xs i ∈ lieAt V' (τs i)) → ∀ g, ContDiff ℝ ∞ fun t : Fin k → ℝ => ψ (s (g * (List.ofFn fun i => oneP θ V' (τs i) (Xs i) (t i)).prod) * y)) ∧ ∃ N : ℕ, ∀ l : List (D.what₂.Tau × Matrix (Fin V'.rank) (Fin V'.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V' p.1) → ∀ x, ∃ C : ℝ, ∀ g ∈ GinfC V', ‖(l.foldr (fun p f => Rder θ V' p.1 p.2 f) (fun h => ψ (s h * y))) (x * g)‖ ≤ C * normInf θ V' g ^ N := by
  intro D θ hθ V V' ι hι s hs Γ ψ hψ y hy
  refine ⟨fun k τs Xs hX g => ?_, ?_⟩
  · choose Z hZ e using fun i => exists_lie_oneP hθ hι hs (τs i) (hX i)
    have key := hψ.smooth k (fun i => oneP θ V (τs i) (Z i))
      (fun i => GlobalTheory.SphSmooth.isRealLine_oneP hθ V (hZ i)) (s g * y)
    have e2 : (fun t : Fin k → ℝ => ψ (s (g * (List.ofFn fun i => oneP θ V' (τs i) (Xs i) (t i)).prod) * y)) =
        fun t => ψ (s g * y * (List.ofFn fun i => oneP θ V (τs i) (Z i) (t i)).prod) := by
      funext t
      have e3 : s (List.ofFn fun i => oneP θ V' (τs i) (Xs i) (t i)).prod =
          (List.ofFn fun i => oneP θ V (τs i) (Z i) (t i)).prod := by
        rw [map_list_prod, List.map_ofFn]
        congr 2
        funext i
        exact e i (t i)
      rw [map_mul, mul_assoc, hy, ← mul_assoc, e3]
    rw [e2]
    exact key
  · obtain ⟨N, hN⟩ := hψ.growth
    rcases Nat.eq_zero_or_pos V'.rank with hV | hV
    · refine ⟨0, fun l _ x => ⟨‖(l.foldr (fun p f => Rder θ V' p.1 p.2 f) (fun h => ψ (s h * y))) x‖, fun g _ => ?_⟩⟩
      have hg1 : g = 1 := Subtype.ext (Units.ext (Matrix.ext fun i j => absurd i.2 (by omega)))
      rw [hg1]
      simp
    · obtain ⟨d, hd⟩ := GlobalTheory.Grow.height_le_normInf_pow (θ := θ) V hθ
      obtain ⟨K, hK0, hK⟩ := normInf_s_le θ hι hs hV
      refine ⟨d * N, fun l hl x => ?_⟩
      obtain ⟨l', h1, h2⟩ := foldr_Rder_eq hθ hι hs hy ψ l hl
      obtain ⟨C, hC⟩ := hN l' h1
      refine ⟨|C| * (GlobalTheory.Grow.height V (s x * y) * K ^ d) ^ N, fun g hg => ?_⟩
      have hn : 1 ≤ normInf θ V' g := GlobalTheory.RatCount.one_le_normInf θ hV g
      have hsg := Formalism.IndefR.Mi.s_mem_GinfC hι hs hg
      have hnn : 0 ≤ normInf θ V (s g) := by unfold Formalism.L2.Theta.normInf; positivity
      have b1 : GlobalTheory.Grow.height V (s g) ≤ (K * normInf θ V' g) ^ d :=
        (hd _ hsg).trans (pow_le_pow_left₀ hnn (hK g) d)
      have b2 : GlobalTheory.Grow.height V (s (x * g) * y) ≤ GlobalTheory.Grow.height V (s x * y) * (K * normInf θ V' g) ^ d := by
        have e : s (x * g) * y = s x * y * s g := by rw [map_mul, mul_assoc, hy, ← mul_assoc]
        rw [e]
        exact (GlobalTheory.Grow.height_mul_le V _ _).trans
          (mul_le_mul_of_nonneg_left b1 (GlobalTheory.Grow.height_pos V _).le)
      have h0 : 0 ≤ GlobalTheory.Grow.height V (s (x * g) * y) := (GlobalTheory.Grow.height_pos V _).le
      rw [h2]
      calc _ ≤ C * GlobalTheory.Grow.height V (s (x * g) * y) ^ N := hC _
        _ ≤ |C| * GlobalTheory.Grow.height V (s (x * g) * y) ^ N :=
            mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg h0 N)
        _ ≤ |C| * (GlobalTheory.Grow.height V (s x * y) * (K * normInf θ V' g) ^ d) ^ N :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 b2 N) (abs_nonneg C)
        _ = |C| * (GlobalTheory.Grow.height V (s x * y) * K ^ d) ^ N * normInf θ V' g ^ (d * N) := by
            rw [pow_mul, mul_pow K]
            ring

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.SliceReg
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.SmoothAutomorphicDerivativeGrowthStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_term_restrict_smooth_moderate : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V V' : HSp D) (ι : V'.V →ₗ[D.host.E] V.V), HSpace.IsIsomEmb V' V ι → ∀ s : GA D V' →* GA D V, (∀ h, EmbRel V V' ι (s h) h) → ∀ (Γ : Set (GA D V)) (ψ : GA D V → ℂ), IsSmModOn D.sp.cm.sig V.gram Γ ψ → ∀ y : GA D V, (∀ h, s h * y = y * s h) → (∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V'.rank) (Fin V'.rank) ℂ), (∀ i, Xs i ∈ lieAt V' (τs i)) → ∀ g, ContDiff ℝ ∞ fun t : Fin k → ℝ => ψ (s (g * (List.ofFn fun i => oneP θ V' (τs i) (Xs i) (t i)).prod) * y)) ∧ ∃ N : ℕ, ∀ l : List (D.what₂.Tau × Matrix (Fin V'.rank) (Fin V'.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V' p.1) → ∀ x, ∃ C : ℝ, ∀ g ∈ GinfC V', ‖(l.foldr (fun p f => Rder θ V' p.1 p.2 f) (fun h => ψ (s h * y))) (x * g)‖ ≤ C * normInf θ V' g ^ N := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.SliceReg.slice_regular | exact GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.SliceReg.slice_regular | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.SliceReg.slice_regular <;> assumption)
end
end
