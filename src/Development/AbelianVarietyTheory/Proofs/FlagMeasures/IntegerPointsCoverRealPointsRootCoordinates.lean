module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeUnipotentIntegralNormalisedHaar

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalLinkConjugateMemIntegralRealPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalLinkConjugateMemIntegralRealPoints
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Matrix

namespace GlobalTheory.CoverAct

theorem ratLink_mem_ROinf : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (W : WittDat X) (u u' : D.what₂.Word) (s : TT Y u u') (n : (VS D).V ≃ₗ[D.host.E] (VS D).V), n ∈ NLam (Formalism.HermitianLatticesTheory.gmap (W.δ u) s.lam) (lf D (FlagOfWord W u)) ∩ NLam (Formalism.HermitianLatticesTheory.gmap (W.δ u) s.lam) (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame) → ∃ x : X.B.I.GA, Formalism.L2.SG.TermOp.RatLink X x ((W.δ u)⁻¹ * n * W.δ u) ∧ x.1 ∈ Formalism.L2.SG.TermOp.ROinf s := by
  intro D X Y W u u' s n hn
  obtain ⟨h1, h2⟩ := hn
  have hδ := W.isom u
  have hm1 : (W.δ u)⁻¹ * n * W.δ u ∈ NLam s.lam (lf D (X.Fu u)) := by
    rw [← Formalism.L2.SG.TermTieOf.mapL_lf W u] at h1
    exact (Formalism.L2.SG.Pf.mem_NLam_map (W.δ u) hδ _ _ _).1 h1
  have hm2 : (W.δ u)⁻¹ * n * W.δ u ∈ NLam s.lam s.frame :=
    (Formalism.L2.SG.Pf.mem_NLam_map (W.δ u) hδ _ _ _).1 h2
  have hiso : (W.δ u)⁻¹ * n * W.δ u ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT :=
    mul_mem (mul_mem (inv_mem hδ) h1.1.1) hδ
  have hlin : s.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := s.rep.2.2.1
  have hlam : Formalism.HermitianLatticesTheory.gmap s.lin s.lam' = s.lam := s.rep.2.2.2.1
  have hfr : s.frame = Formalism.L2.SG.Saturated.mapL s.lin hlin (lf D (X.Fu u')) := by
    unfold Formalism.L2.SG.TermOp.GTerm.frame Formalism.L2.SG.TermOp.mapLF
    rw [dite_eq_left hlin]
    rfl
  rw [hfr, ← hlam] at hm2
  have hm3 := (Formalism.L2.SG.Pf.mem_NLam_map s.lin hlin _ _ _).1 hm2
  obtain ⟨x, hx⟩ := Formalism.L2.SG.Pf.ratPt_holds D X _ hiso
  exact ⟨x, hx, x, _, hx, rfl, hm1, hm3⟩

end GlobalTheory.CoverAct
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalLinkConjugateMemIntegralRealPointsStatement
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalLink_conjugate_mem_integralRealPoints : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (W : WittDat X) (u u' : D.what₂.Word) (s : TT Y u u') (n : (VS D).V ≃ₗ[D.host.E] (VS D).V), n ∈ NLam (Formalism.HermitianLatticesTheory.gmap (W.δ u) s.lam) (lf D (FlagOfWord W u)) ∩ NLam (Formalism.HermitianLatticesTheory.gmap (W.δ u) s.lam) (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame) → ∃ x : X.B.I.GA, Formalism.L2.SG.TermOp.RatLink X x ((W.δ u)⁻¹ * n * W.δ u) ∧ x.1 ∈ Formalism.L2.SG.TermOp.ROinf s := by
  first | exact @GlobalTheory.CoverAct.ratLink_mem_ROinf | exact GlobalTheory.CoverAct.ratLink_mem_ROinf | (intros; apply GlobalTheory.CoverAct.ratLink_mem_ROinf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalFrameGramEmbedEqRealFrameGram
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalFrameGramEmbedEqRealFrameGram
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Matrix

namespace GlobalTheory.ZhatRat

theorem mapFlag_fvec {D : D7} {r : ℕ} {T : D.host.E} (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (h : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (F : FlagG (VS D) r T) (b : Fin (r + 1)) :
    (Formalism.L2.SG.TermOp.mapFlag γ h F).fvec b = γ (F.fvec b) := by
  refine Fin.lastCases ?_ (fun b' => ?_) b
  · simp only [FlagG.fvec, Fin.snoc_last, Formalism.L2.SG.TermOp.mapFlag]
  · simp only [FlagG.fvec, Fin.snoc_castSucc, Formalism.L2.SG.TermOp.mapFlag]

theorem frm_one {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (v : NumberField.InfinitePlace X.B.I.F)
    (a : Fin (D.R.rS + 1)) :
    Formalism.L2.SG.RealObj.frm X u 1 v a = rv X.B.I v (X.crd ((X.Fu u).fvec a)) := by
  unfold Formalism.L2.SG.RealObj.frm Formalism.L2.SG.RealObj.famSc Formalism.L2.SG.RealObj.fam
  rw [Complex.ofReal_one, one_pow, inv_one, one_smul]
  refine Fin.lastCases ?_ (fun a' => ?_) a
  · rw [Fin.snoc_last, FlagG.fvec, Fin.snoc_last, X.flagZVector u]
    rfl
  · rw [Fin.snoc_castSucc, FlagG.fvec, Fin.snoc_castSucc, X.Fu_e u]
    rfl

end GlobalTheory.ZhatRat


open GlobalTheory.ZhatRat in
theorem GlobalTheory.zhatRat_embed : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (W : WittDat X) (u u' : D.what₂.Word) (s : TT Y u u') (τ : D.what₂.Tau), (ZhatL (lf D (FlagOfWord W u)) (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame)).map (embS D τ) = Formalism.L2.SG.RealObj.ZX X u u' 1 s.pt.1 (X.pl.symm τ) := by
  intro D X Y W u u' s τ
  obtain ⟨M, _, hM1, _, hM3⟩ := s.rep.2.1
  have hiso : s.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := s.rep.2.2.1
  rw [← mapL_lf W u]
  refine (congrArg (fun Z => Matrix.map Z (embS D τ)) (zhatL_mapL (W.δ u) (W.isom u) (lf D (X.Fu u)) s.frame)).trans ?_
  ext a b
  simp only [Matrix.map_apply]
  have hM1' : ∀ v, uMat (s.pt.1 v) = (X.B.I.P v)⁻¹ * (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map ⇑(X.B.I.φ v) * X.B.I.P v := hM1
  have hM3' : ∀ y, X.crd (s.lin y) = (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ X.crd y := hM3
  have hL : (s.frame).fl.fvec b = s.lin ((X.Fu u').fvec b) := by
    unfold Formalism.L2.SG.TermOp.GTerm.frame Formalism.L2.SG.TermOp.mapLF
    rw [dite_eq_left hiso]
    exact mapFlag_fvec _ hiso _ _
  change embS D τ (brS (VS D) (s.frame.fl.fvec b) ((X.Fu u).fvec a)) = _
  rw [hL]
  unfold brS Formalism.L2.SG.RealObj.ZX Formalism.L2.SG.RealObj.Zhat
  rw [frm_one, frm_one, hM1', Formalism.L2.SG.Pf.Level.rv_mulVec, ← hM3', Formalism.L2.SG.Pf.Level.hJ_rv, X.φ_eq,
    X.pl.apply_symm_apply, Formalism.L2.SG.PoincareInHH.Cut.hform_crd]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalFrameGramEmbedEqRealFrameGramStatement
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalFrameGram_embed_eq_realFrameGram : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (W : WittDat X) (u u' : D.what₂.Word) (s : TT Y u u') (τ : D.what₂.Tau), (ZhatL (lf D (FlagOfWord W u)) (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame)).map (embS D τ) = Formalism.L2.SG.RealObj.ZX X u u' 1 s.pt.1 (X.pl.symm τ) := by
  first | exact @GlobalTheory.zhatRat_embed | exact GlobalTheory.zhatRat_embed | (intros; apply GlobalTheory.zhatRat_embed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPointRationalIsometryActsFrameMatrix
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPointRationalIsometryActsFrameMatrix
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Matrix

noncomputable section

namespace GlobalTheory.ActQ

theorem snoc_map {α β : Type*} {r : ℕ} (f : α → β) (e : Fin r → α) (z : α) (j : Fin (r + 1)) :
    f (Fin.snoc (α := fun _ => α) e z j) = Fin.snoc (α := fun _ => β) (fun a => f (e a)) (f z) j := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [Fin.snoc_last]
  · simp only [Fin.snoc_castSucc]

end GlobalTheory.ActQ

theorem GlobalTheory.realPoint_ratIsom_isMatOn : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (s : TT Y u u') (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (x : X.B.I.GA) (A : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E), Formalism.L2.SG.TermOp.RatLink X x n → (∀ j, n (frame s.frame j) = ∑ i, A i j • frame s.frame i) → ∀ v : NumberField.InfinitePlace X.B.I.F, GlobalTheory.LoopAct.IsMatOn (uMat (x.1 v)) (fun j => uMat (s.pt.1 v) *ᵥ Formalism.L2.SG.RealObj.frm X u' 1 v j) (A.map (embS D (X.pl v))) := by
  intro D X Y u u' s n x A hR hA v
  obtain ⟨M, -, hM1, -, hM3⟩ := hR
  obtain ⟨M', -, hM1', -, hM3'⟩ := s.rep.2.1
  have hP' : ∀ v, uMat (s.pt.1 v) = (X.B.I.P v)⁻¹ * (↑M' : Matrix _ _ _).map ⇑(X.B.I.φ v) * X.B.I.P v := hM1'
  have hL' : ∀ y, X.crd (s.lin y) = (↑M' : Matrix _ _ _) *ᵥ X.crd y := hM3'
  have hiso : s.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := s.rep.2.2.1
  have hfr : ∀ j, frame s.frame j = s.lin (Fin.snoc (α := fun _ => (VS D).V) X.eX (X.zu u') j) := by
    intro j
    have e1 : s.frame = Formalism.L2.SG.TermOp.mapLF s.lin (lf D (X.Fu u')) := rfl
    rw [e1]
    unfold Formalism.L2.SG.TermOp.mapLF
    rw [dite_eq_left hiso]
    rw [GlobalTheory.ActQ.snoc_map (f := (s.lin : (VS D).V → (VS D).V)), ← X.Fu_e u', ← X.flagZVector u']
    rfl
  have hfrm : ∀ j, Formalism.L2.SG.RealObj.frm X u' 1 v j =
      rv X.B.I v (X.crd (Fin.snoc (α := fun _ => (VS D).V) X.eX (X.zu u') j)) := by
    intro j
    unfold Formalism.L2.SG.RealObj.frm Formalism.L2.SG.RealObj.famSc Formalism.L2.SG.RealObj.fam
    simp only [Complex.ofReal_one, one_pow, inv_one, one_smul]
    rw [GlobalTheory.ActQ.snoc_map (f := fun y => rv X.B.I v (X.crd y))]
    rfl
  have hf : ∀ j, uMat (s.pt.1 v) *ᵥ Formalism.L2.SG.RealObj.frm X u' 1 v j = rv X.B.I v (X.crd (frame s.frame j)) := by
    intro j
    rw [hfrm, hfr, hL', ← Formalism.L2.SG.Pf.Level.rv_mulVec X v, ← hP' v]
  have hsum : ∀ (c : Fin (D.R.rS + 1) → D.host.E) (w : Fin (D.R.rS + 1) → (VS D).V),
      rv X.B.I v (X.crd (∑ i, c i • w i)) = ∑ i, embS D (X.pl v) (c i) • rv X.B.I v (X.crd (w i)) := by
    intro c w
    have hc : X.crd (∑ i, c i • w i) = ∑ i, X.ιE.symm (c i) • X.crd (w i) := by
      funext l
      set_option synthInstance.maxHeartbeats 100000 in
        simp [HidaSetting.crd, Formalism.L2.SG.HidaSetting.crdOf, map_sum, Finset.sum_apply, smul_eq_mul]
    rw [hc]
    unfold rv
    have hv : (fun l => X.B.I.φ v ((∑ i, X.ιE.symm (c i) • X.crd (w i)) l)) =
        ∑ i, embS D (X.pl v) (c i) • fun l => X.B.I.φ v (X.crd (w i) l) := by
      funext l
      set_option synthInstance.maxHeartbeats 100000 in
        simp [Finset.sum_apply, map_sum, X.φ_eq]
    rw [hv, Matrix.mulVec_sum]
    simp_rw [Matrix.mulVec_smul]
  intro b
  dsimp only
  rw [hf b, hM1 v, Formalism.L2.SG.Pf.Level.rv_mulVec, ← hM3, hA b, hsum]
  simp_rw [hf, Matrix.map_apply]

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPointRationalIsometryActsFrameMatrixStatement
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realPoint_rationalIsometry_acts_frame_matrix : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (s : TT Y u u') (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (x : X.B.I.GA) (A : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E), Formalism.L2.SG.TermOp.RatLink X x n → (∀ j, n (frame s.frame j) = ∑ i, A i j • frame s.frame i) → ∀ v : NumberField.InfinitePlace X.B.I.F, GlobalTheory.LoopAct.IsMatOn (uMat (x.1 v)) (fun j => uMat (s.pt.1 v) *ᵥ Formalism.L2.SG.RealObj.frm X u' 1 v j) (A.map (embS D (X.pl v))) := by
  first | exact @GlobalTheory.realPoint_ratIsom_isMatOn | exact GlobalTheory.realPoint_ratIsom_isMatOn | (intros; apply GlobalTheory.realPoint_ratIsom_isMatOn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameMatrixMemUnipotentStabilizerFrameGram
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameMatrixMemUnipotentStabilizerFrameGram
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Matrix

noncomputable section

open scoped Classical

namespace GlobalTheory.FrameStab

open Formalism.L2.SG.RealObj

variable {n m r : ℕ}

def colMat (f : Fin m → Fin n → ℂ) : Matrix (Fin n) (Fin m) ℂ := Matrix.of fun i a => f a i

theorem isMatOn_iff (g : Matrix (Fin n) (Fin n) ℂ) (f : Fin m → Fin n → ℂ) (M : Matrix (Fin m) (Fin m) ℂ) :
    GlobalTheory.LoopAct.IsMatOn g f M ↔ g * colMat f = colMat f * M := by
  constructor
  · intro h
    ext i b
    have := congrFun (h b) i
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    simp only [Matrix.mul_apply, colMat, Matrix.of_apply, this, mul_comm]
  · intro h b
    ext i
    have := congrFun (congrFun h i) b
    simp only [Matrix.mul_apply, colMat, Matrix.of_apply] at this
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, this, mul_comm]

theorem zhat_eq (ε : Fin n → Bool) (f f' : Fin (r + 1) → Fin n → ℂ) (G : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.L2.SG.RealObj.Zhat ε f f' G = (colMat f)ᴴ * Formalism.REAL.Jm ε * G * colMat f' := by
  rw [Matrix.mul_assoc, Matrix.mul_assoc]
  ext a b
  simp only [Formalism.L2.SG.RealObj.Zhat, Formalism.L2.SG.HidaSetting.hJ, Matrix.mul_apply, Matrix.mulVec, dotProduct, colMat,
    Matrix.of_apply, Matrix.conjTranspose_apply, Pi.star_apply]

theorem conjTranspose_mul_zhat_mul {ε : Fin n → Bool} {f f' : Fin (r + 1) → Fin n → ℂ}
    {Y G Gi : Matrix (Fin n) (Fin n) ℂ} {P M : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ}
    (hY : Yᴴ * Formalism.REAL.Jm ε * Y = Formalism.REAL.Jm ε) (hG : G * Gi = 1)
    (hP : GlobalTheory.LoopAct.IsMatOn Y f P) (hM : GlobalTheory.LoopAct.IsMatOn (Gi * Y * G) f' M) :
    Pᴴ * (Formalism.L2.SG.RealObj.Zhat ε f f' G * M) = Formalism.L2.SG.RealObj.Zhat ε f f' G := by
  rw [isMatOn_iff] at hP hM
  rw [zhat_eq]
  calc Pᴴ * ((colMat f)ᴴ * Formalism.REAL.Jm ε * G * colMat f' * M)
      = (colMat f * P)ᴴ * Formalism.REAL.Jm ε * G * (colMat f' * M) := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = (Y * colMat f)ᴴ * Formalism.REAL.Jm ε * G * (Gi * Y * G * colMat f') := by rw [hP, hM]
    _ = (colMat f)ᴴ * (Yᴴ * Formalism.REAL.Jm ε * ((G * Gi) * Y)) * G * colMat f' := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = (colMat f)ᴴ * Formalism.REAL.Jm ε * G * colMat f' := by
        rw [hG, Matrix.one_mul, hY]

theorem isLoUni_conjTranspose {N : ℕ} {P : Matrix (Fin N) (Fin N) ℂ} (h : Formalism.MainNotions.S.IsUpUni P) :
    Formalism.MainNotions.S.IsLoUni Pᴴ := by
  intro i j
  refine ⟨fun hij => ?_, fun hij => ?_⟩
  · rw [Matrix.conjTranspose_apply, (h j i).1 hij, star_zero]
  · rw [Matrix.conjTranspose_apply, (h j i).2 hij.symm, star_one]

theorem mem_stabU_of_conjTranspose_mul {N : ℕ} {Z P M : Matrix (Fin N) (Fin N) ℂ} (hZ : IsUnit Z.det)
    (hP : Formalism.MainNotions.S.IsUpUni P) (hM : Formalism.MainNotions.S.IsUpUni M) (h : Pᴴ * (Z * M) = Z) :
    M ∈ GlobalTheory.LoopV.stabU Z := by
  refine ⟨hM, ?_⟩
  have e : Pᴴ * (Z * M * Z⁻¹) = 1 := by
    rw [← Matrix.mul_assoc, h, Matrix.mul_nonsing_inv _ hZ]
  rw [← Matrix.inv_eq_right_inv e]
  exact (Formalism.L2.SG.Pf.ZsVolGrp.isLoUni_inv (isLoUni_conjTranspose hP)).1

end GlobalTheory.FrameStab

namespace GlobalTheory.FrameStab

variable {n r : ℕ}

theorem exists_coeff_of_mem_spanLt {e : Fin r → Fin n → ℂ} {k : ℕ} {x : Fin n → ℂ}
    (hx : x ∈ Formalism.L2.SG.HidaSetting.spanLt e k) :
    ∃ c : Fin r → ℂ, (∀ b : Fin r, ¬ b.1 < k → c b = 0) ∧ x = ∑ b, c b • e b := by
  obtain ⟨l, hl, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination ℂ).1 hx
  refine ⟨l, fun b hb => ?_, ?_⟩
  · exact (Finsupp.mem_supported' ℂ l).1 hl b hb
  · rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    intro i; exact zero_smul _ _

theorem exists_isUpUni_isMatOn {e : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {Y : Matrix (Fin n) (Fin n) ℂ}
    (h : Formalism.L2.SG.HidaSetting.InS e z Y) :
    ∃ P : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ, Formalism.MainNotions.S.IsUpUni P ∧
      GlobalTheory.LoopAct.IsMatOn Y (Formalism.L2.SG.RealObj.fam e z) P := by
  choose ca hca0 hcae using fun a : Fin r => exists_coeff_of_mem_spanLt (h.1 a)
  obtain ⟨cz, -, hcz⟩ := exists_coeff_of_mem_spanLt h.2
  let Q : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ := fun i j =>
    Fin.lastCases (motive := fun _ => ℂ) 0
      (fun c : Fin r => Fin.lastCases (motive := fun _ => ℂ) (cz c) (fun a : Fin r => ca a c) j) i
  have hQl : ∀ j, Q (Fin.last r) j = 0 := fun j => by simp [Q]
  have hQcl : ∀ c, Q (Fin.castSucc c) (Fin.last r) = cz c := fun c => by simp [Q]
  have hQcc : ∀ c a, Q (Fin.castSucc c) (Fin.castSucc a) = ca a c := fun c a => by simp [Q]
  refine ⟨1 + Q, fun i j => ?_, fun b => ?_⟩
  · refine Fin.lastCases ?_ (fun c => ?_) i
    · refine ⟨fun hj => ?_, fun hj => ?_⟩
      · rw [Matrix.add_apply, hQl, Matrix.one_apply_ne (ne_of_lt hj).symm, add_zero]
      · rw [Matrix.add_apply, hQl, hj, Matrix.one_apply_eq, add_zero]
    · refine Fin.lastCases ?_ (fun a => ?_) j
      · exact ⟨fun hj => absurd hj (not_lt.2 (Fin.castSucc_lt_last c).le),
          fun hj => absurd hj (Fin.castSucc_lt_last c).ne⟩
      · refine ⟨fun hj => ?_, fun hj => ?_⟩
        · rw [Matrix.add_apply, hQcc, Matrix.one_apply_ne (ne_of_lt hj).symm, zero_add]
          exact hca0 a c (not_lt.2 (Fin.castSucc_lt_castSucc_iff.1 hj).le)
        · rw [Matrix.add_apply, hQcc, hj, Matrix.one_apply_eq, Fin.castSucc_inj.1 hj]
          rw [hca0 a a (lt_irrefl _), add_zero]
  · rw [Fin.sum_univ_castSucc]
    simp only [Formalism.L2.SG.RealObj.fam, Fin.snoc_castSucc, Fin.snoc_last, Matrix.add_apply, add_smul,
      Finset.sum_add_distrib, hQl, zero_smul, add_zero]
    refine Fin.lastCases ?_ (fun a => ?_) b
    · simp only [Fin.snoc_last, hQcl, Matrix.one_apply_eq, one_smul,
        Matrix.one_apply_ne (Fin.castSucc_lt_last _).ne, zero_smul, Finset.sum_const_zero, zero_add]
      rw [← hcz, Matrix.sub_mulVec, Matrix.one_mulVec, sub_add_cancel]
    · simp only [Fin.snoc_castSucc, hQcc, Matrix.one_apply_ne (Fin.castSucc_lt_last _).ne', zero_smul,
        add_zero]
      have e1 : ∑ x : Fin r, (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (Fin.castSucc x) (Fin.castSucc a) • e x
          = e a := by
        simp only [Matrix.one_apply, Fin.castSucc_inj, ite_smul, one_smul, zero_smul,
          Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [e1, ← hcae a, Matrix.sub_mulVec, Matrix.one_mulVec, add_sub_cancel]

end GlobalTheory.FrameStab

namespace GlobalTheory.FrameStab

theorem frameMat_mem_stabU : ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word) (γ y : X.B.I.Ginf) (v : NumberField.InfinitePlace X.B.I.F) (M : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ), y ∈ Formalism.L2.SG.RealObj.StInf X u u' γ → IsUpUni M → GlobalTheory.LoopAct.IsMatOn (uMat ((γ⁻¹ * y * γ) v)) (Formalism.L2.SG.RealObj.frm X u' 1 v) M → IsUnit (Formalism.L2.SG.RealObj.ZX X u u' 1 γ v).det → M ∈ GlobalTheory.LoopV.stabU (Formalism.L2.SG.RealObj.ZX X u u' 1 γ v) := by
  intro D X u u' γ y v M hy hMu hM hZ
  obtain ⟨P, hPu, hP⟩ := exists_isUpUni_isMatOn ((hy.1 v).1)
  have hf : Formalism.L2.SG.RealObj.frm X u 1 v = Formalism.L2.SG.RealObj.fam
      (fun a => Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR a)) (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u)) := by
    funext a
    simp [Formalism.L2.SG.RealObj.frm, Formalism.L2.SG.RealObj.famSc]
  rw [← hf] at hP
  have hY : (uMat (y v))ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * uMat (y v) = Formalism.REAL.Jm (X.B.I.ε v) := (y v).2
  have hG : uMat (γ v) * uMat (γ⁻¹ v) = 1 := by
    show uMat ((γ * γ⁻¹) v) = 1
    rw [mul_inv_cancel]
    rfl
  exact mem_stabU_of_conjTranspose_mul hZ hPu hMu (conjTranspose_mul_zhat_mul hY hG hP hM)

end GlobalTheory.FrameStab

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameMatrixMemUnipotentStabilizerFrameGramStatement
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameMatrix_mem_unipotentStabilizer_frameGram : ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word) (γ y : X.B.I.Ginf) (v : NumberField.InfinitePlace X.B.I.F) (M : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ), y ∈ Formalism.L2.SG.RealObj.StInf X u u' γ → IsUpUni M → GlobalTheory.LoopAct.IsMatOn (uMat ((γ⁻¹ * y * γ) v)) (Formalism.L2.SG.RealObj.frm X u' 1 v) M → IsUnit (Formalism.L2.SG.RealObj.ZX X u u' 1 γ v).det → M ∈ GlobalTheory.LoopV.stabU (Formalism.L2.SG.RealObj.ZX X u u' 1 γ v) := by
  first | exact @GlobalTheory.FrameStab.frameMat_mem_stabU | exact GlobalTheory.FrameStab.frameMat_mem_stabU | (intros; apply GlobalTheory.FrameStab.frameMat_mem_stabU <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameGramMulEqConjTransposeMulFrameMatrices
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GxDoubleCoset
open scoped Classical ComplexConjugate ENNReal
open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj

noncomputable section

namespace GlobalTheory.GxConj

variable {r n : ℕ}

theorem hJ_adj (ε : Fin n → Bool) (A Ai : Matrix (Fin n) (Fin n) ℂ)
    (hU : Aiᴴ * Formalism.REAL.Jm ε * Ai = Formalism.REAL.Jm ε) (h1 : Ai * A = 1) (x y : Fin n → ℂ) :
    hJ ε x (A *ᵥ y) = hJ ε (Ai *ᵥ x) y := by
  have e : Aiᴴ * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * A := by
    calc Aiᴴ * Formalism.REAL.Jm ε = Aiᴴ * Formalism.REAL.Jm ε * (Ai * A) := by rw [h1, Matrix.mul_one]
      _ = (Aiᴴ * Formalism.REAL.Jm ε * Ai) * A := by simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε * A := by rw [hU]
  have e2 : Aiᴴ *ᵥ (Formalism.REAL.Jm ε *ᵥ y) = Formalism.REAL.Jm ε *ᵥ (A *ᵥ y) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, e]
  unfold hJ
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, e2]

theorem hJ_sum_left {ι : Type*} [Fintype ι] (ε : Fin n → Bool) (s : ι → ℂ) (x : ι → Fin n → ℂ) (y : Fin n → ℂ) :
    hJ ε (∑ c, s c • x c) y = ∑ c, conj (s c) * hJ ε (x c) y := by
  unfold hJ
  simp only [star_sum, star_smul, sum_dotProduct, smul_dotProduct, smul_eq_mul, Complex.star_def]

theorem hJ_sum_right {ι : Type*} [Fintype ι] (ε : Fin n → Bool) (s : ι → ℂ) (x : Fin n → ℂ) (y : ι → Fin n → ℂ) :
    hJ ε x (∑ c, s c • y c) = ∑ c, s c * hJ ε x (y c) := by
  unfold hJ
  simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul, smul_eq_mul]

theorem mulVec_lin {ι : Type*} [Fintype ι] (B : Matrix (Fin n) (Fin n) ℂ) (s : ι → ℂ) (y : ι → Fin n → ℂ) :
    B *ᵥ ∑ c, s c • y c = ∑ c, s c • (B *ᵥ y c) := by
  simp only [Matrix.mulVec_sum, Matrix.mulVec_smul]

theorem zhat_conj (ε : Fin n → Bool) (f f' : Fin (r + 1) → Fin n → ℂ) (A Ai B C : Matrix (Fin n) (Fin n) ℂ)
    (hadj : ∀ x y, hJ ε x (A *ᵥ y) = hJ ε (Ai *ᵥ x) y) (L M : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (hL : ∀ a, Ai *ᵥ f a = ∑ c, L a c • f c) (hM : ∀ b, C *ᵥ f' b = ∑ d, M b d • f' d) :
    Zhat ε f f' (A * B * C) = L.map (starRingEnd ℂ) * Zhat ε f f' B * Mᵀ := by
  ext a b
  have e1 : (A * B * C) *ᵥ f' b = A *ᵥ (B *ᵥ (C *ᵥ f' b)) := by
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  simp only [Formalism.L2.SG.RealObj.Zhat, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply]
  rw [e1, hadj, hL, hM, mulVec_lin, hJ_sum_left]
  simp only [hJ_sum_right, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => ?_
  ring

end GlobalTheory.GxConj

namespace GlobalTheory

open GlobalTheory.GxConj

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameGramMulEqConjTransposeMulFrameMatrices
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Matrix

noncomputable section

namespace GlobalTheory.ZxMul

theorem zx_mul : ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word) (g γ h : X.B.I.Ginf) (v : NumberField.InfinitePlace X.B.I.F) (C B : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ), GlobalTheory.LoopAct.IsMatOn (uMat (g⁻¹ v)) (Formalism.L2.SG.RealObj.frm X u 1 v) C → GlobalTheory.LoopAct.IsMatOn (uMat (h v)) (Formalism.L2.SG.RealObj.frm X u' 1 v) B → Formalism.L2.SG.RealObj.ZX X u u' 1 (g * γ * h) v = Cᴴ * Formalism.L2.SG.RealObj.ZX X u u' 1 γ v * B := by
  intro D X u u' g γ h v C B hC hB
  have hU : (uMat (g⁻¹ v))ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * uMat (g⁻¹ v) = Formalism.REAL.Jm (X.B.I.ε v) := (g⁻¹ v).2
  have e : uMat ((g * γ * h) v) = uMat (g v) * uMat (γ v) * uMat (h v) := rfl
  have hL : ∀ a, uMat (g⁻¹ v) *ᵥ Formalism.L2.SG.RealObj.frm X u 1 v a =
      ∑ c, Cᵀ a c • Formalism.L2.SG.RealObj.frm X u 1 v c := fun a => by
    rw [hC a]; rfl
  have hM : ∀ b, uMat (h v) *ᵥ Formalism.L2.SG.RealObj.frm X u' 1 v b =
      ∑ d, Bᵀ b d • Formalism.L2.SG.RealObj.frm X u' 1 v d := fun b => by
    rw [hB b]; rfl
  unfold Formalism.L2.SG.RealObj.ZX
  rw [e, GlobalTheory.GxConj.zhat_conj _ _ _ _ _ _ _
    (GlobalTheory.GxConj.hJ_adj _ _ _ hU (Formalism.L2.SG.RealObj.InfCut.uMat_inv_mul' (g v))) _ _ hL hM,
    Matrix.transpose_transpose]
  rfl

end GlobalTheory.ZxMul
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameGramMulEqConjTransposeMulFrameMatricesStatement
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameGram_mul_eq_conjTranspose_mul_frameMatrices : ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word) (g γ h : X.B.I.Ginf) (v : NumberField.InfinitePlace X.B.I.F) (C B : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ), GlobalTheory.LoopAct.IsMatOn (uMat (g⁻¹ v)) (Formalism.L2.SG.RealObj.frm X u 1 v) C → GlobalTheory.LoopAct.IsMatOn (uMat (h v)) (Formalism.L2.SG.RealObj.frm X u' 1 v) B → Formalism.L2.SG.RealObj.ZX X u u' 1 (g * γ * h) v = Cᴴ * Formalism.L2.SG.RealObj.ZX X u u' 1 γ v * B := by
  first | exact @GlobalTheory.ZxMul.zx_mul | exact GlobalTheory.ZxMul.zx_mul | (intros; apply GlobalTheory.ZxMul.zx_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalBesselFrameRealPlaceLinearIndependent
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalBesselFrameRealPlaceLinearIndependent
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Matrix

namespace GlobalTheory.RationalFrame

open NumberField Formalism.L2.SG.PoincareInHH

theorem hJ_lin {n : ℕ} (ε : Fin n → Bool) {ι : Type*} [Fintype ι] (x : Fin n → ℂ) (g : ι → ℂ)
    (y : ι → Fin n → ℂ) (c : ℂ) (w : Fin n → ℂ) :
    hJ ε x (∑ i, g i • y i + c • w) = ∑ i, g i * hJ ε x (y i) + c * hJ ε x w := by
  unfold hJ
  simp only [mulVec_add, mulVec_sum, mulVec_smul, dotProduct_add, dotProduct_sum, dotProduct_smul, smul_eq_mul]

theorem frame_linearIndependent (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) :
    LinearIndependent ℂ (Formalism.L2.SG.RealObj.frm X u 1 v) := by
  have hfr : Formalism.L2.SG.RealObj.frm X u 1 v = Formalism.L2.SG.RealObj.fam (fun a => rv X.B.I v (X.eR a))
      (rv X.B.I v (X.zR u)) := by
    funext a
    simp [Formalism.L2.SG.RealObj.frm, Formalism.L2.SG.RealObj.famSc]
  have hze : ∀ a, hJ (X.B.I.ε v) (rv X.B.I v (X.zR u)) (rv X.B.I v (X.eR a)) = 0 := by
    intro a
    refine (Cut.hJ_crd X v _ _).trans ?_
    have h := (VS D).herm.eq (X.eX a) (X.zu u)
    rw [(X.zu_orth u a).1] at h
    rw [← h]
    simp
  have hzz : hJ (X.B.I.ε v) (rv X.B.I v (X.zR u)) (rv X.B.I v (X.zR u)) ≠ 0 := by
    rw [HidaSetting.zR, Cut.hJ_crd X v, X.zu_norm]
    simp only [map_neg, map_natCast, neg_ne_zero, Nat.cast_ne_zero]
    exact ((D.mem u).A.T_prime).ne_zero
  have hfe : ∀ j a, hJ (X.B.I.ε v) (rv X.B.I v (X.fR j)) (rv X.B.I v (X.eR a)) = if a = j then 1 else 0 := by
    intro j a
    refine (Cut.hJ_crd X v _ _).trans ?_
    rw [Cut.hT_f_e X]
    split_ifs <;> simp
  have hfz : ∀ j, hJ (X.B.I.ε v) (rv X.B.I v (X.fR j)) (rv X.B.I v (X.zR u)) = 0 := by
    intro j
    refine (Cut.hJ_crd X v _ _).trans ?_
    rw [(X.zu_orth u j).2]
    simp
  rw [hfr, Fintype.linearIndependent_iff]
  intro g hg
  rw [Fin.sum_univ_castSucc] at hg
  simp only [Formalism.L2.SG.RealObj.fam, Fin.snoc_castSucc, Fin.snoc_last] at hg
  have hlast : g (Fin.last _) = 0 := by
    have h := congrArg (hJ (X.B.I.ε v) (rv X.B.I v (X.zR u))) hg
    rw [hJ_lin] at h
    simp only [hze, mul_zero, Finset.sum_const_zero, zero_add] at h
    unfold hJ at h
    simp only [mulVec_zero, dotProduct_zero] at h
    exact (mul_eq_zero.1 h).resolve_right hzz
  intro i
  refine Fin.lastCases hlast (fun j => ?_) i
  have h := congrArg (hJ (X.B.I.ε v) (rv X.B.I v (X.fR j))) hg
  rw [hJ_lin, hfz] at h
  simp only [hfe, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, add_zero] at h
  unfold hJ at h
  simp only [mulVec_zero, dotProduct_zero] at h
  exact h

end GlobalTheory.RationalFrame
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalBesselFrameRealPlaceLinearIndependentStatement
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalBesselFrame_realPlace_linearIndependent : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (v : NumberField.InfinitePlace X.B.I.F), LinearIndependent ℂ (Formalism.L2.SG.RealObj.frm X u 1 v) := by
  first | exact @GlobalTheory.RationalFrame.frame_linearIndependent | exact GlobalTheory.RationalFrame.frame_linearIndependent | (intros; apply GlobalTheory.RationalFrame.frame_linearIndependent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegerPointsCoverRealPointsRootCoordinates
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Matrix

noncomputable section

open scoped Classical
open MeasureTheory

namespace GlobalTheory.LoopVol

def actSgn (r : ℕ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ := Matrix.diagonal fun b => (-1 : ℂ) ^ (r - b.val)

theorem actSgn_mul_self (r : ℕ) : actSgn r * actSgn r = 1 := by
  rw [actSgn, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext b
  rw [← mul_pow]
  norm_num

theorem actSgn_conj_apply {r : ℕ} (M : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (i j : Fin (r + 1)) :
    (actSgn r * M * actSgn r) i j = (-1 : ℂ) ^ (r - i.val) * M i j * (-1) ^ (r - j.val) := by
  simp [actSgn, Matrix.diagonal_mul, Matrix.mul_diagonal]

theorem act_zhatO_eq {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) :
    Formalism.L2.SG.RealObj.ZhatO Z = Z * actSgn r := by
  ext a b
  simp [Formalism.L2.SG.RealObj.ZhatO, actSgn, Matrix.mul_diagonal, mul_comm]

theorem act_zhatOM_map {K : Type} [Field K] {r : ℕ} (ψ : K →+* ℂ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    (ZhatOM Z).map ψ = Z.map ψ * actSgn r := by
  ext a b
  simp [ZhatOM, actSgn, Matrix.mul_diagonal, mul_comm]

theorem actSgn_conj_ofRoots {r : ℕ} (R : Finset (Fin (r + 1) × Fin (r + 1))) (c : R → ℂ) :
    actSgn r * GlobalTheory.LoopV.ofRoots R c * actSgn r =
      GlobalTheory.LoopV.ofRoots R (fun q => (-1 : ℂ) ^ (r - q.1.1.val) * c q * (-1) ^ (r - q.1.2.val)) := by
  ext i j
  rw [actSgn_conj_apply]
  unfold GlobalTheory.LoopV.ofRoots
  split_ifs with h1 h2
  · rfl
  · subst h2
    rw [mul_one, ← mul_pow]
    norm_num
  · simp

theorem act_isUpUni_sgn {r : ℕ} {M : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (h : IsUpUni M) :
    IsUpUni (actSgn r * M * actSgn r) := fun i j =>
  ⟨fun hij => by rw [actSgn_conj_apply, (h i j).1 hij]; simp,
   fun hij => by subst hij; rw [actSgn_conj_apply, (h i i).2 rfl, mul_one, ← mul_pow]; norm_num⟩

theorem act_isUpUni_map {K : Type} [Field K] {N : ℕ} (ψ : K →+* ℂ) {M : Matrix (Fin N) (Fin N) K}
    (h : IsUpUni M) : IsUpUni (M.map ψ) := fun i j =>
  ⟨fun hij => by simp [(h i j).1 hij], fun hij => by subst hij; simp [(h i i).2 rfl]⟩

theorem act_isLoUni_map {K : Type} [Field K] {N : ℕ} (ψ : K →+* ℂ) {M : Matrix (Fin N) (Fin N) K}
    (h : IsLoUni M) : IsLoUni (M.map ψ) := fun i j =>
  ⟨fun hij => by simp [(h i j).1 hij], fun hij => by subst hij; simp [(h i i).2 rfl]⟩

theorem act_isLoUni_conjTranspose {N : ℕ} {C : Matrix (Fin N) (Fin N) ℂ} (h : IsUpUni C) : IsLoUni Cᴴ :=
  fun i j => ⟨fun hij => by simp [Matrix.conjTranspose_apply, (h j i).1 hij],
    fun hij => by subst hij; simp [Matrix.conjTranspose_apply, (h i i).2 rfl]⟩

theorem act_sgn_mem {r : ℕ} {Z P m : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hZ : IsUnit Z.det)
    (hP : Z * actSgn r = P) (hm : m ∈ GlobalTheory.LoopV.stabU Z) : actSgn r * m * actSgn r ∈ GlobalTheory.LoopV.stabU P := by
  refine ⟨act_isUpUni_sgn hm.1, ?_⟩
  have hss := actSgn_mul_self r
  have hsi : (actSgn r)⁻¹ = actSgn r := Matrix.inv_eq_left_inv hss
  have e : P * (actSgn r * m * actSgn r) * P⁻¹ = Z * m * Z⁻¹ := by
    rw [← hP, Matrix.mul_inv_rev, hsi]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (actSgn r) (actSgn r), hss, Matrix.one_mul, ← Matrix.mul_assoc (actSgn r) (actSgn r), hss,
      Matrix.one_mul]
  rw [e]
  exact hm.2

theorem act_eq_ofRoots {K : Type} [Field K] {r : ℕ} (ψ : K →+* ℂ) (p : Point K (r + 1))
    {Z m : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hZ : IsUnit Z.det) (hP : Z * actSgn r = (ptMat p).map ψ)
    (hm : m ∈ GlobalTheory.LoopV.stabU Z) : m = GlobalTheory.LoopV.ofRoots (GlobalTheory.LoopV.roots (ptMat p)) (fun q => m q.1.1 q.1.2) := by
  have h1 := GlobalTheory.LoopAct.stabU_map_eq_ofRoots ψ p _ (act_sgn_mem hZ hP hm)
  have hss := actSgn_mul_self r
  have h2 : actSgn r * (actSgn r * m * actSgn r) * actSgn r = actSgn r * GlobalTheory.LoopV.ofRoots (GlobalTheory.LoopV.roots (ptMat p))
      (fun q => (actSgn r * m * actSgn r) q.1.1 q.1.2) * actSgn r := congrArg (fun M => actSgn r * M * actSgn r) h1
  rw [actSgn_conj_ofRoots] at h2
  have e : actSgn r * (actSgn r * m * actSgn r) * actSgn r = m := by
    simp only [← Matrix.mul_assoc, hss, Matrix.one_mul]
    rw [Matrix.mul_assoc, hss, Matrix.mul_one]
  rw [e] at h2
  refine h2.trans (congrArg (GlobalTheory.LoopV.ofRoots (GlobalTheory.LoopV.roots (ptMat p))) ?_)
  funext q
  rw [actSgn_conj_apply]
  have ha : ((-1 : ℂ) ^ (r - q.1.1.val)) * (-1) ^ (r - q.1.1.val) = 1 := by rw [← mul_pow]; norm_num
  have hb : ((-1 : ℂ) ^ (r - q.1.2.val)) * (-1) ^ (r - q.1.2.val) = 1 := by rw [← mul_pow]; norm_num
  linear_combination (m q.1.1 q.1.2 * (-1 : ℂ) ^ (r - q.1.2.val) * (-1) ^ (r - q.1.2.val)) * ha + m q.1.1 q.1.2 * hb

theorem act_sign_pow (r : ℕ) (i j : Fin (r + 1)) :
    (-1 : ℂ) ^ (i.val + j.val) = (-1 : ℂ) ^ (r - i.val) * (-1) ^ (r - j.val) := by
  rw [← pow_add, neg_one_pow_eq_pow_mod_two, neg_one_pow_eq_pow_mod_two (n := r - i.val + (r - j.val))]
  have hi := i.isLt
  have hj := j.isLt
  congr 1
  omega

theorem act_neg_one_mp (k : ℕ) : MeasurePreserving (fun x : ℂ => (-1 : ℂ) ^ k * x) volume volume := by
  rcases neg_one_pow_eq_or ℂ k with h | h
  · simp only [h, one_mul]
    exact MeasurePreserving.id volume
  · simp only [h, neg_one_mul]
    exact Measure.measurePreserving_neg volume

open GlobalTheory.LoopAct in
theorem cover_action : ∀ Cg cb Cu cT CT C0 A : ℝ, ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (W : WittDat X) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl : ℝ), Formalism.MainNotions.S.Cnt.Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A → ∀ s : TT Y u u', s.relevant → s.G ≠ 0 → ∀ (w : Point D.host.E (D.R.rS + 1)) (γw sf s' : X.B.I.Ginf), s.toTerm.atPt w → Formalism.L2.SG.RealObj.IsPtRep X u u' w γw → sf ∈ X.SinfU u → s' ∈ X.SinfU u' → s.pt.1 = sf * γw * s'⁻¹ → ∀ (L U : Formalism.MainNotions.S.Cnt.GramM D), IsLoUni L → IsUpUni U → ZhatOM (ZhatL (lf D (FlagOfWord W u)) (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame)) = L * ptMat w * U → ∀ Ω : Set (D.what₂.Tau → GlobalTheory.LoopV.roots (ptMat w) → ℂ), (∀ c : D.what₂.Tau → GlobalTheory.LoopV.roots (ptMat w) → ℂ, ∃ n ∈ NLam (Formalism.HermitianLatticesTheory.gmap (W.δ u) s.lam) (lf D (FlagOfWord W u)) ∩ NLam (Formalism.HermitianLatticesTheory.gmap (W.δ u) s.lam) (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame), ∃ a : Formalism.MainNotions.S.Cnt.GramM D, (∀ j : Fin (D.R.rS + 1), n (frame (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame) j) = ∑ i : Fin (D.R.rS + 1), ((-1) ^ (i.val + j.val) * a i j) • frame (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame) i) ∧ (fun τ (q : GlobalTheory.LoopV.roots (ptMat w)) => ((U * a * U⁻¹).map (embS D τ) * GlobalTheory.LoopV.ofRoots (GlobalTheory.LoopV.roots (ptMat w)) (c τ) : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ) q.1.1 q.1.2) ∈ Ω) → ∃ T : (D.what₂.Tau → GlobalTheory.LoopV.roots (ptMat w) → ℂ) → (D.what₂.Tau → GlobalTheory.LoopV.roots (ptMat w) → ℂ), MeasureTheory.MeasurePreserving T MeasureTheory.volume MeasureTheory.volume ∧ ∀ r ∈ Formalism.L2.SG.TermOp.Vanish.Rset s, ∃ q ∈ Formalism.L2.SG.TermOp.ROinf s, T (GlobalTheory.LoopVol.ratCoord X u' w γw sf (q * r)) ∈ Ω := by
  intro Cg cb Cu cT CT C0 A D X Y W large₂ u u' C' Cl hH s hrel hG w γw sf s' hat hrep hsf hs' hdec L U hL hU hZ Ω hcov
  set R := GlobalTheory.LoopV.roots (ptMat w) with hR
  have hRlt : ∀ q ∈ R, q.1 < q.2 := by
    intro q hq
    simp only [hR, GlobalTheory.LoopV.roots, Finset.mem_filter] at hq
    exact hq.2.1
  have hs'i : s'⁻¹ ∈ X.SinfU u' := Formalism.L2.SG.Pf.Sinf.sinf_inv' X u' hs'
  have hsfi : sf⁻¹ ∈ X.SinfU u := Formalism.L2.SG.Pf.Sinf.sinf_inv' X u hsf
  choose B hBu hBm using fun τ : D.what₂.Tau => GlobalTheory.T.realBesselSubgroup_acts_frame_upperUnitriangular D X u' s'⁻¹ hs'i (X.pl.symm τ)
  choose Cm hCu hCm using fun τ : D.what₂.Tau => GlobalTheory.T.realBesselSubgroup_acts_frame_upperUnitriangular D X u sf⁻¹ hsfi (X.pl.symm τ)
  have hUi := Formalism.L2.SG.Pf.ZsVolGrp.isUpUni_inv hU
  set sg := actSgn D.R.rS with hsg
  have hss : sg * sg = 1 := actSgn_mul_self _
  have hss' : ∀ M : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ, sg * (sg * M) = M := fun M => by
    rw [← Matrix.mul_assoc, hss, Matrix.one_mul]
  set Uc : D.what₂.Tau → Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ := fun τ => U.map (embS D τ) with hUc
  have hUcu : ∀ τ, IsUpUni (Uc τ) := fun τ => act_isUpUni_map _ hU
  have hBi : ∀ τ, (B τ)⁻¹ * B τ = 1 ∧ B τ * (B τ)⁻¹ = 1 := fun τ => (Formalism.L2.SG.Pf.ZsVolGrp.isUpUni_inv (hBu τ)).2
  have hUci : ∀ τ, (Uc τ)⁻¹ * Uc τ = 1 ∧ Uc τ * (Uc τ)⁻¹ = 1 := fun τ =>
    (Formalism.L2.SG.Pf.ZsVolGrp.isUpUni_inv (hUcu τ)).2
  have hUcinv : ∀ τ, (U⁻¹).map (embS D τ) = (Uc τ)⁻¹ := fun τ => by
    refine (Matrix.inv_eq_left_inv ?_).symm
    simp only [hUc]
    rw [← Matrix.map_mul, hUi.2.1, Matrix.map_one _ (map_zero _) (map_one _)]
  set Xm : D.what₂.Tau → Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ := fun τ => Uc τ * sg * (B τ)⁻¹ with hXm
  have hXinv : ∀ τ, (Xm τ)⁻¹ = B τ * sg * (Uc τ)⁻¹ := fun τ => by
    refine Matrix.inv_eq_right_inv ?_
    calc Xm τ * (B τ * sg * (Uc τ)⁻¹) = Uc τ * (sg * (((B τ)⁻¹ * B τ) * (sg * (Uc τ)⁻¹))) := by
          simp only [hXm, Matrix.mul_assoc]
      _ = 1 := by rw [(hBi τ).1, Matrix.one_mul, hss', (hUci τ).2]

  set T : (D.what₂.Tau → R → ℂ) → (D.what₂.Tau → R → ℂ) :=
    fun c τ q => (Xm τ * GlobalTheory.LoopV.ofRoots R (c τ) * (Xm τ)⁻¹) q.1.1 q.1.2 with hTdef
  refine ⟨T, ?_, ?_⟩
  · set a : D.what₂.Tau → Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ := fun τ => Uc τ * (sg * (B τ)⁻¹ * sg) with ha
    set b : D.what₂.Tau → Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ := fun τ => sg * B τ * sg * (Uc τ)⁻¹ with hb
    have hau : ∀ τ, IsUpUni (a τ) := fun τ => Formalism.L2.SG.Pf.ZsVolGrp.isUpUni_mul (hUcu τ)
      (act_isUpUni_sgn (Formalism.L2.SG.Pf.ZsVolGrp.isUpUni_inv (hBu τ)).1)
    have hbu : ∀ τ, IsUpUni (b τ) := fun τ => Formalism.L2.SG.Pf.ZsVolGrp.isUpUni_mul (act_isUpUni_sgn (hBu τ))
      (Formalism.L2.SG.Pf.ZsVolGrp.isUpUni_inv (hUcu τ)).1
    have hconj : ∀ τ (M : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ),
        Xm τ * M * (Xm τ)⁻¹ = a τ * (sg * M * sg) * b τ := fun τ M => by
      rw [hXinv]
      simp only [hXm, ha, hb, Matrix.mul_assoc, hss']
    have hTc : T = (fun (c : D.what₂.Tau → R → ℂ) τ (q : R) => (a τ * GlobalTheory.LoopV.ofRoots R (c τ) * b τ) q.1.1 q.1.2) ∘
        (fun (c : D.what₂.Tau → R → ℂ) τ => (fun (c' : R → ℂ) (q : R) =>
          (-1 : ℂ) ^ (D.R.rS - q.1.1.val + (D.R.rS - q.1.2.val)) * c' q) (c τ)) := by
      funext c τ q
      simp only [hTdef, Function.comp, hconj, hsg, actSgn_conj_ofRoots]
      have hfun : (fun q' : R => (-1 : ℂ) ^ (D.R.rS - q'.1.1.val) * c τ q' * (-1) ^ (D.R.rS - q'.1.2.val)) =
          fun q' : R => (-1 : ℂ) ^ (D.R.rS - q'.1.1.val + (D.R.rS - q'.1.2.val)) * c τ q' := by
        funext q'
        rw [pow_add]
        ring
      rw [hfun]
    rw [hTc]
    refine (GlobalTheory.LoopVol.measurePreserving_mul_pi R hRlt a b hau hbu).comp ?_
    exact volume_preserving_pi fun _ => volume_preserving_pi fun q => act_neg_one_mp _
  · intro r hr
    have hstr := Formalism.L2.SG.LoopTerm.stInf_conj_inv hsf hs' hdec hr
    have hyr : γw⁻¹ * (sf⁻¹ * r * sf) * γw ∈ X.SinfU u' := fun v => (hstr.2 v).1
    choose Mr hMru hMrm using fun τ : D.what₂.Tau => GlobalTheory.T.realBesselSubgroup_acts_frame_upperUnitriangular D X u' _ hyr (X.pl.symm τ)
    obtain ⟨n, hn, a, ha, hΩ⟩ := hcov (T (GlobalTheory.LoopVol.ratCoord X u' w γw sf r))
    obtain ⟨x, hx, hq⟩ := GlobalTheory.T.rationalLink_conjugate_mem_integralRealPoints D X Y W u u' s n hn
    refine ⟨x.1, hq, ?_⟩
    have hqR := Formalism.L2.SG.Pf.LoopBPin.roinf_sub_rset s hq
    have hstq := Formalism.L2.SG.LoopTerm.stInf_conj_inv hsf hs' hdec hqR
    have hyq : γw⁻¹ * (sf⁻¹ * x.1 * sf) * γw ∈ X.SinfU u' := fun v => (hstq.2 v).1
    set Ar : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E :=
      Matrix.of fun i j => (-1) ^ (i.val + j.val) * a i j with hAr
    have hnA : ∀ j, ((W.δ u)⁻¹ * n * W.δ u) (frame s.frame j) = ∑ i, Ar i j • frame s.frame i := by
      intro j
      have e1 : ∀ i, frame (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame) i = W.δ u (frame s.frame i) :=
        fun i => by
          show (Formalism.L2.SG.Saturated.mapFlag (W.δ u) (W.isom u) s.frame.fl).fvec i = _
          rw [Formalism.L2.SG.Saturated.fvec_mapFlag]
      have h := ha j
      simp only [e1] at h
      show (W.δ u).symm (n (W.δ u (frame s.frame j))) = _
      set_option synthInstance.maxHeartbeats 100000 in
        rw [h, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, LinearEquiv.symm_apply_apply]
      rfl
    have hum : ∀ (g h : X.B.I.Ginf) v, uMat ((g * h) v) = uMat (g v) * uMat (h v) := by
      intro g h v
      simp [uMat]
    have huinv : ∀ (g : X.B.I.Ginf) v, uMat (g⁻¹ v) * uMat (g v) = 1 := by
      intro g v
      rw [← hum, inv_mul_cancel]
      simp [uMat]
    convert hΩ using 1
    funext τ q
    set v := X.pl.symm τ with hv
    have hplv : X.pl v = τ := X.pl.apply_symm_apply τ
    set Zv := Formalism.L2.SG.RealObj.ZX X u u' 1 γw v with hZv
    have hptC : Formalism.L2.SG.RealObj.ptC X v w = (ptMat w).map (embS D τ) := by
      ext i j
      simp only [Formalism.L2.SG.RealObj.ptC, Matrix.map_apply, X.φ_eq, RingEquiv.apply_symm_apply, hplv]
    have hZs : Zv * sg = (ptMat w).map (embS D τ) := by
      rw [hZv, hsg, ← act_zhatO_eq, hrep v, hptC]
    have hZu : IsUnit Zv.det := by
      have h1 : IsUnit (Zv * sg).det := by
        rw [hZs]
        have h2 := (GlobalTheory.LoopV.Cell.ptMat_det w).map (embS D τ)
        rw [RingHom.map_det] at h2
        exact h2
      rw [Matrix.det_mul] at h1
      exact isUnit_of_mul_isUnit_left h1
    have hMrs : Mr τ ∈ GlobalTheory.LoopV.stabU Zv := GlobalTheory.T.frameMatrix_mem_unipotentStabilizer_frameGram D X u u' γw _ v (Mr τ) hstr (hMru τ) (hMrm τ) hZu
    obtain ⟨Mq, hMqu, hMqm⟩ := GlobalTheory.T.realBesselSubgroup_acts_frame_upperUnitriangular D X u' _ hyq v
    have hMqs : Mq ∈ GlobalTheory.LoopV.stabU Zv := GlobalTheory.T.frameMatrix_mem_unipotentStabilizer_frameGram D X u u' γw _ v Mq hstq hMqu hMqm hZu

    have hrc : GlobalTheory.LoopV.ofRoots R (GlobalTheory.LoopVol.ratCoord X u' w γw sf r τ) = Mr τ := by
      have e : GlobalTheory.LoopVol.ratCoord X u' w γw sf r τ = fun q' : R => Mr τ q'.1.1 q'.1.2 :=
        funext (GlobalTheory.T.rationalRootCoordinates_eq_frameMatrix D X u' w γw sf r τ (Mr τ) (hMrm τ))
      rw [e]
      exact (act_eq_ofRoots (embS D τ) w hZu hZs hMrs).symm
    have hyqr : γw⁻¹ * (sf⁻¹ * (x.1 * r) * sf) * γw =
        (γw⁻¹ * (sf⁻¹ * x.1 * sf) * γw) * (γw⁻¹ * (sf⁻¹ * r * sf) * γw) := by group
    have hMqrm : IsMatOn (uMat ((γw⁻¹ * (sf⁻¹ * (x.1 * r) * sf) * γw) v)) (Formalism.L2.SG.RealObj.frm X u' 1 v)
        (Mq * Mr τ) := by
      rw [hyqr, hum]
      exact isMatOn_mul hMqm (hMrm τ)
    have hqrc : GlobalTheory.LoopV.ofRoots R (GlobalTheory.LoopVol.ratCoord X u' w γw sf (x.1 * r) τ) = Mq * Mr τ := by
      have e : GlobalTheory.LoopVol.ratCoord X u' w γw sf (x.1 * r) τ = fun q' : R => (Mq * Mr τ) q'.1.1 q'.1.2 :=
        funext (GlobalTheory.T.rationalRootCoordinates_eq_frameMatrix D X u' w γw sf (x.1 * r) τ (Mq * Mr τ) hMqrm)
      rw [e]
      exact (act_eq_ofRoots (embS D τ) w hZu hZs (stabU_mul hZu hMqs hMrs)).symm

    have hAq := GlobalTheory.T.realPoint_rationalIsometry_acts_frame_matrix D X Y u u' s _ x Ar hx hnA v
    rw [hplv] at hAq
    have hc1 := isMatOn_conj hAq (huinv s.pt.1 v)
    have e1 : uMat (s.pt.1⁻¹ v) * uMat (x.1 v) * uMat (s.pt.1 v) =
        uMat ((s' * (γw⁻¹ * (sf⁻¹ * x.1 * sf) * γw) * s'⁻¹) v) := by
      rw [← hum, ← hum]
      congr 2
      rw [hdec]
      group
    rw [e1] at hc1
    have hc2 := isMatOn_mul (hBm τ) hc1
    have hc3 := isMatOn_mul hMqm (hBm τ)
    rw [← hum] at hc2 hc3
    have e2 : s'⁻¹ * (s' * (γw⁻¹ * (sf⁻¹ * x.1 * sf) * γw) * s'⁻¹) = (γw⁻¹ * (sf⁻¹ * x.1 * sf) * γw) * s'⁻¹ := by
      group
    rw [e2] at hc2
    have heq := isMatOn_unique (GlobalTheory.T.rationalBesselFrame_realPlace_linearIndependent D X u' v) hc3 hc2
    have hA' : Ar.map (embS D τ) = sg * a.map (embS D τ) * sg := by
      ext i j
      rw [hsg, actSgn_conj_apply]
      simp only [hAr, Matrix.map_apply, Matrix.of_apply, map_mul, map_pow, map_neg, map_one]
      rw [act_sign_pow D.R.rS i j]
      ring
    have hMq : Mq = B τ * (sg * a.map (embS D τ) * sg) * (B τ)⁻¹ := by
      rw [← hA', ← heq, Matrix.mul_assoc, (hBi τ).2, Matrix.mul_one]

    have hzr := GlobalTheory.T.rationalFrameGram_embed_eq_realFrameGram D X Y W u u' s τ
    have hzm := GlobalTheory.T.frameGram_mul_eq_conjTranspose_mul_frameMatrices D X u u' sf γw s'⁻¹ v (Cm τ) (B τ) (hCm τ) (hBm τ)
    have hkey : (Cm τ)ᴴ * Zv * B τ * sg = L.map (embS D τ) * (Zv * sg) * Uc τ := by
      have h : Matrix.map (ZhatOM (ZhatL (lf D (FlagOfWord W u)) (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame)))
          (embS D τ) = Matrix.map (L * ptMat w * U) (embS D τ) := congrArg (fun M => Matrix.map M (embS D τ)) hZ
      rw [act_zhatOM_map, hzr, hdec, hzm, Matrix.map_mul, Matrix.map_mul, ← hZs] at h
      exact h
    set g0 := B τ * (sg * (Uc τ)⁻¹ * sg) with hg0
    have hCl := act_isLoUni_conjTranspose (hCu τ)
    have hCli := Formalism.L2.SG.Pf.ZsVolGrp.isLoUni_inv hCl
    have hZg : Zv * g0 * Zv⁻¹ = ((Cm τ)ᴴ)⁻¹ * L.map (embS D τ) := by
      have h1 : (Cm τ)ᴴ * (Zv * g0) = L.map (embS D τ) * Zv := by
        calc (Cm τ)ᴴ * (Zv * g0) = ((Cm τ)ᴴ * Zv * B τ * sg) * ((Uc τ)⁻¹ * sg) := by
              simp only [hg0, Matrix.mul_assoc]
          _ = L.map (embS D τ) * Zv := by
              rw [hkey]
              simp only [Matrix.mul_assoc]
              rw [← Matrix.mul_assoc (Uc τ) (Uc τ)⁻¹, (hUci τ).2, Matrix.one_mul, hss, Matrix.mul_one]
      have h2 : Zv * g0 = ((Cm τ)ᴴ)⁻¹ * (L.map (embS D τ) * Zv) := by
        rw [← h1, ← Matrix.mul_assoc ((Cm τ)ᴴ)⁻¹, hCli.2.1, Matrix.one_mul]
      rw [h2, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hZu, Matrix.mul_one]
    have hg0s : g0 ∈ GlobalTheory.LoopV.stabU Zv := by
      refine ⟨Formalism.L2.SG.Pf.ZsVolGrp.isUpUni_mul (hBu τ)
        (act_isUpUni_sgn (Formalism.L2.SG.Pf.ZsVolGrp.isUpUni_inv (hUcu τ)).1), ?_⟩
      rw [hZg]
      exact Formalism.L2.SG.Pf.ZsVolGrp.isLoUni_mul hCli.1 (act_isLoUni_map _ hL)
    have hg0i : g0⁻¹ = sg * Uc τ * sg * (B τ)⁻¹ := by
      refine Matrix.inv_eq_right_inv ?_
      calc g0 * (sg * Uc τ * sg * (B τ)⁻¹) = B τ * (sg * ((Uc τ)⁻¹ * (sg * (sg * (Uc τ * (sg * (B τ)⁻¹)))))) := by
            simp only [hg0, Matrix.mul_assoc]
        _ = 1 := by rw [hss', ← Matrix.mul_assoc (Uc τ)⁻¹, (hUci τ).1, Matrix.one_mul, hss', (hBi τ).2]
    have hXr : Xm τ * Mr τ * (Xm τ)⁻¹ = sg * (g0⁻¹ * Mr τ * g0) * sg := by
      rw [hg0i, hXinv]
      simp only [hXm, hg0, Matrix.mul_assoc, hss', hss, Matrix.mul_one]
    have hXrs : GlobalTheory.LoopV.ofRoots R (T (GlobalTheory.LoopVol.ratCoord X u' w γw sf r) τ) = Xm τ * Mr τ * (Xm τ)⁻¹ := by
      have hm := act_sgn_mem hZu hZs (stabU_mul hZu (stabU_mul hZu (stabU_inv hZu hg0s) hMrs) hg0s)
      have h1 := GlobalTheory.LoopAct.stabU_map_eq_ofRoots (embS D τ) w _ hm
      rw [← hXr] at h1
      rw [h1]
      refine congrArg (GlobalTheory.LoopV.ofRoots R) ?_
      funext q'
      simp only [hTdef]
      rw [hrc]

    rw [hXrs]
    simp only [hTdef]
    have hB1 : ∀ M : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ, (B τ)⁻¹ * (B τ * M) = M := fun M => by
      rw [← Matrix.mul_assoc, (hBi τ).1, Matrix.one_mul]
    have hU1 : ∀ M : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ, (Uc τ)⁻¹ * (Uc τ * M) = M := fun M => by
      rw [← Matrix.mul_assoc, (hUci τ).1, Matrix.one_mul]
    have hfin : ∀ P : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ,
        Xm τ * (B τ * (sg * P * sg) * (B τ)⁻¹ * Mr τ) * (B τ * sg * (Uc τ)⁻¹) =
          Uc τ * P * (Uc τ)⁻¹ * (Xm τ * Mr τ * (B τ * sg * (Uc τ)⁻¹)) := fun P => by
      simp only [hXm, Matrix.mul_assoc, hB1, hU1, hss']
    rw [hqrc, Matrix.map_mul, Matrix.map_mul, hUcinv, hMq, hXinv, hfin]

end GlobalTheory.LoopVol

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegerPointsCoverRealPointsRootCoordinatesStatement
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integerPoints_cover_realPoints_rootCoordinates : ∀ Cg cb Cu cT CT C0 A : ℝ, ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (W : WittDat X) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl : ℝ), Formalism.MainNotions.S.Cnt.Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A → ∀ s : TT Y u u', s.relevant → s.G ≠ 0 → ∀ (w : Point D.host.E (D.R.rS + 1)) (γw sf s' : X.B.I.Ginf), s.toTerm.atPt w → Formalism.L2.SG.RealObj.IsPtRep X u u' w γw → sf ∈ X.SinfU u → s' ∈ X.SinfU u' → s.pt.1 = sf * γw * s'⁻¹ → ∀ (L U : Formalism.MainNotions.S.Cnt.GramM D), IsLoUni L → IsUpUni U → ZhatOM (ZhatL (lf D (FlagOfWord W u)) (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame)) = L * ptMat w * U → ∀ Ω : Set (D.what₂.Tau → GlobalTheory.LoopV.roots (ptMat w) → ℂ), (∀ c : D.what₂.Tau → GlobalTheory.LoopV.roots (ptMat w) → ℂ, ∃ n ∈ NLam (Formalism.HermitianLatticesTheory.gmap (W.δ u) s.lam) (lf D (FlagOfWord W u)) ∩ NLam (Formalism.HermitianLatticesTheory.gmap (W.δ u) s.lam) (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame), ∃ a : Formalism.MainNotions.S.Cnt.GramM D, (∀ j : Fin (D.R.rS + 1), n (frame (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame) j) = ∑ i : Fin (D.R.rS + 1), ((-1) ^ (i.val + j.val) * a i j) • frame (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame) i) ∧ (fun τ (q : GlobalTheory.LoopV.roots (ptMat w)) => ((U * a * U⁻¹).map (embS D τ) * GlobalTheory.LoopV.ofRoots (GlobalTheory.LoopV.roots (ptMat w)) (c τ) : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ) q.1.1 q.1.2) ∈ Ω) → ∃ T : (D.what₂.Tau → GlobalTheory.LoopV.roots (ptMat w) → ℂ) → (D.what₂.Tau → GlobalTheory.LoopV.roots (ptMat w) → ℂ), MeasureTheory.MeasurePreserving T MeasureTheory.volume MeasureTheory.volume ∧ ∀ r ∈ Formalism.L2.SG.TermOp.Vanish.Rset s, ∃ q ∈ Formalism.L2.SG.TermOp.ROinf s, T (GlobalTheory.LoopVol.ratCoord X u' w γw sf (q * r)) ∈ Ω := by
  first | exact @GlobalTheory.LoopVol.cover_action | exact GlobalTheory.LoopVol.cover_action | (intros; apply GlobalTheory.LoopVol.cover_action <;> assumption)
end
