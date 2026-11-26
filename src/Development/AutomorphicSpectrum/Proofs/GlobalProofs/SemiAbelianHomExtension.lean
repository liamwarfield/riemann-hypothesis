module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenImmersionQuasiFiniteLocusOfIsIntegral
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ContinuousConjBlockEmbedding

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.SemiAbelianHomExtension
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CompanionTheory.SAH

theorem semiAbelianHomExtension : GlobalTheory.Published.SemiAbelianHomExtension := by
  intro S _ hS U hU G H _ _ hG hH f hf
  have : IsDominant U.ι := ⟨by
    rw [DenseRange, Scheme.Opens.range_ι]
    exact hU⟩
  exact GlobalTheory.HomExtNormal.existsUnique_hom_extension_of_dvr
    GlobalTheory.existsUnique_hom_extension_semiAbelian S U U.ι hS G H hG hH f hf

end GlobalTheory.CompanionTheory.SAH
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsotropicFrameWittBound
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsotropicFrameWittBound
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section
namespace GlobalTheory.CompanionTheory.IsoFrameBound

open Formalism.UG (cT)

variable {E : Type} [Field E]

theorem rank_map_of_invol (s : E →+* E) (hs : ∀ x, s (s x) = x) {a b : ℕ} (A : Matrix (Fin a) (Fin b) E) :
    (A.map s).rank = A.rank := by
  have hAA : (A.map s).map s = A := by ext i j; simp [hs]
  have key : ∀ (B : Matrix (Fin a) (Fin b) E) (v : Fin a → E), v ∈ LinearMap.range B.mulVecLin →
      (fun i => s (v i)) ∈ LinearMap.range (B.map s).mulVecLin := by
    rintro B v ⟨w, rfl⟩
    refine ⟨fun i => s (w i), ?_⟩
    funext i
    simp only [Matrix.mulVecLin_apply]
    exact (RingHom.map_mulVec s B w i).symm
  let j : LinearMap.range A.mulVecLin ≃+ LinearMap.range (A.map s).mulVecLin :=
    { toFun := fun v => ⟨fun i => s (v.1 i), key A v.1 v.2⟩
      invFun := fun v => ⟨fun i => s (v.1 i), by
        have := key (A.map s) v.1 v.2
        rwa [hAA] at this⟩
      left_inv := fun v => by ext i; simp [hs]
      right_inv := fun v => by ext i; simp [hs]
      map_add' := fun v w => by ext i; simp }
  have hb : Function.Bijective s := ⟨s.injective, fun x => ⟨s x, hs x⟩⟩
  have := rank_eq_of_equiv_equiv s j hb (fun c v => Subtype.ext (funext fun i => by
    show s (c * v.1 i) = s c * s (v.1 i)
    exact map_mul s _ _))
  show Module.finrank E _ = Module.finrank E _
  exact congrArg Cardinal.toNat this.symm

theorem hform_eq (s : E →+* E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    Formalism.UG.hform s J x y = (fun i => s (x i)) ⬝ᵥ (J *ᵥ y) := by
  simp only [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem dot_cT (s : E →+* E) {n k : ℕ} (P : Matrix (Fin n) (Fin k) E) (J : Matrix (Fin n) (Fin n) E)
    (u : Fin k → E) (v : Fin n → E) :
    (fun i => s ((P *ᵥ u) i)) ⬝ᵥ (J *ᵥ v) = (fun i => s (u i)) ⬝ᵥ ((cT s P * J) *ᵥ v) := by
  have e : (fun i => s (u i)) ᵥ* cT s P = fun i => s ((P *ᵥ u) i) := by
    show _ ᵥ* (P.map s)ᵀ = _
    rw [Matrix.vecMul_transpose]
    funext i
    exact (RingHom.map_mulVec s P u i).symm
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec (fun i => s (u i)) (cT s P) (J *ᵥ v), e]

theorem le_of_frames (s : E →+* E) (hs : ∀ x, s (s x) = x) {n m r : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (hJ : cT s J = J) (X Y : Matrix (Fin n) (Fin m) E) (C : Matrix (Fin n) (Fin r) E)
    (xx : cT s X * J * X = 0) (yx : cT s Y * J * X = 1) (cc : cT s C * J * C = 0)
    (an : ∀ z : Fin n → E, (cT s X * J) *ᵥ z = 0 → (cT s Y * J) *ᵥ z = 0 → Formalism.UG.hform s J z z = 0 → z = 0)
    (hC : LinearIndependent E Cᵀ) : r ≤ m := by
  obtain ⟨M, hM⟩ : ∃ M, M = cT s X * J * C := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = cT s Y * J * C := ⟨_, rfl⟩
  obtain ⟨M', hM'⟩ : ∃ M', M' = cT s C * J * X := ⟨_, rfl⟩
  have hXX : cT s (cT s X) = X := by ext i j; simp [cT, hs]
  have hMM : M' = cT s M := by
    rw [hM, hM', Formalism.UG.cT_mul, Formalism.UG.cT_mul, hJ, hXX, Matrix.mul_assoc]
  have step : ∀ a, M *ᵥ a = 0 → X *ᵥ (Q *ᵥ a) = C *ᵥ a := by
    intro a ha
    obtain ⟨b, hb⟩ : ∃ b, b = Q *ᵥ a := ⟨_, rfl⟩
    obtain ⟨z, hz⟩ : ∃ z, z = C *ᵥ a - X *ᵥ b := ⟨_, rfl⟩
    have hA : (cT s X * J) *ᵥ z = 0 := by
      rw [hz, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hM, ha, xx,
        Matrix.zero_mulVec, sub_zero]
    have hB : (cT s Y * J) *ᵥ z = 0 := by
      rw [hz, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, yx, Matrix.one_mulVec, ← hQ, hb,
        sub_self]
    have hh : Formalism.UG.hform s J z z = 0 := by
      rw [hform_eq]
      have e1 : (fun i => s (z i)) = (fun i => s ((C *ᵥ a) i)) - (fun i => s ((X *ᵥ b) i)) := by
        funext i; simp [hz]
      have e2 : (cT s C * J) *ᵥ z = - (M' *ᵥ b) := by
        rw [hz, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, cc, Matrix.zero_mulVec, zero_sub, hM']
      have e3 : (fun i => s (a i)) ᵥ* cT s M = 0 := by
        show _ ᵥ* (M.map s)ᵀ = 0
        rw [Matrix.vecMul_transpose]
        funext i
        have := RingHom.map_mulVec s M a i
        rw [ha] at this
        exact this.symm.trans (by simp)
      rw [e1, sub_dotProduct, dot_cT, dot_cT, hA, dotProduct_zero, sub_zero, e2, dotProduct_neg, neg_eq_zero,
        hMM, Matrix.dotProduct_mulVec, e3, zero_dotProduct]
    have h0 := an z hA hB hh
    rw [← hb]
    rw [hz] at h0
    exact (sub_eq_zero.1 h0).symm
  have hCi : Function.Injective C.mulVec := Matrix.mulVec_injective_iff.2 hC
  let φ : LinearMap.ker M.mulVecLin →ₗ[E] LinearMap.ker M'.mulVecLin :=
    (Q.mulVecLin.comp (LinearMap.ker M.mulVecLin).subtype).codRestrict _ (fun a => by
      have ha : M *ᵥ a.1 = 0 := a.2
      rw [LinearMap.mem_ker]
      show M' *ᵥ (Q *ᵥ a.1) = 0
      rw [hM', ← Matrix.mulVec_mulVec, step a.1 ha, Matrix.mulVec_mulVec, cc, Matrix.zero_mulVec])
  have hφ : Function.Injective φ := by
    refine (injective_iff_map_eq_zero φ).2 fun a h => ?_
    have h1 : Q *ᵥ a.1 = 0 := congrArg Subtype.val h
    have ha : M *ᵥ a.1 = 0 := a.2
    have h2 := step a.1 ha
    rw [h1, Matrix.mulVec_zero] at h2
    exact Subtype.ext (hCi (h2.symm.trans (Matrix.mulVec_zero C).symm))
  have h1 := LinearMap.finrank_le_finrank_of_injective hφ
  have h2 := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  have h3 := LinearMap.finrank_range_add_finrank_ker M'.mulVecLin
  have h4 : M'.rank = M.rank := by
    rw [hMM]
    simp only [cT]
    rw [Matrix.rank_transpose, rank_map_of_invol s hs]
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h2 h3
  have h5 : Module.finrank E (LinearMap.range M.mulVecLin) = M.rank := rfl
  have h6 : Module.finrank E (LinearMap.range M'.mulVecLin) = M'.rank := rfl
  omega

theorem isoFrame_le_wittFrame : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E),
    GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E),
    IsIsoFrame V C → r ≤ m := by
  intro D V m X Y hW r C hC
  have hσ : ∀ x : D.host.E, (D.sp.cm.sig : D.host.E →+* D.host.E) x = star x := fun _ => rfl
  have hJ : cT (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram = V.gram := by
    ext i j
    simp only [cT, Matrix.transpose_apply, Matrix.map_apply, hσ, Formalism.BasicNotions.HSpace.gram]
    exact V.herm.eq (V.frame j) (V.frame i)
  exact le_of_frames (D.sp.cm.sig : D.host.E →+* D.host.E) (fun x => by simp only [hσ, star_star]) V.gram hJ X Y C
    hW.xx (GlobalTheory.WittFrame.yx_eq_one D V m X Y hW) hC.2.2 (fun z h1 h2 h3 => hW.aniso z h1 h2 h3) hC.2.1

end GlobalTheory.CompanionTheory.IsoFrameBound
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsotropicFrameWittBoundStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropic_frame_rank_le_witt_index : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E), IsIsoFrame V C → r ≤ m := by
  first | exact @GlobalTheory.CompanionTheory.IsoFrameBound.isoFrame_le_wittFrame | exact GlobalTheory.CompanionTheory.IsoFrameBound.isoFrame_le_wittFrame | (intros; apply GlobalTheory.CompanionTheory.IsoFrameBound.isoFrame_le_wittFrame <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsotropicFrameRankLeWittIndex
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsotropicFrameRankLeWittIndex
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section
namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice

open GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UEmb (hT_col)
open Formalism.UG (cT)

variable {D : D7} {V V' : HSp D} {ι : V'.V →ₗ[D.host.E] V.V}

theorem frameMat_mulVec (z : Fin V'.rank → D.host.E) :
    frameMat V V' ι *ᵥ z = ⇑(V.frame.repr (ι (V'.frame.equivFun.symm z))) := by
  have h := LinearMap.toMatrix_mulVec_repr V'.frame V.frame ι (V'.frame.equivFun.symm z)
  have hz : ⇑(V'.frame.repr (V'.frame.equivFun.symm z)) = z := funext fun i => repr_symm V' z i
  rw [hz] at h
  exact h

theorem symm_frameMat_mulVec (z : Fin V'.rank → D.host.E) :
    V.frame.equivFun.symm (frameMat V V' ι *ᵥ z) = ι (V'.frame.equivFun.symm z) := by
  rw [frameMat_mulVec]
  have h := V.frame.equivFun.symm_apply_apply (ι (V'.frame.equivFun.symm z))
  rwa [Module.Basis.equivFun_apply] at h

theorem hE_eq_hT (V : HSp D) (a b : Fin V.rank → D.host.E) :
    hE D.sp.cm.sig V.gram a b = V.hT (V.frame.equivFun.symm a) (V.frame.equivFun.symm b) := by
  rw [hT_frame]
  rfl

theorem frameMat_isom (hι : HSpace.IsIsomEmb V' V ι) :
    cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat V V' ι) * V.gram * frameMat V V' ι = V'.gram := by
  rw [cT_frameMat_mul_gram, Matrix.mul_assoc, prM_mul_frameMat hι, Matrix.mul_one]

theorem pairing_submatrix (hι : HSpace.IsIsomEmb V' V ι) {m m' : ℕ} {e : Fin m' → Fin m}
    {A B : Matrix (Fin V.rank) (Fin m) D.host.E} {A' B' : Matrix (Fin V'.rank) (Fin m') D.host.E}
    (hA : frameMat V V' ι * A' = A.submatrix id e) (hB : frameMat V V' ι * B' = B.submatrix id e) :
    cT (D.sp.cm.sig : D.host.E →+* D.host.E) A' * V'.gram * B' =
      (cT (D.sp.cm.sig : D.host.E →+* D.host.E) A * V.gram * B).submatrix e e := by
  have hc : cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat V V' ι * A') =
      cT (D.sp.cm.sig : D.host.E →+* D.host.E) A' * cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat V V' ι) := by
    simp only [Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul]
  have h1 : cT (D.sp.cm.sig : D.host.E →+* D.host.E) A' * V'.gram * B' =
      cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat V V' ι * A') * V.gram * (frameMat V V' ι * B') := by
    rw [← frameMat_isom hι, hc]
    simp only [Matrix.mul_assoc]
  rw [h1, hA, hB]
  ext i j
  simp only [Formalism.UG.cT, Matrix.mul_apply, Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.map_apply, id]

theorem exists_sliceFrame : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (T : Finset (Fin m)) (V' : HSp D) (ι : V'.V →ₗ[D.host.E] V.V), HSpace.IsIsomEmb V' V ι → (∀ v : V.V, v ∈ LinearMap.range ι ↔ ∀ i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T, V.hT (V.frame.equivFun.symm fun j => X j i) v = 0 ∧ V.hT (V.frame.equivFun.symm fun j => Y j i) v = 0) → ∃ (m' : ℕ) (e : Fin m' → Fin m) (X' Y' : Matrix (Fin V'.rank) (Fin m') D.host.E), GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice.IsSliceFrame V V' ι X Y T e X' Y' ∧ GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V'.gram X' Y' := by
  intro D V m X Y hW T V' ι hι hrange
  classical
  obtain ⟨hxx, hyy, hxy, hani⟩ := hW
  have hpair : ∀ {p q : ℕ} (A : Matrix (Fin V.rank) (Fin p) D.host.E)
      (B : Matrix (Fin V.rank) (Fin q) D.host.E) (k : Fin p) (i : Fin q),
      V.hT (V.frame.equivFun.symm fun j => A j k) (V.frame.equivFun.symm fun j => B j i) =
        (cT (D.sp.cm.sig : D.host.E →+* D.host.E) A * V.gram * B) k i := by
    intro p q A B k i
    rw [hT_col V A (fun j => B j i) k]
    rfl
  have hne : ∀ i k, i ∉ upTo T → k ∈ upTo T → i ≠ k := by
    rintro i k hi hk rfl
    exact hi hk
  have hxmem : ∀ i, i ∉ upTo T → (V.frame.equivFun.symm fun j => X j i) ∈ LinearMap.range ι := by
    intro i hi
    rw [hrange]
    intro k hk
    constructor
    · rw [hpair X X k i, hxx, Matrix.zero_apply]
    · rw [← V.herm.eq (V.frame.equivFun.symm fun j => X j i) (V.frame.equivFun.symm fun j => Y j k),
        hpair X Y i k, hxy, Matrix.one_apply_ne (hne i k hi hk), map_zero]
  have hymem : ∀ i, i ∉ upTo T → (V.frame.equivFun.symm fun j => Y j i) ∈ LinearMap.range ι := by
    intro i hi
    rw [hrange]
    intro k hk
    constructor
    · rw [hpair X Y k i, hxy, Matrix.one_apply_ne (hne i k hi hk).symm]
    · rw [hpair Y Y k i, hyy, Matrix.zero_apply]
  set S : Finset (Fin m) := Finset.univ.filter (fun i => i ∉ upTo T) with hS
  have he_mono : StrictMono (fun k => S.orderEmbOfFin rfl k) := (S.orderEmbOfFin rfl).strictMono
  have he_range : ∀ i, i ∉ upTo T ↔ i ∈ Set.range (fun k => S.orderEmbOfFin rfl k) := by
    intro i
    have h : Set.range (fun k => S.orderEmbOfFin rfl k) = (S : Set (Fin m)) :=
      Finset.range_orderEmbOfFin S rfl
    rw [h, hS]
    simp
  have he_out : ∀ k, S.orderEmbOfFin rfl k ∉ upTo T := fun k => (he_range _).2 ⟨k, rfl⟩
  have hx' : ∀ k, ∃ w : V'.V, ι w = V.frame.equivFun.symm fun j => X j (S.orderEmbOfFin rfl k) :=
    fun k => LinearMap.mem_range.1 (hxmem _ (he_out k))
  have hy' : ∀ k, ∃ w : V'.V, ι w = V.frame.equivFun.symm fun j => Y j (S.orderEmbOfFin rfl k) :=
    fun k => LinearMap.mem_range.1 (hymem _ (he_out k))
  choose wx hwx using hx'
  choose wy hwy using hy'
  have hsym : ∀ w : V'.V, V'.frame.equivFun.symm (fun a => V'.frame.repr w a) = w := by
    intro w
    have h := V'.frame.equivFun.symm_apply_apply w
    rw [Module.Basis.equivFun_apply] at h
    exact h
  have hcol : ∀ (Z : Matrix (Fin V.rank) (Fin m) D.host.E) (w : Fin S.card → V'.V),
      (∀ k, ι (w k) = V.frame.equivFun.symm fun j => Z j (S.orderEmbOfFin rfl k)) →
      frameMat V V' ι * Matrix.of (fun a k => V'.frame.repr (w k) a) =
        Z.submatrix id (fun k => S.orderEmbOfFin rfl k) := by
    intro Z w hw
    ext a k
    have h := congrFun (frameMat_mulVec (V := V) (V' := V') (ι := ι)
      (fun b => V'.frame.repr (w k) b)) a
    rw [hsym (w k), hw k, repr_symm] at h
    exact h
  refine ⟨S.card, fun k => S.orderEmbOfFin rfl k, Matrix.of (fun a k => V'.frame.repr (wx k) a),
    Matrix.of (fun a k => V'.frame.repr (wy k) a), ?_, ?_⟩
  · exact And.intro he_mono (And.intro he_range (And.intro (hcol X wx hwx) (hcol Y wy hwy)))
  have hXX := pairing_submatrix hι (hcol X wx hwx) (hcol X wx hwx)
  have hYY := pairing_submatrix hι (hcol Y wy hwy) (hcol Y wy hwy)
  have hXY := pairing_submatrix hι (hcol X wx hwx) (hcol Y wy hwy)
  refine GlobalTheory.SiegelSet.IsWittFrame.mk ?_ ?_ ?_ ?_
  · rw [hXX, hxx]
    rfl
  · rw [hYY, hyy]
    rfl
  · rw [hXY, hxy]
    exact Matrix.submatrix_one _ he_mono.injective
  · intro z' h1 h2 h3
    have hz : frameMat V V' ι *ᵥ z' = 0 := by
      apply hani
      · funext i
        rw [← hT_col, symm_frameMat_mulVec]
        by_cases hi : i ∈ upTo T
        · exact ((hrange _).1 (LinearMap.mem_range_self ι _) i hi).1
        · obtain ⟨k, rfl⟩ := (he_range i).1 hi
          rw [← hwx k, hι (wx k) (V'.frame.equivFun.symm z'), ← hsym (wx k)]
          exact (hT_col V' (Matrix.of fun a k => V'.frame.repr (wx k) a) z' k).trans (congrFun h1 k)
      · funext i
        rw [← hT_col, symm_frameMat_mulVec]
        by_cases hi : i ∈ upTo T
        · exact ((hrange _).1 (LinearMap.mem_range_self ι _) i hi).2
        · obtain ⟨k, rfl⟩ := (he_range i).1 hi
          rw [← hwy k, hι (wy k) (V'.frame.equivFun.symm z'), ← hsym (wy k)]
          exact (hT_col V' (Matrix.of fun a k => V'.frame.repr (wy k) a) z' k).trans (congrFun h2 k)
      · rw [hE_eq_hT, symm_frameMat_mulVec,
          hι (V'.frame.equivFun.symm z') (V'.frame.equivFun.symm z'), ← hE_eq_hT V' z' z']
        exact h3
    have h := congrArg (fun w => prM V V' ι *ᵥ w) hz
    simp only [Matrix.mulVec_mulVec, prM_mul_frameMat hι, Matrix.one_mulVec, Matrix.mulVec_zero] at h
    exact h

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsotropicFrameRankLeWittIndexStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthogonal_subspace_witt_frame_extension : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (T : Finset (Fin m)) (V' : HSp D) (ι : V'.V →ₗ[D.host.E] V.V), HSpace.IsIsomEmb V' V ι → (∀ v : V.V, v ∈ LinearMap.range ι ↔ ∀ i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T, V.hT (V.frame.equivFun.symm fun j => X j i) v = 0 ∧ V.hT (V.frame.equivFun.symm fun j => Y j i) v = 0) → ∃ (m' : ℕ) (e : Fin m' → Fin m) (X' Y' : Matrix (Fin V'.rank) (Fin m') D.host.E), GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice.IsSliceFrame V V' ι X Y T e X' Y' ∧ GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V'.gram X' Y' := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice.exists_sliceFrame | exact GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice.exists_sliceFrame | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice.exists_sliceFrame <;> assumption)
end
end
