module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledSpaceMaximalLevelLattice
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RangeBesselAnisotropicEmbeddingEqSecondModelSubg
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CexpTwoPiINegInvNatSmulAddStar

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CoCptXZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unf.DefCpt

theorem coCpt_X_zero : ∀ (D : D7), GlobalTheory.Unf.CoCpt (D.sp.X 0) := fun D =>
  GlobalTheory.Unf.Inhab.coCpt_of_isAniso
    (GlobalTheory.BesselConvDefinite.isAniso_of_isDefinite (D.sp.X 0) (D.sp.X_sig 0) (D.sp.X_def 0 (Nat.zero_le _)))

end GlobalTheory.Unf.DefCpt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransportedFrameGramOrth
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi

theorem transported_frame_gram_orth : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (F₀ : Formalism.L2.Forms.Forms0 D u) (tr : Formalism.L2.SG.ColDict.Transport X u F₀) (i j : Fin (D.sp.X 0).rank) (a : Fin D.R.rS), (VS D).hT (Formalism.L2.SG.ColDict.qFr tr.wt (Fin.cast (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) i)) (Formalism.L2.SG.ColDict.qFr tr.wt (Fin.cast (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) j)) = (D.sp.X 0).gram i j ∧ (VS D).hT (Formalism.L2.SG.ColDict.qFr tr.wt (Fin.cast (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) i)) (X.eX a) = 0 ∧ (VS D).hT (Formalism.L2.SG.ColDict.qFr tr.wt (Fin.cast (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) i)) (X.fY a) = 0 ∧ (VS D).hT (X.zu u) (Formalism.L2.SG.ColDict.qFr tr.wt (Fin.cast (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) i)) = 0 := by
  intro D X u F₀ tr i j a
  have key : ∀ (x y : (VS D).V), (VS D).hT (tr.wt.symm x) (tr.wt.symm y) = (VS D).hT x y := by
    intro x y
    rw [← tr.wt_isom, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  have key2 : ∀ (x y : (VS D).V), (VS D).hT (tr.wt.symm x) y = (VS D).hT x (tr.wt y) := by
    intro x y
    rw [← tr.wt_isom, LinearEquiv.apply_symm_apply]
  have key3 : ∀ (x y : (VS D).V), (VS D).hT x (tr.wt.symm y) = (VS D).hT (tr.wt x) y := by
    intro x y
    rw [← tr.wt_isom, LinearEquiv.apply_symm_apply]
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Formalism.L2.SG.ColDict.qFr, Formalism.L2.SG.ColDict.xFr, key, Fin.cast_cast, Fin.cast_eq_self]
    exact D.sp.iXY_isom 0 hm _ _
  · simp only [Formalism.L2.SG.ColDict.qFr, Formalism.L2.SG.ColDict.xFr, key2, tr.wt_e]
    exact (D.sp.hyp_orthX a _).1
  · simp only [Formalism.L2.SG.ColDict.qFr, Formalism.L2.SG.ColDict.xFr, key2, tr.wt_f]
    exact (D.sp.hyp_orthX a _).2
  · simp only [Formalism.L2.SG.ColDict.qFr, Formalism.L2.SG.ColDict.xFr, key3, tr.weight_z]
    exact Formalism.MainNotions.BridgeLemma₂.z_orth_embedding D u _

end GlobalTheory.Core.Mi
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHypDec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.SBesEx

theorem gram_scaled {E : Type} [Field E] [StarRing E] {n k l : Type} [Fintype n] (G : Matrix n n E)
    (A : Matrix n k E) (B : Matrix n l E) (α : k → E) (β : l → E) (x : k → n → E) (y : l → n → E)
    (hA : ∀ i a, A i a = α a * x a i) (hB : ∀ i b, B i b = β b * y b i) (a : k) (b : l) :
    (Aᴴ * G * B) a b = star (α a) * β b * (star (x a) ⬝ᵥ (G *ᵥ y b)) := by
  rw [Matrix.mul_assoc]
  simp only [Matrix.mul_apply, conjTranspose_apply, hA, hB, dotProduct, mulVec, Pi.star_apply, Finset.mul_sum,
    star_mul']
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem gram_sum {E : Type} [Field E] [StarRing E] {n k l m : Type} [Fintype n] [Fintype k] [Fintype l]
    (G : Matrix n n E) (I : Matrix n k E) (J : Matrix n l E) (P : Matrix k m E) (Q : Matrix l m E)
    (hIJ : Iᴴ * G * J = 0) (hJI : Jᴴ * G * I = 0) :
    (I * P + J * Q)ᴴ * G * (I * P + J * Q) = Pᴴ * (Iᴴ * G * I) * P + Qᴴ * (Jᴴ * G * J) * Q := by
  have e : (I * P + J * Q)ᴴ * G * (I * P + J * Q) =
      Pᴴ * (Iᴴ * G * I) * P + Qᴴ * (Jᴴ * G * J) * Q + Pᴴ * (Iᴴ * G * J) * Q + Qᴴ * (Jᴴ * G * I) * P := by
    simp only [conjTranspose_add, conjTranspose_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
    abel
  rw [e, hIJ, hJI]
  simp

theorem gram_sum_zero {E : Type} [Field E] [StarRing E] {n k l m p : Type} [Fintype n] [Fintype k] [Fintype l]
    (G : Matrix n n E) (I : Matrix n k E) (J : Matrix n l E) (P : Matrix k m E) (Q : Matrix l m E) (C : Matrix n p E)
    (hI : Iᴴ * G * C = 0) (hJ : Jᴴ * G * C = 0) :
    (I * P + J * Q)ᴴ * G * C = 0 := by
  have e : (I * P + J * Q)ᴴ * G * C = Pᴴ * (Iᴴ * G * C) + Qᴴ * (Jᴴ * G * C) := by
    simp only [conjTranspose_add, conjTranspose_mul, Matrix.add_mul, Matrix.mul_assoc]
  rw [e, hI, hJ]
  simp

theorem exists_hypDec : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (F₀ : Formalism.L2.Forms.Forms0 D u) (tr : Formalism.L2.SG.ColDict.Transport X u F₀) (t lam : D.host.E), t ≠ 0 → lam ≠ 0 → (∀ y y' : (VS D).V, star (GlobalTheory.Core.SBesEx.cY X h y') ⬝ᵥ ((D.sp.Y 0).gram *ᵥ GlobalTheory.Core.SBesEx.cY X h y) = (VS D).hT y' y) → (∀ (i j : Fin (D.sp.X 0).rank) (a : Fin D.R.rS), (VS D).hT (Formalism.L2.SG.ColDict.qFr tr.wt (Fin.cast (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) i)) (Formalism.L2.SG.ColDict.qFr tr.wt (Fin.cast (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) j)) = (D.sp.X 0).gram i j ∧ (VS D).hT (Formalism.L2.SG.ColDict.qFr tr.wt (Fin.cast (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) i)) (X.eX a) = 0 ∧ (VS D).hT (Formalism.L2.SG.ColDict.qFr tr.wt (Fin.cast (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) i)) (X.fY a) = 0 ∧ (VS D).hT (X.zu u) (Formalism.L2.SG.ColDict.qFr tr.wt (Fin.cast (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) i)) = 0) → ∀ (L : HSp D), L.rank = 1 → (∀ i j, L.gram i j = star t * t * (VS D).hT (X.zu u) (X.zu u)) → ∀ (V₀ : HSp D) (o : OrthDec V₀ (D.sp.X 0) L), ∃ d : HypDec (D.sp.Y 0) V₀ D.R.rS, d.e = GlobalTheory.Core.SBesEx.eM X h t lam ∧ d.e' = GlobalTheory.Core.SBesEx.e'M X h t lam ∧ d.i₀ = GlobalTheory.Core.SBesEx.i0M X h u tr.wt t o := by
  intro D X h u F₀ tr t lam ht hlam hiso hfr L hL hLg V₀ o
  have hsym : ∀ x y : (VS D).V, (VS D).hT y x = star ((VS D).hT x y) := fun x y =>
    (LinearMap.isSymm_def.1 (VS D).herm x y).symm
  have hs : ∀ a : Fin D.R.rS, star (scl t lam a) ≠ 0 := fun a =>
    star_ne_zero.2 (mul_ne_zero ht (pow_ne_zero _ hlam))
  set q : Fin (D.sp.X 0).rank → (VS D).V := fun i =>
    Formalism.L2.SG.ColDict.qFr tr.wt (Fin.cast (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) i) with hq
  have hE : ∀ i a, eM X h t lam i a = scl t lam a * cY X h (X.eX a) i := fun _ _ => rfl
  have hE' : ∀ i a, e'M X h t lam i a = (star (scl t lam a))⁻¹ * cY X h (X.fY a) i := fun _ _ => rfl
  have hQ : ∀ i a, qM X h tr.wt i a = (1 : D.host.E) * cY X h (q a) i := fun _ _ => (one_mul _).symm
  have hZ : ∀ i a, zM X h u t L i a = t * cY X h (X.zu u) i := fun _ _ => rfl
  have hzq : ∀ i, (VS D).hT (X.zu u) (q i) = 0 := by
    intro i
    rw [hsym, ← tr.wt_isom, tr.weight_z]
    simp only [hq, Formalism.L2.SG.ColDict.qFr, LinearEquiv.apply_symm_apply, Formalism.L2.SG.ColDict.xFr, D7.zmOf, map_smul]
    rw [D.sp.zm_orth, smul_zero, star_zero]
  have hqq : ∀ i j, (VS D).hT (q i) (q j) = (D.sp.X 0).gram i j := by
    intro i j
    rw [← tr.wt_isom]
    simp only [hq, Formalism.L2.SG.ColDict.qFr, LinearEquiv.apply_symm_apply, Formalism.L2.SG.ColDict.xFr]
    rw [D.sp.iXY_isom 0 (lt_of_lt_of_le two_pos D.R.two_le_m)]
    rfl
  have hQZ : (qM X h tr.wt)ᴴ * (D.sp.Y 0).gram * zM X h u t L = 0 := by
    ext a b
    rw [gram_scaled _ _ _ _ (fun _ => t) _ (fun _ => cY X h (X.zu u)) hQ hZ, hiso, hsym, hzq]
    simp
  have hZQ : (zM X h u t L)ᴴ * (D.sp.Y 0).gram * qM X h tr.wt = 0 := by
    ext a b
    rw [gram_scaled _ _ _ (fun _ => t) _ (fun _ => cY X h (X.zu u)) _ hZ hQ, hiso, hzq]
    simp
  have hQQ : (qM X h tr.wt)ᴴ * (D.sp.Y 0).gram * qM X h tr.wt = (D.sp.X 0).gram := by
    ext a b
    rw [gram_scaled _ _ _ _ _ _ _ hQ hQ, hiso, hqq]
    simp
  have hZZ : (zM X h u t L)ᴴ * (D.sp.Y 0).gram * zM X h u t L = L.gram := by
    ext a b
    rw [gram_scaled _ _ _ (fun _ => t) (fun _ => t) (fun _ => cY X h (X.zu u)) (fun _ => cY X h (X.zu u)) hZ hZ,
      hiso, hLg]
  refine ⟨⟨eM X h t lam, e'M X h t lam, i0M X h u tr.wt t o, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl, rfl, rfl⟩
  · ext a b
    rw [gram_scaled _ _ _ _ _ _ _ hE hE, hiso, X.ee]
    simp
  · ext a b
    rw [gram_scaled _ _ _ _ _ _ _ hE' hE', hiso, X.ff]
    simp
  · ext a b
    rw [gram_scaled _ _ _ _ _ _ _ hE' hE, hiso, hsym, X.ef, Matrix.one_apply]
    by_cases hab : a = b
    · subst hab
      have := hs a
      rw [star_ne_zero] at this
      simp [this]
    · simp [hab, Ne.symm hab]
  · rw [i0M, gram_sum _ _ _ _ _ hQZ hZQ, hQQ, hZZ]
    have := gram_sum V₀.gram o.iA o.iB o.qA o.qB o.orth' o.orth
    rw [o.iA_qA_add, o.isoA, o.isoB] at this
    rw [← this]
    simp
  · refine gram_sum_zero _ _ _ _ _ _ ?_ ?_
    · ext a b
      rw [gram_scaled _ _ _ _ _ _ _ hQ hE, hiso, (hfr a a b).2.1]
      simp
    · ext a b
      rw [gram_scaled _ _ _ (fun _ => t) _ (fun _ => cY X h (X.zu u)) _ hZ hE, hiso, hsym, (X.zu_orth u b).1]
      simp
  · refine gram_sum_zero _ _ _ _ _ _ ?_ ?_
    · ext a b
      rw [gram_scaled _ _ _ _ _ _ _ hQ hE', hiso, (hfr a a b).2.2.1]
      simp
    · ext a b
      rw [gram_scaled _ _ _ (fun _ => t) _ (fun _ => cY X h (X.zu u)) _ hZ hE', hiso, hsym, (X.zu_orth u b).2]
      simp
  · have h1 := o.rank_add
    have h2 := D.sp.X_rank 0 (Nat.zero_le _)
    have h3 := D.sp.Y_rank 0 (Nat.zero_le _)
    have h4 := D.R.two_le_m
    obtain ⟨c, hc⟩ := D.R.m_even
    simp only [Ranks.N, Ranks.rankY, Ranks.r, Ranks.rS, zero_mul, add_zero] at h2 h3 ⊢
    omega

end GlobalTheory.Core.SBesEx

end
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi.Unscaled

variable {D : D7}

def rescale {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (μ : D.host.E) (hμ : μ ≠ 0) : HypDec S S₀ ρ where
  e := μ • d.e
  e' := (star μ)⁻¹ • d.e'
  i₀ := d.i₀
  ee := by simp only [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, d.ee, smul_zero]
  e'e' := by simp only [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, d.e'e', smul_zero]
  e'e := by
    simp only [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, d.e'e, smul_smul, star_inv₀, star_star,
      mul_inv_cancel₀ hμ, one_smul]
  iso := d.iso
  i₀e := by simp only [Matrix.mul_smul, d.i₀e, smul_zero]
  i₀e' := by simp only [Matrix.mul_smul, d.i₀e', smul_zero]
  rank_add := d.rank_add

end GlobalTheory.Core.Mi.Unscaled

namespace GlobalTheory.Core.Mi


open GlobalTheory.Core.SBesEx GlobalTheory.Core.Mi.Unscaled in
theorem exists_sBes_scaled_dual : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (F₀ : Formalism.L2.Forms.Forms0 D u) (tr : Formalism.L2.SG.ColDict.Transport X u F₀), IdE X → IsStdChar D ψ (-1) → ∃ lam : D.host.E, (lam = (X.B.g : D.host.E) ∨ lam = -(X.B.g : D.host.E)) ∧ ∀ (μ : D.host.E) (vA : Vol (D.sp.X 0)), μ ≠ 0 → ∃ B : SBes X h u ψ (D.sp.X 0), B.Adapted tr.wt ∧ B.vA = vA ∧ (∀ k, (B.d.i₀ *ᵥ vecB B.o B.ζ) k = μ * X.ιE (X.zR u (Fin.cast (rank_eq X h) k))) ∧ (∀ k (a : Fin D.R.rS), B.d.e k a = μ * lam ^ (D.R.rS - (a : ℕ)) * X.ιE (X.eR a (Fin.cast (rank_eq X h) k))) ∧ ∀ k (a : Fin D.R.rS), B.d.e' k a = (star (μ * lam ^ (D.R.rS - (a : ℕ))))⁻¹ * X.ιE (X.fR a (Fin.cast (rank_eq X h) k)) := by
  intro D X h u ψ F₀ tr hE hψ
  obtain ⟨lam, hlam, hP⟩ := GlobalTheory.Core.Mi.tiepsi_sign D X h u ψ hE hψ
  have hg : ((X.B.g : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (Formalism.L2.SG.Pf.modulus_g_ne_zero X)
  have hl0 : lam ≠ 0 := by
    rcases hlam with hl | hl <;> rw [hl]
    · exact hg
    · exact neg_ne_zero.2 hg
  refine ⟨lam, hlam, fun μ vA hμ => ?_⟩
  obtain ⟨L, t, ht, hL1, hz0, hLg⟩ := GlobalTheory.RankOneLine.exists_line D X u
  obtain ⟨⟨V₀, o⟩⟩ := GlobalTheory.OrthSumExists.exists_orthDec D (D.sp.X 0) L
  obtain ⟨d₀, hde, hde', hdi⟩ := GlobalTheory.Core.SBesEx.exists_hypDec D X h u F₀ tr t lam ht hl0 (GlobalTheory.Core.SBesEx.cY_isom D X h hE)
    (GlobalTheory.Core.Mi.transported_frame_gram_orth D X u F₀ tr) L hL1 hLg V₀ o
  have hcard : Fintype.card (Fin L.rank) = 1 := by rw [Fintype.card_fin, hL1]
  have hz₀ : d₀.i₀ *ᵥ vecB o (zeta L) = t • cY X h (X.zu u) := by
    rw [vecB, Matrix.mulVec_mulVec, hdi, i0M, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, o.qA_iB, o.qB_iB,
      Matrix.mul_zero, zero_add, Matrix.mul_one]
    funext k
    simp only [Matrix.mulVec, dotProduct, zM, zeta, mul_one, Finset.sum_const, Finset.card_univ, hcard, one_smul,
      Pi.smul_apply, smul_eq_mul]
  have hline₀ : IsLineVec L (zeta L) := by
    refine ⟨hL1, ?_⟩
    simp only [zeta, hLg, dotProduct, Matrix.mulVec, Pi.star_apply, star_one, one_mul, mul_one, Finset.sum_const,
      Finset.card_univ, hcard, one_smul]
    exact mul_ne_zero (mul_ne_zero (star_ne_zero.2 ht) ht) hz0
  have ht' : μ * t⁻¹ ≠ 0 := mul_ne_zero hμ (inv_ne_zero ht)
  set d := rescale d₀ (μ * t⁻¹) ht' with hd
  set ζ : Fin L.rank → D.host.E := (μ * t⁻¹) • zeta L with hζ
  have hline : IsLineVec L ζ := by
    refine ⟨hline₀.1, ?_⟩
    rw [hζ, star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    exact mul_ne_zero (star_ne_zero.2 ht') (mul_ne_zero ht' hline₀.2)
  have hde1 : d.e = eM X h μ lam := by
    funext k a
    show ((μ * t⁻¹) • d₀.e) k a = _
    rw [hde]
    simp only [Matrix.smul_apply, eM, scl, smul_eq_mul]
    field_simp
  have hde1' : d.e' = e'M X h μ lam := by
    funext k a
    show ((star (μ * t⁻¹))⁻¹ • d₀.e') k a = _
    rw [hde']
    simp only [Matrix.smul_apply, e'M, scl, smul_eq_mul, star_mul', star_inv₀, inv_inv, mul_inv]
    have hst : star t ≠ 0 := star_ne_zero.2 ht
    field_simp
  have hz : d.i₀ *ᵥ vecB o ζ = μ • cY X h (X.zu u) := by
    show d₀.i₀ *ᵥ (o.iB *ᵥ ((μ * t⁻¹) • zeta L)) = _
    rw [Matrix.mulVec_smul, Matrix.mulVec_smul, ← vecB, hz₀, smul_smul, inv_mul_cancel_right₀ ht]
  refine ⟨SBes.mk V₀ L d o ζ hline (GlobalTheory.Unf.DefCpt.coCpt_X_zero D) vA
    (GlobalTheory.Unf.Inhab.nonempty_volN d).some (GlobalTheory.T.mem_flagUnipotentRadical_iff_secondModel D X h u μ lam hμ hl0 hE V₀ d hde1)
    (GlobalTheory.T.range_besselAnisotropicEmbedding_eq_secondModelSubgroup D X h u μ lam hμ hl0 hE V₀ L d o ζ hline hde1 hde1' hz)
    (hP μ hμ V₀ L d o ζ hde1 hde1' hz), ?_, rfl, ?_, ?_, ?_⟩
  · intro k j
    show (d₀.i₀ * o.iA) k j = _
    rw [hdi, i0M, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, o.qA_iA, o.qB_iA, Matrix.mul_zero, add_zero,
      Matrix.mul_one]
    rfl
  · intro k
    show (d.i₀ *ᵥ vecB o ζ) k = _
    rw [hz]
    rfl
  · intro k a
    show d.e k a = _
    rw [hde1]
    rfl
  · intro k a
    show d.e' k a = _
    rw [hde1']
    rfl

end GlobalTheory.Core.Mi

end
