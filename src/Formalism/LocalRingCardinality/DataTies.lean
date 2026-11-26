module

public import Formalism.LocalRingCardinality.DataNChTie
public import Formalism.LocalRingCardinality.DataParams
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.LocalRingCardinality.DataDIV
public import Formalism.SharpRestriction.GrowthBounds.IsResidueClassZero

@[expose] public section

section -- merged from Formalism.LocalRingCardinality.DataTies
open MeasureTheory Matrix Formalism.MainNotions.S

noncomputable section

namespace Formalism.BasicNotions

def cdScaleTie (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (P Q : ℕ) (e : Fin P ⊕ Fin Q ≃ Fin n),
    (∀ i, ε (e (Sum.inl i)) = true) → (∀ j, ε (e (Sum.inr j)) = false) →
    ∀ A : Set (Formalism.REAL.UJ ε), MeasurableSet A →
      ((D.s.cdScale n ε : ENNReal) • Formalism.REAL.muG ε) A =
        D.cd.cd P Q {g | ∃ a ∈ A, umat a = Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g)}

def dsigTie (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (τ : D.what₂.Tau) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ → (H →L[ℂ] H)) (d : ℝ),
    IsDS (epsSH D.R) (lamSH D.R (D.hc τ)) σ →
    IsFdeg ((D.s.cdScale _ (epsSH D.R) : ENNReal) • Formalism.REAL.muG (epsSH D.R)) σ d → d = D.dsig τ

def TwCoverPair (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ p : ℕ, p.Prime → ∀ w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥D.LL0),
    ((p : ℕ) : NumberField.RingOfIntegers ↥D.LL0) ∈ w.asIdeal →
    (∃ w' : D.what₂.places.Pl, D.what₂.muAt w' ≠ D.what₂.mu0 ∧
      ∀ x : NumberField.RingOfIntegers ↥D.LL0, x ∈ w.asIdeal ↔ 0 < D.what₂.places.val w' ((x : ↥D.LL0) : D.what₂.LL)) →
    ∃ i, D.ntw.l i = p ∧
      ((∀ x : NumberField.RingOfIntegers ↥D.LL0, x ∈ w.asIdeal ↔ ∃ y ∈ IsLocalRing.maximalIdeal (D.ntw.O0 i),
          algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) y = D.ntw.emb0 i (x : ↥D.LL0)) ∨
       (∀ x : NumberField.RingOfIntegers ↥D.LL0, x ∈ w.asIdeal ↔ ∃ y ∈ IsLocalRing.maximalIdeal (D.ntw.O0 i),
          algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) y = D.ntw.emb0b i (x : ↥D.LL0)))

structure Ties (D : D7) : Prop where
  cdScale_tie : cdScaleTie D
  dsig_tie : dsigTie D

  bu_def : Rows.BuDefQ D.what₂

  tw_cover : TwCoverPair D

  baseField_isGalois : IsGalois ℚ ↥D.LL0

  ft_occ : ∀ π, (∃ σ, D.what₂.ft σ = π) ∨ ∃ σ, D.what₂.ft0 σ = π

def GoodFTAll (D : Formalism.BasicNotions.D7) : Prop := ∀ σ, D.nd.goodRow σ

end Formalism.BasicNotions

end
end

section -- merged from Formalism.LocalRingCardinality.DataParamsT
noncomputable section

namespace Formalism.BasicNotions

open NumberField LevelStarExponents

def logdE (D : D7) : ℝ := Real.log |((discr D.host.E : ℤ) : ℝ)|

def zBase {D : D7} (L : SizeData₂ D) : ℝ := (D.R.f : ℝ) * (D.R.r : ℝ) * L.sc.L

structure ParamsT (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) : Type where

  TO : ℕ

  nWn : ℕ

  nP : ℕ

  PP : ℝ

  Dp : ℕ

  s : ℕ

  CP : ℝ
  one_le_CP : 1 ≤ CP

  eP : ℝ
  eP_ge : 12 ≤ eP

  Cp : ℝ
  Cp_ge : 1 ≤ Cp

  Cb : ℝ
  Cb_nonneg : 0 ≤ Cb

  cTO : ℝ

  ChT : ℝ
  ChT_ge : 1 ≤ ChT

  CbN : ℝ
  CbN_ge : 1 ≤ CbN

  PP_eq : PP = CP * zBase L ^ eP

  Dp_eq : Dp = D.R.f * D.R.r.choose 2

  PP_poly : PP ≤ L.sc.x ^ L.Ct
  Dp_poly : (Dp : ℝ) ≤ L.sc.x ^ L.Ct
  TO_poly : (TO : ℝ) ≤ L.sc.x ^ L.Ct

  nW_win : nW L P.CnW ≤ (nWn : ℝ) ∧ (nWn : ℝ) < nW L P.CnW + 8
  nW_dvd : 8 ∣ nWn

  PP_nW : (2 * (D.R.f : ℝ) * D.R.m) ^ 4 * (nWn : ℝ) ≤ PP

  nW_le : (nWn : ℝ) ≤ PP

  nW_lo : D.R.f * D.R.r * (D.R.r + 1) ≤ nWn ∧ (D.R.k - 1) * D.R.f + 2 * D.R.r ≤ nWn ∧ nP ≤ nWn

  split : D.R.r + D.R.t = nP + TO * nWn
  nP_eq : nP = 8 * D.R.f * D.R.r + 4

  TO_eq : TO = ⌈L.sc.x ^ cTO⌉₊

  TO_ge : PP ^ 4 * (Dp : ℝ) ^ 3 * D.R.k * D.R.f * L.sc.x ^ Cp / ((D.R.m : ℝ) * L.de2) ≤ (TO : ℝ)

  TO_PP : (TO : ℝ) * PP * L.sc.x ^ Cb ≤ L.sc.b

  TO_nW : (Dp + 2) * nWn + 2 * D.R.r ≤ TO

  TO_40 : 40 * (Dp + 2) ≤ TO

  TO_11D2 : 11 * Dp ^ 2 ≤ TO

  order_ge_rank_bound : D.R.r + 2 * (2 * 5 ^ 4 * D.R.r) * (Dp + 1) ≤ TO

  TO_PP' : (TO : ℝ) * PP ≤ L.sc.b ^ (1 / 2 : ℝ)

  precision_cube_order_sq_le : PP ^ 3 * (TO : ℝ) ^ 2 * L.sc.x ^ Cb ≤ L.sc.b

  precision_cube_order_sq_le_sqrt : PP ^ 3 * (TO : ℝ) ^ 2 ≤ L.sc.b ^ (1 / 2 : ℝ)

  TO_Dk : (Dp : ℝ) * D.R.k / D.R.m ≤ (TO : ℝ)

  Del_TO : ((TO : ℝ)) ^ 2 ≤ ((D.s.Del : ℚ) : ℝ)

  Del_gap : ((TO : ℝ) + Dp + 2) * ((TO : ℝ) + Dp + 2 + 2 * (D.R.N D.R.m : ℝ)) ≤ ((D.s.Del : ℚ) : ℝ)

  heightBound_ge_order_sq : 4 * (TO : ℝ) ^ 2 + 2 * D.R.t ≤ h0 L

  heightBound_ge_precision_degree : PP * Dp * D.R.f * (D.R.m : ℝ) ^ 2 * (D.R.N D.R.m : ℝ) * TO ≤ h0 L

  heightBound_ge_precision_cubic : PP * ((D.R.f : ℝ) * D.R.m * D.R.k) ^ 3 * D.R.k / D.R.m ≤ h0 L

  heightBound_ge_order_product : ChT * TO * (D.R.N D.R.m : ℝ) * (D.R.f : ℝ) ^ 2 * (D.R.m : ℝ) ^ 2 * D.R.k * Dp * PP ≤ h0 L

  log_bound_le_sqrt : (TO : ℝ) * (Dp : ℝ) ^ 2 * Real.log L.sc.b * L.sc.x ^ Cb ≤ L.sc.b

  TD2' : (TO : ℝ) * (Dp : ℝ) ^ 2 * Real.log L.sc.b ≤ L.sc.b ^ (1 / 2 : ℝ)

  b_ge : CbN * (D.R.r : ℝ) * D.R.m * D.R.k * PP ^ 2 * (Dp : ℝ) ^ 3 ≤ L.sc.b

  s_odd : Odd s
  s_lo : D.R.r + 5 < s
  s_hi : s ≤ D.R.r + 7

theorem ParamsT.Cp_nonneg {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (T : ParamsT D L P) : 0 ≤ T.Cp :=
  le_trans zero_le_one T.Cp_ge

theorem ParamsT.nW_40 {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (T : ParamsT D L P) : 40 ≤ T.nWn := by
  have hf : 2 ≤ D.R.f := by
    have := D.R.ord_pos
    unfold Ranks.f Ranks.n; omega
  have hr : 6 ≤ D.R.r := by
    have h1 := D.R.two_le_m
    have h2 := D.R.m_add_three_le_k
    unfold Ranks.r; omega
  have h3 : 2 * 6 * (6 + 1) ≤ D.R.f * D.R.r * (D.R.r + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul hf hr) (by omega)
  exact le_trans (by norm_num) (le_trans h3 T.nW_lo.1)

theorem ParamsT.nW_even {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (T : ParamsT D L P) : Even T.nWn :=
  (even_iff_two_dvd.2 (Dvd.dvd.trans (by norm_num) T.nW_dvd))

theorem ParamsT.nP_ge {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (T : ParamsT D L P) :
    8 * D.R.f * D.R.r + 4 ≤ T.nP := T.nP_eq.ge

theorem ParamsT.four_dvd_nP {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (T : ParamsT D L P) : 4 ∣ T.nP := by
  rw [T.nP_eq]; exact ⟨2 * D.R.f * D.R.r + 1, by ring⟩

theorem ParamsT.even_nP₂ {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (T : ParamsT D L P) : Even T.nP :=
  even_iff_two_dvd.2 (Dvd.dvd.trans (by norm_num) T.four_dvd_nP)

theorem ParamsT.PP_pos {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (T : ParamsT D L P)
    (hZ : 0 < zBase L) : 0 < T.PP := by
  rw [T.PP_eq]; have := T.one_le_CP; positivity

end Formalism.BasicNotions

end
end

section -- merged from Formalism.LocalRingCardinality.PosOfIsomEmb
noncomputable section

namespace Formalism.BasicNotions

open NumberField

section gen

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem HSpace.pos_of_isomEmb (A B : HSpace E) (ι : A.V →ₗ[E] B.V) (hι : HSpace.IsIsomEmb A B ι)
    (hA : A.SigOK) (hB : B.SigOK) (τ : E →+* ℂ) (hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a))
    (hdef : A.sig τ = (A.rank, 0) ∨ A.sig τ = (0, A.rank)) (hlt : (B.sig τ).2 < A.rank) :
    A.sig τ = (A.rank, 0) := by
  rcases hdef with h | h
  · exact h
  · exfalso
    have hw : (Matrix.of fun i j => B.hT (ι (A.frame i)) (ι (A.frame j))) = A.gram := by
      ext i j; exact hι _ _
    have hsA := hA τ
    rw [h, ← hw] at hsA
    have key := (sig_family B τ hτ _ hsA (hB τ)).2
    have hs := sig_sum B hB τ
    simp only at key
    omega

theorem HSpace.frame_of_pos (S : HSpace E) (σ : E →+* ℂ)
    (hσ : ∀ a, σ (star a) = (starRingEnd ℂ) (σ a)) (h : Formalism.UG.HasSignature (S.gram.map σ) S.rank 0) :
    ∃ Y : Matrix (Fin S.rank) (Fin S.rank) ℂ, IsUnit Y.det ∧
      ∀ y : S.V, ∑ i, ‖(Y.mulVec fun j => σ (S.frame.repr y j)) i‖ ^ 2 = (σ (S.hT y y)).re := by
  obtain ⟨e, P, hP⟩ := h
  have hJ : Formalism.UG.Jpq S.rank 0 = 1 := by
    ext i j
    rcases i with i | i
    · rcases j with j | j
      · simp [Formalism.UG.Jpq, Matrix.one_apply]
      · exact j.elim0
    · exact i.elim0
  set Pm : Matrix (Fin S.rank ⊕ Fin 0) (Fin S.rank ⊕ Fin 0) ℂ := P.val with hPm
  set Qm : Matrix (Fin S.rank ⊕ Fin 0) (Fin S.rank ⊕ Fin 0) ℂ := (P⁻¹).val with hQm
  have hPQ : Pm * Qm = 1 := by rw [hPm, hQm, ← Units.val_mul, mul_inv_cancel]; rfl
  have hcT : Formalism.UG.cT (starRingEnd ℂ) Pm = Pm.conjTranspose := by
    ext i j; simp [Formalism.UG.cT, Matrix.conjTranspose_apply]
  rw [hcT, hJ] at hP
  set G : Matrix (Fin S.rank) (Fin S.rank) ℂ := S.gram.map σ with hG
  have hGr : G.reindex e e = Qm.conjTranspose * Qm := by
    have h1 : Qm.conjTranspose * (Pm.conjTranspose * G.reindex e e * Pm) * Qm = Qm.conjTranspose * Qm := by
      rw [hP, Matrix.mul_one]
    have h2 : Qm.conjTranspose * Pm.conjTranspose = 1 := by
      rw [← Matrix.conjTranspose_mul, hPQ, Matrix.conjTranspose_one]
    rw [← h1]
    calc G.reindex e e = (Qm.conjTranspose * Pm.conjTranspose) * G.reindex e e * (Pm * Qm) := by
          rw [h2, hPQ, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  let Y : Matrix (Fin S.rank) (Fin S.rank) ℂ := Qm.submatrix e e
  have hGY : G = Y.conjTranspose * Y := by
    have : G = (G.reindex e e).submatrix e e := by ext i j; simp
    rw [this, hGr]
    ext i j
    simp only [Y, Matrix.submatrix_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
    exact (Equiv.sum_comp e _).symm
  refine ⟨Y, ?_, fun y => ?_⟩
  · have : Y.det = Qm.det := Matrix.det_submatrix_equiv_self e Qm
    rw [this]
    exact (Matrix.isUnit_iff_isUnit_det _).mp ⟨P⁻¹, rfl⟩
  · set z : Fin S.rank → ℂ := fun j => σ (S.frame.repr y j) with hz
    have h1 : ∑ i, ‖(Y.mulVec z) i‖ ^ 2 = (star (Y.mulVec z) ⬝ᵥ Y.mulVec z).re := by
      simp [dotProduct, Complex.mul_re, Complex.sq_norm, Complex.normSq_apply]
    have h2 : star (Y.mulVec z) ⬝ᵥ Y.mulVec z = star z ⬝ᵥ G.mulVec z := by
      rw [hGY, Matrix.star_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec (star z)]
    have h3 : σ (S.hT y y) = star z ⬝ᵥ G.mulVec z := by
      have := LinearMap.sum_repr_mul_repr_mulₛₗ S.frame S.frame (B := S.hT) y y
      rw [← this, Finsupp.sum_fintype _ _ (by intro i; simp)]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [dotProduct, Matrix.mulVec, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Finsupp.sum_fintype _ _ (by intro j; simp), map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [smul_eq_mul, map_mul, RingHom.id_apply, hG, hz, Matrix.map_apply, HSpace.gram, Pi.star_apply]
      rw [starRingEnd_apply, hσ]
      simp only [starRingEnd_apply]
      ring
    rw [h1, h2, h3]

theorem HSpace.form_pos (S : HSpace E) (hS : S.SigOK) (τ : E →+* ℂ)
    (hτ : ∀ a, τ (star a) = (starRingEnd ℂ) (τ a)) (h : S.sig τ = (S.rank, 0)) (x : S.V) (hx : x ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ τ (S.hT x x) = (c : ℂ) := by
  have hsig := hS τ
  rw [h] at hsig
  obtain ⟨Y, hY, hsum⟩ := S.frame_of_pos τ hτ hsig
  have hz : (fun j => τ (S.frame.repr x j)) ≠ 0 := by
    intro h0
    apply hx
    apply S.frame.repr.injective
    ext j
    have := congrFun h0 j
    simpa using this
  have hYz : Y.mulVec (fun j => τ (S.frame.repr x j)) ≠ 0 := by
    intro h0
    apply hz
    have hinj : Function.Injective Y.mulVec :=
      Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det Y).mpr hY)
    exact hinj (by rw [h0, Matrix.mulVec_zero])
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hYz
  have hpos : 0 < (τ (S.hT x x)).re := by
    rw [← hsum x]
    refine Finset.sum_pos' (fun j _ => by positivity) ⟨i, Finset.mem_univ _, ?_⟩
    have : 0 < ‖(Y.mulVec fun j => τ (S.frame.repr x j)) i‖ := norm_pos_iff.mpr hi
    positivity
  have hre : τ (S.hT x x) = starRingEnd ℂ (τ (S.hT x x)) := by
    rw [← hτ]
    congr 1
    exact ((S.herm.eq x x)).symm
  refine ⟨(τ (S.hT x x)).re, hpos, ?_⟩
  apply Complex.ext
  · simp
  · have := congrArg Complex.im hre
    simp only [Complex.conj_im] at this
    simp only [Complex.ofReal_im]
    linarith

end gen

section spaces

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
  [Algebra F E]

theorem Spaces.X'_posDef (S : Spaces R F E) (hYm : ∀ τ : E →+* ℂ, (S.Y R.m).sig τ = sigYD R R.m) :
    S.X'.IsPosDef := by
  intro τ
  have hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a) := S.cm.cmUnram.2.1 τ
  refine HSpace.pos_of_isomEmb S.X' (S.Y R.m) S.eYm.toLinearMap S.eYm_isom S.X'_sig (S.Y_sig R.m) τ hτ
    ((factXmDef R F S).1 τ) ?_
  rw [hYm τ, S.X'_rank]
  simp only [sigYD, Nat.sub_self, Nat.zero_div]
  unfold Ranks.rankX' Ranks.r
  have := R.k_ge
  omega

theorem Spaces.X_posDef (S : Spaces R F E)
    (hY : ∀ j, j ≤ R.m → ∀ τ : E →+* ℂ, (S.Y j).sig τ = sigYD R j) (j : ℕ) (hj : j ≤ R.m) :
    (S.X j).IsPosDef := by
  intro τ
  have hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a) := S.cm.cmUnram.2.1 τ
  rcases Nat.lt_or_ge j R.m with hjm | hjm
  · refine HSpace.pos_of_isomEmb (S.X j) (S.Y j) (S.iXY j) (S.iXY_isom j hjm) (S.X_sig j) (S.Y_sig j) τ hτ
      (S.X_def j hj τ) ?_
    rw [hY j hj τ, S.X_rank j hj]
    simp only [sigYD, Ranks.N]
    have h1 := R.m_add_three_le_k
    have h2 : (R.m - j) / 2 < R.k := by omega
    exact lt_of_lt_of_le h2 (Nat.le_add_right _ _)
  · have hjm' : j = R.m := le_antisymm hj hjm
    subst hjm'
    have hX' := Spaces.X'_posDef S (hY R.m le_rfl) τ
    rw [S.X'_rank] at hX'
    rw [S.X_rank R.m le_rfl]
    exact ((factXmDef R F S).2.2 τ).2 hX'

theorem Spaces.X_form_pos (S : Spaces R F E)
    (hY : ∀ j, j ≤ R.m → ∀ τ : E →+* ℂ, (S.Y j).sig τ = sigYD R j) (j : ℕ) (hj : j ≤ R.m)
    (τ : E →+* ℂ) (x : (S.X j).V) (hx : x ≠ 0) : ∃ c : ℝ, 0 < c ∧ τ ((S.X j).hT x x) = (c : ℂ) :=
  HSpace.form_pos (S.X j) (S.X_sig j) τ (S.cm.cmUnram.2.1 τ) (S.X_posDef hY j hj τ) x hx

end spaces

namespace D7

variable (D : D7)

theorem X_posDef (j : ℕ) (hj : j ≤ D.R.m) : letI := D.host.cmStar; (D.sp.X j).IsPosDef :=
  letI := D.host.cmStar; D.sp.X_posDef D.Y_sigval j hj

theorem X'_posDef : letI := D.host.cmStar; D.sp.X'.IsPosDef :=
  letI := D.host.cmStar; D.sp.X'_posDef (D.Y_sigval D.R.m le_rfl)

theorem X_form_pos (j : ℕ) (hj : j ≤ D.R.m) (τ : D.host.E →+* ℂ) :
    letI := D.host.cmStar; ∀ x : (D.sp.X j).V, x ≠ 0 → ∃ c : ℝ, 0 < c ∧ τ ((D.sp.X j).hT x x) = (c : ℂ) :=
  letI := D.host.cmStar; fun x hx => D.sp.X_form_pos D.Y_sigval j hj τ x hx

end D7

end Formalism.BasicNotions

end
end

section -- merged from Formalism.LocalRingCardinality.DataDIVDefs
noncomputable section

namespace Formalism.BasicNotions.DV

open Formalism.BasicNotions NumberField IsDedekindDomain

def MramL (D : D7) (u : D.what₂.Word) : Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V :=
  ((D.fm u).lat 0).L.comap ((D.nuIn u).restrictScalars (𝓞 D.what₂.LL))

def ur (D : D7) (w : D.what₂.places.Pl) (y : ℝ) : ℝ := (D.what₂.places.ramIdx w : ℝ) * y

def Iu (D : D7) (L : SizeData₂ D) (u : D.what₂.Word) :
    FractionalIdeal (nonZeroDivisors (𝓞 D.what₂.LL)) D.what₂.LL :=
  ∏ w ∈ L.supp, ((D.plEq w).asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 D.what₂.LL)) D.what₂.LL) ^
    (-(⌊ur D w (L.sg u w)⌋))

def NprimeDef (D : D7) (L : SizeData₂ D) : Prop :=
  ∀ u, (D.div.Nu u).L = Submodule.span (𝓞 D.what₂.LL)
    {x | ∃ a ∈ Iu D L u, ∃ y ∈ L.NuLat u, x = (a : D.what₂.LL) • y}

def RRDef (D : D7) : Prop :=
  ∀ x : D.div.RR.V, x ∈ D.div.RR.L ↔ ∀ w : D.what₂.places.Pl, ∃ d : 𝓞 D.what₂.LL,
    d ∉ (D.plEq w).asIdeal ∧
    d • x ∈ Submodule.span (𝓞 D.what₂.LL) {y | D.jEE y ∈ D.what₂.RRset (D.what₂.muAt w)}

def LocLe {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module (𝓞 K) V]
    (w : HeightOneSpectrum (𝓞 K)) (k : ℕ) (A B : Submodule (𝓞 K) V) : Prop :=
  ∀ x ∈ A, ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ s • x ∈ (w.asIdeal ^ k) • B

def LocEq {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module (𝓞 K) V]
    (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (𝓞 K) V) : Prop :=
  LocLe w 0 A B ∧ LocLe w 0 B A

def lenLoc {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module (𝓞 K) V]
    (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (𝓞 K) V) : ℕ∞ :=
  letI : w.asIdeal.IsPrime := w.isPrime
  Module.length (Localization.AtPrime w.asIdeal)
    (LocalizedModule w.asIdeal.primeCompl (↥B ⧸ A.comap B.subtype))

def InertK (D : D7) (p : ℕ) : Prop :=
  D.host.cls p = PrimeClass.signal ∨ D.host.cls p = PrimeClass.inertClass

def NuDef (D : D7) (L : SizeData₂ D) : Prop :=
  (∀ u w, D.what₂.places.resChar w ≠ (D.mem u).A.T → LocLe (D.plEq w) 0 (L.NuLat u) (MramL D u)) ∧
  (∀ u w, D.what₂.places.resChar w ≠ (D.mem u).A.T →
    (D.what₂.places.resChar w ∈ L.drop ∨ ¬ InertK D (D.what₂.places.resChar w)) →
      LocEq (D.plEq w) (L.NuLat u) (MramL D u)) ∧
  (∀ u w, ∀ l : ℕ, lenLoc (D.plEq w) (L.NuLat u) (MramL D u) = l →
    (l : ℝ) = (L.lenMN u w : ℝ) * (D.what₂.places.ramIdx w : ℝ))

def meanE (D : D7) (g : (D.what₂.LL →+* ℂ) → ℝ) : ℝ :=
  (∑ σ, g σ) / (Module.finrank ℚ D.what₂.LL : ℝ)

def wSz (D : D7) (j : ℕ) (ρ : D.what₂.Tau) : ℝ :=
  if h : 1 ≤ j ∧ j ≤ D.R.m then (((D.hc ρ).e ⟨j - 1, by omega⟩ : ℚ) : ℝ) else 0

def srcPar (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) (i : ℕ) : ℚ :=
  if h : i < D.R.k then (D.hcW u τ).u ⟨i, h⟩
  else
    if hb : (i - D.R.k) / (D.R.t + 1) < D.R.m then
      -(D.hcW u τ).e ⟨(i - D.R.k) / (D.R.t + 1), hb⟩ +
        ((D.R.t : ℚ) + 2 - 2 * (((i - D.R.k) % (D.R.t + 1) + 1 : ℕ) : ℚ)) / 2
    else 0

def nuRow (D : D7) (u : D.what₂.Word) (j : ℕ) (τ : D.what₂.Tau) (i : ℕ) : ℝ :=
  ((srcPar D u τ i : ℚ) : ℝ) + wSz D j τ -
    (((D.R.N (j - 1) : ℝ) + D.R.N j - 1 - 2 * (i : ℝ)) / 2)

def kerPlace (D : D7) (L : SizeData₂ D) (u : D.what₂.Word) (j : ℕ) (τ : D.what₂.Tau) : ℝ :=
  (∑ i ∈ Finset.range (D.R.N (j - 1)), phF (nuRow D u j τ i)) -
    (∑ i ∈ Finset.range (D.R.N (j - 1)), nuRow D u j τ i) * L.logOm

def SZbP (D : D7) (L : SizeData₂ D) (C : ℝ) (u : D.what₂.Word) : ℝ :=
  -(∑ t : D.host.TT, (L.aT t : ℝ) * Real.log ((D.mem u).A.T : ℝ)) +
    C * ((D.host.TT.card : ℝ) * L.sc.b' * (D.R.N D.R.m : ℝ) +
      (D.R.f : ℝ) * ((D.R.m : ℝ) * L.etaSz + L.Sc) * (D.R.N D.R.m : ℝ) +
      (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2) * L.La

end Formalism.BasicNotions.DV

namespace Formalism.BasicNotions

open Formalism.MainNotions.G

end Formalism.BasicNotions

end
end

section -- merged from Formalism.LocalRingCardinality.DataLatDefs
noncomputable section

namespace Formalism.BasicNotions

open NumberField IsDedekindDomain Formalism.MainNotions.G Classical

structure LatCmp (D : D7) where

  embW : ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    D.what₂.LL →+* (D.gat u w hg).Kf

  embW_int : ∀ u w hg (x : D.what₂.LL), (0 : WithTop ℤ) ≤ D.what₂.places.val w x ↔
    embW u w hg x ∈ Set.range (algebraMap (D.gat u w hg).O (D.gat u w hg).Kf)

  cmp : ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    ((D.fm u).lat 0).V →+ (D.gat u w hg).Fn
  cmp_smul : ∀ u w hg (a : D.what₂.LL) (x : ((D.fm u).lat 0).V),
    cmp u w hg (a • x) = embW u w hg a • cmp u w hg x

  cmp_li : ∀ u w hg, LinearIndependent (D.gat u w hg).Kf (fun a => cmp u w hg (((D.fm u).lat 0).b a))

  cmp_M : ∀ u w hg, Submodule.span (D.gat u w hg).O (cmp u w hg '' (((D.fm u).lat 0).L : Set ((D.fm u).lat 0).V)) =
    (D.gat u w hg).M

def InLoc {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module (𝓞 K) V]
    (w : HeightOneSpectrum (𝓞 K)) (A : Submodule (𝓞 K) V) (x : V) : Prop :=
  ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ s • x ∈ A

namespace LatCmp

variable {D : D7} (c : LatCmp D)

def VramDef (Y : LatInst D) : Prop :=
  ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    (Y.Vram u w hg : Set (D.gat u w hg).Fn) =
      Submodule.span (D.gat u w hg).Kf (c.cmp u w hg '' ((D.fm u).ramSub : Set ((D.fm u).lat 0).V))

def NuServedDef {L : SizeData₂ D} (X : Inst D L) (Y : LatInst D) (K : Consts) : Prop :=
  ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    VV X K (aL L) (bL L) (D.what₂.places.resChar w) ≠ ∅ →
    ∀ x : (D.div.Nu u).V, InLoc (D.plEq w) (L.NuLat u) x ↔ c.cmp u w hg (D.nuIn u x) ∈ NP X Y K u w hg

end LatCmp

namespace LT

variable (D : D7) (u : D.what₂.Word)

abbrev Fn (i : ℕ) : Type := (D.mem u).C.cls i → (D.mem u).C.Y i → ℂ

abbrev Vl (i : ℕ) : Type := ((D.fm u).lat i).V

abbrev Ow (w : D.what₂.places.Pl) : Subring D.what₂.LL := intW D.what₂.places w

instance lvModFin (i : ℕ) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) :
    Module.Finite ((D.mem u).A.Fv v) ((D.fm u).lv i v c) :=
  Module.finite_of_finrank_pos (by rw [(D.fm u).lv_rank]; exact D.R.N_pos i)

instance lvFintype (i : ℕ) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) : Fintype ((D.fm u).lv i v c) :=
  haveI : Finite ((D.fm u).lv i v c) := Module.finite_of_finite ((D.mem u).A.Fv v)
  Fintype.ofFinite _

def Uop (i : ℕ) (v : (D.mem u).A.vT) : Fn D u i →ₗ[ℂ] Fn D u i :=
  LinearMap.pi fun c => ∑ x ∈ Finset.univ.filter (fun x : (D.fm u).lv i v c => (D.fm u).fv i v c x = 1),
    ((D.fm u).upT i v c x).toLinearMap ∘ₗ LinearMap.proj ((D.fm u).up i v c x)

def VVT (w : D.what₂.places.Pl) : Finset (D.mem u).A.vT :=
  if (D.fm u).seenP w then Finset.univ.filter (fun v => (D.fm u).tauOf w v ∈ topsOf D.host D.eTau) else ∅

def Uprod (i : ℕ) (w : D.what₂.places.Pl) : Fn D u i →ₗ[ℂ] Fn D u i :=
  (VVT D u w).toList.foldr (fun v g => (Uop D u i v).comp g) LinearMap.id

def imgL {i j : ℕ} (w : D.what₂.places.Pl) (f : Fn D u i →ₗ[ℂ] Fn D u j)
    (A : Submodule (Ow D w) (Vl D u i)) : Submodule (Ow D w) (Vl D u j) where
  carrier := {y | ∃ x ∈ A, (D.fm u).emb j y = f ((D.fm u).emb i x)}
  add_mem' := by
    rintro a b ⟨x, hx, h1⟩ ⟨y, hy, h2⟩
    exact ⟨x + y, A.add_mem hx hy, by rw [map_add (f := _), map_add (f := _), map_add (f := _), h1, h2]⟩
  zero_mem' := ⟨0, A.zero_mem, by simp⟩
  smul_mem' := by
    rintro r a ⟨x, hx, h1⟩
    refine ⟨r • x, A.smul_mem r hx, ?_⟩
    rw [Subring.smul_def, Subring.smul_def, LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, h1,
      LinearMap.map_smul]

def Sram (w : D.what₂.places.Pl) : Submodule (Ow D w) (Vl D u 0) :=
  (D.fm u).S 0 w ⊓ (D.fm u).ramSub.restrictScalars (Ow D w)

def expT (w : D.what₂.places.Pl) : ℤ :=
  (D.R.m : ℤ) * ∑ v ∈ VVT D u w, (D.fm u).bTop ((D.fm u).tauOf w v)

def Nlam (w : D.what₂.places.Pl) : Submodule (Ow D w) (Vl D u 0) :=
  imgL D u w ((((D.mem u).A.T : ℂ) ^ expT D u w) • (Uprod D u 0 w) ^ D.R.m) (Sram D u w)

end LT

def NuAtTDef (D : D7) (L : SizeData₂ D) : Prop :=
  ∀ u (w : D.what₂.places.Pl), D.what₂.places.resChar w = (D.mem u).A.T →
    ∀ x : (D.div.Nu u).V, InLoc (D.plEq w) (L.NuLat u) x ↔ D.nuIn u x ∈ LT.Nlam D u w

structure LatDefs (D : D7) (L : SizeData₂ D) (X : Inst D L) (Y : LatInst D) (K : Consts) (c : LatCmp D) : Prop where
  vram : c.VramDef Y
  served : c.NuServedDef X Y K
  atT : NuAtTDef D L

end Formalism.BasicNotions

end
end

section -- merged from Formalism.LocalRingCardinality.DataRRMetric
noncomputable section

namespace Formalism.BasicNotions

open NumberField

namespace DV

variable {D : D7}

def UL (A : AmbForm D (RowSide.sharp D)) : Set (A.MtH D.what₂.mu0).V :=
  {u | A.jAmb D.what₂.mu0 u ∈ (RowSide.sharp D).Usp D.what₂.mu0}

def quotNorm (A : AmbForm D (RowSide.sharp D)) (v : InfinitePlace D.what₂.LL) (x : (A.MtH D.what₂.mu0).V) : ℝ :=
  ⨅ u : UL A, Formalism.HermitianLatticesTheory.normAt (A.MtH D.what₂.mu0).b (A.MtH D.what₂.mu0).X v (x + u)

end DV

structure EigIdx (D : D7) (X : DivX D) where
  Pi : Type
  [fin : Fintype Pi]
  [dec : DecidableEq Pi]
  cOf : D.what₂.FT → Pi
  lam_const : ∀ j ∈ SizeData₂.lifts D, ∀ π π' e, D.what₂.isot j π ≠ ⊥ → D.what₂.isot j π' ≠ ⊥ → cOf π = cOf π' →
    X.logLam j π e = X.logLam j π' e

attribute [instance] EigIdx.fin EigIdx.dec

def DV.EEcpart (D : D7) {X : DivX D} (E : EigIdx D X) (c : E.Pi) : Submodule ℂ D.what₂.EE :=
  Submodule.span ℂ (D.what₂.onb '' {σ | E.cOf (D.what₂.ft σ) = c})


open Classical in
def DV.logLamC {D : D7} {X : DivX D} (E : EigIdx D X) (j : ℕ) (c : E.Pi) (e : D.what₂.LL →+* ℂ) : ℝ :=
  if h : ∃ π, E.cOf π = c ∧ D.what₂.isot j π ≠ ⊥ then X.logLam j h.choose e else 0

def RRMetricDef (D : D7) (X : DivX D) (A : AmbForm D (RowSide.sharp D)) (E : EigIdx D X) : Prop :=
  ∀ v : InfinitePlace D.what₂.LL, v ≠ InfinitePlace.mk D.what₂.embLL →
    ∀ (x : E.Pi → D.div.RR.V) (q : E.Pi → (A.MtH D.what₂.mu0).V),
      (∀ c, A.jAmb D.what₂.mu0 (q c) ∈ (RowSide.sharp D).V0 D.what₂.mu0) →
      (∀ c, D.jEE (x c) = (RowSide.sharp D).iota D.what₂.mu0 (A.jAmb D.what₂.mu0 (q c))) →
      (∀ c, D.jEE (x c) ∈ DV.EEcpart D E c) →
        Formalism.HermitianLatticesTheory.normAt D.div.RR.b D.div.RR.X v (∑ c, x c) ^ 2 =
          ∑ c, X.kapR v.embedding * Real.exp (∑ j ∈ SizeData₂.lifts D, DV.logLamC E j c v.embedding) *
            DV.quotNorm A v (q c) ^ 2

end Formalism.BasicNotions

end
end
