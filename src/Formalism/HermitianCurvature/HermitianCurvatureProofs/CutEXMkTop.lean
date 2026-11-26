module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutMKTop

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXMkTopKr
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBQ

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

theorem emb_mu_uni {k p ρ : ℕ} (ν : B.Mat k ρ) (V : Matrix (Fin p) (Fin p) ℂ) (a : Matrix (Fin p) (Fin (2 * ρ + k + 1)) ℂ)
    (b : Matrix (Fin p) (Fin p) ℂ) (c : Matrix (Fin (2 * ρ + k + 1)) (Fin p) ℂ) :
    U.embG k p ρ ν * U.muP k p ρ V * U.blk3 1 a b 0 1 c 0 0 1 =
      U.blk3 V (V * a) (V * b) 0 ν (ν * c) 0 0 (G.wMat p * Vᴴ⁻¹ * G.wMat p) := by
  unfold U.embG U.muP
  rw [Ux3.block3_mul, Ux3.block3_mul]
  congr 1 <;> simp

theorem upper_inj {p : ℕ} {u u' : G.UT p → ℂ} (h : G.upper u = G.upper u') : u = u' := by
  funext p
  have h1 := congrFun (congrFun h p.1.1) p.1.2
  simp only [G.upper, G.strictUpper, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply_ne (ne_of_lt p.2),
    zero_add, dif_pos p.2] at h1
  exact h1

theorem kr_eq_integral_krI_psiR {k p ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k (p + ρ) Wp Wq)
    (hW' : Bj.μW' Set.univ = 1) (hW0' : B0.μW' = Bj.μW'.map (Formalism.FourierDecayAlt.P.PBM.levMt p ρ rfl))
    (hNj : Bj.μN = D.muN k ρ) (hN0 : B0.μN = D.muN k (p + ρ))
    (H : B.Mat k (p + ρ) → (Wq →L[ℂ] Wp)) (y₀ : B.Mat k (p + ρ)) :
    PBG.Kr B0 H y₀ = ∫ s, LeftFubiniLemmas.KrI B0 H y₀ (LeftFubiniLemmas.PsiR s) ∂(LeftFubiniLemmas.muR (p := p) Bj) := by
  classical
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarW'
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarN
  have := Formalism.FourierDecayAlt.P.Dx2.SplitF.sf_RC (k := k) p ρ

  set S : Set (LeftFubiniLemmas.XR k p ρ) := {s | LeftFubiniLemmas.GoodR Bj s} with hSdef
  have hSc : IsClosed S :=
    IsClosed.and ((Formalism.FourierDecayAlt.P.B6.isClosed_UWset k ρ Bj.z').preimage (continuous_fst.comp continuous_fst))
      ((Formalism.FourierDecayAlt.P.B6.isClosed_Nset k ρ).preimage (continuous_snd.comp continuous_fst))
  have hBS : BorelSpace (LeftFubiniLemmas.XR k p ρ) := by
    have : BorelSpace ((G.UT p → ℂ) × (Fin p → ℝ)) := Prod.borelSpace
    have : BorelSpace (U.RC k p ρ) := Prod.borelSpace
    have : BorelSpace (U.RC k p ρ × (G.UT p → ℂ)) := Prod.borelSpace
    have : BorelSpace (Mt k ρ × Mt k ρ) := Prod.borelSpace
    exact Prod.borelSpace
  have hSm : MeasurableSet S := hSc.measurableSet

  have hmp : MeasurePreserving (LeftFubiniLemmas.PsiR (k := k) (p := p) (ρ := ρ)) (LeftFubiniLemmas.muR Bj) (B0.μW'.prod B0.μN) := by
    have h := LeftFubiniLemmas.right_measure_preserving k p ρ Bj.z' Bj.μW' B0.μW' Bj.haarW' hW' hW0'
    unfold LeftFubiniLemmas.muR
    rw [hN0, hNj]
    exact h

  have hinj : Set.InjOn (LeftFubiniLemmas.PsiR (k := k) (p := p) (ρ := ρ)) S := by
    intro s hs s' hs' he
    have he1 := congrArg Prod.fst he
    have he2 := congrArg Prod.snd he
    have h11 : s.1.1 = s'.1.1 := by
      have := congrArg (Formalism.FourierDecayAlt.P.PBM.midMt p ρ rfl) he1
      simpa only [LeftFubiniLemmas.PsiR, Formalism.FourierDecayAlt.P.PBM.midMt_levMt] using this
    have hN : LeftFubiniLemmas.NR s = LeftFubiniLemmas.NR s' := Matrix.of.symm.injective he2
    obtain ⟨a, b, c, hRn⟩ : ∃ a b c, U.Rn k p ρ (LeftFubiniLemmas.rcAct (Matrix.of s.1.1) s.2.1) = U.blk3 1 a b 0 1 c 0 0 1 :=
      ⟨_, _, _, Formalism.FourierDecayAlt.P.Ux3.rn_eq _⟩
    obtain ⟨a', b', c', hRn'⟩ : ∃ a b c, U.Rn k p ρ (LeftFubiniLemmas.rcAct (Matrix.of s'.1.1) s'.2.1) = U.blk3 1 a b 0 1 c 0 0 1 :=
      ⟨_, _, _, Formalism.FourierDecayAlt.P.Ux3.rn_eq _⟩
    unfold LeftFubiniLemmas.NR at hN
    rw [hRn, hRn', emb_mu_uni, emb_mu_uni, Formalism.FourierDecayAlt.P.Ux3.block3_eq_iff] at hN
    obtain ⟨hU, hUa, hUb, -, hν, hνc, -, -, -⟩ := hN
    have hUu : IsUnit (G.upper s.2.2).det := by rw [Formalism.FourierDecayAlt.P.Ux3.det_upper]; exact isUnit_one
    have hνu : IsUnit (Matrix.of s.1.2 : B.Mat k ρ).det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hs.2.1
    have hu : s.2.2 = s'.2.2 := upper_inj hU
    rw [← hU] at hUa hUb
    rw [← hν] at hνc
    have ha : a = a' := by
      have := congrArg (fun M => (G.upper s.2.2)⁻¹ * M) hUa
      simpa only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hUu, Matrix.one_mul] using this
    have hb : b = b' := by
      have := congrArg (fun M => (G.upper s.2.2)⁻¹ * M) hUb
      simpa only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hUu, Matrix.one_mul] using this
    have hc : c = c' := by
      have := congrArg (fun M => (Matrix.of s.1.2 : B.Mat k ρ)⁻¹ * M) hνc
      simpa only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hνu, Matrix.one_mul] using this
    have hR : LeftFubiniLemmas.rcAct (Matrix.of s.1.1) s.2.1 = LeftFubiniLemmas.rcAct (Matrix.of s'.1.1) s'.2.1 :=
      (Formalism.FourierDecayAlt.P.radical_parametrisation k p ρ).1 (by rw [hRn, hRn', ha, hb, hc])
    rw [← h11] at hR
    have hhu : IsUnit (Matrix.of s.1.1 : B.Mat k ρ).det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hs.1.1
    have h21 : s.2.1 = s'.2.1 := by
      have e1 := congrArg Prod.fst hR
      have e2 := congrArg Prod.snd hR
      simp only [LeftFubiniLemmas.rcAct] at e1 e2
      have e1' : (Matrix.of s.1.1 : B.Mat k ρ) * Matrix.of s.2.1.1 = Matrix.of s.1.1 * Matrix.of s'.2.1.1 := by
        ext v w; exact congrFun (congrFun e1 v) w
      have e3 := congrArg (fun M => (Matrix.of s.1.1 : B.Mat k ρ)⁻¹ * M) e1'
      simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hhu, Matrix.one_mul] at e3
      exact Prod.ext (by ext v w; exact congrFun (congrFun e3 v) w) e2
    have h12 : s.1.2 = s'.1.2 := by
      ext v w; exact congrFun (congrFun hν v) w
    exact Prod.ext (Prod.ext h11 h12) (Prod.ext h21 hu)
  have hres : (LeftFubiniLemmas.muR (p := p) Bj).restrict S = LeftFubiniLemmas.muR Bj :=
    Measure.restrict_eq_self_of_ae_mem (LeftFubiniLemmas.ae_goodR Bj)
  have hcont : Continuous (LeftFubiniLemmas.PsiR (k := k) (p := p) (ρ := ρ)) := by
    unfold LeftFubiniLemmas.PsiR
    exact ((Formalism.FourierDecayAlt.P.PBM.levMt_cont p ρ rfl).comp (continuous_fst.comp continuous_fst)).prodMk LeftFubiniLemmas.NR_cont
  have hPol : PolishSpace (LeftFubiniLemmas.XR k p ρ) := {}
  have hSB : StandardBorelSpace (LeftFubiniLemmas.XR k p ρ) := inferInstance
  have : StandardBorelSpace S := hSm.standardBorel
  have hemb : MeasurableEmbedding (fun s : S => LeftFubiniLemmas.PsiR (s : LeftFubiniLemmas.XR k p ρ)) :=
    (hcont.measurable.comp measurable_subtype_coe).measurableEmbedding
      (fun a b hab => Subtype.ext (hinj a.2 b.2 hab))
  rw [LeftFubiniLemmas.kr_eq_int]
  calc ∫ q, LeftFubiniLemmas.KrI B0 H y₀ q ∂(B0.μW'.prod B0.μN)
      = ∫ q, LeftFubiniLemmas.KrI B0 H y₀ q ∂((LeftFubiniLemmas.muR (p := p) Bj).map LeftFubiniLemmas.PsiR) := by rw [hmp.map_eq]
    _ = ∫ q, LeftFubiniLemmas.KrI B0 H y₀ q ∂((Measure.comap Subtype.val (LeftFubiniLemmas.muR (p := p) Bj)).map
          (fun s : S => LeftFubiniLemmas.PsiR (s : LeftFubiniLemmas.XR k p ρ))) := by
        rw [show (fun s : S => LeftFubiniLemmas.PsiR (s : LeftFubiniLemmas.XR k p ρ)) = LeftFubiniLemmas.PsiR ∘ Subtype.val from rfl,
          ← Measure.map_map hcont.measurable measurable_subtype_coe, map_comap_subtype_coe hSm, hres]
    _ = ∫ s : S, LeftFubiniLemmas.KrI B0 H y₀ (LeftFubiniLemmas.PsiR (s : LeftFubiniLemmas.XR k p ρ)) ∂(Measure.comap Subtype.val (LeftFubiniLemmas.muR (p := p) Bj)) :=
        hemb.integral_map _
    _ = ∫ s, LeftFubiniLemmas.KrI B0 H y₀ (LeftFubiniLemmas.PsiR s) ∂((Measure.comap Subtype.val (LeftFubiniLemmas.muR (p := p) Bj)).map
          (Subtype.val : S → LeftFubiniLemmas.XR k p ρ)) :=
        ((MeasurableEmbedding.subtype_coe hSm).integral_map (fun s => LeftFubiniLemmas.KrI B0 H y₀ (LeftFubiniLemmas.PsiR s))).symm
    _ = _ := by rw [map_comap_subtype_coe hSm, hres]

end Formalism.FourierDecayAlt.P.PBQ
end
end

noncomputable section

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.LeftFubiniLemmas
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutEX.MkTopPf

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section alg

variable {k p ρ : ℕ}

theorem pt_eq (Z : Matrix (Fin p) (Fin p) ℂ) (y h h'' : B.Mat k ρ) (hH : h''ᴴ * Hpk k ρ * h'' = Hpk k ρ)
    (a x' : U.RC k p ρ) (u : G.UT p → ℂ) :
    U.Rn k p ρ (-a) * U.embG k p ρ h⁻¹ * U.mMap k p ρ Z y *
        (U.embG k p ρ 1 * U.muP k p ρ (G.upper u) * U.Rn k p ρ (rcAct h'' x')) * U.embG k p ρ h'' =
      PBI.psiC ((a, x'), (Matrix.of.symm (Z * G.upper u), Matrix.of.symm (h⁻¹ * y * h''))) := by
  have e1 : U.Rn k p ρ (rcAct h'' x') * U.embG k p ρ h'' = U.embG k p ρ h'' * U.Rn k p ρ x' :=
    (embedded_group_right_action k p ρ h'' x' hH).symm
  have key : U.muP k p ρ (G.upper u) * (U.Rn k p ρ (rcAct h'' x') * U.embG k p ρ h'') =
      U.embG k p ρ h'' * (U.muP k p ρ (G.upper u) * U.Rn k p ρ x') := by
    rw [e1, ← Matrix.mul_assoc, ← embedded_group_measure_preserving k p ρ h'' (G.upper u), Matrix.mul_assoc]
  have e3 := embedding_map_embedded_group k p ρ Z y h⁻¹ h''
  have e4 : U.mMap k p ρ (Z * G.upper u) (h⁻¹ * y * h'') =
      U.mMap k p ρ Z (h⁻¹ * y * h'') * U.muP k p ρ (G.upper u) := by
    have := embedding_map_lower_unipotent k p ρ 1 Z (G.upper u) (h⁻¹ * y * h'') (by simp)
    rw [Matrix.one_mul, Matrix.conjTranspose_one, inv_one, Formalism.FourierDecayAlt.P.PBM.muP_one, Matrix.one_mul] at this
    exact this
  unfold PBI.psiC
  simp only [Equiv.apply_symm_apply]
  rw [Formalism.FourierDecayAlt.P.PBM.rn_inv, e4, e3, Formalism.FourierDecayAlt.P.PBM.embG_one, Matrix.one_mul]
  simp only [Matrix.mul_assoc]
  rw [key]

end alg

end Formalism.FourierDecayAlt.P.CutEX.MkTopPf

namespace Formalism.FourierDecayAlt.P.CutEX.MkTopPf

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem star_mul_self_psi {k n : ℕ} (z : Fin (2 * n + k + 1) → ℂ) (c : ℂ) (g : B.Mat k n) :
    star (psi k n z c g) * psi k n z c g = 1 := by
  have h1 := Formalism.FourierDecayAlt.P.LeftFubiniLemmas.norm_psi z c g
  have h2 : star (psi k n z c g) * psi k n z c g = ((Complex.normSq (psi k n z c g) : ℝ) : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self]; rfl
  rw [h2, Complex.normSq_eq_norm_sq, h1]
  simp

end Formalism.FourierDecayAlt.P.CutEX.MkTopPf

namespace Formalism.FourierDecayAlt.P.CutEX.MkTopPf

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section right

variable {k p ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]


set_option maxHeartbeats 1000000 in
theorem krI_pt (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k (p + ρ) Wp Wq)
    (hz' : B0.z' = liftVec k p ρ Bj.z') (hπ' : ∀ y : B.Mat k ρ, Bj.π' y = B0.π' (U.embG k p ρ y))
    (b b' : U.RC k p ρ → ℝ) (β : (Fin p → Fin p → ℂ) → ℝ) (Φ : (Fin p → Fin p → ℂ) → Mt k ρ → (Wq →L[ℂ] Wp))
    (Z : Fin p → Fin p → ℂ) (hZ : (Matrix.of Z).det ≠ 0) (y : Mt k ρ) (hyG : (Matrix.of y : B.Mat k ρ) ∈ B.GV k ρ)
    (hΦL : ∀ h1 ∈ UWset k ρ Bj.z, ∀ h2 ∈ UWset k ρ Bj.z',
      Φ Z (Matrix.of.symm (h1 * Matrix.of y * h2)) = (Bj.π h1).comp ((Φ Z y).comp (Bj.π' h2)))
    (hΦU : ∀ (u : G.UT p → ℂ) (y' : Mt k ρ), (Matrix.of y' : B.Mat k ρ) ∈ B.GV k ρ →
      Φ (Matrix.of.symm (Matrix.of Z * G.upper u)) y' =
        psi k (p + ρ) (liftVec k p ρ Bj.z') cStd (U.muP k p ρ (G.upper u)) • Φ Z y')
    (h : B.Mat k ρ) (hh : h ∈ UWset k ρ Bj.z) (a : U.RC k p ρ) (s : XR k p ρ) (hs : GoodR Bj s)
    (hν : (Matrix.of s.1.2 : B.Mat k ρ) = 1) :
    KrI B0 (Formalism.FourierDecayAlt.P.CutMK.HB b b' β Φ) (U.Rn k p ρ (-a) * U.embG k p ρ h⁻¹ * U.mMap k p ρ (Matrix.of Z) (Matrix.of y)) (PsiR s) =
      (((b a * b' s.2.1 * β (Matrix.of.symm (Matrix.of Z * G.upper s.2.2)) : ℝ) : ℂ) *
        star (psi k (p + ρ) (liftVec k p ρ Bj.z') cStd (U.Rn k p ρ s.2.1))) • (Bj.π h⁻¹).comp (Φ Z y) := by
  obtain ⟨hh', hn'⟩ := hs
  set h'' : B.Mat k ρ := Matrix.of s.1.1 with hh''
  have hW := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k ρ Bj.z
  have hW' := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k ρ Bj.z'
  have hN := Formalism.FourierDecayAlt.P.unipotent_radical_closed k ρ
  have hH : h''ᴴ * Hpk k ρ * h'' = Hpk k ρ := hh'.1
  have hNR : (Matrix.of (PsiR s).2 : B.Mat k (p + ρ)) =
      U.embG k p ρ 1 * U.muP k p ρ (G.upper s.2.2) * U.Rn k p ρ (rcAct h'' s.2.1) := by
    simp only [PsiR, NR, Equiv.apply_symm_apply, hν]
    rfl
  have hL : (Matrix.of (PsiR s).1 : B.Mat k (p + ρ)) = U.embG k p ρ h'' := of_levMt _
  have hdet : (Matrix.of (Matrix.of.symm (Matrix.of Z * G.upper s.2.2))).det ≠ 0 := by
    simp only [Equiv.apply_symm_apply]
    rw [Matrix.det_mul, Formalism.FourierDecayAlt.P.Ux3.det_upper, mul_one]
    exact hZ
  have hy'G : (Matrix.of (Matrix.of.symm (h⁻¹ * Matrix.of y * h'')) : B.Mat k ρ) ∈ B.GV k ρ := by
    simp only [Equiv.apply_symm_apply]
    exact BetaSesquilinearity.gv_mul (BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.B6.UWset_sub k ρ Bj.z (hW.inv_mem h hh)) hyG)
      (Formalism.FourierDecayAlt.P.B6.UWset_sub k ρ Bj.z' hh')
  unfold KrI
  rw [hNR, hL, pt_eq (Matrix.of Z) (Matrix.of y) h h'' hH a s.2.1 s.2.2]
  unfold Formalism.FourierDecayAlt.P.CutMK.HB
  rw [PBI.chartCoefficient_apply b b' _ ((a, s.2.1), (Matrix.of.symm (Matrix.of Z * G.upper s.2.2),
    Matrix.of.symm (h⁻¹ * Matrix.of y * h''))) hdet hy'G]
  simp only
  rw [hΦU s.2.2 _ hy'G]
  have e5 : Φ Z (Matrix.of.symm (h⁻¹ * Matrix.of y * h'')) = (Bj.π h⁻¹).comp ((Φ Z y).comp (Bj.π' h'')) :=
    hΦL h⁻¹ (hW.inv_mem h hh) h'' hh'
  rw [e5]
  have uh'' : IsUnit h''.det := hW'.unit _ hh'
  have e6 : B0.π' (U.embG k p ρ h'')⁻¹ = Bj.π' h''⁻¹ := by
    rw [← Formalism.FourierDecayAlt.P.LeftFubiniLemmas.embG_inv uh'', hπ']
  have e7 : (Bj.π' h'').comp (Bj.π' h''⁻¹) = ContinuousLinearMap.id ℂ Wq := by
    rw [← Bj.π'_rep.2 h'' hh' h''⁻¹ (hW'.inv_mem h'' hh'), Matrix.mul_nonsing_inv _ uh'', Bj.π'_rep.1]
    rfl
  have hps : psi k (p + ρ) B0.z' cStd
      (U.embG k p ρ 1 * U.muP k p ρ (G.upper s.2.2) * U.Rn k p ρ (rcAct h'' s.2.1)) =
      psi k (p + ρ) (liftVec k p ρ Bj.z') cStd (U.muP k p ρ (G.upper s.2.2)) *
        psi k (p + ρ) (liftVec k p ρ Bj.z') cStd (U.Rn k p ρ s.2.1) := by
    rw [hz', psi_right_equivariant k p ρ Bj.z' 1 s.2.2 _ Bj.z'_mem hN.one_mem,
      psi_right_action_comm k p ρ Bj.z' h'' s.2.1 Bj.z'_mem hh', Formalism.FourierDecayAlt.P.Qx5.psi_one Bj.z'_mem, one_mul]
  rw [e6, hps]
  simp only [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_assoc, e7, ContinuousLinearMap.comp_id,
    smul_smul]
  congr 1
  have hB := star_mul_self_psi (liftVec k p ρ Bj.z') cStd (U.muP k p ρ (G.upper s.2.2))
  rw [star_mul']
  push_cast
  linear_combination ((b a : ℂ) * (b' s.2.1 : ℂ) * (β (Matrix.of.symm (Matrix.of Z * G.upper s.2.2)) : ℂ) *
    star (psi k (p + ρ) (liftVec k p ρ Bj.z') cStd (U.Rn k p ρ s.2.1))) * hB

end right

end Formalism.FourierDecayAlt.P.CutEX.MkTopPf

namespace Formalism.FourierDecayAlt.P.CutEX.MkTopPf

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section avg

theorem ae_nu_one {k : ℕ} : ∀ᵐ x ∂(D.muN k 0), (Matrix.of x : B.Mat k 0) = 1 := by
  show ∀ᵐ x ∂(Measure.dirac (Matrix.of.symm (1 : B.Mat k 0))), (Matrix.of x : B.Mat k 0) = 1
  rw [ae_dirac_eq]
  exact Filter.eventually_pure.2 (Equiv.apply_symm_apply _ _)

theorem level_zero_measure_univ_eq_one {k : ℕ} : D.muN k 0 Set.univ = 1 := by
  show Measure.dirac (Matrix.of.symm (1 : B.Mat k 0)) Set.univ = 1
  exact measure_univ

theorem right_average_formula : Formalism.FourierDecayAlt.P.CutMK.RightAvg := by
  intro k p ρ Wp Wq _ _ _ _ _ _ hρ Bj B0 hz' hπ' hW' hW0' hNj hN0 b b' β Φ hb' hb'c Z hZ hβi hβ1 y hyG hΦL hΦU
    h hh a
  subst hρ
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarW'
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarN
  have := Formalism.FourierDecayAlt.P.Dx2.SplitF.sf_RC (k := k) p 0
  rw [Formalism.FourierDecayAlt.P.PBQ.kr_eq_integral_krI_psiR Bj B0 hW' hW0' hNj hN0]
  have hae : ∀ᵐ s ∂(muR (p := p) Bj), GoodR Bj s ∧ (Matrix.of s.1.2 : B.Mat k 0) = 1 := by
    have h2 : ∀ᵐ s ∂(muR (p := p) Bj), (Matrix.of s.1.2 : B.Mat k 0) = 1 := by
      unfold muR
      rw [hNj]
      exact Measure.quasiMeasurePreserving_fst.ae (Measure.quasiMeasurePreserving_snd.ae ae_nu_one)
    filter_upwards [ae_goodR (p := p) Bj, h2] with s h1 h3 using ⟨h1, h3⟩
  rw [integral_congr_ae (hae.mono fun s hs => krI_pt Bj B0 hz' hπ' b b' β Φ Z hZ y hyG hΦL hΦU h hh a s hs.1 hs.2),
    integral_smul_const]
  congr 1
  have hfun : (fun s : XR k p 0 => (((b a * b' s.2.1 * β (Matrix.of.symm (Matrix.of Z * G.upper s.2.2)) : ℝ) : ℂ) *
      star (psi k (p + 0) (liftVec k p 0 Bj.z') cStd (U.Rn k p 0 s.2.1)))) =
      fun s => (fun _ : Mt k 0 × Mt k 0 => (1 : ℂ)) s.1 *
        (fun t : U.RC k p 0 × (G.UT p → ℂ) => (b a : ℂ) *
          (((b' t.1 : ℂ) * star (psi k (p + 0) (liftVec k p 0 Bj.z') cStd (U.Rn k p 0 t.1))) *
            ((β (Matrix.of.symm (Matrix.of Z * G.upper t.2)) : ℝ) : ℂ))) s.2 := by
    funext s
    push_cast
    ring
  unfold muR
  rw [hfun]
  refine (integral_prod_mul (μ := Bj.μW'.prod Bj.μN) (ν := (U.muRC k p 0).prod (volume : Measure (G.UT p → ℂ)))
    (fun _ : Mt k 0 × Mt k 0 => (1 : ℂ)) (fun t : U.RC k p 0 × (G.UT p → ℂ) => (b a : ℂ) *
          (((b' t.1 : ℂ) * star (psi k (p + 0) (liftVec k p 0 Bj.z') cStd (U.Rn k p 0 t.1))) *
            ((β (Matrix.of.symm (Matrix.of Z * G.upper t.2)) : ℝ) : ℂ)))).trans ?_
  rw [integral_const_mul]
  rw [show (∫ t : U.RC k p 0 × (G.UT p → ℂ), ((b' t.1 : ℂ) * star (psi k (p + 0) (liftVec k p 0 Bj.z') cStd (U.Rn k p 0 t.1))) *
      ((β (Matrix.of.symm (Matrix.of Z * G.upper t.2)) : ℝ) : ℂ) ∂((U.muRC k p 0).prod volume)) =
      (∫ x, (b' x : ℂ) * star (psi k (p + 0) (liftVec k p 0 Bj.z') cStd (U.Rn k p 0 x)) ∂(U.muRC k p 0)) *
        ∫ v : G.UT p → ℂ, ((β (Matrix.of.symm (Matrix.of Z * G.upper v)) : ℝ) : ℂ) from
    integral_prod_mul (μ := U.muRC k p 0) (ν := (volume : Measure (G.UT p → ℂ))) (fun x : U.RC k p 0 => (b' x : ℂ) * star (psi k (p + 0) (liftVec k p 0 Bj.z') cStd (U.Rn k p 0 x)))
      (fun v : G.UT p → ℂ => ((β (Matrix.of.symm (Matrix.of Z * G.upper v)) : ℝ) : ℂ))]
  rw [integral_const, integral_complex_ofReal, hβ1]
  have hm : (Bj.μW'.prod Bj.μN).real Set.univ = 1 := by
    rw [Measure.real, ← Set.univ_prod_univ, Measure.prod_prod, hW', hNj, level_zero_measure_univ_eq_one]
    simp
  rw [hm]
  unfold Formalism.FourierDecayAlt.P.CutMK.kapR
  simp [U.muRC]

theorem left_average_formula : Formalism.FourierDecayAlt.P.CutMK.LeftAvg := by
  intro k p ρ Wp Wq _ _ _ _ _ _ hρ Bj B0 hW hNj H g b c A hb hbc hK
  subst hρ
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarN
  have := Formalism.FourierDecayAlt.P.Dx2.SplitF.sf_RC (k := k) p 0
  have hWs := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k 0 Bj.z
  have hae : ∀ᵐ x ∂(PBQ.muXP (p := p) Bj), PBQ.GoodP Bj x ∧ (Matrix.of x.1.2 : B.Mat k 0) = 1 := by
    have h2 : ∀ᵐ x ∂(PBQ.muXP (p := p) Bj), (Matrix.of x.1.2 : B.Mat k 0) = 1 := by
      unfold PBQ.muXP
      rw [hNj]
      exact Measure.quasiMeasurePreserving_fst.ae (Measure.quasiMeasurePreserving_snd.ae ae_nu_one)
    filter_upwards [PBQ.ae_goodP (p := p) Bj, h2] with x h1 h3 using ⟨h1, h3⟩
  have hpt : ∀ x : PBQ.XP k p 0, PBQ.GoodP Bj x ∧ (Matrix.of x.1.2 : B.Mat k 0) = 1 →
      PBQ.pbI Bj B0 rfl H g x =
        ((b x.2 : ℂ) * psi k (p + 0) (liftVec k p 0 Bj.z) cStd (U.Rn k p 0 x.2) * c) • A := by
    rintro x ⟨hx, hν⟩
    have hh := hx.1
    have uh : IsUnit (Matrix.of x.1.1 : B.Mat k 0).det := hWs.unit _ hh
    unfold PBQ.pbI PBQ.sP PBQ.cP
    rw [if_pos hx, hν, inv_one, Matrix.mul_one, Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl, hK _ hh x.2,
      Formalism.FourierDecayAlt.P.Qx5.psi_one Bj.z_mem, one_mul]
    have e : (Bj.π (Matrix.of x.1.1)).comp (Bj.π (Matrix.of x.1.1)⁻¹) = ContinuousLinearMap.id ℂ Wp := by
      rw [← Bj.π_rep.2 _ hh _ (hWs.inv_mem _ hh), Matrix.mul_nonsing_inv _ uh, Bj.π_rep.1]
      rfl
    rw [ContinuousLinearMap.comp_smul, ← ContinuousLinearMap.comp_assoc, e, ContinuousLinearMap.id_comp, smul_smul]
    congr 1
    ring
  unfold PBQ.pbF
  rw [integral_congr_ae (hae.mono hpt), integral_smul_const]
  congr 1
  have hfun : (fun x : PBQ.XP k p 0 => (b x.2 : ℂ) * psi k (p + 0) (liftVec k p 0 Bj.z) cStd (U.Rn k p 0 x.2) * c) =
      fun x => (fun _ : Mt k 0 × Mt k 0 => (1 : ℂ)) x.1 *
        (fun t : U.RC k p 0 => (b t : ℂ) * psi k (p + 0) (liftVec k p 0 Bj.z) cStd (U.Rn k p 0 t) * c) x.2 := by
    funext x
    ring
  unfold PBQ.muXP
  rw [hfun]
  refine (integral_prod_mul (μ := Bj.μW.prod Bj.μN) (ν := U.muRC k p 0) (fun _ : Mt k 0 × Mt k 0 => (1 : ℂ))
    (fun t : U.RC k p 0 => (b t : ℂ) * psi k (p + 0) (liftVec k p 0 Bj.z) cStd (U.Rn k p 0 t) * c)).trans ?_
  rw [integral_const, integral_mul_const]
  have hm : (Bj.μW.prod Bj.μN).real Set.univ = 1 := by
    rw [Measure.real, ← Set.univ_prod_univ, Measure.prod_prod, hW, hNj, level_zero_measure_univ_eq_one]
    simp
  rw [hm]
  unfold Formalism.FourierDecayAlt.P.CutMK.kapL
  simp [U.muRC]

end avg

end Formalism.FourierDecayAlt.P.CutEX.MkTopPf

namespace Formalism.FourierDecayAlt.P

theorem top_truncation_of_averages : CutEX.MkTop :=
  CutMK.mkTop_of_avgs CutEX.MkTopPf.right_average_formula CutEX.MkTopPf.left_average_formula

end Formalism.FourierDecayAlt.P
