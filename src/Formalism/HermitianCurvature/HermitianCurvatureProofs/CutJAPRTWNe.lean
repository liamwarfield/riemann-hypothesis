module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepThtFacts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRTWNeAlg

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.ThtAdapted
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.SectionEmbeddingMulVec
open Matrix Finset Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.TW

noncomputable section

open Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P

theorem eb_intertwine {k r m : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    {y z z' : Fin (2 * r + k + 1) → ℂ} {Bs : Fin m → Fin (2 * r + k + 1) → ℂ} (h : IsFrameOf k r [y, z'] Bs)
    {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} (hR : IsRepW k r z π) (hR' : IsRepW k r z' π')
    {g : Mx k r} (hg : g ∈ UH (Hpk k r)) (hgB : IsFrameOf k r [z] (fun a => g *ᵥ Bs a)) (A : Wq →L[ℂ] Wp)
    (hint : ∀ h' ∈ UWset k r z', h' *ᵥ y = y → ∀ v, A (π' h' v) = π (g * h' * g⁻¹) (A v)) (a b : Fin m) (v : Wq) :
    A (EB π' Bs a b v) = EB π (fun a => g *ᵥ Bs a) a b (A v) := by
  have hB' : IsFrameOf k r [z'] Bs := Qx8.frame_sub h (by simp)
  have l' := QrD.frame_lie hB' a b
  have l := QrD.frame_lie hgB a b
  show A (QrD.ecOp π' _ v) = QrD.ecOp π _ (A v)
  rw [← QrD.ecRep_eq hR'.1 hR'.2 l'.1 l'.2, ← QrD.ecRep_eq hR.1 hR.2 l.1 l.2]
  have hU := Qx8.frame_InU h (z := z') (by simp) a b
  have hky := Qx8.hpart_kill Bs a b (Qx8.frame_orth h (v := y) (by simp))
  have hc := Qx8.hpart_conj Bs a b hg
  show A (dRep π' _ v + Complex.I • dRep π' _ v) = dRep π _ (A v) + Complex.I • dRep π _ (A v)
  rw [map_add (f := _), map_smul, hc.1, hc.2]
  congr 1
  · refine Qx8.dRep_intertwine A (Qx8.rep_hasDeriv hR'.1 hR'.2 hU.1 v) fun t => ?_
    rw [Qx8.exp_conj_uh hg]
    exact hint _ (hU.1 t) (Qx8.exp_fix hky.1 t) v
  · congr 1
    refine Qx8.dRep_intertwine A (Qx8.rep_hasDeriv hR'.1 hR'.2 hU.2 v) fun t => ?_
    rw [Qx8.exp_conj_uh hg]
    exact hint _ (hU.2 t) (Qx8.exp_fix hky.2 t) v

theorem hyp_snoc {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W] {n r : ℕ}
    {z e : Fin (2 * r + (n + 1) + 1) → ℂ} {π : Mx (n + 1) r → (W →L[ℂ] W)} {u : ℕ → ℝ} {β : ℂ}
    {L : Fin (n + 1) → ℤ} (hz : inWb (n + 1) r z) (hT : 0 < Tz (n + 1) r z) (hty : IsType (n + 1) r z π u)
    (hL : StrictAnti L)
    (hu : ∀ j : Fin (n + 1), (u ((j : ℕ) + 1) : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 = β + (L j : ℂ))
    (he : inWb (n + 1) r e) (hez : herm (Hpk (n + 1) r) e z = 0) (hee : herm (Hpk (n + 1) r) e e = 1)
    {Bs₀ : Fin n → Fin (2 * r + (n + 1) + 1) → ℂ} (hB₀ : IsFrameOf (n + 1) r [z, e] Bs₀) :
    Hyp (EB π (Fin.snoc (α := fun _ => Fin (2 * r + (n + 1) + 1) → ℂ) Bs₀ e)) β L := by
  obtain ⟨hnt, hrep, hcont, -, hirr, hcap⟩ := hty
  have hR : IsRepW (n + 1) r z π := ⟨hrep, hcont⟩
  have hB₁ := FrameExtension.frame_snoc hB₀ he hez hee
  set Bs₁ : Fin (n + 1) → Fin (2 * r + (n + 1) + 1) → ℂ :=
    Fin.snoc (α := fun _ => Fin (2 * r + (n + 1) + 1) → ℂ) Bs₀ e with hBs₁
  obtain ⟨hgl, hq⟩ := frame_general_linear W (n + 1) r (n + 1) z π Bs₁ hR hB₁
  refine ⟨hgl, ⟨hnt, fun S hS => hirr S (lie_stabilizer W (n + 1) r z π Bs₁ hz hT hR hB₁ S hS)⟩, hL, ?_⟩
  intro w v
  rw [← hq w v, hcap Bs₁ hB₁ w v, FrameExtension.prod_Icc_fin]
  congr 1
  unfold cpol shf
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [← hu j]
  ring

theorem labels2 {n r : ℕ} {T T' : ℝ} {u u' : ℕ → ℝ} (hOK : (⟨n + 1, r, T, T', u, u'⟩ : M.Par).OK)
    (ρ : M.Ty ⟨n + 1, r, T, T', u, u'⟩) (L L' : Fin (n + 1) → ℤ)
    (hL : ∀ j : Fin (n + 1), u ((j : ℕ) + 1) - u 1 = (L j : ℝ))
    (hL' : ∀ j : Fin (n + 1), u' ((j : ℕ) + 1) - u 1 = (L' j : ℝ)) (lab : Fin n → ℤ)
    (hlab : ∀ j : Fin n, (lab j : ℝ) = M.rho ⟨n + 1, r, T, T', u, u'⟩ ρ ((j : ℕ) + 1) - u 1 + 1 / 2) :
    Box L lab ∧ Box L' lab ∧
      ∀ Y : ℂ, cpol (shf ((u 1 : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2) lab) (Y + (((n + 1 : ℕ) : ℂ) - 2) / 2) =
        Formalism.FourierDecayAlt.M.xC ⟨n + 1, r, T, T', u, u'⟩ ρ Y := by
  have hmem : ∀ j : Fin n, (j : ℕ) + 1 ∈ Finset.Icc 1 ((⟨n + 1, r, T, T', u, u'⟩ : M.Par).k - 1) := fun j =>
    Finset.mem_Icc.2 ⟨by omega, by show (j : ℕ) + 1 ≤ n + 1 - 1; omega⟩
  have hI := types_interlace _ hOK ρ
  have hI' : ∀ j : Fin n, M.rho ⟨n + 1, r, T, T', u, u'⟩ ρ ((j : ℕ) + 1) + 1 / 2 ≤ u ((j : ℕ) + 1) ∧
      M.rho ⟨n + 1, r, T, T', u, u'⟩ ρ ((j : ℕ) + 1) + 1 / 2 ≤ u' ((j : ℕ) + 1) ∧ u ((j : ℕ) + 1 + 1) + 1 / 2 ≤ M.rho ⟨n + 1, r, T, T', u, u'⟩ ρ ((j : ℕ) + 1) ∧
      u' ((j : ℕ) + 1 + 1) + 1 / 2 ≤ M.rho ⟨n + 1, r, T, T', u, u'⟩ ρ ((j : ℕ) + 1) := fun j => hI _ (hmem j)
  refine ⟨?_, ?_, ?_⟩
  · intro j
    have h1 := hL j.succ
    have h2 := hL j.castSucc
    simp only [Fin.val_succ, Fin.val_castSucc] at h1 h2
    have h3 := hI' j
    have h4 := hlab j
    constructor
    · have : (L j.succ : ℝ) < (lab j : ℝ) := by linarith
      exact_mod_cast this
    · have : (lab j : ℝ) ≤ (L j.castSucc : ℝ) := by linarith
      exact_mod_cast this
  · intro j
    have h1 := hL' j.succ
    have h2 := hL' j.castSucc
    simp only [Fin.val_succ, Fin.val_castSucc] at h1 h2
    have h3 := hI' j
    have h4 := hlab j
    constructor
    · have : (L' j.succ : ℝ) < (lab j : ℝ) := by linarith
      exact_mod_cast this
    · have : (lab j : ℝ) ≤ (L' j.castSucc : ℝ) := by linarith
      exact_mod_cast this
  · intro Y
    unfold M.xC cpol
    rw [show (⟨n + 1, r, T, T', u, u'⟩ : M.Par).k - 1 = n from rfl, ProductIntervalFrames.prod_Icc_one]
    refine Finset.prod_congr rfl fun j _ => ?_
    have h4 : (lab j : ℂ) = (M.rho ⟨n + 1, r, T, T', u, u'⟩ ρ ((j : ℕ) + 1) : ℂ) - (u 1 : ℂ) + 1 / 2 := by
      have := congrArg (fun x : ℝ => (x : ℂ)) (hlab j)
      push_cast at this
      exact this
    simp only [shf]
    rw [h4]
    push_cast
    ring

section io

variable {k r : ℕ}

theorem section_embedding_mul_vec (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (ζ : ℂ)
    (v : Fin (2 * r + k + 1) → ℂ) :
    SSn.io0 k r z z' μsec ζ *ᵥ v = NF.muZ k r μsec ζ *ᵥ (SSn.prWv k r z' v -
      herm (Hpk k r) (SSn.prWv k r z' v) (SSn.nu0' k r z z' μsec ζ) • SSn.nu0' k r z z' μsec ζ) := by
  set ν := SSn.nu0' k r z z' μsec ζ with hν
  let f : (Fin (2 * r + k + 1) → ℂ) →ₗ[ℂ] (Fin (2 * r + k + 1) → ℂ) :=
    { toFun := fun v => NF.muZ k r μsec ζ *ᵥ (SSn.prWv k r z' v - herm (Hpk k r) (SSn.prWv k r z' v) ν • ν)
      map_add' := fun x y => by
        rw [← Matrix.mulVec_add, TF.prWv_add, DU.hadd_l, add_smul]
        congr 1
        abel
      map_smul' := fun c x => by
        rw [TF.prWv_smul, DU.hsmul_l, RingHom.id_apply, ← Matrix.mulVec_smul, smul_sub, smul_smul] }
  have e : SSn.io0 k r z z' μsec ζ = LinearMap.toMatrix' f := by
    ext i j
    rw [LinearMap.toMatrix'_apply]
    rfl
  rw [e, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  rfl

end io

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.TW
end

open Matrix Finset Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.TW

noncomputable section

open Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P

variable {n r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem nu0'_facts (Bs : B.RealPlaceData (n + 1) r Wp Wq) {ζ : ℂ}
    (hζ : Tz (n + 1) r Bs.z * Tz (n + 1) r Bs.z' < Complex.normSq ζ) {m : ℕ}
    {Fr' : Fin m → Fin (2 * r + (n + 1) + 1) → ℂ}
    (hFr' : IsFrameOf (n + 1) r [(NF.muZ (n + 1) r Bs.μsec ζ)⁻¹ *ᵥ Bs.z, Bs.z'] Fr') :
    inWb (n + 1) r (SSn.nu0' (n + 1) r Bs.z Bs.z' Bs.μsec ζ) ∧
      herm (Hpk (n + 1) r) (SSn.nu0' (n + 1) r Bs.z Bs.z' Bs.μsec ζ) Bs.z' = 0 ∧
      IsFrameOf (n + 1) r [Bs.z', SSn.nu0' (n + 1) r Bs.z Bs.z' Bs.μsec ζ] Fr' := by
  have hz := Bs.z_mem
  have hz' := Bs.z'_mem
  obtain ⟨-, -, hfix, -⟩ := DU.base hz hz' Bs.T_pos Bs.T'_pos Bs.sec hζ
  have hm := NFRadRedA.muZ_uwb Bs.sec hζ
  have hG := NFRadRedA.uwb_glev hm
  have hGi := FrameEntries.glev_inv hG
  have hy : inWb (n + 1) r ((NF.muZ (n + 1) r Bs.μsec ζ)⁻¹ *ᵥ Bs.z) := Qx8.inWb_mulVec hGi hz
  have hW : inWb (n + 1) r (SSn.nu0' (n + 1) r Bs.z Bs.z' Bs.μsec ζ) := by
    show inWb (n + 1) r (SSn.unitH (n + 1) r (SSn.prWv (n + 1) r Bs.z' ((NF.muZ (n + 1) r Bs.μsec ζ)⁻¹ *ᵥ Bs.z)))
    unfold SSn.unitH
    exact Qx8.inWb_smul (DU.prWv_inWb hz' hy) _
  refine ⟨hW, ?_, hFr'.1, hFr'.2.1, fun a w hw => ?_⟩
  · rw [← hfix]; exact DU.prWv_perp Bs.T'_pos hW
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact hFr'.2.2 a _ (by simp)
    · show herm (Hpk (n + 1) r) (Fr' a)
        (SSn.unitH (n + 1) r (SSn.prWv (n + 1) r Bs.z' ((NF.muZ (n + 1) r Bs.μsec ζ)⁻¹ *ᵥ Bs.z))) = 0
      have h0 : herm (Hpk (n + 1) r) (Fr' a)
          (SSn.prWv (n + 1) r Bs.z' ((NF.muZ (n + 1) r Bs.μsec ζ)⁻¹ *ᵥ Bs.z)) = 0 := by
        rw [DU.prWv_of hy, DU.hadd_r, DU.hsmul_r, hFr'.2.2 a ((NF.muZ (n + 1) r Bs.μsec ζ)⁻¹ *ᵥ Bs.z) (by simp),
          hFr'.2.2 a Bs.z' (by simp), mul_zero, add_zero]
      unfold SSn.unitH
      rw [DU.hsmul_r, h0, mul_zero]

theorem tht_adapted (Bs : B.RealPlaceData (n + 1) r Wp Wq) {ζ : ℂ}
    (hζ : Tz (n + 1) r Bs.z * Tz (n + 1) r Bs.z' < Complex.normSq ζ)
    {Bw Bw' : Fin (n + 1) → Fin (2 * r + (n + 1) + 1) → ℂ} (hBw : IsFrameOf (n + 1) r [Bs.z] Bw)
    (hBw' : IsFrameOf (n + 1) r [Bs.z'] Bw') {Fr : Fin n → Fin (2 * r + (n + 1) + 1) → ℂ}
    (hB₁ : IsFrameOf (n + 1) r [Bs.z]
      (Fin.snoc (α := fun _ => Fin (2 * r + (n + 1) + 1) → ℂ) Fr (SSn.nu0 (n + 1) r Bs.z Bs.z' Bs.μsec ζ)))
    (hFr' : IsFrameOf (n + 1) r [(NF.muZ (n + 1) r Bs.μsec ζ)⁻¹ *ᵥ Bs.z, Bs.z']
      (fun a => (NF.muZ (n + 1) r Bs.μsec ζ)⁻¹ *ᵥ Fr a)) (X : Wq →L[ℂ] Wp) (v : Wq) :
    tht (n + 1) r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' (SSn.nu0 (n + 1) r Bs.z Bs.z' Bs.μsec ζ)
        (SSn.nu0' (n + 1) r Bs.z Bs.z' Bs.μsec ζ) (SSn.io0 (n + 1) r Bs.z Bs.z' Bs.μsec ζ) X v =
      ∑ c : Fin n, etaK (EB Bs.π (Fin.snoc (α := fun _ => Fin (2 * r + (n + 1) + 1) → ℂ) Fr
          (SSn.nu0 (n + 1) r Bs.z Bs.z' Bs.μsec ζ))) c
        (X (yK (EB Bs.π' (Fin.snoc (α := fun _ => Fin (2 * r + (n + 1) + 1) → ℂ)
          (fun a => (NF.muZ (n + 1) r Bs.μsec ζ)⁻¹ *ᵥ Fr a) (SSn.nu0' (n + 1) r Bs.z Bs.z' Bs.μsec ζ))) c v)) := by
  have hz := Bs.z_mem
  have hz' := Bs.z'_mem
  have hT := Bs.T_pos
  have hT' := Bs.T'_pos
  have hR : IsRepW (n + 1) r Bs.z Bs.π := ⟨Bs.π_rep, Bs.π_cont⟩
  have hR' : IsRepW (n + 1) r Bs.z' Bs.π' := ⟨Bs.π'_rep, Bs.π'_cont⟩
  obtain ⟨hνfix, hνν, hν'fix, hν'ν'⟩ := DU.base hz hz' hT hT' Bs.sec hζ
  obtain ⟨hν'W, hν'z, hFr2⟩ := nu0'_facts Bs hζ hFr'
  have hm := NFRadRedA.muZ_uwb Bs.sec hζ
  have hG := NFRadRedA.uwb_glev hm
  have hU : NF.muZ (n + 1) r Bs.μsec ζ ∈ UH (Hpk (n + 1) r) := hG.1
  have hmm : NF.muZ (n + 1) r Bs.μsec ζ * (NF.muZ (n + 1) r Bs.μsec ζ)⁻¹ = 1 := Gauge.GC.KLAM.mul_inv_uh hU
  set μ := NF.muZ (n + 1) r Bs.μsec ζ with hμ
  set ν := SSn.nu0 (n + 1) r Bs.z Bs.z' Bs.μsec ζ with hν
  set ν' := SSn.nu0' (n + 1) r Bs.z Bs.z' Bs.μsec ζ with hν'
  have hB₁' := FrameExtension.frame_snoc hFr2 hν'W hν'z hν'ν'
  set B₁ : Fin (n + 1) → Fin (2 * r + (n + 1) + 1) → ℂ :=
    Fin.snoc (α := fun _ => Fin (2 * r + (n + 1) + 1) → ℂ) Fr ν with hB₁def
  set B₁' : Fin (n + 1) → Fin (2 * r + (n + 1) + 1) → ℂ :=
    Fin.snoc (α := fun _ => Fin (2 * r + (n + 1) + 1) → ℂ) (fun a => μ⁻¹ *ᵥ Fr a) ν' with hB₁'def
  have hBc : ∀ c : Fin n, B₁ c.castSucc = Fr c := fun c => by rw [hB₁def, Fin.snoc_castSucc]
  have hBl : B₁ (Fin.last n) = ν := by rw [hB₁def, Fin.snoc_last]
  have hBc' : ∀ c : Fin n, B₁' c.castSucc = μ⁻¹ *ᵥ Fr c := fun c => by rw [hB₁'def, Fin.snoc_castSucc]
  have hBl' : B₁' (Fin.last n) = ν' := by rw [hB₁'def, Fin.snoc_last]
  rw [TF.tht_indep hz hT hR hz' hT' hR' hBw hB₁ hBw' hB₁' ν ν' _, TF.tht_form hz hT hR hB₁, hνfix, hν'fix]
  simp only [ContinuousLinearMap.sum_apply, TF.sandw_apply, ContinuousLinearMap.comp_apply]
  rw [Fin.sum_univ_castSucc]
  have hlast : SSn.io0 (n + 1) r Bs.z Bs.z' Bs.μsec ζ *ᵥ B₁' (Fin.last n) = 0 := by
    rw [section_embedding_mul_vec, hBl', ← hν', hν'fix, hν'ν', one_smul, sub_self, Matrix.mulVec_zero]
  have hpr0 : SSn.prWv (n + 1) r Bs.z (0 : Fin (2 * r + (n + 1) + 1) → ℂ) = 0 := by
    have := TF.prWv_smul (k := n + 1) (r := r) Bs.z 0 0
    simpa using this
  rw [hlast, hpr0, TF.ebM_zero_left, TF.ecOp_zero, ContinuousLinearMap.zero_apply, add_zero]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hc : SSn.io0 (n + 1) r Bs.z Bs.z' Bs.μsec ζ *ᵥ B₁' c.castSucc = Fr c := by
    rw [section_embedding_mul_vec, hBc', ← hν', DU.prWv_fix (hFr2.1 c) (hFr2.2.2 c Bs.z' (by simp)), hFr2.2.2 c ν' (by simp),
      zero_smul, sub_zero, Matrix.mulVec_mulVec, hmm, Matrix.one_mulVec]
  have hFc : SSn.prWv (n + 1) r Bs.z (Fr c) = Fr c := by
    rw [← hBc c]
    exact DU.prWv_fix (hB₁.1 _) (hB₁.2.2 _ Bs.z (by simp))
  rw [hc, hFc]
  have e1 : ebM (n + 1) r (Fr c) ν = unitB (Hpk (n + 1) r) B₁ c.castSucc (Fin.last n) := by
    rw [← TF.ebM_frame, hBc, hBl]
  have e2 : ebM (n + 1) r ν' (B₁' c.castSucc) = unitB (Hpk (n + 1) r) B₁' (Fin.last n) c.castSucc := by
    rw [← TF.ebM_frame, hBl']
  rw [e1, e2]
  rfl

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.TW
end

open Matrix Finset Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR

noncomputable section

open Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P

theorem core (hAlg : TW.TWNeAlg) {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (n r : ℕ) (T T' : ℝ) (u u' : ℕ → ℝ) (Bs : B.RealPlaceData (n + 1) r Wp Wq)
    (hpl : IsPlace ⟨n + 1, r, T, T', u, u'⟩ Bs.z Bs.z' Bs.π Bs.π') (hk : 2 ≤ n + 1)
    (Pr : M.Ty ⟨n + 1, r, T, T', u, u'⟩ → (Fin (2 * r + (n + 1) + 1) → ℂ) → (Wp →L[ℂ] Wp))
    (hPr : PRho.PRhoSpec ⟨n + 1, r, T, T', u, u'⟩ Bs.z Bs.π Pr)
    (Bw Bw' : Fin (n + 1) → Fin (2 * r + (n + 1) + 1) → ℂ) (hBw : IsFrameOf (n + 1) r [Bs.z] Bw)
    (hBw' : IsFrameOf (n + 1) r [Bs.z'] Bw') (l : ℕ) (hl : l ∈ Finset.Icc 1 n)
    (π ρ : M.Ty ⟨n + 1, r, T, T', u, u'⟩) (hUp : M.Up ⟨n + 1, r, T, T', u, u'⟩ l π ρ) (ζ : ℂ)
    (hζT : T * T' < Complex.normSq ζ) (Xf : Wq →L[ℂ] Wp)
    (hXf : Xf ∈ NF.Fib (n + 1) r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ)
    (hfix : (Pr π (SSn.nu0 (n + 1) r Bs.z Bs.z' Bs.μsec ζ)).comp Xf = Xf) (hX0 : Xf ≠ 0) :
    (Pr ρ (SSn.nu0 (n + 1) r Bs.z Bs.z' Bs.μsec ζ)).comp (tht (n + 1) r Bs.z Bs.z' Bs.π Bs.π' Bw Bw'
      (SSn.nu0 (n + 1) r Bs.z Bs.z' Bs.μsec ζ) (SSn.nu0' (n + 1) r Bs.z Bs.z' Bs.μsec ζ)
      (SSn.io0 (n + 1) r Bs.z Bs.z' Bs.μsec ζ) Xf) ≠ 0 := by
  have hOK : (⟨n + 1, r, T, T', u, u'⟩ : M.Par).OK := hpl.1
  have hz : inWb (n + 1) r Bs.z := Bs.z_mem
  have hz' : inWb (n + 1) r Bs.z' := Bs.z'_mem
  have hTz : Tz (n + 1) r Bs.z = T := hpl.2.2.2.1
  have hTz' : Tz (n + 1) r Bs.z' = T' := hpl.2.2.2.2.1
  have hπ : IsType (n + 1) r Bs.z Bs.π u := hpl.2.2.2.2.2.1
  have hπ' : IsType (n + 1) r Bs.z' Bs.π' u' := hpl.2.2.2.2.2.2
  have hζ' : Tz (n + 1) r Bs.z * Tz (n + 1) r Bs.z' < Complex.normSq ζ := by
    rw [hTz, hTz']; exact hζT
  have hT : 0 < Tz (n + 1) r Bs.z := Bs.T_pos
  have hT' : 0 < Tz (n + 1) r Bs.z' := Bs.T'_pos
  have hR : IsRepW (n + 1) r Bs.z Bs.π := ⟨Bs.π_rep, Bs.π_cont⟩
  have hR' : IsRepW (n + 1) r Bs.z' Bs.π' := ⟨Bs.π'_rep, Bs.π'_cont⟩
  obtain ⟨hνfix, hνν, hν'fix, hν'ν'⟩ := DU.base hz hz' hT hT' Bs.sec hζ'
  have hm := NFRadRedA.muZ_uwb Bs.sec hζ'
  have hG := NFRadRedA.uwb_glev hm
  have hU : NF.muZ (n + 1) r Bs.μsec ζ ∈ UH (Hpk (n + 1) r) := hG.1
  have hmm : NF.muZ (n + 1) r Bs.μsec ζ * (NF.muZ (n + 1) r Bs.μsec ζ)⁻¹ = 1 := Gauge.GC.KLAM.mul_inv_uh hU
  have hy : inWb (n + 1) r (NF.muZ (n + 1) r Bs.μsec ζ *ᵥ Bs.z') := Qx8.inWb_mulVec hG hz'
  have hνW : inWb (n + 1) r (SSn.nu0 (n + 1) r Bs.z Bs.z' Bs.μsec ζ) := by
    show inWb (n + 1) r (SSn.unitH (n + 1) r (SSn.prWv (n + 1) r Bs.z (NF.muZ (n + 1) r Bs.μsec ζ *ᵥ Bs.z')))
    unfold SSn.unitH
    exact Qx8.inWb_smul (DU.prWv_inWb hz hy) _
  have hνz : herm (Hpk (n + 1) r) (SSn.nu0 (n + 1) r Bs.z Bs.z' Bs.μsec ζ) Bs.z = 0 := by
    rw [← hνfix]; exact DU.prWv_perp hT hνW
  obtain ⟨Fr, hFr⟩ := exists_frame_two n r Bs.z _ hz hT hνW hνz hνν
  have hFr' : IsFrameOf (n + 1) r [(NF.muZ (n + 1) r Bs.μsec ζ)⁻¹ *ᵥ Bs.z, Bs.z']
      (fun a => (NF.muZ (n + 1) r Bs.μsec ζ)⁻¹ *ᵥ Fr a) :=
    (PRho.GL.gauge_left_line_holds Wp Wq ⟨n + 1, r, T, T', u, u'⟩ Bs hpl hk ζ hζT Fr hFr).1
  obtain ⟨hν'W, hν'z, hFr2⟩ := TW.nu0'_facts Bs hζ' hFr'
  have hB₁ := FrameExtension.frame_snoc hFr hνW hνz hνν
  set μ := NF.muZ (n + 1) r Bs.μsec ζ with hμ
  set ν := SSn.nu0 (n + 1) r Bs.z Bs.z' Bs.μsec ζ with hν
  set ν' := SSn.nu0' (n + 1) r Bs.z Bs.z' Bs.μsec ζ with hν'

  have hIcc : ∀ j : Fin (n + 1), (j : ℕ) + 1 ∈ Finset.Icc 1 (n + 1) := fun j =>
    Finset.mem_Icc.2 ⟨by omega, by omega⟩
  choose L hL using fun j : Fin (n + 1) => hOK.int_u ((j : ℕ) + 1) (hIcc j)
  choose L' hL' using fun j : Fin (n + 1) => hOK.int_u' ((j : ℕ) + 1) (hIcc j)
  have hL2 : ∀ j : Fin (n + 1), u ((j : ℕ) + 1) - u 1 = (L j : ℝ) := hL
  have hL2' : ∀ j : Fin (n + 1), u' ((j : ℕ) + 1) - u 1 = (L' j : ℝ) := hL'
  have hgap : ∀ j : Fin n, max (u ((j : ℕ) + 1 + 1)) (u' ((j : ℕ) + 1 + 1)) + 1 / 2 ≤
      min (u ((j : ℕ) + 1)) (u' ((j : ℕ) + 1)) - 1 / 2 := fun j =>
    hOK.gap ((j : ℕ) + 1) (Finset.mem_Icc.2 ⟨by omega, by show (j : ℕ) + 1 ≤ n + 1 - 1; omega⟩)
  have hanti : StrictAnti L := Fin.strictAnti_iff_succ_lt.2 fun j => by
    have h1 := hL2 j.castSucc
    have h2 := hL2 j.succ
    simp only [Fin.val_castSucc, Fin.val_succ] at h1 h2
    have h3 := hgap j
    have h5 := le_max_left (u ((j : ℕ) + 1 + 1)) (u' ((j : ℕ) + 1 + 1))
    have h6 := min_le_left (u ((j : ℕ) + 1)) (u' ((j : ℕ) + 1))
    have : (L j.succ : ℝ) < (L j.castSucc : ℝ) := by linarith
    exact_mod_cast this
  have hanti' : StrictAnti L' := Fin.strictAnti_iff_succ_lt.2 fun j => by
    have h1 := hL2' j.castSucc
    have h2 := hL2' j.succ
    simp only [Fin.val_castSucc, Fin.val_succ] at h1 h2
    have h3 := hgap j
    have h5 := le_max_right (u ((j : ℕ) + 1 + 1)) (u' ((j : ℕ) + 1 + 1))
    have h6 := min_le_right (u ((j : ℕ) + 1)) (u' ((j : ℕ) + 1))
    have : (L' j.succ : ℝ) < (L' j.castSucc : ℝ) := by linarith
    exact_mod_cast this
  set β : ℂ := (u 1 : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 with hβ
  have hrel : ∀ j : Fin (n + 1), (u ((j : ℕ) + 1) : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 = β + (L j : ℂ) := fun j => by
    have h : (u ((j : ℕ) + 1) : ℂ) - (u 1 : ℂ) = (L j : ℂ) := by
      exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) (hL2 j)
    rw [hβ, ← h]
    ring
  have hrel' : ∀ j : Fin (n + 1), (u' ((j : ℕ) + 1) : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 = β + (L' j : ℂ) := fun j => by
    have h : (u' ((j : ℕ) + 1) : ℂ) - (u 1 : ℂ) = (L' j : ℂ) := by
      exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) (hL2' j)
    rw [hβ, ← h]
    ring

  have hmem : ∀ j : Fin n, (j : ℕ) + 1 ∈ Finset.Icc 1 ((⟨n + 1, r, T, T', u, u'⟩ : M.Par).k - 1) := fun j =>
    Finset.mem_Icc.2 ⟨by omega, by show (j : ℕ) + 1 ≤ n + 1 - 1; omega⟩
  choose N hN using fun j : Fin n => Qx8.rho_int hOK π ((j : ℕ) + 1) (hmem j)
  have hl' := Finset.mem_Icc.1 hl
  have hln : l - 1 < n := by omega
  set i₀ : Fin n := ⟨l - 1, hln⟩ with hi₀
  set Mπ : Fin n → ℤ := fun j => N j + 1 with hMπ
  have hlabπ : ∀ j : Fin n, (Mπ j : ℝ) = M.rho ⟨n + 1, r, T, T', u, u'⟩ π ((j : ℕ) + 1) - u 1 + 1 / 2 := fun j => by
    have := hN j
    change M.rho ⟨n + 1, r, T, T', u, u'⟩ π ((j : ℕ) + 1) - u 1 - 1 / 2 = (N j : ℝ) at this
    rw [hMπ]
    push_cast
    linarith
  have hlabρ : ∀ j : Fin n, ((Function.update Mπ i₀ (Mπ i₀ + 1) j : ℤ) : ℝ) =
      M.rho ⟨n + 1, r, T, T', u, u'⟩ ρ ((j : ℕ) + 1) - u 1 + 1 / 2 := fun j => by
    rw [rho_raise _ l π ρ hUp _ (hmem j)]
    by_cases hj : j = i₀
    · subst hj
      have e : ((i₀ : Fin n) : ℕ) + 1 = l := by rw [hi₀]; show l - 1 + 1 = l; omega
      rw [Function.update_self, if_pos e]
      push_cast
      rw [hlabπ i₀]
      ring
    · have e : ¬ ((j : ℕ) + 1 = l) := fun h => hj (Fin.ext (by rw [hi₀]; show (j : ℕ) = l - 1; omega))
      rw [Function.update_of_ne hj, if_neg e, hlabπ j]
      ring
  obtain ⟨hbπ, hbπ', hcpπ⟩ := TW.labels2 hOK π L L' hL2 hL2' Mπ hlabπ
  obtain ⟨hbρ, hbρ', hcpρ⟩ := TW.labels2 hOK ρ L L' hL2 hL2' _ hlabρ

  have hH := TW.hyp_snoc hz hT hπ hanti hrel hνW hνz hνν hFr
  have hH' := TW.hyp_snoc hz' hT' hπ' hanti' hrel' hν'W hν'z hν'ν' hFr2
  have hsub : subA (EB Bs.π (Fin.snoc (α := fun _ => Fin (2 * r + (n + 1) + 1) → ℂ) Fr ν)) = EB Bs.π Fr :=
    FrameExtension.subA_EB Bs.π Fr ν
  have hsub' : subA (EB Bs.π' (Fin.snoc (α := fun _ => Fin (2 * r + (n + 1) + 1) → ℂ) (fun a => μ⁻¹ *ᵥ Fr a) ν')) =
      EB Bs.π' (fun a => μ⁻¹ *ᵥ Fr a) := FrameExtension.subA_EB Bs.π' _ ν'
  have hq := (frame_general_linear Wp (n + 1) r n Bs.z Bs.π Fr hR (FrameExtension.frame_weaken hFr)).2
  have hback : (fun a => μ *ᵥ (μ⁻¹ *ᵥ Fr a)) = Fr := by
    funext a
    rw [Matrix.mulVec_mulVec, hmm, Matrix.one_mulVec]
  have hXF : Xf ∈ Gauge.GC.FibAt (n + 1) r Bs.z Bs.z' Bs.π Bs.π' μ :=
    fun h hh h' hh' he => hXf (h, h') ⟨hh, hh', he⟩
  have hpos : 0 < PRho.nrmW (n + 1) r Bs.z ν := by
    unfold PRho.nrmW
    rw [hνfix, hνν]; simp
  have hrange : ∀ (σ : M.Ty ⟨n + 1, r, T, T', u, u'⟩) (x : Wp), Pr σ ν x = x ↔
      ∀ Fr2 : Fin n → Fin (2 * r + (n + 1) + 1) → ℂ, IsFrameOf (n + 1) r [Bs.z, SSn.prWv (n + 1) r Bs.z ν] Fr2 →
        ∀ w : ℂ, capRep (n + 1) r Bs.π Fr2 w x =
          M.xC ⟨n + 1, r, T, T', u, u'⟩ σ (w - (((n + 1 : ℕ) : ℂ) - 2) / 2) • x := (hPr.2.2 ν hpos).2.2.2
  have hJi : ∀ (a b : Fin n) (v : Wq), (Xf : Wq →ₗ[ℂ] Wp)
      (subA (EB Bs.π' (Fin.snoc (α := fun _ => Fin (2 * r + (n + 1) + 1) → ℂ) (fun a => μ⁻¹ *ᵥ Fr a) ν')) a b v) =
      subA (EB Bs.π (Fin.snoc (α := fun _ => Fin (2 * r + (n + 1) + 1) → ℂ) Fr ν)) a b ((Xf : Wq →ₗ[ℂ] Wp) v) := by
    intro a b v
    rw [hsub, hsub']
    have h := TW.eb_intertwine hFr' hR hR' hU (by rw [hback]; exact FrameExtension.frame_weaken hFr) Xf
      (fun h' hh' hy' w => Gauge.GC.KLAM.fib_intertwine Bs.π_rep hG hXF hh' hy' w) a b v
    rw [hback] at h
    exact h
  have hJr : ∀ v : Wq, (Xf : Wq →ₗ[ℂ] Wp) v ∈
      CapSp (subA (EB Bs.π (Fin.snoc (α := fun _ => Fin (2 * r + (n + 1) + 1) → ℂ) Fr ν))) (shf β Mπ) := by
    intro v
    rw [hsub, mem_CapSp]
    intro w
    have h1 : Pr π ν (Xf v) = Xf v := by
      have := congrArg (fun A : Wq →L[ℂ] Wp => A v) hfix
      exact this
    have h2 := (hrange π (Xf v)).1 h1 Fr (by rw [hνfix]; exact hFr) w
    have h3 := hcpπ (w - (((n + 1 : ℕ) : ℂ) - 2) / 2)
    rw [sub_add_cancel] at h3
    show qdet (EB Bs.π Fr) w (Xf v) = _
    rw [← hq w (Xf v), h3]
    exact h2
  have hJ0 : (Xf : Wq →ₗ[ℂ] Wp) ≠ 0 := fun h => hX0 (by
    ext v
    exact LinearMap.congr_fun h v)
  obtain ⟨v', hne, hmemW⟩ := hAlg Wp Wq n _ _ β β L L' Mπ Mπ i₀ hH hH' hbπ hbπ' hbρ hbρ' rfl
    (Xf : Wq →ₗ[ℂ] Wp) hJ0 hJi hJr
  intro h0
  apply hne
  have h1 := congrArg (fun A : Wq →L[ℂ] Wp => A v') h0
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply] at h1
  rw [TW.tht_adapted Bs hζ' hBw hBw' hB₁ hFr' Xf v'] at h1
  rw [← h1]
  symm
  refine (hrange ρ _).2 ?_
  intro Fr2 hFr2 w
  rw [hνfix] at hFr2
  rw [hsub, mem_CapSp] at hmemW
  have h3 := hcpρ (w - (((n + 1 : ℕ) : ℂ) - 2) / 2)
  rw [sub_add_cancel] at h3
  rw [Topx1.typ_frame_change (n + 1) r (by omega) Bs.z ν Bs.π Fr2 Fr hz hT hνW hνz hνν hR hFr2 hFr w _, hq w _]
  refine (hmemW w).trans ?_
  rw [h3]
  rfl

theorem tWNe_of_alg (hAlg : TW.TWNeAlg) : TWNe := by
  intro Wp Wq _ _ _ _ _ _ P
  obtain ⟨k, r, T, T', u, u'⟩ := P
  rcases k with _ | n
  · intro Bs hpl hk
    exact absurd hk (by show ¬ (2 ≤ 0); omega)
  intro Bs hpl hk Pr hPr Bw Bw' hBw hBw' l hl π ρ hUp ζ hζ Xf hXf hfix hX0
  exact core hAlg n r T T' u u' Bs hpl hk Pr hPr Bw Bw' hBw hBw' l hl π ρ hUp ζ hζ Xf hXf hfix hX0

theorem word_nonvanishing_holds : TWNe := tWNe_of_alg TW.word_nonvanishing_algebraic

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR
