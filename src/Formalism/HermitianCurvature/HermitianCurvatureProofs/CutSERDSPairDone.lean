module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLExhAll
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ProperDomP

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSPair
open MeasureTheory Filter Topology
open scoped Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

def eR (k r : ℕ) (x : (Fin r → ℂ) × Mx k r) : B.Mat k r := wCell k r (Fin.last r) x.1 * x.2

def RDSPIpSwap : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (π : Mx k r → (Wp →L[ℂ] Wp)) (π' : Mx k r → (Wq →L[ℂ] Wq)) (μ : Measure (Mt k r))
    (Φ Ψ : RadSp k r z z' π π') (c : Fin r → ℂ), radIp μ Φ Ψ = LocFacts₂ μ 0 Ψ Φ c

def RDSPEOm : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq),
    (∀ x ∈ DomR k r D.z D.z', eR k r x ∈ JF.Om k r D.z D.z') ∧ ContinuousOn (eR k r) (DomR k r D.z D.z') ∧
      JF.Om k r D.z D.z' ⊆ B.GPos D

def RDSPZeroR : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (X Y : B.Mat k r → (Wq →L[ℂ] Wp)), X ∈ Q.FFl k r D.z D.z' D.π D.π' 0 (JF.Om k r D.z D.z') →
      Y ∈ Q.FFl k r D.z D.z' D.π D.π' 0 (JF.Om k r D.z D.z') →
      (∀ x ∈ DomR k r D.z D.z', X (eR k r x) = Y (eR k r x)) → ∀ g ∈ JF.Om k r D.z D.z', X g = Y g

def RDSPExh : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq),
    ∀ X ∈ Q.FFl k r D.z D.z' D.π D.π' 0 (JF.Om k r D.z D.z'), ∀ C : Set (B.Mat k r), IsCompact C →
      C ⊆ JF.Om k r D.z D.z' →
      ∃ (F : B.Mat k r → (Wq →L[ℂ] Wp)) (U : Set (B.Mat k r)), B.CkOn ⊤ (B.GV k r) F ∧ HasCompactSupport F ∧
        tsupport F ⊆ JF.Om k r D.z D.z' ∧ IsOpen U ∧ C ⊆ U ∧
        (∀ p, D.inSS p → ∀ g ∈ JF.Om k r D.z D.z', B.sgs p g ∈ U → g ∈ U) ∧
        ∀ g ∈ JF.Om k r D.z D.z', (g ∈ U → B.JF D F g = X g) ∧ (X g = 0 → B.JF D F g = 0)

def RDSPJFMem : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)), B.CkOn ⊤ (B.GV k r) F → HasCompactSupport F → tsupport F ⊆ JF.Om k r D.z D.z' →
      B.JF D F ∈ Q.FFl k r D.z D.z' D.π D.π' 0 (JF.Om k r D.z D.z') ∧
      ∀ g ∈ JF.Om k r D.z D.z', B.JF D F g ≠ 0 → ∃ p, D.inSS p ∧ B.sgs p g ∈ tsupport F

def RDSPOp : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (Θ : B.DiffOp k r Wp Wq), B.SmoothCoef (B.GPos D) Θ → B.Commutes D (B.GPos D) Θ →
    ∀ F : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) F → HasCompactSupport F → tsupport F ⊆ JF.Om k r D.z D.z' →
      (B.CkOn ⊤ (B.GV k r) (B.opApply Θ F) ∧ HasCompactSupport (B.opApply Θ F) ∧
        tsupport (B.opApply Θ F) ⊆ tsupport F) ∧
      (B.CkOn ⊤ (B.GV k r) (B.opAdj Θ F) ∧ HasCompactSupport (B.opAdj Θ F) ∧
        tsupport (B.opAdj Θ F) ⊆ tsupport F) ∧
      ∀ g ∈ JF.Om k r D.z D.z', B.opApply Θ (B.JF D F) g = B.JF D (B.opApply Θ F) g ∧
        B.opAdj Θ (B.JF D F) g = B.JF D (B.opAdj Θ F) g

def RDSPLoc : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Θ : B.DiffOp k r Wp Wq)
    (U : Set (B.Mat k r)) (X Y : B.Mat k r → (Wq →L[ℂ] Wp)), IsOpen U → (∀ g ∈ U, g ∈ B.GV k r → X g = Y g) →
      ∀ g ∈ U, g ∈ B.GV k r → B.opApply Θ X g = B.opApply Θ Y g ∧ B.opAdj Θ X g = B.opAdj Θ Y g

section Help

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem rdsp_hsVec_zero : B.hsVec (0 : Wq →L[ℂ] Wp) = 0 := by
  unfold B.hsVec; simp; rfl

theorem rdsp_ip_congr {a b a' b' : Wq →L[ℂ] Wp} (hb : b = b') (ha : b ≠ 0 → a = a') :
    inner ℂ (B.hsVec a) (B.hsVec b) = inner ℂ (B.hsVec a') (B.hsVec b') := by
  by_cases h : b = 0
  · rw [← hb, h, rdsp_hsVec_zero, inner_zero_right, inner_zero_right]
  · rw [← hb, ha h]

theorem rdsp_resG_congr (J J' : B.Mat k r → (Wq →L[ℂ] Wp)) (x : (Fin r → ℂ) × Mx k r)
    (h : J (eR k r x) = J' (eR k r x)) :
    resG k r (Fin.last r) J x.1 x.2 = resG k r (Fin.last r) J' x.1 x.2 := by
  show _ • J (eR k r x) = _ • J' (eR k r x)
  rw [h]

theorem rdsp_resG_ne (J : B.Mat k r → (Wq →L[ℂ] Wp)) (x : (Fin r → ℂ) × Mx k r)
    (h : resG k r (Fin.last r) J x.1 x.2 ≠ 0) : J (eR k r x) ≠ 0 := by
  intro h0
  apply h
  show _ • J (eR k r x) = 0
  rw [h0, smul_zero]

theorem rdsp_resG_zero (J : B.Mat k r → (Wq →L[ℂ] Wp)) (x : (Fin r → ℂ) × Mx k r) (hx : x.1 ∈ OmX r)
    (h : resG k r (Fin.last r) J x.1 x.2 = 0) : J (eR k r x) = 0 := by
  have h' : ((∏ a : Fin r, (if a.val < (Fin.last r).val then ‖x.1 a‖ ^ (Mdim k r a - 1) else 1) : ℝ) : ℂ) •
      J (eR k r x) = 0 := h
  rcases smul_eq_zero.1 h' with h1 | h1
  · exfalso
    rw [Complex.ofReal_eq_zero, Finset.prod_eq_zero_iff] at h1
    obtain ⟨a, -, ha⟩ := h1
    rw [if_pos (show (a : ℕ) < ((Fin.last r : Fin (r + 1)) : ℕ) by simp)] at ha
    refine hx a (norm_eq_zero.1 ?_)
    rcases Nat.eq_zero_or_pos (Mdim k r a - 1) with hn | hn
    · rw [hn, pow_zero] at ha; exact absurd ha one_ne_zero
    · exact (pow_eq_zero_iff hn.ne').1 ha
  · exact h1

end Help

theorem rDSPair_of_cut (hSw : RDSPIpSwap) (hE : RDSPEOm) (hZ : RDSPZeroR) (hX : RDSPExh) (hM : RDSPJFMem)
    (hO : RDSPOp) (hL : RDSPLoc) : RDSPair := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' hr Θ hΘ J K hJ hK Φ₁ Φ₂ Φ₃ Φ₄ h1 h2 h3 h4
    hT
  subst hz hz' hπ hπ'
  obtain ⟨Kc, hKc, hKcD, hKc0⟩ := hT
  obtain ⟨hEO, hEc, hOP⟩ := hE P.k P.r Wp Wq D
  have hC0c : IsCompact (eR P.k P.r '' Kc) := hKc.image_of_continuousOn (hEc.mono hKcD)
  have hC0O : eR P.k P.r '' Kc ⊆ JF.Om P.k P.r D.z D.z' := by
    rintro _ ⟨x, hx, rfl⟩; exact hEO x (hKcD hx)
  obtain ⟨F₁, U₁, hF₁s, hF₁c, hF₁O, -, hC0U₁, -, hF₁K⟩ := hX P.k P.r Wp Wq D K hK _ hC0c hC0O
  obtain ⟨F₂, U₂, hF₂s, hF₂c, hF₂O, hU₂o, hCU₂, hU₂sat, hF₂J⟩ :=
    hX P.k P.r Wp Wq D J hJ _ (hC0c.union hF₁c) (Set.union_subset hC0O hF₁O)
  obtain ⟨⟨hA1s, hA1c, hA1t⟩, -, hJ1⟩ := hO P.k P.r Wp Wq D Θ hΘ.1 hΘ.2.1 F₁ hF₁s hF₁c hF₁O
  obtain ⟨-, ⟨hB2s, hB2c, hB2t⟩, hJ2⟩ := hO P.k P.r Wp Wq D Θ hΘ.1 hΘ.2.1 F₂ hF₂s hF₂c hF₂O
  have hF₁O' : tsupport (B.opApply Θ F₁) ⊆ JF.Om P.k P.r D.z D.z' := hA1t.trans hF₁O
  have hF₂O' : tsupport (B.opAdj Θ F₂) ⊆ JF.Om P.k P.r D.z D.z' := hB2t.trans hF₂O
  have hM1 := hM P.k P.r Wp Wq D F₁ hF₁s hF₁c hF₁O
  have hM2 := hM P.k P.r Wp Wq D F₂ hF₂s hF₂c hF₂O
  have hM3 := hM P.k P.r Wp Wq D _ hA1s hA1c hF₁O'
  have hM4 := hM P.k P.r Wp Wq D _ hB2s hB2c hF₂O'

  have hKeq : ∀ g ∈ JF.Om P.k P.r D.z D.z', K g = B.JF D F₁ g := by
    refine hZ P.k P.r Wp Wq D K (B.JF D F₁) hK hM1.1 fun x hx => ?_
    by_cases hxK : x ∈ Kc
    · exact ((hF₁K (eR P.k P.r x) (hEO x hx)).1 (hC0U₁ ⟨x, hxK, rfl⟩)).symm
    · have h0 : K (eR P.k P.r x) = 0 := by
        refine rdsp_resG_zero K x hx.1 ?_
        rw [← h2 x hx]; exact hKc0 x hxK
      rw [h0, (hF₁K (eR P.k P.r x) (hEO x hx)).2 h0]
  have hOpen : IsOpen (Q.OmPlus P.k P.r D.z D.z') := Formalism.FourierDecayAlt.P.PositiveOrbitOpen.omPlus_open D.z D.z'

  have hΘK : ∀ g ∈ JF.Om P.k P.r D.z D.z', B.opApply Θ K g = B.JF D (B.opApply Θ F₁) g := by
    intro g hg
    rw [(hL P.k P.r Wp Wq Θ _ K (B.JF D F₁) hOpen (fun g' hg' hgv => hKeq g' ⟨hgv, hg'⟩) g hg.2 hg.1).1]
    exact (hJ1 g hg).1

  have hΘJ : ∀ g ∈ JF.Om P.k P.r D.z D.z', g ∈ U₂ → B.opAdj Θ J g = B.JF D (B.opAdj Θ F₂) g := by
    intro g hg hgU
    rw [(hL P.k P.r Wp Wq Θ _ J (B.JF D F₂) (hU₂o.inter hOpen)
      (fun g' hg' hgv => ((hF₂J g' ⟨hgv, hg'.2⟩).1 hg'.1).symm) g ⟨hgU, hg.2⟩ hg.1).2]
    exact (hJ2 g hg).2

  obtain ⟨A₁, hA₁⟩ := radial_residue_formula Wp Wq P D.z D.z' D.π D.π' X μ L st l0 hD _ hM4.1
  obtain ⟨A₂, hA₂⟩ := radial_residue_formula Wp Wq P D.z D.z' D.π D.π' X μ L st l0 hD _ hM1.1
  obtain ⟨A₃, hA₃⟩ := radial_residue_formula Wp Wq P D.z D.z' D.π D.π' X μ L st l0 hD _ hM2.1
  obtain ⟨A₄, hA₄⟩ := radial_residue_formula Wp Wq P D.z D.z' D.π D.π' X μ L st l0 hD _ hM3.1

  have eL : radIp μ Φ₁ Φ₂ = radIp μ A₁ A₂ := by
    unfold radIp
    refine integral_congr_ae (Eventually.of_forall fun c => ?_)
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    dsimp only
    by_cases hx : (c, Matrix.of g) ∈ DomR P.k P.r D.z D.z'
    · have e2 : (Φ₂ : Fn P.k P.r (Wq →L[ℂ] Wp)) c (Matrix.of g) = (A₂ : Fn P.k P.r (Wq →L[ℂ] Wp)) c (Matrix.of g) := by
        rw [h2 _ hx, hA₂ _ hx]
        exact rdsp_resG_congr _ _ _ (hKeq _ (hEO _ hx))
      refine rdsp_ip_congr e2 fun hne => ?_
      have hxK : (c, Matrix.of g) ∈ Kc := by
        by_contra hxK; exact hne (hKc0 _ hxK)
      rw [h1 _ hx, hA₁ _ hx]
      exact rdsp_resG_congr _ _ _ (hΘJ _ (hEO _ hx) (hCU₂ (Or.inl ⟨_, hxK, rfl⟩)))
    · have z2 : (Φ₂ : Fn P.k P.r (Wq →L[ℂ] Wp)) c (Matrix.of g) = 0 := Φ₂.2.1 (c, Matrix.of g) hx
      have z2' : (A₂ : Fn P.k P.r (Wq →L[ℂ] Wp)) c (Matrix.of g) = 0 := A₂.2.1 (c, Matrix.of g) hx
      exact rdsp_ip_congr (z2.trans z2'.symm) fun hne => absurd z2 hne

  have eR' : radIp μ Φ₃ Φ₄ = radIp μ A₃ A₄ := by
    unfold radIp
    refine integral_congr_ae (Eventually.of_forall fun c => ?_)
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    dsimp only
    by_cases hx : (c, Matrix.of g) ∈ DomR P.k P.r D.z D.z'
    · have e4 : (Φ₄ : Fn P.k P.r (Wq →L[ℂ] Wp)) c (Matrix.of g) = (A₄ : Fn P.k P.r (Wq →L[ℂ] Wp)) c (Matrix.of g) := by
        rw [h4 _ hx, hA₄ _ hx]
        exact rdsp_resG_congr _ _ _ (hΘK _ (hEO _ hx))
      refine rdsp_ip_congr e4 fun hne => ?_
      rw [e4, hA₄ _ hx] at hne
      have hne' := rdsp_resG_ne _ _ hne
      obtain ⟨p, hp, hps⟩ := hM3.2 _ (hEO _ hx) hne'
      have hU : eR P.k P.r (c, Matrix.of g) ∈ U₂ := hU₂sat p hp _ (hEO _ hx) (hCU₂ (Or.inr (hA1t hps)))
      rw [h3 _ hx, hA₃ _ hx]
      exact rdsp_resG_congr _ _ _ ((hF₂J _ (hEO _ hx)).1 hU).symm
    · have z4 : (Φ₄ : Fn P.k P.r (Wq →L[ℂ] Wp)) c (Matrix.of g) = 0 := Φ₄.2.1 (c, Matrix.of g) hx
      have z4' : (A₄ : Fn P.k P.r (Wq →L[ℂ] Wp)) c (Matrix.of g) = 0 := A₄.2.1 (c, Matrix.of g) hx
      exact rdsp_ip_congr (z4.trans z4'.symm) fun hne => absurd z4 hne

  obtain ⟨C1, -, hB⟩ := radial_beta_identity P.k P.r Wp Wq D μ hD.2.1
  have hcc : ∀ (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), B.CkOn ⊤ (B.GV P.k P.r) F → HasCompactSupport F →
      ∀ (A : ℝ) (m : ℕ), B.InCC A m F := fun F hF hFc A m =>
    Formalism.FourierDecayAlt.P.JFxG.cptInCC_G hF hFc (fun g _ hg => image_eq_zero_of_notMem_tsupport hg) A m
  have hβ := Formalism.FourierDecayAlt.P.CompactSupportClassLemmas.compact_support_in_class_general D Θ hΘ.1 hΘ.2.1 F₁ F₂ hF₁s hF₁c (fun g hg _ => hOP (hF₁O hg)) hF₂s hF₂c
    (fun g hg _ => hOP (hF₂O hg))
  rw [eL, eR', hSw P.k P.r D.z D.z' Wp Wq D.π D.π' μ A₁ A₂ 0, hSw P.k P.r D.z D.z' Wp Wq D.π D.π' μ A₃ A₄ 0,
    hB F₁ (B.opAdj Θ F₂) A₂ A₁ (hcc _ hF₁s hF₁c) (hcc _ hB2s hB2c) hA₂ hA₁ 0,
    hB (B.opApply Θ F₁) F₂ A₄ A₃ (hcc _ hA1s hA1c) (hcc _ hF₂s hF₂c) hA₄ hA₃ 0, hβ.2.2.2.2]

end Formalism.FourierDecayAlt.P.CutSE
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSPJFMem
open MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem spectral_pairing_orbital_membership : RDSPJFMem := by
  intro k r Wp Wq _ _ _ _ _ _ D F hF hcs hts
  have hpos : ∀ g ∈ tsupport F, (0 : ℝ) < Gf k r D.z D.z' g := fun g hg => (hts hg).2.2
  obtain ⟨ε, hε, hεle⟩ := hcs.isCompact.exists_forall_le' (PositiveOrbitOpen.gf_cont D.z D.z').continuousOn hpos
  have hnice : NiceAll D F := by
    refine ⟨ε, hε, hF, fun A m => compact_support_finite_class k r _ F (tsupport F) hF hcs.isCompact ?_ A m, ?_⟩
    · intro g hg
      by_contra h
      exact hg (subset_tsupport _ h)
    · intro g _ hg
      exact hεle g (subset_tsupport _ hg)
  refine ⟨(radial_orbital_niceness k r Wp Wq D F hnice).1, ?_⟩
  intro g _ hne
  by_contra hno
  push_neg at hno
  apply hne
  show ∫ p, _ ∂D.μSS = 0
  refine integral_eq_zero_of_ae ?_
  filter_upwards [B5.ae_inSS D] with p hp
  have h0 : F (B.sgs p g) = 0 := by
    by_contra h
    exact hno p hp (subset_tsupport _ h)
  show _ • _ = (0 : Wq →L[ℂ] Wp)
  simp only [B.sgs] at h0
  rw [h0]
  simp

end Formalism.FourierDecayAlt.P.CutSE
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSPOp
open MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Help

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem rdsp_rw_vanish {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (F : B.Mat k r → E) (w : List (B.Mat k r)) :
    ∀ g, g ∉ tsupport F → B.Rw w F g = 0 := by
  intro g hg
  rw [Formalism.FourierDecayAlt.P.JCTx6.Pos.rw_congr_open (isClosed_tsupport F).isOpen_compl (f₁ := F) (f₂ := 0)
    (fun x hx => image_eq_zero_of_notMem_tsupport hx) w g hg, Formalism.FourierDecayAlt.P.CutMP.JA.GA.rw_zero_fn]
  rfl

theorem rdsp_tsupport_sub {E E' : Type*} [Zero E] [Zero E'] {G : B.Mat k r → E} {F : B.Mat k r → E'}
    (h : ∀ g, g ∉ tsupport F → G g = 0) : tsupport G ⊆ tsupport F := by
  apply closure_minimal _ (isClosed_tsupport F)
  intro g hg
  by_contra hc
  exact hg (h g hc)

variable [FiniteDimensional ℂ Wq]

theorem rdsp_opApply_vanishP (Θ : B.DiffOp k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) :
    ∀ g, g ∉ tsupport F → B.opApply Θ F g = 0 := by
  have hz : ∀ x ∈ (tsupport F)ᶜ, F x = 0 := by
    intro x hx
    by_contra hne
    exact hx (subset_tsupport F (Function.mem_support.mpr hne))
  intro g hg
  unfold Formalism.FourierDecayAlt.B.opApply
  have h0 : ∀ T ∈ Θ, T.coef g (B.Rw T.word F g) = 0 := by
    intro T _
    rw [Formalism.FourierDecayAlt.P.Ux8.Rw_vanish (isClosed_tsupport F).isOpen_compl hz T.word g hg, map_zero]
  first
    | (apply List.sum_eq_zero
       intro x hx
       obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hx
       exact h0 T hT)
    | (apply Multiset.sum_eq_zero
       intro x hx
       obtain ⟨T, hT, rfl⟩ := Multiset.mem_map.mp hx
       exact h0 T hT)

theorem rdsp_opAdj_vanishP (Θ : B.DiffOp k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) :
    ∀ g, g ∉ tsupport F → B.opAdj Θ F g = 0 := by
  have hz : ∀ x ∈ (tsupport F)ᶜ, F x = 0 := by
    intro x hx
    by_contra hne
    exact hx (subset_tsupport F (Function.mem_support.mpr hne))
  intro g hg
  unfold Formalism.FourierDecayAlt.B.opAdj
  have h0 : ∀ T ∈ Θ, ((-1 : ℂ) ^ T.word.length) • B.Rw T.word.reverse (fun x => T.coefAdj x (F x)) g = 0 := by
    intro T _
    have hz' : ∀ x ∈ (tsupport F)ᶜ, T.coefAdj x (F x) = 0 := by
      intro x hx
      rw [hz x hx, map_zero]
    rw [Formalism.FourierDecayAlt.P.Ux8.Rw_vanish (isClosed_tsupport F).isOpen_compl hz' T.word.reverse g hg, smul_zero]
  first
    | (apply List.sum_eq_zero
       intro x hx
       obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hx
       exact h0 T hT)
    | (apply Multiset.sum_eq_zero
       intro x hx
       obtain ⟨T, hT, rfl⟩ := Multiset.mem_map.mp hx
       exact h0 T hT)

end Help

theorem spectral_pairing_operator : RDSPOp := by
  intro k r Wp Wq _ _ _ _ _ _ D Θ hS hC F hF hFc hFO
  have hOP : tsupport F ⊆ B.GPos D := fun g hg => ⟨(hFO hg).1, (hFO hg).2.2⟩
  have hsuppF : B.SuppIn (B.GPos D) F :=
    (closure_mono (by exact fun g hg => hg.2)).trans ((closure_minimal subset_closure (isClosed_tsupport F)).trans hOP)
  have hA1t : tsupport (B.opApply Θ F) ⊆ tsupport F := rdsp_tsupport_sub (rdsp_opApply_vanishP Θ F)
  have hB1t : tsupport (B.opAdj Θ F) ⊆ tsupport F := rdsp_tsupport_sub (rdsp_opAdj_vanishP Θ F)
  have hA1s : B.CkOn ⊤ (B.GV k r) (B.opApply Θ F) := by
    refine Formalism.FourierDecayAlt.P.PBJ.ckOn_opApply_list (B.GPos D) F hF hsuppF Θ (fun T hT => (hS T hT).1) fun T _ => ?_
    refine (closure_minimal (fun g hg => ?_) (isClosed_tsupport F)).trans hOP
    by_contra hgF
    exact hg.2 (rdsp_rw_vanish F T.word g hgF)
  have hB1s : B.CkOn ⊤ (B.GV k r) (B.opAdj Θ F) := Formalism.FourierDecayAlt.P.CutMP.JA.FFS.AC.ckOn_opAdj D Θ hS hF hsuppF
  refine ⟨⟨hA1s, hFc.of_isClosed_subset (isClosed_tsupport _) hA1t, hA1t⟩,
    ⟨hB1s, hFc.of_isClosed_subset (isClosed_tsupport _) hB1t, hB1t⟩, ?_⟩

  have hpos : ∃ ε : ℝ, 0 < ε ∧ ∀ g ∈ tsupport F, ε ≤ Formalism.QuantumDeterminants.Gf k r D.z D.z' g := by
    rcases (tsupport F).eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    · obtain ⟨g₀, hg₀, hmin⟩ := hFc.exists_isMinOn h (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.gf_cont D.z D.z').continuousOn
      exact ⟨_, (hFO hg₀).2.2, fun g hg => isMinOn_iff.mp hmin g hg⟩
  obtain ⟨ε, hε, hεG⟩ := hpos
  have hCk : B.CkOn ⊤ (JF.Om k r D.z D.z') (B.JF D F) :=
    (radial_orbital_niceness k r Wp Wq D F ⟨ε, hε, hF, fun A m => Formalism.FourierDecayAlt.P.JFxG.cptInCC_G hF hFc
      (fun g _ hg => image_eq_zero_of_notMem_tsupport hg) A m,
      fun g _ hg => hεG g (subset_tsupport F hg)⟩).2
  have hIn := Formalism.FourierDecayAlt.P.JFxG.cptInCC_G hF hFc (fun g _ hg => image_eq_zero_of_notMem_tsupport hg)
    (6 * (r : ℝ) * (B.opOrder Θ : ℝ) + (r : ℝ) * (4 * (r : ℝ) + 2 * (k : ℝ)) * (6 * (r : ℝ) + 1) + 1) (B.opOrder Θ)
  obtain ⟨hT1, hT2⟩ := Formalism.FourierDecayAlt.P.CutMP.JA.LT.thetaJ_of_adjComm Formalism.FourierDecayAlt.P.CutMP.JA.FFS.adjoint_commutation_holds k r Wp Wq D Θ _ F
    (JF.Om k r D.z D.z') (Formalism.FourierDecayAlt.P.CutMP.JA.SA.thrW_sa k r (B.opOrder Θ)) hS hC hF hIn subset_rfl
    (Formalism.FourierDecayAlt.P.B5.ckOn_mono le_top hCk)
  exact fun g hg => ⟨hT1 g hg, hT2 g hg⟩

end Formalism.FourierDecayAlt.P.CutSE
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSPExh
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLSAExh
namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

theorem average_one_cutoff_on_orbits : Formalism.FourierDecayAlt.P.JFxI.AvgCutoff := avgCutoff_of_smooth averaging_smoothness_holds

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
end

open MeasureTheory Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem spectral_pairing_exhaustion : RDSPExh := by
  intro k r Wp Wq _ _ _ _ _ _ D X hX C hC hCO
  have hX' : X ∈ Q.FFl k r D.z D.z' D.π D.π' 0 (Q.OmPlus k r D.z D.z') := by
    rwa [rdb_ffl_om_eq] at hX
  have hqC : IsCompact (Formalism.FourierDecayAlt.P.CutMP.JA.SA.QO.qOf D.z D.z' '' C) :=
    hC.image_of_continuousOn ((Formalism.FourierDecayAlt.P.CutMP.JA.SA.QO.qOf_contOn D.z D.z').mono fun g hg => (hCO hg).2)
  have hqQ : Formalism.FourierDecayAlt.P.CutMP.JA.SA.QO.qOf D.z D.z' '' C ⊆ JF.QDom k r D.z D.z' := by
    rintro _ ⟨g, hg, rfl⟩
    exact (Formalism.FourierDecayAlt.P.CutMP.JA.SA.QO.om_eq_sgs D (hCO hg)).choose_spec.2.1
  obtain ⟨K', hK'c, hCK', hK'Q⟩ := exists_compact_between hqC (Formalism.FourierDecayAlt.P.BigCellOpenDomain.qdom_open D.z D.z') hqQ
  obtain ⟨φ, hφ, ⟨C', hC'c, hC'O, hC'φ⟩, hint⟩ :=
    Formalism.FourierDecayAlt.P.CutMP.JA.SA.average_one_cutoff_on_orbits k r Wp Wq D K' hK'c hK'Q
  have hsuppC : tsupport (fun g => φ g • X g) ⊆ C' := by
    refine closure_minimal (fun g hg => ?_) hC'c.isClosed
    by_contra hgC
    exact hg (by simp [hC'φ g hgC])
  refine ⟨fun g => φ g • X g,
    Q.OmPlus k r D.z D.z' ∩ Formalism.FourierDecayAlt.P.CutMP.JA.SA.QO.qOf D.z D.z' ⁻¹' interior K', ?_, ?_, ?_,
    Formalism.FourierDecayAlt.P.CutMP.JA.SA.QO.isOpen_qOf D.z D.z' isOpen_interior, ?_, ?_, ?_⟩
  · intro g₀ hg₀
    by_cases hO : g₀ ∈ Q.OmPlus k r D.z D.z'
    · obtain ⟨U₁, φ', hU₁, hg₁, hφ', hφe⟩ := hφ g₀ hg₀
      obtain ⟨U₂, f', hU₂, hg₂, hf', hfe⟩ := hX'.1 g₀ ⟨(Formalism.FourierDecayAlt.P.CapelliUnderIntegral.glev0 g₀).2 hg₀, hO⟩
      refine ⟨U₁ ∩ U₂, fun g => φ' g • f' g, hU₁.inter hU₂, ⟨hg₁, hg₂⟩, ?_, ?_⟩
      · exact (hφ'.mono Set.inter_subset_left).smul (hf'.mono Set.inter_subset_right)
      · intro g hg hgG
        simp only [hφe g hg.1 hgG, hfe g hg.2 ((Formalism.FourierDecayAlt.P.CapelliUnderIntegral.glev0 g).2 hgG)]
    · refine ⟨C'ᶜ, fun _ => 0, hC'c.isClosed.isOpen_compl, fun h => hO (hC'O h).2, contDiffOn_const, ?_⟩
      intro g hg _
      simp [hC'φ g hg]
  · exact hC'c.of_isClosed_subset (isClosed_tsupport _) hsuppC
  · exact hsuppC.trans hC'O
  · intro g hg
    exact ⟨(hCO hg).2, hCK' ⟨g, hg, rfl⟩⟩
  · intro p hp g hg hs
    refine ⟨hg.2, ?_⟩
    have h2 := hs.2
    simp only [Set.mem_preimage] at h2 ⊢
    rwa [Formalism.FourierDecayAlt.P.CutMP.JA.SA.QO.qOf_sgs D hp] at h2
  · intro g hg
    have hJ : B.JF D (fun g => φ g • X g) g = (∫ p, φ (B.sgs p g) ∂D.μSS) • X g := by
      change ∫ p, JF.xiP D p • B.rho D p (fun g => φ g • X g) g ∂D.μSS = _
      rw [← integral_smul_const]
      apply integral_congr_ae
      filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS D] with p hp
      have hr : B.rho D p (fun g => φ g • X g) g = φ (B.sgs p g) • B.rho D p X g := by
        unfold B.rho
        rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
      rw [hr, smul_comm, Formalism.FourierDecayAlt.P.CutMP.JA.SA.eqv_of_FFl D X hX' hp hg]
    refine ⟨fun hgU => ?_, fun h0 => by rw [hJ, h0, smul_zero]⟩
    obtain ⟨p₀, hp₀, -, hge⟩ := Formalism.FourierDecayAlt.P.CutMP.JA.SA.QO.om_eq_sgs D hg
    have h1 := hint p₀ hp₀ _ (interior_subset hgU.2)
    rw [← hge] at h1
    rw [hJ, h1, one_smul]

end Formalism.FourierDecayAlt.P.CutSE
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSPZeroR
open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem spectral_pairing_zero_right : RDSPZeroR := by
  intro k r Wp Wq _ _ _ _ _ _ D X Y hX hY hxy g hg
  obtain ⟨p, hp, hq, hge⟩ := Formalism.FourierDecayAlt.P.CutMP.JA.SA.QO.om_eq_sgs D hg
  set q := Formalism.FourierDecayAlt.P.CutMP.JA.SA.QO.qOf D.z D.z' g with hqdef
  have hgq := Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom D hq
  obtain ⟨x, hxD, w, hw, hres⟩ := radial_group_residue k r Wp Wq D q hq
  have hxe : X (B.gq D q) = Y (B.gq D q) := by
    have e := rdsp_resG_congr X Y x (hxy x hxD)
    rw [hres X hX, hres Y hY] at e
    exact smul_right_injective _ hw e
  have hD : ∀ y ∈ JF.Om k r D.z D.z', y ∈ Q.Glev k r 0 ∩ JF.Om k r D.z D.z' := fun y hy =>
    ⟨Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hy.1, hy⟩
  have hNl : ∀ n ∈ Formalism.QuantumDeterminants.Nset k r, n ∈ Q.Nlev k r 0 := fun n hn => ⟨hn, Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hn.1⟩
  rw [hge]
  exact Formalism.FourierDecayAlt.P.CutMP.JA.LT.agree_sgs D X Y
    (fun y hy n hn => hX.2.1 y (hD y hy) n (hNl n hn))
    (fun y hy n hn => hX.2.2.1 y (hD y hy) n (hNl n hn))
    (fun y hy h hh h' hh' => hX.2.2.2 y (hD y hy) h hh h' hh')
    (fun y hy n hn => hY.2.1 y (hD y hy) n (hNl n hn))
    (fun y hy n hn => hY.2.2.1 y (hD y hy) n (hNl n hn))
    (fun y hy h hh h' hh' => hY.2.2.2 y (hD y hy) h hh h' hh')
    hp hgq hxe

end Formalism.FourierDecayAlt.P.CutSE
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSPLoc
namespace Formalism.FourierDecayAlt.P.CutSE

theorem spectral_pairing_locality : RDSPLoc := by
  intro k r Wp Wq _ _ _ _ _ _ Θ U X Y hU hXY g hgU hgV
  have h : ∀ x ∈ B.GV k r, x ∈ U → X x = Y x := fun x hx hxU => hXY x hxU hx
  exact ⟨Formalism.FourierDecayAlt.P.MinorPolynomials.opApply_congr Θ hU h hgV hgU,
    Formalism.FourierDecayAlt.P.CutMP.JA.LocOp.opAdj_congr_GV Θ hU h g hgV hgU⟩

end Formalism.FourierDecayAlt.P.CutSE
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSPIpSwap
open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

theorem spectral_pairing_inner_swap : RDSPIpSwap := by
  intro k r z z' Wp Wq _ _ _ _ _ _ π π' μ Φ Ψ c
  have hmp := volume_measurePreserving_piCongrLeft (fun _ : Fin r => ℂ)
    (Equiv.subtypeUnivEquiv (p := fun l : Fin r => ((0 : Fin (r + 1)) : ℕ) ≤ l) (fun l => Nat.zero_le _))
  set e := MeasurableEquiv.piCongrLeft (fun _ : Fin r => ℂ)
    (Equiv.subtypeUnivEquiv (p := fun l : Fin r => ((0 : Fin (r + 1)) : ℕ) ≤ l) (fun l => Nat.zero_le _)) with he
  have happ : ∀ (c' : Cf r 0) (l : {l : Fin r // ((0 : Fin (r + 1)) : ℕ) ≤ l}), e c' l.1 = c' l := by
    intro c' l
    rw [he]
    exact MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin r => ℂ)
      (Equiv.subtypeUnivEquiv (p := fun l : Fin r => ((0 : Fin (r + 1)) : ℕ) ≤ l) (fun l => Nat.zero_le _)) c' l
  have hglue : ∀ c' : Cf r 0, glue 0 c c' = e c' := fun c' => funext fun l => by
    simp only [glue]
    rw [dite_eq_left (show ((0 : Fin (r + 1)) : ℕ) ≤ (l : ℕ) from Nat.zero_le _)]
    exact (happ c' ⟨l, Nat.zero_le _⟩).symm
  have hprod : ∀ c' : Cf r 0,
      (∏ l : {l : Fin r // ((0 : Fin (r + 1)) : ℕ) ≤ l}, ‖c' l‖ ^ (-2 : ℤ)) = ∏ l : Fin r, (‖e c' l‖ ^ 2)⁻¹ := by
    intro c'
    refine Fintype.prod_equiv (Equiv.subtypeUnivEquiv (fun l => Nat.zero_le _)) _ _ (fun l => ?_)
    show ‖c' l‖ ^ (-2 : ℤ) = (‖e c' l.1‖ ^ 2)⁻¹
    rw [happ c' l, zpow_neg]
    norm_cast
  unfold radIp LocFacts₂ pairAt dxc
  simp only [B.hsInner]
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  rw [← hmp.integral_comp']
  refine integral_congr_ae (ae_of_all _ fun c' => ?_)
  simp only
  rw [hglue c', ENNReal.toReal_ofReal (Finset.prod_nonneg fun _ _ => by positivity), Complex.real_smul, hprod c']

end Formalism.FourierDecayAlt.P.CutSE
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSPEOm
noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

private theorem continuousAt_w1_of_ne_zero (k r : ℕ) (l : Fin r) {c : ℂ} (hc : c ≠ 0) :
    ContinuousAt (w1 k r l) c := by
  refine continuousAt_pi.2 fun p => continuousAt_pi.2 fun q => ?_
  show ContinuousAt (fun c => w1 k r l c p q) c
  simp only [w1]
  split_ifs
  · exact continuousAt_id
  · exact (continuous_star.continuousAt).inv₀ (star_ne_zero.mpr hc)
  · exact continuousAt_const
  · exact continuousAt_const
private theorem continuousAt_wCell_fst_of_mem_OmX (k r : ℕ) (x : (Fin r → ℂ) × Mx k r) (hx : x.1 ∈ OmX r)
    (i : Fin (r + 1)) : ContinuousAt (fun y : (Fin r → ℂ) × Mx k r => wCell k r i y.1) x := by
  induction i using Fin.induction with
  | zero =>
    simp only [Formalism.FourierDecayAlt.P.Qx6.wCell_zero]
    exact continuousAt_const
  | succ l ih =>
    simp only [Formalism.FourierDecayAlt.P.Qx6.wCell_succ]
    refine ih.mul ?_
    have hf : ContinuousAt (fun y : (Fin r → ℂ) × Mx k r => y.1 l) x := by fun_prop
    exact (continuousAt_w1_of_ne_zero k r l (hx l)).comp (f := fun y : (Fin r → ℂ) × Mx k r => y.1 l) hf

theorem spectral_pairing_big_cell : RDSPEOm := by
  intro k r Wp Wq _ _ _ _ _ _ D
  have hmem : ∀ x ∈ DomR k r D.z D.z', eR k r x ∈ JF.Om k r D.z D.z' := by
    intro x hx
    refine ⟨?_, ?_⟩
    · exact Formalism.FourierDecayAlt.P.TLB.wCell_gv (Pa := M.Par.mk k r 0 0 0 0) D hx
    · exact Formalism.FourierDecayAlt.P5.Rad.wCell_mem_omPlus D.z_mem D.z'_mem hx.1 hx.2.1 hx.2.2
  refine ⟨hmem, ?_, ?_⟩
  · intro x hx
    refine ContinuousAt.continuousWithinAt ?_
    exact (continuousAt_wCell_fst_of_mem_OmX k r x hx.1 (Fin.last r)).mul continuous_snd.continuousAt
  · intro g hg
    exact ⟨hg.1, hg.2.2⟩

end Formalism.FourierDecayAlt.P.CutSE
end
end

namespace Formalism.FourierDecayAlt.P.CutSE

theorem spectral_pairing_identity : RDSPair :=
  rDSPair_of_cut spectral_pairing_inner_swap spectral_pairing_big_cell spectral_pairing_zero_right spectral_pairing_exhaustion spectral_pairing_orbital_membership spectral_pairing_operator
    spectral_pairing_locality

end Formalism.FourierDecayAlt.P.CutSE
