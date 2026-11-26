module

public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TopDensityCutoffDominatedOfHCXi
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WignerMapsThreePlacesExists
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.GridsAtPlaceLongCutNormaliserPositive
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliEigenfunctionBoundThreePlaces

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ShiftExists
open Matrix Finset

noncomputable section

namespace GlobalTheory.WigSh

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.CutBP2

def ShiftExists : Prop :=
  ∃ c₃ Cb : ℝ, 0 ≤ Cb ∧ ∀ (P : M.Par) (Wp Wq : Type)
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (l n₀ lp lm : ℕ) (b : ℝ),
    (∀ i ∈ Finset.Icc 1 P.k, P.u i = P.u' i) →
    1 ≤ l → l < P.k → 2 * (n₀ : ℝ) + 1 ≤ P.u' l - P.u' (l + 1) →
    (∀ i ∈ Finset.Icc 1 P.k, |P.u' i| ≤ b) → (n₀ : ℝ) ≤ b → 1 ≤ b →
    1 ≤ lp → lp ≤ P.k → 1 ≤ lm → lm ≤ P.k →
    ∃ (Wqp : Type) (_ : NormedAddCommGroup Wqp) (_ : InnerProductSpace ℂ Wqp) (_ : FiniteDimensional ℂ Wqp)
      (Wqm : Type) (_ : NormedAddCommGroup Wqm) (_ : InnerProductSpace ℂ Wqm) (_ : FiniteDimensional ℂ Wqm)
      (pp : KB.Pl (shP P P.u (Function.update P.u' (l + 1) (P.u' (l + 1) + (n₀ : ℝ)))) Wp Wqp)
      (pm : KB.Pl (shP P P.u (Function.update P.u' l (P.u' l - (n₀ : ℝ)))) Wp Wqm)
      (Ap : B.Mat P.k P.r → (Wqp →L[ℂ] Wq)) (Am : B.Mat P.k P.r → (Wqm →L[ℂ] Wq))
      (ApPt : C.LPt → (Wqp →L[ℂ] Wq)) (AmPt : C.LPt → (Wqm →L[ℂ] Wq)),
      pp.l0 = lp ∧ pm.l0 = lm ∧
      pp.T.base.z = p.T.base.z ∧ pp.T.base.z' = p.T.base.z' ∧ pp.T.base.π = p.T.base.π ∧
      pm.T.base.z = p.T.base.z ∧ pm.T.base.z' = p.T.base.z' ∧ pm.T.base.π = p.T.base.π ∧
      KB.InDDplus2 (shP P P.u (Function.update P.u' (l + 1) (P.u' (l + 1) + (n₀ : ℝ)))) pp.l0 pp.T.base Cb pp.Θ ∧
      KB.InDDplus2 (shP P P.u (Function.update P.u' l (P.u' l - (n₀ : ℝ)))) pm.l0 pm.T.base Cb pm.Θ ∧
      (∃ (t : ℕ) (c : Fin t → B.Mat P.k P.r → ℂ) (L : Fin t → (Wqp →L[ℂ] Wq)),
        (∀ i, U.IsPolyDeg (n₀ * (P.r + 1)) (c i)) ∧ ∀ g, Ap g = ∑ i, c i g • L i) ∧
      (∃ (t : ℕ) (c : Fin t → B.Mat P.k P.r → ℂ) (L : Fin t → (Wqm →L[ℂ] Wq)),
        (∀ i, U.IsPolyDeg (n₀ * (P.r + 1)) (c i)) ∧ ∀ g, Am g = ∑ i, c i g • L i) ∧
      (∀ γ, D.IsLocPt γ (P.r + 1) → 0 < TBB.Gp p γ → ∀ g ∈ B.GV P.k P.r,
        Zhat P.k P.r p.T.base.z p.T.base.z' g = D.ptMatN γ (P.r + 1) → D.IsDFrame p.T.base p.ν' p.m₀ g →
        ApPt γ = Ap g ∧ AmPt γ = Am g) ∧
      ∀ (A₀ : ℝ) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)),
        c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤ A₀ → B.InCC A₀ 1 f →
        AmapsSh p pp pm f Ap Am ApPt AmPt b n₀

end GlobalTheory.WigSh
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WithRightAction
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace GlobalTheory.WithRightAction

noncomputable def withRight {k r : ℕ} {Wp Wq Wq' : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq']
    (Bs : B.RealPlaceData k r Wp Wq) (π'' : B.Mat k r → (Wq' →L[ℂ] Wq')) (u' : ℕ → ℝ)
    (h : Q.IsType k r Bs.z' π'' u') : B.RealPlaceData k r Wp Wq' :=
  { z := Bs.z, z' := Bs.z', π := Bs.π, π' := π'', μG := Bs.μG, μW := Bs.μW, μN := Bs.μN, μW' := Bs.μW',
    μsec := Bs.μsec, χ := Bs.χ, k_pos := Bs.k_pos, z_mem := Bs.z_mem, z'_mem := Bs.z'_mem, T_pos := Bs.T_pos,
    T'_pos := Bs.T'_pos, π_rep := Bs.π_rep, π'_rep := h.2.1, π_unitary := Bs.π_unitary, π'_unitary := h.2.2.2.1,
    π_cont := Bs.π_cont, π'_cont := h.2.2.1, haarG := Bs.haarG, haarW := Bs.haarW, haarN := Bs.haarN,
    haarW' := Bs.haarW', sec := Bs.sec, χ_smooth := Bs.χ_smooth, χ_supp := Bs.χ_supp, χ_int := Bs.χ_int }

theorem exists_place_other_right_type : ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ (P : M.Par) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (Wq' : Type) [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq'] (p : KB.Pl P Wp Wq) (u u' : ℕ → ℝ) (π'' : B.Mat P.k P.r → (Wq' →L[ℂ] Wq')) (l0 : ℕ), Q.IsPlace (⟨P.k, P.r, P.T, P.T', u, u'⟩ : M.Par) p.T.base.z p.T.base.z' p.T.base.π π'' → 1 ≤ l0 → l0 ≤ P.k → ∃ q : KB.Pl (⟨P.k, P.r, P.T, P.T', u, u'⟩ : M.Par) Wp Wq', q.l0 = l0 ∧ q.T.base.z = p.T.base.z ∧ q.T.base.z' = p.T.base.z' ∧ q.T.base.π = p.T.base.π ∧ q.T.base.π' = π'' ∧ q.ν' = p.ν' ∧ q.m₀ = p.m₀ ∧ KB.InDDplus2 (⟨P.k, P.r, P.T, P.T', u, u'⟩ : M.Par) q.l0 q.T.base Cb q.Θ := by
  obtain ⟨Cb, hCb, hTL⟩ := Formalism.FourierDecayAlt.P.top_lift_exists
  refine ⟨Cb, hCb, ?_⟩
  intro P Wp _ _ _ Wq _ _ _ Wq' _ _ _ p u u' π'' l0 hPl hl1 hl2
  obtain ⟨T, h1, h2, h3, h4, hN⟩ := Formalism.FourierDecayAlt.P.exists_normalized_tower P.k P.r Wp Wq'
    (withRight p.T.base π'' u' hPl.2.2.2.2.2.2)
  change T.base.z = p.T.base.z at h1
  change T.base.z' = p.T.base.z' at h2
  change T.base.π = p.T.base.π at h3
  change T.base.π' = π'' at h4
  have hPT : Q.IsPlace (⟨P.k, P.r, P.T, P.T', u, u'⟩ : M.Par) T.base.z T.base.z' T.base.π T.base.π' := by
    rw [h1, h2, h3, h4]; exact hPl
  have hF : D.IsBaseFrame T.base p.ν' p.m₀ := by
    have := p.hF
    unfold D.IsBaseFrame at this ⊢
    rw [h1, h2]; exact this
  obtain ⟨-, μ, -, -, ⟨-, hμ, -⟩, -⟩ := p.hΘ
  obtain ⟨X⟩ := Formalism.FourierDecayAlt.P.actual_operators_exist _ _ _ _ _ _ _ hPT
  obtain ⟨L, st, g1, g2, g3, g4, g5, g6⟩ := Formalism.FourierDecayAlt.P.level_start_actual _ _ _ _ _ _ _ hPT X l0
  have hD : P5.IsData (⟨P.k, P.r, P.T, P.T', u, u'⟩ : M.Par) T.base.z T.base.z' T.base.π T.base.π' X μ L st l0 :=
    ⟨hPT, hμ, g1, g2, g3, g4, g5, g6⟩
  obtain ⟨f1, f2, f3⟩ := Formalism.FourierDecayAlt.P.HaarMassHermitianCurvature.frameVec_facts T.base p.ν' p.m₀ hF
  obtain ⟨Θ, hI, hC⟩ := hTL Wp Wq' (⟨P.k, P.r, P.T, P.T', u, u'⟩ : M.Par) T.base X μ L st l0 hl1 hl2 hD
  obtain ⟨TP⟩ := Formalism.FourierDecayAlt.P.type_projectors_exist Wp Wq' (⟨P.k, P.r, P.T, P.T', u, u'⟩ : M.Par)
    T.base.z T.base.z' T.base.π T.base.π' (p.m₀.mulVec p.ν') hPT f1 f2 f3
  exact ⟨⟨l0, T, p.ν', p.m₀, Θ, TP, ⟨hl1, hl2, p.hl.2.2⟩, hN, hF, hPT, ⟨X, μ, L, st, hD, hI⟩⟩,
    rfl, h1, h2, h3, h4, rfl, rfl, hC⟩

end GlobalTheory.WithRightAction
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliEigenfunctionPointwiseBoundOfDifferentTyp
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliEigenfunctionPointwiseBoundOfDifferentTyp
open BpJoin Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Formalism.QuantumDeterminants

namespace GlobalTheory.capelliEigenfunction_pointwiseBound_of_differentTypes

theorem decay_le (c₃ Cc r n N A e : ℝ) (hc : c₃ ≤ Cc) (h0 : 0 ≤ Cc) (hr : 0 ≤ r) (hn : r + 1 ≤ n) (hN : 0 ≤ N)
    (he : 0 ≤ e) (h : Cc * (r + 1) ^ 4 * (N * n ^ 2 + n ^ 3) ≤ A - e) :
    c₃ * (r + 1) ^ 2 * (r * n + 1) ≤ A := by
  have h1 : (1 : ℝ) ≤ r + 1 := by linarith
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have h2 : (r + 1) ^ 2 ≤ (r + 1) ^ 4 := pow_le_pow_right₀ h1 (by norm_num)
  have h3 : r * n + 1 ≤ N * n ^ 2 + n ^ 3 := by
    have a1 : r * n + 1 ≤ n ^ 2 := by nlinarith
    have a2 : n ^ 2 ≤ n ^ 3 := pow_le_pow_right₀ hn1 (by norm_num)
    have a3 : 0 ≤ N * n ^ 2 := by positivity
    linarith
  have h4 : 0 ≤ r * n + 1 := by positivity
  calc c₃ * (r + 1) ^ 2 * (r * n + 1) ≤ Cc * (r + 1) ^ 2 * (r * n + 1) := by gcongr
    _ ≤ Cc * (r + 1) ^ 4 * (N * n ^ 2 + n ^ 3) := by gcongr
    _ ≤ A := by linarith

theorem thmBp_eigen_different_types : GlobalTheory.HCXi.BesselXiIntegrable → P5.ThmPActualCpt → NFTopDomAll → ∀ C C₃ C₀ : ℝ, 0 ≤ C → 0 ≤ C₃ → 0 ≤ C₀ → ∃ C₄ Cc : ℝ, ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b c A₀ : ℝ) (n₀ p₀ : ℕ) (lam lam' : Fin (2 * P.r + P.k + 1) → ℝ), StdNum C b c P lam → (n₀ = 0 ∧ ∃ l ∈ Finset.Icc 1 P.k, ((30 * (P.r + 1) ^ 2 + 6 : ℕ) : ℝ) ≤ |P.u l - P.u' l|) → 3 * (P.r + 1) ≤ 2 * p₀ → (p₀ : ℝ) ≤ C₀ * ((P.r : ℝ) + 1) ^ 2 → EigDec f A₀ lam' → Cc * ((P.r : ℝ) + 1) ^ 4 * (((3 * (P.r + 1) : ℕ) : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A₀ - (((2 * P.r + 2) * p₀ + n₀ * (P.r + 1) : ℕ) : ℝ) → (∀ s, |lam' s - lam s| + (((2 * P.r + 2) * p₀ + n₀ * (P.r + 1) : ℕ) : ℝ) ≤ c - 1) → TBB.RegularityBoundBigCell p f b C₃ (2 * p₀ + n₀) → TBB.ThmBpAt p f b C₄ n₀ p₀ := by
  intro hX hP5 hNF C C₃ C₀ hC hC₃ hC₀
  obtain ⟨Cb, -, hsh⟩ := GlobalTheory.WithRightAction.exists_place_other_right_type
  obtain ⟨c₃, hA⟩ := GlobalTheory.WigSh.amapsShExists
  obtain ⟨C₄, Cc, hreg⟩ := GlobalTheory.T.capelli_eigenfunction_bound_three_places hX hP5 hNF Cb C₃ (7 + C) C₀ hC₃ (by linarith) hC₀
  refine ⟨C₄, max (max Cc c₃) 0, ?_⟩
  intro P Wp Wq _ _ _ _ _ _ p f b c A₀ n₀ p₀ lam lam' hS hcase hN hp₀ hE hdec hlam h92
  obtain ⟨rfl, l, hl, hgap⟩ := hcase
  have hl' := Finset.mem_Icc.1 hl
  obtain ⟨q, hq0, hz, hz', hπ, hπ', hν, hm, hD⟩ :=
    hsh P Wp Wq Wq p P.u P.u' p.T.base.π' l p.hP hl'.1 hl'.2
  have hG := hS.1 l hl
  have hc1 : 1 ≤ c := hG.1
  have hcb : c + 2 ≤ b := hG.2.1
  have hk : 2 ≤ P.k := p.hl.2.2
  have hposition : 2 * ((0 : ℕ) : ℝ) + 1 ≤ P.u' 1 - P.u' (1 + 1) := by
    have hg := p.hP.1.gap 1 (Finset.mem_Icc.2 ⟨le_rfl, by omega⟩)
    unfold M.Par.lo M.Par.hi at hg
    have a1 := le_max_right (P.u (1 + 1)) (P.u' (1 + 1))
    have a2 := min_le_right (P.u 1) (P.u' 1)
    push_cast
    linarith
  obtain ⟨Ap, Am, ApPt, AmPt, hAp, hAm, -, hmaps⟩ :=
    hA P Wp Wq Wq Wq P.u P.u' P.u P.u' p q q 1 0 b hz hz' hz hz' (fun h _ => congrFun hπ h) (fun h _ => congrFun hπ h)
      hν hm hν hm le_rfl (by omega) hposition (fun i hi => (hS.1 i hi).2.2.2.2.1) (by push_cast; linarith) (by linarith)
      (fun i _ => by simp) (fun i _ => by simp)
  have hr0 : (0 : ℝ) ≤ P.r := Nat.cast_nonneg _
  have hk0 : (0 : ℝ) ≤ P.k := Nat.cast_nonneg _
  have hm1 := hmaps A₀ f (by
    have := decay_le c₃ _ P.r (2 * (P.r : ℝ) + P.k + 1) _ A₀ _ ((le_max_right Cc c₃).trans (le_max_left _ 0))
      (le_max_right _ _) hr0 (by linarith) (Nat.cast_nonneg _) (Nat.cast_nonneg _) hdec
    push_cast
    exact this) (hE.2.1 1)
  obtain ⟨hpos, hone, Y, hW, hL⟩ := GlobalTheory.T.grids_at_place_longCut_normaliserPositive C b c (shP P P.u P.u') Wp Wq q lam hC
    (by subst hq0; exact hG) (by subst hq0; exact hgap)
  refine hreg P Wp Wq Wq Wq P.u P.u' P.u P.u' p q q f Ap Am ApPt AmPt b
    (b ^ ((7 + C) * ((2 * P.r + 2 : ℕ) : ℝ))) A₀ 0 p₀ (0 * (P.r + 1)) (Pst lam c) (Pst lam c) Y Y 3 (3 * (P.r + 1))
    (by linarith) hone le_rfl (Nat.zero_le _) hp₀ hz hz' hz hz' le_rfl (by omega) hpos hpos hD hD hE.1 hE.2.1
    hAp hAm ?_ hm1 h92 hW hL hW hL hN lam lam' c hE.2.2 ?_ hlam (fun y => le_rfl) (fun y => le_rfl)
  · have hle : Cc ≤ max (max Cc c₃) 0 := (le_max_left Cc c₃).trans (le_max_left _ 0)
    refine le_trans ?_ (hdec.trans (le_of_eq ?_))
    · gcongr
    · push_cast; ring
  · intro s t hst
    have hd := hG.2.2.2.2.2.2.1
    rcases lt_or_gt_of_ne hst with h | h
    · have := hd s t h
      exact le_trans (by linarith) (le_abs_self _)
    · have := hd t s h
      exact le_trans (by linarith) (neg_le_abs _)

end GlobalTheory.capelliEigenfunction_pointwiseBound_of_differentTypes
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliEigenfunctionPointwiseBoundOfDifferentTypStatement
open BpJoin Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Formalism.QuantumDeterminants
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.capelliEigenfunction_pointwiseBound_of_differentTypes : GlobalTheory.HCXi.BesselXiIntegrable → P5.ThmPActualCpt → NFTopDomAll → ∀ C C₃ C₀ : ℝ, 0 ≤ C → 0 ≤ C₃ → 0 ≤ C₀ → ∃ C₄ Cc : ℝ, ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b c A₀ : ℝ) (n₀ p₀ : ℕ) (lam lam' : Fin (2 * P.r + P.k + 1) → ℝ), StdNum C b c P lam → (n₀ = 0 ∧ ∃ l ∈ Finset.Icc 1 P.k, ((30 * (P.r + 1) ^ 2 + 6 : ℕ) : ℝ) ≤ |P.u l - P.u' l|) → 3 * (P.r + 1) ≤ 2 * p₀ → (p₀ : ℝ) ≤ C₀ * ((P.r : ℝ) + 1) ^ 2 → EigDec f A₀ lam' → Cc * ((P.r : ℝ) + 1) ^ 4 * (((3 * (P.r + 1) : ℕ) : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A₀ - (((2 * P.r + 2) * p₀ + n₀ * (P.r + 1) : ℕ) : ℝ) → (∀ s, |lam' s - lam s| + (((2 * P.r + 2) * p₀ + n₀ * (P.r + 1) : ℕ) : ℝ) ≤ c - 1) → TBB.RegularityBoundBigCell p f b C₃ (2 * p₀ + n₀) → TBB.ThmBpAt p f b C₄ n₀ p₀ := by
  first | exact @GlobalTheory.capelliEigenfunction_pointwiseBound_of_differentTypes.thmBp_eigen_different_types | exact GlobalTheory.capelliEigenfunction_pointwiseBound_of_differentTypes.thmBp_eigen_different_types | (intros; apply GlobalTheory.capelliEigenfunction_pointwiseBound_of_differentTypes.thmBp_eigen_different_types <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliEigenfunctionPointwiseBoundOfEqualTypes
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WignerShiftedPlacesExistProof
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WignerShiftedPlacesExistProof
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.CutBP2

namespace GlobalTheory.wignerShiftedPlacesExist_proof

theorem gap_one {P : M.Par} (h : P.OK) (i : ℕ) (hi : i ∈ Finset.Icc 1 (P.k - 1)) :
    P.u' (i + 1) + 1 ≤ P.u' i := by
  have hg := h.gap i hi
  unfold M.Par.lo M.Par.hi at hg
  have h1 := le_max_right (P.u (i + 1)) (P.u' (i + 1))
  have h2 := min_le_right (P.u i) (P.u' i)
  linarith

theorem gap_nat {P : M.Par} (h : P.OK) (i : ℕ) (hi : i ∈ Finset.Icc 1 (P.k - 1)) :
    ∃ N : ℕ, P.u' i - P.u' (i + 1) = (N : ℝ) + 1 := by
  have h1 := gap_one h i hi
  rw [Finset.mem_Icc] at hi
  obtain ⟨a, ha⟩ := h.int_u' i (Finset.mem_Icc.2 ⟨hi.1, by omega⟩)
  obtain ⟨c, hc⟩ := h.int_u' (i + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
  have h2 : ((0 : ℤ) : ℝ) ≤ ((a - c - 1 : ℤ) : ℝ) := by push_cast; linarith
  have h3 : (0 : ℤ) ≤ a - c - 1 := by exact_mod_cast h2
  refine ⟨(a - c - 1).toNat, ?_⟩
  have h4 : (((a - c - 1).toNat : ℤ) : ℝ) = ((a - c - 1 : ℤ) : ℝ) := by rw [Int.toNat_of_nonneg h3]
  push_cast at h4
  linarith

theorem ok_plus {P : M.Par} (h : P.OK) (l n₀ : ℕ) (he : ∀ i ∈ Finset.Icc 1 P.k, P.u i = P.u' i)
    (hg : 2 * (n₀ : ℝ) + 1 ≤ P.u' l - P.u' (l + 1)) :
    (shP P P.u (Function.update P.u' (l + 1) (P.u' (l + 1) + (n₀ : ℝ)))).OK := by
  have hn : (0 : ℝ) ≤ n₀ := Nat.cast_nonneg _
  refine ⟨h.k_pos, h.T_pos, h.T'_pos, h.int_u, ?_, ?_⟩
  · intro i hi
    obtain ⟨a, ha⟩ := h.int_u' i hi
    change ∃ n : ℤ, Function.update P.u' (l + 1) (P.u' (l + 1) + (n₀ : ℝ)) i - P.u 1 = n
    by_cases hil : i = l + 1
    · subst hil
      refine ⟨a + n₀, ?_⟩
      rw [Function.update_self]; push_cast; linarith
    · exact ⟨a, by rw [Function.update_of_ne hil]; exact ha⟩
  · intro i hi
    have h1 := gap_one h i hi
    change i ∈ Finset.Icc 1 (P.k - 1) at hi
    rw [Finset.mem_Icc] at hi
    have e1 := he i (Finset.mem_Icc.2 ⟨hi.1, by omega⟩)
    have e2 := he (i + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
    change max (P.u (i + 1)) (Function.update P.u' (l + 1) (P.u' (l + 1) + (n₀ : ℝ)) (i + 1)) + 1 / 2 ≤
      min (P.u i) (Function.update P.u' (l + 1) (P.u' (l + 1) + (n₀ : ℝ)) i) - 1 / 2
    rw [e1, e2]
    by_cases ha : i = l
    · subst ha
      rw [Function.update_self, Function.update_of_ne (by omega), min_self, max_eq_right (by linarith)]
      linarith
    · rw [Function.update_of_ne (show i + 1 ≠ l + 1 by omega), max_self]
      by_cases hb : i = l + 1
      · subst hb
        rw [Function.update_self, min_eq_left (by linarith)]
        linarith
      · rw [Function.update_of_ne hb, min_self]
        linarith

theorem ok_minus {P : M.Par} (h : P.OK) (l n₀ : ℕ) (he : ∀ i ∈ Finset.Icc 1 P.k, P.u i = P.u' i)
    (hg : 2 * (n₀ : ℝ) + 1 ≤ P.u' l - P.u' (l + 1)) :
    (shP P P.u (Function.update P.u' l (P.u' l - (n₀ : ℝ)))).OK := by
  have hn : (0 : ℝ) ≤ n₀ := Nat.cast_nonneg _
  refine ⟨h.k_pos, h.T_pos, h.T'_pos, h.int_u, ?_, ?_⟩
  · intro i hi
    obtain ⟨a, ha⟩ := h.int_u' i hi
    change ∃ n : ℤ, Function.update P.u' l (P.u' l - (n₀ : ℝ)) i - P.u 1 = n
    by_cases hil : i = l
    · subst hil
      refine ⟨a - n₀, ?_⟩
      rw [Function.update_self]; push_cast; linarith
    · exact ⟨a, by rw [Function.update_of_ne hil]; exact ha⟩
  · intro i hi
    have h1 := gap_one h i hi
    change i ∈ Finset.Icc 1 (P.k - 1) at hi
    rw [Finset.mem_Icc] at hi
    have e1 := he i (Finset.mem_Icc.2 ⟨hi.1, by omega⟩)
    have e2 := he (i + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
    change max (P.u (i + 1)) (Function.update P.u' l (P.u' l - (n₀ : ℝ)) (i + 1)) + 1 / 2 ≤
      min (P.u i) (Function.update P.u' l (P.u' l - (n₀ : ℝ)) i) - 1 / 2
    rw [e1, e2]
    by_cases ha : i = l
    · subst ha
      rw [Function.update_self, Function.update_of_ne (by omega), max_self, min_eq_right (by linarith)]
      linarith
    · rw [Function.update_of_ne ha, min_self]
      by_cases hb : i + 1 = l
      · subst hb
        rw [Function.update_self, max_eq_left (by linarith)]
        linarith
      · rw [Function.update_of_ne hb, max_self]
        linarith

theorem shiftExists_of (hA : GlobalTheory.WigSh.AmapsShExists) : GlobalTheory.WigSh.ShiftExists := by
  obtain ⟨c₃, hc⟩ := hA
  obtain ⟨Cb, hCb, hS⟩ := GlobalTheory.WithRightAction.exists_place_other_right_type
  refine ⟨c₃, Cb, hCb, ?_⟩
  intro P Wp Wq _ _ _ _ _ _ p l n₀ lp lm b he hl1 hl2 hg hb hn hb1 hp1 hp2 hm1 hm2
  obtain ⟨hOK, hz, hz', hT, hT', hπ, hπ'⟩ := p.hP
  obtain ⟨Wqp, i1, i2, i3, Wqm, j1, j2, j3, πp, πm, -, -, htp, htm, -⟩ :=
    GlobalTheory.WigSh.exists_shifted_types_lower_bound Wq P.k P.r p.T.base.z' p.T.base.π' P.u' l n₀ b hz'
      (by rw [hT']; exact hOK.T'_pos) hπ' (gap_nat hOK) hl1 hl2 hg hb hn hb1
  obtain ⟨pp, a1, a2, a3, a4, -, a6, a7, a8⟩ := hS P Wp Wq Wqp p P.u
    (Function.update P.u' (l + 1) (P.u' (l + 1) + (n₀ : ℝ))) πp lp
    ⟨ok_plus hOK l n₀ he hg, hz, hz', hT, hT', hπ, htp⟩ hp1 hp2
  obtain ⟨pm, b1, b2, b3, b4, -, b6, b7, b8⟩ := hS P Wp Wq Wqm p P.u
    (Function.update P.u' l (P.u' l - (n₀ : ℝ))) πm lm
    ⟨ok_minus hOK l n₀ he hg, hz, hz', hT, hT', hπ, htm⟩ hm1 hm2
  obtain ⟨Ap, Am, ApPt, AmPt, c1, c2, c3, c4⟩ := hc P Wp Wq Wqp Wqm P.u
    (Function.update P.u' (l + 1) (P.u' (l + 1) + (n₀ : ℝ))) P.u (Function.update P.u' l (P.u' l - (n₀ : ℝ)))
    p pp pm l n₀ b a2 a3 b2 b3 (fun h _ => congrFun a4 h) (fun h _ => congrFun b4 h) a6 a7 b6 b7 hl1 hl2 hg hb hn hb1
    (fun i _ => by
      by_cases h : i = l + 1
      · subst h; simp
      · rw [Function.update_of_ne h, if_neg h])
    (fun i _ => by
      by_cases h : i = l
      · subst h; simp
      · rw [Function.update_of_ne h, if_neg h])
  exact ⟨Wqp, i1, i2, i3, Wqm, j1, j2, j3, pp, pm, Ap, Am, ApPt, AmPt, a1, b1, a2, a3, a4, b2, b3, b4, a8, b8,
    c1, c2, c3, c4⟩

theorem shiftExists : GlobalTheory.WigSh.ShiftExists := shiftExists_of GlobalTheory.T.wignerMapsThreePlaces_exists

end GlobalTheory.wignerShiftedPlacesExist_proof
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WignerShiftedPlacesExistProofStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wignerShiftedPlacesExist_proof : GlobalTheory.WigSh.ShiftExists := by
  first | exact @GlobalTheory.wignerShiftedPlacesExist_proof.shiftExists | exact GlobalTheory.wignerShiftedPlacesExist_proof.shiftExists | (intros; apply GlobalTheory.wignerShiftedPlacesExist_proof.shiftExists <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliEigenfunctionPointwiseBoundOfEqualTypes
open BpJoin Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Formalism.QuantumDeterminants

namespace GlobalTheory.capelliEigenfunction_pointwiseBound_of_equalTypes

theorem gridNum_update {C b c : ℝ} {P : M.Par} {l : ℕ} {lam : Fin (2 * P.r + P.k + 1) → ℝ}
    (h : GridNum C b c P l lam) (x : ℝ) (hx : |x| ≤ b) :
    GridNum C b c (shP P P.u (Function.update P.u' l x)) l lam := by
  obtain ⟨h1, h2, h3, h4, -, h6, h7, h8, h9, h10, h11⟩ := h
  refine ⟨h1, h2, h3, h4, ?_, h6, h7, h8, ?_, h10, h11⟩
  · change |Function.update P.u' l x l| ≤ b
    rwa [Function.update_self]
  · intro s hs
    obtain ⟨ha, hb⟩ := h9 s hs
    refine ⟨fun hne => ?_, fun hne => ?_⟩
    · change lam s + 1 / 2 ≤ Function.update P.u' l x (s.val + 1)
      rw [Function.update_of_ne hne]; exact ha hne
    · change Function.update P.u' l x (s.val + 2) + 1 / 2 ≤ lam s
      rw [Function.update_of_ne hne]; exact hb hne

theorem decay_le (r k N : ℝ) (hr : 0 ≤ r) (hk : 0 ≤ k) (hN : 0 ≤ N) :
    (r + 1) ^ 2 * (r * (2 * r + k + 1) + 1) ≤ (r + 1) ^ 4 * (N * (2 * r + k + 1) ^ 2 + (2 * r + k + 1) ^ 3) := by
  set n := 2 * r + k + 1 with hn
  have h1 : r + 1 ≤ n := by linarith
  have h2 : r * n + 1 ≤ n ^ 2 := by nlinarith
  have h3 : n ^ 2 ≤ n ^ 3 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have h4 : (r + 1) ^ 2 ≤ (r + 1) ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have h5 : 0 ≤ N * n ^ 2 := by positivity
  have h6 : 0 ≤ r * n + 1 := by nlinarith
  exact mul_le_mul h4 (by linarith) h6 (by positivity)

theorem thmBp_eig_eq : GlobalTheory.HCXi.BesselXiIntegrable → P5.ThmPActualCpt → NFTopDomAll → ∀ C C₃ C₀ : ℝ, 0 ≤ C → 0 ≤ C₃ → 0 ≤ C₀ → ∃ C₄ Cc : ℝ, ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b c A₀ : ℝ) (n₀ p₀ : ℕ) (lam lam' : Fin (2 * P.r + P.k + 1) → ℝ), StdNum C b c P lam → (n₀ = 30 * (P.r + 1) ^ 2 + 6 ∧ (∀ i ∈ Finset.Icc 1 P.k, P.u i = P.u' i) ∧ ∃ l, 1 ≤ l ∧ l < P.k ∧ 2 * (n₀ : ℝ) + 1 ≤ P.u' l - P.u' (l + 1)) → 3 * (P.r + 1) ≤ 2 * p₀ → (p₀ : ℝ) ≤ C₀ * ((P.r : ℝ) + 1) ^ 2 → EigDec f A₀ lam' → Cc * ((P.r : ℝ) + 1) ^ 4 * (((3 * (P.r + 1) : ℕ) : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A₀ - (((2 * P.r + 2) * p₀ + n₀ * (P.r + 1) : ℕ) : ℝ) → (∀ s, |lam' s - lam s| + (((2 * P.r + 2) * p₀ + n₀ * (P.r + 1) : ℕ) : ℝ) ≤ c - 1) → TBB.RegularityBoundBigCell p f b C₃ (2 * p₀ + n₀) → TBB.ThmBpAt p f b C₄ n₀ p₀ := by
  intro hX hP hNF C C₃ C₀ hC hC₃ hC₀
  obtain ⟨c₃, Cb, -, hS⟩ := GlobalTheory.T.wignerShiftedPlacesExist_proof
  obtain ⟨C₄, Cc, hT⟩ := GlobalTheory.T.capelli_eigenfunction_bound_three_places hX hP hNF Cb C₃ (7 + C) C₀ hC₃ (by linarith) hC₀
  refine ⟨C₄, max (max Cc c₃) 0, ?_⟩
  intro P Wp Wq _ _ _ _ _ _ p f b c A₀ n₀ p₀ lam lam' hstd hcase hp₀ hp₀' heig hA hlam hreg
  obtain ⟨hn₀, he, l, hl1, hl2, hg⟩ := hcase
  obtain ⟨hG, -⟩ := hstd
  obtain ⟨hf1, hf2, hf3⟩ := heig
  have hml : l ∈ Finset.Icc 1 P.k := Finset.mem_Icc.2 ⟨hl1, hl2.le⟩
  have hml' : l + 1 ∈ Finset.Icc 1 P.k := Finset.mem_Icc.2 ⟨by omega, by omega⟩
  have Gl := hG l hml
  have Gl' := hG (l + 1) hml'
  have hc1 : 1 ≤ c := Gl.1
  have hcb : c + 2 ≤ b := Gl.2.1
  have hul : |P.u' l| ≤ b := Gl.2.2.2.2.1
  have hul' : |P.u' (l + 1)| ≤ b := Gl'.2.2.2.2.1
  have hn : (0 : ℝ) ≤ n₀ := Nat.cast_nonneg _
  rw [abs_le] at hul hul'
  have hnb : (n₀ : ℝ) ≤ b := by linarith [hul.2, hul'.1]
  obtain ⟨Wqp, i1, i2, i3, Wqm, j1, j2, j3, pp, pm, Ap, Am, ApPt, AmPt, a1, b1, a2, a3, -, b2, b3, -, a8, b8,
      c1, c2, -, c4⟩ := hS P Wp Wq p l n₀ (l + 1) l b he hl1 hl2 hg (fun i hi => (hG i hi).2.2.2.2.1) hnb
    (by linarith) (by omega) (by omega) hl1 hl2.le
  have hr : (0 : ℝ) ≤ P.r := Nat.cast_nonneg _
  have hk : (0 : ℝ) ≤ P.k := Nat.cast_nonneg _
  have hdec := decay_le P.r P.k ((3 * (P.r + 1) : ℕ) : ℝ) hr hk (Nat.cast_nonneg _)
  have hM0 : 0 ≤ max (max Cc c₃) 0 := le_max_right _ _
  have hM1 : Cc ≤ max (max Cc c₃) 0 := (le_max_left _ _).trans (le_max_left _ _)
  have hM2 : c₃ ≤ max (max Cc c₃) 0 := (le_max_right _ _).trans (le_max_left _ _)
  set M := max (max Cc c₃) 0 with hM
  rw [mul_assoc] at hA
  have hA1 : c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤ A₀ := by
    have e : ((2 * P.r + P.k + 1 : ℕ) : ℝ) = 2 * (P.r : ℝ) + P.k + 1 := by push_cast; ring
    rw [e, mul_assoc]
    have t1 := mul_le_mul_of_nonneg_right hM2
      (show 0 ≤ ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * (2 * (P.r : ℝ) + P.k + 1) + 1) by positivity)
    have t2 := mul_le_mul_of_nonneg_left hdec hM0
    have t3 : (0 : ℝ) ≤ (((2 * P.r + 2) * p₀ + n₀ * (P.r + 1) : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hA2 : Cc * ((P.r : ℝ) + 1) ^ 4 * (((3 * (P.r + 1) : ℕ) : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 +
      (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - ((n₀ * (P.r + 1) : ℕ) : ℝ) := by
    rw [mul_assoc]
    have t1 := mul_le_mul_of_nonneg_right hM1
      (show 0 ≤ ((P.r : ℝ) + 1) ^ 4 * (((3 * (P.r + 1) : ℕ) : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 +
      (2 * (P.r : ℝ) + P.k + 1) ^ 3) by positivity)
    rw [Nat.cast_add ((2 * P.r + 2) * p₀)] at hA
    linarith
  have Gp := gridNum_update Gl' (P.u' (l + 1) + (n₀ : ℝ)) (abs_le.2 ⟨by linarith [hul'.1], by linarith [hul.2]⟩)
  have Gm := gridNum_update Gl (P.u' l - (n₀ : ℝ)) (abs_le.2 ⟨by linarith [hul'.1], by linarith [hul.2]⟩)
  obtain ⟨hpos, hΛ, Yp, hWp, hLp⟩ := GlobalTheory.T.grids_at_place_longCut_normaliserPositive C b c _ Wp Wqp pp lam hC (by rw [a1]; exact Gp) (by
    rw [a1]
    change ((30 * (P.r + 1) ^ 2 + 6 : ℕ) : ℝ) ≤
      |P.u (l + 1) - Function.update P.u' (l + 1) (P.u' (l + 1) + (n₀ : ℝ)) (l + 1)|
    rw [Function.update_self, he _ hml', ← hn₀]
    exact le_abs.2 (Or.inr (by linarith)))
  obtain ⟨-, -, Ym, hWm, hLm⟩ := GlobalTheory.T.grids_at_place_longCut_normaliserPositive C b c _ Wp Wqm pm lam hC (by rw [b1]; exact Gm) (by
    rw [b1]
    change ((30 * (P.r + 1) ^ 2 + 6 : ℕ) : ℝ) ≤ |P.u l - Function.update P.u' l (P.u' l - (n₀ : ℝ)) l|
    rw [Function.update_self, he _ hml, ← hn₀]
    exact le_abs.2 (Or.inl (by linarith)))
  have hgap : ∀ s t, s ≠ t → 2 * c ≤ |lam s - lam t| := by
    intro s t hst
    rcases lt_or_gt_of_ne hst with h | h
    · exact le_abs.2 (Or.inl (by linarith [Gl.2.2.2.2.2.2.1 s t h]))
    · exact le_abs.2 (Or.inr (by linarith [Gl.2.2.2.2.2.2.1 t s h]))
  exact hT P Wp Wq Wqp Wqm _ _ _ _ p pp pm f Ap Am ApPt AmPt b (b ^ ((7 + C) * ((2 * P.r + 2 : ℕ) : ℝ))) A₀ n₀ p₀
    (n₀ * (P.r + 1)) (Pst lam c) (Pst lam c) Yp Ym 3 (3 * (P.r + 1)) (by linarith) hΛ le_rfl hn₀.le hp₀' a2 a3 b2 b3
    le_rfl (by omega) hpos hpos a8 b8 hf1 hf2 c1 c2 hA2 (c4 A₀ f hA1 (hf2 1)) hreg hWp hLp hWm hLm hp₀ lam lam' c
    hf3 hgap hlam (fun _ => le_rfl) (fun _ => le_rfl)

end GlobalTheory.capelliEigenfunction_pointwiseBound_of_equalTypes
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliEigenfunctionPointwiseBoundOfEqualTypesStatement
open BpJoin Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Formalism.QuantumDeterminants
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.capelliEigenfunction_pointwiseBound_of_equalTypes : GlobalTheory.HCXi.BesselXiIntegrable → P5.ThmPActualCpt → NFTopDomAll → ∀ C C₃ C₀ : ℝ, 0 ≤ C → 0 ≤ C₃ → 0 ≤ C₀ → ∃ C₄ Cc : ℝ, ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b c A₀ : ℝ) (n₀ p₀ : ℕ) (lam lam' : Fin (2 * P.r + P.k + 1) → ℝ), StdNum C b c P lam → (n₀ = 30 * (P.r + 1) ^ 2 + 6 ∧ (∀ i ∈ Finset.Icc 1 P.k, P.u i = P.u' i) ∧ ∃ l, 1 ≤ l ∧ l < P.k ∧ 2 * (n₀ : ℝ) + 1 ≤ P.u' l - P.u' (l + 1)) → 3 * (P.r + 1) ≤ 2 * p₀ → (p₀ : ℝ) ≤ C₀ * ((P.r : ℝ) + 1) ^ 2 → EigDec f A₀ lam' → Cc * ((P.r : ℝ) + 1) ^ 4 * (((3 * (P.r + 1) : ℕ) : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A₀ - (((2 * P.r + 2) * p₀ + n₀ * (P.r + 1) : ℕ) : ℝ) → (∀ s, |lam' s - lam s| + (((2 * P.r + 2) * p₀ + n₀ * (P.r + 1) : ℕ) : ℝ) ≤ c - 1) → TBB.RegularityBoundBigCell p f b C₃ (2 * p₀ + n₀) → TBB.ThmBpAt p f b C₄ n₀ p₀ := by
  first | exact @GlobalTheory.capelliEigenfunction_pointwiseBound_of_equalTypes.thmBp_eig_eq | exact GlobalTheory.capelliEigenfunction_pointwiseBound_of_equalTypes.thmBp_eig_eq | (intros; apply GlobalTheory.capelliEigenfunction_pointwiseBound_of_equalTypes.thmBp_eig_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.PointwiseBoundCapelliEigenfunction
open BpJoin Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Formalism.QuantumDeterminants

namespace GlobalTheory.BpEigen

theorem pointwise_bound_mono {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    {p : KB.Pl P Wp Wq} {f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} {b C C' : ℝ} {n₀ p₀ : ℕ}
    (hb : 1 ≤ b) (hC : C ≤ C') (h : TBB.ThmBpAt p f b C n₀ p₀) : TBB.ThmBpAt p f b C' n₀ p₀ := by
  intro γ hγ hG
  refine (h γ hγ hG).trans ?_
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (inv_nonneg.2 hG.le) _)
  refine Real.rpow_le_rpow_of_exponent_le hb ?_
  exact mul_le_mul_of_nonneg_right hC (by positivity)

theorem pointwise_bound_eigenfunction : GlobalTheory.HCXi.BesselXiIntegrable → P5.ThmPActualCpt → ∀ C C₃ C₀ : ℝ, 0 ≤ C → 0 ≤ C₃ → 0 ≤ C₀ → ∃ C₄ Cc : ℝ, ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b c A₀ : ℝ) (n₀ p₀ : ℕ) (lam lam' : Fin (2 * P.r + P.k + 1) → ℝ), StdNum C b c P lam → Cases P n₀ → 3 * (P.r + 1) ≤ 2 * p₀ → (p₀ : ℝ) ≤ C₀ * ((P.r : ℝ) + 1) ^ 2 → EigDec f A₀ lam' → Cc * ((P.r : ℝ) + 1) ^ 4 * (((3 * (P.r + 1) : ℕ) : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A₀ - (((2 * P.r + 2) * p₀ + n₀ * (P.r + 1) : ℕ) : ℝ) → (∀ s, |lam' s - lam s| + (((2 * P.r + 2) * p₀ + n₀ * (P.r + 1) : ℕ) : ℝ) ≤ c - 1) → TBB.RegularityBoundBigCell p f b C₃ (2 * p₀ + n₀) → TBB.ThmBpAt p f b C₄ n₀ p₀ := by
  intro hX hP C C₃ C₀ hC hC₃ hC₀
  have hN := GlobalTheory.T.topDensity_cutoff_dominated_of_HC_xi hX
  obtain ⟨D₁, E₁, h₁⟩ := GlobalTheory.T.capelliEigenfunction_pointwiseBound_of_differentTypes hX hP hN C C₃ C₀ hC hC₃ hC₀
  obtain ⟨D₂, E₂, h₂⟩ := GlobalTheory.T.capelliEigenfunction_pointwiseBound_of_equalTypes hX hP hN C C₃ C₀ hC hC₃ hC₀
  refine ⟨max D₁ D₂, max E₁ E₂, ?_⟩
  intro P Wp Wq _ _ _ _ _ _ p f b c A₀ n₀ p₀ lam lam' hS hc h3 hp hE hA hl hR
  have key : ∀ E : ℝ, E ≤ max E₁ E₂ → E * ((P.r : ℝ) + 1) ^ 4 * (((3 * (P.r + 1) : ℕ) : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A₀ - (((2 * P.r + 2) * p₀ + n₀ * (P.r + 1) : ℕ) : ℝ) := by
    intro E hE'
    refine le_trans ?_ hA
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hE' (by positivity)) (by positivity)
  rcases hc with hc | hc
  · have hb : 1 ≤ b := by
      obtain ⟨-, l, hl', -⟩ := hc
      obtain ⟨a1, a2, -⟩ := hS.1 l hl'
      linarith
    exact pointwise_bound_mono hb (le_max_left _ _)
      (h₁ P Wp Wq p f b c A₀ n₀ p₀ lam lam' hS hc h3 hp hE (key _ (le_max_left _ _)) hl hR)
  · have hb : 1 ≤ b := by
      obtain ⟨-, -, l, hl1, hl2, -⟩ := hc
      obtain ⟨a1, a2, -⟩ := hS.1 l (Finset.mem_Icc.2 ⟨hl1, hl2.le⟩)
      linarith
    exact pointwise_bound_mono hb (le_max_right _ _)
      (h₂ P Wp Wq p f b c A₀ n₀ p₀ lam lam' hS hc h3 hp hE (key _ (le_max_right _ _)) hl hR)

end GlobalTheory.BpEigen
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.PointwiseBoundCapelliEigenfunctionStatement
open BpJoin Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Formalism.QuantumDeterminants
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointwiseBound_capelli_eigenfunction : GlobalTheory.HCXi.BesselXiIntegrable → P5.ThmPActualCpt → ∀ C C₃ C₀ : ℝ, 0 ≤ C → 0 ≤ C₃ → 0 ≤ C₀ → ∃ C₄ Cc : ℝ, ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b c A₀ : ℝ) (n₀ p₀ : ℕ) (lam lam' : Fin (2 * P.r + P.k + 1) → ℝ), StdNum C b c P lam → Cases P n₀ → 3 * (P.r + 1) ≤ 2 * p₀ → (p₀ : ℝ) ≤ C₀ * ((P.r : ℝ) + 1) ^ 2 → EigDec f A₀ lam' → Cc * ((P.r : ℝ) + 1) ^ 4 * (((3 * (P.r + 1) : ℕ) : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A₀ - (((2 * P.r + 2) * p₀ + n₀ * (P.r + 1) : ℕ) : ℝ) → (∀ s, |lam' s - lam s| + (((2 * P.r + 2) * p₀ + n₀ * (P.r + 1) : ℕ) : ℝ) ≤ c - 1) → TBB.RegularityBoundBigCell p f b C₃ (2 * p₀ + n₀) → TBB.ThmBpAt p f b C₄ n₀ p₀ := by
  first | exact @GlobalTheory.BpEigen.pointwise_bound_eigenfunction | exact GlobalTheory.BpEigen.pointwise_bound_eigenfunction | (intros; apply GlobalTheory.BpEigen.pointwise_bound_eigenfunction <;> assumption)
end
