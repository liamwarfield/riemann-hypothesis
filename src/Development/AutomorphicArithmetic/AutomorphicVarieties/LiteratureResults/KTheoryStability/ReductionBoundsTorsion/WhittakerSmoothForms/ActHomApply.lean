module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.SBridgeAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.WhittakerSmoothForms.BfDep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.WhittakerSmoothForms.PosDefOfSphere

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.WhittakerSmoothForms.ExtDerivDelG
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.WhittakerSmoothForms.Smooth
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.WhittakerSmoothForms.SkipSuccAbove
noncomputable section

open Set Filter Topology

namespace PositivityTheory.KB.WhittakerCocycle

set_option linter.unusedSectionVars false

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {Γ : Type} [Group Γ]

theorem skip_zero_cons (γ : Γ) (σ : ℕ → Γ) : skip 0 (cons γ σ) = σ := by
  funext n; simp [skip, cons]

theorem skip_succ_cons (i : ℕ) (γ : Γ) (σ : ℕ → Γ) : skip (i + 1) (cons γ σ) = cons γ (skip i σ) := by
  funext n
  cases n with
  | zero => simp [skip, cons]
  | succ m => simp [skip, cons]

theorem delG_cons (n : ℕ) {X : Type} [AddCommGroup X] [Module ℝ X] (β : (ℕ → Γ) → X) (γ : Γ)
    (σ : ℕ → Γ) : delG (n + 1) β (cons γ σ) = β σ - delG n (fun τ => β (cons γ τ)) σ := by
  simp only [delG]
  rw [Finset.sum_range_succ', skip_zero_cons]
  simp only [skip_succ_cons, pow_succ, mul_neg_one, neg_smul, Finset.sum_neg_distrib,
    pow_zero, one_smul]
  abel

theorem skip_succAbove {m : ℕ} (σ : ℕ → Γ) (i : Fin (m + 2)) (l : Fin (m + 1)) :
    skip (i : ℕ) σ (l : ℕ) = σ ((i.succAbove l : Fin (m + 2)) : ℕ) := by
  rw [skip]
  rcases lt_or_ge (l : ℕ) (i : ℕ) with hl | hl
  · rw [if_pos hl, Fin.succAbove_of_castSucc_lt _ _ (by simpa [Fin.lt_def] using hl)]
    simp
  · rw [if_neg (not_lt.mpr hl), Fin.succAbove_of_le_castSucc _ _ (by simpa [Fin.le_def] using hl)]
    simp

variable (U : Set V) (A : Γ →* (V →L[ℝ] V)) (φ : V → ℝ)

theorem pLoc : PLoc U A φ := by
  intro H h hh
  obtain ⟨t, ht, hfin⟩ := H.locFin ⟨h, hh⟩
  obtain ⟨u, hu, hut⟩ := (mem_nhds_subtype U ⟨h, hh⟩ t).mp ht
  refine ⟨hfin.toFinset, u ∩ U, inter_mem hu (H.isOpen.mem_nhds hh), inter_subset_right, ?_⟩
  intro γ hγ x hx
  by_contra hne
  apply hγ
  rw [Set.Finite.mem_toFinset]
  exact ⟨⟨x, hx.2⟩, hne, hut hx.1⟩

theorem finsum_psi (hL : PLoc U A φ) (H : Hyp U A φ) {h : V} (hh : h ∈ U) :
    ∃ s : Finset Γ, ∃ W ∈ 𝓝 h, W ⊆ U ∧ ∀ x ∈ W, (∑ γ ∈ s, psi A φ γ x = 1) ∧
      ∀ {M : Type} [AddCommGroup M] [Module ℝ M] (F : Γ → M),
        ∑ᶠ γ, psi A φ γ x • F γ = ∑ γ ∈ s, psi A φ γ x • F γ := by
  obtain ⟨s, W, hW, hWU, hs⟩ := hL H h hh
  refine ⟨s, W, hW, hWU, fun x hx => ⟨?_, ?_⟩⟩
  · have h1 := H.sum_one x (hWU hx)
    rw [finsum_eq_sum_of_support_subset (s := s)] at h1
    · exact h1
    · intro γ hγ
      by_contra hγs
      exact hγ (hs γ hγs x hx)
  · intro M _ _ F
    apply finsum_eq_sum_of_support_subset
    intro γ hγ
    by_contra hγs
    apply hγ
    simp [hs γ hγs x hx]

theorem pHom (hL : PLoc U A φ) : PHom U A φ := by
  intro H q n β σ h hh
  obtain ⟨s, W, hW, hWU, hs⟩ := finsum_psi U A φ hL H hh
  obtain ⟨h1, hF⟩ := hs h (mem_of_mem_nhds hW)
  have hK : ∀ (β' : (ℕ → Γ) → V → V [⋀^Fin q]→L[ℝ] ℝ) τ,
      Kf A φ β' τ h = ∑ γ ∈ s, psi A φ γ h • β' (cons γ τ) h :=
    fun β' τ => hF (fun γ => β' (cons γ τ) h)
  rw [hK (delG (n + 1) β)]
  simp only [delG_cons, Pi.sub_apply, smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, h1,
    one_smul, sub_sub_cancel]
  simp only [delG, Finset.sum_apply, Pi.smul_apply, hK, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun i _ => smul_comm _ _ _

end PositivityTheory.KB.WhittakerCocycle

end
end

noncomputable section

open Set Filter Topology

namespace PositivityTheory.KB.WhittakerCocycle

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {Γ : Type} [Group Γ]

variable (U : Set V) (A : Γ →* (V →L[ℝ] V)) (φ : V → ℝ)

theorem eta_zero {k : ℕ} (c : (Fin (k + 2) → Γ) → ℝ) (σ : ℕ → Γ) :
    eta A φ c 0 σ = fun _ => ContinuousAlternatingMap.constOfIsEmpty ℝ V (Fin 0) (c fun i => σ i) := rfl

theorem eta_succ {k : ℕ} (c : (Fin (k + 2) → Γ) → ℝ) (j : ℕ) (σ : ℕ → Γ) :
    eta A φ c (j + 1) σ = extDeriv (Kf A φ (eta A φ c j) σ) := rfl

theorem psi_contDiffAt (H : Hyp U A φ) (γ : Γ) {h : V} (hh : h ∈ U) :
    ContDiffAt ℝ (⊤ : ℕ∞) (psi A φ γ) h := by
  have h1 : ContDiffAt ℝ (⊤ : ℕ∞) φ (A γ⁻¹ h) :=
    H.smooth.contDiffAt (H.isOpen.mem_nhds (H.mapsTo _ h hh))
  exact h1.comp h (A γ⁻¹).contDiff.contDiffAt

theorem Kf_contDiffOn (hL : PLoc U A φ) (H : Hyp U A φ) {q : ℕ}
    (β : (ℕ → Γ) → V → V [⋀^Fin q]→L[ℝ] ℝ) (hβ : ∀ τ, ContDiffOn ℝ (⊤ : ℕ∞) (β τ) U) (σ : ℕ → Γ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (Kf A φ β σ) U := by
  intro h hh
  obtain ⟨s, W, hW, hWU, hz⟩ := hL H h hh
  have hsum : ContDiffAt ℝ (⊤ : ℕ∞) (fun x => ∑ γ ∈ s, psi A φ γ x • β (cons γ σ) x) h := by
    apply ContDiffAt.sum
    intro γ _
    exact (psi_contDiffAt U A φ H γ hh).smul ((hβ _).contDiffAt (H.isOpen.mem_nhds hh))
  refine (hsum.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [hW] with x hx
  show (∑ᶠ γ, psi A φ γ x • β (cons γ σ) x) = _
  apply finsum_eq_sum_of_support_subset
  intro γ hγ
  by_contra hn
  apply hγ
  simp [hz γ hn x hx]

theorem extDeriv_contDiffOn (H : Hyp U A φ) {q : ℕ} {ω : V → V [⋀^Fin q]→L[ℝ] ℝ}
    (hω : ContDiffOn ℝ (⊤ : ℕ∞) ω U) : ContDiffOn ℝ (⊤ : ℕ∞) (extDeriv ω) U := by
  have hd : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ ω) U := hω.fderiv_of_isOpen H.isOpen (by simp)
  exact (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ V ℝ).contDiff.comp_contDiffOn hd

theorem pSmooth (hL : PLoc U A φ) : PSmooth U A φ := by
  intro H k c j σ
  have key : ∀ (i : ℕ) (τ : ℕ → Γ), ContDiffOn ℝ (⊤ : ℕ∞) (eta A φ c i τ) U := by
    intro i
    induction i with
    | zero =>
      intro τ
      rw [eta_zero]
      exact contDiffOn_const
    | succ i ih =>
      intro τ
      rw [eta_succ]
      exact extDeriv_contDiffOn U A φ H (Kf_contDiffOn U A φ hL H _ ih τ)
  exact ⟨key j σ, Kf_contDiffOn U A φ hL H _ (key j) σ⟩

theorem pClosed (hS : PSmooth U A φ) : PClosed U A φ := by
  intro H k c j σ h hh
  cases j with
  | zero =>
    rw [eta_zero]
    ext v
    simp [extDeriv, ContinuousAlternatingMap.alternatizeUncurryFin_apply]
  | succ j =>
    rw [eta_succ]
    exact extDeriv_extDeriv_apply ((hS H k c j σ).2.contDiffAt (H.isOpen.mem_nhds hh))
      (by
        rw [minSmoothness_of_isRCLikeNormedField]
        first
        | exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤)
        | (show ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞); exact WithTop.coe_le_coe.2 le_top)
        | simp)

theorem pDep : PDep A φ := by
  intro k c j
  induction j with
  | zero =>
    intro σ σ' hσ
    rw [eta_zero, eta_zero]
    have e : (fun i : Fin (k + 2) => σ i) = fun i : Fin (k + 2) => σ' i := by
      funext i
      have := i.isLt
      exact hσ i (by omega)
    rw [e]
  | succ j ih =>
    intro σ σ' hσ
    rw [eta_succ, eta_succ]
    have e : Kf A φ (eta A φ c j) σ = Kf A φ (eta A φ c j) σ' := by
      funext x
      simp only [Kf]
      congr 1
      funext γ
      rw [ih (cons γ σ) (cons γ σ')]
      intro n hn
      cases n with
      | zero => rfl
      | succ m => exact hσ m (by omega)
    rw [e]

end PositivityTheory.KB.WhittakerCocycle

end
end

noncomputable section

open Set Filter Topology

namespace PositivityTheory.KB.WhittakerCocycle

set_option linter.unusedSectionVars false

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {Γ : Type} [Group Γ]

variable (U : Set V) (A : Γ →* (V →L[ℝ] V)) (φ : V → ℝ)

theorem extDeriv_delG (n : ℕ) {q : ℕ} (β : (ℕ → Γ) → V → V [⋀^Fin q]→L[ℝ] ℝ) (σ : ℕ → Γ) (h : V)
    (hd : ∀ i, DifferentiableAt ℝ (β (skip i σ)) h) :
    delG n (fun τ => extDeriv (β τ)) σ h = extDeriv (delG n β σ) h := by
  have e : delG n β σ = fun x => ∑ i ∈ Finset.range (n + 2), (-1 : ℝ) ^ i • β (skip i σ) x := by
    funext x; simp [delG, Finset.sum_apply]
  rw [e, extDeriv, fderiv_fun_sum (A := fun i y => (-1 : ℝ) ^ i • β (skip i σ) y)
    (fun i _ => (hd i).const_smul ((-1 : ℝ) ^ i))]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [fderiv_fun_const_smul (hd _), delG, Finset.sum_apply, Pi.smul_apply, extDeriv,
    ← ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply, map_sum, map_smul]

theorem pCoc (hH : PHom U A φ) (hS : PSmooth U A φ) (hC : PClosed U A φ) :
    PCoc U A φ := by
  intro H k c hc j
  induction j with
  | zero =>
    intro _ σ h _
    ext v
    simp only [delG, Finset.sum_apply, Pi.smul_apply, eta_zero, ContinuousAlternatingMap.sum_apply,
      ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.constOfIsEmpty_apply,
      ContinuousAlternatingMap.coe_zero, Pi.zero_apply, smul_eq_mul, Nat.sub_zero]
    rw [Finset.sum_range]
    refine (Finset.sum_congr rfl fun i _ => ?_).trans (hc.coc fun l => σ l)
    congr 2
    funext l
    exact skip_succAbove σ i l
  | succ j ih =>
    intro hj σ h hh
    have hj' : j ≤ k + 1 := by omega
    have e1 : k + 1 - (j + 1) = k - j := by omega
    rw [e1]
    have e2 : delG (k - j) (eta A φ c (j + 1)) σ h =
        delG (k - j) (fun τ => extDeriv (Kf A φ (eta A φ c j) τ)) σ h := rfl
    rw [e2, extDeriv_delG (k - j) (Kf A φ (eta A φ c j)) σ h (fun i =>
      ((hS H k c j _).2.contDiffAt (H.isOpen.mem_nhds hh)).differentiableAt (by simp))]
    have hev : delG (k - j) (Kf A φ (eta A φ c j)) σ =ᶠ[𝓝 h] eta A φ c j σ := by
      filter_upwards [H.isOpen.mem_nhds hh] with x hx
      rw [hH H j (k - j) (eta A φ c j) σ x hx]
      have h0 : Kf A φ (delG (k - j + 1) (eta A φ c j)) σ x = 0 := by
        unfold Kf
        have e3 : k - j + 1 = k + 1 - j := by omega
        simp only [e3, ih hj' _ x hx, smul_zero, finsum_zero]
      rw [h0, sub_zero]
    rw [hev.extDeriv_eq]
    exact hC H k c j σ h hh

end PositivityTheory.KB.WhittakerCocycle

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.WhittakerSmoothForms.AltSmulRightComp
noncomputable section

open Set Filter Topology

namespace PositivityTheory.KB.WhittakerCocycle

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {Γ : Type} [Group Γ]

def Nr (U : Set V) (A : Γ →* (V →L[ℝ] V)) (φ : V → ℝ) (h : V) (γ : Γ) : Prop :=
  ∃ hm : A γ⁻¹ h ∈ U, (⟨A γ⁻¹ h, hm⟩ : U) ∈ closure {x : U | φ x ≠ 0}

theorem diffAt_of {U : Set V} (hU : IsOpen U) {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : V → F} (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U) {h : V} (hh : h ∈ U) : DifferentiableAt ℝ f h := by
  exact (hf.contDiffAt (hU.mem_nhds hh)).differentiableAt (by simp)

theorem psi_contDiffOn {U : Set V} {A : Γ →* (V →L[ℝ] V)} {φ : V → ℝ} (H : Hyp U A φ) (γ : Γ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (psi A φ γ) U := by
  have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => φ (A γ⁻¹ x)) U :=
    H.smooth.comp (A γ⁻¹).contDiff.contDiffOn (fun x hx => H.mapsTo γ⁻¹ x hx)
  exact h1

theorem nr_eventually {U : Set V} {A : Γ →* (V →L[ℝ] V)} {φ : V → ℝ} (H : Hyp U A φ) {h : V}
    (hh : h ∈ U) {γ : Γ} (hγ : ¬ Nr U A φ h γ) : psi A φ γ =ᶠ[𝓝 h] fun _ => 0 := by
  have hp : A γ⁻¹ h ∈ U := H.mapsTo _ h hh
  have hn : (⟨A γ⁻¹ h, hp⟩ : U) ∉ closure {x : U | φ x ≠ 0} := fun hc => hγ ⟨hp, hc⟩
  let g : U → U := fun x => ⟨A γ⁻¹ x, H.mapsTo _ x x.2⟩
  have hg : Continuous g :=
    ((A γ⁻¹).continuous.comp continuous_subtype_val).subtype_mk _
  have h1 : ∀ᶠ x in 𝓝 (⟨h, hh⟩ : U), g x ∈ (closure {x : U | φ x ≠ 0})ᶜ :=
    hg.continuousAt (isClosed_closure.isOpen_compl.mem_nhds hn)
  have h2 : ∀ᶠ x in 𝓝 (⟨h, hh⟩ : U), psi A φ γ x.1 = 0 := h1.mono fun x hx => by
    have h3 : g x ∉ {x : U | φ x ≠ 0} := fun h' => hx (subset_closure h')
    simp only [Set.mem_setOf_eq, not_not] at h3
    exact h3
  have h4 : ∀ᶠ x in Filter.map (fun x : U => (x : V)) (𝓝 (⟨h, hh⟩ : U)), psi A φ γ x = 0 := h2
  rw [map_nhds_subtype_val, H.isOpen.nhdsWithin_eq hh] at h4
  exact h4

theorem nr_fderiv {U : Set V} {A : Γ →* (V →L[ℝ] V)} {φ : V → ℝ} (H : Hyp U A φ) {h : V}
    (hh : h ∈ U) {γ : Γ} (hγ : ¬ Nr U A φ h γ) : fderiv ℝ (psi A φ γ) h = 0 := by
  rw [(nr_eventually H hh hγ).fderiv_eq]
  simp

theorem nr_mul {U : Set V} {A : Γ →* (V →L[ℝ] V)} {φ : V → ℝ} {O : Set Γ}
    (hOv : ∀ γ, ∀ h : U, h ∈ closure {x : U | φ x ≠ 0} → ∀ hm : A γ⁻¹ h ∈ U,
      (⟨A γ⁻¹ h, hm⟩ : U) ∈ closure {x : U | φ x ≠ 0} → γ ∈ O)
    {h : V} {γ γ' : Γ} (h1 : Nr U A φ h γ) (h2 : Nr U A φ h γ') : γ⁻¹ * γ' ∈ O := by
  obtain ⟨hm1, hc1⟩ := h1
  obtain ⟨hm2, hc2⟩ := h2
  have key : A (γ⁻¹ * γ')⁻¹ (A γ⁻¹ h) = A γ'⁻¹ h := by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul]
    rw [show (γ⁻¹ * γ')⁻¹ * γ⁻¹ = γ'⁻¹ by group]
  have hm : A (γ⁻¹ * γ')⁻¹ (A γ⁻¹ h) ∈ U := by rw [key]; exact hm2
  refine hOv (γ⁻¹ * γ') ⟨A γ⁻¹ h, hm1⟩ hc1 hm ?_
  convert hc2 using 1
  exact Subtype.ext key

theorem nr_exists {U : Set V} {A : Γ →* (V →L[ℝ] V)} {φ : V → ℝ} (H : Hyp U A φ) {h : V}
    (hh : h ∈ U) : ∃ γ, Nr U A φ h γ := by
  by_contra hne
  have hz : ∀ γ, φ (A γ⁻¹ h) = 0 := fun γ => by
    by_contra h0
    exact hne ⟨γ, H.mapsTo _ h hh, subset_closure h0⟩
  have hs := H.sum_one h hh
  simp only [hz, finsum_zero] at hs
  exact zero_ne_one hs

theorem c_bdd {O : Set Γ} (hO : O.Finite) {k : ℕ} (c : (Fin (k + 2) → Γ) → ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ τ : Fin (k + 2) → Γ, (∀ i, τ i ∈ O) → |c τ| ≤ C := by
  have hfin : (Set.pi Set.univ (fun _ : Fin (k + 2) => O)).Finite := Set.Finite.pi (fun _ => hO)
  obtain ⟨B, hB⟩ := (hfin.image (fun τ => |c τ|)).bddAbove
  refine ⟨max B 0, le_max_right _ _, fun τ hτ => ?_⟩
  exact le_trans (hB ⟨τ, fun i _ => hτ i, rfl⟩) (le_max_left _ _)

theorem alt_smulRight_comp {n : ℕ} (f : V →L[ℝ] ℝ) (b : V [⋀^Fin n]→L[ℝ] ℝ) (T : V →L[ℝ] V) :
    (ContinuousAlternatingMap.alternatizeUncurryFin (f.smulRight b)).compContinuousLinearMap T =
      ContinuousAlternatingMap.alternatizeUncurryFin
        ((f.comp T).smulRight (b.compContinuousLinearMap T)) := by
  ext v
  simp [ContinuousAlternatingMap.alternatizeUncurryFin_apply, Fin.removeNth, Function.comp_def]
  rfl

theorem sum_compCLM {ι : Type} {n : ℕ} (s : Finset ι) (X : ι → V [⋀^Fin n]→L[ℝ] ℝ)
    (T : V →L[ℝ] V) :
    (∑ i ∈ s, X i).compContinuousLinearMap T = ∑ i ∈ s, (X i).compContinuousLinearMap T := by
  ext v
  simp [ContinuousAlternatingMap.sum_apply]

theorem nr_cons {U : Set V} {A : Γ →* (V →L[ℝ] V)} {φ : V → ℝ} {h : V} {γ : Γ} {σ : ℕ → Γ}
    (hγ : Nr U A φ h γ) (hσ : ∀ n, Nr U A φ h (σ n)) : ∀ n, Nr U A φ h (cons γ σ n) := by
  intro n
  cases n with
  | zero => exact hγ
  | succ n => exact hσ n

theorem claim {U : Set V} {A : Γ →* (V →L[ℝ] V)} {φ : V → ℝ} (hL : PLoc U A φ)
    (hS : PSmooth U A φ) (hCl : PClosed U A φ) (H : Hyp U A φ) {O : Set Γ} (hO : O.Finite)
    (hOv : ∀ γ, ∀ h : U, h ∈ closure {x : U | φ x ≠ 0} → ∀ hm : A γ⁻¹ h ∈ U,
      (⟨A γ⁻¹ h, hm⟩ : U) ∈ closure {x : U | φ x ≠ 0} → γ ∈ O)
    {k : ℕ} (c : (Fin (k + 2) → Γ) → ℝ) (hc : Coc c) (j : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ h ∈ U, ∀ (T : V →L[ℝ] V) (M : ℝ), 0 ≤ M →
      (∀ γ, ‖(fderiv ℝ (psi A φ γ) h).comp T‖ ≤ M) → ∀ σ : ℕ → Γ, (∀ n, Nr U A φ h (σ n)) →
      ‖(eta A φ c j σ h).compContinuousLinearMap T‖ ≤ C * M ^ j := by
  classical
  obtain ⟨C0, hC0, hC0b⟩ := c_bdd hO c
  induction j with
  | zero =>
    refine ⟨C0, hC0, fun h hh T M hM hT σ hσ => ?_⟩
    have e : (eta A φ c 0 σ h).compContinuousLinearMap T
        = ContinuousAlternatingMap.constOfIsEmpty ℝ V (Fin 0) (c fun i => σ i) := by
      rw [eta.eq_1]
      ext m
      simp
    rw [e, ContinuousAlternatingMap.norm_constOfIsEmpty, pow_zero, mul_one, Real.norm_eq_abs]
    rw [← hc.inv (σ 0)⁻¹ (fun i => σ i)]
    exact hC0b _ (fun i => nr_mul hOv (hσ 0) (hσ i))
  | succ j ih =>
    obtain ⟨Cj, hCj, hCjb⟩ := ih
    refine ⟨(hO.toFinset.card : ℝ) * (((j : ℝ) + 1) * Cj),
      mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (by positivity) hCj),
      fun h hh T M hM hT σ hσ => ?_⟩
    obtain ⟨s, W, hW, hWU, hs⟩ := hL H h hh
    have hloc : Kf A φ (eta A φ c j) σ =ᶠ[𝓝 h]
        fun x => ∑ γ ∈ s, psi A φ γ x • eta A φ c j (cons γ σ) x := by
      filter_upwards [hW] with x hx
      show ∑ᶠ γ, psi A φ γ x • eta A φ c j (cons γ σ) x = _
      apply finsum_eq_sum_of_support_subset
      intro γ hγ
      by_contra hγs
      exact (Function.mem_support.mp hγ) (by simp [hs γ hγs x hx])
    have hdψ : ∀ γ, DifferentiableAt ℝ (psi A φ γ) h :=
      fun γ => diffAt_of H.isOpen (psi_contDiffOn H γ) hh
    have hdη : ∀ γ, DifferentiableAt ℝ (eta A φ c j (cons γ σ)) h :=
      fun γ => diffAt_of H.isOpen (hS H k c j (cons γ σ)).1 hh
    have hder : fderiv ℝ (Kf A φ (eta A φ c j) σ) h = ∑ γ ∈ s,
        (psi A φ γ h • fderiv ℝ (eta A φ c j (cons γ σ)) h
          + (fderiv ℝ (psi A φ γ) h).smulRight (eta A φ c j (cons γ σ) h)) := by
      rw [hloc.fderiv_eq, fderiv_fun_sum (A := fun γ x => psi A φ γ x • eta A φ c j (cons γ σ) x)
        (fun γ _ => by exact (hdψ γ).smul (hdη γ))]
      refine Finset.sum_congr rfl fun γ _ => ?_
      exact fderiv_fun_smul (hdψ γ) (hdη γ)
    have heta : eta A φ c (j + 1) σ h = ∑ γ ∈ s, ContinuousAlternatingMap.alternatizeUncurryFin
        ((fderiv ℝ (psi A φ γ) h).smulRight (eta A φ c j (cons γ σ) h)) := by
      rw [show eta A φ c (j + 1) σ = extDeriv (Kf A φ (eta A φ c j) σ) from eta.eq_2 A φ c σ j]
      show ContinuousAlternatingMap.alternatizeUncurryFin (fderiv ℝ (Kf A φ (eta A φ c j) σ) h) = _
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hder, ← ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply, map_sum]
      refine Finset.sum_congr rfl fun γ _ => ?_
      rw [map_add (f := _), map_smul, ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply,
        ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply]
      have hz : ContinuousAlternatingMap.alternatizeUncurryFin
          (fderiv ℝ (eta A φ c j (cons γ σ)) h) = 0 := hCl H k c j (cons γ σ) h hh
      rw [hz, smul_zero, zero_add]
    obtain ⟨γ0, hγ0⟩ := nr_exists H hh
    have hcard : (s.filter (Nr U A φ h)).card ≤ hO.toFinset.card := by
      apply Finset.card_le_card_of_injOn (fun γ => γ0⁻¹ * γ)
      · intro γ hγ
        simp only [Finset.coe_filter, Finset.mem_filter, Set.mem_setOf_eq, Finset.mem_coe] at hγ
        simp only [Finset.coe_filter, Set.Finite.coe_toFinset, Set.Finite.mem_toFinset, Finset.mem_coe]
        exact nr_mul hOv hγ0 hγ.2
      · intro a _ b _ hab
        exact mul_left_cancel hab
    have hB : 0 ≤ ((j : ℝ) + 1) * (M * (Cj * M ^ j)) :=
      mul_nonneg (by positivity) (mul_nonneg hM (mul_nonneg hCj (pow_nonneg hM _)))
    have hterm : ∀ γ ∈ s, ‖ContinuousAlternatingMap.alternatizeUncurryFin
        (((fderiv ℝ (psi A φ γ) h).comp T).smulRight
          ((eta A φ c j (cons γ σ) h).compContinuousLinearMap T))‖
        ≤ if Nr U A φ h γ then ((j : ℝ) + 1) * (M * (Cj * M ^ j)) else 0 := by
      intro γ _
      split_ifs with hγ
      · refine (ContinuousAlternatingMap.norm_alternatizeUncurryFin_le _).trans ?_
        rw [ContinuousLinearMap.norm_smulRight_apply]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul (hT γ) (hCjb h hh T M hM hT _ (nr_cons hγ hσ)) (norm_nonneg _) hM)
          (by positivity)
      · refine (ContinuousAlternatingMap.norm_alternatizeUncurryFin_le _).trans (le_of_eq ?_)
        rw [ContinuousLinearMap.norm_smulRight_apply, nr_fderiv H hh hγ]
        simp
    rw [heta, sum_compCLM]
    simp only [alt_smulRight_comp]
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    calc ((s.filter (Nr U A φ h)).card : ℝ) * (((j : ℝ) + 1) * (M * (Cj * M ^ j)))
        ≤ (hO.toFinset.card : ℝ) * (((j : ℝ) + 1) * (M * (Cj * M ^ j))) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hB
      _ = (hO.toFinset.card : ℝ) * (((j : ℝ) + 1) * Cj) * M ^ (j + 1) := by ring

theorem pBound (U : Set V) (A : Γ →* (V →L[ℝ] V)) (φ : V → ℝ) (hL : PLoc U A φ)
    (hS : PSmooth U A φ) (hCl : PClosed U A φ) (hCoc : PCoc U A φ) (hD : PDep A φ) :
    PBound U A φ := by
  intro Hy O hO hOv _ k c hc
  obtain ⟨C, -, hC⟩ := claim hL hS hCl Hy hO hOv c hc (k + 1)
  refine ⟨C, fun h hh T M hM hT => ?_⟩
  obtain ⟨γ0, hγ0⟩ := nr_exists Hy hh
  have e1 : eta A φ c (k + 1) (fun _ => 1) = eta A φ c (k + 1) (skip 0 (cons γ0 fun _ => 1)) :=
    hD k c (k + 1) _ _ (fun n _ => by simp [skip, cons])
  have e2 : eta A φ c (k + 1) (skip 1 (cons γ0 fun _ => 1)) = eta A φ c (k + 1) (fun _ => γ0) :=
    hD k c (k + 1) _ _ (fun n hn => by
      have hn0 : n = 0 := by omega
      subst hn0
      simp [skip, cons])
  have e3 : eta A φ c (k + 1) (skip 0 (cons γ0 fun _ => 1)) h
      = eta A φ c (k + 1) (skip 1 (cons γ0 fun _ => 1)) h := by
    have e0 := hCoc Hy k c hc (k + 1) le_rfl (cons γ0 fun _ => 1) h hh
    apply sub_eq_zero.mp
    simpa [delG, Finset.sum_range_succ, sub_eq_add_neg] using e0
  rw [e1, e3, e2]
  exact hC h hh T M hM hT _ (fun _ => hγ0)

end PositivityTheory.KB.WhittakerCocycle

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.WhittakerSmoothForms.ExtDerivCongrNhds
noncomputable section

open Set Filter Topology

namespace PositivityTheory.KB.WhittakerCocycle

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {Γ : Type} [Group Γ]

theorem cons_mul (a γ : Γ) (σ : ℕ → Γ) :
    (fun n => a * cons γ σ n) = cons (a * γ) (fun n => a * σ n) := by
  funext n; cases n <;> rfl

theorem extDeriv_congr_nhds {n : ℕ} {ω₁ ω₂ : V → V [⋀^Fin n]→L[ℝ] ℝ} {x : V} (h : ω₁ =ᶠ[𝓝 x] ω₂) :
    extDeriv ω₁ x = extDeriv ω₂ x := by
  simp only [extDeriv, h.fderiv_eq]

theorem kf_equiv {U : Set V} {A : Γ →* (V →L[ℝ] V)} {φ : V → ℝ} (hL : PLoc U A φ) (H : Hyp U A φ)
    {q : ℕ} (β : (ℕ → Γ) → V → V [⋀^Fin q]→L[ℝ] ℝ) (B : V →L[ℝ] V) (a : Γ)
    (hB : ∀ h ∈ U, B h ∈ U) (hψ : ∀ γ, ∀ h ∈ U, psi A φ γ (B h) = psi A φ (a * γ) h)
    (hβ : ∀ σ, ∀ h ∈ U, (β σ (B h)).compContinuousLinearMap B = β (fun n => a * σ n) h)
    (σ : ℕ → Γ) {h : V} (hh : h ∈ U) :
    (Kf A φ β σ (B h)).compContinuousLinearMap B = Kf A φ β (fun n => a * σ n) h := by
  obtain ⟨s, W, hW, -, hs⟩ := hL H (B h) (hB h hh)
  have hfin : Function.HasFiniteSupport
      (fun γ => psi A φ γ (B h) • β (cons γ σ) (B h)) := by
    refine s.finite_toSet.subset ?_
    intro γ hγ
    by_contra hγs
    apply hγ
    simp [hs γ hγs (B h) (mem_of_mem_nhds hW)]
  have key : ∀ γ, ContinuousAlternatingMap.compContinuousLinearMapCLM B
      (psi A φ γ (B h) • β (cons γ σ) (B h))
        = psi A φ (a * γ) h • β (cons (a * γ) (fun n => a * σ n)) h := by
    intro γ
    rw [map_smul, ← cons_mul, ← hβ _ h hh, ← hψ γ h hh]
    rfl
  calc (Kf A φ β σ (B h)).compContinuousLinearMap B
      = ContinuousAlternatingMap.compContinuousLinearMapCLM B
          (∑ᶠ γ, psi A φ γ (B h) • β (cons γ σ) (B h)) := rfl
    _ = ∑ᶠ γ, ContinuousAlternatingMap.compContinuousLinearMapCLM B
          (psi A φ γ (B h) • β (cons γ σ) (B h)) := map_finsum _ hfin
    _ = ∑ᶠ γ, psi A φ (a * γ) h • β (cons (a * γ) (fun n => a * σ n)) h := finsum_congr key
    _ = Kf A φ β (fun n => a * σ n) h :=
      finsum_comp_equiv (Equiv.mulLeft a)
        (f := fun γ => psi A φ γ h • β (cons γ (fun n => a * σ n)) h)

theorem pEquiv (U : Set V) (A : Γ →* (V →L[ℝ] V)) (φ : V → ℝ) (hL : PLoc U A φ)
    (hS : PSmooth U A φ) : PEquiv U A φ := by
  intro H k c hc B a hB hψ
  have hfd : ∀ x, fderiv ℝ B x = B := fun x => B.fderiv
  have he : ∀ j σ, ∀ h ∈ U, (eta A φ c j σ (B h)).compContinuousLinearMap B
      = eta A φ c j (fun n => a * σ n) h := by
    intro j
    induction j with
    | zero =>
      intro σ h hh
      rw [eta.eq_1, eta.eq_1]
      ext m
      simp [hc a (fun i => σ i)]
    | succ j ih =>
      intro σ h hh
      have hK : ∀ x ∈ U, (Kf A φ (eta A φ c j) σ (B x)).compContinuousLinearMap B
          = Kf A φ (eta A φ c j) (fun n => a * σ n) x :=
        fun x hx => kf_equiv hL H (eta A φ c j) B a hB hψ ih σ hx
      have hdiff : DifferentiableAt ℝ (Kf A φ (eta A φ c j) σ) (B h) :=
        ((hS H k c j σ).2.contDiffAt (H.isOpen.mem_nhds (hB h hh))).differentiableAt (by simp)
      have hpb := extDeriv_pullback (f := B) (x := h) (r := ⊤) hdiff B.contDiff.contDiffAt le_top
      simp only [hfd] at hpb
      rw [eta.eq_2, eta.eq_2, ← hpb]
      apply extDeriv_congr_nhds
      filter_upwards [H.isOpen.mem_nhds hh] with x hx
      exact hK x hx
  intro j σ h hh
  exact ⟨he j σ h hh, kf_equiv hL H (eta A φ c j) B a hB hψ (he j) σ hh⟩

end PositivityTheory.KB.WhittakerCocycle

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.WhittakerSmoothForms.EvEqLc
noncomputable section

namespace PositivityTheory.KB.WhittakerCocycle

theorem ev_eq_lc {G : Type} [Group G] {m : ℕ} (F : (Fin (m + 1) → G) → ℝ) (z : Chn G m) :
    ev (MonoidHom.id G) F 1 z =
      Finsupp.linearCombination ℝ (fun g : Fin m → G => F (Fin.partialProd g)) z := by
  unfold ev
  rw [Finsupp.linearCombination_apply]
  simp [smul_eq_mul]

private theorem partialProd_contractNth_mul_eq_succAbove {G : Type} [Group G] {k : ℕ} (g : Fin (k + 1) → G) (j l : Fin (k + 1)) :
    Fin.partialProd (Fin.contractNth j (· * ·) g) l = Fin.partialProd g (j.succ.succAbove l) := by
  induction l using Fin.induction with
  | zero =>
    rw [Fin.partialProd_zero, Fin.succAbove_of_castSucc_lt _ _ (by simp [Fin.lt_def])]
    simp
  | succ l ih =>
    rw [Fin.partialProd_succ, ih]
    rcases lt_trichotomy (l : ℕ) j with h | h | h
    · have e1 : j.succ.succAbove l.castSucc = l.castSucc.castSucc :=
        Fin.succAbove_of_castSucc_lt _ _ (by simp [Fin.lt_def]; omega)
      have e2 : j.succ.succAbove l.succ = l.castSucc.succ := by
        rw [Fin.succAbove_of_castSucc_lt _ _ (by simp [Fin.lt_def]; omega)]
        ext
        simp
      rw [e1, e2, Fin.partialProd_succ g l.castSucc, Fin.contractNth_apply_of_lt _ _ _ _ h]
    · have e1 : j.succ.succAbove l.castSucc = l.castSucc.castSucc :=
        Fin.succAbove_of_castSucc_lt _ _ (by simp [Fin.lt_def]; omega)
      have e2 : j.succ.succAbove l.succ = l.succ.succ :=
        Fin.succAbove_of_le_castSucc _ _ (by simp [Fin.le_def]; omega)
      have e3 : (l.succ.castSucc : Fin (k + 2)) = l.castSucc.succ := by
        ext
        simp
      rw [e1, e2, Fin.partialProd_succ g l.succ, e3, Fin.partialProd_succ g l.castSucc,
        Fin.contractNth_apply_of_eq _ _ _ _ h, mul_assoc]
    · have e1 : j.succ.succAbove l.castSucc = l.castSucc.succ :=
        Fin.succAbove_of_le_castSucc _ _ (by simp [Fin.le_def]; omega)
      have e2 : j.succ.succAbove l.succ = l.succ.succ :=
        Fin.succAbove_of_le_castSucc _ _ (by simp [Fin.le_def]; omega)
      have e3 : (l.succ.castSucc : Fin (k + 2)) = l.castSucc.succ := by
        ext
        simp
      rw [e1, e2, Fin.partialProd_succ g l.succ, e3, Fin.contractNth_apply_of_gt _ _ _ _ h]

theorem lc_dC {G : Type} [Group G] {k : ℕ} (b : (Fin (k + 1) → G) → ℝ)
    (hb : Inv (MonoidHom.id G) b) :
    Finsupp.linearCombination ℝ (fun g : Fin (k + 1) → G => dC b (Fin.partialProd g)) =
      (Finsupp.linearCombination ℝ (fun g : Fin k → G => b (Fin.partialProd g))).comp (bd G k) := by
  unfold Inv at hb
  refine Finsupp.lhom_ext (fun g r => ?_)
  rw [LinearMap.comp_apply]
  have hs : Finsupp.single g r = r • Finsupp.single g (1 : ℝ) := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [hs, map_smul, map_smul, map_smul]
  congr 1
  rw [Finsupp.linearCombination_single, one_smul]
  unfold bd
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finsupp.linearCombination_single, one_smul, map_add (f := _), map_sum]
  simp only [map_smul, map_zsmul, Finsupp.linearCombination_single, one_smul, smul_eq_mul, zsmul_eq_mul,
    Int.cast_pow, Int.cast_neg, Int.cast_one]
  unfold dC
  rw [Fin.sum_univ_succ]
  congr 1
  · simp only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero]
    have h0 := hb (g 0) (Fin.partialProd fun i => g i.succ)
    simp only [MonoidHom.id_apply, smul_eq_mul] at h0
    rw [← h0]
    congr 1
    funext l
    exact Fin.partialProd_succ' g l
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Fin.val_succ]
    simp only [one_mul]
    congr 2
    funext l
    exact (partialProd_contractNth_mul_eq_succAbove g j l).symm

theorem pEv {G : Type} [Group G] {k : ℕ} (b : (Fin (k + 1) → G) → ℝ) (hb : Inv (MonoidHom.id G) b)
    (z : Chn G (k + 1)) (hz : IsCyc z) : ev (MonoidHom.id G) (dC b) 1 z = 0 := by
  rw [ev_eq_lc, lc_dC b hb, LinearMap.comp_apply]
  unfold IsCyc at hz
  rw [hz, map_zero]

end PositivityTheory.KB.WhittakerCocycle

end
end

noncomputable section

open NumberField Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB

namespace WhittakerCocycle

variable {L : Type} [Field L] [NumberField L] {N : ℕ}

def actHom (L : Type) [Field L] [NumberField L] (N : ℕ) : Gm L N →* (HS L N →L[ℝ] HS L N) where
  toFun γ := actL (emb L N γ)
  map_one' := by
    refine ContinuousLinearMap.ext fun h => ?_
    rw [map_one, actL_one]
    rfl
  map_mul' a b := by
    refine ContinuousLinearMap.ext fun h => ?_
    rw [map_mul, actL_mul]
    rfl

theorem actHom_apply (γ : Gm L N) (h : HS L N) : actHom L N γ h = actL (emb L N γ) h := rfl

theorem actHom_inv (γ : Gm L N) (h : HS L N) : actHom L N γ⁻¹ h = actL (emb L N γ)⁻¹ h := by
  rw [actHom_apply, map_inv]

theorem hyp_of {Ht : Gp L N → ℝ} (P : PU L N Ht) : Hyp (Pos L N) (actHom L N) P.φ := by
  obtain ⟨hOpen, hConvex⟩ := pos_open_convex L N
  refine Hyp.mk hOpen hConvex (fun g _ hh => actL_pos (emb L N g) hh) P.smooth ?_ ?_
  ·
    have e : (fun γ : Gm L N => {h : Pos L N | P.φ (actHom L N γ⁻¹ h) ≠ 0}) =
        fun γ => {h : Pos L N | P.φ (actL (emb L N γ)⁻¹ h.1) ≠ 0} := by
      funext γ
      simp only [actHom_inv]
    rw [e]
    exact P.locFin
  · intro h hh
    simp only [actHom_inv]
    exact P.sum_one h hh

theorem intS_smul {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {q : ℕ} (s : ℝ) (ω : Form V q)
    (y : Fin (q + 1) → V) : intS (s • ω) y = s * intS ω y := by
  unfold intS
  simp only [Pi.smul_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  exact integral_const_mul _ _

theorem smul_comp {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {q : ℕ} (s : ℝ)
    (f : V [⋀^Fin q]→L[ℝ] ℝ) (T : V →L[ℝ] V) :
    (s • f).compContinuousLinearMap T = s • f.compContinuousLinearMap T := by
  ext v
  simp

theorem finv_of {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {q : ℕ} (s : ℝ)
    (ω : V → V [⋀^Fin q]→L[ℝ] ℝ) (T : V →L[ℝ] V) (h : V)
    (e : (ω (T h)).compContinuousLinearMap T = ω h) :
    ((s • ω) (T h)).compContinuousLinearMap T = (s • ω) h := by
  rw [Pi.smul_apply, Pi.smul_apply, smul_comp, e]

theorem intS_eq {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {q : ℕ} (ω : Form V q)
    (y : Fin (q + 1) → V) : intS ω y = intS' ω y := rfl

theorem fderiv_psi' {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {Γ : Type} [Group Γ]
    {U : Set V} {A : Γ →* (V →L[ℝ] V)} {φ : V → ℝ} (H : Hyp U A φ) (γ : Γ) {p : V} (hp : A γ⁻¹ p ∈ U) :
    fderiv ℝ (psi A φ γ) p = (fderiv ℝ φ (A γ⁻¹ p)).comp (A γ⁻¹) :=
  ((diffAt_of H.isOpen H.smooth hp).hasFDerivAt.comp p (A γ⁻¹).hasFDerivAt).fderiv

end WhittakerCocycle

open WhittakerCocycle

theorem sWhit_of (_hEv : SEv) (hSt : SStokes) : SWhit := by
  intro L _ _ N k Ht P hHt hHt0 c hc hdc
  have H := hyp_of P
  have hoc : Coc c := ⟨fun g y => by simpa using hc g y, fun y => by simpa [dC] using congrFun hdc y⟩
  have hL := pLoc (Pos L N) (actHom L N) P.φ
  have hSm := pSmooth _ _ _ hL
  have hCl := pClosed _ _ _ hSm
  have hD := pDep (actHom L N) P.φ
  have hH := pHom _ _ _ hL
  have hC := pCoc _ _ _ hH hSm hCl
  have hE := pEquiv _ _ _ hL hSm
  have hStk : Stk (Pos L N) := fun q ω hω y hy => hSt (HS L N) (Pos L N) H.isOpen H.convex q ω hω y hy
  obtain ⟨s, hs, b, hbi, hcb⟩ := pComp hH hSm hD hC hE H hStk k c hoc (one L N).1 (one L N).2
  have hs1 : ‖s‖ = 1 := by rcases hs with rfl | rfl <;> simp
  have hη : ContDiffOn ℝ (⊤ : ℕ∞) (eta (actHom L N) P.φ c (k + 1) fun _ => 1) (Pos L N) :=
    (hSm H k c (k + 1) _).1
  refine ⟨s • eta (actHom L N) P.φ c (k + 1) (fun _ => 1), ⟨hη.continuousOn.const_smul s, ?_⟩, ?_, ?_, ?_, ?_⟩
  ·
    funext y
    show dC (intS (s • eta (actHom L N) P.φ c (k + 1) fun _ => 1)) (fun j => (y j).1) = 0
    have hcd : ContDiffOn ℝ 1 (s • eta (actHom L N) P.φ c (k + 1) fun _ => 1) (Pos L N) :=
      (hη.const_smul s).of_le (by exact_mod_cast le_top)
    rw [hSt (HS L N) (Pos L N) H.isOpen H.convex (k + 1) (s • eta (actHom L N) P.φ c (k + 1) fun _ => 1)
      hcd _ (fun j => (y j).2)]
    have e : intS (extDeriv (s • eta (actHom L N) P.φ c (k + 1) fun _ => 1)) (fun j => (y j).1) =
        intS' (fun _ => 0) (fun j => (y j).1) :=
      intS'_congr H.convex (fun x hx => by
        show extDeriv (s • eta (actHom L N) P.φ c (k + 1) fun _ => 1) x = 0
        rw [extDeriv_smul, hCl H k c (k + 1) _ x hx, smul_zero]) (fun j => (y j).2)
    rw [e]
    simp [intS']
  ·
    intro γ h hh
    have e1 := (hE H k c hoc.inv (actHom L N γ) γ⁻¹ (fun h hh => H.mapsTo γ h hh) (fun γ' h _ => by
      simp only [WhittakerCocycle.psi, _root_.mul_inv_rev, inv_inv, map_mul, mul_apply_eq_comp]) (k + 1)
      (fun _ => 1) h hh).1
    have e2 := eta_top H hD hC c hoc (fun _ => γ⁻¹ * 1) (fun _ => 1) h hh
    exact finv_of s _ (actHom L N γ) h (e1.trans e2)
  ·
    intro s' hs' h hh
    obtain ⟨r, hr, hrh⟩ := actL_scal (N := N) s' hs'
    have e1 := (hE H k c hoc.inv (actL (scal L N s')) 1 (fun h hh => actL_pos _ hh) (fun γ h hh => by
      simp only [WhittakerCocycle.psi, one_mul]
      rw [hrh, map_smul]
      exact P.homog r hr _ (H.mapsTo _ _ hh)) (k + 1) (fun _ => 1) h hh).1
    simp only [mul_one] at e1
    exact finv_of s _ (actL (scal L N s')) h e1
  ·
    intro z hz
    have hbInv : Inv (MonoidHom.id (Gm L N)) b := fun g y => by simpa using hbi g y
    have key : ev (MonoidHom.id (Gm L N)) c 1 z =
        ev (MonoidHom.id (Gm L N)) (fun g => s * intS' (eta (actHom L N) P.φ c (k + 1) fun _ => 1)
          (fun l => actHom L N (g l) (one L N).1)) 1 z + ev (MonoidHom.id (Gm L N)) (dC b) 1 z := by
      unfold ev
      rw [← Finsupp.sum_add]
      refine Finsupp.sum_congr fun g _ => ?_
      rw [hcb, mul_add]
      rfl
    rw [key, pEv b hbInv z hz, add_zero]
    unfold ev
    refine Finsupp.sum_congr fun g _ => ?_
    congr 1
    show intS (s • eta (actHom L N) P.φ c (k + 1) fun _ => 1) _ = _
    rw [intS_smul]
    beta_reduce
    rw [intS_eq]
    congr 2
    simp only [MonoidHom.id_apply, smul_eq_mul, mul_one, actHom_apply]
    rfl
  ·
    obtain ⟨Cφ, hCφ⟩ := P.deriv
    obtain ⟨C0, hC0⟩ := pBound _ _ _ hL hSm hCl hC hD H _ P.overlap (fun γ h hh hm hh' => ⟨h, hh, by
      have e : (emb L N γ)⁻¹ • h = ⟨actHom L N γ⁻¹ h, hm⟩ := Subtype.ext (actHom_inv γ h).symm
      rw [e]
      exact hh'⟩) P.bdd k c hoc
    refine ⟨C0 * max Cφ 0 ^ (k + 1), fun x => ?_⟩
    have hx : actL x (one L N).1 ∈ Pos L N := actL_pos x (one L N).2
    have hM : 0 ≤ max Cφ 0 * Ht x := mul_nonneg (le_max_right _ _) (hHt0 x)
    have hder : ∀ γ, ‖(fderiv ℝ (WhittakerCocycle.psi (actHom L N) P.φ γ) (actL x (one L N).1)).comp (actL x)‖ ≤
        max Cφ 0 * Ht x := by
      intro γ
      have hBp : actHom L N γ⁻¹ (actL x (one L N).1) ∈ Pos L N := H.mapsTo _ _ hx
      rw [fderiv_psi' H γ hBp, ContinuousLinearMap.comp_assoc]
      have e1 : actHom L N γ⁻¹ (actL x (one L N).1) = actL (emb L N γ⁻¹ * x) (one L N).1 := by
        rw [actL_mul]
        rfl
      have e2 : (actHom L N γ⁻¹).comp (actL x) = actL (emb L N γ⁻¹ * x) := by
        refine ContinuousLinearMap.ext fun v => ?_
        rw [actL_mul]
        rfl
      rw [e1, e2]
      calc _ ≤ Cφ * Ht (emb L N γ⁻¹ * x) := hCφ _
        _ = Cφ * Ht x := by rw [hHt]
        _ ≤ max Cφ 0 * Ht x := mul_le_mul_of_nonneg_right (le_max_left _ _) (hHt0 x)
    have hb := hC0 _ hx (actL x) _ hM hder
    calc ‖fr (s • eta (actHom L N) P.φ c (k + 1) fun _ => 1) x‖
        = ‖((eta (actHom L N) P.φ c (k + 1) fun _ => 1) (actL x (one L N).1)).compContinuousLinearMap
            (actL x)‖ := by
          unfold fr
          rw [Pi.smul_apply, smul_comp, norm_smul, hs1, one_mul]
      _ ≤ C0 * (max Cφ 0 * Ht x) ^ (k + 1) := hb
      _ = C0 * max Cφ 0 ^ (k + 1) * Ht x ^ (k + 1) := by ring

end PositivityTheory.KB

end
