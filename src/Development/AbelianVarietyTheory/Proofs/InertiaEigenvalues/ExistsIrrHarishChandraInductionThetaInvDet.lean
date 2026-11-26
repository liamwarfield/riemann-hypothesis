module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VecPairApply
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisTorsionFreeCompleteFrobeniusProperties
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinOEModPrimeLaurentField
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConductorExponentAtPlaces
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FirstHalfLocalCohomologyVanishingOfLocalDualityT
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIrrHarishChandraInductionThetaInvDet
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIrrHarishChandraInductionThetaInvDet
open GlobalTheory.GLq GlobalTheory.MirAvg Polynomial

noncomputable section

namespace GlobalTheory.GLq.HCFrobWeight

open scoped Classical

section Reg

variable {H : Type} [Group H] [Fintype H]

theorem sum_irr_coeff (h : H) :
    ∑ σ ∈ (irr_finite_and_finsum_zOf_eq_one H).1.toFinset, (zOf σ).coeff h = if h = 1 then 1 else 0 := by
  obtain ⟨hfin, hsum⟩ := irr_finite_and_finsum_zOf_eq_one H
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at hsum
  have e := congrArg (fun z : MonoidAlgebra ℂ H => z.coeff h) hsum
  simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply] at e
  rw [e, MonoidAlgebra.one_def, MonoidAlgebra.coeff_single, Finsupp.single_apply]
  by_cases hh : h = 1
  · simp [hh]
  · simp [hh, Ne.symm hh]

theorem exists_irr_sum_ne_zero (F : H → ℂ) (hF : F 1 ≠ 0) :
    ∃ σ : H → ℂ, IsIrr σ ∧ ∑ h, F h * σ h⁻¹ ≠ 0 := by
  by_contra hc
  push_neg at hc
  apply hF
  set s := (irr_finite_and_finsum_zOf_eq_one H).1.toFinset with hs
  have h0 : ∑ σ ∈ s, σ 1 / (Fintype.card H : ℂ) * ∑ h, F h * σ h⁻¹ = 0 := by
    refine Finset.sum_eq_zero fun σ hσ => ?_
    rw [hc σ (by simpa [hs] using hσ), mul_zero]
  rw [← h0]
  have e : ∑ σ ∈ s, σ 1 / (Fintype.card H : ℂ) * ∑ h, F h * σ h⁻¹ =
      ∑ h, F h * ∑ σ ∈ s, (zOf σ).coeff h := by
    simp_rw [Finset.mul_sum, ZSumOne.zOf_coeff]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun σ _ => ?_
    ring
  rw [e, hs]
  simp_rw [sum_irr_coeff]
  simp

end Reg

variable {g : ℕ} [Fact g.Prime]

theorem isClass_of_isIrr {n : ℕ} {ψ : Gn g n → ℂ} (hψ : IsIrr ψ) : IsClass ψ := by
  obtain ⟨V, _, hV⟩ := hψ
  intro x y
  rw [← hV, ← hV]
  exact FDRep.char_conj V x y

theorem ip_hc_eq_left (a b n : ℕ) (hn : n = a + b) (χ : Gn g n → ℂ) (hχ : IsClass χ) (α : Gn g a → ℂ)
    (β : Gn g b → ℂ) :
    ip χ (hc a b α β n) = (Fintype.card (Gn g a × Gn g b) : ℂ)⁻¹ *
      ∑ h : Gn g a, (∑ y : Gn g b, res a b χ h y * β y⁻¹) * α h⁻¹ := by
  rw [hc, FrobRecHC.hcT_adjoint g a b n hn χ _ hχ]
  unfold ip
  rw [Fintype.sum_prod_type]
  congr 1
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [Prod.fst_inv, Prod.snd_inv]
  ring

theorem ip_hc_eq_right (a b n : ℕ) (hn : n = a + b) (χ : Gn g n → ℂ) (hχ : IsClass χ) (α : Gn g a → ℂ)
    (β : Gn g b → ℂ) :
    ip χ (hc a b α β n) = (Fintype.card (Gn g a × Gn g b) : ℂ)⁻¹ *
      ∑ y : Gn g b, (∑ h : Gn g a, res a b χ h y * α h⁻¹) * β y⁻¹ := by
  rw [hc, FrobRecHC.hcT_adjoint g a b n hn χ _ hχ]
  unfold ip
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun h _ => ?_
  simp only [Prod.fst_inv, Prod.snd_inv]
  ring

theorem thetaInv_det_inv (θ : (ZMod g)ˣ →* ℂˣ) (y : Gn g 1) :
    ((θ⁻¹ (Matrix.GeneralLinearGroup.det y⁻¹) : ℂˣ) : ℂ) = ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) := by
  simp [map_inv]

end GlobalTheory.GLq.HCFrobWeight

namespace GlobalTheory.GLq.HCFrobWeight

open scoped Classical

theorem exists_irr_hc_thetaInv : ∀ (g : ℕ) [Fact g.Prime] (n : ℕ) (ψ : Gn g (n + 1) → ℂ), IsIrr ψ → ∀ θ : (ZMod g)ˣ →* ℂˣ,
    (∑ x : Gn g 1, ((θ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * res n 1 ψ 1 x ≠ 0 →
      ∃ σ : Gn g n → ℂ, IsIrr σ ∧
        ip ψ (hc n 1 σ (fun y : Gn g 1 => ((θ⁻¹ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) (n + 1)) ≠ 0) ∧
    (∑ x : Gn g 1, ((θ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * res 1 n ψ x 1 ≠ 0 →
      ∃ σ : Gn g n → ℂ, IsIrr σ ∧
        ip ψ (hc 1 n (fun y : Gn g 1 => ((θ⁻¹ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) σ (n + 1)) ≠ 0) := by
  intro g _ n ψ hψ θ
  have hcl := isClass_of_isIrr hψ
  constructor
  · intro hS
    obtain ⟨σ, hσ, hne⟩ := exists_irr_sum_ne_zero
      (fun h : Gn g n => ∑ y : Gn g 1, res n 1 ψ h y * ((θ⁻¹ (Matrix.GeneralLinearGroup.det y⁻¹) : ℂˣ) : ℂ))
      (by simp_rw [thetaInv_det_inv]; simpa [mul_comm] using hS)
    refine ⟨σ, hσ, ?_⟩
    rw [ip_hc_eq_left n 1 (n + 1) rfl ψ hcl]
    exact mul_ne_zero (inv_ne_zero (Nat.cast_ne_zero.2 Fintype.card_ne_zero)) hne
  · intro hS
    obtain ⟨σ, hσ, hne⟩ := exists_irr_sum_ne_zero
      (fun y : Gn g n => ∑ h : Gn g 1, res 1 n ψ h y * ((θ⁻¹ (Matrix.GeneralLinearGroup.det h⁻¹) : ℂˣ) : ℂ))
      (by simp_rw [thetaInv_det_inv]; simpa [mul_comm] using hS)
    refine ⟨σ, hσ, ?_⟩
    rw [ip_hc_eq_right 1 n (n + 1) (by omega) ψ hcl]
    exact mul_ne_zero (inv_ne_zero (Nat.cast_ne_zero.2 Fintype.card_ne_zero)) hne

end GlobalTheory.GLq.HCFrobWeight
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIrrHarishChandraInductionThetaInvDetStatement
open GlobalTheory.GLq GlobalTheory.MirAvg Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_irr_harishChandraInduction_thetaInv_det : ∀ (g : ℕ) [Fact g.Prime] (n : ℕ) (ψ : Gn g (n + 1) → ℂ), IsIrr ψ → ∀ θ : (ZMod g)ˣ →* ℂˣ,
    (∑ x : Gn g 1, ((θ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * res n 1 ψ 1 x ≠ 0 →
      ∃ σ : Gn g n → ℂ, IsIrr σ ∧
        ip ψ (hc n 1 σ (fun y : Gn g 1 => ((θ⁻¹ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) (n + 1)) ≠ 0) ∧
    (∑ x : Gn g 1, ((θ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * res 1 n ψ x 1 ≠ 0 →
      ∃ σ : Gn g n → ℂ, IsIrr σ ∧
        ip ψ (hc 1 n (fun y : Gn g 1 => ((θ⁻¹ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) σ (n + 1)) ≠ 0) := by
  first | exact @GlobalTheory.GLq.HCFrobWeight.exists_irr_hc_thetaInv | exact GlobalTheory.GLq.HCFrobWeight.exists_irr_hc_thetaInv | (intros; apply GlobalTheory.GLq.HCFrobWeight.exists_irr_hc_thetaInv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantTransitionMatrixCover
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantTransitionMatrixCover
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section
namespace GlobalTheory.CovTrans

theorem zOm_smul_eq_q {l : ℕ} [Fact l.Prime] {X : Type} [AddCommGroup X] [Module (Om l) X] [Module ℚ_[l] X]
    [IsScalarTower ℚ_[l] (Om l) X] (c : ℤ_[l]) (x : X) : zOm l c • x = ((c : ℚ_[l])) • x := by
  show (algebraMap ℚ_[l] (Om l) (algebraMap ℤ_[l] ℚ_[l] c)) • x = _
  rw [algebraMap_smul]
  rfl

theorem coord_inj {l : ℕ} [Fact l.Prime] {X : Type} [AddCommGroup X] [Module (Om l) X] [Module ℚ_[l] X]
    [IsScalarTower ℚ_[l] (Om l) X] {n : ℕ} {v : Fin n → X} (hv : LinearIndependent ℚ_[l] v) {u u' : Fin n → ℤ_[l]}
    (h : ∑ i, zOm l (u i) • v i = ∑ i, zOm l (u' i) • v i) : u = u' := by
  simp only [zOm_smul_eq_q] at h
  have := Fintype.linearIndependent_iff.mp hv (fun i => (u i : ℚ_[l]) - u' i)
    (by simp only [sub_smul, Finset.sum_sub_distrib, h, sub_self])
  funext i
  have h2 := this i
  rw [sub_eq_zero] at h2
  exact Subtype.ext h2

theorem dsum {l : ℕ} [Fact l.Prime] {X : Type} [AddCommGroup X] [Module (Om l) X] {p q : ℕ} (α : Fin p → ℤ_[l])
    (β : Fin p → Fin q → ℤ_[l]) (w : Fin q → X) :
    ∑ s, zOm l (α s) • ∑ i, zOm l (β s i) • w i = ∑ i, zOm l (∑ s, β s i * α s) • w i := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finset.smul_sum, smul_smul, map_sum, map_mul, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun s _ => ?_
  rw [mul_comm]

theorem transition : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (a : ℕ) (r : Γ →* GL (Fin a) (Om l)) (d : ℕ) (b : Fin d → Matrix (Fin a) (Fin a) (Om l)), LinearIndependent ℚ_[l] b → ∀ (m m' : ℕ) (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (ρs' : Fin m' → (Γ →* GL (Fin a) (Om l))) (ι : Fin m → Fin m'), (∀ k, ρs' (ι k) = ρs k) → ∀ (t : Fin m → Finset (Matrix (Fin a) (Fin a) (Om l))) (t' : Fin m' → Finset (Matrix (Fin a) (Fin a) (Om l))), (∀ k, t' (ι k) = t k) → ∀ (M M' : ℕ), M ≤ M' → ∀ (d₁ d₂ : ℕ) (ρ₁ : Γ →* GL (Fin d₁) ℤ_[l]) (ρ₂ : Γ →* GL (Fin d₂) ℤ_[l]) (bb₁ : Fin d₁ → Fin m → Matrix (Fin a) (Fin a) (Om l)) (bb₂ : Fin d₂ → Fin m' → Matrix (Fin a) (Fin a) (Om l)) (e₁ : Fin d₁ → ℤ_[l]) (e₂ : Fin d₂ → ℤ_[l]), LinearIndependent ℚ_[l] bb₁ → (∀ k, Reads ρ₁ (ρs k) (fun s => bb₁ s k) e₁) → (∀ k, Reads ρ₂ (ρs' k) (fun s => bb₂ s k) e₂) → (∀ s, bb₂ s ∈ GlobalTheory.TraceConjugationCover.latT ρs' t' M') → (∀ x ∈ GlobalTheory.TraceConjugationCover.latT ρs t M, ∃ z : Fin d₁ → ℤ_[l], x = ∑ s, zOm l (z s) • bb₁ s) → ∀ (P₁ : Matrix (Fin d) (Fin d₁) ℤ_[l]) (P₂ : Matrix (Fin d) (Fin d₂) ℤ_[l]) (n N₁ N₂ : ℕ), n ≤ N₁ → n ≤ N₂ → GlobalTheory.TraceConjugationCover.Carries r b ρs t M bb₁ P₁ N₁ → GlobalTheory.TraceConjugationCover.Carries r b ρs' t' M' bb₂ P₂ N₂ → ∃ f : Matrix (Fin d₁) (Fin d₂) ℤ_[l], (∀ g, f * ((ρ₂ g : GL (Fin d₂) ℤ_[l]) : Matrix (Fin d₂) (Fin d₂) ℤ_[l]) = ((ρ₁ g : GL (Fin d₁) ℤ_[l]) : Matrix (Fin d₁) (Fin d₁) ℤ_[l]) * f) ∧ ∀ i j, (l : ℤ_[l]) ^ n ∣ (P₁ * f - P₂) i j := by
  intro l _ Γ _ a r d b hb m m' ρs ρs' ι hι t t' ht M M' hM d₁ d₂ ρ₁ ρ₂ bb₁ bb₂ e₁ e₂ hbb₁ hR₁ hR₂ hmem₂ hcoord
    P₁ P₂ n N₁ N₂ hn₁ hn₂ hC₁ hC₂
  have hsm : ∀ {k : Fin m} (c : Om l) (w : Matrix (Fin a) (Fin a) (Om l)),
      (Pi.single k (c • w) : Fin m → Matrix (Fin a) (Fin a) (Om l)) = c • Pi.single k w := by
    intro k c w
    funext k₀
    by_cases h : k₀ = k
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  have hπL : ∀ y ∈ GlobalTheory.TraceConjugationCover.latL t' M', y ∘ ι ∈ GlobalTheory.TraceConjugationCover.latL t M := by
    intro y hy
    have hle : Submodule.map (LinearMap.funLeft ℤ_[l] (Matrix (Fin a) (Fin a) (Om l)) ι) (GlobalTheory.TraceConjugationCover.latL t' M') ≤
        GlobalTheory.TraceConjugationCover.latL t M := by
      rw [GlobalTheory.TraceConjugationCover.latL, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      simp only [Set.mem_iUnion, Set.mem_image] at hx
      obtain ⟨k', v, hv, rfl⟩ := hx
      change (Pi.single k' ((l : Om l) ^ M' • v)) ∘ ι ∈ _
      rw [← Finset.univ_sum_single (Pi.single k' ((l : Om l) ^ M' • v) ∘ ι)]
      refine Submodule.sum_mem _ fun k _ => ?_
      by_cases hk : ι k = k'
      · subst hk
        simp only [Function.comp_apply, Pi.single_eq_same]
        have hv' : v ∈ t k := by rw [← ht k]; exact hv
        have e1 : ((l : Om l) ^ M' • v) = zOm l ((l : ℤ_[l]) ^ (M' - M)) • ((l : Om l) ^ M • v) := by
          rw [map_pow, map_natCast, smul_smul, ← pow_add, Nat.sub_add_cancel hM]
        rw [e1, hsm, GlobalTheory.TraceConjugationCover.zOm_smul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_iUnion.mpr ⟨k, v, hv', rfl⟩))
      · simp [Pi.single_eq_of_ne hk]
    exact hle ⟨y, hy, rfl⟩
  have hdec : ∀ j, ∃ (F : Γ →₀ ℤ_[l]) (y : Fin m' → Matrix (Fin a) (Fin a) (Om l)), y ∈ GlobalTheory.TraceConjugationCover.latL t' M' ∧
      bb₂ j = (F.sum fun g c => zOm l c • GlobalTheory.TraceConjugationCover.tup ρs' g) + y := by
    intro j
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp (hmem₂ j)
    obtain ⟨F, hF⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).mp hx
    refine ⟨F, y, hy, ?_⟩
    rw [← hxy, ← hF]
    simp only [GlobalTheory.TraceConjugationCover.zOm_smul]
  choose F y hy hbb using hdec
  have hπF : ∀ (G : Γ →₀ ℤ_[l]), (G.sum fun g c => zOm l c • GlobalTheory.TraceConjugationCover.tup ρs' g) ∘ ι =
      G.sum fun g c => zOm l c • GlobalTheory.TraceConjugationCover.tup ρs g := by
    intro G
    funext k
    simp [Finsupp.sum, Finset.sum_apply, GlobalTheory.TraceConjugationCover.tup, hι]
  have hπbb : ∀ j, bb₂ j ∘ ι = ((F j).sum fun g c => zOm l c • GlobalTheory.TraceConjugationCover.tup ρs g) + y j ∘ ι := by
    intro j
    rw [hbb j, ← hπF]
    rfl
  have hmemT : ∀ j, bb₂ j ∘ ι ∈ GlobalTheory.TraceConjugationCover.latT ρs t M := by
    intro j
    rw [hπbb j]
    refine Submodule.add_mem_sup ?_ (hπL _ (hy j))
    simp only [GlobalTheory.TraceConjugationCover.zOm_smul]
    exact Submodule.finsuppSum_mem _ _ _ _ (fun g _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩))
  choose z hz using fun j => hcoord _ (hmemT j)
  have hcol : ∀ j k, bb₂ j (ι k) = ∑ s, zOm l (z j s) • bb₁ s k := by
    intro j k
    have := congrFun (hz j) k
    simpa [Finset.sum_apply] using this
  refine ⟨Matrix.of fun s j => z j s, ?_, ?_⟩
  · intro g
    ext i j
    have hA : ∀ k, (ρs k g).val * bb₂ j (ι k) =
        ∑ i, zOm l (((ρ₁ g).val * Matrix.of fun s j => z j s) i j) • bb₁ i k := by
      intro k
      have e := fun s => (hR₁ k).equi g s
      try simp only at e
      rw [hcol, Finset.mul_sum]
      simp_rw [Matrix.mul_smul, e]
      rw [dsum]
      simp [Matrix.mul_apply]
    have hB : ∀ k, (ρs k g).val * bb₂ j (ι k) =
        ∑ i, zOm l (((Matrix.of fun s j => z j s) * (ρ₂ g).val) i j) • bb₁ i k := by
      intro k
      rw [← hι k]
      have e := (hR₂ (ι k)).equi g j
      try simp only at e
      rw [e]
      simp_rw [hcol]
      rw [dsum]
      simp [Matrix.mul_apply]
    have key : (fun i => ((Matrix.of fun s j => z j s) * (ρ₂ g).val) i j) =
        fun i => ((ρ₁ g).val * Matrix.of fun s j => z j s) i j := by
      apply GlobalTheory.CovTrans.coord_inj hbb₁
      funext k
      simp only [Finset.sum_apply, Pi.smul_apply]
      rw [← hB k, hA k]
    exact congrArg _ (congrFun key i)
  · intro i j
    have hsingle : ∑ s, zOm l ((Pi.single j 1 : Fin d₂ → ℤ_[l]) s) • bb₂ s = bb₂ j := by
      simp [Pi.single_apply]
    obtain ⟨w₂, hw₂⟩ := hC₂ (Pi.single j 1) (F j) (y j) (hy j) (by rw [hsingle]; exact hbb j)
    obtain ⟨w₁, hw₁⟩ := hC₁ (fun s => z j s) (F j) (y j ∘ ι) (hπL _ (hy j)) (by rw [← hz j, hπbb j])
    have hP₂ : P₂ *ᵥ Pi.single j 1 = fun i => P₂ i j := by
      funext i; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    have hP₁ : P₁ *ᵥ (fun s => z j s) = fun i => (P₁ * Matrix.of fun s j => z j s) i j := by
      funext i; simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
    rw [hP₂] at hw₂
    rw [hP₁] at hw₁
    have key : (fun i => (P₁ * Matrix.of fun s j => z j s) i j - P₂ i j) =
        fun i => (l : ℤ_[l]) ^ n * ((l : ℤ_[l]) ^ (N₁ - n) * w₁ i - (l : ℤ_[l]) ^ (N₂ - n) * w₂ i) := by
      apply GlobalTheory.CovTrans.coord_inj hb
      have hs : ∑ i, zOm l ((P₁ * Matrix.of fun s j => z j s) i j - P₂ i j) • b i =
          ∑ i, zOm l ((P₁ * Matrix.of fun s j => z j s) i j) • b i - ∑ i, zOm l (P₂ i j) • b i := by
        simp only [map_sub, sub_smul, Finset.sum_sub_distrib]
      rw [hs, hw₁, hw₂, add_sub_add_left_eq_sub]
      have e1 : (l : Om l) ^ N₁ = (l : Om l) ^ n * (l : Om l) ^ (N₁ - n) := by rw [← pow_add, Nat.add_sub_cancel' hn₁]
      have e2 : (l : Om l) ^ N₂ = (l : Om l) ^ n * (l : Om l) ^ (N₂ - n) := by rw [← pow_add, Nat.add_sub_cancel' hn₂]
      rw [e1, e2]
      simp only [Finset.smul_sum, smul_smul, map_mul, map_sub, map_pow, map_natCast, mul_sub, sub_smul,
        Finset.sum_sub_distrib, mul_assoc]
    have := congrFun key i
    rw [Matrix.sub_apply, this]
    exact Dvd.intro _ rfl

end GlobalTheory.CovTrans
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantTransitionMatrixCoverStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_equivariant_transition_matrix_cover : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (a : ℕ) (r : Γ →* GL (Fin a) (Om l)) (d : ℕ) (b : Fin d → Matrix (Fin a) (Fin a) (Om l)), LinearIndependent ℚ_[l] b → ∀ (m m' : ℕ) (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (ρs' : Fin m' → (Γ →* GL (Fin a) (Om l))) (ι : Fin m → Fin m'), (∀ k, ρs' (ι k) = ρs k) → ∀ (t : Fin m → Finset (Matrix (Fin a) (Fin a) (Om l))) (t' : Fin m' → Finset (Matrix (Fin a) (Fin a) (Om l))), (∀ k, t' (ι k) = t k) → ∀ (M M' : ℕ), M ≤ M' → ∀ (d₁ d₂ : ℕ) (ρ₁ : Γ →* GL (Fin d₁) ℤ_[l]) (ρ₂ : Γ →* GL (Fin d₂) ℤ_[l]) (bb₁ : Fin d₁ → Fin m → Matrix (Fin a) (Fin a) (Om l)) (bb₂ : Fin d₂ → Fin m' → Matrix (Fin a) (Fin a) (Om l)) (e₁ : Fin d₁ → ℤ_[l]) (e₂ : Fin d₂ → ℤ_[l]), LinearIndependent ℚ_[l] bb₁ → (∀ k, Reads ρ₁ (ρs k) (fun s => bb₁ s k) e₁) → (∀ k, Reads ρ₂ (ρs' k) (fun s => bb₂ s k) e₂) → (∀ s, bb₂ s ∈ GlobalTheory.TraceConjugationCover.latT ρs' t' M') → (∀ x ∈ GlobalTheory.TraceConjugationCover.latT ρs t M, ∃ z : Fin d₁ → ℤ_[l], x = ∑ s, zOm l (z s) • bb₁ s) → ∀ (P₁ : Matrix (Fin d) (Fin d₁) ℤ_[l]) (P₂ : Matrix (Fin d) (Fin d₂) ℤ_[l]) (n N₁ N₂ : ℕ), n ≤ N₁ → n ≤ N₂ → GlobalTheory.TraceConjugationCover.Carries r b ρs t M bb₁ P₁ N₁ → GlobalTheory.TraceConjugationCover.Carries r b ρs' t' M' bb₂ P₂ N₂ → ∃ f : Matrix (Fin d₁) (Fin d₂) ℤ_[l], (∀ g, f * ((ρ₂ g : GL (Fin d₂) ℤ_[l]) : Matrix (Fin d₂) (Fin d₂) ℤ_[l]) = ((ρ₁ g : GL (Fin d₁) ℤ_[l]) : Matrix (Fin d₁) (Fin d₁) ℤ_[l]) * f) ∧ ∀ i j, (l : ℤ_[l]) ^ n ∣ (P₁ * f - P₂) i j := by
  first | (exact @GlobalTheory.CovTrans.transition) | (exact GlobalTheory.CovTrans.transition) | (intros; apply GlobalTheory.CovTrans.transition  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemRangeOfFrob
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.FrobDenom

section Abstract

variable {O RA RW M : Type} [CommRing O] [CommRing RA] [CommRing RW] [Algebra O RA] [Algebra O RW]
  [AddCommGroup M] [Module O M]

theorem repr_incl {κ : Type} (tb : Module.Basis κ O M) (incl : RA →ₐ[O] RW) (u : RA ⊗[O] M) (k : κ) :
    (Algebra.TensorProduct.basis RW tb).repr
        (TensorProduct.map incl.toLinearMap (LinearMap.id : M →ₗ[O] M) u) k =
      incl ((Algebra.TensorProduct.basis RA tb).repr u k) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul r t => simp [Algebra.TensorProduct.basis_repr_tmul]
  | add a b ha hb => simp only [map_add (f := _), Finsupp.add_apply, ha, hb]

theorem map_smul_left (f : RW →ₐ[O] RW) (r : RW) (z : RW ⊗[O] M) :
    TensorProduct.map f.toLinearMap (LinearMap.id : M →ₗ[O] M) (r • z) =
      f r • TensorProduct.map f.toLinearMap (LinearMap.id : M →ₗ[O] M) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x t => simp [TensorProduct.smul_tmul']
  | add a b ha hb => rw [smul_add, map_add (f := _), ha, hb, map_add (f := _), smul_add]

theorem mem_range_of_frob {κ : Type} [Fintype κ] (tb : Module.Basis κ O M) (incl : RA →ₐ[O] RW)
    (φ : RW →ₐ[O] RW)
    (hA : ∀ (p q : Type) [Fintype p] [Fintype q] (Z : Matrix p q RW) (S : Matrix p p RA)
      (S' : Matrix q q RA) (Y : Matrix p q RA),
      Z.map φ = S.map incl * Z * S'.map incl + Y.map incl → ∀ a b, Z a b ∈ Set.range incl)
    (r : RA) (z w : RW ⊗[O] M)
    (hw : w ∈ LinearMap.range (TensorProduct.map incl.toLinearMap (LinearMap.id : M →ₗ[O] M)))
    (h : TensorProduct.map φ.toLinearMap (LinearMap.id : M →ₗ[O] M) z = incl r • z + w) :
    z ∈ LinearMap.range (TensorProduct.map incl.toLinearMap (LinearMap.id : M →ₗ[O] M)) := by
  classical
  obtain ⟨w', rfl⟩ := hw
  set tt := Algebra.TensorProduct.basis RW tb with htt
  set ta := Algebra.TensorProduct.basis RA tb with hta
  have key := hA κ Unit (Matrix.of fun k _ => tt.repr z k) (Matrix.diagonal fun _ => r) 1
    (Matrix.of fun k _ => ta.repr w' k) (by
      ext k u
      have h1 := congrArg (fun x => tt.repr x k) h
      simp only [map_add (f := _), map_smul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at h1
      rw [htt, GlobalTheory.Sandwich.repr_phi, repr_incl, ← htt, ← hta] at h1
      rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, Matrix.diagonal_map (map_zero _)]
      simp only [Matrix.map_apply, Matrix.of_apply, Matrix.add_apply, Matrix.diagonal_mul]
      exact h1)
  choose c hc using fun k => key k ()
  refine ⟨∑ k, c k ⊗ₜ[O] tb k, ?_⟩
  conv_rhs => rw [← tt.sum_repr z]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have := hc k
  simp only [Matrix.of_apply] at this
  rw [← this, htt, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul']
  simp

end Abstract

section Alg

variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A]

theorem φ_prod (φ : A →ₐ[O] A) (X Q : A) (hXQ : φ X = X * Q) (m : ℕ) :
    φ (∏ j ∈ Finset.range (m + 1), (φ ^ j) X) =
      (∏ j ∈ Finset.range (m + 1), (φ ^ j) X) * ∏ j ∈ Finset.range (m + 1), (φ ^ j) Q := by
  rw [map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← AlgHom.mul_apply, ← pow_succ', pow_succ, AlgHom.mul_apply, hXQ, map_mul]

theorem multiset_dvd (f : ℕ → A) (m : ℕ) (J : Multiset ℕ) (hJ : ∀ j ∈ J, j ≤ m) :
    (J.map f).prod ∣ (∏ j ∈ Finset.range (m + 1), f j) ^ Multiset.card J := by
  induction J using Multiset.induction_on with
  | empty => simp
  | cons j J ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ, mul_comm]
    refine mul_dvd_mul (ih fun i hi => hJ i (Multiset.mem_cons_of_mem hi)) ?_
    exact Finset.dvd_prod_of_mem f
      (Finset.mem_range.2 (Nat.lt_succ_of_le (hJ j (Multiset.mem_cons_self j J))))

theorem X_dvd (φ : A →ₐ[O] A) (X : A) (m : ℕ) : X ∣ ∏ j ∈ Finset.range (m + 1), (φ ^ j) X := by
  have := Finset.dvd_prod_of_mem (fun j => (φ ^ j) X) (Finset.mem_range.2 (Nat.succ_pos m))
  simpa using this

end Alg

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    {W : LocWach PD LL O v n}

theorem jD_smulA (E : EtTie W RA RW inclR φR gR πA) (T : LocLat G Qp LL O) (a : LetA O n)
    (x : W.DD T) : E.jD T (a • x) = inclR (E.io a) • E.jD T x := by
  rw [← algebraMap_smul W.EE a x, E.jD_smul, E.ioE_ext]


set_option maxHeartbeats 1000000 in
theorem of_sand (E : EtTie W RA RW inclR φR gR πA)
    (hφ : ∀ a, inclR (E.io (W.φA a)) = φR (inclR (E.io a)))
    (hA : ∀ (p q : Type) [Fintype p] [Fintype q] (Z : Matrix p q RW) (S : Matrix p p RA)
      (S' : Matrix q q RA) (Y : Matrix p q RA),
      Z.map φR = S.map inclR * Z * S'.map inclR + Y.map inclR → ∀ a b, Z a b ∈ Set.range inclR)
    (T : LocLat G Qp LL O) {κ : Type} [Fintype κ] (tb : Module.Basis κ O ↥T.L.T) (m₀ : ℕ)
    (hm₀ : ∀ x ∈ W.N T, ∃ y : TW RA T, TWincl inclR T y =
      TensorProduct.map (LinearMap.mulLeft O (inclR (E.io W.X) ^ m₀)) LinearMap.id (E.jD T x))
    (J : Multiset ℕ) (y : W.DD T) (hy : (J.map fun j => (W.φA ^ j) W.Q).prod • y ∈ W.N T)
    (b : TW RW T) (hb : TWmap φR T b - b = E.jD T y) (m : ℕ) (hJ : ∀ j ∈ J, j ≤ m) :
    ∃ a : ℕ, TensorProduct.map (LinearMap.mulLeft O
      (inclR (E.io (∏ j ∈ Finset.range (m + 1), (W.φA ^ j) W.X)) ^ a)) LinearMap.id b ∈
        TAinf inclR T := by
  set Y := ∏ j ∈ Finset.range (m + 1), (W.φA ^ j) W.X with hY
  set L := ∏ j ∈ Finset.range (m + 1), (W.φA ^ j) W.Q with hL
  set Jp := (J.map fun j => (W.φA ^ j) W.Q).prod with hJp
  have hYL : W.φA Y = Y * L := φ_prod W.φA W.X W.Q W.φA_X m
  refine ⟨m₀ + Multiset.card J, ?_⟩
  rw [GlobalTheory.NL.SandArb.map_mulLeft]
  have hdiv : W.X ^ m₀ * Jp ∣ (Y * L) ^ (m₀ + Multiset.card J) := by
    rw [mul_pow, pow_add, pow_add]
    refine (mul_dvd_mul (pow_dvd_pow_of_dvd (X_dvd W.φA W.X m) m₀) (multiset_dvd _ m J hJ)).trans ?_
    exact ⟨Y ^ Multiset.card J * L ^ m₀, by ring⟩
  obtain ⟨R, hR⟩ := hdiv
  set a := m₀ + Multiset.card J with ha
  have hb' : TWmap φR T b = E.jD T y + b := sub_eq_iff_eq_add.mp hb
  have hφc : TensorProduct.map φR.toLinearMap (LinearMap.id : ↥T.L.T →ₗ[O] ↥T.L.T)
      (inclR (E.io Y) ^ a • b) =
      inclR (E.io (L ^ a)) • (inclR (E.io Y) ^ a • b) + inclR (E.io ((Y * L) ^ a)) • E.jD T y := by
    rw [map_smul_left, map_pow, ← hφ, hYL]
    change inclR (E.io (Y * L)) ^ a • TWmap φR T b = _
    rw [hb', smul_add, add_comm, smul_smul, map_pow, map_pow, map_pow, map_pow, map_mul, map_mul,
      mul_pow, mul_comm]
  have hw : inclR (E.io ((Y * L) ^ a)) • E.jD T y ∈
      LinearMap.range (TensorProduct.map inclR.toLinearMap (LinearMap.id : ↥T.L.T →ₗ[O] ↥T.L.T)) := by
    obtain ⟨y', hy'⟩ := hm₀ _ hy
    rw [GlobalTheory.NL.SandArb.map_mulLeft, jD_smulA] at hy'
    rw [hR, map_mul, map_mul, map_mul, map_mul, mul_comm, mul_smul, mul_smul, map_pow, map_pow]
    refine GlobalTheory.Sandwich.incl_smul_mem inclR _ _ ?_
    rw [← hy']
    exact ⟨y', rfl⟩
  have key := mem_range_of_frob tb inclR φR hA (E.io (L ^ a)) _ _ hw hφc
  exact key

end Generic


set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in
theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (J : Multiset ℕ) (y : W.DD T), (J.map fun j => (W.φA ^ j) W.Q).prod • y ∈ W.N T → ∀ b : TW (RW LL) T, TWmap (φRW LL) T b - b = E.jD T y → ∀ m : ℕ, (∀ j ∈ J, j ≤ m) → ∃ a : ℕ, TensorProduct.map (LinearMap.mulLeft ↥(OL LL) (inclR LL (E.io (∏ j ∈ Finset.range (m + 1), (W.φA ^ j) W.X)) ^ a)) LinearMap.id b ∈ TAinf (inclR LL) T := by
  intro D HW F l _ K s LL h W E T hT J y hy b hb m hJ
  obtain ⟨m₀, hm₀, -⟩ := GlobalTheory.NL.SandArb.sandwich D HW F l K s LL h T hT
  have : Module.Free ↥(OL LL) ↥T.L.T := T.L.free
  have : Module.Finite ↥(OL LL) ↥T.L.T := Module.Finite.iff_fg.mpr T.L.fg
  exact of_sand E (GlobalTheory.NL.IoXQ.main D HW F l K s LL h).2.2.2.2.1
    (GlobalTheory.FrobIntegralCoeff.frobenius_integrality_coeff l LL) T
    (Module.Free.chooseBasis ↥(OL LL) ↥T.L.T) m₀ hm₀ J y hy b hb m hJ

end GlobalTheory.NL.FrobDenom
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelmerCocyclesScalarChangeTransfer
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelmerCocyclesScalarChangeTransfer
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate
open GlobalTheory.ResSel.CoefMap

namespace GlobalTheory.NewPrime.ScalarChange

section General

variable {R R' : Type} [CommRing R] [CommRing R'] (σ : R →+* R') {Γ : Type} [Group Γ] [TopologicalSpace Γ]
  {M : Type} [AddCommGroup M] [Module R M] [Module R' M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [ContinuousConstSMul R M] [ContinuousConstSMul R' M]
  (hs : ∀ (a : R) (m : M), a • m = σ a • m)
  (rho : Representation R Γ M) (rho' : Representation R' Γ M) (he : ∀ g m, rho g m = rho' g m)

def idSl : M →ₛₗ[σ] M where
  toFun m := m
  map_add' _ _ := rfl
  map_smul' c m := hs c m

def tr : H1 rho →ₛₗ[σ] H1 rho' :=
  slH1 rho rho' (idSl σ hs) continuous_id he

def back (z : Z1 rho') : Z1 rho :=
  ⟨z.1, z.2.1, fun g h => by rw [z.2.2, he]⟩

theorem tr_back (z : Z1 rho') :
    tr σ hs rho rho' he (Submodule.Quotient.mk (back rho rho' he z)) = Submodule.Quotient.mk z :=
  congrArg Submodule.Quotient.mk (Subtype.ext rfl)

theorem tr_injective : Function.Injective (tr σ hs rho rho' he) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using Submodule.Quotient.induction_on with
  | H z =>
    have h1 : (Submodule.Quotient.mk (semilinearCoefficientMapCocycles rho rho' (idSl σ hs) continuous_id he z) : H1 rho') = 0 := hx
    rw [Submodule.Quotient.mk_eq_zero] at h1 ⊢
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 h1
    refine (mem_coboundaries1 _ _).2 ⟨m, fun g => ?_⟩
    rw [he]
    exact hm g

theorem res_tr {H : Type} [Group H] [TopologicalSpace H] (phi : H →* Γ) (hphi : Continuous phi) (x : H1 rho) :
    resH1 rho' phi hphi (tr σ hs rho rho' he x) =
      tr σ hs (rho.comp phi) (rho'.comp phi) (fun g m => he (phi g) m) (resH1 rho phi hphi x) :=
  res_slH1 rho rho' (idSl σ hs) continuous_id he phi hphi x

theorem of_tr_mem_ur (J : Subgroup Γ) (x : H1 rho) (hx : tr σ hs rho rho' he x ∈ H1ur rho' J) : x ∈ H1ur rho J := by
  have h0 : resH1 rho' J.subtype continuous_subtype_val (tr σ hs rho rho' he x) = 0 := hx
  have h1 := res_tr σ hs rho rho' he J.subtype continuous_subtype_val x
  exact tr_injective σ hs (rho.comp J.subtype) (rho'.comp J.subtype) (fun g m => he g.1 m)
    (h1.symm.trans (h0.trans (map_zero _).symm))

end General

section Coef

variable {O Λ Λ' : Type} [CommRing O] [CommRing Λ] [Algebra O Λ] [CommRing Λ'] [Algebra O Λ'] (φ : Λ →ₐ[O] Λ')
  {Y : Type} [AddCommGroup Y] [Module Λ Y] [Module Λ' Y] (hY : ∀ (a : Λ) (y : Y), a • y = φ a • y)

include hY in
theorem algebraMap_smul (c : O) (y : Y) : algebraMap O Λ c • y = algebraMap O Λ' c • y := by
  rw [hY, φ.commutes]

include hY in
theorem vec_smul {r : ℕ} (a : Λ) (m : Fin r → Y) : a • m = φ a • m :=
  funext fun c => hY a (m c)

include hY in
theorem repOn_eq_repOn {Γ : Type} [Group Γ] {r : ℕ} (ρ : Γ →* GL (Fin r) O) (κ : Γ →* Λˣ) (κ' : Γ →* Λ'ˣ)
    (hκ : ∀ g, ((κ' g : Λ'ˣ) : Λ') = φ (κ g : Λˣ)) (g : Γ) (m : Fin r → Y) :
    repOn ρ κ Y g m = repOn ρ κ' Y g m := by
  funext a
  change ((κ g : Λˣ) : Λ) • ∑ j, algebraMap O Λ ((ρ g : Matrix (Fin r) (Fin r) O) a j) • m j =
    ((κ' g : Λ'ˣ) : Λ') • ∑ j, algebraMap O Λ' ((ρ g : Matrix (Fin r) (Fin r) O) a j) • m j
  simp only [algebraMap_smul φ hY]
  rw [hY, hκ]

end Coef

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (bkP : BKPh X)
  (i : X.Tw) {r : ℕ} (ρ : GE N →* GL (Fin r) (X.O0 i))
  {Λ Λ' : Type} [CommRing Λ] [Algebra (X.O0 i) Λ] [CommRing Λ'] [Algebra (X.O0 i) Λ']
  (φ : Λ →ₐ[X.O0 i] Λ') (κ : GE N →* Λˣ) (κ' : GE N →* Λ'ˣ) (hκ : ∀ g, ((κ' g : Λ'ˣ) : Λ') = φ (κ g : Λˣ))
  {Y : Type} [AddCommGroup Y] [Module Λ Y] [Module Λ' Y] [TopologicalSpace Y] [DiscreteTopology Y]
  (hY : ∀ (a : Λ) (y : Y), a • y = φ a • y)

abbrev trG : H1 (repOn ρ κ Y) →ₛₗ[(φ : Λ →+* Λ')] H1 (repOn ρ κ' Y) :=
  tr (φ : Λ →+* Λ') (vec_smul φ hY) (repOn ρ κ Y) (repOn ρ κ' Y) (repOn_eq_repOn φ hY ρ κ κ' hκ)

abbrev trL (v : PlE D.host) :
    H1 ((repOn ρ κ Y).comp (DecV N v).subtype) →ₛₗ[(φ : Λ →+* Λ')] H1 ((repOn ρ κ' Y).comp (DecV N v).subtype) :=
  tr (φ : Λ →+* Λ') (vec_smul φ hY) ((repOn ρ κ Y).comp (DecV N v).subtype) ((repOn ρ κ' Y).comp (DecV N v).subtype)
    (fun g m => repOn_eq_repOn φ hY ρ κ κ' hκ g.1 m)

theorem trL_mem_bkOn (v : PlE D.host) (x : H1 ((repOn ρ κ Y).comp (DecV N v).subtype))
    (hx : x ∈ bkOn bkP i ρ κ Y v) : trL i ρ φ κ κ' hκ hY v x ∈ bkOn bkP i ρ κ' Y v := by
  unfold bkOn at hx ⊢
  split_ifs at hx ⊢ with hv
  · induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, c, y, b, hc, hy, hz, rfl⟩ := hx
      refine Submodule.subset_span ⟨semilinearCoefficientMapCocycles _ _ (idSl (φ : Λ →+* Λ') (vec_smul φ hY)) continuous_id
        (fun g m => repOn_eq_repOn φ hY ρ κ κ' hκ g.1 m) z, c, y, b, hc, hy, fun g a => ?_, rfl⟩
      change ((z : ↥(DecV N v) → Fin r → Y) g a) = _
      rw [hz, algebraMap_smul φ hY]
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hx
  · rw [Submodule.mem_bot] at hx ⊢
    rw [hx, map_zero]

theorem exists_mem_bkOn (v : PlE D.host) (x' : H1 ((repOn ρ κ' Y).comp (DecV N v).subtype))
    (hx : x' ∈ bkOn bkP i ρ κ' Y v) : ∃ w ∈ bkOn bkP i ρ κ Y v, trL i ρ φ κ κ' hκ hY v w = x' := by
  by_cases hv : v ∈ placesOver D.host.E (X.l i)
  · have H : ∀ a : Λ', ∃ w ∈ bkOn bkP i ρ κ Y v, trL i ρ φ κ κ' hκ hY v w = a • x' := by
      unfold bkOn at hx
      rw [dite_eq_left hv] at hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        intro a
        obtain ⟨z, c, y, b, hc, hy, hz, rfl⟩ := hx
        refine ⟨Submodule.Quotient.mk (back ((repOn ρ κ Y).comp (DecV N v).subtype) ((repOn ρ κ' Y).comp (DecV N v).subtype)
          (fun g m => repOn_eq_repOn φ hY ρ κ κ' hκ g.1 m) (a • z)), ?_,
          tr_back _ _ _ _ _ _⟩
        unfold bkOn
        rw [dite_eq_left hv]
        refine Submodule.subset_span ⟨back ((repOn ρ κ Y).comp (DecV N v).subtype) ((repOn ρ κ' Y).comp (DecV N v).subtype)
          (fun g m => repOn_eq_repOn φ hY ρ κ κ' hκ g.1 m) (a • z), c, y, a • b, hc, hy,
            fun g e => ?_, rfl⟩
        change a • ((z : ↥(DecV N v) → Fin r → Y) g e) = _
        rw [hz, algebraMap_smul φ hY, smul_comm]
      | zero => exact fun a => ⟨0, Submodule.zero_mem _, by rw [map_zero, smul_zero]⟩
      | add x y _ _ hx hy =>
        intro a
        obtain ⟨w, hw, e⟩ := hx a
        obtain ⟨w', hw', e'⟩ := hy a
        exact ⟨w + w', Submodule.add_mem _ hw hw', by rw [map_add (f := _), e, e', smul_add]⟩
      | smul c x _ hx =>
        intro a
        obtain ⟨w, hw, e⟩ := hx (a * c)
        exact ⟨w, hw, by rw [e, mul_smul]⟩
    simpa using H 1
  · unfold bkOn at hx
    rw [dite_eq_right hv, Submodule.mem_bot] at hx
    exact ⟨0, Submodule.zero_mem _, by rw [map_zero, hx]⟩

theorem trG_mem_selOn (Q : Finset (PlE D.host)) (x : H1 (repOn ρ κ Y)) (hx : x ∈ selOn bkP i ρ κ Y Q) :
    trG i ρ φ κ κ' hκ hY x ∈ selOn bkP i ρ κ' Y Q := by
  refine (mem_Sel _ _ _ _ _).2 fun v => ?_
  have hv := (mem_Sel _ _ _ _ _).1 hx v
  refine (res_tr (φ : Λ →+* Λ') (vec_smul φ hY) (repOn ρ κ Y) (repOn ρ κ' Y) (repOn_eq_repOn φ hY ρ κ κ' hκ)
    (Dec (F := D.host.E) (N.plOm.1 v)).subtype continuous_subtype_val x) ▸ ?_
  unfold Formalism.GaloisCohomology.bkCond at hv ⊢
  split_ifs at hv ⊢ with h1 h2
  · exact trL_mem_bkOn bkP i ρ φ κ κ' hκ hY v _ hv
  · exact Submodule.mem_top
  · exact slH1_ur _ _ _ _ _ _ _ hv

theorem of_trG_mem_selOn (Q : Finset (PlE D.host)) (x : H1 (repOn ρ κ Y))
    (hx : trG i ρ φ κ κ' hκ hY x ∈ selOn bkP i ρ κ' Y Q) : x ∈ selOn bkP i ρ κ Y Q := by
  refine (mem_Sel _ _ _ _ _).2 fun v => ?_
  have hv := (mem_Sel _ _ _ _ _).1 hx v
  have e := res_tr (φ : Λ →+* Λ') (vec_smul φ hY) (repOn ρ κ Y) (repOn ρ κ' Y) (repOn_eq_repOn φ hY ρ κ κ' hκ)
    (Dec (F := D.host.E) (N.plOm.1 v)).subtype continuous_subtype_val x
  have hv' : trL i ρ φ κ κ' hκ hY v (resH1 (repOn ρ κ Y) (Dec (F := D.host.E) (N.plOm.1 v)).subtype continuous_subtype_val x) ∈
      Formalism.GaloisCohomology.bkCond (repOn ρ κ' Y) N.plOm (X.l i) (Spl i ∪ ↑Q) (bkOn bkP i ρ κ' Y) v := e ▸ hv
  unfold Formalism.GaloisCohomology.bkCond at hv' ⊢
  split_ifs at hv' ⊢ with h1 h2
  · obtain ⟨w, hw, e'⟩ := exists_mem_bkOn bkP i ρ φ κ κ' hκ hY v _ hv'
    rwa [← tr_injective _ _ _ _ _ e']
  · exact Submodule.mem_top
  · exact of_tr_mem_ur _ _ _ _ _ _ _ hv'

theorem selC_transfer : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (Λ : Type) [CommRing Λ] [Algebra (X.O0 i) Λ] (Λ' : Type) [CommRing Λ'] [Algebra (X.O0 i) Λ'] (φ : Λ →ₐ[X.O0 i] Λ') (κ : GE N →* Λˣ) (κ' : GE N →* Λ'ˣ), (∀ g, ((κ' g : Λ'ˣ) : Λ') = φ (κ g : Λˣ)) → ∀ (Y : Type) [AddCommGroup Y] [Module Λ Y] [Module Λ' Y] [TopologicalSpace Y] [DiscreteTopology Y], (∀ (a : Λ) (y : Y), a • y = φ a • y) → (∀ g m, repOn (Tgl i s) κ Y g m = repOn (Tgl i s) κ' Y g m) ∧ ∀ Q f, SelC bkP i s κ Y Q f ↔ SelC bkP i s κ' Y Q f := by
  intro D N X bkP i s Λ _ _ Λ' _ _ φ κ κ' hκ Y _ _ _ _ _ hY
  refine ⟨repOn_eq_repOn φ hY (Tgl i s) κ κ' hκ, fun Q f => ⟨?_, ?_⟩⟩
  · rintro ⟨z, rfl, hz⟩
    exact ⟨semilinearCoefficientMapCocycles _ _ (idSl (φ : Λ →+* Λ') (vec_smul φ hY)) continuous_id (repOn_eq_repOn φ hY (Tgl i s) κ κ' hκ) z, rfl,
      trG_mem_selOn bkP i (Tgl i s) φ κ κ' hκ hY Q _ hz⟩
  · rintro ⟨z, rfl, hz⟩
    refine ⟨back _ _ (repOn_eq_repOn φ hY (Tgl i s) κ κ' hκ) z, rfl,
      of_trG_mem_selOn bkP i (Tgl i s) φ κ κ' hκ hY Q _ ?_⟩
    have e := tr_back (φ : Λ →+* Λ') (vec_smul φ hY) (repOn (Tgl i s) κ Y) (repOn (Tgl i s) κ' Y)
      (repOn_eq_repOn φ hY (Tgl i s) κ κ' hκ) z
    exact e ▸ hz

end GlobalTheory.NewPrime.ScalarChange

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelmerCocyclesScalarChangeTransferStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selmerCocycles_scalarChange_transfer : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (Λ : Type) [CommRing Λ] [Algebra (X.O0 i) Λ] (Λ' : Type) [CommRing Λ'] [Algebra (X.O0 i) Λ'] (φ : Λ →ₐ[X.O0 i] Λ') (κ : GE N →* Λˣ) (κ' : GE N →* Λ'ˣ), (∀ g, ((κ' g : Λ'ˣ) : Λ') = φ (κ g : Λˣ)) → ∀ (Y : Type) [AddCommGroup Y] [Module Λ Y] [Module Λ' Y] [TopologicalSpace Y] [DiscreteTopology Y], (∀ (a : Λ) (y : Y), a • y = φ a • y) → (∀ g m, repOn (Tgl i s) κ Y g m = repOn (Tgl i s) κ' Y g m) ∧ ∀ Q f, SelC bkP i s κ Y Q f ↔ SelC bkP i s κ' Y Q f := by
  first | exact @GlobalTheory.NewPrime.ScalarChange.selC_transfer | exact GlobalTheory.NewPrime.ScalarChange.selC_transfer | (intros; apply GlobalTheory.NewPrime.ScalarChange.selC_transfer <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoInvDualOfSetup
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoInvDualOfSetup
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.NewPrime


open IsLocalRing GlobalTheory.ScalarFrob in
theorem noInvDual_of_setup : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host)) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)) (z : GE N), Setup bkP i s κ Q → IsDual i s ρ → IsTameInertiaElementAtTwistPrime X i z → NoInvDual i κ ρ := by
  intro D N X bkP i s A _ _ _ _ κ Q ρ z hS hρ hz Y' _ _ m hm
  obtain ⟨h, hloc, -, -, hκ, -⟩ := hS
  obtain ⟨e, he, -, hu, hε⟩ := GlobalTheory.TwSys.TameScalar.exists_scalar_tmat_of_tame_inertia D N X bkP i s z h.1 hz
  have c0 : residue (X.O0 i) e ≠ 0 := (residue_ne_zero_iff_isUnit _).2 e.isUnit
  have c1 : residue (X.O0 i) e ≠ 1 := by
    rw [← residue_ne_zero_iff_isUnit, map_sub, map_one, sub_ne_zero] at hu
    exact hu
  have e1 : resT i s z = residue (X.O0 i) e • 1 := by
    rw [resT_apply, he]
    ext a b
    by_cases hab : a = b <;> simp [hab]
  have e2 := dual_of_scalar i s (by rw [hε]; simp) c0 e1
  rw [← hρ z] at e2
  have hκ' : ∃ n : ℕ, κ⁻¹ z ^ (X.l i ^ n) = 1 := by
    obtain ⟨n, hn⟩ := hκ z
    exact ⟨n, by rw [MonoidHom.inv_apply, inv_pow, hn, inv_one]⟩
  exact eq_zero_of_scalar Fact.out (GlobalTheory.PrimeToInertia.l_mem i) ρ κ⁻¹ hκ' (inv_ne_one.2 c1) e2 (q := 1) Nat.cast_one m
    (by rw [one_smul]; exact hm z)

end GlobalTheory.NewPrime
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoInvDualOfSetupStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.noInvDual_of_setup_of_isDual_of_tame_inertia : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host)) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)) (z : GE N), Setup bkP i s κ Q → IsDual i s ρ → IsTameInertiaElementAtTwistPrime X i z → NoInvDual i κ ρ := by
  first | exact @GlobalTheory.NewPrime.noInvDual_of_setup | exact GlobalTheory.NewPrime.noInvDual_of_setup | (intros; apply GlobalTheory.NewPrime.noInvDual_of_setup <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNeZeroSmulMemOfSpanEqTop
namespace GlobalTheory.QuotientLatticeTorsion

theorem exists_ne_zero_smul_mem_of_span_eq_top
    {O K V : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
    [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    (N : Submodule O V) (hN : Submodule.span K (N : Set V) = ⊤) (v : V) :
    ∃ b : O, b ≠ 0 ∧ b • v ∈ N := by
  have hv : v ∈ Submodule.span K (N : Set V) := hN ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine N.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact N.smul_mem b hax
    · rw [mul_smul]
      exact N.smul_mem a hby
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj (nonZeroDivisors O) c
    refine ⟨s.1 * a, mul_ne_zero (nonZeroDivisors.ne_zero s.2) ha, ?_⟩
    have key : (s.1 * a) • c • x = r • a • x := by
      rw [← algebraMap_smul K (s.1 * a), ← algebraMap_smul K r, ← algebraMap_smul K a x,
        smul_smul, smul_smul, ← hrs, map_mul]
      congr 1
      ring
    rw [key]
    exact N.smul_mem r hax

theorem quotient_lattice_torsion
    {G : Type} [Group G] [TopologicalSpace G] {Qp : Type} [Field Qp] {LL : Type} [Field LL]
    [Algebra Qp LL] [TopologicalSpace LL] {O : Type} [CommRing O] [Algebra O LL] [IsDomain O]
    [IsFractionRing O LL] (T : Formalism.BasicNotions.LocLat G Qp LL O)
    (w : Formalism.BasicNotions.LocLat.V T ⧸ Formalism.WeaklyAdmissibleFiltrations.Lattice.T (Formalism.BasicNotions.LocLat.L T)) :
    ∃ (b : O), b ≠ (0 : O) ∧
      b • w = (0 : Formalism.BasicNotions.LocLat.V T ⧸ Formalism.WeaklyAdmissibleFiltrations.Lattice.T (Formalism.BasicNotions.LocLat.L T)) := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  obtain ⟨b, hb, hbv⟩ :=
    exists_ne_zero_smul_mem_of_span_eq_top (K := LL) T.L.T T.L.span v
  refine ⟨b, hb, ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact hbv

end GlobalTheory.QuotientLatticeTorsion
end
