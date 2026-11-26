module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SpanColsMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajorantConjugateTransfer

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MmatMulVec
namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex Module Matrix
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace Data

variable {r : ℕ} (X : Data E r)

theorem cc_kappa0 : cc X.κ0 = -X.κ0 := by
  have hx : IsCMField.complexConj E X.ξ0 = -X.ξ0 := X.ξ0_im
  rcases X.κ0_xi with h | h <;> rw [h] <;> simp only [cc, map_mul, map_neg, map_ofNat, hx] <;> ring

theorem tau_kappa0 (τ : X.Ψ) : τ.1 X.κ0 = -(I * X.c τ) := by
  have hcc := congrArg τ.1 X.cc_kappa0
  have hconj : conj (τ.1 X.κ0) = -(τ.1 X.κ0) := by
    rw [← map_neg, ← hcc]
    exact (NumberField.IsCMField.complexEmbedding_complexConj E τ.1 X.κ0).symm
  have hre : (τ.1 X.κ0).re = 0 := by
    have h := congrArg Complex.re hconj
    simp only [Complex.conj_re, Complex.neg_re] at h
    linarith
  have him := X.κ0_sign τ
  have hnorm : ‖τ.1 X.κ0‖ = X.c τ := by
    simp only [Data.c]
    rcases X.κ0_xi with h | h <;> rw [h] <;> simp [map_mul, map_neg, norm_mul, map_ofNat]
  have hz : τ.1 X.κ0 = ((τ.1 X.κ0).im : ℂ) * I := by
    apply Complex.ext <;> simp [hre]
  have habs : ‖τ.1 X.κ0‖ = -(τ.1 X.κ0).im := by
    conv_lhs => rw [hz]
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_neg him]
  apply Complex.ext
  · simp [hre]
  · simp
    linarith

noncomputable def Mmat (u : Fin 2 → Fin r → E) (β : Matrix (Fin 2) (Fin 2) E) : Matrix (Fin r) (Fin r) E :=
  Matrix.of fun a j => (if a = j then 1 else 0) +
    X.κ0 * ∑ i, ∑ k, β i k * u i a * ∑ l, X.Gm j l * cc (u k l)

theorem Mmat_map (u : Fin 2 → Fin r → E) (β : Matrix (Fin 2) (Fin 2) E) (τ : X.Ψ) :
    (X.Mmat u β).map τ.1 = X.zmat u (X.embH β) τ := by
  ext a j
  by_cases h : a = j <;>
    set_option synthInstance.maxHeartbeats 100000 in
      simp [h, Matrix.map_apply, Data.Mmat, Data.zmat, Data.embH, Data.emb, map_add (f := _), map_mul, map_sum,
      X.tau_kappa0 τ, cc, NumberField.IsCMField.complexEmbedding_complexConj] <;> ring

theorem Mmat_zero (u : Fin 2 → Fin r → E) : X.Mmat u 0 = 1 := by
  ext a j
  simp [Data.Mmat, Matrix.one_apply]

private lemma Mmat_mulVec_eq_add_sum (u : Fin 2 → Fin r → E) (β : Matrix (Fin 2) (Fin 2) E) (v : Fin r → E) :
    X.Mmat u β *ᵥ v = v + ∑ i, (X.κ0 * ∑ k, β i k * herm X.Gm v (u k)) • u i := by
  funext a
  simp only [Matrix.mulVec, dotProduct, Data.Mmat, Matrix.of_apply, add_mul, Finset.sum_add_distrib,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Pi.add_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, herm, Finset.mul_sum, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  ring

private lemma herm_add_left_fundamental_domains (G : Matrix (Fin r) (Fin r) E) (x y z : Fin r → E) :
    herm G (x + y) z = herm G x z + herm G y z := by
  simp only [herm, Pi.add_apply, add_mul, Finset.sum_add_distrib]

private lemma herm_smul_left_fundamental_domains (G : Matrix (Fin r) (Fin r) E) (c : E) (x z : Fin r → E) :
    herm G (c • x) z = c * herm G x z := by
  simp only [herm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

private lemma herm_add_right_fundamental_domains' (G : Matrix (Fin r) (Fin r) E) (x y z : Fin r → E) :
    herm G x (y + z) = herm G x y + herm G x z := by
  simp only [herm, Pi.add_apply, cc, map_add (f := _), mul_add, Finset.sum_add_distrib]

private lemma herm_smul_right_eq_cc_mul' (G : Matrix (Fin r) (Fin r) E) (c : E) (x z : Fin r → E) :
    herm G x (c • z) = cc c * herm G x z := by
  simp only [herm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, cc, map_mul]
  ring

theorem Mmat_mul (u : Fin 2 → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (β β' : Matrix (Fin 2) (Fin 2) E) : X.Mmat u β * X.Mmat u β' = X.Mmat u (β + β') := by
  refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
  simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, Mmat_mulVec_eq_add_sum, herm_add_left_fundamental_domains,
    herm_smul_left_fundamental_domains, Fin.sum_univ_two, hu, mul_zero, add_zero, Matrix.add_apply]
  first
    | module
    | (simp only [add_mul, mul_add, add_smul]; abel)

noncomputable def gam (u : Fin 2 → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (β : Matrix (Fin 2) (Fin 2) E) : GL (Fin r) E :=
  ⟨X.Mmat u β, X.Mmat u (-β), by rw [X.Mmat_mul u hu, add_neg_cancel, Mmat_zero],
    by rw [X.Mmat_mul u hu, neg_add_cancel, Mmat_zero]⟩

private lemma cc_herm_Gm_eq_herm_swap (x y : Fin r → E) : cc (herm X.Gm x y) = herm X.Gm y x := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [herm, cc, map_sum, map_mul, NumberField.IsCMField.complexConj_apply_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  first
    | (have hg := X.Gm_herm b a
       simp only [cc] at hg
       rw [hg]
       ring)
    | (have hg := X.Gm_herm a b
       simp only [cc] at hg
       rw [hg]
       ring)

theorem herm_Mmat (u : Fin 2 → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (β : Matrix (Fin 2) (Fin 2) E) (hβ : ∀ i k, cc (β i k) = β k i) (v w : Fin r → E) :
    herm X.Gm (X.Mmat u β *ᵥ v) (X.Mmat u β *ᵥ w) = herm X.Gm v w := by
  have hk : IsCMField.complexConj E X.κ0 = -X.κ0 := X.cc_kappa0
  have hb' : ∀ i k, IsCMField.complexConj E (β i k) = β k i := hβ
  have hh : ∀ x y, IsCMField.complexConj E (herm X.Gm x y) = herm X.Gm y x := cc_herm_Gm_eq_herm_swap X
  simp only [Mmat_mulVec_eq_add_sum, herm_add_left_fundamental_domains, herm_add_right_fundamental_domains', herm_smul_left_fundamental_domains,
    herm_smul_right_eq_cc_mul', Fin.sum_univ_two, hu, mul_zero, add_zero, zero_add, cc, map_mul, map_add,
    hk, hb', hh]
  ring

theorem Mmat_mulVec (u : Fin 2 → Fin r → E) (β : Matrix (Fin 2) (Fin 2) E) (v : Fin r → E) :
    X.Mmat u β *ᵥ v = v + ∑ i, (X.κ0 * ∑ k, β i k * herm X.Gm v (u k)) • u i := by
  funext a
  simp only [Matrix.mulVec, dotProduct, Data.Mmat, Matrix.of_apply, add_mul, Finset.sum_add_distrib,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Pi.add_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, herm, Finset.mul_sum, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  ring

end Data

end ReciprocityTheory.ChartRestriction.G.FD
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowIsotropicPairs
namespace ReciprocityTheory.ChartRestriction.G.FD.FlowIsotropicPairs

open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FlowMajorantFlags
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

private lemma herm_swap_eq_zero_of_eq_zero (X : Data E r) (x y : Fin r → E) (h : herm X.Gm x y = 0) :
    herm X.Gm y x = 0 := by
  have e : cc (herm X.Gm x y) = herm X.Gm y x := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [herm, cc, map_sum, map_mul, NumberField.IsCMField.complexConj_apply_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    first
      | (have hg := X.Gm_herm b a
         simp only [cc] at hg
         rw [hg]
         ring)
      | (have hg := X.Gm_herm a b
         simp only [cc] at hg
         rw [hg]
         ring)
  rw [← e, h]
  simp [cc]

private lemma herm_smul_left_fundamental_domains (G : Matrix (Fin r) (Fin r) E) (c : E) (x z : Fin r → E) :
    herm G (c • x) z = c * herm G x z := by
  simp only [herm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

private lemma herm_smul_right_eq_cc_mul (G : Matrix (Fin r) (Fin r) E) (c : E) (x z : Fin r → E) :
    herm G x (c • z) = cc c * herm G x z := by
  simp only [herm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, cc, map_mul]
  ring

theorem isIsoPair_of (X : DataX E r) {ξ x : Fin r → E} (hξ : X.IsIso ξ) (hxξ : herm X.Gm x ξ = 0)
    (hxx : herm X.Gm x x = 0) (hne : ∀ e : E, x ≠ e • ξ) :
    IsIsoPair X.Gm ![ξ, (X.NC : E) • x] := by
  obtain ⟨-, hξξ, hξ0⟩ := hξ
  have hξx : herm X.Gm ξ x = 0 := herm_swap_eq_zero_of_eq_zero X.toData x ξ hxξ
  unfold IsIsoPair
  refine ⟨?_, LinearIndependent.pair_iff.mpr fun s t hst => ?_⟩
  · intro i k
    fin_cases i <;> fin_cases k <;>
      simp [herm_smul_left_fundamental_domains, herm_smul_right_eq_cc_mul, hξξ, hxξ, hxx, hξx]
  · by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero] at hst
      exact ⟨(smul_eq_zero.mp hst).resolve_right hξ0, rfl⟩
    · exfalso
      have hNC : (X.NC : E) ≠ 0 := Nat.cast_ne_zero.mpr X.NC_pos.ne'
      have htn : t * (X.NC : E) ≠ 0 := mul_ne_zero ht hNC
      have h1 : (t * (X.NC : E)) • x = -(s • ξ) := by
        rw [mul_smul]
        exact eq_neg_of_add_eq_zero_right hst
      apply hne (-(s / (t * X.NC)))
      calc x = (t * X.NC)⁻¹ • ((t * X.NC) • x) := by rw [smul_smul, inv_mul_cancel₀ htn, one_smul]
        _ = -(s / (t * X.NC)) • ξ := by rw [h1, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]

theorem mem_pair (X : DataX E r) {ξ x : Fin r → E} (hξ : X.IsIso ξ) (hx : x ∈ X.L') :
    ∀ i, (![ξ, (X.NC : E) • x] : Fin 2 → Fin r → E) i ∈ X.Λ := by
  obtain ⟨hξΛ, -, -⟩ := hξ
  intro i
  fin_cases i
  · exact hξΛ
  · exact X.NC_sub x hx

theorem xp_facts (X : Data E r) {ξ x : Fin r → E} (hξξ : herm X.Gm ξ ξ = 0) (hξ0 : ξ ≠ 0)
    (hxξ : herm X.Gm x ξ = 0) (hxx : herm X.Gm x x = 0) {z0 : Frame X.Ψ r} (hz0 : z0 ∈ X.dom)
    (τ : X.Ψ) :
    hermC τ.1 X.Gm (X.ucomp z0 ξ (X.embV x) τ) (Data.emb τ.1 ξ) = 0 ∧
      hermC τ.1 X.Gm (X.ucomp z0 ξ (X.embV x) τ) (X.ucomp z0 ξ (X.embV x) τ) = 0 ∧
      X.Hf z0 τ (X.ucomp z0 ξ (X.embV x) τ) (Data.emb τ.1 ξ) = 0 := by
  set α := X.Hf z0 τ (Data.emb τ.1 x) (Data.emb τ.1 ξ) /
    X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) with hα
  have hxp : X.ucomp z0 ξ (X.embV x) τ = Data.emb τ.1 x - α • Data.emb τ.1 ξ := rfl
  have h1 : hermC τ.1 X.Gm (Data.emb τ.1 x) (Data.emb τ.1 ξ) = 0 := by
    rw [hermC_emb, hxξ, map_zero]
  have h2 : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0 := by
    rw [hermC_emb, hξξ, map_zero]
  have h3 : hermC τ.1 X.Gm (Data.emb τ.1 x) (Data.emb τ.1 x) = 0 := by
    rw [hermC_emb, hxx, map_zero]
  have h4 : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 x) = 0 := by
    rw [← hermC_conj τ.1 X.Gm_herm, h1, map_zero]
  have hne : X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) ≠ 0 := by
    rw [X.Hf_self hz0 τ]
    exact_mod_cast (X.maj_pos hz0 τ (emb_ne_zero τ.1 hξ0)).ne'
  rw [hxp]
  refine ⟨?_, ?_, ?_⟩
  · rw [hermC_sub_left, hermC_smul_left, h1, h2, mul_zero, sub_zero]
  · simp only [hermC_sub_left, hermC_sub_right, hermC_smul_left, hermC_smul_right, h1, h2, h3, h4]
    simp
  · rw [Hf_sub_left, Hf_smul_left, hα, div_mul_cancel₀ _ hne, sub_self]

theorem e_facts (X : Data E r) {ξ x : Fin r → E} (hξξ : herm X.Gm ξ ξ = 0) (hξ0 : ξ ≠ 0)
    (hxξ : herm X.Gm x ξ = 0) (hxx : herm X.Gm x x = 0) {z0 : Frame X.Ψ r} (hz0 : z0 ∈ X.dom)
    (e : X.Ψ → Fin r → ℂ) (hxp0 : ∀ τ, X.ucomp z0 ξ (X.embV x) τ ≠ 0)
    (he : ∀ τ, e τ = ((Real.sqrt (X.c τ * X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ)))⁻¹ : ℂ) •
      X.ucomp z0 ξ (X.embV x) τ) :
    X.IsIsoV e ∧ (∀ τ, hermC τ.1 X.Gm (e τ) (Data.emb τ.1 ξ) = 0) ∧
      (∀ τ, X.Hf z0 τ (e τ) (Data.emb τ.1 ξ) = 0) ∧ (∀ τ, X.c τ * X.maj z0 τ (e τ) = 1) := by
  have key : ∀ τ, ∃ k : ℝ, 0 < k ∧ e τ = (k : ℂ) • X.ucomp z0 ξ (X.embV x) τ ∧
      k ^ 2 * (X.c τ * X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ)) = 1 := by
    intro τ
    have hm : 0 < X.c τ * X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ) :=
      mul_pos (MajorantFamilyNorms.c_pos X τ) (X.maj_pos hz0 τ (hxp0 τ))
    refine ⟨(Real.sqrt (X.c τ * X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ)))⁻¹,
      inv_pos.mpr (Real.sqrt_pos.mpr hm), ?_, ?_⟩
    · simp only [he τ, Complex.ofReal_inv]
    · rw [inv_pow, Real.sq_sqrt hm.le, inv_mul_cancel₀ hm.ne']
  refine ⟨fun τ => ?_, fun τ => ?_, fun τ => ?_, fun τ => ?_⟩
  · obtain ⟨k, hk, hek, -⟩ := key τ
    have hf := xp_facts X hξξ hξ0 hxξ hxx hz0 τ
    refine ⟨?_, ?_⟩
    · rw [hek, hermC_smul_left, hermC_smul_right, hf.2.1, mul_zero, mul_zero]
    · rw [hek]
      exact smul_ne_zero (Complex.ofReal_ne_zero.mpr hk.ne') (hxp0 τ)
  · obtain ⟨k, -, hek, -⟩ := key τ
    rw [hek, hermC_smul_left, (xp_facts X hξξ hξ0 hxξ hxx hz0 τ).1, mul_zero]
  · obtain ⟨k, -, hek, -⟩ := key τ
    rw [hek, Hf_smul_left, (xp_facts X hξξ hξ0 hxξ hxx hz0 τ).2.2, mul_zero]
  · obtain ⟨k, -, hek, hk2⟩ := key τ
    rw [hek, maj_smul X hz0, ← hk2]
    ring

theorem flow_facts (X : Data E r) {ξ : Fin r → E} {z0 : Frame X.Ψ r} (hz0 : z0 ∈ X.FramesOverBasis ξ)
    (e : X.Ψ → Fin r → ℂ) (hiso : X.IsIsoV e)
    (heξ : ∀ τ, hermC τ.1 X.Gm (e τ) (Data.emb τ.1 ξ) = 0)
    (hHe : ∀ τ, X.Hf z0 τ (e τ) (Data.emb τ.1 ξ) = 0) (hce : ∀ τ, X.c τ * X.maj z0 τ (e τ) = 1)
    {z : Frame X.Ψ r} (hz : z ∈ X.dom) (hf : X.SameFlag z0 z) :
    (∀ τ, X.ttV e z τ = 1) ∧ X.flowV e (fun _ => -(I / 2)) z ∈ X.FramesOverBasis ξ := by
  have httv : ∀ τ, X.ttV e z τ = 1 := by
    intro τ
    rw [Data.ttV, maj_flag X hz0.1 hz hf, hce τ, div_one]
  have hTz : X.flowV e (fun _ => -(I / 2)) z ∈ X.dom := by
    refine (flowDomainCriterion_holds r X e hiso z hz (fun _ => -(I / 2))).1.mpr fun τ => ?_
    rw [httv τ]
    norm_num
  refine ⟨httv, hTz, fun τ => ?_⟩
  have hve : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (e τ) = 0 := by
    rw [← hermC_conj τ.1 X.Gm_herm, heξ τ, map_zero]
  have hpe : hermC τ.1 X.Gm (X.ppos z τ (Data.emb τ.1 ξ)) (e τ) = 0 :=
    hpe_of X hz τ (Data.emb τ.1 ξ) (e τ) (by rw [Hf_flag X hz0.1 hz hf]; exact hHe τ) (heξ τ)
  rw [maj_flowV X e _ hz hTz τ _ hve hpe, maj_flag X hz0.1 hz hf, hz0.2 τ]

end ReciprocityTheory.ChartRestriction.G.FD.FlowIsotropicPairs
end
