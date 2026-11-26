module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.UnipotentMoves.KatoClassHeckeEulerFactorRelation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LminorSubmatrixCastSucc

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.UnipotentMoves.HermLinApply
namespace UnipMove

open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace DeltaValuation

def linF {r : ℕ} (c : Fin r → ℂ) : (Fin r → ℂ) →ₗ[ℂ] ℂ where
  toFun v := ∑ a, v a * c a
  map_add' u v := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' k v := by simp [Finset.mul_sum, mul_assoc]

lemma linF_apply {r : ℕ} (c : Fin r → ℂ) (v : Fin r → ℂ) : linF c v = ∑ a, v a * c a := rfl

def hermLin {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (K : ℂ) (w : Fin r → ℂ) :
    (Fin r → ℂ) →ₗ[ℂ] ℂ where
  toFun v := K * hermC τ G v w
  map_add' u v := by rw [hermC_add_left]; ring
  map_smul' k v := by rw [hermC_smul_left]; simp only [smul_eq_mul, RingHom.id_apply]; ring

lemma hermLin_apply {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (K : ℂ) (w v : Fin r → ℂ) :
    hermLin τ G K w v = K * hermC τ G v w := rfl

lemma posPart_smul {r : ℕ} (X : Data E r) (x : Frame X.Ψ r) (τ : X.Ψ) (c : ℂ) (v : Fin r → ℂ) :
    X.posPart x τ (c • v) = Complex.normSq c * X.posPart x τ v := by
  unfold Data.posPart
  simp only [hermC_smul_left, map_mul]
  have e : ∀ p q m : ℂ, c * p * m * (conj c * conj q) = (Complex.normSq c : ℂ) * (p * m * conj q) := by
    intro p q m
    rw [Complex.normSq_eq_conj_mul_self]
    ring
  simp only [e, ← Finset.mul_sum]
  rw [Complex.re_ofReal_mul]

lemma maj_smul {r : ℕ} (X : Data E r) (x : Frame X.Ψ r) (τ : X.Ψ) (c : ℂ) (v : Fin r → ℂ) :
    X.maj x τ (c • v) = Complex.normSq c * X.maj x τ v := by
  unfold Data.maj
  rw [posPart_smul, hermC_smul_left, hermC_smul_right]
  have e : c * (conj c * hermC τ.1 X.Gm v v) = (Complex.normSq c : ℂ) * hermC τ.1 X.Gm v v := by
    rw [Complex.normSq_eq_conj_mul_self]
    ring
  rw [e, Complex.re_ofReal_mul]
  ring

lemma O_smul {r : ℕ} (β : 𝓞 E) (v : Fin r → E) : β • v = (β : E) • v := rfl

end DeltaValuation

open DeltaValuation in
theorem sDelta_of (hemb : SEmb E) (hext : SExt E) (hdual : SDual E)
    (hP5 : IsotropicCoefficientSplitting (E := E)) (hP6 : NoShortVectorLowerBound (E := E)) : SDelta E := by
  intro r X ξ z1 ep n' hiso hep hn' hz1 hsep
  have hΛp : ∀ μ, μ ∈ X.Λp ξ ↔ μ ∈ X.Λ ∧ herm X.Gm μ ξ = 0 := fun μ => by
    simp only [Data.Λp, AddSubgroup.mem_inf, Submodule.mem_toAddSubgroup, AddMonoidHom.mem_ker]
    rfl
  have hlin : ∀ (b : E) (x y : Fin r → E), herm X.Gm (b • x) y = b * herm X.Gm x y := by
    intro b x y
    simp only [herm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  obtain ⟨f, hfΛ, hfadd, hfsmul, hfξ⟩ := hP5 r X.toData ξ hiso
  obtain ⟨F, hF⟩ := hext r X.toData ξ f hfadd hfsmul
  obtain ⟨cf, hFc⟩ : ∃ cf : Fin r → E, ∀ x, F x = ∑ a, x a * cf a :=
    ⟨fun a => F (fun j => if a = j then 1 else 0), fun x => by
      rw [LinearMap.pi_apply_eq_sum_univ F x]; simp only [smul_eq_mul]⟩
  have hFξ : F ξ = 1 := by
    have h1 : (1 : E) • ξ ∈ X.Λ := by rw [one_smul]; exact hiso.1
    have h2 : (1 : E) • ξ ∈ X.Λp ξ := (hΛp _).2 ⟨h1, by rw [one_smul]; exact hiso.2.1⟩
    have h3 := hF _ h2
    rw [hfξ 1 h1, one_smul] at h3
    exact h3
  have hn0 : (n' : ℂ) ≠ 0 := by exact_mod_cast hn'.ne'
  let δ₀ : X.Ψ → (Fin r → ℂ) →ₗ[ℂ] ℂ := fun τ => (-(n' : ℂ)) • linF (fun a => τ.1 (cf a))
  obtain ⟨μ₀, hμ₀, hbound⟩ := hP6 r X ξ ep hiso hep z1 hz1 hsep δ₀
  let δ' : X.Ψ → (Fin r → ℂ) →ₗ[ℂ] ℂ := fun τ =>
    δ₀ τ - hermLin τ.1 X.Gm ((dE E : ℂ) * (-τ.1 X.ξ0)) (X.ucomp z1 ξ (X.embV μ₀) τ)
  refine ⟨fun τ => ((n' : ℂ)⁻¹) • δ' τ, ?_, ?_⟩
  · intro u hu τ
    have hb := hbound u hu τ
    have e1 : (((n' : ℂ)⁻¹ • δ' τ) (u τ)) • Data.emb τ.1 ξ = ((n' : ℂ)⁻¹) •
        ((δ₀ τ (u τ) - (dE E : ℂ) * (-τ.1 X.ξ0) *
          hermC τ.1 X.Gm (u τ) (X.ucomp z1 ξ (X.embV μ₀) τ)) • Data.emb τ.1 ξ) := by
      simp only [δ', LinearMap.smul_apply, LinearMap.sub_apply, hermLin_apply, smul_eq_mul, smul_smul]
    have hinv : ((n' : ℂ)⁻¹) = (((n' : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
    rw [e1, maj_smul, hinv, Complex.normSq_ofReal, div_pow]
    have hpos : (0 : ℝ) ≤ (n' : ℝ)⁻¹ * (n' : ℝ)⁻¹ := by positivity
    calc (n' : ℝ)⁻¹ * (n' : ℝ)⁻¹ * X.maj z1 τ ((δ₀ τ (u τ) - (dE E : ℂ) * (-τ.1 X.ξ0) *
          hermC τ.1 X.Gm (u τ) (X.ucomp z1 ξ (X.embV μ₀) τ)) • Data.emb τ.1 ξ)
        ≤ (n' : ℝ)⁻¹ * (n' : ℝ)⁻¹ *
          (frameIndexBound r (fdeg E) (dE E) (rdE E) X.NA X.NC ep ^ 2 * X.maj z1 τ (u τ)) :=
          mul_le_mul_of_nonneg_left hb hpos
      _ = _ := by ring
  · intro μ hμ
    obtain ⟨hμΛ, hμξ⟩ := (hΛp μ).1 hμ
    obtain ⟨hμ₀Λ, hμ₀ξ⟩ := (hΛp μ₀).1 hμ₀
    obtain ⟨α, hα⟩ := hdual (-X.ξ0 * herm X.Gm μ μ₀) (by
      intro a
      have ha : (a : E) • μ ∈ X.Λ := by rw [← O_smul]; exact X.Λ.smul_mem a hμΛ
      obtain ⟨k, hk⟩ := X.EF_int _ ha μ₀ hμ₀Λ
      refine ⟨k, ?_⟩
      rw [← hk, EFf, hlin]
      congr 1
      ring)
    refine ⟨(n' : E) * f μ + α, ?_, ?_⟩
    · rw [add_smul, mul_smul]
      refine X.Λ.add_mem ?_ ?_
      · rw [Nat.cast_smul_eq_nsmul]
        exact nsmul_mem (hfΛ μ hμ) n'
      · rw [← O_smul]
        exact X.Λ.smul_mem α hiso.1
    · funext τ
      have hu : ∀ ν : Fin r → E, X.ucomp z1 ξ (X.embV ν) τ = Data.emb τ.1 ν -
          (X.Hf z1 τ (Data.emb τ.1 ν) (Data.emb τ.1 ξ) / X.Hf z1 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)) •
            Data.emb τ.1 ξ := fun ν => rfl
      have h1 : hermC τ.1 X.Gm (Data.emb τ.1 μ) (Data.emb τ.1 μ₀) = τ.1 (herm X.Gm μ μ₀) :=
        hermC_emb _ _ _ _
      have h2 : hermC τ.1 X.Gm (Data.emb τ.1 μ) (Data.emb τ.1 ξ) = 0 := by
        rw [hermC_emb, hμξ, map_zero]
      have h3 : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 μ₀) = 0 := by
        rw [← hermC_conj τ.1 X.Gm_herm, hermC_emb, hμ₀ξ, map_zero, map_zero]
      have h4 : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0 := by
        rw [hermC_emb, hiso.2.1, map_zero]
      have hherm : hermC τ.1 X.Gm (X.ucomp z1 ξ (X.embV μ) τ) (X.ucomp z1 ξ (X.embV μ₀) τ) =
          τ.1 (herm X.Gm μ μ₀) := by
        rw [hu, hu]
        simp only [hermC_sub_left, hermC_sub_right, hermC_smul_left, hermC_smul_right, h1, h2, h3, h4]
        ring
      have hl1 : linF (fun a => τ.1 (cf a)) (Data.emb τ.1 μ) = τ.1 (F μ) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [linF_apply, hFc, map_sum]
        simp only [Data.emb, map_mul]
      have hl2 : linF (fun a => τ.1 (cf a)) (Data.emb τ.1 ξ) = 1 := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [linF_apply, show (1 : ℂ) = τ.1 (F ξ) by rw [hFξ, map_one], hFc, map_sum]
        simp only [Data.emb, map_mul]
      set co := X.Hf z1 τ (Data.emb τ.1 μ) (Data.emb τ.1 ξ) /
        X.Hf z1 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) with hco
      have hδ' : δ' τ (X.ucomp z1 ξ (X.embV μ) τ) =
          -(n' : ℂ) * (τ.1 (F μ) - co) - (dE E : ℂ) * (-τ.1 X.ξ0) * τ.1 (herm X.Gm μ μ₀) := by
        simp only [δ', δ₀, LinearMap.sub_apply, LinearMap.smul_apply, hermLin_apply, smul_eq_mul]
        rw [hherm, hu μ, map_sub, map_smul, hl1, hl2, smul_eq_mul, mul_one]
      have hL : ((n' : ℂ) • (X.aproj z1 ξ (X.embV μ) - X.lineV ξ (fun τ =>
          (((n' : ℂ)⁻¹) • δ' τ) (X.ucomp z1 ξ (X.embV μ) τ)))) τ =
          ((n' : ℂ) * (co - (n' : ℂ)⁻¹ * δ' τ (X.ucomp z1 ξ (X.embV μ) τ))) • Data.emb τ.1 ξ := by
        show (n' : ℂ) • (co • Data.emb τ.1 ξ -
          (((n' : ℂ)⁻¹) • δ' τ) (X.ucomp z1 ξ (X.embV μ) τ) • Data.emb τ.1 ξ) = _
        rw [LinearMap.smul_apply, smul_eq_mul, ← sub_smul, smul_smul]
      have hR : X.embV (((n' : E) * f μ + α) • ξ) τ = (τ.1 ((n' : E) * f μ + α)) • Data.emb τ.1 ξ := by
        funext a
        simp [Data.embV, Data.emb, map_mul]
      have hdE : ((dE E : ℝ) : ℂ) = (((NumberField.discr E).natAbs : ℕ) : ℂ) := by
        have : (((NumberField.discr E).natAbs : ℕ) : ℝ) = |((NumberField.discr E : ℤ) : ℝ)| := by
          rw [Nat.cast_natAbs, Int.cast_abs]
        rw [dE, ← this]
        push_cast
        rfl
      rw [hL, hR]
      congr 1
      rw [hδ', hF μ hμ, map_add (f := _), map_mul, map_natCast, hα, map_mul, map_natCast, map_mul, map_neg, hdE]
      field_simp
      ring

end

end UnipMove
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.UnipotentMoves.AprojEqZeroOfUz
namespace UnipMove

open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace AffineProjectionSplitting

variable {r : ℕ} (X : Data E r) (ξ : Fin r → E)

private lemma hermC_smul_left_dim {n : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin n) (Fin n) E) (c : ℂ)
    (u v : Fin n → ℂ) : hermC τ G (c • u) v = c * hermC τ G u v := by
  simp only [hermC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

private lemma hermC_sub_left_dim {n : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin n) (Fin n) E)
    (u w v : Fin n → ℂ) : hermC τ G (u - w) v = hermC τ G u v - hermC τ G w v := by
  simp only [hermC, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

private lemma hermC_emb_emb_eq_herm {n : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin n) (Fin n) E)
    (x y : Fin n → E) : hermC τ G (Data.emb τ x) (Data.emb τ y) = τ (herm G x y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hermC, herm, Data.emb, map_sum, map_mul, cc, IsCMField.complexEmbedding_complexConj]

lemma lineV_mem_Iperp (hξ : herm X.Gm ξ ξ = 0) (s : X.Ψ → ℂ) : X.lineV ξ s ∈ X.Iperp ξ := by
  simp only [Data.Iperp, Set.mem_setOf_eq]
  intro τ
  simp only [Data.lineV, hermC_smul_left_dim, hermC_emb_emb_eq_herm, hξ, map_zero, mul_zero]

lemma Iperp_sub {u w : X.Ψ → Fin r → ℂ} (hu : u ∈ X.Iperp ξ) (hw : w ∈ X.Iperp ξ) :
    u - w ∈ X.Iperp ξ := by
  simp only [Data.Iperp, Set.mem_setOf_eq] at hu hw ⊢
  intro τ
  rw [Pi.sub_apply, hermC_sub_left_dim, hu τ, hw τ, sub_zero]

lemma Iperp_smul (c : ℂ) {u : X.Ψ → Fin r → ℂ} (hu : u ∈ X.Iperp ξ) : c • u ∈ X.Iperp ξ := by
  simp only [Data.Iperp, Set.mem_setOf_eq] at hu ⊢
  intro τ
  rw [Pi.smul_apply, hermC_smul_left_dim, hu τ, mul_zero]

lemma aproj_eq_zero_of_Uz {x : Frame X.Ψ r} {u : X.Ψ → Fin r → ℂ} (hu : u ∈ X.Uz x ξ) :
    X.aproj x ξ u = 0 := by
  simp only [Data.Uz, Data.Iperp, Set.mem_setOf_eq] at hu
  obtain ⟨-, h2⟩ := hu
  funext τ
  have hH : X.Hf x τ (u τ) (Data.emb τ.1 ξ) = 0 := by
    have h3 := h2 τ
    simp only [Data.Jz, hermC_smul_left_dim] at h3
    rw [Data.Hf]
    exact (mul_eq_zero.mp h3).resolve_left Complex.I_ne_zero
  simp only [Data.aproj, Data.lineV, hH, zero_div, zero_smul, Pi.zero_apply]

private lemma ppos_const_smul (x : Frame X.Ψ r) (τ : X.Ψ) (c : ℂ) (u : Fin r → ℂ) :
    X.ppos x τ (c • u) = c • X.ppos x τ u := by
  simp only [Data.ppos, hermC_smul_left_dim, Finset.smul_sum, smul_smul, Finset.mul_sum, mul_assoc]

lemma Hf_smul (x : Frame X.Ψ r) (τ : X.Ψ) (c : ℂ) (u w : Fin r → ℂ) :
    X.Hf x τ (c • u) w = c * X.Hf x τ u w := by
  unfold Data.Hf
  rw [ppos_const_smul, smul_comm (2 : ℂ) c, ← smul_sub, hermC_smul_left_dim]

lemma aproj_smul (x : Frame X.Ψ r) (c : ℂ) (u : X.Ψ → Fin r → ℂ) :
    X.aproj x ξ (c • u) = c • X.aproj x ξ u := by
  funext τ
  simp only [Data.aproj, Data.lineV, Pi.smul_apply, Hf_smul, smul_smul, mul_div_assoc]

lemma ucomp_smul (x : Frame X.Ψ r) (c : ℂ) (u : X.Ψ → Fin r → ℂ) :
    X.ucomp x ξ (c • u) = c • X.ucomp x ξ u := by
  simp only [Data.ucomp, aproj_smul, smul_sub]

end AffineProjectionSplitting

lemma split_key {r : ℕ} {X : DataX E r} {ξ : Fin r → E} (hξ : herm X.Gm ξ ξ = 0)
    {z1 z : Frame X.Ψ r} {δ : X.Ψ → (Fin r → ℂ) →ₗ[ℂ] ℂ}
    (hap : ∀ u ∈ X.Iperp ξ, X.aproj z ξ u = X.aproj z1 ξ u - X.lineV ξ (fun τ => δ τ (X.ucomp z1 ξ u τ)))
    (hJ : ∀ u ∈ X.Uz z1 ξ, X.ucomp z ξ (X.Jz z1 u) = X.Jz z (X.ucomp z ξ u))
    {v : X.Ψ → Fin r → ℂ} (hv : v ∈ X.Iperp ξ) (c : ℂ)
    (h1 : X.Jz z1 (X.ucomp z1 ξ v) = c • X.ucomp z1 ξ v) :
    X.Jz z (X.ucomp z ξ v) = c • X.ucomp z ξ v := by
  have hwI : X.ucomp z1 ξ v ∈ X.Iperp ξ :=
    AffineProjectionSplitting.Iperp_sub X.toData ξ hv (AffineProjectionSplitting.lineV_mem_Iperp X.toData ξ hξ _)
  have hUz : X.ucomp z1 ξ v ∈ X.Uz z1 ξ := by
    simp only [Data.Uz, Set.mem_setOf_eq]
    refine ⟨hwI, ?_⟩
    rw [h1]
    exact AffineProjectionSplitting.Iperp_smul X.toData ξ c hwI
  have h0 : X.aproj z1 ξ (X.ucomp z1 ξ v) = 0 := AffineProjectionSplitting.aproj_eq_zero_of_Uz X.toData ξ hUz
  have hu1 : X.ucomp z1 ξ (X.ucomp z1 ξ v) = X.ucomp z1 ξ v := by
    show X.ucomp z1 ξ v - X.aproj z1 ξ (X.ucomp z1 ξ v) = _
    rw [h0, sub_zero]
  have hEq : X.ucomp z ξ (X.ucomp z1 ξ v) = X.ucomp z ξ v := by
    have e1 := hap _ hwI
    have e2 := hap _ hv
    show X.ucomp z1 ξ v - X.aproj z ξ (X.ucomp z1 ξ v) = v - X.aproj z ξ v
    rw [e1, e2, h0, hu1]
    show v - X.aproj z1 ξ v - (0 - _) = v - (X.aproj z1 ξ v - _)
    abel
  have hJ1 := hJ _ hUz
  rw [h1, AffineProjectionSplitting.ucomp_smul, hEq] at hJ1
  exact hJ1.symm

theorem sSplit : SSplit E := by
  unfold SSplit
  intro r X ξ La z1 z lam δ hiso hsd hap hJ
  have hξ : herm X.Gm ξ ξ = 0 := by
    have h := hiso
    simp only [Data.IsIso] at h
    exact h.2.1
  unfold SplitData at hsd ⊢
  obtain ⟨hA, hB, hC, hD, hF, hG⟩ := hsd
  have hv : ∀ j, X.embV (lam j) ∈ X.Iperp ξ := fun j => by
    simp only [Data.Iperp, Set.mem_setOf_eq]
    intro τ
    simp only [Data.embV, AffineProjectionSplitting.hermC_emb_emb_eq_herm, (hA j).2, map_zero]
  refine ⟨hA, hB, hC, fun j hj => ⟨(hD j hj).1, ?_⟩, fun j hj => ⟨(hF j hj).1, ?_⟩, hG⟩
  · exact split_key hξ hap hJ (hv j) I (hD j hj).2
  · have h2 := split_key hξ hap hJ (hv j) (-I) (by rw [(hF j hj).2, neg_smul])
    rw [h2, neg_smul]

end

end UnipMove
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.UnipotentMoves.TopOf
namespace UnipMove

open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem top_of (hemb : SEmb E) (hN1 : RadiusPosLeTenth) (hN2 : KatoClassHeckeEulerFactorRelation) (hN3 : UnipotentMoveNumericalInequalities) (hN4 : EpsilonZeroPos E)
    (hcmp : SCmp E) (hmf : SMajFlag E) (hflag : SFlagMap E) (hgraph : SGraph E)
    (hsplit : SSplit E) (hdelta : SDelta E)
    (hD4 : ShortVectorBound (E := E)) (hD2i : UnitaryComplementMove (E := E)) (hD2ii : ReducedFrameDomainCovering (E := E)) :
    UnitaryUnipotentMove (E := E) := by
  intro r X la P ξ ν c1 w z0 hH x0 hx0 hx0o hfl0 lam h1 Z1 hu1 hfix1 hpres1 hsp1 hfl1 hZ1 n' hn'
  have hD4' := hD4 r X la P ξ ν c1 w z0 hH
  obtain ⟨-, -, hiso, hc1, -, -, hw, -, -, hz0D1, -⟩ := hH
  obtain ⟨hρ0, hρ1⟩ := hN1 c1 w hc1 hw
  have hZ1' : X.zN Z1 < d6rh c1 w / 21 := by
    have : d6rh c1 w / 100 < d6rh c1 w / 21 := by linarith
    linarith
  rcases Nat.eq_zero_or_pos n' with rfl | hn'pos
  · have hone : X.lmulC (fun _ => (1 : Matrix (Fin r) (Fin r) ℂ)) (X.lmulC h1 z0) = X.lmulC h1 z0 := by
      funext τ; simp only [Data.lmulC, one_mul, mat, Matrix.of_apply]; rfl
    refine ⟨fun _ => 1, Z1, ?_, ?_, ?_, ?_, ?_, hZ1'⟩
    · intro τ u v; simp
    · intro τ; simp
    · intro μ _
      refine ⟨0, by simp, ?_⟩
      funext τ a; simp [Data.embV, Data.emb]
    · rw [hone]; exact hsp1
    · rw [hone]; exact hfl1

  have hz0dom : z0 ∈ X.dom := hz0D1.1
  obtain ⟨hz1dom, hap, hmajξ, -⟩ := hD2i r X.toData ξ hiso z0 hz0dom h1 hu1 hfix1 hpres1
  have hz1D1 : X.lmulC h1 z0 ∈ X.FramesOverBasis ξ := ⟨hz1dom, fun τ => by rw [hmajξ τ]; exact hz0D1.2 τ⟩
  have hρ'0 : 0 < d6rh c1 w / 100 := by positivity
  have hρ'1 : d6rh c1 w / 100 ≤ 1 / 10 := by linarith
  have hc := hcmp r X.toData x0 hx0 hx0o (d6rh c1 w / 100) hρ'0 hρ'1 Z1 hZ1 (X.lmulC h1 z0) hz1dom hfl1
  have hmz0 : X.maj z0 = X.maj x0 := hmf r X.toData z0 x0 hz0dom hx0 hfl0
  set ρ := d6rh c1 w with hρdef
  set t := (1 - ρ / 100) / (1 + ρ / 100) with htdef
  have ht0 : 0 < t := by rw [htdef]; apply div_pos <;> linarith
  have ht1 : t ≤ 1 := by rw [htdef, div_le_one (by linarith)]; linarith
  have htinv : (1 + ρ / 100) / (1 - ρ / 100) = 1 / t := by
    rw [htdef, one_div_div]
  set ep0 := flowEpsilonBound X.g (dE E) (fdeg E) X.NA X.NC c1 w with hep0def
  have hep0 : 0 < ep0 := hN4 r X c1 w hc1 hw

  have hns : ∀ x ∈ X.L', herm X.Gm x ξ = 0 → (∀ e : E, x ≠ e • ξ) →
      ∃ τ : X.Ψ, t * ep0 ≤ X.maj (X.lmulC h1 z0) τ (X.ucomp (X.lmulC h1 z0) ξ (X.embV x) τ) := by
    intro x hx hxξ hne
    obtain ⟨τ, hτ⟩ := hD4' x hx hxξ hne
    refine ⟨τ, ?_⟩
    have hI : X.embV x ∈ X.Iperp ξ := fun τ => by
      show hermC τ.1 X.Gm (Data.emb τ.1 x) (Data.emb τ.1 ξ) = 0
      rw [hemb, hxξ, map_zero]
    have hu : X.ucomp (X.lmulC h1 z0) ξ (X.embV x) = X.ucomp z0 ξ (X.embV x) := by
      simp only [Data.ucomp, hap _ hI]
    rw [hu]
    have h1' := (hc τ (X.ucomp z0 ξ (X.embV x) τ)).1
    rw [hmz0] at hτ
    calc t * ep0 ≤ t * X.maj x0 τ (X.ucomp z0 ξ (X.embV x) τ) :=
          mul_le_mul_of_nonneg_left hτ ht0.le
      _ ≤ _ := h1'
  obtain ⟨δ, hδb, hδΛ⟩ := hdelta r X ξ (X.lmulC h1 z0) (t * ep0) n' hiso (mul_pos ht0 hep0) hn'pos
    hz1D1 hns
  set ms := frameIndexBound r (fdeg E) (dE E) (rdE E) X.NA X.NC ep0 with hmsdef
  set κ := frameIndexBound r (fdeg E) (dE E) (rdE E) X.NA X.NC (t * ep0) / n' with hκdef
  have hrd : 0 ≤ rdE E := Real.rpow_nonneg (abs_nonneg _) _
  have hm := hN2 r (fdeg E) (dE E) (rdE E) X.NA X.NC ep0 t (abs_nonneg _) hrd (Nat.cast_nonneg _)
    hep0 ht0 ht1
  have hm' := (hN2 r (fdeg E) (dE E) (rdE E) X.NA X.NC (t * ep0) 1 (abs_nonneg _) hrd
    (Nat.cast_nonneg _) (mul_pos ht0 hep0) one_pos le_rfl).2
  have hn'R : (0 : ℝ) < n' := by exact_mod_cast hn'pos
  have hκ0 : 0 ≤ κ := div_nonneg hm' hn'R.le
  have hmsn : ms / n' ≤ ρ / 1000 := by
    rw [div_le_iff₀ hn'R]
    have h := hn'
    rw [div_le_iff₀ hρ0] at h
    linarith
  have hκρ : κ ≤ ρ / (1000 * t) := by
    calc κ ≤ ms / t / n' := div_le_div_of_nonneg_right hm.1 hn'R.le
      _ = ms / n' / t := by ring
      _ ≤ ρ / 1000 / t := div_le_div_of_nonneg_right hmsn ht0.le
      _ = ρ / (1000 * t) := by ring
  obtain ⟨hκ1, hη1, hfin⟩ := hN3 ρ κ hρ0 hρ1 hκ0 hκρ
  obtain ⟨n, hnu, hnξ, -, -, hnap, -, hnJ, hnb⟩ :=
    hD2ii r X.toData ξ hiso (X.lmulC h1 z0) hz1dom δ κ hκ0 hκ1 hδb

  have hnb0 : ∀ (τ : X.Ψ) (v : Fin r → ℂ),
      X.maj x0 τ (Matrix.mulVec (n τ - 1) v) ≤ (3 * κ / t) ^ 2 * X.maj x0 τ v := by
    intro τ v
    have a1 := (hc τ (Matrix.mulVec (n τ - 1) v)).1
    have a2 := hnb τ v
    have a3 := (hc τ v).2
    rw [htinv] at a3
    have e1 : X.maj x0 τ (Matrix.mulVec (n τ - 1) v) ≤
        X.maj (X.lmulC h1 z0) τ (Matrix.mulVec (n τ - 1) v) / t := by
      rw [le_div_iff₀ ht0]; linarith
    have e2 : X.maj (X.lmulC h1 z0) τ v ≤ X.maj x0 τ v / t := by
      exact le_of_le_of_eq a3 (by ring)
    calc X.maj x0 τ (Matrix.mulVec (n τ - 1) v)
        ≤ X.maj (X.lmulC h1 z0) τ (Matrix.mulVec (n τ - 1) v) / t := e1
      _ ≤ (3 * κ) ^ 2 * X.maj (X.lmulC h1 z0) τ v / t := div_le_div_of_nonneg_right a2 ht0.le
      _ ≤ (3 * κ) ^ 2 * (X.maj x0 τ v / t) / t :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left e2 (sq_nonneg _)) ht0.le
      _ = (3 * κ / t) ^ 2 * X.maj x0 τ v := by field_simp
  have hη0 : 0 ≤ 3 * κ / t := by positivity
  obtain ⟨Z, hZfl, hZn⟩ := hgraph r X.toData x0 hx0 hx0o n Z1 (3 * κ / t) (ρ / 100) hη0
    (by positivity) hZ1 hη1 hnb0
  refine ⟨n, Z, hnu, hnξ, ?_, ?_, ?_, lt_of_le_of_lt hZn hfin⟩
  · intro μ hμ
    obtain ⟨e, he, hid⟩ := hδΛ μ hμ
    refine ⟨e, he, ?_⟩
    have hμξ : herm X.Gm μ ξ = 0 := (AddMonoidHom.mem_ker.mp (AddSubgroup.mem_inf.mp hμ).2)
    have hI : X.embV μ ∈ X.Iperp ξ := fun τ => by
      show hermC τ.1 X.Gm (Data.emb τ.1 μ) (Data.emb τ.1 ξ) = 0
      rw [hemb, hμξ, map_zero]
    rw [hnap _ hI]; exact hid
  · exact hsplit r X ξ _ (X.lmulC h1 z0) (X.lmulC n (X.lmulC h1 z0)) lam δ hiso hsp1
      (fun u hu => hnap u hu) (fun u hu => hnJ u hu)
  · exact fun τ => ((hflag r X.toData (X.lmulC h1 z0) (X.xZ x0 Z1) n hfl1) τ).trans (hZfl τ)

end

end UnipMove
end
