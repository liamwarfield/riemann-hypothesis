module

public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.RealPlaceAnalysis.FinalF
public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SecondLabelsNonempty

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemUJsetOfKset
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace ComplexOrder

namespace GlobalTheory
namespace LowKProj

section General
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem fix_of_mem {E : H →L[ℂ] H} {S : Submodule ℂ H} (hE : IsOrthProjOnto E S) :
    ∀ x ∈ S, E x = x := by
  intro x hx
  obtain ⟨hidem, -, hrange⟩ := hE
  rw [← hrange] at hx
  obtain ⟨y, rfl⟩ := hx
  change E (E y) = E y
  rw [← ContinuousLinearMap.comp_apply, hidem]

theorem apply_mem {E : H →L[ℂ] H} {S : Submodule ℂ H} (hE : IsOrthProjOnto E S) (x : H) :
    E x ∈ S := by
  rw [← hE.2.2]
  exact ⟨x, rfl⟩

theorem norm_le_one {E : H →L[ℂ] H} {S : Submodule ℂ H} (hE : IsOrthProjOnto E S) :
    ‖E‖ ≤ 1 := by
  obtain ⟨hidem, hsym, -⟩ := hE
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  have hEE : E (E x) = E x := by rw [← ContinuousLinearMap.comp_apply, hidem]
  have hsq : ‖E x‖ ^ 2 ≤ ‖x‖ * ‖E x‖ := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), hsym, hEE]
    exact re_inner_le_norm x (E x)
  have h0 : 0 ≤ ‖x‖ := norm_nonneg x
  have h1 : 0 ≤ ‖E x‖ := norm_nonneg (E x)
  nlinarith

theorem exists_proj (S : Submodule ℂ H) [FiniteDimensional ℂ S] :
    ∃ E : H →L[ℂ] H, IsOrthProjOnto E S := by
  have : CompleteSpace S := FiniteDimensional.complete ℂ S
  refine ⟨S.starProjection, ?_, ?_, ?_⟩
  · exact S.isIdempotentElem_starProjection
  · exact S.inner_starProjection_left_eq_right
  · exact S.range_starProjection

theorem comm_of_stable {E A B : H →L[ℂ] H} {S : Submodule ℂ H} (hE : IsOrthProjOnto E S)
    (hAB : ∀ x y, ⟪A x, y⟫_ℂ = ⟪x, B y⟫_ℂ) (hA : ∀ v ∈ S, A v ∈ S) (hB : ∀ v ∈ S, B v ∈ S) :
    E ∘L A = A ∘L E := by
  have hfix := fix_of_mem hE
  have hmem := apply_mem hE
  have hsym := hE.2.1
  ext x
  simp only [ContinuousLinearMap.comp_apply]
  refine ext_inner_right ℂ fun y => ?_

  calc ⟪E (A x), y⟫_ℂ = ⟪A x, E y⟫_ℂ := hsym _ _
    _ = ⟪x, B (E y)⟫_ℂ := hAB _ _
    _ = ⟪x, E (B (E y))⟫_ℂ := by rw [hfix _ (hB _ (hmem y))]
    _ = ⟪E x, B (E y)⟫_ℂ := (hsym _ _).symm
    _ = ⟪A (E x), E y⟫_ℂ := (hAB _ _).symm
    _ = ⟪E (A (E x)), y⟫_ℂ := (hsym _ _).symm
    _ = ⟪A (E x), y⟫_ℂ := by rw [hfix _ (hA _ (hmem x))]

end General

theorem mem_UJset_of_Kset {n : ℕ} {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ}
    (hk : k ∈ Kset ε) : k ∈ UJset ε := by
  obtain ⟨hu, hc⟩ := hk
  have h2 : star k * k = 1 := (Matrix.mem_unitaryGroup_iff').1 hu
  show kᴴ * Jm ε * k = Jm ε
  rw [← Matrix.star_eq_conjTranspose, Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, h2, Matrix.one_mul]

private lemma star_mem_Kset {n : ℕ} {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ}
    (hk : k ∈ Kset ε) : star k ∈ Kset ε := by
  obtain ⟨hu, hc⟩ := hk
  have h1 : k * star k = 1 := (Matrix.mem_unitaryGroup_iff).1 hu
  have h2 : star k * k = 1 := (Matrix.mem_unitaryGroup_iff').1 hu
  refine ⟨(Matrix.mem_unitaryGroup_iff).2 (by rw [star_star]; exact h2), ?_⟩
  calc star k * Jm ε = star k * Jm ε * (k * star k) := by rw [h1, Matrix.mul_one]
    _ = star k * (Jm ε * k) * star k := by simp only [Matrix.mul_assoc]
    _ = star k * (k * Jm ε) * star k := by rw [hc]
    _ = (star k * k) * Jm ε * star k := by simp only [Matrix.mul_assoc]
    _ = Jm ε * star k := by rw [h2, Matrix.one_mul]

theorem inner_adj {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsURepOn (UJset ε) σ) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (x y : H) :
    ⟪σ k x, y⟫_ℂ = ⟪x, σ (star k) y⟫_ℂ := by
  obtain ⟨⟨h1, hmul⟩, hiso, -⟩ := hσ
  have hkU := mem_UJset_of_Kset hk
  have hsU := mem_UJset_of_Kset (star_mem_Kset hk)
  have hks : k * star k = 1 := (Matrix.mem_unitaryGroup_iff).1 hk.1

  let L : H →ₗᵢ[ℂ] H := ⟨(σ k : H →ₗ[ℂ] H), fun v => hiso k hkU v⟩
  have hy : σ k (σ (star k) y) = y := by
    rw [← ContinuousLinearMap.comp_apply, ← hmul k hkU (star k) hsU, hks, h1]
    rfl
  calc ⟪σ k x, y⟫_ℂ = ⟪L x, L (σ (star k) y)⟫_ℂ := by
        change ⟪σ k x, y⟫_ℂ = ⟪σ k x, σ k (σ (star k) y)⟫_ℂ
        rw [hy]
    _ = ⟪x, σ (star k) y⟫_ℂ := L.inner_map_map _ _

theorem lowKSub_stable {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) :
    IsKStableOn ε σ (lowKSub ε lam σ) := by
  intro g hg v hv

  have hle : lowKSub ε lam σ ≤ (lowKSub ε lam σ).comap (σ g : H →ₗ[ℂ] H) :=
    sSup_le fun S hS w hw => le_sSup hS (hS.2.1 g hg w hw)
  exact hle hv

theorem lowK_projection : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDS ε lam σ → (∃ w, IsHighestUnit ε lam σ w) ∧ IsKStableOn ε σ (lowKSub ε lam σ) ∧ (FiniteDimensional ℂ (lowKSub ε lam σ) → ∃ E : H →L[ℂ] H, IsOrthProjOnto E (lowKSub ε lam σ)) ∧ ∀ E : H →L[ℂ] H, IsOrthProjOnto E (lowKSub ε lam σ) → ‖E‖ ≤ 1 ∧ (∀ x ∈ lowKSub ε lam σ, E x = x) ∧ ∀ k ∈ Kset ε, E ∘L σ k = σ k ∘L E ∧ ‖σ k‖ ≤ 1 := by
  intro n ε lam H _ _ _ σ hDS
  obtain ⟨-, -, hrep, -, -, ⟨S, hS⟩, -⟩ := hDS
  refine ⟨?_, lowKSub_stable ε lam σ, fun _ => exists_proj _, ?_⟩
  ·
    obtain ⟨v, hvS, hv0, hwt⟩ := hS.2.2.2.1
    have hn : (‖v‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hv0
    refine ⟨((‖v‖ : ℂ)⁻¹) • v, ?_, ?_, ?_⟩
    · rw [norm_smul, norm_inv, Complex.norm_real, norm_norm]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.2 hv0)
    · have hle : S ≤ lowKSub ε lam σ :=
        le_sSup (show S ∈ {S | IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S} from hS)
      exact Submodule.smul_mem _ _ (hle hvS)
    · intro θ hθ
      rw [map_smul, hwt θ hθ, smul_comm]
  · intro E hE
    refine ⟨norm_le_one hE, fix_of_mem hE, fun k hk => ⟨?_, ?_⟩⟩
    · exact comm_of_stable hE (inner_adj hrep hk) (fun v hv => lowKSub_stable ε lam σ k hk v hv)
        (fun v hv => lowKSub_stable ε lam σ (star k) (star_mem_Kset hk) v hv)
    · exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
        rw [hrep.2.1 k (mem_UJset_of_Kset hk) x, one_mul]

end LowKProj
end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdFormsOfEquivariant
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct

namespace GlobalTheory

theorem adForms_of_equivariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (S : StepLevel F E σ J T f bad) (Γ Gi Gf : Type) [Group Γ] [Group Gi] [Group Gf] (ιi : Γ →* Gi) (ιf : Γ →* Gf) (K : Subgroup Gf) (ψ : K →* ℂˣ) (Φ : Gf ≃* UPts σ J (FiniteAdeleRing (𝓞 F) F)) (h0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (ι : Type) [Fintype ι] (emb : ι → E →+* ℂ) (lam : ι → DomWeight n) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (π : Representation ℂ Gi W) (Jm : W →ₗ⋆[ℂ] (Frames (gramC J emb) → ℂ)), (∀ κ : K, ‖((ψ κ : ℂˣ) : ℂ)‖ = 1) → (∀ h : Gf, h ∈ K ↔ ((h0⁻¹ * Φ h * h0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) ∈ S.U) → (∀ (h : Gf) (hk : h ∈ K) (hy : ((h0⁻¹ * Φ h * h0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) ∈ S.U), ((ψ ⟨h, hk⟩ : ℂˣ) : ℂ) = ((S.chi ⟨_, hy⟩ : ℂˣ) : ℂ)) → (∀ g : GL (Fin n) E, g ∈ UJ (σ : E →+* E) J → ∃ γ : Γ, (Φ (ιf γ)).1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) g) → (∀ (γ : Γ) (g : GL (Fin n) E), (Φ (ιf γ)).1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) g → ∀ (ξ : W) (y y' : Frames (gramC J emb)), IsTr (atInf emb g.1) y' y → Jm (π (ιi γ) ξ) y = Jm ξ y') → (∀ ξ, Jm ξ ∈ ValC (gramC J emb) lam) → ∀ φ : Gf → W, (∀ (γ : Γ) (x : Gf) (κ : K), φ (ιf γ * x * κ) = (((ψ κ)⁻¹ : ℂˣ) : ℂ) • π (ιi γ) (φ x)) → (fun y : UPts σ J (FiniteAdeleRing (𝓞 F) F) => Jm (φ (Φ.symm (y * h0⁻¹)))) ∈ AdForms S emb lam := by
  intro F E _ _ _ _ _ σ n J T f bad S Γ Gi Gf _ _ _ ιi ιf K ψ Φ h0 ι _ emb lam W _ _ π Jm hψ hK hχ hΓ hJ hV φ hφ
  refine Submodule.mem_inf.2 ⟨?_, fun x _ => hV _⟩
  intro g hg x x' κ hx y y' hy
  obtain ⟨γ, hγ⟩ := hΓ g hg
  let κ' : UPts σ J (FiniteAdeleRing (𝓞 F) F) := ⟨κ.1, ((S.U_eq κ.1).1 κ.2).1⟩
  let k : Gf := Φ.symm (h0 * κ' * h0⁻¹)
  have hk1 : h0⁻¹ * Φ k * h0 = κ' := by
    simp only [k, MulEquiv.apply_symm_apply]; group
  have hy1 : ((h0⁻¹ * Φ k * h0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) :
      GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) ∈ S.U := by
    rw [hk1]; exact κ.2
  have hk : k ∈ K := (hK k).2 hy1
  have hc : ((ψ ⟨k, hk⟩ : ℂˣ) : ℂ) = ((S.chi κ : ℂˣ) : ℂ) := by
    rw [hχ k hk hy1]
    congr 2
    apply Subtype.ext
    show ((h0⁻¹ * Φ k * h0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) :
      GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) = κ.1
    rw [hk1]
  have hx' : x' = Φ (ιf γ) * x * κ' := by
    apply Subtype.ext
    rw [hx, ← hγ]; rfl
  have hdec : Φ.symm (x' * h0⁻¹) = ιf γ * Φ.symm (x * h0⁻¹) * ((⟨k, hk⟩ : K) : Gf) := by
    apply Φ.injective
    simp only [k, map_mul Φ, MulEquiv.apply_symm_apply, hx']
    group
  have hconj : (starRingEnd ℂ) (((ψ ⟨k, hk⟩)⁻¹ : ℂˣ) : ℂ) = ((ψ ⟨k, hk⟩ : ℂˣ) : ℂ) := by
    rw [Units.val_inv_eq_inv_val, Complex.inv_eq_conj (hψ _), Complex.conj_conj]
  show Jm (φ (Φ.symm (x' * h0⁻¹))) y = (S.chi κ : ℂ) * Jm (φ (Φ.symm (x * h0⁻¹))) y'
  rw [hdec, hφ, LinearMap.map_smulₛₗ, hconj, hc, Pi.smul_apply, smul_eq_mul, hJ γ g hγ _ y y' hy]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalRankNumberBoundsRankClausesFirstHalf
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalRankNumberBoundsRankClausesFirstHalf
namespace GlobalTheory.Diag.PG

theorem rankNums_first_half : ∀ eps CD : ℝ, 0 < eps → eps < 1 / 52 → 3 ≤ CD → ∀ C : ℝ, ∃ x0 : ℝ, ∀ x, x0 ≤ x →
    ∀ m f k lrd Del : ℝ, RankNums x eps CD m f k lrd Del → C * m ^ 5 * f * x ^ eps ≤ k ∧
      Real.log f ≤ Real.sqrt (m / 2 - 1) ∧ C * x ^ eps ≤ f * Real.log k ∧ C * (m ^ 2 * x ^ eps) ≤ k ∧ C ≤ m ∧
      C * x ^ eps ≤ m - 1 ∧ C ≤ k ∧ 1 < x ^ eps := by
  intro eps CD heps heps' _ C
  set C1 : ℝ := max C 2 with hC1
  have hCC1 : C ≤ C1 := le_max_left _ _
  have hC12 : 2 ≤ C1 := le_max_right _ _
  have e1 : ∀ᶠ x : ℝ in Filter.atTop, C1 ≤ x ^ (eps / 2) :=
    (tendsto_rpow_atTop (by linarith)).eventually_ge_atTop C1
  have e2 : ∀ᶠ x : ℝ in Filter.atTop, C1 + 1 ≤ x ^ ((1 : ℝ) / 52) :=
    (tendsto_rpow_atTop (by norm_num)).eventually_ge_atTop (C1 + 1)
  have e3 : ∀ᶠ x : ℝ in Filter.atTop, (200 : ℝ) ≤ x ^ ((1 : ℝ) / 16) :=
    (tendsto_rpow_atTop (by norm_num)).eventually_ge_atTop 200
  have e4 : ∀ᶠ x : ℝ in Filter.atTop, (2 : ℝ) ≤ x := Filter.eventually_ge_atTop 2
  obtain ⟨x0, hx0⟩ := Filter.eventually_atTop.1 (e1.and (e2.and (e3.and e4)))
  refine ⟨x0, fun x hx m f k lrd Del h => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hx0 x hx
  have hx0' : (0 : ℝ) ≤ x := by linarith
  have hx1 : (1 : ℝ) < x := by linarith
  set A := x ^ eps with hA
  have hA1 : 1 < A := Real.one_lt_rpow hx1 heps
  set y := x ^ ((1 : ℝ) / 52) with hy
  have hAy : A ≤ y := Real.rpow_le_rpow_of_exponent_le hx1.le heps'.le
  set q := x ^ ((1 : ℝ) / 4) with hq
  have hqy : q = y ^ (13 : ℕ) := by
    rw [hq, hy, ← Real.rpow_natCast, ← Real.rpow_mul hx0']; norm_num
  have hy1 : 1 ≤ y := by linarith
  have hy13 : y ^ 2 ≤ y ^ (13 : ℕ) := pow_le_pow_right₀ hy1 (by norm_num)
  have hq_big : C1 * A + 1 ≤ q := by
    rw [hqy]; nlinarith
  have hm : C1 * A + 1 ≤ m := le_trans hq_big h.m_lo
  have hm1 : 1 ≤ m := by nlinarith
  have hm3 : 3 ≤ m := by nlinarith
  have hm4 : m ≤ m ^ 4 := by
    calc m = m ^ 1 := (pow_one m).symm
      _ ≤ m ^ 4 := pow_le_pow_right₀ hm1 (by norm_num)
  have hf : m ≤ f := le_trans hm4 h.mf
  have hf1 : 1 ≤ f := by linarith
  have hk : m ≤ k := le_trans hf h.fk
  have hCA : C * A ≤ C1 * A := mul_le_mul_of_nonneg_right hCC1 (by linarith)
  have hB0 : 0 ≤ m ^ 5 * f * A := by positivity
  have hk1 : C1 * (m ^ 5 * f * A) ≤ k :=
    le_trans (mul_le_mul_of_nonneg_right h1 hB0) h.k_lo
  have hm25 : m ^ 2 ≤ m ^ 5 * f := by
    have : m ^ 2 ≤ m ^ 5 := pow_le_pow_right₀ hm1 (by norm_num)
    nlinarith
  have hlogk : 1 ≤ Real.log k := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hC1A : C1 ≤ C1 * A := by
    have := mul_le_mul_of_nonneg_left hA1.le (by linarith : (0:ℝ) ≤ C1)
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hA1⟩
  · have : C * (m ^ 5 * f * A) ≤ C1 * (m ^ 5 * f * A) := mul_le_mul_of_nonneg_right hCC1 hB0
    calc C * m ^ 5 * f * A = C * (m ^ 5 * f * A) := by ring
      _ ≤ k := le_trans this hk1
  ·
    set t := x ^ ((1 : ℝ) / 16) with ht
    have hqt : q = t ^ (4 : ℕ) := by
      rw [hq, ht, ← Real.rpow_natCast, ← Real.rpow_mul hx0']; norm_num
    have hf0 : 0 < f := by linarith
    have hlf : Real.log f ≤ 5 * Real.log x := by
      have : Real.log f ≤ Real.log (x ^ (5 : ℝ)) :=
        Real.log_le_log hf0 (le_trans h.fk h.k_hi)
      rw [Real.log_rpow (by linarith)] at this
      exact this
    have hlx : Real.log x ≤ t / (1 / 16) := Real.log_le_rpow_div hx0' (by norm_num)
    have h80 : 80 * t ≤ Real.sqrt (m / 2 - 1) := by
      rw [Real.le_sqrt (by linarith)]
      have hmq : t ^ (4 : ℕ) ≤ m := hqt ▸ h.m_lo
      have ht2 : 40000 ≤ t ^ 2 := by nlinarith
      have ht4 : t ^ (4 : ℕ) = t ^ 2 * t ^ 2 := by ring
      have : (80 * t) ^ 2 = 6400 * t ^ 2 := by ring
      nlinarith
      all_goals linarith
    have : 5 * Real.log x ≤ 80 * t := by
      have : t / (1 / 16) = 16 * t := by ring
      linarith
    linarith
  · calc C * A ≤ C1 * A := hCA
      _ ≤ m := by linarith
      _ ≤ f := hf
      _ = f * 1 := (mul_one f).symm
      _ ≤ f * Real.log k := mul_le_mul_of_nonneg_left hlogk (by linarith)
  · have hB2 : 0 ≤ m ^ 2 * A := by positivity
    calc C * (m ^ 2 * A) ≤ C1 * (m ^ 2 * A) := mul_le_mul_of_nonneg_right hCC1 hB2
      _ ≤ C1 * (m ^ 5 * f * A) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        exact mul_le_mul_of_nonneg_right hm25 (by linarith)
      _ ≤ k := hk1
  · linarith
  · linarith
  · linarith

end GlobalTheory.Diag.PG
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalRankNumberBoundsRankClausesFirstHalfStatement
open GlobalTheory.Diag.PG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_rankNums_imp_parameter_lower_bounds : ∀ eps CD : ℝ, 0 < eps → eps < 1 / 52 → 3 ≤ CD → ∀ C : ℝ, ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ m f k lrd Del : ℝ, RankNums x eps CD m f k lrd Del → C * m ^ 5 * f * x ^ eps ≤ k ∧ Real.log f ≤ Real.sqrt (m / 2 - 1) ∧ C * x ^ eps ≤ f * Real.log k ∧ C * (m ^ 2 * x ^ eps) ≤ k ∧ C ≤ m ∧ C * x ^ eps ≤ m - 1 ∧ C ≤ k ∧ 1 < x ^ eps := by
  first | exact @GlobalTheory.Diag.PG.rankNums_first_half | exact GlobalTheory.Diag.PG.rankNums_first_half | (intros; apply GlobalTheory.Diag.PG.rankNums_first_half <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalRankNumberBoundsSizeComparisons
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalRankNumberBoundsSizeComparisons
open GlobalTheory.Diag.PG Filter

noncomputable section

namespace GlobalTheory.Diag.PG.SqrtBound

theorem poly_ineq {t K a : ℝ} (ht2 : 2 ≤ t) (htK : K ≤ t) (ha : a ≤ K) : a * t + t ^ 2 ≤ t ^ 4 / 2 := by
  have ht0 : 0 ≤ t := by linarith
  have hat : a * t ≤ t * t := mul_le_mul_of_nonneg_right (ha.trans htK) ht0
  have h4 : 4 ≤ t ^ 2 := by nlinarith
  nlinarith

theorem scale_facts {eps x : ℝ} (heps : 0 < eps) (hx : 1 ≤ x) :
    Real.log x ≤ 4 * x ^ (eps / 4) / eps ∧ x ^ (eps / 2) = (x ^ (eps / 4)) ^ 2 ∧
      x ^ eps = (x ^ (eps / 4)) ^ 4 := by
  have hx0 : 0 ≤ x := by linarith
  refine ⟨?_, ?_, ?_⟩
  · have h := Real.log_le_rpow_div hx0 (by positivity : 0 < eps / 4)
    calc Real.log x ≤ x ^ (eps / 4) / (eps / 4) := h
      _ = 4 * x ^ (eps / 4) / eps := by field_simp
  · rw [← Real.rpow_mul_natCast hx0]; push_cast; ring_nf
  · rw [← Real.rpow_mul_natCast hx0]; push_cast; ring_nf

theorem exp_bound {eps A x K : ℝ} (heps : 0 < eps) (hA : 0 < A) (hx : 1 ≤ x)
    (ht2 : 2 ≤ x ^ (eps / 4)) (htK : K ≤ x ^ (eps / 4)) (hK : |Real.log A| + 40 / eps ≤ K) :
    A * x ^ 10 * Real.exp (x ^ (eps / 2)) ≤ Real.exp (x ^ eps / 2) := by
  have hx0 : 0 < x := by linarith
  obtain ⟨hlog, h2, h4⟩ := scale_facts heps hx
  set t := x ^ (eps / 4) with ht
  have hp := poly_ineq (a := |Real.log A| + 40 / eps) ht2 htK hK
  have h1 : Real.log A ≤ |Real.log A| := le_abs_self _
  have h3 : |Real.log A| ≤ |Real.log A| * t := le_mul_of_one_le_right (abs_nonneg _) (by linarith)
  have h5 : 10 * Real.log x ≤ 40 / eps * t := by
    calc 10 * Real.log x ≤ 10 * (4 * t / eps) := by linarith
      _ = 40 / eps * t := by ring
  have key : Real.log A + 10 * Real.log x + t ^ 2 ≤ t ^ 4 / 2 := by nlinarith
  have e10 : Real.exp (10 * Real.log x) = x ^ 10 := by
    rw [show (10 : ℝ) * Real.log x = Real.log (x ^ 10) by rw [Real.log_pow]; norm_num]
    exact Real.exp_log (by positivity)
  calc A * x ^ 10 * Real.exp (x ^ (eps / 2))
        = Real.exp (Real.log A + 10 * Real.log x + x ^ (eps / 2)) := by
          rw [Real.exp_add, Real.exp_add, Real.exp_log hA, e10]
    _ ≤ Real.exp (x ^ eps / 2) := Real.exp_le_exp.2 (by rw [h2, h4]; linarith)

theorem log_bound {eps C x K : ℝ} (heps : 0 < eps) (hC : 0 ≤ C) (hx : 1 ≤ x)
    (ht2 : 2 ≤ x ^ (eps / 4)) (htK : K ≤ x ^ (eps / 4)) (hK : 20 * C / eps ≤ K) :
    Real.log x * (5 * C) ≤ x ^ eps / 2 := by
  obtain ⟨hlog, -, h4⟩ := scale_facts heps hx
  set t := x ^ (eps / 4) with ht
  have ht0 : 0 ≤ t := by linarith
  have hp := poly_ineq (a := 20 * C / eps) ht2 htK hK
  have hat : 0 ≤ 20 * C / eps * t := by positivity
  have h1 : Real.log x * (5 * C) ≤ 4 * t / eps * (5 * C) :=
    mul_le_mul_of_nonneg_right hlog (by positivity)
  have h2 : 4 * t / eps * (5 * C) = 20 * C / eps * t := by ring
  rw [h4]
  nlinarith

theorem rankNums_sizes : ∀ eps CD : ℝ, 0 < eps → eps < 1 / 52 → 3 ≤ CD → ∀ C : ℝ, 0 < C → ∃ x0 : ℝ, ∀ x, x0 ≤ x →
    ∀ m f k lrd Del : ℝ, RankNums x eps CD m f k lrd Del → 1 ≤ Del ∧ C * (m * k * Del) ≤ Real.sqrt (bx x eps) ∧
      max (k ^ C) (bx x eps ^ ((1 : ℝ) / 4)) ≤ Real.sqrt (bx x eps) ∧ 12 * k * Del ≤ Real.sqrt (bx x eps) ∧
      Real.sqrt (bx x eps) ≤ bx x eps ^ 2 ∧ bx x eps ^ 2 ≤ bx x eps ^ (3 : ℝ) ∧
      (C ≤ CD → (k * f * x ^ eps) ^ C ≤ Del) := by
  intro eps CD heps _ hCD C hC
  set K0 := max (max 2 (|Real.log C| + 40 / eps)) (max (|Real.log 12| + 40 / eps) (20 * C / eps)) with hK0
  have hK0pos : 0 ≤ K0 := le_trans (by norm_num) (le_trans (le_max_left _ _) (le_max_left _ _))
  refine ⟨max 1 (K0 ^ (4 / eps)), ?_⟩
  intro x hx m f k lrd Del h
  have hx1 : 1 ≤ x := le_trans (le_max_left _ _) hx
  have hx0 : 0 < x := by linarith
  have htK0 : K0 ≤ x ^ (eps / 4) := by
    have h1 : K0 ^ (4 / eps) ≤ x := le_trans (le_max_right _ _) hx
    have h2 := Real.rpow_le_rpow (by positivity) h1 (by positivity : (0 : ℝ) ≤ eps / 4)
    rwa [← Real.rpow_mul hK0pos, show 4 / eps * (eps / 4) = (1 : ℝ) by field_simp, Real.rpow_one] at h2
  have ht2 : 2 ≤ x ^ (eps / 4) := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) htK0
  have htA : |Real.log C| + 40 / eps ≤ x ^ (eps / 4) := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) htK0
  have ht12 : |Real.log 12| + 40 / eps ≤ x ^ (eps / 4) := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) htK0
  have htC : 20 * C / eps ≤ x ^ (eps / 4) := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) htK0

  have hm1 : 1 ≤ m := le_trans (Real.one_le_rpow hx1 (by norm_num)) h.m_lo
  have hm4 : m ≤ m ^ 4 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hm1 3]
  have hf1 : 1 ≤ f := le_trans (by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hm1 4]) h.mf
  have hk1 : 1 ≤ k := le_trans hf1 h.fk
  have hk5 : k ≤ x ^ 5 := by
    have := h.k_hi
    rwa [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at this
  have hm5 : m ≤ x ^ 5 := le_trans (le_trans hm4 (le_trans h.mf h.fk)) hk5
  have hxe1 : 1 ≤ x ^ eps := Real.one_le_rpow hx1 heps.le

  have hB1 : 1 ≤ k * f * x ^ eps := by
    have : 1 ≤ k * f := by nlinarith
    nlinarith
  have hDel1 : 1 ≤ Del := le_trans (Real.one_le_rpow hB1 (by linarith)) h.Del_lo
  have hDelE : Del ≤ Real.exp (x ^ (eps / 2)) :=
    (Real.log_le_iff_le_exp (by linarith)).1 h.Del_hi

  have hsq : Real.sqrt (bx x eps) = Real.exp (x ^ eps / 2) := by
    rw [Real.sqrt_eq_rpow, bx, ← Real.exp_mul]; ring_nf
  have hE0 : 0 ≤ Real.exp (x ^ (eps / 2)) := (Real.exp_pos _).le
  have hx10 : m * k ≤ x ^ 10 := by
    have : x ^ 10 = x ^ 5 * x ^ 5 := by ring
    rw [this]; exact mul_le_mul hm5 hk5 (by linarith) (by positivity)
  have hb1 : 1 ≤ bx x eps := Real.one_le_exp (by positivity)
  refine ⟨hDel1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsq]
    calc C * (m * k * Del) ≤ C * x ^ 10 * Real.exp (x ^ (eps / 2)) := by
          rw [mul_assoc C]
          exact mul_le_mul_of_nonneg_left (mul_le_mul hx10 hDelE (by linarith) (by positivity)) hC.le
      _ ≤ Real.exp (x ^ eps / 2) := exp_bound heps hC hx1 ht2 htA le_rfl
  · rw [hsq]
    refine max_le ?_ ?_
    · have hk0 : 0 < k := by linarith
      rw [Real.rpow_def_of_pos hk0]
      refine Real.exp_le_exp.2 (le_trans ?_ (log_bound heps hC.le hx1 ht2 htC le_rfl))
      have hlk : Real.log k ≤ 5 * Real.log x := by
        have h5 := Real.log_le_log hk0 hk5
        rw [Real.log_pow] at h5; push_cast at h5; linarith
      nlinarith
    · rw [bx, ← Real.exp_mul]
      exact Real.exp_le_exp.2 (by nlinarith [Real.rpow_nonneg hx0.le eps])
  · rw [hsq]
    calc 12 * k * Del ≤ 12 * x ^ 10 * Real.exp (x ^ (eps / 2)) := by
          have hk10 : k ≤ x ^ 10 := le_trans hk5 (pow_le_pow_right₀ hx1 (by norm_num))
          rw [mul_assoc, mul_assoc (12 : ℝ)]
          exact mul_le_mul_of_nonneg_left (mul_le_mul hk10 hDelE (by linarith) (by positivity)) (by norm_num)
      _ ≤ Real.exp (x ^ eps / 2) := exp_bound heps (by norm_num) hx1 ht2 ht12 le_rfl
  · rw [hsq, bx, ← Real.exp_nat_mul]
    exact Real.exp_le_exp.2 (by push_cast; nlinarith [Real.rpow_nonneg hx0.le eps])
  · rw [show bx x eps ^ 2 = bx x eps ^ ((2 : ℕ) : ℝ) from (Real.rpow_natCast _ 2).symm]
    exact Real.rpow_le_rpow_of_exponent_le hb1 (by norm_num)
  · intro hCC
    exact le_trans (Real.rpow_le_rpow_of_exponent_le hB1 hCC) h.Del_lo

end GlobalTheory.Diag.PG.SqrtBound

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalRankNumberBoundsSizeComparisonsStatement
open GlobalTheory.Diag.PG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.globalRankNumberBounds_size_comparisons : ∀ eps CD : ℝ, 0 < eps → eps < 1 / 52 → 3 ≤ CD → ∀ C : ℝ, 0 < C → ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ m f k lrd Del : ℝ, RankNums x eps CD m f k lrd Del → 1 ≤ Del ∧ C * (m * k * Del) ≤ Real.sqrt (bx x eps) ∧ max (k ^ C) (bx x eps ^ ((1 : ℝ) / 4)) ≤ Real.sqrt (bx x eps) ∧ 12 * k * Del ≤ Real.sqrt (bx x eps) ∧ Real.sqrt (bx x eps) ≤ bx x eps ^ 2 ∧ bx x eps ^ 2 ≤ bx x eps ^ (3 : ℝ) ∧ (C ≤ CD → (k * f * x ^ eps) ^ C ≤ Del) := by
  first | exact @GlobalTheory.Diag.PG.SqrtBound.rankNums_sizes | exact GlobalTheory.Diag.PG.SqrtBound.rankNums_sizes | (intros; apply GlobalTheory.Diag.PG.SqrtBound.rankNums_sizes <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormExpSubOneLeExpNorm
open Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants

namespace GlobalTheory

namespace NearUnitaryExp

open scoped Matrix.Norms.Frobenius

theorem norm_exp_sub_one_le_exp_norm {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] (x : A) : ‖NormedSpace.exp x - 1‖ ≤ Real.exp ‖x‖ - 1 := by
  have hx := (hasSum_nat_add_iff' 1).mpr (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) x)
  have hr := (hasSum_nat_add_iff' 1).mpr (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) ‖x‖)
  rw [← Real.exp_eq_exp_ℝ] at hr
  simp only [Finset.range_one, Finset.sum_singleton, Nat.factorial_zero, Nat.cast_one, inv_one,
    pow_zero, one_smul] at hx hr
  refine hx.norm_le_of_bounded hr fun m => ?_
  rw [norm_smul, smul_eq_mul, norm_inv, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left (norm_pow_le' x (Nat.succ_pos m)) (by positivity)

variable {n : ℕ}

theorem sqrt_hs_eq_norm (A : Matrix (Fin n) (Fin n) ℂ) : Real.sqrt (hs A) = ‖A‖ := by
  rw [frobenius_norm_def, Real.sqrt_eq_rpow, hs]
  simp only [Real.rpow_two]

theorem hs_nonneg' (A : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ hs A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem norm_sq_eq_hs (A : Matrix (Fin n) (Fin n) ℂ) : ‖A‖ ^ 2 = hs A := by
  rw [← sqrt_hs_eq_norm, Real.sq_sqrt (hs_nonneg' A)]

private lemma re_star_mul_self_eq_norm_sq (z : ℂ) : (star z * z).re = ‖z‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.star_def, Complex.conj_re,
    Complex.conj_im]
  ring

theorem hs_eq_re_trace (g : Matrix (Fin n) (Fin n) ℂ) : hs g = (trace (gᴴ * g)).re := by
  simp only [hs, trace, Matrix.diag, Matrix.mul_apply, conjTranspose_apply, Complex.re_sum,
    re_star_mul_self_eq_norm_sq]
  exact Finset.sum_comm

theorem norm_unitary_mul {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (A : Matrix (Fin n) (Fin n) ℂ) : ‖k * A‖ = ‖A‖ := by
  have hk' : kᴴ * k = 1 := Matrix.mem_unitaryGroup_iff'.mp hk
  rw [← sqrt_hs_eq_norm, ← sqrt_hs_eq_norm, hs_eq_re_trace, hs_eq_re_trace, conjTranspose_mul,
    Matrix.mul_assoc, ← Matrix.mul_assoc kᴴ k A, hk', Matrix.one_mul]

theorem norm_one_eq : ‖(1 : Matrix (Fin n) (Fin n) ℂ)‖ = Real.sqrt n := by
  rw [← sqrt_hs_eq_norm, hs_eq_re_trace]
  simp

theorem norm_trace_le (A : Matrix (Fin n) (Fin n) ℂ) : ‖A.trace‖ ≤ Real.sqrt n * ‖A‖ := by
  have hdiag : ∑ i, ‖A i i‖ ^ 2 ≤ hs A :=
    Finset.sum_le_sum fun i _ =>
      Finset.single_le_sum (f := fun j => ‖A i j‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  have hsq : (∑ i, ‖A i i‖) ^ 2 ≤ (Real.sqrt n * ‖A‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n), norm_sq_eq_hs]
    calc (∑ i, ‖A i i‖) ^ 2 ≤ (Finset.univ.card : ℝ) * ∑ i, ‖A i i‖ ^ 2 :=
          sq_sum_le_card_mul_sum_sq
      _ ≤ n * hs A := by
          rw [Finset.card_univ, Fintype.card_fin]
          exact mul_le_mul_of_nonneg_left hdiag (Nat.cast_nonneg n)
  have h1 : ‖A.trace‖ ≤ ∑ i, ‖A i i‖ := norm_sum_le _ _
  have h2 : 0 ≤ ∑ i, ‖A i i‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have h3 : 0 ≤ Real.sqrt n * ‖A‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  nlinarith

theorem hs_unitary_sub_one {k : Matrix (Fin n) (Fin n) ℂ}
    (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) : hs (k - 1) = 2 * n - 2 * k.trace.re := by
  have hk' : kᴴ * k = 1 := Matrix.mem_unitaryGroup_iff'.mp hk
  have hprod : (k - 1)ᴴ * (k - 1) = 1 + 1 - kᴴ - k := by
    rw [conjTranspose_sub, conjTranspose_one, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hk',
      Matrix.one_mul, Matrix.mul_one, Matrix.one_mul]
    abel
  rw [hs_eq_re_trace, hprod, trace_sub, trace_sub, trace_add, trace_one, trace_conjTranspose,
    Complex.sub_re, Complex.sub_re, Complex.add_re, Complex.star_def, Complex.conj_re,
    Fintype.card_fin, Complex.natCast_re]
  ring

theorem norm_pow_le_of_unitary {k : Matrix (Fin n) (Fin n) ℂ}
    (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) (E : Matrix (Fin n) (Fin n) ℂ) {c : ℝ}
    (hE : ‖E - 1‖ ≤ c - 1) (j : ℕ) : ‖(k * E) ^ j‖ ≤ c ^ j * Real.sqrt n := by
  induction j with
  | zero => rw [pow_zero, pow_zero, one_mul, norm_one_eq]
  | succ j ih =>
    have hsplit : E * (k * E) ^ j = (k * E) ^ j + (E - 1) * (k * E) ^ j := by
      rw [Matrix.sub_mul, Matrix.one_mul]
      abel
    rw [pow_succ', Matrix.mul_assoc, norm_unitary_mul hk, hsplit]
    have hm := frobenius_norm_mul (E - 1) ((k * E) ^ j)
    have hn0 := norm_nonneg ((k * E) ^ j)
    have hE0 := norm_nonneg (E - 1)
    calc ‖(k * E) ^ j + (E - 1) * (k * E) ^ j‖
        ≤ ‖(k * E) ^ j‖ + ‖(E - 1) * (k * E) ^ j‖ := norm_add_le _ _
      _ ≤ (1 + ‖E - 1‖) * ‖(k * E) ^ j‖ := by linarith
      _ ≤ c * (c ^ j * Real.sqrt n) := by
          apply mul_le_mul (by linarith) ih hn0 (by linarith)
      _ = c ^ (j + 1) * Real.sqrt n := by ring

theorem near_arch : ∀ (n : ℕ) (k X : Matrix (Fin n) (Fin n) ℂ) (ep : ℝ), k ∈ Matrix.unitaryGroup (Fin n) ℂ → X.IsHermitian → 0 ≤ ep → Real.sqrt (hs X) ≤ ep → n * ep ≤ 1 / 4 → (∀ j : ℕ, j ≤ n → ‖((k * NormedSpace.exp X) ^ j).trace - n‖ ≤ 3 * n) ∧ ((k * NormedSpace.exp X).trace = n → Real.sqrt (hs (k * NormedSpace.exp X - 1)) ≤ 3 * Real.sqrt (n * ep)) := by
  intro n k X ep hk _ hep hXe hne
  have hXn : ‖X‖ ≤ ep := by rwa [sqrt_hs_eq_norm] at hXe
  have hE1 : ‖NormedSpace.exp X - 1‖ ≤ Real.exp ep - 1 := by
    have h1 := norm_exp_sub_one_le_exp_norm X
    have h2 := Real.exp_le_exp.mpr hXn
    exact le_trans h1 (by linarith)
  generalize NormedSpace.exp X = E at hE1 ⊢
  have hpow := norm_pow_le_of_unitary hk E hE1
  have hq : Real.exp (1 / 4) ≤ 3 / 2 := by
    have h := Real.abs_exp_sub_one_le (x := 1 / 4) (by norm_num [abs_of_pos])
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)] at h
    linarith [le_abs_self (Real.exp (1 / 4) - 1)]
  have hsn : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt (Nat.cast_nonneg n)
  refine ⟨fun j hj => ?_, fun htr => ?_⟩
  · have hje : (j : ℝ) * ep ≤ 1 / 4 := by
      have : (j : ℝ) ≤ n := by exact_mod_cast hj
      nlinarith
    have hcj : Real.exp ep ^ j ≤ 3 / 2 := by
      rw [← Real.exp_nat_mul]
      exact (Real.exp_le_exp.mpr hje).trans hq
    have htr := norm_trace_le ((k * E) ^ j)
    have hb := hpow j
    have hs0 := Real.sqrt_nonneg (n : ℝ)
    have hbound : ‖((k * E) ^ j).trace‖ ≤ n * (3 / 2) := by
      calc ‖((k * E) ^ j).trace‖ ≤ Real.sqrt n * ‖(k * E) ^ j‖ := htr
        _ ≤ Real.sqrt n * (Real.exp ep ^ j * Real.sqrt n) := mul_le_mul_of_nonneg_left hb hs0
        _ = (Real.sqrt n * Real.sqrt n) * Real.exp ep ^ j := by ring
        _ = n * Real.exp ep ^ j := by rw [hsn]
        _ ≤ n * (3 / 2) := mul_le_mul_of_nonneg_left hcj (Nat.cast_nonneg n)
    calc ‖((k * E) ^ j).trace - n‖ ≤ ‖((k * E) ^ j).trace‖ + ‖(n : ℂ)‖ := norm_sub_le _ _
      _ ≤ 3 * n := by rw [Complex.norm_natCast]; linarith
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hs]
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hs1 : 1 ≤ Real.sqrt n := Real.one_le_sqrt.mpr hn1
    set s := Real.sqrt n with hs_def
    set t := Real.sqrt ep with ht_def
    have ht0 : 0 ≤ t := Real.sqrt_nonneg _
    have htt : t * t = ep := Real.mul_self_sqrt hep
    have hst : s * t ≤ 1 / 2 := by
      have : (s * t) * (s * t) ≤ 1 / 4 := by
        calc (s * t) * (s * t) = (s * s) * (t * t) := by ring
          _ = n * ep := by rw [hsn, htt]
          _ ≤ 1 / 4 := hne
      nlinarith
    have hep1 : ep ≤ 1 := by nlinarith
    have hdel : ‖E - 1‖ ≤ 2 * ep := by
      have h := Real.abs_exp_sub_one_le (x := ep) (by rw [abs_of_nonneg hep]; exact hep1)
      rw [abs_of_nonneg hep] at h
      linarith [le_abs_self (Real.exp ep - 1)]
    have hsplit : k * E = k + k * (E - 1) := by
      rw [Matrix.mul_sub, Matrix.mul_one]
      abel
    have htrk : k.trace = n - (k * (E - 1)).trace := by
      rw [← htr, hsplit, trace_add]
      ring
    have hre : (n : ℝ) - s * ‖E - 1‖ ≤ k.trace.re := by
      have h1 := norm_trace_le (k * (E - 1))
      rw [norm_unitary_mul hk, ← hs_def] at h1
      have h2 := Complex.abs_re_le_norm (k * (E - 1)).trace
      rw [htrk, Complex.sub_re, Complex.natCast_re]
      linarith [le_abs_self (k * (E - 1)).trace.re]
    have hk1 : ‖k - 1‖ ^ 2 ≤ 4 * (s * t) ^ 2 := by
      rw [norm_sq_eq_hs, hs_unitary_sub_one hk]
      have hE0 := norm_nonneg (E - 1)
      have : s * ‖E - 1‖ ≤ s * (2 * (t * t)) := by
        rw [htt]; exact mul_le_mul_of_nonneg_left hdel (by linarith)
      nlinarith
    have hk1' : ‖k - 1‖ ≤ 2 * (s * t) := by
      have := norm_nonneg (k - 1)
      have hst0 : 0 ≤ s * t := mul_nonneg (by linarith) ht0
      nlinarith
    have hsum : k * E - 1 = (k - 1) + k * (E - 1) := by
      rw [hsplit]
      abel
    rw [sqrt_hs_eq_norm, Real.sqrt_mul (Nat.cast_nonneg n), hsum]
    calc ‖(k - 1) + k * (E - 1)‖ ≤ ‖k - 1‖ + ‖k * (E - 1)‖ := norm_add_le _ _
      _ ≤ 2 * (s * t) + 2 * (t * t) := by rw [norm_unitary_mul hk, htt]; linarith
      _ ≤ 3 * (s * t) := by nlinarith

end NearUnitaryExp

end GlobalTheory
end
