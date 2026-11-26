module

public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsAdelicMatrix
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StrongApproximation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexConjIsometryFlagDomainGroupNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitModulusConstantsEquivariantDictionary

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCongruenceDetEqOneOfThreeLe
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCongruenceDetEqOneOfThreeLe
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

open Matrix Polynomial

namespace GlobalTheory.UnitaryCongruenceDetAny

theorem det_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r M : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (γ : GL (Fin r) E), 3 ≤ M → G.det ≠ 0 → Λ.FG → Submodule.span E (Λ : Set (Fin r → E)) = ⊤ → IsUStab G Λ γ → (∀ x ∈ Λ, ∃ y ∈ Λ, (γ : Matrix (Fin r) (Fin r) E).mulVec x - x = M • y) → (γ : Matrix (Fin r) (Fin r) E).det = 1 := by
  intro E _ _ _ r M G Λ γ hM hG hfg hspan hst hcong
  classical
  obtain ⟨hherm, -⟩ := hst
  set g : Matrix (Fin r) (Fin r) E := (γ : Matrix (Fin r) (Fin r) E) with hg
  let φ : E →+* AlgebraicClosure E := algebraMap E (AlgebraicClosure E)
  have hM0 : (M : AlgebraicClosure E) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  have hME : (M : E) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  set A : Matrix (Fin r) (Fin r) E := (M : E)⁻¹ • (g - 1) with hA
  have hAΛ : ∀ x ∈ Λ, A *ᵥ x ∈ Λ := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hcong x hx
    have : A *ᵥ x = y := by
      rw [hA, smul_mulVec, sub_mulVec, one_mulVec, hxy, ← Nat.cast_smul_eq_nsmul E,
        smul_smul, inv_mul_cancel₀ hME, one_smul]
    rw [this]; exact hy
  have hAmap : A.map φ = (M : AlgebraicClosure E)⁻¹ • (g.map φ - 1) := by
    ext i j
    by_cases hij : i = j <;> simp [hA, Matrix.one_apply, hij]
  have hroot : ∀ l ∈ (g.map φ).charpoly.roots,
      IsIntegral ℤ ((l - 1) / (M : AlgebraicClosure E)) := by
    intro l hl
    have hdet : (scalar (Fin r) l - g.map φ).det = 0 := by
      rw [← Matrix.eval_charpoly]; exact (mem_roots'.1 hl).2
    obtain ⟨u, hu, hu0⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hdet
    apply GlobalTheory.UnitaryCongruenceDet.isIntegral_of_left_eigen A Λ hfg hspan hAΛ _ u hu
    have hgu : u ᵥ* g.map φ = l • u := by
      rw [vecMul_sub, sub_eq_zero] at hu0
      rw [← hu0]
      funext j
      simp [scalar_apply, vecMul_diagonal, mul_comm]
    rw [hAmap, vecMul_smul, vecMul_sub, vecMul_one, hgu]
    funext j
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    field_simp
  obtain ⟨z, hz, hprod⟩ := GlobalTheory.UnitaryCongruenceDet.prod_eq_one_add M hM0 _ hroot
  have hφdet : φ g.det = 1 + M * z := by
    rw [RingHom.map_det, ← hprod]
    exact Matrix.det_eq_prod_roots_charpoly _

  set z₀ : E := (g.det - 1) / (M : E) with hz₀
  have hφz : φ z₀ = z := by
    rw [hz₀, map_div₀, map_sub, map_one, map_natCast, hφdet]
    field_simp
    ring
  have hz₀int : IsIntegral ℤ z₀ := by
    have h1 : IsIntegral ℤ (φ z₀) := by rw [hφz]; exact hz
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ E (AlgebraicClosure E))
      (algebraMap E (AlgebraicClosure E)).injective).1 h1

  have hcc := GlobalTheory.UnitaryCongruenceDet.det_mul_cc_det G g hG hherm
  have hnorm : ∀ ψ : E →+* ℂ, ‖ψ g.det‖ = 1 := by
    intro ψ
    have h1 := congrArg ψ hcc
    rw [map_mul, map_one, cc, IsCMField.complexEmbedding_complexConj, Complex.mul_conj] at h1
    have h2 : Complex.normSq (ψ g.det) = 1 := by exact_mod_cast h1
    rw [Complex.normSq_eq_norm_sq] at h2
    exact (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).1 (h2.trans (one_pow 2).symm)

  have hsmall : ∀ ψ : E →+* ℂ, ‖ψ z₀‖ < 1 := by
    intro ψ
    have hMR : (3 : ℝ) ≤ M := by exact_mod_cast hM
    rw [hz₀, map_div₀, map_sub, map_one, map_natCast, norm_div, Complex.norm_natCast,
      div_lt_one (by linarith)]
    calc ‖ψ g.det - 1‖ ≤ ‖ψ g.det‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [hnorm, norm_one]; norm_num
      _ < M := by linarith
  have hz0 : z₀ = 0 := by
    by_contra hne
    let α : 𝓞 E := ⟨z₀, hz₀int⟩
    have hα : α ≠ 0 := by
      intro h; apply hne
      have := congrArg (fun a : 𝓞 E => (a : E)) h
      exact this
    obtain ⟨σ, hσ⟩ := NumberField.exists_conjugate_one_le_norm hα
    exact absurd hσ (not_le.2 (hsmall σ))
  have : g.det - 1 = 0 := by
    have h := hz0
    rw [hz₀, div_eq_zero_iff] at h
    exact h.resolve_right hME
  exact sub_eq_zero.1 this

end GlobalTheory.UnitaryCongruenceDetAny
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCongruenceDetEqOneOfThreeLeStatement
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryCongruence_det_eq_one_of_three_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r M : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (γ : GL (Fin r) E), 3 ≤ M → G.det ≠ 0 → Λ.FG → Submodule.span E (Λ : Set (Fin r → E)) = ⊤ → IsUStab G Λ γ → (∀ x ∈ Λ, ∃ y ∈ Λ, (γ : Matrix (Fin r) (Fin r) E).mulVec x - x = M • y) → (γ : Matrix (Fin r) (Fin r) E).det = 1 := by
  first | exact @GlobalTheory.UnitaryCongruenceDetAny.det_eq_one | exact GlobalTheory.UnitaryCongruenceDetAny.det_eq_one | (intros; apply GlobalTheory.UnitaryCongruenceDetAny.det_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagDomainDataOfFiniteIndexSubgroup
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagDomainDataOfFiniteIndexSubgroup
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.EqCovol

theorem exists_data_of_le_relIndex_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (r : ℕ) (X : Data E r) (Δ : Subgroup (GL (Fin r) E)), Δ ≤ X.Γ → Δ.relIndex X.Γ ≠ 0 →
    ∃ P : Data E r, P.Ψ = X.Ψ ∧ P.Gm = X.Gm ∧ P.p0 = X.p0 ∧ P.Γ = Δ := by
  intro E _ _ _ r X Δ hle hidx
  classical
  have hT : ∃ T : Finset (GL (Fin r) E), ∀ g ∈ X.Γ, ∃ t ∈ T, t⁻¹ * g ∈ Δ := by
    letI := Subgroup.fintypeOfIndexNeZero hidx
    refine ⟨Finset.univ.image
      (fun q : X.Γ ⧸ Δ.subgroupOf X.Γ => ((Quotient.out q : X.Γ) : GL (Fin r) E)), ?_⟩
    intro g hg
    set q : X.Γ ⧸ Δ.subgroupOf X.Γ := QuotientGroup.mk (⟨g, hg⟩ : X.Γ) with hq
    refine ⟨((Quotient.out q : X.Γ) : GL (Fin r) E),
      Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
    have h : ((Quotient.out q : X.Γ) : X.Γ ⧸ Δ.subgroupOf X.Γ) = QuotientGroup.mk (⟨g, hg⟩ : X.Γ) :=
      QuotientGroup.out_eq' q
    have h2 := QuotientGroup.eq.mp h
    rw [Subgroup.mem_subgroupOf] at h2
    simpa using h2
  obtain ⟨T, hT⟩ := hT
  obtain ⟨S, hS⟩ := X.Γ_index
  refine ⟨{ X with
    Γ := Δ
    Γ_stab := fun γ hγ => X.Γ_stab γ (hle hγ)
    Γ_index := ⟨(S ×ˢ T).image (fun p => p.1 * p.2), by
      intro γ hγ
      obtain ⟨s, hs, h1⟩ := hS γ hγ
      obtain ⟨t, ht, h2⟩ := hT _ h1
      refine ⟨s * t, Finset.mem_image.mpr ⟨(s, t), Finset.mem_product.mpr ⟨hs, ht⟩, rfl⟩, ?_⟩
      rw [mul_inv_rev, mul_assoc]
      exact h2⟩
    Γ_free := fun γ hγ => X.Γ_free γ (hle hγ)
    χ_mul := fun la γ hγ γ' hγ' => X.χ_mul la γ (hle hγ) γ' (hle hγ')
    χ_add := fun la la' γ hγ => X.χ_add la la' γ (hle hγ)
    χ_fin := fun la => by
      obtain ⟨n, hn, h⟩ := X.χ_fin la
      exact ⟨n, hn, fun γ hγ => h γ (hle hγ)⟩
    m := X.m * (Δ.relIndex X.Γ).factorial
    m_pos := Nat.mul_pos X.m_pos (Nat.factorial_pos _)
    transv := by
      intro ξ hξ hiso s hs hint
      obtain ⟨γ, hγ, hmat⟩ := X.transv ξ hξ hiso s hs hint
      refine ⟨γ ^ (Δ.relIndex X.Γ).factorial,
        (Subgroup.mem_inf.mp (Subgroup.pow_mem_of_relIndex_ne_zero_of_dvd hidx hγ
          (fun k hk hk' => Nat.dvd_factorial hk hk'))).1, ?_⟩
      rw [Units.val_pow_eq_pow_val, hmat, TransvectionPeriodicity.transvMat_pow X.Gm hiso]
      congr 1
      push_cast
      ring }, rfl, rfl, rfl, rfl⟩

end GlobalTheory.EqCovol
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagDomainDataOfFiniteIndexSubgroupStatement
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_flagDomainData_of_finiteIndex_subgroup : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Δ : Subgroup (GL (Fin r) E)), Δ ≤ X.Γ → Δ.relIndex X.Γ ≠ 0 → ∃ P : Data E r, P.Ψ = X.Ψ ∧ P.Gm = X.Gm ∧ P.p0 = X.p0 ∧ P.Γ = Δ := by
  first | exact @GlobalTheory.EqCovol.exists_data_of_le_relIndex_ne_zero | exact GlobalTheory.EqCovol.exists_data_of_le_relIndex_ne_zero | (intros; apply GlobalTheory.EqCovol.exists_data_of_le_relIndex_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicIndefiniteSelfDualTraceForm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicIndefiniteSelfDualTraceForm
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped nonZeroDivisors Matrix

noncomputable section

namespace GlobalTheory.EqCovol.IsoPlane

open GlobalTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem selfD_of_isSelfDualTr {r : ℕ} (Y : Data E r) (h : IsSelfDualTr Y) : GlobalTheory.SW.SelfD Y Y.Λ := by
  refine ⟨Y.Λ_fg, fun x => (h x).trans (forall₂_congr fun y _ => ?_)⟩
  rw [GlobalTheory.ThFr.EF_def]
  rcases Y.κ0_xi with hk | hk
  · rw [hk, show (2 * Y.ξ0) / 2 = Y.ξ0 by ring]
  · have e : -(-(2 * Y.ξ0) / 2) * herm Y.Gm x y = -(-Y.ξ0 * herm Y.Gm x y) := by ring
    rw [hk, e, map_neg]
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨-n, by rw [hn, Int.cast_neg]⟩
    · rintro ⟨n, hn⟩
      exact ⟨-n, by rw [Int.cast_neg, ← hn, neg_neg]⟩

def hypG : Matrix (Fin 2) (Fin 2) E := !![0, 1; 1, 0]

theorem hypG_herm (a b : Fin 2) : cc (hypG (E := E) a b) = hypG b a := by
  fin_cases a <;> fin_cases b <;> simp [hypG, cc]

theorem hypG_det : (hypG (E := E)).det ≠ 0 := by
  simp [hypG, Matrix.det_fin_two_of]

theorem herm_hypG (x y : Fin 2 → E) : herm hypG x y = x 0 * cc (y 1) + x 1 * cc (y 0) := by
  simp [herm, hypG, Fin.sum_univ_two]

def hypLat (J : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) (Fin 2 → E) :=
  ((1 : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E).comap (LinearMap.proj 0) ⊓
    (J : Submodule (𝓞 E) E).comap (LinearMap.proj 1)

theorem mem_hypLat {J : FractionalIdeal (𝓞 E)⁰ E} {x : Fin 2 → E} :
    x ∈ hypLat J ↔ x 0 ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) ∧ x 1 ∈ J := Iff.rfl

theorem isLattice_hypLat {J : FractionalIdeal (𝓞 E)⁰ E} (hJ0 : J ≠ 0) :
    ReciprocityTheory.MultiplicativeHeights.IsLattice (hypLat J) := by
  classical
  constructor
  · refine Submodule.FG.of_le ((Submodule.fg_span_singleton (Pi.single 0 1 : Fin 2 → E)).sup
      ((FractionalIdeal.fg_of_isNoetherianRing le_rfl J).map
        (LinearMap.single (𝓞 E) (fun _ : Fin 2 => E) 1))) fun x hx => ?_
    obtain ⟨h0, h1⟩ := mem_hypLat.1 hx
    let z : 𝓞 E := ⟨x 0, mem_one_fractionalIdeal_iff.1 h0⟩
    refine Submodule.mem_sup.2 ⟨z • Pi.single 0 1, Submodule.smul_mem _ z (Submodule.mem_span_singleton_self _),
      Pi.single 1 (x 1), ⟨x 1, h1, rfl⟩, ?_⟩
    funext i
    fin_cases i
    · simp [Algebra.smul_def]; rfl
    · simp
  · obtain ⟨j, hj, hj0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (mt FractionalIdeal.coeToSubmodule_eq_bot.1 hJ0)
    have e0 : (Pi.single 0 1 : Fin 2 → E) ∈ Submodule.span E (hypLat J : Set (Fin 2 → E)) :=
      Submodule.subset_span (mem_hypLat.2 ⟨by simp, by rw [Pi.single_eq_of_ne (by decide)]; exact (J : Submodule (𝓞 E) E).zero_mem⟩)
    have e1' : (Pi.single 1 j : Fin 2 → E) ∈ Submodule.span E (hypLat J : Set (Fin 2 → E)) :=
      Submodule.subset_span (mem_hypLat.2 ⟨by simp, by simpa using hj⟩)
    have e1 : (Pi.single 1 1 : Fin 2 → E) ∈ Submodule.span E (hypLat J : Set (Fin 2 → E)) := by
      have := Submodule.smul_mem _ j⁻¹ e1'
      rwa [← Pi.single_smul, smul_eq_mul, inv_mul_cancel₀ hj0] at this
    refine Submodule.eq_top_iff'.2 fun v => ?_
    have hv : v = v 0 • (Pi.single 0 1 : Fin 2 → E) + v 1 • Pi.single 1 1 := by
      funext i; fin_cases i <;> simp
    rw [hv]
    exact add_mem (Submodule.smul_mem _ _ e0) (Submodule.smul_mem _ _ e1)

theorem modular_hypLat {J : FractionalIdeal (𝓞 E)⁰ E} (hJ0 : J ≠ 0) (hJc : ∀ z ∈ J, cc z ∈ J)
    (x : Fin 2 → E) : x ∈ hypLat J ↔ ∀ y ∈ hypLat J, herm hypG x y ∈ J := by
  constructor
  · intro hx y hy
    obtain ⟨hx0, hx1⟩ := mem_hypLat.1 hx
    obtain ⟨hy0, hy1⟩ := mem_hypLat.1 hy
    rw [herm_hypG]
    refine (J : Submodule (𝓞 E) E).add_mem ?_ ?_
    · simpa using FractionalIdeal.mul_mem_mul hx0 (hJc _ hy1)
    · have : cc (y 0) ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) :=
        mem_one_fractionalIdeal_iff.2 (isIntegral_cc (mem_one_fractionalIdeal_iff.1 hy0))
      simpa using FractionalIdeal.mul_mem_mul hx1 this
  · intro h
    have h1 : x 1 ∈ J := by
      have := h (Pi.single 0 1) (mem_hypLat.2 ⟨by simp, by rw [Pi.single_eq_of_ne (by decide)]; exact (J : Submodule (𝓞 E) E).zero_mem⟩)
      simpa [herm_hypG, cc] using this
    have h0 : ∀ j ∈ J, x 0 * j ∈ J := fun j hj => by
      have := h (Pi.single 1 (cc j)) (mem_hypLat.2 ⟨by simp, by simpa using hJc j hj⟩)
      simpa [herm_hypG, cc] using this
    have hle : FractionalIdeal.spanSingleton (𝓞 E)⁰ (x 0) * J ≤ J := by
      refine FractionalIdeal.mul_le.2 fun i hi j hj => ?_
      obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hi
      rw [smul_mul_assoc]
      exact (J : Submodule (𝓞 E) E).smul_mem a (h0 j hj)
    have hle1 : FractionalIdeal.spanSingleton (𝓞 E)⁰ (x 0) ≤ 1 := by
      calc FractionalIdeal.spanSingleton (𝓞 E)⁰ (x 0)
          = J⁻¹ * (FractionalIdeal.spanSingleton (𝓞 E)⁰ (x 0) * J) := by
            rw [mul_left_comm, inv_mul_cancel₀ hJ0, mul_one]
        _ ≤ J⁻¹ * J := mul_le_mul_right hle _
        _ = 1 := inv_mul_cancel₀ hJ0
    exact ⟨hle1 (FractionalIdeal.mem_spanSingleton_self _ _), h1⟩

theorem hypG_signature (τ : E →+* ℂ) : ∃ Q : Matrix (Fin 2) (Fin 2) ℂ, Q.det ≠ 0 ∧
    gram τ hypG Q = Matrix.diagonal fun a : Fin 2 => ((sgn 1 (a : ℕ) : ℝ) : ℂ) := by
  refine ⟨!![1, 1; 1 / 2, -1 / 2], by simp [Matrix.det_fin_two_of]; norm_num, ?_⟩
  ext a b
  fin_cases a <;> fin_cases b <;> simp [gram, hermC, col, hypG, sgn, Fin.sum_univ_two, map_ofNat] <;> norm_num

theorem iso_rank_two (H : Host E) (Y : Data E 2) (hp : Y.p0 = 1) (hY : IsSelfDualTr Y) :
    ∃ z : Fin 2 → E, z ≠ 0 ∧ herm Y.Gm z z = 0 := by
  haveI := H.unram
  obtain ⟨J, hJ0, hJc, hJ⟩ := GlobalTheory.Ker.OntoLat.exists_valueIdeal Y
  have HN := GlobalTheory.QNorm.hasseNormSt
  have hΨ : ∀ τ : E →+* ℂ, τ ∈ (Y.Ψ : Set (E →+* ℂ)) ∨ ComplexEmbedding.conjugate τ ∈ (Y.Ψ : Set (E →+* ℂ)) := by
    intro τ
    by_cases h : ComplexEmbedding.conjugate τ ∈ Y.Ψ
    · exact Or.inr h
    · exact Or.inl ((Y.cmType τ).mpr h)
  have hs : ∀ τ ∈ (Y.Ψ : Set (E →+* ℂ)), ∃ p : ℕ,
      (∃ Q : Matrix (Fin 2) (Fin 2) ℂ, Q.det ≠ 0 ∧
        gram τ Y.Gm Q = Matrix.diagonal fun a : Fin 2 => ((sgn p (a : ℕ) : ℝ) : ℂ)) ∧
      ∃ Q : Matrix (Fin 2) (Fin 2) ℂ, Q.det ≠ 0 ∧
        gram τ hypG Q = Matrix.diagonal fun a : Fin 2 => ((sgn p (a : ℕ) : ℝ) : ℂ) := by
    intro τ hτ
    obtain ⟨Q, hQ, hg⟩ := Y.signature ⟨τ, hτ⟩
    rw [hp] at hg
    exact ⟨1, ⟨Q, hQ, hg⟩, hypG_signature τ⟩
  obtain ⟨P, hP, hPG⟩ := GlobalTheory.SelfDualGenus.congr_of_modular (G := Y.Gm) (G' := hypG) (L := Y.Λ)
    (L' := hypLat J) (GlobalTheory.LocalQuad.landherr_of_hasseNormSt HN) HN hJ0 hJc Y.Gm_herm hypG_herm Y.Gm_det
    hypG_det ⟨Y.Λ_fg, Y.Λ_span⟩ (isLattice_hypLat hJ0) (hJ Y.Λ (selfD_of_isSelfDualTr Y hY))
    (modular_hypLat hJ0 hJc) (GlobalTheory.Published.Landherr.congr_of_signature _ hΨ hs)
  refine ⟨P *ᵥ Pi.single 0 1, fun h => ?_, ?_⟩
  · have := congrFun (Matrix.eq_zero_of_mulVec_eq_zero hP h) 0
    simp at this
  · rw [GlobalTheory.SelfDualGenus.herm_mulVec, ← hPG, herm_hypG]
    simp

end GlobalTheory.EqCovol.IsoPlane

namespace GlobalTheory.EqCovol

theorem exists_isotropic_of_isSelfDualTr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (r : ℕ)
    (Y : Data E r), 1 ≤ Y.p0 → Y.p0 < r → GlobalTheory.EqCovol.IsSelfDualTr Y →
    ∃ z : Fin r → E, z ≠ 0 ∧ herm Y.Gm z z = 0 := by
  intro E _ _ _ H r Y h1 h2 hY
  by_cases hr : 3 ≤ r
  · obtain ⟨cu⟩ := GlobalTheory.CuspExist.nonempty_cuspFD GlobalTheory.QNorm.hasseNormSt E r 1 Y h1 (by omega) (by omega)
    exact ⟨cu.e 0, cu.ind.ne_zero 0, cu.iso 0 0⟩
  · obtain rfl : r = 2 := by omega
    exact IsoPlane.iso_rank_two H Y (by omega) hY

end GlobalTheory.EqCovol
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicIndefiniteSelfDualTraceFormStatement
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isotropic_indefinite_selfDualTraceForm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (r : ℕ) (Y : Data E r), 1 ≤ Y.p0 → Y.p0 < r → GlobalTheory.EqCovol.IsSelfDualTr Y → ∃ z : Fin r → E, z ≠ 0 ∧ herm Y.Gm z z = 0 := by
  first | exact @GlobalTheory.EqCovol.exists_isotropic_of_isSelfDualTr | exact GlobalTheory.EqCovol.exists_isotropic_of_isSelfDualTr | (intros; apply GlobalTheory.EqCovol.exists_isotropic_of_isSelfDualTr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexConjEqOfPowEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexConjEqOfPowEq
namespace GlobalTheory

open Subgroup

theorem relIndex_cocycle_of_ne_zero {A : Type} [Group A] (X Y Z : Subgroup A)
    (hXY : X.relIndex Y ≠ 0) (hYX : Y.relIndex X ≠ 0) (hYZ : Y.relIndex Z ≠ 0)
    (hZY : Z.relIndex Y ≠ 0) (hXZ : X.relIndex Z ≠ 0) (hZX : Z.relIndex X ≠ 0) :
    Y.relIndex X * Z.relIndex Y * X.relIndex Z = X.relIndex Y * Y.relIndex Z * Z.relIndex X := by
  have a1 := relIndex_inf_mul_relIndex Y Z X
  have a2 := relIndex_inf_mul_relIndex Z Y X
  have b1 := relIndex_inf_mul_relIndex Z X Y
  have b2 := relIndex_inf_mul_relIndex X Z Y
  have c1 := relIndex_inf_mul_relIndex X Y Z
  have c2 := relIndex_inf_mul_relIndex Y X Z
  rw [inf_comm Z Y] at a2
  rw [inf_comm Y X] at c2
  rw [inf_comm X Z] at b2
  rw [inf_comm Z Y] at b2
  rw [inf_comm Y X] at a2
  rw [inf_comm X Z] at c2
  have ha : (Y ⊓ Z).relIndex X ≠ 0 := relIndex_inf_ne_zero hYX hZX
  have hb : (Z ⊓ X).relIndex Y ≠ 0 := relIndex_inf_ne_zero hZY hXY
  have hc : (X ⊓ Y).relIndex Z ≠ 0 := relIndex_inf_ne_zero hXZ hYZ
  have hpY : Y.relIndex (Z ⊓ X) ≠ 0 := by
    intro h; apply ha; rw [← a1, h, zero_mul]
  have hpZ : Z.relIndex (X ⊓ Y) ≠ 0 := by
    intro h; apply hb; rw [← b1, h, zero_mul]
  have hpX : X.relIndex (Y ⊓ Z) ≠ 0 := by
    intro h; apply hc; rw [← c1, h, zero_mul]
  have hP : 0 < Z.relIndex (X ⊓ Y) * X.relIndex (Y ⊓ Z) * Y.relIndex (Z ⊓ X) := by
    positivity
  apply Nat.eq_of_mul_eq_mul_left hP
  calc Z.relIndex (X ⊓ Y) * X.relIndex (Y ⊓ Z) * Y.relIndex (Z ⊓ X) *
        (Y.relIndex X * Z.relIndex Y * X.relIndex Z)
      = (Z.relIndex (X ⊓ Y) * Y.relIndex X) * (X.relIndex (Y ⊓ Z) * Z.relIndex Y) *
        (Y.relIndex (Z ⊓ X) * X.relIndex Z) := by ring
    _ = (Y.relIndex (Z ⊓ X) * Z.relIndex X) * (Z.relIndex (X ⊓ Y) * X.relIndex Y) *
        (X.relIndex (Y ⊓ Z) * Y.relIndex Z) := by rw [a2, b2, c2, a1, b1, c1]
    _ = _ := by ring

theorem map_conj_mul {A : Type} [Group A] (K : Subgroup A) (x y : A) :
    K.map (MulAut.conj (x * y)).toMonoidHom =
      (K.map (MulAut.conj y).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext z
  simp [mul_assoc]

theorem relIndex_map_conj {A : Type} [Group A] (H L : Subgroup A) (g : A) :
    (H.map (MulAut.conj g).toMonoidHom).relIndex (L.map (MulAut.conj g).toMonoidHom) =
      H.relIndex L :=
  Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective

theorem map_conj_one {A : Type} [Group A] (K : Subgroup A) :
    K.map (MulAut.conj (1 : A)).toMonoidHom = K := by
  ext x; simp

theorem relIndex_conj_pow_succ {A : Type} [Group A] (K : Subgroup A) (g : A) (i : ℕ) :
    (K.map (MulAut.conj (g ^ (i + 1))).toMonoidHom).relIndex
        (K.map (MulAut.conj (g ^ i)).toMonoidHom) =
      (K.map (MulAut.conj g).toMonoidHom).relIndex K ∧
    (K.map (MulAut.conj (g ^ i)).toMonoidHom).relIndex
        (K.map (MulAut.conj (g ^ (i + 1))).toMonoidHom) =
      K.relIndex (K.map (MulAut.conj g).toMonoidHom) := by
  rw [pow_succ, map_conj_mul, relIndex_map_conj, relIndex_map_conj]
  exact ⟨rfl, rfl⟩

theorem relIndex_conj_pow_induction {A : Type} [Group A] (K : Subgroup A) (g : A)
    (ha : (K.map (MulAut.conj g).toMonoidHom).relIndex K ≠ 0)
    (hb : K.relIndex (K.map (MulAut.conj g).toMonoidHom) ≠ 0) (i : ℕ) :
    (K.map (MulAut.conj (g ^ i)).toMonoidHom).relIndex K ≠ 0 ∧
    K.relIndex (K.map (MulAut.conj (g ^ i)).toMonoidHom) ≠ 0 ∧
    (K.map (MulAut.conj (g ^ i)).toMonoidHom).relIndex K *
        (K.relIndex (K.map (MulAut.conj g).toMonoidHom)) ^ i =
      K.relIndex (K.map (MulAut.conj (g ^ i)).toMonoidHom) *
        ((K.map (MulAut.conj g).toMonoidHom).relIndex K) ^ i := by
  induction i with
  | zero =>
    rw [pow_zero, map_conj_one]
    simp
  | succ i ih =>
    obtain ⟨hu, hv, hi⟩ := ih
    obtain ⟨sa, sb⟩ := relIndex_conj_pow_succ K g i
    set B := K.map (MulAut.conj (g ^ i)).toMonoidHom
    set C := K.map (MulAut.conj (g ^ (i + 1))).toMonoidHom
    set a := (K.map (MulAut.conj g).toMonoidHom).relIndex K
    set b := K.relIndex (K.map (MulAut.conj g).toMonoidHom)
    have hCB : C.relIndex B ≠ 0 := by rw [sa]; exact ha
    have hBC : B.relIndex C ≠ 0 := by rw [sb]; exact hb
    have hCK : C.relIndex K ≠ 0 := relIndex_ne_zero_trans hCB hu
    have hKC : K.relIndex C ≠ 0 := relIndex_ne_zero_trans hv hBC
    have coc := relIndex_cocycle_of_ne_zero K B C hv hu hBC hCB hKC hCK
    rw [sa, sb] at coc
    refine ⟨hCK, hKC, ?_⟩
    apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hv)
    calc C.relIndex K * b ^ (i + 1) * K.relIndex B
        = b * K.relIndex B * C.relIndex K * b ^ i := by ring
      _ = B.relIndex K * a * K.relIndex C * b ^ i := by rw [coc]; ring
      _ = a * K.relIndex C * (B.relIndex K * b ^ i) := by ring
      _ = K.relIndex C * a ^ (i + 1) * K.relIndex B := by rw [hi]; ring

theorem relIndex_conj_eq_of_pow_eq : ∀ (A : Type) [Group A] (K : Subgroup A) (g : A) (n : ℕ), 0 < n →
    (K.map (MulAut.conj g).toMonoidHom).relIndex K ≠ 0 →
    K.relIndex (K.map (MulAut.conj g).toMonoidHom) ≠ 0 →
    (K.map (MulAut.conj (g ^ n)).toMonoidHom).relIndex K =
      K.relIndex (K.map (MulAut.conj (g ^ n)).toMonoidHom) →
    (K.map (MulAut.conj g).toMonoidHom).relIndex K =
      K.relIndex (K.map (MulAut.conj g).toMonoidHom) := by
  intro A _ K g n hn ha hb heq
  obtain ⟨hu, _, hi⟩ := relIndex_conj_pow_induction K g ha hb n
  rw [heq] at hi hu
  have hpow := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hu) hi
  exact (Nat.pow_left_injective (Nat.pos_iff_ne_zero.mp hn) hpow).symm

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexConjEqOfPowEqStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_map_conj_symm_of_relIndex_map_conj_pow_symm : ∀ (A : Type) [Group A] (K : Subgroup A) (g : A) (n : ℕ), 0 < n → (K.map (MulAut.conj g).toMonoidHom).relIndex K ≠ 0 → K.relIndex (K.map (MulAut.conj g).toMonoidHom) ≠ 0 → (K.map (MulAut.conj (g ^ n)).toMonoidHom).relIndex K = K.relIndex (K.map (MulAut.conj (g ^ n)).toMonoidHom) → (K.map (MulAut.conj g).toMonoidHom).relIndex K = K.relIndex (K.map (MulAut.conj g).toMonoidHom) := by
  first | exact @GlobalTheory.relIndex_conj_eq_of_pow_eq | exact GlobalTheory.relIndex_conj_eq_of_pow_eq | (intros; apply GlobalTheory.relIndex_conj_eq_of_pow_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeEqSelfDualLatticesSameHermitianSpace
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UTrans GlobalTheory.UTrans.StrongApprox GlobalTheory.AdLat
open scoped TensorProduct ENNReal

namespace GlobalTheory.EqCovol.SameSpace

theorem mem_map_conj {A : Type} [Group A] (K : Subgroup A) (h k : A) :
    k ∈ K.map (MulAut.conj h).toMonoidHom ↔ h⁻¹ * k * h ∈ K := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [mul_assoc] using hx
  · intro hk
    exact ⟨_, hk, by simp [mul_assoc]⟩

section Abstract

variable {R : Type} [CommRing R] {n : ℕ} {σ : R →+* R} {G : Matrix (Fin n) (Fin n) R}

theorem hf_eq (x y : Fin n → R) : hf σ G x y = x ⬝ᵥ (G *ᵥ fun i => σ (y i)) := by
  simp only [hf, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem isU_iff {γ : Matrix (Fin n) (Fin n) R} : IsU σ G γ ↔ γᵀ * G * γ.map σ = G := by
  have key : ∀ x y, hf σ G (γ *ᵥ x) (γ *ᵥ y) = hf σ (γᵀ * G * γ.map σ) x y := fun x y => by
    have : (fun i => σ ((γ *ᵥ y) i)) = γ.map σ *ᵥ fun i => σ (y i) :=
      funext fun i => RingHom.map_mulVec σ γ y i
    rw [hf_eq, hf_eq, this, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec x, vecMul_transpose]
  refine ⟨fun h => ?_, fun h x y => by rw [key, h]⟩
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  rw [key] at this
  simpa [hf, Pi.single_apply, apply_ite σ] using this

theorem isU_mul {a b : Matrix (Fin n) (Fin n) R} (ha : IsU σ G a) (hb : IsU σ G b) : IsU σ G (a * b) :=
  fun x y => by rw [← mulVec_mulVec, ← mulVec_mulVec, ha, hb]

theorem isU_inv {a : GL (Fin n) R} (ha : IsU σ G a.1) : IsU σ G (a⁻¹).1 := fun x y => by
  rw [← ha, mulVec_mulVec, mulVec_mulVec, Units.mul_inv, one_mulVec, one_mulVec]

theorem isU_pow {a : GL (Fin n) R} (ha : IsU σ G a.1) (k : ℕ) : IsU σ G (a ^ k).1 := by
  induction k with
  | zero => intro x y; simp
  | succ k ih => rw [pow_succ, Units.val_mul]; exact isU_mul ih ha

theorem det_mul_det (hG : IsUnit G.det) {a : Matrix (Fin n) (Fin n) R} (ha : IsU σ G a) :
    a.det * σ a.det = 1 := by
  have e := congrArg det (isU_iff.1 ha)
  rw [det_mul, det_mul, det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at e
  refine hG.mul_right_cancel ?_
  linear_combination e

theorem det_conj (h k : GL (Fin n) R) : (h⁻¹ * k * h).1.det = k.1.det := by
  rw [Units.val_mul, Units.val_mul, det_mul, det_mul, mul_right_comm, ← det_mul, Units.inv_mul, det_one, one_mul]


variable (σ G) in
def cong (H : AddSubgroup (Fin n → R)) (M : ℕ) : Subgroup (GL (Fin n) R) where
  carrier := {k | IsU σ G k.1 ∧ k.1.det = 1 ∧ (k⁻¹).1 ∈ stab H ∧ ∃ B ∈ stab H, k.1 = 1 + (M : R) • B}
  one_mem' := ⟨fun x y => by simp, by simp, by simpa using one_mem _, 0, zero_mem _, by simp⟩
  mul_mem' := by
    rintro a b ⟨ha1, ha2, ha3, B, hB, e⟩ ⟨hb1, hb2, hb3, C, hC, e'⟩
    refine ⟨isU_mul ha1 hb1, by rw [Units.val_mul, det_mul, ha2, hb2, mul_one], ?_,
      B + C + (M : R) • (B * C), add_mem (add_mem hB hC) (natCast_smul_mem _ (mul_mem hB hC)), ?_⟩
    · rw [_root_.mul_inv_rev, Units.val_mul]; exact mul_mem hb3 ha3
    · rw [Units.val_mul, e, e']
      simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one, smul_add]
      abel
  inv_mem' := by
    rintro a ⟨ha1, ha2, ha3, B, hB, e⟩
    refine ⟨isU_inv ha1, ?_, ?_, -((a⁻¹).1 * B), neg_mem (mul_mem ha3 hB), ?_⟩
    · have := congrArg det a.inv_mul
      rwa [det_mul, ha2, mul_one, det_one] at this
    · rw [inv_inv, e]; exact add_mem (one_mem _) (natCast_smul_mem _ hB)
    · rw [← a.inv_mul, e, mul_add, mul_one, Matrix.mul_smul, smul_neg, add_neg_cancel_right]

theorem mem_cong {H : AddSubgroup (Fin n → R)} {M : ℕ} {k : GL (Fin n) R} : k ∈ cong σ G H M ↔
    IsU σ G k.1 ∧ k.1.det = 1 ∧ (k⁻¹).1 ∈ stab H ∧ ∃ B ∈ stab H, k.1 = 1 + (M : R) • B := Iff.rfl

theorem conj_mem_cong {H H' : AddSubgroup (Fin n → R)} {M : ℕ} {h : GL (Fin n) R} (hh : IsU σ G h.1)
    (hH : ∀ A ∈ stab H', (h⁻¹).1 * A * h.1 ∈ stab H) {k : GL (Fin n) R} (hk : k ∈ cong σ G H' M) :
    h⁻¹ * k * h ∈ cong σ G H M := by
  obtain ⟨h1, h2, h3, B, hB, e⟩ := hk
  refine ⟨isU_mul (isU_mul (isU_inv hh) h1) hh, by rw [det_conj, h2], ?_, _, hH B hB, ?_⟩
  · have : (h⁻¹ * k * h)⁻¹ = h⁻¹ * k⁻¹ * h := by group
    rw [this]; exact hH _ h3
  · rw [Units.val_mul, Units.val_mul, e, mul_add, add_mul, mul_one, Units.inv_mul, Matrix.mul_smul,
      Matrix.smul_mul]

theorem conj_mem_stab {H H' : AddSubgroup (Fin n → R)} {h : GL (Fin n) R}
    (h1 : ∀ z ∈ H, h.1 *ᵥ z ∈ H') (h2 : ∀ z ∈ H', (h⁻¹).1 *ᵥ z ∈ H) :
    ∀ A ∈ stab H', (h⁻¹).1 * A * h.1 ∈ stab H := fun A hA z hz => by
  rw [← mulVec_mulVec, ← mulVec_mulVec]
  exact h2 _ (hA _ (h1 z hz))

theorem map_conj_cong {H H' : AddSubgroup (Fin n → R)} {M : ℕ} {h : GL (Fin n) R} (hh : IsU σ G h.1)
    (hH : h.1.mulVec '' H = H') : (cong σ G H M).map (MulAut.conj h).toMonoidHom = cong σ G H' M := by
  have h1 : ∀ z ∈ H, h.1 *ᵥ z ∈ H' := fun z hz => by
    rw [← SetLike.mem_coe, ← hH]; exact ⟨z, hz, rfl⟩
  have h2 : ∀ z ∈ H', (h⁻¹).1 *ᵥ z ∈ H := fun z hz => by
    rw [← SetLike.mem_coe, ← hH] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    rwa [mulVec_mulVec, Units.inv_mul, one_mulVec]
  ext k
  rw [mem_map_conj]
  refine ⟨fun hk => ?_, conj_mem_cong hh (conj_mem_stab h1 h2)⟩
  have := conj_mem_cong (isU_inv hh) (conj_mem_stab (h := h⁻¹) h2 (by simpa using h1)) hk
  simpa [mul_assoc] using this

theorem cong_le_map_conj {H : AddSubgroup (Fin n → R)} {M a b : ℕ} {h : GL (Fin n) R} (hh : IsU σ G h.1)
    (ha : (a : R) • (h⁻¹).1 ∈ stab H) (hb : (b : R) • h.1 ∈ stab H) :
    cong σ G H (M * a * b) ≤ (cong σ G H M).map (MulAut.conj h).toMonoidHom := by
  have key : ∀ k ∈ cong σ G H (M * a * b), ∃ C ∈ stab H, (h⁻¹ * k * h).1 = 1 + (M : R) • C := by
    rintro k ⟨-, -, -, B, hB, e⟩
    refine ⟨_, mul_mem (mul_mem ha hB) hb, ?_⟩
    rw [Units.val_mul, Units.val_mul, e, mul_add, add_mul, mul_one, Units.inv_mul]
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Nat.cast_mul]
    congr 2
    ring
  intro k hk
  rw [mem_map_conj]
  refine ⟨isU_mul (isU_mul (isU_inv hh) hk.1) hh, by rw [det_conj, hk.2.1], ?_, key k hk⟩
  obtain ⟨C, hC, e⟩ := key _ (inv_mem hk)
  have : (h⁻¹ * k * h)⁻¹ = h⁻¹ * k⁻¹ * h := by group
  rw [this, e]
  exact add_mem (one_mem _) (natCast_smul_mem _ hC)

theorem cong_mul_le {H : AddSubgroup (Fin n → R)} {M a : ℕ} : cong σ G H (M * a) ≤ cong σ G H M := by
  rintro k ⟨h1, h2, h3, B, hB, e⟩
  exact ⟨h1, h2, h3, _, natCast_smul_mem a hB, by rw [e, smul_smul, Nat.cast_mul]⟩

theorem exists_det_one_conj_eq (hG : IsUnit G.det) {g : GL (Fin n) R} (hg : IsU σ G g.1) :
    ∃ s : GL (Fin n) R, IsU σ G s.1 ∧ s.1.det = 1 ∧ ∀ k, (g ^ n)⁻¹ * k * g ^ n = s⁻¹ * k * s := by
  have hd := det_mul_det hG hg
  let z : GL (Fin n) R := ⟨σ g.1.det • 1, g.1.det • 1, by simp [smul_smul, mul_comm, hd],
    by simp [smul_smul, mul_comm, hd]⟩
  have hz : ∀ k, z * k = k * z := fun k => Units.ext (by simp [z])
  have hd' : σ g.1.det * σ (σ g.1.det) = 1 := by rw [← map_mul, hd, map_one]
  refine ⟨z * g ^ n, isU_mul (isU_iff.2 ?_) (isU_pow hg n), ?_, fun k => ?_⟩
  · have : (σ g.1.det • (1 : Matrix (Fin n) (Fin n) R)).map σ = σ (σ g.1.det) • 1 := by
      ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h]
    simp [z, this, smul_smul, mul_comm, hd']
  · rw [Units.val_mul, det_mul, Units.val_pow_eq_pow_val, det_pow]
    simp [z, ← mul_pow, mul_comm, hd]
  · rw [_root_.mul_inv_rev, mul_assoc, mul_assoc, mul_assoc, ← mul_assoc k, ← hz k, mul_assoc z,
      inv_mul_cancel_left]

end Abstract

section Adelic

variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

def embGL : GL (Fin n) E →* GL (Fin n) (RA F E) := GeneralLinearGroup.map (emb F)

theorem embGL_val (γ : GL (Fin n) E) : (embGL F γ).1 = (emb F).mapMatrix γ.1 := rfl

theorem emb_injective : Function.Injective (emb F : E →+* RA F E) := by
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 F)
  let v : HeightOneSpectrum (𝓞 F) :=
    ⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField F)⟩
  haveI : Nontrivial (FiniteAdeleRing (𝓞 F) F) := ⟨⟨0, 1, fun h => by
    have : (0 : v.adicCompletion F) = 1 := congrArg (fun a : FiniteAdeleRing (𝓞 F) F => a v) h
    exact zero_ne_one this⟩⟩
  exact Algebra.TensorProduct.includeRight_injective (algebraMap F (FiniteAdeleRing (𝓞 F) F)).injective

variable {F} (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E)

def sgA : RA F E →+* RA F E := (sg (FiniteAdeleRing (𝓞 F) F) c).toRingHom

theorem isU_emb {γ : Matrix (Fin n) (Fin n) E} :
    IsU (sgA c) ((emb F).mapMatrix G) ((emb F).mapMatrix γ) ↔ IsU (c : E →+* E) G γ := by
  have e : ((emb F).mapMatrix γ)ᵀ * (emb F).mapMatrix G * ((emb F).mapMatrix γ).map (sgA c) =
      (emb F).mapMatrix (γᵀ * G * γ.map (c : E →+* E)) := by
    rw [map_mul, map_mul]; rfl
  rw [isU_iff, isU_iff, e]
  exact (Matrix.map_injective (emb_injective F)).eq_iff

variable [NumberField E] {L : Submodule (𝓞 E) (Fin n → E)} (hL : L.FG)
  (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤)


include hL hsp in
theorem embGL_mem_cong {M : ℕ} (hM : 0 < M) (γ : GL (Fin n) E) :
    embGL F γ ∈ cong (sgA c) ((emb F).mapMatrix G) (hat F (L : Set (Fin n → E))) M ↔
      IsU (c : E →+* E) G γ.1 ∧ γ.1.det = 1 ∧ (∀ x, x ∈ L ↔ γ.1 *ᵥ x ∈ L) ∧
        ∀ x ∈ L, ∃ y ∈ L, γ.1 *ᵥ x - x = M • y := by
  have h1 := (hat_rational_points_and_approx F E n L hL hsp).1
  have hME : (M : E) ≠ 0 := by exact_mod_cast hM.ne'
  have hd : ((emb F).mapMatrix γ.1).det = 1 ↔ γ.1.det = 1 := by
    rw [← RingHom.map_det, ← map_one (emb F), (emb_injective F).eq_iff]
  have hst : ∀ A : Matrix (Fin n) (Fin n) E, (emb F).mapMatrix A ∈ stab (hat F (L : Set (Fin n → E))) ↔
      ∀ x ∈ L, A *ᵥ x ∈ L := fun A => ⟨fun h x hx => by
        rw [← h1, ← emb_mulVec]; exact h _ (Translate.fv_mem_hat hx), emb_mem_stab F⟩
  set A : Matrix (Fin n) (Fin n) E := (M : E)⁻¹ • (γ.1 - 1) with hA
  have eA : γ.1 = 1 + (M : E) • A := by rw [hA, smul_inv_smul₀ hME, add_sub_cancel]
  have eA' : (emb F).mapMatrix γ.1 = 1 + (M : RA F E) • (emb F).mapMatrix A := by
    rw [eA, map_add (f := _), map_one, emb_smul, map_natCast]
  have eAx : ∀ x, γ.1 *ᵥ x - x = M • (A *ᵥ x) := fun x => by
    rw [eA, add_mulVec, one_mulVec, add_sub_cancel_left, smul_mulVec, Nat.cast_smul_eq_nsmul]
  have h3 : (∃ B ∈ stab (hat F (L : Set (Fin n → E))), (emb F).mapMatrix γ.1 = 1 + (M : RA F E) • B) ↔
      ∀ x ∈ L, A *ᵥ x ∈ L := by
    rw [← hst]
    refine ⟨?_, fun h => ⟨_, h, eA'⟩⟩
    rintro ⟨B, hB, e⟩
    rw [eA', add_right_inj] at e
    rwa [(isUnit_nat F hM).smul_left_cancel.1 e]
  have h4 : (∀ x ∈ L, ∃ y ∈ L, γ.1 *ᵥ x - x = M • y) ↔ ∀ x ∈ L, A *ᵥ x ∈ L := by
    refine forall₂_congr fun x _ => ⟨?_, fun h => ⟨_, h, eAx x⟩⟩
    rintro ⟨y, hy, e⟩
    rw [eAx, ← Nat.cast_smul_eq_nsmul E, ← Nat.cast_smul_eq_nsmul E] at e
    rwa [smul_right_injective _ hME e]
  rw [mem_cong, ← map_inv, embGL_val, embGL_val, isU_emb, hd, hst, h3, h4]
  refine and_congr_right fun _ => and_congr_right fun _ => and_congr_left fun h => ⟨fun h' x => ⟨fun hx => ?_,
    fun hx => ?_⟩, fun h' x hx => ?_⟩
  · rw [← sub_add_cancel (γ.1 *ᵥ x) x, eAx]
    exact add_mem (nsmul_mem (h x hx) M) hx
  · have := h' _ hx
    rwa [mulVec_mulVec, Units.inv_mul, one_mulVec] at this
  · rw [h', mulVec_mulVec, Units.mul_inv, one_mulVec]
    exact hx

variable (hrk : Module.finrank F E = 2) (hG : IsHerm (c : E →+* E) G)
  (hiso : ∃ z : Fin n → E, z ≠ 0 ∧ hf (c : E →+* E) G z z = 0)


include hL hsp hrk hG hiso in
theorem exists_inv_mul_mem_cong {M : ℕ} (hM : 0 < M) {s : GL (Fin n) (RA F E)}
    (hs : IsU (sgA c) ((emb F).mapMatrix G) s.1) (hd : s.1.det = 1) :
    ∃ γ : GL (Fin n) E, IsU (c : E →+* E) G γ.1 ∧ (embGL F γ)⁻¹ * s ∈
      cong (sgA c) ((emb F).mapMatrix G) (hat F (L : Set (Fin n → E))) M := by
  obtain ⟨γ, h1, h2, h3⟩ := strong_approximation F E c n G hrk hG hiso L hL hsp s hs hd M hM
  let δ : GL (Fin n) E := GeneralLinearGroup.mkOfDetNeZero γ (by rw [h2]; exact one_ne_zero)
  have e : ((embGL F δ⁻¹)⁻¹ * s).1 = (emb F).mapMatrix γ * s.1 := by rw [map_inv, inv_inv]; rfl
  have hdet : ((embGL F δ⁻¹)⁻¹ * s).1.det = 1 := by
    rw [e, det_mul, hd, ← RingHom.map_det, h2, map_one, mul_one]
  obtain ⟨B, hB, eB⟩ := exists_of_cong (H := hat F (L : Set (Fin n → E))) (isUnit_nat F hM)
    (A := (emb F).mapMatrix γ * s.1 - 1) fun z hz => by
      obtain ⟨w, hw, e⟩ := h3 z hz
      exact ⟨w, hw, by rw [sub_mulVec, one_mulVec]; exact sub_eq_of_eq_add' e⟩
  have eB' : ((embGL F δ⁻¹)⁻¹ * s).1 = 1 + (M : RA F E) • B := by rw [e, ← eB, add_sub_cancel]
  refine ⟨δ⁻¹, isU_inv (a := δ) h1, by rw [e]; exact isU_mul ((isU_emb c G).2 h1) hs, hdet, ?_, B, hB, eB'⟩
  refine inv_mulVec_mem_hat F E n L _ c hL hsp ?_ (by rw [hdet, map_one, mul_one])
  rw [eB']
  exact add_mem (one_mem (stab _)) (natCast_smul_mem _ hB)


include hL hsp hrk hG hiso in
theorem relIndex_comap {M : ℕ} (hM : 0 < M) {h : GL (Fin n) (RA F E)}
    (hh : IsU (sgA c) ((emb F).mapMatrix G) h.1) (K : Subgroup (GL (Fin n) (RA F E)))
    (hK : K = cong (sgA c) ((emb F).mapMatrix G) (hat F (L : Set (Fin n → E))) M) :
    ((K.map (MulAut.conj h).toMonoidHom).comap (embGL F)).relIndex (K.comap (embGL F)) =
      (K.map (MulAut.conj h).toMonoidHom).relIndex K ∧
    (K.comap (embGL F)).relIndex ((K.map (MulAut.conj h).toMonoidHom).comap (embGL F)) =
      K.relIndex (K.map (MulAut.conj h).toMonoidHom) := by
  subst hK
  obtain ⟨a, ha0, ha⟩ := exists_bound_stab F hL hsp (h⁻¹).1
  obtain ⟨b, hb0, hb⟩ := exists_bound_stab F hL hsp h.1
  refine GlobalTheory.HL.relIndex_pair_comap_of_dense_image _ _ _ fun s hs => ?_
  have hs' : IsU (sgA c) ((emb F).mapMatrix G) s.1 ∧ s.1.det = 1 := by
    rcases hs with hs | hs
    · rw [mem_map_conj] at hs
      refine ⟨?_, (det_conj h s).symm.trans hs.2.1⟩
      have e : s = h * (h⁻¹ * s * h) * h⁻¹ := by group
      rw [e]
      exact isU_mul (isU_mul hh hs.1) (isU_inv hh)
    · exact ⟨hs.1, hs.2.1⟩
  obtain ⟨γ, -, hγ⟩ := exists_inv_mul_mem_cong c G hL hsp hrk hG hiso
    (Nat.mul_pos (Nat.mul_pos hM ha0) hb0) hs'.1 hs'.2
  exact ⟨γ, cong_le_map_conj hh ha hb hγ, cong_mul_le (cong_mul_le hγ)⟩

end Adelic

section Covolume

open ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.TrueCx

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem covol_of_le (X P : Data E r) (δ : GL (Fin r) E) (hΨ : P.Ψ = X.Ψ) (hG : P.Gm = X.Gm) (hp : P.p0 = X.p0)
    (hδ : ∀ v w, herm X.Gm (δ.1 *ᵥ v) (δ.1 *ᵥ w) = herm X.Gm v w)
    (hle : P.Γ.map (MulAut.conj δ).toMonoidHom ≤ X.Γ)
    (hi : (P.Γ.map (MulAut.conj δ).toMonoidHom).relIndex X.Γ ≠ 0) :
    covol P = covol X * ((P.Γ.map (MulAut.conj δ).toMonoidHom).relIndex X.Γ : ℝ) := by
  have h := GlobalTheory.SubgroupUnfold.lintegral_fundSet_conj_subgroup E r X P hΨ δ _ _ _ _ (fun _ => 1) hG hp hδ hle hi
    (isOrth_x0F X) (isOrth_x0F P) (GlobalTheory.MetricWeightTest.exists_fundSet_orth X (isOrth_x0F X)).choose_spec
    (GlobalTheory.MetricWeightTest.exists_fundSet_orth P (isOrth_x0F P)).choose_spec measurable_const
    (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
  rw [setLIntegral_one, setLIntegral_one] at h
  rw [covol, covol, h, ENNReal.toReal_mul, ENNReal.toReal_natCast, congrArg Finset.card hΨ]
  ring

theorem covol_mul_relIndex (X X' : Data E r) (δ : GL (Fin r) E) (hΨ : X'.Ψ = X.Ψ) (hG : X'.Gm = X.Gm)
    (hp : X'.p0 = X.p0) (hδ : ∀ v w, herm X.Gm (δ.1 *ᵥ v) (δ.1 *ᵥ w) = herm X.Gm v w) :
    covol X * ((X'.Γ.map (MulAut.conj δ).toMonoidHom).relIndex X.Γ : ℝ) =
      covol X' * (X.Γ.relIndex (X'.Γ.map (MulAut.conj δ).toMonoidHom) : ℝ) := by
  set f := (MulAut.conj δ).toMonoidHom with hf
  have hinj : Function.Injective f := (MulAut.conj δ).injective
  have h1 := GlobalTheory.ArithIndex.relIndex_map_conj_ne_zero X' X δ hG (by rw [hG]; exact hδ)
  have h2 := GlobalTheory.ArithIndex.relIndex_map_conj_ne_zero X X' δ⁻¹ hG.symm (GlobalTheory.SubgroupUnfold.isIsom_inv hδ)
  have e : X.Γ.map (MulAut.conj δ⁻¹).toMonoidHom = X.Γ.comap f := by
    ext k
    rw [mem_map_conj, inv_inv]; rfl
  rw [e] at h2
  have e1 : ∀ K : Subgroup (GL (Fin r) E), K.map (MulAut.conj (1 : GL (Fin r) E)).toMonoidHom = K := fun K => by
    ext k
    rw [mem_map_conj]; simp
  obtain ⟨P, hPΨ, hPG, hPp, hP⟩ := GlobalTheory.T.exists_flagDomainData_of_finiteIndex_subgroup E r X' (X.Γ.comap f ⊓ X'.Γ) inf_le_right
    (by rwa [Subgroup.inf_relIndex_right])
  have e2 : P.Γ.map f = X'.Γ.map f ⊓ X.Γ := by
    rw [hP, Subgroup.map_inf _ _ _ hinj, Subgroup.map_comap_eq_self_of_surjective (MulAut.conj δ).surjective,
      inf_comm]
  have a := covol_of_le X P δ (hPΨ.trans hΨ) (hPG.trans hG) (hPp.trans hp) hδ (e2 ▸ inf_le_right)
    (by rwa [← hf, e2, Subgroup.inf_relIndex_right])
  have b := covol_of_le X' P 1 hPΨ hPG hPp (by simp) (by rw [e1, hP]; exact inf_le_right)
    (by rwa [e1, hP, Subgroup.inf_relIndex_right])
  rw [← hf, e2, Subgroup.inf_relIndex_right] at a
  rw [e1, hP, Subgroup.inf_relIndex_right, Subgroup.relIndex_comap] at b
  rw [← a, b]

end Covolume

theorem covol_eq_of_same_space : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (r : ℕ) (Y Y' : ReciprocityTheory.ChartRestriction.G.FD.Data E r), (∀ p : ℕ, p.Prime → l.GoodAt p) → (∀ τ : E →+* ℂ, τ ∈ Y.Ψ ↔ τ (H.rt : E) = H.rt0) → Y'.Ψ = Y.Ψ → Y'.Gm = Y.Gm → Y'.ξ0 = Y.ξ0 → Y'.p0 = Y.p0 → 1 ≤ Y.p0 → Y.p0 < r → GlobalTheory.EqCovol.IsLevGrp l Y → GlobalTheory.EqCovol.IsLevGrp l Y' → GlobalTheory.EqCovol.IsSelfDualTr Y → GlobalTheory.EqCovol.IsSelfDualTr Y' → GlobalTheory.TrueCx.covol Y = GlobalTheory.TrueCx.covol Y' := by
  intro E _ _ _ H l r Y Y' _ _ hΨ hG hξ hp h1 h2 hl hl' hs hs'
  haveI := H.unram
  set F := maximalRealSubfield E
  set c : E ≃ₐ[F] E := IsCMField.complexConj E with hc
  have hM : 3 ≤ l.M' := l.three_le.trans (Nat.le_of_dvd (Nat.lcm_pos (by have := l.three_le; omega) l.A_pos)
    (Nat.dvd_lcm_left _ _))
  have hM0 : 0 < l.M' := by omega
  have hrk : Module.finrank F E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have hH : IsHerm (c : E →+* E) Y.Gm := ⟨IsCMField.complexConj_apply_apply E, by
    by_contra h
    push Not at h
    exact IsCMField.complexConj_ne_one E (AlgEquiv.ext h), Y.Gm_herm, Y.Gm_det⟩
  have hiso : ∃ z : Fin r → E, z ≠ 0 ∧ hf (c : E →+* E) Y.Gm z z = 0 := GlobalTheory.T.exists_isotropic_indefinite_selfDualTraceForm E H r Y h1 h2 hs
  have hcomap : ∀ Z : Data E r, Z.Gm = Y.Gm → IsLevGrp l Z → IsSelfDualTr Z →
      (cong (sgA c) ((emb F).mapMatrix Y.Gm) (hat F (Z.Λ : Set (Fin r → E))) l.M').comap (embGL F) = Z.Γ := by
    intro Z hZ hlZ hsZ
    ext γ
    rw [Subgroup.mem_comap, embGL_mem_cong c Y.Gm Z.Λ_fg Z.Λ_span hM0, GlobalTheory.T.mem_fullLevelGroup_iff_congruence_lcm E H l r Z hlZ hsZ, ← hZ]
    exact ⟨fun h => ⟨⟨h.1, h.2.2.1⟩, h.2.2.2⟩, fun h => ⟨h.1.1,
      GlobalTheory.T.unitaryCongruence_det_eq_one_of_three_le E r _ Z.Gm Z.Λ γ hM Z.Gm_det Z.Λ_fg Z.Λ_span h.1 h.2, h.1.2, h.2⟩⟩
  have hsd : ∀ Z : Data E r, Z.Gm = Y.Gm → Z.ξ0 = Y.ξ0 → IsSelfDualTr Z → GlobalTheory.SW.SelfD Y Z.Λ := by
    intro Z hZ hZξ hsZ
    refine ⟨Z.Λ_fg, fun x => (hsZ x).trans (forall₂_congr fun y _ => ?_)⟩
    rw [GlobalTheory.ThFr.EF_def, hZ, hZξ]
    rcases Y.κ0_xi with h | h <;> rw [h]
    · rw [mul_div_cancel_left₀ _ two_ne_zero]
    · rw [neg_div, mul_div_cancel_left₀ _ two_ne_zero, neg_neg, neg_mul, map_neg]
      exact ⟨fun ⟨k, hk⟩ => ⟨-k, by rw [Int.cast_neg, ← hk, neg_neg]⟩, fun ⟨k, hk⟩ => ⟨-k, by rw [Int.cast_neg, hk]⟩⟩
  obtain ⟨g, hg, hgU⟩ := GlobalTheory.Ker.OntoLat.exists_adelic_matrix F c (fun _ => rfl) Y (hsd Y rfl rfl hs)
    (hsd Y' hG hξ hs')
  replace hgU : IsU (sgA c) ((emb F).mapMatrix Y.Gm) g.1 := hgU
  have hΓ := hcomap Y rfl hl hs
  have hΓ' := hcomap Y' hG hl' hs'
  rw [← map_conj_cong hgU hg] at hΓ'
  generalize hK : cong (sgA c) ((emb F).mapMatrix Y.Gm) (hat F (Y.Λ : Set (Fin r → E))) l.M' = K at hΓ hΓ'

  obtain ⟨a1, a2⟩ := relIndex_comap c Y.Gm Y.Λ_fg Y.Λ_span hrk hH hiso hM0 hgU K hK.symm
  rw [hΓ, hΓ'] at a1 a2
  have e1 : ∀ K : Subgroup (GL (Fin r) E), K.map (MulAut.conj (1 : GL (Fin r) E)).toMonoidHom = K := fun K => by
    ext k
    rw [mem_map_conj]; simp
  have n1 := GlobalTheory.ArithIndex.relIndex_map_conj_ne_zero Y' Y 1 hG (by simp)
  have n2 := GlobalTheory.ArithIndex.relIndex_map_conj_ne_zero Y Y' 1 hG.symm (by simp)
  have hcov := covol_mul_relIndex Y Y' 1 hΨ hG hp (by simp)
  rw [e1] at n1 n2 hcov

  obtain ⟨s, hsU, hs1, hsc⟩ := exists_det_one_conj_eq
    (by rw [← RingHom.map_det]; exact Y.Gm_det.isUnit.map _) hgU
  obtain ⟨γ, hγU, hγ⟩ := exists_inv_mul_mem_cong c Y.Gm Y.Λ_fg Y.Λ_span hrk hH hiso hM0 hsU hs1
  rw [hK] at hγ
  have e2 : K.map (MulAut.conj (g ^ r)).toMonoidHom = K.map (MulAut.conj (embGL F γ)).toMonoidHom := by
    ext k
    rw [mem_map_conj, mem_map_conj, hsc]
    have : s⁻¹ * k * s = ((embGL F γ)⁻¹ * s)⁻¹ * ((embGL F γ)⁻¹ * k * embGL F γ) * ((embGL F γ)⁻¹ * s) := by
      group
    rw [this, K.mul_mem_cancel_right hγ, K.mul_mem_cancel_left (K.inv_mem hγ)]
  obtain ⟨b1, b2⟩ := relIndex_comap c Y.Gm Y.Λ_fg Y.Λ_span hrk hH hiso hM0 (h := embGL F γ)
    ((isU_emb c Y.Gm).2 hγU) K hK.symm
  have e3 : (K.map (MulAut.conj (embGL F γ)).toMonoidHom).comap (embGL F) =
      Y.Γ.map (MulAut.conj γ).toMonoidHom := by
    ext k
    rw [Subgroup.mem_comap, mem_map_conj, mem_map_conj, ← hΓ, Subgroup.mem_comap, map_mul, map_mul, map_inv]
  rw [e3, hΓ] at b1 b2
  have hcov' := mul_left_cancel₀ (GlobalTheory.TrueCx.covol_pos Y).ne' (covol_mul_relIndex Y Y γ rfl rfl rfl hγU)
  have key := GlobalTheory.T.relIndex_map_conj_symm_of_relIndex_map_conj_pow_symm _ K g r (by omega) (a1 ▸ n1) (a2 ▸ n2)
    (by rw [e2, ← b1, ← b2]; exact_mod_cast hcov')
  rw [← a1, ← a2] at key
  rw [← key] at hcov
  exact mul_right_cancel₀ (Nat.cast_ne_zero.2 n1) hcov

end GlobalTheory.EqCovol.SameSpace
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeEqSelfDualLatticesSameHermitianSpaceStatement
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covolume_eq_selfDual_lattices_same_hermitian_space : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (r : ℕ) (Y Y' : ReciprocityTheory.ChartRestriction.G.FD.Data E r), (∀ p : ℕ, p.Prime → l.GoodAt p) → (∀ τ : E →+* ℂ, τ ∈ Y.Ψ ↔ τ (H.rt : E) = H.rt0) → Y'.Ψ = Y.Ψ → Y'.Gm = Y.Gm → Y'.ξ0 = Y.ξ0 → Y'.p0 = Y.p0 → 1 ≤ Y.p0 → Y.p0 < r → GlobalTheory.EqCovol.IsLevGrp l Y → GlobalTheory.EqCovol.IsLevGrp l Y' → GlobalTheory.EqCovol.IsSelfDualTr Y → GlobalTheory.EqCovol.IsSelfDualTr Y' → GlobalTheory.TrueCx.covol Y = GlobalTheory.TrueCx.covol Y' := by
  first | exact @GlobalTheory.EqCovol.SameSpace.covol_eq_of_same_space | exact GlobalTheory.EqCovol.SameSpace.covol_eq_of_same_space | (intros; apply GlobalTheory.EqCovol.SameSpace.covol_eq_of_same_space <;> assumption)
end
