module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FamilyClassSevenDutiesAndStableLattices
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassNumberDvdHstar

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmTypeNormGeneratorOfKummerFieldLe
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmTypeNormGeneratorOfKummerFieldLe
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.KPsiGen

open GlobalTheory.Mem.FieldsEx GlobalTheory.Mem.BaseExt GlobalTheory.IndefiniteRowSideFullHecke.RootValueClassBasis

variable {E : Type} [Field E] [NumberField E]

theorem typeNorm_of_root [IsCMField E] [IsGalois ℚ E] (r : (E →+* ℂ) → ℕ) (n : ℕ)
    (hr : ∀ τ, r τ + r (ComplexEmbedding.conjugate τ) = n) (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K]
    (hK : ∀ (τ : E →+* ℂ) x, τ x ∈ K) (𝔞 : Ideal (𝓞 E)) {h : ℕ} (hpos : 0 < h) (γ : 𝓞 E) (h0 : γ ≠ 0)
    (hγ : 𝔞 ^ h = Ideal.span {γ}) (β : K) (hb : (β : ℂ) ^ h = ∏ τ : E →+* ℂ, τ (γ : E) ^ r τ) : β ≠ 0 ∧
      Submodule.span (𝓞 K) {β} =
        ∏ τ : E →+* ℂ, Submodule.span (𝓞 K) {x : K | ∃ a ∈ 𝔞, (x : ℂ) = τ (a : E)} ^ r τ ∧
      ∀ σ : K →+* ℂ, ‖σ β‖ ^ 2 = (Ideal.absNorm 𝔞 : ℝ) ^ n := by
  classical
  have : NumberField K := NumberField.mk
  have hβ : β ^ h = ∏ τ : E →+* ℂ, τ.codRestrict K (hK τ) (γ : E) ^ r τ := by
    apply Subtype.ext
    simp only [SubmonoidClass.coe_pow, IntermediateField.coe_prod, hb]
    rfl
  have hβ0 : β ≠ 0 := by
    intro h
    rw [h, zero_pow hpos.ne'] at hβ
    refine Finset.prod_ne_zero_iff.2 (fun τ _ => pow_ne_zero _ ?_) hβ.symm
    rw [map_ne_zero]; exact_mod_cast h0
  refine ⟨hβ0, ?_, fun σ => ?_⟩
  · simp only [fun τ => span_eq_extend K τ (hK τ)]
    refine (GlobalTheory.submodule_eq_span_of_pow_eq_span_pow K _ β _ hpos hβ0
      (fg_prod_pow _ _ _ fun τ => extendIdealHom_fg _ _) ?_).symm
    rw [hβ, ← span_singleton_prod_pow, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← pow_mul, mul_comm, pow_mul, ← map_pow, hγ, extendIdealHom_span]
  · have h1 := norm_typeNorm_sq_eq E r n hr K hK (γ : E) σ
    have h2 : ‖σ (β ^ h)‖ ^ 2 = (Ideal.absNorm (Ideal.span {γ}) : ℝ) ^ n := by
      rw [Ideal.absNorm_span_singleton, Nat.cast_natAbs, Int.cast_abs, hβ]
      rw [← Algebra.coe_norm_int, Rat.cast_intCast] at h1
      exact h1
    rw [← hγ, map_pow, map_pow, norm_pow, Nat.cast_pow, ← pow_mul, ← pow_mul,
      mul_comm _ 2, mul_comm _ n, pow_mul, pow_mul] at h2
    exact (pow_left_inj₀ (by positivity) (by positivity) hpos.ne').1 h2

theorem exists_gen_basis (b : ClassBasis E) (𝔞 : Ideal (𝓞 E)) (h𝔞 : 𝔞 ≠ ⊥) :
    ∃ (γ : 𝓞 E) (α : Eˣ) (a : Fin b.k → ℤ) (k : Fin b.k → ℕ), γ ≠ 0 ∧ (∀ i, classNumber E = b.h i * k i) ∧
      𝔞 ^ classNumber E = Ideal.span {γ} ∧
      (γ : E) = ((α ^ classNumber E * ∏ i, (b.γ i ^ k i) ^ a i : Eˣ) : E) := by
  let 𝔠 : (Ideal (𝓞 E))⁰ := ⟨𝔞, mem_nonZeroDivisors_of_ne_zero h𝔞⟩
  obtain ⟨a, ha⟩ := b.span (ClassGroup.mk E (FractionalIdeal.mk0 E 𝔠))
  have hk : ∀ i, ∃ k, classNumber E = b.h i * k := fun i => (orderOf_dvd_card : b.h i ∣ classNumber E)
  choose k hk using hk
  have h1 : ClassGroup.mk E (FractionalIdeal.mk0 E 𝔠 * (∏ i, b.c i ^ a i)⁻¹) = 1 := by
    rw [map_mul, map_inv, map_prod, ha]
    simp only [map_zpow, mul_inv_cancel]
  obtain ⟨x, hx⟩ := (FractionalIdeal.isPrincipal_iff _).1 (ClassGroup.mk_eq_one_iff.1 h1)
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [FractionalIdeal.spanSingleton_zero] at hx
    exact Units.ne_zero _ hx
  have h2 : FractionalIdeal.mk0 E 𝔠 = toPrincipalIdeal (𝓞 E) E (Units.mk0 x hx0) * ∏ i, b.c i ^ a i := by
    rw [← mul_inv_eq_iff_eq_mul]
    exact Units.ext (by rw [hx, coe_toPrincipalIdeal]; rfl)
  set y : Eˣ := Units.mk0 x hx0 ^ classNumber E * ∏ i, (b.γ i ^ k i) ^ a i with hy
  have h3 : FractionalIdeal.mk0 E 𝔠 ^ classNumber E = toPrincipalIdeal (𝓞 E) E y := by
    rw [h2, hy, mul_pow, map_mul, map_pow, map_prod, ← Finset.prod_pow]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_zpow, map_pow, ← b.pow_eq i, ← pow_mul, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul,
      mul_comm, hk i]
    rfl
  have h4 : ((𝔞 ^ classNumber E : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) =
      FractionalIdeal.spanSingleton (𝓞 E)⁰ (y : E) := by
    rw [← coe_toPrincipalIdeal, ← h3, FractionalIdeal.coeIdeal_pow, Units.val_pow_eq_pow_val]
    rfl
  have h5 : (y : E) ∈ ((𝔞 ^ classNumber E : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) := by
    rw [h4]; exact FractionalIdeal.mem_spanSingleton_self _ _
  obtain ⟨γ, -, hγ⟩ := (FractionalIdeal.mem_coeIdeal _).1 h5
  refine ⟨γ, Units.mk0 x hx0, a, k, ?_, hk, ?_, hγ⟩
  · rintro rfl
    exact y.ne_zero (by rw [← hγ, map_zero])
  · apply FractionalIdeal.coeIdeal_injective (K := E)
    simp only
    rw [h4, FractionalIdeal.coeIdeal_span_singleton, hγ]

theorem typeNorm_of_basis [IsCMField E] [IsGalois ℚ E] (r : (E →+* ℂ) → ℕ) (n : ℕ)
    (hr : ∀ τ, r τ + r (ComplexEmbedding.conjugate τ) = n) (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K]
    (hK : ∀ (τ : E →+* ℂ) x, τ x ∈ K) (b : ClassBasis E)
    (hb : ∀ i (z : ℂ), z ^ b.h i = ∏ τ : E →+* ℂ, τ (b.γ i : E) ^ r τ → z ∈ K)
    (𝔞 : Ideal (𝓞 E)) (h𝔞 : 𝔞 ≠ ⊥) : ∃ β : K, β ≠ 0 ∧
      Submodule.span (𝓞 K) {β} =
        ∏ τ : E →+* ℂ, Submodule.span (𝓞 K) {x : K | ∃ a ∈ 𝔞, (x : ℂ) = τ (a : E)} ^ r τ ∧
      ∀ σ : K →+* ℂ, ‖σ β‖ ^ 2 = (Ideal.absNorm 𝔞 : ℝ) ^ n := by
  obtain ⟨γ, α, a, k, h0, hk, hγ, hy⟩ := exists_gen_basis b 𝔞 h𝔞
  let Ψ : Eˣ →* ℂ :=
    { toFun := fun x => ∏ τ : E →+* ℂ, τ (x : E) ^ r τ
      map_one' := by simp
      map_mul' := fun x y => by simp only [Units.val_mul, map_mul, mul_pow, Finset.prod_mul_distrib] }
  choose ψ hψ using fun i => IsAlgClosed.exists_pow_nat_eq (Ψ (b.γ i)) (b.h_pos i)
  have hm : Ψ α * ∏ i, ψ i ^ a i ∈ K :=
    mul_mem (prod_mem fun τ _ => pow_mem (hK τ _) _) (prod_mem fun i _ => zpow_mem (hb i _ (hψ i)) _)
  refine ⟨⟨_, hm⟩, typeNorm_of_root r n hr K hK 𝔞 (classNumber_pos E) γ h0 hγ _ ?_⟩
  rw [hy]
  change (Ψ α * ∏ i, ψ i ^ a i) ^ _ = Ψ _
  rw [mul_pow, map_mul, map_pow, map_prod, ← Finset.prod_pow]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_zpow, map_pow, ← hψ i, ← pow_mul, ← hk i, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul,
    mul_comm]

theorem typeNorm_gen_of_kPsi_le : ∀ (P : Pre) (δ : FieldDat P) (F : IntermediateField ℚ ℂ) [FiniteDimensional ℚ F] (j : ℕ), δ.KPsi j ≤ F → ∀ 𝔞 : Ideal (𝓞 P.host.E), 𝔞 ≠ ⊥ → ∃ β : F, β ≠ 0 ∧ Submodule.span (𝓞 F) {β} = ∏ g : Tau P.R, (Submodule.span (𝓞 F) {x : F | ∃ a ∈ 𝔞, (x : ℂ) = P.host.φ₀ (P.host.sigmaOf g (a : P.host.E))} ^ (P.R.sigW j).1 * Submodule.span (𝓞 F) {x : F | ∃ a ∈ 𝔞, (x : ℂ) = P.host.φ₀ (P.host.sigmaOf g (P.host.conj (a : P.host.E)))} ^ (P.R.sigW j).2) ∧ ∀ σ : F →+* ℂ, ‖σ β‖ ^ 2 = (Ideal.absNorm 𝔞 : ℝ) ^ ((P.R.sigW j).1 + (P.R.sigW j).2) := by
  intro P δ F _ j hF 𝔞 h𝔞
  have hcm : IsCMField P.host.E := P.host.isCMField_hostE
  have hgal : IsGalois ℚ P.host.E := P.host.hostE_isGalois
  simp only [FieldDat.KPsi, kPsiField, sup_le_iff, imField_le_iff, IntermediateField.adjoin_le_iff] at hF
  obtain ⟨⟨hE, -⟩, hψ⟩ := hF
  have hK : ∀ (τ : P.host.E →+* ℂ) x, τ x ∈ F := fun τ x => by
    obtain ⟨σ, hσ⟩ := exists_aut P.host.φ₀ τ
    rw [hσ]; exact hE _
  obtain ⟨β, hβ, hsp, hn⟩ := typeNorm_of_basis (typeExp P.host (P.R.sigW j).1 (P.R.sigW j).2) _
    (typeExp_add P.host _ _) F hK δ.basis (fun i z hz => hψ ⟨i, by
      rw [hz, prod_typeExp, typeNorm, map_prod]
      refine Finset.prod_congr rfl fun g _ => ?_
      rw [map_mul, map_pow, map_pow, conjugate_emb_apply]
      rfl⟩) 𝔞 h𝔞
  refine ⟨β, hβ, ?_, hn⟩
  rw [hsp, prod_typeExp]
  refine Finset.prod_congr rfl fun g _ => ?_
  simp only [conjugate_emb_apply]
  rfl

end GlobalTheory.Mem.KPsiGen

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmTypeNormGeneratorOfKummerFieldLeStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmTypeNorm_generator_of_kummerField_le : ∀ (P : Pre) (δ : FieldDat P) (F : IntermediateField ℚ ℂ) [FiniteDimensional ℚ F] (j : ℕ), δ.KPsi j ≤ F → ∀ 𝔞 : Ideal (𝓞 P.host.E), 𝔞 ≠ ⊥ → ∃ β : F, β ≠ 0 ∧ Submodule.span (𝓞 F) {β} = ∏ g : Tau P.R, (Submodule.span (𝓞 F) {x : F | ∃ a ∈ 𝔞, (x : ℂ) = P.host.φ₀ (P.host.sigmaOf g (a : P.host.E))} ^ (P.R.sigW j).1 * Submodule.span (𝓞 F) {x : F | ∃ a ∈ 𝔞, (x : ℂ) = P.host.φ₀ (P.host.sigmaOf g (P.host.conj (a : P.host.E)))} ^ (P.R.sigW j).2) ∧ ∀ σ : F →+* ℂ, ‖σ β‖ ^ 2 = (Ideal.absNorm 𝔞 : ℝ) ^ ((P.R.sigW j).1 + (P.R.sigW j).2) := by
  first | exact @GlobalTheory.Mem.KPsiGen.typeNorm_gen_of_kPsi_le | exact GlobalTheory.Mem.KPsiGen.typeNorm_gen_of_kPsi_le | (intros; apply GlobalTheory.Mem.KPsiGen.typeNorm_gen_of_kPsi_le <;> assumption)
end
end

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld GlobalTheory.Mem.BaseExt
  GlobalTheory.Mem.FieldsEx
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.KsBase

theorem span_eq_of_isPrincipal {E : Type} [Field E] (φ : E →+* ℂ) (F : IntermediateField ℚ ℂ) (hF : ∀ x, φ x ∈ F)
    (𝔞 : Ideal (𝓞 E)) (h : (𝔞.map (RingOfIntegers.mapRingHom (φ.codRestrict F hF))).IsPrincipal) :
    ∃ β : F, Submodule.span (𝓞 F) {β} = Submodule.span (𝓞 F) {x : F | ∃ a ∈ 𝔞, (x : ℂ) = φ (a : E)} := by
  obtain ⟨b, hb⟩ := h
  refine ⟨(b : F), ?_⟩
  have h := congrArg (Submodule.map (Algebra.linearMap (𝓞 F) F)) hb
  rw [Submodule.map_span, Set.image_singleton, Ideal.map, Ideal.span, Submodule.map_span, Set.image_image] at h
  refine h.symm.trans (congrArg _ ?_)
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, hx⟩
    exact ⟨a, ha, Subtype.ext hx.symm⟩

theorem exists_base_of_contents (B : Pre) (F : IntermediateField ℚ ℂ) [FiniteDimensional ℚ F]
    (hEF : ∀ x, B.host.φ₀ x ∈ F) (hr : rootsField B ≤ F) (hp : rootOne B.host.pde ∈ F)
    (hp' : rootOne B.host.pde' ∈ F) (hh : rootOne (classNumber B.host.E) ∈ F)
    (hc : ∀ 𝔞 : Ideal (𝓞 B.host.E), ∃ β : F,
      Submodule.span (𝓞 F) {β} = Submodule.span (𝓞 F) {x : F | ∃ a ∈ 𝔞, (x : ℂ) = B.host.φ₀ (a : B.host.E)})
    (hk : ∀ j, 1 ≤ j → j ≤ B.R.m → ∀ 𝔞 : Ideal (𝓞 B.host.E), 𝔞 ≠ ⊥ → ∃ β : F, β ≠ 0 ∧
      Submodule.span (𝓞 F) {β} = ∏ g : Tau B.R,
        (Submodule.span (𝓞 F) {x : F | ∃ a ∈ 𝔞, (x : ℂ) = B.host.φ₀ (B.host.sigmaOf g (a : B.host.E))} ^
            (B.R.sigW j).1 *
          Submodule.span (𝓞 F)
            {x : F | ∃ a ∈ 𝔞, (x : ℂ) = B.host.φ₀ (B.host.sigmaOf g (B.host.conj (a : B.host.E)))} ^
            (B.R.sigW j).2) ∧
      ∀ σ : F →+* ℂ, ‖σ β‖ ^ 2 = (Ideal.absNorm 𝔞 : ℝ) ^ ((B.R.sigW j).1 + (B.R.sigW j).2)) :
    ∃ B' : Base, B'.toPre = B ∧ B'.KsC = F := by
  classical
  obtain ⟨SF, hSF, hF⟩ := exists_gens_le F
  let A : Finset ℕ := {B.ramOrder} ∪ Finset.univ.image B.T
  let SR : Finset ℂ := A.image fun N : ℕ => Complex.exp (2 * Real.pi * Complex.I / N)
  obtain ⟨K, hfd, hKgal, hS, -, hconj⟩ := GlobalTheory.exists_galois_subfield_conj_stable (SF ∪ SR) (by
      intro z hz
      rcases Finset.mem_union.1 hz with hz | hz
      exacts [hSF z hz, by
        obtain ⟨N, -, rfl⟩ := Finset.mem_image.1 hz
        exact isAlgebraic_exp N])
  simp only [Finset.mem_union] at hS
  have hFK : F ≤ K := hF K fun z hz => hS z (.inl hz)
  have hEK : ∀ x, B.host.φ₀ x ∈ K := fun x => hFK (hEF x)
  have hR : ∀ N ∈ A, Complex.exp (2 * Real.pi * Complex.I / (N : ℕ)) ∈ K := fun N hN => by
    have hz : Complex.exp (2 * Real.pi * Complex.I / N) ∈ SR := Finset.mem_image.2 ⟨N, hN, rfl⟩
    exact hS _ (.inr hz)
  have : NumberField K := {}
  simp only [rootsField, sup_le_iff, cycField_le_iff] at hr
  obtain ⟨⟨⟨⟨hr1, hr2⟩, hr3⟩, hr4⟩, hr5⟩ := hr
  let f := toComap hFK
  refine ⟨{ toPre := B
            LL := K
            starLL := starOf K hconj
            embLL := K.val
            starLL_cx := fun _ => rfl
            embE := B.host.φ₀.codRestrict K hEK
            embE_φ₀ := rfl
            LL0 := ⊤
            coeffGaloisSubfield_isGalois := IsGalois.of_algEquiv IntermediateField.topEquiv.symm
            Ks := F.comap K.val
            Ks_le := le_top
            E_le_Ks := hEF
            roots_Ks := ?_
            roots_Ks' := ?_
            capit := ?_
            kPsi := ?_
            rootOfUnity_eightQ_mem_coeffGaloisSubfield := ⟨⟨_, hR B.ramOrder (by simp [A])⟩, trivial, rfl⟩
            roots_LL := fun u => ⟨⟨_, hR (B.T u) (Finset.mem_union_right _
              (Finset.mem_image_of_mem _ (Finset.mem_univ u)))⟩, rfl⟩ }, rfl, IntermediateField.ext fun z => ?_⟩
  · intro N hN
    have h : rootOne N ∈ F := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hN
      rcases hN with rfl | rfl | rfl | rfl | rfl <;> assumption
    exact ⟨⟨_, hFK h⟩, h, rfl⟩
  · intro N hN
    have h : rootOne N ∈ F := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hN
      rcases hN with rfl | rfl | rfl <;> assumption
    exact ⟨⟨_, hFK h⟩, h, rfl⟩
  · intro 𝔞
    obtain ⟨β, hsp⟩ := hc 𝔞
    refine ⟨f β, ?_⟩
    have h := congrArg (extend f) hsp
    rw [extend_span, Set.image_singleton] at h
    exact h.trans (image_comap hFK 𝔞 B.host.φ₀ (B.host.φ₀.codRestrict K hEK) fun _ => rfl)
  · intro j hj1 hj 𝔞 h𝔞
    obtain ⟨β, hβ, hsp, hn⟩ := hk j hj1 hj 𝔞 h𝔞
    refine ⟨f β, (map_ne_zero f).2 hβ, ?_, fun σ => hn (σ.comp f)⟩
    have h := congrArg (extend f) hsp
    rw [extend_span, Set.image_singleton, map_prod] at h
    refine h.trans (Finset.prod_congr rfl fun g _ => ?_)
    have e1 := image_comap hFK 𝔞 (B.host.φ₀.comp (B.host.sigmaOf g : B.host.E →+* B.host.E))
      (fun a => B.host.φ₀.codRestrict K hEK (B.host.sigmaOf g a)) fun _ => rfl
    have e2 := image_comap hFK 𝔞 ((B.host.φ₀.comp (B.host.sigmaOf g : B.host.E →+* B.host.E)).comp
        (B.host.conj : B.host.E →+* B.host.E))
      (fun a => B.host.φ₀.codRestrict K hEK (B.host.sigmaOf g (B.host.conj a))) fun _ => rfl
    rw [map_mul, map_pow, map_pow]
    exact congrArg₂ (· * ·) (congrArg (· ^ (B.R.sigW j).1) e1) (congrArg (· ^ (B.R.sigW j).2) e2)
  · constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · exact fun hz => ⟨⟨z, hFK hz⟩, hz, rfl⟩

theorem exists_base_listField (hR : RayField) (hP : PrincipalIdealSt) (P : Pre) (f : GlobalTheory.Mem.Top.Fr P)
    (δ : FieldDat P) : listField δ f ≤ δ.Om ∧ ∃ B : Base, B.toPre = P ∧ B.KsC = listField δ f := by
  have hO : listField δ f ≤ δ.Om := listField_le_Om δ f
  have := host_cplx P
  have := finite_Om δ
  have : FiniteDimensional ℚ (listField δ f) :=
    FiniteDimensional.of_injective (IntermediateField.inclusion hO).toLinearMap (IntermediateField.inclusion_injective hO)
  obtain ⟨h1, -, h3, h4, -, h6⟩ := (listField_le_iff δ f).1 le_rfl
  have hm : 1 ≤ P.R.m := le_trans one_le_two P.R.two_le_m
  refine ⟨hO, exists_base_of_contents P _ ((imField_le_iff _).1 h1) h4
    (h3 (rootOne_mem_ray _ (modulus_ne_zero P) (pde_dvd P) δ.isRay))
    (h3 (rootOne_mem_ray _ (modulus_ne_zero P) (pde'_dvd P) δ.isRay))
    (cycField_le_iff.1 ((le_sup_right.trans le_sup_left).trans (h6 1 le_rfl hm)))
    (fun 𝔞 => span_eq_of_isPrincipal _ _ _ 𝔞
      (hP.of_isRayFieldIn hR (natIdeal_ne_bot (modulus_ne_zero P)) δ.isRay h3 𝔞))
    fun j hj hj' => GlobalTheory.T.cmTypeNorm_generator_of_kummerField_le P δ _ j (h6 j hj hj')⟩

end GlobalTheory.Mem.KsBase

end
