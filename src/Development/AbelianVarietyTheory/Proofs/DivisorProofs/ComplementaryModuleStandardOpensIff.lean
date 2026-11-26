module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTraceDualLocalizationIffForallRegularForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartEqOneOfLevel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplementaryModuleEqTopFormsOfFiniteCover
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOfForallHeightOneLocalizationIntegrallyClosed
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOfForallHeightOneLocalizationIntegrallyClosed
namespace GlobalTheory.NormalHeightOne

theorem mem_of_forall_height_eq_one : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] (z : K),
    (∀ Q : Ideal A, Q.IsPrime → Q.height = 1 → ∃ r c : A, r ∉ Q ∧ algebraMap A K r * z = algebraMap A K c) →
    ∃ c : A, z = algebraMap A K c := by
  intro A K _ _ _ _ _ _ _ z h
  have hz := ((GlobalTheory.normal_domain_height_one.{0, 0, 0} A K).2.1 z).2 (fun p _ hp => by
    obtain ⟨r, c, hr, e⟩ := h p inferInstance hp
    exact (GlobalTheory.mem_primeLocalSubalgebra_iff p z).2 ⟨r, hr, ⟨c, by rw [Algebra.smul_def, e]⟩⟩)
  obtain ⟨c, hc⟩ := hz
  exact ⟨c, hc.symm⟩

end GlobalTheory.NormalHeightOne
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOfForallHeightOneLocalizationIntegrallyClosedStatement
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_of_forall_heightOne_localization_integrallyClosed : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] (z : K), (∀ Q : Ideal A, Q.IsPrime → Q.height = 1 → ∃ r c : A, r ∉ Q ∧ algebraMap A K r * z = algebraMap A K c) → ∃ c : A, z = algebraMap A K c := by
  first | (exact @GlobalTheory.NormalHeightOne.mem_of_forall_height_eq_one) | (exact GlobalTheory.NormalHeightOne.mem_of_forall_height_eq_one) | (intros; apply GlobalTheory.NormalHeightOne.mem_of_forall_height_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplementaryModuleEqTopFormsOfFiniteCover
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

noncomputable section

namespace GlobalTheory.ComplementaryForms

theorem height_under_eq_one {A B : Type} [CommRing A] [IsDomain A] [CommRing B]
    [Algebra A B] [Algebra.HasGoingDown A B] (Q : Ideal B) [Q.IsPrime] (hQ : Q.height = 1)
    (hne : Q.comap (algebraMap A B) ≠ ⊥) : (Q.comap (algebraMap A B)).height = 1 := by
  set p : Ideal A := Q.comap (algebraMap A B) with hp
  haveI : p.IsPrime := Ideal.comap_isPrime _ Q
  haveI : Q.LiesOver p := ⟨rfl⟩
  apply le_antisymm
  · rw [show ((1 : ℕ∞)) = ((1 : ℕ) : ℕ∞) from rfl, Ideal.height_le_iff]
    intro r hr hrp
    by_contra hcon
    have hr0 : r ≠ ⊥ := by
      rintro rfl
      simp at hcon
    haveI := hr
    obtain ⟨P₁, hP₁Q, hP₁, hP₁o⟩ := Ideal.exists_ideal_lt_liesOver_of_lt (p := r) (q := p) Q hrp
    haveI := hP₁
    haveI : (⊥ : Ideal A).IsPrime := Ideal.isPrime_bot
    obtain ⟨P₀, hP₀P₁, hP₀, -⟩ := Ideal.exists_ideal_lt_liesOver_of_lt (p := ⊥) (q := r) P₁
      (bot_lt_iff_ne_bot.mpr hr0)
    haveI := hP₀
    have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hP₀P₁
    have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hP₁Q
    rw [hQ] at h2
    have h4 : (1 : ℕ∞) ≤ P₁.height := le_trans le_add_self h1
    have h3 : (1 : ℕ∞) + 1 ≤ 1 := le_trans (by gcongr) h2
    exact absurd h3 (by decide)
  · haveI : (⊥ : Ideal A).IsPrime := Ideal.isPrime_bot
    have := Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.mpr hne)
    simpa using this


open KaehlerDifferential in
open scoped IntermediateField.algebraAdjoinAdjoin in
theorem exists_basis_D (k F K : Type) [Field k] [Field F] [Field K] [Algebra k F] [Algebra k K]
    [Algebra F K] [IsScalarTower k F K] [Algebra.IsSeparable F K] (d : ℕ) (v : Fin d → F)
    (hv : AlgebraicIndependent k v) (hgen : IntermediateField.adjoin k (Set.range v) = ⊤) :
    ∃ b : Module.Basis (Fin d) K Ω[K⁄k], ∀ j, b j = D k K (algebraMap F K (v j)) := by
  let P := MvPolynomial (Fin d) k
  let A := Algebra.adjoin k (Set.range v)
  let L := IntermediateField.adjoin k (Set.range v)
  letI : Algebra P A := hv.aevalEquiv.toAlgHom.toRingHom.toAlgebra
  haveI : IsScalarTower k P A := .of_algebraMap_eq fun r => (hv.aevalEquiv.commutes r).symm
  haveI : Algebra.FormallyEtale P A :=
    .of_equiv (AlgEquiv.ofBijective (Algebra.ofId P A) hv.aevalEquiv.bijective)
  haveI : Algebra.FormallyEtale A L := .of_isLocalization (nonZeroDivisors _)
  haveI : Algebra.IsSeparable L F := ⟨fun a => by
    have ha : a ∈ L := by rw [show L = ⊤ from hgen]; trivial
    exact (show algebraMap L F ⟨a, ha⟩ = a from rfl) ▸ isSeparable_algebraMap _⟩
  haveI : Algebra.FormallyEtale L F := Algebra.FormallyEtale.of_isSeparable _ F
  haveI : Algebra.FormallyEtale A F := .comp A L F
  haveI : Algebra.FormallyEtale F K := Algebra.FormallyEtale.of_isSeparable F K
  let b₁ : Module.Basis (Fin d) A Ω[A⁄k] :=
    ((mvPolynomialBasis k (Fin d)).baseChange A).map (tensorKaehlerEquivOfFormallyEtale k P A)
  let b₂ : Module.Basis (Fin d) F Ω[F⁄k] := (b₁.baseChange F).map (tensorKaehlerEquivOfFormallyEtale k A F)
  have h₂ : ∀ j, b₂ j = D k F (v j) := by
    intro j
    simp only [b₂, b₁, Module.Basis.map_apply, Module.Basis.baseChange_apply, tensorKaehlerEquivOfFormallyEtale_apply,
      mapBaseChange_tmul, one_smul, mvPolynomialBasis_apply, map_D]
    have e : algebraMap A F (algebraMap P A (MvPolynomial.X j)) = v j := by
      change algebraMap A F (hv.aevalEquiv (MvPolynomial.X j)) = v j
      rw [hv.algebraMap_aevalEquiv, MvPolynomial.aeval_X]
    rw [← e, ← map_D k k A F, ← map_D k k P A]
    exact congrArg _ ((mapBaseChange_tmul k P A 1 _).trans (one_smul _ _))
  refine ⟨(b₂.baseChange K).map (tensorKaehlerEquivOfFormallyEtale k F K), fun j => ?_⟩
  simp only [Module.Basis.map_apply, Module.Basis.baseChange_apply, tensorKaehlerEquivOfFormallyEtale_apply,
    mapBaseChange_tmul, one_smul, h₂, map_D]

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

theorem local_frame (k K : Type) [Field k] [Field K] [Algebra k K] (B : Subalgebra k K) (d : ℕ)
    (τ : DR k K →ₗ[K] K) (w : Fin d → Ω[K⁄k]) (hw : τ (ExteriorAlgebra.ιMulti K d w) = 1)
    (f : B) (u' : Fin d → B) (b : Module.Basis (Fin d) K Ω[K⁄k]) (hb : ∀ j, b j = D k K (u' j : K))
    (hc : ∀ (v : B) (j : Fin d), ∃ c : B, (f : K) * b.repr (D k K (v : K)) j = c) :
    τ (ExteriorAlgebra.ιMulti K d (fun j => D k K (u' j : K))) ≠ 0 ∧
    ∀ y ∈ omB k K B d, ∃ c : B,
      (f : K) ^ d * τ y = τ (ExteriorAlgebra.ιMulti K d (fun j => D k K (u' j : K))) * c := by
  classical
  let φ : Ω[K⁄k] [⋀^Fin d]→ₗ[K] K := τ.compAlternatingMap (ExteriorAlgebra.ιMulti K d)
  have hφ : ∀ v, τ (ExteriorAlgebra.ιMulti K d v) = φ v := fun v => rfl
  have hb' : (⇑b) = fun j => D k K (u' j : K) := funext hb
  have key : ∀ v, φ v = τ (ExteriorAlgebra.ιMulti K d (fun j => D k K (u' j : K))) * b.det v := by
    intro v
    conv_lhs => rw [AlternatingMap.eq_smul_basis_det b φ]
    rw [AlternatingMap.smul_apply, smul_eq_mul, hφ, hb']
  set g := τ (ExteriorAlgebra.ιMulti K d (fun j => D k K (u' j : K))) with hg
  refine ⟨fun h0 => ?_, fun y hy => ?_⟩
  · have := key w
    rw [← hφ, hw, h0, zero_mul] at this
    exact one_ne_zero this
  have hdet : ∀ v : Fin d → K, (∀ j, v j ∈ B) →
      ∃ c : B, (f : K) ^ d * b.det (fun j => D k K (v j)) = c := by
    intro v hv
    choose M hM using fun i j => hc ⟨v j, hv j⟩ i
    refine ⟨(Matrix.of M).det, ?_⟩
    have hs := Matrix.det_smul (b.toMatrix fun j => D k K (v j)) (f : K)
    rw [Fintype.card_fin] at hs
    rw [Module.Basis.det_apply, ← hs]
    have : (f : K) • b.toMatrix (fun j => D k K (v j)) = (algebraMap B K).mapMatrix (Matrix.of M) := by
      ext i j
      simp only [Matrix.smul_apply, Module.Basis.toMatrix_apply, smul_eq_mul, RingHom.mapMatrix_apply,
        Matrix.map_apply, Matrix.of_apply]
      exact hM i j
    rw [this, ← RingHom.map_det]
    rfl
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c₀, hc₀, v, hv, rfl⟩ := hx
    obtain ⟨c, hc'⟩ := hdet v hv
    refine ⟨⟨c₀, hc₀⟩ * c, ?_⟩
    rw [map_smul, smul_eq_mul, hφ, key]
    push_cast
    rw [← hc']
    ring
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c₁, h₁⟩ := hx
    obtain ⟨c₂, h₂⟩ := hy
    exact ⟨c₁ + c₂, by rw [map_add (f := _), mul_add, h₁, h₂]; push_cast; ring⟩
  | smul a x _ hx =>
    obtain ⟨c, h⟩ := hx
    refine ⟨algebraMap k B a * c, ?_⟩
    rw [LinearMap.map_smul_of_tower, Algebra.smul_def, mul_left_comm, h]
    push_cast
    rw [IsScalarTower.algebraMap_apply k B K]
    ring

end GlobalTheory.ComplementaryForms

namespace GlobalTheory.ComplementaryForms

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

theorem complementary_eq_topForms : ∀ (k F K : Type) [Field k] [CharZero k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] [FiniteDimensional F K] (d : ℕ) (u : Fin d → F), AlgebraicIndependent k u → ∀ (A : Subalgebra k F) [IsFractionRing A F], A = Algebra.adjoin k (Set.range u) → ∀ (B : Subalgebra k K), B = (integralClosure A K).restrictScalars k → Algebra.Smooth k B → ∀ τ : DR k K →ₗ[K] K, τ (ExteriorAlgebra.ιMulti K d fun j => D k K (algebraMap F K (u j))) = 1 → ∀ z : K, (∀ b : B, Algebra.trace F K (z * b) ∈ A) ↔ ∃ y ∈ omB k K B d, τ y = z := by
  intro k F K _ _ _ _ _ _ _ _ _ d u hu A _ hA B hB hsm τ hτ z
  classical
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap k F).injective
  haveI : Algebra.IsSeparable F K := inferInstance

  haveI : IsNoetherianRing A := by
    subst hA; exact isNoetherianRing_of_ringEquiv _ hu.aevalEquiv.toRingEquiv
  haveI : UniqueFactorizationMonoid A := by
    subst hA; exact hu.aevalEquiv.toMulEquiv.uniqueFactorizationMonoid inferInstance
  haveI : IsIntegrallyClosed A := inferInstance
  have hgen : IntermediateField.adjoin k (Set.range u) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨a, s, -, rfl⟩ := IsFractionRing.div_surjective (A := A) x
    have hle : ∀ t : A, (t : F) ∈ IntermediateField.adjoin k (Set.range u) := by
      intro t
      have ht : (t : F) ∈ Algebra.adjoin k (Set.range u) := hA ▸ t.2
      exact IntermediateField.algebra_adjoin_le_adjoin k _ ht
    exact div_mem (hle a) (hle s)
  have hrank : Module.finrank K Ω[K⁄k] = d := by
    obtain ⟨b, -⟩ := exists_basis_D k F K d u hu hgen
    simpa using Module.finrank_eq_card_basis b

  let C := integralClosure A K
  haveI : IsFractionRing C K := integralClosure.isFractionRing_of_finite_extension F K
  haveI : IsIntegrallyClosed C := integralClosure.isIntegrallyClosedOfFiniteExtension F
  haveI : IsNoetherianRing C := IsIntegralClosure.isNoetherianRing A F K C
  have hmem : ∀ x : K, x ∈ B ↔ x ∈ C := by subst hB; exact fun x => Iff.rfl
  let e : C ≃+* B :=
    { toFun := fun x => ⟨x.1, (hmem _).2 x.2⟩
      invFun := fun x => ⟨x.1, (hmem _).1 x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  haveI : IsNoetherianRing B := isNoetherianRing_of_ringEquiv C e
  haveI : IsFractionRing B K := by subst hB; exact inferInstanceAs (IsFractionRing C K)
  haveI : IsIntegrallyClosed B := by subst hB; exact inferInstanceAs (IsIntegrallyClosed C)
  haveI : Algebra.Smooth k B := hsm
  haveI : FaithfulSMul A C := by
    refine (faithfulSMul_iff_algebraMap_injective A C).mpr fun a a' h => ?_
    have h' : algebraMap F K (a : F) = algebraMap F K (a' : F) := congrArg (fun x : C => (x : K)) h
    exact Subtype.val_injective ((algebraMap F K).injective h')
  haveI : Algebra.HasGoingDown A C := inferInstance

  have hunder : ∀ Q : Ideal B, Q.IsPrime → Q.height = 1 →
      ∃ p : Ideal A, p.IsPrime ∧ p.height = 1 ∧
        ∀ a : A, ∀ b : B, (b : K) = algebraMap F K a → (b ∈ Q ↔ a ∈ p) := by
    intro Q hQ hQ1
    set Q' : Ideal C := Q.comap (e : C →+* B)
    haveI : Q'.IsPrime := Ideal.comap_isPrime _ Q
    have hQ'1 : Q'.height = 1 := (RingEquiv.height_comap e Q).trans hQ1
    have hne : Q'.comap (algebraMap A C) ≠ ⊥ := by
      have hQ'0 : Q' ≠ ⊥ := by
        rintro h
        rw [h, Ideal.height_bot] at hQ'1
        exact zero_ne_one hQ'1
      obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hQ'0
      exact Ideal.comap_ne_bot_of_integral_mem hx0 hx (integralClosure.isIntegral x)
    refine ⟨Q'.comap (algebraMap A C), Ideal.comap_isPrime _ _, height_under_eq_one Q' hQ'1 hne, ?_⟩
    intro a b hab
    have : b = e (algebraMap A C a) := by
      apply Subtype.ext
      rw [hab]
      rfl
    rw [this]
    rfl
  constructor
  · intro hz
    let J : Ideal B :=
      { carrier := {c | ∃ y ∈ omB k K B d, τ y = (c : K) * z}
        add_mem' := by
          rintro c₁ c₂ ⟨y₁, hy₁, h₁⟩ ⟨y₂, hy₂, h₂⟩
          exact ⟨y₁ + y₂, add_mem hy₁ hy₂, by rw [map_add (f := _), h₁, h₂]; push_cast; ring⟩
        zero_mem' := ⟨0, zero_mem _, by simp⟩
        smul_mem' := by
          rintro c c' ⟨y, hy, h⟩
          refine ⟨(c : K) • y, ((GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties k K B d d).2.1 y hy).2.2.2 _ c.2, ?_⟩
          rw [map_smul, h, smul_eq_mul, smul_eq_mul]
          push_cast
          ring }
    suffices h1J : (1 : B) ∈ J by
      obtain ⟨y, hy, h⟩ := h1J
      exact ⟨y, hy, by simpa using h⟩
    by_contra hJ
    obtain ⟨P, hPmax, hJP⟩ := Ideal.exists_le_maximal J (fun h => hJ (h ▸ Submodule.mem_top))
    haveI := hPmax.isPrime
    obtain ⟨f, u', bP, hfP, hb, hc⟩ := GlobalTheory.T.exists_local_kaehlerD_basis_smooth_subalgebra k K B d hrank P
    obtain ⟨hg0, hloc⟩ := local_frame k K B d τ _ hτ f u' bP hb hc
    set g := τ (ExteriorAlgebra.ιMulti K d (fun j => D k K (u' j : K))) with hg
    obtain ⟨c, hcw⟩ := GlobalTheory.T.mem_of_forall_heightOne_localization_integrallyClosed B K ((f : K) ^ d * z / g) (by
      intro Q hQ hQ1
      obtain ⟨p, hp, hp1, hover⟩ := hunder Q hQ hQ1
      have hcod := (GlobalTheory.T.mem_traceDual_localization_iff_forall_regularForm_alt k F K d u hu A hA B hB hsm τ hτ p hp hp1 z).1 (fun b =>
        ⟨1, ⟨_, hz b⟩, (Ideal.ne_top_iff_one p).1 hp.ne_top, by simp⟩)
      obtain ⟨r, hr, y, hy, hyz⟩ := hcod Q hQ hover
      obtain ⟨c, hc'⟩ := hloc y hy
      refine ⟨r, c, hr, ?_⟩
      change (r : K) * ((f : K) ^ d * z / g) = c
      rw [mul_div_assoc', mul_left_comm, ← hyz, hc', mul_div_assoc]
      field_simp)
    have hfd : f ^ d ∈ J := by
      refine ⟨(c : K) • ExteriorAlgebra.ιMulti K d (fun j => D k K (u' j : K)),
        Submodule.subset_span ⟨c, c.2, _, fun j => (u' j).2, rfl⟩, ?_⟩
      rw [map_smul, smul_eq_mul, ← hg]
      have hcw' : (f : K) ^ d * z / g = c := hcw
      rw [← hcw']
      push_cast
      field_simp
    exact hfP (hPmax.isPrime.mem_of_pow_mem d (hJP hfd))
  · rintro ⟨y, hy, rfl⟩ b
    obtain ⟨c, hc⟩ := GlobalTheory.T.mem_of_forall_heightOne_localization_integrallyClosed A F (Algebra.trace F K (τ y * b)) (by
      intro p hp hp1
      exact (GlobalTheory.T.mem_traceDual_localization_iff_forall_regularForm_alt k F K d u hu A hA B hB hsm τ hτ p hp hp1 (τ y)).2
        (fun Q hQ _ => ⟨1, (Ideal.ne_top_iff_one Q).1 hQ.ne_top, y, hy, by simp⟩) b)
    rw [hc]
    exact c.2

end GlobalTheory.ComplementaryForms
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplementaryModuleEqTopFormsOfFiniteCoverStatement
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complementaryModule_eq_topForms_of_finiteCover : ∀ (k F K : Type) [Field k] [CharZero k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] [FiniteDimensional F K] (d : ℕ) (u : Fin d → F), AlgebraicIndependent k u → ∀ (A : Subalgebra k F) [IsFractionRing A F], A = Algebra.adjoin k (Set.range u) → ∀ (B : Subalgebra k K), B = (integralClosure A K).restrictScalars k → Algebra.Smooth k B → ∀ τ : DR k K →ₗ[K] K, τ (ExteriorAlgebra.ιMulti K d fun j => D k K (algebraMap F K (u j))) = 1 → ∀ z : K, (∀ b : B, Algebra.trace F K (z * b) ∈ A) ↔ ∃ y ∈ omB k K B d, τ y = z := by
  first | (exact @GlobalTheory.ComplementaryForms.complementary_eq_topForms) | (exact GlobalTheory.ComplementaryForms.complementary_eq_topForms) | (intros; apply GlobalTheory.ComplementaryForms.complementary_eq_topForms  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VolumeChartChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VolumeChartChange
set_option autoImplicit false

noncomputable section

open KaehlerDifferential GlobalTheory.CechDR

namespace GlobalTheory.PD

section Alt

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

theorem altMap_add_smul_self {n : ℕ} (f : M [⋀^Fin n]→ₗ[R] N) (v : Fin n → M) (k : Fin n) (c : Fin n → R)
    (hc : c k = 0) : f (fun j => v j + c j • v k) = f v := by
  classical
  have key : ∀ s : Finset (Fin n), f (fun j => v j + if j ∈ s then c j • v k else 0) = f v := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      by_cases hak : a = k
      · subst hak
        have e : (fun j => v j + if j ∈ insert a s then c j • v a else 0) =
            (fun j => v j + if j ∈ s then c j • v a else 0) := by
          funext j
          by_cases hj : j = a
          · subst hj; simp [hc]
          · simp [Finset.mem_insert, hj]
        rw [e, ih]
      · set g : Fin n → M := fun j => v j + if j ∈ s then c j • v k else 0 with hg
        have e1 : (fun j => v j + if j ∈ insert a s then c j • v k else 0) = Function.update g a (v a + c a • v k) := by
          funext j
          by_cases hj : j = a
          · subst hj; simp
          · simp [hg, Function.update_of_ne hj, Finset.mem_insert, hj]
        have e2 : Function.update g a (v a) = g := by
          funext j
          by_cases hj : j = a
          · subst hj; simp [hg, ha]
          · simp [Function.update_of_ne hj]
        have e3 : f (Function.update g a (v k)) = 0 := by
          refine f.map_eq_zero_of_eq _ (i := a) (j := k) ?_ hak
          simp [Function.update_of_ne (Ne.symm hak), hg, hc]
        rw [e1, f.map_update_add, f.map_update_smul, e2, ih, e3, smul_zero, add_zero]
  simpa using key Finset.univ

theorem exists_perm_succ {d : ℕ} (τ : Fin d → Fin (d + 1)) (hinj : Function.Injective τ) (hne : ∀ j, τ j ≠ 0) :
    ∃ π : Equiv.Perm (Fin d), τ = Fin.succ ∘ π := by
  let p : Fin d → Fin d := fun j => (τ j).pred (hne j)
  have hp : Function.Injective p := by
    intro a b hab
    apply hinj
    simpa [p] using congrArg Fin.succ hab
  refine ⟨Equiv.ofBijective p (Finite.injective_iff_bijective.1 hp), ?_⟩
  funext j
  simp [p]

theorem altMap_sub_succAbove {d : ℕ} (f : M [⋀^Fin d]→ₗ[R] N) (θ : Fin (d + 1) → M) (h0 : θ 0 = 0)
    (i : Fin (d + 1)) : ∃ ε : ℤˣ, f (fun j => θ (i.succAbove j) - θ i) = ε • f (fun j => θ j.succ) := by
  classical
  cases i using Fin.cases with
  | zero => exact ⟨1, by simp [h0]⟩
  | succ i' =>
    have hd : 0 < d := Nat.lt_of_le_of_lt (Nat.zero_le _) i'.isLt
    set i : Fin (d + 1) := i'.succ with hi
    set j0 : Fin d := ⟨0, hd⟩ with hj0
    have hσ0 : i.succAbove j0 = 0 := by
      rw [Fin.succAbove_of_castSucc_lt]
      · rfl
      · rw [Fin.lt_def]; simp [hi, hj0]
    set w : Fin d → M := fun j => θ (i.succAbove j) - θ i with hw
    set c : Fin d → R := fun j => if j = j0 then 0 else -1 with hc
    have k1 := altMap_add_smul_self f w j0 c (by simp [hc])
    have e1 : (fun j => w j + c j • w j0) = Function.update (θ ∘ i.succAbove) j0 ((-1 : R) • θ i) := by
      funext j
      by_cases hj : j = j0
      · subst hj; simp [hw, hc, hσ0, h0]
      · simp [hw, hc, hj, hσ0, h0, Function.update_of_ne hj]
    set τ : Fin d → Fin (d + 1) := Function.update i.succAbove j0 i with hτ
    have e2 : Function.update (θ ∘ i.succAbove) j0 (θ i) = θ ∘ τ := by
      funext j
      by_cases hj : j = j0
      · subst hj; simp [hτ]
      · simp [hτ, Function.update_of_ne hj]
    have hτinj : Function.Injective τ := by
      intro a b hab
      by_cases ha : a = j0 <;> by_cases hb : b = j0
      · rw [ha, hb]
      · simp [hτ, ha, Function.update_of_ne hb] at hab
      · simp [hτ, hb, Function.update_of_ne ha] at hab
      · simp only [hτ, Function.update_of_ne ha, Function.update_of_ne hb] at hab
        exact Fin.succAbove_right_injective hab
    have hτne : ∀ j, τ j ≠ 0 := by
      intro j
      by_cases hj : j = j0
      · subst hj; simp [hτ, hi]
      · rw [hτ, Function.update_of_ne hj, ← hσ0]
        exact fun h => hj (Fin.succAbove_right_injective h)
    obtain ⟨π, hπ⟩ := exists_perm_succ τ hτinj hτne
    refine ⟨-Equiv.Perm.sign π, ?_⟩
    rw [← k1, e1, f.map_update_smul, e2, hπ]
    have e3 : θ ∘ (Fin.succ ∘ ⇑π) = (fun j => θ j.succ) ∘ ⇑π := rfl
    rw [e3, f.map_perm, Units.neg_smul, neg_one_smul]

end Alt

theorem volume_chart_change (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F]
    [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F) (h : IsFinCover k K x)
    (i : Fin (d + 1)) : ∃ ε : ℤˣ, (ExteriorAlgebra.ιMulti K d fun j => D k K (algebraMap F K (x (i.succAbove j) / x i))) =
      ε • algebraMap F K (∏ j, x j / x i) • vol0 k K x := by
  have hx := h.pd.ne
  set y : Fin (d + 1) → K := fun a => algebraMap F K (x a / x 0) with hy
  have hy0 : ∀ a, y a ≠ 0 := fun a => (map_ne_zero _).2 (div_ne_zero (hx a) (hx 0))
  set θ : Fin (d + 1) → Ω[K⁄k] := fun a => (y a)⁻¹ • D k K (y a) with hθ
  have hθ0 : θ 0 = 0 := by
    show (algebraMap F K (x 0 / x 0))⁻¹ • D k K (algebraMap F K (x 0 / x 0)) = 0
    rw [div_self (hx 0), map_one, Derivation.map_one_eq_zero, smul_zero]
  have hD : ∀ a, D k K (algebraMap F K (x a / x i)) = algebraMap F K (x a / x i) • (θ a - θ i) := by
    intro a
    have e : algebraMap F K (x a / x i) = y a / y i := by
      simp only [hy, ← map_div₀]
      congr 1
      field_simp [hx 0, hx i]
    have ha := hy0 a
    have hi := hy0 i
    rw [e, Derivation.leibniz_div, hθ]
    simp only [smul_sub, smul_smul]
    congr 2 <;> field_simp
  obtain ⟨ε, hε⟩ := altMap_sub_succAbove (ExteriorAlgebra.ιMulti K d) θ hθ0 i
  refine ⟨ε, ?_⟩
  have hprod : algebraMap F K (∏ j, x j / x i) = ∏ j, algebraMap F K (x (i.succAbove j) / x i) := by
    rw [Fin.prod_univ_succAbove _ i, div_self (hx i), one_mul, map_prod]
  simp only [hD]
  rw [AlternatingMap.map_smul_univ, hε, hprod]
  rw [smul_comm]
  rfl

end GlobalTheory.PD
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VolumeChartChangeStatement
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sign_iMulti_D_chart_change : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ i : Fin (d + 1), ∃ ε : ℤˣ, (ExteriorAlgebra.ιMulti K d fun j => D k K (algebraMap F K (x (i.succAbove j) / x i))) = ε • algebraMap F K (∏ j, x j / x i) • vol0 k K x := by
  first | (exact @GlobalTheory.PD.volume_chart_change) | (exact GlobalTheory.PD.volume_chart_change) | (intros; apply GlobalTheory.PD.volume_chart_change <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplementaryModuleStandardOpensIff
set_option autoImplicit false

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.ComplStd

theorem mem_omA_iff {k F : Type} [Field k] [Field F] [Algebra k F] {d : ℕ} {x : Fin (d + 1) → F}
    (hx : ∀ i, x i ≠ 0) {I : Finset (Fin (d + 1))} {i : Fin (d + 1)} (hi : i ∈ I) (f : F) :
    f ∈ omA k x I ↔ (∏ j, x i / x j) * f ∈ rA k x I := by
  simp only [omA, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulLeft_apply, Subalgebra.mem_toSubmodule]
  refine ⟨fun h => h i hi, fun h i' _ => ?_⟩
  have hg : x i' / x i ∈ rA k x I := Algebra.subset_adjoin ⟨i, hi, i', rfl⟩
  have e : (∏ j, x i' / x j) = (x i' / x i) ^ (d + 1) * ∏ j, x i / x j := by
    rw [show (x i' / x i) ^ (d + 1) = ∏ _j : Fin (d + 1), x i' / x i by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin], ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j _ => (div_mul_div_cancel₀ (hx i)).symm
  rw [e, mul_assoc]
  exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hg _) h

theorem trace_algebraMap_mul {F K : Type} [Field F] [Field K] [Algebra F K] (c : F) (w : K) :
    Algebra.trace F K (algebraMap F K c * w) = c * Algebra.trace F K w := by
  rw [← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]

theorem single (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K]
    [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F) (hc : IsFinCover k K x)
    (τ : DR k K →ₗ[K] K) (hτ : IsTop k K x τ) (i : Fin (d + 1)) (z : K) :
    (∀ b ∈ rB k K x {i}, Algebra.trace F K (z * b) ∈ omA k x {i}) ↔ ∃ y ∈ omB k K (rB k K x {i}) d, τ y = z := by
  haveI := hc.fin
  have hx := hc.pd.ne
  obtain ⟨e, he⟩ := GlobalTheory.T.standardAffineOpen_ring_polynomialEquiv k F d x hc.pd i
  set u : Fin d → F := fun j => x (i.succAbove j) / x i with hu_def
  have hu : AlgebraicIndependent k u := by
    rw [algebraicIndependent_iff_injective_aeval]
    have : MvPolynomial.aeval u = (rA k x {i}).val.comp e.toAlgHom :=
      MvPolynomial.algHom_ext fun j => by simp [he, u]
    rw [this]
    exact Subtype.val_injective.comp e.injective
  have hA : rA k x {i} = Algebra.adjoin k (Set.range u) := by
    apply le_antisymm
    · apply Algebra.adjoin_le
      rintro y ⟨i', hi', j, rfl⟩
      rw [Finset.mem_singleton] at hi'
      subst hi'
      by_cases hj : j = i'
      · subst hj; rw [div_self (hx _)]; exact one_mem _
      · obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hj
        exact Algebra.subset_adjoin ⟨j', rfl⟩
    · apply Algebra.adjoin_le
      rintro y ⟨j, rfl⟩
      exact Algebra.subset_adjoin ⟨i, Finset.mem_singleton_self _, _, rfl⟩
  haveI : IsFractionRing (rA k x {i}) F := (GlobalTheory.T.standardOpenCoordinateRing_isFractionRing_isNoetherianRing k F d x hc.pd {i} (Finset.singleton_nonempty _)).1
  obtain ⟨ε, hε⟩ := GlobalTheory.T.exists_sign_iMulti_D_chart_change k F K d x hc i
  set P : F := ∏ j, x i / x j with hP
  set C : F := ∏ j, x j / x i with hC
  have hPC : algebraMap F K P * algebraMap F K C = 1 := by
    rw [← map_mul, hP, hC, ← Finset.prod_mul_distrib]
    rw [Finset.prod_eq_one fun j _ => by rw [div_mul_div_cancel₀ (hx j), div_self (hx i)], map_one]
  have hPne : algebraMap F K P ≠ 0 := left_ne_zero_of_mul_eq_one hPC
  let τ' : DR k K →ₗ[K] K := (((ε : ℤ) : K) * algebraMap F K P) • τ
  have hτ' : τ' (ExteriorAlgebra.ιMulti K d fun j => D k K (algebraMap F K (u j))) = 1 := by
    simp only [u]
    rw [hε]
    rw [LinearMap.smul_apply, Units.smul_def, map_zsmul, map_smul, hτ.1]
    simp only [smul_eq_mul, zsmul_eq_mul, mul_one]
    have hε2 : ((ε : ℤ) : K) * ((ε : ℤ) : K) = 1 := by
      rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
    linear_combination (algebraMap F K P * algebraMap F K C) * hε2 + hPC
  have key := GlobalTheory.T.complementaryModule_eq_topForms_of_finiteCover k F K d u hu (rA k x {i}) hA (rB k K x {i}) rfl (hc.smooth i) τ' hτ'
    (algebraMap F K P * z)
  have lhs : (∀ b ∈ rB k K x {i}, Algebra.trace F K (z * b) ∈ omA k x {i}) ↔
      ∀ b : rB k K x {i}, Algebra.trace F K (algebraMap F K P * z * b) ∈ rA k x {i} := by
    simp only [Subtype.forall, mem_omA_iff hx (Finset.mem_singleton_self i), mul_assoc, trace_algebraMap_mul]
    exact Iff.rfl
  have rhs : (∃ y ∈ omB k K (rB k K x {i}) d, τ' y = algebraMap F K P * z) ↔
      ∃ y ∈ omB k K (rB k K x {i}) d, τ y = z := by
    have h1 : ∀ y, τ' y = algebraMap F K P * z ↔ ((ε : ℤ) : K) * τ y = z := by
      intro y
      simp only [τ', LinearMap.smul_apply, smul_eq_mul]
      rw [show ((ε : ℤ) : K) * algebraMap F K P * τ y = algebraMap F K P * (((ε : ℤ) : K) * τ y) by ring,
        mul_right_inj' hPne]
    simp only [h1]
    rcases Int.units_eq_one_or ε with rfl | rfl
    · simp
    · constructor
      · rintro ⟨y, hy, h⟩; exact ⟨-y, neg_mem hy, by rw [map_neg]; simpa using h⟩
      · rintro ⟨y, hy, h⟩; exact ⟨-y, neg_mem hy, by rw [map_neg]; simp [h]⟩
  exact lhs.trans (key.trans rhs)

theorem unif (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K]
    [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F) (hc : IsFinCover k K x)
    (I : Finset (Fin (d + 1))) (i : Fin (d + 1)) (hi : i ∈ I) (z : K)
    (h : ∀ b ∈ rB k K x I, Algebra.trace F K (z * b) ∈ omA k x I) :
    ∃ N : ℕ, ∀ b ∈ rB k K x {i},
      Algebra.trace F K (z * algebraMap F K (∏ j ∈ I, x j / x i) ^ N * b) ∈ omA k x {i} := by
  have hx := hc.pd.ne
  set s : F := ∏ j ∈ I, x j / x i with hs
  set P : F := ∏ j, x i / x j with hP
  have hs1 : s ∈ rA k x {i} :=
    Subalgebra.prod_mem _ fun j _ => Algebra.subset_adjoin ⟨i, Finset.mem_singleton_self _, j, rfl⟩
  have hle : rB k K x {i} ≤ rB k K x I :=
    (GlobalTheory.T.finite_cover_ring_localization_chart k F K d x hc {i} i (Finset.mem_singleton_self _)).1 I (Finset.singleton_subset_iff.2 hi)
  haveI : Module.Finite (rA k x {i}) (integralClosure (rA k x {i}) K) :=
    (GlobalTheory.T.finite_cover_chart_smooth_normal k F K d x hc {i} (Finset.singleton_nonempty _)).1
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := rA k x {i}) (M := integralClosure (rA k x {i}) K)
  have hg : ∀ g : integralClosure (rA k x {i}) K, ∃ N : ℕ,
      P * Algebra.trace F K (z * g) * s ^ N ∈ rA k x {i} := by
    intro g
    have hgI : (g : K) ∈ rB k K x I := hle g.2
    exact (GlobalTheory.T.mem_standardOpenCoordinateRing_iff_localization_chart k F d x hc.pd I i hi _).1 ((mem_omA_iff hx hi _).1 (h _ hgI))
  choose Nf hNf using hg
  refine ⟨∑ g ∈ S, Nf g, fun b hb => ?_⟩
  rw [mem_omA_iff hx (Finset.mem_singleton_self i)]
  have hb' : (⟨b, hb⟩ : integralClosure (rA k x {i}) K) ∈ Submodule.span (rA k x {i}) (S : Set _) := by
    rw [hS]; trivial
  have key : ∀ w : integralClosure (rA k x {i}) K, w ∈ Submodule.span (rA k x {i}) (S : Set _) →
      P * Algebra.trace F K (z * algebraMap F K s ^ (∑ g ∈ S, Nf g) * w) ∈ rA k x {i} := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hg)
      have e : P * Algebra.trace F K (z * algebraMap F K s ^ (∑ g ∈ S, Nf g) * g) =
          s ^ m * (P * Algebra.trace F K (z * g) * s ^ Nf g) := by
        rw [hm, mul_comm z, ← map_pow, mul_assoc, trace_algebraMap_mul]; ring
      rw [e]
      exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hs1 _) (hNf g)
    | zero => simp
    | add a c _ _ ha hc =>
      have e : ((a + c : integralClosure (rA k x {i}) K) : K) = a + c := rfl
      rw [e, mul_add, map_add (f := _), mul_add]
      exact add_mem ha hc
    | smul r a _ ha =>
      set_option synthInstance.maxHeartbeats 200000 in
      have e : ((r • a : integralClosure (rA k x {i}) K) : K) = algebraMap F K (r : F) * a := by
        rw [SetLike.val_smul, Algebra.smul_def]; rfl
      have e2 : P * Algebra.trace F K (z * algebraMap F K s ^ (∑ g ∈ S, Nf g) * (algebraMap F K (r : F) * a)) =
          (r : F) * (P * Algebra.trace F K (z * algebraMap F K s ^ (∑ g ∈ S, Nf g) * a)) := by
        rw [show z * algebraMap F K s ^ (∑ g ∈ S, Nf g) * (algebraMap F K (r : F) * a) =
          algebraMap F K (r : F) * (z * algebraMap F K s ^ (∑ g ∈ S, Nf g) * a) by ring, trace_algebraMap_mul]
        ring
      rw [e, e2]
      exact Subalgebra.mul_mem _ r.2 ha
  exact key _ hb'

theorem complementary_iff : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ (τ : DR k K →ₗ[K] K), IsTop k K x τ → ∀ I : Finset (Fin (d + 1)), I.Nonempty → ∀ z : K, (∀ b ∈ rB k K x I, Algebra.trace F K (z * b) ∈ omA k x I) ↔ ∃ y ∈ omB k K (rB k K x I) d, τ y = z := by
  intro k _ _ F K _ _ _ _ _ _ d x hc τ hτ I hI z
  obtain ⟨i, hi⟩ := hI
  have hx := hc.pd.ne
  set s : F := ∏ j ∈ I, x j / x i with hs
  have hsne : algebraMap F K s ≠ 0 :=
    (map_ne_zero _).2 (Finset.prod_ne_zero_iff.2 fun j _ => div_ne_zero (hx j) (hx i))
  constructor
  · intro h
    obtain ⟨N, hN⟩ := unif k F K d x hc I i hi z h
    obtain ⟨y', hy', hτy'⟩ := (single k F K d x hc τ hτ i _).1 hN
    refine ⟨(algebraMap F K s ^ N)⁻¹ • y', (GlobalTheory.T.kahlerFormsOverSubalgebra_standardOpen_iff_pow_smul k F K d x hc I i hi d _).2 ⟨N, ?_⟩, ?_⟩
    · rw [smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hsne), one_smul]; exact hy'
    · rw [map_smul, hτy', smul_eq_mul]; field_simp; exact mul_comm _ _
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨N, hN⟩ := (GlobalTheory.T.kahlerFormsOverSubalgebra_standardOpen_iff_pow_smul k F K d x hc I i hi d y).1 hy
    have h1 := (single k F K d x hc τ hτ i _).2 ⟨_, hN, rfl⟩
    intro b hb
    obtain ⟨M, hM⟩ := ((GlobalTheory.T.finite_cover_ring_localization_chart k F K d x hc I i hi).2 b).1 hb
    have h2 := (mem_omA_iff hx (Finset.mem_singleton_self i) _).1 (h1 _ hM)
    rw [mem_omA_iff hx hi, GlobalTheory.T.mem_standardOpenCoordinateRing_iff_localization_chart k F d x hc.pd I i hi]
    refine ⟨N + M, ?_⟩
    convert h2 using 1
    rw [map_smul, smul_eq_mul, show algebraMap F K s ^ N * τ y * (b * algebraMap F K s ^ M) =
      algebraMap F K (s ^ (N + M)) * (τ y * b) by rw [map_pow, pow_add]; ring, trace_algebraMap_mul]
    ring

end GlobalTheory.ComplStd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplementaryModuleStandardOpensIffStatement
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complementaryModule_standardOpens_iff : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ (τ : DR k K →ₗ[K] K), IsTop k K x τ → ∀ I : Finset (Fin (d + 1)), I.Nonempty → ∀ z : K, (∀ b ∈ rB k K x I, Algebra.trace F K (z * b) ∈ omA k x I) ↔ ∃ y ∈ omB k K (rB k K x I) d, τ y = z := by
  first | (exact @GlobalTheory.ComplStd.complementary_iff) | (exact GlobalTheory.ComplStd.complementary_iff) | (intros; apply GlobalTheory.ComplStd.complementary_iff  <;> assumption)
end
