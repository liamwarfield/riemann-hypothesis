module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDecompositionGroupCyclotomicCharacterZpowN
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedSiegelUnitCoeffGaloisLevel
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicCoboundaryOfDivisible
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspExpansionAtInfinityProperties

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionTowerIntegrality
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionTowerIntegrality
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ.KmapA

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem val_eq_one_iff {K : Type} [Field K] (A : ValuationSubring K) {y : K} (hy : y ≠ 0) :
    A.valuation y = 1 ↔ y ∈ A ∧ y⁻¹ ∈ A := by
  constructor
  · intro h
    refine ⟨(A.valuation_le_one_iff y).1 h.le, (A.valuation_le_one_iff _).1 ?_⟩
    rw [map_inv₀, h, inv_one]
  · rintro ⟨h1, h2⟩
    have hu : IsUnit (⟨y, h1⟩ : A) :=
      isUnit_iff_exists_inv.2 ⟨⟨y⁻¹, h2⟩, Subtype.ext (by simp [hy])⟩
    exact (A.valuation_eq_one_iff _).1 hu

theorem un_map (X : Tower Ω ε) (φ : X.K ≃+* X.K)
    (hφ : ∀ W : ValuationSubring X.K, X.OverY W → X.OverY (W.comap φ.toRingHom)) (m : ℕ) (f : X.Kˣ)
    (hf : f ∈ X.Un m) : Units.map φ.toMonoidHom f ∈ X.Un m := by
  intro W hW
  obtain ⟨g, hg⟩ := hf _ (hφ W hW)
  refine ⟨Units.map φ.toMonoidHom g, ?_⟩
  have hx : ((f : X.K) / (g : X.K) ^ m) ≠ 0 := div_ne_zero f.ne_zero (pow_ne_zero _ g.ne_zero)
  rw [val_eq_one_iff _ hx] at hg
  have hx' : φ ((f : X.K) / (g : X.K) ^ m) ≠ 0 := (map_ne_zero φ).2 hx
  have e : ((Units.map φ.toMonoidHom f : X.Kˣ) : X.K) / ((Units.map φ.toMonoidHom g : X.Kˣ) : X.K) ^ m =
      φ ((f : X.K) / (g : X.K) ^ m) := by
    simp [map_div₀, map_pow]
  rw [e, val_eq_one_iff _ hx']
  refine ⟨ValuationSubring.mem_comap.1 hg.1, ?_⟩
  rw [← map_inv₀]
  exact ValuationSubring.mem_comap.1 hg.2

theorem eval_kmap (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (φ : X.K ≃+* X.K) (n : ℕ) (a : X.Khat l) (f : X.Kˣ)
    (he : AdicCompletion.eval (idl l) (X.Kl l) n a = X.cls l n f) :
    AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l φ a) = X.cls l n (Units.map φ.toMonoidHom f) := by
  rw [AdicCompletion.eval_apply] at he ⊢
  have h2 := AdicCompletion.map_val_apply (idl l) (LinearMap.baseChange ℤ_[l]
    (AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (Units.map φ.toMonoidHom)))) (n := n) a
  refine Eq.trans h2 ?_
  rw [he]
  rfl

theorem kmap_mem_A (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (φ : X.K ≃+* X.K)
    (hφ : ∀ W : ValuationSubring X.K, X.OverY W → X.OverY (W.comap φ.toRingHom)) :
    ∀ a ∈ X.A l, X.kmap l φ a ∈ X.A l := by
  have h : X.A l ≤ (X.A l).comap (X.kmap l φ) := by
    refine Submodule.span_le.2 (fun x hx => ?_)
    refine Submodule.subset_span (fun n => ?_)
    obtain ⟨f, hf, he⟩ := hx n
    exact ⟨_, un_map X φ hφ (l ^ n) f hf, eval_kmap X l φ n x f he⟩
  intro a ha
  exact h ha

end GlobalTheory.KZ.KmapA


open GlobalTheory.KZ.KmapA in
theorem GlobalTheory.KZ.kmap_A_stable : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
    ∀ (l : ℕ) [Fact l.Prime], (∀ (g : GQ), ∀ a ∈ X.A l, X.kmap l (X.sl g).toRingEquiv a ∈ X.A l) ∧
      ∀ (s : Ω ≃ₐ[ℚ] Ω), ∀ a ∈ X.A l, X.kmap l (X.gal s) a ∈ X.A l := by
  intro Ω _ _ _ ε X hinj hhol l _
  have hY := GlobalTheory.T.overAffineJLine_comap_sl_gal ε X hinj hhol
  exact ⟨fun g => kmap_mem_A X l _ (fun W hW => (hY W hW).1 g),
    fun s => kmap_mem_A X l _ (fun W hW => (hY W hW).2 s)⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionTowerIntegralityStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modular_function_tower_integrality : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (l : ℕ) [Fact l.Prime], (∀ (g : GQ), ∀ a ∈ X.A l, X.kmap l (X.sl g).toRingEquiv a ∈ X.A l) ∧ ∀ (s : Ω ≃ₐ[ℚ] Ω), ∀ a ∈ X.A l, X.kmap l (X.gal s) a ∈ X.A l := by
  first | exact @GlobalTheory.KZ.kmap_A_stable | exact GlobalTheory.KZ.kmap_A_stable | (intros; apply GlobalTheory.KZ.kmap_A_stable <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemModularFunctionRingOverIffHasSomeLevelOver
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemModularFunctionRingOverIffHasSomeLevelOver
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN.RingMem

theorem inR_const (E : Subring ℂ) (c : ℂ) (hc : c ∈ E) : InR E fun _ => c := by
  refine ⟨1, 0, one_pos, fun _ _ _ => rfl, fun γ => ?_⟩
  have h := GlobalTheory.QFam.QAllSubring.const (R := E) (N := 1) hc
  simpa only [pow_zero, one_mul] using h

theorem lv_lift {E : Subring ℂ} {f : ℍ → ℂ} {N w : ℕ} (N₂ : ℕ) (hN₂ : 0 < N₂) (w' : ℕ) (hw : w ≤ w')
    (hN : 0 < N) (h : Lv E N w f) : Lv E (N * N₂) w' f :=
  GlobalTheory.T.lv_mono_of_dvd_of_le E N (N * N₂) w w' f (Nat.mul_pos hN hN₂) (dvd_mul_right N N₂) hw h

theorem lv_lift' {E : Subring ℂ} {f : ℍ → ℂ} {N w : ℕ} (N₁ : ℕ) (hN₁ : 0 < N₁) (w' : ℕ) (hw : w ≤ w')
    (hN : 0 < N) (h : Lv E N w f) : Lv E (N₁ * N) w' f :=
  GlobalTheory.T.lv_mono_of_dvd_of_le E N (N₁ * N) w w' f (Nat.mul_pos hN₁ hN) (dvd_mul_left N N₁) hw h

theorem inR_add {E : Subring ℂ} {f g : ℍ → ℂ} (hf : InR E f) (hg : InR E g) : InR E (f + g) := by
  obtain ⟨N₁, w₁, hN₁, hf⟩ := hf
  obtain ⟨N₂, w₂, hN₂, hg⟩ := hg
  have hf' := lv_lift N₂ hN₂ (max w₁ w₂) (le_max_left _ _) hN₁ hf
  have hg' := lv_lift' N₁ hN₁ (max w₁ w₂) (le_max_right _ _) hN₂ hg
  refine ⟨N₁ * N₂, max w₁ w₂, Nat.mul_pos hN₁ hN₂, fun γ hγ τ => ?_, fun γ => ?_⟩
  · simp only [Pi.add_apply, hf'.1 γ hγ τ, hg'.1 γ hγ τ]
  · have h := GlobalTheory.QFam.QAllSubring.add (hf'.2 γ) (hg'.2 γ)
    refine (congrArg (QAll (· ∈ E) (N₁ * N₂)) (funext fun τ => ?_)).mp h
    simp only [Pi.add_apply]; ring

theorem inR_mul {E : Subring ℂ} {f g : ℍ → ℂ} (hf : InR E f) (hg : InR E g) : InR E (f * g) := by
  obtain ⟨N₁, w₁, hN₁, hf⟩ := hf
  obtain ⟨N₂, w₂, hN₂, hg⟩ := hg
  have hf' := lv_lift N₂ hN₂ w₁ le_rfl hN₁ hf
  have hg' := lv_lift' N₁ hN₁ w₂ le_rfl hN₂ hg
  refine ⟨N₁ * N₂, w₁ + w₂, Nat.mul_pos hN₁ hN₂, fun γ hγ τ => ?_, fun γ => ?_⟩
  · simp only [Pi.mul_apply, hf'.1 γ hγ τ, hg'.1 γ hγ τ]
  · have h := GlobalTheory.QFam.QAllSubring.mul (hf'.2 γ) (hg'.2 γ)
    refine (congrArg (QAll (· ∈ E) (N₁ * N₂)) (funext fun τ => ?_)).mp h
    simp only [Pi.mul_apply]; ring

theorem inR_neg {E : Subring ℂ} {f : ℍ → ℂ} (hf : InR E f) : InR E (-f) := by
  obtain ⟨N, w, hN, hf⟩ := hf
  refine ⟨N, w, hN, fun γ hγ τ => ?_, fun γ => ?_⟩
  · simp only [Pi.neg_apply, hf.1 γ hγ τ]
  · have h := GlobalTheory.QFam.QAllSubring.sub (GlobalTheory.QFam.QAllSubring.const (R := E) (N := N) E.zero_mem) (hf.2 γ)
    refine (congrArg (QAll (· ∈ E) N) (funext fun τ => ?_)).mp h
    simp only [Pi.neg_apply]; ring

def inRSubring (E : Subring ℂ) : Subring (ℍ → ℂ) where
  carrier := {f | InR E f}
  mul_mem' := inR_mul
  one_mem' := inR_const E 1 E.one_mem
  add_mem' := inR_add
  zero_mem' := inR_const E 0 E.zero_mem
  neg_mem' := inR_neg

end GlobalTheory.FN.RingMem

theorem GlobalTheory.FN.mem_ring_iff_inR :
    ∀ E : Subring ℂ, (∀ f : ℍ → ℂ, f ∈ GlobalTheory.FN.ring E ↔ InR E f) ∧ ∀ c ∈ E, InR E fun _ => c := by
  intro E
  refine ⟨fun f => ⟨fun h => ?_, mem_ring_of_inR⟩, fun c hc => GlobalTheory.FN.RingMem.inR_const E c hc⟩
  have hle : GlobalTheory.FN.ring E ≤ GlobalTheory.FN.RingMem.inRSubring E :=
    (Subring.closure_le).mpr fun g hg => hg
  exact hle h
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemModularFunctionRingOverIffHasSomeLevelOverStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver : ∀ E : Subring ℂ, (∀ f : ℍ → ℂ, f ∈ GlobalTheory.FN.ring E ↔ InR E f) ∧ ∀ c ∈ E, InR E fun _ => c := by
  first | exact @GlobalTheory.FN.mem_ring_iff_inR | exact GlobalTheory.FN.mem_ring_iff_inR | (intros; apply GlobalTheory.FN.mem_ring_iff_inR <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisActionSiegelUnitInTower
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedSiegelUnitCoeffGaloisLevelStatement
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothedSiegelUnit_coeff_galois_level : ∀ (c M a b d : ℕ) (σ : ℂ ≃+* ℂ), 0 < M → a < M → σ (ee (1 / (M : ℂ))) = ee ((d : ℂ) / M) → GlobalTheory.Sieg.admitted c ![(a : ℚ) / M, (b : ℚ) / M] → GlobalTheory.Sieg.admitted c ![(a : ℚ) / M, ((d * b : ℕ) : ℚ) / M] → ∃ (k : ℤ) (A : ℕ → ℂ), HasQ M (fun τ => sg c ![(a : ℚ) / M, (b : ℚ) / M] τ * ee (-((k : ℂ) / M) * (τ : ℂ))) A ∧ HasQ M (fun τ => sg c ![(a : ℚ) / M, ((d * b : ℕ) : ℚ) / M] τ * ee (-((k : ℂ) / M) * (τ : ℂ))) (fun n => σ (A n)) := by
  first | exact @GlobalTheory.Sieg.sg_coeff_galois_int | exact GlobalTheory.Sieg.sg_coeff_galois_int | (intros; apply GlobalTheory.Sieg.sg_coeff_galois_int <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisActionSiegelUnitInTower
noncomputable section

open scoped UpperHalfPlane MatrixGroups
open GlobalTheory.KZ GlobalTheory.Sieg GlobalTheory.QFam Cardinal

namespace GlobalTheory.KZ.GalUnits

theorem exists_equiv_comp {R K L : Type} [Field R] [Field K] [Field L] [IsAlgClosed K]
    [IsAlgClosed L] (f : R →+* K) (g : R →+* L) (hR : #R ≤ ℵ₀) (hK : ℵ₀ < #K) (hKL : #K = #L) :
    ∃ σ : K ≃+* L, ∀ r : R, σ (f r) = g r := by
  let : Algebra R K := f.toAlgebra
  let : Algebra R L := g.toAlgebra
  obtain ⟨ι, v, hv⟩ := exists_isTranscendenceBasis' R K
  obtain ⟨κ, w, hw⟩ := exists_isTranscendenceBasis' R L
  have h1 : #K = #ι := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' v hv hR hK
  have h2 : #L = #κ :=
    IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' w hw hR (hKL ▸ hK)
  obtain ⟨e⟩ := Cardinal.eq.1 (h1.symm.trans (hKL.trans h2))
  let := IsAlgClosed.isAlgClosure_of_transcendence_basis v hv
  let := IsAlgClosed.isAlgClosure_of_transcendence_basis w hw
  let e' : Algebra.adjoin R (Set.range v) ≃ₐ[R] Algebra.adjoin R (Set.range w) :=
    (hv.1.aevalEquiv.symm.trans (MvPolynomial.renameEquiv R e)).trans hw.1.aevalEquiv
  refine ⟨IsAlgClosure.equivOfEquiv K L e'.toRingEquiv, fun r => ?_⟩
  have hf : f r = algebraMap R K r := rfl
  have hg : g r = algebraMap R L r := rfl
  rw [hf, hg, IsScalarTower.algebraMap_apply R (Algebra.adjoin R (Set.range v)) K,
    IsAlgClosure.equivOfEquiv_algebraMap]
  have : e'.toRingEquiv (algebraMap R _ r) = algebraMap R _ r := e'.commutes r
  rw [this, ← IsScalarTower.algebraMap_apply]

theorem exists_ext {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (s : Ω ≃ₐ[ℚ] Ω) :
    ∃ σ : ℂ ≃+* ℂ, ∀ x : Ω, σ (ε x) = ε (s x) := by
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  have hR : #Ω ≤ ℵ₀ :=
    (Algebra.IsAlgebraic.cardinalMk_le_max ℚ Ω).trans (max_le Cardinal.mk_le_aleph0 le_rfl)
  exact exists_equiv_comp ε (ε.comp (s : Ω →+* Ω)) hR
    (by simp [Cardinal.mk_complex, Cardinal.aleph0_lt_continuum]) rfl

theorem mem_range_of_pow_eq_one {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharZero Ω] (ε : Ω →+* ℂ) {n : ℕ}
    (hn : 0 < n) {w : ℂ} (hw : w ^ n = 1) : ∃ y, ε y = w := by
  have : NeZero (n : Ω) := ⟨Nat.cast_ne_zero.2 hn.ne'⟩
  have : NeZero n := ⟨hn.ne'⟩
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic n Ω)
    (ne_of_gt (Polynomial.degree_cyclotomic_pos n Ω hn))
  have hz' : IsPrimitiveRoot z n := Polynomial.isRoot_cyclotomic_iff.1 hz
  have he : IsPrimitiveRoot (ε z) n := hz'.map_of_injective ε.injective
  obtain ⟨i, -, hi⟩ := he.eq_pow_of_pow_eq_one hw
  exact ⟨z ^ i, by rw [map_pow, hi]⟩

theorem eps_eOm {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (x : ℚ) :
    ε (eOm ε x) = ee (x : ℂ) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hw : Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ^ x.den = 1 := by
    rw [← Complex.exp_nat_mul]
    have : (x.den : ℂ) * (2 * Real.pi * Complex.I * (x : ℂ)) = x.num * (2 * Real.pi * Complex.I) := by
      have hd : (x.den : ℂ) ≠ 0 := by exact_mod_cast x.den_ne_zero
      have : (x : ℂ) = (x.num : ℂ) / x.den := by exact_mod_cast (Rat.num_div_den x).symm
      rw [this]; field_simp
    rw [this, Complex.exp_int_mul_two_pi_mul_I]
  have hex := mem_range_of_pow_eq_one ε x.den_pos hw
  unfold eOm ee
  exact Function.invFun_eq hex


open Classical in
def lc {R : Type} [Zero R] (M : ℕ) (k : ℤ) (A : ℕ → R) (r : ℚ) : R :=
  if h : ∃ n : ℕ, r = ((k : ℚ) + n) / M then A h.choose else 0

theorem lc_eq {R : Type} [Zero R] {M : ℕ} (hM : 0 < M) (k : ℤ) (A : ℕ → R) (n : ℕ) :
    lc M k A (((k : ℚ) + n) / M) = A n := by
  have h : ∃ m : ℕ, ((k : ℚ) + n) / M = ((k : ℚ) + m) / M := ⟨n, rfl⟩
  unfold lc
  rw [dite_eq_left h]
  have hM' : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have := h.choose_spec
  rw [div_left_inj' hM', add_right_inj] at this
  have : h.choose = n := by exact_mod_cast this.symm
  rw [this]

theorem lc_zero {R : Type} [Zero R] {M : ℕ} {k : ℤ} (A : ℕ → R) {r : ℚ} (h : ∀ n : ℕ, r ≠ ((k : ℚ) + n) / M) :
    lc M k A r = 0 := by
  unfold lc
  rw [dite_eq_right]
  push_neg
  exact h

theorem lc_map {R S : Type} [Zero R] [Zero S] (M : ℕ) (k : ℤ) (A : ℕ → R) (g : R → S) (hg : g 0 = 0) (r : ℚ) :
    lc M k (fun n => g (A n)) r = g (lc M k A r) := by
  unfold lc
  split_ifs <;> simp [hg]

theorem eq_lc {R : Type} [Zero R] {M : ℕ} (hM : 0 < M) {k : ℤ} {A : ℕ → R} {F : ℚ → R}
    (h1 : ∀ n : ℕ, F (((k : ℚ) + n) / M) = A n) (h2 : ∀ r : ℚ, (∀ n : ℕ, r ≠ ((k : ℚ) + n) / M) → F r = 0) :
    ∀ r, F r = lc M k A r := by
  intro r
  by_cases h : ∃ n : ℕ, r = ((k : ℚ) + n) / M
  · obtain ⟨n, rfl⟩ := h
    rw [h1, lc_eq hM]
  · push_neg at h
    rw [h2 r h, lc_zero A h]

theorem lc_unique {M : ℕ} (hM : 0 < M) {f : ℍ → ℂ} {k k' : ℤ} {A A' : ℕ → ℂ}
    (h : HasQ M (fun τ => f τ * ee (-((k : ℂ) / M) * (τ : ℂ))) A)
    (h' : HasQ M (fun τ => f τ * ee (-((k' : ℂ) / M) * (τ : ℂ))) A') : lc M k A = lc M k' A' := by
  wlog hk : k ≤ k' generalizing k k' A A'
  · exact (this h' h (le_of_not_ge hk)).symm
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, k' = k + m := ⟨(k' - k).toNat, by omega⟩
  have hs : HasQ M (fun τ => f τ * ee (-((k : ℂ) / M) * (τ : ℂ))) (fun n => if m ≤ n then A' (n - m) else 0) := by
    rw [hasQ_iff] at h' ⊢
    intro τ
    set Q := Complex.exp (2 * Real.pi * Complex.I * τ / M) with hQ
    have h2 := (h' τ).mul_right (Q ^ m)
    have e : f τ * ee (-(((k + m : ℤ) : ℂ) / M) * (τ : ℂ)) * Q ^ m = f τ * ee (-((k : ℂ) / M) * (τ : ℂ)) := by
      rw [mul_assoc]; congr 1
      unfold ee
      rw [hQ, ← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1; push_cast; ring
    rw [e] at h2
    refine (Function.Injective.hasSum_iff (f := fun n => (if m ≤ n then A' (n - m) else 0) * Q ^ n)
      (add_left_injective m) ?_).mp ?_
    · intro x hx
      have : ¬ m ≤ x := by
        intro hmx; exact hx ⟨x - m, by simp only; omega⟩
      simp [this]
    · rw [← hQ] at h2
      have e2 : (fun n => (if m ≤ n then A' (n - m) else 0) * Q ^ n) ∘ (· + m) = fun i => A' i * Q ^ i * Q ^ m := by
        funext n
        simp only [Function.comp, le_add_iff_nonneg_left, zero_le, if_true, Nat.add_sub_cancel, pow_add]
        ring
      rw [e2]; exact h2
  have hA := HasQ.coeff_unique hM h hs
  subst hA
  have hM' : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  funext r
  by_cases hr : ∃ n : ℕ, r = ((k : ℚ) + n) / M
  · obtain ⟨n, rfl⟩ := hr
    rw [lc_eq hM]
    by_cases hmn : m ≤ n
    · rw [if_pos hmn]
      have : ((k : ℚ) + n) / M = (((k + m : ℤ) : ℚ) + ((n - m : ℕ) : ℚ)) / M := by
        push_cast [Nat.cast_sub hmn]; ring
      rw [this, lc_eq hM]
    · rw [if_neg hmn, lc_zero]
      intro n' hn'
      rw [div_left_inj' hM'] at hn'
      push_cast at hn'
      have : (n : ℚ) = m + n' := by linarith
      have : n = m + n' := by exact_mod_cast this
      omega
  · push_neg at hr
    rw [lc_zero _ hr, lc_zero]
    intro n' hn'
    apply hr (m + n')
    rw [hn']; push_cast; ring

end GlobalTheory.KZ.GalUnits

namespace GlobalTheory.KZ

open GalUnits

theorem gal_siegel : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Tower Ω ε) (c : ℕ) (M a b d : ℕ) (s : Ω ≃ₐ[ℚ] Ω), 0 < M → a < M → s (eOm ε (1 / M)) = eOm ε (d / M) → GlobalTheory.Sieg.admitted c ![(a : ℚ) / M, (b : ℚ) / M] → GlobalTheory.Sieg.admitted c ![(a : ℚ) / M, ((d * b : ℕ) : ℚ) / M] → T.gal s (siegel T c ![(a : ℚ) / M, (b : ℚ) / M]) = siegel T c ![(a : ℚ) / M, ((d * b : ℕ) : ℚ) / M] := by
  intro Ω _ _ _ ε T c M a b d s hM ha hs h1 h2
  obtain ⟨σ, hσ⟩ := exists_ext ε s
  have hσM : σ (ee (1 / (M : ℂ))) = ee ((d : ℂ) / M) := by
    have e1 := eps_eOm ε (1 / M)
    have e2 := eps_eOm ε (d / M)
    push_cast at e1 e2
    rw [← e1, hσ, hs, e2]
  obtain ⟨k0, B, hB, hB'⟩ := GlobalTheory.T.smoothedSiegelUnit_coeff_galois_level c M a b d σ hM ha hσM h1 h2
  obtain ⟨k1, A1, hA1, c1, z1⟩ := GlobalTheory.T.siegel_unit_q_expansion_coefficients Ω ε T c M a b hM ha h1
  obtain ⟨k2, A2, hA2, c2, z2⟩ := GlobalTheory.T.siegel_unit_q_expansion_coefficients Ω ε T c M a (d * b) hM ha h2
  have L1 := eq_lc hM c1 z1
  have L2 := eq_lc hM c2 z2
  have U1 := lc_unique hM hA1 hB
  have U2 := lc_unique hM hB' hA2
  apply T.exp.toRingHom.injective
  ext r
  apply ε.injective
  show ε ((T.exp (T.gal s _)).coeff r) = ε ((T.exp _).coeff r)
  rw [T.gal_exp, ← hσ, L1, L2, ← lc_map M k1 A1 ε (map_zero ε), U1, ← lc_map M k0 B σ (map_zero σ), U2,
    lc_map M k2 A2 ε (map_zero ε)]

end GlobalTheory.KZ
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisActionSiegelUnitInTowerStatement
open scoped UpperHalfPlane MatrixGroups
open GlobalTheory.KZ GlobalTheory.Sieg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_action_siegelUnitInTower : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Tower Ω ε) (c : ℕ) (M a b d : ℕ) (s : Ω ≃ₐ[ℚ] Ω), 0 < M → a < M → s (eOm ε (1 / M)) = eOm ε (d / M) → GlobalTheory.Sieg.admitted c ![(a : ℚ) / M, (b : ℚ) / M] → GlobalTheory.Sieg.admitted c ![(a : ℚ) / M, ((d * b : ℕ) : ℚ) / M] → T.gal s (siegel T c ![(a : ℚ) / M, (b : ℚ) / M]) = siegel T c ![(a : ℚ) / M, ((d * b : ℕ) : ℚ) / M] := by
  first | exact @GlobalTheory.KZ.gal_siegel | exact GlobalTheory.KZ.gal_siegel | (intros; apply GlobalTheory.KZ.gal_siegel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLogDerivQExpansionModPrimePowUnique
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLogDerivQExpansionModPrimePowUnique
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.Glue.DlUniq

variable {Ω : Type} [Field Ω]

theorem cg_mul (A : ValuationSubring Ω) (l n : ℕ) (D G : HahnSeries ℚ Ω)
    (hD : ∀ r, CgA A l n (D.coeff r) 0) (hG : ∀ r, G.coeff r ∈ A) : ∀ r, CgA A l n ((D * G).coeff r) 0 := by
  intro r
  have h : ∀ i, ∃ z ∈ A, D.coeff i = (l : Ω) ^ n * z := fun i => by
    obtain ⟨z, hz, e⟩ := hD i; exact ⟨z, hz, by simpa using e⟩
  choose z hzA hz using h
  refine ⟨∑ ij ∈ Finset.addAntidiagonal D.isPWO_support G.isPWO_support r, z ij.1 * G.coeff ij.2, ?_, ?_⟩
  · exact Subring.sum_mem A.toSubring (fun ij _ => mul_mem (hzA _) (hG _))
  · rw [HahnSeries.coeff_mul, sub_zero, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun ij _ => ?_)
    rw [hz, mul_assoc]

theorem cg_sub (A : ValuationSubring Ω) (l n : ℕ) (D E : HahnSeries ℚ Ω)
    (hD : ∀ r, CgA A l n (D.coeff r) 0) (hE : ∀ r, CgA A l n (E.coeff r) 0) : ∀ r, CgA A l n ((D - E).coeff r) 0 := by
  intro r
  obtain ⟨z, hz, e⟩ := hD r
  obtain ⟨w, hw, e'⟩ := hE r
  refine ⟨z - w, A.sub_mem hz hw, ?_⟩
  rw [HahnSeries.coeff_sub, sub_zero, mul_sub, ← e, ← e', sub_zero, sub_zero]

theorem cg_of (A : ValuationSubring Ω) (l n : ℕ) (D E : HahnSeries ℚ Ω)
    (h : ∀ r, CgA A l n (D.coeff r) (E.coeff r)) : ∀ r, CgA A l n ((D - E).coeff r) 0 := by
  intro r
  obtain ⟨z, hz, e⟩ := h r
  exact ⟨z, hz, by rw [HahnSeries.coeff_sub, sub_zero, e]⟩

theorem key (θ : HahnSeries ℚ Ω → HahnSeries ℚ Ω)
    (hL : ∀ P Q, θ (P * Q) = θ P * Q + P * θ Q) (hC : ∀ c : Ω, θ (HahnSeries.C c) = 0)
    (k k2 : Ω) (hk : k ≠ 0) (a b a2 b2 : HahnSeries ℚ Ω)
    (h : HahnSeries.C k * a * b2 = HahnSeries.C k2 * a2 * b) :
    (θ a * b - a * θ b) * (a2 * b2) = (θ a2 * b2 - a2 * θ b2) * (a * b) := by
  have e1 : θ (HahnSeries.C k * a * b2) = HahnSeries.C k * (θ a * b2 + a * θ b2) := by
    rw [mul_assoc, hL, hC, hL]; ring
  have e2 : θ (HahnSeries.C k * a * b2) = HahnSeries.C k2 * (θ a2 * b + a2 * θ b) := by
    rw [h, mul_assoc, hL, hC, hL]; ring
  have h0 : HahnSeries.C k * ((θ a * b - a * θ b) * (a2 * b2) - (θ a2 * b2 - a2 * θ b2) * (a * b)) = 0 := by
    linear_combination (-(a2 * b)) * e1 + (a2 * b) * e2 - (θ a2 * b + a2 * θ b) * h
  rcases mul_eq_zero.mp h0 with h1 | h1
  · exact absurd h1 (HahnSeries.C_ne_zero hk)
  · exact sub_eq_zero.mp h1

end GlobalTheory.Glue.DlUniq

namespace GlobalTheory.Glue.DlUniq

theorem T_pow_mem_Gamma (M : ℕ) : (ModularGroup.T ^ M : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma M := by
  rw [CongruenceSubgroup.Gamma_mem]
  have h := ModularGroup.coe_T_zpow (M : ℤ)
  rw [zpow_natCast] at h
  simp [h]

theorem mem_KT {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (f : X.K) :
    ∃ M : ℕ, 0 < M ∧ f ∈ KT X M := by
  obtain ⟨M, hM, h⟩ := X.level f
  exact ⟨M, hM, h _ (T_pow_mem_Gamma M)⟩

end GlobalTheory.Glue.DlUniq

namespace GlobalTheory.Glue


open GlobalTheory.Glue.DlUniq in
theorem isDl_unique : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  ∀ (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), ((l : ℕ) : Ω) ∈ A.nonunits → ∀ (n : ℕ) (s : ℚ) (f : X.K) (φ φ' : HahnSeries ℚ Ω), IsDl X A l n s f φ → IsDl X A l n s f φ' → ∀ r, CgA A l n (φ.coeff r) (φ'.coeff r) := by
  intro Ω _ _ _ ε X _ l _ A hl n s f φ φ' h1 h2
  obtain ⟨hφA, a, b, κ, hκ, hab, hPa, hPb, hφ⟩ := h1
  obtain ⟨hφ'A, a2, b2, κ2, hκ2, hab2, hPa2, hPb2, hφ'⟩ := h2
  have hth := fun P Q => (GlobalTheory.T.thetaDerivationHahnSeries_leibniz_add_const (Ω := Ω) s P Q)

  have hK : algebraMap Ω X.K κ * a * b2 = algebraMap Ω X.K κ2 * a2 * b := by
    rw [← hab, ← hab2]; ring
  have hE : HahnSeries.C κ * X.exp a * X.exp b2 = HahnSeries.C κ2 * X.exp a2 * X.exp b := by
    have := congrArg X.exp hK
    simp only [map_mul, AlgHom.commutes] at this
    have ec : ∀ c : Ω, algebraMap Ω (HahnSeries ℚ Ω) c = HahnSeries.C c := fun c => by
      rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply]; simp [HahnSeries.ofPowerSeries_C]
    rwa [ec, ec] at this
  have hkey := key (theta s) (fun P Q => (hth P Q).1) (fun c => (hth 0 0).2.2 c) κ κ2 hκ _ _ _ _ hE

  set P := X.exp a * X.exp b * (X.exp a2 * X.exp b2) with hP
  have hPab := GlobalTheory.T.mul_of_isPrimitiveIntegral_hahn_gauss A _ _ hPa hPb
  have hPab2 := GlobalTheory.T.mul_of_isPrimitiveIntegral_hahn_gauss A _ _ hPa2 hPb2
  have hPP : Prim A P := GlobalTheory.T.mul_of_isPrimitiveIntegral_hahn_gauss A _ _ hPab hPab2
  obtain ⟨M, hM, hMK⟩ := mem_KT X (a * b * (a2 * b2))
  have hsupp := (GlobalTheory.T.mem_translationInvariantSubfield_iff_exponents ε X M hM _).mp hMK
  have hsuppP : ∀ r : ℚ, P.coeff r ≠ 0 → (r * M).den = 1 := by
    simpa [hP, map_mul] using hsupp
  have hD1 := cg_mul A l n _ _ (cg_of A l n _ _ hφ) hPab2.1
  have hD2 := cg_mul A l n _ _ (cg_of A l n _ _ hφ') hPab.1
  have hdiff := cg_sub A l n _ _ hD1 hD2
  have hid : (φ * X.exp a * X.exp b - (theta s (X.exp a) * X.exp b - X.exp a * theta s (X.exp b))) * (X.exp a2 * X.exp b2) -
      (φ' * X.exp a2 * X.exp b2 - (theta s (X.exp a2) * X.exp b2 - X.exp a2 * theta s (X.exp b2))) * (X.exp a * X.exp b)
      = (φ - φ') * P := by
    rw [hP]; linear_combination (-1 : HahnSeries ℚ Ω) * hkey
  rw [hid] at hdiff
  have hint : ∀ r, (φ - φ').coeff r ∈ A := fun r => by
    rw [HahnSeries.coeff_sub]; exact sub_mem (hφA r) (hφ'A r)
  have hfin := GlobalTheory.T.primitiveHahnSeries_not_zeroDivisor_modPrimePow l A hl n M P (φ - φ') hM hPP hsuppP hint hdiff
  intro r
  obtain ⟨z, hz, e⟩ := hfin r
  exact ⟨z, hz, by rw [← e, HahnSeries.coeff_sub, sub_zero]⟩

end GlobalTheory.Glue
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLogDerivQExpansionModPrimePowUniqueStatement
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLogDerivQExpansionModPrimePow_unique : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  ∀ (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), ((l : ℕ) : Ω) ∈ A.nonunits → ∀ (n : ℕ) (s : ℚ) (f : X.K) (φ φ' : HahnSeries ℚ Ω), IsDl X A l n s f φ → IsDl X A l n s f φ' → ∀ r, CgA A l n (φ.coeff r) (φ'.coeff r) := by
  first | exact @GlobalTheory.Glue.isDl_unique | exact GlobalTheory.Glue.isDl_unique | (intros; apply GlobalTheory.Glue.isDl_unique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionTowerUnitGroupStableSlashGalois
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionTowerUnitGroupStableSlashGalois
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

noncomputable section

namespace GlobalTheory.KZ

theorem vs_valuation_eq_one_iff {K : Type} [Field K] (V : ValuationSubring K) {x : K} (hx : x ≠ 0) :
    V.valuation x = 1 ↔ x ∈ V ∧ x⁻¹ ∈ V := by
  rw [← V.valuation_le_one_iff, ← V.valuation_le_one_iff, map_inv₀]
  have h0 : V.valuation x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  constructor
  · intro h; simp [h]
  · rintro ⟨h1, h2⟩
    refine le_antisymm h1 ?_
    by_contra hlt
    push_neg at hlt
    have := one_lt_inv₀ (pos_iff_ne_zero.2 h0) |>.2 hlt
    exact absurd h2 (not_le.2 this)

theorem vs_comap_valuation_eq_one_iff {K : Type} [Field K] (φ : K →+* K) (V : ValuationSubring K) {x : K}
    (hx : x ≠ 0) : (V.comap φ).valuation x = 1 ↔ V.valuation (φ x) = 1 := by
  rw [vs_valuation_eq_one_iff _ hx, vs_valuation_eq_one_iff _ ((map_ne_zero φ).2 hx),
    ValuationSubring.mem_comap, ValuationSubring.mem_comap, map_inv₀]

theorem Tower.Un_map {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (φ : X.K →+* X.K)
    (hφ : ∀ W : ValuationSubring X.K, X.OverY W → X.OverY (W.comap φ)) (m : ℕ) {f : X.Kˣ} (hf : f ∈ X.Un m)
    (u : X.Kˣ) (hu : (u : X.K) = φ (f : X.K)) : u ∈ X.Un m := by
  intro W hW
  obtain ⟨a, ha⟩ := hf _ (hφ W hW)
  refine ⟨Units.map φ.toMonoidHom a, ?_⟩
  have hne : (f : X.K) / (a : X.K) ^ m ≠ 0 := div_ne_zero f.ne_zero (pow_ne_zero _ a.ne_zero)
  rw [vs_comap_valuation_eq_one_iff φ W hne, map_div₀, map_pow] at ha
  rw [hu]
  exact ha

theorem Tower.Un_sl_gal : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
    ∀ (m : ℕ) (f : X.Kˣ), f ∈ X.Un m →
      (∀ (g : GQ) (u : X.Kˣ), (u : X.K) = X.sl g (f : X.K) → u ∈ X.Un m) ∧
        ∀ (s : Ω ≃ₐ[ℚ] Ω) (u : X.Kˣ), (u : X.K) = X.gal s (f : X.K) → u ∈ X.Un m := by
  intro Ω _ _ _ ε X hε hj m f hf
  refine ⟨fun g u hu => ?_, fun s u hu => ?_⟩
  · exact X.Un_map (X.sl g).toRingEquiv.toRingHom
      (fun W hW => (Tower.overY_comap_sl_gal ε X hε hj W hW).1 g) m hf u hu
  · exact X.Un_map (X.gal s).toRingHom
      (fun W hW => (Tower.overY_comap_sl_gal ε X hε hj W hW).2 s) m hf u hu

end GlobalTheory.KZ
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionTowerUnitGroupStableSlashGaloisStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modularFunctionTower_unitGroup_stable_slash_galois : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (m : ℕ) (f : X.Kˣ), f ∈ X.Un m → (∀ (g : GQ) (u : X.Kˣ), (u : X.K) = X.sl g (f : X.K) → u ∈ X.Un m) ∧ ∀ (s : Ω ≃ₐ[ℚ] Ω) (u : X.Kˣ), (u : X.K) = X.gal s (f : X.K) → u ∈ X.Un m := by
  first | exact @GlobalTheory.KZ.Tower.Un_sl_gal | exact GlobalTheory.KZ.Tower.Un_sl_gal | (intros; apply GlobalTheory.KZ.Tower.Un_sl_gal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspExpansionCoeffConjOfQExpansionConj
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspExpansionCoeffConjOfQExpansionConj
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem exp_conj : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (s : Ω →+* Ω) (g : ℂ ≃+* ℂ) (N w : ℕ) (f f' : ℍ → ℂ)
    (h h' : HahnSeries ℚ Ω), (∀ x, g (ε x) = ε (s x)) → 0 < N →
    QAll (· ∈ ε.range) N (fun τ => DD τ ^ w * f τ) →
    QConj g N (fun τ => DD τ ^ w * f τ) (fun τ => DD τ ^ w * f' τ) →
    IsExp ε f h → IsExp ε f' h' → ∀ r, h'.coeff r = s (h.coeff r) := by
  intro Ω _ ε s g N w f f' h h' hg hN hA hC hf hf' r
  obtain ⟨a, ha, haE⟩ := hA
  obtain ⟨c, hc, hc'⟩ := hC
  have hac : a = c := HasQ.coeff_unique hN ha hc
  subst hac
  choose b hb using fun n => RingHom.mem_range.mp (haE n)
  have ha' : HasQ N (fun τ => DD τ ^ w * f τ) (fun n => ε (b n)) := by
    have e : (fun n => ε (b n)) = a := funext hb
    rw [e]; exact ha
  have hc2 : HasQ N (fun τ => DD τ ^ w * f' τ) (fun n => ε (s (b n))) := by
    have e : (fun n => ε (s (b n))) = fun n => g (a n) := funext fun n => by rw [← hg, hb]
    rw [e]; exact hc'
  obtain ⟨H, hH, hHk, hH0⟩ := GlobalTheory.T.exists_hahnSeries_isExp_of_hasQ Ω ε N _ b hN ha'
  obtain ⟨H', hH', hHk', hH0'⟩ := GlobalTheory.T.exists_hahnSeries_isExp_of_hasQ Ω ε N _ (fun n => s (b n)) hN hc2
  obtain ⟨hD, hDe, hD0, -, hDZ⟩ := GlobalTheory.T.exists_cuspExpansion_discriminant_integer_leading_one Ω ε
  obtain ⟨hops, huniq, -, -, -⟩ := GlobalTheory.T.isCuspExpansionAtInfinity_properties Ω ε
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.exists_hahnSeries_scale_twist_ringHom Ω Ω s 1 (fun _ => 1) one_pos rfl (fun _ _ => (one_mul 1).symm)
  have hΦc : ∀ x r, (Φ x).coeff r = s (x.coeff r) := fun x r => by simpa using hΦ x r
  have hpow : ∀ (u : ℍ → ℂ) (k : HahnSeries ℚ Ω), IsExp ε u k → ∀ m : ℕ,
      IsExp ε (fun τ => DD τ ^ m * u τ) (hD ^ m * k) := by
    intro u k hu m
    induction m with
    | zero => simpa using hu
    | succ m ih =>
      have hm := (hops _ _ _ _ hDe ih).2.2
      have e1 : (fun τ => DD τ ^ (m + 1) * u τ) = DD * fun τ => DD τ ^ m * u τ := by
        funext τ; simp only [Pi.mul_apply, pow_succ]; ring
      have e2 : hD ^ (m + 1) * k = hD * (hD ^ m * k) := by ring
      rw [e1, e2]; exact hm
  have e1 : hD ^ w * h = H := huniq _ _ _ (hpow f h hf w) hH
  have e2 : hD ^ w * h' = H' := huniq _ _ _ (hpow f' h' hf' w) hH'
  have hΦD : Φ hD = hD := by
    ext r; rw [hΦc]; obtain ⟨n, hn⟩ := hDZ r; rw [hn, map_intCast]
  have hΦH : Φ H = H' := by
    ext r; rw [hΦc]
    by_cases hr : ∃ k : ℕ, r = (k : ℚ) / N
    · obtain ⟨k, rfl⟩ := hr; rw [hHk, hHk']
    · push_neg at hr; rw [hH0 r hr, hH0' r hr, map_zero]
  have key : hD ^ w * Φ h = hD ^ w * h' := by
    rw [e2, ← hΦH, ← e1, map_mul, map_pow, hΦD]
  have hne : hD ^ w ≠ 0 := pow_ne_zero _ hD0
  have hh := mul_left_cancel₀ hne key
  rw [← hh, hΦc]

end GlobalTheory.FN
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspExpansionCoeffConjOfQExpansionConjStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspExpansion_coeff_conj_of_qExpansion_conj : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (s : Ω →+* Ω) (g : ℂ ≃+* ℂ) (N w : ℕ) (f f' : ℍ → ℂ) (h h' : HahnSeries ℚ Ω), (∀ x, g (ε x) = ε (s x)) → 0 < N → QAll (· ∈ ε.range) N (fun τ => DD τ ^ w * f τ) → QConj g N (fun τ => DD τ ^ w * f τ) (fun τ => DD τ ^ w * f' τ) → IsExp ε f h → IsExp ε f' h' → ∀ r, h'.coeff r = s (h.coeff r) := by
  first | exact @GlobalTheory.FN.exp_conj | exact GlobalTheory.FN.exp_conj | (intros; apply GlobalTheory.FN.exp_conj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTowerUnionZetaDerivationModIntegralClosure
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTowerUnionZetaDerivationModIntegralClosure
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

noncomputable section

namespace GlobalTheory.AlmostEt

section DerLemmas

variable {A S M : Type*} [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup M] [Module S M]

theorem IsDerOn.mono' {B C : Subalgebra A S} {D : S → M} (h : IsDerOn C D) (hBC : B ≤ C) :
    IsDerOn B D :=
  ⟨fun x hx y hy => h.add x (hBC hx) y (hBC hy), fun x hx y hy => h.mul x (hBC hx) y (hBC hy), h.alg⟩

theorem IsDerOn.pow_succ_der {B : Subalgebra A S} {D : S → M} (h : IsDerOn B D) {x : S} (hx : x ∈ B)
    (k : ℕ) : D (x ^ (k + 1)) = (((k + 1 : ℕ) : S) * x ^ k) • D x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [_root_.pow_succ' x (k + 1), h.mul x hx _ (pow_mem hx _), ih, smul_smul, ← add_smul]
    congr 1
    push_cast
    ring

theorem IsDerOn.eq_on_adjoin {s : Set S} {D₁ D₂ : S → M} (h₁ : IsDerOn (Algebra.adjoin A s) D₁)
    (h₂ : IsDerOn (Algebra.adjoin A s) D₂) (hs : ∀ x ∈ s, D₁ x = D₂ x) :
    ∀ x ∈ Algebra.adjoin A s, D₁ x = D₂ x := by
  intro x hx
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact hs x hx
  | algebraMap a => rw [h₁.alg, h₂.alg]
  | add x y hx hy ihx ihy => rw [h₁.add x hx y hy, h₂.add x hx y hy, ihx, ihy]
  | mul x y hx hy ihx ihy => rw [h₁.mul x hx y hy, h₂.mul x hx y hy, ihx, ihy]

end DerLemmas

section TowerDer

open GlobalTheory.K5 Polynomial

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem zS_succ_pow_p (T : Tower p Ω) (m : ℕ) : zS T (m + 1) ^ p = zS T m :=
  Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact T.ζpow m)

theorem qS_succ_pow_p (T : Tower p Ω) (m : ℕ) : qS T (m + 1) ^ p = qS T m :=
  Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact T.qpow m)

theorem zS_mem_levelAlg (T : Tower p Ω) (m : ℕ) : zS T m ∈ levelAlg T m :=
  Algebra.subset_adjoin (Set.mem_insert (zS T m) {qS T m})

theorem qS_mem_levelAlg (T : Tower p Ω) (m : ℕ) : qS T m ∈ levelAlg T m :=
  Algebra.subset_adjoin (Set.mem_insert_of_mem _ (Set.mem_singleton (qS T m)))

theorem zS_mem_levelAlg_succ (T : Tower p Ω) (m : ℕ) : zS T m ∈ levelAlg T (m + 1) := by
  rw [← zS_succ_pow_p]; exact pow_mem (zS_mem_levelAlg T (m + 1)) _

theorem qS_mem_levelAlg_succ (T : Tower p Ω) (m : ℕ) : qS T m ∈ levelAlg T (m + 1) := by
  rw [← qS_succ_pow_p]; exact pow_mem (qS_mem_levelAlg T (m + 1)) _

theorem levelAlg_le_succ (T : Tower p Ω) (m : ℕ) : levelAlg T m ≤ levelAlg T (m + 1) :=
  Algebra.adjoin_le (Set.insert_subset_iff.2 ⟨zS_mem_levelAlg_succ T m,
    Set.singleton_subset_iff.2 (qS_mem_levelAlg_succ T m)⟩)

theorem frac_smul_mk (s : integralClosure (O0 p) Ω) (x : Ω) :
    s • (Submodule.Quotient.mk x : Frac p Ω) = Submodule.Quotient.mk ((s : Ω) * x) := by
  rw [← Submodule.Quotient.mk_smul]; rfl

theorem frac_mk_eq_zero (s : integralClosure (O0 p) Ω) :
    (Submodule.Quotient.mk (s : Ω) : Frac p Ω) = 0 := by
  rw [Submodule.Quotient.mk_eq_zero]
  exact ⟨s, rfl⟩

theorem cyc_relation (hc : CharZero Ω) (T : Tower p Ω) (m : ℕ) :
    (Polynomial.aeval (zS T (m + 1)) (Polynomial.derivative (Polynomial.cyclotomic (p ^ (m + 1)) (O0 p)))) •
      (Submodule.Quotient.mk (T.ζ (m + 1) * p / (p : Ω) ^ (m + 1)) : Frac p Ω) = 0 := by
  set z := zS T (m + 1)
  set ζ := T.ζ (m + 1)
  have hp1 : 1 < p := hp.out.one_lt
  have hpos : 0 < p ^ (m + 1) := pow_pos hp.out.pos _
  have hp0 : (p : Ω) ≠ 0 := by exact_mod_cast hp.out.ne_zero

  have hξ : IsPrimitiveRoot (ζ ^ p ^ m) p := by
    have := (T.prim (m + 1)).pow_of_dvd (pow_ne_zero m hp.out.ne_zero) (pow_dvd_pow p (Nat.le_succ m))
    simpa [pow_succ, Nat.mul_div_cancel_left _ (pow_pos hp.out.pos m)] using this

  set gS : integralClosure (O0 p) Ω := ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range i, (z ^ p ^ m) ^ j
  have hgval : (gS : Ω) = ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range i, (ζ ^ p ^ m) ^ j := by
    simp [gS, z, ζ, zS]
  have hg : (gS : Ω) * (ζ ^ p ^ m - 1) = - p := by
    rw [hgval, Finset.sum_mul]
    simp_rw [geom_sum_mul]
    rw [Finset.sum_sub_distrib, hξ.geom_sum_eq_zero hp1]
    simp

  have hroot : Polynomial.aeval ζ (Polynomial.cyclotomic (p ^ (m + 1)) (O0 p)) = 0 := by
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
    exact (T.prim (m + 1)).isRoot_cyclotomic hpos
  have hid := congrArg (fun f => Polynomial.aeval ζ (Polynomial.derivative f))
    (cyclotomic_prime_pow_mul_X_pow_sub_one (O0 p) p m)
  simp only [derivative_mul, derivative_sub, derivative_X_pow, derivative_one, map_add (f := _), map_mul,
    map_sub, hroot, zero_mul, add_zero, sub_zero] at hid
  have hzval : (Polynomial.aeval z (Polynomial.derivative (Polynomial.cyclotomic (p ^ (m + 1)) (O0 p))) : Ω)
      = Polynomial.aeval ζ (Polynomial.derivative (Polynomial.cyclotomic (p ^ (m + 1)) (O0 p))) := by
    exact (Polynomial.aeval_algHom_apply (integralClosure (O0 p) Ω).val z _).symm
  rw [frac_smul_mk, hzval]
  set F := Polynomial.aeval ζ (Polynomial.derivative (Polynomial.cyclotomic (p ^ (m + 1)) (O0 p)))
  have hζ1 : ζ ^ p ^ (m + 1) = 1 := (T.prim (m + 1)).pow_eq_one
  have hF : F * (ζ ^ p ^ m - 1) * ζ = (p : Ω) ^ (m + 1) := by
    have h2 : F * (ζ ^ p ^ m - 1) = (p : Ω) ^ (m + 1) * ζ ^ (p ^ (m + 1) - 1) := by
      simpa [map_natCast] using hid
    rw [h2, mul_assoc, pow_sub_one_mul (pow_ne_zero _ hp.out.ne_zero), hζ1, mul_one]
  have hξ1 : ζ ^ p ^ m - 1 ≠ 0 := sub_ne_zero.2 (hξ.ne_one hp1)
  have key : F * (ζ * p / (p : Ω) ^ (m + 1)) = ((-gS : integralClosure (O0 p) Ω) : Ω) := by
    apply mul_right_cancel₀ hξ1
    push_cast
    rw [neg_mul, hg, neg_neg]
    have hpm : (p : Ω) ^ (m + 1) ≠ 0 := pow_ne_zero _ hp0
    rw [div_eq_mul_inv]
    linear_combination ((p : Ω) * ((p : Ω) ^ (m + 1))⁻¹) * hF + (p : Ω) * mul_inv_cancel₀ hpm
  rw [key, frac_mk_eq_zero]

end TowerDer

end GlobalTheory.AlmostEt

namespace GlobalTheory.AlmostEt

open GlobalTheory.K5

theorem IsDerOn.pow_der {A S M : Type*} [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup M]
    [Module S M] {B : Subalgebra A S} {D : S → M} (h : IsDerOn B D) {x : S} (hx : x ∈ B) {n : ℕ}
    (hn : 0 < n) : D (x ^ n) = ((n : S) * x ^ (n - 1)) • D x := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  simpa using h.pow_succ_der hx k

theorem zeta_derivation : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω],
    IsClo p Ω → ∀ (T : Tower p Ω), ∃ D : (integralClosure (O0 p) Ω) → Frac p Ω,
      IsDerOn (towerAlg T) D ∧ ∀ m : ℕ, D (zS T m) = Submodule.Quotient.mk (T.ζ m * p / (p : Ω) ^ m) ∧
        D (qS T m) = 0 := by
  intro p hp Ω _ _ hc T
  haveI : CharZero Ω := GlobalTheory.K5.Basic.charZero_of_isClo hc
  have hp0 : (p : Ω) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hlev : ∀ m : ℕ, ∃ D : (integralClosure (O0 p) Ω) → Frac p Ω,
      IsDerOn (levelAlg T (m + 1)) D ∧
        D (zS T (m + 1)) = Submodule.Quotient.mk (T.ζ (m + 1) * p / (p : Ω) ^ (m + 1)) ∧
        D (qS T (m + 1)) = 0 := fun m =>
    GlobalTheory.T.exists_derivation_towerLevelAlgebra_prescribed p Ω hc T (m + 1) (Nat.succ_pos m) (Frac p Ω) _ 0
      (cyc_relation inferInstance T m) (smul_zero _)
  choose D hD hDz hDq using hlev
  have hval : ∀ m, D m (zS T m) = Submodule.Quotient.mk (T.ζ m * p / (p : Ω) ^ m) ∧
      D m (qS T m) = 0 := by
    intro m
    constructor
    · rw [← zS_succ_pow_p, (hD m).pow_der (zS_mem_levelAlg T (m + 1)) hp.out.pos, hDz m, frac_smul_mk]
      congr 1
      have hc1 : ((zS T (m + 1) : integralClosure (O0 p) Ω) : Ω) = T.ζ (m + 1) := rfl
      push_cast
      rw [hc1, ← T.ζpow m, ← pow_sub_one_mul hp.out.ne_zero (T.ζ (m + 1))]
      field_simp
      ring
    · rw [← qS_succ_pow_p, (hD m).pow_der (qS_mem_levelAlg T (m + 1)) hp.out.pos, hDq m, smul_zero]
  have hcompat : ∀ m, ∀ x ∈ levelAlg T (m + 1), D (m + 1) x = D m x := by
    intro m
    refine IsDerOn.eq_on_adjoin (s := {zS T (m + 1), qS T (m + 1)})
      ((hD (m + 1)).mono' (levelAlg_le_succ T (m + 1))) (hD m) ?_
    rintro x (rfl | hx)
    · rw [(hval (m + 1)).1, hDz m]
    · rw [Set.mem_singleton_iff.1 hx, (hval (m + 1)).2, hDq m]
  have hmono : Monotone (fun m => levelAlg T (m + 1)) :=
    monotone_nat_of_le_succ fun m => levelAlg_le_succ T (m + 1)
  obtain ⟨D', hD', hD'eq⟩ := isDerOn_iSup_glue (O0 p) (integralClosure (O0 p) Ω) (Frac p Ω)
    (fun m => levelAlg T (m + 1)) hmono D hD hcompat
  have hle : towerAlg T ≤ ⨆ m, levelAlg T (m + 1) := by
    refine Algebra.adjoin_le ?_
    rintro x (⟨m, rfl⟩ | ⟨m, rfl⟩)
    · exact (le_iSup (fun m => levelAlg T (m + 1)) m) (zS_mem_levelAlg_succ T m)
    · exact (le_iSup (fun m => levelAlg T (m + 1)) m) (qS_mem_levelAlg_succ T m)
  refine ⟨D', hD'.mono' hle, fun m => ⟨?_, ?_⟩⟩
  · rw [hD'eq m _ (zS_mem_levelAlg_succ T m), (hval m).1]
  · rw [hD'eq m _ (qS_mem_levelAlg_succ T m), (hval m).2]

end GlobalTheory.AlmostEt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTowerUnionZetaDerivationModIntegralClosureStatement
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_towerUnion_zetaDerivation_modIntegralClosure : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω), ∃ D : (integralClosure (O0 p) Ω) → Frac p Ω, IsDerOn (towerAlg T) D ∧ ∀ m : ℕ, D (zS T m) = Submodule.Quotient.mk (T.ζ m * p / (p : Ω) ^ m) ∧ D (qS T m) = 0 := by
  first | exact @GlobalTheory.AlmostEt.zeta_derivation | exact GlobalTheory.AlmostEt.zeta_derivation | (intros; apply GlobalTheory.AlmostEt.zeta_derivation <;> assumption)
end
end
