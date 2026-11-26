module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasLabelTransportEquiv
public import GroundTheory.LocalFields.RamificationStructure
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixedByCyclotomicKernelEtalePhiSolutionMemWach

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeWildJumpSumOfElementaryAbelian
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeWildJumpSumTotallyRamified
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UpperRamificationGroupOneEqTopOfExponentPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UpperRamificationGroupOneEqTopOfExponentPrime
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem ringChar_residue_eq_of_ordIs (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (p e : ℕ) (hp : p.Prime) (he : 0 < e) (h : OrdIs F p e) :
    ringChar 𝓀[F] = p := by
  have hnu : ¬ IsUnit (p : 𝒪[F]) := by
    intro hu
    have := (IsDiscreteValuationRing.addVal_eq_zero_of_unit (hu.unit))
    unfold OrdIs at h
    simp at this
    rw [this] at h
    norm_cast at h
    omega
  have hm : (p : 𝒪[F]) ∈ IsLocalRing.maximalIdeal 𝒪[F] := hnu
  have h0 : ((p : ℕ) : 𝓀[F]) = 0 := by
    rw [← map_natCast (IsLocalRing.residue 𝒪[F]), IsLocalRing.residue_eq_zero_iff]
    exact hm
  have hd : ringChar 𝓀[F] ∣ p := (ringChar.spec 𝓀[F] p).mp h0
  rcases (Nat.dvd_prime hp).mp hd with h1 | h1
  · exact absurd h1 CharP.ringChar_ne_one
  · exact h1

theorem upperRamificationGroup_one_eq_top_of_exponent :
    ∀ (F M : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field M]
      [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M] [Algebra F M] [ValuativeExtension F M]
      [FiniteDimensional F M] [IsGalois F M] (p e : ℕ), p.Prime → 0 < e → OrdIs F p e →
      upperRamificationGroup F M 0 = ⊤ → (∀ σ : M ≃ₐ[F] M, σ ^ p = 1) → upperRamificationGroup F M 1 = ⊤ := by
  intro F M _ _ _ _ _ _ _ _ _ _ _ _ p e hp he hord h0 hexp
  rw [upperRamificationGroup_zero] at h0
  have hchar := ringChar_residue_eq_of_ordIs F p e hp he hord
  have hcop := coprime_card_lowerRamificationGroup_zero_quotient F M
  rw [hchar] at hcop
  have h1 : lowerRamificationGroup F M 1 = ⊤ := by
    rw [eq_top_iff]
    intro σ _
    have hσ0 : σ ∈ lowerRamificationGroup F M 0 := by rw [h0]; trivial
    set q : lowerRamificationGroup F M 0 ⧸
        (lowerRamificationGroup F M 1).subgroupOf (lowerRamificationGroup F M 0) :=
      QuotientGroup.mk ⟨σ, hσ0⟩ with hq
    have hqp : q ^ p = 1 := by
      rw [hq, ← QuotientGroup.mk_pow]
      have : (⟨σ, hσ0⟩ : lowerRamificationGroup F M 0) ^ p = 1 := Subtype.ext (by simpa using hexp σ)
      rw [this, QuotientGroup.mk_one]
    have hqc : q ^ Nat.card (lowerRamificationGroup F M 0 ⧸
        (lowerRamificationGroup F M 1).subgroupOf (lowerRamificationGroup F M 0)) = 1 := pow_card_eq_one'
    have hg : q ^ Nat.gcd _ p = 1 := pow_gcd_eq_one.mpr ⟨hqc, hqp⟩
    rw [hcop, pow_one, hq, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hg
    exact hg
  have hphi0 : herbrandPhi F M 0 = 0 := by simp [herbrandPhi]
  have hphi1 : herbrandPhi F M 1 = 1 := by
    have := herbrandPhi_of_mem_Icc (K := F) (L := M) 0 (u := 1) (by norm_num)
    have h1' : lowerRamificationGroup F M (((0 : ℕ) : ℤ) + 1) = ⊤ := by simpa using h1
    rw [h1', Subgroup.relIndex_top_left] at this
    simpa [hphi0] using this
  rw [← hphi1, upperRamificationGroup_herbrandPhi, ← Nat.cast_one, lowerRamificationGroupReal_natCast]
  simpa using h1
end GlobalTheory.PMon.Ram
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UpperRamificationGroupOneEqTopOfExponentPrimeStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.upperRamificationGroup_one_eq_top_of_exponent_prime : ∀ (F M : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M] [Algebra F M] [ValuativeExtension F M] [FiniteDimensional F M] [IsGalois F M] (p e : ℕ), p.Prime → 0 < e → OrdIs F p e → upperRamificationGroup F M 0 = ⊤ → (∀ σ : M ≃ₐ[F] M, σ ^ p = 1) → upperRamificationGroup F M 1 = ⊤ := by
  first | exact @GlobalTheory.PMon.Ram.upperRamificationGroup_one_eq_top_of_exponent | exact GlobalTheory.PMon.Ram.upperRamificationGroup_one_eq_top_of_exponent | (intros; apply GlobalTheory.PMon.Ram.upperRamificationGroup_one_eq_top_of_exponent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeWildJumpSumTotallyRamified
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem card_le_jumpSum_wild_of_exponent :
    ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L]
      [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L]
      [FiniteDimensional F L] [IsGalois F L] (p E : ℕ) (B : Subgroup (L ≃ₐ[F] L)), p.Prime → 0 < E →
      lowerRamificationGroup F L 0 = ⊤ → OrdIs L p E → (∀ σ τ : L ≃ₐ[F] L, σ * τ * σ⁻¹ * τ⁻¹ ∈ B) →
      (∀ σ : L ≃ₐ[F] L, σ ^ p ∈ B) → B ≠ ⊤ → Nat.card (L ≃ₐ[F] L) ≤ jumpSum (wild F L) ⊤ B := by
  intro F L _ _ _ _ _ _ _ _ _ _ _ _ p E B hp hE h0 hord hcomm hpow hB
  have hBn : B.Normal := ⟨fun b hb σ => by
    have h := B.mul_mem (hcomm σ b) hb
    simpa [mul_assoc] using h⟩
  set M := IntermediateField.fixedField B
  have hker : (AlgEquiv.restrictNormalHom (F := F) (K₁ := L) M).ker = B := by
    rw [IntermediateField.restrictNormalHom_ker, IntermediateField.fixingSubgroup_fixedField]
  have hsurj := AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := M) L
  obtain ⟨e, hordF, hEe, -⟩ := GlobalTheory.T.normalizedValuationOfPrime_of_galoisExtension F L p E hord
  have he : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · subst h; omega
    · exact h
  have hM0 : upperRamificationGroup F M 0 = ⊤ := by
    rw [← map_upperRamificationGroup M 0, upperRamificationGroup_zero, h0, Subgroup.map_top_of_surjective _ hsurj]
  have hMexp : ∀ s : M ≃ₐ[F] M, s ^ p = 1 := by
    intro s
    obtain ⟨σ, rfl⟩ := hsurj s
    rw [← map_pow, ← MonoidHom.mem_ker, hker]
    exact hpow σ
  have hM1 := GlobalTheory.T.upperRamificationGroup_one_eq_top_of_exponent_prime F M p e hp he hordF hM0 hMexp
  obtain ⟨σ₀, hσ₀⟩ : ∃ σ₀, σ₀ ∉ B := by
    by_contra h
    push_neg at h
    exact hB (eq_top_iff.mpr fun x _ => h x)
  have hmem : AlgEquiv.restrictNormalHom M σ₀ ∈ (upperRamificationGroup F L 1).map (AlgEquiv.restrictNormalHom M) := by
    rw [map_upperRamificationGroup M 1, hM1]; trivial
  obtain ⟨σ, hσ, hσe⟩ := hmem
  have hσB : σ ∉ B := by
    intro hσB
    apply hσ₀
    rw [← hker, MonoidHom.mem_ker, ← hσe, ← MonoidHom.mem_ker, hker]
    exact hσB
  have := GlobalTheory.T.card_mul_le_jumpSum_of_mem_upperRamification_not_mem F L B 1 h0 σ hσ hσB
  rw [mul_one] at this
  exact_mod_cast this

end GlobalTheory.PMon.Ram
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeWildJumpSumTotallyRamifiedStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_le_wild_jumpSum_totallyRamified : ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L] (p E : ℕ) (B : Subgroup (L ≃ₐ[F] L)), p.Prime → 0 < E → lowerRamificationGroup F L 0 = ⊤ → OrdIs L p E → (∀ σ τ : L ≃ₐ[F] L, σ * τ * σ⁻¹ * τ⁻¹ ∈ B) → (∀ σ : L ≃ₐ[F] L, σ ^ p ∈ B) → B ≠ ⊤ → Nat.card (L ≃ₐ[F] L) ≤ jumpSum (wild F L) ⊤ B := by
  first | exact @GlobalTheory.PMon.Ram.card_le_jumpSum_wild_of_exponent | exact GlobalTheory.PMon.Ram.card_le_jumpSum_wild_of_exponent | (intros; apply GlobalTheory.PMon.Ram.card_le_jumpSum_wild_of_exponent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeWildJumpSumOfElementaryAbelian
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem card_le_jumpSum_wild :
    ∀ (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L] (p E : ℕ) (A B : Subgroup (L ≃ₐ[K] L)), p.Prime → 0 < E → A ≤ lowerRamificationGroup K L 0 → OrdIs L p E → (∀ σ ∈ A, ∀ τ ∈ A, σ * τ * σ⁻¹ * τ⁻¹ ∈ B) → (∀ σ ∈ A, σ ^ p ∈ B) → ¬ A ≤ B → Nat.card ↥A ≤ jumpSum (wild K L) A B := by
  intro K L _ _ _ _ _ _ _ _ _ _ _ _ p E A B hp hE hA hord hcomm hpow hnot
  obtain ⟨j, hj, hrange, -, hram⟩ := GlobalTheory.T.galoisGroup_fixedField_baseChange_localField K L A
  have hmemA : ∀ σ, j σ ∈ A := fun σ => hrange.le ⟨σ, rfl⟩
  have htop : lowerRamificationGroup (IntermediateField.fixedField A) L 0 = ⊤ := by
    rw [hram, eq_top_iff]
    intro σ _
    exact hA (hmemA σ)
  have hcomm' : ∀ σ τ : L ≃ₐ[IntermediateField.fixedField A] L,
      σ * τ * σ⁻¹ * τ⁻¹ ∈ B.comap j := by
    intro σ τ
    rw [Subgroup.mem_comap, map_mul, map_mul, map_mul, map_inv, map_inv]
    exact hcomm _ (hmemA σ) _ (hmemA τ)
  have hpow' : ∀ σ : L ≃ₐ[IntermediateField.fixedField A] L, σ ^ p ∈ B.comap j := by
    intro σ
    rw [Subgroup.mem_comap, map_pow]
    exact hpow _ (hmemA σ)
  have hne : B.comap j ≠ ⊤ := by
    intro h
    apply hnot
    intro a ha
    obtain ⟨σ, rfl⟩ := hrange.ge ha
    have : σ ∈ B.comap j := h ▸ Subgroup.mem_top σ
    exact this
  have key := GlobalTheory.T.card_le_wild_jumpSum_totallyRamified (IntermediateField.fixedField A) L p E (B.comap j) hp hE htop hord
    hcomm' hpow' hne
  have hwild : wild (IntermediateField.fixedField A) L = fun t => (wild K L t).comap j := by
    funext t
    exact hram _
  have hcard : Nat.card (L ≃ₐ[IntermediateField.fixedField A] L) = Nat.card ↥A := by
    exact (Nat.card_congr (MonoidHom.ofInjective hj).toEquiv).trans
      (congrArg (fun H : Subgroup (L ≃ₐ[K] L) => Nat.card ↥H) hrange)
  have hjs : jumpSum (wild K L) A B =
      jumpSum (wild (IntermediateField.fixedField A) L) ⊤ (B.comap j) := by
    rw [hwild, GlobalTheory.T.ramificationJumpSum_comap_injective _ _ j (wild K L) B hj]
    exact congrArg (fun H => jumpSum (wild K L) H B) hrange.symm
  calc Nat.card ↥A = Nat.card (L ≃ₐ[IntermediateField.fixedField A] L) := hcard.symm
    _ ≤ _ := key
    _ = jumpSum (wild K L) A B := hjs.symm

end GlobalTheory.PMon.Ram
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeWildJumpSumOfElementaryAbelianStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_le_wildJumpSum_of_elementaryAbelian : ∀ (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L] (p E : ℕ) (A B : Subgroup (L ≃ₐ[K] L)), p.Prime → 0 < E → A ≤ lowerRamificationGroup K L 0 → OrdIs L p E → (∀ σ ∈ A, ∀ τ ∈ A, σ * τ * σ⁻¹ * τ⁻¹ ∈ B) → (∀ σ ∈ A, σ ^ p ∈ B) → ¬ A ≤ B → Nat.card ↥A ≤ jumpSum (wild K L) A B := by
  first | exact @GlobalTheory.PMon.Ram.card_le_jumpSum_wild | exact GlobalTheory.PMon.Ram.card_le_jumpSum_wild | (intros; apply GlobalTheory.PMon.Ram.card_le_jumpSum_wild <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WittTwistInvariantBasisChange
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WittTwistInvariantBasisChange
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

namespace GlobalTheory.HWL.EtMem

section Lin

variable {E S D M : Type} [CommRing E] [CommRing S] [AddCommGroup D] [Module E D] [AddCommGroup M] [Module S M]

theorem exists_basis [Nontrivial S] [Module.Free S M] [Module.Finite S M] {r : ℕ} (io : E → S) (j : D →+ M)
    (hj : ∀ e x, j (e • x) = io e • j x) (hsp : Submodule.span S (Set.range j) = ⊤)
    (b : Module.Basis (Fin r) E D) (hr : Module.finrank S M = r) :
    ∃ e : Module.Basis (Fin r) S M, ∀ i, e i = j (b i) := by
  have h : ⊤ ≤ Submodule.span S (Set.range fun i => j (b i)) := by
    rw [← hsp, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← b.sum_repr x, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [hj]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  refine ⟨basisOfTopLeSpanOfCardEqFinrank _ h (by simp [hr]), fun i => by simp⟩

theorem repr_semi {r : ℕ} (e : Module.Basis (Fin r) S M) (φ : S → S) (Φ : M →+ M)
    (hΦ : ∀ c m, Φ (c • m) = φ c • Φ m) (m : M) (i : Fin r) :
    e.repr (Φ m) i = ∑ k, e.repr (Φ (e k)) i * φ (e.repr m k) := by
  set_option synthInstance.maxHeartbeats 100000 in
    conv_lhs => rw [← e.sum_repr m, map_sum, map_sum]
  simp [hΦ, Finsupp.finsetSum_apply, mul_comm]

theorem isUnit_det {r : ℕ} (e : Module.Basis (Fin r) S M) (φ : S → S) (Φ : M →+ M)
    (hΦ : ∀ c m, Φ (c • m) = φ c • Φ m) (hsp : Submodule.span S {m | Φ m = m} = ⊤) :
    IsUnit (Matrix.of fun i k => e.repr (Φ (e k)) i).det := by
  have h : ∀ m : M, ∃ w : Fin r → S, ∀ i, e.repr m i = ∑ k, e.repr (Φ (e k)) i * w k := by
    intro m
    have hm : m ∈ Submodule.span S {m | Φ m = m} := hsp ▸ Submodule.mem_top
    induction hm using Submodule.span_induction with
    | mem x hx =>
      refine ⟨fun k => φ (e.repr x k), fun i => ?_⟩
      rw [← repr_semi e φ Φ hΦ, show Φ x = x from hx]
    | zero => exact ⟨0, fun i => by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨u, hu⟩ := hx
      obtain ⟨w, hw⟩ := hy
      exact ⟨u + w, fun i => by simp [hu, hw, mul_add, Finset.sum_add_distrib]⟩
    | smul c x _ hx =>
      obtain ⟨u, hu⟩ := hx
      exact ⟨c • u, fun i => by simp [hu, Finset.mul_sum, mul_left_comm]⟩
  choose w hw using h
  refine Matrix.isUnit_det_of_right_inverse (B := Matrix.of fun k j => w (e j) k) ?_
  ext i j
  simp only [Matrix.mul_apply, Matrix.of_apply]
  rw [← hw, e.repr_self, Matrix.one_apply, Finsupp.single_apply]
  simp [eq_comm]

end Lin

section Ten

variable {O S N : Type} [CommRing O] [CommRing S] [Algebra O S] [AddCommGroup N] [Module O N]

theorem map_smul_semi (f : S →ₐ[O] S) (g : N →ₗ[O] N) (c : S) (m : S ⊗[O] N) :
    TensorProduct.map f.toLinearMap g (c • m) = f c • TensorProduct.map f.toLinearMap g m := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul a t => simp [TensorProduct.smul_tmul']
  | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]

theorem map_mulLeft (c : S) (m : S ⊗[O] N) :
    TensorProduct.map (LinearMap.mulLeft O c) (LinearMap.id : N →ₗ[O] N) m = c • m := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul a t => simp [TensorProduct.smul_tmul']
  | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]

theorem span_fixed (f : S →ₐ[O] S) :
    Submodule.span S {m : S ⊗[O] N | TensorProduct.map f.toLinearMap (LinearMap.id : N →ₗ[O] N) m = m} = ⊤ := by
  rw [eq_top_iff]
  rintro m -
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul a t =>
    have : a ⊗ₜ[O] t = a • ((1 : S) ⊗ₜ[O] t) := by simp [TensorProduct.smul_tmul']
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  | add x y hx hy => exact Submodule.add_mem _ hx hy

end Ten

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n s : ℕ}
    {Γ : WGam PD LL O v n s} {R : WSer Γ}
    {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    {I : WIo R RA RW inclR φR gR πA}

theorem res_eq_one (hO : Function.Injective (algebraMap O LL)) (g : G) (hg : (PD.χ g : Qp) = 1) :
    Γ.resΓ g = 1 := by
  apply Γ.χΓ_inj
  rw [map_one Γ.χΓ]
  apply Units.ext
  apply hO
  rw [Γ.χΓ_res g, hg, Units.val_one, map_one, map_one]

theorem mem_range (E : WEt I) (T : LocLat G Qp LL O) (H : G → Prop) (hH : ∀ g, H g → Γ.resΓ g = 1)
    (hu : ∀ x : R.EE, IsUnit (I.ioE x) → IsUnit x) (q : ℕ) (x : Fin q → TW RW T)
    (A : Matrix (Fin q) (Fin q) R.EE)
    (hrat : ∀ (p : ℕ) (F : Matrix (Fin p) (Fin p) R.EE) (U : Matrix (Fin p) (Fin q) RW), IsUnit F →
      (∀ i j g, H g → gR g (U i j) = U i j) → F.map I.ioE * U.map φR = U * A.map I.ioE →
      ∀ i j, U i j ∈ Set.range I.ioE)
    (hx : ∀ g, H g → ∀ i, TWact (gR g) T g (x i) = x i)
    (hφ : ∀ j, TWmap φR T (x j) = ∑ i, TensorProduct.map (LinearMap.mulLeft O (I.ioE (A i j) : RW))
      (LinearMap.id : ↥T.L.T →ₗ[O] ↥T.L.T) (x i)) :
    ∀ i, x i ∈ Set.range (E.jD T) := by
  intro i₀
  rcases subsingleton_or_nontrivial RW with hS | hS
  · haveI : Subsingleton (TW RW T) := Module.subsingleton RW _
    exact ⟨0, Subsingleton.elim _ _⟩
  haveI : Nontrivial O := (algebraMap O RW).domain_nontrivial
  haveI : Nontrivial R.EE := I.ioE.toRingHom.domain_nontrivial
  haveI : Module.Free O ↥T.L.T := T.L.free
  haveI : Module.Finite O ↥T.L.T := Module.Finite.iff_fg.2 T.L.fg
  haveI : Module.Free R.EE (E.DD T) := (E.DD_free T).1
  have hrk : Module.finrank RW (TW RW T) = Module.finrank O ↥T.L.T := Module.finrank_baseChange
  rcases Nat.eq_zero_or_pos (Module.finrank O ↥T.L.T) with h0 | h0
  · haveI : Subsingleton (TW RW T) := (Module.finrank_eq_zero_iff_of_free RW _).1 (hrk.trans h0)
    exact ⟨0, Subsingleton.elim _ _⟩
  haveI : Module.Finite R.EE (E.DD T) := Module.finite_of_finrank_pos ((E.DD_free T).2 ▸ h0)
  let b := Module.finBasisOfFinrankEq R.EE (E.DD T) (E.DD_free T).2
  obtain ⟨e, he⟩ := exists_basis I.ioE (E.jD T).toAddMonoidHom (E.jD_smul T) (E.jD_span T) b hrk
  have he' : ∀ i, e i = E.jD T (b i) := he
  have hrep : ∀ (d : E.DD T) i, e.repr (E.jD T d) i = I.ioE (b.repr d i) := by
    intro d i
    set_option synthInstance.maxHeartbeats 100000 in
      conv_lhs => rw [← b.sum_repr d, map_sum]
    simp only [E.jD_smul, ← he']
    rw [e.repr_sum_self]
  have hsφ : ∀ (c : RW) (m : TW RW T), (TWmap φR T).toAddMonoidHom (c • m) =
      φR c • (TWmap φR T).toAddMonoidHom m := fun c m => map_smul_semi φR _ c m
  let F : Matrix (Fin (Module.finrank O ↥T.L.T)) (Fin (Module.finrank O ↥T.L.T)) R.EE :=
    Matrix.of fun i k => b.repr (E.φD T (b k)) i
  have hF : F.map I.ioE = Matrix.of fun i k => e.repr ((TWmap φR T).toAddMonoidHom (e k)) i := by
    ext i k
    simp only [F, Matrix.map_apply, Matrix.of_apply, LinearMap.toAddMonoidHom_coe]
    rw [he', ← E.jD_φ, hrep]
  have hFu : IsUnit F := by
    rw [Matrix.isUnit_iff_isUnit_det]
    apply hu
    have h1 := isUnit_det e φR (TWmap φR T).toAddMonoidHom hsφ (span_fixed φR)
    rw [← hF] at h1
    rw [AlgHom.map_det]
    exact h1
  have hU := hrat _ F (Matrix.of fun k j => e.repr (x j) k) hFu ?_ ?_
  · choose u hu' using hU
    refine ⟨∑ k, u k i₀ • b k, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [E.jD_smul, ← he', hu', Matrix.of_apply]
    exact e.sum_repr _
  · intro i j g hg
    have hs : ∀ (c : RW) (m : TW RW T), (TWact (gR g) T g).toAddMonoidHom (c • m) =
      gR g c • (TWact (gR g) T g).toAddMonoidHom m := fun c m => map_smul_semi (gR g) _ c m
    have h1 := repr_semi e (gR g) (TWact (gR g) T g).toAddMonoidHom hs (x j) i
    have h2 : ∀ k, TWact (gR g) T g (e k) = e k := fun k => by
      rw [he', ← E.jD_act, hH g hg, E.γD_one]
    simp only [LinearMap.toAddMonoidHom_coe, hx g hg, h2, e.repr_self, Finsupp.single_apply] at h1
    simp only [Matrix.of_apply]
    rw [Finset.sum_eq_single i (fun k _ hk => by simp [hk]) (by simp)] at h1
    simpa using h1.symm
  · rw [hF]
    ext i j
    have h1 := repr_semi e φR (TWmap φR T).toAddMonoidHom hsφ (x j) i
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.map_apply]
    rw [← h1, LinearMap.toAddMonoidHom_coe, hφ]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_mulLeft, map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _

end Generic


set_option maxHeartbeats 1000000 in
theorem fixed_mem_range : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R), IoW I → ∀ (E : WEt I) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (q : ℕ) (x : Fin q → TW (RW LL) T) (A : Matrix (Fin q) (Fin q) R.EE), IsUnit A → (∀ g : ↥(GK K), P.χQ (g : GQ l) = 1 → ∀ i, TWact (AI.gRW LL (g : GQ l)) T g (x i) = x i) → (∀ j, TWmap (φRW LL) T (x j) = ∑ i, TensorProduct.map (LinearMap.mulLeft ↥(OL LL) (I.ioE (A i j) : RW LL)) (LinearMap.id : ↥T.L.T →ₗ[↥(OL LL)] ↥T.L.T) (x i)) → ∀ i, x i ∈ Set.range (E.jD T) := by
  intro l _ P AI K s LL hG Γ R I hI E T q x A hA hx hφ
  have h1 : ∀ g : ↥(GK K), P.χQ (g : GQ l) = 1 → Γ.resΓ g = 1 := fun g hg =>
    res_eq_one Subtype.val_injective g ((P.PD_χ K g).trans (congrArg Units.val hg))
  set_option synthInstance.maxHeartbeats 200000 in
  have h2 : ∀ (p : ℕ) (F : Matrix (Fin p) (Fin p) R.EE) (U : Matrix (Fin p) (Fin q) (RW LL)), IsUnit F →
      (∀ i j (g : ↥(GK K)), P.χQ (g : GQ l) = 1 → AI.gRW LL (g : GQ l) (U i j) = U i j) →
      F.map I.ioE * U.map (φRW LL) = U * A.map I.ioE → ∀ i j, U i j ∈ Set.range I.ioE :=
    fun p F U hF hU hE => GlobalTheory.T.fixedByCyclotomicKernel_etalePhi_solution_mem_wach l P AI K s LL hG Γ R I hI p q F A 0 U hF hA
      (fun i j g hg h1 => hU i j ⟨g, hg⟩ h1)
      (by simpa only [Matrix.map_zero, map_zero, add_zero] using hE)
  exact mem_range E T (fun g => P.χQ (g : GQ l) = 1) h1 (GlobalTheory.T.wachInclusion_injective_saturated_inter l P AI K s LL hG Γ R I hI).2.1 q x A
    h2 hx hφ

end GlobalTheory.HWL.EtMem
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WittTwistInvariantBasisChangeStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_twist_invariant_basis_change : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R), IoW I → ∀ (E : WEt I) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (q : ℕ) (x : Fin q → TW (RW LL) T) (A : Matrix (Fin q) (Fin q) R.EE), IsUnit A → (∀ g : ↥(GK K), P.χQ (g : GQ l) = 1 → ∀ i, TWact (AI.gRW LL (g : GQ l)) T g (x i) = x i) → (∀ j, TWmap (φRW LL) T (x j) = ∑ i, TensorProduct.map (LinearMap.mulLeft ↥(OL LL) (I.ioE (A i j) : RW LL)) (LinearMap.id : ↥T.L.T →ₗ[↥(OL LL)] ↥T.L.T) (x i)) → ∀ i, x i ∈ Set.range (E.jD T) := by
  first | exact @GlobalTheory.HWL.EtMem.fixed_mem_range | exact GlobalTheory.HWL.EtMem.fixed_mem_range | (intros; apply GlobalTheory.HWL.EtMem.fixed_mem_range <;> assumption)
end
end
