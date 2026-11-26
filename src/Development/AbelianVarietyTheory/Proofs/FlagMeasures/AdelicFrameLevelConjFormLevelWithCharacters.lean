module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeLevelLocalDualQuotientLengthOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeFrameLocalBasisUnitriangular
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeFrameConditionCharacterLocal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalLevelCharacterMatchAtTypePrime
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemLevelOfPreservesFirstComponentsSplit
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemLevelOfPreservesFirstComponentsSplit
open Formalism.L2.Forms hiding dualL
open Formalism.BasicNotions Formalism.UG NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G

theorem mem_levelVL_of_first_components : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F)) (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), (∀ x, sp (sigR cm.sig (v.adicCompletion F) x) = swapR _ (sp x)) → (∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a)) → ∀ (L : Submodule (𝓞 E) (Fin n → E)), SelfDualAt cm.sig J v L → ∀ κ ∈ UPts cm.sig J (v.adicCompletion F), (∀ x : Fin n → v.adicCompletion F, (∃ y ∈ loc v L, ∀ b, (sp (y b)).1 = x b) ↔ ∃ y ∈ loc v L, ∀ b, (sp (y b)).1 = ((bc ((RingHom.fst _ _).comp sp.toRingHom) κ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec x b) → κ ∈ levelVL cm.sig J v L := by
  intro F E _ _ _ _ _ _ cm n J v sp hsig hdiag L hsd κ hκ hfirst
  have hint : ∀ x, x ∈ intV E v ↔
      (sp x).1 ∈ v.adicCompletionIntegers F ∧ (sp x).2 ∈ v.adicCompletionIntegers F :=
    split_integral_local F E v sp hdiag

  have pair1 : ∀ z y : Fin n → E ⊗[F] v.adicCompletion F, (sp (hR cm.sig J (v.adicCompletion F) z y)).1 =
      ∑ i, ∑ j, (sp (z i)).2 * (sp (inclE (F := F) (v.adicCompletion F) (J i j))).1 * (sp (y j)).1 := by
    intro z y
    unfold hR hform
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Prod.fst_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Prod.fst_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_mul, hsig]
    rfl
  have pair2 : ∀ z y : Fin n → E ⊗[F] v.adicCompletion F, (sp (hR cm.sig J (v.adicCompletion F) z y)).2 =
      ∑ i, ∑ j, (sp (z i)).1 * (sp (inclE (F := F) (v.adicCompletion F) (J i j))).2 * (sp (y j)).2 := by
    intro z y
    unfold hR hform
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Prod.snd_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Prod.snd_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_mul, hsig]
    rfl

  have hprod : ∀ y : Fin n → E ⊗[F] v.adicCompletion F, y ∈ loc v L ↔
      (∃ y₁ ∈ loc v L, ∀ b, (sp (y₁ b)).1 = (sp (y b)).1) ∧ ∃ y₂ ∈ loc v L, ∀ b, (sp (y₂ b)).2 = (sp (y b)).2 := by
    intro y
    refine ⟨fun hy => ⟨⟨y, hy, fun _ => rfl⟩, y, hy, fun _ => rfl⟩, ?_⟩
    rintro ⟨⟨y₁, h₁, e₁⟩, y₂, h₂, e₂⟩
    have ha : sp.symm (1, 0) ∈ intV E v := by
      rw [hint, sp.apply_symm_apply]; exact ⟨one_mem _, zero_mem _⟩
    have hb : sp.symm (0, 1) ∈ intV E v := by
      rw [hint, sp.apply_symm_apply]; exact ⟨zero_mem _, one_mem _⟩
    have hm := (loc v L).add_mem ((loc v L).smul_mem ⟨_, ha⟩ h₁) ((loc v L).smul_mem ⟨_, hb⟩ h₂)
    have hy : y = (⟨_, ha⟩ : intV E v) • y₁ + (⟨_, hb⟩ : intV E v) • y₂ := by
      funext b
      apply sp.injective
      change sp (y b) = sp (sp.symm (1, 0) * y₁ b + sp.symm (0, 1) * y₂ b)
      rw [map_add (f := _), map_mul, map_mul, sp.apply_symm_apply, sp.apply_symm_apply]
      ext
      · simp [e₁ b]
      · simp [e₂ b]
    rw [hy]; exact hm

  set Kv := v.adicCompletion F with hKv
  set φ1 : E ⊗[F] Kv →+* Kv := (RingHom.fst _ _).comp sp.toRingHom with hφ1
  set φ2 : E ⊗[F] Kv →+* Kv := (RingHom.snd _ _).comp sp.toRingHom with hφ2
  have e1 : ∀ a, φ1 a = (sp a).1 := fun _ => rfl
  have e2 : ∀ a, φ2 a = (sp a).2 := fun _ => rfl
  set K1 : Matrix (Fin n) (Fin n) Kv := (κ : Matrix (Fin n) (Fin n) (E ⊗[F] Kv)).map φ1 with hK1
  set K2 : Matrix (Fin n) (Fin n) Kv := (κ : Matrix (Fin n) (Fin n) (E ⊗[F] Kv)).map φ2 with hK2
  set J2 : Matrix (Fin n) (Fin n) Kv := (J.map (inclE (F := F) Kv)).map φ2 with hJ2

  have hU : cT (sigR cm.sig Kv) (κ : Matrix (Fin n) (Fin n) (E ⊗[F] Kv)) * J.map (inclE (F := F) Kv) *
      (κ : Matrix (Fin n) (Fin n) (E ⊗[F] Kv)) = J.map (inclE (F := F) Kv) := hκ
  have hc : (cT (sigR cm.sig Kv) (κ : Matrix (Fin n) (Fin n) (E ⊗[F] Kv))).map φ2 = K1ᵀ := by
    refine Matrix.ext fun i j => ?_
    show (sp (sigR cm.sig Kv ((κ : Matrix (Fin n) (Fin n) (E ⊗[F] Kv)) j i))).2 = (sp ((κ : Matrix (Fin n) (Fin n) (E ⊗[F] Kv)) j i)).1
    rw [hsig]; rfl
  have hU2 : K1ᵀ * J2 * K2 = J2 := by
    have := congrArg (fun M => M.map φ2) hU
    simp only [Matrix.map_mul] at this
    rw [hc] at this
    exact this
  have hQ : ∀ u w : Fin n → Kv, (K1 *ᵥ u) ⬝ᵥ (J2 *ᵥ (K2 *ᵥ w)) = u ⬝ᵥ (J2 *ᵥ w) := by
    intro u w
    conv_rhs => rw [← hU2, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_transpose]
  have hsum : ∀ u w : Fin n → Kv, (∑ i, ∑ j, u i * J2 i j * w j) = u ⬝ᵥ (J2 *ᵥ w) := by
    intro u w
    simp only [dotProduct, mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

  have hL2 : ∀ w : Fin n → Kv, (∃ y ∈ loc v L, ∀ b, (sp (y b)).2 = w b) ↔
      ∀ u : Fin n → Kv, (∃ z ∈ loc v L, ∀ b, (sp (z b)).1 = u b) → u ⬝ᵥ (J2 *ᵥ w) ∈ v.adicCompletionIntegers F := by
    intro w
    constructor
    · rintro ⟨y, hy, ey⟩ u ⟨z, hz, ez⟩
      have h := ((hint _).1 (((hsd y).1 hy) z hz)).2
      rw [pair2] at h
      simp only [ez, ey] at h
      rw [← hsum]; exact h
    · intro h
      refine ⟨fun b => sp.symm (0, w b), ?_, fun b => by simp⟩
      refine (hsd _).2 fun z hz => (hint _).2 ⟨?_, ?_⟩
      · rw [pair1]; simp
      · rw [pair2]
        have := h (fun b => (sp (z b)).1) ⟨z, hz, fun _ => rfl⟩
        rw [← hsum] at this
        have e : ∀ j, (sp (sp.symm (0, w j))).2 = w j := fun j => by simp
        simp only [e]
        exact this

  have hH : ∀ x : Fin n → Kv, (∃ y ∈ loc v L, ∀ b, (sp (y b)).1 = x b) ↔
      ∃ y ∈ loc v L, ∀ b, (sp (y b)).1 = (K1 *ᵥ x) b := hfirst
  have hK1inv : ∀ u : Fin n → Kv, ∃ u', K1 *ᵥ u' = u := by
    intro u
    refine ⟨(((bc φ1 κ)⁻¹ : GL (Fin n) Kv) : Matrix (Fin n) (Fin n) Kv) *ᵥ u, ?_⟩
    rw [Matrix.mulVec_mulVec]
    have : K1 * (((bc φ1 κ)⁻¹ : GL (Fin n) Kv) : Matrix (Fin n) (Fin n) Kv) = 1 := by
      have := (bc φ1 κ).mul_inv
      exact this
    rw [this, Matrix.one_mulVec]
  have hK2 : ∀ w : Fin n → Kv, (∃ y ∈ loc v L, ∀ b, (sp (y b)).2 = w b) ↔
      ∃ y ∈ loc v L, ∀ b, (sp (y b)).2 = (K2 *ᵥ w) b := by
    intro w
    rw [hL2, hL2]
    constructor
    · intro h u hu
      obtain ⟨u', rfl⟩ := hK1inv u
      rw [hQ]
      exact h u' ((hH u').2 hu)
    · intro h u hu
      rw [← hQ]
      exact h _ ((hH u).1 hu)

  have hc1 : ∀ (x : Fin n → E ⊗[F] Kv) b, (sp (((κ : Matrix (Fin n) (Fin n) (E ⊗[F] Kv)) *ᵥ x) b)).1 =
      (K1 *ᵥ fun j => (sp (x j)).1) b := by
    intro x b
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [mulVec, dotProduct, map_sum, Prod.fst_sum, map_mul, Prod.fst_mul]
    rfl
  have hc2 : ∀ (x : Fin n → E ⊗[F] Kv) b, (sp (((κ : Matrix (Fin n) (Fin n) (E ⊗[F] Kv)) *ᵥ x) b)).2 =
      (K2 *ᵥ fun j => (sp (x j)).2) b := by
    intro x b
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [mulVec, dotProduct, map_sum, Prod.snd_sum, map_mul, Prod.snd_mul]
    rfl
  show κ ∈ UJ _ _ ⊓ stabGL _
  rw [Subgroup.mem_inf]
  refine ⟨hκ, fun x => ?_⟩
  change x ∈ loc v L ↔ _ ∈ loc v L
  rw [hprod x, hprod (_ *ᵥ x)]
  simp only [hc1, hc2]
  rw [hH (fun j => (sp (x j)).1), hK2 (fun j => (sp (x j)).2)]

end GlobalTheory.St.G
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemLevelOfPreservesFirstComponentsSplitStatement
open Formalism.L2.Forms hiding dualL
open Formalism.BasicNotions Formalism.UG NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_level_of_preserves_first_components_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F)) (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), (∀ x, sp (sigR cm.sig (v.adicCompletion F) x) = swapR _ (sp x)) → (∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a)) → ∀ (L : Submodule (𝓞 E) (Fin n → E)), SelfDualAt cm.sig J v L → ∀ κ ∈ UPts cm.sig J (v.adicCompletion F), (∀ x : Fin n → v.adicCompletion F, (∃ y ∈ loc v L, ∀ b, (sp (y b)).1 = x b) ↔ ∃ y ∈ loc v L, ∀ b, (sp (y b)).1 = ((bc ((RingHom.fst _ _).comp sp.toRingHom) κ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec x b) → κ ∈ levelVL cm.sig J v L := by
  first | exact @GlobalTheory.St.G.mem_levelVL_of_first_components | exact GlobalTheory.St.G.mem_levelVL_of_first_components | (intros; apply GlobalTheory.St.G.mem_levelVL_of_first_components <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiagonalTorusTransitiveGenericCharacters
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiagonalTorusTransitiveGenericCharacters
open Formalism.L2.Forms hiding dualL
open Formalism.BasicNotions Formalism.UG NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G.Torus

theorem exists_mulShift {k : Type} [Field k] [Finite k] (ψ ψ' : AddChar k ℂ) (h : ψ ≠ 1) (h' : ψ' ≠ 1) :
    ∃ a : k, a ≠ 0 ∧ ψ' = ψ.mulShift a := by
  classical
  haveI : Fintype k := Fintype.ofFinite k
  have hinj : Function.Injective ψ.mulShift :=
    AddChar.to_mulShift_inj_of_isPrimitive (AddChar.IsPrimitive.of_ne_one h)
  have hbij : Function.Bijective ψ.mulShift :=
    (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, by simp⟩
  obtain ⟨a, ha⟩ := hbij.2 ψ'
  refine ⟨a, ?_, ha.symm⟩
  rintro rfl
  exact h' (by rw [← ha, AddChar.mulShift_zero])

theorem conj_apply {k : Type} [Field k] {n : ℕ} (d : Fin n → kˣ) (M : Matrix (Fin n) (Fin n) k) (x y : Fin n) :
    (diagonal (fun i => ((d i)⁻¹ : kˣ).1) * M * diagonal (fun i => (d i).1) : Matrix (Fin n) (Fin n) k) x y
      = (((d x)⁻¹ * d y : kˣ) : k) * M x y := by
  rw [mul_diagonal, diagonal_mul, Units.val_mul]
  ring

private lemma inJ_diagonal_conj_iff {k : Type} [Field k] {n t : ℕ} (d : Fin n → kˣ) (M : Matrix (Fin n) (Fin n) k) :
    InJ n t n false M ↔ InJ n t n false (diagonal (fun i => ((d i)⁻¹ : kˣ).1) * M * diagonal (fun i => (d i).1)) := by
  have hc : ∀ x y : Fin n, (((d x)⁻¹ * d y : kˣ) : k) ≠ 0 := fun x y => Units.ne_zero _
  have h1 : ∀ x : Fin n, (((d x)⁻¹ * d x : kˣ) : k) = 1 := fun x => by
    rw [inv_mul_cancel, Units.val_one]
  simp only [InJ, conj_apply, mul_eq_zero, hc, false_or, Bool.false_eq_true, false_implies, and_true]
  refine and_congr Iff.rfl (and_congr ?_ ?_)
  · refine forall_congr' fun x => imp_congr_right fun _ => ?_
    rw [h1, one_mul]
  · refine forall_congr' fun x => forall_congr' fun y => imp_congr_right fun _ => ?_
    split_ifs with hxy
    · subst hxy
      rw [h1, one_mul]
    · simp [hc]

private lemma inv_pow_mul_pow_succ_eq {k : Type} [Field k] (u : kˣ) (x y : ℕ) (h : x + 1 = y) :
    (((u ^ x)⁻¹ * u ^ y : kˣ) : k) = u := by
  subst h
  rw [pow_succ, ← mul_assoc, inv_mul_cancel, one_mul]

theorem torus_transitive : ∀ (k : Type) [Field k] [Finite k] (n t : ℕ) (ψ ψ' : AddChar k ℂ) (χ χ' : ℕ → MulChar k ℂ), ψ ≠ 1 → ψ' ≠ 1 → ∃ d : Fin n → kˣ, ∀ M : Matrix (Fin n) (Fin n) k, (InJ n t n false M ↔ InJ n t n false (diagonal (fun i => ((d i)⁻¹ : kˣ).1) * M * diagonal (fun i => (d i).1))) ∧ lamJ ψ' χ' n t 0 n M = (lamJ ψ χ n t 0 n (diagonal (fun i => ((d i)⁻¹ : kˣ).1) * M * diagonal (fun i => (d i).1)))⁻¹ := by
  intro k _ _ n t ψ ψ' χ χ' hψ hψ'
  obtain ⟨a, ha, rfl⟩ := exists_mulShift ψ ψ' hψ hψ'
  set u : kˣ := Units.mk0 (-a) (neg_ne_zero.mpr ha) with hu
  refine ⟨fun i => u ^ (i : ℕ), fun M => ⟨inJ_diagonal_conj_iff _ M, ?_⟩⟩
  simp only [lamJ, conj_apply, Finset.prod_range_zero, mul_one, AddChar.mulShift_apply]
  rw [← AddChar.map_neg_eq_inv]
  congr 1
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  split_ifs with hxy
  · rw [inv_pow_mul_pow_succ_eq u _ _ hxy.1, hu, Units.val_mk0]
    ring
  · simp

end GlobalTheory.St.G.Torus
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiagonalTorusTransitiveGenericCharactersStatement
open Formalism.L2.Forms hiding dualL
open Formalism.BasicNotions Formalism.UG NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonal_torus_transitive_generic_characters : ∀ (k : Type) [Field k] [Finite k] (n t : ℕ) (ψ ψ' : AddChar k ℂ) (χ χ' : ℕ → MulChar k ℂ), ψ ≠ 1 → ψ' ≠ 1 → ∃ d : Fin n → kˣ, ∀ M : Matrix (Fin n) (Fin n) k, (InJ n t n false M ↔ InJ n t n false (diagonal (fun i => ((d i)⁻¹ : kˣ).1) * M * diagonal (fun i => (d i).1))) ∧ lamJ ψ' χ' n t 0 n M = (lamJ ψ χ n t 0 n (diagonal (fun i => ((d i)⁻¹ : kˣ).1) * M * diagonal (fun i => (d i).1)))⁻¹ := by
  first | exact @GlobalTheory.St.G.Torus.torus_transitive | exact GlobalTheory.St.G.Torus.torus_transitive | (intros; apply GlobalTheory.St.G.Torus.torus_transitive <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalLevelCharacterMatchAtTypePrime
open Formalism.L2.Forms hiding dualL
open Formalism.BasicNotions Formalism.UG NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G.Match

theorem diag_lift : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (d : Fin n → (kv F v)ˣ), ∃ D : GL (Fin n) (v.adicCompletion F), (∀ x : Fin n → v.adicCompletion F, (∀ b, x b ∈ v.adicCompletionIntegers F) ↔ ∀ b, ((D : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *ᵥ x) b ∈ v.adicCompletionIntegers F) ∧ ∀ M : Matrix (Fin n) (Fin n) (v.adicCompletion F), redM F v (((D⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * M * (D : Matrix (Fin n) (Fin n) (v.adicCompletion F))) = diagonal (fun i => ((d i)⁻¹ : (kv F v)ˣ).1) * redM F v M * diagonal (fun i => ((d i : (kv F v)ˣ) : kv F v)) := by
  intro F _ _ v n d
  have hs := IsLocalRing.residue_surjective (R := v.adicCompletionIntegers F)
  choose u hu using fun i => hs ((d i : (kv F v)ˣ) : kv F v)
  have hunit : ∀ i, IsUnit (u i) := fun i =>
    isUnit_of_map_unit (IsLocalRing.residue (v.adicCompletionIntegers F)) (u i) (by rw [hu i]; exact (d i).isUnit)
  let w : Fin n → (v.adicCompletionIntegers F)ˣ := fun i => (hunit i).unit
  let e : Fin n → (v.adicCompletion F)ˣ := fun i => Units.map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)).toMonoidHom (w i)
  have he : ∀ i, ((e i : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F := fun i => (w i : v.adicCompletionIntegers F).2
  have he' : ∀ i, (((e i)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F := fun i => (((w i)⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F).2
  have hw : ∀ i, IsLocalRing.residue (v.adicCompletionIntegers F) ((w i : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) = ((d i : (kv F v)ˣ) : kv F v) := fun i => hu i
  have hw' : ∀ i, IsLocalRing.residue (v.adicCompletionIntegers F) (((w i)⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) = (((d i)⁻¹ : (kv F v)ˣ) : kv F v) := by
    intro i
    have h1 := congrArg Units.val (map_inv (Units.map (IsLocalRing.residue (v.adicCompletionIntegers F)).toMonoidHom) (w i))
    have h2 : Units.map (IsLocalRing.residue (v.adicCompletionIntegers F)).toMonoidHom (w i) = d i := Units.ext (hw i)
    rw [h2] at h1
    exact h1
  let D : GL (Fin n) (v.adicCompletion F) :=
    ⟨diagonal (fun i => ((e i : (v.adicCompletion F)ˣ) : v.adicCompletion F)),
      diagonal (fun i => (((e i)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)),
      by rw [diagonal_mul_diagonal]; simp, by rw [diagonal_mul_diagonal]; simp⟩
  refine ⟨D, fun x => ?_, fun M => ?_⟩
  · change _ ↔ ∀ b, (diagonal (fun i => ((e i : (v.adicCompletion F)ˣ) : v.adicCompletion F)) *ᵥ x) b ∈ _
    simp only [mulVec_diagonal]
    refine ⟨fun h b => mul_mem (he b) (h b), fun h b => ?_⟩
    have := mul_mem (he' b) (h b)
    rwa [← mul_assoc, Units.inv_mul, one_mul] at this
  · change redM F v (diagonal (fun i => (((e i)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)) * M *
      diagonal (fun i => ((e i : (v.adicCompletion F)ˣ) : v.adicCompletion F))) = _
    ext a b
    have key : (diagonal (fun i => (((e i)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)) * M *
        diagonal (fun i => ((e i : (v.adicCompletion F)ˣ) : v.adicCompletion F))) a b =
        ((((e a)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * M a b) * ((e b : (v.adicCompletion F)ˣ) : v.adicCompletion F) := by
      simp only [diagonal_mul, mul_diagonal]
    simp only [diagonal_mul, mul_diagonal, redM]
    by_cases hM : M a b ∈ v.adicCompletionIntegers F
    · have hP : ((((e a)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * M a b) * ((e b : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F :=
        mul_mem (mul_mem (he' a) hM) (he b)
      rw [dite_eq_left (key ▸ hP), dite_eq_left hM, ← hw' a, ← hw b, ← map_mul, ← map_mul]
      congr 1
    · have hP : ((((e a)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * M a b) * ((e b : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∉ v.adicCompletionIntegers F := by
        intro hP
        apply hM
        have := mul_mem (mul_mem (he a) hP) (he' b)
        have e1 : ((e a : (v.adicCompletion F)ˣ) : v.adicCompletion F) * ((((e a)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * M a b * ((e b : (v.adicCompletion F)ˣ) : v.adicCompletion F)) * (((e b)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) = M a b := by
          simp [mul_assoc]
        rwa [e1] at this
      rw [dite_eq_right (key ▸ hP), dite_eq_right hM]; simp

end GlobalTheory.St.G.Match

namespace GlobalTheory.St.G.Match

theorem nat_prime_not_mem {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (p q : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) (hpv : (p : 𝓞 F) ∈ v.asIdeal) : (q : 𝓞 F) ∉ v.asIdeal := by
  intro hqv
  have hc : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 hne
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hc
  apply v.isPrime.ne_top
  rw [Ideal.eq_top_iff_one]
  have h1 : (a : 𝓞 F) * (p : 𝓞 F) + (b : 𝓞 F) * (q : 𝓞 F) = 1 := by
    have := congrArg (Int.cast : ℤ → 𝓞 F) hab
    push_cast at this; exact this
  rw [← h1]
  exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ hpv) (v.asIdeal.mul_mem_left _ hqv)

end GlobalTheory.St.G.Match

namespace GlobalTheory.St.G

theorem gmatch_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (T f t k a sk fc : ℕ) (gp : Fin 2 → ℕ) (S : StepLevel F E cm.sig J T f {v : HeightOneSpectrum (𝓞 F) | (gp 0 : 𝓞 F) ∈ v.asIdeal ∨ (gp 1 : 𝓞 F) ∈ v.asIdeal}) (G : GLoc F E cm.sig gp) (Gl : GLev S G a t 0 sk fc false), k = n → a = n → sk = n → fc = n → T.Prime → (∀ i, (gp i).Prime) → gp 0 ≠ gp 1 → (∀ i, T ≠ gp i) → (∀ i, SplitsIn E (gp i)) → ∀ (Fr : AdFrame cm.sig J (hat F S.Lb) (gp 0 * gp 1) k) (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (hv : (gp i : 𝓞 F) ∈ v.asIdeal), ∃ κ ∈ levelVL cm.sig J v S.Lb, ∀ y ∈ levelVL cm.sig J v S.Lb, (Fr.LocK S.Lb v y ↔ κ⁻¹ * y * κ ∈ S.Uloc v) ∧ (Fr.LocK S.Lb v y → Fr.locChi v y = (lamJ (G.psi0 i v hv) (G.chiB i v hv) a t 0 sk (redM F v (G.mat i v hv (Gl.fr i v hv) (κ⁻¹ * y * κ))))⁻¹) := by
  intro F E _ _ _ _ _ _ cm n J hJ hdet T f t k a sk fc gp S G Gl hk ha hsk hfc hT hgp hne hTg hspl Fr i v hv
  subst a sk fc
  have hTv : (T : 𝓞 F) ∉ v.asIdeal := fun h =>
    GlobalTheory.St.G.Match.nat_prime_not_mem v (gp i) T (hgp i) hT (fun e => hTg i e.symm) hv h
  have hTL := GlobalTheory.St.G.stepLevel_tLat F E n cm.sig J T f _ S
  have hSD := GlobalTheory.T.isLocallySelfDual_of_hermitianLatticeOfLevel F E cm n J hJ hdet T f S.Lb hTL v hTv
  have hLat : IsLat S.Lb := ⟨S.Lb_fin, S.Lb_span⟩
  obtain ⟨fr', ψ', hψ', hfr', hK⟩ := GlobalTheory.T.adelicLatticeFrame_local_basis_unitriangular F E cm n J hJ hdet k t gp G S.Lb Fr hk hgp hne hspl hLat i v hv hSD
  have hcard := ((GlobalTheory.T.cmField_splitCompletely_place_structure F E cm (gp i) (hgp i) (hspl i)).2 v hv).1
  haveI : Finite (kv F v) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact (hgp i).ne_zero)
  obtain ⟨d, hd⟩ := GlobalTheory.T.diagonal_torus_transitive_generic_characters (kv F v) n t (G.psi0 i v hv) ψ' (G.chiB i v hv) (fun _ => 1) (G.psi_zero_nontrivial_character i v hv) hψ'
  obtain ⟨D, hDint, hDred⟩ := GlobalTheory.St.G.Match.diag_lift F v n d
  obtain ⟨κ, hκ, -⟩ := (GlobalTheory.T.split_place_lattice_components F E cm n J hJ hdet v (G.sp i v hv) (G.sp_sig i v hv) (G.sp_alg i v hv)).2.1
    (fr' * D * (Gl.fr i v hv)⁻¹)
  have hphi : bc (G.phi i v hv) κ.1 = fr' * D * (Gl.fr i v hv)⁻¹ := hκ
  have hlev : κ.1 ∈ levelVL cm.sig J v S.Lb := by
    refine GlobalTheory.T.mem_level_of_preserves_first_components_split F E cm n J v (G.sp i v hv) (G.sp_sig i v hv) (G.sp_alg i v hv) S.Lb hSD κ.1 κ.2 ?_
    intro x
    refine (Gl.fr_lat i v hv x).trans ?_
    refine Iff.trans ?_ (hfr' _).symm
    rw [hDint]
    rw [hκ]
    simp only [Units.val_mul, mulVec_mulVec, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  refine ⟨κ.1, hlev, fun y hy => ?_⟩
  have hyκ : κ.1⁻¹ * y * κ.1 ∈ levelVL cm.sig J v S.Lb := mul_mem (mul_mem (inv_mem hlev) hy) hlev
  have hg : (Gl.fr i v hv)⁻¹ * bc (G.phi i v hv) (κ.1⁻¹ * y * κ.1) * Gl.fr i v hv
      = D⁻¹ * (fr'⁻¹ * bc (G.phi i v hv) y * fr') * D := by
    rw [map_mul, map_mul, map_inv, hphi]; group
  have hred : redM F v (G.mat i v hv (Gl.fr i v hv) (κ.1⁻¹ * y * κ.1)) =
      diagonal (fun j => ((d j)⁻¹ : (kv F v)ˣ).1) * redM F v (G.mat i v hv fr' y) * diagonal (fun j => ((d j : (kv F v)ˣ) : kv F v)) := by
    rw [← hDred]
    unfold GLoc.mat
    rw [hg, Units.val_mul, Units.val_mul]
  obtain ⟨hK1, hK2⟩ := hK y hy
  refine ⟨?_, fun hy' => ?_⟩
  · rw [hK1, (hd _).1, ← hred, Gl.mem i v hv _ hyκ]
  · rw [hK2 hy', (hd _).2, hred]

end GlobalTheory.St.G
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalLevelCharacterMatchAtTypePrimeStatement
open Formalism.L2.Forms hiding dualL
open Formalism.BasicNotions Formalism.UG NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_level_character_match_at_type_prime : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (T f t k a sk fc : ℕ) (gp : Fin 2 → ℕ) (S : StepLevel F E cm.sig J T f {v : HeightOneSpectrum (𝓞 F) | (gp 0 : 𝓞 F) ∈ v.asIdeal ∨ (gp 1 : 𝓞 F) ∈ v.asIdeal}) (G : GLoc F E cm.sig gp) (Gl : GLev S G a t 0 sk fc false), k = n → a = n → sk = n → fc = n → T.Prime → (∀ i, (gp i).Prime) → gp 0 ≠ gp 1 → (∀ i, T ≠ gp i) → (∀ i, SplitsIn E (gp i)) → ∀ (Fr : AdFrame cm.sig J (hat F S.Lb) (gp 0 * gp 1) k) (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (hv : (gp i : 𝓞 F) ∈ v.asIdeal), ∃ κ ∈ levelVL cm.sig J v S.Lb, ∀ y ∈ levelVL cm.sig J v S.Lb, (Fr.LocK S.Lb v y ↔ κ⁻¹ * y * κ ∈ S.Uloc v) ∧ (Fr.LocK S.Lb v y → Fr.locChi v y = (lamJ (G.psi0 i v hv) (G.chiB i v hv) a t 0 sk (redM F v (G.mat i v hv (Gl.fr i v hv) (κ⁻¹ * y * κ))))⁻¹) := by
  first | exact @GlobalTheory.St.G.gmatch_local | exact GlobalTheory.St.G.gmatch_local | (intros; apply GlobalTheory.St.G.gmatch_local <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TrivialOnDualQuotientIffMemLocalUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TrivialOnDualQuotientIffMemLocalUnitary
open Formalism.L2.Forms hiding dualL
open Formalism.BasicNotions Formalism.UG NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G.FunFix

section Abstract

variable {A : Type} [CommRing A] {k : ℕ} (τ : A →+* A) (J : Matrix (Fin k) (Fin k) A)

theorem hform_sub_left (x x' y : Fin k → A) : hform τ J (x - x') y = hform τ J x y - hform τ J x' y := by
  simp only [hform, Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]

theorem hform_sub_right (x y y' : Fin k → A) : hform τ J x (y - y') = hform τ J x y - hform τ J x y' := by
  simp only [hform, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem hform_smul_swap (c : A) (x y : Fin k → A) : hform τ J x (τ c • y) = hform τ J (c • x) y := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, map_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hform_unitary {g : GL (Fin k) A} (hg : g ∈ UJ τ J) (x y : Fin k → A) :
    hform τ J (g.1 *ᵥ x) (g.1 *ᵥ y) = hform τ J x y := by
  have h : cT τ g.1 * J * g.1 = J := hg
  rw [GlobalTheory.DualFrame.hform_mulVec, mulVec_mulVec, h, GlobalTheory.DualFrame.hform_eq_dot]

theorem hform_move {g : GL (Fin k) A} (hg : g ∈ UJ τ J) (x y : Fin k → A) :
    hform τ J x (g.1 *ᵥ y) = hform τ J ((g⁻¹).1 *ᵥ x) y := by
  rw [← hform_unitary τ J hg ((g⁻¹).1 *ᵥ x) y, mulVec_mulVec, Units.mul_inv, one_mulVec]

variable {τ J} {O : Subring A} {L D : Submodule O (Fin k → A)}

theorem stab_dual (hD : ∀ y, y ∈ D ↔ ∀ x ∈ L, hform τ J x y ∈ O) {g : GL (Fin k) A}
    (hg : g ∈ level τ J L) : g ∈ stabGL D := by
  obtain ⟨hu, hs⟩ := hg
  intro y
  rw [hD, hD]
  constructor
  · intro h x hx
    rw [hform_move τ J hu]
    exact h _ (((stabGL L).inv_mem hs x).1 hx)
  · intro h x hx
    rw [← hform_unitary τ J hu]
    exact h _ ((hs x).1 hx)

theorem triv_iff_stabFun (hD : ∀ y, y ∈ D ↔ ∀ x ∈ L, hform τ J x y ∈ O)
    (hL : ∀ y, y ∈ L ↔ ∀ x ∈ D, hform τ J x y ∈ O)
    {M : Type} [AddCommGroup M] [Module O M] (f : D →ₗ[O] M) (hf0 : f ≠ 0)
    (hfL : ∀ x : D, x.1 ∈ L → f x = 0) (e : O) (hτe : τ e = 1 - e) (hact : ∀ m : M, e • m = m)
    (hfield : ∀ a : O, (∃ b : O, b * a * e = e) ∨ ∀ x ∈ D, (e * a) • x ∈ L)
    (d : Fin k → A) (hd : d ∈ D) (hgen : ∀ x ∈ D, ∃ a ∈ O, x - a • d ∈ L)
    {g : GL (Fin k) A} (hg : g ∈ level τ J L) :
    (∀ x ∈ D, (g.1 - 1) *ᵥ x ∈ L) ↔ g ∈ stabFun D f := by
  have hgD := stab_dual hD hg
  have hval : ∀ (x : D) (a : O), x.1 - a.1 • d ∈ L → f x = a • f ⟨d, hd⟩ := by
    intro x a h
    rw [← map_smul, ← sub_eq_zero, ← map_sub]
    exact hfL _ h
  have hfd : f ⟨d, hd⟩ ≠ 0 := by
    intro h
    apply hf0
    ext x
    obtain ⟨a, ha, hx⟩ := hgen x.1 x.2
    rw [hval x ⟨a, ha⟩ hx, h, smul_zero]
    rfl
  have hker : ∀ x : D, f x = 0 → e • x.1 ∈ L := by
    intro x hx0
    obtain ⟨a, ha, hx⟩ := hgen x.1 x.2
    rcases hfield ⟨a, ha⟩ with ⟨b, hb⟩ | h
    · exfalso
      apply hfd
      rw [← hact (f ⟨d, hd⟩), ← hb, mul_smul, hact, mul_smul, ← hval x ⟨a, ha⟩ hx, hx0, smul_zero]
    · have h1 := L.add_mem (L.smul_mem e hx) (h d hd)
      have h2 : e • (x.1 - a • d) + (e * ⟨a, ha⟩) • d = e • x.1 := by
        rw [smul_sub, mul_smul]
        exact sub_add_cancel _ _
      rwa [h2] at h1
  have hhalf : ∀ g' ∈ stabFun D f, ∀ x ∈ D, e • (g'.1 *ᵥ x - x) ∈ L := by
    rintro g' ⟨h1, h2⟩ x hx
    refine hker (⟨g'.1 *ᵥ x, (h1 x).1 hx⟩ - ⟨x, hx⟩) ?_
    rw [map_sub, sub_eq_zero]
    exact h2 ⟨x, hx⟩
  constructor
  · intro h
    refine ⟨hgD, fun x => ?_⟩
    rw [← sub_eq_zero, ← map_sub]
    refine hfL _ ?_
    have := h x.1 x.2
    rwa [sub_mulVec, one_mulVec] at this
  · intro h x hx
    rw [sub_mulVec, one_mulVec]
    have h1 := hhalf g h x hx
    have h2 : τ e • (g.1 *ᵥ x - x) ∈ L := by
      rw [hL]
      intro z hz
      rw [hform_smul_swap, hform_sub_right, hform_move τ J hg.1, ← hform_sub_left, mulVec_smul, ← smul_sub]
      exact (hD x).1 hx _ (hhalf g⁻¹ ((stabFun D f).inv_mem h) z hz)
    have h3 := L.add_mem h1 h2
    have h4 : e • (g.1 *ᵥ x - x) + τ e • (g.1 *ᵥ x - x) = g.1 *ᵥ x - x := by
      rw [hτe, sub_smul, one_smul]
      exact add_sub_cancel _ _
    rwa [h4] at h3

theorem idem_act {R : Type} [Ring R] {G : Type} [AddCommGroup G] [Module R G] {p : ℕ} (hp : p.Prime)
    (hG : Nat.card G = p) {e : R} (he : e * e = e) : (∀ y : G, e • y = 0) ∨ (∀ y : G, e • y = y) := by
  have : Fact p.Prime := ⟨hp⟩
  have := isSimpleAddGroup_of_prime_card hG
  rcases IsSimpleAddGroup.eq_bot_or_eq_top_of_normal (DistribSMul.toAddMonoidHom G e).range inferInstance
    with h | h
  · left
    intro y
    exact AddSubgroup.mem_bot.1 (h ▸ ⟨y, rfl⟩)
  · right
    intro y
    have hy : y ∈ (DistribSMul.toAddMonoidHom G e).range := by rw [h]; exact AddSubgroup.mem_top y
    obtain ⟨z, hz⟩ := AddMonoidHom.mem_range.1 hy
    rw [← hz]
    show e • e • z = e • z
    rw [smul_smul, he]

theorem unit_or_dvd {K : Type} [Field K] (V : ValuationSubring K) (T : ℕ)
    (hmax : IsLocalRing.maximalIdeal V = Ideal.span {(T : V)}) (sp : A ≃+* K × K)
    (hint : ∀ x, x ∈ O ↔ (sp x).1 ∈ V ∧ (sp x).2 ∈ V) (e : O) (he : sp e = (1, 0)) (a : O) :
    (∃ b : O, b * a * e = e) ∨ ∃ c : O, e * a = c * T := by
  have ha := ((hint a).1 a.2).1
  have hm : ∀ c : V, sp.symm (c, 0) ∈ O := fun c => by
    rw [hint, sp.apply_symm_apply]; exact ⟨c.2, zero_mem _⟩
  by_cases hu : IsUnit (⟨_, ha⟩ : V)
  · obtain ⟨b, hb⟩ := hu.exists_left_inv
    have hb' : (b : K) * (sp a).1 = 1 := congrArg Subtype.val hb
    refine Or.inl ⟨⟨_, hm b⟩, Subtype.ext (sp.injective ?_)⟩
    change sp (sp.symm (b, 0) * a * e) = sp e
    rw [map_mul, map_mul, sp.apply_symm_apply, he]
    ext <;> simp [hb']
  · have h1 : (⟨_, ha⟩ : V) ∈ IsLocalRing.maximalIdeal V := hu
    rw [hmax, Ideal.mem_span_singleton'] at h1
    obtain ⟨c, hc⟩ := h1
    have hc' : (c : K) * T = (sp a).1 := by simpa using congrArg Subtype.val hc
    refine Or.inr ⟨⟨_, hm c⟩, Subtype.ext (sp.injective ?_)⟩
    rw [Subring.coe_mul, Subring.coe_mul, Subring.coe_natCast, map_mul, map_mul, sp.apply_symm_apply, he, map_natCast]
    ext <;> simp [hc']

end Abstract

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem sigR_mem (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) :
    ∀ a ∈ intV E v, sigR σ (v.adicCompletion F) a ∈ intV E v := by
  have : intV E v ≤ (intV E v).comap (sigR σ (v.adicCompletion F)) := by
    refine Subring.closure_le.2 ?_
    rintro _ (⟨⟨_, a, rfl⟩, rfl⟩ | ⟨a, rfl⟩)
    · exact Subring.subset_closure (Or.inl ⟨⟨_, (⟨σ a, (a.isIntegral_coe).map (σ.restrictScalars ℤ)⟩ : 𝓞 E), rfl⟩, rfl⟩)
    · show (σ 1) ⊗ₜ[F] (a : v.adicCompletion F) ∈ intV E v
      rw [map_one]
      exact Subring.subset_closure (Or.inr ⟨a, rfl⟩)
  exact this

theorem nsmul_mem_loc (v : HeightOneSpectrum (𝓞 F)) (T : ℕ) (L L' : Submodule (𝓞 E) (Fin n → E))
    (h : ∀ x ∈ L', (T : E) • x ∈ L) : ∀ x ∈ loc v L', (T : intV E v) • x ∈ loc v L := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    refine Submodule.subset_span ⟨_, h y hy, ?_⟩
    funext i
    simp only [Nat.cast_smul_eq_nsmul, Pi.smul_apply, map_nsmul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
  | smul a b _ hb => rw [smul_comm]; exact Submodule.smul_mem _ _ hb

end Local

theorem trivial_iff_mem_Uloc : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (S : StepLevel F E cm.sig J T f bad), T.Prime → SplitsIn E T → Module.finrank ℚ E = 2 * f → ∀ (v : HeightOneSpectrum (𝓞 F)), (T : 𝓞 F) ∈ v.asIdeal → ∀ y ∈ levelVL cm.sig J v S.Lb, (∀ x ∈ loc v (dualL cm.sig J S.Lb), (y.1 - 1) *ᵥ x ∈ loc v S.Lb) ↔ y ∈ S.Uloc v := by
  intro F E _ _ _ _ _ _ cm n J hJ hdet T f bad S hT hsp hdeg v hv y hy
  obtain ⟨-, d, hd, hgen⟩ := GlobalTheory.T.hermitianLattice_level_local_dual_quotient_length_one F E cm n J hJ hdet T f S.Lb hT hsp hdeg
    (stepLevel_tLat F E n cm.sig J T f bad S) v hv
  obtain ⟨-, hmax, sp, hsig, hdiag⟩ := (GlobalTheory.T.cmField_splitCompletely_place_structure F E cm T hT hsp).2 v hv
  have hint : ∀ x, x ∈ intV E v ↔
      (sp x).1 ∈ v.adicCompletionIntegers F ∧ (sp x).2 ∈ v.adicCompletionIntegers F :=
    split_integral_local F E v sp hdiag
  obtain ⟨B, C, hBC, hB, hC⟩ := GlobalTheory.DualFrame.exists_dual_frames F E cm.sig n J (isUnit_iff_ne_zero.2 hdet) S.Lb
    S.Lb_fin S.Lb_span v
  obtain ⟨hD, hL, -⟩ := GlobalTheory.DualFrames.dual_of_dual_frames _ (intV E v) (sigR cm.sig (v.adicCompletion F))
    (fun a => sp.injective (by rw [hsig, hsig]; rfl)) (sigR_mem _ v) n _
    (by ext i j; exact congrArg (inclE (F := F) (v.adicCompletion F)) (congrFun (congrFun hJ i) j))
    B C _ _ hBC hB hC
  have hTD := nsmul_mem_loc v T S.Lb (dualL cm.sig J S.Lb)
    fun x hx => S.Lb_dual x (GlobalTheory.DualFrame.mem_dualSet_of_mem_span _ _ _ hx)
  have key : ∀ (sp' : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F),
      (∀ x, x ∈ intV E v ↔
        (sp' x).1 ∈ v.adicCompletionIntegers F ∧ (sp' x).2 ∈ v.adicCompletionIntegers F) →
      ∀ e : intV E v, sp' e = (1, 0) → sigR cm.sig (v.adicCompletion F) e = 1 - e →
      (∀ m : S.fM v hv, e • m = m) →
      ((∀ x ∈ loc v (dualL cm.sig J S.Lb), (y.1 - 1) *ᵥ x ∈ loc v S.Lb) ↔ y ∈ stabFun _ (S.fT v hv)) := by
    intro sp' hint' e he hτe hact
    refine triv_iff_stabFun hD hL (S.fT v hv) (S.fT_ne v hv) (S.fT_L v hv) e hτe hact (fun a => ?_) d hd hgen hy
    refine (unit_or_dvd _ T hmax sp' hint' e he a).imp id ?_
    rintro ⟨c, hc⟩ x hx
    rw [hc, mul_smul]
    exact Submodule.smul_mem _ _ (hTD x hx)
  have he : sp.symm (1, 0) ∈ intV E v := by
    rw [hint, sp.apply_symm_apply]; exact ⟨one_mem _, zero_mem _⟩
  have hτ : sigR cm.sig (v.adicCompletion F) (sp.symm (1, 0)) = 1 - sp.symm (1, 0) := by
    apply sp.injective
    rw [hsig, map_sub, map_one, sp.apply_symm_apply]
    ext <;> simp [swapR]
  have hee : (⟨_, he⟩ : intV E v) * ⟨_, he⟩ = ⟨_, he⟩ := by
    apply Subtype.ext
    change sp.symm (1, 0) * sp.symm (1, 0) = sp.symm (1, 0)
    rw [← map_mul]
    simp
  rw [S.UlocAlt v hv, Subgroup.mem_inf, and_iff_right hy]
  rcases idem_act hT (S.fM_card v hv) hee with h0 | h1
  · refine key (sp.trans RingEquiv.prodComm) (fun x => (hint x).trans and_comm) (1 - ⟨_, he⟩) ?_ ?_ fun m => ?_
    · change RingEquiv.prodComm (sp (1 - sp.symm (1, 0))) = _
      rw [map_sub sp, map_one, sp.apply_symm_apply]
      ext <;> simp
    · change sigR cm.sig (v.adicCompletion F) (1 - sp.symm (1, 0)) = 1 - (1 - sp.symm (1, 0))
      rw [map_sub, map_one, hτ]
    · rw [sub_smul, one_smul, h0, sub_zero]
  · exact key sp hint ⟨_, he⟩ (sp.apply_symm_apply _) hτ h1

end GlobalTheory.St.G.FunFix
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TrivialOnDualQuotientIffMemLocalUnitaryStatement
open Formalism.L2.Forms hiding dualL
open Formalism.BasicNotions Formalism.UG NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trivial_on_dual_quotient_iff_mem_localUnitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (S : StepLevel F E cm.sig J T f bad), T.Prime → SplitsIn E T → Module.finrank ℚ E = 2 * f → ∀ (v : HeightOneSpectrum (𝓞 F)), (T : 𝓞 F) ∈ v.asIdeal → ∀ y ∈ levelVL cm.sig J v S.Lb, (∀ x ∈ loc v (dualL cm.sig J S.Lb), (y.1 - 1) *ᵥ x ∈ loc v S.Lb) ↔ y ∈ S.Uloc v := by
  first | exact @GlobalTheory.St.G.FunFix.trivial_iff_mem_Uloc | exact GlobalTheory.St.G.FunFix.trivial_iff_mem_Uloc | (intros; apply GlobalTheory.St.G.FunFix.trivial_iff_mem_Uloc <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicFrameLevelConjFormLevelWithCharacters
noncomputable section

open Formalism.L2.Forms hiding dualL
open Formalism.BasicNotions Formalism.UG NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G.LvlZero

section SlopeTestRemainingChoices

variable {F : Type} [Field F] [NumberField F]


omit [NumberField F] in
theorem not_both_mem {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (v : HeightOneSpectrum (𝓞 F))
    (h1 : (p : 𝓞 F) ∈ v.asIdeal) (h2 : (q : 𝓞 F) ∈ v.asIdeal) : False := by
  have hc : IsCoprime (p : ℤ) (q : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hp hq).mpr hpq)
  obtain ⟨a, b, hab⟩ := hc
  have e : (1 : 𝓞 F) = (a : 𝓞 F) * (p : 𝓞 F) + (b : 𝓞 F) * (q : 𝓞 F) := by
    have := congrArg (Int.cast : ℤ → 𝓞 F) hab
    push_cast at this
    exact this.symm
  have h1' : (1 : 𝓞 F) ∈ v.asIdeal := by
    rw [e]
    exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ h1) (v.asIdeal.mul_mem_left _ h2)
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1')

theorem finite_mem {p : ℕ} (hp : p ≠ 0) : {v : HeightOneSpectrum (𝓞 F) | (p : 𝓞 F) ∈ v.asIdeal}.Finite := by
  have hI : Ideal.span {(p : 𝓞 F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp
  refine (Ideal.finite_factors hI).subset ?_
  intro v hv
  simp only [Set.mem_ofPred_eq] at hv ⊢
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

variable {E : Type} [Field E] [NumberField E] [Algebra F E] {n : ℕ}


omit [NumberField E] in
theorem prVec_sub_one_mulVec (v : HeightOneSpectrum (𝓞 F)) (y : GL (Fin n) (E ⊗[F] Ad F))
    (x : Fin n → E ⊗[F] Ad F) :
    prVec v ((y.1 - 1) *ᵥ x) = ((bc (prV (E := E) v) y).1 - 1) *ᵥ prVec v x := by
  rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.one_mulVec,
    ← GlobalTheory.St.G.Carry.prVec_mulVec]
  funext i
  simp only [prVec, Pi.sub_apply, map_sub]

theorem mem_hat_of_loc {L : Submodule (𝓞 E) (Fin n → E)} (hL : IsLat L) (v : HeightOneSpectrum (𝓞 F))
    (x : Fin n → E ⊗[F] v.adicCompletion F) (hx : x ∈ loc v L) :
    (fun i => Formalism.UG.P.afsplitIE v (x i)) ∈ hat F L := by
  rw [GlobalTheory.T.mem_adelicSpanOfLattice_iff_forall_place F E n L hL]
  intro w
  by_cases hw : w = v
  · subst hw; rw [GlobalTheory.St.G.Carry.prVec_single_self]; exact hx
  · rw [GlobalTheory.St.G.Carry.prVec_single_ne v w hw]; exact Submodule.zero_mem _

end SlopeTestRemainingChoices


set_option maxHeartbeats 2000000 in
theorem level_conj_frame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (T f t k a sk fc : ℕ) (gp : Fin 2 → ℕ) (S : StepLevel F E cm.sig J T f {v : HeightOneSpectrum (𝓞 F) | (gp 0 : 𝓞 F) ∈ v.asIdeal ∨ (gp 1 : 𝓞 F) ∈ v.asIdeal}) (G : GLoc F E cm.sig gp) (Gl : GLev S G a t 0 sk fc false), k = n → a = n → sk = n → fc = n → T.Prime → (∀ i, (gp i).Prime) → gp 0 ≠ gp 1 → (∀ i, T ≠ gp i) → (∀ i, SplitsIn E (gp i)) → SplitsIn E T → Module.finrank ℚ E = 2 * f → ∀ (Fr : AdFrame cm.sig J (hat F S.Lb) (gp 0 * gp 1) k), ∃ κ : UPts cm.sig J (Ad F), κ.1 ∈ stabGL (hat F S.Lb) ∧ ∀ y : UPts cm.sig J (Ad F), (Fr.InK y.1 ↔ ((κ⁻¹ * y * κ : UPts cm.sig J (Ad F)) : GL _ _) ∈ S.U) ∧ ∀ hy : ((κ⁻¹ * y * κ : UPts cm.sig J (Ad F)) : GL _ _) ∈ S.U, Fr.chi y.1 = ((S.chi ⟨_, hy⟩ : ℂˣ) : ℂ) := by
  intro F E _ _ _ _ _ _ cm n J hJ hdet T f t k a sk fc gp S G Gl hk ha hsk hfc hT hgp hne hTg hsplit hsplitT hdeg Fr
  classical
  have hL : IsLat S.Lb := ⟨S.Lb_fin, S.Lb_span⟩
  have hTL : TLat cm.sig J T f S.Lb := GlobalTheory.St.G.stepLevel_tLat F E n cm.sig J T f _ S
  have hD := GlobalTheory.T.dual_lattice_local_characterization F E cm n J hJ hdet S.Lb hL
  have hLD : IsLat (dualL cm.sig J S.Lb) := hD.1
  have hsd : ∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∉ v.asIdeal →
      ∀ x, x ∈ loc v (dualL cm.sig J S.Lb) ↔ x ∈ loc v S.Lb := by
    intro v hv x
    rw [hD.2.1 v x]
    exact (GlobalTheory.T.isLocallySelfDual_of_hermitianLatticeOfLevel F E cm n J hJ hdet T f S.Lb hTL v hv x).symm
  have hlevI : ∀ v (g : GL (Fin n) (E ⊗[F] v.adicCompletion F)), g ∈ levelVL cm.sig J v S.Lb ↔
      g ∈ UPts cm.sig J (v.adicCompletion F) ∧ g ∈ stabGL (loc v S.Lb) := fun v g => Iff.rfl
  have hQauto : ∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∉ v.asIdeal →
      ∀ g : GL (Fin n) (E ⊗[F] v.adicCompletion F), g ∈ stabGL (loc v S.Lb) →
      ∀ x ∈ loc v (dualL cm.sig J S.Lb), (g.1 - 1) *ᵥ x ∈ loc v S.Lb := by
    intro v hv g hg x hx
    rw [hsd v hv] at hx
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    exact Submodule.sub_mem _ ((hg x).mp hx) hx

  have gm := fun (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (hv : (gp i : 𝓞 F) ∈ v.asIdeal) =>
    GlobalTheory.T.local_level_character_match_at_type_prime F E cm n J hJ hdet T f t k a sk fc gp S G Gl hk ha hsk hfc hT hgp hne hTg hsplit Fr i v hv
  choose κl hκl hκs using gm
  let hf : ∀ v : HeightOneSpectrum (𝓞 F), GL (Fin n) (E ⊗[F] v.adicCompletion F) := fun v =>
    if h0 : (gp 0 : 𝓞 F) ∈ v.asIdeal then κl 0 v h0
    else if h1 : (gp 1 : 𝓞 F) ∈ v.asIdeal then κl 1 v h1 else 1
  have hf_g : ∀ i v (h : (gp i : 𝓞 F) ∈ v.asIdeal), hf v = κl i v h := by
    intro i v h
    obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    · simp only [hf, dif_pos h]
    · have h0 : (gp 0 : 𝓞 F) ∉ v.asIdeal := fun h0 => not_both_mem (hgp 0) (hgp 1) hne v h0 h
      simp only [hf, dif_neg h0, dif_pos h]
  have hf_one : ∀ v, (gp 0 : 𝓞 F) ∉ v.asIdeal → (gp 1 : 𝓞 F) ∉ v.asIdeal → hf v = 1 := by
    intro v h0 h1
    simp only [hf, dif_neg h0, dif_neg h1]
  have hf_lev : ∀ v, hf v ∈ levelVL cm.sig J v S.Lb := by
    intro v
    by_cases h0 : (gp 0 : 𝓞 F) ∈ v.asIdeal
    · rw [hf_g 0 v h0]; exact hκl 0 v h0
    by_cases h1 : (gp 1 : 𝓞 F) ∈ v.asIdeal
    · rw [hf_g 1 v h1]; exact hκl 1 v h1
    rw [hf_one v h0 h1]; exact Subgroup.one_mem _
  have hfin : {v | hf v ≠ 1}.Finite := by
    refine ((finite_mem (hgp 0).ne_zero).union (finite_mem (hgp 1).ne_zero)).subset ?_
    intro v hv
    by_contra hc
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or] at hc
    exact hv (hf_one v hc.1 hc.2)
  obtain ⟨x0, hx0, hx0v⟩ := GlobalTheory.T.exists_adelic_unitary_of_finite_support F E n cm.sig J hf (fun v => ((hlevI v _).mp (hf_lev v)).1) hfin
  let κ : UPts cm.sig J (Ad F) := ⟨x0, hx0⟩
  have hκv : ∀ v, bc (prV (E := E) v) (κ : GL (Fin n) (E ⊗[F] Ad F)) = hf v := hx0v
  refine ⟨κ, ?_, ?_⟩
  · exact (GlobalTheory.T.adelicLattice_carry_iff_forall_place F E n S.Lb S.Lb hL hL x0).mpr (fun v x => by
      rw [hx0v v]; exact ((hlevI v _).mp (hf_lev v)).2 x)
  intro y
  have hbcUP : ∀ v, bc (prV (E := E) v) (y : GL (Fin n) (E ⊗[F] Ad F)) ∈ UPts cm.sig J (v.adicCompletion F) :=
    fun v => Formalism.UG.P.afsplit_bc_mem cm.sig J v _ y.2
  have hwv : ∀ v, bc (prV (E := E) v) ((κ⁻¹ * y * κ : UPts cm.sig J (Ad F)) : GL (Fin n) (E ⊗[F] Ad F)) =
      (hf v)⁻¹ * bc (prV (E := E) v) (y : GL (Fin n) (E ⊗[F] Ad F)) * hf v := by
    intro v
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hκv]
  have hconj : ∀ v, (hf v)⁻¹ * bc (prV (E := E) v) (y : GL (Fin n) (E ⊗[F] Ad F)) * hf v ∈ levelVL cm.sig J v S.Lb →
      bc (prV (E := E) v) (y : GL (Fin n) (E ⊗[F] Ad F)) ∈ levelVL cm.sig J v S.Lb := by
    intro v h
    have := (levelVL cm.sig J v S.Lb).mul_mem ((levelVL cm.sig J v S.Lb).mul_mem (hf_lev v) h)
      ((levelVL cm.sig J v S.Lb).inv_mem (hf_lev v))
    simpa [mul_assoc] using this

  have hA : (y : GL (Fin n) (E ⊗[F] Ad F)) ∈ stabGL (hat F S.Lb) ↔
      ∀ v, bc (prV (E := E) v) (y : GL (Fin n) (E ⊗[F] Ad F)) ∈ stabGL (loc v S.Lb) :=
    GlobalTheory.T.adelicLattice_carry_iff_forall_place F E n S.Lb S.Lb hL hL y
  have hB : (∀ x, (∀ z ∈ hat F S.Lb, hR cm.sig J (Ad F) z x ∈ OAd F E) → (y.1.1 - 1) *ᵥ x ∈ hat F S.Lb) ↔
      ∀ v, ∀ x ∈ loc v (dualL cm.sig J S.Lb),
        ((bc (prV (E := E) v) (y : GL (Fin n) (E ⊗[F] Ad F))).1 - 1) *ᵥ x ∈ loc v S.Lb := by
    constructor
    · intro h v x hx
      have hx' := mem_hat_of_loc hLD v x hx
      have h1 := h _ ((hD.2.2 _).mp hx')
      rw [GlobalTheory.T.mem_adelicSpanOfLattice_iff_forall_place F E n S.Lb hL] at h1
      have h2 := h1 v
      rwa [prVec_sub_one_mulVec, GlobalTheory.St.G.Carry.prVec_single_self] at h2
    · intro h x hx
      have hx' := (hD.2.2 x).mpr hx
      rw [GlobalTheory.T.mem_adelicSpanOfLattice_iff_forall_place F E n _ hLD] at hx'
      rw [GlobalTheory.T.mem_adelicSpanOfLattice_iff_forall_place F E n S.Lb hL]
      intro v
      rw [prVec_sub_one_mulVec]
      exact h v _ (hx' v)
  have hIL := fun (hs : (y : GL (Fin n) (E ⊗[F] Ad F)) ∈ stabGL (hat F S.Lb)) =>
    GlobalTheory.T.adelicLatticeFrame_condition_character_local F E cm n J hJ hdet k gp S.Lb Fr hgp hne hL S.Lb_int y.1 hs
  have hK : Fr.InK y.1 ↔ ∀ v, bc (prV (E := E) v) (y : GL (Fin n) (E ⊗[F] Ad F)) ∈ stabGL (loc v S.Lb) ∧
      (∀ x ∈ loc v (dualL cm.sig J S.Lb),
        ((bc (prV (E := E) v) (y : GL (Fin n) (E ⊗[F] Ad F))).1 - 1) *ᵥ x ∈ loc v S.Lb) ∧
      ((gp 0 : 𝓞 F) ∈ v.asIdeal ∨ (gp 1 : 𝓞 F) ∈ v.asIdeal →
        Fr.LocK S.Lb v (bc (prV (E := E) v) (y : GL (Fin n) (E ⊗[F] Ad F)))) := by
    unfold AdFrame.InK
    constructor
    · rintro ⟨hs, hq, hc⟩
      have hs' := hA.mp hs
      have hq' := hB.mp hq
      have hc' := (hIL hs).1.mp hc
      intro v
      refine ⟨hs' v, hq' v, ?_⟩
      rintro (h | h)
      · exact hc' 0 v h
      · exact hc' 1 v h
    · intro h
      have hs := hA.mpr (fun v => (h v).1)
      refine ⟨hs, hB.mpr (fun v => (h v).2.1), (hIL hs).1.mpr ?_⟩
      intro i v hv
      refine (h v).2.2 ?_
      obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
      · exact Or.inl hv
      · exact Or.inr hv
  have hloc : ∀ v, bc (prV (E := E) v) ((κ⁻¹ * y * κ : UPts cm.sig J (Ad F)) : GL (Fin n) (E ⊗[F] Ad F)) ∈ S.Uloc v ↔
      (bc (prV (E := E) v) (y : GL (Fin n) (E ⊗[F] Ad F)) ∈ stabGL (loc v S.Lb) ∧
      (∀ x ∈ loc v (dualL cm.sig J S.Lb),
        ((bc (prV (E := E) v) (y : GL (Fin n) (E ⊗[F] Ad F))).1 - 1) *ᵥ x ∈ loc v S.Lb) ∧
      ((gp 0 : 𝓞 F) ∈ v.asIdeal ∨ (gp 1 : 𝓞 F) ∈ v.asIdeal →
        Fr.LocK S.Lb v (bc (prV (E := E) v) (y : GL (Fin n) (E ⊗[F] Ad F))))) := by
    intro v
    rw [hwv v]
    by_cases hb : (gp 0 : 𝓞 F) ∈ v.asIdeal ∨ (gp 1 : 𝓞 F) ∈ v.asIdeal
    · obtain ⟨i, hi⟩ : ∃ i, (gp i : 𝓞 F) ∈ v.asIdeal := hb.elim (fun h => ⟨0, h⟩) (fun h => ⟨1, h⟩)
      have hTv : (T : 𝓞 F) ∉ v.asIdeal := fun hT' => not_both_mem hT (hgp i) (hTg i) v hT' hi
      have sp := hκs i v hi
      rw [← hf_g i v hi] at sp
      constructor
      · intro hu
        have hl := hconj v (S.Uloc_lev v hu)
        have hl' := (hlevI v _).mp hl
        exact ⟨hl'.2, hQauto v hTv _ hl'.2, fun _ => ((sp _ hl).1).mpr hu⟩
      · rintro ⟨hs, -, hkk⟩
        have hl : bc (prV (E := E) v) (y : GL (Fin n) (E ⊗[F] Ad F)) ∈ levelVL cm.sig J v S.Lb :=
          (hlevI v _).mpr ⟨hbcUP v, hs⟩
        exact ((sp _ hl).1).mp (hkk hb)
    · have h0 : (gp 0 : 𝓞 F) ∉ v.asIdeal := fun h => hb (Or.inl h)
      have h1 : (gp 1 : 𝓞 F) ∉ v.asIdeal := fun h => hb (Or.inr h)
      rw [hf_one v h0 h1, inv_one, one_mul, mul_one]
      by_cases hTv : (T : 𝓞 F) ∈ v.asIdeal
      · have fu := GlobalTheory.T.trivial_on_dual_quotient_iff_mem_localUnitary F E cm n J hJ hdet T f _ S hT hsplitT hdeg v hTv
        constructor
        · intro hu
          have hl := S.Uloc_lev v hu
          exact ⟨((hlevI v _).mp hl).2, (fu _ hl).mpr hu, fun h => absurd h hb⟩
        · rintro ⟨hs, hq, -⟩
          have hl : bc (prV (E := E) v) (y : GL (Fin n) (E ⊗[F] Ad F)) ∈ levelVL cm.sig J v S.Lb :=
            (hlevI v _).mpr ⟨hbcUP v, hs⟩
          exact (fu _ hl).mp hq
      · rw [S.Uloc_hyp v hb hTv]
        constructor
        · intro hl
          have hl' := (hlevI v _).mp hl
          exact ⟨hl'.2, hQauto v hTv _ hl'.2, fun h => absurd h hb⟩
        · rintro ⟨hs, -, -⟩
          exact (hlevI v _).mpr ⟨hbcUP v, hs⟩
  have hU : ((κ⁻¹ * y * κ : UPts cm.sig J (Ad F)) : GL (Fin n) (E ⊗[F] Ad F)) ∈ S.U ↔
      ∀ v, bc (prV (E := E) v) (y : GL (Fin n) (E ⊗[F] Ad F)) ∈ stabGL (loc v S.Lb) ∧
      (∀ x ∈ loc v (dualL cm.sig J S.Lb),
        ((bc (prV (E := E) v) (y : GL (Fin n) (E ⊗[F] Ad F))).1 - 1) *ᵥ x ∈ loc v S.Lb) ∧
      ((gp 0 : 𝓞 F) ∈ v.asIdeal ∨ (gp 1 : 𝓞 F) ∈ v.asIdeal →
        Fr.LocK S.Lb v (bc (prV (E := E) v) (y : GL (Fin n) (E ⊗[F] Ad F)))) := by
    rw [S.U_eq]
    constructor
    · rintro ⟨-, h⟩ v
      exact (hloc v).mp (h v)
    · intro h
      exact ⟨(κ⁻¹ * y * κ).2, fun v => (hloc v).mpr (h v)⟩
  refine ⟨hK.trans hU.symm, ?_⟩
  intro hy
  have hall := hU.mp hy
  have hs : (y : GL (Fin n) (E ⊗[F] Ad F)) ∈ stabGL (hat F S.Lb) := hA.mpr (fun v => (hall v).1)
  rw [(hIL hs).2, Gl.chi_eq ⟨_, hy⟩]
  refine Finset.prod_congr rfl (fun i _ => finprod_congr (fun v => finprod_congr (fun h => ?_)))
  have hb : (gp 0 : 𝓞 F) ∈ v.asIdeal ∨ (gp 1 : 𝓞 F) ∈ v.asIdeal := by
    obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    · exact Or.inl h
    · exact Or.inr h
  have hl : bc (prV (E := E) v) (y : GL (Fin n) (E ⊗[F] Ad F)) ∈ levelVL cm.sig J v S.Lb :=
    (hlevI v _).mpr ⟨hbcUP v, (hall v).1⟩
  rw [(hκs i v h _ hl).2 ((hall v).2.2 hb)]
  dsimp only
  rw [hwv v, hf_g i v h]

end GlobalTheory.St.G.LvlZero
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicFrameLevelConjFormLevelWithCharactersStatement
open Formalism.L2.Forms hiding dualL
open Formalism.BasicNotions Formalism.UG NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicFrameLevel_conj_formLevel_with_characters : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (T f t k a sk fc : ℕ) (gp : Fin 2 → ℕ) (S : StepLevel F E cm.sig J T f {v : HeightOneSpectrum (𝓞 F) | (gp 0 : 𝓞 F) ∈ v.asIdeal ∨ (gp 1 : 𝓞 F) ∈ v.asIdeal}) (G : GLoc F E cm.sig gp) (Gl : GLev S G a t 0 sk fc false), k = n → a = n → sk = n → fc = n → T.Prime → (∀ i, (gp i).Prime) → gp 0 ≠ gp 1 → (∀ i, T ≠ gp i) → (∀ i, SplitsIn E (gp i)) → SplitsIn E T → Module.finrank ℚ E = 2 * f → ∀ (Fr : AdFrame cm.sig J (hat F S.Lb) (gp 0 * gp 1) k), ∃ κ : UPts cm.sig J (Ad F), κ.1 ∈ stabGL (hat F S.Lb) ∧ ∀ y : UPts cm.sig J (Ad F), (Fr.InK y.1 ↔ ((κ⁻¹ * y * κ : UPts cm.sig J (Ad F)) : GL _ _) ∈ S.U) ∧ ∀ hy : ((κ⁻¹ * y * κ : UPts cm.sig J (Ad F)) : GL _ _) ∈ S.U, Fr.chi y.1 = ((S.chi ⟨_, hy⟩ : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.St.G.LvlZero.level_conj_frame | exact GlobalTheory.St.G.LvlZero.level_conj_frame | (intros; apply GlobalTheory.St.G.LvlZero.level_conj_frame <;> assumption)
end
