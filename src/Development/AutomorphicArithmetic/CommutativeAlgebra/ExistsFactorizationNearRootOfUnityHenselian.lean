module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.GoodRoot
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsZeroOfLinearFormJacobianHenselian
section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsCommonZeroOfJacobianIsUnitHenselian
section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsSectionLiftOfEtaleOfHenselian
noncomputable section
open IsLocalRing UpperTheory.Et

theorem UpperTheory.exists_section_lift_of_etale_of_henselian :
    ∀ (A E : Type) [CommRing A] [HenselianLocalRing A] [CommRing E] [Algebra A E] [Algebra.Etale A E] (π : E →ₐ[A] ResidueField A), ∃ σ : E →ₐ[A] A, ∀ x, residue A (σ x) = π x := by
  intro A E _ _ _ _ _ π
  classical
  let Q : Ideal E := RingHom.ker π
  haveI : Q.IsPrime := RingHom.ker_isPrime π
  obtain ⟨f, hfQ, hstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := A) Q
  obtain ⟨P⟩ := hstd.nonempty_standardEtalePresentation
  have hunit : ∀ y : Submonoid.powers f, IsUnit (π y) := by
    rintro ⟨_, n, rfl⟩
    simp only [map_pow]
    exact (isUnit_iff_ne_zero.mpr fun h => hfQ (RingHom.mem_ker.mpr h)).pow n
  let πf : Localization.Away f →ₐ[A] ResidueField A := IsLocalization.liftAlgHom (M := Submonoid.powers f) hunit
  let ι : E →ₐ[A] Localization.Away f := IsScalarTower.toAlgHom A E _
  have hπ : ∀ x, πf (ι x) = π x := fun x => by
    simp [πf, ι]
  let τ : P.Ring →ₐ[A] ResidueField A := πf.comp P.equivRing.symm.toAlgHom
  have hx : P.HasMap (τ P.X) := StandardEtalePair.hasMap_X.map τ
  have key : ∀ b : A, residue A b = τ P.X → ∀ p : Polynomial A, residue A (p.eval b) = Polynomial.aeval (τ P.X) p := by
    intro b hb p
    rw [← hb, ← ResidueField.algebraMap_eq, Polynomial.aeval_algebraMap_apply, Polynomial.coe_aeval_eq_eval]
  obtain ⟨a₀, ha₀⟩ := IsLocalRing.residue_surjective (τ P.X)
  have h1 : P.f.eval a₀ ∈ maximalIdeal A := by
    rw [← IsLocalRing.residue_eq_zero_iff, key a₀ ha₀]
    exact hx.1
  have h2 : IsUnit (P.f.derivative.eval a₀) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, key a₀ ha₀]
    exact hx.isUnit_derivative_f.ne_zero
  obtain ⟨a, ha, ham⟩ := HenselianLocalRing.is_henselian P.f P.monic_f a₀ h1 h2
  have hra : residue A a = τ P.X := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero] at ham
    rw [ham, ha₀]
  have hA : P.HasMap a := by
    refine ⟨by rw [Polynomial.coe_aeval_eq_eval]; exact ha, ?_⟩
    rw [Polynomial.coe_aeval_eq_eval, ← IsLocalRing.residue_ne_zero_iff_isUnit, key a hra]
    exact hx.2.ne_zero
  let ρ : A →ₐ[A] ResidueField A := IsScalarTower.toAlgHom A A (ResidueField A)
  have hρ : ρ.comp (P.lift a hA) = τ := by
    apply StandardEtalePair.hom_ext
    simp [ρ, hra, ResidueField.algebraMap_eq]
  refine ⟨(P.lift a hA).comp (P.equivRing.toAlgHom.comp ι), fun x => ?_⟩
  have := congrArg (fun φ => φ (P.equivRing (ι x))) hρ
  simp only [AlgHom.comp_apply, ρ, IsScalarTower.coe_toAlgHom', ResidueField.algebraMap_eq, τ, AlgEquiv.coe_toAlgHom, AlgHom.coe_coe, AlgEquiv.symm_apply_apply] at this
  simpa [hπ] using this

end
end

noncomputable section
open IsLocalRing UpperTheory.Et

private theorem etale_away_jacobian (A : Type) [CommRing A] (n : ℕ)
    (F : Fin n → MvPolynomial (Fin n) A) :
    Algebra.Etale A (Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range F))
      (Matrix.of fun s t : Fin n => MvPolynomial.pderiv s (F t)).det)) := by
  classical
  let I := Ideal.span (Set.range F)
  let d := Ideal.Quotient.mk I (Matrix.of fun s t : Fin n => MvPolynomial.pderiv s (F t)).det
  let P1 := Algebra.PreSubmersivePresentation.naive (v := F) (id : Fin n → Fin n)
    Function.injective_id
  let P2 := Algebra.PreSubmersivePresentation.localizationAway (Localization.Away d) d
  have hJ : P1.jacobian = d := by
    rw [P1.jacobian_eq_jacobiMatrix_det]
    have hM : P1.jacobiMatrix = Matrix.of fun s t : Fin n => MvPolynomial.pderiv s (F t) := by
      ext i j
      simp [P1]
    rw [hM, Algebra.Generators.algebraMap_apply]
    have hE : MvPolynomial.aeval P1.val = Ideal.Quotient.mkₐ A I :=
      MvPolynomial.algHom_ext fun i => by simp [P1, I, Algebra.Generators.naive]
    exact congrFun (congrArg DFunLike.coe hE) _
  let P : Algebra.SubmersivePresentation A (Localization.Away d) (Unit ⊕ Fin n) (Unit ⊕ Fin n) :=
    { P2.comp P1 with
      jacobian_isUnit := by
        rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
          Algebra.smul_def, Algebra.PreSubmersivePresentation.localizationAway_jacobian, hJ]
        exact (IsLocalization.Away.algebraMap_isUnit d).mul
          (IsLocalization.Away.algebraMap_isUnit d) }
  have : Algebra.IsStandardSmoothOfRelativeDimension 0 A (Localization.Away d) :=
    P.isStandardSmoothOfRelativeDimension (by simp [Algebra.Presentation.dimension])
  infer_instance

theorem UpperTheory.exists_common_zero_of_jacobian_isUnit_henselian :
    ∀ (A : Type) [CommRing A] [HenselianLocalRing A] (n : ℕ) (F : Fin n → MvPolynomial (Fin n) A),
      (∀ i, MvPolynomial.eval 0 (F i) ∈ maximalIdeal A) → IsUnit (Matrix.det (Matrix.of fun i j => MvPolynomial.eval 0 (MvPolynomial.pderiv j (F i)))) →
      ∃ x : Fin n → A, (∀ i, MvPolynomial.eval x (F i) = 0) ∧ ∀ j, x j ∈ maximalIdeal A := by
  intro A _ _ n F hF hU
  classical
  let I := Ideal.span (Set.range F)
  let d := Ideal.Quotient.mk I (Matrix.of fun s t : Fin n => MvPolynomial.pderiv s (F t)).det
  haveI := etale_away_jacobian A n F
  let ψ : MvPolynomial (Fin n) A →ₐ[A] ResidueField A :=
    (Algebra.ofId A (ResidueField A)).comp (MvPolynomial.aeval (0 : Fin n → A))
  have hψ : ∀ p, ψ p = residue A (MvPolynomial.eval 0 p) := fun p => by
    simp [ψ, MvPolynomial.coe_aeval_eq_eval, IsLocalRing.ResidueField.algebraMap_eq]
  have hI : ∀ a ∈ I, ψ a = 0 := by
    intro a ha
    have hle : I ≤ RingHom.ker ψ := by
      refine Ideal.span_le.2 ?_
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, hψ, residue_eq_zero_iff]
      exact hF i
    exact hle ha
  let π0 : (MvPolynomial (Fin n) A ⧸ I) →ₐ[A] ResidueField A := Ideal.Quotient.liftₐ I ψ hI
  have hπ0 : ∀ p, π0 (Ideal.Quotient.mk I p) = residue A (MvPolynomial.eval 0 p) := fun p => by
    rw [← hψ]
    rfl
  have hd : IsUnit (π0 d) := by
    rw [hπ0]
    have hdet : MvPolynomial.eval 0 (Matrix.of fun s t : Fin n => MvPolynomial.pderiv s (F t)).det =
        (Matrix.of fun i j => MvPolynomial.eval 0 (MvPolynomial.pderiv j (F i))).det := by
      rw [RingHom.map_det, ← Matrix.det_transpose]
      congr 1
    rw [hdet]
    exact hU.map (residue A)
  let π : Localization.Away d →ₐ[A] ResidueField A :=
    IsLocalization.liftAlgHom (M := Submonoid.powers d) (f := π0) (by
      rintro ⟨y, k, rfl⟩
      simpa using hd.pow k)
  obtain ⟨σ, hσ⟩ := UpperTheory.exists_section_lift_of_etale_of_henselian A (Localization.Away d) π
  let φ : MvPolynomial (Fin n) A →ₐ[A] A :=
    (σ.comp (IsScalarTower.toAlgHom A _ (Localization.Away d))).comp (Ideal.Quotient.mkₐ A I)
  have hφ : ∀ p, φ p = MvPolynomial.eval (fun j => φ (MvPolynomial.X j)) p := by
    intro p
    rw [← MvPolynomial.coe_aeval_eq_eval]
    exact congrFun (congrArg DFunLike.coe
      (MvPolynomial.algHom_ext (fun j => by simp) : φ = MvPolynomial.aeval _)) p
  refine ⟨fun j => φ (MvPolynomial.X j), fun i => ?_, fun j => ?_⟩
  · rw [← hφ]
    have h0 : Ideal.Quotient.mk I (F i) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨i, rfl⟩)
    simp [φ, h0]
  · rw [← residue_eq_zero_iff]
    show residue A (σ (algebraMap _ (Localization.Away d)
      (Ideal.Quotient.mk I (MvPolynomial.X j)))) = 0
    rw [hσ]
    simp [π, hπ0]

end
end

noncomputable section
open IsLocalRing UpperTheory.Et

private lemma UpperTheory.eval_zero_pderiv {R : Type} [CommRing R] {n : ℕ} (j : Fin n)
    (P : MvPolynomial (Fin n) R) :
    MvPolynomial.eval 0 (MvPolynomial.pderiv j P) = AddMonoidAlgebra.coeff P (Finsupp.single j 1) := by
  rw [MvPolynomial.eval_zero, MvPolynomial.constantCoeff_eq]
  induction P using MvPolynomial.induction_on' with
  | monomial s a =>
    rw [MvPolynomial.pderiv_monomial, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
    by_cases hs : s = Finsupp.single j 1
    · subst hs
      simp
    · rw [if_neg hs]
      split_ifs with h
      · by_cases hsj : s j = 0
        · simp [hsj]
        · exfalso
          apply hs
          ext k
          have hk := DFunLike.congr_fun h k
          by_cases hkj : k = j
          · subst hkj
            simp at hk ⊢
            omega
          · simp [Finsupp.single_apply, hkj, Ne.symm hkj] at hk ⊢
            exact hk
      · rfl
  | add p q hp hq =>
    rw [map_add (f := _), MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq]

theorem UpperTheory.exists_zero_of_linear_form_jacobian_henselian :
    ∀ (A E : Type) [CommRing A] [HenselianLocalRing A] [CommRing E] [Algebra A E] (n : ℕ) (Φ : MvPolynomial (Fin n) E) (L : E →ₗ[A] (Fin n → A)),
      (∀ i, L (MvPolynomial.eval 0 Φ) i ∈ maximalIdeal A) →
      (∀ i j, L (MvPolynomial.eval 0 (MvPolynomial.pderiv j Φ)) i - (if i = j then 1 else 0) ∈ maximalIdeal A) →
      ∃ x : Fin n → A, (∀ j, x j ∈ maximalIdeal A) ∧ L (MvPolynomial.eval (fun j => algebraMap A E (x j)) Φ) = 0 := by
  intro A E _ _ _ _ n Φ L h0 h1
  let G : Fin n → MvPolynomial (Fin n) E → MvPolynomial (Fin n) A := fun i P =>
    ∑ d ∈ P.support, MvPolynomial.monomial d (L (AddMonoidAlgebra.coeff P d) i)
  have hG : ∀ i d P, AddMonoidAlgebra.coeff (G i P) d = L (AddMonoidAlgebra.coeff P d) i := by
    intro i d P
    simp only [G, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · simp only [MvPolynomial.mem_support_iff, not_not] at h
      simp [h]
  have hGadd : ∀ i p q, G i (p + q) = G i p + G i q := by
    intro i p q
    ext d
    rw [MvPolynomial.coeff_add, hG, hG, hG, MvPolynomial.coeff_add, map_add (f := _), Pi.add_apply]
  have key : ∀ i (x : Fin n → A) (P : MvPolynomial (Fin n) E),
      MvPolynomial.eval x (G i P) = L (MvPolynomial.eval (fun j => algebraMap A E (x j)) P) i := by
    intro i x P
    induction P using MvPolynomial.induction_on' with
    | monomial d c =>
      have hm : G i (MvPolynomial.monomial d c) = MvPolynomial.monomial d (L c i) := by
        ext d'
        rw [hG, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
        split_ifs <;> simp
      rw [hm, MvPolynomial.eval_monomial, MvPolynomial.eval_monomial]
      have hp : (d.prod fun k e => (algebraMap A E (x k)) ^ e) = algebraMap A E (d.prod fun k e => x k ^ e) := by
        simp [Finsupp.prod, map_prod, map_pow]
      rw [hp, ← Algebra.commutes, ← Algebra.smul_def, map_smul]
      simp [mul_comm]
    | add p q hp hq =>
      rw [hGadd, map_add (f := _), map_add (f := _), map_add (f := _), Pi.add_apply, hp, hq]
  let F : Fin n → MvPolynomial (Fin n) A := fun i => G i Φ
  have hF0 : ∀ i, MvPolynomial.eval 0 (F i) ∈ maximalIdeal A := by
    intro i
    have h := key i 0 Φ
    have e : (fun j => algebraMap A E ((0 : Fin n → A) j)) = 0 := by
      ext
      simp
    rw [e] at h
    show MvPolynomial.eval 0 (G i Φ) ∈ maximalIdeal A
    rw [h]
    exact h0 i
  have hF1 : ∀ i j, MvPolynomial.eval 0 (MvPolynomial.pderiv j (F i)) =
      L (MvPolynomial.eval 0 (MvPolynomial.pderiv j Φ)) i := by
    intro i j
    rw [UpperTheory.eval_zero_pderiv, UpperTheory.eval_zero_pderiv]
    exact hG i _ Φ
  have hdet : IsUnit (Matrix.of fun i j => MvPolynomial.eval 0 (MvPolynomial.pderiv j (F i))).det := by
    have hM : (residue A).mapMatrix (Matrix.of fun i j => MvPolynomial.eval 0 (MvPolynomial.pderiv j (F i))) = 1 := by
      ext i j
      have h := (residue_eq_zero_iff _).mpr (h1 i j)
      rw [map_sub, sub_eq_zero] at h
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, hF1, h, Matrix.one_apply]
      split_ifs <;> simp
    by_contra hu
    have hm := (mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hu)
    have h := (residue_eq_zero_iff _).mpr hm
    rw [RingHom.map_det, hM, Matrix.det_one] at h
    exact one_ne_zero h
  obtain ⟨x, hx, hxm⟩ := UpperTheory.exists_common_zero_of_jacobian_isUnit_henselian A n F hF0 hdet
  refine ⟨x, hxm, ?_⟩
  funext i
  rw [← key i x Φ]
  exact hx i

end
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsPowerDecompositionOfRootOfUnity
noncomputable section
open IsLocalRing UpperTheory.Et

namespace UpperTheory.LineDecomposition

variable {A D : Type} [CommRing A] [CommRing D] [Algebra A D]

private lemma tsPow (T : TC A D) (i : ℕ) : T.t ^ i * T.s ^ i = 1 := by
  rw [← mul_pow, T.ts, one_pow]

private lemma memS (T : TC A D) {j : ℕ} {x : D} : x ∈ T.S j ↔ x ∈ T.B ∧ T.s ^ j * x ∈ T.C :=
  Iff.rfl

private lemma evB (T : TC A D) (x : D) : ∃ k : ℕ, ∀ m ≥ k, T.t ^ m * x ∈ T.B := by
  obtain ⟨k, hk⟩ := T.locB x
  refine ⟨k, fun m hm => ?_⟩
  have e : T.t ^ m * x = T.t ^ (m - k) * (T.t ^ k * x) := by
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hm]
  rw [e]
  exact T.B.mul_mem (T.B.pow_mem T.tB _) hk

private lemma evC (T : TC A D) (x : D) : ∃ k : ℕ, ∀ m ≥ k, T.s ^ m * x ∈ T.C := by
  obtain ⟨k, hk⟩ := T.locC x
  refine ⟨k, fun m hm => ?_⟩
  have e : T.s ^ m * x = T.s ^ (m - k) * (T.s ^ k * x) := by
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hm]
  rw [e]
  exact T.C.mul_mem (T.C.pow_mem T.sC _) hk

private lemma evCfin (T : TC A D) (F : Finset D) :
    ∃ k : ℕ, ∀ m ≥ k, ∀ z ∈ F, T.s ^ m * z ∈ T.C := by
  choose k hk using fun z => evC T z
  exact ⟨F.sup k, fun m hm z hz => hk z m (le_trans (Finset.le_sup hz) hm)⟩

private def NN (T : TC A D) (X : Finset D) : Submodule A D :=
  Submodule.span A {y | ∃ x ∈ X, ∃ j : ℕ, y = T.s ^ j * x}

private lemma NN_mul (T : TC A D) (X : Finset D) {u : D} (hu : ∀ x ∈ X, u * x ∈ T.C)
    {n : D} (hn : n ∈ NN T X) : u * n ∈ T.C := by
  unfold NN at hn
  induction hn using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, j, rfl⟩ := hy
    have h := T.C.mul_mem (T.C.pow_mem T.sC j) (hu x hx)
    convert h using 1
    ring
  | zero =>
    rw [mul_zero]
    exact T.C.zero_mem
  | add y z _ _ hy hz =>
    rw [mul_add]
    exact T.C.add_mem hy hz
  | smul a y _ hy =>
    rw [mul_smul_comm]
    exact T.C.smul_mem hy a

private lemma split (T : TC A D) (X : Finset D) (hXB : ∀ x ∈ X, x ∈ T.B)
    (hX : ∀ b ∈ T.B, b ∈ Submodule.span A {y | ∃ x ∈ X, ∃ i : ℕ, y = T.t ^ i * x})
    (y : D) : ∃ b ∈ T.B, ∃ n ∈ NN T X, y = b + n := by
  obtain ⟨k, hk⟩ := T.locB y
  have key : ∀ z ∈ Submodule.span A {y | ∃ x ∈ X, ∃ i : ℕ, y = T.t ^ i * x},
      T.s ^ k * z ∈ Subalgebra.toSubmodule T.B ⊔ NN T X := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨x, hx, i, rfl⟩ := hw
      rcases le_or_gt k i with hki | hki
      · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hki
        apply Submodule.mem_sup_left
        have e : T.s ^ k * (T.t ^ (k + d) * x) = T.t ^ d * x := by
          linear_combination (T.t ^ d * x) * tsPow T k
        rw [e]
        exact T.B.mul_mem (T.B.pow_mem T.tB d) (hXB x hx)
      · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hki
        apply Submodule.mem_sup_right
        have e : T.s ^ (i + d + 1) * (T.t ^ i * x) = T.s ^ (d + 1) * x := by
          linear_combination (T.s ^ (d + 1) * x) * tsPow T i
        rw [e]
        exact Submodule.subset_span ⟨x, hx, d + 1, rfl⟩
    | zero =>
      rw [mul_zero]
      exact Submodule.zero_mem _
    | add a b _ _ ha hb =>
      rw [mul_add]
      exact Submodule.add_mem _ ha hb
    | smul r a _ ha =>
      rw [mul_smul_comm]
      exact Submodule.smul_mem _ r ha
  have hy := key _ (hX _ hk)
  have e : T.s ^ k * (T.t ^ k * y) = y := by
    linear_combination y * tsPow T k
  rw [e] at hy
  obtain ⟨b, hb, n, hn, hbn⟩ := Submodule.mem_sup.mp hy
  exact ⟨b, hb, n, hn, hbn.symm⟩

private lemma decomp (T : TC A D) (X : Finset D) (hXB : ∀ x ∈ X, x ∈ T.B)
    (hX : ∀ b ∈ T.B, b ∈ Submodule.span A {y | ∃ x ∈ X, ∃ i : ℕ, y = T.t ^ i * x})
    {ω η : D} (hηω : η * ω = 1) {m : ℕ} (h1 : ω * T.t ^ m ∈ T.B)
    (h3 : ∀ x ∈ X, ω * T.s ^ m * x ∈ T.C) (h4 : ∀ x ∈ X, η * T.s ^ m * x ∈ T.C) (y : D) :
    ∃ b ∈ T.B, ∃ c' ∈ T.C, ∃ p' : D, y = b + c' + p' ∧ ω * T.t ^ m * p' ∈ T.B ∧
      ω * T.s ^ m * p' ∈ T.C := by
  obtain ⟨b₀, hb₀, n₀, hn₀, hz⟩ := split T X hXB hX (ω * T.t ^ m * y)
  obtain ⟨b₂, hb₂, n₂, hn₂, hq⟩ := split T X hXB hX (η * T.s ^ m * b₀)
  have hts := tsPow T m
  refine ⟨b₂, hb₂, η * T.s ^ m * n₀, NN_mul T X h4 hn₀, n₂, ?_, ?_, NN_mul T X h3 hn₂⟩
  · linear_combination hq + η * T.s ^ m * hz - T.t ^ m * T.s ^ m * y * hηω - y * hts
  · have e : ω * T.t ^ m * n₂ = b₀ - ω * T.t ^ m * b₂ := by
      linear_combination (-(ω * T.t ^ m)) * hq + b₀ * T.t ^ m * T.s ^ m * hηω + b₀ * hts
    rw [e]
    exact T.B.sub_mem hb₀ (T.B.mul_mem h1 hb₂)

end UpperTheory.LineDecomposition

open UpperTheory.LineDecomposition in
theorem UpperTheory.exists_power_decomposition_of_root_of_unity :
    ∀ (A D : Type) [CommRing A] [CommRing D] [Algebra A D] (T : TC A D), T.Fin → ∀ (q : ℕ), IsUnit (q : A) → 0 < q → ∀ ω : D, ω ^ q = 1 → ∃ m₀ : ℕ, ∀ m ≥ m₀, ω * T.t ^ m ∈ T.S (2 * m) ∧
      ∀ σ ∈ T.S (2 * q * m), ∃ a ∈ T.S (q * m), ∃ b ∈ T.S (q * m), ∃ c ∈ T.S (2 * m), σ = a + T.t ^ (q * m) * b - (q : D) * (ω * T.t ^ m) ^ (q - 1) * c := by
  classical
  intro A D _ _ _ T hF q hq hq0 ω hω
  obtain ⟨X, hXB, hX⟩ := hF
  have hηω : ω ^ (q - 1) * ω = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel hq0, hω]
  obtain ⟨k₁, hk₁⟩ := evB T ω
  obtain ⟨k₂, hk₂⟩ := evC T ω
  obtain ⟨k₃, hk₃⟩ := evCfin T (X.image (fun x => ω * x))
  obtain ⟨k₄, hk₄⟩ := evCfin T (X.image (fun x => ω ^ (q - 1) * x))
  obtain ⟨r, hr⟩ := hq.exists_left_inv
  refine ⟨max (max k₁ k₂) (max k₃ k₄), fun m hm => ?_⟩
  have hm₁ : k₁ ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hm
  have hm₂ : k₂ ≤ m := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hm
  have hm₃ : k₃ ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hm
  have hm₄ : k₄ ≤ m := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hm
  have hB : ω * T.t ^ m ∈ T.B := by
    rw [mul_comm]
    exact hk₁ m hm₁
  have hC : ω * T.s ^ m ∈ T.C := by
    rw [mul_comm]
    exact hk₂ m hm₂
  have h3 : ∀ x ∈ X, ω * T.s ^ m * x ∈ T.C := fun x hx => by
    have h := hk₃ m hm₃ (ω * x) (Finset.mem_image_of_mem _ hx)
    convert h using 1
    ring
  have h4 : ∀ x ∈ X, ω ^ (q - 1) * T.s ^ m * x ∈ T.C := fun x hx => by
    have h := hk₄ m hm₄ (ω ^ (q - 1) * x) (Finset.mem_image_of_mem _ hx)
    convert h using 1
    ring
  have hts := tsPow T m
  have hu : ω * T.t ^ m ∈ T.S (2 * m) := by
    rw [memS]
    refine ⟨hB, ?_⟩
    have e : T.s ^ (2 * m) * (ω * T.t ^ m) = ω * T.s ^ m := by
      rw [two_mul, pow_add]
      linear_combination ω * T.s ^ m * hts
    rw [e]
    exact hC
  refine ⟨hu, fun σ hσ => ?_⟩
  rw [memS] at hσ
  obtain ⟨b₁, hb₁, c₁, hc₁, p₁, hy, hp1, hp2⟩ :=
    decomp T X hXB hX hηω hB h3 h4 (T.s ^ (q * m) * σ)
  have hqm := tsPow T (q * m)
  have hupow : (ω * T.t ^ m) ^ q = T.t ^ (q * m) := by
    rw [mul_pow, hω, one_mul, ← pow_mul, Nat.mul_comm]
  have hspow : (ω * T.s ^ m) ^ q = T.s ^ (q * m) := by
    rw [mul_pow, hω, one_mul, ← pow_mul, Nat.mul_comm]
  have hup : (ω * T.t ^ m) ^ (q - 1) * (ω * T.t ^ m * p₁) = T.t ^ (q * m) * p₁ := by
    rw [← mul_assoc, pow_sub_one_mul hq0.ne', hupow]
  have hsp : (ω * T.s ^ m) ^ (q - 1) * (ω * T.s ^ m * p₁) = T.s ^ (q * m) * p₁ := by
    rw [← mul_assoc, pow_sub_one_mul hq0.ne', hspow]
  have ha : T.t ^ (q * m) * c₁ ∈ T.S (q * m) := by
    rw [memS]
    constructor
    · have ea : T.t ^ (q * m) * c₁ =
          σ - T.t ^ (q * m) * b₁ - (ω * T.t ^ m) ^ (q - 1) * (ω * T.t ^ m * p₁) := by
        rw [hup]
        linear_combination (-T.t ^ (q * m)) * hy + σ * hqm
      rw [ea]
      exact T.B.sub_mem (T.B.sub_mem hσ.1 (T.B.mul_mem (T.B.pow_mem T.tB _) hb₁))
        (T.B.mul_mem (T.B.pow_mem hB _) hp1)
    · have ec : T.s ^ (q * m) * (T.t ^ (q * m) * c₁) = c₁ := by
        linear_combination c₁ * hqm
      rw [ec]
      exact hc₁
  have hb : b₁ ∈ T.S (q * m) := by
    rw [memS]
    refine ⟨hb₁, ?_⟩
    have eb : T.s ^ (q * m) * b₁ =
        T.s ^ (2 * q * m) * σ - T.s ^ (q * m) * c₁ - (ω * T.s ^ m) ^ (q - 1) * (ω * T.s ^ m * p₁) := by
      rw [hsp, show 2 * q * m = q * m + q * m by ring, pow_add]
      linear_combination (-T.s ^ (q * m)) * hy
    rw [eb]
    exact T.C.sub_mem (T.C.sub_mem hσ.2 (T.C.mul_mem (T.C.pow_mem T.sC _) hc₁))
      (T.C.mul_mem (T.C.pow_mem hC _) hp2)
  have hpS : ω * T.t ^ m * p₁ ∈ T.S (2 * m) := by
    rw [memS]
    refine ⟨hp1, ?_⟩
    have e : T.s ^ (2 * m) * (ω * T.t ^ m * p₁) = ω * T.s ^ m * p₁ := by
      rw [two_mul, pow_add]
      linear_combination (ω * T.s ^ m * p₁) * hts
    rw [e]
    exact hp2
  refine ⟨T.t ^ (q * m) * c₁, ha, b₁, hb, -(r • (ω * T.t ^ m * p₁)),
    Submodule.neg_mem _ (Submodule.smul_mem _ r hpS), ?_⟩
  have hrq : algebraMap A D r * (q : D) = 1 := by
    rw [← map_natCast (algebraMap A D), ← map_mul, hr, map_one]
  rw [Algebra.smul_def]
  linear_combination (-(q : D) * algebraMap A D r) * hup - T.t ^ (q * m) * p₁ * hrq +
    T.t ^ (q * m) * hy - σ * hqm

end
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsTwoChartQuotientOfFiniteCoord
noncomputable section
open IsLocalRing UpperTheory.Et

private theorem coord_mem_of_mem {A D ι : Type} [CommRing A] [CommRing D] [Algebra A D]
    (β : Module.Basis ι A D) (I : Ideal A) {x : D} (hx : x ∈ I.map (algebraMap A D)) (i : ι) :
    β.repr x i ∈ I := by
  have hx' : x ∈ I • (⊤ : Submodule A D) := by
    rw [Ideal.smul_top_eq_map]
    exact hx
  refine Submodule.smul_induction_on (p := fun y => β.repr y i ∈ I) hx' ?_ ?_
  · intro a ha n _
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact I.mul_mem_right _ ha
  · intro y z hy hz
    rw [map_add (f := _), Finsupp.add_apply]
    exact I.add_mem hy hz

private theorem mem_smul_span_of_coord {A D ι : Type} [CommRing A] [CommRing D] [Algebra A D]
    (β : Module.Basis ι A D) (I : Ideal A) (W : Set ι) {x : D}
    (hW : x ∈ Submodule.span A (β '' W)) (hc : ∀ i, β.repr x i ∈ I) :
    x ∈ I • Submodule.span A (β '' W) := by
  have hs : ↑(β.repr x).support ⊆ W := (β.mem_span_image).1 hW
  rw [← β.linearCombination_repr x, Finsupp.linearCombination_apply, Finsupp.sum]
  refine Submodule.sum_mem _ (fun i hi => ?_)
  exact Submodule.smul_mem_smul (hc i) (Submodule.subset_span ⟨i, hs hi, rfl⟩)

private theorem mem_map_of_coord {A D ι : Type} [CommRing A] [CommRing D] [Algebra A D]
    (β : Module.Basis ι A D) (I : Ideal A) {x : D} (hc : ∀ i, β.repr x i ∈ I) :
    x ∈ I.map (algebraMap A D) := by
  rw [← β.linearCombination_repr x, Finsupp.linearCombination_apply, Finsupp.sum]
  refine Ideal.sum_mem _ (fun i _ => ?_)
  rw [Algebra.smul_def]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hc i))

theorem UpperTheory.exists_twoChart_quotient_of_finite_coord :
    ∀ (A D : Type) [CommRing A] [CommRing D] [Algebra A D] (T : TC A D), T.Fin → T.Coord → ∀ I : Ideal A, ∃ T' : TC A (D ⧸ I.map (algebraMap A D)), T'.Fin ∧ T'.t = Ideal.Quotient.mk _ T.t ∧ T'.s = Ideal.Quotient.mk _ T.s ∧
      (∀ j, ∀ y ∈ T'.S j, ∃ x ∈ T.S j, Ideal.Quotient.mk _ x = y) ∧ (∀ j, ∀ x ∈ T.S j, Ideal.Quotient.mk _ x ∈ T'.S j) ∧
      (∀ x ∈ T.B, x ∈ I.map (algebraMap A D) → x ∈ I • Subalgebra.toSubmodule T.B) ∧ ∀ x ∈ T.C, x ∈ I.map (algebraMap A D) → x ∈ I • Subalgebra.toSubmodule T.C := by
  classical
  intro A D _ _ _ T hF hC I
  obtain ⟨ι, β, U, V, hU, hV⟩ := hC
  set J := I.map (algebraMap A D) with hJ
  let q := Ideal.Quotient.mkₐ A J
  have hq : ∀ z, q z = Ideal.Quotient.mk J z := fun z => rfl
  have hsurj : Function.Surjective (Ideal.Quotient.mk J) := Ideal.Quotient.mk_surjective
  have h1 : Ideal.Quotient.mk J T.t * Ideal.Quotient.mk J T.s = 1 := by
    rw [← map_mul, T.ts, map_one]
  let T' : TC A (D ⧸ J) :=
    { B := T.B.map q
      C := T.C.map q
      t := Ideal.Quotient.mk J T.t
      s := Ideal.Quotient.mk J T.s
      ts := h1
      tB := Subalgebra.mem_map.2 ⟨T.t, T.tB, rfl⟩
      sC := Subalgebra.mem_map.2 ⟨T.s, T.sC, rfl⟩
      locB := by
        intro y
        obtain ⟨x, rfl⟩ := hsurj y
        obtain ⟨k, hk⟩ := T.locB x
        exact ⟨k, Subalgebra.mem_map.2 ⟨_, hk, by rw [hq, map_mul, map_pow]⟩⟩
      locC := by
        intro y
        obtain ⟨x, rfl⟩ := hsurj y
        obtain ⟨k, hk⟩ := T.locC x
        exact ⟨k, Subalgebra.mem_map.2 ⟨_, hk, by rw [hq, map_mul, map_pow]⟩⟩ }
  refine ⟨T', ?_, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · obtain ⟨X, hX1, hX2⟩ := hF
    refine ⟨X.image q, ?_, ?_⟩
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
      exact Subalgebra.mem_map.2 ⟨x, hX1 x hx, rfl⟩
    · intro b hb
      obtain ⟨b0, hb0, rfl⟩ := Subalgebra.mem_map.1 hb
      have hm := Submodule.mem_map_of_mem (f := q.toLinearMap) (hX2 b0 hb0)
      rw [Submodule.map_span] at hm
      refine Submodule.span_mono ?_ hm
      rintro _ ⟨y, ⟨x, hx, i, rfl⟩, rfl⟩
      refine ⟨q x, Finset.mem_image.2 ⟨x, hx, rfl⟩, i, ?_⟩
      show q (T.t ^ i * x) = Ideal.Quotient.mk J T.t ^ i * q x
      rw [map_mul, map_pow]
      rfl
  · intro j y hy
    obtain ⟨hyB, hyC⟩ := Submodule.mem_inf.1 hy
    obtain ⟨b, hb, rfl⟩ := Subalgebra.mem_map.1 hyB
    obtain ⟨c, hc, hce⟩ := Subalgebra.mem_map.1 (Submodule.mem_comap.1 hyC)
    have hw : T.t ^ j * c ∈ Submodule.span A (β '' V j) := by
      rw [← (hV j).1, Submodule.mem_comap, LinearMap.mulLeft_apply, ← mul_assoc, ← mul_pow,
        mul_comm T.s, T.ts, one_pow, one_mul]
      exact hc
    have hbw : b - T.t ^ j * c ∈ J := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_pow, ← hq c, hce]
      change Ideal.Quotient.mk J b - Ideal.Quotient.mk J T.t ^ j *
        (Ideal.Quotient.mk J T.s ^ j * Ideal.Quotient.mk J b) = 0
      rw [← mul_assoc, ← mul_pow, h1, one_pow, one_mul, sub_self]
    have hcoord := coord_mem_of_mem β I hbw
    have hbU : ↑(β.repr b).support ⊆ U := β.mem_span_image.1 (by rw [← hU]; exact hb)
    have hwV : ↑(β.repr (T.t ^ j * c)).support ⊆ V j := β.mem_span_image.1 hw
    set f := Finsupp.filter (· ∈ V j) (β.repr b) with hf
    have hrx : β.repr (β.repr.symm f) = f := β.repr.apply_symm_apply f
    refine ⟨β.repr.symm f, Submodule.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
    · show β.repr.symm f ∈ Subalgebra.toSubmodule T.B
      rw [hU, β.mem_span_image, hrx]
      intro i hi
      rw [Finset.mem_coe, hf, Finsupp.support_filter, Finset.mem_filter] at hi
      exact hbU hi.1
    · show β.repr.symm f ∈ Submodule.comap (LinearMap.mulLeft A (T.s ^ j)) (Subalgebra.toSubmodule T.C)
      rw [(hV j).1, β.mem_span_image, hrx]
      intro i hi
      rw [Finset.mem_coe, hf, Finsupp.support_filter, Finset.mem_filter] at hi
      exact hi.2
    · refine Ideal.Quotient.eq.2 (mem_map_of_coord β I (fun i => ?_))
      rw [map_sub, Finsupp.sub_apply, hrx, hf, Finsupp.filter_apply]
      by_cases hi : i ∈ V j
      · rw [if_pos hi, sub_self]
        exact I.zero_mem
      · rw [if_neg hi, zero_sub]
        have hw0 : β.repr (T.t ^ j * c) i = 0 := Finsupp.notMem_support_iff.1 (fun h => hi (hwV h))
        have hci := hcoord i
        rw [map_sub, Finsupp.sub_apply, hw0, sub_zero] at hci
        exact I.neg_mem hci
  · intro j x hx
    obtain ⟨hxB, hxC⟩ := Submodule.mem_inf.1 hx
    refine Submodule.mem_inf.2 ⟨Subalgebra.mem_map.2 ⟨x, hxB, rfl⟩, ?_⟩
    show Ideal.Quotient.mk J T.s ^ j * Ideal.Quotient.mk J x ∈ T.C.map q
    exact Subalgebra.mem_map.2 ⟨T.s ^ j * x, hxC, by rw [hq, map_mul, map_pow]⟩
  · intro x hx hxJ
    have hxs : x ∈ Submodule.span A (β '' U) := by rw [← hU]; exact hx
    rw [hU]
    exact mem_smul_span_of_coord β I U hxs (coord_mem_of_mem β I hxJ)
  · intro x hx hxJ
    have hC0 : Subalgebra.toSubmodule T.C = Submodule.span A (β '' V 0) := by
      rw [← (hV 0).1, pow_zero, LinearMap.mulLeft_one, Submodule.comap_id]
    have hxs : x ∈ Submodule.span A (β '' V 0) := by rw [← hC0]; exact hx
    rw [hC0]
    exact mem_smul_span_of_coord β I (V 0) hxs (coord_mem_of_mem β I hxJ)

end
end

noncomputable section
open IsLocalRing UpperTheory.Et

namespace UpperTheory.LinearFiltration

section
variable {A D : Type} [CommRing A] [CommRing D] [Algebra A D]

private lemma mem_S (T : TC A D) (j : ℕ) (x : D) :
    x ∈ T.S j ↔ x ∈ T.B ∧ T.s ^ j * x ∈ T.C := (Iff.rfl)

private lemma S_mul (T : TC A D) {i j : ℕ} {x y : D} (hx : x ∈ T.S i) (hy : y ∈ T.S j) :
    x * y ∈ T.S (i + j) := by
  rw [mem_S] at *
  refine ⟨T.B.mul_mem hx.1 hy.1, ?_⟩
  have := T.C.mul_mem hx.2 hy.2
  convert this using 1
  ring

private lemma S_one (T : TC A D) (j : ℕ) : (1 : D) ∈ T.S j := by
  rw [mem_S]
  refine ⟨one_mem _, ?_⟩
  rw [mul_one]
  exact pow_mem T.sC j

private lemma S_pow (T : TC A D) {j : ℕ} {x : D} (hx : x ∈ T.S j) (k : ℕ) :
    x ^ k ∈ T.S (k * j) := by
  induction k with
  | zero => simpa using S_one T 0
  | succ k ih =>
    rw [pow_succ, Nat.succ_mul]
    exact S_mul T ih hx

private lemma st_pow (T : TC A D) (j : ℕ) : T.s ^ j * T.t ^ j = 1 := by
  rw [← mul_pow, mul_comm, T.ts, one_pow]

private lemma power_mem_filtration (T : TC A D) (j : ℕ) : T.t ^ j ∈ T.S j := by
  rw [mem_S]
  refine ⟨pow_mem T.tB j, ?_⟩
  rw [st_pow]
  exact one_mem _

private lemma coord_setup (T : TC A D) (hC : T.Coord) (j : ℕ) :
    ∃ (n : ℕ) (e : Fin n → D) (L : D →ₗ[A] (Fin n → A)),
      (∀ i, e i ∈ T.S j) ∧ (∀ i k, L (e k) i = if i = k then 1 else 0) ∧
        ∀ x ∈ T.S j, L x = 0 → x = 0 := by
  classical
  obtain ⟨ι, β, U, V, hB, hV⟩ := hC
  obtain ⟨hVj, hfin⟩ := hV j
  set F := hfin.toFinset with hF
  have hSB : ∀ x, x ∈ T.B ↔ ↑(β.repr x).support ⊆ U := by
    intro x
    rw [← Subalgebra.mem_toSubmodule, hB, Module.Basis.mem_span_image]
  have hSC : ∀ x, T.s ^ j * x ∈ T.C ↔ ↑(β.repr x).support ⊆ V j := by
    intro x
    change x ∈ Submodule.comap (LinearMap.mulLeft A (T.s ^ j)) (Subalgebra.toSubmodule T.C) ↔ _
    rw [hVj, Module.Basis.mem_span_image]
  let L : D →ₗ[A] (Fin F.card → A) :=
    LinearMap.pi fun i => (Finsupp.lapply (F.equivFin.symm i : ι)).comp β.repr.toLinearMap
  refine ⟨F.card, fun i => β (F.equivFin.symm i : ι), L, ?_, ?_, ?_⟩
  · intro i
    have hi : (F.equivFin.symm i : ι) ∈ U ∩ V j := hfin.mem_toFinset.1 (F.equivFin.symm i).2
    rw [mem_S, hSB, hSC, Module.Basis.repr_self]
    refine ⟨?_, ?_⟩ <;> refine (Finset.coe_subset.2 Finsupp.support_single_subset).trans ?_ <;>
      simp [hi.1, hi.2]
  · intro i k
    change β.repr (β (F.equivFin.symm k : ι)) (F.equivFin.symm i : ι) = _
    rw [Module.Basis.repr_self, Finsupp.single_apply]
    by_cases h : i = k
    · subst h; simp
    · rw [if_neg, if_neg h]
      intro h'
      exact h (F.equivFin.symm.injective (Subtype.ext h'.symm))
  · intro x hx hL
    rw [mem_S, hSB, hSC] at hx
    have h0 : β.repr x = 0 := by
      ext a
      by_cases ha : a ∈ (β.repr x).support
      · have haF : a ∈ F := hfin.mem_toFinset.2 ⟨hx.1 ha, hx.2 ha⟩
        have h1 := congrFun hL (F.equivFin ⟨a, haF⟩)
        change β.repr x (F.equivFin.symm (F.equivFin ⟨a, haF⟩) : ι) = 0 at h1
        simpa using h1
      · simpa using ha
    simpa using h0

private lemma L_mem {n : ℕ} (I : Ideal A) (L : D →ₗ[A] (Fin n → A)) (x : D)
    (hx : x ∈ I.map (algebraMap A D)) (i : Fin n) : L x i ∈ I := by
  have key : ∀ d : D, ∀ i, L (d * x) i ∈ I := by
    change x ∈ Submodule.span D (algebraMap A D '' (I : Set A)) at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, ha, rfl⟩ := hy
      intro d i
      rw [mul_comm, ← Algebra.smul_def, map_smul]
      simpa using I.mul_mem_right (L d i) ha
    | zero => intro d i; simp
    | add y z _ _ hy hz =>
      intro d i
      rw [mul_add, map_add (f := _)]
      exact I.add_mem (hy d i) (hz d i)
    | smul e y _ hy =>
      intro d i
      rw [smul_eq_mul, ← mul_assoc]
      exact hy (d * e) i
  simpa using key 1 i

end

section
variable {D : Type} [CommRing D] {n : ℕ}

private def lin (c : D) (a : Fin n → D) : MvPolynomial (Fin n) D :=
  MvPolynomial.C c + ∑ i, MvPolynomial.C (a i) * MvPolynomial.X i

private lemma eval_lin (c : D) (a y : Fin n → D) :
    MvPolynomial.eval y (lin c a) = c + ∑ i, a i * y i := by
  simp [lin]

private lemma pderiv_lin (c : D) (a : Fin n → D) (j : Fin n) :
    MvPolynomial.pderiv j (lin c a) = MvPolynomial.C (a j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [lin, MvPolynomial.pderiv_X, Pi.single_apply, map_sum, Derivation.leibniz]

end

private lemma mem_mm_top {A D : Type} [CommRing A] [IsLocalRing A] [CommRing D] [Algebra A D] (x : D) :
    x ∈ mm (⊤ : Subalgebra A D) ↔ x ∈ (maximalIdeal A).map (algebraMap A D) := by
  change x ∈ maximalIdeal A • (⊤ : Submodule A D) ↔ _
  rw [Ideal.smul_top_eq_map]
  rfl

end UpperTheory.LinearFiltration

open UpperTheory.LinearFiltration in
theorem UpperTheory.exists_factorization_near_root_of_unity_henselian :
    ∀ (A D : Type) [CommRing A] [HenselianLocalRing A] [CommRing D] [Algebra A D] (T : TC A D), T.Fin → T.Coord → ∀ (q : ℕ), IsUnit (q : A) → ∀ ω : D, ω ^ q - 1 ∈ mm (⊤ : Subalgebra A D) →
      ∃ g' ∈ T.B, ∃ g ∈ T.C, ∃ μ : D, g' - 1 ∈ mm T.B ∧ g - 1 ∈ mm T.C ∧ μ - ω ∈ mm (⊤ : Subalgebra A D) ∧ g * g' = μ ^ q := by
  intro A D _ _ _ _ T hF hC q hq ω hω
  classical
  set M := maximalIdeal A with hM
  set J := M.map (algebraMap A D) with hJ
  have hωJ : ω ^ q - 1 ∈ J := (mem_mm_top _).1 hω
  have hq0 : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · subst h; simp at hq
    · exact h
  obtain ⟨T', hT'F, hT't, -, hlift, hproj, -, -⟩ := exists_twoChart_quotient_of_finite_coord A D T hF hC M
  have hω' : (Ideal.Quotient.mk J ω) ^ q = 1 := by
    rw [← map_pow, ← map_one (Ideal.Quotient.mk J), Ideal.Quotient.eq]
    exact hωJ
  obtain ⟨m₀, hm₀⟩ := exists_power_decomposition_of_root_of_unity A (D ⧸ J) T' hT'F q hq hq0 (Ideal.Quotient.mk J ω) hω'
  obtain ⟨k₁, hk₁⟩ := T.locB ω
  obtain ⟨k₂, hk₂⟩ := T.locC ω
  obtain ⟨m, hm⟩ : ∃ m, m = m₀ + k₁ + k₂ := ⟨_, rfl⟩
  have hmm : m ≥ m₀ := by omega
  have hW : ω * T.t ^ m ∈ T.S (2 * m) := by
    rw [mem_S]
    constructor
    · have e : ω * T.t ^ m = T.t ^ (m₀ + k₂) * (T.t ^ k₁ * ω) := by rw [hm]; ring
      rw [e]
      exact mul_mem (pow_mem T.tB _) hk₁
    · have e : T.s ^ (2 * m) * (ω * T.t ^ m) = T.s ^ (m₀ + k₁) * (T.s ^ k₂ * ω) := by
        calc T.s ^ (2 * m) * (ω * T.t ^ m) = T.s ^ m * (T.s ^ m * T.t ^ m) * ω := by ring
          _ = T.s ^ m * ω := by rw [st_pow]; ring
          _ = _ := by rw [hm]; ring
      rw [e]
      exact mul_mem (pow_mem T.sC _) hk₂
  obtain ⟨n, e, L, he, hLe, hLinj⟩ := coord_setup T hC (2 * q * m)
  have hdec : ∀ k, ∃ a ∈ T.S (q * m), ∃ b ∈ T.S (q * m), ∃ c ∈ T.S (2 * m),
      a + T.t ^ (q * m) * b - (q : D) * (ω * T.t ^ m) ^ (q - 1) * c - e k ∈ J := by
    intro k
    obtain ⟨a', ha', b', hb', c', hc', hk⟩ := (hm₀ m hmm).2 _ (hproj _ _ (he k))
    obtain ⟨a, ha, rfl⟩ := hlift _ _ ha'
    obtain ⟨b, hb, rfl⟩ := hlift _ _ hb'
    obtain ⟨c, hc, rfl⟩ := hlift _ _ hc'
    refine ⟨a, ha, b, hb, c, hc, ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    rw [hT't] at hk
    simp only [map_sub, map_add (f := _), map_mul, map_pow, map_natCast]
    rw [hk]
    ring
  choose a ha b hb c hc hkey using hdec
  set Φ : MvPolynomial (Fin n) D :=
    lin (T.t ^ (q * m)) a * lin 1 b - (lin (ω * T.t ^ m) c) ^ q with hΦ
  have ev0 : ∀ (c0 : D) (v : Fin n → D), MvPolynomial.eval 0 (lin c0 v) = c0 := by
    intro c0 v
    rw [eval_lin]
    simp
  have h0 : ∀ i, L (MvPolynomial.eval 0 Φ) i ∈ M := by
    intro i
    apply L_mem M L
    have e0 : MvPolynomial.eval 0 Φ = -(T.t ^ (q * m)) * (ω ^ q - 1) := by
      rw [hΦ]
      simp only [map_sub, map_mul, map_pow, ev0]
      ring
    rw [e0]
    exact J.mul_mem_left _ hωJ
  have hd0 : ∀ j, MvPolynomial.eval 0 (MvPolynomial.pderiv j Φ) =
      a j + T.t ^ (q * m) * b j - (q : D) * (ω * T.t ^ m) ^ (q - 1) * c j := by
    intro j
    rw [hΦ]
    simp only [map_sub, Derivation.leibniz, Derivation.leibniz_pow, pderiv_lin, smul_eq_mul,
      nsmul_eq_mul, map_add, map_mul, map_pow, map_natCast, ev0, MvPolynomial.eval_C]
    ring
  have hd : ∀ i j, L (MvPolynomial.eval 0 (MvPolynomial.pderiv j Φ)) i - (if i = j then 1 else 0) ∈ M := by
    intro i j
    have h1 := L_mem M L _ (hkey j) i
    rw [map_sub, Pi.sub_apply, hLe i j] at h1
    rw [hd0]
    exact h1
  obtain ⟨x, hxM, hΦx⟩ := exists_zero_of_linear_form_jacobian_henselian A D n Φ L h0 hd
  set y : Fin n → D := fun j => algebraMap A D (x j) with hy
  have hsum : ∀ (j : ℕ) (v : Fin n → D), (∀ k, v k ∈ T.S j) → ∑ k, v k * y k ∈ T.S j := by
    intro j v hv
    refine Submodule.sum_mem _ (fun k _ => ?_)
    rw [mul_comm, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (hv k)
  have hsumM : ∀ (S : Subalgebra A D) (v : Fin n → D), (∀ k, v k ∈ S) → ∑ k, v k * y k ∈ mm S := by
    intro S v hv
    refine Submodule.sum_mem _ (fun k _ => ?_)
    rw [mul_comm, ← Algebra.smul_def]
    exact Submodule.smul_mem_smul (hxM k) (by simpa using hv k)
  have hev : MvPolynomial.eval y Φ = (T.t ^ (q * m) + ∑ k, a k * y k) * (1 + ∑ k, b k * y k) -
      (ω * T.t ^ m + ∑ k, c k * y k) ^ q := by
    rw [hΦ]
    simp only [map_sub, map_mul, map_pow, eval_lin]
  have hmem : MvPolynomial.eval y Φ ∈ T.S (2 * q * m) := by
    rw [hev]
    refine Submodule.sub_mem _ ?_ ?_
    · have e1 : 2 * q * m = q * m + q * m := by ring
      rw [e1]
      exact S_mul T (Submodule.add_mem _ (power_mem_filtration T _) (hsum _ _ ha))
        (Submodule.add_mem _ (S_one T _) (hsum _ _ hb))
    · have e2 : 2 * q * m = q * (2 * m) := by ring
      rw [e2]
      exact S_pow T (Submodule.add_mem _ hW (hsum _ _ hc)) q
  have hzero := hLinj _ hmem hΦx
  have hkey2 : (T.t ^ (q * m) + ∑ k, a k * y k) * (1 + ∑ k, b k * y k) =
      (ω * T.t ^ m + ∑ k, c k * y k) ^ q := by
    rw [hev] at hzero
    exact sub_eq_zero.1 hzero
  refine ⟨1 + ∑ k, b k * y k, ?_, 1 + T.s ^ (q * m) * ∑ k, a k * y k, ?_,
    ω + T.s ^ m * ∑ k, c k * y k, ?_, ?_, ?_, ?_⟩
  · exact add_mem (one_mem _) ((mem_S T _ _).1 (hsum _ _ hb)).1
  · exact add_mem (one_mem _) ((mem_S T _ _).1 (hsum _ _ ha)).2
  · rw [add_sub_cancel_left]
    exact hsumM T.B b (fun k => ((mem_S T _ _).1 (hb k)).1)
  · rw [add_sub_cancel_left, Finset.mul_sum]
    simp_rw [← mul_assoc]
    exact hsumM T.C (fun k => T.s ^ (q * m) * a k) (fun k => ((mem_S T _ _).1 (ha k)).2)
  · rw [add_sub_cancel_left, Finset.mul_sum]
    simp_rw [← mul_assoc]
    exact hsumM ⊤ (fun k => T.s ^ m * c k) (fun _ => Algebra.mem_top)
  · calc (1 + T.s ^ (q * m) * ∑ k, a k * y k) * (1 + ∑ k, b k * y k)
          = T.s ^ (q * m) * ((T.t ^ (q * m) + ∑ k, a k * y k) * (1 + ∑ k, b k * y k)) := by
            have h := st_pow T (q * m)
            linear_combination (-(1 + ∑ k, b k * y k)) * h
      _ = T.s ^ (q * m) * (ω * T.t ^ m + ∑ k, c k * y k) ^ q := by rw [hkey2]
      _ = (ω + T.s ^ m * ∑ k, c k * y k) ^ q := by
            rw [show T.s ^ (q * m) = (T.s ^ m) ^ q by ring, ← mul_pow]
            congr 1
            linear_combination ω * st_pow T m

end
