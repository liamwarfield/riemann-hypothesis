module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftAutomorphicForm

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DiagUniformizerBlockEqDiagonalPowMulIntegralGL
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DiagUniformizerBlockEqDiagonalPowMulIntegralGL
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct

namespace GlobalTheory.DiagUnifFactor

theorem getD_pattern (k m i : ℕ) :
    (List.replicate k (1 : ℤ) ++ List.replicate m 0).getD i 0 = if i < k then 1 else 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append]
  split_ifs with h1 h2 h2
  · simp [List.getElem?_replicate, h2]
  · simp at h1; omega
  · simp at h1; omega
  · simp [List.getElem?_replicate]
    split_ifs <;> rfl

theorem main : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n k : ℕ)
    (ϖ π : v.adicCompletion F), Valued.v ϖ = WithZero.exp (-1 : ℤ) → Valued.v π = WithZero.exp (-1 : ℤ) →
    ∃ T ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v), Formalism.UG.diagJ n ϖ k =
      Matrix.diagonal (fun i : Fin n => π ^ ((List.replicate k (1 : ℤ) ++ List.replicate (n - k) 0).getD i.1 0)) *
        (T : Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
  intro F _ _ v n k ϖ π hϖ hπ
  have hπ0 : π ≠ 0 := by
    intro h; rw [h, map_zero] at hπ; exact WithZero.zero_ne_coe hπ
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hϖ; exact WithZero.zero_ne_coe hϖ
  have hu : Valued.v (ϖ / π) = 1 := by
    rw [map_div₀, hϖ, hπ, div_self (WithZero.coe_ne_zero)]
  have hu' : Valued.v (π / ϖ) = 1 := by
    rw [map_div₀, hϖ, hπ, div_self (WithZero.coe_ne_zero)]
  let d : Fin n → v.adicCompletion F := fun i => if (i : ℕ) < k then ϖ / π else 1
  let d' : Fin n → v.adicCompletion F := fun i => if (i : ℕ) < k then π / ϖ else 1
  have hdd' : Matrix.diagonal d * Matrix.diagonal d' = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; simp only [d, d']
    split_ifs
    · rw [div_mul_div_comm, mul_comm ϖ π, div_self (mul_ne_zero hπ0 hϖ0)]
    · exact one_mul 1
  have hd'd : Matrix.diagonal d' * Matrix.diagonal d = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; simp only [d, d']
    split_ifs
    · rw [div_mul_div_comm, mul_comm π ϖ, div_self (mul_ne_zero hϖ0 hπ0)]
    · exact one_mul 1
  let T : GL (Fin n) (v.adicCompletion F) := ⟨Matrix.diagonal d, Matrix.diagonal d', hdd', hd'd⟩
  have hmem : ∀ (e : Fin n → v.adicCompletion F), (∀ i, Valued.v (e i) ≤ 1) →
      ∀ a b, Matrix.diagonal e a b ∈ Formalism.UG.Ov F v := by
    intro e he a b
    show Matrix.diagonal e a b ∈ v.adicCompletionIntegers F
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    by_cases hab : a = b
    · subst hab; rw [Matrix.diagonal_apply_eq]; exact he a
    · rw [Matrix.diagonal_apply_ne _ hab, map_zero]; exact zero_le'
  have hle : ∀ (x : v.adicCompletion F), Valued.v x = 1 → ∀ i : Fin n,
      Valued.v (if (i : ℕ) < k then x else 1) ≤ 1 := by
    intro x hx i; split_ifs
    · exact hx.le
    · rw [map_one]
  refine ⟨T, ?_, ?_⟩
  · have inj : Function.Injective ((Formalism.UG.Ov F v).subtype.mapMatrix (m := Fin n)) :=
      fun A B h => Matrix.ext fun i j => Subtype.ext (congrFun (congrFun h i) j)
    let A : Matrix (Fin n) (Fin n) (Formalism.UG.Ov F v) := fun i j => ⟨Matrix.diagonal d i j, hmem d (hle _ hu) i j⟩
    let B : Matrix (Fin n) (Fin n) (Formalism.UG.Ov F v) := fun i j => ⟨Matrix.diagonal d' i j, hmem d' (hle _ hu') i j⟩
    have hA : (Formalism.UG.Ov F v).subtype.mapMatrix A = Matrix.diagonal d := rfl
    have hB : (Formalism.UG.Ov F v).subtype.mapMatrix B = Matrix.diagonal d' := rfl
    refine ⟨⟨A, B, inj ?_, inj ?_⟩, Units.ext rfl⟩
    · rw [map_mul, hA, hB, map_one, hdd']
    · rw [map_mul, hA, hB, map_one, hd'd]
  · show Matrix.diagonal _ = _ * Matrix.diagonal d
    rw [Matrix.diagonal_mul_diagonal]
    congr 1; funext i
    rw [getD_pattern]
    simp only [d]
    split_ifs
    · rw [zpow_one, mul_div_cancel₀ _ hπ0]
    · rw [zpow_zero, one_mul]

end GlobalTheory.DiagUnifFactor
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DiagUniformizerBlockEqDiagonalPowMulIntegralGLStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagUniformizerBlock_eq_diagonal_pow_mul_integralGL : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n k : ℕ)
    (ϖ π : v.adicCompletion F), Valued.v ϖ = WithZero.exp (-1 : ℤ) → Valued.v π = WithZero.exp (-1 : ℤ) →
    ∃ T ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v), Formalism.UG.diagJ n ϖ k =
      Matrix.diagonal (fun i : Fin n => π ^ ((List.replicate k (1 : ℤ) ++ List.replicate (n - k) 0).getD i.1 0)) *
        (T : Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
  first | exact @GlobalTheory.DiagUnifFactor.main | exact GlobalTheory.DiagUnifFactor.main | (intros; apply GlobalTheory.DiagUnifFactor.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRealSubfieldUniformizerAtSplitPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRealSubfieldUniformizerAtSplitPlace
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct

namespace GlobalTheory.RealUnifSplit

theorem le_exp_neg_one_of_lt {x : WithZero (Multiplicative ℤ)} (h : x < 1) : x ≤ WithZero.exp (-1) := by
  rw [← WithZero.lt_mul_exp_iff_le WithZero.exp_ne_zero, ← WithZero.exp_add, neg_add_cancel,
    WithZero.exp_zero]
  exact h

theorem val_sq_le {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L)
    (z : 𝓞 L) (hz : z ∈ s.w.asIdeal ^ 2) :
    Valued.v (s.i (z : L)) ≤ WithZero.exp (-2) := by
  rw [pow_two] at hz
  refine Submodule.mul_induction_on hz ?_ ?_
  · intro a ha b hb
    have ha' : Valued.v (s.i (a : L)) < 1 := (s.split_mem_ideal a).1 ha
    have hb' : Valued.v (s.i (b : L)) < 1 := (s.split_mem_ideal b).1 hb
    show Valued.v (s.i ((a : L) * (b : L))) ≤ _
    rw [map_mul, map_mul]
    calc Valued.v (s.i (a : L)) * Valued.v (s.i (b : L))
        ≤ WithZero.exp (-1) * WithZero.exp (-1) :=
          mul_le_mul' (le_exp_neg_one_of_lt ha') (le_exp_neg_one_of_lt hb')
      _ = WithZero.exp (-2) := by rw [← WithZero.exp_add]; norm_num
  · intro a b ha hb
    show Valued.v (s.i ((a : L) + (b : L))) ≤ _
    rw [map_add (f := _)]
    exact le_trans (Valuation.map_add _ _ _) (max_le ha hb)

end GlobalTheory.RealUnifSplit

theorem GlobalTheory.realUnif_split {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) :
    ∃ y : 𝓞 L, y ∈ s.w.asIdeal ∧ y ∉ s.w.asIdeal ^ 2 ∧ Formalism.AUTREP.IsUnif L s.v (s.i (y : L)) := by
  obtain ⟨π, hπ⟩ := s.v.intValuation_exists_uniformizer
  have hv : Valued.v (s.i ((algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) π : 𝓞 L) : L)) =
      WithZero.exp (-1) := by
    rw [s.split_val_alg, HeightOneSpectrum.valuation_of_algebraMap, hπ]
  refine ⟨algebraMap _ (𝓞 L) π, ?_, ?_, hv⟩
  · refine (s.split_mem_ideal _).2 ?_
    rw [hv]; rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  · intro h
    have h2 := GlobalTheory.RealUnifSplit.val_sq_le s _ h
    rw [hv] at h2
    have := WithZero.exp_le_exp.1 h2
    omega
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRealSubfieldUniformizerAtSplitPlaceStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_realSubfield_uniformizer_at_splitPlace : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L),
    ∃ y : 𝓞 L, y ∈ s.w.asIdeal ∧ y ∉ s.w.asIdeal ^ 2 ∧ Formalism.AUTREP.IsUnif L s.v (s.i (y : L)) := by
  first | exact @GlobalTheory.realUnif_split | exact GlobalTheory.realUnif_split | (intros; apply GlobalTheory.realUnif_split <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceIdempotentComponentOneDeterminesPart
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceIdempotentComponentOneDeterminesPart
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct

namespace GlobalTheory.PlaceSupp

theorem finPart_surjective (D : D7) : Function.Surjective (Formalism.L2.Theta.finPart D) := by
  intro y
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul a x =>
    exact ⟨((0, a) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ⊗ₜ[D.host.F] x, rfl⟩
  | add y z hy hz =>
    obtain ⟨a, rfl⟩ := hy
    obtain ⟨b, rfl⟩ := hz
    exact ⟨a + b, (Formalism.L2.Theta.finPart D).map_add a b⟩

theorem comp_idem : ∀ (D : D7) (sp : SplitPlace D.host.E) (hF : D.host.F = maximalRealSubfield D.host.E)
    (p : GlobalTheory.LocMod.Place D (sp.w.adicCompletion D.host.E))
    (c : sp.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* sp.w.adicCompletion D.host.E),
    (∀ a : Formalism.L2.Theta.AE D, p.π a = c (sp.proj (GlobalTheory.NJoin.tensCast hF (Formalism.L2.Theta.finPart D a)))) →
    sp.proj (GlobalTheory.NJoin.tensCast hF (Formalism.L2.Theta.finPart D p.e)) = 1 ∧
      ∀ x y, sp.proj (GlobalTheory.NJoin.tensCast hF x) = sp.proj (GlobalTheory.NJoin.tensCast hF y) →
        Formalism.L2.Theta.finPart D p.e * x = Formalism.L2.Theta.finPart D p.e * y := by
  intro D sp hF p c hπ
  have hι1 : p.ι 1 = p.e := by
    have := p.ι_π 1
    rwa [map_one, mul_one] at this
  have hπe : p.π p.e = 1 := by rw [← hι1, p.π_ι]
  refine ⟨?_, ?_⟩
  · apply c.injective
    rw [← hπ, hπe, map_one]
  · intro x y hxy
    obtain ⟨a, rfl⟩ := finPart_surjective D x
    obtain ⟨b, rfl⟩ := finPart_surjective D y
    have hab : p.π a = p.π b := by rw [hπ, hπ, hxy]
    have key : p.e * a = p.e * b := by rw [← p.ι_π, ← p.ι_π, hab]
    rw [← map_mul, ← map_mul, key]

end GlobalTheory.PlaceSupp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceIdempotentComponentOneDeterminesPartStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlaceIdempotent_component_one_determines_part : ∀ (D : D7) (sp : SplitPlace D.host.E) (hF : D.host.F = maximalRealSubfield D.host.E)
    (p : GlobalTheory.LocMod.Place D (sp.w.adicCompletion D.host.E))
    (c : sp.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* sp.w.adicCompletion D.host.E),
    (∀ a : Formalism.L2.Theta.AE D, p.π a = c (sp.proj (GlobalTheory.NJoin.tensCast hF (Formalism.L2.Theta.finPart D a)))) →
    sp.proj (GlobalTheory.NJoin.tensCast hF (Formalism.L2.Theta.finPart D p.e)) = 1 ∧
      ∀ x y, sp.proj (GlobalTheory.NJoin.tensCast hF x) = sp.proj (GlobalTheory.NJoin.tensCast hF y) →
        Formalism.L2.Theta.finPart D p.e * x = Formalism.L2.Theta.finPart D p.e * y := by
  first | exact @GlobalTheory.PlaceSupp.comp_idem | exact GlobalTheory.PlaceSupp.comp_idem | (intros; apply GlobalTheory.PlaceSupp.comp_idem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormaliserGLintEqScalarMulGLint
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormaliserGLintEqScalarMulGLint
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct

namespace GlobalTheory.NormaliserGLint

open Matrix

theorem exists_unif (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ ϖ : v.adicCompletion F, Formalism.UG.IsUnifV F v ϖ := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  refine ⟨(π : v.adicCompletion F), ?_⟩
  unfold Formalism.UG.IsUnifV
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]
  rfl

theorem mul_entries_mem {L : Type} [Field L] (O : Subring L) {n : ℕ} {A B : Matrix (Fin n) (Fin n) L}
    (hA : ∀ i j, A i j ∈ O) (hB : ∀ i j, B i j ∈ O) : ∀ i j, (A * B) i j ∈ O := by
  intro i j
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => O.mul_mem (hA i k) (hB k j)

theorem mulVec_entries_mem {L : Type} [Field L] (O : Subring L) {n : ℕ} {A : Matrix (Fin n) (Fin n) L}
    {z : Fin n → L} (hA : ∀ i j, A i j ∈ O) (hz : ∀ i, z i ∈ O) : ∀ i, (A *ᵥ z) i ∈ O := by
  intro i
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun k _ => O.mul_mem (hA i k) (hz k)

theorem le_of_zpow_eq {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}
    {ϖ : v.adicCompletion F} (hϖ : Formalism.UG.IsUnifV F v ϖ) {p q : ℤ} {w : v.adicCompletion F}
    (hw : w ∈ Formalism.UG.Ov F v) (h : ϖ ^ q = ϖ ^ p * w) : p ≤ q := by
  have hv := congrArg Valued.v h
  rw [map_mul, map_zpow₀, map_zpow₀, hϖ] at hv
  have hw' : Valued.v w ≤ 1 := hw
  have key : ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ^ q ≤
      ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ^ p := by
    rw [hv]; exact mul_le_of_le_one_right' hw'
  rw [← WithZero.coe_zpow, ← WithZero.coe_zpow, WithZero.coe_le_coe, ← ofAdd_zsmul, ← ofAdd_zsmul,
    Multiplicative.ofAdd_le] at key
  simp at key
  omega

end GlobalTheory.NormaliserGLint

namespace GlobalTheory.NormaliserGLint

open Matrix

theorem conj_eq_glint_mul_mul :
    ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ)
    (N : GL (Fin n) (v.adicCompletion F)),
    (∀ g ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v), ∀ z : Fin n → v.adicCompletion F, (∀ i, z i ∈ Formalism.UG.Ov F v) →
      ∃ z' : Fin n → v.adicCompletion F, (∀ i, z' i ∈ Formalism.UG.Ov F v) ∧
        (g : Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec
            ((N : Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec z) =
          (N : Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec z') →
    ∀ X : Matrix (Fin n) (Fin n) (v.adicCompletion F), ∃ k₁ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v),
      ∃ k₂ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v),
        ((N⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * X *
            (N : Matrix (Fin n) (Fin n) (v.adicCompletion F)) =
          (k₁ : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * X * (k₂ : Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
  intro F _ _ v n N hN X
  obtain ⟨ϖ, hϖ⟩ := exists_unif F v
  have hϖO : ϖ ∈ Formalism.UG.Ov F v := by
    change Valued.v ϖ ≤ 1
    rw [hϖ]
    exact (by decide : ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ≤ 1)
  have h0 : ϖ ≠ 0 := by rintro rfl; simp [Formalism.UG.IsUnifV] at hϖ
  obtain ⟨m, -, a, ha, b, hb, hNab⟩ := Formalism.UG.Final.CartanDecomp F v n ϖ hϖO hϖ N
  set O := Formalism.UG.Ov F v with hO
  have hbe := Formalism.UG.P.cartan_entries_of_mem O b hb
  have hbi := Formalism.UG.P.cartan_entries_of_mem O _ (inv_mem hb)
  have hae := Formalism.UG.P.cartan_entries_of_mem O a ha
  have hai := Formalism.UG.P.cartan_entries_of_mem O _ (inv_mem ha)
  have ha1 : ((a⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *
      (a : Matrix (Fin n) (Fin n) (v.adicCompletion F)) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have ha2 : (a : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *
      ((a⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hb2 : (b : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *
      ((b⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have ha1x : ∀ Y : Matrix (Fin n) (Fin n) (v.adicCompletion F),
      ((a⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *
        ((a : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * Y) = Y := by
    intro Y; rw [← Matrix.mul_assoc, ha1, Matrix.one_mul]
  have ha2x : ∀ Y : Matrix (Fin n) (Fin n) (v.adicCompletion F),
      (a : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *
        (((a⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * Y) = Y := by
    intro Y; rw [← Matrix.mul_assoc, ha2, Matrix.one_mul]
  have key : ∀ i j : Fin n, i ≠ j → m i ≤ m j := by
    intro i j hij
    set E : Matrix (Fin n) (Fin n) (v.adicCompletion F) := Matrix.single i j 1 with hE
    have hsq : E * E = 0 := by rw [hE]; simp [Matrix.single_mul_single_of_ne, hij.symm]
    have hEmem : ∀ r s, E r s ∈ O := by
      intro r s
      simp only [hE, Matrix.single_apply]
      split_ifs
      · exact O.one_mem
      · exact O.zero_mem
    have h1mem : ∀ r s, (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) r s ∈ O := by
      intro r s
      rw [Matrix.one_apply]
      split_ifs
      · exact O.one_mem
      · exact O.zero_mem
    have hAB : ((a : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * (1 + E) *
        ((a⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F))) *
        ((a : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * (1 - E) *
        ((a⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F))) = 1 := by
      have hpm : (1 + E) * (1 - E) = 1 := by
        rw [add_mul, one_mul, mul_sub, mul_one, hsq]; abel
      simp only [Matrix.mul_assoc, ha1x]
      rw [← Matrix.mul_assoc (1 + E), hpm, Matrix.one_mul, ha2]
    obtain ⟨g, hg, hgA⟩ := Formalism.UG.P.cartan_exists_glint O _ _ hAB
      (mul_entries_mem O (mul_entries_mem O hae fun r s => O.add_mem (h1mem r s) (hEmem r s)) hai)
      (mul_entries_mem O (mul_entries_mem O hae fun r s => O.sub_mem (h1mem r s) (hEmem r s)) hai)
    have hz : ∀ k, (((b⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *ᵥ
        Pi.single j 1) k ∈ O := mulVec_entries_mem O hbi fun k => by
      rw [Pi.single_apply]; split_ifs
      · exact O.one_mem
      · exact O.zero_mem
    obtain ⟨z', hz', hEq⟩ := hN g hg _ hz
    rw [hgA, hNab] at hEq
    have hL := congrArg (fun w => ((a⁻¹ : GL (Fin n) (v.adicCompletion F)) :
      Matrix (Fin n) (Fin n) (v.adicCompletion F)) *ᵥ w) hEq
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, ha1x, hb2, Matrix.mul_one] at hL
    have hi := congrFun hL i
    rw [Matrix.mulVec_single_one, Matrix.col_apply] at hi
    rw [← Matrix.mulVec_mulVec] at hi
    simp only [Formalism.UG.diagPow, Matrix.mul_diagonal, Matrix.mulVec_diagonal, Matrix.add_apply,
      Matrix.one_apply_ne hij, hE, Matrix.single_apply_same, zero_add, one_mul] at hi
    exact le_of_zpow_eq hϖ (mulVec_entries_mem O hbe hz' i) hi
  obtain ⟨c, hc, hD⟩ : ∃ c : v.adicCompletion F, c ≠ 0 ∧
      Formalism.UG.diagPow F v ϖ m = c • (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
    rcases n with _ | k
    · exact ⟨1, one_ne_zero, by ext i; exact i.elim0⟩
    · refine ⟨ϖ ^ (m 0), zpow_ne_zero _ h0, ?_⟩
      ext i j
      simp only [Formalism.UG.diagPow, Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      split_ifs with h
      · subst h
        have hm : m i = m 0 := by
          rcases eq_or_ne i 0 with rfl | hi
          · rfl
          · exact le_antisymm (key i 0 hi) (key 0 i hi.symm)
        rw [hm, mul_one]
      · rw [mul_zero]
  refine ⟨(a * b)⁻¹, inv_mem (mul_mem ha hb), a * b, mul_mem ha hb, ?_⟩
  have hNc : (N : Matrix (Fin n) (Fin n) (v.adicCompletion F)) =
      c • ((a * b : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
    rw [hNab, hD, Units.val_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  have hNi : ((N⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) =
      c⁻¹ • (((a * b)⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
    have h1 : ((N⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *
        (N : Matrix (Fin n) (Fin n) (v.adicCompletion F)) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h2 : (N : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *
        (c⁻¹ • (((a * b)⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F))) = 1 := by
      rw [hNc, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hc, one_smul, ← Units.val_mul,
        mul_inv_cancel, Units.val_one]
    calc _ = ((N⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *
          ((N : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *
            (c⁻¹ • (((a * b)⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)))) := by
          rw [h2, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  rw [hNi, hNc]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc, mul_inv_cancel₀ hc, one_smul]

end GlobalTheory.NormaliserGLint
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormaliserGLintEqScalarMulGLintStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normaliser_GLint_conj_eq_two_sided_GLint_mul : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ)
    (N : GL (Fin n) (v.adicCompletion F)),
    (∀ g ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v), ∀ z : Fin n → v.adicCompletion F, (∀ i, z i ∈ Formalism.UG.Ov F v) →
      ∃ z' : Fin n → v.adicCompletion F, (∀ i, z' i ∈ Formalism.UG.Ov F v) ∧
        (g : Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec
            ((N : Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec z) =
          (N : Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec z') →
    ∀ X : Matrix (Fin n) (Fin n) (v.adicCompletion F), ∃ k₁ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v),
      ∃ k₂ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v),
        ((N⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * X *
            (N : Matrix (Fin n) (Fin n) (v.adicCompletion F)) =
          (k₁ : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * X * (k₂ : Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
  first | exact @GlobalTheory.NormaliserGLint.conj_eq_glint_mul_mul | exact GlobalTheory.NormaliserGLint.conj_eq_glint_mul_mul | (intros; apply GlobalTheory.NormaliserGLint.conj_eq_glint_mul_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardFrameConjGLintLeSelfDualLatticeStabilize
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardFrameConjGLintLeSelfDualLatticeStabilize
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct

namespace GlobalTheory.SplitFrameLattice


set_option maxHeartbeats 1000000 in
theorem glint_mul_frame_basis : ∀ {D : D7} (hF : D.host.F = maximalRealSubfield D.host.E) {V : TH.HSp D}
    (Ps : Formalism.IndefR.principalLevelFrame.RowPsi V V.rank) (sp : SplitPlace D.host.E)
    (β β' : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)),
    β * β' = 1 → β' * β = 1 →
    (∀ κ, Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram (Ps.ψ κ) =
      β * ((κ.1 : Matrix (Fin V.rank) (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)).map (GlobalTheory.NJoin.tensCast hF).symm) * β') →
    (∀ κ, κ ∈ ReciprocityTheory.Aut.Umax D.host.E V.rank ↔ Ps.ψ κ ∈ Formalism.L2.Theta.KsphC V ∅) →
    ∀ (ε : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)
      (sec : sp.v.adicCompletion (maximalRealSubfield D.host.E) → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)
      (B : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)),
    (∀ t, sp.proj (GlobalTheory.NJoin.tensCast hF (sec t)) = t) →
    (∀ t ∈ sp.v.adicCompletionIntegers (maximalRealSubfield D.host.E), sec t ∈ Formalism.L2.Theta.intAE D) →
    (∀ x ∈ Formalism.L2.Theta.intAE D,
      sp.proj (GlobalTheory.NJoin.tensCast hF x) ∈ sp.v.adicCompletionIntegers (maximalRealSubfield D.host.E)) →
    sp.proj (GlobalTheory.NJoin.tensCast hF ε) = 1 →
    (∀ z, Formalism.IndefR.Mult.IntVec z → (fun a => ε * B.mulVec z a) ∈ Formalism.L2.NTheta.LamHat V) →
    (∀ y ∈ Formalism.L2.NTheta.LamHat V, ∃ z, Formalism.IndefR.Mult.IntVec z ∧ (fun a => ε * y a) = fun a => ε * B.mulVec z a) →
    ∀ g ∈ Formalism.UG.GLint (Fin V.rank) (Formalism.UG.Ov (maximalRealSubfield D.host.E) sp.v),
    ∀ z : Fin V.rank → sp.v.adicCompletion (maximalRealSubfield D.host.E),
      (∀ i, z i ∈ Formalism.UG.Ov (maximalRealSubfield D.host.E) sp.v) →
      ∃ z' : Fin V.rank → sp.v.adicCompletion (maximalRealSubfield D.host.E),
        (∀ i, z' i ∈ Formalism.UG.Ov (maximalRealSubfield D.host.E) sp.v) ∧
        (g : Matrix (Fin V.rank) (Fin V.rank) _).mulVec
            ((β'.map (fun x => sp.proj (GlobalTheory.NJoin.tensCast hF x)) *
              B.map (fun x => sp.proj (GlobalTheory.NJoin.tensCast hF x))).mulVec z) =
          (β'.map (fun x => sp.proj (GlobalTheory.NJoin.tensCast hF x)) *
              B.map (fun x => sp.proj (GlobalTheory.NJoin.tensCast hF x))).mulVec z' := by
  intro D hF V Ps sp β β' hββ' hβ'β hfr hK ε sec B hsec hsecI hint hε b1 b2 g hg z hz
  let φ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E →+*
      sp.v.adicCompletion (maximalRealSubfield D.host.E) :=
    sp.proj.comp (GlobalTheory.NJoin.tensCast hF).toRingHom
  have hfun : (fun x => sp.proj (GlobalTheory.NJoin.tensCast hF x)) = ⇑φ := rfl
  have hφε : φ ε = 1 := hε
  rw [hfun]
  obtain ⟨emb, htriv, hloc⟩ := GlobalTheory.SplitEmb.exists_hom_trivOutside_loc D.host.E V.rank sp
  have hκ : emb g ∈ ReciprocityTheory.Aut.Umax D.host.E V.rank :=
    GlobalTheory.SplitHeckeComm.mem_Umax_of_loc sp (emb g) (htriv g) (by rw [hloc]; exact hg)
  have hKs := (hK (emb g)).1 hκ
  have hz0 : Formalism.IndefR.Mult.IntVec (sec ∘ z) := fun i => hsecI _ (hz i)
  have hy := b1 _ hz0
  have hy' := (hKs.2.1 _).1 hy
  obtain ⟨z'', hz'', e⟩ := b2 _ hy'
  refine ⟨φ ∘ z'', fun i => hint _ (hz'' i), ?_⟩
  have mv : ∀ (M : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) x,
      φ ∘ (M.mulVec x) = (M.map φ).mulVec (φ ∘ x) := fun M x => funext fun i => RingHom.map_mulVec φ M x i
  have hε' : ∀ w : Fin V.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E,
      φ ∘ (fun a => ε * w a) = φ ∘ w := fun w => funext fun a => by
    simp only [Function.comp_apply, map_mul, hφε, one_mul]
  have hg' : (((emb g).1 : Matrix (Fin V.rank) (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)).map
      (GlobalTheory.NJoin.tensCast hF).symm).map φ = (g : Matrix (Fin V.rank) (Fin V.rank) _) := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.map_apply]
    show sp.proj (GlobalTheory.NJoin.tensCast hF ((GlobalTheory.NJoin.tensCast hF).symm _)) = _
    rw [RingEquiv.apply_symm_apply]
    conv_rhs => rw [← hloc g]
    rfl
  have hM : (Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram (Ps.ψ (emb g))).map φ =
      β.map φ * (g : Matrix (Fin V.rank) (Fin V.rank) _) * β'.map φ := by
    rw [hfr (emb g), Matrix.map_mul, Matrix.map_mul, hg']
  have hzφ : φ ∘ (sec ∘ z) = z := funext fun i => hsec _
  have hβ : β'.map φ * β.map φ = 1 := by
    rw [← Matrix.map_mul, hβ'β, Matrix.map_one _ (map_zero φ) (map_one φ)]
  have E := congrArg (fun w => φ ∘ w) e
  rw [hε', hε', mv, mv, hε', mv, hzφ, hM] at E
  have E2 := congrArg (fun w => (β'.map φ).mulVec w) E
  simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hβ, Matrix.one_mul] at E2
  simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc]
  exact E2

end GlobalTheory.SplitFrameLattice
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardFrameConjGLintLeSelfDualLatticeStabilizeStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardFrame_conj_GLint_le_selfDualLattice_stabilizer : ∀ {D : D7} (hF : D.host.F = maximalRealSubfield D.host.E) {V : TH.HSp D}
    (Ps : Formalism.IndefR.principalLevelFrame.RowPsi V V.rank) (sp : SplitPlace D.host.E)
    (β β' : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)),
    β * β' = 1 → β' * β = 1 →
    (∀ κ, Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram (Ps.ψ κ) =
      β * ((κ.1 : Matrix (Fin V.rank) (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)).map (GlobalTheory.NJoin.tensCast hF).symm) * β') →
    (∀ κ, κ ∈ ReciprocityTheory.Aut.Umax D.host.E V.rank ↔ Ps.ψ κ ∈ Formalism.L2.Theta.KsphC V ∅) →
    ∀ (ε : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)
      (sec : sp.v.adicCompletion (maximalRealSubfield D.host.E) → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)
      (B : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)),
    (∀ t, sp.proj (GlobalTheory.NJoin.tensCast hF (sec t)) = t) →
    (∀ t ∈ sp.v.adicCompletionIntegers (maximalRealSubfield D.host.E), sec t ∈ Formalism.L2.Theta.intAE D) →
    (∀ x ∈ Formalism.L2.Theta.intAE D,
      sp.proj (GlobalTheory.NJoin.tensCast hF x) ∈ sp.v.adicCompletionIntegers (maximalRealSubfield D.host.E)) →
    sp.proj (GlobalTheory.NJoin.tensCast hF ε) = 1 →
    (∀ z, Formalism.IndefR.Mult.IntVec z → (fun a => ε * B.mulVec z a) ∈ Formalism.L2.NTheta.LamHat V) →
    (∀ y ∈ Formalism.L2.NTheta.LamHat V, ∃ z, Formalism.IndefR.Mult.IntVec z ∧ (fun a => ε * y a) = fun a => ε * B.mulVec z a) →
    ∀ g ∈ Formalism.UG.GLint (Fin V.rank) (Formalism.UG.Ov (maximalRealSubfield D.host.E) sp.v),
    ∀ z : Fin V.rank → sp.v.adicCompletion (maximalRealSubfield D.host.E),
      (∀ i, z i ∈ Formalism.UG.Ov (maximalRealSubfield D.host.E) sp.v) →
      ∃ z' : Fin V.rank → sp.v.adicCompletion (maximalRealSubfield D.host.E),
        (∀ i, z' i ∈ Formalism.UG.Ov (maximalRealSubfield D.host.E) sp.v) ∧
        (g : Matrix (Fin V.rank) (Fin V.rank) _).mulVec
            ((β'.map (fun x => sp.proj (GlobalTheory.NJoin.tensCast hF x)) *
              B.map (fun x => sp.proj (GlobalTheory.NJoin.tensCast hF x))).mulVec z) =
          (β'.map (fun x => sp.proj (GlobalTheory.NJoin.tensCast hF x)) *
              B.map (fun x => sp.proj (GlobalTheory.NJoin.tensCast hF x))).mulVec z' := by
  first | exact @GlobalTheory.SplitFrameLattice.glint_mul_frame_basis | exact GlobalTheory.SplitFrameLattice.glint_mul_frame_basis | (intros; apply GlobalTheory.SplitFrameLattice.glint_mul_frame_basis <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegralSectionSplitPlaceComponentMap
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegralSectionSplitPlaceComponentMap
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct

namespace GlobalTheory.SplitComp

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem exists_integralSection_splitPlace_componentMap_cast {E : Type} [Field E] [NumberField E] [IsCMField E] (F1 : Subfield E)
    (hF : F1 = maximalRealSubfield E) (sp : SplitPlace E) :
    ∃ sec : sp.v.adicCompletion (maximalRealSubfield E) → FiniteAdeleRing (𝓞 F1) F1 ⊗[F1] E,
      (∀ t, sp.proj (Formalism.IndefR.principalLevelFrame.tensCastR hF (sec t)) = t) ∧
      (∀ t ∈ sp.v.adicCompletionIntegers (maximalRealSubfield E),
        sec t ∈ AddSubgroup.closure {y | ∃ a ∈ Formalism.MainNotions.StandardLattice.intAf F1, ∃ x : 𝓞 E, y = a ⊗ₜ[F1] (x : E)}) ∧
      (∀ x ∈ AddSubgroup.closure {y | ∃ a ∈ Formalism.MainNotions.StandardLattice.intAf F1, ∃ x : 𝓞 E, y = a ⊗ₜ[F1] (x : E)},
        sp.proj (Formalism.IndefR.principalLevelFrame.tensCastR hF x) ∈ sp.v.adicCompletionIntegers (maximalRealSubfield E)) ∧
      ∀ x : E, sp.proj (Formalism.IndefR.principalLevelFrame.tensCastR hF ((1 : FiniteAdeleRing (𝓞 F1) F1) ⊗ₜ[F1] x)) = sp.i x := by
  classical
  subst hF
  have hc : ∀ (a : FiniteAdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)) (x : E),
      Formalism.IndefR.principalLevelFrame.tensCastR (rfl : maximalRealSubfield E = maximalRealSubfield E)
        (a ⊗ₜ[maximalRealSubfield E] x) = x ⊗ₜ[maximalRealSubfield E] a := fun a x => rfl
  have hp : ∀ (a : FiniteAdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)) (x : E),
      sp.proj (x ⊗ₜ[maximalRealSubfield E] a) = sp.i x * a sp.v := fun a x => rfl
  refine ⟨fun t => singleV (maximalRealSubfield E) sp.v t ⊗ₜ[maximalRealSubfield E] (1 : E), ?_, ?_, ?_, ?_⟩
  · intro t
    rw [hc, hp, map_one, one_mul]
    exact RestrictedProduct.single_eq_same _ _ _
  · intro t ht
    apply AddSubgroup.subset_closure
    refine ⟨singleV (maximalRealSubfield E) sp.v t, ?_, 1, by simp⟩
    intro w
    show (singleV (maximalRealSubfield E) sp.v t) w ∈ _
    by_cases h : w = sp.v
    · subst h
      have e : (singleV (maximalRealSubfield E) sp.v t) sp.v = t := RestrictedProduct.single_eq_same _ _ _
      rw [e]
      exact ht
    · have e : (singleV (maximalRealSubfield E) sp.v t) w = 0 := RestrictedProduct.single_eq_of_ne _ _ h
      rw [e]
      exact zero_mem _
  · intro x hx
    induction hx using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, z, rfl⟩ := hy
      rw [hc, hp]
      refine mul_mem ?_ (ha sp.v)
      exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (sp.split_le_one z)
    | zero => simp
    | add y z _ _ hy hz =>
      rw [map_add (f := _), map_add (f := _)]
      exact add_mem hy hz
    | neg y _ hy =>
      rw [map_neg, map_neg]
      exact neg_mem hy
  · intro x
    rw [hc, hp]
    show sp.i x * 1 = sp.i x
    exact mul_one _

theorem proj_tensCast_section : ∀ (D : D7) (sp : SplitPlace D.host.E) (hF : D.host.F = maximalRealSubfield D.host.E),
    ∃ sec : sp.v.adicCompletion (maximalRealSubfield D.host.E) → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E,
      (∀ t, sp.proj (GlobalTheory.NJoin.tensCast hF (sec t)) = t) ∧
      (∀ t ∈ sp.v.adicCompletionIntegers (maximalRealSubfield D.host.E), sec t ∈ Formalism.L2.Theta.intAE D) ∧
      (∀ x ∈ Formalism.L2.Theta.intAE D,
        sp.proj (GlobalTheory.NJoin.tensCast hF x) ∈ sp.v.adicCompletionIntegers (maximalRealSubfield D.host.E)) ∧
      ∀ x : D.host.E, sp.proj (GlobalTheory.NJoin.tensCast hF (Formalism.L2.Theta.finPart D (Formalism.L2.Theta.incA D x))) = sp.i x := by
  intro D sp hF
  obtain ⟨sec, h1, h2, h3, h4⟩ := exists_integralSection_splitPlace_componentMap_cast D.host.F hF sp
  refine ⟨sec, h1, h2, h3, fun x => ?_⟩
  have e : Formalism.L2.Theta.finPart D (Formalism.L2.Theta.incA D x) = (1 : Af D.host.F) ⊗ₜ[D.host.F] x := by
    simp [Formalism.L2.Theta.finPart, Formalism.L2.Theta.incA, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR, Algebra.TensorProduct.map_tmul]
  rw [e]
  exact h4 x

end GlobalTheory.SplitComp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegralSectionSplitPlaceComponentMapStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralSection_splitPlace_componentMap : ∀ (D : D7) (sp : SplitPlace D.host.E) (hF : D.host.F = maximalRealSubfield D.host.E),
    ∃ sec : sp.v.adicCompletion (maximalRealSubfield D.host.E) → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E,
      (∀ t, sp.proj (GlobalTheory.NJoin.tensCast hF (sec t)) = t) ∧
      (∀ t ∈ sp.v.adicCompletionIntegers (maximalRealSubfield D.host.E), sec t ∈ Formalism.L2.Theta.intAE D) ∧
      (∀ x ∈ Formalism.L2.Theta.intAE D,
        sp.proj (GlobalTheory.NJoin.tensCast hF x) ∈ sp.v.adicCompletionIntegers (maximalRealSubfield D.host.E)) ∧
      ∀ x : D.host.E, sp.proj (GlobalTheory.NJoin.tensCast hF (Formalism.L2.Theta.finPart D (Formalism.L2.Theta.incA D x))) = sp.i x := by
  first | exact @GlobalTheory.SplitComp.proj_tensCast_section | exact GlobalTheory.SplitComp.proj_tensCast_section | (intros; apply GlobalTheory.SplitComp.proj_tensCast_section <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardElementSplitPlaceLabel
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct

namespace GlobalTheory.StdEltLabel

set_option maxHeartbeats 4000000 in
theorem std_elt_label : ∀ {D : D7} (hF : D.host.F = maximalRealSubfield D.host.E) {V : TH.HSp D} {n : ℕ} (Ps : Formalism.IndefR.principalLevelFrame.RowPsi V n), GlobalTheory.NJoin.StdFrame hF Ps → V.rank = n → ∀ (sp : SplitPlace D.host.E) (ϖ : (sp.v).adicCompletion (maximalRealSubfield D.host.E)), Formalism.AUTREP.IsUnif D.host.E sp.v ϖ → ∀ k ≤ n, ∃ x₀ ∈ Formalism.AUTREP.tSet D.host.E n sp ϖ k, ∃ (e f : Formalism.L2.Theta.AE D) (ϖ' : 𝓞 D.host.E), Formalism.IndefR.Mult.IsPrimeIdem sp.w e f ∧ ϖ' ∈ sp.w.asIdeal ∧ ϖ' ∉ sp.w.asIdeal ^ 2 ∧ Formalism.IndefR.Mult.SuppF V f (Ps.ψ x₀) ∧ Formalism.IndefR.Mult.DivAt V e (ϖ' : D.host.E) (List.replicate k 1 ++ List.replicate (n - k) 0) (Ps.ψ x₀) := by
  intro D hF V n Ps hS hn sp ϖ hϖ k hk
  subst hn
  classical
  obtain ⟨⟨β, β', h1, h2, hm⟩, hK⟩ := id hS
  have hϖ0 : ϖ ≠ 0 := by
    intro h0
    have := hϖ
    rw [Formalism.AUTREP.IsUnif, h0, map_zero] at this
    exact WithZero.zero_ne_coe this
  let g0 : GL (Fin V.rank) (sp.v.adicCompletion (maximalRealSubfield D.host.E)) :=
    ⟨Formalism.UG.diagJ V.rank ϖ k, Matrix.diagonal (fun i => if (i : ℕ) < k then ϖ⁻¹ else 1),
      by
        rw [Formalism.UG.diagJ, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
        congr 1; funext i; split_ifs <;> simp [hϖ0],
      by
        rw [Formalism.UG.diagJ, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
        congr 1; funext i; split_ifs <;> simp [hϖ0]⟩
  obtain ⟨emb, hembT, hembL⟩ := GlobalTheory.SplitEmb.exists_hom_trivOutside_loc D.host.E V.rank sp
  have hx₀ : emb g0 ∈ Formalism.AUTREP.tSet D.host.E V.rank sp ϖ k :=
    ⟨hembT g0, 1, one_mem _, 1, one_mem _, by rw [hembL]; simp [g0]⟩
  obtain ⟨p, c, hpl, -, -, hπ⟩ := GlobalTheory.T.exists_splitLocalPlaceData_at_splitPlace D sp hF
  have hidem : Formalism.L2.NTheta.IsIdemAt p.e sp.w := ⟨p.split, hpl.2.2⟩
  have hprime : Formalism.IndefR.Mult.IsPrimeIdem sp.w p.e (p.e + Formalism.L2.Theta.cA D p.e) := Or.inl ⟨hidem, rfl⟩
  obtain ⟨y, hy1, hy2, hyu⟩ := GlobalTheory.T.exists_realSubfield_uniformizer_at_splitPlace sp
  refine ⟨emb g0, hx₀, p.e, p.e + Formalism.L2.Theta.cA D p.e, y, hprime, hy1, hy2,
    (GlobalTheory.LabelTransport.suppF_iff_trivOutside D sp hF V V.rank Ps hS _ _ hprime (emb g0)).2 (hembT g0), ?_⟩
  obtain ⟨sec, hs, hO', hO, hinc⟩ := GlobalTheory.T.exists_integralSection_splitPlace_componentMap D sp hF
  obtain ⟨hε, hker⟩ := GlobalTheory.T.splitPlaceIdempotent_component_one_determines_part D sp hF p c hπ
  let φ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E →+* sp.v.adicCompletion (maximalRealSubfield D.host.E) :=
    sp.proj.comp (GlobalTheory.NJoin.tensCast hF).toRingHom
  have hφ : ∀ x, φ x = sp.proj (GlobalTheory.NJoin.tensCast hF x) := fun x => rfl
  have he : p.e * p.e = p.e := p.split.1
  obtain ⟨B, b1, b2⟩ := GlobalTheory.SphLabelOps.exists_basis (P := sp.w) V he (GlobalTheory.SphLabelOps.tie_of_isPrimeIdem hprime)
  have hee : Formalism.L2.Theta.finPart D p.e * Formalism.L2.Theta.finPart D p.e = Formalism.L2.Theta.finPart D p.e := by
    rw [← map_mul, he]
  obtain ⟨C, c1, c2⟩ := (GlobalTheory.LatIntFacts.int_facts V).2.2 _ B hee fun y hy => (b2 y hy).imp fun _ h => h.2
  have mp : ∀ X Y : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E),
      Formalism.L2.Theta.finPart D p.e • (X * Y) = Formalism.L2.Theta.finPart D p.e • (1 : Matrix (Fin V.rank) (Fin V.rank) _) →
        X.map φ * Y.map φ = 1 := by
    intro X Y hXY
    rw [← Matrix.map_mul, ← Matrix.map_one φ (map_zero φ) (map_one φ)]
    refine Matrix.ext fun i j => ?_
    have := congrArg φ (congrFun (congrFun hXY i) j)
    rwa [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, map_mul, hφ, hε, one_mul,
      one_mul] at this
  have hBC := mp _ _ c1
  have hCB := mp _ _ c2
  have hββ' : β.map φ * β'.map φ = 1 := by
    rw [← Matrix.map_mul, h1, Matrix.map_one φ (map_zero φ) (map_one φ)]
  have hβ'β : β'.map φ * β.map φ = 1 := by
    rw [← Matrix.map_mul, h2, Matrix.map_one φ (map_zero φ) (map_one φ)]
  obtain ⟨N, hNdef⟩ : ∃ N : GL (Fin V.rank) (sp.v.adicCompletion (maximalRealSubfield D.host.E)),
      (N : Matrix (Fin V.rank) (Fin V.rank) _) = β'.map φ * B.map φ :=
    ⟨⟨β'.map φ * B.map φ, C.map φ * β.map φ,
      by rw [Matrix.mul_assoc, ← Matrix.mul_assoc (B.map φ), hBC, Matrix.one_mul, hβ'β],
      by rw [Matrix.mul_assoc, ← Matrix.mul_assoc (β.map φ), hββ', Matrix.one_mul, hCB]⟩, rfl⟩
  have hlat := GlobalTheory.T.standardFrame_conj_GLint_le_selfDualLattice_stabilizer hF Ps sp β β' h1 h2 hm hK (Formalism.L2.Theta.finPart D p.e) sec B hs hO' hO hε b1 b2
  obtain ⟨k₁, hk₁, k₂, hk₂, hkk⟩ := GlobalTheory.T.normaliser_GLint_conj_eq_two_sided_GLint_mul _ sp.v V.rank N (by rw [hNdef]; exact hlat) (Formalism.UG.diagJ V.rank ϖ k)
  obtain ⟨T, hT, hTe⟩ := GlobalTheory.T.diagUniformizerBlock_eq_diagonal_pow_mul_integralGL _ sp.v V.rank k ϖ (sp.i (y : D.host.E)) hϖ hyu
  rw [GlobalTheory.DivDual.divAt_iff]
  refine ⟨by simp [hk], ?_⟩
  have hk₂' : T * k₂ ∈ Formalism.UG.GLint (Fin V.rank) (Formalism.UG.Ov (maximalRealSubfield D.host.E) sp.v) := mul_mem hT hk₂
  refine GlobalTheory.SphLabelOps.dv_of_cartan (OK := Formalism.UG.Ov (maximalRealSubfield D.host.E) sp.v) φ sec hs hε hker
    (fun x hx => hO x hx) (fun t ht => hO' t ht) b1 b2
    (Formalism.UG.P.cartan_entries_of_mem _ _ hk₁) (Formalism.UG.P.cartan_entries_of_mem _ _ (inv_mem hk₁))
    (Formalism.UG.P.cartan_entries_of_mem _ _ hk₂') (Formalism.UG.P.cartan_entries_of_mem _ _ (inv_mem hk₂')) ?_
  have hdiag : (Matrix.diagonal fun i : Fin V.rank => φ (Formalism.L2.Theta.finPart D (Formalism.L2.Theta.incA D
      ((y : D.host.E) ^ ((List.replicate k (1 : ℤ) ++ List.replicate (V.rank - k) 0).getD i.1 0))))) =
      Matrix.diagonal (fun i : Fin V.rank => sp.i (y : D.host.E) ^
        ((List.replicate k (1 : ℤ) ++ List.replicate (V.rank - k) 0).getD i.1 0)) := by
    congr 1; funext i; rw [hφ, hinc, map_zpow₀]
  have hA : (Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram (Ps.ψ (emb g0))).map φ =
      β.map φ * Formalism.UG.diagJ V.rank ϖ k * β'.map φ := by
    rw [hm, Matrix.map_mul, Matrix.map_mul]
    congr 2
    have e2 : ((emb g0).1 : Matrix (Fin V.rank) (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)).map sp.proj =
        Formalism.UG.diagJ V.rank ϖ k := congrArg Units.val (hembL g0)
    rw [← e2, Matrix.map_map]
    congr 1
    funext x
    simp [φ]
  have hBN : B.map φ = β.map φ * (N : Matrix (Fin V.rank) (Fin V.rank) _) := by
    rw [hNdef, ← Matrix.mul_assoc, hββ', Matrix.one_mul]
  have hNN : (N : Matrix (Fin V.rank) (Fin V.rank) _) *
      (N⁻¹).val = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [hdiag, hA, hBN]
  calc β.map φ * Formalism.UG.diagJ V.rank ϖ k * β'.map φ * (β.map φ * (N : Matrix (Fin V.rank) (Fin V.rank) _))
      = β.map φ * Formalism.UG.diagJ V.rank ϖ k * (N : Matrix (Fin V.rank) (Fin V.rank) _) := by
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc (β'.map φ), hβ'β, Matrix.one_mul]
    _ = β.map φ * ((N : Matrix (Fin V.rank) (Fin V.rank) _) *
          ((N⁻¹).val *
            Formalism.UG.diagJ V.rank ϖ k * (N : Matrix (Fin V.rank) (Fin V.rank) _))) := by
        have e3 : (N : Matrix (Fin V.rank) (Fin V.rank) _) * ((N⁻¹).val * Formalism.UG.diagJ V.rank ϖ k * (N : Matrix (Fin V.rank) (Fin V.rank) _)) =
            Formalism.UG.diagJ V.rank ϖ k * (N : Matrix (Fin V.rank) (Fin V.rank) _) := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hNN, Matrix.one_mul]
        rw [e3, Matrix.mul_assoc]
    _ = _ := by
        rw [hkk, hTe]
        simp only [Units.val_mul, Matrix.mul_assoc]

end GlobalTheory.StdEltLabel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardElementSplitPlaceLabelStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardElement_splitPlace_label : ∀ {D : D7} (hF : D.host.F = maximalRealSubfield D.host.E) {V : TH.HSp D} {n : ℕ} (Ps : Formalism.IndefR.principalLevelFrame.RowPsi V n), GlobalTheory.NJoin.StdFrame hF Ps → V.rank = n → ∀ (sp : SplitPlace D.host.E) (ϖ : (sp.v).adicCompletion (maximalRealSubfield D.host.E)), Formalism.AUTREP.IsUnif D.host.E sp.v ϖ → ∀ k ≤ n, ∃ x₀ ∈ Formalism.AUTREP.tSet D.host.E n sp ϖ k, ∃ (e f : Formalism.L2.Theta.AE D) (ϖ' : 𝓞 D.host.E), Formalism.IndefR.Mult.IsPrimeIdem sp.w e f ∧ ϖ' ∈ sp.w.asIdeal ∧ ϖ' ∉ sp.w.asIdeal ^ 2 ∧ Formalism.IndefR.Mult.SuppF V f (Ps.ψ x₀) ∧ Formalism.IndefR.Mult.DivAt V e (ϖ' : D.host.E) (List.replicate k 1 ++ List.replicate (n - k) 0) (Ps.ψ x₀) := by
  first | exact @GlobalTheory.StdEltLabel.std_elt_label | exact GlobalTheory.StdEltLabel.std_elt_label | (intros; apply GlobalTheory.StdEltLabel.std_elt_label <;> assumption)
end
