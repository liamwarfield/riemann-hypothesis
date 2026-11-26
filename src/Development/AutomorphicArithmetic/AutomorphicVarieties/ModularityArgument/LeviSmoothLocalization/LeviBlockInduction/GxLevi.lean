module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.LeviBlockInduction.GxDefs

@[expose] public section

attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.LeviBlockInduction.GxMulti
noncomputable section

open MeasureTheory Measure GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Parabolic
open GroundTheory.Automorphic.GodementJacquet
open scoped NNReal ENNReal Classical ValuativeRel

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

set_option linter.unusedSectionVars false

namespace UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]
  [∀ n : ℕ, MeasurableSpace (GL (Fin n) F)] [∀ n : ℕ, BorelSpace (GL (Fin n) F)]
  {W : Type} [AddCommGroup W] [Module ℂ W]


variable (F W) in
def GxMulti (ψ : AddChar F Circle) (r : ℕ) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι = r →
  ∀ (d : ι → ℕ) [∀ i, NeZero (d i)] (μ : ∀ i, Measure (GL (Fin (d i)) F))
    [∀ i, (μ i).IsHaarMeasure]
    (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [T2Space H] [TotallyDisconnectedSpace H] [SecondCountableTopology H]
    (ρ : Representation ℂ ((∀ i, GL (Fin (d i)) F) × H) W), IsAdmissible ρ → ρ.IsIrreducible →
    ∀ α : ι → ℂ, (∀ i, α i ≠ 0) →
      (∀ i v, ρ (Pi.mulSingle i (centralUnif F (d i)), 1) v = α i • v) →
      (∀ v : W, ∀ ℓ ∈ smoothVectors (Representation.dual ρ),
        ∃ C : Set (∀ i, GL (Fin (d i)) F), IsCompact C ∧
          ∀ x, ℓ (ρ (x, 1) v) ≠ 0 → ∃ j : ι → ℤ, (fun i => centralUnif F (d i) ^ j i) * x ∈ C) →
    ∃ γ : RatFunc ℂ, GxShape ((GroundTheory.LocalField.residueCard F : ℕ) : ℂ) γ
        (∏ i, if d i = 1 ∧ ∀ g ∈ integralGL F (d i), ρ (Pi.mulSingle i g, 1) = 1 then
          1 - Polynomial.C (α i) * Polynomial.X else 1) ∧
      ∀ Ψ : ∀ i, Matrix (Fin (d i)) (Fin (d i)) F → ℂ,
      (∀ i, IsSchwartzBruhat (Ψ i)) → ∀ w : W, ∀ ℓ ∈ smoothVectors (Representation.dual ρ),
        RatFE F γ (fun s => ∫ x, multiA ρ Ψ w ℓ s x ∂Measure.pi μ)
          (fun s => ∫ x, multiB ρ (fun i => GJMatrix.localMatrixFourier ψ (Ψ i)) w ℓ s x
            ∂Measure.pi μ)

theorem gxMulti_zero (ψ : AddChar F Circle) : GxMulti F W ψ 0 := by
  intro ι _ _ hcard d _ μ _ H _ _ _ _ _ _ _ ρ _ _ α _ _ _
  have hempty : IsEmpty ι := Fintype.card_eq_zero_iff.1 hcard
  refine ⟨1, by simpa using gxShape_one _, fun Ψ _ w ℓ _ => ?_⟩
  have hval : ∀ f : (∀ i, GL (Fin (d i)) F) → ℂ,
      ∫ x, f x ∂Measure.pi μ = f 1 := by
    intro f
    have hu : (Measure.pi μ).real Set.univ = 1 := by
      rw [Measure.real, Measure.pi_of_empty μ (1 : ∀ i, GL (Fin (d i)) F), measure_univ,
        ENNReal.toReal_one]
    rw [integral_unique, hu, one_smul]
    congr 1
    exact Subsingleton.elim _ _
  refine ⟨RatFunc.C (ℓ w), 0, fun s _ => ?_, fun s _ => ?_⟩
  · show ∫ x, multiA ρ Ψ w ℓ s x ∂Measure.pi μ = _
    rw [hval, RatFunc.eval_C]
    simp only [multiA, Finset.univ_eq_empty, Finset.prod_empty, one_mul]
    rw [show ((1 : ∀ i, GL (Fin (d i)) F), (1 : H)) = 1 from rfl, map_one]
    rfl
  · show ∫ x, multiB ρ (fun i => GJMatrix.localMatrixFourier ψ (Ψ i)) w ℓ s x ∂Measure.pi μ = _
    rw [hval, one_mul, RatFunc.eval_C]
    simp only [multiB, Finset.univ_eq_empty, Finset.prod_empty, one_mul, inv_one]
    rw [show ((1 : ∀ i, GL (Fin (d i)) F), (1 : H)) = 1 from rfl, map_one]
    rfl

theorem gxMulti_succ (hB : GxBlock) {ψ : AddChar F Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {r : ℕ}
    (ih : GxMulti F W ψ r) : GxMulti F W ψ (r + 1) := by
  intro ι _ _ hcard d _ μ _ H _ _ _ _ _ _ _ ρ hadm hirr α hα0 hα hsupp
  obtain ⟨a⟩ : Nonempty ι := Fintype.card_pos_iff.1 (by omega)

  set ρ₁ : Representation ℂ (GL (Fin (d a)) F × ((∀ i : {i // i ≠ a}, GL (Fin (d i)) F) × H)) W :=
    ρ.comp (peelFst d H a).symm.toMonoidHom with hρ₁def
  set ρ₂ : Representation ℂ ((∀ i : {i // i ≠ a}, GL (Fin (d i)) F) × (GL (Fin (d a)) F × H)) W :=
    ρ.comp (peelSnd d H a).symm.toMonoidHom with hρ₂def
  have hρ₁ : ∀ g y h, ρ₁ (g, (y, h)) = ρ (splitSymm d a g y, h) := fun g y h => by
    rw [hρ₁def, MonoidHom.comp_apply]
    exact congrArg ρ (peelFst_symm_apply d H a (g, (y, h)))
  have hρ₂ : ∀ y g h, ρ₂ (y, (g, h)) = ρ (splitSymm d a g y, h) := fun y g h => by
    rw [hρ₂def, MonoidHom.comp_apply]
    exact congrArg ρ (peelSnd_symm_apply d H a (y, (g, h)))
  have hadm₁ : IsAdmissible ρ₁ := (isAdmissible_comp_iff (peelFst d H a).symm ρ).2 hadm
  have hadm₂ : IsAdmissible ρ₂ := (isAdmissible_comp_iff (peelSnd d H a).symm ρ).2 hadm
  have hirr₁ : ρ₁.IsIrreducible := (isIrreducible_comp_iff (peelFst d H a).symm ρ).2 hirr
  have hirr₂ : ρ₂.IsIrreducible := (isIrreducible_comp_iff (peelSnd d H a).symm ρ).2 hirr
  have hsm₁ : ∀ ℓ : Module.Dual ℂ W, ℓ ∈ smoothVectors (Representation.dual ρ₁) ↔
      ℓ ∈ smoothVectors (Representation.dual ρ) := fun ℓ =>
    mem_smoothVectors_dual_comp_iff (peelFst d H a).symm ρ
  have hsm₂ : ∀ ℓ : Module.Dual ℂ W, ℓ ∈ smoothVectors (Representation.dual ρ₂) ↔
      ℓ ∈ smoothVectors (Representation.dual ρ) := fun ℓ =>
    mem_smoothVectors_dual_comp_iff (peelSnd d H a).symm ρ

  have hα₁ : ∀ v, ρ₁ (centralUnif F (d a), 1) v = α a • v := by
    intro v
    change ρ₁ (centralUnif F (d a), ((1 : ∀ i : {i // i ≠ a}, GL (Fin (d i)) F), (1 : H))) v = _
    rw [hρ₁, splitSymm_mulSingle_self]
    exact hα a v
  have hsupp₁ : ∀ v : W, ∀ ℓ ∈ smoothVectors (Representation.dual ρ₁),
      ∃ C : Set (GL (Fin (d a)) F), IsCompact C ∧
        ∀ g, ℓ (ρ₁ (g, 1) v) ≠ 0 → ∃ j : ℤ, centralUnif F (d a) ^ j * g ∈ C := by
    intro v ℓ hℓ
    obtain ⟨C, hC, hCs⟩ := hsupp v ℓ ((hsm₁ ℓ).1 hℓ)
    refine ⟨(fun x : ∀ i, GL (Fin (d i)) F => x a) '' C, hC.image (continuous_apply a),
      fun g hg => ?_⟩
    change ℓ (ρ₁ (g, ((1 : ∀ i : {i // i ≠ a}, GL (Fin (d i)) F), (1 : H))) v) ≠ 0 at hg
    rw [hρ₁, splitSymm_mulSingle_self] at hg
    obtain ⟨j, hj⟩ := hCs _ hg
    exact ⟨j a, _, hj, by simp [Pi.mul_apply]⟩
  obtain ⟨γa, sa, hblock⟩ := exists_blockFE (μ a) hadm₁ hψ hψ1 hα₁ hsupp₁
  have hsh₁ := hB F (d a) (μ a) _ W ρ₁ hadm₁ hirr₁ (α a) (hα0 a) hα₁ hsupp₁ ψ hψ hψ1 γa
    (fun Φ hΦ v ℓ hℓ => (hblock Φ hΦ v ℓ hℓ).2.2)

  have hcard' : Fintype.card {i // i ≠ a} = r := by
    rw [Fintype.card_subtype, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ a),
      Finset.card_univ, hcard]
    rfl
  have hα₂ : ∀ (j : {i // i ≠ a}) v, ρ₂ (Pi.mulSingle j (centralUnif F (d j)), 1) v = α j • v := by
    intro j v
    change ρ₂ (Pi.mulSingle j (centralUnif F (d j)), ((1 : GL (Fin (d a)) F), (1 : H))) v = _
    rw [hρ₂, splitSymm_one_mulSingle]
    exact hα j v
  have hsupp₂ : ∀ v : W, ∀ ℓ ∈ smoothVectors (Representation.dual ρ₂),
      ∃ C : Set (∀ i : {i // i ≠ a}, GL (Fin (d i)) F), IsCompact C ∧
        ∀ y, ℓ (ρ₂ (y, 1) v) ≠ 0 →
          ∃ j : {i // i ≠ a} → ℤ,
            (fun i : {i // i ≠ a} => centralUnif F (d i) ^ j i) * y ∈ C := by
    intro v ℓ hℓ
    obtain ⟨C, hC, hCs⟩ := hsupp v ℓ ((hsm₂ ℓ).1 hℓ)
    refine ⟨(fun x : ∀ i, GL (Fin (d i)) F => fun k : {i // i ≠ a} => x k) '' C,
      hC.image (continuous_pi fun k => continuous_apply (k : ι)), fun y hy => ?_⟩
    change ℓ (ρ₂ (y, ((1 : GL (Fin (d a)) F), (1 : H))) v) ≠ 0 at hy
    rw [hρ₂] at hy
    obtain ⟨j, hj⟩ := hCs _ hy
    refine ⟨fun k => j k, _, hj, ?_⟩
    funext k
    exact centralPow_mul_splitSymm_apply j y k
  obtain ⟨γ', hsh₂, hIH⟩ := ih {i // i ≠ a} hcard' (fun j => d j) (fun j => μ j) (GL (Fin (d a)) F × H) ρ₂
    hadm₂ hirr₂ (fun j => α j) (fun j => hα0 j) hα₂ hsupp₂

  obtain ⟨s₀, hconv⟩ := exists_integrable_multi ρ hadm.1 hα0 hα hsupp μ
  obtain ⟨s₂, hconv₂⟩ := exists_integrable_multi ρ₂ hadm₂.1 (fun j => hα0 j) hα₂ hsupp₂
    (fun j => μ j)
  refine ⟨γa * γ', ?_, fun Ψ hΨ w ℓ hℓ => ?_⟩
  · have e₁ : ∀ g : GL (Fin (d a)) F, ρ₁ (g, 1) = ρ (Pi.mulSingle a g, 1) := fun g => by
      change ρ₁ (g, ((1 : ∀ i : {i // i ≠ a}, GL (Fin (d i)) F), (1 : H))) = _
      rw [hρ₁, splitSymm_mulSingle_self]
    have e₂ : ∀ (j : {i // i ≠ a}) (g : GL (Fin (d j)) F),
        ρ₂ (Pi.mulSingle j g, 1) = ρ (Pi.mulSingle (j : ι) g, 1) := fun j g => by
      change ρ₂ (Pi.mulSingle j g, ((1 : GL (Fin (d a)) F), (1 : H))) = _
      rw [hρ₂, splitSymm_one_mulSingle]
    rw [Fintype.prod_eq_mul_prod_subtype_ne _ a]
    simp only [e₁, e₂] at hsh₁ hsh₂
    exact gxShape_mul hsh₁ hsh₂
  have hℓ₁ : ℓ ∈ smoothVectors (Representation.dual ρ₁) := (hsm₁ ℓ).2 hℓ
  have hℓ₂ : ℓ ∈ smoothVectors (Representation.dual ρ₂) := (hsm₂ ℓ).2 hℓ

  obtain ⟨m₀, hm₀⟩ := (hΨ a).exists_congruence_invariant
  have hw₁ : w ∈ smoothVectors ρ₁ := hadm₁.1 w
  have hnhds : (stabilizerOf ρ₁ w : Set (GL (Fin (d a)) F × ((∀ i : {i // i ≠ a},
      GL (Fin (d i)) F) × H))) ∈ nhds ((1 : GL (Fin (d a)) F),
        (1 : (∀ i : {i // i ≠ a}, GL (Fin (d i)) F) × H)) :=
    (mem_smoothVectors.1 hw₁).mem_nhds (one_mem (stabilizerOf ρ₁ w))
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.1 hnhds
  obtain ⟨Ka, hKac, hKaU⟩ := exists_openSubgroup_isCompact_subset
    (Filter.inter_mem hU ((isOpen_congruenceSubgroup F (d a) m₀).mem_nhds (one_mem _)))
  obtain ⟨K', hK'c, hK'V⟩ := exists_openSubgroup_isCompact_subset hV
  set K := (Ka : Subgroup (GL (Fin (d a)) F)).prod
    (K' : Subgroup ((∀ i : {i // i ≠ a}, GL (Fin (d i)) F) × H)) with hKdef
  have hKc : IsCompact (K : Set (GL (Fin (d a)) F × ((∀ i : {i // i ≠ a}, GL (Fin (d i)) F) × H))) := by
    rw [hKdef, Subgroup.coe_prod]
    exact hKac.prod hK'c
  have hKo : IsOpen (K : Set (GL (Fin (d a)) F × ((∀ i : {i // i ≠ a}, GL (Fin (d i)) F) × H))) := by
    rw [hKdef, Subgroup.coe_prod]
    exact Ka.isOpen.prod K'.isOpen
  have hKa : (Ka : Subgroup (GL (Fin (d a)) F)) ≤ integralGL F (d a) := fun k hk =>
    congruenceSubgroup_le F (d a) m₀ (hKaU hk).2
  have hΨa : ∀ k ∈ (Ka : Subgroup (GL (Fin (d a)) F)), ∀ X,
      Ψ a ((k : Matrix (Fin (d a)) (Fin (d a)) F) * X) = Ψ a X := fun k hk X =>
    (hm₀ k (hKaU hk).2 X).1
  have hΦa : ∀ k ∈ (Ka : Subgroup (GL (Fin (d a)) F)), ∀ X,
      GJMatrix.localMatrixFourier ψ (Ψ a) (X * (k : Matrix (Fin (d a)) (Fin (d a)) F)) =
        GJMatrix.localMatrixFourier ψ (Ψ a) X := fun k hk X =>
    localMatrixFourier_mul_right_of_invariant (hKa hk)
      (fun x => (hm₀ k⁻¹ (inv_mem (hKaU hk).2) x).1) X
  have hwK : w ∈ fixedVectors ρ₁ K := fun k hk =>
    hUV ⟨(hKaU (Subgroup.mem_prod.1 hk).1).1, hK'V (Subgroup.mem_prod.1 hk).2⟩
  have : FiniteDimensional ℂ (fixedVectors ρ₁ K) := hadm₁.2 K hKc hKo
  set b := Module.finBasis ℂ (fixedVectors ρ₁ K) with hb
  set L : Fin (Module.finrank ℂ (fixedVectors ρ₁ K)) → Module.Dual ℂ W := fun i =>
    (((extendFixed hadm₁.1 hKc hKo (b.coord i) : fixedVectors (contragredient ρ₁) K) :
      smoothVectors (Representation.dual ρ₁)) : Module.Dual ℂ W) with hL
  have hLsm : ∀ i, L i ∈ smoothVectors (Representation.dual ρ₁) := fun i =>
    ((extendFixed hadm₁.1 hKc hKo (b.coord i) : fixedVectors (contragredient ρ₁) K) :
      smoothVectors (Representation.dual ρ₁)).2

  have hmp := measurePreserving_piSplitAt d a μ
  have hemb : MeasurableEmbedding (Equiv.piSplitAt a fun i => GL (Fin (d i)) F) :=
    (Homeomorph.piSplitAt a fun i => GL (Fin (d i)) F).toMeasurableEquiv.measurableEmbedding
  have hprod1 : ∀ (g : GL (Fin (d a)) F) (y : ∀ i : {i // i ≠ a}, GL (Fin (d i)) F) (h : H),
      ρ (splitSymm d a g y, h) = ρ₁ (1, (y, h)) * ρ₁ (g, 1) := by
    intro g y h
    rw [← map_mul, ← hρ₁]
    congr 1
    ext1 <;> simp

  have hA : ∀ s : ℂ, max sa (max s₀ s₂) < s.re →
      ∫ x, multiA ρ Ψ w ℓ s x ∂Measure.pi μ =
        ∑ i, blockA (μ a) ρ₁ (Ψ a) w (L i) s *
          ∫ y, multiA ρ₂ (fun j : {i // i ≠ a} => Ψ j) (b i : W) ℓ s y
            ∂Measure.pi (fun j : {i // i ≠ a} => μ j) := by
    intro s hs
    simp only [max_lt_iff] at hs
    obtain ⟨hsa, hs₀, hs₂⟩ := hs
    have hint := (hconv Ψ hΨ w ℓ hℓ).1 s hs₀
    set G : GL (Fin (d a)) F × (∀ j : {i // i ≠ a}, GL (Fin (d j)) F) → ℂ :=
      fun p => multiA ρ Ψ w ℓ s (splitSymm d a p.1 p.2) with hG
    have hGF : ∀ x, G (Equiv.piSplitAt a (fun i => GL (Fin (d i)) F) x) = multiA ρ Ψ w ℓ s x :=
      fun x => by
        simp only [hG]
        rw [show splitSymm d a (Equiv.piSplitAt a (fun i => GL (Fin (d i)) F) x).1
          (Equiv.piSplitAt a (fun i => GL (Fin (d i)) F) x).2 = x from
            (Equiv.piSplitAt a fun i => GL (Fin (d i)) F).symm_apply_apply x]
    have hGint : Integrable G ((μ a).prod (Measure.pi fun j : {i // i ≠ a} => μ j)) := by
      rw [← hmp.integrable_comp_emb hemb]
      exact hint.congr (Filter.Eventually.of_forall fun x => (hGF x).symm)
    have hinner : ∀ y : ∀ j : {i // i ≠ a}, GL (Fin (d j)) F, ∫ g, G (g, y) ∂(μ a) =
        ∑ i, blockA (μ a) ρ₁ (Ψ a) w (L i) s *
          multiA ρ₂ (fun j : {i // i ≠ a} => Ψ j) (b i : W) ℓ s y := by
      intro y
      set μy : smoothVectors (Representation.dual ρ₁) :=
        contragredient ρ₁ ((1 : GL (Fin (d a)) F), (y, (1 : H)))⁻¹ ⟨ℓ, hℓ₁⟩ with hμy
      have hμyv : ∀ v, (μy : Module.Dual ℂ W) v = ℓ (ρ₁ ((1 : GL (Fin (d a)) F), (y, (1 : H))) v) :=
        fun v => by rw [hμy, contragredient_apply_apply, inv_inv]
      set P : ℂ := ∏ j : {i // i ≠ a}, Ψ j (y j : Matrix (Fin (d j)) (Fin (d j)) F) *
        detPow (y j) s with hP
      have hGy : ∀ g, G (g, y) = P * (Ψ a (g : Matrix (Fin (d a)) (Fin (d a)) F) * detPow g s *
          (μy : Module.Dual ℂ W) (ρ₁ (g, 1) w)) := fun g => by
        simp only [hG, multiA]
        rw [prod_splitSymm (fun i x => Ψ i (x : Matrix (Fin (d i)) (Fin (d i)) F) * detPow x s) g y,
          hprod1, Module.End.mul_apply, hμyv]
        ring
      simp_rw [hGy]
      rw [integral_const_mul]
      have hblockA := blockA_eq_sum (μ₀ := μ a) hadm₁.1 hKc hKo hKa hΨa hwK
        (fun ν hν => (hblock (Ψ a) (hΨ a) w ν hν).1 s hsa) μy
      rw [show ∫ g, Ψ a (g : Matrix (Fin (d a)) (Fin (d a)) F) * detPow g s *
          (μy : Module.Dual ℂ W) (ρ₁ (g, 1) w) ∂(μ a) = blockA (μ a) ρ₁ (Ψ a) w μy s from rfl,
        hblockA, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hμyv]
      simp only [multiA]
      rw [show ρ₁ ((1 : GL (Fin (d a)) F), (y, (1 : H))) = ρ₂ (y, ((1 : GL (Fin (d a)) F), (1 : H))) by
        rw [hρ₁, hρ₂]]
      change P * (ℓ (ρ₂ (y, ((1 : GL (Fin (d a)) F), (1 : H))) (b i : W)) *
        blockA (μ a) ρ₁ (Ψ a) w (L i) s) = _
      rw [hP, show ((1 : GL (Fin (d a)) F), (1 : H)) = (1 : GL (Fin (d a)) F × H) from rfl]
      ring
    calc ∫ x, multiA ρ Ψ w ℓ s x ∂Measure.pi μ
        = ∫ x, G (Equiv.piSplitAt a (fun i => GL (Fin (d i)) F) x) ∂Measure.pi μ := by
          simp_rw [hGF]
      _ = ∫ p, G p ∂((μ a).prod (Measure.pi fun j : {i // i ≠ a} => μ j)) :=
          hmp.integral_comp hemb G
      _ = ∫ y, ∫ g, G (g, y) ∂(μ a) ∂(Measure.pi fun j : {i // i ≠ a} => μ j) :=
          integral_prod_symm G hGint
      _ = ∫ y, ∑ i, blockA (μ a) ρ₁ (Ψ a) w (L i) s *
            multiA ρ₂ (fun j : {i // i ≠ a} => Ψ j) (b i : W) ℓ s y
            ∂(Measure.pi fun j : {i // i ≠ a} => μ j) :=
          integral_congr_ae (Filter.Eventually.of_forall hinner)
      _ = _ := by
          rw [integral_finsetSum _ fun i _ =>
            ((hconv₂ (fun j : {i // i ≠ a} => Ψ j) (fun j => hΨ j) (b i : W) ℓ hℓ₂).1 s
              hs₂).const_mul _]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [integral_const_mul]

  set Ψh : ∀ i, Matrix (Fin (d i)) (Fin (d i)) F → ℂ :=
    fun i => GJMatrix.localMatrixFourier ψ (Ψ i) with hΨhdef
  have hΨh : ∀ i, IsSchwartzBruhat (Ψh i) := fun i => (hΨ i).localMatrixFourier hψ hψ1
  have hB' : ∀ s : ℂ, s.re < -max sa (max s₀ s₂) →
      ∫ x, multiB ρ Ψh w ℓ s x ∂Measure.pi μ =
        ∑ i, blockB (μ a) ρ₁ (Ψh a) w (L i) s *
          ∫ y, multiB ρ₂ (fun j : {i // i ≠ a} => Ψh j) (b i : W) ℓ s y
            ∂Measure.pi (fun j : {i // i ≠ a} => μ j) := by
    intro s hs
    have hsa : s.re < -sa := lt_of_lt_of_le hs (neg_le_neg (le_max_left _ _))
    have hs₀ : s.re < -s₀ :=
      lt_of_lt_of_le hs (neg_le_neg ((le_max_left _ _).trans (le_max_right _ _)))
    have hs₂ : s.re < -s₂ :=
      lt_of_lt_of_le hs (neg_le_neg ((le_max_right _ _).trans (le_max_right _ _)))
    have hint := (hconv Ψh hΨh w ℓ hℓ).2 s hs₀
    set G : GL (Fin (d a)) F × (∀ j : {i // i ≠ a}, GL (Fin (d j)) F) → ℂ :=
      fun p => multiB ρ Ψh w ℓ s (splitSymm d a p.1 p.2) with hG
    have hGF : ∀ x, G (Equiv.piSplitAt a (fun i => GL (Fin (d i)) F) x) = multiB ρ Ψh w ℓ s x :=
      fun x => by
        simp only [hG]
        rw [show splitSymm d a (Equiv.piSplitAt a (fun i => GL (Fin (d i)) F) x).1
          (Equiv.piSplitAt a (fun i => GL (Fin (d i)) F) x).2 = x from
            (Equiv.piSplitAt a fun i => GL (Fin (d i)) F).symm_apply_apply x]
    have hGint : Integrable G ((μ a).prod (Measure.pi fun j : {i // i ≠ a} => μ j)) := by
      rw [← hmp.integrable_comp_emb hemb]
      exact hint.congr (Filter.Eventually.of_forall fun x => (hGF x).symm)
    have hinner : ∀ y : ∀ j : {i // i ≠ a}, GL (Fin (d j)) F, ∫ g, G (g, y) ∂(μ a) =
        ∑ i, blockB (μ a) ρ₁ (Ψh a) w (L i) s *
          multiB ρ₂ (fun j : {i // i ≠ a} => Ψh j) (b i : W) ℓ s y := by
      intro y
      set μy : smoothVectors (Representation.dual ρ₁) :=
        contragredient ρ₁ ((1 : GL (Fin (d a)) F), (y⁻¹, (1 : H)))⁻¹ ⟨ℓ, hℓ₁⟩ with hμy
      have hμyv : ∀ v, (μy : Module.Dual ℂ W) v =
          ℓ (ρ₁ ((1 : GL (Fin (d a)) F), (y⁻¹, (1 : H))) v) :=
        fun v => by rw [hμy, contragredient_apply_apply, inv_inv]
      set P : ℂ := ∏ j : {i // i ≠ a}, Ψh j (y j : Matrix (Fin (d j)) (Fin (d j)) F) *
        detPow (y j) ((d j : ℂ) - s) with hP
      have hGy : ∀ g, G (g, y) = P * (Ψh a (g : Matrix (Fin (d a)) (Fin (d a)) F) *
          detPow g ((d a : ℂ) - s) * (μy : Module.Dual ℂ W) (ρ₁ (g⁻¹, 1) w)) := fun g => by
        simp only [hG, multiB]
        rw [prod_splitSymm (fun i x => Ψh i (x : Matrix (Fin (d i)) (Fin (d i)) F) *
            detPow x ((d i : ℂ) - s)) g y, splitSymm_inv, hprod1, Module.End.mul_apply, hμyv]
        ring
      simp_rw [hGy]
      rw [integral_const_mul]
      have hblockB := blockB_eq_sum (μ₀ := μ a) hadm₁.1 hKc hKo hKa hΦa hwK
        (fun ν hν => (hblock (Ψ a) (hΨ a) w ν hν).2.1 s hsa) μy
      rw [show ∫ g, Ψh a (g : Matrix (Fin (d a)) (Fin (d a)) F) * detPow g ((d a : ℂ) - s) *
          (μy : Module.Dual ℂ W) (ρ₁ (g⁻¹, 1) w) ∂(μ a) = blockB (μ a) ρ₁ (Ψh a) w μy s from rfl,
        hblockB, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hμyv]
      simp only [multiB]
      rw [show ρ₁ ((1 : GL (Fin (d a)) F), (y⁻¹, (1 : H))) =
          ρ₂ (y⁻¹, ((1 : GL (Fin (d a)) F), (1 : H))) by rw [hρ₁, hρ₂]]
      change P * (ℓ (ρ₂ (y⁻¹, ((1 : GL (Fin (d a)) F), (1 : H))) (b i : W)) *
        blockB (μ a) ρ₁ (Ψh a) w (L i) s) = _
      rw [hP, show ((1 : GL (Fin (d a)) F), (1 : H)) = (1 : GL (Fin (d a)) F × H) from rfl]
      ring
    calc ∫ x, multiB ρ Ψh w ℓ s x ∂Measure.pi μ
        = ∫ x, G (Equiv.piSplitAt a (fun i => GL (Fin (d i)) F) x) ∂Measure.pi μ := by
          simp_rw [hGF]
      _ = ∫ p, G p ∂((μ a).prod (Measure.pi fun j : {i // i ≠ a} => μ j)) :=
          hmp.integral_comp hemb G
      _ = ∫ y, ∫ g, G (g, y) ∂(μ a) ∂(Measure.pi fun j : {i // i ≠ a} => μ j) :=
          integral_prod_symm G hGint
      _ = ∫ y, ∑ i, blockB (μ a) ρ₁ (Ψh a) w (L i) s *
            multiB ρ₂ (fun j : {i // i ≠ a} => Ψh j) (b i : W) ℓ s y
            ∂(Measure.pi fun j : {i // i ≠ a} => μ j) :=
          integral_congr_ae (Filter.Eventually.of_forall hinner)
      _ = _ := by
          rw [integral_finsetSum _ fun i _ =>
            ((hconv₂ (fun j : {i // i ≠ a} => Ψh j) (fun j => hΨh j) (b i : W) ℓ hℓ₂).2 s
              hs₂).const_mul _]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [integral_const_mul]

  have hterm : ∀ i, RatFE F (γa * γ')
      (fun s => blockA (μ a) ρ₁ (Ψ a) w (L i) s *
        ∫ y, multiA ρ₂ (fun j : {i // i ≠ a} => Ψ j) (b i : W) ℓ s y
          ∂Measure.pi (fun j : {i // i ≠ a} => μ j))
      (fun s => blockB (μ a) ρ₁ (Ψh a) w (L i) s *
        ∫ y, multiB ρ₂ (fun j : {i // i ≠ a} => Ψh j) (b i : W) ℓ s y
          ∂Measure.pi (fun j : {i // i ≠ a} => μ j)) := fun i =>
    ((hblock (Ψ a) (hΨ a) w (L i) (hLsm i)).2.2).mul
      (hIH (fun j => Ψ j) (fun j => hΨ j) (b i : W) ℓ hℓ₂)
  exact (RatFE.sum Finset.univ fun i _ => hterm i).congr ⟨_, hA⟩ ⟨_, hB'⟩

theorem gxMulti_all (hB : GxBlock) {ψ : AddChar F Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) :
    ∀ r, GxMulti F W ψ r
  | 0 => gxMulti_zero ψ
  | r + 1 => gxMulti_succ hB hψ hψ1 (gxMulti_all hB hψ hψ1 r)

end UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
end
end

noncomputable section

open MeasureTheory Measure GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Parabolic
open GroundTheory.Automorphic.GodementJacquet
open scoped NNReal ENNReal Classical ValuativeRel

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

theorem gxLevi (hB : GxBlock) {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [MeasurableSpace F] [BorelSpace F] {n : ℕ} {β : Fin n → ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ (levi F n β) W} (hσ : IsAdmissible σ) [σ.IsIrreducible] (hc : IsCuspidal σ)
    (κ : levi F n β →* ℝ≥0) (hκ : Continuous κ) (μM : Measure (levi F n β)) [μM.IsHaarMeasure]
    {ψ : AddChar F Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {ω : Set.range β → ℂ}
    (hω : ∀ b v, σ (blockUnif F b) v = ω b • v) :
    ∃ γ : RatFunc ℂ, GxShape ((GroundTheory.LocalField.residueCard F : ℕ) : ℂ) γ
      (polF σ fun a => ((κ (blockUnif F a) : ℝ) : ℂ) * ω a) ∧ LeviFE F σ κ μM ψ γ := by
  classical
  have _ : ∀ m : ℕ, BorelSpace (GL (Fin m) F) := fun m => borelSpace_GL_units m
  set e := leviEquivPi F β with he

  set κ' : (∀ a : Set.range β, GL (Fin (blockSize β a)) F) →* ℝ≥0 :=
    κ.comp e.symm.toMonoidHom with hκ'def
  have hκ' : Continuous κ' := hκ.comp e.symm.continuous
  set σ' : Representation ℂ (∀ a : Set.range β, GL (Fin (blockSize β a)) F) W :=
    σ.comp e.symm.toMonoidHom with hσ'def
  set ρ₀ := twist (nnrealCharC κ') σ' with hρ₀def
  set ρ : Representation ℂ ((∀ a : Set.range β, GL (Fin (blockSize β a)) F) × PUnit.{1}) W :=
    ρ₀.comp (prodPUnitEquiv (∀ a : Set.range β, GL (Fin (blockSize β a)) F)).toMulEquiv.toMonoidHom
    with hρdef
  have hρ : ∀ x (h : PUnit.{1}) v, ρ (x, h) v = ((κ (e.symm x) : ℝ) : ℂ) • σ (e.symm x) v :=
    fun x h v => rfl
  have hσ' : IsAdmissible σ' := (isAdmissible_comp_iff e.symm σ).2 hσ
  have hadm : IsAdmissible ρ := (isAdmissible_comp_iff
    (prodPUnitEquiv (∀ a : Set.range β, GL (Fin (blockSize β a)) F)) ρ₀).2
    (isAdmissible_twist κ' hκ' σ' hσ')
  have hirr' : σ'.IsIrreducible := (isIrreducible_comp_iff e.symm σ).2 inferInstance
  have hirr : ρ.IsIrreducible := (isIrreducible_comp_iff
    (prodPUnitEquiv (∀ a : Set.range β, GL (Fin (blockSize β a)) F)) ρ₀).2
    (isIrreducible_twist κ' σ')
  have hsm : ∀ ℓ : Module.Dual ℂ W, ℓ ∈ smoothVectors (Representation.dual ρ) ↔
      ℓ ∈ smoothVectors (Representation.dual σ) := fun ℓ => by
    rw [mem_smoothVectors_dual_comp_iff
      (prodPUnitEquiv (∀ a : Set.range β, GL (Fin (blockSize β a)) F)) ρ₀,
      mem_smoothVectors_dual_twist_iff κ' hκ' σ', mem_smoothVectors_dual_comp_iff e.symm σ]

  have hW : Nontrivial W := nontrivial_of_isIrreducible σ
  have hω0 : ∀ a, ω a ≠ 0 := by
    intro a h0
    obtain ⟨v, hv⟩ := exists_ne (0 : W)
    apply hv
    have h1 : σ (blockUnif F a)⁻¹ (σ (blockUnif F a) v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [← h1, hω, h0, zero_smul, map_zero]
  set αc : Set.range β → ℂ := fun a => ((κ (blockUnif F a) : ℝ) : ℂ) * ω a with hαc
  have hα0 : ∀ a, αc a ≠ 0 := fun a =>
    mul_ne_zero (by simpa using nnrealCharC_ne_zero κ (blockUnif F a)) (hω0 a)
  have hα : ∀ a v, ρ (Pi.mulSingle a (centralUnif F (blockSize β a)), 1) v = αc a • v := by
    intro a v
    rw [hρ, leviEquivPi_symm_mulSingle, hω, smul_smul]

  have hsupp : ∀ v : W, ∀ ℓ ∈ smoothVectors (Representation.dual ρ),
      ∃ C : Set (∀ a : Set.range β, GL (Fin (blockSize β a)) F), IsCompact C ∧
        ∀ x, ℓ (ρ (x, 1) v) ≠ 0 →
          ∃ j : Set.range β → ℤ, (fun a => centralUnif F (blockSize β a) ^ j a) * x ∈ C := by
    intro v ℓ hℓ
    have hℓσ := (hsm ℓ).1 hℓ
    obtain ⟨CM, hCM, hCMs⟩ := exists_compact_of_coeff hσ.1 hc v hℓσ (fun _ => 0)
      (fun b => (blockSize β b : ℤ) - 1)
    refine ⟨e '' CM, hCM.image e.continuous, fun x hx => ?_⟩
    have hpos : ∀ b, (0 : ℤ) < blockSize β b := fun b => by exact_mod_cast blockSize_pos β b
    set j : Set.range β → ℤ := fun b => -(ordDet (x b) / blockSize β b) with hj
    refine ⟨j, e.symm ((fun a => centralUnif F (blockSize β a) ^ j a) * x), ?_, by simp⟩
    refine hCMs _ ?_ fun b => ?_
    · have hmul := apply_centralPow ρ hα0 hα j (ρ (x, 1) v)
      have h2 : ρ ((fun a => centralUnif F (blockSize β a) ^ j a) * x, 1) v =
          (∏ a, αc a ^ j a) • ρ (x, 1) v := by
        rw [← hmul, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
      have h3 := hρ ((fun a => centralUnif F (blockSize β a) ^ j a) * x) 1 v
      intro h0
      apply hx
      have hprod0 : (∏ a, αc a ^ j a) ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => zpow_ne_zero _ (hα0 a)
      have hκ0 := nnrealCharC_ne_zero κ (e.symm ((fun a => centralUnif F (blockSize β a) ^ j a) * x))
      rw [nnrealCharC_apply] at hκ0
      have : ℓ (ρ ((fun a => centralUnif F (blockSize β a) ^ j a) * x, 1) v) = 0 := by
        rw [h3, map_smul, smul_eq_mul, h0, mul_zero]
      rw [h2, map_smul, smul_eq_mul] at this
      exact (mul_eq_zero.1 this).resolve_left hprod0
    · rw [← ordDet_leviEquivPi, ContinuousMulEquiv.apply_symm_apply, Pi.mul_apply,
        ordDet_centralUnif_zpow_mul]
      have h1 := Int.emod_nonneg (ordDet (x b)) (hpos b).ne'
      have h2 := Int.emod_lt_of_pos (ordDet (x b)) (hpos b)
      have h3 := Int.emod_def (ordDet (x b)) (blockSize β b)
      simp only [hj]
      constructor <;> nlinarith

  have _ : ∀ a : Set.range β, NeZero (blockSize β a) := fun a => ⟨(blockSize_pos β a).ne'⟩
  set μb : ∀ a : Set.range β, Measure (GL (Fin (blockSize β a)) F) := fun a => Measure.haar
    with hμb
  obtain ⟨γ, hshape, hmain⟩ := gxMulti_all (W := W) hB hψ hψ1
    (Fintype.card (Set.range β)) (Set.range β) rfl (fun a => blockSize β a) μb
    PUnit.{1} ρ hadm hirr αc hα0 hα hsupp
  obtain ⟨s₀, hconv⟩ := exists_integrable_multi ρ hadm.1 hα0 hα hsupp μb

  set em := e.toHomeomorph.toMeasurableEquiv with hem
  have hν : (Measure.map em μM).IsHaarMeasure :=
    MulEquiv.isHaarMeasure_map μM e.toMulEquiv e.continuous e.symm.continuous
  set c := haarScalarFactor (Measure.map em μM) (Measure.pi μb) with hcdef
  have hc : Measure.map em μM = c • Measure.pi μb :=
    Measure.isMulLeftInvariant_eq_smul (Measure.map em μM) (Measure.pi μb)
  have hemx : ∀ m, e.symm (em m) = m := fun m => e.symm_apply_apply m
  have hint_eq : ∀ f : levi F n β → ℂ,
      ∫ m, f m ∂μM = ((c : ℝ) : ℂ) * ∫ x, f (e.symm x) ∂Measure.pi μb := by
    intro f
    have h1 : ∫ x, f (e.symm x) ∂(Measure.map em μM) = ∫ m, f m ∂μM := by
      rw [integral_map_equiv em]
      simp only [hemx]
    rw [← h1, hc, show (c • Measure.pi μb) = ((c : ℝ≥0∞) • Measure.pi μb) from rfl,
      integral_smul_measure, ENNReal.coe_toReal, Complex.real_smul]
  have hint_of : ∀ f : levi F n β → ℂ,
      Integrable (fun x => f (e.symm x)) (Measure.pi μb) → Integrable f μM := by
    intro f hf
    have h1 : Integrable (fun x => f (e.symm x)) (Measure.map em μM) := by
      rw [hc, show (c • Measure.pi μb) = ((c : ℝ≥0∞) • Measure.pi μb) from rfl]
      exact hf.smul_measure ENNReal.coe_ne_top
    rw [integrable_map_equiv] at h1
    exact h1.congr (Filter.Eventually.of_forall fun m => by simp only [Function.comp_apply, hemx])
  refine ⟨γ, ?_, fun φ hφ w ℓ hℓ => ?_⟩
  · have hk : ∀ a, ∀ g ∈ integralGL F (blockSize β a),
        ρ (Pi.mulSingle a g, 1) = σ (e.symm (Pi.mulSingle a g)) := by
      intro a g hg
      have h1 : κ' (Pi.mulSingle a g) = 1 :=
        eq_one_of_mem_compact (κ'.comp (MonoidHom.mulSingle (fun a : Set.range β => GL (Fin (blockSize β a)) F) a))
          (hκ'.comp (continuous_mulSingle (A := fun a : Set.range β => GL (Fin (blockSize β a)) F) a) :) (isCompact_integralGL F _) hg
      have h2 : κ (e.symm (Pi.mulSingle a g)) = 1 := h1
      ext v
      rw [hρ, h2]
      simp
    unfold polF
    convert hshape using 2 with a
    refine if_congr (and_congr_right fun _ => forall₂_congr fun g hg => ?_) rfl rfl
    rw [hk a g hg]
  set Ψ : ∀ a : Set.range β, Matrix (Fin (blockSize β a)) (Fin (blockSize β a)) F → ℂ :=
    fun a => blockTensor β φ a with hΨdef
  have hΨ : ∀ a, IsSchwartzBruhat (Ψ a) := fun a => isSchwartzBruhat_blockTensor hφ a
  have hℓρ : ℓ ∈ smoothVectors (Representation.dual ρ) := (hsm ℓ).2 hℓ
  have hA_eq : ∀ s x, leviIntegrand σ κ (leviTensor β φ) w ℓ s (e.symm x) =
      multiA ρ Ψ w ℓ s x := by
    intro s x
    simp only [leviIntegrand, multiA]
    rw [leviTensor_leviEquivPi_symm, detPow_leviEquivPi_symm, hρ, map_smul, smul_eq_mul,
      Finset.prod_mul_distrib]
    ring
  have hB_eq : ∀ s x, leviIntegrandB σ κ (leviTensorHat β ψ φ) w ℓ s (e.symm x) =
      multiB ρ (fun a => GJMatrix.localMatrixFourier ψ (Ψ a)) w ℓ s x := by
    intro s x
    simp only [leviIntegrandB, multiB]
    rw [leviTensorHat_leviEquivPi_symm, leviModulus_leviEquivPi_symm, detPow_leviEquivPi_symm,
      hρ, map_smul, smul_eq_mul, map_inv e.symm x, map_inv κ]
    have hdet : ∀ a, detPow (x a) ((blockSize β a : ℂ) - s) =
        ((detModulusPow (x a) : ℝ) : ℂ) * detPow (x a) (-s) := fun a => by
      rw [sub_eq_add_neg, detPow_add, detPow_natCast]
    simp_rw [hdet]
    push_cast
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    ring
  refine ⟨⟨s₀, fun s hs => hint_of _ (((hconv Ψ hΨ w ℓ hℓρ).1 s hs).congr
      (Filter.Eventually.of_forall fun x => (hA_eq s x).symm))⟩,
    ⟨-s₀, fun s hs => hint_of _ (((hconv (fun a => GJMatrix.localMatrixFourier ψ (Ψ a))
      (fun a => (hΨ a).localMatrixFourier hψ hψ1) w ℓ hℓρ).2 s hs).congr
      (Filter.Eventually.of_forall fun x => (hB_eq s x).symm))⟩, ?_⟩
  refine ((hmain Ψ hΨ w ℓ hℓρ).const_mul ((c : ℝ) : ℂ)).congr ⟨0, fun s _ => ?_⟩ ⟨0, fun s _ => ?_⟩
  · rw [hint_eq]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => hA_eq s x)
  · rw [hint_eq]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => hB_eq s x)

end UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
