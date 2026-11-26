module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.LocalZetaIntegralLaurentExpansion
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.LocalZetaIntegralShellMean
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.LocalZetaFunctionalUniqueness

@[expose] public section

attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LaurentBlockInduction.LdMulti
noncomputable section

open MeasureTheory Measure GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Parabolic
open GroundTheory.Automorphic.GodementJacquet
open scoped NNReal ENNReal Classical ValuativeRel

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

set_option linter.unusedSectionVars false

namespace UpperTheory.V.Z.Gam

theorem ldShape_one (q : ℂ) : LdShape q 1 0 := ⟨1, 1, 0, by simp, by simp, one_ne_zero, by simp⟩

theorem ldShape_mul {q : ℂ} {γ₁ γ₂ : RatFunc ℂ} {k₁ k₂ : ℕ} (h₁ : LdShape q γ₁ k₁) (h₂ : LdShape q γ₂ k₂) :
    LdShape q (γ₁ * γ₂) (k₁ + k₂) := by
  obtain ⟨P₁, c₁, j₁, he₁, hd₁, hc₁, rfl⟩ := h₁
  obtain ⟨P₂, c₂, j₂, he₂, hd₂, hc₂, rfl⟩ := h₂
  have hP₁ : P₁ ≠ 0 := by
    rintro rfl
    simp at he₁
  have hP₂ : P₂ ≠ 0 := by
    rintro rfl
    simp at he₂
  refine ⟨P₁ * P₂, c₁ * c₂, j₁ + j₂, by simp [he₁, he₂], ?_, mul_ne_zero hc₁ hc₂, ?_⟩
  · rw [Polynomial.natDegree_mul hP₁ hP₂, hd₁, hd₂]
  · rw [div_mul_div_comm, Polynomial.mul_comp, map_mul, map_mul, map_mul,
      zpow_add₀ RatFunc.X_ne_zero]
    ring

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]
  [∀ n : ℕ, MeasurableSpace (GL (Fin n) F)] [∀ n : ℕ, BorelSpace (GL (Fin n) F)]
  {W : Type} [AddCommGroup W] [Module ℂ W]


variable (F W) in
def LdMulti (ψ : AddChar F Circle) (r : ℕ) : Prop :=
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
    ∃ γ : RatFunc ℂ, LdShape ((GroundTheory.LocalField.residueCard F : ℕ) : ℂ) γ
        (∑ i, if d i = 1 ∧ ∀ g ∈ integralGL F (d i), ρ (Pi.mulSingle i g, 1) = 1 then 1 else 0) ∧
      ∀ Ψ : ∀ i, Matrix (Fin (d i)) (Fin (d i)) F → ℂ,
      (∀ i, IsSchwartzBruhat (Ψ i)) → ∀ w : W, ∀ ℓ ∈ smoothVectors (Representation.dual ρ),
        RatFE F γ (fun s => ∫ x, multiA ρ Ψ w ℓ s x ∂Measure.pi μ)
          (fun s => ∫ x, multiB ρ (fun i => GJMatrix.localMatrixFourier ψ (Ψ i)) w ℓ s x
            ∂Measure.pi μ)

theorem ldMulti_zero (ψ : AddChar F Circle) : LdMulti F W ψ 0 := by
  intro ι _ _ hcard d _ μ _ H _ _ _ _ _ _ _ ρ _ _ α _ _ _
  haveI : IsEmpty ι := Fintype.card_eq_zero_iff.1 hcard
  refine ⟨1, ?_, ?_⟩
  · simpa using ldShape_one ((GroundTheory.LocalField.residueCard F : ℕ) : ℂ)
  · intro Ψ _ w ℓ _
    have hx : ∀ x : (∀ i, GL (Fin (d i)) F), x = 1 := fun x => funext fun i => isEmptyElim i
    have hone : ℓ (ρ (1, 1) w) = ℓ w := by
      rw [Prod.mk_one_one, map_one]
      rfl
    have hA : ∀ s, (∫ x, multiA ρ Ψ w ℓ s x ∂Measure.pi μ) = ℓ w := by
      intro s
      have hf : multiA ρ Ψ w ℓ s = fun _ => ℓ w := by
        funext x
        rw [hx x]
        simpa [multiA] using hone
      rw [hf, integral_const, Measure.pi_of_empty (x := 1)]
      simp
    have hB : ∀ s, (∫ x, multiB ρ (fun i => GJMatrix.localMatrixFourier ψ (Ψ i)) w ℓ s x
        ∂Measure.pi μ) = ℓ w := by
      intro s
      have hf : multiB ρ (fun i => GJMatrix.localMatrixFourier ψ (Ψ i)) w ℓ s = fun _ => ℓ w := by
        funext x
        rw [hx x]
        simpa [multiB] using hone
      rw [hf, integral_const, Measure.pi_of_empty (x := 1)]
      simp
    refine ⟨RatFunc.C (ℓ w), 0, fun s _ => ?_, fun s _ => ?_⟩
    · beta_reduce
      rw [hA]
      simp
    · beta_reduce
      rw [hB]
      simp

theorem ldMulti_succ (hB : LdBlock) {ψ : AddChar F Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {r : ℕ}
    (ih : LdMulti F W ψ r) : LdMulti F W ψ (r + 1) := by
  intro ι _ _ hcard d _ μ _ H _ _ _ _ _ _ _ ρ hadm hirr α hα hcent hsupp
  obtain ⟨a⟩ : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  have hcard' : Fintype.card {i // i ≠ a} = r := by
    have h := Set.card_ne_eq a
    simp only [Set.coe_setOf] at h
    omega
  let σ : Representation ℂ (GL (Fin (d a)) F × (((i : {i // i ≠ a}) → GL (Fin (d i)) F) × H)) W :=
    ρ.comp (peelFst d H a).symm.toMonoidHom
  let ρ' : Representation ℂ (((i : {i // i ≠ a}) → GL (Fin (d i)) F) × (GL (Fin (d a)) F × H)) W :=
    ρ.comp (peelSnd d H a).symm.toMonoidHom
  have hσ : ∀ g y h, σ (g, (y, h)) = ρ (splitSymm d a g y, h) := by
    intro g y h
    show ρ ((peelFst d H a).symm (g, (y, h))) = _
    rw [peelFst_symm_apply]
  have hρ' : ∀ y g h, ρ' (y, (g, h)) = ρ (splitSymm d a g y, h) := by
    intro y g h
    show ρ ((peelSnd d H a).symm (y, (g, h))) = _
    rw [peelSnd_symm_apply]
  have hσadm : IsAdmissible σ := (isAdmissible_comp_iff (peelFst d H a).symm ρ).2 hadm
  have hσirr : σ.IsIrreducible := (isIrreducible_comp_iff (peelFst d H a).symm ρ).2 hirr
  have hσsm : ∀ ℓ : Module.Dual ℂ W, ℓ ∈ smoothVectors σ.dual ↔ ℓ ∈ smoothVectors ρ.dual :=
    fun ℓ => mem_smoothVectors_dual_comp_iff (peelFst d H a).symm ρ
  have hρ'adm : IsAdmissible ρ' := (isAdmissible_comp_iff (peelSnd d H a).symm ρ).2 hadm
  have hρ'irr : ρ'.IsIrreducible := (isIrreducible_comp_iff (peelSnd d H a).symm ρ).2 hirr
  have hρ'sm : ∀ ℓ : Module.Dual ℂ W, ℓ ∈ smoothVectors ρ'.dual ↔ ℓ ∈ smoothVectors ρ.dual :=
    fun ℓ => mem_smoothVectors_dual_comp_iff (peelSnd d H a).symm ρ
  clear_value σ ρ'
  have hσ1 : ∀ g, σ (g, 1) = ρ (Pi.mulSingle a g, 1) := by
    intro g
    rw [show ((g, 1) : GL (Fin (d a)) F × (((i : {i // i ≠ a}) → GL (Fin (d i)) F) × H)) = (g, (1, 1))
      from rfl, hσ, splitSymm_mulSingle_self]
  have hρ'1 : ∀ (j : {i // i ≠ a}) (g : GL (Fin (d j)) F),
      ρ' (Pi.mulSingle j g, 1) = ρ (Pi.mulSingle (j : ι) g, 1) := by
    intro j g
    rw [show ((Pi.mulSingle j g, 1) : ((i : {i // i ≠ a}) → GL (Fin (d i)) F) × (GL (Fin (d a)) F × H))
      = (Pi.mulSingle j g, (1, 1)) from rfl, hρ', splitSymm_one_mulSingle]
  have hσcent : ∀ v, σ (centralUnif F (d a), 1) v = α a • v := by
    intro v
    rw [hσ1]
    exact hcent a v
  have hρ'cent : ∀ (j : {i // i ≠ a}) v, ρ' (Pi.mulSingle j (centralUnif F (d j)), 1) v = α j • v := by
    intro j v
    rw [hρ'1]
    exact hcent j v
  have hσsupp : ∀ v : W, ∀ ℓ ∈ smoothVectors σ.dual, ∃ C : Set (GL (Fin (d a)) F), IsCompact C ∧
      ∀ g, ℓ (σ (g, 1) v) ≠ 0 → ∃ j : ℤ, centralUnif F (d a) ^ j * g ∈ C := by
    intro v ℓ hℓ
    obtain ⟨C, hC, hCx⟩ := hsupp v ℓ ((hσsm ℓ).1 hℓ)
    refine ⟨(fun x => x a) '' C, hC.image (continuous_apply a), fun g hg => ?_⟩
    rw [hσ1] at hg
    obtain ⟨j, hj⟩ := hCx _ hg
    exact ⟨j a, _, hj, by simp⟩
  have hρ'supp : ∀ v : W, ∀ ℓ ∈ smoothVectors ρ'.dual,
      ∃ C : Set ((i : {i // i ≠ a}) → GL (Fin (d i)) F), IsCompact C ∧
        ∀ y, ℓ (ρ' (y, 1) v) ≠ 0 → ∃ j : {i // i ≠ a} → ℤ,
          (fun i : {i // i ≠ a} => centralUnif F (d i) ^ j i) * y ∈ C := by
    intro v ℓ hℓ
    obtain ⟨C, hC, hCx⟩ := hsupp v ℓ ((hρ'sm ℓ).1 hℓ)
    refine ⟨(fun x (k : {i // i ≠ a}) => x (k : ι)) '' C,
      hC.image (continuous_pi fun k => continuous_apply (k : ι)), fun y hy => ?_⟩
    rw [show ((y, 1) : ((i : {i // i ≠ a}) → GL (Fin (d i)) F) × (GL (Fin (d a)) F × H))
      = (y, (1, 1)) from rfl, hρ'] at hy
    obtain ⟨j, hj⟩ := hCx _ hy
    exact ⟨fun k => j k, _, hj, funext fun k => centralPow_mul_splitSymm_apply j y k⟩
  haveI := hσirr
  obtain ⟨γa, s₁, hblk⟩ := exists_blockFE (μ a) hσadm hψ hψ1 hσcent hσsupp
  have hsha := hB F (d a) (μ a) _ W σ hσadm hσirr (α a) (hα a) hσcent hσsupp ψ hψ hψ1 γa
    (fun Φ hΦ v ℓ hℓ => (hblk Φ hΦ v ℓ hℓ).2.2)
  obtain ⟨γ', hsh', hFE'⟩ := ih {i // i ≠ a} hcard' (fun i => d i) (fun i => μ i)
    (GL (Fin (d a)) F × H) ρ' hρ'adm hρ'irr (fun i => α i) (fun i => hα i) hρ'cent hρ'supp
  refine ⟨γa * γ', ?_, ?_⟩
  · have h := ldShape_mul hsha hsh'
    rw [Fintype.sum_eq_add_sum_subtype_ne _ a]
    simp only [hσ1, hρ'1] at h
    exact h
  · intro Ψ hΨ w ℓ hℓ
    obtain ⟨s₂, hint⟩ := exists_integrable_multi ρ hadm.1 hα hcent hsupp μ
    obtain ⟨s₃, hint'⟩ := exists_integrable_multi ρ' hρ'adm.1 (α := fun i => α i) (fun i => hα i)
      hρ'cent hρ'supp (fun i => μ i)
    have hstab : (stabilizerOf σ w : Set (GL (Fin (d a)) F × (((i : {i // i ≠ a}) → GL (Fin (d i)) F) × H)))
        ∈ nhds ((1, 1) : GL (Fin (d a)) F × (((i : {i // i ≠ a}) → GL (Fin (d i)) F) × H)) :=
      (hσadm.1 w).mem_nhds (Subgroup.one_mem _)
    rw [mem_nhds_prod_iff] at hstab
    obtain ⟨u, hu, v, hv, huv⟩ := hstab
    obtain ⟨m0, hm0⟩ := (hΨ a).exists_congruence_invariant
    have hu' : u ∩ (congruenceSubgroup F (d a) m0 : Set (GL (Fin (d a)) F)) ∈ nhds (1 : GL (Fin (d a)) F) :=
      Filter.inter_mem hu ((isOpen_congruenceSubgroup F (d a) m0).mem_nhds (Subgroup.one_mem _))
    obtain ⟨K₁, hK₁c, hK₁u⟩ := exists_openSubgroup_isCompact_subset hu'
    obtain ⟨K₂, hK₂c, hK₂v⟩ := exists_openSubgroup_isCompact_subset hv
    let Ka : Subgroup (GL (Fin (d a)) F) := (K₁ : Subgroup (GL (Fin (d a)) F))
    let K' : Subgroup (((i : {i // i ≠ a}) → GL (Fin (d i)) F) × H) :=
      (K₂ : Subgroup (((i : {i // i ≠ a}) → GL (Fin (d i)) F) × H))
    have hKc : IsCompact ((Ka.prod K' : Subgroup _) : Set (GL (Fin (d a)) F × (((i : {i // i ≠ a}) → GL (Fin (d i)) F) × H))) := by
      rw [Subgroup.coe_prod]
      exact hK₁c.prod hK₂c
    have hKo : IsOpen ((Ka.prod K' : Subgroup _) : Set (GL (Fin (d a)) F × (((i : {i // i ≠ a}) → GL (Fin (d i)) F) × H))) := by
      rw [Subgroup.coe_prod]
      exact K₁.isOpen.prod K₂.isOpen
    haveI : FiniteDimensional ℂ (fixedVectors σ (Ka.prod K')) := hσadm.2 _ hKc hKo
    have hKa : Ka ≤ integralGL F (d a) := fun k hk => congruenceSubgroup_le F (d a) m0 (hK₁u hk).2
    have hΨinv : ∀ k ∈ Ka, ∀ X : Matrix (Fin (d a)) (Fin (d a)) F, Ψ a ((k : Matrix (Fin (d a)) (Fin (d a)) F) * X) = Ψ a X := fun k hk X => (hm0 k (hK₁u hk).2 X).1
    have hΦinv : ∀ k ∈ Ka, ∀ X : Matrix (Fin (d a)) (Fin (d a)) F, GJMatrix.localMatrixFourier ψ (Ψ a) (X * (k : Matrix (Fin (d a)) (Fin (d a)) F)) =
        GJMatrix.localMatrixFourier ψ (Ψ a) X := fun k hk X =>
      localMatrixFourier_mul_right_of_invariant (hKa hk)
        (fun x => (hm0 k⁻¹ (Subgroup.inv_mem _ (hK₁u hk).2) x).1) X
    have hwfix : w ∈ fixedVectors σ (Ka.prod K') := fun h hh =>
      huv ⟨(hK₁u (Subgroup.mem_prod.1 hh).1).1, hK₂v (Subgroup.mem_prod.1 hh).2⟩
    let b := Module.finBasis ℂ (fixedVectors σ (Ka.prod K'))
    let L : Fin (Module.finrank ℂ (fixedVectors σ (Ka.prod K'))) → Module.Dual ℂ W := fun i =>
      (((extendFixed hσadm.1 hKc hKo (b.coord i) : fixedVectors (contragredient σ) (Ka.prod K')) :
        smoothVectors σ.dual) : Module.Dual ℂ W)
    have hL : ∀ i, L i ∈ smoothVectors σ.dual := fun i =>
      ((extendFixed hσadm.1 hKc hKo (b.coord i) : fixedVectors (contragredient σ) (Ka.prod K')) :
        smoothVectors σ.dual).2
    let m : ((i : {i // i ≠ a}) → GL (Fin (d i)) F) → smoothVectors σ.dual := fun y =>
      contragredient σ ((1, (y, 1))⁻¹) ⟨ℓ, (hσsm ℓ).2 hℓ⟩
    have hm : ∀ y v, (m y : Module.Dual ℂ W) v = ℓ (ρ (splitSymm d a 1 y, 1) v) := by
      intro y v
      simp only [m]
      rw [contragredient_apply_apply, inv_inv, hσ]
    have hsplit : ∀ g y, ρ (splitSymm d a g y, 1) = ρ (splitSymm d a 1 y, 1) * σ (g, 1) := by
      intro g y
      rw [← hσ, ← hσ, ← map_mul]
      congr 1
      ext <;> simp
    have hρ'y : ∀ y v, ρ' (y, 1) v = ρ (splitSymm d a 1 y, 1) v := by
      intro y v
      rw [show ((y, 1) : ((i : {i // i ≠ a}) → GL (Fin (d i)) F) × (GL (Fin (d a)) F × H))
        = (y, (1, 1)) from rfl, hρ']
    let e := (Homeomorph.piSplitAt a (fun i => GL (Fin (d i)) F)).toMeasurableEquiv
    have hmp : MeasurePreserving e (Measure.pi μ) ((μ a).prod (Measure.pi fun j : {i // i ≠ a} => μ j)) :=
      measurePreserving_piSplitAt d a μ
    have he : ∀ g y, e.symm (g, y) = splitSymm d a g y := fun g y => rfl
    have hA : ∀ s : ℂ, max s₁ (max s₂ s₃) < s.re →
        (∫ x, multiA ρ Ψ w ℓ s x ∂Measure.pi μ) =
          ∑ i, blockA (μ a) σ (Ψ a) w (L i) s *
            ∫ y, multiA ρ' (fun j => Ψ j) (b i : W) ℓ s y ∂Measure.pi (fun j : {i // i ≠ a} => μ j) := by
      intro s hs
      have hs₁ : s₁ < s.re := lt_of_le_of_lt (le_max_left _ _) hs
      have hs₂ : s₂ < s.re := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hs
      have hs₃ : s₃ < s.re := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hs
      have hinner : ∀ y, (∫ g, multiA ρ Ψ w ℓ s (splitSymm d a g y) ∂μ a) =
          ∑ i, blockA (μ a) σ (Ψ a) w (L i) s * multiA ρ' (fun j => Ψ j) (b i : W) ℓ s y := by
        intro y
        have hpt : ∀ g, multiA ρ Ψ w ℓ s (splitSymm d a g y) =
            (∏ j : {i // i ≠ a}, Ψ j ↑(y j) * detPow (y j) s) *
              (Ψ a ↑g * detPow g s * (m y : Module.Dual ℂ W) (σ (g, 1) w)) := by
          intro g
          simp only [multiA]
          rw [prod_splitSymm (fun i (x : GL (Fin (d i)) F) => Ψ i ↑x * detPow x s), hsplit, Module.End.mul_apply, hm]
          ring
        simp_rw [hpt]
        rw [integral_const_mul]
        have hsum := blockA_eq_sum hσadm.1 hKc hKo hKa hΨinv hwfix
          (fun μ' hμ' => (hblk (Ψ a) (hΨ a) w μ' hμ').1 s hs₁) (m y)
        simp only [blockA] at hsum ⊢
        rw [hsum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [multiA]
        rw [hρ'y, ← hm]
        ring
      have hintA := (hint Ψ hΨ w ℓ hℓ).1 s hs₂
      calc (∫ x, multiA ρ Ψ w ℓ s x ∂Measure.pi μ)
          = ∫ z, multiA ρ Ψ w ℓ s (e.symm z) ∂(μ a).prod (Measure.pi fun j : {i // i ≠ a} => μ j) := by
            rw [← hmp.integral_comp']
            simp
        _ = ∫ y, ∫ g, multiA ρ Ψ w ℓ s (splitSymm d a g y) ∂μ a ∂Measure.pi (fun j : {i // i ≠ a} => μ j) := by
            rw [integral_prod_symm]
            · rfl
            · apply (hmp.integrable_comp_emb e.measurableEmbedding
                (g := fun z => multiA ρ Ψ w ℓ s (e.symm z))).1
              simpa [Function.comp_def] using hintA
        _ = ∫ y, ∑ i, blockA (μ a) σ (Ψ a) w (L i) s * multiA ρ' (fun j => Ψ j) (b i : W) ℓ s y
              ∂Measure.pi (fun j : {i // i ≠ a} => μ j) := by
            simp_rw [hinner]
        _ = _ := by
            rw [integral_finsetSum]
            · simp_rw [integral_const_mul]
            · intro i _
              exact ((hint' (fun j => Ψ j) (fun j => hΨ j) (b i : W) ℓ ((hρ'sm ℓ).2 hℓ)).1 s hs₃).const_mul _
    have hB' : ∀ s : ℂ, s.re < -max s₁ (max s₂ s₃) →
        (∫ x, multiB ρ (fun i => GJMatrix.localMatrixFourier ψ (Ψ i)) w ℓ s x ∂Measure.pi μ) =
          ∑ i, blockB (μ a) σ (GJMatrix.localMatrixFourier ψ (Ψ a)) w (L i) s *
            ∫ y, multiB ρ' (fun j => GJMatrix.localMatrixFourier ψ (Ψ j)) (b i : W) ℓ s y
              ∂Measure.pi (fun j : {i // i ≠ a} => μ j) := by
      intro s hs
      have hs₁ : s.re < -s₁ := lt_of_lt_of_le hs (neg_le_neg (le_max_left _ _))
      have hs₂ : s.re < -s₂ := lt_of_lt_of_le hs (neg_le_neg ((le_max_left _ _).trans (le_max_right _ _)))
      have hs₃ : s.re < -s₃ := lt_of_lt_of_le hs (neg_le_neg ((le_max_right _ _).trans (le_max_right _ _)))
      have hinner : ∀ y, (∫ g, multiB ρ (fun i => GJMatrix.localMatrixFourier ψ (Ψ i)) w ℓ s
          (splitSymm d a g y) ∂μ a) =
          ∑ i, blockB (μ a) σ (GJMatrix.localMatrixFourier ψ (Ψ a)) w (L i) s *
            multiB ρ' (fun j => GJMatrix.localMatrixFourier ψ (Ψ j)) (b i : W) ℓ s y := by
        intro y
        have hpt : ∀ g, multiB ρ (fun i => GJMatrix.localMatrixFourier ψ (Ψ i)) w ℓ s (splitSymm d a g y) =
            (∏ j : {i // i ≠ a}, GJMatrix.localMatrixFourier ψ (Ψ j) ↑(y j) * detPow (y j) (↑(d j) - s)) *
              (GJMatrix.localMatrixFourier ψ (Ψ a) ↑g * detPow g (↑(d a) - s) *
                (m y⁻¹ : Module.Dual ℂ W) (σ (g⁻¹, 1) w)) := by
          intro g
          simp only [multiB]
          rw [prod_splitSymm (fun i (x : GL (Fin (d i)) F) =>
              GJMatrix.localMatrixFourier ψ (Ψ i) ↑x * detPow x (↑(d i) - s)),
            splitSymm_inv, hsplit, Module.End.mul_apply, hm]
          ring
        simp_rw [hpt]
        rw [integral_const_mul]
        have hsum := blockB_eq_sum hσadm.1 hKc hKo hKa hΦinv hwfix
          (fun μ' hμ' => (hblk (Ψ a) (hΨ a) w μ' hμ').2.1 s hs₁) (m y⁻¹)
        simp only [blockB] at hsum ⊢
        rw [hsum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [multiB]
        rw [hρ'y, ← hm]
        ring
      have hintB := (hint (fun i => GJMatrix.localMatrixFourier ψ (Ψ i))
        (fun i => (hΨ i).localMatrixFourier hψ hψ1) w ℓ hℓ).2 s hs₂
      calc (∫ x, multiB ρ (fun i => GJMatrix.localMatrixFourier ψ (Ψ i)) w ℓ s x ∂Measure.pi μ)
          = ∫ z, multiB ρ (fun i => GJMatrix.localMatrixFourier ψ (Ψ i)) w ℓ s (e.symm z)
              ∂(μ a).prod (Measure.pi fun j : {i // i ≠ a} => μ j) := by
            rw [← hmp.integral_comp']
            simp
        _ = ∫ y, ∫ g, multiB ρ (fun i => GJMatrix.localMatrixFourier ψ (Ψ i)) w ℓ s (splitSymm d a g y)
              ∂μ a ∂Measure.pi (fun j : {i // i ≠ a} => μ j) := by
            rw [integral_prod_symm]
            · rfl
            · apply (hmp.integrable_comp_emb e.measurableEmbedding
                (g := fun z => multiB ρ (fun i => GJMatrix.localMatrixFourier ψ (Ψ i)) w ℓ s (e.symm z))).1
              simpa [Function.comp_def] using hintB
        _ = ∫ y, ∑ i, blockB (μ a) σ (GJMatrix.localMatrixFourier ψ (Ψ a)) w (L i) s *
              multiB ρ' (fun j => GJMatrix.localMatrixFourier ψ (Ψ j)) (b i : W) ℓ s y
              ∂Measure.pi (fun j : {i // i ≠ a} => μ j) := by
            simp_rw [hinner]
        _ = _ := by
            rw [integral_finsetSum]
            · simp_rw [integral_const_mul]
            · intro i _
              exact ((hint' (fun j => GJMatrix.localMatrixFourier ψ (Ψ j))
                (fun j => (hΨ j).localMatrixFourier hψ hψ1) (b i : W) ℓ ((hρ'sm ℓ).2 hℓ)).2 s hs₃).const_mul _
    have hfe : RatFE F (γa * γ')
        (fun z => ∑ i ∈ Finset.univ, blockA (μ a) σ (Ψ a) w (L i) z *
          ∫ y, multiA ρ' (fun j => Ψ j) (b i : W) ℓ z y ∂Measure.pi (fun j : {i // i ≠ a} => μ j))
        (fun z => ∑ i ∈ Finset.univ, blockB (μ a) σ (GJMatrix.localMatrixFourier ψ (Ψ a)) w (L i) z *
          ∫ y, multiB ρ' (fun j => GJMatrix.localMatrixFourier ψ (Ψ j)) (b i : W) ℓ z y
            ∂Measure.pi (fun j : {i // i ≠ a} => μ j)) :=
      RatFE.sum Finset.univ fun i _ => RatFE.mul (hblk (Ψ a) (hΨ a) w (L i) (hL i)).2.2
        (hFE' (fun j => Ψ j) (fun j => hΨ j) (b i : W) ℓ ((hρ'sm ℓ).2 hℓ))
    exact hfe.congr ⟨max s₁ (max s₂ s₃), hA⟩ ⟨-max s₁ (max s₂ s₃), hB'⟩

theorem ldMulti_all (hB : LdBlock) {ψ : AddChar F Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) :
    ∀ r, LdMulti F W ψ r
  | 0 => ldMulti_zero ψ
  | r + 1 => ldMulti_succ hB hψ hψ1 (ldMulti_all hB hψ hψ1 r)

end UpperTheory.V.Z.Gam
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LaurentBlockInduction.LdBlock
noncomputable section

open MeasureTheory Polynomial GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Parabolic
open GroundTheory.Automorphic.GodementJacquet
open scoped NNReal Classical ValuativeRel

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace UpperTheory.V.Z.Gam

private def LF (f : ℂ → ℂ) : Prop := ∃ (P : ℂ[X]) (N : ℕ), ∀ x : ℂ, x ≠ 0 → f x = P.eval x / x ^ N

private theorem LF.add {f g : ℂ → ℂ} (hf : LF f) (hg : LF g) : LF fun x => f x + g x := by
  obtain ⟨P, N, h⟩ := hf
  obtain ⟨Q, M, h'⟩ := hg
  refine ⟨P * X ^ M + Q * X ^ N, N + M, fun x hx => ?_⟩
  simp only [h x hx, h' x hx, eval_add, eval_mul, eval_pow, eval_X]
  field_simp
  ring

private theorem LF.mul {f g : ℂ → ℂ} (hf : LF f) (hg : LF g) : LF fun x => f x * g x := by
  obtain ⟨P, N, h⟩ := hf
  obtain ⟨Q, M, h'⟩ := hg
  refine ⟨P * Q, N + M, fun x hx => ?_⟩
  simp only [h x hx, h' x hx, eval_mul]
  field_simp
  ring

private theorem LF.mono (c : ℂ) (k : ℤ) : LF fun x => c * x ^ k := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · exact ⟨C c * X ^ n, 0, fun x _ => by simp⟩
  · exact ⟨C c, n, fun x _ => by simp [div_eq_mul_inv]⟩

private theorem LF.mono' (κ c : ℂ) (k : ℤ) : LF fun x => c * (κ / x) ^ k := by
  obtain ⟨P, N, h⟩ := LF.mono (c * κ ^ k) (-k)
  refine ⟨P, N, fun x hx => ?_⟩
  rw [← h x hx]
  simp only [div_zpow, zpow_neg]
  ring

private theorem LF.sum {ι : Type} (S : Finset ι) {f : ι → ℂ → ℂ} (h : ∀ i, LF (f i)) : LF fun x => ∑ i ∈ S, f i x := by
  induction S using Finset.induction_on with
  | empty => exact ⟨0, 0, fun x _ => by simp⟩
  | insert a s ha ih => simpa only [Finset.sum_insert ha] using (h a).add ih

private theorem LF.poly (κ : ℂ) (P : ℂ[X]) : LF fun x => P.eval (κ / x) := by
  simp only [eval_eq_sum_range]
  exact LF.sum _ fun i => by simpa using LF.mono' κ (P.coeff i) (i : ℤ)

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

private theorem rat_eq {γ : RatFunc ℂ} {a b : ℂ → ℂ} (h : RatFE F γ a b) {P Q P' Q' : ℂ[X]} {t t' : ℝ}
    (ha : ∀ s : ℂ, t < s.re → Q.eval (qs F s) ≠ 0 ∧ a s = P.eval (qs F s) / Q.eval (qs F s))
    (hb : ∀ s : ℂ, s.re < t' → Q'.eval (qs F s) ≠ 0 ∧ b s = P'.eval (qs F s) / Q'.eval (qs F s)) :
    algebraMap ℂ[X] (RatFunc ℂ) P' / algebraMap ℂ[X] (RatFunc ℂ) Q' =
      γ * (algebraMap ℂ[X] (RatFunc ℂ) P / algebraMap ℂ[X] (RatFunc ℂ) Q) := by
  obtain ⟨R, s₁, h₁, h₂⟩ := h
  have hR : R = algebraMap ℂ[X] (RatFunc ℂ) P / algebraMap ℂ[X] (RatFunc ℂ) Q :=
    eq_of_eval_qs_eq_right (F := F) (s₁ := max s₁ t) fun s hs => by
      rw [max_lt_iff] at hs
      rw [← h₁ s hs.1, eval_div_algebraMap _ _ (ha s hs.2).1, (ha s hs.2).2]
  rw [← hR]
  exact eq_of_eval_qs_eq_left (F := F) (s₁ := min (-s₁) t') fun s hs => by
    rw [lt_min_iff] at hs
    rw [← h₂ s hs.1, eval_div_algebraMap _ _ (hb s hs.2).1, (hb s hs.2).2]

private theorem core {γ : RatFunc ℂ} {a b a' b' f f' : ℂ → ℂ} (h : RatFE F γ a b) (h' : RatFE F γ a' b')
    {D D' : ℂ[X]} (hD : D ≠ 0) (hD' : D' ≠ 0) {c c' : ℂ} (hc : c ≠ 0) (hc' : c' ≠ 0) {i : ℕ} (hf : LF f) (hf' : LF f') {t t' : ℝ}
    (ha : ∀ s : ℂ, t < s.re → D.eval (qs F s) ≠ 0 ∧ a s = c / D.eval (qs F s) ∧ a' s = f' (qs F s) / D.eval (qs F s))
    (hb : ∀ s : ℂ, s.re < t' → D'.eval (qs F s) ≠ 0 ∧ b s = f (qs F s) / D'.eval (qs F s) ∧
      b' s = c' * qs F s ^ i / D'.eval (qs F s)) :
    ∃ (r : ℂ) (j : ℤ), r ≠ 0 ∧
      γ = RatFunc.C r * RatFunc.X ^ j * algebraMap ℂ[X] (RatFunc ℂ) D / algebraMap ℂ[X] (RatFunc ℂ) D' := by
  obtain ⟨P, N, hP⟩ := hf
  obtain ⟨P', N', hP'⟩ := hf'
  have e1 := rat_eq h (P := C c) (Q := D) (P' := P) (Q' := X ^ N * D') (t := t) (t' := t')
    (fun s hs => ⟨(ha s hs).1, by rw [(ha s hs).2.1, eval_C]⟩)
    (fun s hs => ⟨by simp [(hb s hs).1, qs_ne_zero], by
      rw [(hb s hs).2.1, hP _ (qs_ne_zero s), div_div]; simp⟩)
  have e2 := rat_eq h' (P := P') (Q := X ^ N' * D) (P' := C c' * X ^ i) (Q' := D') (t := t) (t' := t')
    (fun s hs => ⟨by simp [(ha s hs).1, qs_ne_zero], by
      rw [(ha s hs).2.2, hP' _ (qs_ne_zero s), div_div]; simp⟩)
    (fun s hs => ⟨(hb s hs).1, by rw [(hb s hs).2.2]; simp⟩)
  simp only [map_mul, map_pow, RatFunc.algebraMap_X, RatFunc.algebraMap_C] at e1 e2
  have n1 := RatFunc.algebraMap_ne_zero hD
  have n2 := RatFunc.algebraMap_ne_zero hD'
  have nX : (RatFunc.X : RatFunc ℂ) ≠ 0 := RatFunc.X_ne_zero
  have nc : (RatFunc.C c : RatFunc ℂ) ≠ 0 := by simpa using hc
  have nc' : (RatFunc.C c' : RatFunc ℂ) ≠ 0 := by simpa using hc'
  set d := algebraMap ℂ[X] (RatFunc ℂ) D
  set d' := algebraMap ℂ[X] (RatFunc ℂ) D'
  have hγ : γ ≠ 0 := by
    rintro rfl
    rw [zero_mul] at e2
    exact div_ne_zero (mul_ne_zero nc' (pow_ne_zero _ nX)) n2 e2
  have m1 : γ * d' / d ∈ laurentSubalgebra := by
    have : γ * d' / d = RatFunc.C c⁻¹ * (algebraMap ℂ[X] (RatFunc ℂ) P / RatFunc.X ^ N) := by
      rw [map_inv₀]
      field_simp at e1 ⊢
      linear_combination -e1
    rw [this]
    exact mul_mem (C_mem_laurentSubalgebra _) (mem_laurentSubalgebra_iff.2 ⟨P, N, rfl⟩)
  have m2 : (γ * d' / d)⁻¹ ∈ laurentSubalgebra := by
    have : (γ * d' / d)⁻¹ = RatFunc.C c'⁻¹ * (algebraMap ℂ[X] (RatFunc ℂ) P' / RatFunc.X ^ (N' + i)) := by
      rw [map_inv₀, pow_add]
      field_simp at e2 ⊢
      linear_combination e2
    rw [this]
    exact mul_mem (C_mem_laurentSubalgebra _) (mem_laurentSubalgebra_iff.2 ⟨P', N' + i, rfl⟩)
  obtain ⟨r, k, l, hr, he⟩ := exists_eq_C_mul_X_pow_of_mem m1 m2 (div_ne_zero (mul_ne_zero hγ n2) n1)
  simp only [map_mul, map_pow, RatFunc.algebraMap_X, RatFunc.algebraMap_C] at he
  refine ⟨r, (k : ℤ) - l, hr, ?_⟩
  rw [zpow_sub₀ nX, zpow_natCast, zpow_natCast]
  field_simp at he ⊢
  linear_combination he

private theorem blockB_ind {m : ℕ} [MeasurableSpace (GL (Fin m) F)] [BorelSpace (GL (Fin m) F)] {H : Type} [Group H]
    {W : Type} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (GL (Fin m) F × H) W}
    (μ : Measure (GL (Fin m) F)) {r : ℕ} {K' : Subgroup H} {v : W}
    (hv : v ∈ fixedVectors σ ((congruenceSubgroup F m r).prod K')) (ℓ : Module.Dual ℂ W) (s : ℂ) :
    blockB μ σ (indGL (congruenceSubgroup F m r : Set (GL (Fin m) F))) v ℓ s =
      μ.real (congruenceSubgroup F m r : Set (GL (Fin m) F)) * ℓ v := by
  have hdet : ∀ g ∈ congruenceSubgroup F m r, detPow g (m - s) = 1 := fun g hg =>
    detPow_of_mem_integralGL (congruenceSubgroup_le F m r hg) _
  have hfix : ∀ g ∈ congruenceSubgroup F m r, σ (g⁻¹, 1) v = v := fun g hg =>
    mem_fixedVectors.1 hv _ (Subgroup.mem_prod.2 ⟨inv_mem hg, K'.one_mem⟩)
  simp only [blockB, mul_assoc]
  rw [integral_indGL_mul μ (isOpen_congruenceSubgroup F m r).measurableSet (x₀ := 1)
    (fun g hg => by rw [hdet g hg, hdet 1 (one_mem _), hfix g hg, hfix 1 (one_mem _)]),
    hdet 1 (one_mem _), one_mul, hfix 1 (one_mem _)]

theorem ldBlock_of (hL : LdLaurent) (hM : LdMean) (hT : LdTate) : LdBlock := by
  intro F _ _ _ _ _ _ m _ _ _ μ _ H _ _ _ _ _ _ _ W _ _ σ hσ hirr α hα0 hα hsupp ψ hψ hψ1 γ hFE
  obtain ⟨v₀, hv₀ne⟩ := exists_ne_zero_of_isIrreducible (ρ := σ)
  obtain ⟨r₀, K₀', hK₀'c, hK₀'o, hv₀⟩ := exists_fixed_prod₀ hσ.1 v₀
  obtain ⟨ℓ₀, hℓ₀, hℓ₀v₀⟩ : ∃ ℓ₀ ∈ smoothVectors (Representation.dual σ), ℓ₀ v₀ ≠ 0 := by
    set 𝕂₀ := (congruenceSubgroup F m r₀).prod K₀'
    have h𝕂₀c : IsCompact (𝕂₀ : Set (GL (Fin m) F × H)) := by
      rw [Subgroup.coe_prod]; exact (isCompact_congruenceSubgroup F m r₀).prod hK₀'c
    have h𝕂₀o : IsOpen (𝕂₀ : Set (GL (Fin m) F × H)) := by
      rw [Subgroup.coe_prod]; exact (isOpen_congruenceSubgroup F m r₀).prod hK₀'o
    obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ (fixedVectors σ 𝕂₀), φ ⟨v₀, hv₀⟩ ≠ 0 := by
      by_contra h
      push Not at h
      exact hv₀ne (congrArg Subtype.val ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 h))
    set ef := fixedContragredientEquiv hσ.1 h𝕂₀c h𝕂₀o with hef
    refine ⟨_, ((ef.symm φ : fixedVectors (contragredient σ) 𝕂₀) : smoothVectors (Representation.dual σ)).2, ?_⟩
    have h := congrArg (fun f : Module.Dual ℂ (fixedVectors σ 𝕂₀) => f ⟨v₀, hv₀⟩) (ef.apply_symm_apply φ)
    rw [hef, fixedContragredientEquiv_apply, restrictFixed_apply] at h
    rw [hef, h]
    exact hφ
  have hcc : IsCentralCoeff m α (fun g => ℓ₀ (σ (g, 1) v₀)) := by
    refine ⟨?_, hα0, ?_, hsupp v₀ ℓ₀ hℓ₀⟩
    · set K : Subgroup (GL (Fin m) F) := (stabilizerOf σ v₀).comap (MonoidHom.inl _ _)
      have hKo : IsOpen (K : Set (GL (Fin m) F)) :=
        (hσ.1 v₀).preimage (continuous_id.prodMk continuous_const)
      refine (isLocallyConstant_of_mul_right hKo fun g k hk => ?_).continuous
      have hk' : σ (k, 1) v₀ = v₀ := mem_stabilizerOf.1 hk
      show ℓ₀ (σ (g * k, 1) v₀) = ℓ₀ (σ (g, 1) v₀)
      rw [show ((g * k, (1 : H)) : GL (Fin m) F × H) = (g, 1) * (k, 1) by simp,
        map_mul, Module.End.mul_apply, hk']
    · intro g
      rw [show ((centralUnif F m * g, (1 : H)) : GL (Fin m) F × H) =
        (centralUnif F m, 1) * (g, 1) by simp, map_mul, Module.End.mul_apply,
        hα, map_smul, smul_eq_mul]
  set t : ℝ := Real.logb (LocalField.residueCard F) ‖α‖ / m
  have hR : ∀ s : ℂ, t < s.re → ‖α * qs F s ^ m‖ < 1 := fun s hs => norm_mul_qs_pow_lt_one hα0 hs
  have hLft : ∀ s : ℂ, s.re < t + m → ‖α⁻¹ * qs F ((m : ℂ) - s) ^ m‖ < 1 := fun s hs => by
    have hs' := lt_norm_mul_qs_pow hα0 hs
    have hq : (1 : ℝ) < LocalField.residueCard F := by exact_mod_cast LocalField.one_lt_residueCard
    have hq0 : (0 : ℝ) < LocalField.residueCard F := by linarith
    have hqs : ‖qs F ((m : ℂ) - s)‖ = ((LocalField.residueCard F : ℝ) ^ (-(m : ℝ))) / ‖qs F s‖ := by
      rw [norm_qs, norm_qs, Complex.sub_re, Complex.natCast_re, neg_sub, Real.rpow_sub hq0,
        Real.rpow_neg hq0.le, Real.rpow_neg hq0.le]
      field_simp
    have hpos : 0 < ‖α * qs F s ^ m‖ :=
      norm_pos_iff.2 (mul_ne_zero hα0 (pow_ne_zero _ (qs_ne_zero s)))
    rw [norm_mul, norm_inv, norm_pow, hqs, div_pow, ← Real.rpow_natCast, ← Real.rpow_mul hq0.le]
    rw [norm_mul, norm_pow] at hpos hs'
    have hlhs : ((LocalField.residueCard F : ℝ) ^ m) ^ (-(m : ℤ)) =
        (LocalField.residueCard F : ℝ) ^ (-(m : ℝ) * m) := by
      rw [← Real.rpow_natCast, ← Real.rpow_intCast, ← Real.rpow_mul hq0.le]
      push_cast
      ring_nf
    rw [hlhs] at hs'
    rw [inv_mul_eq_div, div_div, mul_comm (‖qs F s‖ ^ m), div_lt_one hpos]
    linarith
  split_ifs with hu
  · obtain ⟨rfl, hu⟩ := hu
    obtain ⟨Φ, hΦ, r, hr, hZ⟩ := hT F μ
    obtain ⟨Φ', hΦ', hF⟩ := exists_localMatrixFourier_eq hψ hψ1 hΦ
    have h1 : σ ((1 : GL (Fin 1) F), (1 : H)) = 1 := hu 1 (one_mem _)
    have hA := hZ α _ hcc (fun g hg => by simp only [hu g hg, h1])
    have hB := hZ α⁻¹ _ hcc.inv (fun g hg => by simp only [hu _ (inv_mem hg), inv_one, h1])
    obtain ⟨P, N, hP⟩ := hcc.inv.exists_eq_div_zeta μ (hΦ.localMatrixFourier hψ hψ1)
    obtain ⟨P', N', hP'⟩ := hcc.exists_eq_div_zeta μ hΦ'
    set q : ℂ := ((LocalField.residueCard F : ℕ) : ℂ) with hq
    have hq0 : q ≠ 0 := Nat.cast_ne_zero.2 LocalField.residueCard_ne_zero
    have hne : ∀ z : ℂ, ‖z‖ < 1 → 1 - z ≠ 0 := fun z hz h => by
      rw [← sub_eq_zero.1 h, norm_one] at hz; exact lt_irrefl _ hz
    have hD : (1 - C α * X : ℂ[X]).eval 0 = 1 := by simp
    have hD' : ((1 - C α * X : ℂ[X]).comp (C q * X)).eval 0 = 1 := by simp
    have hy : ∀ s : ℂ, qs F (((1 : ℕ) : ℂ) - s) = q⁻¹ / qs F s := fun s => by
      rw [Nat.cast_one]; exact qs_one_sub s
    have hFE' := hFE Φ' hΦ' v₀ ℓ₀ hℓ₀
    rw [hF] at hFE'
    obtain ⟨c, j, hc, hγ⟩ := core (hFE Φ hΦ v₀ ℓ₀ hℓ₀) hFE' (D := 1 - C α * X) (D' := (1 - C α * X).comp (C q * X))
      (fun h => by rw [h] at hD; simp at hD) (fun h => by rw [h] at hD'; simp at hD')
      (c := r * ℓ₀ v₀) (c' := -(α * q) * (r * ℓ₀ v₀)) (mul_ne_zero hr hℓ₀v₀)
      (mul_ne_zero (neg_ne_zero.2 (mul_ne_zero hα0 hq0)) (mul_ne_zero hr hℓ₀v₀)) (i := 1)
      (((LF.poly q⁻¹ P).mul (LF.mono' q⁻¹ 1 (-(N : ℤ)))).mul (LF.mono (-(α * q)) 1))
      (f' := fun x => P'.eval x / x ^ N') ⟨P', N', fun _ _ => rfl⟩ (t := t) (t' := t + (1 : ℕ))
      (fun s hs => by
        have h2 := hne _ (hR s hs)
        refine ⟨by simpa using h2, ?_, ?_⟩
        · rw [blockA, hA s (hR s hs), h1]; simp
        · rw [blockA, hP' s (hR s hs), div_div]; simp)
      (fun s hs => by
        have h2 := hne _ (hLft s hs)
        have hx := qs_ne_zero (F := F) s
        have h3 : 1 - α * (q * qs F s) ≠ 0 := by
          intro h
          apply h2
          rw [hy]
          field_simp
          linear_combination -h
        have h4 : 1 - α⁻¹ * (q⁻¹ / qs F s) = (1 - α * (q * qs F s)) / (-(α * q) * qs F s) := by
          field_simp
          ring
        refine ⟨by simpa using h3, ?_, ?_⟩
        · rw [blockB, hP _ (hLft s hs), hy, pow_one, h4]
          simp only [sub_comp, one_comp, mul_comp, C_comp, X_comp, eval_sub, eval_one, eval_mul, eval_C, eval_X,
            zpow_neg, zpow_natCast, zpow_one]
          field_simp
        · rw [blockB, hB _ (hLft s hs), hy, h4, inv_one, h1]
          simp only [sub_comp, one_comp, mul_comp, C_comp, X_comp, eval_sub, eval_one, eval_mul, eval_C, eval_X,
            Module.End.one_apply]
          field_simp)
    refine ⟨_, c, j, hD, ?_, hc, hγ⟩
    rw [show (1 - C α * X : ℂ[X]) = C (-α) * X + C 1 by simp; ring]
    exact natDegree_linear (neg_ne_zero.2 hα0)
  · have hm := hM F m μ H W σ hσ hirr α hα0 hα hsupp hu v₀ ℓ₀ hℓ₀
    have he₀ := isSchwartzBruhat_indGL (isCompact_congruenceSubgroup F m r₀) (isOpen_congruenceSubgroup F m r₀)
    obtain ⟨Φ', hΦ', hF⟩ := exists_localMatrixFourier_eq hψ hψ1 he₀
    obtain ⟨S, a, hS⟩ := hL F m μ α⁻¹ _ hcc.inv (fun k => (hm k).2) _ (he₀.localMatrixFourier hψ hψ1)
    obtain ⟨S', a', hS'⟩ := hL F m μ α _ hcc (fun k => (hm k).1) _ hΦ'
    have hA₀ : ((μ.real (congruenceSubgroup F m r₀ : Set (GL (Fin m) F)) : ℝ) : ℂ) * ℓ₀ v₀ ≠ 0 := by
      refine mul_ne_zero ?_ hℓ₀v₀
      have : μ.real (congruenceSubgroup F m r₀ : Set (GL (Fin m) F)) ≠ 0 := by
        rw [measureReal_ne_zero_iff ((isCompact_congruenceSubgroup F m r₀).measure_lt_top.ne)]
        exact ((isOpen_congruenceSubgroup F m r₀).measure_pos μ ⟨1, one_mem _⟩).ne'
      exact_mod_cast this
    have hFE' := hFE Φ' hΦ' v₀ ℓ₀ hℓ₀
    rw [hF] at hFE'
    obtain ⟨c, j, hc, hγ⟩ := core (hFE _ he₀ v₀ ℓ₀ hℓ₀) hFE' (D := 1) (D' := 1) one_ne_zero one_ne_zero hA₀ hA₀ (i := 0)
      (LF.sum S fun k => LF.mono' (qs F (m : ℂ)) (a k) k) (LF.sum S' fun k => LF.mono (a' k) k) (t := t) (t' := t + m)
      (fun s hs => ⟨by simp, by rw [blockA_indGL μ hv₀]; simp, by rw [blockA, hS' s (hR s hs)]; simp⟩)
      (fun s hs => ⟨by simp, by rw [blockB, hS _ (hLft s hs), qs_natCast_sub]; simp, by rw [blockB_ind μ hv₀]; simp⟩)
    exact ⟨1, c, j, by simp, by simp, hc, by simpa using hγ⟩

end UpperTheory.V.Z.Gam
end
end

noncomputable section

open MeasureTheory Measure GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Parabolic
open GroundTheory.Automorphic.GodementJacquet
open scoped NNReal ENNReal Classical ValuativeRel

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace UpperTheory.V.Z.Gam

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F] {n : ℕ} {β : Fin n → ℕ}
  {W : Type} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (levi F n β) W}

private theorem exists_shape (hB : LdBlock) (hσ : IsAdmissible σ) [σ.IsIrreducible] (hc : IsCuspidal σ)
    (κ : levi F n β →* ℝ≥0) (hκ : Continuous κ) (μM : Measure (levi F n β)) [μM.IsHaarMeasure]
    {ψ : AddChar F Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) :
    ∃ γ : RatFunc ℂ, LdShape ((GroundTheory.LocalField.residueCard F : ℕ) : ℂ) γ (cntF σ) ∧ LeviFE F σ κ μM ψ γ := by
  classical
  have hsm : IsSmooth σ := hσ.1
  haveI bGL : ∀ m, BorelSpace (GL (Fin m) F) := fun m => borelSpace_GL_units m
  haveI nz : ∀ a : ↑(Set.range β), NeZero (blockSize β a) := fun a => ⟨(blockSize_pos β a).ne'⟩
  obtain ⟨e, he⟩ : ∃ e, e = leviEquivPi F β := ⟨_, rfl⟩
  obtain ⟨τ, hτ⟩ : ∃ τ, τ = twist (nnrealCharC κ) σ := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E, E = (prodPUnitEquiv.{_, 0} ((a : ↑(Set.range β)) → GL (Fin (blockSize β a)) F)).trans e.symm :=
    ⟨_, rfl⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Representation ℂ (((a : ↑(Set.range β)) → GL (Fin (blockSize β a)) F) × PUnit.{1}) W,
      ρ = τ.comp E.toMonoidHom := ⟨_, rfl⟩
  have hEx : ∀ x, E (x, (1 : PUnit.{1})) = e.symm x := fun x => by subst hE; rfl
  have hτm : ∀ m v, τ m v = nnrealCharC κ m • σ m v := fun m v => by subst hτ; rfl
  have hρx : ∀ x v, ρ (x, (1 : PUnit.{1})) v = nnrealCharC κ (e.symm x) • σ (e.symm x) v := fun x v => by
    subst hρ; rw [← hτm, ← hEx]; rfl
  have hτA : IsAdmissible τ := hτ ▸ isAdmissible_twist κ hκ σ hσ
  haveI hτI : Representation.IsIrreducible τ := hτ ▸ isIrreducible_twist κ σ
  have hρA : IsAdmissible ρ := hρ ▸ (isAdmissible_comp_iff E τ).2 hτA
  haveI hρI : Representation.IsIrreducible ρ := hρ ▸ (isIrreducible_comp_iff E τ).2 hτI
  have hℓ : ∀ ℓ, ℓ ∈ smoothVectors (Representation.dual ρ) ↔ ℓ ∈ smoothVectors σ.dual := fun ℓ => by
    subst hρ hτ
    rw [mem_smoothVectors_dual_comp_iff, mem_smoothVectors_dual_twist_iff κ hκ]
  haveI : Nontrivial W := nontrivial_of_isIrreducible σ
  obtain ⟨ω, hω⟩ := exists_blockChar (σ := τ) hτA.1
  have hω0 : ∀ b, ω b ≠ 0 := by
    intro b h0
    obtain ⟨v, hv⟩ := exists_ne (0 : W)
    apply hv
    have h1 : τ (blockUnif F b)⁻¹ (τ (blockUnif F b) v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [← h1, hω, h0, zero_smul, map_zero]
  have hcent : ∀ (i : ↑(Set.range β)) (v : W),
      ρ (Pi.mulSingle i (centralUnif F (blockSize β i)), (1 : PUnit.{1})) v = ω i • v := by
    intro i v
    rw [← hω, ← leviEquivPi_symm_mulSingle, ← he, ← hEx]
    subst hρ; rfl
  have hcpt : ∀ (v : W), ∀ ℓ ∈ smoothVectors (Representation.dual ρ), ∃ C, IsCompact C ∧
      ∀ (x : (a : ↑(Set.range β)) → GL (Fin (blockSize β a)) F),
        ℓ (ρ (x, (1 : PUnit.{1})) v) ≠ 0 →
          ∃ j : ↑(Set.range β) → ℤ, (fun i => centralUnif F (blockSize β i) ^ j i) * x ∈ C := by
    intro v ℓ hl
    obtain ⟨C0, hC0, hC0m⟩ := exists_compact_of_coeff hsm hc v ((hℓ ℓ).1 hl) (fun _ => 0)
      (fun a => (blockSize β a : ℤ) - 1)
    refine ⟨e '' C0, hC0.image e.continuous, fun x hx => ?_⟩
    refine ⟨fun a => -(ordDet (x a) / (blockSize β a : ℤ)), ?_⟩
    obtain ⟨y, hy⟩ : ∃ y, y = (fun i => centralUnif F (blockSize β i) ^ (-(ordDet (x i) / (blockSize β i : ℤ)))) * x :=
      ⟨_, rfl⟩
    rw [← hy]
    refine ⟨e.symm y, hC0m _ ?_ ?_, e.apply_symm_apply y⟩
    · have h1 : ρ (y, (1 : PUnit.{1})) v =
          (∏ i, ω i ^ (-(ordDet (x i) / (blockSize β i : ℤ)))) • ρ (x, (1 : PUnit.{1})) v := by
        have hp : (y, (1 : PUnit.{1})) = ((fun i => centralUnif F (blockSize β i) ^ (-(ordDet (x i) / (blockSize β i : ℤ)))),
            (1 : PUnit.{1})) * (x, (1 : PUnit.{1})) := by rw [hy]; rfl
        rw [hp, map_mul, Module.End.mul_apply, apply_centralPow ρ hω0 hcent]
      intro h0
      apply hx
      have h2 : ℓ (ρ (y, (1 : PUnit.{1})) v) = 0 := by rw [hρx, map_smul, h0, smul_zero]
      rw [h1, map_smul, smul_eq_mul] at h2
      exact (mul_eq_zero.1 h2).resolve_left (Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (hω0 i))
    · intro b
      rw [← ordDet_leviEquivPi, ← he, e.apply_symm_apply, hy]
      simp only [Pi.mul_apply, ordDet_centralUnif_zpow_mul]
      have hd : (0:ℤ) < blockSize β b := by exact_mod_cast blockSize_pos β b
      have h3 := Int.emod_nonneg (ordDet (x b)) hd.ne'
      have h4 := Int.emod_lt_of_pos (ordDet (x b)) hd
      have h5 := Int.mul_ediv_add_emod (ordDet (x b)) (blockSize β b)
      constructor <;> linarith
  obtain ⟨μ', hμ'⟩ : ∃ μ' : (a : ↑(Set.range β)) → Measure (GL (Fin (blockSize β a)) F),
      μ' = fun _ => Measure.haar := ⟨_, rfl⟩
  haveI hμ'H : ∀ a, (μ' a).IsHaarMeasure := fun a => by subst hμ'; infer_instance
  obtain ⟨γ, hγs, hγfe⟩ := ldMulti_all (F := F) (W := W) hB hψ hψ1 (Fintype.card ↑(Set.range β))
    ↑(Set.range β) rfl (fun a => blockSize β a) μ' PUnit.{1} ρ hρA hρI ω hω0 hcent hcpt
  obtain ⟨s₁, hs₁⟩ := exists_integrable_multi ρ hρA.1 hω0 hcent hcpt μ'
  refine ⟨γ, ?_, ?_⟩
  · convert hγs using 1
    subst he
    unfold cntF
    rw [Finset.sum_boole, Nat.cast_id]
    congr 1
    apply Finset.filter_congr
    intro i _
    apply and_congr_right
    intro _
    apply forall₂_congr
    intro g hg
    have hk : κ ((leviEquivPi F β).symm (Pi.mulSingle i g)) = 1 := by
      refine eq_one_of_mem_compact κ hκ (K := (integralGL F (blockSize β i)).map
        (((leviEquivPi F β).symm.toMonoidHom).comp (MonoidHom.mulSingle _ i))) ?_ (Subgroup.mem_map_of_mem _ hg)
      rw [Subgroup.coe_map]
      exact (isCompact_integralGL F _).image
        (f := fun x => (leviEquivPi F β).symm (Pi.mulSingle i x))
        ((leviEquivPi F β).symm.continuous.comp (continuous_mulSingle (A := fun a : ↑(Set.range β) => GL (Fin (blockSize β a)) F) i))
    have hx : ρ (Pi.mulSingle i g, (1 : PUnit.{1})) = σ ((leviEquivPi F β).symm (Pi.mulSingle i g)) := by
      refine LinearMap.ext fun v => ?_
      rw [hρx, nnrealCharC_apply, hk]
      simp
    rw [hx]
  · intro φ hφ w ℓ hl
    have hlρ := (hℓ ℓ).2 hl
    obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : (a : ↑(Set.range β)) → Matrix (Fin (blockSize β a)) (Fin (blockSize β a)) F → ℂ,
        Ψ = fun a => blockTensor β φ a := ⟨_, rfl⟩
    have hΨs : ∀ a, IsSchwartzBruhat (Ψ a) := by subst hΨ; exact isSchwartzBruhat_blockTensor hφ
    have hΨh : ∀ a, IsSchwartzBruhat (GJMatrix.localMatrixFourier ψ (Ψ a)) :=
      fun a => (hΨs a).localMatrixFourier hψ hψ1
    have hA : ∀ s x, leviIntegrand σ κ (leviTensor β φ) w ℓ s (e.symm x) = multiA ρ Ψ w ℓ s x := by
      intro s x
      subst he hΨ
      simp only [leviIntegrand, multiA, leviTensor_leviEquivPi_symm, detPow_leviEquivPi_symm, hρx, map_smul,
        smul_eq_mul, nnrealCharC_apply, Finset.prod_mul_distrib]
      ring
    have hB2 : ∀ s x, leviIntegrandB σ κ (leviTensorHat β ψ φ) w ℓ s (e.symm x) =
        multiB ρ (fun a => GJMatrix.localMatrixFourier ψ (Ψ a)) w ℓ s x := by
      intro s x
      subst he hΨ
      have hd : ∀ a, detPow (x a) ((blockSize β a : ℂ) - s) = ((detModulusPow (x a) : ℝ) : ℂ) * detPow (x a) (-s) :=
        fun a => by rw [sub_eq_add_neg, detPow_add, detPow_natCast]
      simp only [leviIntegrandB, multiB, leviTensorHat_leviEquivPi_symm, detPow_leviEquivPi_symm,
        leviModulus_leviEquivPi_symm, hρx, map_inv, map_smul, smul_eq_mul, nnrealCharC_apply, hd,
        Finset.prod_mul_distrib]
      push_cast
      ring
    obtain ⟨em, hem⟩ : ∃ em : levi F n β ≃ᵐ ((a : ↑(Set.range β)) → GL (Fin (blockSize β a)) F),
        em = e.toHomeomorph.toMeasurableEquiv := ⟨_, rfl⟩
    have hemx : ∀ m, em m = e m := fun m => by subst hem; rfl
    haveI : (μM.map em).IsHaarMeasure := by
      subst hem
      exact ContinuousMulEquiv.isHaarMeasure_map μM e
    obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, c = (μM.map em).haarScalarFactor (Measure.pi μ') := ⟨_, rfl⟩
    have hmap : μM.map em = (c : ℝ≥0∞) • Measure.pi μ' := by
      rw [hc]; exact isMulLeftInvariant_eq_smul _ _
    have hcomp : ∀ g : levi F n β → ℂ, (fun x => g (e.symm x)) ∘ em = g := fun g => by
      funext m; simp only [Function.comp, hemx, ContinuousMulEquiv.symm_apply_apply]
    have hint : ∀ g : levi F n β → ℂ,
        Integrable (fun x => g (e.symm x)) (Measure.pi μ') → Integrable g μM := by
      intro g hg
      have := hg.smul_measure (c := (c : ℝ≥0∞)) ENNReal.coe_ne_top
      rw [← hmap, em.measurableEmbedding.integrable_map_iff, hcomp] at this
      exact this
    have hI : ∀ g : levi F n β → ℂ, ∫ m, g m ∂μM = (c : ℂ) * ∫ x, g (e.symm x) ∂(Measure.pi μ') := by
      intro g
      have h1 := integral_map_equiv (μ := μM) em (fun x => g (e.symm x))
      rw [hmap, integral_smul_measure] at h1
      simp only [hemx, ContinuousMulEquiv.symm_apply_apply] at h1
      rw [← h1]
      simp [Complex.real_smul]
    refine ⟨⟨s₁, fun s hs => hint _ ?_⟩, ⟨-s₁, fun s hs => hint _ ?_⟩, ?_⟩
    · simp only [hA]
      exact (hs₁ Ψ hΨs w ℓ hlρ).1 s hs
    · simp only [hB2]
      exact (hs₁ _ hΨh w ℓ hlρ).2 s hs
    · refine ((hγfe Ψ hΨs w ℓ hlρ).const_mul (c : ℂ)).congr ⟨0, fun s _ => ?_⟩ ⟨0, fun s _ => ?_⟩
      · rw [hI]; simp only [hA]
      · rw [hI]; simp only [hB2]

end UpperTheory.V.Z.Gam

theorem UpperTheory.V.Z.Gam.leviDiv :
    UpperTheory.V.Z.Gam.LeviDiv := by
  intro F _ _ _ _ _ _ n β W _ _ σ hσ hirr hc κ hκ μ _ ψ hψ hψ1 γ hγ
  have hB : LdBlock := ldBlock_of UpperTheory.local_zeta_integral_laurent_expansion UpperTheory.local_zeta_integral_shell_mean UpperTheory.local_zeta_integral_tate_comparison
  obtain ⟨γ₀, hshape, hfe⟩ := UpperTheory.V.Z.Gam.exists_shape hB hσ hc κ hκ μ hψ hψ1
  obtain rfl := UpperTheory.local_zeta_functional_uniqueness F n β W σ hσ hirr κ hκ μ ψ γ γ₀ hγ hfe
  exact hshape
