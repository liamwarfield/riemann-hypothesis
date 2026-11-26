module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertiaTorsionQuotientConjInvariantDecomposition
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspFunctionalValueModPrimePowDiamondIndepende

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertiaCocycleEqZeroOfVanishWildTameGenerator
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertiaCocycleEqZeroOfVanishWildTameGenerator
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA GlobalTheory.InertCoh
open scoped Matrix

namespace GlobalTheory.CocWildTame

theorem eq_zero_on_Ine : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : R2 Ω l) (B : ValuationSubring Ω) (γ : G ℚ Ω), Formalism.BasicNotions.TameGenAt B γ → ∀ z : G ℚ Ω → Fin 2 → Qbar l, (∀ i, Continuous fun s => z s i) → (∀ s ∈ Ine (F := ℚ) B, ∀ t ∈ Ine (F := ℚ) B, z (s * t) = z s + mat W s *ᵥ z t) → (∀ σ : G ℚ Ω, (∀ y : Ω, y ≠ 0 → B.valuation (σ y / y - 1) < 1) → z σ = 0) → z γ = 0 → ∀ s ∈ Ine (F := ℚ) B, z s = 0 := by
  intro l _ Ω _ _ W B γ hγ z hz hcoc hw hγ0 s hs
  have hwild : ∀ σ : G ℚ Ω, (∀ y : Ω, y ≠ 0 → B.valuation (σ y / y - 1) < 1) → σ ∈ Ine (F := ℚ) B :=
    fun σ hσ => GlobalTheory.TameConjInv.wild_mem_Ine B hσ
  have h1 : z 1 = 0 := hw 1 (fun y hy => by simp [div_self hy])
  have key : ∀ h ∈ Subgroup.closure (insert γ {σ : G ℚ Ω | ∀ y : Ω, y ≠ 0 → B.valuation (σ y / y - 1) < 1}),
      h ∈ Ine (F := ℚ) B ∧ z h = 0 := by
    intro h hh
    induction hh using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | hx
      · exact ⟨hγ.1, hγ0⟩
      · exact ⟨hwild x hx, hw x hx⟩
    | one => exact ⟨one_mem _, h1⟩
    | mul x y _ _ ihx ihy =>
      obtain ⟨hx, hzx⟩ := ihx
      obtain ⟨hy, hzy⟩ := ihy
      exact ⟨mul_mem hx hy, by rw [hcoc x hx y hy, hzx, hzy, Matrix.mulVec_zero, add_zero]⟩
    | inv x _ ihx =>
      obtain ⟨hx, hzx⟩ := ihx
      refine ⟨inv_mem hx, ?_⟩
      have := hcoc x⁻¹ (inv_mem hx) x hx
      rw [inv_mul_cancel, h1, hzx, Matrix.mulVec_zero, add_zero] at this
      exact this.symm
  have hclosed : IsClosed {t : G ℚ Ω | z t = 0} := by
    have : {t : G ℚ Ω | z t = 0} = ⋂ i, (fun t => z t i) ⁻¹' {0} := by
      ext t; simp [funext_iff]
    rw [this]
    exact isClosed_iInter fun i => (isClosed_singleton).preimage (hz i)
  have hsub : ((Subgroup.closure (insert γ {σ : G ℚ Ω | ∀ y : Ω, y ≠ 0 → B.valuation (σ y / y - 1) < 1}) :
      Subgroup (G ℚ Ω)) : Set (G ℚ Ω)) ⊆ {t : G ℚ Ω | z t = 0} := fun h hh => (key h hh).2
  exact (closure_minimal hsub hclosed) (hγ.2 hs)

end GlobalTheory.CocWildTame
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertiaCocycleEqZeroOfVanishWildTameGeneratorStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA GlobalTheory.InertCoh
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertiaCocycle_eq_zero_of_vanish_wild_tameGenerator : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : R2 Ω l) (B : ValuationSubring Ω) (γ : G ℚ Ω), Formalism.BasicNotions.TameGenAt B γ → ∀ z : G ℚ Ω → Fin 2 → Qbar l, (∀ i, Continuous fun s => z s i) → (∀ s ∈ Ine (F := ℚ) B, ∀ t ∈ Ine (F := ℚ) B, z (s * t) = z s + mat W s *ᵥ z t) → (∀ σ : G ℚ Ω, (∀ y : Ω, y ≠ 0 → B.valuation (σ y / y - 1) < 1) → z σ = 0) → z γ = 0 → ∀ s ∈ Ine (F := ℚ) B, z s = 0 := by
  first | exact @GlobalTheory.CocWildTame.eq_zero_on_Ine | exact GlobalTheory.CocWildTame.eq_zero_on_Ine | (intros; apply GlobalTheory.CocWildTame.eq_zero_on_Ine <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegralCoboundaryWildInertiaAwayFromL
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegralCoboundaryWildInertiaAwayFromL
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA GlobalTheory.InertCoh
open scoped Matrix

namespace GlobalTheory.WildCob

theorem eq_one_of_pow_near {K : Type} [NormedField K] [IsUltrametricDist K] {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n K) (h1 : ∀ i j, ‖(A - 1) i j‖ < 1)
    (h : ∀ ε : ℝ, 0 < ε → ∃ m : ℕ, ‖(m : K)‖ = 1 ∧ ∀ i j, ‖(A ^ m - 1) i j‖ < ε) : A = 1 := by
  obtain ⟨X, rfl⟩ : ∃ X, A = 1 + X := ⟨A - 1, by abel⟩
  simp only [add_sub_cancel_left] at h1
  by_contra hne
  have hX : ∃ i j, X i j ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hne (by rw [show X = 0 from Matrix.ext hc, add_zero])
  obtain ⟨i₀, j₀, h0⟩ := hX
  obtain ⟨⟨a, b⟩, -, hab⟩ := Finset.exists_max_image (Finset.univ : Finset (n × n)) (fun p => ‖X p.1 p.2‖)
    ⟨(i₀, j₀), Finset.mem_univ _⟩
  set r := ‖X a b‖ with hr
  have hle : ∀ i j, ‖X i j‖ ≤ r := fun i j => hab (i, j) (Finset.mem_univ _)
  have hr0 : 0 < r := (norm_pos_iff.2 h0).trans_le (hle _ _)
  have hr1 : r < 1 := h1 a b
  have hmul : ∀ (Y Z : Matrix n n K) (s t : ℝ), 0 ≤ s → 0 ≤ t → (∀ i j, ‖Y i j‖ ≤ s) → (∀ i j, ‖Z i j‖ ≤ t) →
      ∀ i j, ‖(Y * Z) i j‖ ≤ s * t := by
    intro Y Z s t hs ht hY hZ i j
    rw [Matrix.mul_apply]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hs ht) fun k _ => ?_
    rw [norm_mul]
    exact mul_le_mul (hY _ _) (hZ _ _) (norm_nonneg _) hs
  have hrr : 0 ≤ r * r := mul_nonneg hr0.le hr0.le
  have key : ∀ m : ℕ, ∀ i j, ‖((1 + X) ^ m - 1 - (m : K) • X) i j‖ ≤ r * r := by
    intro m
    induction m with
    | zero => intro i j; simpa using hrr
    | succ m ih =>
      intro i j
      have e : (1 + X) ^ (m + 1) - 1 - ((m + 1 : ℕ) : K) • X =
          ((1 + X) ^ m - 1 - (m : K) • X) + (((1 + X) ^ m - 1 - (m : K) • X) * X + (m : K) • (X * X)) := by
        simp only [pow_succ, mul_add, sub_mul, mul_one, one_mul, Nat.cast_succ, add_smul, one_smul, Matrix.smul_mul]
        abel
      rw [e, Matrix.add_apply, Matrix.add_apply]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ih i j)
        ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)))
      · exact (hmul _ _ _ _ hrr hr0.le ih hle i j).trans (mul_le_of_le_one_right hrr hr1.le)
      · rw [Matrix.smul_apply, smul_eq_mul, norm_mul]
        exact (mul_le_of_le_one_left (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one K m)).trans
          (hmul _ _ _ _ hr0.le hr0.le hle hle i j)
  obtain ⟨m, hm, hm'⟩ := h r hr0
  have e : (m : K) * X a b = ((1 + X) ^ m - 1) a b + -(((1 + X) ^ m - 1 - (m : K) • X) a b) := by
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have h2 : ‖(m : K) * X a b‖ < r := by
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt (hm' a b) ?_)
    rw [norm_neg]
    exact (key m a b).trans_lt (mul_lt_of_lt_one_right hr0 hr1)
  rw [norm_mul, hm, one_mul] at h2
  exact lt_irrefl _ h2

theorem exists_open_subgroup {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (V : Set (G ℚ Ω)) (hV : V ∈ nhds (1 : G ℚ Ω)) :
    ∃ H : Subgroup (G ℚ Ω), IsOpen (H : Set (G ℚ Ω)) ∧ H.index ≠ 0 ∧ (H : Set (G ℚ Ω)) ⊆ V := by
  obtain ⟨L, hL, hsub⟩ := (krullTopology_mem_nhds_one_iff ℚ Ω _).mp hV
  have : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  refine ⟨L.fixingSubgroup, L.fixingSubgroup_isOpen, ?_, hsub⟩
  rw [← IntermediateField.finrank_eq_fixingSubgroup_index]
  exact Module.finrank_pos.ne'

theorem exists_pow_mem {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (B : ValuationSubring Ω) {l : ℕ} (hl : l.Prime)
    (hvl : ¬ B.valuation (l : Ω) < 1) {σ : G ℚ Ω} (hσ : σ ∈ GlobalTheory.WeilDeligne.Wild ℚ B) (V : Set (G ℚ Ω))
    (hV : V ∈ nhds (1 : G ℚ Ω)) : ∃ m : ℕ, ¬ l ∣ m ∧ σ ^ m ∈ V := by
  obtain ⟨H, ho, hidx, hsub⟩ := exists_open_subgroup V hV
  have hvl1 : B.valuation (l : Ω) = 1 :=
    le_antisymm ((B.valuation_le_one_iff _).mpr (natCast_mem B l)) (not_lt.mp hvl)
  obtain ⟨N, hN, -, hmem⟩ := Subgroup.exists_pow_mem_of_index_ne_zero hidx σ
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' l hl.ne_one
  refine ⟨m, hm, hsub (GlobalTheory.WildKill.mem_of_wild B H ho (σ ^ m) (l ^ a) ?_
    ((GlobalTheory.WeilDeligne.Wild ℚ B).pow_mem hσ m) ?_)⟩
  · rw [Nat.cast_pow, map_pow, hvl1, one_pow]; exact lt_irrefl _
  · rw [← pow_mul, mul_comm]; exact hmem

theorem isUnit_natCast {l : ℕ} [hl : Fact l.Prime] {m : ℕ} (hm : ¬ l ∣ m) : IsUnit (m : ℤ_[l]) := by
  rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
  exact (Nat.Prime.coprime_iff_not_dvd hl.out).2 hm

theorem norm_natCast_eq_one {l : ℕ} [hl : Fact l.Prime] {m : ℕ} (hm : ¬ l ∣ m) : ‖(m : Qbar l)‖ = 1 := by
  rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), norm_algebraMap', Padic.norm_natCast_eq_one_iff]
  exact (Nat.Prime.coprime_iff_not_dvd hl.out).2 hm

noncomputable def aff {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime] (W : R2 Ω l) (z : G ℚ Ω → Fin 2 → Qbar l)
    (s : G ℚ Ω) : Matrix (Fin 2 ⊕ Unit) (Fin 2 ⊕ Unit) (Qbar l) :=
  Matrix.fromBlocks (mat W s) (Matrix.of fun i _ => z s i) 0 1

theorem main : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (W : R2 Ω l) (c : Coef l) (B : ValuationSubring Ω) (q : Pl), Continuous W → (∀ s i j, mat W s i j ∈ c.O) → IsPlaceOver B q → ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∀ z ∈ coc W c (Ine (F := ℚ) B), ∃ v : Fin 2 → Qbar l, (∀ i, v i ∈ c.O) ∧ ∀ σ : G ℚ Ω, (∀ y : Ω, y ≠ 0 → B.valuation (σ y / y - 1) < 1) → z σ = mat W σ *ᵥ v - v := by
  intro l hl Ω _ _ _ W c B q hW _ hB hq z hz
  obtain ⟨hzc, hzO, hzm⟩ := mem_coc.1 hz
  have hvl : ¬ B.valuation (l : Ω) < 1 := by
    intro h
    apply hq
    rw [← hB]
    simpa using h
  set P := GlobalTheory.WeilDeligne.Wild ℚ B with hP
  have hPI : P ≤ Ine (F := ℚ) B := GlobalTheory.WeilDeligne.Wild_le_Ine
  have hz1 : z 1 = 0 := by
    have := hzm 1 (one_mem _) 1 (one_mem _)
    rw [mul_one, mat, map_one, Units.val_one, Matrix.one_mulVec] at this
    exact left_eq_add.1 this
  have ha1 : aff W z 1 = 1 := by
    rw [aff, ← Matrix.fromBlocks_one]
    congr 1
    · simp
    · ext i j; simp [hz1]
  let M : P →* Matrix (Fin 2 ⊕ Unit) (Fin 2 ⊕ Unit) (Qbar l) :=
    { toFun := fun s => aff W z s
      map_one' := ha1
      map_mul' := fun s t => by
        simp only [aff, Matrix.fromBlocks_multiply, Subgroup.coe_mul]
        congr 1
        · simp [mat]
        · ext i j
          rw [hzm s (hPI s.2) t (hPI t.2), Matrix.mul_one]
          exact add_comm _ _
        · simp
        · simp }
  have hM : ∀ s : P, M s = aff W z s := fun _ => rfl
  have hcont : ∀ i j, Continuous fun s => aff W z s i j := by
    have hWc : Continuous fun s => mat W s := Units.continuous_val.comp hW
    rintro (i | i) (j | j)
    · exact hWc.matrix_elem i j
    · exact hzc i
    · exact continuous_const
    · exact continuous_const
  have hV : ∀ ε : ℝ, 0 < ε → {s : G ℚ Ω | ∀ i j, ‖(aff W z s - 1) i j‖ < ε} ∈ nhds (1 : G ℚ Ω) := by
    intro ε hε
    refine IsOpen.mem_nhds ?_ (by simp [ha1, hε])
    simp only [Set.setOf_forall]
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
    exact isOpen_lt ((hcont i j).sub continuous_const).norm continuous_const
  have hker : ∀ s : P, (∀ i j, ‖(aff W z s - 1) i j‖ < 1) → s ∈ M.ker := by
    intro s hs
    refine eq_one_of_pow_near (M s) hs fun ε hε => ?_
    obtain ⟨m, hm, hm'⟩ := exists_pow_mem B hl.out hvl s.2 _ (hV ε hε)
    exact ⟨m, norm_natCast_eq_one hm, by rw [← map_pow]; exact hm'⟩
  have hfi : M.ker.FiniteIndex := by
    obtain ⟨H, -, hidx, hsub⟩ := exists_open_subgroup _ (hV 1 one_pos)
    have : H.FiniteIndex := ⟨hidx⟩
    exact Subgroup.finiteIndex_of_le (H := H.subgroupOf P) fun s hs => hker s (hsub hs)
  classical
  let Q := P ⧸ M.ker
  letI : Fintype Q := Fintype.ofFinite _
  have hcard : ¬ l ∣ Fintype.card Q := by
    intro hd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card l hd
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨m, hm, hm'⟩ := exists_pow_mem B hl.out hvl s.2 _ (hV 1 one_pos)
    apply hm
    rw [← hx, orderOf_dvd_iff_pow_eq_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hker _ hm'
  let Mq : Q →* Matrix (Fin 2 ⊕ Unit) (Fin 2 ⊕ Unit) (Qbar l) := QuotientGroup.lift M.ker M fun _ h => h
  have hMq : ∀ x : Q, Mq x = aff W z (x.out : P) := fun x => by
    conv_lhs => rw [← QuotientGroup.out_eq' x]
    rfl
  have hS : ∀ s : P, aff W z s * ∑ x : Q, Mq x = ∑ x : Q, Mq x := fun s => by
    rw [Finset.mul_sum]
    exact Fintype.sum_equiv (Equiv.mulLeft (s : Q)) _ _ fun x => by
      rw [Equiv.coe_mulLeft, map_mul]; rfl
  obtain ⟨u, hu⟩ := isUnit_natCast hcard
  have hinv : (Fintype.card Q : Qbar l) * algebraMap ℤ_[l] (Qbar l) (↑u⁻¹) = 1 := by
    rw [← map_natCast (algebraMap ℤ_[l] (Qbar l)), ← hu, ← map_mul, Units.mul_inv, map_one]
  refine ⟨fun i => -(algebraMap ℤ_[l] (Qbar l) (↑u⁻¹) * ∑ x : Q, z (x.out : P) i), fun i =>
    c.O.neg_mem (c.O.mul_mem (c.O.algebraMap_mem _) (c.O.sum_mem fun x _ => hzO _ _)), fun σ hσ => ?_⟩
  funext i
  have h1 := congrFun (congrFun (hS ⟨σ, hσ⟩) (Sum.inl i)) (Sum.inr ())
  simp only [hMq, Matrix.mul_apply, Matrix.sum_apply, aff, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂, Matrix.of_apply, Matrix.one_apply_eq, Fin.sum_univ_two,
    Finset.univ_unique, Finset.sum_singleton, Finset.sum_const, Finset.card_univ, Finset.card_singleton, one_smul, nsmul_eq_mul, Nat.cast_one,
    one_mul, mul_one] at h1
  simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  linear_combination (algebraMap ℤ_[l] (Qbar l) (↑u⁻¹)) * h1 - z σ i * hinv

end GlobalTheory.WildCob
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegralCoboundaryWildInertiaAwayFromLStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA GlobalTheory.InertCoh
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_coboundary_wildInertia_away_from_l : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (W : R2 Ω l) (c : Coef l) (B : ValuationSubring Ω) (q : Pl), Continuous W → (∀ s i j, mat W s i j ∈ c.O) → IsPlaceOver B q → ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∀ z ∈ coc W c (Ine (F := ℚ) B), ∃ v : Fin 2 → Qbar l, (∀ i, v i ∈ c.O) ∧ ∀ σ : G ℚ Ω, (∀ y : Ω, y ≠ 0 → B.valuation (σ y / y - 1) < 1) → z σ = mat W σ *ᵥ v - v := by
  first | exact @GlobalTheory.WildCob.main | exact GlobalTheory.WildCob.main | (intros; apply GlobalTheory.WildCob.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoboundaryOfPadicAlgClUniformApprox
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoboundaryOfPadicAlgClUniformApprox
open scoped Matrix

namespace GlobalTheory.UniformCoboundary

theorem exists_finset_fixed {K : Type} [Field K] {Γ : Type} (S : Set Γ)
    (M : Γ → Matrix (Fin 2) (Fin 2) K) :
    ∃ T : Finset Γ, (↑T ⊆ S) ∧
      ∀ v : Fin 2 → K, (∀ t ∈ T, M t *ᵥ v = v) → ∀ s ∈ S, M s *ᵥ v = v := by
  classical
  let W : Finset Γ → Submodule K (Fin 2 → K) :=
    fun T => ⨅ t ∈ T, LinearMap.ker (Matrix.toLin' (M t) - LinearMap.id)
  have hW : ∀ (T : Finset Γ) (v : Fin 2 → K), v ∈ W T ↔ ∀ t ∈ T, M t *ᵥ v = v := by
    intro T v
    simp only [W, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      Matrix.toLin'_apply, LinearMap.id_apply, sub_eq_zero]
  obtain ⟨_, ⟨T, hTS, rfl⟩, hmin⟩ :=
    (wellFounded_lt (α := Submodule K (Fin 2 → K))).has_min
      {P | ∃ T : Finset Γ, ↑T ⊆ S ∧ W T = P} ⟨_, ∅, by simp, rfl⟩
  refine ⟨T, hTS, fun v hv s hs => ?_⟩
  have hle : W (insert s T) ≤ W T := by
    intro w hw
    rw [hW] at hw ⊢
    exact fun t ht => hw t (Finset.mem_insert_of_mem ht)
  have hnlt : ¬ W (insert s T) < W T :=
    hmin _ ⟨insert s T, by rw [Finset.coe_insert]; exact Set.insert_subset hs hTS, rfl⟩
  have heq : W (insert s T) = W T := (hle.lt_or_eq).resolve_left hnlt
  have hv' : v ∈ W (insert s T) := by rw [heq, hW]; exact hv
  exact (hW _ _).1 hv' s (Finset.mem_insert_self s T)

theorem exists_bound {K : Type} [NormedField K] {ι : Type} [Fintype ι]
    (L : (ι → K) →ₗ[K] (Fin 2 → K)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (w : ι → K) (ε : ℝ), 0 ≤ ε → (∀ p, ‖w p‖ ≤ ε) → ∀ k, ‖L w k‖ ≤ C * ε := by
  classical
  refine ⟨∑ k, ∑ p, ‖L (Pi.single p 1) k‖, by positivity, fun w ε hε hw k => ?_⟩
  have h1 : w = ∑ p, w p • (Pi.single p 1 : ι → K) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  have h2 : L w k = ∑ p, w p * L (Pi.single p 1) k := by
    conv_lhs => rw [h1]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, Finset.sum_apply]
  have h3 : ‖L w k‖ ≤ (∑ p, ‖L (Pi.single p 1) k‖) * ε := by
    rw [h2, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_left (hw p) (norm_nonneg _)
  refine h3.trans (mul_le_mul_of_nonneg_right ?_ hε)
  exact Finset.single_le_sum (f := fun k => ∑ p, ‖L (Pi.single p 1) k‖)
    (fun k _ => by positivity) (Finset.mem_univ k)

theorem coboundary_of_approx {K : Type} [NormedField K] (q : K) (hq : ‖q‖ < 1) (Γ : Type)
    (S : Set Γ) (M : Γ → Matrix (Fin 2) (Fin 2) K) (f : ℕ → Γ → Fin 2 → K) (y : Γ → Fin 2 → K)
    (hM : ∀ s i j, ‖M s i j‖ ≤ 1)
    (hf : ∀ r, ∃ v : Fin 2 → K, ∀ s ∈ S, f r s = M s *ᵥ v - v)
    (hy : ∀ r s i, ‖y s i - f r s i‖ ≤ ‖q ^ r‖) :
    ∃ v : Fin 2 → K, ∀ s ∈ S, y s = M s *ᵥ v - v := by
  classical
  obtain ⟨T, hTS, hT⟩ := exists_finset_fixed S M
  let e : (Fin 2 → K) →ₗ[K] (T × Fin 2 → K) :=
    LinearMap.pi fun p => (LinearMap.proj p.2).comp (Matrix.toLin' (M p.1) - LinearMap.id)
  have he : ∀ v (p : T × Fin 2), e v p = (M p.1 *ᵥ v - v) p.2 := by
    intro v p
    simp [e, Matrix.toLin'_apply]
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective e.rangeRestrict
    (LinearMap.range_rangeRestrict e)
  obtain ⟨L, hL⟩ := LinearMap.exists_extend g
  have heL : ∀ v, e (L (e v)) = e v := by
    intro v
    have h1 : L (e v) = g (e.rangeRestrict v) := LinearMap.congr_fun hL (e.rangeRestrict v)
    have h2 : e.rangeRestrict (g (e.rangeRestrict v)) = e.rangeRestrict v :=
      LinearMap.congr_fun hg (e.rangeRestrict v)
    rw [h1]
    exact congrArg Subtype.val h2
  have hSL : ∀ v, ∀ s ∈ S, M s *ᵥ (L (e v)) - L (e v) = M s *ᵥ v - v := by
    intro v s hs
    have h0 : e (L (e v) - v) = 0 := by rw [map_sub, heL, sub_self]
    have h1 : ∀ t ∈ T, M t *ᵥ (L (e v) - v) = L (e v) - v := by
      intro t ht
      rw [← sub_eq_zero]
      funext i
      have := congrFun h0 (⟨t, ht⟩, i)
      rw [he] at this
      exact this
    have h2 := hT _ h1 s hs
    rw [Matrix.mulVec_sub] at h2
    rw [sub_eq_sub_iff_sub_eq_sub]
    exact h2
  obtain ⟨C, hC, hCb⟩ := exists_bound L
  let Y : T × Fin 2 → K := fun p => y p.1 p.2
  refine ⟨L Y, fun s hs => ?_⟩
  funext i
  rw [← sub_eq_zero, ← norm_le_zero_iff]
  have key : ∀ r : ℕ, ‖y s i - (M s *ᵥ L Y - L Y) i‖ ≤ (1 + 3 * C) * ‖q‖ ^ r := by
    intro r
    obtain ⟨vr, hvr⟩ := hf r
    have hε : 0 ≤ ‖q‖ ^ r := by positivity
    have hu : ∀ k, ‖L (Y - e vr) k‖ ≤ C * ‖q‖ ^ r := by
      refine hCb _ _ hε fun p => ?_
      rw [Pi.sub_apply, he, ← hvr p.1 (hTS p.1.2), ← norm_pow]
      exact hy r p.1 p.2
    have hv : L Y = L (e vr) + L (Y - e vr) := by simp [map_sub]
    generalize L (Y - e vr) = u at hu hv
    have hid : M s *ᵥ L Y - L Y = f r s + (M s *ᵥ u - u) := by
      rw [hvr s hs, ← hSL vr s hs, hv, Matrix.mulVec_add]
      abel
    have hMu : ‖(M s *ᵥ u) i‖ ≤ 2 * (C * ‖q‖ ^ r) := by
      have : (M s *ᵥ u) i = M s i 0 * u 0 + M s i 1 * u 1 := by
        simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      rw [this]
      have hb : ∀ k, ‖M s i k * u k‖ ≤ C * ‖q‖ ^ r := fun k => by
        rw [norm_mul]
        exact (mul_le_of_le_one_left (norm_nonneg _) (hM s i k)).trans (hu k)
      have := norm_add_le (M s i 0 * u 0) (M s i 1 * u 1)
      linarith [hb 0, hb 1]
    have h1 : y s i - (M s *ᵥ L Y - L Y) i = (y s i - f r s i) - ((M s *ᵥ u) i - u i) := by
      rw [hid]
      simp only [Pi.add_apply, Pi.sub_apply]
      ring
    have h2 := hy r s i
    rw [norm_pow] at h2
    rw [h1]
    have h3 := norm_sub_le (y s i - f r s i) ((M s *ᵥ u) i - u i)
    have h4 := norm_sub_le ((M s *ᵥ u) i) (u i)
    have h5 := hu i
    linarith
  have hlim : Filter.Tendsto (fun r : ℕ => (1 + 3 * C) * ‖q‖ ^ r) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg q) hq).const_mul (1 + 3 * C)
  exact ge_of_tendsto' hlim key

theorem coboundary_of_padic_approx : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) (S : Set Γ) (M : Γ → Matrix (Fin 2) (Fin 2) (PadicAlgCl l)) (f : ℕ → Γ → Fin 2 → PadicAlgCl l) (y : Γ → Fin 2 → PadicAlgCl l), (∀ s i j, ‖M s i j‖ ≤ 1) → (∀ r, ∃ v : Fin 2 → PadicAlgCl l, ∀ s ∈ S, f r s = M s *ᵥ v - v) → (∀ r s i, ‖y s i - f r s i‖ ≤ ‖((l : ℕ) : PadicAlgCl l) ^ r‖) → ∃ v : Fin 2 → PadicAlgCl l, ∀ s ∈ S, y s = M s *ᵥ v - v := by
  intro l _ Γ S M f y hM hf hy
  refine coboundary_of_approx ((l : ℕ) : PadicAlgCl l) ?_ Γ S M f y hM hf hy
  have h : ((l : ℕ) : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by
    rw [map_natCast]
  have h0 : ‖algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l])‖ = ‖(l : ℚ_[l])‖ :=
    PadicAlgCl.norm_extends l _
  rw [h, h0]
  exact Padic.norm_p_lt_one

end GlobalTheory.UniformCoboundary
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoboundaryOfPadicAlgClUniformApproxStatement
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coboundary_of_padicAlgCl_uniform_approx : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) (S : Set Γ) (M : Γ → Matrix (Fin 2) (Fin 2) (PadicAlgCl l)) (f : ℕ → Γ → Fin 2 → PadicAlgCl l) (y : Γ → Fin 2 → PadicAlgCl l), (∀ s i j, ‖M s i j‖ ≤ 1) → (∀ r, ∃ v : Fin 2 → PadicAlgCl l, ∀ s ∈ S, f r s = M s *ᵥ v - v) → (∀ r s i, ‖y s i - f r s i‖ ≤ ‖((l : ℕ) : PadicAlgCl l) ^ r‖) → ∃ v : Fin 2 → PadicAlgCl l, ∀ s ∈ S, y s = M s *ᵥ v - v := by
  first | exact @GlobalTheory.UniformCoboundary.coboundary_of_padic_approx | exact GlobalTheory.UniformCoboundary.coboundary_of_padic_approx | (intros; apply GlobalTheory.UniformCoboundary.coboundary_of_padic_approx <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormCompatibleSystemFrobeniusEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormCompatibleSystemFrobeniusEqZero
open scoped Matrix

namespace GlobalTheory.NormSystemVanishing

theorem sum_mem_of_orbit_sums {G H : Type} [CommGroup G] [Fintype G] [DecidableEq G]
    [AddCommGroup H] (P : AddSubgroup H) (u : G) (f : G → H) (S : Finset G)
    (hS : ∀ g ∈ S, g * u ∈ S)
    (hP : ∀ g, ∑ j ∈ Finset.range (orderOf u), f (g * u ^ j) ∈ P) :
    ∑ g ∈ S, f g ∈ P := by
  have hn : 0 < orderOf u := orderOf_pos u
  induction S using Finset.strongInduction with
  | H S ih =>
    rcases S.eq_empty_or_nonempty with rfl | ⟨g, hg⟩
    · simp
    have hpow : ∀ j, g * u ^ j ∈ S := by
      intro j
      induction j with
      | zero => simpa using hg
      | succ j ihj => rw [pow_succ, ← mul_assoc]; exact hS _ ihj
    have hOS : (Finset.range (orderOf u)).image (fun j => g * u ^ j) ⊆ S := by
      intro y hy
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hy
      exact hpow j
    have hgO : g ∈ (Finset.range (orderOf u)).image (fun j => g * u ^ j) :=
      Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hn, by simp⟩
    have hsumO : ∑ y ∈ (Finset.range (orderOf u)).image (fun j => g * u ^ j), f y =
        ∑ j ∈ Finset.range (orderOf u), f (g * u ^ j) := by
      rw [Finset.sum_image]
      intro i hi j hj hij
      exact pow_injOn_Iio_orderOf (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)
        (mul_left_cancel hij)
    rw [← Finset.sum_sdiff hOS, hsumO]
    refine P.add_mem (ih _ (Finset.sdiff_ssubset hOS ⟨g, hgO⟩) ?_) (hP g)
    intro y hy
    rw [Finset.mem_sdiff] at hy ⊢
    refine ⟨hS y hy.1, fun hyu => hy.2 ?_⟩
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hyu
    refine Finset.mem_image.mpr
      ⟨(j + (orderOf u - 1)) % orderOf u, Finset.mem_range.mpr (Nat.mod_lt _ hn), ?_⟩
    show g * u ^ ((j + (orderOf u - 1)) % orderOf u) = y
    rw [pow_mod_orderOf, pow_add, ← mul_assoc, hj, mul_assoc, ← pow_succ',
      Nat.sub_add_cancel hn, pow_orderOf_eq_one, mul_one]

theorem fixed_of_dvd {O H : Type} [CommRing O] [AddCommGroup H] [Module O H]
    (ψ : Module.End O H) (m : H) {p n : ℕ} (hm : (ψ ^ p) m = m) (h : p ∣ n) :
    (ψ ^ n) m = m := by
  obtain ⟨k, rfl⟩ := h
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.mul_succ, pow_add, Module.End.mul_apply, hm, ih]

theorem exists_stable_exponent {O H : Type} [CommRing O] [IsNoetherianRing O] [AddCommGroup H]
    [Module O H] (M : Submodule O H) (hM : M.FG) (ψ : Module.End O H) (l : ℕ) :
    ∃ a₀ : ℕ, ∀ m ∈ M, ∀ a : ℕ, (ψ ^ l ^ a) m = m → (ψ ^ l ^ a₀) m = m := by
  have : IsNoetherian O M := isNoetherian_of_fg_of_noetherian M hM
  have key : ∀ (a : ℕ) (x : M),
      x ∈ LinearMap.ker ((ψ ^ l ^ a - 1).comp M.subtype) ↔ (ψ ^ l ^ a) x = x := by
    intro a x
    simp [sub_eq_zero]
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr ‹IsNoetherian O M›
    ⟨fun a => LinearMap.ker ((ψ ^ l ^ a - 1).comp M.subtype), fun a b hab x hx => by
      rw [key] at hx ⊢
      exact fixed_of_dvd ψ _ hx (pow_dvd_pow l hab)⟩
  refine ⟨n, fun m hm a ha => ?_⟩
  rcases le_total a n with h | h
  · exact fixed_of_dvd ψ m ha (pow_dvd_pow l h)
  · have e : LinearMap.ker ((ψ ^ l ^ n - 1).comp M.subtype) =
        LinearMap.ker ((ψ ^ l ^ a - 1).comp M.subtype) := hn a h
    have h1 : (⟨m, hm⟩ : M) ∈ LinearMap.ker ((ψ ^ l ^ a - 1).comp M.subtype) := (key a _).mpr ha
    rw [← e] at h1
    exact (key n _).mp h1

theorem eq_zero_of_forall_divisible {O H : Type} [CommRing O] [IsNoetherianRing O]
    [IsLocalRing O] [AddCommGroup H] [Module O H] (M : Submodule O H) (hM : M.FG) (t : O)
    (ht : ¬ IsUnit t) (x : H) (hx : ∀ k : ℕ, ∃ m ∈ M, x = t ^ k • m) : x = 0 := by
  have : Module.Finite O M := Module.Finite.iff_fg.mpr hM
  have hx0 : x ∈ M := by
    obtain ⟨m, hm, e⟩ := hx 0
    simpa [e] using hm
  have hI : Ideal.span {t} ≠ ⊤ := by rwa [Ne, Ideal.span_singleton_eq_top]
  have hbot := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := M) _ hI
  have hmem : (⟨x, hx0⟩ : M) ∈ (⨅ i : ℕ, (Ideal.span {t}) ^ i • ⊤ : Submodule O M) := by
    rw [Submodule.mem_iInf]
    intro i
    obtain ⟨m, hm, e⟩ := hx i
    have he : (⟨x, hx0⟩ : M) = t ^ i • (⟨m, hm⟩ : M) := Subtype.ext (by simpa using e)
    rw [he]
    refine Submodule.smul_mem_smul ?_ Submodule.mem_top
    rw [Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton_self _
  rw [hbot, Submodule.mem_bot] at hmem
  simpa using congrArg Subtype.val hmem

private theorem sum_fibre_units_zmod_pow_eq_of_le {H : Type} [AddCommGroup H] (l : ℕ) [Fact l.Prime]
    (c : ∀ r : ℕ, (ZMod (l ^ r))ˣ → H)
    (hc : ∀ r x, c r x = ∑ x' ∈ Finset.univ.filter (fun x' : (ZMod (l ^ (r + 1)))ˣ =>
      Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom x' = x),
        c (r + 1) x') (r : ℕ) (x : (ZMod (l ^ r))ˣ) :
    ∀ (n : ℕ) (hn : r ≤ n), c r x = ∑ x' ∈ Finset.univ.filter (fun x' : (ZMod (l ^ n))ˣ =>
      ZMod.unitsMap (pow_dvd_pow l hn) x' = x), c n x' := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    simp [Finset.filter_eq']
  | succ n hmn ih =>
    have hcomp : ∀ y : (ZMod (l ^ (n + 1)))ˣ,
        ZMod.unitsMap (pow_dvd_pow l (Nat.le_succ_of_le hmn)) y =
          ZMod.unitsMap (pow_dvd_pow l hmn)
            (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ n)) (ZMod (l ^ n))).toMonoidHom y) :=
      fun y => (DFunLike.congr_fun
        (ZMod.unitsMap_comp (pow_dvd_pow l hmn) (pow_dvd_pow l (Nat.le_succ n))) y).symm
    have hmaps : ∀ y ∈ Finset.univ.filter (fun y : (ZMod (l ^ (n + 1)))ˣ =>
        ZMod.unitsMap (pow_dvd_pow l (Nat.le_succ_of_le hmn)) y = x),
        Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ n)) (ZMod (l ^ n))).toMonoidHom y ∈
          Finset.univ.filter (fun x' : (ZMod (l ^ n))ˣ => ZMod.unitsMap (pow_dvd_pow l hmn) x' = x) := by
      intro y hy
      rw [Finset.mem_filter] at hy ⊢
      exact ⟨Finset.mem_univ _, by rw [← hcomp]; exact hy.2⟩
    rw [ih, ← Finset.sum_fiberwise_of_maps_to hmaps (c (n + 1))]
    refine Finset.sum_congr rfl fun x' hx' => ?_
    rw [hc n x', Finset.filter_filter]
    refine Finset.sum_congr (Finset.filter_congr fun y _ => ?_) fun _ _ => rfl
    rw [Finset.mem_filter] at hx'
    constructor
    · intro h
      exact ⟨by rw [hcomp, h]; exact hx'.2, h⟩
    · exact fun h => h.2

theorem sum_tower {H : Type} [AddCommGroup H] (l : ℕ) [Fact l.Prime]
    (c : ∀ r : ℕ, (ZMod (l ^ r))ˣ → H)
    (hc : ∀ r x, c r x = ∑ x' ∈ Finset.univ.filter (fun x' : (ZMod (l ^ (r + 1)))ˣ =>
      Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom x' = x),
        c (r + 1) x') (r k : ℕ) (x : (ZMod (l ^ r))ˣ) :
    c r x = ∑ x' ∈ Finset.univ.filter (fun x' : (ZMod (l ^ (r + k)))ˣ =>
      ZMod.unitsMap (pow_dvd_pow l (Nat.le_add_right r k)) x' = x), c (r + k) x' := sum_fibre_units_zmod_pow_eq_of_le l c hc r x (r + k) (Nat.le_add_right r k)

theorem totient_dvd (l : ℕ) [hl : Fact l.Prime] (n s : ℕ) (h : n ≤ s) :
    Nat.totient (l ^ n) ∣ (l - 1) * l ^ s := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    rw [Nat.totient_prime_pow_succ hl.out, mul_comm (l ^ n)]
    exact mul_dvd_mul_left _ (pow_dvd_pow l (by omega))

theorem unit_pow_eq_one (l : ℕ) [hl : Fact l.Prime] (n s : ℕ) (h : n ≤ s)
    (v : (ZMod (l ^ n))ˣ) : v ^ ((l - 1) * l ^ s) = 1 := by
  obtain ⟨d, hd⟩ := totient_dvd l n s h
  rw [hd, pow_mul, ZMod.pow_totient, one_pow]

theorem unit_pow_ne_one (l : ℕ) [hl : Fact l.Prime] (q : ℕ) (hq : Nat.Coprime q l) (h2 : 2 ≤ q)
    (B n : ℕ) (hB : 0 < B) (hn : q ^ B ≤ n) :
    (ZMod.unitOfCoprime q (Nat.Coprime.pow_right n hq)) ^ B ≠ 1 := by
  intro he
  have hl2 : 2 ≤ l := hl.out.two_le
  have hqB : 2 ≤ q ^ B := le_trans h2 (Nat.le_self_pow hB.ne' q)
  have hlt : q ^ B < l ^ n := lt_of_le_of_lt hn (Nat.lt_pow_self (by omega))
  have h1 := congrArg Units.val he
  rw [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Units.val_one, ← Nat.cast_pow,
    ← Nat.cast_one, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hlt,
    Nat.mod_eq_of_lt (by omega)] at h1
  omega

theorem normCompatible_eq_zero : ∀ (O H : Type) [CommRing O] [IsNoetherianRing O] [IsLocalRing O] [AddCommGroup H] [Module O H] (l : ℕ) [Fact l.Prime], ¬ IsUnit (l : O) → ∀ (q : ℕ) (hq : Nat.Coprime q l), 2 ≤ q → ∀ (M : Submodule O H), M.FG → ∀ (F : H →ₗ[O] H), (∀ x ∈ M, F x ∈ M) → ∀ (c : ∀ r : ℕ, (ZMod (l ^ r))ˣ → H), (∀ r x, c r x ∈ M) → (∀ r x, F (c r x) = c r (x * ZMod.unitOfCoprime q (Nat.Coprime.pow_right r hq))) → (∀ r x, c r x = ∑ x' ∈ Finset.univ.filter (fun x' : (ZMod (l ^ (r + 1)))ˣ => Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom x' = x), c (r + 1) x') → ∀ r x, c r x = 0 := by
  intro O H _ _ _ _ _ l _ hl q hq hq2 M hM F _ c hcM hF hc r x
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hFpow : ∀ (r : ℕ) (y : (ZMod (l ^ r))ˣ) (j : ℕ),
      (F ^ j) (c r y) = c r (y * ZMod.unitOfCoprime q (Nat.Coprime.pow_right r hq) ^ j) := by
    intro r y j
    induction j generalizing y with
    | zero => simp
    | succ j ih => rw [pow_succ, Module.End.mul_apply, hF, ih, mul_assoc, ← pow_succ']
  obtain ⟨a₀, ha₀⟩ := exists_stable_exponent M hM (F ^ (l - 1)) l
  have hfix : ∀ s, a₀ ≤ s → ∀ (r : ℕ) (y : (ZMod (l ^ r))ˣ),
      (F ^ ((l - 1) * l ^ s)) (c r y) = c r y := by
    intro s hs r y
    have h1 : ((F ^ (l - 1)) ^ l ^ r) (c r y) = c r y := by
      rw [← pow_mul, hFpow, unit_pow_eq_one l r r le_rfl, mul_one]
    have h3 := ha₀ _ (hcM r y) r h1
    rw [← pow_mul] at h3
    exact fixed_of_dvd F _ h3 (mul_dvd_mul_left _ (pow_dvd_pow l hs))
  refine eq_zero_of_forall_divisible M hM (l : O) hl (c r x) fun K => ?_
  obtain ⟨s, hs1, hs2⟩ : ∃ s, a₀ ≤ s ∧ r ≤ s := ⟨max a₀ r, le_max_left _ _, le_max_right _ _⟩
  have hBpos : 0 < (l - 1) * l ^ (s + K) := Nat.mul_pos (by omega) (pow_pos (by omega) _)
  obtain ⟨k, hk⟩ : ∃ k, q ^ ((l - 1) * l ^ (s + K)) ≤ r + k := ⟨_, Nat.le_add_left _ _⟩
  obtain ⟨u, hu⟩ : ∃ u : (ZMod (l ^ (r + k)))ˣ,
      u = ZMod.unitOfCoprime q (Nat.Coprime.pow_right (r + k) hq) := ⟨_, rfl⟩
  have hmap : ZMod.unitsMap (pow_dvd_pow l (Nat.le_add_right r k)) u =
      ZMod.unitOfCoprime q (Nat.Coprime.pow_right r hq) := by
    subst hu
    ext
    rw [ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, ZMod.coe_unitOfCoprime,
      ZMod.coe_unitOfCoprime, map_natCast]
  have hw1 : ZMod.unitsMap (pow_dvd_pow l (Nat.le_add_right r k)) (u ^ ((l - 1) * l ^ s)) = 1 := by
    rw [map_pow, hmap, unit_pow_eq_one l r s hs2]
  have hwinv : ∀ (g : (ZMod (l ^ (r + k)))ˣ) (j : ℕ),
      c (r + k) (g * (u ^ ((l - 1) * l ^ s)) ^ j) = c (r + k) g := by
    intro g j
    rw [← pow_mul, hu, ← hFpow]
    exact fixed_of_dvd F _ (hfix s hs1 (r + k) g) (dvd_mul_right _ _)
  have hdvd : orderOf (u ^ ((l - 1) * l ^ s)) ∣ l ^ (r + k) := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← pow_mul, mul_assoc, ← pow_add]
    exact unit_pow_eq_one l (r + k) (s + (r + k)) (by omega) u
  have hne : (u ^ ((l - 1) * l ^ s)) ^ l ^ K ≠ 1 := by
    rw [← pow_mul, mul_assoc, ← pow_add, hu]
    exact unit_pow_ne_one l q hq hq2 _ (r + k) hBpos hk
  have hK : l ^ K ∣ orderOf (u ^ ((l - 1) * l ^ s)) := by
    obtain ⟨e, -, he⟩ := (Nat.dvd_prime_pow (Fact.out : l.Prime)).mp hdvd
    rcases le_or_gt K e with h | h
    · rw [he]; exact pow_dvd_pow l h
    · exact absurd (orderOf_dvd_iff_pow_eq_one.mp (he ▸ pow_dvd_pow l h.le)) hne
  obtain ⟨t, ht⟩ := hK
  have hmem : c r x ∈ (Submodule.map (((l : O) ^ K) • LinearMap.id) M).toAddSubgroup := by
    rw [sum_tower l c hc r k x]
    refine sum_mem_of_orbit_sums _ (u ^ ((l - 1) * l ^ s)) (c (r + k)) _ ?_ ?_
    · intro g hg
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, map_mul, hw1, mul_one] at hg ⊢
      exact hg
    · intro g
      rw [Finset.sum_congr rfl (fun j _ => hwinv g j), Finset.sum_const, Finset.card_range, ht]
      rw [Submodule.mem_toAddSubgroup, Submodule.mem_map]
      refine ⟨(t : O) • c (r + k) g, M.smul_mem _ (hcM _ _), ?_⟩
      rw [LinearMap.smul_apply, LinearMap.id_apply, smul_smul, ← Nat.cast_smul_eq_nsmul O,
        Nat.cast_mul, Nat.cast_pow]
  rw [Submodule.mem_toAddSubgroup, Submodule.mem_map] at hmem
  obtain ⟨m, hm, e⟩ := hmem
  exact ⟨m, hm, by simpa using e.symm⟩

end GlobalTheory.NormSystemVanishing
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormCompatibleSystemFrobeniusEqZeroStatement
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normCompatible_system_frobenius_eq_zero : ∀ (O H : Type) [CommRing O] [IsNoetherianRing O] [IsLocalRing O] [AddCommGroup H] [Module O H] (l : ℕ) [Fact l.Prime], ¬ IsUnit (l : O) → ∀ (q : ℕ) (hq : Nat.Coprime q l), 2 ≤ q → ∀ (M : Submodule O H), M.FG → ∀ (F : H →ₗ[O] H), (∀ x ∈ M, F x ∈ M) → ∀ (c : ∀ r : ℕ, (ZMod (l ^ r))ˣ → H), (∀ r x, c r x ∈ M) → (∀ r x, F (c r x) = c r (x * ZMod.unitOfCoprime q (Nat.Coprime.pow_right r hq))) → (∀ r x, c r x = ∑ x' ∈ Finset.univ.filter (fun x' : (ZMod (l ^ (r + 1)))ˣ => Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom x' = x), c (r + 1) x') → ∀ r x, c r x = 0 := by
  first | exact @GlobalTheory.NormSystemVanishing.normCompatible_eq_zero | exact GlobalTheory.NormSystemVanishing.normCompatible_eq_zero | (intros; apply GlobalTheory.NormSystemVanishing.normCompatible_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ShiftedCocycleLimitIntegral
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix

namespace GlobalTheory.InertCoh

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem norm_le_one_of_isIntegral (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ 1 := by
  have hc : ∀ c : ℤ_[l], ‖algebraMap ℤ_[l] (PadicAlgCl l) c‖ ≤ 1 := by
    intro c
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), norm_algebraMap']
    exact c.2
  by_contra h
  push_neg at h
  obtain ⟨p, hm, hp⟩ := hx
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hm.coeff_natDegree, map_one, one_mul] at hp
  have h1 : x ^ p.natDegree = - ∑ i ∈ Finset.range p.natDegree, algebraMap ℤ_[l] (PadicAlgCl l) (p.coeff i) * x ^ i :=
    eq_neg_of_add_eq_zero_right hp
  rcases Nat.eq_zero_or_pos p.natDegree with hz | hz
  · rw [hz] at h1; simp at h1
  have h2 : ‖∑ i ∈ Finset.range p.natDegree, algebraMap ℤ_[l] (PadicAlgCl l) (p.coeff i) * x ^ i‖ ≤
      ‖x‖ ^ (p.natDegree - 1) := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i hi => ?_
    rw [norm_mul, norm_pow]
    have hi' := Finset.mem_range.1 hi
    calc _ ≤ 1 * ‖x‖ ^ i := mul_le_mul_of_nonneg_right (hc _) (by positivity)
      _ ≤ _ := by rw [one_mul]; exact pow_le_pow_right₀ h.le (by omega)
  rw [← norm_neg, ← h1, norm_pow] at h2
  exact absurd h2 (not_le.2 (pow_lt_pow_right₀ h (by omega)))

theorem norm_le_one_of_mem_O (c : Coef l) {x : Qbar l} (hx : x ∈ c.O) : ‖x‖ ≤ 1 :=
  norm_le_one_of_isIntegral x ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨x, hx⟩ : c.O)).map c.O.val)

theorem mat_mul (W : R2 Ω l) (s t : G ℚ Ω) : mat W (s * t) = mat W s * mat W t := by
  simp [mat, map_mul, Units.val_mul]

def frobOp (W : R2 Ω l) (c : Coef l) (φ : G ℚ Ω) :
    (G ℚ Ω → Fin 2 → Qbar l) →ₗ[c.O] (G ℚ Ω → Fin 2 → Qbar l) where
  toFun z s := mat W φ *ᵥ z (φ⁻¹ * s * φ)
  map_add' a b := by funext s; simp [Matrix.mulVec_add]
  map_smul' k a := by funext s; simp [Matrix.mulVec_smul]

theorem frobOp_apply (W : R2 Ω l) (c : Coef l) (φ : G ℚ Ω) (z : G ℚ Ω → Fin 2 → Qbar l) (s : G ℚ Ω) :
    frobOp W c φ z s = mat W φ *ᵥ z (φ⁻¹ * s * φ) := rfl

theorem conj_mem_Ine' {B : ValuationSubring Ω} {φ s : G ℚ Ω} (hφ : φ ∈ Dec (F := ℚ) B)
    (hs : s ∈ Ine (F := ℚ) B) : φ⁻¹ * s * φ ∈ Ine (F := ℚ) B := by
  have := conj_mem_Ine ((Dec (F := ℚ) B).inv_mem hφ) hs
  rwa [inv_inv] at this

theorem frobOp_cob (W : R2 Ω l) (c : Coef l) (B : ValuationSubring Ω) {φ : G ℚ Ω} (hφ : φ ∈ Dec (F := ℚ) B) :
    cob W c (Ine (F := ℚ) B) ≤ (cob W c (Ine (F := ℚ) B)).comap (frobOp W c φ) := by
  rintro z ⟨v, hv⟩
  refine ⟨mat W φ *ᵥ v, fun s hs => ?_⟩
  rw [frobOp_apply, hv _ (conj_mem_Ine' hφ hs), Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    ← mat_mul, ← mat_mul]
  congr 2
  group

theorem frobOp_coc (W : R2 Ω l) (c : Coef l) (B : ValuationSubring Ω) (hWO : ∀ s i j, mat W s i j ∈ c.O)
    {φ : G ℚ Ω} (hφ : φ ∈ Dec (F := ℚ) B) :
    ∀ z ∈ coc W c (Ine (F := ℚ) B), frobOp W c φ z ∈ coc W c (Ine (F := ℚ) B) := by
  rintro z ⟨h1, h2, h3⟩
  have hconj : Continuous fun s : G ℚ Ω => φ⁻¹ * s * φ := (continuous_const.mul continuous_id).mul continuous_const
  refine ⟨fun i => ?_, fun s i => ?_, fun s hs t ht => ?_⟩
  · simp only [frobOp_apply, Matrix.mulVec, dotProduct]
    exact continuous_finsetSum _ fun j _ => continuous_const.mul ((h1 j).comp hconj)
  · simp only [frobOp_apply, Matrix.mulVec, dotProduct]
    exact Subalgebra.sum_mem _ fun j _ => Subalgebra.mul_mem _ (hWO _ _ _) (h2 _ _)
  · simp only [frobOp_apply]
    have e : φ⁻¹ * (s * t) * φ = (φ⁻¹ * s * φ) * (φ⁻¹ * t * φ) := by group
    rw [e, h3 _ (conj_mem_Ine' hφ hs) _ (conj_mem_Ine' hφ ht), Matrix.mulVec_add, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, ← mat_mul, ← mat_mul]
    congr 3
    group

variable [IsAlgClosure ℚ Ω]

theorem cycMod_eq_one_of_mem_Ine {B : ValuationSubring Ω} {q : Pl} (hB : IsPlaceOver B q)
    (hl : ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal) (r : ℕ) {s : G ℚ Ω} (hs : s ∈ Ine (F := ℚ) B) :
    cycMod ℚ Ω l r s = 1 := by
  have h := cycZ_toZModPow_eq hl hB (q := 1) (fun x hx => by simpa using hs.2 x hx) r
  ext
  simp only [cycMod, MonoidHom.coe_comp, Function.comp_apply, Units.coe_map, Units.val_one]
  rw [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, h]
  simp

theorem coprime_normV {q : Pl} (hl : ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal) : Nat.Coprime (normV q) l := by
  have hp := GlobalTheory.TameConjInv.prime_normV q
  refine (Nat.coprime_primes hp (Fact.out : l.Prime)).2 fun h => hl ?_
  have hnorm : normV q = Ideal.absNorm q.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
  have hmem : ((normV q : ℕ) : 𝓞 ℚ) ∈ q.asIdeal := by
    rw [hnorm]
    exact Ideal.absNorm_mem q.asIdeal
  rwa [h] at hmem

theorem cycMod_frob {B : ValuationSubring Ω} {q : Pl} (hB : IsPlaceOver B q) (hl : ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal)
    {φ : G ℚ Ω} (hφ : IsFrob B (normV q) φ) (r : ℕ) :
    cycMod ℚ Ω l r φ = ZMod.unitOfCoprime (normV q) (Nat.Coprime.pow_right r (coprime_normV hl)) := by
  have h := cycZ_of_isFrob hl hB hφ
  ext
  simp only [cycMod, MonoidHom.coe_comp, Function.comp_apply, Units.coe_map, ZMod.coe_unitOfCoprime]
  rw [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, h]
  simp

end GlobalTheory.InertCoh

namespace GlobalTheory.InertCoh

theorem not_isUnit_natCast_O {l : ℕ} [Fact l.Prime] (c : Coef l) : ¬ IsUnit ((l : ℕ) : c.O) := by
  rintro ⟨u, hu⟩
  have h1 : ((u : c.O) : Qbar l) * ((u⁻¹ : c.Oˣ) : c.O) = 1 := by
    rw [← Subalgebra.coe_mul, Units.mul_inv, Subalgebra.coe_one]
  have h2 : ((u : c.O) : Qbar l) = ((l : ℕ) : Qbar l) := by rw [hu]; simp
  have hl : ‖((l : ℕ) : Qbar l)‖ < 1 := by
    have e : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by rw [map_natCast]
    rw [e, PadicAlgCl.norm_extends l (l : ℚ_[l]), Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  have h3 := norm_le_one_of_mem_O c (((u⁻¹ : c.Oˣ) : c.O)).2
  have h4 := congrArg norm h1
  rw [norm_mul, norm_one, h2] at h4
  have : ‖((l : ℕ) : Qbar l)‖ * ‖(((u⁻¹ : c.Oˣ) : c.O) : Qbar l)‖ < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) h3) hl
  linarith

theorem unr_of_limit_spec : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (W : R2 Ω l) (c : Coef l) (Y : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l) (η : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) (y : G ℚ Ω → Fin 2 → Qbar l), Continuous W → (∀ s i j, mat W s i j ∈ c.O) → (∀ r x i, Continuous fun s => Y r s x i) → (∀ r s x i, Y r s x i ∈ c.O) → (∀ r, ShCoc (mat W) (cycMod ℚ Ω l r)⁻¹ (Y r)) → (∀ r s, Y r s = push (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) (Y (r + 1)) s) → (∀ r x, η r x ∈ c.O) → (∀ r s i, ‖y s i - spec (η r) (Y r) s i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) → ∀ q : Pl, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∃ B : ValuationSubring Ω, IsPlaceOver B q ∧ ∃ v : Fin 2 → Qbar l, ∀ s ∈ Ine (F := ℚ) B, y s = mat W s *ᵥ v - v := by
  intro l _ Ω _ _ _ W c Y η y hW hWO hYc hYO hsh hnorm hη hy q hl
  obtain ⟨B, hB⟩ := exists_isPlaceOver Ω q
  refine ⟨B, hB, ?_⟩
  obtain ⟨φ, hφ⟩ := exists_isFrob hB
  obtain ⟨γ, hγ⟩ := GlobalTheory.TameInertiaGen.exists_tameGenAt ℚ Ω q B hB
  have hq := coprime_normV hl
  let u : ∀ r : ℕ, (ZMod (l ^ r))ˣ := fun r => ZMod.unitOfCoprime (normV q) (Nat.Coprime.pow_right r hq)
  let z : ∀ r : ℕ, (ZMod (l ^ r))ˣ → G ℚ Ω → Fin 2 → Qbar l := fun r x s => Y r s x
  have hzZ : ∀ r x, z r x ∈ coc W c (Ine (F := ℚ) B) := by
    intro r x
    refine ⟨fun i => hYc r x i, fun s i => hYO r s x i, fun s hs t _ => ?_⟩
    have h := hsh r s t x
    simp only [MonoidHom.inv_apply, cycMod_eq_one_of_mem_Ine hB hl r hs, inv_one, mul_one] at h
    exact h
  have hFB := frobOp_cob W c B hφ.1
  let FH := (cob W c (Ine (F := ℚ) B)).mapQ (cob W c (Ine (F := ℚ) B)) (frobOp W c φ) hFB
  have hFM : ∀ x ∈ (coc W c (Ine (F := ℚ) B)).map (cob W c (Ine (F := ℚ) B)).mkQ,
      FH x ∈ (coc W c (Ine (F := ℚ) B)).map (cob W c (Ine (F := ℚ) B)).mkQ := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨frobOp W c φ w, frobOp_coc W c B hWO hφ.1 w hw, rfl⟩
  have hfrob : ∀ r x, FH ((cob W c (Ine (F := ℚ) B)).mkQ (z r x)) =
      (cob W c (Ine (F := ℚ) B)).mkQ (z r (x * u r)) := by
    intro r x
    show Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    rw [← sub_eq_zero, ← Submodule.Quotient.mk_sub, Submodule.Quotient.mk_eq_zero]
    refine ⟨Y r φ (x * u r), fun s hs => ?_⟩
    have h1 := hsh r φ (φ⁻¹ * s * φ) (x * u r)
    have h2 := hsh r s φ (x * u r)
    rw [MonoidHom.inv_apply, cycMod_frob hB hl hφ r] at h1
    rw [MonoidHom.inv_apply, cycMod_eq_one_of_mem_Ine hB hl r hs, inv_one, mul_one] at h2
    have e : φ * (φ⁻¹ * s * φ) = s * φ := by group
    rw [e, h2, mul_inv_cancel_right] at h1
    show mat W φ *ᵥ Y r (φ⁻¹ * s * φ) x - Y r s (x * u r) = mat W s *ᵥ Y r φ (x * u r) - Y r φ (x * u r)
    calc mat W φ *ᵥ Y r (φ⁻¹ * s * φ) x - Y r s (x * u r)
        = (Y r φ (x * u r) + mat W φ *ᵥ Y r (φ⁻¹ * s * φ) x) - Y r φ (x * u r) - Y r s (x * u r) := by abel
      _ = (Y r s (x * u r) + mat W s *ᵥ Y r φ (x * u r)) - Y r φ (x * u r) - Y r s (x * u r) := by rw [h1]
      _ = _ := by abel
  have hN : ∀ r x, (cob W c (Ine (F := ℚ) B)).mkQ (z r x) = ∑ x' ∈ Finset.univ.filter (fun x' : (ZMod (l ^ (r + 1)))ˣ =>
      Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom x' = x),
      (cob W c (Ine (F := ℚ) B)).mkQ (z (r + 1) x') := by
    intro r x
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum]
    congr 1
    funext s
    rw [Finset.sum_apply]
    show Y r s x = _
    rw [hnorm r s]
    rfl
  have hFG : ((coc W c (Ine (F := ℚ) B)).map (cob W c (Ine (F := ℚ) B)).mkQ).FG :=
    GlobalTheory.T.fg_inertiaCocycles_mod_coboundaries_coefRing l Ω W c (Ine (F := ℚ) B) {σ | ∀ y : Ω, y ≠ 0 → B.valuation (σ y / y - 1) < 1} γ hW hWO
      (fun w hw => GlobalTheory.T.exists_integral_coboundary_wildInertia_away_from_l l Ω W c B q hW hWO hB hl w hw)
      (fun w hw hP h0 => GlobalTheory.T.inertiaCocycle_eq_zero_of_vanish_wild_tameGenerator l Ω W B γ hγ w hw.1 hw.2.2 (fun σ hσ => hP σ hσ) h0)
  have hlO : ¬ IsUnit ((l : ℕ) : c.O) := not_isUnit_natCast_O c
  haveI : IsLocalRing c.O := IsDiscreteValuationRing.toIsLocalRing
  haveI : IsNoetherianRing c.O := inferInstance
  have hzero := GlobalTheory.T.normCompatible_system_frobenius_eq_zero c.O _ l hlO (normV q) hq (GlobalTheory.TameConjInv.prime_normV q).two_le
    ((coc W c (Ine (F := ℚ) B)).map (cob W c (Ine (F := ℚ) B)).mkQ) hFG FH hFM
    (fun r x => (cob W c (Ine (F := ℚ) B)).mkQ (z r x)) (fun r x => Submodule.mem_map_of_mem (hzZ r x)) hfrob hN
  have hspec : ∀ r, spec (η r) (Y r) ∈ cob W c (Ine (F := ℚ) B) := by
    intro r
    have e : spec (η r) (Y r) = ∑ x, (⟨η r x, hη r x⟩ : c.O) • z r x := by
      funext s
      simp only [spec, Finset.sum_apply, Pi.smul_apply, Subalgebra.smul_def]
      rfl
    rw [e]
    refine Submodule.sum_mem _ fun x _ => Submodule.smul_mem _ _ ?_
    have h := hzero r x
    rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h
  exact GlobalTheory.T.coboundary_of_padicAlgCl_uniform_approx l (G ℚ Ω) (Ine (F := ℚ) B : Set (G ℚ Ω)) (mat W) (fun r => spec (η r) (Y r)) y
    (fun s i j => norm_le_one_of_mem_O c (hWO s i j)) (fun r => hspec r) hy

end GlobalTheory.InertCoh

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ShiftedCocycleLimitIntegralStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shifted_cocycle_limit_integral : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (W : R2 Ω l) (c : Coef l) (Y : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l) (η : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) (y : G ℚ Ω → Fin 2 → Qbar l), Continuous W → (∀ s i j, mat W s i j ∈ c.O) → (∀ r x i, Continuous fun s => Y r s x i) → (∀ r s x i, Y r s x i ∈ c.O) → (∀ r, ShCoc (mat W) (cycMod ℚ Ω l r)⁻¹ (Y r)) → (∀ r s, Y r s = push (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) (Y (r + 1)) s) → (∀ r x, η r x ∈ c.O) → (∀ r s i, ‖y s i - spec (η r) (Y r) s i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) → ∀ q : Pl, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∃ B : ValuationSubring Ω, IsPlaceOver B q ∧ ∃ v : Fin 2 → Qbar l, ∀ s ∈ Ine (F := ℚ) B, y s = mat W s *ᵥ v - v := by
  first | exact @GlobalTheory.InertCoh.unr_of_limit_spec | exact GlobalTheory.InertCoh.unr_of_limit_spec | (intros; apply GlobalTheory.InertCoh.unr_of_limit_spec ; all_goals assumption)
end
