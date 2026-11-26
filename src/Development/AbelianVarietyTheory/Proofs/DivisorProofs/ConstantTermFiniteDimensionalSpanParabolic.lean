module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraCapelliUniformDiagonalBlocks
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapelliKilledSmoothFunctionCentreOrbitFiniteDime

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RightTranslateHarishChandraFiniteFormProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RightTranslateHarishChandraFiniteFormProperties
open NumberField MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.HCF

theorem fold_replicate_cap {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
    (c : Module.End ℂ (Sm E a)) (χ : Module.End ℂ (Sm E a) → ℂ) (φ : Sm E a) (n : ℕ) :
    (List.replicate n c).foldr (fun z f => z f - χ z • f) φ = ((c - algebraMap ℂ _ (χ c)) ^ n) φ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, List.foldr_cons, ih, pow_succ', Module.End.mul_apply, LinearMap.sub_apply,
      Module.algebraMap_end_apply]

theorem rt_translate_kill : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))) (W : Submodule ℂ (Kinf E a → ℂ)) (X : Set (Module.End ℂ (Sm E a) → ℂ)) (S : Finset (Module.End ℂ (Sm E a) → ℂ)), X ⊆ ↑S → ∀ (N : ℕ), ∀ φ ∈ GlobalTheory.HCF.formsGL E a L W X N, ∀ (t : GL (Fin a) (Af E)) (κ : Kinf E a), (∀ γ g, (rt E a (finGL E a t * infGL E a (Unitary.toUnits κ)) φ).1 (ratGL E a γ * g) = (rt E a (finGL E a t * infGL E a (Unitary.toUnits κ)) φ).1 g) ∧ IsOpen {k | finRep E a k (rt E a (finGL E a t * infGL E a (Unitary.toUnits κ)) φ) = rt E a (finGL E a t * infGL E a (Unitary.toUnits κ)) φ} ∧ ∀ (τ : E →+* ℂ) (u : ℂ), Polynomial.aeval (cap τ u) (∏ χ ∈ S, (Polynomial.X - Polynomial.C (χ (cap τ u))) ^ N) (rt E a (finGL E a t * infGL E a (Unitary.toUnits κ)) φ) = 0 := by
  intro E _ _ _ a L W X S hXS N φ hφ t κ
  obtain ⟨hA, -, -, χ₀, hχ₀, hnil⟩ := hφ
  set h := finGL E a t * infGL E a (Unitary.toUnits κ) with hh
  refine ⟨fun γ g => ?_, ?_, fun τ u => ?_⟩
  · rw [rt_apply, rt_apply, mul_assoc, hA.left]
  · refine isOpen_stab_of_mem_nhds (finRep E a) _ ?_
    have hc : Continuous fun k : GL (Fin a) (Af E) => t⁻¹ * k * t := by fun_prop
    have ho := hA.level.preimage hc
    refine Filter.mem_of_superset (ho.mem_nhds (by simp)) fun k hk => ?_
    have hk' : rt E a (finGL E a (t⁻¹ * k * t)) φ = φ := hk
    change rt E a (finGL E a k) (rt E a h φ) = rt E a h φ
    have e : finGL E a k * h = h * finGL E a (t⁻¹ * k * t) := by
      rw [hh, mul_assoc (finGL E a t), infGL_comm, ← mul_assoc (finGL E a t), ← map_mul,
        show t * (t⁻¹ * k * t) = k * t by group, map_mul]
      simp only [mul_assoc]
    rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, hk']
  · classical
    have hcap : cap τ u ∈ Zalg E a := Algebra.subset_adjoin ⟨τ, u, rfl⟩
    have hc : Commute (cap (a := a) τ u) (rt E a h) := by
      have h1 : Commute (cap τ u) (rt E a (finGL E a t)) := commute_cap_finRep (a := a) τ u t
      have h2 := GlobalTheory.CapAdInv.cap_commute_rt_infGL E a τ u (Unitary.toUnits κ)
      rw [hh, map_mul]
      exact h1.mul_right h2
    have hP : ∀ p : Polynomial ℂ, Commute (Polynomial.aeval (cap (a := a) τ u) p) (rt E a h) := by
      intro p
      have hle : Algebra.adjoin ℂ {cap (a := a) τ u} ≤ Subalgebra.centralizer ℂ {rt E a h} := by
        refine Algebra.adjoin_le ?_
        rintro _ rfl
        rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
        rintro g rfl
        exact hc.eq.symm
      exact ((Subalgebra.mem_centralizer_iff ℂ).1 (hle (Polynomial.aeval_mem_adjoin_singleton ℂ _)) _ rfl).symm
    rw [← Module.End.mul_apply, (hP _).eq, Module.End.mul_apply]
    have h0 : Polynomial.aeval (cap (a := a) τ u) ((Polynomial.X - Polynomial.C (χ₀ (cap τ u))) ^ N) φ = 0 := by
      have := hnil (List.replicate N (cap τ u)) (List.length_replicate ..) fun z hz => by
        rw [List.eq_of_mem_replicate hz]; exact hcap
      rw [fold_replicate_cap] at this
      simpa [map_pow, map_sub, Polynomial.aeval_X, Polynomial.aeval_C] using this
    rw [← Finset.prod_erase_mul S _ (hXS hχ₀), Polynomial.aeval_mul, Module.End.mul_apply, h0]
    simp only [map_zero]

end GlobalTheory.HCF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RightTranslateHarishChandraFiniteFormPropertiesStatement
open NumberField MeasureTheory GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rightTranslate_harishChandraFiniteForm_properties : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))) (W : Submodule ℂ (Kinf E a → ℂ)) (X : Set (Module.End ℂ (Sm E a) → ℂ)) (S : Finset (Module.End ℂ (Sm E a) → ℂ)), X ⊆ ↑S → ∀ (N : ℕ), ∀ φ ∈ GlobalTheory.HCF.formsGL E a L W X N, ∀ (t : GL (Fin a) (Af E)) (κ : Kinf E a), (∀ γ g, (rt E a (finGL E a t * infGL E a (Unitary.toUnits κ)) φ).1 (ratGL E a γ * g) = (rt E a (finGL E a t * infGL E a (Unitary.toUnits κ)) φ).1 g) ∧ IsOpen {k | finRep E a k (rt E a (finGL E a t * infGL E a (Unitary.toUnits κ)) φ) = rt E a (finGL E a t * infGL E a (Unitary.toUnits κ)) φ} ∧ ∀ (τ : E →+* ℂ) (u : ℂ), Polynomial.aeval (cap τ u) (∏ χ ∈ S, (Polynomial.X - Polynomial.C (χ (cap τ u))) ^ N) (rt E a (finGL E a t * infGL E a (Unitary.toUnits κ)) φ) = 0 := by
  first | exact @GlobalTheory.HCF.rt_translate_kill | exact GlobalTheory.HCF.rt_translate_kill | (intros; apply GlobalTheory.HCF.rt_translate_kill <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixUnitOpUpperBlockLeviEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixUnitOpUpperBlockLeviEqZero
open NumberField MeasureTheory GlobalTheory.CuspRep

noncomputable section

namespace GlobalTheory.LeviGA

open Matrix

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a r : ℕ}

theorem mul_mul_upper {R : Type} [CommRing R] (A N B : Matrix (Fin a) (Fin a) R)
    (hA : ∀ k p : Fin a, ((k : ℕ) < r ↔ (p : ℕ) < r) ∨ A k p = 0)
    (hB : ∀ q l : Fin a, ((q : ℕ) < r ↔ (l : ℕ) < r) ∨ B q l = 0)
    (hN : ∀ p q : Fin a, ¬((p : ℕ) < r ∧ r ≤ (q : ℕ)) → N p q = 0)
    (k l : Fin a) (hkl : ¬((k : ℕ) < r ∧ r ≤ (l : ℕ))) : (A * N * B) k l = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun q _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_eq_zero fun p _ => ?_
  by_cases hpq : (p : ℕ) < r ∧ r ≤ (q : ℕ)
  · rcases hA k p with h1 | h1
    · rcases hB q l with h2 | h2
      · exact absurd ⟨h1.2 hpq.1, by by_contra h; exact absurd (h2.2 (by omega)) (by omega)⟩ hkl
      · rw [h2, mul_zero]
    · rw [h1, zero_mul, zero_mul]
  · rw [hN p q hpq, mul_zero, zero_mul]

theorem lieD_single_blkGL (hr : r ≤ a) (f : Sm E a)
    (hf : ∀ (x : BlockIx a r → Ad E) (g : GA E a), f.1 (unip x * g) = f.1 g)
    (i j : Fin a) (hi : (i : ℕ) < r) (hj : r ≤ (j : ℕ)) (p : GA E r × GA E (a - r)) (x : Cinf E) :
    lieD (toL (Matrix.single i j x)) f.1 (blkGL hr p) = 0 := by
  set m : GA E a := blkGL hr p with hm
  set S : Matrix (Fin a) (Fin a) (Cinf E) := Matrix.single i j x with hS
  have hij : j ≠ i := fun h => by rw [h] at hj; omega
  have hSS : S * S = 0 := by rw [hS]; simp [hij, hij.symm]
  let c : ℝ → GL (Fin a) (Cinf E) := fun t =>
    ⟨1 + t • S, 1 - t • S, by simp [mul_sub, add_mul, smul_mul_smul_comm, hSS],
      by simp [sub_mul, mul_add, smul_mul_smul_comm, hSS]⟩
  have h0 : c 0 = 1 := Units.ext (by simp [c])
  have hc : HasDerivAt (fun t => toL (c t).val) (toL S) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const (toL S)).const_add (toL (1 : Matrix (Fin a) (Fin a) (Cinf E)))
    rw [one_smul] at this
    exact this
  have hd := hasDerivAt_curve f m c (toL S) h0 hc

  have hconst : ∀ t, f.1 (m * infGL E a (c t)) = f.1 m := by
    intro t
    set N : Matrix (Fin a) (Fin a) (Ad E) := matN a (sInf E) (t • S) with hN
    have hinf : (infGL E a (c t)).val = 1 + N := by
      change 1 - matN a (sInf E) 1 + matN a (sInf E) (1 + t • S) = 1 + N
      rw [map_add (f := _)]; abel
    have hNsupp : ∀ p q : Fin a, ¬((p : ℕ) < r ∧ r ≤ (q : ℕ)) → N p q = 0 := by
      intro p q hpq
      have : (t • S) p q = 0 := by
        rw [hS, Matrix.smul_apply]
        by_cases e : p = i ∧ q = j
        · exact absurd (by rw [e.1, e.2]; exact ⟨hi, hj⟩) hpq
        · rw [Matrix.single_apply_of_ne (h := by tauto), smul_zero]
      change sInf E ((t • S) p q) = 0
      rw [this, map_zero]
    have hinv : m⁻¹ = blkGL hr p⁻¹ := by rw [hm, map_inv]
    let y : BlockIx a r → Ad E := fun q => (m.val * N * (m⁻¹).val) q.1.1 q.1.2
    have hy : nilM y = m.val * N * (m⁻¹).val := by
      ext k l
      simp only [nilM, Matrix.of_apply, y]
      split_ifs with h
      · rfl
      · exact (mul_mul_upper _ _ _ (blkGL_block hr p) (by rw [hinv]; exact blkGL_block hr _) hNsupp k l h).symm
    have e : m * infGL E a (c t) = unip y * m := by
      apply Units.ext
      change m.val * (infGL E a (c t)).val = (1 + nilM y) * m.val
      rw [hinf, hy, add_mul, one_mul, mul_add, mul_one, mul_assoc _ _ m.val,
        Units.inv_mul, mul_one]
    rw [e, hf]
  have hfun : (fun t => f.1 (m * infGL E a (c t))) = fun _ => f.1 m := funext hconst
  rw [hfun] at hd
  exact hd.unique (hasDerivAt_const 0 _)

theorem Eop_upper_blkGL_eq_zero :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ) (hr : r ≤ a) (f : Sm E a),
      (∀ (x : BlockIx a r → Ad E) (g : GA E a), f.1 (unip x * g) = f.1 g) → ∀ (τ : E →+* ℂ) (i j : Fin a),
        (i : ℕ) < r → r ≤ (j : ℕ) → ∀ (m₁ : GA E r) (m₂ : GA E (a - r)),
          (Eop τ i j f).1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂)) = 0 := by
  intro E _ _ _ a r hr f hf τ i j hi hj m₁ m₂
  have key : ∀ x : Cinf E, (lieS E a i j x f).1 (blkGL hr (m₁, m₂)) = 0 := fun x =>
    lieD_single_blkGL hr f hf i j hi hj (m₁, m₂) x
  simp only [Eop, LinearMap.smul_apply, LinearMap.sub_apply, Submodule.coe_smul, Submodule.coe_sub, Pi.smul_apply,
    Pi.sub_apply, key, smul_zero, sub_zero]

end GlobalTheory.LeviGA
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixUnitOpUpperBlockLeviEqZeroStatement
open NumberField MeasureTheory GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrixUnitOp_upperBlock_levi_eq_zero : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ) (hr : r ≤ a) (f : Sm E a), (∀ (x : BlockIx a r → Ad E) (g : GA E a), f.1 (unip x * g) = f.1 g) → ∀ (τ : E →+* ℂ) (i j : Fin a), (i : ℕ) < r → r ≤ (j : ℕ) → ∀ (m₁ : GA E r) (m₂ : GA E (a - r)), (Eop τ i j f).1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂)) = 0 := by
  first | exact @GlobalTheory.LeviGA.Eop_upper_blkGL_eq_zero | exact GlobalTheory.LeviGA.Eop_upper_blkGL_eq_zero | (intros; apply GlobalTheory.LeviGA.Eop_upper_blkGL_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviRestrictionVanishingPreservedByOperator
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviRestrictionVanishingPreservedByOperator
open NumberField MeasureTheory GlobalTheory.CuspRep

noncomputable section

namespace GlobalTheory.LeviDeriv

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a r : ℕ}

theorem block_mul {R : Type} [CommRing R] {M N : Matrix (Fin a) (Fin a) R}
    (hM : ∀ i j : Fin a, ((i : ℕ) < r ↔ (j : ℕ) < r) ∨ M i j = 0)
    (hN : ∀ i j : Fin a, ((i : ℕ) < r ↔ (j : ℕ) < r) ∨ N i j = 0) :
    ∀ i j : Fin a, ((i : ℕ) < r ↔ (j : ℕ) < r) ∨ (M * N) i j = 0 := by
  intro i j
  by_cases h : ((i : ℕ) < r ↔ (j : ℕ) < r)
  · exact Or.inl h
  · right
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases hM i k with h1 | h1
    · rcases hN k j with h2 | h2
      · exact absurd (h1.trans h2) h
      · rw [h2, mul_zero]
    · rw [h1, zero_mul]

theorem block_infGL (y : GL (Fin a) (Cinf E))
    (hy : ∀ i j : Fin a, ((i : ℕ) < r ↔ (j : ℕ) < r) ∨ (y : Matrix (Fin a) (Fin a) (Cinf E)) i j = 0) :
    ∀ i j : Fin a, ((i : ℕ) < r ↔ (j : ℕ) < r) ∨ (infGL E a y : Matrix (Fin a) (Fin a) (Ad E)) i j = 0 := by
  intro i j
  by_cases h' : ((i : ℕ) < r ↔ (j : ℕ) < r)
  · exact Or.inl h'
  · right
    have h := (hy i j).resolve_left h'
    have hij : i ≠ j := fun e => h' (by rw [e])
    change (1 : Matrix (Fin a) (Fin a) (Ad E)) i j - sInf E ((1 : Matrix (Fin a) (Fin a) (Cinf E)) i j) +
      sInf E ((y : Matrix (Fin a) (Fin a) (Cinf E)) i j) = 0
    rw [h, Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, map_zero, sub_zero, zero_add]

theorem lieD_single_blkGL (hr : r ≤ a) (f : Sm E a)
    (hf : ∀ (m₁ : GA E r) (m₂ : GA E (a - r)), f.1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂)) = 0)
    (i j : Fin a) (hij : (i : ℕ) < r ↔ (j : ℕ) < r) (x : Cinf E) (m₁ : GA E r) (m₂ : GA E (a - r)) :
    lieD (toL (Matrix.single i j x)) f.1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂)) = 0 := by
  set m := GlobalTheory.LeviGA.blkGL hr (m₁, m₂)
  set X : Lie E a := toL (Matrix.single i j x)
  have hz : ∀ t : ℝ, chart f.1 m (oneL E a + t • X) = 0 := by
    intro t
    unfold chart
    split_ifs with hu
    · have hyb : ∀ k l : Fin a, ((k : ℕ) < r ↔ (l : ℕ) < r) ∨
          ((hu.unit : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E)) k l = 0 := by
        intro k l
        rw [hu.unit_spec]
        by_cases hkl : ((k : ℕ) < r ↔ (l : ℕ) < r)
        · exact Or.inl hkl
        · right
          have hne : k ≠ l := fun e => hkl (by rw [e])
          have hs : Matrix.single i j x k l = 0 := by
            rw [Matrix.single_apply]
            rw [if_neg]
            rintro ⟨e1, e2⟩
            exact hkl (by rw [← e1, ← e2]; exact hij)
          change (1 : Matrix (Fin a) (Fin a) (Cinf E)) k l + t • Matrix.single i j x k l = 0
          rw [hs, Matrix.one_apply_ne hne, smul_zero, add_zero]
      obtain ⟨p, hp⟩ := GlobalTheory.LeviGA.exists_blkGL hr (m * infGL E a hu.unit)
        (by rw [Units.val_mul]; exact block_mul (GlobalTheory.LeviGA.blkGL_block hr _) (block_infGL _ hyb))
      rw [← hp]
      exact hf p.1 p.2
    · rfl
  have hline : HasDerivAt (fun t : ℝ => oneL E a + t • X) X 0 := by
    have := ((hasDerivAt_id' (0 : ℝ)).smul_const X).const_add (oneL E a)
    rwa [one_smul] at this
  have hd : HasFDerivAt (chart f.1 m) (fderiv ℝ (chart f.1 m) (oneL E a)) (oneL E a + (0 : ℝ) • X) := by
    rw [zero_smul, add_zero]
    exact (differentiableAt_chart f.2 m).hasFDerivAt
  have h1 := hd.comp_hasDerivAt (0 : ℝ) hline
  have h2 : HasDerivAt (chart f.1 m ∘ fun t : ℝ => oneL E a + t • X) 0 0 := by
    have e : (chart f.1 m ∘ fun t : ℝ => oneL E a + t • X) = fun _ => 0 := funext hz
    rw [e]
    exact hasDerivAt_const _ _
  exact h1.unique h2

theorem Eop_blkGL_eq_zero : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ) (hr : r ≤ a)
    (f : Sm E a), (∀ (m₁ : GA E r) (m₂ : GA E (a - r)), f.1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂)) = 0) →
    ∀ (τ : E →+* ℂ) (i j : Fin a), ((i : ℕ) < r ↔ (j : ℕ) < r) → ∀ (m₁ : GA E r) (m₂ : GA E (a - r)),
      (Eop τ i j f).1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂)) = 0 := by
  intro E _ _ _ a r hr f hf τ i j hij m₁ m₂
  have k := fun x => lieD_single_blkGL hr f hf i j hij x m₁ m₂
  change (1 / 2 : ℂ) * ((lieS E a i j (atEmb τ 1) f).1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂)) -
    Complex.I * (lieS E a i j (atEmb τ Complex.I) f).1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂))) = 0
  rw [lieS_apply, lieS_apply, lie_apply, lie_apply, k, k]
  simp

end GlobalTheory.LeviDeriv

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviRestrictionVanishingPreservedByOperatorStatement
open NumberField MeasureTheory GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_restriction_vanishing_preserved_by_operator : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ) (hr : r ≤ a) (f : Sm E a), (∀ (m₁ : GA E r) (m₂ : GA E (a - r)), f.1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂)) = 0) → ∀ (τ : E →+* ℂ) (i j : Fin a), ((i : ℕ) < r ↔ (j : ℕ) < r) → ∀ (m₁ : GA E r) (m₂ : GA E (a - r)), (Eop τ i j f).1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂)) = 0 := by
  first | exact @GlobalTheory.LeviDeriv.Eop_blkGL_eq_zero | exact GlobalTheory.LeviDeriv.Eop_blkGL_eq_zero | (intros; apply GlobalTheory.LeviDeriv.Eop_blkGL_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviSliceSmoothAndMatrixUnitAction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviSliceSmoothAndMatrixUnitAction
noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep Matrix Topology
open scoped ContDiff

namespace GlobalTheory.LeviSliceGA

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a r : ℕ}

def lowL (hr : r ≤ a) : Lie E (a - r) →L[ℝ] Lie E a :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => toL (Matrix.reindex (GlobalTheory.LeviGA.blkEquiv hr) (GlobalTheory.LeviGA.blkEquiv hr)
        (Matrix.fromBlocks 0 0 0 (Matrix.of y)))
      map_add' := fun y z => by
        funext i j
        obtain ⟨i, rfl⟩ := (GlobalTheory.LeviGA.blkEquiv hr).surjective i
        obtain ⟨j, rfl⟩ := (GlobalTheory.LeviGA.blkEquiv hr).surjective j
        rcases i with i | i <;> rcases j with j | j <;> simp [toL, Matrix.reindex_apply]
      map_smul' := fun c y => by
        funext i j
        obtain ⟨i, rfl⟩ := (GlobalTheory.LeviGA.blkEquiv hr).surjective i
        obtain ⟨j, rfl⟩ := (GlobalTheory.LeviGA.blkEquiv hr).surjective j
        rcases i with i | i <;> rcases j with j | j <;> simp [toL, Matrix.reindex_apply] }

theorem lowL_apply (hr : r ≤ a) (y : Lie E (a - r)) : lowL hr y = toL (Matrix.reindex (GlobalTheory.LeviGA.blkEquiv hr)
    (GlobalTheory.LeviGA.blkEquiv hr) (Matrix.fromBlocks 0 0 0 (Matrix.of y))) := rfl

def affA (hr : r ≤ a) (y : Lie E (a - r)) : Lie E a :=
  lowL hr y + toL (Matrix.reindex (GlobalTheory.LeviGA.blkEquiv hr) (GlobalTheory.LeviGA.blkEquiv hr) (Matrix.fromBlocks 1 0 0 0))

theorem affA_val (hr : r ≤ a) (u : GL (Fin (a - r)) (Cinf E)) :
    affA hr (toL u.val) = toL (GlobalTheory.LeviGA.blkGL hr (1, u)).val := by
  rw [affA, lowL_apply, GlobalTheory.LeviGA.blkGL_val]
  funext i j
  obtain ⟨i, rfl⟩ := (GlobalTheory.LeviGA.blkEquiv hr).surjective i
  obtain ⟨j, rfl⟩ := (GlobalTheory.LeviGA.blkEquiv hr).surjective j
  rcases i with i | i <;> rcases j with j | j <;> simp [toL, Matrix.reindex_apply]

theorem infGL_apply {n : ℕ} (g : GL (Fin n) (Cinf E)) (i j : Fin n) :
    (infGL E n g : Matrix (Fin n) (Fin n) (Ad E)) i j = (1 : Matrix (Fin n) (Fin n) (Ad E)) i j -
      sInf E ((1 : Matrix (Fin n) (Fin n) (Cinf E)) i j) + sInf E ((g : Matrix (Fin n) (Fin n) (Cinf E)) i j) := rfl

theorem blkGL_infGL (hr : r ≤ a) (u : GL (Fin (a - r)) (Cinf E)) :
    GlobalTheory.LeviGA.blkGL hr ((1 : GA E r), infGL E (a - r) u) = infGL E a (GlobalTheory.LeviGA.blkGL hr (1, u)) := by
  apply Units.ext
  ext i j
  obtain ⟨i, rfl⟩ := (GlobalTheory.LeviGA.blkEquiv hr).surjective i
  obtain ⟨j, rfl⟩ := (GlobalTheory.LeviGA.blkEquiv hr).surjective j
  rw [GlobalTheory.LeviGA.blkGL_apply, infGL_apply, GlobalTheory.LeviGA.blkGL_apply]
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.one_apply, (GlobalTheory.LeviGA.blkEquiv hr).injective.eq_iff, infGL_apply]

theorem chart_slice (hr : r ≤ a) (m₁ : GA E r) (φ : GA E a → ℂ) (m₂ : GA E (a - r)) {y : Lie E (a - r)}
    (hy : y ∈ invSet E (a - r)) :
    chart (fun m : GA E (a - r) => φ (GlobalTheory.LeviGA.blkGL hr (m₁, m))) m₂ y =
      chart φ (GlobalTheory.LeviGA.blkGL hr (m₁, m₂)) (affA hr y) := by
  obtain ⟨u, hu⟩ := hy
  have e : y = toL u.val := hu.symm
  subst e
  rw [chart_val, affA_val, chart_val, ← blkGL_infGL, ← map_mul, Prod.mk_mul_mk, mul_one]

theorem affA_one (hr : r ≤ a) : affA hr (oneL E (a - r)) = oneL E a := by
  have h := affA_val (E := E) hr 1
  rw [show ((1 : GL (Fin r) (Cinf E)), (1 : GL (Fin (a - r)) (Cinf E))) = 1 from rfl, map_one] at h
  exact h

theorem hasFDerivAt_affA (hr : r ≤ a) (y : Lie E (a - r)) : HasFDerivAt (affA hr) (lowL (E := E) hr) y :=
  (lowL hr).hasFDerivAt.add_const _

theorem lowL_single (hr : r ≤ a) (p p' : Fin (a - r)) (x : Cinf E) :
    lowL hr (toL (Matrix.single p p' x)) =
      toL (Matrix.single (GlobalTheory.LeviGA.blkEquiv hr (Sum.inr p)) (GlobalTheory.LeviGA.blkEquiv hr (Sum.inr p')) x) := by
  rw [lowL_apply]
  funext i j
  obtain ⟨i, rfl⟩ := (GlobalTheory.LeviGA.blkEquiv hr).surjective i
  obtain ⟨j, rfl⟩ := (GlobalTheory.LeviGA.blkEquiv hr).surjective j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [toL, Matrix.reindex_apply, Matrix.single_apply, (GlobalTheory.LeviGA.blkEquiv hr).injective.eq_iff] <;>
    by_cases hi : i = p <;> by_cases hj : j = p' <;> simp [hi, hj, Pi.single_apply] <;> intros <;> simp_all

theorem slice_mem_Sm (hr : r ≤ a) (m₁ : GA E r) (f : Sm E a) :
    (fun m₂ : GA E (a - r) => f.1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂))) ∈ Sm E (a - r) := fun m₂ =>
  ((f.2 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂))).comp ((lowL (E := E) hr).contDiff.add contDiff_const).contDiffOn
    (fun y hy => by
      obtain ⟨u, hu⟩ := hy
      have e : y = toL u.val := hu.symm
      subst e
      show affA hr _ ∈ _
      rw [affA_val]
      exact val_mem_invSet _)).congr fun y hy => chart_slice hr m₁ f.1 m₂ hy

theorem lieS_slice (hr : r ≤ a) (m₁ : GA E r) (f : Sm E a) (p p' : Fin (a - r)) (ψ : Sm E (a - r))
    (hψ : ψ.1 = fun m₂ : GA E (a - r) => f.1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂))) (x : Cinf E) (m₂ : GA E (a - r)) :
    (lieS E (a - r) p p' x ψ).1 m₂ =
      (lieS E a (GlobalTheory.LeviGA.blkEquiv hr (Sum.inr p)) (GlobalTheory.LeviGA.blkEquiv hr (Sum.inr p')) x f).1
        (GlobalTheory.LeviGA.blkGL hr (m₁, m₂)) := by
  rw [GlobalTheory.CuspRep.lieS_apply, GlobalTheory.CuspRep.lieS_apply, GlobalTheory.CuspRep.lie_apply, GlobalTheory.CuspRep.lie_apply, lieD, lieD, hψ]
  have ev : chart (fun m : GA E (a - r) => f.1 (GlobalTheory.LeviGA.blkGL hr (m₁, m))) m₂ =ᶠ[𝓝 (oneL E (a - r))]
      chart f.1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂)) ∘ affA hr :=
    Filter.eventually_of_mem (isOpen_invSet.mem_nhds isUnit_one) fun y hy => chart_slice hr m₁ f.1 m₂ hy
  have hd : HasFDerivAt (chart f.1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂)))
      (fderiv ℝ (chart f.1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂))) (oneL E a)) (affA hr (oneL E (a - r))) := by
    rw [affA_one]; exact (differentiableAt_chart f.2 _).hasFDerivAt
  rw [ev.fderiv_eq, (hd.comp (oneL E (a - r)) (hasFDerivAt_affA hr _)).fderiv]
  simp only [ContinuousLinearMap.comp_apply, lowL_single]

theorem slice_smooth_Eop : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ) (hr : r ≤ a)
    (m₁ : GA E r) (f : Sm E a),
    (fun m₂ : GA E (a - r) => f.1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂))) ∈ Sm E (a - r) ∧
      ∀ (τ : E →+* ℂ) (p p' : Fin (a - r)) (ψ : Sm E (a - r)),
        ψ.1 = (fun m₂ : GA E (a - r) => f.1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂))) →
        (Eop τ p p' ψ).1 = fun m₂ : GA E (a - r) =>
          (Eop τ (GlobalTheory.LeviGA.blkEquiv hr (Sum.inr p)) (GlobalTheory.LeviGA.blkEquiv hr (Sum.inr p')) f).1
            (GlobalTheory.LeviGA.blkGL hr (m₁, m₂)) := by
  intro E _ _ _ a r hr m₁ f
  refine ⟨slice_mem_Sm hr m₁ f, fun τ p p' ψ hψ => funext fun m₂ => ?_⟩
  simp only [Eop, LinearMap.smul_apply, LinearMap.sub_apply, Submodule.coe_smul, Submodule.coe_sub, Pi.smul_apply,
    Pi.sub_apply, lieS_slice hr m₁ f p p' ψ hψ]

end GlobalTheory.LeviSliceGA
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviSliceSmoothAndMatrixUnitActionStatement
open NumberField MeasureTheory GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leviSlice_smooth_and_matrixUnit_action : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ) (hr : r ≤ a) (m₁ : GA E r) (f : Sm E a), (fun m₂ : GA E (a - r) => f.1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂))) ∈ Sm E (a - r) ∧ ∀ (τ : E →+* ℂ) (p p' : Fin (a - r)) (ψ : Sm E (a - r)), ψ.1 = (fun m₂ : GA E (a - r) => f.1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂))) → (Eop τ p p' ψ).1 = fun m₂ : GA E (a - r) => (Eop τ (GlobalTheory.LeviGA.blkEquiv hr (Sum.inr p)) (GlobalTheory.LeviGA.blkEquiv hr (Sum.inr p')) f).1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂)) := by
  first | exact @GlobalTheory.LeviSliceGA.slice_smooth_Eop | exact GlobalTheory.LeviSliceGA.slice_smooth_Eop | (intros; apply GlobalTheory.LeviSliceGA.slice_smooth_Eop <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AevalQuantumDeterminantIntertwining
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AevalQuantumDeterminantIntertwining
open NumberField MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.CapelliIntertw

theorem qdet_map {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (f : A →ₐ[ℂ] B) {n : ℕ}
    (E : Fin n → Fin n → A) (u : ℂ) :
    f (Formalism.REAL.qdet E u) = Formalism.REAL.qdet (fun a b => f (E a b)) u := by
  unfold Formalism.REAL.qdet Formalism.REAL.qminor Formalism.REAL.Tm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_mul, map_intCast, map_list_prod, List.map_ofFn]
  congr 2
  congr 1
  funext k
  simp only [Function.comp_apply, map_add]
  split_ifs <;> simp

variable {M M' : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup M'] [Module ℂ M'] (T : M →ₗ[ℂ] M')

def intertw : Subalgebra ℂ (Module.End ℂ M × Module.End ℂ M') where
  carrier := {z | ∀ v, T (z.1 v) = z.2 (T v)}
  mul_mem' := by
    intro a b ha hb v
    simp only [Prod.fst_mul, Prod.snd_mul, Module.End.mul_apply]
    rw [ha, hb]
  add_mem' := by
    intro a b ha hb v
    simp only [Prod.fst_add, Prod.snd_add, LinearMap.add_apply, map_add (f := _)]
    rw [ha, hb]
  algebraMap_mem' := by
    intro c v
    simp [Module.algebraMap_end_apply]

end GlobalTheory.CapelliIntertw

theorem GlobalTheory.capelli_intertw : ∀ (M M' : Type) [AddCommGroup M] [Module ℂ M] [AddCommGroup M'] [Module ℂ M'] (T : M →ₗ[ℂ] M') (n : ℕ) (X : Fin n → Fin n → Module.End ℂ M) (Y : Fin n → Fin n → Module.End ℂ M'), (∀ i j v, T (X i j v) = Y i j (T v)) → ∀ (u : ℂ) (p : Polynomial ℂ) (v : M), T (Polynomial.aeval (Formalism.REAL.qdet X u) p v) = Polynomial.aeval (Formalism.REAL.qdet Y u) p (T v) := by
  intro M M' _ _ _ _ T n X Y hXY u p v
  let S := GlobalTheory.CapelliIntertw.intertw T
  let Z : Fin n → Fin n → S := fun a b => ⟨(X a b, Y a b), fun w => hXY a b w⟩
  let q : S := Polynomial.aeval (Formalism.REAL.qdet Z u) p
  have h1 : ((q : Module.End ℂ M × Module.End ℂ M').1) = Polynomial.aeval (Formalism.REAL.qdet X u) p := by
    have := Polynomial.aeval_algHom_apply ((AlgHom.fst ℂ _ _).comp S.val) (Formalism.REAL.qdet Z u) p
    rw [GlobalTheory.CapelliIntertw.qdet_map] at this
    exact this.symm
  have h2 : ((q : Module.End ℂ M × Module.End ℂ M').2) = Polynomial.aeval (Formalism.REAL.qdet Y u) p := by
    have := Polynomial.aeval_algHom_apply ((AlgHom.snd ℂ _ _).comp S.val) (Formalism.REAL.qdet Z u) p
    rw [GlobalTheory.CapelliIntertw.qdet_map] at this
    exact this.symm
  rw [← h1, ← h2]
  exact q.2 v
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AevalQuantumDeterminantIntertwiningStatement
open NumberField MeasureTheory GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.aeval_quantumDeterminant_intertwining : ∀ (M M' : Type) [AddCommGroup M] [Module ℂ M] [AddCommGroup M'] [Module ℂ M'] (T : M →ₗ[ℂ] M') (n : ℕ) (X : Fin n → Fin n → Module.End ℂ M) (Y : Fin n → Fin n → Module.End ℂ M'), (∀ i j v, T (X i j v) = Y i j (T v)) → ∀ (u : ℂ) (p : Polynomial ℂ) (v : M), T (Polynomial.aeval (Formalism.REAL.qdet X u) p v) = Polynomial.aeval (Formalism.REAL.qdet Y u) p (T v) := by
  first | exact @GlobalTheory.capelli_intertw | exact GlobalTheory.capelli_intertw | (intros; apply GlobalTheory.capelli_intertw <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EopPreservesLeftUnipotentInvariance
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EopPreservesLeftUnipotentInvariance
open NumberField MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.CuspRep.UnipInv

theorem Eop_unip_left :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ) (f : Sm E a),
      (∀ (x : BlockIx a r → Ad E) (g : GA E a), f.1 (unip x * g) = f.1 g) →
      ∀ (τ : E →+* ℂ) (i j : Fin a) (x : BlockIx a r → Ad E) (g : GA E a),
        (Eop τ i j f).1 (unip x * g) = (Eop τ i j f).1 g := by
  intro E _ _ _ a r f hf τ i j x g
  have hc : chart f.1 (unip x * g) = chart f.1 g := by
    funext y
    unfold chart
    split_ifs
    · rw [mul_assoc, hf]
    · rfl
  have hD : ∀ X, lieD X f.1 (unip x * g) = lieD X f.1 g := fun X => by
    simp only [lieD, hc]
  simp only [Eop, LinearMap.smul_apply, LinearMap.sub_apply, Submodule.coe_smul, Submodule.coe_sub,
    Pi.smul_apply, Pi.sub_apply, lieS_apply, lie_apply, hD]

end GlobalTheory.CuspRep.UnipInv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EopPreservesLeftUnipotentInvarianceStatement
open NumberField MeasureTheory GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eop_preserves_left_unipotent_invariance : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ) (f : Sm E a), (∀ (x : BlockIx a r → Ad E) (g : GA E a), f.1 (unip x * g) = f.1 g) → ∀ (τ : E →+* ℂ) (i j : Fin a) (x : BlockIx a r → Ad E) (g : GA E a), (Eop τ i j f).1 (unip x * g) = (Eop τ i j f).1 g := by
  first | exact @GlobalTheory.CuspRep.UnipInv.Eop_unip_left | exact GlobalTheory.CuspRep.UnipInv.Eop_unip_left | (intros; apply GlobalTheory.CuspRep.UnipInv.Eop_unip_left <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermFiniteDimensionalSpanParabolic
noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.SliceTwoCentre

theorem sliceTwoCentre : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ, ∀ (r : ℕ), 0 < r → ∀ (hr : r < a), ∀ [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 → ∀ (t : GL (Fin a) (Af E)) (κ : Kinf E a), ∃ (X' : Set (Module.End ℂ (Sm E (a - r)) → ℂ)) (D : ℕ), X'.Finite ∧ ∀ φ ∈ GlobalTheory.HCF.formsGL E a L W X N, ∀ m₁ : GA E r, ∀ ψ : Sm E (a - r), ψ.1 = (fun m₂ : GA E (a - r) => ∫ x in 𝓕, φ.1 (unip x * (GlobalTheory.LeviGA.blkGL hr.le (m₁, m₂) * finGL E a t * infGL E a (Unitary.toUnits κ))) ∂μ) → FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E (a - r)) => z ψ) '' Zalg E (a - r))) ∧ Module.finrank ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E (a - r)) => z ψ) '' Zalg E (a - r))) ≤ D ∧ ∀ (χ' : Module.End ℂ (Sm E (a - r)) → ℂ) (u : Sm E (a - r)), u ∈ Submodule.span ℂ ((fun z : Module.End ℂ (Sm E (a - r)) => z ψ) '' Zalg E (a - r)) → u ≠ 0 → (∀ z ∈ Zalg E (a - r), z u = χ' z • u) → ∃ χ ∈ X', ∀ z ∈ Zalg E (a - r), χ' z = χ z := by
  intro E _ _ _ a L hL W hW X hX N r hr0 hr _ _ μ 𝓕 hμ h𝓕 h1 t κ
  classical
  have hra : r ≤ a := hr.le
  let Q : (E →+* ℂ) → ℂ → Polynomial ℂ := fun τ u =>
    ∏ χ ∈ hX.toFinset, (Polynomial.X - Polynomial.C (χ (cap τ (u - ((a : ℂ) - 1) / 2)))) ^ N
  have hQ : ∀ τ u, Q τ u ≠ 0 := fun τ u =>
    Finset.prod_ne_zero_iff.2 fun χ _ => pow_ne_zero _ (Polynomial.X_sub_C_ne_zero _)
  let M' : Submodule ℂ (Sm E a) :=
    { carrier := {f | ∀ (x : BlockIx a r → Ad E) (g : GA E a), f.1 (unip x * g) = f.1 g}
      add_mem' := fun {f f'} hf hf' x g => by
        simp only [Set.mem_setOf_eq] at hf hf'
        simp [hf x g, hf' x g]
      zero_mem' := fun x g => rfl
      smul_mem' := fun c f hf x g => by
        simp only [Set.mem_setOf_eq] at hf
        simp [hf x g] }
  let K : Submodule ℂ (Sm E a) :=
    { carrier := {f | ∀ (m₁ : GA E r) (m₂ : GA E (a - r)), f.1 (GlobalTheory.LeviGA.blkGL hra (m₁, m₂)) = 0}
      add_mem' := fun {f f'} hf hf' m₁ m₂ => by
        simp only [Set.mem_setOf_eq] at hf hf'
        simp [hf m₁ m₂, hf' m₁ m₂]
      zero_mem' := fun m₁ m₂ => rfl
      smul_mem' := fun c f hf m₁ m₂ => by
        simp only [Set.mem_setOf_eq] at hf
        simp [hf m₁ m₂] }
  have hq : ∀ τ : E →+* ℂ, ∃ q : ℂ → Polynomial ℂ, (∀ u, q u ≠ 0) ∧ ∀ v ∈ M',
      (∀ u, Polynomial.aeval (Formalism.REAL.qdet (Eop τ) u) (Q τ u) v = 0) → ∀ u,
        Polynomial.aeval (Formalism.REAL.qdet (fun p p' : Fin (a - r) => Eop τ (GlobalTheory.LeviGA.blkEquiv hra (Sum.inr p))
          (GlobalTheory.LeviGA.blkEquiv hra (Sum.inr p'))) u) (q u) v ∈ K := by
    intro τ
    obtain ⟨q, hq0, hqK⟩ := GlobalTheory.T.harishChandra_capelli_uniform_diagonalBlocks (Sm E a) a r hra (Eop τ) (glRel_Eop τ) M' K
      (fun i j f hf => GlobalTheory.T.eop_preserves_left_unipotent_invariance E a r f hf τ i j)
      (fun i j hi hj f hf => GlobalTheory.T.matrixUnitOp_upperBlock_levi_eq_zero E a r hra f hf τ i j hi hj)
      (fun i j hij f hf => GlobalTheory.T.levi_restriction_vanishing_preserved_by_operator E a r hra f hf τ i j hij) (Q τ) (hQ τ)
    exact ⟨q, hq0, fun v hv hk u => (hqK v hv hk u).2⟩
  choose q hq0 hqK using hq
  obtain ⟨X', D, hX', hfin⟩ := GlobalTheory.T.capelliKilled_smoothFunction_centreOrbit_finiteDimensional E (a - r) (fun τ u => q τ (u + (((a - r : ℕ) : ℂ) - 1) / 2))
    (fun τ u => hq0 τ _)
  refine ⟨X', D, hX', fun φ hφ m₁ ψ hψ => hfin ψ fun τ u => ?_⟩
  obtain ⟨hl, ho, hk⟩ := GlobalTheory.T.rightTranslate_harishChandraFiniteForm_properties E a L W X hX.toFinset (by simp) N φ hφ t κ
  obtain ⟨hcSm, -⟩ := GlobalTheory.ConstTermSmooth.constTerm_mem_Sm E a r μ 𝓕 hμ h𝓕 h1 _ hl ho
  let c : Sm E a := ⟨_, hcSm⟩
  have hcM : c ∈ M' := fun x g => constTerm_unip_invariant E a r μ 𝓕 hμ h𝓕 _ hl x g
  have hcQ : ∀ u, Polynomial.aeval (Formalism.REAL.qdet (Eop τ) u) (Q τ u) c = 0 := by
    intro u
    have e : Formalism.REAL.qdet (Eop (a := a) τ) u = cap (a := a) τ (u - ((a : ℂ) - 1) / 2) := by
      rw [cap, sub_add_cancel]
    rw [e]
    have hz : Polynomial.aeval (cap (a := a) τ (u - ((a : ℂ) - 1) / 2)) (Q τ u) ∈ Zalg E a := by
      rw [← Polynomial.aeval_subalgebra_coe (Q τ u) (Zalg E a)
        ⟨cap (a := a) τ (u - ((a : ℂ) - 1) / 2), Algebra.subset_adjoin ⟨τ, _, rfl⟩⟩]
      exact SetLike.coe_mem _
    have h2 := GlobalTheory.T.constant_term_center_action_smooth_form E a r μ 𝓕 hμ h𝓕 h1 _ hl ho _ hz c rfl
    refine Subtype.ext (h2.trans (funext fun g => ?_))
    rw [hk τ (u - ((a : ℂ) - 1) / 2)]
    simp
  have hK := hqK τ c hcM hcQ (u + (((a - r : ℕ) : ℂ) - 1) / 2)
  let T : Sm E a →ₗ[ℂ] Sm E (a - r) :=
    { toFun := fun f => ⟨_, (GlobalTheory.T.leviSlice_smooth_and_matrixUnit_action E a r hra m₁ f).1⟩
      map_add' := fun f f' => rfl
      map_smul' := fun c f => rfl }
  have hT : ∀ (p p' : Fin (a - r)) (f : Sm E a),
      T (Eop τ (GlobalTheory.LeviGA.blkEquiv hra (Sum.inr p)) (GlobalTheory.LeviGA.blkEquiv hra (Sum.inr p')) f) = Eop τ p p' (T f) :=
    fun p p' f => Subtype.ext ((GlobalTheory.T.leviSlice_smooth_and_matrixUnit_action E a r hra m₁ f).2 τ p p' (T f) rfl).symm
  have hψc : T c = ψ := by
    refine Subtype.ext (hψ.symm ▸ funext fun m₂ => ?_)
    simp only [T, c, LinearMap.coe_mk, AddHom.coe_mk, rt_apply, mul_assoc]
  have h3 := GlobalTheory.T.aeval_quantumDeterminant_intertwining (Sm E a) (Sm E (a - r)) T (a - r)
    (fun p p' => Eop τ (GlobalTheory.LeviGA.blkEquiv hra (Sum.inr p)) (GlobalTheory.LeviGA.blkEquiv hra (Sum.inr p'))) (Eop τ)
    hT (u + (((a - r : ℕ) : ℂ) - 1) / 2) (q τ (u + (((a - r : ℕ) : ℂ) - 1) / 2)) c
  have h0 : T (Polynomial.aeval (Formalism.REAL.qdet (fun p p' : Fin (a - r) => Eop τ (GlobalTheory.LeviGA.blkEquiv hra (Sum.inr p))
      (GlobalTheory.LeviGA.blkEquiv hra (Sum.inr p'))) (u + (((a - r : ℕ) : ℂ) - 1) / 2))
      (q τ (u + (((a - r : ℕ) : ℂ) - 1) / 2)) c) = 0 :=
    Subtype.ext (funext fun m₂ => hK m₁ m₂)
  show Polynomial.aeval (cap τ u) (q τ (u + (((a - r : ℕ) : ℂ) - 1) / 2)) ψ = 0
  rw [cap, ← hψc, ← h3, h0]

end GlobalTheory.SliceTwoCentre

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermFiniteDimensionalSpanParabolicStatement
open NumberField MeasureTheory GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_term_finite_dimensional_span_parabolic : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ, ∀ (r : ℕ), 0 < r → ∀ (hr : r < a), ∀ [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 → ∀ (t : GL (Fin a) (Af E)) (κ : Kinf E a), ∃ (X' : Set (Module.End ℂ (Sm E (a - r)) → ℂ)) (D : ℕ), X'.Finite ∧ ∀ φ ∈ GlobalTheory.HCF.formsGL E a L W X N, ∀ m₁ : GA E r, ∀ ψ : Sm E (a - r), ψ.1 = (fun m₂ : GA E (a - r) => ∫ x in 𝓕, φ.1 (unip x * (GlobalTheory.LeviGA.blkGL hr.le (m₁, m₂) * finGL E a t * infGL E a (Unitary.toUnits κ))) ∂μ) → FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E (a - r)) => z ψ) '' Zalg E (a - r))) ∧ Module.finrank ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E (a - r)) => z ψ) '' Zalg E (a - r))) ≤ D ∧ ∀ (χ' : Module.End ℂ (Sm E (a - r)) → ℂ) (u : Sm E (a - r)), u ∈ Submodule.span ℂ ((fun z : Module.End ℂ (Sm E (a - r)) => z ψ) '' Zalg E (a - r)) → u ≠ 0 → (∀ z ∈ Zalg E (a - r), z u = χ' z • u) → ∃ χ ∈ X', ∀ z ∈ Zalg E (a - r), χ' z = χ z := by
  first | exact @GlobalTheory.SliceTwoCentre.sliceTwoCentre | exact GlobalTheory.SliceTwoCentre.sliceTwoCentre | (intros; apply GlobalTheory.SliceTwoCentre.sliceTwoCentre <;> assumption)
end
