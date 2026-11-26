module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.UOfSat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CapCentral

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.LieX0EqRaisingLowering
open NumberField GlobalTheory.CuspRep Matrix UpperTheory.V

namespace UpperTheory.V.Br.WeightVectorLie

variable {F : Type} [Field F] [NumberField F]

private noncomputable def rot (t : ℝ) : TR.Kinf F 2 :=
  ⟨!![fun _ => Real.cos t, fun _ => Real.sin t; fun _ => -Real.sin t, fun _ => Real.cos t], by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j v
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_apply] <;>
      nlinarith [Real.sin_sq_add_cos_sq t]⟩

omit [NumberField F] in
private theorem rot_zero : rot 0 = (1 : TR.Kinf F 2) := by
  ext i j v
  fin_cases i <;> fin_cases j <;> simp [rot]

private noncomputable def X0 : TR.Lie F 2 := TR.toL !![0, 1; -1, 0]

private theorem lie_X0_eq_raising_lowering [IsTotallyReal F] [Subsingleton (InfinitePlace F)] (v : InfinitePlace F) (φ : TR.Sm F 2) :
    TR.Eop v 0 1 φ - TR.Eop v 1 0 φ = TR.lie F 2 X0 φ := by
  unfold TR.Eop
  rw [← LinearMap.sub_apply, ← map_sub]
  congr 2
  ext i j u
  obtain rfl : u = v := Subsingleton.elim _ _
  fin_cases i <;> fin_cases j <;> simp [X0]

private theorem rot_deriv : HasDerivAt (fun t : ℝ => TR.toL (Unitary.toUnits (rot (F := F) t)).val) X0 0 := by
  refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun v => ?_
  fin_cases i <;> fin_cases j
  · simpa [X0, rot] using Real.hasDerivAt_cos 0
  · simpa [X0, rot] using Real.hasDerivAt_sin 0
  · simpa [X0, rot] using (Real.hasDerivAt_sin 0).fun_neg
  · simpa [X0, rot] using Real.hasDerivAt_cos 0

private theorem lie_mem [IsTotallyReal F] (U : Submodule ℂ (TR.Sm F 2)) [FiniteDimensional ℂ U]
    (hU : ∀ k, ∀ ψ ∈ U, TR.cptRep F 2 k ψ ∈ U) (ψ : TR.Sm F 2) (hψ : ψ ∈ U) : TR.lie F 2 X0 ψ ∈ U := by
  let U' : Submodule ℂ (GA F 2 → ℂ) := U.map (TR.Sm F 2).subtype
  have hcl : IsClosed (U' : Set (GA F 2 → ℂ)) := U'.closed_of_finiteDimensional
  have key : ∀ g, HasDerivAt (fun t => (TR.cptRep F 2 (rot t) ψ).1 g) ((TR.lie F 2 X0 ψ).1 g) 0 := fun g =>
    TR.hasDerivAt_curve ψ g (fun t => Unitary.toUnits (rot t)) X0 (by rw [rot_zero, map_one]) rot_deriv
  have hm : (TR.lie F 2 X0 ψ).1 ∈ U' := by
    refine hcl.mem_of_tendsto (b := nhdsWithin (0 : ℝ) {0}ᶜ)
      (f := fun t g => slope (fun t => (TR.cptRep F 2 (rot t) ψ).1 g) 0 t)
      (tendsto_pi_nhds.2 fun g => hasDerivAt_iff_tendsto_slope.1 (key g)) (Filter.Eventually.of_forall fun t => ?_)
    exact U'.smul_of_tower_mem ((t - 0)⁻¹ : ℝ)
      (U'.sub_mem (Submodule.mem_map_of_mem (hU (rot t) ψ hψ)) (Submodule.mem_map_of_mem (hU (rot 0) ψ hψ)))
  obtain ⟨χ, hχ, e⟩ := hm
  rwa [← Subtype.ext e]

private theorem eig_abs {G M : Type} [Group G] [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M) (D : Module.End ℂ M)
    (hD : ∀ U : Submodule ℂ M, FiniteDimensional ℂ U → (∀ k, ∀ ψ ∈ U, ρ k ψ ∈ U) → ∀ ψ ∈ U, D ψ ∈ U)
    (V : Submodule ℂ M) (φ : M) (hφ0 : φ ≠ 0) (hV : ∀ k, ρ k φ ∈ V)
    (hf : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => ρ k φ))) :
    ∃ ψ ∈ V, ψ ≠ 0 ∧ ∃ z : ℂ, D ψ = z • ψ := by
  let U : Submodule ℂ M := Submodule.span ℂ (Set.range fun k => ρ k φ)
  have hUV : U ≤ V := Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact hV k)
  have hU : ∀ k, ∀ ψ ∈ U, ρ k ψ ∈ U := fun k ψ hψ => by
    have h : U ≤ U.comap (ρ k) := Submodule.span_le.2 (by
      rintro _ ⟨k', rfl⟩
      exact Submodule.subset_span ⟨k * k', by simp⟩)
    exact h hψ
  have hφU : φ ∈ U := Submodule.subset_span ⟨1, by simp⟩
  have : Nontrivial U := ⟨⟨⟨φ, hφU⟩, 0, fun h => hφ0 (congrArg Subtype.val h)⟩⟩
  obtain ⟨z, hz⟩ := Module.End.exists_eigenvalue (D.restrict (hD U hf hU))
  obtain ⟨ψ, hψ⟩ := hz.exists_hasEigenvector
  exact ⟨ψ.1, hUV ψ.2, fun h => hψ.2 (Subtype.ext h), z, congrArg Subtype.val hψ.apply_eq_smul⟩

private theorem act_cpt [IsTotallyReal F] (k : TR.Kinf F 2) : TR.act (.cpt k) = TR.cptRep F 2 k := by
  rw [TR.act]

private theorem eig [IsTotallyReal F] [Subsingleton (InfinitePlace F)] (π : TR.CuspSub F 2) :
    ∃ φ ∈ π.V, φ ≠ 0 ∧ ∃ z : ℂ, ∀ v, TR.Eop v 0 1 φ - TR.Eop v 1 0 φ = z • φ := by
  obtain ⟨φ, hφ, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot π.ne_bot
  obtain ⟨ψ, h1, h2, z, h3⟩ := eig_abs (TR.cptRep F 2) (TR.lie F 2 X0) (fun U _ hU => lie_mem U hU) π.V φ hφ0
    (fun k => by rw [← act_cpt]; exact π.stable _ φ hφ) (π.cusp φ hφ).1.kfin
  exact ⟨ψ, h1, h2, z, fun v => (lie_X0_eq_raising_lowering v ψ).trans h3⟩

private theorem int_of [IsTotallyReal F] [Subsingleton (InfinitePlace F)] (ψ : TR.Sm F 2) (h0 : ψ ≠ 0) (z : ℂ)
    (he : ∀ v, TR.Eop v 0 1 ψ - TR.Eop v 1 0 ψ = z • ψ) : ∃ n : ℤ, z = Complex.I * n := by
  have hr : IsRot (F := F) (fun _ => 2 * Real.pi) 1 := by
    ext i j v
    fin_cases i <;> fin_cases j <;> simp
  obtain ⟨g, hg⟩ : ∃ g, ψ.1 g ≠ 0 := by
    by_contra h
    push Not at h
    exact h0 (Subtype.ext (funext h))
  have h1 := rotEig F ψ z he _ _ hr g
  rw [map_one, mul_one] at h1
  have h2 : Complex.exp (z * (2 * Real.pi)) = 1 := by
    have h3 := mul_right_cancel₀ hg (h1.symm.trans (one_mul _).symm)
    have : Unique (InfinitePlace F) := uniqueOfSubsingleton (Classical.arbitrary _)
    simpa using h3
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h2
  refine ⟨n, ?_⟩
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  apply mul_right_cancel₀ hpi
  rw [hn]; ring

end UpperTheory.V.Br.WeightVectorLie

open UpperTheory.V.Br.WeightVectorLie in
theorem UpperTheory.V.Br.wtVec :
    UpperTheory.V.Br.WtVec := by
  intro π
  obtain ⟨φ, hφ, h0, z, he⟩ := eig π
  obtain ⟨n, rfl⟩ := int_of φ h0 z he
  exact ⟨φ, hφ, h0, n, he⟩
end

noncomputable section

open NumberField UpperTheory.V UpperTheory.V.Af Complex

namespace UpperTheory.V.Br

private theorem low_of {V : Type} [AddCommGroup V] [Module ℂ V] (A B C J : Module.End ℂ V) (H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (k : ℕ)
    (hk : 3 ≤ k) (hAB : ∀ x, A (B x) = B (A x) + B x) (hAC : ∀ x, A (C x) = C (A x) - C x)
    (hBC : ∀ x, B (C x) = C (B x) + (2 : ℂ) • A x)
    (hCas : ∀ x, C (B x) = ((k : ℂ) * (k - 2) / 4) • x - A (A x) - A x)
    (hH : ∀ x, H x x = 0 → x = 0) (hA : ∀ x y, H (A x) y = -H x (A y)) (hB : ∀ x y, H (B x) y = -H x (B y))
    (hC : ∀ x y, H (C x) y = -H x (C y))
    (hJ : ∀ x, J x = 0 → x = 0) (hJA : ∀ x, A (J x) = J (A x)) (hJB : ∀ x, B (J x) = -J (B x)) (hJC : ∀ x, C (J x) = -J (C x))
    (hw : ∃ x, x ≠ 0 ∧ ∃ n : ℤ, B x - C x = (I * n) • x) :
    ∃ x, x ≠ 0 ∧ B x - C x = (I * k) • x ∧ (2 : ℂ) • A x = I • (B x + C x) := by
  have hI : I * I = -1 := I_mul_I
  have key := sl2Low V ((-I) • (B - C)) (A + (I / 2) • (B + C)) (A - (I / 2) • (B + C)) H k hk ?_ ?_ ?_ ?_ hH ?_ ?_ ?_ ?_
  · obtain ⟨x, hx, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := key
    · simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply] at h1 h2
      refine ⟨x, hx, ?_, ?_⟩
      · have : B x - C x = I • ((-I) • (B x - C x)) := by
          rw [smul_smul, mul_neg, hI, neg_neg, one_smul]
        rw [this, h1, smul_smul]
      · linear_combination (norm := module) (2 : ℂ) • h2
    · simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply] at h1 h2
      refine ⟨J x, fun h => hx (hJ x h), ?_, ?_⟩
      · have : B x - C x = I • ((-I) • (B x - C x)) := by
          rw [smul_smul, mul_neg, hI, neg_neg, one_smul]
        rw [h1] at this
        have h3 := congrArg J this
        simp only [map_sub, map_smul] at h3
        rw [hJB, hJC]
        linear_combination (norm := module) -h3
      · have h3 := congrArg J h2
        simp only [map_add (f := _), map_smul, map_zero] at h3
        rw [hJA, hJB, hJC]
        linear_combination (norm := module) (2 : ℂ) • h3
  · ext x
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply, map_add (f := _), map_sub, map_smul,
      hAB, hAC, hBC]
    match_scalars <;> grind
  · ext x
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply, map_add (f := _), map_sub, map_smul,
      hAB, hAC, hBC]
    match_scalars <;> grind
  · ext x
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply, map_add (f := _), map_sub, map_smul,
      Module.End.one_apply, hAB, hAC, hBC, hCas]
    match_scalars <;> grind
  · ext x
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply, map_add (f := _), map_sub, map_smul,
      Module.End.one_apply, hAB, hAC, hBC, hCas]
    match_scalars <;> grind
  · intro x y
    simp [hB, hC]
    ring
  · intro x y
    simp [hA, hB, hC, map_ofNat]
    ring
  · intro x y
    simp [hA, hB, hC, map_ofNat]
    ring
  · obtain ⟨x, hx, n, h⟩ := hw
    refine ⟨x, hx, n, ?_⟩
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, h, smul_smul]
    congr 1
    grind

private def eps : TR.Kinf ℚ 2 :=
  ⟨Matrix.diagonal ![-1, 1], by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp⟩

private theorem eps_Eop (v : InfinitePlace ℚ) (i j : Fin 2) (φ : TR.Sm ℚ 2) :
    TR.cptRep ℚ 2 eps (TR.Eop v i j φ) = (if i = j then 1 else -1 : ℂ) • TR.Eop v i j (TR.cptRep ℚ 2 eps φ) := by
  have h := LinearMap.congr_fun (TR.Cen.rt_Eop (Unitary.toUnits eps) v i j) φ
  have e1 : (Unitary.toUnits eps).val = Matrix.diagonal ![-1, 1] := rfl
  have e2 : ((Unitary.toUnits eps)⁻¹).val = Matrix.diagonal ![-1, 1] := by
    change star (Matrix.diagonal ![-1, 1] : Matrix (Fin 2) (Fin 2) (TR.Rinf ℚ)) = _
    rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    congr 1
  rw [e1, e2] at h
  refine h.trans ?_
  change _ = _ • TR.Eop v i j (TR.rt ℚ 2 (TR.infGL ℚ 2 (Unitary.toUnits eps)) φ)
  fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_two]

end UpperTheory.V.Br

open UpperTheory.V.Br in
theorem UpperTheory.V.Br.holVec :
    UpperTheory.V.Br.HolVec := by
  classical
  intro k hk π hπ H hH
  let v : InfinitePlace ℚ := default
  have hv : ∀ w : InfinitePlace ℚ, w = v := fun w => Subsingleton.elim _ _
  let E : Fin 2 → Fin 2 → Module.End ℂ π.V := fun i j => (TR.Eop v i j).restrict fun φ h => π.stable (.lie _) φ h
  have hE : ∀ i j x, (E i j x).1 = TR.Eop v i j x.1 := fun _ _ _ => rfl
  have hcap := capTwo ℚ π v _ _ (hπ v)
  have hD : ∀ φ ∈ π.V, TR.Eop v 1 1 φ = -TR.Eop v 0 0 φ := fun φ hφ => by
    have := (hcap φ hφ).1
    rw [add_neg_cancel, zero_smul] at this
    exact eq_neg_of_add_eq_zero_right this
  have hrel : ∀ i j k l φ, _ := fun i j k l (φ : TR.Sm ℚ 2) => LinearMap.congr_fun (TR.glRel_Eop (a := 2) v i j k l) φ
  have hadj : ∀ i j x y, H (E i j x) y = -H x (E i j y) := fun i j x y => eq_neg_of_add_eq_zero_left (hH.lie _ x y)
  have hJ : ∀ i j x, π.op (.cpt eps) (E i j x) = (if i = j then 1 else -1 : ℂ) • E i j (π.op (.cpt eps) x) := fun i j x =>
    Subtype.ext (eps_Eop v i j x.1)
  have hBC : ∀ x, E 0 1 (E 1 0 x) = E 1 0 (E 0 1 x) + (2 : ℂ) • E 0 0 x := fun x => by
    refine Subtype.ext ?_
    have h := hrel 0 1 1 0 x.1
    simp only [if_true, LinearMap.sub_apply, Module.End.mul_apply, hD _ x.2] at h
    simp only [Submodule.coe_add, Submodule.coe_smul, hE]
    linear_combination (norm := module) h
  have key := low_of (E 0 0) (E 0 1) (E 1 0) (π.op (.cpt eps)) H k hk ?_ ?_ hBC ?_ hH.definite (hadj 0 0) (hadj 0 1)
    (hadj 1 0) ?_ ?_ ?_ ?_ ?_
  · obtain ⟨x, hx, h1, h2⟩ := key
    refine ⟨x.1, x.2, fun h => hx (Subtype.ext h), fun w => ?_, fun w => ?_, fun w => ?_⟩
    · rw [hv w]
      exact congrArg Subtype.val h1
    · rw [hv w, hD _ x.2, sub_neg_eq_add, ← two_smul ℂ]
      exact congrArg Subtype.val h2
    · rw [hv w, hD _ x.2, add_neg_cancel]
  · intro x
    refine Subtype.ext ?_
    have h := hrel 0 0 0 1 x.1
    simp at h
    simp only [Submodule.coe_add, hE]
    linear_combination (norm := module) h
  · intro x
    refine Subtype.ext ?_
    have h := hrel 0 0 1 0 x.1
    simp at h
    simp only [Submodule.coe_sub, hE]
    linear_combination (norm := module) h
  · intro x
    refine Subtype.ext ?_
    have h := (hcap x.1 x.2).2
    have h' := congrArg Subtype.val (hBC x)
    rw [hD _ x.2, map_neg, hD (TR.Eop v 0 0 x.1) (E 0 0 x).2, neg_neg] at h
    simp only [Submodule.coe_add, Submodule.coe_sub, Submodule.coe_smul, hE] at h h' ⊢
    linear_combination (norm := module) (1 / 2 : ℂ) • h - (1 / 2 : ℂ) • h'
  · intro x h
    refine hH.definite x ?_
    rw [← hH.cpt eps x x, h]
    simp
  · intro x
    simp [hJ]
  · intro x
    simp [hJ]
  · intro x
    simp [hJ]
  · obtain ⟨φ, hφ, h0, n, h⟩ := wtVec π
    exact ⟨⟨φ, hφ⟩, fun e => h0 (congrArg Subtype.val e), n, Subtype.ext (h v)⟩
