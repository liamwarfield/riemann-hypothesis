module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.SumCoordRe
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.AlgIrr

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.PetEx
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.OpenFix
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.SqUniq
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct
open Formalism.L2.Host GlobalTheory.UnitaryBC

section
variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem chi_split {χ : HChar E} {s : ℝ} (h : χ.IsAbsPow s) :
    ((chiDet a χ (splitCentre E a 1) : ℂˣ) : ℂ) = ((Real.exp ((a : ℝ) * s * Fintype.card (E →+* ℂ)) : ℝ) : ℂ) := by
  have e : chiDet a χ (splitCentre E a 1) = chiInf χ (GeneralLinearGroup.det
      (Units.map (Matrix.scalar (Fin a)).toMonoidHom (expU fun _ : InfinitePlace E => ((1 : ℝ) : ℂ)))) :=
    congrArg χ.1 (det_infGL _)
  rw [e, GlobalTheory.CuspRep.InfType.chiInf_eq χ (fun σ => σ) (fun _ z => ((‖z‖ : ℝ) : ℂ) ^ (s : ℂ)) (fun σ z hz =>
    ContinuousAt.cpow (Complex.continuous_ofReal.comp continuous_norm).continuousAt continuousAt_const
      (Complex.ofReal_mem_slitPlane.2 (norm_pos_iff.2 hz))) h.2.2]
  have d : ((GeneralLinearGroup.det (Units.map (Matrix.scalar (Fin a)).toMonoidHom
      (expU fun _ : InfinitePlace E => ((1 : ℝ) : ℂ))) : (Cinf E)ˣ) : Cinf E) =
      ((expU fun _ : InfinitePlace E => ((1 : ℝ) : ℂ) : (Cinf E)ˣ) : Cinf E) ^ a := by
    simp [Matrix.det_diagonal]
  have c : ∀ σ : E →+* ℂ, ‖coord σ (((expU fun _ : InfinitePlace E => ((1 : ℝ) : ℂ) : (Cinf E)ˣ) : Cinf E) ^ a)‖ =
      Real.exp a := fun σ => by
    have c1 : coord σ (fun _ : InfinitePlace E => ((1 : ℝ) : ℂ)) = 1 := map_one (coord σ)
    rw [map_pow, norm_pow, GlobalTheory.CuspRep.InfType.coord_expU, c1, Complex.norm_exp, Complex.one_re, Real.exp_one_pow]
  simp only [d, c]
  rw [← Complex.ofReal_cpow (Real.exp_pos _).le, ← Real.exp_mul, Finset.prod_const, Finset.card_univ,
    ← Complex.ofReal_pow, ← Real.exp_nat_mul, mul_comm]

omit [_root_.NumberField.IsTotallyComplex E] in
private theorem absPow_uniq {χ χ' : HChar E} {s : ℝ} (h : χ.IsAbsPow s) (h' : χ'.IsAbsPow s) : χ = χ' := by
  rw [← mul_inv_eq_one]
  refine GlobalTheory.DiscSpec.Model.eq_one_of_isAbsPow ⟨fun v x hx => ?_, fun v => ?_, fun k => ?_⟩
  · have loc_mul (a b : HChar E) : (a * b).loc v x = a.loc v x * b.loc v x := rfl
    have loc_inv (a : HChar E) : (a⁻¹).loc v x = (a.loc v x)⁻¹ := rfl
    rw [loc_mul, loc_inv, h.1 v x hx, h'.1 v x hx, inv_one, mul_one]
  · have : χ.val v = χ'.val v := Units.ext ((h.2.1 v).trans (h'.2.1 v).symm)
    rw [HChar.val_mul, HChar.val_inv, this, mul_inv_cancel]; simp
  · have : χ.inf k = χ'.inf k := Units.ext ((h.2.2 k).trans (h'.2.2 k).symm)
    rw [HChar.inf_mul, HChar.inf_inv, this, mul_inv_cancel]; simp

end

theorem UpperTheory.V.Lit.Bor.sqUniq :
    UpperTheory.V.Lit.Bor.SqUniq := by
  rintro E _ _ _ a ha r χ ⟨⟨s, hs⟩, htw⟩ φ hφ ⟨s', χ', hs', hsq⟩
  have hfun : ∀ ν : HChar E, (mulChi a ν φ).1 = fun g => ((chiDet a ν g : ℂˣ) : ℂ) * φ.1 g := fun ν =>
    funext fun g => by rw [mulChi_apply, mul_comm]
  by_cases h0 : ∀ g, φ.1 g = 0
  · rw [hfun]
    simpa only [h0, mul_zero] using hsq
  obtain ⟨g, hg⟩ := not_forall.1 h0
  have hz : lie E a (oneL E a) (mulChi a χ φ) = (0 : ℂ) • mulChi a χ φ := by
    rw [htw, hφ, (ellFacts E a).1 ha, mul_one, ← add_smul, neg_add_cancel, zero_smul, map_zero, zero_smul]
  have h1 := aInv E a _ _ hz 1 g
  have h2 := hsq.1 1 g
  have h3 := aInv E a _ _ hφ 1 g
  simp only [hfun, zero_mul, Complex.exp_zero, one_mul, map_mul, Units.val_mul, h3] at h1 h2
  have key : ∀ x y : ℂ, y ≠ 0 → x * y * (Complex.exp (-(r : ℂ) * (1 : ℝ)) * φ.1 g) = y * φ.1 g →
      x = (Complex.exp (-(r : ℂ) * (1 : ℝ)))⁻¹ := fun x y hy h =>
    eq_inv_of_mul_eq_one_left (mul_right_cancel₀ (mul_ne_zero hy hg) (by linear_combination h))
  have h4 := (key _ _ (Units.ne_zero _) h1).trans (key _ _ (Units.ne_zero _) h2).symm
  rw [chi_split hs, chi_split hs', Complex.ofReal_inj, Real.exp_eq_exp] at h4
  have hc : (Fintype.card (E →+* ℂ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have ha' : (a : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  obtain rfl : s = s' := mul_left_cancel₀ ha' (mul_right_cancel₀ hc h4)
  rw [hfun, absPow_uniq hs hs']
  exact hsq
end

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem open_fix {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (v : V) {S : Set G} (hS : IsOpen S) (h1 : (1 : G) ∈ S) (h : ∀ g ∈ S, ρ g v = v) :
    IsOpen {g | ρ g v = v} := by
  rw [isOpen_iff_forall_mem_open]
  intro g hg
  refine ⟨(fun x => g⁻¹ * x) ⁻¹' S, fun x hx => ?_, hS.preimage (by fun_prop), by simpa using h1⟩
  have e : x = g * (g⁻¹ * x) := by group
  have hg' : ρ g v = v := hg
  show ρ x v = v
  rw [e, map_mul, Module.End.mul_apply, h _ hx, hg']

theorem UpperTheory.V.Lit.Bor.sqMem :
    UpperTheory.V.Lit.Bor.SqMem := by
  intro E _ _ _ a ha μ _ r χ hχ φ hφ
  change IsOpen {k | finRep E a k (mulChi a χ φ) = mulChi a χ φ} ∧ _
  induction hφ using Submodule.span_induction with
  | mem φ h =>
    have hl : IsOpen {k | finRep E a k φ = φ} := h.level
    have ho : IsOpen {k | finRep E a k (mulChi a χ φ) = mulChi a χ φ} := by
      refine open_fix (finRep E a) _ (hl.inter (isOpen_ker_chiDet (a := a) χ)) ⟨by simp, by simp⟩ ?_
      rintro k ⟨h1, h2⟩
      have h1' : rt E a (finGL E a k) φ = φ := h1
      have h2' : chiDet a χ (finGL E a k) = 1 := h2
      change rt E a (finGL E a k) (mulChi a χ φ) = _
      rw [rt_mulChi, h1', h2']
      simp
    have hs := sqUniq E a ha r χ hχ φ h.one (by simpa using h.sq [])
    refine ⟨ho, (CuspidalL2GL.memL2_iff_isSqInt (ContAut.continuous_of_isOpen_stab E a _ ho) (fun γ g => ?_) hs.1).2 hs⟩
    rw [mulChi_apply, mulChi_apply, map_mul, chiDet_ratGL, one_mul, h.left]
  | zero =>
    rw [map_zero]
    refine ⟨?_, fun _ _ _ => rfl, MeasureTheory.MemLp.zero⟩
    convert isOpen_univ using 1
    ext k
    simp only [Set.mem_setOf_eq, map_zero, Set.mem_univ]
  | add φ ψ _ _ h h' =>
    rw [map_add (f := _)]
    refine ⟨open_fix (finRep E a) _ (h.1.inter h'.1) ⟨by simp, by simp⟩ ?_,
      fun γ hγ g => congrArg₂ (· + ·) (h.2.1 γ hγ g) (h'.2.1 γ hγ g), h.2.2.add h'.2.2⟩
    rintro k ⟨h1, h2⟩
    exact (map_add _ _ _).trans (congrArg₂ (· + ·) h1 h2)
  | smul c φ _ h =>
    rw [map_smul]
    refine ⟨open_fix (finRep E a) _ h.1 (by simp) ?_,
      fun γ hγ g => congrArg (c • ·) (h.2.1 γ hγ g), h.2.2.const_smul c⟩
    intro k h1
    exact (map_smul _ _ _).trans (congrArg (c • ·) h1)
end

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct


open MeasureTheory GlobalTheory.CuspRep.CuspidalL2GL in
theorem UpperTheory.V.Lit.Bor.petEx :
    UpperTheory.V.Lit.Bor.PetEx := by
  intro E _ _ _ a ha r
  obtain ⟨χ, hχ⟩ := twEx E a ha r
  let μ : Measure (GA E a) := Measure.haar
  have hs := sqMem E a ha μ r χ hχ
  have hm : ∀ φ ∈ (sqSub E a r).map (mulChi a χ).toLinearMap,
      GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ φ.1 := by
    rintro _ ⟨φ, hφ, rfl⟩
    exact (hs φ hφ).2
  obtain ⟨p, hp⟩ := LinearMap.exists_leftInverse_of_injective (sqSub E a r).subtype (Submodule.ker_subtype _)
  obtain ⟨T, hT⟩ : ∃ T : Sm E a →ₗ[ℂ] GlobalTheory.AutomorphicL2Unitary.L2 (GlobalTheory.UnitaryBC.latticeGL E a) μ, ∀ φ ∈ sqSub E a r, ∀ (ψ : Sm E a)
      (h : GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ ψ.1), ψ = mulChi a χ φ → T φ = h.toL2 := by
    refine ⟨toL2ₗ μ _ hm ∘ₗ (mulChi a χ).toLinearMap.submoduleMap (sqSub E a r) ∘ₗ p, ?_⟩
    rintro φ hφ _ h rfl
    have e : p φ = ⟨φ, hφ⟩ := LinearMap.congr_fun hp ⟨φ, hφ⟩
    simp only [LinearMap.comp_apply, e]
    rfl
  refine ⟨((innerₛₗ ℂ) ∘ₛₗ T).compl₂ T, ⟨fun x y => ?_, fun x _ => ?_, fun x hx h0 => ?_⟩, fun X φ hφ ψ hψ => ?_⟩
  · exact (inner_conj_symm (T y) (T x)).symm
  · exact inner_self_nonneg (𝕜 := ℂ) (x := T x)
  · have h1 : T x = 0 := inner_self_eq_zero.1 (show inner ℂ (T x) (T x) = 0 from h0)
    rw [hT x hx _ (hs x hx).2 rfl] at h1
    by_contra hne
    refine toL2_ne_zero (hs x hx).2 (ContAut.continuous_of_isOpen_stab E a _ (hs x hx).1) (fun e => hne ?_) h1
    exact (mulChi a χ).map_eq_zero_iff.1 (Subtype.ext e)
  · have hL := (sqLie E a r).2 X
    have hmem : ∀ f ∈ sqSub E a r, lie E a X f + ((r * ell E a X : ℝ) : ℂ) • f ∈ sqSub E a r := fun f hf =>
      add_mem (hL f hf) (Submodule.smul_mem _ _ hf)
    have hd : ∀ f ∈ sqSub E a r, GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ (lie E a X (mulChi a χ f)).1 :=
      fun f hf => by
        rw [hχ.2]
        exact (hs _ (hmem f hf)).2
    have hk := skew_lie_action_L2 E a μ X _ _ (hs φ hφ).1 (hs ψ hψ).1 (hs φ hφ).2 (hs ψ hψ).2 (hd φ hφ) (hd ψ hψ)
    rw [← hT _ (hmem φ hφ) _ (hd φ hφ) (hχ.2 X φ), ← hT _ (hmem ψ hψ) _ (hd ψ hψ) (hχ.2 X ψ),
      ← hT φ hφ _ (hs φ hφ).2 rfl, ← hT ψ hψ _ (hs ψ hψ).2 rfl, map_add, map_add, map_smul, map_smul,
      inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, Complex.conj_ofReal] at hk
    change inner ℂ (T (lie E a X φ)) (T ψ) + inner ℂ (T φ) (T (lie E a X ψ)) = _ * inner ℂ (T φ) (T ψ)
    push_cast at hk ⊢
    linear_combination hk
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.XiSchur
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

theorem UpperTheory.V.Lit.Bor.xiSchur :
    UpperTheory.V.Lit.Bor.XiSchur := by
  intro E _ _ _ a Ξ
  refine ⟨fun X Y => GlobalTheory.AlgInfChar.dmat_bracket Ξ X Y, fun P hP => ?_⟩
  rcases subsingleton_or_nontrivial (Fin Ξ.d → ℂ) with h | h
  · exact ⟨0, Matrix.ext fun i => congrFun (Subsingleton.elim (α := Fin Ξ.d → ℂ) _ _)⟩
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (Matrix.toLin' P : Module.End ℂ (Fin Ξ.d → ℂ))
  have hs : Stab (eEnd Ξ) (Module.End.eigenspace (Matrix.toLin' P : Module.End ℂ (Fin Ξ.d → ℂ)) c) := by
    intro τ i j w hw
    have hcm : Commute P (eL Ξ.dmat τ i j) := ((hP _).sub_right ((hP _).smul_right _)).smul_right _
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hw ⊢
    rw [eEnd, Matrix.toLin'_apply, Matrix.mulVec_mulVec, hcm.eq, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_smul]
  have ht := ((algIrr E a Ξ).2 _ hs).resolve_left hc
  refine ⟨c, Matrix.toLin'.injective (LinearMap.ext fun v => ?_)⟩
  have hv : v ∈ Module.End.eigenspace (Matrix.toLin' P : Module.End ℂ (Fin Ξ.d → ℂ)) c := by
    rw [ht]; trivial
  rw [Module.End.mem_eigenspace_iff.1 hv, map_smul, Matrix.toLin'_one]
  rfl
end
