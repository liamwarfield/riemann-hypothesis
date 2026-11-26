module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemExpSolCons
noncomputable section

open NumberField GlobalTheory.CuspRep

namespace GlobalTheory.HCF

def solStep (c : ℂ) (V : Submodule ℂ (ℝ → ℂ)) : Submodule ℂ (ℝ → ℂ) :=
    { carrier := {f | Differentiable ℝ f ∧ (deriv f - c • f) ∈ V}
      add_mem' := fun {f g} hf hg => by
        refine ⟨hf.1.add hg.1, ?_⟩
        have e : deriv (f + g) - c • (f + g) = (deriv f - c • f) + (deriv g - c • g) := by
          funext x
          simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          rw [deriv_add (hf.1 x) (hg.1 x)]; ring
        rw [e]; exact add_mem hf.2 hg.2
      zero_mem' := ⟨differentiable_const 0, by
        have e : deriv (0 : ℝ → ℂ) - c • (0 : ℝ → ℂ) = 0 := by
          funext x; simp
        rw [e]; exact zero_mem _⟩
      smul_mem' := fun k f hf => by
        refine ⟨hf.1.const_smul k, ?_⟩
        have e : deriv (k • f) - c • (k • f) = k • (deriv f - c • f) := by
          funext x
          simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          rw [deriv_const_smul k (hf.1 x)]; simp only [smul_eq_mul]; ring
        rw [e]; exact Submodule.smul_mem _ _ hf.2 }

def expSol (l : List ℂ) : Submodule ℂ (ℝ → ℂ) := l.foldr solStep ⊥

theorem mem_expSol_nil {f : ℝ → ℂ} : f ∈ expSol [] ↔ f = 0 := Submodule.mem_bot ℂ

theorem mem_expSol_cons {c : ℂ} {l : List ℂ} {f : ℝ → ℂ} :
    f ∈ expSol (c :: l) ↔ Differentiable ℝ f ∧ (deriv f - c • f) ∈ expSol l := Iff.rfl

variable (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)

def expCurve (t : ℝ) : GA E a :=
  Matrix.GeneralLinearGroup.scalar (Fin a) (infId E (expU (t • (1 : Cinf E))))

abbrev scalD : Module.End ℂ (Sm E a) := lie E a (Central.scL a 1)

variable {E a}

theorem expCurve_add (s t : ℝ) : expCurve E a (s + t) = expCurve E a s * expCurve E a t := by
  unfold expCurve
  rw [add_smul, expU_add, map_mul, map_mul]

theorem expCurve_zero : expCurve E a 0 = 1 := by
  unfold expCurve
  rw [zero_smul, expU_zero, map_one, map_one]

end GlobalTheory.HCF

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicAbsDetMulArchimedeanExpScalarCurve
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicAbsDetMulArchimedeanExpScalarCurve
noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology

namespace GlobalTheory.HCF

theorem expCurve_eq_diagUnits (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (t : ℝ) :
    expCurve E a t = GroundTheory.Automorphic.Reduction.diagUnits a
      (fun _ : Fin a => GroundTheory.Automorphic.Reduction.posIdele (K := E) (Real.exp t) (Real.exp_pos t)) := by
  rw [GlobalTheory.CuspBoundSiegel.posIdele_exp]
  have e : t • (1 : Cinf E) = fun _ => (t : ℂ) := by
    funext w; simp
  unfold expCurve
  rw [e]
  refine Units.ext ?_
  rw [GroundTheory.Automorphic.Reduction.coe_diagUnits]
  rfl

theorem absDetA_mul_expCurve (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (g : GA E a) (t : ℝ) :
    absDetA (g * expCurve E a t) = absDetA g * Real.exp (t * (a * Module.finrank ℚ E)) := by
  unfold absDetA
  rw [GroundTheory.Automorphic.Reduction.adeleAbs_units (K := E), GroundTheory.Automorphic.Reduction.adeleAbs_units (K := E),
    map_mul, map_mul, Positive.val_mul, expCurve_eq_diagUnits, GlobalTheory.CuspBoundSiegel.ideleModule_det_diagUnits_posIdele,
    ← Real.exp_nat_mul]
  congr 2
  push_cast; ring

end GlobalTheory.HCF

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicAbsDetMulArchimedeanExpScalarCurveStatement
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicAbsDet_mul_archimedeanExpScalarCurve : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (g : GA E a) (t : ℝ),
    absDetA (g * expCurve E a t) = absDetA g * Real.exp (t * (a * Module.finrank ℚ E)) := by
  first | exact @GlobalTheory.HCF.absDetA_mul_expCurve | exact GlobalTheory.HCF.absDetA_mul_expCurve | (intros; apply GlobalTheory.HCF.absDetA_mul_expCurve <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExponentialPolynomialSolutionSpaceFiniteDimensio
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExponentialPolynomialSolutionSpaceFiniteDimensio
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology

namespace GlobalTheory.HCF

theorem eq_smul_exp_of_deriv_eq {c : ℂ} {f : ℝ → ℂ} (hf : Differentiable ℝ f)
    (h : deriv f = c • f) : f = f 0 • (fun t : ℝ => Complex.exp (c * t)) := by
  have hd : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Complex.exp (-c * s)) (-c * Complex.exp (-c * t)) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => -c * (s : ℂ)) (-c * 1) t :=
      (hasDerivAt_id t).ofReal_comp.const_mul (-c)
    have := h1.cexp
    simpa [mul_comm] using this
  set g : ℝ → ℂ := fun t => Complex.exp (-c * t) * f t with hg
  have hgd : ∀ t, HasDerivAt g 0 t := by
    intro t
    have h2 := (hd t).mul (hf t).hasDerivAt
    have e : deriv f t = c * f t := by
      have := congrFun h t; simpa using this
    rw [e] at h2
    have h3 := h2.congr_deriv (show _ = (0:ℂ) by ring)
    exact h3
  have hgdiff : Differentiable ℝ g := fun t => (hgd t).differentiableAt
  have hc := is_const_of_deriv_eq_zero hgdiff (fun t => (hgd t).deriv)
  funext t
  have h0 := hc t 0
  simp only [hg, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul] at h0
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← h0, mul_comm (Complex.exp _) (f t), mul_assoc, ← Complex.exp_add]
  have e2 : -c * (t : ℂ) + c * t = 0 := by ring
  rw [e2, Complex.exp_zero, mul_one]

theorem expSol_finiteDimensional : ∀ l : List ℂ, FiniteDimensional ℂ (expSol l)
  | [] => by
      have : expSol [] = ⊥ := rfl
      rw [this]; infer_instance
  | c :: l => by
      haveI := expSol_finiteDimensional l
      let φ : expSol (c :: l) →ₗ[ℂ] expSol l :=
        { toFun := fun f => ⟨deriv (f : ℝ → ℂ) - c • (f : ℝ → ℂ), (mem_expSol_cons.1 f.2).2⟩
          map_add' := fun f g => by
            apply Subtype.ext
            have hf := (mem_expSol_cons.1 f.2).1
            have hg := (mem_expSol_cons.1 g.2).1
            funext x
            simp only [Submodule.coe_add, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
            rw [deriv_add (hf x) (hg x)]; ring
          map_smul' := fun k f => by
            apply Subtype.ext
            have hf := (mem_expSol_cons.1 f.2).1
            funext x
            simp only [Submodule.coe_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
              Submodule.coe_smul_of_tower]
            rw [deriv_const_smul k (hf x)]; simp only [smul_eq_mul]; ring }
      have hker : ((LinearMap.ker φ).map (expSol (c :: l)).subtype) ≤
          Submodule.span ℂ {fun t : ℝ => Complex.exp (c * t)} := by
        rintro _ ⟨f, hf, rfl⟩
        have hd := (mem_expSol_cons.1 f.2).1
        have h0 : deriv (f : ℝ → ℂ) - c • (f : ℝ → ℂ) = 0 := by
          have := congrArg Subtype.val (LinearMap.mem_ker.1 hf)
          simpa [φ] using this
        have h1 : deriv (f : ℝ → ℂ) = c • (f : ℝ → ℂ) := sub_eq_zero.1 h0
        rw [Submodule.mem_span_singleton]
        exact ⟨(f : ℝ → ℂ) 0, (eq_smul_exp_of_deriv_eq hd h1).symm⟩
      haveI : FiniteDimensional ℂ ((LinearMap.ker φ).map (expSol (c :: l)).subtype) :=
        Submodule.finiteDimensional_of_le hker
      have hkerFG : (LinearMap.ker φ).FG :=
        Submodule.fg_of_fg_map_injective _ (Submodule.injective_subtype _)
          (Submodule.fg_iff_finiteDimensional _ |>.2 inferInstance)
      have hmapFG : ((⊤ : Submodule ℂ (expSol (c :: l))).map φ).FG :=
        IsNoetherian.noetherian _
      have htop : (⊤ : Submodule ℂ (expSol (c :: l))).FG :=
        Submodule.fg_of_fg_map_of_fg_inf_ker φ hmapFG (by rw [top_inf_eq]; exact hkerFG)
      exact Module.finite_def.2 htop

end GlobalTheory.HCF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExponentialPolynomialSolutionSpaceFiniteDimensioStatement
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exponentialPolynomialSolutionSpace_finiteDimensional : ∀ l : List ℂ, FiniteDimensional ℂ (expSol l) := by
  first | exact @GlobalTheory.HCF.expSol_finiteDimensional | exact GlobalTheory.HCF.expSol_finiteDimensional | (intros; apply GlobalTheory.HCF.expSol_finiteDimensional <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExponentialPolynomialEqZeroOfEqOnIoo
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExponentialPolynomialEqZeroOfEqOnIoo
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology

namespace GlobalTheory.HCF

theorem expSol_eq_zero_of_eqOn_Ioo :
    ∀ (l : List ℂ) (f : ℝ → ℂ), f ∈ expSol l → ∀ s t : ℝ, s < t → (∀ x ∈ Set.Ioo s t, f x = 0) → f = 0 := by
  intro l
  induction l with
  | nil => intro f hf _ _ _ _; exact mem_expSol_nil.1 hf
  | cons c l ih =>
    intro f hf s t hst h0
    rw [mem_expSol_cons] at hf
    obtain ⟨hd, hg⟩ := hf
    have hg0 : deriv f - c • f = 0 := by
      refine ih _ hg s t hst (fun x hx => ?_)
      have hev : f =ᶠ[𝓝 x] (fun _ => (0 : ℂ)) :=
        Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hx) (fun y hy => h0 y hy)
      simp [Pi.sub_apply, hev.deriv_eq, h0 x hx]
    have hder : ∀ x, HasDerivAt f (c * f x) x := by
      intro x
      have h1 := congrFun hg0 x
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1
      have e : deriv f x = c * f x := sub_eq_zero.1 h1
      rw [← e]; exact (hd x).hasDerivAt
    set k : ℝ → ℂ := fun x => Complex.exp (-c * x) * f x with hk
    have hkd : ∀ x, HasDerivAt k 0 x := by
      intro x
      have h1 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := (hasDerivAt_id x).ofReal_comp
      have h2 := ((h1.const_mul (-c)).cexp).mul (hder x)
      have h3 := h2.congr_deriv (show _ = (0 : ℂ) by ring)
      exact h3
    have hkc : ∀ x y, k x = k y := fun x y =>
      is_const_of_deriv_eq_zero (fun z => (hkd z).differentiableAt) (fun z => (hkd z).deriv) x y
    have hm : (s + t) / 2 ∈ Set.Ioo s t := ⟨by linarith, by linarith⟩
    funext x
    have := hkc x ((s + t) / 2)
    simp only [hk, h0 _ hm, mul_zero] at this
    simpa [Complex.exp_ne_zero] using this

end GlobalTheory.HCF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExponentialPolynomialEqZeroOfEqOnIooStatement
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exponentialPolynomial_eq_zero_of_eqOn_Ioo : ∀ (l : List ℂ) (f : ℝ → ℂ), f ∈ expSol l → ∀ s t : ℝ, s < t → (∀ x ∈ Set.Ioo s t, f x = 0) → f = 0 := by
  first | exact @GlobalTheory.HCF.expSol_eq_zero_of_eqOn_Ioo | exact GlobalTheory.HCF.expSol_eq_zero_of_eqOn_Ioo | (intros; apply GlobalTheory.HCF.expSol_eq_zero_of_eqOn_Ioo <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimContinuousNormLeOnIccOfDetermined
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimContinuousNormLeOnIccOfDetermined
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology

namespace GlobalTheory

theorem finiteDim_norm_le_on_Icc_of_determined :
    ∀ (V : Submodule ℂ (ℝ → ℂ)), FiniteDimensional ℂ V → (∀ f ∈ V, Continuous f) → ∀ ℓ : ℝ, 0 < ℓ →
    (∀ f ∈ V, (∀ x ∈ Set.Icc 0 ℓ, f x = 0) → f = 0) → ∀ R : ℝ, ∃ C : ℝ, ∀ f ∈ V, ∀ M : ℝ,
      (∀ x ∈ Set.Icc 0 ℓ, ‖f x‖ ≤ M) → ∀ t ∈ Set.Icc (-R) R, ‖f t‖ ≤ C * M := by
  intro V hV hcont ℓ hℓ hdet R
  let ev : Set.Icc (0:ℝ) ℓ → Module.Dual ℂ V := fun x =>
    (LinearMap.proj (R := ℂ) (φ := fun _ : ℝ => ℂ) (x:ℝ)).comp V.subtype
  obtain ⟨κ, a, -, hspan, hli⟩ := exists_linearIndependent' ℂ ev
  haveI : Finite κ := hli.finite
  letI : Fintype κ := Fintype.ofFinite κ
  classical
  let T : V →ₗ[ℂ] (κ → ℂ) := LinearMap.pi (fun k => ev (a k))
  have hT : LinearMap.ker T = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro g hg
    have h1 : Submodule.span ℂ (Set.range (ev ∘ a)) ≤ LinearMap.ker (Module.Dual.eval ℂ V g) := by
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      have := congrFun hg k
      simpa [T] using this
    rw [hspan] at h1
    have h2 : ∀ x ∈ Set.Icc (0:ℝ) ℓ, (g : ℝ → ℂ) x = 0 := by
      intro x hx
      have := h1 (Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩)
      simpa [ev] using this
    exact Subtype.ext (hdet g g.2 h2)
  obtain ⟨S, hS⟩ := LinearMap.exists_leftInverse_of_injective T hT
  let g : κ → ℝ → ℂ := fun k => (S (Pi.single k 1) : ℝ → ℂ)
  have hB : ∀ k, ∃ B, ∀ t ∈ Set.Icc (-R) R, ‖g k t‖ ≤ B := fun k =>
    (isCompact_Icc).exists_bound_of_continuousOn (hcont _ (S (Pi.single k 1)).2).continuousOn
  choose B hB using hB
  refine ⟨∑ k, max (B k) 0, ?_⟩
  intro f hf M hM t ht
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 ⟨le_rfl, hℓ.le⟩)
  have e : (⟨f, hf⟩ : V) = S (T ⟨f, hf⟩) := (LinearMap.congr_fun hS _).symm
  have e2 : T ⟨f, hf⟩ = ∑ k, (f (a k)) • (Pi.single k 1 : κ → ℂ) := by
    ext j; simp [T, ev, Finset.sum_apply, Pi.single_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e2, map_sum] at e
  have e3 := congrFun (congrArg Subtype.val e) t
  have hft : f t = ∑ k, f (a k) * g k t := by
    simpa [g, Finset.sum_apply] using e3
  rw [hft, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_mul, mul_comm]
  exact mul_le_mul ((hB k t ht).trans (le_max_left _ _)) (hM _ (a k).2) (norm_nonneg _)
    (le_max_right _ _)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimContinuousNormLeOnIccOfDeterminedStatement
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDim_continuous_norm_le_on_Icc_of_determined : ∀ (V : Submodule ℂ (ℝ → ℂ)), FiniteDimensional ℂ V → (∀ f ∈ V, Continuous f) → ∀ ℓ : ℝ, 0 < ℓ →
    (∀ f ∈ V, (∀ x ∈ Set.Icc 0 ℓ, f x = 0) → f = 0) → ∀ R : ℝ, ∃ C : ℝ, ∀ f ∈ V, ∀ M : ℝ,
      (∀ x ∈ Set.Icc 0 ℓ, ‖f x‖ ≤ M) → ∀ t ∈ Set.Icc (-R) R, ‖f t‖ ≤ C * M := by
  first | exact @GlobalTheory.finiteDim_norm_le_on_Icc_of_determined | exact GlobalTheory.finiteDim_norm_le_on_Icc_of_determined | (intros; apply GlobalTheory.finiteDim_norm_le_on_Icc_of_determined <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraFiniteFormsGLSpanKilledScalarDeriva
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraFiniteFormsGLSpanKilledScalarDeriva
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology

namespace GlobalTheory.HCF

theorem span_formsGL_killed_scalD : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E)))
    (W : Submodule ℂ (Kinf E a → ℂ)) (X : Set (Module.End ℂ (Sm E a) → ℂ)), X.Finite → ∀ N : ℕ,
    ∃ Λ : List ℂ, ∀ φ ∈ Submodule.span ℂ (formsGL E a L W X N),
      (Λ.map fun c => scalD E a - algebraMap ℂ (Module.End ℂ (Sm E a)) c).prod φ = 0 := by
  intro E _ _ _ a L W X hX N
  set S : Module.End ℂ (Sm E a) := scalD E a with hS
  set f : ℂ → Module.End ℂ (Sm E a) := fun c => S - algebraMap ℂ (Module.End ℂ (Sm E a)) c with hf
  have hSZ : S ∈ Zalg E a := Central.lie_mem_Zalg 1

  have hpow : ∀ (χ : Module.End ℂ (Sm E a) → ℂ) (φ : Sm E a), CentralNilGL χ N φ → (f (χ S) ^ N) φ = 0 := by
    intro χ φ h
    have key : ∀ n : ℕ, (List.replicate n S).foldr (fun z g => z g - χ z • g) φ = (f (χ S) ^ n) φ := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [List.replicate_succ, List.foldr_cons, ih, pow_succ', Module.End.mul_apply]
        simp [hf, Algebra.algebraMap_eq_smul_one]
    rw [← key]
    exact h _ (List.length_replicate) (fun z hz => by rw [List.eq_of_mem_replicate hz]; exact hSZ)
  have hc : ∀ c d, Commute (f c) (f d) := fun c d =>
    Commute.sub_left (Commute.sub_right (Commute.refl S) (Algebra.commute_algebraMap_right _ _))
      (Commute.sub_right (Algebra.commute_algebraMap_left _ _) (Algebra.commute_algebraMap_left _ _))
  have hcl : ∀ (l : List ℂ) c, Commute (f c) (l.map f).prod := fun l c =>
    Commute.list_prod_right _ _ fun y hy => by
      obtain ⟨d, -, rfl⟩ := List.mem_map.1 hy
      exact hc c d
  let G : (Module.End ℂ (Sm E a) → ℂ) → List ℂ := fun χ => List.replicate N (χ S)
  have main : ∀ (Ls : List (Module.End ℂ (Sm E a) → ℂ)) (φ : Sm E a),
      (∃ χ ∈ Ls, (f (χ S) ^ N) φ = 0) → ((Ls.flatMap G).map f).prod φ = 0 := by
    intro Ls
    induction Ls with
    | nil => intro φ h; simp at h
    | cons χ0 rest ih =>
      intro φ ⟨χ, hχ, h0⟩
      rw [List.flatMap_cons, List.map_append, List.prod_append]
      have hA : ((G χ0).map f).prod = f (χ0 S) ^ N := by
        simp [G, List.map_replicate, List.prod_replicate]
      rcases List.mem_cons.1 hχ with rfl | hr
      · have hcomm : Commute ((G χ).map f).prod ((rest.flatMap G).map f).prod := by
          rw [hA]; exact (hcl _ _).pow_left N
        rw [hcomm.eq, Module.End.mul_apply, hA, h0, map_zero]
      · rw [Module.End.mul_apply, ih φ ⟨χ, hr, h0⟩, map_zero]
  refine ⟨hX.toFinset.toList.flatMap G, fun φ hφ => ?_⟩
  have hsub : formsGL E a L W X N ⊆ (LinearMap.ker ((hX.toFinset.toList.flatMap G).map f).prod : Set (Sm E a)) := by
    intro ψ hψ
    obtain ⟨χ, hχX, hχ⟩ := hψ.2.2.2
    exact LinearMap.mem_ker.2 (main _ ψ ⟨χ, by simpa using hχX, hpow χ ψ hχ⟩)
  exact LinearMap.mem_ker.1 ((Submodule.span_le.2 hsub) hφ)

end GlobalTheory.HCF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraFiniteFormsGLSpanKilledScalarDerivaStatement
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harishChandraFiniteFormsGL_span_killed_scalarDerivative : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E)))
    (W : Submodule ℂ (Kinf E a → ℂ)) (X : Set (Module.End ℂ (Sm E a) → ℂ)), X.Finite → ∀ N : ℕ,
    ∃ Λ : List ℂ, ∀ φ ∈ Submodule.span ℂ (formsGL E a L W X N),
      (Λ.map fun c => scalD E a - algebraMap ℂ (Module.End ℂ (Sm E a)) c).prod φ = 0 := by
  first | exact @GlobalTheory.HCF.span_formsGL_killed_scalD | exact GlobalTheory.HCF.span_formsGL_killed_scalD | (intros; apply GlobalTheory.HCF.span_formsGL_killed_scalD <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormLeSupWiderBandGenCentralEigenforms
noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology

namespace GlobalTheory.HCF

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem hasDerivAt_expCurve (ψ : Sm E a) (g : GA E a) (t : ℝ) :
    HasDerivAt (fun x => ψ.1 (g * expCurve E a x)) ((scalD E a ψ).1 (g * expCurve E a t)) t := by
  have h1 := Central.hasDerivAt_scalar (1 : Cinf E) ψ (g * expCurve E a t)
  have h3 := HasDerivAt.comp_sub_const t t ((sub_self t).symm ▸ h1)
  refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
  have e : expCurve E a x = expCurve E a t * expCurve E a (x - t) := by
    rw [← expCurve_add, add_sub_cancel]
  simp only [Function.comp_apply]
  rw [e, ← mul_assoc]
  rfl

theorem commute_scalD_sub (c c' : ℂ) :
    Commute (scalD E a - algebraMap ℂ (Module.End ℂ (Sm E a)) c) (scalD E a - algebraMap ℂ (Module.End ℂ (Sm E a)) c') :=
  Commute.sub_left ((Commute.refl _).sub_right (Algebra.commute_algebraMap_right c' _))
    (Algebra.commute_algebraMap_left c _)

theorem mem_expSol_of_prod (l : List ℂ) : ∀ (ψ : Sm E a),
    (l.map fun c => scalD E a - algebraMap ℂ (Module.End ℂ (Sm E a)) c).prod ψ = 0 →
    ∀ g : GA E a, (fun x => ψ.1 (g * expCurve E a x)) ∈ expSol l := by
  induction l with
  | nil =>
    intro ψ h g
    simp only [List.map_nil, List.prod_nil, Module.End.one_apply] at h
    subst h
    exact mem_expSol_nil.2 rfl
  | cons c l ih =>
    intro ψ h g
    refine mem_expSol_cons.2 ⟨fun x => (hasDerivAt_expCurve ψ g x).differentiableAt, ?_⟩
    have hc : Commute (scalD E a - algebraMap ℂ (Module.End ℂ (Sm E a)) c)
        (l.map fun c => scalD E a - algebraMap ℂ (Module.End ℂ (Sm E a)) c).prod :=
      Commute.list_prod_right _ _ fun b hb => by
        obtain ⟨c', -, rfl⟩ := List.mem_map.1 hb
        exact commute_scalD_sub c c'
    have h2 : (l.map fun c => scalD E a - algebraMap ℂ (Module.End ℂ (Sm E a)) c).prod
        ((scalD E a - algebraMap ℂ (Module.End ℂ (Sm E a)) c) ψ) = 0 := by
      rw [List.map_cons, List.prod_cons] at h
      rw [← Module.End.mul_apply, ← hc.eq]; exact h
    have h3 := ih _ h2 g
    have e : deriv (fun x => ψ.1 (g * expCurve E a x)) - c • (fun x => ψ.1 (g * expCurve E a x)) =
        fun x => ((scalD E a - algebraMap ℂ (Module.End ℂ (Sm E a)) c) ψ).1 (g * expCurve E a x) := by
      funext x
      simp only [Pi.sub_apply, Pi.smul_apply]
      rw [(hasDerivAt_expCurve ψ g x).deriv]
      simp [Module.algebraMap_end_apply]
    rw [e]; exact h3

theorem norm_le_of_band_wide : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ (N : ℕ) (c : ℝ), 1 ≤ c → ∃ C : ℝ, ∀ φ ∈ Submodule.span ℂ (formsGL E a L W X N), ∀ M : ℝ, (∀ h ∈ band E a, ‖φ.1 h‖ ≤ M) → ∀ g : GA E a, c⁻¹ ≤ absDetA g → absDetA g ≤ 2 * c → ‖φ.1 g‖ ≤ C * M := by
  intro E _ _ _ a L _ W _ X hX N c hc
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · refine ⟨1, fun φ _ M hM g _ _ => ?_⟩
    have e : g = 1 := Units.ext (Subsingleton.elim _ _)
    rw [one_mul]; exact hM g (e ▸ one_mem_band)
  obtain ⟨Λ, hΛ⟩ := GlobalTheory.T.harishChandraFiniteFormsGL_span_killed_scalarDerivative E a L W X hX N
  set κ : ℝ := a * Module.finrank ℚ E with hκ
  have hκ0 : 0 < κ := mul_pos (by exact_mod_cast ha) (by exact_mod_cast Module.finrank_pos)
  set ℓ : ℝ := Real.log 2 / κ
  have hℓ : 0 < ℓ := div_pos (Real.log_pos (by norm_num)) hκ0
  have hvan : ∀ f ∈ expSol Λ, (∀ x ∈ Set.Icc 0 ℓ, f x = 0) → f = 0 := fun f hf h0 =>
    GlobalTheory.T.exponentialPolynomial_eq_zero_of_eqOn_Ioo Λ f hf 0 ℓ hℓ fun x hx => h0 x (Set.Ioo_subset_Icc_self hx)
  have hcont : ∀ f ∈ expSol Λ, Continuous f := by
    intro f hf
    cases Λ with
    | nil => rw [mem_expSol_nil.1 hf]; exact continuous_const
    | cons c l => exact (mem_expSol_cons.1 hf).1.continuous
  obtain ⟨C, hC⟩ := GlobalTheory.T.finiteDim_continuous_norm_le_on_Icc_of_determined (expSol Λ) (GlobalTheory.T.exponentialPolynomialSolutionSpace_finiteDimensional Λ) hcont ℓ hℓ hvan (Real.log (2 * c) / κ)
  refine ⟨C, fun φ hφ M hM g hg1 hg2 => ?_⟩
  have hgpos := absDetA_pos g
  set τ : ℝ := Real.log (absDetA g) / κ
  set g1 := g * expCurve E a (-τ)
  have hdet1 : absDetA g1 = 1 := by
    rw [GlobalTheory.T.adelicAbsDet_mul_archimedeanExpScalarCurve, ← hκ, show -τ * κ = -Real.log (absDetA g) by simp only [τ]; field_simp, Real.exp_neg,
      Real.exp_log hgpos, mul_inv_cancel₀ hgpos.ne']
  have hf := mem_expSol_of_prod Λ φ (hΛ φ hφ) g1
  have hband : ∀ x ∈ Set.Icc 0 ℓ, ‖φ.1 (g1 * expCurve E a x)‖ ≤ M := by
    intro x hx
    refine hM _ ⟨?_, ?_⟩
    · rw [GlobalTheory.T.adelicAbsDet_mul_archimedeanExpScalarCurve, hdet1, one_mul, ← hκ]
      exact Real.one_le_exp (mul_nonneg hx.1 hκ0.le)
    · rw [GlobalTheory.T.adelicAbsDet_mul_archimedeanExpScalarCurve, hdet1, one_mul, ← hκ]
      have : x * κ ≤ Real.log 2 := by
        have := hx.2; simp only [ℓ] at this; rwa [le_div_iff₀ hκ0] at this
      calc Real.exp (x * κ) ≤ Real.exp (Real.log 2) := Real.exp_le_exp.2 this
        _ = 2 := Real.exp_log (by norm_num)
  have hτ : τ ∈ Set.Icc (-(Real.log (2 * c) / κ)) (Real.log (2 * c) / κ) := by
    have hc0 : 0 < c := lt_of_lt_of_le one_pos hc
    have l1 : Real.log (absDetA g) ≤ Real.log (2 * c) := Real.log_le_log hgpos hg2
    have l2 : -Real.log c ≤ Real.log (absDetA g) := by
      rw [← Real.log_inv]; exact Real.log_le_log (inv_pos.2 hc0) hg1
    have l3 : Real.log c ≤ Real.log (2 * c) := Real.log_le_log hc0 (by linarith)
    constructor
    · rw [← neg_div]; exact div_le_div_of_nonneg_right (by linarith) hκ0.le
    · exact div_le_div_of_nonneg_right l1 hκ0.le
  have := hC _ hf M hband τ hτ
  have e : g1 * expCurve E a τ = g := by
    simp only [g1]; rw [mul_assoc, ← expCurve_add, neg_add_cancel, expCurve_zero, mul_one]
  simpa only [e] using this

end GlobalTheory.HCF

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormLeSupWiderBandGenCentralEigenformsStatement
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_le_sup_wider_band_genCentralEigenforms : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ (N : ℕ) (c : ℝ), 1 ≤ c → ∃ C : ℝ, ∀ φ ∈ Submodule.span ℂ (formsGL E a L W X N), ∀ M : ℝ, (∀ h ∈ band E a, ‖φ.1 h‖ ≤ M) → ∀ g : GA E a, c⁻¹ ≤ absDetA g → absDetA g ≤ 2 * c → ‖φ.1 g‖ ≤ C * M := by
  first | exact @GlobalTheory.HCF.norm_le_of_band_wide | exact GlobalTheory.HCF.norm_le_of_band_wide | (intros; apply GlobalTheory.HCF.norm_le_of_band_wide <;> assumption)
end
