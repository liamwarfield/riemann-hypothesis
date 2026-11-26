module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.PiLaws

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.KillsIrreducible
open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace

private lemma fixed_integral {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (ν : Measure α) (Q : E →L[ℂ] E) (f : α → E) (hf : ∀ m, Q (f m) = f m) : Q (∫ m, f m ∂ν) = ∫ m, f m ∂ν := by
  by_cases hi : Integrable f ν
  · rw [← Q.integral_comp_comm hi]
    exact integral_congr_ae (Eventually.of_forall hf)
  · rw [integral_undef hi, map_zero]

private lemma kills_irreducible {G H : Type*} [Group G] [TopologicalSpace G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (π : GroundTheory.Automorphic.UnitaryRep G H) (τ : Submodule ℂ H) (hcl : IsClosed (τ : Set H))
    (hinv : ∀ g, ∀ v ∈ τ, π g v ∈ τ)
    (hirr : ∀ ρ : Submodule ℂ H, ρ ≤ τ → IsClosed (ρ : Set H) → (∀ g, ∀ v ∈ ρ, π g v ∈ ρ) → ρ = ⊥ ∨ ρ = τ)
    (P : H →L[ℂ] H) (v : H) (hv : v ∈ τ) (hv0 : v ≠ 0) (hall : ∀ g, P (π g v) = 0) (u : H) (hu : u ∈ τ) : P u = 0 := by
  let ρ : Submodule ℂ H :=
    { carrier := {x | x ∈ τ ∧ ∀ g, P (π g x) = 0}
      add_mem' := fun {a b} ha hb => ⟨τ.add_mem ha.1 hb.1, fun g => by rw [map_add (f := _), map_add (f := _), ha.2 g, hb.2 g, add_zero]⟩
      zero_mem' := ⟨τ.zero_mem, fun g => by rw [map_zero, map_zero]⟩
      smul_mem' := fun c x hx => ⟨τ.smul_mem c hx.1, fun g => by rw [map_smul, map_smul, hx.2 g, smul_zero]⟩ }
  have hmem : ∀ x, x ∈ ρ ↔ x ∈ τ ∧ ∀ g, P (π g x) = 0 := fun x => Iff.rfl
  have hclρ : IsClosed (ρ : Set H) := by
    have he : (ρ : Set H) = (τ : Set H) ∩ ⋂ g, {x | P (π g x) = 0} := by
      ext x
      simp only [SetLike.mem_coe, hmem, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
    rw [he]
    exact hcl.inter (isClosed_iInter fun g => isClosed_eq (P.continuous.comp (π g).continuous) continuous_const)
  have hinvρ : ∀ g, ∀ x ∈ ρ, π g x ∈ ρ := fun h x hx =>
    (hmem _).2 ⟨hinv h x ((hmem x).1 hx).1, fun g => by
      rw [← GroundTheory.Automorphic.UnitaryRep.map_mul_apply]; exact ((hmem x).1 hx).2 _⟩
  have hvρ : v ∈ ρ := (hmem v).2 ⟨hv, hall⟩
  rcases hirr ρ (fun x hx => ((hmem x).1 hx).1) hclρ hinvρ with h | h
  · exact absurd (by simpa [h] using hvρ) hv0
  · have hu' : u ∈ ρ := h ▸ hu
    have := ((hmem u).1 hu').2 1
    rwa [GroundTheory.Automorphic.UnitaryRep.map_one_apply] at this

private lemma occ_abs {G H A ι α : Type*} [Group G] [TopologicalSpace G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [MeasurableSpace α] (π : GroundTheory.Automorphic.UnitaryRep G H) (ν : Measure α) (gl : ι → A → G)
    (un : ι → α → G) (t : ι → α → ℂ) (P : ι → H →L[ℂ] H) (τ Z : Submodule ℂ H) (hcl : IsClosed (τ : Set H))
    (hinv : ∀ g, ∀ v ∈ τ, π g v ∈ τ)
    (hirr : ∀ ρ : Submodule ℂ H, ρ ≤ τ → IsClosed (ρ : Set H) → (∀ g, ∀ v ∈ ρ, π g v ∈ ρ) → ρ = ⊥ ∨ ρ = τ)
    (hun : ∀ i m, ∃ a, un i m = gl i a) (hcomm : ∀ i j, i ≠ j → ∀ a b, Commute (gl i a) (gl j b))
    (hdec : ∀ i g, ∃ a h, g = gl i a * h ∧ ∀ b, Commute h (gl i b)) (hPP : ∀ i, P i ∘L P i = P i)
    (hPc : ∀ i h, (∀ b, Commute h (gl i b)) → Commute (P i) (π h))
    (hPint : ∀ i v, P i v = ∫ m, t i m • π (un i m) v ∂ν) (hZτ : Z ≤ τ) (hZ : Z ≠ ⊥)
    (hgl : ∀ i a, ∀ v ∈ Z, π (gl i a) v ∈ Z) (hPi : ∀ i, ∀ v ∈ Z, P i v ∈ Z) (hocc : ∀ i, ∃ v ∈ τ, P i v ≠ 0)
    (s : Finset ι) : ∃ v ∈ Z, v ≠ 0 ∧ ∀ i ∈ s, P i v = v := by
  have hsw : ∀ i h, (∀ b, Commute h (gl i b)) → ∀ x, P i (π h x) = π h (P i x) :=
    fun i h hc x => DFunLike.congr_fun (hPc i h hc).eq x
  have key : ∀ i, ∀ v ∈ τ, v ≠ 0 → ∃ a, P i (π (gl i a) v) ≠ 0 := by
    intro i v hv hv0
    by_contra hno
    push_neg at hno
    have hall : ∀ g, P i (π g v) = 0 := by
      intro g
      obtain ⟨a, h, rfl, hc⟩ := hdec i g
      rw [(hc a).eq.symm, GroundTheory.Automorphic.UnitaryRep.map_mul_apply, hsw i h hc, hno a, map_zero]
    obtain ⟨u, hu, hu0⟩ := hocc i
    exact hu0 (kills_irreducible π τ hcl hinv hirr (P i) v hv hv0 hall u hu)
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hZ
    exact ⟨v, hv, hv0, by simp⟩
  | insert i s hi ih =>
    obtain ⟨v, hvZ, hv0, hvs⟩ := ih
    obtain ⟨a, ha⟩ := key i v (hZτ hvZ) hv0
    refine ⟨P i (π (gl i a) v), hPi _ _ (hgl _ _ _ hvZ), ha, ?_⟩
    intro j hj
    rcases Finset.mem_insert.1 hj with rfl | hj
    · exact DFunLike.congr_fun (hPP j) _
    · have hne : i ≠ j := fun h => hi (h ▸ hj)
      have hw : P j (π (gl i a) v) = π (gl i a) v := by
        rw [hsw j _ (fun b => hcomm i j hne a b), hvs j hj]
      rw [hPint i]
      refine fixed_integral ν (P j) _ fun m => ?_
      obtain ⟨c, hc⟩ := hun i m
      rw [map_smul, hc, hsw j _ (fun b => hcomm i j hne c b), hw]

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.occ :
    ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (ι : Type) [Fintype ι] (C : Co K ι) (μ : Measure (G1 K 2)) [μ.IsHaarMeasure] (τ : Submodule ℂ (LL μ)), CuspIrr μ τ → ∀ (Z : Submodule ℂ (LL μ)) (s : Finset ι) (n : ι → ℕ) (q : ι → ℤ), Z ≤ τ → Z ≠ ⊥ → (∀ i a, ∀ v ∈ Z, rightRegularRep (Gam K 2) μ (C.gl i a) v ∈ Z) →
      (∀ i n q, ∀ v ∈ Z, C.Pi μ i n q v ∈ Z) → (∀ i, ∃ v ∈ τ, C.Pi μ i (n i) (q i) v ≠ 0) → ∃ v ∈ Z, v ≠ 0 ∧ ∀ i ∈ s, C.Pi μ i (n i) (q i) v = v := by
  intro K _ _ _ ι _ C μ _ τ hτ Z s n q hZτ hZ hgl hPi hocc
  obtain ⟨-, -, hun, -, -, hcomm, -, hdec, -⟩ := coLaws K ι C
  have hP' : ∀ i, ∃ P : LL μ →L[ℂ] LL μ, (∀ v, P v = C.Pi μ i (n i) (q i) v) ∧ P ∘L P = P ∧
      ∀ h : G1 K 2, (∀ b, Commute h (C.gl i b)) → Commute P (rightRegularRep (Gam K 2) μ h) := fun i => by
    obtain ⟨P, h₁, -, h₂, -, h₃, -⟩ := (piLaws K ι C μ).1 i (n i) (q i)
    exact ⟨P, h₁, h₂, h₃⟩
  choose P hPv hPP hPc using hP'
  obtain ⟨v, hv, hv0, hvs⟩ := occ_abs (rightRegularRep (Gam K 2) μ) μK C.gl C.un (fun i => T (n i) (q i)) P τ Z hτ.closed hτ.inv hτ.irr
    (fun i m => ⟨_, hun i m⟩) hcomm hdec hPP hPc (fun i v => hPv i v) hZτ hZ hgl
    (fun i v hv => by rw [hPv]; exact hPi _ _ _ _ hv) (fun i => by
      obtain ⟨v, hv, h⟩ := hocc i
      exact ⟨v, hv, by rwa [hPv]⟩) s
  exact ⟨v, hv, hv0, fun i hi => by rw [← hPv]; exact hvs i hi⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.ExpInjInt
open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA

private theorem scal_comm (t : ℝ) (a : GL (Fin 2) ℂ) :
    Commute ((kC (tC t t) : GL2C) : GL (Fin 2) ℂ) a := by
  apply Units.ext
  show ((tC t t : U2) : Matrix (Fin 2) (Fin 2) ℂ) * (a : Matrix (Fin 2) (Fin 2) ℂ) =
    (a : Matrix (Fin 2) (Fin 2) ℂ) * ((tC t t : U2) : Matrix (Fin 2) (Fin 2) ℂ)
  have h : ((tC t t : U2) : Matrix (Fin 2) (Fin 2) ℂ) =
      Complex.exp (t * Complex.I) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [coe_tC]; ext r s; fin_cases r <;> fin_cases s <;> simp
  rw [h]; simp

private theorem T_cont (n : ℕ) (q : ℤ) : Continuous (T n q) :=
  continuous_const.mul (KT.continuous_conj_psi n q n)

private theorem T_shift (n : ℕ) (q : ℤ) (t : ℝ) (m : U2) :
    T n q ((tC t t)⁻¹ * m) = Complex.exp (Complex.I * ((((n : ℤ) + 2 * q : ℤ) : ℂ) * t)) * T n q m := by
  have hinv : (tC t t)⁻¹ = tC (-t) (-t) := by
    rw [inv_eq_iff_mul_eq_one]
    apply Subtype.ext
    rw [Matrix.UnitaryGroup.mul_val, coe_tC, coe_tC]
    ext r s; fin_cases r <;> fin_cases s <;> simp [← Complex.exp_add]
  rw [hinv]
  simp only [T]
  rw [KT.psi_tC_mul n q le_rfl, map_mul, ← Complex.exp_conj]
  have h : conj (Complex.I * ((((n : ℝ) + q) * (-t) + ((n : ℝ) - n + q) * (-t) : ℝ) : ℂ)) =
      Complex.I * ((((n : ℤ) + 2 * q : ℤ) : ℂ) * t) := by
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    push_cast
    ring
  rw [h]; ring

private theorem exp_inj_int {a b : ℤ} (h : ∀ t : ℝ, Complex.exp (Complex.I * ((a : ℂ) * t)) =
    Complex.exp (Complex.I * ((b : ℂ) * t))) : a = b := by
  by_contra hab
  have hne : ((a : ℂ) - b) ≠ 0 := by
    rw [sub_ne_zero]; exact_mod_cast hab
  have hne' : ((a : ℝ) - b) ≠ 0 := by
    rw [sub_ne_zero]; exact_mod_cast hab
  have h1 := h (Real.pi / ((a : ℝ) - b))
  have h2 : Complex.exp (Complex.I * ((a : ℂ) * ((Real.pi / ((a : ℝ) - b) : ℝ) : ℂ)) -
      Complex.I * ((b : ℂ) * ((Real.pi / ((a : ℝ) - b) : ℝ) : ℂ))) = 1 := by
    rw [Complex.exp_sub, h1, div_self (Complex.exp_ne_zero _)]
  have h3 : Complex.I * ((a : ℂ) * ((Real.pi / ((a : ℝ) - b) : ℝ) : ℂ)) -
      Complex.I * ((b : ℂ) * ((Real.pi / ((a : ℝ) - b) : ℝ) : ℂ)) = (Real.pi : ℂ) * Complex.I := by
    push_cast
    field_simp
  rw [h3, Complex.exp_pi_mul_I] at h2
  norm_num at h2

section Abstract

variable {G : Type*} [Group G] [TopologicalSpace G] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] (R : UnitaryRep G H) (u : U2 → G)

private theorem eig_abs (hu : ∀ a b, u (a * b) = u a * u b) (hc : Continuous u) (n : ℕ) (q : ℤ) (t : ℝ) (v : H) :
    R (u (tC t t)) (∫ m, T n q m • R (u m) v ∂μK) =
      Complex.exp (Complex.I * ((((n : ℤ) + 2 * q : ℤ) : ℂ) * t)) • ∫ m, T n q m • R (u m) v ∂μK := by
  have hint : Integrable (fun m => T n q m • R (u m) v) μK :=
    KT.integrable_of_continuous ((T_cont n q).smul ((R.continuous_orbit v).comp hc))
  rw [← ContinuousLinearMap.integral_comp_comm _ hint, ← integral_smul,
    ← integral_mul_left_K (fun m => Complex.exp (Complex.I * ((((n : ℤ) + 2 * q : ℤ) : ℂ) * t)) •
      T n q m • R (u m) v) (tC t t)]
  congr 1
  funext m
  have h := T_shift n q t (tC t t * m)
  rw [inv_mul_cancel_left] at h
  rw [map_smul, ← UnitaryRep.map_mul_apply, ← hu, smul_smul, ← h]

private theorem occ_abs (hu : ∀ a b, u (a * b) = u a * u b) (hc : Continuous u)
    (hz : ∀ t g, Commute (u (tC t t)) g) (τ : Submodule ℂ H) (hcl : IsClosed (τ : Set H))
    (hinv : ∀ g, ∀ v ∈ τ, R g v ∈ τ)
    (hirr : ∀ ρ : Submodule ℂ H, ρ ≤ τ → IsClosed (ρ : Set H) → (∀ g, ∀ v ∈ ρ, R g v ∈ ρ) → ρ = ⊥ ∨ ρ = τ)
    {n n' : ℕ} {q q' : ℤ} {w w' : H} (hw : w ∈ τ) (hw' : w' ∈ τ) (hw0 : w ≠ 0) (hw0' : w' ≠ 0)
    (e : ∀ t : ℝ, R (u (tC t t)) w = Complex.exp (Complex.I * ((((n : ℤ) + 2 * q : ℤ) : ℂ) * t)) • w)
    (e' : ∀ t : ℝ, R (u (tC t t)) w' = Complex.exp (Complex.I * ((((n' : ℤ) + 2 * q' : ℤ) : ℂ) * t)) • w') :
    (n' : ℤ) + 2 * q' = n + 2 * q := by
  let c : ℝ → ℂ := fun t => Complex.exp (Complex.I * ((((n : ℤ) + 2 * q : ℤ) : ℂ) * t))
  let ρ : Submodule ℂ H :=
    { carrier := {x | x ∈ τ ∧ ∀ t : ℝ, R (u (tC t t)) x = c t • x}
      add_mem' := fun {x y} hx hy => ⟨τ.add_mem hx.1 hy.1, fun t => by rw [map_add (f := _), hx.2, hy.2, smul_add]⟩
      zero_mem' := ⟨τ.zero_mem, fun t => by simp⟩
      smul_mem' := fun a x hx => ⟨τ.smul_mem a hx.1, fun t => by rw [map_smul, hx.2, smul_comm]⟩ }
  have hρτ : ρ ≤ τ := fun x hx => hx.1
  have hρcl : IsClosed (ρ : Set H) := by
    have e₀ : (ρ : Set H) = (τ : Set H) ∩ ⋂ t : ℝ, {x | R (u (tC t t)) x = c t • x} := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
      rfl
    rw [e₀]
    exact hcl.inter (isClosed_iInter fun t =>
      isClosed_eq (ContinuousLinearMap.continuous _) (continuous_const_smul _))
  have hρinv : ∀ g, ∀ x ∈ ρ, R g x ∈ ρ := by
    intro g x hx
    refine ⟨hinv g x hx.1, fun t => ?_⟩
    rw [← UnitaryRep.map_mul_apply, (hz t g).eq, UnitaryRep.map_mul_apply, hx.2, map_smul]
  have hwρ : w ∈ ρ := ⟨hw, e⟩
  rcases hirr ρ hρτ hρcl hρinv with h0 | h1
  · rw [h0] at hwρ
    exact absurd ((Submodule.mem_bot ℂ).1 hwρ) hw0
  · have hwρ' : w' ∈ ρ := h1 ▸ hw'
    refine exp_inj_int fun t => ?_
    have e1 := hwρ'.2 t
    rw [e' t] at e1
    exact smul_left_injective ℂ hw0' e1

end Abstract

section

variable {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] {ι : Type} [Fintype ι] (C : Co K ι)

private theorem un_central (i : ι) (t : ℝ) (g : G1 K 2) : Commute (C.un i (tC t t)) g := by
  obtain ⟨-, -, hun, -, hmul, -, -, hdec, -⟩ := UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.coLaws K ι C
  obtain ⟨a, h, rfl, hh⟩ := hdec i g
  rw [hun]
  refine Commute.mul_right ?_ (hh _).symm
  show _ * _ = _ * _
  rw [← hmul, ← hmul, (scal_comm t a).eq]

private theorem un_mul (i : ι) (a b : U2) : C.un i (a * b) = C.un i a * C.un i b := by
  obtain ⟨-, -, hun, -, hmul, -⟩ := UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.coLaws K ι C
  rw [hun, hun, hun, map_mul]
  exact hmul i _ _

private theorem un_cont (i : ι) : Continuous (C.un i) := by
  obtain ⟨-, -, hun, hc, -⟩ := UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.coLaws K ι C
  have h : C.un i = fun m => C.gl i (kC m : GL2C) := funext (hun i)
  rw [h]
  exact (hc i).comp (continuous_subtype_val.comp continuous_kC)

end

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.minEx :
    ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (ι : Type) [Fintype ι] (C : Co K ι) (μ : Measure (G1 K 2)) [μ.IsHaarMeasure] (τ : Submodule ℂ (LL μ)), CuspIrr μ τ → ∀ i, ∃ n q, C.MinAt μ τ i n q := by
  intro K _ _ _ ι _ C μ _ τ hτ i
  obtain ⟨hP, -, -, hall⟩ := UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.piLaws K ι C μ
  have hmem : ∀ (n : ℕ) (q : ℤ) (v : LL μ), v ∈ τ → C.Pi μ i n q v ∈ τ := by
    intro n q v hv
    obtain ⟨P, h1, -, -, -, -, h2⟩ := hP i n q
    rw [← h1]
    exact h2 τ hτ v hv
  have heig : ∀ (n : ℕ) (q : ℤ) (v : LL μ) (t : ℝ), rightRegularRep (Gam K 2) μ (C.un i (tC t t)) (C.Pi μ i n q v) =
      Complex.exp (Complex.I * ((((n : ℤ) + 2 * q : ℤ) : ℂ) * t)) • C.Pi μ i n q v := fun n q v t =>
    eig_abs (rightRegularRep (Gam K 2) μ) (C.un i) (un_mul C i) (un_cont C i) n q t v
  have hex : ∃ n : ℕ, ∃ (q : ℤ) (v : LL μ), v ∈ τ ∧ C.Pi μ i n q v ≠ 0 := by
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hτ.ne
    by_contra hno
    push_neg at hno
    exact hv0 (hall i v fun n q g => hno n q _ (hτ.inv g v hv))
  obtain ⟨q, v, hv, hne⟩ := Nat.find_spec hex
  refine ⟨Nat.find hex, q, ⟨v, hv, hne⟩, fun n' q' hab w hw => ?_⟩
  by_contra hw0
  exact hab ⟨Nat.find_min' hex ⟨q', w, hw, hw0⟩,
    occ_abs (rightRegularRep (Gam K 2) μ) (C.un i) (un_mul C i) (un_cont C i) (un_central C i) τ hτ.closed hτ.inv hτ.irr
      (hmem _ _ _ hv) (hmem _ _ _ hw) hne hw0 (heig _ _ _) (heig _ _ _)⟩
end
