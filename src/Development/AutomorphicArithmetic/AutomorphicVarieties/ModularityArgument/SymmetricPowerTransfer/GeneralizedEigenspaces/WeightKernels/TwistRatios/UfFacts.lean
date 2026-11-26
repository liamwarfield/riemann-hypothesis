module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.GoodSet

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.UfFacts
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem UpperTheory.V.Z.Sym.Ga.det_ne {k : Type} [Field k] (g : GL (Fin 2) k) :
    (g : Matrix (Fin 2) (Fin 2) k).det ≠ 0 :=
  (Matrix.isUnits_det_units g).ne_zero

private theorem UpperTheory.V.Z.Sym.Ga.det_inv {k : Type} [Field k] (g : GL (Fin 2) k) :
    ((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).det = ((g : Matrix (Fin 2) (Fin 2) k).det)⁻¹ := by
  have h : ((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) * (g : Matrix (Fin 2) (Fin 2) k) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h2 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_one] at h2
  exact eq_inv_of_mul_eq_one_left h2

private theorem UpperTheory.V.Z.Sym.Ga.trace_inv {k : Type} [Field k] (g : GL (Fin 2) k) :
    ((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).trace =
      (g : Matrix (Fin 2) (Fin 2) k).trace / (g : Matrix (Fin 2) (Fin 2) k).det := by
  rw [Matrix.coe_units_inv, Matrix.inv_def, Matrix.adjugate_fin_two, Ring.inverse_eq_inv', Matrix.trace_smul,
    Matrix.trace_fin_two, Matrix.trace_fin_two]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    smul_eq_mul]
  rw [div_eq_inv_mul, add_comm]

theorem UpperTheory.V.Z.Sym.Ga.ufFacts :
    ∀ (k : Type) [Field k] (g : GL (Fin 2) k), (∀ a b : kˣ, (g : Matrix (Fin 2) (Fin 2) k).charpoly = (X - C (a : k)) * (X - C (b : k)) → Ga.uf g = (a / b : kˣ) + ((a / b : kˣ)⁻¹ : kˣ)) ∧ Ga.uf g⁻¹ = Ga.uf g ∧ (∀ x : GL (Fin 2) k, Ga.uf (x * g * x⁻¹) = Ga.uf g) ∧ (∀ (g' P : GL (Fin 2) k) (μ : kˣ), (g : Matrix (Fin 2) (Fin 2) k)ᵀ * (P : Matrix (Fin 2) (Fin 2) k) * (g' : Matrix (Fin 2) (Fin 2) k) = (μ : k) • (P : Matrix (Fin 2) (Fin 2) k) → Ga.uf g' = Ga.uf g) ∧ ∀ (Γ : Type) [Group Γ] (ρ : Γ →* GL (Fin 2) k) (s : Γ), Ga.tr (ad0 ρ s) = Ga.uf (ρ s) + 1 := by
  intro k _ g
  have hd := Ga.det_ne g
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a b h
    have h' := h
    rw [Matrix.charpoly_fin_two] at h'
    have e0 := congrArg (Polynomial.eval 0) h'
    have e1 := congrArg (Polynomial.eval 1) h'
    simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at e0 e1
    have hdet : (g : Matrix (Fin 2) (Fin 2) k).det = a * b := by linear_combination e0
    have htr : (g : Matrix (Fin 2) (Fin 2) k).trace = a + b := by linear_combination e0 - e1
    have ha : (a : k) ≠ 0 := a.ne_zero
    have hb : (b : k) ≠ 0 := b.ne_zero
    simp only [Ga.uf, Ga.tr]
    rw [htr, hdet, Units.val_inv_eq_inv_val, Units.val_div_eq_div_val]
    field_simp
    ring
  · simp only [Ga.uf, Ga.tr]
    rw [Ga.trace_inv, Ga.det_inv]
    field_simp
  · intro x
    have hx : ((x⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) * (x : Matrix (Fin 2) (Fin 2) k) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have ht : ((x * g * x⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).trace = (g : Matrix (Fin 2) (Fin 2) k).trace := by
      rw [Units.val_mul, Units.val_mul, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hx, Matrix.one_mul]
    have hdt : ((x * g * x⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).det = (g : Matrix (Fin 2) (Fin 2) k).det := by
      rw [Units.val_mul, Units.val_mul, Matrix.det_mul, mul_comm, Matrix.det_mul, ← mul_assoc, ← Matrix.det_mul, hx,
        Matrix.det_one, one_mul]
    simp only [Ga.uf, Ga.tr]
    rw [ht, hdt]
  · intro g' P μ h
    have hμ : (μ : k) ≠ 0 := μ.ne_zero
    have hP := Ga.det_ne P
    have hPi : (P : Matrix (Fin 2) (Fin 2) k) * ((P⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hPi' : ((P⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) * (P : Matrix (Fin 2) (Fin 2) k) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hg : ((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)ᵀ * (g : Matrix (Fin 2) (Fin 2) k)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one]
    have hform : (g' : Matrix (Fin 2) (Fin 2) k) = (μ : k) • (((P⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) *
        ((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)ᵀ * (P : Matrix (Fin 2) (Fin 2) k)) := by
      have e := congrArg (fun M => ((P⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) *
        ((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)ᵀ * M) h
      rw [Matrix.mul_smul] at e
      rw [← e]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)ᵀ) ((g : Matrix (Fin 2) (Fin 2) k)ᵀ), hg,
        Matrix.one_mul, ← Matrix.mul_assoc, hPi', Matrix.one_mul]
    have htr : (g' : Matrix (Fin 2) (Fin 2) k).trace =
        μ * ((g : Matrix (Fin 2) (Fin 2) k).trace / (g : Matrix (Fin 2) (Fin 2) k).det) := by
      rw [hform, Matrix.trace_smul, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hPi, Matrix.one_mul,
        Matrix.trace_transpose, Ga.trace_inv, smul_eq_mul]
    have hdt : (g' : Matrix (Fin 2) (Fin 2) k).det = μ ^ 2 / (g : Matrix (Fin 2) (Fin 2) k).det := by
      have e := congrArg Matrix.det h
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul, Fintype.card_fin] at e
      field_simp
      have : (P : Matrix (Fin 2) (Fin 2) k).det * ((g' : Matrix (Fin 2) (Fin 2) k).det * (g : Matrix (Fin 2) (Fin 2) k).det) =
          (P : Matrix (Fin 2) (Fin 2) k).det * (μ : k) ^ 2 := by linear_combination e
      exact mul_left_cancel₀ hP this
    simp only [Ga.uf, Ga.tr]
    rw [htr, hdt]
    field_simp
  · intro Γ _ ρ s
    have hd' := Ga.det_ne (ρ s)
    have e : (ad0 ρ s : Matrix (Fin 3) (Fin 3) k) =
        (((ρ s : Matrix (Fin 2) (Fin 2) k).det)⁻¹) • symSquareMatrixHom k (ρ s : Matrix (Fin 2) (Fin 2) k) := by
      rw [ad0, tw_val]
      simp [Matrix.GeneralLinearGroup.det]
    simp only [Ga.tr, Ga.uf]
    rw [e, Matrix.trace_smul, Matrix.trace_fin_two, Matrix.trace_fin_three]
    have hd2 := hd'
    rw [Matrix.det_fin_two] at hd2 ⊢
    simp [symSquareMatrixHom]
    field_simp
    ring
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.EpsAway
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.Ga

private theorem cyc_eq_of_pow {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 L)} (hl : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal)
    (h : IsPlaceOver A w) {σ : G L Ω} {q : ℕ}
    (hσ : ∀ x, A.valuation x ≤ 1 → A.valuation (σ x - x ^ q) < 1) :
    (cycBar L Ω l σ : Qbar l) = (q : Qbar l) := by
  have h1 : ((cycZ L Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) = (q : ℤ_[l]) :=
    PadicInt.ext_of_toZModPow.mp (cycZ_toZModPow_eq hl h hσ)
  simp [cycBar, h1]

end UpperTheory.V.Z.Sym.Ga

theorem UpperTheory.V.Z.Sym.Ga.epsAway :
    Af.Hypotheses₂ → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (w : Plc L), ((l : ℕ) : 𝓞 L) ∉ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion L)ˣ), IsLocalArtin h a → ∀ s : Weil h, ι (Ga.ep l (s : G L Ω)) = (absPow (w.adicCompletion L) 1 (a s) : ℂ) ∧ ι (Ga.ep l (s : G L Ω)) = ((normV w : ℕ) : ℂ) ^ deg s := by
  intro _ L Ω _ _ _ _ _ l _ ι w hl A h a ha s
  have hfrob : (cycBar L Ω l ((frob h : Weil h) : G L Ω) : Qbar l) = ((normV w : ℕ) : Qbar l) :=
    Ga.cyc_eq_of_pow hl h (isFrob_frob (h := h)).2
  set t : Weil h := s * (frob h) ^ (-deg s) with ht
  have hdt : deg t = 0 := by
    rw [ht, deg_mul, deg_zpow, deg_frob]
    ring
  have hI : (t : G L Ω) ∈ Ine (F := L) A :=
    actsAs_zero_iff.1 (actsAs_of_deg (a := 0) (b := 0) (by simpa using hdt))
  have hine : (cycBar L Ω l (t : G L Ω) : Qbar l) = 1 := by
    have := Ga.cyc_eq_of_pow (σ := (t : G L Ω)) (q := 1) hl h (fun x hx => by simpa using hI.2 x hx)
    simpa using this
  have hs : s = t * (frob h) ^ (deg s) := by
    rw [ht, mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
  have hε : Ga.ep l (s : G L Ω) = ((normV w : ℕ) : Qbar l) ^ deg s := by
    show (cycBar L Ω l (s : G L Ω) : Qbar l) = _
    conv_lhs => rw [hs]
    rw [Subgroup.coe_mul, map_mul, Units.val_mul, hine, one_mul, Subgroup.coe_zpow, map_zpow,
      Units.val_zpow_eq_zpow_val, hfrob]
  have hq : ι (Ga.ep l (s : G L Ω)) = ((normV w : ℕ) : ℂ) ^ deg s := by
    rw [hε, map_zpow₀, map_natCast]
  refine ⟨?_, hq⟩
  have := DFunLike.congr_fun (ha.absPow_comp 1) s
  rw [Complex.ofReal_one] at this
  rw [hq, ← MonoidHom.comp_apply, this, GlobalTheory.WeilDeligne.unrChar_apply, Units.val_zpow_eq_zpow_val]
  simp
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.BadClosed
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Sym.Ga.badClosed :
    ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (r : G L Ω →* GL (Fin 2) (Qbar l)), Continuous r → (Continuous fun g => Ga.uf (r g)) ∧ (Continuous fun g : G L Ω => Ga.ep l g) ∧ IsClosed (Ga.Bad r) := by
  intro L Ω _ _ _ _ _ l _ r hr
  have hm : Continuous fun g => ((r g : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) :=
    Units.continuous_val.comp hr
  have hU : Continuous fun g => Ga.uf (r g) := by
    unfold Ga.uf Ga.tr
    refine ((hm.matrix_trace.pow 2).div hm.matrix_det fun g => ?_).sub continuous_const
    exact (Matrix.isUnits_det_units (r g)).ne_zero
  have hE : Continuous fun g : G L Ω => Ga.ep l g := by
    have hu : Continuous fun g : G L Ω => ((cycZ L Ω l g : ℤ_[l]ˣ) : ℤ_[l]) :=
      (Units.continuous_val (M := ℤ_[l])).comp (continuous_cycZ L Ω l)
    have hz : Continuous fun g : G L Ω => (((cycZ L Ω l g : ℤ_[l]) : ℚ_[l])) :=
      continuous_subtype_val.comp hu
    have h := (continuous_algebraMap ℚ_[l] (Qbar l)).comp hz
    convert h using 1
    funext g
    rfl
  have hne : ∀ g : G L Ω, Ga.ep l g ≠ 0 := fun g => (cycBar L Ω l g).ne_zero
  refine ⟨hU, hE, ?_⟩
  have hset : Ga.Bad r = ⋃ m ∈ Finset.Icc (-2 : ℤ) 2,
      {g | Ga.uf (r g) ^ 2 - 2 = Ga.ep l g ^ m + Ga.ep l g ^ (-m)} := by
    ext g
    simp only [Ga.Bad, Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_Icc, exists_prop, abs_le]
  rw [hset]
  refine isClosed_biUnion_finset fun m _ => isClosed_eq ((hU.pow 2).sub continuous_const) ?_
  exact (hE.zpow₀ m fun g => Or.inl (hne g)).add (hE.zpow₀ (-m) fun g => Or.inl (hne g))
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.IneInf
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem ine_of_emb {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [Algebra ℚ Ω]
    [IsScalarTower ℚ L Ω] (A : ValuationSubring Ω) (s : G L Ω)
    (h : Base.galEmb ℚ L Ω s ∈ Ine (F := ℚ) A) : s ∈ Ine (F := L) A := h

theorem UpperTheory.V.Z.Sym.Ga.ineInf :
    ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), A.valuation (l : Ω) < 1 → ∀ H : Subgroup (G L Ω), IsOpen (H : Set (G L Ω)) → ∃ s ∈ H, s ∈ Ine (F := L) A ∧ ¬ IsOfFinOrder (cycBar L Ω l s) := by
  intro L Ω _ _ _ _ _ l _ A hA H hH
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap L Ω).injective
  haveI : IsScalarTower ℚ L Ω := inferInstance
  haveI : Algebra.IsAlgebraic L Ω := IsAlgClosure.isAlgebraic
  haveI : IsAlgClosure ℚ Ω := ⟨IsAlgClosure.isAlgClosed L, Algebra.IsAlgebraic.trans ℚ L Ω⟩
  haveI : IsGalois L Ω := IsAlgClosure.isGalois L Ω
  haveI : Finite (G L Ω ⧸ H) := H.quotient_finite_of_isOpen hH
  obtain ⟨hemb, -, hidx⟩ := Base.galEmbTop ℚ L Ω
  have hrange : (Base.galEmb ℚ L Ω).range = Base.galOf ℚ L Ω := by
    apply le_antisymm
    · rintro _ ⟨s, rfl⟩
      exact Base.galEmb_mem ℚ L Ω s
    · intro σ hσ
      refine ⟨{ σ.toRingEquiv with commutes' := fun x => hσ x }, ?_⟩
      ext x
      rw [Base.galEmb_apply]
      rfl
  have hfin : (H.map (Base.galEmb ℚ L Ω)).index ≠ 0 := by
    rw [H.index_map_of_injective hemb.injective, hrange, hidx]
    exact mul_ne_zero Subgroup.index_ne_zero_of_finite Module.finrank_pos.ne'
  haveI : (H.map (Base.galEmb ℚ L Ω)).FiniteIndex := ⟨hfin⟩
  have hu : IsUnit ((1 : ℤ_[l]) + l) := by
    by_contra h
    have h1 : (l : ℤ_[l]) ∣ 1 + l :=
      (PadicInt.norm_lt_one_iff_dvd _).mp (PadicInt.mem_nonunits.mp (mem_nonunits_iff.mpr h))
    have hl : IsUnit (l : ℤ_[l]) := isUnit_of_dvd_one ((dvd_add_left (dvd_refl _)).mp h1)
    have h2 : ‖(l : ℤ_[l])‖ < 1 := (PadicInt.norm_lt_one_iff_dvd _).mpr (dvd_refl _)
    rw [PadicInt.isUnit_iff.mp hl] at h2
    exact lt_irrefl _ h2
  have hv : ¬ IsOfFinOrder hu.unit := by
    intro hv
    obtain ⟨n, hn, hpow⟩ := hv.exists_pow_eq_one
    have h2 : ((1 : ℤ_[l]) + l) ^ n = 1 := by
      have := congrArg Units.val hpow
      simpa using this
    have h3 : ((1 + l) ^ n : ℕ) = 1 := by
      exact_mod_cast h2
    rcases Nat.pow_eq_one.mp h3 with h4 | h4
    · have := (Fact.out : l.Prime).pos
      omega
    · omega
  obtain ⟨τ, hτ, hτv⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hA hu.unit
  have hpow : τ ^ (H.map (Base.galEmb ℚ L Ω)).normalCore.index ∈ H.map (Base.galEmb ℚ L Ω) :=
    Subgroup.normalCore_le _ (Subgroup.pow_index_mem _ τ)
  obtain ⟨s, hs, hsτ⟩ := hpow
  have hsI : Base.galEmb ℚ L Ω s ∈ Ine (F := ℚ) A := by
    rw [hsτ]
    exact Subgroup.pow_mem _ hτ _
  refine ⟨s, hs, ine_of_emb A s hsI, ?_⟩
  have hcyc : cycZ L Ω l s = cycZ ℚ Ω l (Base.galEmb ℚ L Ω s) := by
    simp only [cycZ, MonoidHom.comp_apply]
    congr 1
  have hinj : Function.Injective ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom) :=
    (algebraMap ℚ_[l] (Qbar l)).injective.comp Subtype.val_injective
  have hmap : Function.Injective (Units.map ((algebraMap ℚ_[l] (Qbar l)).comp
      PadicInt.Coe.ringHom : ℤ_[l] →* Qbar l)) := by
    intro a b hab
    exact Units.ext (hinj (congrArg Units.val hab))
  intro hfo
  have hval : cycBar L Ω l s = Units.map ((algebraMap ℚ_[l] (Qbar l)).comp
      PadicInt.Coe.ringHom : ℤ_[l] →* Qbar l) (hu.unit ^ (H.map (Base.galEmb ℚ L Ω)).normalCore.index) := by
    simp only [cycBar, MonoidHom.comp_apply, hcyc, hsτ, map_pow, hτv]
    rfl
  rw [hval, ← orderOf_pos_iff, orderOf_injective _ hmap, orderOf_pos_iff, isOfFinOrder_pow] at hfo
  rcases hfo with h | h
  · exact hv h
  · exact Subgroup.FiniteIndex.index_ne_zero h
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.Coset
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Sym.Ga.coset :
    ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] (V : Set Γ), IsOpen V → ∀ g ∈ V, ∃ H : Subgroup Γ, H.Normal ∧ IsOpen (H : Set Γ) ∧ ∀ h ∈ H, g * h ∈ V := by
  intro Γ _ _ _ _ _ V hV g hg
  have hU : IsOpen ((fun x : Γ => g * x) ⁻¹' V) := hV.preimage (continuous_const_mul g)
  have h1 : (1 : Γ) ∈ (fun x : Γ => g * x) ⁻¹' V := by simpa using hg
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hU h1
  exact ⟨H.toSubgroup, H.isNormal', H.isOpen', fun h hh => hH hh⟩
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.TrPair
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Sym.Ga.trPair :
    ∀ (k : Type) [Field k] (n : ℕ) (g g' P : GL (Fin n) k) (μ : kˣ), (g : Matrix (Fin n) (Fin n) k)ᵀ * (P : Matrix (Fin n) (Fin n) k) * (g' : Matrix (Fin n) (Fin n) k) = (μ : k) • (P : Matrix (Fin n) (Fin n) k) → Ga.tr g' = μ * Ga.tr g⁻¹ := by
  intro k _ n g g' P μ h
  set A : Matrix (Fin n) (Fin n) k := (g : Matrix (Fin n) (Fin n) k)
  set Ai : Matrix (Fin n) (Fin n) k := ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)
  set B : Matrix (Fin n) (Fin n) k := (g' : Matrix (Fin n) (Fin n) k)
  set M : Matrix (Fin n) (Fin n) k := (P : Matrix (Fin n) (Fin n) k)
  set Mi : Matrix (Fin n) (Fin n) k := ((P⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)
  have hA : A * Ai = 1 := g.mul_inv
  have hM : Mi * M = 1 := P.inv_mul
  have hM' : M * Mi = 1 := P.mul_inv
  have hB : B = Mi * Aiᵀ * (Aᵀ * M * B) := by
    have : Aiᵀ * Aᵀ = 1 := by rw [← Matrix.transpose_mul, hA, Matrix.transpose_one]
    calc B = Mi * M * B := by rw [hM, Matrix.one_mul]
      _ = Mi * (Aiᵀ * Aᵀ) * M * B := by rw [this, Matrix.mul_one]
      _ = Mi * Aiᵀ * (Aᵀ * M * B) := by simp only [Matrix.mul_assoc]
  show B.trace = μ * Ai.trace
  rw [hB, h, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    hM', Matrix.one_mul, Matrix.trace_transpose]
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.WtOf
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem infOfWeight_reflect_eq_weights (lam : DomWeight 2) : (infOfWeight lam).map (fun z => (((2 : ℕ) : ℂ) - 1) / 2 - z) = ({-lam.w 0, 1 - lam.w 1} : Multiset ℤ).map (fun k : ℤ => (k : ℂ)) := by
  simp only [infOfWeight, Multiset.map_map, Function.comp_def, Fin.univ_val_map]
  simp [List.ofFn_succ]
  rw [← Multiset.cons_coe, Multiset.coe_singleton]
  congr 2
  ring

theorem UpperTheory.V.Z.Sym.Ga.wtOf :
    ∀ (m : ℕ) (b : ℤ) (lam : DomWeight 2), ({b, b + m} : Multiset ℤ).map (fun k : ℤ => (k : ℂ)) = (infOfWeight lam).map (fun z => (((2 : ℕ) : ℂ) - 1) / 2 - z) → lam.w 0 - lam.w 1 = (m : ℤ) - 1 := by
  intro m b lam h
  rw [infOfWeight_reflect_eq_weights] at h
  have hz : ({b, b + m} : Multiset ℤ) = {-lam.w 0, 1 - lam.w 1} :=
    Multiset.map_injective Int.cast_injective h
  have hanti : lam.w 1 ≤ lam.w 0 := lam.anti (by decide)
  have hs := congrArg Multiset.sum hz
  simp at hs
  have hb : b ∈ ({-lam.w 0, 1 - lam.w 1} : Multiset ℤ) := by
    rw [← hz]; simp
  simp at hb
  rcases hb with hb | hb <;> omega
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.Select
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Sym.Ga.select :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (X : Set (Plc L)), ∃ P ⊆ X, Set.InjOn (fun w : Plc L => w.under (𝓞 (Lp L))) P ∧ ∀ w ∈ X, ∃ w' ∈ P, w'.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L)) := by
  intro L _ _ _ X
  rcases isEmpty_or_nonempty (Plc L) with hE | hN
  · refine ⟨∅, Set.empty_subset _, Set.injOn_empty _, ?_⟩
    intro w
    exact (IsEmpty.false w).elim
  set f : Plc L → _ := fun w : Plc L => w.under (𝓞 (Lp L)) with hf
  have spec : ∀ w ∈ X, Classical.epsilon (fun v => v ∈ X ∧ f v = f w) ∈ X ∧
      f (Classical.epsilon (fun v => v ∈ X ∧ f v = f w)) = f w :=
    fun w hw => Classical.epsilon_spec (p := fun v => v ∈ X ∧ f v = f w) ⟨w, hw, rfl⟩
  refine ⟨(fun w => Classical.epsilon (fun v => v ∈ X ∧ f v = f w)) '' X, ?_, ?_, ?_⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact (spec w hw).1
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
    have hab' : f a = f b := by
      have := hab
      simp only at this
      rw [(spec a ha).2, (spec b hb).2] at this
      exact this
    simp only [hab']
  · intro w hw
    exact ⟨_, ⟨w, hw, rfl⟩, (spec w hw).2⟩
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.AutIso
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.Ga.AutomorphyInvariantUnderRepIso

section Rep

variable {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {r r' : Γ →* GL (Fin n) k}

private theorem act_conj (g : GL (Fin n) k) (hg : ∀ s, r' s = g * r s * g⁻¹) (s : Γ) (v : Fin n → k) :
    (r' s : Matrix (Fin n) (Fin n) k) *ᵥ ((g : Matrix (Fin n) (Fin n) k) *ᵥ v) =
      (g : Matrix (Fin n) (Fin n) k) *ᵥ ((r s : Matrix (Fin n) (Fin n) k) *ᵥ v) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul, hg]
  congr 2
  group

private theorem ss_iso (h : RepIso r r') (hr : IsSSRep r) : IsSSRep r' := by
  obtain ⟨g, hg⟩ := h
  refine GlobalTheory.LatticeComplement.isSSRep_of_intertwine r r' (g : Matrix (Fin n) (Fin n) k)
    ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) (Units.mul_inv g) (fun s => ?_) hr
  rw [hg s, ← Units.val_mul, ← Units.val_mul]
  congr 1
  group

private theorem irr_iso (h : RepIso r r') (hr : IsIrr r) : IsIrr r' := by
  obtain ⟨g, hg⟩ := h
  refine ⟨hr.1, fun _ _ _ => Submodule.mem_top, fun W _ hW => ?_⟩
  let e : (Fin n → k) ≃ₗ[k] (Fin n → k) := (Matrix.GeneralLinearGroup.toLin g).toLinearEquiv
  have he : ∀ v, e v = (g : Matrix (Fin n) (Fin n) k) *ᵥ v := fun _ => rfl
  have hinv := hr.2.2 (W.comap (e : (Fin n → k) →ₗ[k] (Fin n → k))) le_top (fun s v hv => by
    change e _ ∈ W
    have h1 : e v ∈ W := hv
    rw [he] at h1 ⊢
    rw [← act_conj g hg]
    exact hW s _ h1)
  have hW' : W = (W.comap (e : (Fin n → k) →ₗ[k] (Fin n → k))).map (e : (Fin n → k) →ₗ[k] (Fin n → k)) :=
    (Submodule.map_comap_eq_of_surjective e.surjective W).symm
  rcases hinv with h0 | h0
  · left
    rw [hW', h0, Submodule.map_bot]
  · right
    rw [hW', h0, Submodule.map_top, LinearEquiv.range]

private theorem tw_iso (χ : Γ →* kˣ) (h : RepIso r r') : RepIso (tw r χ) (tw r' χ) := by
  obtain ⟨g, hg⟩ := h
  refine ⟨g, fun s => Units.ext ?_⟩
  simp only [Units.val_mul, tw_val, hg s, Matrix.mul_smul, Matrix.smul_mul]

private theorem comp_iso {Γ' : Type} [Group Γ'] (φ : Γ' →* Γ) (h : RepIso r r') : RepIso (r.comp φ) (r'.comp φ) := by
  obtain ⟨g, hg⟩ := h
  exact ⟨g, fun s => hg (φ s)⟩

end Rep

private theorem att_iso {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
    {ι : Qbar l ≃+* ℂ} {r r' : G F Ω →* GL (Fin n) (Qbar l)} {sat : HeightOneSpectrum (𝓞 F) → Multiset ℂˣ → Prop}
    (h : RepIso r r') (H : AttachedSys ι r sat) : AttachedSys ι r' sat :=
  ⟨ss_iso h H.1, H.2.mono fun _ ⟨B, hB, hB'⟩ => ⟨B, hB, hB'.of_iso h⟩⟩

end UpperTheory.V.Z.Sym.Ga.AutomorphyInvariantUnderRepIso

open UpperTheory.V.Z.Sym.Ga.AutomorphyInvariantUnderRepIso in
theorem UpperTheory.V.Z.Sym.Ga.autIso :
    ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ) (r r' : G L Ω →* GL (Fin n) (Qbar l)), RepIso r r' → (IsAutC ι r → IsAutC ι r') ∧ (IsAutCsd ι r → IsAutCsd ι r') ∧ (IsIrr r → IsIrr r') ∧ (IrrOpen r → IrrOpen r') ∧ RepIso r' r ∧ ∀ ξ, RepIso (tw r ξ) (tw r' ξ) := by
  intro L Ω _ _ _ _ _ _ l _ ι n r r' h
  refine ⟨?_, ?_, irr_iso h, ?_, h.symm', fun ξ => tw_iso ξ h⟩
  · rintro ⟨π, h1, h2⟩
    exact ⟨π, h1, att_iso h h2⟩
  · rintro ⟨π, h1, h2, h3⟩
    exact ⟨π, h1, h2, att_iso h h3⟩
  · intro hr H hH
    exact irr_iso (comp_iso H.subtype h) (hr H hH)
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.KerLe
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SubalgebraEqTop
noncomputable def UpperTheory.Reformulated.B.Qe26.IsInv :
    {Γ : Type} →
      [inst : Group Γ] → {k : Type} → [inst_1 : Field k] → {a : ℕ} → (Γ →* GL (Fin a) k) → Submodule k (Fin a → k) → Prop :=
    fun {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) ↦
      ∀ (g : Γ), ∀ v ∈ W, (↑((ρ : Γ → GL (Fin a) k) g) : Matrix (Fin a) (Fin a) k).mulVec v ∈ W

noncomputable def UpperTheory.Reformulated.B.Qe26.IsIrrSub :
    {Γ : Type} →
      [inst : Group Γ] → {k : Type} → [inst_1 : Field k] → {a : ℕ} → (Γ →* GL (Fin a) k) → Submodule k (Fin a → k) → Prop :=
    fun {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) ↦
      W ≠ ⊥ ∧ UpperTheory.Reformulated.B.Qe26.IsInv ρ W ∧ ∀ W' ≤ W, UpperTheory.Reformulated.B.Qe26.IsInv ρ W' → W' = ⊥ ∨ W' = W

noncomputable def UpperTheory.Reformulated.B.Qe26.IsIrr :
    {Γ k : Type} → [inst : Group Γ] → [inst_1 : Field k] → {n : ℕ} → (Γ →* GL (Fin n) k) → Prop :=
    fun {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) ↦ UpperTheory.Reformulated.B.Qe26.IsIrrSub r ⊤

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qe26.tr :
    {k : Type} → [inst : Field k] → {n : ℕ} → GL (Fin n) k → k :=
    fun {k : Type} [Field k] {n : ℕ} (g : GL (Fin n) k) ↦ (↑g : Matrix (Fin n) (Fin n) k).trace

private theorem UpperTheory.Reformulated.B.Qe26.subalgebra_eq_top {k V : Type} [Field k] [IsAlgClosed k]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] [Nontrivial V]
    (S : Subalgebra k (Module.End k V))
    (h : ∀ W : Submodule k V, (∀ s ∈ S, ∀ v ∈ W, s v ∈ W) → W = ⊥ ∨ W = ⊤) :
    S = ⊤ := by
  have hsimple : IsSimpleModule S V := by
    rw [isSimpleModule_iff]
    refine ⟨fun p ↦ ?_⟩
    rcases h (p.restrictScalars k) (fun s hs v hv ↦ p.smul_mem ⟨s, hs⟩ hv) with h1 | h1
    · left
      simpa using h1
    · right
      simpa using h1
  have hb := IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed (A := S) (V := V) k
  have hfin : Module.Finite (Module.End S V) V :=
    Module.Finite.of_restrictScalars_finite k _ _
  rw [eq_top_iff]
  intro T _
  let T' : Module.End (Module.End S V) V :=
    { toFun := T
      map_add' := T.map_add
      map_smul' := fun c v ↦ by
        obtain ⟨a, rfl⟩ := hb.2 c
        simp }
  obtain ⟨s, hs⟩ := Module.Finite.toModuleEnd_moduleEnd_surjective (R := S) (M := V) T'
  have : T = s.1 := by
    ext v
    exact (LinearMap.congr_fun hs v).symm
  rw [this]
  exact s.2

private theorem UpperTheory.Reformulated.B.Qe26.lift_surjective {k : Type} [Field k] [IsAlgClosed k] {H : Type}
    [Group H] {n : ℕ} (R : H →* GL (Fin n) k) (hR : UpperTheory.Reformulated.B.Qe26.IsIrr R) :
    Function.Surjective (MonoidAlgebra.lift k (Matrix (Fin n) (Fin n) k) H
      ((Units.coeHom (Matrix (Fin n) (Fin n) k)).comp R)) := by
  obtain ⟨h0, -, h1⟩ := hR
  set L := MonoidAlgebra.lift k (Matrix (Fin n) (Fin n) k) H
      ((Units.coeHom (Matrix (Fin n) (Fin n) k)).comp R) with hL
  have hnt : Nontrivial (Fin n → k) := (Submodule.nontrivial_iff k).1 ⟨⟨_, _, h0⟩⟩
  have htop := UpperTheory.Reformulated.B.Qe26.subalgebra_eq_top
    (((Matrix.toLinAlgEquiv' (R := k) (n := Fin n)).toAlgHom.comp L).range) (by
      intro W hW
      refine h1 W le_top (fun g v hv ↦ ?_)
      have := hW _ ⟨MonoidAlgebra.single g 1, rfl⟩ v hv
      simpa [hL] using this)
  intro M
  have hM : Matrix.toLinAlgEquiv' M ∈
      ((Matrix.toLinAlgEquiv' (R := k) (n := Fin n)).toAlgHom.comp L).range := by
    rw [htop]; trivial
  obtain ⟨x, hx⟩ := hM
  exact ⟨x, (Matrix.toLinAlgEquiv' (R := k) (n := Fin n)).injective hx⟩

theorem UpperTheory.Reformulated.B.Qe26.kerLe :
    ∀ (k : Type) [inst : Field k] [IsAlgClosed k] (H : Type) [inst_2 : Group H] (n : ℕ) (R : H →* GL (Fin n) k),
      UpperTheory.Reformulated.B.Qe26.IsIrr R →
        ∀ (x₀ : GL (Fin n) k) (B : Type) [inst_3 : Ring B] [inst_4 : Algebra k B] [Module.Finite k B] (φ : H →* B)
          (f : B →ₗ[k] k),
          (∀ (h : H), UpperTheory.Reformulated.B.Qe26.tr (x₀ * (R : H → GL (Fin n) k) h) = (f : B → k) ((φ : H → B) h)) →
            n ^ (2 : ℕ) ≤ Module.finrank k ↥(Algebra.adjoin k (Set.range (⇑φ : H → B))) ∧
              ∀ (x : MonoidAlgebra k H),
                ((MonoidAlgebra.lift k B H : (H →* B) → MonoidAlgebra k H →ₐ[k] B) φ : MonoidAlgebra k H → B) x = (0 : B) →
                  ((MonoidAlgebra.lift k (Matrix (Fin n) (Fin n) k) H :
                            (H →* Matrix (Fin n) (Fin n) k) → MonoidAlgebra k H →ₐ[k] Matrix (Fin n) (Fin n) k)
                          ((Units.coeHom (Matrix (Fin n) (Fin n) k)).comp R) :
                        MonoidAlgebra k H → Matrix (Fin n) (Fin n) k)
                      x =
                    (0 : Matrix (Fin n) (Fin n) k) := by
  intro k _ _ H _ n R hR x₀ B _ _ _ φ f hf
  have hsurj := UpperTheory.Reformulated.B.Qe26.lift_surjective R hR
  set L := MonoidAlgebra.lift k (Matrix (Fin n) (Fin n) k) H
      ((Units.coeHom (Matrix (Fin n) (Fin n) k)).comp R) with hL
  set Φ := MonoidAlgebra.lift k B H φ with hΦ
  have htr : ∀ y, ((x₀ : Matrix (Fin n) (Fin n) k) * L y).trace = f (Φ y) := by
    intro y
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp [mul_add, ha, hb]
    | single g c =>
      have := hf g
      simp only [UpperTheory.Reformulated.B.Qe26.tr, Units.val_mul] at this
      simp [hL, hΦ, ← this]
  have hker : ∀ x, Φ x = 0 → L x = 0 := by
    intro x hx
    rw [Matrix.ext_iff_trace_mul_left]
    intro M
    obtain ⟨y, hy⟩ := hsurj ((↑x₀⁻¹ : Matrix (Fin n) (Fin n) k) * M)
    have := htr (y * x)
    rw [map_mul, map_mul, hx, hy, mul_zero, map_zero, ← mul_assoc, Units.mul_inv_cancel_left] at this
    simpa using this
  refine ⟨?_, hker⟩
  have hle : LinearMap.ker Φ.toLinearMap ≤ LinearMap.ker L.toLinearMap := fun x hx ↦ hker x hx
  have hrange : LinearMap.range Φ.toLinearMap ≤
      Subalgebra.toSubmodule (Algebra.adjoin k (Set.range φ)) := by
    rintro _ ⟨y, rfl⟩
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add]; exact add_mem ha hb
    | single g c =>
      have : Φ.toLinearMap (MonoidAlgebra.single g c) = c • φ g := by simp [hΦ]
      rw [this]
      exact Submodule.smul_mem _ _ (Algebra.subset_adjoin ⟨g, rfl⟩)
  let ψ : LinearMap.range Φ.toLinearMap →ₗ[k] Matrix (Fin n) (Fin n) k :=
    ((LinearMap.ker Φ.toLinearMap).liftQ L.toLinearMap hle).comp
      Φ.toLinearMap.quotKerEquivRange.symm.toLinearMap
  have hψ : Function.Surjective ψ := by
    intro M
    obtain ⟨y, rfl⟩ := hsurj M
    exact ⟨Φ.toLinearMap.quotKerEquivRange (Submodule.Quotient.mk y), by simp [ψ]⟩
  calc n ^ 2 = Module.finrank k (Matrix (Fin n) (Fin n) k) := by
        simp [Module.finrank_matrix, sq]
    _ ≤ Module.finrank k (LinearMap.range Φ.toLinearMap) :=
        LinearMap.finrank_le_finrank_of_surjective hψ
    _ ≤ Module.finrank k (Subalgebra.toSubmodule (Algebra.adjoin k (Set.range φ))) :=
        Submodule.finrank_mono hrange
    _ = _ := rfl
end

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Sym.Ga.kerLe :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (H : Type) [Group H] (n : ℕ) (R : H →* GL (Fin n) k), IsIrr R → ∀ (x₀ : GL (Fin n) k) (B : Type) [Ring B] [Algebra k B] [Module.Finite k B] (φ : H →* B) (f : B →ₗ[k] k), (∀ h, Ga.tr (x₀ * R h) = f (φ h)) → n ^ 2 ≤ Module.finrank k (Algebra.adjoin k (Set.range φ)) ∧ ∀ x : MonoidAlgebra k H, MonoidAlgebra.lift k B H φ x = 0 → MonoidAlgebra.lift k (Matrix (Fin n) (Fin n) k) H ((Units.coeHom _).comp R) x = 0 :=
  _root_.UpperTheory.Reformulated.B.Qe26.kerLe
end
end
