module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.LinkedUnlOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.OrbitCount
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.CRealEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SeedPtOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.PxIsCont
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.FinLamOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.FirstPrimeConditionTransfer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SecondThirdPrimeConditionTransfer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SeedOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.ComponentsGoodRankTwo
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.PropagationTheoremGL3
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormLeOneOfIsIntegral

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.OpenEx
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.AbsGood
theorem UpperTheory.V.J.absGood :
    UpperTheory.V.J.AbsGood := by
  intro l _ O _ _ _ _ _ F T₂ T₃ J₂ J₃ h₂ h₃
  obtain ⟨φ₂, hφ₂, hs₂⟩ := UpperTheory.V.Pr.phiEx l O F 2 T₂
  obtain ⟨φ₃, hφ₃, hs₃⟩ := UpperTheory.V.Pr.phiEx l O F 3 T₃
  obtain ⟨Λ₂, hΛ₂⟩ := h₂.fin
  obtain ⟨Λ₃, hΛ₃⟩ := h₃.fin
  have good₂ : UpperTheory.V.Pr.AllGood T₂.S (Ideal.map φ₂ J₂) :=
    UpperTheory.V.Pr.components_good_rank_two l O F T₂.C₀ T₂.ok T₂.big T₂.S (Ideal.map φ₂ J₂)
      (UpperTheory.V.Pr.finLamOf l O F 2 T₂ φ₂ hφ₂ hs₂ Λ₂ J₂ hΛ₂)
      (UpperTheory.V.Pr.p1Of l O F 2 T₂ φ₂ hφ₂ h₂.n4 J₂ h₂.p1)
      (UpperTheory.V.Pr.seedOf l O F 2 T₂ φ₂ hφ₂ J₂ h₂.unr h₂.dim h₂.seed)
  refine ⟨φ₃, hφ₃, hs₃, ?_⟩
  exact (UpperTheory.V.Pr.components_good_rank_three l O F T₃.C₀ T₃.ok T₃.big T₂.S (Ideal.map φ₂ J₂)
      (UpperTheory.V.Pr.finLamOf l O F 2 T₂ φ₂ hφ₂ hs₂ Λ₂ J₂ hΛ₂) good₂
      T₃.S (Ideal.map φ₃ J₃)
      (UpperTheory.V.Pr.finLamOf l O F 3 T₃ φ₃ hφ₃ hs₃ Λ₃ J₃ hΛ₃)
      (UpperTheory.V.Pr.p1Of l O F 3 T₃ φ₃ hφ₃ h₃.n4 J₃ h₃.p1)
      (UpperTheory.V.Pr.rankThree_deformationSetup_splitting_condition l O F T₃ φ₃ hφ₃ h₃.n4 J₃ h₃.p3)
      (UpperTheory.V.Pr.seedOf l O F 3 T₃ φ₃ hφ₃ J₃ h₃.unr h₃.dim h₃.seed)).1
end

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af

namespace UpperTheory.V.J

open UpperTheory.V.Pr

end UpperTheory.V.J
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.XiAdic
noncomputable section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing

open IsLocalRing Formalism.ConjugateSelfDual UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.Pr

namespace UpperTheory.V.J

private def xiExt {l : ℕ} [Fact l.Prime] {k k' : Type} [Field k] [Field k'] {Φ : Fr.Frame l k} {n : ℕ}
    {K : Type} [CommRing K] (f : k →+* k') (ρ : Fr.NRep Φ n K) : Fr.NRep (Φ.ext f) n K where
  r := ρ.r
  ψ := ρ.ψ
  pol := ρ.pol
  diag := ρ.diag
  ord := ρ.ord

private theorem xi_adic {Γ R S : Type} [TopologicalSpace Γ] [CommRing R] [CommRing S] [IsLocalRing R]
    [IsLocalRing S] (φ : R →+* S) [IsLocalHom φ] {u : Γ → R} (h : AdicCont (maximalIdeal R) u) :
    AdicCont (maximalIdeal S) fun g => φ (u g) := by
  unfold AdicCont at h ⊢
  intro N
  have h1 : Ideal.map φ (maximalIdeal R) ≤ maximalIdeal S :=
    Ideal.map_le_iff_le_comap.mpr (fun a ha => Ideal.mem_comap.mpr (map_nonunit φ a ha))
  have hle : maximalIdeal R ^ N ≤ Ideal.comap φ (maximalIdeal S ^ N) := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono h1 N
  have hc := (h N).comp (Ideal.quotientMap (maximalIdeal S ^ N) φ hle)
  convert hc using 1
  ext g
  rfl

private theorem xi_key {O A O₁ : Type} [CommRing O] [IsLocalRing O] [CommRing A] [IsLocalRing A]
    [CommRing O₁] [IsLocalRing O₁] [IsNoetherianRing O₁] [IsAdicComplete (maximalIdeal O₁) O₁]
    [Algebra O A] [IsLocalHom (algebraMap O A)] (j : A →+* O₁) [IsLocalHom j]
    (f : ResidueField O →+* ResidueField O₁)
    (hf : ∀ a, f (residue O a) = residue O₁ (j (algebraMap O A a))) (x : A) (u : ResidueField O)
    (h : residue A x = ResidueField.map (algebraMap O A) u) : res O₁ O₁ (j x) = f u := by
  obtain ⟨a, rfl⟩ := residue_surjective u
  have h1 : x - algebraMap O A a ∈ maximalIdeal A := by
    rw [← residue_eq_zero_iff, map_sub, h, ResidueField.map_residue, sub_self]
  have h2 : j x - j (algebraMap O A a) ∈ maximalIdeal O₁ := by
    rw [← map_sub]
    exact map_nonunit j _ h1
  have h3 : residue O₁ (j x) = residue O₁ (j (algebraMap O A a)) := by
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    exact h2
  rw [hf, ← h3]
  simp only [res]
  simp
  rw [RingEquiv.symm_apply_eq]
  rfl

private theorem xi_lift {l : ℕ} [Fact l.Prime] {O A O₁ : Type} [CommRing O] [IsLocalRing O] [CommRing A]
    [IsLocalRing A] [CommRing O₁] [IsLocalRing O₁] [IsNoetherianRing O₁]
    [IsAdicComplete (maximalIdeal O₁) O₁] [Algebra O A] [IsLocalHom (algebraMap O A)] (j : A →+* O₁)
    [IsLocalHom j] (f : ResidueField O →+* ResidueField O₁)
    (hf : ∀ a, f (residue O a) = residue O₁ (j (algebraMap O A a)))
    {Φ : Fr.Frame l (ResidueField O)} {n : ℕ} (ρ : Fr.NRep Φ n A) (h : IsLiftA O ρ) :
    Fr.IsLift O₁ ((xiExt f ρ).map j) := by
  obtain ⟨hc, hb, hd⟩ := h
  refine ⟨⟨fun i k => ?_, fun v i => ?_⟩, ⟨fun g i => ?_, fun v i g => ?_⟩, fun g i k hik => ?_⟩
  · exact xi_adic j (hc.1 i k)
  · exact xi_adic j (hc.2 v i)
  · change res O₁ O₁ (j (ρ.r g i i)) = _
    rw [xi_key j f hf (ρ.r g i i) _ (hb.1 g i)]
    simp [Fr.Frame.ext, map_pow]
    rfl
  · change res O₁ O₁ (j ((ρ.ψ v i g : Aˣ) : A)) = _
    rw [xi_key j f hf _ _ (hb.2 v i g)]
    simp [Fr.Frame.ext, map_pow]
    rfl
  · change res O₁ O₁ (j (ρ.r g i k)) = 0
    rw [xi_key j f hf (ρ.r g i k) 0 (by rw [map_zero]; exact hd g i k hik), map_zero]

private theorem xi_loc {l : ℕ} [Fact l.Prime] (c c₁ : Coef l) (A : Subalgebra c.O (PadicAlgCl l))
    (hA : ∀ x ∈ A, x ∈ c₁.O) : ∃ j : A →+* c₁.O, (∀ x, (j x).1 = x.1) ∧ IsLocalHom j := by
  let j : A →+* c₁.O :=
    { toFun := fun x => ⟨x.1, hA x.1 x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  refine ⟨j, fun x => rfl, ?_⟩
  have hfin := c₁.fin
  have hint : (algebraMap ℤ_[l] c₁.O).IsIntegral :=
    algebraMap_isIntegral_iff.mpr (Algebra.IsIntegral.of_finite ℤ_[l] c₁.O)
  have hcomp : j.comp ((algebraMap c.O A).comp (algebraMap ℤ_[l] c.O)) = algebraMap ℤ_[l] c₁.O :=
    RingHom.ext fun x => Subtype.ext rfl
  have hj : j.IsIntegral := RingHom.IsIntegral.tower_top _ j (hcomp ▸ hint)
  refine hj.isLocalHom (fun x y h => ?_)
  have h' := congrArg (fun z : c₁.O => (z : PadicAlgCl l)) h
  exact Subtype.ext h'

theorem xiEx :
    UpperTheory.V.J.XiEx := by
  intro Ω _ _ _ l _ ι c _ N _ e ψ η σ g₁ B M H L _ _ _ _ _ Φ k c₁ _ f R A _ _ _ hA ρ hρ
  obtain ⟨j, hj, _⟩ := xi_loc c c₁ A hA
  have hf : ∀ a, f (residue c.O a) = residue c₁.O (j (algebraMap c.O A a)) := fun a =>
    R.hf a _ (hj (algebraMap c.O A a)).symm
  obtain ⟨ξ, hξ, -⟩ := R.S.univ c₁.O _ (xi_lift j f hf ρ hρ)
  refine ⟨ξ, fun g a b => ?_, fun v i g => ?_⟩
  · exact (congrArg (fun t : Fr.NRep _ _ c₁.O => (t.r g a b).1) hξ).trans (hj _)
  · exact (congrArg (fun t : Fr.NRep _ _ c₁.O => ((t.ψ v i g : c₁.Oˣ) : c₁.O).1) hξ).trans (hj _)

end UpperTheory.V.J

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.NotIrrOfLine
noncomputable section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Alg
open UpperTheory.V.W UpperTheory.V.Pr

namespace UpperTheory.V.J

private theorem norm_lt_of_mem {l : ℕ} [Fact l.Prime] (c : Coef l) (x : c.O) (hx : x ∈ maximalIdeal c.O) :
    ‖(x : Qbar l)‖ < 1 := by
  haveI := c.dvr
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible c.O
  by_cases hx0 : x = 0
  · subst hx0
    simp
  have hcast : (((l : ℕ) : c.O) : Qbar l) = ((l : ℕ) : Qbar l) := map_natCast c.O.val l
  have hlne : ((l : ℕ) : c.O) ≠ 0 := by
    intro h0
    have h1 : (((l : ℕ) : c.O) : Qbar l) = 0 := by rw [h0]; rfl
    rw [hcast] at h1
    exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast h1)
  obtain ⟨e, u, hle⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hlne hϖ
  obtain ⟨a, v, hxa⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
  have hlt := GlobalTheory.CoefCoord.norm_natCast_lt_one (l := l)
  have he : e ≠ 0 := by
    rintro rfl
    have hu := GlobalTheory.CoefCoord.norm_unit c u
    rw [pow_zero, mul_one] at hle
    rw [← hle, hcast] at hu
    linarith
  have ha : a ≠ 0 := by
    rintro rfl
    rw [pow_zero, mul_one] at hxa
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hxa] at hx
    exact hx v.isUnit
  obtain ⟨a', rfl⟩ := Nat.exists_eq_add_one_of_ne_zero ha
  have key : x ^ e = ((l : ℕ) : c.O) * (↑u⁻¹ * ↑v ^ e * ϖ ^ (a' * e)) := by
    rw [hxa, hle]
    linear_combination (-(↑v ^ e * ϖ ^ e * ϖ ^ (a' * e))) * u.mul_inv
  have h2 : ‖(x : Qbar l)‖ ^ e
      = ‖(((l : ℕ) : c.O) : Qbar l)‖ * ‖((↑u⁻¹ * ↑v ^ e * ϖ ^ (a' * e) : c.O) : Qbar l)‖ := by
    rw [← norm_pow, ← norm_mul, ← SubmonoidClass.coe_pow, ← MulMemClass.coe_mul, key]
  have h3 := GlobalTheory.CoefCoord.norm_le_one c (↑u⁻¹ * ↑v ^ e * ϖ ^ (a' * e))
  have h4 : ‖(x : Qbar l)‖ ^ e < 1 := by
    rw [h2, hcast]
    calc _ ≤ ‖((l : ℕ) : Qbar l)‖ * 1 := by gcongr
      _ < 1 := by simpa using hlt
  by_contra hge
  push_neg at hge
  exact absurd h4 (not_lt.mpr (one_le_pow₀ hge))

private theorem map_mem_max {O R : Type} [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R] [Algebra O R]
    (ξ : R →ₐ[O] O) (x : R) (hx : x ∈ maximalIdeal R) : ξ x ∈ maximalIdeal O := by
  by_contra h
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at h
  obtain ⟨u, hu⟩ := h
  have hy : ξ (x * algebraMap O R (↑u⁻¹ : O) - 1) = 0 := by
    rw [map_sub, map_mul, AlgHom.commutes, ← hu, map_one]
    simp
  have hm : x * algebraMap O R (↑u⁻¹ : O) - 1 ∈ maximalIdeal R := by
    by_contra h2
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at h2
    have h3 := h2.map ξ
    rw [hy] at h3
    exact not_isUnit_zero h3
  have h1 : (1 : R) ∈ maximalIdeal R := by
    have h4 := (maximalIdeal R).sub_mem ((maximalIdeal R).mul_mem_right (algebraMap O R ↑u⁻¹) hx) hm
    simpa using h4
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr h1)

private theorem not_irr_of_line {Γ k : Type} [Group Γ] [Field k] (r : Γ →* GL (Fin 3) k) (j : Fin 3)
    (h : ∀ s i, i ≠ j → (r s).val i j = 0) : ¬ IsIrr r := by
  intro hI
  obtain ⟨-, -, hmin⟩ := hI
  have hinv : Formalism.MainNotions.N.IsInv r (Submodule.span k {Pi.single j (1 : k)}) := by
    intro g v hv
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
    refine Submodule.mem_span_singleton.mpr ⟨a * (r g).val j j, ?_⟩
    ext i
    simp only [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
    by_cases hij : i = j
    · subst hij
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    · simp [Matrix.mulVec, dotProduct, Pi.single_apply, hij, h g i hij]
  rcases hmin _ le_top hinv with h0 | htop
  · have hs : (Pi.single j (1 : k) : Fin 3 → k) = 0 := by
      rw [← Submodule.mem_bot k, ← h0]
      exact Submodule.mem_span_singleton_self _
    have := congrFun hs j
    simp at this
  · have hj : j + 1 ≠ j := by fin_cases j <;> decide
    have hmem : (Pi.single (j + 1) (1 : k) : Fin 3 → k) ∈ Submodule.span k {Pi.single j (1 : k)} := by
      rw [htop]
      exact Submodule.mem_top
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
    have := congrFun ha (j + 1)
    simp [Pi.single_apply, hj] at this

private theorem ti_of {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Fr.Frame l k} {K : Type} [CommRing K]
    (ρ : Fr.NRep F 3 K) (p : Ideal K) (H : ∀ j : Fin 3, ¬ ∀ g i, i ≠ j → ρ.r g i j ∈ p) : ρ.TI p := by
  refine ⟨⟨fun hle => H 0 ?_, fun hle => H 2 ?_⟩, fun _ hle => H 1 ?_⟩
  · intro g i hi
    exact hle (Ideal.subset_span ⟨g, i, 0, by revert hi; fin_cases i <;> decide, rfl⟩)
  · intro g i hi
    exact hle (Ideal.subset_span ⟨g, i, 2, by revert hi; fin_cases i <;> decide, rfl⟩)
  · intro g i hi
    refine hle (Ideal.subset_span ⟨g, i, 1, ?_, rfl⟩)
    revert hi
    fin_cases i <;> simp [Fr.w] <;> decide

end UpperTheory.V.J

theorem UpperTheory.V.J.xiTI :
    UpperTheory.V.J.XiTI := by
  intro Ω _ _ _ l _ ι c _ N _ e ψ η σ g₁ B M H L _ _ _ _ _ Φ k c₁ _ f R ξ r hr hi
  have hcol : ∀ j : Fin 3, ¬ ∀ g i, i ≠ j → ξ (R.S.ρ.r g i j) = 0 := by
    intro j h
    refine not_irr_of_line r j (fun s i hij => ?_) hi
    rw [hr s]
    exact congrArg Subtype.val (h (k.p0 s) i hij)
  refine ⟨ti_of _ _ fun j h => hcol j fun g i hij => h g i hij, ⟨fun a => GlobalTheory.CoefCoord.norm_le_one c₁ _,
    fun b hb => norm_lt_of_mem c₁ _ (map_mem_max ξ b.1 hb)⟩, ti_of _ _ fun j h => hcol j fun g i hij => ?_⟩
  have h0 : ptA R ξ (R.S.u.r g i j) = 0 := h g i hij
  exact Subtype.ext h0

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.XiArith
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr

private theorem xa_norm {l : ℕ} [Fact l.Prime] (c : Coef l) (y : c.O) : ‖(y.1 : PadicAlgCl l)‖ ≤ 1 := by
  have hz : IsIntegral ℤ_[l] y.1 := (Algebra.IsIntegral.isIntegral (R := ℤ_[l]) y).map c.O.val
  have hq : IsIntegral ℚ_[l] y.1 := Algebra.IsIntegral.isIntegral _
  have h0 : ‖(y.1 : PadicAlgCl l)‖ = spectralValue (minpoly ℚ_[l] y.1) := rfl
  rw [h0, spectralValue_le_one_iff (minpoly.monic hq), ]
  intro n
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] hz, Polynomial.coeff_map]
  exact PadicInt.norm_le_one _

private theorem xa_pow {l : ℕ} [Fact l.Prime] (c : Coef l) [Fr.IsCoef l c.O] :
    ∃ e : ℕ, maximalIdeal c.O ^ e ≤ Ideal.span {(l : c.O)} := by
  have hl0 : (l : c.O) ≠ 0 := fun h => by
    have h1 : ((l : c.O) : PadicAlgCl l) = 0 := congrArg Subtype.val h
    have h2 : ((l : ℕ) : PadicAlgCl l) = 0 := by simpa using h1
    exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast h2)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible c.O
  obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hϖ
  refine ⟨e, ?_⟩
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, hu, Ideal.span_singleton_le_span_singleton]
  exact (Units.isUnit u).mul_left_dvd.2 dvd_rfl

private theorem xa_lnorm {l : ℕ} [Fact l.Prime] : ‖((l : ℕ) : PadicAlgCl l)‖ < 1 := by
  have h := PadicAlgCl.norm_extends (p := l) ((l : ℕ) : ℚ_[l])
  have h2 : (((l : ℕ) : ℚ_[l]) : PadicAlgCl l) = ((l : ℕ) : PadicAlgCl l) := by simp
  rw [h2] at h
  rw [h]
  exact Padic.norm_p_lt_one

private theorem xa_key {l : ℕ} [Fact l.Prime] (c : Coef l) {e : ℕ} (he : maximalIdeal c.O ^ e ≤ Ideal.span {(l : c.O)})
    (N : ℕ) (x : c.O) (hx : x ∈ maximalIdeal c.O ^ (e * N)) :
    ‖(x.1 : PadicAlgCl l)‖ ≤ ‖((l : ℕ) : PadicAlgCl l)‖ ^ N := by
  have h1 : x ∈ Ideal.span {(l : c.O) ^ N} := by
    rw [← Ideal.span_singleton_pow]
    rw [pow_mul] at hx
    exact Ideal.pow_right_mono he N hx
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.1 h1
  have h2 : (((l : c.O) ^ N * y : c.O).1 : PadicAlgCl l) = ((l : ℕ) : PadicAlgCl l) ^ N * y.1 := by
    rw [Subalgebra.coe_mul, Subalgebra.coe_pow, show (((l : c.O)).1 : PadicAlgCl l) = ((l : ℕ) : PadicAlgCl l) from map_natCast c.O.val l]
  rw [h2, norm_mul, norm_pow]
  exact mul_le_of_le_one_right (by positivity) (xa_norm c y)

private theorem xa_top {l : ℕ} [Fact l.Prime] {Γ : Type} [TopologicalSpace Γ] (u : Γ → PadicAlgCl l)
    (H : ∀ (g₀ : Γ) (ε : ℝ), 0 < ε → ∀ᶠ g in nhds g₀, ‖u g - u g₀‖ < ε) : Continuous u := by
  rw [continuous_iff_continuousAt]
  intro g₀
  rw [Metric.continuousAt_iff']
  intro ε hε
  simpa only [dist_eq_norm] using H g₀ ε hε

private theorem xa_cont {l : ℕ} [Fact l.Prime] (c : Coef l) [Fr.IsCoef l c.O] {Γ : Type} [TopologicalSpace Γ]
    (f : Γ → c.O) (h : Alg.AdicCont (maximalIdeal c.O) f) : Continuous fun g => ((f g).1 : PadicAlgCl l) := by
  obtain ⟨e, he⟩ := xa_pow c
  refine xa_top _ fun g₀ ε hε => ?_
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε (xa_lnorm (l := l))
  have h0 := (h (e * N)).eventually_eq g₀
  refine h0.mono fun g hg => ?_
  have h1 : f g - f g₀ ∈ maximalIdeal c.O ^ (e * N) := Ideal.Quotient.eq.1 hg
  have h2 : ((f g).1 : PadicAlgCl l) - (f g₀).1 = ((f g - f g₀ : c.O).1 : PadicAlgCl l) :=
    (map_sub c.O.val (f g) (f g₀)).symm
  rw [h2]
  exact lt_of_le_of_lt (xa_key c he N _ h1) hN

private theorem xa_gl {Γ k : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Field k] [TopologicalSpace k]
    [IsTopologicalRing k] {n : ℕ} (r : Γ →* GL (Fin n) k) (χ : Γ →* kˣ) (hχ : Continuous χ)
    (hr : ∀ i j, Continuous fun s => (r s : Matrix (Fin n) (Fin n) k) i j) : Continuous (tw r χ) := by
  have h0 : Continuous fun s => (tw r χ s : Matrix (Fin n) (Fin n) k) := by
    refine continuous_matrix fun i j => ?_
    simp only [tw_val, Matrix.smul_apply, smul_eq_mul]
    exact (Units.continuous_val.comp hχ).mul (hr i j)
  refine Units.continuous_iff.2 ⟨h0, ?_⟩
  have h1 : (fun s => (((tw r χ s)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) =
      fun s => (tw r χ s⁻¹ : Matrix (Fin n) (Fin n) k) := by
    funext s
    rw [map_inv]
  rw [h1]
  exact h0.comp continuous_inv

private theorem xa_adic {O R Γ : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O]
    [CommRing R] [Algebra O R] [Alg.IsCO O R] [TopologicalSpace Γ] (ξ : R →ₐ[O] O) {u : Γ → R}
    (h : Alg.AdicCont (maximalIdeal R) u) : Alg.AdicCont (maximalIdeal O) fun g => ξ (u g) := fun N => by
  have hm : ∀ x ∈ maximalIdeal R, ξ x ∈ maximalIdeal O := fun x hx => by
    have h1 := Alg.res_map ξ x
    rw [(Alg.res_eq_zero_iff O R x).2 hx] at h1
    exact (Alg.res_eq_zero_iff O O _).1 h1
  have hle : maximalIdeal R ^ N ≤ (maximalIdeal O ^ N).comap (ξ : R →+* O) := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 hm) N
  exact (h N).comp (Ideal.quotientMap _ (ξ : R →+* O) hle)

private theorem ap_det {n : ℕ} {A B G H : Type} [CommRing A] [CommRing B] [Group G] [Group H]
    (ρ : G →* Matrix (Fin n) (Fin n) A) (f : A →+* B) (p : H →* G) (τ : H →* Matrix (Fin n) (Fin n) B)
    (h : ∀ g, τ g = (ρ (p g)).map f) : ((W.GDet.ofRep ρ).map f).comap p = W.GDet.ofRep τ := by
  refine W.GDet.ext fun C _ _ x => ?_
  letI : Algebra A C := ((algebraMap B C).comp f).toAlgebra
  change (W.GDet.repAlg ρ C (MonoidAlgebra.mapDomainRingHom C p x)).det = (W.GDet.repAlg τ C x).det
  congr 1
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | single g r =>
    ext i j
    simp [W.GDet.repAlg, h]
    rfl

private theorem ap_locAlg (hG : GlobalTheory.Published.GlobalArtinReciprocity) {L Ω : Type} [Field L] [NumberField L] [Field Ω]
    [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (ka : G L Ω →* (Qbar l)ˣ)
    (hka : Sd.IsAlgChar ι ka) {A : ValuationSubring Ω} {w : W.Plc L} (h : IsPlaceOver A w)
    (hw : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal) :
    ∃ wt : W.Emb l w → ℤ, ∀ (m : ℤ) (χ : G L Ω →* (Qbar l)ˣ), IsOpen (χ.ker : Set (G L Ω)) →
      ∀ κ : Dec (F := L) A →* (Qbar l)ˣ,
        (∀ g : Dec (F := L) A, (g : G L Ω) ∈ Ine (F := L) A → κ g = cycBar L Ω l g ^ m * χ g * ka g) →
        W.IsLocAlg h κ fun τ => wt τ - m := by
  obtain ⟨-, art, Y, a, hart, -, hY⟩ := hka
  refine ⟨fun τ => -a ((ι.toRingHom.comp τ.1).comp (algebraMap L (w.adicCompletion L))), fun m χ hχ κ hκ => ?_⟩
  by_cases hl : ∃ b, GlobalTheory.LocLanglands.IsLocalArtin h b
  swap
  · exact ⟨1, by simp, fun b hb => absurd ⟨b, hb⟩ hl⟩
  obtain ⟨ph, h1⟩ := Loc.laHecke h art hart ι Y a ka hY hl
  have h2 := (Loc.laMul h).2.1 _ _ _ m (Loc.laCyc hG h hw)
  have h3 := (Loc.laMul h).2.2 (χ.comp (Dec (F := L) A).subtype) (χ.comp (Ine (F := L) A).subtype)⁻¹
    (Subgroup.isOpen_mono (H₁ := χ.ker.comap (Ine (F := L) A).subtype) (fun x hx => inv_eq_one.2 hx)
      (hχ.preimage continuous_subtype_val)) fun s => mul_inv_cancel _
  have h4 := ((Loc.laMul h).1 _ _ _ _ _ _ ((Loc.laMul h).1 _ _ _ _ _ _ h2 h3).1 h1).1
  refine ⟨_, h4.1, fun b hb s => ?_⟩
  have h5 := h4.2 b hb s
  rw [hκ _ s.2]
  refine Eq.trans ?_ (h5.trans ?_)
  · rfl
  · refine finprod_congr fun τ => ?_
    congr 1
    simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
    ring

private theorem ap_psi {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (c : Coef l)
    {N : ℕ} [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (L : Type) [Field L] [NumberField L] [Algebra L Ω]
    [IsAlgClosure L Ω] (m : ℤ) :
    ∃ χ : G L Ω →* (Qbar l)ˣ, IsOpen (χ.ker : Set (G L Ω)) ∧ ∀ g : G L Ω,
      (Chr.Psi l e (Chr.dirG ℚ Ω ψ) (galEmb ℚ L Ω g) ^ m).val.1 = (cycBar L Ω l g ^ ((e : ℤ) * m) * χ g).val := by
  let u : c.Oˣ →* (Qbar l)ˣ := Units.map c.O.val.toRingHom.toMonoidHom
  refine ⟨((u.comp (Chr.dirG ℚ Ω ψ)).comp (galEmb ℚ L Ω)) ^ m, ?_, fun g => ?_⟩
  · refine Subgroup.isOpen_mono (H₁ := (Chr.cls ℚ Ω N).ker.comap (galEmb ℚ L Ω)) (fun g hg => ?_)
      ((Chr.clsFacts ℚ Ω N).1.preimage (galEmbTop ℚ L Ω).1.continuous)
    have h1 : Chr.cls ℚ Ω N (galEmb ℚ L Ω g) = 1 := hg
    rw [MonoidHom.mem_ker, MonoidHom.zpow_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, Chr.dirG, MonoidHom.comp_apply,
      h1, map_one, map_one, one_zpow]
  · have h1 : u (chiO ℚ Ω l c.O (galEmb ℚ L Ω g)) = cycBar L Ω l g := Units.ext rfl
    change (u _).val = _
    rw [map_zpow, Chr.Psi, MonoidHom.mul_apply, map_mul, MonoidHom.zpow_apply, map_zpow, h1, mul_zpow, ← zpow_mul]
    rfl

theorem UpperTheory.V.J.xiArith :
    GlobalTheory.Published.GlobalArtinReciprocity → UpperTheory.V.J.XiArith := by
  intro hG Ω _ _ _ l _ ι c _ N _ e ψ η σ g₁ B M H L _ _ _ _ _ Φ k c₁ _ f R hka φ hφ ξ r hr hirr hψ
  letI : CommRing R.S.B := Subalgebra.toCommRing R.S.B
  letI : Algebra c₁.O R.S.B := Subalgebra.algebra R.S.B
  obtain ⟨hD1, hP1⟩ := hφ
  have hD0 : R.B₀.u.D.map ((R.S.B.val.comp φ : R.B₀.B →ₐ[c₁.O] R.S.R) : R.B₀.B →+* R.S.R) =
      W.GDet.ofRep (R.K.tw R.S.ρ) := hD1
  have hP0 : ∀ v i, W.pushCh ((R.S.B.val.comp φ : R.B₀.B →ₐ[c₁.O] R.S.R) : R.B₀.B →+* R.S.R) (R.B₀.u.ψ v i) =
      R.K.twψ R.S.ρ v i := hP1
  let F : R.B₀.B →ₐ[c₁.O] c₁.O := ξ.comp (R.S.B.val.comp φ)
  let j : c₁.O →ₐ[c₁.O] Qbar l := Algebra.ofId c₁.O (Qbar l)
  let ρ₂ : Fr.NRep (Φ.ext f) 3 c₁.O := R.S.ρ.map (ξ : R.S.R →+* c₁.O)
  have hD : R.B₀.u.D.map (F : R.B₀.B →+* c₁.O) = W.GDet.ofRep (R.K.tw ρ₂) := by
    rw [← R.K.ofRep_tw_map, ← hD0, (CA.d_gmap _).2.1]
    rfl
  have hP : ∀ v i, W.pushCh (F : R.B₀.B →+* c₁.O) (R.B₀.u.ψ v i) = R.K.twψ ρ₂ v i := fun v i => by
    rw [← R.K.twψ_map, ← hP0 v i]
    rfl
  have hw : ∀ v : W.Vl l L, ((l : ℕ) : 𝓞 L) ∈ (R.s.w v).asIdeal := fun v => by
    have h1 := (R.s.hA v (l : ℕ)).2 v.2
    refine (R.s.hw v (l : ℕ)).1 ?_
    simpa using h1
  choose wt hwt using fun v : W.Vl l L => ap_locAlg hG ι _ hka.alg (R.s.hw v) (hw v)
  refine ⟨⟨fun v i τ => wt v τ - (e : ℤ) * Fr.w 3 i, ⟨fun v τ a b hab => ?_, fun v i => ?_⟩⟩,
    tw r (cycBar L Ω l)⁻¹, ?_, ?_, (UpperTheory.isIrr_twist_and_repIso_of_twist_repIso _ _ 3 _).1 r hirr⟩
  · have h1 : Fr.w 3 b < Fr.w 3 a := by
      have h2 : (a : ℕ) < b := hab
      unfold Fr.w
      split_ifs <;> omega
    have h3 : (0 : ℤ) < e := by exact_mod_cast H.e_pos
    exact sub_lt_sub_left (mul_lt_mul_of_pos_left h1 h3) _
  · obtain ⟨χ, hχ, h1⟩ := ap_psi c e ψ L (Ω := Ω) (Fr.w 3 i)
    refine hwt v _ χ hχ _ fun g hg => Units.ext ?_
    have h2 : F (R.B₀.u.ψ v i g).val = (R.K.twψ ρ₂ v i g).val := congrArg (fun t => (t g).val) (hP v i)
    have h3 := hψ (R.K.e v) i (R.K.lam v g) ((R.K.lam_I v g).2 hg)
    rw [R.lam_j] at h3
    rw [Units.val_mul, ← h1, ← R.κ_pr]
    change j (F (R.B₀.u.ψ v i g).val) = _
    rw [h2]
    exact congrArg (fun t : Qbar l => t * (R.K.κ (R.V.pr g)).val.1) h3
  · refine xa_gl r _ hka.alg.1 fun a b => ?_
    have hp0 : Continuous k.p0 :=
      ((k.p_cont.comp ((galEmbTop ℚ L Ω).1.continuous.subtype_mk _)).subtype_mk _)
    have e1 : (fun s => (r s : Matrix (Fin 3) (Fin 3) (Qbar l)) a b) = fun s => (ξ (R.S.ρ.r (k.p0 s) a b)).1 :=
      funext fun s => by rw [hr s]; rfl
    rw [e1]
    exact xa_cont c₁ (fun s => ξ (R.S.ρ.r (k.p0 s) a b)) fun N =>
      (xa_adic ξ (R.S.lift.1.1 a b) N).comp_continuous hp0
  · have h1 : W.UniversalOrdinaryDeterminantRing.Pt.D (j.comp F) = (W.GDet.ofRep (R.K.tw ρ₂)).map (j : c₁.O →+* Qbar l) :=
      congrArg (fun D => D.map (j : c₁.O →+* Qbar l)) hD
    refine (congrArg (fun D => D.comap R.V.pr) h1).trans (ap_det _ _ _ _ fun g => ?_)
    change (tw r (cycBar L Ω l)⁻¹ g).val = _
    rw [tw_val, hr, ← R.κ_pr, ← R.π_pr]
    rfl
end
