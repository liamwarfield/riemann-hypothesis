module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RationalVectorsSameLengthOneUnitaryOrbit
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneSemisimple
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneSemisimple
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.WeilDeligne

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {V : Type} [AddCommGroup V] [Module ℂ V]

theorem exists_frob_pow_mul_ineIncl_mul (m : ℕ) (hm : 0 < m) (σ : Weil h) :
    ∃ (r : ℕ) (τ : Ine (F := E) A) (q : ℤ), r < m ∧
      σ = frob h ^ r * ineIncl h τ * (frob h ^ m) ^ q := by
  have hm' : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  have hdeg : deg (σ * (frob h ^ m) ^ (-(deg σ / m))) = deg σ % m := by
    rw [deg_mul, deg_zpow, deg_pow, deg_frob, Int.emod_def]
    ring
  obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul (deg_frob (h := h)) (σ * (frob h ^ m) ^ (-(deg σ / m)))
  have hr0 : 0 ≤ deg σ % (m : ℤ) := Int.emod_nonneg _ hm'
  have hr1 : deg σ % (m : ℤ) < m := Int.emod_lt_of_pos _ (by exact_mod_cast hm)
  refine ⟨(deg σ % m).toNat, τ, deg σ / m, by omega, ?_⟩
  have hz : frob h ^ (deg σ % (m : ℤ)).toNat = frob h ^ (deg σ % (m : ℤ)) := by
    rw [← zpow_natCast, Int.toNat_of_nonneg hr0]
  rw [hz, ← hdeg, ← hτ, mul_assoc, ← _root_.zpow_add, neg_add_cancel, zpow_zero, mul_one]

theorem isSemisimpleRepresentation_of_isSmooth [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (Weil h) V) (hρ : IsSmooth ρ)
    (hss : ∀ σ, Module.End.IsSemisimple (ρ σ)) : ρ.IsSemisimpleRepresentation := by
  classical
  obtain ⟨m, hm⟩ : ∃ m : ℕ, 0 < m := ⟨1, one_pos⟩
  refine ⟨fun P => ?_⟩
  have hPinv : P.toSubmodule ∈ Module.End.invtSubmodule (ρ (frob h ^ m)) := by
    rw [Module.End.mem_invtSubmodule]
    intro v hv
    exact P.apply_mem_toSubmodule _ hv
  obtain ⟨Q, hQ, hc⟩ := (Module.End.isSemisimple_iff.mp (hss (frob h ^ m))) _ hPinv
  rw [Module.End.mem_invtSubmodule] at hQ
  let p : Module.End ℂ V := P.toSubmodule.projection Q hc
  have hp1 : ∀ v ∈ P.toSubmodule, p v = v := fun v hv => Submodule.projection_apply_left hc ⟨v, hv⟩
  have hp2 : ∀ v ∈ Q, p v = 0 := fun v hv => Submodule.projection_apply_right hc ⟨v, hv⟩
  have hpm : ∀ v, p v ∈ P.toSubmodule := fun v => Submodule.projection_apply_mem hc v
  have hpT : ρ (frob h ^ m) * p = p * ρ (frob h ^ m) := by
    ext v
    obtain ⟨x, hx, y, hy, rfl⟩ :=
      Submodule.mem_sup.1 (show v ∈ P.toSubmodule ⊔ Q by rw [hc.sup_eq_top]; trivial)
    simp only [Module.End.mul_apply, map_add (f := _), hp1 _ hx, hp2 _ hy, add_zero,
      hp1 _ (hPinv hx), hp2 _ (hQ hy), map_zero]
  have hinv : ∀ σ : Weil h, ρ σ * ρ σ⁻¹ = 1 := fun σ => by rw [← map_mul, mul_inv_cancel, map_one]
  have hinv' : ∀ σ : Weil h, ρ σ⁻¹ * ρ σ = 1 := fun σ => by rw [← map_mul, inv_mul_cancel, map_one]
  let c : Weil h → Module.End ℂ V := fun σ => ρ σ * p * ρ σ⁻¹
  have hcm : ∀ σ v, c σ v ∈ P.toSubmodule := fun σ v => P.apply_mem_toSubmodule σ (hpm _)
  have hc1 : ∀ σ, ∀ v ∈ P.toSubmodule, c σ v = v := by
    intro σ v hv
    show ρ σ (p (ρ σ⁻¹ v)) = v
    rw [hp1 _ (P.apply_mem_toSubmodule _ hv), ← Module.End.mul_apply, hinv, Module.End.one_apply]
  have hper : ∀ σ, c (σ * frob h ^ m) = c σ := by
    intro σ
    simp only [c, _root_.mul_inv_rev, map_mul]
    calc ρ σ * ρ (frob h ^ m) * p * (ρ (frob h ^ m)⁻¹ * ρ σ⁻¹)
        = ρ σ * (ρ (frob h ^ m) * p * ρ (frob h ^ m)⁻¹) * ρ σ⁻¹ := by simp only [mul_assoc]
      _ = ρ σ * (p * (ρ (frob h ^ m) * ρ (frob h ^ m)⁻¹)) * ρ σ⁻¹ := by rw [hpT]; simp only [mul_assoc]
      _ = ρ σ * p * ρ σ⁻¹ := by rw [hinv, mul_one]
  have hzper : ∀ σ (q : ℤ), c (σ * (frob h ^ m) ^ q) = c σ := by
    intro σ q
    induction q using Int.induction_on with
    | zero => simp
    | succ q ih => rw [_root_.zpow_add_one, ← mul_assoc, hper, ih]
    | pred q ih =>
      rw [← ih, ← hper, mul_assoc, ← _root_.zpow_add_one]
      congr 3
      ring
  have hFfin := hρ.finite_range
  have hCfin : (Set.range c).Finite := by
    refine (((Set.finite_Iio m).prod (hFfin.prod hFfin)).image
      (fun t : ℕ × (Module.End ℂ V × Module.End ℂ V) =>
        ρ (frob h ^ t.1) * (t.2.1 * p * t.2.2) * ρ ((frob h ^ t.1)⁻¹))).subset ?_
    rintro _ ⟨σ, rfl⟩
    obtain ⟨r, τ, q, hr, rfl⟩ := exists_frob_pow_mul_ineIncl_mul m hm σ
    refine ⟨(r, ρ (ineIncl h τ), ρ (ineIncl h τ⁻¹)), ⟨hr, ⟨τ, rfl⟩, ⟨τ⁻¹, rfl⟩⟩, ?_⟩
    show _ = c _
    rw [hzper]
    simp only [c, _root_.mul_inv_rev, map_mul, map_inv, mul_assoc]
  set Cf := hCfin.toFinset with hCf
  have hCmem : ∀ x, x ∈ Cf ↔ ∃ σ, c σ = x := fun x => by simp [Cf]
  have hcard : Cf.card ≠ 0 := Finset.card_ne_zero_of_mem ((hCmem _).2 ⟨1, rfl⟩)
  let S : Module.End ℂ V := ∑ x ∈ Cf, x
  let qa : Module.End ℂ V := (Cf.card : ℂ)⁻¹ • S
  have hSm : ∀ v, S v ∈ P.toSubmodule := by
    intro v
    simp only [S]
    rw [LinearMap.sum_apply]
    refine P.toSubmodule.sum_mem fun x hx => ?_
    obtain ⟨σ, rfl⟩ := (hCmem x).1 hx
    exact hcm σ v
  have hS1 : ∀ v ∈ P.toSubmodule, S v = (Cf.card : ℂ) • v := by
    intro v hv
    simp only [S]
    rw [LinearMap.sum_apply]
    rw [Finset.sum_congr rfl (g := fun _ => v), Finset.sum_const, Nat.cast_smul_eq_nsmul]
    intro x hx
    obtain ⟨σ, rfl⟩ := (hCmem x).1 hx
    exact hc1 σ v hv
  have hSeq : ∀ g : Weil h, ρ g * S = S * ρ g := by
    intro g
    have h1 : ∑ x ∈ Cf, ρ g * x * ρ g⁻¹ = ∑ x ∈ Cf, x := by
      refine Finset.sum_nbij' (fun x => ρ g * x * ρ g⁻¹) (fun x => ρ g⁻¹ * x * ρ g)
        ?_ ?_ ?_ ?_ (fun _ _ => rfl)
      · intro x hx
        obtain ⟨σ, rfl⟩ := (hCmem x).1 (Finset.mem_coe.1 hx)
        exact Finset.mem_coe.2 ((hCmem _).2 ⟨g * σ, by simp only [c, _root_.mul_inv_rev, map_mul, mul_assoc]⟩)
      · intro x hx
        obtain ⟨σ, rfl⟩ := (hCmem x).1 (Finset.mem_coe.1 hx)
        exact Finset.mem_coe.2 ((hCmem _).2 ⟨g⁻¹ * σ, by
          simp only [c, _root_.mul_inv_rev, map_mul, inv_inv, mul_assoc]⟩)
      · intro x _
        simp only [← mul_assoc, hinv', one_mul]
        rw [mul_assoc, hinv', mul_one]
      · intro x _
        simp only [← mul_assoc, hinv, one_mul]
        rw [mul_assoc, hinv, mul_one]
    calc ρ g * S = (∑ x ∈ Cf, ρ g * x * ρ g⁻¹) * ρ g := by
          rw [Finset.sum_mul]
          simp only [S, Finset.mul_sum, mul_assoc, hinv', mul_one]
      _ = S * ρ g := by rw [h1]
  have hqm : ∀ v, qa v ∈ P.toSubmodule := fun v => P.toSubmodule.smul_mem _ (hSm v)
  have hq1 : ∀ v ∈ P.toSubmodule, qa v = v := by
    intro v hv
    show (Cf.card : ℂ)⁻¹ • S v = v
    rw [hS1 v hv, inv_smul_smul₀ (by exact_mod_cast hcard)]
  have hqe : ∀ g v, qa (ρ g v) = ρ g (qa v) := by
    intro g v
    show (Cf.card : ℂ)⁻¹ • S (ρ g v) = ρ g ((Cf.card : ℂ)⁻¹ • S v)
    rw [map_smul, ← Module.End.mul_apply S, ← hSeq, Module.End.mul_apply]
  let q' : V →ₗ[ℂ] P.toSubmodule := qa.codRestrict P.toSubmodule hqm
  have hcompl : IsCompl P.toSubmodule (LinearMap.ker q') :=
    LinearMap.isCompl_of_proj fun x => Subtype.ext (hq1 x x.2)
  refine ⟨⟨LinearMap.ker q', fun g v hv => ?_⟩, ?_⟩
  · have h0 : qa v = 0 := congrArg Subtype.val hv
    apply Subtype.ext
    show qa (ρ g v) = 0
    rw [hqe, h0, map_zero]
  · rw [isCompl_iff, disjoint_iff, codisjoint_iff,
      ← Subrepresentation.toSubmodule_injective.eq_iff,
      ← Subrepresentation.toSubmodule_injective.eq_iff]
    rw [isCompl_iff, disjoint_iff, codisjoint_iff] at hcompl
    exact hcompl

end GlobalTheory.WeilDeligne

namespace GlobalTheory.WeilDeligne.WDRep

theorem isSemisimpleRepresentation_rho : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω]
    [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E))
    (h : IsPlaceOver A w) (n : ℕ) (a : WDRep h (Fin n → ℂ)), a.ρ.IsSemisimpleRepresentation := by
  intro E Ω _ _ _ _ _ A w h n a
  exact isSemisimpleRepresentation_of_isSmooth a.ρ a.smooth a.semisimple

end GlobalTheory.WeilDeligne.WDRep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneSemisimpleStatement
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_deligne_semisimple : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (n : ℕ) (a : WDRep h (Fin n → ℂ)), a.ρ.IsSemisimpleRepresentation := by
  first | exact @GlobalTheory.WeilDeligne.WDRep.isSemisimpleRepresentation_rho | exact GlobalTheory.WeilDeligne.WDRep.isSemisimpleRepresentation_rho | (intros; apply GlobalTheory.WeilDeligne.WDRep.isSemisimpleRepresentation_rho <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStandardAdelicAddChar
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStandardAdelicAddChar
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

theorem sFin_sLoc_eq (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (y : w.adicCompletion E) :
    sFin E (sLoc E w y) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.pairA E 0 (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.singleV E w y) := by
  classical
  refine Prod.ext rfl ?_
  refine Subtype.ext (funext fun v => ?_)
  change (sLoc E w y) v = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.singleV E w y v
  by_cases h : v = w
  · subst h
    rw [GlobalTheory.StdDual.singleV_self]
    exact (Pi.single_eq_same v y : (Pi.single v y : ∀ u : HeightOneSpectrum (𝓞 E), u.adicCompletion E) v = y)
  · rw [GlobalTheory.StdDual.singleV_of_ne _ h]
    exact (Pi.single_eq_of_ne h y : (Pi.single w y : ∀ u : HeightOneSpectrum (𝓞 E), u.adicCompletion E) v = 0)

theorem exists_stdPsi : ∀ (E : Type) [Field E] [NumberField E], ∃ ψ : AddChar (Ad E) ℂ, StdPsi ψ := by
  intro E _ _
  obtain ⟨ψ, hψ, -⟩ := GlobalTheory.StdCharUnique.existsUnique_isStdChar E
  let L : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf E →+ ℂ :=
    AddMonoidHom.mk' (fun x => (GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.traceInf E x : ℂ)) fun a b => by
      rw [GlobalTheory.StdCharUnique.traceInf_add, Complex.ofReal_add]
  have hL : Continuous L := Complex.continuous_ofReal.comp (GlobalTheory.StdCharUnique.continuous_traceInf E)
  have hT : ∀ x : E, L (algebraMap E _ x) = ((Algebra.trace ℚ E x : ℚ) : ℂ) := fun x => by
    show ((GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.traceInf E (algebraMap E _ x) : ℝ) : ℂ) = _
    rw [GlobalTheory.StdCharUnique.traceInf_algebraMap, Complex.ofReal_ratCast]
  have hinf : ∀ x, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.psiInf E ψ x = Complex.exp (-(2 * Real.pi * Complex.I * L x)) := fun x => by
    rw [hψ.2, GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.stdInf]
    congr 1
    show _ * ((GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.traceInf E x : ℝ) : ℂ) = -(_ * ((GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.traceInf E x : ℝ) : ℂ))
    ring
  have hv : ∀ v, ∃ y, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.psiV E ψ v y ≠ 1 := fun v => by
    obtain ⟨y, hy⟩ := GlobalTheory.StdCharLocal.psiV_ne_one_of_trace (GlobalTheory.StdAdelicChar.isCharAF_inv hψ.1) (fun a => by
      rw [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.psiInf, AddChar.inv_apply', ← Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.psiInf, hinf, hT, ← Complex.exp_neg, neg_neg]) v
    refine ⟨y, fun h1 => hy ?_⟩
    rw [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.psiV] at h1 ⊢
    rw [AddChar.inv_apply', h1, inv_one]
  refine ⟨ψ, hψ.1.1, hψ.1.2.1, hψ.1.2.2.1, fun x h => GlobalTheory.RatAnnih.adele_rat hψ.1 hv L hL hT hinf x h, ?_⟩
  intro w
  obtain ⟨y, hy⟩ := hv w
  refine ⟨y, ?_⟩
  rw [sFin_sLoc_eq]
  exact hy

end GlobalTheory.CuspGeneric

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStandardAdelicAddCharStatement
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_standardAdelicAddChar : ∀ (E : Type) [Field E] [NumberField E], ∃ ψ : AddChar (Ad E) ℂ, StdPsi ψ := by
  first | exact @GlobalTheory.CuspGeneric.exists_stdPsi | exact GlobalTheory.CuspGeneric.exists_stdPsi | (intros; apply GlobalTheory.CuspGeneric.exists_stdPsi <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompletionBaseChangePlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompletionBaseChangePlaces
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompositumCompletion

theorem exists_completion_map {L L' : Type} [Field L] [NumberField L] [Field L'] [NumberField L']
    (jL : L →+* L') (v : HeightOneSpectrum (𝓞 L)) (v' : HeightOneSpectrum (𝓞 L'))
    (h : ∀ x : 𝓞 L, RingOfIntegers.mapRingHom jL x ∈ v'.asIdeal ↔ x ∈ v.asIdeal) :
    ∃ μ : v.adicCompletion L →+* v'.adicCompletion L', Continuous μ ∧
      ∀ x, μ (algebraMap L _ x) = algebraMap L' _ (jL x) := by
  letI : Algebra L L' := jL.toAlgebra
  haveI : v'.asIdeal.LiesOver v.asIdeal := ⟨by ext x; exact (h x).symm⟩
  have hc := (HeightOneSpectrum.uniformContinuous_algebraMap_liesOver L L' v v').continuous
  let φ : v.adicCompletion L →+* v'.adicCompletion L' :=
    ((HeightOneSpectrum.adicCompletion.equiv L' v').symm.toRingHom.comp
    (UniformSpace.Completion.mapRingHom
      (algebraMap (WithVal (v.valuation L)) (WithVal (v'.valuation L'))) hc)).comp
      (HeightOneSpectrum.adicCompletion.equiv L v).toRingHom
  refine ⟨φ, ?_, fun x => ?_⟩
  · exact (HeightOneSpectrum.adicCompletion.continuous_ofCompletion L' v').comp
      ((UniformSpace.Completion.continuous_map
        (f := algebraMap (WithVal (v.valuation L)) (WithVal (v'.valuation L')))).comp
        (HeightOneSpectrum.adicCompletion.continuous_toCompletion L v))
  · apply HeightOneSpectrum.adicCompletion.ext
    exact UniformSpace.Completion.mapRingHom_coe hc (WithVal.toVal _ x)

theorem exists_ringEquiv_completion : ∀ (E L E' L' : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Algebra E L] [Field E'] [NumberField E'] [Field L'] [NumberField L'] [Algebra E' L'] (w : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (𝓞 L)) (w' : HeightOneSpectrum (𝓞 E')) (v' : HeightOneSpectrum (𝓞 L')) (j : E →+* E') (jL : L →+* L') (i : w.adicCompletion E ≃+* w'.adicCompletion E'), (∀ x : 𝓞 E, algebraMap (𝓞 E) (𝓞 L) x ∈ v.asIdeal ↔ x ∈ w.asIdeal) → (∀ x : 𝓞 E', algebraMap (𝓞 E') (𝓞 L') x ∈ v'.asIdeal ↔ x ∈ w'.asIdeal) → (∀ x : 𝓞 L, RingOfIntegers.mapRingHom jL x ∈ v'.asIdeal ↔ x ∈ v.asIdeal) → (∀ x, jL (algebraMap E L x) = algebraMap E' L' (j x)) → Algebra.adjoin E' (Set.range jL) = ⊤ → Continuous i → (∀ x, i (algebraMap E _ x) = algebraMap E' _ (j x)) → ∃ iL : v.adicCompletion L ≃+* v'.adicCompletion L', Continuous iL ∧ ∀ x, iL (algebraMap L _ x) = algebraMap L' _ (jL x) := by
  intro E L E' L' _ _ _ _ _ _ _ _ _ _ w v w' v' j jL i hv hv' hjv hjL hadj hic hij
  obtain ⟨κ, hκc, hκ⟩ := exists_completion_map (algebraMap E L) w v (fun x => hv x)
  obtain ⟨κ', hκ'c, hκ'⟩ := exists_completion_map (algebraMap E' L') w' v' (fun x => hv' x)
  obtain ⟨μ, hμc, hμ⟩ := exists_completion_map jL v v' hjv
  have hcomm : ∀ a, μ (κ a) = κ' (i a) := fun a =>
    congrFun ((HeightOneSpectrum.denseRange_algebraMap E w).equalizer (hμc.comp hκc) (hκ'c.comp hic)
      (funext fun x => by simp only [Function.comp_apply, hκ, hμ, hjL, hij, hκ'])) a
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := E) (M := L)
  have hrange : Set.range jL ⊆ Submodule.span E' (jL '' (s : Set L)) := by
    rintro _ ⟨x, rfl⟩
    have hx : x ∈ Submodule.span E (s : Set L) := hs ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => simp
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | smul c a _ ha =>
      rw [Algebra.smul_def, map_mul, hjL, ← Algebra.smul_def]; exact Submodule.smul_mem _ _ ha
  have htop : Submodule.span E' (Set.range jL) = ⊤ := by
    have h1 := Algebra.adjoin_eq_span E' (Set.range jL)
    rw [hadj, Algebra.top_toSubmodule] at h1
    have hcl : (Submonoid.closure (Set.range jL) : Set L') = Set.range jL :=
      congrArg SetLike.coe (Submonoid.closure_eq (MonoidHom.mrange jL))
    rw [h1, hcl]
  have hspan : ∀ y : L', y ∈ Submodule.span E' (jL '' (s : Set L)) := fun y => by
    have hy : y ∈ Submodule.span E' (Set.range jL) := htop ▸ Submodule.mem_top
    exact (Submodule.span_le.2 hrange) hy
  letI : Algebra (w'.adicCompletion E') (v'.adicCompletion L') := κ'.toAlgebra
  haveI : ContinuousSMul (w'.adicCompletion E') (v'.adicCompletion L') :=
    continuousSMul_of_algebraMap _ _ hκ'c
  letI : NontriviallyNormedField (w'.adicCompletion E') := Valued.toNontriviallyNormedField _ _
  let M : Submodule (w'.adicCompletion E') (v'.adicCompletion L') :=
    Submodule.span _ ((fun y => algebraMap L' (v'.adicCompletion L') (jL y)) '' (s : Set L))
  haveI : FiniteDimensional (w'.adicCompletion E') M :=
    FiniteDimensional.span_of_finite _ (s.finite_toSet.image _)
  have hcl : IsClosed (M : Set (v'.adicCompletion L')) := Submodule.closed_of_finiteDimensional _
  have hM : ∀ y : L', algebraMap L' (v'.adicCompletion L') y ∈ M := fun y => by
    induction hspan y using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨x, hx, rfl⟩ := hz
      exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => simp
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | smul c a _ ha =>
      have e : algebraMap L' (v'.adicCompletion L') (c • a) =
          (algebraMap E' (w'.adicCompletion E') c) • algebraMap L' (v'.adicCompletion L') a := by
        rw [Algebra.smul_def c a, map_mul, ← hκ']; rfl
      rw [e]; exact Submodule.smul_mem _ _ ha
  have hMμ : ∀ z ∈ M, z ∈ Set.range μ := fun z hz => by
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨x, _, rfl⟩ := hz
      exact ⟨algebraMap L _ x, hμ x⟩
    | zero => exact ⟨0, map_zero μ⟩
    | add a b _ _ ha hb =>
      obtain ⟨a', rfl⟩ := ha; obtain ⟨b', rfl⟩ := hb; exact ⟨a' + b', map_add μ a' b'⟩
    | smul c a _ ha =>
      obtain ⟨a', rfl⟩ := ha
      exact ⟨κ (i.symm c) * a', by rw [map_mul, hcomm, i.apply_symm_apply]; rfl⟩
  have hsurj : Function.Surjective μ := fun y => by
    have hy : y ∈ (M : Set (v'.adicCompletion L')) :=
      (HeightOneSpectrum.denseRange_algebraMap L' v').induction_on
        (p := fun y => y ∈ (M : Set (v'.adicCompletion L'))) y hcl hM
    exact hMμ y hy
  exact ⟨RingEquiv.ofBijective μ ⟨μ.injective, hsurj⟩, hμc, fun x => hμ x⟩

end GlobalTheory.CompositumCompletion
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompletionBaseChangePlacesStatement
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completion_base_change_places : ∀ (E L E' L' : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Algebra E L] [Field E'] [NumberField E'] [Field L'] [NumberField L'] [Algebra E' L'] (w : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (𝓞 L)) (w' : HeightOneSpectrum (𝓞 E')) (v' : HeightOneSpectrum (𝓞 L')) (j : E →+* E') (jL : L →+* L') (i : w.adicCompletion E ≃+* w'.adicCompletion E'), (∀ x : 𝓞 E, algebraMap (𝓞 E) (𝓞 L) x ∈ v.asIdeal ↔ x ∈ w.asIdeal) → (∀ x : 𝓞 E', algebraMap (𝓞 E') (𝓞 L') x ∈ v'.asIdeal ↔ x ∈ w'.asIdeal) → (∀ x : 𝓞 L, RingOfIntegers.mapRingHom jL x ∈ v'.asIdeal ↔ x ∈ v.asIdeal) → (∀ x, jL (algebraMap E L x) = algebraMap E' L' (j x)) → Algebra.adjoin E' (Set.range jL) = ⊤ → Continuous i → (∀ x, i (algebraMap E _ x) = algebraMap E' _ (j x)) → ∃ iL : v.adicCompletion L ≃+* v'.adicCompletion L', Continuous iL ∧ ∀ x, iL (algebraMap L _ x) = algebraMap L' _ (jL x) := by
  first | exact @GlobalTheory.CompositumCompletion.exists_ringEquiv_completion | exact GlobalTheory.CompositumCompletion.exists_ringEquiv_completion | (intros; apply GlobalTheory.CompositumCompletion.exists_ringEquiv_completion <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneParamDualListSumAbsTwistSpecial
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneParamDualListSumAbsTwistSpecial
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
open TensorProduct Module
namespace GlobalTheory.WDDual
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']

theorem iso_sum_dual (a : WDRep h V) (b : WDRep h V') : (a.dual.sum b.dual).Iso (a.sum b).dual := by
  refine ⟨Module.dualProdDualEquivDual ℂ V V', fun σ x => ?_, fun x => ?_⟩
  · ext v <;> simp
  · ext v <;> simp

theorem iso_tensor_dual (a : WDRep h V) (b : WDRep h V') :
    (a.dual.tensor b.dual).Iso (a.tensor b).dual := by
  refine ⟨TensorProduct.dualDistribEquiv ℂ V V', fun σ x => ?_, fun x => ?_⟩
  · induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul f g =>
      refine TensorProduct.ext' fun m n => ?_
      simp [TensorProduct.dualDistrib_apply]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  · induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul f g =>
      refine TensorProduct.ext' fun m n => ?_
      simp [TensorProduct.dualDistrib_apply]
      ring
    | add x y hx hy => simp only [map_add (f := _), hx, hy]


omit [IsAlgClosure E Ω] in
theorem qPow_neg' (s : ℝ) : qPow w (-s) = (qPow w s)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← qPow_add, neg_add_cancel, qPow_zero])

theorem iso_tw_dual (a : WDRep h V) (s : ℝ) : (a.tw s).dual.Iso (a.dual.tw (-s)) := by
  refine ⟨LinearEquiv.refl ℂ _, fun σ f => ?_, fun f => rfl⟩
  ext v
  simp only [WDRep.tw, WDRep.dual_ρ, WDRep.twist_ρ, unrChar_apply, LinearEquiv.refl_apply,
    LinearMap.dualMap_apply, LinearMap.smul_apply, map_smul, smul_eq_mul, qPow_neg', map_inv, _root_.inv_zpow']
  congr 2
  simp

theorem shiftEnd_single {n : ℕ} (j : Fin n) :
    shiftEnd n (Pi.single j 1) = if hj : (j : ℕ) + 1 < n then Pi.single ⟨j + 1, hj⟩ 1 else 0 := by
  ext k
  rw [shiftEnd_apply]
  split_ifs with h1 h2 h2 <;> simp only [Pi.single_apply, Fin.ext_iff, Fin.val_mk, Pi.zero_apply] <;>
    split_ifs <;> first | rfl | (exfalso; have := k.2; have := j.2; omega)

theorem spEig_rev {n : ℕ} (i : Fin n) : WDRep.spEig w n i.rev = (WDRep.spEig w n i)⁻¹ := by
  rw [WDRep.spEig, WDRep.spEig, ← qPow_neg']
  congr 1
  rw [Fin.val_rev]
  have : (i : ℕ) + 1 ≤ n := i.2
  rw [Nat.cast_sub (by omega)]
  push_cast
  ring

theorem diagEnd_single {n : ℕ} (c : Fin n → ℂ) (j : Fin n) :
    WeilDeligne.diagEnd c (Pi.single j 1) = c j • Pi.single j (1 : ℂ) := by
  ext k; by_cases hk : k = j
  · subst hk; simp
  · simp [hk]

def spDualMap (n : ℕ) : Dual ℂ (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) where
  toFun f i := (-1 : ℂ) ^ (i : ℕ) * f (Pi.single i.rev 1)
  map_add' f g := by ext i; simp [mul_add]
  map_smul' c f := by ext i; simp; ring

theorem spDualMap_apply {n : ℕ} (f : Dual ℂ (Fin n → ℂ)) (i : Fin n) :
    spDualMap n f i = (-1 : ℂ) ^ (i : ℕ) * f (Pi.single i.rev 1) := rfl

theorem spDualMap_injective (n : ℕ) : Function.Injective (spDualMap n) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro f hf
  refine LinearMap.pi_ext fun j x => ?_
  have := congrFun hf j.rev
  rw [spDualMap_apply, Fin.rev_rev, Pi.zero_apply, mul_eq_zero] at this
  have h1 : f (Pi.single j 1) = 0 := this.resolve_left (pow_ne_zero _ (by norm_num))
  have h2 : (Pi.single j x : Fin n → ℂ) = x • Pi.single j (1 : ℂ) := by
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [h2, map_smul, h1, smul_zero]; simp

theorem iso_sp_dual (n : ℕ) : (WDRep.sp h n).dual.Iso (WDRep.sp h n) := by
  refine ⟨LinearMap.linearEquivOfInjective (spDualMap n) (spDualMap_injective n)
    (by simp [Subspace.dual_finrank_eq]), fun σ f => ?_, fun f => ?_⟩
  · ext i
    simp only [LinearMap.linearEquivOfInjective_apply, spDualMap_apply, WDRep.dual_ρ, WDRep.sp_ρ,
      LinearMap.dualMap_apply, diagEnd_single, map_smul, smul_eq_mul, WeilDeligne.diagEnd_apply, spEig_rev]
    simp
    ring
  · ext i
    simp only [LinearMap.linearEquivOfInjective_apply, spDualMap_apply, WDRep.dual_N, WDRep.sp_N,
      LinearMap.neg_apply, LinearMap.dualMap_apply, shiftEnd_single, shiftEnd_apply]
    by_cases hi : 1 ≤ (i : ℕ)
    · have hr : (i.rev : ℕ) + 1 < n := by rw [Fin.val_rev]; omega
      rw [dite_eq_left hr, if_pos hi]
      have he : (⟨(i.rev : ℕ) + 1, hr⟩ : Fin n) = (⟨(i : ℕ) - 1, by omega⟩ : Fin n).rev := by
        ext; simp only [Fin.val_rev]; omega
      rw [he]
      obtain ⟨k, hk⟩ : ∃ k, (i : ℕ) = k + 1 := ⟨(i : ℕ) - 1, by omega⟩
      simp only [hk, Nat.add_sub_cancel, pow_succ]
      ring
    · have hr : ¬ (i.rev : ℕ) + 1 < n := by rw [Fin.val_rev]; omega
      rw [dite_eq_right hr, if_neg hi]
      simp

namespace WDClass

theorem lpDual_lpZero : (WD.lpZero (h := h)).lpDual = WD.lpZero (h := h) := by
  rw [WD.lpZero, WD.lpDual_mk]
  exact WD.sound ⟨LinearEquiv.ofFinrankEq _ _ (by simp [Subspace.dual_finrank_eq]),
    fun _ _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩

theorem lpDual_lpSum (x y : WD h) : (x.lpSum y).lpDual = x.lpDual.lpSum y.lpDual := by
  induction x using WD.ind with
  | hP n a =>
    induction y using WD.ind with
    | hP m b =>
      rw [WD.lpSum_mk, WD.lpDual_mk, WD.lpDual_mk, WD.lpDual_mk, WD.lpSum_mk]
      exact WD.sound (iso_sum_dual a b).symm

theorem lpDual_sumList (l : List (WD h)) : (sumList l).lpDual = sumList (l.map WD.lpDual) := by
  induction l with
  | nil => exact lpDual_lpZero
  | cons x l ih =>
    show (x.lpSum (sumList l)).lpDual = x.lpDual.lpSum (sumList (l.map WD.lpDual))
    rw [lpDual_lpSum, ih]

theorem lpDual_lpTw (y : WD h) (s : ℝ) : (y.lpTw s).lpDual = y.lpDual.lpTw (-s) := by
  induction y using WD.ind with
  | hP n a =>
    rw [WD.lpTw_mk, WD.lpDual_mk, WD.lpDual_mk, WD.lpTw_mk]
    exact WD.sound (iso_tw_dual a s)

theorem lpDual_lpChar_lpSp (y : WD h) (n : ℕ) :
    (y.lpChar (WD.lpSp (h := h) n)).lpDual = y.lpDual.lpChar (WD.lpSp (h := h) n) := by
  induction y using WD.ind with
  | hP m a =>
    rw [WD.lpSp, WD.lpChar_mk, WD.lpDual_mk, WD.lpDual_mk, WD.lpChar_mk]
    exact WD.sound ((iso_tensor_dual a (WDRep.sp h n)).symm.trans
      ((WDRep.Iso.refl a.dual).tensor (iso_sp_dual n)))

end WDClass

theorem lpDual_sum_tw_sp : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w),
    (∀ l : List (WD h), (sumList l).lpDual = sumList (l.map WD.lpDual)) ∧
    (∀ (y : WD h) (s : ℝ), (y.lpTw s).lpDual = y.lpDual.lpTw (-s)) ∧
    ∀ (y : WD h) (n : ℕ), (y.lpChar (WD.lpSp (h := h) n)).lpDual = y.lpDual.lpChar (WD.lpSp (h := h) n) :=
  fun _ _ _ _ _ _ _ _ _ _ =>
    ⟨WDClass.lpDual_sumList, WDClass.lpDual_lpTw, WDClass.lpDual_lpChar_lpSp⟩

end GlobalTheory.WDDual
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneParamDualListSumAbsTwistSpecialStatement
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilDeligneParam_dual_listSum_absTwist_special : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w), (∀ l : List (WD h), (sumList l).lpDual = sumList (l.map WD.lpDual)) ∧ (∀ (y : WD h) (s : ℝ), (y.lpTw s).lpDual = y.lpDual.lpTw (-s)) ∧ ∀ (y : WD h) (n : ℕ), (y.lpChar (WD.lpSp (h := h) n)).lpDual = y.lpDual.lpChar (WD.lpSp (h := h) n) := by
  intro E Ω _ _ _ _ _ A w h
  have dual_sp (y : WD h) (n : ℕ) :
      (y.lpChar (WD.lpSp (h := h) n)).lpDual = y.lpDual.lpChar (WD.lpSp (h := h) n) := by
    induction y using WD.ind with
    | hP m a =>
      rw [WD.lpSp, WD.lpChar_mk, WD.lpDual_mk, WD.lpDual_mk, WD.lpChar_mk]
      exact WD.sound ((GlobalTheory.WDDual.iso_tensor_dual a (WDRep.sp (h := h) n)).symm.trans
        ((WDRep.Iso.refl a.dual).tensor (GlobalTheory.WDDual.iso_sp_dual (h := h) n)))
  exact ⟨GlobalTheory.WDDual.WDClass.lpDual_sumList, GlobalTheory.WDDual.WDClass.lpDual_lpTw,
    dual_sp⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalArtinReciprocityMapUnique
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalArtinReciprocityMapUnique
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open Neutral.B1 Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat

namespace GlobalTheory.ArtinUniq

variable {E : Type} [Field E] [NumberField E]

theorem eq_one_of_unit_unif {B : Type} [Group B] (v : HeightOneSpectrum (𝓞 E)) (f : (v.adicCompletion E)ˣ →* B)
    (hu : ∀ x, IsUnitAt v x → f x = 1) (hp : ∀ x, IsUnifAt v x → f x = 1) (x : (v.adicCompletion E)ˣ) : f x = 1 := by
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer E v
  have hv : Valued.v ((π : E) : v.adicCompletion E) = WithZero.exp (-1) := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]
  have hπ0 : ((π : E) : v.adicCompletion E) ≠ 0 := by
    intro h
    rw [h, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  let p : (v.adicCompletion E)ˣ := Units.mk0 _ hπ0
  have hpv : Valued.v (p : v.adicCompletion E) = WithZero.exp (-1) := hv
  have hfp : f p = 1 := hp p hpv
  have key : ∀ n : ℤ, ∀ y : (v.adicCompletion E)ˣ, Valued.v (y : v.adicCompletion E) = WithZero.exp n → f y = 1 := by
    intro n
    induction n using Int.induction_on with
    | zero => exact fun y hy => hu y (by show Valued.v _ = 1; rw [hy, WithZero.exp_zero])
    | succ n ih =>
      intro y hy
      have h1 : f (y * p) = 1 := ih _ (by
        rw [Units.val_mul, map_mul, hy, hpv, ← WithZero.exp_add]
        congr 1
        ring)
      rwa [map_mul, hfp, mul_one] at h1
    | pred n ih =>
      intro y hy
      have h1 : f (y * p⁻¹) = 1 := ih _ (by
        rw [Units.val_mul, map_mul, hy, Units.val_inv_eq_inv_val, map_inv₀, hpv, ← WithZero.exp_neg,
          ← WithZero.exp_add]
        congr 1
        ring)
      rwa [map_mul, map_inv, hfp, inv_one, mul_one] at h1
  have h0 : Valued.v (x : v.adicCompletion E) ≠ 0 := by simp
  exact key _ x (WithZero.exp_log h0).symm

variable {Ω : Type} [Field Ω] [Algebra E Ω]

theorem unif_eq {art art' : Ideles E →* Gab E Ω} (ha : IsGlobalArtin art) (ha' : IsGlobalArtin art')
    {B : Type} [Group B] (χ : Gab E Ω →* B) (v : HeightOneSpectrum (𝓞 E))
    (hu' : ∀ y, IsUnitAt v y → χ (art' (localIdele E v y)) = 1) (x : (v.adicCompletion E)ˣ) (hx : IsUnifAt v x) :
    χ (art (localIdele E v x)) = χ (art' (localIdele E v x)) := by
  obtain ⟨A, hA⟩ := ReciprocityTheory.Gal.exists_isPlaceOver Ω v
  obtain ⟨σ, hσ, e⟩ := (ha.frob v A hA _).mp ⟨x, hx, rfl⟩
  obtain ⟨y, hy, e'⟩ := (ha'.frob v A hA _).mpr ⟨σ, hσ, e⟩
  have hxy : IsUnitAt v (x * y⁻¹) := by
    show Valued.v _ = 1
    have hy0 : Valued.v (y : v.adicCompletion E) ≠ 0 := by simp
    rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hx, ← hy, mul_inv_cancel₀ hy0]
  have h2 : localIdele E v x = localIdele E v (x * y⁻¹) * localIdele E v y := by
    rw [← map_mul, inv_mul_cancel_right]
  conv_rhs => rw [h2, map_mul, map_mul, hu' _ hxy, one_mul, e']

end GlobalTheory.ArtinUniq

namespace GlobalTheory.ArtinUniq

variable {E : Type} [Field E] [NumberField E]

theorem eq_infPart {B : Type} [CommGroup B] (D : Ideles E →* B) (hD : IsOpen (D.ker : Set (Ideles E)))
    (hloc : ∀ v x, D (localIdele E v x) = 1) (x : Ideles E) :
    D x = D (GlobalTheory.HeckeSplit.infIdele E (GlobalTheory.HeckeSplit.infPart E x)) := by
  have hnhds : {z : Ideles E | D z = D x} ∈ nhds x := by
    have e : {z : Ideles E | D z = D x} = (fun z => x⁻¹ * z) ⁻¹' (D.ker : Set (Ideles E)) := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv]
      rw [inv_mul_eq_one, eq_comm]
    rw [e]
    exact ((continuous_const.mul continuous_id).isOpen_preimage _ hD).mem_nhds (by simp)
  obtain ⟨T, hT⟩ := ((GlobalTheory.HeckeSplit.tendsto_truncIdele x).eventually hnhds).exists
  have h1 : ∀ v ∈ T, D (HeckeValGen.localIdele E v (GlobalTheory.HeckeSplit.finPart E v x)) = 1 := fun v _ => hloc v _
  rw [← show D (GlobalTheory.HeckeSplit.truncIdele x T) = D x from hT, GlobalTheory.HeckeSplit.truncIdele, map_mul, map_prod,
    Finset.prod_eq_one h1, mul_one]

theorem eq_one_of_local {B : Type} [CommGroup B] (D : Ideles E →* B) (hD : IsOpen (D.ker : Set (Ideles E)))
    (hdiag : ∀ k : Eˣ, D (diagUnits E k) = 1) (hinf : ∀ y ∈ infConn E, D y = 1)
    (hloc : ∀ v x, D (localIdele E v x) = 1) : D = 1 := by
  ext x
  rw [eq_infPart D hD hloc x, MonoidHom.one_apply]
  set y := GlobalTheory.HeckeSplit.infPart E x
  let C := Subgroup.connectedComponentOfOne (InfiniteAdeleRing E)ˣ
  have hopen : IsOpen ((fun z => y⁻¹ * z) ⁻¹' (C : Set (InfiniteAdeleRing E)ˣ)) :=
    (continuous_const.mul continuous_id).isOpen_preimage _ (isOpen_connectedComponentOfOne_inf E)
  obtain ⟨k, hk⟩ := (denseRange_units_inf E).exists_mem_open hopen ⟨y, by simp [C.one_mem]⟩
  set kinf : (InfiniteAdeleRing E)ˣ := Units.map (algebraMap E (InfiniteAdeleRing E)).toMonoidHom k with hkinf
  have hk' : y⁻¹ * kinf ∈ C := hk
  have h1 : D (GlobalTheory.HeckeSplit.infIdele E kinf) = 1 := by
    have h := eq_infPart D hD hloc (diagUnits E k)
    have e : GlobalTheory.HeckeSplit.infPart E (diagUnits E k) = kinf := Units.ext rfl
    rw [e, hdiag k] at h
    exact h.symm
  have h2 : D (GlobalTheory.HeckeSplit.infIdele E (y⁻¹ * kinf)) = 1 := hinf _ ⟨_, hk', rfl⟩
  have e : y = kinf * (y⁻¹ * kinf)⁻¹ := by group
  rw [e, map_mul, map_inv, map_mul, map_inv, h1, h2, inv_one, mul_one]

end GlobalTheory.ArtinUniq

namespace GlobalTheory.ArtinUniq

theorem val_div_sub_one_le {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {a c : K}
    (hc : c ≠ 0) {N m : ℕ} (hm : (WithZero.log (w.valuation K c)).natAbs ≤ m)
    (h : w.valuation K (a - c) ≤ WithZero.exp (-((N : ℤ) + m))) :
    w.valuation K (a / c - 1) ≤ WithZero.exp (-(N : ℤ)) := by
  have hv : w.valuation K c ≠ 0 := (Valuation.ne_zero_iff _).mpr hc
  rw [div_sub_one hc, map_div₀, ← WithZero.exp_log hv, div_le_iff₀ (by simp), ← WithZero.exp_add]
  refine h.trans (WithZero.exp_le_exp.mpr ?_)
  have : -(m : ℤ) ≤ WithZero.log (w.valuation K c) := by omega
  omega

theorem val_le_of_le {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {x : K} {N N' : ℤ}
    (h : w.valuation K x ≤ WithZero.exp (-N)) (hN : N' ≤ N) : w.valuation K x ≤ WithZero.exp (-N') :=
  h.trans (WithZero.exp_le_exp.mpr (by omega))

theorem globalArtin_unique : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (art art' : Neutral.B1.Ideles E →* GlobalTheory.HeckeGal.Gab E Ω), GlobalTheory.HeckeGal.IsGlobalArtin art →
    GlobalTheory.HeckeGal.IsGlobalArtin art' → art = art' := by
  intro E Ω _ _ _ _ _ art art' ha ha'
  classical
  ext x
  rw [← div_eq_one]
  refine GlobalTheory.GabSep.eq_one_of_forall_isOpen_subgroup E Ω _ fun U hU => ?_
  let χ : Gab E Ω →* Gab E Ω ⧸ U := QuotientGroup.mk' U
  have hker : ∀ a : Ideles E →* Gab E Ω, IsGlobalArtin a → IsOpen ((χ.comp a).ker : Set (Ideles E)) := by
    intro a h
    have e : ((χ.comp a).ker : Set (Ideles E)) = a ⁻¹' U := by
      ext y
      simp [χ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
    rw [e]
    exact hU.preimage h.quot.continuous
  have hdiag : ∀ a : Ideles E →* Gab E Ω, IsGlobalArtin a → ∀ k : Eˣ, a (diagUnits E k) = 1 := by
    intro a h k
    have hk : diagUnits E k ∈ a.ker := by
      rw [h.ker]
      exact Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_left ⟨k, rfl⟩)
    exact hk
  have hinf : ∀ a : Ideles E →* Gab E Ω, IsGlobalArtin a → ∀ y ∈ infConn E, a y = 1 := by
    intro a h y hy
    have hk : y ∈ a.ker := by
      rw [h.ker]
      exact Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_right hy)
    exact hk
  let ψ : Ideles E →* Gab E Ω ⧸ U := χ.comp art
  let ψ' : Ideles E →* Gab E Ω ⧸ U := χ.comp art'
  let D : Ideles E →* Gab E Ω ⧸ U := ψ / ψ'
  let V : Subgroup (Ideles E) := ψ.ker ⊓ ψ'.ker
  have hV : IsOpen (V : Set (Ideles E)) := (hker art ha).inter (hker art' ha')
  have hDV : ∀ z ∈ V, D z = 1 := fun z hz => by
    show ψ z / ψ' z = 1
    rw [MonoidHom.mem_ker.mp hz.1, MonoidHom.mem_ker.mp hz.2, div_one]
  have hDo : IsOpen (D.ker : Set (Ideles E)) := Subgroup.isOpen_mono (fun z hz => hDV z hz) hV
  have hDd : ∀ k : Eˣ, D (diagUnits E k) = 1 := fun k => by
    show χ (art _) / χ (art' _) = 1
    rw [hdiag art ha, hdiag art' ha', map_one, div_one]
  have hDi : ∀ y ∈ infConn E, D y = 1 := fun y hy => by
    show χ (art _) / χ (art' _) = 1
    rw [hinf art ha y hy, hinf art' ha' y hy, map_one, div_one]
  obtain ⟨S, M, -, hSu, hSc⟩ := GlobalTheory.OpenIdeleCongr.open_subgroup_contains_congr E V hV ∅

  have hgood : ∀ v ∉ S, ∀ z, D (localIdele E v z) = 1 := fun v hv z => by
    refine eq_one_of_unit_unif v (D.comp (localIdele E v)) (fun y hy => hDV _ (hSu v hv y hy)) (fun y hy => ?_) z
    show ψ _ / ψ' _ = 1
    rw [div_eq_one]
    exact unif_eq ha ha' χ v (fun y' hy' => MonoidHom.mem_ker.mp (hSu v hv y' hy').2) y hy

  have hbad : ∀ v ∈ S, ∀ z, D (localIdele E v z) = 1 := fun v hv z => by
    have ho : IsOpen ((D.comp (localIdele E v)).ker : Set (v.adicCompletion E)ˣ) :=
      hDo.preimage (GlobalTheory.Mem.UnrAe.continuous_localIdele v)
    have ho1 : IsOpen (((1 : (v.adicCompletion E)ˣ →* Gab E Ω ⧸ U)).ker : Set (v.adicCompletion E)ˣ) := by
      rw [MonoidHom.ker_one]
      exact isOpen_univ
    refine GlobalTheory.units_adicCompletion_hom_ext E v _ (D.comp (localIdele E v)) 1 ho ho1 (fun c => ?_) z
    rw [MonoidHom.one_apply, MonoidHom.comp_apply, ← locUnit_apply]
    let m : ℕ := (WithZero.log (v.valuation E (c : E))).natAbs
    obtain ⟨a, hap, hapos⟩ :=
      GlobalTheory.FinPlaceApproxPos.approxpos_target E S (fun u => if u = v then (c : E) else 1) (M + 1 + m)
    have haW : v.valuation E (a - c) ≤ WithZero.exp (-(((M + 1 : ℕ) : ℤ) + m)) := by
      have := hap v hv
      rw [if_pos rfl] at this
      exact val_le_of_le v this (by push_cast; omega)
    have hz : v.valuation E (a / c - 1) ≤ WithZero.exp (-((M + 1 : ℕ) : ℤ)) :=
      val_div_sub_one_le v c.ne_zero le_rfl haW
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [zero_div, zero_sub, Valuation.map_neg, map_one, ← WithZero.exp_zero, WithZero.exp_le_exp] at hz
      push_cast at hz
      omega
    let au : Eˣ := Units.mk0 a ha0
    let q : Eˣ := au / c
    have hq : (q : E) = a / c := by simp [q, au]
    have hqV : locUnit E v q ∈ V := hSc v hv q (by rw [hq]; exact val_le_of_le v hz (by push_cast; omega))
    have hprod := GlobalTheory.ProdLocUnitPos.prod_locUnit_eq_one_of_pos E _ D hDo hDd hDi au (fun φ => hapos φ) S
      (fun u hu => by rw [locUnit_apply]; exact hgood u hu _)
    rw [Finset.prod_eq_single_of_mem v hv (fun u hu hne => hDV _ (hSc u hu au (by
      have := hap u hu
      rw [if_neg hne] at this
      exact val_le_of_le u this (by push_cast; omega))))] at hprod
    have e : au = c * q := by simp [q]
    rw [e, map_mul, map_mul, hDV _ hqV, mul_one] at hprod
    exact hprod
  have hD : D = 1 := eq_one_of_local D hDo hDd hDi fun v z => by
    by_cases hv : v ∈ S
    · exact hbad v hv z
    · exact hgood v hv z
  have h1 : χ (art x / art' x) = 1 := by
    rw [_root_.map_div]
    exact DFunLike.congr_fun hD x
  exact (QuotientGroup.eq_one_iff _).mp h1

end GlobalTheory.ArtinUniq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalArtinReciprocityMapUniqueStatement
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.globalArtinReciprocityMap_unique : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (art art' : Neutral.B1.Ideles E →* GlobalTheory.HeckeGal.Gab E Ω), GlobalTheory.HeckeGal.IsGlobalArtin art → GlobalTheory.HeckeGal.IsGlobalArtin art' → art = art' := by
  first | exact @GlobalTheory.ArtinUniq.globalArtin_unique | exact GlobalTheory.ArtinUniq.globalArtin_unique | (intros; apply GlobalTheory.ArtinUniq.globalArtin_unique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormVZpowDegEq
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands

theorem normV_zpow_deg_eq {K L Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω]
    [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] {A : ValuationSubring Ω}
    {v : HeightOneSpectrum (𝓞 K)} {v' : HeightOneSpectrum (𝓞 L)} {h : IsPlaceOver A v} {h' : IsPlaceOver A v'}
    (σ' : Weil h') (σ : Weil h) (hσ : ∀ z : Ω, (σ : G K Ω) z = (σ' : G L Ω) z) :
    ((normV v' : ℕ) : ℝ) ^ deg σ' = ((normV v : ℕ) : ℝ) ^ deg σ := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  obtain ⟨a, b, ha⟩ := σ'.2
  obtain ⟨c, d, hc⟩ := σ.2
  rw [deg_eq ha, deg_eq hc]
  set q' := normV v' with hq'
  set q := normV v with hq
  have hq'0 : 0 < q' := (zero_lt_one.trans (one_lt_normV v'))
  have hq0 : 0 < q := (zero_lt_one.trans (one_lt_normV v))
  have key : ∀ x : Ω, A.valuation x ≤ 1 →
      A.valuation (x ^ (q' ^ a * q ^ d) - x ^ (q ^ c * q' ^ b)) < 1 := by
    intro x hx
    have hy : A.valuation ((σ' : G L Ω) x) ≤ 1 := val_apply_le_one ha.1 hx
    have h1 := cong_pow (val_pow_le_one hy _) (val_pow_le_one hx _) (ha.2 x hx) (q ^ d)
    have h2' := hc.2 x hx
    rw [hσ] at h2'
    have h2 := cong_pow (val_pow_le_one hy _) (val_pow_le_one hx _) h2' (q' ^ b)
    rw [← pow_mul, ← pow_mul] at h1 h2
    rw [mul_comm (q ^ d) (q' ^ b)] at h2
    exact cong_trans (cong_symm h1) h2
  have hN : q' ^ a * q ^ d = q ^ c * q' ^ b := by
    rcases lt_trichotomy (q' ^ a * q ^ d) (q ^ c * q' ^ b) with hlt | heq | hgt
    · obtain ⟨x, hx, hx'⟩ := exists_not_cong_pow (A := A)
        (Nat.mul_pos (pow_pos hq'0 a) (pow_pos hq0 d)) hlt
      exact absurd (cong_symm (key x hx)) hx'
    · exact heq
    · obtain ⟨x, hx, hx'⟩ := exists_not_cong_pow (A := A)
        (Nat.mul_pos (pow_pos hq0 c) (pow_pos hq'0 b)) hgt
      exact absurd (key x hx) hx'
  have hR : ((q' : ℕ) : ℝ) ^ a * ((q : ℕ) : ℝ) ^ d = ((q : ℕ) : ℝ) ^ c * ((q' : ℕ) : ℝ) ^ b := by
    exact_mod_cast hN
  have h1 : ((q' : ℕ) : ℝ) ≠ 0 := by positivity
  have h2 : ((q : ℕ) : ℝ) ≠ 0 := by positivity
  rw [zpow_sub₀ h1, zpow_sub₀ h2, zpow_natCast, zpow_natCast, zpow_natCast, zpow_natCast,
    div_eq_div_iff (pow_ne_zero _ h1) (pow_ne_zero _ h2)]
  linarith

end GlobalTheory.LocLanglands

namespace GlobalTheory.LocLanglands

end GlobalTheory.LocLanglands
end
