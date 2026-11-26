module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.OrthogonalLatticeSameGenus

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.ZMemPerp
open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Wb

variable (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)

abbrev nX : Submodule D.host.E (perpS (VS D) F0.X) := F0.X.comap (perpS (VS D) F0.X).subtype

theorem hT_X_perp {x y : (VS D).V} (hx : x ∈ F0.X) (hy : y ∈ perpS (VS D) F0.X) : (VS D).hT x y = 0 :=
  hy x hx

theorem hT_perp_X {x y : (VS D).V} (hx : x ∈ perpS (VS D) F0.X) (hy : y ∈ F0.X) : (VS D).hT x y = 0 := by
  rw [← (VS D).herm.eq y x, hx y hy, map_zero]

def hWbFun (x y : WbQ D F0) : D.host.E :=
  Quotient.liftOn₂' x y (fun a b => (VS D).hT a.1 b.1) (by
    intro a₁ b₁ a₂ b₂ ha hb
    have ha' : a₁.1 - a₂.1 ∈ F0.X := by
      have := (Submodule.quotientRel_def (nX D F0)).1 ha
      simpa using this
    have hb' : b₁.1 - b₂.1 ∈ F0.X := by
      have := (Submodule.quotientRel_def (nX D F0)).1 hb
      simpa using this
    have e1 : (VS D).hT (a₁.1 - a₂.1) b₁.1 = 0 := hT_X_perp D F0 ha' b₁.2
    have e2 : (VS D).hT a₂.1 (b₁.1 - b₂.1) = 0 := hT_perp_X D F0 a₂.2 hb'
    simp only [map_sub, LinearMap.sub_apply] at e1 e2
    show (VS D).hT a₁.1 b₁.1 = (VS D).hT a₂.1 b₂.1
    linear_combination e1 + e2)

theorem hWbFun_mk (a b : perpS (VS D) F0.X) :
    hWbFun D F0 (Submodule.Quotient.mk a) (Submodule.Quotient.mk b) = (VS D).hT a.1 b.1 := rfl

def hWb : WbQ D F0 →ₗ⋆[D.host.E] WbQ D F0 →ₗ[D.host.E] D.host.E :=
  LinearMap.mk₂'ₛₗ (starRingEnd D.host.E) (RingHom.id D.host.E) (hWbFun D F0)
    (by
      intro x₁ x₂ y
      induction x₁ using Submodule.Quotient.induction_on with | H a₁ => ?_
      induction x₂ using Submodule.Quotient.induction_on with | H a₂ => ?_
      induction y using Submodule.Quotient.induction_on with | H b => ?_
      rw [← Submodule.Quotient.mk_add, hWbFun_mk, hWbFun_mk, hWbFun_mk]
      simp)
    (by
      intro c x y
      induction x using Submodule.Quotient.induction_on with | H a => ?_
      induction y using Submodule.Quotient.induction_on with | H b => ?_
      rw [← Submodule.Quotient.mk_smul, hWbFun_mk, hWbFun_mk]
      simp)
    (by
      intro x y₁ y₂
      induction x using Submodule.Quotient.induction_on with | H a => ?_
      induction y₁ using Submodule.Quotient.induction_on with | H b₁ => ?_
      induction y₂ using Submodule.Quotient.induction_on with | H b₂ => ?_
      rw [← Submodule.Quotient.mk_add, hWbFun_mk, hWbFun_mk, hWbFun_mk]
      simp)
    (by
      intro c x y
      induction x using Submodule.Quotient.induction_on with | H a => ?_
      induction y using Submodule.Quotient.induction_on with | H b => ?_
      rw [← Submodule.Quotient.mk_smul, hWbFun_mk, hWbFun_mk]
      simp)

theorem hWb_mk (a b : perpS (VS D) F0.X) :
    hWb D F0 (Submodule.Quotient.mk a) (Submodule.Quotient.mk b) = (VS D).hT a.1 b.1 := rfl

theorem z_mem_perp : F0.z ∈ perpS (VS D) F0.X := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, rfl⟩ := hy
    exact F0.z_orth a
  | zero => simp
  | add y w _ _ h1 h2 => simp [h1, h2]
  | smul c y _ h => simp [h]

def zbar : WbQ D F0 := Submodule.Quotient.mk ⟨F0.z, z_mem_perp D F0⟩

theorem hWb_zbar : hWb D F0 (zbar D F0) (zbar D F0) = -T := by
  rw [zbar, hWb_mk]
  exact F0.z_norm

def Mof (Λ : Submodule (𝓞 D.host.E) (VS D).V) : Submodule (𝓞 D.host.E) (WbQ D F0) :=
  (Λ.comap ((perpS (VS D) F0.X).subtype.restrictScalars (𝓞 D.host.E))).map
    ((nX D F0).mkQ.restrictScalars (𝓞 D.host.E))

end Wb

def WbDef : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u)),
    Formalism.HermitianLattices.Ext.L3.IsTotPosDef (hPerp (hWb D F0) (zbar D F0)) ∧
      finrank D.host.E (wPerp (hWb D F0) (zbar D F0)) = D.R.k

def RowM : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u)) (Λ : Submodule (𝓞 D.host.E) (VS D).V),
    IsRowLat D F0 Λ → IsGlueLat (hWb D F0) (zbar D F0) (Mof D F0 Λ)

def RowSurj : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u)) (M : Submodule (𝓞 D.host.E) (WbQ D F0)),
    IsGlueLat (hWb D F0) (zbar D F0) M → ∃ Λ, IsRowLat D F0 Λ ∧ Mof D F0 Λ = M

def RowClass : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u)) (Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V),
    IsRowLat D F0 Λ → IsRowLat D F0 Λ' →
      ((∃ γ ∈ stabF D F0, Formalism.HermitianLatticesTheory.gmap γ Λ = Λ') ↔
        ∃ σ ∈ hz (hWb D F0) (zbar D F0), Formalism.HermitianLatticesTheory.gmap σ (Mof D F0 Λ) = Mof D F0 Λ')

def RowWeight : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u)) (Λ : Submodule (𝓞 D.host.E) (VS D).V),
    IsRowLat D F0 Λ → Nat.card (autLz D F0 Λ) = Nat.card (stabZ (hWb D F0) (zbar D F0) (Mof D F0 Λ))

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.CountCoeEqMultiplicity
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.VFEqEmultiplicity
open NumberField Module IsDedekindDomain Formalism.HermitianLattices.Ext.L3

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.R6

section

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

theorem vF_eq_emultiplicity {F : Type} [Field F] [NumberField F] (𝔭 : Ideal (𝓞 F)) (h𝔭 : 𝔭.IsPrime)
    (h0 : 𝔭 ≠ ⊥) (α : 𝓞 F) (hα : α ≠ 0) :
    ((vF 𝔭 α : ℕ) : ℕ∞) = emultiplicity 𝔭 (Ideal.span {α}) := by
  have hs : Ideal.span {α} ≠ ⊥ := by simpa using hα
  have hfm : FiniteMultiplicity 𝔭 (Ideal.span {α}) :=
    FiniteMultiplicity.of_prime_left (Ideal.prime_of_isPrime h0 h𝔭) hs
  rw [hfm.emultiplicity_eq_multiplicity]
  congr 1
  unfold vF
  have hset : {e : ℕ | α ∈ 𝔭 ^ e} = Set.Iic (multiplicity 𝔭 (Ideal.span {α})) := by
    ext e
    simp only [Set.mem_ofPred_eq, Set.mem_Iic]
    rw [← hfm.pow_dvd_iff_le_multiplicity, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  rw [hset, csSup_Iic]

end

theorem countExt_single (K F : Type) [Field K] [NumberField K] [Field F] [NumberField F] [Algebra F K]
    (𝔭 : Ideal (𝓞 F)) (P : HeightOneSpectrum (𝓞 K)) (α : 𝓞 F) (h𝔭 : 𝔭.IsMaximal)
    (hP : P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 K)) = 𝔭) (hα : α ≠ 0) :
    FractionalIdeal.count K P (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (algebraMap F K (α : F))) =
      ((P.asIdeal.ramificationIdx (𝓞 F) * vF 𝔭 α : ℕ) : ℤ) := by
  have h0 : 𝔭 ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (NumberField.RingOfIntegers.not_isField F)
  haveI : P.asIdeal.LiesOver 𝔭 := ⟨by rw [Ideal.under_def, hP]⟩
  set β : 𝓞 K := algebraMap (𝓞 F) (𝓞 K) α
  have hβ : β ≠ 0 := by
    intro h
    apply hα
    exact (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K)) (by rw [map_zero]; exact h)
  have hsβ : Ideal.span {β} ≠ ⊥ := by simpa using hβ
  have hsα : Ideal.span {α} ≠ ⊥ := by simpa using hα
  have hK : algebraMap F K (α : F) = algebraMap (𝓞 K) K β := rfl
  rw [hK, ← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe K P hsβ,
    Ideal.count_associates_factors_eq hsβ P.isPrime P.ne_bot,
    HeightOneSpectrum.count_normalizedFactors_eq_multiplicity hsβ P]
  congr 1
  have hfmP : FiniteMultiplicity P.asIdeal (Ideal.span {β}) :=
    FiniteMultiplicity.of_prime_left P.prime hsβ
  have hmap : Ideal.span {β} = (Ideal.span {α}).map (algebraMap (𝓞 F) (𝓞 K)) := by
    rw [Ideal.map_span, Set.image_singleton]
  have he := Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx'_mul hsα
    (Ideal.prime_of_isPrime h0 h𝔭.isPrime).irreducible P.irreducible P.ne_bot
  rw [← hmap, hfmP.emultiplicity_eq_multiplicity, ← vF_eq_emultiplicity 𝔭 h𝔭.isPrime h0 α hα,
    Ideal.ramificationIdx'_eq_ramificationIdx 𝔭 P.asIdeal h0] at he
  exact_mod_cast he

theorem count_extension : CountExt := by
  intro K F _ _ _ _ _ n 𝔭 P α h𝔭 hP hα
  have h0 : 𝔭 ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (NumberField.RingOfIntegers.not_isField F)
  have hprod : (∏ j, ((α j : 𝓞 F) : F)) = ((∏ j, α j : 𝓞 F) : F) := by simp
  have hne : (∏ j, α j) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => hα j
  rw [hprod, countExt_single K F 𝔭 P _ h𝔭 hP hne]
  congr 2
  have key : ((vF 𝔭 (∏ j, α j) : ℕ) : ℕ∞) = ((∑ j, vF 𝔭 (α j) : ℕ) : ℕ∞) := by
    rw [vF_eq_emultiplicity 𝔭 h𝔭.isPrime h0 _ hne, ← Ideal.prod_span_singleton, Nat.cast_sum]
    rw [Finset.emultiplicity_prod (Ideal.prime_of_isPrime h0 h𝔭.isPrime)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [vF_eq_emultiplicity 𝔭 h𝔭.isPrime h0 _ (hα j)]
  exact_mod_cast key

end PI.UnitaryGroupMassFormula.CntFormula.R6
end
end

open NumberField Module IsDedekindDomain Formalism.HermitianLattices.Ext.L3

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.R6

theorem count_coe_eq_multiplicity {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (v : HeightOneSpectrum R) {I : Ideal R} (hI : I ≠ ⊥) :
    FractionalIdeal.count K v (I : FractionalIdeal (nonZeroDivisors R) K) = (multiplicity v.asIdeal I : ℤ) := by
  rw [FractionalIdeal.count_coeIdeal K v hI, Ideal.count_associates_factors_eq hI v.isPrime v.ne_bot,
    HeightOneSpectrum.count_normalizedFactors_eq_multiplicity hI v]

theorem eq_of_count_eq {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] {I J : FractionalIdeal (nonZeroDivisors R) K} (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ v : HeightOneSpectrum R, FractionalIdeal.count K v I = FractionalIdeal.count K v J) : I = J := by
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI,
    ← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hJ]
  simp_rw [h]

def belowP {K F : Type} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra F K]
    (P : HeightOneSpectrum (𝓞 K)) : HeightOneSpectrum (𝓞 F) where
  asIdeal := P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 K))
  isPrime := P.isPrime.comap _
  ne_bot := by
    intro h
    have hmax : (P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 K))).IsMaximal :=
      Ideal.isMaximal_under_of_isIntegral_of_isMaximal P.asIdeal
    exact Ring.ne_bot_of_isMaximal_of_not_isField hmax (NumberField.RingOfIntegers.not_isField F) h

theorem exists_above {K F : Type} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra F K]
    (v : HeightOneSpectrum (𝓞 F)) : ∃ P : HeightOneSpectrum (𝓞 K), belowP P = v := by
  have hker : RingHom.ker (algebraMap (𝓞 F) (𝓞 K)) ≤ v.asIdeal := by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K))]
    exact bot_le
  haveI := v.isMaximal
  obtain ⟨Q, hQ, hQc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral v.asIdeal hker
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    apply v.ne_bot
    rw [← hQc, Ideal.under_def, ← RingHom.ker_eq_comap_bot,
      (RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K))]
  refine ⟨⟨Q, hQ.isPrime, hQ0⟩, ?_⟩
  ext1
  exact hQc

theorem norm_mass_assembly : NormAssembly := by
  intro K F _ _ _ _ _ h2 J w hJ0 hc
  classical
  set wv : HeightOneSpectrum (𝓞 F) → ℕ := fun v => w v.asIdeal with hwv

  have hcJ : ∀ P : HeightOneSpectrum (𝓞 K), FractionalIdeal.count K P J =
      ((P.asIdeal.ramificationIdx (𝓞 F) * wv (belowP P) : ℕ) : ℤ) := fun P =>
    hc _ P (Ideal.isMaximal_under_of_isIntegral_of_isMaximal P.asIdeal) rfl
  have he : ∀ P : HeightOneSpectrum (𝓞 K), P.asIdeal.ramificationIdx (𝓞 F) ≠ 0 := by
    intro P
    haveI := P.isPrime
    exact (Ideal.ramificationIdx_pos (R := 𝓞 F) P.asIdeal).ne'

  have hfinJ := FractionalIdeal.finite_factors (K := K) J
  have hsupp : {v : HeightOneSpectrum (𝓞 F) | wv v ≠ 0}.Finite := by
    refine (hfinJ.image belowP).subset ?_
    intro v hv
    obtain ⟨P, rfl⟩ := exists_above (K := K) v
    refine ⟨P, ?_, rfl⟩
    show FractionalIdeal.count K P J ≠ 0
    rw [hcJ P]
    exact_mod_cast Nat.mul_ne_zero (he P) hv

  have hmsF : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal ^ wv v := by
    refine hsupp.subset ?_
    intro v hv h0
    apply hv
    show v.asIdeal ^ wv v = 1
    rw [show wv v = 0 from h0, pow_zero]
  set IF : Ideal (𝓞 F) := ∏ᶠ v : HeightOneSpectrum (𝓞 F), v.asIdeal ^ wv v with hIF
  have hIF0 : IF ≠ ⊥ := by
    rw [hIF, finprod_eq_prod _ hmsF]
    exact Finset.prod_ne_zero_iff.mpr fun v _ => pow_ne_zero _ v.ne_bot
  have hcF : ∀ v : HeightOneSpectrum (𝓞 F), multiplicity v.asIdeal IF = wv v := by
    intro v
    have h1 := count_coe_eq_multiplicity (K := F) v hIF0
    have h2 : ((IF : Ideal (𝓞 F)) : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
        ∏ᶠ u : HeightOneSpectrum (𝓞 F), (u.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ^ ((wv u : ℕ) : ℤ) := by
      rw [hIF, FractionalIdeal.coeIdeal_finprod (nonZeroDivisors (𝓞 F)) F le_rfl]
      simp_rw [FractionalIdeal.coeIdeal_pow, zpow_natCast]
    rw [h2, FractionalIdeal.count_finprod] at h1
    · exact_mod_cast h1.symm
    · show {u | ¬ ((wv u : ℕ) : ℤ) = 0}.Finite
      simpa using hsupp

  have hJ : J = ((IF.map (algebraMap (𝓞 F) (𝓞 K)) : Ideal (𝓞 K)) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
    have hm0 : IF.map (algebraMap (𝓞 F) (𝓞 K)) ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot hIF0
    refine eq_of_count_eq hJ0 (by rwa [Ne, FractionalIdeal.coeIdeal_eq_zero]) fun P => ?_
    rw [hcJ P, count_coe_eq_multiplicity P hm0]
    haveI : P.asIdeal.LiesOver (belowP (K := K) (F := F) P).asIdeal := ⟨rfl⟩
    have hem := Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx'_mul hIF0
      (belowP (K := K) (F := F) P).irreducible P.irreducible P.ne_bot
    rw [(FiniteMultiplicity.of_prime_left P.prime hm0).emultiplicity_eq_multiplicity,
      (FiniteMultiplicity.of_prime_left (belowP (K := K) (F := F) P).prime hIF0).emultiplicity_eq_multiplicity,
      hcF, Ideal.ramificationIdx'_eq_ramificationIdx _ P.asIdeal (belowP (K := K) (F := F) P).ne_bot] at hem
    exact_mod_cast hem.symm

  have hfr : Module.finrank (𝓞 F) (𝓞 K) = 2 := by
    rw [← IsFractionRing.finrank_eq (𝓞 F) F (𝓞 K) K]
    exact h2
  have hNJ : (FractionalIdeal.absNorm J : ℝ) = ((Ideal.absNorm IF : ℕ) : ℝ) ^ 2 := by
    rw [hJ, FractionalIdeal.coeIdeal_absNorm, Ideal.absNorm_algebraMap, hfr]
    push_cast
    rfl
  have hNIF : Ideal.absNorm IF = ∏ᶠ v : HeightOneSpectrum (𝓞 F), Ideal.absNorm v.asIdeal ^ wv v := by
    rw [hIF, map_finprod Ideal.absNorm hmsF]
    simp only [map_pow]
  have hms2 : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) => Ideal.absNorm v.asIdeal ^ wv v := by
    refine hsupp.subset ?_
    intro v hv h0
    apply hv
    show Ideal.absNorm v.asIdeal ^ wv v = 1
    rw [show wv v = 0 from h0, pow_zero]
  have hms3 : Function.HasFiniteMulSupport
      fun v : HeightOneSpectrum (𝓞 F) => ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ wv v := by
    refine hsupp.subset ?_
    intro v hv h0
    apply hv
    show ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ wv v = 1
    rw [show wv v = 0 from h0, pow_zero]
  let e : HeightOneSpectrum (𝓞 F) ≃ {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} :=
    { toFun := fun v => ⟨v.asIdeal, v.isMaximal⟩
      invFun := fun p => ⟨p.1, p.2.isPrime,
        Ring.ne_bot_of_isMaximal_of_not_isField p.2 (NumberField.RingOfIntegers.not_isField F)⟩
      left_inv := fun v => rfl
      right_inv := fun p => rfl }
  have ht : (∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, (Ideal.absNorm 𝔭.1 : ℝ) ^ w 𝔭.1) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 F), ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ wv v := by
    rw [← e.tprod_eq]
    exact tprod_eq_finprod hms3
  have hcast := map_finprod (Nat.castRingHom ℝ) hms2
  simp only [map_pow, eq_natCast] at hcast
  rw [hNJ, hNIF, ht, hcast]

end PI.UnitaryGroupMassFormula.CntFormula.R6
end
end
