module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareSeriesSquareIntegrable
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuotientInvariantMeasurability.MeasurableAvgS
public import Formalism.PeriodIntegrals.KFinSmooth
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdicIntegersCompact.IsCompactAdicCompletionIntegers
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramInjectivity.InstFintypeColChoice
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedCharacterOne.IsIntegralAtSuperdiagonalSum
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Minkowski

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FoldUnfold
section -- merged from Formalism.PeriodIntegrals.FoldUnfold
open MeasureTheory
open scoped ENNReal NNReal

namespace PI.FoldUnfold

def FoldUnfold : Prop :=
  ∀ (G : Type*) [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G)
    [μ.IsMulLeftInvariant] (Γ S : Subgroup G) [Countable Γ], S ≤ Γ →
  ∀ (F : Set G), IsFundamentalDomain S F μ →
  ∀ (FΓ : Set G), IsFundamentalDomain Γ FΓ μ →
  ∀ (D : Set G), Formalism.L2.SG.FoldBound.IsRightTransversal Γ S D →
  ∀ (f : G → ℝ≥0∞), Measurable f → (∀ s ∈ S, ∀ y : G, f (s * y) = f y) →
    (∫⁻ x in FΓ, ∑' δ : D, f ((δ : G) * x) ∂μ) = ∫⁻ y in F, f y ∂μ

end PI.FoldUnfold
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnfoldingIdentity.FoldUnfoldMain
noncomputable section

open MeasureTheory
open scoped ENNReal NNReal Pointwise

namespace PI.FoldUnfold.UnitaryGroupMassFormula

theorem count_ae_one {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G)
    (S : Subgroup G) [Countable S] (F : Set G) (hF : IsFundamentalDomain S F μ) :
    ∀ᵐ y ∂μ, ∑' s : S, F.indicator (fun _ => (1 : ℝ≥0∞)) ((s : G) * y) = 1 := by

  have hcov := hF.ae_covers
  have hnull : ∀ᵐ y ∂μ, ∀ s t : S, s ≠ t → ¬ ((s : G) * y ∈ F ∧ (t : G) * y ∈ F) := by
    rw [ae_all_iff]
    intro s
    rw [ae_all_iff]
    intro t
    by_cases hst : s = t
    · exact Filter.Eventually.of_forall fun y h => absurd hst h
    · have hd : AEDisjoint μ (s⁻¹ • F) (t⁻¹ • F) := hF.aedisjoint (inv_injective.ne hst)
      have h0 : μ (s⁻¹ • F ∩ t⁻¹ • F) = 0 := hd
      have h1 : ∀ᵐ y ∂μ, y ∉ s⁻¹ • F ∩ t⁻¹ • F := ae_iff.mpr (by simpa using h0)
      filter_upwards [h1] with y hy _ hyy
      apply hy
      exact ⟨by simpa [Set.mem_inv_smul_set_iff, Subgroup.smul_def] using hyy.1,
        by simpa [Set.mem_inv_smul_set_iff, Subgroup.smul_def] using hyy.2⟩
  filter_upwards [hcov, hnull] with y hy huniq
  obtain ⟨g, hg⟩ := hy
  rw [Subgroup.smul_def, smul_eq_mul] at hg
  rw [tsum_eq_single g]
  · simp [Set.indicator_of_mem hg]
  · intro b hb
    have : (b : G) * y ∉ F := fun hb' => huniq b g hb ⟨hb', hg⟩
    simp [Set.indicator_of_notMem this]

theorem foldUnfold_main : PI.FoldUnfold.FoldUnfold := by
  intro G _ _ _ μ _ Γ S _ hSΓ F hF FΓ hFΓ D hD f hf hfS
  haveI : Countable S := Function.Injective.countable (Subgroup.inclusion_injective hSΓ)
  haveI : Countable D := Function.Injective.countable
    (f := fun d : D => (⟨d.1, hD.1 d.2⟩ : Γ)) (fun a b h => Subtype.ext (congrArg (fun γ : Γ => (γ : G)) h))

  have hpt : ∀ᵐ x ∂μ, ∑' γ : Γ, F.indicator f ((γ : G) * x) = ∑' δ : D, f ((δ : G) * x) := by
    have hA : ∀ᵐ x ∂μ, ∀ δ : D,
        ∑' s : S, F.indicator (fun _ => (1 : ℝ≥0∞)) ((s : G) * ((δ : G) * x)) = 1 := by
      rw [ae_all_iff]
      intro δ
      exact (measurePreserving_mul_left μ (δ : G)).quasiMeasurePreserving.ae (count_ae_one μ S F hF)
    filter_upwards [hA] with x hx
    let e : S × D → Γ := fun p => ⟨(p.1 : G) * p.2, Γ.mul_mem (hSΓ p.1.2) (hD.1 p.2.2)⟩
    have he : Function.Bijective e := by
      constructor
      · rintro ⟨s, δ⟩ ⟨s', δ'⟩ h
        have hγ : ((s : G) * δ) ∈ Γ := Γ.mul_mem (hSΓ s.2) (hD.1 δ.2)
        obtain ⟨q, _, hq⟩ := hD.2 _ hγ
        have h1 := hq (s, δ) rfl
        have h2 := hq (s', δ') (congrArg Subtype.val h).symm
        exact h1.trans h2.symm
      · intro γ
        obtain ⟨q, hq, _⟩ := hD.2 γ γ.2
        exact ⟨q, Subtype.ext hq⟩
    rw [← (Equiv.ofBijective e he).tsum_eq, ENNReal.tsum_prod', ENNReal.tsum_comm]
    refine tsum_congr fun δ => ?_
    calc _ = ∑' s : S, F.indicator (fun _ => (1 : ℝ≥0∞)) ((s : G) * ((δ : G) * x)) * f ((δ : G) * x) := by
          refine tsum_congr fun s => ?_
          show F.indicator f ((s : G) * δ * x) = _
          rw [mul_assoc, ← hfS s s.2 ((δ : G) * x)]
          by_cases hm : (s : G) * ((δ : G) * x) ∈ F
          · simp [Set.indicator_of_mem hm]
          · simp [Set.indicator_of_notMem hm]
      _ = f ((δ : G) * x) := by rw [ENNReal.tsum_mul_right, hx δ, one_mul]
  rw [← lintegral_indicator₀ hF.nullMeasurableSet, hFΓ.lintegral_eq_tsum'' (F.indicator f),
    ← lintegral_tsum]
  · apply lintegral_congr_ae
    filter_upwards [ae_restrict_of_ae hpt] with x hx
    exact hx.symm
  · intro γ
    have h1 : AEMeasurable (F.indicator f) μ := hf.aemeasurable.indicator₀ hF.nullMeasurableSet
    exact (h1.comp_quasiMeasurePreserving
      (measurePreserving_mul_left μ (γ : G)).quasiMeasurePreserving).restrict

end PI.FoldUnfold.UnitaryGroupMassFormula
end
end

theorem lintegralTransversalSum : PI.FoldUnfold.FoldUnfold :=
  PI.FoldUnfold.UnitaryGroupMassFormula.foldUnfold_main
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QuotInv
theorem quotient_invariant : PI.QuotInv := PI.QuotInvW.quotInv
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AreaLat
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeArea.ImConjMulCombo
namespace PI.AreaLatWork

open PI

lemma im_conj_mul_combo (w₁ w₂ : ℂ) (m n m' n' : ℤ) :
    ((starRingEnd ℂ) (m • w₁ + n • w₂) * (m' • w₁ + n' • w₂)).im
      = ((m * n' - n * m' : ℤ) : ℝ) * ((starRingEnd ℂ) w₁ * w₂).im := by
  simp only [zsmul_eq_mul, map_add (f := _), map_mul, map_intCast, Complex.mul_im, Complex.mul_re,
    Complex.add_re, Complex.add_im, Complex.intCast_re, Complex.intCast_im, Complex.conj_re,
    Complex.conj_im]
  push_cast
  ring

lemma im_integral (w₁ w₂ : ℂ) :
    ∀ a ∈ lat2 w₁ w₂, ∀ b ∈ lat2 w₁ w₂,
      ∃ n : ℤ, ((starRingEnd ℂ) a * b).im = n * ((starRingEnd ℂ) w₁ * w₂).im := by
  intro a ha b hb
  obtain ⟨m, n, rfl⟩ := (AddSubgroup.mem_closure_pair (x := w₁) (y := w₂)).mp ha
  obtain ⟨m', n', rfl⟩ := (AddSubgroup.mem_closure_pair (x := w₁) (y := w₂)).mp hb
  exact ⟨m * n' - n * m', im_conj_mul_combo w₁ w₂ m n m' n'⟩

theorem areaLat : PI.AreaLat := by
  intro w₁ w₂ hne
  refine ⟨?_, im_integral w₁ w₂⟩
  unfold PI.area
  apply IsLeast.csInf_eq
  constructor
  · refine ⟨abs_pos.mpr hne, w₁, ?_, w₂, ?_, rfl⟩
    · exact AddSubgroup.subset_closure (Set.mem_insert _ _)
    · exact AddSubgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  · rintro a ⟨ha, x, hx, y, hy, rfl⟩
    obtain ⟨n, hn⟩ := im_integral w₁ w₂ x hx y hy
    rw [hn, abs_mul] at ha ⊢
    have hn0 : (n : ℝ) ≠ 0 := by
      intro h0
      rw [h0, abs_zero, zero_mul] at ha
      exact lt_irrefl _ ha
    have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs (by exact_mod_cast hn0)
    have h2 := mul_le_mul_of_nonneg_right hn1 (abs_nonneg (((starRingEnd ℂ) w₁ * w₂).im))
    linarith

end PI.AreaLatWork
end

theorem area_lattice_formula : PI.AreaLat := PI.AreaLatWork.areaLat
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.IntAdCpctOpen
theorem finiteAdeleIntegers_compactOpen : Formalism.L2.Props.IntAdelesCompactOpen := PI.IntAdCpctOpenWork.main
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WwInjective
theorem wwInjective_of (h : PI.WwCauchyBinet.WwCauchyBinet) : PI.WwInjective.WwInjective :=
  PI.WwInjectiveWork.wwInjective_of h
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TwChrOne
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedCharacterOne.TwChrOneMain
open NumberField IsDedekindDomain

noncomputable section

namespace PI.TwChrOne.Pf

theorem twChrOne_main : PI.TwChrOne.TwChrOne := by
  intro E K _ _ _ _ P psi ξ kj N c hpsi

  have memJ : ∀ r ∈ Loc.Cbe (LocE.JQ P (Ideal.absNorm P.asIdeal) kj N c)
      (1 : Sp E (N + c) ≃ₗ[E] Sp E (N + c)), r ∈ LocE.JQ P (Ideal.absNorm P.asIdeal) kj N c := by
    intro r hr
    unfold Loc.Cbe at hr
    have h2 := (Subgroup.mem_inf.mp hr).2
    rw [Subgroup.mem_comap] at h2
    simpa using h2

  have chi_eq : ∀ r ∈ LocE.JQ P (Ideal.absNorm P.asIdeal) kj N c,
      ChiL P psi ξ kj N c 1 r = (LocE.unitV ξ (Ment kj N c r).det)⁻¹ := by
    intro r hr
    unfold ChiL
    rw [hpsi _ (isIntegralAt_superdiagonalSum P (hI_of P hr)), inv_one, one_mul, inv_one, one_mul, mul_one]
    rfl
  have unit_of : ∀ r ∈ LocE.JQ P (Ideal.absNorm P.asIdeal) kj N c,
      IsUnit (redP P (Ment kj N c r).det) := by
    intro r hr
    rw [redP_det_Ment P (hI_of P hr)]
    exact isUnit_Mb P hr
  refine ⟨fun r hr => ?_, fun r hr r' hr' r'' hr'' hx => ?_⟩
  · have hJ := memJ r hr
    rw [chi_eq r hJ]
    refine inv_ne_zero ?_
    unfold LocE.unitV
    rw [dite_eq_left (unit_of r hJ)]
    exact Units.ne_zero _
  · have hJ := memJ r hr
    have hJ' := memJ r' hr'
    have hJ'' := memJ r'' hr''
    rw [chi_eq r hJ, chi_eq r' hJ', chi_eq r'' hJ'', ← mul_inv]
    congr 1
    have hd : redP P (Ment kj N c r'').det =
        redP P (Ment kj N c r).det * redP P (Ment kj N c r').det := by
      rw [redP_det_Ment P (hI_of P hJ''), redP_det_Ment P (hI_of P hJ),
        redP_det_Ment P (hI_of P hJ'), ← Matrix.det_mul]
      congr 1
      apply Mb_mul_of P (fun i hi1 hi2 j hj => red_DA P hJ i hi1 hi2 j hj) (hI_of P hJ) (hI_of P hJ')
      intro t
      have ht : kj + t.1 < N := by have := t.isLt; omega
      have := hx (Loc.eN E N (kj + t.1))
      rwa [inX_eN ht] at this
    have hu := unit_of r hJ
    have hu' := unit_of r' hJ'
    have hu'' := unit_of r'' hJ''
    unfold LocE.unitV
    rw [dite_eq_left hu'', dite_eq_left hu, dite_eq_left hu']
    have hmul : hu''.unit = hu.unit * hu'.unit := Units.ext (by simp [hd])
    rw [hmul, map_mul, Units.val_mul]

end PI.TwChrOne.Pf
end
end

theorem TwChrOne : PI.TwChrOne.TwChrOne := PI.TwChrOne.Pf.twChrOne_main
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.MinkowskiQ
section -- merged from Formalism.PeriodIntegrals.MinkowskiQ
namespace PI

def MinkowskiBoundQ : Prop :=
  ∀ (N : ℕ) (G : Subgroup (Matrix.GeneralLinearGroup (Fin N) ℚ)), Finite G →
    Nat.card G ∣ minkowskiM N

end PI
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MinkowskiTorsionFree.Lattice
namespace PI.MkQ

open Matrix

variable {N : ℕ} (G : Subgroup (GeneralLinearGroup (Fin N) ℚ))

def orbitSet : Set (Fin N → ℚ) :=
  Set.range fun p : G × Fin N =>
    ((p.1 : GeneralLinearGroup (Fin N) ℚ) : Matrix (Fin N) (Fin N) ℚ).mulVec (Pi.single p.2 1)

def lat : Submodule ℤ (Fin N → ℚ) := Submodule.span ℤ (orbitSet G)

theorem single_mem (i : Fin N) : (Pi.single i 1 : Fin N → ℚ) ∈ lat G := by
  apply Submodule.subset_span
  refine ⟨(1, i), ?_⟩
  show (((1 : G) : GeneralLinearGroup (Fin N) ℚ) : Matrix (Fin N) (Fin N) ℚ) *ᵥ Pi.single i 1 =
    Pi.single i 1
  exact Matrix.one_mulVec _

theorem mulVec_mem (g : G) {v : Fin N → ℚ} (hv : v ∈ lat G) :
    ((g : GeneralLinearGroup (Fin N) ℚ) : Matrix (Fin N) (Fin N) ℚ).mulVec v ∈ lat G := by
  have hv' : v ∈ Submodule.span ℤ (orbitSet G) := hv
  clear hv
  induction hv' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨h, i⟩, rfl⟩ := hx
    apply Submodule.subset_span
    refine ⟨(g * h, i), ?_⟩
    show (((g * h : G) : GeneralLinearGroup (Fin N) ℚ) : Matrix (Fin N) (Fin N) ℚ) *ᵥ Pi.single i 1 =
      ((g : GeneralLinearGroup (Fin N) ℚ) : Matrix (Fin N) (Fin N) ℚ) *ᵥ
        (((h : GeneralLinearGroup (Fin N) ℚ) : Matrix (Fin N) (Fin N) ℚ) *ᵥ Pi.single i 1)
    rw [Matrix.mulVec_mulVec]
    rfl
  | zero => simp
  | add x y _ _ hx hy =>
    rw [Matrix.mulVec_add]
    exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [Matrix.mulVec_smul]
    exact Submodule.smul_mem _ a hx

noncomputable def rho : G →* Module.End ℤ (lat G) where
  toFun g := ((((g : GeneralLinearGroup (Fin N) ℚ) : Matrix (Fin N) (Fin N) ℚ).mulVecLin).restrictScalars
    ℤ).restrict (fun v hv => mulVec_mem G g hv)
  map_one' := by ext v i; simp
  map_mul' g g' := by
    ext v : 1
    apply Subtype.ext
    show _ = ((g : GeneralLinearGroup (Fin N) ℚ) : Matrix (Fin N) (Fin N) ℚ).mulVec
      (((g' : GeneralLinearGroup (Fin N) ℚ) : Matrix (Fin N) (Fin N) ℚ).mulVec (v : Fin N → ℚ))
    simp [Matrix.mulVec_mulVec]

theorem rho_apply_coe (g : G) (v : lat G) :
    ((rho G g v : lat G) : Fin N → ℚ) =
      ((g : GeneralLinearGroup (Fin N) ℚ) : Matrix (Fin N) (Fin N) ℚ).mulVec v := rfl

section finite

variable [Finite G]

theorem orbitSet_finite : (orbitSet G).Finite := Set.finite_range _

instance : Module.Finite ℤ (lat G) := Module.Finite.span_of_finite ℤ (orbitSet_finite G)

instance : Module.IsTorsionFree ℤ (lat G) := inferInstance

instance : Module.Free ℤ (lat G) := Module.free_of_finite_type_torsion_free'

theorem card_basis : Fintype.card (Module.Free.ChooseBasisIndex ℤ (lat G)) = N := by
  classical
  apply le_antisymm
  · have h1 : LinearIndependent ℤ
        (fun i => ((Module.Free.chooseBasis ℤ (lat G) i : lat G) : Fin N → ℚ)) :=
      (Module.Free.chooseBasis ℤ (lat G)).linearIndependent.map' (lat G).subtype
        (Submodule.ker_subtype _)
    have h2 : LinearIndependent ℚ
        (fun i => ((Module.Free.chooseBasis ℤ (lat G) i : lat G) : Fin N → ℚ)) :=
      (LinearIndependent.iff_fractionRing (R := ℤ) (K := ℚ)).1 h1
    simpa using h2.fintype_card_le_finrank
  · have h3 : LinearIndependent ℚ (fun i : Fin N => (Pi.single i 1 : Fin N → ℚ)) := by
      have h7 := (Pi.basisFun ℚ (Fin N)).linearIndependent
      rwa [show ⇑(Pi.basisFun ℚ (Fin N)) = fun i : Fin N => (Pi.single i 1 : Fin N → ℚ) from
        funext fun i => by simp] at h7
    have h4 : LinearIndependent ℤ (fun i : Fin N => (Pi.single i 1 : Fin N → ℚ)) :=
      (LinearIndependent.iff_fractionRing (R := ℤ) (K := ℚ)).2 h3
    have h5 : LinearIndependent ℤ (fun i : Fin N => (⟨Pi.single i 1, single_mem G i⟩ : lat G)) :=
      LinearIndependent.of_comp (lat G).subtype h4
    have h6 := h5.fintype_card_le_finrank
    rw [Module.finrank_eq_card_chooseBasisIndex] at h6
    simpa using h6

noncomputable def basisFin : Module.Basis (Fin N) ℤ (lat G) :=
  (Module.Free.chooseBasis ℤ (lat G)).reindex (Fintype.equivFinOfCardEq (card_basis G))

noncomputable def phi : G →* GeneralLinearGroup (Fin N) ℤ :=
  (Units.map (LinearMap.toMatrixAlgEquiv (basisFin G)).toRingEquiv.toMonoidHom).comp
    (rho G).toHomUnits

theorem phi_injective : Function.Injective (phi G) := by
  intro g g' h
  have h1 : rho G g = rho G g' := by
    have h0 := congrArg (fun u : GeneralLinearGroup (Fin N) ℤ => (u : Matrix (Fin N) (Fin N) ℤ)) h
    change (LinearMap.toMatrixAlgEquiv (basisFin G)) (rho G g) =
      (LinearMap.toMatrixAlgEquiv (basisFin G)) (rho G g') at h0
    exact (LinearMap.toMatrixAlgEquiv (basisFin G)).injective h0
  have h2 : ∀ i, ((g : GeneralLinearGroup (Fin N) ℚ) : Matrix (Fin N) (Fin N) ℚ).mulVec (Pi.single i 1) =
      ((g' : GeneralLinearGroup (Fin N) ℚ) : Matrix (Fin N) (Fin N) ℚ).mulVec (Pi.single i 1) := by
    intro i
    have h0 := congrArg
      (fun f : Module.End ℤ (lat G) => ((f ⟨Pi.single i 1, single_mem G i⟩ : lat G) : Fin N → ℚ)) h1
    simpa [rho_apply_coe] using h0
  apply Subtype.ext
  apply Units.ext
  ext a b
  have h0 := congrFun (h2 b) a
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h0

end finite

theorem minkowskiBoundQ : PI.MinkowskiBoundQ := by
  intro N G hG
  let e := MonoidHom.ofInjective (phi_injective G)
  have : Finite (phi G).range := Finite.of_equiv _ e.toEquiv
  rw [Nat.card_congr e.toEquiv]
  exact card_dvd_minkowskiNumber N _ inferInstance

end PI.MkQ
end

theorem minkowski_bound_rat : PI.MinkowskiBoundQ := PI.MkQ.minkowskiBoundQ
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.KerSplit
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.KernelSplitting.IsIntegralHalf
noncomputable section
open NumberField Polynomial

namespace PI.UnitaryGroupMassFormula.KerSplit

theorem isIntegral_sqrt {K : Type} [Field K] (d : ℕ) (s : K) (hs : s * s = -(d : K)) :
    IsIntegral ℤ s := by
  refine ⟨X ^ 2 + C (d : ℤ), monic_X_pow_add_C _ two_ne_zero, ?_⟩
  have e : (algebraMap ℤ K) (d : ℤ) = (d : K) := by simp
  rw [eval₂_add, eval₂_X_pow, eval₂_C, e]
  linear_combination hs

theorem isIntegral_half {K : Type} [Field K] [CharZero K] (d : ℕ) (s : K) (hd : d % 8 = 7)
    (hs : s * s = -(d : K)) : IsIntegral ℤ ((1 + s) / 2) := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, d + 1 = 4 * k := ⟨(d + 1) / 4, by omega⟩
  have hkK : (d : K) + 1 = 4 * (k : K) := by exact_mod_cast hk
  refine ⟨X ^ 2 - X + C (k : ℤ), ?_, ?_⟩
  · have e : (X ^ 2 - X + C (k : ℤ) : ℤ[X]) = X ^ 2 - (X - C (k : ℤ)) := by ring
    rw [e]
    apply monic_X_pow_sub
    rw [degree_X_sub_C]
    exact WithBot.coe_lt_coe.mpr (by norm_num)
  · have e : (algebraMap ℤ K) (k : ℤ) = (k : K) := by simp
    rw [eval₂_add, eval₂_sub, eval₂_X_pow, eval₂_X, eval₂_C, e]
    linear_combination (1 / 4 : K) * hs - (1 / 4 : K) * hkK

private theorem exists_isPrime_natCast_mem {K : Type} [Field K] [NumberField K] (p : ℕ) (hp : p.Prime) :
    ∃ P : Ideal (𝓞 K), P.IsPrime ∧ ((p : ℕ) : 𝓞 K) ∈ P := by
  have hnu : ¬ IsUnit ((p : ℕ) : 𝓞 K) := by
    rintro ⟨v, hv⟩
    have h1 : algebraMap (𝓞 K) K (↑v⁻¹ : 𝓞 K) * (p : K) = 1 := by
      rw [← map_natCast (algebraMap (𝓞 K) K) p, ← map_mul, ← hv, Units.inv_mul, map_one]
    have h2 : algebraMap (𝓞 K) K (↑v⁻¹ : 𝓞 K) = algebraMap ℚ K ((p : ℚ)⁻¹) := by
      rw [map_inv₀, map_natCast]
      exact eq_inv_of_mul_eq_one_left h1
    have hint : IsIntegral ℤ (algebraMap ℚ K ((p : ℚ)⁻¹)) := by
      rw [← h2]
      exact RingOfIntegers.isIntegral_coe _
    have hq : IsIntegral ℤ ((p : ℚ)⁻¹) :=
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ ℚ K) (algebraMap ℚ K).injective).1 hint
    obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 hq
    have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hn' : (n : ℚ) = (p : ℚ)⁻¹ := by simpa using hn
    have h4 : ((n * p : ℤ) : ℚ) = 1 := by
      push_cast
      rw [hn']
      exact inv_mul_cancel₀ hp0
    have h5 : n * (p : ℤ) = 1 := by exact_mod_cast h4
    have h6 : (p : ℤ) ∣ 1 := ⟨n, by rw [mul_comm]; exact h5.symm⟩
    have h7 := Int.eq_one_of_dvd_one (by positivity) h6
    have h8 : p = 1 := by exact_mod_cast h7
    exact hp.one_lt.ne' h8
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (Ideal.span {((p : ℕ) : 𝓞 K)})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  exact ⟨M, hM.isPrime, hle (Ideal.subset_span (Set.mem_singleton _))⟩

theorem splitsAt_two {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
    (cj : E ≃ₐ[ℚ] E) (d : ℕ) (s : K) (hd : d % 8 = 7) (hs : s * s = -(d : K))
    (hcj : cj (algebraMap K E s) = -algebraMap K E s) : PI.KerIso.SplitsAt K cj 2 := by
  obtain ⟨P, hP, h2P⟩ := exists_isPrime_natCast_mem (K := K) 2 Nat.prime_two
  obtain ⟨m, hm⟩ : ∃ m : ℕ, d + 1 = 8 * m := ⟨(d + 1) / 8, by omega⟩
  have hmK : (d : K) + 1 = 8 * (m : K) := by exact_mod_cast hm
  obtain ⟨aO, haK⟩ : ∃ x : 𝓞 K, algebraMap (𝓞 K) K x = (1 + s) / 2 :=
    ⟨⟨_, isIntegral_half d s hd hs⟩, rfl⟩
  obtain ⟨bO, hbK⟩ : ∃ x : 𝓞 K, algebraMap (𝓞 K) K x = (1 + -s) / 2 :=
    ⟨⟨_, isIntegral_half d (-s) hd (by rw [neg_mul_neg]; exact hs)⟩, rfl⟩
  have hinj := IsFractionRing.injective (𝓞 K) K
  have hsum : aO + bO = 1 := hinj (by rw [map_add (f := _), haK, hbK, map_one]; ring)
  have hprod : aO * bO = ((2 : ℕ) : 𝓞 K) * (m : 𝓞 K) := hinj (by
    rw [map_mul, haK, hbK, map_mul, map_natCast, map_natCast]
    push_cast
    linear_combination (-1 / 4 : K) * hs + (1 / 4 : K) * hmK)
  have hca : cj (algebraMap K E ((1 + s) / 2)) = algebraMap K E ((1 + -s) / 2) := by
    simp only [map_div₀, map_add (f := _), map_neg, map_one, map_ofNat, hcj]
  have hcb : cj (algebraMap K E ((1 + -s) / 2)) = algebraMap K E ((1 + s) / 2) := by
    simp only [map_div₀, map_add (f := _), map_neg, map_one, map_ofNat, hcj, neg_neg]
  have hab : aO * bO ∈ P := by
    rw [hprod]
    exact P.mul_mem_right _ h2P
  have hcoe : ∀ x : 𝓞 K, (x : K) = algebraMap (𝓞 K) K x := fun _ => rfl
  rcases hP.mem_or_mem hab with ha | hb
  · refine ⟨P, hP, h2P, aO, bO, ?_, ha, fun hb => hP.ne_top ?_⟩
    · rw [hcoe, hcoe, haK, hbK]
      exact hca
    · rw [Ideal.eq_top_iff_one, ← hsum]
      exact P.add_mem ha hb
  · refine ⟨P, hP, h2P, bO, aO, ?_, hb, fun ha => hP.ne_top ?_⟩
    · rw [hcoe, hcoe, haK, hbK]
      exact hcb
    · rw [Ideal.eq_top_iff_one, ← hsum]
      exact P.add_mem ha hb

theorem splitsAt_odd {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
    (cj : E ≃ₐ[ℚ] E) (d p : ℕ) (s : K) (hs : s * s = -(d : K))
    (hcj : cj (algebraMap K E s) = -algebraMap K E s) (hp : p.Prime) (hp2 : p ≠ 2)
    (hJ : jacobiSym (-(d : ℤ)) p = 1) : PI.KerIso.SplitsAt K cj p := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hP, hpP⟩ := exists_isPrime_natCast_mem (K := K) p hp
  obtain ⟨r, t, ht⟩ : ∃ r t : ℤ, r * r + (d : ℤ) = (p : ℤ) * t := by
    obtain ⟨c, hc⟩ := ZMod.isSquare_of_jacobiSym_eq_one hJ
    obtain ⟨t, ht⟩ : (p : ℤ) ∣ (c.val : ℤ) * (c.val : ℤ) + d := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [ZMod.natCast_zmod_val]
      push_cast at hc
      linear_combination -hc
    exact ⟨_, t, ht⟩
  have hg : Int.gcd (-(d : ℤ)) (p : ℤ) = 1 := by
    by_contra h
    have h0 := (jacobiSym.eq_zero_iff_not_coprime (a := -(d : ℤ)) (b := p)).2 h
    rw [hJ] at h0
    exact one_ne_zero h0
  obtain ⟨x, y, hxy⟩ := Int.isCoprime_iff_gcd_eq_one.2 hg
  obtain ⟨sO, hsK⟩ : ∃ z : 𝓞 K, algebraMap (𝓞 K) K z = s := ⟨⟨s, isIntegral_sqrt d s hs⟩, rfl⟩
  have hinj := IsFractionRing.injective (𝓞 K) K
  have hss : sO * sO = -((d : ℕ) : 𝓞 K) :=
    hinj (by rw [map_mul, hsK, map_neg, map_natCast]; exact hs)
  have hprod : ((r : 𝓞 K) + sO) * ((r : 𝓞 K) - sO) = ((p : ℕ) : 𝓞 K) * (t : 𝓞 K) := by
    have h1 : ((r * r + d : ℤ) : 𝓞 K) = ((p * t : ℤ) : 𝓞 K) := by rw [ht]
    push_cast at h1
    linear_combination h1 - hss
  have hab : ((r : 𝓞 K) + sO) * ((r : 𝓞 K) - sO) ∈ P := by
    rw [hprod]
    exact P.mul_mem_right _ hpP
  have hnot : ¬ ((r : 𝓞 K) + sO ∈ P ∧ (r : 𝓞 K) - sO ∈ P) := by
    rintro ⟨h1, h2⟩
    have h2s : (2 : 𝓞 K) * sO ∈ P := by
      have h3 := P.sub_mem h1 h2
      rwa [show (r : 𝓞 K) + sO - ((r : 𝓞 K) - sO) = 2 * sO by ring] at h3
    obtain ⟨q, hq⟩ := hp.odd_of_ne_two hp2
    have hc' : (((q + 1 : ℕ)) : 𝓞 K) * 2 = ((p : ℕ) : 𝓞 K) + 1 := by
      rw [hq]
      push_cast
      ring
    have hsP : sO ∈ P := by
      have e : sO = (((q + 1 : ℕ)) : 𝓞 K) * (2 * sO) - sO * ((p : ℕ) : 𝓞 K) := by
        linear_combination (-sO) * hc'
      rw [e]
      exact P.sub_mem (P.mul_mem_left _ h2s) (P.mul_mem_left _ hpP)
    have hdP : ((d : ℕ) : 𝓞 K) ∈ P := by
      have h4 := P.mul_mem_left sO hsP
      rw [hss] at h4
      exact (P.neg_mem_iff).1 h4
    apply hP.ne_top
    rw [Ideal.eq_top_iff_one]
    have e1 : (1 : 𝓞 K) = ((x : ℤ) : 𝓞 K) * (-((d : ℕ) : 𝓞 K)) + (y : 𝓞 K) * ((p : ℕ) : 𝓞 K) := by
      have h5 := congrArg (fun z : ℤ => (z : 𝓞 K)) hxy
      push_cast at h5
      exact h5.symm
    rw [e1]
    exact P.add_mem (P.mul_mem_left _ (P.neg_mem hdP)) (P.mul_mem_left _ hpP)
  have hca : cj (algebraMap K E (algebraMap (𝓞 K) K ((r : 𝓞 K) + sO))) =
      algebraMap K E (algebraMap (𝓞 K) K ((r : 𝓞 K) - sO)) := by
    simp only [map_add (f := _), map_sub, map_neg, map_intCast, hsK, hcj, sub_eq_add_neg]
  have hcb : cj (algebraMap K E (algebraMap (𝓞 K) K ((r : 𝓞 K) - sO))) =
      algebraMap K E (algebraMap (𝓞 K) K ((r : 𝓞 K) + sO)) := by
    simp only [map_add (f := _), map_sub, map_neg, map_intCast, hsK, hcj, sub_eq_add_neg, neg_neg]
  have hcoe : ∀ z : 𝓞 K, (z : K) = algebraMap (𝓞 K) K z := fun _ => rfl
  rcases hP.mem_or_mem hab with ha | hb
  · refine ⟨P, hP, hpP, (r : 𝓞 K) + sO, (r : 𝓞 K) - sO, ?_, ha, fun hb => hnot ⟨ha, hb⟩⟩
    rw [hcoe, hcoe]
    exact hca
  · refine ⟨P, hP, hpP, (r : 𝓞 K) - sO, (r : 𝓞 K) + sO, ?_, hb, fun ha => hnot ⟨ha, hb⟩⟩
    rw [hcoe, hcoe]
    exact hcb

end PI.UnitaryGroupMassFormula.KerSplit
end
end

theorem kernel_split_of_jacobi : PI.KerIso.SplitOfJacobi := by
  intro K E _ _ _ _ _ cj d p s hd hs hcj hp hJ
  by_cases h2 : p = 2
  · subst h2
    exact PI.UnitaryGroupMassFormula.KerSplit.splitsAt_two cj d s hd hs hcj
  · exact PI.UnitaryGroupMassFormula.KerSplit.splitsAt_odd cj d p s hs hcj hp h2 (hJ.resolve_left h2)
end
