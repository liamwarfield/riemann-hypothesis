module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.ZMemPerp
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaModuloX.IotaSurjectiveHolds

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.ExistsExactIdeal
open NumberField Module IsDedekindDomain

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.R6

section Dedekind

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

theorem count_span_unit (v : HeightOneSpectrum R) (s : R) (hs : s ∉ v.asIdeal) :
    FractionalIdeal.count K v (FractionalIdeal.spanSingleton (nonZeroDivisors R) (algebraMap R K s)) = 0 := by
  have hs0 : s ≠ 0 := fun h => hs (h ▸ v.asIdeal.zero_mem)
  have hsp : Ideal.span {s} ≠ ⊥ := by simpa using hs0
  rw [← FractionalIdeal.coeIdeal_span_singleton, count_coe_eq_multiplicity v hsp]
  have : multiplicity v.asIdeal (Ideal.span {s}) = 0 := by
    apply multiplicity_eq_zero_of_not_dvd
    rwa [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  simp [this]

theorem count_le_of_mem (v : HeightOneSpectrum R) {I : FractionalIdeal (nonZeroDivisors R) K} {y : K}
    (hy : y ∈ I) (hy0 : y ≠ 0) :
    FractionalIdeal.count K v I ≤ FractionalIdeal.count K v (FractionalIdeal.spanSingleton _ y) :=
  FractionalIdeal.count_mono K v (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hy0)
    (FractionalIdeal.spanSingleton_le_iff_mem.mpr hy)

theorem exists_exact_ideal (v : HeightOneSpectrum R) (T : Finset R) (hT : T.Nonempty) (h0 : ∀ g ∈ T, g ≠ 0) :
    ∃ g ∈ T, multiplicity v.asIdeal (Ideal.span {g}) = multiplicity v.asIdeal (Ideal.span (T : Set R)) := by
  classical
  induction hT using Finset.Nonempty.cons_induction with
  | singleton a => exact ⟨a, Finset.mem_singleton_self a, by simp⟩
  | cons a T ha hT ih =>
    have hT0 : ∀ g ∈ T, g ≠ 0 := fun g hg => h0 g (Finset.mem_cons_of_mem hg)
    obtain ⟨g, hg, hgm⟩ := ih hT0
    have ha0 : Ideal.span {a} ≠ ⊥ := by simpa using h0 a (Finset.mem_cons_self a T)
    have hT' : Ideal.span (T : Set R) ≠ ⊥ := by
      intro hb
      have : g ∈ Ideal.span (T : Set R) := Ideal.subset_span hg
      rw [hb, Ideal.mem_bot] at this
      exact hT0 g hg this
    have hspan : Ideal.span ((Finset.cons a T ha : Finset R) : Set R) = Ideal.span {a} ⊔ Ideal.span (T : Set R) := by
      rw [Finset.coe_cons, Ideal.span_insert]
    rw [hspan, HeightOneSpectrum.multiplicity_sup v ha0 hT']
    rcases le_total (multiplicity v.asIdeal (Ideal.span {a})) (multiplicity v.asIdeal (Ideal.span (T : Set R))) with h | h
    · exact ⟨a, Finset.mem_cons_self a T, (min_eq_left h).symm⟩
    · exact ⟨g, Finset.mem_cons_of_mem hg, by rw [min_eq_right h, hgm]⟩

theorem exists_exact (v : HeightOneSpectrum R) {I : FractionalIdeal (nonZeroDivisors R) K} (hI : I ≠ 0) :
    ∃ y ∈ I, y ≠ 0 ∧
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton (nonZeroDivisors R) y) = FractionalIdeal.count K v I := by
  classical
  obtain ⟨a, J, ha, hIJ⟩ := FractionalIdeal.exists_eq_spanSingleton_mul I
  have hJ0 : J ≠ ⊥ := by
    rintro rfl
    apply hI
    rw [hIJ, FractionalIdeal.coeIdeal_bot, mul_zero]
  obtain ⟨T, hT⟩ := (IsNoetherian.noetherian J : J.FG)
  set T' := T.filter (· ≠ 0)
  have hT' : Ideal.span (T' : Set R) = J := by
    rw [← hT]
    apply le_antisymm
    · exact Ideal.span_mono (by intro z hz; exact (Finset.mem_filter.mp hz).1)
    · rw [Ideal.span_le]
      intro z hz
      by_cases hz0 : z = 0
      · rw [hz0]; exact Ideal.zero_mem _
      · exact Ideal.subset_span (Finset.mem_filter.mpr ⟨hz, hz0⟩)
  have hne : T'.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    apply hJ0
    rw [← hT', hemp, Finset.coe_empty, Ideal.span_empty]
  obtain ⟨g, hgT, hgm⟩ := exists_exact_ideal v T' hne (fun g hg => (Finset.mem_filter.mp hg).2)
  have hg0 : g ≠ 0 := (Finset.mem_filter.mp hgT).2
  have hgJ : g ∈ J := hT' ▸ Ideal.subset_span hgT
  have ha' : algebraMap R K a ≠ 0 := (IsFractionRing.injective R K).ne_iff.mpr ha |>.trans_eq (map_zero _) |> fun h => by
    simpa using (map_ne_zero_iff (algebraMap R K) (IsFractionRing.injective R K)).mpr ha
  have hg' : algebraMap R K g ≠ 0 := (map_ne_zero_iff (algebraMap R K) (IsFractionRing.injective R K)).mpr hg0
  refine ⟨(algebraMap R K a)⁻¹ * algebraMap R K g, ?_, mul_ne_zero (inv_ne_zero ha') hg', ?_⟩
  · rw [hIJ]
    exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ _)
      (FractionalIdeal.mem_coeIdeal_of_mem _ hgJ)
  · have hsa : FractionalIdeal.spanSingleton (nonZeroDivisors R) (algebraMap R K a)⁻¹ ≠ 0 :=
      FractionalIdeal.spanSingleton_ne_zero_iff.mpr (inv_ne_zero ha')
    have hsg : FractionalIdeal.spanSingleton (nonZeroDivisors R) (algebraMap R K g) ≠ 0 :=
      FractionalIdeal.spanSingleton_ne_zero_iff.mpr hg'
    have hJc : (J : FractionalIdeal (nonZeroDivisors R) K) ≠ 0 := by
      rwa [Ne, FractionalIdeal.coeIdeal_eq_zero]
    have hsp : Ideal.span {g} ≠ ⊥ := by simpa using hg0
    rw [← FractionalIdeal.spanSingleton_mul_spanSingleton, FractionalIdeal.count_mul K v hsa hsg, hIJ,
      FractionalIdeal.count_mul K v hsa hJc, ← FractionalIdeal.coeIdeal_span_singleton,
      count_coe_eq_multiplicity v hsp, count_coe_eq_multiplicity v hJ0, hgm, hT']

theorem prod_mem_prod' {ι : Type*} (s : Finset ι) (𝔞 : ι → FractionalIdeal (nonZeroDivisors R) K)
    (m : ι → K) (hm : ∀ i, m i ∈ 𝔞 i) : ∏ i ∈ s, m i ∈ ∏ i ∈ s, 𝔞 i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact (FractionalIdeal.mem_one_iff _).mpr ⟨1, map_one _⟩
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj]
    exact FractionalIdeal.mul_mem_mul (hm j) ih

theorem det_mem_prod {ι : Type*} [Fintype ι] [DecidableEq ι] (𝔞 : ι → FractionalIdeal (nonZeroDivisors R) K)
    (M : Matrix ι ι K) (hM : ∀ i k, M i k ∈ 𝔞 i) : M.det ∈ ∏ i, 𝔞 i := by
  rw [Matrix.det_apply]
  refine Submodule.sum_mem _ fun σ _ => ?_
  have hp : ∏ i, M (σ i) i ∈ ∏ i, 𝔞 i := by
    have : ∏ i, M (σ i) i = ∏ j, M j (σ.symm j) := by
      rw [← Equiv.prod_comp σ (fun j => M j (σ.symm j))]
      simp
    rw [this]
    exact prod_mem_prod' _ 𝔞 _ fun j => hM j _
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · rw [h, one_smul]; exact hp
  · rw [h, Units.neg_smul, one_smul]; exact Submodule.neg_mem _ hp

end Dedekind

end PI.UnitaryGroupMassFormula.CntFormula.R6
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.UnimodOneGenus
open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def UnimodOneGenus : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (V : Type) [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K),
    Formalism.HermitianLatticesTheory.IsCMUnram K → h.IsSymm → h.Nondegenerate →
    ∀ L M : Submodule (𝓞 K) V, Submodule.IsLattice K L → Submodule.IsLattice K M →
      Formalism.HermitianLatticesTheory.IsUnimodular h L → Formalism.HermitianLatticesTheory.IsUnimodular h M → Formalism.HermitianLatticesTheory.SameGenus h L M

section Constr

variable (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)

def aaI (a : Fin D.R.rS) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E :=
  ddS D ^ (-((D.R.rS : ℤ) - (a : ℕ)))

def PartnerOK (f : Fin D.R.rS → (VS D).V) : Prop :=
  (∀ a b, (VS D).hT (F0.e a) (f b) = if a = b then 1 else 0) ∧ (∀ a b, (VS D).hT (f a) (f b) = 0) ∧
    ∀ a, (VS D).hT (f a) F0.z = 0

def vPr (f : Fin D.R.rS → (VS D).V) (v : (VS D).V) : (VS D).V :=
  v - ∑ a, (VS D).hT (F0.e a) v • f a

theorem vPr_add (f : Fin D.R.rS → (VS D).V) (v w : (VS D).V) :
    vPr D F0 f (v + w) = vPr D F0 f v + vPr D F0 f w := by
  simp only [vPr, map_add (f := _), add_smul, Finset.sum_add_distrib]
  abel

theorem vPr_smul (f : Fin D.R.rS → (VS D).V) (c : D.host.E) (v : (VS D).V) :
    vPr D F0 f (c • v) = c • vPr D F0 f v := by
  simp only [vPr, map_smul, smul_eq_mul, mul_smul, smul_sub, Finset.smul_sum]

theorem vPr_zero (f : Fin D.R.rS → (VS D).V) : vPr D F0 f 0 = 0 := by
  simp [vPr]

theorem fi_add {I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E} {x y : D.host.E}
    (hx : x ∈ I) (hy : y ∈ I) : x + y ∈ I := by
  have h := Submodule.add_mem (I : Submodule (𝓞 D.host.E) D.host.E)
    (FractionalIdeal.mem_coe.mpr hx) (FractionalIdeal.mem_coe.mpr hy)
  exact FractionalIdeal.mem_coe.mp h

theorem fi_zero (I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : (0 : D.host.E) ∈ I := by
  exact FractionalIdeal.mem_coe.mp (Submodule.zero_mem (I : Submodule (𝓞 D.host.E) D.host.E))

theorem fi_mul {I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E} (o : 𝓞 D.host.E) {x : D.host.E}
    (hx : x ∈ I) : (o : D.host.E) * x ∈ I := by
  have h := Submodule.smul_mem (I : Submodule (𝓞 D.host.E) D.host.E) o (FractionalIdeal.mem_coe.mpr hx)
  rw [Algebra.smul_def] at h
  exact FractionalIdeal.mem_coe.mp h

theorem star_int (o : 𝓞 D.host.E) : ∃ o' : 𝓞 D.host.E, (o' : D.host.E) = star (o : D.host.E) := by
  exact ⟨NumberField.RingOfIntegers.mapRingHom (starRingEnd D.host.E) o, rfl⟩

def lamC (f : Fin D.R.rS → (VS D).V) (M : Submodule (𝓞 D.host.E) (WbQ D F0)) :
    Submodule (𝓞 D.host.E) (VS D).V where
  carrier := {v | (∀ a, star ((VS D).hT (F0.e a) v) ∈ (aaI D a)⁻¹) ∧
    (∃ w : perpS (VS D) F0.X, (w : (VS D).V) = vPr D F0 f v ∧ (Submodule.Quotient.mk w : WbQ D F0) ∈ M) ∧
    ∀ a, (VS D).hT (f a) (vPr D F0 f v) ∈ aaI D a}
  add_mem' := by
    rintro v v' ⟨h1, ⟨w, hw, hwM⟩, h3⟩ ⟨h1', ⟨w', hw', hwM'⟩, h3'⟩
    refine ⟨fun a => ?_, ⟨w + w', ?_, ?_⟩, fun a => ?_⟩
    · rw [map_add (f := _), star_add]; exact fi_add D (h1 a) (h1' a)
    · rw [Submodule.coe_add, hw, hw', vPr_add]
    · rw [Submodule.Quotient.mk_add]; exact M.add_mem hwM hwM'
    · rw [vPr_add, map_add (f := _)]; exact fi_add D (h3 a) (h3' a)
  zero_mem' := by
    refine ⟨fun a => ?_, ⟨0, ?_, ?_⟩, fun a => ?_⟩
    · simp only [map_zero, star_zero]; exact fi_zero D _
    · simp [vPr_zero]
    · simp
    · simp only [vPr_zero, map_zero]; exact fi_zero D _
  smul_mem' := by
    rintro o v ⟨h1, ⟨w, hw, hwM⟩, h3⟩
    have hs : o • v = (o : D.host.E) • v := (algebraMap_smul D.host.E o v).symm
    refine ⟨fun a => ?_, ⟨o • w, ?_, ?_⟩, fun a => ?_⟩
    · obtain ⟨o', ho'⟩ := star_int D o
      rw [hs, map_smul, smul_eq_mul, star_mul, ← ho', mul_comm]
      exact fi_mul D o' (h1 a)
    · rw [hs, vPr_smul, ← hw]
      show o • (w : (VS D).V) = _
      exact (algebraMap_smul D.host.E o (w : (VS D).V)).symm
    · rw [Submodule.Quotient.mk_smul]; exact M.smul_mem o hwM
    · rw [hs, vPr_smul, map_smul, smul_eq_mul]; exact fi_mul D o (h3 a)

end Constr

def PartnerEx : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u)), ∃ f, PartnerOK D F0 f

def LamLattice : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u)) (f : Fin D.R.rS → (VS D).V)
    (M : Submodule (𝓞 D.host.E) (WbQ D F0)), PartnerOK D F0 f → IsGlueLat (hWb D F0) (zbar D F0) M →
      Submodule.IsLattice D.host.E (lamC D F0 f M)

def LamUnimod : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u)) (f : Fin D.R.rS → (VS D).V)
    (M : Submodule (𝓞 D.host.E) (WbQ D F0)), PartnerOK D F0 f → IsGlueLat (hWb D F0) (zbar D F0) M →
      Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT (lamC D F0 f M)

def LamFlag : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u)) (f : Fin D.R.rS → (VS D).V)
    (M : Submodule (𝓞 D.host.E) (WbQ D F0)), PartnerOK D F0 f → IsGlueLat (hWb D F0) (zbar D F0) M →
      F0.z ∈ lamC D F0 f M ∧ XLam (lamC D F0 f M) (lf D F0) = XS D F0 ∧
      (∀ c : D.host.E, c • F0.z ∈ Lsub (lamC D F0 f M) (lf D F0) → ∃ o : 𝓞 D.host.E, (o : D.host.E) = c) ∧
      Mof D F0 (lamC D F0 f M) = M

def LocGenXS : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u))
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)), ∃ c : Fin D.R.rS → D.host.E, (∀ a, c a ≠ 0) ∧
      (((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → ∀ a, c a = 1) ∧
      (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XS D F0) =
        Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Submodule.span (𝓞 D.host.E) (Set.range fun a => c a • F0.e a)))

private theorem row_riesz (D : Formalism.BasicNotions.D7) (φ : (VS D).V →ₗ[D.host.E] D.host.E) : ∃ μ : (VS D).V, ∀ v, (VS D).hT μ v = φ v := by
  classical
  obtain ⟨bs, hbs⟩ := Formalism.HermitianLatticesTheory.dualLattice_dualBasis (VS D).hT (VS D).nondeg (VS D).frame
  refine ⟨∑ j, star (φ ((VS D).frame j)) • bs j, fun v => ?_⟩
  have key : (VS D).hT (∑ j, star (φ ((VS D).frame j)) • bs j) = φ := by
    apply (VS D).frame.ext
    intro i
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, LinearMap.sum_apply]
    have hs : ∀ j, (VS D).hT (star (φ ((VS D).frame j)) • bs j) ((VS D).frame i) =
        φ ((VS D).frame j) * (if i = j then 1 else 0) := by
      intro j
      rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_star]
      congr 1
      rw [← (VS D).herm.eq ((VS D).frame i) (bs j), hbs]
      split_ifs <;> simp
    simp only [hs, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [key]

private theorem row_span_eq_top_of_unimodular (D : Formalism.BasicNotions.D7) {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hL : Λ.FG) (hU : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ) :
    Submodule.span D.host.E (Λ : Set (VS D).V) = ⊤ := by
  by_contra hspan
  obtain ⟨φ, hφ₀, hφ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hspan)
  obtain ⟨μ, hμ⟩ := row_riesz D φ
  have hμ₀ : μ ≠ 0 := by
    intro h
    apply hφ₀
    ext y
    simpa [h] using (hμ y).symm
  have hline (a : D.host.E) : a • μ ∈ Λ := by
    rw [← hU]
    change a • μ ∈ Formalism.E.hdual (VS D).hT Λ
    simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]
    intro y hy
    have hy₀ := LinearMap.mem_ker.mp (hφ (Submodule.subset_span hy))
    simp [← (VS D).herm.eq (a • μ) y, LinearMap.map_smulₛₗ, hμ, hy₀]
  obtain ⟨ψ, hψ, -⟩ := Submodule.exists_le_ker_of_notMem
    (show μ ∉ (⊥ : Submodule D.host.E (VS D).V) by simpa using hμ₀)
  let f := ψ.restrictScalars (𝓞 D.host.E)
  have hmap (x : D.host.E) : x ∈ Λ.map f := by
    refine ⟨(x / ψ μ) • μ, hline _, ?_⟩
    change ψ ((x / ψ μ) • μ) = x
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hψ]
  obtain ⟨d, hd₀, hd⟩ := FractionalIdeal.isFractional_of_fg
    (S := nonZeroDivisors (𝓞 D.host.E)) (hL.map f)
  have hinj := IsFractionRing.injective (𝓞 D.host.E) D.host.E
  have hne {a : 𝓞 D.host.E} (ha : a ≠ 0) : algebraMap (𝓞 D.host.E) D.host.E a ≠ 0 :=
    fun h => ha (hinj (h.trans (map_zero _).symm))
  have hinteger (x : D.host.E) : IsLocalization.IsInteger (𝓞 D.host.E) x := by
    have hx := hd _ (hmap ((algebraMap (𝓞 D.host.E) D.host.E d)⁻¹ * x))
    rwa [Algebra.smul_def, ← mul_assoc, mul_inv_cancel₀ (hne (nonZeroDivisors.ne_zero hd₀)),
      one_mul] at hx
  apply RingOfIntegers.not_isField D.host.E
  refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, ?_⟩
  intro a ha
  obtain ⟨b, hb⟩ := hinteger ((algebraMap (𝓞 D.host.E) D.host.E a)⁻¹)
  refine ⟨b, hinj ?_⟩
  rw [map_mul, hb, map_one, mul_inv_cancel₀ (hne ha)]


theorem rowSurj_of (hJ : UnimodOneGenus) (hP : PartnerEx) (hL : LamLattice) (hU : LamUnimod)
    (hF : LamFlag) (hG : LocGenXS) : RowSurj := by
  intro D u F0 M hM
  obtain ⟨f, hf⟩ := hP D u F0
  obtain ⟨hz, hX, hprim, hMof⟩ := hF D u F0 f M hf hM
  have hLat := hL D u F0 f M hf hM
  have hUn := hU D u F0 f M hf hM
  have hFull : Submodule.IsFullLattice D.host.E (lamC D F0 f M) :=
    { toIsLattice := hLat, span_eq_top := row_span_eq_top_of_unimodular D hLat.fg hUn }
  refine ⟨lamC D F0 f M, ?_, hMof⟩
  refine ⟨?_, ⟨hLat, hUn, ⟨hz, rfl⟩, ?_, hprim⟩, hX⟩
  ·
    exact ⟨hFull, hJ D.host.E (VS D).V (VS D).hT D.sp.cm.cmUnram (VS D).herm (VS D).nondeg
      (VS D).L0 (lamC D F0 f M) (VS D).standardTuple_isLattice hLat (VS D).baseLattice_isUnimodular hUn⟩
  · intro P
    rw [hX]
    exact hG D u F0 P

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.RowLatticeMassHolds
open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowMPf

open PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem perpS_eq_orth (D : D7) (U : Submodule D.host.E (VS D).V) : perpS (VS D) U = orth (VS D) U := by
  ext v
  rw [PI.UnitaryGroupMassFormula.BetaModX.Iota.mem_orth'']
  rfl

theorem e_mem_perp (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (a : Fin D.R.rS) :
    F0.e a ∈ perpS (VS D) F0.X := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, rfl⟩ := hy
    exact F0.e_iso b a
  | zero => simp
  | add y w _ _ h1 h2 => simp [h1, h2]
  | smul c y _ h => simp [h]

theorem X_le_perp (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) : F0.X ≤ perpS (VS D) F0.X := by
  unfold FlagG.X
  rw [Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  exact e_mem_perp D F0 a

theorem mem_Mof (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (x : WbQ D F0) :
    x ∈ Mof D F0 Λ ↔ ∃ a : perpS (VS D) F0.X, (a : (VS D).V) ∈ Λ ∧ Submodule.Quotient.mk a = x := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩

theorem mk_eq_mk (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (a b : perpS (VS D) F0.X) :
    (Submodule.Quotient.mk a : WbQ D F0) = Submodule.Quotient.mk b ↔ (a : (VS D).V) - b ∈ F0.X := by
  rw [Submodule.Quotient.eq]
  rfl

theorem Mof_fg (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (hfg : Λ.FG) : (Mof D F0 Λ).FG := by
  apply Submodule.FG.map
  apply Submodule.fg_of_fg_map_injective ((perpS (VS D) F0.X).subtype.restrictScalars (𝓞 D.host.E))
    Subtype.val_injective
  refine Submodule.FG.of_le hfg ?_
  rintro _ ⟨y, hy, rfl⟩
  exact hy

theorem Mof_span (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (hsp : Submodule.span D.host.E (Λ : Set (VS D).V) = ⊤) :
    Submodule.span D.host.E (Mof D F0 Λ : Set (WbQ D F0)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  induction x using Submodule.Quotient.induction_on with | H a => ?_
  obtain ⟨d, hd, hdm⟩ := PI.UnitaryGroupMassFormula.BetaModX.Iota.exists_smul_mem Λ hsp (a : (VS D).V)
  have hdE : algebraMap (𝓞 D.host.E) D.host.E d ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 D.host.E) D.host.E)).mpr hd
  have hmem : (Submodule.Quotient.mk (d • a) : WbQ D F0) ∈ Mof D F0 Λ := by
    rw [mem_Mof]
    refine ⟨d • a, ?_, rfl⟩
    rw [Submodule.coe_smul_of_tower]
    exact hdm
  have e : (Submodule.Quotient.mk a : WbQ D F0) =
      (algebraMap (𝓞 D.host.E) D.host.E d)⁻¹ • (Submodule.Quotient.mk (d • a) : WbQ D F0) := by
    rw [← algebraMap_smul D.host.E d a, Submodule.Quotient.mk_smul, smul_smul, inv_mul_cancel₀ hdE, one_smul]
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

theorem Mof_isLattice (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (hL : Submodule.IsLattice D.host.E Λ) : Submodule.IsLattice D.host.E (Mof D F0 Λ) :=
  Submodule.IsLattice.of_fg D.host.E (Mof_fg D F0 Λ hL.fg)

theorem Mof_unimod (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (hL : Submodule.IsLattice D.host.E Λ) (hU : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ) :
    Formalism.HermitianLatticesTheory.IsUnimodular (hWb D F0) (Mof D F0 Λ) := by
  have hsp : Submodule.span D.host.E (Λ : Set (VS D).V) = ⊤ := by
    by_contra hspan
    obtain ⟨φ, hφ₀, hφ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hspan)
    obtain ⟨bs, hbs⟩ := Formalism.HermitianLatticesTheory.dualLattice_dualBasis (VS D).hT (VS D).nondeg (VS D).frame
    let μ := ∑ j, star (φ ((VS D).frame j)) • bs j
    have hμ : ∀ v, (VS D).hT μ v = φ v := by
      have key : (VS D).hT μ = φ := by
        apply (VS D).frame.ext
        intro i
        dsimp [μ]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, LinearMap.sum_apply]
        have hs : ∀ j, (VS D).hT (star (φ ((VS D).frame j)) • bs j) ((VS D).frame i) =
            φ ((VS D).frame j) * (if i = j then 1 else 0) := by
          intro j
          rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_star]
          congr 1
          rw [← (VS D).herm.eq ((VS D).frame i) (bs j), hbs]
          split_ifs <;> simp
        simp only [hs, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      intro v
      rw [key]
    have hμ₀ : μ ≠ 0 := by
      intro h
      apply hφ₀
      ext y
      simpa [h] using (hμ y).symm
    have hline (a : D.host.E) : a • μ ∈ Λ := by
      rw [← hU]
      rw [Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
      intro y hy
      have hy₀ := LinearMap.mem_ker.mp (hφ (Submodule.subset_span hy))
      simp [← (VS D).herm.eq (a • μ) y, LinearMap.map_smulₛₗ, hμ, hy₀]
    obtain ⟨ψ, hψ, -⟩ := Submodule.exists_le_ker_of_notMem
      (show μ ∉ (⊥ : Submodule D.host.E (VS D).V) by simpa using hμ₀)
    let f := ψ.restrictScalars (𝓞 D.host.E)
    have hmap (x : D.host.E) : x ∈ Λ.map f := by
      refine ⟨(x / ψ μ) • μ, hline _, ?_⟩
      change ψ ((x / ψ μ) • μ) = x
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hψ]
    obtain ⟨d, hd₀, hd⟩ := FractionalIdeal.isFractional_of_fg
      (S := nonZeroDivisors (𝓞 D.host.E)) (hL.fg.map f)
    have hinj := IsFractionRing.injective (𝓞 D.host.E) D.host.E
    have hne {a : 𝓞 D.host.E} (ha : a ≠ 0) : algebraMap (𝓞 D.host.E) D.host.E a ≠ 0 :=
      fun h => ha (hinj (h.trans (map_zero _).symm))
    have hinteger (x : D.host.E) : IsLocalization.IsInteger (𝓞 D.host.E) x := by
      have hx := hd _ (hmap ((algebraMap (𝓞 D.host.E) D.host.E d)⁻¹ * x))
      rwa [Algebra.smul_def, ← mul_assoc, mul_inv_cancel₀ (hne (nonZeroDivisors.ne_zero hd₀)),
        one_mul] at hx
    apply RingOfIntegers.not_isField D.host.E
    refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, ?_⟩
    intro a ha
    obtain ⟨b, hb⟩ := hinteger ((algebraMap (𝓞 D.host.E) D.host.E a)⁻¹)
    refine ⟨b, hinj ?_⟩
    rw [map_mul, hb, map_one, mul_inv_cancel₀ (hne ha)]
  have hU' : Formalism.HermitianLatticesTheory.dual (VS D).hT Λ = Λ := hU
  show Formalism.HermitianLatticesTheory.dual (hWb D F0) (Mof D F0 Λ) = Mof D F0 Λ
  apply le_antisymm
  · intro x hx
    rw [Formalism.HermitianLatticesTheory.dualBasic_mem_dual] at hx
    induction x using Submodule.Quotient.induction_on with | H a => ?_

    have hint : ∀ l : perpS (VS D) F0.X, (l : (VS D).V) ∈ Λ →
        (VS D).hT (l : (VS D).V) (a : (VS D).V) ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
      intro l hl
      have := hx (Submodule.Quotient.mk l) ((mem_Mof D F0 Λ _).2 ⟨l, hl, rfl⟩)
      rwa [hWb_mk] at this
    obtain ⟨ρ, hρX, hρid⟩ := PI.UnitaryGroupMassFormula.BetaModX.Iota.exists_retract Λ hL.fg (perpS (VS D) F0.X)
    let f : Λ →ₗ[𝓞 D.host.E] D.host.E :=
      ((VS D).hT (a : (VS D).V)).restrictScalars (𝓞 D.host.E) ∘ₗ Λ.subtype ∘ₗ ρ
    obtain ⟨w, hw⟩ := PI.UnitaryGroupMassFormula.BetaModX.Iota.riesz (VS D).hT (VS D).herm (VS D).nondeg Λ hL.fg
      hsp f

    have hwΛ : w ∈ Λ := by
      rw [← hU', Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
      intro y hy
      rw [PI.UnitaryGroupMassFormula.BetaModX.Iota.herm'' (S := VS D) w y, hw y hy]
      have e1 : f ⟨y, hy⟩ = (VS D).hT (a : (VS D).V) ((ρ ⟨y, hy⟩ : Λ) : (VS D).V) := rfl
      rw [e1, ← PI.UnitaryGroupMassFormula.BetaModX.Iota.herm'' (S := VS D)]
      exact hint ⟨_, hρX ⟨y, hy⟩⟩ (ρ ⟨y, hy⟩).2

    have hwv : ∀ v ∈ perpS (VS D) F0.X, (VS D).hT (w - (a : (VS D).V)) v = 0 := by
      intro v hv
      obtain ⟨d, hd, hdm⟩ := PI.UnitaryGroupMassFormula.BetaModX.Iota.exists_smul_mem Λ hsp v
      have hdE : algebraMap (𝓞 D.host.E) D.host.E d ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 D.host.E) D.host.E)).mpr hd
      have hdp : d • v ∈ perpS (VS D) F0.X := by
        rw [← algebraMap_smul D.host.E d v]
        exact Submodule.smul_mem _ _ hv
      have h1 := hw (d • v) hdm
      have e1 : f ⟨d • v, hdm⟩ = (VS D).hT (a : (VS D).V) ((ρ ⟨d • v, hdm⟩ : Λ) : (VS D).V) := rfl
      rw [e1, hρid ⟨d • v, hdm⟩ hdp] at h1
      have h2 : (VS D).hT (w - (a : (VS D).V)) (d • v) = 0 := by
        rw [map_sub, LinearMap.sub_apply, h1]
        simp
      rw [← algebraMap_smul D.host.E d v, LinearMap.map_smul, smul_eq_mul] at h2
      exact (mul_eq_zero.1 h2).resolve_left hdE

    have hwX : w - (a : (VS D).V) ∈ F0.X := by
      have : w - (a : (VS D).V) ∈ orth (VS D) (orth (VS D) F0.X) := by
        rw [PI.UnitaryGroupMassFormula.BetaModX.Iota.mem_orth'']
        intro v hv
        rw [← perpS_eq_orth] at hv
        rw [PI.UnitaryGroupMassFormula.BetaModX.Iota.herm'' (S := VS D), hwv v hv, star_zero]
      rwa [PI.ScalarPairDr.W.orth_orth] at this
    have hwp : w ∈ perpS (VS D) F0.X := by
      have e : w = (a : (VS D).V) + (w - (a : (VS D).V)) := by abel
      rw [e]
      exact Submodule.add_mem _ a.2 (X_le_perp D F0 hwX)
    rw [mem_Mof]
    refine ⟨⟨w, hwp⟩, hwΛ, ?_⟩
    rw [mk_eq_mk]
    exact hwX
  · intro x hx
    rw [Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
    intro y hy
    obtain ⟨a, ha, rfl⟩ := (mem_Mof D F0 Λ x).1 hx
    obtain ⟨b, hb, rfl⟩ := (mem_Mof D F0 Λ y).1 hy
    rw [hWb_mk]
    obtain ⟨o, ho⟩ := PI.UnitaryGroupMassFormula.BetaModX.Iota.int_val (S := VS D) hU hb ha
    exact Submodule.mem_one.2 ⟨o, ho⟩

theorem zbar_mem (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (hz : F0.z ∈ Λ) : zbar D F0 ∈ Mof D F0 Λ :=
  (mem_Mof D F0 Λ _).2 ⟨⟨F0.z, z_mem_perp D F0⟩, hz, rfl⟩

theorem zbar_prim (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (hprim : ∀ c : D.host.E, c • F0.z ∈ Lsub Λ (lf D F0) → ∃ o : 𝓞 D.host.E, (o : D.host.E) = c)
    (c : D.host.E) (hc : c • zbar D F0 ∈ Mof D F0 Λ) : ∃ o : 𝓞 D.host.E, (o : D.host.E) = c := by
  apply hprim
  obtain ⟨a, ha, hae⟩ := (mem_Mof D F0 Λ _).1 hc
  rw [zbar, ← Submodule.Quotient.mk_smul, mk_eq_mk] at hae
  have hzo : F0.z ∈ orth (VS D) F0.X := by
    rw [← perpS_eq_orth]
    exact z_mem_perp D F0
  have hao : (a : (VS D).V) ∈ orth (VS D) F0.X := by
    rw [← perpS_eq_orth]
    exact a.2
  have hcz : c • F0.z = (a : (VS D).V) + -((a : (VS D).V) - c • F0.z) := by abel
  refine ⟨?_, ?_⟩
  · rw [hcz]
    refine Submodule.add_mem_sup ?_ ?_
    · exact ⟨ha, hao⟩
    · exact Submodule.neg_mem _ (by simpa using hae)
  · exact (orth (VS D) F0.X).smul_mem c hzo

theorem row_lattice_mass_holds : RowM := by
  intro D u F0 Λ hrow
  obtain ⟨_, ⟨hL, hU, ⟨hz, _⟩, hconv⟩, _⟩ := hrow
  exact ⟨Mof_isLattice D F0 Λ hL, Mof_unimod D F0 Λ hL hU, zbar_mem D F0 Λ hz,
    zbar_prim D F0 Λ hconv.2⟩

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowMPf

theorem PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.row_lattice_mass_holds : PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowM :=
  PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowMPf.row_lattice_mass_holds
end
end
