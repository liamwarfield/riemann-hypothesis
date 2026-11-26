module

public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmEigenLineDegreeFormula
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegrality

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmLieLineDegreeOfEigenLineDegreeFormula
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NormalisedDegreeCmEigenLineEq
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.TwoMulDegEigenLatticePolarizedAbelianScheme
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HasTypeOfIso
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.CM

theorem hasType_of_iso : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (G G' : Over (Sp R)) [GrpObj G] [GrpObj G'] (a : OAct (𝓞 E) G) (a' : OAct (𝓞 E) G') (e : G ≅ G') (ρ : R) (p q : ℕ), Serre.IsLinearHom a a' e.hom → HasType H a' ρ p q → HasType H a ρ p q := by
  intro E _ _ _ H R _ G G' _ _ a a' e ρ p q he h k _ _ β hβ τ
  have := he.isMonHom
  have key : ∀ n, LieMult a (spMap β) τ n ↔ LieMult a' (spMap β) τ n := fun n => by
    have := LiePull.lieMult_pull _ _ _ G' G (𝟙 _) e.hom.left a' a (isGrpPullback_of_iso e)
      (fun c => congrArg (fun z => z.left) (he.comm c)) k (spMap β) τ n
    rwa [Category.comp_id] at this
  rw [key, key]
  exact h k β hβ τ

end GlobalTheory.CM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.TwoMulDegEigenLatticePolarizedAbelianScheme
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem two_mul_deg_eigLat_of_polAV : DegSt → ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [NeZero H.d] (χ : DirichletCharacter ℂ H.d), IsKroneckerChar χ → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (P : Out.PolAV (Sp (𝓞 K))) (act : OAct (𝓞 E) P.A), (∀ a, LamEq P.L (act.act a) (𝟙 P.A) P.L (𝟙 P.A) (act.act (H.bar a))) → Splits E K → ρ ^ 2 = -(H.d : 𝓞 K) → HasType H act ρ 1 0 → ∀ (F : GenFib P) (h : HermFam K (Fin F.P₀.g → K)), F.IsHerm h → ∀ τ : 𝓞 E →+* 𝓞 K, τ H.rt = ρ → ((2 * deg h (F.eigLat act τ) : ℝ) : ℂ) = logOm E χ := by
  intro hD hT hL E _ _ _ H _ χ hχ K _ _ ρ P act hbal hs hρ ht F h hh τ hτ
  obtain ⟨T, e, -, hlin, hlam⟩ := exists_pat_of_polAV hL E H (𝓞 K) P act hbal
  obtain ⟨F₁⟩ := GenFib.nonempty_of_baseChange hL.polBaseChange K T.pol
  obtain ⟨h₁, hh₁⟩ := (LieMetric.exists_unique_isHerm hT hL K T.pol F₁).1
  have ht₁ : HasType H T.t.act ρ 1 0 := hasType_of_iso E H (𝓞 K) _ _ _ _ e ρ 1 0 hlin ht
  rw [← deg_eigLat_eq_of_iso hT hL K T.pol P F₁ F h₁ h (𝓞 E) T.t.act act e hh₁ hh hlin hlam τ]
  exact hD E H χ hχ K ρ T hs hρ ht₁ F₁ h₁ hh₁ τ hτ

end GlobalTheory.LamF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.TwoMulDegEigenLatticePolarizedAbelianSchemeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_mul_deg_eigenLattice_polarizedAbelianScheme : DegSt → ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [NeZero H.d] (χ : DirichletCharacter ℂ H.d), IsKroneckerChar χ → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (P : Out.PolAV (Sp (𝓞 K))) (act : OAct (𝓞 E) P.A), (∀ a, LamEq P.L (act.act a) (𝟙 P.A) P.L (𝟙 P.A) (act.act (H.bar a))) → Splits E K → ρ ^ 2 = -(H.d : 𝓞 K) → HasType H act ρ 1 0 → ∀ (F : GenFib P) (h : HermFam K (Fin F.P₀.g → K)), F.IsHerm h → ∀ τ : 𝓞 E →+* 𝓞 K, τ H.rt = ρ → ((2 * deg h (F.eigLat act τ) : ℝ) : ℂ) = logOm E χ := by
  first | exact @GlobalTheory.LamF.two_mul_deg_eigLat_of_polAV | exact GlobalTheory.LamF.two_mul_deg_eigLat_of_polAV | (intros; apply GlobalTheory.LamF.two_mul_deg_eigLat_of_polAV <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.DegEqNdegOfLine
open NumberField ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM

namespace GlobalTheory.LamF

theorem deg_eq_ndeg_of_line : ∀ (K : Type) [Field K] [NumberField K] (V : Type) [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : HermFam K V) (Λ : Submodule (𝓞 K) V) (v : V) (ℓ : MLine K),
    v ≠ 0 → ℓ.Good → (∀ z, z ∈ Λ ↔ ∃ c ∈ ℓ.I, z = c • v) → (∀ s, ℓ.n s ^ 2 = (h.form s v v).re) →
    deg h Λ = ℓ.ndeg := by
  intro K _ _ V _ _ _ _ h Λ v ℓ hv hℓ hΛ hn
  rw [GlobalTheory.CM.deg_ideal_smul h Λ hv (m := fun s => ℓ.n s ^ 2) (fun s => pow_pos (hℓ.2 s) 2)
    (fun s => (hn s).symm) hℓ.1 (fun z => (hΛ z).trans ⟨fun ⟨c, a, b⟩ => ⟨c, b, a⟩, fun ⟨c, a, b⟩ => ⟨c, b, a⟩⟩),
    MLine.ndeg, MLine.deg, meanLog]
  simp only [Real.log_pow, ← Finset.mul_sum, Nat.cast_ofNat]
  ring

end GlobalTheory.LamF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieMultOfEigenbasis
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF.LieType

theorem repr_eq_zero {k O V J : Type} [Field k] [CommRing O] [AddCommGroup V] [Module k V] [Module O V]
    [SMulCommClass O k V] (b : Module.Basis J k V) (χ : J → (O →+* k)) (hb : ∀ i a, a • b i = χ i a • b i)
    (ψ : O →+* k) (w : V) (hw : ∀ a : O, a • w = ψ a • w) (j : J) (hj : χ j ≠ ψ) : b.repr w j = 0 := by
  obtain ⟨a, ha⟩ : ∃ a, χ j a ≠ ψ a := by
    by_contra h
    push Not at h
    exact hj (RingHom.ext h)
  have e : (b.coord j).comp (DistribSMul.toLinearMap k V a) = χ j a • b.coord j := b.ext fun i => by
    by_cases h : i = j
    · subst h
      simp [hb]
    · simp [hb, Finsupp.single_eq_of_ne' h]
  have e' := LinearMap.congr_fun e w
  simp only [LinearMap.comp_apply, DistribSMul.toLinearMap_apply, hw, map_smul, LinearMap.smul_apply, smul_eq_mul,
    Module.Basis.coord_apply] at e'
  exact (mul_eq_mul_right_iff.1 e').resolve_left ha.symm

theorem lieMult_of_eigenbasis {k O : Type} [Field k] [CommRing O] {G : Over (Sp k)} [GrpObj G] [IsCommMonObj G]
    (a : OAct O G) {n : ℕ} {v : Fin n → (epsR k ⟶ G)} (hv : IsLieBasis v) (χ : Fin n → (O →+* k))
    (hχ : Function.Injective χ) (h : ∀ x i, IsLieComb (Pi.single i (χ i x)) v (v i ≫ a.act x)) :
    (∀ i, LieMult a (𝟙 _) (χ i) 1) ∧ ∀ ψ, (∀ i, χ i ≠ ψ) → LieMult a (𝟙 _) ψ 0 := by
  let b := Serre.Lie.basis a hv
  have hb : ∀ i x, x • b i = χ i x • b i := fun i x => by
    have h1 := h x i
    obtain e : v = fun i => (b i).hom := funext fun i => (Serre.Lie.hom_basis hv i).symm
    rw [e, Serre.Lie.isLieComb_iff] at h1
    refine (Serre.Lie.ext h1 : x • b i = _).trans ?_
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj]) (by simp), Pi.single_eq_same]
  refine ⟨fun i => ?_, fun ψ hψ => ?_⟩
  · have e : Serre.Lie.eig a (χ i) = Submodule.span k {b i} := by
      refine le_antisymm (fun w hw => ?_) ((Submodule.span_singleton_le_iff_mem _ _).2 (hb i))
      rw [← b.sum_repr w, Finset.sum_eq_single i (fun j _ hj => by
        rw [repr_eq_zero b χ hb (χ i) w hw j (hχ.ne hj), zero_smul]) (by simp)]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    rw [Serre.Lie.lieMult_id_iff, e]
    exact ⟨Module.finBasisOfFinrankEq _ _ (finrank_span_singleton (b.ne_zero i))⟩
  · have e : Serre.Lie.eig a ψ = ⊥ := by
      refine eq_bot_iff.2 fun w hw => ?_
      rw [Submodule.mem_bot, ← b.sum_repr w]
      exact Finset.sum_eq_zero fun j _ => by rw [repr_eq_zero b χ hb ψ w hw j (hψ j), zero_smul]
    rw [Serre.Lie.lieMult_id_iff, e]
    exact ⟨Module.Basis.empty _⟩

theorem exists_label {E K k : Type} [Field E] [NumberField E] [Field K] [CharZero K] [Field k] [IsAlgClosed k]
    (j : K →+* k) (lab : (E →+* ℂ) → (E →+* K)) (hl : Function.Injective lab) (τ : 𝓞 E →+* k) :
    ∃ t, τ = j.comp ((lab t).comp (algebraMap (𝓞 E) E)) := by
  have : CharZero k := j.charZero_iff j.injective |>.1 inferInstance
  have hτ : Function.Injective τ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_under_eq_bot (R := ℤ) ?_
    change Ideal.comap (algebraMap ℤ (𝓞 E)) (RingHom.ker τ) = ⊥
    rw [RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
    exact RingHom.injective_int _
  have hi : Function.Injective fun t => j.comp (lab t) := fun t t' e =>
    hl (RingHom.ext fun x => j.injective (RingHom.congr_fun e x))
  have hs := ((Fintype.bijective_iff_injective_and_card _).2
    ⟨hi, (Embeddings.card E ℂ).trans (Embeddings.card E k).symm⟩).2
  obtain ⟨t, ht⟩ := hs (IsFractionRing.lift hτ : E →+* k)
  refine ⟨t, RingHom.ext fun a => ?_⟩
  exact ((RingHom.congr_fun ht _).trans (IsFractionRing.lift_algebraMap hτ a)).symm

theorem hasType_of_isLieType : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] (H : Host E) (K : Type) [Field K] [NumberField K] (A : Out.PolAV (Sp (𝓞 K))) (x : KeyIn K) (φ : x.P.A.left ⟶ A.A.left) (hf : IsPolFibre (algebraMap (𝓞 K) K) A x.P φ) (oa : A.OAct (𝓞 E)) (act : OAct (𝓞 E) A.A) (S : Set (E →+* ℂ)) (τ : Fin x.P.g ≃ S) (lab : (E →+* ℂ) → (E →+* K)) (ρ : 𝓞 K), act.act = oa.act → Function.Injective lab → (∀ t, t ∈ S ↔ lab t (H.rt : E) = (ρ : K)) → IsLieType A oa x φ τ lab → HasType H act ρ 1 0 := by
  intro E _ _ _ _ H K _ _ A x φ hf oa act S τ lab ρ hact hl hS hT k _ _ β hβ σ
  obtain ⟨act', e⟩ := ellPull_exists_oAct hf.2.1 act
  have := x.P.isAb.comm
  have := x.P.smoothDim
  have : Smooth x.P.A.hom := SmoothOfRelativeDimension.smooth x.P.g _
  let res : (E →+* ℂ) → (𝓞 E →+* K) := fun t => (lab t).comp (algebraMap (𝓞 E) E)
  have hres : Function.Injective res := fun t t' h => hl (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) h)
  obtain ⟨h1, h0⟩ := lieMult_of_eigenbasis act' x.basis (fun i => res (τ i))
    (hres.comp (Subtype.val_injective.comp τ.injective)) fun a i => by
      obtain ⟨w, hw, ew⟩ := hT a i
      obtain rfl : w = x.v i ≫ act'.act a := by
        refine Over.OverMorphism.ext (hf.2.1.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
        rw [← ew, Over.comp_left, Category.assoc, e, hact]
      exact hw
  let j : K →+* k := IsFractionRing.lift hβ
  have hj : ∀ a : 𝓞 K, j a = β a := IsFractionRing.lift_algebraMap hβ
  obtain ⟨t, rfl⟩ := exists_label j lab hl σ
  have key : ∀ n, LieMult act' (𝟙 _) (res t) n → LieMult act (spMap β) (j.comp (res t)) n := fun n h => by
    rw [← LieExt.lieMult_extend_iff j, LiePull.lieMult_pull _ _ _ _ _ _ _ act act' hf.2.1 e,
      spMap_comp_spMap] at h
    convert h using 2
    exact (RingHom.ext hj).symm
  have ht : t ∈ S ↔ j.comp (res t) H.rt = β ρ := by
    rw [hS, ← hj]
    exact j.injective.eq_iff.symm
  refine ⟨fun h => key _ ?_, fun h => key _ (h0 _ fun i hi => h (ht.1 ?_))⟩
  · simpa using h1 (τ.symm ⟨t, ht.2 h⟩)
  · rw [← hres hi]
    exact (τ i).2

end GlobalTheory.LamF.LieType
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NormalisedDegreeCmEigenLineEq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem splits_of_injective_label {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K]
    {lab : (E →+* ℂ) → (E →+* K)} (hl : Function.Injective lab) : GlobalTheory.CM.Splits E K := by
  rw [GlobalTheory.CM.splits_iff_card]
  refine le_antisymm GlobalTheory.CM.card_ringHom_le_finrank ?_
  have h1 : Nat.card (E →+* ℂ) = Module.finrank ℚ E := by
    rw [Nat.card_eq_fintype_card]
    exact NumberField.Embeddings.card E ℂ
  rw [← h1]
  exact Nat.card_le_card_of_injective lab hl

theorem ndeg_vecLine_eq : DegSt → ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] (H : Host E) [NeZero H.d] (χ : DirichletCharacter ℂ H.d), IsKroneckerChar χ → (∀ a : 𝓞 E, star a = H.bar a) → ∀ (K : Type) [Field K] [NumberField K] (A : Out.PolAV (Sp (𝓞 K))) (oa : A.OAct (𝓞 E)) (x : KeyIn K) (φ : x.P.A.left ⟶ A.A.left) (S : Set (E →+* ℂ)) (τ : Fin x.P.g ≃ S) (lab : (E →+* ℂ) → (E →+* K)) (ρ : 𝓞 K), IsFibreOf A x (gmap K) φ → Function.Injective lab → ρ ^ 2 = -(H.d : 𝓞 K) → (∀ t, t ∈ S ↔ lab t (H.rt : E) = (ρ : K)) → IsLieType A oa x φ τ lab → ∀ (i : Fin x.P.g) (ℓ : MLine K), IsVecLine A x φ i ℓ → ℓ.ndeg = (logOm E χ).re / 2 := by
  intro hD hU hL E _ _ _ _ H _ χ hχ hstar K _ _ A oa x φ S τ lab ρ hfib hl hρ hS hLie i ℓ hℓ
  have hf : IsPolFibre (algebraMap (𝓞 K) K) A x.P φ :=
    (GlobalTheory.LamF.isFibreOf_iff_isPolFibre (𝓞 K) K (algebraMap (𝓞 K) K) A x φ).1 hfib
  have hoa : ∃ act : OAct (𝓞 E) A.A, act.act = oa.act := by
    exact (GlobalTheory.LamF.ringAct_iff_oAct (𝓞 E) _ A.A).1 oa.1
  obtain ⟨act, hact⟩ := hoa
  have hsplit : GlobalTheory.CM.Splits E K := splits_of_injective_label hl
  have htype : HasType H act ρ 1 0 :=
    GlobalTheory.LamF.LieType.hasType_of_isLieType E H K A x φ hf oa act S τ lab ρ hact hl hS hLie
  have hlam : ∀ a, LamEq A.L (act.act a) (𝟙 A.A) A.L (𝟙 A.A) (act.act (H.bar a)) := by
    intro a
    have hr := oa.rosati a
    rw [← hact, hstar] at hr
    exact (GlobalTheory.RosLam.rosatiAdj_iff_lamEq hL.globalFns _ A (act.act a) (act.act (H.bar a))
      (act.hom a) (act.hom (H.bar a))).1 hr
  set F : GenFib A := GenFib.mk x.P φ hf x.v x.basis with hF
  obtain ⟨⟨h, hh⟩, -⟩ := GlobalTheory.CM.LieMetric.exists_unique_isHerm hU hL K A F
  set t : 𝓞 E →+* 𝓞 K := RingOfIntegers.mapRingHom (lab (τ i)) with ht
  have htv : ∀ a : 𝓞 E, (t a : K) = lab (τ i) (a : E) := fun a => rfl
  have hti : t H.rt = ρ := by
    apply RingOfIntegers.ext
    rw [htv]
    exact (hS (τ i)).1 (τ i).2
  have hdeg := GlobalTheory.T.two_mul_deg_eigenLattice_polarizedAbelianScheme hD hU hL E H χ hχ K ρ A act hlam hsplit hρ htype F h hh t hti
  have hline : deg h (F.eigLat act t) = ℓ.ndeg := by
    refine GlobalTheory.LamF.deg_eq_ndeg_of_line K (Fin x.P.g → K) h (F.eigLat act t) (Pi.single i 1) ℓ ?_ hℓ.1 ?_ ?_
    · intro h0
      have := congrFun h0 i
      simp at this
    · intro z
      rw [GlobalTheory.LamF.EigLine.mem_eigLat_iff E K A x φ hf oa act S τ lab hact hl hLie i t htv z]
      constructor
      · rintro ⟨hz, r, rfl⟩
        refine ⟨r, ?_, ?_⟩
        · exact (GlobalTheory.T.mem_lieVector_line_ideal_iff_mem_lie_lattice K A x φ hf i ℓ hℓ r).2 hz
        · ext j
          by_cases hj : j = i
          · subst hj; simp
          · simp [hj]
      · rintro ⟨c, hc, rfl⟩
        refine ⟨?_, c, ?_⟩
        · have := (GlobalTheory.T.mem_lieVector_line_ideal_iff_mem_lie_lattice K A x φ hf i ℓ hℓ c).1 hc
          convert this using 1
          ext j
          by_cases hj : j = i
          · subst hj; simp
          · simp [hj]
        · ext j
          by_cases hj : j = i
          · subst hj; simp
          · simp [hj]
    · exact GlobalTheory.CM.LieMetric.vecLine_norm_sq_eq_form hU hL K A x φ hf h hh i ℓ hℓ
  have hre := congrArg Complex.re hdeg
  rw [Complex.ofReal_re] at hre
  rw [← hline]
  linarith

end GlobalTheory.LamF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NormalisedDegreeCmEigenLineEqStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalisedDegree_cmEigenLine_eq : DegSt → ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] (H : Host E) [NeZero H.d] (χ : DirichletCharacter ℂ H.d), IsKroneckerChar χ → (∀ a : 𝓞 E, star a = H.bar a) → ∀ (K : Type) [Field K] [NumberField K] (A : Out.PolAV (Sp (𝓞 K))) (oa : A.OAct (𝓞 E)) (x : KeyIn K) (φ : x.P.A.left ⟶ A.A.left) (S : Set (E →+* ℂ)) (τ : Fin x.P.g ≃ S) (lab : (E →+* ℂ) → (E →+* K)) (ρ : 𝓞 K), IsFibreOf A x (gmap K) φ → Function.Injective lab → ρ ^ 2 = -(H.d : 𝓞 K) → (∀ t, t ∈ S ↔ lab t (H.rt : E) = (ρ : K)) → IsLieType A oa x φ τ lab → ∀ (i : Fin x.P.g) (ℓ : MLine K), IsVecLine A x φ i ℓ → ℓ.ndeg = (logOm E χ).re / 2 := by
  first | exact @GlobalTheory.LamF.ndeg_vecLine_eq | exact GlobalTheory.LamF.ndeg_vecLine_eq | (intros; apply GlobalTheory.LamF.ndeg_vecLine_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmLieLineDegreeOfEigenLineDegreeFormula
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem lamDegSt_of_degSt : DegSt → ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [NeZero H.d] (χ : DirichletCharacter ℂ H.d), IsKroneckerChar χ → LamDegSt H (logOm E χ).re := by
  intro hD hU hL E _ _ _ H _ χ hχ _ l c hstar nΨ n' f o La ho
  obtain ⟨-, -, -, -, hΨ, h', -, -, -, tΨ, t', -, -, -, -, -, vΨ, v', -⟩ := ho
  obtain ⟨hb, -, -, ρ, hρ, h1, h2, -⟩ := labK_spec E H l c o.K₁
  exact ⟨fun k => GlobalTheory.T.normalisedDegree_cmEigenLine_eq hD hU hL E H χ hχ hstar o.K₁ o.AΨ o.oaΨ o.xΨ o.φΨg (psiSet H) o.τΨ (labK c o.K₁) ρ
      hΨ hb.1 hρ h1 tΨ k _ (vΨ k),
    fun k => GlobalTheory.T.normalisedDegree_cmEigenLine_eq hD hU hL E H χ hχ hstar o.K₁ o.A' o.oa' o.x' o.φ'g (psiSet H)ᶜ o.τ' (labK c o.K₁) (-ρ)
      h' hb.1 (by rw [neg_sq, hρ]) h2 t' k _ (v' k)⟩

end GlobalTheory.LamF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmLieLineDegreeOfEigenLineDegreeFormulaStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmLieLineDegree_of_eigenLineDegreeFormula : DegSt → ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [NeZero H.d] (χ : DirichletCharacter ℂ H.d), IsKroneckerChar χ → LamDegSt H (logOm E χ).re := by
  first | exact @GlobalTheory.LamF.lamDegSt_of_degSt | exact GlobalTheory.LamF.lamDegSt_of_degSt | (intros; apply GlobalTheory.LamF.lamDegSt_of_degSt <;> assumption)
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

theorem GlobalTheory.LamF.lamDegSt_logOm : ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [NeZero H.d] (χ : DirichletCharacter ℂ H.d), IsKroneckerChar χ → LamDegSt H (logOm E χ).re :=
  fun hΘ hL =>
    GlobalTheory.T.cmLieLineDegree_of_eigenLineDegreeFormula
      (GlobalTheory.T.cmEigenLine_degreeFormula (GlobalTheory.T.cmEllipticCurve_exists_of_uniformisation hΘ hL.polBaseChange GlobalTheory.T.semiAbelian_hom_extends_uniquely_over_dvr) hΘ hL GlobalTheory.T.semiAbelian_hom_extends_uniquely_over_dvr) hΘ hL
