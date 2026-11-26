module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjDescendLowerLevel
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ValuationCoeEqNorm
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PowEqScaleAndExistsUniqueTorsion

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionLocalPresentationSmoothGroup
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionLocalPresentationSmoothGroup
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.TorsionPres

section Alg

variable {O : Type} [CommRing O] [IsLocalRing O] {B : Type} [CommRing B] [Algebra O B]

theorem exists_lift_atPrime (e : B →ₐ[O] O) (S : Type) [CommRing S] [Algebra B S] [Algebra O S]
    [IsScalarTower O B S] [IsLocalization.AtPrime S ((IsLocalRing.maximalIdeal O).comap e)]
    {A : Type} [CommRing A] [Algebra O A] (h : B →ₐ[O] A)
    (hh : ∀ b, IsUnit (e b) → IsUnit (h b)) :
    ∃ φ : S →ₐ[O] A, ∀ b, φ (algebraMap B S b) = h b := by
  have hu : ∀ t : ((IsLocalRing.maximalIdeal O).comap e).primeCompl, IsUnit (h t) := fun t =>
    hh _ (IsLocalRing.notMem_maximalIdeal.mp t.2)
  exact ⟨IsLocalization.liftAlgHom (S := S) hu, fun b => by
    simp [IsLocalization.liftAlgHom_apply]⟩

theorem isUnit_of_aug (e : B →ₐ[O] O) (S : Type) [CommRing S] [Algebra B S] [Algebra O S]
    [IsScalarTower O B S] [IsLocalization.AtPrime S ((IsLocalRing.maximalIdeal O).comap e)]
    (eS : S →ₐ[O] O) (he : ∀ b, eS (algebraMap B S b) = e b) (s : S) (hs : IsUnit (eS s)) :
    IsUnit s := by
  obtain ⟨⟨b, t⟩, h⟩ :=
    IsLocalization.surj ((IsLocalRing.maximalIdeal O).comap e).primeCompl s
  have ht : IsUnit (e t) := IsLocalRing.notMem_maximalIdeal.mp t.2
  have hb : IsUnit (e b) := by
    have := congrArg eS h
    simp only [map_mul, he] at this
    rw [← this]
    exact hs.mul ht
  have hb' : b ∈ ((IsLocalRing.maximalIdeal O).comap e).primeCompl :=
    IsLocalRing.notMem_maximalIdeal.mpr hb
  have := IsLocalization.map_units S (⟨b, hb'⟩ : ((IsLocalRing.maximalIdeal O).comap e).primeCompl)
  exact isUnit_of_mul_isUnit_left (h ▸ this)

variable {g : ℕ}

theorem exists_smul_ker_le (π : MvPolynomial (Fin g) O →ₐ[O] B) (hπ : π.toRingHom.Etale)
    (e : B →ₐ[O] O) :
    ∃ r : B, e r = 1 ∧ ∀ b, e b = 0 → r * b ∈ Ideal.span (Set.range fun i =>
      π (MvPolynomial.X i) - algebraMap O B (e (π (MvPolynomial.X i)))) := by
  set J : Ideal B := Ideal.span (Set.range fun i =>
      π (MvPolynomial.X i) - algebraMap O B (e (π (MvPolynomial.X i)))) with hJ
  set I : Ideal B := RingHom.ker e with hI
  have hsub : ∀ b, b - algebraMap O B (e b) ∈ I := fun b => by
    simp [hI, RingHom.mem_ker]
  have h1 : Ideal.Quotient.mkₐ O (J ⊔ I * I) =
      (Ideal.Quotient.mkₐ O (J ⊔ I * I)).comp ((Algebra.ofId O B).comp e) := by
    refine GlobalTheory.NilCoord.ext_of_nil π hπ _ _ (fun b => ⟨2, ?_⟩) (fun j => ?_)
    · simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Algebra.ofId_apply]
      rw [← map_sub, ← map_pow, Ideal.Quotient.eq_zero_iff_mem, pow_two]
      exact Ideal.mem_sup_right (Ideal.mul_mem_mul (hsub b) (hsub b))
    · simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Algebra.ofId_apply]
      rw [Ideal.Quotient.eq]
      exact Ideal.mem_sup_left (Ideal.subset_span ⟨j, rfl⟩)
  have h2 : I ≤ J ⊔ I • I := by
    intro b hb
    have := AlgHom.congr_fun h1 b
    have hb' : e b = 0 := hb
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Algebra.ofId_apply, hb', map_zero] at this
    exact Ideal.Quotient.eq_zero_iff_mem.mp this
  have hfp : Algebra.FinitePresentation O B := by
    letI : Algebra (MvPolynomial (Fin g) O) B := π.toRingHom.toAlgebra
    haveI : Algebra.Etale (MvPolynomial (Fin g) O) B := hπ
    haveI : IsScalarTower O (MvPolynomial (Fin g) O) B :=
      IsScalarTower.of_algebraMap_eq fun r => (π.commutes r).symm
    exact Algebra.FinitePresentation.trans O (MvPolynomial (Fin g) O) B
  have hfg : I.FG := Algebra.FinitePresentation.ker_fG_of_surjective e
    (fun c => ⟨algebraMap O B c, by simp⟩)
  obtain ⟨r, hr1, hr2⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup hfg le_rfl h2
  refine ⟨r, ?_, fun b hb => hr2 (Submodule.smul_mem_pointwise_smul b r I hb)⟩
  have : e (r - 1) = 0 := hr1
  rwa [map_sub, map_one, sub_eq_zero] at this

theorem exists_coords (π : MvPolynomial (Fin g) O →ₐ[O] B) (hπ : π.toRingHom.Etale)
    (e : B →ₐ[O] O) (S : Type) [CommRing S] [Algebra B S] [Algebra O S]
    [IsScalarTower O B S] [IsLocalization.AtPrime S ((IsLocalRing.maximalIdeal O).comap e)]
    (eS : S →ₐ[O] O) (he : ∀ b, eS (algebraMap B S b) = e b) :
    ∃ x : Fin g → S, RingHom.ker eS = Ideal.span (Set.range x) ∧
      (∀ j, ∃ v : S →ₐ[O] DualNumber O, (TrivSqZeroExt.fstHom O O O).comp v = eS ∧
        ∀ i, v (x i) = TrivSqZeroExt.inr (if i = j then 1 else 0)) ∧
      ∃ ρ : S →ₐ[O] MvPowerSeries (Fin g) (IsLocalRing.ResidueField O),
        ∀ i, ρ (x i) = MvPowerSeries.X i := by
  let x : Fin g → S := fun i =>
    algebraMap B S (π (MvPolynomial.X i) - algebraMap O B (e (π (MvPolynomial.X i))))
  letI : Algebra (MvPolynomial (Fin g) O) B := π.toRingHom.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin g) O) B := hπ
  haveI : IsScalarTower O (MvPolynomial (Fin g) O) B :=
    IsScalarTower.of_algebraMap_eq fun r => (π.commutes r).symm
  refine ⟨x, le_antisymm ?_ ?_, fun j => ?_, ?_⟩
  · obtain ⟨r, hr1, hr2⟩ := exists_smul_ker_le π hπ e
    intro s hs
    have hs' : eS s = 0 := hs
    obtain ⟨⟨b, t⟩, h⟩ :=
      IsLocalization.surj ((IsLocalRing.maximalIdeal O).comap e).primeCompl s
    have hb : e b = 0 := by
      have := congrArg eS h
      simp only [map_mul, he, hs', zero_mul] at this
      exact this.symm
    have h3 : algebraMap B S (r * b) ∈ Ideal.span (Set.range x) := by
      have := Ideal.mem_map_of_mem (algebraMap B S) (hr2 b hb)
      rwa [Ideal.map_span, ← Set.range_comp] at this
    have hr : IsUnit (algebraMap B S r) := isUnit_of_aug e S eS he _ (by rw [he, hr1]; exact isUnit_one)
    have ht : IsUnit (algebraMap B S t) := IsLocalization.map_units S t
    rw [map_mul, ← h, Ideal.unit_mul_mem_iff_mem _ hr, Ideal.mul_unit_mem_iff_mem _ ht] at h3
    exact h3
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simp [x, he, RingHom.mem_ker]
  · obtain ⟨φ, h1, h2⟩ := GlobalTheory.NilCoord.exists_of_nil π hπ
      ((Algebra.ofId O (DualNumber O)).comp e)
      (fun i => TrivSqZeroExt.inr (if i = j then (1 : O) else 0))
      (fun i => ⟨2, by rw [pow_two, TrivSqZeroExt.inr_mul_inr]⟩)
    have h3 : (TrivSqZeroExt.fstHom O O O).comp φ = e := by
      refine GlobalTheory.NilCoord.ext_of_nil π hπ _ _ (fun b => ?_) (fun i => ?_)
      · simpa [Algebra.ofId_apply, TrivSqZeroExt.algebraMap_eq_inl] using (h1 b).map (TrivSqZeroExt.fstHom O O O)
      · rw [AlgHom.comp_apply, h2, map_add (f := _)]
        exact add_zero _
    obtain ⟨v, hv⟩ := exists_lift_atPrime e S φ (fun b hb => by
      rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
      rwa [← h3] at hb)
    refine ⟨v, ?_, fun i => ?_⟩
    · refine IsLocalization.algHom_ext ((IsLocalRing.maximalIdeal O).comap e).primeCompl ?_
      ext b
      show (v (algebraMap B S b)).fst = eS (algebraMap B S b)
      rw [hv, he]
      exact AlgHom.congr_fun h3 b
    · simp [x, hv, h2, Algebra.ofId_apply]
  · let A := MvPowerSeries (Fin g) (IsLocalRing.ResidueField O)
    let ρ : MvPolynomial (Fin g) O →ₐ[O] A :=
      MvPolynomial.aeval (fun j => algebraMap O A (e (π (MvPolynomial.X j))) + MvPowerSeries.X j)
    letI : Algebra (MvPolynomial (Fin g) O) A := ρ.toRingHom.toAlgebra
    let J : Ideal A := Ideal.span (Set.range MvPowerSeries.X)
    have hf₀ : ((Ideal.Quotient.mkₐ O J).comp ((Algebra.ofId O A).comp e)).comp π =
        (Ideal.Quotient.mkₐ O J).comp ρ := by
      apply MvPolynomial.algHom_ext
      intro j
      simp only [AlgHom.coe_comp, Function.comp_apply, Ideal.Quotient.mkₐ_eq_mk, ρ,
        MvPolynomial.aeval_X, Algebra.ofId_apply]
      rw [eq_comm, Ideal.Quotient.eq, add_sub_cancel_left]
      exact Ideal.subset_span ⟨j, rfl⟩
    let f₀ : B →ₐ[MvPolynomial (Fin g) O] A ⧸ J :=
      { ((Ideal.Quotient.mkₐ O J).comp ((Algebra.ofId O A).comp e)).toRingHom with
        commutes' := fun p => AlgHom.congr_fun hf₀ p }
    obtain ⟨φ', hφ'⟩ := Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete (I := J) f₀
    have hc : ∀ p, φ' (π p) = ρ p := fun p => φ'.commutes p
    let φ : B →ₐ[O] A := { φ'.toRingHom with
      commutes' := fun r => by
        show φ' (algebraMap O B r) = _
        rw [← π.commutes, hc, ρ.commutes] }
    have hφ : ∀ b, φ b = φ' b := fun _ => rfl
    have hJ : J ≤ RingHom.ker (MvPowerSeries.constantCoeff) := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact MvPowerSeries.constantCoeff_X i
    obtain ⟨v, hv⟩ := exists_lift_atPrime e S φ (fun b hb => by
      have e1 : Ideal.Quotient.mk J (φ' b) = Ideal.Quotient.mk J (algebraMap O A (e b)) :=
        AlgHom.congr_fun hφ' b
      rw [Ideal.Quotient.eq] at e1
      have e2 := hJ e1
      rw [RingHom.mem_ker, map_sub, sub_eq_zero] at e2
      rw [hφ, MvPowerSeries.isUnit_iff_constantCoeff, e2]
      exact (hb.map _).map _)
    refine ⟨v, fun i => ?_⟩
    simp only [x]
    rw [hv, map_sub, AlgHom.commutes, hφ, hc]
    simp [ρ]

end Alg

section Geo

variable {O : Type} [CommRing O] [IsLocalRing O] {G : Over (Sp O)} [GrpObj G]

theorem exists_pt_of_aug (C : Chart.Chart G) {A : Type} [CommRing A] [Algebra O A] (α : A →ₐ[O] O)
    (hα : ∀ a, IsUnit (α a) → IsUnit a) (z : specO O A ⟶ G) (hz : ptMap α ≫ z = 1) :
    ∃ h : Γ(G.left, C.U) →ₐ[O] A, z = Chart.pt C h ∧ α.comp h = Chart.eps C := by
  haveI : IsLocalHom α.toRingHom := ⟨hα⟩
  haveI : IsLocalRing A := RingHom.domain_isLocalRing α.toRingHom
  have hz' : Chart.spMap α ≫ z = Chart.pt C ((Algebra.ofId O O).comp (Chart.eps C)) :=
    hz.trans (Chart.pt_eps C O).symm
  have hU : ⊤ ≤ z.left ⁻¹ᵁ C.U := by
    intro p _
    have hsp : (p : PrimeSpectrum A) ⤳ IsLocalRing.closedPoint A :=
      (PrimeSpectrum.le_iff_specializes _ _).mp
        (IsLocalRing.le_maximalIdeal (p : PrimeSpectrum A).isPrime.ne_top)
    refine hsp.mem_open (z.left ⁻¹ᵁ C.U).isOpen ?_
    let p₀ : ↥(Spec (CommRingCat.of O)) := IsLocalRing.closedPoint O
    have hp : (Spec.map (CommRingCat.ofHom α.toRingHom)).base p₀ = IsLocalRing.closedPoint A :=
      IsLocalRing.comap_closedPoint α.toRingHom
    have e := congrArg (fun y : Chart.sp O ⟶ G => y.left.base p₀) hz'
    simp only [Over.comp_left, Chart.spMap_left, Chart.pt_left, Scheme.Hom.comp_apply] at e
    show z.left (IsLocalRing.closedPoint A) ∈ C.U
    rw [← hp, e]
    exact C.hU.range_fromSpec.subset (Set.mem_range_self _)
  obtain ⟨h, rfl⟩ := Chart.exists_pt C z hU
  refine ⟨h, rfl, ?_⟩
  rw [Chart.spMap_pt] at hz'
  exact Chart.pt_injective C hz'

theorem exists_local_ring (G : Over (Sp O)) [GrpObj G] (g : ℕ)
    (hG : SmoothOfRelativeDimension g G.hom) :
    ∃ (S : Type) (_ : CommRing S) (_ : Algebra O S) (u : specO O S ⟶ G) (eS : S →ₐ[O] O)
      (x : Fin g → S),
      (∀ s, IsUnit (eS s) → IsUnit s) ∧
      (∀ (A : Type) [CommRing A] [Algebra O A], ptMap ((Algebra.ofId O A).comp eS) ≫ u = 1) ∧
      (∀ (A : Type) [CommRing A] [Algebra O A] (φ ψ : S →ₐ[O] A),
        ptMap φ ≫ u = ptMap ψ ≫ u → φ = ψ) ∧
      (∀ (A : Type) [CommRing A] [Algebra O A] (α : A →ₐ[O] O), (∀ a, IsUnit (α a) → IsUnit a) →
        ∀ z : specO O A ⟶ G, ptMap α ≫ z = 1 → ∃ φ : S →ₐ[O] A, ptMap φ ≫ u = z) ∧
      RingHom.ker eS = Ideal.span (Set.range x) ∧
      (∀ j, ∃ v : S →ₐ[O] DualNumber O, (TrivSqZeroExt.fstHom O O O).comp v = eS ∧
        ∀ i, v (x i) = TrivSqZeroExt.inr (if i = j then 1 else 0)) ∧
      ∃ ρ : S →ₐ[O] MvPowerSeries (Fin g) (IsLocalRing.ResidueField O),
        ∀ i, ρ (x i) = MvPowerSeries.X i := by
  obtain ⟨C, π, hπ⟩ := GlobalTheory.NilCoord.exists_etale_chart G g hG
  let e := Chart.eps C
  let S := Localization.AtPrime ((IsLocalRing.maximalIdeal O).comap e)
  obtain ⟨eS, he⟩ := exists_lift_atPrime e S e (fun _ h => h)
  obtain ⟨x, hx⟩ := exists_coords π hπ e S eS he
  let κ : Γ(G.left, C.U) →ₐ[O] S := IsScalarTower.toAlgHom O _ S
  have hpt : ∀ (A : Type) [CommRing A] [Algebra O A] (φ : S →ₐ[O] A),
      ptMap φ ≫ Chart.pt C κ = Chart.pt C (φ.comp κ) := fun A _ _ φ => Chart.spMap_pt C φ κ
  refine ⟨S, inferInstance, inferInstance, Chart.pt C κ, eS, x, isUnit_of_aug e S eS he,
    fun A _ _ => ?_, fun A _ _ φ ψ h => ?_, fun A _ _ α hα z hz => ?_, hx⟩
  · rw [hpt, ← Chart.pt_eps C A]
    congr 1
    ext b
    exact congrArg (algebraMap O A) (he b)
  · rw [hpt, hpt] at h
    have h1 := Chart.pt_injective C h
    refine AlgHom.coe_ringHom_injective (IsLocalization.ringHom_ext
      ((IsLocalRing.maximalIdeal O).comap e).primeCompl ?_)
    ext b
    exact AlgHom.congr_fun h1 b
  · obtain ⟨h, rfl, hh⟩ := exists_pt_of_aug C α hα z hz
    obtain ⟨φ, hφ⟩ := exists_lift_atPrime e S h (fun b hb => hα _ (by
      rwa [← AlgHom.comp_apply, hh]))
    refine ⟨φ, ?_⟩
    rw [hpt]
    congr 1
    ext b
    exact hφ b

end Geo

theorem local_presentation : ∀ (O : Type) [CommRing O] [IsLocalRing O] (G : Over (Sp O)) [GrpObj G] [IsCommMonObj G] (n : ℕ) (H : Type) [CommRing H] [Algebra O H] [Module.Finite O H] (y : specO O H ⟶ G) (g : ℕ), SmoothOfRelativeDimension g G.hom → y ^ n = 1 → (∀ (S : Type) [CommRing S] [Algebra O S] (z : specO O S ⟶ G), z ^ n = 1 → ∃! φ : H →ₐ[O] S, ptMap φ ≫ y = z) → ∀ (ε : H →ₐ[O] O), ptMap ε ≫ y = 1 → ∀ (T : Type) [CommRing T] [Algebra H T] [Algebra O T] [IsScalarTower O H T] [IsLocalization.AtPrime T ((IsLocalRing.maximalIdeal O).comap ε)] (εT : T →ₐ[O] O), (∀ h, εT (algebraMap H T h) = ε h) → ∃ (S : Type) (_ : CommRing S) (_ : Algebra O S) (π : S →ₐ[O] T) (x : Fin g → S) (a : Matrix (Fin g) (Fin g) S) (ρ : S →+* MvPowerSeries (Fin g) (IsLocalRing.ResidueField O)), Function.Surjective π ∧ RingHom.ker π = Ideal.span (Set.range (a.mulVec x)) ∧ RingHom.ker εT = Ideal.span (Set.range fun i => π (x i)) ∧ (∀ i j, εT (π (a i j)) = if i = j then (n : O) else 0) ∧ (∀ i, ρ (x i) = MvPowerSeries.X i) ∧ ∀ c ∈ IsLocalRing.maximalIdeal O, ρ (algebraMap O S c) = 0 := by
  intro O _ _ G _ _ n H _ _ _ y g hG hy huniv ε hε T _ _ _ _ _ εT hεT
  obtain ⟨S, _, _, u, eS, x, hloc, hone, hinj, hex, hker, hv, ρ, hρ⟩ := exists_local_ring G g hG
  have hcomp : ∀ {A A' A'' : Type} [CommRing A] [Algebra O A] [CommRing A'] [Algebra O A']
      [CommRing A''] [Algebra O A''] (φ : A →ₐ[O] A') (ψ : A' →ₐ[O] A'') (z : specO O A ⟶ G),
      ptMap (ψ.comp φ) ≫ z = ptMap ψ ≫ ptMap φ ≫ z := fun φ ψ z => by
    rw [← Category.assoc, GlobalTheory.TangentPow.ptMap_comp_ptMap]
  have hone' : ptMap eS ≫ u = 1 := by
    have := hone O
    rwa [show (Algebra.ofId O O).comp eS = eS from by ext; simp] at this
  obtain ⟨ν, hν⟩ := hex S eS hloc (u ^ n) (by rw [comp_pow, hone', one_pow])
  have heν : eS.comp ν = eS := hinj _ _ _ (by rw [hcomp, hν, comp_pow, hone', one_pow])
  have hxk : ∀ i, eS (x i) = 0 := fun i => by
    have : x i ∈ RingHom.ker eS := hker ▸ Ideal.subset_span ⟨i, rfl⟩
    exact this
  have ha : ∀ i, ∃ c : Fin g → S, ∑ j, c j * x j = ν (x i) := fun i => by
    rw [← Ideal.mem_span_range_iff_exists_fun, ← hker, RingHom.mem_ker, ← AlgHom.comp_apply, heν,
      hxk]
  choose a ha using ha
  have hax : Matrix.mulVec (Matrix.of a) x = fun i => ν (x i) := funext fun i => ha i
  let κ : H →ₐ[O] T := IsScalarTower.toAlgHom O H T
  have hεκ : εT.comp κ = ε := AlgHom.ext hεT
  obtain ⟨π, hπ⟩ := hex T εT (isUnit_of_aug ε T εT hεT) (ptMap κ ≫ y) (by rw [← hcomp, hεκ, hε])
  have hεπ : εT.comp π = eS := hinj _ _ _ (by rw [hcomp, hπ, ← hcomp, hεκ, hε, hone'])
  have hπν : π.comp ν = (Algebra.ofId O T).comp eS := hinj _ _ _ (by
    rw [hone, hcomp, hν, comp_pow, hπ, ← comp_pow, hy, comp_one])
  set K : Ideal S := Ideal.span (Set.range fun i => ν (x i)) with hK
  have hKπ : K ≤ RingHom.ker π := by
    rw [hK, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    have := AlgHom.congr_fun hπν (x i)
    simpa [hxk, RingHom.mem_ker] using this
  let q : S →ₐ[O] S ⧸ K := Ideal.Quotient.mkₐ O K
  have hqν : q.comp ν = (Algebra.ofId O (S ⧸ K)).comp eS := by
    ext s
    have h1 : s - algebraMap O S (eS s) ∈ Ideal.span (Set.range x) := by
      rw [← hker]
      simp [RingHom.mem_ker]
    have h2 := Ideal.mem_map_of_mem ν h1
    rw [Ideal.map_span, ← Set.range_comp, map_sub, AlgHom.commutes] at h2
    exact Ideal.Quotient.eq.mpr h2
  obtain ⟨φ, hφ, -⟩ := huniv (S ⧸ K) (ptMap q ≫ u) (by rw [← comp_pow, ← hν, ← hcomp, hqν, hone])
  let πq : (S ⧸ K) →ₐ[O] T := Ideal.Quotient.liftₐ K π fun s hs => hKπ hs
  have hπq : πq.comp q = π := by ext; rfl
  have hπφ : πq.comp φ = κ := by
    refine (huniv T (ptMap κ ≫ y) (by rw [← comp_pow, hy, comp_one])).unique ?_ rfl
    rw [hcomp, hφ, ← hcomp, hπq, hπ]
  obtain ⟨ψ, hψ⟩ := exists_lift_atPrime ε T φ (fun h hh => by
    obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (φ h)
    have : eS s = ε h := by
      rw [← hεπ, ← hπq, ← hεκ, ← hπφ]
      simp only [AlgHom.comp_apply]
      rw [← hs]
      rfl
    rw [← hs]
    exact (hloc s (this ▸ hh)).map _)
  have hψκ : ψ.comp κ = φ := AlgHom.ext hψ
  have hψπ : ψ.comp π = q := hinj _ _ _ (by rw [hcomp, hπ, ← hcomp, hψκ, hφ])
  have hid : πq.comp ψ = AlgHom.id O T := by
    refine AlgHom.coe_ringHom_injective (IsLocalization.ringHom_ext
      ((IsLocalRing.maximalIdeal O).comap ε).primeCompl ?_)
    ext h
    show πq (ψ (algebraMap H T h)) = algebraMap H T h
    rw [hψ]
    exact AlgHom.congr_fun hπφ h
  have hsurj : Function.Surjective π := fun t => by
    obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (ψ t)
    refine ⟨s, ?_⟩
    have : πq (ψ t) = t := AlgHom.congr_fun hid t
    rw [← this, ← hs]
    rfl
  refine ⟨S, inferInstance, inferInstance, π, x, Matrix.of a, ρ.toRingHom, hsurj, ?_, ?_, ?_, hρ, ?_⟩
  · rw [hax]
    refine le_antisymm (fun s hs => ?_) hKπ
    have h1 : π s = 0 := hs
    have h2 : ψ (π s) = q s := AlgHom.congr_fun hψπ s
    rw [h1, map_zero] at h2
    exact Ideal.Quotient.eq_zero_iff_mem.mp h2.symm
  · refine le_antisymm (fun t ht => ?_) ?_
    · obtain ⟨s, rfl⟩ := hsurj t
      have h1 : s ∈ RingHom.ker eS := by
        rw [← hεπ]
        exact ht
      have h2 := Ideal.mem_map_of_mem π (hker ▸ h1)
      rwa [Ideal.map_span, ← Set.range_comp] at h2
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact (AlgHom.congr_fun hεπ (x i)).trans (hxk i)
  · intro i j
    obtain ⟨v, hv1, hv2⟩ := hv j
    have h1 := GlobalTheory.TangentPow.pow_eq_scale_comp (y := ptMap v ≫ u) (by rw [← hcomp, hv1, hone']) n
    rw [← comp_pow, ← hν, ← hcomp, ← hcomp] at h1
    have h2 := congrArg TrivSqZeroExt.snd (AlgHom.congr_fun (hinj _ _ _ h1) (x i))
    have h3 : ∀ s, (v s).fst = eS s := fun s => AlgHom.congr_fun hv1 s
    rw [AlgHom.comp_apply, ← ha] at h2
    have h4 : εT (π (Matrix.of a i j)) = eS (a i j) := AlgHom.congr_fun hεπ _
    rw [h4]
    have h5 : eS (a i j) = n * TrivSqZeroExt.snd (if i = j then DualNumber.eps else 0 : DualNumber O) := by
      simpa [hv2, h3, TrivSqZeroExt.snd_sum] using h2
    rw [h5]
    split_ifs <;> simp
  · intro c hc
    show ρ (algebraMap O S c) = 0
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply O (IsLocalRing.ResidueField O),
      IsLocalRing.ResidueField.algebraMap_eq, (IsLocalRing.residue_eq_zero_iff c).mpr hc, map_zero]

end GlobalTheory.TorsionPres
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionLocalPresentationSmoothGroupStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.torsion_local_presentation_smooth_group : ∀ (O : Type) [CommRing O] [IsLocalRing O] (G : Over (Sp O)) [GrpObj G] [IsCommMonObj G] (n : ℕ) (H : Type) [CommRing H] [Algebra O H] [Module.Finite O H] (y : specO O H ⟶ G) (g : ℕ), SmoothOfRelativeDimension g G.hom → y ^ n = 1 → (∀ (S : Type) [CommRing S] [Algebra O S] (z : specO O S ⟶ G), z ^ n = 1 → ∃! φ : H →ₐ[O] S, ptMap φ ≫ y = z) → ∀ (ε : H →ₐ[O] O), ptMap ε ≫ y = 1 → ∀ (T : Type) [CommRing T] [Algebra H T] [Algebra O T] [IsScalarTower O H T] [IsLocalization.AtPrime T ((IsLocalRing.maximalIdeal O).comap ε)] (εT : T →ₐ[O] O), (∀ h, εT (algebraMap H T h) = ε h) → ∃ (S : Type) (_ : CommRing S) (_ : Algebra O S) (π : S →ₐ[O] T) (x : Fin g → S) (a : Matrix (Fin g) (Fin g) S) (ρ : S →+* MvPowerSeries (Fin g) (IsLocalRing.ResidueField O)), Function.Surjective π ∧ RingHom.ker π = Ideal.span (Set.range (a.mulVec x)) ∧ RingHom.ker εT = Ideal.span (Set.range fun i => π (x i)) ∧ (∀ i j, εT (π (a i j)) = if i = j then (n : O) else 0) ∧ (∀ i, ρ (x i) = MvPowerSeries.X i) ∧ ∀ c ∈ IsLocalRing.maximalIdeal O, ρ (algebraMap O S c) = 0 := by
  first | exact @GlobalTheory.TorsionPres.local_presentation | exact GlobalTheory.TorsionPres.local_presentation | (intros; apply GlobalTheory.TorsionPres.local_presentation <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIntegralOfLocalPresentationPow
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.DetNotMemSpanMulVecOfSocle
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.DetUpdateRowAlternatingMulVecMem
open scoped TensorProduct

namespace GlobalTheory

theorem det_updateRow_single_mul_sub_mem {T : Type} [CommRing T] {g : ℕ} (x : Fin g → T)
    (I : Ideal T) (m : Matrix (Fin g) (Fin g) T) (p : Fin g)
    (hm : ∀ q, q ≠ p → m.mulVec x q ∈ I) (i j : Fin g) :
    x j * (m.updateRow p (Pi.single i 1)).det - x i * (m.updateRow p (Pi.single j 1)).det ∈ I := by
  set m' := m.updateRow p (Pi.single i 1) with hm'
  have h1 : m'.adjugate.mulVec (m'.mulVec x) = m'.det • x := by
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
  have h2 : ∑ q, m'.adjugate j q * m'.mulVec x q = m'.det * x j := by
    have := congrFun h1 j
    simpa [Matrix.mulVec, dotProduct] using this
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p)] at h2
  have h3 : m'.adjugate j p = (m.updateRow p (Pi.single j 1)).det := by
    rw [Matrix.adjugate_apply, hm', Matrix.updateRow_idem]
  have h4 : m'.mulVec x p = x i := by
    simp [hm', Matrix.mulVec]
  rw [h3, h4] at h2
  have h5 : ∑ q ∈ Finset.univ.erase p, m'.adjugate j q * m'.mulVec x q ∈ I := by
    refine I.sum_mem fun q hq => I.mul_mem_left _ ?_
    have hq' : q ≠ p := Finset.ne_of_mem_erase hq
    have : m'.mulVec x q = m.mulVec x q := by
      simp [hm', Matrix.mulVec, Matrix.updateRow_ne hq']
    rw [this]
    exact hm q hq'
  convert h5 using 1
  linear_combination -h2

theorem det_updateRow_alternating_mulVec_mem {T : Type} [CommRing T] {g : ℕ} (x : Fin g → T)
    (I : Ideal T) (m : Matrix (Fin g) (Fin g) T) (p : Fin g)
    (hm : ∀ q, q ≠ p → m.mulVec x q ∈ I) (s : Matrix (Fin g) (Fin g) T)
    (hs : s.transpose = -s) (hd : ∀ i, s i i = 0) :
    (m.updateRow p (s.mulVec x)).det ∈ I := by
  have h1 : (m.updateRow p (s.mulVec x)).det
      = ∑ ij : Fin g × Fin g,
          s ij.1 ij.2 * (x ij.2 * (m.updateRow p (Pi.single ij.1 1)).det) := by
    have e : ∀ v : Fin g → T, (m.updateRow p v).det
        = ∑ i, v i * (m.updateRow p (Pi.single i 1)).det := by
      intro v
      have := Matrix.cramer_transpose_apply m v p
      rw [← this, Matrix.cramer_eq_adjugate_mulVec]
      simp only [Matrix.mulVec, dotProduct]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Matrix.adjugate_transpose, Matrix.transpose_apply, Matrix.adjugate_apply, mul_comm]
    rw [e, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, mul_assoc]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h1, ← Ideal.Quotient.eq_zero_iff_mem, map_sum]
  refine Finset.sum_ninvolution Prod.swap ?_ ?_ (fun _ => Finset.mem_univ _) Prod.swap_swap
  · rintro ⟨i, j⟩
    rw [← map_add (f := _), Ideal.Quotient.eq_zero_iff_mem]
    have hji : s j i = - s i j := by
      have := congrFun (congrFun hs i) j
      simpa using this
    have := I.mul_mem_left (s i j) (det_updateRow_single_mul_sub_mem x I m p hm i j)
    convert this using 1
    simp only [Prod.fst_swap, Prod.snd_swap, hji]
    ring
  · rintro ⟨i, j⟩ h e
    apply h
    have : j = i := congrArg Prod.fst e
    subst this
    simp [hd]

theorem det_sub_det_mem_span_of_mulVec_eq :
    ∀ (T : Type) [CommRing T] (g : ℕ) (x : Fin g → T), (∀ r : Fin g → _, ∑ i, r i * x i = 0 → ∃ s : Matrix (Fin g) (Fin g) _, s.transpose = -s ∧ (∀ i, s i i = 0) ∧ r = s.mulVec x) → ∀ c c' : Matrix (Fin g) (Fin g) T, c.mulVec x = c'.mulVec x → c.det - c'.det ∈ Ideal.span (Set.range (c.mulVec x)) := by
  intro T _ g x hx c c' hc
  set I := Ideal.span (Set.range (c.mulVec x)) with hI
  let M : Finset (Fin g) → Matrix (Fin g) (Fin g) T :=
    fun S => Matrix.of fun i => if i ∈ S then c' i else c i
  have hM : ∀ S q, (M S).mulVec x q = c.mulVec x q := by
    intro S q
    by_cases h : q ∈ S
    · rw [hc]; simp [M, Matrix.mulVec, h]
    · simp [M, Matrix.mulVec, h]
  have key : ∀ S : Finset (Fin g), c.det - (M S).det ∈ I := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      have : M ∅ = c := by ext i j; simp [M]
      simp [this]
    | insert p S hp ih =>
      obtain ⟨s, hs, hd, hr⟩ := hx (c p - c' p) (by
        have := congrFun hc p
        simp only [Matrix.mulVec, dotProduct] at this
        simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
        exact sub_eq_zero.mpr this)
      have h1 := det_updateRow_alternating_mulVec_mem x I (M S) p
        (fun q _ => by rw [hM]; exact Ideal.subset_span ⟨q, rfl⟩) s hs hd
      rw [← hr] at h1
      have e1 : (M S).updateRow p (c' p) = M (insert p S) := by
        ext i j
        by_cases h : i = p
        · subst h; simp [M]
        · simp [M, Matrix.updateRow_ne h, h]
      have e2 : (M S).updateRow p (c p) = M S := by
        ext i j
        by_cases h : i = p
        · subst h; simp [M, hp]
        · simp [Matrix.updateRow_ne h]
      have e3 := Matrix.det_updateRow_add (M S) p (c p - c' p) (c' p)
      rw [sub_add_cancel, e1, e2] at e3
      have := I.add_mem ih h1
      convert this using 1
      linear_combination e3
  have := key Finset.univ
  have e : M Finset.univ = c' := by ext i j; simp [M]
  rwa [e] at this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.MvPowerSeriesVariablesSyzygySocle
open scoped TensorProduct

namespace GlobalTheory

open MvPowerSeries Finsupp in
theorem coeff_mul_X_ite {k : Type} [CommRing k] {g : ℕ} (f : MvPowerSeries (Fin g) k)
    (j : Fin g) (m : Fin g →₀ ℕ) :
    coeff m (f * X j) = if m j ≠ 0 then coeff (m - single j 1) f else 0 := by
  classical
  rw [X_def, coeff_mul_monomial, mul_one]
  congr 1
  simp [Finsupp.single_le_iff, Nat.one_le_iff_ne_zero]

open MvPowerSeries Finsupp in
theorem mvPowerSeries_X_syzygy {k : Type} [CommRing k] {g : ℕ}
    (r : Fin g → MvPowerSeries (Fin g) k) (hr : ∑ i, r i * X i = 0) :
    ∃ s : Matrix (Fin g) (Fin g) (MvPowerSeries (Fin g) k), s.transpose = -s ∧ (∀ i, s i i = 0) ∧
      r = s.mulVec (fun i => X i) := by
  classical
  let t : Matrix (Fin g) (Fin g) (MvPowerSeries (Fin g) k) := fun i j n =>
    if j < i ∧ ∀ l < j, n l = 0 then coeff (n + single j 1) (r i) else 0
  have ht : ∀ i j n, coeff n (t i j) =
      if j < i ∧ ∀ l < j, n l = 0 then coeff (n + single j 1) (r i) else 0 := fun _ _ _ => rfl
  refine ⟨t - t.transpose, by simp [Matrix.transpose_sub], fun i => by simp, ?_⟩
  funext i
  ext m
  have h1 : ∀ j, coeff m (t i j * X j) =
      if m j ≠ 0 ∧ j < i ∧ ∀ l < j, m l = 0 then coeff m (r i) else 0 := by
    intro j
    rw [coeff_mul_X_ite, ht]
    by_cases hj : m j = 0
    · simp [hj]
    · have e : m - single j 1 + single j 1 = m :=
        tsub_add_cancel_of_le (by simpa [Finsupp.single_le_iff, Nat.one_le_iff_ne_zero] using hj)
      have e2 : (∀ l < j, (m - single j 1 : Fin g →₀ ℕ) l = 0) ↔ ∀ l < j, m l = 0 := by
        refine forall_congr' fun l => forall_congr' fun hl => ?_
        simp [Finsupp.single_apply, hl.ne']
      simp only [e, e2, hj, ne_eq, not_false_eq_true, if_true, true_and]
  have h2 : ∀ j, coeff m (t j i * X j) =
      if (∀ l < i, m l = 0) ∧ j ≠ i then coeff (m + single i 1) (r j * X j) else 0 := by
    intro j
    rw [coeff_mul_X_ite, ht, coeff_mul_X_ite]
    by_cases hji : j = i
    · simp [hji]
    have e0 : (m + single i 1 : Fin g →₀ ℕ) j = m j := by
      simp [Finsupp.single_apply, Ne.symm hji]
    rw [e0]
    by_cases hj : m j = 0
    · simp [hj]
    have e : m - single j 1 + single i 1 = m + single i 1 - single j 1 :=
      tsub_add_eq_add_tsub (by simpa [Finsupp.single_le_iff, Nat.one_le_iff_ne_zero] using hj)
    rw [e]
    rcases lt_or_gt_of_ne hji with h | h
    · have : ¬ ∀ l < i, m l = 0 := fun H => hj (H j h)
      simp [this, h.not_gt]
    · have e2 : (∀ l < i, (m - single j 1 : Fin g →₀ ℕ) l = 0) ↔ ∀ l < i, m l = 0 := by
        refine forall_congr' fun l => forall_congr' fun hl => ?_
        simp [Finsupp.single_apply, (hl.trans h).ne']
      simp only [e2, hj, h, hji, ne_eq, not_false_eq_true, if_true, true_and, and_true]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, Matrix.sub_apply, Matrix.transpose_apply, sub_mul,
    map_sum, map_sub, h1, h2, Finset.sum_sub_distrib]
  by_cases hi : ∀ l < i, m l = 0
  · rw [Finset.sum_eq_zero (fun j _ => if_neg (fun H => H.1 (hi j H.2.1)))]
    have h3 := congrArg (coeff (m + single i 1)) hr
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_zero, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), coeff_mul_X_ite] at h3
    simp only [iff_true_intro hi, true_and]
    rw [← Finset.sum_filter, Finset.filter_ne']
    simp only [Finsupp.add_apply, single_eq_same, add_tsub_cancel_right] at h3
    rw [if_pos (by omega)] at h3
    linear_combination h3
  · simp only [hi, false_and, if_false, Finset.sum_const_zero, sub_zero]
    push_neg at hi
    obtain ⟨l, hl, hml⟩ := hi
    obtain ⟨j, hj, hmin⟩ := WellFounded.has_min (wellFounded_lt (α := Fin g)) {j | m j ≠ 0} ⟨l, hml⟩
    have hj0 : ∀ a < j, m a = 0 := fun a ha => by
      by_contra h; exact hmin a h ha
    rw [Finset.sum_eq_single j]
    · rw [if_pos ⟨hj, lt_of_le_of_lt (not_lt.1 (hmin l hml)) hl, hj0⟩]
    · intro b _ hb
      refine if_neg fun H => ?_
      rcases lt_or_gt_of_ne hb with h | h
      · exact H.1 (hj0 b h)
      · exact hj (H.2.2 j h)
    · simp

open MvPowerSeries Finsupp in
theorem mvPowerSeries_prod_X_pow_notMem {k : Type} [CommRing k] [Nontrivial k] {g : ℕ} (N : ℕ) :
    ∏ i, (X i : MvPowerSeries (Fin g) k) ^ N ∉
      Ideal.span (Set.range fun i => (X i : MvPowerSeries (Fin g) k) ^ (N + 1)) := by
  classical
  intro h
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.1 h
  have hp : ∀ s : Finset (Fin g), ∏ i ∈ s, (X i : MvPowerSeries (Fin g) k) ^ N =
      monomial (∑ i ∈ s, single i N) 1 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, X_pow_eq, monomial_mul_monomial, one_mul]
  have := congrArg (coeff (∑ i : Fin g, single i N)) hc
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hp, coeff_monomial_same, map_sum, Finset.sum_eq_zero] at this
  · exact zero_ne_one this
  · intro i _
    refine X_pow_dvd_iff.1 (dvd_mul_left _ _) _ ?_
    simp [Finsupp.finsetSum_apply, Finsupp.single_apply]

theorem mvPowerSeries_variables_syzygy_socle :
    ∀ (k : Type) [Field k] (g : ℕ) (x : Fin g → MvPowerSeries (Fin g) k), (∀ i, x i = MvPowerSeries.X i) → (∀ r : Fin g → _, ∑ i, r i * x i = 0 → ∃ s : Matrix (Fin g) (Fin g) _, s.transpose = -s ∧ (∀ i, s i i = 0) ∧ r = s.mulVec x) ∧ ∀ N : ℕ, ∏ i, x i ^ N ∉ Ideal.span (Set.range fun i => x i ^ (N + 1)) := by
  intro k _ g x hx
  obtain rfl : x = fun i => MvPowerSeries.X i := funext hx
  exact ⟨fun r hr => mvPowerSeries_X_syzygy r hr, fun N => mvPowerSeries_prod_X_pow_notMem N⟩

end GlobalTheory
end

open scoped TensorProduct

namespace GlobalTheory

theorem det_notMem_span_mulVec_of_socle {T : Type} [CommRing T] {g N : ℕ} (x : Fin g → T)
    (hsyz : ∀ r : Fin g → T, ∑ i, r i * x i = 0 → ∃ s : Matrix (Fin g) (Fin g) T,
      s.transpose = -s ∧ (∀ i, s i i = 0) ∧ r = s.mulVec x)
    (hsoc : ∏ i, x i ^ N ∉ Ideal.span (Set.range fun i => x i ^ (N + 1)))
    (a : Matrix (Fin g) (Fin g) T)
    (h : ∀ i, x i ^ (N + 1) ∈ Ideal.span (Set.range (a.mulVec x))) :
    a.det ∉ Ideal.span (Set.range (a.mulVec x)) := by
  intro hdet
  have h' : ∀ i, ∃ c : Fin g → T, ∑ j, c j * a.mulVec x j = x i ^ (N + 1) := fun i =>
    Ideal.mem_span_range_iff_exists_fun.mp (h i)
  choose b hb using h'
  let B : Matrix (Fin g) (Fin g) T := Matrix.of b
  have hB : B.mulVec (a.mulVec x) = fun i => x i ^ (N + 1) := by
    funext i
    exact hb i
  set J : Ideal T := Ideal.span (Set.range fun i => x i ^ (N + 1)) with hJ
  have hf : ∀ i, B.det * a.mulVec x i ∈ J := by
    intro i
    have e : B.adjugate.mulVec (B.mulVec (a.mulVec x)) = B.det • a.mulVec x := by
      rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
    have e' := congrFun e i
    rw [hB, Pi.smul_apply, smul_eq_mul] at e'
    rw [← e']
    exact Ideal.mem_span_range_iff_exists_fun.mpr ⟨fun j => B.adjugate i j, rfl⟩
  have hBa : (B * a).det ∈ J := by
    obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hdet
    rw [Matrix.det_mul, ← hc, Finset.mul_sum]
    refine Ideal.sum_mem _ fun j _ => ?_
    rw [mul_left_comm]
    exact Ideal.mul_mem_left _ _ (hf j)
  have hBx : (B * a).mulVec x = fun i => x i ^ (N + 1) := by
    rw [← Matrix.mulVec_mulVec, hB]
  have hD : (Matrix.diagonal fun i => x i ^ N).mulVec x = fun i => x i ^ (N + 1) := by
    funext i
    rw [Matrix.mulVec_diagonal, pow_succ]
  have key := GlobalTheory.det_sub_det_mem_span_of_mulVec_eq T g x hsyz (B * a)
    (Matrix.diagonal fun i => x i ^ N) (hBx.trans hD.symm)
  rw [hBx, Matrix.det_diagonal] at key
  have := J.sub_mem hBa key
  rw [sub_sub_cancel] at this
  exact hsoc this

theorem det_notMem_span_mulVec_X : ∀ (k : Type) [Field k] (g N : ℕ) (a : Matrix (Fin g) (Fin g) (MvPowerSeries (Fin g) k)), (∀ i, (MvPowerSeries.X i : MvPowerSeries (Fin g) k) ^ N ∈ Ideal.span (Set.range (a.mulVec MvPowerSeries.X))) → a.det ∉ Ideal.span (Set.range (a.mulVec MvPowerSeries.X)) := by
  intro k _ g N a h
  obtain ⟨hsyz, hsoc⟩ := GlobalTheory.mvPowerSeries_variables_syzygy_socle k g MvPowerSeries.X (fun _ => rfl)
  refine det_notMem_span_mulVec_of_socle MvPowerSeries.X hsyz (hsoc N) a fun i => ?_
  rw [pow_succ]
  exact Ideal.mul_mem_right _ _ (h i)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIntegralOfLocalPresentationPow
open scoped TensorProduct

namespace GlobalTheory

theorem exists_pow_mul_one_sub_mem_map_maximalIdeal (O H : Type) [CommRing O] [IsLocalRing O]
    [CommRing H] [Algebra O H] [Module.Finite O H] (u : H) :
    ∃ (N : ℕ) (y : H), u ^ N * (1 - y * u) ∈ (IsLocalRing.maximalIdeal O).map (algebraMap O H) := by
  set m := IsLocalRing.maximalIdeal O
  set J := m.map (algebraMap O H)
  letI : Field (O ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite (O ⧸ m) (H ⧸ J) := Module.Finite.of_restrictScalars_finite O _ _
  haveI : IsArtinianRing (H ⧸ J) := IsArtinianRing.of_finite (O ⧸ m) _
  obtain ⟨N, y, hy⟩ := IsArtinian.exists_pow_succ_smul_dvd (R := H ⧸ J) (M := H ⧸ J)
    (Ideal.Quotient.mk J u) 1
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨N, y, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  simp only [smul_eq_mul, mul_one, Nat.succ_eq_add_one, pow_succ] at hy
  simp only [map_mul, map_pow, map_sub, map_one]
  linear_combination -hy

theorem exists_mul_kills_ker_of_localization (O H : Type) [CommRing O] [CommRing H] [Algebra O H]
    [Module.Finite O H] (ε : H →ₐ[O] O) (M : Submonoid H) (T : Type) [CommRing T] [Algebra H T]
    [IsLocalization M T] (u : H) (hu : ∀ h, ε h = 0 → algebraMap H T (h * u) = 0) :
    ∃ s : M, ∀ h, ε h = 0 → h * (s * u) = 0 := by
  classical
  obtain ⟨G, hG⟩ := Module.Finite.fg_top (R := O) (M := H)
  have h1 : ∀ b : H, ∃ s : M, (s : H) * ((b - algebraMap O H (ε b)) * u) = 0 := fun b =>
    (IsLocalization.map_eq_zero_iff M T _).1 (hu _ (by simp))
  choose s hs using h1
  refine ⟨∏ b ∈ G, s b, fun h hh => ?_⟩
  have key : ∀ h : H, (h - algebraMap O H (ε h)) * (((∏ b ∈ G, s b : M) : H) * u) = 0 := by
    intro h
    have hmem : h ∈ Submodule.span O (G : Set H) := by rw [hG]; trivial
    induction hmem using Submodule.span_induction with
    | mem b hb =>
      rw [← Finset.mul_prod_erase G s hb, Submonoid.coe_mul]
      linear_combination ((∏ x ∈ G.erase b, s x : M) : H) * hs b
    | zero => simp
    | add a b _ _ ha hb =>
      rw [map_add (f := _), map_add (f := _)]
      linear_combination ha + hb
    | smul c a _ ha =>
      rw [map_smul, smul_eq_mul, map_mul, Algebra.smul_def]
      linear_combination algebraMap O H c * ha
  simpa [hh] using key h

theorem exists_integral_of_local_presentation :
    ∀ (O H : Type) [CommRing O] [IsLocalRing O] [CommRing H] [Algebra O H] [Module.Finite O H] (ε : H →ₐ[O] O) (g n : ℕ) (T : Type) [CommRing T] [Algebra H T] [Algebra O T] [IsScalarTower O H T] [IsLocalization.AtPrime T ((IsLocalRing.maximalIdeal O).comap ε)] (εT : T →ₐ[O] O), (∀ h, εT (algebraMap H T h) = ε h) → ∀ (S : Type) [CommRing S] [Algebra O S] (π : S →ₐ[O] T) (x : Fin g → S) (a : Matrix (Fin g) (Fin g) S) (ρ : S →+* MvPowerSeries (Fin g) (IsLocalRing.ResidueField O)), Function.Surjective π → RingHom.ker π = Ideal.span (Set.range (a.mulVec x)) → RingHom.ker εT = Ideal.span (Set.range fun i => π (x i)) → (∀ i j, εT (π (a i j)) = if i = j then (n : O) else 0) → (∀ i, ρ (x i) = MvPowerSeries.X i) → (∀ c ∈ IsLocalRing.maximalIdeal O, ρ (algebraMap O S c) = 0) → ∃ l : H, (∀ h, ε h = 0 → h * l = 0) ∧ (n : O) ^ g ∣ ε l ∧ l ∉ (IsLocalRing.maximalIdeal O).map (algebraMap O H) := by
  intro O H _ _ _ _ _ ε g n T _ _ _ _ _ εT hε S _ _ π x a ρ hπ hker hkerT ha hρx hρm
  classical
  set m := IsLocalRing.maximalIdeal O with hm
  set p : Ideal H := m.comap ε with hp
  have hmT : (m.map (algebraMap O H)).map (algebraMap H T) = m.map (algebraMap O T) := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  have hmS : (m.map (algebraMap O S)).map (π : S →+* T) = m.map (algebraMap O T) := by
    rw [Ideal.map_map, AlgHom.comp_algebraMap]
  set A : Matrix (Fin g) (Fin g) (MvPowerSeries (Fin g) (IsLocalRing.ResidueField O)) :=
    ρ.mapMatrix a with hA
  have hred : ∀ z : S, π z ∈ m.map (algebraMap O T) →
      ρ z ∈ Ideal.span (Set.range (A.mulVec MvPowerSeries.X)) := by
    intro z hz
    rw [← hmS] at hz
    have hz' : z ∈ m.map (algebraMap O S) ⊔ RingHom.ker π := by
      have := Ideal.comap_map_of_surjective (π : S →+* T) hπ (m.map (algebraMap O S))
      have h2 : z ∈ ((m.map (algebraMap O S)).map (π : S →+* T)).comap (π : S →+* T) := hz
      rw [this] at h2
      exact h2
    have hle : m.map (algebraMap O S) ⊔ RingHom.ker π ≤
        (Ideal.span (Set.range (A.mulVec MvPowerSeries.X))).comap ρ := by
      refine sup_le ?_ ?_
      · rw [Ideal.map_le_iff_le_comap]
        intro c hc
        simp only [Ideal.mem_comap, hρm c hc, zero_mem]
      · rw [hker, Ideal.span_le]
        rintro _ ⟨i, rfl⟩
        refine Ideal.subset_span ⟨i, ?_⟩
        simp [hA, Matrix.mulVec, dotProduct, hρx]
    exact hle hz'
  have hx0 : ∀ i, εT (π (x i)) = 0 := fun i => by
    have : π (x i) ∈ RingHom.ker εT := by rw [hkerT]; exact Ideal.subset_span ⟨i, rfl⟩
    exact this
  have hnil : ∀ i, ∃ N : ℕ, π (x i) ^ N ∈ m.map (algebraMap O T) := by
    intro i
    obtain ⟨⟨u, t⟩, hut⟩ := IsLocalization.surj p.primeCompl (π (x i))
    have hu : ε u = 0 := by
      have := congrArg εT hut
      rw [map_mul, hx0, zero_mul, hε] at this
      exact this.symm
    obtain ⟨N, y, hy⟩ := exists_pow_mul_one_sub_mem_map_maximalIdeal O H u
    have hy' := Ideal.mem_map_of_mem (algebraMap H T) hy
    rw [hmT, map_mul, map_pow] at hy'
    have hunit : IsUnit (algebraMap H T (1 - y * u)) := by
      refine IsLocalization.map_units T (⟨1 - y * u, ?_⟩ : p.primeCompl)
      intro hc
      have hc' : ε (1 - y * u) ∈ m := hc
      rw [map_sub, map_mul, hu, mul_zero, sub_zero, map_one] at hc'
      exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 hc')
    rw [Ideal.mul_unit_mem_iff_mem _ hunit] at hy'
    simp only at hut
    rw [← hut, mul_pow,
      Ideal.mul_unit_mem_iff_mem _ ((IsLocalization.map_units T t).pow N)] at hy'
    exact ⟨N, hy'⟩
  choose N hN using hnil
  have hdet : π a.det ∉ m.map (algebraMap O T) := by
    intro hc
    refine det_notMem_span_mulVec_X _ g (Finset.univ.sup N) A (fun i => ?_) ?_
    · rw [← hρx, ← map_pow]
      apply hred
      rw [map_pow]
      exact Ideal.pow_mem_of_pow_mem _ (hN i) (Finset.le_sup (Finset.mem_univ i))
    · rw [hA, ← RingHom.map_det]
      exact hred _ hc
  have hkill : ∀ w : T, εT w = 0 → w * π a.det = 0 := by
    intro w hw
    have hw' : w ∈ RingHom.ker εT := hw
    rw [hkerT] at hw'
    have hle : Ideal.span (Set.range fun i => π (x i)) ≤
        LinearMap.ker (LinearMap.mulRight T (π a.det)) := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      change π (x i) * π a.det = 0
      rw [← map_mul]
      change x i * a.det ∈ RingHom.ker π
      have h1 : x i * a.det = (a.adjugate.mulVec (a.mulVec x)) i := by
        rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
        simp [mul_comm]
      rw [h1, hker]
      change ∑ j, a.adjugate i j * a.mulVec x j ∈ _
      exact Ideal.sum_mem _ fun j _ =>
        Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self j))
    exact hle hw'
  have hval : εT (π a.det) = (n : O) ^ g := by
    have h1 : εT (π a.det) = ((εT.comp π).mapMatrix a).det := by
      rw [← AlgHom.map_det]; rfl
    have h2 : (εT.comp π).mapMatrix a = Matrix.diagonal fun _ => (n : O) := by
      ext i j
      simp [Matrix.diagonal_apply, ha]
    rw [h1, h2, Matrix.det_diagonal]
    simp
  obtain ⟨⟨u, t⟩, hut⟩ := IsLocalization.surj p.primeCompl (π a.det)
  simp only at hut
  obtain ⟨s, hs⟩ := exists_mul_kills_ker_of_localization O H ε p.primeCompl T u (fun h hh => by
    rw [map_mul, ← hut, ← mul_assoc, hkill _ (by rw [hε, hh]), zero_mul])
  refine ⟨s * u, hs, ?_, fun hc => hdet ?_⟩
  · have := congrArg εT hut
    rw [map_mul, hval, hε, hε] at this
    rw [map_mul, ← this]
    exact Dvd.dvd.mul_left (dvd_mul_right _ _) _
  · have hc' := Ideal.mem_map_of_mem (algebraMap H T) hc
    rw [hmT, map_mul, Ideal.unit_mul_mem_iff_mem _ (IsLocalization.map_units T s), ← hut,
      Ideal.mul_unit_mem_iff_mem _ (IsLocalization.map_units T t)] at hc'
    exact hc'

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIntegralOfLocalPresentationPowStatement
open scoped TensorProduct
theorem _root_.GlobalTheory.T.exists_integral_of_local_presentation_pow : ∀ (O H : Type) [CommRing O] [IsLocalRing O] [CommRing H] [Algebra O H] [Module.Finite O H] (ε : H →ₐ[O] O) (g n : ℕ) (T : Type) [CommRing T] [Algebra H T] [Algebra O T] [IsScalarTower O H T] [IsLocalization.AtPrime T ((IsLocalRing.maximalIdeal O).comap ε)] (εT : T →ₐ[O] O), (∀ h, εT (algebraMap H T h) = ε h) → ∀ (S : Type) [CommRing S] [Algebra O S] (π : S →ₐ[O] T) (x : Fin g → S) (a : Matrix (Fin g) (Fin g) S) (ρ : S →+* MvPowerSeries (Fin g) (IsLocalRing.ResidueField O)), Function.Surjective π → RingHom.ker π = Ideal.span (Set.range (a.mulVec x)) → RingHom.ker εT = Ideal.span (Set.range fun i => π (x i)) → (∀ i j, εT (π (a i j)) = if i = j then (n : O) else 0) → (∀ i, ρ (x i) = MvPowerSeries.X i) → (∀ c ∈ IsLocalRing.maximalIdeal O, ρ (algebraMap O S c) = 0) → ∃ l : H, (∀ h, ε h = 0 → h * l = 0) ∧ (n : O) ^ g ∣ ε l ∧ l ∉ (IsLocalRing.maximalIdeal O).map (algebraMap O H) := by
  first | exact @GlobalTheory.exists_integral_of_local_presentation | exact GlobalTheory.exists_integral_of_local_presentation | (intros; apply GlobalTheory.exists_integral_of_local_presentation <;> assumption)
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem exists_algHom_localization_augmentation (O : Type) [CommRing O] [IsLocalRing O]
    (H : Type) [CommRing H] [Algebra O H] (ε : H →ₐ[O] O) :
    ∃ εT : Localization.AtPrime ((IsLocalRing.maximalIdeal O).comap ε) →ₐ[O] O,
      ∀ h, εT (algebraMap H _ h) = ε h := by

  have hunit : ∀ s : ((IsLocalRing.maximalIdeal O).comap ε).primeCompl, IsUnit (ε s) := by
    intro s
    by_contra hs
    apply s.2
    show ε s ∈ IsLocalRing.maximalIdeal O
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact hs
  refine ⟨IsLocalization.liftAlgHom (M := ((IsLocalRing.maximalIdeal O).comap ε).primeCompl)
    (S := Localization.AtPrime ((IsLocalRing.maximalIdeal O).comap ε)) hunit, fun h => ?_⟩
  rw [IsLocalization.liftAlgHom_apply]
  exact IsLocalization.lift_eq hunit h

theorem pow_dvd_trace_torsion :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (G : Over (Sp O)) [GrpObj G] [IsCommMonObj G] (n : ℕ) (H : Type) [CommRing H] [Algebra O H] [Module.Finite O H] [Module.Free O H] (y : specO O H ⟶ G) (g : ℕ), SmoothOfRelativeDimension g G.hom → y ^ n = 1 → (∀ (S : Type) [CommRing S] [Algebra O S] (z : specO O S ⟶ G), z ^ n = 1 → ∃! φ : H →ₐ[O] S, ptMap φ ≫ y = z) → ∀ h : H, (n : O) ^ g ∣ Algebra.trace O H h := by
  intro O _ _ G _ _ n H _ _ _ _ y g hsm hy huniv h

  obtain ⟨ε, hε, -⟩ := huniv O 1 (one_pow n)
  obtain ⟨εT, hεT⟩ := exists_algHom_localization_augmentation O H ε

  obtain ⟨S, _, _, π, x, a, ρ, hπ, hker, hkerε, ha, hρ, hρm⟩ :=
    GlobalTheory.T.torsion_local_presentation_smooth_group O G n H y g hsm hy huniv ε hε
      (Localization.AtPrime ((IsLocalRing.maximalIdeal O).comap ε)) εT hεT

  obtain ⟨l, hl, hdvd, hlm⟩ :=
    GlobalTheory.T.exists_integral_of_local_presentation_pow O H ε g n (Localization.AtPrime ((IsLocalRing.maximalIdeal O).comap ε)) εT hεT
      S π x a ρ hπ hker hkerε ha hρ hρm

  obtain ⟨Θ, hΘ⟩ := GlobalTheory.T.exists_diagonal_element_lmul_eq_nonzero_geometric_points O G n H y hy huniv ε l (ε l) hε hl rfl hlm
  exact dvd_trans hdvd (GlobalTheory.T.dvd_trace_of_tensor_lmul_eq O H Θ (ε l) hΘ h)

end GlobalTheory
