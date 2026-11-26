module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEtaleOfIsEtaleCompletion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
public import Lean
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteOrderChartsMiddleSteps
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MatchTupleChartMemberChart
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorusCharacterRestrictionTraitSurjective

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicArcSmoothAlgebraNonvanishing
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicArcSmoothAlgebraNonvanishing
namespace GlobalTheory.HolArc

theorem isAlgebraic_of_etale (S R : Type) [CommRing S] [IsDomain S] [CommRing R] [IsDomain R]
    [Algebra S R] [Algebra.Etale S R] [FaithfulSMul S R] : Algebra.IsAlgebraic S R := by
  let K := FractionRing S
  let L := FractionRing R
  letI : Algebra K L := FractionRing.liftAlgebra S L
  haveI : IsScalarTower S K L := FractionRing.isScalarTower_liftAlgebra S L
  haveI : Algebra.FormallyEtale R L := .of_isLocalization (nonZeroDivisors _)
  haveI : Algebra.FormallyUnramified S L := Algebra.FormallyUnramified.comp S R L
  haveI : Algebra.FormallyUnramified K L := Algebra.FormallyUnramified.of_restrictScalars S K L
  haveI : Algebra.EssFiniteType R L := .of_isLocalization L (nonZeroDivisors _)
  haveI : Algebra.EssFiniteType S L := Algebra.EssFiniteType.comp S R L
  haveI : Algebra.EssFiniteType K L := Algebra.EssFiniteType.of_comp S K L
  haveI : Algebra.IsSeparable K L := Algebra.FormallyUnramified.isSeparable K L
  haveI : Algebra.IsAlgebraic K L := inferInstance
  haveI : Algebra.IsAlgebraic S L := (IsFractionRing.comap_isAlgebraic_iff (A := S) (K := K)).2 inferInstance
  exact Algebra.IsAlgebraic.of_injective (IsScalarTower.toAlgHom S R L)
    (IsFractionRing.injective R L)

theorem faithfulSMul_of_flat (S R : Type) [CommRing S] [IsDomain S] [CommRing R] [IsDomain R]
    [Algebra S R] [Module.Flat S R] : FaithfulSMul S R := by
  rw [faithfulSMul_iff_algebraMap_injective, injective_iff_map_eq_zero]
  intro a ha
  by_contra h
  have hreg : IsSMulRegular R a :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero h)
  have : a • (1 : R) = a • (0 : R) := by simp [Algebra.smul_def, ha]
  exact one_ne_zero (hreg this)

theorem exists_line (m : ℕ) (q : MvPolynomial (Fin m) ℂ) (hq : q ≠ 0) (b₀ : Fin m → ℂ) :
    ∃ (v : Fin m → ℂ) (ρ : ℝ), 0 < ρ ∧
      ∀ u ∈ Metric.ball (0 : ℂ) ρ, u ≠ 0 → MvPolynomial.eval (b₀ + u • v) q ≠ 0 := by
  obtain ⟨w, hw⟩ : ∃ w, MvPolynomial.eval w q ≠ 0 := by
    by_contra h
    push_neg at h
    exact hq (MvPolynomial.funext fun x => by simpa using h x)
  let v := w - b₀
  let Q : Polynomial ℂ := MvPolynomial.aeval
    (fun i => Polynomial.C (b₀ i) + Polynomial.X * Polynomial.C (v i)) q
  have hQ : ∀ u, Q.eval u = MvPolynomial.eval (b₀ + u • v) q := fun u => by
    have : (Polynomial.evalRingHom u).comp
        (MvPolynomial.aeval (R := ℂ) (fun i => Polynomial.C (b₀ i) + Polynomial.X * Polynomial.C (v i)) :
          MvPolynomial (Fin m) ℂ →ₐ[ℂ] Polynomial ℂ).toRingHom =
        MvPolynomial.eval (b₀ + u • v) := by
      refine MvPolynomial.ringHom_ext (fun a => ?_) fun i => ?_ <;> simp <;> ring
    exact congrArg (fun f : MvPolynomial (Fin m) ℂ →+* ℂ => f q) this
  have hQ0 : Q ≠ 0 := fun h => hw (by
    have := hQ 1
    simpa [h, v] using this.symm)
  have hfin : (((Q.roots.toFinset.erase 0 : Finset ℂ) : Set ℂ))ᶜ ∈ nhds (0 : ℂ) :=
    (Finset.finite_toSet _).isClosed.isOpen_compl.mem_nhds (by simp)
  obtain ⟨ρ, hρ, hb⟩ := Metric.mem_nhds_iff.1 hfin
  refine ⟨v, ρ, hρ, fun u hu hu0 h => hb hu ?_⟩
  simp only [Finset.coe_erase, Set.mem_diff, Finset.mem_coe, Multiset.mem_toFinset,
    Set.mem_singleton_iff, Polynomial.mem_roots hQ0, Polynomial.IsRoot.def, hQ, h]
  simpa using hu0

end GlobalTheory.HolArc

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

namespace GlobalTheory.HolArc

theorem exists_holPts_ne_zero : ∀ (F A : Type) [Field F] [CommRing A] [IsDomain A] [Algebra F A], Algebra.Smooth F A → ∀ (ψ₀ : A →+* ℂ) (p : A), p ≠ 0 → ∃ (ψ : ℂ → (A →+* ℂ)) (r : ℝ), IsHolPts ψ r ∧ ψ 0 = ψ₀ ∧ (∀ u ∈ Metric.ball (0 : ℂ) r, (ψ u).comp (algebraMap F A) = ψ₀.comp (algebraMap F A)) ∧ ∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → ψ u p ≠ 0 := by
  intro F A _ _ _ _ hS ψ₀ p hp
  haveI := hS
  haveI : (RingHom.ker ψ₀).IsPrime := RingHom.ker_isPrime ψ₀
  obtain ⟨g, m, s, hg, het⟩ := SmoothPointFamily.exists_etale_away (R := F) (RingHom.ker ψ₀)
  have hg₀ : ψ₀ g ≠ 0 := hg
  have hgne : g ≠ 0 := fun h => hg₀ (by simp [h])
  let σ : F →+* ℂ := ψ₀.comp (algebraMap F A)
  let R := Localization.Away g
  let ι : A →+* R := algebraMap A R
  have hle : Submonoid.powers g ≤ nonZeroDivisors A :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hgne
  haveI : IsDomain R := IsLocalization.isDomain_localization hle
  have hι : Function.Injective ι := IsLocalization.injective R hle
  let e : R →+* ℂ := IsLocalization.Away.lift g (g := ψ₀) (isUnit_iff_ne_zero.2 hg₀)
  have he : ∀ a, e (ι a) = ψ₀ a := fun a => IsLocalization.Away.lift_eq g _ a
  let P : MvPolynomial (Fin m) F →+* R := MvPolynomial.eval₂Hom (algebraMap F R) fun i => ι (s i)
  have hPC : ∀ k, P (MvPolynomial.C k) = ι (algebraMap F A k) := fun k => by
    simp only [P, MvPolynomial.eval₂Hom_C]
    exact IsScalarTower.algebraMap_apply F A R k
  have hPX : ∀ i, P (MvPolynomial.X i) = ι (s i) := fun i => by simp [P]
  have heC : ∀ k, e (P (MvPolynomial.C k)) = σ k := fun k => by rw [hPC, he]; rfl

  obtain ⟨c, hc0, hc⟩ : ∃ c : MvPolynomial (Fin m) F, c ≠ 0 ∧ ι p ∣ P c := by
    letI : Algebra (MvPolynomial (Fin m) F) R := P.toAlgebra
    haveI : Algebra.Etale (MvPolynomial (Fin m) F) R := het
    haveI : FaithfulSMul (MvPolynomial (Fin m) F) R := faithfulSMul_of_flat _ _
    haveI := isAlgebraic_of_etale (MvPolynomial (Fin m) F) R
    exact (Algebra.IsAlgebraic.isAlgebraic (ι p)).exists_nonzero_dvd
      (mem_nonZeroDivisors_of_ne_zero ((map_ne_zero_iff ι hι).2 hp))
  obtain ⟨N, τ, n, f, O, hN, hO, hO₀, hd, hτ, hrec⟩ :=
    GlobalTheory.EtaleFamily.exists_holomorphic_sections 0 m F R P Set.univ (fun _ => σ) 0 e het
      isOpen_univ trivial (fun a => differentiableOn_const _) heC
  obtain ⟨h3, h4⟩ := hrec 0 e heC hO₀
  simp only [hPX, he] at h3 h4
  let b₀ : Fin m → ℂ := fun i => ψ₀ (s i)
  have hq0 : MvPolynomial.map σ c ≠ 0 :=
    (map_ne_zero_iff _ (MvPolynomial.map_injective σ σ.injective)).2 hc0
  obtain ⟨v, ρ, hρ, hline⟩ := exists_line m (MvPolynomial.map σ c) hq0 b₀
  let ℓ : ℂ → (Fin 0 → ℂ) × (Fin m → ℂ) := fun u => (0, b₀ + u • v)
  have hℓd : Differentiable ℂ ℓ :=
    (differentiable_const _).prodMk ((differentiable_const _).add (differentiable_id.smul_const v))
  have hℓ0 : ℓ 0 = (0, b₀) := by simp [ℓ]
  have hNo : ℓ ⁻¹' N ∈ 𝓝 (0 : ℂ) :=
    (hN.preimage hℓd.continuous).mem_nhds (by simpa only [Set.mem_preimage, hℓ0] using h3)
  obtain ⟨ρ', hρ', hb⟩ := Metric.mem_nhds_iff.1 hNo
  have hsub : ∀ u ∈ Metric.ball (0 : ℂ) (min ρ ρ'), ℓ u ∈ N := fun u hu =>
    hb (Metric.ball_subset_ball (min_le_right _ _) hu)
  refine ⟨fun u => (τ (ℓ u)).comp ι, min ρ ρ', ⟨lt_min hρ hρ', fun a => ?_⟩, ?_, fun u hu => ?_,
    fun u hu hu0 h => ?_⟩
  · exact (hd (ι a)).comp hℓd.differentiableOn hsub
  · refine RingHom.ext fun a => ?_
    simp only [RingHom.comp_apply, hℓ0]
    rw [show ((0 : Fin 0 → ℂ), b₀) = (0, fun i => ψ₀ (s i)) from rfl, h4, he]
  · refine RingHom.ext fun k => ?_
    simp only [RingHom.comp_apply]
    rw [← hPC]
    exact (hτ _ (hsub u hu)).2.1 k
  · have hev : (τ (ℓ u)).comp P = (MvPolynomial.eval (b₀ + u • v)).comp (MvPolynomial.map σ) := by
      refine MvPolynomial.ringHom_ext (fun k => ?_) fun i => ?_
      · simpa using (hτ _ (hsub u hu)).2.1 k
      · simpa [ℓ] using (hτ _ (hsub u hu)).2.2 i
    obtain ⟨d, hd'⟩ := hc
    have h0 : τ (ℓ u) (P c) = 0 := by
      rw [hd', map_mul]
      exact mul_eq_zero_of_left h _
    have h1 := congrArg (fun f : MvPolynomial (Fin m) F →+* ℂ => f c) hev
    simp only [RingHom.comp_apply] at h1
    exact hline u (Metric.ball_subset_ball (min_le_left _ _) hu) hu0 (h1.symm.trans h0)

end GlobalTheory.HolArc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicArcSmoothAlgebraNonvanishingStatement
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_holomorphic_arc_smooth_algebra_nonvanishing : ∀ (F A : Type) [Field F] [CommRing A] [IsDomain A] [Algebra F A], Algebra.Smooth F A → ∀ (ψ₀ : A →+* ℂ) (p : A), p ≠ 0 → ∃ (ψ : ℂ → (A →+* ℂ)) (r : ℝ), IsHolPts ψ r ∧ ψ 0 = ψ₀ ∧ (∀ u ∈ Metric.ball (0 : ℂ) r, (ψ u).comp (algebraMap F A) = ψ₀.comp (algebraMap F A)) ∧ ∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → ψ u p ≠ 0 := by
  first | exact @GlobalTheory.HolArc.exists_holPts_ne_zero | exact GlobalTheory.HolArc.exists_holPts_ne_zero | (intros; apply GlobalTheory.HolArc.exists_holPts_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.W1idxUnionW1jwFinite
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdxVanishOffFinite
noncomputable section

namespace GlobalTheory.Mem.IdxFin

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

theorem exists_unif {R V : Type} [CommRing R] [IsDomain R] [AddCommGroup V] [Module R V] (A B : Submodule R V)
    (hA : A.FG) (h : ∀ x ∈ A, ∃ s : R, s ≠ 0 ∧ s • x ∈ B) : ∃ s : R, s ≠ 0 ∧ ∀ x ∈ A, s • x ∈ B := by
  classical
  obtain ⟨S, rfl⟩ := hA
  choose! f hf using h
  refine ⟨∏ y ∈ S, f y, Finset.prod_ne_zero_iff.2 fun y hy => (hf y (Submodule.subset_span hy)).1, fun x hx => ?_⟩
  have : Submodule.span R (S : Set V) ≤ B.comap ((∏ y ∈ S, f y) • LinearMap.id) := by
    rw [Submodule.span_le]
    intro y hy
    show (∏ y ∈ S, f y) • y ∈ B
    rw [← Finset.prod_erase_mul S f hy, mul_smul]
    exact B.smul_mem _ (hf y (Submodule.subset_span hy)).2
  exact this hx

theorem locLen_finite {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module (𝓞 K) V]
    (A C : Submodule (𝓞 K) V) (hA : A.FG) :
    {w : HeightOneSpectrum (𝓞 K) | Formalism.HermitianLatticesTheory.locLen w.asIdeal A C ≠ 0}.Finite := by
  by_cases h : ∀ x ∈ A, ∃ s : 𝓞 K, s ≠ 0 ∧ s • x ∈ C
  · obtain ⟨s, hs, hC⟩ := exists_unif A C hA h
    have hf := Ideal.finite_factors (I := Ideal.span {s}) (by simpa using hs)
    refine hf.subset fun w hw => ?_
    by_contra hn
    have hsw : s ∉ w.asIdeal := fun h => hn (Ideal.dvd_span_singleton.2 h)
    have : (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal C).comap (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A).subtype = ⊤ := by
      rw [eq_top_iff]
      rintro ⟨x, t, ht, hx⟩ -
      exact ⟨s * t, Submonoid.mul_mem _ hsw ht, by rw [mul_smul]; exact hC _ hx⟩
    apply hw
    unfold Formalism.HermitianLatticesTheory.locLen
    rw [this]
    simp [Module.length_eq_zero]
  · push Not at h
    obtain ⟨x, hx, hxC⟩ := h
    refine Set.Finite.subset Set.finite_empty fun w hw => hw ?_
    unfold Formalism.HermitianLatticesTheory.locLen
    have hxA : x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A := ⟨1, Submonoid.one_mem _, by simpa using hx⟩
    let φ : 𝓞 K →ₗ[𝓞 K] ((Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A) ⧸
        (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal C).comap (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A).subtype) :=
      LinearMap.toSpanSingleton _ _ (Submodule.Quotient.mk ⟨x, hxA⟩)
    have hφ : Function.Injective φ := by
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro r hr
      by_contra hr0
      have h1 : Submodule.Quotient.mk (p := (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal C).comap (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A).subtype)
          (r • (⟨x, hxA⟩ : Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A)) = 0 := hr
      rw [Submodule.Quotient.mk_eq_zero] at h1
      obtain ⟨t, ht, h2⟩ := h1
      refine hxC (t * r) (mul_ne_zero (fun h0 => ht (h0 ▸ w.asIdeal.zero_mem)) hr0) ?_
      rw [mul_smul]
      exact h2
    have hle := Module.length_le_of_injective φ hφ
    have htop : Module.length (𝓞 K) (𝓞 K) = ⊤ := by
      by_contra hne
      have hfl := Module.length_ne_top_iff.1 hne
      have hart : IsArtinianRing (𝓞 K) := (isFiniteLength_iff_isNoetherian_isArtinian.1 hfl).2
      exact RingOfIntegers.not_isField K (IsArtinianRing.isField_of_isDomain _)
    rw [htop, top_le_iff] at hle
    rw [hle]
    rfl

theorem lidx_finite {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module (𝓞 K) V]
    (A B : Submodule (𝓞 K) V) (hA : A.FG) (hB : B.FG) :
    {w : HeightOneSpectrum (𝓞 K) | Formalism.HermitianLatticesTheory.lidx w.asIdeal A B ≠ 0}.Finite := by
  refine ((locLen_finite A (A ⊓ B) hA).union (locLen_finite B (A ⊓ B) hB)).subset fun w hw => ?_
  by_contra hn
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hn
  apply hw
  unfold Formalism.HermitianLatticesTheory.lidx
  rw [hn.1, hn.2]
  simp

end GlobalTheory.Mem.IdxFin

end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.NonzeroPlacesOverPrimes

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain

theorem conjPl_injective {K : Type} [Field K] [StarRing K] :
    Function.Injective (Formalism.DivisionValues.conjPl (K := K)) := by
  intro v w h
  have h1 : Ideal.map (Formalism.DivisionValues.cO K) v.asIdeal = Ideal.map (Formalism.DivisionValues.cO K) w.asIdeal :=
    congrArg HeightOneSpectrum.asIdeal h
  have hb : Function.Bijective (Formalism.DivisionValues.cO K) := (Formalism.DivisionValues.cO K).bijective
  have h2 := congrArg (Ideal.comap (Formalism.DivisionValues.cO K)) h1
  rw [Ideal.comap_map_of_bijective _ hb, Ideal.comap_map_of_bijective _ hb] at h2
  exact HeightOneSpectrum.ext h2

theorem dual_fg {K : Type} [Field K] [NumberField K] [StarRing K] {d : ℕ} (H : Matrix (Fin d) (Fin d) K)
    (hH : IsUnit H.det) (A : Submodule (𝓞 K) (Fin d → K)) (hA : Submodule.IsFullLattice K A) :
    (Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform H) A).FG := by
  classical
  obtain ⟨S, hS⟩ := hA.toIsLattice.fg
  have hSm : ∀ a ∈ S, a ∈ A := fun a ha => hS ▸ Submodule.subset_span ha
  have mem : ∀ x, x ∈ Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform H) A ↔
      ∀ y ∈ A, ∃ c : 𝓞 K, algebraMap (𝓞 K) K c = Formalism.DivisionValues.hform H y x := by
    intro x
    unfold Formalism.HermitianLatticesTheory.dual Formalism.E.hdual
    simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars, Submodule.mem_one]
  choose g hg using fun (x : Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform H) A) (a : S) => (mem x).1 x.2 a (hSm a a.2)
  have inj : Function.Injective (algebraMap (𝓞 K) K) := FaithfulSMul.algebraMap_injective (𝓞 K) K
  let φ : Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform H) A →ₗ[𝓞 K] (S → 𝓞 K) :=
    { toFun := g
      map_add' := fun x y => funext fun a => inj (by
        rw [hg, Submodule.coe_add, map_add (f := _), Pi.add_apply, map_add (f := _), hg, hg])
      map_smul' := fun s x => funext fun a => inj (by
        rw [hg, Submodule.coe_smul, ← algebraMap_smul K s (x : Fin d → K), map_smul]
        simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, map_mul, hg]) }
  have hφ : Function.Injective φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    have h0 : ∀ a ∈ S, Formalism.DivisionValues.hform H a x = 0 := by
      intro a ha
      rw [← hg x ⟨a, ha⟩, show g x ⟨a, ha⟩ = 0 from congrFun hx ⟨a, ha⟩, map_zero]
    have hL : ∀ a ∈ A, Formalism.DivisionValues.hform H a x = 0 := by
      intro a ha
      rw [← hS] at ha
      induction ha using Submodule.span_induction with
      | mem a ha => exact h0 a ha
      | zero => simp
      | add a b _ _ ha hb => rw [map_add (f := _), LinearMap.add_apply, ha, hb, add_zero]
      | smul s a _ ha => rw [← algebraMap_smul K s a, LinearMap.map_smulₛₗ, LinearMap.smul_apply, ha, smul_zero]
    have hV : ∀ a, Formalism.DivisionValues.hform H a x = 0 := by
      intro a
      have ha : a ∈ Submodule.span K (A : Set (Fin d → K)) := by rw [Submodule.IsFullLattice.span_eq_top (self := hA)]; trivial
      induction ha using Submodule.span_induction with
      | mem a ha => exact hL a ha
      | zero => simp
      | add a b _ _ ha hb => rw [map_add (f := _), LinearMap.add_apply, ha, hb, add_zero]
      | smul s a _ ha => rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, ha, smul_zero]
    have hM : Matrix.mulVec H (x : Fin d → K) = 0 := by
      funext i
      have := hV (Pi.single i 1)
      simpa [Formalism.DivisionValues.hform, Matrix.toLinearMapₛₗ₂'_apply, dotProduct, Matrix.mulVec, Pi.single_apply, mul_comm] using this
    exact Subtype.ext (Matrix.eq_zero_of_mulVec_eq_zero hH.ne_zero hM)
  exact Module.Finite.iff_fg.1 (Module.Finite.of_injective φ hφ)

end GlobalTheory.Mem.NonzeroPlacesOverPrimes

namespace GlobalTheory.Mem.NonzeroPlacesOverPrimes

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem jw_finite_of_lat {K : Type} [Field K] [NumberField K] [StarRing K] {d : ℕ} (H : Matrix (Fin d) (Fin d) K)
    (hH : IsUnit H.det) (A : Submodule (𝓞 K) (Fin d → K)) (hA : Submodule.IsFullLattice K A) :
    {w : HeightOneSpectrum (𝓞 K) | Formalism.DivisionValues.jw H w A ≠ 0}.Finite :=
  GlobalTheory.Mem.IdxFin.lidx_finite A _ hA.toIsLattice.fg (dual_fg H hH A hA)

theorem idx_finite_of_fg {K : Type} [Field K] [NumberField K] {d d' : ℕ} (M : Submodule (𝓞 K) (Fin d' → K))
    (θ : Matrix (Fin d') (Fin d) K) (L : Submodule (𝓞 K) (Fin d → K)) (hM : M.FG) (hL : L.FG) :
    {w : HeightOneSpectrum (𝓞 K) | Formalism.DivisionValues.idx w M (Formalism.DivisionValues.matLat θ L) ≠ 0}.Finite :=
  GlobalTheory.Mem.IdxFin.lidx_finite M _ hM (hL.map _)

end GlobalTheory.Mem.NonzeroPlacesOverPrimes

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymmetricPolyChernRoots
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymmetricPolyChernRoots
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BlockSymm

section Split

variable (R : Type) [CommRing R] {ι : Type} (m : ι → ℕ)

def chernRootsOver : MvPolynomial (ι × ℕ) R →ₐ[R] MvPolynomial (Root m) R :=
  aeval fun x => rename (Sigma.mk x.1) (esymm (Fin (m x.1)) R x.2)

variable {m} [DecidableEq ι] (τ₀ : ι)

def rootSplit : Root m ≃ Fin (m τ₀) ⊕ Root (fun τ : {τ // τ ≠ τ₀} => m τ.1) :=
  GlobalTheory.InnerAutomorphism.sigmaSplit (fun τ => Fin (m τ)) τ₀

def splitEquiv : MvPolynomial (Root m) R ≃ₐ[R]
    MvPolynomial (Fin (m τ₀)) (MvPolynomial (Root (fun τ : {τ // τ ≠ τ₀} => m τ.1)) R) :=
  (renameEquiv R (rootSplit τ₀)).trans (sumAlgEquiv R _ _)

theorem splitEquiv_X_self (i : Fin (m τ₀)) :
    splitEquiv R τ₀ (X (⟨τ₀, i⟩ : Root m)) = X i := by
  have e : rootSplit τ₀ (⟨τ₀, i⟩ : Root m) = Sum.inl i := GlobalTheory.InnerAutomorphism.sigmaSplit_self (fun τ => Fin (m τ)) τ₀ i
  simp [splitEquiv, e]

theorem splitEquiv_X_ne {τ : ι} (h : τ ≠ τ₀) (i : Fin (m τ)) :
    splitEquiv R τ₀ (X (⟨τ, i⟩ : Root m)) = C (X ⟨⟨τ, h⟩, i⟩) := by
  have e : rootSplit τ₀ (⟨τ, i⟩ : Root m) = Sum.inr ⟨⟨τ, h⟩, i⟩ := GlobalTheory.InnerAutomorphism.sigmaSplit_of_ne (fun τ => Fin (m τ)) h i
  simp [splitEquiv, e]

theorem splitEquiv_symm_X (i : Fin (m τ₀)) :
    (splitEquiv R τ₀).symm (X i) = X (⟨τ₀, i⟩ : Root m) := by
  rw [AlgEquiv.symm_apply_eq, splitEquiv_X_self]

theorem splitEquiv_symm_C (c : MvPolynomial (Root (fun τ : {τ // τ ≠ τ₀} => m τ.1)) R) :
    (splitEquiv R τ₀).symm (C c) = rename (fun y => (⟨y.1.1, y.2⟩ : Root m)) c := by
  rw [AlgEquiv.symm_apply_eq]
  induction c using MvPolynomial.induction_on with
  | C r =>
    simp only [rename_C]
    change _ = splitEquiv R τ₀ (algebraMap R _ r)
    rw [AlgEquiv.commutes]; rfl
  | add p q hp hq => simp [map_add (f := _), ← hp, ← hq]
  | mul_X p y hp =>
    simp only [map_mul, rename_X]
    rw [← hp, splitEquiv_X_ne R τ₀ y.1.2]

theorem splitEquiv_symm_esymm (j : ℕ) :
    (splitEquiv R τ₀).symm (esymm (Fin (m τ₀)) (MvPolynomial (Root (fun τ : {τ // τ ≠ τ₀} => m τ.1)) R) j) =
      chernRootsOver R m (X (τ₀, j)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [chernRootsOver, esymm, map_sum, map_prod, splitEquiv_symm_X]

theorem splitEquiv_rename_update (σ : Equiv.Perm (Fin (m τ₀))) (S : MvPolynomial (Root m) R) :
    splitEquiv R τ₀ (rename (Equiv.sigmaCongrRight
      (Function.update (1 : ∀ τ, Equiv.Perm (Fin (m τ))) τ₀ σ)) S) = rename σ (splitEquiv R τ₀ S) := by
  have : ((splitEquiv R τ₀).toAlgHom.comp (rename (Equiv.sigmaCongrRight
      (Function.update (1 : ∀ τ, Equiv.Perm (Fin (m τ))) τ₀ σ)))) =
      ((rename σ).restrictScalars R).comp (splitEquiv R τ₀).toAlgHom := by
    ext ⟨τ, i⟩ : 1
    by_cases h : τ = τ₀
    · subst h; simp [splitEquiv_X_self]
    · simp [splitEquiv_X_ne R τ₀ h, Function.update_of_ne h]
  exact congrArg (· S) (congrArg DFunLike.coe this)

theorem splitEquiv_rename_rest (w' : ∀ τ : {τ // τ ≠ τ₀}, Equiv.Perm (Fin (m τ.1))) (S : MvPolynomial (Root m) R) :
    splitEquiv R τ₀ (rename (Equiv.sigmaCongrRight
      (fun τ => if h : τ = τ₀ then (1 : Equiv.Perm (Fin (m τ))) else w' ⟨τ, h⟩)) S) =
      MvPolynomial.map (rename (Equiv.sigmaCongrRight w')).toRingHom (splitEquiv R τ₀ S) := by
  have : ((splitEquiv R τ₀).toAlgHom.comp (rename (Equiv.sigmaCongrRight
      (fun τ => if h : τ = τ₀ then (1 : Equiv.Perm (Fin (m τ))) else w' ⟨τ, h⟩)))) =
      (mapAlgHom (rename (Equiv.sigmaCongrRight w'))).comp (splitEquiv R τ₀).toAlgHom := by
    ext ⟨τ, i⟩ : 1
    by_cases h : τ = τ₀
    · subst h; simp [splitEquiv_X_self]
    · simp [splitEquiv_X_ne R τ₀ h, h]
  exact congrArg (· S) (congrArg DFunLike.coe this)

theorem rename_chernRootsOver (T : MvPolynomial ({τ // τ ≠ τ₀} × ℕ) R) :
    rename (fun y : Root (fun τ : {τ // τ ≠ τ₀} => m τ.1) => (⟨y.1.1, y.2⟩ : Root m))
      (chernRootsOver R (fun τ : {τ // τ ≠ τ₀} => m τ.1) T) =
      chernRootsOver R m (rename (Prod.map Subtype.val id) T) := by
  induction T using MvPolynomial.induction_on with
  | C r => simp [chernRootsOver]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p x hp =>
    simp only [map_mul, hp]
    congr 1
    simp [chernRootsOver, rename_rename]
    rfl

end Split

theorem mem_range_chernRootsOver (n : ℕ) : ∀ (ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι = n →
    ∀ (R : Type) [CommRing R] (m : ι → ℕ) (S : MvPolynomial (Root m) R),
    (∀ w : ∀ τ, Equiv.Perm (Fin (m τ)), rename (Equiv.sigmaCongrRight w) S = S) →
    S ∈ (chernRootsOver R m).range := by
  induction n with
  | zero =>
    intro ι _ _ hc R _ m S _
    haveI : IsEmpty ι := Fintype.card_eq_zero_iff.mp hc
    rw [eq_C_of_isEmpty S]
    exact Subalgebra.algebraMap_mem _ _
  | succ n ih =>
    intro ι _ _ hc R _ m S hS
    obtain ⟨τ₀⟩ : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
    have hc' : Fintype.card {τ // τ ≠ τ₀} = n := by
      simp [Fintype.card_subtype_compl, hc]
    let R' := MvPolynomial (Root (fun τ : {τ // τ ≠ τ₀} => m τ.1)) R
    let f : Fin (m τ₀) → MvPolynomial (Fin (m τ₀)) R' := fun i => esymm (Fin (m τ₀)) R' (↑i + 1)
    have hsym : splitEquiv R τ₀ S ∈ symmetricSubalgebra (Fin (m τ₀)) R' := by
      rw [mem_symmetricSubalgebra]
      intro σ
      rw [← splitEquiv_rename_update, hS]
    obtain ⟨T, hT⟩ := esymmAlgHom_fin_surjective R' (m := m τ₀) (n := m τ₀) le_rfl ⟨_, hsym⟩
    have hT' : aeval f T = splitEquiv R τ₀ S := by
      rw [← esymmAlgHom_apply, hT]
    have hcoef : ∀ d, AddMonoidAlgebra.coeff T d ∈ (chernRootsOver R (fun τ : {τ // τ ≠ τ₀} => m τ.1)).range := by
      intro d
      apply ih _ hc' R
      intro w'
      have hinv : MvPolynomial.map (rename (Equiv.sigmaCongrRight w')).toRingHom T = T := by
        apply esymmAlgHom_fin_injective R' (m := m τ₀) (n := m τ₀) le_rfl
        apply Subtype.ext
        rw [esymmAlgHom_apply, esymmAlgHom_apply]
        change aeval f _ = aeval f T
        rw [hT', ← hS (fun τ => if h : τ = τ₀ then 1 else w' ⟨τ, h⟩), splitEquiv_rename_rest, ← hT',
          aeval_def, aeval_def, algebraMap_eq, eval₂_map, eval₂_comp_left, map_comp_C]
        congr 1
        funext i
        exact (map_esymm _ _ _ _).symm
      have := congrArg (AddMonoidAlgebra.coeff · d) hinv
      rwa [coeff_map] at this
    let k : MvPolynomial (Fin (m τ₀)) R' →+* MvPolynomial (Root m) R :=
      (splitEquiv R τ₀).symm.toRingEquiv.toRingHom
    have hSE : S = k (eval₂ C f T) := by
      change S = (splitEquiv R τ₀).symm _
      rw [← algebraMap_eq, ← aeval_def, hT', AlgEquiv.symm_apply_apply]
    have key : k (eval₂ C f T) = eval₂ (k.comp C) (k ∘ f) T := eval₂_comp_left k C f T
    rw [hSE, key, eval₂_eq]
    refine Subalgebra.sum_mem _ fun d _ => Subalgebra.mul_mem _ ?_ (Subalgebra.prod_mem _ fun i _ => Subalgebra.pow_mem _ ?_ _)
    · obtain ⟨Tc, hTc⟩ := (AlgHom.mem_range _).mp (hcoef d)
      rw [RingHom.comp_apply, ← hTc]
      change (splitEquiv R τ₀).symm (C _) ∈ _
      rw [splitEquiv_symm_C, rename_chernRootsOver]
      exact AlgHom.mem_range_self _ _
    · change (splitEquiv R τ₀).symm (esymm _ _ _) ∈ _
      rw [splitEquiv_symm_esymm]
      exact AlgHom.mem_range_self _ _

theorem exists_chernRoots_eq_of_blockSymmetric : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (S : MvPolynomial (Root m) ℝ),
    (∀ w : ∀ τ, Equiv.Perm (Fin (m τ)), rename (Equiv.sigmaCongrRight w) S = S) →
    ∃ R : MvPolynomial (ι × ℕ) ℝ, chernRoots m R = S := by
  intro ι _ m S hS
  classical
  obtain ⟨R, hR⟩ := (AlgHom.mem_range _).mp (mem_range_chernRootsOver _ ι rfl ℝ m S hS)
  exact ⟨R, hR⟩

end GlobalTheory.BlockSymm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymmetricPolyChernRootsStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetric_poly_chern_roots : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (S : MvPolynomial (Root m) ℝ), (∀ w : ∀ τ, Equiv.Perm (Fin (m τ)), rename (Equiv.sigmaCongrRight w) S = S) → ∃ R : MvPolynomial (ι × ℕ) ℝ, chernRoots m R = S := by
  first | exact @GlobalTheory.BlockSymm.exists_chernRoots_eq_of_blockSymmetric | exact GlobalTheory.BlockSymm.exists_chernRoots_eq_of_blockSymmetric | (intros; apply GlobalTheory.BlockSymm.exists_chernRoots_eq_of_blockSymmetric <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaKeyRuleValueAtThetaPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaKeyRuleValueAtThetaPoint
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.FrameUnif GlobalTheory.Reg
open scoped Matrix TensorProduct

namespace GlobalTheory.KeyFourth

section Unif

open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.OrthoMetric GlobalTheory.ArchMetricCompare Formalism.L2.LamCM GlobalTheory.CM GlobalTheory.Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l}

theorem exists_unif_of_frame {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ ty) (i : Fin F.n)
    {P : (F.Di i).La →+ (Fin g → ℂ)} (hP : IsPeriod (F.Di i) ty P) {y : Sp ℂ ⟶ Xo.X} (hy : y = F.u i P)
    {s : LB.Sec (PPx y)} (Φ : FibKey Xo ℂ y) (ht : SecTie Φ.m Φ.th s)
    {θ : (Fin g → ℂ) → ℂ} {fr : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ}
    (c₁ : ∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j})
    (c₂ : ∀ j z, ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j z ≠ 0)
    (c₃ : ∀ j j' z, ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      fr j z = valAt' (F.ex i P z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j')
      (Xo.univ.t.PP.L.g j j').val * fr j' z)
    (c₄ : ∀ j, ⊤ ≤ (F.ex i P 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j 0 = valAt' y ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j))
      (Xo.univ.t.PP.rig.s (fun _ => j)).val)
    (c₆ : ∀ j z (pt : Sp ℂ ⟶ Gx y), pt ≫ gxFst y = (F.ex i P z).left → pt ≫ gxSnd y = 𝟙 (Sp ℂ) →
      ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' pt ((PPx y).U (fun _ => j)) (s.f (fun _ => j)) = θ z * fr j z) :
    ∃ u : HolUnif Φ.key.P.A Φ.key.P.L g, u.Λ = P.range.toIntSubmodule ∧
      u.IsRig Φ.key.rig ∧ u.IsFn Φ.key.th θ ∧ ∀ z, (u.ex z).left ≫ Φ.m.φ = (F.ex i P z).left := by
  subst hy
  obtain ⟨w, ⟨hw, hrig⟩, hth⟩ := val_tie Φ.m ht
  obtain ⟨w', hw', hinv⟩ := ConjUnif.exists_inv w hw
  have hL := Φ.T.t.PP.isLB
  have hM := LB.isLB_pull Xo.univ.t.PP.isLB Φ.m.φ
  have hol := isHolTo_exp F i hP
  let u₁ := fibreUnif Φ.m.cart (F.ex i P) P.range fr (F.ex_add i P hP) (F.ex_onto i P hP) (F.ex_ker i P hP)
    hP.2.2.1 hP.2.2.2.1 hol c₁ c₂ c₃
  have hex : ∀ z, (u₁.ex z).left ≫ Φ.m.φ = (F.ex i P z).left := fun z => liftPt_comp Φ.m.cart _
  have hle : ∀ z j, ⊤ ≤ (u₁.ex z).left ⁻¹ᵁ (Xo.univ.t.PP.L.pull Φ.m.φ).U j →
      ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U (j PUnit.unit) := fun z j => (lift_le Φ.m.cart _ j).1
  have hfr : ∀ (j : Xo.univ.t.PP.L.ι) (k : Φ.T.t.PP.L.ι) (z : Fin g → ℂ),
      ⊤ ≤ (u₁.ex z).left ⁻¹ᵁ ((Xo.univ.t.PP.L.pull Φ.m.φ).U (fun _ => j) ⊓ Φ.T.t.PP.L.U k) →
      valAt' (u₁.ex z).left ((Xo.univ.t.PP.L.pull Φ.m.φ).U (fun _ => j) ⊓ Φ.T.t.PP.L.U k)
        (w.s (fun _ => j, k)).val * (carry u₁ hM hL hw').fr k z = fr j z := by
    intro j k z hz
    obtain ⟨hj, hk⟩ := (top_le_preimage_inf _ _ _).1 hz
    rw [carry_fr u₁ hM hL hw' k (fun _ => j) z hk hj, hinv _ _ _ hz]
    exact mul_inv_cancel_left₀ (valAt'_unit_ne_zero _ hz (w.s (fun _ => j, k))) _
  refine ⟨carry u₁ hM hL hw', rfl, ?_, ?_, hex⟩
  · intro k hk
    have h0 : (u₁.ex 0).left = eSec Φ.T.t.G := by
      rw [(u₁.ker 0).2 u₁.Λ.zero_mem, Hom.one_def]
      simp [eSec]
    obtain ⟨j, hj⟩ := exists_chart_at hM (u₁.ex 0).left
    have hk' : ⊤ ≤ (u₁.ex 0).left ⁻¹ᵁ Φ.T.t.PP.L.U (k PUnit.unit) := by
      rw [h0]
      exact fun p hp => mem_pull.1 (hk hp)
    have hz := (top_le_preimage_inf _ _ _).2 ⟨hj, hk'⟩
    have e := hfr (j PUnit.unit) (k PUnit.unit) 0 hz
    rw [c₄ _ (hle 0 j hj), h0] at e
    rw [h0] at hz
    have e' := val_rig Φ.m.cm.e_comm w Φ.T.t.PP.rig Xo.univ.t.PP.rig hrig (j PUnit.unit) (k PUnit.unit) hz
    rw [Φ.m.base] at e'
    exact mul_left_cancel₀ (valAt'_unit_ne_zero _ hz _) (e.trans e')
  · intro k z hk
    obtain ⟨j, hj⟩ := exists_chart_at hM (u₁.ex z).left
    have hz := (top_le_preimage_inf _ _ _).2 ⟨hj, hk⟩
    obtain ⟨pt, p₁, p₂, hpt⟩ := hth (u₁.ex z).left (Over.w _)
    have e := hfr (j PUnit.unit) k z hz
    refine mul_left_cancel₀ (valAt'_unit_ne_zero _ hz (w.s (fun _ => j PUnit.unit, k))) ?_
    have e₁ := hpt (j PUnit.unit) k hz
    have e₂ := c₆ (j PUnit.unit) z pt (p₁.trans (hex z)) p₂ (hle z j hj)
    rw [← e] at e₂
    exact e₁.symm.trans (e₂.trans (mul_left_comm _ _ _))

end Unif

theorem mulVec_period {g : ℕ} {La : Type} [AddCommGroup La] (P : La →+ (Fin g → ℂ))
    (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] La) (h τ : Matrix (Fin g) (Fin g) ℂ)
    (hn : ∀ i, h *ᵥ P (bas (Pi.single (Sum.inl i) 1)) = Pi.single i 1 ∧
      h *ᵥ P (bas (Pi.single (Sum.inr i) 1)) = τ *ᵥ Pi.single i 1) (a : Fin g ⊕ Fin g → ℤ) :
    h *ᵥ P (bas a) = (fun i => (a (Sum.inl i) : ℂ)) + τ *ᵥ (fun i => (a (Sum.inr i) : ℂ)) := by
  have h1 : ∀ m : Fin g → ℤ, (fun i => (m i : ℂ)) = ∑ i, m i • (Pi.single i 1 : Fin g → ℂ) := by
    intro m; ext k; simp [Finset.sum_apply, Pi.single_apply]
  have h2 : a = ∑ s, a s • (Pi.single s 1 : Fin g ⊕ Fin g → ℤ) := by
    ext k; simp [Finset.sum_apply, Pi.single_apply]
  rw [h1 (fun i => a (Sum.inl i)), h1 (fun i => a (Sum.inr i))]
  conv_lhs => rw [h2]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_zsmul, Fintype.sum_sum_type, map_add (f := _), Matrix.mulVec_add, Matrix.mulVec_sum,
    Matrix.mulVec_smul, (hn _).1, (hn _).2]

theorem normalAt_of_coord (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L x.P.g) {La : Type} [AddCommGroup La]
    (P : La →+ (Fin x.P.g → ℂ)) (bas : (Fin x.P.g ⊕ Fin x.P.g → ℤ) ≃ₗ[ℤ] La)
    (h τ : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (c₁ c₂ : Fin x.P.g → ℂ) (a : ℂ) (hu : IsUnit h.det)
    (hsymm : τ.IsSymm) (hpos : (τ.map Complex.im).PosDef)
    (hn : ∀ i, h *ᵥ P (bas (Pi.single (Sum.inl i) 1)) = Pi.single i 1 ∧
      h *ᵥ P (bas (Pi.single (Sum.inr i) 1)) = τ *ᵥ Pi.single i 1)
    (hΛ : u.Λ = P.range.toIntSubmodule) (hR : u.IsRig x.rig)
    (hF : u.IsFn x.th fun z => a * thetaChar τ c₁ c₂ (h *ᵥ z)) (hD : ∀ i, u.IsDiff (Pi.single i 1) (x.v i)) :
    KeyPow.NormalAt x τ ((2 * Real.pi * Complex.I : ℂ) • hᵀ) c₁ c₂ a := by
  let φ : (Fin x.P.g → ℂ) ≃L[ℂ] (Fin x.P.g → ℂ) :=
    (Matrix.toLinearEquiv' h (Matrix.invertibleOfIsUnitDet _ hu)).symm.toContinuousLinearEquiv
  have hφ : ∀ z, h *ᵥ φ z = z := fun z =>
    (Matrix.toLinearEquiv' h (Matrix.invertibleOfIsUnitDet _ hu)).apply_symm_apply z
  have hφ' : ∀ z, φ (h *ᵥ z) = z := fun z =>
    (Matrix.toLinearEquiv' h (Matrix.invertibleOfIsUnitDet _ hu)).symm_apply_apply z
  have hπ : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  clear_value φ
  refine ⟨KeyNormalForm.change u φ (fun _ => 0) (differentiable_const _), hsymm, hpos, fun z => ?_,
    KeyNormalForm.isRig_change u φ _ _ rfl hR,
    KeyNormalForm.isFn_change u φ _ _ hF fun z => by simp only [hφ, Complex.exp_zero, mul_one],
    fun i => KeyNormalForm.isDiff_change u φ _ _ ?_⟩
  · rw [KeyNormalForm.mem_change, hΛ]
    constructor
    · rintro ⟨v, hv⟩
      obtain ⟨m, rfl⟩ := bas.surjective v
      refine ⟨fun i => m (Sum.inl i), fun i => m (Sum.inr i), ?_⟩
      rw [← hφ z, ← hv]
      exact mulVec_period _ bas _ _ hn m
    · rintro ⟨m, n, rfl⟩
      refine ⟨bas (Sum.elim m n), ?_⟩
      rw [← hφ' (P _), mulVec_period _ bas _ _ hn]
      rfl
  · have e₁ : (2 * Real.pi * Complex.I : ℂ)⁻¹ • ((2 * Real.pi * Complex.I : ℂ) • hᵀ) i = h *ᵥ Pi.single i 1 := by
      funext j
      simp only [Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, Matrix.transpose_apply, Matrix.mulVec_single_one,
        Matrix.col_apply]
      rw [inv_mul_cancel_left₀ hπ]
    rw [e₁, hφ']
    exact hD i

theorem value_at_thetaPt : ∀ κ : GlobalTheory.KeyCl.Rule, GlobalTheory.KeyCl.Homog (fun _ => 1) κ → GlobalTheory.KeyCl.ThetaOne κ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1)) (r : ℕ) (M : GlobalTheory.FrameUnif.ModelsOf F r) (k : Fin F.n) (T : ThetaData e F M k), ∀ b ∈ T.co ⁻¹' (M.X k).dom, ∀ (a : ℂ) (y : FrPt Xo c (CAt σ)) (Φ : FibKey Xo ℂ y.x), a ≠ 0 → IsThetaPt T b a y → Tied (S := ℂ) e y.s y.u Φ → a ^ 8 * (κ ℂ Φ.key : ℂ) = ((2 * Real.pi * Complex.I) ^ g * (T.h b).det) ^ 4 := by
  intro κ hH hT E _ _ _ H Dw l Xo c σ g e F r M k T b hb a y Φ ha ⟨hx, hder, hsec⟩ ⟨ht, hg, hv⟩
  subst hg
  have hP := T.isPer _ hb
  obtain ⟨hu, hsymm, hpos, hn⟩ := T.norm b hb
  have hj : Differentiable ℂ (fun z : Fin Φ.T.g → ℂ => (b, z)) := by fun_prop
  obtain ⟨u, hΛ, hR, hF, hex⟩ := exists_unif_of_frame F k hP hx Φ ht
    (θ := fun z => a * thetaChar (T.ta b) T.c₁ T.c₂ (T.h b *ᵥ z)) (fr := fun j z => T.fr j (b, z))
    (fun j => (T.fr_hol j).comp hj.differentiableOn fun z hz => ⟨hb, hz⟩)
    (fun j z hz => T.fr_ne j b z hb hz) (fun j j' z hz => T.fr_coc j j' b z hb hz)
    (fun j hj => (T.fr_rig j b hb hj).trans (congrArg (fun q => valAt' q _ _) hx.symm)) hsec
  have hπ : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have hN := normalAt_of_coord Φ.key u _ T.bas (T.h b) (T.ta b) T.c₁ T.c₂ a hu hsymm hpos hn hΛ hR hF fun i => by
    obtain ⟨W, hW, -⟩ := (existsUnique_isDiff_and_linear Φ.key u).1 _ (Φ.basis.1 i)
    have d := OrthoMetric.isDerivAt0_comp u Φ.m.φ (e := fun z => (F.ex k (T.Pf (T.co b)) z).left) hex (Φ.basis.1 i) hW
    have d' := hder (e i).1 (e i).2
    rw [show e.symm ⟨(e i).1, (e i).2⟩ = i from e.symm_apply_apply i,
      ← show _ = y.u (e i).1 (e i).2 from hv i] at d'
    obtain ⟨t₁, -, t₃⟩ := isDerivAt0_ex_isTanAt E H Dw l Xo _ _ _ F k _ hP
    have hWi : W = Pi.single i 1 := (t₃ _ (t₁ _ _ d)).unique d d'
    exact hWi ▸ hW
  have hdet : ((2 * Real.pi * Complex.I : ℂ) • (T.h b)ᵀ).det = (2 * Real.pi * Complex.I) ^ Φ.T.g * (T.h b).det := by
    rw [Matrix.det_smul, Matrix.det_transpose, Fintype.card_fin]
  have key := KeyCl.value_of_normalAt hH hT Φ.key ⟨T.half₁, T.half₂⟩ ha
    (hdet.trans_ne (mul_ne_zero (pow_ne_zero _ hπ) hu.ne_zero)) hN
  rw [key, mul_div_cancel₀ _ (pow_ne_zero 8 ha)]
  exact congrArg (· ^ 4) hdet

end GlobalTheory.KeyFourth
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaKeyRuleValueAtThetaPointStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.FrameUnif GlobalTheory.Reg
open scoped Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_key_rule_value_at_theta_point : ∀ κ : GlobalTheory.KeyCl.Rule, GlobalTheory.KeyCl.Homog (fun _ => 1) κ → GlobalTheory.KeyCl.ThetaOne κ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1)) (r : ℕ) (M : GlobalTheory.FrameUnif.ModelsOf F r) (k : Fin F.n) (T : ThetaData e F M k), ∀ b ∈ T.co ⁻¹' (M.X k).dom, ∀ (a : ℂ) (y : FrPt Xo c (CAt σ)) (Φ : FibKey Xo ℂ y.x), a ≠ 0 → IsThetaPt T b a y → Tied (S := ℂ) e y.s y.u Φ → a ^ 8 * (κ ℂ Φ.key : ℂ) = ((2 * Real.pi * Complex.I) ^ g * (T.h b).det) ^ 4 := by
  first | exact @GlobalTheory.KeyFourth.value_at_thetaPt | exact GlobalTheory.KeyFourth.value_at_thetaPt | (intros; apply GlobalTheory.KeyFourth.value_at_thetaPt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsCoordinatesIndexOfFamilyTupleEq
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsCoordinatesIndexOfFamilyTupleEq
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Rw

variable (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (hX : X.B.fields.Ok) (Xg : Finset (Gc X.B px → X.B.LL))
  (tr : TrI X.B px)


set_option maxHeartbeats 2000000 in
theorem rMat_famR_eq (U U' : Set I.ι) (P : Subgroup (Gc X.B px)) (ψ : P →* X.toD7.what₂.LLˣ) (t : TupU I U) (t' : TupU I U')
    (h : t.1 = t'.1) :
    rMat (D := X.toD7) (famR X I hX U Xg tr).A P ψ t = rMat (D := X.toD7) (famR X I hX U' Xg tr).A P ψ t' := by
  obtain ⟨τ, hτ⟩ := t
  obtain ⟨τ', hτ'⟩ := t'
  obtain rfl : τ = τ' := h
  exact (by with_unfolding_all exact ((Eq.refl (rMat (D := X.toD7) (famR X I hX U Xg tr).A P ψ ⟨τ, hτ⟩)) :))


set_option maxHeartbeats 2000000 in
theorem lMat_famR_eq (U U' : Set I.ι) (P : Subgroup (Gc X.B px)) (ψ : P →* X.toD7.what₂.LLˣ) (i : Fin X.toD7.R.m)
    (t : TupU I U) (t' : TupU I U') (h : t.1 = t'.1) :
    lMat (D := X.toD7) (famR X I hX U Xg tr).A P ψ i t = lMat (D := X.toD7) (famR X I hX U' Xg tr).A P ψ i t' := by
  obtain ⟨τ, hτ⟩ := t
  obtain ⟨τ', hτ'⟩ := t'
  obtain rfl : τ = τ' := h
  exact (by with_unfolding_all exact ((Eq.refl (lMat (D := X.toD7) (famR X I hX U Xg tr).A P ψ i ⟨τ, hτ⟩)) :))


set_option maxHeartbeats 2000000 in
theorem mAU_mLU_ixOf : ∀ (X : Stages) (px : PreX X.B.toPre) (I : ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (t : TupU I U), (∀ b, mAU X I hX Xg tr b (ixOf I U t) = rMat (D := X.toD7) (famR X I hX U Xg tr).A (levP (face0 X I hX U Xg tr).lv2 b).1 (levP (face0 X I hX U Xg tr).lv2 b).2 t) ∧ ∀ i : Fin X.toD7.R.m, mLU X I hX Xg tr (ixOf I U t) ((i : ℕ) + 1) = lMat (D := X.toD7) (famR X I hX U Xg tr).A (face0 X I hX U Xg tr).lv2.P0 (face0 X I hX U Xg tr).lv2.ψ0 i t := by
  intro X px I hX U Xg tr t
  refine ⟨fun b => ?_, fun i => ?_⟩
  · cases b
    · exact rMat_famR_eq X I hX Xg tr Set.univ U (lev0 I) (chr0 I) (tAll I (ixOf I U t)) t (tup_ixOf I t)
    · exact rMat_famR_eq X I hX Xg tr Set.univ U (lev1 I) (chr1 I) (tAll I (ixOf I U t)) t (tup_ixOf I t)
  · have hi : 1 ≤ (i : ℕ) + 1 ∧ (i : ℕ) + 1 ≤ X.toD7.R.m := ⟨by omega, i.2⟩
    unfold mLU
    rw [dite_eq_left hi]
    exact lMat_famR_eq X I hX Xg tr Set.univ U (lev0 I) (chr0 I) i (tAll I (ixOf I U t)) t (tup_ixOf I t)

end GlobalTheory.Mem.R3.Rw

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsCoordinatesIndexOfFamilyTupleEqStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formsCoordinates_indexOfFamilyTuple_eq : ∀ (X : Stages) (px : PreX X.B.toPre) (I : ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (t : TupU I U), (∀ b, mAU X I hX Xg tr b (ixOf I U t) = rMat (D := X.toD7) (famR X I hX U Xg tr).A (levP (face0 X I hX U Xg tr).lv2 b).1 (levP (face0 X I hX U Xg tr).lv2 b).2 t) ∧ ∀ i : Fin X.toD7.R.m, mLU X I hX Xg tr (ixOf I U t) ((i : ℕ) + 1) = lMat (D := X.toD7) (famR X I hX U Xg tr).A (face0 X I hX U Xg tr).lv2.P0 (face0 X I hX U Xg tr).lv2.ψ0 i t := by
  first | exact @GlobalTheory.Mem.R3.Rw.mAU_mLU_ixOf | exact GlobalTheory.Mem.R3.Rw.mAU_mLU_ixOf | (intros; apply GlobalTheory.Mem.R3.Rw.mAU_mLU_ixOf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartsTupleTrivQ
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC.ChTw


set_option maxHeartbeats 8000000 in
theorem match_base_trivQ : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 B.host.F))) (i : ℕ), i ≤ B.R.m → ∀ (Ch0 : Type) (chOf0 : (I.stp u I.mu0 i).Cl → Ch0) (Lb0 : Ch0 → Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)) (U0 : Ch0 → Subgroup (GA B (B.R.N i))) (chi0 : ∀ β, U0 β →* ℂˣ) (y0 : (I.stp u I.mu0 i).Cl → GA B (B.R.N i)) (st0 : ∀ c, (I.stp u I.mu0 i).Stab c → GL (Fin (B.R.N i)) B.host.E) (k0 : Ch0 → GA B (B.R.N i)), 1 ≤ i → i < B.R.m → (∀ v, v ∈ Q ↔ I.UnderQ a v) → I.Reads u I.mu0 i chOf0 Lb0 U0 chi0 y0 st0 k0 → ∃ (g : Chart I u a i → Ch0) (k : Chart I u a i → GA B (B.R.N i)), AdmK I u a i k ∧ (∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → bc (prV (E := B.host.E) v) (k β) = 1) ∧ ∀ β, ∃ c, chartOf I u a i c = β ∧ ∃ c0, chOf0 c0 = g β ∧ ∀ x : GA B (B.R.N i), (∀ v ∈ Q, bc (prV (E := B.host.E) v) x = 1) → (∀ κ, LocMv I u a i c ((k β)⁻¹ * x * k β) κ → ∃ κ0, LocMv I u I.mu0 i c0 ((k0 (g β))⁻¹ * x * k0 (g β)) κ0 ∧ (I.stp u a i).chr c.1 κ = (I.stp u I.mu0 i).chr c0.1 κ0) ∧ (∀ κ0, LocMv I u I.mu0 i c0 ((k0 (g β))⁻¹ * x * k0 (g β)) κ0 → ∃ κ, LocMv I u a i c ((k β)⁻¹ * x * k β) κ) := by
  intro B X I hI hP l u a Q i hi Ch0 chOf0 Lb0 U0 chi0 y0 st0 k0 h1 h2 hQ hR0
  obtain ⟨c0f, t, ht1, ht2, ht3, hM⟩ := GlobalTheory.Mem.Col2.TC.ChTw.Match.match_idx I hI hP l u a Q i hi h1 h2 hQ
  refine ⟨fun β => chOf0 (c0f β), fun β => k0 (chOf0 (c0f β)) * t β,
    GlobalTheory.Mem.Col2.TC.ChTw.admissibleBasePoint_chart_mul_twist I hI u a i Ch0 chOf0 Lb0 U0 chi0 y0 st0 k0 hR0 _ t ht1 ht2 ht3, ?_, ?_⟩
  · intro β v hv
    obtain ⟨hT, hg⟩ := GlobalTheory.Mem.Col2.TC.underQ_prime_to_bad I hI l u a v hv
    show bc (prV (E := B.host.E) v) (k0 (chOf0 (c0f β)) * t β) = 1
    rw [map_mul, hR0.k_off (chOf0 (c0f β)) v hT (GlobalTheory.Mem.Col2.TC.not_underQ_mu0 I hI v) (Or.inl rfl), ht2 β v (Or.inr hg), mul_one]
  intro β
  obtain ⟨c, hc, hs⟩ := hM β
  refine ⟨c, hc, c0f β, rfl, ?_⟩
  intro x hx
  have e : (k0 (chOf0 (c0f β)) * t β)⁻¹ * x * (k0 (chOf0 (c0f β)) * t β) =
      (t β)⁻¹ * ((k0 (chOf0 (c0f β)))⁻¹ * x * k0 (chOf0 (c0f β))) * t β := by group
  rw [e]
  refine hs _ fun v hv => ?_
  rw [map_mul, map_mul, hx v hv, mul_one, map_inv, inv_mul_cancel]


set_option maxHeartbeats 8000000 in
theorem charts_match_trivQ : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (i : ℕ) (hi : i ≤ B.R.m) (Ch0 : Type) (chOf0 : (I.stp u I.mu0 i).Cl → Ch0) (K0 : ∀ β : Ch0, LevelChart (I.rec7 l Z) (B.T u) (badG (I.rec7 l Z)) i hi (fun c : {c // chOf0 c = β} => (I.chain l u I.mu0).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u I.mu0 i c.1))), 1 ≤ i → i < B.R.m → (∀ v, v ∈ Q ↔ I.UnderQ a v) → I.ReadsK l Z u I.mu0 i hi chOf0 K0 → ∃ (g : Chart I u a i → Ch0) (k : Chart I u a i → GA B (B.R.N i)), AdmK I u a i k ∧ (∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → bc (prV (E := B.host.E) v) (k β) = 1) ∧ ∀ (K : ∀ β : Chart I u a i, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) i hi (fun c : {c // chartOf I u a i c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))), I.Reads u a i (chartOf I u a i) (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (chartOf I u a i c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chartOf I u a i c)).stabI ⟨c, rfl⟩ s).1) k → ∀ β, (∀ κ : (K β).lev.U, (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → ∃ h' : κ.1 ∈ (K0 (g β)).lev.U, (K β).lev.chi κ = (K0 (g β)).lev.chi ⟨κ.1, h'⟩) ∧ ∀ κ' : (K0 (g β)).lev.U, (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ'.1 = 1) → κ'.1 ∈ (K β).lev.U := by
  intro B X I hI hP l Z u a Q i hi Ch0 chOf0 K0 h1 h2 hQ hR0
  obtain ⟨k0, hk0⟩ := hR0
  obtain ⟨g, k, hk, hkQ, hM⟩ := match_base_trivQ I hI hP l u a Q i hi Ch0 chOf0 _ _ _ _ _ k0 h1 h2 hQ hk0
  refine ⟨g, k, hk, hkQ, ?_⟩
  intro K hK β
  obtain ⟨c, hc, c0, hc0, hx⟩ := hM β
  subst hc
  have hgram := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.2.2 i hi).1
  have huni : ∀ {bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))} (S : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (B.T u) (I.rec7 l Z).R.f bad) (x : GA B (B.R.N i)), x ∈ S.U → x ∈ Formalism.L2.Herm.UstdAf B.sp.cm (B.R.N i) := by
    intro bad S x hx
    have h := ((S.U_eq x).1 hx).1
    rw [hgram] at h
    exact h
  have hnQ0 : ∀ v, ¬ I.UnderQ I.mu0 v := by
    rintro v ⟨P, hP, -⟩
    rw [ColIn.twistPrimes_reference_tuple_eq_empty] at hP
    exact absurd hP (Finset.notMem_empty _)
  refine ⟨fun κ hκ => ?_, fun κ' hκ' => ?_⟩
  · obtain ⟨κ1, hl1⟩ := GlobalTheory.Mem.Col2.TC.ChTw.locMv_of_mem I hI l u a i hi _ _ _ _ _ _ k hK c κ.1 (huni _ κ.1 κ.2)
      (fun v hv => hκ v ((hQ v).2 hv)) κ.2
    obtain ⟨κ0, hl0, hchr⟩ := (hx κ.1 hκ).1 κ1 hl1
    obtain ⟨hm0, hc0'⟩ := reads_of_locMv I hI hk0 c0 κ.1 κ0 (by rw [hc0]; exact hl0)
    obtain ⟨hm, hcc⟩ := reads_of_locMv I hI hK c κ.1 κ1 hl1
    have key : ∀ β0 (e : chOf0 c0 = β0), ∃ h' : κ.1 ∈ (K0 β0).lev.U,
        (((K0 β0).lev.chi ⟨κ.1, h'⟩ : ℂˣ) : ℂ) = B.embLL (((I.stp u I.mu0 i).chr c0.1 κ0 : B.LLˣ) : B.LL) := by
      intro β0 e
      subst e
      exact ⟨hm0, hc0'⟩
    obtain ⟨h', e'⟩ := key _ hc0
    refine ⟨h', Units.ext ?_⟩
    rw [e', ← hchr]
    exact hcc
  · have hm0 : κ'.1 ∈ (K0 (chOf0 c0)).lev.U := by rw [hc0]; exact κ'.2
    obtain ⟨κ0, hl0⟩ := GlobalTheory.Mem.Col2.TC.ChTw.locMv_of_mem I hI l u I.mu0 i hi _ _ _ _ _ _ k0 hk0 c0 κ'.1 (huni _ κ'.1 hm0)
      (fun v hv => absurd hv (hnQ0 v)) hm0
    rw [hc0] at hl0
    obtain ⟨κ, hl⟩ := (hx κ'.1 hκ').2 κ0 hl0
    exact (reads_of_locMv I hI hK c κ'.1 κ hl).1


set_option maxHeartbeats 8000000 in
theorem charts_tuple_trivQ : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (i : ℕ) (hi : i ≤ B.R.m) (Ch0 : Type) (chOf0 : (I.stp u I.mu0 i).Cl → Ch0) (K0 : ∀ β : Ch0, LevelChart (I.rec7 l Z) (B.T u) (badG (I.rec7 l Z)) i hi (fun c : {c // chOf0 c = β} => (I.chain l u I.mu0).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u I.mu0 i c.1))), 1 ≤ i → i < B.R.m → (∀ v, v ∈ Q ↔ I.UnderQ a v) → I.ReadsK l Z u I.mu0 i hi chOf0 K0 → ∃ (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a i).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))) (g : Ch → Ch0), (∃ k : Ch → GA B (B.R.N i), I.Reads u a i chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k ∧ ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → bc (prV (E := B.host.E) v) (k β) = 1) ∧ ∀ β, (∀ v, v ∉ Q → (K β).lev.Uloc v = (K0 (g β)).lev.Uloc v) ∧ (∃ n : ℕ, 0 < n ∧ ∀ κ, (K β).lev.chi κ ^ n = 1) ∧ ∀ (κ : (K β).lev.U) (κ' : (K0 (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = (K0 (g β)).lev.chi κ' := by
  intro B X I hok hpins l Z u a Q i hi Ch0 chOf0 K0 h1 h2 hQ hR
  obtain ⟨g, k, hk, hkQ, hC⟩ := charts_match_trivQ I hok hpins l Z u a Q i hi Ch0 chOf0 K0 h1 h2 hQ hR
  obtain ⟨K, hKB⟩ := GlobalTheory.Mem.Col2.ChExM.exists_charts I hok hpins l Z u a Q i hi h1 h2 hQ k hk
  have hK := hKB.1
  have hfin := hKB.2
  have hCK := hC K hK
  haveI := finite_chart I l u a i
  refine ⟨Chart I u a i, inferInstance, chartOf I u a i, K, g, ⟨k, hK, hkQ⟩, fun β => ⟨?_, hfin β, ?_⟩⟩
  · intro v hv
    refine GlobalTheory.stepLevel_uloc_eq_of_agree (K β).lev (K0 (g β)).lev (Q : Set _) (fun x hx => ⟨fun hxK => ?_, fun hx0 => ?_⟩) v hv
    · exact ((hCK β).1 ⟨x, hxK⟩ hx).1
    · exact (hCK β).2 ⟨x, hx0⟩ hx
  · intro κ κ' he hq
    obtain ⟨h', e⟩ := (hCK β).1 κ hq
    exact e.trans (congrArg (K0 (g β)).lev.chi (Subtype.ext he))

end GlobalTheory.Mem.Col2.TC.ChTw
end
end
