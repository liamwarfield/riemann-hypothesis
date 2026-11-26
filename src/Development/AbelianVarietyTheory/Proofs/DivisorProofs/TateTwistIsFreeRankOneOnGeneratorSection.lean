module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistSectionsLocallyGenerated
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMayerVietorisConnectingExact
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasisKaehlerOfAlgebraicIndependent
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpObjTangentVectorAddAtPoint
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSupercuspidalOfIsCuspidal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafSectionsExact

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistIsFreeRankOneOnGeneratorSection
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistIsFreeRankOneOnGeneratorSection
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.TwistedGenericPoint

theorem loc_point {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P) (u : U) :
    ∃ (V : Scheme.{0}) (j : V ⟶ U) (v : V), Etale j ∧ j v = u ∧ P V j := by
  obtain ⟨S, hS, hP⟩ := h
  obtain ⟨𝒰, h𝒰⟩ := Scheme.exists_cover_of_mem_grothendieckTopology hS
  obtain ⟨hsurj, hprop⟩ := (Scheme.ofArrows_mem_precoverage_iff _).1 𝒰.mem₀
  obtain ⟨k, v, hv⟩ := hsurj u
  exact ⟨𝒰.X k, 𝒰.f k, v, hprop k, hv, hP _ _ (h𝒰 _ (𝒰.f k) (Presieve.ofArrows.mk k))⟩

theorem isEmpty_of_subsingleton (X : Scheme.{0}) [Subsingleton Γ(X, ⊤)] : IsEmpty X := by
  refine ⟨fun x => ?_⟩
  have := (X.presheaf.germ ⊤ x trivial).hom.domain_nontrivial
  exact not_subsingleton Γ(X, ⊤) inferInstance

theorem smul_residue {q : ℕ} {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M] (n : ℕ) (y : M) :
    n • y = (ULift.up (n : ZMod q) : ULift.{1} (ZMod q)) • y := by
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
  rfl

end GlobalTheory.TwistedGenericPoint

namespace GlobalTheory


open GlobalTheory.TwistedGenericPoint in
theorem twGen_gen : ∀ (q : ℕ) (i : ℤ) (S : Scheme.{0}) (ζ : Prim q Γ(S, ⊤)), Gen (tw q i) S (twGen i ζ) := by
  intro q i S ζ U s
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · have : Subsingleton Γ(S, ⊤) := by
      obtain ⟨hu, _⟩ := ζ.2
      exact subsingleton_of_zero_eq_one (isUnit_zero_iff.1 (by simpa using hu))
    have hS := isEmpty_of_subsingleton S
    have hU : IsEmpty U := ⟨fun u => hS.elim (s u)⟩
    exact ⟨fun _ u => (hU.elim u), fun _ hne _ => (hU.elim hne.some)⟩
  · haveI : NeZero q := ⟨hq.ne'⟩
    obtain ⟨-, h2, h3, h4, -⟩ := GlobalTheory.T.tateTwist_sections_locally_generated q i
    refine ⟨fun x u => ?_, fun c hne hc => ?_⟩
    · obtain ⟨V, j, v, hj, hjv, c, hc⟩ := loc_point (h2 U (ζ.map s.appTop.hom) x) u
      refine ⟨V, j, v, (c : ZMod q), hj, hjv, ?_⟩
      have e : Sec.pull (j ≫ s) (twGen i ζ) = twGen i ((ζ.map s.appTop.hom).map j.appTop.hom) :=
        h4 V S (j ≫ s) ζ
      rw [e]
      exact hc.trans (smul_residue c _)
    · haveI : Nonempty U := hne
      have e : Sec.pull s (twGen i ζ) = twGen i (ζ.map s.appTop.hom) := h4 U S s ζ
      rw [e] at hc
      have h0 : c.val • twGen i (ζ.map s.appTop.hom) = 0 := by
        rw [smul_residue (q := q), ZMod.natCast_zmod_val]
        exact hc
      have hd := h3 U _ c.val h0
      rw [← ZMod.natCast_zmod_val c]
      exact (ZMod.natCast_eq_zero_iff _ _).2 hd

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistIsFreeRankOneOnGeneratorSectionStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwist_isFreeRankOne_on_generatorSection : ∀ (q : ℕ) (i : ℤ) (S : Scheme.{0}) (ζ : Prim q Γ(S, ⊤)), Gen (tw q i) S (twGen i ζ) := by
  first | (exact @GlobalTheory.twGen_gen) | (exact GlobalTheory.twGen_gen) | (intros; apply GlobalTheory.twGen_gen  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MayerVietorisEquivalenceOfCover
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MayerVietorisEquivalenceOfCover
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.MayerVietorisEqv

theorem a4 : GlobalTheory.EtC.A4 := by
  intro R _ U V E U' V' E' f g f' g' p u v hu hv F hc hc' hU hV hW
  obtain ⟨d, hex, hnat⟩ := GlobalTheory.T.exists_mayerVietoris_connecting_exact R F
  have hwf : pullback.map f g f' g' u v p hu hv ≫ pullback.fst f' g' = pullback.fst f g ≫ u := pullback.lift_fst _ _ _
  have hwg : pullback.map f g f' g' u v p hu hv ≫ pullback.snd f' g' = pullback.snd f g ≫ v := pullback.lift_snd _ _ _
  have cf : ∀ n x, pull R f F n (pull R p F n x) = pull R u F n (pull R f' F n x) := by
    intro n x; rw [← pull_comp, ← pull_comp, hu]
  have cg : ∀ n x, pull R g F n (pull R p F n x) = pull R v F n (pull R g' F n x) := by
    intro n x; rw [← pull_comp, ← pull_comp, hv]
  have cfst : ∀ n x, pull R (pullback.map f g f' g' u v p hu hv) F n (pull R (pullback.fst f' g') F n x) =
      pull R (pullback.fst f g) F n (pull R u F n x) := by
    intro n x; rw [← pull_comp, ← pull_comp, hwf]
  have csnd : ∀ n x, pull R (pullback.map f g f' g' u v p hu hv) F n (pull R (pullback.snd f' g') F n x) =
      pull R (pullback.snd f g) F n (pull R v F n x) := by
    intro n x; rw [← pull_comp, ← pull_comp, hwg]
  have hcond : ∀ n x, pull R (pullback.fst f g) F n (pull R f F n x) =
      pull R (pullback.snd f g) F n (pull R g F n x) := by
    intro n x; rw [← pull_comp, ← pull_comp, pullback.condition]
  intro n
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by ring⟩
  constructor
  · rw [injective_iff_map_eq_zero]
    intro y hy
    have h1 : pull R f' F (m + 1) y = 0 := by
      apply (hU (m + 1)).1
      rw [← cf, hy, map_zero, map_zero]
    have h2 : pull R g' F (m + 1) y = 0 := by
      apply (hV (m + 1)).1
      rw [← cg, hy, map_zero, map_zero]
    obtain ⟨c, rfl⟩ := ((hex f' g' hc' m).2.2 y).1 ⟨h1, h2⟩
    have hd : d f g hc m (pull R (pullback.map f g f' g' u v p hu hv) F m c) = 0 := by
      rw [← hnat f g f' g' p u v hu hv hc hc' m c]; exact hy
    obtain ⟨a, b, hab⟩ := ((hex f g hc m).2.1 _).1 hd
    obtain ⟨a', rfl⟩ := (hU m).2 a
    obtain ⟨b', rfl⟩ := (hV m).2 b
    have hc1 : c = pull R (pullback.fst f' g') F m a' - pull R (pullback.snd f' g') F m b' := by
      apply (hW m).1
      rw [hab, map_sub, cfst, csnd]
    exact ((hex f' g' hc' m).2.1 c).2 ⟨a', b', hc1⟩
  · intro z
    obtain ⟨a', ha'⟩ := (hU (m + 1)).2 (pull R f F (m + 1) z)
    obtain ⟨b', hb'⟩ := (hV (m + 1)).2 (pull R g F (m + 1) z)
    have hab : pull R (pullback.fst f' g') F (m + 1) a' = pull R (pullback.snd f' g') F (m + 1) b' := by
      apply (hW (m + 1)).1
      rw [cfst, csnd, ha', hb', hcond]
    obtain ⟨y, hy1, hy2⟩ := ((hex f' g' hc' (m + 1)).1 a' b').1 hab
    have k1 : pull R f F (m + 1) (z - pull R p F (m + 1) y) = 0 := by
      rw [map_sub, cf, hy1, ha', sub_self]
    have k2 : pull R g F (m + 1) (z - pull R p F (m + 1) y) = 0 := by
      rw [map_sub, cg, hy2, hb', sub_self]
    obtain ⟨c, hc0⟩ := ((hex f g hc m).2.2 _).1 ⟨k1, k2⟩
    obtain ⟨c', rfl⟩ := (hW m).2 c
    refine ⟨y + d f' g' hc' m c', ?_⟩
    rw [map_add (f := _), hnat f g f' g' p u v hu hv hc hc' m c', hc0]
    abel

end GlobalTheory.MayerVietorisEqv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MayerVietorisEquivalenceOfCoverStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mayerVietoris_equivalence_of_cover : GlobalTheory.EtC.A4 := by
  first | (exact @GlobalTheory.MayerVietorisEqv.a4) | (exact GlobalTheory.MayerVietorisEqv.a4) | (intros; apply GlobalTheory.MayerVietorisEqv.a4  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeGeneratorTopForm
open GlobalTheory GlobalTheory.TopForm

namespace GlobalTheory

open KaehlerDifferential IsLocalRing Module

theorem isFreeGen_dForm_uniformiser_cons : ∀ (k V : Type) [Field k] [CharZero k] [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (α : k →+* V) (n : ℕ) (t : V) (w : Fin n → V), α.EssFiniteType →
    Irreducible t → Nonempty (Module.Basis (Fin (n + 1)) V (Omega α)) →
    (∀ P : MvPolynomial (Fin n) k, P ≠ 0 → IsUnit (MvPolynomial.eval₂ α w P)) →
    IsFreeGen V (dForm α (Fin.cons t w : Fin (n + 1) → V)) := by
  intro k V _ _ _ _ _ α n t w hft ht hb₀ hw
  obtain ⟨b₀⟩ := hb₀
  letI := α.toAlgebra
  haveI : Algebra.EssFiniteType k V := hft
  haveI : Algebra.FormallySmooth k V := formallySmooth_of_isRegularLocalRing_of_perfectField k V
  let κ := ResidueField V
  let wb : Fin n → κ := fun i => algebraMap V κ (w i)

  have hai : AlgebraicIndependent k wb := by
    rw [algebraicIndependent_iff]
    intro P hP
    by_contra hne
    have hu := hw P hne
    have e : MvPolynomial.aeval wb P = algebraMap V κ (MvPolynomial.eval₂ α w P) := by
      rw [show wb = algebraMap V κ ∘ w from rfl, MvPolynomial.aeval_algebraMap_apply]
      rfl
    rw [e] at hP
    exact (residue_ne_zero_iff_isUnit _).mpr hu hP

  have hdli : LinearIndependent κ fun i => D k κ (wb i) := by
    have hs : AlgebraicIndepOn k id (Set.range wb) := by
      exact (algebraicIndependent_subtype_range hai.injective).mpr hai
    obtain ⟨s, hsub, hs⟩ := exists_isTranscendenceBasis_superset hs
    haveI := hs.isAlgebraic_field
    haveI : Algebra.IsSeparable (IntermediateField.adjoin k (Set.range ((↑) : s → κ))) κ :=
      Algebra.IsAlgebraic.isSeparable_of_perfectField
    obtain ⟨b, hb⟩ := exists_basis_kaehler_of_algebraicIndependent hs.1
    let ι : Fin n → s := fun i => ⟨wb i, hsub (Set.mem_range_self i)⟩
    have hι : Function.Injective ι := fun i j h => hai.injective (congrArg Subtype.val h)
    have := b.linearIndependent.comp ι hι
    convert this using 1
    funext i
    simp [ι, hb]
  have ht₀ : algebraMap V κ t = 0 := (residue_eq_zero_iff t).mpr (by
    rw [ht.maximalIdeal_eq]
    exact Ideal.mem_span_singleton_self t)
  let z : Fin (n + 1) → V := Fin.cons t w
  have hli : LinearIndependent κ (TensorProduct.mk V κ Ω[V⁄k] 1 ∘ fun i => D k V (z i)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_succ] at hg
    simp only [Function.comp_apply, TensorProduct.mk_apply, z, Fin.cons_zero, Fin.cons_succ] at hg
    have hφ := congrArg (mapBaseChange k V κ) hg
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_add (f := _), map_sum, map_smul, map_zero, mapBaseChange_tmul, one_smul, map_D, ht₀,
      Derivation.map_zero, smul_zero, zero_add] at hφ
    have hs : ∀ i : Fin n, g i.succ = 0 :=
      Fintype.linearIndependent_iff.mp hdli (fun i => g i.succ) hφ
    simp only [hs, zero_smul, Finset.sum_const_zero, add_zero] at hg
    have h0 : g 0 = 0 := by
      rcases smul_eq_zero.mp hg with h | h
      · exact h
      · exact absurd h (one_tmul_D_ne_zero k ht)
    intro i
    exact Fin.cases h0 hs i
  have hsp := hli.span_eq_top_of_card_eq_finrank' (by
    rw [Fintype.card_fin, Module.finrank_eq_card_basis (b₀.baseChange κ), Fintype.card_fin])
  haveI : Module.Free V Ω[V⁄k] := Module.Free.of_basis b₀
  haveI : Module.Finite V Ω[V⁄k] := Module.Finite.of_basis b₀
  haveI : Module.FinitePresentation V Ω[V⁄k] := Module.finitePresentation_of_finite V _
  obtain ⟨b, hb⟩ := Module.exists_basis_of_basis_baseChange (R := V) (fun i => D k V (z i)) hli hsp
    (Module.Flat.rTensor_preserves_injective_linearMap (maximalIdeal V).subtype
      Subtype.val_injective)
  exact isFreeGen_dForm z b hb

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KrullDimQuotientMinimalPrimeOverL
namespace GlobalTheory

universe u

theorem trdeg_quotient_eq_of_mem_minimalPrimes_span (R : Type u) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] (k : Type u) [Field k] [Algebra R k]
    (hk : Function.Surjective (algebraMap R k)) {ϖ : R} (hϖ0 : ϖ ≠ 0)
    (hker : RingHom.ker (algebraMap R k) = Ideal.span {ϖ})
    {A : Type u} [CommRing A] [IsDomain A] [Algebra R A] [Algebra.FiniteType R A]
    [FaithfulSMul R A] {q : Ideal A}
    (hq : q ∈ (Ideal.span {algebraMap R A ϖ}).minimalPrimes)
    [Algebra k (A ⧸ q)] [IsScalarTower R k (A ⧸ q)] :
    Algebra.trdeg k (A ⧸ q) = Algebra.trdeg R A := by
  have hqp := hq.1.1
  have : Algebra.FiniteType k (A ⧸ q) := .of_restrictScalars_finiteType R k _
  obtain ⟨s, g, hg, hint⟩ := exists_integral_inj_algHom_of_fg k (A ⧸ q)
  choose x hx using fun i : Fin s ↦ Ideal.Quotient.mk_surjective (g (MvPolynomial.X i))
  let φ : (MvPolynomial (Fin s) R) →ₐ[R] A := MvPolynomial.aeval x
  have hφ (r : (MvPolynomial (Fin s) R)) :
      Ideal.Quotient.mk q (φ r) = g (MvPolynomial.map (algebraMap R k) r) := by
    have : (Ideal.Quotient.mk q).comp φ.toRingHom =
        g.toRingHom.comp (MvPolynomial.map (algebraMap R k)) := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp only [φ, AlgHom.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe,
          Function.comp_apply, MvPolynomial.algHom_C, MvPolynomial.map_C]
        rw [← IsScalarTower.algebraMap_apply]
        rfl
      · intro i
        simp [φ, hx]
    exact congr($this r)
  have hmem (r : (MvPolynomial (Fin s) R)) : φ r ∈ q ↔ MvPolynomial.C ϖ ∣ r := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, hφ, map_eq_zero_iff g hg, ← RingHom.mem_ker,
      MvPolynomial.ker_map, hker, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
  have hϖA : algebraMap R A ϖ ≠ 0 := by
    intro h
    exact hϖ0 ((FaithfulSMul.algebraMap_injective R A) (h.trans (map_zero _).symm))
  have hinj : Function.Injective φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro r hr
    by_contra hr0
    have hnu : ¬ IsUnit (MvPolynomial.C ϖ : (MvPolynomial (Fin s) R)) := fun h ↦ hqp.ne_top <|
      Ideal.eq_top_of_isUnit_mem _ ((hmem _).mpr dvd_rfl) (h.map φ)
    obtain ⟨n, a, ha, rfl⟩ := WfDvdMonoid.max_power_factor' hr0 hnu
    rw [map_mul, map_pow, MvPolynomial.algHom_C, mul_eq_zero] at hr
    rcases hr with hr | hr
    · exact hϖA (pow_eq_zero_iff'.mp hr).1
    · exact ha ((hmem a).mp (hr ▸ q.zero_mem))
  let := φ.toRingHom.toAlgebra
  have : IsScalarTower R (MvPolynomial (Fin s) R) A :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (φ.commutes x).symm
  have : FaithfulSMul (MvPolynomial (Fin s) R) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  have : Algebra.FiniteType (MvPolynomial (Fin s) R) A :=
    .of_restrictScalars_finiteType R (MvPolynomial (Fin s) R) A
  let := g.toRingHom.toAlgebra
  have : IsScalarTower k (MvPolynomial (Fin s) k) (A ⧸ q) :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (g.commutes x).symm
  have : FaithfulSMul (MvPolynomial (Fin s) k) (A ⧸ q) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hg
  have : Algebra.IsIntegral (MvPolynomial (Fin s) k) (A ⧸ q) := ⟨hint⟩
  have : Algebra.QuasiFiniteAt (MvPolynomial (Fin s) R) q := by
    refine quasiFiniteAt_of_isolated (MvPolynomial (Fin s) R) A q
      (fun q' hq' h hle ↦ ?_) (fun q' hq' h hle ↦ ?_)
    · refine hle.antisymm (hq.2 ⟨hq', ?_⟩ hle)
      rw [Ideal.span_singleton_le_iff_mem]
      have : (MvPolynomial.C ϖ : (MvPolynomial (Fin s) R)) ∈ q'.under (MvPolynomial (Fin s) R) :=
        h.ge ((hmem _).mpr dvd_rfl)
      have : φ (MvPolynomial.C ϖ) ∈ q' := this
      simpa using this
    · have : q'.map (Ideal.Quotient.mk q) = ⊥ := by
        refine Ideal.eq_bot_of_comap_eq_bot (R := MvPolynomial (Fin s) k) (eq_bot_iff.mpr ?_)
        intro y hy
        obtain ⟨r, rfl⟩ := MvPolynomial.map_surjective _ hk y
        have hy : g (MvPolynomial.map (algebraMap R k) r) ∈ q'.map (Ideal.Quotient.mk q) := hy
        rw [← hφ, Ideal.mem_quotient_iff_mem hle] at hy
        have : φ r ∈ q := h.le (show r ∈ q'.under (MvPolynomial (Fin s) R) from hy)
        rw [← Ideal.Quotient.eq_zero_iff_mem, hφ, map_eq_zero_iff g hg] at this
        exact this
      rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker] at this
      exact this.antisymm hle
  have := isAlgebraic_of_quasiFiniteAt (MvPolynomial (Fin s) R) A q
  rw [trdeg_eq_of_isAlgebraic_top k (MvPolynomial (Fin s) k),
    trdeg_eq_of_isAlgebraic_top R (MvPolynomial (Fin s) R) A,
    MvPolynomial.trdeg_of_isDomain, MvPolynomial.trdeg_of_isDomain]

theorem ringKrullDim_quotient_eq_trdeg_of_mem_minimalPrimes_natPrime (A : Type) [CommRing A]
    [IsDomain A] [CharZero A] [Algebra.FiniteType ℤ A] (l : ℕ) [Fact l.Prime] (q : Ideal A)
    [q.IsPrime] (hq : q ∈ (Ideal.span {(l : A)}).minimalPrimes) (d : ℕ)
    (hd : Algebra.trdeg ℤ A = d) : ringKrullDim (A ⧸ q) = d := by
  have hk : Function.Surjective (algebraMap ℤ (ZMod l)) := ZMod.intCast_surjective
  have hker : RingHom.ker (algebraMap ℤ (ZMod l)) = Ideal.span {(l : ℤ)} := by
    rw [algebraMap_int_eq]; exact ZMod.ker_intCastRingHom l
  have hl0 : (l : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have : FaithfulSMul ℤ A := (faithfulSMul_iff_algebraMap_injective _ _).mpr
    (by rw [algebraMap_int_eq]; exact Int.cast_injective)
  have hq' : q ∈ (Ideal.span {algebraMap ℤ A (l : ℤ)}).minimalPrimes := by simpa using hq
  have hlq : (l : A) ∈ q := hq.1.2 (Ideal.mem_span_singleton_self _)
  have hle : RingHom.ker (algebraMap ℤ (ZMod l)) ≤ RingHom.ker (algebraMap ℤ (A ⧸ q)) := by
    rw [hker, Ideal.span_singleton_le_iff_mem, RingHom.mem_ker,
      IsScalarTower.algebraMap_apply ℤ A (A ⧸ q), Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem]
    simpa using hlq
  let := ((algebraMap ℤ (ZMod l)).liftOfSurjective hk ⟨_, hle⟩).toAlgebra
  have : IsScalarTower ℤ (ZMod l) (A ⧸ q) := IsScalarTower.of_algebraMap_eq fun x ↦
    (RingHom.liftOfSurjective_comp_apply _ hk ⟨_, hle⟩ x).symm
  have : Algebra.FiniteType (ZMod l) (A ⧸ q) := .of_restrictScalars_finiteType ℤ _ _
  refine ringKrullDim_eq_of_trdeg_eq (ZMod l) _ ?_
  rw [trdeg_quotient_eq_of_mem_minimalPrimes_span ℤ (ZMod l) hk hl0 hker hq', hd]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiscreteSpaceCocycleVanishingPos
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiscreteSpaceCocycleVanishingPos
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.DiscRep
variable {R : Type} [CommRing R]

def asum (m : ℕ) : ℤ := ∑ i : Fin (m + 1), (-1 : ℤ) ^ (i : ℕ)

theorem asum_succ (k : ℕ) : asum (k + 1) = asum k + (-1) ^ (k + 1) := by
  rw [asum, Fin.sum_univ_castSucc]
  simp [asum]

theorem asum_even (m : ℕ) : asum m = if Even m then 1 else 0 := by
  induction m with
  | zero => simp [asum]
  | succ k ih =>
    rw [asum_succ, ih]
    rcases Nat.even_or_odd k with h | h
    · have h' : ¬ Even (k + 1) := by simpa [Nat.even_add_one] using h
      simp [h, h', (h.add_one).neg_one_pow]
    · have h' : Even (k + 1) := h.add_one
      have h'' : ¬ Even k := Nat.not_even_iff_odd.mpr h
      simp [h', h'', h'.neg_one_pow]

variable (R) in
abbrev C (F : PSh) : ChainComplex (Shv R) ℕ := (chainsN R).obj (disc.obj F)

theorem C_d (F : PSh) (p : ℕ) :
    (C R F).d (p + 1) p = (asum (p + 1)) • (𝟙 ((free R).obj F) : (C R F).X (p + 1) ⟶ (C R F).X p) := by
  rw [show (C R F).d (p + 1) p = ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map ((disc.obj F).δ i) from
    AlgebraicTopology.alternatingFaceMapComplex_obj_d _ p]
  simp only [asum, Finset.sum_smul, SimplicialObject.δ]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (disc.obj F).map (SimplexCategory.δ i).op = 𝟙 F from rfl]
  exact congrArg (fun f => (-1 : ℤ) ^ (i : ℕ) • f) ((free R).map_id F)

def idX (F : PSh) (i j : ℕ) : (C R F).X i ⟶ (C R F).X j := 𝟙 ((free R).obj F)

theorem idX_comp (F : PSh) (i j k : ℕ) : idX (R := R) F i j ≫ idX F j k = idX F i k := Category.id_comp _

theorem C_d' (F : PSh) (p : ℕ) : (C R F).d (p + 1) p = (asum (p + 1)) • idX F (p + 1) p := C_d F p

def piC (F : PSh) : C R F ⟶ C R F where
  f i := if i = 0 then 𝟙 _ else 0
  comm' i j hij := by
    obtain rfl : i = j + 1 := hij.symm
    rw [if_neg (Nat.succ_ne_zero j), zero_comp, C_d']
    rcases j with _ | j
    · rw [asum_even, if_neg (by decide), zero_smul, zero_comp]
    · rw [if_neg (Nat.succ_ne_zero j), comp_zero]

def htpC (F : PSh) : Homotopy (𝟙 (C R F)) (piC F) where
  hom i j := if i + 1 = j ∧ Odd i then idX F i j else 0
  zero i j w := by
    rw [if_neg]
    rintro ⟨h, -⟩
    exact w h
  comm i := by
    rcases i with _ | k
    · rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex, C_d']
      simp [piC, asum_even]
    · rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex, C_d', C_d']
      simp only [piC, if_neg (Nat.succ_ne_zero k), add_zero, true_and, asum_even]
      rcases Nat.even_or_odd k with h | h
      · have h1 : ¬ Even (k + 1) := by simpa [Nat.even_add_one] using h
        have h2 : Even (k + 1 + 1) := h1 |> fun _ => (h.add_one).add_one
        have h3 : Odd (k + 1) := h.add_one
        have h4 : ¬ Odd k := Nat.not_odd_iff_even.mpr h
        simp only [h1, h2, h3, h4, if_true, if_false, one_smul, zero_smul, comp_zero, zero_comp, zero_add, idX_comp]
        rfl
      · have h1 : Even (k + 1) := h.add_one
        have h3 : ¬ Odd (k + 1) := Nat.not_odd_iff_even.mpr h1
        simp only [h1, h, h3, if_true, if_false, one_smul, comp_zero, zero_comp, add_zero, idX_comp]
        rfl

def piZ (F : PSh) : (chains R).obj (disc.obj F) ⟶ (chains R).obj (disc.obj F) :=
  HomologicalComplex.extendMap (piC F) ComplexShape.embeddingDownNat

def htpZ (F : PSh) : Homotopy (𝟙 ((chains R).obj (disc.obj F))) (piZ F) :=
  (Homotopy.ofEq (HomologicalComplex.extendMap_id (C R F) ComplexShape.embeddingDownNat).symm).trans
    ((htpC F).extend ComplexShape.embeddingDownNat)

theorem piZ_f (F : PSh) (p : ℕ) (hp : 0 < p) : (piZ (R := R) F).f (-(p : ℤ)) = 0 := by
  have h1 := HomologicalComplex.extendMap_f (piC (R := R) F) ComplexShape.embeddingDownNat (i := p) (i' := -(p : ℤ)) rfl
  simp only [piC, if_neg hp.ne', zero_comp, comp_zero] at h1
  exact h1

end GlobalTheory.EtC.DiscRep


open GlobalTheory.EtC.DiscRep in
theorem GlobalTheory.EtC.discRep : ∀ (R : Type) [CommRing R] (F : PSh) (I : Cx R) (n : ℤ)
    (x : CohomologyClass ((chains R).obj (disc.obj F)) I n), ∃ α : Cocycle ((chains R).obj (disc.obj F)) I n,
      CohomologyClass.mk α = x ∧ ∀ (p : ℕ), 0 < p → ∀ (s : ℤ) (h : -(p : ℤ) + n = s), α.1.v (-(p : ℤ)) s h = 0 := by
  intro R _ F I n x
  obtain ⟨α, rfl⟩ := x.mk_surjective
  refine ⟨zcomp (Cocycle.ofHom (piZ F)) α (zero_add n), ?_, ?_⟩
  · rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
      mem_coboundaries_iff _ (n - 1) (by omega)]
    refine ⟨-(n.negOnePow • (Cochain.ofHomotopy (htpZ F)).comp α.1 (by omega)), ?_⟩
    rw [δ_neg, δ_units_smul, δ_comp _ _ _ 0 (n + 1) n (by omega) (by omega) (by omega), Cocycle.δ_eq_zero, δ_ofHomotopy]
    ext p q hpq
    simp [zcomp, Cochain.comp_v _ _ (zero_add n) p p q (add_zero p) hpq, smul_smul]
  · intro p hp s h
    simp [zcomp, Cochain.comp_v _ _ (zero_add n) _ _ s (add_zero _) h, piZ_f F p hp]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiscreteSpaceCocycleVanishingPosStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_discreteSpace_cocycle_vanishing_pos : ∀ (R : Type) [CommRing R] (F : PSh) (I : Cx R) (n : ℤ) (x : CohomologyClass ((chains R).obj (disc.obj F)) I n), ∃ α : Cocycle ((chains R).obj (disc.obj F)) I n, CohomologyClass.mk α = x ∧ ∀ (p : ℕ), 0 < p → ∀ (s : ℤ) (h : -(p : ℤ) + n = s), α.1.v (-(p : ℤ)) s h = 0 := by
  first | (exact @GlobalTheory.EtC.discRep) | (exact GlobalTheory.EtC.discRep) | (intros; apply GlobalTheory.EtC.discRep  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EpsZeroPtEpsScalePt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.GrpTangentPt

noncomputable section

namespace GlobalTheory.TanPtMod

variable {S : Scheme.{0}} {k : Type} [CommRing k] (x : Sp k ⟶ S)

def epsZeroPt : Over.mk x ⟶ epsPtR x :=
  Over.homMk (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) (by
    change Spec.map _ ≫ Spec.map _ ≫ x = x
    rw [← Category.assoc, ← Spec.map_comp]
    conv_rhs => rw [← Category.id_comp x]
    congr 1
    rw [← Spec.map_id]
    congr 1)

@[reassoc]
lemma epsZeroPt_epsScalePt (c : k) : epsZeroPt x ≫ epsScalePt x c = epsZeroPt x := by
  ext1
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun z => ?_)
  simp

lemma epsScalePt_mul (a b : k) : epsScalePt x a ≫ epsScalePt x b = epsScalePt x (a * b) := by
  rw [sqZeroMapPt_comp]
  congr 1
  refine LinearMap.ext_ring ?_
  simp

variable (G : Over S) [GrpObj G] [IsCommMonObj G]

def tanSub : Subgroup (epsPtR x ⟶ G) where
  carrier := {w | epsZeroPt x ≫ w = 1}
  one_mem' := comp_one _
  mul_mem' {a b} ha hb := by
    change epsZeroPt x ≫ (a * b) = 1
    rw [comp_mul, ha, hb, _root_.one_mul]
  inv_mem' {a} ha := by
    change epsZeroPt x ≫ a⁻¹ = 1
    rw [GrpObj.comp_inv, ha, _root_.inv_one]

lemma mem_tanSub_iff (w : epsPtR x ⟶ G) :
    w ∈ tanSub x G ↔ spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ w.left = (1 : Over.mk x ⟶ G).left := by
  change epsZeroPt x ≫ w = 1 ↔ _
  exact ⟨fun h => congrArg Over.Hom.left h, fun h => Over.OverMorphism.ext h⟩

abbrev Tan : Type := Additive (tanSub x G)

variable {x G}

def Tan.hom (v : Tan x G) : epsPtR x ⟶ G := (Additive.toMul v : tanSub x G).1

def Tan.mk (w : epsPtR x ⟶ G) (hw : w ∈ tanSub x G) : Tan x G := Additive.ofMul ⟨w, hw⟩

lemma Tan.hom_mem (v : Tan x G) : v.hom ∈ tanSub x G := (Additive.toMul v : tanSub x G).2

@[ext] lemma Tan.ext {v w : Tan x G} (h : v.hom = w.hom) : v = w :=
  Additive.toMul.injective (Subtype.ext h)

def Tan.homAdd : Tan x G →+ Additive (epsPtR x ⟶ G) := (tanSub x G).subtype.toAdditive

lemma Tan.hom_sum {I : Type} (s : Finset I) (v : I → Tan x G) : (∑ i ∈ s, v i).hom = ∏ i ∈ s, (v i).hom := by
  have := map_sum (Tan.homAdd (x := x) (G := G)) v s
  exact congrArg Additive.toMul this

instance : Module k (Tan x G) where
  smul c v := Tan.mk (epsScalePt x c ≫ v.hom) (by
    change epsZeroPt x ≫ _ = 1
    rw [epsZeroPt_epsScalePt_assoc]; exact v.hom_mem)
  one_smul v := Tan.ext (by
    change epsScalePt x 1 ≫ v.hom = _
    rw [epsScalePt_one, Category.id_comp])
  mul_smul a b v := Tan.ext (by
    change epsScalePt x (a * b) ≫ v.hom = epsScalePt x a ≫ epsScalePt x b ≫ v.hom
    rw [← Category.assoc, epsScalePt_mul])
  smul_zero c := Tan.ext (comp_one _)
  smul_add c v w := Tan.ext (comp_mul _ _ _)
  add_smul a b v := Tan.ext (epsScalePt_add_comp x a b ((mem_tanSub_iff x G _).mp v.hom_mem))
  zero_smul v := Tan.ext (epsScalePt_zero_comp x ((mem_tanSub_iff x G _).mp v.hom_mem))

@[simp] lemma Tan.hom_smul (c : k) (v : Tan x G) : (c • v).hom = epsScalePt x c ≫ v.hom := rfl

def Tan.map (f : G ⟶ G) [IsMonHom f] : Tan x G →ₗ[k] Tan x G where
  toFun v := Tan.mk (v.hom ≫ f) (by
    change epsZeroPt x ≫ _ = 1
    rw [← Category.assoc, v.hom_mem, one_comp])
  map_add' v w := Tan.ext (mul_comp _ _ _)
  map_smul' c v := Tan.ext (Category.assoc _ _ _)

def actEnd {O : Type} [Ring O] (a : OActN O G) : O →+* Module.End k (Tan x G) where
  toFun b := haveI := a.hom b; Tan.map (a.act b)
  map_one' := by
    refine LinearMap.ext fun v => Tan.ext ?_
    change v.hom ≫ a.act 1 = v.hom
    rw [a.one, Category.comp_id]
  map_mul' b c := by
    refine LinearMap.ext fun v => Tan.ext ?_
    change v.hom ≫ a.act (b * c) = (v.hom ≫ a.act c) ≫ a.act b
    rw [a.mul, Category.assoc]
  map_zero' := by
    have h : a.act 0 = 1 := by
      have := a.add 0 0
      rw [add_zero] at this
      exact mul_left_cancel (this.symm.trans (_root_.mul_one _).symm)
    refine LinearMap.ext fun v => Tan.ext ?_
    change v.hom ≫ a.act 0 = 1
    rw [h, comp_one]
  map_add' b c := by
    refine LinearMap.ext fun v => Tan.ext ?_
    change v.hom ≫ a.act (b + c) = (v.hom ≫ a.act b) * (v.hom ≫ a.act c)
    rw [a.add, comp_mul]

end GlobalTheory.TanPtMod
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IwahoriRegularSplit
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitDiagOfLower
open GlobalTheory.UnitLemma Polynomial

noncomputable section

namespace GlobalTheory.IwahoriRoots

open IsDedekindDomain

section Val

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {E : Type} [Field E]
  [Algebra O E] [IsFractionRing O E]

theorem valuation_unif (ϖ : O) (hϖ : Irreducible ϖ) :
    (IsDiscreteValuationRing.maximalIdeal O).valuation E (algebraMap O E ϖ) = WithZero.exp (-1 : ℤ) := by
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_singleton _ hϖ.ne_zero
    ((IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ)

theorem valuation_of_isUnit {u : O} (hu : IsUnit u) :
    (IsDiscreteValuationRing.maximalIdeal O).valuation E (algebraMap O E u) = 1 := by
  obtain ⟨u, rfl⟩ := hu
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  set v := IsDiscreteValuationRing.maximalIdeal O
  have h1 := v.intValuation_le_one (u : O)
  have h2 := v.intValuation_le_one ((u⁻¹ : Oˣ) : O)
  have h3 : v.intValuation (u : O) * v.intValuation ((u⁻¹ : Oˣ) : O) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  refine le_antisymm h1 ?_
  calc (1 : WithZero (Multiplicative ℤ)) = v.intValuation (u : O) * v.intValuation ((u⁻¹ : Oˣ) : O) := h3.symm
    _ ≤ v.intValuation (u : O) * 1 := by gcongr
    _ = v.intValuation (u : O) := mul_one _

end Val

theorem isUnit_diag_of_lower {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (x : GL (Fin n) O)
    (hx : ∀ i j, j < i → (x : Matrix (Fin n) (Fin n) O) i j ∈ IsLocalRing.maximalIdeal O)
    (i : Fin n) : IsUnit ((x : Matrix (Fin n) (Fin n) O) i i) := by
  have h1 : ((x : Matrix (Fin n) (Fin n) O).map (IsLocalRing.residue O)).BlockTriangular id := by
    intro a b hab
    simp only [Matrix.map_apply]
    exact (IsLocalRing.residue_eq_zero_iff _).2 (hx a b hab)
  have h2 : IsUnit ((x : Matrix (Fin n) (Fin n) O).map (IsLocalRing.residue O)).det := by
    have e : ((x : Matrix (Fin n) (Fin n) O).map (IsLocalRing.residue O)).det =
        IsLocalRing.residue O (x : Matrix (Fin n) (Fin n) O).det := (RingHom.map_det _ _).symm
    rw [e]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 x.isUnit).map _
  rw [Matrix.det_of_upperTriangular h1] at h2
  have h3 := isUnit_of_dvd_unit (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)) h2
  simp only [Matrix.map_apply] at h3
  exact isUnit_of_map_unit (IsLocalRing.residue O) _ h3

theorem iwahori_roots : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] (E : Type) [Field E] [Algebra O E] [IsFractionRing O E]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (ϖ : O), Irreducible ϖ →
    ∀ (n : ℕ) (a : Fin n → ℤ), StrictAnti a → ∀ x y : GL (Fin n) O,
    (∀ i j, j < i → (x : Matrix (Fin n) (Fin n) O) i j ∈ IsLocalRing.maximalIdeal O) →
    (∀ i j, j < i → (y : Matrix (Fin n) (Fin n) O) i j ∈ IsLocalRing.maximalIdeal O) →
    ∃ r : Fin n → E, (∀ i, r i ≠ 0 ∧ val O (r i) = a i) ∧
      ((x : Matrix (Fin n) (Fin n) O).map (algebraMap O E) *
        Matrix.diagonal (fun i => algebraMap O E ϖ ^ a i) *
        (y : Matrix (Fin n) (Fin n) O).map (algebraMap O E)).charpoly = ∏ i, (X - C (r i)) := by
  intro O _ _ _ _ E _ _ _ _ ϖ hϖ n a ha x y hx hy
  have hspan := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  have hm : ϖ ∈ IsLocalRing.maximalIdeal O := by rw [hspan]; exact Ideal.mem_span_singleton_self ϖ
  haveI : IsAdicComplete (Ideal.span {ϖ}) O := by rw [← hspan]; infer_instance
  have hinj : Function.Injective (algebraMap O E) := IsFractionRing.injective O E
  have hϖ0 : algebraMap O E ϖ ≠ 0 := (map_ne_zero_iff _ hinj).2 hϖ.ne_zero
  obtain ⟨N, hNa⟩ : ∃ N : ℤ, ∀ i, N ≤ a i := by
    obtain ⟨N, hN⟩ := (Set.finite_range a).bddBelow
    exact ⟨N, fun i => hN ⟨i, rfl⟩⟩
  let b : Fin n → ℕ := fun i => (a i - N).toNat
  have hab : ∀ i, a i = N + b i := fun i => by
    have := hNa i
    simp only [b]
    omega
  have hb : StrictAnti b := fun i j h => by
    have := ha h
    rw [hab, hab] at this
    omega
  have hdvd : ∀ z : O, z ∈ IsLocalRing.maximalIdeal O → ϖ ∣ z := fun z hz => by
    rw [hspan] at hz
    exact Ideal.mem_span_singleton.1 hz
  set G : Matrix (Fin n) (Fin n) O :=
    (x : Matrix (Fin n) (Fin n) O) * Matrix.diagonal (fun i => ϖ ^ b i) * y with hG
  have hroot := GlobalTheory.IwahoriEigen.exists_root_of_coeff ϖ hm hb G.charpoly
    (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]) (fun j hj => by
      have := GlobalTheory.IwahoriNewtonTest.intersectionNumber_baseChange O ϖ hm n b hb x y (isUnit_diag_of_lower x hx)
        (isUnit_diag_of_lower y hy) (fun i j h => hdvd _ (hx i j h)) (fun i j h => hdvd _ (hy i j h))
        (n - j) (Nat.sub_le _ _)
      rwa [Nat.sub_sub_self hj] at this)
  choose z hz hzr using hroot
  set M : Matrix (Fin n) (Fin n) E := (x : Matrix (Fin n) (Fin n) O).map (algebraMap O E) *
    Matrix.diagonal (fun i => algebraMap O E ϖ ^ a i) *
    (y : Matrix (Fin n) (Fin n) O).map (algebraMap O E) with hM
  have hMG : M = algebraMap O E ϖ ^ N • G.map (algebraMap O E) := by
    have : Matrix.diagonal (fun i => algebraMap O E ϖ ^ a i) =
        algebraMap O E ϖ ^ N • (Matrix.diagonal (fun i => ϖ ^ b i)).map (algebraMap O E) := by
      rw [Matrix.diagonal_map (map_zero _), ← Matrix.diagonal_smul]
      congr 1
      funext i
      rw [hab, zpow_add₀ hϖ0]
      simp
    rw [hM, this, hG, Matrix.map_mul, Matrix.map_mul, Matrix.mul_smul, Matrix.smul_mul]
  let r : Fin n → E := fun i => algebraMap O E ϖ ^ N * algebraMap O E (ϖ ^ b i * z i)
  have hr0 : ∀ i, r i ≠ 0 := fun i =>
    mul_ne_zero (zpow_ne_zero _ hϖ0) ((map_ne_zero_iff _ hinj).2
      (mul_ne_zero (pow_ne_zero _ hϖ.ne_zero) (hz i).ne_zero))
  have hv : ∀ i, (IsDiscreteValuationRing.maximalIdeal O).valuation E (r i) =
      WithZero.exp (-(a i)) := fun i => by
    simp only [r, map_mul, map_pow, map_zpow₀, valuation_unif ϖ hϖ, valuation_of_isUnit (hz i), mul_one]
    rw [← WithZero.exp_zsmul, ← WithZero.exp_nsmul, ← WithZero.exp_add, hab]
    congr 1
    simp
    ring
  have hval : ∀ i, val O (r i) = a i := fun i => by
    simp only [val, hv i, WithZero.log_exp, neg_neg]
  have hrinj : Function.Injective r := fun i j h => by
    have h1 := hval i
    rw [h, hval j] at h1
    exact ha.injective h1.symm
  have hrt : ∀ i, M.charpoly.IsRoot (r i) := fun i => by
    have h1 : ((G.map (algebraMap O E)).charpoly).IsRoot (algebraMap O E (ϖ ^ b i * z i)) := by
      rw [Matrix.charpoly_map]
      exact Polynomial.IsRoot.map (algebraMap O E) (hzr i)
    rw [IsRoot.def, Matrix.eval_charpoly] at h1 ⊢
    have : Matrix.scalar (Fin n) (r i) - M = algebraMap O E ϖ ^ N •
        (Matrix.scalar (Fin n) (algebraMap O E (ϖ ^ b i * z i)) - G.map (algebraMap O E)) := by
      rw [hMG, smul_sub]
      congr 1
      rw [Matrix.scalar_apply, Matrix.scalar_apply, ← Matrix.diagonal_smul]
      rfl
    rw [this, Matrix.det_smul, h1, mul_zero]
  refine ⟨r, fun i => ⟨hr0 i, hval i⟩, ?_⟩
  refine eq_of_monic_of_dvd_of_natDegree_le (monic_prod_X_sub_C _ _) M.charpoly_monic ?_ ?_
  · exact Finset.prod_dvd_of_coprime
      (fun i _ j _ h => pairwise_coprime_X_sub_C hrinj h) fun i _ => dvd_iff_isRoot.2 (hrt i)
  · rw [Matrix.charpoly_natDegree_eq_dim, natDegree_finsetProd_X_sub_C_eq_card]
    simp

end GlobalTheory.IwahoriRoots
end
end

open Polynomial ValuativeRel

namespace GlobalTheory.IwahoriRegular

theorem regular_split : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (ϖ : kˣ),
  ValuativeRel.valuation k (ϖ : k) = ValuativeRel.uniformizer k →
  ∀ ν : Fin N → ℤ, StrictAnti ν → ∀ x ∈ GlobalTheory.SmGL.iwahori k (Fin N), ∀ y ∈ GlobalTheory.SmGL.iwahori k (Fin N),
    let g := x * GlobalTheory.GLDoubling.torusElt k (Fin N) ϖ ν * y
    (g : Matrix (Fin N) (Fin N) k).charpoly.Separable ∧ (g : Matrix (Fin N) (Fin N) k).charpoly.Splits := by
  intro k _ _ _ _ N ϖ hϖ ν hν x hx y hy
  letI := IsTopologicalAddGroup.rightUniformSpace k
  haveI := isUniformAddGroup_of_addCommGroup (G := k)
  have hlt : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  let w : 𝒪[k] := ⟨ϖ, hlt.le⟩
  have hw : Irreducible w := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]
    ext z
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Valuation.Integer.not_isUnit_iff_valuation_lt_one,
      Ideal.mem_span_singleton, (Valuation.integer.integers (valuation k)).dvd_iff_le, ← le_uniformizer_iff, ← hϖ]
    rfl
  obtain ⟨x', hx', rfl⟩ := hx
  obtain ⟨y', hy', rfl⟩ := hy
  have low : ∀ h : GL (Fin N) 𝒪[k], h ∈ (GlobalTheory.SmGL.borel 𝓀[k] (Fin N)).comap
      (Matrix.GeneralLinearGroup.map (n := Fin N) (IsLocalRing.residue 𝒪[k])) →
      ∀ i j, j < i → (h : Matrix (Fin N) (Fin N) 𝒪[k]) i j ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
    intro h hh i j hij
    have := (GlobalTheory.SmGL.mem_borel _).1 hh i j hij
    exact (IsLocalRing.residue_eq_zero_iff _).1 this
  obtain ⟨r, hr, hchar⟩ := GlobalTheory.IwahoriRoots.iwahori_roots 𝒪[k] k w hw N ν hν x' y' (low x' hx') (low y' hy')
  have hinj : Function.Injective r := fun i j h => hν.injective (by rw [← (hr i).2, ← (hr j).2, h])
  have e : ((Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) x' * GlobalTheory.GLDoubling.torusElt k (Fin N) ϖ ν *
      Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) y' : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) =
      (x' : Matrix (Fin N) (Fin N) 𝒪[k]).map (algebraMap 𝒪[k] k) *
        Matrix.diagonal (fun i => algebraMap 𝒪[k] k w ^ ν i) *
        (y' : Matrix (Fin N) (Fin N) 𝒪[k]).map (algebraMap 𝒪[k] k) := by
    rw [Units.val_mul, Units.val_mul, GlobalTheory.GLDoubling.val_torusElt]
    rfl
  show Separable (Matrix.charpoly _) ∧ Splits (Matrix.charpoly _)
  rw [e, hchar]
  exact ⟨separable_prod_X_sub_C_iff.2 hinj, Polynomial.Splits.prod fun i _ => Polynomial.Splits.X_sub_C _⟩

end GlobalTheory.IwahoriRegular
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdmissibleAdelicMatrixFamilyOrdersFinite
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdmissibleAdelicMatrixFamilyOrdersFinite
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.Nef

theorem lineFin : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ (n : ℕ) (g : Place k F → Matrix (Fin n) (Fin n) F), admitted g → {v : Place k F | ord v (g v).det ≠ 0}.Finite ∧ ∀ w : Fin n → F, w ≠ 0 → {v : Place k F | nrm v ((g v).mulVec w) ≠ 1}.Finite ∧ ∀ v, (g v).mulVec w ≠ 0 := by
  intro k F _ _ _ _ _ hFF n g hg
  obtain ⟨hdet, hfin⟩ := hg
  refine ⟨hfin.subset ?_, fun w hw => ⟨?_, fun v h => hw (Matrix.eq_zero_of_mulVec_eq_zero (hdet v) h)⟩⟩
  · intro v hv hu
    apply hv
    simp [ord, hu.2]
  · let S : Set (Place k F) := {v | ¬ Unimod v (g v)} ∪
      ⋃ i ∈ {i : Fin n | w i ≠ 0}, {v : Place k F | v.1 (w i) ≠ 1}
    have hS : S.Finite := hfin.union (Set.Finite.biUnion (Set.toFinite _)
      fun i hi => ((GlobalTheory.T.functionField_finite_support_sum_order_eq_zero k F hFF (w i) hi).1))
    refine hS.subset fun v hv => ?_
    by_contra hvS
    simp only [S, Set.mem_union, Set.mem_setOf_eq, Set.mem_iUnion, not_or, not_not, not_exists] at hvS
    obtain ⟨hu, hw1⟩ := hvS
    apply hv
    rw [(((GlobalTheory.T.functionFieldPlaceOrder_calculus k F v).2.2.2.2.2.2.2.2.1) n (g v) w hu)]
    obtain ⟨i0, hi0⟩ : ∃ i, w i ≠ 0 := by
      by_contra h; push_neg at h; exact hw (funext h)
    have h1 : ∀ i, v.1 (w i) ≤ 1 := by
      intro i
      by_cases hi : w i = 0
      · simp [hi]
      · exact le_of_eq (hw1 i hi)
    apply le_antisymm
    · exact Finset.sup_le fun i _ => h1 i
    · have := Finset.le_sup (f := fun i => v.1 (w i)) (Finset.mem_univ i0)
      have e : v.1 (w i0) = 1 := hw1 i0 hi0
      rw [e] at this; exact this

end GlobalTheory.Nef
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdmissibleAdelicMatrixFamilyOrdersFiniteStatement
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissibleAdelicMatrixFamily_orders_finite : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ (n : ℕ) (g : Place k F → Matrix (Fin n) (Fin n) F), admitted g → {v : Place k F | ord v (g v).det ≠ 0}.Finite ∧ ∀ w : Fin n → F, w ≠ 0 → {v : Place k F | nrm v ((g v).mulVec w) ≠ 1}.Finite ∧ ∀ v, (g v).mulVec w ≠ 0 := by
  first | exact @GlobalTheory.Nef.lineFin | exact GlobalTheory.Nef.lineFin | (intros; apply GlobalTheory.Nef.lineFin <;> assumption)
end
end
