module

public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.BaseLen
public import Formalism.LocalRingCardinality.Lemmas
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ApplyLayers
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniqueFits
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasLabelTransportEquiv
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfIsCrystallineSpan

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthInvariantsLtTop
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.FiniteTwistInvariants

variable {O : Type} [CommRing O] [IsDomain O]

theorem length_quot_ne_top [IsDiscreteValuationRing O] (a : O) (ha : a ≠ 0) :
    Module.length O (O ⧸ Ideal.span {a}) ≠ ⊤ := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  have : Ideal.span {(u : O) * ϖ ^ n} = IsLocalRing.maximalIdeal O ^ n := by
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_mul_left_unit u.isUnit]
  rw [this, IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]
  exact ENat.coe_ne_top n

theorem fix_frac_zero {Γ : Type} {r : ℕ} (M : Γ → Matrix (Fin r) (Fin r) O)
    (hker : ∀ v : Fin r → O, (∀ g, (M g).mulVec v = v) → v = 0)
    (x : Fin r → FractionRing O) (hx : ∀ g, ((M g).map (algebraMap O (FractionRing O))).mulVec x = x) :
    x = 0 := by
  obtain ⟨⟨b, hb⟩, hbi⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) x
  choose u hu using hbi
  have hinj := IsFractionRing.injective O (FractionRing O)
  have hu' : (fun j => algebraMap O (FractionRing O) (u j)) = algebraMap O (FractionRing O) b • x := by
    funext j; rw [hu j]; simp [Algebra.smul_def]
  have h0 : u = 0 := by
    refine hker u fun g => ?_
    funext j
    apply hinj
    rw [RingHom.map_mulVec]
    show ((M g).map (algebraMap O (FractionRing O))).mulVec (fun j => algebraMap O (FractionRing O) (u j)) j = _
    rw [hu', Matrix.mulVec_smul, hx g]
    exact (congrFun hu' j).symm
  have hb0 : algebraMap O (FractionRing O) b ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap O (FractionRing O))]
    exact fun h => nonZeroDivisors.ne_zero hb (hinj h)
  have : algebraMap O (FractionRing O) b • x = 0 := by
    rw [← hu', h0]; funext j; simp
  exact (smul_eq_zero.mp this).resolve_left hb0

end GlobalTheory.FiniteTwistInvariants

namespace GlobalTheory.FiniteTwistInvariants

theorem exists_finset_ker {K V Γ : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : Γ → V →ₗ[K] V) (h : ∀ x, (∀ g, f g x = 0) → x = 0) :
    ∃ s : Finset Γ, ∀ x, (∀ g ∈ s, f g x = 0) → x = 0 := by
  classical
  let S : Set (Submodule K V) := Set.range fun s : Finset Γ => ⨅ g ∈ s, LinearMap.ker (f g)
  obtain ⟨p, ⟨s, rfl⟩, hmin⟩ := (wellFounded_lt (α := Submodule K V)).has_min S ⟨_, ⟨∅, rfl⟩⟩
  refine ⟨s, fun x hx => h x fun g => ?_⟩
  have hle : (⨅ g' ∈ insert g s, LinearMap.ker (f g')) ≤ ⨅ g' ∈ s, LinearMap.ker (f g') := by
    rw [Finset.iInf_insert]; exact inf_le_right
  have heq : (⨅ g' ∈ insert g s, LinearMap.ker (f g')) = ⨅ g' ∈ s, LinearMap.ker (f g') := by
    by_contra hne
    exact hmin _ ⟨insert g s, rfl⟩ (lt_of_le_of_ne hle hne)
  have hxs : x ∈ ⨅ g' ∈ s, LinearMap.ker (f g') := by
    simp only [Submodule.mem_iInf, LinearMap.mem_ker]; exact hx
  rw [← heq] at hxs
  simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hxs
  exact hxs g (Finset.mem_insert_self g s)

variable {O : Type} [CommRing O] [IsDomain O]

theorem exists_killer {ι : Type} [Fintype ι] {r : ℕ} (A : ι → Matrix (Fin r) (Fin r) O)
    (h : ∀ x : Fin r → FractionRing O, (∀ q, ((A q).map (algebraMap O (FractionRing O))).mulVec x = 0) → x = 0) :
    ∃ c : O, c ≠ 0 ∧ ∀ x : Fin r → FractionRing O,
      (∀ q, ((A q).map (algebraMap O (FractionRing O))).mulVec x ∈ stdG O (FractionRing O) r) →
        c • x ∈ stdG O (FractionRing O) r := by
  classical
  set K := FractionRing O
  have hinj := IsFractionRing.injective O K
  let B : Matrix (ι × Fin r) (Fin r) K := fun p j => algebraMap O K (A p.1 p.2 j)
  have hB : ∀ x p, (B.mulVec x) p = (((A p.1).map (algebraMap O K)).mulVec x) p.2 := fun _ _ => rfl
  have hker : LinearMap.ker (Matrix.toLin' B) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker, Matrix.toLin'_apply] at hx
    refine h x fun q => ?_
    funext i
    rw [← hB x (q, i), hx]; rfl
  obtain ⟨P, hP⟩ := LinearMap.exists_leftInverse_of_injective _ hker
  set P' := LinearMap.toMatrix' P
  have hPB : P' * B = 1 := by
    rw [← LinearMap.toMatrix'_toLin' B, ← LinearMap.toMatrix'_comp, hP, LinearMap.toMatrix'_id]
  obtain ⟨⟨b, hb⟩, hbi⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O)
    (fun p : Fin r × (ι × Fin r) => P' p.1 p.2)
  choose Q hQ using hbi
  refine ⟨b, nonZeroDivisors.ne_zero hb, fun x hx => ?_⟩
  choose y hy using hx
  let Y : ι × Fin r → O := fun p => y p.1 p.2
  have hY : (fun p => algebraMap O K (Y p)) = B.mulVec x := by
    funext p
    rw [hB]
    exact congrFun (hy p.1) p.2
  refine ⟨(Matrix.of fun j p => Q (j, p)).mulVec Y, ?_⟩
  funext j
  simp only [LinearMap.compLeft_apply, Function.comp_apply, Algebra.linearMap_apply]
  rw [RingHom.map_mulVec]
  have hQ' : (Matrix.of fun j p => Q (j, p)).map (algebraMap O K) = algebraMap O K b • P' := by
    ext j p
    simp only [Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    rw [hQ (j, p), Algebra.smul_def]
  have hYf : (⇑(algebraMap O K) ∘ Y) = B.mulVec x := hY
  rw [hQ', hYf, Matrix.smul_mulVec, Matrix.mulVec_mulVec, hPB, Matrix.one_mulVec, Pi.smul_apply,
    Pi.smul_apply, algebraMap_smul]

end GlobalTheory.FiniteTwistInvariants

namespace GlobalTheory.FiniteTwistInvariants

variable {O : Type} [CommRing O] [IsDomain O]

theorem stdG_eq_span (r : ℕ) :
    stdG O (FractionRing O) r = Submodule.span O (Set.range fun j : Fin r => (Pi.single j 1 : Fin r → FractionRing O)) := by
  ext x
  rw [Submodule.mem_span_range_iff_exists_fun]
  show x ∈ LinearMap.range _ ↔ _
  rw [LinearMap.mem_range]
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨u, funext fun k => ?_⟩
    simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def]
  · rintro ⟨u, rfl⟩
    refine ⟨u, funext fun k => ?_⟩
    simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def]

theorem WKG_mk {Γ : Type} [Group Γ] {r : ℕ} (M : Γ →* Matrix (Fin r) (Fin r) O) (g : Γ) (x : Fin r → FractionRing O) :
    WKG M g (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (((M g).map (algebraMap O (FractionRing O))).mulVec x) := rfl

theorem length_invariants_lt_top [IsDiscreteValuationRing O] {Γ Γ' : Type} [Group Γ] [Group Γ'] {r : ℕ}
    (M : Γ →* Matrix (Fin r) (Fin r) O) (f : Γ' →* Γ)
    (hker : ∀ v : Fin r → O, (∀ g, (M (f g)).mulVec v = v) → v = 0) :
    Module.length O ↥(Representation.invariants ((WKG M).comp f)) < ⊤ := by
  classical
  set K := FractionRing O
  let A : Γ' → Matrix (Fin r) (Fin r) O := fun g => M (f g) - 1
  have hAm : ∀ g, (A g).map (algebraMap O K) = (M (f g)).map (algebraMap O K) - 1 := by
    intro g
    show (algebraMap O K).mapMatrix (M (f g) - 1) = _
    rw [map_sub, map_one]; rfl
  have hK : ∀ x : Fin r → K, (∀ g, ((A g).map (algebraMap O K)).mulVec x = 0) → x = 0 := by
    intro x hx
    refine fix_frac_zero (fun g => M (f g)) hker x fun g => ?_
    have := hx g
    rwa [hAm, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at this
  obtain ⟨s, hs⟩ := exists_finset_ker (fun g => Matrix.toLin' ((A g).map (algebraMap O K)))
    (fun x hx => hK x fun g => by simpa [Matrix.toLin'_apply] using hx g)
  obtain ⟨c, hc0, hc⟩ := exists_killer (fun q : s => A q.1)
    (fun x hx => hs x fun g hg => by simpa [Matrix.toLin'_apply] using hx ⟨g, hg⟩)
  have hinj := IsFractionRing.injective O K
  have ha : algebraMap O K c ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap O K)]
    exact fun h => hc0 (hinj h)
  have hW : ∀ x ∈ Representation.invariants ((WKG M).comp f), c ^ 1 • x = 0 := by
    intro x hx
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [pow_one, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    refine hc x fun q => ?_
    have h1 := hx q.1
    rw [MonoidHom.comp_apply, WKG_mk, Submodule.Quotient.eq] at h1
    show ((A q.1).map (algebraMap O K)).mulVec x ∈ _
    rwa [hAm, Matrix.sub_mulVec, Matrix.one_mulVec]
  have hle := length_le_of_killed (LL := K) (stdG O K r) _ (stdG_eq_span r) c ha 1 _ hW
  have hL := length_quot_ne_top c hc0
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hL
  refine lt_of_le_of_lt hle ?_
  rw [← hm]
  norm_cast
  exact ENat.coe_lt_top _

end GlobalTheory.FiniteTwistInvariants

namespace GlobalTheory.FiniteTwistInvariants

theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), TruncatedSeriesCountingIdentities.admG2 i r ρ π → ∀ w ∈ placesOver D.host.E (D.nd.l i), Module.length (D.nd.O i) ↥(Representation.invariants ((Br.WKO i ρ π).comp (decS D.nd w))) < ⊤ := by
  intro D i r ρ π hG2 w hw
  have hH0 := (hG2 w hw (TruncatedSeriesCountingIdentities.CoefExt.self i w hw)).1.2.2.2.2.2.1
  show Module.length _ ↥(Representation.invariants ((WKG (WpO D.nd i ρ π)).comp (decS D.nd w))) < ⊤
  refine length_invariants_lt_top (WpO D.nd i ρ π) (decS D.nd w) fun v hv => ?_
  set C := TruncatedSeriesCountingIdentities.CoefExt.self i w hw
  set Bw := D.nbr i w hw
  let φ : D.nd.O i →+* ↥C.LL.1 :=
    (TruncatedSeriesCountingIdentities.CoefExt.inc C).comp ((algebraMap (Br.Ow Bw) (Br.LLw Bw)).comp Bw.eO.toRingHom)
  have hφ : Function.Injective φ := by
    intro a b hab
    have h1 := (TruncatedSeriesCountingIdentities.CoefExt.inc C).injective hab
    exact Br.toLL_inj Bw h1
  have hloc : ∀ gK, TruncatedSeriesCountingIdentities.locC C (WpO D.nd i ρ π) gK = (WpO D.nd i ρ π (decS D.nd w (Br.ι Bw gK))).map φ := fun _ => rfl
  have hmem : (fun j => φ (v j)) ∈ H0V (matRep (TruncatedSeriesCountingIdentities.locC C (WpO D.nd i ρ π))) := by
    simp only [H0V, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply]
    intro gK
    rw [sub_eq_zero]
    show Matrix.toLinAlgEquiv' _ _ = _
    rw [Matrix.toLinAlgEquiv'_apply, hloc]
    funext j
    rw [show (fun j => φ (v j)) = ⇑φ ∘ v from rfl, ← RingHom.map_mulVec, hv]
  rw [hH0, Submodule.mem_bot] at hmem
  funext j
  exact hφ (by simpa using congrFun hmem j)

end GlobalTheory.FiniteTwistInvariants
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelAllEquivSel
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel

noncomputable section

open Pointwise

namespace GlobalTheory.SelInf

section
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

theorem conj_Ine {A : ValuationSubring Ω} {g σ : G F Ω} (hσ : σ ∈ Ine (F := F) (g • A)) :
    g⁻¹ * σ * g ∈ Ine (F := F) A := by
  have m : ∀ y : Ω, y ∈ g • A ↔ (g⁻¹ : G F Ω) y ∈ A := fun y => by
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
  have m' : ∀ y : Ω, (g • A).valuation y < 1 ↔ A.valuation ((g⁻¹ : G F Ω) y) < 1 := fun y => by
    rw [valuation_lt_one_iff', valuation_lt_one_iff', m, m, map_inv₀,
      map_eq_zero_iff _ (g⁻¹ : G F Ω).injective]
  have c : ∀ x : Ω, (g⁻¹ : G F Ω) (g x) = x := fun x => by
    show (g⁻¹ * g) x = x
    simp
  refine ⟨?_, fun x hx => ?_⟩
  · have h : σ • g • A = g • A := hσ.1
    show (g⁻¹ * σ * g) • A = A
    rw [mul_smul, mul_smul, h, inv_smul_smul]
  · have hx' : (g • A).valuation (g x) ≤ 1 := by
      rw [ValuationSubring.valuation_le_one_iff, m, c]
      exact (A.valuation_le_one_iff x).1 hx
    have h := (m' _).1 (hσ.2 _ hx')
    rw [map_sub, c] at h
    exact h

variable {R R' : Type} [CommRing R] [CommRing R'] {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [DiscreteTopology M] {M' : Type} [AddCommGroup M'] [Module R' M'] [TopologicalSpace M'] [DiscreteTopology M']
  {S : Set (HeightOneSpectrum (𝓞 F))} {ρ : Representation R (G F Ω) M} {ρS : Representation R' (GS Ω S) M'}
  (e : M ≃+ M') (he : ∀ g m, e (ρ g m) = ρS (toGS Ω S g) (e m))

include he in
theorem triv_of_mem {σ : G F Ω} (hσ : σ ∈ NS Ω S) (m : M) : ρ σ m = m := by
  apply e.injective
  have : toGS Ω S σ = 1 := (QuotientGroup.eq_one_iff σ).2 hσ
  rw [he, this, map_one]
  rfl

def infZ (z : Z1 ρS) : Z1 ρ :=
  ⟨fun g => e.symm (z.1 (toGS Ω S g)),
    (continuous_of_discreteTopology (f := e.symm)).comp (z.2.1.comp (continuous_toGS Ω S)), fun g h => by
      apply e.injective
      beta_reduce
      rw [map_add (f := _), he, map_mul, z.2.2]
      simp⟩

theorem infZ_apply (z : Z1 ρS) (g : G F Ω) : (infZ e he z).1 g = e.symm (z.1 (toGS Ω S g)) := rfl

theorem mk_infZ_eq_iff (z z' : Z1 ρS) :
    (Submodule.Quotient.mk (infZ e he z) : H1 ρ) = Submodule.Quotient.mk (infZ e he z') ↔
      (Submodule.Quotient.mk z : H1 ρS) = Submodule.Quotient.mk z' := by
  rw [Submodule.Quotient.eq, Submodule.Quotient.eq, Submodule.mem_comap, Submodule.mem_comap, mem_coboundaries1, mem_coboundaries1]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨e m, fun g => ?_⟩
    obtain ⟨g, rfl⟩ : ∃ g', toGS Ω S g' = g := QuotientGroup.mk'_surjective _ g
    have h1 : e.symm (z.1 (toGS Ω S g)) - e.symm (z'.1 (toGS Ω S g)) = ρ g m - m := hm g
    have h2 := congrArg e h1
    rw [map_sub, map_sub, he, e.apply_symm_apply, e.apply_symm_apply] at h2
    exact h2
  · rintro ⟨m, hm⟩
    refine ⟨e.symm m, fun g => ?_⟩
    have h1 : z.1 (toGS Ω S g) - z'.1 (toGS Ω S g) = ρS (toGS Ω S g) m - m := hm (toGS Ω S g)
    change e.symm (z.1 (toGS Ω S g)) - e.symm (z'.1 (toGS Ω S g)) = _
    apply e.injective
    rw [map_sub, map_sub, he, e.apply_symm_apply, e.apply_symm_apply, e.apply_symm_apply]
    exact h1

def infH : H1 ρS → H1 ρ := fun x => Submodule.Quotient.mk (infZ e he x.out)

theorem infH_mk (z : Z1 ρS) : infH e he (Submodule.Quotient.mk z) = Submodule.Quotient.mk (infZ e he z) :=
  (mk_infZ_eq_iff e he _ _).2 (Quotient.out_eq' _)

theorem infH_injective : Function.Injective (infH e he) := by
  intro x y h
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [infH_mk, infH_mk] at h
  exact (mk_infZ_eq_iff e he _ _).1 h

theorem Ine_le_NS {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) {A : ValuationSubring Ω} (hA : IsPlaceOver A v)
    {σ : G F Ω} (hσ : σ ∈ Ine (F := F) A) : σ ∈ NS Ω S := by
  apply Subgroup.le_topologicalClosure
  apply Subgroup.subset_normalClosure
  simp only [Set.mem_iUnion]
  exact ⟨v, hv, A, hA, hσ⟩

theorem z_one {Γ : Type} [Group Γ] [TopologicalSpace Γ] {π : Representation R Γ M} (z : Z1 π) : z.1 1 = 0 := by
  have := z.2.2 1 1
  simpa using this

include he in
theorem mem_unrAt_iff {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) {A : ValuationSubring Ω} (hA : IsPlaceOver A v)
    (z : Z1 ρ) :
    resH1 ρ (Dec (F := F) A).subtype continuous_subtype_val (Submodule.Quotient.mk z) ∈ Formalism.GaloisCohomology.unrAt ρ A ↔
      ∀ σ ∈ Ine (F := F) A, z.1 σ = 0 := by
  have h0 : resH1 ρ (Dec (F := F) A).subtype continuous_subtype_val (Submodule.Quotient.mk z) ∈ Formalism.GaloisCohomology.unrAt ρ A ↔
      (Submodule.Quotient.mk (restrictCocycles1 _ ((Ine (F := F) A).subgroupOf (Dec (F := F) A)).subtype continuous_subtype_val
        (restrictCocycles1 ρ (Dec (F := F) A).subtype continuous_subtype_val z)) : H1 _) = 0 := Iff.rfl
  rw [h0, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, mem_coboundaries1]
  constructor
  · rintro ⟨m, hm⟩ σ hσ
    have h1 : z.1 σ = ρ σ m - m := hm ⟨⟨σ, Ine_le_Dec A hσ⟩, hσ⟩
    rw [h1, triv_of_mem e he (Ine_le_NS hv hA hσ), sub_self]
  · intro h
    refine ⟨0, fun g => ?_⟩
    rw [map_zero, sub_zero]
    exact h g.1.1 g.2

include he in
theorem vanish_NS [IsAlgClosure F Ω] (A : Formalism.GaloisCohomology.Places F Ω) (z : Z1 ρ)
    (h : ∀ v ∉ S, ∀ σ ∈ Ine (F := F) (A.1 v), z.1 σ = 0) : ∀ σ ∈ NS Ω S, z.1 σ = 0 := by
  have hz := z.2.2
  have hinv : ∀ g, z.1 g + ρ g (z.1 g⁻¹) = 0 := fun g => by
    rw [← hz, mul_inv_cancel, z_one]
  let K : Subgroup (G F Ω) :=
    { carrier := {g | g ∈ NS Ω S ∧ z.1 g = 0}
      one_mem' := ⟨one_mem _, z_one z⟩
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        exact ⟨mul_mem ha hb, by rw [hz, ha', hb', map_zero, add_zero]⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨inv_mem ha, ?_⟩
        have := hinv a
        rwa [ha', zero_add, triv_of_mem e he ha] at this }
  have hK : K.Normal := ⟨by
    rintro a ⟨ha, ha'⟩ g
    refine ⟨(normal_NS S).conj_mem a ha g, ?_⟩
    rw [mul_assoc, hz, hz, ha', zero_add, triv_of_mem e he ha, hinv]⟩
  have hc : IsClosed (K : Set (G F Ω)) :=
    (isClosed_NS Ω S).inter ((isClosed_discrete {(0 : M)}).preimage z.2.1)
  have hle : Subgroup.normalClosure
      (⋃ v ∈ Sᶜ, ⋃ A ∈ {A : ValuationSubring (Ω) | IsPlaceOver A v}, Inertia (F := F) A) ≤ K := by
    apply Subgroup.normalClosure_le_normal
    intro τ hτ
    simp only [Set.mem_iUnion] at hτ
    obtain ⟨v, hv, B, hB, hτ⟩ := hτ
    obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver (F := F) (A.2 v) hB
    have h1 := conj_Ine (F := F) hτ
    have h2 : g⁻¹ * τ * g ∈ K := ⟨Ine_le_NS hv (A.2 v) h1, h v hv _ h1⟩
    have h3 := hK.conj_mem _ h2 g
    have h4 : g * (g⁻¹ * τ * g) * g⁻¹ = τ := by group
    rwa [h4] at h3
  intro σ hσ
  exact (Subgroup.topologicalClosure_minimal _ hle hc hσ).2

theorem exists_infZ (z : Z1 ρ) (h : ∀ σ ∈ NS Ω S, z.1 σ = 0) : ∃ z', infZ e he z' = z := by
  have hz := z.2.2
  have hw : ∀ a b : G F Ω, (QuotientGroup.leftRel (NS Ω S)) a b → e (z.1 a) = e (z.1 b) := by
    intro a b hab
    rw [QuotientGroup.leftRel_apply] at hab
    have : z.1 (a * (a⁻¹ * b)) = z.1 a := by rw [hz, h _ hab, map_zero, add_zero]
    rw [← this, mul_inv_cancel_left]
  refine ⟨⟨Quotient.lift (fun g => e (z.1 g)) hw,
    Continuous.quotient_lift ((continuous_of_discreteTopology (f := e)).comp z.2.1) hw, fun g g' => ?_⟩, ?_⟩
  · obtain ⟨g, rfl⟩ : ∃ g', toGS Ω S g' = g := QuotientGroup.mk'_surjective _ g
    obtain ⟨g', rfl⟩ : ∃ g'', toGS Ω S g'' = g' := QuotientGroup.mk'_surjective _ g'
    rw [← map_mul]
    change e (z.1 (g * g')) = e (z.1 g) + ρS (toGS Ω S g) (e (z.1 g'))
    rw [hz, map_add (f := _), he]
  · exact Subtype.ext (funext fun g => e.symm_apply_apply (z.1 g))

end

theorem selAll_equiv_sel : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (R R' : Type) [CommRing R] [CommRing R'] (M : Type) [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] (M' : Type) [AddCommGroup M'] [Module R' M'] [TopologicalSpace M'] [DiscreteTopology M'] (S : Finset (HeightOneSpectrum (𝓞 F))) (A : Formalism.GaloisCohomology.Places F Ω) (ρ : Representation R (G F Ω) M) (ρS : Representation R' (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M') (e : M ≃+ M'), ContAction ρ → (∀ g m, e (ρ g m) = ρS (toGS Ω _ g) (e m)) → ∀ (L : ∀ v, Submodule R (H1 (ρ.comp (Dec (F := F) (A.1 v)).subtype))) (LS : LocCond ρS (locFam S (fun v => A.1 v.1))), (∀ v ∉ S, L v = Formalism.GaloisCohomology.unrAt ρ (A.1 v)) → (∀ (v : S) (z : Z1 (ρ.comp (Dec (F := F) (A.1 v.1)).subtype)) (z' : Z1 (ρS.comp (locFam S (fun v => A.1 v.1) v))), (∀ g, z'.1 g = e (z.1 g)) → (Submodule.Quotient.mk z ∈ L v.1 ↔ Submodule.Quotient.mk z' ∈ LS v)) → Nonempty (Formalism.GaloisCohomology.SelAll ρ A L ≃ Sel ρS (locFam S (fun v => A.1 v.1)) (continuous_locFam S _) LS) := by
  intro F Ω _ _ _ _ _ R R' _ _ M _ _ _ _ M' _ _ _ _ S A ρ ρS e _ he L LS hL hLS
  have key : ∀ (z : Z1 ρS) (v : S),
      resH1 ρ (Dec (F := F) (A.1 v.1)).subtype continuous_subtype_val (Submodule.Quotient.mk (infZ e he z)) ∈ L v.1 ↔
      resH1 ρS (locFam S (fun v => A.1 v.1) v) (continuous_locFam S _ v) (Submodule.Quotient.mk z) ∈ LS v :=
    fun z v => hLS v (restrictCocycles1 ρ (Dec (F := F) (A.1 v.1)).subtype continuous_subtype_val (infZ e he z))
      (restrictCocycles1 ρS (locFam S (fun v => A.1 v.1) v) (continuous_locFam S _ v) z)
      (fun g => (e.apply_symm_apply _).symm)
  have hall : ∀ y : H1 ρ, y ∈ Formalism.GaloisCohomology.SelAll ρ A L ↔
      ∀ v, resH1 ρ (Dec (F := F) (A.1 v)).subtype continuous_subtype_val y ∈ L v :=
    fun y => mem_Sel ρ (fun v => (Dec (F := F) (A.1 v)).subtype) (fun _ => continuous_subtype_val) L y
  have hmem : ∀ x : H1 ρS, x ∈ Sel ρS (locFam S (fun v => A.1 v.1)) (continuous_locFam S _) LS ↔
      infH e he x ∈ Formalism.GaloisCohomology.SelAll ρ A L := by
    intro x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [infH_mk, hall, mem_Sel]
    constructor
    · intro h v
      by_cases hv : v ∈ S
      · exact (key z ⟨v, hv⟩).2 (h ⟨v, hv⟩)
      · rw [hL v hv, mem_unrAt_iff e he (by simpa using hv) (A.2 v)]
        intro σ hσ
        have : toGS Ω (S : Set (HeightOneSpectrum (𝓞 F))) σ = 1 :=
          (QuotientGroup.eq_one_iff σ).2 (Ine_le_NS (by simpa using hv) (A.2 v) hσ)
        rw [infZ_apply, this, z_one, map_zero]
    · intro h v
      exact (key z v).1 (h v.1)
  refine ⟨(Equiv.ofBijective (fun x : Sel ρS (locFam S (fun v => A.1 v.1)) (continuous_locFam S _) LS =>
    (⟨infH e he x.1, (hmem _).1 x.2⟩ : Formalism.GaloisCohomology.SelAll ρ A L)) ⟨?_, ?_⟩).symm⟩
  · intro x y h
    exact Subtype.ext (infH_injective e he (congrArg Subtype.val h))
  · rintro ⟨y, hy⟩
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have hy' := (hall _).1 hy
    obtain ⟨z', rfl⟩ := exists_infZ e he z (vanish_NS e he A z fun v hv => by
      have hv' : v ∉ S := by simpa using hv
      have := hy' v
      rwa [hL v hv', mem_unrAt_iff e he hv (A.2 v)] at this)
    exact ⟨⟨Submodule.Quotient.mk z', (hmem _).2 (by rw [infH_mk]; exact hy)⟩, Subtype.ext (infH_mk e he z')⟩

end GlobalTheory.SelInf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZgFormula
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZgFormula
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.ZgAll

theorem eq_top_of_closed {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [CompactSpace G]
    (lam : G →* Multiplicative ℤ_[l]) (hlam : Continuous lam) (g₀ : G)
    (h₀ : lam g₀ = Multiplicative.ofAdd 1) (S : Subgroup G) (hS : IsClosed (S : Set G))
    (hker : ∀ h, lam h = 1 → h ∈ S) (hg₀ : g₀ ∈ S) (g : G) : g ∈ S := by
  have hc : IsClosed (lam '' (S : Set G)) := (hS.isCompact.image hlam).isClosed
  have hsub : Set.range (fun n : ℤ => Multiplicative.ofAdd (n : ℤ_[l])) ⊆ lam '' (S : Set G) := by
    rintro _ ⟨n, rfl⟩
    refine ⟨g₀ ^ n, S.zpow_mem hg₀ n, ?_⟩
    rw [map_zpow, h₀, ← ofAdd_zsmul]
    simp
  have hd : DenseRange (fun n : ℤ => Multiplicative.ofAdd (n : ℤ_[l])) :=
    PadicInt.denseRange_intCast
  have hmem : lam g ∈ lam '' (S : Set G) := hc.closure_subset_iff.2 hsub (hd (lam g))
  obtain ⟨a, ha, hag⟩ := hmem
  have h1 : g * a⁻¹ ∈ S := hker _ (by rw [map_mul, map_inv, hag, mul_inv_cancel])
  simpa using S.mul_mem h1 ha

end GlobalTheory.NL.ZgAll

namespace GlobalTheory.NL.ZgAll

variable {l : ℕ} [Fact l.Prime] {G M : Type} [Group G] [TopologicalSpace G] [CompactSpace G]
  [AddCommGroup M] [TopologicalSpace M] [T2Space M]

theorem coc_inv (a : G → M →+ M) (Z : G → M) (hZm : ∀ g h, Z (g * h) = Z g + a g (Z h))
    (h1 : Z 1 = 0) (g : G) : Z g⁻¹ = -a g⁻¹ (Z g) := by
  have := hZm g⁻¹ g
  rw [inv_mul_cancel, h1] at this
  exact eq_neg_of_add_eq_zero_left this.symm

theorem mem_and_comm (a : G → M →+ M)
    (lam : G →* Multiplicative ℤ_[l]) (hlam : Continuous lam) (g₀ : G) (h₀ : lam g₀ = Multiplicative.ofAdd 1)
    (J : AddSubgroup M) (hJ : IsClosed (J : Set M)) (hJa : ∀ g, ∀ x ∈ J, a g x ∈ J)
    (hJk : ∀ h, lam h = 1 → ∀ x ∈ J, a h x = x) (z : M) (hz : z ∈ J)
    (Z : G → M) (hZc : Continuous Z) (hZm : ∀ g h, Z (g * h) = Z g + a g (Z h))
    (hZk : ∀ h, lam h = 1 → Z h = 0) (hZ₀ : Z g₀ = z) :
    (∀ g, Z g ∈ J) ∧ ∀ g, a g₀ (Z g) - Z g = a g z - z := by
  have h1 : Z 1 = 0 := hZk 1 (map_one lam)
  let S : Subgroup G :=
    { carrier := {g | Z g ∈ J}
      one_mem' := by simp [h1]
      mul_mem' := by
        intro g h hg hh
        simp only [Set.mem_setOf_eq, hZm] at hg hh ⊢
        exact J.add_mem hg (hJa g _ hh)
      inv_mem' := by
        intro g hg
        simp only [Set.mem_setOf_eq, coc_inv a Z hZm h1] at hg ⊢
        exact J.neg_mem (hJa _ _ hg) }
  have hS : IsClosed (S : Set G) := hJ.preimage hZc
  have hall : ∀ g, Z g ∈ J := fun g =>
    eq_top_of_closed lam hlam g₀ h₀ S hS (fun h hh => by
      change Z h ∈ J
      rw [hZk h hh]; exact J.zero_mem) (by change Z g₀ ∈ J; rw [hZ₀]; exact hz) g
  refine ⟨hall, fun g => ?_⟩
  set k := g₀ * g * (g * g₀)⁻¹ with hk
  have hk1 : lam k = 1 := by
    simp only [hk, map_mul, map_inv]
    rw [mul_comm (lam g) (lam g₀), mul_inv_cancel]
  have e1 : g₀ * g = k * (g * g₀) := by rw [hk, inv_mul_cancel_right]
  have e2 : Z (g₀ * g) = Z (g * g₀) := by
    rw [e1, hZm, hZk k hk1, zero_add, hJk k hk1 _ (hall _)]
  rw [hZm, hZm, hZ₀] at e2
  rw [sub_eq_sub_iff_add_eq_add, add_comm (a g z), ← e2, add_comm]

theorem uniq (a : G → M →+ M)
    (lam : G →* Multiplicative ℤ_[l]) (hlam : Continuous lam) (g₀ : G) (h₀ : lam g₀ = Multiplicative.ofAdd 1)
    (Z Z' : G → M) (hZc : Continuous Z) (hZc' : Continuous Z')
    (hZm : ∀ g h, Z (g * h) = Z g + a g (Z h)) (hZm' : ∀ g h, Z' (g * h) = Z' g + a g (Z' h))
    (hZk : ∀ h, lam h = 1 → Z h = 0) (hZk' : ∀ h, lam h = 1 → Z' h = 0) (h₀' : Z g₀ = Z' g₀) (g : G) :
    Z g = Z' g := by
  have h1 : Z 1 = 0 := hZk 1 (map_one lam)
  have h1' : Z' 1 = 0 := hZk' 1 (map_one lam)
  let S : Subgroup G :=
    { carrier := {g | Z g = Z' g}
      one_mem' := by simp [h1, h1']
      mul_mem' := by
        intro g h hg hh
        simp only [Set.mem_setOf_eq, hZm, hZm'] at hg hh ⊢
        rw [hg, hh]
      inv_mem' := by
        intro g hg
        simp only [Set.mem_setOf_eq, coc_inv a Z hZm h1, coc_inv a Z' hZm' h1'] at hg ⊢
        rw [hg] }
  exact eq_top_of_closed lam hlam g₀ h₀ S (isClosed_eq hZc hZc')
    (fun h hh => by change Z h = Z' h; rw [hZk h hh, hZk' h hh]) h₀' g

end GlobalTheory.NL.ZgAll

namespace GlobalTheory.NL.ZgAll

set_option maxHeartbeats 8000000 in
theorem zg_formula_let : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (y z : W.DD T), z ∈ aN W T letπ → ∀ hyz : (y, z) ∈ W.divisibleCocycles T, ∃ zz : ↥W.GKs → W.DD T, (∀ g, zz g ∈ aN W T letπ) ∧ (∀ g, W.γ T (zz g) - zz g = W.γD T (W.resΓ g) z - z) ∧ ∀ b : TW (RW LL) T, TWmap (φRW LL) T b - b = E.jD T y → ∃ c : ↥(latticeCocycles (resLat T W.GKs)), Submodule.Quotient.mk c = W.cl T ⟨(y, z), hyz⟩ ∧ ∀ g : ↥W.GKs, ∃ t : ↥T.L.T, (t : T.V) = (c : ↥W.GKs → T.V) g ∧ (1 : RW LL) ⊗ₜ[↥(OL LL)] t = E.jD T (zz g) - (TWact ((D.locA l).gRW LL ((g : ↥(GK K)) : GQ l)) T g b - b) := by
  set_option synthInstance.maxHeartbeats 40000 in
    intro D HW F l _ K s LL h W E T hT y z hz hyz
    have hc := GlobalTheory.HerrClassMaps.compact_GK K
    have H2 := GlobalTheory.HWL.Coord.exists_gamma_coordinates l (D.loc l) K s LL h (gamOf W ((HW l).W_s K s LL h))
    rcases H2 with ⟨⟨lam₀, hlc₀, hl1₀, hlg₀, ⟨g₁, hg₁⟩, hcl⟩, -⟩
    have hcs : CompactSpace ↥W.GKs := isCompact_iff_compactSpace.1 hcl.isCompact
    have hlamW : ∃ lam : ↥W.GKs →* Multiplicative ℤ_[l], Continuous lam ∧
        (∀ g : ↥W.GKs, lam g = 1 ↔ W.resΓ (g : ↥(GK K)) = 1) ∧
        (∀ g : ↥W.GKs, lam g = Multiplicative.ofAdd 1 ↔ W.resΓ (g : ↥(GK K)) = W.gam) ∧
        ∃ g : ↥W.GKs, lam g = Multiplicative.ofAdd 1 := ⟨lam₀, hlc₀, hl1₀, hlg₀, g₁, hg₁⟩
    rcases hlamW with ⟨lam, hlc, hl1, hlg, g₀, hg₀⟩
    have H1 := GlobalTheory.T.etaleComparison_pi_wachLattice_closed_weak D HW F l K s LL h T hT
    rcases H1 with ⟨τ, hT2, hTG, hact, hemb, hclo⟩

    let a : ↥W.GKs → TW (RW LL) T →+ TW (RW LL) T := fun g =>
      (TWact ((D.locA l).gRW LL (((g : ↥(GK K))) : GQ l)) T (g : ↥(GK K))).toAddMonoidHom
    have ha1 : ∀ g x, a g x = TWact ((D.locA l).gRW LL (((g : ↥(GK K))) : GQ l)) T (g : ↥(GK K)) x :=
      fun g x => rfl
    have hamul : ∀ g g' x, a (g * g') x = a g (a g' x) := by
      intro g g' x
      simp only [ha1]
      exact GlobalTheory.HerrClassMaps.TWact_mul _ _ _
        (fun r => GlobalTheory.HerrClassMaps.gRW_mul (D.locA l) LL _ _ r) T _ _ x
    have ha1t : ∀ g (t : ↥T.L.T), a g ((1 : RW LL) ⊗ₜ[↥(OL LL)] t) =
        (1 : RW LL) ⊗ₜ[↥(OL LL)] (⟨T.ρ (g : ↥(GK K)) t, T.L.stable _ t t.2⟩ : ↥T.L.T) := fun g t =>
      GlobalTheory.HerrClassMaps.TWact_one_tmul _ T _ t
    have haj : ∀ g (w : W.DD T), a g (E.jD T w) = E.jD T (W.γD T (W.resΓ (g : ↥(GK K))) w) := fun g w =>
      (E.jD_act T (g : ↥(GK K)) w).symm
    letI := τ
    have hl1' := hl1
    have hlg' := hlg
    have hstab : ∀ (γ' : W.Gam) (w : W.DD T), w ∈ aN W T letπ → W.γD T γ' w ∈ aN W T letπ := by
      intro γ' w hw
      obtain ⟨n, hn, rfl⟩ := hw
      have hx : (letπ : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) • n ∈ W.N T := (W.N T).smul_mem _ hn
      obtain ⟨y', hy', e⟩ := W.N_π T γ' _ hx
      refine ⟨n + y', (W.N T).add_mem hn hy', ?_⟩
      change (letπ : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) • (n + y') =
        W.γD T γ' ((letπ : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) • n)
      rw [smul_add, ← e]
      abel
    let J : AddSubgroup (TW (RW LL) T) :=
      (aN W T letπ).toAddSubgroup.map (E.jD T).toAddMonoidHom
    have hJm : ∀ x, x ∈ J ↔ ∃ w ∈ aN W T letπ, E.jD T w = x := fun x => AddSubgroup.mem_map
    have hJ : IsClosed (J : Set (TW (RW LL) T)) := by
      have : (J : Set (TW (RW LL) T)) = E.jD T '' (aN W T letπ : Set (W.DD T)) := by
        ext x
        exact (hJm x).trans Iff.rfl
      rw [this]; exact hclo
    have hJa : ∀ g, ∀ x ∈ J, a g x ∈ J := by
      intro g x hx
      obtain ⟨w, hw, rfl⟩ := (hJm x).1 hx
      rw [haj]
      exact (hJm _).2 ⟨_, hstab _ w hw, rfl⟩
    have hJk : ∀ h' : ↥W.GKs, lam h' = 1 → ∀ x ∈ J, a h' x = x := by
      intro h' hh x hx
      obtain ⟨w, -, rfl⟩ := (hJm x).1 hx
      rw [haj, (hl1' h').1 hh, W.γD_one]
    haveI hCA : ContinuousAdd (TW (RW LL) T) := hTG.toContinuousAdd
    haveI hCN : ContinuousNeg (TW (RW LL) T) := hTG.toContinuousNeg
    haveI hCS : ContinuousSub (TW (RW LL) T) :=
      ⟨Continuous.congr (continuous_fst.add continuous_snd.neg) (fun p => (sub_eq_add_neg p.1 p.2).symm)⟩
    let Zf : TW (RW LL) T → ↥(latticeCocycles (resLat T W.GKs)) → ↥W.GKs → TW (RW LL) T := fun b c g =>
      (1 : RW LL) ⊗ₜ[↥(OL LL)] (⟨(c : ↥W.GKs → T.V) g, GlobalTheory.HerrClassMaps.mem_T c g⟩ : ↥T.L.T) + (a g b - b)
    have hZc : ∀ b c, Continuous (Zf b c) := fun b c =>
      (hemb.comp (c.2.1.1.subtype_mk fun g => GlobalTheory.HerrClassMaps.mem_T c g)).add
        (((hact b).comp continuous_subtype_val).sub continuous_const)
    have hZm : ∀ b c g g', Zf b c (g * g') = Zf b c g + a g (Zf b c g') := by
      intro b c g g'
      have e : (⟨(c : ↥W.GKs → T.V) (g * g'), GlobalTheory.HerrClassMaps.mem_T c (g * g')⟩ : ↥T.L.T) =
          ⟨(c : ↥W.GKs → T.V) g, GlobalTheory.HerrClassMaps.mem_T c g⟩ +
            ⟨T.ρ (g : ↥(GK K)) ((c : ↥W.GKs → T.V) g'), T.L.stable _ _ (GlobalTheory.HerrClassMaps.mem_T c g')⟩ :=
        Subtype.ext (c.2.1.2 g g')
      simp only [Zf, map_add (a g), map_sub (a g), ha1t, hamul, e, TensorProduct.tmul_add]
      abel
    have hfit : ∀ b, TWmap (φRW LL) T b - b = E.jD T y → ∃ c : ↥(latticeCocycles (resLat T W.GKs)),
        Submodule.Quotient.mk c = W.cl T ⟨(y, z), hyz⟩ ∧ (∀ h' : ↥W.GKs, lam h' = 1 → Zf b c h' = 0) ∧
          Zf b c g₀ = E.jD T z := by
      intro b hb
      have H := E.cl_def T ⟨(y, z), hyz⟩ b hb
      rcases H with ⟨c, hc1, hc2⟩
      refine ⟨c, hc1, fun h' hh => ?_, ?_⟩
      · have e := (hc2 h' ⟨_, GlobalTheory.HerrClassMaps.mem_T c h'⟩ rfl).1 ((hl1' h').1 hh)
        simp only [Zf]
        rw [e]
        exact neg_add_cancel _
      · have e := (hc2 g₀ ⟨_, GlobalTheory.HerrClassMaps.mem_T c g₀⟩ rfl).2 ((hlg' g₀).1 hg₀)
        simp only [Zf]
        simp only [e]
        exact sub_add_cancel _ _
    have hb₀ex := (GlobalTheory.WittTensorFixed.main l K LL T).1 (E.jD T y)
    rcases hb₀ex with ⟨b₀, hb₀⟩
    have H0 := hfit b₀ hb₀
    rcases H0 with ⟨c₀, -, hk₀, hg₀'⟩
    have hzJ : E.jD T z ∈ J := (hJm _).2 ⟨z, hz, rfl⟩
    have HM := mem_and_comm a lam hlc g₀ hg₀ J hJ hJa hJk _ hzJ (Zf b₀ c₀) (hZc b₀ c₀) (hZm b₀ c₀) hk₀ hg₀'
    rcases HM with ⟨hall, hcomm⟩
    choose zz hzz hzzj using fun g => (hJm _).1 (hall g)
    refine ⟨zz, hzz, fun g => ?_, fun b hb => ?_⟩
    · apply E.jD_inj T
      have h1 := hcomm g
      simp only [← hzzj g, haj, (hlg' g₀).1 hg₀] at h1
      simp only [map_sub, LocWach.γ]
      exact h1
    · have H := hfit b hb
      rcases H with ⟨c, hc1, hk, hgc⟩
      refine ⟨c, hc1, fun g => ⟨⟨_, GlobalTheory.HerrClassMaps.mem_T c g⟩, rfl, ?_⟩⟩
      have hu := uniq a lam hlc g₀ hg₀ (Zf b c) (Zf b₀ c₀) (hZc b c) (hZc b₀ c₀) (hZm b c) (hZm b₀ c₀) hk hk₀
        (hgc.trans hg₀'.symm) g
      simp only [hzzj g, ← hu]
      simp only [Zf]
      exact (add_sub_cancel_right _ _).symm

theorem zg_formula : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (y z : ((HW l).W K s LL h).DD T), z ∈ aN ((HW l).W K s LL h) T letπ → ∀ hyz : (y, z) ∈ ((HW l).W K s LL h).divisibleCocycles T, ∃ zz : ↥((HW l).W K s LL h).GKs → ((HW l).W K s LL h).DD T, (∀ g, zz g ∈ aN ((HW l).W K s LL h) T letπ) ∧ (∀ g, ((HW l).W K s LL h).γ T (zz g) - zz g = ((HW l).W K s LL h).γD T (((HW l).W K s LL h).resΓ g) z - z) ∧ ∀ b : TW (RW LL) T, TWmap (φRW LL) T b - b = ((F l).E K s LL h).tie.jD T y → ∃ c : ↥(latticeCocycles (resLat T ((HW l).W K s LL h).GKs)), Submodule.Quotient.mk c = ((HW l).W K s LL h).cl T ⟨(y, z), hyz⟩ ∧ ∀ g : ↥((HW l).W K s LL h).GKs, ∃ t : ↥T.L.T, (t : T.V) = (c : ↥((HW l).W K s LL h).GKs → T.V) g ∧ (1 : RW LL) ⊗ₜ[↥(OL LL)] t = ((F l).E K s LL h).tie.jD T (zz g) - (TWact ((D.locA l).gRW LL ((g : ↥(GK K)) : GQ l)) T g b - b) :=
  fun D HW F l _ K s LL h => zg_formula_let D HW F l K s LL h

end GlobalTheory.NL.ZgAll
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZgFormulaStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zg_formula_alt : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (y z : ((HW l).W K s LL h).DD T), z ∈ aN ((HW l).W K s LL h) T letπ → ∀ hyz : (y, z) ∈ ((HW l).W K s LL h).divisibleCocycles T, ∃ zz : ↥((HW l).W K s LL h).GKs → ((HW l).W K s LL h).DD T, (∀ g, zz g ∈ aN ((HW l).W K s LL h) T letπ) ∧ (∀ g, ((HW l).W K s LL h).γ T (zz g) - zz g = ((HW l).W K s LL h).γD T (((HW l).W K s LL h).resΓ g) z - z) ∧ ∀ b : TW (RW LL) T, TWmap (φRW LL) T b - b = ((F l).E K s LL h).tie.jD T y → ∃ c : ↥(latticeCocycles (resLat T ((HW l).W K s LL h).GKs)), Submodule.Quotient.mk c = ((HW l).W K s LL h).cl T ⟨(y, z), hyz⟩ ∧ ∀ g : ↥((HW l).W K s LL h).GKs, ∃ t : ↥T.L.T, (t : T.V) = (c : ↥((HW l).W K s LL h).GKs → T.V) g ∧ (1 : RW LL) ⊗ₜ[↥(OL LL)] t = ((F l).E K s LL h).tie.jD T (zz g) - (TWact ((D.locA l).gRW LL ((g : ↥(GK K)) : GQ l)) T g b - b) := by
  first | exact @GlobalTheory.NL.ZgAll.zg_formula | exact GlobalTheory.NL.ZgAll.zg_formula | (intros; apply GlobalTheory.NL.ZgAll.zg_formula <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StrictnessOfTied
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FilteredIsoOfFilZero
noncomputable section

namespace GlobalTheory.DeRhamCompare

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N TensorProduct GlobalTheory.IndefiniteRowSideFullHecke

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL]

variable [TopologicalSpace G] [TopologicalSpace LL]

section Whole

variable {V V' : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
  [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
  {ρ : Representation LL G V} {ρ' : Representation LL G V'}

omit [TopologicalSpace G] [TopologicalSpace LL]

end Whole

end Generic

section At

variable (K LL : FinExt l)

end At

private theorem dualExactSequence_mapdR_eq {K LL : _root_.Formalism.BasicNotions.Loc.FinExt l}
    {T T' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.Lat K LL} (f : T.V →ₗ[↥LL.1] T'.V) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.mapdR P f = _root_.GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual.mapdR (Qp := ℚ_[l]) (BdR := P.R.BdR) f :=
  rfl

private theorem strictness_of_dualExactSequence_strict
    (h : _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.Strict l P) : _root_.GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual.Strictness l P := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.Strict _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.OverGood
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.StrictAt _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.IsSES _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.SubSES
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.Emb at h
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual.Strictness _root_.GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual.StrictCore
  · intro K s LL hg T₀ T₁ T₂ f g hf hg' hi he hs h₀ h₁ h₂ τ a
    obtain ⟨k₁, k₂, k₃⟩ := h K s LL hg T₀ T₁ T₂ f g ⟨hf, hg', hi, he, hs⟩ h₀ h₁ h₂ τ a
    simp only [dualExactSequence_mapdR_eq] at k₁ k₂ k₃
    refine ⟨k₁, ?_, ?_⟩
    · ext y
      simpa [Submodule.mem_inf] using k₂ y
    · ext z
      simpa using k₃ z

private theorem dualExactSequence_strict_of_strictness
    (h : _root_.GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual.Strictness l P) : _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.Strict l P := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual.Strictness _root_.GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual.StrictCore at h
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.Strict _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.OverGood
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.StrictAt _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.IsSES _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.SubSES
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.Emb
  · intro K s LL hg T₀ T₁ T₂ f g hfg h₀ h₁ h₂ τ a
    obtain ⟨hf, hg', hi, he, hs⟩ := hfg
    have k := h K s LL hg T₀ T₁ T₂ f g
    have k' := k hf hg' hi he hs
    have k'' := k' h₀ h₁ h₂
    have k3 := k'' τ
    have k4 := k3 a
    obtain ⟨k₁, k₂, k₃⟩ := k4
    refine ⟨k₁, fun y => ?_, fun z => ?_⟩
    · have := SetLike.ext_iff.mp k₂ y
      simpa [Submodule.mem_inf, dualExactSequence_mapdR_eq] using this
    · have := SetLike.ext_iff.mp k₃ z
      simpa [dualExactSequence_mapdR_eq] using this

theorem _root_.GlobalTheory.DeRhamCompare.strict_iff :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.Strict l P ↔ _root_.GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual.Strictness l P :=
  ⟨strictness_of_dualExactSequence_strict P,
    dualExactSequence_strict_of_strictness P⟩

end GlobalTheory.DeRhamCompare
end
end

open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions

namespace GlobalTheory.FontaineExtensionCriteria

open GlobalTheory.Per.FontaineBound in
theorem fontCore_of_tied {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI)
    (K : FinExt l) : LocalSituation.fontCore (P.PD K) := by
  intro LL _ _ _ O _ _ hO A
  have : FiniteDimensional ℚ_[l] LL := hO.2.1
  have hd := ddR_finite_le (P.PD K) (isField_of_tied T) A.ρ
  refine ⟨?_, hd, fun hc => ?_⟩
  · have := isDomain_cris (P.PD K) (isField_of_tied T)
    have := (P.PD K).finK₀
    refine finite_finrank_le (P.PD K).actB (fun b b' hb h => GlobalTheory.T.ratio_invariant_in_K0 l P AI T K b' b hb fun g hg => ?_) A.ρ
    have h1 := h ⟨g, hg⟩
    rw [P.PD_actB, P.PD_actB] at h1
    rw [mul_comm, h1, mul_comm]
  · refine (GlobalTheory.Per.CrisDR.abstract_cmp (P.PD K) A.ρ
      (fun m x hx b hb => GlobalTheory.T.injective_tensor_Bcris_to_BdR l P AI T K m x hx b ?_) hd.1 hd.2 hc).1
    simpa only [P.PD_ι] using hb

theorem strictness_of_tied {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) :
    GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual.Strictness l P :=
  (GlobalTheory.DeRhamCompare.strict_iff P).1 (GlobalTheory.DRFil.deRhamComparison l P AI ⟨T⟩).2.2.2.2.2.1

theorem extCrys_of_tied : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P),
    Nonempty (LocTied l P AI) → GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions.ExtCrys P :=
  fun P _ ⟨T⟩ => GlobalTheory.CrysExt.extCrys P (fontCore_of_tied T) (strictness_of_tied T)

end GlobalTheory.FontaineExtensionCriteria
end
