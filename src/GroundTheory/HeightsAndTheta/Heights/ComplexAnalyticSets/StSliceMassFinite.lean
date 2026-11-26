module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPlaneSliceMass

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceMassFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

noncomputable section

def SliceMassFinite.Statement : Prop :=
  ∀ (n d : ℕ) (h : HermNorm n) (I : Ideal (MvPolynomial (Fin n) ℂ)) (ℓ : Fin n → ℂ)
    (A : Matrix (Fin d) (Fin n) ℂ),
    I.IsPrime → linForm ℓ - 1 ∈ I → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) = d →
    IsFiniteProjection I A →
      Integrable (chartAbsDens I A (fun _ => 1) (fun _ x => Real.log (h.dualNorm x)))

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFormIntPos
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets ReciprocityTheory.AnForm
open scoped ContDiff

noncomputable section

namespace FormIntegralPositivity

variable {n : ℕ}

theorem analyticAt_sheet {d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {x : Fin n → ℂ} {s : (Fin d → ℂ) → Fin n → ℂ} (hs : IsSheetAt J A x s) :
    AnalyticAt ℂ s (A *ᵥ x) := by
  obtain ⟨U, hU, hxU, hsU, -⟩ := hs
  rw [analyticAt_pi_iff]
  intro i
  exact ReciprocityTheory.ChartRestriction.G.Geo.osgood d U (fun y => s y i) hU
    (fun y hy => differentiableWithinAt_pi.mp (hsU y hy) i) (A *ᵥ x) hxU

end FormIntegralPositivity


end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalCurveJacobian
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def NormalCurveJacobian.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) → ringKrullDim (MvPolynomial σ ℂ ⧸ I) = (1 : ℕ) →
      w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn I →
        ∃ (k : ℕ) (f : Fin k → MvPolynomial σ ℂ) (D : MvPolynomial σ ℂ),
          k + 1 = Fintype.card σ ∧ (∀ j, f j ∈ I) ∧
            LinearIndependent ℂ (fun j (i : σ) => eval w (pderiv i (f j))) ∧
            eval w D ≠ 0 ∧ ∀ p ∈ I, D * p ∈ Ideal.span (Set.range f)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StUniformiserGradientIndependent
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def UniformiserGradientIndependent.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) (t : MvPolynomial σ ℂ),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) →
    ringKrullDim (MvPolynomial σ ℂ ⧸ I) = (1 : ℕ) → w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn I →
    Irreducible (algebraMap (MvPolynomial σ ℂ) (pointLocalRing I w) t) →
      ∃ (k : ℕ) (f : Fin k → MvPolynomial σ ℂ), k + 1 = Fintype.card σ ∧ (∀ j, f j ∈ I) ∧
        LinearIndependent ℂ (Fin.cons (fun i ↦ eval w (pderiv i t)) (fun j i ↦ eval w (pderiv i (f j))) :
          Fin (k + 1) → σ → ℂ)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalModelPointOfPlace
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

theorem NormalModelPointOfPlace.proof (hLoc : NormalisationModelLocalization.Statement)
    (hMax : ModelLocalizationMaximalPoint.Statement) (hAt : LocalizationAtPrimeQuotient.Statement.{0}) :
    NormalModelPointOfPlace.Statement := by
  intro n J q M hJ P
  obtain ⟨e, he⟩ := hLoc n J q M hJ
  obtain ⟨P', hP'def⟩ : ∃ P' : @Ideal (Localization (normalModelSubmonoid M q)) CommSemiring.toSemiring,
      P' = P.asIdeal.comap (e.symm : Localization (normalModelSubmonoid M q) →+* curveNormalisation J q) :=
    ⟨_, rfl⟩
  have hP' : P'.IsMaximal := by
    rw [hP'def]
    exact Ideal.comap_isMaximal_of_surjective _ e.symm.surjective
  have hPp : P'.IsPrime := by
    rw [hP'def]
    infer_instance
  obtain ⟨w, hw, hq, hcomap⟩ := hMax n J q M P' hP'
  obtain ⟨eAt, heAt⟩ := hAt (MvPolynomial (Fin n ⊕ Fin M.m) ℂ) M.ideal (normalModelSubmonoid M q) P'
    (RingHom.ker (eval w : MvPolynomial (Fin n ⊕ Fin M.m) ℂ →+* ℂ)) hcomap
  let eP : Localization.AtPrime P.asIdeal ≃+* Localization.AtPrime P' :=
    IsLocalization.ringEquivOfRingEquiv (M := P.asIdeal.primeCompl) (T := P'.primeCompl)
      (Localization.AtPrime P.asIdeal) (Localization.AtPrime P') e (by
        ext y
        constructor
        · rintro ⟨x, hx, rfl⟩
          subst hP'def
          show e.symm (e x) ∉ P.asIdeal
          simpa using hx
        · intro hy
          subst hP'def
          exact ⟨e.symm y, hy, by simp⟩)
  refine ⟨w, hw, hq, fun f ↦ ?_⟩
  rw [← ord_ringEquiv (eP.trans eAt)]
  congr 1
  rw [RingEquiv.trans_apply, IsLocalization.ringEquivOfRingEquiv_eq, he, heAt]
  rfl

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.ExistsMulEqZeroOfMemAssociatedPrime
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing RingTheory.Sequence Pointwise

theorem weaklyRegular_eq_nil_of_socle {R M : Type*} [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    {z : M} (hz : z ≠ 0) (hk : ∀ r ∈ maximalIdeal R, r • z = 0) {rs : List R}
    (hm : ∀ r ∈ rs, r ∈ maximalIdeal R) (hreg : IsWeaklyRegular M rs) : rs = [] := by
  cases rs with
  | nil => rfl
  | cons r rs =>
    exfalso
    have h := ((isWeaklyRegular_cons_iff M r rs).mp hreg).1
    exact hz (h (show r • z = r • (0 : M) by rw [hk r (hm r List.mem_cons_self), smul_zero]))

theorem algebraMap_not_mem_map_of_colon_le {B : Type*} [CommRing B] (Q : Ideal B) [Q.IsPrime] (I : Ideal B)
    {y : B} (hy : ∀ r, r * y ∈ I → r ∈ Q) :
    algebraMap B (Localization.AtPrime Q) y ∉ I.map (algebraMap B (Localization.AtPrime Q)) := by
  intro h
  obtain ⟨⟨i, s⟩, hs⟩ := (IsLocalization.mem_map_algebraMap_iff Q.primeCompl _).mp h
  rw [← map_mul, IsLocalization.eq_iff_exists Q.primeCompl] at hs
  obtain ⟨c, hc⟩ := hs
  have h1 : (↑c * ↑s) * y ∈ I := by
    rw [show (↑c * ↑s) * y = ↑c * (y * ↑s) by ring, hc]
    exact I.mul_mem_left _ i.2
  have h2 := hy _ h1
  exact (Q.primeCompl.mul_mem c.2 s.2) h2

theorem mul_algebraMap_mem_map_of_le_colon {B : Type*} [CommRing B] (Q : Ideal B) [Q.IsPrime] (I : Ideal B)
    {y : B} (hy : ∀ r ∈ Q, r * y ∈ I) :
    ∀ m ∈ maximalIdeal (Localization.AtPrime Q),
      m * algebraMap B (Localization.AtPrime Q) y ∈ I.map (algebraMap B (Localization.AtPrime Q)) := by
  intro m hm
  rw [← Localization.AtPrime.map_eq_maximalIdeal] at hm
  have hle : Q.map (algebraMap B (Localization.AtPrime Q)) ≤
      (I.map (algebraMap B (Localization.AtPrime Q))).colon {algebraMap B (Localization.AtPrime Q) y} := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, Submodule.mem_colon_singleton, smul_eq_mul, ← map_mul]
    exact Ideal.mem_map_of_mem _ (hy r hr)
  have := hle hm
  rwa [Submodule.mem_colon_singleton, smul_eq_mul] at this

theorem ringKrullDim_le_zero_of_socle {L : Type*} [CommRing L] [IsLocalRing L] (hS : SerreSAt L 2)
    {z : L} (hz : z ≠ 0) (hk : ∀ m ∈ maximalIdeal L, m * z = 0) : ringKrullDim L ≤ 0 := by
  obtain ⟨rs, hm, hreg, hlen⟩ := hS
  have := weaklyRegular_eq_nil_of_socle hz (fun m hm => by rw [smul_eq_mul]; exact hk m hm) hm hreg
  subst this
  simp only [List.length_nil, Nat.cast_zero] at hlen
  exact (min_le_iff.mp hlen).resolve_left (by decide)

theorem exists_mul_eq_zero_of_mem_associatedPrime {B : Type*} [CommRing B] [IsNoetherianRing B]
    (hR : SerreR B 1) (hS : SerreS B 2) {Q : Ideal B} (hQ : IsAssociatedPrime Q B) {q : B} (hq : q ∈ Q) :
    ∃ t ∉ Q, t * q = 0 := by
  obtain ⟨hprime, y, rfl⟩ := isAssociatedPrime_iff.mp hQ
  set Q := (⊥ : Submodule B B).colon {y} with hQdef
  have hmem : ∀ r, r ∈ Q ↔ r * y = 0 := fun r => by
    rw [hQdef, Submodule.mem_colon_singleton, smul_eq_mul, Submodule.mem_bot]
  let L := Localization.AtPrime Q
  have hz : algebraMap B L y ≠ 0 := by
    have := algebraMap_not_mem_map_of_colon_le Q ⊥ (y := y) (fun r hr => (hmem r).mpr (by simpa using hr))
    simpa [Ideal.map_bot] using this
  have hk : ∀ m ∈ maximalIdeal L, m * algebraMap B L y = 0 := fun m hm => by
    have := mul_algebraMap_mem_map_of_le_colon Q ⊥ (y := y) (fun r hr => by simpa using (hmem r).mp hr) m hm
    simpa [Ideal.map_bot] using this
  have hdim := ringKrullDim_le_zero_of_socle (hS Q) hz hk
  have hreg : IsRegularLocalRing L := hR Q (hdim.trans (by decide))
  have hsf := (isRegularLocalRing_iff L).mp hreg
  have h0 : (maximalIdeal L).spanFinrank = 0 := by
    have : ((maximalIdeal L).spanFinrank : WithBot ℕ∞) ≤ 0 := hsf ▸ hdim
    exact Nat.le_zero.mp (by exact_mod_cast this)
  have hbot : maximalIdeal L = ⊥ :=
    (Submodule.spanFinrank_eq_zero_iff_eq_bot (maximalIdeal L).fg_of_isNoetherianRing).mp h0
  have hqm : algebraMap B L q ∈ maximalIdeal L := by
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff L Q]
    exact hq
  rw [hbot, Submodule.mem_bot, IsLocalization.map_eq_zero_iff Q.primeCompl] at hqm
  obtain ⟨⟨t, ht⟩, htq⟩ := hqm
  exact ⟨t, ht, htq⟩

theorem ringKrullDim_le_one_of_colon_span {B : Type*} [CommRing B] [IsNoetherianRing B] (hS : SerreS B 2)
    {b y : B} (hb : b ∈ nonZeroDivisors B) (Q : Ideal B) [Q.IsPrime]
    (hQ : ∀ r, r ∈ Q ↔ r * y ∈ Ideal.span {b}) : ringKrullDim (Localization.AtPrime Q) ≤ 1 := by
  set L := Localization.AtPrime Q
  set f := algebraMap B L
  have hbQ : b ∈ Q := (hQ b).mpr (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self b))
  have hbm : f b ∈ maximalIdeal L := (IsLocalization.AtPrime.to_map_mem_maximal_iff L Q b).mpr hbQ
  have hbL : f b ∈ nonZeroDivisors L :=
    IsLocalization.map_nonZeroDivisors_le Q.primeCompl L (Submonoid.mem_map_of_mem _ hb)
  have hbreg : IsSMulRegular L (f b) := fun u v huv => by
    simp only [smul_eq_mul] at huv
    have : (u - v) * f b = 0 := by rw [sub_mul, mul_comm u, mul_comm v, huv, sub_self]
    exact sub_eq_zero.mp ((mul_right_mem_nonZeroDivisors_eq_zero_iff hbL).mp this)
  have hmap : (Ideal.span {b}).map f = Ideal.span {f b} := by
    rw [Ideal.map_span, Set.image_singleton]
  have hsm : ∀ z : L, z ∈ f b • (⊤ : Submodule L L) ↔ z ∈ Ideal.span {f b} := fun z => by
    rw [Submodule.mem_smul_pointwise_iff_exists, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨w, -, hw⟩
      exact ⟨w, by rw [← hw, smul_eq_mul, mul_comm]⟩
    · rintro ⟨w, hw⟩
      exact ⟨w, trivial, by rw [smul_eq_mul, mul_comm, hw]⟩
  let zb : QuotSMulTop (f b) L := Submodule.Quotient.mk (f y)
  have hz : zb ≠ 0 := by
    intro h
    rw [Submodule.Quotient.mk_eq_zero, hsm, ← hmap] at h
    exact algebraMap_not_mem_map_of_colon_le Q _ (fun r hr => (hQ r).mpr hr) h
  have hk : ∀ m ∈ maximalIdeal L, m • zb = 0 := fun m hm => by
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, hsm, ← hmap, smul_eq_mul]
    exact mul_algebraMap_mem_map_of_le_colon Q _ (fun r hr => (hQ r).mp hr) m hm
  obtain ⟨rs, hm, hreg, hlen⟩ := hS Q
  obtain ⟨rs', hlen', hm', hreg'⟩ := GroundTheory.Heights₂.Heights.exists_isRegular_quotSMulTop hm hreg hbreg hbm
  have hnil := weaklyRegular_eq_nil_of_socle hz hk hm' hreg'.toIsWeaklyRegular
  subst hnil
  simp only [List.length_nil] at hlen'
  have h1 : rs.length ≤ 1 := by omega
  have h2 : min (2 : WithBot ℕ∞) (ringKrullDim L) ≤ 1 := hlen.trans (by exact_mod_cast h1)
  exact (min_le_iff.mp h2).resolve_left (by decide)

theorem isReduced_of_serre {B : Type*} [CommRing B] [IsNoetherianRing B] (hR : SerreR B 1) (hS : SerreS B 2) :
    IsReduced B := by
  refine ⟨fun x hx => ?_⟩
  by_contra hx0
  obtain ⟨Q, hQ, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing B x hx0
  have hprime : Q.IsPrime := hQ.isPrime
  obtain ⟨n, hn⟩ := hx
  have hxQ : x ∈ Q := hprime.mem_of_pow_mem n (by rw [hn]; exact Q.zero_mem)
  obtain ⟨t, ht, htx⟩ := exists_mul_eq_zero_of_mem_associatedPrime hR hS hQ hxQ
  exact ht (hle (by rw [Submodule.mem_colon_singleton, smul_eq_mul, Submodule.mem_bot]; exact htx))

theorem isIntegrallyClosed_of_serre {B : Type} [CommRing B] [IsNoetherianRing B] (hR : SerreR B 1)
    (hS : SerreS B 2) : IsIntegrallyClosed B := by
  refine isIntegrallyClosedIn_iff.mpr ⟨IsLocalization.injective (FractionRing B) le_rfl, fun {x} hx => ?_⟩
  obtain ⟨⟨a, ⟨b, hb⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors B) x
  suffices ha : a ∈ Ideal.span {b} by
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp ha
    exact ⟨c, by rw [IsLocalization.eq_mk'_iff_mul_eq, ← map_mul, hc]⟩
  by_contra ha
  have ha0 : (Ideal.Quotient.mk (Ideal.span {b}) a) ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨Q, hQ, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing B _ ha0
  obtain ⟨hprime, yb, hyb⟩ := isAssociatedPrime_iff.mp hQ
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective yb
  have hcol : ∀ r z : B, r ∈ (⊥ : Submodule B (B ⧸ Ideal.span {b})).colon {Ideal.Quotient.mk _ z} ↔
      r * z ∈ Ideal.span {b} := fun r z => by
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot, ← Ideal.Quotient.eq_zero_iff_mem, map_mul,
      Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
  have hQy : ∀ r, r ∈ Q ↔ r * y ∈ Ideal.span {b} := fun r => by rw [hyb, hcol]
  have haQ : ∀ r, r * a ∈ Ideal.span {b} → r ∈ Q := fun r hr => hle ((hcol r a).mpr hr)
  set L := Localization.AtPrime Q
  set f := algebraMap B L
  have hdim := ringKrullDim_le_one_of_colon_span hS hb Q hQy
  have : IsRegularLocalRing L := hR Q hdim
  have : IsDomain L := GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.isDomain
  have hic : IsIntegrallyClosed L :=
    GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.isIntegrallyClosed_of_ringKrullDim_le_one hdim
  have hnz : ∀ s ∈ nonZeroDivisors B, f s ∈ nonZeroDivisors L := fun s hs =>
    IsLocalization.map_nonZeroDivisors_le Q.primeCompl L (Submonoid.mem_map_of_mem _ hs)
  let K := FractionRing L
  let g : B →+* K := (algebraMap L K).comp f
  have hg : ∀ s : nonZeroDivisors B, IsUnit (g s) := fun s =>
    IsLocalization.map_units K (⟨f s, hnz s s.2⟩ : nonZeroDivisors L)
  let φ : FractionRing B →+* K := IsLocalization.lift hg
  have hφ : ∀ r, φ (algebraMap B (FractionRing B) r) = g r := IsLocalization.lift_eq hg
  have hint : IsIntegral L (φ (IsLocalization.mk' (FractionRing B) a ⟨b, hb⟩)) := by
    obtain ⟨p, hp, hpx⟩ := hx
    refine ⟨p.map f, hp.map f, ?_⟩
    rw [Polynomial.eval₂_map, show (algebraMap L K).comp f = φ.comp (algebraMap B (FractionRing B)) from
      (IsLocalization.lift_comp hg).symm, ← Polynomial.hom_eval₂, hpx, map_zero]
  obtain ⟨c, hc⟩ := (isIntegrallyClosedIn_iff.mp hic).2 hint
  have h1 : φ (IsLocalization.mk' (FractionRing B) a ⟨b, hb⟩) * g b = g a := by
    rw [← hφ, ← hφ, ← map_mul, IsLocalization.mk'_spec]
  have h2 : c * f b = f a := IsFractionRing.injective L K (by rw [map_mul, hc]; exact h1)
  apply algebraMap_not_mem_map_of_colon_le Q (Ideal.span {b}) haQ
  rw [← h2]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self b))

theorem isDomain_of_serre {B : Type} [CommRing B] [IsLocalRing B] [IsNoetherianRing B] (hR : SerreR B 1)
    (hS : SerreS B 2) : IsDomain B := by
  have hred : IsReduced B := isReduced_of_serre hR hS
  have hic : IsIntegrallyClosed B := isIntegrallyClosed_of_serre hR hS
  refine @NoZeroDivisors.to_isDomain B _ _ ⟨fun {u v} huv => ?_⟩
  by_contra! h
  obtain ⟨hu, hv⟩ := h
  let J : Ideal B := Ideal.span {u} ⊔ (⊥ : Submodule B B).colon {u}
  have hJ : ∃ s ∈ J, s ∈ nonZeroDivisors B := by
    by_contra! hJ
    have hsub : (J : Set B) ⊆ ⋃ p ∈ associatedPrimes B B, (p : Set B) := by
      rw [biUnion_associatedPrimes_eq_compl_nonZeroDivisors]
      exact fun s hs => hJ s hs
    obtain ⟨Q, hQ, hJQ⟩ := (Ideal.subset_union_prime_finite (associatedPrimes.finite B B) (f := id) ⊥ ⊥
      (fun Q hQ _ _ => hQ.isPrime)).mp hsub
    obtain ⟨t, ht, htu⟩ := exists_mul_eq_zero_of_mem_associatedPrime hR hS hQ
      (hJQ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self u)))
    exact ht (hJQ (Ideal.mem_sup_right (by
      rw [Submodule.mem_colon_singleton, smul_eq_mul, Submodule.mem_bot]; exact htu)))
  obtain ⟨s, hsJ, hs⟩ := hJ
  obtain ⟨x, hx, w, hw, rfl⟩ := Submodule.mem_sup.mp hsJ
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hx
  have hwu : w * u = 0 := by
    rwa [Submodule.mem_colon_singleton, smul_eq_mul, Submodule.mem_bot] at hw
  have hxy : r * u * w = 0 := by rw [mul_assoc, mul_comm u w, hwu, mul_zero]
  let e := IsLocalization.mk' (FractionRing B) (r * u) (⟨r * u + w, hs⟩ : nonZeroDivisors B)
  have he : e * e = e := by
    rw [← IsLocalization.mk'_mul, IsLocalization.mk'_eq_iff_eq]
    congr 1
    simp only [Submonoid.coe_mul]
    linear_combination (-(r * u + w)) * hxy
  have hint : IsIntegral B e := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X, ?_, ?_⟩
    · exact Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X]; norm_num)
    · simp [Polynomial.eval₂_sub, pow_two, he]
  obtain ⟨c, hc⟩ := (isIntegrallyClosedIn_iff.mp hic).2 hint
  have hc' : c * (r * u + w) = r * u := by
    rw [IsLocalization.eq_mk'_iff_mul_eq] at hc
    exact IsLocalization.injective (FractionRing B) le_rfl (by rw [map_mul]; exact hc)
  have h1 : c * (w * w) = 0 := by linear_combination w * hc' + (1 - c) * hxy
  have h2 : (1 - c) * ((r * u) * (r * u)) = 0 := by linear_combination (-(r * u)) * hc' + c * hxy
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self c with hc1 | hc1
  · have hw0 : w = 0 := IsReduced.eq_zero w ⟨2, by rw [pow_two]; exact (hc1.mul_right_eq_zero).mp h1⟩
    subst hw0
    rw [add_zero] at hs
    apply hv
    exact (mul_left_mem_nonZeroDivisors_eq_zero_iff hs).mp (by rw [mul_assoc, huv, mul_zero])
  · have hx0 : r * u = 0 := IsReduced.eq_zero _ ⟨2, by rw [pow_two]; exact (hc1.mul_right_eq_zero).mp h2⟩
    rw [hx0, zero_add] at hs
    exact hu ((mul_left_mem_nonZeroDivisors_eq_zero_iff hs).mp hwu)

theorem SerreNormalOfRegularDepth.proof : SerreNormalOfRegularDepth.Statement := by
  intro A _ hA hR hS P _
  set B := Localization.AtPrime P
  have hRB : SerreR B 1 := fun Q _ =>
    (hR (Q.comap (algebraMap A B))).of_ringEquiv
      (IsLocalization.localizationLocalizationAtPrimeIsoLocalization P.primeCompl Q).toRingEquiv
  have hSB : SerreS B 2 := fun Q _ =>
    (hS (Q.comap (algebraMap A B))).of_ringEquiv
      (IsLocalization.localizationLocalizationAtPrimeIsoLocalization P.primeCompl Q).toRingEquiv
  exact ⟨isDomain_of_serre hRB hSB, isIntegrallyClosed_of_serre hRB hSB⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPrimePlaceBranchExists
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

theorem PrimePlaceBranchExists.proof (hA : NormalModelPointOfPlace.Statement) (hB : NormalModelDisc.Statement)
    (hC : NormalModelProjectionLocallyInjective.Statement) (hO : NormalCurveBranchOrder.Statement) :
    PrimePlaceBranchExists.Statement := by
  intro n J q hJ hdim P

  have hq : q ∈ zeroSet J := by
    by_contra h
    have := curveLocalRing_subsingleton J q h
    rw [ringKrullDim_eq_bot_of_subsingleton] at hdim
    exact absurd hdim (by decide)
  have hle : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≤ (n : ℕ) := by
    refine (ringKrullDim_quotient_le J).trans ?_
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  obtain ⟨e, he⟩ : ∃ e : ℕ, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = e := by
    have h0 : (0 : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) :=
      ringKrullDim_nonneg_of_nontrivial
    generalize ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d at h0 hle ⊢
    induction d using WithBot.recBotCoe with
    | bot => simp at h0
    | coe x =>
      induction x using ENat.recTopCoe with
      | top =>
        exfalso
        simp only [not_le.2 (show ((n : ℕ) : WithBot ℕ∞) < ((⊤ : ℕ∞) : WithBot ℕ∞) from
          WithBot.coe_lt_coe.2 (ENat.natCast_lt_top n))] at hle
      | coe e => exact ⟨e, rfl⟩
  have hloc : ringKrullDim (curveLocalRing J q) = (e : ℕ) := LocalDimDomain.proof n e J hJ he q hq
  have hdim1 : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (1 : ℕ) := by
    rw [he]
    rw [hloc] at hdim
    exact_mod_cast hdim
  obtain ⟨M⟩ := IndefiniteRowSideFullHecke.ComplexSets.NormalModelExists.proof n J hJ
  obtain ⟨w, hw, hwq, hord⟩ := hA n J q M hJ P
  obtain ⟨r, hr, φ, hφd, hφi, hφm, hφ0⟩ := hB n J M w hJ hdim1 hw
  obtain ⟨U, hU, hUi⟩ := hC n J M w hJ hdim1 hw

  have hcont : ContinuousAt φ 0 := hφd.continuousOn.continuousAt (Metric.ball_mem_nhds 0 hr)
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.1 (hcont.preimage_mem_nhds (hφ0 ▸ hU))
  have hρ : 0 < min r ε := lt_min hr hε
  have hsub : Metric.ball (0 : Fin 1 → ℂ) (min r ε) ⊆ Metric.ball 0 r :=
    Metric.ball_subset_ball (min_le_left _ _)
  have hsubU : ∀ t ∈ Metric.ball (0 : Fin 1 → ℂ) (min r ε), φ t ∈ U := fun t ht ↦
    hεU (Metric.ball_subset_ball (min_le_right _ _) ht)
  let ν : VarBranch J 1 q :=
    { radius := min r ε, radius_pos := hρ, toFun := fun t i ↦ φ t (Sum.inl i),
      differentiableOn := differentiableOn_pi.2 fun i ↦ differentiableOn_pi.1 (hφd.mono hsub) (Sum.inl i),
      injOn := fun a ha b hb hab ↦ hφi (hsub ha) (hsub hb)
        (hUi ⟨hφm (hsub ha), hsubU a ha⟩ ⟨hφm (hsub hb), hsubU b hb⟩ hab),
      map_zero := by
        funext i
        rw [hφ0]
        exact congrFun hwq i,
      mapsTo := fun t ht g hg ↦ by
        have hg' : rename Sum.inl g ∈ M.ideal := Ideal.mem_comap.1 (M.comap_eq.symm ▸ hg)
        have h := hφm (hsub ht) _ hg'
        rw [eval_rename] at h
        exact h }
  refine ⟨ν, fun f ↦ ?_⟩
  rw [hord f, hO n J M w (min r ε) φ hJ hdim1 hρ (hφd.mono hsub) (hφi.mono hsub) (fun t ht ↦ hφm (hsub ht)) hφ0]
  unfold branchOrder
  simp only [eval_rename]
  rfl

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRegFormCompare
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix Filter Topology ReciprocityTheory.AnForm ComplexSets
open scoped ContDiff ComplexOrder

noncomputable section

namespace RegularizedFormComparison

open TubeFormComparison

theorem posSemidef_hessC_logReg_comp {n D : ℕ} (u : Fin n → ℂ) {ε : ℝ} (hε : 0 < ε)
    (s : (Fin D → ℂ) → Fin n → ℂ) (y : Fin D → ℂ) (hs : AnalyticAt ℂ s y) :
    (hessC (logReg u ε ∘ s) y).PosSemidef := by
  set τ : (Fin D → ℂ) → Fin 1 → ℂ := fun z _ => ((√ε : ℝ) : ℂ)⁻¹ * linEval u (s z) with hτ
  have hτa : AnalyticAt ℂ τ y := by
    refine analyticAt_pi_iff.2 fun _ => analyticAt_const.mul ?_
    unfold linEval
    exact Finset.analyticAt_fun_sum (f := fun j z => u j * s z j) _ fun j _ =>
      analyticAt_const.mul (analyticAt_pi_iff.1 hs j)
  have hsq : ((√ε : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hε).ne'
  have he : logReg u ε ∘ s =
      fun z => (1 / 2 : ℝ) * HilbertSamuel.ProjFS.logPot (τ z) + Real.log ε / 2 := by
    funext z
    have h1 : HilbertSamuel.ProjFS.logPot (τ z) = Real.log (1 + ‖linEval u (s z)‖ ^ 2 / ε) := by
      show Real.log (1 + euclPot (τ z)) = _
      congr 2
      simp only [euclPot, hτ, Finset.univ_unique, Finset.sum_singleton, norm_mul, norm_inv, mul_pow,
        inv_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg ε),
        Real.sq_sqrt hε.le]
      ring
    have h2 : ‖linEval u (s z)‖ ^ 2 + ε = ε * (1 + ‖linEval u (s z)‖ ^ 2 / ε) := by
      field_simp
      ring
    simp only [Function.comp_apply, logReg]
    rw [h1, h2, Real.log_mul hε.ne' (by positivity)]
    ring
  have hconst : ∀ (F : (Fin D → ℂ) → ℝ) (c : ℝ), hessC (fun z => F z + c) y = hessC F y := by
    intro F c
    have h : fderiv ℝ (fun z => F z + c) = fderiv ℝ F := funext fun z => fderiv_add_const c
    unfold hessC
    rw [h]
  have hL2 : ContDiffAt ℝ 2 (HilbertSamuel.ProjFS.logPot (N := 1)) (τ y) :=
    ((SheetFormComparison.contDiff_logPot 1).of_le (WithTop.coe_le_coe.2 le_top)).contDiffAt
  rw [he, hconst (fun z => (1 / 2 : ℝ) * HilbertSamuel.ProjFS.logPot (τ z)),
    ReciprocityTheory.AnForm.M.hessC_const_mul']
  have hcomp : hessC (fun z => HilbertSamuel.ProjFS.logPot (τ z)) y =
      hessC (HilbertSamuel.ProjFS.logPot ∘ τ) y := rfl
  rw [hcomp, ReciprocityTheory.AnForm.A.hessC_comp _ τ y hτa hL2]
  have hP : (hessC (HilbertSamuel.ProjFS.logPot (N := 1)) (τ y)).PosSemidef :=
    ReciprocityTheory.AnForm.M.hessC_posSemidef _ _ hL2 fun w => HilbertSamuel.ProjFS.levi_logPot_nonneg _ w
  set B := (ReciprocityTheory.AnForm.A.jacC τ y).map (starRingEnd ℂ) with hB
  have hBJ : Bᴴ = (ReciprocityTheory.AnForm.A.jacC τ y)ᵀ := by
    ext a b
    simp [hB]
  rw [← hBJ]
  exact (hP.conjTranspose_mul_mul_same B).smul (Complex.zero_le_real.2 (by norm_num))

theorem maDens_euclPot_nonneg {n d : ℕ} (g : (Fin n → ℂ) → ℝ) (s : (Fin (d + 1) → ℂ) → Fin n → ℂ)
    (y : Fin (d + 1) → ℂ) (hs : AnalyticAt ℂ s y) (hM : (hessC (g ∘ s) y).PosSemidef) :
    0 ≤ maDens (fun k => vecCons g (fun _ : Fin d => euclPot) k ∘ s) y := by
  have hE2 : ∀ _ : Fin d, ContDiffAt ℝ 2 (euclPot : (Fin n → ℂ) → ℝ) (s y) := fun _ =>
    ((contDiff_euclPot n).of_le (WithTop.coe_le_coe.2 le_top)).contDiffAt
  have hb : ∀ _ : Fin d, (hessC (euclPot : (Fin n → ℂ) → ℝ) (s y) + ((1 : ℝ) : ℂ) • 1).PosSemidef ∧
      (-hessC (euclPot : (Fin n → ℂ) → ℝ) (s y) + ((1 : ℝ) : ℂ) • 1).PosSemidef := fun _ => by
    rw [hessC_euclPot]
    refine ⟨?_, ?_⟩
    · simpa using Matrix.PosSemidef.one.add Matrix.PosSemidef.one
    · simpa using (Matrix.PosSemidef.zero : (0 : Matrix (Fin n) (Fin n) ℂ).PosSemidef)
  have key := abs_maDens_cons_le g (fun _ : Fin d => euclPot) s y hs hE2 hb hM
  have h0 := (abs_nonneg _).trans key
  rw [one_pow, mul_one] at h0
  exact nonneg_of_mul_nonneg_right h0 (by positivity)

end RegularizedFormComparison


open TubeFormComparison RegularizedFormComparison in
theorem RegFormCompare.proof : RegFormCompare.Statement := by
  intro n d J A φ f _hJ _hdim hA hφ hfc hfs
  set K := zeroSet J ∩ tsupport f with hKdef
  have hK : IsCompact K := hfs.isCompact.inter_left (isClosed_zeroSet J)
  choose U hU hZU hφU using hφ
  obtain ⟨c, hc, hb⟩ := exists_hessC_bound φ K hK U hU
    (fun i => Set.inter_subset_left.trans (hZU i)) (fun i => (hφU i).of_le (WithTop.coe_le_coe.2 le_top))
  obtain ⟨M, hM⟩ := hfc.bounded_above_of_compact_support hfs
  have hM0 : 0 ≤ max M 0 := le_max_right _ _
  have hC : 0 ≤ max M 0 * (3 ^ (d + 1) * c ^ d) := by positivity
  refine ⟨max M 0 * (3 ^ (d + 1) * c ^ d), hC, fun u ε hε v w hw hvw y => ?_⟩
  unfold chartDens chartAbsDens sheetSum
  rw [finsum_mem_eq_finite_toFinset_sum _ (IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y),
    finsum_mem_eq_finite_toFinset_sum _ (IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y), Finset.mul_sum]
  refine Finset.sum_le_sum fun x hx => ?_
  rw [Set.Finite.mem_toFinset] at hx
  obtain ⟨hxZ, hxy⟩ := hx
  subst hxy
  split_ifs with hsx
  swap
  · simp
  dsimp only
  obtain ⟨V, hV, hyV, hsd, hsx', -, -⟩ := hsx.choose_spec
  set s := hsx.choose with hsdef
  have hsa : AnalyticAt ℂ s (A *ᵥ x) :=
    analyticAt_pi_iff.2 fun i =>
      ReciprocityTheory.AnForm.Osgood.osgood _ V (fun z => s z i) hV (differentiableOn_pi.1 hsd i) _ hyV
  have hMs := posSemidef_hessC_logReg_comp u hε s (A *ᵥ x) hsa
  have hE := maDens_euclPot_nonneg (logReg u ε) s (A *ᵥ x) hsa hMs
  by_cases hxf : x ∈ tsupport f
  · have hφx : ∀ i, ContDiffAt ℝ 2 (φ i) (s (A *ᵥ x)) := fun i => by
      rw [hsx']
      exact ((hφU i).contDiffAt ((hU i).mem_nhds (hZU i hxZ))).of_le (WithTop.coe_le_coe.2 le_top)
    have hbx : ∀ i, (hessC (φ i) (s (A *ᵥ x)) + (c : ℂ) • 1).PosSemidef ∧
        (-hessC (φ i) (s (A *ᵥ x)) + (c : ℂ) • 1).PosSemidef := fun i => by
      rw [hsx']
      exact hb i x ⟨hxZ, hxf⟩
    have key := abs_maDens_cons_le _ φ s (A *ᵥ x) hsa hφx hbx hMs
    have hfx : |f x| ≤ max M 0 := (Real.norm_eq_abs (f x) ▸ hM x).trans (le_max_left _ _)
    have hvx : |v x| ≤ w x := hvw x hxf
    rw [abs_mul, abs_mul]
    calc |v x| * |f x| * |maDens (fun k => vecCons (logReg u ε) φ k ∘ s) (A *ᵥ x)|
        ≤ w x * max M 0 * (3 ^ (d + 1) * c ^ d *
            maDens (fun k => vecCons (logReg u ε) (fun _ => euclPot) k ∘ s) (A *ᵥ x)) := by
          have hwx := hw x
          have hK0 : 0 ≤ (3 : ℝ) ^ (d + 1) * c ^ d := by positivity
          have h1 : |v x| * |f x| ≤ w x * max M 0 := mul_le_mul hvx hfx (abs_nonneg _) (hw x)
          calc |v x| * |f x| * |maDens (fun k => vecCons (logReg u ε) φ k ∘ s) (A *ᵥ x)|
              ≤ w x * max M 0 * |maDens (fun k => vecCons (logReg u ε) φ k ∘ s) (A *ᵥ x)| :=
                mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
            _ ≤ _ := mul_le_mul_of_nonneg_left key (mul_nonneg hwx hM0)
      _ = _ := by ring
  · rw [image_eq_zero_of_notMem_tsupport hxf, mul_zero, zero_mul, abs_zero]
    exact mul_nonneg hC (mul_nonneg (hw x) hE)

end

end GroundTheory.Heights₂.Heights
end
