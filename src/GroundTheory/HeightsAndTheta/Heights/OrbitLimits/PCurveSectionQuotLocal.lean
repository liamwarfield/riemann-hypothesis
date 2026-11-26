module

public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveVertPointLengthSteps

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveSectionQuotLocal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.HilbertSamuel.LiftBirationalAmple

noncomputable section

namespace CurveSectionQuotientLocal

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  (y : (Σ k, ι k) → Ω)

theorem chart_mem_curveSectionMod (c : ∀ k, ι k) (d : K → ℕ) :
    ∏ k, y ⟨k, c k⟩ ^ d k ∈ curveSectionMod y (fun k => (d k : ℤ)) := by
  classical
  show _ ∈ chartLat y _ 1
  have h := chartLat_prod (y := y) Finset.univ (fun k => y ⟨k, c k⟩ ^ d k)
    (fun k => d k • (Pi.single k 1 : K → ℤ))
    (fun k _ => chartLat_pow (chartLat_var (y := y) ⟨k, c k⟩) (d k))
  convert h using 2
  funext j
  rw [Finset.sum_apply, Finset.sum_eq_single j]
  · simp
  · intro k _ hk
    simp [Ne.symm hk]
  · simp


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem exists_mul_mem_of_mem_chartRingZ (m : Ideal (curveRing y)) (hm : m.IsPrime) (c : ∀ k, ι k)
    (h : ∀ p : Σ k, ι k, ∃ a b : curveRing y, b ∉ m ∧ (b : Ω) * (y p / y ⟨p.1, c p.1⟩) = a)
    {z : Ω} (hz : z ∈ chartRingZ y c) :
    ∃ a b : curveRing y, b ∉ m ∧ (b : Ω) * z = a := by
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    exact h p
  | algebraMap r =>
    refine ⟨(r : curveRing y), 1, (Ideal.ne_top_iff_one m).mp hm.ne_top, ?_⟩
    simp
  | add x z _ _ hx hz =>
    obtain ⟨a₁, b₁, hb₁, e₁⟩ := hx
    obtain ⟨a₂, b₂, hb₂, e₂⟩ := hz
    refine ⟨b₂ * a₁ + b₁ * a₂, b₁ * b₂, fun hmem => (hm.mem_or_mem hmem).elim hb₁ hb₂, ?_⟩
    push_cast
    rw [← e₁, ← e₂]
    ring
  | mul x z _ _ hx hz =>
    obtain ⟨a₁, b₁, hb₁, e₁⟩ := hx
    obtain ⟨a₂, b₂, hb₂, e₂⟩ := hz
    refine ⟨a₁ * a₂, b₁ * b₂, fun hmem => (hm.mem_or_mem hmem).elim hb₁ hb₂, ?_⟩
    push_cast
    rw [← e₁, ← e₂]
    ring

end CurveSectionQuotientLocal


open CurveSectionQuotientLocal in
theorem CurveSectionQuotLocal.proof : CurveSectionQuotLocal.Statement := by
  intro K _ ι _ Ω _ y s d _hy _hs _hsP m c hm hc hrat a b hb hba
  set x := aeval y s with hx_def
  set e₀ : Ω := ∏ k, y ⟨k, c k⟩ ^ d k with he₀_def
  have he₀ : e₀ ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)

  let e : curveSectionMod y (fun k => (d k : ℤ)) := ⟨e₀, chart_mem_curveSectionMod y c d⟩
  let φ : curveRing y →ₗ[curveRing y] curveSectionQuot y (fun k => (d k : ℤ)) x :=
    LinearMap.toSpanSingleton (curveRing y) _ (Submodule.Quotient.mk e)
  have hφ : ∀ β : curveRing y, φ β = Submodule.Quotient.mk (β • e) := fun β => by
    simp [φ, Submodule.Quotient.mk_smul]
  have hφ0 : ∀ β : curveRing y, φ β = 0 ↔ ∃ γ : curveRing y, (γ : Ω) * x = β * e₀ := by
    intro β
    rw [hφ, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.mem_span_singleton]
    rfl
  have hle : Ideal.span {a} ≤ LinearMap.ker φ := by
    rw [Ideal.span_singleton_le_iff_mem, LinearMap.mem_ker, hφ0]
    exact ⟨b, hba⟩
  let ψ : (curveRing y ⧸ Ideal.span {a}) →ₗ[curveRing y] curveSectionQuot y (fun k => (d k : ℤ)) x :=
    (Ideal.span {a}).liftQ φ hle

  have hker : ∀ q, ψ q = 0 → b • q = 0 := by
    intro q hq
    obtain ⟨β, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨γ, hγ⟩ := (hφ0 β).mp hq
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul,
      Ideal.mem_span_singleton']
    refine ⟨γ, Subtype.ext ?_⟩
    push_cast
    apply mul_right_cancel₀ he₀
    rw [mul_assoc, ← hba, mul_assoc, ← hγ]
    ring

  have hsurj0 : ∀ n : curveSectionMod y (fun k => (d k : ℤ)),
      ∃ r : curveRing y, r ∉ m ∧ ∃ β : curveRing y, r • n = β • e := by
    intro n
    have hn : (n : Ω) ∈ chartLat y (fun k => (d k : ℤ)) 1 := n.2
    have hnc : (n : Ω) * e₀⁻¹ ∈ chartRingZ y c := by
      have h1 := (mem_chartLat_one y).mp hn c hc
      have h2 : ∏ k, y ⟨k, c k⟩ ^ (-((fun k => (d k : ℤ)) k)) = e₀⁻¹ := by
        rw [he₀_def, ← Finset.prod_inv_distrib]
        refine Finset.prod_congr rfl fun k _ => ?_
        rw [zpow_neg, zpow_natCast]
      rwa [h2] at h1
    obtain ⟨β, r, hr, hβ⟩ := exists_mul_mem_of_mem_chartRingZ y m hm c hrat hnc
    refine ⟨r, hr, β, Subtype.ext ?_⟩
    show (r : Ω) * n = β * e₀
    rw [← hβ]
    field_simp

  let S := m.primeCompl
  let Φ := IsLocalizedModule.map S (LocalizedModule.mkLinearMap S (curveRing y ⧸ Ideal.span {a}))
    (LocalizedModule.mkLinearMap S (curveSectionQuot y (fun k => (d k : ℤ)) x)) ψ
  have hΦ : ∀ q (r : S), Φ (LocalizedModule.mk q r) = LocalizedModule.mk (ψ q) r :=
    fun q r => IsLocalizedModule.map_LocalizedModules S _ q r
  have hinj : Function.Injective Φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro z
    refine LocalizedModule.induction_on (β := fun z => Φ z = 0 → z = 0) (fun q r hz => ?_) z
    rw [hΦ, ← LocalizedModule.zero_mk r, LocalizedModule.mk_eq] at hz
    obtain ⟨u, hu⟩ := hz
    simp only [smul_zero, Submonoid.smul_def] at hu
    rw [← map_smul, ← map_smul] at hu
    have hq := hker _ hu
    rw [← LocalizedModule.zero_mk r, LocalizedModule.mk_eq]
    refine ⟨⟨b * u, S.mul_mem hb u.2⟩, ?_⟩
    simp only [smul_zero, Submonoid.smul_def, mul_smul]
    exact hq
  have hsurj : Function.Surjective Φ := by
    intro z
    refine LocalizedModule.induction_on (β := fun z => ∃ w, Φ w = z) (fun n r => ?_) z
    obtain ⟨n', rfl⟩ := Submodule.Quotient.mk_surjective _ n
    obtain ⟨r', hr', β, hβ⟩ := hsurj0 n'
    refine ⟨LocalizedModule.mk (Submodule.Quotient.mk β) (⟨r', hr'⟩ * r), ?_⟩
    rw [hΦ]
    have hψ : ψ (Submodule.Quotient.mk β) = Submodule.Quotient.mk (β • e) := by
      rw [← hφ]
      rfl
    rw [hψ, ← hβ, Submodule.Quotient.mk_smul]
    exact LocalizedModule.mk_cancel_common_left ⟨r', hr'⟩ r _
  have := hm
  let E := (LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩).extendScalarsOfIsLocalization S
    (Localization.AtPrime m)
  unfold locLen
  rw [dite_eq_left hm, dite_eq_left hm, E.length_eq]

end

end GroundTheory.Heights₂.Heights.Targets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveVertPointNagata
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

instance isPrime_map_C_maximalIdeal_mv (K : Type*) (R : Type*) [CommRing R] [IsLocalRing R] :
    ((IsLocalRing.maximalIdeal R).map (MvPolynomial.C : R →+* MvPolynomial K R)).IsPrime := by
  rw [← Ideal.mk_ker (I := IsLocalRing.maximalIdeal R), ← MvPolynomial.ker_map]
  exact RingHom.ker_isPrime _

abbrev mNagataRing (K : Type*) (R : Type*) [CommRing R] [IsLocalRing R] : Type _ :=
  Localization.AtPrime ((IsLocalRing.maximalIdeal R).map (MvPolynomial.C : R →+* MvPolynomial K R))

def CurveVertPointNagata.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (s : MRing ι) (d : K → ℕ),
    IsArithVar (mCoordIdeal y) 1 → ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s d → s ∉ mCoordIdeal y →
      ∀ W ∈ divSupp (mCoordIdeal y) s, ∀ c : ∀ k, ι k, (∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ W) →
        ∀ [W.IsPrime] [(curvePtIdeal y W).IsPrime] (a b : (Σ k, ι k) → curveRing y)
          (hb : ∀ p, b p ∉ curvePtIdeal y W), (∀ p, (b p : Ω) * (y p / y ⟨p.1, c p.1⟩) = a p) →
          ∃ Φ : Localization.AtPrime W →+* mNagataRing K (Localization.AtPrime (curvePtIdeal y W)),
            Function.Surjective Φ ∧
            RingHom.ker Φ = (mCoordIdeal y).map (algebraMap (MRing ι) _) ∧
            ∀ f : MRing ι, Φ (algebraMap _ _ f) =
              algebraMap (MvPolynomial K (Localization.AtPrime (curvePtIdeal y W))) _
                (aeval (fun p : (Σ k, ι k) => MvPolynomial.C (IsLocalization.mk'
                  (Localization.AtPrime (curvePtIdeal y W)) (a p)
                  (⟨b p, hb p⟩ : (curvePtIdeal y W).primeCompl)) * MvPolynomial.X p.1) f)

end

end GroundTheory.Heights₂.Heights.Targets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveVertPointLength
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

namespace CurveVerticalPointLength

theorem maximal_and_mult_eq (hCh : CurveVertPointChart.Statement) (hMC : CurveVertPointMultChart.Statement)
    (hSQ : CurveSectionQuotLocal.Statement) {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {Ω : Type} [Field Ω] {y : (Σ k, ι k) → Ω} {s : MRing ι} {d : K → ℕ}
    (hP : IsArithVar (mCoordIdeal y) 1) (hs : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s d) (hsP : s ∉ mCoordIdeal y)
    {W : Ideal (MRing ι)} (hW : W ∈ divSupp (mCoordIdeal y) s) :
    (curvePtIdeal y W).IsMaximal ∧
      multAt (mCoordIdeal y ⊔ Ideal.span {s}) W =
        locLen (curvePtIdeal y W) (curveSectionQuot y (fun k => (d k : ℤ)) (aeval y s)) := by
  choose c hc using hW.2
  obtain ⟨hmax, hrat, hmem⟩ := hCh K ι Ω y s d hP hs hsP W hW c hc
  have hPW : mCoordIdeal y ≤ W := le_trans le_sup_left hW.1.1.2
  have hsW : s ∈ W := hW.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => ne_zero_of_X_notMem fun h => hc k (hPW h)
  obtain ⟨a, b, -, hb, hab⟩ := (hmem d s hs).mp hsW
  refine ⟨hmax, ?_⟩
  rw [hMC K ι Ω y s d hP hs hsP W hW c hc a b hb hab,
    hSQ K ι Ω y s d hP hs hsP _ c hmax.isPrime hyc hrat a b hb hab]

end CurveVerticalPointLength

theorem CurveVertPointLength.proof (hCh : CurveVertPointChart.Statement) (hInj : CurveVertPointInj.Statement)
    (hSurj : CurveVertPointSurj.Statement) (hMC : CurveVertPointMultChart.Statement)
    (hSQ : CurveSectionQuotLocal.Statement) : CurveVertPointLength.Statement := by
  intro K _ ι _ Ω _ y s d hP hs hsP
  refine ⟨⟨fun W hW => ?_, hInj K ι Ω y s d hP hs hsP,
      fun m hm => hSurj K ι Ω y s d hP hs hsP m hm.1 hm.2⟩,
    fun W hW => (CurveVerticalPointLength.maximal_and_mult_eq hCh hMC hSQ hP hs hsP hW).2⟩
  obtain ⟨hmax, hmult⟩ := CurveVerticalPointLength.maximal_and_mult_eq hCh hMC hSQ hP hs hsP hW
  exact ⟨hmax, hmult ▸ (IndefiniteRowSideFullHecke.Inter.multAt_pos_of_mem_divSupp hW).ne'⟩

end

end GroundTheory.Heights₂.Heights.Targets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveVertPointInj
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

namespace CurveVerticalPointInjective

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem coord_ne_zero (y : (Σ k, ι k) → Ω) (p : Σ k, ι k)
    (hp : (X p : MRing ι) ∉ mCoordIdeal y) : y p ≠ 0 := by
  intro h0
  apply hp
  simp [mCoordIdeal, mConeMap, RingHom.mem_ker, h0]

theorem isMultiHomogIdeal_of_mem_divSupp (y : (Σ k, ι k) → Ω) (s : MRing ι) (d : K → ℕ)
    (hA : IsArithVar (mCoordIdeal y) 1) (hs : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s d) {W : Ideal (MRing ι)}
    (hW : W ∈ divSupp (mCoordIdeal y) s) : IsMultiHomogIdeal W := by
  classical
  have hP : NumbersDVR.IsMultiHomogIdeal (mCoordIdeal y) :=
    (Bridge.isMultiHomogIdeal_iff _).2 hA.2.1.2.1
  have hJ := NumbersDVR.SupSpanMultiHomog.full.{0} ℤ K ι (mCoordIdeal y) s d hP
    ((Bridge.isMultiHomog_iff s _).2 hs)
  exact (Bridge.isMultiHomogIdeal_iff _).1
    (NumbersDVR.MinimalPrimeMultiHomog.full.{0} ℤ K ι _ W hJ hW.1)

end CurveVerticalPointInjective


open CurveVerticalPointInjective in
theorem CurveVertPointInj.proof (hCh : CurveVertPointChart.Statement) : CurveVertPointInj.Statement := by
  intro K _ ι _ Ω _ y s d hA hs hsP W hW W' hW' hWW'
  choose c hc using hW.2
  choose c' hc' using hW'.2
  obtain ⟨hmax, hrat, hform⟩ := hCh K ι Ω y s d hA hs hsP W hW c hc
  obtain ⟨-, -, hform'⟩ := hCh K ι Ω y s d hA hs hsP W' hW' c' hc'
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k =>
    coord_ne_zero y _ fun h => hc k (le_sup_left.trans hW.1.1.2 h)
  choose a' b' hb' hab' using fun k => hrat ⟨k, c' k⟩
  have hab'' : ∀ k, (b' k : Ω) * y ⟨k, c' k⟩ = a' k * y ⟨k, c k⟩ := fun k => by
    rw [← hab' k]; field_simp [hyc k]
  have hle : W' ≤ W := by
    obtain ⟨S, hS, hSeq⟩ := isMultiHomogIdeal_of_mem_divSupp y s d hA hs hW'
    rw [hSeq, Ideal.span_le]
    intro g hg
    obtain ⟨e, he⟩ := hS g hg
    obtain ⟨a, b, ha, hb, habg⟩ := (hform' e g he).1 (hSeq ▸ Ideal.subset_span hg)
    rw [← hWW'] at ha hb
    refine (hform e g he).2 ⟨a * ∏ k, a' k ^ e k, (∏ k, b' k ^ e k) * b, Ideal.mul_mem_right _ _ ha, ?_, ?_⟩
    · intro h
      rcases hmax.isPrime.mem_or_mem h with h | h
      · obtain ⟨k, -, hk⟩ := (hmax.isPrime.prod_mem_iff (s := Finset.univ)).1 h
        exact hb' k (hmax.isPrime.mem_of_pow_mem _ hk)
      · exact hb h
    · push_cast
      calc (∏ k, (b' k : Ω) ^ e k) * b * aeval y g
          = a * ∏ k, ((b' k : Ω) * y ⟨k, c' k⟩) ^ e k := by
            rw [mul_assoc, habg, Finset.prod_congr rfl fun k _ => mul_pow (b' k : Ω) _ (e k),
              Finset.prod_mul_distrib]; ring
        _ = (a * ∏ k, (a' k : Ω) ^ e k) * ∏ k, y ⟨k, c k⟩ ^ e k := by
            simp_rw [hab'', mul_pow, Finset.prod_mul_distrib]; ring
  exact le_antisymm (hW.1.2 ⟨hW'.1.1.1, hW'.1.1.2⟩ hle) hle

end GroundTheory.Heights₂.Heights.Targets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.CurveVerticalPointChart
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

set_option linter.unusedSectionVars false

namespace CurveVerticalPointChart

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem prod_pow_add (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (e f : K → ℕ) :
    ∏ k, y ⟨k, c k⟩ ^ (e + f) k = (∏ k, y ⟨k, c k⟩ ^ e k) * ∏ k, y ⟨k, c k⟩ ^ f k := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun k _ => by rw [Pi.add_apply, pow_add]

theorem form_add {f g : MRing ι} {a : K → ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a) (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g a) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (f + g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (support_add hm) with h | h
  · exact hf m h k
  · exact hg m h k

theorem form_sub {f g : MRing ι} {a : K → ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a) (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g a) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (f - g) a := by
  rw [sub_eq_add_neg]
  refine form_add hf ?_
  intro m hm
  rw [support_neg] at hm
  exact hg m hm

theorem form_C (n : ℤ) : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (C n : MRing ι) 0 := by
  classical
  intro m hm k
  rw [C_apply] at hm
  have : m = 0 := Finset.mem_singleton.mp (support_monomial_subset hm)
  subst this
  simp

theorem mem_of_aeval_eq (y : (Σ k, ι k) → Ω) {W : Ideal (MRing ι)} (hPW : mCoordIdeal y ≤ W)
    {f g : MRing ι} {a a' : K → ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a) (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g a') (haa : a = a')
    (he : aeval y f = aeval y g) (hfW : f ∈ W) : g ∈ W := by
  subst haa
  have h0 : f - g ∈ mCoordIdeal y :=
    HilbertSamuel.SmallSectionsNonzero.mem_mCoordIdeal_of_aeval_eq_zero y (form_sub hf hg)
      (by rw [map_sub, he, sub_self])
  have h1 := W.sub_mem hfW (hPW h0)
  rwa [sub_sub_cancel] at h1

theorem chartMono_notMem {W : Ideal (MRing ι)} (hWp : W.IsPrime) {c : ∀ k, ι k}
    (hc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ W) (e : K → ℕ) :
    HilbertSamuel.SmallSectionsNonzero.chartMono c e ∉ W := by
  classical
  rw [HilbertSamuel.SmallSectionsNonzero.chartMono, Ideal.IsPrime.prod_mem_iff]
  rintro ⟨k, -, hk⟩
  exact hc k (hWp.mem_of_pow_mem _ hk)

theorem mem_of_chartMono_mul {W : Ideal (MRing ι)} (hWp : W.IsPrime) {c : ∀ k, ι k}
    (hc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ W) {e : K → ℕ} {f : MRing ι}
    (h : HilbertSamuel.SmallSectionsNonzero.chartMono c e * f ∈ W) : f ∈ W :=
  (hWp.mem_or_mem h).resolve_left (chartMono_notMem hWp hc e)

theorem exists_rep (y : (Σ k, ι k) → Ω) {c : ∀ k, ι k} (hyc : ∀ k, y ⟨k, c k⟩ ≠ 0) {r : Ω}
    (hr : r ∈ chartRingZ y c) :
    ∃ (e : K → ℕ) (k : MRing ι), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog k e ∧ r * ∏ k, y ⟨k, c k⟩ ^ e k = aeval y k := by
  obtain ⟨e, k, hk, he⟩ :=
    HilbertSamuel.SmallSectionsNonzero.exists_form_of_mem_chartRingZ y c hyc hr
  exact ⟨e, k, hk, he.symm⟩

theorem mem_chart (y : (Σ k, ι k) → Ω) {c : ∀ k, ι k} (hyc : ∀ k, y ⟨k, c k⟩ ≠ 0) (b : curveRing y) :
    (b : Ω) ∈ chartRingZ y c :=
  mem_curveRing.mp b.2 c hyc

def chartPrime (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (W : Ideal (MRing ι)) : Set Ω :=
  {r | ∃ (e : K → ℕ) (g : MRing ι), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g e ∧ g ∈ W ∧ r * ∏ k, y ⟨k, c k⟩ ^ e k = aeval y g}

theorem mem_chartPrime_iff (y : (Σ k, ι k) → Ω) {c : ∀ k, ι k} {W : Ideal (MRing ι)}
    (hPW : mCoordIdeal y ≤ W) (hWp : W.IsPrime) (hc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ W) {r : Ω}
    {e : K → ℕ} {k : MRing ι} (hk : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog k e) (hr : r * ∏ k, y ⟨k, c k⟩ ^ e k = aeval y k) :
    r ∈ chartPrime y c W ↔ k ∈ W := by
  constructor
  · rintro ⟨d, g, hg, hgW, hd⟩
    apply mem_of_chartMono_mul hWp hc (e := d)
    refine mem_of_aeval_eq y hPW
      (Inter.AvoidRing.isMultiHomog_mul (HilbertSamuel.SmallSectionsNonzero.isMultiHomog_chartMono c e) hg)
      (Inter.AvoidRing.isMultiHomog_mul (HilbertSamuel.SmallSectionsNonzero.isMultiHomog_chartMono c d) hk)
      (add_comm e d) ?_ (W.mul_mem_left _ hgW)
    simp only [map_mul, HilbertSamuel.SmallSectionsNonzero.aeval_chartMono]
    linear_combination (-(∏ k, y ⟨k, c k⟩ ^ e k)) * hd + (∏ k, y ⟨k, c k⟩ ^ d k) * hr
  · intro hkW
    exact ⟨e, k, hk, hkW, hr⟩

theorem chartPrime_add (y : (Σ k, ι k) → Ω) {c : ∀ k, ι k} {W : Ideal (MRing ι)} {r r' : Ω}
    (hr : r ∈ chartPrime y c W) (hr' : r' ∈ chartPrime y c W) : r + r' ∈ chartPrime y c W := by
  obtain ⟨d, g, hg, hgW, hd⟩ := hr
  obtain ⟨e, g', hg', hg'W, he⟩ := hr'
  have h1 := Inter.AvoidRing.isMultiHomog_mul hg (HilbertSamuel.SmallSectionsNonzero.isMultiHomog_chartMono c e)
  have h2 := Inter.AvoidRing.isMultiHomog_mul hg' (HilbertSamuel.SmallSectionsNonzero.isMultiHomog_chartMono c d)
  rw [add_comm e d] at h2
  refine ⟨d + e, _, form_add h1 h2, W.add_mem (W.mul_mem_right _ hgW) (W.mul_mem_right _ hg'W), ?_⟩
  simp only [map_add (f := _), map_mul, HilbertSamuel.SmallSectionsNonzero.aeval_chartMono]
  rw [prod_pow_add]
  linear_combination (∏ k, y ⟨k, c k⟩ ^ e k) * hd + (∏ k, y ⟨k, c k⟩ ^ d k) * he

theorem chartPrime_mul (y : (Σ k, ι k) → Ω) {c : ∀ k, ι k} (hyc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    {W : Ideal (MRing ι)} {a r : Ω} (ha : a ∈ chartRingZ y c) (hr : r ∈ chartPrime y c W) :
    a * r ∈ chartPrime y c W := by
  obtain ⟨d, g, hg, hgW, hd⟩ := hr
  obtain ⟨e, k, hk, hae⟩ := exists_rep y hyc ha
  refine ⟨e + d, k * g, Inter.AvoidRing.isMultiHomog_mul hk hg, W.mul_mem_left _ hgW, ?_⟩
  rw [map_mul, prod_pow_add]
  linear_combination (r * ∏ k, y ⟨k, c k⟩ ^ d k) * hae + (aeval y k) * hd

def chartPrimeB (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (W : Ideal (MRing ι))
    (hyc : ∀ k, y ⟨k, c k⟩ ≠ 0) : Ideal (curveRing y) where
  carrier := {b | (b : Ω) ∈ chartPrime y c W}
  add_mem' {a b} ha hb := by
    change ((a : Ω) + b) ∈ chartPrime y c W
    exact chartPrime_add y ha hb
  zero_mem' := ⟨0, 0, fun m hm => by simp at hm, W.zero_mem, by simp⟩
  smul_mem' a b hb := by
    change ((a : Ω) * b) ∈ chartPrime y c W
    exact chartPrime_mul y hyc (mem_chart y hyc a) hb

theorem mem_chartPrimeB {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} {W : Ideal (MRing ι)}
    {hyc : ∀ k, y ⟨k, c k⟩ ≠ 0} {b : curveRing y} : b ∈ chartPrimeB y c W hyc ↔ (b : Ω) ∈ chartPrime y c W :=
  Iff.rfl

theorem chartPrimeB_isPrime (y : (Σ k, ι k) → Ω) {c : ∀ k, ι k} {W : Ideal (MRing ι)}
    (hPW : mCoordIdeal y ≤ W) (hWp : W.IsPrime) (hc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ W)
    (hyc : ∀ k, y ⟨k, c k⟩ ≠ 0) : (chartPrimeB y c W hyc).IsPrime := by
  refine ⟨?_, ?_⟩
  · rw [Ideal.ne_top_iff_one]
    intro h
    have h1 := (mem_chartPrime_iff y hPW hWp hc (r := ((1 : curveRing y) : Ω)) (e := 0) (k := 1)
      Inter.AvoidRing.isMultiHomog_one (by simp)).mp (mem_chartPrimeB.mp h)
    exact hWp.ne_top ((Ideal.eq_top_iff_one W).mpr h1)
  · intro a b hab
    obtain ⟨e, k, hk, ha⟩ := exists_rep y hyc (mem_chart y hyc a)
    obtain ⟨e', k', hk', hb⟩ := exists_rep y hyc (mem_chart y hyc b)
    have hkk : k * k' ∈ W := (mem_chartPrime_iff y hPW hWp hc (r := ((a * b : curveRing y) : Ω))
      (Inter.AvoidRing.isMultiHomog_mul hk hk') (by
        rw [Subring.coe_mul, map_mul, prod_pow_add]
        linear_combination ((b : Ω) * ∏ k, y ⟨k, c k⟩ ^ e' k) * ha + (aeval y k) * hb)).mp
      (mem_chartPrimeB.mp hab)
    rcases hWp.mem_or_mem hkk with h | h
    · exact Or.inl ⟨e, k, hk, h, ha⟩
    · exact Or.inr ⟨e', k', hk', h, hb⟩

theorem curvePtIdeal_eq (y : (Σ k, ι k) → Ω) {c : ∀ k, ι k} {W : Ideal (MRing ι)}
    (hPW : mCoordIdeal y ≤ W) (hWp : W.IsPrime) (hc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ W)
    (hyc : ∀ k, y ⟨k, c k⟩ ≠ 0) : curvePtIdeal y W = chartPrimeB y c W hyc := by
  apply le_antisymm
  · rw [curvePtIdeal, Ideal.span_le]
    rintro b ⟨δ, g, h, hg, hh, hgW, hhW, hb⟩
    obtain ⟨e, k, hk, hbk⟩ := exists_rep y hyc (mem_chart y hyc b)
    have hkh : k * h ∈ W := mem_of_aeval_eq y hPW
      (Inter.AvoidRing.isMultiHomog_mul (HilbertSamuel.SmallSectionsNonzero.isMultiHomog_chartMono c e) hg)
      (Inter.AvoidRing.isMultiHomog_mul hk hh) rfl
      (by
        simp only [map_mul, HilbertSamuel.SmallSectionsNonzero.aeval_chartMono]
        linear_combination (-(∏ k, y ⟨k, c k⟩ ^ e k)) * hb + (aeval y h) * hbk)
      (W.mul_mem_left _ hgW)
    exact ⟨e, k, hk, (hWp.mem_or_mem hkh).resolve_right hhW, hbk⟩
  · intro b hb
    obtain ⟨d, g, hg, hgW, hd⟩ := mem_chartPrimeB.mp hb
    apply Ideal.subset_span
    refine ⟨d, g, HilbertSamuel.SmallSectionsNonzero.chartMono c d, hg,
      HilbertSamuel.SmallSectionsNonzero.isMultiHomog_chartMono c d, hgW, chartMono_notMem hWp hc d, ?_⟩
    rw [HilbertSamuel.SmallSectionsNonzero.aeval_chartMono]
    exact hd

theorem chartPrimeB_isMaximal (y : (Σ k, ι k) → Ω) {c : ∀ k, ι k} {W : Ideal (MRing ι)}
    (hB : Module.Finite ℤ (curveRing y))
    (hPW : mCoordIdeal y ≤ W) (hWp : W.IsPrime) (hc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ W)
    (hyc : ∀ k, y ⟨k, c k⟩ ≠ 0) {n : ℤ} (hn : n ≠ 0) (hnW : (C n : MRing ι) ∈ W) :
    (chartPrimeB y c W hyc).IsMaximal := by
  have := chartPrimeB_isPrime y hPW hWp hc hyc
  have hnm : (n : curveRing y) ∈ chartPrimeB y c W hyc := by
    refine mem_chartPrimeB.mpr ⟨0, C n, form_C n, hnW, ?_⟩
    simp
  have : Module.Finite ℤ (curveRing y ⧸ chartPrimeB y c W hyc) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℤ (chartPrimeB y c W hyc)).toLinearMap
      Ideal.Quotient.mk_surjective
  have htor : Module.IsTorsion ℤ (curveRing y ⧸ chartPrimeB y c W hyc) := by
    intro x
    refine ⟨⟨n, mem_nonZeroDivisors_of_ne_zero hn⟩, ?_⟩
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    show n • Ideal.Quotient.mk _ b = 0
    rw [zsmul_eq_mul, ← map_intCast (Ideal.Quotient.mk (chartPrimeB y c W hyc)), ← map_mul,
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right _ _ hnm
  have : Finite (curveRing y ⧸ chartPrimeB y c W hyc) := Module.finite_of_fg_torsion _ htor
  exact Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain _)

def locSub (y : (Σ k, ι k) → Ω) (m : Ideal (curveRing y)) (hm : m.IsPrime) : Subring Ω where
  carrier := {r | ∃ a b : curveRing y, b ∉ m ∧ (b : Ω) * r = a}
  mul_mem' {r r'} := by
    rintro ⟨a, b, hb, h⟩ ⟨a', b', hb', h'⟩
    refine ⟨a * a', b * b', fun h'' => (hm.mem_or_mem h'').elim hb hb', ?_⟩
    rw [Subring.coe_mul, Subring.coe_mul]
    linear_combination ((b' : Ω) * r') * h + (a : Ω) * h'
  one_mem' := ⟨1, 1, (Ideal.ne_top_iff_one m).mp hm.ne_top, by simp⟩
  add_mem' {r r'} := by
    rintro ⟨a, b, hb, h⟩ ⟨a', b', hb', h'⟩
    refine ⟨a * b' + b * a', b * b', fun h'' => (hm.mem_or_mem h'').elim hb hb', ?_⟩
    rw [Subring.coe_add, Subring.coe_mul, Subring.coe_mul, Subring.coe_mul]
    linear_combination (b' : Ω) * h + (b : Ω) * h'
  zero_mem' := ⟨0, 1, (Ideal.ne_top_iff_one m).mp hm.ne_top, by simp⟩
  neg_mem' {r} := by
    rintro ⟨a, b, hb, h⟩
    refine ⟨-a, b, hb, ?_⟩
    rw [Subring.coe_neg]
    linear_combination -h

theorem mem_locSub {y : (Σ k, ι k) → Ω} {m : Ideal (curveRing y)} {hm : m.IsPrime} {r : Ω} :
    r ∈ locSub y m hm ↔ ∃ a b : curveRing y, b ∉ m ∧ (b : Ω) * r = a :=
  Iff.rfl

theorem chart_le_locSub (y : (Σ k, ι k) → Ω) (m : Ideal (curveRing y)) (hm : m.IsPrime) (c : ∀ k, ι k)
    (h : ∀ p : Σ k, ι k, y p / y ⟨p.1, c p.1⟩ ∈ locSub y m hm) {r : Ω} (hr : r ∈ chartRingZ y c) :
    r ∈ locSub y m hm := by
  rw [chartRingZ] at hr
  induction hr using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    exact h p
  | algebraMap n =>
    rw [algebraMap_int_eq, eq_intCast]
    exact intCast_mem _ n
  | add x x' _ _ hx hx' => exact add_mem hx hx'
  | mul x x' _ _ hx hx' => exact mul_mem hx hx'

end CurveVerticalPointChart

end

end GroundTheory.Heights₂.Heights.Targets
end
