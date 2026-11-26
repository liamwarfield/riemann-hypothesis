module

public import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.LatticeOpenCompactNhdsBasis

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.ExistsFinsetSep
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual

namespace GlobalTheory.CompanionTheory.LocDual.Kernels

theorem mem_of_forall_pow {O M : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [AddCommGroup M] [Module O M] (Λ E : Submodule O M) (hΛ : Λ.FG) (ϖ : O) (hϖ : ¬ IsUnit ϖ)
    (w : M) (h : ∀ n : ℕ, ∃ e ∈ E, ∃ t ∈ Λ, w = e + ϖ ^ n • t) : w ∈ E := by
  classical
  set N : Submodule O (M ⧸ E) := Λ.map E.mkQ with hNdef
  have hNfg : N.FG := hΛ.map _
  haveI : Module.Finite O N := Module.Finite.iff_fg.2 hNfg
  have hE : ∀ e ∈ E, E.mkQ e = 0 := fun e he => (Submodule.Quotient.mk_eq_zero E).2 he
  obtain ⟨e₀, he₀, t₀, ht₀, hw₀⟩ := h 0
  have hwN : E.mkQ w ∈ N := ⟨t₀, ht₀, by rw [hw₀, pow_zero, one_smul, map_add (f := _), hE e₀ he₀, zero_add]⟩
  have hI : Ideal.span {ϖ} ≠ ⊤ := fun h' => hϖ (Ideal.span_singleton_eq_top.1 h')
  have hbot := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := N) (Ideal.span {ϖ}) hI
  have hmem : (⟨E.mkQ w, hwN⟩ : N) ∈ (⨅ i : ℕ, Ideal.span {ϖ} ^ i • ⊤ : Submodule O N) := by
    refine Submodule.mem_iInf _ |>.2 fun i => ?_
    obtain ⟨e, he, t, ht, hw⟩ := h i
    have htN : E.mkQ t ∈ N := ⟨t, ht, rfl⟩
    have heq : (⟨E.mkQ w, hwN⟩ : N) = ϖ ^ i • (⟨E.mkQ t, htN⟩ : N) := by
      apply Subtype.ext
      rw [Submodule.coe_smul]
      show E.mkQ w = ϖ ^ i • E.mkQ t
      rw [hw, map_add (f := _), map_smul, hE e he, zero_add]
    rw [heq]
    exact Submodule.smul_mem_smul (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self ϖ) i) Submodule.mem_top
  rw [hbot, Submodule.mem_bot] at hmem
  have h0 : E.mkQ w = 0 := congrArg Subtype.val hmem
  exact (Submodule.Quotient.mk_eq_zero E).1 h0

theorem exists_finset_sep {k U G X : Type} [Field k] [AddCommGroup U] [Module k U]
    [FiniteDimensional k U] [AddCommGroup X] [Module k X] (φ : U →ₗ[k] G → X) :
    ∃ F : Finset G, ∀ u, (∀ g ∈ F, φ u g = 0) → φ u = 0 := by
  classical
  let Kf : Finset G → Submodule k U := fun F => ⨅ g ∈ F, LinearMap.ker ((LinearMap.proj g).comp φ)
  obtain ⟨_, ⟨F, rfl⟩, hmin⟩ := WellFounded.has_min (wellFounded_lt (α := Submodule k U)) (Set.range Kf)
    ⟨Kf ∅, Set.mem_range_self _⟩
  have hall : ∀ g, Kf F ≤ LinearMap.ker ((LinearMap.proj g).comp φ) := by
    intro g
    have hle : Kf (insert g F) ≤ Kf F := by
      refine le_iInf₂ fun g' hg' => iInf₂_le g' (Finset.mem_insert_of_mem hg')
    have heq : Kf (insert g F) = Kf F := by
      by_contra hne
      exact hmin _ (Set.mem_range_self _) (lt_of_le_of_ne hle hne)
    rw [← heq]
    exact iInf₂_le g (Finset.mem_insert_self g F)
  refine ⟨F, fun u hu => funext fun g => ?_⟩
  have huF : u ∈ Kf F := by
    simp only [Kf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj, Function.eval]
    exact hu
  have := hall g huF
  simpa using this

end GlobalTheory.CompanionTheory.LocDual.Kernels
end

section -- merged from Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.H2LineOfTateH2AndCoboundaries
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual

noncomputable section

namespace GlobalTheory.CompanionTheory.LocDual.Top

section Hom

variable {O LL : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field LL] [Algebra O LL]
  [IsFractionRing O LL]

theorem exists_mul_of_linear (T : Submodule O LL) (hT : T = LinearMap.range (Algebra.linearMap O LL))
    {ϖ : O} (hϖ : Irreducible ϖ) (hc : IsAdicComplete (Ideal.span {ϖ}) O) (ψ : LL →ₗ[O] LL ⧸ T) :
    ∃ u : LL, ∀ a, ψ a = Submodule.Quotient.mk (a * u) := by
  obtain ⟨p, hp⟩ : ∃ p : LL, p = algebraMap O LL ϖ := ⟨_, rfl⟩
  have hp0 : p ≠ 0 := fun h => hϖ.ne_zero (IsFractionRing.injective O LL (by simpa [hp] using h))
  have hmem : ∀ x : LL, x ∈ T ↔ ∃ o : O, algebraMap O LL o = x := by
    intro x
    rw [hT]
    simp [LinearMap.mem_range]
  choose u hu using fun n : ℕ => Submodule.Quotient.mk_surjective T (ψ ((p⁻¹) ^ n))
  have step : ∀ n, ∃ o : O, algebraMap O LL o = p * u (n + 1) - u n := by
    intro n
    rw [← hmem, ← Submodule.Quotient.eq]
    have h1 : (Submodule.Quotient.mk (p * u (n + 1)) : LL ⧸ T) =
        ϖ • Submodule.Quotient.mk (u (n + 1)) := by
      rw [← Submodule.Quotient.mk_smul, Algebra.smul_def, hp]
    rw [h1, hu, hu, ← map_smul, Algebra.smul_def, ← hp]
    congr 1
    rw [pow_succ]
    field_simp
  choose o ho using step
  obtain ⟨y, hyd⟩ : ∃ y : ℕ → O, y = fun n => ∑ i ∈ Finset.range n, ϖ ^ i * o i := ⟨_, rfl⟩
  have hys : ∀ n, y (n + 1) = y n + ϖ ^ n * o n := by
    intro n
    simp [hyd, Finset.sum_range_succ]
  have hy0 : y 0 = 0 := by simp [hyd]
  have hy : ∀ n, p ^ n * u n = u 0 + algebraMap O LL (y n) := by
    intro n
    induction n with
    | zero => simp [hy0]
    | succ n ih =>
      have h2 : p ^ (n + 1) * u (n + 1) = p ^ n * u n + p ^ n * (p * u (n + 1) - u n) := by ring
      rw [h2, ih, ← ho n, hys, map_add (f := _), map_mul, map_pow, ← hp]
      ring
  have hI : ∀ m, ((Ideal.span {ϖ}) ^ m • ⊤ : Submodule O O) = Ideal.span {ϖ ^ m} := by
    intro m
    simp [Ideal.span_singleton_pow]
  have hcauchy : ∀ {m n}, m ≤ n → y m ≡ y n [SMOD ((Ideal.span {ϖ}) ^ m • ⊤ : Submodule O O)] := by
    intro m n hmn
    rw [SModEq.sub_mem, hI, Ideal.mem_span_singleton]
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      rw [hys]
      have h3 : y m - (y n + ϖ ^ n * o n) = (y m - y n) - ϖ ^ n * o n := by ring
      rw [h3]
      exact dvd_sub ih (Dvd.dvd.mul_right (pow_dvd_pow _ hmn) _)
  obtain ⟨Y, hY⟩ := IsPrecomplete.prec hc.toIsPrecomplete hcauchy
  refine ⟨u 0 + algebraMap O LL Y, ?_⟩
  have hpow : ∀ n, ψ ((p⁻¹) ^ n) = Submodule.Quotient.mk ((p⁻¹) ^ n * (u 0 + algebraMap O LL Y)) := by
    intro n
    rw [← hu, Submodule.Quotient.eq, hmem]
    have h4 := hY n
    rw [SModEq.sub_mem, hI, Ideal.mem_span_singleton] at h4
    obtain ⟨t, ht⟩ := h4
    refine ⟨t, ?_⟩
    have h5 : algebraMap O LL (y n) - algebraMap O LL Y = p ^ n * algebraMap O LL t := by
      rw [← map_sub, ht, map_mul, map_pow, ← hp]
    have h6 : u n = (p⁻¹) ^ n * (u 0 + algebraMap O LL (y n)) := by
      rw [← hy, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hp0, one_pow, one_mul]
    rw [h6, ← mul_sub]
    have h7 : u 0 + algebraMap O LL (y n) - (u 0 + algebraMap O LL Y) = p ^ n * algebraMap O LL t := by
      rw [← h5]
      ring
    rw [h7, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hp0, one_pow, one_mul]
  intro a
  obtain ⟨x, w, hw, rfl⟩ := IsFractionRing.div_surjective (A := O) a
  have hw0 : w ≠ 0 := nonZeroDivisors.ne_zero hw
  obtain ⟨n, e, he⟩ := IsDiscreteValuationRing.associated_pow_irreducible hw0 hϖ
  have hw1 : algebraMap O LL w ≠ 0 := fun h => hw0 (IsFractionRing.injective O LL (by simpa using h))
  have ha : algebraMap O LL x / algebraMap O LL w = (x * e) • (p⁻¹) ^ n := by
    rw [Algebra.smul_def, map_mul, div_eq_iff hw1]
    have h8 : p ^ n = algebraMap O LL w * algebraMap O LL (e : O) := by
      rw [hp, ← map_pow, ← he, map_mul]
    have h9 : p ^ n ≠ 0 := pow_ne_zero _ hp0
    rw [inv_pow]
    field_simp
    rw [h8]
    ring
  rw [ha, map_smul, hpow, ← Submodule.Quotient.mk_smul, Algebra.smul_def, Algebra.smul_def, mul_assoc]

end Hom

section Red

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL : Type} [Field LL] [Algebra Qp LL] {O : Type} [CommRing O] [Algebra O LL]

def red (L1 : Lattice (O := O) (charRep (cycLL PD LL))) : (G × G → LL) →ₗ[O] (G × G → LL ⧸ L1.T) :=
  LinearMap.compLeft L1.T.mkQ (G × G)

def Zc (L1 : Lattice (O := O) (charRep (cycLL PD LL))) : Submodule O (G × G → LL) :=
  (ReciprocityTheory.Def.Z2 (repD L1) ⊤).comap (red L1)

def cls (L1 : Lattice (O := O) (charRep (cycLL PD LL))) : Zc L1 →ₗ[O] ReciprocityTheory.Def.H2 (repD L1) ⊤ :=
  (Submodule.mkQ _) ∘ₗ ((red L1).restrict (q := ReciprocityTheory.Def.Z2 (repD L1) ⊤) (fun _ h => h))

theorem cls_eq_zero_iff (L1 : Lattice (O := O) (charRep (cycLL PD LL))) (w : Zc L1) :
    cls L1 w = 0 ↔ CobO PD L1 (w : G × G → LL) := by
  simp only [cls, LinearMap.comp_apply, Submodule.mkQ_apply]
  rw [Submodule.Quotient.mk_eq_zero]
  rfl

theorem mem_Zc [TopologicalSpace LL] [IsTopologicalRing LL]
    (L1 : Lattice (O := O) (charRep (cycLL PD LL)))
    (hop : IsOpen (L1.T : Set LL)) {z : G × G → LL} (hz : Continuous z)
    (hd : ReciprocityTheory.Def.d2 (charRep (cycLL PD LL)) z = 0) : z ∈ Zc L1 := by
  refine ⟨⟨?_, fun _ => trivial⟩, ?_⟩
  · intro s
    have h1 : IsOpen ((Submodule.Quotient.mk : LL → LL ⧸ L1.T) ⁻¹' s) := by
      rw [isOpen_iff_forall_mem_open]
      intro y hy
      refine ⟨(fun t => t - y) ⁻¹' (L1.T : Set LL), ?_, hop.preimage (by fun_prop), ?_⟩
      · intro t ht
        have h2 : (Submodule.Quotient.mk t : LL ⧸ L1.T) = Submodule.Quotient.mk y :=
          (Submodule.Quotient.eq _).2 ht
        simpa [Set.mem_preimage, h2] using hy
      · simp [Set.mem_preimage]
    exact h1.preimage hz
  · ext x
    have h3 := congrFun hd x
    have h4 : (Submodule.Quotient.mk (ReciprocityTheory.Def.d2 (charRep (cycLL PD LL)) z x) : LL ⧸ L1.T) = 0 := by
      rw [h3]
      simp
    exact h4

theorem topLine_at [TopologicalSpace LL] [IsTopologicalRing LL] [IsDomain O] [IsDiscreteValuationRing O]
    [IsFractionRing O LL] (L1 : Lattice (O := O) (charRep (cycLL PD LL)))
    (hT : L1.T = LinearMap.range (Algebra.linearMap O LL)) (hop : IsOpen (L1.T : Set LL))
    {ϖ : O} (hϖ : Irreducible ϖ) (hc : IsAdicComplete (Ideal.span {ϖ}) O)
    (φ : ReciprocityTheory.Def.H2 (repD L1) ⊤ ≃ₗ[O] (LL ⧸ L1.T))
    (hC : ∀ z : G × G → LL, Continuous z → (CobL PD z ↔ ∀ a : LL, CobO PD L1 (a • z)))
    {z z' : G × G → LL} (hz : Continuous z) (hz' : Continuous z')
    (hd : ReciprocityTheory.Def.d2 (charRep (cycLL PD LL)) z = 0)
    (hd' : ReciprocityTheory.Def.d2 (charRep (cycLL PD LL)) z' = 0) (hn : ¬ CobL PD z) :
    ∃ a : LL, CobL PD (z' - a • z) := by
  have hsm : ∀ {w : G × G → LL}, Continuous w → ReciprocityTheory.Def.d2 (charRep (cycLL PD LL)) w = 0 →
      ∀ a : LL, a • w ∈ Zc L1 := by
    intro w hw hdw a
    refine mem_Zc L1 hop (hw.const_smul a) ?_
    rw [map_smul, hdw, smul_zero]
  have key : ∀ {w : G × G → LL} (hw : Continuous w) (hdw : ReciprocityTheory.Def.d2 (charRep (cycLL PD LL)) w = 0),
      ∃ u : LL, ∀ a : LL, φ (cls L1 ⟨a • w, hsm hw hdw a⟩) = Submodule.Quotient.mk (a * u) := by
    intro w hw hdw
    let ι : LL →ₗ[O] Zc L1 :=
      { toFun := fun a => ⟨a • w, hsm hw hdw a⟩
        map_add' := fun a b => Subtype.ext (add_smul a b w)
        map_smul' := fun r a => Subtype.ext (by
          ext x
          simp [Algebra.smul_def, mul_assoc]) }
    exact exists_mul_of_linear L1.T hT hϖ hc ((φ.toLinearMap ∘ₗ cls L1) ∘ₗ ι)
  obtain ⟨u, hu⟩ := key hz hd
  obtain ⟨u', hu'⟩ := key hz' hd'
  have hu0 : u ≠ 0 := by
    rintro rfl
    apply hn
    rw [hC z hz]
    intro a
    have h1 := hu a
    rw [mul_zero, Submodule.Quotient.mk_zero, map_eq_zero_iff φ φ.injective, cls_eq_zero_iff] at h1
    exact h1
  refine ⟨u' / u, ?_⟩
  have hwc : Continuous (z' - (u' / u) • z) := hz'.sub (hz.const_smul _)
  have hdw : ReciprocityTheory.Def.d2 (charRep (cycLL PD LL)) (z' - (u' / u) • z) = 0 := by
    rw [map_sub, map_smul, hd, hd', smul_zero, sub_zero]
  rw [hC _ hwc]
  intro b
  have h2 : (⟨b • (z' - (u' / u) • z), hsm hwc hdw b⟩ : Zc L1) =
      ⟨b • z', hsm hz' hd' b⟩ - ⟨(b * (u' / u)) • z, hsm hz hd _⟩ := by
    apply Subtype.ext
    simp [smul_sub, mul_smul]
  have h3 : φ (cls L1 ⟨b • (z' - (u' / u) • z), hsm hwc hdw b⟩) = 0 := by
    rw [h2, map_sub, map_sub, hu, hu', ← Submodule.Quotient.mk_sub]
    have h4 : b * u' - b * (u' / u) * u = 0 := by
      field_simp
      ring
    rw [h4, Submodule.Quotient.mk_zero]
  rw [map_eq_zero_iff φ φ.injective, cls_eq_zero_iff] at h3
  exact h3

end Red

end GlobalTheory.CompanionTheory.LocDual.Top
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.T2SpaceOfLatticeNhdsBasis
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FgZ1T
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CompactQuotientSubmodule
theorem UpperTheory.compact_quotient_submodule :
    ∀ {LL O W Q : Type} [Field LL] [CommRing O] [Algebra O LL] [AddCommGroup W] [Module LL W] [Module O W]
        [IsScalarTower O LL W] [TopologicalSpace LL] [TopologicalSpace W] [ContinuousSMul LL W]
        [IsTopologicalAddGroup W] [T2Space W] [AddCommGroup Q] [Module O Q] [Finite Q]
        (Z : Submodule O W) (p : O) (f : Z →ₗ[O] Q),
        IsCompact (Set.range (algebraMap O LL)) →
        (∀ U ∈ nhds (0 : W), ∃ n : ℕ, ∀ z ∈ Z, p ^ n • z ∈ U) →
        (∀ z : Z, f z = 0 → ∃ w ∈ Z, (z : W) = p • w) →
        Z.FG := by
  intro LL O W Q _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Z p f hK hsmall hker
  classical
  have := Fintype.ofFinite Q
  let s : Q → Z := Function.invFun f
  have hs : ∀ z : Z, f (s (f z)) = f z := fun z => Function.invFun_eq ⟨z, rfl⟩
  let v : Q → W := fun q => (s q : W)
  let N : Submodule O W := Submodule.span O (Set.range v)
  have hNZ : N ≤ Z := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨q, rfl⟩
    exact (s q).2
  have hstep : ∀ z ∈ Z, ∃ a ∈ N, ∃ w ∈ Z, z = a + p • w := by
    intro z hz
    obtain ⟨w, hw, e⟩ := hker (⟨z, hz⟩ - s (f ⟨z, hz⟩)) (by rw [map_sub, hs, sub_self])
    refine ⟨v (f ⟨z, hz⟩), Submodule.subset_span ⟨_, rfl⟩, w, hw, ?_⟩
    rw [← e]
    simp [v]
  have hiter : ∀ n : ℕ, ∀ z ∈ Z, ∃ a ∈ N, ∃ w ∈ Z, z = a + p ^ n • w := by
    intro n
    induction n with
    | zero => exact fun z hz => ⟨0, N.zero_mem, z, hz, by simp⟩
    | succ n ih =>
      intro z hz
      obtain ⟨a, ha, w, hw, e⟩ := ih z hz
      obtain ⟨b, hb, u, hu, e'⟩ := hstep w hw
      refine ⟨a + p ^ n • b, N.add_mem ha (N.smul_mem _ hb), u, hu, ?_⟩
      rw [e, e', smul_add, smul_smul, pow_succ, add_assoc]
  have hcomp : IsCompact (N : Set W) := by
    have hc : Continuous (fun c : Q → LL => ∑ q, c q • v q) := by fun_prop
    have h1 := (isCompact_univ_pi (fun _ : Q => hK)).image hc
    convert h1 using 1
    ext x
    simp only [SetLike.mem_coe, N, Submodule.mem_span_range_iff_exists_fun, Set.mem_image]
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨fun q => algebraMap O LL (c q), fun q _ => ⟨c q, rfl⟩, by simp⟩
    · rintro ⟨c, hc, rfl⟩
      choose d hd using fun q => hc q (Set.mem_univ q)
      exact ⟨d, by simp [← hd]⟩
  have hZN : Z ≤ N := by
    intro z hz
    by_contra hzN
    have hopen : IsOpen ((fun x : W => z - x) ⁻¹' (N : Set W)ᶜ) :=
      hcomp.isClosed.isOpen_compl.preimage (by fun_prop)
    obtain ⟨n, hn⟩ := hsmall _ (hopen.mem_nhds (by simpa using hzN))
    obtain ⟨a, ha, w, hw, e⟩ := hiter n z hz
    apply hn w hw
    have : z - p ^ n • w = a := by rw [e]; simp
    simpa [this] using ha
  rw [le_antisymm hZN hNZ]
  exact Submodule.fg_span (Set.finite_range v)
end

open Formalism.WeaklyAdmissibleFiltrations

/-- Finitely generated lattice cocycles from finite mod-`ϖ` quotient cocycles
(condensed from 527 lines of `pp.explicit` dump; restores PR #57). -/
theorem UpperTheory.Reformulated.B.Gub2.fg_Z1T :
    ∀ {G : Type} [Group G] [TopologicalSpace G] {LL O V : Type}
      [Field LL] [CommRing O] [Algebra O LL] [AddCommGroup V]
      [Module LL V] [Module O V] [IsScalarTower O LL V]
      {ρ : Representation LL G V} [TopologicalSpace V] [ContinuousAdd V]
      [ContinuousConstSMul LL V] [TopologicalSpace LL] [ContinuousSMul LL V]
      [IsTopologicalAddGroup V] [T2Space V]
      (L : Lattice (O := O) ρ) {ϖ : O}, algebraMap O LL ϖ ≠ 0 →
      (nhds (0 : V)).HasBasis (fun _ : ℕ => True) (fun n => (fun x => ϖ ^ n • x) '' (L.T : Set V)) →
      IsCompact (Set.range (algebraMap O LL)) →
      ∀ (hI : StableSub L (Ideal.span {ϖ ^ 1} • (⊤ : Submodule O L.T))),
      Finite (quotientCocycles L (Ideal.span {ϖ ^ 1} • (⊤ : Submodule O L.T)) hI) →
      (latticeCocycles L).FG := by
  intro G _ _ LL O V _ _ _ _ _ _ _ ρ _ _ _ _ _ _ _ L ϖ hϖ hb hc hI hfin
  have hmem : ∀ x : L.T, x ∈ (Ideal.span {ϖ ^ 1} • (⊤ : Submodule O L.T)) ↔
      ∃ y ∈ L.T, ϖ • y = (x : V) := by
    intro x
    rw [pow_one, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨y, -, rfl⟩
      exact ⟨y, y.2, rfl⟩
    · rintro ⟨y, hy, h⟩
      exact ⟨⟨y, hy⟩, trivial, Subtype.ext h⟩
  have hred : ∀ c : latticeCocycles L, redT L _ c ∈ quotientCocycles L _ hI := by
    intro c
    have hcont : Continuous (c : G → V) := c.2.1.1
    refine ⟨(IsLocallyConstant.iff_eventually_eq _).2 fun g => ?_, fun g h => ?_⟩
    · have h0 : Filter.Tendsto (fun y => (c : G → V) y - (c : G → V) g) (nhds g) (nhds 0) := by
        have := (hcont.sub (continuous_const (y := (c : G → V) g))).tendsto g
        rw [Pi.sub_apply, sub_self] at this
        exact this
      filter_upwards [h0 (hb.mem_of_mem (i := 1) trivial)] with y hy
      obtain ⟨v, hv, hvy⟩ := hy
      refine (Submodule.Quotient.eq _).2 ((hmem _).2 ⟨v, hv, ?_⟩)
      rw [← pow_one ϖ]
      exact hvy
    · have : evT L (g * h) c = evT L g c + actT L g (evT L h c) :=
        Subtype.ext (c.2.1.2 g h)
      change Submodule.mkQ _ (evT L (g * h) c) = _
      rw [this, map_add (f := _)]
      rfl
  refine UpperTheory.compact_quotient_submodule (LL := LL) (latticeCocycles L) ϖ
    ((redT L _).codRestrict (quotientCocycles L _ hI) hred) hc ?_ ?_
  · intro U hU
    rw [nhds_pi, Filter.mem_pi] at hU
    obtain ⟨I, hIf, t, ht, hsub⟩ := hU
    obtain ⟨n, -, hn⟩ := hb.mem_iff.1 ((Filter.biInter_mem hIf).2 fun i _ => ht i)
    refine ⟨n, fun z hz => hsub fun i hi => ?_⟩
    exact Set.mem_iInter₂.1 (hn ⟨z i, hz.2 i trivial, rfl⟩) i hi
  · intro z hz
    have hz' : ∀ g, ∃ y ∈ L.T, ϖ • y = (z : G → V) g := fun g =>
      (hmem (evT L g z)).1
        ((Submodule.Quotient.mk_eq_zero _).1 (congrFun (congrArg Subtype.val hz) g))
    refine ⟨(algebraMap O LL ϖ)⁻¹ • (z : G → V),
      ⟨(continuousCocycles ρ).smul_mem _ z.2.1, fun g _ => ?_⟩, ?_⟩
    · obtain ⟨y, hy, h⟩ := hz' g
      have : ((algebraMap O LL ϖ)⁻¹ • (z : G → V)) g = y := by
        rw [Pi.smul_apply, ← h, ← algebraMap_smul LL ϖ y, inv_smul_smul₀ hϖ]
      rw [this]
      exact hy
    · rw [← algebraMap_smul LL ϖ, smul_inv_smul₀ hϖ]
end

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual

noncomputable section

namespace GlobalTheory.CompanionTheory.LocDual.FinT

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] {LL O V : Type} [Field LL] [CommRing O] [Algebra O LL]
    [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V}
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]

theorem mem_smulTop (L : Lattice (O := O) ρ) (ϖ : O) (x : ↥L.T) :
    x ∈ (Ideal.span {ϖ ^ 1} • ⊤ : Submodule O ↥L.T) ↔ ∃ y : ↥L.T, ϖ • y = x := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  simp

theorem fg_Z1T [TopologicalSpace LL] [ContinuousSMul LL V] [IsTopologicalAddGroup V] [T2Space V] (L : Lattice (O := O) ρ) {ϖ : O}
    (h0 : algebraMap O LL ϖ ≠ 0)
    (hB : (nhds (0 : V)).HasBasis (fun _ : ℕ => True) (fun n => (fun x => ϖ ^ n • x) '' (L.T : Set V)))
    (hK : IsCompact (Set.range (algebraMap O LL)))
    (hI : StableSub L (Ideal.span {ϖ ^ 1} • ⊤ : Submodule O ↥L.T)) (hfin : Finite ↥(quotientCocycles L _ hI)) :
    (latticeCocycles L).FG :=
  _root_.UpperTheory.Reformulated.B.Gub2.fg_Z1T L h0 hB hK hI hfin

theorem t2Space_of_lattice_nhds_basis [IsTopologicalAddGroup V] [IsNoetherianRing O] [IsLocalRing O] (L : Lattice (O := O) ρ) {ϖ : O}
    (hϖ : ¬ IsUnit ϖ)
    (hB : (nhds (0 : V)).HasBasis (fun _ : ℕ => True) (fun n => (fun x => ϖ ^ n • x) '' (L.T : Set V))) :
    T2Space V := by
  refine IsTopologicalAddGroup.t2Space_of_zero_sep fun x hx => ?_
  by_contra hcon
  push_neg at hcon
  have hin : ∀ n : ℕ, ∃ t ∈ L.T, ϖ ^ n • t = x := fun n => hcon _ (hB.mem_of_mem (i := n) trivial)
  haveI : Module.Finite O ↥L.T := Module.Finite.iff_fg.2 L.fg
  have hbot := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := ↥L.T) (Ideal.span {ϖ})
    (fun h => hϖ (Ideal.span_singleton_eq_top.1 h))
  obtain ⟨t₀, ht₀, he₀⟩ := hin 0
  have hxT : x ∈ L.T := by
    rw [pow_zero, one_smul] at he₀
    exact he₀ ▸ ht₀
  have hmem : (⟨x, hxT⟩ : ↥L.T) ∈ (⨅ i : ℕ, (Ideal.span {ϖ}) ^ i • (⊤ : Submodule O ↥L.T)) := by
    rw [Submodule.mem_iInf]
    intro n
    obtain ⟨t, ht, he⟩ := hin n
    rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists]
    exact ⟨⟨t, ht⟩, trivial, Subtype.ext he⟩
  rw [hbot, Submodule.mem_bot] at hmem
  exact hx (congrArg Subtype.val hmem)

def toV (L : Lattice (O := O) ρ) : LatticeCohomology L →ₗ[O] H1V ρ :=
  Submodule.liftQ _
    (((Submodule.mkQ ((B1 ρ).comap (continuousCocycles ρ).subtype)).restrictScalars O) ∘ₗ
      { toFun := fun c => ⟨(c : G → V), c.2.1⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl })
    (by
      rintro c ⟨x, _, hx⟩
      refine (Submodule.Quotient.mk_eq_zero _).2 ?_
      exact ⟨x, hx⟩)

theorem toV_mk (L : Lattice (O := O) ρ) (c : ↥(latticeCocycles L)) :
    toV L (Submodule.Quotient.mk c) = Submodule.Quotient.mk ⟨(c : G → V), c.2.1⟩ := rfl

theorem isLocalized_toV [IsDomain O] [IsFractionRing O LL] (L : Lattice (O := O) ρ) {ϖ : O} (h0 : ϖ ≠ 0)
    (hInt : ∀ c : G → V, Continuous c → ∃ n : ℕ, ∀ g, ϖ ^ n • c g ∈ L.T) :
    IsLocalizedModule (nonZeroDivisors O) (toV L) := by
  refine { map_units := ?_, surj := ?_, exists_of_eq := ?_ }
  · intro s
    have hs : algebraMap O LL (s : O) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
    rw [Module.End.isUnit_iff]
    constructor
    · intro x y hxy
      have hxy' : (s : O) • x = (s : O) • y := hxy
      rw [← algebraMap_smul LL (s : O) x, ← algebraMap_smul LL (s : O) y] at hxy'
      exact smul_right_injective _ hs hxy'
    · intro y
      refine ⟨(algebraMap O LL (s : O))⁻¹ • y, ?_⟩
      change (s : O) • ((algebraMap O LL (s : O))⁻¹ • y) = y
      rw [← algebraMap_smul LL (s : O), smul_smul, mul_inv_cancel₀ hs, one_smul]
  · intro y
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨n, hn⟩ := hInt (c : G → V) c.2.1
    have hz : ϖ ^ n • (c : G → V) ∈ latticeCocycles L :=
      ⟨(continuousCocycles ρ).restrictScalars O |>.smul_mem _ c.2, fun g _ => hn g⟩
    refine ⟨⟨Submodule.Quotient.mk ⟨_, hz⟩, ⟨ϖ ^ n, pow_mem (mem_nonZeroDivisors_of_ne_zero h0) n⟩⟩, ?_⟩
    rfl
  · intro x₁ x₂ h
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x₁
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ x₂
    rw [toV_mk, toV_mk, Submodule.Quotient.eq] at h
    obtain ⟨v, hv⟩ := h
    obtain ⟨n, hn⟩ := hInt (fun _ => v) continuous_const
    refine ⟨⟨ϖ ^ n, pow_mem (mem_nonZeroDivisors_of_ne_zero h0) n⟩, ?_⟩
    rw [Submonoid.mk_smul, Submonoid.mk_smul, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
    refine ⟨ϖ ^ n • v, hn 1, ?_⟩
    funext g
    have hvg : ρ g v - v = (a : G → V) g - (b : G → V) g := congrFun hv g
    change ρ g (ϖ ^ n • v) - ϖ ^ n • v = ϖ ^ n • (a : G → V) g - ϖ ^ n • (b : G → V) g
    rw [← smul_sub, ← hvg, ← algebraMap_smul LL (ϖ ^ n) v, map_smul, ← smul_sub, algebraMap_smul]

end Gen

end GlobalTheory.CompanionTheory.LocDual.FinT
end
end
