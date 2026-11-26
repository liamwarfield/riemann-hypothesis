module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.HtOfSum
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.ChevPrime
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.DerRep

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.TanBound
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

private theorem add_vanish {l : ℕ} [Fact l.Prime] {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [CompactSpace H] (f : H → PadicAlgCl l) (hf : Continuous f) (hm : ∀ a b, f (a * b) = f a + f b)
    {ι : Type} (u : ι → H) (g : H)
    (hg : ∀ (A : Type) [CommGroup A] [Finite A], IsPGroup l A → ∀ χ : H →* A, IsOpen (χ.ker : Set H) →
      (∀ a, χ (u a) = 1) → χ g = 1) (hu : ∀ a, f (u a) = 0) : f g = 0 := by
  classical
  have f1 : f 1 = 0 := by
    have h11 := hm 1 1
    rw [mul_one] at h11
    have h12 : f 1 + f 1 = f 1 + 0 := by rw [add_zero, ← h11]
    exact add_left_cancel h12
  have fpow : ∀ (h : H) (m : ℕ), f (h ^ m) = (m : PadicAlgCl l) * f h := by
    intro h m
    induction m with
    | zero => simp [f1]
    | succ m ih =>
      rw [pow_succ, hm, ih]
      push_cast
      ring
  let fm : H →* Multiplicative (PadicAlgCl l) :=
    { toFun := fun h => Multiplicative.ofAdd (f h)
      map_one' := by
        show Multiplicative.ofAdd (f 1) = 1
        rw [f1]
        rfl
      map_mul' := fun a b => by
        show Multiplicative.ofAdd (f (a * b)) = Multiplicative.ofAdd (f a) * Multiplicative.ofAdd (f b)
        rw [hm]
        rfl }
  have hl : ‖((l : ℕ) : PadicAlgCl l)‖ = 1 / (l : ℝ) := by
    rw [← PadicAlgCl.valuation_coe, PadicAlgCl.valuation_p]
    simp
  have hl1 : 1 / (l : ℝ) < 1 := by
    have h2 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
    exact (div_lt_one (by linarith)).mpr h2
  have key : ∀ ε : ℝ, 0 < ε → ‖f g‖ < ε := by
    intro ε hε
    let W : Subgroup (Multiplicative (PadicAlgCl l)) :=
      { carrier := {x | ‖Multiplicative.toAdd x‖ < ε}
        one_mem' := by
          show ‖(0 : PadicAlgCl l)‖ < ε
          rw [norm_zero]
          exact hε
        mul_mem' := fun {a b} ha hb => by
          show ‖Multiplicative.toAdd a + Multiplicative.toAdd b‖ < ε
          exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
        inv_mem' := fun {a} ha => by
          show ‖-Multiplicative.toAdd a‖ < ε
          rw [norm_neg]
          exact ha }
    let N : Subgroup fm.range := W.subgroupOf fm.range
    let χ : H →* fm.range ⧸ N := (QuotientGroup.mk' N).comp fm.rangeRestrict
    have hker : ∀ h, χ h = 1 ↔ ‖f h‖ < ε := by
      intro h
      simp only [χ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
        Subgroup.mem_subgroupOf]
      rfl
    have hsurj : Function.Surjective χ :=
      (QuotientGroup.mk'_surjective N).comp fm.rangeRestrict_surjective
    have hopen : IsOpen (χ.ker : Set H) := by
      have hset : (χ.ker : Set H) = {h | ‖f h‖ < ε} := by
        ext h
        exact hker h
      rw [hset]
      exact isOpen_lt (continuous_norm.comp hf) continuous_const
    haveI : Finite (fm.range ⧸ N) := by
      haveI : Finite (H ⧸ χ.ker) := Subgroup.quotient_finite_of_isOpen _ hopen
      exact Finite.of_surjective (QuotientGroup.kerLift χ)
        (fun a => by
          obtain ⟨h, rfl⟩ := hsurj a
          exact ⟨h, rfl⟩)
    have hp : IsPGroup l (fm.range ⧸ N) := by
      intro a
      obtain ⟨h, rfl⟩ := hsurj a
      have hpos : (0 : ℝ) < ‖f h‖ + 1 := by positivity
      obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hε hpos) hl1
      refine ⟨k, ?_⟩
      rw [← map_pow, hker, fpow, norm_mul, Nat.cast_pow, norm_pow, hl]
      calc (1 / (l : ℝ)) ^ k * ‖f h‖ ≤ (1 / (l : ℝ)) ^ k * (‖f h‖ + 1) := by
            gcongr
            linarith
        _ < ε / (‖f h‖ + 1) * (‖f h‖ + 1) := by gcongr
        _ = ε := by field_simp
    exact (hker g).mp (hg _ hp χ hopen (fun a => (hker _).mpr (by rw [hu a, norm_zero]; exact hε)))
  by_contra hne
  exact lt_irrefl _ (key _ (norm_pos_iff.mpr hne))

private theorem rank_le_card_add_rank_of_kernel {K M : Type} [Field K] [AddCommGroup M] [Module K M] {ι : Type} [Fintype ι]
    (P Q : Submodule K M) (e : ι → M →ₗ[K] K) (h : ∀ x ∈ P, (∀ i, e i x = 0) → x ∈ Q) :
    Module.rank K P ≤ (Fintype.card ι : ℕ) + Module.rank K Q := by
  classical
  let φ : P →ₗ[K] (ι → K) := LinearMap.pi (fun i => (e i).comp P.subtype)
  have h1 := LinearMap.rank_range_add_rank_ker φ
  have h2 : Module.rank K (LinearMap.range φ) ≤ (Fintype.card ι : ℕ) := by
    calc Module.rank K (LinearMap.range φ) ≤ Module.rank K (ι → K) := Submodule.rank_le _
      _ = _ := rank_fun'
  have h3 : Module.rank K (LinearMap.ker φ) ≤ Module.rank K Q := by
    rw [(Submodule.equivMapOfInjective P.subtype Subtype.val_injective (LinearMap.ker φ)).rank_eq]
    apply Submodule.rank_mono
    rintro _ ⟨x, hx, rfl⟩
    apply h _ x.2
    intro i
    have := congrFun (LinearMap.mem_ker.mp hx) i
    simpa [φ] using this
  rw [← h1]
  exact add_le_add h2 h3

set_option synthInstance.maxHeartbeats 200000 in
theorem UpperTheory.V.J.tanBound :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) [Fr.IsCoef l c.O] (F : Fr.Frame l (ResidueField c.O)) (C₀ n : ℕ), F.Ok C₀ → (n = 2 ∨ n = 3) →
        ∀ (S : Fr.Space c.O F n), ∀ ξ : S.A →ₐ[c.O] Qbar l, IntPt S ξ →
          Module.rank (Qbar l) (PtDer ξ (Qbar l)) ≤ (n * F.d : ℕ) + Module.rank (Qbar l) (FixTan S ξ) := by
  intro l _ c _ F C₀ n hF hn S ξ hξ
  choose u a₀ hu1 hu2 hgen using hF.gen
  let ev : S.A → ((S.A →ₗ[c.O] Qbar l) →ₗ[Qbar l] Qbar l) := fun x =>
    { toFun := fun D => D x, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have key := rank_le_card_add_rank_of_kernel (PtDer ξ (Qbar l)) (FixTan S ξ)
    (fun j : (Σ v : F.V, Fin n × Fin (F.dv v)) => ev ↑(S.u.ψ j.1 j.2.1 (u j.1 j.2.2))) ?_
  · have hc : Fintype.card (Σ v : F.V, Fin n × Fin (F.dv v)) = n * F.d := by
      rw [Fintype.card_sigma, UpperTheory.V.Fr.Frame.d, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun v _ => ?_)
      rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    rw [hc] at key
    exact key
  · intro D hD hz
    have hD' : ∀ x y, D (x * y) = ξ x • D y + ξ y • D x := hD
    refine Submodule.mem_inf.mpr ⟨hD, ?_⟩
    show ∀ (v : F.V) (i : Fin n), ∀ g ∈ F.Iv v, D ↑((S.u.ψ v i) g) = 0
    intro v i g hg
    obtain ⟨hx, hd⟩ := (derRep l c F C₀ n hF hn S ξ hξ D hD).2.2 v i
    have hne : ∀ h : F.Gv v, ξ ↑((S.u.ψ v i) h) ≠ 0 := by
      intro h hh
      have h1 := congrArg ξ (congrArg Units.val (mul_inv_cancel ((S.u.ψ v i) h)))
      rw [Units.val_mul, map_mul, hh, zero_mul, Units.val_one, map_one] at h1
      exact zero_ne_one h1
    let f : F.Gv v → PadicAlgCl l := fun h => D ↑((S.u.ψ v i) h) * (ξ ↑((S.u.ψ v i) h))⁻¹
    have hfc : Continuous f := hd.mul (hx.inv₀ hne)
    have hfm : ∀ a b, f (a * b) = f a + f b := by
      intro a b
      have ha := hne a
      have hb := hne b
      simp only [f, map_mul, Units.val_mul, hD', smul_eq_mul]
      field_simp
      ring
    have hzero : ∀ a, f (u v a) = 0 := by
      intro a
      have := hz ⟨v, (i, a)⟩
      simp only [f]
      rw [show D ↑((S.u.ψ v i) (u v a)) = 0 from this, zero_mul]
    have h0 := add_vanish f hfc hfm (u v) g
      (fun A _ _ hA χ ho h1 => hgen v A hA χ ho h1 g hg) hzero
    have hg0 := hne g
    simp only [f, mul_eq_zero, inv_eq_zero] at h0
    exact h0.resolve_right hg0
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.IntOfNorm
set_option linter.overlappingInstances false
set_option synthInstance.maxHeartbeats 200000

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

private theorem int_of_norm {l : ℕ} [Fact l.Prime] (z : Qbar l) (hz : ‖z‖ ≤ 1) :
    ∃ f : Polynomial ℤ_[l], f.Monic ∧ Polynomial.aeval z f = 0 := by
  have hi : IsIntegral ℚ_[l] z := Algebra.IsIntegral.isIntegral z
  have hm : (minpoly ℚ_[l] z).Monic := minpoly.monic hi
  have h1 : spectralValue (minpoly ℚ_[l] z) ≤ 1 := by
    rw [← PadicAlgCl.spectralNorm_eq l z] at hz
    exact hz
  have h2 := (spectralValue_le_one_iff hm).1 h1
  have hl : minpoly ℚ_[l] z ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨_, h2 n⟩, rfl⟩
  obtain ⟨f, hf, -, hfm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl hm
  refine ⟨f, hfm, ?_⟩
  rw [← Polynomial.aeval_map_algebraMap ℚ_[l], hf, minpoly.aeval]

private theorem int_pt {l : ℕ} [Fact l.Prime] {D : Type} [CommRing D] (ξ : D →+* Qbar l) (h : ∀ a, ‖ξ a‖ ≤ 1)
    (φ : ℤ_[l] →+* D) (hφ : ∀ t, ξ (φ t) = algebraMap ℤ_[l] (Qbar l) t) (a : D) :
    ∃ f : Polynomial ℤ_[l], f.Monic ∧ ξ (f.eval₂ φ a) = 0 := by
  obtain ⟨f, hf, h0⟩ := int_of_norm (ξ a) (h a)
  refine ⟨f, hf, ?_⟩
  rw [Polynomial.hom_eval₂, ← h0, Polynomial.aeval_def]
  congr 1
  exact RingHom.ext hφ

private def nx {l : ℕ} [Fact l.Prime] {D : Type} [CommRing D] (ξ : D →+* Qbar l) (h : ∀ a, ‖ξ a‖ ≤ 1) : Ideal D where
  carrier := {a | ‖ξ a‖ < 1}
  add_mem' {a b} ha hb := by
    show ‖ξ (a + b)‖ < 1
    rw [map_add (f := _)]
    exact lt_of_le_of_lt (PadicAlgCl.isNonarchimedean l _ _) (max_lt ha hb)
  zero_mem' := by
    show ‖ξ 0‖ < 1
    simp
  smul_mem' c a ha := by
    show ‖ξ (c • a)‖ < 1
    rw [smul_eq_mul, map_mul, norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (h c)) ha

private theorem nx_prime {l : ℕ} [Fact l.Prime] {D : Type} [CommRing D] (ξ : D →+* Qbar l) (h : ∀ a, ‖ξ a‖ ≤ 1) :
    (nx ξ h).IsPrime := by
  refine ⟨fun e => ?_, fun {a b} hab => ?_⟩
  · have h1 : ‖ξ 1‖ < 1 := (Ideal.eq_top_iff_one _).1 e
    simp at h1
  · by_contra hn
    rw [not_or] at hn
    have ha : ‖ξ a‖ = 1 := le_antisymm (h a) (not_lt.1 hn.1)
    have hb : ‖ξ b‖ = 1 := le_antisymm (h b) (not_lt.1 hn.2)
    have h1 : ‖ξ (a * b)‖ < 1 := hab
    rw [map_mul, norm_mul, ha, hb, one_mul] at h1
    exact lt_irrefl _ h1

private theorem norm_l_lt {l : ℕ} [Fact l.Prime] : ‖(l : Qbar l)‖ < 1 := by
  rw [← map_natCast (algebraMap ℚ_[l] (Qbar l)) l, norm_algebraMap']
  exact Padic.norm_p_lt_one

private theorem nx_max {l : ℕ} [Fact l.Prime] {D : Type} [CommRing D] (ξ : D →+* Qbar l) (h : ∀ a, ‖ξ a‖ ≤ 1)
    (φ : ℤ_[l] →+* D) (hφ : ∀ t, ξ (φ t) = algebraMap ℤ_[l] (Qbar l) t) : (nx ξ h).IsMaximal := by
  haveI hpr := nx_prime ξ h
  haveI hnt : Nontrivial (D ⧸ nx ξ h) := Ideal.Quotient.nontrivial_iff.2 hpr.ne_top
  haveI hdom : IsDomain (D ⧸ nx ξ h) := Ideal.Quotient.isDomain _
  haveI hbp : (⊥ : Ideal (D ⧸ nx ξ h)).IsPrime := Ideal.isPrime_bot
  let f : ℤ_[l] →+* D ⧸ nx ξ h := (Ideal.Quotient.mk (nx ξ h)).comp φ
  have hf : f.IsIntegral := fun z => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨p, hp, h0⟩ := int_pt ξ h φ hφ a
    refine ⟨p, hp, ?_⟩
    have e : p.eval₂ f (Ideal.Quotient.mk (nx ξ h) a) = Ideal.Quotient.mk (nx ξ h) (p.eval₂ φ a) :=
      (Polynomial.hom_eval₂ p φ (Ideal.Quotient.mk (nx ξ h)) a).symm
    rw [e, Ideal.Quotient.eq_zero_iff_mem]
    show ‖ξ _‖ < 1
    rw [h0]
    simp
  have hk : (maximalIdeal ℤ_[l]) ≤ (⊥ : Ideal (D ⧸ nx ξ h)).comap f := by
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.span_le, Set.singleton_subset_iff]
    show f (l : ℤ_[l]) ∈ (⊥ : Ideal (D ⧸ nx ξ h))
    rw [Ideal.mem_bot, map_natCast, ← map_natCast (Ideal.Quotient.mk (nx ξ h)), Ideal.Quotient.eq_zero_iff_mem]
    show ‖ξ (l : D)‖ < 1
    rw [map_natCast]
    exact norm_l_lt
  have hm : ((⊥ : Ideal (D ⧸ nx ξ h)).comap f).IsMaximal := by
    rw [← (maximalIdeal.isMaximal ℤ_[l]).eq_of_le (Ideal.comap_ne_top _ hbp.ne_top) hk]
    exact maximalIdeal.isMaximal _
  haveI := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap' f hf ⊥ hm
  have h2 := Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk (nx ξ h)) (K := (⊥ : Ideal (D ⧸ nx ξ h)))
    Ideal.Quotient.mk_surjective
  rwa [← RingHom.ker_eq_comap_bot, Ideal.mk_ker] at h2

private theorem td_zero {l : ℕ} [Fact l.Prime] {B A : Type} [CommRing B] [CommRing A] [Algebra B A] (q : Ideal A)
    [q.IsPrime] (ψ : ℤ_[l] →+* B)
    (h : ∀ a, ∃ f : Polynomial ℤ_[l], f.Monic ∧ f.eval₂ ((algebraMap B A).comp ψ) a ∈ q) :
    Algebra.trdeg (B ⧸ q.comap (algebraMap B A)) (A ⧸ q) = 0 := by
  haveI hcp : (q.comap (algebraMap B A)).IsPrime := Ideal.IsPrime.comap _
  haveI hnt : Nontrivial (B ⧸ q.comap (algebraMap B A)) := Ideal.Quotient.nontrivial_iff.2 hcp.ne_top
  haveI : Algebra.IsIntegral (B ⧸ q.comap (algebraMap B A)) (A ⧸ q) := ⟨fun z => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨p, hp, h0⟩ := h a
    refine ⟨p.map ((Ideal.Quotient.mk _).comp ψ), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have e := Polynomial.hom_eval₂ p ((algebraMap B A).comp ψ) (Ideal.Quotient.mk q) a
    rw [Ideal.Quotient.eq_zero_iff_mem.2 h0] at e
    exact e.symm⟩
  haveI : Algebra.IsAlgebraic (B ⧸ q.comap (algebraMap B A)) (A ⧸ q) := Algebra.IsIntegral.isAlgebraic
  exact trdeg_eq_zero

private theorem down {A R : Type} [CommRing A] [CommRing R] [IsLocalRing R] (ι : A →+* R) (hf : ι.Flat)
    (x q : Ideal A) [x.IsPrime] [q.IsPrime] (hq : q ≤ x) (hl : (maximalIdeal R).comap ι = x) :
    ∃ Q : Ideal R, Q.IsPrime ∧ Q.comap ι = q ∧ Q ∈ (q.map ι).minimalPrimes := by
  letI := ι.toAlgebra
  haveI : Module.Flat A R := hf
  haveI : Algebra.HasGoingDown A R := Algebra.HasGoingDown.of_flat
  haveI : (maximalIdeal R).LiesOver x := ⟨hl.symm⟩
  obtain ⟨P, -, hp, hlo⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := q) (q := x) (maximalIdeal R) hq
  have hc : P.comap ι = q := hlo.over.symm
  have hne : q.map ι ≤ P := Ideal.map_le_iff_le_comap.2 hc.ge
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_minimalPrimes_le hne
  exact ⟨Q, hQ.1.1, le_antisymm (hc ▸ Ideal.comap_mono hQP) (Ideal.map_le_iff_le_comap.1 hQ.1.2), hQ⟩

private theorem dim_ge {R : Type} [CommRing R] [IsLocalRing R] (Q : Ideal R) [Q.IsPrime] (z : R)
    (hz : z ∈ maximalIdeal R) (hn : z ∉ Q) : 1 ≤ ringKrullDim (R ⧸ Q) := by
  have hp : ((maximalIdeal R).map (Ideal.Quotient.mk Q)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance))
  haveI hnt : Nontrivial (R ⧸ Q) := Ideal.Quotient.nontrivial_iff.2 (Ideal.IsPrime.ne_top inferInstance)
  haveI hdom : IsDomain (R ⧸ Q) := Ideal.Quotient.isDomain _
  have h0 : (0 : WithBot ℕ∞) < ringKrullDim (R ⧸ Q) := by
    refine Order.krullDim_pos_iff.2 ⟨⟨⊥, Ideal.isPrime_bot⟩, ⟨_, hp⟩, ?_⟩
    refine (PrimeSpectrum.asIdeal_lt_asIdeal _ _).1 (bot_lt_iff_ne_bot.2 fun e => ?_)
    have h1 : Ideal.Quotient.mk Q z ∈ (maximalIdeal R).map (Ideal.Quotient.mk Q) := Ideal.mem_map_of_mem _ hz
    have e' : (maximalIdeal R).map (Ideal.Quotient.mk Q) = ⊥ := e
    rw [e', Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at h1
    exact hn h1
  generalize ringKrullDim (R ⧸ Q) = d at h0 ⊢
  induction d using WithBot.recBotCoe with
  | bot => simp at h0
  | coe d => exact_mod_cast Order.one_le_iff_pos (α := ℕ∞).2 (by exact_mod_cast h0)

private theorem dim_fin {O Y : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing Y] [Algebra O Y]
    [Module.Finite O Y] : ringKrullDim Y ≤ 1 := by
  have h1 : ringKrullDim O = 1 :=
    IsPrincipalIdealRing.ringKrullDim_eq_one O (IsDiscreteValuationRing.not_isField O)
  rw [← h1]
  refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap O Y)) fun a b hab => ?_
  exact (PrimeSpectrum.asIdeal_lt_asIdeal _ _).1
    (Ideal.IsIntegral.comap_lt_comap ((PrimeSpectrum.asIdeal_lt_asIdeal _ _).2 hab))

private theorem dim_pt {l : ℕ} [Fact l.Prime] (c : Coef l) [Fr.IsCoef l c.O] (R : Type) [CommRing R] [Algebra c.O R]
    [IsCO c.O R] (y : R →ₐ[c.O] Qbar l) : ringKrullDim (R ⧸ RingHom.ker y) ≤ 1 := by
  haveI : Module.Finite c.O y.range := (coPt l c R y).1
  have hker : RingHom.ker (y.rangeRestrict : R →+* y.range) = RingHom.ker y := by
    ext a
    rw [RingHom.mem_ker, RingHom.mem_ker]
    exact Subtype.ext_iff
  have e : R ⧸ RingHom.ker y ≃+* y.range := (Ideal.quotEquivOfEq hker.symm).trans
    (RingHom.quotientKerEquivOfSurjective (f := (y.rangeRestrict : R →+* y.range)) y.rangeRestrict_surjective)
  rw [ringKrullDim_eq_of_ringEquiv e]
  exact dim_fin (O := c.O)

private noncomputable def zA {l : ℕ} [Fact l.Prime] (c : Coef l) (B : Type) [CommRing B] [Algebra c.O B] : ℤ_[l] →+* B :=
  (algebraMap c.O B).comp (algebraMap ℤ_[l] c.O)

private theorem td_pt {l : ℕ} [Fact l.Prime] (c : Coef l) {F : Fr.Frame l (ResidueField c.O)} {n : ℕ} (S : Fr.Space c.O F n)
    (ξ : S.A →ₐ[c.O] Qbar l) (h : ∀ a, ‖ξ a‖ ≤ 1) : S.td (RingHom.ker ξ) = 0 := by
  haveI hq : (RingHom.ker ξ).IsPrime := RingHom.ker_isPrime ξ
  have hφ : ∀ t, (ξ : S.A →+* Qbar l) (((algebraMap S.B S.A).comp (zA c S.B)) t) = algebraMap ℤ_[l] (Qbar l) t := fun t =>
    ((congrArg ξ (S.inc.commutes _)).trans (ξ.commutes _)).trans rfl
  have h2 : ∀ a, ∃ f : Polynomial ℤ_[l], f.Monic ∧ f.eval₂ ((algebraMap S.B S.A).comp (zA c S.B)) a ∈ RingHom.ker ξ := fun a => by
    obtain ⟨f, hf, h0⟩ := int_pt (ξ : S.A →+* Qbar l) h _ hφ a
    exact ⟨f, hf, RingHom.mem_ker.2 h0⟩
  exact td_zero (RingHom.ker ξ) (zA c S.B) h2

private theorem max_pt {l : ℕ} [Fact l.Prime] (c : Coef l) {F : Fr.Frame l (ResidueField c.O)} {n : ℕ} (S : Fr.Space c.O F n)
    (ξ : S.A →ₐ[c.O] Qbar l) (h : ∀ a, ‖(ξ : S.A →+* Qbar l) a‖ ≤ 1) : (nx (ξ : S.A →+* Qbar l) h).IsMaximal :=
  nx_max _ h (zA c S.A) fun t => (ξ.commutes _).trans rfl

private theorem dim_up {l : ℕ} [Fact l.Prime] {c : Coef l} [Fr.IsCoef l c.O] {F : Fr.Frame l (ResidueField c.O)} {C₀ n : ℕ}
    (hF : F.Ok C₀) (hn : n = 2 ∨ n = 3) (S : Fr.Space c.O F n) (ξ : S.A →ₐ[c.O] Qbar l) (h : ∀ a, ‖ξ a‖ ≤ 1)
    {x : Ideal S.A} (L : S.Loc x) (Q : Ideal L.R) (hQ : Q.IsPrime) (hc : L.im Q = RingHom.ker ξ) :
    ringKrullDim (L.R ⧸ Q) ≤ 1 := by
  have hup := (Fr.loc_dim hF hn S x L).1 Q hQ 0 (by rw [hc, td_pt c S ξ h]; simp)
  have hpi : L.π Q = RingHom.ker (ξ.comp S.inc) := by
    show S.π (L.im Q) = _
    rw [hc]
    ext b
    rfl
  obtain ⟨hco, -⟩ := Fr.co_B hF hn S
  haveI := hco
  have hd := dim_pt c S.B (ξ.comp S.inc)
  rw [hpi] at hup
  simpa using hup.trans (by simpa using hd)

private theorem l_mem {l : ℕ} {O R : Type} [CommRing O] [IsLocalRing O] [CharP (ResidueField O) l] [CommRing R] [Algebra O R]
    [IsCO O R] : ((l : ℕ) : R) ∈ maximalIdeal R := by
  rw [← res_eq_zero_iff O R, map_natCast]
  exact CharP.cast_eq_zero _ l

private theorem l_not {l : ℕ} [Fact l.Prime] {A R : Type} [CommRing A] [CommRing R] (ι : A →+* R) (ξ : A →+* Qbar l)
    (Q : Ideal R) (hc : ∀ a, ι a ∈ Q → ξ a = 0) : ((l : ℕ) : R) ∉ Q := fun h => by
  have h1 := hc (l : A) (by rw [map_natCast]; exact h)
  rw [map_natCast] at h1
  exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) h1

theorem UpperTheory.V.J.locAt :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) [Fr.IsCoef l c.O] (F : Fr.Frame l (ResidueField c.O)) (C₀ n : ℕ), F.Ok C₀ → (n = 2 ∨ n = 3) →
        ∀ (S : Fr.Space c.O F n), ∀ ξ : S.A →ₐ[c.O] Qbar l, IntPt S ξ → ∃ (x : Ideal S.A) (L : S.Loc x) (Q : Ideal L.R), Over S L (RingHom.ker ξ) Q := by
  intro l _ c _ F C₀ n hF hn S ξ hξ
  haveI hxm := max_pt c S ξ hξ.1
  have hB : S.mB ≤ S.π (nx (ξ : S.A →+* Qbar l) hξ.1) := fun b hb => hξ.2 b hb
  obtain ⟨L⟩ := Fr.loc_ex hF hn S _ hxm hB
  have hfl := (Fr.loc_flat hF hn S _ L).1
  haveI hq : (RingHom.ker ξ).IsPrime := RingHom.ker_isPrime ξ
  have hqx : RingHom.ker ξ ≤ nx (ξ : S.A →+* Qbar l) hξ.1 := fun a ha => by
    show ‖ξ a‖ < 1
    rw [RingHom.mem_ker.1 ha, norm_zero]
    exact one_pos
  obtain ⟨Q, hQ, hQc, hQm⟩ := @down S.A L.R _ _ _ (L.ι : S.A →+* L.R) hfl _ _ hxm.isPrime hq hqx L.lies
  haveI := hQ
  have hn' := l_not (l := l) (L.ι : S.A →+* L.R) (ξ : S.A →+* Qbar l) Q fun a ha => RingHom.mem_ker.1 (hQc.le ha)
  have d1 := dim_up hF hn S ξ hξ.1 L Q hQ hQc
  have d2 := dim_ge Q _ (l_mem (l := l) (O := L.O') (R := L.R)) hn'
  exact ⟨_, L, Q, hQ, hQc, hQm, le_antisymm d1 d2⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.CompDim
set_option linter.overlappingInstances false

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

private theorem dim_arith {h : ℕ∞} {D E : WithBot ℕ∞} {N N' a : ℕ}
    (h1 : (h : WithBot ℕ∞) + D = ((N + 1 : ℕ) : WithBot ℕ∞)) (h2 : h ≤ (N' : ℕ∞)) (h3 : N = N' + (a + 1))
    (h4 : D ≤ E + ((1 : ℕ) : WithBot ℕ∞)) : ((1 + a : ℕ) : WithBot ℕ∞) ≤ E := by
  induction E using WithBot.recBotCoe with
  | bot =>
    rw [WithBot.bot_add, le_bot_iff] at h4
    rw [h4, WithBot.add_bot] at h1
    exact absurd h1.symm (WithBot.natCast_ne_bot _)
  | coe E =>
    induction D using WithBot.recBotCoe with
    | bot =>
      rw [WithBot.add_bot] at h1
      exact absurd h1.symm (WithBot.natCast_ne_bot _)
    | coe D =>
      have h1' : h + D = ((N + 1 : ℕ) : ℕ∞) := by exact_mod_cast h1
      have h4' : D ≤ E + ((1 : ℕ) : ℕ∞) := by exact_mod_cast h4
      have : ((1 + a : ℕ) : ℕ∞) ≤ E := by
        induction E using ENat.recTopCoe with
        | top => exact le_top
        | coe e =>
          induction D using ENat.recTopCoe with
          | top => simp at h4'
          | coe d =>
            induction h using ENat.recTopCoe with
            | top => simp at h2
            | coe k =>
              have a1 : k + d = N + 1 := by exact_mod_cast h1'
              have a2 : k ≤ N' := by exact_mod_cast h2
              have a4 : d ≤ e + 1 := by exact_mod_cast h4'
              have : 1 + a ≤ e := by omega
              exact_mod_cast this
      exact_mod_cast this

private theorem min_below {A R : Type} [CommRing A] [CommRing R] (f : A →+* R) (hf : f.Flat) (Q : Ideal R)
    (hQ : Q.IsPrime) (P : Ideal A) (hP : P ∈ minimalPrimes A) (h : P ≤ Q.comap f) :
    ∃ P' ∈ minimalPrimes R, P'.comap f = P := by
  letI := f.toAlgebra
  haveI : Module.Flat A R := hf
  haveI : Algebra.HasGoingDown A R := Algebra.HasGoingDown.of_flat
  haveI : P.IsPrime := hP.1.1
  haveI : (Q.comap f).IsPrime := Ideal.IsPrime.comap f
  haveI : Q.LiesOver (Q.comap f) := ⟨rfl⟩
  obtain ⟨Q', -, hQ', hl⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := P) (q := Q.comap f) Q h
  obtain ⟨P', hP', hle⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal R)) (J := Q') bot_le
  refine ⟨P', hP', ?_⟩
  have e : Q'.comap f = P := hl.over.symm
  have h1 : P'.comap f ≤ P := e ▸ Ideal.comap_mono hle
  haveI : P'.IsPrime := hP'.1.1
  exact le_antisymm h1 (hP.2 ⟨Ideal.IsPrime.comap f, bot_le⟩ h1)

theorem UpperTheory.V.J.compDim :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) [Fr.IsCoef l c.O] (F : Fr.Frame l (ResidueField c.O)) (C₀ n : ℕ), F.Ok C₀ → (n = 2 ∨ n = 3) →
        ∀ (S : Fr.Space c.O F n), ∀ (q x : Ideal S.A) (L : S.Loc x) (Q : Ideal L.R), Over S L q Q → S.u.TI q → ∀ P ∈ minimalPrimes S.A, P ≤ q →
          ((1 + n * F.d : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (S.B ⧸ S.π P) := by
  intro l _ c _ F C₀ n hF hn S q x L Q hO hTI P hP hPq
  obtain ⟨hQ, hQq, -, -⟩ := hO
  have hflat := (Fr.loc_flat hF hn S x L).1
  obtain ⟨P', hP', hc⟩ := min_below (L.ι : S.A →+* L.R) hflat Q hQ P hP (by
    have : Q.comap (L.ι : S.A →+* L.R) = q := hQq
    rw [this]; exact hPq)
  have hPp : P'.IsPrime := hP'.1.1
  have him : L.im P' = P := hc
  have hoff : S.u.OffTri P :=
    ⟨fun h => hTI.1.1 (h.trans hPq), fun h => hTI.1.2 (h.trans hPq)⟩
  have htd : S.td (L.im P') ≤ ((1 : ℕ) : Cardinal) := by
    rw [him, Nat.cast_one]
    exact Fr.fibre hF hn S P hP.1.1 hoff
  have hdim := (Fr.loc_dim hF hn S x L).1 P' hPp 1 htd
  have hπ : L.π P' = S.π P := by
    show S.π (L.im P') = _
    rw [him]
  rw [hπ] at hdim
  obtain ⟨N, N', p, f, hN, hs, hk⟩ := Fr.pres hF hn S x L
  obtain ⟨e1, e2⟩ := htPres L.O' N N' L.R (p : MvPowerSeries (Fin N) L.O' →+* L.R) f hs hk P' hPp
  have h0 : P'.height = 0 := Ideal.height_eq_zero_iff.mpr hP'
  rw [h0, zero_add] at e2
  exact dim_arith e1 e2 (by rw [hN]) hdim
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.DomMin
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

theorem UpperTheory.V.J.domMin :
    ∀ (A : Type) [CommRing A] (q : Ideal A) [q.IsPrime], IsDomain (Localization.AtPrime q) → ∀ P ∈ minimalPrimes A, P ≤ q → ∀ a ∈ P, ∃ s ∉ P, s * a = 0 := by
  intro A _ q _ hD P hP hPq a ha
  letI : Nontrivial (Localization.AtPrime q) := hD.toNontrivial
  letI : NoZeroDivisors (Localization.AtPrime q) :=
    isCancelMulZero_iff_noZeroDivisors.mp hD.toIsCancelMulZero
  have hK : (RingHom.ker (algebraMap A (Localization.AtPrime q))).IsPrime := RingHom.ker_isPrime _
  have hle : RingHom.ker (algebraMap A (Localization.AtPrime q)) ≤ P := by
    intro x hx
    obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff q.primeCompl (Localization.AtPrime q) x).1 hx
    have h0 : (m : A) * x ∈ P := by rw [hm]; exact P.zero_mem
    exact (hP.1.1.mem_or_mem h0).resolve_left (fun h => m.2 (hPq h))
  have hge : P ≤ RingHom.ker (algebraMap A (Localization.AtPrime q)) := hP.2 ⟨hK, bot_le⟩ hle
  obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff q.primeCompl (Localization.AtPrime q) a).1 (hge ha)
  exact ⟨m, fun h => m.2 (hPq h), hm⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.RedCrit
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

theorem UpperTheory.V.J.redCrit :
    ∀ (A : Type) [CommRing A] [IsNoetherianRing A] (q : Ideal A), q.IsPrime → (∀ P ∈ associatedPrimes A A, P ≤ q → P ∈ minimalPrimes A) →
        (∀ P ∈ minimalPrimes A, P ≤ q → ∀ a ∈ P, ∃ s ∉ P, s * a = 0) → ∀ a : A, (∀ P : Ideal A, P.IsPrime → P ≤ q → a ∈ P) → ∃ s ∉ q, s * a = 0 := by
  intro A _ _ q hq h1 h2 a ha
  by_contra hcon
  push_neg at hcon
  let N : Submodule A A := Submodule.span A {a}
  have hann : ∀ x, x ∈ Module.annihilator A N ↔ x * a = 0 := by
    intro x
    rw [Module.mem_annihilator]
    constructor
    · intro h
      exact congrArg Subtype.val (h ⟨a, Submodule.mem_span_singleton_self a⟩)
    · intro h m
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp m.2
      apply Subtype.ext
      change x * (m : A) = 0
      rw [← hc, smul_eq_mul, mul_left_comm, h, mul_zero]
  have hle : Module.annihilator A N ≤ q := by
    intro x hx
    by_contra hxq
    exact hcon x hxq ((hann x).mp hx)
  obtain ⟨P, hP, hPq⟩ := Ideal.exists_minimalPrimes_le hle
  have hPass : P ∈ associatedPrimes A N :=
    Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes A N hP
  have hPA : P ∈ associatedPrimes A A :=
    associatedPrimes.subset_of_injective N.injective_subtype hPass
  have hPmin := h1 P hPA hPq
  obtain ⟨s, hsP, hs⟩ := h2 P hPmin hPq a (ha P hPmin.1.1 hPq)
  exact hsP (hP.1.2 ((hann s).mpr hs))
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.RegDom
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

private theorem exists_der (O T : Type) [CommRing O] [CommRing T] [IsLocalRing T] [Algebra O T]
    [Algebra.FormallySmooth O (ResidueField T)] :
    ∃ r : Derivation O T (maximalIdeal T).Cotangent,
      ∀ (t : T) (ht : t ∈ maximalIdeal T), r t = - (maximalIdeal T).toCotangent ⟨t, ht⟩ := by
  set m := maximalIdeal T with hm
  let g : (T ⧸ m ^ 2) →ₐ[O] ResidueField T :=
    Ideal.Quotient.liftₐ (m ^ 2) (IsScalarTower.toAlgHom O T (ResidueField T)) (fun a ha => by
      have : a ∈ m := Ideal.pow_le_self two_ne_zero ha
      exact (residue_eq_zero_iff a).2 this)
  have hg : ∀ a : T, g (Ideal.Quotient.mk _ a) = residue T a := fun a => rfl
  have hmem : ∀ a ∈ m, Ideal.Quotient.mk (m ^ 2) a ∈ m.cotangentIdeal := fun a ha =>
    Submodule.mem_map_of_mem ha
  have hker : RingHom.ker (g : (T ⧸ m ^ 2) →+* ResidueField T) = m.cotangentIdeal := by
    ext b
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
    constructor
    · intro h
      refine hmem a ((residue_eq_zero_iff a).1 ?_)
      rw [← hg]
      exact h
    · rintro ⟨a', ha', h⟩
      rw [RingHom.mem_ker]
      show g (Ideal.Quotient.mk _ a) = 0
      have h' : Ideal.Quotient.mk (m ^ 2) a' = Ideal.Quotient.mk (m ^ 2) a := h
      rw [← h', hg]
      exact (residue_eq_zero_iff a').2 ha'
  have hsurj : Function.Surjective g := fun y => by
    obtain ⟨a, rfl⟩ := residue_surjective y
    exact ⟨Ideal.Quotient.mk _ a, rfl⟩
  have hnil : IsNilpotent (RingHom.ker (g : (T ⧸ m ^ 2) →+* ResidueField T)) :=
    ⟨2, by rw [hker]; exact m.cotangentIdeal_square⟩
  let s : ResidueField T →ₐ[O] (T ⧸ m ^ 2) :=
    Algebra.FormallySmooth.liftOfSurjective (AlgHom.id O _) g hsurj hnil
  have hs : ∀ x, g (s x) = x := fun x =>
    Algebra.FormallySmooth.liftOfSurjective_apply (AlgHom.id O _) g hsurj hnil x
  let f : T →ₐ[O] (T ⧸ m ^ 2) := s.comp (IsScalarTower.toAlgHom O T (ResidueField T))
  have e : (Ideal.Quotient.mkₐ O m.cotangentIdeal).comp f =
      IsScalarTower.toAlgHom O T ((T ⧸ m ^ 2) ⧸ m.cotangentIdeal) := by
    ext t
    show Ideal.Quotient.mk m.cotangentIdeal (f t) = Ideal.Quotient.mk m.cotangentIdeal (Ideal.Quotient.mk (m ^ 2) t)
    rw [Ideal.Quotient.eq, ← hker, RingHom.mem_ker]
    show g (s (residue T t) - Ideal.Quotient.mk _ t) = 0
    rw [map_sub, hs, hg, sub_self]
  let d := derivationToSquareZeroOfLift m.cotangentIdeal m.cotangentIdeal_square f e
  refine ⟨m.cotangentEquivIdeal.symm.toLinearMap.compDer d, fun t ht => ?_⟩
  have hf : f t = 0 := by
    show s (residue T t) = 0
    rw [(residue_eq_zero_iff t).2 ht, map_zero]
  have hd : d t = - ⟨Ideal.Quotient.mk (m ^ 2) t, hmem t ht⟩ := by
    apply Subtype.ext
    show f t - Ideal.Quotient.mk (m ^ 2) t = _
    rw [hf, zero_sub]
    rfl
  change m.cotangentEquivIdeal.symm.toLinearMap (d t) = _
  rw [hd, m.cotangentEquivIdeal.symm.toLinearMap.map_neg]
  congr 1
  exact m.cotangentEquivIdeal_symm_apply t ht

private theorem formally_smooth_of_char_zero_field (O E k : Type) [CommRing O] [IsDomain O] [Field E] [Algebra O E] [IsFractionRing O E]
    [Field k] [CharZero k] [Algebra O k] [Algebra E k] [IsScalarTower O E k] [Algebra.IsAlgebraic O k] :
    Algebra.FormallySmooth O k := by
  haveI : Algebra.IsAlgebraic E k := (IsFractionRing.comap_isAlgebraic_iff (A := O) (K := E) (C := k)).1 inferInstance
  haveI : CharZero E := (algebraMap E k).charZero
  haveI : Algebra.IsSeparable E k := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : Algebra.FormallyEtale E k := Algebra.FormallyEtale.of_isSeparable _ _
  haveI : Algebra.FormallyEtale O E := Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors O)
  haveI : Algebra.FormallyEtale O k := Algebra.FormallyEtale.comp O E k
  exact inferInstance

private theorem formallySmooth_res (O K k : Type) [CommRing O] [IsDomain O] [Field K] [Algebra O K] [FaithfulSMul O K]
    [CharZero K] [Algebra.IsAlgebraic O K] [Field k] [Algebra O k] (ι : k →+* K)
    (hι : ∀ a, ι (algebraMap O k a) = algebraMap O K a) : Algebra.FormallySmooth O k := by
  letI : Algebra k K := ι.toAlgebra
  haveI : IsScalarTower O k K := IsScalarTower.of_algebraMap_eq fun a => (hι a).symm
  haveI : CharZero k := ι.charZero
  haveI : FaithfulSMul O k := (faithfulSMul_iff_algebraMap_injective O k).2
    (Function.Injective.of_comp (f := ι) (by
      have : (ι ∘ algebraMap O k) = algebraMap O K := funext hι
      rw [this]
      exact FaithfulSMul.algebraMap_injective O K))
  haveI : Algebra.IsAlgebraic O k := Algebra.IsAlgebraic.tower_bot_of_injective (A := K) ι.injective
  letI : Algebra (FractionRing O) k := FractionRing.liftAlgebra O k
  haveI : IsScalarTower O (FractionRing O) k := FractionRing.isScalarTower_liftAlgebra O k
  exact formally_smooth_of_char_zero_field O (FractionRing O) k

private theorem algebraic_coef (l : ℕ) [Fact l.Prime] (c : Coef l) : Algebra.IsAlgebraic c.O (Qbar l) := by
  haveI : Algebra.IsAlgebraic ℤ_[l] (Qbar l) :=
    (IsFractionRing.comap_isAlgebraic_iff (A := ℤ_[l]) (K := ℚ_[l]) (C := Qbar l)).2 inferInstance
  refine Algebra.IsAlgebraic.extendScalars (R := ℤ_[l]) ?_
  refine Function.Injective.of_comp (f := algebraMap c.O (Qbar l)) ?_
  have : (algebraMap c.O (Qbar l)) ∘ (algebraMap ℤ_[l] c.O) = algebraMap ℤ_[l] (Qbar l) :=
    funext fun a => (IsScalarTower.algebraMap_apply _ _ _ a).symm
  rw [this, IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] (Qbar l), RingHom.coe_comp]
  exact (algebraMap ℚ_[l] (Qbar l)).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l])

section Pt

variable {O A K T : Type} [CommRing O] [CommRing A] [Field K] [Algebra O A] [Algebra O K]
  (ξ : A →ₐ[O] K) [(RingHom.ker ξ).IsPrime] [CommRing T] [IsLocalRing T] [Algebra A T]
  [IsLocalization.AtPrime T (RingHom.ker ξ)]

include ξ in
private theorem exists_frac (t : T) : ∃ (a u : A), u ∉ RingHom.ker ξ ∧ algebraMap A T u * t = algebraMap A T a := by
  obtain ⟨a, u, rfl⟩ := IsLocalization.exists_mk'_eq (RingHom.ker ξ).primeCompl t
  exact ⟨a, u, u.2, IsLocalization.mk'_spec' T a u⟩

private theorem exists_res : ∃ ι : ResidueField T →+* K, ∀ a, ι (residue T (algebraMap A T a)) = ξ a := by
  have hu : ∀ y : (RingHom.ker ξ).primeCompl, IsUnit ((ξ : A →+* K) y) := fun y =>
    isUnit_iff_ne_zero.2 fun h => y.2 (RingHom.mem_ker.2 h)
  let ξ' : T →+* K := IsLocalization.lift (M := (RingHom.ker ξ).primeCompl) (g := (ξ : A →+* K)) hu
  have hξ : ∀ a, ξ' (algebraMap A T a) = ξ a := fun a => IsLocalization.lift_eq hu a
  haveI : IsLocalHom ξ' := ⟨fun t ht => by
    obtain ⟨a, u, hu', h⟩ := exists_frac ξ t
    have h1 : ξ u * ξ' t = ξ a := by rw [← hξ, ← hξ, ← map_mul, h]
    have h2 : ξ a ≠ 0 := by
      rw [← h1]
      exact mul_ne_zero (fun h0 => hu' (RingHom.mem_ker.2 h0)) ht.ne_zero
    have h3 : IsUnit (algebraMap A T a) :=
      IsLocalization.map_units T (⟨a, fun h0 => h2 (RingHom.mem_ker.1 h0)⟩ : (RingHom.ker ξ).primeCompl)
    rw [← h] at h3
    exact isUnit_of_mul_isUnit_right h3⟩
  exact ⟨ResidueField.lift ξ', fun a => by rw [ResidueField.lift_residue_apply, hξ]⟩

private theorem rank_ge [Algebra O T] [IsScalarTower O A T] [IsNoetherianRing T]
    [Algebra.FormallySmooth O (ResidueField T)] :
    ((Module.finrank (ResidueField T) (CotangentSpace T) : ℕ) : Cardinal) ≤ Module.rank K (PtDer ξ K) := by
  obtain ⟨ι, hι⟩ := exists_res (T := T) ξ
  obtain ⟨r, hr⟩ := exists_der O T
  letI : Algebra (ResidueField T) K := ι.toAlgebra
  have hact : ∀ (x : A) (φ : CotangentSpace T →ₗ[ResidueField T] K) (c : CotangentSpace T),
      φ (algebraMap A T x • c) = ξ x * φ c := fun x φ c => by
    have h1 : algebraMap A T x • c = residue T (algebraMap A T x) • c := (algebraMap_smul _ _ c).symm
    rw [h1, φ.map_smul, Algebra.smul_def]
    show ι _ * _ = _
    rw [hι]
  let Dl : (CotangentSpace T →ₗ[ResidueField T] K) → (A →ₗ[O] K) := fun φ =>
    { toFun := fun x => φ (r (algebraMap A T x))
      map_add' := fun x y => by simp only [map_add (f := _)]
      map_smul' := fun a x => by
        have h1 : algebraMap A T (a • x) = a • algebraMap A T x :=
          map_smul (IsScalarTower.toAlgHom O A T) a x
        have h2 : a • r (algebraMap A T x) = algebraMap A T (algebraMap O A a) • r (algebraMap A T x) := by
          rw [← IsScalarTower.algebraMap_apply, algebraMap_smul]
        rw [h1, r.map_smul, h2, hact, AlgHom.commutes, Algebra.smul_def, RingHom.id_apply] }
  have hDl : ∀ φ, Dl φ ∈ PtDer ξ K := fun φ f g => by
    show φ (r (algebraMap A T (f * g))) = ξ f • φ (r (algebraMap A T g)) + ξ g • φ (r (algebraMap A T f))
    rw [map_mul, r.leibniz, map_add (f := _), hact, hact]
    rfl
  let Ψ : (CotangentSpace T →ₗ[ResidueField T] K) →ₗ[K] PtDer ξ K :=
    { toFun := fun φ => ⟨Dl φ, hDl φ⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective Ψ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro φ h0
    have h1 : ∀ x, φ (r (algebraMap A T x)) = 0 := fun x =>
      congrArg (fun D : PtDer ξ K => (D : A →ₗ[O] K) x) h0
    refine LinearMap.ext fun c => ?_
    obtain ⟨⟨t, ht⟩, rfl⟩ := (maximalIdeal T).toCotangent_surjective c
    obtain ⟨a, u, hu, h⟩ := exists_frac ξ t
    have ha : algebraMap A T a ∈ maximalIdeal T := by
      rw [← h]
      exact Ideal.mul_mem_left _ _ ht
    have h2 : (⟨algebraMap A T a, ha⟩ : maximalIdeal T) = algebraMap A T u • ⟨t, ht⟩ :=
      Subtype.ext h.symm
    have h3 := h1 a
    rw [hr _ ha, h2, map_smul, map_neg, neg_eq_zero] at h3
    have h4 : ξ u * φ ((maximalIdeal T).toCotangent ⟨t, ht⟩) = 0 := by
      rw [← hact]
      exact h3
    exact (mul_eq_zero.1 h4).resolve_left fun h0 => hu (RingHom.mem_ker.2 h0)
  haveI : Module.Free (ResidueField T) (CotangentSpace T) := Module.Free.of_divisionRing _ _
  let b := Module.finBasis (ResidueField T) (CotangentSpace T)
  have h5 := LinearMap.rank_le_of_injective (Ψ ∘ₗ (b.constr K).toLinearMap)
    (hinj.comp (b.constr K).injective)
  rwa [rank_fin_fun] at h5

end Pt

theorem UpperTheory.V.J.regDom :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (A : Type) [CommRing A] [IsNoetherianRing A] [Algebra c.O A] (ξ : A →ₐ[c.O] Qbar l) (d : ℕ) [(RingHom.ker ξ).IsPrime],
        Module.rank (Qbar l) (PtDer ξ (Qbar l)) ≤ d → (d : ℕ∞) ≤ (RingHom.ker ξ).height → IsDomain (Localization.AtPrime (RingHom.ker ξ)) := by
  intro l _ c A _ _ _ ξ d _ h1 h2
  haveI : IsNoetherianRing (Localization.AtPrime (RingHom.ker ξ)) :=
    IsLocalization.isNoetherianRing (RingHom.ker ξ).primeCompl _ inferInstance
  obtain ⟨ι, hι⟩ := exists_res (T := Localization.AtPrime (RingHom.ker ξ)) ξ
  haveI := algebraic_coef l c
  haveI : Algebra.FormallySmooth c.O (ResidueField (Localization.AtPrime (RingHom.ker ξ))) :=
    formallySmooth_res c.O (Qbar l) _ ι fun a => by
      have := hι (algebraMap c.O A a)
      rwa [AlgHom.commutes, ← IsScalarTower.algebraMap_apply] at this
  have h3 := (rank_ge (T := Localization.AtPrime (RingHom.ker ξ)) ξ).trans h1
  have h4 : Module.finrank (ResidueField (Localization.AtPrime (RingHom.ker ξ)))
      (CotangentSpace (Localization.AtPrime (RingHom.ker ξ))) ≤ d := by exact_mod_cast h3
  haveI : IsRegularLocalRing (Localization.AtPrime (RingHom.ker ξ)) := by
    apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
    rw [spanFinrank_maximalIdeal_eq_finrank_cotangentSpace,
      IsLocalization.AtPrime.ringKrullDim_eq_height (RingHom.ker ξ)]
    have h5 : ((Module.finrank (ResidueField (Localization.AtPrime (RingHom.ker ξ)))
      (CotangentSpace (Localization.AtPrime (RingHom.ker ξ))) : ℕ) : ℕ∞) ≤ (RingHom.ker ξ).height :=
      (by exact_mod_cast h4 : ((Module.finrank _ _ : ℕ) : ℕ∞) ≤ d).trans h2
    exact_mod_cast h5
  exact GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.isDomain
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.HeightLeOfDim
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

private theorem height_le_of_dim {R : Type} [CommRing R] [IsLocalRing R] (Q : Ideal R) [hQ : Q.IsPrime]
    (h1 : ringKrullDim (R ⧸ Q) = 1) (N : ℕ)
    (h : ∀ P : Ideal R, P.IsPrime → P ≤ Q → ringKrullDim (R ⧸ P) ≤ ((N + 1 : ℕ) : WithBot ℕ∞)) :
    Q.height ≤ (N : ℕ∞) := by
  have e : Q.height = Order.height (⟨Q, hQ⟩ : PrimeSpectrum R) :=
    PrimeSpectrum.height_eq_orderHeight (⟨Q, hQ⟩ : PrimeSpectrum R)
  rw [e, Order.height_le_iff]
  intro p hp
  have hQm : Q < maximalIdeal R := by
    refine lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hQ.ne_top) ?_
    intro hEq
    haveI : Q.IsMaximal := hEq ▸ IsLocalRing.maximalIdeal.isMaximal R
    letI := Ideal.Quotient.field Q
    rw [ringKrullDim_eq_zero_of_field] at h1
    exact absurd h1 (by decide)
  have hlt : p.last < (⟨maximalIdeal R, inferInstance⟩ : PrimeSpectrum R) :=
    lt_of_le_of_lt hp hQm
  let s : LTSeries (PrimeSpectrum R) := p.snoc _ hlt
  set P := p.head.asIdeal with hPdef
  have hPp : P.IsPrime := p.head.isPrime
  have hPQ : P ≤ Q := (LTSeries.monotone p (Fin.zero_le (Fin.last _))).trans hp
  have hmem : ∀ i, s i ∈ PrimeSpectrum.zeroLocus (P : Set R) := by
    intro i
    have h0 := LTSeries.monotone s (Fin.zero_le i)
    rw [show s 0 = p.head from RelSeries.head_snoc _ _ _] at h0
    rw [PrimeSpectrum.mem_zeroLocus]
    exact fun a ha => h0 ha
  let t : LTSeries (PrimeSpectrum.zeroLocus (P : Set R)) :=
    ⟨s.length, fun i => ⟨s i, hmem i⟩, fun i => s.step i⟩
  have ht : ((s.length : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ P) := by
    rw [ringKrullDim_quotient]
    exact Order.le_krullDim_iff.2 ⟨t, rfl⟩
  have hb := ht.trans (h P hPp hPQ)
  have hsl : s.length = p.length + 1 := RelSeries.snoc_length _ _ _
  rw [hsl] at hb
  have hb' : p.length + 1 ≤ N + 1 := by exact_mod_cast hb
  exact_mod_cast (by omega : p.length ≤ N)

theorem UpperTheory.V.J.htUp :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) [Fr.IsCoef l c.O] (F : Fr.Frame l (ResidueField c.O)) (C₀ n : ℕ), F.Ok C₀ → (n = 2 ∨ n = 3) →
        ∀ (S : Fr.Space c.O F n), ∀ (M : Ideal S.B), AllGood S M → (∀ Z : Ideal S.B, Z.IsPrime → M ≤ Z → ringKrullDim (S.B ⧸ Z) ≤ ((1 + n * F.d : ℕ) : WithBot ℕ∞)) →
          ∀ (q x : Ideal S.A) (L : S.Loc x) (Q : Ideal L.R), Over S L q Q → S.u.TI q → Q.height ≤ ((n * F.d + 1 : ℕ) : ℕ∞) := by
  intro l _ c _ F C₀ n hF hn S M hM hZ q x L Q hO hT
  obtain ⟨hQp, him, -, hdim⟩ := hO
  refine height_le_of_dim Q hdim (n * F.d + 1) ?_
  intro P hP hPQ
  have hPq : L.im P ≤ q := him ▸ Ideal.comap_mono hPQ
  have hTP : S.u.TI (L.im P) :=
    ⟨⟨fun h => hT.1.1 (h.trans hPq), fun h => hT.1.2 (h.trans hPq)⟩,
      fun h3 h => hT.2 h3 (h.trans hPq)⟩
  have hprime : (L.im P).IsPrime := Ideal.comap_isPrime _ _
  have htd : S.td (L.im P) ≤ ((1 : ℕ) : Cardinal) := by
    rw [Nat.cast_one]
    exact Fr.fibre hF hn S _ hprime hTP.1
  have h1 := (Fr.loc_dim hF hn S x L).1 P hP 1 htd
  have hπ : (L.π P).IsPrime := Ideal.comap_isPrime _ _
  have h2 := hZ (L.π P) hπ (hM _ hprime hTP)
  calc ringKrullDim (L.R ⧸ P) ≤ ringKrullDim (S.B ⧸ L.π P) + ((1 : ℕ) : WithBot ℕ∞) := h1
    _ ≤ ((1 + n * F.d : ℕ) : WithBot ℕ∞) + ((1 : ℕ) : WithBot ℕ∞) := by gcongr
    _ = ((n * F.d + 1 + 1 : ℕ) : WithBot ℕ∞) := by
      rw [← Nat.cast_add]
      congr 1
      omega
end

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

theorem UpperTheory.V.J.redAbs : UpperTheory.V.J.RedAbs := by
  set_option synthInstance.maxHeartbeats 200000 in
  intro l _ c _ F C₀ n hF hn S M Gd hAG hDB hTan ξ hξ hTI b hb
  haveI hA : IsNoetherianRing S.A := (Fr.gr_A hF hn S).2.2.2.2.2.1
  haveI hq : (RingHom.ker ξ).IsPrime := RingHom.ker_isPrime _
  obtain ⟨x, L, Q, hO⟩ := UpperTheory.V.J.locAt l c F C₀ n hF hn S ξ hξ
  have hN : Q.height ≤ ((n * F.d + 1 : ℕ) : ℕ∞) :=
    UpperTheory.V.J.htUp l c F C₀ n hF hn S M hAG (fun Z hZ hMZ => (hDB Z hZ hMZ).1) _ x L Q hO hTI
  have hass := (UpperTheory.V.J.htLow l c F C₀ n hF hn S _ x L Q hO).2 hN
  have hTIle : ∀ P : Ideal S.A, P ≤ RingHom.ker ξ → S.u.TI P := fun P hle =>
    ⟨⟨fun h => hTI.1.1 (h.trans hle), fun h => hTI.1.2 (h.trans hle)⟩, fun h3 h => hTI.2 h3 (h.trans hle)⟩
  have hmin : ∀ P ∈ minimalPrimes S.A, P ≤ RingHom.ker ξ → ∀ a ∈ P, ∃ s ∉ P, s * a = 0 := by
    intro P hP hPq
    have hPp : P.IsPrime := hP.1.1
    have hPT := hTIle P hPq
    have hZp : (S.π P).IsPrime := Ideal.IsPrime.comap _
    have hMZ : M ≤ S.π P := hAG P hPp hPT
    obtain ⟨hle, hdn⟩ := hDB (S.π P) hZp hMZ
    have hdim : ringKrullDim (S.B ⧸ S.π P) = ((1 + n * F.d : ℕ) : WithBot ℕ∞) :=
      le_antisymm hle (UpperTheory.V.J.compDim l c F C₀ n hF hn S _ x L Q hO hTI P hP hPq)
    obtain ⟨ξ', hV, hT', hPk, hG⟩ := UpperTheory.V.J.genPt l c F C₀ n hF hn S P Gd hP hPT (hdn hdim)
    haveI hq' : (RingHom.ker ξ').IsPrime := RingHom.ker_isPrime _
    have hMk : M ≤ RingHom.ker (ξ'.comp S.inc) := fun m hm => hPk (hMZ hm)
    have hF1 := hTan ξ' hV hT' hMk hG
    have hrk : Module.rank (Qbar l) (PtDer ξ' (Qbar l)) ≤ ((n * F.d + 1 : ℕ) : Cardinal) := by
      refine (UpperTheory.V.J.tanBound l c F C₀ n hF hn S ξ' hV.1).trans ?_
      rw [Nat.cast_add, Nat.cast_one]
      gcongr
    obtain ⟨x', L', Q', hO'⟩ := UpperTheory.V.J.locAt l c F C₀ n hF hn S ξ' hV.1
    have hht := (UpperTheory.V.J.htLow l c F C₀ n hF hn S _ x' L' Q' hO').1
    have hdom := UpperTheory.V.J.regDom l c S.A ξ' (n * F.d + 1) hrk hht
    exact UpperTheory.V.J.domMin S.A (RingHom.ker ξ') hdom P hP hPk
  obtain ⟨s, hs, hsb⟩ := UpperTheory.V.J.redCrit S.A (RingHom.ker ξ) hq hass hmin (S.inc b)
    (fun P hPp hPq => hAG P hPp (hTIle P hPq) hb)
  exact ⟨s, fun h => hs (RingHom.mem_ker.2 h), hsb⟩
