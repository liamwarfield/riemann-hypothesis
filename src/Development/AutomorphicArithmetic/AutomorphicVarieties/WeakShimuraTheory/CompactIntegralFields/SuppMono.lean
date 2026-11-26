module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.ChCore
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.Pur
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.RestrT
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.OverFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.FlagFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidualChains.RtFacts

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidualChains.ExistsResidualDatumOverRestrictionToRationals
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Chain.exists_residual_datum_over_restriction_to_rationals :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → ∀ (k : Type) [Field k] (a : c.O →+* k), (∀ x ∈ maximalIdeal c.O, a x = 0) →
      ∀ c₀ : PD Unit (G ℚ Ω) k, (frQ D T.pr (resQ T.F T.g0)).IsRes a c₀ → c₀.In nP →
      ∃ s : PD T.ι (G T.F Ω) k, (T.fr ∅).IsRes a s ∧ T.OverQ c₀ s := by
  intro _ Ω _ _ _ l _ c D T hT k _ a ha c₀ hc₀ hin
  have hG : D.Good := by
    rcases hT.2 with h | h
    · exact h.1.1
    · exact h.1.1
  haveI : NumberField T.F := T.nF
  have hl : l.Prime := Fact.out
  have hpl : ∀ v, ∃ g : G ℚ Ω, (∀ x : Ω, g x ∈ T.pl v ↔ x ∈ D.pl l) ∧
      (∀ s ∈ Dec (T.pl v), g⁻¹ * resQ T.F s * g ∈ Dec (D.pl l)) ∧
      (∀ s ∈ Ine (T.pl v), g⁻¹ * resQ T.F s * g ∈ Ine (D.pl l)) := fun v =>
    Rq.placeMove T.F l hl (T.pl v) (D.pl l) (T.ovl v) (hG.pl_over l hl)
  choose g hg using hpl
  have hne : ∀ h : G ℚ Ω, a ((frQ D T.pr (resQ T.F T.g0)).ν h : c.O) ≠ 0 := by
    intro h
    exact ((Units.map a.toMonoidHom) ((frQ D T.pr (resQ T.F T.g0)).ν h)).ne_zero
  have hn : ∀ v, ∃ n' : UpperTheory.V.GradeZeroInterpolatingElement.M4 k, IsLow n' ∧ IsUp (adj n' * c₀.r (g v) * c₀.n ()) ∧
      (SuppM nP (c₀.r (g v)) ∧ SuppM qQ (c₀.n ()) → SuppM qQ n') := fun v =>
    Rt.flagNew k _ (c₀.r (g v)) (c₀.n ()) (hne (g v)) (hc₀.pair.mult (g v)) (hc₀.pair.low ())
      (Or.inl ⟨hin.1 (g v), hin.2 ()⟩)
  choose n' hn' using hn
  have key : ∀ v, ∀ s ∈ Dec (T.pl v), IsUp (adj (n' v) * c₀.r (resQ T.F s) * n' v) ∧
      ∀ i, (adj (n' v) * c₀.r (resQ T.F s) * n' v) i i = a ((frQ D T.pr (resQ T.F T.g0)).χ i (resQ T.F s) : c.O) := by
    intro v s hs
    have hconj := (hg v).2.1 s hs
    have hX : c₀.r (g v) * c₀.r (g v)⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    obtain ⟨h1, h2⟩ := Rt.flagMove k (c₀.r (g v)) (c₀.r (g v)⁻¹)
      (c₀.r ((g v)⁻¹ * resQ T.F s * g v)) (c₀.n ()) (n' v) hX (hc₀.pair.low ()) (hn' v).1
      (hn' v).2.1 (hc₀.pair.flag () _ hconj)
    have he : c₀.r (g v) * c₀.r ((g v)⁻¹ * resQ T.F s * g v) * c₀.r (g v)⁻¹ =
        c₀.r (resQ T.F s) := by
      rw [← map_mul, ← map_mul]
      congr 1
      group
    rw [he] at h1 h2
    refine ⟨h1, fun i => ?_⟩
    rw [h2 i]
    refine (hc₀.res.char () _ hconj i).trans ?_
    rw [map_mul, map_mul, map_inv, mul_comm _ ((frQ D T.pr (resQ T.F T.g0)).χ i (resQ T.F s)), inv_mul_cancel_right]
  refine ⟨⟨c₀.r.comp (resQ T.F), n'⟩, ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_⟩,
    ⟨rfl, fun v => ⟨(), g v, (hg v).1, (hn' v).2.1⟩⟩⟩
  · intro h
    exact hc₀.pair.mult (resQ T.F h)
  · rintro h ⟨A, hA, hI, hb⟩
    show c₀.r (resQ T.F h) = 1
    have hAl : ¬ A.valuation (l : Ω) < 1 := hA l (Finset.mem_insert_self _ _)
    by_cases hS : ∃ p ∈ D.Sb, A.valuation (p : Ω) < 1
    · obtain ⟨p, hp, hpA⟩ := hS
      have hpS : p ∈ D.S := (Finset.mem_filter.1 hp).1
      have hpp : p.Prime := hG.S_prime p hpS
      obtain ⟨γ, -, -, hγ⟩ := Rq.placeMove T.F p hpp A (D.pl p) hpA (hG.pl_over p hpp)
      have hmem := hγ h hI
      have hψ : D.ψ (resQ T.F h) = 1 := by
        refine hT.1.kb A ?_ h hI hb
        intro q hq
        rw [Finset.mem_singleton] at hq
        subst hq
        exact hAl
      have hk := hc₀.pair.kill (γ⁻¹ * resQ T.F h * γ) (Or.inr ⟨p, hp, Subgroup.mem_inf.2 ⟨hmem, by
        rw [MonoidHom.mem_ker, map_mul, map_mul, hψ, mul_one, map_inv, inv_mul_cancel]⟩⟩)
      have hx : resQ T.F h = γ * (γ⁻¹ * resQ T.F h * γ) * γ⁻¹ := by group
      rw [hx, map_mul, map_mul, hk, mul_one, ← map_mul, mul_inv_cancel, map_one]
    · push_neg at hS
      refine hc₀.pair.kill _ (Or.inl ⟨A, ?_, hI, hb⟩)
      intro q hq
      rcases Finset.mem_insert.1 hq with rfl | hq
      · exact hAl
      · exact not_lt.2 (hS q hq)
  · exact hc₀.pair.nrm
  · intro v
    exact (hn' v).1
  · intro v s hs
    exact (key v s hs).1
  · intro v s hs i
    obtain ⟨hsD, m, hm⟩ := hs
    refine ((key v s hsD).2 i).trans ?_
    have hchar : CharP k l := by
      haveI := c.dvr
      haveI := c.fin
      have hmax : ((l : ℕ) : c.O) ∈ IsLocalRing.maximalIdeal c.O := by
        obtain ⟨Q, hQ, hQc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (R := ℤ_[l]) (S := c.O)
          (IsLocalRing.maximalIdeal ℤ_[l]) (IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _))
        change Q.comap (algebraMap ℤ_[l] c.O) = _ at hQc
        have hlQ : ((l : ℕ) : c.O) ∈ Q := by
          have h0 : ((l : ℕ) : ℤ_[l]) ∈ Q.comap (algebraMap ℤ_[l] c.O) := by
            rw [hQc, PadicInt.maximalIdeal_eq_span_p]
            exact Ideal.subset_span (Set.mem_singleton _)
          simpa using h0
        exact (IsLocalRing.mem_maximalIdeal _).2 fun hu =>
          hQ.ne_top (Ideal.eq_top_of_isUnit_mem _ hlQ hu)
      rw [CharP.charP_iff_prime_eq_zero hl]
      have h0 := ha _ hmax
      simpa using h0
    let φ : G T.F Ω →* kˣ := (Units.map a.toMonoidHom).comp
      (((frQ D T.pr (resQ T.F T.g0)).χ i).comp (resQ T.F))
    have hφv : ∀ x, (φ x : k) = c₀.r (resQ T.F x) i i := fun x =>
      (hc₀.res.diag (resQ T.F x) i).symm
    have hlc : IsLocallyConstant (fun x : G T.F Ω => c₀.r (resQ T.F x) i i) := by
      have h1 := (hc₀.cont i i 1).comp_continuous (UpperTheory.V.Af.continuous_restrictScalarsHom ℚ T.F Ω)
      refine IsLocallyConstant.desc _ (Ideal.Quotient.mk ((⊥ : Ideal k) ^ 1)) h1 ?_
      intro x y hxy
      rw [Ideal.Quotient.eq, pow_one, Ideal.mem_bot, sub_eq_zero] at hxy
      exact hxy
    have hcl : IsClosed ((φ.ker : Subgroup (G T.F Ω)) : Set (G T.F Ω)) := by
      have he : ((φ.ker : Subgroup (G T.F Ω)) : Set (G T.F Ω)) =
          (fun x : G T.F Ω => c₀.r (resQ T.F x) i i) ⁻¹' {1} := by
        ext x
        simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, Set.mem_singleton_iff,
          ← hφv, Units.val_eq_one]
      rw [he]
      exact (hlc.isClopen_fiber 1).isClosed
    have hcomm : ⁅Dec (T.pl v), Dec (T.pl v)⁆ ≤ φ.ker :=
      le_trans (Subgroup.commutator_mono le_top le_top) (Abelianization.commutator_subset_ker φ)
    have hker := Subgroup.topologicalClosure_minimal _ hcomm hcl hm
    rw [MonoidHom.mem_ker, map_pow] at hker
    have hx : (φ s : k) ^ (l ^ m) = 1 := by
      rw [← Units.val_pow_eq_pow_val, hker, Units.val_one]
    have hz : ((φ s : k) - 1) ^ (l ^ m) = 0 := by
      rw [sub_pow_char_pow, one_pow, hx, sub_self]
    exact sub_eq_zero.1 (pow_eq_zero_iff (pow_ne_zero _ hl.ne_zero) |>.1 hz)
  · intro h i
    exact hc₀.res.diag (resQ T.F h) i
  · intro v s hs i
    exact (key v s hs).2 i
  · exact Or.inl ⟨fun h => hin.1 (resQ T.F h), fun v => (hn' v).2.2 ⟨hin.1 _, hin.2 ()⟩⟩
  · intro i j N
    exact (hc₀.cont i j N).comp_continuous
      (UpperTheory.V.Af.continuous_restrictScalarsHom ℚ T.F Ω)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidualChains.EntIff
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Chain.entIff :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] (Φ : Fr O Γ) {k : Type} [Field k] (a : O →+* k)
      (c : PD Φ.ι Γ k), Φ.IsRes a c →
      (Supp nP c.r → (Ent c.r (-wPs) ↔ ∃ g, c.r g 2 0 ≠ 0)) ∧ (Supp nM c.r → (Ent c.r (-wAl) ↔ ∃ g, c.r g 1 0 ≠ 0)) := by
  intro O Γ _ _ _ Φ k _ a c hc
  have hadj : ∀ g, adj (c.r g⁻¹) = a ↑(Φ.ν g⁻¹) • c.r g := by
    intro g
    have hm : adj (c.r g⁻¹) * c.r g⁻¹ = a ↑(Φ.ν g⁻¹) • 1 := hc.pair.mult g⁻¹
    calc adj (c.r g⁻¹) = adj (c.r g⁻¹) * (c.r g⁻¹ * c.r g) := by
          rw [← map_mul, inv_mul_cancel, map_one, mul_one]
      _ = a ↑(Φ.ν g⁻¹) • c.r g := by rw [← mul_assoc, hm, smul_mul_assoc, one_mul]
  have hν : ∀ g, a ↑(Φ.ν g) ≠ 0 := fun g => ((Φ.ν g).isUnit.map a).ne_zero
  have ent : ∀ {R : Type} [CommRing R] (X : M4 R), adj X 3 1 = - X 2 0 ∧ adj X 3 2 = X 1 0 := by
    intro R _ X
    simp [adj_apply, sgn]
  have e31 : ∀ g, c.r g 3 1 ≠ 0 → c.r g⁻¹ 2 0 ≠ 0 := by
    intro g hg h0
    have := (ent (c.r g⁻¹)).1
    rw [hadj, h0, neg_zero, Matrix.smul_apply, smul_eq_mul] at this
    exact mul_ne_zero (hν _) hg this
  have e32 : ∀ g, c.r g 3 2 ≠ 0 → c.r g⁻¹ 1 0 ≠ 0 := by
    intro g hg h0
    have := (ent (c.r g⁻¹)).2
    rw [hadj, h0, Matrix.smul_apply, smul_eq_mul] at this
    exact mul_ne_zero (hν _) hg this
  have wP : ∀ i j : Fin 4, wt i j = -wPs → (i = 2 ∧ j = 0) ∨ (i = 3 ∧ j = 1) := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [wt, lamW, muW, wPs, Prod.ext_iff]
  have wA : ∀ i j : Fin 4, wt i j = -wAl → (i = 1 ∧ j = 0) ∨ (i = 3 ∧ j = 2) := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [wt, lamW, muW, wAl, Prod.ext_iff]
  have w20 : wt 2 0 = -wPs := by simp [wt, lamW, muW, wPs]
  have w10 : wt 1 0 = -wAl := by simp [wt, lamW, muW, wAl]
  refine ⟨fun _ => ⟨?_, ?_⟩, fun _ => ⟨?_, ?_⟩⟩
  · rintro ⟨g, i, j, hw, hne⟩
    rcases wP i j hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨g, hne⟩
    · exact ⟨g⁻¹, e31 g hne⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, 2, 0, w20, hg⟩
  · rintro ⟨g, i, j, hw, hne⟩
    rcases wA i j hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨g, hne⟩
    · exact ⟨g⁻¹, e32 g hne⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, 1, 0, w10, hg⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidualChains.LvSmulOne
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Ws.Chain.Levi

variable {k : Type} [Field k]

private def Par (X : M4 k) : Prop := ∀ i j : Fin 4, i.1 < 2 → 2 ≤ j.1 → X i j = 0

private def lv (X : M4 k) : M4 k := Matrix.of fun i j => if (i.1 < 2 ↔ j.1 < 2) then X i j else 0

private theorem lv_apply (X : M4 k) (i j : Fin 4) : lv X i j = if (i.1 < 2 ↔ j.1 < 2) then X i j else 0 := rfl

private theorem lv_diag (X : M4 k) (i : Fin 4) : lv X i i = X i i := by
  rw [lv_apply, if_pos Iff.rfl]

end UpperTheory.V.Ws.Chain.Levi

private theorem levi_lemma {k : Type} [Field k] (X : M4 k) :
    adj (UpperTheory.V.Ws.Chain.Levi.lv X) = UpperTheory.V.Ws.Chain.Levi.lv (adj X) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj, UpperTheory.V.Ws.Chain.Levi.lv_apply] <;> rfl

private theorem levi_lv_mul_of_par {k : Type} [Field k] (X Y : M4 k) (hX : UpperTheory.V.Ws.Chain.Levi.Par X)
    (hY : UpperTheory.V.Ws.Chain.Levi.Par Y) :
    UpperTheory.V.Ws.Chain.Levi.lv (X * Y) = UpperTheory.V.Ws.Chain.Levi.lv X * UpperTheory.V.Ws.Chain.Levi.lv Y := by
  have h02 := hX 0 2 (by decide) (by decide)
  have h03 := hX 0 3 (by decide) (by decide)
  have h12 := hX 1 2 (by decide) (by decide)
  have h13 := hX 1 3 (by decide) (by decide)
  have g02 := hY 0 2 (by decide) (by decide)
  have g03 := hY 0 3 (by decide) (by decide)
  have g12 := hY 1 2 (by decide) (by decide)
  have g13 := hY 1 3 (by decide) (by decide)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [UpperTheory.V.Ws.Chain.Levi.lv_apply, Matrix.mul_apply, Fin.sum_univ_four,
      h02, h03, h12, h13, g02, g03, g12, g13]

private theorem levi_par_mul {k : Type} [Field k] (X Y : M4 k) (hX : UpperTheory.V.Ws.Chain.Levi.Par X)
    (hY : UpperTheory.V.Ws.Chain.Levi.Par Y) : UpperTheory.V.Ws.Chain.Levi.Par (X * Y) := by
  intro i j hi hj
  rw [Matrix.mul_apply, Fin.sum_univ_four, hY 0 j (by decide) hj, hY 1 j (by decide) hj,
    hX i 2 hi (by decide), hX i 3 hi (by decide)]
  simp

private theorem levi_par_adj {k : Type} [Field k] (X : M4 k) (hX : UpperTheory.V.Ws.Chain.Levi.Par X) :
    UpperTheory.V.Ws.Chain.Levi.Par (adj X) := by
  intro i j hi hj
  have h := hX j.rev i.rev (by rw [Fin.val_rev]; omega) (by rw [Fin.val_rev]; omega)
  simp [adj, h]

private theorem levi_par_of_apply_eq_zero_of_lt {k : Type} [Field k] (X : M4 k) (hX : ∀ i j : Fin 4, i < j → X i j = 0) :
    UpperTheory.V.Ws.Chain.Levi.Par X := by
  intro i j hi hj
  exact hX i j (Fin.lt_def.2 (by omega))

private theorem levi_lemma_6 {k : Type} [Field k] (X : M4 k) (hX : SuppM nM X) :
    ∀ i j : Fin 4, i < j → X i j = 0 := by
  intro i j hij
  apply hX i j (ne_of_lt hij)
  revert hij
  fin_cases i <;> fin_cases j <;> decide

private theorem suppM_neg_wAl_levi_lv_of_apply_eq_zero_of_lt {k : Type} [Field k] (X : M4 k) (hX : ∀ i j : Fin 4, i < j → X i j = 0) :
    SuppM {-wAl} (UpperTheory.V.Ws.Chain.Levi.lv X) := by
  intro i j hij hw
  rw [UpperTheory.V.Ws.Chain.Levi.lv_apply]
  split_ifs with h
  · rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact hX i j hlt
    · exfalso
      revert hgt hw h
      fin_cases i <;> fin_cases j <;> decide
  · rfl

private theorem levi_lv_smul_one {k : Type} [Field k] (c : k) :
    UpperTheory.V.Ws.Chain.Levi.lv (c • (1 : M4 k)) = c • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [UpperTheory.V.Ws.Chain.Levi.lv_apply]

private theorem isUp_levi_lv_of_isUp {k : Type} [Field k] (X : M4 k) (hX : IsUp X) :
    IsUp (UpperTheory.V.Ws.Chain.Levi.lv X) := by
  intro i j h
  rw [UpperTheory.V.Ws.Chain.Levi.lv_apply]
  split_ifs
  · exact hX i j h
  · rfl

private theorem levi_lv_adj_mul_mul_of_par {k : Type} [Field k] (A B : M4 k) (hA : UpperTheory.V.Ws.Chain.Levi.Par A)
    (hB : UpperTheory.V.Ws.Chain.Levi.Par B) :
    UpperTheory.V.Ws.Chain.Levi.lv (adj A * B * A) =
      adj (UpperTheory.V.Ws.Chain.Levi.lv A) * UpperTheory.V.Ws.Chain.Levi.lv B * UpperTheory.V.Ws.Chain.Levi.lv A := by
  rw [levi_lv_mul_of_par _ _ (levi_par_mul _ _ (levi_par_adj _ hA) hB) hA, levi_lv_mul_of_par _ _ (levi_par_adj _ hA) hB, levi_lemma]

private theorem isGSp_levi_lv_of_par {k : Type} [Field k] (X : M4 k) (hX : UpperTheory.V.Ws.Chain.Levi.Par X)
    (ν : k) (h : IsGSp ν X) : IsGSp ν (UpperTheory.V.Ws.Chain.Levi.lv X) := by
  unfold IsGSp at h ⊢
  rw [levi_lemma, ← levi_lv_mul_of_par _ _ (levi_par_adj _ hX) hX, h, levi_lv_smul_one]

open UpperTheory.V.Ws.Chain.Levi in
theorem UpperTheory.V.Ws.Chain.levi :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] (Φ : Fr O Γ) {k : Type} [Field k] (a : O →+* k),
      (∀ v, ∀ s ∈ Φ.Mu v, s ∈ Φ.Gv v) → ∀ c : PD Φ.ι Γ k, Φ.IsRes a c → Supp nM c.r →
      ∃ c' : PD Φ.ι Γ k, Φ.IsRes a c' ∧ Supp {-wAl} c'.r ∧ (∀ v, SuppM {-wAl} (c'.n v)) ∧ c'.SameAl c := by
  intro O Γ _ _ _ Φ k _ a _ c hc hr
  have hL : ∀ g, ∀ i j : Fin 4, i < j → c.r g i j = 0 := fun g => levi_lemma_6 _ (hr g)
  have hP : ∀ g, Levi.Par (c.r g) := fun g => levi_par_of_apply_eq_zero_of_lt _ (hL g)
  have hNL : ∀ v, ∀ i j : Fin 4, i < j → c.n v i j = 0 := fun v => (hc.pair.low v).2.2
  have hN : ∀ v, Levi.Par (c.n v) := fun v => levi_par_of_apply_eq_zero_of_lt _ (hNL v)
  let r' : Γ →* M4 k :=
    { toFun := fun g => lv (c.r g)
      map_one' := by
        simp only [map_one]
        simpa using levi_lv_smul_one (1 : k)
      map_mul' := fun x y => by
        simp only [map_mul]
        exact levi_lv_mul_of_par _ _ (hP x) (hP y) }
  have hr' : ∀ g, r' g = lv (c.r g) := fun g => rfl
  have hψ : ∀ v i s, (PD.mk r' (fun v => lv (c.n v))).ψ v i s = c.ψ v i s := by
    intro v i s
    show (adj (lv (c.n v)) * r' s * lv (c.n v)) i i = (adj (c.n v) * c.r s * c.n v) i i
    rw [hr', ← levi_lv_adj_mul_mul_of_par _ _ (hN v) (hP s), lv_diag]
  refine ⟨PD.mk r' (fun v => lv (c.n v)), ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_⟩, ?_, ?_, ?_⟩
  · intro g
    exact isGSp_levi_lv_of_par _ (hP g) _ (hc.pair.mult g)
  · intro g hg
    show lv (c.r g) = 1
    rw [hc.pair.kill g hg]
    simpa using levi_lv_smul_one (1 : k)
  · intro i j hij
    show lv (c.r Φ.g0) i j = 0
    rw [lv_apply]
    split_ifs
    · exact hc.pair.nrm hij
    · rfl
  · intro v
    refine ⟨isGSp_levi_lv_of_par _ (hN v) _ (hc.pair.low v).1, fun i => ?_, fun i j hij => ?_⟩
    · show lv (c.n v) i i = 1
      rw [lv_diag]
      exact (hc.pair.low v).2.1 i
    · show lv (c.n v) i j = 0
      rw [lv_apply]
      split_ifs
      · exact hNL v i j hij
      · rfl
  · intro v s hs
    show IsUp (adj (lv (c.n v)) * r' s * lv (c.n v))
    rw [hr', ← levi_lv_adj_mul_mul_of_par _ _ (hN v) (hP s)]
    exact isUp_levi_lv_of_isUp _ (hc.pair.flag v s hs)
  · intro v s hs i
    rw [hψ]
    exact hc.pair.mu v s hs i
  · intro g i
    show lv (c.r g) i i = _
    rw [lv_diag]
    exact hc.res.diag g i
  · intro v s hs i
    rw [hψ]
    exact hc.res.char v s hs i
  · right
    intro g
    show SuppM nM (lv (c.r g))
    intro i j hij hw
    exact suppM_neg_wAl_levi_lv_of_apply_eq_zero_of_lt _ (hL g) i j hij (by
      intro hm
      apply hw
      rw [Finset.mem_singleton] at hm
      rw [hm]
      decide)
  · intro i j
    show AdicCont ⊥ (fun g => lv (c.r g) i j)
    simp only [lv_apply]
    split_ifs
    · exact hc.cont i j
    · intro N
      exact IsLocallyConstant.const _
  · intro g
    exact suppM_neg_wAl_levi_lv_of_apply_eq_zero_of_lt _ (hL g)
  · intro v
    exact suppM_neg_wAl_levi_lv_of_apply_eq_zero_of_lt _ (hNL v)
  · refine ⟨fun g => ?_, fun v => ?_⟩
    · show c.r g 1 0 = lv (c.r g) 1 0
      rw [lv_apply, if_pos (by decide)]
    · show c.n v 1 0 = lv (c.n v) 1 0
      rw [lv_apply, if_pos (by decide)]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidualChains.MovePs
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private def UpperTheory.V.Ws.Chain.uu {k : Type} [CommRing k] (y : k) : M4 k := !![1, 0, 0, 0; 0, 1, 0, 0; y, 0, 1, 0; 0, y, 0, 1]

private theorem adj_mul_M4 {k : Type} [Field k] (A B : M4 k) : adj (A * B) = adj B * adj A := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj, sgn, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

private theorem adj_uu_mul_diag_mul_uu_eq_of_diag_pairs {k : Type} [Field k] (z : k) (D : M4 k) (hD : ∀ i j : Fin 4, i ≠ j → D i j = 0)
    (h02 : D 0 0 = D 2 2) (h13 : D 1 1 = D 3 3) :
    adj (UpperTheory.V.Ws.Chain.uu z) * D * UpperTheory.V.Ws.Chain.uu z = D := by
  have e01 := hD 0 1 (by decide)
  have e02 := hD 0 2 (by decide)
  have e03 := hD 0 3 (by decide)
  have e10 := hD 1 0 (by decide)
  have e12 := hD 1 2 (by decide)
  have e13 := hD 1 3 (by decide)
  have e20 := hD 2 0 (by decide)
  have e21 := hD 2 1 (by decide)
  have e23 := hD 2 3 (by decide)
  have e30 := hD 3 0 (by decide)
  have e31 := hD 3 1 (by decide)
  have e32 := hD 3 2 (by decide)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [adj, sgn, UpperTheory.V.Ws.Chain.uu, Matrix.mul_apply, Fin.sum_univ_four,
      e01, e02, e03, e10, e12, e13, e20, e21, e23, e30, e31, e32]
  all_goals (simp only [h02, h13]; ring)

private theorem adj_uu_mul_uu_eq_one {k : Type} [Field k] (z : k) :
    adj (UpperTheory.V.Ws.Chain.uu z) * UpperTheory.V.Ws.Chain.uu z = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj, sgn, UpperTheory.V.Ws.Chain.uu, Matrix.mul_apply, Fin.sum_univ_four]

private theorem mul_lowerTriangular_M4 {k : Type} [Field k] (A B : M4 k) (hA : ∀ i j : Fin 4, i < j → A i j = 0)
    (hB : ∀ i j : Fin 4, i < j → B i j = 0) : ∀ i j : Fin 4, i < j → (A * B) i j = 0 := by
  intro i j h
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro l _
  rcases lt_or_ge i l with h1 | h1
  · rw [hA i l h1, zero_mul]
  · rw [hB l j (lt_of_le_of_lt h1 h), mul_zero]

private theorem adj_lowerTriangular_M4 {k : Type} [Field k] (A : M4 k) (hA : ∀ i j : Fin 4, i < j → A i j = 0) :
    ∀ i j : Fin 4, i < j → adj A i j = 0 := by
  intro i j h
  simp only [adj, Matrix.of_apply]
  rw [hA j.rev i.rev (Fin.rev_lt_rev.2 h), smul_zero]

private theorem lowerTriangular_of_suppM_neg_wAl {k : Type} [Field k] (X : M4 k) (hX : SuppM {-wAl} X) :
    ∀ i j : Fin 4, i < j → X i j = 0 := by
  intro i j h
  apply hX i j (ne_of_lt h)
  revert h
  fin_cases i <;> fin_cases j <;> decide

private theorem mul_uu_eq_explicit_of_suppM_neg_wAl_unit_diag {k : Type} [Field k] (X : M4 k) (z : k) (hX : SuppM {-wAl} X)
    (hd : ∀ i, X i i = 1) :
    X * UpperTheory.V.Ws.Chain.uu z = !![1, 0, 0, 0; X 1 0, 1, 0, 0; z, 0, 1, 0; X 3 2 * z, z, X 3 2, 1] := by
  have hL := lowerTriangular_of_suppM_neg_wAl X hX
  have e01 := hL 0 1 (by decide)
  have e02 := hL 0 2 (by decide)
  have e03 := hL 0 3 (by decide)
  have e12 := hL 1 2 (by decide)
  have e13 := hL 1 3 (by decide)
  have e23 := hL 2 3 (by decide)
  have e20 := hX 2 0 (by decide) (by decide)
  have e21 := hX 2 1 (by decide) (by decide)
  have e30 := hX 3 0 (by decide) (by decide)
  have e31 := hX 3 1 (by decide) (by decide)
  have d0 := hd 0
  have d1 := hd 1
  have d2 := hd 2
  have d3 := hd 3
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [UpperTheory.V.Ws.Chain.uu, Matrix.mul_apply, Fin.sum_univ_four,
      e01, e02, e03, e12, e13, e23, e20, e21, e30, e31, d0, d1, d2, d3]

theorem UpperTheory.V.Ws.Chain.movePs :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] (Φ : Fr O Γ) {k : Type} [Field k] (a : O →+* k),
      (∀ i g, Φ.χ i g * Φ.χ i.rev g = Φ.ν g) → (∀ v, ∀ s ∈ Φ.Mu v, s ∈ Φ.Gv v) → (∀ v, ∀ s ∈ Φ.Gv v, a (Φ.rt wPs s) = 1) →
      ∀ c : PD Φ.ι Γ k, Φ.IsRes a c → Supp {-wAl} c.r → (∀ v, SuppM {-wAl} (c.n v)) → ∀ y : Φ.ι → k,
      ∃ c' : PD Φ.ι Γ k, Φ.IsRes a c' ∧ c'.r = c.r ∧ ∀ v, SuppM qQ (c'.n v) ∧ c'.n v 1 0 = c.n v 1 0 ∧ c'.n v 2 0 = y v := by
  intro O Γ _ _ _ Φ k _ a hrev hMu hrt c hc hr hn y
  have hnL : ∀ v, ∀ i j : Fin 4, i < j → c.n v i j = 0 := fun v => lowerTriangular_of_suppM_neg_wAl _ (hn v)
  have hrL : ∀ g, ∀ i j : Fin 4, i < j → c.r g i j = 0 := fun g => lowerTriangular_of_suppM_neg_wAl _ (hr g)
  have hnd : ∀ v i, c.n v i i = 1 := fun v => (hc.pair.low v).2.1
  have hform : ∀ v, c.n v * UpperTheory.V.Ws.Chain.uu (y v) =
      !![1, 0, 0, 0; c.n v 1 0, 1, 0, 0; y v, 0, 1, 0; c.n v 3 2 * y v, y v, c.n v 3 2, 1] :=
    fun v => mul_uu_eq_explicit_of_suppM_neg_wAl_unit_diag _ _ (hn v) (hnd v)
  have hkey : ∀ v, ∀ s ∈ Φ.Gv v,
      adj (c.n v * UpperTheory.V.Ws.Chain.uu (y v)) * c.r s * (c.n v * UpperTheory.V.Ws.Chain.uu (y v)) =
        adj (c.n v) * c.r s * c.n v := by
    intro v s hs
    have hM : adj (c.n v * UpperTheory.V.Ws.Chain.uu (y v)) * c.r s * (c.n v * UpperTheory.V.Ws.Chain.uu (y v)) =
        adj (UpperTheory.V.Ws.Chain.uu (y v)) * (adj (c.n v) * c.r s * c.n v) * UpperTheory.V.Ws.Chain.uu (y v) := by
      rw [adj_mul_M4]
      simp only [mul_assoc]
    rw [hM]
    have hLM := mul_lowerTriangular_M4 _ _ (mul_lowerTriangular_M4 _ _ (adj_lowerTriangular_M4 _ (hnL v)) (hrL s)) (hnL v)
    have hUp := hc.pair.flag v s hs
    have hch : ∀ i, (adj (c.n v) * c.r s * c.n v) i i = a ↑(Φ.χ i s) := fun i => hc.res.char v s hs i
    have h2ne : a ↑(Φ.χ 2 s) ≠ 0 := ((Φ.χ 2 s).isUnit.map a).ne_zero
    have h02 : a ↑(Φ.χ 0 s) = a ↑(Φ.χ 2 s) := by
      have h := hrt v s hs
      simp [Fr.rt, wPs] at h
      exact (mul_inv_eq_one₀ h2ne).1 h
    have h13 : a ↑(Φ.χ 1 s) = a ↑(Φ.χ 3 s) := by
      have e0 := congrArg (fun u : Oˣ => a ↑u) (hrev 0 s)
      have e1 := congrArg (fun u : Oˣ => a ↑u) (hrev 1 s)
      simp only [Units.val_mul, map_mul] at e0 e1
      have r0 : (0 : Fin 4).rev = 3 := rfl
      have r1 : (1 : Fin 4).rev = 2 := rfl
      rw [r0] at e0
      rw [r1] at e1
      rw [h02] at e0
      have e : a ↑(Φ.χ 2 s) * a ↑(Φ.χ 3 s) = a ↑(Φ.χ 2 s) * a ↑(Φ.χ 1 s) := by
        rw [e0, ← e1]
        ring
      exact (mul_left_cancel₀ h2ne e).symm
    apply adj_uu_mul_diag_mul_uu_eq_of_diag_pairs
    · intro i j hij
      rcases lt_or_gt_of_ne hij with h | h
      · exact hLM i j h
      · exact hUp i j h
    · rw [hch, hch, h02]
    · rw [hch, hch, h13]
  refine ⟨PD.mk c.r (fun v => c.n v * UpperTheory.V.Ws.Chain.uu (y v)), ⟨⟨hc.pair.mult, hc.pair.kill, hc.pair.nrm,
    ?_, ?_, ?_⟩, ⟨hc.res.diag, ?_, ?_⟩, hc.cont⟩, rfl, ?_⟩
  · intro v
    refine ⟨?_, ?_, ?_⟩
    · show adj (c.n v * UpperTheory.V.Ws.Chain.uu (y v)) * (c.n v * UpperTheory.V.Ws.Chain.uu (y v)) = (1 : k) • 1
      rw [adj_mul_M4]
      have hg : adj (c.n v) * c.n v = (1 : k) • 1 := (hc.pair.low v).1
      rw [one_smul] at hg ⊢
      rw [show adj (UpperTheory.V.Ws.Chain.uu (y v)) * adj (c.n v) * (c.n v * UpperTheory.V.Ws.Chain.uu (y v)) =
          adj (UpperTheory.V.Ws.Chain.uu (y v)) * (adj (c.n v) * c.n v) * UpperTheory.V.Ws.Chain.uu (y v) by
        simp only [mul_assoc], hg, mul_one, adj_uu_mul_uu_eq_one]
    · intro i
      show (c.n v * UpperTheory.V.Ws.Chain.uu (y v)) i i = 1
      rw [hform v]
      fin_cases i <;> rfl
    · intro i j hij
      show (c.n v * UpperTheory.V.Ws.Chain.uu (y v)) i j = 0
      rw [hform v]
      revert hij
      fin_cases i <;> fin_cases j <;> intro hij <;> first | rfl | exact absurd hij (by decide)
  · intro v s hs
    show IsUp (adj (c.n v * UpperTheory.V.Ws.Chain.uu (y v)) * c.r s * (c.n v * UpperTheory.V.Ws.Chain.uu (y v)))
    rw [hkey v s hs]
    exact hc.pair.flag v s hs
  · intro v s hs i
    show (adj (c.n v * UpperTheory.V.Ws.Chain.uu (y v)) * c.r s * (c.n v * UpperTheory.V.Ws.Chain.uu (y v))) i i = 1
    rw [hkey v s (hMu v s hs)]
    exact hc.pair.mu v s hs i
  · intro v s hs i
    show (adj (c.n v * UpperTheory.V.Ws.Chain.uu (y v)) * c.r s * (c.n v * UpperTheory.V.Ws.Chain.uu (y v))) i i = _
    rw [hkey v s hs]
    exact hc.res.char v s hs i
  · right
    intro g i j hij hw
    apply hr g i j hij
    intro hm
    apply hw
    rw [Finset.mem_singleton] at hm
    rw [hm]
    decide
  · intro v
    refine ⟨?_, ?_, ?_⟩
    · show SuppM qQ (c.n v * UpperTheory.V.Ws.Chain.uu (y v))
      rw [hform v]
      intro i j hij hw
      revert hij hw
      fin_cases i <;> fin_cases j <;> intro hij hw <;>
        first | rfl | exact absurd rfl hij | exact absurd (by decide) hw
    · show (c.n v * UpperTheory.V.Ws.Chain.uu (y v)) 1 0 = c.n v 1 0
      rw [hform v]
      rfl
    · show (c.n v * UpperTheory.V.Ws.Chain.uu (y v)) 2 0 = y v
      rw [hform v]
      rfl
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem supp_mono {R : Type} [CommRing R] {S S' : Finset (ℤ × ℤ)} (h : S ⊆ S') {X : M4 R} (hX : SuppM S X) :
    SuppM S' X := fun i j hij hw => hX i j hij fun hs => hw (h hs)

theorem UpperTheory.V.Ws.chain2 :
    CohomologyHyp → SeedII → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T₀ : Tower D), Ctx2 D → T₀.Ok → T₀.Two → TameL l T₀.F → ∀ (ι : PadicAlgCl l ≃+* ℂ) (𝔞 : Amb l) (c₀ : PD Unit (G ℚ Ω) 𝔞.k), LatShape D T₀.pr (resQ T₀.F T₀.g0) (𝔞.red c) c₀ →
      ∃ T₁ : Tower D, T₀.Le T₁ ∧ TameL l T₁.F ∧ ∀ T : Tower D, T₁.Le T → T.Deep →
        ∃ (c₁ : Coef l) (h : c.O ≤ c₁.O) (Q : PD T.ι (G T.F Ω) c₁.O), T.SeedPair ι h Q ∧
          ∀ c₀' : PD T.ι (G T.F Ω) 𝔞.k, T.OverQ c₀ c₀' → (T.fr ∅).IsRes (𝔞.red c) c₀' → (T.fr ∅).Chain (𝔞.red c) c₀' (Q.map (𝔞.red c₁)) := by
  intro hP hS Ω _ _ _ l _ c D T₀ hC hO hT hL ι 𝔞 c₀ hc₀
  have hG : D.Good := hC.1
  have hF : T₀.Fit := ⟨hO, Or.inl ⟨hC, hT⟩⟩
  have ha : ∀ x ∈ maximalIdeal c.O, 𝔞.red c x = 0 := fun x hx =>
    (residue_eq_zero_iff _).2 (map_nonunit (𝔞.a c) x hx)
  have hrt := (Chain.rtFacts D hG T₀ hO _ _ ha).1
  obtain ⟨s₀, hs₀, ho₀⟩ := Chain.exists_residual_datum_over_restriction_to_rationals hP D T₀ hF _ _ ha c₀ hc₀.res ⟨hc₀.supp, fun _ => hc₀.flag⟩
  have hq₀ := goodQ D hG T₀ hF _ _ ha _ c₀ s₀ hc₀ hrt ho₀ hs₀
  obtain ⟨W, s, -, -, hW, hs, -, hsQ, -, hsP, -, -, hsA⟩ :=
    gysinAl hP D T₀ hF _ _ ha ∅ (by simp) s₀ s₀ hs₀ hs₀ (hq₀ ∅).2.1 (hq₀ ∅).2.1
  obtain ⟨T₁, h01, hL1, hD⟩ := diesEx D hG T₀ hL hO W hW
  refine ⟨T₁, h01, hL1, fun T h1 hdeep => ?_⟩
  have h0 : T₀.Le T := (leFit D hG T₀ T₁ h01).2.2.2.2.2.2 T h1
  obtain ⟨lO, lT, -, -, lF, -⟩ := leFit D hG T₀ T h0
  have tO := lO hO
  have tT := lT hT
  have tF := lF hF
  have hDT : ∀ w ∈ W, Dies l w T.F := fun w hw θ h1' h2 =>
    (IntermediateField.fixingSubgroup_antitone h1.le).trans (hD w hw θ h1' h2)
  obtain ⟨c₁, h, Q, hQ, hQV, hQE⟩ := hS Ω l c D T hC tO tT hdeep ι
  refine ⟨c₁, h, Q, hQ, fun c₀' ho hr => ?_⟩
  obtain ⟨sR, sV, sE⟩ := Chain.seedRes D T ι 𝔞 h Q hQ
  have sV := sV hQV
  obtain ⟨c₃, r₃, o₃⟩ := restrT D hG T₀ T h0 hF _ _ ha W hW hDT s hs (Or.inr (Or.inl hsQ.1))
  obtain ⟨t, rt, ot⟩ := restrT D hG T₀ T h0 hF _ _ ha W hW hDT s₀ (hq₀ W).1 (Or.inr (Or.inr hs₀))
  have hsP' : s.In nP := ⟨fun g => supp_mono (by decide) (hsQ.1 g), hsQ.2⟩
  have hsM : Supp nM s.r := fun g => supp_mono (by decide) (hsQ.1 g)
  obtain ⟨-, f2, f3, f4, -, -, f7, -⟩ := overFacts D hG T₀ T h0 hF _ _ ha W ∅ s s₀ c₃ t hs (hq₀ W).1 r₃ rt o₃ ot
  obtain ⟨-, -, -, -, -, -, -, g8⟩ := overFacts D hG T₀ T h0 hF _ _ ha W ∅ s₀ s t c₃ (hq₀ W).1 hs rt r₃ ot o₃
  obtain rfl : c₀' = t := g8 c₀ _ hc₀.res.pair ho₀ c₀' hr ho
  have q₃ : Supp qQ c₃.r := f2 _ hsQ.1
  have i₃ : c₃.In nP := f3 hsP'
  have m₃ : Supp nM c₃.r := f2 _ hsM
  have p₃ : c₃.SamePs c₀' := f4 hsP' (hq₀ W).2.1 hsP
  have a₃ : Ent c₃.r (-wAl) := (f7 hsM).1 hsA
  obtain ⟨-, i₀, g₀⟩ := goodQ D hG T tF _ _ ha (resQ T₀.F T₀.g0) c₀ c₀' (h0.pr ▸ hc₀) (h0.pr ▸ hrt) ho hr ∅
  have ok : (T.fr ∅).Ok (𝔞.red c) := (std hP D T tF ∅ c le_rfl).2 _ _ ha
  have hmu : ∀ v, ∀ s ∈ (T.fr ∅).Mu v, s ∈ (T.fr ∅).Gv v := fun v s hs => hs.1
  have hrb := (Chain.rtFacts D hG T tO _ _ ha).2
  obtain ⟨c₄', r₄', u₄', n₄', e₄'⟩ := Chain.levi (T.fr ∅) _ hmu c₃ r₃ m₃
  obtain ⟨c₄, r₄, e₄, n₄⟩ := Chain.movePs (T.fr ∅) _ ok.mul hmu
    (fun v s hs => (hrb _ _).2 (tT.atL _ (T.ovl v) s hs)) c₄' r₄' u₄' n₄' fun v => (Q.map (𝔞.red c₁)).n v 2 0
  have u₄ : Supp {-wAl} c₄.r := e₄ ▸ u₄'
  have m₄ : Supp nM c₄.r := fun g => supp_mono (by decide) (u₄ g)
  have v₄ : Supp vV c₄.r := fun g => supp_mono (by decide) (u₄ g)
  have al : c₃.SameAl c₄ := ⟨fun g => by rw [e₄, e₄'.1], fun v => ((n₄ v).2.1.trans (e₄'.2 v)).symm⟩
  have a₄ : Ent c₄.r (-wAl) := by
    obtain ⟨g, hg⟩ := ((Chain.entIff (T.fr ∅) (𝔞.red c) c₃ r₃).2 m₃).1 a₃
    exact ((Chain.entIff (T.fr ∅) (𝔞.red c) c₄ r₄).2 m₄).2 ⟨g, al.1 g ▸ hg⟩
  have G₀ : (T.fr ∅).Good (𝔞.red c) c₀' := g₀.elim (fun x => Or.inl ⟨x.1, Or.inl x.2⟩) fun x => Or.inr (Or.inr (Or.inl x))
  have G₃ : (T.fr ∅).Good (𝔞.red c) c₃ := by
    by_cases hp : Ent c₃.r (-wPs)
    · exact Or.inl ⟨hp, Or.inr a₃⟩
    rcases g₀ with x | x
    · obtain ⟨g, hg⟩ := ((Chain.entIff (T.fr ∅) (𝔞.red c) c₀' hr).1 i₀.1).1 x.1
      exact absurd (((Chain.entIff (T.fr ∅) (𝔞.red c) c₃ r₃).1 i₃.1).2 ⟨g, p₃.1 g ▸ hg⟩) hp
    refine Or.inr (Or.inr (Or.inl ⟨⟨fun g i j hij hw => ?_, fun v => ⟨i₃.2 v, p₃.2 v ▸ (x.1.2 v).2⟩⟩, a₃⟩))
    by_cases hq : wt i j = -wPs
    · by_contra hne
      exact hp ⟨g, i, j, hq, hne⟩
    · exact q₃ g i j hij (by revert hw hq; revert i j; decide)
  have G₄ : (T.fr ∅).Good (𝔞.red c) c₄ :=
    Or.inr (Or.inr (Or.inl ⟨⟨v₄, fun v => ⟨(n₄ v).1, (n₄ v).2.2 ▸ (sV.2 v).2⟩⟩, a₄⟩))
  have Gs : (T.fr ∅).Good (𝔞.red c) (Q.map (𝔞.red c₁)) := by
    rcases hQE with x | x
    · exact Or.inr (Or.inr (Or.inl ⟨sV, sE _ x⟩))
    refine Or.inr (Or.inr (Or.inr ⟨sV, sE _ x.1, sE _ x.2, fun v => ?_⟩))
    obtain ⟨g, hg, hne⟩ := tT.bigL _ (T.ovl v)
    exact ⟨g, hg, fun h1 => hne (by rw [(hrb _ _).1 h1, one_pow])⟩
  have L₁ := lineP (T.fr ∅) _ ok c₀' c₃ hr r₃ i₀ i₃ ⟨fun g => (p₃.1 g).symm, fun v => (p₃.2 v).symm⟩
  have L₂ := lineM (T.fr ∅) _ ok c₃ c₄ r₃ r₄ m₃ m₄ al
  have L₃ := lineP (T.fr ∅) _ ok c₄ _ r₄ sR ⟨fun g => supp_mono (by decide) (v₄ g), fun v => (n₄ v).1⟩
    ⟨fun g => supp_mono (by decide) (sV.1 g), fun v => (sV.2 v).1⟩
    ⟨fun g => (v₄ g 2 0 (by decide) (by decide)).trans (sV.1 g 2 0 (by decide) (by decide)).symm, fun v => (n₄ v).2.2⟩
  exact ⟨G₀, ((Relation.ReflTransGen.single ⟨G₃, L₁⟩).tail ⟨G₄, L₂⟩).tail ⟨Gs, L₃⟩⟩
