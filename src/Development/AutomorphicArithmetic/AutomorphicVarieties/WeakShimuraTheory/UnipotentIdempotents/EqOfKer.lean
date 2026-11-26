module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.BarFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmHom

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.PlacesEq
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

private theorem nat_place {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {A : ValuationSubring Ω}
    {v : W.Plc F} (h : IsPlaceOver A v) (n : ℕ) : A.valuation (n : Ω) < 1 ↔ (n : 𝓞 F) ∈ v.asIdeal := by
  have key := h (n : 𝓞 F)
  simpa using key

open scoped Pointwise in
theorem UpperTheory.V.Ws.Lk.placesEq :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} (T : Tower D), ∃ e : W.Vl l T.L ≃ T.ι, ∀ v : W.Vl l T.L, IsPlaceOver (T.pl (e v)) v.1 := by
  intro Ω _ _ _ l _ c D T
  obtain ⟨hF, ⟨φ, hφ, -⟩, -⟩ := galEq T
  have hfix : ∀ (g : G T.F Ω) (y : W.Lp T.L), g (algebraMap (W.Lp T.L) Ω y) = algebraMap (W.Lp T.L) Ω y := by
    intro g y
    have hy := (hF (algebraMap (W.Lp T.L) Ω y)).2 ⟨y, rfl⟩
    exact g.commutes ⟨_, hy⟩
  have hmove : ∀ (g : G T.F Ω) {A B : ValuationSubring Ω}, (∀ x, g x ∈ B ↔ x ∈ A) →
      ∀ {v : W.Plc (W.Lp T.L)}, IsPlaceOver A v → IsPlaceOver B v := by
    intro g A B hg v h x
    have key := val_lt_one (σ := g.toRingEquiv) hg (algebraMap (W.Lp T.L) Ω x)
    have hx : g.toRingEquiv (algebraMap (W.Lp T.L) Ω x) = algebraMap (W.Lp T.L) Ω x := hfix g x
    rw [hx] at key
    rw [key]
    exact h x
  have hA : ∀ v : W.Vl l T.L, ∃ A : ValuationSubring Ω, IsPlaceOver A v.1 := fun v => exists_isPlaceOver Ω v.1
  choose A hAv using hA
  have hAl : ∀ v, (A v).valuation (l : Ω) < 1 := fun v => (nat_place (hAv v) l).2 v.2
  choose e he using fun v => (T.cover (A v) (hAl v)).exists
  have hover : ∀ v, IsPlaceOver (T.pl (e v)) v.1 := by
    intro v
    obtain ⟨g, hg⟩ := he v
    refine hmove g⁻¹ ?_ (hAv v)
    intro x
    rw [← hg]
    simp
  refine ⟨Equiv.ofBijective e ⟨?_, ?_⟩, hover⟩
  · intro v v' hvv
    apply Subtype.ext
    have h1 := hover v
    have h2 := hover v'
    rw [hvv] at h1
    exact eq_of_isPlaceOver h1 h2
  · intro w
    have hne : T.pl w ≠ ⊤ := by
      intro htop
      exact ((places (W.Lp T.L) Ω l (T.pl w)).2.1 htop).2 (T.ovl w)
    obtain ⟨v0, hv0⟩ := (places (W.Lp T.L) Ω l (T.pl w)).1 hne
    have hv0l : (l : 𝓞 (W.Lp T.L)) ∈ v0.asIdeal := (nat_place hv0 l).1 (T.ovl w)
    refine ⟨⟨v0, hv0l⟩, ?_⟩
    obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver hv0 (hAv ⟨v0, hv0l⟩)
    apply (T.cover (A ⟨v0, hv0l⟩) (hAl _)).unique (he _)
    refine ⟨φ σ, fun x => ?_⟩
    rw [hφ, ← hσ, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← AlgEquiv.smul_def, inv_smul_smul]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.GExRtZero
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

private theorem gEx_rt_wt {O Γ : Type} [CommRing O] [Group Γ] (Φ : Fr O Γ) (g : Γ)
    (h : Φ.χ 0 g * Φ.χ 3 g = Φ.χ 1 g * Φ.χ 2 g) (i j : Fin 4) : Φ.rt (wt i j) g * Φ.χ j g = Φ.χ i g := by
  have hd : Φ.χ 3 g = (Φ.χ 0 g)⁻¹ * (Φ.χ 1 g * Φ.χ 2 g) := eq_inv_mul_of_mul_eq h
  fin_cases i <;> fin_cases j <;> simp [Fr.rt, wt, lamW, muW, hd] <;>
    apply Additive.ofMul.injective <;> simp <;> abel

private theorem gEx_rt_add {O Γ : Type} [CommRing O] [Group Γ] (Φ : Fr O Γ) (g : Γ) (w w' : ℤ × ℤ) :
    Φ.rt (w + w') g = Φ.rt w g * Φ.rt w' g := by
  simp only [Fr.rt, MonoidHom.coe_mk, OneHom.coe_mk, Prod.fst_add, Prod.snd_add, zpow_add]
  exact mul_mul_mul_comm _ _ _ _

private theorem gEx_rt_zero {O Γ : Type} [CommRing O] [Group Γ] (Φ : Fr O Γ) (g : Γ) : Φ.rt 0 g = 1 := by
  simp [Fr.rt]

private theorem gEx_abs {O Γ Δ k : Type} [CommRing O] [Group Γ] [Group Δ] [Field k] [Finite k] (Φ : Fr O Γ)
    (h : ∀ g, Φ.χ 0 g * Φ.χ 3 g = Φ.χ 1 g * Φ.χ 2 g) (a : O →+* k) (φ : Δ →* Γ) (ω : Γ →* Oˣ)
    (hω : ∀ w, ∃ g, a (Φ.rt w (φ g)) ≠ a (ω (φ g))) :
    ∃ g, (∀ i j, a (Φ.χ i (φ g)) = a (Φ.χ j (φ g))) ∧ a (ω (φ g)) ≠ 1 := by
  classical
  let κ : Fin 4 → Δ →* kˣ := fun i => (Units.map a.toMonoidHom).comp ((Φ.χ i).comp φ)
  let ω' : Δ →* kˣ := (Units.map a.toMonoidHom).comp (ω.comp φ)
  have hmain : ω' ∉ Subgroup.closure (Set.range fun q : Fin 4 × Fin 4 => κ q.1 / κ q.2) := by
    intro hmem
    let S : Subgroup (Δ →* kˣ) :=
      { carrier := {ψ | ∃ w : ℤ × ℤ, ∀ g, ψ g = Units.map a.toMonoidHom (Φ.rt w (φ g))}
        mul_mem' := by
          rintro ψ₁ ψ₂ ⟨w₁, h₁⟩ ⟨w₂, h₂⟩
          exact ⟨w₁ + w₂, fun g => by simp [h₁, h₂, gEx_rt_add]⟩
        one_mem' := ⟨0, fun g => by simp [gEx_rt_zero]⟩
        inv_mem' := by
          rintro ψ ⟨w, hw⟩
          refine ⟨-w, fun g => ?_⟩
          have hinv : Φ.rt (-w) (φ g) = (Φ.rt w (φ g))⁻¹ := by
            rw [eq_inv_iff_mul_eq_one, ← gEx_rt_add]
            simp [gEx_rt_zero]
          simp [hw, hinv] }
    have hle : Subgroup.closure (Set.range fun q : Fin 4 × Fin 4 => κ q.1 / κ q.2) ≤ S := by
      rw [Subgroup.closure_le]
      rintro _ ⟨⟨p, q⟩, rfl⟩
      refine ⟨wt p q, fun g => ?_⟩
      have hpq := gEx_rt_wt Φ (φ g) (h _) p q
      simp only [κ, MonoidHom.div_apply, MonoidHom.comp_apply, ← hpq, map_mul]
      exact mul_div_cancel_right _ _
    obtain ⟨w, hw⟩ := hle hmem
    obtain ⟨g, hg⟩ := hω w
    apply hg
    have := congrArg Units.val (hw g)
    simpa [ω'] using this.symm
  obtain ⟨g, hg1, hg2⟩ := (Loc.v0e κ ω').2 hmain
  refine ⟨g, fun i j => ?_, ?_⟩
  · have := congrArg Units.val (hg1 i j)
    simpa [κ] using this
  · intro h1
    apply hg2
    ext
    simpa [ω'] using h1

theorem UpperTheory.V.Ws.Lk.gEx :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} (T : Tower D), T.Ok → ∃ g : G T.L Ω, (∀ i j, Raw.bar (chi D T.pr i) (resQ T.L g) = Raw.bar (chi D T.pr j) (resQ T.L g)) ∧ Raw.bar D.om (resQ T.L g) ≠ 1 := by
  intro Ω _ _ _ l _ c D T hT
  haveI := c.dvr
  haveI := c.fin
  haveI : Finite (ResidueField c.O) :=
    IsLocalRing.ResidueField.finite_of_finite (R := ℤ_[l]) inferInstance
  have hrel : ∀ x, (T.fr ∅).χ 0 x * (T.fr ∅).χ 3 x = (T.fr ∅).χ 1 x * (T.fr ∅).χ 2 x := by
    intro x
    simp only [Tower.fr, MonoidHom.coe_comp, Function.comp_apply, chi]
    cases T.pr <;> simp [lab, Raw.ps, Raw.th, mul_comm]
  have hω : ∀ w, ∃ g, residue c.O ((T.fr ∅).rt w (resLe T.F_le g) : c.O) ≠
      residue c.O ((D.om.comp (resQ T.F)) (resLe T.F_le g) : c.O) := by
    intro w
    obtain ⟨g, hgL, hg⟩ := hT.g2 w
    obtain ⟨g', rfl⟩ := ((galEq T).2.2 g).1 hgL
    exact ⟨g', hg⟩
  obtain ⟨g, hg1, hg2⟩ :=
    gEx_abs (T.fr ∅) hrel (residue c.O) (resLe T.F_le) (D.om.comp (resQ T.F)) hω
  exact ⟨g, fun i j => hg1 i j, hg2⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.CcOf
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

theorem UpperTheory.V.Ws.Lk.ccOf :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} (T : Tower D) (s : W.HidaSetting l T.L Ω), ∃ σ ∉ T.K.fixingSubgroup, ∀ g g' : G T.L Ω, W.resP T.L Ω g' = s.c * W.resP T.L Ω g * s.c⁻¹ → resQ T.L g' = σ * resQ T.L g * σ⁻¹ := by
  intro Ω _ _ _ l _ c D T s
  obtain ⟨j, hj⟩ := s.hc
  refine ⟨(s.c : Ω ≃ₐ[W.Lp T.L] Ω).restrictScalars ℚ, ?_, ?_⟩
  · intro hfix
    rw [IntermediateField.fixingSubgroup, mem_fixingSubgroup_iff] at hfix
    have hreal : NumberField.ComplexEmbedding.IsReal (j.comp (T.K.val : T.K →+* Ω)) := by
      rw [NumberField.ComplexEmbedding.isReal_iff]
      ext x
      rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
      have hx := hfix (x : Ω) x.2
      change s.c (x : Ω) = (x : Ω) at hx
      simp only [RingHom.comp_apply]
      rw [← hj]
      change j (s.c (x : Ω)) = j (x : Ω)
      rw [hx]
    exact NumberField.IsTotallyComplex.complexEmbedding_not_isReal _ hreal
  · intro g g' h
    ext x
    have hx := congrArg (fun f : G (W.Lp T.L) Ω => f x) h
    exact hx
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.EqOfMem
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

private theorem exists_conj (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] :
    ∃ c : G (W.Lp L) Ω, ∃ j : Ω →+* ℂ, ∀ x, j (c x) = starRingEnd ℂ (j x) := by
  obtain ⟨φ⟩ : Nonempty (L →+* ℂ) := inferInstance
  letI : Algebra L ℂ := φ.toAlgebra
  haveI : Algebra.IsAlgebraic L Ω := IsAlgClosure.isAlgebraic
  let j : Ω →ₐ[L] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  letI : Algebra Ω ℂ := (j : Ω →+* ℂ).toAlgebra
  haveI : IsScalarTower (W.Lp L) Ω ℂ := IsScalarTower.of_algebraMap_eq fun x => (j.commutes (x : L)).symm
  let s : ℂ →ₐ[W.Lp L] ℂ :=
    { starRingEnd ℂ with commutes' := fun x => (mem_maximalRealSubfield_iff (x : L)).1 x.2 φ }
  exact ⟨s.restrictNormal' Ω, j, fun x => s.restrictNormal_commutes Ω x⟩

private theorem ne_top {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] {A : ValuationSubring Ω}
    {v : W.Plc k} (h : IsPlaceOver A v) : A ≠ ⊤ := by
  rintro rfl
  refine v.ne_bot (eq_bot_iff.2 fun x hx => ?_)
  have h1 := (h x).2 hx
  rw [valuation_lt_one_iff'] at h1
  have h2 := h1.2.resolve_right fun h' => h' (ValuationSubring.mem_top _)
  simpa using h2

private theorem val_nat {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] {A : ValuationSubring Ω}
    {v : W.Plc k} (h : IsPlaceOver A v) (q : ℕ) : A.valuation (q : Ω) < 1 ↔ (q : 𝓞 k) ∈ v.asIdeal := by
  simpa using h (q : 𝓞 k)

private theorem fin_nat {k : Type} [Field k] [NumberField k] {q : ℕ} (hq : q ≠ 0) :
    {v : W.Plc k | (q : 𝓞 k) ∈ v.asIdeal}.Finite := by
  have h := Ideal.finite_factors (I := Ideal.span {(q : 𝓞 k)}) (by simpa using hq)
  simpa [Ideal.dvd_span_singleton] using h

private theorem eq_of_mem {k : Type} [Field k] [NumberField k] {v : W.Plc k} {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h1 : (p : 𝓞 k) ∈ v.asIdeal) (h2 : (q : 𝓞 k) ∈ v.asIdeal) : p = q := by
  by_contra hne
  obtain ⟨a, b, hab⟩ := Nat.Coprime.cast (R := 𝓞 k) ((Nat.coprime_primes hp hq).2 hne)
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (hab ▸ add_mem (v.asIdeal.mul_mem_left a h1) (v.asIdeal.mul_mem_left b h2)))

theorem UpperTheory.V.Ws.Lk.mkSet :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω], l ≠ 2 → (∀ A : ValuationSubring Ω, Ine (F := W.Lp L) A ≤ (W.resP L Ω).range) → ∀ S : Finset ℕ, (∀ q ∈ S, q.Prime) → l ∈ S → (∀ q ∈ S, ∀ A : ValuationSubring Ω, A.valuation (q : Ω) < 1 → Dec (F := W.Lp L) A ≤ (W.resP L Ω).range) → ∀ A₀ : W.Vl l L → ValuationSubring Ω, (∀ v, IsPlaceOver (A₀ v) v.1) → ∀ (v₀ : W.Plc (W.Lp L)) (B : ValuationSubring Ω) (p : ℕ), p.Prime → p ≠ 2 → p ∉ S → ¬ (p : ℤ) ∣ discr L → ((p : ℕ) : 𝓞 (W.Lp L)) ∈ v₀.asIdeal → normV v₀ = p → IsPlaceOver B v₀ → Dec (F := W.Lp L) B ≤ (W.resP L Ω).range → ∃ s : W.HidaSetting l L Ω, (∀ v : W.Vl l L, s.A v = A₀ v) ∧ s.A s.v0 = B ∧ s.S.Finite ∧ (∀ q ∈ S, ¬ B.valuation (q : Ω) < 1) ∧ ∀ (A : ValuationSubring Ω) (v : W.Plc (W.Lp L)), IsPlaceOver A v → v ∉ s.S → ∀ q ∈ S, ¬ A.valuation (q : Ω) < 1 := by
  classical
  intro l hl L Ω _ _ _ _ _ _ hodd hunr S hS hlS hsp A₀ hA₀ v₀ B p hp hp2 hpS hpd hpv hnv hB hBs
  have hq0 : ∀ q ∈ S, (q : 𝓞 (W.Lp L)) ∉ v₀.asIdeal := fun q hq h =>
    hpS (eq_of_mem hp (hS q hq) hpv h ▸ hq)
  obtain ⟨c, hc⟩ := exists_conj L Ω
  have hex : ∀ v : W.Plc (W.Lp L), ∃ A : ValuationSubring Ω, IsPlaceOver A v ∧
      (∀ h : (l : 𝓞 (W.Lp L)) ∈ v.asIdeal, A = A₀ ⟨v, h⟩) ∧ (v = v₀ → A = B) := by
    intro v
    by_cases h : (l : 𝓞 (W.Lp L)) ∈ v.asIdeal
    · exact ⟨A₀ ⟨v, h⟩, hA₀ ⟨v, h⟩, fun _ => rfl, fun e => absurd (e ▸ h) (hq0 l hlS)⟩
    · by_cases e : v = v₀
      · exact ⟨B, e ▸ hB, fun h' => absurd h' h, fun _ => rfl⟩
      · obtain ⟨A, hA⟩ := exists_isPlaceOver Ω v
        exact ⟨A, hA, fun h' => absurd h' h, fun e' => absurd e' e⟩
  choose A hA hAl hA0 using hex
  choose w hw using fun v => (places L Ω l (A v)).1 (ne_top (hA v))
  have hfin : {v : W.Plc (W.Lp L) | (∃ q ∈ S, (q : 𝓞 (W.Lp L)) ∈ v.asIdeal) ∧ (l : 𝓞 (W.Lp L)) ∉ v.asIdeal}.Finite :=
    (S.finite_toSet.biUnion fun q hq => fin_nat (k := W.Lp L) (hS q hq).ne_zero).subset fun v hv => by
      obtain ⟨⟨q, hq, h⟩, -⟩ := hv
      exact Set.mem_biUnion hq h
  refine ⟨{ odd := hodd, unr := fun B _ _ => hunr B, c := c, hc := hc, w := w, A := A, hw := hw, hA := hA,
            St := hfin.toFinset, St_l := fun u hu => (hfin.mem_toFinset.1 hu).2, v0 := v₀, v0_St := ?_, p := p,
            p_prime := hp, p_odd := hp2, p_ne := fun e => hpS (e ▸ hlS), p_unr := hpd, norm_v0_eq_one := hnv,
            split := ?_ }, fun v => hAl v.1 v.2, hA0 v₀ rfl, ?_, fun q hq h => hq0 q hq ((val_nat hB q).1 h), ?_⟩
  · intro h
    obtain ⟨⟨q, hq, h⟩, -⟩ := hfin.mem_toFinset.1 h
    exact hq0 q hq h
  · rintro v (h | h | rfl)
    · exact hsp l hlS _ ((val_nat (hA v) l).2 h)
    · obtain ⟨⟨q, hq, h⟩, -⟩ := hfin.mem_toFinset.1 h
      exact hsp q hq _ ((val_nat (hA v) q).2 h)
    · rw [hA0 v rfl]; exact hBs
  · exact (fin_nat hl.out.ne_zero).union ((Finset.finite_toSet _).union (Set.finite_singleton v₀))
  · intro A' v hv hvS q hq h
    refine hvS ?_
    by_cases h' : (l : 𝓞 (W.Lp L)) ∈ v.asIdeal
    · exact Or.inl h'
    · exact Or.inr (Or.inl (hfin.mem_toFinset.2 ⟨⟨q, hq, (val_nat hv q).1 h⟩, h'⟩))
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.RangeOpen
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

private theorem range_open (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] : IsOpen ((W.resP L Ω).range : Set (G (W.Lp L) Ω)) := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element (W.Lp L) L
  have hadj : Algebra.adjoin (W.Lp L) {α} = ⊤ :=
    (IntermediateField.adjoin_simple_eq_top_iff_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic α)).mp hα
  have hset : ((W.resP L Ω).range : Set (G (W.Lp L) Ω)) =
      {τ | τ (algebraMap L Ω α) = algebraMap L Ω α} := by
    ext τ
    constructor
    · rintro ⟨σ, rfl⟩
      exact σ.commutes α
    · intro hτ
      have hext : (τ.toAlgHom.comp (IsScalarTower.toAlgHom (W.Lp L) L Ω)) =
          IsScalarTower.toAlgHom (W.Lp L) L Ω := by
        refine AlgHom.ext_of_adjoin_eq_top hadj ?_
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst hx
        exact hτ
      have hfix : ∀ l : L, τ (algebraMap L Ω l) = algebraMap L Ω l := fun l =>
        DFunLike.congr_fun hext l
      refine ⟨{ τ with commutes' := hfix }, ?_⟩
      ext x
      rfl
  rw [hset]
  exact isOpen_setOf_apply (algebraMap L Ω α) (fun y => y = algebraMap L Ω α)

theorem UpperTheory.V.Ws.Lk.v0Ex :
    ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [CharZero Ω] [Algebra L Ω] [IsAlgClosure L Ω] (U : Subgroup (G L Ω)), IsOpen (U : Set (G L Ω)) → ∀ (g : G L Ω) (M : ℕ), M ≠ 0 → ∃ (v : W.Plc (W.Lp L)) (A : ValuationSubring Ω) (p : ℕ), p.Prime ∧ ¬ p ∣ M ∧ ((p : ℕ) : 𝓞 (W.Lp L)) ∈ v.asIdeal ∧ normV v = p ∧ IsPlaceOver A v ∧ Dec (F := W.Lp L) A ≤ (W.resP L Ω).range ∧ (∀ d ∈ Dec (F := L) A, ∃ n : ℤ, d⁻¹ * g ^ n ∈ U) ∧ ∃ d ∈ Dec (F := L) A, d⁻¹ * g ∈ U := by
  intro L Ω _ _ _ _ _ _ _ U hU g M hM
  have hinj : Function.Injective (W.resP L Ω) := fun a b h =>
    AlgEquiv.ext fun x => DFunLike.congr_fun h x
  have hemb := (W.continuous_resP (L := L) (Ω := Ω)).isClosedEmbedding hinj
  have himg : IsOpen ((W.resP L Ω) '' (U : Set (G L Ω))) := by
    obtain ⟨t, ht, hpre⟩ := hemb.isInducing.isOpen_iff.mp hU
    rw [← hpre, Set.image_preimage_eq_inter_range]
    refine ht.inter ?_
    rw [← MonoidHom.coe_range]
    exact range_open L Ω
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one himg
    ⟨1, U.one_mem, map_one _⟩
  obtain ⟨v, A, p, σ, -, hp, hpM, -, hpv, hnv, -, hAv, hIne, hfrob, hσg⟩ :=
    Loc.v00 (F := W.Lp L) (Ω := Ω) N.toSubgroup N.isOpen' (W.resP L Ω g) ∅ M hM
  have hback : ∀ x : G L Ω, W.resP L Ω x ∈ N.toSubgroup → x ∈ U := by
    intro x hx
    obtain ⟨u, hu, hux⟩ := hN hx
    rw [hinj hux] at hu
    exact hu
  have hdec : ∀ d : G L Ω, d ∈ Dec (F := L) A ↔ W.resP L Ω d ∈ Dec (F := W.Lp L) A := by
    intro d
    rw [mem_Dec, mem_Dec]
    exact Iff.rfl
  have hσH : σ ∈ Subgroup.zpowers (W.resP L Ω g) ⊔ N.toSubgroup := by
    have h1 : W.resP L Ω g ∈ Subgroup.zpowers (W.resP L Ω g) ⊔ N.toSubgroup :=
      Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    have h2 : σ⁻¹ * W.resP L Ω g ∈ Subgroup.zpowers (W.resP L Ω g) ⊔ N.toSubgroup :=
      Subgroup.mem_sup_right hσg
    have h3 := Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ h2)
    have h4 : W.resP L Ω g * (σ⁻¹ * W.resP L Ω g)⁻¹ = σ := by group
    rwa [h4] at h3
  have hHclosed : IsClosed ((Subgroup.zpowers (W.resP L Ω g) ⊔ N.toSubgroup :
      Subgroup (G (W.Lp L) Ω)) : Set (G (W.Lp L) Ω)) :=
    Subgroup.isClosed_of_isOpen _ (Subgroup.isOpen_mono le_sup_right N.isOpen')
  have hDecH : Dec (F := W.Lp L) A ≤ Subgroup.zpowers (W.resP L Ω g) ⊔ N.toSubgroup := by
    intro d hd
    have hfrob' : IsFrob A (normV v) σ := by
      rw [hnv]
      exact hfrob
    have hcl := GlobalTheory.TameQuot.closure_frob_sup_Ine (W.Lp L) Ω A v hAv ⟨σ, hfrob.1⟩ hfrob'
    have hle : (Subgroup.zpowers (⟨σ, hfrob.1⟩ : Dec (F := W.Lp L) A) ⊔
        (Ine A).subgroupOf (Dec (F := W.Lp L) A)) ≤
        (Subgroup.zpowers (W.resP L Ω g) ⊔ N.toSubgroup).subgroupOf (Dec (F := W.Lp L) A) := by
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le, Subgroup.mem_subgroupOf]
        exact hσH
      · intro x hx
        rw [Subgroup.mem_subgroupOf] at hx ⊢
        exact Subgroup.mem_sup_right (hIne hx)
    have hclosed : IsClosed (((Subgroup.zpowers (W.resP L Ω g) ⊔ N.toSubgroup).subgroupOf
        (Dec (F := W.Lp L) A) : Subgroup (Dec (F := W.Lp L) A)) : Set (Dec (F := W.Lp L) A)) :=
      hHclosed.preimage continuous_subtype_val
    have hmin := Subgroup.topologicalClosure_minimal _ hle hclosed
    rw [hcl] at hmin
    exact Subgroup.mem_subgroupOf.mp (hmin (Subgroup.mem_top (⟨d, hd⟩ : Dec (F := W.Lp L) A)))
  have hHrange : Subgroup.zpowers (W.resP L Ω g) ⊔ N.toSubgroup ≤ (W.resP L Ω).range := by
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact ⟨g, rfl⟩
    · intro x hx
      obtain ⟨u, -, hu⟩ := hN hx
      exact ⟨u, hu⟩
  obtain ⟨d0, hd0⟩ := hHrange hσH
  refine ⟨v, A, p, hp, hpM, hpv, hnv, hAv, hDecH.trans hHrange, ?_, d0, ?_, ?_⟩
  · intro d hd
    obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_right.mp (hDecH ((hdec d).mp hd))
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    refine ⟨n, hback _ ?_⟩
    rw [map_mul, map_inv, map_zpow, ← hyz]
    have h5 : (W.resP L Ω g ^ n * z)⁻¹ * W.resP L Ω g ^ n = z⁻¹ := by group
    rw [h5]
    exact N.toSubgroup.inv_mem hz
  · rw [hdec, hd0]
    exact hfrob.1
  · apply hback
    rw [map_mul, map_inv, hd0]
    exact hσg
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

private noncomputable def bu {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    (L : IntermediateField ℚ Ω) (γ : G ℚ Ω →* c.Oˣ) : G L Ω →* (ResidueField c.O)ˣ :=
  ((Units.map (residue c.O).toMonoidHom).comp γ).comp (resQ L)

private theorem bu_val {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    (L : IntermediateField ℚ Ω) (γ : G ℚ Ω →* c.Oˣ) (g : G L Ω) :
    (bu L γ g : ResidueField c.O) = Raw.bar γ (resQ L g) := rfl

private theorem bu_open {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    (L : IntermediateField ℚ Ω) [NumberField L] (γ : G ℚ Ω →* c.Oˣ) (h : IsOpen {g : G ℚ Ω | Raw.bar γ g = 1}) :
    IsOpen ((bu L γ).ker : Set (G L Ω)) := by
  have hk : ((bu L γ).ker : Set (G L Ω)) = resQ L ⁻¹' {g | Raw.bar γ g = 1} := by
    ext g
    simp [MonoidHom.mem_ker, Units.ext_iff, bu_val]
  rw [hk]
  exact h.preimage (Af.continuous_restrictScalarsHom ℚ L Ω)

private theorem eq_of_ker {Γ Δ : Type} [Group Γ] [Group Δ] {f : Γ →* Δ} {a b : Γ} (h : a⁻¹ * b ∈ f.ker) : f a = f b := by
  rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at h
  exact h

private theorem dec_of {Ω F F' : Type} [Field Ω] [Field F] [Field F'] [NumberField F] [NumberField F'] [Algebra F Ω] [Algebra F' Ω] {A : ValuationSubring Ω}
    {σ : G F Ω} {τ : G F' Ω} (h : ∀ x, τ x = σ x) (hσ : σ ∈ Dec (F := F) A) : τ ∈ Dec (F := F') A := by
  have h2 := apply_mem_iff_of_mem_Dec hσ
  rw [mem_Dec]
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, ← h2 (τ⁻¹ x), ← h]
  simp

theorem UpperTheory.V.Ws.Lk.setEx :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} (T : Tower D), D.Good → T.Ok → Nonempty (SetD T) := by
  intro Ω _ _ _ l _ c D T hG hT
  classical
  obtain ⟨hps, hom, -⟩ := barFacts hG
  obtain ⟨g0, hg0eq, hg0om⟩ := gEx T hT
  let U : Subgroup (G T.L Ω) := (bu T.L (D.ps 0)).ker ⊓ (bu T.L (D.ps 1)).ker ⊓
    (bu T.L (D.ps 2)).ker ⊓ (bu T.L (D.ps 3)).ker ⊓ (bu T.L D.om).ker
  have hU : IsOpen (U : Set (G T.L Ω)) := by
    simp only [U, Subgroup.coe_inf]
    exact ((((bu_open _ _ (hps 0)).inter (bu_open _ _ (hps 1))).inter (bu_open _ _ (hps 2))).inter
      (bu_open _ _ (hps 3))).inter (bu_open _ _ hom)
  have hM0 : 2 * (∏ q ∈ D.S, q) * (NumberField.discr T.L).natAbs ≠ 0 := by
    have h1 : (∏ q ∈ D.S, q) ≠ 0 := Finset.prod_ne_zero_iff.2 fun q hq => (hG.S_prime q hq).ne_zero
    have h2 : (NumberField.discr T.L).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero _)
    exact mul_ne_zero (mul_ne_zero two_ne_zero h1) h2
  obtain ⟨v, B, p, hp, hpM, hpv, hnorm, hB, hBdec, hBpow, hBone⟩ := v0Ex T.L Ω U hU g0 _ hM0
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact hpM (dvd_mul_of_dvd_left (dvd_mul_right 2 _) _)
  have hpS : p ∉ D.S := fun h =>
    hpM (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ h) 2) _)
  have hpd : ¬ (p : ℤ) ∣ NumberField.discr T.L := by
    intro h
    apply hpM
    apply dvd_mul_of_dvd_right
    simpa using Int.natAbs_dvd_natAbs.mpr h
  obtain ⟨e, he⟩ := placesEq T
  obtain ⟨-, ⟨φ, hφ, hφL⟩, -⟩ := galEq T
  have hIne : ∀ A : ValuationSubring Ω, Ine (F := W.Lp T.L) A ≤ (W.resP T.L Ω).range := by
    intro A σ hσ
    apply (hφL σ).1
    apply hT.unr A
    exact ⟨dec_of (hφ σ) hσ.1, fun x hx => by rw [hφ]; exact hσ.2 x hx⟩
  have hSdec : ∀ q ∈ D.S, ∀ A : ValuationSubring Ω, A.valuation q < 1 →
      Dec (F := W.Lp T.L) A ≤ (W.resP T.L Ω).range := by
    intro q hq A hA σ hσ
    apply (hφL σ).1
    show resQ T.F (φ σ) ∈ T.K.fixingSubgroup
    apply hT.split q hq A hA
    exact dec_of (fun x => by simp [resQ, hφ]) hσ
  obtain ⟨s, hsA, hs0, hsfin, hsB, hsaway⟩ := mkSet l T.L Ω hG.l_odd hIne D.S hG.S_prime hG.l_mem hSdec
    (fun v => T.pl (e v)) he v B p hp hp2 hpS hpd hpv hnorm hB hBdec
  refine ⟨SetD.mk s e hsA hsfin hsaway ?_ ?_ ?_ (ccOf T s)⟩
  · rw [hs0]
    exact hsB
  · intro g hg i j
    rw [hs0] at hg
    obtain ⟨n, hn⟩ := hBpow g hg
    simp only [U, Subgroup.mem_inf] at hn
    obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, -⟩ := hn
    have key : ∀ k, bu T.L (D.ps k) g = bu T.L (D.ps k) (g0 ^ n) := by
      intro k
      fin_cases k
      exacts [eq_of_ker h0, eq_of_ker h1, eq_of_ker h2, eq_of_ker h3]
    have hg0' : bu T.L (chi D T.pr i) g0 = bu T.L (chi D T.pr j) g0 :=
      Units.ext (by rw [bu_val, bu_val]; exact hg0eq i j)
    rw [← bu_val, ← bu_val]
    change ((bu T.L (D.ps (lab T.pr i)) g : ResidueField c.O)) = (bu T.L (D.ps (lab T.pr j)) g : ResidueField c.O)
    rw [key, key]
    congr 1
    simp only [map_pow, map_zpow]
    exact congrArg (· ^ n) hg0'
  · obtain ⟨d, hd, hdU⟩ := hBone
    refine ⟨d, by rw [hs0]; exact hd, ?_⟩
    have h4 : d⁻¹ * g0 ∈ (bu T.L D.om).ker := (Subgroup.mem_inf.1 hdU).2
    rw [← bu_val, eq_of_ker h4, bu_val]
    exact hg0om
