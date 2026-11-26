module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValuationResidueLemmas
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscAE
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ExistsPowSmulMemBall

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsPtOrdEqAddValuation
open ReciprocityTheory.ChartRestriction.G.T0 Formalism.MainNotions.Gaps.EtaleWeightGaps
open scoped TensorProduct

namespace GlobalTheory

def valCentreOn {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (S : Subalgebra O A)
    (u : AddValuation A (WithTop ℤ)) (h0 : ∀ a ∈ S, 0 ≤ u a) : Ideal S where
  carrier := {a | 0 < u (a : A)}
  add_mem' := fun {a b} ha hb => by
    have := u.map_add (a : A) (b : A)
    exact lt_of_lt_of_le (lt_min ha hb) this
  zero_mem' := by
    change 0 < u ((0 : S) : A)
    simp
  smul_mem' := fun c a ha => by
    change 0 < u ((c : A) * (a : A))
    rw [u.map_mul]
    exact lt_of_lt_of_le ha (le_add_of_nonneg_left (h0 _ c.2))

theorem mem_valCentreOn {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (S : Subalgebra O A)
    (u : AddValuation A (WithTop ℤ)) (h0 : ∀ a ∈ S, 0 ≤ u a) (a : S) :
    a ∈ valCentreOn S u h0 ↔ 0 < u (a : A) := Iff.rfl

theorem valCentreOn_isPrime {O A : Type} [CommRing O] [CommRing A] [Algebra O A]
    (S : Subalgebra O A) (u : AddValuation A (WithTop ℤ)) (h0 : ∀ a ∈ S, 0 ≤ u a) :
    (valCentreOn S u h0).IsPrime := by
  refine ⟨?_, fun {a b} hab => ?_⟩
  · rw [Ideal.ne_top_iff_one, mem_valCentreOn]
    simp
  · rw [mem_valCentreOn] at hab
    rw [mem_valCentreOn, mem_valCentreOn]
    by_contra hc
    rw [not_or, not_lt, not_lt] at hc
    rw [MulMemClass.coe_mul, u.map_mul] at hab
    exact absurd hab (not_lt.2 (add_nonpos hc.1 hc.2))

theorem addVal_eq_of_associated_loc {O A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing A] [Algebra O A] (ζ : Pts O A) (u : AddValuation A (WithTop ℤ))
    (hz : ∀ s : As O A, s ∉ ζ.asIdeal → u (s : A) = 0) (a b : As O A)
    (hab : Associated (algebraMap (As O A) (Loc ζ) a) (algebraMap (As O A) (Loc ζ) b)) :
    u (a : A) = u (b : A) := by
  obtain ⟨w, hw⟩ := hab
  obtain ⟨⟨s, t⟩, hst⟩ := IsLocalization.surj ζ.asIdeal.primeCompl (w : Loc ζ)
  have ht : IsUnit (algebraMap (As O A) (Loc ζ) t) := IsLocalization.map_units _ t
  have hs : s ∉ ζ.asIdeal := by
    have h1 : IsUnit (algebraMap (As O A) (Loc ζ) s) := by
      have := w.isUnit.mul ht
      simpa only [hst] using this
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (Loc ζ) ζ.asIdeal s).1 h1
  have h2 : algebraMap (As O A) (Loc ζ) (a * s) = algebraMap (As O A) (Loc ζ) (b * t) := by
    rw [map_mul, map_mul, ← hw, mul_assoc]
    exact congrArg _ hst.symm
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists ζ.asIdeal.primeCompl (Loc ζ)).1 h2
  have h3 := congrArg (fun x : As O A => u (x : A)) hc
  simp only [MulMemClass.coe_mul, AddValuation.map_mul] at h3
  rw [hz _ c.2, hz _ hs, hz _ t.2] at h3
  simpa using h3

theorem exists_pt_ord_eq_addValuation : ∀ (O A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing A] [Algebra O A] (ϖ : O), IsUnif (A := A) ϖ → ∀ [∀ ζ : Pts O A, IsDVRAt ζ] (u : AddValuation A (WithTop ℤ)), (∀ a ∈ As O A, 0 ≤ u a) → 0 < u (algebraMap O A ϖ) → (∃ a, u a = 1) → ∃ ζ : Pts O A, ∀ a, ord ϖ ζ a = u a := by
  intro O A _ _ _ _ _ ϖ h hD u h0 hϖ h1
  haveI hP := valCentreOn_isPrime (As O A) u h0
  have hcm : ((valCentreOn (As O A) u h0).comap (algebraMap O (As O A))).IsMaximal := by
    have hle : IsLocalRing.maximalIdeal O ≤
        (valCentreOn (As O A) u h0).comap (algebraMap O (As O A)) := by
      rw [h.irreducible.maximalIdeal_eq, Ideal.span_singleton_le_iff_mem, Ideal.mem_comap,
        mem_valCentreOn]
      exact hϖ
    have := (IsLocalRing.maximalIdeal.isMaximal O).eq_of_le (Ideal.IsPrime.ne_top inferInstance) hle
    rw [← this]
    infer_instance
  have hmax : (valCentreOn (As O A) u h0).IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := O) _ hcm
  let ζ : Pts O A := ⟨valCentreOn (As O A) u h0, hmax⟩
  have hz : ∀ s : As O A, s ∉ ζ.asIdeal → u (s : A) = 0 := fun s hs =>
    le_antisymm (not_lt.1 hs) (h0 _ s.2)
  refine ⟨ζ, ?_⟩
  haveI : IsDVRAt ζ := hD ζ
  haveI : IsDomain (Loc ζ) := IsDVRAt.isDomain
  haveI : IsDiscreteValuationRing (Loc ζ) := IsDVRAt.isDVR
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible (Loc ζ)
  obtain ⟨⟨π, t⟩, hπt⟩ := IsLocalization.surj ζ.asIdeal.primeCompl p
  have hπ : Irreducible (algebraMap (As O A) (Loc ζ) π) := by
    have ht : IsUnit (algebraMap (As O A) (Loc ζ) t) := IsLocalization.map_units _ t
    have : Associated p (algebraMap (As O A) (Loc ζ) π) := ⟨ht.unit, hπt⟩
    exact this.irreducible hp
  have hπpos : 0 < u (π : A) := by
    by_contra hc
    exact hπ.not_isUnit ((IsLocalization.AtPrime.isUnit_to_map_iff (Loc ζ) ζ.asIdeal π).2 hc)
  have key : ∀ a : As O A, (vL ζ a = ⊤ ∧ u (a : A) = ⊤) ∨
      ∃ n : ℕ, vL ζ a = n ∧ u (a : A) = n • u (π : A) := by
    intro a
    by_cases ha : algebraMap (As O A) (Loc ζ) a = 0
    · refine Or.inl ⟨(vL_eq_top_iff ζ a).2 ha, ?_⟩
      rw [addVal_eq_of_associated_loc ζ u hz a 0 (by rw [ha, map_zero])]
      simp
    · obtain ⟨n, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
      refine Or.inr ⟨n, ?_, ?_⟩
      · rw [vL_eq_addVal]
        exact IsDiscreteValuationRing.addVal_def _ w hπ n hw
      · rw [addVal_eq_of_associated_loc ζ u hz a (π ^ n)
          (by rw [hw, map_pow]; exact associated_unit_mul_left _ _ w.isUnit)]
        rw [SubmonoidClass.coe_pow, u.map_pow]
  have hϖtop : u (algebraMap O A ϖ) ≠ ⊤ := by
    intro ht
    obtain ⟨v, hv⟩ := h.isUnit.exists_right_inv
    have := congrArg u hv
    rw [u.map_mul, ht, top_add, u.map_one] at this
    exact WithTop.top_ne_zero this
  have hϖe : u (algebraMap O A ϖ) = ep ϖ ζ • u (π : A) := by
    rcases key (algebraMap O (As O A) ϖ) with ⟨_, h2⟩ | ⟨n, h2, h3⟩
    · exact absurd h2 hϖtop
    · rw [← coe_ep ζ h, Nat.cast_inj] at h2
      rw [h2]
      exact h3
  have hmtop : u (π : A) ≠ ⊤ := by
    intro ht
    apply hϖtop
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (ep_pos ζ h).ne'
    rw [hϖe, hk, succ_nsmul, ht, add_top]
  obtain ⟨M, hM⟩ := WithTop.ne_top_iff_exists.1 hmtop
  have hM0 : 0 < M := by
    rw [← hM] at hπpos
    exact_mod_cast hπpos
  have key2 : ∀ x : A, (ord ϖ ζ x = ⊤ ∧ u x = ⊤) ∨
      ∃ z : ℤ, ord ϖ ζ x = z ∧ u x = ((z * M : ℤ) : WithTop ℤ) := by
    intro x
    obtain ⟨k, hk⟩ := h.denom x
    have e1 := ord_pow_smul ζ h k x
    rw [ord_of_mem ζ h hk] at e1
    have e2 : u (ϖ ^ k • x) = (((k : ℤ) * (ep ϖ ζ : ℤ) * M : ℤ) : WithTop ℤ) + u x := by
      rw [Algebra.smul_def, map_pow, u.map_mul, u.map_pow, hϖe, ← hM, ← WithTop.coe_nsmul,
        ← WithTop.coe_nsmul, nsmul_eq_mul, nsmul_eq_mul, mul_assoc]
    rcases key ⟨_, hk⟩ with ⟨h2, h3⟩ | ⟨n, h2, h3⟩
    · left
      rw [h2, ENat.map_top, eq_comm, WithTop.add_eq_top] at e1
      change u (ϖ ^ k • x) = ⊤ at h3
      rw [h3, eq_comm, WithTop.add_eq_top] at e2
      exact ⟨e1.resolve_left WithTop.coe_ne_top, e2.resolve_left WithTop.coe_ne_top⟩
    · right
      rw [h2, ENat.map_natCast] at e1
      change u (ϖ ^ k • x) = _ at h3
      rw [h3, ← hM, ← WithTop.coe_nsmul, nsmul_eq_mul] at e2
      refine ⟨n - k * ep ϖ ζ, ?_, ?_⟩
      · generalize ord ϖ ζ x = y at e1
        cases y with
        | top => simp at e1
        | coe y =>
          rw [← WithTop.coe_add, WithTop.coe_inj] at e1
          rw [WithTop.coe_inj]
          linarith
      · generalize u x = y at e2
        cases y with
        | top => exact absurd (e2.trans (add_top _)) WithTop.coe_ne_top
        | coe y =>
          rw [← WithTop.coe_add, WithTop.coe_inj] at e2
          rw [WithTop.coe_inj]
          linarith
  have hM1 : M = 1 := by
    obtain ⟨a, ha⟩ := h1
    rcases key2 a with ⟨_, h3⟩ | ⟨z, _, h3⟩
    · rw [ha] at h3
      exact absurd h3 WithTop.one_ne_top
    · rw [ha, ← WithTop.coe_one, WithTop.coe_inj] at h3
      exact Int.eq_one_of_mul_eq_one_left hM0.le h3.symm
  intro a
  rcases key2 a with ⟨h2, h3⟩ | ⟨z, h2, h3⟩
  · rw [h2, h3]
  · rw [h2, h3, hM1, mul_one]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.FdegEqFinrankResidueField
open ReciprocityTheory.ChartRestriction.G.T0 Formalism.MainNotions.Gaps.EtaleWeightGaps
open scoped TensorProduct

namespace GlobalTheory.ResDegPlace

open IsLocalRing

theorem finrank_eq_of_surjective {S₀ S k K k' K' : Type*} [CommRing S₀] [CommRing S] [Field k]
    [Field K] [Field k'] [Field K'] [Algebra k K] [Algebra k' K'] (j : S₀ →+* S)
    (p₀ : S₀ →+* k) (q₀ : S₀ →+* k') (p : S →+* K) (q : S →+* K')
    (hp₀ : Function.Surjective p₀) (hq₀ : Function.Surjective q₀)
    (hp : Function.Surjective p) (hq : Function.Surjective q)
    (hker : ∀ x, p x = 0 ↔ q x = 0)
    (h₁ : ∀ r, algebraMap k K (p₀ r) = p (j r)) (h₂ : ∀ r, algebraMap k' K' (q₀ r) = q (j r)) :
    Module.finrank k K = Module.finrank k' K' := by
  have hk : RingHom.ker p = RingHom.ker q := by
    ext x; simp only [RingHom.mem_ker]; exact hker x
  have hk₀ : RingHom.ker p₀ = RingHom.ker q₀ := by
    ext x
    simp only [RingHom.mem_ker]
    rw [← map_eq_zero_iff _ (algebraMap k K).injective, h₁, hker, ← h₂,
      map_eq_zero_iff _ (algebraMap k' K').injective]
  let e : K ≃+* K' := (RingHom.quotientKerEquivOfSurjective hp).symm.trans
    ((Ideal.quotEquivOfEq hk).trans (RingHom.quotientKerEquivOfSurjective hq))
  let e₀ : k ≃+* k' := (RingHom.quotientKerEquivOfSurjective hp₀).symm.trans
    ((Ideal.quotEquivOfEq hk₀).trans (RingHom.quotientKerEquivOfSurjective hq₀))
  have he : ∀ x, e (p x) = q x := fun x => by
    have : (RingHom.quotientKerEquivOfSurjective hp).symm (p x) = Ideal.Quotient.mk _ x := by
      rw [RingEquiv.symm_apply_eq]; rfl
    simp only [e, RingEquiv.trans_apply, this]; rfl
  have he₀ : ∀ x, e₀ (p₀ x) = q₀ x := fun x => by
    have : (RingHom.quotientKerEquivOfSurjective hp₀).symm (p₀ x) = Ideal.Quotient.mk _ x := by
      rw [RingEquiv.symm_apply_eq]; rfl
    simp only [e₀, RingEquiv.trans_apply, this]; rfl
  refine Algebra.finrank_eq_of_equiv_equiv e₀ e ?_
  ext y
  obtain ⟨r, rfl⟩ := hp₀ y
  change algebraMap k' K' (e₀ (p₀ r)) = e (algebraMap k K (p₀ r))
  rw [he₀, h₂, h₁, he]

theorem mem_maximalIdeal_vRing {L : Type*} [Field L] (w : AddValuation L (WithTop ℤ))
    (x : vRing w) : x ∈ maximalIdeal (vRing w) ↔ 0 < w (x : L) := by
  have hunit : IsUnit x ↔ w (x : L) = 0 :=
    (Valuation.valuationSubring.integers (w : Valuation L _)).isUnit_iff_valuation_eq_one
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hunit]
  exact ⟨fun h => lt_of_le_of_ne x.2 (Ne.symm h), fun h => h.ne'⟩

theorem exists_eq_of_nonneg {R F L : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field F] [Algebra R F] [IsFractionRing R F] [Field L] [Algebra F L] [Algebra R L]
    [IsScalarTower R F L] {w : AddValuation L (WithTop ℤ)} (hw : w ∈ ValPl.PlacesOver R L)
    (x : F) (hx : 0 ≤ w (algebraMap F L x)) : ∃ a : R, algebraMap R F a = x := by
  by_cases hx0 : x = 0
  · exact ⟨0, by rw [map_zero, hx0]⟩
  rcases ValuationRing.isInteger_or_isInteger R x with ⟨a, ha⟩ | ⟨a, ha⟩
  · exact ⟨a, ha⟩
  · by_cases hau : IsUnit a
    · obtain ⟨u, rfl⟩ := hau
      refine ⟨↑u⁻¹, ?_⟩
      rw [map_units_inv, ha, inv_inv]
    · exfalso
      have hpos := ((hw.2 a).2).2 hau
      rw [IsScalarTower.algebraMap_apply R F L, ha, map_inv₀] at hpos
      have hxL : algebraMap F L x ≠ 0 := by
        rw [Ne, map_eq_zero_iff _ (algebraMap F L).injective]; exact hx0
      have hs : w (algebraMap F L x) + w (algebraMap F L x)⁻¹ = 0 := by
        rw [← AddValuation.map_mul, mul_inv_cancel₀ hxL, AddValuation.map_one]
      have := ValPl.wt_add_eq_zero hx hpos.le hs
      rw [this, zero_add] at hs
      rw [hs] at hpos
      exact lt_irrefl _ hpos

section
variable {O A : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing A]
  [Algebra O A] {ϖ : O}

theorem ord_pos_iff (h : IsUnif (A := A) ϖ) (ζ : Pts O A) [IsDVRAt ζ] (a : As O A) :
    0 < ord ϖ ζ (a : A) ↔ a ∈ ζ.asIdeal := by
  rw [ord_of_mem ζ h a.2, ← not_not (a := a ∈ ζ.asIdeal), ← vL_eq_zero_iff ζ a]
  change 0 < (vL ζ a).map (Nat.cast : ℕ → ℤ) ↔ _
  generalize vL ζ a = v
  cases v with
  | top => simp
  | coe n =>
    rw [ENat.map_natCast, WithTop.coe_pos]
    simp [Nat.pos_iff_ne_zero]

theorem exists_approx (h : IsUnif (A := A) ϖ) (ζ : Pts O A) [IsDVRAt ζ] (x : A) (hx : 0 ≤ ord ϖ ζ x) :
    ∃ a : As O A, 0 < ord ϖ ζ ((a : A) - x) := by
  obtain ⟨n, hn⟩ := h.denom x
  have h1 := hx
  rw [ord_eq ζ h hn, ordAt_nonneg_iff ζ h, vL_eq_addVal, vL_eq_addVal,
    IsDiscreteValuationRing.addVal_le_iff_dvd] at h1
  obtain ⟨c, hc⟩ := h1
  obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective ζ.asIdeal.primeCompl c
  have h2 : algebraMap (As O A) (Loc ζ) (⟨ϖ ^ n • x, hn⟩ * (s : As O A)) =
      algebraMap (As O A) (Loc ζ) (algebraMap O (As O A) ϖ ^ n * b) := by
    rw [map_mul, hc, mul_assoc, IsLocalization.mk'_spec, ← map_mul]
  obtain ⟨t, ht⟩ := (IsLocalization.eq_iff_exists ζ.asIdeal.primeCompl (Loc ζ)).1 h2
  have h3 : (algebraMap O A ϖ) ^ n * ((((t : As O A) : A) * ((s : As O A) : A)) * x) =
      (algebraMap O A ϖ) ^ n * (((t : As O A) : A) * (b : A)) := by
    have := congrArg Subtype.val ht
    simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, Algebra.smul_def, map_pow] at this
    have e : ((algebraMap O (As O A) ϖ : As O A) : A) = algebraMap O A ϖ := rfl
    rw [e] at this
    linear_combination this
  have h4 := (h.isUnit.pow n).mul_right_inj.1 h3
  obtain ⟨d, i, hi, hdi⟩ := Ideal.IsMaximal.exists_inv ζ.isMaximal (t * s).2
  refine ⟨d * (t * b), ?_⟩
  have h5 : ((d * (t * b) : As O A) : A) - x = ((-i : As O A) : A) * x := by
    have := congrArg Subtype.val hdi
    simp only [Submonoid.coe_mul, AddMemClass.coe_add, MulMemClass.coe_mul, OneMemClass.coe_one,
      NegMemClass.coe_neg] at this ⊢
    linear_combination x * this - (d : A) * h4
  rw [h5, ord_mul ζ h]
  exact add_pos_of_pos_of_nonneg ((ord_pos_iff h ζ _).2 (ζ.asIdeal.neg_mem hi)) hx

end

theorem pos_of_sub_pos {S : Type*} [CommRing S] (u : AddValuation S (WithTop ℤ)) {x y : S}
    (h : 0 < u (x - y)) (hy : 0 < u y) : 0 < u x := by
  have := u.map_lt_add h hy
  rwa [sub_add_cancel] at this

theorem fdeg_eq_finrank_residueField : ∀ (R R' F : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R'] [IsLocalHom (algebraMap R R')] [Field F] [Algebra R F] [IsFractionRing R F], Function.Surjective (IsLocalRing.ResidueField.map (algebraMap R R')) → ∀ (L : Type) [Field L] [Algebra F L] [Algebra R L] [IsScalarTower R F L] (A : Type) [CommRing A] [Algebra R' A] (ϖ : R'), IsUnif (A := A) ϖ → ∀ (ζ : Pts R' A) [IsDVRAt ζ] (w : AddValuation L (WithTop ℤ)), w ∈ ValPl.PlacesOver R L → ∀ (S : Type) [CommRing S] (u : AddValuation S (WithTop ℤ)) (Ψ : A →+* S) (ι : L →+* S), Function.Surjective Ψ → (∀ r : R, Ψ (algebraMap R' A (algebraMap R R' r)) = ι (algebraMap R L r)) → (∀ g, u (ι g) = w g) → (∀ a, ord ϖ ζ a = u (Ψ a)) → (∀ x, 0 ≤ u x → ∃ g, 0 ≤ w g ∧ 0 < u (x - ι g)) → fdeg ζ = (letI := resAlg (F := F) w; Module.finrank (IsLocalRing.ResidueField ((vRing w).comap (algebraMap F L))) (IsLocalRing.ResidueField (vRing w))) := by
  intro R R' F _ _ _ _ _ _ _ _ _ _ _ hRR L _ _ _ _ A _ _ ϖ h ζ _ w hw S _ u Ψ ι hΨ hcomp hι hord
    hres
  letI := resAlg (F := F) w
  let T : Subring (As R' A × vRing w) :=
    { carrier := {z | 0 < u (Ψ (z.1 : A) - ι (z.2 : L))}
      mul_mem' := by
        intro z z' hz hz'
        change 0 < u (Ψ ((z.1 : A) * z'.1) - ι ((z.2 : L) * z'.2))
        have e : Ψ ((z.1 : A) * z'.1) - ι ((z.2 : L) * z'.2) =
            (Ψ (z'.1 : A) - ι (z'.2 : L)) * Ψ z.1 + (Ψ (z.1 : A) - ι (z.2 : L)) * ι z'.2 := by
          rw [map_mul, map_mul]; ring
        rw [e]
        refine u.map_lt_add ?_ ?_
        · rw [u.map_mul, ← hord]
          exact add_pos_of_pos_of_nonneg hz' (ord_nonneg ζ h z.1.2)
        · rw [u.map_mul, hι]
          exact add_pos_of_pos_of_nonneg hz z'.2.2
      one_mem' := by
        change 0 < u (Ψ 1 - ι 1)
        simp
      add_mem' := by
        intro z z' hz hz'
        change 0 < u (Ψ ((z.1 : A) + z'.1) - ι ((z.2 : L) + z'.2))
        rw [map_add (f := _), map_add (f := _), add_sub_add_comm]
        exact u.map_lt_add hz hz'
      zero_mem' := by
        change 0 < u (Ψ 0 - ι 0)
        simp
      neg_mem' := by
        intro z hz
        change 0 < u (Ψ (-(z.1 : A)) - ι (-(z.2 : L)))
        rw [map_neg, map_neg, ← neg_sub', u.map_neg]
        exact hz }
  have hT : ∀ z : T, 0 < u (Ψ (z.1.1 : A) - ι (z.1.2 : L)) := fun z => z.2
  let jw : R →+* vRing w := (algebraMap R L).codRestrict (vRing w) (fun r => (hw.2 r).1)
  let j : R →+* T := (((algebraMap R' (As R' A)).comp (algebraMap R R')).prod jw).codRestrict T
    (fun r => by
      change 0 < u (Ψ (algebraMap R' A (algebraMap R R' r)) - ι (algebraMap R L r))
      rw [hcomp, sub_self]; simp)
  have hOw : ∀ a : R, algebraMap R F a ∈ (vRing w).comap (algebraMap F L) := fun a => by
    rw [ValuationSubring.mem_comap, ← IsScalarTower.algebraMap_apply]
    exact (hw.2 a).1
  let φ : R →+* (vRing w).comap (algebraMap F L) := (algebraMap R F).codRestrict _ hOw
  let p : T →+* ResidueField (Loc ζ) := ((residue (Loc ζ)).comp (algebraMap (As R' A) (Loc ζ))).comp
    ((RingHom.fst _ _).comp T.subtype)
  let q : T →+* ResidueField (vRing w) := (residue (vRing w)).comp
    ((RingHom.snd _ _).comp T.subtype)
  refine finrank_eq_of_surjective j ((residue R').comp (algebraMap R R')) ((residue _).comp φ) p q
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro y
    obtain ⟨y, rfl⟩ := hRR y
    obtain ⟨r, rfl⟩ := residue_surjective y
    exact ⟨r, rfl⟩
  · intro y
    obtain ⟨x, rfl⟩ := residue_surjective y
    obtain ⟨a, ha⟩ := exists_eq_of_nonneg hw (x : F) x.2
    exact ⟨a, congrArg (residue _) (Subtype.ext ha)⟩
  · intro y
    haveI := ζ.isMaximal
    obtain ⟨a, rfl⟩ := Ideal.algebraMap_residueField_surjective ζ.asIdeal y
    obtain ⟨g, hg, hag⟩ := hres (Ψ a) (by rw [← hord]; exact ord_nonneg ζ h a.2)
    exact ⟨⟨(a, ⟨g, hg⟩), hag⟩, rfl⟩
  · intro y
    obtain ⟨g, rfl⟩ := residue_surjective y
    obtain ⟨x, hx⟩ := hΨ (ι g)
    obtain ⟨a, ha⟩ := exists_approx h ζ x (by rw [hord, hx, hι]; exact g.2)
    rw [hord, map_sub, hx] at ha
    exact ⟨⟨(a, g), ha⟩, rfl⟩
  · intro z
    change residue (Loc ζ) (algebraMap (As R' A) (Loc ζ) z.1.1) = 0 ↔ residue (vRing w) z.1.2 = 0
    rw [residue_eq_zero_iff, residue_eq_zero_iff, mem_maximalIdeal_vRing,
      IsLocalization.AtPrime.to_map_mem_maximal_iff (Loc ζ) ζ.asIdeal, ← ord_pos_iff h, hord, ← hι]
    refine ⟨pos_of_sub_pos u ?_, pos_of_sub_pos u (hT z)⟩
    rw [← neg_sub, u.map_neg]
    exact hT z
  · intro r
    rfl
  · intro r
    change residue (vRing w) (comapIncl (vRing w) (algebraMap F L) (φ r)) = residue (vRing w) (jw r)
    congr 1
    exact Subtype.ext (IsScalarTower.algebraMap_apply R F L r).symm

end GlobalTheory.ResDegPlace
end
