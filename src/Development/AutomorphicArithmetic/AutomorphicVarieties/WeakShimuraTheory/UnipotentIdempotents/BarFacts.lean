module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.TCont
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.CharpolySmulScale
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusDensity.FrobDense

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.BarFacts
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

private theorem open_bar {Γ O : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CommRing O] [IsLocalRing O]
    (γ : Γ →* Oˣ) (H : Subgroup Γ) (hH : IsOpen (H : Set Γ)) (h : ∀ g ∈ H, residue O (γ g : O) = 1) :
    IsOpen {g : Γ | residue O (γ g : O) = 1} := by
  have h2 : H ≤ ((Units.map (residue O).toMonoidHom).comp γ).ker := fun g hg => Units.ext (h g hg)
  have h3 := Subgroup.isOpen_mono h2 hH
  convert h3 using 1
  ext g
  exact ⟨fun h => Units.ext h, fun h => congrArg Units.val h⟩

theorem UpperTheory.V.Ws.Lk.barFacts :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c}, D.Good → (∀ i, IsOpen {g : G ℚ Ω | Raw.bar (D.ps i) g = 1}) ∧ IsOpen {g : G ℚ Ω | Raw.bar D.om g = 1} ∧ ∀ A, Raw.Away D.S A → ∀ g ∈ Ine (F := ℚ) A, (∀ i, D.ps i g = 1) ∧ D.rbar g = 1 := by
  intro Ω _ _ _ l _ c D h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hr, ho, hu⟩ := facts D h
  refine ⟨fun i => open_bar _ _ hr fun g hg => ?_, open_bar _ _ ho fun g hg => ?_, fun A hA g hg => ?_⟩
  · have h1 : D.rbar g = 1 := hg
    simpa [Raw.rbar, Raw.r0, diagRep, mapRep] using congrFun (congrFun h1 i) i
  · rw [MonoidHom.mem_ker.1 hg, Units.val_one, map_one]
  · have h2 : ∀ i, D.ps i g = 1 := fun i => hu i A hA hg
    refine ⟨h2, ?_⟩
    ext i j
    by_cases e : i = j
    · subst e
      simp [Raw.rbar, Raw.r0, diagRep, mapRep, h2]
    · simp [Raw.rbar, Raw.r0, diagRep, mapRep, e]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.PrFacts
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

theorem UpperTheory.V.Ws.Lk.prFacts :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : W.HidaSetting l L Ω) (V : s.Lev), Function.Surjective V.pr ∧ (∀ g : G L Ω, ∃ g' : G L Ω, W.resP L Ω g' = s.c * W.resP L Ω g * s.c⁻¹ ∧ V.frame.conj (V.pr g) = V.pr g') ∧ (∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R] (g : G L Ω), (V.frame.eps O R (V.pr g) : R) = algebraMap O R (chiO L Ω l O g)) ∧ ∀ (v : W.Vl l L) (g : Dec (F := L) (s.A v)), g ∈ V.frame.mu v → ∃ a : ℕ, (g : G L Ω) ^ l ^ a ∈ (commutator (G L Ω)).topologicalClosure := by
  intro l _ L Ω _ _ _ _ _ _ s V
  refine ⟨fun x => ?_, fun t => ?_, fun O _ _ R _ _ g => ?_, fun v g hg => ?_⟩
  · obtain ⟨y, hy⟩ : ∃ y, toGS Ω V.S' y = x.1 := QuotientGroup.mk'_surjective _ x.1
    obtain ⟨t, rfl⟩ : y ∈ (W.resP L Ω).range := (V.hη y).1 (by rw [hy]; exact x.2)
    exact ⟨t, Subtype.ext hy⟩
  · obtain ⟨t', ht'⟩ : s.c * W.resP L Ω t * s.c⁻¹ ∈ (W.resP L Ω).range := by
      rw [← V.hη, map_mul (toGS Ω V.S'), map_mul (toGS Ω V.S'), map_inv (toGS Ω V.S')]
      exact (V.frame.conj (V.pr t)).2
    refine ⟨t', ht', Subtype.ext ?_⟩
    show toGS Ω V.S' s.c * toGS Ω V.S' (W.resP L Ω t) * (toGS Ω V.S' s.c)⁻¹ = toGS Ω V.S' (W.resP L Ω t')
    rw [ht', map_mul, map_mul, map_inv]
  · have h : V.ε (toGS Ω V.S' (W.resP L Ω g)) = cycZ L Ω l g := DFunLike.congr_fun V.hε (W.resP L Ω g)
    show algebraMap O R (algebraMap ℤ_[l] O (V.ε (toGS Ω V.S' (W.resP L Ω g)) : ℤ_[l]ˣ)) = _
    rw [h]
    rfl
  · have hg' : (QuotientGroup.mk' _ g : TopologicalAbelianization (Dec (F := L) (s.A v))) ∈
        CommGroup.primaryComponent (TopologicalAbelianization (Dec (F := L) (s.A v))) l := hg
    obtain ⟨a, ha⟩ : ∃ a : ℕ, (QuotientGroup.mk' _ g : TopologicalAbelianization (Dec (F := L) (s.A v))) ^ l ^ a = 1 := by
      first
      | exact exists_orderOf_eq_prime_pow_iff.1 hg'
      | exact hg'
      | simpa using hg'
    refine ⟨a, ?_⟩
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at ha
    have hle : (commutator (Dec (F := L) (s.A v))).topologicalClosure ≤
        (commutator (G L Ω)).topologicalClosure.comap (Dec (F := L) (s.A v)).subtype := by
      refine Subgroup.topologicalClosure_minimal _ ?_
        ((Subgroup.isClosed_topologicalClosure _).preimage continuous_subtype_val)
      rw [← Subgroup.map_le_iff_le_comap, commutator_def, Subgroup.map_commutator]
      exact (Subgroup.commutator_mono le_top le_top).trans (Subgroup.le_topologicalClosure _)
    exact hle ha
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.PlusEq
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

private theorem plus_eq {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    {D : Raw Ω c} (T : Tower D) (x : Ω) : x ∈ T.F ↔ ∃ y : W.Lp T.L, algebraMap (W.Lp T.L) Ω y = x := by
  classical
  set E : Subfield T.L := Subfield.comap (T.L.val : T.L →+* Ω) T.F.toSubfield with hEdef
  let e : E ≃+* T.F :=
    { toFun := fun y => ⟨((y : T.L) : Ω), y.2⟩
      invFun := fun z => ⟨⟨(z : Ω), T.F_le z.2⟩, z.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  haveI : IsTotallyReal E := IsTotallyReal.ofRingEquiv e.symm
  have hEM : E ≤ maximalRealSubfield T.L := IsTotallyReal.le_maximalRealSubfield E
  have hdE : Module.finrank ℚ E = Module.finrank ℚ T.F :=
    (RingEquiv.toRatAlgEquiv e).toLinearEquiv.finrank_eq
  have hsup : Module.finrank ℚ T.L ≤ Module.finrank ℚ T.F * 2 := by
    have h1 := IntermediateField.finrank_sup_le T.F T.K
    rw [T.degK, ← T.hL] at h1
    exact h1
  have hM : Module.finrank ℚ (maximalRealSubfield T.L) * 2 = Module.finrank ℚ T.L := by
    rw [← Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield T.L) T.L]
    exact (letI : Module.Free (maximalRealSubfield T.L) T.L := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (maximalRealSubfield T.L) T.L)
  letI : Module.Free E T.L := Module.Free.of_divisionRing _ _
  have hE2 : Module.finrank ℚ E * Module.finrank E T.L = Module.finrank ℚ T.L :=
    Module.finrank_mul_finrank ℚ E T.L
  have hle : Module.finrank ℚ E ≤ Module.finrank ℚ (maximalRealSubfield T.L) :=
    LinearMap.finrank_le_finrank_of_injective
      (f := (Subfield.inclusion hEM).toRatAlgHom.toLinearMap) (Subfield.inclusion hEM).injective
  have hpos : 0 < Module.finrank ℚ E := Module.finrank_pos
  have hposM : 0 < Module.finrank ℚ (maximalRealSubfield T.L) := Module.finrank_pos
  have hdeg : Module.finrank E T.L = 2 := by
    apply le_antisymm
    · have : Module.finrank ℚ E * Module.finrank E T.L ≤ Module.finrank ℚ E * 2 := by
        rw [hE2, hdE]; exact hsup
      exact Nat.le_of_mul_le_mul_left this hpos
    · have : Module.finrank ℚ (maximalRealSubfield T.L) * 2 ≤
          Module.finrank ℚ (maximalRealSubfield T.L) * Module.finrank E T.L := by
        rw [hM, ← hE2]
        exact Nat.mul_le_mul_right _ hle
      exact Nat.le_of_mul_le_mul_left this hposM
  haveI : Algebra.IsQuadraticExtension E T.L := { finrank_eq_two' := hdeg }
  have hEq : E = maximalRealSubfield T.L := NumberField.CMExtension.eq_maximalRealSubfield T.L E
  constructor
  · intro hx
    have hy : (⟨x, T.F_le hx⟩ : T.L) ∈ maximalRealSubfield T.L := by
      rw [← hEq]; exact hx
    exact ⟨⟨⟨x, T.F_le hx⟩, hy⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    have hy : (y : T.L) ∈ E := by rw [hEq]; exact y.2
    exact hy

private theorem fix_L {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    {D : Raw Ω c} (T : Tower D) (τ : G T.F Ω) : τ ∈ T.GalL ↔ ∀ x : T.L, τ (x : Ω) = x := by
  have hF : resQ T.F τ ∈ T.F.fixingSubgroup := by
    rw [IntermediateField.fixingSubgroup, mem_fixingSubgroup_iff]
    intro y hy
    exact τ.commutes ⟨y, hy⟩
  unfold Tower.GalL
  rw [Subgroup.mem_comap]
  constructor
  · intro h x
    have hsup : resQ T.F τ ∈ (T.F ⊔ T.K).fixingSubgroup := by
      rw [IntermediateField.fixingSubgroup_sup]
      exact ⟨hF, h⟩
    rw [← T.hL, IntermediateField.fixingSubgroup, mem_fixingSubgroup_iff] at hsup
    exact hsup x x.2
  · intro h
    rw [IntermediateField.fixingSubgroup, mem_fixingSubgroup_iff]
    intro y hy
    exact h ⟨y, Lk.K_le T hy⟩

theorem UpperTheory.V.Ws.Lk.galEq :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} (T : Tower D), (∀ x : Ω, x ∈ T.F ↔ ∃ y : W.Lp T.L, algebraMap (W.Lp T.L) Ω y = x) ∧ (∃ φ : G (W.Lp T.L) Ω ≃* G T.F Ω, (∀ σ x, φ σ x = σ x) ∧ ∀ σ, φ σ ∈ T.GalL ↔ σ ∈ (W.resP T.L Ω).range) ∧ ∀ τ : G T.F Ω, τ ∈ T.GalL ↔ τ ∈ (resLe T.F_le).range := by
  intro Ω _ _ _ l _ c D T
  have hP := plus_eq T
  refine ⟨hP, ?_, ?_⟩
  · let φ : G (W.Lp T.L) Ω ≃* G T.F Ω :=
      { toFun := fun σ => AlgEquiv.ofRingEquiv (f := (σ : Ω ≃ₐ[W.Lp T.L] Ω).toRingEquiv) (fun x => by
            obtain ⟨y, hy⟩ := (hP (x : Ω)).1 x.2
            change σ (x : Ω) = (x : Ω)
            rw [← hy]
            exact σ.commutes y)
        invFun := fun σ => AlgEquiv.ofRingEquiv (f := (σ : Ω ≃ₐ[T.F] Ω).toRingEquiv) (fun y => by
            have hx := (hP (algebraMap (W.Lp T.L) Ω y)).2 ⟨y, rfl⟩
            exact σ.commutes ⟨_, hx⟩)
        left_inv := fun σ => by ext; rfl
        right_inv := fun σ => by ext; rfl
        map_mul' := fun σ τ => by ext; rfl }
    refine ⟨φ, fun σ x => rfl, fun σ => ?_⟩
    rw [fix_L, MonoidHom.mem_range]
    constructor
    · intro h
      exact ⟨AlgEquiv.ofRingEquiv (f := (σ : Ω ≃ₐ[W.Lp T.L] Ω).toRingEquiv) (fun x => h x), by ext; rfl⟩
    · rintro ⟨ρ, rfl⟩ x
      exact ρ.commutes x
  · intro τ
    rw [fix_L, MonoidHom.mem_range]
    constructor
    · intro h
      exact ⟨AlgEquiv.ofRingEquiv (f := (τ : Ω ≃ₐ[T.F] Ω).toRingEquiv) (fun x => h x), by ext; rfl⟩
    · rintro ⟨ρ, rfl⟩ x
      exact ρ.commutes x
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.OchOf
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

theorem UpperTheory.V.Ws.Lk.ochOf :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} (Q : QCh T) (c' : Coef l) (h : c.O ≤ c'.O) (κ β : G T.L Ω →* c'.Oˣ), toQ κ = Q.κ → toQ β = Q.β → (AdicCont (maximalIdeal c'.O) fun g => (κ g : c'.O)) → (AdicCont (maximalIdeal c'.O) fun g => (β g : c'.O)) → (∀ g, residue c'.O (β g) = 1) → Nonempty (OCh T c' h) := by
  intro Ω _ _ _ l _ c D T Q c' h κ β hκQ hβQ hκc hβc hβr
  let U : (c'.O)ˣ →* (PadicAlgCl l)ˣ := Units.map (algebraMap c'.O (PadicAlgCl l) : c'.O →* PadicAlgCl l)
  have hUinj : Function.Injective U := fun a b hab => Units.ext (Subtype.val_injective (congrArg Units.val hab))
  have hUκ : ∀ g, U (κ g) = Q.κ g := fun g => by
    rw [← hκQ]
    rfl
  have hUβ : ∀ g, U (β g) = Q.β g := fun g => by
    rw [← hβQ]
    rfl
  have hUchi : ∀ g, U (chiO T.L Ω l c'.O g) = cycBar T.L Ω l g := fun g => by
    rw [← (auChi T.L Ω c').1]
    rfl
  have hUth : ∀ r, ((inc h (D.th r : c.O) : c'.O) : PadicAlgCl l) = ((toQ D.th r : (PadicAlgCl l)ˣ) : PadicAlgCl l) := fun r => rfl
  refine ⟨{ κ := κ, β := β, t := Q.t, κ_cont := hκc, β_cont := hβc, t_cont := Q.t_cont, β_t := ?_, β_red := hβr, conj := ?_, t_unr := Q.t_unr, unr := ?_, tame := ?_, mu := ?_, cyc := ?_ }⟩
  · intro g hg
    have h1 := Q.β_t hg
    rw [MonoidHom.mem_ker] at h1 ⊢
    apply hUinj
    rw [hUβ, map_one]
    exact h1
  · intro σ hσ g g' hg
    obtain ⟨e1, e2, e3⟩ := Q.conj σ hσ g g' hg
    refine ⟨?_, ?_, e3⟩
    · apply Subtype.val_injective
      have e1' := congrArg Units.val e1
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_one] at e1'
      have k1 : ((κ g : c'.O) : PadicAlgCl l) = (Q.κ g : PadicAlgCl l) := congrArg Units.val (hUκ g)
      have k2 : ((κ g' : c'.O) : PadicAlgCl l) = (Q.κ g' : PadicAlgCl l) := congrArg Units.val (hUκ g')
      have k3 : ((chiO T.L Ω l c'.O g : c'.O) : PadicAlgCl l) = (cycBar T.L Ω l g : PadicAlgCl l) := congrArg Units.val (hUchi g)
      simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, OneMemClass.coe_one, k1, k2, k3, hUth]
      exact e1'
    · apply hUinj
      rw [map_mul, hUβ, hUβ, map_one]
      exact e2
  · intro A hA g hg
    have h1 := Q.unr A hA hg
    rw [MonoidHom.mem_ker] at h1 ⊢
    apply hUinj
    rw [hUκ, map_one]
    exact h1
  · obtain ⟨m, hm, hmA⟩ := Q.tame
    refine ⟨m, hm, fun A hA g hg => hUinj ?_⟩
    rw [map_pow, hUκ, map_one]
    exact hmA A hA g hg
  · intro g a ha
    refine ⟨hUinj ?_, (Q.mu g a ha).2⟩
    rw [hUκ, map_one]
    exact (Q.mu g a ha).1
  · intro A hA
    obtain ⟨a, b, k, hk, hb, hall⟩ := Q.cyc A hA
    refine ⟨a, b, k, hk, hb, fun g hg => ⟨hUinj ?_, hUinj ?_⟩⟩
    · rw [map_pow, map_mul, map_zpow, hUκ, hUchi, map_one]
      exact (hall g hg).1
    · rw [map_pow, map_mul, map_pow, map_zpow, hUβ, hUchi, map_one]
      exact (hall g hg).2
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.KapConj
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

private theorem kapConj_alg {M : Type} [CommGroup M] (k k' y b b' o x p E : M) (e n : ℕ)
    (h0 : k * k' * (o ^ (e + 3) * x * p) = 1) (h1 : y ^ 2 * o = E) (h2 : b * b' = 1) :
    (k * y⁻¹ ^ (e + 4) * b ^ n) * (k' * y⁻¹ ^ (e + 4) * b' ^ n) * (E * o⁻¹ * x * (E ^ e * p)) * E ^ 3 = 1 := by
  subst h1
  apply Additive.ofMul.injective
  have h0' := congrArg Additive.ofMul h0
  have h2' := congrArg Additive.ofMul h2
  simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_one, add_smul, one_smul, neg_smul, smul_add, smul_neg] at h0' h2' ⊢
  have hk : Additive.ofMul k' = -(Additive.ofMul k +
      (e • Additive.ofMul o + 3 • Additive.ofMul o + Additive.ofMul x + Additive.ofMul p)) := by
    rw [eq_neg_iff_add_eq_zero, ← h0']
    abel
  have hb : Additive.ofMul b' = -Additive.ofMul b := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact h2'
  rw [hk, hb]
  simp only [smul_add, smul_neg, neg_add, neg_neg, two_smul]
  abel

theorem UpperTheory.V.Ws.Lk.kapConj :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} (P : Pre T), T.Deep → ∀ σ ∉ T.K.fixingSubgroup, ∀ g g' : G T.L Ω, resQ T.L g' = σ * resQ T.L g * σ⁻¹ → P.κ g * P.κ g' * toQ D.th (resQ T.L g) * cycBar T.L Ω l g ^ 3 = 1 ∧ P.βL g * P.βL g' = 1 ∧ P.tL g * P.tL g' = 1 := by
  intro Ω _ _ _ l _ c D T P hDeep σ hσ g g' hgg
  have hKL := K_le T
  have hFL : T.F ≤ T.L := T.hL ▸ le_sup_left
  have hres : ∀ h : G T.L Ω, resQ T.K (resLe hKL h) = resQ T.L h := fun h => rfl
  have hresF : ∀ h : G T.L Ω, resQ T.F (resLe hFL h) = resQ T.L h := fun h => rfl
  have hss : resQ T.K (resLe hKL g') = σ * resQ T.K (resLe hKL g) * σ⁻¹ := by
    rw [hres, hres]
    exact hgg
  obtain ⟨m, hm, hψ⟩ := hDeep
  have hψg : ∃ m, l.Coprime m ∧ D.ψ (resQ T.K (resLe hKL g)) ^ m = 1 :=
    ⟨m, hm, by rw [hres, ← hresF]; exact hψ _⟩
  have h0 := P.κ₀_conj σ hσ _ _ hss hψg
  obtain ⟨hb, ht⟩ := P.conj σ hσ _ _ hss
  refine ⟨?_, hb, ht⟩
  have hγ : P.γ (resQ T.L g') = P.γ (resQ T.L g) := by
    rw [hgg, map_mul, map_mul, map_inv, mul_comm (P.γ σ), mul_inv_cancel_right]
  have hcyc : cycBar T.L Ω l g = cycBar ℚ Ω l (resQ T.L g) := by
    rfl
  have hchi : ∀ x, toQ (chiO ℚ Ω l c.O) x = cycBar ℚ Ω l x := fun x => by
    rw [← (auChi ℚ Ω c).1]
  have hth : ∀ x, toQ D.th x = toQ (chiO ℚ Ω l c.O) x * (toQ D.om x)⁻¹ * toQ D.ξ x *
      (toQ (chiO ℚ Ω l c.O) x ^ D.e * toQ D.ψ x) := by
    intro x
    simp only [toQ, W.pushCh, Raw.th, Raw.al, Raw.Psi, Chr.Psi, MonoidHom.comp_apply, MonoidHom.mul_apply,
      MonoidHom.inv_apply, map_mul, map_inv]
    rw [show (chiO ℚ Ω l c.O ^ (D.e : ℤ)) x = (chiO ℚ Ω l c.O x) ^ (D.e : ℤ) from rfl, zpow_natCast, map_pow]
  have hk0 : toQ (D.om ^ (D.e + 3) * D.ξ * D.ψ) (resQ T.L g) =
      toQ D.om (resQ T.L g) ^ (D.e + 3) * toQ D.ξ (resQ T.L g) * toQ D.ψ (resQ T.L g) := by
    simp only [toQ, W.pushCh, MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.pow_apply, map_mul, map_pow]
  rw [hres, hk0] at h0
  have h1 := P.γ_sq (resQ T.L g)
  have key := kapConj_alg _ _ _ _ _ _ _ _ _ D.e (D.e % 2) h0 h1 hb
  rw [hth, hchi, hcyc]
  simp only [Pre.κ, Pre.βL, MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.pow_apply, MonoidHom.inv_apply]
  rw [hγ]
  exact key
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.ExistsCharacterOfDirichletData
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

private theorem cls_one {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {n M : ℕ} [NeZero n] (h : n ∣ M) {s : G ℚ Ω}
    (hs : ∀ ζ : Ω, ζ ^ M = 1 → s ζ = ζ) : Chr.cls ℚ Ω n s = 1 := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω n
  have h1 : s ζ = ζ := hs ζ (by obtain ⟨k, rfl⟩ := h; rw [pow_mul, hζ.pow_eq_one, one_pow])
  have h2 := Chr.cls_spec (k := ℚ) n s ζ hζ.pow_eq_one
  rw [h1] at h2
  have h3 : ζ ^ ((Chr.cls ℚ Ω n s : ZMod n)).val = ζ ^ (1 : ℕ) := by rw [pow_one]; exact h2.symm
  have hfin : IsOfFinOrder ζ := isOfFinOrder_iff_pow_eq_one.2 ⟨n, NeZero.pos n, hζ.pow_eq_one⟩
  rw [hfin.pow_eq_pow_iff_modEq, ← hζ.eq_orderOf] at h3
  ext
  rw [Units.val_one, ← ZMod.natCast_zmod_val ((Chr.cls ℚ Ω n s : ZMod n)), (ZMod.natCast_eq_natCast_iff _ _ _).2 h3,
    Nat.cast_one]

private theorem exp_ex {l n : ℕ} (hl : l.Prime) (hn : n ≠ 0) :
    ∃ k m : ℕ, l.Coprime m ∧ n ∣ k * m ∧ ∀ m' : ℕ, l.Coprime m' → k ≡ 1 [MOD Nat.gcd n m'] := by
  obtain ⟨a, m, hlm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn l hl.one_lt.ne'
  have hcop : l.Coprime m := (Nat.Prime.coprime_iff_not_dvd hl).2 hlm
  have hcop2 : (l ^ a).Coprime m := Nat.Coprime.pow_left a hcop
  let k := Nat.chineseRemainder hcop2 0 1
  have hk0 : k ≡ 0 [MOD l ^ a] := k.2.1
  have hk1 : k ≡ 1 [MOD m] := k.2.2
  refine ⟨k, m, hcop, ?_, ?_⟩
  · exact Nat.mul_dvd_mul (Nat.modEq_zero_iff_dvd.1 hk0) dvd_rfl
  · intro m' hm'
    refine Nat.ModEq.of_dvd ?_ hk1
    have hg : (Nat.gcd (l ^ a * m) m').Coprime (l ^ a) :=
      Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_right _ _) (Nat.Coprime.pow_right a hm'.symm)
    exact hg.dvd_of_dvd_mul_left (Nat.gcd_dvd_left _ _)

private theorem cyclotomicClass_eq_of_isComplexConj {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (N : ℕ) [NeZero N] {σ τ : G ℚ Ω}
    (hσ : IsCC σ) (hτ : IsCC τ) : Chr.cls ℚ Ω N σ = Chr.cls ℚ Ω N τ := by
  have key : ∀ {ρ : G ℚ Ω}, IsCC ρ → ∀ ζ : Ω, ζ ^ N = 1 → ρ ζ = ζ⁻¹ := by
    rintro ρ ⟨j, hj⟩ ζ hζ
    apply j.injective
    rw [hj, map_inv₀, Complex.inv_eq_conj]
    exact Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hζ, map_one]) (NeZero.ne N)
  have h1 : Chr.cls ℚ Ω N (τ⁻¹ * σ) = 1 := cls_one (dvd_refl N) (fun ζ hζ => by
    rw [AlgEquiv.mul_apply, key hσ ζ hζ, ← key hτ ζ hζ]
    exact AlgEquiv.aut_inv τ ▸ τ.symm_apply_apply ζ)
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  exact h1.symm

private theorem exists_character_of_dirichlet_data {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [hl : Fact l.Prime] {c : Coef l}
    {D : Raw Ω c} (hD : D.Good) {e N : ℕ} [NeZero N] {ψ : DirichletCharacter c.O N} {n' p₁ m₀ : ℕ}
    (hO : Aut.OfChar D e ψ n' p₁ m₀) :
    ∃ (χ : G ℚ Ω →* c.Oˣ) (N m : ℕ), 1 ≤ N ∧ Af.KillsMu N χ ∧ l.Coprime m ∧ χ ^ m = 1 ∧ (∀ σ, IsCC σ → χ σ = 1) ∧
      (∀ A, Raw.Away D.S A → Ine (F := ℚ) A ≤ χ.ker) ∧
      ∀ g, (∃ m' : ℕ, l.Coprime m' ∧ D.ψ g ^ m' = 1) → χ g = (D.om ^ (D.e + 3) * D.ξ * D.ψ) g := by
  obtain ⟨-, hpsi, -, hp1, ξ', ξ₀, -, -, -, hxi⟩ := hO
  haveI := hp1
  have hlp : l.Prime := hl.out
  haveI : NeZero l := ⟨hlp.ne_zero⟩
  have hl2 : l ≠ 2 := hD.l_odd
  have hn0 : Fintype.card (ZMod N)ˣ ≠ 0 := Fintype.card_ne_zero
  obtain ⟨k, m, hlm, hnkm, hk⟩ := exp_ex hlp hn0
  have hom : IsOmT c D.om := ⟨hD.om_pow, fun σ => Ideal.Quotient.eq.1 (hD.om_bar σ)⟩
  obtain ⟨hker1, hker2, -, -, hcc, hunr, -, -⟩ := (omT Ω l c).2 D.om hom
  obtain ⟨mξ, hlξ, hξm⟩ := hD.xi_ord
  have hψn : ∀ g, D.ψ g ^ Fintype.card (ZMod N)ˣ = 1 := by
    intro g
    rw [hpsi]
    show (MulChar.toUnitHom ψ) (Chr.cls ℚ Ω N g) ^ Fintype.card (ZMod N)ˣ = 1
    rw [← map_pow, pow_card_eq_one, map_one]
  have hψk : ∀ g, (∃ m' : ℕ, l.Coprime m' ∧ D.ψ g ^ m' = 1) → D.ψ g ^ k = D.ψ g := by
    rintro g ⟨m', hm', hg⟩
    have hd : orderOf (D.ψ g) ∣ Nat.gcd (Fintype.card (ZMod N)ˣ) m' :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one (hψn g)) (orderOf_dvd_of_pow_eq_one hg)
    conv_rhs => rw [← pow_one (D.ψ g)]
    exact pow_eq_pow_iff_modEq.2 ((hk m' hm').of_dvd hd)
  have hψ1 : D.ψ ^ Fintype.card (ZMod N)ˣ = 1 := MonoidHom.ext fun g => by rw [MonoidHom.pow_apply, hψn g, MonoidHom.one_apply]
  refine ⟨D.om ^ (D.e + 3) * D.ξ * D.ψ ^ k, l * N * p₁ * 2 ^ n', (l - 1) * mξ * m, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Nat.pos_of_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hlp.ne_zero (NeZero.ne N)) (NeZero.ne p₁)) (pow_ne_zero _ two_ne_zero))
  · intro s hs
    have hl' : Chr.cls ℚ Ω l s = 1 := cls_one ⟨N * p₁ * 2 ^ n', by ring⟩ hs
    have hN' : Chr.cls ℚ Ω N s = 1 := cls_one ⟨l * p₁ * 2 ^ n', by ring⟩ hs
    have hp' : Chr.cls ℚ Ω p₁ s = 1 := cls_one ⟨l * N * 2 ^ n', by ring⟩ hs
    have hq' : Chr.cls ℚ Ω (2 ^ n') s = 1 := cls_one ⟨l * N * p₁, by ring⟩ hs
    have h1 : D.om s = 1 := by
      have : s ∈ (Chr.cls ℚ Ω l).ker := hl'
      rw [← hker2] at this
      exact this
    have h2 : D.ξ s = 1 := by
      rw [hxi, MonoidHom.mul_apply]
      simp only [Chr.dirG, MonoidHom.comp_apply, hp', hq', map_one, mul_one]
    have h3 : D.ψ s = 1 := by
      rw [hpsi]
      simp only [Chr.dirG, MonoidHom.comp_apply, hN', map_one]
    simp only [MonoidHom.mul_apply, MonoidHom.pow_apply, h1, h2, h3, one_pow, mul_one]
  · have h : l.Coprime (l - 1) := (Nat.Prime.coprime_iff_not_dvd hlp).2
      (Nat.not_dvd_of_pos_of_lt (Nat.sub_pos_of_lt hlp.one_lt) (Nat.sub_lt hlp.pos one_pos))
    exact Nat.Coprime.mul_right (Nat.Coprime.mul_right h hlξ) hlm
  · obtain ⟨t, ht⟩ := hnkm
    have a1 : (D.om ^ (D.e + 3)) ^ ((l - 1) * mξ * m) = 1 := by
      rw [← pow_mul, show (D.e + 3) * ((l - 1) * mξ * m) = (l - 1) * ((D.e + 3) * mξ * m) by ring, pow_mul,
        hD.om_pow, one_pow]
    have a2 : D.ξ ^ ((l - 1) * mξ * m) = 1 := by
      rw [show (l - 1) * mξ * m = mξ * ((l - 1) * m) by ring, pow_mul, hξm, one_pow]
    have a3 : (D.ψ ^ k) ^ ((l - 1) * mξ * m) = 1 := by
      rw [← pow_mul, show k * ((l - 1) * mξ * m) = Fintype.card (ZMod N)ˣ * (t * ((l - 1) * mξ)) by
        rw [show Fintype.card (ZMod N)ˣ * (t * ((l - 1) * mξ)) = (Fintype.card (ZMod N)ˣ * t) * ((l - 1) * mξ) by ring,
          ← ht]
        ring, pow_mul, hψ1, one_pow]
    rw [mul_pow, mul_pow, a1, a2, a3, mul_one, mul_one]
  · intro σ hσ
    have ho : D.om σ = -1 := hcc σ hσ hl2
    have hx : D.ξ σ = -1 := by
      rw [← hD.xi_odd, hxi]
      simp only [MonoidHom.mul_apply, Chr.dirG, MonoidHom.comp_apply, cyclotomicClass_eq_of_isComplexConj _ hσ hD.isCC]
    have hchi : chiO ℚ Ω l c.O D.cc = -1 := by
      have h := IsConjOm.cyc (E := ℚ) (l := l) (σ := MulSemiringAction.toRingAut (G ℚ Ω) Ω D.cc) hD.isCC
      show Units.map _ (cycZ ℚ Ω l D.cc) = -1
      rw [show cycZ ℚ Ω l D.cc = -1 from h]
      ext
      simp
    have hP := hD.Psi_even
    simp only [Raw.Psi, Chr.Psi, MonoidHom.mul_apply] at hP
    rw [show (chiO ℚ Ω l c.O ^ (D.e : ℤ)) D.cc = (chiO ℚ Ω l c.O D.cc) ^ (D.e : ℤ) from rfl, hchi, zpow_natCast] at hP
    have hψσ : D.ψ σ = (-1) ^ D.e := by
      rw [hpsi] at hP ⊢
      have : Chr.dirG ℚ Ω ψ σ = Chr.dirG ℚ Ω ψ D.cc := by
        simp only [Chr.dirG, MonoidHom.comp_apply, cyclotomicClass_eq_of_isComplexConj _ hσ hD.isCC]
      rw [this]
      rw [← mul_right_inj ((-1 : c.Oˣ) ^ D.e), hP, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
    have hsq : D.ψ σ ^ k = D.ψ σ := hψk σ ⟨2, (Nat.coprime_primes hlp Nat.prime_two).2 hl2,
      by rw [hψσ, ← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]⟩
    simp only [MonoidHom.mul_apply, MonoidHom.pow_apply]
    rw [ho, hx, hsq, hψσ, ← pow_succ, ← pow_add]
    exact Even.neg_one_pow ⟨D.e + 2, by ring⟩
  · intro A hA
    have h1 : Ine A ≤ D.om.ker := hunr A (hA l hD.l_mem)
    have h2 := hD.xi_unr A hA
    have h3 := hD.psi_unr A hA
    intro x hx
    have a1 : D.om x = 1 := h1 hx
    have a2 : D.ξ x = 1 := h2 hx
    have a3 : D.ψ x = 1 := h3 hx
    rw [MonoidHom.mem_ker]
    simp only [MonoidHom.mul_apply, MonoidHom.pow_apply, a1, a2, a3, one_pow, mul_one]
  · intro g hg
    simp only [MonoidHom.mul_apply, MonoidHom.pow_apply]
    rw [hψk g hg]

theorem UpperTheory.V.Ws.Lk.etaEx :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c}, (Ctx2 D ∨ Ctx3 D) → ∃ (η : G ℚ Ω →* (PadicAlgCl l)ˣ) (N m : ℕ), 1 ≤ N ∧ Af.KillsMu N η ∧ l.Coprime m ∧ η ^ m = 1 ∧ (∀ σ, IsCC σ → η σ = 1) ∧ (∀ A, Raw.Away D.S A → Ine (F := ℚ) A ≤ η.ker) ∧ ∀ g, (∃ m' : ℕ, l.Coprime m' ∧ D.ψ g ^ m' = 1) → η g * toQ (D.om ^ (D.e + 3) * D.ξ * D.ψ) g = 1 := by
  intro Ω _ _ _ l _ c D hC
  have key : ∃ (χ : G ℚ Ω →* c.Oˣ) (N m : ℕ), 1 ≤ N ∧ Af.KillsMu N χ ∧ l.Coprime m ∧ χ ^ m = 1 ∧
      (∀ σ, IsCC σ → χ σ = 1) ∧ (∀ A, Raw.Away D.S A → Ine (F := ℚ) A ≤ χ.ker) ∧
      ∀ g, (∃ m' : ℕ, l.Coprime m' ∧ D.ψ g ^ m' = 1) → χ g = (D.om ^ (D.e + 3) * D.ξ * D.ψ) g := by
    rcases hC with ⟨hD, h, t, e, ψ, -, -, -, -, -, hO⟩ | ⟨hD, h, t, e, ψ, -, -, -, -, -, hO⟩
    · exact exists_character_of_dirichlet_data hD hO
    · exact exists_character_of_dirichlet_data hD hO
  obtain ⟨χ, N, m, hN, hK, hm, hχm, hcc, hA, hg⟩ := key
  have hval : ∀ g, (toQ χ)⁻¹ g = (Units.map (algebraMap c.O (PadicAlgCl l) : c.O →* PadicAlgCl l) (χ g))⁻¹ :=
    fun g => rfl
  refine ⟨(toQ χ)⁻¹, N, m, hN, ?_, hm, ?_, ?_, ?_, ?_⟩
  · intro s hs
    rw [hval, hK s hs, map_one, inv_one]
  · ext g
    rw [MonoidHom.pow_apply, hval, inv_pow, ← map_pow, ← MonoidHom.pow_apply, hχm]
    simp
  · intro σ hσ
    rw [hval, hcc σ hσ, map_one, inv_one]
  · intro A hAw x hx
    have h1 : χ x = 1 := hA A hAw hx
    rw [MonoidHom.mem_ker, hval, h1, map_one, inv_one]
  · intro g hg'
    rw [hval, show toQ (D.om ^ (D.e + 3) * D.ξ * D.ψ) g =
      Units.map (algebraMap c.O (PadicAlgCl l) : c.O →* PadicAlgCl l) ((D.om ^ (D.e + 3) * D.ξ * D.ψ) g) from rfl,
      ← hg g hg', inv_mul_cancel]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.HalfEx
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

private theorem norm_algebraMap_padicInt_padicAlgCl {l : ℕ} [Fact l.Prime] (a : ℤ_[l]) :
    ‖algebraMap ℤ_[l] (PadicAlgCl l) a‖ = ‖a‖ := by
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), PadicAlgCl.norm_extends]
  rfl

private theorem norm_le_one_of_isIntegral_padicInt' {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) :
    ‖x‖ ≤ 1 := by
  obtain ⟨p, hm, hp⟩ := hx
  by_contra h
  push_neg at h
  have hd0 : p.natDegree ≠ 0 := by
    intro h0
    have h1 := Polynomial.eq_one_of_monic_natDegree_zero hm h0
    subst h1
    simp at hp
  obtain ⟨m, hmdeg⟩ : ∃ m, p.natDegree = m + 1 := ⟨p.natDegree - 1, by omega⟩
  have hc : p.coeff (m + 1) = 1 := by
    rw [← hmdeg]
    exact Polynomial.Monic.coeff_natDegree hm
  rw [Polynomial.eval₂_eq_sum_range, hmdeg, Finset.sum_range_succ, hc, map_one, one_mul] at hp
  have hsum : ‖∑ i ∈ Finset.range (m + 1), (algebraMap ℤ_[l] (PadicAlgCl l)) (p.coeff i) * x ^ i‖
      ≤ ‖x‖ ^ m := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
    intro i hi
    rw [norm_mul, norm_pow]
    have h1 : ‖(algebraMap ℤ_[l] (PadicAlgCl l)) (p.coeff i)‖ ≤ 1 := by
      rw [norm_algebraMap_padicInt_padicAlgCl]
      exact PadicInt.norm_le_one _
    have h2 : ‖x‖ ^ i ≤ ‖x‖ ^ m :=
      pow_le_pow_right₀ h.le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
    calc _ ≤ 1 * ‖x‖ ^ m := mul_le_mul h1 h2 (by positivity) zero_le_one
      _ = _ := one_mul _
  have heq : x ^ (m + 1) =
      -∑ i ∈ Finset.range (m + 1), (algebraMap ℤ_[l] (PadicAlgCl l)) (p.coeff i) * x ^ i := by
    linear_combination hp
  have hn := congrArg norm heq
  rw [norm_neg, norm_pow] at hn
  have h3 : ‖x‖ ^ (m + 1) ≤ ‖x‖ ^ m := hn ▸ hsum
  have h4 : ‖x‖ ^ m < ‖x‖ ^ (m + 1) := pow_lt_pow_right₀ h (Nat.lt_succ_self m)
  linarith

private theorem norm_coe_padicAlgCl_coefO_le_one {l : ℕ} [Fact l.Prime] (c : Coef l) (x : c.O) :
    ‖(x : PadicAlgCl l)‖ ≤ 1 := by
  haveI := c.fin
  haveI : Algebra.IsIntegral ℤ_[l] c.O := Algebra.IsIntegral.of_finite ℤ_[l] c.O
  exact norm_le_one_of_isIntegral_padicInt' _ ((Algebra.IsIntegral.isIntegral x).map c.O.val)

private theorem norm_natCast_prime_padicAlgCl_eq_inv {l : ℕ} [Fact l.Prime] : ‖(l : PadicAlgCl l)‖ = (l : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℤ_[l] (PadicAlgCl l)) l, norm_algebraMap_padicInt_padicAlgCl, PadicInt.norm_p]

private theorem norm_coe_lt_one_of_mem_maximalIdeal_coefO {l : ℕ} [Fact l.Prime] (c : Coef l) (x : c.O)
    (hx : x ∈ IsLocalRing.maximalIdeal c.O) : ‖(x : PadicAlgCl l)‖ < 1 := by
  haveI := c.dvr
  have hcast : ((l : c.O) : PadicAlgCl l) = (l : PadicAlgCl l) := by simp
  have hl : ‖((l : c.O) : PadicAlgCl l)‖ = (l : ℝ)⁻¹ := by rw [hcast, norm_natCast_prime_padicAlgCl_eq_inv]
  have hlt : (l : ℝ)⁻¹ < 1 :=
    inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  have hl0 : (l : c.O) ≠ 0 := by
    intro h0
    have hne : (l : ℝ)⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero)
    rw [h0, ZeroMemClass.coe_zero, norm_zero] at hl
    exact hne hl.symm
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible c.O
  have hL : Ideal.span {(l : c.O)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact hl0
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hL hϖ
  have hdvd : ϖ ∣ x := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer] at hϖ
    rw [hϖ, Ideal.mem_span_singleton] at hx
    exact hx
  have hxn : x ^ n ∈ Ideal.span {(l : c.O)} := by
    rw [hn, Ideal.mem_span_singleton]
    exact pow_dvd_pow_of_dvd hdvd n
  rw [Ideal.mem_span_singleton] at hxn
  obtain ⟨y, hy⟩ := hxn
  have hy' : (x : PadicAlgCl l) ^ n = ((l : c.O) : PadicAlgCl l) * (y : PadicAlgCl l) := by
    have h5 := congrArg (fun z : c.O => (z : PadicAlgCl l)) hy
    simpa using h5
  have hnorm : ‖(x : PadicAlgCl l)‖ ^ n < 1 := by
    rw [← norm_pow, hy', norm_mul, hl]
    calc (l : ℝ)⁻¹ * ‖(y : PadicAlgCl l)‖ ≤ (l : ℝ)⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left (norm_coe_padicAlgCl_coefO_le_one c y) (by positivity)
      _ < 1 := by rw [mul_one]; exact hlt
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · rw [h0, pow_zero] at hnorm
    exact absurd hnorm (lt_irrefl 1)
  · exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) hpos.ne').mp hnorm

private theorem norm_pow_sub_one_le_of_norm_sub_one_lt_one {l : ℕ} [Fact l.Prime] (z : PadicAlgCl l) (h : ‖z - 1‖ < 1) (i : ℕ) :
    ‖z ^ i - 1‖ ≤ ‖z - 1‖ := by
  have hz1 : ‖z‖ ≤ 1 := by
    have h1 := IsUltrametricDist.norm_add_le_max (z - 1) 1
    rw [sub_add_cancel, norm_one] at h1
    exact h1.trans (max_le h.le le_rfl)
  rw [← geom_sum_mul, norm_mul, mul_comm]
  have h2 : ‖∑ j ∈ Finset.range i, z ^ j‖ ≤ 1 := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
    intro j _
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) hz1
  calc ‖z - 1‖ * ‖∑ j ∈ Finset.range i, z ^ j‖ ≤ ‖z - 1‖ * 1 :=
        mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ = ‖z - 1‖ := mul_one _

private theorem padicAlgCl_eq_one_of_pow_eq_one_of_norm_sub_one_lt_one {l : ℕ} [Fact l.Prime] (z : PadicAlgCl l) (m : ℕ)
    (hm : ‖(m : PadicAlgCl l)‖ = 1) (hz : z ^ m = 1) (h : ‖z - 1‖ < 1) : z = 1 := by
  have hS : ∑ i ∈ Finset.range m, z ^ i =
      (m : PadicAlgCl l) + ∑ i ∈ Finset.range m, (z ^ i - 1) := by
    rw [Finset.sum_sub_distrib]
    simp
  have hsmall : ‖∑ i ∈ Finset.range m, (z ^ i - 1)‖ < 1 :=
    lt_of_le_of_lt (IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _)
      (fun i _ => norm_pow_sub_one_le_of_norm_sub_one_lt_one z h i)) h
  have hSn : ‖∑ i ∈ Finset.range m, z ^ i‖ = 1 := by
    rw [hS, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hm]; exact hsmall.ne'), hm]
    exact max_eq_left hsmall.le
  have hprod : (∑ i ∈ Finset.range m, z ^ i) * (z - 1) = 0 := by
    rw [geom_sum_mul, hz, sub_self]
  rcases mul_eq_zero.mp hprod with h0 | h0
  · rw [h0, norm_zero] at hSn
    exact absurd hSn zero_ne_one
  · exact sub_eq_zero.mp h0

private theorem norm_padicInt_unit_pow_pred_sub_one_lt_one {l : ℕ} [Fact l.Prime] (u : ℤ_[l]ˣ) :
    ‖(u : ℤ_[l]) ^ (l - 1) - 1‖ < 1 := by
  have hmem : (u : ℤ_[l]) ^ (l - 1) - 1 ∈ RingHom.ker (PadicInt.toZMod (p := l)) := by
    rw [RingHom.mem_ker, RingHom.map_sub, map_pow, map_one]
    have hne : PadicInt.toZMod (u : ℤ_[l]) ≠ 0 := ((u.isUnit).map PadicInt.toZMod).ne_zero
    rw [ZMod.pow_card_sub_one_eq_one hne, sub_self]
  rw [PadicInt.ker_toZMod] at hmem
  exact PadicInt.mem_nonunits.mp ((IsLocalRing.mem_maximalIdeal _).mp hmem)

private theorem norm_natCast_prime_sub_one_padicAlgCl_eq_one {l : ℕ} [Fact l.Prime] : ‖((l - 1 : ℕ) : PadicAlgCl l)‖ = 1 := by
  have hl1 : 1 ≤ l := (Fact.out : l.Prime).one_lt.le
  have hlt : (l : ℝ)⁻¹ < 1 :=
    inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  rw [Nat.cast_sub hl1, Nat.cast_one, sub_eq_neg_add,
    IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
      (by rw [norm_neg, norm_one, norm_natCast_prime_padicAlgCl_eq_inv]; exact hlt.ne'),
    norm_neg, norm_one, norm_natCast_prime_padicAlgCl_eq_inv]
  exact max_eq_left hlt.le

private theorem sq_mul_eq_of_pow_two_mul_pred_eq_of_norm_sub_lt_one {l : ℕ} [Fact l.Prime] (b w y : PadicAlgCl l) (hb : ‖b - 1‖ < 1)
    (hw : w ^ (l - 1) = 1) (hw1 : ‖w‖ ≤ 1) (hwy : ‖w - y‖ < 1) (hy1 : ‖y‖ = 1)
    (hbn : b ^ (2 * (l - 1)) = y ^ (l - 1)) : b ^ 2 * w = y := by
  have hy0 : y ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hy1
    exact zero_ne_one hy1
  have hb1 : ‖b ^ 2 - 1‖ < 1 := lt_of_le_of_lt (norm_pow_sub_one_le_of_norm_sub_one_lt_one b hb 2) hb
  have hz : (b ^ 2 * w * y⁻¹) ^ (l - 1) = 1 := by
    rw [mul_pow, mul_pow, ← pow_mul, hbn, hw, mul_one, inv_pow,
      mul_inv_cancel₀ (pow_ne_zero _ hy0)]
  have hyi : ‖y⁻¹‖ = 1 := by rw [norm_inv, hy1, inv_one]
  have hz1 : ‖b ^ 2 * w * y⁻¹ - 1‖ < 1 := by
    have hyy : y * y⁻¹ = 1 := mul_inv_cancel₀ hy0
    have hsplit : b ^ 2 * w * y⁻¹ - 1 = (b ^ 2 - 1) * w * y⁻¹ + (w - y) * y⁻¹ := by
      linear_combination hyy
    rw [hsplit]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
    · rw [norm_mul, norm_mul, hyi, mul_one]
      calc ‖b ^ 2 - 1‖ * ‖w‖ ≤ ‖b ^ 2 - 1‖ * 1 := mul_le_mul_of_nonneg_left hw1 (norm_nonneg _)
        _ < 1 := by rw [mul_one]; exact hb1
    · rw [norm_mul, hyi, mul_one]
      exact hwy
  exact (mul_inv_eq_one₀ hy0).mp (padicAlgCl_eq_one_of_pow_eq_one_of_norm_sub_one_lt_one _ (l - 1) norm_natCast_prime_sub_one_padicAlgCl_eq_one hz hz1)

private theorem coe_cycBar_eq_algebraMap_cycZ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]
    (g : G ℚ Ω) :
    ((cycBar ℚ Ω l g : (PadicAlgCl l)ˣ) : PadicAlgCl l) =
      algebraMap ℤ_[l] (PadicAlgCl l) (cycZ ℚ Ω l g : ℤ_[l]) := rfl

private theorem coe_toQ_apply {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]
    {c : Coef l} (om : G ℚ Ω →* (↥c.O)ˣ) (g : G ℚ Ω) :
    ((toQ om g : (PadicAlgCl l)ˣ) : PadicAlgCl l) = ((om g : c.O) : PadicAlgCl l) := rfl

private theorem coe_chiO_eq_algebraMap_cycZ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]
    {c : Coef l} (g : G ℚ Ω) :
    ((chiO ℚ Ω l c.O g : c.O) : PadicAlgCl l) =
      algebraMap ℤ_[l] (PadicAlgCl l) (cycZ ℚ Ω l g : ℤ_[l]) := rfl

private theorem sub_chiO_mem_maximalIdeal_of_bar_eq {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]
    {c : Coef l} (om : G ℚ Ω →* (↥c.O)ˣ) (g : G ℚ Ω)
    (h : Raw.bar om g = Raw.bar (chiO ℚ Ω l c.O) g) :
    (om g : c.O) - (chiO ℚ Ω l c.O g : c.O) ∈ IsLocalRing.maximalIdeal c.O :=
  (Ideal.Quotient.eq (I := IsLocalRing.maximalIdeal c.O)).mp h

theorem UpperTheory.V.Ws.Lk.halfEx :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c}, D.Good → ∃ γ : G ℚ Ω →* (PadicAlgCl l)ˣ, Continuous γ ∧ (∀ g, ‖(γ g : PadicAlgCl l) - 1‖ < 1) ∧ (∀ g, γ g ^ 2 * toQ D.om g = cycBar ℚ Ω l g) ∧ (cycZ ℚ Ω l).ker ≤ γ.ker := by
  intro Ω _ _ _ l _ c D hD
  have hl2 : l ≠ 2 := hD.l_odd
  have hlp : l.Prime := Fact.out
  obtain ⟨π, hπapp⟩ : ∃ π : G ℚ Ω →* ℤ_[l]ˣ, ∀ g, π g = (cycZ ℚ Ω l g) ^ (l - 1) :=
    ⟨(cycZ ℚ Ω l) ^ (l - 1), fun g => rfl⟩
  have hπc : Continuous π := by
    have hfun : (⇑π) = fun g => (cycZ ℚ Ω l g) ^ (l - 1) := funext hπapp
    rw [hfun]
    exact (continuous_cycZ ℚ Ω l).pow _
  have hπn : ∀ s, ‖((π s : ℤ_[l]ˣ) : ℤ_[l]) - 1‖ < 1 := by
    intro s
    rw [hπapp, Units.val_pow_eq_pow_val]
    exact norm_padicInt_unit_pow_pred_sub_one_lt_one _
  have hn : 0 < 2 * (l - 1) := by
    have := hlp.two_le
    omega
  obtain ⟨t, β, c₁, htc, htk, htβ, hβc, hβ1, hβn, -⟩ :=
    Tw.rootChar l hl2 (G ℚ Ω) π hπc hπn (2 * (l - 1)) hn
  refine ⟨β, hβc, fun g => (hβ1 g).2, ?_, ?_⟩
  · intro g
    apply Units.ext
    rw [Units.val_mul, Units.val_pow_eq_pow_val, coe_cycBar_eq_algebraMap_cycZ, coe_toQ_apply]
    apply sq_mul_eq_of_pow_two_mul_pred_eq_of_norm_sub_lt_one (l := l) _ _ _ (hβ1 g).2
    · have h := congrArg (fun f : G ℚ Ω →* (↥c.O)ˣ => ((f g : c.O) : PadicAlgCl l)) hD.om_pow
      simpa using h
    · exact norm_coe_padicAlgCl_coefO_le_one c _
    · have h := norm_coe_lt_one_of_mem_maximalIdeal_coefO c _ (sub_chiO_mem_maximalIdeal_of_bar_eq D.om g (hD.om_bar g))
      rw [AddSubgroupClass.coe_sub, coe_chiO_eq_algebraMap_cycZ] at h
      exact h
    · rw [norm_algebraMap_padicInt_padicAlgCl]
      exact PadicInt.isUnit_iff.mp (Units.isUnit _)
    · rw [hβn g, hπapp, Units.val_pow_eq_pow_val, map_pow]
  · intro g hg
    apply htβ
    rw [htk, MonoidHom.mem_ker, hπapp, (MonoidHom.mem_ker).mp hg, one_pow]
end
