module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ReframeSt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WithISelf
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomTransport

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLogFrame
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch

noncomputable section
namespace GlobalTheory.Ex.Arch

section Generic
variable {O : Type} [CommRing O] [StarRing O]


omit [StarRing O] in
theorem exists_lift_ct [IsDedekindDomain O] [Module.Finite ℤ O] {V G X : Type} [AddCommGroup V] [Module ℂ V] [CommGroup G]
    [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [Module O X] (F : O →+* Module.End ℂ V) (ex : V → G)
    (hadd : ∀ z w, ex (z + w) = ex z * ex w) (hs : Function.Surjective ex) (c : X → G)
    (hc : ∀ x y, c (x + y) = c x * c y) (hl : ∀ (a : O) x z, ex z = c x → ex (F a z) = c (a • x)) :
    ∃ ct : X →+ V, (∀ (a : O) x, ct (a • x) = F a (ct x)) ∧ ∀ x, c x = ex (ct x) := by
  let _ : Module O V := Module.compHom V F
  have e0 : ex 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have c0 : c 0 = 1 := by
    have := hc 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  let P : Submodule O (X × V) :=
    { carrier := {p | ex p.2 = c p.1}
      zero_mem' := e0.trans c0.symm
      add_mem' := fun {p q} hp hq => by
        change ex (p.2 + q.2) = c (p.1 + q.1)
        rw [hadd, hc, (show ex p.2 = _ from hp), (show ex q.2 = _ from hq)]
      smul_mem' := fun a p hp => hl a p.1 p.2 hp }
  obtain ⟨g, hg⟩ := GlobalTheory.Forms.exists_linearMap_lift_of_int (LinearMap.fst O X V ∘ₗ P.subtype)
    (fun x => by
      obtain ⟨z, hz⟩ := hs (c x)
      exact ⟨⟨(x, z), hz⟩, rfl⟩) LinearMap.id
  refine ⟨(LinearMap.snd O X V ∘ₗ P.subtype ∘ₗ g).toAddMonoidHom,
    fun a x => (LinearMap.snd O X V ∘ₗ P.subtype ∘ₗ g).map_smul a x, fun x => ?_⟩
  have h1 : (g x).1.1 = x := hg x
  have h2 : ex (g x).1.2 = c (g x).1.1 := (g x).2
  rw [h1] at h2
  exact h2.symm

theorem exists_log_frame [IsDedekindDomain O] [Module.Finite ℤ O] [Module.Free ℤ O] {N : NumD ℂ} {B : AnArc O}
    {ex : (Fin B.gB → ℂ) → N.A} {fr : (Fin B.gB → ℂ) → ℂˣ} {th : (Fin B.gB → ℂ) → ℂ} (hab : IsAbFrame N.toNumB B ex fr th)
    {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [Module O X] (e : X ≃+ N.X)
    (ct : X →+ (Fin B.gB → ℂ)) (hc : ∀ x, N.c (e x) = ex (ct x)) {w : O} (hw : w + star w = 1)
    (hbal : ∀ (a : O) y x, (N.τ (e (a • y)) (e x) : ℂ) * fr (ct (a • y) + ct x) * fr (ct y) * fr (ct (star a • x)) =
      N.τ (e y) (e (star a • x)) * fr (ct y + ct (star a • x)) * fr (ct (a • y)) * fr (ct x)) :
    ∃ T : X →+ X →+ ℂ, (∀ x y, T x y = T y x) ∧ (∀ (a : O) y x, T (a • y) x = T y (star a • x)) ∧
      ∀ x y, eTwoPi (T x y) * fr (ct x) * fr (ct y) = N.τ (e x) (e y) * fr (ct x + ct y) := by
  have := GlobalTheory.Forms.projective_of_int O X
  have : Module.Finite O X := Module.Finite.of_restrictScalars_finite ℤ O X
  obtain ⟨T, h1, h2, h3⟩ := GlobalTheory.Forms.exists_log_of_bimul hw
    (fun x y : X => N.τ (e x) (e y) * fr (ct x + ct y) / fr (ct x) / fr (ct y))
    (fun y x x' => by
      have a := congrArg Additive.ofMul (N.τ_add_right (e y) (e x) (e x'))
      have b := congrArg Additive.ofMul (hab.2.2.2.2.2.1 (ct x) (ct x') (ct y))
      apply Additive.ofMul.injective
      simp only [hc, map_add (f := _), add_comm (ct y), ofMul_mul, ofMul_div] at a b ⊢
      linear_combination (norm := abel) a - b)
    (fun y x => by rw [N.τ_symm, add_comm, div_right_comm])
    (fun a y x => by
      have b := hbal a y x
      simp only [← Units.val_mul, Units.val_inj] at b
      replace b := congrArg Additive.ofMul b
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_div] at b ⊢
      linear_combination (norm := abel) b)
  refine ⟨AddMonoidHom.mk' (fun x => (T x).toAddMonoidHom) fun x y => by ext; simp, h1, h2, fun x y => ?_⟩
  change Complex.exp (2 * Real.pi * Complex.I * T x y) * _ * _ = _
  rw [← h3]
  simp only [← Units.val_mul, Units.val_inj]
  rw [mul_right_comm, div_mul_cancel, div_mul_cancel]

end Generic

theorem dict_of_val : BrActSt → ValSt → DictSt := by
  intro hBr hVal E _ _ _ H D R _ _ _ A k β hβ
  let _ := H.starRing
  obtain ⟨B, ex, fr, th, hab, hth, hchi, hsig, hF, hros, hprim⟩ := hVal E H D R A
  have := A.closed
  obtain ⟨b1, b2, b3⟩ := hBr R A.D₀ A.even A.bimult ℂ A.N A.ν (𝓞 E) A.oa
  have := A.D₀.freeX
  have := A.D₀.finX
  set e : A.D₀.X ≃+ A.N.X := A.ν.eX.symm with he
  have hee : ∀ x, A.ν.eX (e x) = x := A.ν.eX.apply_symm_apply
  have hw : H.w0 + star H.w0 = 1 := by
    show H.w0 + H.bar H.w0 = 1
    rw [GlobalTheory.HostModel.cmHost_bar_halfIntegerGenerator, add_sub_cancel]
  obtain ⟨ct, hct, hc⟩ := exists_lift_ct B.F ex hab.1 hab.2.1 (fun x : A.D₀.X => A.N.c (e x))
    (fun x y => by rw [map_add (f := _), A.N.c_add]) (fun a x z hz => A.ν.eA.injective (by
      rw [hF, hz, A.ν.c_eq, A.ν.c_eq, hee, hee, DegPre.cF, DegPre.cF, A.oa.c_lin, Category.assoc]))
  obtain ⟨T, hT1, hT2, hT⟩ := exists_log_frame hab e ct hc hw (fun a y x => by
    obtain ⟨r, hr, h⟩ := b1 a
    have h1 := h (e y) (e x)
    have h2 := hros a (star a) r hr (ct y) (ct x)
    rw [hee, hee, hc, hc] at h1
    rw [← h1, hct, hct]
    linear_combination -(A.N.τ (e (a • y)) (e x) : ℂ) * h2)
  have hact : ∀ (a : 𝓞 E) x, e (a • x) = A.act a (e x) := fun a x => by rw [ArcF.act, hee]
  let B' : An H :=
    { B with
      X := A.D₀.X
      acg := inferInstance
      free := inferInstance
      fin := inferInstance
      mod := inferInstance
      ct := ct
      ct_smul := hct
      T := T
      T_symm := hT1
      T_adj := hT2
      psi := fun x => A.N.ψ (e x) * fr (ct x)
      psi_neg := fun x => by
        rw [map_neg, map_neg, ← hab.2.2.2.2.2.2.1, ← hc, ← _root_.mul_assoc, A.N.even]
      psi_add := fun x y => by
        have h := hT x y
        rw [map_add (f := _), map_add (f := _), A.N.ψ_add]
        push_cast
        linear_combination -(A.N.ψ (e x) : ℂ) * A.N.ψ (e y) * h
      be := β.be.comp e.toIntLinearEquiv.toLinearMap e.toIntLinearEquiv.toLinearMap
      be_symm := fun x y => β.symm _ _
      be_pos := fun x hx => β.pos _ fun h => hx (e.map_eq_zero_iff.1 h)
      be_adj := fun a y x => by
        change β.be (e (a • y)) (e x) = β.be (e y) (e (star a • x))
        rw [hact, hact]
        exact hβ a _ _
      be_even := fun x => (dvd_mul_right 2 (k : ℤ)).trans (β.dvd _ _) }
  have hab' : IsAbFrame A.N.toNumB B' ex fr th := by
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := hab
    refine ⟨a1, a2, a3, a4, a5, a6, a7, ⟨a8.1, fun l z => ?_⟩, a9⟩
    have := a8.2 l z
    rw [map_zero] at this ⊢
    exact this
  refine ⟨B', ⟨e, ex, fr, th, hab', hc, fun _ => rfl⟩, ⟨hact, ?_⟩, fun _ _ => rfl, ⟨hw, hchi, fun y => ?_⟩, hth, hsig⟩
  · rintro a g g' c c' v hg hg' hgg ⟨hv1, hv2⟩
    obtain ⟨r, hr, h⟩ := b2 a
    obtain ⟨h1, h2⟩ := h g g' c c' hg hg' hgg
    change c.b = ex v.2 at hv1
    refine ⟨A.ν.eA.injective (by rw [h1, hv1]; exact (hF a v.2).symm), fun x : A.D₀.X => ?_⟩
    have h3 := h2 (e x)
    have h4 : (c.s (e (star a • x)) : ℂ) * fr (ct (star a • x) + v.2) =
      eTwoPi (v.1 (star a • x)) * fr (ct (star a • x)) * fr v.2 := hv2 (star a • x)
    have h5 := hros (star a) a r hr (ct x) v.2
    rw [hee, hc, hv1] at h3
    rw [hct] at h4
    change (c'.s (e x) : ℂ) * fr (ct x + B.F a v.2) = eTwoPi (v.1 (star a • x)) * fr (ct x) * fr (B.F a v.2)
    refine mul_right_cancel₀ (mul_ne_zero (fr (B.F (star a) (ct x))).ne_zero (fr v.2).ne_zero) ?_
    rw [h3]
    linear_combination (c.s (e (star a • x)) : ℂ) * h5 + (fr (ct x) : ℂ) * fr (B.F a v.2) * h4
  · obtain ⟨t, ht, h⟩ := b3 H.w0 A.w0
    have h1 := h (e y)
    have h2 := hprim t ht (ct y)
    have h3 := hT y (H.w0 • y)
    rw [hee, hc] at h1
    rw [hct] at h3
    change ((A.N.ψ (e y) * fr (ct y) : ℂˣ) : ℂ) = eTwoPi (T y (H.w0 • y))
    refine mul_right_cancel₀ (mul_ne_zero (fr (ct y)).ne_zero (fr (B.F H.w0 (ct y))).ne_zero) ?_
    rw [Units.val_mul, ← h1]
    linear_combination (A.N.τ (e y) (e (H.w0 • y)) : ℂ) * h2 - h3

end GlobalTheory.Ex.Arch
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsValuedFieldValuationCentreLePow
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteAlgClosedFieldCentredAtPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteAlgClosedFieldCentredAtPrime
namespace GlobalTheory.Ex

theorem exists_complete_isAlgClosed_centred_at_prime :
    ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [FaithfulSMul R K] [Algebra.IsAlgebraic R K] (P : Ideal R), P.IsPrime → P ≠ ⊥ → ∃ (C : Type) (_ : NontriviallyNormedField C) (_ : IsUltrametricDist C) (_ : CompleteSpace C) (_ : IsAlgClosed C) (gam : K →+* C), (∀ r, ‖gam (algebraMap R K r)‖ ≤ 1) ∧ ∀ r ∈ P, ‖gam (algebraMap R K r)‖ < 1 := by
  intro R K _ _ _ _ _ _ _ P hP hP0
  obtain ⟨O, _, _, _, _, φ, hker, hcom⟩ :=
    GlobalTheory.exists_complete_discreteValuationRing_of_prime_lt (⊥ : Ideal R) P (bot_lt_iff_ne_bot.2 hP0)
  have hφ : Function.Injective φ := (RingHom.injective_iff_ker_eq_bot φ).2 hker
  obtain ⟨C, i1, i2, i3, i4, i5, -, -, h1, h2⟩ :=
    GlobalTheory.Ex.exists_complete_isAlgClosed_cExt O (FractionRing O)
  let ψ : R →+* C := (algebraMap (FractionRing O) C).comp ((algebraMap O (FractionRing O)).comp φ)
  have hψ : Function.Injective ψ :=
    (algebraMap (FractionRing O) C).injective.comp
      ((IsFractionRing.injective O (FractionRing O)).comp hφ)
  letI : Algebra R C := ψ.toAlgebra
  haveI : FaithfulSMul R C := (faithfulSMul_iff_algebraMap_injective R C).2 hψ
  let g : K →ₐ[R] C := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hg : ∀ r, g.toRingHom (algebraMap R K r) = ψ r := fun r => g.commutes r
  refine ⟨C, i1, i2, i3, i4, g.toRingHom, fun r => ?_, fun r hr => ?_⟩
  · rw [hg]
    exact h1 (φ r)
  · rw [hg]
    exact h2 (φ r) (by rw [← hcom] at hr; exact hr)

end GlobalTheory.Ex
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteAlgClosedFieldCentredAtPrimeStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complete_algClosed_field_centred_at_prime : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [FaithfulSMul R K] [Algebra.IsAlgebraic R K] (P : Ideal R), P.IsPrime → P ≠ ⊥ → ∃ (C : Type) (_ : NontriviallyNormedField C) (_ : IsUltrametricDist C) (_ : CompleteSpace C) (_ : IsAlgClosed C) (gam : K →+* C), (∀ r, ‖gam (algebraMap R K r)‖ ≤ 1) ∧ ∀ r ∈ P, ‖gam (algebraMap R K r)‖ < 1 := by
  first | exact @GlobalTheory.Ex.exists_complete_isAlgClosed_centred_at_prime | exact GlobalTheory.Ex.exists_complete_isAlgClosed_centred_at_prime | (intros; apply GlobalTheory.Ex.exists_complete_isAlgClosed_centred_at_prime <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsValuedFieldValuationCentreLePow
namespace GlobalTheory

theorem exists_valuedField_centred_subalgebra (R K : Type) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [Field K] [Algebra R K] [FaithfulSMul R K] [Algebra.IsAlgebraic R K]
    (u : R) (hu : u ≠ 0) (A : Subalgebra R K) (hA : A.FG) (P : Ideal A) (hP : P.IsPrime)
    (huP : algebraMap R A u ∈ P) :
    ∃ (C : Type) (_ : NontriviallyNormedField C) (_ : IsUltrametricDist C) (_ : CompleteSpace C)
      (_ : IsAlgClosed C) (gam : K →+* C), (∀ x ∈ A, ‖gam x‖ ≤ 1) ∧
        ∀ x : A, x ∈ P → ‖gam (x : K)‖ < 1 := by
  have hinjK : Function.Injective (algebraMap R K) := FaithfulSMul.algebraMap_injective R K
  have hinj : Function.Injective (algebraMap R A) := by
    intro a b hab
    apply hinjK
    have := congrArg (fun x : A => (x : K)) hab
    simpa using this
  haveI : IsNoetherianRing A := isNoetherianRing_of_fg hA
  haveI : Algebra.IsAlgebraic A K := Algebra.IsAlgebraic.extendScalars hinj
  haveI : FaithfulSMul A K :=
    (faithfulSMul_iff_algebraMap_injective A K).2 Subtype.val_injective
  have hne : P ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at huP
    exact hu (hinj (by rw [huP, map_zero]))
  obtain ⟨C, i1, i2, i3, i4, gam, h1, h2⟩ := GlobalTheory.T.exists_complete_algClosed_field_centred_at_prime A K P hP hne
  exact ⟨C, i1, i2, i3, i4, gam, fun x hx => h1 ⟨x, hx⟩, fun x hx => h2 x hx⟩

theorem exists_valuedField_centre_le_pow : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R] [Field K] [Algebra R K] [FaithfulSMul R K] [Algebra.IsAlgebraic R K] (u : R), u ∈ IsLocalRing.maximalIdeal R → u ≠ 0 → ∀ R₁ : Subalgebra R K, Module.Finite R R₁ → ∀ S : ValuationSubring K, (∀ r, algebraMap R K r ∈ S) → ∀ e : ℕ, ∃ (C : Type) (_ : NontriviallyNormedField C) (_ : IsUltrametricDist C) (_ : CompleteSpace C) (_ : IsAlgClosed C) (gam : K →+* C), (∀ r, ‖gam (algebraMap R K r)‖ ≤ 1) ∧ ‖gam (algebraMap R K u)‖ < 1 ∧ ∀ f ∈ R₁, S.valuation f < 1 → ‖gam f‖ < 1 ∧ (S.valuation (algebraMap R K u) = 1 → ‖gam f‖ ≤ ‖gam (algebraMap R K u)‖ ^ e) := by
  intro R K _ _ _ _ _ _ _ _ u hum hu R₁ hfin S hS e
  have hinjK : Function.Injective (algebraMap R K) := FaithfulSMul.algebraMap_injective R K
  have hR : ∀ r, S.valuation (algebraMap R K r) ≤ 1 := fun r =>
    (S.valuation_le_one_iff _).2 (hS r)
  have hR₁ : ∀ x ∈ R₁, S.valuation x ≤ 1 := by
    intro x hx
    have hint : IsIntegral R x := by
      have h := (Algebra.IsIntegral.isIntegral (R := R) (⟨x, hx⟩ : R₁)).map R₁.val
      simpa using h
    letI : Algebra R S := ((algebraMap R K).codRestrict S.toSubring hS).toAlgebra
    haveI : IsScalarTower R S K := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have hint' : IsIntegral S x := hint.tower_top
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := S) (K := K)).1 hint'
    rw [← hy]
    exact (S.valuation_le_one_iff _).2 y.2
  have hfg : (Subalgebra.toSubmodule R₁).FG := Module.Finite.iff_fg.1 hfin
  let q : Ideal R₁ :=
    { carrier := {x | S.valuation (x : K) < 1}
      add_mem' := fun {a b} ha hb => by
        simpa using S.valuation.map_add_lt ha hb
      zero_mem' := by simp
      smul_mem' := fun c x hx => by
        have hx' : S.valuation (x : K) < 1 := hx
        show S.valuation ((c : K) * (x : K)) < 1
        rw [map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (hR₁ _ c.2)) hx' }
  have hq : ∀ x : R₁, x ∈ q ↔ S.valuation (x : K) < 1 := fun _ => Iff.rfl
  have hqp : q.IsPrime := by
    refine ⟨?_, ?_⟩
    · rw [Ideal.ne_top_iff_one, hq]; simp
    · intro a b hab
      by_contra hcon
      rw [not_or, hq, hq, not_lt, not_lt] at hcon
      rw [hq, Subalgebra.coe_mul, map_mul, le_antisymm (hR₁ _ a.2) hcon.1,
        le_antisymm (hR₁ _ b.2) hcon.2] at hab
      simp at hab
  by_cases hv : S.valuation (algebraMap R K u) = 1
  ·
    set U : K := algebraMap R K u with hU
    have hU0 : U ≠ 0 := fun h => hu (hinjK (by rw [← hU, h, map_zero]))
    let Q : Submodule R K := (q.restrictScalars R).map R₁.val.toLinearMap
    have hQ : Q.FG := by
      haveI : IsNoetherian R R₁ := isNoetherian_of_isNoetherianRing_of_finite R R₁
      exact Submodule.FG.map _ (IsNoetherian.noetherian _)
    let N : Submodule R K := Subalgebra.toSubmodule R₁ ⊔
      Q.map (LinearMap.mulRight R (U ^ (e + 1))⁻¹)
    have hN : N.FG := Submodule.FG.sup hfg (hQ.map _)
    let A : Subalgebra R K := Algebra.adjoin R (N : Set K)
    have hA : A.FG := by
      obtain ⟨s, hs⟩ := hN
      refine ⟨s, ?_⟩
      show _ = Algebra.adjoin R (N : Set K)
      rw [← hs, Algebra.adjoin_span]
    have hinv : ∀ x ∈ A, ∃ a ∈ R₁, S.valuation (x - a) < 1 := by
      intro x hx
      induction hx using Algebra.adjoin_induction with
      | mem x hx =>
        obtain ⟨a, ha, _, ⟨_, ⟨g, hg, rfl⟩, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hx
        refine ⟨a, ha, ?_⟩
        have hg' : S.valuation (g : K) < 1 := hg
        simpa [hv] using hg'
      | algebraMap r => exact ⟨_, R₁.algebraMap_mem r, by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨a, ha, hx⟩ := hx
        obtain ⟨b, hb, hy⟩ := hy
        refine ⟨a + b, R₁.add_mem ha hb, ?_⟩
        rw [show x + y - (a + b) = (x - a) + (y - b) by ring]
        exact S.valuation.map_add_lt hx hy
      | mul x y _ _ hx hy =>
        obtain ⟨a, ha, hx⟩ := hx
        obtain ⟨b, hb, hy⟩ := hy
        refine ⟨a * b, R₁.mul_mem ha hb, ?_⟩
        rw [show x * y - a * b = (x - a) * (y - b) + (b * (x - a) + a * (y - b)) by ring]
        refine S.valuation.map_add_lt ?_ (S.valuation.map_add_lt ?_ ?_) <;> rw [map_mul]
        · exact lt_of_le_of_lt (mul_le_of_le_one_left' hx.le) hy
        · exact lt_of_le_of_lt (mul_le_of_le_one_left' (hR₁ _ hb)) hx
        · exact lt_of_le_of_lt (mul_le_of_le_one_left' (hR₁ _ ha)) hy
    have hnu : ¬ IsUnit (algebraMap R A u) := by
      intro hun
      obtain ⟨x, hx⟩ := hun.exists_right_inv
      have hx' : U * (x : K) = 1 := by
        have := congrArg (fun x : A => (x : K)) hx
        simpa using this
      obtain ⟨a, ha, hxa⟩ := hinv x x.2
      obtain ⟨M, hM, hqM⟩ := Ideal.exists_le_maximal q hqp.ne_top
      have hMc : (M.comap (algebraMap R R₁)).IsMaximal := by
        letI : M.IsMaximal := hM
        exact Ideal.isMaximal_under_of_isIntegral_of_isMaximal M
      have huM : algebraMap R R₁ u ∈ M := by
        rw [← Ideal.mem_comap, IsLocalRing.eq_maximalIdeal hMc]; exact hum
      have h1 : (1 - algebraMap R R₁ u * ⟨a, ha⟩ : R₁) ∈ q := by
        rw [hq]
        have : ((1 - algebraMap R R₁ u * ⟨a, ha⟩ : R₁) : K) = U * (x - a) := by
          rw [mul_sub, hx']; simp [hU]
        rw [this, map_mul, hv, one_mul]
        exact hxa
      apply hM.ne_top
      rw [Ideal.eq_top_iff_one]
      simpa using M.add_mem (hqM h1) (M.mul_mem_right (⟨a, ha⟩ : R₁) huM)
    obtain ⟨P, hP, huP⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.2 hnu)
    obtain ⟨C, i1, i2, i3, i4, gam, h1, h2⟩ :=
      exists_valuedField_centred_subalgebra R K u hu A hA P hP.isPrime huP
    have hgu : ‖gam U‖ < 1 := h2 _ huP
    refine ⟨C, i1, i2, i3, i4, gam, fun r => h1 _ (A.algebraMap_mem r), hgu, ?_⟩
    intro f hf hvf
    have hmem : f * (U ^ (e + 1))⁻¹ ∈ A :=
      Algebra.subset_adjoin (Submodule.mem_sup_right
        (Submodule.mem_map.2 ⟨f, Submodule.mem_map.2 ⟨⟨f, hf⟩, hvf, rfl⟩, rfl⟩))
    have hle : ‖gam f‖ ≤ ‖gam U‖ ^ (e + 1) := by
      have hf' : f = f * (U ^ (e + 1))⁻¹ * U ^ (e + 1) := by field_simp
      have h3 := h1 _ hmem
      rw [hf', map_mul, norm_mul, map_pow, norm_pow]
      exact mul_le_of_le_one_left (by positivity) h3
    refine ⟨hle.trans_lt (pow_lt_one₀ (norm_nonneg _) hgu (by omega)), fun _ => hle.trans ?_⟩
    exact pow_le_pow_of_le_one (norm_nonneg _) hgu.le (by omega)
  · have huq : algebraMap R R₁ u ∈ q := lt_of_le_of_ne (hR u) hv
    obtain ⟨C, i1, i2, i3, i4, gam, h1, h2⟩ :=
      exists_valuedField_centred_subalgebra R K u hu R₁ (Subalgebra.fg_of_fg_toSubmodule hfg)
        q hqp huq
    exact ⟨C, i1, i2, i3, i4, gam, fun r => h1 _ (R₁.algebraMap_mem r), h2 _ huq,
      fun f hf hvf => ⟨h2 ⟨f, hf⟩ hvf, fun h => absurd h hv⟩⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsValuedFieldValuationCentreLePowStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_valuedField_valuationCentre_le_pow : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R] [Field K] [Algebra R K] [FaithfulSMul R K] [Algebra.IsAlgebraic R K] (u : R), u ∈ IsLocalRing.maximalIdeal R → u ≠ 0 → ∀ R₁ : Subalgebra R K, Module.Finite R R₁ → ∀ S : ValuationSubring K, (∀ r, algebraMap R K r ∈ S) → ∀ e : ℕ, ∃ (C : Type) (_ : NontriviallyNormedField C) (_ : IsUltrametricDist C) (_ : CompleteSpace C) (_ : IsAlgClosed C) (gam : K →+* C), (∀ r, ‖gam (algebraMap R K r)‖ ≤ 1) ∧ ‖gam (algebraMap R K u)‖ < 1 ∧ ∀ f ∈ R₁, S.valuation f < 1 → ‖gam f‖ < 1 ∧ (S.valuation (algebraMap R K u) = 1 → ‖gam f‖ ≤ ‖gam (algebraMap R K u)‖ ^ e) := by
  first | exact @GlobalTheory.exists_valuedField_centre_le_pow | exact GlobalTheory.exists_valuedField_centre_le_pow | (intros; apply GlobalTheory.exists_valuedField_centre_le_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TwistIsoTorsionRepresentativeMulEquiv
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TwistIsoTorsionRepresentativeMulEquiv
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel
noncomputable section
namespace GlobalTheory.Relabel.TwIso
variable {O : Type} [CommRing O] {N N' : NumD O} {k : ℕ} (β : N.Form k) (u : Oˣ)

def twP (r : Oˣ) (y : N.X) (g : N.Gt) : (N.twist β u).Gt :=
  ⟨g.b, fun z => g.s z * r ^ β.be y z, (N.twG β r g (fun z => β.be y z) (fun _ _ => map_add _ _ _)).mult⟩

theorem twistMap_add_mul (r : Oˣ) (y y' : N.X) (g g' : N.Gt) :
    twP β u r (y + y') (g * g') = twP β u r y g * twP β u r y' g' :=
  NumD.Gt.ext rfl (funext fun (z : N.X) => by
    show g.s z * g'.s z / N.θ (N.c z) g.b g'.b * r ^ β.be (y + y') z =
      g.s z * r ^ β.be y z * (g'.s z * r ^ β.be y' z) / N.θ (N.c z) g.b g'.b
    rw [map_add (f := _), LinearMap.add_apply, zpow_add]
    apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_div]; abel)

theorem twistMap_mul_mul (r r' : Oˣ) (y : N.X) (g g' : N.Gt) :
    twP β u (r * r') y (g * g') = twP β u r y g * twP β u r' y g' :=
  NumD.Gt.ext rfl (funext fun (z : N.X) => by
    show g.s z * g'.s z / N.θ (N.c z) g.b g'.b * (r * r') ^ β.be y z =
      g.s z * r ^ β.be y z * (g'.s z * r' ^ β.be y z) / N.θ (N.c z) g.b g'.b
    rw [mul_zpow]
    apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_div]; abel)

theorem twistMap_pow (r : Oˣ) (y : N.X) (g : N.Gt) (m : ℕ) : twP β u r y g ^ m = twP β u (r ^ m) y (g ^ m) := by
  induction m with
  | zero =>
    simp only [pow_zero]
    refine NumD.Gt.ext rfl (funext fun (z : N.X) => ?_)
    show (1 : Oˣ) = 1 * 1 ^ β.be y z
    simp
  | succ m ih =>
    rw [pow_succ (twP β u r y g) m, ih, ← twistMap_mul_mul, ← pow_succ, ← pow_succ]

theorem twistMap_io (y : N.X) : twP β u u y (N.io y) = (N.twist β u).io y :=
  NumD.Gt.ext rfl (funext fun (z : N.X) => by
    show N.τ y z * u ^ β.be y z = (N.twist β u).τ y z
    rw [NumD.twist_τ])

theorem twistMap_nsmul (r : Oˣ) (j : ℕ) (y : N.X) (g : N.Gt) : twP β u r (j • y) g = twP β u (r ^ j) y g :=
  NumD.Gt.ext rfl (funext fun (z : N.X) => by
    show g.s z * r ^ β.be (j • y) z = g.s z * (r ^ j) ^ β.be y z
    rw [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul, zpow_mul, zpow_natCast])

theorem twistMap_bijective₂ (r : Oˣ) (y : N.X) : Function.Bijective (twP β u r y) := by
  constructor
  · intro g g' h
    have hb : g.b = g'.b := congrArg (fun x => x.b) h
    have hs : ∀ z, g.s z * r ^ β.be y z = g'.s z * r ^ β.be y z :=
      fun z => congrFun (congrArg (fun x => x.s) h) z
    exact NumD.Gt.ext hb (funext fun z => mul_right_cancel (hs z))
  · intro h
    refine ⟨⟨h.b, fun z => h.s z * r⁻¹ ^ β.be y z,
      (N.twG β r⁻¹ ⟨h.b, h.s, h.mult⟩ (fun z => β.be y z) (fun _ _ => map_add _ _ _)).mult⟩, ?_⟩
    refine NumD.Gt.ext rfl (funext fun (z : N.X) => ?_)
    show h.s z * r⁻¹ ^ β.be y z * r ^ β.be y z = h.s z
    rw [inv_zpow, inv_mul_cancel_right]

def isoG {M M' : NumD O} (J : NumD.Iso M M') : M.Gt →* M'.Gt :=
  MonoidHom.mk' (NumD.Hom.ofIso J).img fun g h =>
    (((NumD.Hom.ofIso J).rel_iff _ _).1 (((NumD.Hom.ofIso J).rel_img g).mul ((NumD.Hom.ofIso J).rel_img h))).symm

theorem rel_iff_isoG {M M' : NumD O} (J : NumD.Iso M M') (g : M.Gt) (g' : M'.Gt) : J.Rel g g' ↔ g' = isoG J g := by
  rw [← NumD.Hom.ofIso_rel, NumD.Hom.rel_iff]
  exact Iff.rfl

theorem isoG_io {M M' : NumD O} (J : NumD.Iso M M') (y : M.X) : isoG J (M.io y) = M'.io (J.e y) :=
  (((NumD.Hom.ofIso J).rel_iff _ _).1 ((NumD.Hom.ofIso J).rel_io y)).symm

private theorem eq_of_div_eq_div_div {G : Type*} [CommGroup G] {a b c d x y : G} (h1 : a = b) (h2 : c = d)
    (h : x / y = a / b / (c / d)) : x = y := by
  rw [div_eq_one.mpr h1, div_eq_one.mpr h2, div_one] at h
  exact div_eq_one.mp h

theorem isoG_bijective {M M' : NumD O} (J : NumD.Iso M M') : Function.Bijective (isoG J) := by
  refine ⟨(injective_iff_map_eq_one (isoG J)).2 fun g hg => ?_, fun g' => ?_⟩
  · obtain ⟨hb, hs⟩ := (rel_iff_isoG J g 1).2 hg.symm
    have hgb : g.b = 1 := by
      have h1 : J.φ g.b = 1 := by rw [← hb]; rfl
      exact (MulEquiv.map_eq_one_iff J.φ).1 h1
    refine NumD.Gt.ext hgb (funext fun χ => ?_)
    have h2 := hs χ
    simp only [NumD.Gt.generator_inv_base, hgb, _root_.mul_one, J.h_one, _root_.one_mul] at h2
    show g.s χ = 1
    exact mul_right_cancel (h2.symm.trans (_root_.one_mul _).symm)
  · refine ⟨⟨J.φ.symm g'.b, fun χ => g'.s (J.e χ) * J.h (M.c χ * J.φ.symm g'.b) /
        (J.h (M.c χ) * J.h (J.φ.symm g'.b)), fun χ χ' => ?_⟩, ?_⟩
    · have hm := g'.mult (J.e χ) (J.e χ')
      have ht := J.θ_eq (M.c χ) (M.c χ') (J.φ.symm g'.b)
      rw [J.c_eq, J.c_eq, ← map_add J.e χ χ'] at hm
      rw [MulEquiv.apply_symm_apply] at ht
      rw [M.c_add]
      refine eq_of_div_eq_div_div hm ht ?_
      apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_div]; abel
    · refine ((rel_iff_isoG J _ g').1 ⟨(J.φ.apply_symm_apply _).symm, fun χ => ?_⟩).symm
      show g'.s (J.e χ) * J.h (M.c χ * J.φ.symm g'.b) = g'.s (J.e χ) * J.h (M.c χ * J.φ.symm g'.b) /
        (J.h (M.c χ) * J.h (J.φ.symm g'.b)) * J.h (M.c χ) * J.h (J.φ.symm g'.b)
      rw [mul_assoc _ (J.h (M.c χ)), div_mul_cancel]

variable {β u} (J : NumD.Iso (N.twist β u) N')

theorem twJ_elim {r : Oˣ} {j : ℕ} {q : N.QT j} {q' : N'.QT j} (h : TwJ β u r J q q') :
    q'.1.1.toAdd = J.e q.1.1.toAdd ∧ q'.1.2 = isoG J (twP β u r q.1.1.toAdd q.1.2) := by
  obtain ⟨p, ⟨h1, h2, h3⟩, e, hr⟩ := h
  have hp : p.1.2 = twP β u r q.1.1.toAdd q.1.2 := NumD.Gt.ext h2 (funext h3)
  refine ⟨e.trans (congrArg (fun x => J.e (Multiplicative.toAdd x)) h1), ?_⟩
  rw [← hp]
  exact (rel_iff_isoG J _ _).1 hr

def twQ {r : Oˣ} {j : ℕ} (h : r ^ j = u) (q : N.QT j) : (N.twist β u).QT j :=
  ⟨(q.1.1, twP β u r q.1.1.toAdd q.1.2), by
    change twP β u r q.1.1.toAdd q.1.2 ^ j = (N.twist β u).io q.1.1.toAdd
    rw [twistMap_pow, h, N.mem_QT.1 q.2, twistMap_io]⟩

def tauHom {r : Oˣ} {j : ℕ} (h : r ^ j = u) : N.QT j →* N'.QT j :=
  MonoidHom.mk' (fun q => ⟨(Multiplicative.ofAdd (J.e q.1.1.toAdd), isoG J (twP β u r q.1.1.toAdd q.1.2)), by
      change isoG J (twP β u r q.1.1.toAdd q.1.2) ^ j = N'.io (J.e q.1.1.toAdd)
      rw [← map_pow, twistMap_pow, h, N.mem_QT.1 q.2, twistMap_io]
      exact isoG_io J _⟩)
    fun q q' => Subtype.ext (Prod.ext (congrArg Multiplicative.ofAdd (map_add J.e q.1.1.toAdd q'.1.1.toAdd))
      ((congrArg (isoG J) (twistMap_add_mul β u r q.1.1.toAdd q'.1.1.toAdd q.1.2 q'.1.2)).trans (map_mul _ _ _)))

theorem tauHom_bijective {r : Oˣ} {j : ℕ} (h : r ^ j = u) : Function.Bijective (tauHom J h) := by
  constructor
  · intro q₁ q₂ hq
    have h1 : J.e q₁.1.1.toAdd = J.e q₂.1.1.toAdd := congrArg (fun q => q.1.1.toAdd) hq
    have h2 : isoG J (twP β u r q₁.1.1.toAdd q₁.1.2) = isoG J (twP β u r q₂.1.1.toAdd q₂.1.2) :=
      congrArg (fun q => q.1.2) hq
    have e1 : q₁.1.1.toAdd = q₂.1.1.toAdd := J.e.injective h1
    rw [e1] at h2
    have e2 := (twistMap_bijective₂ β u r _).1 ((isoG_bijective J).1 h2)
    exact Subtype.ext (Prod.ext (Multiplicative.toAdd.injective e1) e2)
  · intro q'
    obtain ⟨g', hg'⟩ := (isoG_bijective J).2 q'.1.2
    obtain ⟨g, hg⟩ := (twistMap_bijective₂ β u r (J.e.symm q'.1.1.toAdd)).2 g'
    refine ⟨⟨(Multiplicative.ofAdd (J.e.symm q'.1.1.toAdd), g), ?_⟩, ?_⟩
    · have hq := N'.mem_QT.1 q'.2
      have e0 : twP β u r (J.e.symm q'.1.1.toAdd) g ^ j = twP β u u (J.e.symm q'.1.1.toAdd) (g ^ j) :=
        (twistMap_pow β u r (J.e.symm q'.1.1.toAdd) g j).trans
          (congrArg (fun s => twP β u s (J.e.symm q'.1.1.toAdd) (g ^ j)) h)
      have hq2 : isoG J (twP β u u (J.e.symm q'.1.1.toAdd) (g ^ j)) = N'.io q'.1.1.toAdd :=
        (congrArg (isoG J) e0.symm).trans ((map_pow (isoG J) _ j).trans
          ((congrArg (fun t => isoG J t ^ j) hg).trans ((congrArg (· ^ j) hg').trans hq)))
      have hio : isoG J (twP β u u (J.e.symm q'.1.1.toAdd) (N.io (J.e.symm q'.1.1.toAdd))) = N'.io q'.1.1.toAdd :=
        (congrArg (isoG J) (twistMap_io β u (J.e.symm q'.1.1.toAdd))).trans
          ((isoG_io J _).trans (congrArg N'.io (J.e.apply_symm_apply _)))
      exact N.mem_QT.2 ((twistMap_bijective₂ β u u _).1 ((isoG_bijective J).1 (hq2.trans hio.symm)))
    · refine Subtype.ext (Prod.ext ?_ ?_)
      · show Multiplicative.ofAdd (J.e (J.e.symm q'.1.1.toAdd)) = q'.1.1
        rw [J.e.apply_symm_apply]
        rfl
      · exact (congrArg (isoG J) hg).trans hg'

theorem tauHom_qTriv {r : Oˣ} {j : ℕ} (h : r ^ j = u) (z : N.X) : tauHom J h (N.qTriv j z) = N'.qTriv j (J.e z) := by
  refine Subtype.ext (Prod.ext ?_ ?_)
  · exact congrArg Multiplicative.ofAdd (map_nsmul J.e j z)
  · exact (congrArg (isoG J) ((twistMap_nsmul β u r j z (N.io z)).trans
      (show twP β u (r ^ j) z (N.io z) = (N.twist β u).io z by rw [h, twistMap_io]))).trans (isoG_io J z)

theorem wp_twQ {r : Oˣ} {j : ℕ} (h : r ^ j = u) (q₁ q₂ : N.QT j) :
    (N.twist β u).wp (twQ (β := β) h q₁) (twQ h q₂) = N.wp q₁ q₂ := by
  show q₁.1.2.s q₂.1.1.toAdd * r ^ β.be q₁.1.1.toAdd q₂.1.1.toAdd * cubN N.θ j 1 q₂.1.2.b q₁.1.2.b /
      (q₂.1.2.s q₁.1.1.toAdd * r ^ β.be q₂.1.1.toAdd q₁.1.1.toAdd * cubN N.θ j 1 q₁.1.2.b q₂.1.2.b) =
    q₁.1.2.s q₂.1.1.toAdd * cubN N.θ j 1 q₂.1.2.b q₁.1.2.b /
      (q₂.1.2.s q₁.1.1.toAdd * cubN N.θ j 1 q₁.1.2.b q₂.1.2.b)
  rw [β.symm q₂.1.1.toAdd q₁.1.1.toAdd]
  apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_div]; abel

end GlobalTheory.Relabel.TwIso


open GlobalTheory.Relabel.TwIso in
theorem GlobalTheory.Relabel.twJ_mulEquiv : ∀ (O : Type) [CommRing O] (N N' : NumD O) (k : ℕ) (β : N.Form k) (u : Oˣ) (J : NumD.Iso (N.twist β u) N'), (∀ (r : Oˣ) (j : ℕ), r ^ j = u → ∃ τ : N.QT j ≃* N'.QT j, (∀ q q', τ q = q' ↔ TwJ β u r J q q') ∧ (∀ q₁ q₂, N.QEq q₁ q₂ ↔ N'.QEq (τ q₁) (τ q₂)) ∧ ∀ q₁ q₂, N'.wp (τ q₁) (τ q₂) = N.wp q₁ q₂) ∧ ∀ (r₁ r₂ : Oˣ) (n n' m : ℕ) (q₁ : N.QT n) (q₂ : N.QT n') (q₁' : N'.QT n) (q₂' : N'.QT n'), r₂ ^ m = r₁ → q₁.1.1 = q₂.1.1 → q₁.1.2 = q₂.1.2 ^ m → TwJ β u r₁ J q₁ q₁' → TwJ β u r₂ J q₂ q₂' → q₁'.1.1 = q₂'.1.1 ∧ q₁'.1.2 = q₂'.1.2 ^ m := by
  intro O _ N N' k β u J
  refine ⟨fun r j h => ?_, fun r₁ r₂ n n' m q₁ q₂ q₁' q₂' hr e1 e2 t1 t2 => ?_⟩
  · refine ⟨MulEquiv.ofBijective (tauHom J h) (tauHom_bijective J h), fun q q' => ?_,
      fun q₁ q₂ => ?_, fun q₁ q₂ => ?_⟩
    · show tauHom J h q = q' ↔ _
      constructor
      · rintro rfl
        exact ⟨twQ (β := β) h q, ⟨rfl, rfl, fun _ => rfl⟩, rfl, (rel_iff_isoG J _ _).2 rfl⟩
      · intro ht
        obtain ⟨e, he⟩ := twJ_elim J ht
        refine Subtype.ext (Prod.ext ?_ he.symm)
        exact (congrArg Multiplicative.ofAdd e).symm
    · rw [NumD.qEq_iff, NumD.qEq_iff]
      show (∃ z, q₂ = q₁ * N.qTriv j z) ↔ ∃ z, tauHom J h q₂ = tauHom J h q₁ * N'.qTriv j z
      constructor
      · rintro ⟨z, rfl⟩
        exact ⟨J.e z, (map_mul _ _ _).trans (congrArg _ (tauHom_qTriv J h z))⟩
      · rintro ⟨z, hz⟩
        refine ⟨J.e.symm z, (tauHom_bijective J h).1 ?_⟩
        exact hz.trans ((congrArg (tauHom J h q₁ * ·) ((tauHom_qTriv J h (J.e.symm z)).trans
          (congrArg (N'.qTriv j) (J.e.apply_symm_apply z))).symm).trans (map_mul (tauHom J h) q₁ _).symm)
    · have hrel : ∀ q : N.QT j, (NumD.Hom.ofIso J).Rel (twQ (β := β) h q).1.2 (tauHom J h q).1.2 :=
        fun q => (NumD.Hom.ofIso J).rel_img _
      have hw := NumD.Hom.wp_eq (NumD.Hom.ofIso J) (twQ (β := β) h q₁) (twQ (β := β) h q₂)
        (tauHom J h q₁) (tauHom J h q₂) rfl (hrel q₁) rfl (hrel q₂)
      rw [wp_twQ] at hw
      show N'.wp (tauHom J h q₁) (tauHom J h q₂) = _
      rw [hw]
      exact Units.ext rfl
  · obtain ⟨a1, b1⟩ := twJ_elim J t1
    obtain ⟨a2, b2⟩ := twJ_elim J t2
    refine ⟨?_, ?_⟩
    · exact Multiplicative.toAdd.injective
        (a1.trans ((congrArg (fun x => J.e (Multiplicative.toAdd x)) e1).trans a2.symm))
    · rw [b1, b2]
      calc isoG J (twP β u r₁ q₁.1.1.toAdd q₁.1.2) = isoG J (twP β u r₂ q₂.1.1.toAdd q₂.1.2 ^ m) := by
            rw [twistMap_pow, hr, e1, e2]
        _ = _ := map_pow _ _ _
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TwistIsoTorsionRepresentativeMulEquivStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_iso_torsionRepresentative_mulEquiv : ∀ (O : Type) [CommRing O] (N N' : NumD O) (k : ℕ) (β : N.Form k) (u : Oˣ) (J : NumD.Iso (N.twist β u) N'), (∀ (r : Oˣ) (j : ℕ), r ^ j = u → ∃ τ : N.QT j ≃* N'.QT j, (∀ q q', τ q = q' ↔ TwJ β u r J q q') ∧ (∀ q₁ q₂, N.QEq q₁ q₂ ↔ N'.QEq (τ q₁) (τ q₂)) ∧ ∀ q₁ q₂, N'.wp (τ q₁) (τ q₂) = N.wp q₁ q₂) ∧ ∀ (r₁ r₂ : Oˣ) (n n' m : ℕ) (q₁ : N.QT n) (q₂ : N.QT n') (q₁' : N'.QT n) (q₂' : N'.QT n'), r₂ ^ m = r₁ → q₁.1.1 = q₂.1.1 → q₁.1.2 = q₂.1.2 ^ m → TwJ β u r₁ J q₁ q₁' → TwJ β u r₂ J q₂ q₂' → q₁'.1.1 = q₂'.1.1 ∧ q₁'.1.2 = q₂'.1.2 ^ m := by
  first | exact @GlobalTheory.Relabel.twJ_mulEquiv | exact GlobalTheory.Relabel.twJ_mulEquiv | (intros; apply GlobalTheory.Relabel.twJ_mulEquiv <;> assumption)
end
end
