module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitBlockCosetThetaVectorMemThetaFunctions
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.InVVwIffOfNotTorsion
public import Development.AutomorphicArithmetic.DivisorFrames.ExistsNsmulMemSumImageLatticeOfSurjectiveMod

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.DivisorFrames.ExistsInjectiveLatticeHomRingOfIntegersOfFinrank
open NumberField

private lemma rk (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) [h : DiscreteTopology Λ] : Module.finrank ℤ Λ ≤ 2 * g := by
  have h1 := Real.finrank_eq_int_finrank_of_discrete (E := Fin g → ℂ) (s := (Λ : Set (Fin g → ℂ))) (by rw [Submodule.span_eq]; exact h)
  have h2 : Set.finrank ℤ (Λ : Set (Fin g → ℂ)) = Module.finrank ℤ Λ := by
    unfold Set.finrank; rw [Submodule.span_eq]
  have h3 : Set.finrank ℝ (Λ : Set (Fin g → ℂ)) ≤ Module.finrank ℝ (Fin g → ℂ) := Submodule.finrank_le _
  have h4 : Module.finrank ℝ (Fin g → ℂ) = 2 * g := by
    rw [Module.finrank_pi_fintype]; simp [mul_comm]
  omega

theorem UpperTheory.exists_injective_lattice_hom_ringOfIntegers_of_finrank_ge :
    ∀ (E : Type) [Field E] [NumberField E] (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ))
        (α : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)), 2 * g ≤ Module.finrank ℚ E → DiscreteTopology Λ →
        ∀ (hs : ∀ s, ∀ z ∈ Λ, α s z ∈ Λ),
        ∃ ι : Λ →+ 𝓞 E, Function.Injective ι ∧ ∀ (s : 𝓞 E) (x : Λ), ι ⟨α s x, hs s x x.2⟩ = s * ι x := by
  intro E _ _ g Λ α hg hd hs
  by_cases h0 : ∀ x : Λ, x = 0
  · refine ⟨0, fun a b _ => by rw [h0 a, h0 b], fun s x => by simp⟩
  push Not at h0
  obtain ⟨x0, hx0⟩ := h0
  let ψ' : 𝓞 E →+ Λ :=
    { toFun := fun s => ⟨α s x0, hs s x0 x0.2⟩
      map_zero' := by ext1; simp
      map_add' := fun a b => by ext1; simp }
  let ψ : 𝓞 E →ₗ[ℤ] Λ := ψ'.toIntLinearMap
  have hψ : ∀ s, (ψ s : Fin g → ℂ) = α s x0 := fun s => rfl
  have hinj : Function.Injective ψ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro s hs0
    by_contra hne
    have hz : α s x0 = 0 := by rw [← hψ, hs0]; rfl
    have hm := Ideal.absNorm_mem (Ideal.span {s})
    have hn : Ideal.absNorm (Ideal.span {s}) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hne
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hm
    have : α (t * s) x0 = 0 := by rw [map_mul, Module.End.mul_apply, hz, map_zero]
    rw [ht, map_natCast, Module.End.natCast_apply, ← Nat.cast_smul_eq_nsmul ℂ, smul_eq_zero] at this
    rcases this with h | h
    · exact hn (by exact_mod_cast h)
    · exact hx0 (Subtype.ext h)
  have hr : Module.finrank ℤ (LinearMap.range ψ) = Module.finrank ℤ Λ := by
    apply le_antisymm (Submodule.finrank_le _)
    rw [LinearMap.finrank_range_of_inj hinj, RingOfIntegers.rank]
    exact (rk g Λ).trans hg
  have hfin : Finite (Λ ⧸ LinearMap.range ψ) := Submodule.finiteQuotientOfFreeOfRankEq _ hr
  set d := Nat.card (Λ ⧸ LinearMap.range ψ) with hdd
  have hd0 : d ≠ 0 := Nat.card_pos.ne'
  have hmem : ∀ x : Λ, ∃ t, ψ t = d • x := by
    intro x
    have : (LinearMap.range ψ).mkQ (d • x) = 0 := by
      rw [map_nsmul]; exact card_nsmul_eq_zero'
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
    exact this
  choose f hf using hmem
  refine ⟨AddMonoidHom.mk' f (fun a b => hinj ?_), fun a b hab => ?_, fun s x => hinj ?_⟩
  · rw [map_add (f := _), hf, hf, hf, smul_add]
  · have h1 : f a = f b := hab
    have h2 : d • a = d • b := by rw [← hf, ← hf, h1]
    have h3 : (d : ℂ) • (a : Fin g → ℂ) = (d : ℂ) • (b : Fin g → ℂ) := by
      simp only [Nat.cast_smul_eq_nsmul]
      exact congrArg Subtype.val h2
    exact Subtype.ext (smul_right_injective _ (by exact_mod_cast hd0) h3)
  · change ψ (f _) = ψ (s * f x)
    rw [hf]
    ext1
    rw [hψ, map_mul, Module.End.mul_apply, ← hψ, hf]
    exact (map_nsmul (α s) d (x : Fin g → ℂ)).symm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionCmUnitaryShimuraMemClosureLinearHomImages
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTorsionMemClosureGenerators
open NumberField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatCM.CplxGen

section Points

open scoped CategoryTheory.Obj

variable {S : Scheme.{0}} (f : Sp ℂ ⟶ S)

private def pt {G : Over S} (x : 𝟙_ (Over (Sp ℂ)) ⟶ (Over.pullback f).obj G) : Over.mk f ⟶ G :=
  Over.homMk (x.left ≫ pullback.fst G.hom f) (by
    have h : x.left ≫ pullback.snd G.hom f = 𝟙 _ := Over.w x
    rw [Category.assoc, pullback.condition, ← Category.assoc, h]
    exact Category.id_comp _)

private theorem pt_injective {G : Over S} : Function.Injective (pt f (G := G)) := fun a b e =>
  Over.OverMorphism.ext (pullback.hom_ext (congrArg (fun q => q.left) e) ((Over.w a).trans (Over.w b).symm))

private theorem pt_surjective {G : Over S} : Function.Surjective (pt f (G := G)) := fun y =>
  ⟨Over.homMk (pullback.lift y.left (𝟙 _) ((Over.w y).trans (Category.id_comp _).symm)) (pullback.lift_snd _ _ _),
    Over.OverMorphism.ext (pullback.lift_fst _ _ _)⟩

private theorem pt_map {G G' : Over S} (φ : G ⟶ G') (x : 𝟙_ (Over (Sp ℂ)) ⟶ (Over.pullback f).obj G) :
    pt f (x ≫ (Over.pullback f).map φ) = pt f x ≫ φ := by
  refine Over.OverMorphism.ext ?_
  simp only [pt, Over.homMk_left, Over.comp_left, Over.pullback_map_left, Category.assoc]
  exact congrArg (x.left ≫ ·) (pullback.lift_fst _ _ _)

private theorem pt_mul {G : Over S} [GrpObj G] (x y : 𝟙_ (Over (Sp ℂ)) ⟶ (Over.pullback f).obj G) :
    pt f (x * y) = pt f x * pt f y := by
  let ρ : Over.mk ((𝟙_ (Over (Sp ℂ))).hom ≫ f) ⟶ Over.mk f := Over.homMk (𝟙 _) (by simp)
  have h := (isGrpPullback_pullback G f).2 _ x y (ρ ≫ pt f x) (ρ ≫ pt f y) (Category.id_comp _) (Category.id_comp _)
  rw [← MonObj.comp_mul] at h
  refine Over.OverMorphism.ext ?_
  exact h.symm.trans (Category.id_comp _)

private theorem exists_unif (P : Out.PolAV S) : ∃ (L : LB ((Over.pullback f).obj P.A).left)
    (_ : HolUnif ((Over.pullback f).obj P.A) L P.g), IsAbelianScheme ((Over.pullback f).obj P.A) ∧
      SmoothOfRelativeDimension P.g ((Over.pullback f).obj P.A).hom := by
  have := P.isAb.comm
  let h := isGrpPullback_pullback P.A f
  have gen_refl {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) :
      LB.Gen.IsGen (⟨fun p => L.g p.1 p.2⟩ : LB.Iso L L) := by
    refine fun p q => unit_ext fun y hy => ?_
    refine (gm_res _ y _ hy _).trans (Eq.symm ((map_mul _ _ _).trans ((congrArg₂ (· * ·)
      (gm_div L L (𝟙 X) y p q hy) (gm_res _ y _ hy _)).trans ?_)))
    have a := gm_cocycle hL (𝟙 X) y hy.1.1 hy.2.1 hy.2.2
    have b := gm_cocycle hL (𝟙 X) y hy.1.1 hy.1.2 hy.2.2
    show gm (𝟙 X) y _ (L.g p.1 q.1) * (gm (𝟙 X) y _ (L.g p.2 q.2))⁻¹ * gm (𝟙 X) y _ (L.g q.1 q.2) =
      gm (𝟙 X) y _ (L.g p.1 p.2)
    rw [mul_right_comm, a, ← b, mul_inv_cancel_right]
  let Q : Out.PolAV (Sp ℂ) := {
    A := (Over.pullback f).obj P.A
    isAb := {
      comm := inferInstance
      smooth := MorphismProperty.of_isPullback (P := @Smooth) h.1 P.isAb.smooth
      proper := MorphismProperty.of_isPullback (P := @IsProper) h.1 P.isAb.proper
      geomConnected := MorphismProperty.of_isPullback (P := @GeometricallyConnected) h.1 P.isAb.geomConnected }
    g := P.g
    smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 P.smoothDim
    L := P.L.pull _
    isLB := pull_isLB P.isLB _
    rigid := PolBaseChange.rigidified_pull h P.rigid
    sym := PolBaseChange.sym_pull h P.sym
    ample := by
      haveI := P.isAb.proper
      exact AmpleBaseChange.relAmple_of_isPullback P.isLB P.ample h.1
    ktriv := kTriv_pull h P.isLB (pull_isLB P.isLB _) ((isGen_iff _).1 (gen_refl (pull_isLB P.isLB _))) P.ktriv }
  obtain ⟨rig, hrig⟩ := Q.rigid
  obtain ⟨v, -⟩ := thetaUnifAV_all Q rig hrig
  exact ⟨_, v, Q.isAb, Q.smoothDim⟩

set_option synthInstance.maxHeartbeats 100000 in
private theorem exists_unif_points (P Q : Out.PolAV S) :
    ∃ (ΛA : Submodule ℤ (Fin P.g → ℂ)) (ΛB : Submodule ℤ (Fin Q.g → ℂ))
      (eA : (Fin P.g → ℂ) → (Over.mk f ⟶ P.A)) (eB : (Fin Q.g → ℂ) → (Over.mk f ⟶ Q.A)),
      (∀ z w, eA (z + w) = eA z * eA w) ∧ Function.Surjective eA ∧ (∀ z, eA z = 1 ↔ z ∈ ΛA) ∧
      DiscreteTopology ΛA ∧ Submodule.span ℝ (ΛA : Set (Fin P.g → ℂ)) = ⊤ ∧
      (∀ z w, eB (z + w) = eB z * eB w) ∧ Function.Surjective eB ∧ (∀ z, eB z = 1 ↔ z ∈ ΛB) ∧
      DiscreteTopology ΛB ∧
      (∀ φ : P.A ⟶ P.A, IsMonHom φ → ∃ M : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ), ∀ z, eA (M z) = eA z ≫ φ) ∧
      (∀ φ : Q.A ⟶ Q.A, IsMonHom φ → ∃ M : (Fin Q.g → ℂ) →ₗ[ℂ] (Fin Q.g → ℂ), ∀ z, eB (M z) = eB z ≫ φ) ∧
      (∀ φ : P.A ⟶ Q.A, IsMonHom φ → ∃ M : (Fin P.g → ℂ) →ₗ[ℂ] (Fin Q.g → ℂ), ∀ z, eB (M z) = eA z ≫ φ) := by
  obtain ⟨L, u, hA, hdA⟩ := exists_unif f P
  obtain ⟨L', v, hB, hdB⟩ := exists_unif f Q
  have hu := TorusTransfer.tangent_bijective u hdA
  have hv := TorusTransfer.tangent_bijective v hdB
  have one : ∀ {G : Over S} [GrpObj G] (x : 𝟙_ (Over (Sp ℂ)) ⟶ (Over.pullback f).obj G), pt f x = 1 ↔ x = 1 :=
    fun {G} _ x => map_eq_one_iff (MonoidHom.mk' (pt f (G := G)) (pt_mul f)) (pt_injective f)
  refine ⟨u.Λ, v.Λ, fun z => pt f (u.ex z), fun z => pt f (v.ex z),
    fun z w => by beta_reduce; rw [u.ex_add, pt_mul],
    (pt_surjective f).comp u.ex_onto, fun z => (one _).trans (u.ker z), u.discrete, u.full,
    fun z w => by beta_reduce; rw [v.ex_add, pt_mul], (pt_surjective f).comp v.ex_onto, fun z => (one _).trans (v.ker z),
    v.discrete, fun φ _ => ?_, fun φ _ => ?_, fun φ _ => ?_⟩
  · obtain ⟨M, hM, -⟩ := HomLinear.exists_linear_of_isMonHom _ _ hA hA _ _ _ _ u u hu.1 hu.2
      ((Over.pullback f).map φ) inferInstance
    exact ⟨M, fun z => by beta_reduce; rw [hM, pt_map]⟩
  · obtain ⟨M, hM, -⟩ := HomLinear.exists_linear_of_isMonHom _ _ hB hB _ _ _ _ v v hv.1 hv.2
      ((Over.pullback f).map φ) inferInstance
    exact ⟨M, fun z => by beta_reduce; rw [hM, pt_map]⟩
  · obtain ⟨M, hM, -⟩ := HomLinear.exists_linear_of_isMonHom _ _ hA hB _ _ _ _ u v hv.1 hv.2
      ((Over.pullback f).map φ) inferInstance
    exact ⟨M, fun z => by beta_reduce; rw [hM, pt_map]⟩

end Points

private theorem lattice_mem_closure (E : Type) [Field E] [NumberField E] (gA gB p : ℕ)
    (ΛA : Submodule ℤ (Fin gA → ℂ)) (ΛB : Submodule ℤ (Fin gB → ℂ)) (αA : 𝓞 E →+* Module.End ℂ (Fin gA → ℂ))
    (αB : 𝓞 E →+* Module.End ℂ (Fin gB → ℂ)) (J : Fin p → (Fin gA → ℂ) →ₗ[ℂ] (Fin gB → ℂ))
    (hdim : 2 * gA ≤ Module.finrank ℚ E) (hAd : DiscreteTopology ΛA)
    (hAf : Submodule.span ℝ (ΛA : Set (Fin gA → ℂ)) = ⊤) (hBd : DiscreteTopology ΛB)
    (sA : ∀ s, ∀ z ∈ ΛA, αA s z ∈ ΛA) (sB : ∀ s, ∀ z ∈ ΛB, αB s z ∈ ΛB)
    (inter : ∀ a s z, J a (αA s z) = αB s (J a z)) (hJ : ∀ a, ∀ z ∈ ΛA, J a z ∈ ΛB)
    (honto : ∀ w, ∃ v : Fin p → (Fin gA → ℂ), w - ∑ a, J a (v a) ∈ ΛB) (l : Fin gB → ℂ) (hl : l ∈ ΛB) :
    l ∈ AddSubmonoid.closure {w : Fin gB → ℂ | ∃ (m : ℕ) (z : Fin p → 𝓞 E) (x : Fin gA → ℂ), 0 < m ∧ x ∈ ΛA ∧
      (∀ x' ∈ ΛA, (m : ℂ)⁻¹ • ∑ a, J a (αA (z a) x') ∈ ΛB) ∧ w = (m : ℂ)⁻¹ • ∑ a, J a (αA (z a) x)} := by
  classical
  obtain ⟨N, x, hN, hx, hNl⟩ := UpperTheory.exists_nsmul_mem_sum_image_lattice_of_surjective_mod gA gB p ΛA ΛB J hAf hBd hJ honto l hl
  obtain ⟨j, hj, hjs⟩ := UpperTheory.exists_injective_lattice_hom_ringOfIntegers_of_finrank_ge E gA ΛA αA hdim hAd sA
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  let I : Ideal (𝓞 E) := Ideal.span (Set.range j)
  by_cases hI : I = ⊥
  · have h0 : ∀ a, x a = 0 := fun a => by
      have h : j ⟨x a, hx a⟩ ∈ I := Ideal.subset_span ⟨_, rfl⟩
      rw [hI, Ideal.mem_bot, ← map_zero j] at h
      exact congrArg Subtype.val (hj h)
    simp only [h0, map_zero, Finset.sum_const_zero] at hNl
    rw [(smul_eq_zero.1 hNl).resolve_left hN.ne']
    exact zero_mem _
  obtain ⟨c, hcI, hc⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  obtain ⟨I', hI'⟩ : I ∣ Ideal.span {c} := Ideal.dvd_span_singleton.2 hcI
  have hmem : ∀ t ∈ I, ∃ y : ΛA, j y = t := fun t ht => by
    refine Submodule.span_induction (p := fun t _ => ∃ y : ΛA, j y = t) (fun t ht => ht) ⟨0, map_zero _⟩ ?_ ?_ ht
    · rintro _ _ - - ⟨y, rfl⟩ ⟨y', rfl⟩
      exact ⟨y + y', map_add _ _ _⟩
    · rintro s _ - ⟨y, rfl⟩
      exact ⟨_, hjs s y⟩
  have hdiv : ∀ b ∈ I', ∀ y : ΛA, ∃ u, u * c = j y * b := fun b hb y =>
    Ideal.mem_span_singleton'.1 (hI' ▸ Ideal.mul_mem_mul (Ideal.subset_span ⟨y, rfl⟩) hb)
  have key : ∀ t ∈ I * I', ∃ u, u * c = t ∧ αB u l ∈ AddSubmonoid.closure
      {w : Fin gB → ℂ | ∃ (m : ℕ) (z : Fin p → 𝓞 E) (x : Fin gA → ℂ), 0 < m ∧ x ∈ ΛA ∧
        (∀ x' ∈ ΛA, (m : ℂ)⁻¹ • ∑ a, J a (αA (z a) x') ∈ ΛB) ∧ w = (m : ℂ)⁻¹ • ∑ a, J a (αA (z a) x)} := by
    intro t ht
    refine Submodule.mul_induction_on ht (fun r hr b hb => ?_) ?_
    · obtain ⟨y, rfl⟩ := hmem r hr
      choose φ hφ using hdiv b hb
      have hsw : ∀ y y' : ΛA, αA (φ y) y' = αA (φ y') y := fun y y' => by
        have h : (⟨αA (φ y) y', sA _ _ y'.2⟩ : ΛA) = ⟨αA (φ y') y, sA _ _ y.2⟩ := hj (by
          rw [hjs, hjs]
          refine mul_right_cancel₀ hc ?_
          linear_combination j y' * hφ y - j y * hφ y')
        exact congrArg Subtype.val h
      have hval : ∀ y' : ΛA, (N : ℂ)⁻¹ • ∑ a, J a (αA (φ ⟨x a, hx a⟩) y') = αB (φ y') l := fun y' => by
        have : ∑ a, J a (αA (φ ⟨x a, hx a⟩) y') = N • αB (φ y') l := by
          set_option synthInstance.maxHeartbeats 100000 in
            rw [← map_nsmul, hNl, map_sum]
          exact Finset.sum_congr rfl fun a _ => by rw [hsw, inter]
        rw [this, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hN0, one_smul]
      refine ⟨φ y, hφ y, AddSubmonoid.subset_closure ⟨N, fun a => φ ⟨x a, hx a⟩, y, hN, y.2, fun x' hx' => ?_,
        (hval y).symm⟩⟩
      rw [hval ⟨x', hx'⟩]
      exact sB _ _ hl
    · rintro _ _ ⟨u, rfl, hu⟩ ⟨u', rfl, hu'⟩
      exact ⟨u + u', add_mul _ _ _, by rw [map_add (f := _), LinearMap.add_apply]; exact add_mem hu hu'⟩
  obtain ⟨u, hu, h⟩ := key c (hI' ▸ Ideal.mem_span_singleton_self c)
  obtain rfl : u = 1 := mul_right_cancel₀ hc (hu.trans (_root_.one_mul c).symm)
  simpa using h

section Unif

variable {P : Type} [CommGroup P] {g : ℕ} {e : (Fin g → ℂ) → P} {Λ : Submodule ℤ (Fin g → ℂ)}

private theorem eq_zero_of_smul_mem (hd : DiscreteTopology Λ) {z : Fin g → ℂ} (hz : ∀ t : ℂ, t • z ∈ Λ) : z = 0 := by
  have hc : Continuous fun t : ℂ => (⟨t • z, hz t⟩ : Λ) := by fun_prop
  have h := (IsLocallyConstant.iff_continuous _).2 hc |>.apply_eq_of_preconnectedSpace 1 0
  simpa using congrArg Subtype.val h

private theorem e_zero (hadd : ∀ z w, e (z + w) = e z * e w) : e 0 = 1 := by
  have h := hadd 0 0
  rw [add_zero] at h
  simpa using h.symm

private def eHom (hadd : ∀ z w, e (z + w) = e z * e w) : (Fin g → ℂ) →+ Additive P where
  toFun z := Additive.ofMul (e z)
  map_zero' := by rw [e_zero hadd]; rfl
  map_add' z w := by rw [hadd]; rfl

private theorem e_sub (hadd : ∀ z w, e (z + w) = e z * e w) (z w : Fin g → ℂ) : e (z - w) = e z * (e w)⁻¹ := by
  have h := hadd (z - w) w
  rw [sub_add_cancel] at h
  rw [h, mul_inv_cancel_right]

private theorem e_nsmul (hadd : ∀ z w, e (z + w) = e z * e w) (k : ℕ) (z : Fin g → ℂ) : e (k • z) = e z ^ k :=
  congrArg Additive.toMul (map_nsmul (eHom hadd) k z)

private theorem e_sum (hadd : ∀ z w, e (z + w) = e z * e w) {Idx : Type} (s : Finset Idx) (f : Idx → Fin g → ℂ) :
    e (s.sum f) = s.prod (fun i => e (f i)) :=
  congrArg Additive.toMul (map_sum (eHom hadd) f s)

private theorem mem_of_eq (hadd : ∀ z w, e (z + w) = e z * e w) (hker : ∀ z, e z = 1 ↔ z ∈ Λ) {z w : Fin g → ℂ}
    (h : e z = e w) : z - w ∈ Λ := by
  rw [← hker, e_sub hadd, h, mul_inv_cancel]

private theorem rigid (hadd : ∀ z w, e (z + w) = e z * e w) (hker : ∀ z, e z = 1 ↔ z ∈ Λ) (hd : DiscreteTopology Λ)
    {W : Type} [AddCommGroup W] [Module ℂ W] (M M' : W →ₗ[ℂ] (Fin g → ℂ)) (h : ∀ z, e (M z) = e (M' z)) :
    M = M' := by
  ext1 z
  have := eq_zero_of_smul_mem hd (z := M z - M' z) fun t => by
    have := mem_of_eq hadd hker (h (t • z))
    rwa [map_smul, map_smul, ← smul_sub] at this
  exact sub_eq_zero.1 this

end Unif

private theorem comp_prod' {S : Scheme.{0}} {T A B : Over S} [MonObj B] [IsCommMonObj B] {Idx : Type} (s : Finset Idx)
    (x : T ⟶ A) (f : Idx → (A ⟶ B)) : x ≫ s.prod f = s.prod (fun i => x ≫ f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, MonObj.comp_mul, ih]

private theorem exists_widePullback_of_iteratedLine {P : Type} [CommGroup P] {p : ℕ} (f : Fin p ⊕ Fin 0 → P) (g : Fin p → P)
    (h : ∀ a, g a = f (Sum.inl a)) :
    (List.ofFn fun j : Fin (p + 0) => f (finSumFinEquiv.symm j)).prod * (∏ a, g a)⁻¹ = 1 := by
  rw [List.prod_ofFn, Equiv.prod_comp finSumFinEquiv.symm f, Fintype.prod_sum_type, mul_inv_eq_one]
  simp [h]

theorem _root_.GlobalTheory.T.cm_torsion_mem_closure_generators : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0) (n : ℕ), 0 < n →
    ∀ y : Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ X.B.t.G, y ^ n = 1 →
    y ∈ Submonoid.closure {w : Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ X.B.t.G |
      ∃ (m : ℕ) (x : Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ (X.A true).t.G) (z : Fin p → 𝓞 E),
        0 < m ∧ x ^ (n * m) = 1 ∧
        (∀ x' : Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ (X.A true).t.G, x' ^ m = 1 →
          x' ≫ ∏ a, ((X.A true).t.act.act (z a) ≫ GlobalTheory.FlatCM.phiP X a) = 1) ∧
        w = x ≫ ∏ a, ((X.A true).t.act.act (z a) ≫ GlobalTheory.FlatCM.phiP X a)} := by
  intro E _ _ _ H _ K _ _ ρ σ₁ p X n hn y hy
  classical
  obtain ⟨ΛA, ΛB, eA, eB, hAadd, hAsurj, hAker, hAd, hAf, hBadd, hBsurj, hBker, hBd, lA, lB, lJ⟩ :=
    exists_unif_points (spMap (σ₁.comp (algebraMap (𝓞 K) K))) (X.A true).pol X.B.pol
  choose αA hαA using fun s => lA ((X.A true).t.act.act s) ((X.A true).t.act.hom s)
  choose αB hαB using fun s => lB (X.B.t.act.act s) (X.B.t.act.hom s)
  choose J hJ using fun a : Fin p => lJ (GlobalTheory.FlatCM.phiP X a) (X.lin (Sum.inl a)).isMonHom
  have hdim : 2 * (X.A true).g ≤ Module.finrank ℚ E := by
    rw [GlobalTheory.CMSharedCompare.dim_eq (X.A true) X.split X.typeP X.ρ_sq]
    omega
  have act0 : ∀ {G : Over (Sp (𝓞 K))} [GrpObj G] (a : OAct (𝓞 E) G), a.act 0 = 1 := by
    intro G _ a
    have h := a.add 0 0
    rw [add_zero] at h
    simpa using h.symm

  let αA' : 𝓞 E →+* Module.End ℂ (Fin (X.A true).g → ℂ) :=
    { toFun := αA
      map_one' := rigid hAadd hAker hAd _ _ fun z => by
        rw [hαA, (X.A true).t.act.one, Category.comp_id]; rfl
      map_mul' := fun s t => rigid hAadd hAker hAd _ _ fun z => by
        show eA (αA (s * t) z) = eA (αA s (αA t z))
        rw [hαA, hαA, hαA, Category.assoc, ← (X.A true).t.act.mul, mul_comm]
      map_zero' := rigid hAadd hAker hAd _ _ fun z => by
        show eA (αA 0 z) = eA 0
        rw [hαA, act0, MonObj.comp_one, e_zero hAadd]
      map_add' := fun s t => rigid hAadd hAker hAd _ _ fun z => by
        show eA (αA (s + t) z) = eA (αA s z + αA t z)
        rw [hαA, hAadd, hαA, hαA, (X.A true).t.act.add, MonObj.comp_mul] }
  let αB' : 𝓞 E →+* Module.End ℂ (Fin X.B.g → ℂ) :=
    { toFun := αB
      map_one' := rigid hBadd hBker hBd _ _ fun z => by
        rw [hαB, X.B.t.act.one, Category.comp_id]; rfl
      map_mul' := fun s t => rigid hBadd hBker hBd _ _ fun z => by
        show eB (αB (s * t) z) = eB (αB s (αB t z))
        rw [hαB, hαB, hαB, Category.assoc, ← X.B.t.act.mul, mul_comm]
      map_zero' := rigid hBadd hBker hBd _ _ fun z => by
        show eB (αB 0 z) = eB 0
        rw [hαB, act0, MonObj.comp_one, e_zero hBadd]
      map_add' := fun s t => rigid hBadd hBker hBd _ _ fun z => by
        show eB (αB (s + t) z) = eB (αB s z + αB t z)
        rw [hαB, hBadd, hαB, hαB, X.B.t.act.add, MonObj.comp_mul] }
  have lin : ∀ a, Serre.IsLinearHom (X.A true).t.act X.B.t.act (GlobalTheory.FlatCM.phiP X a) := fun a => X.lin (Sum.inl a)
  have stabA : ∀ s, ∀ z ∈ ΛA, αA' s z ∈ ΛA := fun s z hz => by
    have := (X.A true).t.act.hom s
    rw [← hAker] at hz ⊢
    show eA (αA s z) = 1
    rw [hαA, hz, MonObj.one_comp]
  have stabB : ∀ s, ∀ z ∈ ΛB, αB' s z ∈ ΛB := fun s z hz => by
    have := X.B.t.act.hom s
    rw [← hBker] at hz ⊢
    show eB (αB s z) = 1
    rw [hαB, hz, MonObj.one_comp]
  have inter : ∀ a s z, J a (αA' s z) = αB' s (J a z) := fun a s z => by
    have h := rigid hBadd hBker hBd ((J a).comp (αA s)) ((αB s).comp (J a)) fun z => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hJ, hαA, hαB, hJ, Category.assoc, (lin a).comm,
        Category.assoc]
    exact congrArg (fun M : (Fin (X.A true).g → ℂ) →ₗ[ℂ] (Fin X.B.g → ℂ) => M z) h
  have hJΛ : ∀ a, ∀ z ∈ ΛA, J a z ∈ ΛB := fun a z hz => by
    have := (lin a).isMonHom
    rw [← hAker] at hz
    rw [← hBker, hJ, hz, MonObj.one_comp]
  have honto : ∀ w, ∃ v : Fin p → (Fin (X.A true).g → ℂ), w - ∑ a, J a (v a) ∈ ΛB := by
    intro w
    obtain ⟨x, hx⟩ := X.onto (eB w)
    choose v hv using fun a : Fin p => hAsurj (x (Sum.inl a))
    refine ⟨v, (hBker _).1 ?_⟩
    rw [e_sub hBadd, e_sum hBadd, hx]
    exact exists_widePullback_of_iteratedLine (fun j : Fin p ⊕ Fin 0 => (x j ≫ X.φ j :
      Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ X.B.t.G)) (fun a => eB (J a (v a)))
      fun a => (hJ a (v a)).trans (congrArg (· ≫ GlobalTheory.FlatCM.phiP X a) (hv a))
  have hG : ∀ (u : Fin (X.A true).g → ℂ) (z : Fin p → 𝓞 E),
      eA u ≫ ∏ a, ((X.A true).t.act.act (z a) ≫ GlobalTheory.FlatCM.phiP X a) = eB (∑ a, J a (αA' (z a) u)) := by
    intro u z
    rw [comp_prod', e_sum hBadd]
    refine Finset.prod_congr rfl fun a _ => ?_
    show _ = eB (J a (αA (z a) u))
    rw [hJ, hαA, Category.assoc]
  obtain ⟨w, rfl⟩ := hBsurj y
  have hnw : n • w ∈ ΛB := (hBker _).1 (by rw [e_nsmul hBadd, hy])
  have hcl := lattice_mem_closure E (X.A true).g X.B.g p ΛA ΛB αA' αB' J hdim hAd hAf hBd
    stabA stabB inter hJΛ honto _ hnw
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have key : ∀ l ∈ AddSubmonoid.closure {w : Fin X.B.g → ℂ | ∃ (m : ℕ) (z : Fin p → 𝓞 E) (x : Fin (X.A true).g → ℂ),
      0 < m ∧ x ∈ ΛA ∧ (∀ x' ∈ ΛA, (m : ℂ)⁻¹ • ∑ a, J a (αA' (z a) x') ∈ ΛB) ∧
        w = (m : ℂ)⁻¹ • ∑ a, J a (αA' (z a) x)},
      eB ((n : ℂ)⁻¹ • l) ∈ Submonoid.closure {w : Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ X.B.t.G |
        ∃ (m : ℕ) (x : Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ (X.A true).t.G) (z : Fin p → 𝓞 E),
          0 < m ∧ x ^ (n * m) = 1 ∧
          (∀ x' : Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ (X.A true).t.G, x' ^ m = 1 →
            x' ≫ ∏ a, ((X.A true).t.act.act (z a) ≫ GlobalTheory.FlatCM.phiP X a) = 1) ∧
          w = x ≫ ∏ a, ((X.A true).t.act.act (z a) ≫ GlobalTheory.FlatCM.phiP X a)} := by
    intro l hl
    induction hl using AddSubmonoid.closure_induction with
    | mem t ht =>
      obtain ⟨m, z, x, hm, hx, hkill, rfl⟩ := ht
      have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
      refine Submonoid.subset_closure ⟨m, eA (((n * m : ℕ) : ℂ)⁻¹ • x), z, hm, ?_, ?_, ?_⟩
      · rw [← e_nsmul hAadd, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
          mul_inv_cancel₀ (by exact_mod_cast (Nat.mul_pos hn hm).ne'), one_smul]
        exact (hAker x).2 hx
      · intro x' hx'
        obtain ⟨u, rfl⟩ := hAsurj x'
        have hu : m • u ∈ ΛA := (hAker _).1 (by rw [e_nsmul hAadd, hx'])
        have h := hkill _ hu
        have e1 : (m : ℂ)⁻¹ • ∑ a, J a (αA' (z a) (m • u)) = ∑ a, J a (αA' (z a) u) := by
          simp only [map_nsmul, ← Finset.smul_sum]
          rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hm0, one_smul]
        rw [e1] at h
        rw [hG, (hBker _).2 h]
      · rw [hG]
        congr 1
        simp only [map_smul, ← Finset.smul_sum, smul_smul, Nat.cast_mul, mul_inv]
    | zero => rw [smul_zero, e_zero hBadd]; exact Submonoid.one_mem _
    | add a b _ _ ha hb => rw [smul_add, hBadd]; exact Submonoid.mul_mem _ ha hb
  have := key _ hcl
  rwa [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hn0, one_smul] at this

end GlobalTheory.FlatCM.CplxGen

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomKillsTorsionOfComplexPointsOneEmbedding
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomKillsTorsionOfComplexPointsOneEmbedding
open NumberField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.TorsionKill

theorem eq_of_pullback_eq {S S' : Scheme.{0}} (t : S' ⟶ S) [IsSchemeTheoreticallyDominant t]
    [QuasiCompact t] {Y X : Over S} [Flat Y.hom] [IsSeparated X.hom] {a b : Y ⟶ X}
    (h : (Over.pullback t).map a = (Over.pullback t).map b) : a = b := by
  apply Over.OverMorphism.ext
  refine GlobalTheory.KernelNoTorsion.eq_of_isSchemeTheoreticallyDominant X.hom ((Over.w a).trans (Over.w b).symm)
    (pullback.fst Y.hom t) ?_
  have h' := congr(($h).left ≫ pullback.fst X.hom t)
  exact (pullback.lift_fst _ _ _).symm.trans (h'.trans (pullback.lift_fst _ _ _))

theorem isSchemeTheoreticallyDominant_complexPoint (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) :
    IsSchemeTheoreticallyDominant (spMap (σ.comp (algebraMap (𝓞 K) K))) := by
  have : IsDominant (spMap (σ.comp (algebraMap (𝓞 K) K))) := by
    rw [isDominant_iff]
    refine (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr ?_
    have hinj : Function.Injective (σ.comp (algebraMap (𝓞 K) K)) := by
      rw [RingHom.coe_comp]; exact σ.injective.comp (IsFractionRing.injective (𝓞 K) K)
    exact ((RingHom.injective_iff_ker_eq_bot _).mp hinj).le.trans bot_le
  exact IsSchemeTheoreticallyDominant.of_isDominant _

theorem flat_ker (S : Scheme.{0}) (P : Out.PolAV S) (m : ℕ) (hm : 1 ≤ m) :
    Flat (pullback (𝟙 P.A ^ m) η[P.A]).hom := by
  have gi := GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected
  have hfin : IsFinite ((𝟙 P.A ^ m)).left := GlobalTheory.MulFinite.isFinite_mulA
    (GlobalTheory.MulPull.mulPull_of_cube_of_symm GlobalTheory.AbLaw.CubeAssembly.cube_gen
      (GlobalTheory.exists_gen_negLB GlobalTheory.laws_without_cohomology.1)).1 GlobalTheory.laws_without_cohomology.2.2.1 gi S P m hm
  have hc := P.isAb.comm
  have hsm := P.isAb.smooth
  have hmon := GlobalTheory.AbLaw.MulN.isMonHom_mulA P.A m
  have hgeo : ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S),
      Flat ((Over.pullback t).map ((𝟙 P.A ^ m))).left ∧
        Surjective ((Over.pullback t).map ((𝟙 P.A ^ m))).left := fun K _ _ t =>
    GlobalTheory.flat_and_surjective_of_isFinite_abelianEnd gi K _
      (ReciprocityTheory.ChartRestriction.G.Out.TLinPf.isAb_pullback t P.A P.isAb) _ inferInstance
      (MorphismProperty.of_isPullback (P := @IsFinite) (GlobalTheory.AbLaw.MulN.isPullback_baseChange t _) hfin)
  have hf := GlobalTheory.flat_of_isFinite_of_finitePresentation_of_flat_geometric_fibres S _ _ _ inferInstance inferInstance
    inferInstance hfin fun K _ _ t => (hgeo K t).1
  have hp := (IsPullback.of_hasPullback (𝟙 P.A ^ m) η[P.A]).map (Over.forget S)
  have he : Flat (pullback.snd (𝟙 P.A ^ m) η[P.A]).left :=
    MorphismProperty.of_isPullback (P := @Flat) hp hf
  have hw : (pullback.snd (𝟙 P.A ^ m) η[P.A]).left = (pullback (𝟙 P.A ^ m) η[P.A]).hom := by
    simpa using Over.w (pullback.snd (𝟙 P.A ^ m) η[P.A])
  rw [hw] at he
  exact he

theorem kill_complex (A' B' : Over (Sp ℂ)) [GrpObj A'] [GrpObj B'] (hA : IsAbelianScheme A')
    [IsSeparated B'.hom] [LocallyOfFiniteType B'.hom] (N : ℕ) (hN : 1 ≤ N) (φ : A' ⟶ B')
    (h : ∀ p : Over.mk (𝟙 (Sp ℂ)) ⟶ pullback (𝟙 A' ^ N) η[A'],
      p ≫ pullback.fst (𝟙 A' ^ N) η[A'] ≫ φ = p ≫ 1) :
    pullback.fst (𝟙 A' ^ N) η[A'] ≫ φ = 1 := by
  have hunit : IsUnit ((N : ℕ) : Γ(Sp ℂ, ⊤)) := by
    have := (IsUnit.mk0 (N : ℂ) (by exact_mod_cast (show N ≠ 0 by omega))).map
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
    rwa [map_natCast] at this
  obtain ⟨-, -, het, -⟩ := abelianScheme_id_pow_finite_etale_surjective _ A' N hA hunit
  have hp := (IsPullback.of_hasPullback ((𝟙 A' ^ N)) η[A']).map (Over.forget (Sp ℂ))
  have he : Etale (pullback.snd ((𝟙 A' ^ N)) η[A']).left :=
    MorphismProperty.of_isPullback (P := @Etale) hp het
  have hw : (pullback.snd ((𝟙 A' ^ N)) η[A']).left = (pullback (𝟙 A' ^ N) η[A']).hom := by
    simpa using Over.w (pullback.snd ((𝟙 A' ^ N)) η[A'])
  rw [hw] at he
  have : IsReduced (pullback (𝟙 A' ^ N) η[A']).left :=
    GlobalTheory.isReduced_of_smooth_of_isReduced (pullback (𝟙 A' ^ N) η[A']).hom
  refine Over.OverMorphism.ext ?_
  have : LocallyOfFiniteType ((pullback.fst (𝟙 A' ^ N) η[A'] ≫ φ).left ≫ B'.hom) := by
    rw [Over.w]; infer_instance
  refine ext_of_apply_eq B'.hom Set.univ isClosed_univ.isLocallyClosed dense_univ (fun z _ hz => ?_)
    ((Over.w _).trans (Over.w _).symm)
  let p : Over.mk (𝟙 (Sp ℂ)) ⟶ pullback (𝟙 A' ^ N) η[A'] :=
    Over.homMk (pointOfClosedPoint (pullback (𝟙 A' ^ N) η[A']).hom z hz) (pointOfClosedPoint_comp _ _ _)
  have e := h p
  have e' := congrArg (fun q => q.left (IsLocalRing.closedPoint ℂ)) e
  have hz' : p.left (IsLocalRing.closedPoint ℂ) = z := pointOfClosedPoint_apply _ z hz _
  simp only [Over.comp_left] at e'
  rw [← hz']
  exact e'

end GlobalTheory.TorsionKill

noncomputable section
namespace GlobalTheory.TorsionKill

def ptOf {S : Scheme.{0}} (t : Sp ℂ ⟶ S) {A : Over S}
    (y : Over.mk (𝟙 (Sp ℂ)) ⟶ (Over.pullback t).obj A) : Over.mk t ⟶ A :=
  Over.homMk (y.left ≫ pullback.fst A.hom t) (by
    have hy : y.left ≫ pullback.snd A.hom t = 𝟙 _ := by simpa using Over.w y
    simp only [Over.mk_hom, Category.assoc, pullback.condition, reassoc_of% hy, Category.id_comp])

theorem ptOf_comp {S : Scheme.{0}} (t : Sp ℂ ⟶ S) {A B : Over S}
    (y : Over.mk (𝟙 (Sp ℂ)) ⟶ (Over.pullback t).obj A) (f : A ⟶ B) :
    ptOf t (y ≫ (Over.pullback t).map f) = ptOf t y ≫ f := by
  ext
  simp [ptOf, pullback.lift_fst]

theorem ptOf_injective {S : Scheme.{0}} (t : Sp ℂ ⟶ S) {A : Over S} :
    Function.Injective (ptOf t (A := A)) := by
  intro y y' h
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact congrArg (fun q => q.left) h
  · have hy : y.left ≫ pullback.snd A.hom t = 𝟙 _ := by simpa using Over.w y
    have hy' : y'.left ≫ pullback.snd A.hom t = 𝟙 _ := by simpa using Over.w y'
    rw [hy, hy']

set_option synthInstance.maxHeartbeats 100000 in
theorem ptOf_one {S : Scheme.{0}} (t : Sp ℂ ⟶ S) {A : Over S} [GrpObj A] :
    ptOf t (1 : Over.mk (𝟙 (Sp ℂ)) ⟶ (Over.pullback t).obj A) = 1 := by
  have e : (1 : Over.mk (𝟙 (Sp ℂ)) ⟶ (Over.pullback t).obj A) =
      (toUnit _ ≫ Functor.LaxMonoidal.ε (Over.pullback t)) ≫ (Over.pullback t).map η[A] := by
    rw [Hom.one_def, Category.assoc]; rfl
  rw [e, ptOf_comp, Hom.one_def, toUnit_unique (ptOf t _) (toUnit _)]

end GlobalTheory.TorsionKill

noncomputable section
namespace GlobalTheory.TorsionKill

theorem kill_torsion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (A B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (G : A.t.G ⟶ B.t.G),
    IsMonHom G → ∀ m : ℕ, 0 < m →
    (∀ x : Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ A.t.G, x ^ m = 1 → x ≫ G = 1) →
    ∀ (T : Over (Sp (𝓞 K))) (x : T ⟶ A.t.G), x ^ m = 1 → x ≫ G = 1 := by
  intro E _ _ _ H K _ _ σ A B G _ m hm hpt T x hx
  let inc : pullback (𝟙 A.t.G ^ m) η[A.t.G] ⟶ A.t.G := pullback.fst _ _
  suffices hY : inc ≫ G = 1 by
    have hx' : x ≫ (𝟙 A.t.G ^ m) = toUnit T ≫ η[A.t.G] := by
      rw [MonObj.comp_pow, Category.comp_id]; exact hx
    rw [← pullback.lift_fst x (toUnit T) hx', Category.assoc]
    change _ ≫ inc ≫ G = 1
    rw [hY, MonObj.comp_one]
  have := flat_ker _ A.pol m hm
  have := isSchemeTheoreticallyDominant_complexPoint K σ
  have := B.ab.proper
  have := A.ab.proper
  have : IsSeparated B.t.G.hom := inferInstance
  refine eq_of_pullback_eq (spMap (σ.comp (algebraMap (𝓞 K) K))) ?_
  set t := spMap (σ.comp (algebraMap (𝓞 K) K)) with ht
  let F := Over.pullback t
  have hA' : IsAbelianScheme (F.obj A.t.G) := ReciprocityTheory.ChartRestriction.G.Out.TLinPf.isAb_pullback t A.t.G A.ab
  have : IsSeparated (F.obj B.t.G).hom := by change IsSeparated (pullback.snd _ _); infer_instance
  have : LocallyOfFiniteType (F.obj B.t.G).hom := by change LocallyOfFiniteType (pullback.snd _ _); infer_instance
  have hpow : F.map (𝟙 A.t.G ^ m) = 𝟙 (F.obj A.t.G) ^ m := by
    simpa using map_pow (F.homMonoidHom (X := A.t.G) (M := A.t.G)) (𝟙 A.t.G) m
  have hinc : inc ≫ (𝟙 A.t.G ^ m) = 1 := by
    rw [show inc ≫ (𝟙 A.t.G ^ m) = pullback.snd (𝟙 A.t.G ^ m) η[A.t.G] ≫ η[A.t.G] from pullback.condition,
      toUnit_unique (pullback.snd (𝟙 A.t.G ^ m) η[A.t.G]) (toUnit _)]
    rfl
  have hFinc : F.map inc ≫ (𝟙 (F.obj A.t.G) ^ m) = toUnit _ ≫ η[F.obj A.t.G] := by
    rw [← hpow, ← F.map_comp, hinc, Functor.map_one]; rfl
  have key := kill_complex (F.obj A.t.G) (F.obj B.t.G) hA' m hm (F.map G) (fun p => by
    let y := p ≫ pullback.fst (𝟙 (F.obj A.t.G) ^ m) η[F.obj A.t.G]
    have hy1 : y ≫ 𝟙 (F.obj A.t.G) ^ m = 1 := by
      have c : pullback.fst (𝟙 (F.obj A.t.G) ^ m) η[F.obj A.t.G] ≫ 𝟙 (F.obj A.t.G) ^ m =
          pullback.snd (𝟙 (F.obj A.t.G) ^ m) η[F.obj A.t.G] ≫ η[F.obj A.t.G] := pullback.condition
      simp only [y, Category.assoc, c]
      rw [← Category.assoc, toUnit_unique (p ≫ pullback.snd _ _) (toUnit _)]
      rfl
    have hyp : ptOf t y ^ m = 1 := by
      rw [← Category.comp_id (ptOf t y), ← MonObj.comp_pow, ← ptOf_comp, hpow, hy1, ptOf_one]
    have h2 : ptOf t (y ≫ F.map G) = ptOf t 1 := by
      rw [ptOf_comp, ptOf_one]; exact hpt _ hyp
    have h3 := ptOf_injective t h2
    simp only [y, Category.assoc] at h3
    rw [h3, MonObj.comp_one])
  have hl : F.map inc = pullback.lift (F.map inc) (toUnit _) hFinc ≫ pullback.fst _ _ :=
    (pullback.lift_fst _ _ _).symm
  rw [F.map_comp, Functor.map_one, hl, Category.assoc, key, MonObj.comp_one]

end GlobalTheory.TorsionKill
end
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomKillsTorsionOfComplexPointsOneEmbeddingStatement
open NumberField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hom_kills_torsion_of_complexPoints_oneEmbedding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (A B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (G : A.t.G ⟶ B.t.G),
    IsMonHom G → ∀ m : ℕ, 0 < m →
    (∀ x : Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ A.t.G, x ^ m = 1 → x ≫ G = 1) →
    ∀ (T : Over (Sp (𝓞 K))) (x : T ⟶ A.t.G), x ^ m = 1 → x ≫ G = 1 := by
  first | exact @GlobalTheory.TorsionKill.kill_torsion | exact GlobalTheory.TorsionKill.kill_torsion | (intros; apply GlobalTheory.TorsionKill.kill_torsion <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionCmUnitaryShimuraMemClosureLinearHomImages
set_option autoImplicit false

open NumberField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM

noncomputable section

namespace GlobalTheory.FlatCM.TorsGen

theorem exists_linear_pow_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (A B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (G : A.t.G ⟶ B.t.G),
    GlobalTheory.Serre.IsLinearHom A.t.act B.t.act G → ∀ m : ℕ, 0 < m →
    (∀ x : Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ A.t.G, x ^ m = 1 → x ≫ G = 1) →
    ∃ F : A.t.G ⟶ B.t.G, GlobalTheory.Serre.IsLinearHom A.t.act B.t.act F ∧ F ^ m = G := by
  intro E _ _ _ H K _ _ σ A B G hG m hm hker
  have hGm := hG.isMonHom
  obtain ⟨_, hfl, hsu, -⟩ := GlobalTheory.abelianSchemeLaws_all.1.mulN (Sp (𝓞 K)) A.pol m hm
  have : Flat (ReciprocityTheory.ChartRestriction.G.Out.mulA A.t.G m).left := hfl
  have : Surjective (ReciprocityTheory.ChartRestriction.G.Out.mulA A.t.G m).left := hsu
  have hc : IsCommMonObj A.t.G := A.ab.comm
  have hcB : IsCommMonObj B.t.G := B.ab.comm
  have hall := GlobalTheory.T.hom_kills_torsion_of_complexPoints_oneEmbedding E H K σ A B G hGm m hm hker
  obtain ⟨F, hF⟩ := GlobalTheory.DivisibleHom.exists_factor (A := A.t.G) m G hall
  have hFm : IsMonHom (ReciprocityTheory.ChartRestriction.G.Out.mulA A.t.G m ≫ F) := hF ▸ hGm
  have : IsMonHom F := GlobalTheory.DivisibleHom.isMonHom_of_factor m F
  refine ⟨F, ⟨this, fun c => ?_⟩, by rw [← hF, GlobalTheory.DivisibleHom.mulA_comp]⟩
  have := A.t.act.hom c
  have := B.t.act.hom c
  apply GlobalTheory.DivisibleHom.cancel_of_flat_surjective (ReciprocityTheory.ChartRestriction.G.Out.mulA A.t.G m)
  rw [← Category.assoc, GlobalTheory.DivisibleHom.mulA_comp, ← GlobalTheory.DivisibleHom.comp_mulA, Category.assoc, hF, hG.comm,
    ← Category.assoc, hF]

theorem gen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0) (n : ℕ), 0 < n →
    ∀ y : Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ X.B.t.G, y ^ n = 1 →
    y ∈ Submonoid.closure {w : Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ X.B.t.G |
      ∃ (x : Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ (X.A true).t.G) (f : (X.A true).t.G ⟶ X.B.t.G),
        x ^ n = 1 ∧ GlobalTheory.Serre.IsLinearHom (X.A true).t.act X.B.t.act f ∧
        (∃ m : ℕ, 0 < m ∧ ∃ z : Fin p → 𝓞 E, f ^ m = ∏ a, ((X.A true).t.act.act (z a) ≫ GlobalTheory.FlatCM.phiP X a)) ∧
        w = x ≫ f} := by
  intro E _ _ _ H hH K _ _ ρ σ₁ p X n hn y hy
  refine Submonoid.closure_mono ?_ (GlobalTheory.T.cm_torsion_mem_closure_generators E H hH K ρ σ₁ p X n hn y hy)
  rintro w ⟨m, x, z, hm, hx, hG, rfl⟩
  obtain ⟨F, hF, hFm⟩ := exists_linear_pow_eq E H K σ₁ (X.A true) X.B _
    (GlobalTheory.FlatCM.HomLat.isLinearHom_prod X z) m hm hG
  have := hF.isMonHom
  refine ⟨x ^ m, F, ?_, hF, ⟨m, hm, z, hFm⟩, ?_⟩
  · rw [← pow_mul, mul_comm, hx]
  · rw [← hFm, MonObj.comp_pow, MonObj.pow_comp]

end GlobalTheory.FlatCM.TorsGen

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionCmUnitaryShimuraMemClosureLinearHomImagesStatement
open NumberField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_cmUnitaryShimura_mem_closure_linearHom_images : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0) (n : ℕ), 0 < n →
    ∀ y : Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ X.B.t.G, y ^ n = 1 →
    y ∈ Submonoid.closure {w : Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ X.B.t.G |
      ∃ (x : Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ (X.A true).t.G) (f : (X.A true).t.G ⟶ X.B.t.G),
        x ^ n = 1 ∧ GlobalTheory.Serre.IsLinearHom (X.A true).t.act X.B.t.act f ∧
        (∃ m : ℕ, 0 < m ∧ ∃ z : Fin p → 𝓞 E, f ^ m = ∏ a, ((X.A true).t.act.act (z a) ≫ GlobalTheory.FlatCM.phiP X a)) ∧
        w = x ≫ f} := by
  first | exact @GlobalTheory.FlatCM.TorsGen.gen | exact GlobalTheory.FlatCM.TorsGen.gen | (intros; apply GlobalTheory.FlatCM.TorsGen.gen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearHomKillsTorsionOfWeilPairingDivisible
set_option autoImplicit false

open NumberField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM

noncomputable section

namespace GlobalTheory.FlatCM.TorsKill

section Act

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {O : Type} [CommRing O] (o : OAct O G) {T : Over S}

theorem comp_act_zero (x : T ⟶ G) : x ≫ o.act 0 = 1 := by
  have h : x ≫ o.act (0 + 0) = (x ≫ o.act 0) * (x ≫ o.act 0) := by rw [o.add, MonObj.comp_mul]
  rw [add_zero] at h
  exact mul_left_cancel (a := x ≫ o.act 0) (by rw [_root_.mul_one]; exact h.symm)

theorem comp_act_nat (x : T ⟶ G) (n : ℕ) : x ≫ o.act (n : O) = x ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, pow_zero, comp_act_zero]
  | succ n ih => rw [Nat.cast_succ, o.add, MonObj.comp_mul, ih, o.one, Category.comp_id, pow_succ]

theorem comp_act_nat_mul (x : T ⟶ G) (n : ℕ) (hx : x ^ n = 1) (r : O) : x ≫ o.act ((n : O) * r) = 1 := by
  have := o.hom r
  rw [o.mul, ← Category.assoc, comp_act_nat, hx, MonObj.one_comp]

end Act

theorem weilIs_one_left (hW : Out.WeilSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : Out.PolAV S) {T : Over S}
    (k : ℕ) (y : T ⟶ P.A) (hy : y ^ k = 1) : Out.WeilIs P.A P.L k 1 y 1 := by
  obtain ⟨e, he, hu⟩ := (hW S P k T).1 1 y (one_pow k) hy
  have h2 := (hW S P k T).2.1 1 1 y e e he he
  rw [_root_.one_mul] at h2
  have h3 : e * e = e := hu _ h2
  have he1 : e = 1 := mul_left_cancel (a := e) (by rw [_root_.mul_one]; exact h3)
  rwa [he1] at he

theorem kill : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0) (ψ : (X.A true).t.G ⟶ X.B.t.G),
    GlobalTheory.Serre.IsLinearHom (X.A true).t.act X.B.t.act ψ → ∀ n : ℕ, 0 < n →
    (∀ f : (X.A true).t.G ⟶ X.B.t.G, GlobalTheory.Serre.IsLinearHom (X.A true).t.act X.B.t.act f →
      (∃ m : ℕ, 0 < m ∧ ∃ z : Fin p → 𝓞 E, f ^ m = ∏ a, ((X.A true).t.act.act (z a) ≫ GlobalTheory.FlatCM.phiP X a)) →
      ∃ r : 𝓞 E, GlobalTheory.CM.WeilEq X.B.t.PP.L f ψ (X.A true).t.PP.L ((X.A true).t.act.act ((n : 𝓞 E) * r)) (𝟙 _)
        (spMap (σ₁.comp (algebraMap (𝓞 K) K)))) →
    ∀ u : Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ (X.A true).t.G, u ^ n = 1 → u ≫ ψ = 1 := by
  intro E _ _ _ H hH K _ _ ρ σ₁ p X ψ hψ n hn hWe u hu
  have laws := GlobalTheory.lawsFieldsSeparately
  have hWS : Out.WeilSt := laws.2.2.2.2.2.2.2.2.2.1
  have hND : Out.WeilNondegSt := laws.2.2.2.2.2.2.2.2.2.2.1
  have hBC : Out.PolBaseChangeSt := laws.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have u1 : unitOn (1 : ℂˣ) = 1 := map_one _

  have hgen : ∀ (x : Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ (X.A true).t.G)
      (f : (X.A true).t.G ⟶ X.B.t.G), x ^ n = 1 → Serre.IsLinearHom (X.A true).t.act X.B.t.act f →
      (∃ m : ℕ, 0 < m ∧ ∃ z : Fin p → 𝓞 E, f ^ m = ∏ a, ((X.A true).t.act.act (z a) ≫ GlobalTheory.FlatCM.phiP X a)) →
      Out.WeilIs X.B.pol.A X.B.pol.L n (x ≫ f) (u ≫ ψ) 1 := by
    intro x f hx hf hm
    obtain ⟨r, hr⟩ := hWe f hf hm
    have h := (hr n x u 1 hn hx hu).2
    rw [u1] at h
    apply h
    rw [comp_act_nat_mul _ x n hx r, Category.comp_id]
    exact weilIs_one_left hWS (X.A true).pol n u hu
  have hall : ∀ y : Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ X.B.t.G, y ^ n = 1 →
      Out.WeilIs X.B.pol.A X.B.pol.L n (u ≫ ψ) y 1 := by
    intro y hy
    have hψn : (u ≫ ψ) ^ n = 1 := GlobalTheory.LevelRigid.pairing_tors u ψ hψ.isMonHom n hu
    suffices h : Out.WeilIs X.B.pol.A X.B.pol.L n y (u ≫ ψ) 1 by
      have := GlobalTheory.CommPairing.weilIs_symm X.B.pol.isLB h
      rwa [inv_one] at this
    have hmem := GlobalTheory.T.torsion_cmUnitaryShimura_mem_closure_linearHom_images E H hH K ρ σ₁ p X n hn y hy
    clear hy
    induction hmem using Submonoid.closure_induction with
    | mem w hw =>
      obtain ⟨x, f, hx, hf, hm, rfl⟩ := hw
      exact hgen x f hx hf hm
    | one => exact weilIs_one_left hWS X.B.pol n (u ≫ ψ) hψn
    | mul a b _ _ ha hb =>
      have := (hWS _ X.B.pol n _).2.1 a b (u ≫ ψ) 1 1 ha hb
      rwa [_root_.mul_one] at this
  exact GlobalTheory.LevelRigid.pairing_nondeg hWS hND hBC X.B.pol ℂ _ n (Nat.cast_ne_zero.2 hn.ne') (u ≫ ψ)
    (GlobalTheory.LevelRigid.pairing_tors u ψ hψ.isMonHom n hu) hall

end GlobalTheory.FlatCM.TorsKill
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearHomKillsTorsionOfWeilPairingDivisibleStatement
open NumberField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearHom_kills_torsion_of_weilPairing_divisible : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0) (ψ : (X.A true).t.G ⟶ X.B.t.G),
    GlobalTheory.Serre.IsLinearHom (X.A true).t.act X.B.t.act ψ → ∀ n : ℕ, 0 < n →
    (∀ f : (X.A true).t.G ⟶ X.B.t.G, GlobalTheory.Serre.IsLinearHom (X.A true).t.act X.B.t.act f →
      (∃ m : ℕ, 0 < m ∧ ∃ z : Fin p → 𝓞 E, f ^ m = ∏ a, ((X.A true).t.act.act (z a) ≫ GlobalTheory.FlatCM.phiP X a)) →
      ∃ r : 𝓞 E, GlobalTheory.CM.WeilEq X.B.t.PP.L f ψ (X.A true).t.PP.L ((X.A true).t.act.act ((n : 𝓞 E) * r)) (𝟙 _)
        (spMap (σ₁.comp (algebraMap (𝓞 K) K)))) →
    ∀ u : Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ (X.A true).t.G, u ^ n = 1 → u ≫ ψ = 1 := by
  first | exact @GlobalTheory.FlatCM.TorsKill.kill | exact GlobalTheory.FlatCM.TorsKill.kill | (intros; apply GlobalTheory.FlatCM.TorsKill.kill <;> assumption)
end
