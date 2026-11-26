module

public import GroundTheory.GlobalFields.SplittingFromInequality.Decomposition
public import GroundTheory.GlobalFields.TateThesis.ChebotarevAbelian

@[expose] public section

section -- merged from GroundTheory.GlobalFields.TateThesis.ChebotarevCount
section -- merged from GroundTheory.GlobalFields.TateThesis.ChebotarevFrobenius
namespace GroundTheory.Global

open NumberField IsDedekindDomain IntermediateField
open scoped Pointwise

noncomputable section

section Unique

variable {F L : Type*} [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]
  [IsGalois F L]

theorem arithFrobAt_eq_of_isArithFrobAt (w : HeightOneSpectrum (𝓞 L))
    (he : w.asIdeal.ramificationIdx (𝓞 F) = 1) {τ : Gal(L/F)}
    (hτ : IsArithFrobAt (𝓞 F) τ w.asIdeal) : arithFrobAt (𝓞 F) Gal(L/F) w.asIdeal = τ := by
  have : IsGaloisGroup Gal(L/F) (𝓞 F) (𝓞 L) := IsGaloisGroup.of_isFractionRing _ _ _ F L
  have hmem := (IsArithFrobAt.arithFrobAt (𝓞 F) Gal(L/F) w.asIdeal).mul_inv_mem_inertia hτ
  have hcard : Nat.card (w.asIdeal.inertia Gal(L/F)) = 1 := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (w.asIdeal.under (𝓞 F)) w.asIdeal,
      Ideal.ramificationIdxIn_eq_ramificationIdx _ w.asIdeal Gal(L/F)]
    exact he
  rw [Subgroup.card_eq_one.mp hcard, Subgroup.mem_bot, mul_inv_eq_one] at hmem
  exact hmem

theorem ramificationIdx_smul (τ : Gal(L/F)) (w : HeightOneSpectrum (𝓞 L)) :
    (τ • w).asIdeal.ramificationIdx (𝓞 F) = w.asIdeal.ramificationIdx (𝓞 F) := by
  have : IsGaloisGroup Gal(L/F) (𝓞 F) (𝓞 L) := IsGaloisGroup.of_isFractionRing _ _ _ F L
  have : (τ • w).asIdeal.LiesOver (AdeleBaseChange.below (K := F) w).asIdeal :=
    (AdeleBaseChange.below_eq_iff _ _).1 (below_smul τ w)
  exact Ideal.ramificationIdx_eq_of_isGaloisGroup (AdeleBaseChange.below (K := F) w).asIdeal
    (τ • w).asIdeal w.asIdeal Gal(L/F)

theorem arithFrobAt_smul (τ : Gal(L/F)) (w : HeightOneSpectrum (𝓞 L))
    (he : w.asIdeal.ramificationIdx (𝓞 F) = 1) :
    arithFrobAt (𝓞 F) Gal(L/F) (τ • w).asIdeal =
      τ * arithFrobAt (𝓞 F) Gal(L/F) w.asIdeal * τ⁻¹ :=
  arithFrobAt_eq_of_isArithFrobAt (τ • w) (by rw [ramificationIdx_smul, he])
    ((IsArithFrobAt.arithFrobAt (𝓞 F) Gal(L/F) w.asIdeal).conj τ)

end Unique

section Tower

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem isArithFrobAt_restrictScalars_iff (E : IntermediateField K L) (w : HeightOneSpectrum (𝓞 L))
    (hf : (w.asIdeal.under (𝓞 E)).inertiaDeg (𝓞 K) = 1) (τ : Gal(L/E)) :
    IsArithFrobAt (𝓞 K) (τ.restrictScalars K) w.asIdeal ↔ IsArithFrobAt (𝓞 E) τ w.asIdeal := by
  have hcard : Nat.card (𝓞 K ⧸ w.asIdeal.under (𝓞 K)) =
      Nat.card (𝓞 E ⧸ w.asIdeal.under (𝓞 E)) := by
    have h := Ideal.absNorm_pow_inertiaDeg ((w.asIdeal.under (𝓞 E)).under (𝓞 K))
      (w.asIdeal.under (𝓞 E))
    rw [hf, pow_one, Ideal.under_under] at h
    rw [← Submodule.cardQuot_apply, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply,
      ← Ideal.absNorm_apply, h]
  change (∀ x, _ - x ^ Nat.card (𝓞 K ⧸ w.asIdeal.under (𝓞 K)) ∈ w.asIdeal) ↔
    (∀ x, _ - x ^ Nat.card (𝓞 E ⧸ w.asIdeal.under (𝓞 E)) ∈ w.asIdeal)
  rw [hcard]
  rfl

variable [IsGalois K L]

theorem eq_of_under_eq_of_le_stabilizer (H : Subgroup Gal(L/K)) (w w' : HeightOneSpectrum (𝓞 L))
    (hH : H ≤ MulAction.stabilizer Gal(L/K) w.asIdeal)
    (h : w'.asIdeal.under (𝓞 (fixedField H)) = w.asIdeal.under (𝓞 (fixedField H))) : w' = w := by
  have : IsGaloisGroup Gal(L/fixedField H) (𝓞 (fixedField H)) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing _ _ _ (fixedField H) L
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (𝓞 (fixedField H)) (𝓞 L)
    Gal(L/fixedField H) w.asIdeal w'.asIdeal h.symm
  have hgH : g.restrictScalars K ∈ H := by
    have h1 : g.restrictScalars K ∈ fixingSubgroup (fixedField H) :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx ↦ g.commutes ⟨x, hx⟩
    rwa [fixingSubgroup_fixedField] at h1
  have hs := hH hgH
  rw [MulAction.mem_stabilizer_iff] at hs
  refine HeightOneSpectrum.ext ?_
  rw [hg]
  exact hs

end Tower

end

end GroundTheory.Global
end

namespace GroundTheory.Global

open NumberField IsDedekindDomain IntermediateField AdeleBaseChange
open scoped Pointwise

noncomputable section

section Sets

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

def chebotarevSet (C : Set Gal(L/K)) : Set (HeightOneSpectrum (𝓞 K)) :=
  {v | ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal.LiesOver v.asIdeal →
    w.asIdeal.ramificationIdx (𝓞 K) = 1 ∧ arithFrobAt (𝓞 K) Gal(L/K) w.asIdeal ∈ C}


omit [IsGalois K L] in
theorem mem_fixingSubgroup_fixedField_zpowers (σ : Gal(L/K)) :
    σ ∈ fixingSubgroup (fixedField (Subgroup.zpowers σ)) := by
  rw [fixingSubgroup_fixedField]
  exact Subgroup.mem_zpowers σ

def galFixedZpowers (σ : Gal(L/K)) : Gal(L/fixedField (Subgroup.zpowers σ)) :=
  fixingSubgroupEquiv _ ⟨σ, mem_fixingSubgroup_fixedField_zpowers σ⟩

omit [IsGalois K L] in
theorem restrictScalars_galFixedZpowers (σ : Gal(L/K)) :
    (galFixedZpowers σ).restrictScalars K = σ :=
  AlgEquiv.ext fun _ ↦ rfl


omit [IsGalois K L] in
theorem restrictScalars_mem_zpowers (σ : Gal(L/K)) (g : Gal(L/fixedField (Subgroup.zpowers σ))) :
    g.restrictScalars K ∈ Subgroup.zpowers σ := by
  have h1 : g.restrictScalars K ∈ fixingSubgroup (fixedField (Subgroup.zpowers σ)) :=
    (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx ↦ g.commutes ⟨x, hx⟩
  rwa [fixingSubgroup_fixedField] at h1


omit [IsGalois K L] in
theorem isMulCommutative_gal_fixedField_zpowers (σ : Gal(L/K)) :
    IsMulCommutative Gal(L/fixedField (Subgroup.zpowers σ)) := ⟨⟨fun a b ↦ by
  apply AlgEquiv.restrictScalars_injective K
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (restrictScalars_mem_zpowers σ a)
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (restrictScalars_mem_zpowers σ b)
  have h : ∀ c d : Gal(L/fixedField (Subgroup.zpowers σ)),
      (c * d).restrictScalars K = c.restrictScalars K * d.restrictScalars K :=
    fun _ _ ↦ AlgEquiv.ext fun _ ↦ rfl
  rw [h, h, ← hi, ← hj, zpow_mul_comm]⟩⟩

theorem natCard_gal_fixedField_zpowers (σ : Gal(L/K)) :
    Nat.card Gal(L/fixedField (Subgroup.zpowers σ)) = orderOf σ := by
  rw [IsGalois.card_aut_eq_finrank, finrank_fixedField_eq_card, Nat.card_zpowers]

def deuringSet (σ : Gal(L/K)) : Set (HeightOneSpectrum (𝓞 (fixedField (Subgroup.zpowers σ)))) :=
  {u | u.asIdeal.inertiaDeg (𝓞 K) = 1 ∧ ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal.LiesOver u.asIdeal →
    w.asIdeal.ramificationIdx (𝓞 K) = 1 ∧
      arithFrobAt (𝓞 (fixedField (Subgroup.zpowers σ))) Gal(L/fixedField (Subgroup.zpowers σ))
        w.asIdeal = galFixedZpowers σ}

theorem absNorm_eq_of_inertiaDeg_eq_one {E : Type*} [Field E] [NumberField E] [Algebra K E]
    (u : HeightOneSpectrum (𝓞 E)) (hf : u.asIdeal.inertiaDeg (𝓞 K) = 1) :
    Ideal.absNorm u.asIdeal = Ideal.absNorm (HeightOneSpectrum.under (𝓞 K) u).asIdeal := by
  have h := Ideal.absNorm_pow_inertiaDeg (u.asIdeal.under (𝓞 K)) u.asIdeal
  rw [hf, pow_one] at h
  rw [HeightOneSpectrum.under_asIdeal, h]

end Sets

section Deuring

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

theorem under_mem_deuringSet (σ : Gal(L/K)) (w : HeightOneSpectrum (𝓞 L))
    (he : w.asIdeal.ramificationIdx (𝓞 K) = 1) (hσ : arithFrobAt (𝓞 K) Gal(L/K) w.asIdeal = σ) :
    HeightOneSpectrum.under (𝓞 (fixedField (Subgroup.zpowers σ))) w ∈ deuringSet σ := by
  set u := HeightOneSpectrum.under (𝓞 (fixedField (Subgroup.zpowers σ))) w with hudef
  have hD : MulAction.stabilizer Gal(L/K) w.asIdeal = Subgroup.zpowers σ := by
    rw [stabilizer_eq_zpowers_arithFrobAt (below K w) w he, hσ]
  have hwu : w.asIdeal.LiesOver u.asIdeal := ⟨rfl⟩
  have huv : u.asIdeal.LiesOver (below K w).asIdeal :=
    ⟨by rw [hudef, HeightOneSpectrum.under_asIdeal, Ideal.under_under]; rfl⟩
  have hf := ramificationIdx_eq_one_and_inertiaDeg_eq_one_of_stabilizer_le (Subgroup.zpowers σ)
    (below K w) u w hD.le
  refine ⟨hf.2, fun w' hw' ↦ ?_⟩
  have hw'w : w' = w := eq_of_under_eq_of_le_stabilizer (Subgroup.zpowers σ) w w' hD.ge
    (by rw [← hw'.over, ← hwu.over])
  subst w'
  refine ⟨he, arithFrobAt_eq_of_isArithFrobAt w ?_ ?_⟩
  · have := Ideal.ramificationIdx_tower (R := 𝓞 K) u.asIdeal w.asIdeal
    rw [he] at this
    exact (mul_eq_one.1 this.symm).2
  · rw [← isArithFrobAt_restrictScalars_iff (fixedField (Subgroup.zpowers σ)) w hf.2,
      restrictScalars_galFixedZpowers, ← hσ]
    exact IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) w.asIdeal

theorem arithFrobAt_eq_of_mem_deuringSet (σ : Gal(L/K))
    {u : HeightOneSpectrum (𝓞 (fixedField (Subgroup.zpowers σ)))} (hu : u ∈ deuringSet σ)
    (w : HeightOneSpectrum (𝓞 L)) [hw : w.asIdeal.LiesOver u.asIdeal] :
    w.asIdeal.ramificationIdx (𝓞 K) = 1 ∧ arithFrobAt (𝓞 K) Gal(L/K) w.asIdeal = σ := by
  obtain ⟨he, hF⟩ := hu.2 w hw
  refine ⟨he, arithFrobAt_eq_of_isArithFrobAt w he ?_⟩
  have hf : (w.asIdeal.under (𝓞 (fixedField (Subgroup.zpowers σ)))).inertiaDeg (𝓞 K) = 1 := by
    rw [← hw.over]
    exact hu.1
  have h0 := IsArithFrobAt.arithFrobAt (𝓞 (fixedField (Subgroup.zpowers σ)))
    Gal(L/fixedField (Subgroup.zpowers σ)) w.asIdeal
  rw [hF] at h0
  have h := (isArithFrobAt_restrictScalars_iff (fixedField (Subgroup.zpowers σ)) w hf
    (galFixedZpowers σ)).2 h0
  rwa [restrictScalars_galFixedZpowers] at h

theorem under_mem_chebotarevSet (σ : Gal(L/K))
    {u : HeightOneSpectrum (𝓞 (fixedField (Subgroup.zpowers σ)))} (hu : u ∈ deuringSet σ) :
    HeightOneSpectrum.under (𝓞 K) u ∈ chebotarevSet {τ : Gal(L/K) | IsConj σ τ} := by
  have : IsGaloisGroup Gal(L/K) (𝓞 K) (𝓞 L) := IsGaloisGroup.of_isFractionRing _ _ _ K L
  intro w hw
  obtain ⟨⟨w0, hw0⟩⟩ := nonempty_placesOver L u
  obtain ⟨he0, hF0⟩ := arithFrobAt_eq_of_mem_deuringSet σ hu w0
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (𝓞 K) (𝓞 L) Gal(L/K)
    w0.asIdeal w.asIdeal (by rw [← hw.over, HeightOneSpectrum.under_asIdeal, hw0.over,
      Ideal.under_under])
  have hgw : w = g • w0 := HeightOneSpectrum.ext hg
  subst hgw
  refine ⟨by rw [ramificationIdx_smul, he0], ?_⟩
  rw [arithFrobAt_smul g w0 he0, hF0]
  exact isConj_iff.2 ⟨g, rfl⟩

end Deuring

section Count

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

theorem card_fiber_deuringSet_mul_orderOf (σ : Gal(L/K)) {v : HeightOneSpectrum (𝓞 K)}
    (hv : v ∈ chebotarevSet {τ : Gal(L/K) | IsConj σ τ}) :
    Nat.card {u // u ∈ deuringSet σ ∧ HeightOneSpectrum.under (𝓞 K) u = v} * orderOf σ =
      Nat.card (Subgroup.centralizer {σ}) := by
  have : IsGaloisGroup Gal(L/K) (𝓞 K) (𝓞 L) := IsGaloisGroup.of_isFractionRing _ _ _ K L
  set Z := Subgroup.centralizer {σ}

  obtain ⟨⟨w1, hw1⟩⟩ := nonempty_placesOver L v
  obtain ⟨he1, hc⟩ := hv w1 hw1
  obtain ⟨c, hc⟩ := isConj_iff.1 hc
  set w0 := c⁻¹ • w1 with hw0def
  have he0 : w0.asIdeal.ramificationIdx (𝓞 K) = 1 := by rw [ramificationIdx_smul, he1]
  have hF0 : arithFrobAt (𝓞 K) Gal(L/K) w0.asIdeal = σ := by
    rw [hw0def, arithFrobAt_smul _ _ he1, ← hc]
    group
  have hw0 : w0.asIdeal.LiesOver v.asIdeal :=
    (below_eq_iff _ _).1 ((below_smul _ _).trans ((below_eq_iff _ _).2 hw1))
  have hD0 : MulAction.stabilizer Gal(L/K) w0.asIdeal = Subgroup.zpowers σ := by
    rw [stabilizer_eq_zpowers_arithFrobAt (below K w0) w0 he0, hF0]
  have hle : Subgroup.zpowers σ ≤ Z :=
    Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 rfl)

  set S : Set (HeightOneSpectrum (𝓞 L)) :=
    {w | w.asIdeal.LiesOver v.asIdeal ∧ arithFrobAt (𝓞 K) Gal(L/K) w.asIdeal = σ} with hSdef
  have heS : ∀ w ∈ S, w.asIdeal.ramificationIdx (𝓞 K) = 1 := fun w hw ↦ (hv w hw.1).1
  have hDS : ∀ w ∈ S, MulAction.stabilizer Gal(L/K) w.asIdeal = Subgroup.zpowers σ := by
    intro w hw
    rw [stabilizer_eq_zpowers_arithFrobAt (below K w) w (heS w hw), hw.2]

  have hSorb : S = MulAction.orbit Z w0 := by
    ext w
    constructor
    · rintro ⟨hwv, hwF⟩
      obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (𝓞 K) (𝓞 L) Gal(L/K)
        w0.asIdeal w.asIdeal (hw0.over.symm.trans hwv.over)
      have hgw : w = g • w0 := HeightOneSpectrum.ext hg
      have hconj := arithFrobAt_smul g w0 he0
      rw [← hgw, hwF, hF0] at hconj
      have hgZ : g ∈ Z := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc g * σ = (g * σ * g⁻¹) * g := by group
          _ = σ * g := by rw [← hconj]
      exact ⟨⟨g, hgZ⟩, hgw.symm⟩
    · rintro ⟨z, rfl⟩
      have hz : (z : Gal(L/K)) * σ = σ * z := Subgroup.mem_centralizer_singleton_iff.1 z.2
      refine ⟨(below_eq_iff _ _).1 ((below_smul (z : Gal(L/K)) w0).trans
        ((below_eq_iff _ _).2 hw0)), ?_⟩
      change arithFrobAt (𝓞 K) Gal(L/K) ((z : Gal(L/K)) • w0).asIdeal = σ
      rw [arithFrobAt_smul _ w0 he0, hF0, hz]
      group

  have hstab : MulAction.stabilizer Z w0 = (Subgroup.zpowers σ).subgroupOf Z := by
    ext z
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, ← hD0, MulAction.mem_stabilizer_iff]
    constructor
    · intro h
      exact congrArg HeightOneSpectrum.asIdeal h
    · intro h
      exact HeightOneSpectrum.ext h
  have hcardS : Nat.card S * orderOf σ = Nat.card Z := by
    rw [hSorb, Nat.card_coe_set_eq, ← MulAction.index_stabilizer, ← Nat.card_zpowers,
      ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, ← hstab, mul_comm,
      Subgroup.card_mul_index]

  let f : S → {u // u ∈ deuringSet σ ∧ HeightOneSpectrum.under (𝓞 K) u = v} := fun w ↦
    ⟨HeightOneSpectrum.under (𝓞 (fixedField (Subgroup.zpowers σ))) w.1,
      under_mem_deuringSet σ w.1 (heS w.1 w.2) w.2.2,
      HeightOneSpectrum.ext (by
        rw [HeightOneSpectrum.under_asIdeal, HeightOneSpectrum.under_asIdeal, Ideal.under_under]
        exact w.2.1.over.symm)⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      have h := congrArg (fun x ↦ x.1.asIdeal) hab
      simp only [f, HeightOneSpectrum.under_asIdeal] at h
      exact (Subtype.ext (eq_of_under_eq_of_le_stabilizer (Subgroup.zpowers σ) a.1 b.1
        (hDS a.1 a.2).ge h.symm)).symm
    · rintro ⟨u, hu, huv⟩
      obtain ⟨⟨w, hw⟩⟩ := nonempty_placesOver L u
      obtain ⟨-, hF⟩ := arithFrobAt_eq_of_mem_deuringSet σ hu w
      have hwv : w.asIdeal.LiesOver v.asIdeal :=
        ⟨by rw [← huv, HeightOneSpectrum.under_asIdeal, hw.over, Ideal.under_under]⟩
      exact ⟨⟨w, hwv, hF⟩, Subtype.ext (HeightOneSpectrum.ext hw.over.symm)⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), hcardS]

end Count

end

end GroundTheory.Global
end

namespace GroundTheory.Global

open NumberField IsDedekindDomain IntermediateField AdeleBaseChange Filter Topology Set

noncomputable section

universe u

section Sums

variable {K E : Type*} [Field K] [NumberField K] [Field E] [NumberField E]

theorem primeIdealZetaSum_eq_mul_of_card_fiber {A : Set (HeightOneSpectrum (𝓞 E))}
    {T : Set (HeightOneSpectrum (𝓞 K))} (π : HeightOneSpectrum (𝓞 E) → HeightOneSpectrum (𝓞 K))
    (hπ : ∀ u ∈ A, π u ∈ T) (hN : ∀ u ∈ A, Ideal.absNorm u.asIdeal = Ideal.absNorm (π u).asIdeal)
    {n : ℕ} (hn : n ≠ 0) (hcard : ∀ v ∈ T, Nat.card {u // u ∈ A ∧ π u = v} = n) {s : ℝ}
    (hs : 1 < s) : A.primeIdealZetaSum s = n * T.primeIdealZetaSum s := by
  classical
  let p : A → T := fun u ↦ ⟨π u, hπ u u.2⟩
  have hcard' : ∀ v : T, Nat.card {u // p u = v} = n := by
    intro v
    rw [← hcard v.1 v.2]
    exact Nat.card_congr
      { toFun := fun u ↦ ⟨u.1.1, u.1.2, congrArg Subtype.val u.2⟩
        invFun := fun u ↦ ⟨⟨u.1, u.2.1⟩, Subtype.ext u.2.2⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
  have hfin : ∀ v : T, Finite {u // p u = v} := fun v ↦
    Nat.finite_of_card_ne_zero (by rw [hcard']; exact hn)
  have hsumA := summable_absNorm_rpow_neg_subtype A hs
  rw [Set.primeIdealZetaSum_def, Set.primeIdealZetaSum_def,
    ← (Equiv.sigmaFiberEquiv p).tsum_eq,
    Summable.tsum_sigma'
      (f := fun q ↦ (Ideal.absNorm ((Equiv.sigmaFiberEquiv p) q).1.asIdeal : ℝ) ^ (-s))
      (fun v ↦ by have := hfin v; exact Summable.of_finite)
      ((Equiv.sigmaFiberEquiv p).summable_iff.mpr hsumA :),
    ← tsum_mul_left]
  refine tsum_congr fun v ↦ ?_
  have := hfin v
  let _ := Fintype.ofFinite {u // p u = v}
  rw [tsum_fintype]
  calc ∑ u : {u // p u = v}, (Ideal.absNorm (Equiv.sigmaFiberEquiv p ⟨v, u⟩).1.asIdeal : ℝ) ^ (-s)
      = ∑ _u : {u // p u = v}, (Ideal.absNorm v.1.asIdeal : ℝ) ^ (-s) :=
        Finset.sum_congr rfl fun u _ ↦ by
          rw [Equiv.sigmaFiberEquiv_apply, hN u.1.1 u.1.2,
            show π u.1.1 = v.1 from congrArg Subtype.val u.2]
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, hcard', nsmul_eq_mul]

open private HasDirichletDensity.eq_1 from Mathlib.NumberTheory.NumberField.DirichletDensity in
theorem HasDirichletDensity.union {A B : Set (HeightOneSpectrum (𝓞 K))} {a b : ℝ}
    (hA : A.HasDirichletDensity a) (hB : B.HasDirichletDensity b) (hd : Disjoint A B) :
    (A ∪ B).HasDirichletDensity (a + b) := by
  rw [HasDirichletDensity.eq_1] at hA hB ⊢
  refine (hA.add hB).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [primeIdealZetaSum_union hd hs, add_div]

end Sums

section Class

variable {G : Type*} [Group G]

theorem natCard_isConj_mul_natCard_centralizer (σ : G) :
    Nat.card {τ : G | IsConj σ τ} * Nat.card (Subgroup.centralizer {σ}) = Nat.card G := by
  have horb : MulAction.orbit (ConjAct G) σ = {τ : G | IsConj σ τ} := by
    ext τ
    rw [ConjAct.mem_orbit_conjAct, isConj_comm]
    rfl
  have hstab : Nat.card (Subgroup.centralizer {σ}) =
      Nat.card (MulAction.stabilizer (ConjAct G) σ) :=
    Nat.card_congr (Equiv.subtypeEquiv ConjAct.toConjAct.toEquiv fun g ↦ by
      rw [Subgroup.mem_centralizer_singleton_iff]
      change _ ↔ ConjAct.toConjAct g • σ = σ
      rw [ConjAct.toConjAct_smul, mul_inv_eq_iff_eq_mul]
      rfl)
  rw [Nat.card_coe_set_eq, ← horb, ← MulAction.index_stabilizer, hstab, mul_comm,
    Subgroup.card_mul_index]
  rfl

end Class

section Deuring

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

theorem hasDirichletDensity_deuringSet (σ : Gal(L/K)) :
    (deuringSet σ).HasDirichletDensity (1 / orderOf σ) := by
  have := isMulCommutative_gal_fixedField_zpowers σ
  have hab := hasDirichletDensity_setOf_arithFrobAt_eq (K := fixedField (Subgroup.zpowers σ))
    (L := L) (galFixedZpowers σ)
  rw [natCard_gal_fixedField_zpowers] at hab
  have h1 := (hasDirichletDensity_inter_degreeOnePrimes_iff K _ _).2 hab
  refine (hasDirichletDensity_iff_of_subset_of_isBoundedUnder ?_
    (isBoundedUnder_primeIdealZetaSum_of_finite
      (((finite_setOf_ramificationIdx_ne_one K L).image
        (HeightOneSpectrum.under (𝓞 (fixedField (Subgroup.zpowers σ))))).subset ?_)) _).2 h1
  · intro u hu
    refine ⟨fun w hw ↦ ⟨?_, (hu.2 w hw).2⟩, hu.1⟩
    have h := Ideal.ramificationIdx_tower (R := 𝓞 K) u.asIdeal w.asIdeal
    rw [(hu.2 w hw).1] at h
    exact (mul_eq_one.1 h.symm).2
  · rintro u ⟨⟨hab, hdeg⟩, hnot⟩
    by_contra hu
    refine hnot ⟨hdeg, fun w hw ↦ ⟨?_, (hab w hw).2⟩⟩
    by_contra he
    exact hu ⟨w, he, HeightOneSpectrum.ext hw.over.symm⟩

open private HasDirichletDensity.eq_1 from Mathlib.NumberTheory.NumberField.DirichletDensity in
theorem hasDirichletDensity_chebotarevSet_isConj (σ : Gal(L/K)) :
    (chebotarevSet {τ : Gal(L/K) | IsConj σ τ}).HasDirichletDensity
      (1 / Nat.card (Subgroup.centralizer {σ})) := by
  set E := fixedField (Subgroup.zpowers σ)
  set T := chebotarevSet {τ : Gal(L/K) | IsConj σ τ}
  set A := deuringSet σ
  set n := Nat.card (Subgroup.centralizer {σ}) / orderOf σ with hndef
  have hm : 0 < orderOf σ := orderOf_pos σ
  have hle : Subgroup.zpowers σ ≤ Subgroup.centralizer {σ} :=
    Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 rfl)
  have hZ : n * orderOf σ = Nat.card (Subgroup.centralizer {σ}) := by
    refine Nat.div_mul_cancel ?_
    rw [← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le hle
  have hn : n ≠ 0 := by
    intro h
    rw [h, zero_mul] at hZ
    exact Nat.card_pos.ne' hZ.symm
  have hcard : ∀ v ∈ T, Nat.card {u // u ∈ A ∧ HeightOneSpectrum.under (𝓞 K) u = v} = n :=
    fun v hv ↦ Nat.eq_of_mul_eq_mul_right hm ((card_fiber_deuringSet_mul_orderOf σ hv).trans hZ.symm)
  have hsum : ∀ s : ℝ, 1 < s → A.primeIdealZetaSum s = n * T.primeIdealZetaSum s := fun s hs ↦
    primeIdealZetaSum_eq_mul_of_card_fiber (HeightOneSpectrum.under (𝓞 K))
      (fun u hu ↦ under_mem_chebotarevSet σ hu)
      (fun u hu ↦ absNorm_eq_of_inertiaDeg_eq_one u hu.1) hn hcard hs
  have hA := hasDirichletDensity_deuringSet σ
  have hEK := tendsto_primeIdealZetaSum_univ_div_univ E K
  have hEpos := (tendsto_primeIdealZetaSum_univ_atTop E).eventually_gt_atTop 0
  have hKpos := (tendsto_primeIdealZetaSum_univ_atTop K).eventually_gt_atTop 0
  rw [HasDirichletDensity.eq_1] at hA ⊢
  have hlim := (hA.const_mul (n : ℝ)⁻¹).mul hEK
  have hval : (n : ℝ)⁻¹ * (1 / orderOf σ) * 1 = 1 / Nat.card (Subgroup.centralizer {σ}) := by
    rw [← hZ]
    push_cast
    have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have : (orderOf σ : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    field_simp
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin, hEpos, hKpos] with s hs hE hK
  rw [hsum s hs]
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  field_simp

end Deuring

section Main

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

theorem isConj_arithFrobAt_of_liesOver {v : HeightOneSpectrum (𝓞 K)} (w w' : HeightOneSpectrum (𝓞 L))
    (hw : w.asIdeal.LiesOver v.asIdeal) (hw' : w'.asIdeal.LiesOver v.asIdeal) :
    IsConj (arithFrobAt (𝓞 K) Gal(L/K) w.asIdeal) (arithFrobAt (𝓞 K) Gal(L/K) w'.asIdeal) :=
  isConj_arithFrobAt (𝓞 K) Gal(L/K) w.asIdeal w'.asIdeal (hw.over.symm.trans hw'.over)

theorem chebotarevSet_empty : chebotarevSet (∅ : Set Gal(L/K)) = ∅ := by
  ext v
  simp only [mem_empty_iff_false, iff_false]
  intro hv
  obtain ⟨⟨w, hw⟩⟩ := nonempty_placesOver L v
  exact (hv w hw).2

theorem chebotarevSet_mono {C C' : Set Gal(L/K)} (h : C ⊆ C') :
    chebotarevSet C ⊆ chebotarevSet C' :=
  fun _ hv w hw ↦ ⟨(hv w hw).1, h (hv w hw).2⟩

theorem disjoint_chebotarevSet {C C' : Set Gal(L/K)} (h : Disjoint C C') :
    Disjoint (chebotarevSet C) (chebotarevSet C') := by
  refine Set.disjoint_left.2 fun v h1 h2 ↦ ?_
  obtain ⟨⟨w, hw⟩⟩ := nonempty_placesOver L v
  exact Set.disjoint_left.1 h (h1 w hw).2 (h2 w hw).2

theorem chebotarevSet_eq_union (C : Set Gal(L/K)) (σ : Gal(L/K)) :
    chebotarevSet C = chebotarevSet (C ∩ {τ | IsConj σ τ}) ∪
      chebotarevSet (C \ {τ | IsConj σ τ}) := by
  refine Subset.antisymm (fun v hv ↦ ?_)
    (union_subset (chebotarevSet_mono inter_subset_left) (chebotarevSet_mono sdiff_subset))
  obtain ⟨⟨w1, hw1⟩⟩ := nonempty_placesOver L v
  by_cases h : IsConj σ (arithFrobAt (𝓞 K) Gal(L/K) w1.asIdeal)
  · refine Or.inl fun w hw ↦ ⟨(hv w hw).1, (hv w hw).2, ?_⟩
    exact h.trans (isConj_arithFrobAt_of_liesOver w1 w hw1 hw)
  · refine Or.inr fun w hw ↦ ⟨(hv w hw).1, (hv w hw).2, fun h' ↦ h ?_⟩
    exact h'.trans (isConj_arithFrobAt_of_liesOver w w1 hw hw1)

theorem hasDirichletDensity_chebotarevSet (C : Set Gal(L/K))
    (hC : ∀ σ ∈ C, ∀ τ : Gal(L/K), τ * σ * τ⁻¹ ∈ C) :
    (chebotarevSet C).HasDirichletDensity (Nat.card C / Nat.card Gal(L/K)) := by
  suffices h : ∀ n : ℕ, ∀ C : Set Gal(L/K), (∀ σ ∈ C, ∀ τ : Gal(L/K), τ * σ * τ⁻¹ ∈ C) →
      Nat.card C = n → (chebotarevSet C).HasDirichletDensity (n / Nat.card Gal(L/K)) from
    h _ C hC rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro C hC hn
  rcases C.eq_empty_or_nonempty with rfl | ⟨σ, hσ⟩
  · subst hn
    rw [chebotarevSet_empty]
    simpa using Set.hasDirichletDensity_empty
  set cl := {τ : Gal(L/K) | IsConj σ τ} with hcldef
  have hcl : cl ⊆ C := fun τ hτ ↦ by
    obtain ⟨c, rfl⟩ := isConj_iff.1 hτ
    exact hC σ hσ c
  have hC' : ∀ ρ ∈ C \ cl, ∀ τ : Gal(L/K), τ * ρ * τ⁻¹ ∈ C \ cl := fun ρ hρ τ ↦
    ⟨hC ρ hρ.1 τ, fun h ↦ hρ.2 (h.trans (isConj_iff.2 ⟨τ, rfl⟩).symm)⟩
  have hcard : Nat.card ↥(C \ cl) + Nat.card ↥cl = n := by
    rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq,
      Set.ncard_sdiff_add_ncard_of_subset hcl (Set.toFinite C), ← Nat.card_coe_set_eq, hn]
  have hclpos : 0 < Nat.card ↥cl := by
    have : Nonempty ↥cl := ⟨⟨σ, IsConj.refl σ⟩⟩
    exact Nat.card_pos
  have h1 := ih _ (by omega) (C \ cl) hC' rfl
  have h2 := hasDirichletDensity_chebotarevSet_isConj σ
  have hd := disjoint_chebotarevSet (L := L) (disjoint_sdiff_right : Disjoint cl (C \ cl))
  have hU := HasDirichletDensity.union h2 h1 hd
  rw [chebotarevSet_eq_union C σ, inter_eq_right.2 hcl]
  convert hU using 1
  have hG := natCard_isConj_mul_natCard_centralizer σ
  rw [← hcldef] at hG
  have hZ : (Nat.card (Subgroup.centralizer {σ}) : ℝ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hcl' : (Nat.card ↥cl : ℝ) ≠ 0 := by exact_mod_cast hclpos.ne'
  rw [← hcard, ← hG]
  push_cast
  field_simp
  ring

theorem hasDirichletDensity_setOf_arithFrobAt_mem (C : Set Gal(L/K))
    (hC : ∀ σ ∈ C, ∀ τ : Gal(L/K), τ * σ * τ⁻¹ ∈ C) :
    {v : HeightOneSpectrum (𝓞 K) | ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal.LiesOver v.asIdeal →
      w.asIdeal.ramificationIdx (𝓞 K) = 1 ∧ arithFrobAt (𝓞 K) Gal(L/K) w.asIdeal ∈ C}.HasDirichletDensity
      (Nat.card C / Nat.card Gal(L/K)) :=
  hasDirichletDensity_chebotarevSet C hC

theorem hasDirichletDensity_setOf_exists_arithFrobAt_mem (C : Set Gal(L/K))
    (hC : ∀ σ ∈ C, ∀ τ : Gal(L/K), τ * σ * τ⁻¹ ∈ C) :
    {v : HeightOneSpectrum (𝓞 K) | (∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal.LiesOver v.asIdeal →
      w.asIdeal.ramificationIdx (𝓞 K) = 1) ∧ ∃ w : HeightOneSpectrum (𝓞 L),
        w.asIdeal.LiesOver v.asIdeal ∧ arithFrobAt (𝓞 K) Gal(L/K) w.asIdeal ∈ C}.HasDirichletDensity
      (Nat.card C / Nat.card Gal(L/K)) := by
  convert hasDirichletDensity_chebotarevSet C hC using 1
  ext v
  constructor
  · rintro ⟨he, w1, hw1, hC1⟩ w hw
    refine ⟨he w hw, ?_⟩
    obtain ⟨c, hc⟩ := isConj_iff.1 (isConj_arithFrobAt_of_liesOver w1 w hw1 hw)
    rw [← hc]
    exact hC _ hC1 c
  · intro hv
    obtain ⟨⟨w, hw⟩⟩ := nonempty_placesOver L v
    exact ⟨fun w' hw' ↦ (hv w' hw').1, w, hw, (hv w hw).2⟩

end Main

end

end GroundTheory.Global
