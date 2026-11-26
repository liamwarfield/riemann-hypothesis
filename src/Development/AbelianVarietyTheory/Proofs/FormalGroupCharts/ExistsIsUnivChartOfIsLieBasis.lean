module

public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.JetPointAddSqZeroEqProdMulTangent

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.JetChartCoordinatesUniqueCommGroup
section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.JetChartCoordinatesUniqueCommGroup
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open SqZero

theorem jetCoord_eq_of_sub_mem {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))}
    [GrpObj G] [IsCommMonObj G] (hG : Smooth G.hom) {d : ℕ} {v : Fin d → (epsR R ⟶ G)}
    (hv : IsLieBasis v) {x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G}
    (hx₁ : ∀ m, spMap (jetTruncR R (Fin d) m) ≫ x (m + 1) = x m)
    (hx₂ : ∀ m, spMap (jetZeroR R (Fin d) m) ≫ x m = 1)
    (hx₃ : ∀ j, spMap (dualLift (Pi.single j (1 : R))) ≫ x 1 = v j)
    {A : Type} [CommRing A] [Algebra R A] (aug : A →ₐ[R] R) (J : Ideal A)
    (hJ : J * RingHom.ker aug = ⊥) (hJ' : J ≤ RingHom.ker aug) {m : ℕ}
    (ψ ψ' : JetR R (Fin d) m →ₐ[R] A) (hψ : aug.comp ψ = jetAug R (Fin d) m)
    (hψ' : aug.comp ψ' = jetAug R (Fin d) m) (hδ : ∀ j, ψ' (zR m j) - ψ (zR m j) ∈ J)
    (h : spMap ψ ≫ x m = spMap ψ' ≫ x m) : ψ = ψ' := by
  have hJ2 : J ^ 2 = ⊥ := by
    rw [← le_bot_iff, pow_two, ← hJ]
    exact Ideal.mul_mono_right hJ'
  let c : Fin d → J := fun j => ⟨_, hδ j⟩
  have hc : ∀ j, (c j : A) * (c j : A) = 0 := fun j => mul_eq_zero_of_sq hJ2 (c j).2 (c j).2
  have he : ∀ j, epsTo R (c j : A) (hc j) (TrivSqZeroExt.inr 1) = c j := fun j => epsTo_eps _ _
  have key := GlobalTheory.T.jetPoint_add_sqZero_eq_prod_mul_tangent R G hG d v hv x hx₁ hx₂ hx₃ A aug J hJ hJ' m ψ ψ' hψ hψ'
    (fun j => epsTo R (c j : A) (hc j)) (fun j => by rw [he]; exact (c j).2)
    (fun j => by rw [he]; exact (add_sub_cancel _ _).symm)
  rw [← h] at key
  have h1 : lieExp v (fun j => (c j : A)) hc = 1 := mul_eq_right.1 key.symm
  have h0 : c = 0 := by
    apply (expHom_bijective hv hJ2).1
    rw [map_zero]
    exact congrArg Additive.ofMul (Subtype.ext h1)
  refine jet_ext fun j => ?_
  have : ψ' (zR m j) - ψ (zR m j) = 0 := congrArg Subtype.val (congrFun h0 j)
  exact (sub_eq_zero.1 this).symm

theorem jetCoord_unique (R : Type) [CommRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
    [IsCommMonObj G] (hG : Smooth G.hom) (d : ℕ) (v : Fin d → (epsR R ⟶ G)) (hv : IsLieBasis v)
    (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G)
    (hx₁ : ∀ m, spMap (jetTruncR R (Fin d) m) ≫ x (m + 1) = x m)
    (hx₂ : ∀ m, spMap (jetZeroR R (Fin d) m) ≫ x m = 1)
    (hx₃ : ∀ j, spMap (dualLift (Pi.single j (1 : R))) ≫ x 1 = v j)
    (A : Type) [CommRing A] [Algebra R A] (aug : A →ₐ[R] R) (m : ℕ)
    (hN : (RingHom.ker aug) ^ (m + 1) = ⊥) (ψ ψ' : JetR R (Fin d) m →ₐ[R] A)
    (hψ : aug.comp ψ = jetAug R (Fin d) m) (hψ' : aug.comp ψ' = jetAug R (Fin d) m)
    (h : spMap ψ ≫ x m = spMap ψ' ≫ x m) : ψ = ψ' := by
  set N := RingHom.ker aug with hNdef
  have main : ∀ k j, ψ' (zR m j) - ψ (zR m j) ∈ N ^ (k + 1) := by
    intro k
    induction k with
    | zero =>
      intro j
      rw [zero_add, pow_one, hNdef, RingHom.mem_ker, map_sub, ← AlgHom.comp_apply,
        ← AlgHom.comp_apply, hψ, hψ', sub_self]
    | succ k ih =>
      let q : A →ₐ[R] A ⧸ N ^ (k + 1 + 1) := Ideal.Quotient.mkₐ R _
      have hq : Function.Surjective q := Ideal.Quotient.mkₐ_surjective R _
      let aug' : (A ⧸ N ^ (k + 1 + 1)) →ₐ[R] R := Ideal.Quotient.liftₐ _ aug
        (fun a ha => Ideal.pow_le_self (by omega) ha)
      have haug : aug'.comp q = aug := AlgHom.ext fun _ => rfl
      have hker : RingHom.ker aug' = N.map q := by
        apply le_antisymm
        · intro a ha
          obtain ⟨b, rfl⟩ := hq a
          exact Ideal.mem_map_of_mem _ ha
        · exact Ideal.map_le_iff_le_comap.2 fun a ha => ha
      have e := jetCoord_eq_of_sub_mem hG hv hx₁ hx₂ hx₃ aug' ((N ^ (k + 1)).map q)
        (by rw [hker, ← Ideal.map_mul, ← pow_succ]; exact Ideal.map_quotient_self _)
        (by rw [hker]; exact Ideal.map_mono (Ideal.pow_le_self (by omega)))
        (q.comp ψ) (q.comp ψ') (by rw [← AlgHom.comp_assoc, haug, hψ])
        (by rw [← AlgHom.comp_assoc, haug, hψ'])
        (fun j => by
          rw [AlgHom.comp_apply, AlgHom.comp_apply, ← map_sub]
          exact Ideal.mem_map_of_mem _ (ih j))
        (by rw [← spMap_comp, ← spMap_comp, Category.assoc, Category.assoc, h])
      intro j
      exact Ideal.Quotient.eq.1 (AlgHom.congr_fun e (zR m j)).symm
  refine jet_ext fun j => ?_
  have := main m j
  rw [hN, Ideal.mem_bot] at this
  exact (sub_eq_zero.1 this).symm

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.JetChartCoordinatesUniqueCommGroupStatement
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.jetChart_coordinates_unique_commGroup : ∀ (R : Type) [CommRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], Smooth G.hom → ∀ (d : ℕ) (v : Fin d → (epsR R ⟶ G)), IsLieBasis v → ∀ (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G), (∀ m, spMap (jetTruncR R (Fin d) m) ≫ x (m + 1) = x m) → (∀ m, spMap (jetZeroR R (Fin d) m) ≫ x m = 1) → (∀ j, spMap (dualLift (Pi.single j (1 : R))) ≫ x 1 = v j) → ∀ (A : Type) [CommRing A] [Algebra R A] (aug : A →ₐ[R] R) (m : ℕ), (RingHom.ker aug) ^ (m + 1) = ⊥ → ∀ ψ ψ' : JetR R (Fin d) m →ₐ[R] A, aug.comp ψ = jetAug R (Fin d) m → aug.comp ψ' = jetAug R (Fin d) m → spMap ψ ≫ x m = spMap ψ' ≫ x m → ψ = ψ' := by
  first | exact @GlobalTheory.jetCoord_unique | exact GlobalTheory.jetCoord_unique | (intros; apply GlobalTheory.jetCoord_unique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsJetChartCoordinatesNilpotent
section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsJetChartCoordinatesNilpotent
set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.JetOnto

variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G]

theorem comp_eq_of_factor {A B C : Type} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
    [CommRing C] [Algebra R C] {X : Over (Spec (CommRingCat.of R))} (p : A →ₐ[R] B) (q : B →ₐ[R] C)
    {y y' : sp (R₀ := R) A ⟶ X} (h : spMap p ≫ y = spMap p ≫ y') :
    spMap (q.comp p) ≫ y = spMap (q.comp p) ≫ y' := by
  rw [← spMap_comp, Category.assoc, Category.assoc, h]

theorem aug_comp_jetLift {A : Type} [CommRing A] [Algebra R A] (aug : A →ₐ[R] R) {d m : ℕ}
    (h : (RingHom.ker aug) ^ (m + 1) = ⊥) (b : Fin d → A) (hb : ∀ j, b j ∈ RingHom.ker aug) :
    aug.comp (jetLift R _ h b hb) = jetAug R (Fin d) m :=
  jet_ext fun j => by
    rw [AlgHom.comp_apply, jetLift_zR, jetAug_zR]; exact hb j

theorem spMap_jetAug {d : ℕ} (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G)
    (h0 : ∀ m, spMap (jetZeroR R (Fin d) m) ≫ x m = 1) (m : ℕ) :
    spMap (jetAug R (Fin d) m) ≫ x m = 1 := by
  have e : jetAug R (Fin d) m = (jetAug R (Fin d) 0).comp (jetZeroR R (Fin d) m) :=
    (jet_ext fun j => by rw [AlgHom.comp_apply, jetAug_zR]; exact (jetAug_zR (R := R) 0 j).symm)
  rw [e, ← spMap_comp, Category.assoc, h0 m, comp_one']

end GlobalTheory.JetOnto

namespace GlobalTheory

open JetOnto

theorem exists_jet_coordinates : ∀ (R : Type) [CommRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], Smooth G.hom → ∀ (d : ℕ) (v : Fin d → (epsR R ⟶ G)), IsLieBasis v → ∀ (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G), (∀ m, spMap (jetTruncR R (Fin d) m) ≫ x (m + 1) = x m) → (∀ m, spMap (jetZeroR R (Fin d) m) ≫ x m = 1) → (∀ j, spMap (dualLift (Pi.single j (1 : R))) ≫ x 1 = v j) → ∀ (A : Type) [CommRing A] [Algebra R A] (aug : A →ₐ[R] R) (m : ℕ), (RingHom.ker aug) ^ (m + 1) = ⊥ → ∀ y : sp (R₀ := R) A ⟶ G, spMap aug ≫ y = 1 → ∃ ψ : JetR R (Fin d) m →ₐ[R] A, aug.comp ψ = jetAug R (Fin d) m ∧ y = spMap ψ ≫ x m := by
  intro R _ G _ _ hG d v hv x ht h0 h1 A _ _ aug m hN y hy
  have key : ∀ k : ℕ, ∃ (b : Fin d → A) (hb : ∀ j, b j ∈ RingHom.ker aug),
      spMap (Ideal.Quotient.mkₐ R ((RingHom.ker aug) ^ (k + 1))) ≫ y =
        spMap (Ideal.Quotient.mkₐ R ((RingHom.ker aug) ^ (k + 1))) ≫
          spMap (jetLift R _ hN b hb) ≫ x m := by
    intro k
    induction k with
    | zero =>
      refine ⟨fun _ => 0, fun _ => zero_mem _, ?_⟩
      have e : Ideal.Quotient.mkₐ R ((RingHom.ker aug) ^ (0 + 1)) =
          (Algebra.ofId R _).comp aug := by
        ext a
        change Ideal.Quotient.mk _ a = Ideal.Quotient.mk _ (algebraMap R A (aug a))
        rw [Ideal.Quotient.eq, zero_add, pow_one, RingHom.mem_ker, map_sub, AlgHom.commutes,
          Algebra.algebraMap_self, RingHom.id_apply, sub_self]
      rw [e]
      refine comp_eq_of_factor _ _ ?_
      rw [hy, ← Category.assoc, spMap_comp, aug_comp_jetLift, spMap_jetAug x h0]
    | succ k ih =>
      obtain ⟨b, hb, ih⟩ := ih
      set N := RingHom.ker aug with hNdef
      let B := A ⧸ N ^ (k + 1 + 1)
      let π : A →ₐ[R] B := Ideal.Quotient.mkₐ R (N ^ (k + 1 + 1))
      have hπ : Function.Surjective π := Ideal.Quotient.mk_surjective
      let augB : B →ₐ[R] R := Ideal.Quotient.liftₐ _ aug
        (fun a ha => (Ideal.pow_le_self (by omega) ha : a ∈ N))
      have haug : augB.comp π = aug := by ext a; rfl
      have hker : RingHom.ker augB = N.map π := by
        apply le_antisymm
        · intro z hz
          obtain ⟨a, rfl⟩ := hπ z
          exact Ideal.mem_map_of_mem _ hz
        · exact Ideal.map_le_iff_le_comap.2 fun a ha => ha
      let J : Ideal B := (N ^ (k + 1)).map π
      have hJN : J * RingHom.ker augB = ⊥ := by
        rw [hker, ← Ideal.map_mul, ← pow_succ]
        exact Ideal.map_quotient_self _
      have hJle : J ≤ RingHom.ker augB := by
        rw [hker]
        exact Ideal.map_mono (Ideal.pow_le_self (by omega))
      have hJ : J ^ 2 = ⊥ := by
        rw [← le_bot_iff, pow_two, ← hJN]
        exact Ideal.mul_mono_right hJle
      let q : (A ⧸ N ^ (k + 1)) →ₐ[R] B ⧸ J := Ideal.Quotient.liftₐ _
        ((Ideal.Quotient.mkₐ R J).comp π)
        (fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ ha))
      have hq : q.comp (Ideal.Quotient.mkₐ R (N ^ (k + 1))) = (Ideal.Quotient.mkₐ R J).comp π := by
        ext a; rfl
      have h2 := comp_eq_of_factor _ q ih
      rw [hq, ← spMap_comp, Category.assoc, Category.assoc] at h2
      haveI := hG
      obtain ⟨c, hc, -⟩ := SqZero.existsUnique_eq_lieExp_mul hv hJ h2.symm
      choose δ hδ hδc using fun j => (Ideal.mem_map_iff_of_surjective π hπ).1 (c j).2
      have hb' : ∀ j, b j + δ j ∈ N := fun j =>
        add_mem (hb j) (Ideal.pow_le_self (by omega) (hδ j))
      refine ⟨fun j => b j + δ j, hb', ?_⟩
      have h3 := GlobalTheory.T.jetPoint_add_sqZero_eq_prod_mul_tangent R G hG d v hv x ht h0 h1 B augB J hJN hJle m
        (π.comp (jetLift R _ hN b hb)) (π.comp (jetLift R _ hN (fun j => b j + δ j) hb'))
        (by rw [← AlgHom.comp_assoc, haug, aug_comp_jetLift])
        (by rw [← AlgHom.comp_assoc, haug, aug_comp_jetLift])
        (fun j => SqZero.epsTo R (c j : B) (SqZero.mul_eq_zero_of_sq hJ (c j).2 (c j).2))
        (fun j => by erw [SqZero.epsTo_eps]; exact (c j).2)
        (fun j => by
          erw [SqZero.epsTo_eps]
          rw [AlgHom.comp_apply, AlgHom.comp_apply, jetLift_zR, jetLift_zR,
            map_add, hδc])
      change spMap π ≫ y = spMap π ≫ _
      rw [hc, ← Category.assoc, spMap_comp, ← Category.assoc, spMap_comp, h3]
      rfl
  obtain ⟨b, hb, h⟩ := key m
  refine ⟨jetLift R _ hN b hb, aug_comp_jetLift aug hN b hb, ?_⟩
  let q : (A ⧸ (RingHom.ker aug) ^ (m + 1)) →ₐ[R] A := Ideal.Quotient.liftₐ _ (AlgHom.id R A)
    (fun a ha => by rw [hN] at ha; exact ha)
  have hq : q.comp (Ideal.Quotient.mkₐ R ((RingHom.ker aug) ^ (m + 1))) = AlgHom.id R A := by
    ext a; rfl
  have h2 := comp_eq_of_factor _ q h
  rwa [hq, spMap_id, Category.id_comp, Category.id_comp] at h2

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsJetChartCoordinatesNilpotentStatement
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.exists_jetChart_coordinates_nilpotent : ∀ (R : Type) [CommRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], Smooth G.hom → ∀ (d : ℕ) (v : Fin d → (epsR R ⟶ G)), IsLieBasis v → ∀ (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G), (∀ m, spMap (jetTruncR R (Fin d) m) ≫ x (m + 1) = x m) → (∀ m, spMap (jetZeroR R (Fin d) m) ≫ x m = 1) → (∀ j, spMap (dualLift (Pi.single j (1 : R))) ≫ x 1 = v j) → ∀ (A : Type) [CommRing A] [Algebra R A] (aug : A →ₐ[R] R) (m : ℕ), (RingHom.ker aug) ^ (m + 1) = ⊥ → ∀ y : sp (R₀ := R) A ⟶ G, spMap aug ≫ y = 1 → ∃ ψ : JetR R (Fin d) m →ₐ[R] A, aug.comp ψ = jetAug R (Fin d) m ∧ y = spMap ψ ≫ x m := by
  first | exact @GlobalTheory.exists_jet_coordinates | exact GlobalTheory.exists_jet_coordinates | (intros; apply GlobalTheory.exists_jet_coordinates <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsJetPointsOfIsLieBasis
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.JetPoint

open GlobalTheory.SqZero

variable {R : Type} [CommRing R]

theorem jetTruncR_surjective (κ : Type) (m : ℕ) : Function.Surjective (jetTruncR R κ m) := by
  intro y
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨Ideal.Quotient.mk _ p, rfl⟩

theorem jetAug_comp_jetTruncR (κ : Type) (m : ℕ) :
    (jetAug R κ m).comp (jetTruncR R κ m) = jetAug R κ (m + 1) :=
  jet_ext fun j => by
    rw [jetAug_zR]
    exact jetAug_zR (R := R) m j

theorem ker_jetTruncR_isNilpotent (κ : Type) (m : ℕ) :
    IsNilpotent (RingHom.ker (jetTruncR R κ m)) := by
  have hle : RingHom.ker (jetTruncR R κ m) ≤ RingHom.ker (jetAug R κ (m + 1)) := by
    intro a ha
    have ha' : jetTruncR R κ m a = 0 := ha
    change jetAug R κ (m + 1) a = 0
    rw [← jetAug_comp_jetTruncR, AlgHom.comp_apply, ha', map_zero]
  refine ⟨m + 1 + 1, ?_⟩
  rw [Ideal.zero_eq_bot, ← le_bot_iff, ← ker_jetAug_pow (R := R) κ (m + 1)]
  exact Ideal.pow_right_mono hle _

theorem jetZeroR_comp_jetTruncR (κ : Type) (m : ℕ) :
    (jetZeroR R κ m).comp (jetTruncR R κ m) = jetZeroR R κ (m + 1) :=
  jet_ext fun _ => rfl

theorem zR_zero_eq_zero {κ : Type} (j : κ) : zR (R := R) 0 j = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.2 (by
    rw [zero_add, pow_one]
    exact Ideal.subset_span ⟨j, rfl⟩)

theorem zR_one_mul_self {κ : Type} (j : κ) : zR (R := R) 1 j * zR (R := R) 1 j = 0 :=
  mul_eq_zero_of_sq (ker_jetAug_pow (R := R) κ 1) (zR_mem_ker 1 j) (zR_mem_ker 1 j)

end GlobalTheory.JetPoint

namespace GlobalTheory

open SqZero JetPoint

theorem exists_jetPoints_of_isLieBasis :
    ∀ (R : Type) [CommRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], Smooth G.hom → ∀ (d : ℕ) (v : Fin d → (epsR R ⟶ G)), IsLieBasis v → ∃ (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G), (∀ m, spMap (jetTruncR R (Fin d) m) ≫ x (m + 1) = x m) ∧ (∀ m, spMap (jetZeroR R (Fin d) m) ≫ x m = 1) ∧ (∀ j, spMap (dualLift (Pi.single j (1 : R))) ≫ x 1 = v j) := by
  intro R _ G _ _ hG d v hv
  have htan : ∀ i, IsTan (v i) := fun i => (isTan_iff _).2 (hv.1 i)
  choose L hL using fun m => ptsMap_surjective_of_isNilpotent (G := G) hv (jetTruncR R (Fin d) m)
    (jetTruncR_surjective _ m) (ker_jetTruncR_isNilpotent _ m)
  let x₁ : sp (R₀ := R) (JetR R (Fin d) 1) ⟶ G :=
    lieExp v (fun j => zR (R := R) 1 j) zR_one_mul_self
  let y : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) (m + 1)) ⟶ G :=
    fun m => Nat.rec (motive := fun m => sp (R₀ := R) (JetR R (Fin d) (m + 1)) ⟶ G) x₁
      (fun k z => L (k + 1) z) m
  let x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G :=
    fun m => Nat.casesOn (motive := fun m => sp (R₀ := R) (JetR R (Fin d) m) ⟶ G) m 1 y
  have h₁ : ∀ m, spMap (jetTruncR R (Fin d) m) ≫ x (m + 1) = x m := by
    rintro (_ | m)
    · change spMap _ ≫ lieExp v _ _ = 1
      rw [comp_lieExp, lieExp]
      exact Finset.prod_eq_one fun i _ => epsTo_zero_comp (htan i) _ (zR_zero_eq_zero i) _
    · exact hL (m + 1) (y m)
  refine ⟨x, h₁, fun m => ?_, fun j => ?_⟩
  · induction m with
    | zero => exact comp_one' _
    | succ m ih => rw [← jetZeroR_comp_jetTruncR, ← spMap_comp, Category.assoc, h₁, ih]
  · change spMap _ ≫ lieExp v _ _ = _
    rw [comp_lieExp, lieExp, Finset.prod_eq_single j]
    · have : ∀ (t : DualNumber R) (ht : t * t = 0), t = DualNumber.eps →
          epsTo R t ht = AlgHom.id R _ := fun t ht e =>
        DualNumber.algHom_ext (by rw [epsTo_eps, e]; rfl)
      rw [this _ _ (by rw [dualLift_zR, Pi.single_eq_same]; rfl), spMap_id]
      exact Category.id_comp _
    · intro i _ hi
      exact epsTo_zero_comp (htan i) _
        (by rw [dualLift_zR, Pi.single_eq_of_ne hi, TrivSqZeroExt.inr_zero]) _
    · simp

end GlobalTheory
end
end

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_isUnivChart_of_isLieBasis :
    ∀ (R : Type) [CommRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G],
      Smooth G.hom → ∀ (d : ℕ) (v : Fin d → (epsR R ⟶ G)), IsLieBasis v →
      ∃ (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G), IsUnivChart G d x ∧
        (∀ j, spMap (dualLift (Pi.single j (1 : R))) ≫ x 1 = v j) := by
  intro R _ G _ _ hG d v hv
  obtain ⟨x, h₁, h₂, h₃⟩ := GlobalTheory.exists_jetPoints_of_isLieBasis R G hG d v hv
  refine ⟨x, ⟨h₁, h₂, ?_⟩, h₃⟩
  intro A _ _ aug m hm y hy
  obtain ⟨ψ, hψ, hyψ⟩ := GlobalTheory.T.exists_jetChart_coordinates_nilpotent R G hG d v hv x h₁ h₂ h₃ A aug m hm y hy
  refine ⟨ψ, ⟨hψ, hyψ⟩, ?_⟩
  rintro ψ' ⟨hψ', hyψ'⟩
  exact GlobalTheory.T.jetChart_coordinates_unique_commGroup R G hG d v hv x h₁ h₂ h₃ A aug m hm ψ' ψ hψ' hψ (hyψ'.symm.trans hyψ)

end GlobalTheory
