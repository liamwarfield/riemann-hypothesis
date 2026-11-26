module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitClosed
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeDecompositionOfIdeleApprox
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefOverOfFiniteOrbit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensFacts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFactorAHLamDiag
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMultiplierIntegralImaginary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveOpenPartProductMapIrreducibleFibres
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveOpenPartProductMapIrreducibleFibres
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_over_lift_of_range_subset {T : Scheme.{0}} {Z H V : Over T} (e : V ⟶ H) [IsOpenImmersion e.left]
    (f : Z ⟶ H) (h : Set.range f.left ⊆ Set.range e.left) : ∃ a : Z ⟶ V, a ≫ e = f := by
  refine ⟨Over.homMk (IsOpenImmersion.lift e.left f.left h) ?_, ?_⟩
  · rw [← Over.w e, ← Category.assoc, IsOpenImmersion.lift_fac, Over.w f]
  · ext
    simp

theorem surjective_mul_of_open_of_irreducible_fibres : ∀ (T : Scheme.{0}) (H V : Over T) [GrpObj H] (e : V ⟶ H), IsOpenImmersion e.left → Surjective V.hom → (∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ T), IrreducibleSpace (pullback H.hom t : Scheme.{0})) → Surjective ((fst V V ≫ e) * (snd V V ≫ e)).left := by
  intro T H V _ e he hV hirr
  refine ⟨fun x => ?_⟩
  let t : Spec (CommRingCat.of (H.left.residueField x)) ⟶ T := H.left.fromSpecResidueField x ≫ H.hom
  let g : Over.mk t ⟶ H := Over.homMk (H.left.fromSpecResidueField x) rfl
  have hI := hirr (H.left.residueField x) t
  let X : Over T := Over.mk (pullback.snd H.hom t ≫ t)
  let p : X ⟶ H := Over.homMk (pullback.fst H.hom t) pullback.condition
  let c : X ⟶ Over.mk t := Over.homMk (pullback.snd H.hom t) rfl
  let φ : X ⟶ H := (c ≫ g) * p⁻¹
  let Y : Over T := Over.mk (pullback.snd V.hom t ≫ t)
  let q : Y ⟶ V := Over.homMk (pullback.fst V.hom t) pullback.condition
  let d : Y ⟶ Over.mk t := Over.homMk (pullback.snd V.hom t) rfl
  have hl : ∀ h : Y ⟶ H, ∃ l : Y ⟶ X, l ≫ p = h ∧ l ≫ c = d := by
    intro h
    refine ⟨Over.homMk (pullback.lift h.left (pullback.snd V.hom t) (Over.w h)) ?_, ?_, ?_⟩
    · exact pullback.lift_snd_assoc _ _ _ _
    · ext; exact pullback.lift_fst _ _ _
    · ext; exact pullback.lift_snd _ _ _
  have hY : Nonempty Y.left := by
    have : Surjective (pullback.snd V.hom t) := inferInstance
    obtain ⟨y, -⟩ := (pullback.snd V.hom t).surjective (closedPoint _)
    exact ⟨y⟩
  obtain ⟨y⟩ := hY
  have hopen : IsOpen (Set.range e.left) := e.left.isOpenEmbedding.isOpen_range
  have hne : ∀ (l : Y ⟶ X) (ψ : X ⟶ H), l ≫ ψ = q ≫ e → (ψ.left ⁻¹' Set.range e.left).Nonempty := by
    intro l ψ h
    refine ⟨l.left y, q.left y, ?_⟩
    change (q ≫ e).left y = (l ≫ ψ).left y
    rw [h]
  have h1 : (p.left ⁻¹' Set.range e.left).Nonempty := by
    obtain ⟨l, hlp, -⟩ := hl (q ≫ e)
    exact hne l p hlp
  have h2 : (φ.left ⁻¹' Set.range e.left).Nonempty := by
    obtain ⟨l, hlp, hlc⟩ := hl ((q ≫ e)⁻¹ * (d ≫ g))
    refine hne l φ ?_
    simp only [φ]
    rw [MonObj.comp_mul, GrpObj.comp_inv, hlp, ← Category.assoc, hlc]
    group
  have hI' : IrreducibleSpace X.left := hI
  have ho1 : IsOpen (p.left ⁻¹' Set.range e.left) := hopen.preimage p.left.continuous
  have ho2 : IsOpen (φ.left ⁻¹' Set.range e.left) := hopen.preimage φ.left.continuous
  obtain ⟨z, hz1, hz2⟩ := nonempty_preirreducible_inter ho1 ho2 h1 h2
  let U : X.left.Opens := ⟨_, ho1.inter ho2⟩
  let Z : Over T := Over.mk (U.ι ≫ X.hom)
  let j : Z ⟶ X := Over.homMk U.ι rfl
  obtain ⟨a, ha⟩ := exists_over_lift_of_range_subset e (j ≫ φ) (by
    rintro _ ⟨u, rfl⟩
    exact u.2.2)
  obtain ⟨b, hb⟩ := exists_over_lift_of_range_subset e (j ≫ p) (by
    rintro _ ⟨u, rfl⟩
    exact u.2.1)
  have key : lift a b ≫ ((fst V V ≫ e) * (snd V V ≫ e)) = j ≫ c ≫ g := by
    rw [MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc, ha, hb, ← MonObj.comp_mul]
    simp only [φ, inv_mul_cancel_right]
  let u : Z.left := (⟨z, hz1, hz2⟩ : U)
  refine ⟨(lift a b).left u, ?_⟩
  change (lift a b ≫ ((fst V V ≫ e) * (snd V V ≫ e))).left u = x
  rw [key]
  exact H.left.fromSpecResidueField_apply x _

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveOpenPartProductMapIrreducibleFibresStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.surjective_openPart_productMap_irreducible_fibres : ∀ (T : Scheme.{0}) (H V : Over T) [GrpObj H] (e : V ⟶ H), IsOpenImmersion e.left → Surjective V.hom → (∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ T), IrreducibleSpace (pullback H.hom t : Scheme.{0})) → Surjective ((fst V V ≫ e) * (snd V V ≫ e)).left := by
  first | exact @GlobalTheory.Mum.surjective_mul_of_open_of_irreducible_fibres | exact GlobalTheory.Mum.surjective_mul_of_open_of_irreducible_fibres | (intros; apply GlobalTheory.Mum.surjective_mul_of_open_of_irreducible_fibres <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ElementaryMatrixEndomorphismGroupPullbackTranspo
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ElementaryMatrixEndomorphismGroupPullbackTranspo
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section
namespace GlobalTheory.MatEndPull

theorem ext_of_pb {T T' : Scheme.{0}} {t : T' ⟶ T} {G : Over T} {G' : Over T'} [GrpObj G] [GrpObj G']
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G t φ) {X : Over T'} {x y : X ⟶ G'}
    (e : x.left ≫ φ = y.left ≫ φ) : x = y := by
  apply Over.OverMorphism.ext
  apply h.1.hom_ext e
  rw [Over.w x, Over.w y]

theorem one_left_eq {T : Scheme.{0}} {X M : Over T} [GrpObj M] : (1 : X ⟶ M).left = X.hom ≫ η[M].left := by
  rw [Hom.one_def, Over.comp_left]
  congr 1

theorem mul_comp_lift {T T' : Scheme.{0}} {t : T' ⟶ T} {B : Over T} {B' : Over T'} [GrpObj B] [GrpObj B']
    {φ : B'.left ⟶ B.left} (h : IsGrpPullback B' B t φ) {f : B ⟶ B} [IsMonHom f] {f' : B' ⟶ B'}
    (e : f'.left ≫ φ = φ ≫ f.left) {X : Over T'} (x y : X ⟶ B') :
    (x * y) ≫ f' = (x ≫ f') * (y ≫ f') := by
  apply ext_of_pb h
  have e₁ := h.2 X x y (pushPt h.1.w x) (pushPt h.1.w y) rfl rfl
  have e₂ := h.2 X (x ≫ f') (y ≫ f') (pushPt h.1.w x ≫ f) (pushPt h.1.w y ≫ f)
    (by simp [pushPt, e]) (by simp [pushPt, e])
  rw [← e₂, Over.comp_left, Category.assoc, e, ← Category.assoc, ← e₁, ← Over.comp_left, mul_comp]

theorem isMonHom_lift {T T' : Scheme.{0}} {t : T' ⟶ T} {B : Over T} {B' : Over T'} [GrpObj B] [GrpObj B']
    {φ : B'.left ⟶ B.left} (h : IsGrpPullback B' B t φ) {f : B ⟶ B} [IsMonHom f] {f' : B' ⟶ B'}
    (e : f'.left ≫ φ = φ ≫ f.left) : IsMonHom f' := by
  have h1 : ∀ (X : Over T'), (1 : X ⟶ B') ≫ f' = 1 := fun X => by
    have := mul_comp_lift h e (1 : X ⟶ B') 1
    rw [_root_.mul_one] at this
    exact mul_eq_left.1 this.symm
  refine ⟨?_, ?_⟩
  · have := h1 (𝟙_ _)
    simpa [Hom.one_def] using this
  · have := mul_comp_lift h e (fst B' B') (snd B' B')
    simpa [Hom.mul_def] using this

theorem unit_pull {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] {G' : Over S'}
    [GrpObj G'] {φ : G'.left ⟶ G.left} (hG : IsGrpPullback G' G f φ) :
    η[G'].left ≫ φ = f ≫ η[G].left := by
  have h := hG.2 (𝟙_ _) 1 1 (pushPt hG.1.w 1) (pushPt hG.1.w 1) rfl rfl
  rw [_root_.mul_one] at h
  have h3 : pushPt hG.1.w (1 : 𝟙_ (Over S') ⟶ G') * pushPt hG.1.w 1 = pushPt hG.1.w 1 :=
    Over.OverMorphism.ext h
  have h4 : (1 : 𝟙_ (Over S') ⟶ G').left ≫ φ = (1 : Over.mk ((𝟙_ (Over S')).hom ≫ f) ⟶ G).left :=
    congrArg Over.Hom.left (mul_eq_left.1 h3)
  rw [one_left_eq, one_left_eq] at h4
  simpa using h4

theorem matEnd_pull : ∀ {T T' : Scheme.{0}} {t : T' ⟶ T} {B C : Over T} [GrpObj B] [GrpObj C] {B' C' : Over T'} [GrpObj B'] [GrpObj C'] {φB : B'.left ⟶ B.left} {χ : C'.left ⟶ C.left} (pr : Fin 8 → (B ⟶ C)) (pr' : Fin 8 → (B' ⟶ C')) (a b : Fin 8) (f₁ : B ⟶ B) (f₁' : B' ⟶ B'), IsGrpPullback B' B t φB → IsGrpPullback C' C t χ → (∀ w, (pr' w).left ≫ χ = φB ≫ (pr w).left) → f₁'.left ≫ φB = φB ≫ f₁.left → MatEnd pr a b f₁ → MatEnd pr' a b f₁' := by
  intro T T' t B C _ _ B' C' _ _ φB χ pr pr' a b f₁ f₁' hB hC hpr e hf
  obtain ⟨hm, hw⟩ := hf
  haveI := hm
  refine ⟨isMonHom_lift hB e, fun w => ?_⟩
  apply ext_of_pb hC
  have key : (f₁' ≫ pr' w).left ≫ χ = φB ≫ (f₁ ≫ pr w).left := by
    rw [Over.comp_left, Category.assoc, hpr, ← Category.assoc, e, Category.assoc, ← Over.comp_left]
  rw [key, hw w]
  split_ifs
  · exact (hpr b).symm
  · rw [one_left_eq, one_left_eq, ← Category.assoc, hB.1.w, Category.assoc, Category.assoc,
      unit_pull hC]

end GlobalTheory.MatEndPull

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ElementaryMatrixEndomorphismGroupPullbackTranspoStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.elementaryMatrixEndomorphism_groupPullback_transport : ∀ {T T' : Scheme.{0}} {t : T' ⟶ T} {B C : Over T} [GrpObj B] [GrpObj C] {B' C' : Over T'} [GrpObj B'] [GrpObj C'] {φB : B'.left ⟶ B.left} {χ : C'.left ⟶ C.left} (pr : Fin 8 → (B ⟶ C)) (pr' : Fin 8 → (B' ⟶ C')) (a b : Fin 8) (f₁ : B ⟶ B) (f₁' : B' ⟶ B'), IsGrpPullback B' B t φB → IsGrpPullback C' C t χ → (∀ w, (pr' w).left ≫ χ = φB ≫ (pr w).left) → f₁'.left ≫ φB = φB ≫ f₁.left → MatEnd pr a b f₁ → MatEnd pr' a b f₁' := by
  first | exact @GlobalTheory.MatEndPull.matEnd_pull | exact GlobalTheory.MatEndPull.matEnd_pull | (intros; apply GlobalTheory.MatEndPull.matEnd_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightZeroSectionNonzeroAtOrigin
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightZeroSectionNonzeroAtOrigin
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.OriginSec

theorem isUnit_sval_iff' {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    IsUnit (sval s r z J) ↔ r z ∈ nonzeroLocus s := by
  have key : ∀ (U : Y.Opens) (_ : r z ∈ U) (f : Γ(Y, U)), IsUnit (gs r z U f) ↔ IsUnit (gs (𝟙 Y) (r z) U f) :=
    fun U h f => by rw [gs_stalkMap r z U h, isUnit_map_iff]
  refine ⟨fun h => (mem_nonzeroLocus s _).2 ⟨_, hJ.mem φ r, (key _ (hJ.mem φ r) _).1 h⟩, fun h => ?_⟩
  obtain ⟨j, hj, hu⟩ := (mem_nonzeroLocus s _).1 h
  rw [sval, sec_trans s r z (hJ.mem φ r) hj]
  exact (Units.isUnit _).mul ((key _ hj _).2 hu)

theorem c_zero {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) : D.c 0 = η[D.P.A] := by
  have h := D.c_add 0 0
  simp only [add_zero, padd] at h
  rw [← Hom.mul_def] at h
  have : D.c 0 = 1 := by simpa using h
  rw [this, Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]

theorem formEq_zero {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (k : ℕ) :
    FormEq (K := Fin 1) (fun _ => 𝟙 D.P.A.left) (fun _ => (k : ℤ)) (D.famφB 0) (DegPre.famε k) := by
  have e1 : (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ η[D.P.A])).left = 𝟙 D.P.A.left := by
    rw [padd, ← Hom.mul_def, ← Hom.one_def, _root_.mul_one]; rfl
  intro U _ h
  rw [Fin.prod_univ_four, Fin.prod_univ_one]
  simp only [DegPre.famφB, DegPre.famε, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, c_zero, e1]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow]
  module

end GlobalTheory.Mum.OriginSec


open GlobalTheory.Mum.OriginSec GlobalTheory.SecRingIso in
theorem GlobalTheory.Mum.exists_secB_zero_nonzero_origin : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)), ∃ k₀ : ℕ, ∀ k ≥ k₀, ∃ b : D.toPre.SecB k 0, eSec D.toPre.P.A (closedPoint R) ∈ nonzeroLocus b := by
  intro R _ _ _ _ D
  have : IsProper D.toPre.P.A.hom := D.toPre.P.isAb.proper
  obtain ⟨n, hn, a, b, ha, hb⟩ := GlobalTheory.exists_sec_succ_of_relAmple R D.toPre.P.A D.toPre.P.L D.toPre.P.isLB
    D.toPre.P.ample (eSec D.toPre.P.A (closedPoint R))
  let Q : ℕ → Prop := fun m => ∃ d : H0 D.toPre.P.L m, eSec D.toPre.P.A (closedPoint R) ∈ nonzeroLocus d
  have hQ : ∀ m m', Q m → Q m' → Q (m + m') := fun m m' ⟨d, hd⟩ ⟨d', hd'⟩ => by
    obtain ⟨e, he⟩ := exists_mul d d'
    exact ⟨e, mem_mul he hd hd'⟩
  have hij : ∀ i j : ℕ, Q (n * (i + 1) + (n + 1) * j) := by
    intro i j
    induction j with
    | zero =>
      induction i with
      | zero => simpa using (⟨a, ha⟩ : Q n)
      | succ i ih =>
        have := hQ _ _ ih ⟨a, ha⟩
        rwa [show n * (i + 1 + 1) + (n + 1) * 0 = n * (i + 1) + (n + 1) * 0 + n by ring]
    | succ j ih =>
      have := hQ _ _ ih ⟨b, hb⟩
      rwa [show n * (i + 1) + (n + 1) * (j + 1) = n * (i + 1) + (n + 1) * j + (n + 1) by ring]
  refine ⟨n * (n + 1), fun k hk => ?_⟩
  obtain ⟨d, hd⟩ : Q k := by
    have hk' : n * (k / n) + k % n = k := Nat.div_add_mod k n
    have hr : k % n < n := Nat.mod_lt _ hn
    have hq : n + 1 ≤ k / n := (Nat.le_div_iff_mul_le hn).2 (by rw [mul_comm]; exact hk)
    obtain ⟨t, ht⟩ : ∃ t, k / n = k % n + 1 + t := ⟨k / n - k % n - 1, by omega⟩
    have e : k = n * (t + 1) + (n + 1) * (k % n) := by
      conv_lhs => rw [← hk', ht]
      ring
    rw [e]
    exact hij _ _
  obtain ⟨b', hb'⟩ := exists_sec D.toPre.P.isLB (formEq_zero D.toPre k) d
  refine ⟨b', ?_⟩
  obtain ⟨J, hJ⟩ : ∃ J, Good D.toPre.P.L (eSec D.toPre.P.A (closedPoint R)) J :=
    ⟨fun χ => (exists_chart D.toPre.P.isLB (χ (eSec D.toPre.P.A (closedPoint R)))).choose,
      fun χ => (exists_chart D.toPre.P.isLB (χ (eSec D.toPre.P.A (closedPoint R)))).choose_spec⟩
  have h1 := (isUnit_sval_iff' d (𝟙 _) _ hJ).2 hd
  rw [← hb' _ (𝟙 _) _ J hJ] at h1
  exact (isUnit_sval_iff' b' (𝟙 _) _ hJ).1 h1
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightZeroSectionNonzeroAtOriginStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weightZero_section_nonzero_at_origin : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)), ∃ k₀ : ℕ, ∀ k ≥ k₀, ∃ b : D.toPre.SecB k 0, eSec D.toPre.P.A (closedPoint R) ∈ nonzeroLocus b := by
  first | exact @GlobalTheory.Mum.exists_secB_zero_nonzero_origin | exact GlobalTheory.Mum.exists_secB_zero_nonzero_origin | (intros; apply GlobalTheory.Mum.exists_secB_zero_nonzero_origin <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisTransitiveOnFibresFlatBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisTransitiveOnFibresFlatBaseChange
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.GalOrbit

variable {R R' : Type} [CommRing R] [CommRing R'] {ρ : R →+* R'}

theorem spMap_gal_comp (σ : Gal ρ) : spMap (Gal.hom σ) ≫ spMap ρ = spMap ρ := by
  rw [← Spec.map_comp]; congr 1; ext r; exact σ.2 r

theorem spMap_gal_mul (σ τ : Gal ρ) :
    spMap (Gal.hom (σ * τ)) = spMap (Gal.hom σ) ≫ spMap (Gal.hom τ) := by
  rw [← Spec.map_comp]; rfl

theorem spMap_gal_one : spMap (Gal.hom (1 : Gal ρ)) = 𝟙 _ := by
  rw [← Spec.map_id]; rfl

variable {X Z : Scheme.{0}} {f : X ⟶ Sp R} {p : Z ⟶ X} {s : Z ⟶ Sp R'}
  (hpb : IsPullback p s f (spMap ρ))

def act (σ : Gal ρ) : Z ⟶ Z :=
  hpb.lift p (s ≫ spMap (Gal.hom σ)) (by rw [Category.assoc, spMap_gal_comp, hpb.w])

@[reassoc] theorem galoisBaseChangeSchemeAction_comp_snd (σ : Gal ρ) : act hpb σ ≫ s = s ≫ spMap (Gal.hom σ) := hpb.lift_snd _ _ _

theorem act_one : act hpb 1 = 𝟙 Z := by
  have hp : act hpb 1 ≫ p = p := hpb.lift_fst _ _ _
  exact hpb.hom_ext (by rw [hp, Category.id_comp])
    (by rw [galoisBaseChangeSchemeAction_comp_snd, spMap_gal_one, Category.comp_id, Category.id_comp])

theorem act_mul (σ τ : Gal ρ) : act hpb (σ * τ) = act hpb σ ≫ act hpb τ := by
  have hp (g : Gal ρ) : act hpb g ≫ p = p := hpb.lift_fst _ _ _
  exact hpb.hom_ext (by rw [hp, Category.assoc, hp, hp])
    (by rw [galoisBaseChangeSchemeAction_comp_snd, Category.assoc, galoisBaseChangeSchemeAction_comp_snd, galoisBaseChangeSchemeAction_comp_snd_assoc, spMap_gal_mul])

def actAut : Gal ρ →* Aut Z where
  toFun σ :=
    { asIso :=
        { hom := act hpb σ⁻¹
          inv := act hpb σ
          hom_inv_id := by rw [← act_mul, inv_mul_cancel, act_one]
          inv_hom_id := by rw [← act_mul, mul_inv_cancel, act_one] } }
  map_one' := Aut.ext (Iso.ext (by change act hpb 1⁻¹ = 𝟙 Z; rw [inv_one, act_one]))
  map_mul' σ τ := Aut.ext (Iso.ext (by
    change act hpb (σ * τ)⁻¹ = act hpb τ⁻¹ ≫ act hpb σ⁻¹
    rw [mul_inv_rev, act_mul]))

end GlobalTheory.Mum.GalOrbit

namespace GlobalTheory.Mum

theorem gal_transitive_on_fibres : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'],
    Function.Injective (algebraMap R R') → IsGal (algebraMap R R') → ∀ (Y : Over (Sp R)), Flat Y.hom →
    ∀ (Z : Scheme.{0}) (p : Z ⟶ Y.left) (s : Z ⟶ Sp R'), IsPullback p s Y.hom (spMap (algebraMap R R')) →
    ∀ z z' : Z, p z = p z' → ∃ (σ : Gal (algebraMap R R')) (h : Z ⟶ Z),
      h ≫ p = p ∧ h ≫ s = s ≫ spMap (Gal.hom σ) ∧ h z = z' := by
  intro R R' _ _ _ hinj hG Y hfl Z p s hpb z z' hzz
  have : Finite (Gal (algebraMap R R')) := hG.1
  have : Flat Y.hom := hfl
  have : IsAffineHom p := MorphismProperty.of_isPullback (P := @IsAffineHom) hpb.flip inferInstance
  have hp (σ : Gal (algebraMap R R')) : GalOrbit.act hpb σ ≫ p = p := hpb.lift_fst _ _ _
  have hinv : ∀ W : Y.left.Opens, IsAffineOpen W → ∀ u : Γ(Z, p ⁻¹ᵁ W),
      GlobalTheory.IsInvariantSection (GalOrbit.actAut hpb) _ u → u ∈ Set.range (p.app W) := by
    intro W hW u hu
    refine (InvFun.affine_inv (algebraMap R R') hinj hG hpb (GalOrbit.act hpb) hp
      (GalOrbit.galoisBaseChangeSchemeAction_comp_snd hpb) hW).2 u fun σ hσ => ?_
    obtain ⟨h₁, h₂⟩ := hu σ⁻¹
    have key : ∀ (τ τ' : Gal (algebraMap R R')) (_ : τ = τ') (e : p ⁻¹ᵁ W ≤ GalOrbit.act hpb τ ⁻¹ᵁ (p ⁻¹ᵁ W))
        (e' : p ⁻¹ᵁ W ≤ GalOrbit.act hpb τ' ⁻¹ᵁ (p ⁻¹ᵁ W)),
        ((GalOrbit.act hpb τ).appLE _ _ e).hom u = ((GalOrbit.act hpb τ').appLE _ _ e').hom u := by
      rintro τ _ rfl _ _; rfl
    exact (key _ _ (inv_inv σ).symm hσ h₁).trans h₂
  obtain ⟨g, hg⟩ := (GlobalTheory.apply_eq_iff_exists_aut_of_invariant (GalOrbit.actAut hpb) p
    (fun g => hp g⁻¹) hinv z z').1 hzz
  exact ⟨g⁻¹, GalOrbit.act hpb g⁻¹, hp _, GalOrbit.galoisBaseChangeSchemeAction_comp_snd hpb _, hg⟩

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisTransitiveOnFibresFlatBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_transitive_on_fibres_flat_baseChange : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'], Function.Injective (algebraMap R R') → IsGal (algebraMap R R') → ∀ (Y : Over (Sp R)), Flat Y.hom → ∀ (Z : Scheme.{0}) (p : Z ⟶ Y.left) (s : Z ⟶ Sp R'), IsPullback p s Y.hom (spMap (algebraMap R R')) → ∀ z z' : Z, p z = p z' → ∃ (σ : Gal (algebraMap R R')) (h : Z ⟶ Z), h ≫ p = p ∧ h ≫ s = s ≫ spMap (Gal.hom σ) ∧ h z = z' := by
  first | exact @GlobalTheory.Mum.gal_transitive_on_fibres | exact GlobalTheory.Mum.gal_transitive_on_fibres | (intros; apply GlobalTheory.Mum.gal_transitive_on_fibres <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpTorsionDefOver
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep

variable {V V₁ : Type} [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁]

theorem exists_points_equiv {W₀ : Type} [CommRing W₀] (ρ : V →+* V₁) (ib : W₀ →+* V) (Q : Data V) (D : DegPre V₁)
    (pr : Fin 8 → (D.P.A ⟶ (Over.pullback (spMap ρ)).obj Q.B)) (hpr : ∀ a, IsMonHom (pr a))
    (huniv : ∀ (T : Over (Sp V₁)) (y : Fin 8 → (T ⟶ (Over.pullback (spMap ρ)).obj Q.B)),
      ∃! x : T ⟶ D.P.A, ∀ a, x ≫ pr a = y a)
    (B₀ : Over (Sp W₀)) [GrpObj B₀] (β : Q.B.left ⟶ B₀.left) (hβ : IsGrpPullback Q.B B₀ (spMap ib) β)
    {X : Scheme.{0}} (t : X ⟶ Sp V₁) (g : X ⟶ Sp W₀) (hg : t ≫ spMap ρ ≫ spMap ib = g) :
    ∃ Φ : (Over.mk t ⟶ D.P.A) ≃* (Fin 8 → (Over.mk g ⟶ B₀)),
      ∀ x a, (Φ x a).left = x.left ≫ (pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) ≫ β := by
  obtain ⟨E1, hE1⟩ := GlobalTheory.GroupBplus.Aff.exists_mulEquiv_points_of_isGrpPullback
    (isGrpPullback_pullback Q.B (spMap ρ)) t (t ≫ spMap ρ) rfl
  obtain ⟨E2, hE2⟩ := GlobalTheory.GroupBplus.Aff.exists_mulEquiv_points_of_isGrpPullback hβ (t ≫ spMap ρ) g
    (by rw [Category.assoc]; exact hg)
  let P : (Over.mk t ⟶ D.P.A) →* (Fin 8 → (Over.mk t ⟶ (Over.pullback (spMap ρ)).obj Q.B)) :=
    Pi.monoidHom fun a =>
      { toFun := fun x => x ≫ pr a
        map_one' := MonObj.one_comp _
        map_mul' := fun x y => MonObj.mul_comp _ _ _ }
  have hP : Function.Bijective P := by
    refine ⟨fun x y h => ?_, fun y => ?_⟩
    · obtain ⟨z, -, hz⟩ := huniv (Over.mk t) (P x)
      exact (hz x fun a => rfl).trans (hz y fun a => (congrFun h a).symm).symm
    · obtain ⟨z, hz, -⟩ := huniv (Over.mk t) y
      exact ⟨z, funext hz⟩
  refine ⟨(MulEquiv.ofBijective P hP).trans (MulEquiv.piCongrRight fun _ => E1.trans E2), fun x a => ?_⟩
  show (E2 (E1 (x ≫ pr a))).left = _
  rw [hE2, hE1, Over.comp_left]
  simp only [Category.assoc]

theorem spMap_three {A B C E : Type} [CommRing A] [CommRing B] [CommRing C] [CommRing E] (f : A →+* B) (g : B →+* C)
    (h : C →+* E) : spMap h ≫ spMap g ≫ spMap f = spMap ((h.comp g).comp f) := by
  simp only [spMap, ← Spec.map_comp]; rfl

theorem sharp_c_defOver {W₀ : Type} [CommRing W₀] (ρ : V →+* V₁) (ib : W₀ →+* V) (Q : Data V) (D : DegPre V₁)
    (e : (Fin 8 → Q.X) ≃+ D.X) (pr : Fin 8 → (D.P.A ⟶ (Over.pullback (spMap ρ)).obj Q.B))
    (hc : ∀ mu a, (D.c (e mu) ≫ pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) = spMap ρ ≫ (Q.c (mu a)).left)
    (B₀ : Over (Sp W₀)) (β : Q.B.left ⟶ B₀.left) (c₀ : Q.X → (𝟙_ (Over (Sp W₀)) ⟶ B₀))
    (hβc : ∀ a, (Q.c a).left ≫ β = spMap ib ≫ (c₀ a).left)
    (K : Type) [Field K] (ev : V₁ →+* K) (k₀ : Subfield K) (hk : ∀ a, ev (ρ (ib a)) ∈ k₀) :
    ∀ mu a, DefOver k₀ (spMap ev ≫ (D.c (e mu) ≫ pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) ≫ β) := by
  intro mu a
  have h : spMap ev ≫ (D.c (e mu) ≫ pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) ≫ β =
      spMap ((ev.comp ρ).comp ib) ≫ (c₀ (mu a)).left := by
    rw [reassoc_of% (hc mu a), hβc, ← spMap_three]
    simp only [Category.assoc]
  rw [h]
  refine ⟨spMap (((ev.comp ρ).comp ib).codRestrict k₀ hk) ≫ (c₀ (mu a)).left, ?_⟩
  rw [← Category.assoc]
  congr 1
  simp only [spMap, ← Spec.map_comp]; rfl

theorem sharp_torsion_defOver {W₀ : Type} [CommRing W₀] [IsNoetherianRing V₁] (ρ : V →+* V₁) (ib : W₀ →+* V)
    (Q : Data V) (D : DegPre V₁)
    (pr : Fin 8 → (D.P.A ⟶ (Over.pullback (spMap ρ)).obj Q.B)) (hpr : ∀ a, IsMonHom (pr a))
    (huniv : ∀ (T : Over (Sp V₁)) (y : Fin 8 → (T ⟶ (Over.pullback (spMap ρ)).obj Q.B)),
      ∃! x : T ⟶ D.P.A, ∀ a, x ≫ pr a = y a)
    (B₀ : Over (Sp W₀)) [GrpObj B₀] (β : Q.B.left ⟶ B₀.left) (hβ : IsGrpPullback Q.B B₀ (spMap ib) β)
    (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K) (hk₀ : IsAlgClosed k₀)
    (hk : ∀ a, ev (ρ (ib a)) ∈ k₀) (N : ℕ) (hN : 1 ≤ N) (hNu : IsUnit (N : V₁))
    (x : Over.mk (spMap ev) ⟶ D.P.A) (hx : x ^ N = 1) (a : Fin 8) :
    DefOver k₀ (x.left ≫ (pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) ≫ β) := by
  classical
  obtain ⟨Φ, hΦ⟩ := exists_points_equiv ρ ib Q D pr hpr huniv B₀ β hβ (spMap ev) (spMap ((ev.comp ρ).comp ib))
    (spMap_three _ _ _)
  have hNK : (N : K) ≠ 0 := by
    have := (hNu.map ev).ne_zero
    simpa using this
  have hcard := (GlobalTheory.abelianSchemeLaws_all.1.mulN (Sp V₁) D.P N hN).2.2.2.2 K (spMap ev) hNK
  have hfin : Finite {y : Over.mk (spMap ev) ⟶ D.P.A // y ^ N = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ (by omega))
  refine defOver_of_finite_orbit K k₀ hk₀ _ _ ((Set.finite_range fun y : {y : Over.mk (spMap ev) ⟶ D.P.A // y ^ N = 1} =>
    (Φ y.1 a).left).subset ?_)
  rintro _ ⟨σ, hσ, rfl⟩
  have hσf : spMap σ.toRingHom ≫ spMap ((ev.comp ρ).comp ib) = spMap ((ev.comp ρ).comp ib) := by
    simp only [spMap, ← Spec.map_comp]
    congr 2
    ext w
    exact hσ _ (hk w)
  let h : Over.mk (spMap ((ev.comp ρ).comp ib)) ⟶ Over.mk (spMap ((ev.comp ρ).comp ib)) :=
    Over.homMk (spMap σ.toRingHom) hσf
  refine ⟨⟨Φ.symm (fun b => h ≫ Φ x b), ?_⟩, ?_⟩
  · have e : (fun b => h ≫ Φ x b) ^ N = 1 := by
      funext b
      rw [Pi.pow_apply, ← MonObj.comp_pow, ← Pi.pow_apply, ← map_pow, hx, map_one, Pi.one_apply, MonObj.comp_one]
    rw [← map_pow, e, map_one]
  · show (Φ (Φ.symm fun b => h ≫ Φ x b) a).left = _
    rw [MulEquiv.apply_symm_apply, Over.comp_left, hΦ]
    rfl

end GlobalTheory.Poinc.Sep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearisationInvariantRigidifiedBundle
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearisationInvariantRigidifiedBundle
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.GenDesc

noncomputable section

namespace GlobalTheory.MumLin

variable {X Y Z : Scheme.{0}} {L : LB X}

theorem exists_gen_diff (hL : L.IsLB) (σ : X ⟶ X) (h : LBIso L (L.pull σ)) :
    ∃ w : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, σ] ![1, -1]), w.IsGen := by
  have h1 := (GlobalTheory.TripleCompare.lbIso_iff_pull_id L (L.pull σ)).1 h
  obtain ⟨t, ht⟩ := (GlobalTheory.TripleCompare.lbIso_iff_gen _ _ _ _).1 h1
  obtain ⟨w, hw, -⟩ := DVR.gen_transport (φ' := ![𝟙 X, σ]) (ε' := ![1, -1]) hL (by
    rw [DVR.sameSum_iff_fsum, DVR.fsum_sumElim]
    simp [DVR.fsum, Fin.sum_univ_two]) t ht
  exact ⟨w, hw⟩

theorem corr_of_pull_section (hL : L.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')} (ht : t.IsGen) (ht' : t'.IsGen)
    (hs : DVR.fsum φ ε = DVR.fsum φ' ε') (p : Y ⟶ Z) (z : Z ⟶ Y) (hzp : z ≫ p = 𝟙 Z)
    (hp : Function.Surjective p.appTop.hom)
    (H : LB.Gen.Corr L _ ε _ ε' (LB.pullGen L φ ε t z) (LB.pullGen L φ' ε' t' z)) :
    LB.Gen.Corr L φ ε φ' ε' t t' := by
  have hq : (LB.mulGen L _ _ _ _ t (LB.invGen L φ' ε' t')).IsGen :=
    DVR.mulGen_isGen_of_isGen t ht _ (DVR.invGen_isGen_of_isGen t' ht')
  have h0 : DVR.fsum (fun k => 𝟙 Y ≫ Sum.elim φ φ' k) (Sum.elim ε fun k => -ε' k) = 0 := by
    rw [DVR.fsum_comp, DVR.fsum_sumElim, DVR.fsum_neg, hs, add_neg_cancel, Finsupp.mapDomain_zero]
  obtain ⟨c, hc⟩ := DVR.exists_value hL _ _ _ hq (𝟙 Y) h0
  have key : ∀ (W : Scheme.{0}) (r : W ⟶ Y) (w : W) (J : (W ⟶ X) → L.ι), Good L w J →
      val (LB.mulGen L _ _ _ _ t (LB.invGen L φ' ε' t')) r w J = gm r w ⊤ c := by
    intro W r w J hJ
    have e1 := val_pull hJ (LB.mulGen L _ _ _ _ t (LB.invGen L φ' ε' t')) (𝟙 Y) r
    rw [Category.comp_id] at e1
    rw [← e1, val_of _ r w J (fun k => J (r ≫ 𝟙 Y ≫ Sum.elim φ φ' k)) (fun _ => rfl),
      ← hc _ (fun k₁ k₂ e => by simp only [e])]
    exact gm_res r w le_top (hJ.mem _ r) c
  have hz1 : ∀ w : Z, gm z w ⊤ c = 1 := by
    intro w
    obtain ⟨J, hJ, -⟩ := exists_good (Z := Z) L hL w (K := PEmpty) PEmpty.elim PEmpty.elim
      (fun a => a.elim) (fun a => a.elim)
    have e1 := val_pull hJ t z (𝟙 Z)
    have e2 := val_pull hJ t' z (𝟙 Z)
    rw [Category.id_comp] at e1 e2
    rw [← key Z z w J hJ, val_mul hJ, val_inv, ← e1, ← e2, val_corr hJ H, mul_inv_cancel]
  obtain ⟨d, hd⟩ := hp c.val
  have d1 : d = 1 := fn_ext fun w _ => by
    have e' : gm (𝟙 Z ≫ z) w ⊤ c = 1 := by rw [Category.id_comp]; exact hz1 w
    have e'' := (gs_pull (𝟙 Z ≫ z) p w ⊤ trivial d).symm.trans ((congrArg (gs (𝟙 Z ≫ z) w ⊤) hd).trans
      ((gs_unit _ w ⊤ trivial c).trans (congrArg Units.val e')))
    rw [Category.assoc, hzp, Category.comp_id] at e''
    rw [e'', gs_eq _ w ⊤ trivial, map_one, map_one, Units.val_one]
  have c1 : c = 1 := Units.ext (by rw [← hd, d1, map_one]; rfl)
  refine corr_of_val hL fun y J hJ => ?_
  have e := key Y (𝟙 Y) y J hJ
  rw [c1, map_one, val_mul hJ, val_inv, mul_inv_eq_one] at e
  exact e

theorem exists_linearisation : ∀ (T X : Scheme.{0}) (π : X ⟶ T) (e : T ⟶ X), e ≫ π = 𝟙 T → Function.Surjective π.appTop.hom → ∀ (L : LB X), L.IsLB → (∃ r : LB.Gen (L.pull e), r.IsGen) → ∀ (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (θ : Ga → (T ⟶ T)), (∀ a c, ρ (a * c) = ρ a ≫ ρ c) → (∀ a c, θ (a * c) = θ a ≫ θ c) → (∀ a, e ≫ ρ a = θ a ≫ e) → (∀ a, LBIso L (L.pull (ρ a))) → ∃ u : ∀ a, LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, ρ a] ![1, -1]), (∀ a, (u a).IsGen) ∧ ∀ a c, LB.Gen.Corr L _ _ _ _ (u (a * c)) (LB.mulGen L _ _ _ _ (u a) (LB.pullGen L _ _ (u c) (ρ a))) := by
  intro T X π e he hπ L hL ⟨r, hr⟩ Ga _ ρ θ hρ hθ heρ hiso
  have hex : ∀ a, ∃ u : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, ρ a] ![1, -1]), u.IsGen ∧
      LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u e)
        (LB.mulGen L _ _ _ _ r (LB.invGen L _ _ (LB.pullGen L _ _ r (θ a)))) := by
    intro a
    obtain ⟨w, hw⟩ := exists_gen_diff hL (ρ a) (hiso a)
    refine DVR.exists_normalized_to hL _ _ w hw π e he _ _ _
      (DVR.mulGen_isGen_of_isGen r hr _ (DVR.invGen_isGen_of_isGen _ (DVR.pullGen_isGen_of_isGen _ _ r hr _))) ?_
    rw [DVR.fsum_sumElim]
    simp [DVR.fsum, Fin.sum_univ_two, heρ a]
  choose u hu hue using hex
  refine ⟨u, hu, fun a c => ?_⟩
  refine corr_of_pull_section hL (hu _) (DVR.mulGen_isGen_of_isGen _ (hu a) _ (DVR.pullGen_isGen_of_isGen _ _ _ (hu c) _))
    ?_ π e he hπ ?_
  · rw [DVR.fsum_sumElim]
    simp only [DVR.fsum, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Category.comp_id, hρ]
    rw [add_assoc, ← add_assoc (Finsupp.single (ρ a) (-1 : ℤ)), ← Finsupp.single_add, neg_add_cancel, Finsupp.single_zero,
      zero_add]
  · refine corr_of_val hL fun y J hJ => ?_
    have v1 := val_corr hJ (hue (a * c)) (𝟙 T)
    have v2 := val_corr hJ (hue a) (𝟙 T)
    have v3 := val_corr hJ (hue c) (θ a)
    simp only [val_mul hJ, val_inv, val_pull hJ, Category.id_comp, Category.assoc, hθ] at v1 v2 v3 ⊢
    rw [heρ a, v1, v2, v3, _root_.mul_assoc, inv_mul_cancel_left]

end GlobalTheory.MumLin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearisationInvariantRigidifiedBundleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.GenDesc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linearisation_invariant_rigidified_bundle : ∀ (T X : Scheme.{0}) (π : X ⟶ T) (e : T ⟶ X), e ≫ π = 𝟙 T → Function.Surjective π.appTop.hom → ∀ (L : LB X), L.IsLB → (∃ r : LB.Gen (L.pull e), r.IsGen) → ∀ (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (θ : Ga → (T ⟶ T)), (∀ a c, ρ (a * c) = ρ a ≫ ρ c) → (∀ a c, θ (a * c) = θ a ≫ θ c) → (∀ a, e ≫ ρ a = θ a ≫ e) → (∀ a, LBIso L (L.pull (ρ a))) → ∃ u : ∀ a, LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, ρ a] ![1, -1]), (∀ a, (u a).IsGen) ∧ ∀ a c, LB.Gen.Corr L _ _ _ _ (u (a * c)) (LB.mulGen L _ _ _ _ (u a) (LB.pullGen L _ _ (u c) (ρ a))) := by
  first | exact @GlobalTheory.MumLin.exists_linearisation | exact GlobalTheory.MumLin.exists_linearisation | (intros; apply GlobalTheory.MumLin.exists_linearisation <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinProdIsGen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.MumSide

section Helpers
variable {X Y : Scheme.{0}} {L : LB X}

theorem exists_zpow (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (n : ℤ) :
    ∃ t' : LB.Gen (LB.LinComb L φ (fun k => n * ε k)), t'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J → val t' r z J = val t r z J ^ n := by
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · exact ⟨GeneratorPullback.powGen L φ ε t m, DVR.powGen_isGen _ _ _ _ ht m,
      fun Z r z J _ => (DVR.val_pow t m r z J).trans (zpow_natCast _ _).symm⟩
  · obtain ⟨t', ht', hv⟩ := exists_gen hL (φ' := φ) (ε' := fun k => -(m : ℤ) * ε k) (fun U _ h => by
        refine Finset.prod_congr rfl fun k _ => ?_
        show _ = h (φ k) ^ (-(m : ℤ) * ε k)
        rw [neg_mul]) (LB.invGen L _ _ (GeneratorPullback.powGen L φ ε t m))
        (DVR.invGen_isGen _ _ _ _ (DVR.powGen_isGen _ _ _ _ ht m))
    refine ⟨t', ht', fun Z r z J hJ => ?_⟩
    rw [hv Z r z J hJ, val_inv, DVR.val_pow, zpow_neg, zpow_natCast]

theorem finProd_isGen {I K : Type} [Fintype I] [Fintype K] (φ : I → K → (Y ⟶ X)) (ε : I → K → ℤ)
    (t : ∀ i, LB.Gen (LB.LinComb L (φ i) (ε i))) (ht : ∀ i, (t i).IsGen) : (GeneratorPullback.finProdGen L φ ε t).IsGen := by
  intro (j : I × K → L.ι) (j' : I × K → L.ι)
  refine unit_ext fun y hy => ?_
  have v : ∀ j : I × K → L.ι, y ∈ LB.wchart L (fun p : I × K => φ p.1 p.2) j →
      gm (𝟙 Y) y (LB.wchart L (fun p : I × K => φ p.1 p.2) j) ((GeneratorPullback.finProdGen L φ ε t).s j) =
        ∏ i, gm (𝟙 Y) y (LB.wchart L (φ i) (fun k => j (i, k))) ((t i).s (fun k => j (i, k))) := fun j hj =>
    (map_prod _ _ _).trans (Finset.prod_congr rfl fun _ _ => gm_res (𝟙 Y) y _ hj _)
  refine ((gm_res (𝟙 Y) y _ hy _).trans (v j hy.1)).trans (Eq.trans ?_ ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (gm_linComb L _ _ (𝟙 Y) y j j' hy.1 hy.2) ((gm_res (𝟙 Y) y _ hy _).trans (v j' hy.2)))).symm)
  rw [Fintype.prod_prod_type, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => gen_trans (ht i) (𝟙 Y) y
    (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.1 (i, k)) (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.2 (i, k))

theorem val_finProd {I K : Type} [Fintype I] [Fintype K] (φ : I → K → (Y ⟶ X)) (ε : I → K → ℤ)
    (t : ∀ i, LB.Gen (LB.LinComb L (φ i) (ε i))) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    val (GeneratorPullback.finProdGen L φ ε t) r z J = ∏ i, val (t i) r z J :=
  (map_prod _ _ _).trans (Finset.prod_congr rfl fun i _ =>
    gm_res r z _ (hJ.mem (fun p : I × K => φ p.1 p.2) r) _)

end Helpers

section Rows
variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}

theorem comp_tensφ' {S : Scheme.{0}} {B B' T : Over S} [GrpObj B] (pr : Fin r → (B' ⟶ B)) (x : T ⟶ B')
    (k : (Fin r × Fin r) × Fin 4) : x.left ≫ tensφ pr k = GlobalTheory.PolDeg.lamPts (x ≫ pr k.1.1) (x ≫ pr k.1.2) k.2 := by
  obtain ⟨⟨i, j⟩, k⟩ := k
  fin_cases k
  · exact congrArg (·.left) (MonObj.comp_mul x (pr i) (pr j))
  · rfl
  · rfl
  · exact congrArg (·.left) (MonObj.comp_one (M := B) x)

theorem matAct_zero (T : Tens D D' W) : GlobalTheory.TensAct.matAct T 0 = 1 := by
  have h := GlobalTheory.TensAct.matAct_add T 0 0
  rw [add_zero] at h
  exact mul_eq_left.1 h.symm

theorem four_eq (T : Tens D D' W) (A : Matrix (Fin r) (Fin r) ℤ) (f : D'.P.A ⟶ D'.P.A)
    (hf : f = GlobalTheory.TensAct.matAct T A) (a : Fin 4) :
    (![(padd D'.P.A (𝟙 _) f).left, 𝟙 D'.P.A.left, f.left, (toUnit D'.P.A ≫ η[D'.P.A]).left] :
      Fin 4 → (D'.P.A.left ⟶ D'.P.A.left)) a =
      (GlobalTheory.TensAct.matAct T ((![1 + A, 1, A, 0] : Fin 4 → Matrix (Fin r) (Fin r) ℤ) a)).left := by
  subst hf
  fin_cases a
  · show (padd D'.P.A (𝟙 _) _).left = (GlobalTheory.TensAct.matAct T (1 + A)).left
    rw [GlobalTheory.TensAct.matAct_add, GlobalTheory.TensAct.matAct_one]; rfl
  · show 𝟙 D'.P.A.left = (GlobalTheory.TensAct.matAct T 1).left
    rw [GlobalTheory.TensAct.matAct_one]; rfl
  · rfl
  · show (toUnit D'.P.A ≫ η[D'.P.A]).left = (GlobalTheory.TensAct.matAct T 0).left
    rw [matAct_zero]; rfl

theorem sum_one_smul {X : Type} [AddCommGroup X] (v : Fin r → X) (i : Fin r) :
    ∑ k, (1 : Matrix (Fin r) (Fin r) ℤ) i k • v k = v i := by
  rw [Finset.sum_eq_single i]
  · rw [Matrix.one_apply_eq, one_smul]
  · intro l _ hl
    rw [Matrix.one_apply_ne hl.symm, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem xe_four (T : Tens D D' W) (A : Matrix (Fin r) (Fin r) ℤ) (y : D'.X) (a : Fin 4) (i : Fin r) :
    T.xe ((![y + GlobalTheory.TensAct.latAct T A y, y, GlobalTheory.TensAct.latAct T A y, 0] : Fin 4 → D'.X) a) i =
      ∑ k, (![1 + A, 1, A, 0] : Fin 4 → Matrix (Fin r) (Fin r) ℤ) a i k • T.xe y k := by
  fin_cases a
  · show T.xe (y + GlobalTheory.TensAct.latAct T A y) i = ∑ k, (1 + A) i k • T.xe y k
    rw [map_add (f := _), Pi.add_apply, GlobalTheory.TensAct.xe_latAct]
    simp only [Matrix.add_apply, add_smul, Finset.sum_add_distrib, sum_one_smul]
  · show T.xe y i = ∑ k, (1 : Matrix (Fin r) (Fin r) ℤ) i k • T.xe y k
    rw [sum_one_smul]
  · show T.xe (GlobalTheory.TensAct.latAct T A y) i = ∑ k, A i k • T.xe y k
    rw [GlobalTheory.TensAct.xe_latAct]
  · show T.xe 0 i = ∑ k, (0 : Matrix (Fin r) (Fin r) ℤ) i k • T.xe y k
    simp only [map_zero, Pi.zero_apply, Matrix.zero_apply, zero_smul, Finset.sum_const_zero]

end Rows

end GlobalTheory.MumSide
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineChartRatLift
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory.Points
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.UPoinc.ChartAt

theorem spec_ext_of_isFractionRing {A K T : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
    [CommRing T] (h₁ h₂ : Sp T ⟶ Sp K) (e : h₁ ≫ spMap (algebraMap A K) = h₂ ≫ spMap (algebraMap A K)) : h₁ = h₂ := by
  obtain ⟨g₁, rfl⟩ := Spec.map_surjective h₁
  obtain ⟨g₂, rfl⟩ := Spec.map_surjective h₂
  rw [spMap, ← Spec.map_comp, ← Spec.map_comp] at e
  have e' := congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  congr 1
  ext1
  exact IsLocalization.ringHom_ext (nonZeroDivisors A) e'

theorem exists_int_dvd {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {cf : Coeff l} (C : UCompact Xo cf) {a : C.o} (ha : a ≠ 0) :
    ∃ n : ℤ, n ≠ 0 ∧ a ∣ (n : C.o) := by
  haveI := C.ded
  have h1 : IsAlgebraic ℚ (C.b a) := Algebra.IsAlgebraic.isAlgebraic _
  have h2 : IsAlgebraic ℤ (C.b a) := (IsFractionRing.isAlgebraic_iff ℤ ℚ cf.F).2 h1
  have h3 : IsAlgebraic ℤ a := (isAlgebraic_algHom_iff C.b.toIntAlgHom C.inj).1 h2
  have h4 := Ideal.comap_ne_bot_of_algebraic_mem ha (Ideal.mem_span_singleton_self a) h3
  obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h4
  refine ⟨n, hn0, ?_⟩
  have := Ideal.mem_span_singleton.1 (Ideal.mem_comap.1 hn)
  simpa using this

end GlobalTheory.UPoinc.ChartAt

namespace GlobalTheory.UPoinc.ChartAt

theorem exists_affine_chart_ratLift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X : USetup C) (w : X.M.Z), X.π w ∈ Set.range C.i → ∃ (U₀ : X.M.Z.Opens) (u₀ : Sp (ratHull (X.M.ringOn U₀)) ⟶ Xo.XF cf), IsAffineOpen U₀ ∧ w ∈ U₀ ∧ spMap (ratHull (X.M.ringOn U₀)).val.toRingHom ≫ u₀ = X.uΩ := by
  intro E _ _ _ H Dw l Xo cf C X w hw
  haveI := X.ar.char
  haveI := C.iF_open
  haveI := C.ded
  letI := C.b.toAlgebra
  haveI := C.isFractionRing
  haveI : IsPreimmersion (spMap C.b) := IsPreimmersion.of_isLocalization (nonZeroDivisors C.o)
  have hemb := Scheme.Hom.isEmbedding (pullback.fst C.z (spMap C.b))
  obtain ⟨V, hVo, hV⟩ := hemb.isInducing.isOpen_iff.1 C.iF.isOpenEmbedding.isOpen_range
  set V' : X.M.Z.Opens := X.π ⁻¹ᵁ ⟨V, hVo⟩ with hV'def
  have hwV : w ∈ V' := by
    obtain ⟨x, hx⟩ := hw
    show X.π w ∈ V
    have : C.iF x ∈ pullback.fst C.z (spMap C.b) ⁻¹' V := hV ▸ ⟨x, rfl⟩
    rw [← hx]
    simpa using this
  obtain ⟨U, hU, hwU, hUV⟩ := exists_isAffineOpen_mem_and_subset (X := X.M.Z) (U := V') hwV
  have hne : ((U : X.M.Z.Opens) : Set X.M.Z).Nonempty := ⟨w, hwU⟩
  set R₀ := X.M.ringOn U with hR₀
  let φ : Γ(X.M.Z, U) ⟶ CommRingCat.of R₀ := CommRingCat.ofHom (X.M.sectionsEquiv U hne).toRingHom
  let f : Sp R₀ ⟶ X.M.Z := Spec.map φ ≫ hU.fromSpec
  let g : Sp (ratHull R₀) ⟶ C.Z := spMap (toRat R₀) ≫ f ≫ X.π
  have hgV : ∀ y, g y ∈ V := by
    intro y
    have hy : hU.fromSpec (Spec.map φ (spMap (toRat R₀) y)) ∈ Set.range hU.fromSpec := ⟨_, rfl⟩
    rw [hU.range_fromSpec] at hy
    exact hUV hy
  let ψ : C.o →+* ratHull R₀ := (Spec.preimage (g ≫ C.z)).hom
  have hψ : ∀ a : nonZeroDivisors C.o, IsUnit (ψ a) := by
    rintro ⟨a, ha⟩
    obtain ⟨n, hn, hdvd⟩ := exists_int_dvd C (nonZeroDivisors.ne_zero ha)
    exact isUnit_of_dvd_unit (map_dvd ψ hdvd) (by simpa using isUnit_intCast_ratHull R₀ hn)
  let θ : cf.F →+* ratHull R₀ := IsLocalization.lift (M := nonZeroDivisors C.o) hψ
  have hθ : θ.comp (algebraMap C.o cf.F) = ψ := IsLocalization.lift_comp hψ
  have hw' : g ≫ C.z = spMap θ ≫ spMap C.b := by
    rw [spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    change _ = Spec.map (CommRingCat.ofHom (θ.comp (algebraMap C.o cf.F)))
    rw [hθ]
    exact (Spec.map_preimage _).symm
  let g' : Sp (ratHull R₀) ⟶ pullback C.z (spMap C.b) := pullback.lift g (spMap θ) hw'
  have hrange : Set.range g' ⊆ Set.range C.iF := by
    rintro _ ⟨y, rfl⟩
    rw [← hV]
    show pullback.fst C.z (spMap C.b) (g' y) ∈ V
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst]
    exact hgV y
  refine ⟨U, IsOpenImmersion.lift C.iF g' hrange, hU, hwU, ?_⟩
  have hpt : ⊤ ≤ X.M.pt ⁻¹ᵁ U := X.M.top_le_preimage_pt hne
  have hφ : φ ≫ CommRingCat.ofHom R₀.val.toRingHom = valMap X.M.pt U hpt := by
    ext a
    show ((X.M.sectionsEquiv U hne a : X.M.ringOn U) : X.Ω₁) = _
    rw [RatModel.coe_sectionsEquiv, ← valR_eq, valF_eq_valR]
  have hf : spMap R₀.val.toRingHom ≫ f = X.M.pt := by
    simp only [f, ← Category.assoc]
    rw [spMap, ← Spec.map_comp, hφ, specMap_valMap_fromSpec]
  have hfst : spMap (ratHull R₀).val.toRingHom ≫ g = X.uΩ ≫ C.i := by
    show spMap (ratHull R₀).val.toRingHom ≫ spMap (toRat R₀) ≫ f ≫ X.π = _
    rw [← Category.assoc, spMap_val_toRat, ← Category.assoc, hf, X.comp]
    simp only [USetup.uΩ, Category.assoc]
  rw [← cancel_mono C.iF, Category.assoc, IsOpenImmersion.lift_fac]
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, hfst]
    simp only [UCompact.i, Category.assoc]
  · have key : spMap (ratHull R₀).val.toRingHom ≫ g' ≫ pullback.snd C.z (spMap C.b) ≫ spMap C.b =
        X.uΩ ≫ C.iF ≫ pullback.snd C.z (spMap C.b) ≫ spMap C.b := by
      rw [← pullback.condition, ← Category.assoc g', pullback.lift_fst, reassoc_of% hfst]
      simp only [UCompact.i, Category.assoc]
    exact spec_ext_of_isFractionRing (A := C.o) _ _ (by simpa only [Category.assoc] using key)

end GlobalTheory.UPoinc.ChartAt
end
