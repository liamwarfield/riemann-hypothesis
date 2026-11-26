module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import ReciprocityTheory.DualLattices.VEqZeroOfPowEqOne

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.TwhopfInd
open GlobalTheory.CompanionTheory.Ar.BT TensorProduct

namespace PositivityTheory.HtPt.Twhopf

theorem translate_mem : ∀ (R : Type) [CommRing R] (T : Type) [CommGroup T] (A : Subalgebra R (T → R)), IsHopfOrder A → ∀ f ∈ A, ∀ t, (fun h => f (t * h)) ∈ A := by
  intro R _ T _ A hA f hf t
  have key : ∀ g ∈ prodSpan A, (fun h => g (t, h)) ∈ A := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hg
      have e : (fun h => a (t, h).1 * b (t, h).2) = a t • b := by
        funext h
        simp [smul_eq_mul]
      rw [e]
      exact A.smul_mem hb _
    | zero => exact A.zero_mem
    | add x y _ _ hx hy => exact A.add_mem hx hy
    | smul r x _ hx => exact A.smul_mem hx r
  exact key _ (hA.comul f hf)

theorem exists_coset_coord {T H : Type} [CommGroup T] [CommGroup H] (ι : H →* T) :
    ∃ κ : T → H, ∀ t, (QuotientGroup.mk t : T ⧸ ι.range).out * ι (κ t) = t := by
  have key : ∀ t : T, ∃ h : H, ι h = ((QuotientGroup.mk t : T ⧸ ι.range).out)⁻¹ * t := fun t =>
    MonoidHom.mem_range.mp (QuotientGroup.eq.mp (QuotientGroup.out_eq' _))
  choose κ hκ using key
  exact ⟨κ, fun t => by rw [hκ, mul_inv_cancel_left]⟩

theorem ind_hopf : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (H : Type) [CommGroup H] (ι : H →* T), Function.Injective ι → ∀ A : Subalgebra R (H → R), IsHopfOrder A → IsHopfOrder (indOrder ι A) := by
  classical
  intro R _ _ T _ _ H _ ι hι A hA
  have : Fintype (T ⧸ ι.range) := Fintype.ofFinite _
  have : Module.Finite R A := hA.finite
  have : Module.Projective R A := hA.projective
  obtain ⟨κ, hκ⟩ := exists_coset_coord ι
  have hmk : ∀ t h, (QuotientGroup.mk (t * ι h) : T ⧸ ι.range) = QuotientGroup.mk t := by
    intro t h
    rw [QuotientGroup.eq]
    exact MonoidHom.mem_range.mpr ⟨h⁻¹, by rw [map_inv, mul_inv_rev, inv_mul_cancel_right]⟩
  have hκmul : ∀ t h, κ (t * ι h) = κ t * h := by
    intro t h
    apply hι
    have e1 := hκ (t * ι h)
    have e2 := hκ t
    rw [hmk] at e1
    rw [map_mul]
    apply mul_left_cancel (a := (QuotientGroup.mk t : T ⧸ ι.range).out)
    rw [e1, ← mul_assoc, e2]
  let ext : T ⧸ ι.range → (H → R) → T → R := fun c a x =>
    if (QuotientGroup.mk x : T ⧸ ι.range) = c then a (κ x) else 0
  have hext_mem : ∀ c a, a ∈ A → ext c a ∈ indOrder ι A := by
    intro c a ha
    rw [OrderApi.mem_indOrder]
    intro t
    have e : (fun h => ext c a (t * ι h)) =
        if (QuotientGroup.mk t : T ⧸ ι.range) = c then (fun h => a (κ t * h)) else 0 := by
      funext h
      simp only [ext, hmk, hκmul]
      split_ifs <;> rfl
    rw [e]
    split_ifs
    · exact translate_mem R H A hA a ha (κ t)
    · exact A.zero_mem
  have hdecomp : ∀ f : T → R, ∑ c, ext c (fun h => f (c.out * ι h)) = f := by
    intro f
    funext x
    rw [Finset.sum_apply, Finset.sum_eq_single (QuotientGroup.mk x)]
    · simp only [ext, ↓reduceIte, hκ]
    · intro c _ hc
      simp only [ext]
      rw [if_neg (fun h => hc h.symm)]
    · intro h
      exact absurd (Finset.mem_univ _) h
  let extL : T ⧸ ι.range → (H → R) →ₗ[R] (T → R) := fun c =>
    { toFun := ext c
      map_add' := fun a b => by
        funext x
        simp only [ext, Pi.add_apply]
        split_ifs <;> simp
      map_smul' := fun r a => by
        funext x
        simp only [ext, Pi.smul_apply, RingHom.id_apply]
        split_ifs <;> simp }
  let Φ : indOrder ι A →ₗ[R] (T ⧸ ι.range → A) :=
    { toFun := fun f c => ⟨fun h => (f : T → R) (c.out * ι h),
        (OrderApi.mem_indOrder ι A f).mp f.2 c.out⟩
      map_add' := fun f g => by
        funext c
        exact Subtype.ext rfl
      map_smul' := fun r f => by
        funext c
        exact Subtype.ext rfl }
  let Ψ : (T ⧸ ι.range → A) →ₗ[R] indOrder ι A :=
    { toFun := fun a => ⟨∑ c, extL c (a c),
        Subalgebra.sum_mem _ (fun c _ => hext_mem c (a c) (a c).2)⟩
      map_add' := fun a b => by
        apply Subtype.ext
        simp only [Pi.add_apply, Subalgebra.coe_add, map_add (f := _), Finset.sum_add_distrib]
      map_smul' := fun r a => by
        apply Subtype.ext
        simp only [Pi.smul_apply, Subalgebra.coe_smul, map_smul, Finset.smul_sum,
          RingHom.id_apply] }
  have hΨΦ : Ψ.comp Φ = LinearMap.id := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    exact hdecomp (f : T → R)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Module.Finite.of_surjective Ψ (fun f => ⟨Φ f, by
      rw [← LinearMap.comp_apply, hΨΦ, LinearMap.id_apply]⟩)
  · have : Module.Projective R (T ⧸ ι.range → A) :=
      Module.Projective.of_equiv
        (DFinsupp.linearEquivFunOnFintype (R := R) (M := fun _ : T ⧸ ι.range => A))
    exact Module.Projective.of_split Φ Ψ hΨΦ
  · obtain ⟨d, hd, hdf⟩ := hA.full
    refine ⟨d, hd, fun f => ?_⟩
    rw [OrderApi.mem_indOrder]
    intro t
    exact hdf _
  · intro f hf
    have hg : ∀ c c' : T ⧸ ι.range,
        (fun z : H × H => f (c.out * c'.out * ι (z.1 * z.2))) ∈ prodSpan A := fun c c' =>
      hA.comul _ ((OrderApi.mem_indOrder ι A f).mp hf (c.out * c'.out))
    have hlift : ∀ (c c' : T ⧸ ι.range) (G : H × H → R), G ∈ prodSpan A →
        (fun z : T × T => if (QuotientGroup.mk z.1 : T ⧸ ι.range) = c ∧
          (QuotientGroup.mk z.2 : T ⧸ ι.range) = c' then G (κ z.1, κ z.2) else 0) ∈
          prodSpan (indOrder ι A) := by
      intro c c' G hG
      induction hG using Submodule.span_induction with
      | mem g hg =>
        obtain ⟨a, ha, b, hb, rfl⟩ := hg
        have e : (fun z : T × T => if (QuotientGroup.mk z.1 : T ⧸ ι.range) = c ∧
            (QuotientGroup.mk z.2 : T ⧸ ι.range) = c' then a (κ z.1, κ z.2).1 * b (κ z.1, κ z.2).2
            else 0) = fun z => ext c a z.1 * ext c' b z.2 := by
          funext z
          by_cases h1 : (QuotientGroup.mk z.1 : T ⧸ ι.range) = c <;>
            by_cases h2 : (QuotientGroup.mk z.2 : T ⧸ ι.range) = c' <;> simp [ext, h1, h2]
        rw [e]
        exact OrderApi.mul_mem_prodSpan (hext_mem c a ha) (hext_mem c' b hb)
      | zero =>
        convert (prodSpan (indOrder ι A)).zero_mem using 1
        funext z
        simp
      | add x y _ _ hx hy =>
        convert (prodSpan (indOrder ι A)).add_mem hx hy using 1
        funext z
        by_cases h1 : (QuotientGroup.mk z.1 : T ⧸ ι.range) = c <;>
          by_cases h2 : (QuotientGroup.mk z.2 : T ⧸ ι.range) = c' <;>
          simp [h1, h2]
      | smul r x _ hx =>
        convert (prodSpan (indOrder ι A)).smul_mem r hx using 1
        funext z
        by_cases h1 : (QuotientGroup.mk z.1 : T ⧸ ι.range) = c <;>
          by_cases h2 : (QuotientGroup.mk z.2 : T ⧸ ι.range) = c' <;>
          simp [h1, h2]
    have hsum : (fun z : T × T => f (z.1 * z.2)) = ∑ c : T ⧸ ι.range, ∑ c' : T ⧸ ι.range,
        (fun z : T × T => if (QuotientGroup.mk z.1 : T ⧸ ι.range) = c ∧
          (QuotientGroup.mk z.2 : T ⧸ ι.range) = c' then
          (fun w : H × H => f (c.out * c'.out * ι (w.1 * w.2))) (κ z.1, κ z.2) else 0) := by
      funext z
      rw [Finset.sum_apply, Finset.sum_eq_single (QuotientGroup.mk z.1)]
      · rw [Finset.sum_apply, Finset.sum_eq_single (QuotientGroup.mk z.2)]
        · simp only [and_self, ↓reduceIte]
          calc f (z.1 * z.2) = f ((QuotientGroup.mk z.1 : T ⧸ ι.range).out * ι (κ z.1) *
                ((QuotientGroup.mk z.2 : T ⧸ ι.range).out * ι (κ z.2))) := by rw [hκ, hκ]
            _ = _ := by rw [map_mul, mul_mul_mul_comm]
        · intro c' _ hc'
          rw [if_neg (fun h => hc' h.2.symm)]
        · intro h
          exact absurd (Finset.mem_univ _) h
      · intro c _ hc
        rw [Finset.sum_apply]
        apply Finset.sum_eq_zero
        intro c' _
        rw [if_neg (fun h => hc h.1.symm)]
      · intro h
        exact absurd (Finset.mem_univ _) h
    rw [hsum]
    exact Submodule.sum_mem _ (fun c _ => Submodule.sum_mem _ (fun c' _ => hlift c c' _ (hg c c')))
  · intro f hf
    rw [OrderApi.mem_indOrder] at hf ⊢
    intro t
    have e : (fun h => f ((t * ι h)⁻¹)) = fun x => (fun h => f (t⁻¹ * ι h)) x⁻¹ := by
      funext h
      rw [mul_inv]
      simp only [map_inv]
    rw [e]
    exact hA.inv _ (hf t⁻¹)

theorem res_ind {R T : Type} [CommRing R] [CommGroup T] (H : Subgroup T) (A : Subalgebra R (H → R))
    (hA : IsHopfOrder A) : resOrder H.subtype (indOrder H.subtype A) = A := by
  classical
  apply le_antisymm
  · intro x hx
    obtain ⟨f, hf, rfl⟩ := Subalgebra.mem_map.mp hx
    have h1 := (OrderApi.mem_indOrder _ A f).mp hf 1
    convert h1 using 1
    funext h
    simp [GlobalTheory.CompanionTheory.Ar.BT.pullFun]
  · intro a ha
    let f : T → R := fun x => if hx : x ∈ H then a ⟨x, hx⟩ else 0
    have hf : f ∈ indOrder H.subtype A := by
      rw [OrderApi.mem_indOrder]
      intro t
      by_cases ht : t ∈ H
      · have e : (fun h : H => f (t * H.subtype h)) = fun h => a (⟨t, ht⟩ * h) := by
          funext h
          simp only [f, Subgroup.coe_subtype]
          rw [dite_eq_left (H.mul_mem ht h.2)]
          rfl
        rw [e]
        exact translate_mem R H A hA a ha ⟨t, ht⟩
      · have e : (fun h : H => f (t * H.subtype h)) = 0 := by
          funext h
          simp only [f, Subgroup.coe_subtype, Pi.zero_apply]
          rw [dite_eq_right]
          intro hm
          exact ht (by simpa using H.mul_mem hm (H.inv_mem h.2))
        rw [e]
        exact A.zero_mem
    exact Subalgebra.mem_map.mpr ⟨f, hf, by
      funext h
      simp [GlobalTheory.CompanionTheory.Ar.BT.pullFun, f]⟩

end PositivityTheory.HtPt.Twhopf
end

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.ValAtRestrict
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.HtPt.Unc

noncomputable def valHom {B : Type} [CommRing B] {X : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) : Γ(X, U) →+* B :=
  (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom.comp (x.appLE U ⊤ h).hom

theorem valHom_apply {B : Type} [CommRing B] {X : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (s : Γ(X, U)) : valHom x U h s = valAt x U h s := rfl

theorem valAt_restrict {B : Type} [CommRing B] {X : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X) {U V : X.Opens}
    (i : V ⟶ U) (hV : ⊤ ≤ x ⁻¹ᵁ V) (hU : ⊤ ≤ x ⁻¹ᵁ U) (s : Γ(X, U)) :
    valAt x V hV ((X.presheaf.map i.op).hom s) = valAt x U hU s :=
  congrArg (fun φ => (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom (φ.hom s)) (x.map_appLE hV i.op)

theorem top_le_of_le {Y X : Scheme.{0}} (x : Y ⟶ X) {U V : X.Opens} (i : V ≤ U) (hV : ⊤ ≤ x ⁻¹ᵁ V) :
    ⊤ ≤ x ⁻¹ᵁ U := fun _ hz => i (hV hz)

theorem top_le_of_mem {K : Type} [Field K] {X : Scheme.{0}} (x : Spec (CommRingCat.of K) ⟶ X) {U : X.Opens}
    (z : Spec (CommRingCat.of K)) (hz : x z ∈ U) : ⊤ ≤ x ⁻¹ᵁ U := fun w _ => by
  have e : w = z := Subsingleton.elim (α := PrimeSpectrum K) w z
  subst e
  exact hz

theorem sec_inj : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens) (s : Γ(Γ.G.left, U)), (∀ (t : T) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U), valAt (Γ.pt t).left U h s = 0) → s = 0 := by
  intro R _ _ T _ _ Γ U s hs
  have := Γ.flat
  have := Γ.gen_reduced
  have hdom : IsDominant (genPt R).hom :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
      change RingHom.ker (algebraMap R (FractionRing R)) ≤ _
      rw [(RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))]
      exact bot_le)⟩
  have : IsSchemeTheoreticallyDominant (genPt R).hom := .of_isDominant _
  have : QuasiCompact (genPt R).hom :=
    inferInstanceAs (QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))
  let j := pullback.fst Γ.G.hom (genPt R).hom
  apply j.app_injective U
  rw [map_zero]
  apply eq_zero_of_basicOpen_eq_bot
  rw [← Scheme.preimage_basicOpen, eq_bot_iff]
  intro z hz
  exfalso
  have hz' : j z ∈ Γ.G.left.basicOpen s := hz
  have hgen : (Γ.G.hom (j z)).asIdeal = ⊥ := by
    have e : Γ.G.hom (j z) = (genPt R).hom (pullback.snd Γ.G.hom (genPt R).hom z) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
    rw [e]
    generalize pullback.snd Γ.G.hom (genPt R).hom z = w
    have hw : PrimeSpectrum.asIdeal (R := FractionRing R) w = ⊥ :=
      (Ideal.eq_bot_or_top _).resolve_right (PrimeSpectrum.isPrime (R := FractionRing R) w).ne_top
    change Ideal.comap (algebraMap R (FractionRing R)) (PrimeSpectrum.asIdeal (R := FractionRing R) w) = ⊥
    rw [hw]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R (FractionRing R))
  obtain ⟨t, x, hx⟩ := Γ.pt_onto _ hgen
  rw [← hx] at hz'
  have h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U := top_le_of_mem _ x (Γ.G.left.basicOpen_le s hz')
  have h0 : (Γ.pt t).left.appLE U ⊤ h s = 0 := by
    apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom).1
    rw [map_zero]
    exact hs t h
  have h1 := Scheme.basicOpen_appLE (Γ.pt t).left ⊤ U h s
  rw [h0, Scheme.basicOpen_zero] at h1
  have h2 : x ∈ (⊤ : (genPt R).left.Opens) ⊓ (Γ.pt t).left ⁻¹ᵁ Γ.G.left.basicOpen s := ⟨trivial, hz'⟩
  rw [← h1] at h2
  exact h2

theorem reg_iff : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens) (f : T → FractionRing R), (∀ g ∈ U, Γ.RegularAt f g) ↔ ∃ s : Γ(Γ.G.left, U), ∀ (t : T) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U), valAt (Γ.pt t).left U h s = f t := by
  intro R _ _ T _ _ Γ U f
  refine ⟨fun h => ?_, fun ⟨s, hs⟩ g hg => ⟨U, hg, s, hs⟩⟩
  choose W hW s hs using fun g : U => h g.1 g.2
  let V : U → Γ.G.left.Opens := fun g => W g ⊓ U
  let sf : ∀ g : U, Γ(Γ.G.left, V g) := fun g =>
    (Γ.G.left.presheaf.map (homOfLE (inf_le_left : V g ≤ W g)).op).hom (s g)
  have hsf : ∀ (g : U) (t : T) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ V g), valAt (Γ.pt t).left (V g) h (sf g) = f t :=
    fun g t h => (valAt_restrict _ _ h (top_le_of_le _ inf_le_left h) _).trans (hs g t _)
  have hcomp : TopCat.Presheaf.IsCompatible Γ.G.left.sheaf.1 V sf := by
    intro a b
    have := sec_inj R T Γ (V a ⊓ V b)
      ((Γ.G.left.presheaf.map (homOfLE (inf_le_left : V a ⊓ V b ≤ V a)).op).hom (sf a) -
        (Γ.G.left.presheaf.map (homOfLE (inf_le_right : V a ⊓ V b ≤ V b)).op).hom (sf b)) (fun t h => by
          rw [← valHom_apply, map_sub, valHom_apply, valHom_apply,
            valAt_restrict _ _ h (top_le_of_le _ inf_le_left h),
            valAt_restrict _ _ h (top_le_of_le _ inf_le_right h), hsf, hsf, sub_self])
    exact sub_eq_zero.1 this
  obtain ⟨σ, hσ, -⟩ := Γ.G.left.sheaf.existsUnique_gluing' V U (fun g => homOfLE inf_le_right)
    (fun g hg => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨g, hg⟩, hW ⟨g, hg⟩, hg⟩) sf hcomp
  refine ⟨σ, fun t ht => ?_⟩
  let x : Spec (CommRingCat.of (FractionRing R)) := default
  let g : U := ⟨(Γ.pt t).left x, ht (Set.mem_univ x)⟩
  have hg : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ V g := top_le_of_mem (Γ.pt t).left x ⟨hW g, g.2⟩
  exact (valAt_restrict _ (homOfLE (inf_le_right : V g ≤ U)) hg ht σ).symm.trans
    ((congrArg (valAt (Γ.pt t).left (V g) hg) (hσ g)).trans (hsf g t hg))

theorem finite_le : ∀ (R : Type) [CommRing R] [IsLocalRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (U U' : X.Opens), IsFinite (U.ι ≫ f) → (∀ x : X, f x = IsLocalRing.closedPoint R → x ∈ U') → U ≤ U' := by
  intro R _ _ X f U U' hU hU' x hx
  let x' : U.toScheme := ⟨x, hx⟩
  have hc : IsClosed ((U.ι ≫ f) '' closure {x'}) := (U.ι ≫ f).isClosedMap _ isClosed_closure
  have hs : (U.ι ≫ f) x' ⤳ IsLocalRing.closedPoint R := IsLocalRing.specializes_closedPoint (R := R) _
  obtain ⟨y, hy, e⟩ := hs.mem_closed hc ⟨x', subset_closure rfl, rfl⟩
  have h1 : U.ι x' ⤳ U.ι y := (specializes_iff_mem_closure.2 hy).map U.ι.continuous
  exact h1.mem_open U'.isOpen (hU' _ (by rw [← Scheme.Hom.comp_apply]; exact e))

end PositivityTheory.HtPt.Unc
end

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.BtOrderOfPoints
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.HtPt.Mk

theorem bt_pgsh : ∀ (R C : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field C] [Algebra R C], Function.Injective (algebraMap R C) → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] (A : Subalgebra R (Multiplicative N → R)), IsHopfOrder A → ∃ AA : ReciprocityTheory.PGsh.L2.HopfOrder R (C := C) N, ∀ f : N → C, f ∈ AA.carrier ↔ ∃ g ∈ A, ∀ x, f x = algebraMap R C (g (Multiplicative.ofAdd x)) := by
  intro R C _ _ _ _ _ hinj N _ _ _ A hA
  classical
  let φ : (Multiplicative N → R) →ₗ[R] (N → C) :=
    { toFun := fun g x => algebraMap R C (g (Multiplicative.ofAdd x))
      map_add' := by
        intro g h
        funext x
        simp
      map_smul' := by
        intro r g
        funext x
        simp [Algebra.smul_def] }
  have hφ : ∀ g x, φ g x = algebraMap R C (g (Multiplicative.ofAdd x)) := fun _ _ => rfl
  haveI := hA.finite
  haveI := hA.projective
  haveI : Module.Free R A := Module.free_of_flat_of_isLocalRing
  obtain ⟨d, hd0, hd⟩ := hA.full
  have hcardT : Module.finrank R (Multiplicative N → R) = Fintype.card N := by
    rw [Module.finrank_fintype_fun_eq_card]
    exact Fintype.card_congr Multiplicative.toAdd
  have hrank : Module.finrank R A = Fintype.card N := by
    apply le_antisymm
    · rw [← hcardT]
      exact LinearMap.finrank_le_finrank_of_injective (f := A.val.toLinearMap) Subtype.val_injective
    · let sc : (Multiplicative N → R) →ₗ[R] A :=
        { toFun := fun f => ⟨d • f, hd f⟩
          map_add' := fun f g => Subtype.ext (smul_add d f g)
          map_smul' := fun r f => Subtype.ext (smul_comm d r f) }
      have hsc : Function.Injective sc := by
        intro f g hfg
        have h2 : d • f = d • g := congrArg Subtype.val hfg
        exact smul_right_injective _ hd0 h2
      rw [← hcardT]
      exact LinearMap.finrank_le_finrank_of_injective hsc
  let b : Module.Basis N R A := (Module.finBasisOfFinrankEq R A hrank).reindex (Fintype.equivFin N).symm
  refine ⟨{ carrier := (Subalgebra.toSubmodule A).map φ
            lat := ?_
            le_int := ?_
            one_mem := ?_
            mul_mem := ?_
            comul := ?_
            antipode := ?_ }, ?_⟩
  · refine ⟨fun x j => φ (b j) x, ?_, ?_⟩
    · let M : Matrix N N R := fun x j => (b j : Multiplicative N → R) (Multiplicative.ofAdd x)
      have hdet : Matrix.det (fun x j => φ (b j) x : Matrix N N C) = algebraMap R C M.det := by
        rw [RingHom.map_det]
        rfl
      rw [hdet]
      apply isUnit_iff_ne_zero.mpr
      rw [map_ne_zero_iff _ hinj]
      intro h0
      obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
      apply hv0
      have hsum : ∑ j, v j • b j = 0 := by
        apply Subtype.ext
        funext t
        have h3 := congrFun hv (Multiplicative.toAdd t)
        simpa [Matrix.mulVec, dotProduct, M, mul_comm] using h3
      exact funext (Fintype.linearIndependent_iff.mp b.linearIndependent v hsum)
    · apply le_antisymm
      · rintro f ⟨g, hg, rfl⟩
        have hg' : (⟨g, hg⟩ : A) = ∑ j, b.repr ⟨g, hg⟩ j • b j := (b.sum_repr _).symm
        have hgs : g = ∑ j, b.repr ⟨g, hg⟩ j • (b j : Multiplicative N → R) := by
          have h4 : ((⟨g, hg⟩ : A) : Multiplicative N → R)
              = ((∑ j, b.repr ⟨g, hg⟩ j • b j : A) : Multiplicative N → R) := congrArg Subtype.val hg'
          rw [AddSubmonoidClass.coe_finsetSum] at h4
          exact h4
        set_option synthInstance.maxHeartbeats 100000 in
          rw [hgs, map_sum]
        refine Submodule.sum_mem _ fun j _ => ?_
        rw [map_smul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
      · rw [Submodule.span_le]
        rintro _ ⟨j, rfl⟩
        exact ⟨b j, (b j).2, rfl⟩
  · rintro f ⟨g, hg, rfl⟩ x
    exact ⟨g (Multiplicative.ofAdd x), rfl⟩
  · refine ⟨1, A.one_mem, ?_⟩
    funext x
    simp [hφ]
  · rintro f g ⟨f', hf', rfl⟩ ⟨g', hg', rfl⟩
    refine ⟨f' * g', A.mul_mem hf' hg', ?_⟩
    funext x
    simp [hφ]
  · rintro f ⟨g, hg, rfl⟩
    let ψ : (Multiplicative N × Multiplicative N → R) →ₗ[R] (N × N → C) :=
      { toFun := fun F p => algebraMap R C (F (Multiplicative.ofAdd p.1, Multiplicative.ofAdd p.2))
        map_add' := by
          intro F G
          funext p
          simp
        map_smul' := by
          intro r F
          funext p
          simp [Algebra.smul_def] }
    have hle : GlobalTheory.CompanionTheory.Ar.BT.prodSpan A ≤
        (ReciprocityTheory.PGsh.L2.tensorSpan R ((Subalgebra.toSubmodule A).map φ)).comap ψ := by
      rw [GlobalTheory.CompanionTheory.Ar.BT.prodSpan, Submodule.span_le]
      rintro _ ⟨a, ha, a', ha', rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap]
      apply Submodule.subset_span
      refine ⟨φ a, ⟨a, ha, rfl⟩, φ a', ⟨a', ha', rfl⟩, ?_⟩
      funext p
      simp [hφ, ψ]
    have h5 := hle (hA.comul g hg)
    rw [Submodule.mem_comap] at h5
    convert h5 using 1
    funext p
    simp [hφ, ψ, ReciprocityTheory.PGsh.L2.addPull, LinearMap.funLeft_apply]
  · rintro f ⟨g, hg, rfl⟩
    refine ⟨fun t => g t⁻¹, hA.inv g hg, ?_⟩
    funext x
    simp [hφ]
  · intro f
    show f ∈ (Subalgebra.toSubmodule A).map φ ↔ _
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨g, hg, fun x => rfl⟩
    · rintro ⟨g, hg, hfg⟩
      exact ⟨g, hg, funext fun x => (hfg x).symm⟩

end PositivityTheory.HtPt.Mk
end
