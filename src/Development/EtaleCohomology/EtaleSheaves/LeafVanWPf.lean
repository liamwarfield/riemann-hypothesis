module

public import Development.EtaleCohomology.EtaleSheaves.LeafVanStalk

@[expose] public section

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafVanWPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.LeafVanWPf
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut LateralTheory.E.LeafVan0Pf

section Cone
variable {C : Type*} [Category C] [Preadditive C] {K L M : CochainComplex C ℤ} (φ : K ⟶ L) [HomologicalComplex.HasHomotopyCofiber φ]

theorem desc_δ {n m : ℤ} (α : Cochain K M m) (β : Cochain L M n) (h : m + 1 = n) (n' : ℤ) (hn' : n + 1 = n') :
    δ n n' (mappingCone.descCochain φ α β h) =
      mappingCone.descCochain φ (δ m n α + n'.negOnePow • (Cochain.ofHom φ).comp β (zero_add n)) (δ n n' β) hn' := by
  rw [mappingCone.δ_descCochain φ α β h n' hn']; rfl

theorem desc_eq_zero {n m : ℤ} {α : Cochain K M m} {β : Cochain L M n} {h : m + 1 = n}
    (H : mappingCone.descCochain φ α β h = 0) : α = 0 ∧ β = 0 := by
  constructor
  · have := mappingCone.inl_descCochain φ α β h
    rw [H, Cochain.comp_zero] at this; exact this.symm
  · have := mappingCone.inr_descCochain φ α β h
    rw [H, Cochain.comp_zero] at this; exact this.symm

theorem units_mul_self' (u : ℤˣ) : u * u = 1 := Int.units_mul_self u

theorem cone_zero
    (hinj : ∀ (n : ℤ) (x : Cocycle L M n),
      CohomologyClass.mk (zcomp (Cocycle.ofHom φ) x (zero_add n)) = 0 → CohomologyClass.mk x = 0)
    (hsurj : ∀ (n : ℤ) (y : Cocycle K M n), ∃ x : Cocycle L M n,
      CohomologyClass.mk (zcomp (Cocycle.ofHom φ) x (zero_add n)) = CohomologyClass.mk y)
    (n : ℤ) (z : Cocycle (mappingCone φ) M n) : CohomologyClass.mk z = 0 := by
  set a : Cochain K M (n - 1) := (mappingCone.inl φ).comp z.1 (by omega) with ha
  set b : Cochain L M n := (Cochain.ofHom (mappingCone.inr φ)).comp z.1 (zero_add n) with hb
  have hz : z.1 = mappingCone.descCochain φ a b (by omega) := by
    rw [mappingCone.ext_cochain_from_iff φ (n - 1) n (by omega)]
    simp [ha, hb]
  have h0 := Cocycle.δ_eq_zero z (n + 1)
  rw [hz, desc_δ φ a b _ (n + 1) rfl] at h0
  obtain ⟨h1, h2⟩ := desc_eq_zero φ h0
  have hda : δ (n - 1) n a = -((n + 1).negOnePow • (Cochain.ofHom φ).comp b (zero_add n)) := eq_neg_of_add_eq_zero_left h1
  let bc : Cocycle L M n := Cocycle.mk b (n + 1) rfl h2
  have hb0 : CohomologyClass.mk bc = 0 := by
    apply hinj
    rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
    refine ⟨-((n + 1).negOnePow • a), ?_⟩
    rw [δ_neg, δ_units_smul, hda, smul_neg, neg_neg, smul_smul, units_mul_self', one_smul]
    simp [zcomp, bc]
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)] at hb0
  obtain ⟨γ, hγ⟩ := hb0
  change δ (n - 1) n γ = b at hγ
  set a' : Cochain K M (n - 1) := a - n.negOnePow • (Cochain.ofHom φ).comp γ (zero_add _) with ha'
  let w : Cochain (mappingCone φ) M (n - 1) := mappingCone.descCochain φ (0 : Cochain K M (n - 1 - 1)) γ (by omega)
  have hw : δ (n - 1) n w = mappingCone.descCochain φ (n.negOnePow • (Cochain.ofHom φ).comp γ (zero_add _)) b (by omega) := by
    simp only [w]; rw [desc_δ φ _ γ _ n (by omega), hγ, δ_zero, zero_add]
  have hda' : δ (n - 1) n a' = 0 := by
    have e : mappingCone.descCochain φ a' (0 : Cochain L M n) (by omega) = z.1 - δ (n - 1) n w := by
      rw [hz, hw, mappingCone.ext_cochain_from_iff φ (n - 1) n (by omega)]
      simp [ha']
    have e2 := congrArg (δ n (n + 1)) e
    rw [δ_sub, δ_δ, sub_zero, Cocycle.δ_eq_zero, desc_δ φ _ _ _ (n + 1) rfl] at e2
    have := (desc_eq_zero φ e2).1
    simpa using this
  obtain ⟨x, hx⟩ := hsurj (n - 1) (Cocycle.mk a' n (by omega) hda')
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
    mem_coboundaries_iff _ (n - 1 - 1) (by omega)] at hx
  obtain ⟨γ', hγ'⟩ := hx
  change δ (n - 1 - 1) (n - 1) γ' = (Cochain.ofHom φ).comp x.1 (zero_add _) - a' at hγ'
  have hdx := Cocycle.δ_eq_zero x n
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨w + n.negOnePow • mappingCone.descCochain φ (0 : Cochain K M (n - 1 - 1)) x.1 (by omega) -
    mappingCone.descCochain φ γ' (0 : Cochain L M (n - 1)) (by omega), ?_⟩
  rw [δ_sub, δ_add, δ_units_smul, hw, desc_δ φ _ _ _ n (by omega), desc_δ φ _ _ _ n (by omega), hγ', hdx]
  change _ = z.1
  rw [hz, mappingCone.ext_cochain_from_iff φ (n - 1) n (by omega)]
  constructor
  · simp only [mappingCone.inl_descCochain, Cochain.comp_add, Cochain.comp_sub, Cochain.comp_units_smul, δ_zero, zero_add,
      Cochain.comp_zero, smul_zero, add_zero, smul_smul, units_mul_self', one_smul, ha']
    abel
  · simp
end Cone

section Geo
variable {R : Type} [CommRing R] (F : Shv R)

theorem hrel_sub {U E : Spc} (f : U ⟶ E) (h : Eqv R f F) (n : ℤ) : Subsingleton (Hrel R f F n) := by
  have hinj : ∀ (n : ℤ) (x : Cocycle ((chains R).obj E) (res R F) n),
      CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains R).map f)) x (zero_add n)) = 0 → CohomologyClass.mk x = 0 := by
    intro n x hx
    apply (h n).1
    change CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains R).map f)) x (zero_add n)) = pull R f F n 0
    rw [map_zero]; exact hx
  have hsurj : ∀ (n : ℤ) (y : Cocycle ((chains R).obj U) (res R F) n), ∃ x : Cocycle ((chains R).obj E) (res R F) n,
      CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains R).map f)) x (zero_add n)) = CohomologyClass.mk y := by
    intro n y
    obtain ⟨c, hc⟩ := (h n).2 (CohomologyClass.mk y)
    obtain ⟨x, rfl⟩ := c.mk_surjective
    exact ⟨x, hc⟩
  refine ⟨fun y y' => ?_⟩
  obtain ⟨z, rfl⟩ := y.mk_surjective
  obtain ⟨z', rfl⟩ := y'.mk_surjective
  change CohomologyClass.mk z = CohomologyClass.mk z'
  rw [cone_zero _ hinj hsurj n z, cone_zero _ hinj hsurj n z']

theorem eqv_of_iso {X Y : Scheme.{0}} (f : X ⟶ Y) [IsIso f] : Eqv R (sch.map f) F := by
  intro n
  refine Function.bijective_iff_has_inverse.2 ⟨pull R (sch.map (inv f)) F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, ← Functor.map_comp, IsIso.inv_hom_id, CategoryTheory.Functor.map_id, pull_id]
  · rw [← pull_comp, ← Functor.map_comp, IsIso.hom_inv_id, CategoryTheory.Functor.map_id, pull_id]

theorem eqv_of_square {P Q X Y : Scheme.{0}} (a : P ⟶ X) (f : X ⟶ Y) (h : P ⟶ Q) (c : Q ⟶ Y) (w : a ≫ f = h ≫ c)
    (ha : Eqv R (sch.map a) F) (hh : Eqv R (sch.map h) F) (hc : Eqv R (sch.map c) F) : Eqv R (sch.map f) F := by
  intro n
  have key : ∀ y, pull R (sch.map a) F n (pull R (sch.map f) F n y) = pull R (sch.map h) F n (pull R (sch.map c) F n y) := by
    intro y; rw [← pull_comp, ← pull_comp, ← Functor.map_comp, ← Functor.map_comp, w]
  constructor
  · intro y y' e
    apply (hc n).1; apply (hh n).1
    rw [← key, ← key, e]
  · intro x
    obtain ⟨u, hu⟩ := (hh n).2 (pull R (sch.map a) F n x)
    obtain ⟨v, rfl⟩ := (hc n).2 u
    refine ⟨v, (ha n).1 ?_⟩
    rw [key, hu]
end Geo

theorem commGroup_inv_eq_conj_twist_identity {B W S X T : Scheme.{0}} (pA : X ⟶ S) (s : S ⟶ B) (ι : W ⟶ B) [Mono ι] (r : T ⟶ S) (w : T ⟶ W)
    (hw : w ≫ ι = r ≫ s) (hc : (pullback.fst (pullback.fst (pA ≫ s) ι ≫ pA) r ≫ pullback.fst (pA ≫ s) ι) ≫ pA =
      pullback.snd (pullback.fst (pA ≫ s) ι ≫ pA) r ≫ r) :
    IsIso (pullback.lift (pullback.fst (pullback.fst (pA ≫ s) ι ≫ pA) r ≫ pullback.fst (pA ≫ s) ι)
      (pullback.snd (pullback.fst (pA ≫ s) ι ≫ pA) r) hc) := by
  have c1 : pullback.fst pA r ≫ pA ≫ s = (pullback.snd pA r ≫ w) ≫ ι := by
    simp only [Category.assoc, hw]; exact pullback.condition_assoc s
  have c2 : pullback.lift (pullback.fst pA r) (pullback.snd pA r ≫ w) c1 ≫ pullback.fst (pA ≫ s) ι ≫ pA =
      pullback.snd pA r ≫ r := by
    rw [← Category.assoc, pullback.lift_fst, pullback.condition]
  refine ⟨⟨pullback.lift (pullback.lift (pullback.fst pA r) (pullback.snd pA r ≫ w) c1) (pullback.snd pA r) c2, ?_, ?_⟩⟩
  · apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [Category.assoc, Category.id_comp, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
          pullback.lift_snd_assoc]
      · rw [← cancel_mono ι]
        simp only [Category.assoc, Category.id_comp, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
          pullback.lift_snd_assoc, hw]
        have e3 : pullback.fst (pA ≫ s) ι ≫ pA ≫ s = pullback.snd (pA ≫ s) ι ≫ ι := pullback.condition
        have e4 := pullback.condition_assoc (f := pullback.fst (pA ≫ s) ι ≫ pA) (g := r) s
        simp only [Category.assoc] at e4
        rw [← e3]
        first | exact e4 | exact e4.symm
    · simp only [Category.assoc, Category.id_comp, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
          pullback.lift_snd_assoc]
  · apply pullback.hom_ext
    · simp only [Category.assoc, Category.id_comp, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
          pullback.lift_snd_assoc]
    · simp only [Category.assoc, Category.id_comp, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
          pullback.lift_snd_assoc]

theorem closed_eq {A : Type} [CommRing A] [IsLocalRing A] (x : Sp A) (hx : ∀ z : Sp A, z ⤳ x) :
    x = IsLocalRing.closedPoint A :=
  ((IsLocalRing.specializes_closedPoint x).antisymm (hx _)).eq

theorem LeafVanW_of : LeafVanW := by
  intro hH q _ k _ hq i B W Y b ι _ p hp A _ s hA hx m
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hE2, -⟩ := hH
  obtain ⟨hHen, hsep⟩ := hA
  haveI : IsProper p := hp
  have hqA : IsUnit (q : A) := by
    have := hq.map (Spec.preimage (s ≫ b)).hom
    simpa using this

  obtain ⟨x, hx1, w0, hw0⟩ := hx
  have hxc := closed_eq x hx1
  have hrpt : (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) (IsLocalRing.closedPoint (IsLocalRing.ResidueField A)) =
      IsLocalRing.closedPoint A := IsLocalRing.comap_closedPoint (IsLocalRing.residue A)
  haveI : Surjective (pullback.fst (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ s) ι) := by
    constructor
    intro t
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ s) (g := ι)
      (IsLocalRing.closedPoint (IsLocalRing.ResidueField A)) w0 (by
        have := congrArg s hrpt
        rw [← hxc, ← hw0] at this
        exact this)
    exact ⟨z, hz.trans (Subsingleton.elim _ _)⟩
  haveI := isIso_of_isClosedImmersion_of_surjective (pullback.fst (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ s) ι)
  have hw : (inv (pullback.fst (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ s) ι) ≫ pullback.snd _ _) ≫ ι =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ s := by
    rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]

  have e1 := hE2 q A ⟨hHen, hsep⟩ hqA (pullback.snd p s) i
  have e2 := hE2 q A ⟨hHen, hsep⟩ hqA (pullback.fst (pullback.snd p s ≫ s) ι ≫ pullback.snd p s) i
  have hc : (pullback.fst (pullback.fst (pullback.snd p s ≫ s) ι ≫ pullback.snd p s) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) ≫
      pullback.fst (pullback.snd p s ≫ s) ι) ≫ pullback.snd p s =
      pullback.snd (pullback.fst (pullback.snd p s ≫ s) ι ≫ pullback.snd p s) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) ≫
        Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) := by
    rw [Category.assoc, pullback.condition]
  haveI := commGroup_inv_eq_conj_twist_identity (pullback.snd p s) s ι _ _ hw hc
  have heqv : Eqv (ZMod q) (sch.map (prS p ι s)) (tw q i) :=
    eqv_of_square _ _ _ _ _ (pullback.lift_fst _ _ _).symm e2 (eqv_of_iso _ (pullback.lift (pullback.fst (pullback.fst (pullback.snd p s ≫ s) ι ≫ pullback.snd p s)
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) ≫ pullback.fst (pullback.snd p s ≫ s) ι) _ hc)) e1
  exact hrel_sub _ _ heqv m

end LateralTheory.E.LeafVanWPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.ResSmulGen
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.MulPf LateralTheory.E.TwistTrivial

namespace LateralTheory.E.GenPf

theorem field_log {q : ℕ} {K : Type} [Field K] (ζ ξ : Prim q K) :
    ∃! a : (ZMod q)ˣ, ξ.1 = ζ.1 ^ (a : ZMod q).val := by
  haveI : NeZero (q : K) := ⟨ζ.2.1.ne_zero⟩
  haveI : NeZero q := NeZero.of_neZero_natCast K
  have hp : ∀ η : Prim q K, IsPrimitiveRoot η.1 q := fun η => by
    rw [← Polynomial.isRoot_cyclotomic_iff, ← Polynomial.map_cyclotomic_int, Polynomial.IsRoot.def,
      Polynomial.eval_map]
    exact η.2.2
  obtain ⟨i, hi, hc, he⟩ := (hp ζ).isPrimitiveRoot_iff.1 (hp ξ)
  refine ⟨ZMod.unitOfCoprime i hc, ?_, fun b hb => ?_⟩
  · simp only [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hi, he]
  · apply Units.ext
    have := (hp ζ).pow_inj (ZMod.val_lt (b : ZMod q)) hi (hb.symm.trans he.symm)
    rw [ZMod.coe_unitOfCoprime, ← this, ZMod.natCast_zmod_val]

theorem field_pow {q : ℕ} {K : Type} [Field K] (ζ : Prim q K) (a b : ZMod q) :
    ζ.1 ^ (a * b).val = (ζ.1 ^ a.val) ^ b.val := by
  haveI : NeZero (q : K) := ⟨ζ.2.1.ne_zero⟩
  haveI : NeZero q := NeZero.of_neZero_natCast K
  have hp : IsPrimitiveRoot ζ.1 q := by
    rw [← Polynomial.isRoot_cyclotomic_iff, ← Polynomial.map_cyclotomic_int, Polynomial.IsRoot.def,
      Polynomial.eval_map]
    exact ζ.2.2
  rw [ZMod.val_mul, ← pow_mul, ← pow_eq_pow_mod _ hp.pow_eq_one]

theorem field_ann {q : ℕ} (j : ℤ) {K : Type} [Field K] (ζ : Prim q K) (c : ULift.{1} (ZMod q))
    (h : Finsupp.single ζ c ∈ twRel q j K) : c = 0 := by
  choose lg hlg hu using fun ξ => field_log ζ ξ
  let φ : (Prim q K →₀ ULift.{1} (ZMod q)) →ₗ[ULift.{1} (ZMod q)] ULift.{1} (ZMod q) :=
    Finsupp.linearCombination _ (fun ξ => ULift.up ((lg ξ ^ j : (ZMod q)ˣ) : ZMod q))
  have hk : twRel q j K ≤ LinearMap.ker φ := by
    refine Submodule.span_le.2 ?_
    rintro x ⟨η, ξ, a, hξ, rfl⟩
    have e : lg η * a = lg ξ := hu ξ _ (by
      show ξ.1 = ζ.1 ^ ((lg η * a : (ZMod q)ˣ) : ZMod q).val
      rw [Units.val_mul, field_pow, ← hlg η, hξ])
    show φ _ = 0
    rw [map_sub]
    simp only [φ, Finsupp.linearCombination_single, ← e, one_smul, smul_eq_mul]
    rw [sub_eq_zero, mul_zpow]
    apply ULift.ext
    simp only [ULift.mul_down, Units.val_mul, ULift.one_down]
    ring
  have h1 : lg ζ = 1 := by
    haveI : NeZero (q : K) := ⟨ζ.2.1.ne_zero⟩
    haveI : NeZero q := NeZero.of_neZero_natCast K
    have e : lg ζ * lg ζ = lg ζ := hu ζ _ (by
      show ζ.1 = ζ.1 ^ ((lg ζ * lg ζ : (ZMod q)ˣ) : ZMod q).val
      rw [Units.val_mul, field_pow, ← hlg ζ, ← hlg ζ])
    simpa using e
  have := hk h
  simp only [LinearMap.mem_ker, φ, Finsupp.linearCombination_single, h1, one_zpow, smul_eq_mul] at this
  exact (mul_one c).symm.trans this

theorem ring_ann {q : ℕ} (j : ℤ) {A : Type} [CommRing A] [Nontrivial A] (ζ : Prim q A) (c : ULift.{1} (ZMod q))
    (h : Finsupp.single ζ c ∈ twRel q j A) : c = 0 := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal A
  letI := Ideal.Quotient.field M
  have := twRel_le q j (Ideal.Quotient.mk M) h
  rw [Submodule.mem_comap, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single] at this
  exact field_ann j _ c this

theorem ann {q : ℕ} (j l : ℤ) {X : Scheme.{0}} (ζ : Prim q Γ(X, ⊤)) (c : ULift.{1} (ZMod q))
    (h : c • twGen j ζ = 0) : c • twGen l ζ = 0 := by
  have h0 : ofRings.sec (twF q j) X (Submodule.Quotient.mk (Finsupp.single ζ c) : (twF q j).obj Γ(X, ⊤)) =
      ofRings.sec (twF q j) X 0 := by
    rw [sec_single, h]
    exact (map_zero _).symm
  have hS := Presheaf.equalizerSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q j))
    (X := op X) _ _ h0
  refine sep _ hS _ _ (fun Y f hf => ?_)
  have hf' : (Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map f.appTop.hom) (Finsupp.single ζ c)) :
      (twF q j).obj Γ(Y, ⊤)) = 0 := Eq.trans hf (map_zero _)
  rw [Finsupp.mapDomain_single] at hf'
  by_cases hY : Nonempty Y
  · haveI : Nontrivial Γ(Y, ⊤) := by
      haveI : Nonempty (⊤ : Y.Opens) := hY.elim fun y => ⟨⟨y, trivial⟩⟩
      infer_instance
    have hc := ring_ann j _ c ((Submodule.Quotient.mk_eq_zero _).1 hf')
    rw [hc, zero_smul]
  · haveI : IsEmpty Y := not_nonempty_iff.1 hY
    exact sep ⊥ (by exact Scheme.bot_mem_grothendieckTopology Y) _ _ (fun _ _ hg => hg.elim)

theorem res_comp {q : ℕ} {j : ℤ} {X Y Z : Scheme.{0}} (h : Z ⟶ Y) (f : Y ⟶ X) (x : Sec (tw q j) X) :
    Sec.res (h ≫ f) x = Sec.res h (Sec.res f x) := by
  simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]

theorem res_smul_gen {q : ℕ} {j : ℤ} {X Y : Scheme.{0}} (f : Y ⟶ X) (ζ : Prim q Γ(X, ⊤)) (c : ULift.{1} (ZMod q)) :
    Sec.res f (c • twGen j ζ) = c • twGen j (ζ.map f.appTop.hom) := by
  rw [← genRes]
  exact map_smul _ _ _

theorem ann2 {q : ℕ} (j l : ℤ) {X : Scheme.{0}} (ζ : Prim q Γ(X, ⊤)) (c d : ULift.{1} (ZMod q))
    (h : c • twGen j ζ = d • twGen j ζ) : c • twGen l ζ = d • twGen l ζ := by
  rw [← sub_eq_zero, ← sub_smul] at h ⊢
  exact ann j l ζ _ h

theorem wd (hR : RootPow) {q : ℕ} {j k l : ℤ} (h : j + k = l) {X : Scheme.{0}} (ζ ξ : Prim q Γ(X, ⊤))
    (c d c' d' : ULift.{1} (ZMod q)) (h1 : c • twGen j ζ = c' • twGen j ξ) (h2 : d • twGen k ζ = d' • twGen k ξ) :
    (c * d) • twGen l ζ = (c' * d') • twGen l ξ := by
  obtain ⟨S, hS, hp⟩ := hR q X ζ {ξ}
  refine sep S hS _ _ (fun Y f hf => ?_)
  obtain ⟨a, ha⟩ := hp f hf ξ (Finset.mem_singleton_self _)
  have e1 := congrArg (Sec.res f) h1
  have e2 := congrArg (Sec.res f) h2
  rw [res_smul_gen, res_smul_gen] at e1 e2 ⊢
  rw [twGen_pow _ _ _ a ha, smul_smul] at e1 e2 ⊢
  have f1 := ann2 _ l _ _ _ e1
  have f2 := ann2 _ l _ _ _ e2
  rw [mul_smul, f2, smul_smul, mul_comm c, mul_smul, f1, smul_smul]
  congr 1
  subst h
  rw [zpow_add]
  apply ULift.ext
  simp only [ULift.mul_down, Units.val_mul]
  ring

def Good {q : ℕ} {j k l : ℤ} {X : Scheme.{0}} (y : Sec (tw q k) X) (x : Sec (tw q j) X) (z : Sec (tw q l) X) : Prop :=
  (y = 0 ∧ z = 0) ∨ ∃ (ζ : Prim q Γ(X, ⊤)) (c d : ULift.{1} (ZMod q)),
    x = c • twGen j ζ ∧ y = d • twGen k ζ ∧ z = (c * d) • twGen l ζ

theorem Good.res {q : ℕ} {j k l : ℤ} {X Y : Scheme.{0}} {y : Sec (tw q k) X} {x : Sec (tw q j) X} {z : Sec (tw q l) X}
    (hg : Good y x z) (f : Y ⟶ X) : Good (Sec.res f y) (Sec.res f x) (Sec.res f z) := by
  rcases hg with ⟨rfl, rfl⟩ | ⟨ζ, c, d, rfl, rfl, rfl⟩
  · exact Or.inl ⟨map_zero _, map_zero _⟩
  · exact Or.inr ⟨_, c, d, res_smul_gen _ _ _, res_smul_gen _ _ _, res_smul_gen _ _ _⟩

theorem Good.uniq (hR : RootPow) {q : ℕ} {j k l : ℤ} (h : j + k = l) {X : Scheme.{0}} {y : Sec (tw q k) X}
    {x : Sec (tw q j) X} {z z' : Sec (tw q l) X} (hg : Good y x z) (hg' : Good y x z') : z = z' := by
  rcases hg with ⟨hy, hz⟩ | ⟨ζ, c, d, hx, hy, hz⟩ <;> rcases hg' with ⟨hy', hz'⟩ | ⟨ξ, c', d', hx', hy', hz'⟩
  · rw [hz, hz']
  · rw [hz, hz', mul_smul, ann k l ξ d' (hy'.symm.trans hy), smul_zero]
  · rw [hz, hz', mul_smul, ann k l ζ d (hy.symm.trans hy'), smul_zero]
  · rw [hz, hz']
    exact wd hR h _ _ _ _ _ _ (hx.symm.trans hx') (hy.symm.trans hy')

theorem locGen' (hR : RootPow) {q : ℕ} {j : ℤ} {X : Scheme.{0}} (ζ : Prim q Γ(X, ⊤)) (x : Sec (tw q j) X) :
    ∃ S ∈ Scheme.etaleTopology X, ∀ ⦃Y : Scheme.{0}⦄ (f : Y ⟶ X), S f →
      ∃ c : ULift.{1} (ZMod q), Sec.res f x = c • twGen j (ζ.map f.appTop.hom) := by
  obtain ⟨S, hS, hp⟩ := LocGen_of hR q j X ζ x
  refine ⟨S, hS, fun Y f hf => ?_⟩
  obtain ⟨c, hc⟩ := hp f hf
  exact ⟨c, hc.trans (Int.cast_smul_eq_zsmul _ _ _).symm⟩

def locSieve {q : ℕ} {j k : ℤ} (l : ℤ) {X : Scheme.{0}} (y : Sec (tw q k) X) (x x' : Sec (tw q j) X) : Sieve X where
  arrows Y f := ∃ z z' : Sec (tw q l) Y, Good (Sec.res f y) (Sec.res f x) z ∧ Good (Sec.res f y) (Sec.res f x') z' ∧
    Good (Sec.res f y) (Sec.res f (x + x')) (z + z')
  downward_closed := by
    rintro Y Z f ⟨z, z', h1, h2, h3⟩ g
    refine ⟨Sec.res g z, Sec.res g z', ?_, ?_, ?_⟩
    · rw [res_comp, res_comp]; exact h1.res g
    · rw [res_comp, res_comp]; exact h2.res g
    · rw [res_comp, res_comp]
      have := h3.res g
      rwa [show Sec.res g (z + z') = Sec.res g z + Sec.res g z' from map_add _ _ _] at this

theorem locSieve_mem (hR : RootPow) {q : ℕ} {j k : ℤ} (l : ℤ) {X : Scheme.{0}} (y : Sec (tw q k) X) (x x' : Sec (tw q j) X) :
    locSieve l y x x' ∈ Scheme.etaleTopology X := by
  obtain ⟨S, hS, hv⟩ := locPres y
  refine Scheme.etaleTopology.transitive hS _ (fun Y f hf => ?_)
  obtain ⟨v, hv⟩ := hv f hf
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  by_cases hne : Nonempty (Prim q Γ(Y, ⊤))
  · obtain ⟨ζ⟩ := hne
    obtain ⟨S1, hS1, h1⟩ := locGen' hR ζ (Sec.res f y)
    obtain ⟨S2, hS2, h2⟩ := locGen' hR ζ (Sec.res f x)
    obtain ⟨S3, hS3, h3⟩ := locGen' hR ζ (Sec.res f x')
    refine Scheme.etaleTopology.superset_covering ?_
      (Scheme.etaleTopology.intersection_covering hS1 (Scheme.etaleTopology.intersection_covering hS2 hS3))
    rintro Z g ⟨g1, g2, g3⟩
    obtain ⟨d, hd⟩ := h1 g g1
    obtain ⟨c, hc⟩ := h2 g g2
    obtain ⟨c', hc'⟩ := h3 g g3
    rw [← res_comp] at hd hc hc'
    refine ⟨_, _, Or.inr ⟨_, c, d, hc, hd, rfl⟩, Or.inr ⟨_, c', d, hc', hd, rfl⟩, Or.inr ⟨_, c + c', d, ?_, hd, ?_⟩⟩
    · rw [add_smul, ← hc, ← hc']
      exact map_add _ _ _
    · rw [add_mul, add_smul]
  · have hw : w = 0 := by
      ext ξ
      exact (hne ⟨ξ⟩).elim
    have hy : Sec.res f y = 0 := by
      rw [hv, hw]
      exact map_zero _
    have hm : locSieve l y x x' f := ⟨0, 0, Or.inl ⟨hy, rfl⟩, Or.inl ⟨hy, rfl⟩, Or.inl ⟨hy, add_zero _⟩⟩
    rw [Sieve.pullback_eq_top_of_mem _ hm]
    exact Scheme.etaleTopology.top_mem _

def Rel {q : ℕ} {j k l : ℤ} {X : Scheme.{0}} (y : Sec (tw q k) X) (x : Sec (tw q j) X) (z : Sec (tw q l) X) : Prop :=
  ∀ ⦃Y : Scheme.{0}⦄ (f : Y ⟶ X) (t : Sec (tw q l) Y), Good (Sec.res f y) (Sec.res f x) t → Sec.res f z = t

theorem rel_ex (hR : RootPow) {q : ℕ} {j k l : ℤ} (h : j + k = l) {X : Scheme.{0}} (y : Sec (tw q k) X) (x : Sec (tw q j) X) :
    ∃ z : Sec (tw q l) X, Rel y x z := by
  have hS := locSieve_mem hR l y x x
  have hsh := (isSheaf_iff_isSheaf_of_type _ _).1 ((sheafCompose Scheme.etaleTopology (forget _)).obj (tw q l)).2 _ hS
  have hz : ∀ ⦃Y : Scheme.{0}⦄ (f : Y ⟶ X), locSieve l y x x f → ∃ z : Sec (tw q l) Y, Good (Sec.res f y) (Sec.res f x) z :=
    fun Y f hf => hf.imp fun _ hz => hz.choose_spec.1
  choose z hz using hz
  obtain ⟨t, ht, -⟩ := hsh z (fun Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ e => by
    have a1 := (hz f₁ h₁).res g₁
    have a2 := (hz f₂ h₂).res g₂
    rw [← res_comp, ← res_comp] at a1 a2
    rw [e] at a1
    exact a1.uniq hR h a2)
  refine ⟨t, fun Y f s hs => ?_⟩
  refine sep _ (Scheme.etaleTopology.pullback_stable f hS) _ _ (fun Z g hg => ?_)
  have e : Sec.res (F := tw q l) (g ≫ f) t = z (g ≫ f) hg := ht (g ≫ f) hg
  refine (res_comp g f t).symm.trans (e.trans ?_)
  have a1 := hs.res g
  rw [← res_comp, ← res_comp] at a1
  exact (hz _ hg).uniq hR h a1

theorem Rel.res {q : ℕ} {j k l : ℤ} {X Y : Scheme.{0}} {y : Sec (tw q k) X} {x : Sec (tw q j) X} {z : Sec (tw q l) X}
    (hr : Rel y x z) (f : Y ⟶ X) : Rel (Sec.res f y) (Sec.res f x) (Sec.res f z) := by
  intro Z g t ht
  rw [← res_comp, ← res_comp] at ht
  rw [← res_comp]
  exact hr _ t ht

theorem Rel.uniq (hR : RootPow) {q : ℕ} {j k l : ℤ} {X : Scheme.{0}} {y : Sec (tw q k) X}
    {x : Sec (tw q j) X} {z z' : Sec (tw q l) X} (hg : Rel y x z) (hg' : Rel y x z') : z = z' := by
  refine sep _ (locSieve_mem hR l y x x) _ _ ?_
  rintro Y f ⟨t, -, ht, -⟩
  rw [hg f t ht, hg' f t ht]

theorem Gen_of (hR : RootPow) : LateralTheory.E.MulPf.Gen := by
  intro q
  choose m hm using fun (j k l : ℤ) (h : j + k = l) (X : Scheme.{0}) (y : Sec (tw q k) X) (x : Sec (tw q j) X) => rel_ex hR h y x
  refine ⟨fun j k l h X y => AddMonoidHom.mk' (m j k l h X y) (fun x x' => ?_), ?_, ?_⟩
  · refine sep _ (locSieve_mem hR l y x x') _ _ ?_
    rintro Y f ⟨t, t', h1, h2, h3⟩
    rw [hm j k l h X y _ f _ h3, ← hm j k l h X y _ f _ h1, ← hm j k l h X y _ f _ h2]
    exact (map_add _ _ _).symm
  · intro j k l h X Y f y x
    exact ((hm j k l h X y x).res f).uniq hR (hm j k l h Y _ _)
  · intro j k l h X ζ
    refine sep ⊤ (Scheme.etaleTopology.top_mem _) _ _ (fun Y f _ => ?_)
    refine hm j k l h X _ _ f _ (Good.res (Or.inr ⟨ζ, 1, 1, ?_, ?_, ?_⟩) f) <;> simp only [mul_one, one_smul]

end LateralTheory.E.GenPf
end
end
