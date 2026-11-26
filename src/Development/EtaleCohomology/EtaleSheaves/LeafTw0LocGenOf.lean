module

public import Development.EtaleCohomology.EtaleSheaves.LeafSHNbSys

@[expose] public section

section -- merged from Development.EtaleCohomology.EtaleSheaves.Geo
section -- merged from Development.EtaleCohomology.EtaleSheaves.PowQEqOne
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafTw0LocGenPfA

theorem pow_q_eq_one {q : ℕ} {B : Type} [CommRing B] (x : B)
    (hx : Polynomial.aeval x (Polynomial.cyclotomic q ℤ) = 0) : x ^ q = 1 := by
  obtain ⟨p, hp⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one q ℤ
  have := congrArg (Polynomial.aeval x) hp
  simp only [map_sub, map_pow, Polynomial.aeval_X, map_one, map_mul, hx, zero_mul] at this
  exact sub_eq_zero.1 this

theorem local_eq {q : ℕ} [NeZero q] {B : Type} [CommRing B] [IsLocalRing B] (hq : IsUnit (q : B)) {x y : B}
    (hx : x ^ q = 1) (hy : y ^ q = 1) (hr : IsLocalRing.residue B x = IsLocalRing.residue B y) : x = y := by
  have hg := geom_sum₂_mul x y q
  rw [hx, hy, sub_self] at hg
  have hyu : IsUnit y := IsUnit.of_pow_eq_one hy (NeZero.ne q)
  have hres : IsLocalRing.residue B (∑ i ∈ Finset.range q, x ^ i * y ^ (q - 1 - i)) =
      IsLocalRing.residue B ((q : B) * y ^ (q - 1)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_mul, map_pow, map_natCast]
    rw [Finset.sum_congr rfl (g := fun _ => IsLocalRing.residue B y ^ (q - 1))]
    · simp
    · intro i hi
      rw [map_mul, map_pow, map_pow, hr, ← pow_add]
      congr 1; have := Finset.mem_range.1 hi; omega
  have hu' : IsUnit (∑ i ∈ Finset.range q, x ^ i * y ^ (q - 1 - i)) := by
    have h1 : IsUnit (IsLocalRing.residue B ((q : B) * y ^ (q - 1))) := (hq.mul (hyu.pow _)).map _
    rw [← hres] at h1
    exact (isUnit_map_iff (IsLocalRing.residue B) _).1 h1
  exact sub_eq_zero.1 ((IsUnit.mul_right_eq_zero hu').1 hg)

theorem res_root {q : ℕ} {B : Type} [CommRing B] [IsLocalRing B] (z : B)
    (hz : Polynomial.aeval z (Polynomial.cyclotomic q ℤ) = 0) :
    Polynomial.IsRoot (Polynomial.cyclotomic q (IsLocalRing.ResidueField B)) (IsLocalRing.residue B z) := by
  have h := Polynomial.aeval_algHom_apply (IsLocalRing.residue B).toIntAlgHom z (Polynomial.cyclotomic q ℤ)
  rw [hz, map_zero] at h
  rw [← Polynomial.map_cyclotomic_int, Polynomial.IsRoot.def, Polynomial.eval_map]
  rw [Polynomial.aeval_def, algebraMap_int_eq] at h
  exact h

theorem local_pow {q : ℕ} [NeZero q] {B : Type} [CommRing B] [IsLocalRing B] (hq : IsUnit (q : B)) {ζ ξ : B}
    (hζ : Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0) (hξ : Polynomial.aeval ξ (Polynomial.cyclotomic q ℤ) = 0) :
    ∃ a : (ZMod q)ˣ, ξ = ζ ^ (a : ZMod q).val := by
  have : NeZero ((q : ℕ) : IsLocalRing.ResidueField B) :=
    ⟨by simpa [map_natCast] using (hq.map (IsLocalRing.residue B)).ne_zero⟩
  have root : ∀ z : B, Polynomial.aeval z (Polynomial.cyclotomic q ℤ) = 0 →
      IsPrimitiveRoot (IsLocalRing.residue B z) q := fun z hz =>
    Polynomial.isRoot_cyclotomic_iff.1 (res_root z hz)
  obtain ⟨i, hi, hpow⟩ := (root ζ hζ).eq_pow_of_pow_eq_one ((root ξ hξ).pow_eq_one)
  have hc : i.Coprime q :=
    ((root ζ hζ).pow_iff_coprime (Nat.pos_of_ne_zero (NeZero.ne q)) i).1 (hpow ▸ root ξ hξ)
  refine ⟨ZMod.unitOfCoprime i hc, ?_⟩
  have hval : ((ZMod.unitOfCoprime i hc : (ZMod q)ˣ) : ZMod q).val = i := by
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hi]
  rw [hval]
  refine local_eq hq (pow_q_eq_one ξ hξ) ?_ ?_
  · rw [← pow_mul, mul_comm, pow_mul, pow_q_eq_one ζ hζ, one_pow]
  · rw [map_pow]; exact hpow.symm

end LateralTheory.E.LeafTw0LocGenPfA
end
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafTw0LocGenPfB
open LateralTheory.E.LeafTw0LocGenPfA

theorem geo {q : ℕ} [NeZero q] (V : Scheme.{0}) (ζ ξ : Prim q Γ(V, ⊤)) :
    Loc V fun W h => ∃ a : (ZMod q)ˣ, h.appTop ξ.1 = (h.appTop ζ.1) ^ (a : ZMod q).val := by
  classical
  have key : ∀ x : V, ∃ (Wx : V.Opens) (_ : x ∈ Wx) (a : (ZMod q)ˣ),
      V.presheaf.map (homOfLE le_top : Wx ⟶ ⊤).op ξ.1 =
        V.presheaf.map (homOfLE le_top : Wx ⟶ ⊤).op (ζ.1 ^ (a : ZMod q).val) := by
    intro x
    have hq : IsUnit ((q : V.presheaf.stalk x)) := by
      simpa using ζ.2.1.map (V.presheaf.germ ⊤ x trivial).hom
    have hr : ∀ z : Γ(V, ⊤), Polynomial.aeval z (Polynomial.cyclotomic q ℤ) = 0 →
        Polynomial.aeval ((V.presheaf.germ ⊤ x trivial).hom z) (Polynomial.cyclotomic q ℤ) = 0 := by
      intro z hz
      have h := Polynomial.aeval_algHom_apply (V.presheaf.germ ⊤ x trivial).hom.toIntAlgHom z (Polynomial.cyclotomic q ℤ)
      rw [hz, map_zero] at h
      exact h
    obtain ⟨a, ha⟩ := local_pow hq (hr _ ζ.2.2) (hr _ ξ.2.2)
    have h2 : (V.presheaf.germ ⊤ x trivial).hom ξ.1 = (V.presheaf.germ ⊤ x trivial).hom (ζ.1 ^ (a : ZMod q).val) := by
      rw [map_pow]; exact ha
    obtain ⟨Wx, hx, i1, i2, he⟩ := TopCat.Presheaf.germ_eq V.presheaf (U := ⊤) (V := ⊤) x trivial trivial _ _ h2
    refine ⟨Wx, hx, a, ?_⟩
    have e1 : i1 = homOfLE le_top := Subsingleton.elim _ _
    have e2 : i2 = homOfLE le_top := Subsingleton.elim _ _
    subst e1 e2
    exact he
  choose Wx hx a ha using key
  have fin : ∀ (x : V) {W : Scheme.{0}} (g' : W ⟶ (Wx x).toScheme),
      (g' ≫ (Wx x).ι).appTop ξ.1 = ((g' ≫ (Wx x).ι).appTop ζ.1) ^ (a x : ZMod q).val := by
    intro x W g'
    have hle : (Wx x).ι ''ᵁ ⊤ ≤ Wx x := by simp
    have hW : ∀ z : Γ(V, ⊤), (Wx x).ι.appTop z =
        V.presheaf.map (homOfLE hle).op (V.presheaf.map (homOfLE le_top : Wx x ⟶ ⊤).op z) := by
      intro z
      rw [Scheme.Opens.ι_appTop, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl
    rw [Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hW, hW, ha x]
    simp only [map_pow]
    exact map_pow (ConcreteCategory.hom (Scheme.Hom.appTop g')) _ _
  let 𝒰 : V.Cover (Scheme.precoverage @Etale) :=
    Scheme.Cover.mkOfCovers V (fun x => (Wx x).toScheme) (fun x => (Wx x).ι) (fun x => ⟨x, ⟨x, hx x⟩, rfl⟩)
  refine ⟨_, Scheme.Cover.mem_grothendieckTopology 𝒰, fun W h hh => ?_⟩
  obtain ⟨x, g, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hh
  exact ⟨a x, fin x g⟩

end LateralTheory.E.LeafTw0LocGenPfB
end
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafTw0LocGenPf
open LateralTheory.E.LeafTw0LocGenPfA LateralTheory.E.LeafTw0LocGenPfB

theorem loc_top {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : ∀ V g, P V g) : Loc U P :=
  ⟨⊤, GrothendieckTopology.top_mem _ _, fun V g _ => h V g⟩

theorem loc_finset {ι : Type*} [DecidableEq ι] {U : Scheme.{0}} (s : Finset ι)
    {P : ι → ∀ V : Scheme.{0}, (V ⟶ U) → Prop}
    (h : ∀ i ∈ s, Loc U (P i)) : Loc U fun V g => ∀ i ∈ s, P i V g := by
  induction s using Finset.induction_on with
  | empty => exact loc_top fun _ _ i hi => by simp at hi
  | insert j s hj ih =>
    obtain ⟨S0, h0, hP0⟩ := h j (Finset.mem_insert_self j s)
    obtain ⟨S1, h1, hP1⟩ := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    refine ⟨S0 ⊓ S1, Scheme.etaleTopology.intersection_covering h0 h1, fun V g hg i hi => ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact hP0 V g hg.1
    · exact hP1 V g hg.2 i hi

theorem res_sec {R : Type} [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) {W V : Scheme.{0}}
    (g : W ⟶ V) (x : M.obj Γ(V, ⊤)) :
    Sec.res g (ofRings.sec M V x) = ofRings.sec M W ((M.map g.appTop).hom x) := by
  have := congrArg (fun f => f.hom x) ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)).naturality g.op)
  exact this.symm

theorem relq {q : ℕ} {A : CommRingCat.{0}} (ζ ξ : Prim q A) (a : (ZMod q)ˣ) (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) :
    (Submodule.Quotient.mk (Finsupp.single ξ 1) : (Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q 0 A) =
      Submodule.Quotient.mk (Finsupp.single ζ 1) := by
  rw [Submodule.Quotient.eq]
  refine Submodule.subset_span ⟨ζ, ξ, a, h, ?_⟩
  simp
  rfl

theorem mk_mapDomain {q : ℕ} {A B : CommRingCat.{0}} (f : A ⟶ B) (r : Prim q A →₀ ULift.{1} (ZMod q))
    (ζ0 : Prim q A)
    (hrel : ∀ ξ ∈ r.support, (Submodule.Quotient.mk (Finsupp.single (Prim.map f.hom ξ) 1) :
      (Prim q B →₀ ULift.{1} (ZMod q)) ⧸ twRel q 0 B) = Submodule.Quotient.mk (Finsupp.single (Prim.map f.hom ζ0) 1)) :
    (Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map f.hom) r) : (Prim q B →₀ ULift.{1} (ZMod q)) ⧸ twRel q 0 B) =
      (r.sum fun _ c => c) • Submodule.Quotient.mk (Finsupp.single (Prim.map f.hom ζ0) 1) := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← Submodule.mkQ_apply, Finsupp.mapDomain, Finsupp.sum, map_sum, Finsupp.sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun ξ hξ => ?_
  rw [← hrel ξ hξ, Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul, Finsupp.smul_single_one]

theorem LeafTw0LocGen_of : LateralTheory.E.LeafTw0LocSplitPf.LeafTw0LocGen := by
  classical
  intro q _ U n a
  have hA : ∀ k, Loc U fun V g => ∃ t : (twF q 0).obj Γ(V, ⊤), ofRings.sec (twF q 0) V t = Sec.res g (a k) := by
    intro k
    exact ⟨_, Presheaf.imageSieve_mem Scheme.etaleTopology
      (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q 0)) (U := op U) (a k), fun V g hg => hg⟩
  have hA' := loc_finset (U := U) Finset.univ (fun k _ => hA k)
  refine LateralTheory.E.LeafTensMonoPf.loc_trans hA' fun V g hg => ?_
  choose t ht using fun k => hg k (Finset.mem_univ k)
  let r : Fin n → (Prim q Γ(V, ⊤) →₀ ULift.{1} (ZMod q)) := fun k =>
    (Submodule.Quotient.mk_surjective _ (t k : (Prim q Γ(V, ⊤) →₀ ULift.{1} (ZMod q)) ⧸ twRel q 0 Γ(V, ⊤))).choose
  have hr : ∀ k, (Submodule.Quotient.mk (r k) : (Prim q Γ(V, ⊤) →₀ ULift.{1} (ZMod q)) ⧸ twRel q 0 Γ(V, ⊤)) = t k :=
    fun k => (Submodule.Quotient.mk_surjective _ (t k : (Prim q Γ(V, ⊤) →₀ ULift.{1} (ZMod q)) ⧸ twRel q 0 Γ(V, ⊤))).choose_spec
  rcases isEmpty_or_nonempty (Prim q Γ(V, ⊤)) with hE | ⟨⟨ζ0⟩⟩
  · refine loc_top fun W h => ⟨0, fun _ => 0, fun k => ?_, Or.inl rfl⟩
    rw [zero_smul, LateralTheory.E.LeafTensMonoPf.res_comp, ← ht k, ← hr k, Subsingleton.elim (r k) 0,
      Submodule.Quotient.mk_zero]
    unfold ofRings.sec
    have h0 := map_zero (((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q 0)).app (op V)).hom)
    first
      | exact (congrArg (Sec.res h) h0).trans (map_zero _)
      | (erw [h0]; exact map_zero _)
  · obtain ⟨S, hS, hP⟩ := loc_finset (U := V) (Finset.univ.biUnion fun k => (r k).support) (fun ξ _ => geo V ζ0 ξ)
    refine ⟨S, hS, fun W h hh => ?_⟩
    have hrel := hP W h hh
    refine ⟨twGen 0 (Prim.map h.appTop.hom ζ0), fun k => (r k).sum fun _ c => c, fun k => ?_, Or.inr ⟨_, rfl⟩⟩
    rw [LateralTheory.E.LeafTensMonoPf.res_comp, ← ht k, ← hr k]
    refine (res_sec (twF q 0) h _).trans ?_
    have e1 : ((twF q 0).map h.appTop).hom (Submodule.Quotient.mk (r k)) =
        Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map h.appTop.hom) (r k)) := rfl
    rw [e1, mk_mapDomain h.appTop (r k) ζ0 (fun ξ hξ => ?_)]
    · exact map_smul _ _ _
    · obtain ⟨b, hb⟩ := hrel ξ (Finset.mem_biUnion.2 ⟨k, Finset.mem_univ _, hξ⟩)
      exact relq _ _ b hb

end LateralTheory.E.LeafTw0LocGenPf
