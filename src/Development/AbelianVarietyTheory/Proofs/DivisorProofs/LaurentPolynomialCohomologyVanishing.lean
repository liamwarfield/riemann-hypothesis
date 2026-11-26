module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentPolynomialTateTwistCohomologyVanishingInd

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFactorStrictHenselisation
open IsLocalRing

namespace GlobalTheory.StrictHensFactor

theorem exists_factor_strictHenselisation : ∀ (A C B : Type) [CommRing A] [IsLocalRing A] [CommRing C] [Algebra A C] [CommRing B] [HenselianLocalRing B] [IsSepClosed (ResidueField B)] [Algebra A B] [IsLocalHom (algebraMap A B)] (u : C →ₐ[A] B), ∃ (D : Type) (_ : CommRing D) (_ : IsLocalRing D) (_ : Algebra A D) (c : C →ₐ[A] D) (w : D →ₐ[A] B), w.comp c = u ∧ ∃ (P : Ideal C) (_ : P.IsPrime) (φ : Localization.AtPrime P →+* D), GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ ∧ φ.comp (algebraMap C (Localization.AtPrime P)) = (c : C →+* D) ∧ P.comap (algebraMap A C) = maximalIdeal A := by
  intro A C B _ _ _ _ _ _ _ _ _ u
  set P : Ideal C := (maximalIdeal B).comap (u : C →+* B) with hP
  haveI hPp : P.IsPrime := Ideal.comap_isPrime _ _
  let L := Localization.AtPrime P
  have hu : ∀ y : P.primeCompl, IsUnit ((u : C →+* B) y) := by
    intro y
    have := y.2
    by_contra hy
    exact this ((IsLocalRing.mem_maximalIdeal _).2 hy)
  let b : L →+* B := IsLocalization.lift hu
  have hb : b.comp (algebraMap C L) = (u : C →+* B) := IsLocalization.lift_comp hu
  haveI hbloc : IsLocalHom b := by
    refine ⟨fun x hx => ?_⟩
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl x
    rw [IsLocalization.AtPrime.isUnit_mk'_iff]
    intro ha
    have h1 : (u : C →+* B) a = (u : C →+* B) s * b (IsLocalization.mk' _ a s) :=
      (IsLocalization.lift_mk'_spec _ _ _ _).1 rfl
    have h2 : IsUnit ((u : C →+* B) a) := by
      rw [h1]; exact (hu s).mul hx
    exact (IsLocalRing.mem_maximalIdeal _).1 ha h2
  obtain ⟨S, _, _, _, hloc, hsc, -, -, -, ι, _, _, _, Si, hmono, hcov, hA⟩ :=
    GlobalTheory.exists_strictHenselisation L (SeparableClosure (ResidueField L))
  have hind : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap L S) := by
    refine GlobalTheory.StrictHensUnion.indEtale_of_directed_union L S ι Si hmono hcov fun i => ?_
    obtain ⟨A', _, _, _, q, _, ⟨e⟩⟩ := hA i
    exact GlobalTheory.StrictHensUnion.indEtale_of_algEquiv e
      (GlobalTheory.StrictHensUnion.indEtale_localization_of_etale L A' q.primeCompl)
  have hstrict : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation (algebraMap L S) :=
    ⟨inferInstance, hsc, hloc, hind⟩
  obtain ⟨g, hg⟩ := GlobalTheory.NCyc.StrictLocLift.exists_ringHom_of_isStrictHenselisation
    (algebraMap L S) hstrict b
  let cR : C →+* S := (algebraMap L S).comp (algebraMap C L)
  letI algAS : Algebra A S := (cR.comp (algebraMap A C)).toAlgebra
  let c : C →ₐ[A] S := { cR with commutes' := fun a => rfl }
  have hgc : g.comp cR = (u : C →+* B) := by
    rw [← RingHom.comp_assoc, hg, hb]
  let w : S →ₐ[A] B :=
    { g with
      commutes' := fun a => by
        change g (cR (algebraMap A C a)) = algebraMap A B a
        rw [← RingHom.comp_apply, hgc]
        exact u.commutes a }
  refine ⟨S, inferInstance, inferInstance, algAS, c, w, ?_, P, hPp, algebraMap L S, hstrict, rfl, ?_⟩
  · ext x
    exact DFunLike.congr_fun hgc x
  · ext a
    rw [hP, Ideal.comap_comap, Ideal.mem_comap]
    have : ((u : C →+* B).comp (algebraMap A C)) a = algebraMap A B a := u.commutes a
    rw [this, IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      mem_nonunits_iff, isUnit_map_iff]

end GlobalTheory.StrictHensFactor
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentCohomologyVanishingOfNoetherianHenselian
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNoetherianShFactor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNoetherianShFactor
open GlobalTheory.EtC IsLocalRing

namespace GlobalTheory.NoethSHFactor

theorem exists_noetherian_sh_factor : ∀ (R A : Type) [CommRing R] [IsNoetherianRing R] [CommRing A], SH A →
    ∀ b : R →+* A, ∃ (C : Type) (_ : CommRing C), IsNoetherianRing C ∧ SH C ∧
      ∃ (f : R →+* C) (g : C →+* A), g.comp f = b := by
  intro R A _ _ _ hA b
  obtain ⟨hH, hsep⟩ := hA
  let p : Ideal R := (maximalIdeal A).comap b
  haveI : p.IsPrime := Ideal.comap_isPrime _ _
  let Rp := Localization.AtPrime p
  have hunit : ∀ y : p.primeCompl, IsUnit (b y) := by
    intro y
    by_contra h
    exact y.2 ((mem_maximalIdeal _).2 h)
  let b' : Rp →+* A := IsLocalization.lift (M := p.primeCompl) hunit
  have hb' : b'.comp (algebraMap R Rp) = b := IsLocalization.lift_comp hunit
  letI : Algebra Rp A := b'.toAlgebra
  haveI hloc : IsLocalHom (algebraMap Rp A) := by
    refine ⟨fun x hx => ?_⟩
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl x
    rw [IsLocalization.AtPrime.isUnit_mk'_iff]
    intro hr
    have h1 : IsLocalization.mk' Rp r s * algebraMap R Rp s = algebraMap R Rp r :=
      IsLocalization.mk'_spec Rp r s
    have h2 : IsUnit (b r) := by
      rw [← hb', RingHom.comp_apply, ← h1, map_mul]
      exact hx.mul (by rw [← RingHom.comp_apply, hb']; exact hunit s)
    exact (mem_maximalIdeal _).1 hr h2
  have hfactor :=
    _root_.GlobalTheory.StrictHensFactor.exists_factor_strictHenselisation Rp Rp A
      (Algebra.ofId Rp A)
  obtain ⟨D, _, _, _, c, w, hwc, P, _, φ, hφ, _, _⟩ := hfactor
  haveI : IsNoetherianRing Rp := IsLocalization.isNoetherianRing p.primeCompl Rp inferInstance
  haveI : IsNoetherianRing (Localization.AtPrime P) :=
    IsLocalization.isNoetherianRing P.primeCompl _ inferInstance
  letI : Algebra (Localization.AtPrime P) D := φ.toAlgebra
  have hD : IsNoetherianRing D :=
    GlobalTheory.StalkNoeth.isNoetherianRing_of_indEt (Localization.AtPrime P) D hφ.2.2.2
  refine ⟨D, inferInstance, hD, ⟨hφ.1, hφ.2.1⟩, (c : Rp →+* D).comp (algebraMap R Rp), (w : D →+* A), ?_⟩
  rw [← RingHom.comp_assoc]
  have hwc' : (w : D →+* A).comp (c : Rp →+* D) = b' :=
    congrArg AlgHom.toRingHom hwc
  rw [hwc', hb']

end GlobalTheory.NoethSHFactor
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNoetherianShFactorStatement
open GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_noetherian_sh_factorization : ∀ (R A : Type) [CommRing R] [IsNoetherianRing R] [CommRing A], SH A → ∀ b : R →+* A, ∃ (C : Type) (_ : CommRing C), IsNoetherianRing C ∧ SH C ∧ ∃ (f : R →+* C) (g : C →+* A), g.comp f = b := by
  first | (exact @GlobalTheory.NoethSHFactor.exists_noetherian_sh_factor) | (exact GlobalTheory.NoethSHFactor.exists_noetherian_sh_factor) | (intros; apply GlobalTheory.NoethSHFactor.exists_noetherian_sh_factor  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentCohomologyVanishingOfNoetherianHenselian
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.LaurentNoeth

def lmap {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) : LaurentPolynomial R →+* LaurentPolynomial S :=
  LaurentPolynomial.eval₂ ((LaurentPolynomial.C : S →+* LaurentPolynomial S).comp f) (laurentVarUnit S)

theorem laurentVarUnit_zpow (S : Type) [CommRing S] (n : ℤ) :
    ((laurentVarUnit S ^ n : (LaurentPolynomial S)ˣ) : LaurentPolynomial S) = LaurentPolynomial.T n := by
  induction n using Int.induction_on with
  | zero => simp
  | succ k ih =>
    rw [zpow_add_one, Units.val_mul, ih, LaurentPolynomial.T_add]; rfl
  | pred k ih =>
    rw [zpow_sub_one, Units.val_mul, ih, sub_eq_add_neg, LaurentPolynomial.T_add]; rfl

theorem laurentMap_C_mul_T {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (a : R) (n : ℤ) :
    lmap f (LaurentPolynomial.C a * LaurentPolynomial.T n) = LaurentPolynomial.C (f a) * LaurentPolynomial.T n := by
  simp [lmap, laurentVarUnit_zpow]

theorem lext {R : Type} [CommRing R] {p p' : LaurentPolynomial R} (h : ∀ n, p.coeff n = p'.coeff n) : p = p' :=
  AddMonoidAlgebra.ext (Finsupp.ext h)

theorem lmap_apply {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (p : LaurentPolynomial R) (n : ℤ) :
    (lmap f p).coeff n = f (p.coeff n) := by
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add (f := _), AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, Finsupp.add_apply, hp, hq,
      map_add]
  | C_mul_T k a =>
    rw [laurentMap_C_mul_T, ← LaurentPolynomial.single_eq_C_mul_T, ← LaurentPolynomial.single_eq_C_mul_T,
      AddMonoidAlgebra.coeff_single, AddMonoidAlgebra.coeff_single, Finsupp.single_apply, Finsupp.single_apply]
    split_ifs <;> simp

theorem lmap_injective {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (hf : Function.Injective f) :
    Function.Injective (lmap f) := by
  intro p p' h
  refine lext fun n => ?_
  apply hf
  rw [← lmap_apply, ← lmap_apply, h]

theorem lmap_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    lmap (g.comp f) = (lmap g).comp (lmap f) := by
  refine RingHom.ext fun p => lext fun n => ?_
  rw [RingHom.comp_apply, lmap_apply, lmap_apply, lmap_apply, RingHom.comp_apply]

theorem spMap_comp' {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (F : R →+* S) (G : S →+* T) :
    spMap (G.comp F) = spMap G ≫ spMap F := by
  show sch.map (Spec.map (CommRingCat.ofHom (G.comp F))) = sch.map (Spec.map (CommRingCat.ofHom G)) ≫ sch.map (Spec.map (CommRingCat.ofHom F))
  rw [CommRingCat.ofHom_comp, Spec.map_comp, Functor.map_comp]

attribute [local instance] Classical.propDecidable

variable {A : Type} [CommRing A]

def sub (u : A) (s : Finset A) : Subalgebra ℤ A := Algebra.adjoin ℤ (↑(insert u s) : Set A)

theorem sub_mono (u : A) : Monotone (sub u) := fun _ _ h =>
  Algebra.adjoin_mono (Finset.coe_subset.2 (Finset.insert_subset_insert u h))

theorem mem_sub (u : A) (s : Finset A) {a : A} (ha : a ∈ insert u s) : a ∈ sub u s :=
  Algebra.subset_adjoin (Finset.mem_coe.2 ha)

theorem lmap_val_comp (u : A) {s t : Finset A} (hst : s ≤ t) :
    (lmap (sub u t).val.toRingHom).comp (lmap (Subalgebra.inclusion (sub_mono u hst)).toRingHom) =
      lmap (sub u s).val.toRingHom := by
  rw [← lmap_comp]; rfl

def diag (u : A) : Finset A ⥤ CommRingCat.{0} where
  obj s := CommRingCat.of (LaurentPolynomial (sub u s))
  map {s t} h := CommRingCat.ofHom (lmap (Subalgebra.inclusion (sub_mono u (leOfHom h))).toRingHom)
  map_id s := CommRingCat.hom_ext (RingHom.ext fun p => lext fun n => by
    simp only [CommRingCat.hom_ofHom, CommRingCat.hom_id, RingHom.id_apply, lmap_apply]; rfl)
  map_comp f g := CommRingCat.hom_ext (RingHom.ext fun p => lext fun n => by
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply, lmap_apply]; rfl)

def cocone (u : A) : Cocone (diag u) where
  pt := CommRingCat.of (LaurentPolynomial A)
  ι := { app := fun s => CommRingCat.ofHom (lmap (sub u s).val.toRingHom)
         naturality := fun s t h => by
           simp only [Functor.const_obj_map, Category.comp_id]
           exact CommRingCat.hom_ext (lmap_val_comp u (leOfHom h)) }

theorem exists_preimage (u : A) (x : LaurentPolynomial A) : ∃ s y, lmap (sub u s).val.toRingHom y = x := by
  induction x using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨s, y, rfl⟩ := hp
    obtain ⟨t, z, rfl⟩ := hq
    refine ⟨s ∪ t, lmap (Subalgebra.inclusion (sub_mono u Finset.subset_union_left)).toRingHom y +
      lmap (Subalgebra.inclusion (sub_mono u Finset.subset_union_right)).toRingHom z, ?_⟩
    rw [map_add (f := _), ← RingHom.comp_apply, ← RingHom.comp_apply, ← lmap_comp, ← lmap_comp]
    rfl
  | C_mul_T k a =>
    refine ⟨{a}, LaurentPolynomial.C ⟨a, mem_sub u _ (by simp)⟩ * LaurentPolynomial.T k, ?_⟩
    rw [laurentMap_C_mul_T]
    rfl

theorem cocone_isColimit (u : A) : Nonempty (IsColimit (cocone u)) := by
  haveI : ReflectsColimitsOfShape (Finset A) (forget CommRingCat.{0}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  refine ⟨isColimitOfReflects (forget CommRingCat.{0}) ?_⟩
  refine Types.FilteredColimit.isColimitOf _ _ ?_ ?_
  · intro x
    change LaurentPolynomial A at x
    obtain ⟨s, y, hy⟩ := exists_preimage u x
    exact ⟨s, y, hy.symm⟩
  · intro s t xs xt h
    refine ⟨s ∪ t, homOfLE Finset.subset_union_left, homOfLE Finset.subset_union_right, ?_⟩
    apply lmap_injective (sub u (s ∪ t)).val.toRingHom (fun a b hab => Subtype.ext hab)
    · change (lmap (sub u (s ∪ t)).val.toRingHom).comp (lmap _) xs = (lmap (sub u (s ∪ t)).val.toRingHom).comp (lmap _) xt
      rw [← lmap_comp, ← lmap_comp]
      exact h

theorem sub_fg (u : A) (s : Finset A) : (sub u s).FG := ⟨insert u s, rfl⟩

end GlobalTheory.EtC.LaurentNoeth


open GlobalTheory.EtC.LaurentNoeth in
theorem GlobalTheory.EtC.laurent_vanishing_of_noetherian : ∀ (q : ℕ) [NeZero q], (∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) → ∀ n i : ℤ, 2 ≤ n → Subsingleton (Ht q (sp (LaurentPolynomial A)) n i)) → ∀ (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ n i : ℤ, 2 ≤ n → Subsingleton (Ht q (sp (LaurentPolynomial A)) n i) := by
  classical
  intro q _ hN A _ hA hq n i hn
  refine ⟨fun x y => ?_⟩
  suffices key : ∀ x : Ht q (sp (LaurentPolynomial A)) n i, x = 0 by rw [key x, key y]
  intro x
  set u : A := ((hq.unit⁻¹ : Aˣ) : A)
  obtain ⟨hc⟩ := cocone_isColimit u
  have hqL : IsUnit (q : LaurentPolynomial A) := by
    have := hq.map (LaurentPolynomial.C : A →+* LaurentPolynomial A); simpa using this
  obtain ⟨j, y, hy⟩ := (GlobalTheory.T.etaleCohomology_twisted_filtered_colimit_continuity q (diag u) (cocone u) hc n i).1 x hqL
  haveI : Algebra.FiniteType ℤ (sub u j) := (Subalgebra.fg_iff_finiteType _).1 (sub_fg u j)
  haveI : IsNoetherianRing (sub u j) := Algebra.FiniteType.isNoetherianRing ℤ _
  obtain ⟨C, _, hCn, hCsh, f, g, hfg⟩ := GlobalTheory.T.exists_noetherian_sh_factorization (sub u j) A hA (sub u j).val.toRingHom
  haveI := hCn
  have hqS : IsUnit (q : sub u j) := by
    refine isUnit_iff_exists_inv.2 ⟨⟨u, mem_sub u j (Finset.mem_insert_self u j)⟩, ?_⟩
    apply Subtype.ext
    simp [u]
  have hqC : IsUnit (q : C) := by have := hqS.map f; simpa using this
  haveI := hN C hCsh hqC n i hn
  have e : (cocone u).ι.app j = CommRingCat.ofHom ((lmap g).comp (lmap f)) := by
    rw [← lmap_comp, hfg]; rfl
  rw [← hy, e]
  change pull _ (spMap ((lmap g).comp (lmap f))) _ _ y = 0
  rw [spMap_comp']
  refine (pull_comp (ZMod q) (spMap (lmap g)) (spMap (lmap f)) (tw q i) n y).trans ?_
  have : pull _ (spMap (lmap f)) (tw q i) n y = 0 := Subsingleton.elim _ _
  rw [this, map_zero]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentCohomologyVanishingOfNoetherianHenselianStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laurentCohomology_vanishing_of_noetherian_henselian : ∀ (q : ℕ) [NeZero q], (∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) → ∀ n i : ℤ, 2 ≤ n → Subsingleton (Ht q (sp (LaurentPolynomial A)) n i)) → ∀ (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ n i : ℤ, 2 ≤ n → Subsingleton (Ht q (sp (LaurentPolynomial A)) n i) := by
  first | (exact @GlobalTheory.EtC.laurent_vanishing_of_noetherian) | (exact GlobalTheory.EtC.laurent_vanishing_of_noetherian) | (intros; apply GlobalTheory.EtC.laurent_vanishing_of_noetherian  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicativeGroupCohomologyStrictlyHenselian
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentCohomology
namespace GlobalTheory.LaurentCohomologyVanishing

open GlobalTheory.EtC

theorem vanishing_below (q : ℕ) [NeZero q] (k : ℕ) :
    ∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) →
      ∀ m i : ℤ, 2 ≤ m → m < 2 + (k : ℤ) → Subsingleton (Ht q (sp (LaurentPolynomial A)) m i) := by
  induction k with
  | zero =>
    intro A _ _ _ _ m i h2 hm
    push_cast at hm
    omega
  | succ k ih =>
    intro A _ _ hA hq m i h2 hm
    push_cast at hm
    rcases lt_or_eq_of_le (show m ≤ 2 + (k : ℤ) by omega) with h | h
    · exact ih A hA hq m i h2 h
    · subst h
      exact GlobalTheory.T.laurentPolynomial_tateTwistCohomology_vanishing_inductive q (2 + k) (by omega) ih A hA hq i

theorem laurent_cohomology (q : ℕ) [NeZero q] (A : Type) [CommRing A] (hA : SH A) (hq : IsUnit (q : A))
    (n i : ℤ) :
    (2 ≤ n → Subsingleton (Ht q (sp (LaurentPolynomial A)) n i)) ∧
      Nonempty (Ht q (sp (LaurentPolynomial A)) 1 i ≃+ ZMod q) := by
  refine ⟨fun hn => GlobalTheory.T.laurentCohomology_vanishing_of_noetherian_henselian q (fun B _ _ hB hqB m j hm =>
    vanishing_below q m.toNat B hB hqB m j hm (by omega)) A hA hq n i hn, ?_⟩
  obtain ⟨e⟩ := GlobalTheory.T.nonempty_ht_zero_addEquiv_zmod_of_sh q A hA hq (i - 1)
  exact ⟨(AddEquiv.ofBijective (gmPhi q A i) (GlobalTheory.T.laurentKummerCupProduct_bijective_strictlyHenselian q A hA hq i)).symm.trans e⟩

end GlobalTheory.LaurentCohomologyVanishing
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicativeGroupCohomologyStrictlyHenselian
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem GlobalTheory.gm_cohomology_strictlyHenselian : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) →
    ∀ n i : ℤ, (2 ≤ n → Subsingleton (Ht q (sp (LaurentPolynomial A)) n i)) ∧
      Nonempty (Ht q (sp (LaurentPolynomial A)) 1 i ≃+ ZMod q) := by
  first
  | exact @_root_.GlobalTheory.LaurentCohomologyVanishing.laurent_cohomology
  | exact _root_.GlobalTheory.LaurentCohomologyVanishing.laurent_cohomology
  | (apply _root_.GlobalTheory.LaurentCohomologyVanishing.laurent_cohomology <;> assumption)
  | (intros; apply _root_.GlobalTheory.LaurentCohomologyVanishing.laurent_cohomology <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LaurentCohomologyVanishing.laurent_cohomology <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LaurentCohomologyVanishing.laurent_cohomology ..)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicativeGroupCohomologyStrictlyHenselianStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicativeGroup_cohomology_strictlyHenselian : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ n i : ℤ, (2 ≤ n → Subsingleton (Ht q (sp (LaurentPolynomial A)) n i)) ∧ Nonempty (Ht q (sp (LaurentPolynomial A)) 1 i ≃+ ZMod q) := by
  first | (exact @GlobalTheory.gm_cohomology_strictlyHenselian) | (exact GlobalTheory.gm_cohomology_strictlyHenselian) | (intros; apply GlobalTheory.gm_cohomology_strictlyHenselian  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentPolynomialCohomologyVanishing
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem laurentPolynomial_cohomology_strictlyHenselian_vanishing : GlobalTheory.EtC.C5 := fun q _ A _ hA hq n i => GlobalTheory.T.multiplicativeGroup_cohomology_strictlyHenselian q A hA hq n i

end GlobalTheory.EtC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentPolynomialCohomologyVanishingStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_cohomology_locally_acyclic : GlobalTheory.EtC.C5 := by
  first | (exact @GlobalTheory.EtC.laurentPolynomial_cohomology_strictlyHenselian_vanishing) | (exact GlobalTheory.EtC.laurentPolynomial_cohomology_strictlyHenselian_vanishing) | (intros; apply GlobalTheory.EtC.laurentPolynomial_cohomology_strictlyHenselian_vanishing  <;> assumption)
end
