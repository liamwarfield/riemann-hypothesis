module

public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyVanishingAlgebraicOverRatFunc

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionRingAwayEtaleDedekindArtinianReduced
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionRingAwayEtaleDedekindArtinianReduced
namespace GlobalTheory

theorem mem_minimalPrimes_of_disjoint_nonZeroDivisors {R : Type} [CommRing R] [IsReduced R]
    [IsNoetherianRing R] (p : Ideal R) [p.IsPrime] (hp : Disjoint (p : Set R) (nonZeroDivisors R)) :
    p ∈ minimalPrimes R := by
  classical
  have hfin : (minimalPrimes R).Finite := minimalPrimes.finite_of_isNoetherianRing R
  have hsub : (p : Set R) ⊆ ⋃ q ∈ hfin.toFinset, (q : Set R) := by
    intro x hx
    have hx' : x ∉ nonZeroDivisors R := Set.disjoint_left.mp hp hx
    rw [mem_nonZeroDivisors_iff_right] at hx'
    push Not at hx'
    obtain ⟨y, hxy, hy⟩ := hx'
    have hrad : (⊥ : Ideal R).radical = ⊥ := by
      exact nilradical_eq_zero R
    have : x ∈ ⋃ q ∈ (⊥ : Ideal R).minimalPrimes, (q : Set R) := by
      rw [Ideal.iUnion_minimalPrimes]
      refine ⟨y, ?_, ?_⟩
      · rw [hrad]; simpa using hy
      · rw [hrad]; simpa [mul_comm] using hxy
    simpa [Set.Finite.mem_toFinset] using this
  have hprime : ∀ q ∈ hfin.toFinset, q.IsPrime := fun q hq =>
    ((Set.Finite.mem_toFinset hfin).1 hq).isPrime
  obtain ⟨q, hq, hpq⟩ := (Ideal.subset_union_prime (⊥ : Ideal R) ⊥ fun q hq _ _ => hprime q hq).1 hsub
  have hqm : q ∈ minimalPrimes R := (Set.Finite.mem_toFinset hfin).1 hq
  have : q ≤ p := hqm.2 ⟨inferInstance, bot_le⟩ hpq
  exact (le_antisymm hpq this) ▸ hqm

theorem total_fractions_isArtinian_isReduced (R : Type) [CommRing R] [IsReduced R]
    [IsNoetherianRing R] : IsArtinianRing (FractionRing R) ∧ IsReduced (FractionRing R) := by
  have hN : IsNoetherianRing (FractionRing R) :=
    IsLocalization.isNoetherianRing (nonZeroDivisors R) _ inferInstance
  have hRed : IsReduced (FractionRing R) := inferInstance
  refine ⟨?_, hRed⟩
  rw [isArtinianRing_iff_isNoetherianRing_krullDimLE_zero]
  refine ⟨hN, Ring.krullDimLE_zero_iff.mpr fun P hP => ?_⟩
  obtain ⟨M, hM, hPM⟩ := Ideal.exists_le_maximal P hP.ne_top
  have key : ∀ (Q : Ideal (FractionRing R)), Q.IsPrime →
      Q.comap (algebraMap R (FractionRing R)) ∈ minimalPrimes R := by
    intro Q hQ
    have h := (IsLocalization.isPrime_iff_isPrime_disjoint (nonZeroDivisors R) (FractionRing R) Q).1 hQ
    have := h.1
    exact mem_minimalPrimes_of_disjoint_nonZeroDivisors _ h.2.symm
  have h1 := key P hP
  have h2 := key M hM.isPrime
  have hle : M.comap (algebraMap R (FractionRing R)) ≤ P.comap (algebraMap R (FractionRing R)) :=
    h2.2 ⟨h1.1.1, bot_le⟩ (Ideal.comap_mono hPM)
  have : P = M := by
    rw [← IsLocalization.map_under (nonZeroDivisors R) (FractionRing R) P,
      ← IsLocalization.map_under (nonZeroDivisors R) (FractionRing R) M]
    exact congrArg _ (le_antisymm (Ideal.comap_mono hPM) hle)
  exact this ▸ hM

theorem fractionRing_away_etale_isArtinian_isReduced : ∀ (B : Type) [CommRing B] [IsDedekindDomain B] (f : B) (A' : Type) [CommRing A'] [Algebra B A'] [Algebra.Etale B A'], IsArtinianRing (FractionRing (Localization.Away (algebraMap B A' f))) ∧ IsReduced (FractionRing (Localization.Away (algebraMap B A' f))) := by
  intro B _ _ f A' _ _ _
  have : IsNoetherianRing A' := Algebra.FiniteType.isNoetherianRing B A'
  have : IsReduced A' := GlobalTheory.isReduced_algebra_of_smooth_of_isNoetherianRing B A'
  have : IsNoetherianRing (Localization.Away (algebraMap B A' f)) :=
    IsLocalization.isNoetherianRing (Submonoid.powers (algebraMap B A' f)) _ inferInstance
  have : IsReduced (Localization.Away (algebraMap B A' f)) := inferInstance
  exact total_fractions_isArtinian_isReduced _

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionRingAwayEtaleDedekindArtinianReducedStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fractionRing_away_etale_dedekind_artinian_reduced : ∀ (B : Type) [CommRing B] [IsDedekindDomain B] (f : B) (A' : Type) [CommRing A'] [Algebra B A'] [Algebra.Etale B A'], IsArtinianRing (FractionRing (Localization.Away (algebraMap B A' f))) ∧ IsReduced (FractionRing (Localization.Away (algebraMap B A' f))) := by
  first | (exact @GlobalTheory.fractionRing_away_etale_isArtinian_isReduced) | (exact GlobalTheory.fractionRing_away_etale_isArtinian_isReduced) | (intros; apply GlobalTheory.fractionRing_away_etale_isArtinian_isReduced <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassVanishesAwayNonZeroDivisor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassVanishesAwayNonZeroDivisor
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC.TotFracAway

variable (R : Type) [CommRing R]

structure Idx where

  val : R
  mem : val ∈ nonZeroDivisors R

instance : Preorder (Idx R) where
  le a b := a.val ∣ b.val
  le_refl a := dvd_refl a.val
  le_trans _ _ _ := dvd_trans

instance : IsDirected (Idx R) (· ≤ ·) :=
  ⟨fun a b => ⟨⟨a.val * b.val, Submonoid.mul_mem _ a.mem b.mem⟩, dvd_mul_right _ _, dvd_mul_left _ _⟩⟩

instance : Nonempty (Idx R) := ⟨⟨1, Submonoid.one_mem _⟩⟩

variable {R}

theorem isUnit_of_dvd {a b : R} (h : a ∣ b) : IsUnit (algebraMap R (Localization.Away b) a) :=
  isUnit_of_dvd_unit (map_dvd _ h) (IsLocalization.Away.algebraMap_isUnit b)

def tr {a b : R} (h : a ∣ b) : Localization.Away a →+* Localization.Away b :=
  Localization.awayLift (algebraMap R _) a (isUnit_of_dvd h)

theorem tr_comp {a b : R} (h : a ∣ b) : (tr h).comp (algebraMap R _) = algebraMap R _ :=
  IsLocalization.Away.lift_comp a (isUnit_of_dvd h)

theorem away_ext {a : R} {S : Type} [CommRing S] {f g : Localization.Away a →+* S}
    (h : f.comp (algebraMap R _) = g.comp (algebraMap R _)) : f = g :=
  IsLocalization.ringHom_ext (Submonoid.powers a) h


variable (R) in
def diag : Idx R ⥤ CommRingCat.{0} where
  obj a := CommRingCat.of (Localization.Away a.val)
  map {a b} h := CommRingCat.ofHom (tr (leOfHom h : a.val ∣ b.val))
  map_id a := by
    ext1
    refine away_ext ?_
    simp [tr_comp]
  map_comp {a b c} f g := by
    ext1
    refine away_ext ?_
    simp [RingHom.comp_assoc, tr_comp]

def toFrac (a : Idx R) : Localization.Away a.val →+* FractionRing R :=
  Localization.awayLift (algebraMap R _) a.val
    (IsLocalization.map_units (FractionRing R) (⟨a.val, a.mem⟩ : nonZeroDivisors R))

theorem toFrac_comp (a : Idx R) : (toFrac a).comp (algebraMap R _) = algebraMap R (FractionRing R) :=
  IsLocalization.Away.lift_comp a.val
    (IsLocalization.map_units (FractionRing R) (⟨a.val, a.mem⟩ : nonZeroDivisors R))


variable (R) in
def cocone : Cocone (diag R) where
  pt := CommRingCat.of (FractionRing R)
  ι :=
    { app := fun a => CommRingCat.ofHom (toFrac a)
      naturality := fun a b h => by
        ext1
        refine away_ext ?_
        simp [diag, RingHom.comp_assoc, tr_comp, toFrac_comp] }

def idx1 : Idx R := ⟨1, Submonoid.one_mem _⟩

theorem desc_unit (s : Cocone (diag R)) (y : nonZeroDivisors R) :
    IsUnit (((s.ι.app idx1).hom.comp (algebraMap R (Localization.Away (1 : R)))) y) := by
  let b : Idx R := ⟨y.1, y.2⟩
  have hw := s.w (homOfLE (show (idx1 : Idx R) ≤ b from one_dvd _))
  rw [← hw]
  change IsUnit ((s.ι.app b).hom ((tr (one_dvd y.1)) (algebraMap R _ y.1)))
  rw [← RingHom.comp_apply (tr _), tr_comp]
  exact (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away y.1) y.1).map (s.ι.app b).hom


variable (R) in
def isColim : IsColimit (cocone R) where
  desc s := CommRingCat.ofHom (IsLocalization.lift (M := nonZeroDivisors R) (S := FractionRing R) (desc_unit s))
  fac s a := by
    have hw := s.w (homOfLE (show (idx1 : Idx R) ≤ a from one_dvd _))
    ext1
    change (IsLocalization.lift (M := nonZeroDivisors R) (S := FractionRing R) (desc_unit s)).comp (toFrac a) = (s.ι.app a).hom
    refine away_ext ?_
    rw [RingHom.comp_assoc, toFrac_comp, IsLocalization.lift_comp, ← hw]
    ext b
    exact congrArg (s.ι.app a).hom (DFunLike.congr_fun (tr_comp (one_dvd a.val)) b)
  uniq s m hm := by
    ext1
    change m.hom = IsLocalization.lift (M := nonZeroDivisors R) (S := FractionRing R) (desc_unit s)
    refine IsLocalization.ringHom_ext (S := FractionRing R) (nonZeroDivisors R) ?_
    rw [IsLocalization.lift_comp, ← hm idx1]
    ext b
    exact congrArg m.hom (DFunLike.congr_fun (toFrac_comp idx1) b).symm

theorem spMap_comp {A A' A'' : Type} [CommRing A] [CommRing A'] [CommRing A''] (f : A →+* A') (g : A' →+* A'') :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, ← Functor.map_comp, ← Spec.map_comp]
  rfl

end GlobalTheory.EtC.TotFracAway


open GlobalTheory.EtC.TotFracAway in
theorem GlobalTheory.EtC.classVanishesAwayNZD : ∀ (q : ℕ) (R : Type) [CommRing R], IsUnit (q : R) → ∀ (n i : ℤ)
    (z : Ht q (sp R) n i), pull _ (spMap (algebraMap R (FractionRing R))) _ _ z = 0 →
    ∃ g ∈ nonZeroDivisors R, pull _ (spMap (algebraMap R (Localization.Away g))) _ _ z = 0 := by
  intro q R _ hq n i x hx
  have hB1 := (GlobalTheory.T.etaleCohomology_twisted_filtered_colimit_continuity q (diag R) (cocone R) (isColim R) n i).2
  have hq1 : IsUnit (q : Localization.Away (idx1 : Idx R).val) := by
    have := hq.map (algebraMap R (Localization.Away (idx1 : Idx R).val))
    rwa [map_natCast] at this
  have h2 : pull _ (spMap (toFrac (idx1 : Idx R))) _ _
      (pull _ (spMap (algebraMap R (Localization.Away (idx1 : Idx R).val))) _ _ x) = 0 := by
    rw [← pull_comp, ← spMap_comp, toFrac_comp]
    exact hx
  obtain ⟨k, f, hk⟩ := hB1 idx1 (pull _ (spMap (algebraMap R (Localization.Away (idx1 : Idx R).val))) _ _ x) hq1 h2
  have hf : (idx1 : Idx R).val ∣ k.val := leOfHom f
  refine ⟨k.val, k.mem, ?_⟩
  have e : algebraMap R (Localization.Away k.val) =
      (tr hf).comp (algebraMap R (Localization.Away (idx1 : Idx R).val)) := by
    rw [tr_comp]
  rw [e, spMap_comp, pull_comp]
  exact hk
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassVanishesAwayNonZeroDivisorStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.class_vanishes_away_nonZeroDivisor : ∀ (q : ℕ) (R : Type) [CommRing R], IsUnit (q : R) → ∀ (n i : ℤ) (z : Ht q (sp R) n i), pull _ (spMap (algebraMap R (FractionRing R))) _ _ z = 0 → ∃ g ∈ nonZeroDivisors R, pull _ (spMap (algebraMap R (Localization.Away g))) _ _ z = 0 := by
  first | (exact @GlobalTheory.EtC.classVanishesAwayNZD) | (exact GlobalTheory.EtC.classVanishesAwayNZD) | (intros; apply GlobalTheory.EtC.classVanishesAwayNZD  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyVanishesArtinian
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReductionToSiegelDomain
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC.ArtCoh

theorem ht_subsingleton_of_ringEquiv (q : ℕ) {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S) (n i : ℤ)
    [h : Subsingleton (Ht q (sp R) n i)] : Subsingleton (Ht q (sp S) n i) := by
  have hid : spMap (e : R →+* S) ≫ spMap (e.symm : S →+* R) = 𝟙 (sp S) := by
    rw [← Functor.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (e : R →+* S).comp (e.symm : S →+* R) = RingHom.id S := by ext x; simp
    rw [this]
    simp
  constructor
  intro x y
  have hx : pull _ (spMap (e : R →+* S)) _ _ (pull _ (spMap (e.symm : S →+* R)) _ _ x) = x := by
    rw [← pull_comp, hid, pull_id]
  have hy : pull _ (spMap (e : R →+* S)) _ _ (pull _ (spMap (e.symm : S →+* R)) _ _ y) = y := by
    rw [← pull_comp, hid, pull_id]
  rw [← hx, ← hy, Subsingleton.elim (pull _ (spMap (e.symm : S →+* R)) _ _ x)
    (pull _ (spMap (e.symm : S →+* R)) _ _ y)]

theorem ht_subsingleton_prod (q : ℕ) (A B : Type) [CommRing A] [CommRing B] (n i : ℤ)
    [Subsingleton (Ht q (sp A) n i)] [Subsingleton (Ht q (sp B) n i)] : Subsingleton (Ht q (sp (A × B)) n i) := by
  constructor
  intro x y
  exact (GlobalTheory.EtC.ProdCoh.ht_prod_bijective q A B n i).1 (Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _))

theorem ht_subsingleton_of_subsingleton (q : ℕ) (Z : Type) [CommRing Z] [Subsingleton Z] (n i : ℤ) :
    Subsingleton (Ht q (sp Z) n i) := by
  have hfs : RingHom.fst Z Z = RingHom.snd Z Z := by ext x; exact Subsingleton.elim _ _
  constructor
  intro a b
  obtain ⟨x, hx⟩ := (GlobalTheory.EtC.ProdCoh.ht_prod_bijective q Z Z n i).2 (a, b)
  have h1 := congrArg Prod.fst hx
  have h2 := congrArg Prod.snd hx
  simp only at h1 h2
  rw [hfs] at h1
  rw [← h1, ← h2]

theorem ht_subsingleton_pi (q : ℕ) (n i : ℤ) (ι : Type) [Finite ι] : ∀ (R : ι → Type) [∀ j, CommRing (R j)],
    (∀ j, Subsingleton (Ht q (sp (R j)) n i)) → Subsingleton (Ht q (sp (∀ j, R j)) n i) := by
  induction ι using Finite.induction_empty_option with
  | of_equiv e ih =>
    intro R _ hR
    have := ih (fun a => R (e a)) (fun a => hR (e a))
    exact ht_subsingleton_of_ringEquiv q (RingEquiv.piCongrLeft R e) n i
  | h_empty =>
    intro R _ _
    exact ht_subsingleton_of_subsingleton q _ n i
  | h_option ih =>
    intro R _ hR
    have h1 := hR none
    have h2 := ih (fun a => R (some a)) (fun a => hR (some a))
    have := ht_subsingleton_prod q (R none) (∀ a, R (some a)) n i
    exact ht_subsingleton_of_ringEquiv q (RingEquiv.piOptionEquivProd (R := R)).symm n i

theorem ht_subsingleton_artinian : ∀ (q : ℕ) (K : Type) [CommRing K] [IsArtinianRing K] [IsReduced K] (n i : ℤ),
    (∀ M : MaximalSpectrum K, Subsingleton (Ht q (sp (K ⧸ M.asIdeal)) n i)) → Subsingleton (Ht q (sp K) n i) := by
  intro q K _ _ _ n i h
  have := ht_subsingleton_pi q n i (MaximalSpectrum K) (fun M => K ⧸ M.asIdeal) h
  exact ht_subsingleton_of_ringEquiv q (IsArtinianRing.equivPi K).toRingEquiv.symm n i

end GlobalTheory.EtC.ArtCoh
end

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cohomology_vanishes_artinian : ∀ (q : ℕ) (K : Type) [CommRing K] [IsArtinianRing K] [IsReduced K] (n i : ℤ), (∀ M : MaximalSpectrum K, Subsingleton (Ht q (sp (K ⧸ M.asIdeal)) n i)) → Subsingleton (Ht q (sp K) n i) := by
  first | (exact @GlobalTheory.EtC.ArtCoh.ht_subsingleton_artinian) | (exact GlobalTheory.EtC.ArtCoh.ht_subsingleton_artinian) | (intros; apply GlobalTheory.EtC.ArtCoh.ht_subsingleton_artinian <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleMaximalQuotientAlgebraic
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleMaximalQuotientAlgebraic
namespace GlobalTheory

namespace FracAlgEtale

theorem exists_isAlgebraic_ratFunc_of_ringHom (k B : Type) [Field k] [CommRing B]
    [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B] (hB : ¬ IsField B) (f : B)
    (hf : f ≠ 0) (A' : Type) [CommRing A'] [Algebra B A'] [Algebra.Etale B A'] (R : Type)
    [CommRing R] [Algebra A' R] [IsLocalization.Away (algebraMap B A' f) R] (Q : Type)
    [CommRing Q] [Algebra R Q] [IsFractionRing R Q] (K : Type) [Field K] (π : Q →+* K)
    (hπ : Function.Surjective π) :
    ∃ _ : Algebra (RatFunc k) K, Algebra.IsAlgebraic (RatFunc k) K := by
  let ι : R →+* Q := algebraMap R Q
  letI : Algebra B R := ((algebraMap A' R).comp (algebraMap B A')).toAlgebra
  haveI : IsScalarTower B A' R := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : Algebra A' K := (π.comp (ι.comp (algebraMap A' R))).toAlgebra
  letI : Algebra B K := ((algebraMap A' K).comp (algebraMap B A')).toAlgebra
  haveI : IsScalarTower B A' K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let F := FractionRing B

  haveI : Module.Flat A' R := IsLocalization.flat R (Submonoid.powers (algebraMap B A' f))
  haveI : Module.Flat B R := Module.Flat.trans B A' R
  have hreg : ∀ b ∈ nonZeroDivisors B, algebraMap B R b ∈ nonZeroDivisors R := by
    intro b hb
    have hs := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := R) hb
    rw [mem_nonZeroDivisors_iff]
    refine ⟨fun x hx => hs ?_, fun x hx => hs ?_⟩
    · show b • x = b • (0 : R)
      rw [smul_zero, Algebra.smul_def]
      first | exact hx | (rw [mul_comm]; exact hx)
    · show b • x = b • (0 : R)
      rw [smul_zero, Algebra.smul_def]
      first | exact hx | (rw [mul_comm]; exact hx)
  have hunitR : ∀ s ∈ nonZeroDivisors R, IsUnit (π (ι s)) := fun s hs =>
    (IsLocalization.map_units Q (⟨s, hs⟩ : nonZeroDivisors R)).map π
  have hBK : ∀ b : B, algebraMap B K b = π (ι (algebraMap B R b)) := fun b => rfl
  have hunit : ∀ y : nonZeroDivisors B, IsUnit (algebraMap B K y) := fun y => by
    rw [hBK]; exact hunitR _ (hreg _ y.2)
  letI : Algebra F K := (IsLocalization.lift (M := nonZeroDivisors B) (S := F) hunit).toAlgebra
  haveI : IsScalarTower B F K := IsScalarTower.of_algebraMap_eq fun b =>
    (IsLocalization.lift_eq (M := nonZeroDivisors B) (S := F) hunit b).symm

  haveI : Module.Finite F (TensorProduct B F A') := Algebra.FormallyUnramified.finite_of_free F _
  let ψ : TensorProduct B F A' →ₐ[F] K :=
    Algebra.TensorProduct.lift (Algebra.ofId F K) (IsScalarTower.toAlgHom B A' K)
      (fun _ _ => Commute.all _ _)
  have hA : ∀ a : A', IsIntegral F (algebraMap A' K a) := fun a => by
    have h1 := (Algebra.IsIntegral.isIntegral (R := F) ((1 : F) ⊗ₜ[B] a)).map ψ
    simpa [ψ] using h1
  have hAR : ∀ a : A', π (ι (algebraMap A' R a)) = algebraMap A' K a := fun a => rfl
  have hf' : f ∈ nonZeroDivisors B := mem_nonZeroDivisors_of_ne_zero hf
  have hR : ∀ x : R, IsIntegral F (π (ι x)) := by
    intro x
    obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, hx⟩ := IsLocalization.surj (Submonoid.powers (algebraMap B A' f)) x
    have hx' := congrArg (fun y => π (ι y)) hx
    simp only [map_mul, map_pow] at hx'
    have hfK : π (ι (algebraMap A' R (algebraMap B A' f))) = algebraMap F K (algebraMap B F f) := by
      rw [← IsScalarTower.algebraMap_apply B F K]; rfl
    rw [hfK, hAR] at hx'
    have hu : IsUnit (algebraMap F K (algebraMap B F f)) := by
      rw [← IsScalarTower.algebraMap_apply B F K]; exact hunit ⟨f, hf'⟩
    have hne : (algebraMap F K (algebraMap B F f)) ^ n ≠ 0 := pow_ne_zero _ hu.ne_zero
    have : π (ι x) = algebraMap A' K a * ((algebraMap F K (algebraMap B F f)) ^ n)⁻¹ :=
      (eq_mul_inv_iff_mul_eq₀ hne).2 hx'
    rw [this]
    exact (hA a).mul ((isIntegral_algebraMap (R := F) (A := K) (x := algebraMap B F f)).pow n).inv
  have hall : ∀ z : K, IsIntegral F z := by
    intro z
    obtain ⟨q, rfl⟩ := hπ z
    obtain ⟨⟨x, s⟩, hq⟩ := IsLocalization.surj (nonZeroDivisors R) q
    have hq' : π q * π (ι s) = π (ι x) := by
      rw [← map_mul]; exact congrArg π hq
    have : π q = π (ι x) * (π (ι s))⁻¹ := (eq_mul_inv_iff_mul_eq₀ (hunitR _ s.2).ne_zero).2 hq'
    rw [this]
    exact (hR x).mul (hR s).inv
  haveI : Algebra.IsIntegral F K := ⟨hall⟩
  haveI : Algebra.IsAlgebraic F K := inferInstance

  obtain ⟨algRF, hRF⟩ := GlobalTheory.FracAlgDedekind.exists_isAlgebraic_ratFunc k B hB
  letI algK : Algebra (RatFunc k) K := ((algebraMap F K).comp (algebraMap (RatFunc k) F)).toAlgebra
  haveI : IsScalarTower (RatFunc k) F K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact ⟨algK, Algebra.IsAlgebraic.trans (RatFunc k) F K⟩

theorem exists_isAlgebraic_ratFunc_residue : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], ¬ IsField B → ∀ (f : B), f ≠ 0 → ∀ (A' : Type) [CommRing A'] [Algebra B A'] [Algebra.Etale B A'] (M : MaximalSpectrum (FractionRing (Localization.Away (algebraMap B A' f)))), ∃ _ : Algebra (RatFunc k) (FractionRing (Localization.Away (algebraMap B A' f)) ⧸ M.asIdeal), Algebra.IsAlgebraic (RatFunc k) (FractionRing (Localization.Away (algebraMap B A' f)) ⧸ M.asIdeal) := by
  intro k B _ _ _ _ _ _ hB f hf A' _ _ _ M
  haveI : M.asIdeal.IsMaximal := M.isMaximal
  letI : Field (FractionRing (Localization.Away (algebraMap B A' f)) ⧸ M.asIdeal) :=
    Ideal.Quotient.field M.asIdeal
  exact exists_isAlgebraic_ratFunc_of_ringHom k B hB f hf A' (Localization.Away (algebraMap B A' f))
    (FractionRing (Localization.Away (algebraMap B A' f)))
    (FractionRing (Localization.Away (algebraMap B A' f)) ⧸ M.asIdeal) (Ideal.Quotient.mk M.asIdeal)
    (Ideal.Quotient.mk_surjective (I := M.asIdeal))

end FracAlgEtale

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleMaximalQuotientAlgebraicStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_maximal_quotient_algebraic : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], ¬ IsField B → ∀ (f : B), f ≠ 0 → ∀ (A' : Type) [CommRing A'] [Algebra B A'] [Algebra.Etale B A'] (M : MaximalSpectrum (FractionRing (Localization.Away (algebraMap B A' f)))), ∃ _ : Algebra (RatFunc k) (FractionRing (Localization.Away (algebraMap B A' f)) ⧸ M.asIdeal), Algebra.IsAlgebraic (RatFunc k) (FractionRing (Localization.Away (algebraMap B A' f)) ⧸ M.asIdeal) := by
  first | (exact @GlobalTheory.FracAlgEtale.exists_isAlgebraic_ratFunc_residue) | (exact GlobalTheory.FracAlgEtale.exists_isAlgebraic_ratFunc_residue) | (intros; apply GlobalTheory.FracAlgEtale.exists_isAlgebraic_ratFunc_residue  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNbhdAwayOfAddMulEqOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNbhdAwayOfAddMulEqOne
open GlobalTheory.AffineCurveNbhd

namespace GlobalTheory.AffineCurveNbhd

theorem isNbhd_away_of_add_mul_eq_one (B A' : Type) [CommRing B] [CommRing A'] [Algebra B A'] (f : B) (h c : A')
    (hN : IsNbhd B A' f) (hh : h + algebraMap B A' f * c = 1) : IsNbhd B (Localization.Away h) f := by
  set F := algebraMap B A' f with hF
  have hpow : ∀ m : ℕ, F ∣ h ^ m - 1 := by
    intro m
    have h1 : F ∣ h - 1 := ⟨-c, by linear_combination hh⟩
    have := sub_dvd_pow_sub_pow h 1 m
    rw [one_pow] at this
    exact h1.trans this
  have hL : ∀ b : B, algebraMap B (Localization.Away h) b =
      algebraMap A' (Localization.Away h) (algebraMap B A' b) := fun b =>
    IsScalarTower.algebraMap_apply B A' (Localization.Away h) b
  refine ⟨?_, ?_⟩
  · intro a'
    obtain ⟨⟨x, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers h) a'
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
    simp only at hs
    rw [← hn] at hs
    obtain ⟨b, hb⟩ := hN.1 x
    rw [Ideal.mem_span_singleton] at hb
    obtain ⟨d, hd⟩ := hb
    refine ⟨b, ?_⟩
    rw [Ideal.mem_span_singleton, hL b, hL f]
    obtain ⟨u, hu⟩ := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away h) h |>.exists_right_inv
    have hu1 : algebraMap A' (Localization.Away h) F ∣ u - 1 := by
      refine ⟨algebraMap A' (Localization.Away h) c * u, ?_⟩
      have := congrArg (algebraMap A' (Localization.Away h)) hh
      simp only [map_add (f := _), map_mul, map_one] at this
      linear_combination hu - u * this
    have hun : algebraMap A' (Localization.Away h) F ∣ u ^ n - 1 := by
      have := sub_dvd_pow_sub_pow u 1 n
      rw [one_pow] at this
      exact hu1.trans this
    obtain ⟨e, he⟩ := hun
    have ha' : a' = algebraMap A' (Localization.Away h) x * u ^ n := by
      have : a' * (algebraMap A' (Localization.Away h) h * u) ^ n = a' := by rw [hu, one_pow, mul_one]
      rw [← this, mul_pow, ← mul_assoc, ← map_pow, hs]
    refine ⟨algebraMap A' (Localization.Away h) x * e + algebraMap A' (Localization.Away h) d, ?_⟩
    have hx : algebraMap A' (Localization.Away h) x =
        algebraMap A' (Localization.Away h) (algebraMap B A' b) + algebraMap A' (Localization.Away h) F *
          algebraMap A' (Localization.Away h) d := by
      rw [← map_mul, ← map_add (f := _), ← hd]; ring_nf
    rw [ha']
    linear_combination (algebraMap A' (Localization.Away h) x) * he + hx
  · intro a ha
    rw [Ideal.mem_span_singleton, hL a, hL f] at ha
    obtain ⟨y, hy⟩ := ha
    obtain ⟨⟨x, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers h) y
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
    simp only at hs
    have heq : algebraMap A' (Localization.Away h) (algebraMap B A' a * h ^ n) =
        algebraMap A' (Localization.Away h) (F * x) := by
      rw [map_mul, map_mul, hy, ← hs, hn]; ring
    obtain ⟨⟨k, hk⟩, hk'⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers h) _).mp heq
    obtain ⟨m, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp hk
    simp only at hk'
    apply hN.2
    rw [Ideal.mem_span_singleton]
    obtain ⟨g, hg⟩ := hpow (m + n)
    refine ⟨h ^ m * x - g * algebraMap B A' a, ?_⟩
    rw [← hF]
    linear_combination hk' - algebraMap B A' a * hg

end GlobalTheory.AffineCurveNbhd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNbhdAwayOfAddMulEqOneStatement
open GlobalTheory.AffineCurveNbhd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isNbhd_away_of_add_algebraMap_mul_eq_one : ∀ (B A' : Type) [CommRing B] [CommRing A'] [Algebra B A'] (f : B) (h c : A'), IsNbhd B A' f → h + algebraMap B A' f * c = 1 → IsNbhd B (Localization.Away h) f := by
  first | (exact @GlobalTheory.AffineCurveNbhd.isNbhd_away_of_add_mul_eq_one) | (exact GlobalTheory.AffineCurveNbhd.isNbhd_away_of_add_mul_eq_one) | (intros; apply GlobalTheory.AffineCurveNbhd.isNbhd_away_of_add_mul_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvdMulPowEtaleNbhdZeroLocus
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvdMulPowEtaleNbhdZeroLocus
open GlobalTheory.AffineCurveNbhd

noncomputable section

namespace GlobalTheory.LocDivEtale

open IsLocalRing

theorem span_singleton_eq_maximalIdeal_pow {L : Type} [CommRing L] [IsLocalRing L] [IsNoetherianRing L] (π : L)
    (hπ : maximalIdeal L = Ideal.span {π}) (x : L) (hx : x ≠ 0) :
    ∃ n : ℕ, Ideal.span {x} = maximalIdeal L ^ n := by
  classical
  have hK := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal L) (maximalIdeal.isMaximal L).ne_top
  have hex : ∃ n, x ∉ maximalIdeal L ^ (n + 1) := by
    by_contra h
    push_neg at h
    apply hx
    have : x ∈ ⨅ i, maximalIdeal L ^ i := by
      rw [Ideal.mem_iInf]; intro i
      cases i with
      | zero => simp
      | succ k => exact h k
    rw [hK] at this; exact this
  obtain ⟨n, hn, hn'⟩ : ∃ n, x ∉ maximalIdeal L ^ (n + 1) ∧ x ∈ maximalIdeal L ^ n := by
    refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0]; simp
    · have := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
      push_neg at this
      rwa [Nat.sub_add_cancel hpos] at this
  clear hex
  refine ⟨n, ?_⟩
  rw [hπ, Ideal.span_singleton_pow] at hn' hn ⊢
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hn'
  have hyu : IsUnit y := by
    by_contra hy'
    apply hn
    have : y ∈ maximalIdeal L := (mem_maximalIdeal _).2 hy'
    rw [hπ] at this
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 this
    rw [Ideal.mem_span_singleton']
    exact ⟨z, by rw [← hy, ← hz]; ring⟩
  rw [← hy]
  exact Ideal.span_singleton_mul_left_unit hyu _

theorem exists_local_uniformizer (B : Type) [CommRing B] [IsDedekindDomain B] (m : Ideal B) [m.IsPrime]
    (hm0 : m ≠ ⊥) : ∃ π ∈ m, ∀ b ∈ m, ∃ t ∉ m, ∃ c : B, t * b = π * c := by
  haveI : IsDiscreteValuationRing (Localization.AtPrime m) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B hm0 _
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime m)
  obtain ⟨⟨π, t⟩, hπt⟩ := IsLocalization.surj m.primeCompl ϖ
  simp only at hπt
  have hmax := hϖ.maximalIdeal_eq
  refine ⟨π, ?_, ?_⟩
  · rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime m) m, ← hπt]
    exact Ideal.mul_mem_right _ _ (hϖ.not_isUnit)
  · intro b hb
    have hb' : algebraMap B (Localization.AtPrime m) b ∈ maximalIdeal (Localization.AtPrime m) :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime m) m b).2 hb
    rw [hmax] at hb'
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hb'
    obtain ⟨⟨c, u⟩, hcu⟩ := IsLocalization.surj m.primeCompl z
    simp only at hcu
    have heq : algebraMap B (Localization.AtPrime m) (b * (t * u)) =
        algebraMap B (Localization.AtPrime m) (π * c) := by
      rw [map_mul, map_mul, map_mul, ← hz, ← hπt, ← hcu]; ring
    obtain ⟨w, hw⟩ := (IsLocalization.eq_iff_exists m.primeCompl (Localization.AtPrime m)).1 heq
    refine ⟨w * (t * u), ?_, w * c, ?_⟩
    · exact (m.primeCompl).mul_mem w.2 ((m.primeCompl).mul_mem t.2 u.2)
    · rw [show (w : B) * (t * u) * b = w * (b * (t * u)) by ring, hw]; ring

theorem exists_dvd_mul_pow : ∀ (B A' : Type) [CommRing B] [IsDedekindDomain B] [CommRing A'] [Algebra B A']
    [Algebra.Etale B A'] (f : B), f ≠ 0 → IsNbhd B A' f → ∀ a ∈ nonZeroDivisors A', ∀ M : Ideal A', M.IsMaximal →
    algebraMap B A' f ∈ M → ∃ s ∉ M, ∃ N : ℕ, a ∣ s * algebraMap B A' f ^ N := by
  intro B A' _ _ _ _ _ f hf hN a ha M hM hfM
  classical
  set m : Ideal B := M.comap (algebraMap B A') with hm_def
  haveI : m.IsPrime := Ideal.comap_isPrime _ _
  have hfm : f ∈ m := hfM
  have hm0 : m ≠ ⊥ := by
    intro h; apply hf
    rw [h] at hfm; exact (Submodule.mem_bot _).1 hfm
  obtain ⟨π, hπm, hπ⟩ := exists_local_uniformizer B m hm0
  let L := Localization.AtPrime M
  haveI : IsNoetherianRing A' := Algebra.FiniteType.isNoetherianRing B A'
  haveI : IsNoetherianRing L := IsLocalization.isNoetherianRing M.primeCompl L inferInstance
  let φ : B →+* L := (algebraMap A' L).comp (algebraMap B A')
  have hmem : ∀ b ∈ m, φ b ∈ Ideal.span {φ π} := by
    intro b hb
    obtain ⟨t, ht, c, htc⟩ := hπ b hb
    have hu : IsUnit (φ t) := IsLocalization.map_units L (⟨algebraMap B A' t, ht⟩ : M.primeCompl)
    refine (Ideal.unit_mul_mem_iff_mem _ hu).1 ?_
    rw [← map_mul, htc, map_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  have hmax : maximalIdeal L = Ideal.span {φ π} := by
    apply le_antisymm
    · rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_le_iff_le_comap]
      intro x hx
      obtain ⟨b, hb⟩ := hN.1 x
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hb
      have hbm : b ∈ m := by
        show algebraMap B A' b ∈ M
        have : algebraMap B A' b = x - c * algebraMap B A' f := by rw [hc]; ring
        rw [this]; exact M.sub_mem hx (M.mul_mem_left _ hfM)
      have hx' : x = algebraMap B A' b + c * algebraMap B A' f := by rw [hc]; ring
      show algebraMap A' L x ∈ Ideal.span {φ π}
      rw [hx', map_add (f := _), map_mul]
      exact Ideal.add_mem _ (hmem b hbm) (Ideal.mul_mem_left _ _ (hmem f hfm))
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff L M _).2 hπm
  have ha0 : algebraMap A' L a ≠ 0 := by
    intro h
    obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff M.primeCompl L a).1 h
    have : (s : A') = 0 := (mem_nonZeroDivisors_iff.1 ha).2 _ hs
    exact s.2 (this ▸ M.zero_mem)
  obtain ⟨n, hn⟩ := span_singleton_eq_maximalIdeal_pow (φ π) hmax _ ha0
  have hfL : φ f ^ n ∈ Ideal.span {algebraMap A' L a} := by
    rw [hn]; exact Ideal.pow_mem_pow ((IsLocalization.AtPrime.to_map_mem_maximal_iff L M _).2 hfM) n
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hfL
  obtain ⟨⟨y, s⟩, hys⟩ := IsLocalization.surj M.primeCompl z
  simp only at hys
  have heq : algebraMap A' L (algebraMap B A' f ^ n * s) = algebraMap A' L (y * a) := by
    rw [map_mul, map_mul, map_pow, ← hys]
    show φ f ^ n * _ = _
    rw [← hz]; ring
  obtain ⟨w, hw⟩ := (IsLocalization.eq_iff_exists M.primeCompl L).1 heq
  refine ⟨w * s, (M.primeCompl).mul_mem w.2 s.2, n, w * y, ?_⟩
  rw [show (w : A') * s * algebraMap B A' f ^ n = w * (algebraMap B A' f ^ n * s) by ring, hw]; ring

end GlobalTheory.LocDivEtale
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvdMulPowEtaleNbhdZeroLocusStatement
open GlobalTheory.AffineCurveNbhd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dvd_mul_pow_etale_nbhd_zeroLocus : ∀ (B A' : Type) [CommRing B] [IsDedekindDomain B] [CommRing A'] [Algebra B A'] [Algebra.Etale B A'] (f : B), f ≠ 0 → IsNbhd B A' f → ∀ a ∈ nonZeroDivisors A', ∀ M : Ideal A', M.IsMaximal → algebraMap B A' f ∈ M → ∃ s ∉ M, ∃ N : ℕ, a ∣ s * algebraMap B A' f ^ N := by
  first | (exact @GlobalTheory.LocDivEtale.exists_dvd_mul_pow) | (exact GlobalTheory.LocDivEtale.exists_dvd_mul_pow) | (intros; apply GlobalTheory.LocDivEtale.exists_dvd_mul_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HigherDegreeClassDiesOnFinerEtaleNeighbourhood
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GlobalTheory.AffineCurveNbhd

noncomputable section
namespace GlobalTheory.KillFiner

theorem pull_spMap_comp (q : ℕ) {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (ρ : R →+* S) (ψ : S →+* T)
    (n i : ℤ) (z : Ht q (sp R) n i) :
    pull _ (spMap (ψ.comp ρ)) _ _ z = pull _ (spMap ψ) _ _ (pull _ (spMap ρ) _ _ z) := by
  have e : spMap (ψ.comp ρ) = spMap ψ ≫ spMap ρ := by
    show sch.map (Spec.map (CommRingCat.ofHom (ψ.comp ρ))) = sch.map (Spec.map (CommRingCat.ofHom ψ)) ≫ sch.map (Spec.map (CommRingCat.ofHom ρ))
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Functor.map_comp]
  rw [e, pull_comp]

theorem main : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ f : B, f ≠ 0 → ¬ IsUnit f → ∀ (A' : Type) [CommRing A'] [Algebra B A'] [Algebra.Etale B A'], IsNbhd B A' f → ∀ (m i : ℤ), 2 ≤ m → ∀ z : Ht q (sp (Localization.Away (algebraMap B A' f))) m i, ∃ (A'' : Type) (_ : CommRing A'') (_ : Algebra B A'') (_ : Algebra.Etale B A'') (φ : A' →ₐ[B] A''), IsNbhd B A'' f ∧ pull _ (spMap (awayHom φ f)) _ _ z = 0 := by
  intro q _ k B _ _ _ _ _ _ hq f hf hfu A' _ _ _ hN
  set f' : A' := algebraMap B A' f with hf'
  intro m i hm z
  set R := Localization.Away f'
  have hBf : ¬ IsField B := fun hB => hfu (by
    letI := hB.toField; exact isUnit_iff_ne_zero.mpr hf)
  have hqR : IsUnit (q : R) := by
    have := ((hq.map (algebraMap k B)).map (algebraMap B A')).map (algebraMap A' R)
    simpa only [map_natCast] using this

  have hFR : Subsingleton (Ht q (sp (FractionRing R)) m i) := by
    obtain ⟨hArt, hRed⟩ := GlobalTheory.T.fractionRing_away_etale_dedekind_artinian_reduced B f A'
    refine GlobalTheory.T.cohomology_vanishes_artinian q _ m i (fun M => ?_)
    obtain ⟨alg, halg⟩ := GlobalTheory.T.etale_maximal_quotient_algebraic k B hBf f hf A' M
    have hqM : IsUnit (q : FractionRing R ⧸ M.asIdeal) := by
      have := (hqR.map (algebraMap R (FractionRing R))).map (Ideal.Quotient.mk M.asIdeal)
      rwa [map_natCast, map_natCast] at this
    haveI := M.isMaximal
    letI : Field (FractionRing R ⧸ M.asIdeal) := Ideal.Quotient.field _
    exact GlobalTheory.T.etale_cohomology_vanishing_algebraic_over_ratFunc q k (FractionRing R ⧸ M.asIdeal) hqM m i hm

  obtain ⟨g, hg, hz⟩ := GlobalTheory.T.class_vanishes_away_nonZeroDivisor q R hqR m i z (Subsingleton.elim _ _)

  have hf'reg : IsSMulRegular A' f' := by
    have h := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := A') (mem_nonZeroDivisors_of_ne_zero hf)
    intro x y hxy
    apply h
    simpa [Algebra.smul_def, hf'] using hxy
  have hpow : ∀ (N : ℕ) (y : A'), f' ^ N * y = 0 → y = 0 := by
    intro N y hy
    induction N generalizing y with
    | zero => simpa using hy
    | succ N ih =>
      apply ih
      apply hf'reg
      simp only [smul_eq_mul, mul_zero]
      rw [← hy]; ring

  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers f') g
  simp only at hs
  have ha : a ∈ nonZeroDivisors A' := by
    suffices key : ∀ y : A', y * a = 0 → y = 0 from
      mem_nonZeroDivisors_iff.mpr ⟨fun y hy => key y (by rw [mul_comm]; exact hy), key⟩
    intro y hy
    have h1 : algebraMap A' R y * g = 0 := by
      have hsu : IsUnit (algebraMap A' R (s : A')) := IsLocalization.map_units R s
      apply hsu.mul_left_injective
      simp only [zero_mul]
      rw [mul_assoc, hs, ← map_mul, hy, map_zero]
    have h2 : algebraMap A' R y = 0 := (mem_nonZeroDivisors_iff.mp hg).2 _ h1
    rw [IsLocalization.map_eq_zero_iff (Submonoid.powers f')] at h2
    obtain ⟨⟨c, N, rfl⟩, hc⟩ := h2
    exact hpow N y hc

  let J : Ideal A' :=
    { carrier := {x | ∃ N : ℕ, a ∣ x * f' ^ N}
      add_mem' := by
        rintro x y ⟨N₁, h₁⟩ ⟨N₂, h₂⟩
        refine ⟨N₁ + N₂, ?_⟩
        have e : (x + y) * f' ^ (N₁ + N₂) = (x * f' ^ N₁) * f' ^ N₂ + (y * f' ^ N₂) * f' ^ N₁ := by ring
        rw [e]
        exact dvd_add (h₁.mul_right _) (h₂.mul_right _)
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c x ⟨N, h⟩
        refine ⟨N, ?_⟩
        rw [smul_eq_mul, mul_assoc]
        exact h.mul_left c }
  have hJ : J ⊔ Ideal.span {f'} = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    have hfM : f' ∈ M := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    obtain ⟨t, htM, N, hN⟩ := GlobalTheory.T.exists_dvd_mul_pow_etale_nbhd_zeroLocus B A' f hf hN a ha M hM hfM
    exact htM (hle (Ideal.mem_sup_left ⟨N, hN⟩))
  have h1 : (1 : A') ∈ J ⊔ Ideal.span {f'} := by rw [hJ]; trivial
  obtain ⟨h, ⟨N, hhN⟩, y, hy, hhy⟩ := Submodule.mem_sup.mp h1
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hy

  refine ⟨Localization.Away h, inferInstance, inferInstance, inferInstance,
    IsScalarTower.toAlgHom B A' (Localization.Away h), GlobalTheory.T.isNbhd_away_of_add_algebraMap_mul_eq_one B A' f h c hN (by rw [← hhy]; ring), ?_⟩
  set φ := IsScalarTower.toAlgHom B A' (Localization.Away h)
  set S := Localization.Away (algebraMap B (Localization.Away h) f)
  have hcomp : ∀ x : A', awayHom φ f (algebraMap A' R x) = algebraMap _ S (φ x) := fun x =>
    RingHom.congr_fun (awayHom_comp_algebraMap φ f) x
  have hfS : IsUnit (algebraMap _ S (φ f')) := by
    rw [hf', AlgHom.commutes]; exact IsLocalization.Away.algebraMap_isUnit _
  have hhS : IsUnit (algebraMap _ S (φ h)) :=
    (IsLocalization.Away.algebraMap_isUnit h).map (algebraMap _ S)
  have haS : IsUnit (algebraMap _ S (φ a)) := by
    apply isUnit_of_dvd_unit (y := algebraMap _ S (φ (h * f' ^ N)))
    · exact map_dvd _ (map_dvd _ hhN)
    · rw [map_mul, map_pow, map_mul, map_pow]; exact hhS.mul (hfS.pow N)
  have hgS : IsUnit (awayHom φ f g) := by
    have e : awayHom φ f g * awayHom φ f (algebraMap A' R s) = algebraMap _ S (φ a) := by
      rw [← map_mul, hs, hcomp]
    rw [← e] at haS
    exact isUnit_of_mul_isUnit_left haS
  have hfac : (IsLocalization.Away.lift g hgS).comp (algebraMap R (Localization.Away g)) = awayHom φ f :=
    IsLocalization.Away.lift_comp g hgS
  rw [← hfac, pull_spMap_comp, hz, map_zero]
end GlobalTheory.KillFiner
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HigherDegreeClassDiesOnFinerEtaleNeighbourhoodStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GlobalTheory.AffineCurveNbhd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.higherDegree_class_dies_on_finer_etaleNeighbourhood : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ f : B, f ≠ 0 → ¬ IsUnit f → ∀ (A' : Type) [CommRing A'] [Algebra B A'] [Algebra.Etale B A'], IsNbhd B A' f → ∀ (m i : ℤ), 2 ≤ m → ∀ z : Ht q (sp (Localization.Away (algebraMap B A' f))) m i, ∃ (A'' : Type) (_ : CommRing A'') (_ : Algebra B A'') (_ : Algebra.Etale B A'') (φ : A' →ₐ[B] A''), IsNbhd B A'' f ∧ pull _ (spMap (awayHom φ f)) _ _ z = 0 := by
  first | (exact @GlobalTheory.KillFiner.main) | (exact GlobalTheory.KillFiner.main) | (intros; apply GlobalTheory.KillFiner.main <;> assumption)
end
