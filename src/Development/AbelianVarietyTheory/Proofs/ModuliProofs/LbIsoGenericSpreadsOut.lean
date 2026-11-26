module

public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsFgForallOverLbIso
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyPerfectSectionsComplexOfSmoothProj
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecBaseChangeOfPerf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIdCompCancel
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MvPolynomialEqZeroOfEventually
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegelForm
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LbIsoGenericSpreadsOut
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LbIsoGenericSpreadsOut
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

namespace GenericLB

open Spread

private theorem lbIso_pull_iff_lbIso_pull_pull_of_eq_comp {W X Y : Scheme.{0}} {M N : LB X} (hM : M.IsLB) (hN : N.IsLB) {a : Y ⟶ X}
    (j : W ⟶ Y) {a' : W ⟶ X} (ha : a' = j ≫ a) :
    LBIso (M.pull a') (N.pull a') ↔ LBIso ((M.pull a).pull j) ((N.pull a).pull j) := by
  have hM' := LB.isLB_pull hM a'
  have hN' := LB.isLB_pull hN a'
  have hMj := LB.isLB_pull (LB.isLB_pull hM a) j
  have hNj := LB.isLB_pull (LB.isLB_pull hN a) j
  constructor
  · intro h
    exact LBIso.trans hMj hM' hNj (LBIso.symm (lbIso_pull_pull hM j ha))
      (LBIso.trans hM' hN' hNj h (lbIso_pull_pull hN j ha))
  · intro h
    exact LBIso.trans hM' hMj hN' (lbIso_pull_pull hM j ha)
      (LBIso.trans hMj hNj hN' h (LBIso.symm (lbIso_pull_pull hN j ha)))

theorem exists_finset_lbIso {k A : Type} [CommRing k] [CommRing A] [Algebra k A] {B : Scheme.{0}} (pB : B ⟶ Sp k)
    [QuasiCompact pB] [QuasiSeparated pB] {M N : LB B} (hM : M.IsLB) (hN : N.IsLB)
    (H : LBIso (M.pull (pullback.fst pB (spMap (algebraMap k A)))) (N.pull (pullback.fst pB (spMap (algebraMap k A))))) :
    ∃ s : Finset A, LBIso (M.pull (pullback.fst pB (spMap (algebraMap k (Algebra.adjoin k (s : Set A))))))
      (N.pull (pullback.fst pB (spMap (algebraMap k (Algebra.adjoin k (s : Set A)))))) := by
  classical
  obtain ⟨j, g, hg⟩ := exists_lbIso_of_isLimit (bcDiagram pB A)
    (bcCone pB A).π.app (fun {_ _} f => (bcCone pB A).w f) (isLimitBcCone pB A)
    (i := Opposite.op ∅)
    (M.pull (pullback.fst _ _)) (N.pull (pullback.fst _ _))
    (LB.isLB_pull hM _) (LB.isLB_pull hN _)
    ((lbIso_pull_iff_lbIso_pull_pull_of_eq_comp hM hN _ (bcMap_fst pB _).symm).mp H)
  exact ⟨j.unop, (lbIso_pull_iff_lbIso_pull_pull_of_eq_comp hM hN ((bcDiagram pB A).map g) (bcMap_fst pB _).symm).mpr hg⟩

theorem exists_denom {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (s : Finset K) : ∃ f : R, f ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R'), IsUnit (φ f) →
      ∃ ψ : Algebra.adjoin R (s : Set K) →+* R', ψ.comp (algebraMap R _) = φ := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors R) s
  refine ⟨b, nonZeroDivisors.ne_zero b.2, ?_⟩
  intro R' _ φ hφ
  have hb0 : (b : R) ≠ 0 := nonZeroDivisors.ne_zero b.2
  have hunit : IsUnit (algebraMap R K (b : R)) := IsLocalization.map_units K b
  let g0 : Localization.Away (b : R) →+* K := IsLocalization.Away.lift (b : R) hunit
  have hg0 : ∀ r : R, g0 (algebraMap R _ r) = algebraMap R K r := fun r => IsLocalization.lift_eq _ r
  let g : Localization.Away (b : R) →ₐ[R] K := { g0 with commutes' := hg0 }
  have hinj : Function.Injective g := by
    change Function.Injective g0
    refine (IsLocalization.lift_injective_iff _).mpr fun x y => ?_
    exact ((IsLocalization.injective (Localization.Away (b : R))
      (powers_le_nonZeroDivisors_of_noZeroDivisors hb0)).eq_iff).trans
      (IsFractionRing.injective R K).eq_iff.symm
  have hle : Algebra.adjoin R (s : Set K) ≤ g.range := by
    refine Algebra.adjoin_le fun x hx => ?_
    obtain ⟨a, ha⟩ := hb x hx
    refine ⟨IsLocalization.mk' (Localization.Away (b : R)) a ⟨(b : R), Submonoid.mem_powers _⟩, ?_⟩
    show IsLocalization.Away.lift (b : R) hunit _ = x
    unfold IsLocalization.Away.lift
    rw [IsLocalization.lift_mk'_spec]
    rw [ha, Algebra.smul_def]
  refine ⟨((IsLocalization.Away.lift (b : R) hφ).comp
    ((AlgEquiv.ofInjective g hinj).symm : g.range →ₐ[R] Localization.Away (b : R)).toRingHom).comp
    (Subalgebra.inclusion hle).toRingHom, ?_⟩
  ext r
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.commutes]
  exact IsLocalization.lift_eq _ r

end GenericLB

theorem lbIso_generic_spreads_out : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (B : Scheme.{0}) (pB : B ⟶ Sp R) (M N : LB B), QuasiCompact pB → QuasiSeparated pB → M.IsLB → N.IsLB → LBIso (M.pull (pullback.fst pB (spMap (algebraMap R K)))) (N.pull (pullback.fst pB (spMap (algebraMap R K)))) → ∃ f : R, f ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R'), IsUnit (φ f) → LBIso (M.pull (pullback.fst pB (spMap φ))) (N.pull (pullback.fst pB (spMap φ))) := by
  intro R K _ _ _ _ _ _ B pB M N hqc hqs hM hN H
  have := hqc
  have := hqs
  obtain ⟨s, hs⟩ := GenericLB.exists_finset_lbIso pB hM hN H
  obtain ⟨f, hf0, hf⟩ := GenericLB.exists_denom (R := R) s
  refine ⟨f, hf0, fun R' _ φ hφ => ?_⟩
  obtain ⟨ψ, hψ⟩ := hf R' φ hφ
  have key : spMap φ = spMap ψ ≫ spMap (algebraMap R (Algebra.adjoin R (s : Set K))) := by
    rw [spMap_comp_ring, hψ]
  exact Spread.lbIso_pull_comp
    (pullback.lift (pullback.fst pB (spMap φ)) (pullback.snd _ _ ≫ spMap ψ)
      (by rw [pullback.condition, key, Category.assoc]))
    (pullback.lift_fst _ _ _).symm (pullback.lift_fst _ _ _).symm hs

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LbIsoGenericSpreadsOutStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.lbIso_generic_spreads_out_alt : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (B : Scheme.{0}) (pB : B ⟶ Sp R) (M N : LB B), QuasiCompact pB → QuasiSeparated pB → M.IsLB → N.IsLB → LBIso (M.pull (pullback.fst pB (spMap (algebraMap R K)))) (N.pull (pullback.fst pB (spMap (algebraMap R K)))) → ∃ f : R, f ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R'), IsUnit (φ f) → LBIso (M.pull (pullback.fst pB (spMap φ))) (N.pull (pullback.fst pB (spMap φ))) := by
  first | exact @GlobalTheory.lbIso_generic_spreads_out | exact GlobalTheory.lbIso_generic_spreads_out | (intros; apply GlobalTheory.lbIso_generic_spreads_out <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSectionNeZeroFibreOfGenericSection
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSectionNeZeroFibreOfGenericSection
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section
namespace GlobalTheory.GenericSection
open GlobalTheory.AbLaw GlobalTheory.AbLaw.SecBC

theorem exists_ker_ne_zero {R K K' : Type} [CommRing R] [Field K] [Field K'] (g : R →+* K) (g' : R →+* K')
    (hg : Function.Injective g) {a b : ℕ} (D : Matrix (Fin b) (Fin a) R) (v : Fin a → K) (hv : v ≠ 0)
    (h : (D.map g).mulVec v = 0) : ∃ v' : Fin a → K', v' ≠ 0 ∧ (D.map g').mulVec v' = 0 := by
  by_contra hno
  push Not at hno
  have hind : LinearIndependent K' (fun j : Fin a => fun i : Fin b => (D.map g') i j) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    by_contra hc0
    push Not at hc0
    have hc' : c ≠ 0 := fun h0 => by
      obtain ⟨j, hj⟩ := hc0
      exact hj (by rw [h0]; rfl)
    apply hno c hc'
    funext i
    have := congrFun hc i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    rw [Pi.zero_apply] at this
    rw [← this]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  obtain ⟨e, -, he⟩ := GlobalTheory.exists_maximal_minor_ne_zero_of_linearIndependent K' b (Fin a) _ hind
  have hdet : (D.submatrix e id).det ≠ 0 := by
    intro h0
    apply he
    have : (Matrix.of fun k j => (D.map g') (e k) j) = (D.submatrix e id).map g' := by
      ext k j
      rfl
    have hm := RingHom.map_det g' (D.submatrix e id)
    rw [RingHom.mapMatrix_apply] at hm
    rw [this, ← hm, h0, map_zero]
  have hdetK : ((D.map g).submatrix e id).det ≠ 0 := by
    have : (D.map g).submatrix e id = (D.submatrix e id).map g := rfl
    have hm := RingHom.map_det g (D.submatrix e id)
    rw [RingHom.mapMatrix_apply] at hm
    rw [this, ← hm]
    exact fun h0 => hdet (hg (by rw [h0, map_zero]))
  apply hv
  apply Matrix.eq_zero_of_mulVec_eq_zero hdetK
  funext k
  have := congrFun h (e k)
  simpa [Matrix.mulVec, dotProduct, Matrix.submatrix] using this

def zeroSec {X : Scheme.{0}} (M : LB X) : LB.Sec M where
  f := fun _ => 0
  compat := fun _ _ => by rw [map_zero, map_zero, mul_zero]

theorem exists_sec_iff {X X' Y : Scheme.{0}} {L : LB Y} {p : X ⟶ Y} {R R' : Type} [CommRing R] [CommRing R']
    {f : X ⟶ Spec (CommRingCat.of R)} (F : Perf f (L.pull p)) (g : R →+* R') {π : X' ⟶ X}
    {f' : X' ⟶ Spec (CommRingCat.of R')} (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom g)))
    {q : X' ⟶ Y} (e : q = π ≫ p) :
    (∃ (s : (L.pull q).Sec) (j : _), s.f j ≠ 0) ↔ ∃ v : Fin F.a → R', v ≠ 0 ∧ (F.D₀.map g).mulVec v = 0 := by
  subst e
  unfold LB.pull at F ⊢
  let c : R' →+* Γ(X', ⊤) := f'.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom
  obtain ⟨h1, h2, h3⟩ := SecBC.rep_main (F := F) (ψ := fun _ => π ≫ p) (fun _ => rfl) g f' H c (fun _ => rfl)
  have h0 : SecBC.Rep π (fun _ => π ≫ p) F c 0 (zeroSec (L.LinComb (fun _ : PUnit.{1} => π ≫ p) (fun _ => 1))).f := by
    have hs := SecBC.Rep.sum (F := F) (ψ := fun _ => π ≫ p) (c := c) (fun _ => rfl) (I := Empty)
      (w := Empty.elim) (b := Empty.elim) (fun l => l.elim) Empty.elim
    haveI : IsEmpty Empty := Empty.instIsEmpty
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at hs
    exact hs
  constructor
  · rintro ⟨s, j, hs⟩
    obtain ⟨v, hv, hrep⟩ := h2 s
    refine ⟨v, fun hv0 => hs ?_, hv⟩
    subst hv0
    rw [SecBC.Rep.sec_eq (fun _ => rfl) hrep h0]
    rfl
  · rintro ⟨v, hv0, hv⟩
    obtain ⟨s, hs⟩ := h1 v hv
    by_contra hno
    push Not at hno
    apply hv0
    have hz : s = zeroSec _ := SecBC.sec_ext (fun j => hno s j)
    rw [hz] at hs
    exact h3 v 0 (zeroSec (L.LinComb (fun _ : PUnit.{1} => π ≫ p) (fun _ => 1))) hv (Matrix.mulVec_zero _) hs h0

theorem exists_ringHom {S : Scheme.{0}} {R K : Type} [CommRing R] [Field K] (t : Sp R ⟶ S) [IsOpenImmersion t]
    (x : Sp K ⟶ S) (h : Set.range x ⊆ Set.range t) :
    ∃ g : R →+* K, Spec.map (CommRingCat.ofHom g) ≫ t = x := by
  refine ⟨(Spec.preimage (IsOpenImmersion.lift t x h)).hom, ?_⟩
  rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  exact IsOpenImmersion.lift_fac t x h

theorem exists_isPullback {A S T T' : Scheme.{0}} (a : A ⟶ S) (t : T ⟶ S) (u : T' ⟶ T) (x : T' ⟶ S)
    (h : u ≫ t = x) : ∃ π : pullback a x ⟶ pullback a t,
      IsPullback π (pullback.snd a x) (pullback.snd a t) u ∧ pullback.fst a x = π ≫ pullback.fst a t := by
  subst h
  have hc : pullback.fst a (u ≫ t) ≫ a = (pullback.snd a (u ≫ t) ≫ u) ≫ t := by
    rw [pullback.condition, Category.assoc]
  refine ⟨pullback.lift _ _ hc, ?_, (pullback.lift_fst _ _ hc).symm⟩
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ hc) (IsPullback.of_hasPullback a t)
  rw [pullback.lift_fst]
  exact IsPullback.of_hasPullback a (u ≫ t)

theorem exists_sec_ne_zero_of_generic : Out.Laws → ∀ (S : Scheme.{0}) [IsIntegral S] (P : Out.PolAV S) (N : LB P.A.left) (K K' : Type) [Field K] [Field K'] (x : Sp K ⟶ S) (y : Sp K' ⟶ S) (s : (N.pull (pullback.fst P.A.hom x)).Sec), N.IsLB → Set.range x = {genericPoint S} → (∃ j, s.f j ≠ 0) → ∃ (s' : (N.pull (pullback.fst P.A.hom y)).Sec) (j : _), s'.f j ≠ 0 := by
  intro hLaws S _ P N K K' _ _ x y s hN hx hs
  obtain ⟨W, hW, hyW, -⟩ := exists_isAffineOpen_mem_and_subset
    (show y (IsLocalRing.closedPoint K') ∈ (⊤ : S.Opens) from trivial)
  let t : Sp Γ(S, W) ⟶ S := hW.fromSpec
  have hrange : Set.range t = W := hW.range_fromSpec
  have hgen : genericPoint S ∈ (W : Set S) := by
    rw [(genericPoint_spec S).mem_open_set_iff W.isOpen]
    exact ⟨_, trivial, hyW⟩
  have : Nonempty W := ⟨⟨_, hyW⟩⟩
  have hxr : Set.range x ⊆ Set.range t := by
    rw [hx, hrange]
    simpa using hgen
  have hyr : Set.range y ⊆ Set.range t := by
    rintro _ ⟨z, rfl⟩
    rw [hrange, Subsingleton.elim z (IsLocalRing.closedPoint K')]
    exact hyW
  obtain ⟨gx, hgx⟩ := exists_ringHom t x hxr
  obtain ⟨gy, hgy⟩ := exists_ringHom t y hyr
  have hinj : Function.Injective gx := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro r hr
    by_contra hr0
    have hne : (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum Γ(S, W))).Nonempty :=
      ⟨⟨⊥, Ideal.isPrime_bot⟩, by simpa [PrimeSpectrum.mem_basicOpen] using hr0⟩
    have hop : IsOpen (t '' (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum Γ(S, W)))) :=
      t.isOpenEmbedding.isOpenMap _ (PrimeSpectrum.basicOpen r).isOpen
    have hg2 : genericPoint S ∈ t '' (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum Γ(S, W))) := by
      rw [(genericPoint_spec S).mem_open_set_iff hop]
      obtain ⟨q, hq⟩ := hne
      exact ⟨_, trivial, q, hq, rfl⟩
    obtain ⟨q, hq, hqe⟩ := hg2
    have hxpt : x (IsLocalRing.closedPoint K) = genericPoint S := by
      have hm : x (IsLocalRing.closedPoint K) ∈ Set.range x := ⟨_, rfl⟩
      rw [hx] at hm
      exact hm
    have hq2 : q = Spec.map (CommRingCat.ofHom gx) (IsLocalRing.closedPoint K) := by
      apply t.isOpenEmbedding.injective
      rw [hqe, ← hxpt, ← hgx]
      rfl
    rw [hq2] at hq
    apply (PrimeSpectrum.mem_basicOpen _ _).1 hq
    show r ∈ (PrimeSpectrum.comap gx (IsLocalRing.closedPoint K)).asIdeal
    rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, hr]
    exact zero_mem _
  have H0 : IsPullback (pullback.fst P.A.hom t) (pullback.snd P.A.hom t) P.A.hom t :=
    IsPullback.of_hasPullback _ _
  obtain ⟨n, -, m, σ, hlb, hva⟩ := polAV_veryAmpleBy hLaws.polBaseChange S P Γ(S, W) t _ _ _ H0
  have : Smooth P.A.hom := by
    have := P.smoothDim
    exact SmoothOfRelativeDimension.smooth P.g P.A.hom
  have hproj : IsProjBy (pullback.snd P.A.hom t) := ⟨_, hlb, m, σ, hva⟩
  obtain ⟨F⟩ := GlobalTheory.T.nonempty_perfectSectionsComplex_of_smooth_proj Γ(S, W) _ (pullback.snd P.A.hom t) inferInstance hproj
    (N.pull (pullback.fst P.A.hom t)) (LB.isLB_pull hN _)
  obtain ⟨πx, hπx, hex⟩ := exists_isPullback P.A.hom t (Spec.map (CommRingCat.ofHom gx)) x hgx
  obtain ⟨πy, hπy, hey⟩ := exists_isPullback P.A.hom t (Spec.map (CommRingCat.ofHom gy)) y hgy
  obtain ⟨v, hv, hker⟩ := (exists_sec_iff F gx hπx hex).1 ⟨s, hs⟩
  obtain ⟨v', hv', hker'⟩ := exists_ker_ne_zero gx gy hinj F.D₀ v hv hker
  exact (exists_sec_iff F gy hπy hey).2 ⟨v', hv', hker'⟩

end GlobalTheory.GenericSection
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSectionNeZeroFibreOfGenericSectionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_ne_zero_fibre_of_generic_section : Out.Laws → ∀ (S : Scheme.{0}) [IsIntegral S] (P : Out.PolAV S) (N : LB P.A.left) (K K' : Type) [Field K] [Field K'] (x : Sp K ⟶ S) (y : Sp K' ⟶ S) (s : (N.pull (pullback.fst P.A.hom x)).Sec), N.IsLB → Set.range x = {genericPoint S} → (∃ j, s.f j ≠ 0) → ∃ (s' : (N.pull (pullback.fst P.A.hom y)).Sec) (j : _), s'.f j ≠ 0 := by
  first | exact @GlobalTheory.GenericSection.exists_sec_ne_zero_of_generic | exact GlobalTheory.GenericSection.exists_sec_ne_zero_of_generic | (intros; apply GlobalTheory.GenericSection.exists_sec_ne_zero_of_generic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaIdealPrimeAvoidingVariable
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaIdealPrimeAvoidingVariable
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.ZM

namespace GlobalTheory.ThetaPrime

theorem eval₂_smul_of_isHomogeneous {o K I : Type} [CommRing o] [CommRing K] (β : o →+* K)
    (v : I → K) (c : K) {F : MvPolynomial I o} {n : ℕ} (hF : F.IsHomogeneous n) :
    MvPolynomial.eval₂ β (c • v) F = c ^ n * MvPolynomial.eval₂ β v F := by
  classical
  rw [MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have h1 : ∑ i ∈ m.support, m i = n := by
    have := hF (MvPolynomial.mem_support_iff.1 hm)
    rw [← this, Finsupp.weight_apply, Finsupp.sum]
    simp
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, h1]
  ring

theorem exists_homogenisation {o I D : Type} [CommRing o] (a₀ : I) (a : D → I)
    (G : MvPolynomial D o) : ∃ (n : ℕ) (H : MvPolynomial I o),
      ∀ (K : Type) [Field K] (β : o →+* K) (v : I → K), v a₀ ≠ 0 →
        MvPolynomial.eval₂ β v H = v a₀ ^ n * MvPolynomial.eval₂ β (fun i => v (a i) / v a₀) G := by
  induction G using MvPolynomial.induction_on with
  | C c => exact ⟨0, MvPolynomial.C c, fun K _ β v _ => by simp⟩
  | add p q hp hq =>
    obtain ⟨n, H, hH⟩ := hp
    obtain ⟨m, H', hH'⟩ := hq
    refine ⟨n + m, MvPolynomial.X a₀ ^ m * H + MvPolynomial.X a₀ ^ n * H', fun K _ β v hv => ?_⟩
    simp only [MvPolynomial.eval₂_add, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_pow,
      MvPolynomial.eval₂_X, hH K β v hv, hH' K β v hv]
    ring
  | mul_X p i hp =>
    obtain ⟨n, H, hH⟩ := hp
    refine ⟨n + 1, H * MvPolynomial.X (a i), fun K _ β v hv => ?_⟩
    simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, hH K β v hv]
    field_simp
    ring

noncomputable def coneIdeal {o I Z : Type} [CommRing o] (em : o →+* ℂ) (B : Set Z) (θ : Z → I → ℂ) :
    Ideal (MvPolynomial I o) :=
  ⨅ (z : Z) (_ : z ∈ B) (c : ℂ) (_ : c ≠ 0), RingHom.ker (MvPolynomial.eval₂Hom em (c • θ z))

theorem mem_coneIdeal {o I Z : Type} [CommRing o] {em : o →+* ℂ} {B : Set Z} {θ : Z → I → ℂ}
    {F : MvPolynomial I o} : F ∈ coneIdeal em B θ ↔
      ∀ z ∈ B, ∀ c : ℂ, c ≠ 0 → MvPolynomial.eval₂ em (c • θ z) F = 0 := by
  simp [coneIdeal, Ideal.mem_iInf, RingHom.mem_ker]

theorem coneIdeal_isPrime {o I : Type} [CommRing o] [Countable o] [Countable I] (em : o →+* ℂ)
    {d : ℕ} {B : Set (Fin d → ℂ)} (θ : (Fin d → ℂ) → I → ℂ) (ho : IsOpen B)
    (hc : IsPreconnected B) (hn : B.Nonempty) (hd : ∀ a, DifferentiableOn ℂ (fun z => θ z a) B) :
    (coneIdeal em B θ).IsPrime := by
  obtain ⟨z, hz, c, hc0, h⟩ :=
    GlobalTheory.exists_veryGeneral_point_of_holomorphic_family o em I d B θ ho hc hn hd
  have : coneIdeal em B θ = RingHom.ker (MvPolynomial.eval₂Hom em (c • θ z)) := by
    ext F
    rw [mem_coneIdeal, RingHom.mem_ker, MvPolynomial.coe_eval₂Hom]
    exact ⟨fun hF => hF z hz c hc0, h F⟩
  rw [this]
  exact RingHom.ker_isPrime _

theorem exists_ratios {o I : Type} [CommRing o] [Finite I] (em : o →+* ℂ)
    (hem : Function.Injective em) {d : ℕ} {B : Set (Fin d → ℂ)} (θ : (Fin d → ℂ) → I → ℂ)
    (ho : IsOpen B) (hd : ∀ a, DifferentiableOn ℂ (fun z => θ z a) B)
    (hf : ∀ z ∈ B, {z' ∈ B | ∃ c : ℂ, θ z' = c • θ z}.Countable) (a₁ : I)
    (h₁ : MvPolynomial.X a₁ ∉ coneIdeal em B θ) :
    ∃ (a₀ : I) (a : Fin d → I), MvPolynomial.X a₀ ∉ coneIdeal em B θ ∧
      ∀ (K : Type) [Field K] (β : o →+* K) (v : I → K),
        RingHom.ker (MvPolynomial.eval₂Hom β v) = coneIdeal em B θ →
        ∀ G : MvPolynomial (Fin d) o, MvPolynomial.eval₂ β (fun i => v (a i) / v a₀) G = 0 →
          G = 0 := by
  rw [mem_coneIdeal] at h₁
  push Not at h₁
  obtain ⟨z₁, hz₁, c₁, -, h₁⟩ := h₁
  have h₁' : θ z₁ a₁ ≠ 0 := by
    intro h
    apply h₁
    simp [h]
  have hcont : ContinuousAt (fun z => θ z a₁) z₁ :=
    (hd a₁).continuousOn.continuousAt (ho.mem_nhds hz₁)
  have hU : {z | z ∈ B ∧ θ z a₁ ≠ 0} ∈ nhds z₁ :=
    Filter.inter_mem (ho.mem_nhds hz₁) (hcont.eventually_ne h₁')
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU
  have hsub : Metric.ball z₁ ε ⊆ B := fun z hz => (hball hz).1
  obtain ⟨a₀, a, ⟨z₀, hz₀, h₀⟩, hind⟩ := GlobalTheory.CountableFibres.exists_independent_ratios d I
    (Metric.ball z₁ ε) θ Metric.isOpen_ball (convex_ball z₁ ε).isPreconnected
    ⟨z₁, Metric.mem_ball_self hε⟩ (fun a => (hd a).mono hsub)
    (fun z hz => ⟨fun h => (hball hz).2 (by rw [h]; rfl),
      Set.Countable.mono (fun z' hz' => And.intro (hsub hz'.1) hz'.2) (hf z (hsub hz))⟩)
  have hX : MvPolynomial.X a₀ ∉ coneIdeal em B θ := by
    intro h
    have := mem_coneIdeal.1 h z₀ (hsub hz₀) 1 one_ne_zero
    simp [h₀] at this
  refine ⟨a₀, a, hX, fun K _ β v hv G hG => ?_⟩
  have hv₀ : v a₀ ≠ 0 := by
    intro h
    apply hX
    rw [← hv, RingHom.mem_ker]
    simp [h]
  obtain ⟨n, H, hH⟩ := exists_homogenisation a₀ a G
  have hHP : H ∈ coneIdeal em B θ := by
    rw [← hv, RingHom.mem_ker, MvPolynomial.coe_eval₂Hom, hH K β v hv₀, hG, mul_zero]
  have hmap : MvPolynomial.map em G = 0 := by
    refine hind _ fun z hz hz0 => ?_
    have := mem_coneIdeal.1 hHP z (hsub hz) 1 one_ne_zero
    rw [one_smul, hH ℂ em _ hz0] at this
    rw [MvPolynomial.eval_map]
    exact (mul_eq_zero.1 this).resolve_left (pow_ne_zero _ hz0)
  exact MvPolynomial.map_injective em hem (by rw [hmap, map_zero])

theorem countable_of_finiteType (o : Type) [CommRing o] (h : Algebra.FiniteType ℤ o) :
    Countable o := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 h
  have : Countable (MvPolynomial (Fin n) ℤ) := by
    rw [← Cardinal.mk_le_aleph0_iff]
    exact MvPolynomial.cardinalMk_le_max.trans (by simp)
  exact hf.countable

theorem span_range_eq_top {K I : Type} [Field K] {v : I → K} (hv : v ≠ 0) :
    Ideal.span (Set.range v) = ⊤ := by
  obtain ⟨a, ha⟩ := Function.ne_iff.1 hv
  exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨a, rfl⟩) (IsUnit.mk0 _ ha)

theorem exists_prime_independent_ratios : Out.Laws → Out.Laws2 → ∀ (g N' : ℕ) (J : Type) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) (w w' : J) (o : Type) [CommRing o] (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (C : TObj g (N' ^ 2) J b (spMap em) → Prop) (d : ℕ), ArBase em → GoodClass em C Mat κ w w' d → ∀ (p : Ideal (MvPolynomial (Ix g (N' ^ 2)) o)) (a₁ : Ix g (N' ^ 2)), N' ≠ 0 → p.IsPrime → thIdeal em C ≤ p → MvPolynomial.X a₁ ∉ p → ∃ (P : Ideal (MvPolynomial (Ix g (N' ^ 2)) o)) (a₀ : Ix g (N' ^ 2)) (a : Fin d → Ix g (N' ^ 2)), P.IsPrime ∧ thIdeal em C ≤ P ∧ P ≤ p ∧ MvPolynomial.X a₀ ∉ P ∧ ∀ (K : Type) [Field K] (β : o →+* K) (v : Ix g (N' ^ 2) → K), RingHom.ker (MvPolynomial.eval₂Hom β v) = P → ∀ G : MvPolynomial (Fin d) o, MvPolynomial.eval₂ β (fun i => v (a i) / v a₀) G = 0 → G = 0 := by
  intro hL hL2 g N' J Mat κ w w' o _ b em C d hAr hG p a₁ hN hp hle hX
  obtain ⟨-, hft, hem⟩ := hAr
  have : Countable o := countable_of_finiteType o hft
  have : NeZero (N' ^ 2) := ⟨pow_ne_zero _ hN⟩
  obtain ⟨r, B, θ, hfam, hcov⟩ := hG.fam
  have hmem : ∀ F, F ∈ thIdeal em C ↔ ∀ t v, C t → t.HasTh (𝟙 _) v →
      MvPolynomial.eval₂ em v F = 0 := by
    intro F
    simp [thIdeal, Ideal.mem_iInf, RingHom.mem_ker]
  have hinf : (Finset.univ : Finset (Fin r)).inf (fun i => coneIdeal em (B i) (θ i)) ≤ p := by
    refine le_trans (fun F hF => ?_) hle
    rw [hmem]
    intro t v ht hv
    obtain ⟨i, z, hz, hθ⟩ := hcov t ht
    have hFi : F ∈ coneIdeal em (B i) (θ i) :=
      (Finset.inf_le (f := fun i => coneIdeal em (B i) (θ i)) (Finset.mem_univ i)) hF
    have key : ∃ c : ℂ, c ≠ 0 ∧ v = c • θ i z := by
      by_cases h0 : θ i z = 0
      · refine ⟨1, one_ne_zero, ?_⟩
        by_contra hne
        rw [h0, smul_zero] at hne
        obtain ⟨u, hu⟩ := GlobalTheory.hasTh_unique_unit hL hL2 o g N' J b _ _ t ℂ _ v (θ i z) hv hθ
          (span_range_eq_top hne)
        apply hne
        funext a
        have := hu a
        rw [h0] at this
        simpa using this
      · obtain ⟨u, hu⟩ := GlobalTheory.hasTh_unique_unit hL hL2 o g N' J b _ _ t ℂ _ (θ i z) v hθ hv
          (span_range_eq_top h0)
        exact ⟨u, u.ne_zero, funext hu⟩
    obtain ⟨c, hc, rfl⟩ := key
    exact mem_coneIdeal.1 hFi z hz c hc
  obtain ⟨i, -, hi⟩ := hp.inf_le'.1 hinf
  obtain ⟨ho, hc, hd, hz⟩ := hfam i
  have hX' : MvPolynomial.X a₁ ∉ coneIdeal em (B i) (θ i) := fun h => hX (hi h)
  have hn : (B i).Nonempty := by
    by_contra hne
    apply hX'
    rw [mem_coneIdeal]
    intro z hz
    exact absurd ⟨z, hz⟩ hne
  obtain ⟨a₀, a, h₀, hind⟩ := exists_ratios em hem (θ i) ho hd (fun z hz' => (hz z hz').2) a₁ hX'
  refine ⟨_, a₀, a, coneIdeal_isPrime em (θ i) ho hc hn hd, fun F hF => ?_, hi, h₀, hind⟩
  rw [mem_coneIdeal]
  intro z hz' c _
  obtain ⟨t, ht, hθ⟩ := (hz z hz').1
  have hcomp := (GlobalTheory.ZM.ThIdeal.thIdeal_radical_homogeneous_torsionFree o g N' J b em C hem).2.1 F hF
  rw [← MvPolynomial.sum_homogeneousComponent F, MvPolynomial.eval₂_sum]
  refine Finset.sum_eq_zero fun e _ => ?_
  rw [eval₂_smul_of_isHomogeneous em _ c (MvPolynomial.homogeneousComponent_isHomogeneous e F),
    (hmem _).1 (hcomp e) t _ ht hθ, mul_zero]

end GlobalTheory.ThetaPrime
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaIdealPrimeAvoidingVariableStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_ideal_prime_avoiding_variable : Out.Laws → Out.Laws2 → ∀ (g N' : ℕ) (J : Type) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) (w w' : J) (o : Type) [CommRing o] (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (C : TObj g (N' ^ 2) J b (spMap em) → Prop) (d : ℕ), ArBase em → GoodClass em C Mat κ w w' d → ∀ (p : Ideal (MvPolynomial (Ix g (N' ^ 2)) o)) (a₁ : Ix g (N' ^ 2)), N' ≠ 0 → p.IsPrime → thIdeal em C ≤ p → MvPolynomial.X a₁ ∉ p → ∃ (P : Ideal (MvPolynomial (Ix g (N' ^ 2)) o)) (a₀ : Ix g (N' ^ 2)) (a : Fin d → Ix g (N' ^ 2)), P.IsPrime ∧ thIdeal em C ≤ P ∧ P ≤ p ∧ MvPolynomial.X a₀ ∉ P ∧ ∀ (K : Type) [Field K] (β : o →+* K) (v : Ix g (N' ^ 2) → K), RingHom.ker (MvPolynomial.eval₂Hom β v) = P → ∀ G : MvPolynomial (Fin d) o, MvPolynomial.eval₂ β (fun i => v (a i) / v a₀) G = 0 → G = 0 := by
  first | exact @GlobalTheory.ThetaPrime.exists_prime_independent_ratios | exact GlobalTheory.ThetaPrime.exists_prime_independent_ratios | (intros; apply GlobalTheory.ThetaPrime.exists_prime_independent_ratios <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.MemOfMemImage
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.GlueTwoLB

variable {X Y Z : Scheme.{0}}

def stU (f : Z ⟶ Y) (z : Z) : (Y.presheaf.stalk (f z))ˣ →* (Z.presheaf.stalk z)ˣ :=
  Units.map (f.stalkMap z).hom.toMonoidHom

theorem stU_gm (f : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (h : g (f z) ∈ U) (a : Γ(X, U)ˣ) :
    stU f z (gm g (f z) U a) = gm (f ≫ g) z U a := by
  rw [← gm_pull f g z U h]
  apply Units.ext
  rw [gm_val f z (g ⁻¹ᵁ U) h]
  show (f.stalkMap z).hom (gm g (f z) U a).val = _
  rw [gm_val g (f z) U h]
  exact Scheme.Hom.germ_stalkMap_apply f _ z h _

theorem stU_injective (f : Z ⟶ Y) [IsOpenImmersion f] (z : Z) : Function.Injective (stU f z) :=
  Units.map_injective (ConcreteCategory.bijective_of_isIso (f.stalkMap z)).1

theorem stU_gm_id (f : Z ⟶ Y) (z : Z) (U : Y.Opens) (h : f z ∈ U) (a : Γ(Y, U)ˣ) :
    stU f z (gm (𝟙 Y) (f z) U a) = gm f z U a := by
  rw [stU_gm f (𝟙 Y) z U h, Category.comp_id]

theorem exists_push (ψ : Z ⟶ Y) [IsOpenImmersion ψ] (W : Z.Opens) (V : Y.Opens)
    (h : ∀ y ∈ V, ∃ z ∈ W, ψ z = y) (a : Γ(Z, W)ˣ) :
    ∃ b : Γ(Y, V)ˣ, ∀ z : Z, ψ z ∈ V → gm ψ z V b = gm (𝟙 Z) z W a := by
  have hle : V ≤ ψ ''ᵁ W := fun y hy => h y hy
  refine ⟨res hle (Units.map (ψ.appIso W).inv.hom.toMonoidHom a), fun z hz => ?_⟩
  have hW : z ∈ W := by
    obtain ⟨z', hz', e⟩ := h _ hz
    rwa [← ψ.isOpenEmbedding.injective e]
  rw [gm_res ψ z hle hz]
  apply Units.ext
  rw [gm_val ψ z _ (hle hz), gm_val (𝟙 Z) z W hW]
  have e := congrArg (fun q => q.hom a.val) (ψ.appIso_inv_app W)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  exact (congrArg (Z.presheaf.germ (ψ ⁻¹ᵁ ψ ''ᵁ W) z (hle hz)).hom e).trans
    (TopCat.Presheaf.germ_res_apply Z.presheaf _ z (hle hz) _)

theorem iso_self {L : LB X} (hL : L.IsLB) : LBIso L L := by
  refine ⟨⟨fun p => L.g p.1 p.2⟩, fun p q => unit_ext fun y hy => ?_⟩
  refine (gm_res _ y _ hy _).trans (Eq.symm ((map_mul _ _ _).trans ((congrArg₂ (· * ·)
    (gm_div L L (𝟙 X) y p q hy) (gm_res _ y _ hy _)).trans ?_)))
  have a := gm_cocycle hL (𝟙 X) y hy.1.1 hy.2.1 hy.2.2
  have b := gm_cocycle hL (𝟙 X) y hy.1.1 hy.1.2 hy.2.2
  show gm (𝟙 X) y _ (L.g p.1 q.1) * (gm (𝟙 X) y _ (L.g p.2 q.2))⁻¹ * gm (𝟙 X) y _ (L.g q.1 q.2) =
    gm (𝟙 X) y _ (L.g p.1 p.2)
  rw [mul_right_comm, a, ← b, mul_inv_cancel_right]

theorem isLB_of_stalk {L : LB X} (hc : ∀ x, ∃ i, x ∈ L.U i)
    (h : ∀ x i j k, x ∈ L.U i → x ∈ L.U j → x ∈ L.U k →
      gm (𝟙 X) x _ (L.g i j) * gm (𝟙 X) x _ (L.g j k) = gm (𝟙 X) x _ (L.g i k)) : L.IsLB := {
  cover := top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 (hc y)
  g_self i := unit_ext fun y hy => by
    rw [gm_res (𝟙 X) y _ hy, map_one]
    exact mul_eq_left.1 (h y i i i hy hy hy)
  cocycle i j k := unit_ext fun y hy => by
    rw [map_mul, gm_res (𝟙 X) y _ hy, gm_res (𝟙 X) y _ hy, gm_res (𝟙 X) y _ hy]
    exact h y i j k hy.1.1 hy.1.2 hy.2 }

theorem cocycle_descend {L : LB Y} (ψ : Z ⟶ Y) [IsOpenImmersion ψ] (z : Z) {i j k : L.ι}
    (hi : ψ z ∈ L.U i) (hj : ψ z ∈ L.U j) (hk : ψ z ∈ L.U k)
    (h : gm ψ z _ (L.g i j) * gm ψ z _ (L.g j k) = gm ψ z _ (L.g i k)) :
    gm (𝟙 Y) (ψ z) _ (L.g i j) * gm (𝟙 Y) (ψ z) _ (L.g j k) = gm (𝟙 Y) (ψ z) _ (L.g i k) := by
  apply stU_injective ψ z
  rw [map_mul, stU_gm_id ψ z (L.U i ⊓ L.U j) ⟨hi, hj⟩, stU_gm_id ψ z (L.U j ⊓ L.U k) ⟨hj, hk⟩,
    stU_gm_id ψ z (L.U i ⊓ L.U k) ⟨hi, hk⟩, h]

theorem mem_of_mem_image (ψ : Z ⟶ Y) [IsOpenImmersion ψ] {W : Z.Opens} {z : Z} (h : ψ z ∈ ψ ''ᵁ W) : z ∈ W := by
  obtain ⟨z', hz', e⟩ := h
  rwa [← ψ.isOpenEmbedding.injective e]

theorem exists_push_inf (ψ : Z ⟶ Y) [IsOpenImmersion ψ] (W W' : Z.Opens) (a : Γ(Z, W ⊓ W')ˣ) :
    ∃ b : Γ(Y, ψ ''ᵁ W ⊓ ψ ''ᵁ W')ˣ, ∀ z : Z, z ∈ W → z ∈ W' →
      gm ψ z (ψ ''ᵁ W ⊓ ψ ''ᵁ W') b = gm (𝟙 Z) z (W ⊓ W') a := by
  obtain ⟨b, hb⟩ := exists_push ψ (W ⊓ W') (ψ ''ᵁ W ⊓ ψ ''ᵁ W') (by
    rintro y ⟨⟨z, hz, rfl⟩, h'⟩
    exact ⟨z, ⟨hz, mem_of_mem_image ψ h'⟩, rfl⟩) a
  exact ⟨b, fun z h h' => hb z ⟨⟨z, h, rfl⟩, ⟨z, h', rfl⟩⟩⟩

theorem gen_stalk {Y₀ Y₁ Y₂ : Scheme.{0}} {φ₁ : Y₀ ⟶ Y₁} {φ₂ : Y₀ ⟶ Y₂} {L₁ : LB Y₁} {L₂ : LB Y₂}
    {w : LB.Iso (L₁.pull φ₁) (L₂.pull φ₂)} (hw : w.IsGen) (y : Y₀) {i i' : L₁.ι} {k k' : L₂.ι}
    (hi : φ₁ y ∈ L₁.U i) (hi' : φ₁ y ∈ L₁.U i') (hk : φ₂ y ∈ L₂.U k) (hk' : φ₂ y ∈ L₂.U k') :
    gw w (𝟙 Y₀) y k (fun _ => i) = gm φ₂ y _ (L₂.g k k') * (gm φ₁ y _ (L₁.g i i'))⁻¹ *
      gw w (𝟙 Y₀) y k' (fun _ => i') := by
  have := (isGen_iff w).1 hw Y₀ (𝟙 Y₀) y k k' (fun _ => i) (fun _ => i') hk hk' (mem_pull.2 hi) (mem_pull.2 hi')
  rw [gm_pull_g L₁ φ₁ (𝟙 Y₀) y _ _ (mem_pull.2 hi) (mem_pull.2 hi'), Category.id_comp, Category.id_comp] at this
  exact this

def pullChart (L : LB X) (F : Y ⟶ X) : ChartPull (L.pull F) L F where
  idx J := J PUnit.unit
  le _ _ hy := mem_pull.1 hy
  g y J J' hj hj' := (gm_pull_g L F (𝟙 _) y J J' hj hj').trans (by rw [Category.id_comp])

theorem glue : ∀ (Y Y₀ Y₁ Y₂ : Scheme.{0}) (ψ₁ : Y₁ ⟶ Y) (ψ₂ : Y₂ ⟶ Y) (φ₁ : Y₀ ⟶ Y₁) (φ₂ : Y₀ ⟶ Y₂) (L₁ : LB Y₁) (L₂ : LB Y₂), IsOpenImmersion ψ₁ → IsOpenImmersion ψ₂ → IsPullback φ₁ φ₂ ψ₁ ψ₂ → Set.range ψ₁ ∪ Set.range ψ₂ = Set.univ → L₁.IsLB → L₂.IsLB → LBIso (L₁.pull φ₁) (L₂.pull φ₂) → ∃ L : LB Y, L.IsLB ∧ LBIso L₁ (L.pull ψ₁) ∧ LBIso L₂ (L.pull ψ₂) := by
  intro Y Y₀ Y₁ Y₂ ψ₁ ψ₂ φ₁ φ₂ L₁ L₂ o₁ o₂ hp hcov h₁ h₂ ⟨w, hw⟩
  have p₁ : IsOpenImmersion φ₁ := MorphismProperty.of_isPullback hp.flip o₂
  have hpt : ∀ y, ψ₁ (φ₁ y) = ψ₂ (φ₂ y) := fun y => congrArg (fun g => g y) hp.w
  have lift : ∀ y₁ y₂, ψ₁ y₁ = ψ₂ y₂ → ∃ y, φ₁ y = y₁ ∧ φ₂ y = y₂ := fun y₁ y₂ e =>
    Scheme.exists_preimage_of_isPullback hp y₁ y₂ e
  have hsq := hp.w
  choose g₁ hg₁ using fun i j => exists_push_inf ψ₁ _ _ (L₁.g i j)
  choose g₂ hg₂ using fun i j => exists_push_inf ψ₂ _ _ (L₂.g i j)
  have hm : ∀ (k : L₂.ι) (i : L₁.ι), ∃ b : Γ(Y, ψ₂ ''ᵁ L₂.U k ⊓ ψ₁ ''ᵁ L₁.U i)ˣ, ∀ y : Y₀,
      φ₂ y ∈ L₂.U k → φ₁ y ∈ L₁.U i → gm (φ₁ ≫ ψ₁) y _ b = gw w (𝟙 Y₀) y k (fun _ => i) := by
    intro k i
    obtain ⟨b, hb⟩ := exists_push (φ₁ ≫ ψ₁) ((L₂.pull φ₂).U (fun _ => k) ⊓ (L₁.pull φ₁).U (fun _ => i))
      (ψ₂ ''ᵁ L₂.U k ⊓ ψ₁ ''ᵁ L₁.U i) (by
        rintro y ⟨⟨y₂, h₂, rfl⟩, ⟨y₁, h₁, e⟩⟩
        obtain ⟨z, rfl, rfl⟩ := lift y₁ y₂ e
        exact ⟨z, ⟨mem_pull.2 h₂, mem_pull.2 h₁⟩, e⟩) (w.s (fun _ => k, fun _ => i))
    exact ⟨b, fun y hk hi => hb y ⟨⟨_, hk, (hpt y).symm⟩, ⟨_, hi, rfl⟩⟩⟩
  choose m hm using hm
  let L : LB Y :=
    { «ι» := L₁.ι ⊕ L₂.ι
      U := Sum.elim (fun i => ψ₁ ''ᵁ L₁.U i) (fun k => ψ₂ ''ᵁ L₂.U k)
      g := fun p q => match p, q with
        | .inl i, .inl j => g₁ i j
        | .inr k, .inr l => g₂ k l
        | .inr k, .inl i => m k i
        | .inl i, .inr k => (res (le_inf inf_le_right inf_le_left) (m k i))⁻¹ }

  have key : ∀ y : Y₀, ∃ t : L.ι → (Y₀.presheaf.stalk y)ˣ, ∀ p q, ψ₁ (φ₁ y) ∈ L.U p → ψ₁ (φ₁ y) ∈ L.U q →
      gm (φ₁ ≫ ψ₁) y _ (L.g p q) = t p * (t q)⁻¹ := by
    intro y
    obtain ⟨i₀, hi₀⟩ := exists_chart h₁ (φ₁ y)
    have ml : ∀ i, ψ₁ (φ₁ y) ∈ L.U (.inl i) → φ₁ y ∈ L₁.U i := fun i h => mem_of_mem_image ψ₁ h
    have mr : ∀ k, ψ₁ (φ₁ y) ∈ L.U (.inr k) → φ₂ y ∈ L₂.U k := fun k h => mem_of_mem_image ψ₂ (hpt y ▸ h)
    have mix : ∀ k i, φ₂ y ∈ L₂.U k → φ₁ y ∈ L₁.U i → gm (φ₁ ≫ ψ₁) y _ (m k i) =
        gw w (𝟙 Y₀) y k (fun _ => i₀) * (gm φ₁ y _ (L₁.g i i₀))⁻¹ := fun k i hk hi => by
      rw [hm k i y hk hi, gen_stalk hw y hi hi₀ hk hk, gm_self h₂ φ₂ y hk, _root_.one_mul, mul_comm]
    refine ⟨Sum.elim (fun i => gm φ₁ y _ (L₁.g i i₀)) (fun k => gw w (𝟙 Y₀) y k (fun _ => i₀)), ?_⟩
    rintro (i | k) (j | l) hp hq
    · have e := congrArg (stU φ₁ y) (hg₁ i j _ (ml i hp) (ml j hq))
      rw [stU_gm φ₁ ψ₁ y (ψ₁ ''ᵁ L₁.U i ⊓ ψ₁ ''ᵁ L₁.U j) ⟨hp, hq⟩, stU_gm_id φ₁ y (L₁.U i ⊓ L₁.U j) ⟨ml i hp, ml j hq⟩] at e
      refine e.trans ?_
      exact eq_mul_inv_of_mul_eq (gm_cocycle h₁ φ₁ y (ml i hp) (ml j hq) hi₀)
    · refine ((map_inv _ _).trans (congrArg (·⁻¹) ((gm_res (φ₁ ≫ ψ₁) y _
        (show (φ₁ ≫ ψ₁) y ∈ ψ₁ ''ᵁ L₁.U i ⊓ ψ₂ ''ᵁ L₂.U l from ⟨hp, hq⟩) _).trans
        (mix l i (mr l hq) (ml i hp))))).trans ?_
      rw [mul_inv_rev, inv_inv]; rfl
    · exact mix k j (mr k hp) (ml j hq)
    · have e := congrArg (stU φ₂ y) (hg₂ k l _ (mr k hp) (mr l hq))
      rw [stU_gm φ₂ ψ₂ y (ψ₂ ''ᵁ L₂.U k ⊓ ψ₂ ''ᵁ L₂.U l) ⟨⟨_, mr k hp, rfl⟩, ⟨_, mr l hq, rfl⟩⟩,
        stU_gm_id φ₂ y (L₂.U k ⊓ L₂.U l) ⟨mr k hp, mr l hq⟩, ← hsq] at e
      refine e.trans (eq_mul_inv_of_mul_eq ?_)
      have := gen_stalk hw y hi₀ hi₀ (mr k hp) (mr l hq)
      rw [gm_self h₁ φ₁ y hi₀, inv_one, _root_.mul_one] at this
      exact this.symm
  have hL : L.IsLB := by
    refine isLB_of_stalk (fun x => ?_) ?_
    · rcases (hcov.symm ▸ Set.mem_univ x : x ∈ Set.range ψ₁ ∪ Set.range ψ₂) with ⟨y, rfl⟩ | ⟨y, rfl⟩
      · obtain ⟨i, hi⟩ := exists_chart h₁ y
        exact ⟨.inl i, y, hi, rfl⟩
      · obtain ⟨i, hi⟩ := exists_chart h₂ y
        exact ⟨.inr i, y, hi, rfl⟩
    have ov : ∀ x p q r (i : L₁.ι) (k : L₂.ι), x ∈ L.U (.inl i) → x ∈ L.U (.inr k) →
        x ∈ L.U p → x ∈ L.U q → x ∈ L.U r →
        gm (𝟙 Y) x _ (L.g p q) * gm (𝟙 Y) x _ (L.g q r) = gm (𝟙 Y) x _ (L.g p r) := by
      rintro x p q r i k ⟨y₁, -, rfl⟩ ⟨y₂, -, e⟩ hp hq hr
      obtain ⟨y, rfl, rfl⟩ := lift y₁ y₂ e.symm
      obtain ⟨t, ht⟩ := key y
      refine cocycle_descend (φ₁ ≫ ψ₁) y hp hq hr ?_
      rw [ht p q hp hq, ht q r hq hr, ht p r hp hr, _root_.mul_assoc, inv_mul_cancel_left]
    rintro x (i | i) (j | j) (k | k) hi hj hk
    · obtain ⟨y, hy, rfl⟩ := id hi
      have hj' := mem_of_mem_image ψ₁ hj
      have hk' := mem_of_mem_image ψ₁ hk
      refine cocycle_descend ψ₁ y hi hj hk ?_
      exact (congrArg₂ (· * ·) (hg₁ i j y hy hj') (hg₁ j k y hj' hk')).trans
        ((gm_cocycle h₁ (𝟙 _) y hy hj' hk').trans (hg₁ i k y hy hk').symm)
    · exact ov x _ _ _ i k hi hk hi hj hk
    · exact ov x _ _ _ i j hi hj hi hj hk
    · exact ov x _ _ _ i j hi hj hi hj hk
    · exact ov x _ _ _ j i hj hi hi hj hk
    · exact ov x _ _ _ j i hj hi hi hj hk
    · exact ov x _ _ _ k i hk hi hi hj hk
    · obtain ⟨y, hy, rfl⟩ := id hi
      have hj' := mem_of_mem_image ψ₂ hj
      have hk' := mem_of_mem_image ψ₂ hk
      refine cocycle_descend ψ₂ y hi hj hk ?_
      exact (congrArg₂ (· * ·) (hg₂ i j y hy hj') (hg₂ j k y hj' hk')).trans
        ((gm_cocycle h₂ (𝟙 _) y hy hj' hk').trans (hg₂ i k y hy hk').symm)
  let c₁ : ChartPull L₁ L ψ₁ := ⟨Sum.inl, fun i y hy => ⟨y, hy, rfl⟩, fun y i j hi hj => (hg₁ i j y hi hj).symm⟩
  let c₂ : ChartPull L₂ L ψ₂ := ⟨Sum.inr, fun i y hy => ⟨y, hy, rfl⟩, fun y i j hi hj => (hg₂ i j y hi hj).symm⟩
  exact ⟨L, hL, LBIso.chartPull c₁ (pullChart L ψ₁) (iso_self hL),
    LBIso.chartPull c₂ (pullChart L ψ₂) (iso_self hL)⟩

end GlobalTheory.GlueTwoLB
end
end
