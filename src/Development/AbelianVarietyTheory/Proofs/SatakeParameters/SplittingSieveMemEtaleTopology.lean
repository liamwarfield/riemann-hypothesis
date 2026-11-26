module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LeviRep

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FibrePointsLEId
noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.EtC.Tr

def FibrePointsLE {Z X : Scheme.{0}} (f : Z ⟶ X) (n : ℕ) : Prop :=
  ∀ (K : Type) [Field K] (y : Spec (CommRingCat.of K) ⟶ X) (s : Fin (n + 1) → (Spec (CommRingCat.of K) ⟶ Z)),
    (∀ j, s j ≫ f = y) → ¬ Function.Injective s

def diagCompl {Z X : Scheme.{0}} (f : Z ⟶ X) [IsSeparated f] : (pullback f f).Opens :=
  ⟨(Set.range (pullback.diagonal f))ᶜ, (pullback.diagonal f).isClosedEmbedding.isClosed_range.isOpen_compl⟩

def diagComplHom {Z X : Scheme.{0}} (f : Z ⟶ X) [IsSeparated f] : (diagCompl f).toScheme ⟶ Z :=
  (diagCompl f).ι ≫ pullback.snd f f

end GlobalTheory.EtC.Tr
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitsFinitelyOverSchemeOfIsEmptyPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitsFinitelyOverSchemeOfIsEmptyPullback
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.EtC.Tr

theorem splits_of_isEmpty_pullback : ∀ {Z X V : Scheme.{0}} (f : Z ⟶ X) (y : V ⟶ X),
    IsEmpty (pullback f y : Scheme.{0}) → GlobalTheory.EtC.Tr.Splits f y := by
  intro Z X V f y hE
  have hP : IsInitial (pullback f y) := isInitialOfIsEmpty
  refine ⟨0, Fin.elim0, fun j => j.elim0, ?_⟩
  refine ⟨⟨hP.to _, ?_, hP.hom_ext _ _⟩⟩
  apply Sigma.hom_ext
  intro j
  exact j.elim0

end GlobalTheory.EtC.Tr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitsFinitelyOverSchemeOfIsEmptyPullbackStatement
open CategoryTheory Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitsFinitelyOverScheme_of_isEmpty_pullback : ∀ {Z X V : Scheme.{0}} (f : Z ⟶ X) (y : V ⟶ X), IsEmpty (pullback f y : Scheme.{0}) → GlobalTheory.EtC.Tr.Splits f y := by
  first | (exact @GlobalTheory.EtC.Tr.splits_of_isEmpty_pullback) | (exact GlobalTheory.EtC.Tr.splits_of_isEmpty_pullback) | (intros; apply GlobalTheory.EtC.Tr.splits_of_isEmpty_pullback  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFibreFieldPointsCardLEOfIsFiniteIsAffine
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFibreFieldPointsCardLEOfIsFiniteIsAffine
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.EtC.Tr

theorem ringHom_count_bound {A B : Type} [CommRing A] [CommRing B] (g : A →+* B)
    (hg : g.Finite) : ∃ n : ℕ, ∀ (K : Type) [Field K] (ψ : A →+* K) (φ : Fin (n + 1) → (B →+* K)),
      (∀ j, (φ j).comp g = ψ) → ¬ Function.Injective φ := by
  letI := g.toAlgebra
  have hfin : Module.Finite A B := hg
  obtain ⟨S, hS⟩ := hfin.fg_top
  refine ⟨S.card, fun K _ ψ φ hφ hinj => ?_⟩
  let L : (Fin (S.card + 1) → K) →ₗ[K] (S → K) :=
    { toFun := fun c s => ∑ j, c j * φ j (s : B)
      map_add' := by intro c d; funext s; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by intro a c; funext s; simp [Finset.mul_sum, mul_assoc] }
  have hker : LinearMap.ker L ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by simp)
  obtain ⟨c, hc, hc0⟩ := (Submodule.ne_bot_iff _).1 hker
  have hcS : ∀ s ∈ S, ∑ j, c j * φ j s = 0 := by
    intro s hs
    have := congrFun (LinearMap.mem_ker.1 hc) ⟨s, hs⟩
    simpa [L] using this
  have hall : ∀ b : B, ∑ j, c j * φ j b = 0 := by
    intro b
    have hb : b ∈ Submodule.span A (S : Set B) := hS ▸ Submodule.mem_top
    induction hb using Submodule.span_induction with
    | mem x hx => exact hcS x hx
    | zero => simp
    | add x y _ _ hx hy => simp [mul_add, Finset.sum_add_distrib, hx, hy]
    | smul a x _ hx =>
      have e : ∀ j, φ j (a • x) = ψ a * φ j x := by
        intro j
        rw [Algebra.smul_def, map_mul, ← hφ j]
        rfl
      simp only [e]
      calc ∑ j, c j * (ψ a * φ j x) = ψ a * ∑ j, c j * φ j x := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
        _ = 0 := by rw [hx, mul_zero]
  have hli := (linearIndependent_monoidHom B K).comp (fun j => (φ j : B →* K))
    (fun i j h => hinj (RingHom.ext fun b => DFunLike.congr_fun h b))
  have := (Fintype.linearIndependent_iff.1 hli) c (by
    funext b
    simpa [Finset.sum_apply, smul_eq_mul] using hall b)
  exact hc0 (funext this)

theorem finite_fibrePointsLE_of_isAffine : ∀ {Z X : Scheme.{0}} (f : Z ⟶ X) [IsFinite f] [IsAffine X],
    ∃ n, GlobalTheory.EtC.Tr.FibrePointsLE f n := by
  intro Z X f _ _
  haveI := isAffine_of_isAffineHom f
  obtain ⟨n, hn⟩ := ringHom_count_bound f.appTop.hom f.finite_appTop
  refine ⟨n, fun K _ y s hs hinj => ?_⟩
  refine hn K (y.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom
    (fun j => ((s j).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom) (fun j => ?_) ?_
  · rw [← hs j, Scheme.Hom.comp_appTop, Category.assoc]
    simp only [CommRingCat.hom_comp]
  · intro i j h
    apply hinj
    apply ext_of_isAffine
    exact (cancel_mono (Scheme.ΓSpecIso (CommRingCat.of K)).hom).1 (CommRingCat.hom_ext h)

end GlobalTheory.EtC.Tr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFibreFieldPointsCardLEOfIsFiniteIsAffineStatement
open CategoryTheory Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fibreFieldPointsCardLE_of_isFinite_isAffine : ∀ {Z X : Scheme.{0}} (f : Z ⟶ X) [IsFinite f] [IsAffine X], ∃ n, GlobalTheory.EtC.Tr.FibrePointsLE f n := by
  first | (exact @GlobalTheory.EtC.Tr.finite_fibrePointsLE_of_isAffine) | (exact GlobalTheory.EtC.Tr.finite_fibrePointsLE_of_isAffine) | (intros; apply GlobalTheory.EtC.Tr.finite_fibrePointsLE_of_isAffine  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FibreFieldPointsCardLEDiagonalComplementSecondPr
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FibreFieldPointsCardLEDiagonalComplementSecondPr
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.EtC.Tr

theorem fibrePointsLE_diagComplHom {Z X : Scheme.{0}} (f : Z ⟶ X) [IsFinite f] [Etale f] (n : ℕ)
    (h : FibrePointsLE f (n + 1)) : FibrePointsLE (diagComplHom f) n := by
  intro K _ y s hs hinj
  set t : Fin (n + 1) → (Spec (CommRingCat.of K) ⟶ Z) := fun j => s j ≫ (diagCompl f).ι ≫ pullback.fst f f
    with ht
  have hsnd : ∀ j, s j ≫ (diagCompl f).ι ≫ pullback.snd f f = y := fun j => by
    simpa [diagComplHom] using hs j
  have htf : ∀ j, t j ≫ f = y ≫ f := fun j => by
    simp only [ht, Category.assoc, pullback.condition]
    rw [← hsnd j]
    simp only [Category.assoc]
  have hne : ∀ j, t j ≠ y := by
    intro j hj
    have heq : s j ≫ (diagCompl f).ι = y ≫ pullback.diagonal f := by
      apply pullback.hom_ext
      · simp [← hj, ht]
      · simp [hsnd j]
    obtain ⟨x⟩ : Nonempty (Spec (CommRingCat.of K)) := inferInstance
    have h1 : (s j ≫ (diagCompl f).ι).base x ∈ diagCompl f := by
      rw [← SetLike.mem_coe, ← Scheme.Opens.range_ι]
      exact ⟨_, rfl⟩
    rw [heq] at h1
    exact h1 ⟨_, rfl⟩
  apply h K (y ≫ f) (Fin.cons y t)
  · intro j
    cases j using Fin.cases with
    | zero => simp
    | succ j => simpa using htf j
  · intro i j hij
    cases i using Fin.cases <;> cases j using Fin.cases
    · rfl
    · simp only [Fin.cons_zero, Fin.cons_succ] at hij; exact absurd hij.symm (hne _)
    · simp only [Fin.cons_zero, Fin.cons_succ] at hij; exact absurd hij (hne _)
    · rename_i i j
      simp only [Fin.cons_succ] at hij
      congr 1
      apply hinj
      rw [← cancel_mono (diagCompl f).ι]
      apply pullback.hom_ext
      · simpa [ht] using hij
      · simp [hsnd i, hsnd j]

end GlobalTheory.EtC.Tr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FibreFieldPointsCardLEDiagonalComplementSecondPrStatement
open CategoryTheory Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibreFieldPointsCardLE_diagonalComplementSecondProjection : ∀ {Z X : Scheme.{0}} (f : Z ⟶ X) [IsFinite f] [Etale f] (n : ℕ), GlobalTheory.EtC.Tr.FibrePointsLE f (n + 1) → GlobalTheory.EtC.Tr.FibrePointsLE (GlobalTheory.EtC.Tr.diagComplHom f) n := by
  first | (exact @GlobalTheory.EtC.Tr.fibrePointsLE_diagComplHom) | (exact GlobalTheory.EtC.Tr.fibrePointsLE_diagComplHom) | (intros; apply GlobalTheory.EtC.Tr.fibrePointsLE_diagComplHom  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemEtaleTopologyOfPullbackFiniteEtale
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemEtaleTopologyOfPullbackFiniteEtale
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.EtC.Tr

theorem mem_etaleTopology_of_pullback_finite : ∀ {Z X : Scheme.{0}} (f : Z ⟶ X) [IsFinite f] [Etale f] (T : Sieve X), T.pullback f ∈ Scheme.etaleTopology Z → (∀ {V : Scheme.{0}} (v : V ⟶ X), IsEmpty (pullback f v : Scheme.{0}) → T v) → T ∈ Scheme.etaleTopology X := by
  intro Z X f _ _ T hT hE
  let U : X.Opens := ⟨(Set.range f.base)ᶜ, f.isClosedMap.isClosed_range.isOpen_compl⟩
  have hU : IsEmpty (pullback f U.ι : Scheme.{0}) := by
    refine ⟨fun p => ?_⟩
    have h1 : (pullback.snd f U.ι ≫ U.ι).base p = (pullback.fst f U.ι ≫ f).base p := by
      rw [pullback.condition]
    have h2 : (pullback.snd f U.ι ≫ U.ι).base p ∈ U := by
      rw [Scheme.Hom.comp_base, TopCat.comp_app]
      have hr := U.range_ι
      exact (Set.ext_iff.1 hr _).1 ⟨_, rfl⟩
    rw [h1, Scheme.Hom.comp_base, TopCat.comp_app] at h2
    exact h2 ⟨_, rfl⟩
  have hTU : T U.ι := hE U.ι hU
  let V : Bool → Scheme.{0} := fun b => Bool.rec U.toScheme Z b
  let j : ∀ b, V b ⟶ X := fun b => match b with
    | true => f
    | false => U.ι
  have hmem : Presieve.ofArrows V j ∈ Scheme.etalePrecoverage X := by
    refine (Scheme.ofArrows_mem_precoverage_iff _).2 ⟨fun x => ?_, fun b => ?_⟩
    · by_cases hx : x ∈ Set.range f.base
      · obtain ⟨z, rfl⟩ := hx
        exact ⟨true, z, rfl⟩
      · exact ⟨false, ⟨x, hx⟩, rfl⟩
    · cases b
      · change Etale U.ι
        infer_instance
      · change Etale f
        infer_instance
  refine Scheme.etaleTopology.transitive (Precoverage.generate_mem_toGrothendieck hmem) _ ?_
  rintro W g ⟨Y, h, k, ⟨b⟩, rfl⟩
  rw [Sieve.pullback_comp]
  refine Scheme.etaleTopology.pullback_stable h ?_
  cases b
  · change T.pullback U.ι ∈ _
    rw [Sieve.pullback_eq_top_of_mem _ hTU]
    exact Scheme.etaleTopology.top_mem _
  · exact hT

end GlobalTheory.EtC.Tr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemEtaleTopologyOfPullbackFiniteEtaleStatement
open CategoryTheory Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_etaleTopology_of_pullback_finite_etale : ∀ {Z X : Scheme.{0}} (f : Z ⟶ X) [IsFinite f] [Etale f] (T : Sieve X), T.pullback f ∈ Scheme.etaleTopology Z → (∀ {V : Scheme.{0}} (v : V ⟶ X), IsEmpty (pullback f v : Scheme.{0}) → T v) → T ∈ Scheme.etaleTopology X := by
  first | (exact @GlobalTheory.EtC.Tr.mem_etaleTopology_of_pullback_finite) | (exact GlobalTheory.EtC.Tr.mem_etaleTopology_of_pullback_finite) | (intros; apply GlobalTheory.EtC.Tr.mem_etaleTopology_of_pullback_finite  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsEmptyOfFibreFieldPointsCardLEZero
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsEmptyOfFibreFieldPointsCardLEZero
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.EtC.Tr

theorem isEmpty_of_fibrePointsLE_zero {Z X : Scheme.{0}} (f : Z ⟶ X) (h : FibrePointsLE f 0) :
    IsEmpty Z := by
  refine ⟨fun z => ?_⟩
  exact h (Z.residueField z) (Z.fromSpecResidueField z ≫ f) (fun _ => Z.fromSpecResidueField z)
    (fun _ => rfl) (fun a b _ => Fin.subsingleton_one.elim a b)

end GlobalTheory.EtC.Tr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsEmptyOfFibreFieldPointsCardLEZeroStatement
open CategoryTheory Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isEmpty_of_fibreFieldPointsCardLE_zero : ∀ {Z X : Scheme.{0}} (f : Z ⟶ X), GlobalTheory.EtC.Tr.FibrePointsLE f 0 → IsEmpty Z := by
  first | (exact @GlobalTheory.EtC.Tr.isEmpty_of_fibrePointsLE_zero) | (exact GlobalTheory.EtC.Tr.isEmpty_of_fibrePointsLE_zero) | (intros; apply GlobalTheory.EtC.Tr.isEmpty_of_fibrePointsLE_zero  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DiagonalComplementSecondProjectionIsFiniteEtale
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DiagonalComplementSecondProjectionIsFiniteEtale
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.EtC.Tr

theorem diagComplHom_isFinite_etale : ∀ {Z X : Scheme.{0}} (f : Z ⟶ X) [IsFinite f] [Etale f],
    IsFinite (GlobalTheory.EtC.Tr.diagComplHom f) ∧ Etale (GlobalTheory.EtC.Tr.diagComplHom f) := by
  intro Z X f _ _
  have hopen : IsOpen (Set.range (pullback.diagonal f)) :=
    (pullback.diagonal f).isOpenEmbedding.isOpen_range
  have hcl : IsClosedImmersion (diagCompl f).ι :=
    IsClosedImmersion.of_isPreimmersion _ (by
      rw [Scheme.Opens.range_ι]
      exact hopen.isClosed_compl)
  unfold diagComplHom
  exact ⟨inferInstance, inferInstance⟩

end GlobalTheory.EtC.Tr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DiagonalComplementSecondProjectionIsFiniteEtaleStatement
open CategoryTheory Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonalComplementSecondProjection_isFinite_etale : ∀ {Z X : Scheme.{0}} (f : Z ⟶ X) [IsFinite f] [Etale f], IsFinite (GlobalTheory.EtC.Tr.diagComplHom f) ∧ Etale (GlobalTheory.EtC.Tr.diagComplHom f) := by
  first | (exact @GlobalTheory.EtC.Tr.diagComplHom_isFinite_etale) | (exact GlobalTheory.EtC.Tr.diagComplHom_isFinite_etale) | (intros; apply GlobalTheory.EtC.Tr.diagComplHom_isFinite_etale  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitsPullbackSndOfSplitsDiagonalComplement
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitsPullbackSndOfSplitsDiagonalComplement
open CategoryTheory Limits AlgebraicGeometry

noncomputable section
namespace GlobalTheory.EtC.Tr

theorem splits_pullbackSnd_of_splits_diagComplHom {Z X V : Scheme.{0}} (f : Z ⟶ X) [IsFinite f] [Etale f]
    (v : V ⟶ Z) (h : Splits (diagComplHom f) v) : Splits (pullback.snd f f) v := by
  obtain ⟨m, s, hs, hiso⟩ := h
  have hδs : pullback.diagonal f ≫ pullback.snd f f = 𝟙 Z := pullback.diagonal_snd f
  let t : Fin (m + 1) → (V ⟶ pullback f f) :=
    Fin.cons (α := fun _ => V ⟶ pullback f f) (v ≫ pullback.diagonal f) (fun j => s j ≫ (diagCompl f).ι)
  have ht0 : t 0 = v ≫ pullback.diagonal f := rfl
  have hts : ∀ k : Fin m, t k.succ = s k ≫ (diagCompl f).ι := fun k => rfl
  have ht : ∀ j, t j ≫ pullback.snd f f = v := by
    intro j
    induction j using Fin.cases with
    | zero => rw [ht0, Category.assoc, hδs, Category.comp_id]
    | succ k => rw [hts, Category.assoc]; exact hs k
  refine ⟨m + 1, t, ht, ?_⟩
  let d : Fin m → (V ⟶ pullback (diagComplHom f) v) :=
    fun j => pullback.lift (s j) (𝟙 V) (by rw [hs j, Category.id_comp])
  let Φ : ∐ (fun _ : Fin m => V) ⟶ pullback (diagComplHom f) v := Sigma.desc d
  have hΦ : IsIso Φ := hiso
  have hdΦ : ∀ k, d k = Sigma.ι (fun _ : Fin m => V) k ≫ Φ := fun k => (Sigma.ι_desc _ _).symm
  let eU : pullback (diagComplHom f) v ⟶ pullback (pullback.snd f f) v :=
    pullback.map (diagComplHom f) v (pullback.snd f f) v (diagCompl f).ι (𝟙 V) (𝟙 Z)
      (by simp [diagComplHom]) (by simp)
  let eD : pullback (pullback.diagonal f ≫ pullback.snd f f) v ⟶ pullback (pullback.snd f f) v :=
    pullback.map _ v (pullback.snd f f) v (pullback.diagonal f) (𝟙 V) (𝟙 Z) (by simp) (by simp)
  let l : V ⟶ pullback (pullback.diagonal f ≫ pullback.snd f f) v :=
    pullback.lift v (𝟙 V) (by rw [hδs]; simp)
  have hl : IsIso l := by
    have h1 : IsIso (pullback.diagonal f ≫ pullback.snd f f) := by rw [hδs]; infer_instance
    have h2 : l ≫ pullback.snd _ _ = 𝟙 V := pullback.lift_snd _ _ _
    have h3 : IsIso (l ≫ pullback.snd (pullback.diagonal f ≫ pullback.snd f f) v) := by
      rw [h2]; infer_instance
    exact IsIso.of_isIso_comp_right l (pullback.snd _ _)
  let g : Fin (m + 1) → (V ⟶ pullback (pullback.snd f f) v) :=
    Fin.cons (α := fun _ => V ⟶ pullback (pullback.snd f f) v) (l ≫ eD) (fun k => d k ≫ eU)
  have hg : (Sigma.desc (fun j => pullback.lift (t j) (𝟙 V) (by rw [ht j, Category.id_comp])) :
      ∐ (fun _ : Fin (m + 1) => V) ⟶ pullback (pullback.snd f f) v) = Sigma.desc g := by
    refine Sigma.hom_ext _ _ (fun j => ?_)
    rw [Sigma.ι_desc, Sigma.ι_desc]
    induction j using Fin.cases with
    | zero =>
      apply pullback.hom_ext
      · rw [pullback.lift_fst]
        show t 0 = (l ≫ eD) ≫ _
        rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst, ht0]
      · rw [pullback.lift_snd]
        show 𝟙 V = (l ≫ eD) ≫ _
        rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd, Category.id_comp]
    | succ k =>
      apply pullback.hom_ext
      · rw [pullback.lift_fst]
        show t k.succ = (d k ≫ eU) ≫ _
        rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst, hts]
      · rw [pullback.lift_snd]
        show 𝟙 V = (d k ≫ eU) ≫ _
        rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd, Category.id_comp]
  rw [hg]
  have hΦi : IsOpenImmersion Φ := inferInstance
  have hι : ∀ k, IsOpenImmersion (Sigma.ι (fun _ : Fin m => V) k) := fun k => inferInstance
  have hδo : IsOpenImmersion (pullback.diagonal f) := inferInstance
  have hUo : IsOpenImmersion eU := inferInstance
  have hDo : IsOpenImmersion eD := inferInstance
  have hgo : ∀ j, IsOpenImmersion (g j) := by
    intro j
    induction j using Fin.cases with
    | zero => show IsOpenImmersion (l ≫ eD); infer_instance
    | succ k => show IsOpenImmersion (d k ≫ eU); rw [hdΦ]; infer_instance
  have hgπ' : ∀ j, g j ≫ pullback.fst (pullback.snd f f) v = t j := by
    intro j
    induction j using Fin.cases with
    | zero =>
      show (l ≫ eD) ≫ _ = t 0
      rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst, ht0]
    | succ k =>
      show (d k ≫ eU) ≫ _ = t k.succ
      rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst, hts]
  have hgπ : ∀ j y, pullback.fst (pullback.snd f f) v (g j y) = t j y := by
    intro j y
    rw [← Scheme.Hom.comp_apply, hgπ']
  have hsep : ∀ a b, pullback.diagonal f a ≠ (diagCompl f).ι b := by
    intro a b hab
    have hb : (diagCompl f).ι b ∈ Set.range (diagCompl f).ι := ⟨b, rfl⟩
    rw [Scheme.Opens.range_ι] at hb
    exact hb ⟨a, hab⟩
  rw [isIso_iff_isOpenImmersion_and_surjective]
  refine ⟨isOpenImmersion_sigmaDesc _ g ?_, ⟨fun p => ?_⟩⟩
  · intro i j hij
    rw [Function.onFun, Set.disjoint_left]
    rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
    have hπ := congrArg (pullback.fst (pullback.snd f f) v) hy
    rw [hgπ, hgπ] at hπ
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact hij rfl
      | succ k =>
        rw [ht0, hts, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hπ
        exact hsep _ _ hπ.symm
    | succ k =>
      induction j using Fin.cases with
      | zero =>
        rw [ht0, hts, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hπ
        exact hsep _ _ hπ
      | succ k' =>
        have h1 : d k' y = d k x := by
          apply eU.isOpenEmbedding.injective
          have hy' : (d k' ≫ eU) y = (d k ≫ eU) x := hy
          rwa [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hy'
        rw [hdΦ, hdΦ, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at h1
        have h2 := (sigmaι_eq_iff _ _ _ _ _).mp (Φ.isOpenEmbedding.injective h1)
        exact hij (by rw [(Sigma.mk.inj_iff.mp h2).1])
  · by_cases hp : pullback.fst (pullback.snd f f) v p ∈ Set.range (pullback.diagonal f)
    · have hpD : p ∈ Set.range eD := by
        rw [Scheme.Pullback.range_map]
        exact ⟨hp, ⟨pullback.snd (pullback.snd f f) v p, rfl⟩⟩
      obtain ⟨q, rfl⟩ := hpD
      refine ⟨Sigma.ι (fun _ : Fin (m + 1) => V) 0 (inv l q), ?_⟩
      rw [← Scheme.Hom.comp_apply, Sigma.ι_desc]
      show (l ≫ eD) (inv l q) = eD q
      rw [Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply (inv l), IsIso.inv_hom_id]
      rfl
    · have hpU : p ∈ Set.range eU := by
        rw [Scheme.Pullback.range_map]
        refine ⟨?_, ⟨pullback.snd (pullback.snd f f) v p, rfl⟩⟩
        rw [Set.mem_preimage, Scheme.Opens.range_ι]
        exact hp
      obtain ⟨q, rfl⟩ := hpU
      obtain ⟨⟨k, x⟩, hkx⟩ := (sigmaMk (fun _ : Fin m => V)).surjective (inv Φ q)
      rw [sigmaMk_mk] at hkx
      refine ⟨Sigma.ι (fun _ : Fin (m + 1) => V) k.succ x, ?_⟩
      rw [← Scheme.Hom.comp_apply, Sigma.ι_desc]
      show (d k ≫ eU) x = eU q
      rw [hdΦ, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hkx, ← Scheme.Hom.comp_apply (inv Φ),
        IsIso.inv_hom_id]
      rfl

end GlobalTheory.EtC.Tr
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitsPullbackSndOfSplitsDiagonalComplementStatement
open CategoryTheory Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splits_pullbackSnd_of_splits_diagonalComplement : ∀ {Z X V : Scheme.{0}} (f : Z ⟶ X) [IsFinite f] [Etale f] (v : V ⟶ Z), GlobalTheory.EtC.Tr.Splits (GlobalTheory.EtC.Tr.diagComplHom f) v → GlobalTheory.EtC.Tr.Splits (pullback.snd f f) v := by
  first | exact @GlobalTheory.EtC.Tr.splits_pullbackSnd_of_splits_diagComplHom | exact GlobalTheory.EtC.Tr.splits_pullbackSnd_of_splits_diagComplHom | (intros; apply GlobalTheory.EtC.Tr.splits_pullbackSnd_of_splits_diagComplHom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitsFinitelyOverSchemeOfPullbackSnd
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitsFinitelyOverSchemeOfPullbackSnd
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.EtC.Tr

theorem splits_of_splits_pullback_snd {Z X S V : Scheme.{0}} (f : Z ⟶ X) (x : S ⟶ X) (v : V ⟶ S) :
    GlobalTheory.EtC.Tr.Splits (pullback.snd f x) v → GlobalTheory.EtC.Tr.Splits f (v ≫ x) := by
  rintro ⟨m, s, hs, hiso⟩
  refine ⟨m, fun j => s j ≫ pullback.fst f x, fun j => ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hs j]
  · have heq : (Sigma.desc (fun j => pullback.lift (s j ≫ pullback.fst f x) (𝟙 V)
        (by rw [Category.assoc, pullback.condition, ← Category.assoc, hs j, Category.id_comp])) :
          ∐ (fun _ : Fin m => V) ⟶ pullback f (v ≫ x)) =
        (Sigma.desc (fun j => pullback.lift (s j) (𝟙 V) (by rw [hs j, Category.id_comp])) :
          ∐ (fun _ : Fin m => V) ⟶ pullback (pullback.snd f x) v) ≫
          (pullbackLeftPullbackSndIso f x v).hom := by
      apply Sigma.hom_ext
      intro j
      rw [Sigma.ι_desc, Sigma.ι_desc_assoc]
      apply pullback.hom_ext
      · rw [pullback.lift_fst, Category.assoc, pullbackLeftPullbackSndIso_hom_fst, pullback.lift_fst_assoc]
      · rw [pullback.lift_snd, Category.assoc, pullbackLeftPullbackSndIso_hom_snd, pullback.lift_snd]
    rw [heq]
    infer_instance

end GlobalTheory.EtC.Tr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitsFinitelyOverSchemeOfPullbackSndStatement
open CategoryTheory Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitsFinitelyOverScheme_of_pullback_snd : ∀ {Z X S V : Scheme.{0}} (f : Z ⟶ X) (x : S ⟶ X) (v : V ⟶ S), GlobalTheory.EtC.Tr.Splits (pullback.snd f x) v → GlobalTheory.EtC.Tr.Splits f (v ≫ x) := by
  first | (exact @GlobalTheory.EtC.Tr.splits_of_splits_pullback_snd) | (exact GlobalTheory.EtC.Tr.splits_of_splits_pullback_snd) | (intros; apply GlobalTheory.EtC.Tr.splits_of_splits_pullback_snd  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplittingSieveMemEtaleTopology
noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.EtC.Tr

theorem splitSieve_mem_of_fibrePointsLE : ∀ (n : ℕ) {Z X : Scheme.{0}} (f : Z ⟶ X) [IsFinite f] [Etale f],
    FibrePointsLE f n → splitSieve f (𝟙 X) ∈ Scheme.etaleTopology X := by
  intro n
  induction n with
  | zero =>
    intro Z X f _ _ h
    have : IsEmpty Z := GlobalTheory.T.isEmpty_of_fibreFieldPointsCardLE_zero f h
    have hs : Splits f (𝟙 X ≫ 𝟙 X) := GlobalTheory.T.splitsFinitelyOverScheme_of_isEmpty_pullback f _ (Function.isEmpty (pullback.fst f (𝟙 X ≫ 𝟙 X)))
    have hmem : splitSieve f (𝟙 X) (𝟙 X) := ⟨X, 𝟙 X, 𝟙 X, hs, Category.id_comp _⟩
    rw [Sieve.id_mem_iff_eq_top] at hmem
    rw [hmem]; exact (Scheme.etaleTopology).top_mem X
  | succ n ih =>
    intro Z X f _ _ h
    obtain ⟨hfin, het⟩ := GlobalTheory.T.diagonalComplementSecondProjection_isFinite_etale f
    have hg := ih (diagComplHom f) (GlobalTheory.T.fibreFieldPointsCardLE_diagonalComplementSecondProjection f n h)
    refine GlobalTheory.T.mem_etaleTopology_of_pullback_finite_etale f _ ?_ (fun {V} v hv => ?_)
    · refine (Scheme.etaleTopology).superset_covering ?_ hg
      rintro V u ⟨W, w, v, hv, rfl⟩
      have h1 : Splits (pullback.snd f f) (v ≫ 𝟙 Z) := GlobalTheory.T.splits_pullbackSnd_of_splits_diagonalComplement f _ hv
      have h2 : Splits f ((v ≫ 𝟙 Z) ≫ f) := GlobalTheory.T.splitsFinitelyOverScheme_of_pullback_snd f f _ h1
      exact ⟨W, w, v ≫ f, by simpa using h2, by simp⟩
    · exact ⟨V, 𝟙 V, v, by simpa using GlobalTheory.T.splitsFinitelyOverScheme_of_isEmpty_pullback f v hv, Category.id_comp _⟩

theorem splitSieve_mem : ∀ {Z X S : Scheme.{0}} (f : Z ⟶ X) [IsFinite f] [Etale f] (x : S ⟶ X),
    splitSieve f x ∈ Scheme.etaleTopology S := by
  intro Z X S f _ _ x
  let 𝒰 := S.affineCover
  have hU : Sieve.ofArrows 𝒰.X 𝒰.f ∈ Scheme.etaleTopology S :=
    Scheme.zariskiTopology_le_etaleTopology _ (𝒰.mem_grothendieckTopology)
  refine (Scheme.etaleTopology).transitive hU _ ?_
  rintro Y u ⟨W, w, _, ⟨i⟩, rfl⟩
  rw [Sieve.pullback_comp]
  refine (Scheme.etaleTopology).pullback_stable w ?_
  obtain ⟨n, hn⟩ := GlobalTheory.T.exists_fibreFieldPointsCardLE_of_isFinite_isAffine (pullback.snd f (𝒰.f i ≫ x))
  have hi := splitSieve_mem_of_fibrePointsLE n (pullback.snd f (𝒰.f i ≫ x)) hn
  refine (Scheme.etaleTopology).superset_covering ?_ hi
  rintro V u ⟨W', w', v, hv, rfl⟩
  have h1 := GlobalTheory.T.splitsFinitelyOverScheme_of_pullback_snd f (𝒰.f i ≫ x) (v ≫ 𝟙 _) hv
  exact ⟨W', w', v ≫ 𝒰.f i, by simpa using h1, by simp⟩

end GlobalTheory.EtC.Tr
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplittingSieveMemEtaleTopologyStatement
open CategoryTheory Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splittingSieve_mem_etaleTopology : ∀ {Z X S : Scheme.{0}} (f : Z ⟶ X) [IsFinite f] [Etale f] (x : S ⟶ X), GlobalTheory.EtC.Tr.splitSieve f x ∈ Scheme.etaleTopology S := by
  first | exact @GlobalTheory.EtC.Tr.splitSieve_mem | exact GlobalTheory.EtC.Tr.splitSieve_mem | (intros; apply GlobalTheory.EtC.Tr.splitSieve_mem <;> assumption)
end
