module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemNonzeroLocusIffChart
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw

noncomputable section
namespace GlobalTheory.AbVarProj

section General
variable {X Y : Scheme.{0}} {L : LB X}

theorem mem_nonzeroLocus_iff_sval {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (y : Y) {J : (Y ⟶ X) → L.ι} (hJ : Good L y J) :
    y ∈ nonzeroLocus s ↔ IsUnit (sval s (𝟙 Y) y J) := by
  refine ⟨fun h => ?_, fun h => (mem_nonzeroLocus s y).2 ⟨_, hJ.mem φ (𝟙 Y), h⟩⟩
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 h
  exact isUnit_sval s (𝟙 Y) y hJ k hk

end General

section Group
variable {S : Scheme.{0}} (A : Over S) [GrpObj A]

end Group

end GlobalTheory.AbVarProj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionTwistedLineBundleNonzeroClosedFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionTranslateTensorFibreNonvanishing
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonvanishingTwistedSectionsDescendFieldExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonvanishingTwistedSectionsDescendFieldExtension
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.TwistDescent

open ReciprocityTheory.ChartRestriction.G.Geo.Tor (gs gs_eq gs_mul gs_pull gs_res gs_compat mem_pull chartPullOut chartPullUnpull)

theorem ker_descend {k K : Type} [Field k] [Field K] [Algebra k K] {a b : ℕ}
    (D : Matrix (Fin b) (Fin a) k) (v : Fin a → K) (hv : (D.map (algebraMap k K)).mulVec v = 0) :
    ∃ (r : ℕ) (e : Fin r → K) (u : Fin r → Fin a → k), (∀ l, D.mulVec (u l) = 0) ∧
      ∀ j, v j = ∑ l, e l * algebraMap k K (u l j) := by
  classical
  let V := Submodule.span k (Set.range v)
  haveI : Module.Finite k V := FiniteDimensional.span_of_finite k (Set.finite_range v)
  let bV := Module.finBasis k V
  have hv' : ∀ j, v j ∈ V := fun j => Submodule.subset_span ⟨j, rfl⟩
  have hli : LinearIndependent k (fun l => (bV l : K)) :=
    bV.linearIndependent.map' V.subtype (Submodule.ker_subtype V)
  obtain ⟨c, hc⟩ : ∃ c : Fin (Module.finrank k V) → Fin a → k, ∀ j, v j = ∑ l, c l j • (bV l : K) :=
    ⟨fun l j => bV.repr ⟨v j, hv' j⟩ l, fun j => by
      have := congrArg Subtype.val (bV.sum_repr ⟨v j, hv' j⟩)
      rw [Submodule.coe_sum] at this
      simpa using this.symm⟩
  refine ⟨_, fun l => (bV l : K), c, fun l => ?_, fun j => ?_⟩
  · funext p
    have hp := congrFun hv p
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply, hc, Finset.mul_sum] at hp
    rw [Finset.sum_comm] at hp
    have : ∑ l, (∑ j, D p j * c l j) • (bV l : K) = 0 := by
      rw [← hp]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.smul_def, Algebra.smul_def, map_mul]
      ring
    exact Fintype.linearIndependent_iff.1 hli _ this l
  · rw [hc j]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Algebra.smul_def, mul_comm]

theorem mem_nonzeroLocus_iff_isUnit {X Z : Scheme.{0}} {N : LB X} (s : LB.Sec N) (r : Z ⟶ X) (z : Z) {j : N.ι}
    (hj : r z ∈ N.U j) : r z ∈ nonzeroLocus s ↔ IsUnit (gs r z _ (s.f j)) := by
  have key : ∀ {j : N.ι} (hj : r z ∈ N.U j), IsUnit (gs r z _ (s.f j)) ↔ r z ∈ X.basicOpen (s.f j) := by
    intro j hj
    rw [gs_eq r z _ hj]
    refine ((Z.mem_basicOpen ((r.app _).hom (s.f j)) z hj).symm).trans ?_
    rw [← Scheme.Hom.preimage_basicOpen]
    rfl
  rw [key hj]
  refine ⟨fun h => ?_, fun h => TopologicalSpace.Opens.mem_iSup.2 ⟨j, h⟩⟩
  obtain ⟨j', hj'⟩ := TopologicalSpace.Opens.mem_iSup.1 h
  have hm : r z ∈ N.U j' := X.basicOpen_le _ hj'
  rw [← key hj, gs_compat s r z hj hm]
  exact (Units.isUnit _).mul ((key hm).2 hj')

theorem linComb_whisker {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) (q : ℕ)
    {T T' : Over S} (ρ : T' ⟶ T) (c : T ⟶ A) :
    LB.LinComb L (K := Fin 2) (fun k => (ρ ▷ A).left ≫ ![(snd T A).left, (translPt A c).left] k)
      ![(q : ℤ) - 1, 1] = twistLB A L q (ρ ≫ c) := by
  unfold twistLB
  congr 1
  funext k
  fin_cases k
  · show (ρ ▷ A).left ≫ (snd T A).left = (snd T' A).left
    rw [← Over.comp_left, whiskerRight_snd]
  · show (ρ ▷ A).left ≫ (translPt A c).left = (translPt A (ρ ≫ c)).left
    rw [← Over.comp_left]
    congr 1
    simp [translPt, comp_lift_assoc]

theorem exists_sec_of_baseChange : ∀ (S : Scheme.{0}) (P : PolAV S) (k : Type) [Field k] (K : Type) [Field K] [Algebra k K] (t : Spec (CommRingCat.of k) ⟶ S) (c : Over.mk t ⟶ P.A), (∀ z : (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ t) ⊗ P.A).left, ∃ s : LB.Sec (twistLB P.A P.L 2 ((Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap k K))) rfl : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ t) ⟶ Over.mk t) ≫ c)), z ∈ nonzeroLocus s) → ∀ y : (Over.mk t ⊗ P.A).left, ∃ s : LB.Sec (twistLB P.A P.L 2 c), y ∈ nonzeroLocus s := by
  intro S P k _ K _ _ t c hK y
  classical
  let ιK : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k) := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let T := Over.mk t
  let h : Over.mk (ιK ≫ t) ⟶ T := Over.homMk ιK rfl
  rw [← linComb_whisker P.A P.L 2 h c] at hK
  let M : LB (T ⊗ P.A).left := twistLB P.A P.L 2 c
  have hM : M.IsLB := LB.isLB_linComb P.isLB _ _
  let f : (T ⊗ P.A).left ⟶ Spec (CommRingCat.of k) := (fst T P.A).left
  let π := (h ▷ P.A).left
  let f' : (Over.mk (ιK ≫ t) ⊗ P.A).left ⟶ Spec (CommRingCat.of K) := (fst (Over.mk (ιK ≫ t)) P.A).left
  have H : IsPullback π f' f ιK := GlobalTheory.AbLaw.SecBC.isPullback_whisker P.A h
  have hpb := GlobalTheory.AbLaw.SecBC.isPullback_snd P.A T
  haveI : IsProper f := MorphismProperty.of_isPullback (P := @IsProper) hpb P.isAb.proper
  haveI : Smooth f := MorphismProperty.of_isPullback (P := @Smooth) hpb P.isAb.smooth
  haveI : Flat f := inferInstance
  obtain ⟨Q⟩ := GlobalTheory.ProperFinite.nonempty_perf_of_isProper f hM
  haveI hι : Surjective ιK := ⟨fun p => ⟨⟨⊥, Ideal.isPrime_bot⟩, Subsingleton.elim _ _⟩⟩
  have hπ : Surjective π := MorphismProperty.of_isPullback (P := @Surjective) H.flip hι
  obtain ⟨z, rfl⟩ := hπ.surj y
  by_contra hy
  push Not at hy
  obtain ⟨sK, hsK⟩ := hK z
  obtain ⟨i, hi⟩ := GlobalTheory.SecTwist.perf_cover Q (π z)
  have m₁ : π z ∈ M.U (Q.ch i) := Q.le i hi
  have m₂ : z ∈ (LB.LinComb P.L (K := Fin 2) (fun k => π ≫ ![(snd T P.A).left, (translPt P.A c).left] k)
      ![((2 : ℕ) : ℤ) - 1, 1]).U (Q.ch i) :=
    Set.mem_iInter.2 fun k => Set.mem_iInter.1 m₁ k
  let sb : LB.Sec (M.pull π) := GlobalTheory.SecTwist.pullSec (chartPullOut P.L _ _ π _ fun _ => rfl) sK
  obtain ⟨E, hE⟩ := GlobalTheory.SecTwist.perf_sec Q (algebraMap k K) H
  have hu1 : IsUnit (gs (𝟙 _) z ((M.pull π).U (fun _ => Q.ch i)) (sb.f (fun _ => Q.ch i))) := by
    have a₁ := GlobalTheory.SecTwist.gs_pullSec (chartPullOut P.L _ _ π _ fun _ => rfl) sK (𝟙 _) z (fun _ => Q.ch i)
      (mem_pull.2 m₁)
    rw [Category.id_comp] at a₁
    refine a₁ ▸ (mem_nonzeroLocus_iff_isUnit sK (𝟙 _) z m₂).1 hsK
  obtain ⟨r, e, u, hu, hvu⟩ := ker_descend Q.D₀ (E.symm sb).1 (E.symm sb).2
  have h₀ : IsPullback (𝟙 _) f f (Spec.map (CommRingCat.ofHom (RingHom.id k))) := by
    rw [CommRingCat.ofHom_id, Spec.map_id]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  obtain ⟨E₀, hE₀⟩ := GlobalTheory.SecTwist.perf_sec Q (RingHom.id k) h₀
  have ker : ∀ l, (Q.D₀.map (RingHom.id k)).mulVec (u l) = 0 := fun l => by
    rw [show Q.D₀.map (RingHom.id k) = Q.D₀ from rfl]
    exact hu l
  let s : Fin r → LB.Sec M := fun l => GlobalTheory.SecTwist.pullSec (chartPullUnpull M (𝟙 _) rfl) (E₀ ⟨u l, ker l⟩)
  have hG : ∀ l, gs π z (M.U (Q.ch i)) ((s l).f (Q.ch i)) =
      ∑ j, ReciprocityTheory.ChartRestriction.G.Geo.Tor.cst (π ≫ f) z (u l j) * gs π z (Q.W i) (Q.u j i) := fun l => by
    have a₃ := GlobalTheory.SecTwist.gs_pullSec (chartPullUnpull M (𝟙 _) rfl) (E₀ ⟨u l, ker l⟩) π z (Q.ch i) m₁
    have a₄ := hE₀ ⟨u l, ker l⟩ i _ π z hi
    rw [Category.comp_id] at a₃ a₄
    exact a₃.trans a₄
  have hnu : ∀ l, gs π z (M.U (Q.ch i)) ((s l).f (Q.ch i)) ∈ IsLocalRing.maximalIdeal _ := fun l => by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← mem_nonzeroLocus_iff_isUnit (s l) π z m₁]
    exact hy (s l)
  have e1 : ∀ a : k, ReciprocityTheory.ChartRestriction.G.Geo.Tor.cst f' z (algebraMap k K a) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.cst (π ≫ f) z a :=
    fun a => by
      rw [← ReciprocityTheory.ChartRestriction.G.Geo.Tor.cst_comp]
      congr 1
      exact H.w.symm
  have hsb := hE (E.symm sb) i _ (𝟙 _) z hi
  rw [Equiv.apply_symm_apply] at hsb
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Category.id_comp, hvu, ← GlobalTheory.SecTwist.cstHom_apply, map_sum, map_mul] at hsb
  simp only [GlobalTheory.SecTwist.cstHom_apply, e1] at hsb
  refine (IsLocalRing.mem_maximalIdeal _).1 ?_ hu1
  rw [hsb]
  have key : ∀ l, ReciprocityTheory.ChartRestriction.G.Geo.Tor.cst f' z (e l) * gs π z (M.U (Q.ch i)) ((s l).f (Q.ch i)) ∈
      IsLocalRing.maximalIdeal _ := fun l => Ideal.mul_mem_left _ _ (hnu l)
  have := Ideal.sum_mem (IsLocalRing.maximalIdeal _) fun l (_ : l ∈ Finset.univ) => key l
  simp only [hG, Finset.mul_sum] at this
  rw [Finset.sum_comm] at this
  convert this using 2 with j
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

end GlobalTheory.TwistDescent
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonvanishingTwistedSectionsDescendFieldExtensionStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonvanishing_twistedSections_descend_fieldExtension : ∀ (S : Scheme.{0}) (P : PolAV S) (k : Type) [Field k] (K : Type) [Field K] [Algebra k K] (t : Spec (CommRingCat.of k) ⟶ S) (c : Over.mk t ⟶ P.A), (∀ z : (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ t) ⊗ P.A).left, ∃ s : LB.Sec (twistLB P.A P.L 2 ((Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap k K))) rfl : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ t) ⟶ Over.mk t) ≫ c)), z ∈ nonzeroLocus s) → ∀ y : (Over.mk t ⊗ P.A).left, ∃ s : LB.Sec (twistLB P.A P.L 2 c), y ∈ nonzeroLocus s := by
  first | exact @GlobalTheory.TwistDescent.exists_sec_of_baseChange | exact GlobalTheory.TwistDescent.exists_sec_of_baseChange | (intros; apply GlobalTheory.TwistDescent.exists_sec_of_baseChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionTwistNonvanishingRationalPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarisationSectionNonemptyNonvanishing
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarisationSectionNonemptyNonvanishing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.FibreTheta

theorem exists_sec_nonempty : ∀ (S : Scheme.{0}) (P : PolAV S) (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ S),
    IsIntegral (Over.mk t ⊗ P.A).left → ∃ θ : LB.Sec (LB.LinComb P.L (K := Fin 1) ![(snd (Over.mk t) P.A).left] ![1]),
      (nonzeroLocus θ : Set (Over.mk t ⊗ P.A).left).Nonempty := by
  intro S P K _ t hI
  let T : Over S := Over.mk t
  obtain ⟨⟨b, hb⟩, -⟩ := GlobalTheory.abelianSchemeLaws_all.2.secTwist S P 1 le_rfl K t (1 : T ⟶ P.A)
  have := P.isAb.comm
  have e : translPt P.A (1 : T ⟶ P.A) = snd T P.A := by
    show (fst T P.A ≫ 1) * snd T P.A = _
    rw [MonObj.comp_one, _root_.one_mul]
  have i₀ : Fin (1 ^ P.g) := ⟨0, by simp⟩
  have su : ∀ {M : Type} [AddCommMonoid M] (q : Fin (1 ^ P.g) → M), ∑ i, q i = q i₀ := fun q =>
    Finset.sum_eq_single i₀ (fun a _ h => absurd (Fin.ext (by have := a.2; have := i₀.2; simp at *; omega)) h) (by simp)

  have nz : ∃ j, (b i₀).f j ≠ 0 := by
    by_contra hz
    push_neg at hz
    obtain ⟨r, -, hu⟩ := hb (b i₀)
    have h0 : ∀ r' : Fin (1 ^ P.g) → Γ(T.left, ⊤), ∀ j, (b i₀).f j = ∑ i, ((T ⊗ P.A).left.presheaf.map
        (homOfLE le_top).op).hom ((fst T P.A).left.appTop.hom (r' i)) * (b i).f j := fun r' j => by
      rw [su, hz j, mul_zero]
    have := (hu (fun _ => 0) (h0 _)).trans (hu (fun _ => 1) (h0 _)).symm
    exact zero_ne_one ((Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm.injective
      ((map_zero _).trans ((congrFun this i₀).trans (map_one _).symm)))
  obtain ⟨j, hj⟩ := nz
  haveI : IsReduced (T ⊗ P.A).left := inferInstance
  obtain ⟨y, hy⟩ : ∃ y, y ∈ (T ⊗ P.A).left.basicOpen ((b i₀).f j) := by
    by_contra h
    push_neg at h
    exact hj (eq_zero_of_basicOpen_eq_bot _ (eq_bot_iff.2 fun y hy' => (h y hy').elim))
  have hy₀ : y ∈ nonzeroLocus (b i₀) := TopologicalSpace.Opens.mem_iSup.2 ⟨j, hy⟩
  have hF : FormEq (![(snd T P.A).left, (translPt P.A (1 : T ⟶ P.A)).left] : Fin 2 → _)
      ![((1 : ℕ) : ℤ) - 1, 1] (![(snd T P.A).left] : Fin 1 → _) ![1] := by
    intro U _ h
    rw [e]; simp [Fin.prod_univ_succ]
  obtain ⟨s, hs⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_sec P.isLB hF (b i₀)
  choose J hJ using fun χ : (T ⊗ P.A).left ⟶ P.A.left => exists_chart P.isLB (χ y)
  have hJ' : Good P.L y J := hJ
  refine ⟨s, y, ?_⟩
  show y ∈ nonzeroLocus s
  rw [GlobalTheory.AbVarProj.mem_nonzeroLocus_iff_sval s y hJ', hs _ (𝟙 _) y J hJ']
  exact (GlobalTheory.AbVarProj.mem_nonzeroLocus_iff_sval (b i₀) y hJ').1 hy₀

end GlobalTheory.FibreTheta
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarisationSectionNonemptyNonvanishingStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polarisation_section_nonempty_nonvanishing : ∀ (S : Scheme.{0}) (P : PolAV S) (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ S), IsIntegral (Over.mk t ⊗ P.A).left → ∃ θ : LB.Sec (LB.LinComb P.L (K := Fin 1) ![(snd (Over.mk t) P.A).left] ![1]), (nonzeroLocus θ : Set (Over.mk t ⊗ P.A).left).Nonempty := by
  first | exact @GlobalTheory.FibreTheta.exists_sec_nonempty | exact GlobalTheory.FibreTheta.exists_sec_nonempty | (intros; apply GlobalTheory.FibreTheta.exists_sec_nonempty <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointMemTranslates
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointMemTranslates
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AlgClosedFibre

theorem exists_point_mem_translates :
    ∀ (S : Scheme.{0}) (P : PolAV S) (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S),
      IrreducibleSpace (Over.mk t ⊗ P.A).left → ∀ (U : (Over.mk t ⊗ P.A).left.Opens),
      (U : Set (Over.mk t ⊗ P.A).left).Nonempty → ∀ (a c : Over.mk t ⟶ P.A) (p : Spec (CommRingCat.of K)),
      ∃ u : Over.mk t ⟶ P.A, (lift (𝟙 (Over.mk t)) (c * u * a)).left p ∈ U ∧
        (lift (𝟙 (Over.mk t)) (u⁻¹ * a)).left p ∈ U := by
  intro S P K _ _ t hirr U hU a c p
  let T : Over S := Over.mk t
  let E : Over S := T ⊗ P.A
  have hsm : Smooth P.A.hom := P.isAb.smooth
  have hlft : LocallyOfFiniteType (fst T P.A).left := by
    change LocallyOfFiniteType (pullback.fst t P.A.hom)
    infer_instance
  have hJ0 : JacobsonSpace T.left := by
    change JacobsonSpace (PrimeSpectrum K)
    infer_instance
  have hJ : JacobsonSpace E.left := LocallyOfFiniteType.jacobsonSpace (fst T P.A).left
  let g₁ : E ⟶ E := lift (fst T P.A) ((fst T P.A ≫ c) * snd T P.A * (fst T P.A ≫ a))
  let g₂ : E ⟶ E := lift (fst T P.A) ((snd T P.A)⁻¹ * (fst T P.A ≫ a))
  let h₁ : E ⟶ E := lift (fst T P.A) ((fst T P.A ≫ c)⁻¹ * snd T P.A * (fst T P.A ≫ a)⁻¹)
  let h₂ : E ⟶ E := lift (fst T P.A) ((fst T P.A ≫ a) * (snd T P.A)⁻¹)
  have e₁ : h₁ ≫ g₁ = 𝟙 E := by
    ext1
    · simp [g₁, h₁]
    · simp [g₁, h₁, MonObj.comp_mul, GrpObj.comp_inv, _root_.mul_assoc]
      exact (Category.id_comp _).symm
  have e₂ : h₂ ≫ g₂ = 𝟙 E := by
    ext1
    · simp [g₂, h₂]
    · simp [g₂, h₂, MonObj.comp_mul, GrpObj.comp_inv, _root_.mul_assoc]
      exact (Category.id_comp _).symm
  have ne : ∀ {f g : E ⟶ E}, g ≫ f = 𝟙 E → ((f.left ⁻¹ᵁ U : E.left.Opens) : Set E.left).Nonempty := by
    intro f g h
    obtain ⟨w, hw⟩ := hU
    refine ⟨g.left w, ?_⟩
    change f.left (g.left w) ∈ U
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, h]
    exact hw
  have hin := nonempty_preirreducible_inter (TopologicalSpace.Opens.isOpen _)
      (TopologicalSpace.Opens.isOpen _) (ne e₁) (ne e₂)
  obtain ⟨z, hz, hc⟩ := nonempty_inter_closedPoints hin
    ((TopologicalSpace.Opens.isOpen _).inter (TopologicalSpace.Opens.isOpen _)).isLocallyClosed
  let q := pointOfClosedPoint (fst T P.A).left z hc
  have hq : q ≫ (fst T P.A).left = 𝟙 _ := pointOfClosedPoint_comp _ z hc
  have hqw : q ≫ E.hom = t := by
    rw [← Over.w (fst T P.A), ← Category.assoc, hq, Category.id_comp]
    rfl
  let Q : T ⟶ E := Over.homMk q hqw
  have hQf : Q ≫ fst T P.A = 𝟙 T := by
    ext1
    exact hq
  have hQf' : ∀ (f : T ⟶ P.A), Q ≫ fst T P.A ≫ f = f := fun f => by
    rw [← Category.assoc, hQf, Category.id_comp]
  have hqp : q p = z := pointOfClosedPoint_apply _ z hc p
  refine ⟨Q ≫ snd T P.A, ?_, ?_⟩
  · have hQ : lift (𝟙 T) (c * (Q ≫ snd T P.A) * a) = Q ≫ g₁ := by
      ext1
      · simp only [lift_fst, Category.assoc, g₁, hQf]
      · simp only [lift_snd, Category.assoc, g₁, MonObj.comp_mul, hQf']
    rw [hQ, Over.comp_left, Scheme.Hom.comp_apply]
    change g₁.left (q p) ∈ U
    rw [hqp]
    exact hz.1
  · have hQ : lift (𝟙 T) ((Q ≫ snd T P.A)⁻¹ * a) = Q ≫ g₂ := by
      ext1
      · simp only [lift_fst, Category.assoc, g₂, hQf]
      · simp only [lift_snd, Category.assoc, g₂, MonObj.comp_mul, GrpObj.comp_inv, hQf']
    rw [hQ, Over.comp_left, Scheme.Hom.comp_apply]
    change g₂.left (q p) ∈ U
    rw [hqp]
    exact hz.2

end GlobalTheory.AlgClosedFibre
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointMemTranslatesStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_point_mem_translates' : ∀ (S : Scheme.{0}) (P : PolAV S) (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S), IrreducibleSpace (Over.mk t ⊗ P.A).left → ∀ (U : (Over.mk t ⊗ P.A).left.Opens), (U : Set (Over.mk t ⊗ P.A).left).Nonempty → ∀ (a c : Over.mk t ⟶ P.A) (p : Spec (CommRingCat.of K)), ∃ u : Over.mk t ⟶ P.A, (lift (𝟙 (Over.mk t)) (c * u * a)).left p ∈ U ∧ (lift (𝟙 (Over.mk t)) (u⁻¹ * a)).left p ∈ U := by
  first | exact @GlobalTheory.AlgClosedFibre.exists_point_mem_translates | exact GlobalTheory.AlgClosedFibre.exists_point_mem_translates | (intros; apply GlobalTheory.AlgClosedFibre.exists_point_mem_translates <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionTwistNonvanishingRationalPoint
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic ReciprocityTheory.ChartRestriction.G.H1.SquareUnits
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.TwistFibre

variable {S : Scheme.{0}} (P : PolAV S) {K : Type} [Field K] (t : Spec (CommRingCat.of K) ⟶ S)

theorem unitAt_square (x₁ x₂ : Over.mk t ⟶ P.A) (y : (Over.mk t ⊗ P.A).left) :
    UnitAt P.L ![(translPt P.A (x₁ * x₂)).left, (snd (Over.mk t) P.A).left,
      (translPt P.A x₁).left, (translPt P.A x₂).left] ![1, 1, -1, -1] y := by
  obtain ⟨V, hpV, c, hc⟩ := (GlobalTheory.AbSquare.square_of_cube GlobalTheory.AbLaw.CubeAssembly.cube_gen).1 S P (Over.mk t) x₁ x₂
    (IsLocalRing.closedPoint K)
  have hV : V = ⊤ := eq_top_iff.2 fun q _ => by
    rw [spec_pt_eq (k := K) q (IsLocalRing.closedPoint K)]; exact hpV
  subst hV
  obtain ⟨s, hs⟩ := exists_sec_of_pullGen (Z := (Over.mk t ⊗ P.A).left)
    ((fst (Over.mk t) P.A).left ⁻¹ᵁ ⊤).ι c hc
  let e := IsOpenImmersion.lift ((fst (Over.mk t) P.A).left ⁻¹ᵁ ⊤).ι (𝟙 _)
    (by rintro _ ⟨q, rfl⟩; rw [Scheme.Opens.range_ι]; trivial)
  have he : e ≫ ((fst (Over.mk t) P.A).left ⁻¹ᵁ ⊤).ι = 𝟙 _ :=
    IsOpenImmersion.lift_fac _ _ _
  refine UnitAt.congr P.isLB ?_ ⟨pullSec s e, fun J hJ => ?_⟩
  · refine formEq_of_add fun U _ hh => ?_
    simp only [← Category.assoc, he, Category.id_comp]
  · rw [sval_pullSec s e (𝟙 _) y hJ]
    exact hs _ y J hJ

theorem isIntegral_fibre : IsIntegral (Over.mk t ⊗ P.A).left := by
  have := P.isAb.smooth
  have := P.isAb.geomConnected
  have : GeometricallyIntegral P.A.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ inferInstance inferInstance
  exact GeometricallyIntegral.geometrically_isIntegral (f := P.A.hom) t (pullback.snd t P.A.hom)
    (pullback.fst t P.A.hom) (IsPullback.of_hasPullback t P.A.hom).flip

def trY (w : Over.mk t ⟶ P.A) : Over.mk t ⊗ P.A ⟶ Over.mk t ⊗ P.A := lift (fst _ _) (translPt P.A w)

theorem trY_snd (w : Over.mk t ⟶ P.A) :
    (trY P t w).left ≫ (snd (Over.mk t) P.A).left = (translPt P.A w).left := by
  rw [← Over.comp_left, trY, lift_snd]

theorem lift_trY (a w : Over.mk t ⟶ P.A) : lift (𝟙 (Over.mk t)) a ≫ trY P t w = lift (𝟙 (Over.mk t)) (w * a) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [trY]
  · rw [Category.assoc, trY, lift_snd, lift_snd, translPt, comp_lift_assoc, lift_fst_assoc, Category.id_comp,
      lift_snd, Hom.mul_def]

theorem isUnit_sval_of_mem {X Y Z : Scheme.{0}} {L : LB X} {I : Type} [Fintype I] {φ : I → (Y ⟶ X)} {ε : I → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) (h : r z ∈ nonzeroLocus s) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) : IsUnit (sval s r z J) := by
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 h
  exact ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.isUnit_sval s r z hJ k hk

theorem exists_sec_twist_mem_nonzeroLocus : ∀ (S : Scheme.{0}) (P : PolAV S) (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S) (c : Over.mk t ⟶ P.A) (a : Over.mk t ⟶ P.A) (p : Spec (CommRingCat.of K)), ∃ s : LB.Sec (twistLB P.A P.L 2 c), (lift (𝟙 (Over.mk t)) a).left p ∈ nonzeroLocus s := by
  intro S P K _ _ t c a p
  have hI := isIntegral_fibre P t
  obtain ⟨θ, hθ⟩ := GlobalTheory.T.exists_polarisation_section_nonempty_nonvanishing S P K t hI
  obtain ⟨u, h₁, h₂⟩ := GlobalTheory.T.exists_point_mem_translates' S P K t inferInstance (nonzeroLocus θ) hθ a c p
  obtain ⟨g, hg⟩ := unitAt_square P t (c * u) u⁻¹ ((lift (𝟙 (Over.mk t)) a).left p)
  have hF : FormEq (Sum.elim (Sum.elim (fun k => (trY P t (c * u)).left ≫ ![(snd (Over.mk t) P.A).left] k)
      (fun k => (trY P t u⁻¹).left ≫ ![(snd (Over.mk t) P.A).left] k))
      ![(translPt P.A (c * u * u⁻¹)).left, (snd (Over.mk t) P.A).left,
        (translPt P.A (c * u)).left, (translPt P.A u⁻¹).left])
      (Sum.elim (Sum.elim ![1] ![1]) ![1, 1, -1, -1])
      ![(snd (Over.mk t) P.A).left, (translPt P.A c).left] ![((2 : ℕ) : ℤ) - 1, 1] := by
    refine formEq_of_add fun U _ h => ?_
    simp only [Fintype.sum_sum_type, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Matrix.cons_val_one, Matrix.head_cons]
    rw [trY_snd, trY_snd, mul_inv_cancel_right]
    simp
    abel
  obtain ⟨σ, hσ⟩ := exists_sec P.isLB hF (mulSec (mulSec (pullSec θ (trY P t (c * u)).left)
    (pullSec θ (trY P t u⁻¹).left)) g)
  refine ⟨σ, ?_⟩
  choose J hJ using fun χ : (Over.mk t ⊗ P.A).left ⟶ P.A.left => exists_chart P.isLB (χ ((lift (𝟙 (Over.mk t)) a).left p))
  have hJ' : Good P.L ((lift (𝟙 (Over.mk t)) a).left p) J := hJ
  refine (GlobalTheory.AbVarProj.mem_nonzeroLocus_iff_sval σ _ hJ').2 ?_
  rw [hσ _ _ _ J hJ', sval_mulSec _ _ _ _ hJ',
    sval_mulSec _ _ _ _ hJ', sval_pullSec _ _ _ _ hJ', sval_pullSec _ _ _ _ hJ']
  refine ((isUnit_sval_of_mem θ _ _ ?_ hJ').mul (isUnit_sval_of_mem θ _ _ ?_ hJ')).mul (hg J hJ')
  · rw [Category.id_comp, ← Scheme.Hom.comp_apply, ← Over.comp_left, lift_trY]
    exact h₁
  · rw [Category.id_comp, ← Scheme.Hom.comp_apply, ← Over.comp_left, lift_trY]
    exact h₂

end GlobalTheory.TwistFibre
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionTwistNonvanishingRationalPointStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_twist_nonvanishing_rationalPoint : ∀ (S : Scheme.{0}) (P : PolAV S) (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S) (c : Over.mk t ⟶ P.A) (a : Over.mk t ⟶ P.A) (p : Spec (CommRingCat.of K)), ∃ s : LB.Sec (twistLB P.A P.L 2 c), (lift (𝟙 (Over.mk t)) a).left p ∈ nonzeroLocus s := by
  first | exact @GlobalTheory.TwistFibre.exists_sec_twist_mem_nonzeroLocus | exact GlobalTheory.TwistFibre.exists_sec_twist_mem_nonzeroLocus | (intros; apply GlobalTheory.TwistFibre.exists_sec_twist_mem_nonzeroLocus <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionTranslateTensorFibreNonvanishing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.TwistFibreGen

theorem exists_sec_of_closed {X : Scheme.{0}} [CompactSpace X] (M : LB X)
    (h : ∀ z : X, IsClosed ({z} : Set X) → ∃ s : LB.Sec M, z ∈ nonzeroLocus s) (z : X) :
    ∃ s : LB.Sec M, z ∈ nonzeroLocus s := by
  by_contra hz
  push_neg at hz
  let C : Set X := ⋂ s : LB.Sec M, ((nonzeroLocus s : X.Opens) : Set X)ᶜ
  have hC : IsClosed C := isClosed_iInter fun s => (nonzeroLocus s).isOpen.isClosed_compl
  obtain ⟨w, hw, hcl⟩ := hC.exists_closed_singleton ⟨z, Set.mem_iInter.2 fun s => hz s⟩
  obtain ⟨s, hs⟩ := h w hcl
  exact Set.mem_iInter.1 hw s hs

theorem compactSpace_fibre {S : Scheme.{0}} (P : PolAV S) (k : Type) [Field k]
    (t : Spec (CommRingCat.of k) ⟶ S) : CompactSpace (Over.mk t ⊗ P.A).left := by
  have := P.isAb.proper
  have : QuasiCompact (pullback.fst t P.A.hom) := inferInstance
  exact QuasiCompact.compactSpace_of_compactSpace (pullback.fst t P.A.hom)

theorem exists_sec_algClosed {S : Scheme.{0}} (P : PolAV S) (K : Type) [Field K] [IsAlgClosed K]
    (t : Spec (CommRingCat.of K) ⟶ S) (c : Over.mk t ⟶ P.A) (z : (Over.mk t ⊗ P.A).left) :
    ∃ s : LB.Sec (twistLB P.A P.L 2 c), z ∈ nonzeroLocus s := by
  have := compactSpace_fibre P K t
  refine exists_sec_of_closed _ (fun z hz => ?_) z
  have := P.isAb.smooth
  have : LocallyOfFiniteType (fst (Over.mk t) P.A).left :=
    (inferInstance : LocallyOfFiniteType (pullback.fst t P.A.hom))
  let f := (fst (Over.mk t) P.A).left
  let p₀ := pointOfClosedPoint f z hz
  have hw : p₀ ≫ (Over.mk t ⊗ P.A).hom = (Over.mk t).hom := by
    rw [← Over.w (fst (Over.mk t) P.A), ← Category.assoc, pointOfClosedPoint_comp]
    exact Category.id_comp _
  let q : Over.mk t ⟶ Over.mk t ⊗ P.A := Over.homMk p₀ hw
  have hq : q ≫ fst (Over.mk t) P.A = 𝟙 _ := by
    ext1
    exact pointOfClosedPoint_comp f z hz
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_section_twist_nonvanishing_rationalPoint S P K t c (q ≫ snd _ _) (IsLocalRing.closedPoint _)
  refine ⟨s, ?_⟩
  have e : lift (𝟙 (Over.mk t)) (q ≫ snd (Over.mk t) P.A) = q := by
    rw [← hq, lift_comp_fst_snd]
  rw [e] at hs
  have h2 : q.left (IsLocalRing.closedPoint K) = z := pointOfClosedPoint_apply f z hz _
  rw [← h2]
  exact hs

theorem exists_sec_mem_nonzeroLocus : ∀ (S : Scheme.{0}) (P : PolAV S) (k : Type) [Field k]
    (t : Spec (CommRingCat.of k) ⟶ S) (c : Over.mk t ⟶ P.A) (y : (Over.mk t ⊗ P.A).left),
    ∃ s : LB.Sec (twistLB P.A P.L 2 c), y ∈ nonzeroLocus s := by
  intro S P k _ t c y
  exact GlobalTheory.T.nonvanishing_twistedSections_descend_fieldExtension S P k (AlgebraicClosure k) t c (fun z => exists_sec_algClosed P _ _ _ z) y

end GlobalTheory.TwistFibreGen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionTranslateTensorFibreNonvanishingStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_translateTensor_fibre_nonvanishing : ∀ (S : Scheme.{0}) (P : PolAV S) (k : Type) [Field k] (t : Spec (CommRingCat.of k) ⟶ S) (c : Over.mk t ⟶ P.A) (y : (Over.mk t ⊗ P.A).left), ∃ s : LB.Sec (twistLB P.A P.L 2 c), y ∈ nonzeroLocus s := by
  first | exact @GlobalTheory.TwistFibreGen.exists_sec_mem_nonzeroLocus | exact GlobalTheory.TwistFibreGen.exists_sec_mem_nonzeroLocus | (intros; apply GlobalTheory.TwistFibreGen.exists_sec_mem_nonzeroLocus <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionTwistedLineBundleNonzeroClosedFibre
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.TwistGen

theorem whisker_eq_twistLB {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) (q : ℕ)
    {T T' : Over S} (ρ : T' ⟶ T) (c : T ⟶ A) :
    LB.LinComb L (K := Fin 2) (fun k => (ρ ▷ A).left ≫ ![(snd T A).left, (translPt A c).left] k)
      ![(q : ℤ) - 1, 1] = twistLB A L q (ρ ≫ c) := by
  unfold twistLB
  congr 1
  funext k
  fin_cases k
  · show (ρ ▷ A).left ≫ (snd T A).left = (snd T' A).left
    rw [← Over.comp_left, whiskerRight_snd]
  · show (ρ ▷ A).left ≫ (translPt A c).left = (translPt A (ρ ≫ c)).left
    rw [← Over.comp_left]
    congr 1
    simp [translPt, comp_lift_assoc]

theorem mem_of_isPullSecLC {X Y Y' : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (h : Y' ⟶ Y) (s : LB.Sec (LB.LinComb L φ ε)) (s' : LB.Sec (LB.LinComb L (fun k => h ≫ φ k) ε))
    (hs : IsPullSecLC L φ ε h s s') (y : Y') (hy : y ∈ nonzeroLocus s') : h y ∈ nonzeroLocus s := by
  obtain ⟨(j : K → L.ι), hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  rw [hs j] at hj
  erw [Scheme.basicOpen_res] at hj
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, (Scheme.preimage_basicOpen h (s.f j)).ge hj.2⟩

theorem transfer {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (α : D.X)
    (s : LB.Sec (twistLB D.P.A D.P.L 2 (D.c α)))
    (z : (𝟙_ (Over (Spec (CommRingCat.of R))) ⊗ D.P.A).left) (hz : z ∈ nonzeroLocus s) :
    ∃ σ : D.SecB 2 α, (snd _ D.P.A).left z ∈ nonzeroLocus σ := by
  let T := 𝟙_ (Over (Spec (CommRingCat.of R)))
  let A := D.P.A
  let iota : A.left ⟶ (T ⊗ A).left := (lift (toUnit A) (𝟙 A)).left
  have hsec : snd T A ≫ lift (toUnit A) (𝟙 A) = 𝟙 (T ⊗ A) := by
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · exact (toUnit_unique _ _)
    · rw [Category.assoc, lift_snd, Category.comp_id, Category.id_comp]
  have hiota : iota ((snd T A).left z) = z := by
    have e : (snd T A).left ≫ iota = 𝟙 _ := by rw [← Over.comp_left, hsec]; rfl
    have e' := congrArg (fun f => f.base z) e
    exact e'
  obtain ⟨u₀, hu₀⟩ := DVR.exists_gen_of_local (V := R) D.P.L D.P.isLB (K := Fin 2)
    (![(D.c α).left, η[A].left] : Fin 2 → (Spec (CommRingCat.of R) ⟶ A.left)) ![-1, 1]
  let u := LB.pullGen D.P.L _ _ u₀ (toUnit A).left
  have hu : u.IsGen := DVR.pullGen_isGen_of_isGen _ _ u₀ hu₀ _
  let s₁ := pullMulSec s iota u hu
  have hF : FormEq (Sum.elim (fun k => iota ≫ ![(snd T A).left, (translPt A (D.c α)).left] k)
      (fun k => (toUnit A).left ≫ (![(D.c α).left, η[A].left] : Fin 2 → (Spec (CommRingCat.of R) ⟶ A.left)) k))
      (Sum.elim ![((2 : ℕ) : ℤ) - 1, 1] ![-1, 1]) (D.famφB α) (DegPre.famε 2) := by
    have e₁ : iota ≫ (snd T A).left = 𝟙 _ := by
      rw [← Over.comp_left, lift_snd]; rfl
    have e₂ : iota ≫ (translPt A (D.c α)).left = (padd A (𝟙 A) (toUnit A ≫ D.c α)).left := by
      rw [← Over.comp_left]
      congr 1
      show lift (toUnit A) (𝟙 A) ≫ ((fst T A ≫ D.c α) * snd T A) = 𝟙 A * (toUnit A ≫ D.c α)
      rw [Hom.mul_def, Hom.mul_def, ← Category.assoc, comp_lift, lift_snd, ← Category.assoc, lift_fst]
      show (toUnit A ≫ D.c α) * 𝟙 A = 𝟙 A * (toUnit A ≫ D.c α)
      exact mul_comm _ _
    intro U _ hh
    simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_four, Sum.elim_inl, Sum.elim_inr,
      DegPre.famφB, DegPre.famε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, e₁, e₂]
    simp only [_root_.mul_assoc]; rfl
  obtain ⟨σ, hσ⟩ := exists_sec D.P.isLB hF s₁
  refine ⟨σ, ?_⟩
  set xx := (snd T A).left z
  choose J hJ using fun χ : A.left ⟶ A.left => exists_chart D.P.isLB (χ xx)
  obtain ⟨(k : Fin 2 → D.P.L.ι), hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
  have hv : IsUnit (sval s (𝟙 A.left ≫ iota) xx J) := by
    refine H1.SectionArithmetic.isUnit_sval s (𝟙 A.left ≫ iota) xx hJ k ?_
    rw [Category.id_comp, hiota]; exact hk
  have hval : IsUnit (sval σ (𝟙 A.left) xx J) := by
    rw [hσ _ _ xx J hJ, sval_pullMulSec s iota u hu (𝟙 A.left) xx hJ]
    exact hv.mul (Units.isUnit _)
  have hm := (Good.mem hJ (D.famφB α) (𝟙 A.left))
  rw [sval] at hval
  erw [gs_eq (𝟙 A.left) xx _ hm] at hval
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨fun k => J (𝟙 A.left ≫ D.famφB α k), ?_⟩
  exact (A.left.mem_basicOpen _ xx hm).2 hval

theorem exists_sec_nonzeroLocus_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R],
    IsAdicComplete (IsLocalRing.maximalIdeal R) R → ∀ (D : DegPre R) (α : D.X) (x : D.P.A.left),
    D.P.A.hom x = IsLocalRing.closedPoint R → ∃ σ : D.SecB 2 α, x ∈ nonzeroLocus σ := by
  intro R _ _ _ _ _ D α x hx
  let S := Spec (CommRingCat.of R)
  let tk : Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶ S :=
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
  let T : Over S := 𝟙_ (Over S)
  let ρ : Over.mk (tk ≫ T.hom) ⟶ Over.mk T.hom := Over.homMk tk rfl
  obtain ⟨y, hy⟩ : ∃ y : (Over.mk (tk ≫ T.hom) ⊗ D.P.A).left, (snd _ D.P.A).left y = x := by
    obtain ⟨p⟩ : Nonempty (Spec (CommRingCat.of (IsLocalRing.ResidueField R))) := inferInstance
    obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback (f := tk ≫ T.hom) (g := D.P.A.hom) p x (by
      rw [hx]; exact IsLocalRing.PrimeSpectrum.comap_residue R p)
    exact ⟨z, hz⟩
  have hg := GlobalTheory.T.exists_section_translateTensor_fibre_nonvanishing S D.P _ (tk ≫ T.hom) (ρ ≫ D.c α) y
  rw [← whisker_eq_twistLB] at hg
  obtain ⟨sb, hsb⟩ := hg
  obtain ⟨s, hs⟩ := (GlobalTheory.abelianSchemeLaws_all.2.secTwist S D.P 2 (by norm_num) R T.hom (D.c α)).2 sb
  have hz := mem_of_isPullSecLC D.P.L _ _ _ s sb hs y hsb
  obtain ⟨σ, hσ⟩ := transfer D α s _ hz
  refine ⟨σ, ?_⟩
  have e : (snd T D.P.A).left ((ρ ▷ D.P.A).left y) = x := by
    rw [← hy]
    have e' := congrArg (fun f => f.left.base y) (whiskerRight_snd ρ D.P.A)
    exact e'
  rwa [e] at hσ

end GlobalTheory.TwistGen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionTwistedLineBundleNonzeroClosedFibreStatement
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_twistedLineBundle_nonzero_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R], IsAdicComplete (IsLocalRing.maximalIdeal R) R → ∀ (D : DegPre R) (α : D.X) (x : D.P.A.left), D.P.A.hom x = IsLocalRing.closedPoint R → ∃ σ : D.SecB 2 α, x ∈ nonzeroLocus σ := by
  first | exact @GlobalTheory.TwistGen.exists_sec_nonzeroLocus_closedFibre | exact GlobalTheory.TwistGen.exists_sec_nonzeroLocus_closedFibre | (intros; apply GlobalTheory.TwistGen.exists_sec_nonzeroLocus_closedFibre <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBundleSectionUnitAtClosedPointTorusChart
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.SecConst


open ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic in
theorem exists_secB_isUnit_const : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r))) → ∀ (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.D.toPre.P.A.left) (c' : P.D.toPre.X → (Sp (DualNumber k) ⟶ B'.left)), IsGrpPullback B' P.D.toPre.P.A (spMap ρ) π₁ → IsGrpPullback B' P.D.toPre.P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → (∀ y, c' y ≫ B'.hom = 𝟙 _ ∧ c' y ≫ π₁ = spMap ρ ≫ (P.D.toPre.c y).left ∧ c' y ≫ π₂ = spMap (constHom ρ) ≫ (P.D.toPre.c y).left) → ∃ e₀ : ℕ, ∀ e : ℕ, e₀ ≤ e → ∀ mu α : P.D.toPre.X, ∃ σ : P.D.toPre.SecB e α, ∀ zz J, Good P.D.toPre.P.L zz J → IsUnit (sval σ (spMap (constHom ρ) ≫ (P.D.toPre.c mu).left) zz J) := by
  intro E _ _ _ H k _ _ m d t P gam _ _ _ Y n' v' dd _ D q _ h _ _ _ ρ hρ B' _ π₁ π₂ c' _ _ _ _
  refine ⟨6, fun e he mu al => ?_⟩
  have hpt : ∀ zz, (spMap (constHom ρ) ≫ (P.D.toPre.c mu).left) zz =
      (P.D.toPre.c mu).left (IsLocalRing.closedPoint (ChartRing k m d)) := by
    intro zz
    rw [Scheme.Hom.comp_apply]
    congr 1
    have key : ∀ r : ChartRing k m d,
        (constHom ρ) r = algebraMap k (DualNumber k) (MvPowerSeries.constantCoeff r) := by
      intro r
      simp [constHom, hρ r]
    apply PrimeSpectrum.ext
    ext r
    show (constHom ρ) r ∈ PrimeSpectrum.asIdeal (R := DualNumber k) zz ↔
      r ∈ IsLocalRing.maximalIdeal (ChartRing k m d)
    rw [key, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff,
      isUnit_iff_ne_zero, not_not]
    by_cases h0 : MvPowerSeries.constantCoeff r = 0
    · simp [h0, Ideal.zero_mem]
    · refine iff_of_false (fun hm => ?_) h0
      have hu : IsUnit (algebraMap k (DualNumber k) (MvPowerSeries.constantCoeff r)) :=
        (isUnit_iff_ne_zero.2 h0).map _
      exact (PrimeSpectrum.isPrime (R := DualNumber k) zz).ne_top (Ideal.eq_top_of_isUnit_mem _ hm hu)
  have hxc : P.D.toPre.P.A.hom ((P.D.toPre.c mu).left (IsLocalRing.closedPoint (ChartRing k m d))) =
      IsLocalRing.closedPoint (ChartRing k m d) := by
    show ((P.D.toPre.c mu).left ≫ P.D.toPre.P.A.hom) _ = _
    rw [Over.w (P.D.toPre.c mu)]
    rfl
  obtain ⟨σ₂, hσ₂⟩ := GlobalTheory.T.exists_section_twistedLineBundle_nonzero_closedFibre (ChartRing k m d) (GlobalTheory.MumfordChart.admissibleBase_chartRing k m d).2.2.2 P.D.toPre al _ hxc
  have hA := (GlobalTheory.abelianSchemeLaws_all).1.ample
  obtain ⟨N, s, hcov⟩ := (hA (Spec (CommRingCat.of (ChartRing k m d))) P.D.toPre.P (e - 2) (by omega)).1 ⊤
    (isAffineOpen_top _)
  obtain ⟨ρ', hρ'⟩ : ∃ ρ' : P.D.toPre.P.A.left ⟶ (P.D.toPre.P.A.hom ⁻¹ᵁ ⊤).toScheme,
      ρ' ≫ (P.D.toPre.P.A.hom ⁻¹ᵁ ⊤).ι = 𝟙 _ :=
    ⟨IsOpenImmersion.lift _ (𝟙 _) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      trivial), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1
    (show ρ' ((P.D.toPre.c mu).left (IsLocalRing.closedPoint (ChartRing k m d))) ∈ ⨆ i, nonzeroLocus (s i) by
      rw [hcov]; trivial)
  have hF : FormEq (Sum.elim (DegPre.famφB P.D.toPre al)
      (fun _ : Fin (e - 2) => ρ' ≫ (P.D.toPre.P.A.hom ⁻¹ᵁ ⊤).ι))
      (Sum.elim (DegPre.famε 2) (fun _ => 1)) (DegPre.famφB P.D.toPre al) (DegPre.famε e) := by
    intro U _ hh
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, hρ', Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, zpow_one, Fin.prod_univ_four]
    have e0 : DegPre.famφB P.D.toPre al 0 = 𝟙 _ := rfl
    have x0 : DegPre.famε 2 0 = 1 := by simp [DegPre.famε]
    have y0 : DegPre.famε e 0 = (e : ℤ) - 1 := rfl
    have x1 : DegPre.famε 2 1 = DegPre.famε e 1 := rfl
    have x2 : DegPre.famε 2 2 = DegPre.famε e 2 := rfl
    have x3 : DegPre.famε 2 3 = DegPre.famε e 3 := rfl
    rw [x0, y0, x1, x2, x3, e0, show (e : ℤ) - 1 = 1 + ((e - 2 : ℕ) : ℤ) by omega, zpow_add, zpow_natCast,
      zpow_one]
    ac_rfl
  obtain ⟨σ, hσ⟩ := exists_sec P.D.toPre.P.isLB hF (mulSec σ₂ (pullSec (s i) ρ'))
  refine ⟨σ, fun zz J hJ => ?_⟩
  rw [hσ _ _ zz J hJ, sval_mulSec _ _ _ zz hJ]
  erw [sval_pullSec (s i) ρ' _ zz hJ]
  refine IsUnit.mul ?_ ?_
  · obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hσ₂
    exact isUnit_sval σ₂ _ zz hJ j (by rw [hpt]; exact hj)
  · obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hi
    exact isUnit_sval (s i) _ zz hJ j (by rw [Scheme.Hom.comp_apply, hpt]; exact hj)

end GlobalTheory.SecConst
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBundleSectionUnitAtClosedPointTorusChartStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bundleSection_unit_at_closedPoint_torusChart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r))) → ∀ (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.D.toPre.P.A.left) (c' : P.D.toPre.X → (Sp (DualNumber k) ⟶ B'.left)), IsGrpPullback B' P.D.toPre.P.A (spMap ρ) π₁ → IsGrpPullback B' P.D.toPre.P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → (∀ y, c' y ≫ B'.hom = 𝟙 _ ∧ c' y ≫ π₁ = spMap ρ ≫ (P.D.toPre.c y).left ∧ c' y ≫ π₂ = spMap (constHom ρ) ≫ (P.D.toPre.c y).left) → ∃ e₀ : ℕ, ∀ e : ℕ, e₀ ≤ e → ∀ mu α : P.D.toPre.X, ∃ σ : P.D.toPre.SecB e α, ∀ zz J, Good P.D.toPre.P.L zz J → IsUnit (sval σ (spMap (constHom ρ) ≫ (P.D.toPre.c mu).left) zz J) := by
  first | exact @GlobalTheory.SecConst.exists_secB_isUnit_const | exact GlobalTheory.SecConst.exists_secB_isUnit_const | (intros; apply GlobalTheory.SecConst.exists_secB_isUnit_const <;> assumption)
end
