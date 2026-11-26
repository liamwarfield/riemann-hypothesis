module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineCharactersGivenJumpsUnramifiedTwists
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivExteriorTensorOfIrreducibleProdRep

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCuspidalJacquetModuleSecondBlockOfVanishing
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCuspidalJacquetModuleSecondBlockOfVanishing
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Topology

namespace GlobalTheory.JacMinCuspGL

open GlobalTheory.SmGL.CuspMax GlobalTheory.JacMinCusp Matrix

theorem isCuspidal_jac₂_inr : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (a b n : ℕ) (h : a + b = n) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π →
    (∀ (r t : ℕ) (h' : r + t = n), 0 < t → t < b → Subsingleton (Jacquet π (unipRad k (two (stdSum h'))))) →
    IsCuspidal (k := k) (n := Fin b) ((jac₂ (stdSum h) π).comp (MonoidHom.inr (GL (Fin a) k) (GL (Fin b) k))) := by
  intro k _ _ _ _ a b n h V _ _ π hπ hmin
  set J := (jac₂ (stdSum h) π).comp (MonoidHom.inr (GL (Fin a) k) (GL (Fin b) k)) with hJdef
  refine (isCuspidal_iff_maximal k b _ J).2 ⟨isSmooth_comp (isSmooth_jac₂ _ hπ) _
    (continuous_const.prodMk continuous_id :
      Continuous fun x : GL (Fin b) k => ((1 : GL (Fin a) k), x)),
    fun r t h' hr ht => ?_⟩
  have hcd : a + r + t = n := by omega
  have hJ : twKer π (unipRad k (two (stdSum hcd))) 1 = ⊤ :=
    Submodule.Quotient.subsingleton_iff.1 (hmin (a + r) t hcd ht (by omega))
  set Kab := twKer π (unipRad k (two (stdSum h))) 1 with hKab
  set K' := twKer J (unipRad k (two (stdSum h'))) 1 with hK'

  have hB : ∀ g : GL (Fin a) k × GL (Fin b) k, g.1 = 1 → GeneralLinearGroup.det g.2 = 1 → ∀ v : V,
      jac₂ (stdSum h) π g (Submodule.Quotient.mk v) =
        Submodule.Quotient.mk (π (leviEmb k (two (stdSum h)) (leviTwo k _ _ g)) v) := by
    intro g h1 h2 v
    have hd : deltaHalf k (Two (Fin a) (Fin b)) (leviTwo k _ _ g) = 1 := by
      rw [deltaHalf_two, h1, h2]; simp
    show GlobalTheory.SmGL.jac (two (stdSum h)) π (leviTwo k _ _ g) _ = _
    rw [jac_mk, hd]; simp
  have hN : ∀ u ∈ unipRad k (two (stdSum h)), ∀ v : V,
      (Submodule.Quotient.mk (π u v) : V ⧸ Kab) = Submodule.Quotient.mk v := by
    intro u hu v
    exact (Submodule.Quotient.eq Kab).2 (Submodule.subset_span ⟨⟨u, hu⟩, v, by simp⟩)

  have hC : ∀ u ∈ unipRad k (two (stdSum hcd)), ∀ v : V,
      (Submodule.Quotient.mk (π u v) : V ⧸ Kab) - Submodule.Quotient.mk v ∈ K' := by
    intro u hu v
    have hu' := (mem_unipRad_two_iff hcd).1 hu
    have hp : u ∈ parab k (two (stdSum h)) := by
      rw [mem_parab]
      intro i j hij
      rw [blk_two_stdSum_lt] at hij
      rw [hu' i j (by omega), Matrix.one_apply_ne]
      intro hij'; subst hij'; omega
    obtain ⟨n', hn', hun⟩ := exists_levi_mul_unip k (two (stdSum h)) ⟨u, hp⟩
    set g := (leviTwo k (Fin a) (Fin b)).symm (leviProj k (two (stdSum h)) ⟨u, hp⟩) with hg
    have hlg : leviTwo k _ _ g = leviProj k (two (stdSum h)) ⟨u, hp⟩ := by simp [g]
    have hg1 : g.1 = 1 := by
      ext i j
      show (leviProj k (two (stdSum h)) ⟨u, hp⟩ false : Matrix (Fin a) (Fin a) k) i j = _
      rw [leviProj_apply, two_false, two_false]
      rw [hu' _ _ (by simp; omega)]
      simp [Matrix.one_apply, stdSum]
    have hg2 : g.2 ∈ unipRad k (two (stdSum h')) := by
      rw [mem_unipRad_two_iff]
      intro i j hij
      show (leviProj k (two (stdSum h)) ⟨u, hp⟩ true : Matrix (Fin b) (Fin b) k) i j = _
      rw [leviProj_apply, two_true, two_true]
      rw [hu' _ _ (by simp; omega)]
      simp [Matrix.one_apply, stdSum]
    have hdet : GeneralLinearGroup.det g.2 = 1 := det_eq_one_of_mem_unipRad k hg2
    have hu_eq : u = leviEmb k (two (stdSum h)) (leviTwo k _ _ g) * n' := by rw [hlg]; exact hun
    have hJu : J g.2 (Submodule.Quotient.mk v) = Submodule.Quotient.mk (π u v) := by
      rw [hu_eq, map_mul, Module.End.mul_apply]
      show jac₂ (stdSum h) π (1, g.2) _ = _
      rw [hB (1, g.2) rfl hdet, show ((1, g.2) : GL (Fin a) k × GL (Fin b) k) = g from Prod.ext hg1.symm rfl]
      refine (Submodule.Quotient.eq Kab).2 ?_
      rw [← map_sub]
      refine twKer_le_comap π _ _ (leviEmb_mem_normalizer k _ _) ?_
      have := (Submodule.Quotient.eq Kab).1 (hN n' hn' v)
      rw [← neg_sub]
      exact Kab.neg_mem this
    rw [← hJu]
    exact Submodule.subset_span ⟨⟨g.2, hg2⟩, Submodule.Quotient.mk v, by simp⟩
  refine Submodule.Quotient.subsingleton_iff.2 (eq_top_iff.2 fun x _ => ?_)
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective Kab x
  have hle : twKer π (unipRad k (two (stdSum hcd))) 1 ≤ K'.comap Kab.mkQ := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, w, rfl⟩
    simpa [Submodule.mkQ_apply] using hC u u.2 w
  exact hle (hJ ▸ Submodule.mem_top)

end GlobalTheory.JacMinCuspGL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCuspidalJacquetModuleSecondBlockOfVanishingStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCuspidal_jacquetModule_second_block_of_vanishing : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b n : ℕ) (h : a + b = n) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → (∀ (r t : ℕ) (h' : r + t = n), 0 < t → t < b → Subsingleton (Jacquet π (unipRad k (two (stdSum h'))))) → IsCuspidal (k := k) (n := Fin b) ((jac₂ (stdSum h) π).comp (MonoidHom.inr (GL (Fin a) k) (GL (Fin b) k))) := by
  first | exact @GlobalTheory.JacMinCuspGL.isCuspidal_jac₂_inr | exact GlobalTheory.JacMinCuspGL.isCuspidal_jac₂_inr | (intros; apply GlobalTheory.JacMinCuspGL.isCuspidal_jac₂_inr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetNontrivial
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
open GlobalTheory.PRep GlobalTheory.SmGL

namespace GlobalTheory.SmGL.JacquetEmptyFirstBlock

theorem jacquet_nontrivial : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V),
    π.IsIrreducible → ∀ (h : 0 + n = n), Nontrivial (Jacquet π (unipRad k (two (stdSum h)))) := by
  intro k _ _ _ _ n V _ _ π hπ h
  have key : ∀ x, GlobalTheory.SmGL.blk (two (stdSum h)) x = true := by
    intro x
    unfold GlobalTheory.SmGL.blk
    obtain ⟨⟨b, y⟩, hy⟩ : ∃ p, (two (stdSum h)).symm x = p := ⟨_, rfl⟩
    rw [hy]
    cases b
    · exact Fin.elim0 y
    · rfl
  have hbot : unipRad k (two (stdSum h)) = ⊥ := by
    by_contra hne
    obtain ⟨i, j, hij⟩ := (GlobalTheory.SmGL.CuspMax.unipRad_ne_bot_iff).1 hne
    rw [key i, key j] at hij
    exact lt_irrefl _ hij
  have hker : twKer π (⊥ : Subgroup (GL (Fin n) k)) 1 = ⊥ := by
    unfold twKer
    rw [Submodule.span_eq_bot]
    rintro w ⟨⟨g, hg⟩, v, rfl⟩
    rw [Subgroup.mem_bot] at hg
    subst hg
    simp
  have hV : Nontrivial V := by
    by_contra hV
    rw [not_nontrivial_iff_subsingleton] at hV
    have : IsSimpleOrder (Subrepresentation π) := hπ
    exact (bot_ne_top : (⊥ : Subrepresentation π) ≠ ⊤)
      (Subrepresentation.ext (Subsingleton.elim _ _))
  rw [hbot]
  show Nontrivial (V ⧸ twKer π ⊥ 1)
  rw [hker]
  exact (Submodule.quotEquivOfEqBot (⊥ : Submodule ℂ V) rfl).toEquiv.nontrivial

end GlobalTheory.SmGL.JacquetEmptyFirstBlock
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitarisableComplexRepOfSupercuspidalUnitaryCeStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnitarisableComplexRep_of_supercuspidal_unitary_center : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (l : Module.Dual ℂ V), l ∈ smoothPart ρ.dual → l ≠ 0 → ρ.IsIrreducible → IsSupercuspidal ρ → (∀ z ∈ Subgroup.center G, ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ v, ρ z v = c • v) → IsUnitarisable ρ := by
  first | exact @GlobalTheory.isUnitarisable_of_isSupercuspidal | exact GlobalTheory.isUnitarisable_of_isSupercuspidal | (intros; apply GlobalTheory.isUnitarisable_of_isSupercuspidal <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedJacquetTwoBlocksFinitelyGenerated
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanOrbitEqTop
namespace GlobalTheory.SpanOrbitTop

theorem span_orbit_eq_top {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ G V) (hπ : Representation.IsIrreducible π) {v : V} (hv : v ≠ 0) :
    Submodule.span ℂ (Set.range fun g : G ↦ π g v) = ⊤ := by
  have hinv : ∀ (h : G) ⦃x : V⦄, x ∈ Submodule.span ℂ (Set.range fun g : G ↦ π g v) →
      π h x ∈ Submodule.span ℂ (Set.range fun g : G ↦ π g v) := by
    intro h x hx
    have hle : (Submodule.span ℂ (Set.range fun g : G ↦ π g v)).map (π h) ≤
        Submodule.span ℂ (Set.range fun g : G ↦ π g v) := by
      rw [Submodule.map_span_le]
      rintro _ ⟨g, rfl⟩
      exact Submodule.subset_span ⟨h * g, by simp [map_mul]⟩
    exact hle (Submodule.mem_map_of_mem hx)
  let S : Subrepresentation π := ⟨Submodule.span ℂ (Set.range fun g : G ↦ π g v), hinv⟩
  have hvS : v ∈ S.toSubmodule := Submodule.subset_span ⟨1, by simp⟩
  have := hπ
  rcases eq_bot_or_eq_top S with h | h
  · exfalso
    have hb : v ∈ (⊥ : Subrepresentation π).toSubmodule := h ▸ hvS
    exact hv ((Submodule.mem_bot ℂ).mp hb)
  · exact congrArg Subrepresentation.toSubmodule h

end GlobalTheory.SpanOrbitTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedJacquetTwoBlocksFinitelyGenerated
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Topology

namespace GlobalTheory.JacquetFinGen

theorem span_orbit_eq_top {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ G V) (hπ : π.IsIrreducible) {v : V} (hv : v ≠ 0) :
    Submodule.span ℂ (Set.range fun g : G => π g v) = ⊤ := by
  first
  | exact @_root_.GlobalTheory.SpanOrbitTop.span_orbit_eq_top
  | exact _root_.GlobalTheory.SpanOrbitTop.span_orbit_eq_top
  | (apply _root_.GlobalTheory.SpanOrbitTop.span_orbit_eq_top <;> assumption)
  | (intros; apply _root_.GlobalTheory.SpanOrbitTop.span_orbit_eq_top <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SpanOrbitTop.span_orbit_eq_top <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SpanOrbitTop.span_orbit_eq_top ..)

theorem jacquet_fg : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (a b n : ℕ) (h : a + b = n) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → π.IsIrreducible →
    ∃ s : Finset (Jacquet π (unipRad k (two (stdSum h)))),
      Submodule.span ℂ {w | ∃ g : GL (Fin a) k × GL (Fin b) k, ∃ v ∈ s, w = jac₂ (stdSum h) π g v} = ⊤ := by
  intro k _ _ _ _ a b n h V _ _ π hsm hirr
  classical
  haveI := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hirr
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  set e := stdSum h
  set N := unipRad k (two e)
  have hO := GlobalTheory.SmoothRiesz.finite_orbit π hsm (KO k (Fin n)) (GlobalTheory.SplitFlip.isCompact_KO (k := k) (n := Fin n)) v
  let s : Finset (Jacquet π N) := hO.toFinset.image (Submodule.Quotient.mk (p := twKer π N 1))
  refine ⟨s, ?_⟩
  set T := {w | ∃ g : GL (Fin a) k × GL (Fin b) k, ∃ x ∈ s, w = jac₂ e π g x}
  have key : ∀ g : GL (Fin n) k,
      (Submodule.Quotient.mk (π g v) : Jacquet π N) ∈ Submodule.span ℂ T := by
    intro g
    obtain ⟨p, w, hw, rfl⟩ := GlobalTheory.SmGL.MultiIrr.exists_parab_mul (two e) g
    obtain ⟨u, hu, hp⟩ := exists_levi_mul_unip k (two e) p
    set m := leviProj k (two e) p
    set y := π w v
    have hy : Submodule.Quotient.mk (p := twKer π N 1) y ∈ s :=
      Finset.mem_image.2 ⟨y, hO.mem_toFinset.2 ⟨w, hw, rfl⟩, rfl⟩
    have hu' : (Submodule.Quotient.mk (π u y) : Jacquet π N) = Submodule.Quotient.mk y := by
      rw [Submodule.Quotient.eq]
      exact Submodule.subset_span ⟨⟨u, hu⟩, y, by simp⟩
    have h1 : π (↑p * w) v = π (leviEmb k (two e) m) (π u y) := by
      rw [hp]; simp only [map_mul, Module.End.mul_apply, y]
    have h2 : (Submodule.Quotient.mk (π (leviEmb k (two e) m) (π u y)) : Jacquet π N) =
        ((deltaHalf k _ m : ℂˣ) : ℂ) • jac₂ e π ((leviTwo k (Fin a) (Fin b)).symm m)
          (Submodule.Quotient.mk y) := by
      show _ = _ • GlobalTheory.SmGL.jac (two e) π (leviTwo k (Fin a) (Fin b) ((leviTwo k (Fin a) (Fin b)).symm m)) _
      rw [MulEquiv.apply_symm_apply, ← hu', jac_mk, smul_smul, Units.mul_inv, one_smul]
    rw [h1, h2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, _, hy, rfl⟩)
  have hle : Submodule.span ℂ (Set.range fun g : GL (Fin n) k => π g v) ≤
      (Submodule.span ℂ T).comap (twKer π N 1).mkQ :=
    Submodule.span_le.2 (by rintro _ ⟨g, rfl⟩; exact key g)
  rw [GlobalTheory.JacquetFinGen.span_orbit_eq_top π hirr hv, top_le_iff] at hle
  rw [eq_top_iff]
  rintro x -
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have : y ∈ (Submodule.span ℂ T).comap (twKer π N 1).mkQ := hle ▸ Submodule.mem_top
  exact this

end GlobalTheory.JacquetFinGen
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedJacquetTwoBlocksFinitelyGeneratedStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalizedJacquetTwoBlocks_finitelyGenerated : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b n : ℕ) (h : a + b = n) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → π.IsIrreducible → ∃ s : Finset (Jacquet π (unipRad k (two (stdSum h)))), Submodule.span ℂ {w | ∃ g : GL (Fin a) k × GL (Fin b) k, ∃ v ∈ s, w = jac₂ (stdSum h) π g v} = ⊤ := by
  first | exact @GlobalTheory.JacquetFinGen.jacquet_fg | exact GlobalTheory.JacquetFinGen.jacquet_fg | (intros; apply GlobalTheory.JacquetFinGen.jacquet_fg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIrreducibleQuotientFinitelyGeneratedRep
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIrreducibleQuotientFinitelyGeneratedRep
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Topology

namespace GlobalTheory.IrrQuot

theorem main : ∀ (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (s : Finset V), Nontrivial V → Submodule.span ℂ {w | ∃ g : G, ∃ v ∈ s, w = ρ g v} = ⊤ → ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (τ : Representation ℂ G W), τ.IsIrreducible ∧ ∃ f : ρ.IntertwiningMap τ, Function.Surjective f := by
  intro G V _ _ _ ρ s hV hspan
  have key : ∀ T : Subrepresentation ρ, (∀ v ∈ s, v ∈ T.toSubmodule) → T = ⊤ := by
    intro T hT
    apply Subrepresentation.toSubmodule_injective
    refine eq_top_iff.2 ?_
    rw [← hspan]
    refine Submodule.span_le.2 ?_
    rintro w ⟨g, v, hv, rfl⟩
    exact T.apply_mem_toSubmodule g (hT v hv)
  haveI : Module.Finite (MonoidAlgebra ℂ G) ρ.asModule := by
    let t : Finset ρ.asModule := s
    refine ⟨⟨t, ?_⟩⟩
    have h := key (Subrepresentation.ofSubmodule' (Submodule.span (MonoidAlgebra ℂ G) (t : Set ρ.asModule)))
      (fun v hv => Submodule.subset_span (R := MonoidAlgebra ℂ G) (s := (t : Set ρ.asModule)) hv)
    refine eq_top_iff.2 fun x _ => ?_
    have hx : x ∈ Subrepresentation.ofSubmodule' (Submodule.span (MonoidAlgebra ℂ G) (t : Set ρ.asModule)) := by
      rw [h]; trivial
    exact hx
  haveI : IsCoatomic (Subrepresentation ρ) :=
    (OrderIso.isCoatomic_iff Subrepresentation.subrepresentationSubmoduleOrderIso).2 inferInstance
  have hbt : (⊥ : Subrepresentation ρ) ≠ ⊤ := by
    intro h
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have : v ∈ (⊤ : Subrepresentation ρ).toSubmodule := trivial
    rw [← h] at this
    exact hv this
  obtain ⟨M, hM, -⟩ := (eq_top_or_exists_le_coatom (⊥ : Subrepresentation ρ)).resolve_left hbt
  refine ⟨_, inferInstance, inferInstance, GlobalTheory.SmGL.subQuot ⊤ M, GlobalTheory.SmGL.isIrreducible_subQuot hM.covBy_top, ?_⟩
  refine ⟨⟨(Submodule.mkQ _).comp (LinearMap.codRestrict (⊤ : Subrepresentation ρ).toSubmodule LinearMap.id (fun _ => trivial)), fun g => rfl⟩, ?_⟩
  intro y
  obtain ⟨⟨v, _⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  exact ⟨v, rfl⟩

end GlobalTheory.IrrQuot
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIrreducibleQuotientFinitelyGeneratedRepStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_irreducible_quotient_finitelyGenerated_rep : ∀ (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (s : Finset V), Nontrivial V → Submodule.span ℂ {w | ∃ g : G, ∃ v ∈ s, w = ρ g v} = ⊤ → ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (τ : Representation ℂ G W), τ.IsIrreducible ∧ ∃ f : ρ.IntertwiningMap τ, Function.Surjective f := by
  first | exact @GlobalTheory.IrrQuot.main | exact GlobalTheory.IrrQuot.main | (intros; apply GlobalTheory.IrrQuot.main <;> assumption)
end
end

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Topology

namespace GlobalTheory.JacFactor

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isCuspidal_of_isSubquotient {n V W : Type} [Fintype n] [DecidableEq n] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {π : Representation ℂ (GL n k) V} {τ : Representation ℂ (GL n k) W}
    (hτ : IsCuspidal τ) (h : IsSubquotient π τ) : IsCuspidal π := by
  refine ⟨h.isSmooth hτ.1, fun s d e he => ?_⟩
  obtain ⟨S, f, hf⟩ := GlobalTheory.JacquetExact.isSubquotient_jac e hτ.1 h
  haveI := hτ.2 s d e he
  exact hf.subsingleton

theorem exists_root_norm {ω : kˣ →* ℂˣ} (hω : IsSmoothChar ω) {b : ℕ} (hb : 0 < b) :
    ∃ ψ : kˣ →* ℂˣ, IsSmoothChar ψ ∧ ∀ z, ‖((ω * ψ ^ b) z : ℂ)‖ = 1 := by
  let f : kˣ →* ℂ :=
    { toFun := fun z => ((‖(ω z : ℂ)‖ ^ (-(b : ℝ)⁻¹) : ℝ) : ℂ)
      map_one' := by simp
      map_mul' := fun x y => by
        rw [map_mul, Units.val_mul, norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _), Complex.ofReal_mul] }
  refine ⟨f.toHomUnits, Subgroup.isOpen_mono (H₁ := ω.ker) (fun z hz => ?_) hω, fun z => ?_⟩
  · refine Units.ext ?_
    have hz' : ω z = 1 := hz
    show ((‖(ω z : ℂ)‖ ^ (-(b : ℝ)⁻¹) : ℝ) : ℂ) = 1
    rw [hz']; simp
  · have h0 : 0 < ‖(ω z : ℂ)‖ := norm_pos_iff.2 (Units.ne_zero _)
    have e : ((f.toHomUnits z : ℂˣ) : ℂ) = ((‖(ω z : ℂ)‖ ^ (-(b : ℝ)⁻¹) : ℝ) : ℂ) := rfl
    rw [MonoidHom.mul_apply, MonoidHom.pow_apply, Units.val_mul, Units.val_pow_eq_pow_val, e, norm_mul, norm_pow,
      Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg h0.le _), ← Real.rpow_natCast, ← Real.rpow_mul h0.le,
      neg_mul, inv_mul_cancel₀ (by positivity), Real.rpow_neg_one, mul_inv_cancel₀ h0.ne']

theorem exists_irreducible_sub {b : ℕ} (hb : 0 < b) {X : Type} [AddCommGroup X] [Module ℂ X] [Nontrivial X]
    (τ : Representation ℂ (GL (Fin b) k) X) (hτ : IsCuspidal τ)
    (hz : ∀ z ∈ Subgroup.center (GL (Fin b) k), ∃ c : ℂ, ∀ w, τ z w = c • w) :
    ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (ρ : Representation ℂ (GL (Fin b) k) Y),
      ρ.IsIrreducible ∧ IsCuspidal ρ ∧ ∃ ι : Y →ₗ[ℂ] X, ι ≠ 0 ∧ ∀ g v, ι (ρ g v) = τ g (ι v) := by
  classical
  obtain ⟨x, hx⟩ := exists_ne (0 : X)
  let S : Subrepresentation τ := ⟨Submodule.span ℂ (Set.range fun g => τ g x), fun g v hv => by
    have hle : Submodule.span ℂ (Set.range fun g => τ g x) ≤
        (Submodule.span ℂ (Set.range fun g => τ g x)).comap (τ g) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨g', rfl⟩
      exact Submodule.subset_span ⟨g * g', by simp⟩
    exact hle hv⟩
  have hxS : x ∈ S.toSubmodule := Submodule.subset_span ⟨1, by simp⟩
  have hnt : Nontrivial S.toSubmodule := ⟨⟨⟨x, hxS⟩, 0, fun h => hx (congrArg Subtype.val h)⟩⟩
  obtain ⟨Y, _, _, ρ, hρi, p, hp⟩ := GlobalTheory.T.exists_irreducible_quotient_finitelyGenerated_rep _ _ S.toRepresentation {⟨x, hxS⟩} hnt (by
    refine Submodule.map_injective_of_injective S.toSubmodule.injective_subtype ?_
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype]
    show _ = Submodule.span ℂ (Set.range fun g => τ g x)
    congr 1
    ext y
    constructor
    · rintro ⟨_, ⟨g, v, hv, rfl⟩, rfl⟩
      rw [Finset.mem_singleton.1 hv]
      exact ⟨g, rfl⟩
    · rintro ⟨g, rfl⟩
      exact ⟨_, ⟨g, _, Finset.mem_singleton_self _, rfl⟩, rfl⟩)
  have hρc : IsCuspidal ρ := isCuspidal_of_isSubquotient hτ ⟨S, p, hp⟩
  have hSs : IsSmooth S.toRepresentation :=
    IsSubquotient.isSmooth ⟨S, Representation.IntertwiningMap.id _, Function.surjective_id⟩ hτ.1
  obtain ⟨ω, hω, hωc⟩ := GlobalTheory.LocGL.exists_smooth_hasCentralChar hρc.1 hρi
  obtain ⟨ψ, hψ, hψ1⟩ := exists_root_norm hω hb
  have hc' : IsCuspidal (GlobalTheory.SmGL.twist ρ (detChar (Fin b) ψ)) := GlobalTheory.LocGL.isCuspidal_twist hρc hψ
  have hsc := GlobalTheory.CuspCoef.isSupercuspidal_of_isCuspidal k b Y _ hc'
  haveI : Nontrivial Y := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hρi
  obtain ⟨y, hy⟩ := exists_ne (0 : Y)
  obtain ⟨l, hl, hly⟩ := GlobalTheory.T.exists_smoothDual_ne_zero_at_vector _ _ (GlobalTheory.SmGL.twist ρ (detChar (Fin b) ψ)) (fun U hU => by
    obtain ⟨γ, hγ, h⟩ := GlobalTheory.CentralExponent.exists_cong_subset (n := Fin b) hU
    exact ⟨_, GlobalTheory.CentralExponent.isOpen_cong γ hγ, GlobalTheory.CentralExponent.isCompact_cong γ hγ, h⟩) hc'.1 y hy
  have hu := GlobalTheory.T.isUnitarisableComplexRep_of_supercuspidal_unitary_center _ _ _ l hl (fun h => hly (by rw [h]; rfl)) (GlobalTheory.LocGL.isIrreducible_twist hρi _) hsc
    (fun z hz => by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz
      obtain ⟨z, rfl⟩ := hz
      have h := GlobalTheory.LocGL.hasCentralChar_twist hωc ψ z
      rw [Fintype.card_fin] at h
      exact ⟨_, hψ1 z, h⟩)
  obtain ⟨ι, hι⟩ := GlobalTheory.T.exists_nonzero_intertwiningMap_from_unitary_supercuspidal _ _ _ (GlobalTheory.SmGL.twist S.toRepresentation (detChar (Fin b) ψ)) _ (twistMap p _)
    (isSmooth_twist hSs hψ.detChar) hsc hu
    (fun z hz' => by
      obtain ⟨c, hc⟩ := hz z hz'
      refine ⟨(detChar (Fin b) ψ z : ℂ) * c, fun w => ?_⟩
      rw [twist_apply, mul_smul]
      exact congrArg _ (Subtype.ext (hc w)))
    (fun h => by
      obtain ⟨w, hw⟩ := hp y
      have h1 : twistMap p (detChar (Fin b) ψ) w = y := hw
      rw [h] at h1
      exact hy h1.symm)
  refine ⟨Y, _, _, ρ, hρi, hρc, S.toSubmodule.subtype ∘ₗ ι.toLinearMap, fun h => hι ?_, fun g v => ?_⟩
  · ext v
    exact LinearMap.congr_fun h v
  · have h1 := Representation.IntertwiningMap.isIntertwining _ _ ι g v
    rw [twist_apply, twist_apply, map_smul] at h1
    exact congrArg Subtype.val (smul_right_injective _ (Units.ne_zero _) h1)

theorem exists_map_jac₂ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V)
    (hs : IsSmooth π) (hi : π.IsIrreducible) (hn : 0 < n) :
    ∃ (a b : ℕ) (h : a + b = n) (W W' : Type) (_ : AddCommGroup W) (_ : Module ℂ W)
      (_ : AddCommGroup W') (_ : Module ℂ W')
      (σ : Representation ℂ (GL (Fin a) k) W) (ρ : Representation ℂ (GL (Fin b) k) W'),
      0 < b ∧ IsSmooth σ ∧ σ.IsIrreducible ∧ IsSmooth ρ ∧ ρ.IsIrreducible ∧ IsCuspidal ρ ∧
      ∃ φ : (jac₂ (stdSum h) π).IntertwiningMap (extTensor σ ρ), φ ≠ 0 := by
  classical
  have hex : ∃ b : ℕ, 0 < b ∧ ∃ (a : ℕ) (h : a + b = n), Nontrivial (Jacquet π (unipRad k (two (stdSum h)))) :=
    ⟨n, hn, 0, zero_add n, GlobalTheory.SmGL.JacquetEmptyFirstBlock.jacquet_nontrivial k n V π hi _⟩
  obtain ⟨hb, a, h, hnt⟩ := Nat.find_spec hex
  have hmin := fun t (ht : t < Nat.find hex) => Nat.find_min hex ht
  generalize Nat.find hex = b at hb h hnt hmin
  have hJc := GlobalTheory.T.isCuspidal_jacquetModule_second_block_of_vanishing k a b n h V π hs fun r t h' h0 ht =>
    not_nontrivial_iff_subsingleton.1 fun h1 => hmin t ht ⟨h0, r, h', h1⟩
  obtain ⟨s, hspan⟩ := GlobalTheory.T.normalizedJacquetTwoBlocks_finitelyGenerated k a b n h V π hs hi
  obtain ⟨X, _, _, τ, hτi, f, hf⟩ := GlobalTheory.T.exists_irreducible_quotient_finitelyGenerated_rep _ _ _ s hnt hspan
  have hτs : IsSmooth τ := (IsSubquotient.of_surjective f hf).isSmooth (isSmooth_jac₂ _ hs)
  have hτc : IsCuspidal (k := k) (n := Fin b) (τ.comp (MonoidHom.inr _ _)) :=
    isCuspidal_of_isSubquotient hJc (IsSubquotient.of_surjective (compMap f _) hf)
  haveI : Nontrivial X := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hτi
  haveI := GlobalTheory.LocGL.secondCountableTopology_GL k (Fin a)
  haveI := GlobalTheory.LocGL.secondCountableTopology_GL k (Fin b)
  obtain ⟨Y, _, _, ρ, hρi, hρc, hι⟩ := exists_irreducible_sub hb (τ.comp (MonoidHom.inr _ _)) hτc fun z hz =>
    GlobalTheory.LocGL.exists_eq_smul_of_isSmooth hτs hτi ⟨τ (1, z), fun g => by
      rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, ← map_mul, ← map_mul]
      congr 1
      exact Prod.ext (by simp) (Subgroup.mem_center_iff.1 hz g.2).symm⟩
  obtain ⟨W, _, _, σ, hσs, hσi, ⟨φ⟩⟩ := GlobalTheory.T.exists_equiv_exteriorTensor_of_irreducible_prod_rep _ _ X Y τ ρ hτs hτi hρi
    (GlobalTheory.T.injective_tensor_lift_equivariant_maps_of_irreducible _ X Y (τ.comp (MonoidHom.inr _ _)) ρ hρi (GlobalTheory.LocGL.schur_GL hρc.1 hρi)) hι
  refine ⟨a, b, h, W, Y, _, _, _, _, σ, ρ, hb, hσs, hσi, hρc.1, hρi, hρc, φ.toIntertwiningMap.comp f, fun h0 => ?_⟩
  obtain ⟨x, hx⟩ := exists_ne (0 : X)
  obtain ⟨w, rfl⟩ := hf x
  have h1 : φ (f w) = 0 := congrArg (fun F => F w) h0
  exact hx ((map_eq_zero_iff φ φ.injective).1 h1)

end GlobalTheory.JacFactor
