module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestFunctionsTransportLocalLatticeIsometries
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberZeroSmallImage

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInequivalentRepresentativesThroughMember
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInequivalentRepresentativesThroughMember
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S

namespace GlobalTheory.TrUnion

theorem exists_reps_through : ∀ (G : Type) [Group G] [TopologicalSpace G] (m : ℕ) (W : Fin m → Type) [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)] (σ : ∀ i, Representation ℂ G (W i)), ∀ i₀ : Fin m, ∃ (n : ℕ) (s : Fin n → Fin m), (∀ i j, i ≠ j → IsEmpty ((σ (s i)).Equiv (σ (s j)))) ∧ (∃ j, s j = i₀) ∧ ∀ i, ∃ j, Nonempty ((σ i).Equiv (σ (s j))) := by
  intro G _ _ m W _ _ σ i₀
  classical
  let R : Fin m → Fin m → Prop := fun i j => Nonempty ((σ i).Equiv (σ j))
  have hrefl : ∀ i, R i i := fun i => ⟨Representation.Equiv.refl _⟩
  have hsymm : ∀ {i j}, R i j → R j i := fun ⟨e⟩ => ⟨e.symm⟩
  have htrans : ∀ {i j k}, R i j → R j k → R i k := fun ⟨e⟩ ⟨e'⟩ => ⟨e.trans e'⟩
  let S : Setoid (Fin m) := ⟨R, ⟨hrefl, hsymm, htrans⟩⟩
  let f : Fin m → Fin m := fun i => if R i i₀ then i₀ else (Quotient.mk S i).out
  have hf : ∀ i, R (f i) i := by
    intro i
    by_cases h : R i i₀
    · simp only [f, if_pos h]; exact hsymm h
    · simp only [f, if_neg h]; exact Quotient.mk_out (s := S) i
  have hfc : ∀ i j, R i j → f i = f j := by
    intro i j hij
    by_cases h : R i i₀
    · have h' : R j i₀ := htrans (hsymm hij) h
      simp only [f, if_pos h, if_pos h']
    · have h' : ¬ R j i₀ := fun h' => h (htrans hij h')
      simp only [f, if_neg h, if_neg h']
      rw [Quotient.sound (s := S) hij]
  let T : Finset (Fin m) := Finset.univ.image f
  let e : T ≃ Fin T.card := T.equivFin
  refine ⟨T.card, fun k => (e.symm k).1, ?_, ?_, ?_⟩
  · intro k l hkl
    refine ⟨fun hR => ?_⟩
    apply hkl
    obtain ⟨x, -, hx⟩ := Finset.mem_image.1 (e.symm k).2
    obtain ⟨y, -, hy⟩ := Finset.mem_image.1 (e.symm l).2
    have hxy : R x y := by
      have h1 : R (f x) (f y) := by rw [hx, hy]; exact ⟨hR⟩
      exact htrans (hsymm (hf x)) (htrans h1 (hf y))
    have : (e.symm k).1 = (e.symm l).1 := by rw [← hx, ← hy]; exact hfc x y hxy
    exact e.symm.injective (Subtype.ext this)
  · have hmem : i₀ ∈ T := Finset.mem_image.2 ⟨i₀, Finset.mem_univ _, by simp only [f, if_pos (hrefl i₀)]⟩
    exact ⟨e ⟨i₀, hmem⟩, by simp⟩
  · intro i
    have hmem : f i ∈ T := Finset.mem_image_of_mem f (Finset.mem_univ i)
    refine ⟨e ⟨f i, hmem⟩, ?_⟩
    show R i (e.symm (e ⟨f i, hmem⟩)).1
    rw [Equiv.symm_apply_apply]
    exact hsymm (hf i)

end GlobalTheory.TrUnion
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInequivalentRepresentativesThroughMemberStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inequivalentRepresentatives_through_member : ∀ (G : Type) [Group G] [TopologicalSpace G] (m : ℕ) (W : Fin m → Type) [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)] (σ : ∀ i, Representation ℂ G (W i)), ∀ i₀ : Fin m, ∃ (n : ℕ) (s : Fin n → Fin m), (∀ i j, i ≠ j → IsEmpty ((σ (s i)).Equiv (σ (s j)))) ∧ (∃ j, s j = i₀) ∧ ∀ i, ∃ j, Nonempty ((σ i).Equiv (σ (s j))) := by
  first | exact @GlobalTheory.TrUnion.exists_reps_through | exact GlobalTheory.TrUnion.exists_reps_through | (intros; apply GlobalTheory.TrUnion.exists_reps_through <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RepresentationTransportTopGroupEquiv
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RepresentationTransportTopGroupEquiv
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S
namespace GlobalTheory.TransportIso

theorem irreducible_admissible_integralOp_transport : ∀ (G G' : Type) [Group G] [Group G'] [TopologicalSpace G] [TopologicalSpace G'] [MeasurableSpace G] [BorelSpace G] [MeasurableSpace G'] [BorelSpace G'] (Φ : G ≃ₜ* G') (ν : Measure G) (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G W), (σ.IsIrreducible → Representation.IsIrreducible (σ.comp Φ.symm.toMulEquiv.toMonoidHom)) ∧ (IsAdmissible σ → IsAdmissible (σ.comp Φ.symm.toMulEquiv.toMonoidHom : Representation ℂ G' W)) ∧ ∀ (f : G → ℂ) (f' : G' → ℂ), (∀ g, f' (Φ g) = f g) → ∀ A, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp (ν.map Φ) (σ.comp Φ.symm.toMulEquiv.toMonoidHom : Representation ℂ G' W) f' A ↔ GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ f A := by
  intro G G' _ _ _ _ _ _ _ _ Φ ν W _ _ σ
  have hs : ∀ g' : G', Φ.symm.toMulEquiv g' = Φ.symm g' := fun _ => rfl
  have hs2 : ∀ g' : G', Φ.symm.toMulEquiv.toMonoidHom g' = Φ.symm g' := fun _ => rfl
  have hcomp' : ∀ g' : G', (σ.comp Φ.symm.toMulEquiv.toMonoidHom) g' = σ (Φ.symm g') := fun _ => rfl
  have hcomp : ∀ g : G, (σ.comp Φ.symm.toMulEquiv.toMonoidHom) (Φ g) = σ g := by
    intro g; rw [hcomp', Φ.symm_apply_apply]
  refine ⟨?_, ?_, ?_⟩
  · intro hσ
    let e : Subrepresentation (σ.comp Φ.symm.toMulEquiv.toMonoidHom) ≃o Subrepresentation σ :=
      { toFun := fun U => ⟨U.toSubmodule, fun g v hv => by
          have := U.apply_mem_toSubmodule (Φ g) hv
          rwa [hcomp] at this⟩
        invFun := fun U => ⟨U.toSubmodule, fun g' v hv => by
          rw [hcomp']
          exact U.apply_mem_toSubmodule _ hv⟩
        left_inv := fun U => rfl
        right_inv := fun U => rfl
        map_rel_iff' := Iff.rfl }
    exact e.isSimpleOrder
  · rintro ⟨hsm, hfd⟩
    refine ⟨?_, ?_⟩
    · intro v
      have : {g' : G' | (σ.comp Φ.symm.toMulEquiv.toMonoidHom) g' v = v} = Φ.symm ⁻¹' {g | σ g v = v} := by
        ext g'; exact Iff.rfl
      rw [this]
      exact (hsm v).preimage Φ.symm.continuous
    · intro K' hK'o hK'c
      let K : Subgroup G := K'.comap Φ.toMulEquiv.toMonoidHom
      have hKo : IsOpen (K : Set G) := hK'o.preimage Φ.continuous
      have hKc : IsCompact (K : Set G) := by
        have : (K : Set G) = Φ.symm '' (K' : Set G') := by
          ext g; constructor
          · intro hg; exact ⟨Φ g, hg, by simp⟩
          · rintro ⟨g', hg', rfl⟩
            show Φ (Φ.symm g') ∈ K'
            simpa using hg'
        rw [this]; exact hK'c.image Φ.symm.continuous
      have heq : GlobalTheory.PRep.fixed (σ.comp Φ.symm.toMulEquiv.toMonoidHom) K' = GlobalTheory.PRep.fixed σ K := by
        ext v
        simp only [GlobalTheory.PRep.fixed, GlobalTheory.PRep.eig]
        constructor
        · intro hv h
          have := hv ⟨Φ h, h.2⟩
          simp at this ⊢
          convert this using 3
          exact (Φ.symm_apply_apply _).symm
        · intro hv h
          have := hv ⟨Φ.symm h, show Φ (Φ.symm h) ∈ K' by simpa using h.2⟩
          simp at this ⊢
          convert this using 3
          rfl
      rw [heq]
      exact hfd K hKo hKc
  · intro f f' hf A
    let e : G ≃ᵐ G' := Φ.toHomeomorph.toMeasurableEquiv
    have hmap : ν.map Φ = ν.map e := rfl
    have he : ∀ g, e g = Φ g := fun g => rfl
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp, hmap]
    refine forall_congr' fun v => forall_congr' fun l => ?_
    rw [integrable_map_equiv, integral_map_equiv]
    have hfun : ((fun g' => f' g' * l ((σ.comp Φ.symm.toMulEquiv.toMonoidHom) g' v)) ∘ e) = fun g => f g * l (σ g v) := by
      funext g; simp only [Function.comp_apply, he, hf, hcomp]
    have hfun' : (fun g => f' (e g) * l ((σ.comp Φ.symm.toMulEquiv.toMonoidHom) (e g) v)) = fun g => f g * l (σ g v) := by
      funext g; simp only [Function.comp_apply, he, hf, hcomp]
    rw [hfun, hfun']

end GlobalTheory.TransportIso
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RepresentationTransportTopGroupEquivStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.representation_transport_topGroupEquiv : ∀ (G G' : Type) [Group G] [Group G'] [TopologicalSpace G] [TopologicalSpace G'] [MeasurableSpace G] [BorelSpace G] [MeasurableSpace G'] [BorelSpace G'] (Φ : G ≃ₜ* G') (ν : Measure G) (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G W), (σ.IsIrreducible → Representation.IsIrreducible (σ.comp Φ.symm.toMulEquiv.toMonoidHom)) ∧ (IsAdmissible σ → IsAdmissible (σ.comp Φ.symm.toMulEquiv.toMonoidHom : Representation ℂ G' W)) ∧ ∀ (f : G → ℂ) (f' : G' → ℂ), (∀ g, f' (Φ g) = f g) → ∀ A, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp (ν.map Φ) (σ.comp Φ.symm.toMulEquiv.toMonoidHom : Representation ℂ G' W) f' A ↔ GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ f A := by
  first | exact @GlobalTheory.TransportIso.irreducible_admissible_integralOp_transport | exact GlobalTheory.TransportIso.irreducible_admissible_integralOp_transport | (intros; apply GlobalTheory.TransportIso.irreducible_admissible_integralOp_transport <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAuxiliarySplitPlaceNotMemFinsetStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAuxiliarySplitPlaceNotMemFinsetAlt
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AuxiliarySplitPlace

theorem exists_auxiliarySplitPlace_notMem_finset : ∀ (D : D7) (V : HSp D) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))),
    ∃ U : AuxiliaryPlaceHermitianSpace V, U.u ∉ S := fun D V S =>
  exists_auxiliaryPlace_not_mem_finset (isCMExt_host D) (isHermND_gram V) (SelfDual.isSelfDualAt_frameLat D V) S

end GlobalTheory.AuxiliarySplitPlace
end

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_splitPlaceHermitianSpace_notMem_finset : ∀ (D : D7) (V : HSp D) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))), ∃ U : AuxiliaryPlaceHermitianSpace V, U.u ∉ S := by
  first | exact @GlobalTheory.AuxiliarySplitPlace.exists_auxiliarySplitPlace_notMem_finset | exact GlobalTheory.AuxiliarySplitPlace.exists_auxiliarySplitPlace_notMem_finset | (intros; apply GlobalTheory.AuxiliarySplitPlace.exists_auxiliarySplitPlace_notMem_finset <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportPureTensorsProductMeasureFiniteAdelic
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportPureTensorsProductMeasureFiniteAdelic
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TrMultTransport

section Density

open GlobalTheory.AdelicU GlobalTheory.PlaceGen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E))

theorem exists_levelOff_subset [Submodule.IsFullLattice E L] (N : Set (GAd σ J)) (hN : IsOpen N)
    (h1 : (1 : GAd σ J) ∈ N) : ∃ S, (levelOff σ J L S : Set (GAd σ J)) ⊆ N := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨g, hg⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    (fun S : Finset (HeightOneSpectrum (𝓞 F)) => (levelOff σ J L S : Set (GAd σ J)) \ N)
    (fun S S' => ⟨S ∪ S', Set.diff_subset_diff_left (levelOff_anti σ J L Finset.subset_union_left),
      Set.diff_subset_diff_left (levelOff_anti σ J L Finset.subset_union_right)⟩)
    (fun S => Set.diff_nonempty.2 (hcon S))
    (fun S => (isCompact_levelOff σ J L S).diff hN)
    (fun S => ((isCompact_levelOff σ J L S).diff hN).isClosed)
  rw [Set.mem_iInter] at hg
  have e : g = 1 := GAd_ext σ J
    (fun w => by rw [mem_finPts_iff_forall.1 (mem_levelOff.1 (hg ∅).1).1 w, map_one])
    fun v => by rw [(mem_levelOff.1 (hg {v}).1).2.1 v (Finset.mem_singleton_self v), map_one]
  exact (hg ∅).2 (e ▸ h1)

end Density

theorem dense_locFin (D : D7) (V : HSp D) :
    Dense ((⨆ v, (locFin V v).range : Subgroup (GfC V)) : Set (GfC V)) := by
  classical
  haveI hL : Submodule.IsFullLattice D.host.E (stdLattice D.host.E V.rank) := isLattice_stdLattice
  set H : Subgroup (GfC V) := ⨆ v, (locFin V v).range with hH
  have hemb : ∀ v x, GlobalTheory.AdelicU.emb D.sp.cm.sig V.gram v x ∈ H.map (GfC V).subtype := fun v x =>
    ⟨locFin V v x, Subgroup.mem_iSup_of_mem v ⟨x, rfl⟩, rfl⟩
  intro g
  rw [mem_closure_iff]
  intro o ho hgo
  obtain ⟨U, hU, rfl⟩ := isOpen_induced_iff.1 ho
  let N : Set (GA D V) := (fun k => (g : GA D V) * k⁻¹) ⁻¹' U
  have hN : IsOpen N := hU.preimage (continuous_const.mul continuous_inv)
  have h1 : (1 : GA D V) ∈ N := by simpa [N] using hgo
  obtain ⟨S₀, hS₀⟩ := GlobalTheory.TrMultTransport.exists_levelOff_subset D.sp.cm.sig V.gram (stdLattice D.host.E V.rank) N hN h1
  have hf := Filter.eventually_cofinite.1
    (GlobalTheory.AdelicU.eventually_proj_mem_stabLoc D.sp.cm.sig V.gram (stdLattice D.host.E V.rank) (g : GA D V))
  set S' := S₀ ∪ hf.toFinset with hS'
  set x := embAt D.sp.cm.sig V.gram S' (projAt D.sp.cm.sig V.gram S' (g : GA D V)) with hx
  have hxm := GlobalTheory.AdelicU.mem_atPts.1 (embAt_mem D.sp.cm.sig V.gram S' (projAt D.sp.cm.sig V.gram S' (g : GA D V)))
  have hgfin : (g : GA D V) ∈ GlobalTheory.AdelicU.finPts D.sp.cm.sig V.gram := g.2
  have hrest : (partAway D.sp.cm.sig V.gram S' (g : GA D V) : GA D V) ∈
      levelOff D.sp.cm.sig V.gram (stdLattice D.host.E V.rank) S' := by
    refine mem_levelOff.2 ⟨mul_mem (inv_mem hxm.1) hgfin, mem_awayPts.1 (partAway _ _ S' (g : GA D V)).2, fun v hv => ?_⟩
    change proj D.sp.cm.sig V.gram v ((embAt _ _ S' (projAt _ _ S' (g : GA D V)))⁻¹ * (g : GA D V)) ∈ _
    rw [map_mul, map_inv, hxm.2 v hv, inv_one, one_mul]
    by_contra hc
    exact hv (Finset.mem_union_right _ (hf.mem_toFinset.2 hc))
  have hp : (partAway D.sp.cm.sig V.gram S' (g : GA D V) : GA D V) ∈ N :=
    hS₀ (GlobalTheory.PlaceGen.levelOff_anti _ _ _ Finset.subset_union_left hrest)
  have hxe : (g : GA D V) * (partAway D.sp.cm.sig V.gram S' (g : GA D V) : GA D V)⁻¹ = x := by
    exact mul_inv_eq_of_eq_mul (embAt_mul_partAway D.sp.cm.sig V.gram S' (g : GA D V)).symm
  have hxH : x ∈ H.map (GfC V).subtype :=
    GlobalTheory.PlaceGen.piCoprod_mem (fun v : S' => GlobalTheory.AdelicU.emb D.sp.cm.sig V.gram v) _ _ (fun v y => hemb v y) _
  obtain ⟨y, hy, hye⟩ := hxH
  refine ⟨y, ?_, hy⟩
  show (y : GA D V) ∈ U
  have : (y : GA D V) = x := hye
  rw [this, ← hxe]
  exact hp

theorem finLoc_transport {D : D7} {V V' : HSp D}
    (j : ∀ v, GLoc D.sp.cm.sig V.gram v ≃ₜ* GLoc D.sp.cm.sig V'.gram v) (Φ : GfC V ≃ₜ* GfC V')
    (hΦ : ∀ v g, Φ (locFin V v g) = locFin V' v (j v g)) (v : HeightOneSpectrum (𝓞 D.host.F)) (g : GfC V) :
    finLoc V' v (Φ g) = j v (finLoc V v g) := by
  let f₁ : GfC V →* Gv V' v := (finLoc V' v).comp Φ.toMulEquiv.toMonoidHom
  let f₂ : GfC V →* Gv V' v := (j v).toMulEquiv.toMonoidHom.comp (finLoc V v)
  have hc : ∀ {W : HSp D}, Continuous (finLoc W v) := fun {W} =>
    (continuous_proj D.sp.cm.sig W.gram v).comp continuous_subtype_val
  have c₁ : Continuous f₁ := hc.comp Φ.continuous
  have c₂ : Continuous f₂ := (j v).continuous.comp hc
  have hle : (⨆ u, (locFin V u).range) ≤ MonoidHom.eqLocus f₁ f₂ := iSup_le fun u => by
    rintro _ ⟨x, rfl⟩
    show finLoc V' v (Φ (locFin V u x)) = j v (finLoc V v (locFin V u x))
    rw [hΦ]
    by_cases h : v = u
    · subst h
      simp [finLoc]
    · simp [finLoc, proj_emb_ne _ _ h]
  have := Set.EqOn.closure (s := ((⨆ u, (locFin V u).range : Subgroup (GfC V)) : Set (GfC V)))
    (fun x hx => hle hx) c₁ c₂
  rw [(dense_locFin D V).closure_eq] at this
  exact this (Set.mem_univ g)

theorem transport :
    ∀ (D : D7) (V V' : HSp D) (j : ∀ v, GLoc D.sp.cm.sig V.gram v ≃ₜ* GLoc D.sp.cm.sig V'.gram v),
      (∀ v g, j v g ∈ Kv V' v ↔ g ∈ Kv V v) → ∀ Φ : GfC V ≃ₜ* GfC V',
      (∀ v g, Φ (locFin V v g) = locFin V' v (j v g)) →
      (∀ ff g, finFn V' (transfer j ff) (Φ g) = finFn V ff g) ∧
      ∀ μf ν, IsFinMeas V μf ν → IsFinMeas V' (fun v => (μf v).map (j v)) (ν.map Φ) := by
  intro D V V' j hK Φ hΦ
  have h1 : ∀ ff g, finFn V' (transfer j ff) (Φ g) = finFn V ff g := fun ff g => by
    refine finprod_congr fun v => ?_
    have := finLoc_transport j Φ hΦ v g
    simp only [finLoc, MonoidHom.comp_apply, Subgroup.coe_subtype] at this
    simp only [GlobalTheory.Orb.transfer, Function.comp_apply, this, ContinuousMulEquiv.symm_apply_apply]
  refine ⟨h1, fun μf ν hν => ?_⟩
  haveI := hν.1
  refine ⟨Φ.isHaarMeasure_map ν, fun ff' hff' => ?_⟩
  let ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ := fun v => ff' v ∘ j v
  have ht : GlobalTheory.Orb.transfer j ff = ff' := funext fun v => funext fun y => by
    simp [ff, GlobalTheory.Orb.transfer]
  have hff : IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff := by
    have := hff'.transfer (fun v => (j v).symm) (Filter.Eventually.of_forall fun v g => by
      have := hK v ((j v).symm g)
      rw [ContinuousMulEquiv.apply_symm_apply] at this
      exact this.symm)
    convert this using 1
    funext v y
    simp [ff, GlobalTheory.Orb.transfer]
  have hm : MeasurableEmbedding (⇑Φ) := Φ.toHomeomorph.measurableEmbedding
  rw [hm.integral_map]
  have e1 : ∀ g, finFn V' ff' (Φ g) = finFn V ff g := fun g => by
    rw [← h1 ff g, ht]
  simp only [e1, hν.2 ff hff]
  refine finprod_congr fun v => ?_
  have hjm : MeasurableEmbedding (⇑(j v)) := (j v).toHomeomorph.measurableEmbedding
  show _ = ∫ x, ff' v x ∂(μf v).map (j v)
  rw [hjm.integral_map]
  rfl
end GlobalTheory.TrMultTransport
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportPureTensorsProductMeasureFiniteAdelicStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transport_pureTensors_productMeasure_finiteAdelic : ∀ (D : D7) (V V' : HSp D) (j : ∀ v, GLoc D.sp.cm.sig V.gram v ≃ₜ* GLoc D.sp.cm.sig V'.gram v), (∀ v g, j v g ∈ Kv V' v ↔ g ∈ Kv V v) → ∀ Φ : GfC V ≃ₜ* GfC V', (∀ v g, Φ (locFin V v g) = locFin V' v (j v g)) → (∀ ff g, finFn V' (transfer j ff) (Φ g) = finFn V ff g) ∧ ∀ μf ν, IsFinMeas V μf ν → IsFinMeas V' (fun v => (μf v).map (j v)) (ν.map Φ) := by
  first | exact @GlobalTheory.TrMultTransport.transport | exact GlobalTheory.TrMultTransport.transport | (intros; apply GlobalTheory.TrMultTransport.transport <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRestrictedProductHaarGivenFiniteFactors
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRestrictedProductHaarGivenFiniteFactors
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ProdMeas

theorem exists_isFinMeas {D : D7} (V : HSp D) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) [∀ v, (μf v).IsHaarMeasure]
    (h1 : ∀ᶠ v in cofinite, μf v (Kv V v) = 1) : ∃ ν, IsFinMeas V μf ν := by
  obtain ⟨ν, hν⟩ := (existsUnique_isRestrictedProdFinPts D.sp.cm.sig V.gram (frameLat V) μf h1).exists
  refine ⟨ν, hν.2.2.1, fun ff hf => ?_⟩
  let S := (eventually_cofinite.1 (hf.2.and h1)).toFinset
  have hS : ∀ v ∉ S, ff v = unitLoc _ _ (frameLat V) v ∧ μf v (Kv V v) = 1 := fun v hv => by
    simpa only [S, Finite.mem_toFinset, mem_setOf_eq, not_not] using hv
  rw [finprod_eq_prod_of_mulSupport_subset (s := S) _ fun v hv => by_contra fun h => hv (by
    rw [(hS v h).1, unitLoc]
    refine (integral_indicator_const _ (isOpen_stabLoc _ _ _ v).measurableSet).trans ?_
    rw [Measure.real, (hS v h).2, ENNReal.toReal_one, one_smul]; rfl)]
  have hcount : Countable (HeightOneSpectrum (𝓞 D.host.F)) := GlobalTheory.AdelicUnitaryTop.countable_heightOneSpectrum _
  have hsf : ∀ w : Empty, SigmaFinite (w.elim : Measure PUnit.{1}) := fun w => w.elim
  have key := (GlobalTheory.RestrMeas.IsCylProd.integral_tensor_indicator (𝕜 := ℂ) (fa := fun w => w.elim) (ff := ff) hν.2.2.2
    (fun w => w.elim) (fun v => ((continuous_proj _ _ v).comp continuous_subtype_val).measurable)
    (fun v => (isOpen_stabLoc _ _ _ v).measurableSet) (fun x => eventually_proj_mem_stabLoc _ _ _ x.1)
    (S := S) (fun v hv => (hS v hv).2) (fun v hv => (hS v hv).1) (fun w => w.elim)
    fun v _ => (hf.1 v).1.continuous.integrable_of_hasCompactSupport (hf.1 v).2).2
  simp_rw [@Finset.univ_eq_empty Empty _ ⟨Empty.elim⟩, Finset.prod_empty, one_mul] at key
  exact key

end GlobalTheory.ProdMeas

namespace GlobalTheory.ProdMeas

theorem exists_prod_of_haar : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure]
    (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)), (∀ v, (μf v).IsHaarMeasure) → (∀ᶠ v in cofinite, μf v (Kv V v) = 1) →
    (∃ μa, IsRestrictedProd D.sp.cm.sig V.gram (frameLat V) μa μf μ) ∧ ∃ ν, IsFinMeas V μf ν := by
  intro D V μ _ μf hf h1
  haveI := hf
  refine ⟨?_, exists_isFinMeas V μf h1⟩
  obtain ⟨μ₀, h₀⟩ := (existsUnique_isRestrictedProd D.sp.cm.sig V.gram (frameLat V) (fun _ => Measure.haar) μf h1).exists
  haveI := h₀.haar
  have he : μ = Measure.haarScalarFactor μ μ₀ • μ₀ := Measure.isMulLeftInvariant_eq_smul μ μ₀
  have hc : Measure.haarScalarFactor μ μ₀ ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at he
    exact (NeZero.ne μ) he
  classical
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace D.host.F))
  rw [he]
  exact ⟨_, h₀.smul_arch w hc⟩

end GlobalTheory.ProdMeas
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRestrictedProductHaarGivenFiniteFactorsStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_restrictedProduct_haar_given_finiteFactors : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)), (∀ v, (μf v).IsHaarMeasure) → (∀ᶠ v in cofinite, μf v (Kv V v) = 1) → (∃ μa, IsRestrictedProd D.sp.cm.sig V.gram (frameLat V) μa μf μ) ∧ ∃ ν, IsFinMeas V μf ν := by
  first | exact @GlobalTheory.ProdMeas.exists_prod_of_haar | exact GlobalTheory.ProdMeas.exists_prod_of_haar | (intros; apply GlobalTheory.ProdMeas.exists_prod_of_haar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenCompactLevelSphericalOffTypes
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenCompactLevelSphericalOffTypes
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TrMult.OneLevel

variable {D : D7}

def levelAd {V : HSp D} (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) : Subgroup (GA D V) :=
  levelOpen D.sp.cm.sig V.gram (frameLat V) ⊓
    (⨅ v : T.S, (stabLocOne D.sp.cm.sig V.gram (T.frame v).emb (frameLat V)).comap (proj D.sp.cm.sig V.gram v.1)) ⊓
    U.frame.iwahori.comap (proj D.sp.cm.sig V.gram U.u)

def level {V : HSp D} (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) : Subgroup (GfC V) := (levelAd T U).subgroupOf (GfC V)

theorem mem_levelAd {V : HSp D} {T : TypeDataG V} {U : AuxiliaryPlaceHermitianSpace V} {g : GA D V} :
    g ∈ levelAd T U ↔ (∀ v, proj D.sp.cm.sig V.gram v g ∈ Kv V v) ∧
      (∀ v : T.S, proj D.sp.cm.sig V.gram v.1 g ∈ stabLocOne D.sp.cm.sig V.gram (T.frame v).emb (frameLat V)) ∧
      proj D.sp.cm.sig V.gram U.u g ∈ U.frame.iwahori := by
  simp [levelAd, mem_levelOpen, Subgroup.mem_iInf, and_assoc]

theorem isOpen_levelAd {V : HSp D} (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) : IsOpen (levelAd T U : Set (GA D V)) := by
  let : Submodule.IsFullLattice D.host.E (frameLat V) := SelfDual.isLattice_frameLat V
  simp only [levelAd, Subgroup.coe_inf, Subgroup.coe_iInf, Subgroup.coe_comap]
  refine ((isOpen_levelOpen _ _ _).inter (isOpen_iInter_of_finite fun v => ?_)).inter
    (U.frame.isOpen_iwahori.preimage (continuous_proj _ _ _))
  exact (isOpen_stabLocOne _ _ _ (isCMExt_host D)).preimage (continuous_proj _ _ _)

theorem isClosed_levelAd {V : HSp D} (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) : IsClosed (levelAd T U : Set (GA D V)) :=
  Subgroup.isClosed_of_isOpen _ (isOpen_levelAd T U)

theorem isOpen_level {V : HSp D} (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) : IsOpen (level T U : Set (GfC V)) := by
  rw [level, Subgroup.coe_subgroupOf]
  exact (isOpen_levelAd T U).preimage continuous_subtype_val

theorem isCompact_level {V : HSp D} (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) : IsCompact (level T U : Set (GfC V)) := by
  let : Submodule.IsFullLattice D.host.E (frameLat V) := SelfDual.isLattice_frameLat V
  rw [Subtype.isCompact_iff]
  have e : ((↑) : GfC V → GA D V) '' (level T U : Set (GfC V)) =
      (levelFin D.sp.cm.sig V.gram (frameLat V) : Set (GA D V)) ∩ levelAd T U := by
    ext g
    simp only [level, Set.mem_image, SetLike.mem_coe, Subgroup.mem_subgroupOf, Set.mem_inter_iff, mem_levelFin]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x.2, (mem_levelAd.1 hx).1⟩, hx⟩
    · rintro ⟨⟨hf, -⟩, hg⟩
      exact ⟨⟨g, hf⟩, hg, rfl⟩
  rw [e]
  exact (isCompact_levelFin _ _ _).inter_right (isClosed_levelAd T U)

theorem conv_mul_left {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant]
    {f f' : G → ℂ} {a : G} (ha : ∀ y, f (a * y) = f y) (x : G) : conv μ f f' (a * x) = conv μ f f' x := by
  simp only [conv]
  rw [← integral_mul_left_eq_self _ a]
  refine integral_congr_ae (.of_forall fun y => ?_)
  simp only [ha, mul_inv_rev, mul_assoc, inv_mul_cancel_left]

end GlobalTheory.TrMult.OneLevel


open GlobalTheory.TrMult.OneLevel in
theorem GlobalTheory.TrMult.oneLevel : ∀ (D : D7) (V : HSp D) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V), ∃ K : Subgroup (GfC V), IsOpen (K : Set (GfC V)) ∧ IsCompact (K : Set (GfC V)) ∧ ∀ (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)), (∀ v, (μf v).IsHaarMeasure) → ∀ ff, IsTestFin T U μf ff → SphRest T U ff → IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff ∧ ∀ k ∈ K, ∀ g, finFn V ff (k * g) = finFn V ff g := by
  intro D V T U
  let : Submodule.IsFullLattice D.host.E (frameLat V) := SelfDual.isLattice_frameLat V
  refine ⟨level T U, isOpen_level T U, isCompact_level T U, fun μf hμ ff hT hS => ⟨hT.isFinFamily, fun k hk g => ?_⟩⟩
  obtain ⟨hK, hOne, hI⟩ := mem_levelAd.1 (Subgroup.mem_subgroupOf.1 hk)
  simp only [finFn]
  refine finprod_congr fun v => ?_
  rw [Subgroup.coe_mul, map_mul]
  generalize proj D.sp.cm.sig V.gram v (g : GA D V) = x
  by_cases hv : v ∈ T.S
  · obtain ⟨h, -, e⟩ := hT.2.1 ⟨v, hv⟩
    have he : ∀ y, T.idem μf ⟨v, hv⟩ (proj D.sp.cm.sig V.gram v (k : GA D V) * y) = T.idem μf ⟨v, hv⟩ y := fun y =>
      (typeIdem_mul_ker (μf v) (T.frame ⟨v, hv⟩).red (T.τ ⟨v, hv⟩) (k := ⟨_, hK v⟩)
        (((T.frame ⟨v, hv⟩).red_eq_one_iff _).2 (hOne ⟨v, hv⟩)) y).1
    simp only at e
    rw [e]
    exact conv_mul_left _ (conv_mul_left _ he) x
  · by_cases hu : v = U.u
    · subst hu
      obtain ⟨t, -, e⟩ := hT.2.2.1
      rw [e]
      simp only [SplitAt.cosetFn, SplitAt.iwahoriCoset, Set.indicator]
      congr 1
      apply propext
      rw [DoubleCoset.mem_doubleCoset, DoubleCoset.mem_doubleCoset]
      constructor
      · rintro ⟨a, ha, b, hb, e⟩
        refine ⟨(proj D.sp.cm.sig V.gram U.u (k : GA D V))⁻¹ * a, mul_mem (inv_mem hI) ha, b, hb, ?_⟩
        simp only [mul_assoc]
        rw [eq_inv_mul_iff_mul_eq]
        simpa only [mul_assoc] using e
      · rintro ⟨a, ha, b, hb, rfl⟩
        exact ⟨_ * a, mul_mem hI ha, b, hb, by group⟩
    · simpa using hS v hv hu _ (hK v) 1 (one_mem _) x
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenCompactLevelSphericalOffTypesStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_openCompact_level_sphericalOffTypes : ∀ (D : D7) (V : HSp D) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V), ∃ K : Subgroup (GfC V), IsOpen (K : Set (GfC V)) ∧ IsCompact (K : Set (GfC V)) ∧ ∀ (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)), (∀ v, (μf v).IsHaarMeasure) → ∀ ff, IsTestFin T U μf ff → SphRest T U ff → IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff ∧ ∀ k ∈ K, ∀ g, finFn V ff (k * g) = finFn V ff g := by
  first | exact @GlobalTheory.TrMult.oneLevel | exact GlobalTheory.TrMult.oneLevel | (intros; apply GlobalTheory.TrMult.oneLevel <;> assumption)
end
end

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TrMultEnd

structure RepB (G : Type) [Group G] where

  X : Type
  [acg : AddCommGroup X]
  [mod : Module ℂ X]

  ρ : Representation ℂ G X

attribute [instance] RepB.acg RepB.mod

theorem RepB.transport {G : Type} [Group G] {B : RepB G} {X : Type} [AddCommGroup X] [Module ℂ X]
    {ρ : Representation ℂ G X} (h : B = ⟨X, ρ⟩)
    (P : ∀ (X : Type) [AddCommGroup X] [Module ℂ X], Representation ℂ G X → Prop) : P B.X B.ρ ↔ P X ρ := by
  subst h; rfl

theorem exists_family {G : Type} [Group G] [TopologicalSpace G]
    {n₁ : ℕ} {W₁ : Fin n₁ → Type} [∀ i, AddCommGroup (W₁ i)] [∀ i, Module ℂ (W₁ i)] (A : ∀ i, Representation ℂ G (W₁ i))
    {n₂ : ℕ} {W₂ : Fin n₂ → Type} [∀ i, AddCommGroup (W₂ i)] [∀ i, Module ℂ (W₂ i)] (B : ∀ i, Representation ℂ G (W₂ i))
    {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G W) :
    ∃ (m : ℕ) (Ws : Fin m → Type) (_ : ∀ i, AddCommGroup (Ws i)) (_ : ∀ i, Module ℂ (Ws i))
      (τ : ∀ i, Representation ℂ G (Ws i)),
      (∀ i j, i ≠ j → IsEmpty ((τ i).Equiv (τ j))) ∧
      (∀ i, ∃ j, Nonempty ((A i).Equiv (τ j))) ∧ (∀ i, ∃ j, Nonempty ((B i).Equiv (τ j))) ∧
      (∀ P : ∀ (X : Type) [AddCommGroup X] [Module ℂ X], Representation ℂ G X → Prop,
        (∀ i, P _ (A i)) → (∀ i, P _ (B i)) → P W σ → ∀ j, P _ (τ j)) ∧
      ∃ j₀, ∀ P : ∀ (X : Type) [AddCommGroup X] [Module ℂ X], Representation ℂ G X → Prop, P W σ → P _ (τ j₀) := by
  let b : Fin (n₁ + n₂ + 1) → RepB G :=
    Fin.append (Fin.append (fun i => (⟨W₁ i, A i⟩ : RepB G)) fun i => ⟨W₂ i, B i⟩) fun _ : Fin 1 => ⟨W, σ⟩
  have hbA : ∀ i, b (Fin.castAdd 1 (Fin.castAdd n₂ i)) = ⟨W₁ i, A i⟩ := fun i => by simp [b]
  have hbB : ∀ i, b (Fin.castAdd 1 (Fin.natAdd n₁ i)) = ⟨W₂ i, B i⟩ := fun i => by simp [b]
  have hbσ : b (Fin.natAdd (n₁ + n₂) 0) = ⟨W, σ⟩ := by simp [b]
  have hb : ∀ k, (∃ i, b k = ⟨W₁ i, A i⟩) ∨ (∃ i, b k = ⟨W₂ i, B i⟩) ∨ b k = ⟨W, σ⟩ := by
    intro k
    refine Fin.addCases (fun k' => ?_) (fun k' => ?_) k
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) k'
      · exact Or.inl ⟨i, hbA i⟩
      · exact Or.inr (Or.inl ⟨i, hbB i⟩)
    · exact Or.inr (Or.inr (by rw [Subsingleton.elim k' 0]; exact hbσ))
  obtain ⟨n, s, hne, ⟨j₀, hj₀⟩, hcov⟩ :=
    GlobalTheory.T.exists_inequivalentRepresentatives_through_member G (n₁ + n₂ + 1) (fun k => (b k).X) (fun k => (b k).ρ) (Fin.natAdd (n₁ + n₂) 0)
  refine ⟨n, fun j => (b (s j)).X, fun j => inferInstance, fun j => inferInstance, fun j => (b (s j)).ρ, hne,
    fun i => ?_, fun i => ?_, fun P hA hB hσ k => ?_, j₀, fun P hP => ?_⟩
  · obtain ⟨j, hj⟩ := hcov (Fin.castAdd 1 (Fin.castAdd n₂ i))
    exact ⟨j, (RepB.transport (hbA i) (fun X _ _ ρ => Nonempty (ρ.Equiv ((b (s j)).ρ)))).1 hj⟩
  · obtain ⟨j, hj⟩ := hcov (Fin.castAdd 1 (Fin.natAdd n₁ i))
    exact ⟨j, (RepB.transport (hbB i) (fun X _ _ ρ => Nonempty (ρ.Equiv ((b (s j)).ρ)))).1 hj⟩
  · rcases hb (s k) with ⟨i, h⟩ | ⟨i, h⟩ | h
    · exact (RepB.transport h P).2 (hA i)
    · exact (RepB.transport h P).2 (hB i)
    · exact (RepB.transport h P).2 hσ
  · exact (RepB.transport ((congrArg b hj₀).trans hbσ) P).2 hP

def equivComp {G H : Type} [Group G] [Group H] {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    {ρ : Representation ℂ G X} {ρ' : Representation ℂ G Y} (e : ρ.Equiv ρ') (f : H →* G) :
    Representation.Equiv (ρ.comp f : Representation ℂ H X) (ρ'.comp f) :=
  Representation.Equiv.mk e.toLinearEquiv fun h => by
    ext x; exact congrArg (fun l : X →ₗ[ℂ] Y => l x) (e.isIntertwining' (f h))

def equivCompSymm {G H : Type} [Group G] [Group H] {X : Type} [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ G X) (Φ : G ≃* H) :
    Representation.Equiv ρ (((ρ.comp Φ.symm.toMonoidHom : Representation ℂ H X).comp Φ.toMonoidHom : Representation ℂ G X)) :=
  Representation.Equiv.mk (LinearEquiv.refl ℂ X) fun g => by ext x; simp

def equivCompSymm' {G H : Type} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H] {X : Type} [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ H X) (Φ : G ≃ₜ* H) :
    Representation.Equiv ρ (((ρ.comp Φ.symm.symm.toMulEquiv.toMonoidHom : Representation ℂ G X).comp Φ.symm.toMulEquiv.toMonoidHom : Representation ℂ H X)) :=
  Representation.Equiv.mk (LinearEquiv.refl ℂ X) fun g => by
    ext x
    change ρ g x = ρ (Φ (Φ.symm g)) x
    rw [Φ.apply_symm_apply]

end GlobalTheory.TrMultEnd

namespace GlobalTheory.TrMultEnd


end GlobalTheory.TrMultEnd
