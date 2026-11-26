module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePIsogenyTargetsAtCharPPoint

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsAlgClosedEmbeddingsOfFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsAlgClosedEmbeddingsOfFamily
namespace GlobalTheory

open MvPolynomial

theorem exists_isAlgClosed_embeddings_of_family :
    ∀ (F : Type) [Field F] (I : Type) (k : I → Type) [∀ i, Field (k i)] (f : ∀ i, F →+* k i),
      ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (g : ∀ i, k i →+* L) (h : F →+* L),
        ∀ i, (g i).comp (f i) = h := by
  intro F _ I k _ f
  let K := FractionRing (MvPolynomial (Σ i, k i) F)
  let Ω := AlgebraicClosure K
  have key : ∀ i, ∃ g : k i →+* Ω, g.comp (f i) = algebraMap F Ω := by
    intro i
    letI : Algebra F (k i) := (f i).toAlgebra
    obtain ⟨s, hs⟩ := exists_isTranscendenceBasis F (k i)
    let x : (Σ i, k i) → Ω := fun j => algebraMap K Ω (algebraMap (MvPolynomial (Σ i, k i) F) K (X j))
    have hx : AlgebraicIndependent F x := by
      have h0 := MvPolynomial.algebraicIndependent_X (Σ i, k i) F
      have h1 : Function.Injective (IsScalarTower.toAlgHom F (MvPolynomial (Σ i, k i) F) K) :=
        IsFractionRing.injective _ _
      have h2 : Function.Injective (IsScalarTower.toAlgHom F K Ω) :=
        (algebraMap K Ω).injective
      have := (h0.map' h1).map' h2
      exact this
    have hv : AlgebraicIndependent F (fun b : s => x ⟨i, b.1⟩) :=
      hx.comp (fun b : s => (⟨i, b.1⟩ : Σ i, k i)) (by
        intro a b hab
        exact Subtype.ext (by simpa using hab))
    let φ0 : IntermediateField.adjoin F (Set.range ((↑) : s → k i)) →ₐ[F] Ω :=
      (IntermediateField.val _).comp (hv.aevalEquivField.toAlgHom.comp hs.1.reprField)
    have halg := hs.isAlgebraic_field
    obtain ⟨φ, -⟩ := IntermediateField.exists_algHom_of_splits' φ0
      (fun (y : k i) => ⟨(Algebra.IsAlgebraic.isAlgebraic
        (R := IntermediateField.adjoin F (Set.range ((↑) : s → k i))) y).isIntegral,
        IsAlgClosed.splits _⟩)
    refine ⟨φ.toRingHom, ?_⟩
    ext y
    exact φ.commutes y
  choose g hg using key
  exact ⟨Ω, inferInstance, inferInstance, g, algebraMap F Ω, hg⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsAlgClosedEmbeddingsOfFamilyStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isAlgClosed_compatible_embeddings_of_family : ∀ (F : Type) [Field F] (I : Type) (k : I → Type) [∀ i, Field (k i)] (f : ∀ i, F →+* k i), ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (g : ∀ i, k i →+* L) (h : F →+* L), ∀ i, (g i).comp (f i) = h := by
  first | (exact @GlobalTheory.exists_isAlgClosed_embeddings_of_family) | (exact GlobalTheory.exists_isAlgClosed_embeddings_of_family) | (intros; apply GlobalTheory.exists_isAlgClosed_embeddings_of_family  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePointsClosureGenericCorrespondenceSnd
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePIsogenySourcesAtCharPPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePIsogenySourcesAtCharPPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.UPel.HT.ES.SourceFin

open GlobalTheory.UPel.HT.ESDual GlobalTheory.UPel.HT.ES.CorrQF

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}

def scaleMap {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {o : Obj b N s} {o' : Obj b N s'} {f : S' ⟶ S}
    (m : ObjMap o' o f) (e : ℕ) : ObjMap (scale o' e rfl) (scale o e rfl) f where
  φ := m.φ
  φ₂ := m.φ₂
  cart := m.cart
  sq := m.sq
  act := m.act
  pol := m.pol
  eta y := m.eta _

theorem exists_scale_mono (hN : 0 < N) (hp : N.Coprime p) (M : Model b N) (e : ℕ) :
    ∃ τ : M.X ⟶ M.X, Mono τ ∧ τ ≫ M.s = M.s ∧ Nonempty (ObjMap (scale M.univ e rfl) M.univ τ) := by
  obtain ⟨f, hf⟩ := exists_inv_exp hN hp e
  obtain ⟨τ, ⟨hτ, ⟨m⟩⟩, -⟩ := M.rep _ _ (scale M.univ e rfl)
  obtain ⟨τ', ⟨hτ', ⟨m'⟩⟩, -⟩ := M.rep _ _ (scale M.univ f rfl)
  have n : ObjMap (scale (scale M.univ e rfl) f rfl) M.univ (𝟙 M.X) :=
    { φ := (idMap M.univ).φ
      φ₂ := (idMap M.univ).φ₂
      cart := (idMap M.univ).cart
      sq := (idMap M.univ).sq
      act := (idMap M.univ).act
      pol := (idMap M.univ).pol
      eta := fun y => by
        have h : (scale (scale M.univ e rfl) f rfl).eta y = M.univ.eta y := by
          show M.univ.eta (p ^ e • p ^ f • y) = _
          rw [smul_smul, ← pow_add, eta_congr M.univ hf (pow_pos (Fact.out : p.Prime).pos _)]
        rw [h]
        exact (idMap M.univ).eta y }
  have h1 : τ ≫ τ' = 𝟙 M.X :=
    (M.rep _ _ (scale (scale M.univ e rfl) f rfl)).unique
      ⟨by rw [Category.assoc, hτ', hτ], ⟨compMap (scaleMap m f) m'⟩⟩ ⟨Category.id_comp _, ⟨n⟩⟩
  exact ⟨τ, mono_of_mono_fac h1, hτ, ⟨m⟩⟩

theorem exists_isPIsog_scale {S : Scheme.{0}} {s : S ⟶ Sp R} {e : ℕ} {o o' : Obj b N s} {ψ : o.A ⟶ o'.A}
    (hψ : IsPIsog (p ^ e) o o' ψ) : ∃ ψ' : o'.A ⟶ (scale o e rfl).A, IsPIsog (p ^ e) o' (scale o e rfl) ψ' := by
  obtain ⟨ψ', hm, h₁, h₂⟩ := hψ.2.2.2.2.2
  obtain ⟨a, l, P⟩ := dual_clauses hψ h₁ h₂
  exact ⟨ψ', ⟨e, rfl⟩, hm, a, l, P, ψ, hψ.2.1, h₂, h₁⟩

theorem not_mem_basicOpen {X : Scheme.{0}} (z : X) {k : Type} [Field k] [CharP k p]
    (h : X.residueField z →+* k) : z ∉ X.basicOpen ((p : ℕ) : Γ(X, ⊤)) := by
  rw [Scheme.mem_basicOpen_top, map_natCast]
  intro hu
  have := hu.map (h.comp (X.residue z).hom)
  rw [map_natCast, CharP.cast_eq_zero] at this
  exact not_isUnit_zero this

theorem exists_residueField_hom {X : Scheme.{0}} {k : Type} [Field k] (ζ : Sp k ⟶ X) {z : X}
    (hz : ζ (IsLocalRing.closedPoint k) = z) :
    ∃ h : X.residueField z →+* k, spMap h ≫ X.fromSpecResidueField z = ζ := by
  subst hz
  exact ⟨(X.descResidueField (Scheme.stalkClosedPointTo ζ)).hom,
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField k X ζ⟩

theorem finite_isogSource : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → (p : R) ∈ IsLocalRing.maximalIdeal R → ∀ (c : ℕ), D.m = 1 → ∀ (M : Model b N) (z : M.X), {u : M.X | ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (_ : CharP k p) (ζ υ : Sp k ⟶ M.X) (ou oz : Obj b N (ζ ≫ M.s)) (_ : ObjMap ou M.univ υ) (_ : ObjMap oz M.univ ζ) (ψ : ou.A ⟶ oz.A), υ ≫ M.s = ζ ≫ M.s ∧ IsPIsog c ou oz ψ ∧ ζ (IsLocalRing.closedPoint k) = z ∧ υ (IsLocalRing.closedPoint k) = u}.Finite := by
  intro p _ D R _ _ _ _ b N hN hNp _ c hm M z
  set Z := {u : M.X | ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (_ : CharP k p) (ζ υ : Sp k ⟶ M.X) (ou oz : Obj b N (ζ ≫ M.s)) (_ : ObjMap ou M.univ υ) (_ : ObjMap oz M.univ ζ) (ψ : ou.A ⟶ oz.A), υ ≫ M.s = ζ ≫ M.s ∧ IsPIsog c ou oz ψ ∧ ζ (IsLocalRing.closedPoint k) = z ∧ υ (IsLocalRing.closedPoint k) = u} with hZ
  rcases Z.eq_empty_or_nonempty with h0 | ⟨u₀, k₀, _, _, _, ζ₀, _, _, _, -, -, _, -, hψ₀, hz₀, -⟩
  · rw [h0]; exact Set.finite_empty
  obtain ⟨e, rfl⟩ := hψ₀.1
  obtain ⟨h₀, -⟩ := exists_residueField_hom ζ₀ hz₀
  have hz := not_mem_basicOpen (p := p) z h₀
  obtain ⟨τ, hmono, hτ, ⟨mτ⟩⟩ := exists_scale_mono (by omega) hNp M e
  have key : ∀ u : Z, ∃ (k : Type) (_ : Field k) (σ : M.X.residueField z →+* k) (υ : Sp k ⟶ M.X),
      (∀ q, υ q = u.1) ∧ IsogTarget M (p ^ e) (spMap σ ≫ M.X.fromSpecResidueField z) (υ ≫ τ) := by
    rintro ⟨u, k, _, _, _, ζ, υ, ou, oz, mu, mz, ψ, hs, hψ, hζ, hu⟩
    obtain ⟨σ, hσ⟩ := exists_residueField_hom ζ hζ
    obtain ⟨ψ', hψ'⟩ := exists_isPIsog_scale hψ
    refine ⟨k, inferInstance, σ, υ, fun q => ?_, ?_⟩
    · rw [Subsingleton.elim q (IsLocalRing.closedPoint k)]
      exact hu
    · rw [hσ]
      exact ⟨by rw [Category.assoc, hτ, hs], oz, scale ou e rfl, ψ', ⟨mz⟩, ⟨compMap (scaleMap mu e) mτ⟩, hψ'⟩
  choose k hk σ υ hυ hT using key
  obtain ⟨L, _, _, g, h, hg⟩ := GlobalTheory.T.exists_isAlgClosed_compatible_embeddings_of_family (M.X.residueField z) Z k σ
  have hfin := (GlobalTheory.T.finite_pIsogenyTargets_at_charP_point p D R b N hN hNp hm (p ^ e) M z hz L h).preimage
    (f := fun υ' : Sp L ⟶ M.X => υ' ≫ τ) (fun x _ y _ hxy => (cancel_mono τ).1 hxy)
  refine (Set.Finite.biUnion hfin fun υ' _ => Set.finite_range (fun q : Sp L => υ' q)).subset ?_
  intro u hu
  have h1 := isogTarget_spMap p D R b N M (p ^ e) (k ⟨u, hu⟩) L (g ⟨u, hu⟩) _ _ (hT ⟨u, hu⟩)
  have e1 : spMap (g ⟨u, hu⟩) ≫ spMap (σ ⟨u, hu⟩) ≫ M.X.fromSpecResidueField z =
      spMap h ≫ M.X.fromSpecResidueField z := by
    rw [← Category.assoc, ← hg ⟨u, hu⟩]
    simp [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  rw [e1, ← Category.assoc] at h1
  simp only [Set.mem_iUnion, Set.mem_range]
  refine ⟨spMap (g ⟨u, hu⟩) ≫ υ ⟨u, hu⟩, h1, Classical.arbitrary _, ?_⟩
  rw [Scheme.Hom.comp_apply, hυ ⟨u, hu⟩ _]

end GlobalTheory.UPel.HT.ES.SourceFin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePIsogenySourcesAtCharPPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_pIsogenySources_at_charP_point : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → (p : R) ∈ IsLocalRing.maximalIdeal R → ∀ (c : ℕ), D.m = 1 → ∀ (M : Model b N) (z : M.X), {u : M.X | ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (_ : CharP k p) (ζ υ : Sp k ⟶ M.X) (ou oz : Obj b N (ζ ≫ M.s)) (_ : ObjMap ou M.univ υ) (_ : ObjMap oz M.univ ζ) (ψ : ou.A ⟶ oz.A), υ ≫ M.s = ζ ≫ M.s ∧ IsPIsog c ou oz ψ ∧ ζ (IsLocalRing.closedPoint k) = z ∧ υ (IsLocalRing.closedPoint k) = u}.Finite := by
  first | (exact @GlobalTheory.UPel.HT.ES.SourceFin.finite_isogSource) | (exact GlobalTheory.UPel.HT.ES.SourceFin.finite_isogSource) | (intros; apply GlobalTheory.UPel.HT.ES.SourceFin.finite_isogSource <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPIsogenyAtClosedPointOfDvrLimit
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPIsogenyAtClosedPointOfDvrLimit
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section

namespace GlobalTheory.UPel.HT.ES.ClosedPtIsog

theorem charP_of_notMem_basicOpen {X : Scheme.{0}} {k : Type} [Field k] {p : ℕ} (hp : p.Prime) (h : Sp k ⟶ X)
    (hz : h (IsLocalRing.closedPoint k) ∉ X.basicOpen ((p : ℕ) : Γ(X, ⊤))) : CharP k p := by
  refine (CharP.charP_iff_prime_eq_zero hp).2 ?_
  by_contra hne
  apply hz
  have hu : IsUnit ((p : ℕ) : Γ(Sp k, h ⁻¹ᵁ ⊤)) := by
    have := (IsUnit.mk0 _ hne).map
      (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (Sp k).presheaf.map (homOfLE (le_top (a := h ⁻¹ᵁ ⊤))).op).hom)
    rwa [map_natCast] at this
  have hm : IsLocalRing.closedPoint k ∈ h ⁻¹ᵁ X.basicOpen ((p : ℕ) : Γ(X, ⊤)) := by
    rw [Scheme.preimage_basicOpen, map_natCast, Scheme.basicOpen_of_isUnit _ hu]
    trivial
  exact hm

theorem exists_isPIsog_closedPoint : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → (p : R) ∈ IsLocalRing.maximalIdeal R → ∀ (c : ℕ) (M : Model b N) (Y₀ : Scheme.{0}) (s₀ t₀ : Y₀ ⟶ M.X) (o₀ o₀' : Obj b N (s₀ ≫ M.s)) (ms₀ : ObjMap o₀ M.univ s₀) (mt₀ : ObjMap o₀' M.univ t₀) (ψ₀ : o₀.A ⟶ o₀'.A), s₀ ≫ M.s = t₀ ≫ M.s → IsPIsog c o₀ o₀' ψ₀ → ∀ z : M.X, z ∉ M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)) → {u : M.X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' z' : Sp V ⟶ M.X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ s₀ ∧ spMap (algebraMap V K) ≫ z' = x ≫ t₀ ∧ y' (IsLocalRing.closedPoint V) = u ∧ z' (IsLocalRing.closedPoint V) = z} ⊆ {u : M.X | ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (_ : CharP k p) (ζ υ : Sp k ⟶ M.X) (ou oz : Obj b N (ζ ≫ M.s)) (_ : ObjMap ou M.univ υ) (_ : ObjMap oz M.univ ζ) (ψ : ou.A ⟶ oz.A), υ ≫ M.s = ζ ≫ M.s ∧ IsPIsog c ou oz ψ ∧ ζ (IsLocalRing.closedPoint k) = z ∧ υ (IsLocalRing.closedPoint k) = u} := by
  intro p _ D R _ _ _ _ b N hN hNp _ c M Y₀ s₀ t₀ o₀ o₀' ms₀ mt₀ ψ₀ hst hψ z hz u hu
  obtain ⟨V, K, _, _, _, _, _, _, y', z', x, hy, hz', hyu, hzz⟩ := hu
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.spec_fractionRing V K
  have hyz : y' ≫ M.s = z' ≫ M.s :=
    GlobalTheory.ExtUnique.hom_ext_of_dominant (Spec.map (CommRingCat.ofHom (Int.castRingHom R))) (specZIsTerminal.hom_ext _ _)
      (spMap (algebraMap V K)) (by rw [reassoc_of% hy, reassoc_of% hz', hst])
  have pull : ∀ {S S' : Scheme.{0}} {s : S ⟶ Sp R} (o : Obj b N s) (f : S' ⟶ S) (σ : S' ⟶ Sp R), f ≫ s = σ →
      ∃ o₁ : Obj b N σ, Nonempty (ObjMap o₁ o f) := by
    rintro S S' s o f σ rfl
    exact GlobalTheory.HTPull.exists_objMap_pull p D R b N S S' s f o
  have objMapComp : ∀ {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R}
      {s₃ : S₃ ⟶ Sp R} {o₁ : Obj b N s₁} {o₂ : Obj b N s₂} {o₃ : Obj b N s₃}
      {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃}, ObjMap o₁ o₂ f → ObjMap o₂ o₃ g →
      ObjMap o₁ o₃ (f ≫ g) := by
    intro S₁ S₂ S₃ s₁ s₂ s₃ o₁ o₂ o₃ f g m₁ m₂
    exact {
      φ := m₁.φ ≫ m₂.φ
      φ₂ := m₁.φ₂ ≫ m₂.φ₂
      cart := IsGrpPullback.comp m₁.cart m₂.cart
      sq := ⟨by rw [Category.assoc, m₂.sq.1, ← Category.assoc, m₁.sq.1, Category.assoc],
        by rw [Category.assoc, m₂.sq.2, ← Category.assoc, m₁.sq.2, Category.assoc]⟩
      act := fun c => by rw [← Category.assoc, m₁.act, Category.assoc, m₂.act, Category.assoc]
      pol := LBIso.trans o₁.isLB (pull_isLB o₂.isLB m₁.φ₂) (pull_isLB o₃.isLB _) m₁.pol
        (LBIso.chartPull (chartPullPull o₂.P m₁.φ₂)
          (chartPullSame o₃.P (fun _ : PUnit => m₁.φ₂ ≫ m₂.φ₂) (fun _ => m₂.φ₂) (fun _ => 1) m₁.φ₂ (fun _ => rfl))
          m₂.pol)
      eta := fun y => by rw [← Category.assoc, m₁.eta, Category.assoc, m₂.eta, Category.assoc] }
  obtain ⟨oV, ⟨mV⟩⟩ := pull M.univ y' (z' ≫ M.s) hyz
  obtain ⟨oV', ⟨mV'⟩⟩ := pull M.univ z' (z' ≫ M.s) rfl
  obtain ⟨oK, ⟨nK⟩⟩ := pull o₀ x _ rfl
  obtain ⟨oK', ⟨nK'⟩⟩ := pull o₀' x _ rfl
  obtain ⟨ψK, hψK, -⟩ := ValExt.isPIsog_pull p D R b N c _ _ _ _ x o₀ o₀' oK oK' nK nK' ψ₀ hψ
  have m₁ : ObjMap oK M.univ (spMap (algebraMap V K) ≫ y') := hy ▸ objMapComp nK ms₀
  have m₁' : ObjMap oK' M.univ (spMap (algebraMap V K) ≫ z') := hz' ▸ objMapComp nK' mt₀
  obtain ⟨n₁, -⟩ := GlobalTheory.HTSympCover.exists_objMap_cancel_φ m₁ mV
  obtain ⟨n₁', -⟩ := GlobalTheory.HTSympCover.exists_objMap_cancel_φ m₁' mV'
  obtain ⟨e, he⟩ := hψ.exists_eq_pow
  have hdom : IsDominant (spMap (algebraMap V K)) := inferInstance
  obtain ⟨ψV, hψV, -⟩ := PIsogExt.exists_isPIsog_extend p D R b N hN hNp 0 c
    ⟨e, he, fun h => absurd h (lt_irrefl 0)⟩ _ _ (spMap (algebraMap V K)) _ (z' ≫ M.s)
    (GlobalTheory.isOpenImmersion_spMap_of_isDiscreteValuationRing V K) hdom inferInstance
    (fun y => (GlobalTheory.isDomain_and_isIntegrallyClosed_stalk_Sp V y).2)
    (fun y => (GlobalTheory.isDomain_and_isIntegrallyClosed_stalk_Sp V y).1) oV oV' oK oK' n₁ n₁' ψK hψK
  let k := AlgebraicClosure (IsLocalRing.ResidueField V)
  let φ : V →+* k := (algebraMap (IsLocalRing.ResidueField V) k).comp (IsLocalRing.residue V)
  let g : Sp k ⟶ Sp V := spMap φ
  have hg : g (IsLocalRing.closedPoint k) = IsLocalRing.closedPoint V := IsLocalRing.comap_closedPoint φ
  have hζ : (g ≫ z') (IsLocalRing.closedPoint k) = z :=
    (Scheme.Hom.comp_apply g z' _).trans ((congrArg z' hg).trans hzz)
  have hυ : (g ≫ y') (IsLocalRing.closedPoint k) = u :=
    (Scheme.Hom.comp_apply g y' _).trans ((congrArg y' hg).trans hyu)
  obtain ⟨ou, ⟨nu⟩⟩ := pull oV g ((g ≫ z') ≫ M.s) (Category.assoc _ _ _).symm
  obtain ⟨oz, ⟨nz⟩⟩ := pull oV' g ((g ≫ z') ≫ M.s) (Category.assoc _ _ _).symm
  obtain ⟨ψk, hψk, -⟩ := ValExt.isPIsog_pull p D R b N c _ _ _ _ g oV oV' ou oz nu nz ψV hψV
  exact ⟨k, inferInstance, inferInstance, charP_of_notMem_basicOpen Fact.out (g ≫ z') (hζ ▸ hz), g ≫ z', g ≫ y', ou, oz,
    objMapComp nu mV, objMapComp nz mV', ψk,
    by rw [Category.assoc, Category.assoc, hyz], hψk, hζ, hυ⟩

end GlobalTheory.UPel.HT.ES.ClosedPtIsog
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPIsogenyAtClosedPointOfDvrLimitStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pIsogeny_at_closedPoint_of_dvr_limit : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → (p : R) ∈ IsLocalRing.maximalIdeal R → ∀ (c : ℕ) (M : Model b N) (Y₀ : Scheme.{0}) (s₀ t₀ : Y₀ ⟶ M.X) (o₀ o₀' : Obj b N (s₀ ≫ M.s)) (ms₀ : ObjMap o₀ M.univ s₀) (mt₀ : ObjMap o₀' M.univ t₀) (ψ₀ : o₀.A ⟶ o₀'.A), s₀ ≫ M.s = t₀ ≫ M.s → IsPIsog c o₀ o₀' ψ₀ → ∀ z : M.X, z ∉ M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)) → {u : M.X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' z' : Sp V ⟶ M.X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ s₀ ∧ spMap (algebraMap V K) ≫ z' = x ≫ t₀ ∧ y' (IsLocalRing.closedPoint V) = u ∧ z' (IsLocalRing.closedPoint V) = z} ⊆ {u : M.X | ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (_ : CharP k p) (ζ υ : Sp k ⟶ M.X) (ou oz : Obj b N (ζ ≫ M.s)) (_ : ObjMap ou M.univ υ) (_ : ObjMap oz M.univ ζ) (ψ : ou.A ⟶ oz.A), υ ≫ M.s = ζ ≫ M.s ∧ IsPIsog c ou oz ψ ∧ ζ (IsLocalRing.closedPoint k) = z ∧ υ (IsLocalRing.closedPoint k) = u} := by
  first | (exact @GlobalTheory.UPel.HT.ES.ClosedPtIsog.exists_isPIsog_closedPoint) | (exact GlobalTheory.UPel.HT.ES.ClosedPtIsog.exists_isPIsog_closedPoint) | (intros; apply GlobalTheory.UPel.HT.ES.ClosedPtIsog.exists_isPIsog_closedPoint  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDvrLimitsCorrespondenceFiniteSnd
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDvrLimitsCorrespondenceFiniteSnd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES

theorem finite_dvr_limits_of_finite_snd : ∀ (X Y₀ S : Scheme.{0}) (q : X ⟶ S) (U : X.Opens) (s₀ t₀ : Y₀ ⟶ X)
    (gt : Y₀ ⟶ U.toScheme), IsSeparated q → IsAffine S → s₀ ≫ q = t₀ ≫ q → gt ≫ U.ι = t₀ → IsFinite gt →
    ∀ z : X, z ∈ U → {u : X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V)
      (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' z' : Sp V ⟶ X) (x : Sp K ⟶ Y₀),
      spMap (algebraMap V K) ≫ y' = x ≫ s₀ ∧ spMap (algebraMap V K) ≫ z' = x ≫ t₀ ∧
      y' (IsLocalRing.closedPoint V) = u ∧ z' (IsLocalRing.closedPoint V) = z}.Finite := by
  intro X Y₀ S q U s₀ t₀ gt hq hS _ hgt hfin z hz
  refine ((gt.finite_preimage_singleton ⟨z, hz⟩).image s₀).subset ?_
  rintro u ⟨V, K, _, _, _, _, _, _, y', z', x, h1, h2, rfl, rfl⟩

  have hr : Set.range z' ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint w).map z'.continuous).mem_open U.isOpen hz
  set z'' := IsOpenImmersion.lift U.ι z' hr with hz''
  have hfac : z'' ≫ U.ι = z' := IsOpenImmersion.lift_fac _ _ _

  have hsq : x ≫ gt = spMap (algebraMap V K) ≫ z'' := by
    rw [← cancel_mono U.ι, Category.assoc, hgt, Category.assoc, hfac, h2]
  have hE : ValuativeCriterion.Existence gt :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed gt) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact) gt).1
  obtain ⟨l, hl1, hl2⟩ := (hE { R := V, K := K, i₁ := x, i₂ := z'', commSq := ⟨hsq⟩ }).exists_lift
  dsimp only at hl1 hl2

  have hU := IsSeparated.valuativeCriterion (q ≫ terminal.from S)
  have hsq' : (x ≫ s₀) ≫ (q ≫ terminal.from S) = spMap (algebraMap V K) ≫ terminal.from _ :=
    terminal.hom_ext _ _
  have hy : y' = l ≫ s₀ := by
    have := hU { R := V, K := K, i₁ := x ≫ s₀, i₂ := terminal.from _, commSq := ⟨hsq'⟩ }
    have e := this.elim ⟨y', h1, terminal.hom_ext _ _⟩
      ⟨l ≫ s₀, by change spMap (algebraMap V K) ≫ l ≫ s₀ = x ≫ s₀; rw [← Category.assoc, hl1], terminal.hom_ext _ _⟩
    exact congrArg CommSq.LiftStruct.l e
  refine ⟨l (IsLocalRing.closedPoint V), ?_, ?_⟩
  · show gt (l _) = _
    apply Subtype.ext
    change (l ≫ gt ≫ U.ι) _ = z' _
    rw [← Category.assoc, hl2, hfac]
  · rw [hy]; rfl

end GlobalTheory.UPel.HT.ES
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDvrLimitsCorrespondenceFiniteSndStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_dvr_limits_correspondence_finite_snd : ∀ (X Y₀ S : Scheme.{0}) (q : X ⟶ S) (U : X.Opens) (s₀ t₀ : Y₀ ⟶ X) (gt : Y₀ ⟶ U.toScheme), IsSeparated q → IsAffine S → s₀ ≫ q = t₀ ≫ q → gt ≫ U.ι = t₀ → IsFinite gt → ∀ z : X, z ∈ U → {u : X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' z' : Sp V ⟶ X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ s₀ ∧ spMap (algebraMap V K) ≫ z' = x ≫ t₀ ∧ y' (IsLocalRing.closedPoint V) = u ∧ z' (IsLocalRing.closedPoint V) = z}.Finite := by
  first | (exact @GlobalTheory.UPel.HT.ES.finite_dvr_limits_of_finite_snd) | (exact GlobalTheory.UPel.HT.ES.finite_dvr_limits_of_finite_snd) | (intros; apply GlobalTheory.UPel.HT.ES.finite_dvr_limits_of_finite_snd  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePointsClosureGenericCorrespondenceSnd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

theorem GlobalTheory.UPel.HT.ES.finite_dvrPartners_snd : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → (p : R) ∈ IsLocalRing.maximalIdeal R → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → D.m = 1 → ∀ M : Model b N, ∀ (Y₀ : Scheme.{0}) (s₀ t₀ : Y₀ ⟶ M.X) (gs gt : Y₀ ⟶ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme) (o₀ o₀' : Obj b N (s₀ ≫ M.s)) (ms₀ : ObjMap o₀ M.univ s₀) (mt₀ : ObjMap o₀' M.univ t₀) (ψ₀ : o₀.A ⟶ o₀'.A), s₀ ≫ M.s = t₀ ≫ M.s → gs ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = s₀ → gt ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = t₀ → IsFinite gs → Etale gs → IsFinite gt → Etale gt → IsPIsog c o₀ o₀' ψ₀ → IsTj r w j o₀ o₀' ψ₀ → ∀ z : M.X, {u : M.X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' z' : Sp V ⟶ M.X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ s₀ ∧ spMap (algebraMap V K) ≫ z' = x ≫ t₀ ∧ y' (IsLocalRing.closedPoint V) = u ∧ z' (IsLocalRing.closedPoint V) = z}.Finite := by
  intro p _ D R _ _ _ _ b N hN hNp hpR r w j c hw hu hj hc hm M Y₀ s₀ t₀ gs gt o₀ o₀' ms₀ mt₀ ψ₀ hst hgs hgt _ _ hgtf _ hψ _ z
  by_cases hz : z ∈ M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))
  · exact GlobalTheory.T.finite_dvr_limits_correspondence_finite_snd M.X Y₀ (Sp R) M.s _ s₀ t₀ gt (GlobalTheory.ZM.isSeparated_of_isQProjOver M.qproj) inferInstance hst hgt
      hgtf z hz
  · exact (GlobalTheory.T.finite_pIsogenySources_at_charP_point p D R b N hN hNp hpR c hm M z).subset
      (GlobalTheory.T.exists_pIsogeny_at_closedPoint_of_dvr_limit p D R b N hN hNp hpR c M Y₀ s₀ t₀ o₀ o₀' ms₀ mt₀ ψ₀ hst hψ z hz)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePointsClosureGenericCorrespondenceSndStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_points_closure_genericCorrespondence_snd : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → (p : R) ∈ IsLocalRing.maximalIdeal R → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → D.m = 1 → ∀ M : Model b N, ∀ (Y₀ : Scheme.{0}) (s₀ t₀ : Y₀ ⟶ M.X) (gs gt : Y₀ ⟶ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme) (o₀ o₀' : Obj b N (s₀ ≫ M.s)) (ms₀ : ObjMap o₀ M.univ s₀) (mt₀ : ObjMap o₀' M.univ t₀) (ψ₀ : o₀.A ⟶ o₀'.A), s₀ ≫ M.s = t₀ ≫ M.s → gs ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = s₀ → gt ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = t₀ → IsFinite gs → Etale gs → IsFinite gt → Etale gt → IsPIsog c o₀ o₀' ψ₀ → IsTj r w j o₀ o₀' ψ₀ → ∀ z : M.X, {u : M.X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' z' : Sp V ⟶ M.X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ s₀ ∧ spMap (algebraMap V K) ≫ z' = x ≫ t₀ ∧ y' (IsLocalRing.closedPoint V) = u ∧ z' (IsLocalRing.closedPoint V) = z}.Finite := by
  first | (exact @GlobalTheory.UPel.HT.ES.finite_dvrPartners_snd) | (exact GlobalTheory.UPel.HT.ES.finite_dvrPartners_snd) | (intros; apply GlobalTheory.UPel.HT.ES.finite_dvrPartners_snd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePointsClosureGenericCorrespondenceFst
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPIsogenyTargetOfDvrSpecialisation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPIsogenyTargetOfDvrSpecialisation
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section

namespace GlobalTheory.UPel.HT.ES.CorrQF

theorem exists_geomPt_closedPoint (V : Type) [CommRing V] [IsLocalRing V] (X : Scheme.{0}) (y : Sp V ⟶ X) :
    ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (σ : X.residueField (y (IsLocalRing.closedPoint V)) →+* k)
      (π : Sp k ⟶ Sp V), π ≫ y = spMap σ ≫ X.fromSpecResidueField (y (IsLocalRing.closedPoint V)) ∧
      ∀ q, π q = IsLocalRing.closedPoint V := by
  let k := AlgebraicClosure (IsLocalRing.ResidueField V)
  let g₀ : V →+* k := (algebraMap (IsLocalRing.ResidueField V) k).comp (IsLocalRing.residue V)
  haveI : IsLocalHom g₀ := RingHom.isLocalHom_comp _ _
  have hπ : ∀ q, spMap g₀ q = IsLocalRing.closedPoint V := by
    intro q
    have hq : q = IsLocalRing.closedPoint k := Subsingleton.elim (α := PrimeSpectrum k) _ _
    rw [hq]
    exact IsLocalRing.comap_closedPoint g₀
  obtain ⟨⟨x, σ⟩, h⟩ := (Scheme.SpecToEquivOfField k X).symm.surjective (spMap g₀ ≫ y)
  rw [Scheme.SpecToEquivOfField_symm_apply] at h
  have hx : x = y (IsLocalRing.closedPoint V) := by
    let q : Sp k := IsLocalRing.closedPoint k
    have e : (Spec.map σ ≫ X.fromSpecResidueField x) q = (spMap g₀ ≫ y) q := congrArg (fun g : Sp k ⟶ X => g q) h
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hπ, Scheme.fromSpecResidueField_apply] at e
    exact e
  subst hx
  exact ⟨k, inferInstance, inferInstance, σ.hom, spMap g₀, h.symm, hπ⟩

theorem exists_isogTarget_of_dvr : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (c : ℕ) (M : Model b N) (Y₀ : Scheme.{0}) (s₀ t₀ : Y₀ ⟶ M.X) (o₀ o₀' : Obj b N (s₀ ≫ M.s)) (ms₀ : ObjMap o₀ M.univ s₀) (mt₀ : ObjMap o₀' M.univ t₀) (ψ₀ : o₀.A ⟶ o₀'.A), s₀ ≫ M.s = t₀ ≫ M.s → IsPIsog c o₀ o₀' ψ₀ → ∀ u : M.X, ∀ z ∈ {z : M.X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' z' : Sp V ⟶ M.X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ s₀ ∧ spMap (algebraMap V K) ≫ z' = x ≫ t₀ ∧ y' (IsLocalRing.closedPoint V) = u ∧ z' (IsLocalRing.closedPoint V) = z}, ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (σ : M.X.residueField u →+* k) (ζ : Sp k ⟶ M.X), (∀ q, ζ q = z) ∧ CorrQF.IsogTarget M c (spMap σ ≫ M.X.fromSpecResidueField u) ζ := by
  rintro p _ D R _ b N hN hNp c M Y₀ s₀ t₀ o₀ o₀' ms₀ mt₀ ψ₀ hst hψ u z ⟨V, K, _, _, _, _, _, _, y, z', x, hxy, hxz, rfl, rfl⟩
  let eK : K →+* FractionRing V := (IsLocalization.algEquiv (nonZeroDivisors V) K (FractionRing V)).toRingEquiv.toRingHom
  have heK : eK.comp (algebraMap V K) = algebraMap V (FractionRing V) := by
    ext a; exact (IsLocalization.algEquiv (nonZeroDivisors V) K (FractionRing V)).commutes a
  let kF : Sp (FractionRing V) ⟶ Sp V := spMap (algebraMap V (FractionRing V))
  let x' : Sp (FractionRing V) ⟶ Y₀ := spMap eK ≫ x
  have hk : kF = spMap eK ≫ spMap (algebraMap V K) := by
    simp only [kF, spMap, ← heK, CommRingCat.ofHom_comp, Spec.map_comp]
  have hxy' : kF ≫ y = x' ≫ s₀ := by rw [hk, Category.assoc, hxy]; rfl
  have hxz' : kF ≫ z' = x' ≫ t₀ := by rw [hk, Category.assoc, hxz]; rfl
  obtain ⟨o, ⟨my⟩⟩ := GlobalTheory.HTPull.exists_objMap_pull p D R b N M.X (Sp V) M.s y M.univ
  obtain ⟨oK, ⟨mK⟩⟩ := GlobalTheory.HTPull.exists_objMap_pull p D R b N (Sp V) (Sp (FractionRing V)) (y ≫ M.s) kF o
  have m1 : ObjMap oK M.univ (x' ≫ s₀) := hxy' ▸ GlobalTheory.UPel.HT.ObjMapComp.comp mK my
  obtain ⟨n₀, -⟩ := GlobalTheory.HTSympCover.exists_objMap_cancel_φ m1 ms₀
  have key : ∀ σ : Sp (FractionRing V) ⟶ Sp R, x' ≫ (s₀ ≫ M.s) = σ →
      ∃ o' : Obj b N σ, Nonempty (ObjMap o' o₀' x') := by
    rintro σ rfl
    exact GlobalTheory.HTPull.exists_objMap_pull p D R b N Y₀ (Sp (FractionRing V)) (s₀ ≫ M.s) x' o₀'
  obtain ⟨oK', ⟨n₀'⟩⟩ := key (kF ≫ (y ≫ M.s)) (by rw [← Category.assoc, ← hxy', Category.assoc])
  obtain ⟨ψK, hψK, -⟩ := ValExt.isPIsog_pull p D R b N c Y₀ (Sp (FractionRing V)) (s₀ ≫ M.s) (kF ≫ (y ≫ M.s)) x'
    o₀ o₀' oK oK' n₀ n₀' ψ₀ hψ
  obtain ⟨o', m', ψ, hψV, -⟩ := IsogDVR.exists_isPIsog_extend_dvr p D R b N hN hNp c V (y ≫ M.s) o oK oK' mK ψK hψK
  obtain ⟨z, ⟨hz, ⟨mz⟩⟩, -⟩ := M.rep (Sp V) (y ≫ M.s) o'
  obtain ⟨f, -, huniq⟩ := M.rep (Sp (FractionRing V)) (kF ≫ (y ≫ M.s)) oK'
  have e1 := huniq (kF ≫ z) ⟨by rw [Category.assoc, hz], ⟨GlobalTheory.UPel.HT.ObjMapComp.comp m' mz⟩⟩
  have e2 := huniq (x' ≫ t₀) ⟨by rw [Category.assoc, ← hst, ← Category.assoc, ← hxy', Category.assoc],
    ⟨GlobalTheory.UPel.HT.ObjMapComp.comp n₀' mt₀⟩⟩
  haveI : IsSeparated M.s := by
    obtain ⟨n, i, hi, -, e⟩ := M.qproj
    have : IsSeparated (PSpace.str R n) := by
      unfold PSpace.str
      infer_instance
    rw [← e]
    infer_instance
  haveI : M.X.IsSeparated := ⟨by rw [← terminal.comp_from M.s]; infer_instance⟩
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.spec_fractionRing V (FractionRing V)
  haveI : IsDominant kF := inferInstanceAs (IsDominant (spMap (algebraMap V (FractionRing V))))
  have hzz : z = z' := ext_of_isDominant kF (by rw [e1, ← e2, hxz'])
  subst hzz
  obtain ⟨k, _, _, σ, π, hπ, hπc⟩ := exists_geomPt_closedPoint V M.X y
  refine ⟨k, inferInstance, inferInstance, σ, π ≫ z, fun q => by rw [Scheme.Hom.comp_apply, hπc], ?_⟩
  rw [← hπ]
  obtain ⟨o₁, ⟨n⟩⟩ := GlobalTheory.HTPull.exists_objMap_pull p D R b N (Sp V) (Sp k) (y ≫ M.s) π o
  obtain ⟨o₁', ⟨n'⟩⟩ := GlobalTheory.HTPull.exists_objMap_pull p D R b N (Sp V) (Sp k) (y ≫ M.s) π o'
  obtain ⟨ψ₁, hψ₁, -⟩ := ValExt.isPIsog_pull p D R b N c (Sp V) (Sp k) (y ≫ M.s) (π ≫ (y ≫ M.s)) π
    o o' o₁ o₁' n n' ψ hψV
  refine ⟨by rw [Category.assoc, Category.assoc, hz], ?_⟩
  rw [Category.assoc]
  exact ⟨o₁, o₁', ψ₁, ⟨GlobalTheory.UPel.HT.ObjMapComp.comp n my⟩, ⟨GlobalTheory.UPel.HT.ObjMapComp.comp n' mz⟩, hψ₁⟩

end GlobalTheory.UPel.HT.ES.CorrQF
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPIsogenyTargetOfDvrSpecialisationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pIsogenyTarget_of_dvr_specialisation : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (c : ℕ) (M : Model b N) (Y₀ : Scheme.{0}) (s₀ t₀ : Y₀ ⟶ M.X) (o₀ o₀' : Obj b N (s₀ ≫ M.s)) (ms₀ : ObjMap o₀ M.univ s₀) (mt₀ : ObjMap o₀' M.univ t₀) (ψ₀ : o₀.A ⟶ o₀'.A), s₀ ≫ M.s = t₀ ≫ M.s → IsPIsog c o₀ o₀' ψ₀ → ∀ u : M.X, ∀ z ∈ {z : M.X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' z' : Sp V ⟶ M.X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ s₀ ∧ spMap (algebraMap V K) ≫ z' = x ≫ t₀ ∧ y' (IsLocalRing.closedPoint V) = u ∧ z' (IsLocalRing.closedPoint V) = z}, ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (σ : M.X.residueField u →+* k) (ζ : Sp k ⟶ M.X), (∀ q, ζ q = z) ∧ CorrQF.IsogTarget M c (spMap σ ≫ M.X.fromSpecResidueField u) ζ := by
  first | (exact @GlobalTheory.UPel.HT.ES.CorrQF.exists_isogTarget_of_dvr) | (exact GlobalTheory.UPel.HT.ES.CorrQF.exists_isogTarget_of_dvr) | (intros; apply GlobalTheory.UPel.HT.ES.CorrQF.exists_isogTarget_of_dvr  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSectionOverOrdinaryLocus
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSectionOverOrdinaryLocus
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section

namespace GlobalTheory.UPel.HT.ES.CorrQF

theorem finite_specialisations_of_finite_open {R : Type} [CommRing R] {X : Scheme.{0}} (sX : X ⟶ Sp R)
    [IsSeparated sX] (U : X.Opens) (Y₀ : Scheme.{0}) (s₀ t₀ : Y₀ ⟶ X) (gs : Y₀ ⟶ U.toScheme)
    (hgs : gs ≫ U.ι = s₀) [IsFinite gs] (u : X) (hu : u ∈ U) :
    {z : X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K)
      (_ : Algebra V K) (_ : IsFractionRing V K) (y' z' : Sp V ⟶ X) (x : Sp K ⟶ Y₀),
      spMap (algebraMap V K) ≫ y' = x ≫ s₀ ∧ spMap (algebraMap V K) ≫ z' = x ≫ t₀ ∧
      y' (IsLocalRing.closedPoint V) = u ∧ z' (IsLocalRing.closedPoint V) = z}.Finite := by
  have hF : (s₀.base ⁻¹' {u}).Finite := by
    refine (gs.finite_preimage_singleton (⟨u, hu⟩ : U)).subset fun y hy => ?_
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hy ⊢
    apply U.ι.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, hgs, hy]
    rfl
  refine (hF.image t₀.base).subset ?_
  rintro z ⟨V, K, _, _, _, _, _, _, y', z', x, h1, h2, h3, h4⟩
  have hrange : Set.range y'.base ⊆ Set.range U.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint (R := V) w).map y'.continuous).mem_open U.isOpen (h3 ▸ hu)
  have hy''f : IsOpenImmersion.lift U.ι y' hrange ≫ U.ι = y' := IsOpenImmersion.lift_fac _ _ _
  have hE : ValuativeCriterion.Existence gs :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed gs) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact) gs).1
  have hw : x ≫ gs = Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ IsOpenImmersion.lift U.ι y' hrange := by
    rw [← cancel_mono U.ι, Category.assoc, hgs, Category.assoc, hy''f]
    exact h1.symm
  obtain ⟨⟨l, hl1, hl2⟩⟩ :=
    (hE { R := V, K := K, i₁ := x, i₂ := IsOpenImmersion.lift U.ι y' hrange, commSq := ⟨hw⟩ }).exists_lift
  have hl1' : spMap (algebraMap V K) ≫ l = x := hl1
  have hl2' : l ≫ gs = IsOpenImmersion.lift U.ι y' hrange := hl2
  have : IsDominant (spMap (algebraMap V K)) :=
    ⟨PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _ |>.2 (by
      exact ((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective V K)).le.trans bot_le)⟩
  have hlz : l ≫ t₀ = z' := by
    refine ext_of_isDominant_of_isSeparated (sX ≫ spMap (algebraMap ℤ R)) ?_ (spMap (algebraMap V K)) ?_
    · exact specZIsTerminal.hom_ext _ _
    · rw [reassoc_of% hl1', h2]
  refine ⟨l (IsLocalRing.closedPoint V), ?_, ?_⟩
  · simp only [Set.mem_preimage, Set.mem_singleton_iff]
    have hc : (l ≫ gs ≫ U.ι) (IsLocalRing.closedPoint V) = y' (IsLocalRing.closedPoint V) := by
      rw [reassoc_of% hl2', hy''f]
    calc s₀ (l (IsLocalRing.closedPoint V)) = (l ≫ gs ≫ U.ι) (IsLocalRing.closedPoint V) := by
          rw [hgs]; first | rfl | simp
      _ = u := hc.trans h3
  · rw [← h4, ← hlz]
    first | rfl | simp

theorem isSeparated_structure_morphism_model {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    (M : Model b N) : IsSeparated M.s := by
  obtain ⟨n, i, hi, -, e⟩ := M.qproj
  have := isProper_str R n
  rw [← e]
  infer_instance

theorem finite_specialisations_of_finite_source : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (M : Model b N) (Y₀ : Scheme.{0}) (s₀ t₀ : Y₀ ⟶ M.X) (gs : Y₀ ⟶ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme), gs ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = s₀ → IsFinite gs → ∀ u : M.X, u ∈ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))) → {z : M.X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' z' : Sp V ⟶ M.X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ s₀ ∧ spMap (algebraMap V K) ≫ z' = x ≫ t₀ ∧ y' (IsLocalRing.closedPoint V) = u ∧ z' (IsLocalRing.closedPoint V) = z}.Finite := by
  intro p _ D R _ b N M Y₀ s₀ t₀ gs hgs hfin u hu
  have := isSeparated_structure_morphism_model M
  exact finite_specialisations_of_finite_open M.s _ Y₀ s₀ t₀ gs hgs u hu

end GlobalTheory.UPel.HT.ES.CorrQF
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSectionOverOrdinaryLocusStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_section_over_ordinary_locus : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (M : Model b N) (Y₀ : Scheme.{0}) (s₀ t₀ : Y₀ ⟶ M.X) (gs : Y₀ ⟶ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme), gs ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = s₀ → IsFinite gs → ∀ u : M.X, u ∈ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))) → {z : M.X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' z' : Sp V ⟶ M.X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ s₀ ∧ spMap (algebraMap V K) ≫ z' = x ≫ t₀ ∧ y' (IsLocalRing.closedPoint V) = u ∧ z' (IsLocalRing.closedPoint V) = z}.Finite := by
  first | (exact @GlobalTheory.UPel.HT.ES.CorrQF.finite_specialisations_of_finite_source) | (exact GlobalTheory.UPel.HT.ES.CorrQF.finite_specialisations_of_finite_source) | (intros; apply GlobalTheory.UPel.HT.ES.CorrQF.finite_specialisations_of_finite_source  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePointsClosureGenericCorrespondenceFst
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES
open GlobalTheory.UPel.HT.ES.CorrQF

theorem closure_points_finite_fst : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → (p : R) ∈ IsLocalRing.maximalIdeal R → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → D.m = 1 → ∀ M : Model b N, ∀ (Y₀ : Scheme.{0}) (s₀ t₀ : Y₀ ⟶ M.X) (gs gt : Y₀ ⟶ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme) (o₀ o₀' : Obj b N (s₀ ≫ M.s)) (ms₀ : ObjMap o₀ M.univ s₀) (mt₀ : ObjMap o₀' M.univ t₀) (ψ₀ : o₀.A ⟶ o₀'.A), s₀ ≫ M.s = t₀ ≫ M.s → gs ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = s₀ → gt ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = t₀ → IsFinite gs → Etale gs → IsFinite gt → Etale gt → IsPIsog c o₀ o₀' ψ₀ → IsTj r w j o₀ o₀' ψ₀ → ∀ u : M.X, {z : M.X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' z' : Sp V ⟶ M.X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ s₀ ∧ spMap (algebraMap V K) ≫ z' = x ≫ t₀ ∧ y' (IsLocalRing.closedPoint V) = u ∧ z' (IsLocalRing.closedPoint V) = z}.Finite := by
  intro p _ D R _ _ _ _ b N hN hNp hpR r w j c hw huw hj hc hm M Y₀ s₀ t₀ gs gt o₀ o₀' ms₀ mt₀ ψ₀ hst hgs hgt hfs hes hft het hψ htj u
  by_cases hu : u ∈ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))
  · exact GlobalTheory.T.finite_section_over_ordinary_locus p D R b N M Y₀ s₀ t₀ gs hgs hfs u hu
  · set Z := {z : M.X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' z' : Sp V ⟶ M.X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ s₀ ∧ spMap (algebraMap V K) ≫ z' = x ≫ t₀ ∧ y' (IsLocalRing.closedPoint V) = u ∧ z' (IsLocalRing.closedPoint V) = z} with hZ
    have key := fun (z : Z) => GlobalTheory.T.exists_pIsogenyTarget_of_dvr_specialisation p D R b N hN hNp c M Y₀ s₀ t₀ o₀ o₀' ms₀ mt₀ ψ₀ hst hψ u z.1 z.2
    choose k hk _ σ ζ hζ hT using key
    obtain ⟨L, _, _, g, h, hg⟩ := GlobalTheory.T.exists_isAlgClosed_compatible_embeddings_of_family (M.X.residueField u) Z k σ
    refine (Set.Finite.biUnion (GlobalTheory.T.finite_pIsogenyTargets_at_charP_point p D R b N hN hNp hm c M u hu L h) fun ζ' _ => Set.finite_range (fun q : Sp L => ζ' q)).subset ?_
    intro z hz
    have h1 := GlobalTheory.T.isPIsogenyTargetOfPointPair_field_extension p D R b N M c (k ⟨z, hz⟩) L (g ⟨z, hz⟩) _ _ (hT ⟨z, hz⟩)
    have e : spMap (g ⟨z, hz⟩) ≫ spMap (σ ⟨z, hz⟩) ≫ M.X.fromSpecResidueField u = spMap h ≫ M.X.fromSpecResidueField u := by
      rw [← Category.assoc, ← hg ⟨z, hz⟩]
      simp [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
    rw [← Category.assoc] at h1
    simp only [Set.mem_iUnion, Set.mem_range]
    refine ⟨spMap (g ⟨z, hz⟩) ≫ ζ ⟨z, hz⟩, ?_, Classical.arbitrary _, ?_⟩
    · simpa [e] using h1
    · rw [Scheme.Hom.comp_apply, hζ ⟨z, hz⟩ _]

end GlobalTheory.UPel.HT.ES
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePointsClosureGenericCorrespondenceFstStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_points_closure_genericCorrespondence_fst : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → (p : R) ∈ IsLocalRing.maximalIdeal R → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → D.m = 1 → ∀ M : Model b N, ∀ (Y₀ : Scheme.{0}) (s₀ t₀ : Y₀ ⟶ M.X) (gs gt : Y₀ ⟶ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme) (o₀ o₀' : Obj b N (s₀ ≫ M.s)) (ms₀ : ObjMap o₀ M.univ s₀) (mt₀ : ObjMap o₀' M.univ t₀) (ψ₀ : o₀.A ⟶ o₀'.A), s₀ ≫ M.s = t₀ ≫ M.s → gs ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = s₀ → gt ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = t₀ → IsFinite gs → Etale gs → IsFinite gt → Etale gt → IsPIsog c o₀ o₀' ψ₀ → IsTj r w j o₀ o₀' ψ₀ → ∀ u : M.X, {z : M.X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' z' : Sp V ⟶ M.X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ s₀ ∧ spMap (algebraMap V K) ≫ z' = x ≫ t₀ ∧ y' (IsLocalRing.closedPoint V) = u ∧ z' (IsLocalRing.closedPoint V) = z}.Finite := by
  first | (exact @GlobalTheory.UPel.HT.ES.closure_points_finite_fst) | (exact GlobalTheory.UPel.HT.ES.closure_points_finite_fst) | (intros; apply GlobalTheory.UPel.HT.ES.closure_points_finite_fst <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrExtensionTargetGenericCorrespondence
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrExtensionTargetGenericCorrespondence
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES.ValExt

theorem exists_ext_target : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → (p : R) ∈ IsLocalRing.maximalIdeal R → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → D.m = 1 → ∀ M : Model b N, ∀ (Y₀ : Scheme.{0}) (s₀ t₀ : Y₀ ⟶ M.X) (gs gt : Y₀ ⟶ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme) (o₀ o₀' : Obj b N (s₀ ≫ M.s)) (ms₀ : ObjMap o₀ M.univ s₀) (mt₀ : ObjMap o₀' M.univ t₀) (ψ₀ : o₀.A ⟶ o₀'.A), s₀ ≫ M.s = t₀ ≫ M.s → gs ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = s₀ → gt ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = t₀ → IsFinite gs → Etale gs → IsFinite gt → Etale gt → IsPIsog c o₀ o₀' ψ₀ → IsTj r w j o₀ o₀' ψ₀ → ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (y : Sp V ⟶ M.X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y = x ≫ s₀ → ∃ z : Sp V ⟶ M.X, spMap (algebraMap V K) ≫ z = x ≫ t₀ :=
  of_ext GlobalTheory.UPel.HT.ES.IsogDVR.exists_isPIsog_extend_dvr

end GlobalTheory.UPel.HT.ES.ValExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrExtensionTargetGenericCorrespondenceStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dvr_extension_target_generic_correspondence : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → (p : R) ∈ IsLocalRing.maximalIdeal R → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → D.m = 1 → ∀ M : Model b N, ∀ (Y₀ : Scheme.{0}) (s₀ t₀ : Y₀ ⟶ M.X) (gs gt : Y₀ ⟶ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme) (o₀ o₀' : Obj b N (s₀ ≫ M.s)) (ms₀ : ObjMap o₀ M.univ s₀) (mt₀ : ObjMap o₀' M.univ t₀) (ψ₀ : o₀.A ⟶ o₀'.A), s₀ ≫ M.s = t₀ ≫ M.s → gs ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = s₀ → gt ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = t₀ → IsFinite gs → Etale gs → IsFinite gt → Etale gt → IsPIsog c o₀ o₀' ψ₀ → IsTj r w j o₀ o₀' ψ₀ → ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (y : Sp V ⟶ M.X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y = x ≫ s₀ → ∃ z : Sp V ⟶ M.X, spMap (algebraMap V K) ≫ z = x ≫ t₀ := by
  first | (exact @GlobalTheory.UPel.HT.ES.ValExt.exists_ext_target) | (exact GlobalTheory.UPel.HT.ES.ValExt.exists_ext_target) | (intros; apply GlobalTheory.UPel.HT.ES.ValExt.exists_ext_target  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorCorrespondenceExtendSourceDvr
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectExtendOfPIsogenyDvr
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectExtendOfPIsogenyDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES.IsogDVR

theorem exists_obj_extend_of_isPIsog : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (c : ℕ) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (v : Sp V ⟶ Sp R) (o : Obj b N v) (oK o₁ : Obj b N (spMap (algebraMap V K) ≫ v)) (m : ObjMap oK o (spMap (algebraMap V K))) (ψ : oK.A ⟶ o₁.A), IsPIsog c oK o₁ ψ → ∃ o' : Obj b N v, Nonempty (ObjMap o₁ o' (spMap (algebraMap V K))) := by
  intro p _ D R _ b N _ _ c V K _ _ _ _ _ _ v o o₀ o₀' m ψ₀ h
  have hc := h.pos
  obtain ⟨-, hhom, -, -, -, ψ', hhom', h1, h2⟩ := id h
  obtain ⟨hf, hfl⟩ := GlobalTheory.IsogFiniteFlat.isFinite_and_flat_of_quasiInverse _ o₀.A o₀'.A o₀.ab o₀'.ab ψ₀ ψ' c hc.ne'
    hhom hhom' h1 h2
  have hsc : Surjective (ψ'.left ≫ ψ₀.left) := by
    rw [← Over.comp_left, h2]; exact GlobalTheory.AbelianLimit.surjective_pow o₀'.A o₀'.ab c hc
  have hs : Surjective ψ₀.left := Surjective.of_comp ψ'.left ψ₀.left
  have hcomm := o.ab.comm
  obtain ⟨B, _, φB, hB, hφB⟩ := exists_model V K o.A o.ab o₀.A o₀'.A m.φ ψ₀ c m.cart o₀'.ab hc
    (fun T x hx => by
      have : x ≫ ψ₀ ≫ ψ' = 1 := by rw [← Category.assoc, hx, MonObj.one_comp]
      rwa [h1, MonObj.comp_pow, Category.comp_id] at this)
  exact exists_obj V K v _ rfl o₀' B φB hB hφB

end GlobalTheory.UPel.HT.ES.IsogDVR
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectExtendOfPIsogenyDvrStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_harrisTaylorObject_extend_of_pIsogeny_dvr : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (c : ℕ) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (v : Sp V ⟶ Sp R) (o : Obj b N v) (oK o₁ : Obj b N (spMap (algebraMap V K) ≫ v)) (m : ObjMap oK o (spMap (algebraMap V K))) (ψ : oK.A ⟶ o₁.A), IsPIsog c oK o₁ ψ → ∃ o' : Obj b N v, Nonempty (ObjMap o₁ o' (spMap (algebraMap V K))) := by
  first | (exact @GlobalTheory.UPel.HT.ES.IsogDVR.exists_obj_extend_of_isPIsog) | (exact GlobalTheory.UPel.HT.ES.IsogDVR.exists_obj_extend_of_isPIsog) | (intros; apply GlobalTheory.UPel.HT.ES.IsogDVR.exists_obj_extend_of_isPIsog  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorCorrespondenceExtendSourceDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section

namespace GlobalTheory.ESValT

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}

def scaleMap {S S' : Scheme.{0}} {s t : S ⟶ Sp R} {s' t' : S' ⟶ Sp R} {o : Obj b N s} {o₁ : Obj b N s'}
    {f : S' ⟶ S} (m : ObjMap o₁ o f) (e : ℕ) (h : s = t) (h' : s' = t') :
    ObjMap (ESDual.scale o₁ e h') (ESDual.scale o e h) f where
  φ := m.φ
  φ₂ := m.φ₂
  cart := m.cart
  sq := m.sq
  act := m.act
  pol := m.pol
  eta y := m.eta _

theorem extend_source : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → (p : R) ∈ IsLocalRing.maximalIdeal R → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → D.m = 1 → ∀ M : Model b N, ∀ (Y₀ : Scheme.{0}) (s₀ t₀ : Y₀ ⟶ M.X) (gs gt : Y₀ ⟶ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme) (o₀ o₀' : Obj b N (s₀ ≫ M.s)) (ms₀ : ObjMap o₀ M.univ s₀) (mt₀ : ObjMap o₀' M.univ t₀) (ψ₀ : o₀.A ⟶ o₀'.A), s₀ ≫ M.s = t₀ ≫ M.s → gs ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = s₀ → gt ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = t₀ → IsFinite gs → Etale gs → IsFinite gt → Etale gt → IsPIsog c o₀ o₀' ψ₀ → IsTj r w j o₀ o₀' ψ₀ → ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (y : Sp V ⟶ M.X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y = x ≫ t₀ → ∃ z : Sp V ⟶ M.X, spMap (algebraMap V K) ≫ z = x ≫ s₀ := by
  intro p _ D R _ _ _ _ b N hN hNp hpm r w j c _ _ _ _ _ M Y₀ s₀ t₀ gs gt o₀ o₀' ms₀ mt₀ ψ₀ hst _ _ _ _ _ _ hψ _ V K _ _ _ _ _ _ y x hy
  set κ := spMap (algebraMap V K) with hκ
  obtain ⟨e, rfl⟩ := hψ.1
  obtain ⟨f', hf'⟩ := ESDual.exists_inv_exp (N := N) (by omega) hNp e
  obtain ⟨ψ', hψ'm, h₁, h₂⟩ := hψ.2.2.2.2.2
  haveI := hψ'm
  obtain ⟨hact, heta, ⟨hpol⟩⟩ := ESDual.dual_clauses hψ h₁ h₂
  have hrev : IsPIsog (p ^ e) (ESDual.scale o₀' f' rfl) o₀ ψ' := by
    refine ⟨⟨e, rfl⟩, hψ'm, hact, fun z => ?_, ⟨hpol⟩, ψ₀, hψ.2.1, h₂, h₁⟩
    show o₀.eta z = o₀'.eta (p ^ f' • z) ≫ ψ'
    rw [← heta, smul_smul, ← pow_add, ESDual.eta_congr o₀ hf' (pow_pos (Fact.out : p.Prime).pos _)]
  obtain ⟨oV, ⟨mV⟩⟩ := GlobalTheory.HTPull.exists_objMap_pull p D R b N M.X (Sp V) M.s y M.univ
  obtain ⟨oK, ⟨mK⟩⟩ := GlobalTheory.HTPull.exists_objMap_pull p D R b N (Sp V) (Sp K) (y ≫ M.s) κ oV
  have hb : κ ≫ y ≫ M.s = x ≫ s₀ ≫ M.s := by
    rw [← Category.assoc, hy, Category.assoc, ← hst]
  obtain ⟨o₁, ⟨m₁⟩⟩ : ∃ o₁ : Obj b N (κ ≫ y ≫ M.s), Nonempty (ObjMap o₁ o₀ x) := by
    rw [hb]; exact GlobalTheory.HTPull.exists_objMap_pull p D R b N Y₀ (Sp K) (s₀ ≫ M.s) x o₀
  have mKU : ObjMap oK M.univ (x ≫ t₀) := hy ▸ ESDual.compMap mK mV
  obtain ⟨mK0, -⟩ := GlobalTheory.HTSympCover.exists_objMap_cancel_φ mKU mt₀
  obtain ⟨ψK, hψK, -⟩ := GlobalTheory.T.isPIsogenyOfSimilitude_pullback_objects p D R b N (p ^ e) Y₀ (Sp K) (s₀ ≫ M.s) (κ ≫ y ≫ M.s) x _ _
    (ESDual.scale oK f' rfl) o₁ (scaleMap mK0 f' rfl rfl) m₁ ψ' hrev
  obtain ⟨o'', ⟨m''⟩⟩ := GlobalTheory.T.exists_harrisTaylorObject_extend_of_pIsogeny_dvr p D R b N hN hNp (p ^ e) V K (y ≫ M.s) (ESDual.scale oV f' rfl)
    (ESDual.scale oK f' rfl) o₁ (scaleMap mK f' rfl rfl) ψK hψK
  obtain ⟨z, ⟨hz, ⟨mz⟩⟩, -⟩ := M.rep (Sp V) (y ≫ M.s) o''
  refine ⟨z, ?_⟩
  obtain ⟨g, -, hg⟩ := M.rep (Sp K) (κ ≫ y ≫ M.s) o₁
  have e1 := hg (κ ≫ z) ⟨by rw [Category.assoc, hz], ⟨ESDual.compMap m'' mz⟩⟩
  have e2 := hg (x ≫ s₀) ⟨by rw [Category.assoc, hb], ⟨ESDual.compMap m₁ ms₀⟩⟩
  exact e1.trans e2.symm

end GlobalTheory.ESValT
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorCorrespondenceExtendSourceDvrStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_correspondence_extend_source_dvr : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → (p : R) ∈ IsLocalRing.maximalIdeal R → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → D.m = 1 → ∀ M : Model b N, ∀ (Y₀ : Scheme.{0}) (s₀ t₀ : Y₀ ⟶ M.X) (gs gt : Y₀ ⟶ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme) (o₀ o₀' : Obj b N (s₀ ≫ M.s)) (ms₀ : ObjMap o₀ M.univ s₀) (mt₀ : ObjMap o₀' M.univ t₀) (ψ₀ : o₀.A ⟶ o₀'.A), s₀ ≫ M.s = t₀ ≫ M.s → gs ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = s₀ → gt ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = t₀ → IsFinite gs → Etale gs → IsFinite gt → Etale gt → IsPIsog c o₀ o₀' ψ₀ → IsTj r w j o₀ o₀' ψ₀ → ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (y : Sp V ⟶ M.X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y = x ≫ t₀ → ∃ z : Sp V ⟶ M.X, spMap (algebraMap V K) ≫ z = x ≫ s₀ := by
  first | (exact @GlobalTheory.ESValT.extend_source) | (exact GlobalTheory.ESValT.extend_source) | (intros; apply GlobalTheory.ESValT.extend_source <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFibreCorrespondenceOfIsFiniteFirst
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFibreCorrespondenceOfIsFiniteFirst
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.FibreCrit

theorem exists_generization_mem {Y : Scheme.{0}} [IsLocallyNoetherian Y] {O : Set Y} (hO : IsOpen O)
    (hd : Dense O) (y : Y) : ∃ e0 : Y, e0 ⤳ y ∧ e0 ∈ O := by
  obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (U := ⊤) (x := y) trivial
  have : IsAffine U := hU
  have : IsNoetherian U.toScheme := {}
  obtain ⟨y', rfl⟩ : y ∈ Set.range U.ι := by rw [Scheme.Opens.range_ι]; exact hyU
  have hC := irreducibleComponent_mem_irreducibleComponents y'
  obtain ⟨o, ho, hne, hoC⟩ :=
    TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent _ hC
  obtain ⟨_, ⟨w, hwo, rfl⟩, hwO⟩ :=
    hd.inter_open_nonempty _ (U.ι.isOpenEmbedding.isOpenMap _ ho) (hne.image _)
  have hg := hC.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ hC)
  exact ⟨U.ι hC.1.genericPoint, (hg.specializes mem_irreducibleComponent).map U.ι.continuous,
    ((hg.specializes (hoC hwo)).map U.ι.continuous).mem_open hO hwO⟩

theorem spMap_algebraMap_apply (V K : Type) [CommRing V] [IsDomain V] [Field K] [Algebra V K]
    [IsFractionRing V K] (p : Sp K) : spMap (algebraMap V K) p = (⊥ : PrimeSpectrum V) := by
  refine PrimeSpectrum.ext ?_
  show Ideal.comap (algebraMap V K) p.asIdeal = ⊥
  rw [(Ideal.eq_bot_or_top p.asIdeal).resolve_right p.isPrime.ne_top, ← RingHom.ker_eq_comap_bot]
  exact (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective V K)

end GlobalTheory.FibreCrit

namespace GlobalTheory.FibreCrit

theorem finite_fibre_of_isFinite : ∀ (X Y₀ Y : Scheme.{0}) (s t : Y ⟶ X) (i : Y₀ ⟶ Y), IsFinite s → IsOpenImmersion i → IsDominant i → IsLocallyNoetherian Y → (∀ z : X, {u : X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' z' : Sp V ⟶ X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ i ≫ s ∧ spMap (algebraMap V K) ≫ z' = x ≫ i ≫ t ∧ y' (IsLocalRing.closedPoint V) = u ∧ z' (IsLocalRing.closedPoint V) = z}.Finite) → ∀ z : X, {y : Y | t y = z}.Finite := by
  intro X Y₀ Y s t i hs hi hd hY hfin z
  refine (s.finite_preimage (hfin z)).subset ?_
  intro y hy
  simp only [Set.mem_ofPred_eq] at hy
  obtain ⟨e0, he0y, he0i⟩ := exists_generization_mem i.isOpenEmbedding.isOpen_range i.denseRange y
  obtain ⟨V, _, _, _, g, hg0, hg1⟩ : ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V)
      (_ : IsDiscreteValuationRing V) (g : Sp V ⟶ Y),
      g (⊥ : PrimeSpectrum V) ∈ Set.range i ∧ g (IsLocalRing.closedPoint V) = y := by
    by_cases he : e0 = y
    · subst he
      have hpt : ∀ q, (spMap (algebraMap (Y.residueField e0) (PowerSeries (Y.residueField e0))) ≫
          Y.fromSpecResidueField e0) q = e0 := fun q => by
        have h := Set.mem_range_self (f := Y.fromSpecResidueField e0)
          (spMap (algebraMap (Y.residueField e0) (PowerSeries (Y.residueField e0))) q)
        rw [Scheme.range_fromSpecResidueField] at h
        rw [Scheme.Hom.comp_apply]
        exact h
      exact ⟨PowerSeries (Y.residueField e0), inferInstance, inferInstance, inferInstance,
        spMap (algebraMap (Y.residueField e0) (PowerSeries (Y.residueField e0))) ≫
          Y.fromSpecResidueField e0, (hpt _).symm ▸ he0i, hpt _⟩
    · obtain ⟨O, hO, hV, -, f, hf0, hf1⟩ :=
        GlobalTheory.exists_complete_discreteValuationRing_of_specializes he0y he
      exact ⟨O, inferInstance, hO, hV, f, hf0 ▸ he0i, hf1⟩
  have hr : Set.range (spMap (algebraMap V (FractionRing V)) ≫ g) ⊆ Set.range i := by
    rintro _ ⟨q, rfl⟩
    rw [Scheme.Hom.comp_apply, spMap_algebraMap_apply V (FractionRing V) q]
    exact hg0
  refine ⟨V, FractionRing V, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, g ≫ s, g ≫ t, IsOpenImmersion.lift i _ hr, ?_, ?_, ?_, ?_⟩
  · exact (congrArg (· ≫ s) (IsOpenImmersion.lift_fac i _ hr)).symm.trans (Category.assoc _ _ _)
  · exact (congrArg (· ≫ t) (IsOpenImmersion.lift_fac i _ hr)).symm.trans (Category.assoc _ _ _)
  · exact (Scheme.Hom.comp_apply g s _).trans (congrArg s hg1)
  · exact ((Scheme.Hom.comp_apply g t _).trans (congrArg t hg1)).trans hy

end GlobalTheory.FibreCrit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFibreCorrespondenceOfIsFiniteFirstStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_fibre_correspondence_of_isFinite_first : ∀ (X Y₀ Y : Scheme.{0}) (s t : Y ⟶ X) (i : Y₀ ⟶ Y), IsFinite s → IsOpenImmersion i → IsDominant i → IsLocallyNoetherian Y → (∀ z : X, {u : X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' z' : Sp V ⟶ X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ i ≫ s ∧ spMap (algebraMap V K) ≫ z' = x ≫ i ≫ t ∧ y' (IsLocalRing.closedPoint V) = u ∧ z' (IsLocalRing.closedPoint V) = z}.Finite) → ∀ z : X, {y : Y | t y = z}.Finite := by
  first | (exact @GlobalTheory.FibreCrit.finite_fibre_of_isFinite) | (exact GlobalTheory.FibreCrit.finite_fibre_of_isFinite) | (intros; apply GlobalTheory.FibreCrit.finite_fibre_of_isFinite  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperOfDvrLiftThroughFiniteCorrespondence
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperOfDvrLiftThroughFiniteCorrespondence
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.FiniteCoverProper

theorem isProper_of_lift_through_finite : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X Y₀ Y : Scheme.{0}) (τ : X ⟶ Sp R) (s t : Y ⟶ X) (i : Y₀ ⟶ Y), IsQProjOver τ → IsFinite s → IsOpenImmersion i → IsDominant i → t ≫ τ = s ≫ τ → (∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (y : Sp V ⟶ X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y = x ≫ i ≫ t → ∃ z : Sp V ⟶ X, spMap (algebraMap V K) ≫ z = x ≫ i ≫ s) → IsProper t := by
  intro R _ _ X Y₀ Y τ s t i hτ hs hi hd ht h
  have hX : IsLocallyNoetherian X := by
    obtain ⟨N, j, hj, -, e⟩ := hτ
    have : IsProper (PSpace.str R N) := isProper_str R N
    have : LocallyOfFiniteType τ := by rw [← e]; infer_instance
    have : IsLocallyNoetherian (Sp R) :=
      inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of R)))
    exact LocallyOfFiniteType.isLocallyNoetherian τ
  have hsep : IsSeparated τ := by
    obtain ⟨N, j, hj, -, e⟩ := hτ
    have : IsProper (PSpace.str R N) := isProper_str R N
    have : IsImmersion j := hj
    rw [← e]; infer_instance
  have hY : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian s
  have hq : IsQProjOver (t ≫ τ) := ht ▸ GlobalTheory.isQProjOver_comp_of_isFinite_general s hτ
  refine GlobalTheory.ValuativeGeneric.isProper_of_lift_generic R Y X t τ hsep hq ?_
  intro V K _ _ _ _ _ _ _ x y hx hxy
  have hgen : genericPoints Y ⊆ Set.range i := GlobalTheory.genericPoints_subset_range_of_isDominant i
  have hr : Set.range x ⊆ Set.range i := hx.trans hgen
  have hx₀ : IsOpenImmersion.lift i x hr ≫ i = x := IsOpenImmersion.lift_fac i x hr
  obtain ⟨z, hz⟩ := h V K y (IsOpenImmersion.lift i x hr) (by rw [← Category.assoc, hx₀, hxy])
  have hE : ValuativeCriterion.Existence s :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed s) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact) s).1
  have hw : x ≫ s = Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ z := by
    rw [← hx₀, Category.assoc]; exact hz.symm
  obtain ⟨⟨x', hx', -⟩⟩ := (hE { R := V, K := K, i₁ := x, i₂ := z, commSq := ⟨hw⟩ }).exists_lift
  exact ⟨x', hx'⟩

end GlobalTheory.FiniteCoverProper
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperOfDvrLiftThroughFiniteCorrespondenceStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isProper_of_dvr_lift_through_finite_correspondence : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X Y₀ Y : Scheme.{0}) (τ : X ⟶ Sp R) (s t : Y ⟶ X) (i : Y₀ ⟶ Y), IsQProjOver τ → IsFinite s → IsOpenImmersion i → IsDominant i → t ≫ τ = s ≫ τ → (∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (y : Sp V ⟶ X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y = x ≫ i ≫ t → ∃ z : Sp V ⟶ X, spMap (algebraMap V K) ≫ z = x ≫ i ≫ s) → IsProper t := by
  first | (exact @GlobalTheory.FiniteCoverProper.isProper_of_lift_through_finite) | (exact GlobalTheory.FiniteCoverProper.isProper_of_lift_through_finite) | (intros; apply GlobalTheory.FiniteCoverProper.isProper_of_lift_through_finite  <;> assumption)
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section

namespace GlobalTheory.ExtT

theorem exists_finite_extension : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → (p : R) ∈ IsLocalRing.maximalIdeal R → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → D.m = 1 → ∀ M : Model b N, ∀ (Y₀ : Scheme.{0}) (s₀ t₀ : Y₀ ⟶ M.X) (gs gt : Y₀ ⟶ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme) (o₀ o₀' : Obj b N (s₀ ≫ M.s)) (ms₀ : ObjMap o₀ M.univ s₀) (mt₀ : ObjMap o₀' M.univ t₀) (ψ₀ : o₀.A ⟶ o₀'.A), s₀ ≫ M.s = t₀ ≫ M.s → gs ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = s₀ → gt ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = t₀ → IsFinite gs → Etale gs → IsFinite gt → Etale gt → IsPIsog c o₀ o₀' ψ₀ → IsTj r w j o₀ o₀' ψ₀ → ∀ (Y : Scheme.{0}) (s : Y ⟶ M.X) (i : Y₀ ⟶ Y), IsOpenImmersion i → IsDominant i → i ≫ s = s₀ → IsFinite s → (∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) → Flat (s ≫ M.s) → IsLocallyNoetherian Y → (∀ (S : Scheme.{0}) (f : S ⟶ Y), IsUnit ((p : ℕ) : Γ(S, ⊤)) → ∃ f₀ : S ⟶ Y₀, f₀ ≫ i = f) → ∃ t : Y ⟶ M.X, i ≫ t = t₀ ∧ t ≫ M.s = s ≫ M.s ∧ IsFinite t := by
  intro p _ D R _ _ _ _ b N hN hNp hpm r w j c hw hu hj hc hm M Y₀ s₀ t₀ gs gt o₀ o₀' ms₀ mt₀ ψ₀ hst hgs hgt hfs
    hes hft het hiso htj Y s i hio hid his hsf hnorm hflat hln hfac
  have hred : IsReduced Y := GlobalTheory.T.isReduced_normalModel_generic_correspondence p D R b N hpm M Y₀ s₀ gs hgs hes Y s i hio his hflat hfac
  have hval : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
      [IsFractionRing V K] (y : Sp V ⟶ Y) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y = x ≫ i →
      ∃ z : Sp V ⟶ M.X, spMap (algebraMap V K) ≫ z = x ≫ t₀ := by
    intro V K _ _ _ _ _ _ y x hy
    exact GlobalTheory.T.exists_dvr_extension_target_generic_correspondence p D R b N hN hNp hpm r w j c hw hu hj hc hm M Y₀ s₀ t₀ gs gt o₀ o₀' ms₀ mt₀ ψ₀ hst hgs hgt hfs hes hft het hiso htj V K (y ≫ s) x (by rw [← Category.assoc, hy, Category.assoc, his])
  have hqf : ∀ y : Y, {z : M.X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V)
      (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' : Sp V ⟶ Y) (z' : Sp V ⟶ M.X)
      (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ i ∧ spMap (algebraMap V K) ≫ z' = x ≫ t₀ ∧
      y' (IsLocalRing.closedPoint V) = y ∧ z' (IsLocalRing.closedPoint V) = z}.Finite := by
    intro y
    refine (GlobalTheory.T.finite_points_closure_genericCorrespondence_fst p D R b N hN hNp hpm r w j c hw hu hj hc hm M Y₀ s₀ t₀ gs gt o₀ o₀' ms₀ mt₀ ψ₀ hst hgs hgt hfs hes hft het hiso htj (s y)).subset ?_
    rintro z ⟨V, K, i1, i2, i3, i4, i5, i6, y', z', x, h1, h2, h3, h4⟩
    exact ⟨V, K, i1, i2, i3, i4, i5, i6, y' ≫ s, z', x, by rw [← Category.assoc, h1, Category.assoc, his], h2,
      by rw [← h3]; rfl, h4⟩
  obtain ⟨t, hit, htσ⟩ := GlobalTheory.T.extension_over_normal_quasi_projective_base R Y₀ Y M.X i (s ≫ M.s) M.s t₀ hio hid hln hred hnorm M.qproj
    (by rw [reassoc_of% his, hst]) hval hqf
  have hP : IsProper t := GlobalTheory.T.isProper_of_dvr_lift_through_finite_correspondence R M.X Y₀ Y M.s s t i M.qproj hsf hio hid htσ (fun V K _ _ _ _ _ _ y x hy => by
    obtain ⟨z, hz⟩ := GlobalTheory.T.harrisTaylor_correspondence_extend_source_dvr p D R b N hN hNp hpm r w j c hw hu hj hc hm M Y₀ s₀ t₀ gs gt o₀ o₀' ms₀ mt₀ ψ₀ hst hgs hgt hfs hes hft het hiso htj V K y x (by rw [hy, hit])
    exact ⟨z, by rw [hz, his]⟩)
  have hC : ∀ z : M.X, {y : Y | t y = z}.Finite := GlobalTheory.T.finite_fibre_correspondence_of_isFinite_first M.X Y₀ Y s t i hsf hio hid hln (fun z => by
    simpa only [his, hit] using GlobalTheory.T.finite_points_closure_genericCorrespondence_snd p D R b N hN hNp hpm r w j c hw hu hj hc hm M Y₀ s₀ t₀ gs gt o₀ o₀' ms₀ mt₀ ψ₀ hst hgs hgt hfs hes hft het hiso htj z)
  haveI : LocallyQuasiFinite t := LocallyQuasiFinite.of_finite_preimage_singleton t hC
  exact ⟨t, hit, htσ, IsFinite.of_isProper_of_locallyQuasiFinite t⟩

end GlobalTheory.ExtT
