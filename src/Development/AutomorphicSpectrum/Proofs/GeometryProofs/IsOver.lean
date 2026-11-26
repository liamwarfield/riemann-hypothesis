module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GrGenOfIsFlagVBOn
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateFunctionalUnique

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsOver
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

def IsOver {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H} {Xo : Moduli D l}
    {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type}
    [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y) (z : Sp ℂ ⟶ 𝔐.X) (κ : c.F →+* ℂ)
    (p : Sp ℂ ⟶ Xo.X) : Prop :=
  ∃ x : Sp ℂ ⟶ Xo.XF c, x ≫ Y.j = z ≫ 𝔐.f ∧ x ≫ pullback.fst _ _ = p ∧ x ≫ pullback.snd _ _ = spMap κ

end GlobalTheory.CompanionTheory.Ar.Cusp.FamEx
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeStableUnderAction
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeStableUnderAction
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieStable

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem lat_stable : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G : Over X) [GrpObj G] (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel G ξ V) (O : Type) [CommRing O] (act : OAct O G) (ρ : O →+* Module.End Ω V), M.IsActOf act.act ρ → ∀ (p : Cpt ξ) (a : O), ∀ e ∈ M.lat p, ρ a e ∈ M.lat p := by
  intro X Ω _ ξ G _ V _ _ M O _ act ρ hact p a e he
  change e ∈ Submodule.span (regAt ξ p) {e | ∃ v, M.Extends p e v} at he
  change ρ a e ∈ Submodule.span (regAt ξ p) {e | ∃ v, M.Extends p e v}
  induction he using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv⟩ := hx
    unfold LieModel.Extends at hv
    obtain ⟨hv1, hv2⟩ := hv
    refine Submodule.subset_span ⟨v ≫ act.act a, ?_⟩
    unfold LieModel.Extends
    refine ⟨?_, ?_⟩
    · unfold IsTanAt at hv1 ⊢
      have := act.hom a
      rw [Over.comp_left, ← Category.assoc, hv1, ← Over.comp_left]
      congr 1
      simp
    · have h := hact a x
      rw [h, Over.comp_left, hv2, Over.comp_left]
      exact Category.assoc _ _ _
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r x _ hx =>
    rw [Subring.smul_def, map_smul, ← Subring.smul_def]
    exact Submodule.smul_mem _ r hx

end GlobalTheory.CompanionTheory.Ar.LieStable
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeStableUnderActionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
alias GlobalTheory.T.lie_lattice_stable_under_action := GlobalTheory.CompanionTheory.Ar.LieStable.lat_stable
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntegralElementRegular
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntegralElementRegular
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.IntReg

theorem mem_regAt_of_isIntegral_of_stalk :
    ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (p : Cpt ξ), IsCptGen ξ →
      IsIntegrallyClosed (X.presheaf.stalk p.1) → ∀ a : Ω, IsIntegral ℤ a → a ∈ regAt ξ p := by
  intro X Ω _ ξ p hξ hcl a ha
  have hinj : Function.Injective (genMap ξ p) := hξ.inj p
  let _ : Algebra (X.presheaf.stalk p.1) Ω := (genMap ξ p).toAlgebra
  have hmap : ∀ x, algebraMap (X.presheaf.stalk p.1) Ω x = genMap ξ p x := fun _ => rfl
  have : IsDomain (X.presheaf.stalk p.1) := hinj.isDomain _
  have : FaithfulSMul (X.presheaf.stalk p.1) Ω :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  have : IsFractionRing (X.presheaf.stalk p.1) Ω := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨b, c, hc, e⟩ := exists_frac_genMap ξ hξ p z
    exact ⟨b, c, by rw [hmap, hmap, ← e, mul_div_cancel_right₀ _ hc]⟩
  have hb : _root_.IsIntegral (X.presheaf.stalk p.1) a := ha.tower_top
  obtain ⟨w, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hb
  exact ⟨w, rfl⟩

end GlobalTheory.CompanionTheory.Ar.IntReg
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntegralElementRegularStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
alias GlobalTheory.T.integral_element_regular := GlobalTheory.CompanionTheory.Ar.IntReg.mem_regAt_of_isIntegral_of_stalk
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackMap
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.LieJ

noncomputable def epsOver {X : Scheme.{0}} {Ω Ω' : Type} [CommRing Ω] [CommRing Ω'] (x : Sp Ω ⟶ X) (y : Sp Ω' ⟶ X) (i : Ω →+* Ω')
    (h : y = Spec.map (CommRingCat.ofHom i) ≫ x) : epsAt y ⟶ epsAt x :=
  Over.homMk (Spec.map (CommRingCat.ofHom (dualMap i))) (by
    subst h
    have hr : (dualMap i).comp (algebraMap Ω (DualNumber Ω)) = (algebraMap Ω' (DualNumber Ω')).comp i := by
      ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
    show Spec.map (CommRingCat.ofHom (dualMap i)) ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω (DualNumber Ω))) ≫ x =
      Spec.map (CommRingCat.ofHom (algebraMap Ω' (DualNumber Ω'))) ≫ Spec.map (CommRingCat.ofHom i) ≫ x
    rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, hr])

theorem isTanAt_epsOver {X : Scheme.{0}} {Ω Ω' : Type} [CommRing Ω] [CommRing Ω'] (G : Over X) [GrpObj G]
    (x : Sp Ω ⟶ X) (y : Sp Ω' ⟶ X) (i : Ω →+* Ω') (h : y = Spec.map (CommRingCat.ofHom i) ≫ x)
    (v : epsAt x ⟶ G) (hv : IsTanAt G x v) : IsTanAt G y (epsOver x y i h ≫ v) := by
  have hr : (TrivSqZeroExt.fstHom Ω' Ω' Ω').toRingHom.comp (dualMap i) = i.comp (TrivSqZeroExt.fstHom Ω Ω Ω).toRingHom := by
    refine RingHom.ext fun a => ?_
    simp [dualMap]
  have hone : (Over.homMk (Spec.map (CommRingCat.ofHom i)) h.symm : Over.mk y ⟶ Over.mk x) ≫ (1 : Over.mk x ⟶ G) = 1 := by
    exact MonObj.comp_one _
  have h1 := congrArg (fun w => w.left) hone
  show Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom Ω' Ω' Ω').toRingHom) ≫ Spec.map (CommRingCat.ofHom (dualMap i)) ≫ v.left = _
  rw [← h1, Over.comp_left, ← hv, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hr, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  rfl

theorem exists_map : ∀ (X X' : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω' ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω') (G : Over X) (G' : Over X') [GrpObj G] [GrpObj G'] (φ : G'.left ⟶ G.left) (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] (M : LieModel G ξ V) (M' : LieModel G' ξ' V'), GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → IsGrpPullback G' G f φ → ∃ j : V →+ V', ∀ e, (M'.pt (j e)).left ≫ φ = Spec.map (CommRingCat.ofHom (dualMap i)) ≫ (M.pt e).left := by
  intro X X' Ω Ω' _ _ ξ ξ' f i G G' _ _ φ V V' _ _ _ _ M M' hd hp
  obtain ⟨N, hN⟩ := (LiePull.lieModel_pullback X X' G G' f φ hp Ω' ξ' V').2 M'
  have ex : ∀ e, ∃ t, N.pt t = epsOver ξ (ξ' ≫ f) i hd ≫ M.pt e :=
    fun e => N.onto _ (isTanAt_epsOver G ξ (ξ' ≫ f) i hd _ (M.tan e))
  choose g hg using ex
  refine ⟨AddMonoidHom.mk' g fun a b => N.inj ?_, fun e => ?_⟩
  · rw [N.add, hg, hg, hg, M.add, comp_mul]
  · show (M'.pt (g e)).left ≫ φ = _
    rw [hN, hg]
    rfl

end GlobalTheory.CompanionTheory.Ar.LieJ
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackMapStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
alias GlobalTheory.T.lie_model_pullback_map := GlobalTheory.CompanionTheory.Ar.LieJ.exists_map
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DualMapOfFieldExtension
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DualMapOfFieldExtension
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.DualExt

theorem dual_ext : ∀ (Ω Ω' : Type) [Field Ω] [Field Ω'] (i : Ω →+* Ω') (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] (j : V →+ V'), IsExtOver i j → Submodule.span Ω' (Set.range j) = ⊤ → ∃ jd : Module.Dual Ω V →+ Module.Dual Ω' V', ∀ w e, jd w (j e) = i (w e) := by
  intro Ω Ω' _ _ i V V' _ _ _ _ j hext hspan
  let b := Module.Basis.ofVectorSpace Ω V
  have hj : ∀ e : V, j e = (b.repr e).sum fun k a => i a • j (b k) := by
    intro e
    conv_lhs => rw [← b.linearCombination_repr e]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, Finsupp.sum]
    exact Finset.sum_congr rfl fun k _ => hext.1 _ _
  have hli : LinearIndependent Ω' fun k => j (b k) := by
    rw [linearIndependent_iff_finset_linearIndependent]
    intro s
    have h := hext.2 s.card (fun m => b (s.equivFin.symm m))
      (b.linearIndependent.comp (fun m => (s.equivFin.symm m : _))
        (Subtype.val_injective.comp s.equivFin.symm.injective))
    have h2 := h.comp s.equivFin s.equivFin.injective
    convert h2 using 1
    funext k
    simp
  have hsp : ⊤ ≤ Submodule.span Ω' (Set.range fun k => j (b k)) := by
    rw [← hspan, Submodule.span_le]
    rintro _ ⟨e, rfl⟩
    rw [hj e, Finsupp.sum]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  let b' := Module.Basis.mk hli hsp
  refine ⟨AddMonoidHom.mk' (fun w => b'.constr Ω' fun k => i (w (b k))) fun w₁ w₂ => ?_, fun w e => ?_⟩
  · rw [← map_add (f := _)]
    congr 1
    funext k
    simp
  · show b'.constr Ω' (fun k => i (w (b k))) (j e) = i (w e)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hj e, Finsupp.sum, map_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      conv_rhs => rw [← b.linearCombination_repr e, Finsupp.linearCombination_apply, Finsupp.sum,
      map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, show j (b k) = b' k from (Module.Basis.mk_apply hli hsp k).symm, Module.Basis.constr_basis,
      map_smul, smul_eq_mul, smul_eq_mul, map_mul]

end GlobalTheory.CompanionTheory.Ar.DualExt
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DualMapOfFieldExtensionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
alias GlobalTheory.T.dual_map_of_field_extension := GlobalTheory.CompanionTheory.Ar.DualExt.dual_ext
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackAction
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackAction
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.LieBaseAct

theorem baseChange_act : ∀ (X X' : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω' ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω') (G : Over X) (G' : Over X') [GrpObj G] [GrpObj G'] (φ : G'.left ⟶ G.left) (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] (M : LieModel G ξ V) (M' : LieModel G' ξ' V') (j : V →+ V') (O : Type) [CommRing O] (act : O → (G ⟶ G)) (act' : O → (G' ⟶ G')) (ρ : O →+* Module.End Ω V) (ρ' : O →+* Module.End Ω' V'), GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → IsGrpPullback G' G f φ → (∀ e, (M'.pt (j e)).left ≫ φ = Spec.map (CommRingCat.ofHom (dualMap i)) ≫ (M.pt e).left) → M.IsActOf act ρ → M'.IsActOf act' ρ' → (∀ a, (act' a).left ≫ φ = φ ≫ (act a).left) → ∀ a e, ρ' a (j e) = j (ρ a e) := by
  intro X X' Ω Ω' _ _ ξ ξ' f i G G' _ _ φ V V' _ _ _ _ M M' j O _ act act' ρ ρ' _ hpb hpt hM hM' hcomm a e
  apply M'.inj
  rw [hM' a (j e)]
  apply Over.OverMorphism.ext
  apply hpb.1.hom_ext
  · simp only [Over.comp_left, Category.assoc, hcomm a]
    rw [← Category.assoc, hpt e, hpt (ρ a e), hM a e, Over.comp_left]
    simp only [Category.assoc]
  · rw [Over.w, Over.w]

end GlobalTheory.CompanionTheory.Ar.LieBaseAct
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackActionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
alias GlobalTheory.T.lie_model_pullback_action := GlobalTheory.CompanionTheory.Ar.LieBaseAct.baseChange_act
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DualRevDualRev
namespace GlobalTheory.CompanionTheory.Ar.Num.HodgeModel

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {K : Type} {ι : K → Type} {R : Type} [CommRing R]

def dualRev {r : ℕ} (Q : LocPair ι R (Fin r)) : LocPair ι R (Fin r) :=
  ⟨fun i => -Q.x (Fin.rev i), fun i => -Q.x' (Fin.rev i), fun i => Q.g (Fin.rev i), fun i => Q.f (Fin.rev i)⟩

def labelPair (D : Datum H) (T : LocPair ι R (CMType H × Fin (D.p + D.q))) :
    ∀ s : CMType H ⊕ CMType H, LocPair ι R (Fin (labelRk D s))
  | .inl τ => T.comp fun i => (τ, Fin.castAdd D.q i)
  | .inr τ => dualRev (T.comp fun i => (τ, Fin.natAdd D.p i))

def omPair (D : Datum H) (T : LocPair ι R (CMType H × Fin (D.p + D.q))) :
    ∀ s : CMType H ⊕ CMType H, LocPair ι R (Fin (labelRk D s.swap)) :=
  fun s => dualRev (labelPair D T s.swap)

def omPairM (D : Datum H) (T : LocPair ι R (CMType H × Fin (D.p + D.q))) :
    ∀ s : CMType H ⊕ CMType H, LocPair ι R (Fin (Sum.elim (fun _ : CMType H => D.q) (fun _ : CMType H => D.p) s))
  | .inl τ => omPair D T (.inl τ)
  | .inr τ => omPair D T (.inr τ)

theorem dualRev_dualRev {r : ℕ} (Q : LocPair ι R (Fin r)) : dualRev (dualRev Q) = Q := by
  obtain ⟨x, x', f, g⟩ := Q
  simp [dualRev, Fin.rev_rev]

theorem map_map {R' R'' : Type} [CommRing R'] [CommRing R''] {σ : Type} (T : LocPair ι R σ) (ψ : R →+* R')
    (ψ' : R' →+* R'') : (T.map ψ).map ψ' = T.map (ψ'.comp ψ) := by
  obtain ⟨x, x', f, g⟩ := T
  simp [LocPair.map, MvPolynomial.map_map]

end GlobalTheory.CompanionTheory.Ar.Num.HodgeModel
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DifferentScaledLatticeExtension
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DifferentScaledLatticeExtension
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem scale_pull_ext : ∀ (Ω Ω' : Type) [Field Ω] [Field Ω'] (i : Ω →+* Ω') (R : Subring Ω) (R' : Subring Ω') (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] (j : V →+ V') (W : Submodule Ω V) (W' : Submodule Ω' V') (O : Type) [CommRing O] (σ : O →+* Ω) (𝔡 : Ideal O) (d₀ : O) (D : Submodule R V) (D' : Submodule R' V'), IsExtOver i j → (∀ a ∈ R, i a ∈ R') → W' = Submodule.span Ω' (j '' (W : Set V)) → d₀ ∈ 𝔡 → σ d₀ ≠ 0 → (∀ d ∈ 𝔡, σ d / σ d₀ ∈ R) → (∀ e ∈ D, e ∈ W) → D' = Submodule.span R' (j '' (D : Set V)) → Submodule.span R' {e | e ∈ W' ∧ ∀ d ∈ 𝔡, (i.comp σ) d • e ∈ D'} = Submodule.span R' (j '' (Submodule.span R {e | e ∈ W ∧ ∀ d ∈ 𝔡, σ d • e ∈ D} : Set V)) := by
  intro Ω Ω' _ _ i R R' V V' _ _ _ _ j W W' O _ σ 𝔡 d₀ D D' hsemi hR hW' hd₀ hσd₀ hdiv hDW hD'
  have hj : ∀ (a : Ω) (v : V), j (a • v) = i a • j v := hsemi.1
  subst hW' hD'
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro e ⟨-, he⟩
    have hu : i (σ d₀) ≠ 0 := (map_ne_zero i).mpr hσd₀
    have key : ∀ y ∈ Submodule.span R' (j '' (D : Set V)),
        (i (σ d₀))⁻¹ • y ∈ Submodule.span R'
          (j '' (Submodule.span R {e | e ∈ W ∧ ∀ d ∈ 𝔡, σ d • e ∈ D} : Set V)) := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨x, hx, rfl⟩ := hy
        apply Submodule.subset_span
        refine ⟨(σ d₀)⁻¹ • x, Submodule.subset_span ⟨W.smul_mem (σ d₀)⁻¹ (hDW x hx), fun d hd => ?_⟩, ?_⟩
        · rw [smul_smul, ← div_eq_mul_inv]
          exact D.smul_mem ⟨σ d / σ d₀, hdiv d hd⟩ hx
        · rw [hj, map_inv₀]
      | zero => rw [smul_zero]; exact Submodule.zero_mem _
      | add y z _ _ hy hz => rw [smul_add]; exact Submodule.add_mem _ hy hz
      | smul a y _ hy =>
        have e1 : (i (σ d₀))⁻¹ • (a • y) = a • ((i (σ d₀))⁻¹ • y) :=
          show (i (σ d₀))⁻¹ • ((a : Ω') • y) = (a : Ω') • ((i (σ d₀))⁻¹ • y) by
            rw [smul_smul, smul_smul, mul_comm]
        rw [e1]
        exact Submodule.smul_mem _ a hy
    have h1 := key _ (he d₀ hd₀)
    rwa [RingHom.comp_apply, inv_smul_smul₀ hu] at h1
  · rw [Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    induction hv using Submodule.span_induction with
    | mem v hv =>
      apply Submodule.subset_span
      refine ⟨Submodule.subset_span ⟨v, hv.1, rfl⟩, fun d hd => ?_⟩
      rw [RingHom.comp_apply, ← hj]
      exact Submodule.subset_span ⟨_, hv.2 d hd, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      show j ((a : Ω) • x) ∈ _
      rw [hj]
      exact Submodule.smul_mem _ ⟨i a, hR a a.2⟩ hx

end GlobalTheory.CompanionTheory.Ar
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DifferentScaledLatticeExtensionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
alias GlobalTheory.T.different_scaled_lattice_extension := GlobalTheory.CompanionTheory.Ar.scale_pull_ext
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DifferentIdealLocalGenerator
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DifferentIdealLocalGenerator
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

open scoped nonZeroDivisors

theorem differentIdeal_principal_in_localSubring :
    ∀ (F : Type) [Field F] [NumberField F] (Ω : Type) [Field Ω] [CharZero Ω] (R : Subring Ω)
      [IsLocalRing R] (σ : 𝓞 F →+* Ω), (∀ a, σ a ∈ R) →
      ∃ d₀ ∈ differentIdeal ℤ (𝓞 F), σ d₀ ≠ 0 ∧
        ∀ d ∈ differentIdeal ℤ (𝓞 F), σ d / σ d₀ ∈ R := by
  intro F _ _ Ω _ _ R _ σ hσ
  have hinj : Function.Injective σ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
    ext n
    simp [RingHom.mem_ker, Ideal.mem_comap]
  set I : Ideal (𝓞 F) := differentIdeal ℤ (𝓞 F) with hIdef
  have hI0 : I ≠ ⊥ := differentIdeal_ne_bot
  let J : FractionalIdeal (𝓞 F)⁰ F := (I : FractionalIdeal (𝓞 F)⁰ F)
  have hJ0 : J ≠ 0 := by
    simpa [J] using hI0
  have hJ : J * J⁻¹ = 1 := mul_inv_cancel₀ hJ0
  let σ' : 𝓞 F →+* R := σ.codRestrict R hσ
  let P : Ideal (𝓞 F) := (IsLocalRing.maximalIdeal R).comap σ'
  have hP1 : (1 : 𝓞 F) ∉ P := by
    intro h
    have : (1 : R) ∈ IsLocalRing.maximalIdeal R := by simpa [P] using h
    exact (Ideal.ne_top_iff_one _).1 (IsLocalRing.maximalIdeal.isMaximal R).ne_top this

  have hex : ∃ x ∈ I, ∃ y ∈ J⁻¹, ∃ u : 𝓞 F, algebraMap (𝓞 F) F u = algebraMap (𝓞 F) F x * y ∧
      u ∉ P := by
    by_contra hcon
    push_neg at hcon
    have hle : J * J⁻¹ ≤ (P : FractionalIdeal (𝓞 F)⁰ F) := by
      rw [FractionalIdeal.mul_le]
      intro a ha b hb
      obtain ⟨x, hx, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 ha
      have hab : algebraMap (𝓞 F) F x * b ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
        rw [← hJ]
        exact FractionalIdeal.mul_mem_mul ha hb
      obtain ⟨u, hu⟩ := (FractionalIdeal.mem_one_iff _).1 hab
      rw [← hu]
      exact (FractionalIdeal.mem_coeIdeal _).2 ⟨u, hcon x hx b hb u hu, rfl⟩
    have h1 : (1 : F) ∈ (P : FractionalIdeal (𝓞 F)⁰ F) :=
      hle (by rw [hJ]; exact FractionalIdeal.one_mem_one _)
    obtain ⟨w, hw, hw1⟩ := (FractionalIdeal.mem_coeIdeal _).1 h1
    have : w = 1 := by
      apply IsFractionRing.injective (𝓞 F) F
      simpa using hw1
    exact hP1 (this ▸ hw)
  obtain ⟨x, hx, y, hy, u, hu, huP⟩ := hex
  have hunit : IsUnit (σ' u) := by
    by_contra hnu
    exact huP ((IsLocalRing.mem_maximalIdeal _).2 hnu)
  have hσu : σ u ≠ 0 := by
    intro h0
    have : σ' u = 0 := Subtype.ext h0
    rw [this] at hunit
    exact not_isUnit_zero hunit
  have hx0 : x ≠ 0 := by
    rintro rfl
    have : u = 0 := by
      apply IsFractionRing.injective (𝓞 F) F
      simpa using hu
    exact hσu (by simp [this])
  refine ⟨x, hx, fun h => hx0 (hinj (by simpa using h)), fun d hd => ?_⟩
  have hdJ : algebraMap (𝓞 F) F d ∈ J := (FractionalIdeal.mem_coeIdeal _).2 ⟨d, hd, rfl⟩
  have hdy : algebraMap (𝓞 F) F d * y ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
    rw [← hJ]
    exact FractionalIdeal.mul_mem_mul hdJ hy
  obtain ⟨v, hv⟩ := (FractionalIdeal.mem_one_iff _).1 hdy
  have hrel : d * u = x * v := by
    apply IsFractionRing.injective (𝓞 F) F
    rw [map_mul, map_mul, hu, hv]
    ring
  have hrel' : σ d * σ u = σ x * σ v := by rw [← map_mul, ← map_mul, hrel]
  have hσx : σ x ≠ 0 := fun h => hx0 (hinj (by simpa using h))
  obtain ⟨w, hw⟩ := hunit.exists_right_inv
  have hw' : σ u * (w : Ω) = 1 := congrArg Subtype.val hw
  have key : σ d / σ x = σ v * (w : Ω) := by
    rw [div_eq_iff hσx]
    calc σ d = σ d * (σ u * (w : Ω)) := by rw [hw', _root_.mul_one]
      _ = (σ d * σ u) * (w : Ω) := by ring
      _ = σ v * (w : Ω) * σ x := by rw [hrel']; ring
  rw [key]
  exact R.mul_mem (hσ v) w.2

end GlobalTheory.CompanionTheory.Ar
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DifferentIdealLocalGeneratorStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
alias GlobalTheory.T.different_ideal_local_generator := GlobalTheory.CompanionTheory.Ar.differentIdeal_principal_in_localSubring
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DiscriminantEigenProjector
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.ScaledCasimir

section General

variable {J A : Type*} [Fintype J] [DecidableEq J] [CommRing A] (a : Module.Basis J ℤ A)

noncomputable def dualScaled (m : J) : A :=
  ∑ n, (Algebra.traceMatrix ℤ a).adjugate m n • a n

theorem trace_dualScaled_mul_basis (m p : J) :
    Algebra.trace ℤ A (dualScaled a m * a p) =
      if m = p then (Algebra.traceMatrix ℤ a).det else 0 := by
  have h := congrFun (congrFun (Matrix.adjugate_mul (Algebra.traceMatrix ℤ a)) m) p
  simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, _root_.mul_one,
    mul_zero] at h
  rw [← h]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dualScaled, Finset.sum_mul, map_sum, smul_mul_assoc, map_zsmul, smul_eq_mul,
    Algebra.traceMatrix_apply, Algebra.traceForm_apply]

theorem trace_dualScaled_mul (m : J) (y : A) :
    Algebra.trace ℤ A (dualScaled a m * y) = a.repr y m * (Algebra.traceMatrix ℤ a).det := by
  conv_lhs => rw [← a.sum_repr y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finset.mul_sum, map_sum, mul_smul_comm, map_zsmul, trace_dualScaled_mul_basis,
    smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem eq_of_trace_mul_basis (hd : (Algebra.traceMatrix ℤ a).det ≠ 0) {x y : A}
    (H : ∀ p, Algebra.trace ℤ A (x * a p) = Algebra.trace ℤ A (y * a p)) : x = y := by
  have hz : (fun q => a.repr (x - y) q) = 0 := by
    apply Matrix.eq_zero_of_vecMul_eq_zero hd
    funext p
    have h1 : Algebra.trace ℤ A ((x - y) * a p) = 0 := by
      rw [sub_mul, map_sub, H p, sub_self]
    conv at h1 => lhs; rw [← a.sum_repr (x - y)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Finset.sum_mul, map_sum, smul_mul_assoc, map_zsmul, smul_eq_mul] at h1
    simpa [Matrix.vecMul, dotProduct, Algebra.traceMatrix_apply, Algebra.traceForm_apply] using h1
  have : x - y = 0 := by
    apply a.repr.injective
    ext q
    simpa using congrFun hz q
  exact sub_eq_zero.mp this

theorem mul_dualScaled (hd : (Algebra.traceMatrix ℤ a).det ≠ 0) (b : A) (n : J) :
    b * dualScaled a n = ∑ m, a.repr (b * a m) n • dualScaled a m := by
  apply eq_of_trace_mul_basis a hd
  intro p
  have h1 : b * dualScaled a n * a p = dualScaled a n * (b * a p) := by ring
  rw [h1, trace_dualScaled_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finset.sum_mul, map_sum, smul_mul_assoc, map_zsmul, trace_dualScaled_mul,
    Module.Basis.repr_self, smul_eq_mul]
  simp [Finsupp.single_apply]

theorem sum_dualScaled_mul (hd : (Algebra.traceMatrix ℤ a).det ≠ 0) :
    ∑ m, dualScaled a m * a m = (((Algebra.traceMatrix ℤ a).det : ℤ) : A) := by
  apply eq_of_trace_mul_basis a hd
  intro k
  have h1 : ∀ m, dualScaled a m * a m * a k = dualScaled a m * (a k * a m) := fun m => by ring
  have h2 : (((Algebra.traceMatrix ℤ a).det : ℤ) : A) * a k =
      (Algebra.traceMatrix ℤ a).det • a k := by rw [zsmul_eq_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.sum_mul, map_sum, h2, map_zsmul, Algebra.trace_eq_matrix_trace a (a k)]
  simp only [h1, trace_dualScaled_mul, Matrix.trace, Matrix.diag_apply,
    Algebra.leftMulMatrix_eq_repr_mul, smul_eq_mul, Finset.mul_sum, ← Finset.sum_mul]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => _root_.mul_comm _ _

theorem equivariant (hd : (Algebra.traceMatrix ℤ a).det ≠ 0)
    {Ω V : Type*} [Field Ω] [AddCommGroup V] [Module Ω V]
    (ρ : A →+* Module.End Ω V) (σ : A →+* Ω) (b : A) (v : V) :
    ρ b (∑ m, σ (dualScaled a m) • ρ (a m) v) =
      σ b • ∑ m, σ (dualScaled a m) • ρ (a m) v := by
  have hmul : ∀ m, ρ b (ρ (a m) v) = ∑ n, ((a.repr (b * a m) n : ℤ) : Ω) • ρ (a n) v := by
    intro m
    have h0 : ρ b (ρ (a m) v) = ρ (b * a m) v := by simp [map_mul]
    rw [h0]
    conv_lhs => rw [← a.sum_repr (b * a m)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.sum_apply, map_zsmul, LinearMap.smul_apply, Int.cast_smul_eq_zsmul]
  have hc : ∀ n, σ b * σ (dualScaled a n) =
      ∑ m, σ (dualScaled a m) * ((a.repr (b * a m) n : ℤ) : Ω) := by
    intro n
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_mul, mul_dualScaled a hd, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_zsmul, zsmul_eq_mul, mul_comm]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, hmul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [hc n, Finset.sum_smul]

end General

theorem exists_scaledCasimir :
    ∀ (F : Type) [Field F] [NumberField F], ∃ (n : ℕ) (a c : Fin n → 𝓞 F), (∑ m, c m * a m = (((NumberField.discr F : ℤ) : 𝓞 F))) ∧ ∀ (Ω : Type) [Field Ω] (V : Type) [AddCommGroup V] [Module Ω V] (ρ : 𝓞 F →+* Module.End Ω V) (σ : 𝓞 F →+* Ω) (b : 𝓞 F) (v : V), ρ b (∑ m, σ (c m) • ρ (a m) v) = σ b • ∑ m, σ (c m) • ρ (a m) v := by
  intro F _ _
  let a := Module.finBasis ℤ (𝓞 F)
  have hdet : (Algebra.traceMatrix ℤ a).det = NumberField.discr F := by
    rw [← Algebra.discr_def, NumberField.discr_eq_discr]
  have hd : (Algebra.traceMatrix ℤ a).det ≠ 0 := by
    rw [hdet]; exact NumberField.discr_ne_zero F
  refine ⟨_, a, dualScaled a, ?_, ?_⟩
  · rw [sum_dualScaled_mul a hd, hdet]
  · intro Ω _ V _ _ ρ σ b v
    exact equivariant a hd ρ σ b v

end GlobalTheory.CompanionTheory.Ar.ScaledCasimir
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmTypeHostAutPermutation
section -- merged from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.CmTypeLabelTwistPermutation
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.UnitarySelfGeneration

theorem cm_type_label_twist_permutation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (g : HostAut H), ∃ π : CMType H ≃ CMType H, (∀ τ, (π τ).1 = τ.1.comp g.σ.toRingHom) ∧ ∀ s, labelEmb c (Sum.map π π s) = (labelEmb c s).comp g.s.toRingHom := by
  intro E _ _ _ H l c g
  let F : HostAut H → CMType H → CMType H := fun g τ =>
    ⟨τ.1.comp g.σ.toRingHom, by
      show τ.1 (g.σ (H.rt : E)) = _
      rw [g.fix]
      exact τ.2⟩
  refine ⟨⟨F g, F g.symm, fun τ => ?_, fun τ => ?_⟩, fun _ => rfl, ?_⟩
  · refine Subtype.ext (RingHom.ext fun x => ?_)
    show τ.1 (g.σ (g.σ.symm x)) = τ.1 x
    rw [RingEquiv.apply_symm_apply]
  · refine Subtype.ext (RingHom.ext fun x => ?_)
    show τ.1 (g.σ.symm (g.σ x)) = τ.1 x
    rw [RingEquiv.symm_apply_apply]
  · rintro (τ | τ)
    · exact RingHom.ext fun x => Subtype.ext rfl
    · refine RingHom.ext fun x => Subtype.ext ?_
      show τ.1 ((g.s (H.bar x) : 𝓞 E) : E) = τ.1 ((H.bar (g.s x) : 𝓞 E) : E)
      rw [g.s_bar]

end PositivityTheory.UnitarySelfGeneration
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmTypeHostAutPermutation
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.Label

theorem automorphism_permutes_labels : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (g : HostAut H), ∃ π : CMType H ≃ CMType H, (∀ τ, (π τ).1 = τ.1.comp g.σ.toRingHom) ∧ ∀ s, labelEmb c (Sum.map π π s) = (labelEmb c s).comp g.s.toRingHom :=
  @PositivityTheory.UnitarySelfGeneration.cm_type_label_twist_permutation

end GlobalTheory.CompanionTheory.Ar.Label
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmTypeHostAutPermutationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
alias GlobalTheory.T.cm_type_host_aut_permutation := GlobalTheory.CompanionTheory.Ar.Label.automorphism_permutes_labels
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateDualEqOfOmegaEq
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DifferentIdealAutomorphismInvariant
section -- merged from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.MapMemDifferentIdealIff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.UnitarySelfGeneration

theorem map_mem_differentIdeal (E : Type) [Field E] [NumberField E] (s : 𝓞 E ≃+* 𝓞 E) (d : 𝓞 E)
    (hd : d ∈ differentIdeal ℤ (𝓞 E)) : s d ∈ differentIdeal ℤ (𝓞 E) := by
  have key : IsLocalization.coeSubmodule E (differentIdeal ℤ (𝓞 E)) =
      1 / Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E) := coeSubmodule_differentIdeal ℤ ℚ (𝓞 E)
  let τ : E ≃+* E := IsFractionRing.ringEquivOfRingEquiv (K := E) (L := E) s
  have hτ : ∀ b : 𝓞 E, τ (algebraMap (𝓞 E) E b) = algebraMap (𝓞 E) E (s b) :=
    fun b => IsFractionRing.ringEquivOfRingEquiv_algebraMap s b
  let τq : E ≃ₐ[ℚ] E := AlgEquiv.ofRingEquiv (f := τ) fun x => τ.toRingHom.map_rat_algebraMap x
  have htr : ∀ x : E, Algebra.trace ℚ E (τ x) = Algebra.trace ℚ E x :=
    fun x => Algebra.trace_eq_of_algEquiv τq x
  have h1 : ∀ a : E, a ∈ (1 : Submodule (𝓞 E) E) → τ a ∈ (1 : Submodule (𝓞 E) E) := by
    intro a ha
    obtain ⟨b, rfl⟩ := Submodule.mem_one.1 ha
    exact Submodule.mem_one.2 ⟨s b, (hτ b).symm⟩
  have hdual : ∀ y ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E),
      τ.symm y ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E) := by
    intro y hy
    rw [Submodule.mem_traceDual] at hy ⊢
    intro a ha
    have h2 := hy (τ a) (h1 a ha)
    rw [Algebra.traceForm_apply] at h2 ⊢
    rw [← htr, map_mul, RingEquiv.apply_symm_apply]
    exact h2
  have hd' : algebraMap (𝓞 E) E d ∈
      (1 / Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E) : Submodule (𝓞 E) E) := by
    rw [← key]
    exact (IsLocalization.mem_coeSubmodule _ _).2 ⟨d, hd, rfl⟩
  have hs : algebraMap (𝓞 E) E (s d) ∈ IsLocalization.coeSubmodule E (differentIdeal ℤ (𝓞 E)) := by
    rw [key, Submodule.mem_div_iff_forall_mul_mem]
    intro y hy
    have h2 := (Submodule.mem_div_iff_forall_mul_mem.1 hd') (τ.symm y) (hdual y hy)
    have h3 := h1 _ h2
    rwa [map_mul, hτ, RingEquiv.apply_symm_apply] at h3
  obtain ⟨y, hy, hyd⟩ := (IsLocalization.mem_coeSubmodule _ _).1 hs
  rwa [IsFractionRing.injective (𝓞 E) E hyd] at hy

theorem map_mem_differentIdeal_iff : ∀ (E : Type) [Field E] [NumberField E] (s : 𝓞 E ≃+* 𝓞 E) (d : 𝓞 E), s d ∈ differentIdeal ℤ (𝓞 E) ↔ d ∈ differentIdeal ℤ (𝓞 E) := by
  intro E _ _ s d
  constructor
  · intro h
    have := map_mem_differentIdeal E s.symm (s d) h
    rwa [RingEquiv.symm_apply_apply] at this
  · exact map_mem_differentIdeal E s d

end PositivityTheory.UnitarySelfGeneration
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DifferentIdealAutomorphismInvariant
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem mem_differentIdeal_ringEquiv_iff :
    ∀ (E : Type) [Field E] [NumberField E] (s : 𝓞 E ≃+* 𝓞 E) (d : 𝓞 E),
      s d ∈ differentIdeal ℤ (𝓞 E) ↔ d ∈ differentIdeal ℤ (𝓞 E) :=
  @PositivityTheory.UnitarySelfGeneration.map_mem_differentIdeal_iff

end GlobalTheory.CompanionTheory.Ar
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DifferentIdealAutomorphismInvariantStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
alias GlobalTheory.T.different_ideal_automorphism_invariant := GlobalTheory.CompanionTheory.Ar.mem_differentIdeal_ringEquiv_iff
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateDualEqOfOmegaEq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem htDual_htW_relabel : ∀ (E : Type) [Field E] [NumberField E] (s : 𝓞 E ≃+* 𝓞 E) (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G G' : Over X) [GrpObj G] [GrpObj G'] (L : LB G.left) (L' : LB G'.left) (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel G ξ V) (M' : LieModel G' ξ V) (n n' : ℕ) (ρ : 𝓞 E →+* Module.End Ω V) (τ : 𝓞 E →+* Ω) (q : Cpt ξ), M'.htOm L' n' q = M.htOm L n q → M'.htDual L' n' (ρ.comp s.toRingHom) (τ.comp s.toRingHom) q = M.htDual L n ρ τ q ∧ M'.htW L' n' (ρ.comp s.toRingHom) (τ.comp s.toRingHom) (differentIdeal ℤ (𝓞 E)) q = M.htW L n ρ τ (differentIdeal ℤ (𝓞 E)) q := by
  intro E _ _ s X Ω _ ξ G G' _ _ L L' V _ _ M M' n n' ρ τ q h
  have hE : eigSp (ρ.comp s.toRingHom) (τ.comp s.toRingHom) = eigSp ρ τ :=
    eigSp_comp_ringEquiv Ω V (𝓞 E) ρ s τ
  have h1 : M'.htDual L' n' (ρ.comp s.toRingHom) (τ.comp s.toRingHom) q = M.htDual L n ρ τ q := by
    unfold LieModel.htDual
    rw [hE, h]
  refine ⟨h1, ?_⟩
  unfold LieModel.htW
  rw [hE, h1]
  congr 1
  ext e
  constructor
  · rintro ⟨he, H⟩
    refine ⟨he, fun d hd => ?_⟩
    have hd' : s.symm d ∈ differentIdeal ℤ (𝓞 E) :=
      (GlobalTheory.T.different_ideal_automorphism_invariant E s (s.symm d)).1 (by simpa using hd)
    simpa using H _ hd'
  · rintro ⟨he, H⟩
    exact ⟨he, fun d hd => H _ ((GlobalTheory.T.different_ideal_automorphism_invariant E s d).2 hd)⟩

end GlobalTheory.CompanionTheory.Ar
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateDualEqOfOmegaEqStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
alias GlobalTheory.T.hodge_tate_dual_eq_of_omega_eq := GlobalTheory.CompanionTheory.Ar.htDual_htW_relabel
end
end
