module

public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDualOfIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingEqOneTrivialOnAxis
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaChr
public import Formalism.LocalToGlobal.CarriedPlMap
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DivRows3GIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadNatZero
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.DiagonalLagrangianIntegralSiegelParabolicTransfo

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniversalSectionBasesShrunkAffineChart
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniversalSectionBasesShrunkAffineChart
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.Poinc.exists_univBasis_affineChart : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (U₀ : M.Z.Opens) (w : M.Z), IsAffineOpen U₀ → w ∈ U₀ → ∀ (P : PolAV (Sp (M.ringOn U₀))) (N : ℕ), 1 ≤ N → ∃ (U : M.Z.Opens) (h : M.ringOn U₀ ≤ M.ringOn U) (P' : PolAV (Sp (M.ringOn U))) (φ : P'.A.left ⟶ P.A.left), U ≤ U₀ ∧ IsAffineOpen U ∧ w ∈ U ∧ IsGrpPullback P'.A P.A (spMap (Subalgebra.inclusion h).toRingHom) φ ∧ LBIso P'.L (P.L.pull φ) ∧ P'.g = P.g ∧ (∃ th : LB.Sec (LPow P'.A P'.L 1 (baseOver (Sp (M.ringOn U)))), GlobalTheory.ThetaReal.UnivBasis P' 1 (fun _ : Fin 1 => SecM.ofSec P'.A th)) ∧ ∃ b : Fin (N ^ P'.g) → SecM P'.A P'.L (N : ℕ) (baseOver (Sp (M.ringOn U))), GlobalTheory.ThetaReal.UnivBasis P' (N : ℕ) b := by
  intro o Ω _ _ _ M U₀ w _ hw P N hN
  obtain ⟨hL, hL₂⟩ := GlobalTheory.abelianSchemeLaws_all
  have hle : M.ringOn U₀ ≤ M.O w := RatModel.ringOn_le_O hw
  let p : PrimeSpectrum (M.ringOn U₀) :=
    ⟨(IsLocalRing.maximalIdeal (M.O w)).comap (Subalgebra.inclusion hle).toRingHom, inferInstance⟩
  obtain ⟨V₁, m₁, b₁, hb₁⟩ := GlobalTheory.ThetaReal.exists_univBasis hL₂.secBaseChangeAny P 1 le_rfl p
  obtain ⟨V₂, m₂, b₂, hb₂⟩ := GlobalTheory.ThetaReal.exists_univBasis hL₂.secBaseChangeAny P N hN p
  obtain ⟨_, ⟨f, rfl⟩, hpf, hfV⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (u := ((V₁ ⊓ V₂ : (Sp (M.ringOn U₀)).Opens) : Set (Sp (M.ringOn U₀)))) (a := p) ⟨m₁, m₂⟩ (V₁ ⊓ V₂).isOpen
  have hfu : IsUnit (Subalgebra.inclusion hle f) := by
    by_contra hn
    exact hpf ((IsLocalRing.mem_maximalIdeal _).2 hn)
  obtain ⟨h0, hinv⟩ := (RatModel.isUnit_O_iff _).1 hfu
  obtain ⟨U, g, hU, hwU, hUU₀, hg⟩ := RatModel.exists_affine_of_mem_O hinv hw
  have h : M.ringOn U₀ ≤ M.ringOn U := RatModel.ringOn_anti (fun x hx => hUU₀ hx)
  have finv : ((f : Ω))⁻¹ ∈ M.ringOn U := (RatModel.mem_ringOn_iff_exists ⟨w, hwU⟩).2 ⟨g, hg⟩
  have hrange : ∀ V : (Sp (M.ringOn U₀)).Opens, V₁ ⊓ V₂ ≤ V →
      Set.range (spMap (Subalgebra.inclusion h).toRingHom) ⊆ V := by
    rintro V hV _ ⟨q, rfl⟩
    apply hV
    apply hfV
    show f ∉ (PrimeSpectrum.comap (Subalgebra.inclusion h).toRingHom q).asIdeal
    intro hq
    have hu : IsUnit (Subalgebra.inclusion h f) :=
      IsUnit.of_mul_eq_one ⟨_, finv⟩ (Subtype.ext (mul_inv_cancel₀ h0))
    exact q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hq hu)
  have fac : ∀ V : (Sp (M.ringOn U₀)).Opens, V₁ ⊓ V₂ ≤ V → ∃ τ : Sp (M.ringOn U) ⟶ (overRes (T := baseOver (Sp (M.ringOn U₀))) V).left,
      τ ≫ (overRes (T := baseOver (Sp (M.ringOn U₀))) V).hom = spMap (Subalgebra.inclusion h).toRingHom := fun V hV =>
    ⟨IsOpenImmersion.lift V.ι (spMap (Subalgebra.inclusion h).toRingHom) (by rw [Scheme.Opens.range_ι]; exact hrange V hV),
      by
        change _ ≫ V.ι ≫ 𝟙 _ = _
        rw [Category.comp_id, IsOpenImmersion.lift_fac]⟩
  obtain ⟨τ₁, hτ₁⟩ := fac V₁ inf_le_left
  obtain ⟨τ₂, hτ₂⟩ := fac V₂ inf_le_right
  obtain ⟨P', φ, hg, hφ, hiso⟩ := GlobalTheory.exists_isPolFibre hL.polBaseChange (Subalgebra.inclusion h).toRingHom P
  refine ⟨U, h, P', φ, hUU₀, hU, hwU, hφ, hiso.symm, hg, ?_, ?_⟩
  · obtain ⟨c₁, hc₁⟩ := GlobalTheory.T.universalBasis_move_baseChange _ _ _ P P' φ hφ hiso.symm _ _ _ τ₁ hτ₁ b₁ hb₁
    haveI : Unique (Fin (1 ^ P.g)) := by rw [one_pow]; infer_instance
    have key : GlobalTheory.ThetaReal.UnivBasis P' ((1 : ℕ) : ℤ) (fun _ : Fin 1 => c₁ default) := by
      intro T hT u
      have h2 := @hc₁ T hT u
      obtain ⟨c, hc⟩ := h2
      exact ⟨c.reindex (finCongr (one_pow _)), fun i => (Module.Basis.reindex_apply c _ i).trans
        ((hc _).trans (congrArg _ (congrArg c₁ (Subsingleton.elim _ _))))⟩
    exact ⟨SecM.toSec P'.A (c₁ default), key⟩
  · obtain ⟨c₂, hc₂⟩ := GlobalTheory.T.universalBasis_move_baseChange _ _ _ P P' φ hφ hiso.symm _ _ _ τ₂ hτ₂ b₂ hb₂
    let e : Fin (N ^ P.g) ≃ Fin (N ^ P'.g) := finCongr (by rw [hg])
    refine ⟨fun i => c₂ (e.symm i), fun T hT u => ?_⟩
    have h2 := @hc₂ T hT u
    obtain ⟨c, hc⟩ := h2
    exact ⟨c.reindex e, fun i => (Module.Basis.reindex_apply c _ i).trans (hc _)⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniversalSectionBasesShrunkAffineChartStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_universal_section_bases_shrunk_affineChart : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (U₀ : M.Z.Opens) (w : M.Z), IsAffineOpen U₀ → w ∈ U₀ → ∀ (P : PolAV (Sp (M.ringOn U₀))) (N : ℕ), 1 ≤ N → ∃ (U : M.Z.Opens) (h : M.ringOn U₀ ≤ M.ringOn U) (P' : PolAV (Sp (M.ringOn U))) (φ : P'.A.left ⟶ P.A.left), U ≤ U₀ ∧ IsAffineOpen U ∧ w ∈ U ∧ IsGrpPullback P'.A P.A (spMap (Subalgebra.inclusion h).toRingHom) φ ∧ LBIso P'.L (P.L.pull φ) ∧ P'.g = P.g ∧ (∃ th : LB.Sec (LPow P'.A P'.L 1 (baseOver (Sp (M.ringOn U)))), GlobalTheory.ThetaReal.UnivBasis P' 1 (fun _ : Fin 1 => SecM.ofSec P'.A th)) ∧ ∃ b : Fin (N ^ P'.g) → SecM P'.A P'.L (N : ℕ) (baseOver (Sp (M.ringOn U))), GlobalTheory.ThetaReal.UnivBasis P' (N : ℕ) b := by
  first | exact @GlobalTheory.Poinc.exists_univBasis_affineChart | exact GlobalTheory.Poinc.exists_univBasis_affineChart | (intros; apply GlobalTheory.Poinc.exists_univBasis_affineChart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulEqZeroOfMemMap
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

open TensorProduct

namespace GlobalTheory.LiftSys

theorem algHom_mem_map {R B B' : Type} [CommRing R] [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B']
    (I : Ideal R) (α : B →ₐ[R] B') {b : B} (hb : b ∈ I.map (algebraMap R B)) :
    α b ∈ I.map (algebraMap R B') := by
  have h := Ideal.mem_map_of_mem (α : B →+* B') hb
  rwa [Ideal.map_map, AlgHom.comp_algebraMap] at h

theorem mul_eq_zero_of_mem_map {R B' : Type} [CommRing R] [CommRing B'] [Algebra R B'] {I : Ideal R}
    (hI : I ^ 2 = 0) {x y : B'} (hx : x ∈ I.map (algebraMap R B')) (hy : y ∈ I.map (algebraMap R B')) :
    x * y = 0 := by
  have h := Ideal.mul_mem_mul hx hy
  rw [← pow_two, map_sq hI B'] at h
  simpa using h

theorem exists_unique_formExt : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Par s₀ → ∀ (U : AffOp X₀) (B B' : Type) [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B'] (p : B →+* Sec s₀ U.unop.1), SemiHom π p → Function.Surjective p → (∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) → ∀ (α : B →ₐ[R] B') (E : GlobForm s₀ →+ B'), (∀ (r : R) w, E (π r • w) = r • E w) → (∀ w, E w ∈ I.map (algebraMap R B')) → ∃! θ : Ω[Sec s₀ U.unop.1⁄R₀] →+ B', (∀ b w, θ (p b • w) = α b * θ w) ∧ (∀ w, θ w ∈ I.map (algebraMap R B')) ∧ ∀ w : GlobForm s₀, θ (w.1 U) = E w := by
  intro R R₀ _ _ I hI π hπ hk X₀ s₀ hpar U B B' _ _ _ _ p hsemi hsurj hker α E hE hEmem
  have hb : IsBaseChange (Sec s₀ U.unop.1) (evForm s₀ U) := hpar U
  let l : Sec s₀ U.unop.1 → B := Function.surjInv hsurj
  have hl : ∀ s, p (l s) = s := Function.surjInv_eq hsurj
  have key : ∀ b b' : B, p b = p b' → ∀ x ∈ I.map (algebraMap R B'), α b * x = α b' * x := by
    intro b b' h x hx
    have h1 : b - b' ∈ I.map (algebraMap R B) := (hker _).1 (by rw [map_sub, h, sub_self])
    have h2 := mul_eq_zero_of_mem_map hI (algHom_mem_map I α h1) hx
    rw [map_sub, sub_mul] at h2
    exact sub_eq_zero.1 h2
  let g : Sec s₀ U.unop.1 → GlobForm s₀ →+ B' := fun s =>
    AddMonoidHom.mk' (fun w => α (l s) * E w) (fun w w' => by simp [mul_add])
  let f : Sec s₀ U.unop.1 →+ GlobForm s₀ →+ B' :=
    AddMonoidHom.mk' g (fun s t => by
      ext w
      show α (l (s + t)) * E w = α (l s) * E w + α (l t) * E w
      rw [key (l (s + t)) (l s + l t) (by rw [map_add (f := _), hl, hl, hl]) _ (hEmem w), map_add (f := _), add_mul])
  have hf : ∀ (r : R₀) (s : Sec s₀ U.unop.1) (w : GlobForm s₀), f (r • s) w = f s (r • w) := by
    intro r s w
    obtain ⟨r', rfl⟩ := hπ r
    show α (l (π r' • s)) * E w = α (l s) * E (π r' • w)
    rw [key (l (π r' • s)) (r' • l s) (by rw [hl, hsemi, hl]) _ (hEmem w), hE, map_smul,
      smul_mul_assoc, mul_smul_comm]
  let T := TensorProduct.liftAddHom f hf
  let θ : Ω[Sec s₀ U.unop.1⁄R₀] →+ B' := T.comp (hb.equiv.symm.toLinearMap.toAddMonoidHom)
  have hθ : ∀ x, θ x = T (hb.equiv.symm x) := fun _ => rfl
  have hsm : ∀ (b : B) (t : Sec s₀ U.unop.1 ⊗[R₀] GlobForm s₀), T (p b • t) = α b * T t := by
    intro b t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul s w =>
      rw [TensorProduct.smul_tmul', TensorProduct.liftAddHom_tmul, TensorProduct.liftAddHom_tmul]
      show α (l (p b • s)) * E w = α b * (α (l s) * E w)
      rw [key (l (p b • s)) (b * l s) (by rw [hl, map_mul, hl, smul_eq_mul]) _ (hEmem w), map_mul, mul_assoc]
    | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), hx, hy, mul_add]
  have hmem : ∀ t : Sec s₀ U.unop.1 ⊗[R₀] GlobForm s₀, T t ∈ I.map (algebraMap R B') := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul s w => exact Ideal.mul_mem_left _ _ (hEmem w)
    | add x y hx hy => rw [map_add (f := _)]; exact Ideal.add_mem _ hx hy
  have hev : ∀ w : GlobForm s₀, θ (w.1 U) = E w := by
    intro w
    have h1 : hb.equiv.symm (w.1 U) = 1 ⊗ₜ w := by
      rw [LinearEquiv.symm_apply_eq, IsBaseChange.equiv_tmul, one_smul]; rfl
    rw [hθ, h1, TensorProduct.liftAddHom_tmul]
    show α (l 1) * E w = E w
    rw [key (l 1) 1 (by rw [hl, map_one]) _ (hEmem w), map_one, one_mul]
  refine ⟨θ, ⟨fun b w => ?_, fun w => hmem _, hev⟩, fun y ⟨hy1, _, hy3⟩ => ?_⟩
  · rw [hθ, hθ, LinearEquiv.map_smul, hsm]
  · ext x
    refine hb.inductionOn x ?_ ?_ ?_
    · intro w
      exact (hy3 w).trans (hev w).symm
    · intro s n hn
      rw [← hl s, hy1, hn, hθ, hθ, LinearEquiv.map_smul, hsm]
    · intro n₁ n₂ h₁ h₂
      rw [map_add (f := _), map_add (f := _), h₁, h₂]

end GlobalTheory.LiftSys
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncComponentsLocalSnc
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R.FinalTheorems
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O

open ReciprocityTheory.AnForm.R

namespace GlobalTheory.SncLocal

theorem mem_comps_of_compList {X : Scheme.{0}} {B : Set X} {m : ℕ} {C : Fin m → Closeds X}
    (hC : FinalTheorems.CompList B C) (i : Fin m) : (C i : Set X) ∈ ReciprocityTheory.AnForm.R.comps B := by
  classical
  refine ⟨⟨hC.1 i, hC.2.1 ▸ Set.subset_iUnion (fun j => (C j : Set X)) i⟩, fun D hD hiD => ?_⟩
  obtain ⟨z, hz, hDz⟩ := (isIrreducible_iff_sUnion_isClosed.1 hD.1)
    (Finset.univ.image fun j => (C j : Set X))
    (fun z hz => by
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hz
      exact (C j).isClosed)
    (by
      refine hD.2.trans (hC.2.1 ▸ Set.iUnion_subset fun j => ?_)
      exact Set.subset_sUnion_of_mem (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_univ j))))
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hz
  have hij : i = j := hC.2.2 i j (hiD.trans hDz)
  subst hij
  exact hDz

theorem lSncAt_of_snc (X : Scheme.{0}) [IsNoetherian X] (B : Closeds X) (m : ℕ) (C : Fin m → Closeds X)
    (hB : Snc (Scheme.IdealSheafData.vanishingIdeal B)) (hC : CompList (B : Set X) C) (x : X) :
    LSncAt X C x := by
  obtain ⟨hreg, U, hx, n, f, J, hrsp, hZU⟩ := hB x
  haveI := hreg
  have hs : ((Scheme.IdealSheafData.vanishingIdeal B).support : Set X) = B := by simp
  obtain ⟨O, hxO, -, hO⟩ := exists_open_comps x U hx f J hrsp hZU
  have key : ∀ i : {i : Fin m // x ∈ C i}, ∃ j ∈ J,
      ReciprocityTheory.AnForm.R.IsBranch ((Scheme.IdealSheafData.vanishingIdeal B).support : Set X) (f j) x (C i.1) ∧
      stalkId (Scheme.IdealSheafData.vanishingIdeal (C i.1)) x =
        Ideal.span {X.presheaf.germ U.1 x hx (f j)} := by
    rintro ⟨i, hxi⟩
    have hCi : ((C i : Closeds X) : Set X) ∈
        ReciprocityTheory.AnForm.R.comps ((Scheme.IdealSheafData.vanishingIdeal B).support : Set X) :=
      hs ▸ mem_comps_of_compList hC i
    have hO' := hO _ hCi
    have hq : ∀ q : PrimeSpectrum (X.presheaf.stalk x), X.fromSpecStalk x q ∈ (C i : Set X) ↔
        ∃ j ∈ J, ReciprocityTheory.AnForm.R.IsBranch ((Scheme.IdealSheafData.vanishingIdeal B).support : Set X)
          (f j) x (C i) ∧ X.presheaf.germ U.1 x hx (f j) ∈ q.asIdeal := by
      intro q
      have hqO : X.fromSpecStalk x q ∈ (O : Set X) := by
        have h : X.fromSpecStalk x q ∈ Set.range (X.fromSpecStalk x) := ⟨q, rfl⟩
        rw [Scheme.range_fromSpecStalk] at h
        exact Specializes.mem_open h O.isOpen hxO
      have h := Set.ext_iff.1 hO' (X.fromSpecStalk x q)
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, hqO, and_true, true_and,
        GlobalTheory.SncComponents.fromSpecStalk_mem_zeroLocus_iff U x hx] at h
      exact h
    obtain ⟨j, hj, hbj, -⟩ := (hq (IsLocalRing.closedPoint _)).1
      (by rw [Scheme.fromSpecStalk_closedPoint]; exact hxi)
    refine ⟨j, hj, hbj, ?_⟩
    have hCC : (C i).compl.compl = C i := SetLike.coe_injective (compl_compl _)
    have hp : Prime (X.presheaf.germ U.1 x hx (f j)) :=
      prime_of_regular_params (fun i => X.presheaf.germ U.1 x hx (f i)) hrsp.1 hrsp.2 j
    have h := GlobalTheory.AffineComplement.stalkId_vanishingIdeal_compl (C i).compl x
      (X.presheaf.germ U.1 x hx (f j)) fun q => by
        refine not_congr ((hq q).trans ⟨?_, fun h => ⟨j, hj, hbj, h⟩⟩)
        rintro ⟨k, hk, hbk, h⟩
        by_cases hjk : j = k
        · exact hjk ▸ h
        · exact absurd rfl (branch_ne x U hx f J hrsp hZU hj hk hjk hbj hbk)
    rw [hCC] at h
    rw [h]
    exact ((Ideal.span_singleton_prime hp.ne_zero).2 hp).radical
  choose g hgJ hgb hgs using key
  refine ⟨hreg, n, fun k => X.presheaf.germ U.1 x hx (f k), ⟨g, fun a b hab => ?_⟩, hrsp, hgs⟩
  have h1 := hgb a
  rw [hab] at h1
  obtain ⟨D, -, hD⟩ := existsUnique_branch x U hx f J hrsp hZU (g b) (hgJ b)
  have e : (C a.1 : Set X) = C b.1 := (hD _ h1).trans (hD _ (hgb b)).symm
  exact Subtype.ext (hC.2.2 _ _ e.le)

theorem lSncAt_of_snc' : ∀ (X : Scheme.{0}) [IsNoetherian X] (B : Closeds X) (m : ℕ) (C : Fin m → Closeds X), Snc (Scheme.IdealSheafData.vanishingIdeal B) → CompList (B : Set X) C → ∀ x : X, LSncAt X C x :=
  fun X _ B m C hB hC x => lSncAt_of_snc X B m C hB hC x

end GlobalTheory.SncLocal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareDecompositionExtendsFromGenericFibreSemiAb
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareDecompositionExtendsFromGenericFibreSemiAb
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.GenericDec


open ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison in
theorem gen_pull_div_of_gen_div {X Y : Scheme.{0}} (M N : LB X) (a : Y ⟶ X)
    (h : ∃ t : LB.Gen (LB.div (M.pull a) (N.pull a)), t.IsGen) :
    ∃ t : LB.Gen ((LB.div M N).pull a), t.IsGen := by
  refine exists_gen_transfer (L := LB.div (M.pull a) (N.pull a)) (L' := (LB.div M N).pull a)
    (fun p => ((fun _ => (p PUnit.unit).1), (fun _ => (p PUnit.unit).2))) (fun j y hy => ?_)
    (fun i j y hy => ?_) h
  · exact ⟨Set.mem_iInter.2 fun _ => (Set.mem_iInter.1 hy PUnit.unit).1,
      Set.mem_iInter.2 fun _ => (Set.mem_iInter.1 hy PUnit.unit).2⟩
  · have hM : a.base y ∈ M.U (i PUnit.unit).1 ⊓ M.U (j PUnit.unit).1 :=
      ⟨(Set.mem_iInter.1 hy.1 PUnit.unit).1, (Set.mem_iInter.1 hy.2 PUnit.unit).1⟩
    have hN : a.base y ∈ N.U (i PUnit.unit).2 ⊓ N.U (j PUnit.unit).2 :=
      ⟨(Set.mem_iInter.1 hy.1 PUnit.unit).2, (Set.mem_iInter.1 hy.2 PUnit.unit).2⟩
    refine (germ_pull (LB.div M N) a i j y hy ⟨⟨hM.1, hN.1⟩, ⟨hM.2, hN.2⟩⟩).trans ?_
    refine (gU_pullU a _ y _ _).trans ?_
    refine (congrArg _ (germ_div M N _ _ (a.base y) _)).trans ?_
    rw [map_mul, map_inv]
    refine Eq.trans ?_ (germ_div _ _ _ _ y _).symm
    exact congrArg₂ (· * ·) ((germ_pull M a (fun _ => (i PUnit.unit).1) (fun _ => (j PUnit.unit).1) y _ hM).trans (gU_pullU a _ y _ _)).symm
      (congrArg (·⁻¹) ((germ_pull N a (fun _ => (i PUnit.unit).2) (fun _ => (j PUnit.unit).2) y _ hN).trans (gU_pullU a _ y _ _)).symm)

theorem lbIso_of_generic {R' : Type} [CommRing R'] [IsDomain R'] [IsNoetherianRing R'] [IsIntegrallyClosed R']
    [IsLocalRing R'] (G : Over (Sp R')) [GrpObj G] (hG : IsSemiAbelian G) {P Q : LB G.left} (hP : P.IsLB)
    (hQ : Q.IsLB) (h : LBIso (P.pull (pullback.fst G.hom (jK R'))) (Q.pull (pullback.fst G.hom (jK R')))) :
    LBIso P Q :=
  PicGenericInj.exists_gen_of_generic R' G hG (LB.div Q P) (LB.isLB_div hQ hP)
    (gen_pull_div_of_gen_div Q P _ h)

theorem sqDec_of_generic : ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsNoetherianRing R'] [IsIntegrallyClosed R']
    [IsLocalRing R'] (G : Over (Sp R')) [GrpObj G], IsSemiAbelian G → ∀ (L M : LB G.left), L.IsLB → M.IsLB →
    SqDec ((Over.pullback (jK R')).obj G) (L.pull (pullback.fst G.hom (jK R')))
      (M.pull (pullback.fst G.hom (jK R'))) → SqDec G L M := by
  intro R' _ _ _ _ _ G _ hG L M hL hM hD
  obtain ⟨N, a₀, r, a, β, hN, ha₀, hβ, H⟩ := hD
  have ext : ∀ i, ∃ B : G ⟶ G, IsMonHom B ∧ (Over.pullback (jK R')).map B = β i := fun i =>
    (semiAbelian_hom_extend_generic R' G G hG hG (β i) (hβ i)).exists
  choose B hBm hBe using ext
  refine ⟨N, a₀, r, a, B, hN, ha₀, hBm, ?_⟩
  set f := pullback.fst G.hom (jK R') with hf
  have hc : ∀ o : Option (Fin r), (o.elim (𝟙 _) fun i => (β i).left) ≫ f =
      f ≫ (o.elim (𝟙 G.left) fun i => (B i).left) := by
    intro o
    cases o with
    | none => simp
    | some i =>
      simp only [Option.elim_some]
      rw [← hBe i]
      simp only [hf, Over.pullback_map_left, pullback.lift_fst]
  have i1 := (lbIso_lbPow_pull hL f N).symm
  have i5 := GlobalTheory.SymExtend.lbIso_linComb_pull hM f (fun o : Option (Fin r) => o.elim (𝟙 _) fun i => (β i).left)
    (fun o : Option (Fin r) => o.elim (𝟙 G.left) fun i => (B i).left) (fun o => o.elim (a₀ : ℤ) fun i => (a i : ℤ)) f hc
  have j1 := i1.trans (pull_isLB (isLB_lbPow hL N) f) (isLB_lbPow (pull_isLB hL f) N)
    (LB.isLB_linComb (pull_isLB hM f) _ _) H
  have j2 := j1.trans (pull_isLB (isLB_lbPow hL N) f) (LB.isLB_linComb (pull_isLB hM f) _ _)
    (pull_isLB (LB.isLB_linComb hM _ _) f) i5
  exact lbIso_of_generic G hG (isLB_lbPow hL N) (LB.isLB_linComb hM _ _) j2

end GlobalTheory.GenericDec
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareDecompositionExtendsFromGenericFibreSemiAbStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.squareDecomposition_extends_from_genericFibre_semiAbelian : ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsNoetherianRing R'] [IsIntegrallyClosed R'] [IsLocalRing R'] (G : Over (Sp R')) [GrpObj G], IsSemiAbelian G → ∀ (L M : LB G.left), L.IsLB → M.IsLB → SqDec ((Over.pullback (jK R')).obj G) (L.pull (pullback.fst G.hom (jK R'))) (M.pull (pullback.fst G.hom (jK R'))) → SqDec G L M := by
  first | exact @GlobalTheory.GenericDec.sqDec_of_generic | exact GlobalTheory.GenericDec.sqDec_of_generic | (intros; apply GlobalTheory.GenericDec.sqDec_of_generic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLevelConjugateCharacter
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.R3.LinkLev

theorem spack_X_eq_of_heq {D : D7} {F F' : ∀ u, Formalism.L2.Forms.Forms0 D u} (hF : F = F') (P : GlobalTheory.Mem.SRe.SPack D F)
    (P' : GlobalTheory.Mem.SRe.SPack D F') (h : HEq P P') : P.X = P'.X := by
  subst hF
  rw [eq_of_heq h]

theorem conjLevel_of_setting_eq {D : D7} (X X' : Formalism.L2.SG.HidaSetting.HidaSetting D) (hX : X = X')
    (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (h' : X'.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (ι : Formalism.L2.Theta.GA D (D.sp.Y 0) ≃* X.B.I.GA) (hι : ι = (Formalism.L2.SG.RowsJoinPinned.iotaX X h).toMulEquiv)
    (t t' : Formalism.L2.Theta.GA D (Yc D 0)) (ht : t = t') (J : Set (Formalism.L2.Theta.GA D (Yc D 0)))
    (χ : Formalism.L2.Theta.GA D (Yc D 0) → ℂ)
    (hc : Formalism.IndefR.AutomorphicEvaluation.ConjLevel t'⁻¹ J χ (Formalism.L2.SG.RowsJoinPinned.iotaX X' h' ⁻¹' GlobalTheory.Mem.SRe.concreteLevelAdelicSubset X')
      (fun k => GlobalTheory.Mem.SRe.adelicCharacterOfHidaSetting X' (Formalism.L2.SG.RowsJoinPinned.iotaX X' h' k))) :
    Formalism.IndefR.AutomorphicEvaluation.ConjLevel t⁻¹ J χ (ι ⁻¹' seeKS X) (fun k => seeChiS X (ι k)) := by
  subst hX
  subst hι
  subst ht
  exact hc

theorem of_setting_eq {D : D7}
    (P : ∀ X : Formalism.L2.SG.HidaSetting.HidaSetting D, X.B.I = Formalism.L2.SG.InstExistsPf.instOf D → Formalism.L2.Theta.GA D (D.sp.Y 0) → Prop)
    (X X' : Formalism.L2.SG.HidaSetting.HidaSetting D) (hX : X = X') (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (h' : X'.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t t' : Formalism.L2.Theta.GA D (D.sp.Y 0)) (ht : t = t') (hP : P X' h' t') :
    P X h t := by
  subst hX
  subst ht
  exact hP

end GlobalTheory.Mem.R3.LinkLev

namespace GlobalTheory.Mem.R3.LinkLev
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem levels_withErr_updS (R : RealDat3 D A3 Ks) (kap : ℝ) (lam e) (F : Face3 D A3) (Dc Sp Zsc)
    (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : Formalism.L2.Theta.GA D (D.sp.Y 0)) :
    (Formalism.IndefR.AutomorphicEvaluation.ConjLevel t⁻¹ (levS _ (((R.updS kap lam).withErr e).βY 0) (((R.updS kap lam).withErr e).dat0 (((R.updS kap lam).withErr e).toRealDat.levR (reFace F Dc Sp Zsc).lv2 true)))
      (Formalism.IndefR.Lev.levChi _ (((R.updS kap lam).withErr e).βY 0) (((R.updS kap lam).withErr e).dat0 (((R.updS kap lam).withErr e).toRealDat.levR (reFace F Dc Sp Zsc).lv2 true)))
      (Formalism.L2.SG.RowsJoinPinned.iotaX X h ⁻¹' GlobalTheory.Mem.SRe.concreteLevelAdelicSubset X) (fun k => GlobalTheory.Mem.SRe.adelicCharacterOfHidaSetting X (Formalism.L2.SG.RowsJoinPinned.iotaX X h k)) ∧
      Formalism.L2.SG.RowLevelMatch.RowLevelMatchAt ((R.updS kap lam).withErr e).toRealDat (reFace F Dc Sp Zsc).lv2 X h t) ↔
    (Formalism.IndefR.AutomorphicEvaluation.ConjLevel t⁻¹ (GlobalTheory.Mem.SRe.JR R.toRealDat F.lv2) (GlobalTheory.Mem.SRe.chiR R.toRealDat F.lv2)
      (Formalism.L2.SG.RowsJoinPinned.iotaX X h ⁻¹' GlobalTheory.Mem.SRe.concreteLevelAdelicSubset X) (fun k => GlobalTheory.Mem.SRe.adelicCharacterOfHidaSetting X (Formalism.L2.SG.RowsJoinPinned.iotaX X h k)) ∧
      Formalism.L2.SG.RowLevelMatch.RowLevelMatchAt R.toRealDat F.lv2 X h t) := Iff.rfl

end GlobalTheory.Mem.R3.LinkLev

namespace GlobalTheory.Mem.R3.LinkLev

open GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3.Tr


set_option maxHeartbeats 4000000 in
theorem levels_of_twArgs {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
    {L : SizeData₂ (w.st Z).toD7} {hT : GatTies (w.st Z).toD7} {Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L} {Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7}
    {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (w.st Z).toD7} {cX : ExtraC} {ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX}
    {t : RowsT K w Z Wt ex.p0} (a : TwArgs ex t) (x : TwIn ex) (ax : HEq a.x x) (X : Formalism.L2.SG.HidaSetting.HidaSetting (w.st Z).toD7)
    (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf (w.st Z).toD7) (s : Formalism.L2.Theta.GA (w.st Z).toD7 ((w.st Z).toD7.sp.Y 0))
    (hs : Formalism.IndefR.AutomorphicEvaluation.ConjLevel s⁻¹ (GlobalTheory.Mem.SRe.JR t.r.z.R.toRealDat t.r.z.F.lv2) (GlobalTheory.Mem.SRe.chiR t.r.z.R.toRealDat t.r.z.F.lv2)
      (Formalism.L2.SG.RowsJoinPinned.iotaX X h ⁻¹' GlobalTheory.Mem.SRe.concreteLevelAdelicSubset X) (fun k => GlobalTheory.Mem.SRe.adelicCharacterOfHidaSetting X (Formalism.L2.SG.RowsJoinPinned.iotaX X h k)) ∧
      Formalism.L2.SG.RowLevelMatch.RowLevelMatchAt t.r.z.R.toRealDat t.r.z.F.lv2 X h s) :
    Formalism.IndefR.AutomorphicEvaluation.ConjLevel s⁻¹ (levS _ (x.R.βY 0) (x.R.dat0 (x.R.toRealDat.levR x.F.lv2 true)))
      (Formalism.IndefR.Lev.levChi _ (x.R.βY 0) (x.R.dat0 (x.R.toRealDat.levR x.F.lv2 true)))
      (Formalism.L2.SG.RowsJoinPinned.iotaX X h ⁻¹' GlobalTheory.Mem.SRe.concreteLevelAdelicSubset X) (fun k => GlobalTheory.Mem.SRe.adelicCharacterOfHidaSetting X (Formalism.L2.SG.RowsJoinPinned.iotaX X h k)) ∧
      Formalism.L2.SG.RowLevelMatch.RowLevelMatchAt x.R.toRealDat x.F.lv2 X h s := by
  cases ax
  obtain ⟨Dc, Sp, Zsc, lam, err, lam_eq, x, pack, _⟩ := a
  obtain ⟨G, grp, fin, Pl0, I0, T0, A3, core, alg, R, F, cG, _⟩ := x
  dsimp only at pack ⊢
  cases pack
  exact (levels_withErr_updS _ _ _ _ _ _ _ _ _ _ _).2 hs

end GlobalTheory.Mem.R3.LinkLev

namespace GlobalTheory.Mem.R3.LinkLev


end GlobalTheory.Mem.R3.LinkLev
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSemiAbelianUniformisationPullbackInjectiveLoc
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSemiAbelianUniformisationPullbackInjectiveLoc
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.UT GlobalTheory.ArcPull GlobalTheory.PullLinear

noncomputable section

namespace GlobalTheory.Mum

theorem has_pull : ∀ (R R' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), AdmBase R (maximalIdeal R) → AdmBase R' (maximalIdeal R') → Function.Injective ρ → IsLocalHom ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')), Nonempty (IsPullDeg ρ D.toPre D'.toPre) → Has D → Has D' := by
  intro R R' _ _ _ _ _ _ ρ hR hR' hinj hloc D D' ⟨hD⟩ ⟨G, _, _, A, hsa, ⟨U⟩⟩
  have hP := GlobalTheory.abelianSchemeLaws_all.1.polBaseChange
  have hG := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  have hS := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  have hT := GlobalTheory.twistBaseChange
  have hI : (maximalIdeal R).map ρ ≤ maximalIdeal R' := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
    exact fun h => (mem_maximalIdeal x).1 hx (isUnit_of_map_unit ρ x h)
  have sq : spMap (fracMap hinj) ≫ jK R = jK R' ≫ spMap ρ := (fracMap_sq hinj).symm.trans (Category.id_comp _)
  obtain ⟨A', gA, pA, dA, mA, tA⟩ := hP _ _ (spMap (fracMap hinj)) A
  have gpA : IsGrpPullback A'.A A.A (spMap (fracMap hinj)) gA := ⟨pA, fun T x y x₀ y₀ hx hy => by
    have e₁ : x₀ = Out.toBase pA.w x := Over.OverMorphism.ext hx
    have e₂ : y₀ = Out.toBase pA.w y := Over.OverMorphism.ext hy
    rw [e₁, e₂, ← mA]; rfl⟩
  have gpG := ThetaBaseChange.grp_generic U.toUnifPre
  have gp' : IsGrpPullback ((Over.pullback (jK R')).obj ((Over.pullback (specOf ρ)).obj G)) G
      (spMap (fracMap hinj) ≫ jK R)
      (pullback.fst ((Over.pullback (specOf ρ)).obj G).hom (jK R') ≫ pullback.fst G.hom (spMap ρ)) :=
    ((isGrpPullback_pullback ((Over.pullback (specOf ρ)).obj G) (jK R')).comp
      (isGrpPullback_pullback G (spMap ρ))).congr sq.symm rfl
  obtain ⟨eA, mE, heA⟩ := grpPullback_iso gp' (gpA.comp gpG)
  have hgi : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have hbc : (Iso.refl ((Over.pullback (specOf ρ)).obj G)).hom.left ≫ pullback.fst G.hom (specOf ρ) =
      pullback.fst G.hom (spMap ρ) :=
    Category.id_comp _
  have wA : LBIso (A'.L.pull eA.hom.left) (U.LG.L.pull (pullback.fst ((Over.pullback (specOf ρ)).obj G).hom (jK R') ≫
      (Iso.refl ((Over.pullback (specOf ρ)).obj G)).hom.left ≫ pullback.fst G.hom (specOf ρ))) := by
    refine LBIso.trans (pull_isLB A'.isLB _) (pull_isLB (pull_isLB A.isLB gA) eA.hom.left)
      (pull_isLB U.LG.isLB _)
      ((LBIso.symm tA).chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull A'.L _ _ rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (A.L.pull gA) _ _ rfl)) ?_
    refine LBIso.chartPull (h := eA.hom.left ≫ gA ≫ U.gen.inv.left)
      (chartPullLinComb A.L gA (fun _ => eA.hom.left) (fun _ => U.gen.hom.left) _ _ fun _ => ?_)
      (chartPullSame U.LG.L _ (fun _ => pullback.fst G.hom (jK R)) _ _ fun _ => ?_) U.ext
    · rw [Category.assoc, Category.assoc, hgi, Category.comp_id]
    · rw [hbc, ← heA]; simp only [Category.assoc]
  have he : eSec ((Over.pullback (specOf ρ)).obj G) ≫ (Iso.refl ((Over.pullback (specOf ρ)).obj G)).hom.left ≫
      pullback.fst G.hom (specOf ρ) = specOf ρ ≫ eSec G := by
    rw [hbc]; exact (cubeMapOf (isGrpPullback_pullback G (spMap ρ))).e_comm
  have hr : (rigPullOf (G := G) (G' := (Over.pullback (specOf ρ)).obj G) _ (specOf ρ) he U.LG.L U.LG.rig).IsGen :=
    LBxP.isGen_pullAlong U.LG.L _ (specOf ρ) (fun _ : PUnit => eSec G) (fun _ => 1)
      (fun _ => eSec ((Over.pullback (specOf ρ)).obj G)) (fun _ => he) U.LG.rig U.LG.rigGen
  let L' : RigLB ((Over.pullback (specOf ρ)).obj G) :=
    ⟨U.LG.L.pull ((Iso.refl ((Over.pullback (specOf ρ)).obj G)).hom.left ≫ pullback.fst G.hom (specOf ρ)),
      rigPullOf (G := G) (G' := (Over.pullback (specOf ρ)).obj G) _ (specOf ρ) he U.LG.L U.LG.rig,
      pull_isLB U.LG.isLB _, hr⟩
  have mR : IsMonHom (Iso.refl ((Over.pullback (specOf ρ)).obj G)).hom := by
    show IsMonHom (𝟙 _); infer_instance
  have hgD : D'.toPre.P.g = D.toPre.P.g := H1.dim_unique _ D'.toPre.P.smoothDim
    ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (pull_grp hD).1 D.toPre.P.smoothDim)
    (eSec D'.toPre.P.A (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R'))
  obtain ⟨U', -, -, -⟩ := GlobalTheory.TorsionFormCompare.exists_unif_pull_of_deg hP hG hS hT R R' _ _ hR hR' ρ hI D A G hsa
    U D' hD hgD ((Over.pullback (specOf ρ)).obj G) (Iso.refl _) mR A' dA eA mE wA L' (idIso _) he
    (idIso_isGen L'.isLB) (fun p => hr p.1 p.2)
  exact ⟨(Over.pullback (specOf ρ)).obj G, inferInstance, inferInstance, A', IsSemiAbelian.pullback _ G hsa, ⟨U'⟩⟩

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSemiAbelianUniformisationPullbackInjectiveLocStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSemiAbelianUniformisation_pullback_injective_local : ∀ (R R' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), AdmBase R (maximalIdeal R) → AdmBase R' (maximalIdeal R') → Function.Injective ρ → IsLocalHom ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')), Nonempty (IsPullDeg ρ D.toPre D'.toPre) → Has D → Has D' := by
  first | exact @GlobalTheory.Mum.has_pull | exact GlobalTheory.Mum.has_pull | (intros; apply GlobalTheory.Mum.has_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareZeroAugmentedAlgebra
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareZeroAugmentedAlgebra
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.Obs.TrivAug

variable {R R₀ : Type} [CommRing R] [CommRing R₀]

theorem mul_eq_of_map_eq {I : Ideal R} (hI : I ^ 2 = 0) {π : R →+* R₀} (hk : RingHom.ker π = I)
    {a b : R} (h : π a = π b) (i : I) : a * (i : R) = b * i := by
  have h1 : a - b ∈ I := hk ▸ (RingHom.mem_ker.2 (by rw [map_sub, h, sub_self]))
  have h2 : (a - b) * (i : R) ∈ I ^ 2 := by
    rw [pow_two]; exact Ideal.mul_mem_mul h1 i.2
  rw [hI, Ideal.zero_eq_bot, Ideal.mem_bot, sub_mul, sub_eq_zero] at h2
  exact h2

def smulI (I : Ideal R) {π : R →+* R₀} (hπ : Function.Surjective π) : SMul R₀ I :=
  ⟨fun r i => ⟨Function.surjInv hπ r * i, I.mul_mem_left _ i.2⟩⟩

def modI {I : Ideal R} (hI : I ^ 2 = 0) {π : R →+* R₀} (hπ : Function.Surjective π)
    (hk : RingHom.ker π = I) : Module R₀ I :=
  @Function.Surjective.moduleLeft R R₀ I _ _ _ _ (smulI I hπ) π hπ (fun c x => by
    apply Subtype.ext
    show Function.surjInv hπ (π c) * (x : R) = c * x
    exact mul_eq_of_map_eq hI hk (Function.surjInv_eq hπ (π c)) x)

def modOpI {I : Ideal R} (hI : I ^ 2 = 0) {π : R →+* R₀} (hπ : Function.Surjective π)
    (hk : RingHom.ker π = I) : Module R₀ᵐᵒᵖ I :=
  letI := modI hI hπ hk
  Module.compHom I (RingEquiv.toOpposite R₀).symm.toRingHom

end GlobalTheory.Obs.TrivAug
end

open GlobalTheory.Obs.TrivAug in
theorem GlobalTheory.Obs.exists_aug : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I), ∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra R₀ R₁), Nonempty (Aug I π R₁) := by
  intro R R₀ _ _ I hI π hπ hk
  letI : Module R₀ I := modI hI hπ hk
  letI : Module R₀ᵐᵒᵖ I := modOpI hI hπ hk
  haveI : IsCentralScalar R₀ I := ⟨fun r m => by
    apply Subtype.ext
    show Function.surjInv hπ (MulOpposite.unop (MulOpposite.op r)) * (m : R) = Function.surjInv hπ r * m
    rfl⟩
  haveI : IsScalarTower R₀ R₀ᵐᵒᵖ I := ⟨fun r s m => by
    apply Subtype.ext
    show Function.surjInv hπ (MulOpposite.unop (r • s)) * (m : R) = Function.surjInv hπ r * (Function.surjInv hπ (MulOpposite.unop s) * m)
    rw [← _root_.mul_assoc]
    refine mul_eq_of_map_eq hI hk ?_ m
    simp [Function.surjInv_eq hπ, smul_eq_mul, mul_comm]⟩
  refine ⟨TrivSqZeroExt R₀ I, inferInstance, inferInstance, ⟨?_⟩⟩
  exact
  { q := TrivSqZeroExt.fstHom R₀ R₀ I
    k := { toFun := fun y => (y.snd : R), map_zero' := rfl, map_add' := fun _ _ => rfl }
    mem := fun y => y.snd.2
    smul := fun r y => by
      show Function.surjInv hπ (π r) * (y.snd : R) = r * y.snd
      exact mul_eq_of_map_eq hI hk (Function.surjInv_eq hπ (π r)) _
    one := rfl
    sq := fun y y' h h' => by
      have h0 : y.fst = 0 := h
      have h0' : y'.fst = 0 := h'
      ext
      · simp [h0]
      · simp [h0, h0']
    inj := fun y h h' => by
      have h0 : y.fst = 0 := h
      ext
      · exact h0
      · have h1 : (y.snd : R) = 0 := h'
        rw [h1]; rfl
    surj := fun i hi => ⟨TrivSqZeroExt.inr ⟨i, hi⟩, rfl, rfl⟩ }
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareZeroAugmentedAlgebraStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_squareZeroAugmentedAlgebra : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I), ∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra R₀ R₁), Nonempty (Aug I π R₁) := by
  first | exact @GlobalTheory.Obs.exists_aug | exact GlobalTheory.Obs.exists_aug | (intros; apply GlobalTheory.Obs.exists_aug <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareZeroSmoothLiftSystemPresents
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareZeroSmoothLiftSystemPresents
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftSys.OfLift

theorem sec_smooth {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) [Smooth s] (U : X.affineOpens) :
    Algebra.Smooth R (Sec s U.1) := by
  have h := HasRingHomProperty.appLE @Smooth s ‹_› ⟨⊤, isAffineOpen_top _⟩ U le_top
  have h' : RingHom.Smooth ((s.appLE ⊤ U.1 le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) :=
    RingHom.Smooth.comp (RingHom.Smooth.of_bijective
      (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.bijective) h
  exact RingHom.smooth_algebraMap.mp h'

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀}
  {X₀ X : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀} {s : X ⟶ Sp R} {i : X₀ ⟶ X}

theorem surjective_spMap (hI : I ^ 2 = 0) (hk : RingHom.ker π = I) (hπ : Function.Surjective π) :
    Surjective (spMap π) := by
  constructor
  intro x
  have hx : (show PrimeSpectrum R from x) ∈ Set.range (PrimeSpectrum.comap π) := by
    refine (range_comap_of_surjective R₀ π hπ).ge ?_
    rw [hk]
    intro a ha
    have h2 : a ^ 2 = 0 := by
      have := Ideal.pow_mem_pow ha 2
      rwa [hI, Ideal.zero_eq_bot, Ideal.mem_bot] at this
    exact (show PrimeSpectrum R from x).2.mem_of_pow_mem 2 (by rw [h2]; exact zero_mem _)
  obtain ⟨y, hy⟩ := hx
  exact ⟨y, hy⟩

variable (hpb : IsPullback i s₀ s (spMap π)) (hπ : Function.Surjective π) (hn : IsNilpotent (RingHom.ker π))

def liftOpen (U : X₀.affineOpens) : X.affineOpens :=
  ⟨(GlobalTheory.AffineThickening.exists_isAffineOpen_preimage_eq_of_isNilpotent R R₀ π hπ hn X X₀ s s₀ i hpb U.1 U.2).choose,
    (GlobalTheory.AffineThickening.exists_isAffineOpen_preimage_eq_of_isNilpotent R R₀ π hπ hn X X₀ s s₀ i hpb U.1 U.2).choose_spec.1⟩

theorem preimage_liftOpen (U : X₀.affineOpens) : i ⁻¹ᵁ (liftOpen hpb hπ hn U).1 = U.1 :=
  (GlobalTheory.AffineThickening.exists_isAffineOpen_preimage_eq_of_isNilpotent R R₀ π hπ hn X X₀ s s₀ i hpb U.1 U.2).choose_spec.2

theorem liftOpen_mono (hi : Function.Surjective i.base) {U V : X₀.affineOpens} (h : V ≤ U) :
    liftOpen hpb hπ hn V ≤ liftOpen hpb hπ hn U := by
  intro x hx
  obtain ⟨y, rfl⟩ := hi x
  have hy : y ∈ i ⁻¹ᵁ (liftOpen hpb hπ hn V).1 := hx
  rw [preimage_liftOpen] at hy
  have hy' : y ∈ i ⁻¹ᵁ (liftOpen hpb hπ hn U).1 := by
    rw [preimage_liftOpen]; exact h hy
  exact hy'

def pr (U : X₀.affineOpens) : GlobalTheory.CechDR.Pair i := ⟨(U, liftOpen hpb hπ hn U), (preimage_liftOpen hpb hπ hn U).ge⟩

end GlobalTheory.LiftSys.OfLift


open GlobalTheory.LiftSys.OfLift in
theorem GlobalTheory.LiftSys.exists_sys_presents : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), ∀ (X : Scheme.{0}) (s : X ⟶ Sp R) (i : X₀ ⟶ X), IsPullback i s₀ s (spMap π) → Smooth s → ∃ S : Sys I π s₀, Nonempty (S.Presents s i) := by
  intro R R₀ _ _ I hI π hπ hk X₀ s₀ X s i hpb hsm
  have hn : IsNilpotent (RingHom.ker π) := ⟨2, hk ▸ hI⟩
  haveI := surjective_spMap hI hk hπ
  have hi : Function.Surjective i.base :=
    (MorphismProperty.of_isPullback (P := @Surjective) hpb.flip ‹_›).surj
  let G : AffOp X₀ ⥤ AffOp X :=
    (Monotone.functor (f := liftOpen hpb hπ hn) fun _ _ h ↦ liftOpen_mono hpb hπ hn hi h).op
  let S : Sys I π s₀ :=
    { F := G ⋙ OAff s
      p := fun U ↦ GlobalTheory.CechDR.secPull s s₀ (pr hpb hπ hn U.unop)
      semi := fun U ↦ GlobalTheory.CechDR.semiHom_secPull hpb.w _
      nat := fun {U V} a b ↦ (congrArg (fun t ↦ t.hom b) (i.map_appLE (pr hpb hπ hn V.unop).2
          (homOfLE (liftOpen_mono hpb hπ hn hi (leOfHom a.unop))).op)).trans
        (congrArg (fun t ↦ t.hom b) (i.appLE_map (pr hpb hπ hn U.unop).2 (homOfLE (show V.unop.1 ≤ U.unop.1 from leOfHom a.unop)).op)).symm
      surj := fun U ↦ (GlobalTheory.CechDR.secPull_surjective_and_ker R R₀ I π hπ hk X₀ X s₀ s i hpb (pr hpb hπ hn U.unop) (preimage_liftOpen hpb hπ hn U.unop)).1
      ker := fun U b ↦ (GlobalTheory.CechDR.secPull_surjective_and_ker R R₀ I π hπ hk X₀ X s₀ s i hpb (pr hpb hπ hn U.unop) (preimage_liftOpen hpb hπ hn U.unop)).2 b
      smooth := fun U ↦ sec_smooth s _ }
  exact ⟨S, ⟨⟨fun U ↦ affPt s (liftOpen hpb hπ hn U.unop), fun U ↦ (liftOpen hpb hπ hn U.unop).2.isOpenImmersion_fromSpec, fun U ↦ affPt_w s _,
    fun U V a ↦ affPt_res s _, fun U ↦ GlobalTheory.CechDR.secPull_affPt s s₀ (pr hpb hπ hn U.unop),
    S.cover_of_surjective ⟨hi⟩ _ fun U ↦ GlobalTheory.CechDR.secPull_affPt s s₀ (pr hpb hπ hn U.unop)⟩⟩⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareZeroSmoothLiftSystemPresentsStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_squareZeroSmoothLiftSystem_presents : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), ∀ (X : Scheme.{0}) (s : X ⟶ Sp R) (i : X₀ ⟶ X), IsPullback i s₀ s (spMap π) → Smooth s → ∃ S : Sys I π s₀, Nonempty (S.Presents s i) := by
  first | exact @GlobalTheory.LiftSys.exists_sys_presents | exact GlobalTheory.LiftSys.exists_sys_presents | (intros; apply GlobalTheory.LiftSys.exists_sys_presents <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawLeftRestrictionGlobal
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp.TupLe

variable {D : D7}

theorem isConjPl_div {P P' : Pl D.host.E} (h : Formalism.BasicNotions.IsConjPl D.host P P') : Formalism.L2.DIV.IsConjPl P P' :=
  fun a b e => h a b (by rw [e, Formalism.BasicNotions.Examples₂.star_eq_conj])

theorem lev_isConjPl_iff {P P' : Pl D.host.E} : Lev.IsConjPl P P' ↔ P' = Formalism.L2.DIV.conjPl P := by
  refine ⟨fun h => (isConjPl_div (isConjPl_of_lev h)).eq_conjPl, ?_⟩
  rintro rfl
  have h : Lev.IsConjPl P (Formalism.DivisionValues.conjPl P) := GlobalTheory.GoodPrimes.isConjPl_iff.2 rfl
  rwa [(isConjPl_div (isConjPl_of_lev h)).eq_conjPl] at h

theorem isConjPl_conjPl_divisor (P : Pl D.host.E) : Formalism.BasicNotions.IsConjPl D.host P (Formalism.L2.DIV.conjPl P) :=
  isConjPl_of_lev (lev_isConjPl_iff.2 rfl)


open Classical in
theorem disjoint_conj {X : Finset (Pl D.host.E)} (hX : SplitSet X) : Disjoint X (X.image Formalism.L2.DIV.conjPl) := by
  refine Finset.disjoint_left.2 fun P hP hQ => ?_
  obtain ⟨P₀, h0, rfl⟩ := Finset.mem_image.1 hQ
  have a1 : Formalism.L2.NTheta.IsIdemAt (cA D (idemAt P₀)) (Formalism.L2.DIV.conjPl P₀) :=
    GlobalTheory.MovedIdem.isIdemAt_conj (hX.isIdemAt h0) fun x => Iff.rfl
  have a2 := hX.mul_conj hP h0
  rw [idemAt_eq a1, a1.1.1] at a2
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (Formalism.L2.DIV.conjPl P₀).ne_bot
  refine (a1.2 x hx0).1 hx ?_
  rw [a2, zero_mul, map_zero]
  exact zero_mem _


open Classical in
theorem idem_add_cA {X : Finset (Pl D.host.E)} (hX : SplitSet X) :
    idem X + cA D (idem X) = idem (X ∪ X.image Formalism.L2.DIV.conjPl) := by
  rw [← idem_eq (GlobalTheory.RefDatumLev.isIdemSum_conjPl hX.isIdemSum), idem, idem, idem, Finset.sum_union (disjoint_conj hX)]


open Classical in
theorem idem_add_cA_eq {X Y : Finset (Pl D.host.E)} (hX : SplitSet X) (hY : SplitSet Y)
    (h : ∀ P, P ∈ X ∪ X.image Formalism.L2.DIV.conjPl ↔ P ∈ Y ∪ Y.image Formalism.L2.DIV.conjPl) :
    idem X + cA D (idem X) = idem Y + cA D (idem Y) := by
  rw [idem_add_cA hX, idem_add_cA hY]
  congr 1
  ext P
  exact h P


open Classical in
theorem mem_half_closure {ch : Set (Pl D.host.E)}
    (hch : ∀ P P', Formalism.BasicNotions.IsConjPl D.host P P' → P ≠ P' → (P ∈ ch ↔ P' ∉ ch)) {A B : Finset (Pl D.host.E)}
    (hcl : ∀ P, P ∈ A ∨ P ∈ B → Formalism.L2.DIV.conjPl P ∈ A ∨ Formalism.L2.DIV.conjPl P ∈ B)
    (hne : ∀ P, P ∈ A ∨ P ∈ B → Formalism.L2.DIV.conjPl P ≠ P) (P : Pl D.host.E) :
    P ∈ half ch A ∪ half ch B ∪ (half ch A ∪ half ch B).image Formalism.L2.DIV.conjPl ↔ P ∈ A ∨ P ∈ B := by
  have hY : ∀ P, P ∈ half ch A ∪ half ch B → P ∈ A ∨ P ∈ B := fun P h => by
    rcases Finset.mem_union.1 h with h | h
    exacts [Or.inl (mem_half.1 h).1, Or.inr (mem_half.1 h).1]
  have hmY : ∀ P, P ∈ A ∨ P ∈ B → P ∈ ch → P ∈ half ch A ∪ half ch B := fun P hP hc => by
    rcases hP with h | h
    exacts [Finset.mem_union_left _ (mem_half.2 ⟨h, hc⟩), Finset.mem_union_right _ (mem_half.2 ⟨h, hc⟩)]
  constructor
  · intro h
    rcases Finset.mem_union.1 h with h | h
    · exact hY P h
    · obtain ⟨P', hP', rfl⟩ := Finset.mem_image.1 h
      exact hcl P' (hY P' hP')
  · intro hP
    by_cases hc : P ∈ ch
    · exact Finset.mem_union_left _ (hmY P hP hc)
    · have hc' : Formalism.L2.DIV.conjPl P ∈ ch := by
        by_contra hc'
        exact hc ((hch P (Formalism.L2.DIV.conjPl P) (isConjPl_conjPl_divisor P) (hne P hP).symm).2 hc')
      exact Finset.mem_union_right _
        (Finset.mem_image.2 ⟨Formalism.L2.DIV.conjPl P, hmY _ (hcl P hP) hc', Formalism.L2.DIV.conjPl_conjPl P⟩)

theorem not_mem_of_coprime {P : Pl D.host.E} {l q : ℕ} (hq : (q : 𝓞 D.host.E) ∈ P.asIdeal) (hc : Nat.Coprime l q) :
    (l : 𝓞 D.host.E) ∉ P.asIdeal := fun hl => by
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hc
  refine P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
  have e : (u : 𝓞 D.host.E) * (l : 𝓞 D.host.E) + (v : 𝓞 D.host.E) * (q : 𝓞 D.host.E) = 1 := by
    have := congrArg (Int.cast : ℤ → 𝓞 D.host.E) huv
    push_cast at this
    exact this
  rw [← e]
  exact add_mem (Ideal.mul_mem_left _ _ hl) (Ideal.mul_mem_left _ _ hq)


end GlobalTheory.BigOn.Exp.TupLe
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalLagrangianIntegralSiegelParabolicTransfo
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
theorem _root_.GlobalTheory.T.diagonal_lagrangian_integral_siegel_parabolic_transform : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∀ (χS : (AF F ⊗[F] E)ˣ →* Circle) (ωd : GAF σ JS × GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) →*
            Module.End ℂ (WOF F E nS (nT + nT) → ℂ)),
        IsWeilDatumOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)
            (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
      ∃ α : GL (Fin nT) (AF F ⊗[F] E) →* Circle, Continuous α ∧
        (∀ a : GL (Fin nT) E, α (Matrix.GeneralLinearGroup.map (incAF F E) a) = 1) ∧
        ∀ (h : GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)) (t : GL (Fin nT) (AF F ⊗[F] E)),
          mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) h * ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) = ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) * t.1 →
          ∀ f, IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f →
            GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) (ωd (1, h) f) = (α t : ℂ) * ((((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F) (Matrix.GeneralLinearGroup.det t)) : ℝ) ^ ((Fintype.card (Fin nS) : ℝ) / 2) : ℝ) : ℂ) * GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) f := by
  first | exact @PositivityTheory.ThKW.lagrangian_integral_fundamental_domain | exact PositivityTheory.ThKW.lagrangian_integral_fundamental_domain | (intros; apply PositivityTheory.ThKW.lagrangian_integral_fundamental_domain <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VolumeImageComplPtsIn
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.Mean4 GlobalTheory.Mean4O
open MeasureTheory GlobalTheory.ChartGlue

namespace GlobalTheory.Mean4O.CoverInt

theorem volume_image_compl_ptsIn : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (σ : k →+* ℂ), Function.Injective σ → (∀ W : X.Opens, Nonempty W → Function.Injective (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p W)) → ∀ U : X.Opens, genericPoint X ∈ U → ∀ (D : ℕ) (c : AlgChart p σ D), MeasureTheory.volume (c.e '' (c.e.source ∩ (ptsIn p σ U)ᶜ)) = 0 := by
  intro k _ X _ p σ hσ _ U hU D c
  have : IsDomain k := hσ.isDomain σ
  refine measure_mono_null ?_ (ae_iff.1 (SemiPosBir.ae_mem hσ c (U := U) ⟨_, hU⟩))
  rintro _ ⟨z, hz, rfl⟩ h
  have h₁ := h (c.e.map_source hz.1)
  rw [c.e.left_inv hz.1] at h₁
  exact hz.2 h₁

end GlobalTheory.Mean4O.CoverInt
end
end
