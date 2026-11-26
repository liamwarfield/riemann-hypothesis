module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusInvariantFieldConstCoeffs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantHeatOperatorsDifferenceGlobal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAddHomInvariantFieldKillsWeightZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecHomExtOfLocalizationAtPrimes
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecHomExtOfLocalizationAtPrimes
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SpecLocalExt

theorem hom_ext_of_localizationAtPrime : ∀ (A : Type) [CommRing A] (X : Scheme.{0}) (a b : Sp A ⟶ X), (∀ (P : Ideal A) [P.IsPrime], spMap (algebraMap A (Localization.AtPrime P)) ≫ a = spMap (algebraMap A (Localization.AtPrime P)) ≫ b) → a = b := by
  intro A _ X a b h
  refine GlobalTheory.hom_ext_of_isLocalRing fun B _ _ φ => ?_
  let P : Ideal A := (IsLocalRing.maximalIdeal B).comap φ
  haveI : P.IsPrime := Ideal.comap_isPrime φ (IsLocalRing.maximalIdeal B)
  have hu : ∀ y : P.primeCompl, IsUnit (φ y) := fun y => by
    by_contra hy
    exact y.2 ((IsLocalRing.mem_maximalIdeal _).2 hy)
  let ψ : Localization.AtPrime P →+* B := IsLocalization.lift hu
  have e : φ = ψ.comp (algebraMap A (Localization.AtPrime P)) := (IsLocalization.lift_comp hu).symm
  have h' := h P
  simp only [spMap] at h'
  rw [e, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, Category.assoc, h']

end GlobalTheory.SpecLocalExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecHomExtOfLocalizationAtPrimesStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spec_hom_ext_of_localization_at_primes : ∀ (A : Type) [CommRing A] (X : Scheme.{0}) (a b : Sp A ⟶ X), (∀ (P : Ideal A) [P.IsPrime], spMap (algebraMap A (Localization.AtPrime P)) ≫ a = spMap (algebraMap A (Localization.AtPrime P)) ≫ b) → a = b := by
  first | exact @GlobalTheory.SpecLocalExt.hom_ext_of_localizationAtPrime | exact GlobalTheory.SpecLocalExt.hom_ext_of_localizationAtPrime | (intros; apply GlobalTheory.SpecLocalExt.hom_ext_of_localizationAtPrime <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusTangentOfRaynaudTangentOverUnit
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusTangentOfRaynaudTangentOverUnit
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatMod.TorField

open TrivSqZeroExt (inl inr)
open ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht (coord coord_comp)

theorem exists_torTan_of_q : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (p : epsR R ⟶ Y.H), IsTangent p → p ≫ Y.q = 1 → ∃ ℓ : Q.X →+ R, p = GlobalTheory.HeatMod.TorField.torTan ℓ ≫ Y.i := by
  intro R _ _ Q O _ _ _ oa Y p hp hq
  have hmono : ∀ {T : Over (Sp R)} (a b : T ⟶ splitTorus (Sp R) (RayEv.Chr Q)), a ≫ Y.i = b ≫ Y.i → a = b :=
    fun a b h => Y.isKernel.hom_ext h (toUnit_unique _ _)
  have hw : p ≫ Y.q = toUnit _ ≫ η[Q.P.A] := by rw [hq, Hom.one_def]
  let t := Y.isKernel.lift p (toUnit _) hw
  have ht : t ≫ Y.i = p := Y.isKernel.lift_fst _ _ _
  have := Y.i_linear.isMonHom
  have htan : Chart.spMap (Chart.fstD R) ≫ t = 1 := hmono _ _ (by
    rw [Category.assoc, ht, MonObj.one_comp]; exact (Chart.isTan_iff p).2 hp)
  let a : RayEv.Chr Q → DualNumber R := fun χ =>
    (Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).hom.hom ((coord t).hom (AddMonoidAlgebra.single χ 1))
  have hfst : ∀ χ, (a χ).fst = 1 := fun χ => by
    have e := congrArg (fun f => (coord f).hom (AddMonoidAlgebra.single χ 1)) htan
    simp only at e
    rw [coord_comp, Diag.coord_one, CommRingCat.hom_comp, RingHom.comp_apply, Chart.spMap_left] at e
    have nat := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Chart.fstD R).toRingHom)
    have k := congrArg (fun f => f.hom ((coord t).hom (AddMonoidAlgebra.single χ 1))) nat
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at k
    rw [e, map_one] at k
    exact k.symm
  have h0 : a 0 = 1 := by
    show (Scheme.ΓSpecIso _).hom.hom ((coord t).hom (AddMonoidAlgebra.single 0 1)) = 1
    rw [Diag.coord_single_zero, map_one]
  have hadd : ∀ x y, a (x + y) = a x * a y := fun x y => by
    show (Scheme.ΓSpecIso _).hom.hom ((coord t).hom (AddMonoidAlgebra.single (x + y) 1)) = _
    rw [Diag.coord_single_add, map_mul]
  have hform : ∀ χ, a χ = 1 + inr (a χ).snd := fun χ => by
    ext
    · rw [hfst χ]; simp
    · simp
  let ℓ : Q.X →+ R :=
    { toFun := fun χ => (a χ).snd
      map_zero' := (congrArg TrivSqZeroExt.snd h0).trans TrivSqZeroExt.snd_one
      map_add' := fun x y => (congrArg TrivSqZeroExt.snd (hadd x y)).trans (by
        rw [hform x, hform y]
        simp only [mul_add, add_mul, _root_.one_mul, _root_.mul_one, TrivSqZeroExt.inr_mul_inr, add_zero,
          TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_one, TrivSqZeroExt.snd_inr, zero_add]) }
  refine ⟨ℓ, ?_⟩
  rw [← ht]
  refine congrArg (· ≫ Y.i) (Diag.hom_ext fun χ => ?_)
  rw [torTan, Diag.coord_ofChar]
  show _ = (Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + inr (a χ).snd)
  rw [← hform χ]
  show _ = (Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom
    ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).hom.hom ((coord t).hom (AddMonoidAlgebra.single χ 1)))
  rw [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]

end GlobalTheory.HeatMod.TorField
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusTangentOfRaynaudTangentOverUnitStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torus_tangent_of_raynaud_tangent_over_unit : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (p : epsR R ⟶ Y.H), IsTangent p → p ≫ Y.q = 1 → ∃ ℓ : Q.X →+ R, p = GlobalTheory.HeatMod.TorField.torTan ℓ ≫ Y.i := by
  first | exact @GlobalTheory.HeatMod.TorField.exists_torTan_of_q | exact GlobalTheory.HeatMod.TorField.exists_torTan_of_q | (intros; apply GlobalTheory.HeatMod.TorField.exists_torTan_of_q <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentKillingWeightZeroMapsToAbelianPartUnit
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentKillingWeightZeroMapsToAbelianPartUnit
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HeatMod.TorField

open TrivSqZeroExt (inl inr)

theorem residue_eq_zero_of_sq {B : Type} [CommRing B] [IsLocalRing B] (x : B) (h : x * x = 0) :
    IsLocalRing.residue B x = 0 :=
  (IsLocalRing.residue_eq_zero_iff x).2 ((IsLocalRing.mem_maximalIdeal x).2 (mem_nonunits_iff.2 fun hu => by
    have := hu.mul hu
    rw [h] at this
    exact not_isUnit_zero this))

theorem lieExp_comp_q_eq_one : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (v : Fin n → TanM (𝟙 (Sp R)) Y.H) (u : Fin n → (epsR R ⟶ Y.H)), (∀ a, IsTangent (u a)) → (∀ a, (u a).left = (tv (v a)).left) → ∀ (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ e : Fin n → R, (∀ (V : Q.P.A.left.Opens) f, IsWt Y 0 (Y.q.left ⁻¹ᵁ V) f → ∑ a, constFn Y.H.hom _ (e a) * dd a _ f = 0) → ∀ (B : Type) [CommRing B] [IsLocalRing B] (ψ : DualNumber R →+* B), spMap ψ ≫ (GlobalTheory.SqZero.lieExp u (fun a => (TrivSqZeroExt.inr (e a) : DualNumber R)) (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _) ≫ Y.q).left = spMap ψ ≫ (1 : epsR R ⟶ Q.P.A).left := by
  intro R _ _ Q O _ _ _ oa Y n v u ht hu dd hd e hw B _ _ ψ
  letI : Algebra R B := (ψ.comp (TrivSqZeroExt.inlHom R R)).toAlgebra
  let ψ' : DualNumber R →ₐ[R] B := { ψ with commutes' := fun r => rfl }
  have hqm : IsMonHom Y.q := Y.q_linear.isMonHom
  let c : Fin n → DualNumber R := fun a => inr (e a)
  have hc : ∀ a, c a * c a = 0 := fun _ => TrivSqZeroExt.inr_mul_inr _ _ _
  let p : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) (DualNumber R) ⟶ Y.H := GlobalTheory.SqZero.lieExp u c hc
  let z : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) B ⟶ Y.H := 1
  let t : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) B ⟶ Y.H := ReciprocityTheory.ChartRestriction.G.Chart.spMap ψ' ≫ p
  have hψ : (ReciprocityTheory.ChartRestriction.G.Chart.spMap ψ').left = spMap ψ := ReciprocityTheory.ChartRestriction.G.Chart.spMap_left ψ'
  have e1 : spMap ψ ≫ (p ≫ Y.q).left = t.left ≫ Y.q.left := by
    rw [← hψ]; rfl
  have e2 : spMap ψ ≫ (1 : epsR R ⟶ Q.P.A).left = z.left ≫ Y.q.left := by
    rw [← hψ, ← Over.comp_left, ← Over.comp_left]
    congr 1
    rw [ReciprocityTheory.ChartRestriction.G.Chart.comp_one', MonObj.one_comp]
  show spMap ψ ≫ (p ≫ Y.q).left = _
  rw [e1, e2]

  refine ReciprocityTheory.ChartRestriction.G.PullbackSections.hom_ext_of_local (R := CommRingCat.of B) ?_ ?_
  · letI : Algebra R (IsLocalRing.ResidueField B) :=
      ((IsLocalRing.residue B).comp (algebraMap R B)).toAlgebra
    let r : B →ₐ[R] IsLocalRing.ResidueField B := { IsLocalRing.residue B with commutes' := fun _ => rfl }
    have htan : IsTangent p :=
      GlobalTheory.Reg.isTangent_of_isLieComb ht ((GlobalTheory.SqZero.isLieComb_iff_lieExp e p).2 rfl)
    have hrc : r.comp ψ' = (Algebra.ofId R (IsLocalRing.ResidueField B)).comp (ReciprocityTheory.ChartRestriction.G.Chart.fstD R) :=
      DualNumber.algHom_ext (by
        have : r (ψ' DualNumber.eps) = 0 := residue_eq_zero_of_sq _ (by
          rw [← map_mul, DualNumber.eps_mul_eps, map_zero])
        rw [AlgHom.comp_apply, this, AlgHom.comp_apply]
        simp [ReciprocityTheory.ChartRestriction.G.Chart.fstD])
    have hr : ReciprocityTheory.ChartRestriction.G.Chart.spMap r ≫ t = ReciprocityTheory.ChartRestriction.G.Chart.spMap r ≫ z := by
      rw [ReciprocityTheory.ChartRestriction.G.Chart.comp_one']
      show ReciprocityTheory.ChartRestriction.G.Chart.spMap r ≫ ReciprocityTheory.ChartRestriction.G.Chart.spMap ψ' ≫ p = 1
      rw [← Category.assoc, ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp, hrc, ← ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp,
        Category.assoc, show ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.fstD R) ≫ p = 1 from
          (ReciprocityTheory.ChartRestriction.G.Chart.isTan_iff p).2 htan, ReciprocityTheory.ChartRestriction.G.Chart.comp_one']
    have H : (ReciprocityTheory.ChartRestriction.G.Chart.spMap r).left ≫ t.left ≫ Y.q.left =
        (ReciprocityTheory.ChartRestriction.G.Chart.spMap r).left ≫ z.left ≫ Y.q.left := by
      rw [← Category.assoc, ← Category.assoc]
      exact congrArg (fun f => Over.Hom.left f ≫ Y.q.left) hr
    rw [ReciprocityTheory.ChartRestriction.G.Chart.spMap_left] at H
    have hcp : (Spec.map (CommRingCat.ofHom r.toRingHom)).base (IsLocalRing.closedPoint (IsLocalRing.ResidueField B)) =
        IsLocalRing.closedPoint (CommRingCat.of B) := IsLocalRing.comap_closedPoint (IsLocalRing.residue B)
    rw [← hcp]
    exact congrArg (fun f => f (IsLocalRing.closedPoint (IsLocalRing.ResidueField B))) H
  · intro U h₁ h₂
    have H : ∀ g, valR (t.left ≫ Y.q.left) U g = valR (z.left ≫ Y.q.left) U g := by
      intro g
      have hz : ⊤ ≤ z.left ⁻¹ᵁ (Y.q.left ⁻¹ᵁ U) := h₂
      let e' : Fin n → B := fun a => ψ' (c a)
      have he' : ∀ i j, e' i * e' j = 0 := fun i j => by
        simp only [e', ← map_mul, c, TrivSqZeroExt.inr_mul_inr, map_zero]
      obtain ⟨b₁, b₂⟩ := valR_prod hu ht hd e' he' z (Y.q.left ⁻¹ᵁ U) hz Finset.univ
      have ht' : t = (∏ i ∈ Finset.univ, (ReciprocityTheory.ChartRestriction.G.Chart.spMap (GlobalTheory.SqZero.epsTo R (e' i) (he' i i)) ≫ u i :
          ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) B ⟶ Y.H)) * z := by
        rw [_root_.mul_one]
        exact GlobalTheory.SqZero.comp_lieExp u ψ' c hc
      rw [← ht'] at b₁ b₂
      have hF : pbT Y.q.left g (Y.q.left ⁻¹ᵁ U) = (Y.q.left.appLE U (Y.q.left ⁻¹ᵁ U) le_rfl).hom g :=
        GlobalTheory.KS.pbT_of_le _ le_rfl g
      have hwF := hw U _ (isWt_pbT Y U g (Y.q.left ⁻¹ᵁ U) le_rfl)
      rw [← GlobalTheory.Points.valR_appLE t.left Y.q.left le_rfl b₁ g, ← GlobalTheory.Points.valR_appLE z.left Y.q.left le_rfl hz g,
        ← hF, b₂]
      have hz' : z.left ≫ Y.H.hom = spMap (algebraMap R B) := Over.w z
      have key : ∀ i, e' i = ψ (inr 1) * algebraMap R B (e i) := fun i => by
        show ψ (inr (e i)) = ψ (inr 1) * ψ (inl (e i))
        rw [← map_mul]
        congr 1
        ext <;> simp
      have hv := congrArg (valR z.left (Y.q.left ⁻¹ᵁ U)) hwF
      set_option synthInstance.maxHeartbeats 100000 in
        rw [GlobalTheory.ZH.CrdCalc.valR_eq _ _ hz, map_sum, GlobalTheory.ZH.CrdCalc.valR_eq _ _ hz, map_zero] at hv
      simp only [← GlobalTheory.ZH.CrdCalc.valR_eq _ _ hz, WtAlg.valR_mul'' _ _ hz,
        GlobalTheory.Points.valR_constFn_of_over _ _ _ hz' _ hz] at hv
      simp only [key, _root_.mul_assoc, ← Finset.mul_sum, hv, mul_zero, add_zero]
    ext g
    have := H g
    rw [GlobalTheory.ZH.CrdCalc.valR_eq _ _ h₁, GlobalTheory.ZH.CrdCalc.valR_eq _ _ h₂] at this
    exact (Scheme.ΓSpecIso (CommRingCat.of B)).commRingCatIsoToRingEquiv.injective this

end GlobalTheory.HeatMod.TorField
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentKillingWeightZeroMapsToAbelianPartUnitStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_killing_weight_zero_maps_to_abelianPart_unit : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (v : Fin n → TanM (𝟙 (Sp R)) Y.H) (u : Fin n → (epsR R ⟶ Y.H)), (∀ a, IsTangent (u a)) → (∀ a, (u a).left = (tv (v a)).left) → ∀ (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ e : Fin n → R, (∀ (V : Q.P.A.left.Opens) f, IsWt Y 0 (Y.q.left ⁻¹ᵁ V) f → ∑ a, constFn Y.H.hom _ (e a) * dd a _ f = 0) → ∀ (B : Type) [CommRing B] [IsLocalRing B] (ψ : DualNumber R →+* B), spMap ψ ≫ (GlobalTheory.SqZero.lieExp u (fun a => (TrivSqZeroExt.inr (e a) : DualNumber R)) (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _) ≫ Y.q).left = spMap ψ ≫ (1 : epsR R ⟶ Q.P.A).left := by
  first | exact @GlobalTheory.HeatMod.TorField.lieExp_comp_q_eq_one | exact GlobalTheory.HeatMod.TorField.lieExp_comp_q_eq_one | (intros; apply GlobalTheory.HeatMod.TorField.lieExp_comp_q_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAddHomInvariantFieldKillsWeightZero
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HeatMod.TorUniq
open GlobalTheory.ZH.CrdCalc (valR_res valR_spMap)
open ReciprocityTheory.ChartRestriction.G.Chart (sp)
open TrivSqZeroExt (inl inr)
open ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht (coord coord_comp)
open GlobalTheory.HeatMod.TorField

theorem exists_addHom_of_kills_wt_zero : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ e : Fin n → R, (∀ (V : Q.P.A.left.Opens) f, IsWt Y 0 (Y.q.left ⁻¹ᵁ V) f → ∑ a, constFn Y.H.hom _ (e a) * dd a _ f = 0) → ∃ ℓ : Q.X →+ R, ∀ (α : Q.X) (V : Q.P.A.left.Opens) f, IsWt Y α (Y.q.left ⁻¹ᵁ V) f → ∑ a, constFn Y.H.hom _ (e a) * dd a _ f = constFn Y.H.hom _ (ℓ α) * f := by
  intro R _ _ Q O _ _ _ oa Y n v dd hd e he
  obtain ⟨u, hb, hu⟩ := exists_isLieBasis v
  have hc : IsLieComb e u (GlobalTheory.SqZero.lieExp u (fun a => (TrivSqZeroExt.inr (e a) : DualNumber R)) (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _)) := (GlobalTheory.SqZero.isLieComb_iff_lieExp e _).2 rfl
  have ht := GlobalTheory.Reg.isTangent_of_isLieComb hb.1 hc
  have hq : GlobalTheory.SqZero.lieExp u (fun a => (TrivSqZeroExt.inr (e a) : DualNumber R)) (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _) ≫ Y.q = 1 :=
    Over.OverMorphism.ext (GlobalTheory.T.spec_hom_ext_of_localization_at_primes _ _ _ _ fun P _ => GlobalTheory.T.tangent_killing_weight_zero_maps_to_abelianPart_unit R Q O oa Y n (fun a => v a) u hb.1 hu dd hd e he _ _)
  obtain ⟨ℓ, hℓ⟩ := GlobalTheory.T.exists_torus_tangent_of_raynaud_tangent_over_unit R Q O oa Y _ ht hq
  refine ⟨ℓ, fun α V f hf => ?_⟩
  show combF Y.H.hom dd e _ f = _
  refine sub_eq_zero.1 (Adjust.eq_zero_of_valR_points _ _ fun S _ g hg => ?_)
  obtain ⟨φ', hφ'⟩ := Spec.map_surjective (R := CommRingCat.of R) (S := CommRingCat.of S) (g ≫ Y.H.hom)
  let φ : R →+* S := φ'.hom
  have hφ : g ≫ Y.H.hom = spMap φ := hφ'.symm
  letI : Algebra R S := φ.toAlgebra
  let z : sp (R₀ := R) S ⟶ Y.H := Over.homMk g hφ
  let ψ : DualNumber R →ₐ[R] DualNumber S := GlobalTheory.SqZero.dualMap (Algebra.ofId R S)
  have hψ : ∀ a : R, ψ (inr a) = inr (φ a) := fun a => GlobalTheory.SqZero.dualMap_inr _ _
  obtain ⟨a₁, a₂⟩ := valR_spMap (GlobalTheory.SqZero.inlS R S).toRingHom g _ hg
  obtain ⟨b₁, b₂⟩ := valR_prod hu hb.1 hd (fun i => ψ (inr (e i)))
    (fun _ _ => by rw [← map_mul, TrivSqZeroExt.inr_mul_inr, map_zero]) (ReciprocityTheory.ChartRestriction.G.Chart.spMap (GlobalTheory.SqZero.inlS R S) ≫ z) _ a₁ Finset.univ
  have E0 := congrArg (ReciprocityTheory.ChartRestriction.G.Chart.spMap ψ ≫ ·) hℓ.symm
  simp only [GlobalTheory.SqZero.comp_lieExp, ← Category.assoc] at E0
  rw [GlobalTheory.SqZero.lieExp] at E0
  rw [← E0] at b₁ b₂
  have k := valR_torus_mul Y (S := DualNumber S) (φ := algebraMap R (DualNumber S)) (ReciprocityTheory.ChartRestriction.G.Chart.spMap ψ ≫ torTan ℓ) _
    (coord_torTan ℓ ψ) (ReciprocityTheory.ChartRestriction.G.Chart.spMap (GlobalTheory.SqZero.inlS R S) ≫ z) hf a₁ b₁
  have a₃ : ∀ s, valR (A := DualNumber S) (ReciprocityTheory.ChartRestriction.G.Chart.spMap (GlobalTheory.SqZero.inlS R S) ≫ z).left (Y.q.left ⁻¹ᵁ V) s = inl (valR g _ s) := a₂
  have k' := congrArg TrivSqZeroExt.snd ((b₂ f).symm.trans k)
  have hu' : ((Units.map ψ.toRingHom.toMonoidHom (epsUnit (ℓ α)) : (DualNumber S)ˣ) : DualNumber S) = 1 + inr (φ (ℓ α)) := by
    rw [← hψ, ← map_one ψ, ← map_add (f := _)]; rfl
  simp only [a₃, hψ, hu'] at k'
  set_option synthInstance.maxHeartbeats 100000 in
    rw [WtAlg.valR_sub' _ _ hg, WtAlg.valR_mul'' _ _ hg, Adjust.valR_const _ φ g hφ _ hg, combF,
    GlobalTheory.ZH.CrdCalc.valR_eq _ _ hg, map_sum, sub_eq_zero]
  simp only [← GlobalTheory.ZH.CrdCalc.valR_eq _ _ hg, WtAlg.valR_mul'' _ _ hg, Adjust.valR_const _ φ g hφ _ hg]
  simpa [TrivSqZeroExt.snd_sum, _root_.mul_comm] using k'

end GlobalTheory.HeatMod.TorUniq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAddHomInvariantFieldKillsWeightZeroStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_addHom_invariantField_kills_weightZero : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ e : Fin n → R, (∀ (V : Q.P.A.left.Opens) f, IsWt Y 0 (Y.q.left ⁻¹ᵁ V) f → ∑ a, constFn Y.H.hom _ (e a) * dd a _ f = 0) → ∃ ℓ : Q.X →+ R, ∀ (α : Q.X) (V : Q.P.A.left.Opens) f, IsWt Y α (Y.q.left ⁻¹ᵁ V) f → ∑ a, constFn Y.H.hom _ (e a) * dd a _ f = constFn Y.H.hom _ (ℓ α) * f := by
  first | exact @GlobalTheory.HeatMod.TorUniq.exists_addHom_of_kills_wt_zero | exact GlobalTheory.HeatMod.TorUniq.exists_addHom_of_kills_wt_zero | (intros; apply GlobalTheory.HeatMod.TorUniq.exists_addHom_of_kills_wt_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorFourierTermValuesEqOfLocalIdentity
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorsRelatedFourierTermImages
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorsRelatedFourierTermImages
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.HeatUniq.FourierChart

open GlobalTheory.KS GlobalTheory.Heat.Glue

theorem images_eq : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (dd : Fin n → Fld Y.H.left) (D : R → R), (∀ a, IsField ⊤ (dd a)) → ∀ (h h' : Heat Y.H Y.q.left Q.P.L dd D), IsBasic Y h → IsBasic Y h' → ∀ (k : ℕ) (α : Q.X) (C : R), (∀ (i : h.J) (i' : h'.J) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ h.W i ⊓ h'.W i' → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V) f → op Y.H dd h.Θ h.u (h.d i) (h.p i) (h.p' i) k (Y.q.left ⁻¹ᵁ V) (pbT Y.q.left (Q.P.L.g (h.j i) (h'.j i')).val (Y.q.left ⁻¹ᵁ V) ^ k * f) = pbT Y.q.left (Q.P.L.g (h.j i) (h'.j i')).val (Y.q.left ⁻¹ᵁ V) ^ k * (op Y.H dd h'.Θ h'.u (h'.d i') (h'.p i') (h'.p' i') k (Y.q.left ⁻¹ᵁ V) f + constFn Y.H.hom _ C * f)) → ∀ (τ₁ τ₁' τ₂ τ₂'' : SecM Y.q.left Q.P.L k), (∀ (y : Y.H.left) J, Good Q.P.L y J → sval τ₁ (𝟙 Y.H.left) y J = sval τ₂ (𝟙 Y.H.left) y J) → (∀ (j : Q.P.L.ι) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ Y.q.left ⁻¹ᵁ Q.P.L.U j → IsWt Y α (Y.q.left ⁻¹ᵁ V) (rsT (τ₂.f fun _ => j) (Y.q.left ⁻¹ᵁ V))) → h.Acts k τ₁ τ₁' → h'.Acts k τ₂ τ₂'' → ∀ (y : Y.H.left) J, Good Q.P.L y J → sval τ₁' (𝟙 Y.H.left) y J = sval τ₂'' (𝟙 Y.H.left) y J + gs (𝟙 _) y ⊤ (scal Y.H.hom C) * sval τ₂ (𝟙 Y.H.left) y J := by
  intro R _ _ Q Oa _ _ _ oa Y n dd D hdd h h' hb hb' k α C hloc τ₁ τ₁' τ₂ τ₂'' hgerm hwt hA hA'
  have hL : Q.P.L.IsLB := Q.P.isLB

  have e1 : ∀ c : Fin 1 → Q.P.L.ι, τ₁.f c = τ₂.f c := by
    intro c
    refine fn_ext fun x hx => ?_
    obtain ⟨J, hJ, hJc⟩ := exists_good Q.P.L hL x (fun _ : Fin 1 => 𝟙 Y.H.left ≫ Y.q.left) c
      (fun a b _ => by rw [Subsingleton.elim a b]) (fun k => by
        simpa using Set.mem_iInter.1 hx k)
    have := hgerm x J hJ
    rwa [sval_of τ₁ (𝟙 _) x J c hJc, sval_of τ₂ (𝟙 _) x J c hJc] at this

  have loc : ∀ (hh : Heat Y.H Y.q.left Q.P.L dd D) (i : hh.J) (O : Y.H.left.Opens) (hO : O ≤ hh.W i)
      (f : Γ(Y.H.left, hh.W i)),
      rsT (op Y.H dd hh.Θ hh.u (hh.d i) (hh.p i) (hh.p' i) k (hh.W i) f) O =
        op Y.H dd hh.Θ hh.u (hh.d i) (hh.p i) (hh.p' i) k O (rsT f O) := by
    intro hh i O hO f
    have hd : ∀ g, resG Y.H.left hO (hh.d i (hh.W i) g) = hh.d i O (resG Y.H.left hO g) :=
      fun g => ((hh.lift i).1.2.2 (hh.W i) O hO le_rfl g).symm
    have hdd' : ∀ a g, resG Y.H.left hO (dd a (hh.W i) g) = dd a O (resG Y.H.left hO g) :=
      fun a g => ((hdd a).2.2 (hh.W i) O hO le_top g).symm
    have hc : ∀ r, resG Y.H.left hO (constFn Y.H.hom (hh.W i) r) = constFn Y.H.hom O r :=
      fun r => (rsT_of_le hO _).symm.trans (rsT_constFn Y.H.hom hO r)
    have hp : ∀ p : Γ(Y.H.left, hh.W i), resG Y.H.left hO (rsT p (hh.W i)) = rsT p O := fun p => by
      rw [← rsT_of_le hO, rsT_rsT le_rfl hO]
    rw [rsT_of_le hO, rsT_of_le hO]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Heat.op, map_add (f := _), map_sub, map_mul, map_sum, map_pow, map_natCast, map_ofNat, hd, hdd', hc, hp]

  have actO : ∀ (hh : Heat Y.H Y.q.left Q.P.L dd D) (τ τ' : SecM Y.q.left Q.P.L k), hh.Acts k τ τ' →
      ∀ (i : hh.J) (O : Y.H.left.Opens), O ≤ hh.W i →
      rsT (τ'.f fun _ => hh.j i) O =
        op Y.H dd hh.Θ hh.u (hh.d i) (hh.p i) (hh.p' i) k O (rsT (τ.f fun _ => hh.j i) O) := by
    intro hh τ τ' hAc i O hO
    have hW : hh.W i ≤ (LB.LinComb Q.P.L (K := Fin 1) (fun _ => Y.q.left) fun _ => (k : ℤ)).U (fun _ => hh.j i) := le_wchart _ (hh.le i)
    rw [← rsT_rsT hW hO (τ'.f _), hAc i, loc hh i O hO, rsT_rsT hW hO]

  have chart : ∀ (i : h.J) (i' : h'.J), ∃ O : Y.H.left.Opens, O = h.W i ⊓ h'.W i' ∧
      rsT (τ₁'.f fun _ => h'.j i') O =
        rsT (τ₂''.f fun _ => h'.j i') O + constFn Y.H.hom O C * rsT (τ₂.f fun _ => h'.j i') O := by
    intro i i'
    obtain ⟨V, hV⟩ := (hb i).1
    obtain ⟨V', hV'⟩ := (hb' i').1
    have hO : Y.q.left ⁻¹ᵁ (V ⊓ V') = h.W i ⊓ h'.W i' := by rw [hV, hV']; rfl
    refine ⟨Y.q.left ⁻¹ᵁ (V ⊓ V'), hO, ?_⟩
    have hO1 : Y.q.left ⁻¹ᵁ (V ⊓ V') ≤ h.W i := hO.le.trans inf_le_left
    have hO2 : Y.q.left ⁻¹ᵁ (V ⊓ V') ≤ h'.W i' := hO.le.trans inf_le_right
    have hOc : Y.q.left ⁻¹ᵁ (V ⊓ V') ≤ LB.wchart Q.P.L (fun _ : Fin 1 => Y.q.left) (fun _ => h.j i) ⊓
        LB.wchart Q.P.L (fun _ : Fin 1 => Y.q.left) (fun _ => h'.j i') :=
      le_inf (hO1.trans (le_wchart _ (h.le i))) (hO2.trans (le_wchart _ (h'.le i')))
    have hOU : Y.q.left ⁻¹ᵁ (V ⊓ V') ≤ Y.q.left ⁻¹ᵁ (Q.P.L.U (h.j i) ⊓ Q.P.L.U (h'.j i')) :=
      fun y hy => ⟨h.le i (hO1 hy), h'.le i' (hO2 hy)⟩
    have hunit : pbT Y.q.left (Q.P.L.g (h.j i) (h'.j i')).val (Y.q.left ⁻¹ᵁ (V ⊓ V')) *
        pbT Y.q.left (Q.P.L.g (h.j i) (h'.j i'))⁻¹.val (Y.q.left ⁻¹ᵁ (V ⊓ V')) = 1 := by
      rw [← pbT_mul, Units.mul_inv, pbT_one _ hOU]
    have hw := hwt (h'.j i') (V ⊓ V') (hO2.trans (h'.le i'))
    have key := hloc i i' (V ⊓ V') hO.le _ hw
    have s1 := sec_rel Y.q.left k τ₁ (fun _ => h.j i) (fun _ => h'.j i') hOc
    have s1' := sec_rel Y.q.left k τ₁' (fun _ => h.j i) (fun _ => h'.j i') hOc
    have a1 := actO h τ₁ τ₁' hA i _ hO1
    have a2 := actO h' τ₂ τ₂'' hA' i' _ hO2
    beta_reduce at s1 s1'
    rw [e1, e1] at s1
    rw [e1, s1, key, ← a2, s1'] at a1
    have hu : IsUnit (pbT Y.q.left (Q.P.L.g (h.j i) (h'.j i')).val (Y.q.left ⁻¹ᵁ (V ⊓ V')) ^ k) :=
      (show IsUnit _ from ⟨⟨_, _, hunit, by rw [mul_comm]; exact hunit⟩, rfl⟩).pow k
    exact hu.mul_left_cancel a1

  intro y J hJ
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (show y ∈ ⨆ i, h.W i by rw [h.cover]; trivial)
  obtain ⟨i', hi'⟩ := TopologicalSpace.Opens.mem_iSup.1 (show y ∈ ⨆ i, h'.W i by rw [h'.cover]; trivial)
  obtain ⟨O, hOeq, hid⟩ := chart i i'
  have hyO : y ∈ O := hOeq ▸ ⟨hi, hi'⟩
  have hOc : O ≤ LB.wchart Q.P.L (fun _ : Fin 1 => Y.q.left) (fun _ => h'.j i') :=
    hOeq ▸ (inf_le_right.trans (le_wchart _ (h'.le i')))
  have hyJ := hJ.mem (fun _ : Fin 1 => Y.q.left) (𝟙 Y.H.left)
  have hyj' : (𝟙 Y.H.left) y ∈ LB.wchart Q.P.L (fun _ : Fin 1 => Y.q.left) (fun _ => h'.j i') := hOc hyO
  have tr : ∀ τ : SecM Y.q.left Q.P.L k, sval τ (𝟙 Y.H.left) y J =
      (trF (fun _ : Fin 1 => Y.q.left) (fun _ => (k : ℤ)) (𝟙 Y.H.left) y
        (fun _ => J (𝟙 Y.H.left ≫ Y.q.left)) (fun _ => h'.j i')).val *
        gs (𝟙 Y.H.left) y O (rsT (τ.f fun _ => h'.j i') O) := by
    intro τ
    refine (sec_trans τ (𝟙 Y.H.left) y hyJ hyj').trans (congrArg _ ?_)
    rw [rsT_of_le (show O ≤ (LB.LinComb Q.P.L (K := Fin 1) (fun _ => Y.q.left) fun _ => (k : ℤ)).U (fun _ => h'.j i') from hOc)]
    exact (gs_res (𝟙 Y.H.left) y hOc hyO _).symm
  have hc : gs (𝟙 Y.H.left) y O (constFn Y.H.hom O C) = gs (𝟙 _) y ⊤ (scal Y.H.hom C) := by
    rw [gs_constFn Y.H.hom O (𝟙 Y.H.left) y hyO C, Category.id_comp, cst, gs_eq Y.H.hom y ⊤ trivial]
    exact (gs_eq (𝟙 _) y ⊤ trivial _).symm
  rw [tr τ₁', tr τ₂'', tr τ₂, hid, gs_add _ _ _ hyO, gs_mul _ _ _ hyO, hc]
  ring

end GlobalTheory.HeatUniq.FourierChart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorsRelatedFourierTermImagesStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heatOperators_related_fourierTerm_images : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (dd : Fin n → Fld Y.H.left) (D : R → R), (∀ a, IsField ⊤ (dd a)) → ∀ (h h' : Heat Y.H Y.q.left Q.P.L dd D), IsBasic Y h → IsBasic Y h' → ∀ (k : ℕ) (α : Q.X) (C : R), (∀ (i : h.J) (i' : h'.J) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ h.W i ⊓ h'.W i' → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V) f → op Y.H dd h.Θ h.u (h.d i) (h.p i) (h.p' i) k (Y.q.left ⁻¹ᵁ V) (pbT Y.q.left (Q.P.L.g (h.j i) (h'.j i')).val (Y.q.left ⁻¹ᵁ V) ^ k * f) = pbT Y.q.left (Q.P.L.g (h.j i) (h'.j i')).val (Y.q.left ⁻¹ᵁ V) ^ k * (op Y.H dd h'.Θ h'.u (h'.d i') (h'.p i') (h'.p' i') k (Y.q.left ⁻¹ᵁ V) f + constFn Y.H.hom _ C * f)) → ∀ (τ₁ τ₁' τ₂ τ₂'' : SecM Y.q.left Q.P.L k), (∀ (y : Y.H.left) J, Good Q.P.L y J → sval τ₁ (𝟙 Y.H.left) y J = sval τ₂ (𝟙 Y.H.left) y J) → (∀ (j : Q.P.L.ι) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ Y.q.left ⁻¹ᵁ Q.P.L.U j → IsWt Y α (Y.q.left ⁻¹ᵁ V) (rsT (τ₂.f fun _ => j) (Y.q.left ⁻¹ᵁ V))) → h.Acts k τ₁ τ₁' → h'.Acts k τ₂ τ₂'' → ∀ (y : Y.H.left) J, Good Q.P.L y J → sval τ₁' (𝟙 Y.H.left) y J = sval τ₂'' (𝟙 Y.H.left) y J + gs (𝟙 _) y ⊤ (scal Y.H.hom C) * sval τ₂ (𝟙 Y.H.left) y J := by
  first | exact @GlobalTheory.HeatUniq.FourierChart.images_eq | exact GlobalTheory.HeatUniq.FourierChart.images_eq | (intros; apply GlobalTheory.HeatUniq.FourierChart.images_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudFourierTermLocalFunctionIsWeight
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudFourierTermLocalFunctionIsWeight
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Heat

theorem isWt_rsT_of_isTerm : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (k : ℕ) (α : Q.X) (σ : Q.SecB k α) (τ : SecM Y.q.left Q.P.L k), IsTerm Y k α σ τ → ∀ (j : Q.P.L.ι) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ Y.q.left ⁻¹ᵁ Q.P.L.U j → IsWt Y α (Y.q.left ⁻¹ᵁ V) (rsT (τ.f fun _ => j) (Y.q.left ⁻¹ᵁ V)) := by
  intro R _ _ Q O _ _ _ oa Y k α σ τ hT j V hVj S _ φ x x' c a a' ha ha' hV hV' hq hc
  subst ha ha'
  have hle : Y.q.left ⁻¹ᵁ V ≤ (LB.LinComb Q.P.L (K := Fin 1) (fun _ => Y.q.left) fun _ => (k : ℤ)).U fun _ => j :=
    fun z hz => Set.mem_iInter.2 fun _ => hVj hz
  have hql : x'.left ≫ Y.q.left = x.left ≫ Y.q.left := by
    have := congrArg CommaMorphism.left hq
    simpa using this

  have key : ((x'.left.appLE (Y.q.left ⁻¹ᵁ V) ⊤ hV').hom (rsT (τ.f fun _ => j) (Y.q.left ⁻¹ᵁ V))) =
      (show Γ((Over.mk (spMap φ)).left, ⊤) from (unitOn (c α)).val) * (x.left.appLE (Y.q.left ⁻¹ᵁ V) ⊤ hV).hom (rsT (τ.f fun _ => j) (Y.q.left ⁻¹ᵁ V)) := by
    refine fn_ext fun y _ => ?_
    have hy : x.left y ∈ Y.q.left ⁻¹ᵁ V := hV trivial
    have hy' : x'.left y ∈ Y.q.left ⁻¹ᵁ V := hV' trivial
    obtain ⟨J, hJ, eJ⟩ := exists_good Q.P.L Q.P.isLB y (fun _ : Unit => x.left ≫ Y.q.left) (fun _ => j)
      (fun _ _ _ => rfl) (fun _ => hVj hy)
    have e := hT _ x' y J hJ
    have e0 := hT _ x y J hJ
    rw [hq, hc α y J hJ] at e
    rw [gs_mul (𝟙 _) y ⊤ trivial, gs_unit (𝟙 _) y ⊤ trivial, gs_appLE _ _ ⊤ _ (𝟙 _) y trivial,
      gs_appLE _ _ ⊤ _ (𝟙 _) y trivial, Category.id_comp, Category.id_comp]
    simp only [rsT, dif_pos hle]
    erw [gs_res _ y hle hy, gs_res _ y hle hy']
    have e1 := sval_of τ x'.left y J (fun _ => j) (fun _ => (congrArg J hql).trans (eJ ()))
    have e2 := sval_of τ x.left y J (fun _ => j) (fun _ => eJ ())
    rw [e1] at e
    rw [e2] at e0
    refine e.trans ?_
    refine Eq.trans ?_ (congrArg (fun t => _ * t) e0.symm)
    simp only [Units.val_mul]
    ring
  unfold valR
  rw [dif_pos hV, dif_pos hV', key, map_mul]
  congr 1
  simp [unitOn]

end GlobalTheory.Heat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudFourierTermLocalFunctionIsWeightStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.raynaudFourierTerm_localFunction_isWeight : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (k : ℕ) (α : Q.X) (σ : Q.SecB k α) (τ : SecM Y.q.left Q.P.L k), IsTerm Y k α σ τ → ∀ (j : Q.P.L.ι) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ Y.q.left ⁻¹ᵁ Q.P.L.U j → IsWt Y α (Y.q.left ⁻¹ᵁ V) (rsT (τ.f fun _ => j) (Y.q.left ⁻¹ᵁ V)) := by
  first | exact @GlobalTheory.Heat.isWt_rsT_of_isTerm | exact GlobalTheory.Heat.isWt_rsT_of_isTerm | (intros; apply GlobalTheory.Heat.isWt_rsT_of_isTerm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudProjectionSectionValuesIdentity
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudProjectionSectionValuesIdentity
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FourierDescent

theorem cst_eq_gs_scal {R : Type} [CommRing R] {Z : Scheme.{0}} (p : Z ⟶ Sp R) (z : Z) (C : R) :
    cst p z C = gs (𝟙 _) z ⊤ (scal p C) := by
  have h := gs_pull (𝟙 Z) p z ⊤ trivial ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom C)
  rw [Category.id_comp] at h
  exact h.symm

theorem values_identity : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (k : ℕ) (α : Q.X) (σ σ' σ'' : Q.SecB k α) (C : R), (∀ (y : Y.H.left) J, Good Q.P.L y J → sval σ' Y.q.left y J = sval σ'' Y.q.left y J + gs (𝟙 _) y ⊤ (scal Y.H.hom C) * sval σ Y.q.left y J) → ∀ (T : Over (Sp R)) (x : T ⟶ Q.P.A) z J, Good Q.P.L z J → sval σ' x.left z J = sval σ'' x.left z J + gs (𝟙 _) z ⊤ (scal T.hom C) * sval σ x.left z J := by
  intro R _ _ Q O _ _ _ oa Y k α σ σ' σ'' C hyp T x z J hJ
  classical
  have hL := Q.P.isLB
  have : Smooth Y.q.left := GlobalTheory.RayEv.Ray.smooth_q Y
  have : Surjective Y.q.left := (GlobalTheory.RayEv.Ray.surjective_quasiCompact_q Y).1
  have key : ∀ j : Fin 4 → Q.P.L.ι, σ'.f j =
      σ''.f j + constFn Q.P.A.hom ((LB.LinComb Q.P.L (DegPre.famφB Q α) (DegPre.famε k)).U j) C * σ.f j := by
    intro j
    apply GlobalTheory.EigenDescent.app_injective_of_flat_surjective Y.q.left
    apply fn_ext
    intro y hy
    rw [gs_pull (𝟙 _) Y.q.left y _ hy, gs_pull (𝟙 _) Y.q.left y _ hy, Category.id_comp]
    obtain ⟨J', hJ'⟩ : ∃ J', Good Q.P.L y J' :=
      ⟨fun ψ => (exists_chart hL (ψ y)).choose, fun ψ => (exists_chart hL (ψ y)).choose_spec⟩
    have h := hyp y J' hJ'
    have hm := hJ'.mem (DegPre.famφB Q α) Y.q.left
    rw [gs_add _ _ _ hy, gs_mul _ _ _ hy, gs_constFn _ _ _ _ hy]
    erw [sec_trans σ' _ y hy hm, sec_trans σ'' _ y hy hm, sec_trans σ _ y hy hm]
    rw [Over.w Y.q, cst_eq_gs_scal]
    change _ * sval σ' Y.q.left y J' = _ * sval σ'' Y.q.left y J' + _ * (_ * sval σ Y.q.left y J')
    rw [h]
    ring
  have hm := hJ.mem (DegPre.famφB Q α) x.left
  change gs x.left z _ (σ'.f _) = gs x.left z _ (σ''.f _) + _ * gs x.left z _ (σ.f _)
  rw [key]
  erw [gs_add _ _ _ hm, gs_mul _ _ _ hm, gs_constFn _ _ _ _ hm]
  rw [Over.w x, cst_eq_gs_scal]
  rfl

end GlobalTheory.FourierDescent
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudProjectionSectionValuesIdentityStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.raynaudProjection_sectionValues_identity : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (k : ℕ) (α : Q.X) (σ σ' σ'' : Q.SecB k α) (C : R), (∀ (y : Y.H.left) J, Good Q.P.L y J → sval σ' Y.q.left y J = sval σ'' Y.q.left y J + gs (𝟙 _) y ⊤ (scal Y.H.hom C) * sval σ Y.q.left y J) → ∀ (T : Over (Sp R)) (x : T ⟶ Q.P.A) z J, Good Q.P.L z J → sval σ' x.left z J = sval σ'' x.left z J + gs (𝟙 _) z ⊤ (scal T.hom C) * sval σ x.left z J := by
  first | exact @GlobalTheory.FourierDescent.values_identity | exact GlobalTheory.FourierDescent.values_identity | (intros; apply GlobalTheory.FourierDescent.values_identity <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorFourierTermValuesEqOfLocalIdentity
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Heat

theorem sval_eq_of_localIdentity : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (h h' : Heat Y.H Y.q.left Q.P.L dd ⇑D), IsBasic Y h → IsBasic Y h' → ∀ c : ℕ → Q.X → R, (∀ (i : h.J) (i' : h'.J) (k : ℕ) (α : Q.X) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ h.W i ⊓ h'.W i' → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V) f → op Y.H dd h.Θ h.u (h.d i) (h.p i) (h.p' i) k (Y.q.left ⁻¹ᵁ V) (pbT Y.q.left (Q.P.L.g (h.j i) (h'.j i')).val (Y.q.left ⁻¹ᵁ V) ^ k * f) = pbT Y.q.left (Q.P.L.g (h.j i) (h'.j i')).val (Y.q.left ⁻¹ᵁ V) ^ k * (op Y.H dd h'.Θ h'.u (h'.d i') (h'.p i') (h'.p' i') k (Y.q.left ⁻¹ᵁ V) f + constFn Y.H.hom _ (c k α) * f)) → ∀ (k : ℕ) (α : Q.X) (σ σ' σ'' : Q.SecB k α), TActs Y h k α σ σ' → TActs Y h' k α σ σ'' → ∀ (T : Over (Sp R)) (x : T ⟶ Q.P.A) z J, Good Q.P.L z J → sval σ' x.left z J = sval σ'' x.left z J + gs (𝟙 _) z ⊤ (scal T.hom (c k α)) * sval σ x.left z J := by
  intro R _ _ Q O _ _ _ oa Y n v dd hv D h h' hb hb' c hc k α σ σ' σ'' ⟨τ₁, τ₁', t1, t1', a1⟩ ⟨τ₂, τ₂'', t2, t2'', a2⟩ T x z J hJ
  refine GlobalTheory.T.raynaudProjection_sectionValues_identity R Q O oa Y k α σ σ' σ'' (c k α) ?_ T x z J hJ
  intro y J' hJ'
  have e : ∀ (s : Q.SecB k α) (τ : SecM Y.q.left Q.P.L k), IsTerm Y k α s τ →
      sval τ (𝟙 Y.H.left) y J' = sval s Y.q.left y J' * (val ((Y.Φ Y.H (𝟙 _)).s α) (𝟙 _) y J').val := by
    intro s τ hτ
    have := hτ Y.H (𝟙 _) y J' hJ'
    simpa only [Over.id_left, Category.id_comp] using this
  have key := GlobalTheory.T.heatOperators_related_fourierTerm_images R Q O oa Y n dd D (fun a => (hv a).1) h h' hb hb' k α (c k α) (fun i i' => hc i i' k α) τ₁ τ₁' τ₂ τ₂''
    (fun y J hJ => by
      have a := t1 Y.H (𝟙 _) y J hJ
      have b := t2 Y.H (𝟙 _) y J hJ
      simp only [Over.id_left, Category.id_comp] at a b
      rw [a, b])
    (GlobalTheory.T.raynaudFourierTerm_localFunction_isWeight R Q O oa Y k α σ τ₂ t2) a1 a2 y J' hJ'
  rw [e σ' τ₁' t1', e σ'' τ₂'' t2'', e σ τ₂ t2] at key
  set u := val ((Y.Φ Y.H (𝟙 _)).s α) (𝟙 _) y J'
  have : (sval σ' Y.q.left y J' - (sval σ'' Y.q.left y J' + gs (𝟙 _) y ⊤ (scal Y.H.hom (c k α)) * sval σ Y.q.left y J')) * u.val = 0 := by
    rw [sub_mul, key]; ring
  have h0 := congrArg (· * (u⁻¹ : (Y.H.left.presheaf.stalk y)ˣ).val) this
  simp only [Units.mul_inv_cancel_right, zero_mul] at h0
  exact sub_eq_zero.1 h0

end GlobalTheory.Heat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorFourierTermValuesEqOfLocalIdentityStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heat_operator_fourier_term_values_eq_of_local_identity : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (h h' : Heat Y.H Y.q.left Q.P.L dd ⇑D), IsBasic Y h → IsBasic Y h' → ∀ c : ℕ → Q.X → R, (∀ (i : h.J) (i' : h'.J) (k : ℕ) (α : Q.X) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ h.W i ⊓ h'.W i' → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V) f → op Y.H dd h.Θ h.u (h.d i) (h.p i) (h.p' i) k (Y.q.left ⁻¹ᵁ V) (pbT Y.q.left (Q.P.L.g (h.j i) (h'.j i')).val (Y.q.left ⁻¹ᵁ V) ^ k * f) = pbT Y.q.left (Q.P.L.g (h.j i) (h'.j i')).val (Y.q.left ⁻¹ᵁ V) ^ k * (op Y.H dd h'.Θ h'.u (h'.d i') (h'.p i') (h'.p' i') k (Y.q.left ⁻¹ᵁ V) f + constFn Y.H.hom _ (c k α) * f)) → ∀ (k : ℕ) (α : Q.X) (σ σ' σ'' : Q.SecB k α), TActs Y h k α σ σ' → TActs Y h' k α σ σ'' → ∀ (T : Over (Sp R)) (x : T ⟶ Q.P.A) z J, Good Q.P.L z J → sval σ' x.left z J = sval σ'' x.left z J + gs (𝟙 _) z ⊤ (scal T.hom (c k α)) * sval σ x.left z J := by
  first | exact @GlobalTheory.Heat.sval_eq_of_localIdentity | exact GlobalTheory.Heat.sval_eq_of_localIdentity | (intros; apply GlobalTheory.Heat.sval_eq_of_localIdentity <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorConjUnitPowCorrections
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorConjUnitPowCorrections
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatConj

section Ring

variable {A : Type} [CommRing A] (δ : A → A)
  (hadd : ∀ x y, δ (x + y) = δ x + δ y) (hmul : ∀ x y, δ (x * y) = x * δ y + y * δ x)
include hadd hmul

theorem der_natCast (k : ℕ) : δ (k : A) = 0 := by
  have h0 : δ 0 = 0 := by
    have := hadd 0 0
    simp only [add_zero] at this
    linear_combination -this
  have h1 : δ 1 = 0 := by
    have := hmul 1 1
    rw [_root_.one_mul] at this
    linear_combination -this
  induction k with
  | zero => simpa using h0
  | succ k ih => rw [Nat.cast_succ, hadd, ih, h1, add_zero]

theorem der_pow (g g' : A) (hg : g * g' = 1) (k : ℕ) : δ (g ^ k) = (k : A) * g ^ k * (δ g * g') := by
  induction k with
  | zero =>
    have := hmul 1 1
    rw [_root_.one_mul] at this
    simp only [pow_zero, Nat.cast_zero, zero_mul]
    linear_combination -this
  | succ k ih =>
    rw [pow_succ, hmul, ih]
    push_cast
    linear_combination -(δ g * g ^ k) * hg

theorem der_pow_mul (g g' : A) (hg : g * g' = 1) (k : ℕ) (f : A) :
    δ (g ^ k * f) = g ^ k * (δ f + (k : A) * (δ g * g') * f) := by
  rw [hmul, der_pow δ hadd hmul g g' hg]
  ring

theorem der_natCast_mul (k : ℕ) (x : A) : δ ((k : A) * x) = (k : A) * δ x := by
  rw [hmul, der_natCast δ hadd hmul]
  ring

end Ring

end GlobalTheory.HeatConj

namespace GlobalTheory.HeatConj

theorem op_pow_mul : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (n : ℕ) (dd : Fin n → Fld G.left) (Θ : Matrix (Fin n) (Fin n) R), Θᵀ = Θ → ∀ (u : Fin n → R) (d : Fld G.left) (W₀ Wp Wo : G.left.Opens) (p p' : Γ(G.left, Wp)) (k : ℕ) (g g' : Γ(G.left, Wo)), g * g' = 1 → Wo ≤ W₀ → IsField W₀ d → (∀ a, IsField W₀ (dd a)) → ∀ f, op G dd Θ u d p p' k Wo (g ^ k * f) = g ^ k * (op G dd Θ u d p p' k Wo f - 2 * (k : Γ(G.left, Wo)) * ∑ a, ∑ b, constFn G.hom Wo (Θ a b) * (dd b Wo g * g') * dd a Wo f + ((k : Γ(G.left, Wo)) ^ 2 * (2 * (d Wo g * g') - ∑ a, ∑ b, constFn G.hom Wo (Θ a b) * (dd a Wo g * g') * (dd b Wo g * g')) + (k : Γ(G.left, Wo)) * (2 * ∑ a, constFn G.hom Wo (u a) * (dd a Wo g * g') - ∑ a, ∑ b, constFn G.hom Wo (Θ a b) * dd a Wo (dd b Wo g * g'))) * f) := by
  intro R _ G _ _ n dd Θ hΘ u d W₀ Wp Wo p p' k g g' hg hWo hd hdd f
  have E3 := der_pow_mul (d Wo) (hd.1 Wo hWo) (hd.2.1 Wo hWo) g g' hg k f
  have E2 : ∀ a, dd a Wo (g ^ k * f) = g ^ k * (dd a Wo f + (k : Γ(G.left, Wo)) * (dd a Wo g * g') * f) :=
    fun a => der_pow_mul (dd a Wo) ((hdd a).1 Wo hWo) ((hdd a).2.1 Wo hWo) g g' hg k f
  have E1 : ∀ a b, dd a Wo (dd b Wo (g ^ k * f)) = g ^ k * (dd a Wo (dd b Wo f) +
      (k : Γ(G.left, Wo)) * (dd b Wo g * g') * dd a Wo f + (k : Γ(G.left, Wo)) * (dd a Wo g * g') * dd b Wo f +
      (k : Γ(G.left, Wo)) * dd a Wo (dd b Wo g * g') * f +
      (k : Γ(G.left, Wo)) ^ 2 * (dd a Wo g * g') * (dd b Wo g * g') * f) := by
    intro a b
    have ha := (hdd a).1 Wo hWo
    have hm := (hdd a).2.1 Wo hWo
    rw [E2 b, der_pow_mul (dd a Wo) ha hm g g' hg k, ha, mul_assoc (k : Γ(G.left, Wo)),
      der_natCast_mul (dd a Wo) ha hm, hm]
    ring
  have hsym : ∑ a, ∑ b, constFn G.hom Wo (Θ a b) * (dd a Wo g * g') * dd b Wo f =
      ∑ a, ∑ b, constFn G.hom Wo (Θ a b) * (dd b Wo g * g') * dd a Wo f := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    have : Θ b a = Θ a b := by
      have := congrFun (congrFun hΘ a) b
      simpa [Matrix.transpose_apply] using this
    rw [this]
  have hS : ∑ a, ∑ b, constFn G.hom Wo (Θ a b) * dd a Wo (dd b Wo (g ^ k * f)) =
      g ^ k * ∑ a, ∑ b, constFn G.hom Wo (Θ a b) * dd a Wo (dd b Wo f) +
      ((k : Γ(G.left, Wo)) * g ^ k) * ∑ a, ∑ b, constFn G.hom Wo (Θ a b) * (dd b Wo g * g') * dd a Wo f +
      ((k : Γ(G.left, Wo)) * g ^ k) * ∑ a, ∑ b, constFn G.hom Wo (Θ a b) * (dd a Wo g * g') * dd b Wo f +
      ((k : Γ(G.left, Wo)) * g ^ k) * (∑ a, ∑ b, constFn G.hom Wo (Θ a b) * dd a Wo (dd b Wo g * g')) * f +
      ((k : Γ(G.left, Wo)) ^ 2 * g ^ k) *
        (∑ a, ∑ b, constFn G.hom Wo (Θ a b) * (dd a Wo g * g') * (dd b Wo g * g')) * f := by
    simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [E1]
    ring
  have hU : ∑ a, constFn G.hom Wo (u a) * dd a Wo (g ^ k * f) =
      g ^ k * ∑ a, constFn G.hom Wo (u a) * dd a Wo f +
      ((k : Γ(G.left, Wo)) * g ^ k) * (∑ a, constFn G.hom Wo (u a) * (dd a Wo g * g')) * f := by
    simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [E2]
    ring
  unfold op
  rw [E3]
  linear_combination -hS + 2 * hU - ((k : Γ(G.left, Wo)) * g ^ k) * hsym

end GlobalTheory.HeatConj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorConjUnitPowCorrectionsStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heatOperator_conj_unitPow_corrections : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (n : ℕ) (dd : Fin n → Fld G.left) (Θ : Matrix (Fin n) (Fin n) R), Θᵀ = Θ → ∀ (u : Fin n → R) (d : Fld G.left) (W₀ Wp Wo : G.left.Opens) (p p' : Γ(G.left, Wp)) (k : ℕ) (g g' : Γ(G.left, Wo)), g * g' = 1 → Wo ≤ W₀ → IsField W₀ d → (∀ a, IsField W₀ (dd a)) → ∀ f, op G dd Θ u d p p' k Wo (g ^ k * f) = g ^ k * (op G dd Θ u d p p' k Wo f - 2 * (k : Γ(G.left, Wo)) * ∑ a, ∑ b, constFn G.hom Wo (Θ a b) * (dd b Wo g * g') * dd a Wo f + ((k : Γ(G.left, Wo)) ^ 2 * (2 * (d Wo g * g') - ∑ a, ∑ b, constFn G.hom Wo (Θ a b) * (dd a Wo g * g') * (dd b Wo g * g')) + (k : Γ(G.left, Wo)) * (2 * ∑ a, constFn G.hom Wo (u a) * (dd a Wo g * g') - ∑ a, ∑ b, constFn G.hom Wo (Θ a b) * dd a Wo (dd b Wo g * g'))) * f) := by
  first | exact @GlobalTheory.HeatConj.op_pow_mul | exact GlobalTheory.HeatConj.op_pow_mul | (intros; apply GlobalTheory.HeatConj.op_pow_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineScalarTorusInvariantHeatOperators
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatUniq

theorem exists_affine_scalar : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [Algebra ℚ R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (h h' : Heat Y.H Y.q.left Q.P.L dd ⇑D), IsBasic Y h → IsBasic Y h' → h.Θ = h'.Θ → h.u = h'.u → ∃ (ℓ : Q.X →+ R) (π π' : R), ∀ (k : ℕ) (α : Q.X) (σ σ' σ'' : Q.SecB k α), TActs Y h k α σ σ' → TActs Y h' k α σ σ'' → ∀ (T : Over (Sp R)) (x : T ⟶ Q.P.A) z J, Good Q.P.L z J → sval σ'' x.left z J = sval σ' x.left z J + gs (𝟙 _) z ⊤ (scal T.hom (2 * (k : R) * ℓ α + 2 * (k : R) ^ 2 * π + 2 * (k : R) * π')) * sval σ x.left z J := by
  intro R _ _ _ _ _ Q O _ _ _ oa Y n v dd hdd D h' h hb' hb hΘ' hu'
  have hΘ : h.Θ = h'.Θ := hΘ'.symm
  have hu : h.u = h'.u := hu'.symm
  obtain ⟨e, π, π', hT, hG⟩ := GlobalTheory.T.torusInvariant_heatOperators_difference_global R Q O oa Y n v dd hdd D h h' hb hb' hΘ hu
  obtain ⟨ℓ, hℓ⟩ := GlobalTheory.T.exists_addHom_invariantField_kills_weightZero R Q O oa Y n v dd hdd e hT
  refine ⟨ℓ, π, π', ?_⟩
  intro k α σ σ'' σ' h1' h1 T x z J hJ
  refine GlobalTheory.T.heat_operator_fourier_term_values_eq_of_local_identity R Q O oa Y n v dd hdd D h h' hb hb'
    (fun k α => 2 * (k : R) * ℓ α + 2 * (k : R) ^ 2 * π + 2 * (k : R) * π') ?_ k α σ σ' σ'' h1 h1' T x z J hJ
  intro i i' k α V hV f hf
  obtain ⟨h2d, h3, h4⟩ := hG i i' _ hV
  simp only [dlg] at h2d h3 h4
  have hle : Y.q.left ⁻¹ᵁ V ≤ Y.q.left ⁻¹ᵁ (Q.P.L.U (h.j i) ⊓ Q.P.L.U (h'.j i')) := fun pt hpt =>
    ⟨h.le i (hV hpt).1, h'.le i' (hV hpt).2⟩
  have hg : pbT Y.q.left (Q.P.L.g (h.j i) (h'.j i')).val (Y.q.left ⁻¹ᵁ V) *
      pbT Y.q.left (Q.P.L.g (h.j i) (h'.j i'))⁻¹.val (Y.q.left ⁻¹ᵁ V) = 1 := by
    unfold pbT
    rw [dite_eq_left hle, dite_eq_left hle, ← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
  have mono : ∀ (δ : Fld Y.H.left) {W₁ W₂ : Y.H.left.Opens}, W₁ ≤ W₂ → IsField W₂ δ → IsField W₁ δ :=
    fun δ W₁ W₂ hle H => ⟨fun W hW => H.1 W (hW.trans hle), fun W hW => H.2.1 W (hW.trans hle),
      fun W W' hh hW => H.2.2 W W' hh (hW.trans hle)⟩
  rw [GlobalTheory.T.heatOperator_conj_unitPow_corrections R Y.H n dd h.Θ h.symm h.u (h.d i) (h.W i) (h.W i) _ (h.p i) (h.p' i) k _ _ hg (hV.trans inf_le_left)
    (h.lift i).1 (fun a => mono _ le_top (hdd a).1) f]
  congr 1
  have hc : constFn Y.H.hom (Y.q.left ⁻¹ᵁ V) (2 * (k : R) * ℓ α + 2 * (k : R) ^ 2 * π + 2 * (k : R) * π') =
      2 * (k : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V)) * constFn Y.H.hom _ (ℓ α) +
        2 * (k : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V)) ^ 2 * constFn Y.H.hom _ π +
        2 * (k : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V)) * constFn Y.H.hom _ π' := by
    simp only [constFn, map_add (f := _), map_mul, map_pow, map_natCast, map_ofNat]
  simp only [hc]
  have hl := hℓ α V f hf
  unfold op
  rw [← hΘ, ← hu]
  linear_combination (2 * (k : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V))) * h2d f + (k : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V)) ^ 2 * f * h3 +
    (k : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V)) * f * h4 + 2 * (k : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V)) * hl

end GlobalTheory.HeatUniq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineScalarTorusInvariantHeatOperatorsStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_scalar_torusInvariant_heatOperators : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [Algebra ℚ R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (h h' : Heat Y.H Y.q.left Q.P.L dd ⇑D), IsBasic Y h → IsBasic Y h' → h.Θ = h'.Θ → h.u = h'.u → ∃ (ℓ : Q.X →+ R) (π π' : R), ∀ (k : ℕ) (α : Q.X) (σ σ' σ'' : Q.SecB k α), TActs Y h k α σ σ' → TActs Y h' k α σ σ'' → ∀ (T : Over (Sp R)) (x : T ⟶ Q.P.A) z J, Good Q.P.L z J → sval σ'' x.left z J = sval σ' x.left z J + gs (𝟙 _) z ⊤ (scal T.hom (2 * (k : R) * ℓ α + 2 * (k : R) ^ 2 * π + 2 * (k : R) * π')) * sval σ x.left z J := by
  first | exact @GlobalTheory.HeatUniq.exists_affine_scalar | exact GlobalTheory.HeatUniq.exists_affine_scalar | (intros; apply GlobalTheory.HeatUniq.exists_affine_scalar <;> assumption)
end
