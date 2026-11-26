module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalChartEqOfSameGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiFiniteTautologicalChartOfSeparation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtaleCompletionOfQuasiFiniteGaloisRigid

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalChartGaloisRigidStalk
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubMemPowOfMemMaximalIdeal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EtUniq

theorem sub_mem_pow_of_mem_maximalIdeal {O W V : Type} [CommRing O] [IsLocalRing O] [CommRing W]
    [IsLocalRing W] [CommRing V] [IsLocalRing V] (φ : O →+* W)
    (hm : (maximalIdeal O).map φ = maximalIdeal W)
    (θ₁ θ₂ : W →+* V) [IsLocalHom θ₂] (hO : θ₁.comp φ = θ₂.comp φ) (k : ℕ)
    (hk : ∀ w, θ₁ w - θ₂ w ∈ maximalIdeal V ^ (k + 1)) :
    ∀ x ∈ maximalIdeal W, θ₁ x - θ₂ x ∈ maximalIdeal V ^ (k + 2) := by
  intro x hx
  rw [← hm] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, -, rfl⟩ := hy
    have := congrArg (fun f => f a) hO
    simp only [RingHom.comp_apply] at this
    rw [this, sub_self]; exact zero_mem _
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add (f := _), map_add (f := _), add_sub_add_comm]; exact add_mem hx hy
  | smul a x hx' hx =>
    have hx'' : x ∈ maximalIdeal W := by rw [← hm]; exact hx'
    have h2 : θ₂ x ∈ maximalIdeal V :=
      (mem_maximalIdeal _).2 fun h => (mem_maximalIdeal _).1 hx'' (isUnit_of_map_unit θ₂ x h)
    simp only [smul_eq_mul, map_mul]
    have e : θ₁ a * θ₁ x - θ₂ a * θ₂ x = θ₁ a * (θ₁ x - θ₂ x) + (θ₁ a - θ₂ a) * θ₂ x := by ring
    rw [e]
    refine add_mem (Ideal.mul_mem_left _ _ hx) ?_
    rw [show k + 2 = (k + 1) + 1 from rfl, pow_succ]
    exact Ideal.mul_mem_mul (hk a) h2

abbrev Gr (V : Type) [CommRing V] [IsLocalRing V] (k : ℕ) : Type :=
  ↥(maximalIdeal V ^ (k + 1)) ⧸ (maximalIdeal V • (⊤ : Submodule V ↥(maximalIdeal V ^ (k + 1))))

noncomputable instance (V : Type) [CommRing V] [IsLocalRing V] (k : ℕ) : Module (ResidueField V) (Gr V k) :=
  inferInstanceAs (Module (V ⧸ maximalIdeal V) (Gr V k))

noncomputable abbrev grModule {W V : Type} [CommRing W] [IsLocalRing W] [CommRing V] [IsLocalRing V]
    (θ : W →+* V) [IsLocalHom θ] (k : ℕ) : Module (ResidueField W) (Gr V k) :=
  Module.compHom _ (ResidueField.map θ)

theorem gr_mk_eq_zero_iff (V : Type) [CommRing V] [IsLocalRing V] (k : ℕ)
    (v : ↥(maximalIdeal V ^ (k + 1))) :
    (Submodule.Quotient.mk v : Gr V k) = 0 ↔ (v : V) ∈ maximalIdeal V ^ (k + 2) := by
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_top_iff, Ideal.smul_eq_mul, ← pow_succ']

theorem gr_mk_eq_mk (V : Type) [CommRing V] [IsLocalRing V] (k : ℕ)
    (u v : ↥(maximalIdeal V ^ (k + 1))) (h : (u : V) - v ∈ maximalIdeal V ^ (k + 2)) :
    (Submodule.Quotient.mk u : Gr V k) = Submodule.Quotient.mk v := by
  rw [← sub_eq_zero, ← Submodule.Quotient.mk_sub, gr_mk_eq_zero_iff]; simpa using h

theorem sub_mem_pow_succ {O W V : Type} [CommRing O] [IsLocalRing O] [CommRing W]
    [IsLocalRing W] [CommRing V] [IsLocalRing V] (φ : O →+* W)
    (hm : (maximalIdeal O).map φ = maximalIdeal W)
    (hu : ((residue W).comp φ).FormallyUnramified)
    (θ₁ θ₂ : W →+* V) [IsLocalHom θ₁] [IsLocalHom θ₂] (hO : θ₁.comp φ = θ₂.comp φ) (k : ℕ)
    (hk : ∀ w, θ₁ w - θ₂ w ∈ maximalIdeal V ^ (k + 1)) :
    ∀ w, θ₁ w - θ₂ w ∈ maximalIdeal V ^ (k + 2) := by
  have hW := sub_mem_pow_of_mem_maximalIdeal φ hm θ₁ θ₂ hO k hk
  letI : Algebra O (ResidueField W) := ((residue W).comp φ).toAlgebra
  haveI : Algebra.FormallyUnramified O (ResidueField W) := hu
  letI : Module (ResidueField W) (Gr V k) := grModule θ₁ k
  letI : Module O (Gr V k) := Module.compHom _ (algebraMap O (ResidueField W))
  haveI : IsScalarTower O (ResidueField W) (Gr V k) := ⟨fun a b x => by
    show ResidueField.map θ₁ (a • b) • x = ResidueField.map θ₁ (algebraMap O _ a) • (ResidueField.map θ₁ b • x)
    rw [Algebra.smul_def, map_mul, mul_smul]⟩
  let δ₀ : W → Gr V k := fun w => Submodule.Quotient.mk ⟨θ₁ w - θ₂ w, hk w⟩
  have hsm : ∀ (c : W) (v : ↥(maximalIdeal V ^ (k + 1))), residue W c • (Submodule.Quotient.mk v : Gr V k) =
      Submodule.Quotient.mk (θ₁ c • v) := by
    intro c v
    show ResidueField.map θ₁ (residue W c) • (Submodule.Quotient.mk v : Gr V k) = _
    rw [ResidueField.map_residue]
    rfl
  let s := Function.surjInv (residue_surjective (R := W))
  have hs : ∀ w, δ₀ (s (residue W w)) = δ₀ w := by
    intro w
    refine gr_mk_eq_mk V k _ _ ?_
    have hmem : s (residue W w) - w ∈ maximalIdeal W := by
      rw [← Ideal.Quotient.eq]
      exact Function.surjInv_eq _ _
    have := hW _ hmem
    simp only [map_sub] at this ⊢
    convert this using 1; ring
  let D : Derivation O (ResidueField W) (Gr V k) :=
    { toFun := fun x => δ₀ (s x)
      map_add' := by
        intro x y
        obtain ⟨a, rfl⟩ := residue_surjective x
        obtain ⟨b, rfl⟩ := residue_surjective y
        rw [← map_add (f := _), hs, hs, hs, ← Submodule.Quotient.mk_add]
        refine gr_mk_eq_mk V k _ _ ?_
        simp only [Submodule.coe_add, map_add (f := _)]
        convert zero_mem (maximalIdeal V ^ (k + 2)) using 1; ring
      map_smul' := by
        intro c x
        obtain ⟨a, rfl⟩ := residue_surjective x
        simp only [RingHom.id_apply]
        rw [Algebra.smul_def, show algebraMap O (ResidueField W) c = residue W (φ c) from rfl,
          ← map_mul, hs, hs]
        show _ = residue W (φ c) • δ₀ a
        rw [hsm]
        refine gr_mk_eq_mk V k _ _ ?_
        simp only [Submodule.coe_smul, smul_eq_mul, map_mul]
        have := congrArg (fun f => f c) hO
        simp only [RingHom.comp_apply] at this
        rw [this]
        convert zero_mem (maximalIdeal V ^ (k + 2)) using 1; ring
      map_one_eq_zero' := by
        show δ₀ (s 1) = 0
        rw [← map_one (residue W), hs]
        show (Submodule.Quotient.mk _ : Gr V k) = 0
        rw [gr_mk_eq_zero_iff]; simp
      leibniz' := by
        intro x y
        obtain ⟨a, rfl⟩ := residue_surjective x
        obtain ⟨b, rfl⟩ := residue_surjective y
        show δ₀ (s _) = residue W a • δ₀ (s _) + residue W b • δ₀ (s _)
        rw [← map_mul, hs, hs, hs, hsm, hsm, ← Submodule.Quotient.mk_add]
        refine gr_mk_eq_mk V k _ _ ?_
        simp only [Submodule.coe_add, Submodule.coe_smul, smul_eq_mul, map_mul]
        have e : θ₁ a * θ₁ b - θ₂ a * θ₂ b - (θ₁ a * (θ₁ b - θ₂ b) + θ₁ b * (θ₁ a - θ₂ a)) =
            (θ₁ a - θ₂ a) * (θ₂ b - θ₁ b) := by ring
        rw [e, show k + 2 = (k + 1) + 1 from rfl, pow_succ]
        refine Ideal.mul_mem_mul (hk a) ?_
        have := Ideal.pow_le_self (n := k + 1) (I := maximalIdeal V) (by omega) (hk b)
        rw [← neg_sub]; exact neg_mem this }
  have hD : ∀ x, D x = 0 := by
    intro x
    rw [← Derivation.liftKaehlerDifferential_comp_D D x,
      Subsingleton.elim (KaehlerDifferential.D O (ResidueField W) x) 0, map_zero]
  intro w
  have h1 : δ₀ w = 0 := by
    rw [← hs]
    exact hD (residue W w)
  exact (gr_mk_eq_zero_iff V k _).1 h1

theorem localHom_ext : ∀ (O W V : Type) [CommRing O] [IsLocalRing O] [CommRing W] [IsLocalRing W] [IsNoetherianRing W] [CommRing V] [IsLocalRing V] [IsNoetherianRing V] (φ : O →+* W), IsAdicComplete (maximalIdeal W) W → IsEtaleCompletion φ → ((residue W).comp φ).FormallyUnramified → ∀ θ₁ θ₂ : W →+* V, IsLocalHom θ₁ → IsLocalHom θ₂ → θ₁.comp φ = θ₂.comp φ → (∀ w, θ₁ w - θ₂ w ∈ maximalIdeal V) → θ₁ = θ₂ := by
  intro O W V _ _ _ _ _ _ _ _ φ _ hφ hu θ₁ θ₂ h₁ h₂ hO hres
  have hk : ∀ k w, θ₁ w - θ₂ w ∈ maximalIdeal V ^ (k + 1) := by
    intro k
    induction k with
    | zero => simpa using hres
    | succ k ih => exact sub_mem_pow_succ φ hφ.2.1 hu θ₁ θ₂ hO k ih
  ext w
  rw [← sub_eq_zero, ← Ideal.mem_bot,
    ← Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal V).ne_top, Ideal.mem_iInf]
  intro i
  cases i with
  | zero => simp
  | succ i => exact hk i w

end GlobalTheory.EtUniq
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalChartGaloisRigidStalk
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChart.Inj

theorem spMap_comp_eq {S : Scheme.{0}} {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] (ξ : Sp R ⟶ S)
    (ρ₁ ρ₂ : R →+* R') (h : ρ₁.comp (Scheme.stalkClosedPointTo ξ).hom = ρ₂.comp (Scheme.stalkClosedPointTo ξ).hom) :
    spMap ρ₁ ≫ ξ = spMap ρ₂ ≫ ξ := by
  rw [← Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ, ← Category.assoc, ← Category.assoc, ← Spec.map_comp,
    ← Spec.map_comp]
  congr 2
  ext a
  exact congrArg (fun f => f a) h

theorem genPt_eq {X S : Scheme.{0}} (j : X ⟶ S) [Mono j] {R R' : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    [CommRing R'] [IsDomain R'] (ξ : Sp R ⟶ S) (y : Sp (FractionRing R) ⟶ X) (hy : y ≫ j = jK R ≫ ξ)
    (ρ₁ ρ₂ : R →+* R') (h : ρ₁.comp (Scheme.stalkClosedPointTo ξ).hom = ρ₂.comp (Scheme.stalkClosedPointTo ξ).hom)
    (κ₁ κ₂ : Sp (FractionRing R') ⟶ Sp (FractionRing R)) (h₁ : κ₁ ≫ jK R = jK R' ≫ spMap ρ₁)
    (h₂ : κ₂ ≫ jK R = jK R' ≫ spMap ρ₂) : κ₁ ≫ y = κ₂ ≫ y := by
  rw [← cancel_mono j, Category.assoc, Category.assoc, hy, ← Category.assoc, ← Category.assoc, h₁, h₂,
    Category.assoc, Category.assoc, spMap_comp_eq ξ ρ₁ ρ₂ h]

theorem stalk_comp_eq {X : Scheme.{0}} {W V : Type} [CommRing W] [IsLocalRing W] [CommRing V] [IsLocalRing V]
    (u : Sp W ⟶ X) (g₁ g₂ : W →+* V) [IsLocalHom g₁] [IsLocalHom g₂] (hu : spMap g₁ ≫ u = spMap g₂ ≫ u) :
    g₁.comp (Scheme.stalkClosedPointTo u).hom = g₂.comp (Scheme.stalkClosedPointTo u).hom := by
  have l : ∀ (g : W →+* V) [IsLocalHom g], IsLocalHom (Scheme.stalkClosedPointTo u ≫ CommRingCat.ofHom g).hom := by
    intro g _
    rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom]; infer_instance
  have e : ∀ (g : W →+* V) [IsLocalHom g], spMap g ≫ u = (SpecToEquivOfLocalRing X (.of V)).symm
      ⟨u (closedPoint W), Scheme.stalkClosedPointTo u ≫ CommRingCat.ofHom g, l g⟩ := by
    intro g _
    rw [SpecToEquivOfLocalRing_symm_apply, Spec.map_comp_assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  have hinj := (SpecToEquivOfLocalRing X (.of V)).symm.injective ((e g₁).symm.trans (hu.trans (e g₂)))
  obtain ⟨h₁, h₂⟩ := SpecToEquivOfLocalRing_eq_iff.mp hinj
  simp only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp] at h₂
  ext a
  have := congrArg (fun q => q.hom a) h₂
  simpa using this

theorem base_eq {o : Type} [CommRing o] {ζ : o} {g n : ℕ} {φ : InvFun ℤ} (C : Taut ζ g n φ) {V : Type}
    [CommRing V] [IsLocalRing V] [IsNoetherianRing V] (θ₁ θ₂ : C.R →+* V) [IsLocalHom θ₁] [IsLocalHom θ₂]
    (hu : spMap (θ₁.comp C.iw) ≫ C.u = spMap (θ₂.comp C.iw) ≫ C.u) (hm : ∀ r, θ₁ r - θ₂ r ∈ maximalIdeal V) :
    θ₁.comp C.iw = θ₂.comp C.iw := by
  haveI : IsLocalHom C.iw := C.ψ_loc
  haveI : IsNoetherianRing C.W := C.noeth
  have hO := stalk_comp_eq C.u (θ₁.comp C.iw) (θ₂.comp C.iw) hu
  exact GlobalTheory.EtUniq.localHom_ext _ _ _ _ C.complete C.u_et C.u_sep _ _ inferInstance inferInstance hO (fun w => hm _)

theorem eq_of_base_coord {o : Type} [CommRing o] {ζ : o} {g n : ℕ} {φ : InvFun ℤ} (C : Taut ζ g n φ) {V : Type}
    [CommRing V] [IsLocalRing V] [IsNoetherianRing V] (θ₁ θ₂ : C.R →+* V) [IsLocalHom θ₁] [IsLocalHom θ₂]
    (hW : θ₁.comp C.iw = θ₂.comp C.iw) (hs : ∀ k, θ₁ (C.s k) = θ₂ (C.s k)) : θ₁ = θ₂ := by
  refine GlobalTheory.TChart.cuniq _ _ _ C.ψ C.compl θ₁ θ₂ inferInstance inferInstance ?_
  apply MvPolynomial.ringHom_ext
  · intro w
    exact congrArg (fun f => f w) hW
  · intro k
    exact hs k

end GlobalTheory.TChart.Inj


open GlobalTheory.TChart.Inj in
theorem GlobalTheory.TChart.galRigid_stalk_of_isFam : ∀ {g n : ℕ} {φ : InvFun ℤ}, 3 ≤ n → ∀ (F : SFam g n (zetaAway n)) (S : Scheme.{0}) (j : F.X ⟶ S) [IsOpenImmersion j], ∀ (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (y : Sp (FractionRing C.R) ⟶ F.X) (α₁ : pullback G₁.hom (jK C.R) ⟶ F.univ.A.left) (ξ : Sp C.R ⟶ S), C.IsFam F G₁ y α₁ → y ≫ j = jK C.R ≫ ξ → GalRigid (Scheme.stalkClosedPointTo ξ).hom := by
  intro g n φ hn F S j _ C G₁ _ _ y α₁ ξ hF hy R' _ _ _ θ σ hR' hθ hfin hσ hfix hres
  haveI : IsNoetherianRing R' := hR'.1
  haveI : IsLocalHom θ := RingHom.IsIntegral.isLocalHom hfin.to_isIntegral hθ
  haveI : IsLocalHom ((σ : R' →+* R').comp θ) := by
    haveI : IsLocalHom (σ : R' →+* R') := inferInstance
    infer_instance
  obtain ⟨κ₁, hκ₁⟩ := GlobalTheory.PolDeg.exists_genericMap hθ
  obtain ⟨κ₂, hκ₂⟩ := GlobalTheory.PolDeg.exists_genericMap (ρ := (σ : R' →+* R').comp θ) (σ.injective.comp hθ)
  have hf : θ.comp (Scheme.stalkClosedPointTo ξ).hom =
      ((σ : R' →+* R').comp θ).comp (Scheme.stalkClosedPointTo ξ).hom :=
    RingHom.ext fun a => (hfix a).symm
  have hyy := genPt_eq j ξ y hy _ _ hf κ₁ κ₂ hκ₁ hκ₂
  have hm : ∀ r, θ r - ((σ : R' →+* R').comp θ) r ∈ maximalIdeal R' := fun r => by
    rw [← neg_sub]; exact neg_mem (hres r)
  obtain ⟨hu, hs'⟩ := GlobalTheory.T.tautologicalChart_eq_of_same_genericPoint hn F C G₁ y α₁ hF R' θ ((σ : R' →+* R').comp θ) hR' hθ (σ.injective.comp hθ)
    inferInstance inferInstance κ₁ κ₂ hκ₁ hκ₂ hyy
  have hW := base_eq C θ ((σ : R' →+* R').comp θ) hu hm
  have e := eq_of_base_coord C θ ((σ : R' →+* R').comp θ) hW (hs' hW)
  intro r
  exact (congrArg (fun f => f r) e).symm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalChartGaloisRigidStalkStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tautologicalChart_galois_rigid_stalk : ∀ {g n : ℕ} {φ : InvFun ℤ}, 3 ≤ n → ∀ (F : SFam g n (zetaAway n)) (S : Scheme.{0}) (j : F.X ⟶ S) [IsOpenImmersion j], ∀ (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (y : Sp (FractionRing C.R) ⟶ F.X) (α₁ : pullback G₁.hom (jK C.R) ⟶ F.univ.A.left) (ξ : Sp C.R ⟶ S), C.IsFam F G₁ y α₁ → y ≫ j = jK C.R ≫ ξ → GalRigid (Scheme.stalkClosedPointTo ξ).hom := by
  first | exact @GlobalTheory.TChart.galRigid_stalk_of_isFam | exact GlobalTheory.TChart.galRigid_stalk_of_isFam | (intros; apply GlobalTheory.TChart.galRigid_stalk_of_isFam <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingKrullDimStalkLeTautologicalChartRing
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMaximalMvPolynomialLocalization
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

namespace GlobalTheory.DedekindDimFormula
open ReciprocityTheory.CA

theorem isMaximal_comap_C {o : Type} [CommRing o] [IsJacobsonRing o] (N : ℕ)
    (𝔑 : Ideal (MvPolynomial (Fin N) o)) [𝔑.IsMaximal] :
    (𝔑.comap (MvPolynomial.C : o →+* MvPolynomial (Fin N) o)).IsMaximal := by
  have hi := MvPolynomial.quotient_mk_comp_C_isIntegral_of_isJacobsonRing 𝔑
  letI := Ideal.Quotient.field 𝔑
  have := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' _ hi
    (⊥ : Ideal (MvPolynomial (Fin N) o ⧸ 𝔑))
  rwa [← Ideal.comap_comap, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker] at this

theorem isCM_localization (o : Type) [CommRing o] [IsDomain o] [IsDedekindDomain o] :
    ∃ δ : ℕ, ∀ (p : Ideal o) [p.IsMaximal],
      IsCM (Localization.AtPrime p) ∧ ringKrullDim (Localization.AtPrime p) = δ := by
  by_cases hf : IsField o
  · refine ⟨0, fun p _ => ?_⟩
    letI := hf.toField
    have hp : p = ⊥ := (Ideal.eq_bot_or_top p).resolve_right (Ideal.IsMaximal.ne_top inferInstance)
    have hd : ringKrullDim (Localization.AtPrime p) = 0 := by
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p), hp,
        Ideal.height_bot]
      rfl
    refine ⟨⟨inferInstance, 0, by rw [hd]; rfl, ?_⟩, hd⟩
    refine ⟨[], rfl, by simp, ?_⟩
    rw [IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal (by simp)]
    exact RingTheory.Sequence.IsWeaklyRegular.nil _ _
  · refine ⟨1, fun p _ => ?_⟩
    have hp : p ≠ ⊥ := by
      intro h
      exact hf (Ring.isField_iff_maximal_bot.mpr (h ▸ inferInstance))
    haveI : IsDiscreteValuationRing (Localization.AtPrime p) :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain o hp _
    have hd := IsDiscreteValuationRing.ringKrullDim_eq_one (Localization.AtPrime p)
    refine ⟨⟨inferInstance, 1, by rw [hd]; rfl, ?_⟩, by rw [hd]; rfl⟩
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime p)
    have hm : ϖ ∈ IsLocalRing.maximalIdeal (Localization.AtPrime p) := hϖ.not_isUnit
    refine ⟨[ϖ], rfl, by simpa using hm, ?_⟩
    rw [IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal (by simpa using hm),
      RingTheory.Sequence.isWeaklyRegular_singleton_iff]
    exact IsSMulRegular.of_ne_zero hϖ.ne_zero

theorem exists_maximal_mvPolynomial_localization' {o : Type} [CommRing o] (N : ℕ) (p : Ideal o) [p.IsMaximal] (𝔑 : Ideal (MvPolynomial (Fin N) o)) [𝔑.IsMaximal]
    (hc : 𝔑.comap (MvPolynomial.C : o →+* MvPolynomial (Fin N) o) = p) :
    ∃ (𝔑' : Ideal (MvPolynomial (Fin N) (Localization.AtPrime p))) (_ : 𝔑'.IsMaximal),
      𝔑'.comap (MvPolynomial.C : Localization.AtPrime p →+* _) =
        IsLocalRing.maximalIdeal (Localization.AtPrime p) ∧
      Nonempty (Localization.AtPrime 𝔑' ≃+* Localization.AtPrime 𝔑) ∧ 𝔑'.height = 𝔑.height := by
  classical
  letI : Algebra (MvPolynomial (Fin N) o) (MvPolynomial (Fin N) (Localization.AtPrime p)) :=
    MvPolynomial.algebraMvPolynomial
  let W : Submonoid (MvPolynomial (Fin N) o) := p.primeCompl.map (MvPolynomial.C (σ := Fin N))
  haveI hL : IsLocalization W (MvPolynomial (Fin N) (Localization.AtPrime p)) :=
    MvPolynomial.isLocalization p.primeCompl (Localization.AtPrime p)
  have hdisj : Disjoint (W : Set (MvPolynomial (Fin N) o)) (𝔑 : Set _) := by
    rw [Set.disjoint_left]
    rintro x ⟨m, hm, rfl⟩ hx
    exact hm (hc ▸ (show m ∈ 𝔑.comap MvPolynomial.C from hx))
  let 𝔑' := 𝔑.map (algebraMap (MvPolynomial (Fin N) o) (MvPolynomial (Fin N) (Localization.AtPrime p)))
  haveI hP : 𝔑'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint W _ 𝔑 inferInstance hdisj
  have hcm : 𝔑'.comap (algebraMap (MvPolynomial (Fin N) o) (MvPolynomial (Fin N) (Localization.AtPrime p))) = 𝔑 :=
    IsLocalization.under_map_of_isPrime_disjoint W _ inferInstance hdisj
  haveI hM : 𝔑'.IsMaximal := by
    refine ⟨⟨hP.ne_top, fun J hJ => ?_⟩⟩
    by_contra hJt
    have h1 : 𝔑 ≤ J.comap (algebraMap (MvPolynomial (Fin N) o) (MvPolynomial (Fin N) (Localization.AtPrime p))) :=
      hcm ▸ Ideal.comap_mono hJ.le
    have h2 : J.comap (algebraMap (MvPolynomial (Fin N) o) (MvPolynomial (Fin N) (Localization.AtPrime p))) ≠ ⊤ := by
      intro h
      apply hJt
      rw [Ideal.eq_top_iff_one]
      have : (1 : MvPolynomial (Fin N) o) ∈ J.comap (algebraMap (MvPolynomial (Fin N) o) (MvPolynomial (Fin N) (Localization.AtPrime p))) := h ▸ Submodule.mem_top
      simpa using this
    have h3 := (‹𝔑.IsMaximal›.eq_of_le h2 h1)
    have h4 : J = 𝔑' := by
      have h5 := IsLocalization.map_under W (MvPolynomial (Fin N) (Localization.AtPrime p)) J
      change Ideal.map _ (J.comap (algebraMap (MvPolynomial (Fin N) o) (MvPolynomial (Fin N) (Localization.AtPrime p)))) = J at h5
      rw [← h3] at h5
      exact h5.symm
    exact hJ.ne' h4
  refine ⟨𝔑', hM, ?_, ?_, IsLocalization.height_map_of_disjoint W 𝔑 hdisj⟩
  · haveI : (𝔑'.comap (MvPolynomial.C : Localization.AtPrime p →+* _)).IsPrime := Ideal.comap_isPrime _ _
    refine le_antisymm (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)) ?_
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, Ideal.mem_comap]
    have e : (MvPolynomial.C (algebraMap o (Localization.AtPrime p) x) : MvPolynomial (Fin N) (Localization.AtPrime p)) =
        algebraMap (MvPolynomial (Fin N) o) (MvPolynomial (Fin N) (Localization.AtPrime p)) (MvPolynomial.C x) := by
      rw [MvPolynomial.algebraMap_def, MvPolynomial.map_C]
    rw [e]
    exact Ideal.mem_map_of_mem _ (by rw [← hc] at hx; exact hx)
  · haveI h0 : IsLocalization.AtPrime (Localization.AtPrime 𝔑')
        (𝔑'.comap (algebraMap (MvPolynomial (Fin N) o) (MvPolynomial (Fin N) (Localization.AtPrime p)))) :=
      IsLocalization.isLocalization_isLocalization_atPrime_isLocalization W _ 𝔑'
    haveI : IsLocalization 𝔑.primeCompl (Localization.AtPrime 𝔑') := by
      have hsub : (𝔑'.comap (algebraMap (MvPolynomial (Fin N) o) (MvPolynomial (Fin N) (Localization.AtPrime p)))).primeCompl = 𝔑.primeCompl :=
        Submonoid.ext fun x => by simp only [Ideal.mem_primeCompl_iff, hcm]
      have h0' : IsLocalization (𝔑'.comap (algebraMap (MvPolynomial (Fin N) o) (MvPolynomial (Fin N) (Localization.AtPrime p)))).primeCompl (Localization.AtPrime 𝔑') := h0
      rw [hsub] at h0'
      exact h0'
    exact ⟨(IsLocalization.algEquiv 𝔑.primeCompl (Localization.AtPrime 𝔑') (Localization.AtPrime 𝔑)).toRingEquiv⟩

theorem polyEquidim : ∀ (o : Type) [CommRing o] [IsDomain o] [IsDedekindDomain o] [IsJacobsonRing o] (N : ℕ),
    ∃ d : ℕ, ∀ (𝔑 : Ideal (MvPolynomial (Fin N) o)) [𝔑.IsMaximal],
      IsCM (Localization.AtPrime 𝔑) ∧ 𝔑.height = (d : ℕ∞) := by
  intro o _ _ _ _ N
  obtain ⟨δ, hδ⟩ := isCM_localization o
  refine ⟨δ + N, fun 𝔑 _ => ?_⟩
  haveI := isMaximal_comap_C N 𝔑
  obtain ⟨hCM, hdim⟩ := hδ (𝔑.comap (MvPolynomial.C : o →+* MvPolynomial (Fin N) o))
  obtain ⟨𝔑', h𝔑', hc, ⟨e⟩, hh⟩ := exists_maximal_mvPolynomial_localization' N _ 𝔑 rfl
  have h := isCM_localization_mvPolynomial hCM N 𝔑' hc
  refine ⟨h.1.of_ringEquiv e, ?_⟩
  have h2 := h.2
  rw [hdim, hh] at h2
  have h3 : ((𝔑.height : ℕ∞) : WithBot ℕ∞) = (((δ + N : ℕ) : ℕ∞) : WithBot ℕ∞) := by
    rw [h2]; push_cast; ring
  exact WithBot.coe_injective h3

end GlobalTheory.DedekindDimFormula

namespace GlobalTheory.DedekindDimFormula

theorem affine_heights (o A : Type) [CommRing o] [IsDomain o] [IsDedekindDomain o] [IsJacobsonRing o]
    [CommRing A] [IsDomain A] [Algebra o A] [Algebra.FiniteType o A] :
    ∃ h : ℕ, (∀ (M : Ideal A) [M.IsMaximal], M.height = (h : ℕ∞)) ∧
      ∀ (P M : Ideal A) [P.IsPrime] [M.IsMaximal],
        (M.height : WithBot ℕ∞) ≤ (P.height : WithBot ℕ∞) + ringKrullDim (A ⧸ P) := by
  obtain ⟨N, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹Algebra.FiniteType o A›
  obtain ⟨d, hd⟩ := polyEquidim o N
  set Q := RingHom.ker (f : MvPolynomial (Fin N) o →+* A) with hQdef
  haveI : Q.IsPrime := RingHom.ker_isPrime _
  let e : (MvPolynomial (Fin N) o ⧸ Q) ≃+* A :=
    RingHom.quotientKerEquivOfSurjective (f := (f : MvPolynomial (Fin N) o →+* A)) hf
  obtain ⟨M₀, hM₀⟩ := Ideal.exists_maximal (MvPolynomial (Fin N) o ⧸ Q)
  haveI : (M₀.comap (Ideal.Quotient.mk Q)).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  have hQle : Q.height ≤ d := by
    rw [← (hd (M₀.comap (Ideal.Quotient.mk Q))).2]
    exact Ideal.height_mono fun x hx => by
      simp [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx, M₀.zero_mem]
  obtain ⟨k, hk⟩ : ∃ k : ℕ, Q.height = k := by
    have : Q.height ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top d) hQle
    exact ⟨Q.height.toNat, (ENat.coe_toNat this).symm⟩
  have hkd : k ≤ d := by rw [hk] at hQle; exact_mod_cast hQle
  refine ⟨d - k, fun M _ => ?_, fun P M _ _ => ?_⟩
  · haveI : (M.comap e).IsMaximal := Ideal.comap_isMaximal_of_surjective _ e.surjective
    haveI : ((M.comap e).comap (Ideal.Quotient.mk Q)).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
    obtain ⟨hCM, hh⟩ := hd ((M.comap e).comap (Ideal.Quotient.mk Q))
    have e1 := GlobalTheory.FinTypeIntCatenary.height_comap_mk Q (M.comap e) hCM
    rw [hh, hk, RingEquiv.height_comap] at e1
    have : ((d - k : ℕ) : ℕ∞) + k = M.height + k := by
      rw [← Nat.cast_add, Nat.sub_add_cancel hkd, e1, add_comm]
    exact (WithTop.add_right_cancel (ENat.coe_ne_top k) this).symm
  · haveI : (P.comap e).IsPrime := Ideal.comap_isPrime _ _
    haveI : (M.comap e).IsMaximal := Ideal.comap_isMaximal_of_surjective _ e.surjective
    have h := GlobalTheory.FinTypeIntCatenary.height_le_of_equidim d (fun 𝔑 _ => hd 𝔑) Q (P.comap e) (M.comap e)
    rw [RingEquiv.height_comap, RingEquiv.height_comap] at h
    have hdim : ringKrullDim ((MvPolynomial (Fin N) o ⧸ Q) ⧸ P.comap e) = ringKrullDim (A ⧸ P) :=
      ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv _ _ e
        (Ideal.map_comap_of_surjective _ e.surjective P).symm)
    rwa [hdim] at h

end GlobalTheory.DedekindDimFormula

namespace GlobalTheory.DedekindDimFormula

end GlobalTheory.DedekindDimFormula
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingKrullDimStalkLeTautologicalChartRing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChart.ChartDim

theorem isAlgebraic_of_quasiFinite (A K : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [FaithfulSMul A K]
    [Algebra.QuasiFinite A K] : Algebra.IsAlgebraic A K := by
  letI : Algebra (FractionRing A) K := FractionRing.liftAlgebra A K
  haveI : IsScalarTower A (FractionRing A) K := FractionRing.isScalarTower_liftAlgebra A K
  haveI : Algebra.QuasiFinite (FractionRing A) K := .of_restrictScalars A _ _
  haveI : Module.Finite (FractionRing A) K := Algebra.QuasiFinite.iff_of_isArtinianRing.1 inferInstance
  haveI : Algebra.IsAlgebraic A (FractionRing A) := IsLocalization.isAlgebraic _ (nonZeroDivisors A)
  exact Algebra.IsAlgebraic.trans A (FractionRing A) K

theorem trdeg_le (k A B K : Type) [CommRing k] [IsDomain k] [CommRing A] [IsDomain A] [CommRing B] [Field K] [Algebra k A]
    [Algebra k B] [Algebra k K] [Algebra A K] [IsScalarTower k A K] [FaithfulSMul k A] [FaithfulSMul A K]
    [Algebra.IsAlgebraic A K] (b : B →ₐ[k] K) (hb : Function.Injective b) : Algebra.trdeg k B ≤ Algebra.trdeg k A := by
  refine (trdeg_le_of_injective b hb).trans ?_
  rw [← trdeg_add_eq k A (A := K), trdeg_eq_zero (R := A) (A := K), add_zero]

theorem ringKrullDim_le_of_isAlgebraic (A B K : Type) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Field K]
    [Algebra.FiniteType ℤ A] [Algebra.FiniteType ℤ B] [Algebra A K] [FaithfulSMul A K] [Algebra.IsAlgebraic A K]
    (b : B →+* K) (hb : Function.Injective b) : ringKrullDim B ≤ ringKrullDim A := by
  have ha := FaithfulSMul.algebraMap_injective A K
  obtain ⟨p, hp⟩ := CharP.exists K
  haveI : CharP A p := RingHom.charP _ ha p
  haveI : CharP B p := RingHom.charP _ hb p
  rcases CharP.char_is_prime_or_zero K p with h | rfl
  · haveI := Fact.mk h
    letI := ZMod.algebra A p
    letI := ZMod.algebra B p
    letI := ZMod.algebra K p
    haveI : IsScalarTower ℤ (ZMod p) A := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
    haveI : IsScalarTower ℤ (ZMod p) B := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
    haveI : IsScalarTower (ZMod p) A K := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
    haveI : Algebra.FiniteType (ZMod p) A := Algebra.FiniteType.of_restrictScalars_finiteType ℤ _ _
    haveI : Algebra.FiniteType (ZMod p) B := Algebra.FiniteType.of_restrictScalars_finiteType ℤ _ _
    obtain ⟨s, hs⟩ := Cardinal.lt_aleph0.mp (trdeg_lt_aleph0_of_finiteType (R := ZMod p) (S := A))
    obtain ⟨t, ht⟩ := Cardinal.lt_aleph0.mp (trdeg_lt_aleph0_of_finiteType (R := ZMod p) (S := B))
    have hle := trdeg_le (ZMod p) A B K
      { b with commutes' := fun r => RingHom.congr_fun (Subsingleton.elim (b.comp (algebraMap (ZMod p) B)) _) r } hb
    rw [hs, ht] at hle
    rw [ReciprocityTheory.CA.ringKrullDim_eq_of_trdeg_eq_field s hs, ReciprocityTheory.CA.ringKrullDim_eq_of_trdeg_eq_field t ht]
    exact_mod_cast hle
  · haveI : CharZero A := CharP.charP_to_charZero _
    haveI : CharZero B := CharP.charP_to_charZero _
    haveI : FaithfulSMul ℤ A := (faithfulSMul_iff_algebraMap_injective _ _).mpr (RingHom.injective_int _)
    have hle := trdeg_le ℤ A B K b.toIntAlgHom hb
    rw [IntFiniteTypeDim.ringKrullDim_eq_trdeg_add_one A (RingHom.injective_int _),
      IntFiniteTypeDim.ringKrullDim_eq_trdeg_add_one B (RingHom.injective_int _)]
    exact WithBot.coe_le_coe.2 (add_le_add_left (OrderHomClass.mono Cardinal.toENat hle) 1)

theorem finiteType_int_quotient {A : Type} [CommRing A] [Algebra.FiniteType ℤ A] (I : Ideal A) :
    @Algebra.FiniteType ℤ (A ⧸ I) _ _ (Ring.toIntAlgebra _) :=
  Algebra.FiniteType.of_surjective (Ideal.Quotient.mk I).toIntAlgHom Ideal.Quotient.mk_surjective

theorem finiteType_int_mvPolynomial (A σ : Type) [CommRing A] [Algebra.FiniteType ℤ A] [Finite σ] :
    @Algebra.FiniteType ℤ (MvPolynomial σ A) _ _ (Ring.toIntAlgebra _) := by
  have h : Algebra.FiniteType ℤ (MvPolynomial σ A) := Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  convert h
  · rfl

theorem ringKrullDim_quotient_ker_le {A B K : Type} [CommRing A] [CommRing B] [Field K]
    [Algebra.FiniteType ℤ A] [Algebra.FiniteType ℤ B] (a : A →+* K) (ha : a.QuasiFinite) (b : B →+* K) :
    ringKrullDim (B ⧸ RingHom.ker b) ≤ ringKrullDim (A ⧸ RingHom.ker a) := by
  haveI := RingHom.ker_isPrime a
  haveI := RingHom.ker_isPrime b
  letI := a.toAlgebra
  letI := (RingHom.kerLift a).toAlgebra
  haveI : IsScalarTower A (A ⧸ RingHom.ker a) K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.QuasiFinite A K := ha
  haveI : Algebra.QuasiFinite (A ⧸ RingHom.ker a) K := .of_restrictScalars A _ _
  haveI : FaithfulSMul (A ⧸ RingHom.ker a) K := (faithfulSMul_iff_algebraMap_injective _ _).mpr (RingHom.kerLift_injective a)
  haveI := isAlgebraic_of_quasiFinite (A ⧸ RingHom.ker a) K
  haveI := finiteType_int_quotient (RingHom.ker a)
  haveI := finiteType_int_quotient (RingHom.ker b)
  exact ringKrullDim_le_of_isAlgebraic _ _ K (RingHom.kerLift b) (RingHom.kerLift_injective b)

theorem exists_flat_quasiFinite {o : Type} [CommRing o] {X : Scheme.{0}} (s : X ⟶ Sp o) (D : ℕ)
    (hs : SmoothOfRelativeDimension D s) (y : X) :
    ∃ φ : MvPolynomial (Fin D) o →+* X.presheaf.stalk y, φ.Flat ∧ φ.QuasiFinite := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have hW : IsAffineOpen W := hW
  have h0 := HasRingHomProperty.appLE (@SmoothOfRelativeDimension D) s hs ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ le_top
  obtain ⟨t, ht, h'⟩ := (RingHom.locally_iff_isLocalization
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso _).1 h0
  have hcov := hW.self_le_iSup_basicOpen_iff.2 ht hxW
  obtain ⟨⟨g, hg⟩, hxg⟩ := TopologicalSpace.Opens.mem_iSup.1 hcov
  have hl := hW.isLocalization_basicOpen g
  have h1 := h' g hg Γ(X, X.basicOpen g)
  have h3 := RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
    (Scheme.ΓSpecIso (CommRingCat.of o)).symm.commRingCatIsoToRingEquiv h1
  obtain ⟨φ, -, hφ⟩ := h3.exists_etale_mvPolynomial
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨y, hxg⟩ : X.basicOpen g)
  haveI := (hW.basicOpen g).isLocalization_stalk ⟨y, hxg⟩
  letI := φ.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin D) o) Γ(X, X.basicOpen g) := hφ
  refine ⟨(algebraMap Γ(X, X.basicOpen g) (X.presheaf.stalk y)).comp φ, RingHom.Flat.comp ?_ ?_, RingHom.QuasiFinite.comp ?_ ?_⟩
  · exact (inferInstance : Module.Flat (MvPolynomial (Fin D) o) Γ(X, X.basicOpen g))
  · exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat _ ((hW.basicOpen g).primeIdealOf ⟨y, hxg⟩).asIdeal.primeCompl)
  · exact RingHom.quasiFinite_algebraMap.2 (.of_isLocalization ((hW.basicOpen g).primeIdealOf ⟨y, hxg⟩).asIdeal.primeCompl)
  · exact (inferInstance : Algebra.QuasiFinite (MvPolynomial (Fin D) o) Γ(X, X.basicOpen g))

theorem ringKrullDim_le_add_of_flat {B R : Type} [CommRing B] [IsDomain B] [Algebra.FiniteType ℤ B] [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (ψ : B →+* R) (hψ : ψ.Flat) :
    ringKrullDim B ≤ ringKrullDim R + ringKrullDim (B ⧸ RingHom.ker ((residue R).comp ψ)) := by
  haveI := ReciprocityTheory.AnForm.R.IntegerToRational.isJacobsonRing_int
  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing ℤ B
  obtain ⟨h, hh, hle⟩ := DedekindDimFormula.affine_heights ℤ B
  set P := RingHom.ker ((residue R).comp ψ) with hP
  haveI : P.IsPrime := RingHom.ker_isPrime _
  obtain ⟨M, hM⟩ := Ideal.exists_maximal B
  have h1 : ringKrullDim B ≤ (M.height : WithBot ℕ∞) :=
    (ringKrullDim_le_iff_isMaximal_height_le _).2 fun m hm => by rw [hh m, hh M]
  refine h1.trans ((hle P M).trans (add_le_add_left ?_ _))
  letI := ψ.toAlgebra
  haveI : Module.Flat B R := hψ
  haveI : (maximalIdeal R).LiesOver P := ⟨by rw [hP, ← RingHom.comap_ker, ker_residue]; rfl⟩
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim,
    Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown P (maximalIdeal R)]
  exact WithBot.coe_le_coe.2 le_self_add

theorem mem_of_mem_minimalPrimes {A : Type} [CommRing A] [IsNoetherianRing A] {U : Set (PrimeSpectrum A)} (hU : IsOpen U)
    (hD : Dense U) (Q : PrimeSpectrum A) (hQ : Q.asIdeal ∈ minimalPrimes A) : Q ∈ U := by
  classical
  let t := (minimalPrimes.finite_of_isNoetherianRing A).toFinset.erase Q.asIdeal
  have h1 : ¬ t.inf id ≤ Q.asIdeal := fun h => by
    obtain ⟨I, hI, hle⟩ := Q.isPrime.inf_le'.1 h
    obtain ⟨hne, hI⟩ := Finset.mem_erase.1 hI
    rw [Set.Finite.mem_toFinset] at hI
    exact hne (le_antisymm hle (hQ.2 hI.1 hle))
  obtain ⟨f, hf, hfQ⟩ := SetLike.not_le_iff_exists.1 h1
  obtain ⟨z, hz, hzU⟩ := hD.inter_open_nonempty _ (PrimeSpectrum.basicOpen f).isOpen ⟨Q, hfQ⟩
  obtain ⟨Q', hQ', hle⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal A)) (J := z.asIdeal) bot_le
  have hQQ : Q' = Q.asIdeal := by
    by_contra hne
    have : t.inf id ≤ Q' := Finset.inf_le (f := id) (Finset.mem_erase.2 ⟨hne, (Set.Finite.mem_toFinset _).2 hQ'⟩)
    exact hz (hle (this hf))
  exact ((PrimeSpectrum.le_iff_specializes Q z).1 (show Q.asIdeal ≤ z.asIdeal from hQQ ▸ hle)).mem_open hU hzU

theorem finiteType_sections {o : Type} [CommRing o] [Algebra.FiniteType ℤ o] {S : Scheme.{0}} (s : S ⟶ Sp o)
    [LocallyOfFiniteType s] {U : S.Opens} (hU : IsAffineOpen U) : Algebra.FiniteType ℤ Γ(S, U) := by
  have hl : LocallyOfFiniteType (Spec.map (Spec.preimage (hU.fromSpec ≫ s))) := by
    rw [Spec.map_preimage]; infer_instance
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at hl
  have h := hl.comp (RingHom.finiteType_algebraMap.2 (inferInstance : Algebra.FiniteType ℤ o))
  rw [← RingHom.finiteType_algebraMap]
  convert h using 1
  exact Subsingleton.elim _ _

theorem exists_stalk_hom {S : Scheme.{0}} {U : S.Opens} (hU : IsAffineOpen U) (P : PrimeSpectrum Γ(S, U)) :
    ∃ a : Γ(S, U) →+* S.presheaf.stalk (hU.fromSpec P), a.QuasiFinite ∧ (maximalIdeal _).comap a = P.asIdeal ∧
      ringKrullDim (S.presheaf.stalk (hU.fromSpec P)) = P.asIdeal.height := by
  have hx : hU.fromSpec P ∈ U := by
    have : hU.fromSpec P ∈ Set.range hU.fromSpec := ⟨P, rfl⟩
    rwa [hU.range_fromSpec] at this
  letI : Algebra Γ(S, U) (S.presheaf.stalk (hU.fromSpec P)) :=
    TopCat.Presheaf.algebra_section_stalk S.presheaf (⟨hU.fromSpec P, hx⟩ : U)
  haveI : IsLocalization.AtPrime (S.presheaf.stalk (hU.fromSpec P)) P.asIdeal := hU.isLocalization_stalk' P hx
  exact ⟨algebraMap _ _, RingHom.quasiFinite_algebraMap.2 (.of_isLocalization P.asIdeal.primeCompl),
    IsLocalization.AtPrime.under_maximalIdeal _ P.asIdeal, IsLocalization.AtPrime.ringKrullDim_eq_height P.asIdeal _⟩

theorem ringKrullDim_sections_le {o : Type} [CommRing o] [Algebra.FiniteType ℤ o] {S X : Scheme.{0}} (s : S ⟶ Sp o)
    [LocallyOfFiniteType s] (j : X ⟶ S) [IsOpenImmersion j] (hj : Dense (Set.range j)) (sX : X ⟶ Sp o) (D : ℕ)
    (hs : SmoothOfRelativeDimension D sX) {U : S.Opens} (hU : IsAffineOpen U) :
    ringKrullDim Γ(S, U) ≤ ringKrullDim o + D := by
  haveI := finiteType_sections s hU
  haveI : IsNoetherianRing Γ(S, U) := Algebra.FiniteType.isNoetherianRing ℤ _
  haveI : IsNoetherianRing o := Algebra.FiniteType.isNoetherianRing ℤ _
  rw [← ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot Γ(S, U))]
  refine IntFiniteTypeDim.ringKrullDim_quotient_le_of_minimalPrimes _ _ fun Q hQ => ?_
  let q : PrimeSpectrum Γ(S, U) := ⟨Q, hQ.1.1⟩
  obtain ⟨y, hy⟩ : q ∈ hU.fromSpec ⁻¹' Set.range j :=
    mem_of_mem_minimalPrimes (j.isOpenEmbedding.isOpen_range.preimage hU.fromSpec.continuous)
      (hj.preimage hU.fromSpec.isOpenEmbedding.isOpenMap) q hQ
  obtain ⟨φ, -, hφ⟩ := exists_flat_quasiFinite sX D hs y
  obtain ⟨a, -, ha, -⟩ := exists_stalk_hom hU q
  let e : S.presheaf.stalk (hU.fromSpec q) →+* X.presheaf.stalk y :=
    (j.stalkMap y).hom.comp (S.presheaf.stalkCongr (.of_eq hy.symm)).hom.hom
  haveI : IsLocalHom e := RingHom.isLocalHom_comp _ _
  haveI := finiteType_int_mvPolynomial o (Fin D)
  have h := ringKrullDim_quotient_ker_le ((residue _).comp φ)
    ((RingHom.QuasiFinite.of_finite (RingHom.Finite.of_surjective _ residue_surjective)).comp hφ)
    ((residue _).comp (e.comp a))
  rw [← RingHom.comap_ker (residue _) (e.comp a), ker_residue, ← Ideal.comap_comap, IsLocalRing.maximalIdeal_comap, ha] at h
  refine h.trans ((ringKrullDim_quotient_le _).trans ?_)
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem flat_map {A B σ : Type} [CommRing A] [CommRing B] {f : A →+* B} (hf : f.Flat) :
    (MvPolynomial.map (σ := σ) f).Flat := by
  letI := f.toAlgebra
  letI : Algebra (MvPolynomial σ A) (MvPolynomial σ B) := MvPolynomial.algebraMvPolynomial
  haveI : Module.Flat A B := hf
  exact RingHom.Flat.isStableUnderBaseChange A B (MvPolynomial σ A) (MvPolynomial σ B) hf

theorem card_basis {r : ℕ} {J : Type} [Fintype J] (ε : Module.Basis J ℤ (balForms (id : ℤ → ℤ) (Fin r → ℤ))) :
    Fintype.card J = r * (r + 1) / 2 := by
  have e : balForms (id : ℤ → ℤ) (Fin r → ℤ) = GlobalTheory.Forms.symForms ℤ (Fin r → ℤ) ℤ :=
    Submodule.ext fun β => mem_balForms_int.trans GlobalTheory.Forms.mem_symForms.symm
  rw [← Module.finrank_eq_card_basis ε, e, GlobalTheory.Forms.finrank_symLattice, Module.finrank_fin_fun, Nat.choose_two_right,
    Nat.add_sub_cancel, mul_comm]

theorem exists_ringKrullDim_eq (A : Type) [CommRing A] [IsDomain A] [Algebra.FiniteType ℤ A] : ∃ k : ℕ, ringKrullDim A = k := by
  obtain ⟨h, hh, -⟩ := haveI := ReciprocityTheory.AnForm.R.IntegerToRational.isJacobsonRing_int; DedekindDimFormula.affine_heights ℤ A
  have h1 : ringKrullDim A ≤ (h : ℕ∞) := (ringKrullDim_le_iff_isMaximal_height_le _).2 fun m hm => by rw [hh m]
  have h0 : 0 ≤ ringKrullDim A := ringKrullDim_nonneg_of_nontrivial
  induction hA : ringKrullDim A with
  | bot => simp [hA] at h0
  | coe a =>
    rw [hA, WithBot.coe_le_coe] at h1
    exact ⟨a.toNat, by rw [← WithBot.coe_natCast, ENat.coe_toNat (ne_top_of_le_ne_top (ENat.coe_ne_top h) h1)]⟩

theorem ringKrullDim_stalk_le {o : Type} [CommRing o] [Algebra.FiniteType ℤ o] {S X : Scheme.{0}} (s : S ⟶ Sp o)
    [LocallyOfFiniteType s] (j : X ⟶ S) [IsOpenImmersion j] (hj : Dense (Set.range j)) (sX : X ⟶ Sp o) (D : ℕ)
    (hs : SmoothOfRelativeDimension D sX) {B R : Type} [CommRing B] [IsDomain B] [Algebra.FiniteType ℤ B] [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] (ψ : B →+* R) (hψ : ψ.Flat) (hB : ringKrullDim B = ringKrullDim o + D) {x : S}
    (f : S.presheaf.stalk x →+* R) [IsLocalHom f] (hf : ((residue R).comp f).Finite) :
    ringKrullDim (S.presheaf.stalk x) ≤ ringKrullDim R := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hU : IsAffineOpen U := hU
  obtain ⟨P, rfl⟩ : x ∈ Set.range hU.fromSpec := by rw [hU.range_fromSpec]; exact hxU
  obtain ⟨a, ha₁, ha₂, ha₃⟩ := exists_stalk_hom hU P
  haveI := finiteType_sections s hU
  have h1 := ringKrullDim_quotient_ker_le (((residue R).comp f).comp a) ((RingHom.QuasiFinite.of_finite hf).comp ha₁)
    ((residue R).comp ψ)
  rw [← RingHom.comap_ker _ a, ← RingHom.comap_ker _ f, ker_residue, IsLocalRing.maximalIdeal_comap, ha₂] at h1
  haveI := P.isPrime
  haveI := finiteType_int_quotient P.asIdeal
  obtain ⟨k, hk⟩ := exists_ringKrullDim_eq (Γ(S, U) ⧸ P.asIdeal)
  have h2 := (RegularAscent.height_add_ringKrullDim_quotient_le P.asIdeal).trans
    ((ringKrullDim_sections_le s j hj sX D hs hU).trans (hB.ge.trans
      ((ringKrullDim_le_add_of_flat ψ hψ).trans (add_le_add_right h1 _))))
  rw [hk] at h2
  rw [ha₃]
  exact ENat.WithBot.add_le_add_natCast_right_iff.1 h2

theorem ringKrullDim_stalk_le_chart : ∀ g : ℕ, 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ → NoSelfInt id g φ → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) (d : ℕ) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), MinAt5 F z i OZ → BlowAt F z i φ d π j BD → ∀ (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (y : Sp (FractionRing C.R) ⟶ F.X) (α₁ : pullback G₁.hom (jK C.R) ⟶ F.univ.A.left) (ξ : Sp C.R ⟶ S), C.IsFam F G₁ y α₁ → y ≫ j = jK C.R ≫ ξ → ((residue C.R).comp (Scheme.stalkClosedPointTo ξ).hom).Finite → ringKrullDim (S.presheaf.stalk (ξ (closedPoint C.R))) ≤ ringKrullDim C.R := by
  intro g _ φ _ _ n hn _ F Z z i OZ d S π j _ BD _ hB C G₁ _ _ y α₁ ξ _ _ hf
  obtain ⟨J, -, -, -, -, hP, hD, -⟩ := hB
  have hn0 : n ≠ 0 := by omega
  haveI : IsProper (π ≫ z) := GlobalTheory.SchemeWords.isProper_of_isProjOver hP
  haveI := finiteType_cycAway n
  haveI : IsNoetherianRing (cycAway n) := Algebra.FiniteType.isNoetherianRing ℤ _
  haveI : IsNoetherianRing C.R := C.compl.1
  have hd : SmoothOfRelativeDimension C.h C.F.univ.A.hom :=
    GlobalTheory.SiegSharpCover.smoothDim C.F.univ (by omega) (cycBase hn0).ζ.isUnit (isUnit_natCast hn0)
  haveI := GlobalTheory.smoothOfRelativeDimension_powObj C.F.univ.A C.h hd C.T.r
  haveI := C.F.smooth
  obtain ⟨χ, hχ, -⟩ := exists_flat_quasiFinite (LowChart.toO C.F C.T.r) (C.T.r * C.h + C.h * (C.h + 1) / 2)
    (smoothOfRelativeDimension_comp _ _ (LowChart.powA C.F C.T.r).hom C.F.s) (C.u (closedPoint C.W))
  haveI := finiteType_int_mvPolynomial (cycAway n) (Fin (C.T.r * C.h + C.h * (C.h + 1) / 2))
  haveI := finiteType_int_mvPolynomial (MvPolynomial (Fin (C.T.r * C.h + C.h * (C.h + 1) / 2)) (cycAway n)) (Fin C.m ⊕ Fin C.N)
  refine ringKrullDim_stalk_le (π ≫ z) j hD F.s _ F.smooth _ ((flat_map (hχ.comp C.u_et.1)).comp C.compl.2.2.1) ?_ _ hf
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card, Fintype.card_fin, card_basis C.ε, add_assoc, ← Nat.cast_add]
  congr 2
  obtain ⟨a, ha⟩ := Nat.even_mul_succ_self C.h
  obtain ⟨b, hb⟩ := Nat.even_mul_succ_self C.T.r
  have : (C.h + C.T.r) * (C.h + C.T.r + 1) = C.h * (C.h + 1) + C.T.r * (C.T.r + 1) + 2 * (C.T.r * C.h) := by ring
  rw [C.genus] at this
  omega

end GlobalTheory.TChart.ChartDim
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingKrullDimStalkLeTautologicalChartRingStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringKrullDim_stalk_le_tautologicalChartRing : ∀ g : ℕ, 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ → NoSelfInt id g φ → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) (d : ℕ) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), MinAt5 F z i OZ → BlowAt F z i φ d π j BD → ∀ (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (y : Sp (FractionRing C.R) ⟶ F.X) (α₁ : pullback G₁.hom (jK C.R) ⟶ F.univ.A.left) (ξ : Sp C.R ⟶ S), C.IsFam F G₁ y α₁ → y ≫ j = jK C.R ≫ ξ → ((residue C.R).comp (Scheme.stalkClosedPointTo ξ).hom).Finite → ringKrullDim (S.presheaf.stalk (ξ (closedPoint C.R))) ≤ ringKrullDim C.R := by
  first | exact @GlobalTheory.TChart.ChartDim.ringKrullDim_stalk_le_chart | exact GlobalTheory.TChart.ChartDim.ringKrullDim_stalk_le_chart | (intros; apply GlobalTheory.TChart.ChartDim.ringKrullDim_stalk_le_chart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalChartCentreIsCompletedEtaleLocalMap
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChartEt

theorem injective_of_flat_isLocalHom {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (f : A →+* B) (hf : f.Flat) [hl : IsLocalHom f] : Function.Injective f := by
  algebraize [f]
  have : IsLocalHom (algebraMap A B) := hl
  have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := A) (B := B)
  exact FaithfulSMul.algebraMap_injective A B

theorem charZero_stalk_of_flat {o : Type} [CommRing o] [IsDomain o] [CharZero o] (X : Scheme.{0}) (s : X ⟶ Sp o)
    [Flat s] (x : X) : CharZero (X.presheaf.stalk x) := by
  have hf : (s.stalkMap x).hom.Flat := Flat.stalkMap s x
  have h0 : CharZero ((Sp o).presheaf.stalk (s x)) := by
    have : CharZero Γ(Sp o, ⊤) := (Scheme.ΓSpecIso (.of o)).hom.hom.charZero
    exact charZero_of_injective_ringHom (f := ((Sp o).presheaf.germ ⊤ (s x) trivial).hom)
      (germ_injective_of_isIntegral (Sp o) (U := ⊤) (s x) trivial)
  exact charZero_of_injective_ringHom (injective_of_flat_isLocalHom _ hf)

theorem essFiniteType_int_stalk (n : ℕ) (X : Scheme.{0}) (s : X ⟶ Sp (cycAway n)) [LocallyOfFiniteType s] (x : X) :
    Algebra.EssFiniteType ℤ (X.presheaf.stalk x) := by
  have h1 : (s.stalkMap x).hom.EssFiniteType := LocallyOfFiniteType.stalkMap s x
  let p : PrimeSpectrum (cycAway n) := s x
  have h2 : (algebraMap (cycAway n) ((Spec.structureSheaf (cycAway n)).presheaf.stalk p)).EssFiniteType :=
    RingHom.essFiniteType_algebraMap.2 (Algebra.EssFiniteType.of_isLocalization _ p.asIdeal.primeCompl)
  haveI := finiteType_cycAway n
  have h3 : (algebraMap ℤ (cycAway n)).EssFiniteType := RingHom.essFiniteType_algebraMap.2 inferInstance
  have h4 := (h3.comp h2).comp h1
  rw [← RingHom.essFiniteType_algebraMap]
  convert h4
  exact RingHom.ext_int _ _

theorem charZero_stalk_centre {g n : ℕ} (F : SFam g n (zetaAway n)) {S : Scheme.{0}} (j : F.X ⟶ S)
    {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (y : Sp (FractionRing R) ⟶ F.X) (ξ : Sp R ⟶ S)
    (hy : y ≫ j = jK R ≫ ξ) : CharZero (S.presheaf.stalk (ξ (closedPoint R))) := by
  haveI := F.smooth
  haveI : Smooth F.s := SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) F.s
  haveI : Flat F.s := inferInstance
  let w : Sp (FractionRing R) := closedPoint (FractionRing R)
  have hsp : ξ (jK R w) ⤳ ξ (closedPoint R) := (specializes_closedPoint _).map ξ.continuous
  have hjw : j (y w) = ξ (jK R w) := by
    rw [← Scheme.Hom.comp_apply, hy, Scheme.Hom.comp_apply]
  haveI : CharZero (F.X.presheaf.stalk (y w)) := charZero_stalk_of_flat F.X F.s (y w)
  haveI h₁ : CharZero (S.presheaf.stalk (j (y w))) := (j.stalkMap (y w)).hom.charZero
  rw [hjw] at h₁
  exact (S.presheaf.stalkSpecializes hsp).hom.charZero

end GlobalTheory.TChartEt

namespace GlobalTheory.TChartEt

theorem isEtaleCompletion_tautChart : GlobalTheory.Poinc.Sep.SepSt → ∀ g : ℕ, 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ → NoSelfInt id g φ → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) (d : ℕ) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), MinAt5 F z i OZ → BlowAt F z i φ d π j BD → ∀ (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (y : Sp (FractionRing C.R) ⟶ F.X) (α₁ : pullback G₁.hom (jK C.R) ⟶ F.univ.A.left) (ξ : Sp C.R ⟶ S), C.IsFam F G₁ y α₁ → y ≫ j = jK C.R ≫ ξ → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom ∧ ((residue C.R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified := by
  intro hSep g hg φ hφ hns n hn ho F Z z i OZ d S π j _ BD hM hB C G₁ _ _ y α₁ ξ hF hy
  obtain ⟨J, h₁, h₂, h₃, hNB, hP, h₄⟩ := hB
  haveI : GlobalTheory.IsNormalScheme S := hNB.1
  haveI : CharZero (S.presheaf.stalk (ξ (closedPoint C.R))) := charZero_stalk_centre F j y ξ hy
  haveI : LocallyOfFiniteType (π ≫ z) := by
    obtain ⟨N, ιP, hιP, e⟩ := hP
    rw [← e]
    haveI := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str (cycAway n) N
    infer_instance
  haveI : Algebra.EssFiniteType ℤ (S.presheaf.stalk (ξ (closedPoint C.R))) :=
    essFiniteType_int_stalk n S (π ≫ z) _
  haveI : IsNoetherianRing C.R := C.compl.1
  obtain ⟨hqf, hfin⟩ := GlobalTheory.T.quasiFinite_tautologicalChart_of_separation hSep g hg φ hφ hns n hn ho F Z z i OZ d S π j BD hM
    ⟨J, h₁, h₂, h₃, hNB, hP, h₄⟩ C G₁ y α₁ ξ hF hy
  have hdim := GlobalTheory.T.ringKrullDim_stalk_le_tautologicalChartRing g hg φ hφ hns n hn ho F Z z i OZ d S π j BD hM
    ⟨J, h₁, h₂, h₃, hNB, hP, h₄⟩ C G₁ y α₁ ξ hF hy hfin
  have hgal := GlobalTheory.T.tautologicalChart_galois_rigid_stalk hn F S j C G₁ y α₁ ξ hF hy
  exact GlobalTheory.T.isEtaleCompletion_of_quasiFinite_galoisRigid _ _ (Scheme.stalkClosedPointTo ξ).hom C.compl.2.1 hqf hfin hdim hgal

end GlobalTheory.TChartEt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalChartCentreIsCompletedEtaleLocalMapStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tautologicalChart_centre_isCompletedEtaleLocalMap : GlobalTheory.Poinc.Sep.SepSt → ∀ g : ℕ, 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ → NoSelfInt id g φ → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) (d : ℕ) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), MinAt5 F z i OZ → BlowAt F z i φ d π j BD → ∀ (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (y : Sp (FractionRing C.R) ⟶ F.X) (α₁ : pullback G₁.hom (jK C.R) ⟶ F.univ.A.left) (ξ : Sp C.R ⟶ S), C.IsFam F G₁ y α₁ → y ≫ j = jK C.R ≫ ξ → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom ∧ ((residue C.R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified := by
  first | exact @GlobalTheory.TChartEt.isEtaleCompletion_tautChart | exact GlobalTheory.TChartEt.isEtaleCompletion_tautChart | (intros; apply GlobalTheory.TChartEt.isEtaleCompletion_tautChart <;> assumption)
end
