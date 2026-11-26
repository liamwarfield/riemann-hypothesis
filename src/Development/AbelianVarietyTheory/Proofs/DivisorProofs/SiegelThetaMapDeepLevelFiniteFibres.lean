module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePointsCycAway
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSymmetricFunctionsDegreeFactorialBasicPrope
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinJetSmulDirection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasThetaConstantsTwoLevelsMoveCartesian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProjSpaceMapOfTupleHasDivisor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieModelIsBaseChange

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSiegelPointsE8ThetaPower
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerE8BundleIsoOfPrincipalSiegelIso
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerE8BundleIsoOfPrincipalSiegelIso
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.SiegLev GlobalTheory.SiegLevCalc GlobalTheory.SiegelPullComp GlobalTheory.SiegelPull
open GlobalTheory.CechPic

noncomputable section

namespace GlobalTheory.SharpIso

theorem iso_of_sRel : ∀ (g n N : ℕ) (B : Type) [CommRing B] (ζ : B) (K : Type) [Field K] (s : Sp K ⟶ Sp B) (c : SiegPre g n ζ s) (b : TBase K N) (C : SiegPre g N (b.ζ : K) (𝟙 (Sp K))) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * (8 * g)) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin g ⊕ Fin g → ℤ))) (t : TObj (8 * g) N J b (𝟙 (Sp K))) (Q : PolAV (Sp K)) (pr : Fin 8 → (Q.A ⟶ c.A)), (∀ u, IsMonHom (pr u)) → (∀ (T' : Over (Sp K)) (y : Fin 8 → (T' ⟶ c.A)), ∃! x : T' ⟶ Q.A, ∀ u, x ≫ pr u = y u) → LBIso Q.L (LB.LinComb c.P (K := Fin 8 × Fin 8) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)) → SRel C c 0 0 (𝟙 _) → IsSharp W a bas t C → ∃ φ : t.A ≅ Q.A, IsMonHom φ.hom ∧ LBIso t.L (Q.L.pull φ.hom.left) := by
  intro g n N B _ ζ K _ s c b C W J a bas t Q pr hpr huniv hQ hrel hsharp
  obtain ⟨φ, hpb, ⟨φ₂, hsq, hP⟩, -⟩ := hrel
  obtain ⟨pr', hpr', huniv', ht, -, -⟩ := hsharp
  have w : φ ≫ c.A.hom = C.A.hom := by simpa using hpb.1.w
  let f : C.A ⟶ c.A := Over.homMk φ w
  haveI : IsIso φ := hpb.1.isIso_fst_of_isIso
  haveI : IsIso f := by
    have : IsIso ((Over.forget _).map f) := by simpa [f] using (inferInstance : IsIso φ)
    exact isIso_of_reflects_iso f (Over.forget _)
  haveI hf : IsMonHom f := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isMonHom_of_mul f
    (fun _ x y => GlobalTheory.AbelianLetters.mul_comp_of_isGrpPullback_id f hpb x y)
  obtain ⟨ψ, hψ, -⟩ := huniv t.A (fun u => pr' u ≫ f)
  obtain ⟨χ, hχ, -⟩ := huniv' Q.A (fun u => pr u ≫ inv f)
  have h1 : ψ ≫ χ = 𝟙 _ := (huniv' t.A pr').unique (fun u => by
      rw [Category.assoc, hχ, ← Category.assoc, hψ, Category.assoc, IsIso.hom_inv_id, Category.comp_id])
    (fun u => Category.id_comp _)
  have h2 : χ ≫ ψ = 𝟙 _ := (huniv Q.A pr).unique (fun u => by
      rw [Category.assoc, hψ, ← Category.assoc, hχ, Category.assoc, IsIso.inv_hom_id, Category.comp_id])
    (fun u => Category.id_comp _)
  have hm : ∀ u, IsMonHom (ψ ≫ pr u) := fun u => by
    rw [hψ]; haveI := hpr' u; infer_instance
  have hψm : IsMonHom ψ := by
    refine ⟨(huniv _ fun u => η[Q.A] ≫ pr u).unique (fun u => ?_) fun _ => rfl,
      (huniv _ fun u => μ[t.A] ≫ ψ ≫ pr u).unique (fun u => Category.assoc _ _ _) fun u => ?_⟩
    · have := hm u
      have := hpr u
      rw [Category.assoc, IsMonHom.one_hom, IsMonHom.one_hom]
    · have := hm u
      have := hpr u
      rw [Category.assoc, IsMonHom.mul_hom, IsMonHom.mul_hom, ← Category.assoc, tensorHom_comp_tensorHom]
  refine ⟨⟨ψ, χ, h1, h2⟩, hψm, ?_⟩
  have hsq' : Geo.Tor.IsSquare φ (f ⊗ₘ f).left :=
    ⟨by rw [← Over.comp_left, tensorHom_fst]; rfl, by rw [← Over.comp_left, tensorHom_snd]; rfl⟩
  obtain rfl := GlobalTheory.LamPull.isSquare_unique hsq hsq'
  have key : ∀ uv : Fin 8 × Fin 8, (lift (pr' uv.1) (pr' uv.2)).left ≫ (f ⊗ₘ f).left =
      ψ.left ≫ (lift (pr uv.1) (pr uv.2)).left := fun uv => by
    rw [← Over.comp_left, ← Over.comp_left, lift_map, comp_lift, hψ, hψ]
  rw [← cls_eq_iff t.isLB (pull_isLB Q.isLB _), (cls_eq_iff t.isLB (LB.isLB_linComb C.isLB _ _)).2 ht,
    cls_linComb C.isLB, (cls_eq_iff C.isLB (pull_isLB c.isLB _)).2 hP, cls_pull c.isLB,
    cls_pull Q.isLB, (cls_eq_iff Q.isLB (LB.isLB_linComb c.isLB _ _)).2 hQ, cls_linComb c.isLB]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_zsmul, ← pull_comp, key]

end GlobalTheory.SharpIso
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerE8BundleIsoOfPrincipalSiegelIsoStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.SiegLev GlobalTheory.SiegLevCalc GlobalTheory.SiegelPullComp GlobalTheory.SiegelPull
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eighthPower_E8Bundle_iso_of_principalSiegelIso : ∀ (g n N : ℕ) (B : Type) [CommRing B] (ζ : B) (K : Type) [Field K] (s : Sp K ⟶ Sp B) (c : SiegPre g n ζ s) (b : TBase K N) (C : SiegPre g N (b.ζ : K) (𝟙 (Sp K))) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * (8 * g)) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin g ⊕ Fin g → ℤ))) (t : TObj (8 * g) N J b (𝟙 (Sp K))) (Q : PolAV (Sp K)) (pr : Fin 8 → (Q.A ⟶ c.A)), (∀ u, IsMonHom (pr u)) → (∀ (T' : Over (Sp K)) (y : Fin 8 → (T' ⟶ c.A)), ∃! x : T' ⟶ Q.A, ∀ u, x ≫ pr u = y u) → LBIso Q.L (LB.LinComb c.P (K := Fin 8 × Fin 8) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)) → SRel C c 0 0 (𝟙 _) → IsSharp W a bas t C → ∃ φ : t.A ≅ Q.A, IsMonHom φ.hom ∧ LBIso t.L (Q.L.pull φ.hom.left) := by
  first | exact @GlobalTheory.SharpIso.iso_of_sRel | exact GlobalTheory.SharpIso.iso_of_sRel | (intros; apply GlobalTheory.SharpIso.iso_of_sRel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsFiniteOfPolarisedAVIsoAlgClosed
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsFiniteOfPolarisedAVIsoAlgClosed
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.SiegLev GlobalTheory.SiegLevCalc GlobalTheory.SiegelPullComp GlobalTheory.SiegelPull

noncomputable section

namespace GlobalTheory.ThetaFiniteIso

theorem thetaPts_finite : ∀ (G N' : ℕ) (J : Type) (K : Type) [Field K] [IsAlgClosed K] (b : TBase K (N' ^ 2)) (Q : PolAV (Sp K)), Odd N' → 3 ≤ N' → ∃ V : Set (Ix G (N' ^ 2) → K), V.Finite ∧ ∀ t : TObj G (N' ^ 2) J b (𝟙 (Sp K)), (∃ φ : t.A ≅ Q.A, IsMonHom φ.hom ∧ LBIso t.L (Q.L.pull φ.hom.left)) → ∃ v ∈ V, t.HasTh (𝟙 _) v := by
  intro G N' J K _ _ b Q ho _
  haveI : NeZero (N' ^ 2) := ⟨pow_ne_zero _ ho.pos.ne'⟩
  let T : Over (Sp K) := Over.mk (𝟙 (Sp K))
  let T₀ : Over (Sp K) := Over.mk (T.hom ≫ 𝟙 (Sp K))
  let fn : K → Γ(T.left, ⊤) := fun c => (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c
  let Tor := {y : T₀ ⟶ Q.A // y ^ (N' ^ 2) = 1}
  have e : T₀ ≅ 𝟙_ (Over (Sp K)) :=
    (CartesianMonoidalCategory.isTerminalTensorUnit).uniqueUpToIso
      (IsTerminal.ofUniqueHom (fun Y => Over.homMk Y.hom (by simp [T₀, T]))
        (fun Y m => Over.OverMorphism.ext (by simpa [T₀, T] using Over.w m))) |>.symm
  haveI hTor : Finite Tor := by
    have := GlobalTheory.AbTorsionFinite.finite_torsion K Q.A Q.isAb (N' ^ 2) (Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ ho.pos.ne'))
    refine Finite.of_injective (fun y : Tor => (⟨e.inv ≫ y.1, by rw [← MonObj.comp_pow, y.2, MonObj.comp_one]⟩ :
      {x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ Q.A // x ^ (N' ^ 2) = 1})) ?_
    intro y y' h
    exact Subtype.ext ((cancel_epi e.inv).1 (congrArg Subtype.val h))
  let ch : (Ix G (N' ^ 2) → Tor) → (Ix G (N' ^ 2) → K) := fun l =>
    if h : ∃ v : Ix G (N' ^ 2) → K, IsThetaPt Q N' (fun a => (l a).1) (fun a => fn (v a)) then h.choose else 0
  refine ⟨Set.range ch, Set.finite_range ch, fun t ⟨φ, hφ, hw⟩ => ?_⟩
  haveI := hφ
  let x : Ix G (N' ^ 2) → (T ⟶ t.pol.A) := fun a => (Over.homMk (𝟙 (Sp K)) (by simp [T]) : T ⟶ Out.baseOver (Sp K)) ≫ t.lab a
  have hk : ∀ a, x a ^ (N' ^ 2) = 1 := fun a => by
    exact (MonObj.comp_pow _ _ _).symm.trans ((congrArg (_ ≫ ·) (GlobalTheory.ThetaPtUp.lab_pow t a)).trans (MonObj.comp_one _))
  let x₀ : Ix G (N' ^ 2) → (T₀ ⟶ Q.A) := fun a => Over.homMk ((x a).left ≫ φ.hom.left) (by
    exact (Category.assoc _ _ _).trans ((congrArg ((x a).left ≫ ·) (Over.w φ.hom)).trans
      ((Over.w (x a)).trans (Category.comp_id _).symm)))
  have hx : ∀ a, (x₀ a).left = (x a).left ≫ φ.hom.left := fun a => rfl
  have hp : IsGrpPullback t.pol.A Q.A (𝟙 (Sp K)) φ.hom.left := isGrpPullback_of_iso φ
  have key : ∀ v : Ix G (N' ^ 2) → K, t.HasTh (𝟙 _) v ↔ IsThetaPt Q N' x₀ (fun a => fn (v a)) := fun v =>
    GlobalTheory.ThetaPtUp.isThetaPt_iff (P := t.pol) (P₀ := Q) (T := T) hp hw hx hk _
  let r : T₀ ⟶ T := Over.homMk (𝟙 (Sp K)) (by simp [T₀, T])
  have hk₀ : ∀ a, x₀ a ^ (N' ^ 2) = 1 := fun a => by
    have e₁ : x₀ a = r ≫ x a ≫ φ.hom := Over.OverMorphism.ext (Category.id_comp _).symm
    have h2 : (x a ≫ φ.hom) ^ (N' ^ 2) = 1 := by
      have := map_pow (IsMonHom.monoidHom φ.hom T) (x a) (N' ^ 2)
      have h1 : IsMonHom.monoidHom φ.hom T (x a ^ (N' ^ 2)) = 1 := by
        erw [hk a]; exact map_one _
      exact this.symm.trans h1
    rw [e₁, ← MonObj.comp_pow, h2, MonObj.comp_one]
  let l : Ix G (N' ^ 2) → Tor := fun a => ⟨x₀ a, hk₀ a⟩
  obtain ⟨v, hv⟩ := GlobalTheory.FamRep.exists_hasTh_field GlobalTheory.firstFiveLaws.1 GlobalTheory.firstFiveLaws.2.1 ho t K (𝟙 _)
  have h : ∃ v : Ix G (N' ^ 2) → K, IsThetaPt Q N' (fun a => (l a).1) (fun a => fn (v a)) := ⟨v, (key v).1 hv⟩
  refine ⟨ch l, ⟨l, rfl⟩, (key _).2 ?_⟩
  simp only [ch, dif_pos h]
  exact h.choose_spec

end GlobalTheory.ThetaFiniteIso

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsFiniteOfPolarisedAVIsoAlgClosedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.SiegLev GlobalTheory.SiegLevCalc GlobalTheory.SiegelPullComp GlobalTheory.SiegelPull
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaConstants_finite_of_polarisedAVIso_algClosed : ∀ (G N' : ℕ) (J : Type) (K : Type) [Field K] [IsAlgClosed K] (b : TBase K (N' ^ 2)) (Q : PolAV (Sp K)), Odd N' → 3 ≤ N' → ∃ V : Set (Ix G (N' ^ 2) → K), V.Finite ∧ ∀ t : TObj G (N' ^ 2) J b (𝟙 (Sp K)), (∃ φ : t.A ≅ Q.A, IsMonHom φ.hom ∧ LBIso t.L (Q.L.pull φ.hom.left)) → ∃ v ∈ V, t.HasTh (𝟙 _) v := by
  first | exact @GlobalTheory.ThetaFiniteIso.thetaPts_finite | exact GlobalTheory.ThetaFiniteIso.thetaPts_finite | (intros; apply GlobalTheory.ThetaFiniteIso.thetaPts_finite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticLevelPrincipalSiegelAlgClosed
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticLevelPrincipalSiegelAlgClosed
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.SiegLev GlobalTheory.SiegLevCalc GlobalTheory.SiegelPullComp GlobalTheory.SiegelPull
open ReciprocityTheory.ChartRestriction.G GlobalTheory.CechPic

noncomputable section

namespace GlobalTheory.SiegLift

theorem exists_level_of_forget : ∀ (g n N : ℕ) (B : Type) [CommRing B] (ζ : B) (K : Type) [Field K] [IsAlgClosed K]
    (s : Sp K ⟶ Sp B) (c : SiegPre g n ζ s) (b : TBase K N), Odd N → 3 ≤ N → c.Principal →
    SmoothOfRelativeDimension g c.A.hom → ∃ C : SiegPre g N (b.ζ : K) (𝟙 (Sp K)), SRel C c 0 0 (𝟙 _) := by
  intro g n N B _ ζ k _ _ s c b ho hN3 hc hg
  have hL := GlobalTheory.abelianSchemeLaws_all.1
  have hG := hL.globalFns
  have hD : c.diag.IsLB := pull_isLB c.isLB _
  have hN : ((N : ℕ) : k) ≠ 0 := b.unit.ne_zero
  have hN₀ : N ≠ 0 := fun e => hN (by rw [e, Nat.cast_zero])
  have hz : IsPrimitiveRoot b.ζ N := IsPrimitiveRoot.coe_units_iff.1 (b.prim k (RingHom.id k))
  have hz₂ : IsPrimitiveRoot (b.ζ ^ 2) N := hz.pow_of_coprime 2 (Nat.coprime_two_left.2 ho)
  have card := GlobalTheory.card_torsion_geometricPoint_of_field GlobalTheory.card_torsion_abelianVariety _ c.A c.ab g hg

  obtain ⟨L, hLM, ⟨cu⟩⟩ := GlobalTheory.Moduli.cubicalStr_of_triv_theta hL _ c.A c.ab c.diag hD
    (DVR.exists_gen_of_isLB_local (V := k) _ (pull_isLB hD _))
    (GlobalTheory.exists_gen_theta_of_isAbelianScheme k c.A c.ab _ hD)
  have toW : ∀ {m : ℕ} {T : Over (Sp k)} {x y : T ⟶ c.A} {u}, UU.CubWeil cu m x y u →
      Out.WeilIs c.A c.diag m x y u := fun H => hLM ▸ (UU.cubWeil_iff_weilIs hG c.ab H.1 H.2.1 _).1 H
  obtain ⟨f₁, f₂, f₃⟩ := (GlobalTheory.ChF.exists_gen_theta_tensor_and_finite_flat_surjective_pow k c.A c.diag c.P c.ab
    hD hc.1 c.isLB).2 N (Nat.pos_of_ne_zero hN₀)
  let H : Subgroup (𝟙_ (Over (Sp k)) ⟶ c.A) := (powMonoidHom N).ker
  have hH : ∀ x : H, x.1 ^ N = 1 := fun x => x.2
  have ex : ∀ x y : H, ∃ u : kˣ, UU.CubWeil cu N x.1 y.1 (unitOn u) := fun x y => by
    obtain ⟨u, hu, -⟩ := UU.existsUnique_cubWeil cu (hH x) (hH y)
    obtain ⟨w, rfl⟩ : ∃ w : kˣ, unitOn w = u :=
      ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom.toMonoidHom u,
        Units.ext (CommRingCat.inv_hom_apply (Scheme.ΓSpecIso (CommRingCat.of k)) u.val)⟩
    exact ⟨w, hu⟩
  choose w hw using ex
  have uq : ∀ x y u, UU.CubWeil cu N x.1 y.1 (unitOn u) → w x y = u := fun x y u H =>
    SiegelOfPolarised.unitOn_inj ((hw x y).unique H)
  have l : ∀ x x' y, w (x * x') y = w x y * w x' y := fun x x' y => uq _ _ _ (by
    have := (hw x y).mul_left (hw x' y)
    unfold unitOn at this ⊢
    rwa [map_mul])
  have sk : ∀ x y, w y x = (w x y)⁻¹ := fun x y => uq _ _ _ (by
    have := (hw x y).symm
    unfold unitOn at this ⊢
    rwa [map_inv])
  have u1 : unitOn (1 : kˣ) = 1 := map_one _
  let e : H →* H →* kˣ := MonoidHom.mk' (fun x => MonoidHom.mk' (w x) fun y y' => by
    rw [sk (y * y'), l, mul_inv, ← sk, ← sk]) fun x x' => MonoidHom.ext fun y => l x x' y
  obtain ⟨l₁, add₁, w₁⟩ := exists_symplectic_hom (g := g) (Nat.pos_of_ne_zero hN₀) hz₂
    (fun x => Subtype.ext (hH x)) (fun m hm => by
      obtain ⟨r, hr⟩ := hm
      have hm : (m : k) ≠ 0 := left_ne_zero_of_mul (by rwa [hr, Nat.cast_mul] at hN)
      refine Eq.trans (Nat.card_congr ?_) (card k (𝟙 _) m hm)
      exact ⟨fun x => ⟨x.1.1, congrArg Subtype.val x.2⟩, fun x => ⟨⟨x.1, show x.1 ^ N = 1 by
        rw [hr, pow_mul, x.2, one_pow]⟩, Subtype.ext x.2⟩, fun _ => rfl, fun _ => rfl⟩)
    e (fun x => uq _ _ _ (u1 ▸ UU.cubWeil_self cu (hH x))) (fun x hx => Subtype.ext (by
      have t := GlobalTheory.CubNondeg.main hL _ c.A c.ab L cu k (𝟙 _) N hN f₁ f₂ f₃ x.1 (hH x) fun y hy => by
        have := hw x ⟨y, hy⟩
        rwa [show w x ⟨y, hy⟩ = 1 from hx ⟨y, hy⟩, u1] at this
      rw [hLM] at t
      have s₂ : x.1 ^ 2 = 1 := sq_eq_one_of_translDiff c hc (𝟙 _) x.1 t
      exact (pow_eq_one_iff_of_coprime (Nat.coprime_two_left.2 ho)).1 ⟨s₂, hH x⟩))
  let l₂ : (Fin g ⊕ Fin g → ℤ) → (𝟙_ (Over (Sp k)) ⟶ c.A) := fun a => (l₁ a).1
  have add₂ : ∀ a a', l₂ (a + a') = l₂ a * l₂ a' := fun a a' => congrArg Subtype.val (add₁ a a')
  have tors₂ : ∀ a, l₂ a ^ N = 1 := fun a => hH _
  have w₂ : ∀ a a', UU.CubWeil cu N (l₂ a) (l₂ a') (unitOn ((b.ζ ^ 2) ^ omegaStd a a')) := fun a a' =>
    (show w (l₁ a) (l₁ a') = _ from w₁ a a') ▸ hw (l₁ a) (l₁ a')

  have mk : ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (x : Sp k' ⟶ Sp k) (β : k →+* k') (z : k'ˣ),
        x ≫ 𝟙 _ = spMap β → (z : k') = β b.ζ →
        (∀ a, (toUnit (Over.mk x) ≫ l₂ a = 1 ↔ ∃ v, a = N • v)) ∧
        (∀ y : Over.mk x ⟶ c.A, y ^ N = 1 → ∃ a, toUnit _ ≫ l₂ a = y) ∧
        ∀ a a', Out.WeilIs c.A c.diag (N : ℕ) (toUnit (Over.mk x) ≫ l₂ a) (toUnit _ ≫ l₂ a')
          (unitOn (z ^ (2 * omegaStd a a'))) := by
    intro k' _ _ x β z hx hzz
    obtain rfl : x = spMap β := (Category.comp_id _).symm.trans hx
    obtain rfl : z = Units.map β.toMonoidHom b.ζ := Units.ext hzz
    have hz' : IsPrimitiveRoot (Units.map β.toMonoidHom (b.ζ ^ 2)) N :=
      hz₂.map_of_injective (Units.map_injective β.injective)
    have hk' : ((N : ℕ) : k') ≠ 0 := by rw [← map_natCast β]; exact (map_ne_zero β).2 hN
    have W : ∀ a a', UU.CubWeil cu N (toUnit (Over.mk (spMap β)) ≫ l₂ a) (toUnit _ ≫ l₂ a')
        (unitOn (Units.map β.toMonoidHom (b.ζ ^ 2) ^ omegaStd a a')) := fun a a' => by
      have H := (w₂ a a').comp (toUnit (Over.mk (spMap β)))
      have e : Units.map (toUnit (Over.mk (spMap β))).left.appTop.hom.toMonoidHom
          (unitOn ((b.ζ ^ 2) ^ omegaStd a a')) = unitOn (Units.map β.toMonoidHom ((b.ζ ^ 2) ^ omegaStd a a')) :=
        Units.ext (congrArg (fun q => q.hom ((b.ζ ^ 2) ^ omegaStd a a').val)
          (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β))).symm
      rw [e, map_zpow] at H
      exact H
    have ker : ∀ a, toUnit (Over.mk (spMap β)) ≫ l₂ a = 1 → ∃ v, a = N • v := fun a ha =>
      SiegelOfPolarised.exists_smul_of_dvd fun a' => by
        have w₁ := W a a'
        rw [ha] at w₁
        have e := SiegelOfPolarised.unitOn_inj
          ((w₁.unique (UU.cubWeil_one_left cu w₁.2.1)).trans (map_one _).symm)
        exact (hz'.zpow_eq_one_iff_dvd _).1 e
    refine ⟨fun a => ⟨ker a, ?_⟩, SiegelOfPolarised.onto_torsion hN₀ _ (fun a b => by rw [add₂, MonObj.comp_mul])
      (fun a => by rw [← MonObj.comp_pow, tors₂, MonObj.comp_one]) ker ?_, fun a a' => ?_⟩
    · rintro ⟨v, rfl⟩
      have pw : ∀ m : ℕ, l₂ (m • v) = l₂ v ^ m := fun m => by
        induction m with
        | zero => rw [zero_smul, pow_zero]; exact mul_eq_left.1 ((add₂ 0 0).symm.trans (by rw [add_zero]))
        | succ m ih => rw [succ_nsmul, add₂, ih, pow_succ]
      rw [pw, tors₂, MonObj.comp_one]
    · rw [card k' _ _ hk']
      simp [two_mul]
    · have H := toW (W a a')
      rwa [map_pow, ← zpow_ofNat, ← zpow_mul] at H
  refine ⟨{ A := c.A
            ab := c.ab
            P := c.P
            isLB := c.isLB
            rig₁ := c.rig₁
            rig₂ := c.rig₂
            symm := c.symm
            lev := l₂
            lev_add := add₂
            lev_tors := tors₂
            geom := mk },
    𝟙 _, @isGrpPullback_of_iso _ _ _ _ _ (Iso.refl c.A) (inferInstanceAs (IsMonHom (𝟙 c.A))),
    ⟨𝟙 _, ⟨by simp, by simp⟩, ?_⟩, fun a => ?_⟩
  · exact (CechPic.cls_eq_iff c.isLB (pull_isLB c.isLB _)).1
      ((CechPic.pull_id _).symm.trans (CechPic.cls_pull c.isLB _ _).symm)
  · simp

end GlobalTheory.SiegLift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticLevelPrincipalSiegelAlgClosedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.SiegLev GlobalTheory.SiegLevCalc GlobalTheory.SiegelPullComp GlobalTheory.SiegelPull
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symplecticLevel_principalSiegel_algClosed : ∀ (g n N : ℕ) (B : Type) [CommRing B] (ζ : B) (K : Type) [Field K] [IsAlgClosed K] (s : Sp K ⟶ Sp B) (c : SiegPre g n ζ s) (b : TBase K N), Odd N → 3 ≤ N → c.Principal → SmoothOfRelativeDimension g c.A.hom → ∃ C : SiegPre g N (b.ζ : K) (𝟙 (Sp K)), SRel C c 0 0 (𝟙 _) := by
  first | exact @GlobalTheory.SiegLift.exists_level_of_forget | exact GlobalTheory.SiegLift.exists_level_of_forget | (intros; apply GlobalTheory.SiegLift.exists_level_of_forget <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSiegelPointsE8ThetaPower
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.SharpFiniteTh
open GlobalTheory.SiegLev GlobalTheory.SiegLevCalc GlobalTheory.SiegelPullComp GlobalTheory.SiegelPull

theorem finite_sharpOver : ∀ (g n : ℕ), 2 ≤ n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (K : Type) [Field K] [IsAlgClosed K] (Q : PolAV (Sp K)), Set.Finite {y : Sp K ⟶ F.X | GlobalTheory.Poinc.SharpOver F W Q y} := by
  intro g n hn2 F W hW K _ _ Q
  have hn : n ≠ 0 := by omega
  have hζ : IsUnit (zetaAway n) := by rw [← cycBase_ζ hn]; exact Units.isUnit _
  obtain ⟨ℓ, hℓ, hodd, hℓK⟩ : ∃ ℓ : ℕ, ℓ.Prime ∧ Odd ℓ ∧ (ℓ : K) ≠ 0 := by
    by_cases h3 : ((3 : ℕ) : K) = 0
    · refine ⟨5, by norm_num, by decide, fun h5 => ?_⟩
      have h2 : (2 : K) = 0 := by
        have e : ((5 : ℕ) : K) - ((3 : ℕ) : K) = 0 := by rw [h5, h3, sub_zero]
        push_cast at e; linear_combination e
      have h1 : (1 : K) = 0 := by
        have e : ((3 : ℕ) : K) - 2 = 0 := by rw [h3, h2, sub_zero]
        push_cast at e; linear_combination e
      exact one_ne_zero h1
    · exact ⟨3, Nat.prime_three, by decide, h3⟩
  obtain ⟨hL, hL2⟩ := abelianSchemeLaws_all
  obtain ⟨bas, hbas⟩ := GlobalTheory.SiegEighth.exists_isSharpBasis g W hW
  let a : Fin 8 × Fin 8 → Matrix (Fin 8) (Fin 8) ℤ := fun uv => Matrix.single uv.1 uv.2 1
  have he : ∀ u v : Fin 8, ∃ j : Fin 8 × Fin 8, a j = Matrix.single u v 1 := fun u v => ⟨(u, v), rfl⟩
  obtain ⟨Mat, κ, hsh⟩ := GlobalTheory.ThetaQuasiFinite.exists_shape hL hW a bas
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.ThetaQuasiFinite.tMap_of_hasTh hL hL2 (Fin 8 × Fin 8) Mat κ ℓ hℓ hodd
  set N' := ℓ ^ (j₀ + 1) with hN'
  have hN'odd : Odd N' := hodd.pow
  have hN'3 : 3 ≤ N' := le_trans (by have := hℓ.two_le; rcases hodd with ⟨r, hr⟩; omega) (Nat.le_self_pow (by omega) ℓ)
  set N := N' ^ 2 with hN
  have hNodd : Odd N := hN'odd.pow
  have hN3 : 3 ≤ N := le_trans hN'3 (Nat.le_self_pow (by omega) N')
  have hNK : ((N : ℕ) : K) ≠ 0 := by
    rw [hN, hN', Nat.cast_pow, Nat.cast_pow]; exact pow_ne_zero _ (pow_ne_zero _ hℓK)
  haveI : NeZero ((N : ℕ) : K) := ⟨hNK⟩
  obtain ⟨z0, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K N
  have hz0 : z0 ≠ 0 := hz.ne_zero (by omega)
  let b : TBase K N := ⟨Units.mk0 z0 hz0, hNK.isUnit, fun K' _ β => hz.map_of_injective β.injective⟩
  have hbζ : b.ζ ^ N = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hz.pow_eq_one)
  have key : ∀ y : Sp K ⟶ F.X, GlobalTheory.Poinc.SharpOver F W Q y → ∃ (C : SiegPre g N (b.ζ : K) (𝟙 (Sp K)))
      (t : TObj (8 * g) N (Fin 8 × Fin 8) b (𝟙 (Sp K))), C.Principal ∧ SRel C F.univ 0 0 y ∧ IsSharp W a bas t C ∧
      ∃ φ : t.A ≅ Q.A, IsMonHom φ.hom ∧ LBIso t.L (Q.L.pull φ.hom.left) := by
    intro y hy
    obtain ⟨c, hc, pr, hpr, huniv, hiso⟩ := hy
    have hc0 := GlobalTheory.ThetaQuasiFinite.sRel_zero_of_siegPB hc
    have hcP : c.Principal := sRel_principal hc0 F.princ
    have hd : SmoothOfRelativeDimension g c.A.hom := GlobalTheory.SiegSharpCover.smoothDim c hn2 hζ (isUnit_natCast hn)
    obtain ⟨C, hC⟩ := GlobalTheory.T.exists_symplecticLevel_principalSiegel_algClosed g n N _ _ K _ c b hNodd hN3 hcP hd
    have hCP : C.Principal := sRel_principal hC hcP
    obtain ⟨t, ht⟩ := GlobalTheory.SiegelPower.exists_tObj_isSharp hL hL2 g (8 * g) W _ a bas hW hbas N K b (Sp K) (𝟙 _) C hNodd hN3 hbζ hCP
    have hCF : SRel C F.univ 0 0 y := by simpa using sRel_comp hc0 hC
    exact ⟨C, t, hCP, hCF, ht, GlobalTheory.T.eighthPower_E8Bundle_iso_of_principalSiegelIso g n N _ _ K _ c b C W _ a bas t Q pr hpr huniv hiso hC ht⟩
  obtain ⟨V, hVf, hV⟩ := GlobalTheory.T.thetaConstants_finite_of_polarisedAVIso_algClosed (8 * g) N' (Fin 8 × Fin 8) K b Q hN'odd hN'3
  have := GlobalTheory.ThetaQuasiFinite.finite_points_cycAway hn K
  let T : (Ix (8 * g) N → K) → (Sp K ⟶ Sp (cycAway n)) → Set (Sp K ⟶ F.X) := fun v x₀ =>
    {y | y ≫ F.s = x₀ ∧ ∃ (C : SiegPre g N (b.ζ : K) (𝟙 (Sp K))) (t : TObj (8 * g) N (Fin 8 × Fin 8) b (𝟙 (Sp K))),
      C.Principal ∧ SRel C F.univ 0 0 y ∧ IsSharp W a bas t C ∧ t.HasTh (𝟙 _) v}
  have hT : ∀ v x₀, (T v x₀).Finite := by
    intro v x₀
    rcases (T v x₀).eq_empty_or_nonempty with h0 | ⟨y₀, -, C₀, t₀, hC₀, -, H₀, hv₀⟩
    · rw [h0]; exact Set.finite_empty
    refine (GlobalTheory.ThetaQuasiFinite.finite_of_fibre (Nat.one_le_iff_ne_zero.2 hn) F K x₀ C₀).subset ?_
    rintro y ⟨hx, C, t, hC, hCF, H, hv⟩
    have hNz : N ≠ 0 := by omega
    have m := hj₀ (j₀ + 1) (by omega) K b K (𝟙 _) t t₀ v (hsh N hNz K b (Sp K) (𝟙 _) C t hC H)
      (hsh N hNz K b (Sp K) (𝟙 _) C₀ t₀ hC₀ H₀) hv hv₀
    have p := PowerPullback.backward hL.globalFns hW hC hC₀ H H₀ he m
    have := sRel_comp hCF (GlobalTheory.ThetaQuasiFinite.sRel_zero_of_siegPB p)
    exact ⟨hx, by simpa using this⟩
  refine (Set.Finite.biUnion hVf fun v _ => Set.finite_iUnion fun x₀ => hT v x₀).subset ?_
  intro y hy
  obtain ⟨C, t, hC, hCF, H, φ⟩ := key y hy
  obtain ⟨v, hvV, hv⟩ := hV t φ
  exact Set.mem_biUnion hvV (Set.mem_iUnion.2 ⟨y ≫ F.s, rfl, C, t, hC, hCF, H, hv⟩)

end GlobalTheory.SharpFiniteTh
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSiegelPointsE8ThetaPowerStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_siegelPoints_e8ThetaPower : ∀ (g n : ℕ), 2 ≤ n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (K : Type) [Field K] [IsAlgClosed K] (Q : PolAV (Sp K)), Set.Finite {y : Sp K ⟶ F.X | GlobalTheory.Poinc.SharpOver F W Q y} := by
  first | exact @GlobalTheory.SharpFiniteTh.finite_sharpOver | exact GlobalTheory.SharpFiniteTh.finite_sharpOver | (intros; apply GlobalTheory.SharpFiniteTh.finite_sharpOver <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelThetaMapDeepLevelFiniteFibres
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SiegThQF

theorem sharpOver_of_polIso {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {K : Type} [Field K]
    {Q Q' : PolAV (Sp K)} {y : Sp K ⟶ F.X} (φ : Q'.A ≅ Q.A) (hφ : IsPolIso Q' Q φ) (h : GlobalTheory.Poinc.SharpOver F W Q y) :
    GlobalTheory.Poinc.SharpOver F W Q' y := by
  have := hφ.1
  obtain ⟨t, ht⟩ := hφ.2
  have h1 : LBIso Q'.L (Q.L.pull φ.hom.left) := LBIso.symm ⟨t, ht⟩
  simpa using GlobalTheory.Poinc.sharpOver_pullback g n _ _ F W _ _ Q Q' y (𝟙 _) φ.hom.left h (isGrpPullback_of_iso φ) h1

theorem finite_sharp (g n : ℕ) (hn : 2 ≤ n) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (hW : IsE8 W)
    (K : Type) [Field K] [IsAlgClosed K] (Q : PolAV (Sp K)) :
    Set.Finite {y : Sp K ⟶ F.X | GlobalTheory.Poinc.SharpOver F W Q y} :=
  GlobalTheory.T.finite_siegelPoints_e8ThetaPower g n (by omega) F W hW K Q

def ThData {g n : ℕ} (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) {K : Type} [Field K] (y : Sp K ⟶ F.X)
    (h m : ℕ) (ze : Γ(Sp K, ⊤)ˣ) (v : (Fin (2 * h) → ZMod (m ^ 2)) → Γ((baseOver (Sp K)).left, ⊤)) : Prop :=
  ∃ (Q : PolAV (Sp K)) (hg : Q.g = h) (lev : Out.Level Q (m ^ 2) ze),
    GlobalTheory.Poinc.SharpOver F W Q y ∧ IsThetaPt Q m (levelPoint lev hg) v

theorem finite_thData {g n : ℕ} (hn : 2 ≤ n) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (hW : IsE8 W)
    (ℓ h j : ℕ) (hℓ : ℓ.Prime) (ho : Odd ℓ) (hj : 4 ≤ j) (hbig : ((ℓ ^ 2) ^ 2) ^ h * h.factorial < ℓ ^ j)
    (K : Type) [Field K] [IsAlgClosed K] (hl : ((ℓ : ℕ) : K) ≠ 0) (ze : Γ(Sp K, ⊤)ˣ)
    (v : (Fin (2 * h) → ZMod ((ℓ ^ j) ^ 2)) → Γ((baseOver (Sp K)).left, ⊤)) :
    Set.Finite {y : Sp K ⟶ F.X | ThData F W y h (ℓ ^ j) ze v} := by
  by_cases hne : ∃ y₀ : Sp K ⟶ F.X, ThData F W y₀ h (ℓ ^ j) ze v
  · obtain ⟨y₀, Q₀, hg₀, lev₀, -, hθ₀⟩ := hne
    refine (finite_sharp g n hn F W hW K Q₀).subset ?_
    rintro y ⟨Q, hg, lev, hS, hθ⟩
    have hN' : ℓ ^ j = ℓ ^ (j - 4) * (ℓ ^ 2) ^ 2 := by
      rw [← pow_mul, ← pow_add]; congr 1; omega
    obtain ⟨φ, hφ, -⟩ := (GlobalTheory.thetaPtDetermines_and_endDeterminedOnTorsion).1 h ℓ 2 (j - 4) ((ℓ ^ 2) ^ 2) (ℓ ^ j)
      hℓ ho le_rfl rfl hN' hbig K hl Q₀ Q hg₀ hg ze lev₀ lev v hθ₀ hθ
    exact sharpOver_of_polIso φ hφ hS
  · exact (Set.finite_empty : (∅ : Set (Sp K ⟶ F.X)).Finite).subset
      (by intro y hy; exact False.elim (hne ⟨y, hy⟩))

theorem finite_fibres : ∀ (ℓ : ℕ), ℓ.Prime → Odd ℓ → ∀ (g : ℕ), ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ℓ ∣ n → ∀ (P : PolAV F.X) (rig : LB.Gen (P.L.pull (eSec P.A))) (N : ℕ) (f : F.X ⟶ PSpace (cycAway n) N), ThAt F W P rig (ℓ ^ j) f → QFin f := by
  intro ℓ hℓ ho g
  refine ⟨4 + ((ℓ ^ 2) ^ 2) ^ (8 * g) * (8 * g).factorial, fun j hj n _ hn3 _ F W hW _ P rig N f hth K _ _ x => ?_⟩
  obtain ⟨hPg, hSh, hrig, hmo, -, hmu, hN, -, hmap⟩ := hth
  have hn : 2 ≤ n := by omega
  have hj4 : 4 ≤ j := by omega
  have hbig : ((ℓ ^ 2) ^ 2) ^ (8 * g) * (8 * g).factorial < ℓ ^ j :=
    lt_of_lt_of_le (by omega : ((ℓ ^ 2) ^ 2) ^ (8 * g) * (8 * g).factorial < j) (Nat.lt_pow_self hℓ.one_lt).le
  obtain ⟨β0, -⟩ := GlobalTheory.ThetaQuasiFinite.exists_spMap (x ≫ F.s)
  have hm0 : ((ℓ ^ j : ℕ) : K) ≠ 0 := by
    have := hmu.map β0
    rw [map_natCast] at this
    exact this.ne_zero
  have hl0 : ((ℓ : ℕ) : K) ≠ 0 := fun h0 => hm0 (by rw [Nat.cast_pow, h0, zero_pow (by omega)])
  have hpos : 0 < (ℓ ^ j) ^ 2 := pow_pos (pow_pos hℓ.pos _) _
  haveI : NeZero (((ℓ ^ j) ^ 2 : ℕ) : K) := ⟨by rw [Nat.cast_pow]; exact pow_ne_zero _ hm0⟩
  obtain ⟨z0, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K ((ℓ ^ j) ^ 2)
  let eK := (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm
  have hz' := hz.map_of_injective eK.injective
  set ze : Γ(Sp K, ⊤)ˣ := (hz'.isUnit hpos.ne').unit with hzedef
  have hze : IsPrimitiveRoot ze ((ℓ ^ j) ^ 2) := hz'.isUnit_unit hpos.ne'
  obtain ⟨⟨e, he⟩, -⟩ := (GlobalTheory.T.projectiveHomogeneousCoords_basic_properties).2.2 (cycAway n) K N (x ≫ f)
  obtain ⟨T, hT⟩ := GlobalTheory.T.thetaSymmetricFunctionsDegreeFactorial_scaled_finite K (N + 1) e
  haveI := P.isAb.comm
  haveI : NeZero ((ℓ ^ j) ^ 2) := ⟨hpos.ne'⟩
  refine (Set.finite_iUnion fun d : T × ((Fin (2 * (8 * g)) → ZMod ((ℓ ^ j) ^ 2)) → Fin (N + 1)) =>
    finite_thData hn F W hW ℓ (8 * g) j hℓ ho hj4 hbig K hl0 ze
      (fun a => GlobalTheory.ZH.fn ((d.1 : Fin (N + 1) → K) (d.2 a)))).subset ?_
  intro y hy
  have hy' : y ≫ f = x ≫ f := hy
  obtain ⟨Q, α, hQg, hpb, hQL⟩ := GlobalTheory.PureType.exists_baseChange GlobalTheory.abelianSchemeLaws_all.1.polBaseChange y P
  have hQg' : Q.g = 8 * g := hQg.trans hPg
  have hfib : PolFib P.A P.L (8 * g) (y ≫ 𝟙 F.X) := ⟨Q, α, hQg', by rwa [Category.comp_id], hQL⟩
  obtain ⟨⟨θ, hθ⟩, -⟩ := GlobalTheory.T.principallyPolarisedFibre_exists_generator_stable _ P.A P.L P.isLB (8 * g) K _ hfib
  obtain ⟨pt, cy, hcy⟩ := GlobalTheory.T.exists_thetaConstantList_algClosed _ P.A P.L rig P.isLB hrig (8 * g) (ℓ ^ j) (N + 1) K _ θ hmo hm0 hN hfib
  have hH : HasTh P.A P.L rig (ℓ ^ j) (y ≫ 𝟙 F.X) cy := ⟨θ, pt, hθ, hcy⟩
  have hP1 : PCrd (y ≫ f) (symTup cy) := hmap.1 K y cy hH
  rw [hy'] at hP1
  obtain ⟨a, ha0, ha⟩ := (GlobalTheory.T.projectiveHomogeneousCoords_field_determine_descend).2.1 (cycAway n) K N (x ≫ f) e (symTup cy) he hP1
  obtain ⟨mu, hmu0, hmuT⟩ := hT cy a ha0 ha
  haveI := Q.isAb.comm
  obtain ⟨rigQ, hrigQ⟩ := Q.rigid
  have hQ : HasTh Q.A Q.L rigQ (ℓ ^ j) (𝟙 (Sp K)) cy := by
    rw [hasTh_iff] at hH ⊢
    refine (GlobalTheory.T.hasThetaConstantsTwoLevels_move_cartesian _ P.A P.L rig P.isLB hrig (Sp K) Q.A Q.L rigQ y α Q.isLB hrigQ hpb hQL (ℓ ^ j) (ℓ ^ j)
      (N + 1) (N + 1) K (𝟙 _) cy cy).2 ?_
    simpa only [Category.id_comp, Category.comp_id] using hH
  obtain ⟨lev, β, hβ⟩ := GlobalTheory.T.exists_level_thetaPoint_of_thetaConstants_level_square K Q rigQ (8 * g) (ℓ ^ j) (N + 1) hQg' cy ze hrigQ hmo hm0 hze hQ
  have hSQ : GlobalTheory.Poinc.SharpOver F W Q y := by
    simpa using GlobalTheory.Poinc.sharpOver_pullback g n _ _ F W _ _ P Q (𝟙 F.X) y α hSh hpb hQL
  exact Set.mem_iUnion.2 ⟨(⟨_, hmuT⟩, β), Q, hQg', lev, hSQ, hβ mu hmu0⟩

end GlobalTheory.SiegThQF
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelThetaMapDeepLevelFiniteFibresStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelThetaMap_deepLevel_finite_fibres : ∀ (ℓ : ℕ), ℓ.Prime → Odd ℓ → ∀ (g : ℕ), ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ℓ ∣ n → ∀ (P : PolAV F.X) (rig : LB.Gen (P.L.pull (eSec P.A))) (N : ℕ) (f : F.X ⟶ PSpace (cycAway n) N), ThAt F W P rig (ℓ ^ j) f → QFin f := by
  first | exact @GlobalTheory.SiegThQF.finite_fibres | exact GlobalTheory.SiegThQF.finite_fibres | (intros; apply GlobalTheory.SiegThQF.finite_fibres <;> assumption)
end
