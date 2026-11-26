module

public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProperOfIsProjBy
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullDegCancelTowerOfFields
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaEmbeddingSectionsBaseChangeAffine

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LiftConnectedOfTrivialUnique
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.TrivDescentCompare

section General

theorem smooth_conn {S : Scheme.{0}} {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] {G : Over S}
    [GrpObj G] (Q : TQ G X) : Smooth G.hom ∧ GeometricallyConnected G.hom := by
  have := Q.q_hom
  have := Q.isAb.smooth
  have := Q.isAb.geomConnected
  have hs := Q.smooth_proj_of_free
  have : TwoUniqueSums X := twoUniqueSums_of_free X
  have sq := (H1.torsor_pullback Q.i Q.q Q.isKernel).map (Over.forget _)
  have hc : GeometricallyConnected Q.q.left := by
    have h₁ : GeometricallyConnected ((Over.forget _).map (snd (splitTorus S X) G)) :=
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) (IsPullback.of_hasPullback _ _)
        (GlobalTheory.Diag.geometricallyConnected_hom S X)
    have h₂ : Surjective ((Over.forget _).map Q.q) := Q.q_surj
    exact @GlobalTheory.geometricallyConnected_of_isPullback_of_surjective _ _ _ _ _ _ _ _ sq h₂ h₁
  rw [← Over.w Q.q]
  exact ⟨inferInstance, GeometricallyConnected.comp _ _⟩

variable {Y Y' : Scheme.{0}} {L : LB Y} {L' : LB Y'} {F : Y' ⟶ Y}

theorem exists_iso_ratio (hL : L.IsLB) (hL' : L'.IsLB) {w₁ w₂ : LB.Iso L' (L.pull F)} (g₁ : w₁.IsGen) (g₂ : w₂.IsGen) :
    ∃ u : Γ(Y', ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (y : Z) (j : L.ι) (k : L'.ι), F (r y) ∈ L.U j → r y ∈ L'.U k →
      gw w₁ r y j k = gm r y ⊤ u * gw w₂ r y j k := by
  have h₁ := (isGen_iff _).1 g₁
  have h₂ := (isGen_iff _).1 g₂
  let W : L.ι × L'.ι → Y'.Opens := fun p => (L.pull F).U (fun _ => p.1) ⊓ L'.U p.2
  let v : ∀ p, Γ(Y', W p)ˣ := fun p => w₁.s (fun _ => p.1, p.2) * (w₂.s (fun _ => p.1, p.2))⁻¹
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (y : Z) p, gm r y (W p) (v p) =
      gw w₁ r y p.1 p.2 * (gw w₂ r y p.1 p.2)⁻¹ := fun Z r y p =>
    (map_mul _ _ _).trans (congrArg _ (map_inv _ _))
  obtain ⟨u, hu⟩ := glue_unit ⊤ W (fun _ => le_top) (fun x _ => by
      obtain ⟨j, hj⟩ := exists_chart hL (F x)
      obtain ⟨k, hk⟩ := exists_chart hL' x
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(j, k), mem_pull.2 hj, hk⟩) v (fun p q x hx => by
      have a := h₁ _ (𝟙 Y') x p.1 q.1 p.2 q.2 (mem_pull.1 hx.1.1) (mem_pull.1 hx.2.1) hx.1.2 hx.2.2
      have b := h₂ _ (𝟙 Y') x p.1 q.1 p.2 q.2 (mem_pull.1 hx.1.1) (mem_pull.1 hx.2.1) hx.1.2 hx.2.2
      rw [hv, hv, a, b, mul_inv, _root_.mul_mul_mul_comm, mul_inv_cancel, _root_.one_mul])
  refine ⟨u, fun Z r y j k hj hk => ?_⟩
  have hy : r y ∈ W (j, k) := ⟨mem_pull.2 hj, hk⟩
  rw [← gm_res r y (le_top : W (j, k) ≤ ⊤) hy u, hu, hv, inv_mul_cancel_right]

end General

section Restrict
variable {S S' : Scheme.{0}} {f : S' ⟶ S} {G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] {G' H' : Over S'}
  [GrpObj G'] [IsCommMonObj G'] [GrpObj H'] {F : G'.left ⟶ G.left} {hw : F ≫ G.hom = G'.hom ≫ f}
  {E : H'.left ⟶ H.left} {P : CP G} {P' : CP G'} {w : LB.Iso P'.L.L (P.L.L.pull F)} {i : H ⟶ G} {i' : H' ⟶ G'}

end Restrict

section Lift
variable {S S' : Scheme.{0}} {f : S' ⟶ S} {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G] [IsCommMonObj G]
  {G' : Over S'} [GrpObj G'] [IsCommMonObj G'] {F : G'.left ⟶ G.left} {hw : F ≫ G.hom = G'.hom ≫ f}
  {P : CP G} {P' : CP G'} {w : LB.Iso P'.L.L (P.L.L.pull F)} {i : splitTorus S X ⟶ G} {i' : splitTorus S' X ⟶ G'}

end Lift

section Nil
variable {A : Type} [CommRing A] {J : Ideal A} {X : Type} [AddCommGroup X] {G : Over (Spec (CommRingCat.of A))}
  [GrpObj G] [IsCommMonObj G] {G' : Over (Spec (CommRingCat.of (A ⧸ J)))} [GrpObj G'] [IsCommMonObj G']
  {F : G'.left ⟶ G.left} {hw : F ≫ G.hom = G'.hom ≫ red J} {P : CP G} {P' : CP G'}
  {w : LB.Iso P'.L.L (P.L.L.pull F)} {i : splitTorus _ X ⟶ G} {i' : splitTorus _ X ⟶ G'}

end Nil

section Descent
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G] [IsCommMonObj G]

end Descent

section Iso
variable {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} [GrpObj G] [IsCommMonObj G] [GrpObj G']
  [IsCommMonObj G'] [GrpObj G''] [IsCommMonObj G''] {X : Type} [AddCommGroup X]

end Iso

section Endo
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G] [IsCommMonObj G] {Q : TQ G X} {P : CP G}

end Endo

section Clauses
variable {S : Scheme.{0}}

end Clauses

section Along
variable {A : Type} [CommRing A] {J : Ideal A}

end Along

def IsThickPoint (A : Type) [CommRing A] : Prop := ∃ _ : IsLocalRing A, IsNilpotent (IsLocalRing.maximalIdeal A)

section Diag
open GlobalTheory.PairingLevels

variable {S : Scheme.{0}} {G : Over S} {Y : Over S} {L : LB G.left}

variable [GrpObj G] [IsCommMonObj G] {H : Over S} [GrpObj H] [IsCommMonObj H]

end Diag

section Invariant
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G] [IsCommMonObj G]

theorem act_q (Q : TQ G X) {T : Over S} (t : T ⟶ splitTorus S X) (x : T ⟶ G) :
    ((t ≫ Q.i) * x).left ≫ Q.q.left = x.left ≫ Q.q.left := by
  have := Q.q_hom
  rw [← Over.comp_left, MonObj.mul_comp, Q.comp_i_q, _root_.one_mul, Over.comp_left]

end Invariant

section Torus
open GlobalTheory.PairingLevels
variable {S : Scheme.{0}} {G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] [IsCommMonObj H]

end Torus

def IsBase (A : Type) [CommRing A] : Prop :=
  ConnectedSpace (Spec (CommRingCat.of A)) ∧ ∃ J : Ideal A, IsNilpotent J ∧ IsReduced (A ⧸ J)

section MoreClauses
variable {S : Scheme.{0}}

end MoreClauses

end GlobalTheory.TrivDescentCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsOfDouble
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.PeriodPoint

open CechPic

theorem exists_form {M V : Type} [AddCommGroup M] [AddCommGroup V] (P : M →+ V) (hP : Function.Injective P)
    (B : LinearMap.BilinForm ℤ M) (hB : Function.Bijective B) (Λ : Submodule ℤ V) (hΛ : ∀ z, z ∈ Λ ↔ z ∈ P.range) :
    ∃ Ef : LinearMap.BilinForm ℤ Λ, Function.Bijective Ef ∧
      ∀ a b (ha : P a ∈ Λ) (hb : P b ∈ Λ), Ef ⟨P a, ha⟩ ⟨P b, hb⟩ = B a b := by
  let φ : M ≃ₗ[ℤ] Λ := LinearEquiv.ofBijective
    (P.toIntLinearMap.codRestrict Λ fun a => (hΛ _).2 ⟨a, rfl⟩)
    ⟨fun a b h => hP (congrArg Subtype.val h), fun z => by
      obtain ⟨a, ha⟩ := (hΛ z).1 z.2
      exact ⟨a, Subtype.ext ha⟩⟩
  refine ⟨LinearMap.BilinForm.congr φ B, ?_, fun a b ha hb => ?_⟩
  · have : ⇑(LinearMap.BilinForm.congr φ B) = φ.symm.dualMap ∘ B ∘ φ.symm := by
      funext x; ext y; simp
    rw [this]
    exact φ.symm.dualMap.bijective.comp (hB.comp φ.symm.bijective)
  · have e : ∀ a (ha : P a ∈ Λ), φ.symm ⟨P a, ha⟩ = a := fun a _ => φ.symm_apply_apply a
    rw [LinearMap.BilinForm.congr_apply, e, e]

theorem weilIs_of_isAH (laws : Out.Laws) (Q : Out.PolAV (Sp ℂ)) {g : ℕ} (hg : Q.g = g) (u : HolUnif Q.A Q.L g)
    {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ} (h : u.IsAH Hm χ) (Ef : LinearMap.BilinForm ℤ u.Λ)
    (hE : ∀ a b : u.Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) (k : ℕ) (a b : u.Λ) (c : ℂˣ) (hk : 0 < k)
    (hc : (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (Ef a b : ℂ) / k)) :
    Out.WeilIs Q.A Q.L k (u.ex ((k : ℂ)⁻¹ • (a : Fin g → ℂ))) (u.ex ((k : ℂ)⁻¹ • (b : Fin g → ℂ))) (unitOn c) := by
  subst hg
  have hval := @valAt'_rules
  have hvalaff := @existsUnique_point_of_ringHom
  exact WeilExp.weilIs_exp_riemannForm laws.weil hval (@eq_of_valAt'_eq hval hvalaff) @isReduced_of_smooth_complex
    (ThetaGroupFrame.thetaGrp_in_frame hval (@holFamily_lift hval)) Q u Hm χ Ef ⟨h.1, h.2.2.1, hE, h.2.2.2⟩ k a b c hk hc

theorem cls_of_lam_eq {S : Scheme.{0}} [IsLocallyNoetherian S] (laws : Out.Laws) (Q : Out.PolAV S) [IsCommMonObj Q.A]
    (hΘ : ∃ t : LB.Gen (Theta Q.A Q.L), t.IsGen) (PP : RigLB Q.A) (hs : PP.IsSymmetric)
    (h : LBIso (abelian₂ Q.A PP.L) (abelian₂ Q.A Q.L)) :
    2 • cls PP.L PP.isLB = 2 • cls Q.L Q.isLB ∧
      pull ((𝟙 Q.A : Q.A ⟶ Q.A) ^ 2).left (cls PP.L PP.isLB) = 4 • cls Q.L Q.isLB := by
  set l := cls Q.L Q.isLB with hl
  set p := cls PP.L PP.isLB with hp
  have hlam : ∀ x y : Q.A ⟶ Q.A, lam p x y = lam l x y := fun x y => by
    have h₁ := (cls_eq_iff (LB.isLB_linComb PP.isLB _ _) (LB.isLB_linComb Q.isLB _ _)).2 h
    have h₂ := congrArg (pull (lift x y).left)
      ((cls_cube_two PP.isLB _ _ _).symm.trans (h₁.trans (cls_cube_two Q.isLB _ _ _)))
    simpa only [pull_lam, lift_fst, lift_snd] using h₂
  have hz : ∀ (M : LB Q.A.left) (hM : M.IsLB), Out.Rigidified Q.A M → pull (1 : Q.A ⟶ Q.A).left (cls M hM) = 0 := by
    intro M hM hr
    have h₀ := (cls_eq_zero_iff (pull_isLB hM (eSec Q.A))).2 hr
    rw [cls_pull hM] at h₀
    rw [Hom.one_def, Over.comp_left, pull_comp]
    exact (congrArg _ h₀).trans (map_zero _)
  have hl0 : pull (1 : Q.A ⟶ Q.A).left l = 0 := hz Q.L Q.isLB Q.rigid
  have hp0 : pull (1 : Q.A ⟶ Q.A).left p = 0 := hz PP.L PP.isLB ⟨PP.rig, PP.rigGen⟩
  have hl2 : pull ((𝟙 Q.A : Q.A ⟶ Q.A) * 𝟙 Q.A).left l = 4 • l := by
    have h₀ := (cls_eq_zero_iff (LB.isLB_linComb Q.isLB _ _)).2 (laws.mulPull S Q 2)
    rw [cls_linComb Q.isLB, Fin.sum_univ_two] at h₀
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, pull_id] at h₀
    have e : Out.mulA Q.A 2 = 𝟙 Q.A * 𝟙 Q.A := by rw [← pow_two]
    rw [e, ← hl] at h₀
    norm_num at h₀
    rw [add_neg_eq_zero] at h₀
    rw [← h₀]; rfl
  have hpi : pull ((𝟙 Q.A : Q.A ⟶ Q.A)⁻¹).left p = p := by
    obtain ⟨_, w, hw, -⟩ := hs
    have e := (cls_eq_iff PP.isLB (pull_isLB PP.isLB _)).2 ⟨w, hw⟩
    rw [cls_pull PP.isLB] at e
    rw [Hom.inv_def, Category.id_comp]
    exact e.symm
  have e₁ : lam l (𝟙 Q.A) (𝟙 Q.A) = 2 • l := by
    simp only [lam, hl2, Over.id_left, pull_id, hl0]; abel
  have e₂ : lam l (𝟙 Q.A)⁻¹ (𝟙 Q.A) = -(2 • l) := by
    have := lam_mul_left Q.isLB hΘ (𝟙 Q.A) (𝟙 Q.A)⁻¹ (𝟙 Q.A)
    rw [mul_inv_cancel, lam_one_left, ← hl, e₁] at this
    exact (neg_eq_of_add_eq_zero_right this.symm).symm
  have e₃ : lam p (𝟙 Q.A)⁻¹ (𝟙 Q.A) = -(2 • p) := by
    simp only [lam, inv_mul_cancel, hpi, Over.id_left, pull_id, hp0]; abel
  have e₄ : 2 • p = 2 • l := neg_injective (e₃.symm.trans ((hlam _ _).trans e₂))
  refine ⟨e₄, ?_⟩
  have e₅ := (hlam (𝟙 Q.A) (𝟙 Q.A)).trans e₁
  simp only [lam, Over.id_left, pull_id, hp0] at e₅
  rw [pow_two]
  calc _ = (pull ((𝟙 Q.A : Q.A ⟶ Q.A) * 𝟙 Q.A).left p - p - p + 0) + 2 • p := by abel
    _ = 4 • l := by rw [e₅, e₄]; abel

theorem weilIs_of_double (laws : Out.Laws) (Q Q' : Out.PolAV (Sp ℂ)) [IsCommMonObj Q.A] (ψ : Q.A ⟶ Q'.A) [IsMonHom ψ]
    (h : LBIso (lbPow Q.L 4) (Q'.L.pull ψ.left)) (k : ℕ) (x y : 𝟙_ (Over (Sp ℂ)) ⟶ Q.A) (c : Γ((𝟙_ (Over (Sp ℂ))).left, ⊤)ˣ)
    (hx : (x ≫ ψ) ^ k = 1) (hy : (y ≫ ψ) ^ k = 1) (hc : Out.WeilIs Q.A Q.L ((k * 4 : ℕ) : ℤ) x y c) :
    Out.WeilIs Q'.A Q'.L k (x ≫ ψ) (y ≫ ψ) c := by
  obtain ⟨c', hc', -⟩ := (laws.weil _ Q' k _).1 _ _ hx hy
  have h₁ := (weilIs_along_hom laws.globalFns _ Q.A Q'.A ψ Q.L Q'.L 4 k _ x y c' c' Q.isAb Q'.isAb Q.isLB Q'.isLB
    inferInstance h hc').1
  rw [Nat.cast_mul] at hc
  rwa [CommutatorPairing.weilIs_unique laws.globalFns Q.isAb Q.isLB hc h₁]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_act (hom : (∀ (P P' : Out.PolAV (Sp ℂ)) (g : ℕ) (u : HolUnif P.A P.L g) (u' : HolUnif P'.A P'.L g) (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), P.g = g → P'.g = g → (∀ z ∈ u.Λ, F z ∈ u'.Λ) → ∃ f : P.A ⟶ P'.A, IsMonHom f ∧ ∀ z, u'.ex (F z) = u.ex z ≫ f)) (Q : Out.PolAV (Sp ℂ)) {g : ℕ} (hg : Q.g = g) (u : HolUnif Q.A Q.L g)
    (ty : Fin g → (E →+* ℂ)) (hΛ : ∀ (a : 𝓞 E), ∀ z ∈ u.Λ, (fun k => ty k (a : E) * z k) ∈ u.Λ) :
    ∃ act : OAct (𝓞 E) Q.A, ∀ (a : 𝓞 E) z, u.ex (fun k => ty k (a : E) * z k) = u.ex z ≫ act.act a := by
  have h : ∀ a : 𝓞 E, ∃ f : Q.A ⟶ Q.A, IsMonHom f ∧ ∀ z, u.ex (fun k => ty k (a : E) * z k) = u.ex z ≫ f := fun a =>
    hom Q Q g u u (LinearMap.pi fun k => ty k (a : E) • LinearMap.proj (R := ℂ) (φ := fun _ => ℂ) k) hg hg fun z hz => hΛ a z hz
  choose f hf hex using h
  have := Q.isAb.smooth
  have := Q.isAb.proper
  have : IsReduced Q.A.left := isReduced_of_smooth_complex _ Q.A.hom inferInstance
  have ext : ∀ f f' : Q.A ⟶ Q.A, (∀ z, u.ex z ≫ f = u.ex z ≫ f') → f = f' := fun f f' h =>
    ComplexPoints.over_hom_ext_of_complexPoints fun x => by
      obtain ⟨z, rfl⟩ := u.ex_onto x
      exact h z
  refine ⟨⟨f, hf, ext _ _ fun z => ?_, fun a b => ext _ _ fun z => ?_, fun a b => ext _ _ fun z => ?_⟩, hex⟩
  · rw [← hex, Category.comp_id]; simp
  · rw [← Category.assoc, ← hex, ← hex, ← hex]
    congr 1; funext k; push_cast; rw [map_mul]; ring
  · rw [MonObj.comp_mul, ← hex, ← hex, ← hex, ← u.ex_add]
    congr 1; funext k; push_cast; rw [map_add (f := _), Pi.add_apply]; ring

theorem ex_pow {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) (n : ℕ) (z : Fin g → ℂ) :
    u.ex z ^ n = u.ex (n • z) := by
  induction n with
  | zero => rw [pow_zero, zero_smul, (u.ker 0).2 (zero_mem _)]
  | succ n ih => rw [pow_succ, ih, succ_nsmul, u.ex_add]

theorem exists_triple (laws : Out.Laws) (cube : (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen)) (tor : (∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (Ef : LinearMap.BilinForm ℤ Λ), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) → (∀ a b : Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) → Function.Bijective Ef → ∃ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L g) (χ : u.Λ → ℂ), P.g = g ∧ u.Λ = Λ ∧ u.IsAH Hm χ ∧ (∀ v, IsTangent v → ∃! w, u.IsDiff w v) ∧ (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v))) (hom : (∀ (P P' : Out.PolAV (Sp ℂ)) (g : ℕ) (u : HolUnif P.A P.L g) (u' : HolUnif P'.A P'.L g) (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), P.g = g → P'.g = g → (∀ z ∈ u.Λ, F z ∈ u'.Λ) → ∃ f : P.A ⟶ P'.A, IsMonHom f ∧ ∀ z, u'.ex (F z) = u.ex z ≫ f))
    (adjW : (∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (P : Out.PolAV (Sp k)) (a a' : P.A ⟶ P.A), IsMonHom a → IsMonHom a' → (∀ (n : ℕ) (x y : 𝟙_ (Over (Sp k)) ⟶ P.A) (c : Γ((𝟙_ (Over (Sp k))).left, ⊤)ˣ), 0 < n → x ^ n = 1 → y ^ n = 1 → Out.WeilIs P.A P.L n (x ≫ a) y c → Out.WeilIs P.A P.L n x (y ≫ a') c) → LBIso (cubeLB P.A ![fst P.A P.A ≫ a, snd P.A P.A] P.L) (cubeLB P.A ![fst P.A P.A, snd P.A P.A ≫ a'] P.L))) (prim : (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (B : Over S) [GrpObj B] [IsCommMonObj B] (act : OAct (𝓞 E) B) (M : LB B.left), IsAbelianScheme B → M.IsLB → (∃ t : LB.Gen (Theta B M), t.IsGen) → (∀ a, LBIso (cubeLB B ![fst B B ≫ act.act a, snd B B] M) (cubeLB B ![fst B B, snd B B ≫ act.act (H.bar a)] M)) → ∃ (PP : RigLB B) (_ : CubicalStr B PP), PP.IsSymmetric ∧ LBIso PP.L (cubeLB B ![𝟙 B, act.act H.w0] M) ∧ LBIso (abelian₂ B PP.L) (abelian₂ B M) ∧ LBIso PP.L (cubeLB B ![𝟙 B, act.act H.w0] PP.L) ∧ ∀ a, LBIso (cubeLB B ![fst B B ≫ act.act a, snd B B] PP.L) (cubeLB B ![fst B B, snd B B ≫ act.act (H.bar a)] PP.L))) (princ : (∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (P : Out.PolAV (Sp k)) (n : ℕ) (B : Over (Sp k)) [GrpObj B] (ψ : P.A ⟶ B) (M : LB B.left), 0 < n → IsAbelianScheme B → M.IsLB → IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ P.A // x ≫ ψ = 1} = n ^ P.g → LBIso (abelian₂ P.A (lbPow P.L n)) (abelian₂ P.A (M.pull ψ.left)) → Out.KTriv B M)) (amp : (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A B : Over S) [GrpObj A] [GrpObj B] (ψ : A ⟶ B) (M : LB B.left) (n : ℕ), 0 < n → IsAbelianScheme A → IsAbelianScheme B → M.IsLB → IsFinite ψ.left → (Out.RelAmple B M → Out.RelAmple A (M.pull ψ.left)) ∧ (Out.RelAmple B (lbPow M n) ↔ Out.RelAmple B M) ∧ (Flat ψ.left → Surjective ψ.left → Out.RelAmple A (M.pull ψ.left) → Out.RelAmple B M) ∧ ∀ M' : LB B.left, M'.IsLB → LBIso M M' → Out.RelAmple B M → Out.RelAmple B M'))
    {H : Host E} (D : Datum H) {g : ℕ} (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)) (hP : IsPeriod D ty P) :
    ∃ (t : SAB H (Sp ℂ)) (L : LB t.G.left) (u : HolUnif t.G L g), IsAbelianScheme t.G ∧
      SmoothOfRelativeDimension g t.G.hom ∧ Out.RelAmple t.G t.PP.L ∧ Out.KTriv t.G t.PP.L ∧
      (∀ v, IsTangent v → ∃! w, u.IsDiff w v) ∧ (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) ∧
      (∀ z, u.ex z = 1 ↔ z ∈ P.range) ∧
      (∀ (a : 𝓞 E) z, u.ex (fun k => ty k (a : E) * z k) = u.ex z ≫ t.act.act a) ∧
      ∀ (k : ℕ) (a b : D.La) (c : ℂˣ), 0 < k →
        (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D.EF a b : ℂ) / k) →
        Out.WeilIs t.G t.PP.L k (u.ex ((k : ℂ)⁻¹ • P a)) (u.ex ((k : ℂ)⁻¹ • P b)) (unitOn c) := by
  obtain ⟨hlin, hinj, hdisc, hspan, Hm, hH, hpos, him⟩ := hP
  have hE : ∀ (Λ : Submodule ℤ (Fin g → ℂ)), (∀ z, z ∈ Λ ↔ z ∈ P.range) → ∃ Ef : LinearMap.BilinForm ℤ Λ,
      Function.Bijective Ef ∧ (∀ a b : Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) ∧
      ∀ a b (ha : P a ∈ Λ) (hb : P b ∈ Λ), Ef ⟨P a, ha⟩ ⟨P b, hb⟩ = D.EF a b := fun Λ hΛ => by
    obtain ⟨Ef, h₁, h₂⟩ := exists_form P hinj D.EF D.unimod Λ hΛ
    refine ⟨Ef, h₁, ?_, h₂⟩
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    obtain ⟨a, rfl⟩ := (hΛ a).1 ha
    obtain ⟨b, rfl⟩ := (hΛ b).1 hb
    rw [h₂, him]
  obtain ⟨Ef₀, hb₀, hi₀, -⟩ := hE P.range.toIntSubmodule fun _ => Iff.rfl
  obtain ⟨Q, u, χ, hg, hΛ, hAH, ht₁, ht₂⟩ := tor g P.range.toIntSubmodule Hm Ef₀ hdisc hspan hH hpos hi₀ hb₀
  have hmem : ∀ z, z ∈ u.Λ ↔ z ∈ P.range := fun z => by rw [hΛ]; rfl
  obtain ⟨Ef, -, hi, hEf⟩ := hE u.Λ hmem
  have hker : ∀ z, u.ex z = 1 ↔ z ∈ P.range := fun z => (u.ker z).trans (hmem z)
  have hW : ∀ (k : ℕ) (a b : D.La) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D.EF a b : ℂ) / k) →
      Out.WeilIs Q.A Q.L k (u.ex ((k : ℂ)⁻¹ • P a)) (u.ex ((k : ℂ)⁻¹ • P b)) (unitOn c) := fun k a b c hk hc =>
    weilIs_of_isAH laws Q hg u hAH Ef hi k ⟨P a, (hmem _).2 ⟨a, rfl⟩⟩ ⟨P b, (hmem _).2 ⟨b, rfl⟩⟩ c hk (by rwa [hEf])
  obtain ⟨act, hact⟩ := exists_act hom Q hg u ty fun a z hz => by
    obtain ⟨x, rfl⟩ := (hmem z).1 hz
    exact (hmem _).2 ⟨a • x, funext (hlin a x)⟩
  have hact' : ∀ (a : 𝓞 E) (s : ℂ) x, u.ex (s • P x) ≫ act.act a = u.ex (s • P (a • x)) := fun a s x => by
    rw [← hact]; congr 1; funext k
    simp only [Pi.smul_apply, hlin, smul_eq_mul]; ring
  have htors : ∀ (n : ℕ) (x : 𝟙_ (Over (Sp ℂ)) ⟶ Q.A), 0 < n → x ^ n = 1 → ∃ a, x = u.ex ((n : ℂ)⁻¹ • P a) := by
    intro n x hn hx
    obtain ⟨z, rfl⟩ := u.ex_onto x
    rw [ex_pow, hker] at hx
    obtain ⟨a, ha⟩ := hx
    refine ⟨a, ?_⟩
    rw [ha, ← Nat.cast_smul_eq_nsmul ℂ, inv_smul_smul₀ (Nat.cast_ne_zero.2 hn.ne')]
  have hA := Q.isAb
  have := hA.comm
  have adj : ∀ a, LBIso (cubeLB Q.A ![fst Q.A Q.A ≫ act.act a, snd Q.A Q.A] Q.L)
      (cubeLB Q.A ![fst Q.A Q.A, snd Q.A Q.A ≫ act.act (H.bar a)] Q.L) := fun a => by
    refine adjW ℂ Q _ _ (act.hom a) (act.hom _) fun n x y c hn hx hy hc => ?_
    obtain ⟨x, rfl⟩ := htors n x hn hx
    obtain ⟨y, rfl⟩ := htors n y hn hy
    rw [hact'] at hc ⊢
    let c₀ : ℂˣ := Units.mk0 _ (Complex.exp_ne_zero (-(2 * Real.pi * Complex.I) * (D.EF (a • x) y : ℂ) / n))
    rw [CommutatorPairing.weilIs_unique laws.globalFns hA Q.isLB hc (hW n _ _ c₀ hn rfl)]
    exact hW n _ _ c₀ hn (by rw [← D.adj]; rfl)
  have hΘ := cube _ Q Q.L Q.isLB
  obtain ⟨PP, cub, hsym, -, hlam, hprim, hadj⟩ := prim E H _ Q.A act Q.L hA Q.isLB hΘ adj
  obtain ⟨h₂, h₄⟩ := cls_of_lam_eq laws Q hΘ PP hsym hlam
  have hL := Q.isLB
  have hP' := PP.isLB
  have hid : IsFinite (𝟙 Q.A : Q.A ⟶ Q.A).left := by rw [Over.id_left]; infer_instance
  have hpow : ∀ (M : LB Q.A.left), M.IsLB → ∀ n, (lbPow M n).IsLB := fun M hM n => LB.isLB_linComb hM _ _
  have a₁ : Out.RelAmple Q.A (lbPow Q.L 2) := (amp _ Q.A Q.A (𝟙 _) Q.L 2 two_pos hA hA hL hid).2.1.2 Q.ample
  have a₂ : Out.RelAmple Q.A (lbPow PP.L 2) :=
    (amp _ Q.A Q.A (𝟙 _) _ 1 one_pos hA hA (hpow _ hL 2) hid).2.2.2 _ (hpow _ hP' 2)
      (by rw [← cls_eq_iff (hpow _ hL 2) (hpow _ hP' 2), cls_lbPow hL, cls_lbPow hP', h₂]) a₁
  have a₃ : Out.RelAmple Q.A PP.L := (amp _ Q.A Q.A (𝟙 _) PP.L 2 two_pos hA hA hP' hid).2.1.1 a₂
  have a₄ : Out.KTriv Q.A PP.L := by
    refine princ ℂ Q 1 Q.A (𝟙 _) PP.L one_pos hA hP' inferInstance hid (by rw [Over.id_left]; infer_instance)
      (by rw [Over.id_left]; infer_instance) (by simp) ?_
    refine (cls_eq_iff (LB.isLB_linComb (hpow _ hL 1) _ _) (LB.isLB_linComb (pull_isLB hP' _) _ _)).1 ?_
    refine (cls_cube_two (hpow _ hL 1) _ _ _).trans (Eq.trans ?_ (cls_cube_two (pull_isLB hP' _) _ _ _).symm)
    rw [cls_lbPow hL, cls_pull hP', Over.id_left, pull_id, one_nsmul]
    have h₁ := (cls_eq_iff (LB.isLB_linComb hP' _ _) (LB.isLB_linComb hL _ _)).2 hlam
    exact ((cls_cube_two hP' _ _ _).symm.trans (h₁.trans (cls_cube_two hL _ _ _))).symm
  let Q' : Out.PolAV (Sp ℂ) :=
    { A := Q.A, isAb := hA, g := Q.g, smoothDim := Q.smoothDim, L := PP.L, isLB := hP',
      rigid := ⟨PP.rig, PP.rigGen⟩, sym := sym_of_isSymmetric PP hsym, ample := a₃, ktriv := a₄ }
  refine ⟨{ G := Q.A, semi := isSemiAbelian_of_isAbelianScheme Q.A hA, act := act, PP := PP, cub := cub, sym := hsym,
            adj := hadj, prim := hprim }, Q.L, u, hA, hg ▸ Q.smoothDim, a₃, a₄, ht₁, ht₂, hker, hact,
    fun k a b c hk hc => ?_⟩
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have hdbl : IsMonHom ((𝟙 Q.A : Q.A ⟶ Q.A) ^ 2) := laws.rigidity _ _ _ hA hA _ (by
    have e₁ : (η[Q.A] : 𝟙_ _ ⟶ Q.A) = 1 := by rw [Hom.one_def]; simp
    rw [MonObj.comp_pow, Category.comp_id, e₁, one_pow])
  have hx : ∀ a, u.ex (((k * 4 : ℕ) : ℂ)⁻¹ • P (2 • a)) ≫ (𝟙 Q.A : Q.A ⟶ Q.A) ^ 2 = u.ex ((k : ℂ)⁻¹ • P a) := fun a => by
    rw [MonObj.comp_pow, Category.comp_id, ex_pow, map_nsmul]
    congr 1
    rw [← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, smul_smul]
    congr 1
    clear * - hk'
    push_cast; field_simp; norm_num
  have hx' : ∀ a, u.ex ((k : ℂ)⁻¹ • P a) ^ k = 1 := fun a => by
    rw [ex_pow, hker, ← Nat.cast_smul_eq_nsmul ℂ, smul_inv_smul₀ hk']
    exact ⟨a, rfl⟩
  have := weilIs_of_double laws Q Q' ((𝟙 Q.A : Q.A ⟶ Q.A) ^ 2)
    (by rw [← cls_eq_iff (hpow _ hL 4) (pull_isLB hP' _), cls_lbPow hL, cls_pull hP', h₄]) k _ _ (unitOn c)
    ((congrArg (· ^ k) (hx a)).trans (hx' a)) ((congrArg (· ^ k) (hx b)).trans (hx' b))
    (hW (k * 4) (2 • a) (2 • b) c (by positivity) (by
      rw [hc]; congr 1
      rw [map_nsmul, map_nsmul, LinearMap.smul_apply]
      clear * - hk'
      simp only [nsmul_eq_mul]
      push_cast; field_simp; ring))
  rw [hx, hx] at this
  exact this

end GlobalTheory.PeriodPoint
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaSectionGeneratorPower
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaSpan

open GlobalTheory.VVRank GlobalTheory.EmbPull GlobalTheory.ThetaReal TopologicalSpace

theorem exists_pow_smul_of_mem_span {R R' M M' I : Type} [CommRing R] [CommRing R'] [AddCommGroup M]
    [AddCommGroup M'] [Module R M] [Module R' M'] (σ : R →+* R') (φ : M →ₛₗ[σ] M') (f : R)
    (hf : ∀ d : R', ∃ (m : ℕ) (d₀ : R), σ d₀ = σ (f ^ m) * d) (t : I → M) (y : M')
    (hy : y ∈ Submodule.span R' (Set.range fun i => φ (t i))) :
    ∃ (n : ℕ) (u : M), u ∈ Submodule.span R (Set.range t) ∧ φ u = σ (f ^ n) • y := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    exact ⟨0, t i, Submodule.subset_span ⟨i, rfl⟩, by simp⟩
  | zero => exact ⟨0, 0, Submodule.zero_mem _, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨n, u, hu, e⟩ := hy
    obtain ⟨k, v, hv, e'⟩ := hz
    refine ⟨n + k, f ^ k • u + f ^ n • v,
      Submodule.add_mem _ (Submodule.smul_mem _ _ hu) (Submodule.smul_mem _ _ hv), ?_⟩
    rw [map_add (f := _), LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, e, e', smul_add, smul_smul, smul_smul,
      ← map_mul, ← map_mul, ← pow_add, ← pow_add, add_comm k n]
  | smul d y _ hy =>
    obtain ⟨n, u, hu, e⟩ := hy
    obtain ⟨k, d₀, hd⟩ := hf d
    refine ⟨k + n, d₀ • u, Submodule.smul_mem _ _ hu, ?_⟩
    rw [LinearMap.map_smulₛₗ, e, hd, smul_smul, smul_smul, pow_add, map_mul]
    congr 1
    ring

variable {S : Scheme.{0}} (P : PolAV S)

theorem span_eq_top_of_geomFibres (hS : SecBaseChangeAnySt) [IsAffine S] (N : ℕ) (hN : 1 ≤ N) {I : Type}
    (t : I → SecM P.A P.L N (baseOver S))
    (H : ∀ (K : Type) [Field K] [IsAlgClosed K] (w : Spec (CommRingCat.of K) ⟶ S) (h : Over.mk w ⟶ baseOver S),
      Submodule.span Γ((Over.mk w).left, ⊤) (Set.range fun i => pullM P.A P.L N h (t i)) = ⊤) :
    Submodule.span Γ((baseOver S).left, ⊤) (Set.range t) = ⊤ := by
  have haff : IsAffine (baseOver S).left := ‹IsAffine S›
  refine eq_top_iff.2 fun x _ => ?_
  let J : Ideal Γ((baseOver S).left, ⊤) := (Submodule.span Γ((baseOver S).left, ⊤) (Set.range t)).comap
    (LinearMap.toSpanSingleton _ _ x)
  have key : ∀ p : (baseOver S).left, ∃ f ∈ J, p ∈ (baseOver S).left.basicOpen f := fun p => by
    obtain ⟨V, hV, b, hb⟩ := hS S P N hN p
    obtain ⟨f, hf, hp⟩ := (isAffineOpen_top (baseOver S).left).exists_basicOpen_le (V := V) ⟨p, hV⟩ trivial
    let W := (baseOver S).left.basicOpen f
    let l : overRes W ⟶ overRes (T := baseOver S) V := Over.homMk ((baseOver S).left.homOfLE hf) (by
      change (baseOver S).left.homOfLE hf ≫ V.ι ≫ _ = W.ι ≫ _
      rw [Scheme.homOfLE_ι_assoc])
    have hW : IsAffineOpen W := (isAffineOpen_top _).basicOpen f
    have : IsAffine (overRes W).left := hW
    obtain ⟨c, hc⟩ := exists_basis P N b hb (overRes W) l
    have hspan : Submodule.span Γ((overRes W).left, ⊤)
        (Set.range fun i => pullM P.A P.L N (overResι W) (t i)) = ⊤ := by
      refine span_eq_top_of_functionals c _ fun 𝔪 h𝔪 ℓ hl y => ?_
      obtain ⟨K, _, _, u, hu⟩ := exists_geomPoint (overRes W).left 𝔪 h𝔪
      let w : Spec (CommRingCat.of K) ⟶ S := u ≫ (overRes W).hom
      let h : Over.mk w ⟶ overRes W := Over.homMk u rfl
      have haffK : IsAffine (Over.mk w).left := inferInstanceAs (IsAffine (Spec _))
      obtain ⟨b', hb'⟩ := exists_basis P N b hb (Over.mk w) (h ≫ l)
      refine (hu _).1 (functional_mem_of_span h.left.appTop.hom (pullM P.A P.L N h) c b'
        (fun i => by rw [hc, hb', pullM_comp P.A P.isLB]) _ ?_ ℓ (fun i => (hu _).2 (hl i)) y)
      simp only [pullM_comp P.A P.isLB]
      exact H K w _
    obtain ⟨n, u, hu, e⟩ := exists_pow_smul_of_mem_span (overResι W).left.appTop.hom
      (pullM P.A P.L N (overResι W)) f (exists_pow_mul_extend f) t (pullM P.A P.L N (overResι W) x)
      (hspan.ge trivial)
    obtain ⟨k, hk⟩ := exists_pow_kill_secM P N f (f ^ n • x - u) (by
      rw [map_sub, LinearMap.map_smulₛₗ, e, sub_self])
    refine ⟨f ^ k * f ^ n, ?_, ?_⟩
    · rw [smul_sub, sub_eq_zero, ← mul_smul] at hk
      change (f ^ k * f ^ n) • x ∈ Submodule.span _ _
      rw [hk]
      exact Submodule.smul_mem _ _ hu
    · rw [Scheme.mem_basicOpen_top] at hp ⊢
      simp only [map_mul, map_pow]
      exact (hp.pow _).mul (hp.pow _)
  have hI : Ideal.span (J : Set Γ((baseOver S).left, ⊤)) = ⊤ :=
    (isAffineOpen_top (baseOver S).left).self_le_iSup_basicOpen_iff.1 fun p _ => by
      obtain ⟨f, hf, hp⟩ := key p
      exact Opens.mem_iSup.2 ⟨⟨f, hf⟩, hp⟩
  rw [Ideal.span_eq, Ideal.eq_top_iff_one] at hI
  have := Submodule.mem_comap.1 hI
  rwa [LinearMap.toSpanSingleton_apply, one_smul] at this

theorem pullS_ne_zero (hS : SecBaseChangeAnySt) {T : Over S} [IsAffine T.left] {th : LB.Sec (LPow P.A P.L 1 T)}
    (hth : IsGenSec P.A P.L 1 th) {K : Type} [Field K] (w : Spec (CommRingCat.of K) ⟶ S) (h : Over.mk w ⟶ T) :
    (SecM.ofSec P.A (pullS P.A 1 h th) : SecM P.A P.L 1 (Over.mk w)) ≠ 0 := by
  intro hz
  have haffK : IsAffine (Over.mk w).left := inferInstanceAs (IsAffine (Spec _))
  have hntK : Nontrivial Γ((Over.mk w).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.domain_nontrivial
  obtain ⟨V, hV, b, hb⟩ := hS S P 1 le_rfl (w (default : Spec (CommRingCat.of K)))
  let l : Over.mk w ⟶ overRes (T := baseOver S) V := Over.homMk
    (IsOpenImmersion.lift V.ι w (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨y, rfl⟩
      rw [Subsingleton.elim (α := Spec (CommRingCat.of K)) y default]
      exact hV)) ((congrArg (_ ≫ ·) (Category.comp_id _)).trans (IsOpenImmersion.lift_fac _ _ _))
  obtain ⟨c, -⟩ := exists_basis P 1 b hb (Over.mk w) l
  let i₀ : Fin (1 ^ P.g) := ⟨0, by simp⟩
  obtain ⟨r, hr⟩ := isGenSec_pullS P hS h hth (SecM.toSec P.A (c i₀))
  have hr' : c i₀ = r • SecM.ofSec P.A (pullS P.A 1 h th) := Subtype.ext (funext hr)
  exact c.ne_zero i₀ (hr'.trans ((congrArg (r • ·) hz).trans (smul_zero r)))

theorem span_translates_mulPull_of_isGenSec : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (P : PolAV (Sp R)) (m N : ℕ), N = m ^ 2 → 1 ≤ m → IsUnit (m : Γ(Sp R, ⊤)) → ∀ (th : LB.Sec (LPow P.A P.L 1 (baseOver (Sp R)))), IsGenSec P.A P.L 1 th → ∀ (α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd (baseOver (Sp R)) P.A).left, (snd (baseOver (Sp R)) P.A ^ m).left] ![(N : ℤ), -1])), α.IsGen → ∀ s₀ : LB.Sec (LPow P.A P.L N (baseOver (Sp R))), IsTwistPull P.A P.L (mulT P.A _ m) (snd _ P.A ^ m) (lift_snd _ _) N 1 α th s₀ → ∀ (I : Type) (U : I → ThetaGrp P.A P.L N (baseOver (Sp R))) (t : I → LB.Sec (LPow P.A P.L N (baseOver (Sp R)))), (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp R) (z : Over.mk x ⟶ P.A), z ^ N = 1 → ∃ i, (Over.homMk x (by simp) : Over.mk x ⟶ baseOver (Sp R)) ≫ (U i).pt = z) → (∀ i, IsActOf P.A P.L N (U i) s₀ (t i)) → Submodule.span Γ((baseOver (Sp R)).left, ⊤) (Set.range fun i => (SecM.ofSec P.A (t i) : SecM P.A P.L N (baseOver (Sp R)))) = ⊤ := by
  intro hL hL2 R _ _ _ P m N hN hm hunit th hth α hα s₁ hs₁ I U t hU ht
  subst hN
  have hk : m ^ 2 = 1 ∨ 4 ≤ m ^ 2 := by
    rcases Nat.lt_or_ge m 2 with h | h
    · left; rw [show m = 1 by omega]; rfl
    · right; nlinarith
  have hsurj : Surjective (mulA P.A m).left := (hL.mulN (Sp R) P m hm).2.2.1
  have haff : IsAffine (baseOver (Sp R)).left := inferInstanceAs (IsAffine (Spec _))
  refine span_eq_top_of_geomFibres P hL2.secBaseChangeAny (m ^ 2) (Nat.one_le_pow _ _ hm) _ fun K _ _ w h => ?_
  obtain rfl : h = Over.homMk w (Category.comp_id _) :=
    Over.OverMorphism.ext ((Category.comp_id _).symm.trans (Over.w h))
  set h : Over.mk w ⟶ baseOver (Sp R) := Over.homMk w (Category.comp_id _)
  obtain ⟨ρ', k₁, -, k₃, k₄⟩ := thetaGrp_acts_linearly hL.globalFns (Sp R) P (m ^ 2 : ℕ) (Over.mk w)
  choose U' hU' using fun c => exists_theta_pull P.A P.isLB h (U c)
  have e : ∀ c, pullM P.A P.L (m ^ 2 : ℕ) h (SecM.ofSec P.A (t c)) =
      ρ' (U' c) (SecM.ofSec P.A (pullS P.A _ h s₁)) := fun c =>
    ((k₁ _ _ _).1 ((hU' c).2 _ _ (ht c))).symm
  simp only [e]
  have hI : Nonempty I := ⟨(hU K w 1 (by have := P.isAb.comm; exact one_pow _)).choose⟩
  refine span_translates_eq_top P.A
    ((secM_invariant_eq_bot_or_univ_at_geometric_point hL.polBaseChange).2 hL.irred (Sp R) P K w (m ^ 2) hk
    (by rw [Nat.cast_pow]; exact pow_ne_zero _ (natCast_ne_zero w hunit))) ρ' k₁ k₃ k₄ U'
    (fun θ => ?_) _ fun h0 => ?_
  · obtain ⟨c, hc'⟩ := hU K w θ.pt ((hL.kerPow (Sp R) P (m ^ 2) (Nat.one_le_pow _ _ hm) (Over.mk w) θ.pt).1 fun _ =>
      ⟨⊤, trivial, _, LB.isGen_genPull _ θ.φ θ.isGen _⟩)
    exact ⟨c, (hU' c).1.trans hc'⟩
  · obtain ⟨α', -, k₂⟩ := exists_twist_pull P.A (ψ := mulT P.A (baseOver (Sp R)) m) (hm := lift_snd _ _)
      (b := 1) P.isLB hα h (ψ' := mulT P.A (Over.mk w) m) (lift_snd _ _) (mulT_comm P.A h m)
    have hint : IsIntegral (Over.mk w ⊗ P.A).left :=
      (forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ P.A.hom P.isAb.smooth
        P.isAb.geomConnected).geometrically_isIntegral w _ _
        (IsPullback.of_hasPullback w P.A.hom).flip
    exact pullS_ne_zero P hL2.secBaseChangeAny hth w h
      (ofSec_eq_zero_of_twist P.A P.isLB (surjective_mulT P.A m hsurj _) (k₂ _ _ hs₁) h0)

end GlobalTheory.ThetaSpan
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSymmetricBiadditiveBundleEighthPower
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSymmetricBiadditiveBundleEighthPower
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.EighthPower

open GlobalTheory.CechPic Matrix

theorem map_prod_add {G M : Type*} [CommGroup G] [AddCommGroup M] (f : G → M) (hf : ∀ x y, f (x * y) = f x + f y)
    {n : ℕ} (x : Fin n → G) : f (∏ i, x i) = ∑ i, f (x i) := by
  simpa only [zpow_one, one_smul] using GlobalTheory.BilinCalc.map_prod_zpow f hf x fun _ => 1

theorem map_zpow_add {G M : Type*} [CommGroup G] [AddCommGroup M] (f : G → M) (hf : ∀ x y, f (x * y) = f x + f y)
    (x : G) (c : ℤ) : f (x ^ c) = c • f x := by
  simpa only [Fin.prod_univ_one, Fin.sum_univ_one] using
    GlobalTheory.BilinCalc.map_prod_zpow f hf (n := 1) (fun _ => x) fun _ => c

section Points

variable {S : Scheme.{0}} {G A T T' : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A]

theorem comp_prod_zpow (h : T' ⟶ T) {n : ℕ} (x : Fin n → (T ⟶ A)) (c : Fin n → ℤ) :
    h ≫ (∏ i, x i ^ c i) = ∏ i, (h ≫ x i) ^ c i := by
  let F : (T ⟶ A) →* (T' ⟶ A) := MonoidHom.mk' (fun z => h ≫ z) fun a b => MonObj.comp_mul _ _ _
  have e : F (∏ i, x i ^ c i) = ∏ i, F (x i) ^ c i := by simp only [map_prod, map_zpow]
  exact e

theorem prod_comp_hom (f : G ⟶ A) [IsMonHom f] {n : ℕ} (x : Fin n → (T ⟶ G)) :
    (∏ i, x i) ≫ f = ∏ i, x i ≫ f := by
  let F : (T ⟶ G) →* (T ⟶ A) := MonoidHom.mk' (fun z => z ≫ f) fun a b => MonObj.mul_comp _ _ _
  exact map_prod F x _

omit [IsCommMonObj A] in
theorem comp_id_zpow (x : T ⟶ A) (c : ℤ) : x ≫ (𝟙 A ^ c) = x ^ c := by
  let F : (A ⟶ A) →* (T ⟶ A) := MonoidHom.mk' (fun z => x ≫ z) fun a b => MonObj.comp_mul _ _ _
  have e : F (𝟙 A ^ c) = F (𝟙 A) ^ c := map_zpow F _ _
  exact e.trans (congrArg (· ^ c) (Category.comp_id x))

end Points

theorem prod_zpow_eq {H : Type*} [CommGroup H] (x : H) {n : ℕ} (c : Fin n → ℤ) : ∏ i, x ^ c i = x ^ ∑ i, c i := by
  have h := map_prod (zpowersHom H x) (fun i => Multiplicative.ofAdd (c i)) Finset.univ
  simp only [zpowersHom_apply, toAdd_prod, toAdd_ofAdd] at h
  exact h.symm

theorem main : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (S : Scheme.{0}) (G A : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A] (pr : Fin 8 → (G ⟶ A)) (L : LB G.left) (ρ : Matrix (Fin 8) (Fin 8) ℤ → (G ⟶ G)), IsE8 W → (∀ u, IsMonHom (pr u)) → (∀ (T : Over S) (y : Fin 8 → (T ⟶ A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u) → L.IsLB → (∃ t : LB.Gen (Theta G L), t.IsGen) → (∀ m u, ρ m ≫ pr u = (List.ofFn fun v => pr v ^ m u v).prod) → (∀ m m', m.transpose * (W + W.transpose) = (W + W.transpose) * m' → LBIso (cubeLB G ![fst G G ≫ ρ m, snd G G] L) (cubeLB G ![fst G G, snd G G ≫ ρ m'] L)) → (∀ m, (W + W.transpose) * m = W → LBIso L (cubeLB G ![𝟙 G, ρ m] L)) → ∃ P : LB (G2 A).left, P.IsLB ∧ (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) ∧ (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) ∧ LBIso P (P.pull (lift (snd A A) (fst A A)).left) ∧ (∀ (T : Over S) (x x' y : T ⟶ A), (∃ t : (LB.LinComb P (K := Fin 3) ![(lift (x * x') y).left, (lift x y).left, (lift x' y).left] ![1, -1, -1]).Gen, t.IsGen) ∧ ∃ t : (LB.LinComb P (K := Fin 3) ![(lift y (x * x')).left, (lift y x).left, (lift y x').left] ![1, -1, -1]).Gen, t.IsGen) ∧ LBIso L (LB.LinComb P (K := Fin 8 × Fin 8) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)) := by
  intro W S G A _ _ _ _ pr L ρ hE hpr huniv hL hΘ hρ hadj hprim
  obtain ⟨B, hB⟩ : ∃ B, B = W + W.transpose := ⟨_, rfl⟩
  have hdet : IsUnit B.det := by rw [hB, hE.2]; exact isUnit_one
  have hBs : B.transpose = B := by rw [hB, Matrix.transpose_add, Matrix.transpose_transpose, add_comm]
  rw [← hB] at hadj hprim
  have hBi : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hdet
  obtain ⟨u₀, hu₀⟩ : ∃ u₀ : Fin 8 → ℤ, u₀ = Pi.single 0 1 := ⟨_, rfl⟩
  obtain ⟨u₁, hu₁⟩ : ∃ u₁ : Fin 8 → ℤ, B *ᵥ u₁ = u₀ := ⟨B⁻¹ *ᵥ u₀, by rw [Matrix.mulVec_mulVec, hBi, Matrix.one_mulVec]⟩
  have h00 : u₀ ⬝ᵥ u₀ = 1 := by rw [hu₀]; simp
  have hsymB : ∀ v v' : Fin 8 → ℤ, v ⬝ᵥ B *ᵥ v' = v' ⬝ᵥ B *ᵥ v := fun v v' => by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hBs, dotProduct_comm]
  have ext : ∀ {T : Over S} (x x' : T ⟶ G), (∀ u, x ≫ pr u = x' ≫ pr u) → x = x' := fun {T} x x' h =>
    (huniv T fun u => x' ≫ pr u).unique h fun _ => rfl
  choose ψ hψ using fun v : Fin 8 → ℤ => (huniv A fun u => 𝟙 A ^ v u).exists
  have hψ' : ∀ {T : Over S} (x : T ⟶ A) v u, (x ≫ ψ v) ≫ pr u = x ^ v u := fun x v u => by
    rw [Category.assoc, hψ, comp_id_zpow]
  have ψmul : ∀ {T : Over S} (x y : T ⟶ A) v, (x * y) ≫ ψ v = (x ≫ ψ v) * (y ≫ ψ v) := fun x y v =>
    ext _ _ fun u => by rw [hψ', MonObj.mul_comp, hψ', hψ', _root_.mul_zpow]
  have ψone : ∀ {T : Over S} v, (1 : T ⟶ A) ≫ ψ v = 1 := fun v =>
    ext _ _ fun u => by rw [hψ', MonObj.one_comp, _root_.one_zpow]
  have ψsmul : ∀ {T : Over S} (x : T ⟶ A) (c : ℤ) v, x ≫ ψ (c • v) = (x ^ c) ≫ ψ v := fun x c v =>
    ext _ _ fun u => by rw [hψ', hψ', ← _root_.zpow_mul, Pi.smul_apply, smul_eq_mul]
  have ψρ : ∀ {T : Over S} (x : T ⟶ A) v m, (x ≫ ψ v) ≫ ρ m = x ≫ ψ (m *ᵥ v) := fun x v m =>
    ext _ _ fun u => by
      rw [hψ', Category.assoc, hρ, List.prod_ofFn, comp_prod_zpow]
      simp only [hψ', ← _root_.zpow_mul, prod_zpow_eq]
      congr 1
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have ρdec : ∀ m, ρ m = ∏ v, pr v ≫ ψ (m *ᵥ Pi.single v 1) := fun m =>
    ext _ _ fun u => by
      rw [hρ, List.prod_ofFn, prod_comp_hom]
      refine Finset.prod_congr rfl fun v _ => ?_
      rw [hψ']
      simp
  have iddec : 𝟙 G = ∏ v, pr v ≫ ψ (Pi.single v 1) :=
    ext _ _ fun u => by
      rw [Category.id_comp, prod_comp_hom, Finset.prod_eq_single u (fun b _ hb => by
        rw [hψ', Pi.single_eq_of_ne' hb, zpow_zero]) (by simp), hψ', Pi.single_eq_same, zpow_one]
  have lamL : ∀ {T : Over S} (x y z : T ⟶ G),
      lam (cls L hL) (x * y) z = lam (cls L hL) x z + lam (cls L hL) y z := by
    intro T x y z
    have h₀ := (cls_eq_zero_iff (N := Theta G L) (LB.isLB_linComb hL _ _)).2 hΘ
    have h₁ := (cls_cube_three hL (fst _ _) (snd _ _ ≫ fst _ _) (snd G (G ⊗ G) ≫ snd _ _)
      (LB.isLB_linComb hL _ _)).symm.trans h₀
    have h₂ := congrArg (pull (lift x (lift y z)).left) h₁
    simp only [map_sub, map_zero, pull_lam, MonObj.comp_mul, lift_fst, lift_snd_assoc, lift_snd] at h₂
    rw [sub_sub, sub_eq_zero] at h₂
    exact h₂
  obtain ⟨l, hl⟩ : ∃ l, l = cls L hL := ⟨_, rfl⟩
  rw [← hl] at lamL
  have lamR : ∀ {T : Over S} (x y z : T ⟶ G), lam l z (x * y) = lam l z x + lam l z y := fun x y z => by
    rw [lam_comm, lamL, lam_comm l x, lam_comm l y]
  have adj : ∀ {T : Over S} (x y : T ⟶ G) m m', m.transpose * B = B * m' →
      lam l (x ≫ ρ m) y = lam l x (y ≫ ρ m') := by
    intro T x y m m' hm
    have h := (cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hL _ _)).2 (hadj m m' hm)
    have h' := congrArg (pull (lift x y).left)
      ((cls_cube_two hL _ _ _).symm.trans (h.trans (cls_cube_two hL _ _ _)))
    simpa only [pull_lam, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc, ← hl] using h'
  obtain ⟨p, hp⟩ : ∃ p : ∀ {T : Over S}, (T ⟶ A) → (T ⟶ A) → Pic T.left,
      ∀ {T : Over S} (x y : T ⟶ A), p x y = lam l (x ≫ ψ u₀) (y ≫ ψ u₁) := ⟨_, fun _ _ => rfl⟩
  have pL : ∀ {T : Over S} (x x' y : T ⟶ A), p (x * x') y = p x y + p x' y := fun x x' y => by
    rw [hp, hp, hp, ψmul, lamL]
  have pR : ∀ {T : Over S} (x x' y : T ⟶ A), p y (x * x') = p y x + p y x' := fun x x' y => by
    rw [hp, hp, hp, ψmul, lamR]
  have key : ∀ {T : Over S} (x y : T ⟶ A) v v', lam l (x ≫ ψ v) (y ≫ ψ v') = (v ⬝ᵥ B *ᵥ v') • p x y := by
    intro T x y v v'
    have h := adj (x ≫ ψ u₀) (y ≫ ψ v') (vecMulVec v u₀) (vecMulVec u₁ (B *ᵥ v)) (by
      rw [Matrix.transpose_vecMulVec, Matrix.vecMulVec_mul, Matrix.mul_vecMulVec, hu₁, ← Matrix.mulVec_transpose, hBs])
    have e₁ : vecMulVec v u₀ *ᵥ u₀ = v := by
      rw [Matrix.vecMulVec_mulVec, h00]; simp
    have e₂ : vecMulVec u₁ (B *ᵥ v) *ᵥ v' = (v ⬝ᵥ B *ᵥ v') • u₁ := by
      rw [Matrix.vecMulVec_mulVec, dotProduct_comm, hsymB v' v]; simp
    rw [ψρ, ψρ, e₁, e₂, ψsmul, ← hp] at h
    rw [h]
    exact map_zpow_add (fun z => p x z) (fun a b => pR a b x) y _
  have pS : ∀ {T : Over S} (x y : T ⟶ A), p y x = p x y := fun x y => by
    rw [hp, lam_comm, key, hsymB, hu₁, h00, one_smul]
  have hP : (cubeLB G ![fst A A ≫ ψ u₀, snd A A ≫ ψ u₁] L).IsLB := LB.isLB_linComb hL _ _
  have hc : cls _ hP = p (fst A A) (snd A A) := by rw [cls_cube_two hL, hp, hl]
  have hpull : ∀ {T : Over S} (x y : T ⟶ A), pull (lift x y).left (cls _ hP) = p x y := fun x y => by
    rw [hc, hp, hp, pull_lam, lift_fst_assoc, lift_snd_assoc]
  refine ⟨cubeLB G ![fst A A ≫ ψ u₀, snd A A ≫ ψ u₁] L, hP, ?_, ?_, ?_, fun T x x' y => ⟨?_, ?_⟩, ?_⟩
  · refine (cls_eq_zero_iff (pull_isLB hP _)).1 ?_
    rw [cls_pull hP, hpull, hp, ψone, lam_one_left]
  · refine (cls_eq_zero_iff (pull_isLB hP _)).1 ?_
    rw [cls_pull hP, hpull, hp, ψone, lam_one_right]
  · refine (cls_eq_iff hP (pull_isLB hP _)).1 ?_
    rw [cls_pull hP, hpull, hc, pS]
  · refine (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).1 ?_
    rw [cls_linComb hP, Fin.sum_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_smul, neg_smul, hpull, pL]
    abel
  · refine (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).1 ?_
    rw [cls_linComb hP, Fin.sum_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_smul, neg_smul, hpull, pR]
    abel
  · refine (cls_eq_iff hL (LB.isLB_linComb hP _ _)).1 ?_
    have hw : B * (B⁻¹ * W) = W := by rw [← Matrix.mul_assoc, hBi, Matrix.one_mul]
    have h := ((cls_eq_iff hL (LB.isLB_linComb hL _ _)).2 (hprim _ hw)).trans (cls_cube_two hL _ _ _)
    rw [cls_linComb hP, h, ← hl, Fintype.sum_prod_type, iddec, ρdec,
      map_prod_add (fun z => lam l z _) (fun a b => lamL a b _)]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [map_prod_add (fun z => lam l _ z) (fun a b => lamR a b _)]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [key, hpull, Matrix.mulVec_mulVec, hw]
    congr 1
    simp

end GlobalTheory.EighthPower
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSymmetricBiadditiveBundleEighthPowerStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symmetric_biadditive_bundle_eighthPower : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (S : Scheme.{0}) (G A : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A] (pr : Fin 8 → (G ⟶ A)) (L : LB G.left) (ρ : Matrix (Fin 8) (Fin 8) ℤ → (G ⟶ G)), IsE8 W → (∀ u, IsMonHom (pr u)) → (∀ (T : Over S) (y : Fin 8 → (T ⟶ A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u) → L.IsLB → (∃ t : LB.Gen (Theta G L), t.IsGen) → (∀ m u, ρ m ≫ pr u = (List.ofFn fun v => pr v ^ m u v).prod) → (∀ m m', m.transpose * (W + W.transpose) = (W + W.transpose) * m' → LBIso (cubeLB G ![fst G G ≫ ρ m, snd G G] L) (cubeLB G ![fst G G, snd G G ≫ ρ m'] L)) → (∀ m, (W + W.transpose) * m = W → LBIso L (cubeLB G ![𝟙 G, ρ m] L)) → ∃ P : LB (G2 A).left, P.IsLB ∧ (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) ∧ (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) ∧ LBIso P (P.pull (lift (snd A A) (fst A A)).left) ∧ (∀ (T : Over S) (x x' y : T ⟶ A), (∃ t : (LB.LinComb P (K := Fin 3) ![(lift (x * x') y).left, (lift x y).left, (lift x' y).left] ![1, -1, -1]).Gen, t.IsGen) ∧ ∃ t : (LB.LinComb P (K := Fin 3) ![(lift y (x * x')).left, (lift y x).left, (lift y x').left] ![1, -1, -1]).Gen, t.IsGen) ∧ LBIso L (LB.LinComb P (K := Fin 8 × Fin 8) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)) := by
  first | exact @GlobalTheory.EighthPower.main | exact GlobalTheory.EighthPower.main | (intros; apply GlobalTheory.EighthPower.main <;> assumption)
end
end
