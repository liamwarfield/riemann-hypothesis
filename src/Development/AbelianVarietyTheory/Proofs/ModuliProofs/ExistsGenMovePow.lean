module

public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ThetaGrpActsLinearly
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGenOfSection
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SecCoordBcScaleUnique
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsMvPolynomialOfPolyBoundOffHypersurface
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsConnectedUnramifiedCoverOfIrreducible
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.JacobsonClosedPointsToolsInt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenMovePow
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.WeilIsogeny

open CommutatorPairing

section Gen

variable {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε ε' : K → ℤ}

theorem wchart_le_pow (d : ℕ) (j : K → L.ι) : LB.wchart L φ j ≤ LB.wchart (lbPow L d) φ (fun k _ => j k) :=
  fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy k

theorem exists_gen_of_lbPow (d : ℕ) (hε : ∀ k, ε' k = ε k * d) (a : LB.Gen (LB.LinComb (lbPow L d) φ ε))
    (ha : a.IsGen) : ∃ u : LB.Gen (LB.LinComb L φ ε'), u.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : K → L.ι), r z ∈ LB.wchart L φ j →
        gm r z (LB.wchart L φ j) (u.s j) = gm r z (LB.wchart (lbPow L d) φ (fun k _ => j k)) (a.s fun k _ => j k) := by
  refine ⟨⟨fun j => res (wchart_le_pow d j) (a.s fun k _ => j k)⟩, fun j j' => unit_ext fun y hy => ?_,
    fun Z r z j hj => gm_res r z _ hj _⟩
  refine (gm_res _ y _ hy _).trans ((gm_res _ y _ hy.1 _).trans (Eq.trans ?_ ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (gm_linComb L φ ε' (𝟙 Y) y j j' hy.1 hy.2)
      ((gm_res _ y _ hy _).trans (gm_res _ y _ hy.2 _)))).symm))
  refine (gen_trans ha (𝟙 Y) y (wchart_le_pow d j hy.1) (wchart_le_pow d j' hy.2)).trans (congrArg (· * _) ?_)
  refine Finset.prod_congr rfl fun k _ => ?_
  have e := gm_linComb L (fun _ : PUnit => 𝟙 X) (fun _ => (d : ℤ)) (𝟙 Y ≫ φ k) y (fun _ => j k) (fun _ => j' k)
    (Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy.1 k) (Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy.2 k)
  rw [Fintype.prod_unique, Category.comp_id] at e
  refine (congrArg (· ^ ε k) e).trans ?_
  rw [hε, mul_comm (ε k), zpow_mul]

theorem exists_gen_pow (d : ℕ) (hε : ∀ k, ε' k = ε k * d) (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) :
    ∃ u : LB.Gen (LB.LinComb L φ ε'), u.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), val u r z J = val t r z J ^ d := by
  refine ⟨⟨fun j => t.s j ^ d⟩, fun i j => ?_, fun Z r z J => map_pow _ _ _⟩
  have h := congrArg (· ^ d) (ht i j)
  simp only [mul_pow, ← map_pow] at h
  refine h.trans (congrArg₂ (· * ·) ?_ rfl)
  refine (Finset.prod_pow _ _ _).symm.trans (Finset.prod_congr rfl fun a _ => ?_)
  exact ((zpow_natCast _ _).symm.trans (zpow_mul _ _ _).symm).trans (congrArg _ (hε a).symm)

theorem exists_gen_move_pow {X₀ Y₀ : Scheme.{0}} {M : LB X₀} {F : X ⟶ X₀} (hL : L.IsLB) (hM : M.IsLB) {d : ℕ}
    (w : LB.Iso (lbPow L d) (M.pull F)) (hw : w.IsGen) (hε : ∀ k, ε' k = ε k * d) {φ₀ : K → (Y₀ ⟶ X₀)} (h : Y ⟶ Y₀)
    (hc : ∀ k, φ k ≫ F = h ≫ φ₀ k) (t : LB.Gen (LB.LinComb M φ₀ ε)) (ht : t.IsGen) :
    ∃ u : LB.Gen (LB.LinComb L φ ε'), u.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J J₀),
      Good L z J → Good M z J₀ → val t (r ≫ h) z J₀ =
        (∏ k, (fun χ : Z ⟶ X => gw w χ z (J₀ (χ ≫ F)) (fun _ => J χ)) (r ≫ φ k) ^ ε k) * val u r z J := by
  obtain ⟨b, hb, hm⟩ := H1.exists_gen_move hM (DVR.linComb_isLB L hL _ _) w ((isGen_iff w).1 hw) φ₀ φ ε h hc t ht
  obtain ⟨u, hu, hv⟩ := exists_gen_of_lbPow d hε b hb
  refine ⟨u, hu, fun Z r z J J₀ hJ hJ₀ => ?_⟩
  have m := hm _ r z (fun i => J₀ ((r ≫ φ i) ≫ F)) (fun i _ => J (r ≫ φ i))
    (fun i => hJ₀ ((r ≫ φ i) ≫ F)) (fun i => Set.mem_iInter.2 fun _ => hJ (r ≫ φ i))
  exact (val_of t _ z J₀ _ (fun i => congrArg J₀ (by rw [Category.assoc, Category.assoc, hc]))).trans
    (m.trans (congrArg (_ * ·) (hv _ r z _ (hJ.mem φ r)).symm))

end Gen

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] {L : LB A.left} {M : LB B.left}

theorem weilIs_of_local (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {k : ℤ} {T : Over S}
    {x y : T ⟶ A} {c : Γ(T.left, ⊤)ˣ}
    (h : ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧ ∃ θx θy : ThetaGrp A L k (overRes V),
      θx.pt = overResι V ≫ x ∧ θy.pt = overResι V ≫ y ∧ CommIsOf A L k θx θy (unitRes V c)) :
    WeilIs A L k x y c := by
  intro p
  obtain ⟨V, hV, θx, θy, ex, ey, H⟩ := h p
  refine ⟨V, hV, ⟨θx, θy, ex, ey⟩, fun θ θ' e e' => (commIsOf_iff hL _ _ _).2 fun Z t b z J hJ => ?_⟩
  exact (commVal_indep hG hA hL θ θ' θx θy t t (by rw [e, ex]) (by rw [e', ey]) b z J hJ).trans
    ((commIsOf_iff hL _ _ _).1 H _ t b z J hJ)

theorem exists_theta_pow (d : ℕ) {n : ℤ} {T : Over S} (θ : ThetaGrp A L n T) :
    ∃ θ' : ThetaGrp A L (n * d) T, θ'.pt = θ.pt ∧ ∀ (Z : Over S) (t : Z ⟶ T) (a : Z ⟶ A) (z : Z.left) (J),
      thetaVal θ' t a z J = thetaVal θ t a z J ^ d := by
  obtain ⟨u, hu, hv⟩ := exists_gen_pow (L := L) (K := Fin 2) (φ := ![(snd T A).left, (translPt A θ.pt).left])
    (ε := ![n, -n]) (ε' := ![n * d, -(n * d)]) d (fun k => by fin_cases k <;> simp) θ.φ θ.isGen
  exact ⟨⟨θ.pt, u, hu⟩, rfl, fun Z t a z J => hv _ _ z J⟩

theorem weilIs_pow (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) (d : ℕ) {n : ℤ} {T : Over S}
    {x y : T ⟶ A} {c : Γ(T.left, ⊤)ˣ} (h : WeilIs A L n x y c) : WeilIs A L (n * d) x y (c ^ d) := by
  refine weilIs_of_local hG hA hL fun p => ?_
  obtain ⟨V, hV, ⟨θx, θy, ex, ey⟩, H⟩ := h p
  obtain ⟨θx', fx, vx⟩ := exists_theta_pow d θx
  obtain ⟨θy', fy, vy⟩ := exists_theta_pow d θy
  refine ⟨V, hV, θx', θy', fx.trans ex, fy.trans ey, (commIsOf_iff hL _ _ _).2 fun Z t a z J hJ => ?_⟩
  have e := (commIsOf_iff hL _ _ _).1 (H θx θy ex ey) Z t a z J hJ
  have e' : unitRes V (c ^ d) = unitRes V c ^ d := map_pow _ _ _
  rw [e', map_pow, ← e, commVal, commVal, vx, vx, vy, vy, fx, fy]
  simp only [mul_pow, inv_pow]

theorem exists_theta_pull (hL : L.IsLB) (hM : M.IsLB) (ψ : A ⟶ B) [IsMonHom ψ] {d : ℕ}
    (w : LB.Iso (lbPow L d) (M.pull ψ.left)) (hw : w.IsGen) {n : ℤ} {T : Over S} (x : T ⟶ A)
    (θ₀ : ThetaGrp B M n T) (hx : θ₀.pt = x ≫ ψ) :
    ∃ θ : ThetaGrp A L (n * d) T, θ.pt = x ∧ ∀ (Z : Over S) (t : Z ⟶ T) (a : Z ⟶ A) (z : Z.left) (J J₀),
      Good L z J → Good M z J₀ → thetaVal θ₀ t (a ≫ ψ) z J₀ =
        gw w a.left z (J₀ (a ≫ ψ).left) (fun _ => J a.left) ^ n *
          gw w ((t ≫ x) * a).left z (J₀ (((t ≫ x) * a) ≫ ψ).left) (fun _ => J ((t ≫ x) * a).left) ^ (-n) *
          thetaVal θ t a z J := by
  have hl : ∀ {Z : Over S} (t : Z ⟶ T) (a : Z ⟶ A), lift t a ≫ (T ◁ ψ) = lift t (a ≫ ψ) := fun t a => by simp
  have h₀ : snd T A ≫ ψ = (T ◁ ψ) ≫ snd T B := by simp
  have h₁ : translPt A x ≫ ψ = (T ◁ ψ) ≫ translPt B θ₀.pt := by
    show ((fst T A ≫ x) * snd T A) ≫ ψ = (T ◁ ψ) ≫ ((fst T B ≫ θ₀.pt) * snd T B)
    rw [MonObj.comp_mul, MonObj.mul_comp, hx]
    simp
  have hc : ∀ i : Fin 2, ![(snd T A).left, (translPt A x).left] i ≫ ψ.left =
      (T ◁ ψ).left ≫ ![(snd T B).left, (translPt B θ₀.pt).left] i := fun i => by
    fin_cases i
    · exact congrArg CommaMorphism.left h₀
    · exact congrArg CommaMorphism.left h₁
  obtain ⟨u, hu, hv⟩ := exists_gen_move_pow (ε := ![n, -n]) (ε' := ![n * d, -(n * d)]) hL hM w hw
    (fun k => by fin_cases k <;> simp) (T ◁ ψ).left hc θ₀.φ θ₀.isGen
  refine ⟨⟨x, u, hu⟩, rfl, fun Z t a z J J₀ hJ hJ₀ => ?_⟩
  have m := hv _ (lift t a).left z J J₀ hJ hJ₀
  rw [← Over.comp_left, hl, prod_theta x t a
    (fun χ : Z.left ⟶ A.left => gw w χ z (J₀ (χ ≫ ψ.left)) (fun _ => J χ))] at m
  exact m

theorem weilIs_pull_hom (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) (hM : M.IsLB) (ψ : A ⟶ B)
    [IsMonHom ψ] {d : ℕ} (hw : LBIso (lbPow L d) (M.pull ψ.left)) {n : ℤ} {T : Over S} {x y : T ⟶ A}
    {c : Γ(T.left, ⊤)ˣ} (h : WeilIs B M n (x ≫ ψ) (y ≫ ψ) c) : WeilIs A L (n * d) x y c := by
  obtain ⟨w, hw⟩ := hw
  have := hA.comm
  refine weilIs_of_local hG hA hL fun p => ?_
  obtain ⟨V, hV, ⟨θx₀, θy₀, ex, ey⟩, H⟩ := h p
  obtain ⟨θx, fx, vx⟩ := exists_theta_pull hL hM ψ w hw (overResι V ≫ x) θx₀ (by rw [ex, Category.assoc])
  obtain ⟨θy, fy, vy⟩ := exists_theta_pull hL hM ψ w hw (overResι V ≫ y) θy₀ (by rw [ey, Category.assoc])
  refine ⟨V, hV, θx, θy, fx, fy, (commIsOf_iff hL _ _ _).2 fun Z t a z J hJ => ?_⟩
  choose J₀ hJ₀ using fun χ : Z.left ⟶ B.left => exists_chart hM (χ z)
  have e := (commIsOf_iff hM _ _ _).1 (H θx₀ θy₀ ex ey) Z t (a ≫ ψ) z J₀ hJ₀
  have gx : (t ≫ θx₀.pt) * (a ≫ ψ) = ((t ≫ overResι V ≫ x) * a) ≫ ψ := by
    rw [MonObj.mul_comp, ex]; simp only [Category.assoc]
  have gy : (t ≫ θy₀.pt) * (a ≫ ψ) = ((t ≫ overResι V ≫ y) * a) ≫ ψ := by
    rw [MonObj.mul_comp, ey]; simp only [Category.assoc]
  rw [← e, commVal, commVal, gx, gy, vx _ _ _ _ _ _ hJ hJ₀, vx _ _ _ _ _ _ hJ hJ₀, vy _ _ _ _ _ _ hJ hJ₀,
    vy _ _ _ _ _ _ hJ hJ₀, fx, fy, mul_left_comm (t ≫ overResι V ≫ y) (t ≫ overResι V ≫ x) a]
  simp only [zpow_neg]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.WeilIsogeny

namespace GlobalTheory

theorem weilIs_along_hom : Out.GlobalFnsSt → ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (ψ : A ⟶ B)
    (L : LB A.left) (M : LB B.left) (d : ℕ) (n : ℤ) (T : Over S) (x y : T ⟶ A) (c c' : Γ(T.left, ⊤)ˣ),
    IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → IsMonHom ψ → LBIso (lbPow L d) (M.pull ψ.left) →
    Out.WeilIs B M n (x ≫ ψ) (y ≫ ψ) c' →
      Out.WeilIs A L (n * d) x y c' ∧ (Out.WeilIs A L n x y c → c' = c ^ d) := by
  intro hG S A B _ _ ψ L M d n T x y c c' hA _ hL hM hψ hw h
  have h' := WeilIsogeny.weilIs_pull_hom hG hA hL hM ψ hw h
  exact ⟨h', fun hc => CommutatorPairing.weilIs_unique hG hA hL h' (WeilIsogeny.weilIs_pow hG hA hL d hc)⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueFactorThroughEtaleIsogenyReduced
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueFactorThroughEtaleIsogenyReduced
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkFactor

lemma ext_of_geometricPoints {T X Z : Scheme.{0}} [IsReduced T] (q : X ⟶ Z) [IsSeparated q]
    (f g : T ⟶ X) (h : f ≫ q = g ≫ q)
    (H : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T), x ≫ f = x ≫ g) : f = g := by
  classical

  let K : T → Type := fun t => AlgebraicClosure (T.residueField t)
  let pts : (∐ fun t : T => Sp (K t)) ⟶ T := Sigma.desc fun t =>
    Spec.map (CommRingCat.ofHom (algebraMap (T.residueField t) (K t))) ≫ T.fromSpecResidueField t

  have : Surjective pts := by
    refine ⟨fun t => ⟨Sigma.ι (fun t : T => Sp (K t)) t (IsLocalRing.closedPoint (K t)), ?_⟩⟩
    have e : (Sigma.ι (fun t : T => Sp (K t)) t ≫ pts) (IsLocalRing.closedPoint (K t)) = t := by
      simp only [pts, Sigma.ι_desc]
      exact (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply _ _)
    exact (Scheme.Hom.comp_apply _ _ _).symm.trans e
  refine ext_of_isDominant_of_isSeparated q h pts ?_
  refine Sigma.hom_ext _ _ fun t => ?_
  simpa only [pts, Sigma.ι_desc_assoc] using H (K t) _

theorem exists_unique_factor : ∀ (S : Scheme.{0}) [IsReduced S] (A B B' : Over S) [GrpObj A] [GrpObj B] [GrpObj B'] (ψ : A ⟶ B) (g : A ⟶ B'), IsAbelianScheme A → IsAbelianScheme B → IsSeparated B'.hom → IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → IsMonHom g → (∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S) (x : Over.mk t ⟶ A), x ≫ ψ = 1 → x ≫ g = 1) → ∃ g' : B ⟶ B', IsMonHom g' ∧ ψ ≫ g' = g ∧ ∀ g'' : B ⟶ B', ψ ≫ g'' = g → g'' = g' := by
  intro S _ A B B' _ _ _ ψ g _ _ hsep hψ hfin het hsurj hg H

  let T : Over S := pullback ψ η[B]
  let i : T ⟶ A := pullback.fst ψ η[B]
  have hker : IsPullback i (toUnit T) ψ η[B] := by
    have hp := IsPullback.of_hasPullback ψ η[B]
    rwa [toUnit_unique (pullback.snd ψ η[B]) (toUnit T)] at hp

  have : IsReduced T.left := by
    have hp : IsPullback i.left (toUnit T).left ψ.left (η[B]).left := hker.map (Over.forget S)
    have : Etale (toUnit T).left := MorphismProperty.of_isPullback hp het
    have : IsReduced (𝟙_ (Over S)).left := by dsimp; infer_instance
    exact GlobalTheory.isReduced_of_smooth_of_isReduced (toUnit T).left
  have := hsep

  have hf : i ≫ g = toUnit T ≫ η[B'] := by
    apply Over.OverMorphism.ext
    refine ext_of_geometricPoints B'.hom _ _ (by rw [Over.w, Over.w]) ?_
    intro k _ _ x
    let xo : Over.mk (x ≫ T.hom) ⟶ T := Over.homMk x
    have e1 : (xo ≫ i) ≫ ψ = 1 := by
      rw [Category.assoc, hker.w, ← Category.assoc, Hom.one_def, toUnit_unique (xo ≫ toUnit T) (toUnit _)]
    have e3 : xo ≫ (i ≫ g) = xo ≫ (toUnit T ≫ η[B']) := by
      rw [← Category.assoc, H k (x ≫ T.hom) (xo ≫ i) e1, Hom.one_def, ← Category.assoc,
        toUnit_unique (xo ≫ toUnit T) (toUnit _)]
    simpa only [xo, Over.comp_left, Over.homMk_left] using congrArg CommaMorphism.left e3
  have := hψ; have := hg; have := hfin; have := het; have := hsurj
  obtain ⟨β, hβ, hψβ⟩ := FlatQuotient.exists_desc ψ i g hker hf
  have : Epi ψ := FlatQuotient.epi_of_flat_surjective ψ
  exact ⟨β, hβ, hψβ, fun g'' h'' => (cancel_epi ψ).1 (h''.trans hψβ.symm)⟩

end GlobalTheory.HkFactor
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueFactorThroughEtaleIsogenyReducedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unique_factor_through_etale_isogeny_reduced : ∀ (S : Scheme.{0}) [IsReduced S] (A B B' : Over S) [GrpObj A] [GrpObj B] [GrpObj B'] (ψ : A ⟶ B) (g : A ⟶ B'), IsAbelianScheme A → IsAbelianScheme B → IsSeparated B'.hom → IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → IsMonHom g → (∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S) (x : Over.mk t ⟶ A), x ≫ ψ = 1 → x ≫ g = 1) → ∃ g' : B ⟶ B', IsMonHom g' ∧ ψ ≫ g' = g ∧ ∀ g'' : B ⟶ B', ψ ≫ g'' = g → g'' = g' := by
  first | exact @GlobalTheory.HkFactor.exists_unique_factor | exact GlobalTheory.HkFactor.exists_unique_factor | (intros; apply GlobalTheory.HkFactor.exists_unique_factor <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenOfIsLocallyNoetherian
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PairingLocus

theorem exists_idempotent {R : Type} [CommRing R] {n : ℕ} (hn : IsUnit (n : R)) {u : R} (hu : u ^ n = 1) :
    ∃ e : R, IsIdempotentElem e ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R'), φ u = 1 ↔ φ e = 1 := by
  obtain ⟨m, hm⟩ := hn.exists_left_inv
  have h₀ : (∑ i ∈ Finset.range n, u ^ i) * (u - 1) = 0 := by rw [geom_sum_mul, hu, sub_self]
  have h₁ : u * (m * ∑ i ∈ Finset.range n, u ^ i) = m * ∑ i ∈ Finset.range n, u ^ i := by
    linear_combination m * h₀
  have h₂ : ∀ i : ℕ, u ^ i * (m * ∑ i ∈ Finset.range n, u ^ i) = m * ∑ i ∈ Finset.range n, u ^ i := by
    intro i
    induction i with
    | zero => rw [pow_zero, _root_.one_mul]
    | succ i ih => rw [pow_succ, _root_.mul_assoc, h₁, ih]
  refine ⟨m * ∑ i ∈ Finset.range n, u ^ i, ?_, fun R' _ φ => ⟨fun h => ?_, fun h => ?_⟩⟩
  · show _ * _ = _
    rw [_root_.mul_assoc, Finset.sum_mul, Finset.sum_congr rfl fun i _ => h₂ i, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, ← _root_.mul_assoc, hm, _root_.one_mul]
  · have := congrArg φ hm
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_mul, map_sum, map_pow, h, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      _root_.mul_one, map_natCast, map_one] at this ⊢
    exact this
  · have := congrArg φ h₁
    rwa [map_mul, h, _root_.mul_one] at this

theorem isClosed_basicOpen {X : Scheme.{0}} {e : Γ(X, ⊤)} (he : IsIdempotentElem e) :
    IsClosed (X.basicOpen e : Set X) := by
  have : (X.basicOpen e : Set X) = (X.basicOpen (1 - e) : Set X)ᶜ := by
    ext x
    constructor
    · intro h h'
      have hx : x ∈ X.basicOpen (e * (1 - e)) := by rw [Scheme.basicOpen_mul]; exact ⟨h, h'⟩
      rw [he.mul_one_sub_self, Scheme.basicOpen_zero] at hx
      exact hx
    · intro h
      rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (X.presheaf.germ ⊤ x trivial e) with h' | h'
      · exact (X.mem_basicOpen e x trivial).2 h'
      · exact absurd ((X.mem_basicOpen (U := ⊤) (1 - e) x trivial).2 (by rwa [map_sub, map_one])) h
  rw [this]
  exact (X.basicOpen (1 - e)).isOpen.isClosed_compl

theorem appTop_eq_one_iff {X Y : Scheme.{0}} {e : Γ(X, ⊤)} (he : IsIdempotentElem e) (h : Y ⟶ X) :
    h.appTop.hom e = 1 ↔ Set.range h ⊆ X.basicOpen e := by
  have p : h ⁻¹ᵁ X.basicOpen e = Y.basicOpen (h.appTop.hom e) := Scheme.preimage_basicOpen h e
  constructor
  · rintro H _ ⟨y, rfl⟩
    have : y ∈ h ⁻¹ᵁ X.basicOpen e := by
      rw [p, H, Scheme.basicOpen_of_isUnit _ isUnit_one]; trivial
    exact this
  · intro H
    have hu : IsUnit (h.appTop.hom e) := by
      refine RingedSpace.isUnit_of_isUnit_germ Y.toRingedSpace ⊤ _ fun y hy => ?_
      have : y ∈ Y.basicOpen (h.appTop.hom e) := by rw [← p]; exact H ⟨y, rfl⟩
      exact (Y.mem_basicOpen _ y hy).1 this
    exact hu.mul_left_cancel ((he.map h.appTop.hom).eq.trans (_root_.mul_one _).symm)

theorem exists_clopen_eq {X : Scheme.{0}} {n : ℕ} (hn : IsUnit (n : Γ(X, ⊤))) {c c₀ : Γ(X, ⊤)ˣ}
    (hc : c ^ n = 1) (hc₀ : c₀ ^ n = 1) :
    ∃ U : X.Opens, IsClosed (U : Set X) ∧ ∀ (Y : Scheme.{0}) (h : Y ⟶ X),
      Units.map h.appTop.hom.toMonoidHom c = Units.map h.appTop.hom.toMonoidHom c₀ ↔ Set.range h ⊆ U := by
  have hu : (c * c₀⁻¹).val ^ n = 1 := by
    rw [← Units.val_pow_eq_pow_val, mul_pow, inv_pow, hc, hc₀, inv_one, _root_.mul_one, Units.val_one]
  obtain ⟨e, he, H⟩ := exists_idempotent hn hu
  refine ⟨X.basicOpen e, isClosed_basicOpen he, fun Y h => ?_⟩
  rw [← appTop_eq_one_iff he, ← H, ← mul_inv_eq_one, ← map_inv, ← map_mul, ← Units.val_eq_one]
  rfl

theorem pow_eq_one (hG : GlobalFnsSt) {S : Scheme.{0}} (P : PolAV S) (k : ℕ) {T : Over S} {x y : T ⟶ P.A}
    (hx : x ^ k = 1) {c : Γ(T.left, ⊤)ˣ} (hc : WeilIs P.A P.L k x y c) : c ^ k = 1 := by
  have hpow : ∀ j : ℕ, WeilIs P.A P.L k (x ^ (j + 1)) y (c ^ (j + 1)) := by
    intro j
    induction j with
    | zero => rwa [zero_add, pow_one, pow_one]
    | succ j ih => rw [pow_succ, pow_succ c]; exact weilIs_mul_left hG S P k T _ _ _ _ _ ih hc
  have h := hpow k
  rw [pow_succ, hx, _root_.one_mul] at h
  have := CommutatorPairing.weilIs_unique hG P.isAb P.isLB h hc
  rwa [pow_succ, mul_eq_right] at this

theorem exists_clopen_of_weilIs (hG : GlobalFnsSt) {S : Scheme.{0}} (P : PolAV S) (n : ℕ) {T : Over S}
    {x y : T ⟶ P.A} {c c₀ : Γ(T.left, ⊤)ˣ} (hn : IsUnit (n : Γ(T.left, ⊤))) (hx : x ^ n = 1) (hc : c ^ n = 1)
    (h₀ : WeilIs P.A P.L n x y c₀) :
    ∃ U : T.left.Opens, IsClosed (U : Set T.left) ∧ ∀ (T' : Over S) (h : T' ⟶ T),
      WeilIs P.A P.L n (h ≫ x) (h ≫ y) (Units.map (h.left.appTop).hom.toMonoidHom c) ↔ Set.range h.left ⊆ U := by
  obtain ⟨U, hU, H⟩ := exists_clopen_eq hn hc (pow_eq_one hG P n hx h₀)
  refine ⟨U, hU, fun T' h => ?_⟩
  have h₁ := CommPairing.weilIs_pull hG P.isAb P.isLB h h₀
  rw [← H]
  exact ⟨fun h₂ => CommutatorPairing.weilIs_unique hG P.isAb P.isLB h₂ h₁, fun e => e ▸ h₁⟩

theorem exists_clopen_of_lift : GlobalFnsSt → (∀ (S : Scheme.{0}) (P : PolAV S) (N : ℕ) (T : Over S) (x : T ⟶ P.A),
    x ^ N = 1 → ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧
      ∃ θ : ThetaGrp P.A P.L N (overRes V), θ.pt = overResι V ≫ x) →
    ∀ (S : Scheme.{0}) (P : PolAV S) (n : ℕ) (T : Over S) (x y : T ⟶ P.A) (c : Γ(T.left, ⊤)ˣ), 0 < n →
      IsUnit (n : Γ(T.left, ⊤)) → x ^ n = 1 → y ^ n = 1 → c ^ n = 1 →
      ∃ U : T.left.Opens, IsClosed (U : Set T.left) ∧ ∀ (T' : Over S) (h : T' ⟶ T),
        WeilIs P.A P.L n (h ≫ x) (h ≫ y) (Units.map (h.left.appTop).hom.toMonoidHom c) ↔
          Set.range h.left ⊆ U := by
  intro hG hl S P n T x y c _ hn hx hy hc
  obtain ⟨c₀, h₀, -⟩ := CommutatorPairing.existsUnique_weilIs hG hl S P n T x y hx hy
  exact exists_clopen_of_weilIs hG P n hn hx hc h₀

theorem exists_clopen_of_isLocallyNoetherian (hL : Laws) (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S)
    (n : ℕ) (T : Over S) (x y : T ⟶ P.A) (c : Γ(T.left, ⊤)ˣ) (hn : IsUnit (n : Γ(T.left, ⊤))) (hx : x ^ n = 1)
    (hy : y ^ n = 1) (hc : c ^ n = 1) :
    ∃ U : T.left.Opens, IsClosed (U : Set T.left) ∧ ∀ (T' : Over S) (h : T' ⟶ T),
      WeilIs P.A P.L n (h ≫ x) (h ≫ y) (Units.map (h.left.appTop).hom.toMonoidHom c) ↔ Set.range h.left ⊆ U := by
  obtain ⟨c₀, h₀, -⟩ := (hL.weil S P n T).1 x y hx hy
  exact exists_clopen_of_weilIs hL.globalFns P n hn hx hc h₀

end GlobalTheory.PairingLocus
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SurjectiveAppTopPullbackSndOfApp
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

private theorem surjective_comp_isIso_of_surjective {A B C : CommRingCat} (a : A ⟶ B) (b : B ⟶ C) [IsIso b]
    (ha : Function.Surjective a.hom) : Function.Surjective (a ≫ b).hom := by
  intro y
  obtain ⟨z, rfl⟩ := (ConcreteCategory.bijective_of_isIso b).2 y
  obtain ⟨w, rfl⟩ := ha z
  exact ⟨w, rfl⟩

theorem surjective_appTop_pullback_snd_of_app {X S : Scheme.{0}} (f : X ⟶ S) (V : S.Opens)
    (h : ∀ U : S.Opens, Function.Surjective (f.app U).hom) :
    Function.Surjective (pullback.snd f V.ι).appTop.hom := by
  have hr : Function.Surjective (f ∣_ V).appTop.hom := by
    rw [morphismRestrict_appTop]
    exact @surjective_comp_isIso_of_surjective _ _ _ _ _ (Functor.map_isIso _ _) (h _)
  rw [← pullbackRestrictIsoRestrict_hom_morphismRestrict f V, Scheme.Hom.comp_appTop]
  exact @surjective_comp_isIso_of_surjective _ _ _ _ _
    (inferInstanceAs (IsIso ((pullbackRestrictIsoRestrict f V).hom.app ⊤))) hr

theorem exists_gen_of_local_of_section : ∀ (X S : Scheme.{0}) (f : X ⟶ S) (σ : S ⟶ X) (N : LB X), N.IsLB →
    σ ≫ f = 𝟙 S → (∀ U : S.Opens, Function.Surjective (f.app U).hom) →
    (∀ s : S, ∃ U : S.Opens, s ∈ U ∧ ∃ t : (N.pull (f ⁻¹ᵁ U).ι).Gen, t.IsGen) →
    (∃ t : (N.pull σ).Gen, t.IsGen) → ∃ t : N.Gen, t.IsGen := by
  intro X S f σ N hN hσ hf hl hg
  obtain ⟨c, hc⟩ := hg
  have hp : ∀ V : S.Opens, Function.Surjective (pullback.snd f V.ι).appTop.hom :=
    fun V => surjective_appTop_pullback_snd_of_app f V hf
  have e : σ ≫ f ≫ σ = σ := by rw [← Category.assoc, hσ, Category.id_comp]
  have h0 : ∀ (U : Type) [CommGroup U] (h : (S ⟶ X) → U),
      ∏ k, h (σ ≫ (![𝟙 X, f ≫ σ] : Fin 2 → (X ⟶ X)) k) ^ (![1, -1] : Fin 2 → ℤ) k = 1 := by
    intro U _ h
    simp [Fin.prod_univ_two, e]
  have hloc : ∀ s : S, ∃ U : S.Opens, s ∈ U ∧
      ∃ t : LB.Gen (LB.LinComb N (fun k => (f ⁻¹ᵁ U).ι ≫ (![𝟙 X, f ≫ σ] : Fin 2 → (X ⟶ X)) k)
        (![1, -1] : Fin 2 → ℤ)), t.IsGen := by
    intro s
    obtain ⟨U, hsU, t, ht⟩ := hl s
    refine ⟨U, hsU, ?_⟩
    let c₁ := LB.pullGen N (fun _ : PUnit => σ) (fun _ => 1) c ((f ⁻¹ᵁ U).ι ≫ f)
    have hc₁ : c₁.IsGen := ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen N _ _ c hc _
    let c₂ := LB.invGen N _ _ c₁
    have hc₂ : c₂.IsGen := ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen N _ _ c₁ hc₁
    let m := LB.mulGen N (fun _ : PUnit => (f ⁻¹ᵁ U).ι) (fun _ => 1) _ _ t c₂
    have hm : m.IsGen := ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen N _ _ _ _ t c₂ ht hc₂
    obtain ⟨g, hg, -⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_gen hN
      (φ' := fun k => (f ⁻¹ᵁ U).ι ≫ (![𝟙 X, f ≫ σ] : Fin 2 → (X ⟶ X)) k) (ε' := (![1, -1] : Fin 2 → ℤ))
      (by intro V _ h; simp [Fintype.prod_sum_type, Fin.prod_univ_two]) m hm
    exact ⟨g, hg⟩
  obtain ⟨u, hu⟩ := exists_gen_of_local_on_base hN (K := Fin 2) ![𝟙 X, f ≫ σ] ![1, -1] f σ hσ hp h0 hloc
  let c₃ := LB.pullGen N (fun _ : PUnit => σ) (fun _ => 1) c f
  have hc₃ : c₃.IsGen := ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen N _ _ c hc f
  let m₂ := LB.mulGen N _ _ _ _ u c₃
  have hm₂ : m₂.IsGen := ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen N _ _ _ _ u c₃ hu hc₃
  obtain ⟨g, hg, -⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_gen hN (φ' := fun _ : PUnit => 𝟙 X) (ε' := fun _ => 1)
    (by intro V _ h; simp [Fintype.prod_sum_type, Fin.prod_univ_two]) m₂ hm₂
  exact BoxTheta.exists_gen_of_section N (𝟙 X) (𝟙 X) (Category.id_comp _) g hg

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqOneOfAppLESectionEqOne
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory
namespace RigidFunction

theorem not_mem_basicOpen_fibre {X P F : Scheme.{0}} {K : Type} [Field K] {p : P ⟶ X}
    {t : Spec (CommRingCat.of K) ⟶ X} {φ : F ⟶ P} {q : F ⟶ Spec (CommRingCat.of K)} (w : φ ≫ p = q ≫ t)
    [IsIntegral F] [UniversallyClosed q] (V : X.Opens) (hV : ∀ x, t x ∈ V) (s : Γ(P, p ⁻¹ᵁ V)) (a b : F)
    (ha : φ a ∉ P.basicOpen s) : φ b ∉ P.basicOpen s := by
  have hle : (⊤ : F.Opens) ≤ φ ⁻¹ᵁ (p ⁻¹ᵁ V) := by
    intro c _
    change p (φ c) ∈ V
    rw [← Scheme.Hom.comp_apply, w, Scheme.Hom.comp_apply]
    exact hV _
  have key : ∀ c : F, φ c ∈ P.basicOpen s ↔ c ∈ F.basicOpen ((φ.appLE (p ⁻¹ᵁ V) ⊤ hle).hom s) := by
    intro c
    rw [Scheme.basicOpen_appLE]
    exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  rw [key] at ha ⊢
  have hF := isField_of_universallyClosed K q
  by_cases hs : (φ.appLE (p ⁻¹ᵁ V) ⊤ hle).hom s = 0
  · rw [hs, Scheme.basicOpen_zero]
    exact fun h => h
  · exfalso
    apply ha
    obtain ⟨v, hv⟩ := hF.mul_inv_cancel hs
    rw [Scheme.basicOpen_of_isUnit _ (isUnit_iff_exists_inv.mpr ⟨v, hv⟩)]
    trivial

end RigidFunction

theorem eq_one_of_appLE_section_eq_one :
    ∀ (X : Scheme.{0}) (P : Over X) (e : X ⟶ P.left), e ≫ P.hom = 𝟙 X → Smooth P.hom → GeometricallyIntegral P.hom → (IsReduced X ∧ genericPoints X ⊆ abLocus P) → (∀ (V : X.Opens) (u : Γ(P.left, P.hom ⁻¹ᵁ V)) (h : V ≤ e ⁻¹ᵁ (P.hom ⁻¹ᵁ V)), (e.appLE _ V h).hom u = 1 → u = 1) := by
  intro X P e he hsm hgi hXg V u h hu
  obtain ⟨hred, hgen⟩ := hXg
  have := hsm
  have := hgi
  have : IsReduced P.left := GlobalTheory.isReduced_of_smooth_of_isReduced P.hom

  have h0 : (e.appLE _ V h).hom (u - 1) = 0 := by rw [map_sub, map_one, hu, sub_self]
  rw [← sub_eq_zero, ← basicOpen_eq_bot_iff]
  by_contra hne
  rw [← TopologicalSpace.Opens.not_nonempty_iff_eq_bot, not_not] at hne

  have hopen := P.hom.isOpenMap _ (P.left.basicOpen (u - 1)).isOpen
  obtain ⟨x₀, ⟨y, hy, hyx₀⟩, hxg⟩ :=
    (dense_iff_closure_eq.mpr genericPoints.closure).inter_open_nonempty _ hopen (hne.image _)
  have hxV : x₀ ∈ V := by
    rw [← hyx₀]
    exact P.left.basicOpen_le _ hy
  have hxnot : e x₀ ∉ P.left.basicOpen (u - 1) := by
    intro hm
    have hmem : x₀ ∈ X.basicOpen ((e.appLE _ V h).hom (u - 1)) := by
      rw [Scheme.basicOpen_appLE]
      exact ⟨hxV, hm⟩
    rw [h0, Scheme.basicOpen_zero] at hmem
    exact hmem

  let K := AlgebraicClosure (X.residueField x₀)
  let t : Spec (.of K) ⟶ X :=
    Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x₀) K)) ≫ X.fromSpecResidueField x₀
  have ht : ∀ z, t z = x₀ := by
    intro z
    have hz : t z ∈ Set.range (X.fromSpecResidueField x₀) := ⟨_, (Scheme.Hom.comp_apply _ _ z).symm⟩
    rwa [Scheme.range_fromSpecResidueField] at hz
  let pt : Spec (.of K) := IsLocalRing.closedPoint K
  have : IsProper (pullback.snd P.hom t) := hgen hxg K t ⟨pt, ht pt⟩
  have : IsIntegral (pullback P.hom t) :=
    hgi.geometrically_isIntegral t (pullback.fst _ _) (pullback.snd _ _) (IsPullback.of_hasPullback _ _)
  have hpt : P.hom (e x₀) = t pt := by
    rw [ht, ← Scheme.Hom.comp_apply, he]
    rfl
  obtain ⟨a, ha, -⟩ := Scheme.Pullback.exists_preimage_pullback (e x₀) pt hpt
  obtain ⟨b, hb, -⟩ := Scheme.Pullback.exists_preimage_pullback y pt (hyx₀.trans (ht pt).symm)
  have hfib := RigidFunction.not_mem_basicOpen_fibre pullback.condition V
    (fun z => by rw [ht z]; exact hxV) (u - 1) a b (by rw [ha]; exact hxnot)
  rw [hb] at hfib
  exact hfib hy

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SpMapCompRingHomComp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

private theorem eval₂_monomial_X_mul_C_eq_C_mul_X_pow_degree {R R' σ : Type} [CommRing R] [CommRing R'] (β : R →+* R')
    (w : σ → R') (u : σ →₀ ℕ) (a : R) :
    MvPolynomial.eval₂ ((Polynomial.C : R' →+* Polynomial R').comp β) (fun i => Polynomial.X * Polynomial.C (w i))
        (MvPolynomial.monomial u a) =
      Polynomial.C (MvPolynomial.eval₂ β w (MvPolynomial.monomial u a)) * Polynomial.X ^ u.degree := by
  simp only [MvPolynomial.eval₂_monomial, RingHom.comp_apply, Finsupp.prod, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, ← Polynomial.C_pow, ← map_prod, map_mul, Finsupp.degree_apply]
  ring

theorem coeff_eval₂_scale {R R' σ : Type} [CommRing R] [CommRing R'] (β : R →+* R') (w : σ → R')
    (F : MvPolynomial σ R) (e : ℕ) :
    (MvPolynomial.eval₂Hom ((Polynomial.C : R' →+* Polynomial R').comp β)
      (fun i => Polynomial.X * Polynomial.C (w i)) F).coeff e =
      MvPolynomial.eval₂Hom β w (MvPolynomial.homogeneousComponent e F) := by
  refine MvPolynomial.induction_on' F (fun u a => ?_) (fun p q hp hq => ?_)
  · simp only [MvPolynomial.coe_eval₂Hom]
    rw [eval₂_monomial_X_mul_C_eq_C_mul_X_pow_degree, Polynomial.coeff_C_mul_X_pow,
      MvPolynomial.homogeneousComponent_of_mem ((MvPolynomial.mem_homogeneousSubmodule _ _).2
        (MvPolynomial.isHomogeneous_monomial a rfl))]
    split_ifs <;> simp
  · simp only [map_add (f := _), Polynomial.coeff_add, hp, hq]

theorem eval₂_homogeneousComponent_eq_zero {R R' σ : Type} [CommRing R] [CommRing R'] (β : R →+* R') (w : σ → R')
    (F : MvPolynomial σ R) (e : ℕ)
    (h : MvPolynomial.eval₂Hom ((LaurentPolynomial.C : R' →+* LaurentPolynomial R').comp β)
      (fun i => LaurentPolynomial.T 1 * LaurentPolynomial.C (w i)) F = 0) :
    MvPolynomial.eval₂Hom β w (MvPolynomial.homogeneousComponent e F) = 0 := by
  rw [← coeff_eval₂_scale β w F e]
  have key : Polynomial.toLaurent (MvPolynomial.eval₂Hom ((Polynomial.C : R' →+* Polynomial R').comp β)
      (fun i => Polynomial.X * Polynomial.C (w i)) F) =
      MvPolynomial.eval₂Hom ((LaurentPolynomial.C : R' →+* LaurentPolynomial R').comp β)
        (fun i => LaurentPolynomial.T 1 * LaurentPolynomial.C (w i)) F := by
    simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_comp_left]
    congr 1
    · ext r
      simp
    · funext i
      simp
  rw [h, ← map_zero Polynomial.toLaurent] at key
  rw [Polynomial.toLaurent_injective key, Polynomial.coeff_zero]

theorem spMap_comp_ringHom_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (β : A →+* B) (φ : B →+* C) :
    spMap φ ≫ spMap β = spMap (φ.comp β) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

private theorem secCoord_laurent_T_mul_C_of_secCoord {X Y : Scheme.{0}} {M : LB X} {σ : Type} {th : σ → M.Sec} {R' : Type}
    [CommRing R'] (y : Sp R' ⟶ Y) (a : Y ⟶ X) (v : σ → R') (h : SecCoord M th (y ≫ a) v) :
    SecCoord M th ((spMap (LaurentPolynomial.C : R' →+* LaurentPolynomial R') ≫ y) ≫ a)
      (fun i => LaurentPolynomial.T 1 * LaurentPolynomial.C (v i)) := by
  let u : (LaurentPolynomial R')ˣ := ⟨LaurentPolynomial.T 1, LaurentPolynomial.T (-1),
    by rw [← LaurentPolynomial.T_add]; simp, by rw [← LaurentPolynomial.T_add]; simp⟩
  rw [Category.assoc]
  exact Coord.scale (Coord.baseChange h LaurentPolynomial.C) u

theorem ideals_homogeneous : (∀ (R σ : Type) [CommRing R] (Y X : Scheme.{0}) (s : Y ⟶ Sp R) (M : LB X) (th : σ → M.Sec) (a : Y ⟶ X), M.IsLB → (∀ F ∈ idealOf s M th a, ∀ e, MvPolynomial.homogeneousComponent e F ∈ idealOf s M th a)) ∧ (∀ (R σ₁ σ₂ : Type) [CommRing R] (Y X₁ X₂ : Scheme.{0}) (s : Y ⟶ Sp R) (M₁ : LB X₁) (th₁ : σ₁ → M₁.Sec) (a₁ : Y ⟶ X₁) (M₂ : LB X₂) (th₂ : σ₂ → M₂.Sec) (a₂ : Y ⟶ X₂), M₁.IsLB → M₂.IsLB → (∀ F ∈ graphIdeal s M₁ th₁ a₁ M₂ th₂ a₂, ∀ e, MvPolynomial.homogeneousComponent e F ∈ graphIdeal s M₁ th₁ a₁ M₂ th₂ a₂)) ∧ ∀ (R σ : Type) [CommRing R] (I : Ideal (MvPolynomial σ R)) (Z : Scheme.{0}) (s : Z ⟶ Sp R) (M : LB Z) (th : σ → M.Sec), ProjRep I s M th → ProjRep (idealOf s M th (𝟙 Z)) s M th := by
  refine ⟨?_, ?_, ?_⟩
  · intro R σ _ Y X s M th a _ F hF e
    simp only [idealOf, Submodule.mem_iInf, RingHom.mem_ker] at hF ⊢
    intro R' _ β y v hyv
    have h0 := hF (LaurentPolynomial R') inferInstance (LaurentPolynomial.C.comp β)
      (spMap LaurentPolynomial.C ≫ y) (fun i => LaurentPolynomial.T 1 * LaurentPolynomial.C (v i))
      ⟨by rw [Category.assoc, hyv.1, spMap_comp_ringHom_comp], secCoord_laurent_T_mul_C_of_secCoord y a v hyv.2⟩
    exact eval₂_homogeneousComponent_eq_zero β v F e h0
  · intro R σ₁ σ₂ _ Y X₁ X₂ s M₁ th₁ a₁ M₂ th₂ a₂ _ _ F hF e
    simp only [graphIdeal, Submodule.mem_iInf, RingHom.mem_ker] at hF ⊢
    intro R' _ β y v₁ v₂ hyv
    have h0 := hF (LaurentPolynomial R') inferInstance (LaurentPolynomial.C.comp β)
      (spMap LaurentPolynomial.C ≫ y) (fun i => LaurentPolynomial.T 1 * LaurentPolynomial.C (v₁ i))
      (fun i => LaurentPolynomial.C (v₂ i))
      ⟨by rw [Category.assoc, hyv.1, spMap_comp_ringHom_comp], secCoord_laurent_T_mul_C_of_secCoord y a₁ v₁ hyv.2.1,
        by rw [Category.assoc]; exact Coord.baseChange hyv.2.2 LaurentPolynomial.C⟩
    have hfun : (fun i : σ₁ × σ₂ => LaurentPolynomial.T 1 * LaurentPolynomial.C (v₁ i.1 * v₂ i.2)) =
        fun i => LaurentPolynomial.T 1 * LaurentPolynomial.C (v₁ i.1) * LaurentPolynomial.C (v₂ i.2) := by
      funext i
      rw [map_mul, ← _root_.mul_assoc]
    exact eval₂_homogeneousComponent_eq_zero β (fun i : σ₁ × σ₂ => v₁ i.1 * v₂ i.2) F e
      ((congrArg (fun g => MvPolynomial.eval₂Hom (LaurentPolynomial.C.comp β) g F) hfun).trans h0)
  · intro R σ _ I Z s M th hI
    have hle : ∀ F ∈ I, F ∈ idealOf s M th (𝟙 Z) := by
      intro F hF
      simp only [idealOf, Submodule.mem_iInf, RingHom.mem_ker]
      intro R' _ β y v hyv
      rw [Category.comp_id] at hyv
      exact (hI.2.1 R' β y v hyv.1 hyv.2).2 F hF
    refine ⟨hI.1, ?_, ?_⟩
    · intro R' _ β x v hx hc
      refine ⟨(hI.2.1 R' β x v hx hc).1, fun F hF => ?_⟩
      simp only [idealOf, Submodule.mem_iInf, RingHom.mem_ker] at hF
      exact hF R' inferInstance β x v ⟨hx, by rwa [Category.comp_id]⟩
    · intro R' _ β v hv hz
      exact hI.2.2 R' β v hv fun F hF => hz F (hle F hF)

end GlobalTheory.ZM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FiniteImageOfLocallyConstantOnHolomorphicFamilie
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open Topology Filter

namespace GlobalTheory.FiniteClasses

open GlobalTheory.Points

theorem preconnectedSpace_pts (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A]
    [Algebra.FiniteType ℂ A] : PreconnectedSpace (Pts (spMap (algebraMap ℂ A))) := by
  have hc := isConnected_basicOpen_complexPoints_of_dense
    (exists_isConnected_principalOpen noetherNormalization_primitive
      (isConnected_unramified_cover_of_irreducible isConnected_and_dense_compl_hypersurface
        exists_mvPolynomial_of_poly_bound_off_hypersurface))
    (principalOpen_dense_complexPoints noetherNormalization_primitive
      isConnected_and_dense_compl_hypersurface) A 1 one_ne_zero
  have he := isEmbedding_ptsOverEquivAlgHom (C := ℂ) A (id_eq_spMap_algebraMap ℂ)
  refine ⟨he.isInducing.isPreconnected_image.1 ?_⟩
  convert hc.isPreconnected using 1
  ext x
  constructor
  · rintro ⟨y, -, rfl⟩
    exact ⟨_, rfl, by simp⟩
  · rintro ⟨φ, rfl, -⟩
    exact ⟨(ptsOverEquivAlgHom A (id_eq_spMap_algebraMap ℂ)).symm φ, trivial, by simp⟩

theorem finite_range_affine (A : Type) [CommRing A] [Algebra ℂ A] [Algebra.FiniteType ℂ A] {I : Type*}
    (c : Pts (spMap (algebraMap ℂ A)) → I) (hc : IsLocallyConstant c) : (Set.range c).Finite := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℂ A
  have hcomp : ∀ P : Ideal A, spMap (Ideal.Quotient.mk P) ≫ spMap (algebraMap ℂ A) =
      spMap (algebraMap ℂ (A ⧸ P)) := fun P => by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hfin : (⋃ P ∈ minimalPrimes A,
      Set.range (c ∘ PtsOver.map (spMap (Ideal.Quotient.mk P)) (hcomp P) (𝟙 _))).Finite := by
    refine (minimalPrimes.finite_of_isNoetherianRing A).biUnion fun P hP => ?_
    have : P.IsPrime := hP.1.1
    have := preconnectedSpace_pts (A ⧸ P)
    exact Set.Subsingleton.finite (by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      exact (hc.comp_continuous (PtsOver.continuous_map _ _ _)).apply_eq_of_preconnectedSpace a b)
  refine hfin.subset ?_
  rintro _ ⟨x, rfl⟩
  obtain ⟨φ, rfl⟩ := (ptsEquivAlgHom A).symm.surjective x
  have : (RingHom.ker φ.toRingHom).IsPrime := RingHom.ker_isPrime _
  obtain ⟨P, hP, hle⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal A))
    (J := RingHom.ker φ.toRingHom) bot_le
  refine Set.mem_biUnion (x := P) hP ⟨(ptsEquivAlgHom (A ⧸ P)).symm
    (Ideal.Quotient.liftₐ P φ fun a ha => hle ha), congrArg c (Subtype.ext ?_)⟩
  simp only [PtsOver.map_val, ptsOverEquivAlgHom_symm_val]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem finite_range {Y : Scheme.{0}} (p : Y ⟶ Sp ℂ) [LocallyOfFiniteType p] [QuasiCompact p] {I : Type*}
    (c : Pts p → I) (hc : IsLocallyConstant c) : (Set.range c).Finite := by
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace p
  let 𝒰 := Y.affineOpenCover
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (X := Y)
    (fun i => ((𝒰.f i).opensRange : Set Y)) (fun i => (𝒰.f i).opensRange.isOpen)
    (fun y _ => Set.mem_iUnion.2 ⟨𝒰.idx y, 𝒰.covers y⟩)
  have key : ∀ {R : CommRingCat.{0}} (j : Spec R ⟶ Y) [IsOpenImmersion j],
      (Set.range (c ∘ PtsOver.map j rfl (𝟙 _))).Finite := by
    intro R j _
    have hl : IsLocallyConstant (c ∘ PtsOver.map j rfl (𝟙 _)) :=
      hc.comp_continuous (PtsOver.continuous_map _ _ _)
    have hft : LocallyOfFiniteType (j ≫ p) := inferInstance
    generalize c ∘ PtsOver.map j rfl (𝟙 _) = c' at hl
    generalize j ≫ p = q at c' hl hft
    obtain ⟨φ, rfl⟩ := Spec.map_surjective q
    let _ := φ.hom.toAlgebra
    have : Algebra.FiniteType ℂ R := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 hft
    exact finite_range_affine R c' hl
  refine (t.finite_toSet.biUnion fun i _ => key (𝒰.f i)).subset ?_
  rintro _ ⟨x, rfl⟩
  obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ (x.1 (IsLocalRing.closedPoint ℂ))))
  have hx' : x ∈ Set.range (PtsOver.map (𝒰.f i) rfl (𝟙 _)) := by
    rw [PtsOver.range_map, range_comp_of_isOpenImmersion]
    exact (le_preimage_iff x.1 _).2 hx
  obtain ⟨z, rfl⟩ := hx'
  exact Set.mem_biUnion hi ⟨z, rfl⟩

theorem isLocallyConstant_of_hol {Y : Scheme.{0}} (p : Y ⟶ Sp ℂ) (d : ℕ)
    (hp : SmoothOfRelativeDimension d p) {I : Type*} (c : Pts p → I)
    (H : ∀ (B : Set (Fin d → ℂ)) (y : (Fin d → ℂ) → Pts p), IsOpen B → IsHolTo B (fun b => (y b).1) →
      ∀ b₀ ∈ B, ∀ᶠ b in 𝓝 b₀, c (y b) = c (y b₀)) : IsLocallyConstant c := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  let h := overHomeomorph (C := ℂ) (Over.mk p)
  obtain ⟨W, σ, U, t, hW, h0, hσ, -, hhol, hco, hop, -⟩ := HolChart.exists_holomorphic_chart valAt'_rules
    existsUnique_point_of_ringHom exists_holomorphic_section_of_etale (Over.mk p) d hp (h.symm x)
  have hop' : IsOpen (σ '' W) := by
    refine TopologicalSpace.le_def.1 (le_generateFrom ?_) _ hop
    rintro _ ⟨V, f, O, hO, rfl⟩
    exact (isOpen_basicSet (C := ℂ) V f hO).preimage (isEmbedding_left (Over.mk p)).continuous
  have hx : h (σ 0) = x := by rw [hσ, Homeomorph.apply_symm_apply]
  have hev := H W (fun b => h (σ b)) hW hhol 0 h0
  have hxU : ⊤ ≤ x.1 ⁻¹ᵁ U := by rw [← hx]; exact (hco 0 h0).1
  have hT : Tendsto (fun (z : Pts p) (i : Fin d) => valR z.1 U (t i)) (𝓝 x) (𝓝 0) := by
    refine tendsto_pi_nhds.2 fun i => ?_
    have h1 := ((continuousAt_valR (t i) hxU).comp continuous_subtype_val.continuousAt).tendsto
    have h2 : valR x.1 U (t i) = (0 : Fin d → ℂ) i := by rw [← hx]; exact (hco 0 h0).2 i
    rw [← h2]
    exact h1
  have hN : h '' (σ '' W) ∈ 𝓝 x := (h.isOpenMap _ hop').mem_nhds ⟨_, ⟨0, h0, rfl⟩, hx⟩
  filter_upwards [hN, hT.eventually hev] with z hz hz'
  obtain ⟨_, ⟨w, hw, rfl⟩, rfl⟩ := hz
  have : (fun i => valR (h (σ w)).1 U (t i)) = w := funext (hco w hw).2
  rw [this, hx] at hz'
  exact hz'

theorem finite_image_of_locally_constant_on_holomorphic_families :
    (∀ (k : Type) [Field k] (σ : k →+* ℂ) (X : Scheme.{0}) (s : X ⟶ Sp k) (d : ℕ) (y₀ : Sp ℂ ⟶ X), SmoothOfRelativeDimension d s → y₀ ≫ s = spMap σ → ∃ (B : Set (Fin d → ℂ)) (y : (Fin d → ℂ) → (Sp ℂ ⟶ X)) (U : X.Opens) (f : Fin d → Γ(X, U)) (n : ℕ) (r : Fin n → Γ(X, U)), IsOpen B ∧ (0 : Fin d → ℂ) ∈ B ∧ y 0 = y₀ ∧ (∀ b ∈ B, y b ≫ s = spMap σ) ∧ IsHolTo B y ∧ Set.InjOn y B ∧ ⊤ ≤ y₀ ⁻¹ᵁ U ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ x : Sp ℂ ⟶ X, x ≫ s = spMap σ → ⊤ ≤ x ⁻¹ᵁ U → (∀ i, ‖valAt' x U (r i) - valAt' y₀ U (r i)‖ < ε) → x ∈ y '' B) → ∀ (k : Type) [Field k] (σ : k →+* ℂ) (X : Scheme.{0}) (s : X ⟶ Sp k) (d : ℕ) (I : Type 1) (cls : (Sp ℂ ⟶ X) → I), SmoothOfRelativeDimension d s → QuasiCompact s → (∀ (B : Set (Fin d → ℂ)) (y : (Fin d → ℂ) → (Sp ℂ ⟶ X)), IsOpen B → (∀ b ∈ B, y b ≫ s = spMap σ) → IsHolTo B y → ∀ b₀ ∈ B, ∀ᶠ b in nhds b₀, cls (y b) = cls (y b₀)) → (cls '' {x | x ≫ s = spMap σ}).Finite := by
  intro _ k _ σ X s d I cls hs hq H
  let p := pullback.snd s (spMap σ)
  let q := pullback.fst s (spMap σ)
  have hp : SmoothOfRelativeDimension d p :=
    (smoothOfRelativeDimension_isStableUnderBaseChange d).of_isPullback
      (IsPullback.of_hasPullback s (spMap σ)) hs
  have : Smooth p := SmoothOfRelativeDimension.smooth d p
  have hover : ∀ z : Pts p, (z.1 ≫ q) ≫ s = spMap σ := fun z => by
    rw [Category.assoc, pullback.condition, ← Category.assoc, z.2, Category.id_comp]
  have hl : IsLocallyConstant fun z : Pts p => cls (z.1 ≫ q) := by
    refine isLocallyConstant_of_hol p d hp _ fun B y hB hy => ?_
    refine H B (fun b => (y b).1 ≫ q) hB (fun b _ => hover _) fun U f => ?_
    simp only [valAt'_eq_valR, valR_comp]
    exact hy (q ⁻¹ᵁ U) ((q.app U).hom f)
  refine (finite_range p _ hl).subset ?_
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨⟨pullback.lift x (𝟙 _) (by rw [Category.id_comp]; exact hx), pullback.lift_snd _ _ _⟩, ?_⟩
  exact congrArg cls (pullback.lift_fst _ _ _)

end GlobalTheory.FiniteClasses
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionAndGeometricallyConnect
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.VeryDenseFibres

theorem smooth_fiber_of_smooth_fiber {X T S : Scheme.{0}} (f : X ⟶ S) (t : T ⟶ S) (y : T)
    (h : Smooth ((pullback.snd f t).fiberToSpecResidueField y)) :
    Smooth (f.fiberToSpecResidueField (t y)) := by
  have hp := isPullback_fiberToSpecResidueField_of_isPullback (IsPullback.of_hasPullback f t) y
  refine MorphismProperty.of_isPullback_of_descendsAlong
    (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hp.flip ⟨⟨?_, ?_⟩, ?_⟩ h
  · exact ⟨fun y => ⟨default, Subsingleton.elim _ _⟩⟩
  · infer_instance
  · infer_instance

theorem mem_smoothLocus_of_smooth_fiber {R : CommRingCat.{0}} {X : Scheme.{0}} (f : X ⟶ Spec R)
    [LocallyOfFinitePresentation f] [Flat f] (x : X)
    (h : Smooth (f.fiberToSpecResidueField (f x))) : x ∈ f.smoothLocus := by
  wlog hX : ∃ S, X = Spec S generalizing f X
  · obtain ⟨i, y, rfl⟩ := X.affineCover.exists_eq x
    have _ : Smooth (pullback.snd f ((Spec R).fromSpecResidueField
        ((X.affineCover.f i ≫ f) y))) := h
    have H := this (X.affineCover.f i ≫ f) y (by
      rw [Scheme.Hom.fiberToSpecResidueField, ← pullbackRightPullbackFstIso_inv_snd_snd]
      infer_instance) ⟨_, rfl⟩
    rwa [← Scheme.Hom.preimage_smoothLocus_eq] at H
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  letI := φ.hom.toAlgebra
  haveI : Algebra.FinitePresentation R S :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation) (φ := φ)).mp ‹_›
  haveI : Module.Flat R S :=
    (HasRingHomProperty.Spec_iff (P := @Flat) (φ := φ)).mp ‹_›
  haveI : x.asIdeal.IsPrime := PrimeSpectrum.isPrime x
  let p : PrimeSpectrum R := Spec.map φ x
  haveI : x.asIdeal.LiesOver p.asIdeal := ⟨rfl⟩
  haveI : Algebra.FormallySmooth p.asIdeal.ResidueField (p.asIdeal.Fiber S) := by
    rw [← RingHom.formallySmooth_algebraMap]
    refine RingHom.Smooth.formallySmooth ?_
    rw [← CommRingCat.hom_ofHom (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber ↑S)),
      ← HasRingHomProperty.Spec_iff (P := @Smooth),
      ← MorphismProperty.arrow_mk_iso_iff (P := @Smooth) (Spec.fiberToSpecResidueFieldIso R S p)]
    exact h
  haveI := Algebra.IsSmoothAt.of_formallySmooth_fiber (R := R) p.asIdeal x.asIdeal
  obtain ⟨g, hg, hsm⟩ := Algebra.IsSmoothAt.exists_notMem_smooth R x.asIdeal
  let j : Spec (CommRingCat.of (Localization.Away g)) ⟶ Spec S :=
    Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))
  haveI : IsOpenImmersion j := IsOpenImmersion.of_isLocalization g
  haveI : Smooth (j ≫ Spec.map φ) := by
    rw [← Spec.map_comp, HasRingHomProperty.Spec_iff (P := @Smooth)]
    exact RingHom.smooth_algebraMap.mpr hsm
  obtain ⟨y, rfl⟩ : x ∈ Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away g))) := by
    rw [PrimeSpectrum.localization_away_comap_range _ g]
    exact hg
  have := (j ≫ Spec.map φ).smoothLocus_eq_top.ge (Set.mem_univ y)
  rwa [← Scheme.Hom.preimage_smoothLocus_eq] at this

theorem exists_opens_smoothOfRelativeDimension {X T S : Scheme.{0}} (f : X ⟶ S) [Smooth f]
    (t : T ⟶ S) (g : ℕ) (h : SmoothOfRelativeDimension g (pullback.snd f t)) (x : X) (y : T)
    (hxy : f x = t y) : ∃ W : X.Opens, x ∈ W ∧ SmoothOfRelativeDimension g (W.ι ≫ f) := by
  obtain ⟨n, W, hW, hd⟩ := ReciprocityTheory.ChartRestriction.G.H1.exists_dim f x
  have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} n
  have h1 : SmoothOfRelativeDimension n (pullback.snd (W.ι ≫ f) t) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension n) _ _ hd
  have h2 : SmoothOfRelativeDimension (0 + (0 + g)) (pullback.snd (W.ι ≫ f) t) := by
    rw [← pullbackRightPullbackFstIso_inv_snd_snd]
    infer_instance
  obtain ⟨z, -⟩ := Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback (W.ι ≫ f) t)
    ⟨x, hW⟩ y hxy
  have e : n = g := by simpa using ReciprocityTheory.ChartRestriction.G.H1.dim_unique _ h1 h2 z
  exact ⟨W, hW, e ▸ hd⟩

theorem eq_top_of_forall_mem {R : Type} [CommRing R] {Z : Scheme.{0}} (s : Z ⟶ Sp R)
    [UniversallyClosed s] (P : Set (Ideal R))
    (hP : ∀ q : Ideal R, q.IsPrime → ∃ p ∈ P, p.IsPrime ∧ q ≤ p) (U : Z.Opens)
    (hU : ∀ z : Z, (s z).asIdeal ∈ P → z ∈ U) : U = ⊤ := by
  rw [← top_le_iff]
  intro x _
  by_contra hx
  have hc : IsClosed (s '' (U : Set Z)ᶜ) := s.isClosedMap _ U.2.isClosed_compl
  obtain ⟨p, hp, hp', hle⟩ := hP (s x).asIdeal (PrimeSpectrum.isPrime _)
  have hs : s x ⤳ (⟨p, hp'⟩ : PrimeSpectrum R) := (PrimeSpectrum.le_iff_specializes _ _).1 hle
  obtain ⟨y, hy, hy'⟩ := hs.mem_closed hc ⟨x, hx, rfl⟩
  exact hy (hU y (by rw [hy']; exact hp))

theorem spMap_apply_asIdeal {R K : Type} [CommRing R] [Field K] (x : R →+* K) (y : Sp K) :
    (spMap x y).asIdeal = RingHom.ker x := by
  have : y.asIdeal = ⊥ := by
    have := PrimeSpectrum.isPrime y
    exact Ideal.eq_bot_of_prime _
  change Ideal.comap x y.asIdeal = _
  rw [this]
  rfl

end GlobalTheory.VeryDenseFibres
end
