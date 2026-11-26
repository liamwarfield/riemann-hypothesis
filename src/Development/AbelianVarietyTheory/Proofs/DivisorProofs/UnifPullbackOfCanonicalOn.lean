module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalMumfordFamilyPullbackLocalUniformised

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullDataRefines
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem pullData_refines : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (θ : R →+* V) (Q : Data R) (Q' : Data V) (e : Q'.X ≃+ Q.X) (D : DegPre V) (hB : D.TauBimult) (e' : D.X ≃+ Q'.X), PullData Q θ Q' e → Refines Q' (RingHom.id V) D e' → PullData Q θ (GlobalTheory.PolDeg.Wit.ofDeg D hB) (e'.trans e) := by
  intro R V _ _ _ _ θ Q Q' e D hB e' hP hR
  obtain ⟨β, β₂, w, hpb, hsq, hw, hc, ht⟩ := hP
  obtain ⟨β', β'₂, w', hpb', hsq', hw', hc', ht'⟩ := hR
  have hs : spMap (RingHom.id V) = 𝟙 (Sp V) := Spec.map_id _
  letI := D.P.isAb.comm
  obtain ⟨w'', hw'', hv⟩ := GlobalTheory.T.mumfordBundleIso_comp_values_mul _ _ _ D.P.A Q'.B Q.B D.P.L Q'.M.L Q.M.L
    D.P.isLB Q'.M.isLB Q.M.isLB β'₂ β₂ _ rfl w hw w' hw'
  refine ⟨β' ≫ β, β'₂ ≫ β₂, w'', ?_, ?_, hw'', fun a => ?_, fun a b => ?_⟩
  · exact (hpb'.comp hpb).congr (by rw [hs, Category.id_comp]) rfl
  · refine ⟨?_, ?_⟩
    · erw [Category.assoc, hsq.1, ← Category.assoc, hsq'.1, Category.assoc]
    · erw [Category.assoc, hsq.2, ← Category.assoc, hsq'.2, Category.assoc]
  · have h₁ : (D.c a).left ≫ β' = (Q'.c (e' a)).left := (hc' a).trans (by rw [hs, Category.id_comp])
    show (D.c a).left ≫ β' ≫ β = _
    rw [← Category.assoc, h₁]
    exact hc (e' a)
  · obtain ⟨u, x, y, k, k', hu, hy, hk, hk', h1, h2⟩ := ht (e' a) (e' b)
    refine ⟨u, x, y, k, k', hu, hy, hk, hk', h1, fun z J J' hJ hJ' => ?_⟩
    obtain ⟨I, hI⟩ := GlobalTheory.DegPull.exists_good' Q'.M.isLB z
    have hκ : 𝟙 (TK V).left ≫ jK V = jK V ≫ spMap (RingHom.id V) := by rw [hs, Category.id_comp, Category.comp_id]
    have hca : ∀ a, (D.c a).left ≫ β' = (Q'.c (e' a)).left := fun a => (hc' a).trans (by rw [hs, Category.id_comp])
    have t1 := ht' (𝟙 _) hκ a b z I J' hI hJ'
    have hp : (lift (toUnit (TK V) ≫ D.c a) (toUnit (TK V) ≫ D.c b)).left ≫ β'₂ =
        (lift (toUnit (TK V) ≫ Q'.c (e' a)) (toUnit (TK V) ≫ Q'.c (e' b))).left := by
      apply pullback.hom_ext
      · show _ ≫ (fst Q'.B Q'.B).left = _ ≫ (fst Q'.B Q'.B).left
        rw [Category.assoc, hsq'.1, ← Category.assoc, ← Over.comp_left, lift_fst, ← Over.comp_left, lift_fst,
          Over.comp_left, Over.comp_left, Category.assoc]
        exact congrArg (_ ≫ ·) (hca _)
      · show _ ≫ (snd Q'.B Q'.B).left = _ ≫ (snd Q'.B Q'.B).left
        rw [Category.assoc, hsq'.2, ← Category.assoc, ← Over.comp_left, lift_snd, ← Over.comp_left, lift_snd,
          Over.comp_left, Over.comp_left, Category.assoc]
        exact congrArg (_ ≫ ·) (hca _)
    have t2 := h2 z J I hJ hI
    have t3 := hv _ (lift (toUnit (TK V) ≫ D.c a) (toUnit (TK V) ≫ D.c b)).left z J' I J hJ' hI hJ
    rw [hp] at t3
    have t0 := (Wit.exists_tau D a b).choose_spec.2 _ (𝟙 _) z J' hJ'
    show val (Wit.exists_tau D a b).choose (𝟙 _) z J' = _
    rw [t0, t1, t2]
    erw [t3]
    exact (mul_left_comm _ _ _).trans (congrArg _ (_root_.mul_assoc _ _ _).symm)

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalBaseDataPullbackAlongMap
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCancelGrpPullbackWithSquares
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCancelGrpPullbackWithSquares
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.GrpCancel

theorem exists_cancel_square : ∀ (SA SB SC : Scheme.{0}) (A : Over SA) [GrpObj A] (B : Over SB) [GrpObj B] (C : Over SC) [GrpObj C] (g : SA ⟶ SB) (f : SB ⟶ SC) (a : A.left ⟶ C.left) (b : B.left ⟶ C.left) (a₂ : (G2 A).left ⟶ (G2 C).left) (b₂ : (G2 B).left ⟶ (G2 C).left), IsGrpPullback A C (g ≫ f) a → IsGrpPullback B C f b → IsSquare a a₂ → IsSquare b b₂ → ∃ (β : A.left ⟶ B.left) (β₂ : (G2 A).left ⟶ (G2 B).left), IsGrpPullback A B g β ∧ IsSquare β β₂ ∧ β ≫ b = a ∧ β₂ ≫ b₂ = a₂ := by
  intro SA SB SC A _ B _ C _ g f a b a₂ b₂ ha hb sa sb
  let β : A.left ⟶ B.left := hb.1.lift a (A.hom ≫ g) (by rw [Category.assoc]; exact ha.1.w)
  have e : β ≫ b = a := hb.1.lift_fst _ _ _
  have w : β ≫ B.hom = A.hom ≫ g := hb.1.lift_snd _ _ _
  have hβ : IsGrpPullback A B g β := IsGrpPullback.cancel hb (e.symm ▸ ha) w
  let β₂ : (G2 A).left ⟶ (G2 B).left := (lift (pushPt w (fst A A)) (pushPt w (snd A A))).left
  have s : IsSquare β β₂ :=
    ⟨congrArg (fun z => z.left) (lift_fst (pushPt w (fst A A)) (pushPt w (snd A A))),
      congrArg (fun z => z.left) (lift_snd (pushPt w (fst A A)) (pushPt w (snd A A)))⟩
  refine ⟨β, β₂, hβ, s, e, ?_⟩
  have h₁ : (β₂ ≫ b₂) ≫ (fst C C).left = a₂ ≫ (fst C C).left := by
    rw [Category.assoc, sb.1, ← Category.assoc, s.1, Category.assoc, e, sa.1]
  have h₂ : (β₂ ≫ b₂) ≫ (snd C C).left = a₂ ≫ (snd C C).left := by
    rw [Category.assoc, sb.2, ← Category.assoc, s.2, Category.assoc, e, sa.2]
  exact pullback.hom_ext h₁ h₂

end GlobalTheory.GrpCancel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCancelGrpPullbackWithSquaresStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cancel_grpPullback_with_squares : ∀ (SA SB SC : Scheme.{0}) (A : Over SA) [GrpObj A] (B : Over SB) [GrpObj B] (C : Over SC) [GrpObj C] (g : SA ⟶ SB) (f : SB ⟶ SC) (a : A.left ⟶ C.left) (b : B.left ⟶ C.left) (a₂ : (G2 A).left ⟶ (G2 C).left) (b₂ : (G2 B).left ⟶ (G2 C).left), IsGrpPullback A C (g ≫ f) a → IsGrpPullback B C f b → IsSquare a a₂ → IsSquare b b₂ → ∃ (β : A.left ⟶ B.left) (β₂ : (G2 A).left ⟶ (G2 B).left), IsGrpPullback A B g β ∧ IsSquare β β₂ ∧ β ≫ b = a ∧ β₂ ≫ b₂ = a₂ := by
  first | exact @GlobalTheory.GrpCancel.exists_cancel_square | exact GlobalTheory.GrpCancel.exists_cancel_square | (intros; apply GlobalTheory.GrpCancel.exists_cancel_square <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdZpowMul
namespace GlobalTheory.LaurentFrac

theorem prod_zpow_mul {K : Type} [Field K] {I : Type} [Fintype I] (a : I → K) (N : I → ℤ)
    (ha : ∀ i, a i ≠ 0) :
    (∏ i, a i ^ N i) * ∏ i, a i ^ (-N i).toNat = ∏ i, a i ^ (N i).toNat := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (ha i)]
  congr 1
  omega

theorem exists_frac (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V]
    (θ : R →+* V) {I : Type} [Fintype I] (s : I → R) (N : I → ℤ) (hs : ∀ i, θ (s i) ≠ 0) :
    ∃ x y : R, θ y ≠ 0 ∧
      (∏ i, algebraMap R (FractionRing R) (s i) ^ N i) * algebraMap R _ y = algebraMap R _ x ∧
      (∏ i, algebraMap V (FractionRing V) (θ (s i)) ^ N i) * algebraMap V _ (θ y)
        = algebraMap V _ (θ x) := by
  refine ⟨∏ i, s i ^ (N i).toNat, ∏ i, s i ^ (-N i).toNat, ?_, ?_, ?_⟩
  · rw [map_prod]
    refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
    rw [map_pow]
    exact pow_ne_zero _ (hs i)
  · simp only [map_prod, map_pow]
    refine prod_zpow_mul _ N fun i => ?_
    have h : s i ≠ 0 := fun h => hs i (by rw [h, map_zero])
    exact (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 h
  · simp only [map_prod, map_pow]
    refine prod_zpow_mul _ N fun i => ?_
    exact (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 (hs i)

end GlobalTheory.LaurentFrac
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalBaseDataPullbackAlongMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum
noncomputable section

namespace GlobalTheory.PullFrom

theorem spMap_comp_ring {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap]

theorem good_exists {X Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (z : Z) : ∃ J, Good L z J := by
  obtain ⟨J, hJ, -⟩ := exists_good L hL z (K := Empty) Empty.elim Empty.elim (fun a => a.elim) (fun k => k.elim)
  exact ⟨J, hJ⟩

private theorem sq_ext_lemma {S Z : Scheme.{0}} {G : Over S} {f g : Z ⟶ (G2 G).left}
    (h₁ : f ≫ (fst G G).left = g ≫ (fst G G).left) (h₂ : f ≫ (snd G G).left = g ≫ (snd G G).left) : f = g :=
  Over.tensorObj_ext _ _ h₁ h₂

theorem pullData_of_dataFrom : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (θ : R →+* V) (iw : W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (Q : Data R) (e : Q.X ≃+ (Fin T.r → ℤ)) (Q' : Data V) (e' : Q'.X ≃+ (Fin T.r → ℤ)), (∀ i, θ (s i) ≠ 0) → DataFrom T iw s ε n Q e → DataFrom T (θ.comp iw) (fun i => θ (s i)) ε n Q' e' → PullData Q θ Q' (e'.trans e.symm) := by
  intro o W _ _ _ T R V _ _ _ _ θ iw I _ s ε n Q e Q' e' hs hQ hQ'
  obtain ⟨β₀, β₀₂, w₀, hpb₀, hsq₀, hw₀, hc₀, hτ₀⟩ := hQ
  obtain ⟨β₁, β₁₂, w₁, hpb₁, hsq₁, hw₁, hc₁, hτ₁⟩ := hQ'
  have hcomp : spMap θ ≫ spMap iw = spMap (θ.comp iw) := (spMap_comp_ring iw θ).symm

  obtain ⟨β, β₂, hpb, hsq, hβ, hβ₂⟩ := GlobalTheory.T.exists_cancel_grpPullback_with_squares (Sp V) (Sp R) (Sp W) Q'.B Q.B T.B (spMap θ) (spMap iw)
    β₁ β₀ β₁₂ β₀₂ (hcomp ▸ hpb₁) hpb₀ hsq₁ hsq₀

  obtain ⟨w, hw, hrel⟩ := GlobalTheory.T.mumfordBundleIso_cancel_values_mul (Sp V) (Sp R) (Sp W) Q'.B Q.B T.B Q'.M.L Q.M.L T.M.L Q'.M.isLB Q.M.isLB
    T.M.isLB β₂ β₀₂ β₁₂ hβ₂ w₀ hw₀ w₁ hw₁

  have hcc : ∀ a, (Q'.c a).left ≫ β = spMap θ ≫ (Q.c ((e'.trans e.symm) a)).left := by
    intro a
    apply hpb₀.1.hom_ext
    · simp only [Category.assoc, hβ, hc₁, hc₀, AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
      rw [← hcomp, Category.assoc]
    · simp only [Category.assoc, hpb.1.w]
      simp

  have hsqT : ∀ a b : Q.X, (lift (Q.c a) (Q.c b)).left ≫ β₀₂ =
      spMap iw ≫ (lift (T.c₀ ((n : ℤ) • e a)) (T.c₀ ((n : ℤ) • e b))).left := by
    intro a b
    apply sq_ext_lemma
    · rw [Category.assoc, hsq₀.1, ← Category.assoc, ← Over.comp_left, lift_fst, hc₀, Category.assoc,
        ← Over.comp_left, lift_fst]
    · rw [Category.assoc, hsq₀.2, ← Category.assoc, ← Over.comp_left, lift_snd, hc₀, Category.assoc,
        ← Over.comp_left, lift_snd]
  refine ⟨β, β₂, w, hpb, hsq, hw, hcc, ?_⟩
  intro a b
  set a₀ := (e'.trans e.symm) a with ha₀def
  set b₀ := (e'.trans e.symm) b with hb₀def
  have ha₀ : e a₀ = e' a := by simp [a₀]
  have hb₀ : e b₀ = e' b := by simp [b₀]

  have hsqQ : (lift (toUnit (TK V) ≫ Q'.c a) (toUnit (TK V) ≫ Q'.c b)).left ≫ β₂ =
      ((TK V).hom ≫ spMap θ) ≫ (lift (Q.c a₀) (Q.c b₀)).left := by
    have h₁ : (lift (Q.c a₀) (Q.c b₀)).left ≫ (fst Q.B Q.B).left = (Q.c a₀).left := by
      rw [← Over.comp_left, lift_fst]
    have h₂ : (lift (Q.c a₀) (Q.c b₀)).left ≫ (snd Q.B Q.B).left = (Q.c b₀).left := by
      rw [← Over.comp_left, lift_snd]
    apply sq_ext_lemma
    · rw [Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, lift_fst, Over.comp_left, Category.assoc,
        hcc, Category.assoc, Category.assoc, h₁]
      rfl
    · rw [Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, lift_snd, Over.comp_left, Category.assoc,
        hcc, Category.assoc, Category.assoc, h₂]
      rfl
  obtain ⟨k₀, hk₀, hv₀⟩ := hτ₀ a₀ b₀
  obtain ⟨k₁, hk₁, hv₁⟩ := hτ₁ a b
  obtain ⟨x, y, hy, hxy, hxy'⟩ :=
    GlobalTheory.LaurentFrac.exists_frac R V θ s (fun i => (n : ℤ) * ε i (e' a) (e' b)) hs

  obtain ⟨u, hu, hvu⟩ := GlobalTheory.T.exists_generator_transport_mumfordBundleIso (Sp R) (Sp W) Q.B T.B Q.M.L T.M.L Q.M.isLB T.M.isLB β₀₂ w₀ hw₀
    (𝟙_ (Over (Sp R))) (𝟙_ (Over (Sp W))) (Q.c a₀) (Q.c b₀) (T.c₀ ((n : ℤ) • e a₀))
    (T.c₀ ((n : ℤ) • e b₀)) (spMap iw) (hsqT a₀ b₀) (T.τ₀ _ _) (T.τ₀_gen _ _)
  refine ⟨u, x, y, k₀, k₁, hu, hy, ?_, ?_, ?_, ?_⟩
  · rw [hk₀, ha₀, hb₀]
    exact hxy
  · rw [hk₁]
    exact hxy'
  · intro z J hJ
    obtain ⟨J₀, hJ₀⟩ := good_exists T.M.isLB z
    have hl : (toUnit (TK R)).left ≫ (lift (Q.c a₀) (Q.c b₀)).left =
        (lift (toUnit (TK R) ≫ Q.c a₀) (toUnit (TK R) ≫ Q.c b₀)).left := by
      rw [← Over.comp_left, comp_lift]
    rw [hv₀ z J₀ J hJ₀ hJ, hvu _ _ z J₀ J hJ₀ hJ, hl]
    rfl
  · intro z J J' hJ hJ'
    obtain ⟨J₀, hJ₀⟩ := good_exists T.M.isLB z
    rw [ha₀, hb₀] at hvu
    rw [hv₁ z J₀ J' hJ₀ hJ', hrel _ _ z J' J J₀ hJ' hJ hJ₀, hvu _ ((TK V).hom ≫ spMap θ) z J₀ J hJ₀ hJ, hsqQ,
      Category.assoc ((TK V).hom) (spMap θ) (spMap iw), hcomp, _root_.mul_assoc]

end GlobalTheory.PullFrom

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalBaseDataPullbackAlongMapStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tautological_base_data_pullback_along_map : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (θ : R →+* V) (iw : W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (Q : Data R) (e : Q.X ≃+ (Fin T.r → ℤ)) (Q' : Data V) (e' : Q'.X ≃+ (Fin T.r → ℤ)), (∀ i, θ (s i) ≠ 0) → DataFrom T iw s ε n Q e → DataFrom T (θ.comp iw) (fun i => θ (s i)) ε n Q' e' → PullData Q θ Q' (e'.trans e.symm) := by
  first | exact @GlobalTheory.PullFrom.pullData_of_dataFrom | exact GlobalTheory.PullFrom.pullData_of_dataFrom | (intros; apply GlobalTheory.PullFrom.pullData_of_dataFrom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnifPullbackOfCanonicalOn
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.TChart.Taut

theorem unif_pull_of_canonOn : ∀ {g n : ℕ} {φ : InvFun ℤ} (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (P : LB (G2 G₁).left), IsMumPol C.Q G₁ P → GlobalTheory.Mum.CanonOn C.Q (PrimeSpectrum.basicOpen (∏ k, C.t k)) G₁ P → ∀ (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (θ : C.R →+* V'), IsCN V' → IsLocalHom θ → (∀ k, θ (C.s k) ≠ 0) → ∀ (D' : DegData V' (maximalIdeal V')) (e : D'.toPre.X ≃+ (Fin C.T.r → ℤ)), DegFrom C.T (θ.comp C.iw) (fun k => θ (C.s k)) C.form n D'.toPre e → ∃ (G' : Over (Sp V')) (_ : GrpObj G') (_ : IsCommMonObj G') (π : G'.left ⟶ G₁.left) (π₂ : (G2 G').left ⟶ (G2 G₁).left) (A : PolAV (Sp (FractionRing V'))) (U : Unif (maximalIdeal V') D' A G'), IsGrpPullback G' G₁ (spMap θ) π ∧ IsSquare π π₂ ∧ LBIso (abelian₂ G' U.LG.L) (P.pull π₂) := by
  intro g n φ C G₁ _ _ P hM hC V' _ _ _ θ hV hθ hs D' e hD
  obtain ⟨Q', e', hr, hd⟩ := hD
  have h₁ := GlobalTheory.T.tautological_base_data_pullback_along_map C.T C.R V' θ C.iw C.s C.form n C.Q C.e Q' _ hs C.data hd
  have h₂ := GlobalTheory.Mum.pullData_refines C.R V' θ C.Q Q' _ D'.toPre D'.tau_bimult e' h₁ hr
  refine GlobalTheory.T.canonical_mumford_family_pullback_local_uniformised C.R V' θ hM.1 hV hθ C.Q _ G₁ P hM.2.2.1 hC ?_ D' _ h₂
  rw [genericPoint_eq_bot_of_affine]
  show (∏ k, C.t k) ∉ Ideal.comap θ (⊥ : PrimeSpectrum V').asIdeal
  rw [Ideal.mem_comap, map_prod]
  exact Finset.prod_ne_zero_iff.2 fun k _ => hs (.inl k)

end GlobalTheory.TChart.Taut
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnifPullbackOfCanonicalOnStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unif_pullback_of_canonical_on : ∀ {g n : ℕ} {φ : InvFun ℤ} (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (P : LB (G2 G₁).left), IsMumPol C.Q G₁ P → GlobalTheory.Mum.CanonOn C.Q (PrimeSpectrum.basicOpen (∏ k, C.t k)) G₁ P → ∀ (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (θ : C.R →+* V'), IsCN V' → IsLocalHom θ → (∀ k, θ (C.s k) ≠ 0) → ∀ (D' : DegData V' (maximalIdeal V')) (e : D'.toPre.X ≃+ (Fin C.T.r → ℤ)), DegFrom C.T (θ.comp C.iw) (fun k => θ (C.s k)) C.form n D'.toPre e → ∃ (G' : Over (Sp V')) (_ : GrpObj G') (_ : IsCommMonObj G') (π : G'.left ⟶ G₁.left) (π₂ : (G2 G').left ⟶ (G2 G₁).left) (A : PolAV (Sp (FractionRing V'))) (U : Unif (maximalIdeal V') D' A G'), IsGrpPullback G' G₁ (spMap θ) π ∧ IsSquare π π₂ ∧ LBIso (abelian₂ G' U.LG.L) (P.pull π₂) := by
  first | exact @GlobalTheory.TChart.Taut.unif_pull_of_canonOn | exact GlobalTheory.TChart.Taut.unif_pull_of_canonOn | (intros; apply GlobalTheory.TChart.Taut.unif_pull_of_canonOn <;> assumption)
end
