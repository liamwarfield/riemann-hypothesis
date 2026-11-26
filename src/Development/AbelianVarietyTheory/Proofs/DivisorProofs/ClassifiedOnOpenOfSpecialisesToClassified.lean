module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTripleMapOfSameUniformisedCoords
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTautologicalBaseNsmulDegenerationData
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryModuliObjectSpreadNormalDomain
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodPartMemTautologicalPointTorsion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelPointLiftZeroFirstCoordinate

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreTorsionRationalOfBase
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QkPointGaloisFixedUpToEquivDividedData
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQkPointExtensionOfDividedData
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQkPointExtensionOfDividedData
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DivTorsRat

open GlobalTheory.TorusExt

attribute [local instance] gtGroup

theorem exists_char_descend {X K F : Type} [Group X] [Field K] [Field F] (f : K →+* F) {k : ℕ} (hk : k ≠ 0) {ζ : K}
    (hζ : IsPrimitiveRoot ζ k) (t : X →* Fˣ) (ht : t ^ k = 1) :
    ∃ t₀ : X →* Kˣ, (Units.map f.toMonoidHom).comp t₀ = t := by
  have hinj : Function.Injective (Units.map f.toMonoidHom) := Units.map_injective f.injective
  have : NeZero k := ⟨hk⟩
  have hr : ∀ x, t x ∈ (Units.map f.toMonoidHom).range := fun x => by
    have h1 : ((t x : Fˣ) : F) ^ k = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← MonoidHom.pow_apply, ht]; rfl
    obtain ⟨i, -, hi⟩ := (hζ.map_of_injective f.injective).eq_pow_of_pow_eq_one h1
    exact ⟨(hζ.isUnit hk).unit ^ i, Units.ext (by simpa using hi)⟩
  refine ⟨(MonoidHom.ofInjective hinj).symm.toMonoidHom.comp (t.codRestrict _ hr), MonoidHom.ext fun x => ?_⟩
  exact MonoidHom.apply_ofInjective_symm hinj _

theorem exists_qkExt_of_b {V : Type} [CommRing V] [IsDomain V] {Q : DegPre V} (hB : Q.TauBimult) {K F : Type} [Field K]
    [Field F] [Algebra (FractionRing V) K] [Algebra (FractionRing V) F] (f : K →+* F)
    (hf : f.comp (algebraMap (FractionRing V) K) = algebraMap (FractionRing V) F) {k : ℕ} (hk : k ≠ 0) {ζ : K}
    (hζ : IsPrimitiveRoot ζ k) (p : QkPt Q F k) (hp : p.y = 0) (q : QkPt Q K k) (hq : q.y = 0)
    (hb : p.g.b.left = spMap f ≫ q.g.b.left) : ∃ p₀ : QkPt Q K k, QkExt f p₀ p := by
  have hb' : p.g.b = (gtExt Q f hf q.g).b := (Over.OverMorphism.ext hb).trans (gtExt_b f hf _).symm
  have np : k • p.g = 0 := by rw [qk_nsmul hB, hp, map_zero]
  have nq : k • q.g = 0 := by rw [qk_nsmul hB, hq, map_zero]
  obtain ⟨t, ht⟩ := exists_torusPt_eq (g := p.g + -(gtExt Q f hf q.g)) (by rw [add_b, neg_b, hb', mul_inv_cancel])
  have tk : t ^ k = 1 := by
    have : torusPt Q F (Additive.ofMul (t ^ k)) = torusPt Q F (Additive.ofMul 1) := by
      rw [ofMul_pow, map_nsmul, ← ht, nsmul_add, smul_neg, ← map_nsmul, np, nq, ofMul_one, map_zero, map_zero, neg_zero,
        add_zero]
    exact torusPt_injective this
  obtain ⟨t₀, rfl⟩ := exists_char_descend f hk hζ t tk
  have t0 : t₀ ^ k = 1 := MonoidHom.ext fun x => Units.map_injective (f := f.toMonoidHom) f.injective (by
    have := DFunLike.congr_fun tk x
    rw [MonoidHom.pow_apply, map_pow, MonoidHom.one_apply, map_one]
    exact this)
  refine ⟨qkMk hB 0 (q.g + torusPt Q K (Additive.ofMul t₀)) ?_, (qkExt_iff hB f hf _ _).2 (qk_ext hp ?_)⟩
  · simp only [nsmul_add, nq, ← map_nsmul, ← ofMul_pow, t0, ofMul_one, map_zero, zero_add]
  · show p.g = gtExt Q f hf (q.g + torusPt Q K (Additive.ofMul t₀))
    rw [map_add (f := _), GlobalTheory.QkNumberField.gtExt_torusPt, ← ht]
    abel

theorem exists_ptEquiv {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {F : G'.left ⟶ G.left} (gp : IsGrpPullback G' G f F) (T : Over S') (b : T.left ⟶ S) (hb : b = T.hom ≫ f) :
    ∃ ρ : (T ⟶ G') ≃* (Over.mk b ⟶ G), ∀ x, (ρ x).left = x.left ≫ F := by
  subst hb
  refine ⟨MulEquiv.ofBijective (pushHom gp T) ⟨fun x y e => ?_, fun y => ?_⟩, fun _ => rfl⟩
  · exact Over.OverMorphism.ext (gp.1.hom_ext (congrArg (fun q => q.left) e) ((Over.w x).trans (Over.w y).symm))
  · exact ⟨Over.homMk (gp.1.lift y.left T.hom (Over.w y)) (gp.1.lift_snd _ _ _),
      Over.OverMorphism.ext (gp.1.lift_fst _ _ _)⟩

theorem exists_etaA {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
    {B W : Type} [CommRing B] [CommRing W] {b : Geo.Tor.Base l B} {σ : B →+* W} (o : Obj D l b (spMap σ)) {F : Type} [Field F]
    [IsAlgClosed F] (j : W →+* F) (x : Over.mk (spMap j) ⟶ o.t.G) (hx : x ^ l.A = 1) :
    ∃ a, x.left = spMap j ≫ (o.etaA a).left := by
  obtain ⟨-, I, -, h, -⟩ := o.geom F (spMap j) (j.comp σ) (by
    rw [spMap, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp])
  obtain ⟨a, ha⟩ := (I.onto l.A l.A_pos x).1 hx
  refine ⟨a, ?_⟩
  rw [← ha, ← h]
  simp

theorem exists_qkExt_of_divFrom : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (iw : L.W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : P.D.toPre.X ≃ₗ[𝓞 E] L.D.X), (∀ k, ε k ∈ balForms H.bar L.D.X) → (∀ k, s k ≠ 0) → DivFrom L P.D.toPre P.oD iw s ε e → ∀ p : QkPt P.D.toPre (AlgebraicClosure (FractionRing R)) l.M', p.y = 0 → ∃ p₀ : QkPt P.D.toPre (FractionRing R) l.M', QkExt (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) p₀ p := by
  intro E _ _ _ H D' l c L R _ _ _ _ t P iw I _ s ε e hε hs ⟨g, hD, hdiv⟩ p hp
  have hB := P.D.tau_bimult
  have hM : 0 < l.M' := (LowDat.lowLevel l).A_pos
  let K := FractionRing R
  let F := AlgebraicClosure K
  let j : L.W →+* F := (algebraMap K F).comp ((algebraMap R K).comp iw)
  have hj : spMap j = (TF (R := R) F).hom ≫ spMap iw := by
    show _ = (jFK (R := R) F ≫ jK R) ≫ spMap iw
    simp only [j, jFK, jK, spMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  have gp : IsGrpPullback P.D.toPre.P.A L.D.P.A (spMap iw) (hD.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw)) :=
    pull_grp hD
  obtain ⟨ρ₁, h₁⟩ := exists_ptEquiv gp (TF (R := R) F) (spMap j) hj
  obtain ⟨ρ₂, h₂⟩ := exists_ptEquiv L.ab.1 (Over.mk (spMap j)) (spMap j) (Category.comp_id _).symm
  have hbk : p.g.b ^ l.M' = 1 := by rw [← nsmul_b, qk_nsmul hB, hp, map_zero, zero_b]
  obtain ⟨a, ha⟩ := exists_etaA L.o j (ρ₂.symm (ρ₁ p.g.b)) (by
    show _ ^ l.M' = 1
    rw [← map_pow, ← map_pow, hbk, map_one, map_one])
  obtain ⟨q, hq, hqb⟩ := GlobalTheory.T.exists_levelPoint_lift_zero_first_coordinate L P.D.toPre P.oD iw s ε e g hD hε hs hdiv a
  have hζ : IsPrimitiveRoot (⟨zeta l.M', c.zeta_mem⟩ : c.F) l.M' :=
    IsPrimitiveRoot.of_map_of_injective (f := c.F.val.toRingHom) (Complex.isPrimitiveRoot_exp l.M' hM.ne')
      Subtype.val_injective
  refine exists_qkExt_of_b hB (algebraMap K F) (RingHom.comp_id _) hM.ne'
    (hζ.map_of_injective ((algebraMap R K).comp (iw.comp L.b)).injective) p hp q hq ?_
  have e₂ := h₂ (ρ₂.symm (ρ₁ p.g.b))
  rw [ρ₂.apply_symm_apply, ha, h₁] at e₂
  refine gp.1.hom_ext (e₂.trans (Eq.symm ((Category.assoc _ _ _).trans
    ((congrArg (spMap (algebraMap K F) ≫ ·) hqb).trans ?_)))) ?_
  · rw [hj]
    show _ = (((spMap (algebraMap K F) ≫ jK R) ≫ _) ≫ _) ≫ _
    simp only [Category.assoc]
  · exact (Over.w p.g.b).trans ((Over.w (extMap (R := R) (algebraMap K F) (RingHom.comp_id _) ≫ q.g.b)).symm)

end GlobalTheory.DivTorsRat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQkPointExtensionOfDividedDataStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_qkPoint_extension_of_divided_data : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (iw : L.W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : P.D.toPre.X ≃ₗ[𝓞 E] L.D.X), (∀ k, ε k ∈ balForms H.bar L.D.X) → (∀ k, s k ≠ 0) → DivFrom L P.D.toPre P.oD iw s ε e → ∀ p : QkPt P.D.toPre (AlgebraicClosure (FractionRing R)) l.M', p.y = 0 → ∃ p₀ : QkPt P.D.toPre (FractionRing R) l.M', QkExt (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) p₀ p := by
  first | exact @GlobalTheory.DivTorsRat.exists_qkExt_of_divFrom | exact GlobalTheory.DivTorsRat.exists_qkExt_of_divFrom | (intros; apply GlobalTheory.DivTorsRat.exists_qkExt_of_divFrom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelTorsionPointOfComesFromBase
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelTorsionPointOfComesFromBase
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.DivSol

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

def mulPull {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'} (hD : IsPullDeg φ D D') (n : ℕ) :
    IsPullDeg φ (mulDeg D n) (mulDeg D' n) where
  e := hD.e
  e_hom := hD.e_hom
  w := hD.w
  w_gen := hD.w_gen
  he := hD.he
  w_rig := hD.w_rig
  xe := hD.xe
  c_pr := fun (x : D'.X) => by
    have hx : hD.xe (n • x) = n • hD.xe x := map_nsmul hD.xe n x
    show (D'.c (n • x)).left ≫ _ = specOf φ ≫ (D.c (n • hD.xe x)).left
    rw [← hx]
    exact hD.c_pr (n • x)
  W := hD.W
  psiW := ⟨fun (χ : D.X) => hD.psiW.psi (n • χ), fun (χ : D.X) => hD.psiW.psi_gen (n • χ), fun (χ : D.X) => hD.psiW.psi_eq (n • χ)⟩
  g := hD.g
  g_comm := hD.g_comm
  psi_pr := fun (x : D'.X) => by
    have h := hD.psi_pr (n • x)
    have hx : hD.xe (n • x) = n • hD.xe x := map_nsmul hD.xe n x
    rw [hx] at h
    exact h

theorem mulDeg_psiEven (D : DegPre R) (n : ℕ) (h : D.PsiEven) : (mulDeg D n).PsiEven :=
  fun (a : D.X) => MulDeg.corr_even_degenerationData_negPoint D h (n • a) (n • (-a)) (neg_nsmul a n)

theorem mulDeg_tauBimult (D : DegPre R) (n : ℕ) (h : D.TauBimult) : (mulDeg D n).TauBimult :=
  fun (a a' b : D.X) => MulDeg.corr_bimultiplicative_degenerationData_sums D h (n • a) (n • a') (n • b) (n • (a + a')) (n • (a + a' + b)) (n • (a + b))
    (n • (a' + b)) (nsmul_add _ _ _) (by rw [nsmul_add, nsmul_add]) (nsmul_add _ _ _) (nsmul_add _ _ _)

theorem mulDeg_psiUnitOn (D : DegPre R) (n : ℕ) (h : ∀ y, PsiUnitOn D y Set.univ) :
    ∀ y, PsiUnitOn (mulDeg D n) y Set.univ :=
  fun (y : D.X) => h (n • y)

end GlobalTheory.DivSol

namespace GlobalTheory.DivSol

theorem exists_qkPt_of_divFrom : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (iw : L.W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : P.D.toPre.X ≃ₗ[𝓞 E] L.D.X), (∀ k, ε k ∈ balForms H.bar L.D.X) → (∀ k, s k ≠ 0) → DivFrom L P.D.toPre P.oD iw s ε e → ∀ y : P.D.toPre.X, ∃ p₀ : QkPt P.D.toPre (FractionRing R) l.M', p₀.y = y := by
  intro E _ _ _ H D' l c L R _ _ _ _hB t P iw I _ s ε e _hbal hs hdf y
  obtain ⟨g, hD, hg, -, -⟩ := hdf
  obtain ⟨DR, hR, -, -⟩ := GlobalTheory.DegPull.exists_isPullDeg polBaseChange_holds L.W R iw L.D ⊤
    (GlobalTheory.ArcPull.nonempty_psiOn_top L.D L.gen) trivial
  have hbiR : DR.TauBimult := GlobalTheory.tauBimult_of_isPullDeg globalFns_holds _ _ iw L.D DR hR L.bimult
  have hunR : ∀ y, PsiUnitOn DR y Set.univ := GlobalTheory.PullDegTop.psiUnitOn_univ hR L.gen
  have hevR : DR.PsiEven := GlobalTheory.PsiEvenPull.psiEven_pull globalFns_holds _ _ iw L.D DR hR L.even
  have hC : IsPullDeg (RingHom.id R) (mulDeg DR l.M') (GlobalTheory.PolDeg.rescale P.D.toPre g) :=
    (GlobalTheory.Mum.isPullDeg_unique_any L.W R iw (mulDeg L.D l.M') _ _ ⟨mulPull hR l.M'⟩ ⟨hD⟩).some
  obtain ⟨T, ib, β, ββ, w, hF⟩ := GlobalTheory.T.exists_tautologicalBase_nsmul_degenerationData (RingHom.id R) DR hbiR hunR l.M'
  let e' : P.D.toPre.X ≃+ (Fin T.r → ℤ) := hC.xe.trans ib
  let x : (Fin T.r → ℤ) ≃+ L.D.X := e'.symm.trans e.toAddEquiv
  have hx : ∀ a, x (e' a) = e a := fun a => by simp [x]
  let ε' : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ) := fun k =>
    LinearMap.mk₂ ℤ (fun u v => ε k (x u) (H.w0 • x v) + ε k (x v) (H.w0 • x u))
      (fun m₁ m₂ n => by simp only [map_add (f := _), smul_add, LinearMap.add_apply]; ring)
      (fun c m n => by
        simp only [map_zsmul, LinearMap.smul_apply, LinearMap.map_smul, smul_eq_mul]
        rw [smul_comm H.w0 c (x m)]
        simp only [LinearMap.map_smul, smul_eq_mul]; ring)
      (fun m n₁ n₂ => by simp only [map_add (f := _), smul_add, LinearMap.add_apply]; ring)
      (fun c m n => by
        simp only [map_zsmul, LinearMap.smul_apply, LinearMap.map_smul, smul_eq_mul]
        rw [smul_comm H.w0 c (x n)]
        simp only [LinearMap.map_smul, smul_eq_mul]; ring)
  have hne : ∀ i, algebraMap R (FractionRing R) (s i) ≠ 0 := fun i =>
    (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 (hs i)
  have hgv : ∀ y, ((g y : (FractionRing R)ˣ) : FractionRing R) =
      (∏ k, algebraMap R (FractionRing R) (s k) ^ ((l.M' : ℤ) * ε k (e y) (H.w0 • e y)))⁻¹ := fun y => by
    rw [← hg y, Units.val_inv_eq_inv_val, inv_inv]
  have hcoc : ∀ a a' : P.D.toPre.X, (((g (a + a'))⁻¹ * g a * g a' : (FractionRing R)ˣ) : FractionRing R) =
      ∏ i, algebraMap R (FractionRing R) (s i) ^ ((l.M' : ℤ) * ε' i (e' a) (e' a')) := by
    intro a a'
    rw [Units.val_mul, Units.val_mul, hg (a + a'), hgv a, hgv a', ← Finset.prod_inv_distrib,
      ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← zpow_neg, ← zpow_neg, ← zpow_add₀ (hne i), ← zpow_add₀ (hne i)]
    congr 1
    simp only [ε', LinearMap.mk₂_apply, hx, map_add (f := _), smul_add, LinearMap.add_apply]
    ring
  obtain ⟨β', ββ', w', hF'⟩ := GlobalTheory.T.comesFromTautBase_of_rescaled_pullback_monomial T l.M' (mulDeg DR l.M') (mulDeg_psiEven _ _ hevR)
    (mulDeg_tauBimult _ _ hbiR) (mulDeg_psiUnitOn _ _ hunR) ib β ββ w hF R (RingHom.id R) Function.injective_id
    P.D.toPre g hC s ε' e' (fun _ => rfl) hcoc
  obtain ⟨p, hp, -⟩ := GlobalTheory.TInj.exists_qkPt_tautPt T ε' l.M' R P.D.toPre (RingHom.id R) s e' β' ββ' w'
    P.D.tau_bimult hF' hs (FractionRing R) (e' y)
  exact ⟨p, by rw [hp]; simp⟩

end GlobalTheory.DivSol
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelTorsionPointOfComesFromBaseStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_levelTorsionPoint_of_comesFromBase : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (iw : L.W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : P.D.toPre.X ≃ₗ[𝓞 E] L.D.X), (∀ k, ε k ∈ balForms H.bar L.D.X) → (∀ k, s k ≠ 0) → DivFrom L P.D.toPre P.oD iw s ε e → ∀ y : P.D.toPre.X, ∃ p₀ : QkPt P.D.toPre (FractionRing R) l.M', p₀.y = y := by
  first | exact @GlobalTheory.DivSol.exists_qkPt_of_divFrom | exact GlobalTheory.DivSol.exists_qkPt_of_divFrom | (intros; apply GlobalTheory.DivSol.exists_qkPt_of_divFrom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QkPointGaloisFixedUpToEquivDividedData
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.DivGalFix

open GlobalTheory.TorusExt

attribute [local instance] GlobalTheory.TorusExt.gtGroup

theorem qkPt_rational : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (iw : L.W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : P.D.toPre.X ≃ₗ[𝓞 E] L.D.X), (∀ k, ε k ∈ balForms H.bar L.D.X) → (∀ k, s k ≠ 0) → DivFrom L P.D.toPre P.oD iw s ε e → ∀ q : QkPt P.D.toPre (AlgebraicClosure (FractionRing R)) l.M', ∃ q₀ : QkPt P.D.toPre (FractionRing R) l.M', QkExt (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) q₀ q := by
  intro E _ _ _ H D' l c L R _ _ _ hR t P iw I _ s ε e hε hs hD q
  have hB := P.D.tau_bimult
  have ha : (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))).comp
      (algebraMap (FractionRing R) (FractionRing R)) = algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R)) := by
    rw [Algebra.algebraMap_self, RingHom.comp_id]
  obtain ⟨p₀, hy⟩ := GlobalTheory.T.exists_levelTorsionPoint_of_comesFromBase L R hR t P iw s ε e hε hs hD q.y
  let mkIota : ∀ (F : Type) [Field F] [Algebra (FractionRing R) F], P.D.toPre.X →+ GtPtF P.D.toPre F := fun F _ _ => by
    open ReciprocityTheory.ChartRestriction.G.DVR in
    exact AddMonoidHom.mk' (fun x => (exists_iota (F := F) hB x).choose) fun x x' => by
      obtain ⟨b, v⟩ := (isIota_iff_val _ _).1 (exists_iota (F := F) hB x).choose_spec
      obtain ⟨b', v'⟩ := (isIota_iff_val _ _).1 (exists_iota (F := F) hB x').choose_spec
      obtain ⟨b'', v''⟩ := (isIota_iff_val _ _).1 (exists_iota (F := F) hB (x + x')).choose_spec
      refine (isAdd_iff_eq _ _ _).1 ((isAdd_iff_val _ _ _).2 ⟨by rw [b, b', b'', cPoint_add], fun χ y J hJ => ?_⟩)
      have C : IsCub (th P.D.toPre (T := TF (R := R) F) y J) := isCub_cubV P.D.toPre.cub hJ
      rw [v χ y J hJ, v' χ y J hJ, v'' χ y J hJ, b, b', C.s01, C.s12]
      exact tau_mul (𝟙 (TF (R := R) F)) hJ hB x x' χ
  have hi : ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (x : P.D.toPre.X), GtPtF.IsIota x (mkIota F x) := by
    intro F _ _ x
    exact (exists_iota (F := F) hB x).choose_spec
  have hn : ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (p : QkPt P.D.toPre F l.M'), l.M' • p.g = mkIota F p.y := by
    intro F _ _ p
    obtain ⟨h, h₁, h₂⟩ := p.eq
    exact ((isNsmul_iff_eq _ _ _).1 h₁).symm.trans (isIota_unique h₂ (hi F p.y))
  let mkPt : ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (y : P.D.toPre.X) (g : GtPtF P.D.toPre F), l.M' • g = mkIota F y → QkPt P.D.toPre F l.M' := fun F _ _ y g h =>
    ⟨y, g, l.M' • g, (isNsmul_iff_eq _ _ _).2 rfl, h ▸ hi F y⟩
  obtain ⟨p₁, hp₁, -⟩ := existsUnique_qkExt hB _ ha p₀
  have hp₁y : p₁.y = p₀.y := hp₁.1
  have h0 : l.M' • (q.g - p₁.g) = mkIota (AlgebraicClosure (FractionRing R)) 0 := by
    rw [smul_sub, hn, hn, hp₁y, hy, sub_self, map_zero]
  let r := mkPt (AlgebraicClosure (FractionRing R)) 0 (q.g - p₁.g) h0
  obtain ⟨r₀, hr⟩ := GlobalTheory.T.exists_qkPoint_extension_of_divided_data L R hR t P iw s ε e hε hs hD r rfl
  let z := mkPt (FractionRing R) (p₀.y + r₀.y) (p₀.g + r₀.g) (by rw [smul_add, hn, hn, map_add])
  refine ⟨z, ?_⟩
  have hgy : q.y = z.y := by
    change q.y = p₀.y + r₀.y
    have : r₀.y = 0 := by simpa [r, mkPt] using hr.1.symm
    rw [this, add_zero, hy]
  have hgg : q.g = gtExt P.D.toPre _ ha z.g := by
    have hp := (eq_gtExt_iff _ ha _ _).2 hp₁.2
    have hq := (eq_gtExt_iff _ ha _ _).2 hr.2
    change q.g = gtExt P.D.toPre _ ha (p₀.g + r₀.g)
    rw [map_add, ← hp, ← hq]
    change q.g = p₁.g + (q.g - p₁.g)
    abel
  exact ⟨hgy, (eq_gtExt_iff _ ha _ _).1 hgg⟩

theorem qkExt_equiv_of_divFrom : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (iw : L.W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : P.D.toPre.X ≃ₗ[𝓞 E] L.D.X), (∀ k, ε k ∈ balForms H.bar L.D.X) → (∀ k, s k ≠ 0) → DivFrom L P.D.toPre P.oD iw s ε e → ∀ (σ : AlgebraicClosure (FractionRing R) ≃ₐ[FractionRing R] AlgebraicClosure (FractionRing R)) (p p' : QkPt P.D.toPre (AlgebraicClosure (FractionRing R)) l.M'), QkExt σ.toAlgHom.toRingHom p p' → QkPt.Equiv P.D.toPre (AlgebraicClosure (FractionRing R)) p p' := by
  intro E _ _ _ H D' l c L R _ _ _ hR t P iw I _ s ε e hε hs hD σ p p' hpp'
  refine GlobalTheory.Mum.GalFixQ.qkExt_equiv_of_rational R P.D l.M' (fun q => ?_) σ.toAlgHom p p' hpp'
  obtain ⟨q₀, hq⟩ := qkPt_rational L R hR t P iw s ε e hε hs hD q
  exact ⟨q₀, q, hq, qk_equiv_refl P.D.tau_bimult q⟩

end GlobalTheory.DivGalFix
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QkPointGaloisFixedUpToEquivDividedDataStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.qkPoint_galois_fixed_up_to_equiv_divided_data : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (iw : L.W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : P.D.toPre.X ≃ₗ[𝓞 E] L.D.X), (∀ k, ε k ∈ balForms H.bar L.D.X) → (∀ k, s k ≠ 0) → DivFrom L P.D.toPre P.oD iw s ε e → ∀ (σ : AlgebraicClosure (FractionRing R) ≃ₐ[FractionRing R] AlgebraicClosure (FractionRing R)) (p p' : QkPt P.D.toPre (AlgebraicClosure (FractionRing R)) l.M'), QkExt σ.toAlgHom.toRingHom p p' → QkPt.Equiv P.D.toPre (AlgebraicClosure (FractionRing R)) p p' := by
  first | exact @GlobalTheory.DivGalFix.qkExt_equiv_of_divFrom | exact GlobalTheory.DivGalFix.qkExt_equiv_of_divFrom | (intros; apply GlobalTheory.DivGalFix.qkExt_equiv_of_divFrom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreTorsionRationalOfBase
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UCanon

theorem torsRat_of_divFrom : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (iw : L.W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : P.D.toPre.X ≃ₗ[𝓞 E] L.D.X), (∀ k, ε k ∈ balForms H.bar L.D.X) → (∀ k, s k ≠ 0) → DivFrom L P.D.toPre P.oD iw s ε e → GlobalTheory.TChart.TorsRat t.G l.M' := by
  intro E _ _ _ H D' l c L R _ _ _ hR t P iw I _ s ε e hε hs hD
  haveI : CharZero R := hR.2
  have hadm : AdmBase R (maximalIdeal R) := hR.1
  have hn : 1 ≤ l.M' := Nat.lcm_pos (by have := l.three_le; omega) l.A_pos
  haveI := P.U.gen_hom
  refine GlobalTheory.TorsDescent.torsRat_of_retract_galoisFixed t.G t.G P.A P.U.gen (𝟙 _) (𝟙 _) l.M' P.U.gen_hom
    inferInstance inferInstance (Category.comp_id _) hn ?_
  intro σ x hx
  obtain ⟨y, hy0⟩ : ∃ y : (Over.map (jK R)).obj (TFK (R := R) (AlgebraicClosure (FractionRing R))) ⟶ t.G, y = x := ⟨_, rfl⟩
  obtain ⟨h, hh0⟩ : ∃ h : TFK (R := R) (AlgebraicClosure (FractionRing R)) ⟶ (Over.pullback (jK R)).obj t.G,
    h = (Over.mapPullbackAdj (jK R)).unit.app _ ≫ (Over.pullback (jK R)).map y := ⟨_, rfl⟩
  have hy : y ^ l.M' = 1 := by rw [hy0]; exact hx
  have hmp : ∀ m : ℕ, (Over.pullback (jK R)).map (y ^ m) = ((Over.pullback (jK R)).map y) ^ m := by
    intro m
    induction m with
    | zero => simp [Functor.map_one]
    | succ m ih => rw [pow_succ, Functor.map_mul, ih, pow_succ]
  have hh : h ^ l.M' = 1 := by
    rw [hh0, ← MonObj.comp_pow, ← hmp, hy, Functor.map_one, MonObj.comp_one]
  obtain ⟨a, ha0⟩ : ∃ a : TFK (R := R) (AlgebraicClosure (FractionRing R)) ⟶ P.A.A, a = h ≫ P.U.gen.hom := ⟨_, rfl⟩
  have ha : a ^ l.M' = 1 := by
    rw [ha0, ← MonObj.pow_comp, hh, MonObj.one_comp]
  obtain ⟨f, hT, -⟩ := GlobalTheory.TorsionIso.torsion_clause R (maximalIdeal R) hadm P.D P.A t.G t.semi P.U
    (AlgebraicClosure (FractionRing R)) l.M' hn
  obtain ⟨p, hp⟩ := hT.2.1 a ha
  obtain ⟨⟨p', hext⟩, hpt, hiff⟩ := GlobalTheory.UT.Cl.galois_holds R (maximalIdeal R) hadm P.D P.A t.G t.semi P.U
    (AlgebraicClosure (FractionRing R)) (AlgebraicClosure (FractionRing R)) σ.toAlgHom l.M' hn p
  obtain ⟨a', ha'⟩ := hpt a
  have h2 := (hiff p' a a' hext ha').1 ((hT.1 p a).2 hp.symm)
  have heq := GlobalTheory.T.qkPoint_galois_fixed_up_to_equiv_divided_data L R hR t P iw s ε e hε hs hD σ p p' hext
  have haa : a' = a := ((hT.1 p' a').1 h2).trans (((hT.2.2.1 p p').2 heq).symm.trans hp)
  rw [haa] at ha'
  have e1 : (Over.mapPullbackAdj (jK R)).homEquiv _ _ y = h := by rw [Adjunction.homEquiv_unit, hh0]
  have hyl : y.left = h.left ≫ ((Over.mapPullbackAdj (jK R)).counit.app t.G).left := by
    have e2 : y = (Over.map (jK R)).map h ≫ (Over.mapPullbackAdj (jK R)).counit.app t.G := by
      conv_lhs => rw [← ((Over.mapPullbackAdj (jK R)).homEquiv _ _).symm_apply_apply y, e1]
      exact Adjunction.homEquiv_counit _ _ _ _
    rw [e2, Over.comp_left]
    rfl
  have hhl : spMap σ.toAlgHom.toRingHom ≫ h.left = h.left := by
    have := congrArg (· ≫ P.U.gen.inv.left) ha'
    simp only [ha0, Over.comp_left, Category.assoc] at this
    rw [← Over.comp_left _ _ _ P.U.gen.hom P.U.gen.inv, Iso.hom_inv_id, Over.id_left, Category.comp_id] at this
    exact this.symm
  have hyx : spMap σ.toAlgHom.toRingHom ≫ y.left = y.left := by
    rw [hyl, ← Category.assoc, hhl]
  rw [hy0] at hyx
  simpa using hyx

end GlobalTheory.UCanon
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreTorsionRationalOfBaseStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericFibre_torsion_rational_of_base : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (iw : L.W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : P.D.toPre.X ≃ₗ[𝓞 E] L.D.X), (∀ k, ε k ∈ balForms H.bar L.D.X) → (∀ k, s k ≠ 0) → DivFrom L P.D.toPre P.oD iw s ε e → GlobalTheory.TChart.TorsRat t.G l.M' := by
  first | exact @GlobalTheory.UCanon.torsRat_of_divFrom | exact GlobalTheory.UCanon.torsRat_of_divFrom | (intros; apply GlobalTheory.UCanon.torsRat_of_divFrom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsRatAwayIff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TorsAway

theorem torsRat_away_iff : ∀ (R : Type) [CommRing R] [IsDomain R] (f : R) [IsDomain (Localization.Away f)] (G : Over (Sp R))
    [GrpObj G] (G' : Over (Sp (Localization.Away f))) [GrpObj G'] (π : G'.left ⟶ G.left),
    IsGrpPullback G' G (spMap (algebraMap R (Localization.Away f))) π → ∀ n : ℕ,
      GlobalTheory.TChart.TorsRat G n ↔ GlobalTheory.TChart.TorsRat G' n := by
  intro R _ _ f _ G _ G' _ π hπ n
  have hf : f ≠ 0 := by
    rintro rfl
    have : Subsingleton (Localization.Away (0 : R)) :=
      IsLocalization.subsingleton (M := Submonoid.powers (0 : R)) ⟨1, pow_one _⟩
    exact not_subsingleton (Localization.Away (0 : R)) this
  have hle : Submonoid.powers f ≤ nonZeroDivisors R := powers_le_nonZeroDivisors_of_noZeroDivisors hf
  have hinj : Function.Injective (algebraMap R (Localization.Away f)) := IsLocalization.injective _ hle
  constructor
  · exact GlobalTheory.TChart.AbLevel.torsRat_of_isGrpPullback _ hinj hπ
  · intro h K _ _ κ x hx
    letI : Algebra (Localization.Away f) (FractionRing R) :=
      IsLocalization.localizationAlgebraOfSubmonoidLe (Localization.Away f) (FractionRing R) _ _ hle
    haveI : IsScalarTower R (Localization.Away f) (FractionRing R) :=
      IsLocalization.localization_isScalarTower_of_submonoid_le (Localization.Away f) (FractionRing R) _ _ hle
    haveI : IsFractionRing (Localization.Away f) (FractionRing R) :=
      IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers f) (Localization.Away f)
        (FractionRing R)
    let e := FractionRing.algEquiv (Localization.Away f) (FractionRing R)
    let j : FractionRing (Localization.Away f) →+* FractionRing R := e.toAlgHom.toRingHom
    have hj : ∀ r : R, j (algebraMap _ (FractionRing (Localization.Away f)) (algebraMap R (Localization.Away f) r)) =
        algebraMap R (FractionRing R) r := by
      intro r
      exact (e.commutes _).trans (IsScalarTower.algebraMap_apply R (Localization.Away f) (FractionRing R) r).symm
    have hsq : spMap j ≫ jK (Localization.Away f) ≫ spMap (algebraMap R (Localization.Away f)) = jK R := by
      show spMap j ≫ spMap (algebraMap _ (FractionRing (Localization.Away f))) ≫ spMap (algebraMap R (Localization.Away f)) =
        spMap (algebraMap R (FractionRing R))
      rw [← ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp, ← ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp]
      exact congrArg spMap (RingHom.ext hj)
    let T : Over (Sp (Localization.Away f)) := Over.mk (spMap (κ.comp j) ≫ jK (Localization.Away f))
    have hT : T.hom ≫ spMap (algebraMap R (Localization.Away f)) = spMap κ ≫ jK R := by
      show (spMap (κ.comp j) ≫ jK (Localization.Away f)) ≫ spMap (algebraMap R (Localization.Away f)) = _
      rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp, Category.assoc, Category.assoc, hsq]
    let e0 : Over.mk (T.hom ≫ spMap (algebraMap R (Localization.Away f))) ⟶ Over.mk (spMap κ ≫ jK R) :=
      Over.homMk (𝟙 _) ((Category.id_comp _).trans hT.symm)
    let x' := (GlobalTheory.ObjPull.pushEquiv hπ T).symm (e0 ≫ x)
    have hx' : x' ^ n = 1 := by
      simp only [x']
      rw [← map_pow, ← MonObj.comp_pow, hx, MonObj.comp_one, map_one]
    obtain ⟨y, hy⟩ := h K (κ.comp j) x' hx'
    have hyw : y.left ≫ G'.hom = jK (Localization.Away f) := Over.w y
    refine ⟨Over.homMk (spMap j ≫ y.left ≫ π) ?_, ?_⟩
    · show (spMap j ≫ y.left ≫ π) ≫ G.hom = jK R
      rw [Category.assoc, Category.assoc, hπ.1.w, ← Category.assoc y.left, hyw]
      exact hsq
    · show x.left = spMap κ ≫ spMap j ≫ y.left ≫ π
      have h1 : x'.left ≫ π = x.left :=
        (GlobalTheory.ObjPull.pushEquiv_symm_left hπ T (e0 ≫ x)).trans (Category.id_comp _)
      rw [← h1, hy, ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp]
      simp only [Category.assoc]

end GlobalTheory.TorsAway
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassifiedOnOpenOfSpecialisesToClassified
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ClsOpen

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

end GlobalTheory.ClsOpen


open GlobalTheory.ClsOpen in
theorem GlobalTheory.clsOpen : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (D' : Datum H) (L : LowBase D' c) (R V : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base R → GlobalTheory.Mum.Base V → ∀ (C : Fam Xo c V) (t₁ : SAB H (Sp R)) (P₁ : PELUnif (maximalIdeal R) t₁) (iw : L.W →+* R) (θ : R →+* V), IsLocalHom θ → θ.comp (iw.comp L.b) = C.b → ∀ (m N : ℕ) (s : Fin m ⊕ Fin N → R) (ε : Fin m ⊕ Fin N → LinearMap.BilinForm ℤ L.D.X) (e₁ : P₁.D.toPre.X ≃ₗ[𝓞 E] L.D.X) (e : C.P.D.toPre.X ≃ₗ[𝓞 E] L.D.X), (∀ k, ε k ∈ balForms H.bar L.D.X) → (∀ i, θ (s (.inl i)) ≠ 0) → (∀ j, IsUnit (s (.inr j))) → DivFrom L P₁.D.toPre P₁.oD iw s ε e₁ → DivFrom L C.P.D.toPre C.P.oD (θ.comp iw) (fun k => θ (s k)) ε e → ∃ (y₁ : Sp (FractionRing R) ⟶ Xo.XF c) (yo : Sp (Localization.Away (∏ i, s (.inl i))) ⟶ Xo.XF c) (κ : Sp (FractionRing V) ⟶ Sp (Localization.Away (∏ i, s (.inl i)))), y₁ ≫ pullback.snd _ _ = jK R ≫ spMap (iw.comp L.b) ∧ GlobalTheory.UPoinc.GenOf Xo c y₁ t₁ ∧ (∀ g : Sp (FractionRing R) ⟶ Sp (Localization.Away (∏ i, s (.inl i))), g ≫ spMap (algebraMap R (Localization.Away (∏ i, s (.inl i)))) = jK R → g ≫ yo = y₁) ∧ κ ≫ spMap (algebraMap R (Localization.Away (∏ i, s (.inl i)))) = jK V ≫ spMap θ ∧ κ ≫ yo = C.y := by
  intro E _ _ _ H Dw l Xo c φ D' L R V _ _ _ _ _ _ hR hV C t₁ P₁ iw θ hθ hb m N s ε e₁ e hε hs hu hD₁ hD
  set f : R := ∏ i, s (.inl i) with hf_def
  have hθf : θ f ≠ 0 := by rw [hf_def, map_prod]; exact Finset.prod_ne_zero_iff.2 fun i _ => hs i
  have hf0 : f ≠ 0 := fun h => hθf (by rw [h, map_zero])
  have hsk : ∀ k, s k ≠ 0 := by
    rintro (i | j)
    · exact fun h => hs i (by rw [h, map_zero])
    · exact (hu j).ne_zero
  have hθk : ∀ k, θ (s k) ≠ 0 := by
    rintro (i | j)
    · exact hs i
    · exact ((hu j).map θ).ne_zero
  let A := Localization.Away f
  have hpow : Submonoid.powers f ≤ nonZeroDivisors R := powers_le_nonZeroDivisors_of_noZeroDivisors hf0
  haveI : IsDomain A := IsLocalization.isDomain_localization hpow
  haveI : IsNoetherianRing A := IsLocalization.isNoetherianRing (Submonoid.powers f) A hR.1.1
  haveI : IsIntegrallyClosed R := hR.1.2.2.1
  haveI : IsIntegrallyClosed A := isIntegrallyClosed_of_isLocalization A (Submonoid.powers f) hpow
  have hψ := GlobalTheory.T.psiUnitOn_basicOpen_of_comesFromBase L P₁.D.toPre P₁.oD iw s ε e₁ hD₁ f (by
    rintro (i | j)
    · exact ⟨1, by rw [pow_one, hf_def]; exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)⟩
    · exact ⟨0, (hu j).dvd⟩)
  obtain ⟨tO, ⟨mO⟩⟩ := GlobalTheory.TraitOrder.exists_pull (spMap (algebraMap R A)) t₁
  obtain ⟨hpr, ham, hkt⟩ := GlobalTheory.T.isProper_relAmple_kTriv_of_trivialisations_generate R hR t₁ P₁ f hψ tO mO
  have htors : GlobalTheory.TChart.TorsRat tO.G l.M' :=
    (GlobalTheory.TorsAway.torsRat_away_iff R f t₁.G tO.G mO.φ mO.cart l.M').1 (GlobalTheory.T.genericFibre_torsion_rational_of_base L R hR t₁ P₁ iw s ε e₁ hε hsk hD₁)
  let K := FractionRing V
  have hunitK : IsUnit (((algebraMap V K).comp θ) f) := by
    rw [RingHom.comp_apply]
    exact isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (IsFractionRing.injective V K)).2 hθf)
  let g : A →+* K := IsLocalization.Away.lift f hunitK
  have hg : g.comp (algebraMap R A) = (algebraMap V K).comp θ := IsLocalization.lift_comp _
  let bA : c.F →+* A := (algebraMap R A).comp (iw.comp L.b)
  let incl := (IntermediateField.inclusion c.le).toRingHom
  have hgb : g.comp bA = (algebraMap V K).comp C.b := by
    show g.comp ((algebraMap R A).comp (iw.comp L.b)) = _
    rw [← RingHom.comp_assoc, hg, RingHom.comp_assoc, hb]
  have E1 : spMap g ≫ spMap (algebraMap R A) = jK V ≫ spMap θ :=
    (spMap_comp' _ _).symm.trans ((congrArg spMap hg).trans (spMap_comp' _ _))
  obtain ⟨oK, ⟨mK⟩⟩ := GlobalTheory.LevelQuotRep.obj_pull_same Xo.univ (C.y ≫ pullback.fst _ _)
  have hsK : (C.y ≫ pullback.fst _ _) ≫ Xo.s = spMap g ≫ spMap (bA.comp incl) := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, C.y_over, spMap_comp' incl bA, ← Category.assoc,
      ← spMap_comp' bA g, hgb, spMap_comp']
  obtain ⟨tK, ⟨m₁⟩, ⟨m₂⟩⟩ := (genOf_iff Xo c C.y C.t).1 C.gen
  obtain ⟨bc⟩ := GlobalTheory.T.exists_tripleMap_of_same_uniformised_coords L R V hR hV t₁ P₁ C.t C.P iw θ hθ s ε e₁ e hθk hD₁ hD
  obtain ⟨n₁⟩ := GlobalTheory.TraitOrder.cancel (Category.id_comp _) m₂ mK.toSABMap
  obtain ⟨n₂⟩ := GlobalTheory.TraitOrder.comp rfl bc m₁
  obtain ⟨n₃⟩ := GlobalTheory.TraitOrder.comp (Category.id_comp _) n₂ n₁
  obtain ⟨n₄⟩ := GlobalTheory.TraitOrder.cancel E1 mO n₃
  obtain ⟨o, ho, ⟨mo⟩⟩ := GlobalTheory.T.exists_unitaryModuliObject_spread_normal_domain Dw l c A bA tO hpr ham hkt htors K g _ oK hsK n₄
  obtain ⟨f₀, ⟨hf₀s, ⟨mf₀⟩⟩, -⟩ := Xo.rep (Sp A) (spMap (bA.comp incl)) inferInstance o
  have hf₀ : f₀ ≫ Xo.s = spMap bA ≫ spMap incl := by rw [hf₀s, spMap_comp']
  let yo : Sp A ⟶ Xo.XF c := pullback.lift f₀ (spMap bA) hf₀
  have hκ : spMap g ≫ yo = C.y := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst]
      obtain ⟨mk'⟩ := GlobalTheory.LevelQuotRep.obj_comp mo mf₀
      exact (Xo.rep (Sp K) _ inferInstance oK).unique ⟨by rw [Category.assoc, hf₀s, hsK], ⟨mk'⟩⟩ ⟨rfl, ⟨mK⟩⟩
    · rw [Category.assoc, pullback.lift_snd, C.y_over, ← spMap_comp', hgb, spMap_comp']
  have hunitR : IsUnit ((algebraMap R (FractionRing R)) f) :=
    isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hf0)
  let jA : A →+* FractionRing R := IsLocalization.Away.lift f hunitR
  have hjA : jA.comp (algebraMap R A) = algebraMap R (FractionRing R) := IsLocalization.lift_comp _
  have hg₀ : spMap jA ≫ spMap (algebraMap R A) = jK R := by rw [← spMap_comp', hjA]
  have mo' : SABMap tO Xo.univ.t f₀ := ho ▸ mf₀.toSABMap
  refine ⟨spMap jA ≫ yo, yo, spMap g, ?_, ?_, ?_, E1, hκ⟩
  · rw [Category.assoc, pullback.lift_snd, ← hg₀, Category.assoc]
    show spMap jA ≫ spMap ((algebraMap R A).comp (iw.comp L.b)) = _
    rw [spMap_comp']
  · refine (genOf_iff Xo c _ t₁).2 ?_
    obtain ⟨t', ⟨n⟩⟩ := GlobalTheory.TraitOrder.exists_pull (spMap jA) tO
    exact ⟨t', GlobalTheory.TraitOrder.comp hg₀ mO n,
      GlobalTheory.TraitOrder.comp (by rw [Category.assoc, pullback.lift_fst]) mo' n⟩
  · intro g' hg'
    obtain ⟨φ', rfl⟩ := Spec.map_surjective g'
    have h2 : CommRingCat.ofHom (algebraMap R A) ≫ φ' = CommRingCat.ofHom (algebraMap R (FractionRing R)) :=
      Spec.map_injective (by rw [Spec.map_comp]; exact hg')
    have h3 : φ'.hom = jA := IsLocalization.ringHom_ext (Submonoid.powers f)
      ((congrArg CommRingCat.Hom.hom h2).trans hjA.symm)
    have h4 : φ' = CommRingCat.ofHom jA := by ext1; exact h3
    rw [h4]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassifiedOnOpenOfSpecialisesToClassifiedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classified_on_open_of_specialises_to_classified : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (D' : Datum H) (L : LowBase D' c) (R V : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base R → GlobalTheory.Mum.Base V → ∀ (C : Fam Xo c V) (t₁ : SAB H (Sp R)) (P₁ : PELUnif (maximalIdeal R) t₁) (iw : L.W →+* R) (θ : R →+* V), IsLocalHom θ → θ.comp (iw.comp L.b) = C.b → ∀ (m N : ℕ) (s : Fin m ⊕ Fin N → R) (ε : Fin m ⊕ Fin N → LinearMap.BilinForm ℤ L.D.X) (e₁ : P₁.D.toPre.X ≃ₗ[𝓞 E] L.D.X) (e : C.P.D.toPre.X ≃ₗ[𝓞 E] L.D.X), (∀ k, ε k ∈ balForms H.bar L.D.X) → (∀ i, θ (s (.inl i)) ≠ 0) → (∀ j, IsUnit (s (.inr j))) → DivFrom L P₁.D.toPre P₁.oD iw s ε e₁ → DivFrom L C.P.D.toPre C.P.oD (θ.comp iw) (fun k => θ (s k)) ε e → ∃ (y₁ : Sp (FractionRing R) ⟶ Xo.XF c) (yo : Sp (Localization.Away (∏ i, s (.inl i))) ⟶ Xo.XF c) (κ : Sp (FractionRing V) ⟶ Sp (Localization.Away (∏ i, s (.inl i)))), y₁ ≫ pullback.snd _ _ = jK R ≫ spMap (iw.comp L.b) ∧ GlobalTheory.UPoinc.GenOf Xo c y₁ t₁ ∧ (∀ g : Sp (FractionRing R) ⟶ Sp (Localization.Away (∏ i, s (.inl i))), g ≫ spMap (algebraMap R (Localization.Away (∏ i, s (.inl i)))) = jK R → g ≫ yo = y₁) ∧ κ ≫ spMap (algebraMap R (Localization.Away (∏ i, s (.inl i)))) = jK V ≫ spMap θ ∧ κ ≫ yo = C.y := by
  first | exact @GlobalTheory.clsOpen | exact GlobalTheory.clsOpen | (intros; apply GlobalTheory.clsOpen <;> assumption)
end
