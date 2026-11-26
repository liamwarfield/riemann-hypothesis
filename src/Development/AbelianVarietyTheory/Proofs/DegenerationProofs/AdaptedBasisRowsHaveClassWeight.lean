module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaConstantBoundedByShortestVector

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomogeneousCoordinatesOfGeometricFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomogeneousCoordinatesOfGeometricFibre
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
open GlobalTheory.UT GlobalTheory.ZH.ClassWeight

noncomputable section
namespace GlobalTheory.ZH.CrdMove

theorem stk_onto {F : Type} [Field F] (z : Sp F) : Function.Surjective (toStk z) := fun a => by
  obtain ⟨U, hU, f, rfl⟩ := (Sp F).presheaf.exists_germ_eq a
  obtain rfl : U = ⊤ := eq_top_iff.2 fun y _ => (Subsingleton.elim (α := PrimeSpectrum F) z y) ▸ hU
  obtain ⟨x, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 f
  exact ⟨x, rfl⟩

theorem stk_valR {F : Type} [Field F] {X : Scheme.{0}} (x : Sp F ⟶ X) (U : X.Opens) (z : Sp F) (h : x z ∈ U)
    (a : Γ(X, U)) : toStk z (valR x U a) = gs x z U a := by
  rw [valR_of_field, valF, dite_eq_left ((top_le_iff_mem x U z).2 h), gs_eq x z U h]
  show ((Sp F).presheaf.germ ⊤ z trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
    ((Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom _)) = _
  rw [Iso.hom_inv_id_apply]
  exact TopCat.Presheaf.germ_res_apply (Sp F).presheaf (homOfLE ((top_le_iff_mem x U z).2 h)) z trivial _

theorem crd_iff {F : Type} [Field F] {X : Scheme.{0}} {H : LB X} {J : Type} (s : J → H.Sec) (x : Sp F ⟶ X)
    (v : J → F) (z : Sp F) : Crd H s x v ↔ ∃ (l : H.ι) (c : ((Sp F).presheaf.stalk z)ˣ), x z ∈ H.U l ∧
      ∀ j, toStk z (v j) = c.val * gs x z (H.U l) ((s j).f l) := by
  constructor
  · rintro ⟨l, c, hl, hv⟩
    have hz := (top_le_iff_mem x _ z).1 hl
    refine ⟨l, Units.map (toStk z).toMonoidHom c, hz, fun j => ?_⟩
    rw [hv, map_mul, stk_valR x _ z hz]
    rfl
  · rintro ⟨l, c, hz, hv⟩
    obtain ⟨d, hd⟩ := stk_onto z c.val
    have d0 : d ≠ 0 := fun h0 => by
      have : Nontrivial ((Sp F).presheaf.stalk z) := inferInstance
      rw [h0, map_zero] at hd
      exact Units.ne_zero _ hd.symm
    refine ⟨l, Units.mk0 d d0, (top_le_iff_mem x _ z).2 hz, fun j => (toStk z).injective ?_⟩
    rw [hv, map_mul, stk_valR x _ z hz, Units.val_mk0, hd]

theorem crd_move {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A]
    {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
    {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
    {L₀ : LB G.left} {L₁ : LB A.left} (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (w : LB.Iso L₁ (L₀.pull φ)) {n : ℤ} {I : Type}
    (t : I → LB.Sec (LPow A L₁ n T)) (s : I → LB.Sec (LPow G L₀ n T₀))
    (h : ∀ i, ThetaPtMove.SecRel hp τ hτ w (t i) (s i)) {F : Type} [Field F] (r : Sp F ⟶ (T ⊗ A).left) (v : I → F)
    (hv : Crd (LPow A L₁ n T) t r v) : Crd (LPow G L₀ n T₀) s (r ≫ ThetaPtMove.psi hp τ hτ) v := by
  let z : Sp F := IsLocalRing.closedPoint F
  obtain ⟨l, c, hl, hc⟩ := (crd_iff t r v z).1 hv
  obtain ⟨J, hJ, -⟩ := exists_good L₀ hL₀ z (K := Empty) (fun k => k.elim) (fun k => k.elim) (fun k => k.elim)
    (fun k => k.elim)
  obtain ⟨J', hJ', e⟩ := exists_good L₁ hL₁ z (fun _ : Fin 1 => r ≫ (snd T A).left) l
    (fun a b _ => congrArg l (Subsingleton.elim a b)) (fun k => Set.mem_iInter.1 hl k)
  obtain ⟨d, hd⟩ : ∃ d : ((Sp F).presheaf.stalk z)ˣ, ∀ j,
      VVRank.sv G (s j) (r ≫ ThetaPtMove.psi hp τ hτ) z J = d.val * VVRank.sv A (t j) r z J' :=
    ⟨_, fun j => h j _ r z J J' hJ hJ'⟩
  refine (crd_iff s _ v z).2 ⟨fun _ => J ((r ≫ ThetaPtMove.psi hp τ hτ) ≫ (snd T₀ G).left),
    c * d⁻¹,
    hJ.mem (fun _ : Fin 1 => (snd T₀ G).left) _, fun j => ?_⟩
  have q := hd j
  have q' := sval_of (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => n) (t j) r z J' l e
  refine (hc j).trans ?_
  rw [Units.val_mul, _root_.mul_assoc]
  refine congrArg (c.val * ·) ?_
  rw [Units.eq_inv_mul_iff_mul_eq]
  exact (congrArg (_ * ·) q'.symm).trans q.symm

theorem crd_of_moved : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (w : LB.Iso u.A.L (ρ.P.L.pull u.φ)), w.IsGen → ∀ t : S.J → SecA u.A (PadicAlgCl p) S.N, (∀ i, Moved u w (t i) (ρ.s i)) → ∀ (a : u.PtC) (v : S.J → PadicAlgCl p), Crd (LPow u.A.A u.A.L (S.N : ℤ) (TFK (R := u.V) (PadicAlgCl p))) t (show Sp (PadicAlgCl p) ⟶ _ from (ptSecT u.A.A (a ≫ u.U.gen.hom)).left) v → ρ.Crd (u.toA a) v := by
  intro o Ω _ _ _ _ S ρ p _ y₀ u w _ t ht a v hv
  refine ⟨_, ?_, crd_move u.cart (T := TFK (R := u.V) (PadicAlgCl p)) (T₀ := baseOver (Sp S.R)) (spMap y₀)
    (base_eq u) ρ.P.isLB u.A.isLB w t ρ.s ht _ v hv⟩
  refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (ThetaPtMove.psi_snd' _ _ _)).trans ?_)
  refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ u.φ) (ThetaPtMove.ptSecT_snd _)).trans ?_)
  exact Category.assoc _ _ _

end GlobalTheory.ZH.CrdMove
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomogeneousCoordinatesOfGeometricFibreStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
open GlobalTheory.UT GlobalTheory.ZH.ClassWeight
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homogeneousCoordinates_of_geometricFibre : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (w : LB.Iso u.A.L (ρ.P.L.pull u.φ)), w.IsGen → ∀ t : S.J → SecA u.A (PadicAlgCl p) S.N, (∀ i, Moved u w (t i) (ρ.s i)) → ∀ (a : u.PtC) (v : S.J → PadicAlgCl p), Crd (LPow u.A.A u.A.L (S.N : ℤ) (TFK (R := u.V) (PadicAlgCl p))) t (show Sp (PadicAlgCl p) ⟶ _ from (ptSecT u.A.A (a ≫ u.U.gen.hom)).left) v → ρ.Crd (u.toA a) v := by
  first | exact @GlobalTheory.ZH.CrdMove.crd_of_moved | exact GlobalTheory.ZH.CrdMove.crd_of_moved | (intros; apply GlobalTheory.ZH.CrdMove.crd_of_moved <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGenericSectionsFromIntegralModel
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGenericSectionsFromIntegralModel
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
open GlobalTheory.UT GlobalTheory.ZH.ClassWeight

noncomputable section
namespace GlobalTheory.ZH.IntegralCarry
open GlobalTheory.FieldBaseChange GlobalTheory.ThetaScalar ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ZH.ParTranslate GlobalTheory.ThetaSpecialise

section
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G] (U : UnifPre I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ)

theorem expandsG_extend
    (σ : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))))
    (f : ∀ α : D.toPre.X, D.toPre.SecB k α) (hE : ∀ e, U.ExpandsAt e k σ f) (s : Fam D.toPre F k)
    (hs : FamOf D.toPre F f s) : U.ExpandsG F k (extendSec U F k (genericSec U k σ)) s := by
  have one : ∀ {Y : Scheme.{0}} (π : Y ⟶ Spec (CommRingCat.of F)) (y : Y), gs (𝟙 Y) y ⊤ (scal π (1 : F)) = 1 :=
    fun π y => by simp only [gs_eq _ y ⊤ trivial, scal, map_one]
  refine ⟨1, fun _ => 1, fun _ => σ, fun _ => f, fun _ => hE,
    (secLin_iff_val U.LG.isLB _ _ _ _).2 fun y J hJ => ?_,
    fun α => (secLin_iff_val D.toPre.P.isLB _ _ _ _).2 fun y J hJ => ?_⟩
  · rw [Fin.sum_univ_one, one, _root_.one_mul]
    exact (sval_pullOver _ _ _ _ hJ).trans ((sval_pullOver _ _ _ _ hJ).trans
      (congrArg (fun q => sval σ q y J) (Category.assoc _ _ _)))
  · rw [Fin.sum_univ_one, one, _root_.one_mul]
    exact (SectionScalarValuation.secScal_sval (hs α) _ y hJ).symm

theorem famOf_zero (f : ∀ α : D.toPre.X, D.toPre.SecB k α) (s : Fam D.toPre F k)
    (hs : FamOf D.toPre F f s) (α : D.toPre.X) (h : ∀ j, (f α).f j = 0) (j) : (s.s α).f j = 0 := by
  refine sec_ext_val (s' := (0 : Fam D.toPre F k).s α) D.toPre.P.isLB (fun y J hJ => ?_) j
  refine (SectionScalarValuation.secScal_sval (hs α) _ y hJ).symm.trans (Eq.trans ?_ (sval_zero' (π := famBase D.toPre F) hJ _).symm)
  exact (gs_eq _ _ _ (hJ.mem _ _) _).trans ((congrArg _ ((congrArg _ (h _)).trans (map_zero _))).trans (map_zero _))

theorem crd_carries (w : W0 U) {J : Type}
    (σ : J → LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))))
    (t : J → SecA A F k) (ht : ∀ i, Carries U F k w (t i) (extendSec U F k (genericSec U k (σ i))))
    (a : TFK (R := R) F ⟶ (Over.pullback (jK R)).obj G) (v : J → F)
    (h : Crd _ σ (show Sp F ⟶ G.left from a.left ≫ pullback.fst G.hom (jK R)) v) :
    Crd (LPow A.A A.L (k : ℤ) (TFK (R := R) F)) t (show Sp F ⟶ _ from (ptSecT A.A (a ≫ U.gen.hom)).left) v := by
  obtain ⟨l', c, hl', hv⟩ := h
  obtain ⟨l, rfl⟩ : ∃ l : U.LG.L.ι, l' = fun _ : Fin 1 => l := ⟨l' 0, funext fun i => congrArg l' (Subsingleton.elim _ _)⟩
  let y : Sp F := IsLocalRing.closedPoint F
  let x : Sp F ⟶ G.left := a.left ≫ pullback.fst G.hom (jK R)
  have m : x y ∈ LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => l) := (top_le_iff_mem _ _ y).1 hl'
  have m₀ : x y ∈ U.LG.L.U l := mem_wchart.1 m 0
  obtain ⟨J₀, hJ⟩ := GlobalTheory.UT.CoefBasic.exists_good' A.isLB y
  obtain ⟨d, hd⟩ := exists_unit_carries U F k w a l ((top_le_iff_mem x _ y).2 m₀) y J₀ hJ
  obtain ⟨d₀, hd₀⟩ := toStk_onto y d.val
  have hd₁ : d₀ ≠ 0 := fun h0 => by
    have : Nontrivial ((Sp F).presheaf.stalk y) := inferInstance
    rw [h0, map_zero] at hd₀
    exact Units.ne_zero _ hd₀.symm
  let r : Sp F ⟶ (UnifPre.GF (G := G) F).left := (lift (𝟙 (TFK (R := R) F)) a).left
  let r' : Sp F ⟶ (TFK (R := R) F ⊗ A.A).left := (ptSecT A.A (a ≫ U.gen.hom)).left
  have e₀ : r ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left = a.left :=
    congrArg (fun q => q.left) (lift_snd (𝟙 (TFK (R := R) F)) a)
  have e₁ : (r ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left) ≫ pullback.fst G.hom (jK R) = x := by
    rw [e₀]
  have m₂ : ((r ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left) ≫ pullback.fst G.hom (jK R)) y ∈
      U.LG.L.U l := e₁ ▸ m₀
  have m' := hJ.mem (fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left) r'
  refine ⟨fun _ : Fin 1 => J₀ (r' ≫ (snd (TFK (R := R) F) A.A).left), c * Units.mk0 d₀ hd₁,
    (top_le_iff_mem r' _ y).2 m', fun i => ?_⟩
  rw [hv i, Units.val_mul, _root_.mul_assoc, Units.val_mk0]
  refine congrArg _ ((toStk y).injective ?_)
  rw [map_mul, hd₀]
  refine (toStk_valF_gs x _ y m _).trans (Eq.trans ?_ ((hd _ _ (ht i)).trans
    (congrArg _ (toStk_valF_gs r' _ y m' _).symm)))
  refine Eq.symm ((toStk_valF_gs r _ y (mem_wchart.2 fun _ => m₂) _).trans ?_)
  rw [← e₁]
  exact (gs_pullOver (isPullback_groupBase F).w (fun _ => rfl) (genericSec U k (σ i)) r y (fun _ => l)
      (fun _ => m₂)).trans (gs_pullOver (p := pullback.fst G.hom (jK R)) pullback.condition
        (fun _ => (Category.comp_id _).symm) (σ i) _ y (fun _ => l) (fun _ => m₂))

end

theorem exists_carry : LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (k : ℕ) (J : Type) (σ : J → (u.H k).Sec) (f : J → ∀ α, u.D.toPre.SecB k α), (∀ i e, u.U.toUnifPre.ExpandsAt e k (σ i) (f i)) → (∀ i, ∃ s : Fam u.D.toPre (FractionRing u.V) k, FamOf u.D.toPre _ (f i) s) → ∀ w₀ : W0 u.U.toUnifPre, w₀.IsGen → ∃ (t : J → SecA u.A (PadicAlgCl p) k) (s : J → Fam u.D.toPre (PadicAlgCl p) k), (∀ i, u.U.toUnifPre.ExpandsF (PadicAlgCl p) k w₀ (t i) (s i)) ∧ (∀ i α, (∀ j, (f i α).f j = 0) → ∀ j, ((s i).s α).f j = 0) ∧ ∀ (a : u.PtC) (v : J → PadicAlgCl p), Crd (u.H k) σ (u.toG a) v → Crd (LPow u.A.A u.A.L (k : ℤ) (TFK (R := u.V) (PadicAlgCl p))) t (show Sp (PadicAlgCl p) ⟶ _ from (ptSecT u.A.A (a ≫ u.U.gen.hom)).left) v := by
  intro hL o Ω _ _ _ _ S ρ p _ y₀ u k J σ f hE hf w₀ hw₀
  have hs : ∀ i, ∃ s : Fam u.D.toPre (PadicAlgCl p) k, FamOf u.D.toPre _ (f i) s := fun i => by
    obtain ⟨s, hs⟩ := hf i
    exact GlobalTheory.FamBaseChange.main hL.1.globalFns u.V _ u.D k s (f i) hs (PadicAlgCl p)
  choose s hs using hs
  choose t ht using fun i => exists_carries u.U.toUnifPre (PadicAlgCl p) k w₀ hw₀
    (extendSec u.U.toUnifPre (PadicAlgCl p) k (genericSec u.U.toUnifPre k (σ i)))
  exact ⟨t, s, fun i => ⟨_, ht i, expandsG_extend _ _ k (σ i) (f i) (hE i) (s i) (hs i)⟩,
    fun i α h j => famOf_zero _ k (f i) (s i) (hs i) α h j,
    fun a v h => crd_carries u.U.toUnifPre _ k w₀ σ t ht a v h⟩

end GlobalTheory.ZH.IntegralCarry
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGenericSectionsFromIntegralModelStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
open GlobalTheory.UT GlobalTheory.ZH.ClassWeight
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generic_sections_from_integral_model : LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (k : ℕ) (J : Type) (σ : J → (u.H k).Sec) (f : J → ∀ α, u.D.toPre.SecB k α), (∀ i e, u.U.toUnifPre.ExpandsAt e k (σ i) (f i)) → (∀ i, ∃ s : Fam u.D.toPre (FractionRing u.V) k, FamOf u.D.toPre _ (f i) s) → ∀ w₀ : W0 u.U.toUnifPre, w₀.IsGen → ∃ (t : J → SecA u.A (PadicAlgCl p) k) (s : J → Fam u.D.toPre (PadicAlgCl p) k), (∀ i, u.U.toUnifPre.ExpandsF (PadicAlgCl p) k w₀ (t i) (s i)) ∧ (∀ i α, (∀ j, (f i α).f j = 0) → ∀ j, ((s i).s α).f j = 0) ∧ ∀ (a : u.PtC) (v : J → PadicAlgCl p), Crd (u.H k) σ (u.toG a) v → Crd (LPow u.A.A u.A.L (k : ℤ) (TFK (R := u.V) (PadicAlgCl p))) t (show Sp (PadicAlgCl p) ⟶ _ from (ptSecT u.A.A (a ≫ u.U.gen.hom)).left) v := by
  first | exact @GlobalTheory.ZH.IntegralCarry.exists_carry | exact GlobalTheory.ZH.IntegralCarry.exists_carry | (intros; apply GlobalTheory.ZH.IntegralCarry.exists_carry <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AdaptedBasisRowsHaveClassWeight
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.ClassWeight
open GlobalTheory.UT

theorem proj_mulVec {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) {T : AddSubgroup S.Gam}
    (hT : S.IsoFree T) (c : T →+ ZMod S.N) {K : Type} [CommRing K] (y : o →+* K) (v : S.J → K)
    (h : ∀ t : T, ((S.ρ t).map y).mulVec v = y S.ζN ^ (c t).val • v) : ((S.proj T c).map y).mulVec v = v := by
  have hN := S.N_ge
  have hr := S.r_pos
  have : NeZero S.N := ⟨by omega⟩
  have : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  have := Fintype.ofFinite T
  obtain ⟨d, ⟨e⟩⟩ := hT.2
  have hu : IsUnit (Nat.card T : o) := by
    rw [Nat.card_congr e.toEquiv, Nat.card_fun, Nat.card_zmod, Nat.cast_pow]
    exact S.unit.pow _
  have hζ : S.ζN ^ S.N = 1 := (S.prim.pow (pow_pos (NeZero.pos _) 2) (by ring) : IsPrimitiveRoot S.ζN S.N).pow_eq_one
  have h1 : ∀ a : ZMod S.N, S.ζN ^ (-a).val * S.ζN ^ a.val = 1 := fun a => by
    have := (AddChar.zmodChar S.N hζ).map_add_eq_mul (-a) a
    rw [neg_add_cancel, AddChar.map_zero_eq_one] at this
    exact this.symm
  let φ : Matrix S.J S.J o →+ (S.J → K) :=
    { toFun := fun M => (M.map y).mulVec v
      map_zero' := by simp
      map_add' := fun M M' => by rw [Matrix.map_add _ (map_add y), Matrix.add_mulVec] }
  have hφ : ∀ (a : o) M, φ (a • M) = y a • φ M := fun a M => by
    funext i
    simp [φ, Matrix.mulVec, dotProduct, Finset.mul_sum, _root_.mul_assoc]
  show φ _ = v
  set_option synthInstance.maxHeartbeats 100000 in
    rw [ThetaSys.proj, finsum_eq_sum_of_fintype, hφ, map_sum]
  have h2 : ∀ t : T, φ (S.ζN ^ (-(c t)).val • S.ρ t) = v := fun t => by
    rw [hφ]
    refine (congrArg _ (h t)).trans ?_
    rw [smul_smul, ← map_pow, ← map_mul, h1, map_one, one_smul]
  simp only [h2, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul K, smul_smul, ← map_natCast y, ← map_mul, ← Nat.card_eq_fintype_card,
    Ring.inverse_mul_cancel _ hu, map_one, one_smul]

theorem mulVec_eq_of_eigen {K B M J : Type} [CommRing K] [CommRing B] [AddCommGroup M] [Module B M] [Fintype J]
    (κ : K →+* B) (hκ : Function.Injective κ) (E : M →ₗ[B] M) {s : J → M} (hs : LinearIndependent B s)
    (m : Matrix J J K) (h₁ : ∀ j, E (s j) = ∑ l, κ (m l j) • s l) {t : M} {z c : K} (h₂ : E t = κ z • t)
    {v : J → K} (h₃ : ∑ j, κ (v j) • s j = κ c • t) : m.mulVec v = z • v := by
  have h₄ := congrArg E h₃
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_smul, h₂, smul_comm, ← h₃, map_sum] at h₄
  simp only [map_smul, h₁, Finset.smul_sum, smul_smul] at h₄
  rw [Finset.sum_comm] at h₄
  simp only [← Finset.sum_smul] at h₄
  funext l
  apply hκ
  have h₅ := Fintype.linearIndependent_iffₛ.1 hs _ _ h₄ l
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Pi.smul_apply, smul_eq_mul]
  rw [← h₅]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

section
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorusExt GlobalTheory.FieldBaseChange
attribute [local instance] gtGroup
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I} {F : Type} [Field F]
  [Algebra (FractionRing R) F]

theorem isTor_nsmul {τ : Multiplicative D.toPre.X →* Fˣ} {g : GtPtF D.toPre F} (h : IsTor τ g) (n : ℕ) :
    IsTor (τ ^ n) (n • g) := by
  rw [isTor_iff, isTorusPtF_iff_eq] at h ⊢
  rw [h, ← map_nsmul]
  rfl

theorem exists_qkPt_tor {τ : Multiplicative D.toPre.X →* Fˣ} {g : GtPtF D.toPre F} (h : IsTor τ g) {n : ℕ}
    (hn : τ ^ n = 1) : ∃ q : QkPt D.toPre F n, q.y = 0 ∧ q.g = g := by
  refine ⟨⟨0, g, n • g, (isNsmul_iff_eq _ _ _).2 rfl, ?_⟩, rfl, rfl⟩
  have ht := isTor_nsmul h n
  rw [hn, isTor_iff, isTorusPtF_iff_eq] at ht
  have hz : (n • g).IsZero := (isZero_iff_eq _).2 (by simpa using ht)
  obtain ⟨hb, hv⟩ := (isZero_iff _).1 hz
  refine (isIota_iff 0 _).2 ⟨hb.trans (cPoint_zero _).symm, fun χ y J hJ => ?_⟩
  have face : ∀ x z, th D.toPre (T := TF (R := R) F) y J 1 x z = 1 := by
    intro x z
    have e := val_corr hJ (D.toPre.cub.face 0) (lift x z).left
    rw [val_one] at e
    refine Eq.trans ?_ e
    refine Eq.trans ?_ (val_cub D.toPre.cub (lift x z) hJ (pzero _ _) (x2 _ 0) (x2 _ 1)).symm
    congr 1 <;> simp [x2, pzero, Hom.one_def]
  have t := tau_mul (𝟙 (TF (R := R) F)) hJ D.tau_bimult 0 0 χ
  rw [add_zero, cPoint_zero, face, _root_.mul_one] at t
  exact (hv χ y J hJ).trans (mul_eq_left.1 t.symm).symm

variable [CharZero R] [IsAlgClosed F] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem act_of_class (hL : LL) (hA : AdmBase R I) (hG : IsSemiAbelian G) (U : Unif I D A G) {N : ℕ} (hN : Odd N)
    (q : QkPt D.toPre F N) {τ : Multiplicative D.toPre.X →* Fˣ} (hy : q.y = 0) (hτ : IsTor τ q.g) (hτN : τ ^ N = 1)
    {x : TFK (R := R) F ⟶ A.A} (hx : QkToAkU U.toUnifPre F N q x)
    {θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F)} (hθ : SymLift A.A A.L N N x θ) {w₀ : W0 U.toUnifPre}
    (hw₀ : w₀.IsGen) {t t' : SecA A F N} {s : Fam D.toPre F N} (hs : U.ExpandsF F N w₀ t s) (c : D.toPre.X)
    (hc : ∀ α, (∀ m, α ≠ c + N • m) → ∀ j, (s.s α).f j = 0) (ha : IsActOf A.A A.L N θ t t') :
    SecM.ofSec A.A t' = kf R F (τ (Multiplicative.ofAdd c)).val • SecM.ofSec A.A t := by
  obtain ⟨w, hw⟩ := (GlobalTheory.UT.SymFrame.main hL R I hA D F N hN q).1
  obtain ⟨e, he⟩ := GlobalTheory.exists_linearEquiv_expandsF hL.1.globalFns U F hN.pos w₀ hw₀
  have hΦ := GlobalTheory.T.symmetricLift_oddOrder_acts_as_expansionOperator hL R I hA D A G hG U F N hN q x hx θ hθ w₀ hw₀ w hw t t' s (e t') hs ((he _ _).2 rfl) ha
  have h₁ := ((TorusWeight.torus_weight hL R I hA D A G hG U F N hN q τ hy hτ w hw).2 _ _).1 hΦ
  have h₂ : e t' = (τ (Multiplicative.ofAdd c)).val • s := fam_ext fun α j => by
    refine (h₁ α j).trans ?_
    by_cases h : ∃ m, α = c + N • m
    · obtain ⟨m, rfl⟩ := h
      have : τ (Multiplicative.ofAdd (c + N • m)) = τ (Multiplicative.ofAdd c) := by
        rw [ofAdd_add, map_mul, ofAdd_nsmul, map_pow, ← MonoidHom.pow_apply, hτN, MonoidHom.one_apply, _root_.mul_one]
      rw [this]
      rfl
    · have h0 := hc α (fun m hm => h ⟨m, hm⟩) j
      rw [DVR.smul_f, h0, mul_zero, mul_zero]
  have h₃ := e.injective (h₂.trans ((congrArg _ ((he _ _).1 hs).symm).trans (e.map_smul _ _).symm))
  exact Subtype.ext (funext fun j => congrArg (fun z : LB.Sec _ => z.f j) h₃)
end

theorem exists_torus_point (hL : LL) (hT : UTorsSt) {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω]
    {S : ThetaSys o Ω} {ρ : S.Real} {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} {u : ρ.UTest p y₀} (l : u.Lab)
    (a : S.perp l.yy.ker) : ∃ (q : QkPt u.D.toPre (PadicAlgCl p) S.N) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)
      (τ : Multiplicative u.D.toPre.X →* (PadicAlgCl p)ˣ), q.y = 0 ∧ IsTor τ q.g ∧ τ ^ S.N = 1 ∧
      QkToAkU u.U.toUnifPre (PadicAlgCl p) S.N q x ∧ x.left ≫ u.φ = spMap y₀ ≫ (ρ.pt (S.r • a.1)).left ∧
      ∀ α, (τ (Multiplicative.ofAdd α)).val = y₀ (algebraMap o S.R S.ζN) ^ (l.wt α a).val := by
  have : CharZero u.V :=
    ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V))).charZero
  have hA : AdmBase u.V (IsLocalRing.maximalIdeal u.V) := ⟨inferInstance, inferInstance, inferInstance, u.complete⟩
  have hr := S.r_pos
  have hN₂ := S.N_ge
  have : NeZero S.N := ⟨by omega⟩
  have : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  obtain ⟨x, hx, hadd, -, honto⟩ := GlobalTheory.T.uniformised_model_labelled_torsion_points o Ω S ρ p y₀ u
  let y : o →+* PadicAlgCl p := y₀.comp (algebraMap o S.R)
  obtain ⟨pk, τ, hy, hτ, hq, hval⟩ := GlobalTheory.T.exists_torus_torsionPoint_standardAlternatingForm hL hT o Ω S ρ p y₀ u l x hx hadd honto a.1 a.2
  have hζ : y S.ζN ^ S.N = 1 := by
    have h : IsPrimitiveRoot S.ζN S.N := S.prim.pow (pow_pos (NeZero.pos _) 2) (by ring)
    rw [← map_pow, h.pow_eq_one, map_one]
  have hwt : ∀ α, ((τ ^ S.r) (Multiplicative.ofAdd α)).val = y S.ζN ^ (l.wt α a).val := fun α => by
    obtain ⟨a', ha'⟩ := l.yy_onto (QuotientAddGroup.mk α)
    rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val, hval a' α ha', l.wt_eq a' α ha' a, ZMod.castHom_apply,
      ZMod.cast_eq_val, ZMod.val_natCast, ← pow_eq_pow_mod _ hζ, ← map_pow y, ThetaSys.ζN, ← pow_mul]
    refine (map_pow y _ _).symm.trans (congrArg y ?_)
    rw [← pow_mul]
    congr 1
    ring
  have hτN : (τ ^ S.r) ^ S.N = 1 := MonoidHom.ext fun α => Units.ext (by
    rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val, ← ofAdd_toAdd α, hwt, ← pow_mul, mul_comm, pow_mul, hζ, one_pow]
    rfl)
  let _ := TorusExt.gtGroup u.D.toPre (PadicAlgCl p)
  have hτ' := isTor_nsmul hτ S.r
  obtain ⟨q, hq₀, hq₁⟩ := exists_qkPt_tor hτ' hτN
  have hxr : x a ^ S.r = x (S.r • a) := by
    have h0 : x 0 = 1 := by
      have := hadd 0 0
      rw [add_zero] at this
      exact left_eq_mul.1 this
    exact (map_pow (⟨⟨fun z => x z.toAdd, h0⟩, fun z z' => hadd _ _⟩ : Multiplicative S.Gam →* _)
      (Multiplicative.ofAdd a.1) S.r).symm
  have hq' := (GlobalTheory.T.uniformisation_torsion_maps_compatible_in_level hL u.V _ hA u.D u.A u.G u.semi u.U (PadicAlgCl p) S.N S.r (S.r * S.N) (by omega) hr
    (mul_comm _ _) q pk (x a)).2 (hq₀.trans hy.symm) ((TorusExt.isNsmul_iff_eq _ _ _).2 hq₁) hq
  rw [hxr] at hq'
  exact ⟨q, _, _, hq₀, hq₁ ▸ hτ', hτN, hq', hx _, hwt⟩

theorem row_weight : GlobalTheory.UT.LL → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (σ : S.J → (u.H S.N).Sec) (cls : S.J → u.D.toPre.X) (f : S.J → ∀ α, u.D.toPre.SecB S.N α), u.Basis l S.N σ cls f → ∀ b : Matrix S.J S.J (FractionRing u.V), u.Link σ b → ∀ i, ((S.proj _ (l.wt (cls i))).map fun a => y₀ (algebraMap o S.R a)).mulVec (b.map (algebraMap _ (PadicAlgCl p)) i) = b.map (algebraMap _ (PadicAlgCl p)) i := by
  intro hL hT o Ω _ _ _ _ S ρ p _ y₀ u l σ cls f hB b hb i
  have : CharZero u.V :=
    ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V))).charZero
  have hA : AdmBase u.V (IsLocalRing.maximalIdeal u.V) := ⟨inferInstance, inferInstance, inferInstance, u.complete⟩
  have hodd : Odd S.N := by rw [ρ.N_eq]; exact ρ.n_odd.pow.pow
  have hN₄ : 4 ≤ S.N := by
    have h₁ : 2 ≤ ρ.n ^ ρ.k := ρ.n_prime.two_le.trans (Nat.le_self_pow (by have := ρ.two_le; omega) _)
    rw [ρ.N_eq]
    exact Nat.pow_le_pow_left h₁ 2
  obtain ⟨w, hw⟩ := u.lb
  obtain ⟨w₀, hw₀⟩ := u.U.toUnifPre.ext
  choose s hs using fun j => exists_moved u hw (ρ.s j)
  obtain ⟨t, e, ht, he, hcrd⟩ := GlobalTheory.T.exists_generic_sections_from_integral_model hL o Ω S ρ p y₀ u S.N S.J σ f hB.2.2.2.1 hB.2.2.2.2.1 w₀ hw₀
  obtain ⟨c, hc⟩ := GlobalTheory.T.abelianSections_proportional_of_coordinates hL.1.globalFns u.V u.A (PadicAlgCl p) S.N S.J S.J t s
    (b.map (algebraMap _ (PadicAlgCl p))) fun z => by
      obtain ⟨a, rfl⟩ : ∃ a : u.PtC, z = a ≫ u.U.gen.hom := ⟨z ≫ u.U.gen.inv, by simp⟩
      obtain ⟨v, hv⟩ := ((CrdCalc.crd_calculus _ (LPow u.A.A u.A.L (S.N : ℤ) (TFK (R := u.V) (PadicAlgCl p))) _ s
        (DVR.linComb_isLB _ u.A.isLB _ _)).1 (PadicAlgCl p) (ptSecT u.A.A (a ≫ u.U.gen.hom)).left).1
      have h₁ := hb a v (GlobalTheory.T.homogeneousCoordinates_of_geometricFibre o Ω S ρ p y₀ u w hw s hs a v hv)
      exact ⟨v, (GlobalTheory.T.crd_ne_zero_injective_surjective_of_basis hL o Ω S ρ p y₀ u l S.N hN₄ S.J σ cls f hB).1 a _ h₁, hv, hcrd a _ h₁⟩
  let y : o →+* PadicAlgCl p := y₀.comp (algebraMap o S.R)
  refine proj_mulVec S l.isoFree _ y _ fun a => ?_
  obtain ⟨q, x, τ, hq₀, hτ, hτN, hq, hx, hwt⟩ := exists_torus_point hL hT l a
  obtain ⟨θ, hθ, hact⟩ := GlobalTheory.T.exists_symmetricLift_action_geometricFibre o Ω S ρ p y₀ u w hw s hs a.1 _ hx (hq w₀ hw₀).1
  obtain ⟨E, hE, -⟩ := GlobalTheory.thetaGrp_acts_linearly hL.1.globalFns _ u.A (S.N : ℤ) (TFK (R := u.V) (PadicAlgCl p))
  have h₁ : ∀ j, E θ (SecM.ofSec u.A.A (s j)) =
      ∑ m, kf u.V (PadicAlgCl p) (y (S.ρ a m j)) • SecM.ofSec u.A.A (s m) := fun j =>
    hact j (SecM.toSec u.A.A (E θ (SecM.ofSec u.A.A (s j)))) ((hE _ _ _).2 rfl)
  have h₂ : E θ (SecM.ofSec u.A.A (t i)) =
      kf u.V (PadicAlgCl p) (y S.ζN ^ (l.wt (cls i) a).val) • SecM.ofSec u.A.A (t i) := by
    have h₃ := act_of_class hL hA u.semi u.U hodd q hq₀ hτ hτN hq hθ hw₀ (ht i) (cls i)
      (fun α hα => he i α (hB.2.2.2.2.2.1 i α hα)) (t' := SecM.toSec u.A.A (E θ (SecM.ofSec u.A.A (t i))))
      ((hE _ _ _).2 rfl)
    exact h₃.trans (congrArg (fun z => kf u.V (PadicAlgCl p) z • SecM.ofSec u.A.A (t i)) (hwt (cls i)))
  exact mulVec_eq_of_eigen (kf u.V (PadicAlgCl p)) (kf_bijective _ _).1 (E θ).toLinearMap
    (GlobalTheory.T.linearIndependent_thetaBasis_geometric_fibre hL o Ω S ρ p y₀ u w hw s hs) ((S.ρ a).map y) h₁ h₂ (hc i)

end GlobalTheory.ZH.ClassWeight
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AdaptedBasisRowsHaveClassWeightStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adaptedBasis_rows_have_class_weight : GlobalTheory.UT.LL → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (σ : S.J → (u.H S.N).Sec) (cls : S.J → u.D.toPre.X) (f : S.J → ∀ α, u.D.toPre.SecB S.N α), u.Basis l S.N σ cls f → ∀ b : Matrix S.J S.J (FractionRing u.V), u.Link σ b → ∀ i, ((S.proj _ (l.wt (cls i))).map fun a => y₀ (algebraMap o S.R a)).mulVec (b.map (algebraMap _ (PadicAlgCl p)) i) = b.map (algebraMap _ (PadicAlgCl p)) i := by
  first | exact @GlobalTheory.ZH.ClassWeight.row_weight | exact GlobalTheory.ZH.ClassWeight.row_weight | (intros; apply GlobalTheory.ZH.ClassWeight.row_weight <;> assumption)
end
