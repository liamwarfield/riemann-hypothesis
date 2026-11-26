module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyRestrictBasisExtendedBijective
public import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppTopBijectiveAndSurjectiveNormalDomain
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeDivisorEtalePullbackOrders

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionTowerPresentationCotangentPullbackResRigi
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionTowerPresentationCotangentPullbackResRigi
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt.OmRes

variable {R : Type} [CommRing R]

theorem val_map_coc {X : Scheme.{0}} {s : X ⟶ Sp R} (E E' : SqExt R) (φ : E.C →ₐ[R] E'.C) (φ₀ : E.B →ₐ[R] E'.B)
    (hπ : ∀ c, φ₀ (E.π c) = E'.π (φ c))
    (hi : ∀ b, φ (E.i b) = E'.i (φ₀ b)) (y : Sp E.C ⟶ X) (hy : y ≫ s = spMap (algebraMap R E.C))
    (y' : Sp E'.C ⟶ X) (hy' : y' ≫ s = spMap (algebraMap R E'.C))
    (a : Thick.triv E.C y hy ⟶ Thick.triv E'.C y' hy') (ha : ∀ c, a.φ c = φ c)
    (e : spMap (φ : E.C →+* E'.C) ≫ y = y') (f : Z1 (O (dp0 R) s)) :
    ∃ b : E'.B, E'.val y' hy' f = φ (E.val y hy f) + (ev f a : E'.C) - E'.i b := by
  have e₀ : spMap (φ₀ : E.B →+* E'.B) ≫ spMap (E.π : E.C →+* E.B) ≫ y =
      spMap (E'.π : E'.C →+* E'.B) ≫ y' := by
    rw [← e, ← Category.assoc, ← Category.assoc, ← spMap_comp, ← spMap_comp]
    congr 2
    exact RingHom.ext hπ
  let Φ := E.thickHom E' φ φ₀ hπ (E.red_w hy) (E'.red_w hy') e₀
  let b : Thick.triv E.B _ (E.red_w hy) ⟶ Thick.triv E'.B _ (E'.red_w hy') := Thick.trivHom φ₀ e₀
  have k1 := ev_sq f a (E'.idHom hy') (E.idHom hy) Φ ha
  have k2 := ev_sq f b (E'.secHom (E'.red_w hy') E'.i E'.π_i) (E.secHom (E.red_w hy) E.i E.π_i)
    Φ fun c ↦ (hi c).symm
  refine ⟨ev f b, ?_⟩
  rw [SqExt.val_apply, SqExt.val_apply, map_sub]
  have k1' : (ev f a : E'.C) + (ev f (E'.idHom hy') : E'.C) = φ (ev f (E.idHom hy)) + (ev f Φ : E'.C) := k1
  have k2' : E'.i (ev f b) + (ev f (E'.secHom (E'.red_w hy') E'.i E'.π_i) : E'.C) =
    φ (ev f (E.secHom (E.red_w hy) E.i E.π_i)) + (ev f Φ : E'.C) := k2
  linear_combination k2' - k1'

attribute [local instance] cotOp cotCentral cotTower

variable {D D' : Type} [CommRing D] [Bialgebra R D] [CommRing D'] [Bialgebra R D']

def rho (φ : D →ₐc[R] D') : (cotExt R D).C →ₐ[R] (cotExt R D').C := TrivSqZeroExt.map (cotMap φ)

theorem cotSnd_cotPt (a : D) : cotSnd R D (cotPt R D a) = dUnit (R := R) a := by
  simp [cotSnd, cotPt, TrivSqZeroExt.algebraMap_eq_inl, dUnit]

theorem cotSnd_rho (φ : D →ₐc[R] D') (c : (cotExt R D).C) : cotSnd R D' (rho φ c) = cotMap φ (cotSnd R D c) :=
  TrivSqZeroExt.snd_map _ _

theorem rho_cotPt (φ : D →ₐc[R] D') (a : D) : rho φ (cotPt R D a) = cotPt R D' (φ a) := by
  refine TrivSqZeroExt.ext ?_ ?_
  · refine (TrivSqZeroExt.fst_map _ _).trans ?_
    simp [cotPt, TrivSqZeroExt.algebraMap_eq_inl]
  · exact (cotSnd_rho φ _).trans (by rw [cotSnd_cotPt, cotMap_d]; exact (cotSnd_cotPt _).symm)

theorem cotVal_map {X : Over (Sp R)} (f : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))) (φ : D →ₐc[R] D') (y : Pt X D) :
    cotVal f (spOver (φ : D →ₐ[R] D') ≫ y) =
      cotMap φ (cotVal f y) + dUnit (R := R) (fv f D D' (φ : D →ₐ[R] D') y) := by
  let z : Pt X (cotExt R D).C := spOver (cotPt R D) ≫ y
  let z' : Pt X (cotExt R D').C := spOver (cotPt R D') ≫ spOver (φ : D →ₐ[R] D') ≫ y
  have e : spMap (rho φ : (cotExt R D).C →+* (cotExt R D').C) ≫ z.left = z'.left := by
    change spMap _ ≫ spMap _ ≫ y.left = spMap _ ≫ spMap _ ≫ y.left
    rw [← Category.assoc, ← Category.assoc, ← spMap_comp, ← spMap_comp]
    congr 2
    exact RingHom.ext (rho_cotPt φ)
  let a : trivAt z ⟶ trivAt z' := Thick.trivHom (rho φ) e
  obtain ⟨b, hb⟩ := val_map_coc (cotExt R D) (cotExt R D') (rho φ) (AlgHom.id R R)
    (fun c ↦ (TrivSqZeroExt.fst_map _ _).symm) (fun r ↦ TrivSqZeroExt.map_inl _ _) z.left z.w z'.left z'.w a
    (fun _ ↦ rfl) e f
  have k : rho φ (fv f D _ (cotPt R D) y) + (ev f a : (cotExt R D').C) =
      cotPt R D' (fv f D D' (φ : D →ₐ[R] D') y) + fv f D' _ (cotPt R D') (spOver (φ : D →ₐ[R] D') ≫ y) :=
    ev_sq f (trivMap (cotPt R D) y) a (trivMap (φ : D →ₐ[R] D') y) (trivMap (cotPt R D') _) (rho_cotPt φ)
  have h0 : cotSnd R D' ((cotExt R D').i b) = 0 := rfl
  change cotSnd R D' ((cotExt R D').val z'.left z'.w f - _) =
    cotMap φ (cotSnd R D ((cotExt R D).val z.left z.w f - _)) + _
  rw [← cotSnd_rho, ← cotSnd_cotPt, ← map_add (f := _), ← sub_zero (cotSnd R D' (_ + _)), ← h0, ← map_sub, hb, map_sub (rho φ)]
  congr 1
  linear_combination k

theorem cotMap_res_om (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R)
    (t : G.TorsionTower A) (c : primDR A) (d : Dat t c) (n : ℕ) :
    cotMap (G.res n) (d.om (n + 1)) = d.om n := by
  have h := cotVal_map d.f (G.res n) (t.y (n + 1))
  rw [t.res n, d.res n] at h
  rw [Dat.om, Dat.om, h, map_sub, cotMap_d]
  simp only [dUnit, map_sub]
  abel

end GlobalTheory.PtExt.OmRes
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionTowerPresentationCotangentPullbackResRigiStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionTowerPresentation_cotangentPullback_res_rigidification : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R) (t : G.TorsionTower A) (c : primDR A) (d : Dat t c) (n : ℕ), cotMap (G.res n) (d.om (n + 1)) = d.om n := by
  first | exact @GlobalTheory.PtExt.OmRes.cotMap_res_om | exact GlobalTheory.PtExt.OmRes.cotMap_res_om | (intros; apply GlobalTheory.PtExt.OmRes.cotMap_res_om <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPairRestrictBaseChangeBijective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPairRestrictBaseChangeBijective
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs.PairExt

variable {X X' Y : Scheme.{0}}

theorem pair_point (φ : X' ⟶ X) (x : X') (U : X'.Opens) (hx : x ∈ U) :
    ∃ t : (Pair φ)ᵒᵖ, x ∈ ((pairFst φ).obj t).unop.1 ∧ ((pairFst φ).obj t).unop.1 ≤ U := by
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (x := φ.base x) (U := (⊤ : X.Opens)) trivial
  obtain ⟨W, hW, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := U ⊓ φ ⁻¹ᵁ V) ⟨hx, hxV⟩
  exact ⟨Opposite.op ⟨(⟨W, hW⟩, ⟨V, hV⟩), fun y hy ↦ (hWU hy).2⟩, hxW, fun y hy ↦ (hWU hy).1⟩

theorem pair_point_two (φ : X' ⟶ X) (t₁ t₂ : (Pair φ)ᵒᵖ) (x : X') (U : X'.Opens) (hx : x ∈ U)
    (h₁ : x ∈ ((pairFst φ).obj t₁).unop.1) (h₂ : x ∈ ((pairFst φ).obj t₂).unop.1) :
    ∃ t₃ : (Pair φ)ᵒᵖ, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ x ∈ ((pairFst φ).obj t₃).unop.1 ∧
      ((pairFst φ).obj t₃).unop.1 ≤ U := by
  have h₁' : x ∈ t₁.unop.1.1.1 := h₁
  have h₂' : x ∈ t₂.unop.1.1.1 := h₂
  obtain ⟨V, hV, hxV, hVV⟩ := exists_isAffineOpen_mem_and_subset (x := φ.base x)
    (U := t₁.unop.1.2.1 ⊓ t₂.unop.1.2.1) ⟨t₁.unop.2 h₁', t₂.unop.2 h₂'⟩
  obtain ⟨W, hW, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset (x := x)
    (U := U ⊓ φ ⁻¹ᵁ V ⊓ (t₁.unop.1.1.1 ⊓ t₂.unop.1.1.1)) ⟨⟨hx, hxV⟩, h₁', h₂'⟩
  let t₃ : Pair φ := ⟨(⟨W, hW⟩, ⟨V, hV⟩), fun y hy ↦ (hWU hy).1.2⟩
  refine ⟨Opposite.op t₃, ⟨(homOfLE ?_).op⟩, ⟨(homOfLE ?_).op⟩, hxW, fun y hy ↦ (hWU hy).1.1⟩
  · exact ⟨fun y hy ↦ (hWU hy).2.1, fun y hy ↦ (hVV hy).1⟩
  · exact ⟨fun y hy ↦ (hWU hy).2.2, fun y hy ↦ (hVV hy).2⟩

theorem triple_point (φ : X' ⟶ X) (ψ : X ⟶ Y) (x : X') (U : X'.Opens) (hx : x ∈ U) :
    ∃ t : (Triple φ ψ)ᵒᵖ, x ∈ ((cechTripleProjFirstThird φ ψ ⋙ pairFst (φ ≫ ψ)).obj t).unop.1 ∧
      ((cechTripleProjFirstThird φ ψ ⋙ pairFst (φ ≫ ψ)).obj t).unop.1 ≤ U := by
  obtain ⟨Z, hZ, hxZ, -⟩ := exists_isAffineOpen_mem_and_subset (x := ψ.base (φ.base x)) (U := (⊤ : Y.Opens)) trivial
  obtain ⟨V, hV, hxV, hVZ⟩ := exists_isAffineOpen_mem_and_subset (x := φ.base x) (U := ψ ⁻¹ᵁ Z) hxZ
  obtain ⟨W, hW, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := U ⊓ φ ⁻¹ᵁ V) ⟨hx, hxV⟩
  exact ⟨Opposite.op ⟨(⟨W, hW⟩, ⟨V, hV⟩, ⟨Z, hZ⟩), fun y hy ↦ (hWU hy).2, fun y hy ↦ hVZ hy⟩, hxW,
    fun y hy ↦ (hWU hy).1⟩

theorem triple_point_two (φ : X' ⟶ X) (ψ : X ⟶ Y) (t₁ t₂ : (Triple φ ψ)ᵒᵖ) (x : X') (U : X'.Opens) (hx : x ∈ U)
    (h₁ : x ∈ ((cechTripleProjFirstThird φ ψ ⋙ pairFst (φ ≫ ψ)).obj t₁).unop.1)
    (h₂ : x ∈ ((cechTripleProjFirstThird φ ψ ⋙ pairFst (φ ≫ ψ)).obj t₂).unop.1) :
    ∃ t₃ : (Triple φ ψ)ᵒᵖ, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧
      x ∈ ((cechTripleProjFirstThird φ ψ ⋙ pairFst (φ ≫ ψ)).obj t₃).unop.1 ∧
      ((cechTripleProjFirstThird φ ψ ⋙ pairFst (φ ≫ ψ)).obj t₃).unop.1 ≤ U := by
  have h₁' : x ∈ t₁.unop.1.1.1 := h₁
  have h₂' : x ∈ t₂.unop.1.1.1 := h₂
  have hy₁ : φ.base x ∈ t₁.unop.1.2.1.1 := t₁.unop.2.1 h₁'
  have hy₂ : φ.base x ∈ t₂.unop.1.2.1.1 := t₂.unop.2.1 h₂'
  obtain ⟨Z, hZ, hxZ, hZZ⟩ := exists_isAffineOpen_mem_and_subset (x := ψ.base (φ.base x))
    (U := t₁.unop.1.2.2.1 ⊓ t₂.unop.1.2.2.1) ⟨t₁.unop.2.2 hy₁, t₂.unop.2.2 hy₂⟩
  obtain ⟨V, hV, hxV, hVV⟩ := exists_isAffineOpen_mem_and_subset (x := φ.base x)
    (U := t₁.unop.1.2.1.1 ⊓ t₂.unop.1.2.1.1 ⊓ ψ ⁻¹ᵁ Z) ⟨⟨hy₁, hy₂⟩, hxZ⟩
  obtain ⟨W, hW, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset (x := x)
    (U := U ⊓ φ ⁻¹ᵁ V ⊓ (t₁.unop.1.1.1 ⊓ t₂.unop.1.1.1)) ⟨⟨hx, hxV⟩, h₁', h₂'⟩
  let t₃ : Triple φ ψ := ⟨(⟨W, hW⟩, ⟨V, hV⟩, ⟨Z, hZ⟩), fun y hy ↦ (hWU hy).1.2, fun y hy ↦ (hVV hy).2⟩
  refine ⟨Opposite.op t₃, ⟨(homOfLE ?_).op⟩, ⟨(homOfLE ?_).op⟩, hxW, fun y hy ↦ (hWU hy).1.1⟩
  · exact ⟨fun y hy ↦ (hWU hy).2.1, fun y hy ↦ (hVV hy).1.1, fun y hy ↦ (hZZ hy).1⟩
  · exact ⟨fun y hy ↦ (hWU hy).2.2, fun y hy ↦ (hVV hy).1.2, fun y hy ↦ (hZZ hy).2⟩

theorem extHom_of_id {R₀ : Type} [CommRing R₀] (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] {B : Type} [CommRing B]
    [Algebra R₀ B] (f : B →ₐ[R₀] B) (hf : ∀ b, f b = b) (y : R₁ ⊗[R₀] B) : extHom R₁ f y = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [hf]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem cechTripleRestrict_comp_pairRestrict {R₀ : Type} [CommRing R₀] (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (s' : X' ⟶ Sp R₀)
    (φ : X' ⟶ X) (ψ : X ⟶ Y) (c : CatCoh.H1 (ext R₁ (OAff s'))) :
    (extMap R₁ (cechTripleRestrictFirst φ ψ s')).pull1 ((extMap R₁ (pairRes φ s')).pull1 c) =
      (extMap R₁ (CoefMap.restrict (OAff s') (cechTripleProjFirstThird φ ψ ⋙ pairFst (φ ≫ ψ)))).pull1 c := by
  obtain ⟨f, rfl⟩ := H1.mk_surjective _ c
  rw [CoefMap.pullCohomologyOne_class, CoefMap.pullCohomologyOne_class, CoefMap.pullCohomologyOne_class]
  refine congrArg _ (Subtype.ext ?_)
  funext T T' a
  exact extHom_of_id R₁ (coefHom (cechTripleRestrictFirst φ ψ s') T') (fun _ ↦ rfl) _

theorem pairRes_ext_bijective : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (X X' : Scheme.{0}) (s' : X' ⟶ Sp R₀) (φ : X' ⟶ X), (Function.Bijective (extMap R₁ (pairRes φ s')).pull1 ∧ Function.Bijective (extMap R₁ (pairRes φ s')).pull2) ∧ ∀ (Y : Scheme.{0}) (ψ : X ⟶ Y), Function.Injective (extMap R₁ (cechTripleRestrictFirst φ ψ s')).pull1 := by
  intro R₀ R₁ _ _ _ X X' s' φ
  have hp : Function.Bijective (extMap R₁ (pairRes φ s')).pull1 ∧ Function.Bijective (extMap R₁ (pairRes φ s')).pull2 :=
    GlobalTheory.T.cohomology_restrict_basis_extended_bijective R₀ R₁ X' s' _ (pairFst φ) (pair_point φ) (pair_point_two φ)
  refine ⟨hp, fun Y ψ x y e ↦ ?_⟩
  obtain ⟨x0, rfl⟩ := hp.1.2 x
  obtain ⟨y0, rfl⟩ := hp.1.2 y
  rw [cechTripleRestrict_comp_pairRestrict, cechTripleRestrict_comp_pairRestrict] at e
  rw [(GlobalTheory.T.cohomology_restrict_basis_extended_bijective R₀ R₁ X' s' _ _ (triple_point φ ψ) (triple_point_two φ ψ)).1.1 e]

end GlobalTheory.Obs.PairExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPairRestrictBaseChangeBijectiveStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechPairRestrict_baseChange_bijective : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (X X' : Scheme.{0}) (s' : X' ⟶ Sp R₀) (φ : X' ⟶ X), (Function.Bijective (extMap R₁ (pairRes φ s')).pull1 ∧ Function.Bijective (extMap R₁ (pairRes φ s')).pull2) ∧ ∀ (Y : Scheme.{0}) (ψ : X ⟶ Y), Function.Injective (extMap R₁ (cechTripleRestrictFirst φ ψ s')).pull1 := by
  first | exact @GlobalTheory.Obs.PairExt.pairRes_ext_bijective | exact GlobalTheory.Obs.PairExt.pairRes_ext_bijective | (intros; apply GlobalTheory.Obs.PairExt.pairRes_ext_bijective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImmersionSplitTorusIntoTorusExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImmersionSplitTorusIntoTorusExtension
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps (torus lieMap lieAdd LieCongr IsLieLinear lieCoord)

namespace GlobalTheory.TorusFieldCrit

theorem exists_prime_hom_of_not_surjective {X : Type} [AddCommGroup X] {r : ℕ}
    (M : X →+ (Fin r → ℤ)) (hM : ¬ Function.Surjective M) :
    ∃ p : ℕ, p.Prime ∧ ∃ φ : (Fin r → ℤ) →+ ZMod p, φ ≠ 0 ∧ φ.comp M = 0 := by
  obtain ⟨y, hy⟩ := not_forall.1 hM
  have hQ : Nontrivial ((Fin r → ℤ) ⧸ M.range) :=
    ⟨⟨(y : (Fin r → ℤ) ⧸ M.range), 0, fun h => hy ((QuotientAddGroup.eq_zero_iff y).1 h)⟩⟩
  haveI : AddGroup.FG ((Fin r → ℤ) ⧸ M.range) := inferInstance
  obtain ⟨n, κ, _, p, hp, e, ⟨f⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod ((Fin r → ℤ) ⧸ M.range)
  suffices h : ∃ q, q.Prime ∧ ∃ ψ : ((Fin r → ℤ) ⧸ M.range) →+ ZMod q, Function.Surjective ψ by
    obtain ⟨q, hq, ψ, hψ⟩ := h
    haveI := Fact.mk hq
    refine ⟨q, hq, ψ.comp (QuotientAddGroup.mk' M.range), fun h => ?_, ?_⟩
    · obtain ⟨x, hx⟩ := hψ 1
      obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective M.range x
      have := DFunLike.congr_fun h z
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.zero_apply] at this
      rw [this] at hx
      exact zero_ne_one hx
    · ext x
      simp [(QuotientAddGroup.eq_zero_iff _).2 (AddMonoidHom.mem_range.2 ⟨x, rfl⟩)]
  by_cases hn : 0 < n
  · refine ⟨2, Nat.prime_two, ((Int.castAddHom (ZMod 2)).comp
        ((Finsupp.applyAddHom (⟨0, hn⟩ : Fin n)).comp (AddMonoidHom.fst _ _))).comp f.toAddMonoidHom, ?_⟩
    intro z
    obtain ⟨k, rfl⟩ := ZMod.intCast_surjective z
    refine ⟨f.symm (Finsupp.single ⟨0, hn⟩ k, 0), ?_⟩
    simp
  · have hn0 : n = 0 := by omega
    subst hn0
    obtain ⟨i, hi⟩ : ∃ i, e i ≠ 0 := by
      by_contra h
      push_neg at h
      apply not_subsingleton ((Fin r → ℤ) ⧸ M.range)
      refine ⟨fun a b => f.injective ?_⟩
      have key : ∀ x : (Fin 0 →₀ ℤ) × DirectSum κ (fun j ↦ ZMod (p j ^ e j)), x = 0 := fun x => by
        refine Prod.ext (Finsupp.ext fun j => j.elim0) (DFinsupp.ext fun j => ?_)
        haveI : Subsingleton (ZMod (p j ^ e j)) := by rw [h j, pow_zero]; infer_instance
        exact Subsingleton.elim _ _
      rw [key (f a), key (f b)]
    classical
    haveI := Fact.mk (hp i)
    refine ⟨p i, hp i, ((ZMod.castHom (dvd_pow_self (p i) hi) (ZMod (p i))).toAddMonoidHom.comp
      ((DirectSum.component ℤ κ (fun j => ZMod (p j ^ e j)) i).toAddMonoidHom.comp
        (AddMonoidHom.snd _ _))).comp f.toAddMonoidHom, ?_⟩
    intro z
    obtain ⟨k, rfl⟩ := ZMod.intCast_surjective z
    refine ⟨f.symm (0, DirectSum.lof ℤ κ (fun j => ZMod (p j ^ e j)) i (k : ZMod (p i ^ e i))), ?_⟩
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
      AddEquiv.apply_symm_apply, AddMonoidHom.coe_snd, LinearMap.toAddMonoidHom_coe,
      DirectSum.component.lof_self, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, ZMod.castHom_apply]
    exact ZMod.cast_intCast (dvd_pow_self (p i) hi) k

theorem isClosedImmersion_of_torusExtension (Ω : Type) [Field Ω] (H : Over (Spec (CommRingCat.of Ω)))
    [GrpObj H] (E : TorusExtension H) (r : ℕ) (v : splitTorus (Spec (CommRingCat.of Ω)) (Fin r → ℤ) ⟶ H)
    (hv : IsMonHom v)
    (hker : ∀ (p : ℕ), p.Prime → ∀ φ : (Fin r → ℤ) →+ ZMod p, φ ≠ 0 →
      GlobalTheory.SplitTorus.torusMap (Spec (CommRingCat.of Ω)) φ ≫ v ≠ 1) :
    IsClosedImmersion v.left := by
  letI := E.addCommGroup; letI := E.grpB
  haveI := E.free; haveI := E.finite
  haveI := E.i_hom; haveI := E.q_hom; haveI := E.isAbelian.proper
  haveI : ConnectedSpace (Spec (CommRingCat.of Ω)) := GlobalTheory.SplitTorus.connectedSpace_of_isLocalRing Ω
  have h1 : v ≫ E.q = toUnit _ ≫ η[E.B] :=
    GlobalTheory.splitTorus_hom_proper_trivial_local Ω (Fin r → ℤ) E.B (v ≫ E.q) inferInstance
  let w := E.isKernel.lift v (toUnit _) h1
  have hw : w ≫ E.i = v := E.isKernel.lift_fst _ _ _
  have hmono : Mono E.i := ⟨fun a b e => E.isKernel.hom_ext e (toUnit_unique _ _)⟩
  haveI : IsMonHom w := GlobalTheory.Serre.isMonHom_of_mul_comp w fun T x y => by
    rw [← cancel_mono E.i, MonObj.mul_comp (x ≫ w), Category.assoc, Category.assoc, Category.assoc, hw,
      MonObj.mul_comp]
  obtain ⟨M, hM⟩ := GlobalTheory.SplitTorus.exists_eq_torusMap w
  by_cases hs : Function.Surjective M
  · have hdiag : w = GlobalTheory.Diag.diagMap _ M := by
      rw [hM]; symm
      exact (GlobalTheory.SplitTorus.eq_torusMap_iff _ M).2 fun b => GlobalTheory.Diag.diagMap_chi _ M b
    have hη : IsClosedImmersion (η[E.B] : 𝟙_ _ ⟶ E.B).left :=
      GlobalTheory.isClosedImmersion_of_section_of_isSeparated E.B.hom _ (by simpa using Over.w η[E.B])
    have hpb : IsPullback E.i.left (toUnit _ : splitTorus _ E.X ⟶ 𝟙_ _).left E.q.left (η[E.B] : 𝟙_ _ ⟶ E.B).left :=
      E.isKernel.map (Over.forget _)
    have hi : IsClosedImmersion E.i.left :=
      MorphismProperty.of_isPullback (P := @IsClosedImmersion) hpb.flip hη
    have hw' : IsClosedImmersion w.left := hdiag ▸ GlobalTheory.Diag.isClosedImmersion_diagMap _ hs
    rw [← hw, Over.comp_left]
    infer_instance
  · exfalso
    obtain ⟨p, hp, φ, hφ, hφM⟩ := exists_prime_hom_of_not_surjective M hs
    apply hker p hp φ hφ
    rw [← hw, hM, ← Category.assoc, ← GlobalTheory.SplitTorus.torusMap_comp, hφM, GlobalTheory.SplitTorus.torusMap_zero,
      MonObj.one_comp]

end GlobalTheory.TorusFieldCrit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImmersionSplitTorusIntoTorusExtensionStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps (torus lieMap lieAdd LieCongr IsLieLinear lieCoord)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosedImmersion_splitTorus_into_torusExtension : ∀ (Ω : Type) [Field Ω] (H : Over (Spec (CommRingCat.of Ω))) [GrpObj H], TorusExtension H → ∀ (r : ℕ) (v : splitTorus (Spec (CommRingCat.of Ω)) (Fin r → ℤ) ⟶ H), IsMonHom v → (∀ (p : ℕ), p.Prime → ∀ φ : (Fin r → ℤ) →+ ZMod p, φ ≠ 0 → GlobalTheory.SplitTorus.torusMap (Spec (CommRingCat.of Ω)) φ ≫ v ≠ 1) → IsClosedImmersion v.left := by
  first | exact @GlobalTheory.TorusFieldCrit.isClosedImmersion_of_torusExtension | exact GlobalTheory.TorusFieldCrit.isClosedImmersion_of_torusExtension | (intros; apply GlobalTheory.TorusFieldCrit.isClosedImmersion_of_torusExtension <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCellOfLeadingMinors
set_option autoImplicit false

namespace GlobalTheory.ShFam.Cell

open Matrix

variable {R : Type} [CommRing R]

theorem exists_lowInv_mul_upperUni_of_leadingMinors :
    ∀ (n : ℕ) (N : Matrix (Fin n) (Fin n) R),
      (∀ (k : ℕ) (hk : k ≤ n), IsUnit (N.submatrix (Fin.castLE hk) (Fin.castLE hk)).det) →
      ∃ L U : Matrix (Fin n) (Fin n) R, IsLowInv L ∧ (∀ i j, j < i → U i j = 0) ∧ (∀ i, U i i = 1) ∧ N = L * U := by
  intro n
  induction n with
  | zero =>
    intro N _
    exact ⟨1, 1, ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩, fun i => Fin.elim0 i, fun i => Fin.elim0 i,
      by ext i; exact Fin.elim0 i⟩
  | succ n ih =>
    intro N hN
    set P : Matrix (Fin n) (Fin n) R := N.submatrix Fin.castSucc Fin.castSucc with hP
    have hPm : ∀ (k : ℕ) (hk : k ≤ n), IsUnit (P.submatrix (Fin.castLE hk) (Fin.castLE hk)).det := by
      intro k hk
      have e : P.submatrix (Fin.castLE hk) (Fin.castLE hk)
          = N.submatrix (Fin.castLE (hk.trans (Nat.le_succ n))) (Fin.castLE (hk.trans (Nat.le_succ n))) := by
        ext i j; rfl
      rw [e]; exact hN k _
    obtain ⟨L₀, U₀, ⟨hL₀z, hL₀d⟩, hU₀z, hU₀d, hPLU⟩ := ih P hPm
    have hdL₀ : IsUnit L₀.det := by
      rw [Matrix.det_of_isLowerTriangular L₀ (fun i j h => hL₀z i j h)]
      exact Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one (fun i _ => hL₀d i)
    have hdU₀ : IsUnit U₀.det := by
      rw [Matrix.det_of_isUpperTriangular (M := U₀) (fun i j h => hU₀z i j h)]
      simp [hU₀d]
    set q : Fin n → R := fun i => N (Fin.castSucc i) (Fin.last n)
    set r : Fin n → R := fun j => N (Fin.last n) (Fin.castSucc j)
    set u : Fin n → R := L₀⁻¹ *ᵥ q with hu
    set l : Fin n → R := r ᵥ* U₀⁻¹ with hl
    set d : R := N (Fin.last n) (Fin.last n) - l ⬝ᵥ u with hd
    have hq : L₀ *ᵥ u = q := by rw [hu, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdL₀, Matrix.one_mulVec]
    have hr : l ᵥ* U₀ = r := by rw [hl, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hdU₀, Matrix.vecMul_one]
    let L : Matrix (Fin (n+1)) (Fin (n+1)) R := Matrix.of fun i j =>
      Fin.lastCases (Fin.lastCases d l j) (fun i' => Fin.lastCases 0 (fun j' => L₀ i' j') j) i
    let U : Matrix (Fin (n+1)) (Fin (n+1)) R := Matrix.of fun i j =>
      Fin.lastCases (Fin.lastCases 1 (fun _ => 0) j) (fun i' => Fin.lastCases (u i') (fun j' => U₀ i' j') j) i
    have hLz : ∀ i j, i < j → L i j = 0 := by
      intro i j hij
      induction i using Fin.lastCases with
      | last => exact absurd hij (not_lt.2 (Fin.le_last j))
      | cast i' =>
        induction j using Fin.lastCases with
        | last => simp [L]
        | cast j' => simpa [L] using hL₀z i' j' (Fin.castSucc_lt_castSucc_iff.1 hij)
    have hLdiag : ∀ i, L i i = Fin.lastCases d (fun i' => L₀ i' i') i := by
      intro i
      induction i using Fin.lastCases with
      | last => simp [L]
      | cast i' => simp [L]
    have hUz : ∀ i j, j < i → U i j = 0 := by
      intro i j hij
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => exact absurd hij (lt_irrefl _)
        | cast j' => simp [U]
      | cast i' =>
        induction j using Fin.lastCases with
        | last => exact absurd hij (not_lt.2 (Fin.le_last _))
        | cast j' => simpa [U] using hU₀z i' j' (Fin.castSucc_lt_castSucc_iff.1 hij)
    have hUd : ∀ i, U i i = 1 := by
      intro i
      induction i using Fin.lastCases with
      | last => simp [U]
      | cast i' => simpa [U] using hU₀d i'
    have hNLU : N = L * U := by
      ext i j
      rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last =>
          simp only [L, U, Matrix.of_apply, Fin.lastCases_last, Fin.lastCases_castSucc, mul_one]
          rw [hd]; simp [dotProduct]
        | cast j' =>
          simp only [L, U, Matrix.of_apply, Fin.lastCases_last, Fin.lastCases_castSucc, mul_zero, add_zero]
          have := congrFun hr j'
          simpa [vecMul, dotProduct, r] using this.symm
      | cast i' =>
        induction j using Fin.lastCases with
        | last =>
          simp only [L, U, Matrix.of_apply, Fin.lastCases_last, Fin.lastCases_castSucc, mul_one, add_zero]
          have := congrFun hq i'
          simpa [mulVec, dotProduct, q] using this.symm
        | cast j' =>
          simp only [L, U, Matrix.of_apply, Fin.lastCases_last, Fin.lastCases_castSucc, zero_mul, add_zero]
          have := congrFun (congrFun hPLU i') j'
          simpa [hP, Matrix.mul_apply] using this
    have hdet : IsUnit L.det := by
      have h1 : N.det = L.det * U.det := by rw [hNLU, Matrix.det_mul]
      have h2 : U.det = 1 := by
        rw [Matrix.det_of_isUpperTriangular (M := U) (fun i j h => hUz i j h)]; simp [hUd]
      have h3 : N = N.submatrix (Fin.castLE (le_refl (n+1))) (Fin.castLE (le_refl (n+1))) := by
        ext i j; rfl
      have := hN (n+1) le_rfl
      rw [← h3, h1, h2, mul_one] at this
      exact this
    have hdu : IsUnit d := by
      rw [Matrix.det_of_isLowerTriangular L (fun i j h => hLz i j h), Fin.prod_univ_castSucc] at hdet
      have := isUnit_of_mul_isUnit_right hdet
      simpa [hLdiag] using this
    refine ⟨L, U, ⟨hLz, fun i => ?_⟩, hUz, hUd, hNLU⟩
    rw [hLdiag i]
    induction i using Fin.lastCases with
    | last => simpa using hdu
    | cast i' => simpa using hL₀d i'

end GlobalTheory.ShFam.Cell
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormOrderBirationalPullback
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.BirOrd

theorem formOrd_ratPull_of_over : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (s : Y ⟶ X) [IsDominant s], Function.Bijective (functionFieldMap s) → ∀ (E' : DivOver (s ≫ p)) (E : DivOver p), DivOver.Over s E' E → ∀ (n : ℕ) (η : RatForms p n), η ≠ 0 → E'.formOrd (EtaleKlt.ratPull p s n η) = E.formOrd η := by
  intro k _ X Y _ _ p s _ hbij E' E hO n η hη
  set φ := functionFieldMap s with hφdef
  let φe : X.functionField ≃+* Y.functionField := RingEquiv.ofBijective φ hbij
  have hpc : φ.comp (Cartier.constFn p) = Cartier.constFn (s ≫ p) :=
    EtaleKlt.functionFieldMap_comp_constFn p s
  have hcc : (φe.symm : Y.functionField →+* X.functionField).comp (Cartier.constFn (s ≫ p)) =
      Cartier.constFn p := by
    ext a
    rw [← hpc]
    exact φe.symm_apply_apply _

  let Φ' := TopForm.formMap n (φe.symm : Y.functionField →+* X.functionField) hcc
  have hinv : ∀ ξ : RatForms p n, Φ' (EtaleKlt.ratPull p s n ξ) = ξ := by
    intro ξ
    have e0 : (φe.symm : Y.functionField →+* X.functionField).comp φ = RingHom.id _ := by
      ext x
      exact φe.symm_apply_apply x
    refine (TopForm.formMap_formMap φ (φe.symm : Y.functionField →+* X.functionField)
      (RingHom.id _) e0 hpc hcc (RingHom.id_comp _) ξ).trans ?_
    exact TopForm.formMap_of_eq_id _ rfl _ ξ

  let ψ : E.ring →+* E'.ring := φ.restrict E.ring E'.ring fun x hx => (hO x).1 hx
  have hψv : ∀ a, (ψ a : Y.functionField) = φ a := fun _ => rfl
  have hψb : Function.Bijective ψ := by
    refine ⟨fun a b h => Subtype.ext (hbij.1 (by simpa [hψv] using congrArg Subtype.val h)), ?_⟩
    intro y
    obtain ⟨x, hx⟩ := hbij.2 (y : Y.functionField)
    have hxE : x ∈ E.ring := (hO x).2 (hx ▸ y.2)
    exact ⟨⟨x, hxE⟩, Subtype.ext hx⟩
  let eψ : E.ring ≃+* E'.ring := RingEquiv.ofBijective ψ hψb
  let χ : E'.ring →+* E.ring := eψ.symm
  have hc : ψ.comp E.const = E'.const := by
    ext a
    exact RingHom.congr_fun hpc a
  have hc' : χ.comp E'.const = E.const := by
    ext a
    rw [← hc]
    exact congrArg Subtype.val (eψ.symm_apply_apply (E.const a))
  have hχv : ∀ y, ((χ y : E.ring) : X.functionField) = φe.symm (y : Y.functionField) := by
    intro y
    obtain ⟨x, rfl⟩ := eψ.surjective y
    have h1 : χ (eψ x) = x := eψ.symm_apply_apply x
    rw [h1]
    exact (φe.symm_apply_apply (x : X.functionField)).symm

  have hord : ∀ g : X.functionFieldˣ, E'.ord (Units.map φ.toMonoidHom g) = E.ord g := by
    intro g
    obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible E.ring
    exact EtaleDiv.log_ordFrac_map E.ring E'.ring φ ψ hψv ht (ht.map eψ) g.ne_zero
  have hfe : ∀ ω : Forms E.const n, IsFreeGen E.ring ω →
      IsFreeGen E'.ring (TopForm.formMap n ψ hc ω) := fun ω hω =>
    EtaleDiv.isFreeGen_formMap (EtaleDiv.formallyEtale_of_bijective ψ hψb) hc hω
  have hfe' : ∀ ω : Forms E'.const n, IsFreeGen E'.ring ω →
      IsFreeGen E.ring (TopForm.formMap n χ hc' ω) := fun ω hω =>
    EtaleDiv.isFreeGen_formMap (EtaleDiv.formallyEtale_of_bijective χ eψ.symm.bijective) hc' hω
  have hτ : (E'.ring.subtype.comp ψ).comp E.const = Cartier.constFn (s ≫ p) := by
    rw [RingHom.comp_assoc, hc]
    rfl
  have key : ∀ ω : Forms E.const n,
      EtaleKlt.ratPull p s n (E.toRat n ω) = E'.toRat n (TopForm.formMap n ψ hc ω) := by
    intro ω
    have e : φ.comp E.ring.subtype = E'.ring.subtype.comp ψ := by
      ext x
      rfl
    have k1 := TopForm.formMap_formMap (D := n) E.ring.subtype φ _ e rfl hpc hτ ω
    have k2 := TopForm.formMap_formMap (D := n) ψ E'.ring.subtype _ rfl hc rfl hτ ω
    exact k1.trans k2.symm
  have hτ' : (E.ring.subtype.comp χ).comp E'.const = Cartier.constFn p := by
    rw [RingHom.comp_assoc, hc']
    rfl
  have key' : ∀ ω : Forms E'.const n,
      Φ' (E'.toRat n ω) = E.toRat n (TopForm.formMap n χ hc' ω) := by
    intro ω
    have e : (φe.symm : Y.functionField →+* X.functionField).comp E'.ring.subtype =
        E.ring.subtype.comp χ := by
      ext y
      exact (hχv y).symm
    have k1 := TopForm.formMap_formMap (D := n) E'.ring.subtype
      (φe.symm : Y.functionField →+* X.functionField) _ e rfl hcc hτ' ω
    have k2 := TopForm.formMap_formMap (D := n) χ E.ring.subtype _ rfl hc' rfl hτ' ω
    exact k1.trans k2.symm
  have fwd : ∀ a, E.IsFormOrd η a → E'.IsFormOrd (EtaleKlt.ratPull p s n η) a := by
    rintro a ⟨ω, hω, g, hη', hg⟩
    refine ⟨_, hfe ω hω, Units.map φ.toMonoidHom g, ?_, (hord g).trans hg⟩
    rw [hη', map_smulₛₗ, key]
    rfl
  have bwd : ∀ a, E'.IsFormOrd (EtaleKlt.ratPull p s n η) a → E.IsFormOrd η a := by
    rintro a ⟨ω, hω, f, hη', hf⟩
    let g : X.functionFieldˣ := Units.map (φe.symm : Y.functionField →+* X.functionField).toMonoidHom f
    have hgf : Units.map φ.toMonoidHom g = f := by
      ext
      exact φe.apply_symm_apply (f : Y.functionField)
    refine ⟨_, hfe' ω hω, g, ?_, ?_⟩
    · rw [← hinv η, hη', map_smulₛₗ, key']
      rfl
    · rw [← hord g, hgf, hf]
  have hne : EtaleKlt.ratPull p s n η ≠ 0 := by
    intro h0
    apply hη
    rw [← hinv η, h0, map_zero]
  by_cases h : ∃ a, E.IsFormOrd η a
  · obtain ⟨a, ha⟩ := h
    rw [ha.formOrd_eq hη, (fwd a ha).formOrd_eq hne]
  · have h' : ¬ ∃ a, E'.IsFormOrd (EtaleKlt.ratPull p s n η) a :=
      fun ⟨a, ha⟩ => h ⟨a, bwd a ha⟩
    rw [DivOver.formOrd, DivOver.formOrd, dite_eq_right h, dite_eq_right h']

end GlobalTheory.BirOrd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NaturalPointwiseCochainConstOfGlobalSectionsBase
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NaturalPointwiseCochainConstOfGlobalSectionsBase
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt.NatConst

theorem exists_section (Y : Scheme.{0}) {K : Type} (W : K → Y.Opens) (hW : ⨆ i, W i = ⊤)
    (κ : ∀ D : CommRingCat.{0}, (Spec D ⟶ Y) → D)
    (hκ : ∀ (D D' : CommRingCat.{0}) (φ : D ⟶ D') (x : Spec D ⟶ Y), (∃ i, ⊤ ≤ x ⁻¹ᵁ W i) →
      κ D' (Spec.map φ ≫ x) = φ (κ D x)) :
    ∃ s : Γ(Y, ⊤), ∀ (D : CommRingCat.{0}) (x : Spec D ⟶ Y), (∃ i, ⊤ ≤ x ⁻¹ᵁ W i) →
      κ D x = (Scheme.ΓSpecIso D).hom (x.appTop s) := by
  let J : Type := {U : Y.affineOpens // ∃ i, U.1 ≤ W i}
  let U : J → Y.Opens := fun j ↦ j.1.1
  have hsm : ∀ j : J, ∃ i, ⊤ ≤ j.1.2.fromSpec ⁻¹ᵁ W i := fun j ↦ by
    obtain ⟨i, hi⟩ := j.2
    refine ⟨i, ?_⟩
    rw [← j.1.2.fromSpec_preimage_self]
    exact fun _ h ↦ hi h
  have hcov : ∀ y : Y, ∃ j : J, y ∈ U j := fun y ↦ by
    have hy : y ∈ ⨆ i, W i := by rw [hW]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    obtain ⟨V, hV, hyV, hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens hi
    exact ⟨⟨⟨V, hV⟩, i, hle⟩, hyV⟩
  let sf : ∀ j : J, Γ(Y, U j) := fun j ↦ κ _ j.1.2.fromSpec
  have hgerm : ∀ (j : J) (y : Y) (hy : y ∈ U j),
      Y.presheaf.germ (U j) y hy (sf j) = κ _ (Y.fromSpecStalk y) := fun j y hy ↦ by
    rw [← j.1.2.fromSpecStalk_eq_fromSpecStalk hy]
    exact (hκ _ _ _ _ (hsm j)).symm
  obtain ⟨s, hs, -⟩ := Y.sheaf.existsUnique_gluing' U ⊤ (fun _ ↦ homOfLE le_top)
    (fun y _ ↦ TopologicalSpace.Opens.mem_iSup.2 (hcov y)) sf (fun a b ↦ by
      refine TopCat.Presheaf.section_ext Y.sheaf _ _ _ fun y hy ↦ ?_
      exact ((Y.presheaf.germ_res_apply _ y hy _).trans (hgerm a y hy.1)).trans
        ((Y.presheaf.germ_res_apply _ y hy _).trans (hgerm b y hy.2)).symm)
  have hnat : ∀ (D D' : CommRingCat.{0}) (φ : D ⟶ D') (x : Spec D ⟶ Y),
      (Scheme.ΓSpecIso D').hom ((Spec.map φ ≫ x).appTop s) = φ ((Scheme.ΓSpecIso D).hom (x.appTop s)) := by
    intro D D' φ x
    rw [Scheme.Hom.comp_appTop]
    exact congrArg (fun f ↦ CommRingCat.Hom.hom f (x.appTop s)) (Scheme.ΓSpecIso_naturality φ)
  have hj : ∀ j : J, κ _ j.1.2.fromSpec = (Scheme.ΓSpecIso _).hom (j.1.2.fromSpec.appTop s) := fun j ↦ by
    have h1 : j.1.2.fromSpec.appTop ≫ (Scheme.ΓSpecIso _).hom = Y.presheaf.map (homOfLE le_top).op := by
      have h0 := congrArg (fun q ↦ (Scheme.ΓSpecIso _).inv ≫ Scheme.Hom.appTop q ≫ (Scheme.ΓSpecIso _).hom)
        j.1.2.fromSpec_toSpecΓ
      simp only [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, Scheme.ΓSpecIso_naturality, Category.assoc,
        Iso.inv_hom_id_assoc] at h0
      exact h0
    exact (hs j).symm.trans (congrArg (fun f ↦ CommRingCat.Hom.hom f s) h1).symm
  refine ⟨s, fun D x hx ↦ Module.eq_of_localization_maximal (R := D) (fun P _ ↦ Localization.AtPrime P)
    (fun P _ ↦ Algebra.linearMap D (Localization.AtPrime P)) _ _ fun P hP ↦ ?_⟩
  let φ : D ⟶ CommRingCat.of (Localization.AtPrime P) := CommRingCat.ofHom (algebraMap D _)
  refine (hκ _ _ φ x hx).symm.trans (Eq.trans ?_ (hnat _ _ φ x))
  obtain ⟨j, hy⟩ := hcov ((Spec.map φ ≫ x) (IsLocalRing.closedPoint (CommRingCat.of (Localization.AtPrime P))))
  have htop := Scheme.preimage_eq_top_of_closedPoint_mem _ hy
  have hr : Set.range (Spec.map φ ≫ x) ⊆ Set.range j.1.2.fromSpec := by
    rw [j.1.2.range_fromSpec]
    rintro _ ⟨z, rfl⟩
    have : z ∈ (Spec.map φ ≫ x) ⁻¹ᵁ U j := by rw [htop]; trivial
    exact this
  haveI : IsOpenImmersion j.1.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec (U := j.1.1) j.1.2
  have hf := IsOpenImmersion.lift_fac j.1.2.fromSpec _ hr
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (IsOpenImmersion.lift j.1.2.fromSpec _ hr)
  rw [← hψ] at hf
  rw [← hf]
  exact (hκ _ _ ψ _ (hsm j)).trans ((congrArg ψ (hj j)).trans (hnat _ _ ψ _).symm)

theorem const_of_natural : ∀ (R : Type) [CommRing R] (X : Over (Sp R)) (K : Type) (W : K → X.left.Opens), ⨆ i, W i = ⊤ → Function.Surjective X.hom.appTop.hom → ∀ k : Fn0 X, IsCob W (Fn1.zero X) k → ∃ r : R, ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt X D), Sm W x → k D x = algebraMap R D r := by
  intro R _ X K W hW hs k hk
  let al : ∀ (D : CommRingCat.{0}) (x : Spec D ⟶ X.left), Algebra R D := fun D x ↦
    (Spec.preimage (R := CommRingCat.of R) (x ≫ X.hom)).hom.toAlgebra
  let pt : ∀ (D : CommRingCat.{0}) (x : Spec D ⟶ X.left), @Pt R _ X D _ (al D x) := fun D x ↦ by
    letI : Algebra R D := al D x
    refine Over.homMk (U := SpAlg R D) (V := X) x ?_
    change x ≫ X.hom = Spec.map (Spec.preimage (x ≫ X.hom))
    exact (Spec.map_preimage (x ≫ X.hom)).symm
  let κ : ∀ D : CommRingCat.{0}, (Spec D ⟶ X.left) → D := fun D x ↦ @k D _ (al D x) (pt D x)
  have key : ∀ (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →+* D')
      (x : Pt X D) (x' : Pt X D'), Sm W x → spMap φ ≫ x.left = x'.left → k D' x' = φ (k D x) := by
    intro D _ _ D' _ _ φ x x' hx h
    have h1 : x.left ≫ X.hom = spMap (algebraMap R D) := Over.w x
    have h2 : x'.left ≫ X.hom = spMap (algebraMap R D') := Over.w x'
    have h3 : CommRingCat.ofHom (algebraMap R D) ≫ CommRingCat.ofHom φ = CommRingCat.ofHom (algebraMap R D') := by
      apply Spec.map_injective
      rw [Spec.map_comp]
      change spMap φ ≫ spMap _ = spMap _
      rw [← h1, ← h2, ← h, Category.assoc]
    let ψ : D →ₐ[R] D' := ⟨φ, fun r ↦ congrArg (fun f ↦ CommRingCat.Hom.hom f r) h3⟩
    have h4 := hk D D' ψ x hx
    have h5 : spOver ψ ≫ x = x' := Over.OverMorphism.ext h
    rw [h5] at h4
    exact (sub_eq_zero.1 h4.symm)
  obtain ⟨s, hs'⟩ := exists_section X.left W hW κ fun D D' φ x hx ↦
    @key D _ (al D x) D' _ (al D' (Spec.map φ ≫ x)) φ.hom (pt D x) (pt D' _) hx rfl
  obtain ⟨r, rfl⟩ := hs s
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom r, fun D _ inst x hx ↦ ?_⟩
  have h1 : κ (CommRingCat.of D) x.left = k D x :=
    @key D _ inst D _ (al (CommRingCat.of D) x.left) (RingHom.id D) x (pt (CommRingCat.of D) x.left) hx (by
      change Spec.map (𝟙 _) ≫ _ = _
      rw [Spec.map_id, Category.id_comp]; rfl)
  rw [← h1, hs' (CommRingCat.of D) x.left hx]
  have h2 : x.left ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap R D)) := Over.w x
  have h3 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R D))
  rw [← h2, Scheme.Hom.comp_appTop] at h3
  exact congrArg (fun f ↦ CommRingCat.Hom.hom f r) h3

end GlobalTheory.PtExt.NatConst
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NaturalPointwiseCochainConstOfGlobalSectionsBaseStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.natural_pointwiseCochain_const_of_globalSections_base : ∀ (R : Type) [CommRing R] (X : Over (Sp R)) (K : Type) (W : K → X.left.Opens), ⨆ i, W i = ⊤ → Function.Surjective X.hom.appTop.hom → ∀ k : Fn0 X, IsCob W (Fn1.zero X) k → ∃ r : R, ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt X D), Sm W x → k D x = algebraMap R D r := by
  exact GlobalTheory.PtExt.NatConst.const_of_natural
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackPowersCartesianGroupSquare
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackPowersCartesianGroupSquare
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.PowCart

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} {f : S' ⟶ S} {β : G'.left ⟶ G.left}

theorem square_over_hom_ext (G : Over S) {X : Scheme.{0}} {a b : X ⟶ (G2 G).left}
    (h : ∀ i, a ≫ (x2 G i).left = b ≫ (x2 G i).left) : a = b :=
  pullback.hom_ext (h 0) (h 1)

theorem isPullback_two (hp : IsPullback β G'.hom G.hom f) :
    IsPullback (lift (pushPt hp.w (fst G' G')) (pushPt hp.w (snd G' G'))).left (G2 G').hom (G2 G).hom f := by
  set F2 := (lift (pushPt hp.w (fst G' G')) (pushPt hp.w (snd G' G'))).left with hF2
  have f2 : ∀ i, F2 ≫ (x2 G i).left = (x2 G' i).left ≫ β := fun i => by
    fin_cases i
    · exact congrArg (fun z => z.left) (lift_fst (pushPt hp.w (fst G' G')) (pushPt hp.w (snd G' G')))
    · exact congrArg (fun z => z.left) (lift_snd (pushPt hp.w (fst G' G')) (pushPt hp.w (snd G' G')))
  have w : F2 ≫ (G2 G).hom = (G2 G').hom ≫ f := Over.w (lift (pushPt hp.w (fst G' G')) (pushPt hp.w (snd G' G')))
  have ex : ∀ s : PullbackCone (G2 G).hom f, ∃ l : s.pt ⟶ (G2 G').left,
      l ≫ F2 = s.fst ∧ l ≫ (G2 G').hom = s.snd := by
    intro s
    let P : Over S' := Over.mk s.snd
    let x : Fin 2 → (P ⟶ G') := fun i => Over.homMk
      (hp.lift (s.fst ≫ (x2 G i).left) P.hom (by
        rw [Category.assoc, Over.w]; exact s.condition)) (hp.lift_snd _ _ _)
    have hx : ∀ i, (x i).left ≫ β = s.fst ≫ (x2 G i).left := fun i => hp.lift_fst _ _ _
    let l : P ⟶ G2 G' := lift (x 0) (x 1)
    have lx : ∀ i, l ≫ x2 G' i = x i := fun i => by fin_cases i <;> simp [l, x2]
    refine ⟨l.left, square_over_hom_ext _ fun i => ?_, Over.w l⟩
    rw [Category.assoc, f2, ← hx, ← lx]
    exact (Category.assoc _ _ _).symm
  choose l h₁ h₂ using ex
  refine ⟨⟨w⟩, ⟨PullbackCone.IsLimit.mk w l h₁ h₂ fun s m m₁ m₂ => square_over_hom_ext _ fun i => hp.hom_ext ?_ ?_⟩⟩
  · rw [Category.assoc, Category.assoc, ← f2, ← Category.assoc, ← Category.assoc, m₁, h₁]
  · rw [Category.assoc, Category.assoc, Over.w, m₂, h₂]

theorem fourth_power_over_hom_ext (G : Over S) {X : Scheme.{0}} {a b : X ⟶ (G4 G).left}
    (h : ∀ i, a ≫ (x4 G i).left = b ≫ (x4 G i).left) : a = b := by
  apply pullback.hom_ext
  · exact h 0
  · apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc]; exact h 1
    · apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, Category.assoc, Category.assoc]; exact h 2
      · rw [Category.assoc, Category.assoc, Category.assoc, Category.assoc]; exact h 3

theorem isPullback_four (hp : IsPullback β G'.hom G.hom f) :
    IsPullback (lift (pushPt hp.w (x4 G' 0)) (lift (pushPt hp.w (x4 G' 1))
      (lift (pushPt hp.w (x4 G' 2)) (pushPt hp.w (x4 G' 3))))).left (G4 G').hom (G4 G).hom f := by
  set L4 := lift (pushPt hp.w (x4 G' 0)) (lift (pushPt hp.w (x4 G' 1))
      (lift (pushPt hp.w (x4 G' 2)) (pushPt hp.w (x4 G' 3)))) with hL4
  have f4 : ∀ i, L4.left ≫ (x4 G i).left = (x4 G' i).left ≫ β := fun i => by
    rw [← Over.comp_left]
    have : L4 ≫ x4 G i = pushPt hp.w (x4 G' i) := by fin_cases i <;> simp [L4, x4]
    rw [this]; rfl
  have w : L4.left ≫ (G4 G).hom = (G4 G').hom ≫ f := Over.w L4
  have ex : ∀ s : PullbackCone (G4 G).hom f, ∃ l : s.pt ⟶ (G4 G').left,
      l ≫ L4.left = s.fst ∧ l ≫ (G4 G').hom = s.snd := by
    intro s
    let P : Over S' := Over.mk s.snd
    let x : Fin 4 → (P ⟶ G') := fun i => Over.homMk
      (hp.lift (s.fst ≫ (x4 G i).left) P.hom (by
        rw [Category.assoc, Over.w]; exact s.condition)) (hp.lift_snd _ _ _)
    have hx : ∀ i, (x i).left ≫ β = s.fst ≫ (x4 G i).left := fun i => hp.lift_fst _ _ _
    let l : P ⟶ G4 G' := lift (x 0) (lift (x 1) (lift (x 2) (x 3)))
    have lx : ∀ i, l ≫ x4 G' i = x i := fun i => by fin_cases i <;> simp [l, x4]
    refine ⟨l.left, fourth_power_over_hom_ext _ fun i => ?_, Over.w l⟩
    rw [Category.assoc, f4, ← hx, ← lx]
    exact (Category.assoc _ _ _).symm
  choose l h₁ h₂ using ex
  refine ⟨⟨w⟩, ⟨PullbackCone.IsLimit.mk w l h₁ h₂ fun s m m₁ m₂ => fourth_power_over_hom_ext _ fun i => hp.hom_ext ?_ ?_⟩⟩
  · rw [Category.assoc, Category.assoc, ← f4, ← Category.assoc, ← Category.assoc, m₁, h₁]
  · rw [Category.assoc, Category.assoc, Over.w, m₂, h₂]

theorem isPullback_three [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (gp : IsGrpPullback G' G f β) :
    IsPullback (cubeMapOf gp).F3 (G3 G').hom (G3 G).hom f := by
  have hp := gp.1
  have f3 : ∀ i, (cubeMapOf gp).F3 ≫ (x3 G i).left = (x3 G' i).left ≫ β := cubeMap_comp_proj_three (cubeMapOf gp)
  have w : (cubeMapOf gp).F3 ≫ (G3 G).hom = (G3 G').hom ≫ f :=
    Over.w (lift (pushPt hp.w (x3 G' 0)) (lift (pushPt hp.w (x3 G' 1)) (pushPt hp.w (x3 G' 2))))
  have ex : ∀ s : PullbackCone (G3 G).hom f, ∃ l : s.pt ⟶ (G3 G').left,
      l ≫ (cubeMapOf gp).F3 = s.fst ∧ l ≫ (G3 G').hom = s.snd := by
    intro s
    let P : Over S' := Over.mk s.snd
    let x : Fin 3 → (P ⟶ G') := fun i => Over.homMk
      (hp.lift (s.fst ≫ (x3 G i).left) P.hom (by
        rw [Category.assoc, Over.w]; exact s.condition)) (hp.lift_snd _ _ _)
    have hx : ∀ i, (x i).left ≫ β = s.fst ≫ (x3 G i).left := fun i => hp.lift_fst _ _ _
    let l : P ⟶ G3 G' := lift (x 0) (lift (x 1) (x 2))
    have lx : ∀ i, l ≫ x3 G' i = x i := fun i => by fin_cases i <;> simp [l, x3]
    refine ⟨l.left, hom_ext_triple _ fun i => ?_, Over.w l⟩
    rw [Category.assoc, f3, ← hx, ← lx]
    exact (Category.assoc _ _ _).symm
  choose l h₁ h₂ using ex
  refine ⟨⟨w⟩, ⟨PullbackCone.IsLimit.mk w l h₁ h₂ fun s m m₁ m₂ => hom_ext_triple _ fun i => hp.hom_ext ?_ ?_⟩⟩
  · rw [Category.assoc, Category.assoc, ← f3, ← Category.assoc, ← Category.assoc, m₁, h₁]
  · rw [Category.assoc, Category.assoc, Over.w, m₂, h₂]

theorem isPullback_pow {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] {f : S' ⟶ S} {β : G'.left ⟶ G.left} (h : IsGrpPullback G' G f β) :
    IsPullback (lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G'))).left (G2 G').hom (G2 G).hom f ∧
    IsPullback (cubeMapOf h).F3 (G3 G').hom (G3 G).hom f ∧
    IsPullback (lift (pushPt h.1.w (x4 G' 0)) (lift (pushPt h.1.w (x4 G' 1)) (lift (pushPt h.1.w (x4 G' 2))
      (pushPt h.1.w (x4 G' 3))))).left (G4 G').hom (G4 G).hom f :=
  ⟨isPullback_two h.1, isPullback_three h, isPullback_four h.1⟩

end GlobalTheory.Mum.PowCart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackPowersCartesianGroupSquareStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPullback_powers_cartesian_group_square : ∀ {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] {f : S' ⟶ S} {β : G'.left ⟶ G.left} (h : IsGrpPullback G' G f β), IsPullback (lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G'))).left (G2 G').hom (G2 G).hom f ∧ IsPullback (cubeMapOf h).F3 (G3 G').hom (G3 G).hom f ∧ IsPullback (lift (pushPt h.1.w (x4 G' 0)) (lift (pushPt h.1.w (x4 G' 1)) (lift (pushPt h.1.w (x4 G' 2)) (pushPt h.1.w (x4 G' 3))))).left (G4 G').hom (G4 G).hom f := by
  first | exact @GlobalTheory.Mum.PowCart.isPullback_pow | exact GlobalTheory.Mum.PowCart.isPullback_pow | (intros; apply GlobalTheory.Mum.PowCart.isPullback_pow <;> assumption)
end
end
