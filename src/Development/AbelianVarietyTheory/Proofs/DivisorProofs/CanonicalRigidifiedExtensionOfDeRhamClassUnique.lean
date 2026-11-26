module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExpandsAtSectionUniformised
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionTowerPresentationCotangentPullbackResRigi
public import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeCrystalReducesToDeRhamSqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoOfGenericNormalLocalBase

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalRigidifiedExtensionOfDeRhamClassUnique
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCocycleCotangentValueSubOfCoboundaryA
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCocycleCotangentValueSubOfCoboundaryA
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

attribute [local instance] cotOp cotCentral cotTower

theorem cotSnd_cotPt_eq_dUnit (R : Type) [CommRing R] (D : Type) [CommRing D] [Bialgebra R D] (z : D) :
    cotSnd R D (cotPt R D z) = dUnit (R := R) z := by
  change TrivSqZeroExt.snd (algebraMap R (TrivSqZeroExt R (Cot R D)) (Coalgebra.counit z) +
    TrivSqZeroExt.inr (AugCot.d (Bialgebra.counitAlgHom R D) z)) = _
  rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]

theorem crystallineCocycleCotangentValue_sub_of_coboundary (R : Type) [CommRing R]
    (X : Over (Sp R)) (D : Type) [CommRing D] [Bialgebra R D] (y : Pt X D)
    (f f' : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))) (k : C0 (O (dp0 R) (X.hom ≫ 𝟙 _)))
    (h : d0 _ k = f.1 - f'.1) :
    cotVal f y - cotVal f' y = dUnit (R := R) (A := D) (k (trivAt y)) := by
  have hf : f - f' = ⟨d0 _ k, commAlgFunctorCoboundaryZero_mem_cocyclesOne _ k⟩ := Subtype.ext h.symm
  let E := cotExt R D
  let p : D →ₐ[R] E.C := cotPt R D
  let y' : Pt X E.C := spOver p ≫ y
  let k₀ : E.B := k (Thick.triv E.B _ (E.red_w y'.w))
  let i : E.C := E.i k₀
  have h1 : E.val y'.left y'.w f - E.val y'.left y'.w f' = k (trivAt y') - i := by
    rw [← map_sub, hf]
    exact E.tangentValue_coboundary y'.left y'.w k
  have h2 : fv f D E.C p y - fv f' D E.C p y = k (trivAt y') - p (k (trivAt y)) := by
    let τ : trivAt y ⟶ trivAt y' := trivMap p y
    have e := congrArg (fun g : C1 (O (dp0 R) (X.hom ≫ 𝟙 _)) ↦ g _ _ τ) h
    change d0 _ k _ _ τ = _ at e
    rw [amitsur_d0_apply, mp_O] at e
    exact e.symm
  have hi : cotSnd R D i = 0 := by
    exact TrivSqZeroExt.snd_inl (M := Cot R D) k₀
  change cotSnd R D (E.val y'.left y'.w f - fv f D E.C p y) -
    cotSnd R D (E.val y'.left y'.w f' - fv f' D E.C p y) = _
  rw [← map_sub, sub_sub_sub_comm, h1, h2, sub_sub_sub_cancel_left, map_sub]
  rw [show p (k (trivAt y)) = cotPt R D (k (trivAt y)) from rfl,
    cotSnd_cotPt_eq_dUnit, hi, sub_zero]

end GlobalTheory.PtExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCocycleCotangentValueSubOfCoboundaryAStatement
alias GlobalTheory.T.cotVal_sub_eq_dUnit_of_d0_eq_sub :=
  GlobalTheory.PtExt.crystallineCocycleCotangentValue_sub_of_coboundary
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalRigidifiedExtensionOfDeRhamClassUnique
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem convMul_includeLeft_includeRight {R : Type} [CommRing R] {D : Type} [CommRing D] [Bialgebra R D] :
    (toConv (Algebra.TensorProduct.includeLeft : D →ₐ[R] D ⊗[R] D) *
      toConv (Algebra.TensorProduct.includeRight : D →ₐ[R] D ⊗[R] D)).ofConv = Bialgebra.comulAlgHom R D := by
  ext a
  rw [AlgHom.convMul_apply]
  simp only [Bialgebra.comulAlgHom_apply]
  induction (Coalgebra.comul (R := R) a) with
  | add u v hu hv => simp only [map_add (f := _), hu, hv]
  | tmul u v => simp

theorem cobOne_algebraMap {R : Type} [CommRing R] {D : Type} [CommRing D] [Bialgebra R D] (r : R) :
    cobOne R D (algebraMap R D r) = -algebraMap R (D ⊗[R] D) r := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, cobOne_apply, Algebra.algebraMap_eq_smul_one]
  simp [Algebra.TensorProduct.one_def]

end GlobalTheory.PtExt

namespace GlobalTheory.PtExt

theorem isCan_unique (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R)
    (t : G.TorsionTower A) (c : primDR A) (hA : IsAbelianScheme A) (x x' : G.RigExt)
    (hx : IsCan t c x) (hx' : IsCan t c x') : x = x' := by
  obtain ⟨d, z, w, hz, hw, rfl⟩ := hx
  obtain ⟨d', z', w', hz', hw', rfl⟩ := hx'
  obtain ⟨k, hk⟩ := H1.mk_eq_mk.1 (d.cl.trans d'.cl.symm)
  let κ : Fn0 A := fun D _ _ y ↦ k (trivAt y)
  have hκ : ∀ (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D')
      (y : Pt A D), fv d.f D D' φ y - fv d'.f D D' φ y = κ D' (spOver φ ≫ y) - φ (κ D y) := by
    intro D _ _ D' _ _ φ y
    have := congrFun (congrFun (congrFun hk (trivAt y)) (trivAt (spOver φ ≫ y))) (trivMap φ y)
    exact this.symm
  let e : Fn0 (A ⊗ A) := fun D _ _ u ↦
    d.g D (u ≫ fst A A) (u ≫ snd A A) - d'.g D (u ≫ fst A A) (u ≫ snd A A) -
      (κ D ((u ≫ fst A A) * (u ≫ snd A A)) - κ D (u ≫ fst A A) - κ D (u ≫ snd A A))
  have hcob : IsCob (whole (A ⊗ A)) (Fn1.zero _) e := by
    intro D _ _ D' _ _ φ u _
    have h1 := d.add D D' φ (u ≫ fst A A) (u ≫ snd A A)
    have h2 := d'.add D D' φ (u ≫ fst A A) (u ≫ snd A A)
    have h3 := hκ D D' φ ((u ≫ fst A A) * (u ≫ snd A A))
    have h4 := hκ D D' φ (u ≫ fst A A)
    have h5 := hκ D D' φ (u ≫ snd A A)
    rw [comp_mul] at h3
    simp only [e, Fn1.zero, Category.assoc, map_sub]
    linear_combination -h1 + h2 - h3 + h4 + h5
  obtain ⟨r, hr⟩ := GlobalTheory.T.natural_pointwiseCochain_const_of_globalSections_base R (A ⊗ A) Unit (whole _) (by simp [whole]) (globalFns_holds _ (A ⊗ A)
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA)).2 e hcob
  have he : ∀ (D : Type) [CommRing D] [Algebra R D] (y y' : Pt A D),
      d.g D y y' - d'.g D y y' - (κ D (y * y') - κ D y - κ D y') = algebraMap R D r := by
    intro D _ _ y y'
    have := hr D (lift y y') (sm_whole _)
    simpa [e] using this
  let b : ∀ n, G.A n := fun n ↦ d.h n - d'.h n - κ _ (t.y n) + algebraMap R (G.A n) r
  have hb : b ∈ G.funs := by
    intro n
    have h1 := d.res n
    have h2 := d'.res n
    have h3 := hκ _ _ (G.res n : G.A (n + 1) →ₐ[R] G.A n) (t.y (n + 1))
    rw [t.res] at h3
    have h4 : (G.res n : G.A (n + 1) →ₐ[R] G.A n) (algebraMap R _ r) = algebraMap R _ r := AlgHom.commutes _ _
    change (G.res n : G.A (n + 1) →ₐ[R] G.A n) (b (n + 1)) = b n
    have e1 : ∀ a, (G.res n : G.A (n + 1) →ₐ[R] G.A n) a = G.res n a := fun _ ↦ rfl
    simp only [b, map_sub, map_add (f := _), e1] at h3 h4 ⊢
    linear_combination h1 - h2 - h3 + h4
  refine (Submodule.Quotient.eq _).2 ⟨-⟨b, hb⟩, Prod.ext (Subtype.ext (funext fun n ↦ ?_))
    (Subtype.ext (funext fun n ↦ ?_))⟩
  · change cobOne R _ (-b n) = z.1 n - z'.1 n
    rw [hz, hz']
    have hXY := t.mul n (G.A n ⊗[R] G.A n) (toConv Algebra.TensorProduct.includeLeft)
      (toConv Algebra.TensorProduct.includeRight)
    rw [convMul_includeLeft_includeRight] at hXY
    have h0 := he _ (spOver (Algebra.TensorProduct.includeLeft : G.A n →ₐ[R] G.A n ⊗[R] G.A n) ≫ t.y n)
      (spOver (Algebra.TensorProduct.includeRight : G.A n →ₐ[R] G.A n ⊗[R] G.A n) ≫ t.y n)
    rw [← hXY] at h0
    have hc := hκ _ _ (Bialgebra.comulAlgHom R (G.A n)) (t.y n)
    have hL := hκ _ _ (Algebra.TensorProduct.includeLeft : G.A n →ₐ[R] G.A n ⊗[R] G.A n) (t.y n)
    have hR := hκ _ _ (Algebra.TensorProduct.includeRight : G.A n →ₐ[R] G.A n ⊗[R] G.A n) (t.y n)
    have hk1 := cobOne_apply (O := R) (κ _ (t.y n))
    have hk2 := cobOne_algebraMap (R := R) (D := G.A n) r
    simp only [Bialgebra.comulAlgHom_apply, Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.includeRight_apply] at hc hL hR
    simp only [Dat.coc, b, map_neg, map_add (f := _), map_sub]
    linear_combination hk1 - hk2 - h0 + hc - hL - hR
  · change dUnit (R := R) (-b n) = w.1 n - w'.1 n
    rw [hw, hw']
    have h0 := GlobalTheory.T.cotVal_sub_eq_dUnit_of_d0_eq_sub R A (G.A n) (t.y n) d.f d'.f k hk
    have h1 : dUnit (R := R) (algebraMap R (G.A n) r) = 0 := AugCot.d_algebraMap _ r
    simp only [Dat.om, b]
    change AugCot.d _ _ = _
    simp only [map_neg, map_add (f := _), map_sub]
    change -(dUnit (R := R) _ - dUnit (R := R) _ - dUnit (R := R) _ + dUnit (R := R) _) = _
    rw [h1]
    change _ = cotVal d.f (t.y n) - dUnit (R := R) _ - (cotVal d'.f (t.y n) - dUnit (R := R) _)
    rw [show cotVal d.f (t.y n) - dUnit (R := R) (d.h n) - (cotVal d'.f (t.y n) - dUnit (R := R) (d'.h n)) =
      (cotVal d.f (t.y n) - cotVal d'.f (t.y n)) - dUnit (R := R) (d.h n) + dUnit (R := R) (d'.h n) by abel, h0]
    abel

end GlobalTheory.PtExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalRigidifiedExtensionOfDeRhamClassUniqueStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.canonicalRigidifiedExtensionOfDeRhamClass_unique
    (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R)
    (t : G.TorsionTower A) (c : primDR A) (hA : IsAbelianScheme A) (x x' : G.RigExt)
    (hx : IsCan t c x) (hx' : IsCan t c x') : x = x' :=
  GlobalTheory.PtExt.isCan_unique R A p G t c hA x x' hx hx'
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveFamiliesThetaSymmetricMinMemberCompare
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveFamiliesThetaSymmetricMinMemberCompare
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin.PrimCmp

theorem esymm_map_hom {R R' : Type} [CommRing R] [CommRing R'] (i : R →+* R') (M : Multiset R) (j : ℕ) :
    (M.map i).esymm j = i (M.esymm j) := by
  unfold Multiset.esymm
  rw [Multiset.powersetCard_map, Multiset.map_map, map_multiset_sum, Multiset.map_map]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun s _ => ?_)
  simp only [Function.comp, map_multiset_prod]

theorem symTup_map {R R' : Type} [CommRing R] [CommRing R'] (i : R →+* R') {N : ℕ} (c : Fin N → R) (j : Fin N) :
    i (symTup c j) = symTup (fun b => i (c b)) j := by
  unfold symTup
  rw [map_pow]
  congr 1
  have hm : Finset.univ.val.map (fun b => i (c b)) = (Finset.univ.val.map c).map i := by
    rw [Multiset.map_map]; rfl
  rw [hm, esymm_map_hom]

theorem esymm_map_mul {R : Type} [CommRing R] {A : Type} (t : R) (M : Multiset A) (f : A → R) (j : ℕ) :
    (M.map fun b => t * f b).esymm j = t ^ j * (M.map f).esymm j := by
  have : (M.map fun b => t * f b) = (M.map f).map (fun x => t * x) := by rw [Multiset.map_map]; rfl
  rw [this]
  unfold Multiset.esymm
  rw [Multiset.powersetCard_map, Multiset.map_map, ← Multiset.sum_map_mul_left]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun s hs => ?_)
  have hc := (Multiset.mem_powersetCard.1 hs).2
  simp only [Function.comp]
  rw [Multiset.prod_map_mul]
  simp [hc]

theorem symTup_mul {R : Type} [CommRing R] {N : ℕ} (c : Fin N → R) (t : R) (j : Fin N) :
    symTup (fun b => t * c b) j = t ^ N.factorial * symTup c j := by
  unfold symTup
  have h := esymm_map_mul t (Finset.univ.val) c ((j : ℕ) + 1)
  rw [h, mul_pow, ← pow_mul, Nat.mul_div_cancel' (Nat.dvd_factorial (Nat.succ_pos _) j.2)]

theorem mem_of_isIntegralElem {V K : Type} [CommRing V] [Field K] (i : V →+* K) (W : ValuationSubring K)
    (hW : ∀ v, i v ∈ W) {x : K} (hx : i.IsIntegralElem x) : x ∈ W := by
  obtain ⟨p, hm, hp⟩ := hx
  let φ : V →+* W := i.codRestrict W.toSubring hW
  have hφ : (algebraMap W K).comp φ = i := by ext v; rfl
  have hint : IsIntegral W x := ⟨p.map φ, hm.map φ, by rw [Polynomial.eval₂_map, hφ]; exact hp⟩
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  exact y.2

theorem mem_of_pow_mem {K : Type} [Field K] (W : ValuationSubring K) {w : K} {k : ℕ} (hk : 1 ≤ k)
    (h : w ^ k ∈ W) : w ∈ W := by
  rw [← W.valuation_le_one_iff] at h ⊢
  rw [map_pow] at h
  exact (pow_le_one_iff (by omega)).1 h

theorem mem_range_of_forall {V K : Type} [CommRing V] [IsDomain V] [IsIntegrallyClosed V] [Field K]
    (io : FractionRing V →+* K) (z : FractionRing V)
    (h : ∀ W : ValuationSubring K, (∀ v, io (algebraMap V (FractionRing V) v) ∈ W) → io z ∈ W) :
    z ∈ Set.range (algebraMap V (FractionRing V)) := by
  letI : Algebra V K := (io.comp (algebraMap V (FractionRing V))).toAlgebra
  have hic : IsIntegrallyClosedIn (integralClosure V K).toSubring K :=
    inferInstanceAs (IsIntegrallyClosedIn (integralClosure V K) K)
  have h1 : io z ∈ (integralClosure V K).toSubring := by
    by_contra hn
    obtain ⟨W, hW, hzW⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn hn
    exact hzW (h W (fun v => hW ((integralClosure V K).algebraMap_mem v)))
  let f : FractionRing V →ₐ[V] K := { io with commutes' := fun _ => rfl }
  have h2 : IsIntegral V z := (isIntegral_algHom_iff f (f : FractionRing V →+* K).injective).1 h1
  exact IsIntegrallyClosed.isIntegral_iff.1 h2

end GlobalTheory.UMin.PrimCmp

namespace GlobalTheory.UMin.PrimCmp

theorem key {V K : Type} [CommRing V] [IsDomain V] [Field K] (io : FractionRing V →+* K) (N : ℕ) (c : Fin N → K) (a : K)
    (ha : a ≠ 0) (hP : Prim (io.comp (algebraMap V (FractionRing V))) (fun b => c b / a)) (e : Fin N → FractionRing V)
    (he : ∀ j, io (e j) = symTup c j) (j₀ : Fin N) (he0 : e j₀ ≠ 0)
    (hq : ∀ j, e j / e j₀ ∈ Set.range (algebraMap V (FractionRing V))) (W : ValuationSubring K)
    (hW : ∀ v, io (algebraMap V (FractionRing V) v) ∈ W) :
    io (e j₀) / a ^ N.factorial ∈ W ∧ (io (e j₀) / a ^ N.factorial)⁻¹ ∈ W := by
  have hcW : ∀ b, c b / a ∈ W := fun b => mem_of_isIntegralElem _ W hW (hP.1 b)
  obtain ⟨b₀, hb0, hb0i⟩ := hP.2
  have hb0W : (c b₀ / a)⁻¹ ∈ W := mem_of_isIntegralElem _ W hW hb0i
  let y : Fin N → W := fun b => ⟨c b / a, hcW b⟩
  have hu : IsUnit (y b₀) := (Units.mkOfMulEqOne (y b₀) ⟨_, hb0W⟩ (Subtype.ext (show c b₀ / a * (c b₀ / a)⁻¹ = 1 from mul_inv_cancel₀ hb0))).isUnit
  let z : Fin N → W := fun b => y b * ↑hu.unit⁻¹
  have hz : z b₀ = 1 := by simp [z]
  obtain ⟨k, hk1, hkN, hku⟩ := GlobalTheory.exists_isUnit_esymm_of_eq_one W (Fin N) z b₀ hz
  have hyz : ∀ b, y b = y b₀ * z b := by
    intro b; simp only [z]; rw [mul_left_comm, IsUnit.mul_val_inv, _root_.mul_one]
  have hesy : IsUnit ((Finset.univ.val.map y).esymm k) := by
    have hm : Finset.univ.val.map y = Finset.univ.val.map (fun b => y b₀ * z b) :=
      Multiset.map_congr rfl fun b _ => hyz b
    rw [hm, esymm_map_mul]
    exact (hu.pow k).mul hku
  have hkN' : k ≤ N := by simpa using hkN
  let j₁ : Fin N := ⟨k - 1, by omega⟩
  have hsy : IsUnit (symTup y j₁) := by
    unfold symTup
    have : (j₁ : ℕ) + 1 = k := by simp only [j₁]; omega
    rw [this]
    exact hesy.pow _
  have hcoe : ∀ j, ((symTup y j : W) : K) = io (e j) / a ^ N.factorial := by
    intro j
    have h1 := symTup_map W.subtype y j
    rw [ValuationSubring.coe_subtype] at h1
    rw [h1]
    have h2 : (fun b => ((y b : W) : K)) = fun b => a⁻¹ * c b := by
      funext b; simp [y, div_eq_inv_mul]
    rw [h2, symTup_mul, he, inv_pow, inv_mul_eq_div]
  have ht : io (e j₀) / a ^ N.factorial ∈ W := hcoe j₀ ▸ (symTup y j₀).2
  obtain ⟨v, hv⟩ := hq j₁
  have hr : io (e j₁ / e j₀) ∈ W := by rw [← hv]; exact hW v
  have hio0 : io (e j₀) ≠ 0 := (map_ne_zero io).2 he0
  have hsplit : symTup y j₁ = ⟨_, hr⟩ * ⟨_, ht⟩ := by
    apply Subtype.ext
    rw [hcoe]
    show _ = io (e j₁ / e j₀) * (io (e j₀) / a ^ N.factorial)
    rw [map_div₀]
    field_simp
  rw [hsplit] at hsy
  have htu := isUnit_of_mul_isUnit_right hsy
  refine ⟨ht, ?_⟩
  have h3 : ((↑htu.unit⁻¹ : W) : K) * (io (e j₀) / a ^ N.factorial) = 1 := by
    have := congrArg Subtype.val (IsUnit.val_inv_mul htu)
    rw [MulMemClass.coe_mul, OneMemClass.coe_one] at this
    exact this
  rw [← eq_inv_of_mul_eq_one_left h3]
  exact (↑htu.unit⁻¹ : W).2

end GlobalTheory.UMin.PrimCmp

theorem GlobalTheory.UMin.prim_symTup_cmp : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsIntegrallyClosed V] [Field K] (io : FractionRing V →+* K) (N N' k : ℕ) (J : Type) (c : Fin N → K) (c' : Fin N' → K) (a : K) (e : Fin N → FractionRing V) (th : J → FractionRing V), a ≠ 0 → 1 ≤ k → Prim (io.comp (algebraMap V (FractionRing V))) (fun b => c b / a) → Prim (io.comp (algebraMap V (FractionRing V))) (fun b => c' b / a) → (∀ j, io (e j) = symTup c j) → (∀ x, ∃ b, c' x ^ k = io (th b) ^ k) → (∀ b, ∃ x, c' x ^ k = io (th b) ^ k) → ∀ j₀, e j₀ ≠ 0 → (∀ j, e j / e j₀ ∈ Set.range (algebraMap V (FractionRing V))) → (∀ b, th b ^ N.factorial / e j₀ ∈ Set.range (algebraMap V (FractionRing V))) ∧ ∃ b, th b ≠ 0 ∧ e j₀ / th b ^ N.factorial ∈ Set.range (algebraMap V (FractionRing V)) := by
  intro V K _ _ _ _ io N N' k J c c' a e th ha hk hP hP' he hth1 hth2 j₀ he0 hq
  refine ⟨fun b => ?_, ?_⟩
  · apply GlobalTheory.UMin.PrimCmp.mem_range_of_forall io
    intro W hW
    obtain ⟨-, hti⟩ := GlobalTheory.UMin.PrimCmp.key io N c a ha hP e he j₀ he0 hq W hW
    obtain ⟨x, hx⟩ := hth2 b
    have hw : io (th b) / a ∈ W := by
      refine GlobalTheory.UMin.PrimCmp.mem_of_pow_mem W hk ?_
      rw [div_pow, ← hx, ← div_pow]
      exact pow_mem (GlobalTheory.UMin.PrimCmp.mem_of_isIntegralElem _ W hW (hP'.1 x)) k
    have hio0 : io (e j₀) ≠ 0 := (map_ne_zero io).2 he0
    have heq : io (th b ^ N.factorial / e j₀) = (io (th b) / a) ^ N.factorial * (io (e j₀) / a ^ N.factorial)⁻¹ := by
      rw [map_div₀, map_pow, div_pow, inv_div]
      field_simp
    rw [heq]
    exact mul_mem (pow_mem hw _) hti
  · obtain ⟨x₀, hx0, hx0i⟩ := hP'.2
    obtain ⟨b₁, hb1⟩ := hth1 x₀
    have hk0 : k ≠ 0 := by omega
    have hth0 : io (th b₁) ≠ 0 := by
      intro h0
      apply hx0
      have h2 : c' x₀ ^ k = 0 := by rw [hb1, h0, zero_pow hk0]
      simp [pow_eq_zero_iff hk0 |>.1 h2]
    refine ⟨b₁, fun h => hth0 (by rw [h, map_zero]), ?_⟩
    apply GlobalTheory.UMin.PrimCmp.mem_range_of_forall io
    intro W hW
    obtain ⟨ht, -⟩ := GlobalTheory.UMin.PrimCmp.key io N c a ha hP e he j₀ he0 hq W hW
    have hwi : (io (th b₁) / a)⁻¹ ∈ W := by
      refine GlobalTheory.UMin.PrimCmp.mem_of_pow_mem W hk ?_
      rw [inv_pow, div_pow, ← hb1, ← div_pow, ← inv_pow]
      exact pow_mem (GlobalTheory.UMin.PrimCmp.mem_of_isIntegralElem _ W hW hx0i) k
    have heq : io (e j₀ / th b₁ ^ N.factorial) = (io (e j₀) / a ^ N.factorial) * ((io (th b₁) / a)⁻¹) ^ N.factorial := by
      rw [map_div₀, map_pow, inv_div, div_pow]
      field_simp
    rw [heq]
    exact mul_mem ht (pow_mem hwi _)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveFamiliesThetaSymmetricMinMemberCompareStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitive_families_thetaSymmetric_min_member_compare : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsIntegrallyClosed V] [Field K] (io : FractionRing V →+* K) (N N' k : ℕ) (J : Type) (c : Fin N → K) (c' : Fin N' → K) (a : K) (e : Fin N → FractionRing V) (th : J → FractionRing V), a ≠ 0 → 1 ≤ k → Prim (io.comp (algebraMap V (FractionRing V))) (fun b => c b / a) → Prim (io.comp (algebraMap V (FractionRing V))) (fun b => c' b / a) → (∀ j, io (e j) = symTup c j) → (∀ x, ∃ b, c' x ^ k = io (th b) ^ k) → (∀ b, ∃ x, c' x ^ k = io (th b) ^ k) → ∀ j₀, e j₀ ≠ 0 → (∀ j, e j / e j₀ ∈ Set.range (algebraMap V (FractionRing V))) → (∀ b, th b ^ N.factorial / e j₀ ∈ Set.range (algebraMap V (FractionRing V))) ∧ ∃ b, th b ≠ 0 ∧ e j₀ / th b ^ N.factorial ∈ Set.range (algebraMap V (FractionRing V)) := by
  first | exact @GlobalTheory.UMin.prim_symTup_cmp | exact GlobalTheory.UMin.prim_symTup_cmp | (intros; apply GlobalTheory.UMin.prim_symTup_cmp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPrimeToPLevelLiftSquareZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPrimeToPLevelLiftSquareZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped CategoryTheory.Obj

namespace GlobalTheory.HTLevelLift

theorem existsUnique_torsion_lift_thick (C C₀ : Type) [CommRing C] [CommRing C₀] (π : C →+* C₀)
    (hπ : Function.Surjective π) (hnil : IsNilpotent (RingHom.ker π)) (n : ℕ) (hn : IsUnit (n : C))
    (A₀ : Over (Sp C₀)) [GrpObj A₀] [IsCommMonObj A₀] (A : Over (Sp C)) [GrpObj A] [IsCommMonObj A]
    (i : A₀.left ⟶ A.left) (hA : IsAbelianScheme A) (hpb : IsGrpPullback A₀ A (spMap π) i)
    (s₀ : 𝟙_ (Over (Sp C₀)) ⟶ A₀) (hs₀ : s₀ ^ n = 1) :
    ∃! s : 𝟙_ (Over (Sp C)) ⟶ A, s ^ n = 1 ∧ s₀.left ≫ i = spMap π ≫ s.left := by
  haveI : Smooth A.hom := hA.smooth
  have hn' : IsUnit (n : Γ(Sp C, ⊤)) := by
    simpa using hn.map (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom
  haveI := GlobalTheory.GrpTangent.etale_id_pow A hn'
  let T' : Over (Sp C₀) := 𝟙_ (Over (Sp C₀))
  let T : Over (Sp C) := Over.mk (T'.hom ≫ spMap π)
  have hwi : i ≫ A.hom = A₀.hom ≫ spMap π := hpb.1.w
  have hpt : ∀ x : T' ⟶ A₀, (x.left ≫ i) ≫ A.hom = T.hom := by
    intro x
    rw [Category.assoc, hwi, ← Category.assoc, Over.w x]
    rfl
  let pt : (T' ⟶ A₀) → (T ⟶ A) := fun x => Over.homMk (x.left ≫ i) (hpt x)
  have hone : pt 1 = 1 := by
    have h := hpb.2 T' 1 1 (pt 1) (pt 1) rfl rfl
    rw [_root_.mul_one] at h
    have h2 : pt 1 * pt 1 = pt 1 := Over.OverMorphism.ext h
    exact mul_eq_left.mp h2
  have hpow : ∀ m : ℕ, (pt s₀) ^ m = pt (s₀ ^ m) := by
    intro m
    induction m with
    | zero => rw [pow_zero, pow_zero, hone]
    | succ m ih =>
      rw [pow_succ, pow_succ]
      exact Over.OverMorphism.ext (hpb.2 T' (s₀ ^ m) s₀ ((pt s₀) ^ m) (pt s₀) (by rw [ih]; rfl) rfl)
  have hx : (pt s₀) ^ n = 1 := by rw [hpow, hs₀, hone]
  let f : A.left ⟶ A.left := (𝟙 A ^ n).left
  have hf : ∀ {Y : Over (Sp C)} (y : Y ⟶ A), y.left ≫ f = (y ^ n).left := by
    intro Y y
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  have hone' : ∀ {Y : Over (Sp C)}, ((1 : Y ⟶ A)).left = Y.hom ≫ (η[A] : 𝟙_ (Over (Sp C)) ⟶ A).left := by
    intro Y
    rw [Hom.one_def, Over.comp_left]
    congr 1
  have hw : (s₀.left ≫ i) ≫ f = Spec.map (CommRingCat.ofHom π) ≫ (η[A] : 𝟙_ (Over (Sp C)) ⟶ A).left := by
    have := hf (pt s₀)
    rw [hx, hone'] at this
    simpa [pt, T, T'] using this
  obtain ⟨l, ⟨hl1, hl2⟩, huniq⟩ :=
    GlobalTheory.existsUnique_lift_of_etale_of_surjective f (CommRingCat.ofHom π) hπ hnil (s₀.left ≫ i) _ hw
  have hls : l ≫ A.hom = (𝟙_ (Over (Sp C))).hom := by
    have e : f ≫ A.hom = A.hom := Over.w (𝟙 A ^ n)
    rw [← e, ← Category.assoc, hl2]
    exact Over.w (η[A] : 𝟙_ (Over (Sp C)) ⟶ A)
  let s : 𝟙_ (Over (Sp C)) ⟶ A := Over.homMk l hls
  have hsn : ∀ s' : 𝟙_ (Over (Sp C)) ⟶ A, s' ^ n = 1 ↔ s'.left ≫ f = (η[A] : 𝟙_ (Over (Sp C)) ⟶ A).left := by
    intro s'
    have e1 : ((1 : 𝟙_ (Over (Sp C)) ⟶ A)).left = (η[A] : 𝟙_ (Over (Sp C)) ⟶ A).left := by
      rw [hone']; exact Category.id_comp _
    rw [hf]
    constructor
    · intro h; rw [h, e1]
    · intro h
      apply Over.OverMorphism.ext
      rw [h, e1]
  refine ⟨s, ⟨(hsn s).2 hl2, hl1.symm⟩, ?_⟩
  rintro s' ⟨h1, h2⟩
  exact Over.OverMorphism.ext (huniq s'.left ⟨h2.symm, (hsn s').1 h1⟩)

theorem map_nsmul_pow {La Q : Type} [AddCommGroup La] [Group Q] (f : La → Q) (hf : ∀ x y, f (x + y) = f x * f y)
    (n : ℕ) (x : La) : f (n • x) = f x ^ n := by
  induction n with
  | zero =>
    have h := hf 0 0
    rw [add_zero] at h
    rw [zero_smul, pow_zero]
    exact mul_eq_left.mp h.symm
  | succ n ih => rw [succ_nsmul, hf, ih, pow_succ]

theorem level_lift : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (o₀ : GlobalTheory.UPel.HT.Obj b N (spMap π ≫ spMap tR)), ∀ (A : Over (Sp C)) [GrpObj A] [IsCommMonObj A] (i : o₀.A.left ⟶ A.left) (h : IsGrpPullback o₀.A A (spMap π) i), IsAbelianScheme A → ∀ (act : GlobalTheory.UPel.HT.OActN D.O A), (∀ c, (o₀.act.act c).left ≫ i = i ≫ (act.act c).left) → N.Coprime p → ∀ (P : LB (G2 A).left) (φ₂ : (G2 o₀.A).left ⟶ (G2 A).left), P.IsLB → IsSquare i φ₂ → LBIso o₀.P (P.pull φ₂) → ∃ eta : D.La → (𝟙_ (Over (Sp C)) ⟶ A), (∀ x y, eta (x + y) = eta x * eta y) ∧ (∀ (c : D.O) x, eta (c • x) = eta x ≫ act.act c) ∧ (∀ x, eta (N • x) = 1) ∧ (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp C) (β : R →+* k), x ≫ spMap tR = spMap β → ∃ I : GlobalTheory.UPel.HT.TateIsoO D k (Over.mk x ⟶ A) (fun c g => g ≫ act.act c) (fun n g g' z => Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) n g g' (unitOn z)), ∀ y, toUnit _ ≫ eta y = I.ev N y) ∧ ∀ y, (o₀.eta y).left ≫ i = spMap π ≫ (eta y).left := by
  intro p _ D R _ b N C C₀ _ _ _ _ π hπ hsq tR o₀ A _ _ i h hA act hact hN P φ₂ hP hsqr hLB
  have hnil : IsNilpotent (RingHom.ker π) := ⟨2, hsq⟩
  have hNu : IsUnit (N : C) := by simpa using (b.unit N hN).map tR
  have hlift := fun y => existsUnique_torsion_lift_thick C C₀ π hπ hnil N hNu o₀.A A i hA h (o₀.eta y)
      (by rw [← map_nsmul_pow o₀.eta o₀.eta_add, o₀.eta_ker])
  choose eta hspec huniq using hlift
  let TT : Over (Sp C) := Over.mk ((𝟙_ (Over (Sp C₀))).hom ≫ spMap π)
  let u : TT ⟶ 𝟙_ (Over (Sp C)) := toUnit TT
  have hu : u.left = spMap π := by simpa [TT] using Over.w u
  have hcomp : ∀ s : 𝟙_ (Over (Sp C)) ⟶ A, (u ≫ s).left = spMap π ≫ s.left := fun s => by
    rw [Over.comp_left, hu]
  have hadd : ∀ x y, eta (x + y) = eta x * eta y := by
    intro x y
    refine (huniq (x + y) _ ⟨by rw [mul_pow, (hspec x).1, (hspec y).1, _root_.one_mul], ?_⟩).symm
    have e := h.2 (𝟙_ (Over (Sp C₀))) (o₀.eta x) (o₀.eta y) (u ≫ eta x) (u ≫ eta y)
      (by rw [hcomp, (hspec x).2]) (by rw [hcomp, (hspec y).2])
    rw [o₀.eta_add, ← e, ← MonObj.comp_mul, hcomp]
  refine ⟨eta, hadd, ?_, ?_, ?_, fun y => (hspec y).2⟩
  · intro c x
    haveI := act.hom c
    haveI := o₀.act.hom c
    refine (huniq (c • x) _ ⟨by rw [← MonObj.pow_comp, (hspec x).1, MonObj.one_comp], ?_⟩).symm
    rw [o₀.eta_lin, Over.comp_left, Category.assoc, hact, ← Category.assoc, (hspec x).2, Over.comp_left,
      Category.assoc]
  · intro x
    rw [map_nsmul_pow eta hadd, (hspec x).1]
  · intro k _ _ x β hxβ
    obtain ⟨φ, hφx⟩ := Spec.map_surjective x
    have hker : RingHom.ker π ≤ RingHom.ker φ.hom := by
      intro a ha
      have h2 : a * a ∈ RingHom.ker π ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul ha ha
      rw [hsq] at h2
      have h3 : φ.hom (a * a) = 0 := by
        rw [show a * a = 0 from h2, map_zero]
      rw [RingHom.mem_ker]
      rw [map_mul] at h3
      exact mul_self_eq_zero.mp h3
    let φ₀ : C₀ →+* k := π.liftOfRightInverse (Function.surjInv hπ) (Function.rightInverse_surjInv hπ) ⟨φ.hom, hker⟩
    have hφ : φ₀.comp π = φ.hom := RingHom.liftOfRightInverse_comp _ _ _ _
    have hx : x = spMap φ₀ ≫ spMap π := by
      rw [← hφx]
      show Spec.map φ = Spec.map (CommRingCat.ofHom φ₀) ≫ Spec.map (CommRingCat.ofHom π)
      rw [← Spec.map_comp]
      congr 1
      ext a
      simp [← hφ]
    subst hx
    obtain ⟨I₀, hI₀⟩ := o₀.geom k (spMap φ₀) β (by rw [← Category.assoc]; exact hxβ)
    obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv h (Over.mk (spMap φ₀)) (spMap φ₀ ≫ spMap π) rfl
    have hd : (lift (𝟙 o₀.A) (𝟙 o₀.A)).left ≫ φ₂ = i ≫ (lift (𝟙 A) (𝟙 A)).left :=
      GlobalTheory.AxisTrivExt.lift_match hsqr.1 hsqr.2 (𝟙 o₀.A) (𝟙 o₀.A) (𝟙 A) (𝟙 A) (by simp) (by simp)
    have a3 : LBIso (o₀.P.pull (lift (𝟙 o₀.A) (𝟙 o₀.A)).left)
        ((P.pull φ₂).pull (lift (𝟙 o₀.A) (𝟙 o₀.A)).left) :=
      GenSpread.lbIso_pullback hLB _
    have b1 : LBIso (P.pull (i ≫ (lift (𝟙 A) (𝟙 A)).left)) ((P.pull φ₂).pull (lift (𝟙 o₀.A) (𝟙 o₀.A)).left) :=
      GenSpread.lbIso_pull_pull hP _ hd.symm
    have b2 : LBIso (P.pull (i ≫ (lift (𝟙 A) (𝟙 A)).left)) ((P.pull (lift (𝟙 A) (𝟙 A)).left).pull i) :=
      GenSpread.lbIso_pull_pull hP i rfl
    have iD : LBIso (o₀.P.pull (lift (𝟙 o₀.A) (𝟙 o₀.A)).left) ((P.pull (lift (𝟙 A) (𝟙 A)).left).pull i) :=
      LBIso.trans (pull_isLB o₀.isLB _) (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _)
        (LBIso.trans (pull_isLB o₀.isLB _) (pull_isLB (pull_isLB hP _) _) (pull_isLB hP _) a3 b1.symm) b2
    have lin : ∀ (c : D.O) (g : Over.mk (spMap φ₀) ⟶ o₀.A), e (g ≫ o₀.act.act c) = e g ≫ act.act c := fun c g =>
      Over.OverMorphism.ext (by rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, hact, Category.assoc])
    refine ⟨{ ζ := I₀.ζ
              ζ_prim := I₀.ζ_prim
              ζ_pow := I₀.ζ_pow
              ev := fun n y => e (I₀.ev n y)
              add := fun n y y' => by simp only [I₀.add, map_mul]
              lin := fun n c y => by simp only [I₀.lin, lin]
              ker := fun n hn hp y => by
                rw [← I₀.ker n hn hp y]
                exact ⟨fun E => e.injective (E.trans (map_one e).symm), fun E => by rw [E, map_one]⟩
              onto := fun n hn hp q => by
                obtain ⟨q, rfl⟩ := e.surjective q
                rw [← map_pow]
                refine Iff.trans ?_ ((I₀.onto n hn hp q).trans ?_)
                · exact ⟨fun E => e.injective (E.trans (map_one e).symm), fun E => by rw [E, map_one]⟩
                · exact ⟨fun ⟨y, hy⟩ => ⟨y, by rw [hy]⟩, fun ⟨y, hy⟩ => ⟨y, e.injective hy⟩⟩
              tower := fun n m hn hm hp y => by rw [← map_pow, I₀.tower n m hn hm hp y]
              isom := fun n hn hp y y' =>
                (GlobalTheory.weilIs_iff_of_isGrpPullback_comm _ _ A o₀.A (spMap π) i _ _ (pull_isLB hP _)
                  (pull_isLB o₀.isLB _) h iD (Over.mk (spMap φ₀)) n _ _ (e (I₀.ev n y)) (e (I₀.ev n y')) _
                  (he _) (he _)).1 (I₀.isom n hn hp y y') }, fun y => ?_⟩
    show toUnit _ ≫ eta y = e (I₀.ev N y)
    rw [← hI₀ y]
    have e₁ : (toUnit (Over.mk (spMap φ₀))).left = spMap φ₀ := by simpa using Over.w (toUnit (Over.mk (spMap φ₀)))
    have e₂ : (toUnit (Over.mk (spMap φ₀ ≫ spMap π))).left = spMap φ₀ ≫ spMap π := by
      simpa using Over.w (toUnit (Over.mk (spMap φ₀ ≫ spMap π)))
    apply Over.OverMorphism.ext
    rw [he, Over.comp_left, Over.comp_left, Category.assoc, (hspec y).2, e₁, e₂, Category.assoc]

end GlobalTheory.HTLevelLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPrimeToPLevelLiftSquareZeroStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_primeToP_level_lift_squareZero : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (o₀ : GlobalTheory.UPel.HT.Obj b N (spMap π ≫ spMap tR)), ∀ (A : Over (Sp C)) [GrpObj A] [IsCommMonObj A] (i : o₀.A.left ⟶ A.left) (h : IsGrpPullback o₀.A A (spMap π) i), IsAbelianScheme A → ∀ (act : GlobalTheory.UPel.HT.OActN D.O A), (∀ c, (o₀.act.act c).left ≫ i = i ≫ (act.act c).left) → N.Coprime p → ∀ (P : LB (G2 A).left) (φ₂ : (G2 o₀.A).left ⟶ (G2 A).left), P.IsLB → IsSquare i φ₂ → LBIso o₀.P (P.pull φ₂) → ∃ eta : D.La → (𝟙_ (Over (Sp C)) ⟶ A), (∀ x y, eta (x + y) = eta x * eta y) ∧ (∀ (c : D.O) x, eta (c • x) = eta x ≫ act.act c) ∧ (∀ x, eta (N • x) = 1) ∧ (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp C) (β : R →+* k), x ≫ spMap tR = spMap β → ∃ I : GlobalTheory.UPel.HT.TateIsoO D k (Over.mk x ⟶ A) (fun c g => g ≫ act.act c) (fun n g g' z => Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) n g g' (unitOn z)), ∀ y, toUnit _ ≫ eta y = I.ev N y) ∧ ∀ y, (o₀.eta y).left ≫ i = spMap π ≫ (eta y).left := by
  first | exact @GlobalTheory.HTLevelLift.level_lift | exact GlobalTheory.HTLevelLift.level_lift | (intros; apply GlobalTheory.HTLevelLift.level_lift; all_goals assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertFactor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatPosDefAddNsmulPosDefHermitian
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatPosDefAddNsmulPosDefHermitian
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem posn_quad_hom {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) (r : ℝ) :
    (((r : ℂ) • z) ⬝ᵥ H.mulVec (star ((r : ℂ) • z))).re = r ^ 2 * (z ⬝ᵥ H.mulVec (star z)).re := by
  rw [star_smul, Complex.star_def, Complex.conj_ofReal, Matrix.mulVec_smul, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, smul_eq_mul, ← _root_.mul_assoc, ← Complex.ofReal_mul,
    Complex.re_ofReal_mul]
  ring

theorem posn_quad_add {g : ℕ} (H₀ Hm : Matrix (Fin g) (Fin g) ℂ) (n : ℕ) (z : Fin g → ℂ) :
    (z ⬝ᵥ (Hm + n • H₀).mulVec (star z)).re
      = (z ⬝ᵥ Hm.mulVec (star z)).re + n * (z ⬝ᵥ H₀.mulVec (star z)).re := by
  have h1 : (n • H₀).mulVec (star z) = n • H₀.mulVec (star z) := by
    ext i; simp [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.smul_sum, smul_mul_assoc, _root_.mul_assoc]
  rw [Matrix.add_mulVec, dotProduct_add, h1, dotProduct_smul, Complex.add_re, nsmul_eq_mul,
    ← Complex.ofReal_natCast, Complex.re_ofReal_mul]

theorem posn_cont {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ) :
    Continuous fun z : Fin g → ℂ => (z ⬝ᵥ H.mulVec (star z)).re := by
  fun_prop

theorem posn_main : ∀ (g : ℕ) (H₀ Hm : Matrix (Fin g) (Fin g) ℂ),
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₀.mulVec (star z)).re) →
    ∃ n : ℕ, ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ (Hm + n • H₀).mulVec (star z)).re := by
  intro g H₀ Hm hpos

  have hnorm : ∀ z : Fin g → ℂ, z ≠ 0 →
      ((((‖z‖⁻¹ : ℝ) : ℂ) • z) ∈ Metric.sphere (0 : Fin g → ℂ) 1) := by
    intro z hz
    have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
    rw [mem_sphere_zero_iff_norm, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hr), inv_mul_cancel₀ hr.ne']

  have hred : ∀ (H : Matrix (Fin g) (Fin g) ℂ),
      (∀ w ∈ Metric.sphere (0 : Fin g → ℂ) 1, 0 < (w ⬝ᵥ H.mulVec (star w)).re) →
      ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H.mulVec (star z)).re := by
    intro H hS z hz
    have h := hS _ (hnorm z hz)
    rw [posn_quad_hom] at h
    exact pos_of_mul_pos_right h (sq_nonneg _)
  by_cases hne : (Metric.sphere (0 : Fin g → ℂ) 1).Nonempty
  · have hK : IsCompact (Metric.sphere (0 : Fin g → ℂ) 1) := isCompact_sphere 0 1
    obtain ⟨w₀, hw₀, hmin⟩ := hK.exists_isMinOn hne (posn_cont H₀).continuousOn
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (posn_cont Hm).continuousOn
    have hw₀ne : w₀ ≠ 0 := by
      intro h; rw [h, mem_sphere_zero_iff_norm, norm_zero] at hw₀; exact zero_ne_one hw₀
    set m := (w₀ ⬝ᵥ H₀.mulVec (star w₀)).re with hm
    have hm0 : 0 < m := hpos w₀ hw₀ne
    obtain ⟨n, hn⟩ := exists_nat_gt (C / m)
    refine ⟨n, hred _ ?_⟩
    intro w hw
    rw [posn_quad_add]
    have h1 : m ≤ (w ⬝ᵥ H₀.mulVec (star w)).re := hmin hw
    have h2 : |(w ⬝ᵥ Hm.mulVec (star w)).re| ≤ C := by
      simpa [Real.norm_eq_abs] using hC w hw
    have h3 : C < n * m := by rwa [div_lt_iff₀ hm0] at hn
    have h4 : (n : ℝ) * m ≤ n * (w ⬝ᵥ H₀.mulVec (star w)).re :=
      mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg n)
    have h5 := neg_abs_le (w ⬝ᵥ Hm.mulVec (star w)).re
    linarith
  · refine ⟨0, fun z hz => absurd ⟨_, hnorm z hz⟩ hne⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatPosDefAddNsmulPosDefHermitianStatement
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nat_posDef_add_nsmul_posDef_hermitian : ∀ (g : ℕ) (H₀ Hm : Matrix (Fin g) (Fin g) ℂ),
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₀.mulVec (star z)).re) →
    ∃ n : ℕ, ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ (Hm + n • H₀).mulVec (star z)).re := by
  first | exact @GlobalTheory.posn_main | exact GlobalTheory.posn_main | (intros; apply GlobalTheory.posn_main <;> assumption)
end
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AHBundle

variable {A : Over (Sp ℂ)} [GrpObj A] {g : ℕ}

theorem mem_of_ex_eq {L L' : LB A.left} (u : HolUnif A L g) (u' : HolUnif A L' g) (hex : u'.ex = u.ex)
    {z : Fin g → ℂ} (hz : z ∈ u.Λ) : z ∈ u'.Λ := by
  rw [← u'.ker, hex, u.ker]; exact hz

theorem isFactorAH_divUnif {M M' : LB A.left} (u : HolUnif A M g) (u' : HolUnif A M' g) (hex : u'.ex = u.ex)
    {H H' : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ} {χ' : u'.Λ → ℂ}
    (h : IsFactorAH u H χ) (h' : IsFactorAH u' H' χ') :
    IsFactorAH (GlobalTheory.SameFactor.divUnif u u' hex) (H' - H)
      (fun l => χ' ⟨l.1, mem_of_ex_eq u u' hex l.2⟩ / χ l) := by
  refine ⟨h'.1.sub h.1, fun l => ?_, fun l p z hz => ?_⟩
  · have := h.2.1 l
    rw [norm_div, h'.2.1]
    exact (by rw [this]; norm_num : (1 : ℝ) / ‖χ l‖ = 1)
  · obtain ⟨h1, h2⟩ := (top_le_preimage_inf _ _ _).1 hz
    have hl : u.ex (z + l) = u.ex z := by
      rw [u.ex_add, (u.ker _).2 l.2, _root_.mul_one]
    have e' := h'.2.2 ⟨l.1, mem_of_ex_eq u u' hex l.2⟩ p.1 z (by rw [hex]; exact h1)
    have e := h.2.2 l p.2 z h2
    have n1 := u.fr_ne p.2 z h2
    have n2 := u.fr_ne p.2 (z + l) (by rw [hl]; exact h2)
    have nχ : χ l ≠ 0 := by
      intro h0; have := h.2.1 l; rw [h0, norm_zero] at this; exact zero_ne_one this
    show u'.fr p.1 z * (u.fr p.2 z)⁻¹ = _ * _ * (u'.fr p.1 (z + l) * (u.fr p.2 (z + l))⁻¹)
    rw [e', e]
    simp only [Matrix.sub_mulVec, dotProduct_sub, mul_sub]
    rw [show ∀ a b c d : ℂ, a - b + (c - d) = (a + c) - (b + d) from fun _ _ _ _ => by ring, Complex.exp_sub]
    have ne := Complex.exp_ne_zero (↑Real.pi * (z ⬝ᵥ H.mulVec (star (l : Fin g → ℂ))) +
        ↑Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ H.mulVec (star (l : Fin g → ℂ))))
    field_simp

end GlobalTheory.AHBundle

theorem GlobalTheory.AHBundle.exists_lb_of_factor_chain {g : ℕ} {A : Over (Sp ℂ)} [GrpObj A]
    (L₀ : LB A.left) (u₀ : HolUnif A L₀ g) (H₀ : Matrix (Fin g) (Fin g) ℂ) (χ₀ : u₀.Λ → ℂ) (hL₀ : L₀.IsLB)
    (h₀ : IsFactorAH u₀ H₀ χ₀) (H' : Matrix (Fin g) (Fin g) ℂ)
    (M₁ : LB A.left) (u₁ : HolUnif A M₁ g) (χ₁ : u₁.Λ → ℂ) (hM₁ : M₁.IsLB) (hex₁ : u₁.ex = u₀.ex)
    (h₁ : IsFactorAH u₁ H' χ₁) (k : ℕ) :
    ∃ (M : LB A.left) (u : HolUnif A M g) (χ : u.Λ → ℂ), M.IsLB ∧ u.ex = u₀.ex ∧ IsFactorAH u (H' - k • H₀) χ := by
  induction k with
  | zero => exact ⟨M₁, u₁, χ₁, hM₁, hex₁, by simpa using h₁⟩
  | succ k ih =>
    obtain ⟨M, u, χ, hM, hex, h⟩ := ih
    have hd := GlobalTheory.AHBundle.isFactorAH_divUnif u₀ u hex h₀ h
    have e : H' - (k + 1) • H₀ = (H' - k • H₀) - H₀ := by rw [succ_nsmul, sub_add_eq_sub_sub]
    rw [← e] at hd
    exact ⟨_, _, _, LB.isLB_div hM hL₀, rfl, hd⟩

theorem GlobalTheory.AHBundle.exists_lb_of_hermitian_int : ∀ (g : ℕ) (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A →
    ∀ (L₀ : LB A.left) (u₀ : HolUnif A L₀ g) (H₀ : Matrix (Fin g) (Fin g) ℂ) (χ₀ : u₀.Λ → ℂ), L₀.IsLB → u₀.IsAH H₀ χ₀ →
    ∀ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian →
    (∀ l ∈ u₀.Λ, ∀ l' ∈ u₀.Λ, ∃ n : ℤ, (l ⬝ᵥ Hm.mulVec (star l')).im = n) →
    ∃ (M : LB A.left) (u : HolUnif A M g) (χ : u.Λ → ℂ), M.IsLB ∧ u.ex = u₀.ex ∧ IsFactorAH u Hm χ := by
  intro g A _ hA L₀ u₀ H₀ χ₀ hL₀ hAH Hm hHm hint
  obtain ⟨n, hn⟩ := (GlobalTheory.T.exists_nat_posDef_add_nsmul_posDef_hermitian) g H₀ Hm hAH.2.1
  have hint0 := (GlobalTheory.T.appellHumbertFactor_imForm_integral_on_lattice) g A L₀ u₀ H₀ χ₀ hL₀ (isFactorAH_of_isAH hAH)
  have hint' : ∀ l ∈ u₀.Λ, ∀ l' ∈ u₀.Λ, ∃ m : ℤ, (l ⬝ᵥ (Hm + n • H₀).mulVec (star l')).im = m := by
    intro l hl l' hl'
    obtain ⟨m₁, e₁⟩ := hint l hl l' hl'
    obtain ⟨m₂, e₂⟩ := hint0 l hl l' hl'
    refine ⟨m₁ + n * m₂, ?_⟩
    rw [Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, dotProduct_smul, Complex.add_im,
      nsmul_eq_mul, Complex.mul_im, e₁, e₂]
    push_cast; simp
  have hH' : (Hm + n • H₀).IsHermitian := hHm.add (by
    unfold Matrix.IsHermitian; rw [Matrix.conjTranspose_nsmul, hAH.1.eq])
  obtain ⟨M₁, u₁, χ₁, hM₁, hex₁, h₁⟩ := (GlobalTheory.T.appellHumbert_exists_lineBundle_posDef_hermitian) g A hA L₀ u₀ H₀ χ₀ hL₀ hAH (Hm + n • H₀) hH' hn hint'
  obtain ⟨M, u, χ, hM, hex, h⟩ := GlobalTheory.AHBundle.exists_lb_of_factor_chain L₀ u₀ H₀ χ₀ hL₀ (isFactorAH_of_isAH hAH)
    _ M₁ u₁ χ₁ hM₁ hex₁ (isFactorAH_of_isAH h₁) n
  refine ⟨M, u, χ, hM, hex, ?_⟩
  simpa using h
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalOfGenericFibrePullback
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar

namespace GlobalTheory.FlagCls

theorem isNormalScheme_of_isPreimmersion_of_flat {U X : Scheme.{0}} (j : U ⟶ X) [IsPreimmersion j] [Flat j]
    (h : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme U := by
  intro x
  obtain ⟨h1, h2⟩ := h (j x)
  have hf : (j.stalkMap x).hom.Flat := Flat.stalkMap j x
  have hs : Function.Surjective (j.stalkMap x).hom := j.stalkMap_surjective x
  have hi : Function.Injective (j.stalkMap x).hom := by
    letI := (j.stalkMap x).hom.toAlgebra
    have : Module.Flat (X.presheaf.stalk (j x)) (U.presheaf.stalk x) := hf
    have : IsLocalHom (algebraMap (X.presheaf.stalk (j x)) (U.presheaf.stalk x)) :=
      inferInstanceAs (IsLocalHom (j.stalkMap x).hom)
    have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := X.presheaf.stalk (j x))
      (B := U.presheaf.stalk x)
    exact FaithfulSMul.algebraMap_injective (X.presheaf.stalk (j x)) (U.presheaf.stalk x)
  let e := RingEquiv.ofBijective (j.stalkMap x).hom ⟨hi, hs⟩
  have h3 : IsDomain (U.presheaf.stalk x) := e.symm.toMulEquiv.isDomain _
  exact ⟨h3, IsIntegrallyClosed.of_equiv e⟩

theorem isNormalScheme_of_isPullback_fractionField : ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (N G : Scheme.{0}) (g : N ⟶ Sp R) (j : G ⟶ N) (s : G ⟶ Sp K), IsPullback j s g (spMap (algebraMap R K)) → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme N → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme G := by
  intro R K _ _ _ _ _ N G g j s hp hN
  have hb : IsPreimmersion (spMap (algebraMap R K)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have hbf : Flat (spMap (algebraMap R K)) := by
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat K (nonZeroDivisors R))
  have : IsPreimmersion j := MorphismProperty.of_isPullback (P := @IsPreimmersion) hp.flip hb
  have : Flat j := MorphismProperty.of_isPullback (P := @Flat) hp.flip hbf
  exact isNormalScheme_of_isPreimmersion_of_flat j hN

end GlobalTheory.FlagCls
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDeRhamRingAction
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.DeRham GlobalTheory.DeRhamSheaf GlobalTheory.AbDual GlobalTheory.Cris
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbDatum.DRAct

section Pull

variable {R : Type} [CommRing R] {I : Ideal R} {S : Scheme.{0}} (κ : DividedPowers I) (t : S ⟶ Sp R)
  {A : Over S} [GrpObj A]

theorem primPull_of_eq_id (f : A ⟶ A) [IsMonHom f] (h : f = 𝟙 A) (c : prim κ t A) : primPull κ t f c = c := by
  subst h
  exact Subtype.ext (IsMor.pullCohomologyOne_id _ c.1)

theorem primPull_of_eq_comp (f g k : A ⟶ A) [IsMonHom f] [IsMonHom g] [IsMonHom k] (h : k = f ≫ g)
    (c : prim κ t A) : primPull κ t k c = primPull κ t f (primPull κ t g c) := by
  subst h
  exact (GrpMor.pull_pull _ _ _ (fun _ ↦ rfl) rfl c).symm

theorem primPull_of_eq_mul (f g k : A ⟶ A) [IsMonHom f] [IsMonHom g] [IsMonHom k] (h : k = f * g)
    (c : prim κ t A) : primPull κ t k c = primPull κ t f c + primPull κ t g c := by
  subst h
  exact Subtype.ext (c.2 A f g)

end Pull

variable {O : Type} [CommRing O] {T : Scheme.{0}} {A : Over T} [GrpObj A] (i : OAct O A)

variable {H : T.Modules} (e : ∀ (V : T.Opens) (hV : IsAffineOpen V), Γ(H, V) ≃ₗ[Γ(T, V)] primDR (onAff A hV))

end GlobalTheory.AbDatum.DRAct
end
end
