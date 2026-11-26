module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.TateTwistAffineLineProjectionEquiv
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPstAtOfIsSstAt

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.AffineLineActionFstTwistEquiv
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

noncomputable section

namespace UpperTheory.LineAct

open Polynomial

private def coord {T : Scheme.{0}} (f : T ⟶ Pbf.A1) : Γ(T, ⊤) :=
  f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℤ[X])).inv.hom X)

private theorem coord_comp {T' T : Scheme.{0}} (g : T' ⟶ T) (f : T ⟶ Pbf.A1) :
    coord (g ≫ f) = g.appTop.hom (coord f) := by
  simp [coord]
  rfl

private theorem eq_of_appTop {T : Scheme.{0}} (f : T ⟶ Pbf.A1) :
    f = T.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (CommRingCat.of ℤ[X])).inv ≫ f.appTop) := by
  have h := Scheme.toSpecΓ_naturality f
  have h2 : (Spec (CommRingCat.of ℤ[X])).toSpecΓ ≫ Spec.map (Scheme.ΓSpecIso (CommRingCat.of ℤ[X])).inv = 𝟙 _ := by
    rw [← SpecMap_ΓSpecIso_hom, ← Spec.map_comp]
    simp
  calc f = f ≫ (Spec (CommRingCat.of ℤ[X])).toSpecΓ ≫ Spec.map (Scheme.ΓSpecIso (CommRingCat.of ℤ[X])).inv := by
        rw [h2, Category.comp_id]
    _ = _ := by
        rw [← Category.assoc, h, Category.assoc, ← Spec.map_comp]

private theorem coord_bij (T : Scheme.{0}) : Function.Bijective (coord (T := T)) := by
  constructor
  · intro f g h
    rw [eq_of_appTop f, eq_of_appTop g]
    congr 2
    apply CommRingCat.hom_ext
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    exact h
  · intro a
    refine ⟨T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (eval₂RingHom (Int.castRingHom _) a)), ?_⟩
    simp [coord, Scheme.toSpecΓ_appTop]

private theorem chain_ext {A : CommRingCat.{0}} {n : ℕ} (x y : Fin (n + 1) ⥤ Ob affC A)
    (h : ∀ i, (x.obj i).pt = (y.obj i).pt) : x = y := by
  have ho : ∀ i, x.obj i = y.obj i := fun i => by
    have := h i
    cases hx : x.obj i
    cases hy : y.obj i
    simp_all
  refine CategoryTheory.Functor.ext ho (fun i j f => ?_)
  exact Subtype.ext (Subsingleton.elim (α := PUnit) _ _)

private theorem chain_pt {A : CommRingCat.{0}} {n : ℕ} (x : Fin (n + 1) ⥤ Ob affC A) (i : Fin (n + 1)) :
    (x.obj i).pt = (x.obj 0).pt :=
  ((x.map (homOfLE (Fin.zero_le i))).2).symm

private def lineMap : sch.obj Pbf.A1 ⟶ spc affC where
  app k :=
    { app := fun T => TypeCat.ofHom fun f =>
        (show Fin (k.unop.len + 1) ⥤ Ob affC Γ(T.unop, ⊤) from
          (Functor.const _).obj ⟨coord (show T.unop ⟶ Pbf.A1 from f)⟩)
      naturality := fun T T' g => by
        ext f
        refine chain_ext _ _ fun i => ?_
        exact coord_comp g.unop (show T.unop ⟶ Pbf.A1 from f) }
  naturality m n f := by
    ext T x
    rfl

private theorem lineMap_bij (k : ℕ) (T : Scheme.{0}) :
    Function.Bijective (fun x : Sx (sch.obj Pbf.A1) k T => x.map lineMap) := by
  constructor
  · intro f g h
    refine (coord_bij T).1 ?_
    exact congrArg (fun c : Fin (k + 1) ⥤ Ob affC Γ(T, ⊤) => (c.obj 0).pt) h
  · intro y
    obtain ⟨f, hf⟩ := (coord_bij T).2 ((show Fin (k + 1) ⥤ Ob affC Γ(T, ⊤) from y).obj 0).pt
    refine ⟨f, ?_⟩
    refine chain_ext _ _ fun i => ?_
    exact hf.trans (chain_pt (show Fin (k + 1) ⥤ Ob affC Γ(T, ⊤) from y) i).symm

private theorem mulS_hom_ext {X E Z : Spc} {f g : X ⟶ mulS E Z}
    (h1 : f ≫ mulS.fst E Z = g ≫ mulS.fst E Z) (h2 : f ≫ mulS.snd E Z = g ≫ mulS.snd E Z) : f = g := by
  ext k T x
  have a := ConcreteCategory.congr_hom (NatTrans.congr_app (NatTrans.congr_app h1 k) T) x
  have b := ConcreteCategory.congr_hom (NatTrans.congr_app (NatTrans.congr_app h2 k) T) x
  exact Prod.ext a b

end UpperTheory.LineAct

end

open UpperTheory.LineAct in
theorem UpperTheory.affineLineAction_fst_twistEquiv :
    ∀ (q : ℕ) [NeZero q] (S : Spc) (i : ℤ), Inv q S → Eqv _ (Sp.fst S affC) (tw q i) := by
  intro q _ S i hS
  haveI : IsIso lineMap := UpperTheory.isIso_of_bijective_on_simplices lineMap lineMap_bij
  let u : sch.obj Pbf.A1 ⨯ S ⟶ Sp S affC := mulS.lift prod.snd (prod.fst ≫ lineMap)
  let v : Sp S affC ⟶ sch.obj Pbf.A1 ⨯ S := prod.lift (Sp.snd S affC ≫ inv lineMap) (Sp.fst S affC)
  have hu1 : u ≫ mulS.fst _ _ = prod.snd := rfl
  have hu2 : u ≫ mulS.snd _ _ = prod.fst ≫ lineMap := rfl
  have huv : u ≫ v = 𝟙 _ := by
    apply Limits.prod.hom_ext
    · rw [Category.assoc, prod.lift_fst, ← Category.assoc, hu2]
      simp
    · rw [Category.assoc, prod.lift_snd, Category.id_comp]
      exact hu1
  have hvu : v ≫ u = 𝟙 _ := by
    apply mulS_hom_ext
    · rw [Category.assoc, hu1, prod.lift_snd, Category.id_comp]
    · rw [Category.assoc, hu2, ← Category.assoc, prod.lift_fst]
      simp
  have hpu : ∀ n, Function.Bijective (pull (ZMod q) u (tw q i) n) := fun n =>
    Function.bijective_iff_has_inverse.2 ⟨pull _ v (tw q i) n, fun x => by
      rw [← pull_comp, hvu, pull_id], fun x => by
      rw [← pull_comp, huv, pull_id]⟩
  intro n
  have h := UpperTheory.tateTwist_affineLine_projection_equiv q S i hS n
  have e : (⇑(pull (ZMod q) (prod.snd : sch.obj Pbf.A1 ⨯ S ⟶ S) (tw q i) n)) =
      (pull (ZMod q) u (tw q i) n) ∘ (pull (ZMod q) (Sp.fst S affC) (tw q i) n) := by
    funext x
    rw [← hu1]
    exact pull_comp _ u _ _ n x
  rw [e] at h
  exact (Function.Bijective.of_comp_iff' (hpu n) _).1 h
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.FunctionFieldOfFiniteEtaleCover
section -- merged from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.GermComapEqAlgebraMapGermOfFiniteEtale
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry GlobalTheory.HodgeCoh GlobalTheory.CechDR ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section
namespace UpperTheory.Cb

section Alg

variable {B B' K L : Type} [CommRing B] [CommRing B'] [IsDomain B] [IsDomain B'] [Field K] [Field L]
  [Algebra B B'] [Algebra B K] [Algebra K L] [Algebra B' L] [Algebra B L]
  [IsScalarTower B K L] [IsScalarTower B B' L] [IsFractionRing B K] [IsFractionRing B' L]

include K L in
private theorem injective_algebraMap : Function.Injective (algebraMap B B') := by
  have h : Function.Injective (algebraMap B L) := by
    rw [IsScalarTower.algebraMap_eq B K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective B K)
  rw [IsScalarTower.algebraMap_eq B B' L] at h
  exact Function.Injective.of_comp (f := algebraMap B' L) h

include K L in
private theorem isLocalization_of_integral [Algebra.IsIntegral B B'] :
    IsLocalization (Algebra.algebraMapSubmonoid B' (nonZeroDivisors B)) L := by
  have hinj : Function.Injective (algebraMap B B') := injective_algebraMap (K := K) (L := L)
  have hL : Function.Injective (algebraMap B' L) := IsFractionRing.injective B' L
  refine { map_units := ?_, surj := ?_, exists_of_eq := ?_ }
  · rintro ⟨_, r, hr, rfl⟩
    refine IsUnit.mk0 _ ?_
    exact (map_ne_zero_iff _ hL).2 ((map_ne_zero_iff _ hinj).2 (nonZeroDivisors.ne_zero hr))
  · intro z
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := B') z
    obtain ⟨r, hr, t, ht⟩ := (Algebra.IsIntegral.isIntegral (R := B) b).isAlgebraic.exists_nonzero_dvd hb
    refine ⟨⟨a * t, ⟨algebraMap B B' r, r, mem_nonZeroDivisors_of_ne_zero hr, rfl⟩⟩, ?_⟩
    have hb0 : algebraMap B' L b ≠ 0 := (map_ne_zero_iff _ hL).2 (nonZeroDivisors.ne_zero hb)
    have e : algebraMap B' L (algebraMap B B' r) = algebraMap B' L b * algebraMap B' L t := by
      rw [ht, map_mul]
    change algebraMap B' L a / algebraMap B' L b * algebraMap B' L (algebraMap B B' r) =
      algebraMap B' L (a * t)
    rw [e, map_mul]
    field_simp
  · intro x y h
    exact ⟨1, by rw [hL h]⟩

include K L in
private theorem isPushout_of_integral [Algebra.IsIntegral B B'] : Algebra.IsPushout B K B' L := by
  have h1 := isLocalization_of_integral (B := B) (B' := B') (K := K) (L := L)
  have h2 := (isLocalizedModule_iff_isLocalization (S := nonZeroDivisors B) (A := B') (Aₛ := L)).2 h1
  exact ⟨(isLocalizedModule_iff_isBaseChange (nonZeroDivisors B) K _).1 h2⟩

private theorem algebraMap_etTrace [Module.Finite B B'] [Algebra.Etale B B'] (b : B') :
    algebraMap B K (etTrace B B' b) = Algebra.trace K L (algebraMap B' L b) := by
  haveI := projective_of_etale B B'
  haveI hp := isPushout_of_integral (B := B) (B' := B') (K := K) (L := L)
  haveI : Module.Finite K L := Module.Finite.equiv hp.out.equiv
  rw [← algTrace_eq_trace, algTrace_of_isPushout (B := B) (B' := B') b]
  rfl

end Alg

theorem germ_comap_eq_algebraMap_germ_of_finite_etale : ∀ (Z Y : Scheme.{0}) [IsIntegral Z] [IsIntegral Y] (p : Z ⟶ Sp ℂ) (p' : Y ⟶ Sp ℂ)
    (c : Y ⟶ Z) (hc : c ≫ p = p') [IsFinite c] [Etale c] [Algebra Z.functionField Y.functionField],
    (∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c ⁻¹ᵁ V) (g : Γ(Z, V)),
      (Y.presheaf.germ (c ⁻¹ᵁ V) (genericPoint Y) hV').hom ((c.app V).hom g) =
        algebraMap Z.functionField Y.functionField ((Z.presheaf.germ V (genericPoint Z) hV).hom g)) →
    ∀ (V : Z.Opens) (hV : IsAffineOpen V) (hg : genericPoint Z ∈ V)
      (hg' : genericPoint Y ∈ c ⁻¹ᵁ V) (b' : Γ(Y, c ⁻¹ᵁ V)),
      (Z.presheaf.germ V (genericPoint Z) hg).hom (secTrace (f := c) p p' hV b') =
        Algebra.trace Z.functionField Y.functionField
          ((Y.presheaf.germ (c ⁻¹ᵁ V) (genericPoint Y) hg').hom b') := by
  intro Z Y _ _ p p' c _ _ _ _ hg V hVa hV hV' b'
  haveI : Nonempty V := ⟨⟨_, hV⟩⟩
  haveI : Nonempty (c ⁻¹ᵁ V : Y.Opens) := ⟨⟨_, hV'⟩⟩
  letI := secAlg p p' c V
  haveI := sec_finite (s := p) (s' := p') (f := c) hVa
  haveI := sec_etale (s := p) (s' := p') (f := c) hVa
  letI : Algebra (Sec p V) Z.functionField := (Z.germToFunctionField V).hom.toAlgebra
  letI : Algebra (Sec p' (c ⁻¹ᵁ V)) Y.functionField := (Y.germToFunctionField (c ⁻¹ᵁ V)).hom.toAlgebra
  letI : Algebra (Sec p V) Y.functionField :=
    ((algebraMap Z.functionField Y.functionField).comp (algebraMap (Sec p V) Z.functionField)).toAlgebra
  haveI : IsScalarTower (Sec p V) Z.functionField Y.functionField := .of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower (Sec p V) (Sec p' (c ⁻¹ᵁ V)) Y.functionField :=
    .of_algebraMap_eq fun g ↦ (hg V hV hV' g).symm
  haveI : IsDomain (Sec p V) := inferInstanceAs (IsDomain Γ(Z, V))
  haveI : IsDomain (Sec p' (c ⁻¹ᵁ V)) := inferInstanceAs (IsDomain Γ(Y, c ⁻¹ᵁ V))
  haveI : IsFractionRing (Sec p V) Z.functionField :=
    functionField_isFractionRing_of_isAffineOpen Z V hVa
  haveI : IsFractionRing (Sec p' (c ⁻¹ᵁ V)) Y.functionField :=
    functionField_isFractionRing_of_isAffineOpen Y (c ⁻¹ᵁ V) (hVa.preimage c)
  exact algebraMap_etTrace (B := Sec p V) (B' := Sec p' (c ⁻¹ᵁ V)) (K := Z.functionField)
    (L := Y.functionField) b'

end UpperTheory.Cb
end
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsDeRhamTraceOfSeparable
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD GlobalTheory.CechDR GlobalTheory.HodgeCoh ReciprocityTheory.ChartRestriction.G.Geo.Tor

open TensorProduct

namespace UpperTheory.DeRhamTrace

variable (k K L : Type) [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L]
  [IsScalarTower k K L]

private noncomputable abbrev beta : L ⊗[K] Ω[K⁄k] →ₗ[L] L ⊗[K] DR k K :=
  LinearMap.baseChange L (ι1 (R := k) (B := K))

private theorem beta_anti (x y : L ⊗[K] Ω[K⁄k]) :
    beta k K L x * beta k K L y + beta k K L y * beta k K L x = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb =>
    rw [map_add (f := _), add_mul, mul_add]
    calc _ = (beta k K L a * beta k K L y + beta k K L y * beta k K L a) +
          (beta k K L b * beta k K L y + beta k K L y * beta k K L b) := by abel
      _ = 0 := by rw [ha, hb, add_zero]
  | tmul a ω =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add c d hc hd =>
      rw [map_add (f := _), add_mul, mul_add]
      calc _ = (beta k K L (a ⊗ₜ ω) * beta k K L c + beta k K L c * beta k K L (a ⊗ₜ ω)) +
            (beta k K L (a ⊗ₜ ω) * beta k K L d + beta k K L d * beta k K L (a ⊗ₜ ω)) := by abel
        _ = 0 := by rw [hc, hd, add_zero]
    | tmul b ω' =>
      simp only [beta, LinearMap.baseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul]
      rw [mul_comm b a, ← TensorProduct.tmul_add]
      have : ι1 (R := k) (B := K) ω * ι1 (R := k) (B := K) ω' +
          ι1 (R := k) (B := K) ω' * ι1 (R := k) (B := K) ω = 0 :=
        ExteriorAlgebra.ι_add_mul_swap ω ω'
      rw [this, TensorProduct.tmul_zero]

private theorem beta_sq (x : L ⊗[K] Ω[K⁄k]) : beta k K L x * beta k K L x = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb =>
    rw [map_add (f := _), add_mul, mul_add, mul_add, ha, hb, zero_add, add_zero]
    exact beta_anti k K L a b
  | tmul a ω =>
    simp only [beta, LinearMap.baseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul]
    have : ι1 (R := k) (B := K) ω * ι1 (R := k) (B := K) ω = 0 := ExteriorAlgebra.ι_sq_zero ω
    rw [this, TensorProduct.tmul_zero]

variable [Algebra.FormallyEtale K L]

private noncomputable def phi : Ω[L⁄k] →ₗ[L] L ⊗[K] DR k K :=
  beta k K L ∘ₗ (KaehlerDifferential.isBaseChange_of_formallyEtale k K L).equiv.symm.toLinearMap

private theorem phi_sq (x : Ω[L⁄k]) : phi k K L x * phi k K L x = 0 := beta_sq k K L _

private noncomputable def psi : DR k L →ₐ[L] L ⊗[K] DR k K :=
  ExteriorAlgebra.lift L ⟨phi k K L, phi_sq k K L⟩

private theorem psi_mapDR (ω : DR k K) : psi k K L (GlobalTheory.W1.mapDR k K L ω) = 1 ⊗ₜ ω := by
  have key : ((psi k K L).restrictScalars K).comp (GlobalTheory.W1.mapDR k K L) =
      Algebra.TensorProduct.includeRight := by
    apply ExteriorAlgebra.hom_ext
    refine LinearMap.ext fun η ↦ ?_
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply,
      AlgHom.restrictScalars_apply, Algebra.TensorProduct.includeRight_apply]
    rw [GlobalTheory.W1.mapDR, ExteriorAlgebra.lift_ι_apply]
    simp only [GlobalTheory.W1.map1, LinearMap.comp_apply, LinearMap.restrictScalars_apply]
    rw [psi, ExteriorAlgebra.lift_ι_apply]
    simp only [phi, LinearMap.comp_apply, LinearEquiv.coe_coe, IsBaseChange.equiv_symm_apply,
      beta, LinearMap.baseChange_tmul]
  exact congrArg (fun f ↦ f ω) key

end UpperTheory.DeRhamTrace

open UpperTheory.DeRhamTrace in
theorem UpperTheory.exists_deRhamTrace_of_separable :
    ∀ (k K L : Type) [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L] [FiniteDimensional K L] [Algebra.IsSeparable K L], ∃ T : DR k L →ₗ[k] DR k K, GlobalTheory.W1.IsTrDR k K L T := by
  intro k K L _ _ _ _ _ _ _ _ _
  haveI : Algebra.FormallyEtale K L := Algebra.FormallyEtale.of_isSeparable K L
  let Tr : (L ⊗[K] DR k K) →ₗ[K] DR k K :=
    (TensorProduct.lid K (DR k K)).toLinearMap ∘ₗ LinearMap.rTensor (DR k K) (Algebra.trace K L)
  refine ⟨(Tr.restrictScalars k) ∘ₗ ((psi k K L).toLinearMap.restrictScalars k), ?_⟩
  intro b ω
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, AlgHom.toLinearMap_apply]
  rw [map_smul, psi_mapDR, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  simp [Tr]
end

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD GlobalTheory.CechDR GlobalTheory.HodgeCoh ReciprocityTheory.ChartRestriction.G.Geo.Tor

private theorem mDR_alg_eq_mapDR (k K L : Type) [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L]
    [Algebra K L] [IsScalarTower k K L] (w : DR k K) :
    (semiHom_algebraMap k K L).mDR w = GlobalTheory.W1.mapDR k K L w := by
  induction w using ExteriorAlgebra.induction with
  | algebraMap r =>
    rw [SemiHom.mDR_algebraMap, AlgHom.commutes]
    rfl
  | ι x =>
    have h1 := SemiHom.mDR_ι (semiHom_algebraMap k K L) x
    simp only [ι1] at h1
    rw [h1, SemiHom.oneFormMap_eq_kaehlerDifferential_map _ (fun _ => rfl)]
    simp only [GlobalTheory.W1.mapDR, ExteriorAlgebra.lift_ι_apply, GlobalTheory.W1.map1, LinearMap.coe_comp,
      LinearMap.coe_restrictScalars, Function.comp_apply, ι1]
  | mul a b ha hb => rw [map_mul, map_mul, ha, hb]
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]

private theorem mDR_square {k B B' K L : Type} [Field k] [Field K] [Field L] [CommRing B] [CommRing B']
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L] [Algebra k B] [Algebra k B']
    {α : B →+* K} {β : B →+* B'} {γ : B' →+* L} (hα : SemiHom (RingHom.id k) α)
    (hβ : SemiHom (RingHom.id k) β) (hγ : SemiHom (RingHom.id k) γ)
    (h : ∀ b, γ (β b) = algebraMap K L (α b)) {j : ℕ} (x : Om k B j) :
    hγ.mDR (hβ.mDR (x : DR k B)) = GlobalTheory.W1.mapDR k K L (hα.mDR (x : DR k B)) := by
  rw [← SemiHom.coe_mOm hβ, ← SemiHom.coe_mOm hγ, ← mDR_alg_eq_mapDR, ← SemiHom.coe_mOm hα,
    ← SemiHom.coe_mOm (semiHom_algebraMap k K L),
    SemiHom.mOm_mOm hβ hγ (hβ.comp hγ) (fun _ => rfl),
    SemiHom.mOm_mOm hα (semiHom_algebraMap k K L) (hβ.comp hγ) (fun b => (h b).symm)]

private theorem formGerm_toOm {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] (s : X ⟶ Sp k) (j : ℕ)
    {V : X.Opens} (hV : IsAffineOpen V) (hη : genericPoint X ∈ V) (x : OmU s V j) :
    letI := algΓ s; letI := ffAlg s
    formGerm s j hV hη (toOm s j V x) = (semiHom_germSec s hη).mDR (x : DR k (Sec s V)) := by
  letI := algΓ s; letI := ffAlg s
  change (semiHom_germSec s hη).mDR (((toOmEquiv s j hV).symm (toOm s j V x) : OmU s V j) : DR k (Sec s V)) = _
  rw [← toOmEquiv_apply s j hV, LinearEquiv.symm_apply_apply]

theorem UpperTheory.functionField_of_finite_etale_cover :
    ∀ (Z Y : Scheme.{0}) [IsIntegral Z] [IsIntegral Y] (p : Z ⟶ Sp ℂ) (p' : Y ⟶ Sp ℂ) (c : Y ⟶ Z) (hc : c ≫ p = p') [IsFinite c] [Etale c] [inst : Algebra ℂ Z.functionField] [inst' : Algebra ℂ Y.functionField] [Algebra Z.functionField Y.functionField] [IsScalarTower ℂ Z.functionField Y.functionField] (hinst : inst = ffAlg p) (hinst' : inst' = ffAlg p'), (∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c ⁻¹ᵁ V) (g : Γ(Z, V)), (Y.presheaf.germ (c ⁻¹ᵁ V) (genericPoint Y) hV').hom ((c.app V).hom g) = algebraMap Z.functionField Y.functionField ((Z.presheaf.germ V (genericPoint Z) hV).hom g)) → FiniteDimensional Z.functionField Y.functionField → ∀ (a : ℕ) (V : Z.Opens) (hV : IsAffineOpen V) (hη : genericPoint Z ∈ V) (hη' : genericPoint Y ∈ c ⁻¹ᵁ V) (y : Γ(Omega p' a, c ⁻¹ᵁ V)), letI := algΓ p; letI := algΓ p'; formGermI p a hV hη hinst ((omegaTrace hc a).app V y) = GlobalTheory.W1.trDR ℂ Z.functionField Y.functionField (formGermI p' a (hV.preimage c) hη' hinst' y) := by
  intro Z Y _ _ p p' c hc _ _ inst inst' _ _ hinst hinst' hg hfd a V hV hη hη' y
  subst hinst hinst'
  letI := ffAlg p; letI := ffAlg p'
  haveI : CharZero Z.functionField := charZero_of_injective_algebraMap (algebraMap ℂ Z.functionField).injective
  haveI : Algebra.IsSeparable Z.functionField Y.functionField := Algebra.IsAlgebraic.isSeparable_of_perfectField
  have hT := UpperTheory.exists_deRhamTrace_of_separable ℂ Z.functionField Y.functionField
  have hspec : GlobalTheory.W1.IsTrDR ℂ Z.functionField Y.functionField (GlobalTheory.W1.trDR ℂ Z.functionField Y.functionField) := by
    unfold GlobalTheory.W1.trDR; rw [dite_eq_left hT]; exact hT.choose_spec
  obtain ⟨z, rfl⟩ := toOm_surjective (s := p') (j := a) (hV.preimage c) y
  change formGerm p a hV hη _ = GlobalTheory.W1.trDR ℂ _ _ (formGerm p' a (hV.preimage c) hη' _)
  rw [omegaTrace_app_toOm hc a hV, formGerm_toOm, formGerm_toOm]
  refine formOm_induction (P := fun z ↦ (semiHom_germSec p hη).mDR
      ((formTraceU hc hV a z : OmU p V a) : DR ℂ (Sec p V)) =
    GlobalTheory.W1.trDR ℂ _ _ ((semiHom_germSec p' hη').mDR (z : DR ℂ (Sec p' (c ⁻¹ᵁ V))))) hc hV ?_ ?_ ?_ z
  · simp only [map_zero, ZeroMemClass.coe_zero]
  · intro y z hy hz
    simp only [map_add (f := _), Submodule.coe_add, hy, hz]
  · intro b' x
    have e : ((formPull hc V a x : OmU p' (c ⁻¹ᵁ V) a) : DR ℂ (Sec p' (c ⁻¹ᵁ V))) =
        (semiHom_appSec hc V).mDR (x : DR ℂ (Sec p V)) := SemiHom.coe_mOm _ x
    rw [formTraceU_smul_formPull, Submodule.coe_smul, Submodule.coe_smul, SemiHom.mDR_smul,
      SemiHom.mDR_smul, e, mDR_square (semiHom_germSec p hη) (semiHom_appSec hc V)
        (semiHom_germSec p' hη') (fun b ↦ hg V hη hη' b), hspec]
    exact congrArg (· • _) (UpperTheory.Cb.germ_comap_eq_algebraMap_germ_of_finite_etale Z Y p p' c hc hg V hV hη hη' b')
end
