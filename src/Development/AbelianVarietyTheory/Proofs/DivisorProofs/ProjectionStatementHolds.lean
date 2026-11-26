module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneFormMapRowThreeLevelOfCharacterisation
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalisationEqStdAtOfCongruentOneAtPrime

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectionStatementHolds
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LineNorm
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv actR)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FlatModel.Proj

theorem exists_dual {O κ : Type} [CommRing O] [Fintype κ] [DecidableEq κ] (b : Module.Basis κ ℤ O)
    (hd : Algebra.discr ℤ b ≠ 0) :
    ∃ c : κ → O, (∀ a k, a * c k = ∑ i, b.repr (a * b i) k • c i) ∧
      ∑ i, c i * b i = ((Algebra.discr ℤ b : ℤ) : O) := by
  set T := Algebra.traceMatrix ℤ b with hT
  have hd' : T.det ≠ 0 := hd
  have nd : ∀ x y : O, (∀ l, Algebra.trace ℤ O (x * b l) = Algebra.trace ℤ O (y * b l)) → x = y := by
    intro x y h
    rw [← sub_eq_zero]
    have h1 : Matrix.vecMul (b.repr (x - y)) T = 0 := by
      funext l
      have h2 : Algebra.trace ℤ O ((x - y) * b l) = 0 := by rw [sub_mul, map_sub, h, sub_self]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← b.sum_repr (x - y), Finset.sum_mul, map_sum] at h2
      simp only [smul_mul_assoc, map_smul, smul_eq_mul] at h2
      exact h2
    have h3 := Matrix.eq_zero_of_vecMul_eq_zero hd' h1
    apply b.repr.injective
    rw [map_zero]
    exact DFunLike.coe_injective h3
  let c : κ → O := fun i => ∑ j, T.adjugate i j • b j
  have hc : ∀ i k, Algebra.trace ℤ O (c i * b k) = if i = k then T.det else 0 := by
    intro i k
    have h1 := congrFun (congrFun (Matrix.adjugate_mul T) i) k
    simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, _root_.mul_one, mul_zero] at h1
    rw [← h1]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [c, Finset.sum_mul, map_sum, smul_mul_assoc, map_smul, smul_eq_mul]
    rfl
  have hc2 : ∀ i x, Algebra.trace ℤ O (c i * x) = T.det * b.repr x i := by
    intro i x
    conv_lhs => rw [← b.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Finset.mul_sum, map_sum, mul_smul_comm, map_smul, hc, smul_eq_mul, mul_ite, mul_zero]
    simp [mul_comm]
  refine ⟨c, fun a k => nd _ _ fun l => ?_, nd _ _ fun l => ?_⟩
  · rw [mul_comm a, _root_.mul_assoc, hc2]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Finset.sum_mul, map_sum, smul_mul_assoc, map_smul, hc, smul_eq_mul, mul_ite, mul_zero]
    simp [mul_comm]
  · set_option synthInstance.maxHeartbeats 100000 in
      simp only [Finset.sum_mul, map_sum, _root_.mul_assoc, hc2]
    rw [← zsmul_eq_mul, map_smul, Algebra.trace_eq_matrix_trace b, smul_eq_mul, Matrix.trace, ← Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, mul_comm]

section Lin

variable {O S M κ : Type} [CommRing O] [CommRing S] [AddCommGroup M] [Module S M] [Fintype κ]
  (ρ : O →+* Module.End S M) (σ : O →+* S) (b : Module.Basis κ ℤ O) (c : κ → O)

theorem eig_proj (hc : ∀ a k, a * c k = ∑ i, b.repr (a * b i) k • c i) (a : O) (v : M) :
    ρ a (∑ i, σ (c i) • ρ (b i) v) = σ a • ∑ i, σ (c i) • ρ (b i) v := by
  have h1 : ∀ i, ρ a (ρ (b i) v) = ∑ k, b.repr (a * b i) k • ρ (b k) v := fun i => by
    rw [← Module.End.mul_apply, ← map_mul]
    conv_lhs => rw [← b.sum_repr (a * b i)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, h1, Finset.smul_sum, smul_smul, ← map_mul, hc, map_zsmul, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  rw [smul_comm, smul_assoc]

theorem proj_eig {d : ℤ} (hc : ∑ i, c i * b i = (d : O)) (v : M) (hv : ∀ a, ρ a v = σ a • v) :
    ∑ i, σ (c i) • ρ (b i) v = (d : S) • v := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hv, smul_smul, ← map_mul, ← Finset.sum_smul, ← map_sum, hc, map_intCast]

end Lin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X}

theorem eq_of_comb {S : Type} [CommRing S] {x : Sp S ⟶ X} {m : ℕ} (T : Fin m → TanM x t.G) {w : Fin m → S}
    {u : Sp (DualNumber S) ⟶ t.G.left} (h : IsCombAtG t x (fun i => (tv (T i)).left) w u) :
    u = (tv (∑ i, w i • T i)).left := by
  obtain ⟨y, hy, rfl⟩ := h
  obtain ⟨z, hz, e⟩ := (GlobalTheory.LieMet.isComb_iff T w _).2 rfl
  rw [← e]
  have : y = z := funext fun i => Over.OverMorphism.ext ((hy i).trans (hz i).symm)
  rw [this]

end GlobalTheory.FlatModel.Proj

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClopenGeometricPointsRootOfUnityEqUnit
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClopenGeometricPointsRootOfUnityEqUnit
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.UnitLocus

theorem mem_basicOpen_iff {X : Scheme.{0}} {k : Type} [Field k] (g : Sp k ⟶ X) (s : Γ(X, ⊤)) :
    g (default : PrimeSpectrum k) ∈ X.basicOpen s ↔ IsUnit (g.appTop.hom s) := by
  have p : g ⁻¹ᵁ X.basicOpen s = (Sp k).basicOpen (g.appTop.hom s) := Scheme.preimage_basicOpen g s
  constructor
  · intro H
    refine RingedSpace.isUnit_of_isUnit_germ (Sp k).toRingedSpace ⊤ _ fun y hy => ?_
    have : y ∈ (Sp k).basicOpen (g.appTop.hom s) := by
      rw [← p]
      have e : y = (default : PrimeSpectrum k) := Subsingleton.elim (α := PrimeSpectrum k) _ _
      rw [e]
      exact H
    exact ((Sp k).mem_basicOpen _ y hy).1 this
  · intro H
    have : (default : PrimeSpectrum k) ∈ g ⁻¹ᵁ X.basicOpen s := by
      rw [p, Scheme.basicOpen_of_isUnit _ H]; trivial
    exact this

theorem exists_geometricPoint {X : Scheme.{0}} (x : X) :
    ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (g : Sp k ⟶ X), g (default : PrimeSpectrum k) = x := by
  refine ⟨AlgebraicClosure (X.residueField x), inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) (AlgebraicClosure (X.residueField x)))) ≫
      X.fromSpecResidueField x, ?_⟩
  exact Scheme.fromSpecResidueField_apply x _

theorem avg_cases {R : Type} [CommRing R] [IsDomain R] {n : ℕ} {m w : R} (hm : m * n = 1) (hw : w ^ n = 1) :
    (w = 1 → m * ∑ i ∈ Finset.range n, w ^ i = 1) ∧ (w ≠ 1 → m * ∑ i ∈ Finset.range n, w ^ i = 0) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simpa [h] using hm
  · have h₀ : (∑ i ∈ Finset.range n, w ^ i) * (w - 1) = 0 := by rw [geom_sum_mul, hw, sub_self]
    rw [(mul_eq_zero.1 h₀).resolve_right (sub_ne_zero.2 h), mul_zero]

end GlobalTheory.UnitLocus

namespace GlobalTheory


open UnitLocus in
theorem loc_units_eq :
    ∀ (X : Scheme.{0}) (N : ℕ) (c₀ u : Γ(X, ⊤)ˣ), IsUnit (N : Γ(X, ⊤)) → c₀ ^ N = 1 → (∀ (k : Type) [Field k] [IsAlgClosed k] (g : Sp k ⟶ X), Units.map g.appTop.hom.toMonoidHom u ^ N = 1) → GlobalTheory.HkClopen.Loc (S := X) (fun (k : Type) [Field k] [IsAlgClosed k] (g : Sp k ⟶ X) => Units.map g.appTop.hom.toMonoidHom c₀ = Units.map g.appTop.hom.toMonoidHom u) := by
  intro X N c₀ u hN hc hu
  obtain ⟨m, hm⟩ := hN.exists_left_inv
  let w : Γ(X, ⊤) := (c₀ * u⁻¹).val
  let e : Γ(X, ⊤) := m * ∑ i ∈ Finset.range N, w ^ i
  have key : ∀ (k : Type) [Field k] [IsAlgClosed k] (g : Sp k ⟶ X),
      (g (default : PrimeSpectrum k) ∈ X.basicOpen e ↔
        Units.map g.appTop.hom.toMonoidHom c₀ = Units.map g.appTop.hom.toMonoidHom u) ∧
      (g (default : PrimeSpectrum k) ∈ X.basicOpen (1 - e) ↔
        ¬ Units.map g.appTop.hom.toMonoidHom c₀ = Units.map g.appTop.hom.toMonoidHom u) := by
    intro k _ _ g
    have : IsDomain Γ(Sp k, ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isDomain k
    have hval : g.appTop.hom w =
        (Units.map g.appTop.hom.toMonoidHom c₀ * (Units.map g.appTop.hom.toMonoidHom u)⁻¹).val := by
      rw [← map_inv, ← map_mul]; rfl
    have h1 : Units.map g.appTop.hom.toMonoidHom c₀ = Units.map g.appTop.hom.toMonoidHom u ↔
        g.appTop.hom w = 1 := by
      rw [hval, Units.val_eq_one, mul_inv_eq_one]
    have hw : g.appTop.hom w ^ N = 1 := by
      rw [hval, ← Units.val_pow_eq_pow_val, mul_pow, inv_pow, hu, ← map_pow, hc, map_one, inv_one,
        _root_.mul_one, Units.val_one]
    have hm' : g.appTop.hom m * N = 1 := by
      have := congrArg g.appTop.hom hm
      rwa [map_mul, map_natCast, map_one] at this
    have he : g.appTop.hom e = g.appTop.hom m * ∑ i ∈ Finset.range N, g.appTop.hom w ^ i := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [e, map_mul, map_sum, map_pow]
    obtain ⟨a, b⟩ := avg_cases hm' hw
    rw [mem_basicOpen_iff, mem_basicOpen_iff, h1, map_sub, map_one, he]
    by_cases h : g.appTop.hom w = 1
    · rw [a h]; simp [h]
    · rw [b h]; simp [h]
  refine ⟨X.basicOpen e, ⟨?_, (X.basicOpen e).isOpen⟩, fun k _ _ g => (key k g).1⟩
  have : (X.basicOpen e : Set X) = (X.basicOpen (1 - e) : Set X)ᶜ := by
    ext x
    obtain ⟨k, _, _, g, rfl⟩ := exists_geometricPoint x
    exact (key k g).1.trans (not_not.symm.trans (not_congr (key k g).2.symm))
  rw [this]
  exact (X.basicOpen (1 - e)).isOpen.isClosed_compl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClopenGeometricPointsRootOfUnityEqUnitStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClopen_geometricPoints_rootOfUnity_eq_unit : ∀ (X : Scheme.{0}) (N : ℕ) (c₀ u : Γ(X, ⊤)ˣ), IsUnit (N : Γ(X, ⊤)) → c₀ ^ N = 1 → (∀ (k : Type) [Field k] [IsAlgClosed k] (g : Sp k ⟶ X), Units.map g.appTop.hom.toMonoidHom u ^ N = 1) → GlobalTheory.HkClopen.Loc (S := X) (fun (k : Type) [Field k] [IsAlgClosed k] (g : Sp k ⟶ X) => Units.map g.appTop.hom.toMonoidHom c₀ = Units.map g.appTop.hom.toMonoidHom u) := by
  first | exact @GlobalTheory.loc_units_eq | exact GlobalTheory.loc_units_eq | (intros; apply GlobalTheory.loc_units_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GermMemRangeStalkOfPullbackMulLocalIso
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GermMemRangeStalkOfPullbackMulLocalIso
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

namespace GlobalTheory

theorem germToFunctionField_mem_range_stalk_of_mul_pull : ∀ (k : Type) [CommRing k] (Y X : Scheme.{0}) [IsIntegral Y] [IsIntegral X]
    (p : Y ⟶ Sp k) (σ : X ⟶ Y) (U : Y.Opens) [IsIso (σ ∣_ U)] [Nonempty U] (L : LB Y) (P N : LB X)
    (C : ProdChart P (L.pull σ) N) (J : H0 (σ ≫ p) P ⊤) (g : H0 (σ ≫ p) N ⊤) (s : H0 p L U),
    C.mul (H0.restr le_top J) (H0.pull σ le_rfl s) = H0.restr le_top g → ∀ x : X,
      Function.Bijective (σ.stalkMap x).hom → (∀ (a : P.ι) (ha : x ∈ P.U a), IsUnit (H0.germ a x (memTop x) ha J)) →
      ∀ (i : L.ι) (hi : σ x ∈ L.U i) [Nonempty (U ⊓ L.U i : Y.Opens)],
        Y.germToFunctionField (U ⊓ L.U i) (s.loc i) ∈ (algebraMap (Y.presheaf.stalk (σ x)) Y.functionField).range := by
  intro k _ Y X _ _ p σ U _ _ L P N C J g s hrel x hbij hJ i hi _
  obtain ⟨t, ha, hb, hc⟩ := C.cover x
  have hjx : σ x ∈ L.U (C.b t PUnit.unit) := mem_pull.1 hb
  have hξx : genericPoint X ⤳ x := (genericPoint_spec X).specializes trivial
  have hne : Nonempty (σ ⁻¹ᵁ U) := by
    obtain ⟨⟨y, hy⟩⟩ := ‹Nonempty U›
    obtain ⟨z, -⟩ := (σ ∣_ U).surjective ⟨y, hy⟩
    exact ⟨z⟩
  have hξU : genericPoint X ∈ σ ⁻¹ᵁ U := genericPoint_mem_opens _
  have hσξη : σ (genericPoint X) ⤳ genericPoint Y := by
    obtain ⟨z, hz⟩ := (σ ∣_ U).surjective ⟨genericPoint Y, genericPoint_mem_opens U⟩
    have e : σ z.1 = genericPoint Y := (morphismRestrict_base_coe σ U z).symm.trans (congrArg Subtype.val hz)
    rw [← e]
    exact σ.base.hom.map_specializes ((genericPoint_spec X).specializes trivial)
  have hσξ : σ (genericPoint X) ∈ U ⊓ L.U (C.b t PUnit.unit) :=
    ⟨hξU, (σ.base.hom.map_specializes hξx).mem_open (L.U _).isOpen hjx⟩
  have haξ := hξx.mem_open (P.U (C.a t)).isOpen ha
  have hbξ := hξx.mem_open ((L.pull σ).U (C.b t)).isOpen hb
  have hcξ := hξx.mem_open (N.U (C.c t)).isOpen hc
  have e1 := congrArg (H0.germ (C.c t) (genericPoint X) hξU hcξ) hrel
  rw [C.germ_mul _ _ t _ hξU haξ hbξ hcξ, H0.germ_restr, H0.germ_restr, H0.germ_pull] at e1
  have hsp (B : LB X) (f : H0 (σ ≫ p) B ⊤) (a : B.ι) (hx : x ∈ B.U a) (hξ : genericPoint X ∈ B.U a) :
      H0.germ a (genericPoint X) (memTop _) hξ f =
        X.presheaf.stalkSpecializes hξx (H0.germ a x (memTop x) hx f) := by
    rw [H0.germ_apply, H0.germ_apply]
    exact (X.presheaf.germ_stalkSpecializes_apply _ hξx _).symm
  have hJu := hJ (C.a t) ha
  obtain ⟨h, hh⟩ := hbij.2 (H0.germ (C.c t) x (memTop x) hc g * ↑hJu.unit⁻¹)
  have : Nonempty (L.U (C.b t PUnit.unit)) := ⟨⟨σ x, hjx⟩⟩
  have := nonempty_inf_of_isIntegral U (L.U (C.b t PUnit.unit))
  refine germToFunctionField_mem_range_stalk_of_secOn (LB.coord_mem s) hi hjx ⟨h, ?_⟩
  let φ : Y.functionField →+* X.presheaf.stalk (genericPoint X) :=
    (σ.stalkMap (genericPoint X)).hom.comp (Y.presheaf.stalkSpecializes hσξη).hom
  refine φ.injective ?_
  have eA : φ (algebraMap _ _ h) = X.presheaf.stalkSpecializes hξx (σ.stalkMap x h) := by
    change (σ.stalkMap _).hom ((Y.presheaf.stalkSpecializes ((genericPoint_spec Y).specializes trivial) ≫
      Y.presheaf.stalkSpecializes hσξη).hom h) = _
    rw [TopCat.Presheaf.stalkSpecializes_comp]
    exact Scheme.Hom.stalkSpecializes_stalkMap_apply σ _ _ hξx h
  have eB : φ (Y.germToFunctionField _ (LB.coord s (C.b t PUnit.unit))) =
      (σ.stalkMap (genericPoint X)).hom (H0.germ (C.b t PUnit.unit) (σ (genericPoint X)) hσξ.1 hσξ.2 s) := by
    change (σ.stalkMap _).hom (Y.presheaf.stalkSpecializes hσξη
      (Y.presheaf.germ _ (genericPoint Y) _ (LB.coord s _))) = _
    rw [Y.presheaf.germ_stalkSpecializes_apply _ hσξη]
    rfl
  rw [eA, eB, hh]
  rw [hsp P J (C.a t) ha haξ, hsp N g (C.c t) hc hcξ] at e1
  have hu : IsUnit (X.presheaf.stalkSpecializes hξx (H0.germ (C.a t) x (memTop x) ha J)) := hJu.map _
  apply hu.mul_left_cancel
  rw [e1, ← map_mul]
  exact congrArg _ (by rw [mul_left_comm, hJu.mul_val_inv, mul_one])

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GermMemRangeStalkOfPullbackMulLocalIsoStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.germ_mem_range_stalk_of_pullback_mul_localIso : ∀ (k : Type) [CommRing k] (Y X : Scheme.{0}) [IsIntegral Y] [IsIntegral X]
    (p : Y ⟶ Sp k) (σ : X ⟶ Y) (U : Y.Opens) [IsIso (σ ∣_ U)] [Nonempty U] (L : LB Y) (P N : LB X)
    (C : ProdChart P (L.pull σ) N) (J : H0 (σ ≫ p) P ⊤) (g : H0 (σ ≫ p) N ⊤) (s : H0 p L U),
    C.mul (H0.restr le_top J) (H0.pull σ le_rfl s) = H0.restr le_top g → ∀ x : X,
      Function.Bijective (σ.stalkMap x).hom → (∀ (a : P.ι) (ha : x ∈ P.U a), IsUnit (H0.germ a x (memTop x) ha J)) →
      ∀ (i : L.ι) (hi : σ x ∈ L.U i) [Nonempty (U ⊓ L.U i : Y.Opens)],
        Y.germToFunctionField (U ⊓ L.U i) (s.loc i) ∈ (algebraMap (Y.presheaf.stalk (σ x)) Y.functionField).range := by
  first | exact @GlobalTheory.germToFunctionField_mem_range_stalk_of_mul_pull | exact GlobalTheory.germToFunctionField_mem_range_stalk_of_mul_pull | (intros; apply GlobalTheory.germToFunctionField_mem_range_stalk_of_mul_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComparisonReadableAtPlace
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT Formalism.IndefR.Datum GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.OnCmp
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist GlobalTheory.FlatVecSum
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open GlobalTheory.BigOn.Exp.SerBase
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp

section GenericCmp

variable {O : Type} [CommRing O] [IsDomain O] {M : Type} [AddCommGroup M] [Module (FractionRing O) M] [Module O M]
  [IsScalarTower O (FractionRing O) M] [FiniteDimensional (FractionRing O) M]
  {L : Type} [Field L] [Algebra O L] {eK : FractionRing O →+* ℂ} {G : Type}

theorem exists_smul_eq_sum_finBasis (x : L ⊗[O] M) : ∃ d : O, d ≠ 0 ∧ ∃ c : _ → L,
    d • x = ∑ a, c a ⊗ₜ Module.finBasis (FractionRing O) M a := by
  set v := Module.finBasis (FractionRing O) M
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨1, one_ne_zero, 0, by simp⟩
  | add x y hx hy =>
    obtain ⟨d, hd, c, e⟩ := hx
    obtain ⟨d', hd', c', e'⟩ := hy
    refine ⟨d * d', mul_ne_zero hd hd', d' • c + d • c', ?_⟩
    rw [smul_add, mul_smul d d' y, mul_comm, mul_smul, e, e']
    simp [Finset.smul_sum, TensorProduct.add_tmul, Finset.sum_add_distrib, TensorProduct.smul_tmul']
  | tmul a f =>
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) fun c => v.repr f c
    choose y hy using hd
    refine ⟨d, nonZeroDivisors.coe_ne_zero d, fun c => y c • a, ?_⟩
    rw [← TensorProduct.tmul_smul]
    conv_lhs => rw [← v.sum_repr f]
    rw [Finset.smul_sum, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [TensorProduct.smul_tmul, ← algebraMap_smul (FractionRing O) (y c), hy, smul_assoc]

variable (rd : M →ₛₗ[eK] (G → ℂ)) (eL : L →+* ℂ)
  (hL : ∀ c : O, eL (algebraMap O L c) = eK (algebraMap O (FractionRing O) c))

theorem readExt_eq_smul_of_read
    (hF : ∀ (n : ℕ) (v : Fin n → M), LinearIndependent (FractionRing O) v → LinearIndependent ℂ fun c => rd (v c))
    (s t : L ⊗[O] M) (a : ℂ) (h : readExt rd eL hL s = a • readExt rd eL hL t) (h0 : readExt rd eL hL s ≠ 0) :
    ∃ b : L, eL b = a ∧ s = b • t := by
  set R := readExt rd eL hL with hR
  set v := Module.finBasis (FractionRing O) M
  have hne : ∀ d : O, d ≠ 0 → eL (algebraMap O L d) ≠ 0 := fun d hd => by
    rw [hL]
    exact (map_ne_zero eK).2 ((map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).2 hd)
  have hsm : ∀ (d : O) (x : L ⊗[O] M), R (d • x) = eL (algebraMap O L d) • R x := fun d x => by
    rw [← algebraMap_smul L d x, hR, readExt_smul]
  have hsum : ∀ c : _ → L, R (∑ k, c k ⊗ₜ v k) = ∑ k, eL (c k) • rd (v k) := fun c => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    rfl
  obtain ⟨d, hd, c, es⟩ := exists_smul_eq_sum_finBasis s
  obtain ⟨d', hd', c', et⟩ := exists_smul_eq_sum_finBasis t
  have hcoef : ∀ k, eL (algebraMap O L d') * eL (c k) = a * (eL (algebraMap O L d) * eL (c' k)) := fun k => by
    have e1 : ∑ k, (eL (algebraMap O L d') * eL (c k) - a * (eL (algebraMap O L d) * eL (c' k))) • rd (v k) = 0 := by
      have h1 : eL (algebraMap O L d') • R (d • s) = a • eL (algebraMap O L d) • R (d' • t) := by
        rw [hsm, hsm, h]
        simp only [smul_smul]
        congr 1
        ring
      rw [es, et, hsum, hsum, Finset.smul_sum, Finset.smul_sum, Finset.smul_sum] at h1
      simp only [sub_smul, Finset.sum_sub_distrib, mul_smul]
      rw [h1, sub_self]
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 (hF _ v v.linearIndependent) _ e1 k)
  obtain ⟨k, hk⟩ : ∃ k, c k ≠ 0 := by
    by_contra hc
    push_neg at hc
    apply h0
    have h2 : eL (algebraMap O L d) • R s = 0 := by
      rw [← hsm, es, hsum]
      simp [hc]
    exact (smul_eq_zero.1 h2).resolve_left (hne d hd)
  have hl : eL (algebraMap O L d') * eL (c k) ≠ 0 := mul_ne_zero (hne d' hd') ((map_ne_zero eL).2 hk)
  have hr : eL (algebraMap O L d) * eL (c' k) ≠ 0 := fun h3 => hl (by rw [hcoef k, h3, mul_zero])
  refine ⟨(algebraMap O L d' * c k) / (algebraMap O L d * c' k), ?_, ?_⟩
  · rw [map_div₀, map_mul, map_mul, hcoef k, mul_div_assoc, div_self hr, mul_one]
  · have hb : eL ((algebraMap O L d' * c k) / (algebraMap O L d * c' k)) = a := by
      rw [map_div₀, map_mul, map_mul, hcoef k, mul_div_assoc, div_self hr, mul_one]
    apply readExt_injective rd eL hL hF
    rw [readExt_smul, hb, ← hR, h]

end GenericCmp

end GlobalTheory.BigOn.Exp

namespace GlobalTheory.BigOn.Exp.SerBase


end GlobalTheory.BigOn.Exp.SerBase
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelStructureBaseChangeLabelsTorsion
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelStructureBaseChangeLabelsTorsion
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LevelCarry

theorem linComb_prod' {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {T : Over S} {n : ℕ}
    (y : Fin n → (T ⟶ A)) (a : Fin n → ℕ) : linComb y a = ∏ i, y i ^ a i := List.prod_ofFn

theorem unitOn_zpow' {R : Type} [CommRing R] (u : Rˣ) (n : ℤ) : unitOn (u ^ n) = unitOn u ^ n :=
  map_zpow _ _ _

theorem unitOn_inj' {R : Type} [CommRing R] : Function.Injective (unitOn (R := R)) := by
  intro a b h
  apply Units.ext
  have h' := congrArg Units.val h
  simp only [unitOn, Units.coe_map] at h'
  exact (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm.injective h'

end GlobalTheory.LevelCarry


open GlobalTheory.LevelCarry in
theorem GlobalTheory.levelPoint_baseChange_label : ∀ (K C : Type) [Field K] [Field C] [IsAlgClosed C] (f : K →+* C) (P : PolAV (Sp K))
    (P' : PolAV (Sp C)) (io : (Over.mk (spMap f) ⟶ P.A) ≃* (baseOver (Sp C) ⟶ P'.A)),
    (∀ (k : ℕ) a b (z : Γ(Sp C, ⊤)ˣ), WeilIs P'.A P'.L k (io a) (io b) z → WeilIs P.A P.L k a b z) →
    ∀ (g k : ℕ) (hg : P'.g = g) (ζ : Cˣ) (lev : Out.Level P' k (unitOn ζ)), 2 ≤ k →
      IsPrimitiveRoot ζ k ∧
      (∀ a b, io.symm (levelPoint lev hg (a + b)) = io.symm (levelPoint lev hg a) * io.symm (levelPoint lev hg b)) ∧
      Function.Injective (fun a => io.symm (levelPoint lev hg a)) ∧
      (∀ z : Over.mk (spMap f) ⟶ P.A, z ^ k = 1 → ∃ a, io.symm (levelPoint lev hg a) = z) ∧
      ∀ i j, WeilIs P.A P.L k (io.symm (levelPoint lev hg (Pi.single i 1))) (io.symm (levelPoint lev hg (Pi.single j 1)))
        (unitOn (ζ ^ stdSymp g i j)) := by
  intro K C _ _ _ f P P' io hW g k hg ζ lev hk
  subst hg
  have := P'.isAb.comm
  have hk0 : NeZero k := ⟨by omega⟩
  have E : ∀ c : Fin (2 * P'.g) → ℕ,
      linComb (fun i => (Over.homMk (𝟙 _) (by simp) : Over.mk (𝟙 _) ⟶ baseOver _) ≫ lev.pt i) c =
      linComb lev.pt c := fun c => congrArg (linComb · _) (funext fun i => Category.id_comp (lev.pt i))
  have LP : ∀ a, levelPoint lev rfl a = ∏ i, lev.pt i ^ (a i).val := fun a => by
    rw [levelPoint_rfl]; exact linComb_prod' _ _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact IsPrimitiveRoot.of_map_of_injective
      (f := Units.map (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom.toMonoidHom) lev.prim unitOn_inj'
  · intro a b
    rw [← map_mul]
    congr 1
    rw [LP, LP, LP, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← pow_add, pow_eq_pow_mod ((a i).val + (b i).val) (lev.torsion i), Pi.add_apply, ZMod.val_add]
  · have inj : Function.Injective (levelPoint lev rfl) := by
      intro a b h
      have h₀ := lev.indep C (𝟙 _) (fun i => ⟨(a i).val, ZMod.val_lt _⟩) (fun i => ⟨(b i).val, ZMod.val_lt _⟩)
        ((E _).trans (h.trans (E _).symm))
      exact funext fun i => ZMod.val_injective k (congrArg Fin.val (congrFun h₀ i))
    exact io.symm.injective.comp inj
  · intro z hz
    have hz' : (io z) ^ k = 1 := by rw [← map_pow, hz, map_one]
    obtain ⟨c, hc⟩ := lev.span C (𝟙 _) (io z) hz'
    refine ⟨fun i => ((c i : ℕ) : ZMod k), ?_⟩
    rw [MulEquiv.symm_apply_eq, levelPoint_rfl, Level.toPt]
    exact (congrArg (linComb lev.pt) (funext fun i => ZMod.val_natCast_of_lt (c i).isLt)).trans
      ((E _).symm.trans hc)
  · intro i j
    haveI : Fact (1 < k) := ⟨by omega⟩
    have hs : ∀ i, levelPoint lev rfl (Pi.single i 1) = lev.pt i := fun i => by
      rw [LP, Finset.prod_eq_single i]
      · rw [Pi.single_eq_same, ZMod.val_one, pow_one]
      · intro j _ hj
        rw [Pi.single_eq_of_ne hj, ZMod.val_zero, pow_zero]
      · intro h; exact absurd (Finset.mem_univ i) h
    rw [hs, hs]
    apply hW
    rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, unitOn_zpow']
    exact lev.pairing i j
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelStructureBaseChangeLabelsTorsionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelStructure_baseChange_labels_torsion : ∀ (K C : Type) [Field K] [Field C] [IsAlgClosed C] (f : K →+* C) (P : PolAV (Sp K))
    (P' : PolAV (Sp C)) (io : (Over.mk (spMap f) ⟶ P.A) ≃* (baseOver (Sp C) ⟶ P'.A)),
    (∀ (k : ℕ) a b (z : Γ(Sp C, ⊤)ˣ), WeilIs P'.A P'.L k (io a) (io b) z → WeilIs P.A P.L k a b z) →
    ∀ (g k : ℕ) (hg : P'.g = g) (ζ : Cˣ) (lev : Out.Level P' k (unitOn ζ)), 2 ≤ k →
      IsPrimitiveRoot ζ k ∧
      (∀ a b, io.symm (levelPoint lev hg (a + b)) = io.symm (levelPoint lev hg a) * io.symm (levelPoint lev hg b)) ∧
      Function.Injective (fun a => io.symm (levelPoint lev hg a)) ∧
      (∀ z : Over.mk (spMap f) ⟶ P.A, z ^ k = 1 → ∃ a, io.symm (levelPoint lev hg a) = z) ∧
      ∀ i j, WeilIs P.A P.L k (io.symm (levelPoint lev hg (Pi.single i 1))) (io.symm (levelPoint lev hg (Pi.single j 1)))
        (unitOn (ζ ^ stdSymp g i j)) := by
  first | exact @GlobalTheory.levelPoint_baseChange_label | exact GlobalTheory.levelPoint_baseChange_label | (intros; apply GlobalTheory.levelPoint_baseChange_label <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionSymplecticLabelsOfLevelStructure
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionSymplecticLabelsOfLevelStructure
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.MBLow

theorem qLevel_of_torsion_labels : AllVC fun {V} _ _ _ {D} {A} {G} _ _ U {C} _ _ {N} ν => ∀ (g k : ℕ), 1 ≤ k → ∀ (ζ : Cˣ) (pt : (Fin (2 * g) → ZMod k) → (TFK (R := V) C ⟶ A.A)), IsPrimitiveRoot ζ k → (∀ a b, pt (a + b) = pt a * pt b) → Function.Injective pt → (∀ z : TFK (R := V) C ⟶ A.A, z ^ k = 1 → ∃ a, pt a = z) → (∀ i j, WeilIs A.A A.L k (pt (Pi.single i 1)) (pt (Pi.single j 1)) (unitOn (ζ ^ stdSymp g i j))) → ∃ (p : (Fin (2 * g) → ZMod k) → QkPt D.toPre C k) (q : (Fin (2 * g) → ZMod k) → N.QT k), QLevel N g k ζ q ∧ ∀ a, ν.QPt (p a) (q a) ∧ QkToAkU U.toUnifPre C k (p a) (pt a) := by
  intro V _ _ _ _ hV D A G _ _ hG U C _ _ _ _ _ _ hC N ν hI
  intro g k hk ζ pt hζ hadd hinj hsurj hw
  obtain ⟨f, hf1, hf2, hf3, hf4, hf5⟩ := GlobalTheory.ZH.uTors_closed V hV A G D U C k hk
  obtain ⟨-, -, hAdd, -, hQ⟩ := GlobalTheory.Ex.GtValues.points_correspond V D.toPre D.psi_even D.tau_bimult C N ν
  have hWp := GlobalTheory.WeilValues.weil_eq_values GlobalTheory.Ex.GtValues.points_correspond
    (GlobalTheory.Ex.brFam GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2) V D.toPre D.psi_even D.tau_bimult C N ν k hk
  obtain ⟨hQ1, hQ2, hQ3⟩ := hQ k

  have hmul : ∀ (p₁ p₂ p₃ : QkPt D.toPre C k) (q₁ q₂ : N.QT k), ν.QPt p₁ q₁ → ν.QPt p₂ q₂ → ν.QPt p₃ (q₁ * q₂) →
      f p₃ = f p₁ * f p₂ := by
    intro p₁ p₂ p₃ q₁ q₂ h₁ h₂ h₃
    apply hf4
    refine ⟨p₃, ?_, ?_, ?_⟩
    · rw [← h₃.1, ← h₁.1, ← h₂.1]
      exact map_add ν.eX _ _
    · exact (hAdd _ _ _ _ _ _ h₁.2 h₂.2 h₃.2).2 rfl
    · exact (hQ3 p₃ p₃ _ _ h₃ h₃).2 (by exact ⟨0, by simp, by simp⟩)

  have hpt0 : pt 0 = 1 := by
    have h := hadd 0 0
    rw [add_zero] at h
    exact (mul_eq_left.1 h.symm)
  have hptn : ∀ (n : ℕ) a, pt (n • a) = pt a ^ n := by
    intro n a
    induction n with
    | zero => simpa using hpt0
    | succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]
  have hkt : ∀ a, pt a ^ k = 1 := by
    intro a
    have : k • a = 0 := by
      funext i
      simp [nsmul_eq_mul]
    rw [← hptn, this, hpt0]
  have hex : ∀ a, ∃ p, f p = pt a := fun a => hf2 (pt a) (hkt a)
  choose p hp using hex
  have hexq : ∀ a, ∃ q, ν.QPt (p a) q := fun a => (hQ1 (p a)).exists
  choose q hq using hexq

  have hpow : ∀ (q' : N.QT k) (p' : QkPt D.toPre C k), ν.QPt p' q' → ∀ (n : ℕ) (pn : QkPt D.toPre C k),
      ν.QPt pn (q' ^ n) → f pn = f p' ^ n := by
    intro q' p' hp' n
    induction n with
    | zero =>
      intro pn hpn
      rw [pow_zero] at hpn ⊢
      have h := hmul pn pn pn 1 1 hpn hpn (by rw [_root_.mul_one]; exact hpn)
      exact (mul_eq_left.1 h.symm)
    | succ n ih =>
      intro pn hpn
      obtain ⟨pm, hpm⟩ := hQ2 (q' ^ n)
      rw [pow_succ] at hpn
      rw [hmul pm p' pn _ _ hpm hp' hpn, ih pm hpm, pow_succ]
  have hqk : ∀ q' : N.QT k, q' ^ k = N.qTriv k (Multiplicative.toAdd q'.1.1) := by
    intro q'
    apply Subtype.ext
    apply Prod.ext
    · show q'.1.1 ^ k = Multiplicative.ofAdd (k • Multiplicative.toAdd q'.1.1)
      rw [ofAdd_nsmul, ofAdd_toAdd]
    · show q'.1.2 ^ k = N.io (Multiplicative.toAdd q'.1.1)
      exact (N.mem_QT).1 q'.2
  refine ⟨p, q, ⟨hζ, ?_, ?_, ?_, ?_⟩, fun a => ⟨hq a, (hf1 _ _).2 (hp a).symm⟩⟩
  · intro a b
    obtain ⟨p'', hp''⟩ := hQ2 (q a * q b)
    have h : f p'' = f (p (a + b)) := by rw [hmul _ _ _ _ _ (hq a) (hq b) hp'', hp, hp, hp, hadd]
    exact (hQ3 _ _ _ _ hp'' (hq (a + b))).1 ((hf3 _ _).1 h)
  · intro a b h
    apply hinj
    rw [← hp, ← hp]
    exact (hf3 _ _).2 ((hQ3 _ _ _ _ (hq a) (hq b)).2 h)
  · intro q'
    obtain ⟨p', hp'⟩ := hQ2 q'
    obtain ⟨p₀, hp₀⟩ := hQ2 1
    obtain ⟨pk, hpk⟩ := hQ2 (q' ^ k)
    have h0 := hpow q' p' hp' 0 p₀ (by rw [pow_zero]; exact hp₀)
    have hk' := hpow q' p' hp' k pk hpk
    have heq : N.QEq 1 (q' ^ k) := (N.qEq_iff _ _).2 ⟨_, by rw [_root_.one_mul]; exact hqk q'⟩
    have h1 : f p₀ = f pk := (hf3 _ _).2 ((hQ3 _ _ _ _ hp₀ hpk).2 heq)
    have htor : f p' ^ k = 1 := by rw [← hk', ← h1, h0, pow_zero]
    obtain ⟨a, ha⟩ := hsurj (f p') htor
    refine ⟨a, (hQ3 _ _ _ _ (hq a) hp').1 ((hf3 _ _).1 ?_)⟩
    rw [hp, ha]
  · intro i j
    have h := hw i j
    rw [← hp, ← hp] at h
    have h' := (hf5 _ _ (ζ ^ stdSymp g i j)).2 h
    exact Units.ext ((hWp _ _ _ _ _ (hq _) (hq _)).1 h').symm

end GlobalTheory.MBLow
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionSymplecticLabelsOfLevelStructureStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionSymplecticLabels_of_levelStructure : AllVC fun {V} _ _ _ {D} {A} {G} _ _ U {C} _ _ {N} ν => ∀ (g k : ℕ), 1 ≤ k → ∀ (ζ : Cˣ) (pt : (Fin (2 * g) → ZMod k) → (TFK (R := V) C ⟶ A.A)), IsPrimitiveRoot ζ k → (∀ a b, pt (a + b) = pt a * pt b) → Function.Injective pt → (∀ z : TFK (R := V) C ⟶ A.A, z ^ k = 1 → ∃ a, pt a = z) → (∀ i j, WeilIs A.A A.L k (pt (Pi.single i 1)) (pt (Pi.single j 1)) (unitOn (ζ ^ stdSymp g i j))) → ∃ (p : (Fin (2 * g) → ZMod k) → QkPt D.toPre C k) (q : (Fin (2 * g) → ZMod k) → N.QT k), QLevel N g k ζ q ∧ ∀ a, ν.QPt (p a) (q a) ∧ QkToAkU U.toUnifPre C k (p a) (pt a) := by
  first | exact @GlobalTheory.MBLow.qLevel_of_torsion_labels | exact GlobalTheory.MBLow.qLevel_of_torsion_labels | (intros; apply GlobalTheory.MBLow.qLevel_of_torsion_labels <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaLiftIdempotentForm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaLiftIdempotentForm
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.UnitaryMove

section Generic

variable {A : Type} [CommRing A] {n : ℕ} (c : A →+* A)

def ct (X : Matrix (Fin n) (Fin n) A) : Matrix (Fin n) (Fin n) A := (X.map c).transpose

theorem ct_add (X Y : Matrix (Fin n) (Fin n) A) : ct c (X + Y) = ct c X + ct c Y := by
  simp only [ct, Matrix.map_add _ (map_add c), Matrix.transpose_add]

theorem ct_smul (a : A) (X : Matrix (Fin n) (Fin n) A) : ct c (a • X) = c a • ct c X := by
  ext i j
  simp [ct]

theorem ct_one : ct c (1 : Matrix (Fin n) (Fin n) A) = 1 := by
  rw [ct, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]

theorem ct_mul (X Y : Matrix (Fin n) (Fin n) A) : ct c (X * Y) = ct c Y * ct c X := by
  rw [ct, ct, ct, Matrix.map_mul, Matrix.transpose_mul]

theorem ct_ct (hc : ∀ a, c (c a) = a) (X : Matrix (Fin n) (Fin n) A) : ct c (ct c X) = X := by
  ext i j
  exact hc _

theorem blockUnit (hc : ∀ a, c (c a) = a) {e : A} (he : e * e = e) (he' : e * c e = 0)
    (P Q : Matrix (Fin n) (Fin n) A) (hPQ : e • (P * Q) = e • (1 : Matrix (Fin n) (Fin n) A))
    (hQP : e • (Q * P) = e • (1 : Matrix (Fin n) (Fin n) A)) :
    ((1 - e - c e) • (1 : Matrix (Fin n) (Fin n) A) + e • P + c e • ct c Q) *
        ((1 - e - c e) • (1 : Matrix (Fin n) (Fin n) A) + e • Q + c e • ct c P) = 1 ∧
      ((1 - e - c e) • (1 : Matrix (Fin n) (Fin n) A) + e • Q + c e • ct c P) *
        ((1 - e - c e) • (1 : Matrix (Fin n) (Fin n) A) + e • P + c e • ct c Q) = 1 ∧
      ct c ((1 - e - c e) • (1 : Matrix (Fin n) (Fin n) A) + e • P + c e • ct c Q) =
        (1 - e - c e) • (1 : Matrix (Fin n) (Fin n) A) + e • Q + c e • ct c P := by
  have hee : c e * c e = c e := by rw [← map_mul, he]
  have he2 : c e * e = 0 := by rw [mul_comm, he']
  set f := 1 - e - c e with hf
  have hcf : c f = f := by rw [hf, map_sub, map_sub, map_one, hc]; ring
  have h1 : e * f = 0 := by rw [hf]; linear_combination -he - he'
  have h2 : c e * f = 0 := by rw [hf]; linear_combination -hee - he'
  have h3 : f * e = 0 := by rw [mul_comm, h1]
  have h4 : f * c e = 0 := by rw [mul_comm, h2]
  have h5 : f * f = f := by linear_combination f * hf - h3 - h4
  have hsum : f + e + c e = 1 := by rw [hf]; ring
  have hPQ' : c e • (ct c Q * ct c P) = c e • (1 : Matrix (Fin n) (Fin n) A) := by
    rw [← ct_mul, ← ct_smul, hPQ, ct_smul, ct_one]
  have hQP' : c e • (ct c P * ct c Q) = c e • (1 : Matrix (Fin n) (Fin n) A) := by
    rw [← ct_mul, ← ct_smul, hQP, ct_smul, ct_one]
  refine ⟨?_, ?_, ?_⟩
  · simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul, he, he', hee, he2,
      h1, h2, h3, h4, h5, zero_smul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul, hPQ, hPQ']
    rw [← add_smul, ← add_smul, hsum, one_smul]
  · simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul, he, he', hee, he2,
      h1, h2, h3, h4, h5, zero_smul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul, hQP, hQP']
    rw [← add_smul, ← add_smul, hsum, one_smul]
  · rw [ct_add, ct_add, ct_smul, ct_smul, ct_smul, ct_one, ct_ct c hc, hcf, hc]
    abel

end Generic

variable {D : D7}

theorem cA_cA (z : AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero]
  | tmul a x => exact congrArg (fun y : D.host.E => a ⊗ₜ[D.host.F] y) (star_star x)
  | add a b ha hb => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), ha, hb]

theorem exists_blockUnit : ∀ {D : D7} (V : HSp D), V.gram = 1 → ∀ (e : AE D), e * e = e → e * cA D e = 0 →
    ∀ (P Q : Matrix (Fin V.rank) (Fin V.rank) (AE D)), e • (P * Q) = e • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) →
      e • (Q * P) = e • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) →
    ∃ g : GA D V,
      Formalism.L2.Theta.mt V g = (1 - e - cA D e) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) + e • P + cA D e • (Q.map (cA D)).transpose ∧
      Formalism.L2.Theta.mt V g⁻¹ = (1 - e - cA D e) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) + e • Q + cA D e • (P.map (cA D)).transpose := by
  intro D V hV e he he' P Q hPQ hQP
  obtain ⟨h1, h2, h3⟩ := blockUnit (cA D) cA_cA he he' P Q hPQ hQP
  have hmem : (((1 - e - cA D e) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) + e • P + cA D e • ct (cA D) Q).map (cA D)).transpose *
      V.gram.map (incA D) * ((1 - e - cA D e) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) + e • P + cA D e • ct (cA D) Q) =
      V.gram.map (incA D) := by
    rw [hV, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
    exact (congrArg (· * _) h3).trans h2
  let u : GL (Fin V.rank) (AE D) := ⟨_, _, h1, h2⟩
  have hu : u ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (AF D.host.F) D.sp.cm.sig V.gram := hmem
  let g : GA D V := (⟨u, hu⟩ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (AF D.host.F) D.sp.cm.sig V.gram)
  have hg : Formalism.L2.Theta.mt V g = u.1 := rfl
  have hg' : Formalism.L2.Theta.mt V g⁻¹ = u⁻¹.1 := rfl
  exact ⟨g, hg, hg'⟩
end GlobalTheory.UnitaryMove
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaLiftIdempotentFormStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_theta_lift_idempotent_form : ∀ {D : D7} (V : HSp D), V.gram = 1 → ∀ (e : AE D), e * e = e → e * cA D e = 0 →
    ∀ (P Q : Matrix (Fin V.rank) (Fin V.rank) (AE D)), e • (P * Q) = e • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) →
      e • (Q * P) = e • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) →
    ∃ g : GA D V,
      Formalism.L2.Theta.mt V g = (1 - e - cA D e) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) + e • P + cA D e • (Q.map (cA D)).transpose ∧
      Formalism.L2.Theta.mt V g⁻¹ = (1 - e - cA D e) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) + e • Q + cA D e • (P.map (cA D)).transpose := by
  first | exact @GlobalTheory.UnitaryMove.exists_blockUnit | exact GlobalTheory.UnitaryMove.exists_blockUnit | (intros; apply GlobalTheory.UnitaryMove.exists_blockUnit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixRowSubstitutionPolyEqEvalGenericRowSubstit
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixRowSubstitutionPolyEqEvalGenericRowSubstit
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenCoef.RowSubstSum

def evY (O : Type) [CommRing O] (N : ℕ) (R : Type) [CommRing R] [Algebra O R] (Y : Matrix (Fin N) (Fin N) R) :
    MvPolynomial (Fin N × Fin N) (MvPolynomial (Fin N × Fin N) O) →+* MvPolynomial (Fin N × Fin N) R :=
  eval₂Hom (MvPolynomial.map (algebraMap O R)) (fun v => C (Y v.1 v.2))

theorem evY_genSub (O : Type) [CommRing O] (N : ℕ) (R : Type) [CommRing R] [Algebra O R] (Y : Matrix (Fin N) (Fin N) R)
    (f : MvPolynomial (Fin N × Fin N) O) : evY O N R Y (GlobalTheory.HighWt.genSub O N f) = rowSubst O N R Y f := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    simp [evY, GlobalTheory.HighWt.genSub, rowSubst, MvPolynomial.algebraMap_eq]
  | add p q hp hq =>
    simp only [GlobalTheory.HighWt.genSub, map_add (f := _)] at hp hq ⊢
    rw [hp, hq]
  | mul_X p v hp =>
    simp only [GlobalTheory.HighWt.genSub, map_mul] at hp ⊢
    rw [hp]
    congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      simp [evY, rowSubst, map_sum]

theorem evY_eq_sum (O : Type) [CommRing O] (N : ℕ) (R : Type) [CommRing R] [Algebra O R] (Y : Matrix (Fin N) (Fin N) R)
    (P : MvPolynomial (Fin N × Fin N) (MvPolynomial (Fin N × Fin N) O)) :
    evY O N R Y P = ∑ m ∈ P.support, (m.prod fun v k => Y v.1 v.2 ^ k) • MvPolynomial.map (algebraMap O R) (P.coeff m) := by
  simp only [evY, coe_eval₂Hom, MvPolynomial.eval₂, Finsupp.sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have h : (m.prod fun v k => (C (Y v.1 v.2) : MvPolynomial (Fin N × Fin N) R) ^ k) = C (m.prod fun v k => Y v.1 v.2 ^ k) := by
    simp [Finsupp.prod, map_prod, map_pow]
  rw [h, mul_comm, C_mul']

theorem main : ∀ (O : Type) [CommRing O] (N : ℕ) (R : Type) [CommRing R] [Algebra O R] (Y : Matrix (Fin N) (Fin N) R) (f : MvPolynomial (Fin N × Fin N) O), rowSubst O N R Y f = ∑ m ∈ (GlobalTheory.HighWt.genSub O N f).support, (m.prod fun v k => Y v.1 v.2 ^ k) • MvPolynomial.map (algebraMap O R) ((GlobalTheory.HighWt.genSub O N f).coeff m) := by
  intro O _ N R _ _ Y f
  rw [← evY_genSub, evY_eq_sum]

end GlobalTheory.GenCoef.RowSubstSum

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixRowSubstitutionPolyEqEvalGenericRowSubstitStatement
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrixRowSubstitutionPoly_eq_eval_genericRowSubstitution : ∀ (O : Type) [CommRing O] (N : ℕ) (R : Type) [CommRing R] [Algebra O R] (Y : Matrix (Fin N) (Fin N) R) (f : MvPolynomial (Fin N × Fin N) O), rowSubst O N R Y f = ∑ m ∈ (GlobalTheory.HighWt.genSub O N f).support, (m.prod fun v k => Y v.1 v.2 ^ k) • MvPolynomial.map (algebraMap O R) ((GlobalTheory.HighWt.genSub O N f).coeff m) := by
  first | exact @GlobalTheory.GenCoef.RowSubstSum.main | exact GlobalTheory.GenCoef.RowSubstSum.main | (intros; apply GlobalTheory.GenCoef.RowSubstSum.main <;> assumption)
end
end
