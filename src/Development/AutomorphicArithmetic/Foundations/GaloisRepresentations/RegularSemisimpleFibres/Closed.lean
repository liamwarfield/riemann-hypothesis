module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PTypeChar
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PLiftBlocks
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PTameRead
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PTensFix
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PStableOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PHcChar
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PKillsTrue
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PSepOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CharpolyFromTrace.UnlinkedOfType
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.InflTraceOfMatching
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShintaniLiftKillsProductOfCuspForms
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.InflMatch

@[expose] public section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
  UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.isLocalHom UpperTheory.V.Pr.IsCD.fin
  UpperTheory.V.Alg.IsCO.toIsLocalRing UpperTheory.V.Alg.IsCO.complete
  UpperTheory.V.Alg.IsCO.isLocalHom UpperTheory.V.Alg.IsCO.self

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.TypeOfLblHolds
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PTameChars
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.InertialTypesAlt.tameChars :
    TameChars := by
  intro k _ _ _ _ N V _ _ π ω h
  obtain ⟨μ, hμ, H⟩ := h
  have hs : ∀ j, IsSmoothChar (μ j) := fun j => isSmoothChar_of_isTame (hμ j).isTame
  refine ⟨μ, hs, fun j u hu => ?_, ?_, fun j u => hμ j u⟩
  · exact (hμ j).isTame u hu
  · have := hasSupport_of_isCuspSupport H
    exact this
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PLiftsFix
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.InertialTypesAlt.liftsFix :
    LiftsFix := by
  intro E Ω _ _ _ n X Y h x
  induction h with
  | refl => exact ⟨x, rfl⟩
  | @tail B C _ hs ih =>
    obtain ⟨y, hy⟩ := ih
    obtain ⟨i₁, i₂, -⟩ := hs
    refine ⟨algebraMap B.K C.K y, ?_⟩
    rw [← hy]
    exact (IsScalarTower.algebraMap_apply B.K C.K Ω y).symm
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PBaseQ
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.InertialTypesAlt.baseQ :
    CardRes → BaseQ := by
  intro _ E _ _ v g _ i hi
  have e : 𝓀[v.adicCompletion E] ≃+* ZMod g :=
    (Ideal.quotEquivOfEq (DiscreteGroups.sglob.DzIso.ker_redO i hi).symm).trans
      (RingHom.quotientKerEquivOfSurjective (DiscreteGroups.sglob.DzIso.redO_surjective i hi))
  exact ⟨DiscreteGroups.sglob.DzType.g_not_mem_sq v g i hi, by rw [Nat.card_congr e.toEquiv, Nat.card_zmod], ⟨e⟩⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PTensTr
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem trace_map_eq_prod {s : ℕ} {W : Fin s → Type} [∀ a, AddCommGroup (W a)]
    [∀ a, Module ℂ (W a)] [∀ a, FiniteDimensional ℂ (W a)] (f : ∀ a, W a →ₗ[ℂ] W a) :
    LinearMap.trace ℂ (PiTensorProduct ℂ W) (PiTensorProduct.map f) =
      ∏ a, LinearMap.trace ℂ (W a) (f a) := by
  let b := fun a => Module.finBasis ℂ (W a)
  let B := Basis.piTensorProduct b
  rw [LinearMap.trace_eq_matrix_trace ℂ B]
  have hc : ∀ a, LinearMap.trace ℂ (W a) (f a) = ∑ j, (b a).repr (f a (b a j)) j := by
    intro a
    rw [LinearMap.trace_eq_matrix_trace ℂ (b a), Matrix.trace]
    simp only [Matrix.diag, LinearMap.toMatrix_apply]
  simp only [hc]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ, Matrix.trace]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Matrix.diag, LinearMap.toMatrix_apply, Basis.piTensorProduct_apply, PiTensorProduct.map_tprod,
    Basis.piTensorProduct_repr_tprod_apply]

theorem UpperTheory.Gal.InertialTypesAlt.tensTr :
    TensTr := by
  intro s Γ W _ _ _ _ κ
  refine ⟨Module.Finite.of_basis (Basis.piTensorProduct fun a => Module.finBasis ℂ (W a)), fun x => ?_⟩
  exact trace_map_eq_prod fun a => κ a (x a)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PCardRes
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.InertialTypesAlt.cardRes :
    CardRes := by
  intro E _ _ v
  rw [GroundTheory.Global.natCard_residueField_integer]
  rfl
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PTypeOfLbl
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.InertialTypesAlt.TypesOfLabels

private noncomputable def chRep {H : Type} [Group H] (χ : H →* ℂˣ) : Representation ℂ H ℂ where
  toFun g := ((χ g : ℂˣ) : ℂ) • LinearMap.id
  map_one' := by ext; simp
  map_mul' x y := by ext; simp [mul_comm]

private theorem chRep_apply {H : Type} [Group H] (χ : H →* ℂˣ) (g : H) (z : ℂ) :
    chRep χ g z = ((χ g : ℂˣ) : ℂ) • z := rfl

private theorem trace_chRep {H : Type} [Group H] (χ : H →* ℂˣ) (g : H) :
    LinearMap.trace ℂ ℂ (chRep χ g) = ((χ g : ℂˣ) : ℂ) := by
  show LinearMap.trace ℂ ℂ (((χ g : ℂˣ) : ℂ) • LinearMap.id) = _
  rw [map_smul, LinearMap.trace_id]
  simp

private theorem isCl_trace {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G W) : IsCl (fun g => LinearMap.trace ℂ W (ρ g)) := by
  intro x y
  simp only [map_mul]
  rw [LinearMap.trace_mul_cycle, ← map_mul, mul_inv_cancel, map_one, one_mul]

private theorem trace_zero {W : Type} [AddCommGroup W] [Module ℂ W] (h : ¬ FiniteDimensional ℂ W) :
    LinearMap.trace ℂ W = 0 := by
  ext f
  have hn : ¬ ∃ s : Finset W, Nonempty (Module.Basis s ℂ W) := by
    rintro ⟨s, ⟨b⟩⟩
    exact h (Module.Finite.of_basis b)
  simp only [LinearMap.trace, dif_neg hn]

private theorem ofFn_comp_get {β : Type} (M : List (ℕ × ℕ)) (f : ℕ × ℕ → β) :
    List.ofFn (fun a : Fin M.length => f (M.get a)) = M.map f := by
  rw [List.ofFn_comp', List.ofFn_get]

private theorem sum_fst (M : List (ℕ × ℕ)) : ∑ a : Fin M.length, (M.get a).1 = deg M := by
  unfold GlobalTheory.Shin.deg
  rw [← List.sum_ofFn]
  congr 1
  have := List.ofFn_comp' M.get Prod.fst
  simpa [List.ofFn_get] using this

end UpperTheory.Gal.InertialTypesAlt.TypesOfLabels

open UpperTheory.Gal.InertialTypesAlt.TypesOfLabels in
set_option synthInstance.maxHeartbeats 400000 in
theorem UpperTheory.Gal.InertialTypesAlt.typeOfLbl :
    MeetsIff → FrobL → JDEq → TypeOfLbl := by
  intro hMI hFL hJD k _ _ _ _ θ N V _ _ π b hb hL
  obtain ⟨_, _, hN, hmeet⟩ := hb
  have hd : ∑ a : Fin (b.D ++ b.L).length, ((b.D ++ b.L).get a).1 = N := by
    rw [sum_fst, hN]
    simp [Lbl.rk, GlobalTheory.Shin.deg, List.map_append, List.sum_append]
  let ω : Fin (b.D ++ b.L).length → 𝓀[k]ˣ →* ℂˣ := fun a =>
    (powMonoidHom ((b.D ++ b.L).get a).2).comp
      ((Units.map (θ : AlgebraicClosure 𝓀[k] →* ℂ)).comp
        (Units.map (algebraMap 𝓀[k] (AlgebraicClosure 𝓀[k])).toMonoidHom))
  refine ⟨(b.D ++ b.L).length, fun a => ((b.D ++ b.L).get a).1,
    fun a => ((b.D ++ b.L).get a).2, hd, ω, ?_, ?_, ?_⟩
  · rw [show (fun a : Fin (b.D ++ b.L).length => (((b.D ++ b.L).get a).1, ((b.D ++ b.L).get a).2))
        = (b.D ++ b.L).get from funext fun a => rfl, List.ofFn_get]
  · intro a u
    simp [ω]
  have hJ : JD θ b.D b.L N = hcL (List.ofFn fun i : Fin (b.D ++ b.L).length =>
      (⟨((b.D ++ b.L).get i).1, detc θ ((b.D ++ b.L).get i).1 ((b.D ++ b.L).get i).2⟩ :
        (m : ℕ) × (GL (Fin m) 𝓀[k] → ℂ))) N := by
    rw [(hJD 𝓀[k] θ).1, ofFn_comp_get (b.D ++ b.L)
      (fun p => (⟨p.1, detc θ p.1 p.2⟩ : (m : ℕ) × (GL (Fin m) 𝓀[k] → ℂ))), List.map_append]
    congr 2
    apply List.map_congr_left
    rintro ⟨p1, p2⟩ hp
    have h1 : p1 = 1 := hL _ hp
    subst h1
    rw [(hJD 𝓀[k] θ).2.1]
  obtain ⟨c0, hc0, hF⟩ := hFL 𝓀[k] (b.D ++ b.L).length (fun a => ((b.D ++ b.L).get a).1) N hd
  have hsum := hF (fun i => detc θ ((b.D ++ b.L).get i).1 ((b.D ++ b.L).get i).2)
    (fun g => LinearMap.trace ℂ _ (levelZero π g)) (isCl_trace _)
  have hne : ∑ᶠ p : parab 𝓀[k] (stdBlocks (fun a => ((b.D ++ b.L).get a).1) hd),
      star (∏ i, detc θ ((b.D ++ b.L).get i).1 ((b.D ++ b.L).get i).2
        (leviProj 𝓀[k] (stdBlocks (fun a => ((b.D ++ b.L).get a).1) hd) p i)) *
        LinearMap.trace ℂ _ (levelZero π (p : GL (Fin N) 𝓀[k])) ≠ 0 := by
    intro h0
    unfold Meets at hmeet
    rw [hJ, hsum, h0, mul_zero] at hmeet
    exact hmeet rfl
  have hfd : FiniteDimensional ℂ (fixed π (KOne k (Fin N))) := by
    by_contra hfd
    apply hne
    simp [trace_zero hfd]
  let χ := (UpperTheory.Gal.TypesAndIwahori.leviChar (fun a : Fin (b.D ++ b.L).length => Fin ((b.D ++ b.L).get a).1) ω).comp
    (leviProj 𝓀[k] (stdBlocks (fun a => ((b.D ++ b.L).get a).1) hd))
  have hm : Meets ((levelZero π).comp (parab 𝓀[k] (stdBlocks (fun a => ((b.D ++ b.L).get a).1) hd)).subtype)
      (fun g => LinearMap.trace ℂ ℂ (chRep χ g)) := by
    unfold Meets
    convert hne using 3 with p
    simp only [trace_chRep]
    simp [χ, ω, UpperTheory.Gal.TypesAndIwahori.leviChar_apply, detc]
  obtain ⟨f, hf0, hf⟩ := ((hMI _ _ ℂ _ _).2).1 hm
  have hf1 : f 1 ≠ 0 := fun h => hf0 (LinearMap.ext_ring (by simpa using h))
  refine ⟨(f 1 : V), by simpa using hf1, ?_⟩
  intro g
  obtain ⟨hK, hP⟩ := mem_levelPre.1 g.2
  have h2 := congrArg Subtype.val (hf ⟨redK k (Fin N) ⟨(g : GL (Fin N) k), hK⟩, hP⟩ 1)
  rw [chRep_apply, map_smul] at h2
  simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype, levelZero_apply,
    Submodule.coe_smul] at h2
  rw [← h2]
  rfl
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PJdIso
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Transport

variable {F F' : Type} [Field F] [Field F'] (r : F ≃+* F')

private theorem coe_phi {n : ℕ} (x : GL (Fin n) F) :
    ((Matrix.GeneralLinearGroup.map r.toRingHom x : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') =
      (x : Matrix (Fin n) (Fin n) F).map r := by
  ext i j
  simp [Matrix.GeneralLinearGroup.map_apply]

private def phiE (n : ℕ) : GL (Fin n) F ≃ GL (Fin n) F' where
  toFun := Matrix.GeneralLinearGroup.map r.toRingHom
  invFun := Matrix.GeneralLinearGroup.map r.symm.toRingHom
  left_inv x := by
    apply Units.ext
    ext i j
    simp [Matrix.GeneralLinearGroup.map_apply]
  right_inv x := by
    apply Units.ext
    ext i j
    simp [Matrix.GeneralLinearGroup.map_apply]

private theorem inPar_phi (a : ℕ) {n : ℕ} (x : GL (Fin n) F) :
    InPar a (Matrix.GeneralLinearGroup.map r.toRingHom x) ↔ InPar a x := by
  unfold InPar
  simp only [coe_phi, Matrix.map_apply]
  constructor
  · intro h i j hj hi
    exact (map_eq_zero_iff r r.injective).1 (h i j hj hi)
  · intro h i j hj hi
    rw [h i j hj hi, map_zero]

private theorem ent_map {n : ℕ} (M : Matrix (Fin n) (Fin n) F) (i j : ℕ) :
    ent (M.map r) i j = r (ent M i j) := by
  unfold ent
  split_ifs
  · rfl
  · exact (map_zero r).symm

private theorem tl_map (a : ℕ) {n : ℕ} (M : Matrix (Fin n) (Fin n) F) :
    tl a (M.map r) = (tl a M).map r := by
  ext i j
  simp [tl, ent_map]

private theorem br_map (a b : ℕ) {n : ℕ} (M : Matrix (Fin n) (Fin n) F) :
    br a b (M.map r) = (br a b M).map r := by
  ext i j
  simp [br, ent_map]

private theorem isUnit_map {n : ℕ} (M : Matrix (Fin n) (Fin n) F) :
    IsUnit (M.map r) ↔ IsUnit M := by
  have := isUnit_map_iff (r.mapMatrix (m := Fin n)) M
  simpa [RingEquiv.mapMatrix_apply] using this

private theorem coe_toG {n : ℕ} {M : Matrix (Fin n) (Fin n) F} (h : IsUnit M) :
    ((toG M : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = M := by
  unfold toG
  rw [dite_eq_left h]
  rfl

private theorem toG_map {n : ℕ} (M : Matrix (Fin n) (Fin n) F) :
    toG (M.map r) = Matrix.GeneralLinearGroup.map r.toRingHom (toG M) := by
  by_cases h : IsUnit M
  · apply Units.ext
    rw [coe_toG ((isUnit_map r M).2 h), coe_phi, coe_toG h]
  · have h' : ¬ IsUnit (M.map r) := fun k => h ((isUnit_map r M).1 k)
    unfold toG
    rw [dite_eq_right h, dite_eq_right h', map_one]

private theorem tlG_phi (a : ℕ) {n : ℕ} (x : GL (Fin n) F) :
    tlG a (Matrix.GeneralLinearGroup.map r.toRingHom x) =
      Matrix.GeneralLinearGroup.map r.toRingHom (tlG a x) := by
  unfold tlG
  rw [coe_phi, tl_map, toG_map]

private theorem brG_phi (a b : ℕ) {n : ℕ} (x : GL (Fin n) F) :
    brG a b (Matrix.GeneralLinearGroup.map r.toRingHom x) =
      Matrix.GeneralLinearGroup.map r.toRingHom (brG a b x) := by
  unfold brG
  rw [coe_phi, br_map, toG_map]

include r in
private theorem card_phi (a n : ℕ) :
    Nat.card {p : GL (Fin n) F' // InPar a p} = Nat.card {p : GL (Fin n) F // InPar a p} :=
  (Nat.card_congr ((phiE r n).subtypeEquiv fun x => (inPar_phi r a x).symm)).symm

private theorem gal_id {K : Type} [Field K] (n : ℕ) (y : GL (Fin n) K) : gal (RingHom.id K) n y = y := by
  apply Units.ext
  ext i j
  simp [gal, Matrix.GeneralLinearGroup.map_apply]

private theorem hc_phi (a b : ℕ) (α : GL (Fin a) F' → ℂ) (β : GL (Fin b) F' → ℂ) (n : ℕ)
    (g : GL (Fin n) F) :
    hc a b α β n (Matrix.GeneralLinearGroup.map r.toRingHom g) =
      hc a b (fun x => α (Matrix.GeneralLinearGroup.map r.toRingHom x))
        (fun x => β (Matrix.GeneralLinearGroup.map r.toRingHom x)) n g := by
  unfold hc hcTw
  simp only [gal_id]
  rw [card_phi r a n, ← finsum_comp_equiv (phiE r n)]
  congr 1
  refine finsum_congr fun y => ?_
  have e : (phiE r n y)⁻¹ * Matrix.GeneralLinearGroup.map r.toRingHom g * phiE r n y =
      Matrix.GeneralLinearGroup.map r.toRingHom (y⁻¹ * g * y) := by
    simp only [map_mul, map_inv]
    rfl
  rw [e]
  simp only [inPar_phi, tlG_phi, brG_phi]

private theorem detc_phi (j : AlgebraicClosure F ≃+* AlgebraicClosure F')
    (hj : ∀ x, j (algebraMap _ _ x) = algebraMap _ _ (r x)) (θ : AlgebraicClosure F' →* ℂ)
    (t k : ℕ) (x : GL (Fin t) F) :
    detc θ t k (Matrix.GeneralLinearGroup.map r.toRingHom x) = detc (θ.comp j.toMonoidHom) t k x := by
  unfold detc
  have e : ((x : Matrix (Fin t) (Fin t) F).map r).det = r (x : Matrix (Fin t) (Fin t) F).det :=
    (RingHom.map_det r.toRingHom _).symm
  rw [coe_phi, e, ← hj]
  rfl

end Transport

theorem UpperTheory.Gal.InertialTypesAlt.jdIso :
    CuspIso → JDIso := by
  intro hC F F' _ _ _ r j hj θ D L n g
  have hJ : ∀ (L : List (ℕ × ℕ)) (n : ℕ) (g : GL (Fin n) F),
      J θ L n (Matrix.GeneralLinearGroup.map r.toRingHom g) = J (θ.comp j.toMonoidHom) L n g := by
    intro L
    induction L with
    | nil => intro n g; rfl
    | cons p L ih =>
      intro n g
      rw [J_cons, J_cons, hc_phi]
      congr 1
      · funext x
        exact hC F F' r j hj θ p.1 p.2 x
      · funext x
        exact ih _ x
  induction D generalizing n g with
  | nil => exact hJ L n g
  | cons p D ih =>
    rw [JD_cons, JD_cons, hc_phi]
    congr 1
    · funext x
      exact detc_phi r j hj θ p.1 p.2 x
    · funext x
      exact ih _ x
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PResDeg
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.InertialTypesAlt.resDeg :
    CardRes → ResDeg := by
  intro hcard K M _ _ _ _ _ _ hn v w hns hunr _
  classical
  have hw : (w : HeightOneSpectrum (𝓞 M)).asIdeal.LiesOver v.asIdeal := w.2
  set f := (w : HeightOneSpectrum (𝓞 M)).asIdeal.inertiaDeg (𝓞 K) with hf
  have hfconst : ∀ u : PlacesOver M v,
      (u : HeightOneSpectrum (𝓞 M)).asIdeal.inertiaDeg (𝓞 K) = f := by
    intro u
    haveI := u.2
    exact Ideal.inertiaDeg_eq_of_isGaloisGroup v.asIdeal _ _ Gal(M/K)
  have heone : ∀ u : PlacesOver M v,
      (u : HeightOneSpectrum (𝓞 M)).asIdeal.ramificationIdx (𝓞 K) = 1 := by
    intro u
    haveI := hunr u
    exact Ideal.ramificationIdx_eq_one _ _
  have hsum := GroundTheory.Global.SemiLocal.sum_ramificationIdx_mul_inertiaDeg M v
  have hdvd : f ∣ Module.finrank K M := by
    rw [← hsum]
    apply Finset.dvd_sum
    intro u _
    rw [heone u, hfconst u, one_mul]
  have hf1 : f ≠ 1 := by
    intro h1
    apply hns
    intro u
    haveI := u.2
    have hrk := GroundTheory.Global.SemiLocal.finrank_eq_ramificationIdx_mul_inertiaDeg M v
      (u : HeightOneSpectrum (𝓞 M))
    rw [heone u, hfconst u, h1, one_mul] at hrk
    have htop := Subalgebra.bot_eq_top_of_finrank_eq_one hrk
    intro y
    have hy : y ∈ (⊥ : Subalgebra (HeightOneSpectrum.adicCompletion K v)
        (HeightOneSpectrum.adicCompletion M (u : HeightOneSpectrum (𝓞 M)))) := by
      rw [htop]
      trivial
    obtain ⟨x, hx⟩ := Algebra.mem_bot.mp hy
    exact ⟨x, hx⟩
  have hfn : f = Module.finrank K M := (hn.eq_one_or_self_of_dvd f hdvd).resolve_left hf1
  have hnormK : normV v = v.asIdeal.absNorm := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  have hnormM : normV (w : HeightOneSpectrum (𝓞 M)) =
      (w : HeightOneSpectrum (𝓞 M)).asIdeal.absNorm := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  have hpow : v.asIdeal.absNorm ^ f = (w : HeightOneSpectrum (𝓞 M)).asIdeal.absNorm :=
    Ideal.absNorm_pow_inertiaDeg v.asIdeal _
  have hK := hcard K v
  have hM := hcard M (w : HeightOneSpectrum (𝓞 M))
  have hge : 2 ≤ v.asIdeal.absNorm := by
    have h0 : v.asIdeal.absNorm ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact v.ne_bot
    have h1 : v.asIdeal.absNorm ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]
      exact v.isPrime.ne_top
    omega
  have hcardM : Nat.card 𝓀[HeightOneSpectrum.adicCompletion M (w : HeightOneSpectrum (𝓞 M))] =
      Nat.card 𝓀[HeightOneSpectrum.adicCompletion K v] ^ Module.finrank K M := by
    rw [hM, hK, hnormM, hnormK, ← hpow, hfn]
  haveI : Finite 𝓀[HeightOneSpectrum.adicCompletion K v] :=
    Nat.finite_of_card_ne_zero (by rw [hK, hnormK]; omega)
  haveI : Finite 𝓀[HeightOneSpectrum.adicCompletion M (w : HeightOneSpectrum (𝓞 M))] :=
    Nat.finite_of_card_ne_zero (by rw [hcardM, hK, hnormK]; positivity)
  letI := Fintype.ofFinite 𝓀[HeightOneSpectrum.adicCompletion K v]
  haveI : Module.Finite 𝓀[HeightOneSpectrum.adicCompletion K v]
      𝓀[HeightOneSpectrum.adicCompletion M (w : HeightOneSpectrum (𝓞 M))] :=
    Module.Finite.of_finite
  refine ⟨?_, ?_⟩
  · have hc := Module.natCard_eq_pow_finrank (K := 𝓀[HeightOneSpectrum.adicCompletion K v])
      (V := 𝓀[HeightOneSpectrum.adicCompletion M (w : HeightOneSpectrum (𝓞 M))])
    rw [hcardM] at hc
    have h2 : 2 ≤ Nat.card 𝓀[HeightOneSpectrum.adicCompletion K v] := by
      rw [hK, hnormK]
      exact hge
    exact (Nat.pow_right_injective h2 hc).symm
  · refine ⟨FiniteField.frobeniusAlgEquivOfAlgebraic _ _, fun z => ?_⟩
    rw [FiniteField.frobeniusAlgEquivOfAlgebraic_apply, Nat.card_eq_fintype_card]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PKillsNil
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem frob_ne_one {F F' : Type} [Field F] [Field F'] [Algebra F F'] [Finite F']
    (s : F' ≃ₐ[F] F') (hp : (Module.finrank F F').Prime) (hs : ∀ z, s z = z ^ Nat.card F) :
    s ≠ 1 := by
  rintro rfl
  haveI : Finite F := Finite.of_injective (algebraMap F F') (algebraMap F F').injective
  haveI : Fintype F' := Fintype.ofFinite F'
  have hcard : Nat.card F' = Nat.card F ^ Module.finrank F F' := Module.natCard_eq_pow_finrank
  have hq : 1 < Nat.card F := Finite.one_lt_card
  generalize Nat.card F = q at hs hq hcard
  have hne : (X ^ q - X : F'[X]) ≠ 0 := Polynomial.X_pow_sub_X_ne_zero hq
  have hdeg : (X ^ q - X : F'[X]).natDegree = q := Polynomial.natDegree_X_pow_sub_X (R := F') hq
  have hsub : (Finset.univ : Finset F') ⊆ (X ^ q - X : F'[X]).roots.toFinset := by
    intro z _
    rw [Multiset.mem_toFinset, mem_roots hne]
    have := hs z
    simp only [AlgEquiv.one_apply] at this
    simp [IsRoot, ← this]
  have h1 : Nat.card F' ≤ q := by
    rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
    calc _ ≤ _ := Finset.card_le_card hsub
      _ ≤ Multiset.card (X ^ q - X : F'[X]).roots := Multiset.toFinset_card_le _
      _ ≤ (X ^ q - X : F'[X]).natDegree := card_roots' _
      _ = q := hdeg
  rw [hcard] at h1
  have h2 : q ^ 2 ≤ q ^ Module.finrank F F' := Nat.pow_le_pow_right (by omega) hp.two_le
  nlinarith

theorem UpperTheory.Gal.InertialTypesAlt.killsNil :
    KillsAll → KillsOn fun a => a.D = [] := by
  intro h F F' _ _ _ _ s hp hs ι θ hθ a hD hok hq
  obtain ⟨q, D, L⟩ := a
  simp only at hD hq
  subst hD
  subst hq
  have key := h F F' s hp (frob_ne_one s hp hs) ι θ hθ L (fun p hp' => hok.2.2 p hp') (deg L) rfl
  have hrk : (⟨Nat.card F, [], L⟩ : Lbl).rk = deg L := by
    have h0 : GlobalTheory.Shin.deg ([] : List (ℕ × ℕ)) = 0 := rfl
    simp [Lbl.rk, h0]
  rw [hrk]
  simpa [Lbl.lift, JD_nil] using key
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PMeetsIff
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem sum_ne_iff {H V W : Type} [Group H] [Fintype H] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ H V) (κ : Representation ℂ H W) :
    (∑ g : H, κ.character g⁻¹ * ρ.character g ≠ 0) ↔
      ∃ f : W →ₗ[ℂ] V, f ≠ 0 ∧ ∀ g x, f (κ g x) = ρ g (f x) := by
  classical
  haveI : Invertible (Nat.card H : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have key := Representation.card_inv_mul_sum_char_mul_char_eq_finrank κ ρ
  have hsum : (∑ g : H, κ.character g⁻¹ * ρ.character g) =
      ∑ g : H, ρ.character g * κ.character g⁻¹ :=
    Finset.sum_congr rfl fun g _ => mul_comm _ _
  have hc : (Nat.card H : ℂ)⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  rw [hsum]
  constructor
  · intro h
    have hpos : Module.finrank ℂ (Representation.IntertwiningMap κ ρ) ≠ 0 := by
      intro h0
      rw [h0, Nat.cast_zero] at key
      exact h ((mul_eq_zero.mp key).resolve_left hc)
    haveI := Module.nontrivial_of_finrank_pos (Nat.pos_of_ne_zero hpos)
    obtain ⟨φ, hφ⟩ := exists_ne (0 : Representation.IntertwiningMap κ ρ)
    refine ⟨φ.toLinearMap, ?_, fun g x => Representation.IntertwiningMap.isIntertwining κ ρ φ g x⟩
    intro h0
    exact hφ (Representation.IntertwiningMap.ext (by simpa using h0))
  · rintro ⟨f, hf0, hf⟩
    let φ := f.intertwiningMap_of_isIntertwiningMap κ ρ hf
    have hφ : φ ≠ 0 := by
      intro h0
      apply hf0
      ext x
      have := congrArg (fun ψ : Representation.IntertwiningMap κ ρ => ψ x) h0
      simpa [φ] using this
    have hpos : Module.finrank ℂ (Representation.IntertwiningMap κ ρ) ≠ 0 := by
      rw [← (Representation.invariantsEquivIntertwiningMap κ ρ).finrank_eq]
      apply Nat.pos_iff_ne_zero.mp
      rw [Module.finrank_pos_iff_exists_ne_zero]
      refine ⟨(Representation.invariantsEquivIntertwiningMap κ ρ).symm φ, ?_⟩
      simpa using hφ
    intro hs
    rw [hs, mul_zero] at key
    exact hpos (by exact_mod_cast key.symm)

theorem UpperTheory.Gal.InertialTypesAlt.meetsIff :
    MeetsIff := by
  intro H V W _ _ _ _ _ _ _ _ ρ κ
  classical
  haveI := Fintype.ofFinite H
  have hstar : ∀ g : H, star (LinearMap.trace ℂ W (κ g)) = κ.character g⁻¹ := by
    intro g
    have hmem : (fun g => algebraMap ℂ ℂ (κ.character g)) ∈ GlobalTheory.BI.Virt ℂ ℂ H :=
      AddSubgroup.subset_closure (GlobalTheory.T.isCharacterOverSubfield_of_representation ℂ ℂ H W κ).1
    have := GlobalTheory.T.star_virtualCharacter_eq_apply_inv H _ hmem g
    change star (κ.character g) = _
    simpa using this
  have hM : Meets ρ (fun g => LinearMap.trace ℂ W (κ g)) ↔
      ∑ g : H, κ.character g⁻¹ * ρ.character g ≠ 0 := by
    unfold Meets
    rw [finsum_eq_sum_of_fintype]
    simp only [hstar]
    rfl
  have hswap : (∑ g : H, κ.character g⁻¹ * ρ.character g) =
      ∑ g : H, ρ.character g⁻¹ * κ.character g :=
    Fintype.sum_equiv (Equiv.inv H) _ _ fun g => by simp [mul_comm]
  refine ⟨?_, ?_⟩
  · rw [hM, hswap]
    exact sum_ne_iff κ ρ
  · rw [hM]
    exact sum_ne_iff ρ κ
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PParCons
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section ParConsAux

variable {F : Type} [Field F]

private theorem tl_entry {a n : ℕ} (M : Matrix (Fin n) (Fin n) F) (i j : Fin a) (I J : Fin n)
    (hI : (I : ℕ) = i) (hJ : (J : ℕ) = j) : GlobalTheory.Shin.tl a M i j = M I J := by
  unfold GlobalTheory.Shin.tl GlobalTheory.Shin.ent
  rw [dite_eq_left ⟨by rw [← hI]; exact I.isLt, by rw [← hJ]; exact J.isLt⟩]
  congr 1 <;> ext <;> simp [hI, hJ]

private theorem br_entry {a b n : ℕ} (M : Matrix (Fin n) (Fin n) F) (i j : Fin b) (I J : Fin n)
    (hI : (I : ℕ) = a + i) (hJ : (J : ℕ) = a + j) : GlobalTheory.Shin.br a b M i j = M I J := by
  unfold GlobalTheory.Shin.br GlobalTheory.Shin.ent
  rw [dite_eq_left ⟨by rw [← hI]; exact I.isLt, by rw [← hJ]; exact J.isLt⟩]
  congr 1 <;> ext <;> simp [hI, hJ]

private theorem units_of {a b n : ℕ} (hn : n = a + b) (p : GL (Fin n) F) (h : GlobalTheory.Shin.InPar a p) :
    IsUnit (GlobalTheory.Shin.tl a (p : Matrix (Fin n) (Fin n) F)) ∧
      IsUnit (GlobalTheory.Shin.br a b (p : Matrix (Fin n) (Fin n) F)) := by
  subst hn
  have hM : (p : Matrix (Fin (a + b)) (Fin (a + b)) F).submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks (GlobalTheory.Shin.tl a (p : Matrix (Fin (a + b)) (Fin (a + b)) F))
        (Matrix.of fun i j => (p : Matrix (Fin (a + b)) (Fin (a + b)) F) (Fin.castAdd b i) (Fin.natAdd a j)) 0
        (GlobalTheory.Shin.br a b (p : Matrix (Fin (a + b)) (Fin (a + b)) F)) := by
    refine Matrix.ext fun i j => ?_
    rcases i with i | i <;> rcases j with j | j
    · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁, finSumFinEquiv_apply_left]
      exact (tl_entry _ i j _ _ (by simp) (by simp)).symm
    · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₂, finSumFinEquiv_apply_left,
        finSumFinEquiv_apply_right, Matrix.of_apply]
    · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₁, finSumFinEquiv_apply_left,
        finSumFinEquiv_apply_right, Matrix.zero_apply]
      exact h _ _ (by simp) (by simp)
    · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₂, finSumFinEquiv_apply_right]
      exact (br_entry _ i j _ _ (by simp) (by simp)).symm
  have hu : IsUnit (p : Matrix (Fin (a + b)) (Fin (a + b)) F).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 p.isUnit
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv, hM, Matrix.det_fromBlocks_zero₂₁,
    IsUnit.mul_iff] at hu
  exact ⟨(Matrix.isUnit_iff_isUnit_det _).2 hu.1, (Matrix.isUnit_iff_isUnit_det _).2 hu.2⟩

private theorem toG_coe {n : ℕ} {M : Matrix (Fin n) (Fin n) F} (h : IsUnit M) :
    ((GlobalTheory.Shin.toG M : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = M := by
  unfold GlobalTheory.Shin.toG
  rw [dite_eq_left h]
  rfl

private theorem sv0 {s n : ℕ} (d : Fin (s + 1) → ℕ) (hd : ∑ i, d i = n) (i : Fin (d 0)) :
    ((GlobalTheory.SmGL.stdBlocks d hd ⟨0, i⟩ : Fin n) : ℕ) = i := by
  rw [GlobalTheory.SmGL.stdBlocks_val]
  simp

private theorem svS {s n b : ℕ} (d : Fin (s + 1) → ℕ) (hd : ∑ i, d i = n)
    (hb : ∑ i : Fin s, d i.succ = b) (c : Fin s) (i : Fin (d c.succ)) :
    ((GlobalTheory.SmGL.stdBlocks d hd ⟨c.succ, i⟩ : Fin n) : ℕ) =
      d 0 + ((GlobalTheory.SmGL.stdBlocks (fun i : Fin s => d i.succ) hb ⟨c, i⟩ : Fin b) : ℕ) := by
  rw [GlobalTheory.SmGL.stdBlocks_val, GlobalTheory.SmGL.stdBlocks_val]
  erw [Fin.sum_univ_succ]
  rw [add_assoc]
  congr 2

private theorem inPar_of {s n b : ℕ} (d : Fin (s + 1) → ℕ) (hd : ∑ i, d i = n)
    (hb : ∑ i : Fin s, d i.succ = b) (p : GL (Fin n) F)
    (hp : p ∈ GlobalTheory.SmGL.parab F (GlobalTheory.SmGL.stdBlocks d hd)) : GlobalTheory.Shin.InPar (d 0) p := by
  intro i j hj hi
  obtain ⟨⟨α, i'⟩, rfl⟩ := (GlobalTheory.SmGL.stdBlocks d hd).surjective i
  obtain ⟨⟨β, j'⟩, rfl⟩ := (GlobalTheory.SmGL.stdBlocks d hd).surjective j
  rw [GlobalTheory.SmGL.mem_parab_iff] at hp
  cases β using Fin.cases with
  | zero =>
    cases α using Fin.cases with
    | zero =>
      rw [sv0] at hi
      exact absurd i'.isLt (by omega)
    | succ c => exact hp _ _ _ _ (Fin.succ_pos c)
  | succ c =>
    rw [svS d hd hb] at hj
    omega

private theorem brG_entry {s n b : ℕ} (d : Fin (s + 1) → ℕ) (hd : ∑ i, d i = n)
    (hb : ∑ i : Fin s, d i.succ = b) (hn : n = d 0 + b) (p : GL (Fin n) F)
    (h : GlobalTheory.Shin.InPar (d 0) p) (c c' : Fin s) (i : Fin (d c.succ)) (j : Fin (d c'.succ)) :
    ((GlobalTheory.Shin.brG (d 0) b p : GL (Fin b) F) : Matrix (Fin b) (Fin b) F)
        (GlobalTheory.SmGL.stdBlocks (fun i : Fin s => d i.succ) hb ⟨c, i⟩)
        (GlobalTheory.SmGL.stdBlocks (fun i : Fin s => d i.succ) hb ⟨c', j⟩) =
      (p : Matrix (Fin n) (Fin n) F) (GlobalTheory.SmGL.stdBlocks d hd ⟨c.succ, i⟩)
        (GlobalTheory.SmGL.stdBlocks d hd ⟨c'.succ, j⟩) := by
  unfold GlobalTheory.Shin.brG
  rw [toG_coe (units_of hn p h).2]
  exact br_entry _ _ _ _ _ (svS d hd hb c i) (svS d hd hb c' j)

end ParConsAux

theorem UpperTheory.Gal.InertialTypesAlt.parCons :
    ParCons := by
  intro F _ s n d hd b hb p
  have hn : n = d 0 + b := by rw [← hd, ← hb, Fin.sum_univ_succ]
  refine ⟨⟨fun hp => ⟨inPar_of d hd hb p hp, ?_⟩, fun ⟨h1, h2⟩ => ?_⟩, fun hp hp' => ⟨?_, fun c => ?_⟩⟩
  · have h1 := inPar_of d hd hb p hp
    rw [GlobalTheory.SmGL.mem_parab_iff] at hp ⊢
    intro c c' i j hc
    rw [brG_entry d hd hb hn p h1]
    exact hp _ _ _ _ (Fin.succ_lt_succ_iff.2 hc)
  · rw [GlobalTheory.SmGL.mem_parab_iff] at h2 ⊢
    intro α β i j hαβ
    cases α using Fin.cases with
    | zero => exact absurd hαβ (Fin.not_lt_zero _)
    | succ c =>
      cases β using Fin.cases with
      | zero =>
        apply h1
        · rw [sv0]; exact j.isLt
        · rw [svS d hd hb]; omega
      | succ c' =>
        rw [← brG_entry d hd hb hn p h1]
        exact h2 _ _ _ _ (Fin.succ_lt_succ_iff.1 hαβ)
  · have h1 := inPar_of d hd hb p hp
    ext i j
    change (p : Matrix (Fin n) (Fin n) F) (GlobalTheory.SmGL.stdBlocks d hd ⟨0, i⟩)
      (GlobalTheory.SmGL.stdBlocks d hd ⟨0, j⟩) = _
    unfold GlobalTheory.Shin.tlG
    rw [toG_coe (units_of hn p h1).1]
    exact (tl_entry _ _ _ _ _ (sv0 d hd i) (sv0 d hd j)).symm
  · have h1 := inPar_of d hd hb p hp
    ext i j
    change (p : Matrix (Fin n) (Fin n) F) (GlobalTheory.SmGL.stdBlocks d hd ⟨c.succ, i⟩)
        (GlobalTheory.SmGL.stdBlocks d hd ⟨c.succ, j⟩) =
      ((GlobalTheory.Shin.brG (d 0) b p : GL (Fin b) F) : Matrix (Fin b) (Fin b) F)
        (GlobalTheory.SmGL.stdBlocks (fun i : Fin s => d i.succ) hb ⟨c, i⟩)
        (GlobalTheory.SmGL.stdBlocks (fun i : Fin s => d i.succ) hb ⟨c, j⟩)
    rw [brG_entry d hd hb hn p h1]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PSuppAny
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem prod_block (hBC : UpperTheory.Gal.TypesAndIwahori.BlockCount) {s N : ℕ} (d c : Fin s → ℕ) (hd : ∑ a, d a = N) (y : ℂ) :
    ∏ j : Fin N, (X - C (y ^ c (UpperTheory.Gal.TypesAndIwahori.blockOf d hd j)) : ℂ[X]) =
      ∏ a, (X - C (y ^ c a)) ^ d a := by
  show (Finset.univ.val.map fun j => (fun a => (X - C (y ^ c a) : ℂ[X])) (UpperTheory.Gal.TypesAndIwahori.blockOf d hd j)).prod = _
  rw [hBC ℂ[X] N s d hd (fun a => X - C (y ^ c a)), Multiset.prod_sum]
  simp [Multiset.prod_replicate]

private theorem pol_top (hBC : UpperTheory.Gal.TypesAndIwahori.BlockCount) (hPT : PolTop) (b : Lbl) {s N : ℕ} (d c : Fin s → ℕ)
    (hd : ∑ a, d a = N) (hl : List.ofFn (fun a => (d a, c a)) = b.D ++ b.L) (y : ℂ) (h2 : 2 ≤ b.q)
    (h1 : ∀ p ∈ b.L, p.1 = 1) (hy : y ^ (b.q - 1) = 1) :
    ∏ j : Fin N, (X - C (y ^ c (UpperTheory.Gal.TypesAndIwahori.blockOf d hd j)) : ℂ[X]) = b.pol b.q y := by
  rw [prod_block hBC, (hPT b y h2 h1 hy).2, ← hl, List.map_ofFn, List.prod_ofFn]
  rfl

private theorem pol_bot (hPB : PolBot) (q Q : ℕ) {s : ℕ} (m c : Fin s → ℕ) (y : ℂ) (h2 : 2 ≤ Q) (hy : y ^ (Q - 1) = 1) :
    (⟨q, [], List.ofFn fun a => (m a, c a)⟩ : Lbl).pol Q y =
      ∏ a, ∏ j ∈ Finset.range (m a), (X - C (y ^ (c a * q ^ j * ((Q - 1) / (q ^ m a - 1))))) := by
  rw [hPB q Q _ y h2 hy, List.map_ofFn, List.prod_ofFn]
  rfl

theorem UpperTheory.Gal.InertialTypesAlt.suppAny :
    (LblOn fun a => a.D = []) → LblOf → TypeOfLbl → UpperTheory.Gal.TypesAndIwahori.SuppOfType → UpperTheory.Gal.TypesAndIwahori.BlockCount → TameChars → LeTop → PolTop → PolBot → ResEmbEx → UnifTower → BaseQ → CardRes → ArtRead → CuspIne → SuppIne → SuppAny := by
  intro hOn hOf hTy hSO hBC hTC hLT hPT hPB hRE hUT hBQ hCR hAR hCI hSI
  intro E Ω _ _ _ _ _ _ n hn π Y hY A v w h h' g _ i hi hI τ τ' hτ hτ' hD f hf hs
  haveI : CharZero (v.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  haveI : CharZero (w.adicCompletion Y.K) := charZero_of_injective_algebraMap (algebraMap Y.K _).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  obtain ⟨⟨e, he⟩, Θ, hΘ⟩ := hRE E Ω A v h
  obtain ⟨⟨e', he'⟩, -⟩ := hRE Y.K Ω A w h'
  have eqv : τ.ρ.Equiv (IrrGL.of τ.ρ τ.smooth τ.irred).rep := IrrGL.equivOf _ _ _
  obtain ⟨𝔪, hm⟩ := UpperTheory.Zero.LLC.Pr.exh (v.adicCompletion E) (IrrGL.of τ.ρ τ.smooth τ.irred)
  have hS₀ : HasSupport (IrrGL.of τ.ρ τ.smooth τ.irred).rep (msupp 𝔪) :=
    hasSupport_msupp_of_isL UpperTheory.Zero.LLC.Pr.zel _ 𝔪 _ hm
  have hS : HasSupport τ.ρ (msupp 𝔪) := hS₀.of_equiv eqv.symm
  have hfix : fixed τ.ρ (KOne (v.adicCompletion E) (Fin n)) ≠ ⊥ := GlobalTheory.LocLanglands.fixed_ne_bot_of_equiv eqv.symm hD
  have hθ : Inj (Θ.comp e.toMonoidHom) := fun a b ha hb hab =>
    e.injective (hΘ _ _ (by simpa using ha) (by simpa using hb) hab)
  obtain ⟨hg2, hcard, -⟩ := hBQ E v g i hi
  obtain ⟨s, x, c, hxS, hx, hlbl⟩ := hOf _ (Θ.comp e.toMonoidHom) hθ n _ τ.ρ _ hS hfix
  rw [hcard] at hlbl hx
  obtain ⟨b, hab, hb⟩ := hOn E Ω n hn (Pt.base Ω π) Y hY A Θ hΘ hI v w h h' e e' he he' τ τ' hτ hτ' _ rfl hlbl
  have hbq : b.q = g ^ f := by rw [hb.2.1, hCR, hf]
  have hb2 : 2 ≤ b.q := hb.1.1
  have hf0 : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | h0
    · simp [hbq] at hb2
    · exact h0
  have hdiv : ∀ a, (x a).1 ∣ f := fun a =>
    hs _ hS _ (by rw [← hxS]; exact Multiset.mem_map_of_mem _ (Finset.mem_univ a))
  have hsp : (⟨g, [], List.ofFn fun a => ((x a).1, c a)⟩ : Lbl).Splits b.q := by
    refine ⟨f, hf0, hbq, fun p hp => ?_⟩
    obtain ⟨a, rfl⟩ := (List.mem_ofFn' _ _).1 hp
    exact hdiv a
  obtain ⟨-, -, hL1, hblk⟩ := hLT _ b hlbl.1 hab hsp
  obtain ⟨s', d, c', hd, ω, hl, hω, hTV⟩ := hTy _ (Θ.comp e'.toMonoidHom) n _ τ'.ρ b hb hL1
  have hTS := hSO _ n s' d hd _ τ'.ρ τ'.smooth τ'.irred ω hTV
  obtain ⟨ξ, hξ, hξt, hξs, hξu⟩ := hTC _ n _ τ'.ρ _ hTS
  refine ⟨ξ, hξ, hξt, hξs, ?_⟩
  intro rc hrc a' ha' t
  have hQ : 1 ≤ normV w - 1 := by rw [hf, ← hbq]; omega
  obtain ⟨ϖ, hϖ⟩ : ∃ ϖ : Ω, ϖ ^ (normV w - 1) = (g : Ω) := IsAlgClosed.exists_pow_nat_eq _ hQ
  have hg1 : ((g : ℕ) : 𝓞 Y.K) ∈ w.asIdeal := DiscreteGroups.sglob.DzType.natCast_mem_of_normV w g f hf0 hf
  have hg2' : ((g : ℕ) : 𝓞 Y.K) ∉ w.asIdeal ^ 2 := hUT E Ω n (Pt.base Ω π) Y hY A hI v w h h' g hg2
  obtain ⟨z, u, hz, hu, hres, hpow⟩ := hAR Y.K Ω A w h' g hg1 hg2' a' ha' e' he' t ϖ hϖ
  obtain ⟨y, hyd⟩ : ∃ y : ℂ, y = Θ (IsLocalRing.residue A z) := ⟨_, rfl⟩
  have hy : y ^ (g ^ f - 1) = 1 := by rw [hyd, ← map_pow, ← hf, hpow, map_one]
  have hξ' : ∀ j, ((ξ j (a' (ineIncl h' t)) : ℂˣ) : ℂ) = y ^ c' (UpperTheory.Gal.TypesAndIwahori.blockOf d hd j) := by
    intro j
    rw [← hu, hξu, hω, hyd, ← hres]
    rfl
  let t₀ : Ine (F := E) A := ⟨AlgEquiv.restrictScalars E (t : G Y.K Ω), t.2.1, t.2.2⟩
  have hcu : ∀ a, (rc (x a)).inePol (t₀ : G E Ω) =
      ∏ j ∈ Finset.range (x a).1, (X - C (y ^ (c a * g ^ j * ((g ^ f - 1) / (g ^ (x a).1 - 1))))) := by
    intro a
    rw [hyd]
    exact hCI E Ω A v h g i hi Θ hΘ e (x a) (c a) (hx a).1 (hx a).2.1 (hx a).2.2.1 (hx a).2.2.2 rc hrc f hf0 (hdiv a)
      t₀ ϖ (hf ▸ hϖ) z hz
  have hSx : HasSupport (IrrGL.of τ.ρ τ.smooth τ.irred).rep (msupp 𝔪) := hS₀
  have h1 := hSI E Ω A v h rc hrc _ _ hSx t₀
  rw [← hxS, Multiset.map_map] at h1
  have h2 : (rc (IrrGL.of τ.ρ τ.smooth τ.irred)).inePol (t₀ : G E Ω) =
      ∏ a, ∏ j ∈ Finset.range (x a).1, (X - C (y ^ (c a * g ^ j * ((g ^ f - 1) / (g ^ (x a).1 - 1))))) := by
    rw [h1, ← Finset.prod_congr rfl fun a _ => hcu a]
    rfl
  have h3 := pol_top hBC hPT b d c' hd hl y hb2 hL1 (hbq ▸ hy)
  have h4 := pol_bot hPB g (g ^ f) (fun a => (x a).1) c y (hbq ▸ hb2) hy
  have h5 : b.pol (g ^ f) y = (⟨g, [], List.ofFn fun a => ((x a).1, c a)⟩ : Lbl).pol (g ^ f) y := by
    rw [← hbq]
    unfold Lbl.pol
    rw [hblk]
  rw [hbq, h5, h4] at h3
  simp only [hξ']
  exact h2.trans h3.symm
end

namespace UpperTheory.Gal.InertialTypesAlt

theorem killsAll_holds : KillsAll := GlobalTheory.T.shintani_lift_kills_product_of_cusp_forms

theorem liftHc_holds : LiftHc := GlobalTheory.T.shintaniLift_harishChandraInduction_eq_twisted

theorem killsHc_holds : KillsHc := GlobalTheory.T.twistedHarishChandra_isotypic_part

theorem jAppend_holds : JAppend := fun F _ _ θ => (GlobalTheory.T.harishChandraProductCuspidalGL_list_properties F θ).2.1

theorem normEx_holds : NormEx := by
  intro F F' _ _ _ _ s hs t δ
  haveI : Finite F := Finite.of_injective _ (algebraMap F F').injective
  haveI : Fintype F := Fintype.ofFinite F
  refine GlobalTheory.T.every_element_is_norm F F' s (fun τ => ?_) t δ
  have e : s = FiniteField.frobeniusAlgEquivOfAlgebraic F F' := by
    ext z; rw [hs z, Nat.card_eq_fintype_card]; rfl
  obtain ⟨⟨i, _⟩, hi⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow F F').2 τ
  exact ⟨(i : ℤ), by rw [e]; simpa using hi⟩

theorem frobL_holds : FrobL := frobL frobTwo resCl parCons

theorem lblIso_holds : LblIso := lblIso (jdIso cuspIso)

theorem leTop_holds : LeTop := leTop liftOk liftBlocks (leRank liftOk)

theorem baseQ_holds : BaseQ := baseQ cardRes

theorem jdChar_holds : JDChar := jdChar hcChar

theorem typeOfLbl_holds : TypeOfLbl := typeOfLbl meetsIff frobL_holds jdEq

theorem lblOf_holds : LblOf :=
  lblOf meetsIff frobL_holds jdEq cuspChar tensTr cuspIrr tensFix (subqMap finSec UpperTheory.Gal.TypesAndIwahori.paraFactor) suppStd

theorem killsTrue_holds : KillsOn fun _ => True :=
  killsTrue (killsNil killsAll_holds) liftHc_holds killsHc_holds normEx_holds liftOk jdEq jdChar_holds liftDet

theorem lblOn_of (hT : FinTrace) (P₀ : Lbl → Prop) (h₁ : ∀ a l, P₀ a → P₀ (a.lift l)) (h₂ : KillsOn P₀) : LblOn P₀ :=
  lblOn (baseCase resEmbCompat lblIso_holds) liftsFix placeEx resEmbEx unrOfIne P₀ h₁
    (stepSplit stableOf resEmbCompat lblIso_holds P₀)
    (stepInert hT stableOf resEmbCompat (resDeg cardRes) liftOk jdEq P₀ h₂)

theorem lblTrue_of (hT : FinTrace) : LblOn fun _ => True := lblOn_of hT _ (fun _ _ _ => trivial) killsTrue_holds

theorem suppAny_of (hT : FinTrace) : SuppAny :=
  suppAny (lblOn_of hT _ (fun a l h => by simp only [Lbl.lift, h, List.map_nil]) (killsNil killsAll_holds)) lblOf_holds
    typeOfLbl_holds UpperTheory.Gal.TypesAndIwahori.suppOfType_holds UpperTheory.Gal.TypesAndIwahori.blockCount tameChars leTop_holds polTop polBot resEmbEx
    (unifTower liftsFix placeEx unrOfIne) baseQ_holds cardRes artRead (cuspIne tameRead typeChar nameOf baseQ_holds) suppIne

theorem lblMixed_holds : LblMixed :=
  lblMixed lblOf_holds group1 cuspFrob (inertOf typeChar baseQ_holds) unlFull
    (jdPair jAppend_holds hcOne (hcPair hcChar hcOne) (detPair frobL_holds jdEq) jdChar_holds) jdChar_holds
    (lblFull meetsIff frobL_holds jdEq tensTr avgMap (indMap UpperTheory.Gal.TypesAndIwahori.indSupp UpperTheory.Gal.TypesAndIwahori.paraFactor) tensInc)

theorem mixType_of (hT : FinTrace) : MixType :=
  mixType (lblTrue_of hT) lblMixed_holds sepOf leTop_holds polTop typeOfLbl_holds resEmbEx baseQ_holds cardRes

theorem suppAny_holds (h : GlobalTheory.DZA.InflMatching) : SuppAny := suppAny_of (L.finTrace_of_matching h)

theorem mixType_holds (h : GlobalTheory.DZA.InflMatching) : MixType := mixType_of (L.finTrace_of_matching h)

theorem suppBC_holds (h : GlobalTheory.DZA.InflMatching) : SuppBC := suppBC_of_mix (suppAny_holds h) (mixUnlinked (mixType_holds h))

end UpperTheory.Gal.InertialTypesAlt
end

namespace UpperTheory.Gal.InertialTypesAlt

theorem suppBC_outright : SuppBC := suppBC_holds L.inflMatch

end UpperTheory.Gal.InertialTypesAlt
