module

public import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangeMapMemLattice
public import Formalism.AdmissibleDesigns.InvariantsEqBotIff
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CoefficientBaseChange.CoordBaseChange
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CoefficientBaseChange.FinrankIInfKerEquiv
public import Formalism.SharpRestriction.LevelLetterCocycles.InvariantsGenerators
public import Formalism.SharpRestriction.LevelLetterCocycles.CoordHomMapTrace

@[expose] public section

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.MatOfEquiv
section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CoefExt
theorem coefficient_crystal_generation : Formalism.MainNotions.N.GlobalTheory.CoefCrysGen :=
  PI.CoefExt.coefCrysGen_of PI.CoefExt.invBaseChange
end

noncomputable section

open Classical TensorProduct

namespace Formalism.MainNotions.UnusedSlot80.BCW

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions

section Crys

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL LL' : Type} [Field LL] [Field LL'] [Algebra Qp LL]
    [Algebra Qp LL'] [Algebra LL LL'] [IsScalarTower Qp LL LL']
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

def matOf {k : ℕ} (b : Module.Basis (Fin k) LL V) (ρ : Representation LL G V) :
    G →* Matrix (Fin k) (Fin k) LL :=
  (LinearMap.toMatrixAlgEquiv b).toAlgHom.toRingHom.toMonoidHom.comp ρ

theorem matOf_equiv {k : ℕ} (b : Module.Basis (Fin k) LL V) (ρ : Representation LL G V) (g : G) (x : V) :
    b.equivFun (ρ g x) =
      ((Matrix.toLinAlgEquiv' : Matrix (Fin k) (Fin k) LL ≃ₐ[LL] _).toAlgHom.toRingHom.toMonoidHom.comp
        (matOf b ρ)) g (b.equivFun x) := by
  simp only [matOf, MonoidHom.coe_comp, Function.comp_apply, Module.Basis.equivFun_apply]
  change ⇑(b.repr ((ρ g) x)) = (Matrix.toLinAlgEquiv' (LinearMap.toMatrix b b (ρ g))) ⇑(b.repr x)
  rw [Matrix.toLinAlgEquiv'_apply, LinearMap.toMatrix_mulVec_repr]

theorem isCrys_bρ {k : ℕ} (b : Module.Basis (Fin k) LL V) (ρ : Representation LL G V)
    (h : IsCrys PD ρ) : IsCrys PD (bρ LL' ρ) := by
  have h1 := Formalism.MainNotions.N.K.Norm.isCrys_congr PD b.equivFun (matOf_equiv b ρ) h
  have h2 := coefficient_crystal_generation PD (IsScalarTower.toAlgHom Qp LL LL') (matOf b ρ) h1
  let b' : Module.Basis (Fin k) LL' (LL' ⊗[LL] V) := Algebra.TensorProduct.basis LL' b
  refine Formalism.MainNotions.N.K.Norm.isCrys_congr PD b'.equivFun.symm (fun g y => ?_) h2
  have hm : ∀ g, matOf b' (bρ LL' ρ) g =
      (IsScalarTower.toAlgHom Qp LL LL').mapMatrix (matOf b ρ g) := by
    intro g
    change LinearMap.toMatrix b' b' ((ρ g).baseChange LL') = (LinearMap.toMatrix b b (ρ g)).map _
    rw [LinearMap.toMatrix_baseChange]
    rfl
  apply b'.equivFun.injective
  rw [LinearEquiv.apply_symm_apply]
  have e1 := matOf_equiv b' (bρ LL' ρ) g (b'.equivFun.symm y)
  rw [LinearEquiv.apply_symm_apply] at e1
  rw [e1]
  simp only [MonoidHom.coe_comp, Function.comp_apply, hm]
  rfl

end Crys

section LocC

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL LL' O O' : Type} [Field LL] [Field LL']
    [Algebra Qp LL] [Algebra Qp LL'] [Algebra LL LL'] [IsScalarTower Qp LL LL']
    [TopologicalSpace LL] [TopologicalSpace LL'] [IsTopologicalRing LL'] [CommRing O] [IsDomain O]
    [Algebra O LL] [IsFractionRing O LL] [CommRing O'] [Algebra O' LL'] [Algebra O O'] [Algebra O LL']
    [IsScalarTower O O' LL'] [IsScalarTower O LL LL']

theorem crysLat_b (hc : Continuous (algebraMap LL LL')) (hO' : Function.Injective (algebraMap O' LL'))
    (T : LocLat G Qp LL O) (hT : Formalism.MainNotions.WachCoordinates.CrysLat PD T) :
    Formalism.MainNotions.WachCoordinates.CrysLat PD (bLoc (O' := O') hc hO' T) :=
  ⟨(bLoc (O' := O') hc hO' T).fdim, (bLoc (O' := O') hc hO' T).mtop, (bLoc (O' := O') hc hO' T).cont,
    isCrys_bρ PD (Module.finBasis LL T.V) T.ρ hT.2.2.2⟩

theorem finrank_b (hc : Continuous (algebraMap LL LL')) (hO' : Function.Injective (algebraMap O' LL'))
    (T : LocLat G Qp LL O) :
    Module.finrank LL' (bLoc (O' := O') hc hO' T).V = Module.finrank LL T.V :=
  Module.finrank_baseChange

end LocC

section Jmp

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL LL' : Type} [Field LL] [Field LL'] [Algebra Qp LL]
    [Algebra Qp LL'] [Algebra LL LL'] [IsScalarTower Qp LL LL']
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem isJumpV_bρ (hJ : Formalism.MainNotions.N.GlobalTheory.CoefJumpGen) {k : ℕ} (b : Module.Basis (Fin k) LL V)
    (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) (a : ℤ) :
    IsJumpV PD (bρ LL' ρ) ((IsScalarTower.toAlgHom Qp LL LL').comp τ) a ↔ IsJumpV PD ρ τ a := by
  let b' : Module.Basis (Fin k) LL' (LL' ⊗[LL] V) := Algebra.TensorProduct.basis LL' b
  have hm : ∀ g, matOf b' (bρ LL' ρ) g =
      (IsScalarTower.toAlgHom Qp LL LL').mapMatrix (matOf b ρ g) := by
    intro g
    change LinearMap.toMatrix b' b' ((ρ g).baseChange LL') = (LinearMap.toMatrix b b (ρ g)).map _
    rw [LinearMap.toMatrix_baseChange]
    rfl
  have e1 := Formalism.MainNotions.N.K.Norm.isJumpV_congr PD b.equivFun (matOf_equiv b ρ) τ a
  have e2 := hJ PD (IsScalarTower.toAlgHom Qp LL LL') (matOf b ρ) τ a
  have he' : ∀ g x, b'.equivFun (bρ LL' ρ g x) =
      ((Matrix.toLinAlgEquiv' : Matrix (Fin k) (Fin k) LL' ≃ₐ[LL'] _).toAlgHom.toRingHom.toMonoidHom.comp
        ((IsScalarTower.toAlgHom Qp LL LL').mapMatrix.toRingHom.toMonoidHom.comp (matOf b ρ))) g
        (b'.equivFun x) := by
    intro g x
    rw [matOf_equiv b' (bρ LL' ρ) g x]
    simp only [MonoidHom.coe_comp, Function.comp_apply, hm]
    rfl
  have e3 := Formalism.MainNotions.N.K.Norm.isJumpV_congr PD b'.equivFun he' ((IsScalarTower.toAlgHom Qp LL LL').comp τ) a
  rw [e3, ← e2, ← e1]

end Jmp

section Assemble

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL LL' O O' : Type} [Field LL] [Field LL']
    [Algebra Qp LL] [Algebra Qp LL'] [Algebra LL LL'] [IsScalarTower Qp LL LL']
    [TopologicalSpace LL] [TopologicalSpace LL'] [IsTopologicalRing LL'] [CommRing O] [IsDomain O]
    [Algebra O LL] [IsFractionRing O LL] [CommRing O'] [Algebra O' LL'] [Algebra O O'] [Algebra O LL']
    [IsScalarTower O O' LL'] [IsScalarTower O LL LL']

theorem bcAt_of (hc : Continuous (algebraMap LL LL')) (hO' : Function.Injective (algebraMap O' LL'))
    (hJ : Formalism.MainNotions.N.GlobalTheory.CoefJumpGen)
    (hL : ∀ (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L), Formalism.MainNotions.WachCoordinates.CrysLat PD T₁ →
      Formalism.MainNotions.WachCoordinates.CrysLat PD T₂ → F.Onto → ∀ e, (bHom (O' := O') hc hO' F).LiftF PD e → F.LiftF PD e)
    (hC : ∀ (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L), Formalism.MainNotions.WachCoordinates.CrysLat PD T₁ →
      Formalism.MainNotions.WachCoordinates.CrysLat PD T₂ → F.Onto → ∀ x, Formalism.MainNotions.TruncatedSeriesCountingBounds.ColLeR PD (bHom (O' := O') hc hO' F) x → Formalism.MainNotions.TruncatedSeriesCountingBounds.ColLeR PD F x) :
    Formalism.MainNotions.WachCoordinates.BCAt PD (LL := LL) (O := O) (O' := O') (IsScalarTower.toAlgHom Qp LL LL') := by
  intro T₁ T₂ F h₁ h₂ hF
  refine ⟨bLoc hc hO' T₁, bLoc hc hO' T₂, bHom hc hO' F, crysLat_b PD hc hO' T₁ h₁,
    crysLat_b PD hc hO' T₂ h₂, bHom_onto hc hO' F hF, fun τ a => ⟨?_, ?_⟩, finrank_b hc hO' T₂,
    hL T₁ T₂ F h₁ h₂ hF, hC T₁ T₂ F h₁ h₂ hF⟩
  · exact isJumpV_bρ PD hJ (Module.finBasis LL T₁.V) T₁.ρ τ a
  · exact isJumpV_bρ PD hJ (Module.finBasis LL T₂.V) T₂.ρ τ a

end Assemble

end Formalism.MainNotions.UnusedSlot80.BCW
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusIterateUniformizerUnitProducts
noncomputable section

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

section F2Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

def unitQProds : Submonoid (LetA O n) where
  carrier := {f | ∃ (u : (LetA O n)ˣ) (J : Multiset ℕ), f = (u : LetA O n) * (J.map fun j => (W.φA ^ j) W.Q).prod}
  one_mem' := ⟨1, 0, by simp⟩
  mul_mem' := by
    rintro a b ⟨u, J, rfl⟩ ⟨u', J', rfl⟩
    refine ⟨u * u', J + J', ?_⟩
    rw [Multiset.map_add (f := _), Multiset.prod_add, Units.val_mul]
    ring

theorem ps_mem_unitQProds (hs : W.s = 1) (hq : ∃ w : (LetA O n)ˣ, W.q = (w : LetA O n) * (W.π₀ + ((PD.p : ℕ) : LetA O n)))
    (s : ℕ) : (W.φA ^ s) (W.π₀ + ((PD.p : ℕ) : LetA O n)) ∈ unitQProds W := by
  obtain ⟨w, hw⟩ := hq
  have hQ : W.Q = W.q := by
    simp [LocWach.Q, hs]
  have e : W.π₀ + ((PD.p : ℕ) : LetA O n) = ((w⁻¹ : (LetA O n)ˣ) : LetA O n) * W.Q := by
    rw [hQ, hw, ← mul_assoc, Units.inv_mul, one_mul]
  refine ⟨Units.map ((W.φA ^ s : LetA O n →ₐ[O] LetA O n) : LetA O n →* LetA O n) w⁻¹, {s}, ?_⟩
  rw [e, map_mul]
  simp

theorem pi0pow_mem_aN (T : LocLat G Qp LL O) (M : ℕ) (hM : 1 ≤ (PD.p - 1) * M)
    (hπ : ∃ w : (LetA O n)ˣ, W.π₀ = (w : LetA O n) * letπ ^ (PD.p - 1)) (x : W.DD T) (hx : x ∈ W.N T) :
    W.π₀ ^ M • x ∈ Formalism.MainNotions.DeltaInvariantLattices.aN W T letπ := by
  obtain ⟨w, hw⟩ := hπ
  refine ⟨((w : LetA O n) ^ M * letπ ^ ((PD.p - 1) * M - 1)) • x, (W.N T).smul_mem _ hx, ?_⟩
  have e : W.π₀ ^ M = letπ * ((w : LetA O n) ^ M * letπ ^ ((PD.p - 1) * M - 1)) := by
    rw [hw, mul_pow, ← pow_mul]
    have : (PD.p - 1) * M = ((PD.p - 1) * M - 1) + 1 := by omega
    conv_lhs => rw [this]
    ring
  simp only [Formalism.MainNotions.DeltaInvariantLattices.smulA, LinearMap.smul_apply, LinearMap.id_apply]
  rw [e]
  simp only [mul_smul]

theorem restriction_eq_restriction_H1 (H : Subgroup G) (T : LocLat G Qp LL O) (κ : LatticeCohomology T.L) :
    Formalism.MainNotions.DeltaInvariantLattices.res H T κ = resH1 T H κ := rfl

theorem wach_cocycle_class_mem_latticeFiniteCohomology (hs : W.s = 1) (hp : PD.p ≠ 2) (hfr : Module.finrank K₀ K = 1)
    (h7 : Formalism.MainNotions.DeltaInvariantLattices.WachCrystallineExtension W) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (h2b : Formalism.MainNotions.DeltaInvariantLattices.HerrComplexSecondProperty W)
    (hres : ∀ (T : LocLat G Qp LL O) (pr : ↥(W.wachCocyclesDelta T)) (pr' : ↥(W.divisibleCocycles T)),
      (pr' : W.DD T × W.DD T) = (pr : W.DD T × W.DD T) → resH1 T W.GKs (W.clK T pr) = W.cl T pr')
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (M : ℕ) (hM : 1 ≤ (PD.p - 1) * M)
    (x : ↥(W.wachCocyclesDelta T)) (hz : ∃ z' ∈ W.NΔ T, (x : W.DD T × W.DD T).2 = W.π₀ ^ M • z')
    (Λ : LetA O n) (hΛ : Λ ∈ unitQProds W) (hy : Λ • (x : W.DD T × W.DD T).1 ∈ W.N T) :
    W.clK T x ∈ latticeFiniteCohomology PD T.L := by
  have hg : W.gamK = W.gam := W.gamK_eq_one hs hp
  have hr := ((h9 T hT hs hp).2.2 hfr).1
  obtain ⟨_, _, hπ, _, hq, _⟩ := hr
  have hq' : ∃ w : (LetA O n)ˣ, W.q = (w : LetA O n) * (W.π₀ + ((PD.p : ℕ) : LetA O n)) := by
    obtain ⟨w, hw⟩ := hq
    refine ⟨w, ?_⟩
    rw [hw]
    congr 1
    funext i
    simp [Formalism.MainNotions.DeltaInvariantLattices.Eat]
  have hmem : (x : W.DD T × W.DD T) ∈ W.divisibleCocycles T := by
    have h1 := (Submodule.mem_inf.mp x.2).1
    rw [hg] at h1
    exact h1
  rw [h2b T hT, restriction_eq_restriction_H1, hres T x ⟨_, hmem⟩ rfl]
  obtain ⟨u, J, rfl⟩ := hΛ
  obtain ⟨z', hz', hzz⟩ := hz
  have hy' : (J.map fun j => (W.φA ^ j) W.Q).prod • (x : W.DD T × W.DD T).1 ∈ W.N T := by
    have := (W.N T).smul_mem ((u⁻¹ : (LetA O n)ˣ) : LetA O n) hy
    rwa [← mul_smul, ← mul_assoc, Units.inv_mul, one_mul] at this
  have hzN : (x : W.DD T × W.DD T).2 ∈ Formalism.MainNotions.DeltaInvariantLattices.aN W T letπ := by
    rw [hzz]; exact pi0pow_mem_aN W T M hM hπ z' hz'.1
  have := h7 T hT J (x : W.DD T × W.DD T).1 (x : W.DD T × W.DD T).2 hy' hzN hmem
  exact this

theorem frobenius_iterate_uniformizer_unit_products (hs : W.s = 1) (hp : PD.p ≠ 2) (hfr : Module.finrank K₀ K = 1)
    (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (s : ℕ) :
    (W.φA ^ s) (W.π₀ + ((PD.p : ℕ) : LetA O n)) ∈ unitQProds W := by
  obtain ⟨_, _, _, _, hq, _⟩ := ((h9 T hT hs hp).2.2 hfr).1
  refine ps_mem_unitQProds W hs ?_ s
  obtain ⟨w, hw⟩ := hq
  refine ⟨w, ?_⟩
  rw [hw]
  congr 1
  funext i
  simp [Formalism.MainNotions.DeltaInvariantLattices.Eat]

end F2Core

section F2Rows

theorem caseA_of_le_Kur_of_ne_two {l : ℕ} [Fact l.Prime] (P : LocPrime l) (H : LocHW l P) {K LL : FinExt l} (h : Good K 1 LL)
    (hK : K.1 ≤ MaximalUnramifiedExtension l) (hl : l ≠ 2) : Formalism.MainNotions.LiftingTheory.CaseA (H.W K 1 LL h) := by
  refine ⟨⟨(algebraMap ↥(K0 K) ↥K.1).injective, fun x => ⟨⟨x, x.2, hK x.2⟩, rfl⟩⟩, H.W_s K 1 LL h, ?_⟩
  rw [P.PD_p]
  exact hl

theorem finrank_of_caseA {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n) (hA : Formalism.MainNotions.LiftingTheory.CaseA W) :
    Module.finrank K₀ K = 1 := by
  have e : K₀ ≃ₗ[K₀] K := LinearEquiv.ofBijective (Algebra.linearMap K₀ K) hA.1
  rw [← e.finrank_eq, Module.finrank_self]

end F2Rows

section F2At

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

theorem wach_cohomology_class_unramified_functor (hC : Formalism.MainNotions.LiftingTheory.CaseA W) (h7 : Formalism.MainNotions.DeltaInvariantLattices.WachCrystallineExtension W) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (h2b : Formalism.MainNotions.DeltaInvariantLattices.HerrComplexSecondProperty W)
    (hres : ∀ (T : LocLat G Qp LL O) (pr : ↥(W.wachCocyclesDelta T)) (pr' : ↥(W.divisibleCocycles T)),
      (pr' : W.DD T × W.DD T) = (pr : W.DD T × W.DD T) → resH1 T W.GKs (W.clK T pr) = W.cl T pr') :
    Formalism.MainNotions.WachCoordinates.F2 W := by
  intro hh M hM T hT _ c x hx hΛ
  have hfr := finrank_of_caseA W hC
  obtain ⟨Λ, ⟨k, m, rfl⟩, hΛy⟩ := hΛ
  refine wach_cocycle_class_mem_latticeFiniteCohomology W hC.2.1 hC.2.2 hfr h7 h9 h2b hres T hT M (by omega) x hx.2.2 _ ?_ hΛy.1
  exact Submonoid.prod_mem _ fun s _ => pow_mem (frobenius_iterate_uniformizer_unit_products W hC.2.1 hC.2.2 hfr h9 T hT s) _

theorem wach_cohomology_class_at_functor (h7 : Formalism.MainNotions.DeltaInvariantLattices.WachCrystallineExtension W) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (h2b : Formalism.MainNotions.DeltaInvariantLattices.HerrComplexSecondProperty W)
    (hres : W.gamK = W.gam → ∀ (T : LocLat G Qp LL O) (pr : ↥(W.wachCocyclesDelta T)) (pr' : ↥(W.divisibleCocycles T)),
      (pr' : W.DD T × W.DD T) = (pr : W.DD T × W.DD T) → resH1 T W.GKs (W.clK T pr) = W.cl T pr') :
    Formalism.MainNotions.ArcLiftingSetup.SecondWachFiltration W := by
  intro hC hh M hM T hT _ c y x Λ hΛ _ hΛy hcls
  have hfr := finrank_of_caseA W hC
  obtain ⟨z, hc, hz, rfl⟩ := hcls
  obtain ⟨y', hy', _, hyy⟩ := hΛy
  refine wach_cocycle_class_mem_latticeFiniteCohomology W hC.2.1 hC.2.2 hfr h7 h9 h2b (hres (W.gamK_eq_one hC.2.1 hC.2.2))
    T hT M (by omega) ⟨(y, z), hc⟩ hz Λ ?_ ?_
  · refine (Submonoid.closure_le.mpr ?_) hΛ
    rintro _ ⟨s, rfl⟩
    exact frobenius_iterate_uniformizer_unit_products W hC.2.1 hC.2.2 hfr h9 T hT s
  · show Λ • y ∈ W.N T
    rw [hyy, one_smul]
    exact hy'.1

end F2At

section F2Rows2

theorem wach_cohomology_class_unramified_case (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (h : SecondFiltrationHypotheses D HW F) :
    SecondFiltrationEtale D HW F := fun l _ K LL hA _ =>
  wach_cohomology_class_unramified_functor ((HW l).W K 1 LL hA.2.2) (caseA_of_le_Kur_of_ne_two (D.loc l) (HW l) hA.2.2 hA.1 hA.2.1)
    (h.1 l K 1 LL hA.2.2) (h.2.1 l K 1 LL hA.2.2) (h.2.2 l K 1 LL hA.2.2)
    (((F l).E K 1 LL hA.2.2).tie.clK_res
      (((HW l).W K 1 LL hA.2.2).gamK_eq_one (caseA_of_le_Kur_of_ne_two (D.loc l) (HW l) hA.2.2 hA.1 hA.2.1).2.1
        (caseA_of_le_Kur_of_ne_two (D.loc l) (HW l) hA.2.2 hA.1 hA.2.1).2.2))

theorem cohomology_class_unramified_statement (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : FamilyMassExplicitOfVolumeAgreement D HW F :=
  fun h => wach_cohomology_class_unramified_case D HW F h.1

theorem second_filtration_case_a_of_hypotheses (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (h : SecondFiltrationHypotheses D HW F) :
    SecondFiltrationArcLifting D HW F := fun l _ K LL hG _ _ =>
  wach_cohomology_class_at_functor ((HW l).W K 1 LL hG) (h.1 l K 1 LL hG) (h.2.1 l K 1 LL hG) (h.2.2 l K 1 LL hG)
    ((F l).E K 1 LL hG).tie.clK_res

theorem second_filtration_theorem_arc_lifting (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : SecondFiltrationTheoremArcLifting D HW F :=
  fun h => second_filtration_case_a_of_hypotheses D HW F h.1

end F2Rows2

end Formalism.MainNotions.UnusedSlot80
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.NormAHolds
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

theorem normA_holds {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) : normA P K LL := by
  intro T₁ T₂ F r S η m h up b hA hJ
  unfold Formalism.MainNotions.ElementDenominator.HypA at hA
  obtain ⟨hc1, hc2, hon, _, hj1, hηb, hsum, hjh, hposition⟩ := hA
  have hT1 : ∀ τ, JumpsInV (P.PD K) T₁.ρ τ
      (deep (up τ) (min (b τ) (h + 1)) S ∪ Set.Icc (-((min η h : ℕ) : ℤ)) (min η h : ℕ)) := by
    intro τ a ha
    have ha1 := hj1 τ a ha
    have hah := hjh τ a ha
    simp only [Set.mem_Icc] at hah
    rcases ha1 with h1 | h1
    · left
      unfold deep at h1 ⊢
      split_ifs at h1 ⊢ <;> simp only [Set.mem_Icc] at h1 ⊢ <;> push_cast <;> omega
    · right
      simp only [Set.mem_Icc] at h1 ⊢
      push_cast
      omega
  have hj2h : ∀ τ, JumpsInV (P.PD K) T₂.ρ τ (Set.Icc (-(h : ℤ)) h) := fun τ => hJ τ _ (hjh τ)
  refine ⟨min η h, h + S + 1, fun τ => min (b τ) (h + 1), min_le_left _ _, le_rfl, ?_⟩
  refine ⟨hc1, hc2, hon, hT1, fun τ => hJ τ _ (hT1 τ), fun τ => ?_, fun τ => ?_, by omega,
    fun τ => ?_, hposition⟩
  · have := hηb τ
    show min η h < min (b τ) (h + 1)
    omega
  · show min (b τ) (h + 1) + S ≤ h + S + 1
    omega
  · refine le_of_eq_of_le ?_ (hsum τ)
    apply Finset.sum_subset
    · intro x hx
      simp only [Finset.mem_Icc] at hx ⊢
      push_cast at hx
      omega
    · intro x hx hx'
      simp only [Finset.mem_Icc] at hx hx'
      push_cast at hx'
      have hnj : ¬ IsJumpV (P.PD K) T₂.ρ τ x := by
        intro hj
        have h2 := hj2h τ x hj
        simp only [Set.mem_Icc] at h2
        omega
      unfold IsJumpV at hnj
      push_neg at hnj
      unfold multV
      rw [hnj, sub_self]

theorem normR_holds (D : D7) : normR D := by
  intro l _ _ K LL _
  exact normA_holds (D.loc l) K LL

end Formalism.MainNotions.N.Ln34

end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.PhiItSmul
noncomputable section

namespace Formalism.MainNotions.WachCoordinates.Br

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions

section Model

variable {O : Type} [CommRing O] {Bs : Formalism.ExponentWindows.E.Base O} {n : ℕ} {V : Type} [AddCommGroup V]
  [Module (PowerSeries O) V]

def PsM (Bs : Formalism.ExponentWindows.E.Base O) : Submonoid (PowerSeries O) := Submonoid.closure (Set.range Bs.p)

theorem p_mem (s : ℕ) : Bs.p s ∈ PsM Bs := Submonoid.subset_closure ⟨s, rfl⟩

theorem q_mem : Bs.q ∈ PsM Bs := p_mem (Bs := Bs) 0

theorem φ_p (s : ℕ) : Bs.φ (Bs.p s) = Bs.p (s + 1) := by
  rw [Formalism.ExponentWindows.E.Base.p, Formalism.ExponentWindows.E.Base.p, Function.iterate_succ_apply']

theorem φ_mem {f : PowerSeries O} (hf : f ∈ PsM Bs) : Bs.φ f ∈ PsM Bs := by
  induction hf using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨s, rfl⟩ := hx
    rw [φ_p]
    exact p_mem _
  | one => rw [map_one]; exact one_mem _
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

theorem φit_mem (k : ℕ) {f : PowerSeries O} (hf : f ∈ PsM Bs) : (⇑Bs.φ)^[k] f ∈ PsM Bs := by
  induction k with
  | zero => exact hf
  | succ k ih => rw [Function.iterate_succ_apply']; exact φ_mem ih

theorem Lam_mem (H : ℕ → ℕ) (ell : ℕ) : Formalism.ExponentWindows.abelian₂ Bs.p H ell ∈ PsM Bs :=
  Submonoid.prod_mem _ fun s _ => pow_mem (p_mem s) _

variable (L : Formalism.ExponentWindows.E.Lat Bs n V)

theorem phiIt_smul' (i : ZMod n) (k : ℕ) (a : PowerSeries O) (x : V) :
    L.phiIt i k (a • x) = (⇑Bs.φ)^[k] a • L.phiIt i k x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Formalism.ExponentWindows.E.Lat.phiIt, ih, L.φ_semi, Function.iterate_succ_apply']
    rfl

theorem phiIt_N (hh : ℕ) (h5 : ∀ i, L.P5M i hh) (k : ℕ) :
    ∃ Pr ∈ PsM Bs, ∀ i, ∀ x ∈ L.N i, Pr • L.phiIt i k x ∈ L.N (i + (k : ZMod n)) := by
  induction k with
  | zero =>
    refine ⟨1, one_mem _, fun i x hx => ?_⟩
    rw [one_smul, Nat.cast_zero, add_zero]
    exact hx
  | succ k ih =>
    obtain ⟨Pr, hPr, h⟩ := ih
    refine ⟨Bs.q ^ hh * Bs.φ Pr, mul_mem (pow_mem q_mem _) (φ_mem hPr), fun i x hx => ?_⟩
    rw [Formalism.ExponentWindows.E.Lat.phiIt, mul_smul, ← L.φ_semi]
    apply h5
    have e : i + ((k + 1 : ℕ) : ZMod n) - 1 = i + (k : ZMod n) := by push_cast; ring
    rw [e]
    exact h i x hx

theorem pull_N (hh : ℕ) (h5 : ∀ i, L.P5M i hh) (k : ℕ) :
    ∃ Pr ∈ PsM Bs, ∀ i, ∀ x ∈ L.pull i k, Pr • x ∈ L.N (i + (k : ZMod n)) := by
  obtain ⟨Pr, hPr, h⟩ := phiIt_N L hh h5 k
  refine ⟨Pr, hPr, fun i x hx => ?_⟩
  have : L.pull i k ≤ Formalism.ExponentWindows.E.dv Pr (L.N (i + (k : ZMod n))) := by
    rw [Formalism.ExponentWindows.E.Lat.pull, Submodule.span_le]
    rintro _ ⟨u, hu, rfl⟩
    exact h i u hu
  exact this hx

theorem relay_N (hh : ℕ) (h5 : ∀ i, L.P5M i hh) (c c' : ZMod n) (k j : ℕ)
    (hc : c' + (k : ZMod n) = c) (Λ : PowerSeries O) (hΛ : Λ ∈ PsM Bs) (a : PowerSeries O) (w τ : V)
    (hw : w ∈ Formalism.ExponentWindows.E.dv Λ (L.pull c' k)) (hτ : τ ∈ L.pull c j) :
    ∃ Pr ∈ PsM Bs, Pr • (a • L.phiIt c j w - τ) ∈ L.N (c + (j : ZMod n)) := by
  obtain ⟨Prk, hPrk, hk⟩ := pull_N L hh h5 k
  obtain ⟨Prj, hPrj, hj⟩ := phiIt_N L hh h5 j
  obtain ⟨Prj', hPrj', hj'⟩ := pull_N L hh h5 j
  have h1 : (Prk * Λ) • w ∈ L.N c := by
    rw [mul_smul, ← hc]
    exact hk c' _ hw
  have h2 := hj c _ h1
  rw [phiIt_smul'] at h2
  have h3 := hj' c τ hτ
  refine ⟨Prj' * (Prj * (⇑Bs.φ)^[j] (Prk * Λ)),
    mul_mem hPrj' (mul_mem hPrj (φit_mem j (mul_mem hPrk hΛ))), ?_⟩
  rw [smul_sub]
  refine Submodule.sub_mem _ ?_ ?_
  · have : (Prj' * (Prj * (⇑Bs.φ)^[j] (Prk * Λ))) • a • L.phiIt c j w =
        (Prj' * a) • Prj • (⇑Bs.φ)^[j] (Prk * Λ) • L.phiIt c j w := by
      simp only [smul_smul]
      congr 1
      ring
    rw [this]
    exact Submodule.smul_mem _ _ h2
  · have : (Prj' * (Prj * (⇑Bs.φ)^[j] (Prk * Λ))) • τ = (Prj * (⇑Bs.φ)^[j] (Prk * Λ)) • Prj' • τ := by
      simp only [smul_smul]
      congr 1
      ring
    rw [this]
    exact Submodule.smul_mem _ _ h3

end Model

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {I : BaseId W} {T : LocLat G Qp LL O}

theorem prod_pad {R : Type} [CommMonoid R] (F : ℕ → R) (k : ℕ → ℕ) {m m' : ℕ} (h : m ≤ m') :
    ∏ s ∈ Finset.range m', F s ^ (if s < m then k s else 0) = ∏ s ∈ Finset.range m, F s ^ k s := by
  rw [← Finset.prod_subset (Finset.range_subset_range.2 h)]
  · exact Finset.prod_congr rfl fun s hs => by rw [if_pos (Finset.mem_range.1 hs)]
  · intro s _ hs
    rw [if_neg (fun h' => hs (Finset.mem_range.2 h')), pow_zero]

theorem isPs_one : IsPs W (1 : LetA O n) := ⟨fun _ => 0, 0, by simp⟩

theorem isPs_pS (s : ℕ) : IsPs W (pS W s) := by
  refine ⟨fun t => if t = s then 1 else 0, s + 1, ?_⟩
  rw [Finset.prod_eq_single s]
  · simp
  · intro t _ ht; simp [ht]
  · intro h; exact absurd (Finset.mem_range.2 (Nat.lt_succ_self s)) h

theorem isPs_mul {f g : LetA O n} (hf : IsPs W f) (hg : IsPs W g) : IsPs W (f * g) := by
  obtain ⟨k, m, rfl⟩ := hf
  obtain ⟨k', m', rfl⟩ := hg
  refine ⟨fun s => (if s < m then k s else 0) + (if s < m' then k' s else 0), m + m', ?_⟩
  simp only [pow_add, Finset.prod_mul_distrib]
  rw [prod_pad _ k (Nat.le_add_right m m'), prod_pad _ k' (Nat.le_add_left m' m)]

theorem isPs_d {f : PowerSeries O} (hf : f ∈ PsM I.Bs) : IsPs W (I.d f) := by
  induction hf using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨s, rfl⟩ := hx
    rw [I.d_p]
    exact isPs_pS s
  | one => rw [map_one]; exact isPs_one
  | mul x y _ _ hx hy => rw [map_mul]; exact isPs_mul hx hy

theorem d_smul_NΔ (f : PowerSeries O) {x : W.DD T} (hx : x ∈ W.NΔ T) : I.d f • x ∈ W.NΔ T :=
  ⟨(W.N T).smul_mem _ hx.1, fun δ hδ => by rw [γD_smulA, I.γA_Δ δ hδ, hx.2 δ hδ]⟩

theorem tot_NΔ (C : Coord W I T) (x : ZMod n → C.V) (hx : ∀ i, x i ∈ (latOf C).N i) :
    tot C x ∈ W.NΔ T :=
  ⟨(W.N T).sum_mem fun i _ => hx i, fun δ hδ => tot_Δ C x δ hδ⟩

theorem tot_single (C : Coord W I T) (k : ZMod n) (x : C.V) : tot C (Pi.single k x) = C.t k x := by
  rw [tot, Finset.sum_eq_single k]
  · rw [Pi.single_eq_same]
  · intro i _ hi
    rw [Pi.single_eq_of_ne hi, C.t_zero]
  · intro h; exact absurd (Finset.mem_univ k) h

theorem tot_sm (C : Coord W I T) (M : ℕ) (z : ZMod n → C.V)
    (hz : ∀ i, z i ∈ Formalism.ExponentWindows.E.sm (PowerSeries.X ^ M) ((latOf C).N i)) :
    tot C z ∈ mulSet W T (W.π₀ ^ M) (W.NΔ T) := by
  have h : ∀ i, ∃ x ∈ (latOf C).N i, (PowerSeries.X ^ M : PowerSeries O) • x = z i := fun i => hz i
  choose x hx hxz using h
  refine ⟨tot C x, tot_NΔ C x hx, ?_⟩
  have : z = (PowerSeries.X ^ M : PowerSeries O) • x := by
    funext i
    exact (hxz i).symm
  rw [this, tot_smul, map_pow, I.d_X]

theorem rho_of (hF1 : F1 W) (hF2 : F2 W) (hcr : IsCrys PD T.ρ) (hh M : ℕ)
    (hJ : ∀ τ : K →ₐ[Qp] LL, JumpsInV PD T.ρ τ (Set.Icc (-(hh : ℤ)) hh))
    (hM : hh < (PD.p - 1) * M) (C : Coord W I T) (h5 : ∀ i, (latOf C).P5M i hh)
    (c c' : ZMod n) (k : ℕ) (hc : c' + (k : ZMod n) = c) (Λ : PowerSeries O) (hΛ : Λ ∈ PsM I.Bs)
    (w : C.V) (hw : w ∈ Formalism.ExponentWindows.E.dv Λ ((latOf C).pull c' k)) (j g sig : ℕ) (y z : ZMod n → C.V)
    (hρ : (latOf C).IsRho c j M g sig w y z) : (y, z) ∈ Zf C := by
  obtain ⟨τ, ⟨hτ, -⟩, hy, hcoc, hz⟩ := hρ
  have hZ : (tot C y, tot C z) ∈ W.wachCocyclesDelta T := (cocycle_iff C y z).1 hcoc
  have hzM := tot_sm C M z hz
  have hyt : tot C y = C.t (c + (j : ZMod n)) (I.Bs.lc ^ sig • (latOf C).phiIt c j w - τ) := by
    rw [hy, tot_single]
  refine (mem_Zf C _).2 ⟨⟨_, hZ⟩, ?_, rfl⟩
  refine hF2 hh M hM T hcr hJ (c + (j : ZMod n)) ⟨_, hZ⟩ ⟨?_, ?_, hzM⟩ ?_
  · change (letE (c + (j : ZMod n)) : LetA O n) • tot C y = tot C y
    rw [hyt]
    exact C.t_letter _ _
  · change W.γD T W.gamK (tot C y) - tot C y ∈ mulSet W T (W.π₀ ^ M) (W.NΔ T)
    rw [((mem_Z1DΔ _ _).1 hZ).1]
    obtain ⟨x, hx, hxz⟩ := hzM
    obtain ⟨x', hx', hφ⟩ := ((hF1 hh M hM).1 T hcr hJ).1 x hx
    refine ⟨I.d I.Bs.q • x' - x, (W.NΔ T).sub_mem (d_smul_NΔ _ hx') hx, ?_⟩
    rw [hxz, hφ, smul_sub, I.d_q, mul_smul]
  · obtain ⟨Pr, hPr, hN⟩ := relay_N (latOf C) hh h5 c c' k j hc Λ hΛ (I.Bs.lc ^ sig) w τ hw hτ
    refine ⟨I.d Pr, isPs_d hPr, ?_⟩
    change I.d Pr • tot C y ∈ W.NΔ T
    rw [hyt, ← C.t_smul]
    exact ⟨hN, fun δ hδ => C.t_Δ _ _ δ hδ⟩

theorem rho_field (hF1 : F1 W) (hF2 : F2 W) (hcr : IsCrys PD T.ρ) (hh : ℕ)
    (hJ : ∀ τ : K →ₐ[Qp] LL, JumpsInV PD T.ρ τ (Set.Icc (-(hh : ℤ)) hh)) (hp : 2 ≤ PD.p)
    (C : Coord W I T) (h5 : ∀ i, (latOf C).P5M i hh) (Cu : Formalism.ExponentWindows.E.Cuts n) (H : ZMod n → ℕ → ℕ)
    (j g sig : ℕ) :
    ∀ c ∈ Cu.cuts, ∀ w, (latOf C).Wc Cu (Formalism.ExponentWindows.E.LamOf I.Bs Cu H) c w →
      ∀ y z, (latOf C).IsRho c j (Formalism.ExponentWindows.E.parM I.Bs.ℓ hh g) g sig w y z → (y, z) ∈ Zf C := by
  intro c _ w hw y z hρ
  refine rho_of hF1 hF2 hcr hh _ hJ ?_ C h5 c (c - (Cu.ell c : ZMod n)) (Cu.ell c) (sub_add_cancel _ _)
    _ (Lam_mem (H c) (Cu.ell c)) w hw.2 j g sig y z hρ
  rw [Formalism.ExponentWindows.E.parM, I.ℓ_eq]
  have := Nat.lt_mul_div_succ (hh + 2 * g) (show 0 < PD.p - 1 by omega)
  omega

end Formalism.MainNotions.WachCoordinates.Br
end
end
