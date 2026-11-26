module

public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsDefs
public import GroundTheory.ProfiniteCohomology.PoitouTate.PoitouTateNineTermGs
public import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.GcohCmp

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsDualPf
noncomputable section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global ReciprocityTheory.Gal Formalism.ConjugateSelfDual

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

section Roots

variable {L : Type} [Field L] {N : ℕ} [NeZero N] (w : rootsOfUnity N L)

theorem rootsOfUnity_pow_N : w ^ N = 1 := by
  apply Subtype.ext
  rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
  exact (mem_rootsOfUnity N (w : Lˣ)).1 w.2

def rootOf : ZMod N →+ Additive (rootsOfUnity N L) where
  toFun c := Additive.ofMul (w ^ c.val)
  map_zero' := by simp
  map_add' a b := by
    show Additive.ofMul (w ^ (a + b).val) = Additive.ofMul (w ^ a.val) + Additive.ofMul (w ^ b.val)
    rw [← ofMul_mul, ← pow_add, ZMod.val_add]
    congr 1
    conv_rhs => rw [← Nat.mod_add_div (a.val + b.val) N, pow_add, pow_mul, rootsOfUnity_pow_N w,
      one_pow, mul_one]

theorem rootOf_apply (c : ZMod N) : rootOf w c = Additive.ofMul (w ^ c.val) := rfl

theorem rootOf_bijective (hw : IsPrimitiveRoot (((w : Lˣ) : L)) N) : Function.Bijective (rootOf w) := by
  have hwu : IsPrimitiveRoot w N := by
    rw [← IsPrimitiveRoot.coe_submonoidClass_iff, ← IsPrimitiveRoot.coe_units_iff]
    exact hw
  refine ⟨fun a b h => ?_, fun x => ?_⟩
  · have h' : w ^ a.val = w ^ b.val := Additive.ofMul.injective h
    exact ZMod.val_injective N (hwu.pow_inj (ZMod.val_lt a) (ZMod.val_lt b) h')
  · obtain ⟨i, hi, hx⟩ := hw.eq_pow_of_pow_eq_one
      (ξ := (((Additive.toMul x : rootsOfUnity N L) : Lˣ) : L)) (by
        have := (mem_rootsOfUnity N _).1 (Additive.toMul x).2
        rw [← Units.val_pow_eq_pow_val, this, Units.val_one])
    refine ⟨(i : ZMod N), ?_⟩
    rw [rootOf_apply, ZMod.val_natCast, Nat.mod_eq_of_lt hi]
    have : w ^ i = Additive.toMul x :=
      Subtype.ext (Units.ext (by rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val]; exact hx))
    rw [this]
    rfl

end Roots

section DualGen

variable {Γ H : Type} [Group Γ] [Group H] [TopologicalSpace Γ] [TopologicalSpace H] (θ : Γ ≃ₜ* H)
  {N : ℕ} [NeZero N]
  {M : Type} [AddCommGroup M] [Module (ZMod N) M] (ρ : Representation (ZMod N) Γ M)
  (χ : Γ →* (ZMod N)ˣ) (A D : Rep.{0} (ULift.{0} ℤ) H) (eM : M ≃+ A.V)
  (hM : ∀ g m, eM (ρ g m) = A.ρ (θ g) (eM m)) (rr : ZMod N ≃+ D.V)
  (hr : ∀ g c, D.ρ (θ g) (rr c) = rr ((χ g : ZMod N) * c))


include hM hr in
theorem dualGen : ∃ eD : TDual (ZMod N) M ≃+ (dualRep D A).V,
    (∀ g f, eD (twDual χ ρ g f) = (dualRep D A).ρ (θ g) (eD f)) ∧
      ∀ f m, (eD f : A.V →ₗ[ULift.{0} ℤ] D.V) (eM m) = rr (f m) := by
  let fwd : TDual (ZMod N) M → (A.V →ₗ[ULift.{0} ℤ] D.V) := fun f =>
    (uliftIntLinearEquivAddHom A.V D.V).symm
      (rr.toAddMonoidHom.comp (((f : M →ₗ[ZMod N] ZMod N)).toAddMonoidHom.comp eM.symm.toAddMonoidHom))
  let bwd : (A.V →ₗ[ULift.{0} ℤ] D.V) → TDual (ZMod N) M := fun φ =>
    (rr.symm.toAddMonoidHom.comp ((uliftIntLinearEquivAddHom A.V D.V φ).comp eM.toAddMonoidHom)).toZModLinearMap N
  let eD : TDual (ZMod N) M ≃+ (dualRep D A).V :=
    { toFun := fwd
      invFun := bwd
      left_inv := fun f => LinearMap.ext fun m => by
        show rr.symm (rr (f (eM.symm (eM m)))) = f m
        rw [AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
      right_inv := fun φ => LinearMap.ext fun a => by
        show rr (rr.symm (φ (eM (eM.symm a)))) = φ a
        rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
      map_add' := fun f f' => LinearMap.ext fun a => by
        show rr ((f + f') (eM.symm a)) = rr (f (eM.symm a)) + rr (f' (eM.symm a))
        rw [← map_add (f := _)]
        rfl }
  refine ⟨eD, fun g f => ?_, fun f m => ?_⟩
  · refine LinearMap.ext fun a => ?_
    have h1 : eM.symm (A.ρ (θ g⁻¹) a) = ρ g⁻¹ (eM.symm a) := by
      apply eM.injective
      rw [AddEquiv.apply_symm_apply, hM, AddEquiv.apply_symm_apply]
    show rr ((twDual χ ρ g f) (eM.symm a)) = D.ρ (θ g) (rr (f (eM.symm (A.ρ (θ g)⁻¹ a))))
    rw [hr, ← map_inv, h1]
    rfl
  · show rr (f (eM.symm (eM m))) = rr (f m)
    rw [AddEquiv.symm_apply_apply]

end DualGen

theorem exists_root_of_primitive {L : Type} [Field L] {N : ℕ} (hN0 : N ≠ 0) {z : L}
    (hz : IsPrimitiveRoot z N) : ∃ w : rootsOfUnity N L, ((w : Lˣ) : L) = z :=
  ⟨⟨(hz.isUnit hN0).unit, (mem_rootsOfUnity _ _).2 (Units.ext (by
      rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, hz.pow_eq_one, Units.val_one]))⟩,
    IsUnit.unit_spec _⟩


set_option maxHeartbeats 1000000 in
theorem gsRoots_act_rootOf (Kf : FiniteSubfield) [NumberField Kf.1] [IsAlgClosure Kf.1 (AlgebraicClosure ℚ)]
    (S : Finset (HeightOneSpectrum (𝓞 Kf.1))) {l r : ℕ} [Fact l.Prime] [NeZero (l ^ r)]
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ (l ^ r))
    (e : GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))) ≃ₜ*
        galUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))))
    (he : ∀ (σ : G Kf.1 (AlgebraicClosure ℚ))
        (y : maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))),
        ((e (toGS (AlgebraicClosure ℚ) _ σ) y :
          maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) :
            AlgebraicClosure ℚ) = σ (y : AlgebraicClosure ℚ))
    (μ : GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))) →* (ZMod (l ^ r))ˣ)
    (hμ : μ.comp (toGS (AlgebraicClosure ℚ) _) = cycMod Kf.1 (AlgebraicClosure ℚ) l r)
    (w : rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ)
      (S : Set (HeightOneSpectrum (𝓞 Kf.1)))))
    (hwv : (((w : (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ)
      (S : Set (HeightOneSpectrum (𝓞 Kf.1))))ˣ) : maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ)
      (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) : AlgebraicClosure ℚ) = ζ)
    (g : GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) (c : ZMod (l ^ r)) :
    (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)).ρ (e g) (rootOf w c) =
      rootOf w (((μ g : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) * c) := by
  induction g using QuotientGroup.induction_on with
  | H τ =>
  have hm : μ (toGS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))) τ) =
      cycMod Kf.1 (AlgebraicClosure ℚ) l r τ := DFunLike.congr_fun hμ τ
  have hτ : τ ζ = ζ ^ ((cycMod Kf.1 (AlgebraicClosure ℚ) l r τ : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)).val :=
    cyclotomicCharacter.spec (L := AlgebraicClosure ℚ) l
      (MulSemiringAction.toRingAut (G Kf.1 (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ) τ) ζ hζ.pow_eq_one
  have hζN : ζ ^ (l ^ r) = 1 := hζ.pow_eq_one
  have hmod : ∀ k : ℕ, ζ ^ (k % (l ^ r)) = ζ ^ k := fun k => by
    conv_rhs => rw [← Nat.mod_add_div k (l ^ r), pow_add, pow_mul, hζN, one_pow, mul_one]
  show (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)).ρ
      (e (toGS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))) τ)) (rootOf w c) =
    rootOf w (((μ (toGS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))) τ) :
      (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) * c)
  rw [hm]
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  apply Subtype.ext
  show ((e (toGS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))) τ)
      ((((w ^ c.val : rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))))) : (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))))ˣ) : maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))))) : maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) : AlgebraicClosure ℚ) =
    ((((w ^ (((cycMod Kf.1 (AlgebraicClosure ℚ) l r τ : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) * c).val :
      rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))))) : (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))))ˣ) : maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) : AlgebraicClosure ℚ)
  rw [he τ, SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, IntermediateField.coe_pow, hwv,
    SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, IntermediateField.coe_pow, hwv, map_pow, hτ,
    ← pow_mul, ZMod.val_mul, hmod]

theorem natCast_pow_not_mem (Kf : FiniteSubfield) (S : Finset (HeightOneSpectrum (𝓞 Kf.1))) {l r : ℕ}
    [Fact l.Prime] (hS : ContainsAbove S l) :
    ∀ v ∉ (S : Set (HeightOneSpectrum (𝓞 Kf.1))), (((l ^ r : ℕ) : ℕ) : 𝓞 Kf.1) ∉ v.asIdeal := by
  intro v hv h
  apply hv
  have : ((l : ℕ) : 𝓞 Kf.1) ^ r ∈ v.asIdeal := by simpa using h
  exact Finset.mem_coe.2 (hS v (v.isPrime.mem_of_pow_mem r this))

set_option maxHeartbeats 1000000 in
theorem dualCmp' (Kf : FiniteSubfield) [NumberField Kf.1] [IsAlgClosure Kf.1 (AlgebraicClosure ℚ)]
    (S : Finset (HeightOneSpectrum (𝓞 Kf.1))) {l r : ℕ} [Fact l.Prime] (hr : 0 < r)
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ (l ^ r)) (hS : ContainsAbove S l)
    (e : GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))) ≃ₜ*
        galUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))))
    (he : ∀ (σ : G Kf.1 (AlgebraicClosure ℚ))
        (y : maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))),
        ((e (toGS (AlgebraicClosure ℚ) _ σ) y :
          maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) :
            AlgebraicClosure ℚ) = σ (y : AlgebraicClosure ℚ))
    (μ : GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))) →* (ZMod (l ^ r))ˣ)
    (hμ : μ.comp (toGS (AlgebraicClosure ℚ) _) = cycMod Kf.1 (AlgebraicClosure ℚ) l r)
    {M : Type} [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M]
    (ρ : Representation (ZMod (l ^ r)) (GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) M)
    (A : Rep.{0} (ULift.{0} ℤ)
      (galUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))))
    [IsDiscreteRep A] (eM : M ≃+ A.V) (hM : ∀ g m, eM (ρ g m) = A.ρ (e g) (eM m)) :
    ∃ eD : TDual (ZMod (l ^ r)) M ≃+
        (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) A).V,
      (∀ g f, eD (twDual μ ρ g f) =
        (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) A).ρ (e g) (eD f)) ∧
      ∀ f m, ((((Additive.toMul ((eD f : A.V →ₗ[ULift.{0} ℤ] _) (eM m)) :
          rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ)
            (S : Set (HeightOneSpectrum (𝓞 Kf.1))))) :
          (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))))ˣ) :
            maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) :
              AlgebraicClosure ℚ) = ζ ^ (f m).val := by
  classical
  have hN0 : l ^ r ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
  have hmem : ζ ∈ maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))) :=
    mem_maxUnramifiedOutside_of_pow_eq_one _ hN0 (natCast_pow_not_mem Kf S hS) hζ.pow_eq_one
  haveI : NeZero (l ^ r) := ⟨hN0⟩
  have hζL : IsPrimitiveRoot (⟨ζ, hmem⟩ : maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) (l ^ r) := by
    rw [← IsPrimitiveRoot.coe_submonoidClass_iff]
    exact hζ
  have hex := exists_root_of_primitive (L := maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) hN0 hζL
  refine Exists.elim hex (fun w hwv => ?_)
  have hwv' : (((w : (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))))ˣ) : maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) : AlgebraicClosure ℚ) = ζ := congrArg Subtype.val hwv
  have hw : IsPrimitiveRoot (((w : (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))))ˣ) : maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))))) (l ^ r) := by
    rw [hwv]
    exact hζL
  let rr : ZMod (l ^ r) ≃+ (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)).V :=
    AddEquiv.ofBijective (rootOf w) (rootOf_bijective w hw)
  have hrr : ∀ c, rr c = rootOf w c := fun _ => rfl
  have hr : ∀ g c, (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)).ρ
      (e g) (rr c) = rr (((μ g : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) * c) := fun g c => by
    rw [hrr, hrr]
    exact gsRoots_act_rootOf Kf S ζ hζ e he μ hμ w hwv' g c
  refine Exists.elim (dualGen e ρ μ A
    (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) eM hM rr hr) (fun eD h => ?_)
  refine ⟨eD, h.1, fun f m => ?_⟩
  rw [h.2, hrr, rootOf_apply]
  show ((((w ^ (f m).val : rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))))) : (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))))ˣ) : maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) : AlgebraicClosure ℚ) =
    ζ ^ (f m).val
  rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, IntermediateField.coe_pow, hwv']

end PositivityTheory.Lit1.PTN
end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.FinalGenDefs
noncomputable section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global GroundTheory.LocalField
  ReciprocityTheory.Gal Formalism.ConjugateSelfDual GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

def urChar (K Ω : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field Ω] [Algebra K Ω] [HasUnramifiedRoots K Ω] (N : ℕ+) (σ : Gal(Ω/K)) : ZMod (N : ℕ) :=
  GroundTheory.LocalField.Abstract.ProfiniteInteger.proj N (Multiplicative.toAdd (unramifiedDegree K Ω σ))

theorem zmodToQZ_eq_nsmul {n : ℕ} [NeZero n] (c : ZMod n) :
    zmodToQZ n c = c.val • zmodToQZ n 1 := by
  conv_lhs => rw [← ZMod.natCast_zmod_val c]
  rw [← nsmul_one, map_nsmul]

end PositivityTheory.Lit1.PTN
end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.TransferCupDegreeZeroTwo
noncomputable section

open CategoryTheory MonoidalCategory TensorProduct GroundTheory.ProfCoh ReciprocityTheory.Gal

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

theorem transfer_cup_degree_zero_two {Lv Hv : Type} [Group Lv] [TopologicalSpace Lv] [IsTopologicalGroup Lv]
    [Group Hv] [TopologicalSpace Hv] [IsTopologicalGroup Hv] (ev : Hv ≃* Lv)
    (hevc : Continuous ev.toMonoidHom) {R : Type} [CommRing R] {M M' P : Type}
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
    [AddCommGroup M'] [Module R M'] [TopologicalSpace M'] [DiscreteTopology M']
    [AddCommGroup P] [Module R P] [TopologicalSpace P] [DiscreteTopology P]
    (rho : Representation R Lv M) (rho' : Representation R Lv M') (rhoP : Representation R Lv P)
    (b : M →ₗ[R] M' →ₗ[R] P) (hb : Continuous fun p : M × M' => b p.1 p.2)
    (hbe : ∀ g x y, b (rho g x) (rho' g y) = rhoP g (b x y))
    (A B C : Rep.{0} (ULift.{0} ℤ) Hv) [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C]
    (eA : M ≃+ A.V) (eB : M' ≃+ B.V)
    (heA : ∀ σ m, eA (rho (ev σ) m) = A.ρ σ (eA m))
    (heB : ∀ σ m, eB (rho' (ev σ) m) = B.ρ σ (eB m))
    (μ : A ⊗ B ⟶ C) (rel : P → C.V → Prop)
    (hbμ : ∀ x y, rel (b x y) (μ.hom (eA x ⊗ₜ[ULift.{0} ℤ] eB y)))
    (E : ↥(H0 rho) ≃+ cohomology A 0)
    (hE : ∀ (z : ↥(H0 rho)) (x : cocycles A 0),
      (∀ s, cochainOf A (cocycleι A 0 x) s = eA z.1) → E z = cohomologyπ A 0 x)
    (E' : H2 rho' ≃+ cohomology B 2)
    (hE' : ∀ (z : ↥(Z2 rho')) (x : cocycles B 2),
      (∀ s, cochainOf B (cocycleι B 2 x) s = eB (z.1 (ev (s 0), ev (s 1)))) →
        E' (Submodule.Quotient.mk z) = cohomologyπ B 2 x)
    {Q : Type} [AddCommGroup Q] (jp : H2 rhoP →+ Q) (J : cohomology C 2 →+ Q)
    (hJ : ∀ (W : ↥(Z2 rhoP)) (x : cocycles C 2),
      (∀ s, rel (W.1 (ev (s 0), ev (s 1))) (cochainOf C (cocycleι C 2 x) s)) →
        jp (Submodule.Quotient.mk W) = - J (cohomologyπ C 2 x))
    (m : ↥(H0 rho)) (z : ↥(Z2 rho')) :
    jp (cupProductH0H2 rho rho' rhoP b hb hbe m (Submodule.Quotient.mk z)) =
      - J (cupPairing μ (rfl : 0 + 2 = 2) (E m) (E' (Submodule.Quotient.mk z))) := by
  obtain ⟨e2, he2a, -⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gc2 Hv R M' (rho'.comp ev.toMonoidHom) B eB heB
  obtain ⟨x2, hx2⟩ := he2a (restrictCocycles2 rho' ev.toMonoidHom hevc z)
  have hm : ∀ σ, (rho.comp ev.toMonoidHom) σ m.1 = m.1 := fun σ => (mem_riemannRochSpace_iff_regularAt_everywhere rho m.1).1 m.2 (ev σ)
  obtain ⟨x0, hx0⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.exists_coc A 0 (fun _ => eA m.1) (IsLocallyConstant.const _)
    (by
      refine (PositivityTheory.LocalTateOrthogonality.Gcoh.d_comp (rho.comp ev.toMonoidHom) A eA heA 0 fun _ => m.1).trans ?_
      funext s
      rw [PositivityTheory.LocalTateOrthogonality.Gcoh.dn_zero, hm (s 0), sub_self]
      exact map_zero eA)
  have hEm : E m = cohomologyπ A 0 x0 := hE m x0 (fun s => congrFun hx0 s)
  have hEz : E' (Submodule.Quotient.mk z) = cohomologyπ B 2 x2 := hE' z x2 (fun s => hx2 s)
  rw [hEm, hEz, cupPairing_cohomologyπ]
  refine hJ (cupCocycleH0Z2 rho rho' rhoP b hb hbe m z) _ (fun s => ?_)
  rw [cochainOf_cocycleι_cyclesMap_cupCocycles]
  have h0 : Fin.partialProd s ⟨0, by omega⟩ = 1 := Fin.partialProd_zero s
  rw [h0, map_one]
  rw [show (cochainOf _ (cocycleι _ 0 x0) fun i : Fin 0 => s ⟨i, by omega⟩) = eA m.1 from
    congrFun hx0 _]
  rw [show (cochainOf _ (cocycleι _ 2 x2) fun j : Fin 2 => s ⟨0 + j, by omega⟩) =
    eB (z.1 (ev (s 0), ev (s 1))) from by rw [hx2]; rfl]
  exact hbμ _ _

theorem hloc2 {G D L H : Type} [Group G] [Group D] [Group L] [Group H] {R M : Type} [CommRing R]
    [AddCommGroup M] [Module R M] (ρ : Representation R G M) (φ : D →* G) (ev : L ≃* D) (e : G → H)
    (A : Rep.{0} (ULift.{0} ℤ) H) (eM : M ≃+ A.V)
    (hM : ∀ g m, eM (ρ g m) = A.ρ (e g) (eM m)) (F : L →* H) (hev : ∀ σ, e (φ (ev σ)) = F σ) :
    ∀ σ m, eM ((ρ.comp φ) (ev σ) m) = (Rep.res F A).ρ σ (eM m) := by
  intro σ m
  rw [MonoidHom.comp_apply, hM, hev]
  rfl

end PositivityTheory.Lit1.PTN
end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.ResH1BijectiveOfInverse
noncomputable section

open CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

theorem resH1_bijective_of_inverse {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] {R M : Type} [CommRing R]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
    (rho : Representation R G M) (ψ : H →* G) (hψ : Continuous ψ)
    (χ : G →* H) (hχ : Continuous χ) (h1 : ∀ g, ψ (χ g) = g) (h2 : ∀ h, χ (ψ h) = h) :
    Function.Bijective (resH1 rho ψ hψ) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    induction x using Submodule.Quotient.induction_on with
    | H z =>
      rw [Submodule.Quotient.mk_eq_zero]
      rw [resH1, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
      obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 hx
      refine (mem_coboundaries1 _ _).2 ⟨m, fun g => ?_⟩
      have e := hm (χ g)
      simp only [Submodule.coe_subtype] at e ⊢
      change z.1 (ψ (χ g)) = rho (ψ (χ g)) m - m at e
      rw [h1] at e
      exact e
  · intro x
    induction x using Submodule.Quotient.induction_on with
    | H z =>
      refine ⟨Submodule.Quotient.mk ⟨z.1 ∘ χ, z.2.1.comp hχ, fun g h => ?_⟩, ?_⟩
      · have e := z.2.2 (χ g) (χ h)
        simp only [Function.comp_apply, map_mul]
        rw [e]
        change z.1 (χ g) + rho (ψ (χ g)) (z.1 (χ h)) = _
        rw [h1]
      · rw [resH1, Submodule.mapQ_apply]
        congr 1
        apply Subtype.ext
        funext h
        change z.1 (χ (ψ h)) = z.1 h
        rw [h2]

theorem resCmp1' {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H] (θ : G ≃ₜ* H) {ι : Type} {Lv Hv : ι → Type}
    [∀ v, Group (Lv v)] [∀ v, TopologicalSpace (Lv v)] [∀ v, IsTopologicalGroup (Lv v)]
    [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)] [∀ v, IsTopologicalGroup (Hv v)]
    (lam : ∀ v, Lv v →* G) (hlam : ∀ v, Continuous (lam v)) (φ : ∀ v, Hv v →ₜ* H)
    (ev : ∀ v, Hv v ≃* Lv v) (hev1 : ∀ v, Continuous (ev v)) (hev2 : ∀ v, Continuous (ev v).symm)
    (hev : ∀ v σ, θ (lam v (ev v σ)) = φ v σ) {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [DiscreteTopology M] (rho : Representation R G M) (hc : ContAction rho)
    (A : Rep.{0} (ULift.{0} ℤ) H) [IsDiscreteRep A] (eM : M ≃+ A.V)
    (hM : ∀ g m, eM (rho g m) = A.ρ (θ g) (eM m)) :
    ∃ (E : H1 rho ≃+ cohomology A 1)
      (Ev : ∀ v, H1 (rho.comp (lam v)) ≃+ cohomology (Rep.res (φ v).toMonoidHom A) 1),
      ∀ v x, Ev v (resH1 rho (lam v) (hlam v) x) = ptRes φ A v 1 (E x) := by
  have hθs : Continuous (θ.symm : H ≃* G).toMonoidHom := θ.symm.continuous
  let rho' : Representation R H M := rho.comp (θ.symm : H ≃* G).toMonoidHom
  have hM' : ∀ h m, eM (rho' h m) = A.ρ h (eM m) := fun h m => by
    show eM (rho (θ.symm h) m) = _
    rw [hM]
    simp
  obtain ⟨e1, he1a, he1b⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gc1 H R M rho' A eM hM'
  have bij := resH1_bijective_of_inverse rho (θ.symm : H ≃* G).toMonoidHom hθs
    (θ : G ≃* H).toMonoidHom θ.continuous (fun g => θ.symm_apply_apply g) (fun h => θ.apply_symm_apply h)
  let r1 : H1 rho ≃ₗ[R] H1 rho' := LinearEquiv.ofBijective _ bij
  have hloc : ∀ v, ∀ σ m, eM (((rho.comp (lam v)).comp (ev v).toMonoidHom) σ m) =
      (Rep.res (φ v).toMonoidHom A).ρ σ (eM m) := fun v σ m => by
    show eM (rho (lam v (ev v σ)) m) = A.ρ (φ v σ) (eM m)
    rw [hM, hev]
  choose ev1 hev1a hev1b using fun v => PositivityTheory.LocalTateOrthogonality.Gcoh.gc1 (Hv v) R M
    ((rho.comp (lam v)).comp (ev v).toMonoidHom) (Rep.res (φ v).toMonoidHom A) eM (hloc v)
  have bijv := fun v => resH1_bijective_of_inverse (rho.comp (lam v)) (ev v).toMonoidHom (hev1 v)
    (ev v).symm.toMonoidHom (hev2 v) (fun g => (ev v).apply_symm_apply g) (fun h => (ev v).symm_apply_apply h)
  let rv : ∀ v, H1 (rho.comp (lam v)) ≃ₗ[R] H1 ((rho.comp (lam v)).comp (ev v).toMonoidHom) :=
    fun v => LinearEquiv.ofBijective _ (bijv v)
  refine ⟨r1.toAddEquiv.trans e1, fun v => (rv v).toAddEquiv.trans (ev1 v), fun v x => ?_⟩
  induction x using Submodule.Quotient.induction_on with
  | H z =>
    obtain ⟨y, hy⟩ := he1a (restrictCocycles1 rho (θ.symm : H ≃* G).toMonoidHom hθs z)
    have hE : e1 (r1 (Submodule.Quotient.mk z)) = cohomologyπ A 1 y := he1b _ y hy
    show ev1 v (rv v (resH1 rho (lam v) (hlam v) (Submodule.Quotient.mk z))) =
      ptRes φ A v 1 (e1 (r1 (Submodule.Quotient.mk z)))
    rw [hE]
    have hP : ptRes φ A v 1 (cohomologyπ A 1 y) =
        cohomologyπ _ 1 (cocyclesMapAlong (φ v).toMonoidHom (continuous_toMonoidHom (φ v)) (𝟙 _) 1 y) := by
      unfold ptRes
      exact congrArg (fun f => f.hom y) (cohomologyπ_cohomologyMapAlong (φ v).toMonoidHom
        (continuous_toMonoidHom (φ v)) (𝟙 _) 1)
    rw [hP]
    apply hev1b v
    intro s
    rw [cochainOf_cocycleι_cocyclesMapAlong]
    dsimp only
    rw [hy]
    change eM (z.1 (θ.symm (φ v (s 0)))) = eM (z.1 (lam v (ev v (s 0))))
    rw [← hev]
    exact congrArg (fun t => eM (z.1 t)) (θ.symm_apply_apply _)

end PositivityTheory.Lit1.PTN
end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.ResH2BijectiveOfInverse
noncomputable section

open CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

theorem resH2_bijective_of_inverse {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] {R M : Type} [CommRing R]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
    (rho : Representation R G M) (ψ : H →* G) (hψ : Continuous ψ)
    (χ : G →* H) (hχ : Continuous χ) (h1 : ∀ g, ψ (χ g) = g) (h2 : ∀ h, χ (ψ h) = h) :
    Function.Bijective (resH2 rho ψ hψ) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    induction x using Submodule.Quotient.induction_on with
    | H z =>
      rw [Submodule.Quotient.mk_eq_zero]
      rw [resH2, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
      obtain ⟨c, hc, hcf⟩ := (separated_dvr_second_cohomology_mem _ _).1 hx
      refine (separated_dvr_second_cohomology_mem _ _).2 ⟨c ∘ χ, hc.comp hχ, ?_⟩
      funext p
      have e := congrFun hcf (χ p.1, χ p.2)
      simp only [Submodule.coe_subtype] at e ⊢
      change _ = z.1 (ψ (χ p.1), ψ (χ p.2)) at e
      rw [h1, h1] at e
      rw [← e]
      simp [d1, h1]
  · intro x
    induction x using Submodule.Quotient.induction_on with
    | H z =>
      refine ⟨Submodule.Quotient.mk ⟨fun p => z.1 (χ p.1, χ p.2),
        z.2.1.comp (hχ.prodMap hχ), fun g h k => ?_⟩, ?_⟩
      · have e := z.2.2 (χ g) (χ h) (χ k)
        simp only [map_mul]
        change rho (ψ (χ g)) _ - _ + _ - _ = 0 at e
        rw [h1] at e
        exact e
      · rw [resH2, Submodule.mapQ_apply]
        congr 1
        apply Subtype.ext
        funext p
        change z.1 (χ (ψ p.1), χ (ψ p.2)) = z.1 p
        rw [h2, h2]

theorem resCmp2B {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H] (θ : G ≃ₜ* H) {ι : Type} {Lv Hv : ι → Type}
    [∀ v, Group (Lv v)] [∀ v, TopologicalSpace (Lv v)] [∀ v, IsTopologicalGroup (Lv v)]
    [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)] [∀ v, IsTopologicalGroup (Hv v)]
    (lam : ∀ v, Lv v →* G) (hlam : ∀ v, Continuous (lam v)) (φ : ∀ v, Hv v →ₜ* H)
    (ev : ∀ v, Hv v ≃* Lv v) (hev1 : ∀ v, Continuous (ev v)) (hev2 : ∀ v, Continuous (ev v).symm)
    (hev : ∀ v σ, θ (lam v (ev v σ)) = φ v σ) {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [DiscreteTopology M] (rho : Representation R G M) (hc : ContAction rho)
    (A : Rep.{0} (ULift.{0} ℤ) H) [IsDiscreteRep A] (eM : M ≃+ A.V)
    (hM : ∀ g m, eM (rho g m) = A.ρ (θ g) (eM m)) :
    ∃ (E : H2 rho ≃+ cohomology A 2)
      (Ev : ∀ v, H2 (rho.comp (lam v)) ≃+ cohomology (Rep.res (φ v).toMonoidHom A) 2),
      ∀ v x, Ev v (resH2 rho (lam v) (hlam v) x) = ptRes φ A v 2 (E x) := by
  have hθs : Continuous (θ.symm : H ≃* G).toMonoidHom := θ.symm.continuous
  let rho' : Representation R H M := rho.comp (θ.symm : H ≃* G).toMonoidHom
  have hM' : ∀ h m, eM (rho' h m) = A.ρ h (eM m) := fun h m => by
    show eM (rho (θ.symm h) m) = _
    rw [hM]
    exact congrArg (fun t => A.ρ t (eM m)) (θ.apply_symm_apply h)
  obtain ⟨e2, he2a, he2b⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gc2 H R M rho' A eM hM'
  have bij := resH2_bijective_of_inverse rho (θ.symm : H ≃* G).toMonoidHom hθs
    (θ : G ≃* H).toMonoidHom θ.continuous (fun g => θ.symm_apply_apply g)
    (fun h => θ.apply_symm_apply h)
  let r2 : H2 rho ≃ₗ[R] H2 rho' := LinearEquiv.ofBijective _ bij
  have hloc : ∀ v, ∀ σ m, eM (((rho.comp (lam v)).comp (ev v).toMonoidHom) σ m) =
      (Rep.res (φ v).toMonoidHom A).ρ σ (eM m) := fun v σ m => by
    show eM (rho (lam v (ev v σ)) m) = A.ρ (φ v σ) (eM m)
    rw [hM, hev]
  choose ev2 hev2a hev2b using fun v => PositivityTheory.LocalTateOrthogonality.Gcoh.gc2 (Hv v) R M
    ((rho.comp (lam v)).comp (ev v).toMonoidHom) (Rep.res (φ v).toMonoidHom A) eM (hloc v)
  have bijv := fun v => resH2_bijective_of_inverse (rho.comp (lam v)) (ev v).toMonoidHom (hev1 v)
    (ev v).symm.toMonoidHom (hev2 v) (fun g => (ev v).apply_symm_apply g)
    (fun h => (ev v).symm_apply_apply h)
  let rv : ∀ v, H2 (rho.comp (lam v)) ≃ₗ[R] H2 ((rho.comp (lam v)).comp (ev v).toMonoidHom) :=
    fun v => LinearEquiv.ofBijective _ (bijv v)
  refine ⟨r2.toAddEquiv.trans e2, fun v => (rv v).toAddEquiv.trans (ev2 v), fun v x => ?_⟩
  induction x using Submodule.Quotient.induction_on with
  | H z =>
    obtain ⟨y, hy⟩ := he2a (restrictCocycles2 rho (θ.symm : H ≃* G).toMonoidHom hθs z)
    have hE : e2 (r2 (Submodule.Quotient.mk z)) = cohomologyπ A 2 y := he2b _ y hy
    show ev2 v (rv v (resH2 rho (lam v) (hlam v) (Submodule.Quotient.mk z))) =
      ptRes φ A v 2 (e2 (r2 (Submodule.Quotient.mk z)))
    rw [hE]
    have hP : ptRes φ A v 2 (cohomologyπ A 2 y) =
        cohomologyπ _ 2 (cocyclesMapAlong (φ v).toMonoidHom (continuous_toMonoidHom (φ v)) (𝟙 _) 2 y) := by
      unfold ptRes
      exact congrArg (fun f => f.hom y) (cohomologyπ_cohomologyMapAlong (φ v).toMonoidHom
        (continuous_toMonoidHom (φ v)) (𝟙 _) 2)
    rw [hP]
    apply hev2b v
    intro s
    rw [cochainOf_cocycleι_cocyclesMapAlong]
    dsimp only
    rw [hy]
    change eM (z.1 (θ.symm (φ v (s 0)), θ.symm (φ v (s 1)))) =
      eM (z.1 (lam v (ev v (s 0)), lam v (ev v (s 1))))
    rw [← hev, ← hev]
    exact congrArg (fun t => eM (z.1 t))
      (Prod.ext (θ.symm_apply_apply _) (θ.symm_apply_apply _))

end PositivityTheory.Lit1.PTN
end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsDualQZ
noncomputable section

open GroundTheory.ProfCoh

namespace PositivityTheory.Lit1.PTN

theorem nsmul_eq_zero_of_zmod {N : ℕ} {X : Type} [AddCommGroup X] [Module (ZMod N) X] (a : X) :
    N • a = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod N), ZMod.natCast_self, zero_smul]

def dualQZ {N : ℕ} [NeZero N] {X Y : Type} [AddCommGroup X] [Module (ZMod N) X] [AddCommGroup Y]
    (E : X ≃+ Y) : Module.Dual (ZMod N) X ≃+ (Y →+ QZ) where
  toFun φ := (zmodToQZ N).comp (φ.toAddMonoidHom.comp E.symm.toAddMonoidHom)
  invFun ψ := (zmodOfQZ (ψ.comp E.toAddMonoidHom) (fun a => by
      rw [← map_nsmul, nsmul_eq_zero_of_zmod, map_zero])).toZModLinearMap N
  left_inv φ := LinearMap.ext fun a => zmodToQZ_injective (by
    simp [zmodToQZ_zmodOfQZ])
  right_inv ψ := AddMonoidHom.ext fun y => by
    simp [zmodToQZ_zmodOfQZ]
  map_add' φ φ' := AddMonoidHom.ext fun y => by simp

theorem dualQZ_apply {N : ℕ} [NeZero N] {X Y : Type} [AddCommGroup X] [Module (ZMod N) X]
    [AddCommGroup Y] (E : X ≃+ Y) (φ : Module.Dual (ZMod N) X) (y : Y) :
    dualQZ E φ y = zmodToQZ N (φ (E.symm y)) := rfl

end PositivityTheory.Lit1.PTN
end
end
