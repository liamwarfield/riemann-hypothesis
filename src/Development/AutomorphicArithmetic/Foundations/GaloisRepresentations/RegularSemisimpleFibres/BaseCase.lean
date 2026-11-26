module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.GoodSeg

@[expose] public section
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.fin UpperTheory.V.Pr.IsCD.isLocalHom

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.BaseCase
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.InertialTypesAlt

def BaseCase : Prop :=
  ∀ (K Ω : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field Ω] [Algebra K Ω] (n : ℕ) (π : CuspSub K n)
    (A : ValuationSubring Ω) (Θ : IsLocalRing.ResidueField A →* ℂ) (v : HeightOneSpectrum (𝓞 K)) e e',
    ResEmb A v e → ResEmb A v e' → ∀ τ τ', π.IsLocComp v τ → π.IsLocComp v τ' →
    ∀ a : Lbl, HasLbl (Θ.comp e.toMonoidHom) τ.ρ a → HasLbl (Θ.comp e'.toMonoidHom) τ'.ρ a

end UpperTheory.Gal.InertialTypesAlt
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PSuppStd
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.InertialTypesAlt.suppStd :
    SuppStd := by
  intro k _ _ _ _ _ N V _ _ π S hS
  obtain ⟨t, x, hx, -⟩ := id hS
  have hsum := hS.sum_fst
  have hd : ∑ a, (x a).fst = N := by
    rw [← hx, Multiset.map_map] at hsum
    simpa [Finset.sum_eq_multiset_sum] using hsum
  let τ : IrrRep (GL (Fin N) k) := ⟨V, π, hS.isSmooth, hS.isIrreducible⟩
  refine ⟨t, x, hd, hx, ?_⟩
  exact SupportPerm.isSubquotient_prodIrr_of_hasSupport UpperTheory.Zero.LLC.Pr.zel UpperTheory.Zero.LLC.Pr.bz k N t τ x hd
    (hx ▸ hS)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PPlaceEx
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.InertialTypesAlt.placeEx :
    PlaceEx := by
  intro K M Ω _ _ _ _ _ _ _ _ A v hv n P
  let f : 𝓞 M →+* A := ((algebraMap M Ω).comp (algebraMap (𝓞 M) M)).codRestrict A fun x =>
    ReciprocityTheory.Gal.mem_of_isIntegral_int A (map_isIntegral_int (algebraMap M Ω) x.isIntegral_coe)
  let I : Ideal (𝓞 M) := (IsLocalRing.maximalIdeal A).comap f
  have hmem : ∀ x : 𝓞 M, x ∈ I ↔ A.valuation (algebraMap M Ω (x : M)) < 1 := fun x =>
    ValuationSubring.valuation_lt_one_iff A (f x)
  have hN0 : Ideal.absNorm v.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot
  have hval : A.valuation ((Ideal.absNorm v.asIdeal : ℕ) : Ω) < 1 := by
    have h := (hv ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 K)).2 (Ideal.absNorm_mem v.asIdeal)
    simpa using h
  have hne : I ≠ ⊥ := by
    intro h0
    have h1 : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 M) ∈ I := (hmem _).2 (by simpa using hval)
    rw [h0, Ideal.mem_bot] at h1
    exact Nat.cast_ne_zero.2 hN0 h1
  obtain ⟨τ, hτ, -⟩ := GlobalTheory.CuspRep.LocEx.exists_isLocComp GlobalTheory.automorphicFormsFiniteGL M n P
    ⟨I, Ideal.comap_isPrime _ _, hne⟩
  exact ⟨⟨I, Ideal.comap_isPrime _ _, hne⟩, fun x => (hmem x).symm, τ, hτ⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PUnifTower
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.InertialTypesAlt.unifTower :
    LiftsFix → PlaceEx → UnrOfIne → UnifTower := by
  intro hF hP hU E Ω _ _ _ n X Y hXY
  induction hXY using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro A _ v w hv hw g hg
    have hvw : v = w := by
      apply HeightOneSpectrum.ext
      ext x
      rw [← hv x, hw x]
    rw [← hvw]
    exact hg
  | @head X Z hs hZY ih =>
    intro A hI v w hv hw g hg
    obtain ⟨_, _, _, _, _⟩ := hs
    obtain ⟨u, hu, -⟩ := hP X.K Z.K Ω A v hv n Z.π
    have hfix : ∀ t ∈ Ine (F := X.K) A, UpperTheory.Gal.UnramifiedFromSplittingCriterion.Fixes Z.K t := by
      intro t ht z
      obtain ⟨y, hy⟩ := hF E Ω n Z Y hZY z
      have := hI t ht y
      rwa [hy] at this
    have hgu : ((g : ℕ) : 𝓞 Z.K) ∉ u.asIdeal ^ 2 := by
      have h3 := (hU X.K Z.K Ω A v u hv hu hfix).2.2 (g : 𝓞 X.K) hg
      rwa [map_natCast] at h3
    refine ih A (fun t ht => ?_) u w hu hw g hgu
    exact hI (AlgEquiv.restrictScalars X.K t) ht
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PPolBot
noncomputable section

open Polynomial

namespace UpperTheory.Gal.InertialTypesAlt

private theorem polBot_block (Q : ℕ) (x : ℂ) (hQ : 2 ≤ Q) (hx : x ^ (Q - 1) = 1) (c : ℕ → ℕ) (m : ℕ) :
    (((Multiset.range m).map fun j => ((1 : ℕ), ((c j : ℕ) : ZMod (Q - 1)))).map
      fun b => (X - C (x ^ b.2.val)) ^ b.1).prod = ∏ j ∈ Finset.range m, (X - C (x ^ c j)) := by
  haveI : NeZero (Q - 1) := ⟨by omega⟩
  rw [Multiset.map_map, Finset.prod_eq_multiset_prod, Finset.range_val]
  congr 1
  apply Multiset.map_congr rfl
  intro j _
  simp only [Function.comp, pow_one, ZMod.val_natCast]
  rw [← pow_eq_pow_mod _ hx]

private theorem polBot_list (q Q : ℕ) (x : ℂ) (hQ : 2 ≤ Q) (hx : x ^ (Q - 1) = 1) (L : List (ℕ × ℕ)) :
    (((L.map fun p => (Multiset.range p.1).map fun j =>
      ((1 : ℕ), ((p.2 * q ^ j * ((Q - 1) / (q ^ p.1 - 1)) : ℕ) : ZMod (Q - 1)))).sum).map
        fun b => (X - C (x ^ b.2.val)) ^ b.1).prod =
      (L.map fun p => ∏ j ∈ Finset.range p.1, (X - C (x ^ (p.2 * q ^ j * ((Q - 1) / (q ^ p.1 - 1)))))).prod := by
  induction L with
  | nil => simp
  | cons p L ih =>
    rw [List.map_cons, List.sum_cons, Multiset.map_add (f := _), Multiset.prod_add, ih, List.map_cons, List.prod_cons,
      polBot_block Q x hQ hx (fun j => p.2 * q ^ j * ((Q - 1) / (q ^ p.1 - 1))) p.1]

theorem polBot : PolBot := by
  intro q Q L x hQ hx
  have h := polBot_list q Q x hQ hx L
  simpa [Lbl.pol, Lbl.blocks] using h

end UpperTheory.Gal.InertialTypesAlt
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PFinSec
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.InertialTypesAlt.finSec :
    FinSec := by
  intro H U V _ _ _ _ _ _ ρ σ f hf hsurj
  haveI := Fintype.ofFinite H
  obtain ⟨s₀, hs₀⟩ := f.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hsurj)
  have hs₀' : ∀ y, f (s₀ y) = y := fun y => LinearMap.congr_fun hs₀ y
  have hc : (Fintype.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hρ : ∀ (a b : H) (x : U), ρ (a * b) x = ρ a (ρ b x) := fun a b x => by
    rw [map_mul]; rfl
  have hσ : ∀ (a b : H) (x : V), σ (a * b) x = σ a (σ b x) := fun a b x => by
    rw [map_mul]; rfl
  have hσ1 : ∀ x : V, σ 1 x = x := fun x => by
    rw [map_one]; rfl
  refine ⟨(Fintype.card H : ℂ)⁻¹ • ∑ g : H, (ρ g) ∘ₗ s₀ ∘ₗ (σ g⁻¹), ?_, ?_⟩
  · intro h x
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply, map_smul, map_sum]
    congr 1
    refine Fintype.sum_equiv (Equiv.mulLeft h⁻¹) _ _ fun g => ?_
    simp only [Equiv.coe_mulLeft, mul_inv_rev, inv_inv]
    rw [← hρ, mul_inv_cancel_left, hσ]
  · intro x
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply, map_smul, map_sum]
    have : ∀ g : H, f (ρ g (s₀ (σ g⁻¹ x))) = x := fun g => by
      rw [hf, hs₀', ← hσ, mul_inv_cancel, hσ1]
    simp only [this, Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PLeTop
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem label_le_preserves_splitting (h₁ : LiftOk) (h₂ : LiftBlocks) {a b : Lbl} (ha : a.Ok) (hab : a.Le b) :
    b.Ok ∧ b.rk = a.rk ∧ ∀ Q, b.Splits Q → a.Splits Q ∧ b.blocks Q = a.blocks Q := by
  induction hab with
  | refl => exact ⟨ha, rfl, fun Q hQ => ⟨hQ, rfl⟩⟩
  | @tail m c _ hstep ih =>
    obtain ⟨l, hl, rfl⟩ := hstep
    obtain ⟨hb, hrk, hS⟩ := ih
    obtain ⟨hc, hrk'⟩ := h₁ m l hl hb
    refine ⟨hc, hrk'.trans hrk, fun Q hQ => ?_⟩
    obtain ⟨hbQ, hblk⟩ := h₂ m l Q hl hb hQ
    obtain ⟨haQ, hblk'⟩ := hS Q hbQ
    exact ⟨haQ, hblk.trans hblk'⟩

theorem UpperTheory.Gal.InertialTypesAlt.leTop :
    LiftOk → LiftBlocks → LeRank → LeTop := by
  intro h₁ h₂ h₃ a b ha hab hs
  obtain ⟨hb, hrk, hS⟩ := label_le_preserves_splitting h₁ h₂ ha hab
  obtain ⟨f, hf, hq, hd⟩ := hs
  obtain ⟨c, hc, hbq, hp⟩ := h₃ a b ha hab
  have hcf : c = f := Nat.pow_right_injective ha.1 (hbq.symm.trans hq)
  subst hcf
  have hone : ∀ p ∈ b.L, p.1 = 1 := by
    intro p hpL
    obtain ⟨r, hr, hpr⟩ := hp p hpL
    have hr0 : 0 < r.1 := (ha.2.2 r hr).1
    rw [Nat.gcd_eq_left (hd r hr)] at hpr
    exact Nat.eq_of_mul_eq_mul_right hr0 (by simpa using hpr)
  refine ⟨hb, hrk, hone, (hS b.q ⟨1, Nat.one_pos, (pow_one _).symm, fun p hpL => ?_⟩).2⟩
  rw [hone p hpL]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PPolTop
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem polTop_sum (q : ℕ) (hq : 2 ≤ q) (L : List (ℕ × ℕ)) (hL : ∀ p ∈ L, p.1 = 1) :
    (L.map fun p => (Multiset.range p.1).map fun j =>
      ((1 : ℕ), ((p.2 * q ^ j * ((q - 1) / (q ^ p.1 - 1)) : ℕ) : ZMod (q - 1)))).sum =
      ((L.map fun p => (p.1, ((p.2 : ℕ) : ZMod (q - 1))) : List _) : Multiset _) := by
  induction L with
  | nil => simp
  | cons p L ih =>
    have h1 : p.1 = 1 := hL p (by simp)
    have hpos : 0 < q - 1 := by omega
    rw [List.map_cons, List.sum_cons, ih (fun r hr => hL r (List.mem_cons_of_mem _ hr)), List.map_cons,
      h1]
    simp [Nat.div_self hpos]

theorem UpperTheory.Gal.InertialTypesAlt.polTop :
    PolTop := by
  intro b x hq hL hx
  have hpos : 0 < b.q - 1 := by omega
  have hb : b.blocks b.q = ((b.D ++ b.L).map fun p => (p.1, ((p.2 : ℕ) : ZMod (b.q - 1))) : List _) := by
    unfold Lbl.blocks
    rw [polTop_sum b.q hq b.L hL, List.map_append, ← Multiset.coe_add]
    simp [Nat.div_self hpos]
  refine ⟨hb, ?_⟩
  unfold Lbl.pol
  rw [hb, Multiset.map_coe, Multiset.prod_coe, List.map_map]
  congr 1
  apply List.map_congr_left
  intro p _
  simp only [Function.comp]
  rw [ZMod.val_natCast, ← pow_eq_pow_mod p.2 hx]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PStepSplit
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.InertialTypesAlt.stepSplit :
    StableOf → ResEmbCompat → LblIso → ∀ P₀, StepAt P₀ id := by
  intro hS hC hI P₀ K M Ω _ _ _ _ _ _ _ _ _ _ _ _ hp n hn π P hW A Θ hΘ v w hsplit hunr e e' he he' τ τ' hτ hτ' a hP ha
  refine ⟨a, Relation.ReflTransGen.refl, ?_⟩
  obtain ⟨-, hSL⟩ := hS K M hp n hn π P hW
  obtain ⟨r, j, h1, h2, h3⟩ := hC K M Ω A v w e e' he he'
  have hs : UpperTheory.ConvolutionTheory.GM.Split M v := hsplit
  let i : v.adicCompletion K ≃+* w.1.adicCompletion M :=
    RingEquiv.ofBijective (completionMap v w.1) ⟨(completionMap v w.1).injective, hs w⟩
  have hi : ∀ x, i x = completionMap v w.1 x := fun _ => rfl
  have hic : Continuous i := continuous_completionMap v w.1
  have hal : ∀ x : K, i (algebraMap K _ x) = algebraMap M _ (algebraMap K M x) := fun x => by
    rw [hi, completionMap_algebraMap, IsScalarTower.algebraMap_apply K M (w.1.adicCompletion M)]
  obtain ⟨f, hf⟩ := hSL v w.1 i hic hal τ τ' hτ hτ'
  have he0 : w.1.asIdeal.ramificationIdx (𝓞 K) ≠ 0 := (Ideal.ramificationIdx_pos (R := 𝓞 K) w.1.asIdeal).ne'
  have hle : ∀ x y : w.1.adicCompletion M, valuation _ x ≤ valuation _ y ↔ Valued.v x ≤ Valued.v y := fun x y =>
    ValuativeRel.isEquiv (valuation (w.1.adicCompletion M)) Valued.v x y
  have hle' : ∀ x y : v.adicCompletion K, valuation _ x ≤ valuation _ y ↔ Valued.v x ≤ Valued.v y := fun x y =>
    ValuativeRel.isEquiv (valuation (v.adicCompletion K)) Valued.v x y
  have hv : ∀ x : v.adicCompletion K, valuation _ (i x) ≤ 1 ↔ valuation _ x ≤ 1 := fun x => by
    have a1 := hle (i x) (i 1)
    have a2 := hle' x 1
    rw [map_one (valuation (v.adicCompletion K))] at a2
    rw [map_one i, map_one (valuation (w.1.adicCompletion M))] at a1
    rw [a1, a2, ← map_one i, hi, hi, valued_completionMap, valued_completionMap]
    exact pow_le_pow_iff_left₀ zero_le zero_le he0
  have hcond : ∀ (x : 𝒪[v.adicCompletion K]) (y : 𝒪[w.1.adicCompletion M]), (y : w.1.adicCompletion M) = i x →
      j (algebraMap _ _ (IsLocalRing.residue _ x)) = algebraMap _ _ (IsLocalRing.residue _ y) :=
    fun x y hy => by rw [h2, h1 x y hy]
  have hθ : (Θ.comp e'.toMonoidHom).comp j.toMonoidHom = Θ.comp e.toMonoidHom :=
    MonoidHom.ext fun x => congrArg Θ (h3 x)
  exact hI _ _ i hv j hcond (Θ.comp e'.toMonoidHom) n τ.V τ'.V τ.ρ τ'.ρ f hf a (by rw [hθ]; exact ha)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PSuppIne
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.InertialTypesAlt

open UpperTheory.Zero.LLC in
private theorem charPol_seg' {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a} {rc : IrrGL (k := w.adicCompletion E) → WD h}
    (L : LawsT (h := h) a ha rc) (Δ : Segment (w.adicCompletion E)) (σ : Weil h) :
    (((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp (h := h) Δ.len)).charPol σ
      = (Δ.ms.map fun y => (rc y).charPol σ).prod := by
  rw [(GlobalTheory.WeilDeligne.charPol_lpTw_lpChar_lpSp E Ω A w h (rc Δ.first)).2 Δ.len σ, Segment.ms, Multiset.map_map]
  have h1 : ∀ j : Fin Δ.len, (rc (Δ.term j)).charPol σ = ((rc Δ.first).lpTw ((j : ℕ) : ℝ)).charPol σ := by
    intro j
    rw [Segment.term, show (((j : ℕ) : ℂ)) = ((((j : ℕ) : ℝ)) : ℂ) by push_cast; rfl, L.nu]
  change _ = ∏ j : Fin Δ.len, (fun y => (rc y).charPol σ) (Δ.term j)
  simp only [h1]
  rw [Fin.prod_univ_eq_prod_range (fun j => ((rc Δ.first).lpTw (j : ℝ)).charPol σ) Δ.len]
  rfl

open UpperTheory.Zero.LLC in
private theorem charPol_supp {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a} {rc : IrrGL (k := w.adicCompletion E) → WD h}
    (L : LawsT (h := h) a ha rc) (x : IrrGL (k := w.adicCompletion E))
    (S : Multiset (IrrGL (k := w.adicCompletion E))) (hS : HasSupport x.rep S) (σ : Weil h) :
    (rc x).charPol σ = (S.map fun y => (rc y).charPol σ).prod := by
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨𝔪, hm⟩ := Pr.exh (w.adicCompletion E) x
  have hs : HasSupport x.rep (msupp 𝔪) := GlobalTheory.LocGL.hasSupport_msupp_of_isL Pr.zel _ 𝔪 x hm
  obtain rfl := (goodSeg (w.adicCompletion E)).2.2 x _ _ hS hs
  rw [L.langlands 𝔪.toList x (by rw [Multiset.coe_toList]; exact hm), segSum, CuspExt.charPol_sumList, List.map_map,
    msupp, Multiset.map_bind, Multiset.prod_bind]
  have hl : ∀ (l : List (Segment (w.adicCompletion E))) (F : Segment (w.adicCompletion E) → ℂ[X]),
      (l.map F).prod = ((l : Multiset _).map F).prod := fun l F => by rw [Multiset.map_coe, Multiset.prod_coe]
  rw [hl, Multiset.coe_toList]
  exact congrArg Multiset.prod (Multiset.map_congr rfl fun Δ _ => charPol_seg' L Δ σ)

end UpperTheory.Gal.InertialTypesAlt

theorem UpperTheory.Gal.InertialTypesAlt.suppIne :
    SuppIne := by
  intro E Ω _ _ _ _ _ A v h rc hrc x S hS t
  obtain ⟨a, ha, L⟩ := hrc
  rw [WD.inePol_of_mem_Ine _ t.2,
    Multiset.map_congr rfl fun y _ => WD.inePol_of_mem_Ine (rc y) t.2]
  exact UpperTheory.Gal.InertialTypesAlt.charPol_supp L x S hS _
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PCuspIne
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 800000 in
theorem UpperTheory.Gal.InertialTypesAlt.cuspIne :
    TameRead → TypeChar → NameOf → BaseQ → CuspIne := by
  intro hT hC hN hB
  intro E Ω _ _ _ _ _ A v h g _ i hi Θ hΘ e y c hy hdz hreg htr rc hrc f hf hdiv t ϖ hϖ z hz
  obtain ⟨a, ha, hL⟩ := hrc
  have hty := (UpperTheory.Zero.LLC.typeIff E Ω A v h rc).mp hL.type y
  have hn : 0 < y.fst := Nat.pos_of_dvd_of_pos hdiv hf
  obtain ⟨D⟩ := UpperTheory.Zero.LLC.extEx E Ω A v h g i hi y.fst hn
  obtain ⟨⟨R, hR⟩, hsys⟩ := UpperTheory.Zero.LLC.resEx E Ω A v h g i hi y.fst hn D
  have hrank := (hsys R hR).rank
  obtain ⟨ι, hι⟩ := hT E Ω A v h g y.fst hn D R hR
  obtain ⟨_, hcard, ⟨r⟩⟩ := hB E v g i hi
  haveI : Finite 𝓀[HeightOneSpectrum.adicCompletion E v] :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact (Fact.out : g.Prime).ne_zero)
  obtain ⟨θ, hθ, hreg', hnames⟩ :=
    hN g y.fst hn 𝓀[HeightOneSpectrum.adicCompletion E v] D.K (IsLocalRing.ResidueField A) hrank r e ι Θ hΘ c hreg
  have hcls : GlobalTheory.LocLanglands.cls y.snd.rep = y := by
    unfold GlobalTheory.LocLanglands.cls
    exact IrrGL.of_rep y
  have hy' : (GlobalTheory.LocLanglands.cls y.snd.rep).IsCusp := by rw [hcls]; exact hy
  have hdz' : UpperTheory.Zero.LLC.DZ (GlobalTheory.LocLanglands.cls y.snd.rep) := by rw [hcls]; exact hdz
  obtain ⟨τ, hcusp, hinfl⟩ :=
    (UpperTheory.Zero.LLC.typeEx E Ω A v h g i hi y.fst hn y.snd.rep).1 hy' hdz'
  have hchar := hC E v g i hi r y τ hcusp hinfl
  have hnm := hnames τ (fun γ => (hchar γ).trans (htr γ))
  obtain ⟨_, hin⟩ := hty g i hi y.fst hn D R hR θ hreg' τ hcusp hnm y.snd.rep hcls hinfl
  rw [hin t]
  set N := (g ^ f - 1) / (g ^ y.fst - 1) with hN'
  have hdvd : g ^ y.fst - 1 ∣ g ^ f - 1 := by
    obtain ⟨m, hm⟩ := hdiv
    rw [hm, pow_mul]
    simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow (g ^ y.fst) 1 m
  have hϖ' : (ϖ ^ N) ^ (g ^ y.fst - 1) = (g : Ω) := by
    rw [← pow_mul, hN', Nat.div_mul_cancel hdvd, hϖ]
  have hz' : ((z ^ N : A) : Ω) = (t : G E Ω) (ϖ ^ N) / ϖ ^ N := by
    rw [map_pow, ← div_pow, ← hz]
    push_cast
    rfl
  have hιR : ι ((R t : D.Kˣ) : D.K) = (IsLocalRing.residue A z) ^ N := by
    rw [hι t (ϖ ^ N) hϖ' (z ^ N) hz', map_pow]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  congr 2
  rw [map_pow, Units.val_pow_eq_pow_val, hθ, hιR, map_pow, ← pow_mul, ← pow_mul]
  ring_nf
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PLeRank
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem gcd_step {m m' c l : ℕ} (hm : 0 < m) (hl : l.Prime) (h : m' * Nat.gcd m c = m) :
    (if l ∣ m' then m' / l else m') * Nat.gcd m (c * l) = m := by
  have hg : 0 < Nat.gcd m c := Nat.gcd_pos_of_pos_left _ hm
  obtain ⟨m₁, c₁, hco, hm₁, hc₁⟩ := Nat.exists_coprime m c
  have hmm : m₁ = m' := by
    apply Nat.eq_of_mul_eq_mul_right hg
    rw [← hm₁, h]
  subst hmm
  set g := Nat.gcd m c with hgdef
  have hgcd : Nat.gcd m (c * l) = Nat.gcd m₁ l * g := by
    have e : c * l = (c₁ * l) * g := by
      rw [hc₁]; ring
    rw [e]
    conv_lhs => rw [hm₁]
    rw [Nat.gcd_mul_right, Nat.Coprime.gcd_mul_left_cancel_right l hco.symm]
  rw [hgcd]
  split_ifs with hd
  · rw [Nat.gcd_eq_right hd, ← mul_assoc, Nat.div_mul_cancel hd]
    exact h
  · have : Nat.gcd m₁ l = 1 := ((Nat.Prime.coprime_iff_not_dvd hl).2 hd).symm
    rw [this, one_mul]
    exact h

theorem UpperTheory.Gal.InertialTypesAlt.leRank :
    LiftOk → LeRank := by
  intro hOk a b ha hab
  have key : b.Ok ∧ ∃ c : ℕ, 0 < c ∧ b.q = a.q ^ c ∧
      ∀ p ∈ b.L, ∃ r ∈ a.L, p.1 * Nat.gcd r.1 c = r.1 := by
    induction hab with
    | refl =>
      refine ⟨ha, 1, Nat.one_pos, (pow_one _).symm, fun p hp => ⟨p, hp, ?_⟩⟩
      rw [Nat.gcd_one_right, mul_one]
    | @tail b' b'' _ hs ih =>
      obtain ⟨hb, c, hc, hq, hL⟩ := ih
      obtain ⟨l, hl, rfl⟩ := hs
      refine ⟨(hOk b' l hl hb).1, c * l, Nat.mul_pos hc hl.pos, ?_, ?_⟩
      · change b'.q ^ l = _
        rw [hq, pow_mul]
      · intro p hp
        have hp' : p ∈ liftAll b'.q l b'.L := hp
        unfold liftAll at hp'
        obtain ⟨s, hs, hps⟩ := List.mem_flatMap.1 hp'
        obtain ⟨r, hr, hsr⟩ := hL s hs
        refine ⟨r, hr, ?_⟩
        have hm : 0 < r.1 := (ha.2.2 r hr).1
        have hstep := gcd_step (l := l) hm hl hsr
        have hp1 : p.1 = if l ∣ s.1 then s.1 / l else s.1 := by
          split_ifs at hps ⊢ with hd
          · simp only [liftL, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_map] at hps
            obtain ⟨i, -, rfl⟩ := hps
            rfl
          · simp only [List.mem_singleton] at hps
            rw [hps]
        rw [hp1]
        exact hstep
  exact key.2
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.SumFstMap
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem hcL_cons' {F : Type} [Field F] (p : Σ m : ℕ, GL (Fin m) F → ℂ)
    (Y : List (Σ m : ℕ, GL (Fin m) F → ℂ)) (b n : ℕ) (h : (Y.map Sigma.fst).sum = b) :
    hcL (p :: Y) n = hc p.1 b p.2 (hcL Y b) n := by
  subst h; rfl

private theorem sum_fst_map {F : Type} [Field F] (f : ℕ × ℕ → (Σ m : ℕ, GL (Fin m) F → ℂ))
    (hf : ∀ p, (f p).1 = p.1) (L : List (ℕ × ℕ)) :
    ((L.map f).map Sigma.fst).sum = deg L := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    simp only [List.map_cons, List.sum_cons, ih, hf]
    rfl

private theorem J_eq {F : Type} [Field F] (θ : AlgebraicClosure F →* ℂ) (L : List (ℕ × ℕ)) :
    ∀ n, J θ L n = hcL (L.map fun p => ⟨p.1, cusp θ p.1 p.2⟩) n := by
  induction L with
  | nil => intro n; rfl
  | cons p L ih =>
    intro n
    rw [J_cons, List.map_cons, hcL_cons' _ _ (deg L) n (sum_fst_map _ (fun _ => rfl) L), ih]

private theorem JD_eq {F : Type} [Field F] (θ : AlgebraicClosure F →* ℂ) (D L : List (ℕ × ℕ)) :
    ∀ n, JD θ D L n =
      hcL (D.map (fun p => ⟨p.1, detc θ p.1 p.2⟩) ++ L.map fun p => ⟨p.1, cusp θ p.1 p.2⟩) n := by
  induction D with
  | nil => intro n; simpa [JD_nil] using J_eq θ L n
  | cons p D ih =>
    intro n
    have hs : (((D.map (fun p : ℕ × ℕ => (⟨p.1, detc θ p.1 p.2⟩ : Σ m : ℕ, GL (Fin m) F → ℂ))) ++
        L.map (fun p : ℕ × ℕ => (⟨p.1, cusp θ p.1 p.2⟩ : Σ m : ℕ, GL (Fin m) F → ℂ))).map Sigma.fst).sum =
        deg D + deg L := by
      rw [List.map_append, List.sum_append, sum_fst_map _ (fun _ => rfl) D, sum_fst_map _ (fun _ => rfl) L]
    rw [JD_cons, List.map_cons, List.cons_append, hcL_cons' _ _ (deg D + deg L) n hs, ih]

private theorem cusp_one {F : Type} [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (k : ℕ) :
    cusp θ 1 k = detc θ 1 k := by
  haveI : Fintype F := Fintype.ofFinite F
  funext x
  have hcp : Matrix.charpoly (x : Matrix (Fin 1) (Fin 1) F) = X - C ((x : Matrix (Fin 1) (Fin 1) F) 0 0) := by
    simp [Matrix.charpoly, Matrix.charmatrix, Matrix.det_fin_one]
  have hval := GlobalTheory.T.invariantSubspaceMobiusInverseCharpoly_of_irreducible F (Fin 1 → F) _ (GlobalTheory.T.rootPowerSumCharacter_additive_and_X_sub_one_pow F θ k).1
    (Matrix.toLin' (x : Matrix (Fin 1) (Fin 1) F))
    (by rw [Matrix.charpoly_toLin', hcp]; exact irreducible_X_sub_C _)
  rw [Matrix.charpoly_toLin', hcp] at hval
  simp only [cusp, psiG, detc, Nat.sub_self, pow_zero, one_mul]
  rw [hval, Matrix.det_fin_one]
  simp [GlobalTheory.CuspGL.rootSum]

theorem UpperTheory.Gal.InertialTypesAlt.jdEq :
    JDEq := by
  intro F _ _ θ
  refine ⟨fun D L n => JD_eq θ D L n, cusp_one θ, ?_⟩
  intro D L n
  cases D with
  | nil =>
    cases L with
    | nil => intro x y; rfl
    | cons p L => exact (GlobalTheory.T.twistedHarishChandraInductionGL_isTwistedClassFunction F (RingHom.id F) _ _ n _ _).2.1
  | cons p D => exact (GlobalTheory.T.twistedHarishChandraInductionGL_isTwistedClassFunction F (RingHom.id F) _ _ n _ _).2.1
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PStepInert
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem card_eq_pow_finrank {F F' : Type} [Field F] [Field F'] [Finite F'] (m : Module F F') :
    Nat.card F' = Nat.card F ^ @Module.finrank F F' _ _ m := by
  letI := m
  exact Module.natCard_eq_pow_finrank

private theorem finrank_module_unique {F F' : Type} [Field F] [Field F'] [Finite F] [Finite F'] (m₁ m₂ : Module F F') :
    @Module.finrank F F' _ _ m₁ = @Module.finrank F F' _ _ m₂ :=
  Nat.pow_right_injective (Finite.one_lt_card (α := F))
    ((card_eq_pow_finrank m₁).symm.trans (card_eq_pow_finrank m₂))

theorem UpperTheory.Gal.InertialTypesAlt.stepInert :
    FinTrace → StableOf → ResEmbCompat → ResDeg → LiftOk → JDEq → ∀ P₀, KillsOn P₀ → StepAt P₀ Not := by
  intro hFT hSt hRE hRD hLO hJD P₀ hK K M Ω _ _ _ _ _ _ _ _ _ _ _ _ hl n hn π P hW A Θ hΘ v w hs hu e e' he he'
    τ τ' hτ hτ' a hPa hL
  obtain ⟨hOk, hq, hna, hMeets⟩ := hL
  obtain ⟨r, j, hr, hj, hje⟩ := hRE K M Ω A v w e e' he he'
  letI := r.toAlgebra
  obtain ⟨hfr, s, hsf⟩ := hRD K M hl v w hs hu
  have hfr' : @Module.finrank 𝓀[v.adicCompletion K] 𝓀[w.1.adicCompletion M] _ _ Algebra.toModule = Module.finrank K M :=
    (finrank_module_unique _ _).trans hfr
  have hl' : (@Module.finrank 𝓀[v.adicCompletion K] 𝓀[w.1.adicCompletion M] _ _ Algebra.toModule).Prime := by
    rw [hfr']
    exact hl
  let ι : AlgebraicClosure 𝓀[v.adicCompletion K] →ₐ[𝓀[v.adicCompletion K]] AlgebraicClosure 𝓀[w.1.adicCompletion M] :=
    { j.toRingHom with
      commutes' := fun x => by
        show j (algebraMap _ _ x) = _
        rw [hj x, IsScalarTower.algebraMap_apply 𝓀[v.adicCompletion K] 𝓀[w.1.adicCompletion M]
          (AlgebraicClosure 𝓀[w.1.adicCompletion M]) x]
        rfl }
  let θ' : AlgebraicClosure 𝓀[w.1.adicCompletion M] →* ℂ := Θ.comp e'.toMonoidHom
  have hθ' : Inj θ' := fun x y hx hy h =>
    e'.injective (hΘ _ _ (fun h0 => hx (e'.injective (by simpa using h0)))
      (fun h0 => hy (e'.injective (by simpa using h0))) h)
  have hpull : pullθ ι θ' = Θ.comp e.toMonoidHom := by
    ext x
    show Θ (e' (j x)) = Θ (e x)
    rw [hje]
  rw [← hpull] at hMeets
  subst hna
  have hlift := hLO a _ hl' hOk
  refine ⟨a.lift (@Module.finrank 𝓀[v.adicCompletion K] 𝓀[w.1.adicCompletion M] _ _ Algebra.toModule),
    Relation.ReflTransGen.single ⟨_, hl', rfl⟩, hlift.1, ?_, hlift.2.symm, ?_⟩
  · show a.q ^ _ = _
    rw [hq]
    exact (card_eq_pow_finrank _).symm
  · intro hz
    have hf : IsCl fun g => star (JD (pullθ ι θ') a.D a.L a.rk g) := fun x y => by
      show star _ = star _
      rw [(hJD _ (pullθ ι θ')).2.2 a.D a.L a.rk x y]
    have hTr := hFT K M hl a.rk hn π P (hSt K M hl a.rk hn π P hW).1 hW v w hs hu τ τ' hτ hτ' hr s hsf _ hf hMeets
    have hstar : ∀ δ, shLift s (fun g => star (JD (pullθ ι θ') a.D a.L a.rk g)) δ =
        star (shLift s (JD (pullθ ι θ') a.D a.L a.rk) δ) := fun δ => by
      unfold shLift
      split_ifs <;> simp
    haveI : FiniteDimensional ℂ (fixed τ'.ρ (KOne (w.1.adicCompletion M) (Fin a.rk))) :=
      (UpperTheory.Zero.LLC.Pr.adm _ _ _ _ τ'.smooth τ'.irred).2 _ GlobalTheory.StepData.isOpen_KOne
        (levelPre_bot (k := w.1.adicCompletion M) (n := Fin a.rk) ▸ isCompact_levelPre ⊥)
    refine hTr ?_
    simp only [hstar]
    exact hK _ _ s hl' hsf ι θ' hθ' a hPa hOk hq _ (levelZero τ'.ρ) hz
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PLblOf
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem isCl_trace {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G W) : IsCl fun g => LinearMap.trace ℂ W (ρ g) := by
  intro x y
  show LinearMap.trace ℂ W (ρ (y⁻¹ * x * y)) = LinearMap.trace ℂ W (ρ x)
  rw [map_mul ρ, map_mul ρ, LinearMap.trace_mul_comm, ← mul_assoc, ← map_mul ρ, mul_inv_cancel,
    map_one, one_mul]

theorem UpperTheory.Gal.InertialTypesAlt.lblOf :
    MeetsIff → FrobL → JDEq → CuspChar → TensTr → CuspIrr → TensFix → SubqMap → SuppStd → LblOf := by
  intro hM hF hJ hC hT hCI hTF hSQ hSS k _ _ _ _ _ θ hθ N V _ _ π S hS hfix
  obtain ⟨s, x, hd, hmap, hsub⟩ := hSS k N V π S hS
  have hmem : ∀ a, x a ∈ S := fun a => by
    rw [← hmap]
    exact Multiset.mem_map_of_mem _ (Finset.mem_univ_val a)
  have hcusp : ∀ a, (x a).IsCusp := fun a => hS.isCusp (hmem a)
  have hdz : ∀ y ∈ S, UpperTheory.Zero.LLC.DZ y := by
    obtain ⟨h, x', hx', hcs⟩ := id hS
    intro y hy
    rw [← hx'] at hy
    obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 hy
    have hv : ∃ v ∈ fixed π (KOne k (Fin N)), v ≠ 0 := Submodule.exists_mem_ne_zero_of_ne_bot hfix
    obtain ⟨v, hv, hv0⟩ := UpperTheory.Zero.LLC.Pr.dzs k N ⟨V, π, hS.isSmooth, hS.isIrreducible⟩ h
      (fun a => (x' a).fst)
      (fun a => ⟨(x' a).snd.rep.V, (x' a).rep, (x' a).snd.rep.smooth, (x' a).snd.rep.irr⟩) hcs hv a
    exact (Submodule.ne_bot_iff _).2 ⟨v, hv, hv0⟩
  have hdzx : ∀ a, UpperTheory.Zero.LLC.DZ (x a) := fun a => hdz _ (hmem a)
  have hci := fun a => hCI k (x a) (hcusp a) (hdzx a)
  have hch : ∀ a, ∃ j, Reg (Nat.card 𝓀[k]) (x a).fst j ∧
      ∀ γ, LinearMap.trace ℂ _ (levelZero (x a).rep γ) = cusp θ (x a).fst j γ := by
    intro a
    haveI := (hci a).1
    exact hC 𝓀[k] θ hθ (x a).fst (hcusp a).1 _ (levelZero (x a).rep) (hci a).2.1 (hci a).2.2
  choose c hreg htr using hch
  refine ⟨s, x, c, hmap, fun a => ⟨hcusp a, hdzx a, hreg a, htr a⟩, ?_⟩
  haveI : ∀ a, FiniteDimensional ℂ (fixed (x a).rep (KOne k (Fin (x a).fst))) := fun a => (hci a).1
  haveI hfinV : FiniteDimensional ℂ (fixed π (KOne k (Fin N))) := by
    obtain ⟨-, hadm⟩ := UpperTheory.Zero.LLC.Pr.adm k N V π hS.isSmooth hS.isIrreducible
    have := hadm (levelPre ⊥) (isOpen_levelPre ⊥) (isCompact_levelPre ⊥)
    rwa [levelPre_bot] at this
  obtain ⟨Φ, hΦ1, hΦ2⟩ := hTF k s (fun a => (x a).fst) (fun a => (x a).snd.rep.V) (fun a => (x a).rep)
    (fun a => (x a).snd.rep.smooth)
  obtain ⟨ψ, hψ0, hψ⟩ := hSQ k N s (fun a => (x a).fst) hd _ V _ (piTensor fun a => (x a).rep) π
    (piTensor fun a => levelZero (x a).rep) Φ hΦ1 hΦ2 hsub hfix
  obtain ⟨hfinZ, htrZ⟩ := hT s (fun a => GL (Fin (x a).fst) 𝓀[k])
    (fun a => fixed (x a).rep (KOne k (Fin (x a).fst))) (fun a => levelZero (x a).rep)
  obtain ⟨c0, hc0, hfr⟩ := hF 𝓀[k] s (fun a => (x a).fst) N hd
  have hmeet := ((hM (parab 𝓀[k] (stdBlocks (fun a => (x a).fst) hd)) _ _
    ((levelZero π).comp (parab 𝓀[k] (stdBlocks (fun a => (x a).fst) hd)).subtype)
    ((piTensor fun a => levelZero (x a).rep).comp
      (leviProj 𝓀[k] (stdBlocks (fun a => (x a).fst) hd)))).1).2 ⟨ψ, hψ0, fun p v => hψ p v⟩
  have hJD : JD θ [] (List.ofFn fun a => ((x a).fst, c a)) N =
      hcL (List.ofFn fun i => (⟨(x i).fst, cusp θ (x i).fst (c i)⟩ :
        (m : ℕ) × (GL (Fin m) 𝓀[k] → ℂ))) N := by
    rw [(hJ 𝓀[k] θ).1]
    simp [List.map_ofFn, Function.comp_def]
  refine ⟨⟨Finite.one_lt_card, by simp, ?_⟩, rfl, ?_, ?_⟩
  · intro p hp
    rw [List.mem_ofFn] at hp
    obtain ⟨a, rfl⟩ := hp
    exact ⟨(hcusp a).1, hreg a⟩
  · simp [Lbl.rk, GlobalTheory.Shin.deg, List.sum_ofFn, hd]
  · unfold Meets at hmeet ⊢
    rw [hJD, hfr _ _ (isCl_trace _)]
    refine mul_ne_zero hc0 ?_
    convert hmeet using 1
    refine finsum_congr fun p => ?_
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, htrZ, htr]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PFrobTwo
noncomputable section

open GlobalTheory.Shin
open scoped Classical

namespace UpperTheory.Gal.InertialTypesAlt

private theorem gal_id {F : Type} [Field F] (n : ℕ) (y : GL (Fin n) F) :
    gal (RingHom.id F) n y = y := by
  ext i j
  simp [gal]

private theorem inPar_one {F : Type} [Field F] (a n : ℕ) : InPar a (1 : GL (Fin n) F) := by
  intro i j hj hi
  have hij : i ≠ j := by
    rintro rfl
    omega
  simp [Matrix.one_apply_ne hij]

theorem frobTwo : FrobTwo := by
  intro F _ _ a b n _
  haveI : Fintype (GL (Fin n) F) := Fintype.ofFinite _
  haveI : Fintype (GL (Fin a) F) := Fintype.ofFinite _
  haveI : Fintype (GL (Fin b) F) := Fintype.ofFinite _
  have hN : (Nat.card {p : GL (Fin n) F // InPar a p} : ℂ) ≠ 0 := by
    haveI : Nonempty {p : GL (Fin n) F // InPar a p} := ⟨⟨1, inPar_one a n⟩⟩
    exact_mod_cast (Nat.card_pos (α := {p : GL (Fin n) F // InPar a p})).ne'
  have hG : (Fintype.card (GL (Fin n) F) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  refine ⟨star ((Nat.card {p : GL (Fin n) F // InPar a p} : ℂ)⁻¹) * (Fintype.card (GL (Fin n) F) : ℂ),
    mul_ne_zero (star_ne_zero.2 (inv_ne_zero hN)) hG, ?_⟩
  intro α β T hT
  set w : GL (Fin n) F → ℂ := fun p =>
    if InPar a p then star (α (tlG a p) * β (brG a b p)) * T p else 0 with hw
  have hleft : ∑ᶠ g, star (hc a b α β n g) * T g =
      star ((Nat.card {p : GL (Fin n) F // InPar a p} : ℂ)⁻¹) *
        ((Fintype.card (GL (Fin n) F) : ℂ) * ∑ p, w p) := by
    have hy : ∀ y : GL (Fin n) F,
        ∑ g : GL (Fin n) F, star (if InPar a (y⁻¹ * (g * y)) then
          α (tlG a (y⁻¹ * (g * y))) * β (brG a b (y⁻¹ * (g * y))) else 0) * T g = ∑ p, w p := by
      intro y
      refine Fintype.sum_equiv ((Equiv.mulRight y).trans (Equiv.mulLeft y⁻¹)) _ _ fun g => ?_
      have hTg : T (y⁻¹ * (g * y)) = T g := by
        rw [← mul_assoc]
        exact hT g y
      simp only [Equiv.trans_apply, Equiv.coe_mulLeft, Equiv.coe_mulRight, hw, hTg]
      split_ifs <;> simp
    rw [finsum_eq_sum_of_fintype]
    simp only [hc, hcTw, gal_id, finsum_eq_sum_of_fintype, star_mul', star_sum, mul_assoc,
      ← Finset.mul_sum]
    congr 1
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [hy, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hright : ∑ᶠ x, star (α x) * ∑ᶠ y, star (β y) * resT a b T x y = ∑ p, w p := by
    have key : ∀ p : GL (Fin n) F, ∑ x : GL (Fin a) F, ∑ y : GL (Fin b) F,
        star (α x) * (star (β y) *
          if InPar a p ∧ tlG a p = x ∧ brG a b p = y then T p else 0) = w p := by
      intro p
      rw [Finset.sum_eq_single (tlG a p), Finset.sum_eq_single (brG a b p)]
      · by_cases h : InPar a p <;> simp [hw, h, star_mul', mul_assoc]
      · intro y _ hy
        simp [Ne.symm hy]
      · simp
      · intro x _ hx
        simp [Ne.symm hx]
      · simp
    simp only [resT, finsum_eq_sum_of_fintype, Finset.mul_sum]
    rw [← Finset.sum_congr rfl fun p _ => key p]
    refine (Finset.sum_congr rfl fun x _ => Finset.sum_comm).trans ?_
    exact Finset.sum_comm
  rw [hleft, hright, mul_assoc]

end UpperTheory.Gal.InertialTypesAlt
end
end
