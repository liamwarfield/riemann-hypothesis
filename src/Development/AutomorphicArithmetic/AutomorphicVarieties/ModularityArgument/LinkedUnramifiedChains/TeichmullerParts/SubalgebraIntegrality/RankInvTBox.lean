module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.UnramifiedTrivialInertialType
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwJqMult
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwJqEmbed
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.CLocConjAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsSplitAtOfDecompositionLeRestrictionRange
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.UpOperatorEigenvalues.EigChar

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.RankInvTBox
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing Filter
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.Z.Mult (Cp At IsDec CompOf Mult)
open scoped Matrix TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.V.Z.J.D

section Abs

variable {G H W W' : Type} [Group G] [Group H] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

end Abs

section Fam

variable {I : Type} {Gi Wi Wi' : I → Type} {H X X' : Type} [∀ i, Group (Gi i)] [Group H]
  [∀ i, AddCommGroup (Wi i)] [∀ i, Module ℂ (Wi i)] [∀ i, AddCommGroup (Wi' i)] [∀ i, Module ℂ (Wi' i)]
  [AddCommGroup X] [Module ℂ X] [AddCommGroup X'] [Module ℂ X']

end Fam

end UpperTheory.V.Z.J.D
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.EigBox
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing Filter
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open scoped Matrix TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.V.Z.J.D

section Lin

variable {W W₂ Z Z₂ : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W₂] [Module ℂ W₂]
  [AddCommGroup Z] [Module ℂ Z] [AddCommGroup Z₂] [Module ℂ Z₂]

end Lin

section Rep

variable {G Y X : Type} [Group G] [AddCommGroup Y] [Module ℂ Y] [AddCommGroup X] [Module ℂ X]

end Rep

section Main

variable {L : Type} [Field L] [NumberField L] {n : ℕ} {V : Type} [Fintype V] {S : V → UpperTheory.V.W.Plc L}

end Main

section Inv

variable {G H : Type} [Group G] [Group H] {m : ℕ} (K₁ : Subgroup G) (K₂ : Subgroup H) (τ₀ : K₁ →* GL (Fin m) ℂ)

end Inv

section Box

variable {G H W W' : Type} [Group G] [Group H] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

end Box

end UpperTheory.V.Z.J.D
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.PartRep
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing Filter
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.Z.Mult (Cp At IsDec CompOf Mult)
open scoped Matrix TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.V.Z.J.D

end UpperTheory.V.Z.J.D
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.EquivOfChar
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

namespace UpperTheory.V.Z.J.D

section Abs

variable {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]

private def mulMap (P K : Subgroup G) (hK : IsOpen (K : Set G)) (σ σ' : Representation ℂ P W) (c : G → ℂˣ)
    (hl : ∀ (p : P) (x : G) (v : W), ((c ((p : G) * x) : ℂˣ) : ℂ) • σ p v = σ' p (((c x : ℂˣ) : ℂ) • v))
    (hr : ∀ κ ∈ K, ∀ x, c (x * κ) = c x) : smoothPart (ind P σ) →ₗ[ℂ] smoothPart (ind P σ') where
  toFun f := ⟨⟨fun x => ((c x : ℂˣ) : ℂ) • f.1.1 x, fun p x => by
      have h := f.1.2 p x
      show ((c ((p : G) * x) : ℂˣ) : ℂ) • f.1.1 ((p : G) * x) = _
      rw [h]
      exact hl p x _⟩, by
      refine mem_smoothPart_of_nhds (Filter.mem_of_superset
        (Filter.inter_mem (f.2.mem_nhds (by simp)) (hK.mem_nhds K.one_mem)) ?_)
      rintro g ⟨h1, h2⟩
      have h3 : ind P σ g f.1 = f.1 := h1
      refine Subtype.ext (funext fun x => ?_)
      have h4 : f.1.1 (x * g) = f.1.1 x := congrArg (fun φ : indSpace P σ => φ.1 x) h3
      show ((c (x * g) : ℂˣ) : ℂ) • f.1.1 (x * g) = ((c x : ℂˣ) : ℂ) • f.1.1 x
      rw [h4, hr g h2]⟩
  map_add' f f' := Subtype.ext (Subtype.ext (funext fun x => smul_add _ (f.1.1 x) (f'.1.1 x)))
  map_smul' a f := Subtype.ext (Subtype.ext (funext fun x => smul_comm _ a (f.1.1 x)))

private theorem equiv_of_char (P K : Subgroup G) (hK : IsOpen (K : Set G))
    (hPK : ∀ x : G, ∃ p : P, ∃ w ∈ K, x = (p : G) * w) (σ σ' : Representation ℂ P W) (R : P →* ℂˣ)
    (hR : ∀ p : P, (p : G) ∈ K → R p = 1) (hσ : ∀ (p : P) (v : W), σ' p v = ((R p : ℂˣ) : ℂ) • σ p v) :
    Nonempty (Representation.Equiv ((smInd P σ).comp K.subtype) ((smInd P σ').comp K.subtype)) := by
  obtain ⟨c, hc⟩ : ∃ c : G → ℂˣ, ∀ (p : P) (w : G), w ∈ K → c ((p : G) * w) = R p := by
    refine ⟨fun x => R (Classical.choose (hPK x)), fun p w hw => ?_⟩
    obtain ⟨w', hw', hx⟩ := Classical.choose_spec (hPK ((p : G) * w))
    set q := Classical.choose (hPK ((p : G) * w))
    have hqp : ((q⁻¹ * p : P) : G) ∈ K := by
      have : ((q⁻¹ * p : P) : G) = w' * w⁻¹ := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_eq_iff_eq_mul, ← mul_assoc, ← hx, mul_inv_cancel_right]
      rw [this]
      exact K.mul_mem hw' (K.inv_mem hw)
    have := hR _ hqp
    rw [map_mul, map_inv, inv_mul_eq_one] at this
    exact this
  have hr : ∀ κ ∈ K, ∀ x, c (x * κ) = c x := by
    intro κ hκ x
    obtain ⟨p, w, hw, rfl⟩ := hPK x
    rw [mul_assoc, hc _ _ (K.mul_mem hw hκ), hc _ _ hw]
  have hmul : ∀ (p : P) (x : G), c ((p : G) * x) = R p * c x := by
    intro p x
    obtain ⟨q, w, hw, rfl⟩ := hPK x
    rw [← mul_assoc, ← Subgroup.coe_mul, hc _ _ hw, hc _ _ hw, map_mul]
  have hl : ∀ (p : P) (x : G) (v : W), ((c ((p : G) * x) : ℂˣ) : ℂ) • σ p v = σ' p (((c x : ℂˣ) : ℂ) • v) := by
    intro p x v
    rw [hσ, map_smul, smul_smul, hmul, Units.val_mul]
  have hl' : ∀ (p : P) (x : G) (v : W),
      ((((fun y => (c y)⁻¹) ((p : G) * x)) : ℂˣ) : ℂ) • σ' p v = σ p ((((fun y => (c y)⁻¹) x : ℂˣ) : ℂ) • v) := by
    intro p x v
    simp only [hσ, map_smul, smul_smul, hmul, ← Units.val_mul]
    congr 2
    rw [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
  have hr' : ∀ κ ∈ K, ∀ x, (fun y => (c y)⁻¹) (x * κ) = (fun y => (c y)⁻¹) x := by
    intro κ hκ x
    simp only [hr κ hκ x]
  refine ⟨{ toFun := mulMap P K hK σ σ' c hl hr
            map_add' := (mulMap P K hK σ σ' c hl hr).map_add
            map_smul' := (mulMap P K hK σ σ' c hl hr).map_smul
            isIntertwining' := ?_
            invFun := mulMap P K hK σ' σ (fun y => (c y)⁻¹) hl' hr'
            left_inv := ?_
            right_inv := ?_ }⟩
  · intro g
    refine LinearMap.ext fun f => Subtype.ext (Subtype.ext (funext fun x => ?_))
    show ((c x : ℂˣ) : ℂ) • f.1.1 (x * g) = ((c (x * g) : ℂˣ) : ℂ) • f.1.1 (x * g)
    rw [hr g g.2]
  · intro f
    refine Subtype.ext (Subtype.ext (funext fun x => ?_))
    show (((c x)⁻¹ : ℂˣ) : ℂ) • (((c x : ℂˣ) : ℂ) • f.1.1 x) = f.1.1 x
    rw [smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  · intro f
    refine Subtype.ext (Subtype.ext (funext fun x => ?_))
    show ((c x : ℂˣ) : ℂ) • ((((c x)⁻¹ : ℂˣ) : ℂ) • f.1.1 x) = f.1.1 x
    rw [smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]

end Abs

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem exists_pw (x : GL (Fin n) k) :
    ∃ p : parab k (points (Fin n)), ∃ w ∈ KO k (Fin n), x = (p : GL (Fin n) k) * w := by
  obtain ⟨u, g, w, hw, hx⟩ := UnitInd.exists_iwasawa (points (Fin n)) x
  refine ⟨⟨(u : GL (Fin n) k) * leviEmb k (points (Fin n)) g,
    mul_mem (unipRad_le_parab k (points (Fin n)) u.2) (leviEmb_mem_parab k (points (Fin n)) g)⟩, w, hw, hx⟩

open GlobalTheory.SmGL.PrinProd in
private theorem dg_mem_Uo (p : parab k (points (Fin n))) (hp : (p : GL (Fin n) k) ∈ KO k (Fin n)) (i : Fin n) :
    dg p i ∈ UpperTheory.V.Hi.Uo k := by
  have h1 := ((GlobalTheory.SplitFlip.mem_KO_iff _).1 hp).1 i i
  have h2 := ((GlobalTheory.SplitFlip.mem_KO_iff _).1 hp).2 i i
  rw [← PrinProd.val_dg] at h1
  have h3 : ((dg p⁻¹ i : kˣ) : k) ∈ 𝒪[k] := by
    rw [PrinProd.val_dg]
    simpa using h2
  rw [map_inv, Pi.inv_apply, Units.val_inv_eq_inv_val] at h3
  change valuation k _ = 1
  have a1 : valuation k ((dg p i : kˣ) : k) ≤ 1 := (Valuation.mem_integer_iff _ _).1 h1
  have a2 : valuation k ((dg p i : kˣ) : k)⁻¹ ≤ 1 := (Valuation.mem_integer_iff _ _).1 h3
  rw [map_inv₀] at a2
  have hne : valuation k ((dg p i : kˣ) : k) ≠ 0 := by simp
  exact le_antisymm a1 ((inv_le_one₀ (zero_lt_iff.2 hne)).1 a2)

open GlobalTheory.SmGL.PrinProd in
private theorem sB_apply (χ : Fin n → kˣ →* ℂˣ) (p : parab k (points (Fin n))) (v : ℂ) :
    sB χ p v = ((deltaHalf k (fun _ : Fin n => Unit) (leviProj k (points (Fin n)) p) : ℂˣ) : ℂ) *
      (((torusChar χ (dg p) : ℂˣ) : ℂ) * v) := rfl

end Loc

open GlobalTheory.SmGL.PrinProd in
theorem psRes : PsRes := by
  intro k _ _ _ _ n ω ω' _ _ h
  let χ : Fin n → kˣ →* ℂˣ := fun i => ω i * absPow k ((↑n - 1) / 2)
  let χ' : Fin n → kˣ →* ℂˣ := fun i => ω' i * absPow k ((↑n - 1) / 2)
  let ρ : Fin n → kˣ →* ℂˣ := fun i => ω' i * (ω i)⁻¹
  have hχ : ∀ t, torusChar χ' t = torusChar ρ t * torusChar χ t := by
    intro t
    simp only [torusChar_apply, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [χ, χ', ρ, MonoidHom.mul_apply, MonoidHom.inv_apply]
    group
  refine equiv_of_char (parab k (points (Fin n))) (KO k (Fin n)) GlobalTheory.SplitFlip.isOpen_KO exists_pw
    (sB χ) (sB χ') ((torusChar ρ).comp dg) (fun p hp => ?_) (fun p v => ?_)
  · rw [MonoidHom.comp_apply, torusChar_apply]
    refine Finset.prod_eq_one fun i _ => ?_
    simp only [ρ, MonoidHom.mul_apply, MonoidHom.inv_apply]
    rw [← h i ⟨_, dg_mem_Uo p hp i⟩, mul_inv_cancel]
  · rw [sB_apply, sB_apply, smul_eq_mul, MonoidHom.comp_apply, hχ, Units.val_mul]
    ring

end UpperTheory.V.Z.J.D
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.PrimeNotMemSectionBasePlaceBis
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing Filter
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.Z.J.D

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.V.Z.J.D.AuxBlock5

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
  [IsAlgClosure L Ω] {n : ℕ}

private theorem cmp_of {w : Plc L} (h : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal) (x : UA L n) :
    cmp n w ((away l L n).rangeRestrict x) = cLoc w x := by
  unfold CaseU.cmp
  rw [dite_eq_left h]
  rfl

private theorem cmp_over_l {w : Plc L} (h : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal) (x : Ga l L n) : cmp n w x = 1 := by
  unfold CaseU.cmp
  rw [dite_eq_right (not_not.2 h)]
  rfl

private theorem ext_cmp {x y : Ga l L n} (h : ∀ w, cmp n w x = cmp n w y) : x = y := by
  obtain ⟨x, rfl⟩ := (away l L n).rangeRestrict_surjective x
  obtain ⟨y, rfl⟩ := (away l L n).rangeRestrict_surjective y
  refine Subtype.ext (funext fun w => ?_)
  have e := h w.1
  rwa [cmp_of w.2, cmp_of w.2] at e

private theorem comm_of {a b : Ga l L n} (h : ∀ w, cmp n w a = 1 ∨ cmp n w b = 1) : Commute a b := by
  refine ext_cmp fun w => ?_
  rw [map_mul, map_mul]
  rcases h w with h | h <;> rw [h] <;> simp

private theorem l_under {u : Plc L} :
    ((l : ℕ) : 𝓞 L) ∈ u.asIdeal ↔ ((l : ℕ) : 𝓞 (Lp L)) ∈ (u.under (𝓞 (Lp L))).asIdeal := by
  change _ ↔ algebraMap (𝓞 (Lp L)) (𝓞 L) _ ∈ u.asIdeal
  rw [map_natCast]

private theorem cLoc_over {w u : Plc L} (hw : IsSplitAt w) (x : UA L n) (h1 : cLoc w x = 1)
    (hu : u.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))) : cLoc u x = 1 := by
  have hw1 : ∀ v, v = w → cLoc v x = 1 := by
    rintro v rfl
    exact h1
  rcases (GlobalTheory.SplitPts.over_split hw).2.2 u hu with rfl | rfl
  · exact h1
  · have hce := GlobalTheory.SplitPts.comp_eq x (conjSrc (GlobalTheory.SplitPts.conjE L) w)
    rw [hw1 _ (GlobalTheory.SplitPts.conjSrc_conjSrc_cm w), Units.val_one, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.transpose_one, Matrix.one_mul] at hce
    exact Units.ext hce

private theorem cmp_over {w u : Plc L} (hw : IsSplitAt w) (x : Ga l L n) (h1 : cmp n w x = 1)
    (hu : u.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))) : cmp n u x = 1 := by
  by_cases hl : ((l : ℕ) : 𝓞 L) ∈ u.asIdeal
  · exact cmp_over_l hl x
  have hl' : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal := fun h => hl (l_under.2 (hu ▸ l_under.1 h))
  obtain ⟨x, rfl⟩ := (away l L n).rangeRestrict_surjective x
  rw [cmp_of hl'] at h1
  rw [cmp_of hl]
  exact cLoc_over hw x h1 hu

private theorem loc_one {w u : Plc L} {x : UA L n} (hx : x ∈ locU n w)
    (hu : u.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L))) : cLoc u x = 1 :=
  MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hx).2 u) hu)

variable (s : HidaSetting l L Ω)

private theorem under_w (v : Plc (Lp L)) : (s.w v).under (𝓞 (Lp L)) = v := by
  ext x
  exact (s.hw v (algebraMap (𝓞 (Lp L)) (𝓞 L) x)).symm.trans (s.hA v x)

private theorem split_of {v : Plc (Lp L)} (h : v ∈ s.St ∨ v = s.v0) : IsSplitAt (s.w v) :=
  UpperTheory.isSplitAt_of_decomposition_le_restriction_range L Ω _ _ (s.hA v) (s.split v (Or.inr h)) _ (under_w s v)

private theorem SectionSplitPlaces : ((l : ℕ) : 𝓞 (Lp L)) ∉ s.v0.asIdeal := by
  intro h
  have hp := s.p_prime
  have hcard : Nat.card (𝓞 (Lp L) ⧸ s.v0.asIdeal) = s.p := s.norm_v0_eq_one
  have hl0 : ((l : ℕ) : 𝓞 (Lp L) ⧸ s.v0.asIdeal) = 0 := by
    exact (Ideal.Quotient.eq_zero_iff_mem.2 h : _) |> fun e => by simpa using e
  have hp0 : ((s.p : ℕ) : 𝓞 (Lp L) ⧸ s.v0.asIdeal) = 0 := by
    have := card_nsmul_eq_zero' (G := 𝓞 (Lp L) ⧸ s.v0.asIdeal) (x := 1)
    rw [hcard] at this
    simpa using this
  have hco : Nat.Coprime l s.p := (Nat.coprime_primes (Fact.out : l.Prime) hp).2 (Ne.symm s.p_ne)
  have h1 : (1 : 𝓞 (Lp L) ⧸ s.v0.asIdeal) = 0 := by
    have := Nat.Coprime.isCoprime hco
    obtain ⟨a, b, e⟩ := this
    have e' := congrArg (Int.cast : ℤ → 𝓞 (Lp L) ⧸ s.v0.asIdeal) e
    push_cast at e'
    rw [hl0, hp0] at e'
    simpa using e'.symm
  have hsub : Subsingleton (𝓞 (Lp L) ⧸ s.v0.asIdeal) := subsingleton_of_zero_eq_one h1.symm
  rw [Nat.card_of_subsingleton (0 : 𝓞 (Lp L) ⧸ s.v0.asIdeal)] at hcard
  exact hp.one_lt.ne hcard

private theorem away_of {v : Plc (Lp L)} (h : v ∈ s.St ∨ v = s.v0) : ((l : ℕ) : 𝓞 L) ∉ (s.w v).asIdeal := by
  intro e
  have e' := l_under.1 e
  rw [under_w] at e'
  rcases h with h | rfl
  · exact s.St_l _ h e'
  · exact SectionSplitPlaces s e'

private theorem mem_GaS {x : Ga l L n} : x ∈ GaS n s ↔
    ∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ s.St ∧ w.under (𝓞 (Lp L)) ≠ s.v0 → cmp n w x = 1 := by
  simp only [GaS, Subgroup.mem_iInf, MonoidHom.mem_ker]

private theorem toGS_one {x : Ga l L n} (h : toGS n s x = 1) {w : Plc L}
    (hw : w.under (𝓞 (Lp L)) ∈ s.St ∨ w.under (𝓞 (Lp L)) = s.v0) : cmp n w x = 1 := by
  rcases hw with hw | hw
  · have e : cmp n (s.w (w.under (𝓞 (Lp L)))) x = 1 := congrFun (congrArg Prod.fst h) ⟨_, hw⟩
    exact cmp_over (split_of s (Or.inl hw)) x e (under_w s _).symm
  · have e : cmp n (s.w s.v0) x = 1 := congrArg Prod.snd h
    exact cmp_over (split_of s (Or.inr rfl)) x e (by rw [under_w, hw])

private theorem build (hn : 1 ≤ n) (T : Finset (Plc (Lp L))) (hT : ∀ v ∈ T, IsSplitAt (s.w v))
    (f : ∀ v, GLw n (s.w v)) :
    ∃ x : UA L n, (∀ v ∈ T, cLoc (s.w v) x = f v) ∧ ∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ T → cLoc w x = 1 := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨1, by simp, fun w _ => map_one _⟩
  | insert a T ha ih =>
    obtain ⟨x, hx, hx'⟩ := ih fun v hv => hT v (Finset.mem_insert_of_mem hv)
    obtain ⟨⟨j, hj, hj', -, -⟩, -⟩ := secU l L Ω s n hn (s.w a) (hT a (Finset.mem_insert_self _ _))
    have hloc : ∀ g (u : Plc L), u.under (𝓞 (Lp L)) ≠ a → cLoc u (j g) = 1 := fun g u hu =>
      loc_one (hj g) (by rwa [under_w])
    refine ⟨x * j (f a), fun v hv => ?_, fun w hw => ?_⟩
    · rcases Finset.mem_insert.1 hv with rfl | hv
      · rw [map_mul, hj', hx' _ (by rwa [under_w]), one_mul]
      · rw [map_mul, hx v hv, hloc _ _ (by rw [under_w]; exact fun e => ha (e ▸ hv)), mul_one]
    · rw [map_mul, hx' w fun h => hw (Finset.mem_insert_of_mem h),
        hloc _ w fun h => hw (h ▸ Finset.mem_insert_self _ _), one_mul]

private theorem bij (hn : 1 ≤ n) : Function.Bijective ((toGS n s).comp (GaS n s).subtype) := by
  classical
  refine ⟨(injective_iff_map_eq_one _).2 ?_, fun g => ?_⟩
  · rintro ⟨x, hx⟩ h1
    refine Subtype.ext (ext_cmp fun w => ?_)
    rw [show ((1 : GaS n s) : Ga l L n) = 1 from rfl, map_one]
    by_cases hw : w.under (𝓞 (Lp L)) ∈ s.St ∨ w.under (𝓞 (Lp L)) = s.v0
    · exact toGS_one s h1 hw
    · exact (mem_GaS s).1 hx w (not_or.1 hw)
  · obtain ⟨x, hx, hx'⟩ := build s hn s.St (fun v hv => split_of s (Or.inl hv))
      fun v => if h : v ∈ s.St then g.1 ⟨v, h⟩ else 1
    obtain ⟨⟨j, hj, hj', -, -⟩, -⟩ := secU l L Ω s n hn (s.w s.v0) (split_of s (Or.inr rfl))
    have hloc : ∀ (u : Plc L), u.under (𝓞 (Lp L)) ≠ s.v0 → cLoc u (j g.2) = 1 := fun u hu =>
      loc_one (hj _) (by rwa [under_w])
    have hS : (away l L n).rangeRestrict (x * j g.2) ∈ GaS n s := by
      refine (mem_GaS s).2 fun w hw => ?_
      by_cases hl : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal
      · exact cmp_over_l hl _
      · rw [cmp_of hl, map_mul, hx' w hw.1, hloc w hw.2, one_mul]
    refine ⟨⟨_, hS⟩, Prod.ext (funext fun u => ?_) ?_⟩
    · change cmp n (s.w u) ((away l L n).rangeRestrict (x * j g.2)) = g.1 u
      rw [cmp_of (away_of s (Or.inl u.2)), map_mul, hx _ u.2, dite_eq_left u.2,
        hloc _ (by rw [under_w]; exact fun e => s.v0_St (e ▸ u.2)), mul_one]
    · change cmp n (s.w s.v0) ((away l L n).rangeRestrict (x * j g.2)) = g.2
      rw [cmp_of (away_of s (Or.inr rfl)), map_mul, hx' _ (by rw [under_w]; exact s.v0_St), hj', one_mul]

private theorem secS_spec (h : Function.Bijective ((toGS n s).comp (GaS n s).subtype)) (g : GS n s) :
    toGS n s (secS n s g) = g ∧ secS n s g ∈ GaS n s := by
  unfold secS
  rw [dite_eq_left h]
  exact ⟨(MulEquiv.ofBijective _ h).apply_symm_apply g, ((MulEquiv.ofBijective _ h).symm g).2⟩

private theorem mem_KS {k : Ga l L n} : k ∈ KS n s ↔ toGS n s k = 1 ∧
    ∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ s.S → cmp n w k ∈ KO (w.adicCompletion L) (Fin n) := by
  simp only [KS, Subgroup.mem_inf, Subgroup.mem_iInf, MonoidHom.mem_ker, Subgroup.mem_comap]

private theorem notS {w : Plc L} (h : w.under (𝓞 (Lp L)) ∉ s.S) :
    w.under (𝓞 (Lp L)) ∉ s.St ∧ w.under (𝓞 (Lp L)) ≠ s.v0 :=
  ⟨fun e => h (Or.inr (Or.inl e)), fun e => h (Or.inr (Or.inr e))⟩

private theorem mem_Ub {x : Ga l L n} : x ∈ Ub n s ↔
    (∀ u : s.St, cmp n (s.w u) x ∈ KO ((s.w u).adicCompletion L) (Fin n)) ∧ cmp n (s.w s.v0) x ∈ Kc _ n 1 := by
  simp only [Ub, Subgroup.mem_inf, Subgroup.mem_iInf, Subgroup.mem_comap]

variable {s}

private theorem mem_UQ {V : s.Lev} (Q : QData V) (hV : V.S' = s.S) {x : Ub n s} : x ∈ UQ n Q ↔
    ∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ s.S → cmp n w (x : Ga l L n) ∈ KO (w.adicCompletion L) (Fin n) := by
  have hq : ∀ q : Q.Q, False := fun q => Q.notS q (by
    have h : (Q.wq q).under (𝓞 (Lp L)) ∈ V.S' := by
      rw [Q.range]
      exact Or.inr ⟨q, rfl⟩
    rwa [hV] at h)
  simp only [UQ, Subgroup.mem_inf, Subgroup.mem_iInf, MonoidHom.mem_ker, Subgroup.mem_comap, hV]
  exact ⟨fun h => h.1, fun h => ⟨h, fun q => (hq q).elim⟩⟩

end UpperTheory.V.Z.J.D.AuxBlock5

open UpperTheory.V.Z.J.D.AuxBlock5 in
theorem UpperTheory.V.Z.J.D.secSp :
    SecS := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V hV
  have hb := bij s hn
  refine ⟨hb, fun g k hk => comm_of fun w => ?_, fun Q g => ⟨?_, ?_⟩⟩
  · by_cases hw : w.under (𝓞 (Lp L)) ∈ s.St ∨ w.under (𝓞 (Lp L)) = s.v0
    · exact Or.inr (toGS_one s ((mem_KS s).1 hk).1 hw)
    · exact Or.inl ((mem_GaS s).1 (secS_spec s hb g).2 w (not_or.1 hw))
  · rintro ⟨x, hx, rfl⟩
    have hU := (mem_Ub s).1 x.2
    have hs := secS_spec s hb (toGS n s (x : Ga l L n))
    refine ⟨(secS n s (toGS n s (x : Ga l L n)))⁻¹ * x, (mem_KS s).2 ⟨?_, fun w hw => ?_⟩,
      toGS n s (x : Ga l L n), Subgroup.mem_prod.2 ⟨fun u _ => hU.1 u, hU.2⟩, (mul_inv_cancel_left _ _).symm⟩
    · rw [map_mul, map_inv, hs.1, inv_mul_cancel]
    · rw [map_mul, map_inv, (mem_GaS s).1 hs.2 w (notS s hw), inv_one, one_mul]
      exact (mem_UQ Q hV).1 hx w hw
  · rintro ⟨k, hk, p, hp, rfl⟩
    obtain ⟨hk1, hk2⟩ := (mem_KS s).1 hk
    have hs := secS_spec s hb p
    have hU : secS n s p * k ∈ Ub n s := by
      refine (mem_Ub s).2 ⟨fun u => ?_, ?_⟩
      · have e : cmp n (s.w u) (secS n s p) = p.1 u := congrFun (congrArg Prod.fst hs.1) u
        rw [map_mul, e, toGS_one s hk1 (Or.inl (by rw [UpperTheory.V.Z.J.D.AuxBlock5.under_w]; exact u.2)), mul_one]
        exact (Subgroup.mem_prod.1 hp).1 u (Set.mem_univ _)
      · have e : cmp n (s.w s.v0) (secS n s p) = p.2 := congrArg Prod.snd hs.1
        rw [map_mul, e, toGS_one s hk1 (Or.inr (by rw [UpperTheory.V.Z.J.D.AuxBlock5.under_w])), mul_one]
        exact (Subgroup.mem_prod.1 hp).2
    refine ⟨⟨_, hU⟩, (mem_UQ Q hV).2 fun w hw => ?_, rfl⟩
    change cmp n w (secS n s p * k) ∈ _
    rw [map_mul, (mem_GaS s).1 hs.2 w (notS s hw), one_mul]
    exact hk2 w hw
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.UnitEv
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Z.J.D
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option synthInstance.maxHeartbeats 200000

private theorem norm_le_of_isIntegral {l : ℕ} [Fact l.Prime] {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
    (x : B →+* PadicAlgCl l) (h : ∀ a, ‖x (algebraMap A B a)‖ ≤ 1) {t : B} (ht : IsIntegral A t) : ‖x t‖ ≤ 1 := by
  obtain ⟨p, hm, hp⟩ := ht
  let S := integralClosure ℤ_[l] (PadicAlgCl l)
  let g : A →+* S := (x.comp (algebraMap A B)).codRestrict S.toSubring (fun a => by
    show IsIntegral ℤ_[l] (x (algebraMap A B a))
    exact (UpperTheory.V.Hi.Up.intIff _).2 (h a))
  have hint : IsIntegral S (x t) := by
    refine ⟨p.map g, hm.map g, ?_⟩
    rw [Polynomial.eval₂_map]
    have hc : (algebraMap S (PadicAlgCl l)).comp g = x.comp (algebraMap A B) := by
      ext a
      rfl
    rw [hc, ← Polynomial.hom_eval₂, hp, map_zero]
  exact (UpperTheory.V.Hi.Up.intIff _).1 (isIntegral_trans (R := ℤ_[l]) _ hint)

private theorem isIntegral_of_subalgebra {A Y : Type} [CommRing A] [AddCommGroup Y] [Module A Y] [Module.Finite A Y]
    (T : Subalgebra A (Module.End A Y)) (t : T) : IsIntegral A t := by
  have h : IsIntegral A (t : Module.End A Y) := by
    obtain ⟨p, hp, he⟩ := LinearMap.exists_monic_and_aeval_eq_zero A (t : Module.End A Y)
    exact ⟨p, hp, by rwa [← Polynomial.aeval_def]⟩
  exact (isIntegral_algHom_iff T.val Subtype.val_injective).1 h

private theorem norm_unit {l : ℕ} [Fact l.Prime] {B : Type} [CommRing B] (x : B →+* PadicAlgCl l) (u : Bˣ)
    (h : ∀ t, ‖x t‖ ≤ 1) : ‖x u‖ = 1 := by
  have e : ‖x u‖ * ‖x (u⁻¹ : Bˣ)‖ = 1 := by
    rw [← norm_mul, ← map_mul, Units.mul_inv, map_one, norm_one]
  refine le_antisymm (h _) ?_
  calc (1 : ℝ) = ‖x u‖ * ‖x (u⁻¹ : Bˣ)‖ := e.symm
    _ ≤ ‖x u‖ * 1 := mul_le_mul_of_nonneg_left (h _) (norm_nonneg _)
    _ = ‖x u‖ := mul_one _

theorem UpperTheory.V.Z.J.D.unitEv :
    UnitEv := by
  intro L Ω _ _ _ _ _ l _ n c H hAx A _ _ _ θ _ ι K a _ _ I D ψ hU z v j
  obtain ⟨s, hs⟩ := GlobalTheory.LocLanglands.IsLocalArtin.surj (hAx.art_spec v)
    (UpperTheory.V.Hi.unif (IsDedekindDomain.HeightOneSpectrum.adicCompletion L (H.Sl v)))
  let g : Dec (H.pl v) := ⟨s, GlobalTheory.WeilDeligne.Weil_le_Dec (H.ovr v) s.2⟩
  rw [← hU.ψ_unif v j s g rfl hs]
  apply norm_unit z.toRingHom
  intro t
  refine norm_le_of_isIntegral (A := A) z.toRingHom ?_ (isIntegral_of_subalgebra _ t)
  intro a0
  let y : A →ₐ[c.O] PadicAlgCl l := z.comp (IsScalarTower.toAlgHom c.O A (H.TK θ a K))
  show ‖y a0‖ ≤ 1
  obtain ⟨b, hb⟩ := UpperTheory.V.Alg.IsCO.res_surj (O := c.O) a0
  have hm := UpperTheory.V.Hi.Up.normLt (l := l) (O := c.O) y _ hb
  have hi1 : IsIntegral ℤ_[l] (y (a0 - algebraMap c.O A b)) :=
    (UpperTheory.V.Hi.Up.intIff _).2 hm.le
  have hbi : IsIntegral ℤ_[l] b := by
    haveI := c.fin
    exact IsIntegral.of_finite ℤ_[l] b
  have hi2 : IsIntegral ℤ_[l] (y (algebraMap c.O A b)) := by
    rw [AlgHom.commutes]
    exact (isIntegral_algHom_iff c.O.val Subtype.val_injective).2 hbi
  have := hi1.add hi2
  rw [← map_add (f := _), sub_add_cancel] at this
  exact (UpperTheory.V.Hi.Up.intIff _).1 this
end
