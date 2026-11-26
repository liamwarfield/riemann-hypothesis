module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.ToralDeRham.FrobeniusCharpolyOfUnlinkedUnramifiedSupport
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RestrictsWdPst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightOfSizeBound
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineInputs.InputsOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.LpPowOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.NmEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.WindowMul
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.MatchBCX

@[expose] public section

set_option synthInstance.maxHeartbeats 200000
attribute [local instance 10000] DivisionSemiring.to_moduleIsTorsionFree

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.RkSupp
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClTwistEqSelfOfEqOne
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

namespace GlobalTheory

open GlobalTheory.SmGL GlobalTheory.LocGL in
private theorem clTwist_eq_self_of_eq_one {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (c : IrrCl G) (χ : G →* ℂˣ) (hχ : IsSmoothChar χ) (h1 : χ = 1) : clTwist c χ hχ = c := by
  subst h1; exact clTwist_one c hχ

theorem rankOne_algNorm_locComp (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (π : CuspSub E 1)
    (ψ : HChar E) (hπ : CG.mk π = CG.ofChar ψ) (w : HeightOneSpectrum (𝓞 E))
    (σ : SmIrr (GL (Fin 1) (w.adicCompletion E))) (hσ : π.IsLocComp w σ) :
    algNorm σ = IrrGL.ofChar (ψ.loc w) (ParLaws.isSmoothChar_loc ψ w) := by
  have h1 : (CG.mk π).IsLoc w (Quotient.mk _ σ) := hσ
  rw [hπ] at h1
  have h2 := CG.IsLoc.unique E 1 _ w _ _ h1 (CG.isLoc_ofChar ψ w)
  obtain ⟨e⟩ := Quotient.exact h2
  unfold algNorm IrrGL.nu IrrGL.tw IrrGL.of IrrGL.ofChar
  congr 1
  refine (clTwist_eq_self_of_eq_one _ _ _ ?_).trans ?_
  · ext g
    simp [GlobalTheory.SmGL.detChar, GlobalTheory.SmGL.absPow]
  apply Quotient.sound
  exact ⟨e.trans (Representation.Equiv.refl _)⟩

end GlobalTheory
end

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open GroundTheory.Global.SemiLocal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
open UpperTheory.Gal.GamX

private theorem chs_single {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ξ : kˣ →* ℂˣ) (hξ : IsSmoothChar ξ) : chs ({IrrGL.ofChar ξ hξ} : Multiset (IrrGL (k := k))) = {ξ} := by
  have hex : ∃ ζ : kˣ →* ℂˣ, ∃ hζ, IrrGL.ofChar ξ hξ = IrrGL.ofChar ζ hζ := ⟨ξ, hξ, rfl⟩
  have hc : hex.choose = ξ := by
    obtain ⟨hζ, e⟩ := hex.choose_spec
    exact (IrrGL.ofChar_inj.1 e).symm
  unfold chs
  rw [← Multiset.cons_zero (IrrGL.ofChar ξ hξ), Multiset.filterMap_cons_some _ _ _ (b := ξ) (by rw [dite_eq_left hex, hc])]
  simp

theorem UpperTheory.Gal.GamX.rkSupp :
    UpperTheory.Gal.GamX.RkSupp := by
  unfold RkSupp
  intro K _ _ _ π ψ hπ v s hs
  obtain ⟨σ, hσ, h⟩ := id hs
  have h1 := GlobalTheory.rankOne_algNorm_locComp K π ψ hπ v σ hσ
  have h2 : IrrGL.of σ.ρ σ.smooth σ.irred = IrrGL.ofChar (ψ.loc v) (ParLaws.isSmoothChar_loc ψ v) := by
    rw [← h1]
    simp [GlobalTheory.GalOfCusp.algNorm]
  have hc : (IrrGL.of σ.ρ σ.smooth σ.irred).IsCusp := h2 ▸ IrrGL.isCusp_ofChar _ _
  have h3 : SuppAt π v {IrrGL.of σ.ρ σ.smooth σ.irred} :=
    ⟨σ, hσ, (hasSupport_self hc).of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred).symm⟩
  have h4 := (UpperTheory.V.Z.Gam.suppFacts K 1 le_rfl π v).2.1 _ _ hs h3
  rw [h4, h2, chs_single]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.UpThruOf
open NumberField IsDedekindDomain Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open GroundTheory.Global.SemiLocal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
open UpperTheory.Gal.GamX

theorem UpperTheory.Gal.GamX.upThruOf :
    UpperTheory.Gal.GamX.UpThruOf := by
  unfold UpThruOf UpThru
  intro hC K L _ _ _ _ _ v w s
  rw [Multiset.filter_eq_self]
  intro ζ hζ
  obtain ⟨ξ, hξ, rfl⟩ := Multiset.mem_map.1 hζ
  have hs : IsSmoothChar ξ := (hC _ s).2.1 ξ hξ
  refine ⟨ξ⁻¹, IsSmoothChar.inv hs, fun x _ => by simp⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.GamOneOf
noncomputable section

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open GroundTheory.Global.SemiLocal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace UpperTheory.Gal.GamX

theorem gamOneOf : GamOneOf := by
  unfold GamOneOf GamOne
  intro hC hV hS K L _ _ _ _ _ _ _ _ hp n hn π P hW v w hw s s' hs hs'
  have hsub : Subsingleton (PlacesOver L v) := ⟨fun a b => (hw a).trans (hw b).symm⟩
  have key : ∀ (u : PlacesOver L v) (h : w = u), SuppAt P u.1 (h ▸ s') := by
    rintro u rfl
    exact hs'
  have hval : ∀ θ : (v.adicCompletion K)ˣ →* ℂˣ, IsSmoothChar θ →
      vals (chs s') (θ.comp (nm w)) = vals (up w s) (θ.comp (nm w)) := by
    intro θ hθ
    have h := hS K L hp n hn π P hW v s (fun u => (hw u).symm ▸ s') hs
      (fun u => key u (hw u).symm) θ hθ
    rw [Fintype.sum_subsingleton _ w, Fintype.sum_subsingleton _ w] at h
    exact h
  refine Multiset.ext.2 fun ζ => ?_
  by_cases hT : Thru w ζ
  · obtain ⟨χ, hχ, hu⟩ := id hT
    have hf := hV (w.1.adicCompletion L) (chs s') (up w s) (χ.comp (nm w)) (hval χ hχ)
    have hc := congrArg (Multiset.count ζ) hf
    rw [Multiset.count_filter_of_pos (p := fun ξ => IsUnram (ξ * χ.comp (nm w))) hu,
      Multiset.count_filter_of_pos (p := fun ξ => IsUnram (ξ * χ.comp (nm w))) hu] at hc
    rw [Multiset.count_filter_of_pos hT]
    exact hc
  · rw [Multiset.count_filter_of_neg hT, eq_comm, Multiset.count_eq_zero]
    intro hm
    obtain ⟨ξ, hξ, rfl⟩ := Multiset.mem_map.1 hm
    exact hT ⟨ξ⁻¹, ((hC _ s).2.1 ξ hξ).inv, fun x _ => by simp⟩

end UpperTheory.Gal.GamX
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.LpEvalZero
open NumberField IsDedekindDomain Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open GroundTheory.Global.SemiLocal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
open UpperTheory.Gal.GamX

private theorem lp_zero' : UpperTheory.Gal.GamX.lp (0 : Multiset ℂˣ) = 1 := by
  simp [UpperTheory.Gal.GamX.lp]

private theorem lp_cons' (a : ℂˣ) (A : Multiset ℂˣ) :
    UpperTheory.Gal.GamX.lp (a ::ₘ A) = (1 - Polynomial.C (a : ℂ) * Polynomial.X) * UpperTheory.Gal.GamX.lp A := by
  simp [UpperTheory.Gal.GamX.lp]

private theorem lp_eval_zero (A : Multiset ℂˣ) : (UpperTheory.Gal.GamX.lp A).eval 0 = 1 := by
  induction A using Multiset.induction_on with
  | empty => simp [lp_zero']
  | cons a A ih => rw [lp_cons', Polynomial.eval_mul, ih]; simp

private theorem lp_ne_zero (A : Multiset ℂˣ) : UpperTheory.Gal.GamX.lp A ≠ 0 := by
  intro h
  have h1 := lp_eval_zero A
  rw [h] at h1
  simp at h1

private theorem lin_eq (a : ℂˣ) :
    (1 - Polynomial.C (a : ℂ) * Polynomial.X : ℂ[X]) =
      Polynomial.C (-(a : ℂ)) * (Polynomial.X - Polynomial.C ((a⁻¹ : ℂˣ) : ℂ)) := by
  have ha : (a : ℂ) ≠ 0 := a.ne_zero
  rw [Units.val_inv_eq_inv_val, mul_sub, ← Polynomial.C_mul, neg_mul, mul_inv_cancel₀ ha,
    Polynomial.C_neg, Polynomial.C_neg, Polynomial.C_1]
  ring

private theorem lin_roots (a : ℂˣ) :
    (1 - Polynomial.C (a : ℂ) * Polynomial.X : ℂ[X]).roots = {((a⁻¹ : ℂˣ) : ℂ)} := by
  rw [lin_eq, Polynomial.roots_C_mul _ (by simp), Polynomial.roots_X_sub_C]

private theorem lp_roots (A : Multiset ℂˣ) :
    (UpperTheory.Gal.GamX.lp A).roots = A.map (fun a => ((a⁻¹ : ℂˣ) : ℂ)) := by
  induction A using Multiset.induction_on with
  | empty => simp [lp_zero']
  | cons a A ih =>
    rw [lp_cons', Polynomial.roots_mul (by rw [← lp_cons']; exact lp_ne_zero _), lin_roots, ih,
      Multiset.map_cons, Multiset.singleton_add]

theorem UpperTheory.Gal.GamX.lpInj :
    UpperTheory.Gal.GamX.LpInj := by
  intro A B h
  have h1 := congrArg Polynomial.roots h
  rw [lp_roots, lp_roots] at h1
  exact Multiset.map_injective (fun a b hab => inv_injective (Units.ext hab)) h1
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.ValsExtOfAlt
open NumberField IsDedekindDomain Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open GroundTheory.Global.SemiLocal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
open UpperTheory.Gal.GamX

private theorem map_eq_of_injOn {α β : Type*} (S : Set α) (g : α → β) (hg : Set.InjOn g S)
    (A B : Multiset α) (hA : ∀ x ∈ A, x ∈ S) (hB : ∀ x ∈ B, x ∈ S)
    (h : A.map g = B.map g) : A = B := by
  have key : ∀ C : Multiset α, (∀ x ∈ C, x ∈ S) → ∀ ξ ∈ S, C.count ξ = (C.map g).count (g ξ) := by
    intro C hC ξ hξ
    rw [Multiset.count_map, Multiset.count_eq_card_filter_eq]
    congr 1
    apply Multiset.filter_congr
    intro x hx
    exact ⟨fun e => congrArg g e, fun e => hg hξ (hC x hx) e⟩
  ext ξ
  by_cases hξ : ξ ∈ S
  · rw [key A hA ξ hξ, key B hB ξ hξ, h]
  · rw [Multiset.count_eq_zero_of_notMem (fun m => hξ (hA _ m)),
      Multiset.count_eq_zero_of_notMem (fun m => hξ (hB _ m))]

theorem UpperTheory.Gal.GamX.valsExtOf :
    UpperTheory.Gal.GamX.ValsExtOf := by
  unfold ValsExtOf ValsExt
  intro hP k _ _ _ _ c c' θ h
  have hinj : Set.InjOn (fun ξ : kˣ →* ℂˣ => (ξ * θ) (unif k)) {ξ | IsUnram (ξ * θ)} := by
    intro ξ hξ ξ' hξ' e
    have hu : IsUnram ((ξ * θ) * (ξ' * θ)⁻¹) := isUnram_mul hξ (isUnram_inv hξ')
    exact mul_right_cancel ((hP k).2.1 _ _ hu e)
  exact map_eq_of_injOn _ _ hinj _ _ (fun x hx => (Multiset.mem_filter.1 hx).2)
    (fun x hx => (Multiset.mem_filter.1 hx).2) h
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.TwValsOf
open NumberField IsDedekindDomain Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open GroundTheory.Global.SemiLocal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
open UpperTheory.Gal.GamX

set_option maxHeartbeats 800000 in
theorem UpperTheory.Gal.GamX.twValsOf :
    UpperTheory.Gal.GamX.TwValsOf := by
  intro hNV K L _ _ _ _ _ v d f e hf hne he hA hB c hc θ hθ
  unfold UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.NormVal at hNV
  have hv1 : ∀ {k : Type} [Field k] [ValuativeRel k] (a t : kˣ →* ℂˣ),
      vals {a} t = if IsUnram (a * t) then {(a * t) (unif k)} else 0 := by
    intro k _ _ a t
    unfold vals
    rw [Multiset.filter_singleton]
    split_ifs <;> simp
  have hadd : ∀ {k : Type} [Field k] [ValuativeRel k] (c1 c2 : Multiset (kˣ →* ℂˣ)) (t : kˣ →* ℂˣ),
      vals (c1 + c2) t = vals c1 t + vals c2 t := by
    intro k _ _ c1 c2 t
    simp only [vals, Multiset.filter_add, Multiset.map_add (f := _)]
  induction c using Multiset.induction_on with
  | empty => simp [vals]
  | cons a c ih =>
    have hca : IsSmoothChar a := hc a (Multiset.mem_cons_self a c)
    have ih' := ih (fun ξ h => hc ξ (Multiset.mem_cons_of_mem h))
    have hone : Multiset.map (fun x => x ^ f) (∑ j ∈ Finset.range d, vals {a} (θ * e j)) =
        f • ∑ w : PlacesOver L v, vals (Multiset.map (fun ξ => ξ.comp (nm w)) {a}) (θ.comp (nm w)) := by
      simp only [Multiset.map_singleton, hv1, ← mul_assoc, ← MonoidHom.mul_comp]
      set μ := a * θ with hμ
      have hμs : IsSmoothChar μ := by
        unfold IsSmoothChar at hca hθ ⊢
        have hle : a.ker ⊓ θ.ker ≤ μ.ker := by
          intro x hx
          rw [Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker] at hx
          rw [MonoidHom.mem_ker, hμ, MonoidHom.mul_apply, hx.1, hx.2, mul_one]
        exact Subgroup.isOpen_mono hle (by rw [Subgroup.coe_inf]; exact hca.inter hθ)
      have hcomp : ∀ j (w : PlacesOver L v), (μ * e j).comp (nm w) = μ.comp (nm w) := by
        intro j w
        rw [MonoidHom.mul_comp, he j w, mul_one]
      by_cases hex : ∃ w : PlacesOver L v, IsUnram (μ.comp (nm w))
      · obtain ⟨w1, hw1⟩ := hex
        have hall : ∀ w : PlacesOver L v, IsUnram (μ.comp (nm w)) := fun w => hA w1 w μ hw1
        have hcard := hB w1 μ hμs hw1
        have hsumf : ∑ w' : PlacesOver L v, fdeg w' = Fintype.card (PlacesOver L v) * f := by
          simp only [hf, Finset.sum_const, Finset.card_univ, smul_eq_mul]
        have hfpos : 0 < f := by
          have := (hNV K L v w1 μ).2.2.1
          rwa [hf w1] at this
        have hval : ∀ j, IsUnram (μ * e j) → ∀ w : PlacesOver L v,
            μ ((nm w) (unif (HeightOneSpectrum.adicCompletion L (w : HeightOneSpectrum (𝓞 L))))) =
              (μ * e j) (unif (HeightOneSpectrum.adicCompletion K v)) ^ f := by
          intro j hj w
          have h1 := ((hNV K L v w (μ * e j)).1 hj).2
          have h2 : (e j) ((nm w) (unif (HeightOneSpectrum.adicCompletion L
              (w : HeightOneSpectrum (𝓞 L))))) = 1 := by
            have := congrArg (fun φ => φ (unif (HeightOneSpectrum.adicCompletion L
              (w : HeightOneSpectrum (𝓞 L))))) (he j w)
            simpa using this
          rw [MonoidHom.mul_apply, h2, mul_one, hf w] at h1
          exact h1
        have hpos : 0 < (Finset.filter (fun j => IsUnram (μ * e j)) (Finset.range d)).card := by
          rw [hcard, hsumf]
          exact Nat.mul_pos (Fintype.card_pos_iff.mpr hne) hfpos
        obtain ⟨j0, hj0⟩ := Finset.card_pos.mp hpos
        rw [Finset.mem_filter] at hj0
        refine Eq.trans ((Multiset.eq_replicate (n := Fintype.card (PlacesOver L v) * f)
          (a := (μ * e j0) (unif (HeightOneSpectrum.adicCompletion K v)) ^ f)).mpr ⟨?_, ?_⟩)
          ((Multiset.eq_replicate).mpr ⟨?_, ?_⟩).symm
        · rw [Multiset.card_map, Multiset.card_sum, ← hsumf, ← hcard, Finset.card_filter]
          refine Finset.sum_congr rfl fun j _ => ?_
          split_ifs <;> simp
        · intro b hb
          rw [Multiset.mem_map] at hb
          obtain ⟨x, hx, rfl⟩ := hb
          rw [Multiset.mem_sum] at hx
          obtain ⟨j, -, hxj⟩ := hx
          split_ifs at hxj with hj
          · rw [Multiset.mem_singleton] at hxj
            subst hxj
            rw [← hval j hj w1, hval j0 hj0.2 w1]
          · simp at hxj
        · simp only [hall, ↓reduceIte]
          rw [Multiset.card_nsmul, Multiset.card_sum]
          simp [mul_comm]
        · intro b hb
          simp only [hall, ↓reduceIte] at hb
          have hb' := Multiset.mem_of_mem_nsmul hb
          rw [Multiset.mem_sum] at hb'
          obtain ⟨w, -, hbw⟩ := hb'
          rw [Multiset.mem_singleton] at hbw
          rw [hbw, MonoidHom.comp_apply]
          exact hval j0 hj0.2 w
      · push_neg at hex
        have hno : ∀ j, ¬ IsUnram (μ * e j) := by
          intro j hj
          obtain ⟨w0⟩ := hne
          have := ((hNV K L v w0 (μ * e j)).1 hj).1
          rw [hcomp] at this
          exact hex w0 this
        simp [hno, hex]
    rw [← Multiset.singleton_add]
    simp only [hadd, Multiset.map_add (f := _), Finset.sum_add_distrib, smul_add]
    rw [hone, ih']
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.ChsFacts
noncomputable section

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open GroundTheory.Global.SemiLocal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace UpperTheory.Gal.GamX

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem opt_ofChar (ξ : kˣ →* ℂˣ) (hξ) :
    (if h : ∃ ξ' : kˣ →* ℂˣ, ∃ hξ', (IrrGL.ofChar ξ hξ : IrrGL (k := k)) = IrrGL.ofChar ξ' hξ' then some h.choose else none)
      = some ξ := by
  have h : ∃ ξ' : kˣ →* ℂˣ, ∃ hξ', (IrrGL.ofChar ξ hξ : IrrGL (k := k)) = IrrGL.ofChar ξ' hξ' := ⟨ξ, hξ, rfl⟩
  rw [dite_eq_left h]
  obtain ⟨_, h2⟩ := h.choose_spec
  exact congrArg some (IrrGL.ofChar_inj.1 h2).symm

private theorem chs_cons_ofChar (ξ : kˣ →* ℂˣ) (hξ) (s : Multiset (IrrGL (k := k))) :
    chs (IrrGL.ofChar ξ hξ ::ₘ s) = ξ ::ₘ chs s :=
  Multiset.filterMap_cons_some _ _ _ (opt_ofChar ξ hξ)

private theorem chs_cons_none {y : IrrGL (k := k)} (hy : ¬ ∃ ξ : kˣ →* ℂˣ, ∃ hξ, y = IrrGL.ofChar ξ hξ)
    (s : Multiset (IrrGL (k := k))) : chs (y ::ₘ s) = chs s :=
  Multiset.filterMap_cons_none _ _ (dif_neg hy)

private theorem mem_chs_iff (s : Multiset (IrrGL (k := k))) (ξ : kˣ →* ℂˣ) :
    ξ ∈ chs s ↔ ∃ hξ, IrrGL.ofChar ξ hξ ∈ s := by
  unfold chs
  rw [Multiset.mem_filterMap]
  constructor
  · rintro ⟨y, hy, e⟩
    by_cases h : ∃ ξ : kˣ →* ℂˣ, ∃ hξ, y = IrrGL.ofChar ξ hξ
    · obtain ⟨ξ', hξ', rfl⟩ := h
      rw [opt_ofChar] at e
      obtain rfl := Option.some.inj e
      exact ⟨hξ', hy⟩
    · rw [dif_neg h] at e
      cases e
  · rintro ⟨hξ, h⟩
    exact ⟨_, h, opt_ofChar ξ hξ⟩

private theorem pol_cons (y : IrrGL (k := k)) (s : Multiset (IrrGL (k := k))) (θ : kˣ →* ℂˣ) :
    pol (y ::ₘ s) θ = (if h : ∃ ξ : kˣ →* ℂˣ, (∃ hξ, y = IrrGL.ofChar ξ hξ) ∧ IsUnram (ξ * θ) then
      1 - C (((h.choose * θ) (unif k) : ℂˣ) : ℂ) * X else 1) * pol s θ := by
  unfold pol
  rw [Multiset.map_cons, Multiset.prod_cons]

private theorem lp_cons (a : ℂˣ) (A : Multiset ℂˣ) : lp (a ::ₘ A) = (1 - C ((a : ℂˣ) : ℂ) * X) * lp A := by
  unfold lp
  rw [Multiset.map_cons, Multiset.prod_cons]

private theorem pol_eq_lp (s : Multiset (IrrGL (k := k))) (θ : kˣ →* ℂˣ) : pol s θ = lp (vals (chs s) θ) := by
  induction s using Multiset.induction with
  | empty => simp [pol, lp, vals, chs_zero]
  | cons y s ih =>
    rw [pol_cons, ih]
    by_cases hy : ∃ ξ : kˣ →* ℂˣ, ∃ hξ, y = IrrGL.ofChar ξ hξ
    · obtain ⟨ξ, hξ, rfl⟩ := hy
      rw [chs_cons_ofChar]
      by_cases hu : IsUnram (ξ * θ)
      · have h : ∃ ξ' : kˣ →* ℂˣ, (∃ hξ', (IrrGL.ofChar ξ hξ : IrrGL (k := k)) = IrrGL.ofChar ξ' hξ') ∧ IsUnram (ξ' * θ) :=
          ⟨ξ, ⟨hξ, rfl⟩, hu⟩
        rw [dite_eq_left h]
        obtain ⟨⟨_, h2⟩, _⟩ := h.choose_spec
        have e : h.choose = ξ := (IrrGL.ofChar_inj.1 h2).symm
        rw [e]
        unfold vals
        rw [Multiset.filter_cons_of_pos (p := fun ξ => IsUnram (ξ * θ)) _ hu, Multiset.map_cons, lp_cons]
      · have h : ¬ ∃ ξ' : kˣ →* ℂˣ, (∃ hξ', (IrrGL.ofChar ξ hξ : IrrGL (k := k)) = IrrGL.ofChar ξ' hξ') ∧ IsUnram (ξ' * θ) := by
          rintro ⟨ξ', ⟨_, h2⟩, h3⟩
          obtain rfl := IrrGL.ofChar_inj.1 h2
          exact hu h3
        rw [dif_neg h, one_mul]
        unfold vals
        rw [Multiset.filter_cons_of_neg (p := fun ξ => IsUnram (ξ * θ)) _ hu]
    · have h : ¬ ∃ ξ : kˣ →* ℂˣ, (∃ hξ, y = IrrGL.ofChar ξ hξ) ∧ IsUnram (ξ * θ) := by
        rintro ⟨ξ, h2, _⟩
        exact hy ⟨ξ, h2⟩
      rw [dif_neg h, one_mul, chs_cons_none hy]

end Loc

theorem chsFacts : ChsFacts := by
  unfold ChsFacts
  intro k _ _ _ _ s
  refine ⟨fun ξ => ?_, fun ξ hξ => ?_, fun θ => pol_eq_lp s θ⟩
  · rw [mem_chs_iff]
    rfl
  · obtain ⟨h, _⟩ := (mem_chs_iff s ξ).1 hξ
    exact h

end UpperTheory.Gal.GamX
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.GamSumOf
noncomputable section

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open GroundTheory.Global.SemiLocal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace UpperTheory.Gal.GamX

private theorem lp_zero : lp 0 = 1 := by simp [lp]

private theorem lp_add (A B : Multiset ℂˣ) : lp (A + B) = lp A * lp B := by simp [lp]

private theorem lp_sum {ι : Type} (t : Finset ι) (A : ι → Multiset ℂˣ) :
    lp (∑ i ∈ t, A i) = ∏ i ∈ t, lp (A i) := by
  induction t using Finset.induction_on with
  | empty => simp [lp_zero]
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, lp_add, ih]

private theorem loc_pow_apply {E : Type} [Field E] [NumberField E] (χ : HChar E) (a : ℕ) (v x) :
    (χ ^ a).loc v x = χ.loc v x ^ a := by
  change (χ ^ a).1 _ = _
  rw [SubgroupClass.coe_pow, MonoidHom.pow_apply]
  rfl

theorem gamSumOf : GamSumOf := by
  unfold GamSumOf GamSum
  intro hM hN hV hP hC hF hT K L _ _ _ _ _ _ _ _ hp n hn π P hW v s s' hs hs' θ hθ
  obtain ⟨η, h1, h2⟩ := hN K L hp
  obtain ⟨⟨w₀⟩, hf⟩ := hF K L v
  have hfw : ∀ w : PlacesOver L v, fdeg w = fdeg w₀ := fun w => hf w w₀
  have hf0 : 0 < fdeg w₀ := (hV K L v w₀ 1).2.2.1
  have he : ∀ (j : ℕ) (w : PlacesOver L v), ((η ^ j).loc v).comp (nm w) = 1 := by
    intro j w
    refine MonoidHom.ext fun x => ?_
    have hx := DFunLike.congr_fun (h2 v w).1 x
    simp only [MonoidHom.comp_apply, MonoidHom.one_apply] at hx ⊢
    rw [loc_pow_apply, hx, one_pow]
  have hm := hM K L hp n hn π P hW η h1 v s s' hs hs' θ hθ
  have hlp : lp (∑ j ∈ Finset.range (Module.finrank K L), vals (chs s) (θ * (η ^ j).loc v)) =
      (lp (∑ w, vals (chs (s' w)) (θ.comp (nm w)))).comp (X ^ fdeg w₀) := by
    rw [lp_sum, lp_sum, Polynomial.prod_comp]
    simp only [← (hC _ _).2.2]
    rw [hm]
    exact Finset.prod_congr rfl fun w _ => by rw [hfw w]
  have h3 := hP (fdeg w₀) hf0 _ _ hlp
  have h4 := hT K L v (Module.finrank K L) (fdeg w₀) (fun j => (η ^ j).loc v) hfw ⟨w₀⟩ he
    (fun w w' μ h => (h2 v w).2.1 w' μ h) (fun w μ hμ h => ((h2 v w).2.2 μ hμ).2.2 h)
    (chs s) (hC _ s).2.1 θ hθ
  have h5 := h3.symm.trans h4
  refine Multiset.ext.2 fun a => ?_
  have h6 := congrArg (Multiset.count a) h5
  rw [Multiset.count_nsmul, Multiset.count_nsmul] at h6
  exact Nat.eq_of_mul_eq_mul_left hf0 h6

end UpperTheory.Gal.GamX
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.ToralDeRham.GaloisCompatUnlinkedSupportOfSpherical
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamEqUnramifiedSatakeOfFrobenius
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamEqUnramifiedSatakeOfFrobenius
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut _root_.GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RoadU

theorem wdOf_eq_satWD_of_frobEig : ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ) (r : G E Ω →* GL (Fin n) (Qbar l)), Continuous r → ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w), ∀ B : Multiset ℂˣ, UpperTheory.V.Af.FrobEig ι r w (UpperTheory.V.Af.algSat n (normV w) B) → wdOf h hl ι r = satWD h n B := by
  intro Ω _ E _ _ _ _ l _ ι n r _hr w hl A h B hF
  obtain ⟨hI, hFr⟩ := hF A h
  have ht := isTameChar_tameL h hl
  have hN : IsMonodromy (tameL h hl) r 0 :=
    (isMonodromy_zero_iff (h := h)).mpr (.of_trivial fun σ => hI σ σ.2)
  have hu1 : (wdOf h hl ι r).unr := (hN.unr_wdOf_iff hl ht ι).mpr hI
  have hm : (0 : ℂ) ∉ B.map fun b => ((b⁻¹ : ℂˣ) : ℂ) := by
    simp
  have hs := WD.lpUnr_spec (h := h) _ hm
  have hu2 : (satWD h n B).unr := (WD.unr_tw _ _).mpr hs.1
  rw [WD.unr_eq_lpUnr _ hu1, WD.unr_eq_lpUnr _ hu2]
  congr 1
  rw [satWD, WD.frobEig_tw _ _ hs.1, hs.2.1, WD.frobEig, WD.eig, hN.charPol_wdOf hl ht ι (frob h)]
  have hσ : IsFrob A (normV w) ((frob h : Weil h) : G E Ω) := deg_eq_one_iff.mp deg_frob
  have hc := Formalism.L2.NR.charpoly_map_of_inv ι.toRingHom (r (frob h : G E Ω)) _
    (by rw [← map_inv]; exact hFr _ hσ)
  have e : ∀ s : Multiset ℂ, s.map (fun μ => X - C μ⁻¹) = (s.map (·⁻¹)).map (fun a => X - C a) := fun s => by
    rw [Multiset.map_map]; rfl
  rw [hc, e, roots_multiset_prod_X_sub_C, UpperTheory.V.Af.algSat, Multiset.map_map, Multiset.map_map]
  have hB : (do let a ← B; pure (a : ℂ) : Multiset ℂ) = B.map (Units.val : ℂˣ → ℂ) := by
    simp [Multiset.bind_singleton]
  rw [hB, Multiset.map_map]
  refine Multiset.map_congr rfl fun b _ => ?_
  simp only [Function.comp_apply, Units.val_inv_eq_inv_val]
  have hq : (0 : ℝ) ≤ ((normV w : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_cpow hq, show (1 - (n : ℝ)) / 2 = -(((n : ℝ) - 1) / 2) by ring,
    Real.rpow_neg hq, Complex.ofReal_inv, mul_inv, mul_comm]

end GlobalTheory.RoadU
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamEqUnramifiedSatakeOfFrobeniusStatement
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut _root_.GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilDeligneParam_eq_unramifiedSatake_of_frobenius : ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ) (r : G E Ω →* GL (Fin n) (Qbar l)), Continuous r → ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w), ∀ B : Multiset ℂˣ, UpperTheory.V.Af.FrobEig ι r w (UpperTheory.V.Af.algSat n (normV w) B) → wdOf h hl ι r = satWD h n B := by
  first | (exact @GlobalTheory.RoadU.wdOf_eq_satWD_of_frobEig) | (exact GlobalTheory.RoadU.wdOf_eq_satWD_of_frobEig) | (intros; apply GlobalTheory.RoadU.wdOf_eq_satWD_of_frobEig  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CrystallineDecompositionGroupNoMonodromy
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published
open GlobalTheory GlobalTheory.Cong GlobalTheory.UnitaryBC

namespace GlobalTheory.CrysNoMono

theorem crystalline_decompositionGroup_no_monodromy : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (P : LocPrime l) (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω)
    (h : IsPlaceOver A w) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw) (ρ : ↥(Dec (F := E) A) →* GL (Fin a) (Qbar l)),
    IsCrysAt P Bw ρ → (GlobalTheory.Pst.wdAt P ι Bw h hj ρ).mono0 := by
  intro E Ω _ _ _ _ _ l _ ι a P w A h O _ _ _ Bw hj ρ hc
  by_cases hr : IsPstAt P Bw ρ
  · exact (GlobalTheory.PstLaws.wdParameterAt_monodromy_zero_iff_potCrystalline Bw h hj P ι ρ hr).2 hc.isPotCrysAt
  · rw [wdAt_of_not_isPstAt ι Bw h hj hr, trivWD]
    exact WD.unr_mono0 _ ((WD.unr_mk _).2 (WDRep.unr_diag _))

end GlobalTheory.CrysNoMono
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.ToralDeRham.RcUnlinkedChars
namespace GalTw
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut _root_.GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RoadU.UnlinkedChars

theorem rc_unlinked_chars : UpperTheory.Gal.ToralGalois.Inq → ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [Algebra E Ω] [IsAlgClosure E Ω] (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w), ∀ (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (rc : IrrGL (k := w.adicCompletion E) → WD h), UpperTheory.Zero.LLC.LawsT a ha rc → ∀ (x : IrrGL (k := w.adicCompletion E)) (n : ℕ), ∀ (ξ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)), HasSupport x.rep (chars ξ hξ) → Unlinked (chars ξ hξ) → (rc x).mono0 ∧ ∀ g : Weil h, (rc x).charPol g = ∏ j, (X - C ((ξ j (a g) : ℂˣ) : ℂ)) := by
  intro hI Ω _ E _ _ _ _ w A h a ha rc H x n ξ hξ hs hu
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨𝔪, hm⟩ := hI.exh (w.adicCompletion E) x
  have hs' : HasSupport x.rep (msupp 𝔪) := GlobalTheory.LocGL.hasSupport_msupp_of_isL hI.zel _ 𝔪 x hm
  have he : chars ξ hξ = msupp 𝔪 :=
    GlobalTheory.LocGL.SupportUnique.hasSupport_unique GlobalTheory.RecT.geometricLemma_holds GlobalTheory.bernsteinZelevinskyFiniteness_holds
      hI.zel _ x _ _ hs hs'
  have hL := H.langlands 𝔪.toList x (by rw [Multiset.coe_toList]; exact hm)
  have hmem : ∀ Δ ∈ 𝔪, ∀ i : Fin Δ.len, Δ.term i ∈ chars ξ hξ := fun Δ hΔ i => by
    rw [he, msupp]
    exact Multiset.mem_bind.2 ⟨Δ, hΔ, Multiset.mem_map.2 ⟨i, Finset.mem_univ_val _, rfl⟩⟩

  have hlen : ∀ Δ ∈ 𝔪, Δ.len = 1 := by
    intro Δ hΔ
    by_contra hne
    have h2 : 1 < Δ.len := lt_of_le_of_ne Δ.len_pos (Ne.symm hne)
    refine hu _ (hmem Δ hΔ ⟨1, h2⟩) _ (hmem Δ hΔ ⟨0, Δ.len_pos⟩) ?_
    simp only [Segment.term, IrrGL.nu_nu]
    norm_num
  have hms : ∀ Δ ∈ 𝔪, Δ.ms = {Δ.first} := by
    intro Δ hΔ
    have e : Δ = Segment.single Δ.first Δ.isCusp_first := Segment.ext_first rfl (by rw [hlen Δ hΔ]; rfl)
    rw [e, Segment.ms_single]
    rfl
  have hsupp : msupp 𝔪 = 𝔪.map Segment.first := by
    rw [msupp, ← Multiset.bind_singleton]
    exact Multiset.bind_congr hms
  have hchar : ∀ y ∈ chars ξ hξ, ∃ j, y = IrrGL.ofChar (ξ j) (hξ j) := fun y hy => by
    obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 hy
    exact ⟨j, rfl⟩
  have hfirst : ∀ Δ ∈ 𝔪, ∃ j, Δ.first = IrrGL.ofChar (ξ j) (hξ j) := fun Δ hΔ =>
    hchar _ (by rw [he, hsupp]; exact Multiset.mem_map_of_mem _ hΔ)
  have hsum : rc x = sumList (𝔪.toList.map fun Δ => rc Δ.first) := by
    rw [hL, segSum]
    congr 1
    apply List.map_congr_left
    intro Δ hΔ
    rw [hlen Δ (Multiset.mem_toList.1 hΔ)]
    simp only [Nat.cast_one, sub_self, zero_div]
    exact (GlobalTheory.WeilDeligne.charPol_lpTw_lpChar_lpSp E Ω A w h _).1
  have hpol1 : ∀ j (g : Weil h), (rc (IrrGL.ofChar (ξ j) (hξ j))).charPol g = X - C ((ξ j (a g) : ℂˣ) : ℂ) := by
    intro j g
    rw [H.one, WD.lpOfChar, WD.charPol_mk, WDRep.ofChars_ρ, charpoly_diagEnd]
    simp
  refine ⟨?_, fun g => ?_⟩
  · rw [hsum]
    have key : ∀ L : List (Segment (w.adicCompletion E)), (∀ Δ ∈ L, Δ ∈ 𝔪) →
        (sumList (L.map fun Δ => rc Δ.first)).mono0 := by
      intro L
      induction L with
      | nil =>
        intro _
        show (WD.lpZero (h := h)).mono0
        exact (WD.monodromyZero_ofWeilDeligneRepClass_iff _).2 rfl
      | cons Δ L ih =>
        intro hL'
        obtain ⟨j, hj⟩ := hfirst Δ (hL' Δ List.mem_cons_self)
        show (WD.lpSum _ _).mono0
        refine (WD.monomial_sum_iff _ _).2 ⟨?_, ih fun Δ' h' => hL' Δ' (List.mem_cons_of_mem _ h')⟩
        change (rc Δ.first).mono0
        rw [hj]
        exact WD.mono0_of_lpDim_eq_one (by rw [H.dim]; rfl)
    exact key _ fun Δ hΔ => Multiset.mem_toList.1 hΔ
  · rw [hsum, GlobalTheory.LocLanglands.CuspExt.charPol_sumList, List.map_map]
    have r1 : (∏ j, (X - C ((ξ j (a g) : ℂˣ) : ℂ))) = ((chars ξ hξ).map fun y => (rc y).charPol g).prod := by
      rw [chars, Multiset.map_map, Finset.prod_eq_multiset_prod]
      exact congrArg Multiset.prod (Multiset.map_congr rfl fun j _ => (hpol1 j g).symm)
    rw [r1, he, hsupp, Multiset.map_map, ← Multiset.prod_coe, ← Multiset.map_coe, Multiset.coe_toList]
    rfl

end GlobalTheory.RoadU.UnlinkedChars

section

end
end
end GalTw
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.ToralDeRham.ToralGalois2
open GlobalTheory.RoadU

namespace GalTw
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut _root_.GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RoadU

theorem toralGal_of_holds : UpperTheory.Gal.ToralGalois.Inq → SphericalLevelCondition .all .unr → ToralGal := by
  intro hI hS E Ω _ _ _ _ _ _ l _ ι n hn π χ hπ r hr w hl A h σ hσ ξ hξ hsupp hunl a ha
  have key : ∀ g : Weil h, deg g ≠ 0 →
      (wdOf h hl ι r).mono0 ∧ (wdOf h hl ι r).charPol g = ∏ j, (X - C ((ξ j (a g) : ℂˣ) : ℂ)) := by
    intro g hg
    obtain ⟨M, _, _, _, _, _, _, _, u, h', P, χ', hP, hlift, hfix, B, hB, hchar⟩ :=
      GlobalTheory.T.frobenius_charpoly_of_unlinked_unramified_support hI Ω E l ι n hn π χ hπ r hr w A h σ hσ ξ hξ hsupp hunl a ha g hg
    have hl' : ((l : ℕ) : 𝓞 M) ∉ u.asIdeal := by
      intro hm
      apply hl
      refine (h ((l : ℕ) : 𝓞 E)).mp ?_
      have h1 := (h' ((l : ℕ) : 𝓞 M)).mpr hm
      simp only [map_natCast] at h1 ⊢
      exact h1
    have hr' : Weak P ι (resTo M r) := GlobalTheory.GalCut.weak_comp_res E M Ω l ι n π P hlift r hr
    have hF : UpperTheory.V.Af.FrobEig ι (resTo M r) u (UpperTheory.V.Af.algSat n (normV u) B) :=
      hS M Ω l ι n hn P χ' hP (resTo M r) hr' u trivial B hB hl'
    have hwd : wdOf h' hl' ι (resTo M r) = satWD h' n B :=
      GlobalTheory.T.weilDeligneParam_eq_unramifiedSatake_of_frobenius Ω M l ι n (resTo M r) hr'.1 u hl' A h' B hF
    have hres := GlobalTheory.AboveL.wdOf_restricts E M Ω A w u h h' l ι n r hl hl' hr.1
    obtain ⟨-, hmono, hcp⟩ := GlobalTheory.AboveL.restricts_lpDim_mono0_charPol E M Ω A w u h h' _ _ hres
    let g' : G M Ω := AlgEquiv.ofRingEquiv (f := (g : G E Ω).toRingEquiv) hfix
    have hmem : g' ∈ Weil h' := GlobalTheory.AboveL.mem_weil_of_fix E M Ω A w u h h' g g' fun _ => rfl
    refine ⟨hmono.mp ?_, ?_⟩
    · rw [hwd]
      simp [satWD, WD.lpUnr]
    · rw [← hcp g ⟨g', hmem⟩ fun _ => rfl, hwd]
      exact hchar g ⟨g', hmem⟩ fun _ => rfl
  have hy : ∀ g : Weil h, (WD.mk (WDRep.ofChars h (fun j : Fin n => (ξ j).comp a) fun j => ha.smooth (hξ j))).charPol g =
      ∏ j, (X - C ((ξ j (a g) : ℂˣ) : ℂ)) := by
    intro g
    rw [WD.charPol_mk, WDRep.ofChars_ρ, charpoly_diagEnd]
    rfl
  refine ⟨(key (frob h) (by rw [deg_frob]; exact one_ne_zero)).1, fun g => ?_⟩
  rw [← hy g]
  exact GlobalTheory.AboveL.charPol_eq_of_deg_ne_zero E Ω A w h _ _ (fun g hg => (key g hg).2.trans (hy g).symm) g

end GlobalTheory.RoadU

section
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut _root_.GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

end
end GalTw
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.ToralDeRham.ToralAboveOfHolds
open GlobalTheory.RoadU

namespace GalTw
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut _root_.GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RoadU

theorem toralAbove_of_holds : UpperTheory.Gal.ToralGalois.Inq → GlobalTheory.RoadU.SphericalLevelCondition .all .crys → GlobalTheory.RoadU.SphericalLevelCondition .all .phi → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ (π : CuspSub E n) (χ : HChar (maximalRealSubfield E)), InScope .all l π χ → ∀ r : G E Ω →* GL (Fin n) (Qbar l), Weak π ι r → ∀ (w : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) σ, π.IsLocComp w σ → ∀ (ξ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)), HasSupport (algNorm σ).rep (chars ξ hξ) → Unlinked (chars ξ hξ) → ∀ a : Weil h →* (w.adicCompletion E)ˣ, IsLocalArtin h a → ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : GlobalTheory.Pst.Induces Bw), IsPstAt P Bw (r.comp (Dec (F := E) A).subtype) ∧ (wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype)).mono0 ∧ ∀ g : Weil h, (wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype)).charPol g = ∏ j, (X - C ((ξ j (a g) : ℂˣ) : ℂ)) := by
  intro hI hC hF E Ω _ _ _ _ _ _ l _ ι n hn π χ hπ r hr w hl A h σ hσ ξ hξ hsupp hunl a ha P AI hT O _ _ _ Bw hj
  have key : ∀ g : Weil h, deg g ≠ 0 →
      IsPstAt P Bw (r.comp (Dec (F := E) A).subtype) ∧
      (wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype)).mono0 ∧
      (wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype)).charPol g = ∏ j, (X - C ((ξ j (a g) : ℂˣ) : ℂ)) := by
    intro g hg
    obtain ⟨M, _, _, _, _, _, _, _, u, h', Q, χ', hQ, hlift, hfix, B, hB, hchar⟩ :=
      GlobalTheory.T.frobenius_charpoly_of_unlinked_unramified_support hI Ω E l ι n hn π χ hπ r hr w A h σ hσ ξ hξ hsupp hunl a ha g hg
    have hr' : Weak Q ι (resTo M r) := GlobalTheory.GalCut.weak_comp_res E M Ω l ι n π Q hlift r hr
    obtain ⟨τ, hτ, -⟩ := GlobalTheory.CuspRep.LocEx.exists_isLocComp GlobalTheory.automorphicFormsFiniteGL M n Q u
    have hsph : IsSpherical τ.ρ :=
      GlobalTheory.TempSatUnr.isSpherical_of_hasSatGL (((GlobalTheory.Cong.satake_locComp M n Q u τ hτ).1 B).1 hB)
    have hcl : ClauseAt .crys Q ι (resTo M r) u := hC M Ω l ι n hn Q χ' hQ (resTo M r) hr' u trivial B hB
    have hph : SphAt .phi Q ι (resTo M r) u B := hF M Ω l ι n hn Q χ' hQ (resTo M r) hr' u trivial B hB
    obtain ⟨LL₀, Bw₀, hjj₀, -, -⟩ := GlobalTheory.AboveLRes.exists_bridge (L := M) Bw hj Bw.LL
    have hj₀ : GlobalTheory.Pst.Induces Bw₀ := fun x => by rw [hjj₀]; exact hj x
    have hc₀ := hcl P AI hT A h' _ Bw₀ hj₀ τ hτ hsph
    have hp₀ : IsPstAt P Bw₀ ((resTo M r).comp (Dec (F := M) A).subtype) :=
      GlobalTheory.GalCut.IwaAll.isPstAt_of_isSstAt P AI hT Bw₀ _
        (GlobalTheory.CrysSst.isSstAt_of_isCrysAt l P AI hT M Ω _ _ Bw₀ n _ hc₀)
    have hpst : IsPstAt P Bw (r.comp (Dec (F := E) A).subtype) :=
      GlobalTheory.AboveLRes.isPstAt_of_resTo E M Ω A l P AI hT n r hr.1 O _ Bw Bw₀ hj hj₀ hp₀
    obtain ⟨O', _, _, _, Bw', hj', -, hres⟩ :=
      GlobalTheory.AboveLRes.wdAt_resTo E M Ω A w u h h' l ι P AI hT n r O Bw hj hpst
    obtain ⟨-, hmono, hcp⟩ := GlobalTheory.AboveL.restricts_lpDim_mono0_charPol E M Ω A w u h h' _ _ hres
    have hc' := hcl P AI hT A h' O' Bw' hj' τ hτ hsph
    let g' : G M Ω := AlgEquiv.ofRingEquiv (f := (g : G E Ω).toRingEquiv) hfix
    have hmem : g' ∈ Weil h' := GlobalTheory.AboveL.mem_weil_of_fix E M Ω A w u h h' g g' fun _ => rfl
    refine ⟨hpst, hmono.mp (GlobalTheory.CrysNoMono.crystalline_decompositionGroup_no_monodromy M Ω l ι n P u A h' O' Bw' hj' _ hc'), ?_⟩
    rw [← hcp g ⟨g', hmem⟩ fun _ => rfl, hph P AI hT A h' O' Bw' hj' ⟨g', hmem⟩]
    exact hchar g ⟨g', hmem⟩ fun _ => rfl
  have hy : ∀ g : Weil h, (WD.mk (WDRep.ofChars h (fun j : Fin n => (ξ j).comp a) fun j => ha.smooth (hξ j))).charPol g =
      ∏ j, (X - C ((ξ j (a g) : ℂˣ) : ℂ)) := by
    intro g
    rw [WD.charPol_mk, WDRep.ofChars_ρ, charpoly_diagEnd]
    rfl
  obtain ⟨hpst, hmono, -⟩ := key (frob h) (by rw [deg_frob]; exact one_ne_zero)
  refine ⟨hpst, hmono, fun g => ?_⟩
  rw [← hy g]
  exact GlobalTheory.AboveL.charPol_eq_of_deg_ne_zero E Ω A w h _ _ (fun g hg => (key g hg).2.2.trans (hy g).symm) g

end GlobalTheory.RoadU
end GalTw
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.ToralDeRham.AwayEqOfPlainTor
open GlobalTheory.RoadU

namespace GalTw
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut _root_.GlobalTheory.RoadU
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RoadU

theorem away_eq_of_plainTor : UpperTheory.Gal.ToralGalois.Inq → ToralGal → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ (π : CuspSub E n) (χ : HChar (maximalRealSubfield E)), InScope .all l π χ → ∀ r : G E Ω →* GL (Fin n) (Qbar l), Weak π ι r → ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (σ : SmIrr (GL (Fin n) (w.adicCompletion E))), π.IsLocComp w σ → PlainTor (algNorm σ) → (wdOf h hl ι r).mono0 ∧ ∀ rc : IrrGL (k := w.adicCompletion E) → WD h, UpperTheory.Zero.LLC.IsRecT h rc → wdOf h hl ι r = rc (algNorm σ) := by
  intro hI hT E Ω _ _ _ _ _ _ l _ ι n hn π χ hπ r hr w hl A h σ hσ hp
  have : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨ξ, hξ, hs, hu⟩ := GlobalTheory.RoadU.plainTor_exists_chars (w.adicCompletion E) (algNorm σ) hp
  obtain ⟨a0, ha0⟩ := GlobalTheory.localArtinExists_holds E Ω A w h
  refine ⟨(hT E Ω l ι n hn π χ hπ r hr w hl A h σ hσ ξ hξ hs hu a0 ha0).1, ?_⟩
  rintro rc ⟨a, ha, H⟩
  obtain ⟨h1, h2⟩ := hT E Ω l ι n hn π χ hπ r hr w hl A h σ hσ ξ hξ hs hu a ha
  obtain ⟨h3, h4⟩ := GlobalTheory.RoadU.UnlinkedChars.rc_unlinked_chars hI Ω E w A h a ha rc H (algNorm σ) n ξ hξ hs hu
  exact GlobalTheory.WeakTheRep.eq_of_mono0_charPol _ _ h1 h3 fun g => (h2 g).trans (h4 g).symm

end GlobalTheory.RoadU
end GalTw
end

open GlobalTheory.RoadU

namespace GalTw
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut _root_.GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.DeRhamOfPlainTorus

theorem deRham_of_plainTor (hI : UpperTheory.Gal.ToralGalois.Inq) (hS : SphericalLevelCondition .all .dR) (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω]
    [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ) (hn : 1 ≤ n) (π : CuspSub E n)
    (χ : HChar (maximalRealSubfield E)) (hsc : InScope .all l π χ) (r : G E Ω →* GL (Fin n) (Qbar l)) (hw : Weak π ι r)
    (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (hσ : π.IsLocComp w σ)
    (hp : PlainTor (algNorm σ)) : ClauseAt .dR π ι r w := by
  intro P AI hT A hA O _ _ _ Bw hj
  have : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨ξ, hξ, hs, hu⟩ := GlobalTheory.RoadU.plainTor_exists_chars (w.adicCompletion E) (algNorm σ) hp
  obtain ⟨a, ha⟩ := GlobalTheory.localArtinExists_holds E Ω A w hA
  obtain ⟨M, _, _, _, _, _, _, _, u, h', PM, χ', hsc', hlift, -, B, hB, -⟩ :=
    GlobalTheory.RoadU.exists_sph_lift_of_toral hI Ω E l ι n hn π χ hsc r hw w A hA σ hσ ξ hξ hs hu a ha (frob hA)
      (by rw [deg_frob]; exact one_ne_zero)
  have hwM : Weak PM ι (resTo M r) := GlobalTheory.GalCut.weak_comp_res E M Ω l ι n π PM hlift r hw
  have hcl : ClauseAt .dR PM ι (resTo M r) u := hS M Ω l ι n hn PM χ' hsc' (resTo M r) hwM u trivial B hB
  obtain ⟨O', _, _, _, Bw', hj', hjj, hdesc⟩ :=
    GlobalTheory.DRDescent.deRham_descends E M Ω A w u hA h' l P AI hT n r hw.1 O Bw hj
  obtain ⟨hdR, hjump⟩ := hcl P AI hT A h' O' Bw' hj'
  refine ⟨hdesc hdR, ?_⟩
  intro τ LL' τ' hind J hJ
  obtain ⟨φ, hφ⟩ := IntermediateField.exists_algHom_of_splits
    (fun s : Om l => ⟨Algebra.IsIntegral.isIntegral s, IsAlgClosed.splits _⟩)
    ((IntermediateField.val LL'.1).comp τ')
  have hφx : ∀ x : E, φ (Bw.j (algebraMap E Ω x)) = τ x := by
    intro x
    have := congrArg (fun f => f ⟨Bw.j (algebraMap E Ω x), Bw.j_E x⟩) hφ
    simp only [AlgHom.comp_apply, IntermediateField.val_mk] at this
    rw [this, hind x]
    rfl
  let LL'' : FinExt l := ⟨Bw'.Kw.1.map φ, inferInstance⟩
  let τ'' : ↥Bw'.Kw.1 →ₐ[ℚ_[l]] ↥LL''.1 := (IntermediateField.equivMap Bw'.Kw.1 φ).toAlgHom
  let τL : M →+* Om l := φ.toRingHom.comp (Bw'.j.comp (algebraMap M Ω))
  have hτL : τL.comp (algebraMap E M) = τ := by
    ext x
    show φ (Bw'.j (algebraMap M Ω (algebraMap E M x))) = τ x
    rw [← IsScalarTower.algebraMap_apply E M Ω, hjj, hφx]
  have hind' : IsInduced Bw' τL τ'' := fun x => rfl
  have hJ' : J.map (fun n : ℤ => (n : ℂ)) =
      ((CG.mk PM).infChar (ι.toRingHom.comp τL)).map (fun z => ((n : ℂ) - 1) / 2 - z) := by
    rw [hlift.inf, RingHom.comp_assoc, hτL, hJ]
  exact GlobalTheory.JumpsDescend.jumps_descend E M Ω A w u hA h' l P AI hT n r hw.1 O Bw O' Bw' hj hj' hjj τ τL hτL J
    (hjump τL LL'' τ'' hind' J hJ')

theorem galoisCompat_unlinkedSupport_of_spherical : UpperTheory.Gal.ToralGalois.Inq → GlobalTheory.RoadU.CoreAll → GlobalTheory.DeRhamOfPlainTorus.R1 := by
  intro hI hC E Ω _ _ _ _ _ _ l _ ι n hn π χ hπ r hr w σ hσ hp
  refine ⟨fun hl A h => GlobalTheory.RoadU.away_eq_of_plainTor hI (GlobalTheory.RoadU.toralGal_of_holds hI (hC.2 .unr))
    E Ω l ι n hn π χ hπ r hr w hl A h σ hσ hp,
    fun hl => ⟨deRham_of_plainTor hI (hC.2 .dR) E Ω l ι n hn π χ hπ r hr w σ hσ hp, fun P AI hT A h O _ _ _ Bw hj => ?_⟩⟩
  have : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨ξ, hξ, hs, hu⟩ := GlobalTheory.RoadU.plainTor_exists_chars (w.adicCompletion E) (algNorm σ) hp
  have key := fun a ha => GlobalTheory.RoadU.toralAbove_of_holds hI (hC.2 .crys) (hC.2 .phi) E Ω l ι n hn π χ hπ r hr w hl A h σ hσ
    ξ hξ hs hu a ha P AI hT O Bw hj
  obtain ⟨a0, ha0⟩ := GlobalTheory.localArtinExists_holds E Ω A w h
  refine ⟨(key a0 ha0).1, (key a0 ha0).2.1, ?_⟩
  rintro rc ⟨a, ha, H⟩ g
  exact ((key a ha).2.2 g).trans
    ((GlobalTheory.RoadU.UnlinkedChars.rc_unlinked_chars hI Ω E w A h a ha rc H (algNorm σ) n ξ hξ hs hu).2 g).symm

end GlobalTheory.DeRhamOfPlainTorus

end
end GalTw
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.FdegEq
noncomputable section

open NumberField IsDedekindDomain
open GroundTheory.Global.SemiLocal UpperTheory.V.Z.Gam

namespace UpperTheory.Gal.GamX

theorem fdegEq : FdegEq := by
  intro K L _ _ _ _ _ _ v
  refine ⟨GroundTheory.Global.nonempty_placesOver L v, fun w w' => ?_⟩
  have hw := w.2
  have hw' := w'.2
  unfold fdeg
  rw [Ideal.inertiaDeg'_eq_inertiaDeg v.asIdeal w.1.asIdeal,
    Ideal.inertiaDeg'_eq_inertiaDeg v.asIdeal w'.1.asIdeal]
  exact Ideal.inertiaDeg_eq_of_isGaloisGroup v.asIdeal w.1.asIdeal w'.1.asIdeal Gal(L/K)

end UpperTheory.Gal.GamX
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.CharLiftPrimeHolds
namespace UpperTheory.Gal.GamX

open UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.T

theorem gamSum_holds : GamSum :=
  gamSumOf matchBCX normCnt normVal (lpPowOf lpInj) chsFacts fdegEq (twValsOf normVal)

theorem gamOne_holds : GamOne := gamOneOf chsFacts (valsExtOf polFacts) gamSum_holds

theorem splitSupp_holds : SplitSupp :=
  splitSuppOf nmEq suppFacts Sph.weakStable
    (splitStrong (descStep (coreDesc ci Sph.gm) (liftAll (liftStep (coreLift ci Sph.gm)))))

theorem gamMixed_holds : GamMixed :=
  gamMixed_of gamOne_holds splitSupp_holds chsTr rkSupp (rkLiftOf UpperTheory.V.Z.Gam.normLoc) (upThruOf chsFacts)

theorem charSupp_holds : CharSupp := charSupp_of gamMixed_holds nmEq suppFacts

theorem charLiftPrime_holds : CharLiftPrime := charLiftPrime_of charSupp_holds

end UpperTheory.Gal.GamX
end

namespace UpperTheory.Gal.ToralGalois

theorem inq_holds : Inq := ⟨UpperTheory.Gal.Int.Inp.inp_holds, UpperTheory.Gal.GamX.charLiftPrime_holds⟩

theorem galoisCompat_unlinkedSupport_of_spherical : GlobalTheory.RoadU.CoreAll → GlobalTheory.DeRhamOfPlainTorus.R1 := GalTw.GlobalTheory.DeRhamOfPlainTorus.galoisCompat_unlinkedSupport_of_spherical inq_holds

end UpperTheory.Gal.ToralGalois
