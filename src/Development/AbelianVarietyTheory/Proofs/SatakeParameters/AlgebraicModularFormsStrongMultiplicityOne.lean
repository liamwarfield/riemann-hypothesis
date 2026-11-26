module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeDEqSum
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameBlockTypeAtSplitPlace
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GraphOfFixedGraph

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AlgebraicModularFormsHeckeModulesIsoAllPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrincipalCongruenceSplitTrivOutsideAndAtPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrincipalCongruenceSplitTrivOutsideAndAtPlace
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CongSplitBoth

open GlobalTheory.IdemSplit GlobalTheory.CongSplit

theorem split_cong_at_place : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (N : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (κ : GAf L n), NG.Cong L n N κ → ∃ x y : GAf L n, TrivOutside {v} x ∧ TrivOutside {v}ᶜ y ∧ NG.Cong L n N x ∧ NG.Cong L n N y ∧ κ = x * y := by
  intro L _ _ _ n N v κ hc
  set e := idemAt L v with he_def
  have he : e * e = e := idemAt_mul_self L v
  have he' : (1 - e) * (1 - e) = 1 - e := by
    rw [sub_mul, one_mul, mul_sub, mul_one, he, sub_self, sub_zero]
  have hσ : conjAL L e = e := conjAL_idemAt L v
  have hσ' : conjAL L (1 - e) = 1 - e := by rw [map_sub, map_one, hσ]
  have hei : e ∈ ALint L := idemAt_mem L v
  have hei' : 1 - e ∈ ALint L := Subring.sub_mem _ (one_mem _) hei
  refine ⟨gaFold he hσ κ, gaFold he' hσ' κ, ?_, ?_, ?_, ?_, ?_⟩
  · intro w hw
    have hw' : w ≠ v := by simpa using hw
    ext i j
    rw [Matrix.map_apply, gaFold_val, fold_apply, map_add (f := _), map_mul, map_mul, map_sub, map_one,
      compAt_idemAt_ne L v hw', compAt_one_apply]
    simp
  · intro w hw
    have hw' : w = v := by simpa using hw
    subst hw'
    ext i j
    rw [Matrix.map_apply, gaFold_val, fold_apply, map_add (f := _), map_mul, map_mul, map_sub, map_one,
      compAt_one_apply]
    simp [he_def, compAt_idemAt_self]
  · refine ⟨gaFold_mem_Umax L he hσ hei κ hc.1, fun i j => ?_⟩
    obtain ⟨y, hy, hEq⟩ := hc.2 i j
    refine ⟨e * y, Subring.mul_mem _ hei hy, ?_⟩
    rw [gaFold_val, fold_apply]
    linear_combination e * hEq
  · refine ⟨gaFold_mem_Umax L he' hσ' hei' κ hc.1, fun i j => ?_⟩
    obtain ⟨y, hy, hEq⟩ := hc.2 i j
    refine ⟨(1 - e) * y, Subring.mul_mem _ hei' hy, ?_⟩
    rw [gaFold_val, fold_apply, sub_sub_cancel]
    linear_combination (1 - e) * hEq
  · apply Subtype.ext; apply Units.ext
    show (κ.1 : Matrix (Fin n) (Fin n) (AL L)) = fold e _ * fold (1 - e) _
    rw [fold_mul_fold he, ← add_smul, add_sub_cancel, one_smul]

end GlobalTheory.CongSplitBoth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrincipalCongruenceSplitTrivOutsideAndAtPlaceStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalCongruence_split_trivOutside_and_at_place : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (N : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (κ : GAf L n), NG.Cong L n N κ → ∃ x y : GAf L n, TrivOutside {v} x ∧ TrivOutside {v}ᶜ y ∧ NG.Cong L n N x ∧ NG.Cong L n N y ∧ κ = x * y := by
  first | exact @GlobalTheory.CongSplitBoth.split_cong_at_place | exact GlobalTheory.CongSplitBoth.split_cong_at_place | (intros; apply GlobalTheory.CongSplitBoth.split_cong_at_place <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsDoubleCosetCommutingMapPrincipalCongruence
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsDoubleCosetCommutingMapPrincipalCongruence
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.HeckeIsoMap

theorem isoMap : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S₁ S₂ : Submodule ℂ (GAf L n → a.W)), NG.IsIrrRep a.ρ S₁ → NG.IsoRep S₁ S₂ → ∀ N : ℕ, 0 < N → (∃ f ∈ S₁, (∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) ∧ f ≠ 0) → ∃ φ : (GAf L n → a.W) →ₗ[ℂ] (GAf L n → a.W), (∀ f ∈ S₁, (∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) → φ f ∈ S₂ ∧ ∀ κ, NG.Cong L n N κ → NG.rt L n κ (φ f) = φ f) ∧ (∃ f ∈ S₁, (∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) ∧ φ f ≠ 0) ∧ (∀ (g : GAf L n) (f : GAf L n → a.W), f ∈ S₁ → (∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) → φ (NG.heckeD (GlobalTheory.IsotOrth.congSub L n N) {x | ∃ u ∈ GlobalTheory.IsotOrth.congSub L n N, ∃ u' ∈ GlobalTheory.IsotOrth.congSub L n N, x = u * g * u'} f) = NG.heckeD (GlobalTheory.IsotOrth.congSub L n N) {x | ∃ u ∈ GlobalTheory.IsotOrth.congSub L n N, ∃ u' ∈ GlobalTheory.IsotOrth.congSub L n N, x = u * g * u'} (φ f)) := by
  classical
  intro L _ _ _ n a S₁ S₂ hS₁ hiso N hN hex
  obtain ⟨T, hT⟩ := hiso
  obtain ⟨φ, hφ⟩ := LinearMap.exists_extend (S₂.subtype ∘ₗ T.toLinearMap)
  have hφS : ∀ f (hf : f ∈ S₁), φ f = ((T ⟨f, hf⟩ : S₂) : GAf L n → a.W) := by
    intro f hf
    have := LinearMap.congr_fun hφ ⟨f, hf⟩
    simpa using this
  have hrt : ∀ h (f : GAf L n → a.W), f ∈ S₁ → φ (NG.rt L n h f) = NG.rt L n h (φ f) := by
    intro h f hf
    have hf' : NG.rt L n h f ∈ S₁ := hS₁.1.stable h f hf
    rw [hφS _ hf', hφS _ hf]
    exact hT h ⟨f, hf⟩ ⟨_, hf'⟩ rfl
  refine ⟨φ, ?_, ?_, ?_⟩
  · intro f hf hfix
    refine ⟨?_, fun κ hκ => ?_⟩
    · rw [hφS _ hf]; exact (T ⟨f, hf⟩).2
    · rw [← hrt κ f hf, hfix κ hκ]
  · obtain ⟨f, hf, hfix, hne⟩ := hex
    refine ⟨f, hf, hfix, ?_⟩
    rw [hφS _ hf]
    intro h0
    apply hne
    have : T ⟨f, hf⟩ = 0 := Subtype.ext h0
    have := congrArg Subtype.val ((LinearEquiv.map_eq_zero_iff T).1 this)
    simpa using this
  · intro g f hf hfix
    set J := GlobalTheory.IsotOrth.congSub L n N with hJ
    set D : Set (GAf L n) := {x | ∃ u ∈ J, ∃ u' ∈ J, x = u * g * u'} with hD
    obtain ⟨M, hM, hMc⟩ := GlobalTheory.ConjCong.exists_cong_conj L n N g hN
    have hfin : {c : GAf L n ⧸ J | ∃ x ∈ D, (x : GAf L n ⧸ J) = c}.Finite := by
      refine ((GlobalTheory.HeckeRecon.finite_cosets (L := L) (n := n) (N * M) (Nat.mul_pos hN hM)).image
        (fun c : GAf L n ⧸ GlobalTheory.IsotOrth.congSub L n (N * M) => ((c.out * g : GAf L n) : GAf L n ⧸ J))).subset ?_
      rintro _ ⟨x, ⟨u, hu, u', hu', rfl⟩, rfl⟩
      refine ⟨(u : GAf L n ⧸ GlobalTheory.IsotOrth.congSub L n (N * M)), ⟨u, (show NG.Cong L n N u from hu).1, rfl⟩, ?_⟩
      obtain ⟨k, hk⟩ : ∃ k ∈ GlobalTheory.IsotOrth.congSub L n (N * M),
          (Quotient.out (u : GAf L n ⧸ GlobalTheory.IsotOrth.congSub L n (N * M))) = u * k := by
        have h1 := QuotientGroup.out_eq' (u : GAf L n ⧸ GlobalTheory.IsotOrth.congSub L n (N * M))
        rw [QuotientGroup.eq] at h1
        exact ⟨_, Subgroup.inv_mem _ h1, by group⟩
      obtain ⟨hkmem, hkeq⟩ := hk
      show ((Quotient.out (u : GAf L n ⧸ GlobalTheory.IsotOrth.congSub L n (N * M)) * g : GAf L n) : GAf L n ⧸ J) = ((u * g * u' : GAf L n) : GAf L n ⧸ J)
      rw [hkeq, QuotientGroup.eq]
      have hc : g⁻¹ * k * g ∈ J := hMc k hkmem
      have : (u * k * g)⁻¹ * (u * g * u') = (g⁻¹ * k * g)⁻¹ * u' := by group
      rw [this]
      exact J.mul_mem (J.inv_mem hc) hu'
    have hsum : ∀ F : GAf L n → a.W, NG.heckeD J D F = ∑ c ∈ hfin.toFinset,
        (if hc : ∃ x ∈ D, (x : GAf L n ⧸ J) = c then NG.rt L n hc.choose F else 0) := by
      intro F
      funext x
      rw [GlobalTheory.HeckeRecon.heckeD_eq_sum J D hfin, Finset.sum_apply]
      refine Finset.sum_congr rfl fun c _ => ?_
      split_ifs <;> rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hsum, hsum, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs with hc
    · exact hrt _ f hf
    · exact map_zero φ

end GlobalTheory.HeckeIsoMap
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsDoubleCosetCommutingMapPrincipalCongruenceStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_doubleCosetCommuting_map_principalCongruence : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S₁ S₂ : Submodule ℂ (GAf L n → a.W)), NG.IsIrrRep a.ρ S₁ → NG.IsoRep S₁ S₂ → ∀ N : ℕ, 0 < N → (∃ f ∈ S₁, (∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) ∧ f ≠ 0) → ∃ φ : (GAf L n → a.W) →ₗ[ℂ] (GAf L n → a.W), (∀ f ∈ S₁, (∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) → φ f ∈ S₂ ∧ ∀ κ, NG.Cong L n N κ → NG.rt L n κ (φ f) = φ f) ∧ (∃ f ∈ S₁, (∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) ∧ φ f ≠ 0) ∧ (∀ (g : GAf L n) (f : GAf L n → a.W), f ∈ S₁ → (∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) → φ (NG.heckeD (GlobalTheory.IsotOrth.congSub L n N) {x | ∃ u ∈ GlobalTheory.IsotOrth.congSub L n N, ∃ u' ∈ GlobalTheory.IsotOrth.congSub L n N, x = u * g * u'} f) = NG.heckeD (GlobalTheory.IsotOrth.congSub L n N) {x | ∃ u ∈ GlobalTheory.IsotOrth.congSub L n N, ∃ u' ∈ GlobalTheory.IsotOrth.congSub L n N, x = u * g * u'} (φ f)) := by
  first | exact @GlobalTheory.HeckeIsoMap.isoMap | exact GlobalTheory.HeckeIsoMap.isoMap | (intros; apply GlobalTheory.HeckeIsoMap.isoMap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsStableGraphOfIsoSplitPlaceComponents
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsStableGraphOfIsoSplitPlaceComponents
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocSplitGraph

theorem main : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S₁ S₂ : Submodule ℂ (GAf L n → a.W)) (s : SplitPlace L) (σ₁ σ₂ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))), IsLocS S₁ s σ₁ → IsLocS S₂ s σ₂ → Nonempty (σ₁.ρ.Equiv σ₂.ρ) → ∃ X : Submodule ℂ ((GAf L n → a.W) × (GAf L n → a.W)), X ≠ ⊥ ∧ (∀ z ∈ X, z.1 ∈ S₁ ∧ z.2 ∈ S₂) ∧ (∀ x : GAf L n, TrivOutside {s.v} x → ∀ z ∈ X, (NG.rt L n x z.1, NG.rt L n x z.2) ∈ X) ∧ (∀ u, ((0 : GAf L n → a.W), u) ∈ X → u = 0) ∧ (∀ u, (u, (0 : GAf L n → a.W)) ∈ X → u = 0) := by
  intro L _ _ _ n a S₁ S₂ s σ₁ σ₂ h₁ h₂ hE
  obtain ⟨E⟩ := hE
  obtain ⟨i₁, T₁, hi₁, hiL₁, hT₁inj, hT₁S, hT₁eq⟩ := h₁
  obtain ⟨i₂, T₂, hi₂, hiL₂, hT₂inj, hT₂S, hT₂eq⟩ := h₂

  have hci : i₁ = i₂ := by
    have hd := IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap (K := maximalRealSubfield L) s.v
    have hfun : (i₁ : s.v.adicCompletion (maximalRealSubfield L) → s.w.adicCompletion L) = i₂ := by
      refine hd.equalizer hi₁ hi₂ (funext fun y => ?_)
      simp only [Function.comp_apply]
      rw [← s.i.commutes y, hiL₁, hiL₂]
    exact RingEquiv.ext (congrFun hfun)
  subst hci
  let F : σ₁.V →ₗ[ℂ] (GAf L n → a.W) × (GAf L n → a.W) := T₁.prod (T₂ ∘ₗ E.toLinearEquiv.toLinearMap)
  have hF : ∀ u, F u = (T₁ u, T₂ (E u)) := fun u => rfl
  have hEint : ∀ g u, E (σ₁.ρ g u) = σ₂.ρ g (E u) := fun g u => LinearMap.congr_fun (E.isIntertwining' g) u
  have hnt : Nontrivial σ₁.V := by
    haveI := σ₁.irr
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    apply (bot_ne_top : (⊥ : Subrepresentation σ₁.ρ) ≠ ⊤)
    have : ∀ W : Subrepresentation σ₁.ρ, W = ⊥ := by
      intro W
      ext x
      simp [Subsingleton.elim x 0]
    rw [this ⊤]
  refine ⟨LinearMap.range F, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨u, hu⟩ := exists_ne (0 : σ₁.V)
    intro h
    have hm : F u ∈ LinearMap.range F := ⟨u, rfl⟩
    rw [h, Submodule.mem_bot, hF, Prod.mk_eq_zero] at hm
    exact hu (hT₁inj (hm.1.trans (map_zero T₁).symm))
  · rintro _ ⟨u, rfl⟩
    exact ⟨hT₁S u, hT₂S (E u)⟩
  · rintro x hx _ ⟨u, rfl⟩
    refine ⟨σ₁.ρ (Matrix.GeneralLinearGroup.map i₁.toRingHom (s.loc n x)) u, ?_⟩
    rw [hF, hF, hT₁eq x hx u, hEint, hT₂eq x hx (E u)]
  · rintro u ⟨v, hv⟩
    rw [hF, Prod.mk.injEq] at hv
    have hv0 : v = 0 := hT₁inj (hv.1.trans (map_zero T₁).symm)
    rw [← hv.2, hv0, map_zero, map_zero]
  · rintro u ⟨v, hv⟩
    rw [hF, Prod.mk.injEq] at hv
    have hv0 : E v = 0 := hT₂inj (hv.2.trans (map_zero T₂).symm)
    have : v = 0 := by simpa using hv0
    rw [← hv.1, this, map_zero]

end GlobalTheory.LocSplitGraph
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsStableGraphOfIsoSplitPlaceComponentsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_stable_graph_of_iso_splitPlace_components : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S₁ S₂ : Submodule ℂ (GAf L n → a.W)) (s : SplitPlace L) (σ₁ σ₂ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))), IsLocS S₁ s σ₁ → IsLocS S₂ s σ₂ → Nonempty (σ₁.ρ.Equiv σ₂.ρ) → ∃ X : Submodule ℂ ((GAf L n → a.W) × (GAf L n → a.W)), X ≠ ⊥ ∧ (∀ z ∈ X, z.1 ∈ S₁ ∧ z.2 ∈ S₂) ∧ (∀ x : GAf L n, TrivOutside {s.v} x → ∀ z ∈ X, (NG.rt L n x z.1, NG.rt L n x z.2) ∈ X) ∧ (∀ u, ((0 : GAf L n → a.W), u) ∈ X → u = 0) ∧ (∀ u, (u, (0 : GAf L n → a.W)) ∈ X → u = 0) := by
  first | exact @GlobalTheory.LocSplitGraph.main | exact GlobalTheory.LocSplitGraph.main | (intros; apply GlobalTheory.LocSplitGraph.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsStableGraphOfEqualAnnihilators
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsStableGraphOfEqualAnnihilators
open Module

namespace GlobalTheory.CommDet

variable {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type}

def Stab (C : ι → Subalgebra ℂ (Module.End ℂ V)) (U : Submodule ℂ V) : Prop :=
  ∀ v, ∀ c ∈ C v, ∀ x ∈ U, c x ∈ U

def Comm (C : ι → Subalgebra ℂ (Module.End ℂ V)) (U : Submodule ℂ V) : Prop :=
  ∀ v w, v ≠ w → ∀ c ∈ C v, ∀ d ∈ C w, ∀ x ∈ U, c (d x) = d (c x)

def Irr (C : ι → Subalgebra ℂ (Module.End ℂ V)) (U : Submodule ℂ V) : Prop :=
  ∀ Y ≤ U, Stab C Y → Y = ⊥ ∨ Y = U

def Kills (c : Module.End ℂ V) (U : Submodule ℂ V) : Prop := ∀ x ∈ U, c x = 0

def Graph (C : ι → Subalgebra ℂ (Module.End ℂ V)) (U₁ U₂ : Submodule ℂ V)
    (X : Submodule ℂ (V × V)) : Prop :=
  X ≠ ⊥ ∧ (∀ z ∈ X, z.1 ∈ U₁ ∧ z.2 ∈ U₂) ∧ (∀ v, ∀ c ∈ C v, ∀ z ∈ X, (c z.1, c z.2) ∈ X) ∧
    (∀ u, ((0 : V), u) ∈ X → u = 0) ∧ (∀ u, (u, (0 : V)) ∈ X → u = 0)

theorem kills_iff_map (c : Module.End ℂ V) (U : Submodule ℂ V) :
    Kills c U ↔ U.map c = ⊥ := by
  constructor
  · intro h
    rw [eq_bot_iff]
    rintro _ ⟨x, hx, rfl⟩
    simp [h x hx]
  · intro h x hx
    have : c x ∈ U.map c := Submodule.mem_map_of_mem hx
    rw [h] at this
    simpa using this

theorem kills_scalar {U : Submodule ℂ V} (hU : U ≠ ⊥) (r : ℂ) :
    Kills (algebraMap ℂ (Module.End ℂ V) r) U ↔ r = 0 := by
  constructor
  · intro h
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
    have := h x hx
    rw [Module.algebraMap_end_apply] at this
    exact (smul_eq_zero.mp this).resolve_right hx0
  · rintro rfl x _
    simp

theorem eig_drop (U : Submodule ℂ V) [FiniteDimensional ℂ U] (hU : U ≠ ⊥)
    (g : Module.End ℂ V) (hg : ∀ x ∈ U, g x ∈ U) :
    ∃ μ : ℂ, finrank ℂ (U.map (g - algebraMap ℂ (Module.End ℂ V) μ)) < finrank ℂ U := by
  haveI : Nontrivial U := Submodule.nontrivial_iff_ne_bot.mpr hU
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (g.restrict hg)
  obtain ⟨z, hz⟩ := hμ.exists_hasEigenvector
  refine ⟨μ, ?_⟩
  set f := (g - algebraMap ℂ (Module.End ℂ V) μ).comp U.subtype with hf
  have hr : LinearMap.range f = U.map (g - algebraMap ℂ (Module.End ℂ V) μ) := by
    rw [hf, LinearMap.range_comp, Submodule.range_subtype]
  have hz1 : g (z : V) = μ • (z : V) := by
    have h1 := congrArg Subtype.val hz.apply_eq_smul
    simpa [LinearMap.restrict_apply] using h1
  have hk : z ∈ LinearMap.ker f := by
    simp [hf, hz1]
  have hsum := LinearMap.finrank_range_add_finrank_ker f
  rw [hr] at hsum
  have hpos : 0 < finrank ℂ (LinearMap.ker f) := by
    rw [Nat.pos_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
    intro h
    rw [h] at hk
    exact hz.2 ((Submodule.mem_bot ℂ).mp hk)
  omega

theorem graph_of_scalars (C : ι → Subalgebra ℂ (Module.End ℂ V)) (U₁ U₂ : Submodule ℂ V)
    (h₁ : U₁ ≠ ⊥) (h₂ : U₂ ≠ ⊥)
    (hs : ∀ v, ∀ a ∈ C v, ∃ μ : ℂ, (∀ x ∈ U₁, a x = μ • x) ∧ (∀ x ∈ U₂, a x = μ • x)) :
    ∃ X, Graph C U₁ U₂ X := by
  obtain ⟨x₁, hx₁, hx₁0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h₁
  obtain ⟨x₂, hx₂, hx₂0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h₂
  refine ⟨ℂ ∙ (x₁, x₂), ?_, ?_, ?_, ?_, ?_⟩
  · rw [Ne, Submodule.span_singleton_eq_bot]
    intro h
    exact hx₁0 (congrArg Prod.fst h)
  · intro z hz
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hz
    exact ⟨U₁.smul_mem t hx₁, U₂.smul_mem t hx₂⟩
  · intro v c hc z hz
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hz
    obtain ⟨μ, hμ₁, hμ₂⟩ := hs v c hc
    rw [Submodule.mem_span_singleton]
    refine ⟨t * μ, ?_⟩
    ext
    · simp [hμ₁ x₁ hx₁, smul_smul]
    · simp [hμ₂ x₂ hx₂, smul_smul]
  · intro u hu
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hu
    have e1 : t • x₁ = 0 := congrArg Prod.fst ht
    have e2 : t • x₂ = u := congrArg Prod.snd ht
    have : t = 0 := (smul_eq_zero.mp e1).resolve_right hx₁0
    rw [← e2, this, zero_smul]
  · intro u hu
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hu
    have e1 : t • x₁ = u := congrArg Prod.fst ht
    have e2 : t • x₂ = 0 := congrArg Prod.snd ht
    have : t = 0 := (smul_eq_zero.mp e2).resolve_right hx₂0
    rw [← e1, this, zero_smul]


open Classical in
noncomputable def drop (C : ι → Subalgebra ℂ (Module.End ℂ V)) (v : ι) :
    ι → Subalgebra ℂ (Module.End ℂ V) :=
  fun w => if w = v then ⊥ else C w

theorem drop_le (C : ι → Subalgebra ℂ (Module.End ℂ V)) (v w : ι) : drop C v w ≤ C w := by
  unfold drop
  split_ifs
  · exact bot_le
  · exact le_rfl

theorem drop_ne (C : ι → Subalgebra ℂ (Module.End ℂ V)) (v : ι) {w : ι} (h : w ≠ v) :
    drop C v w = C w := by
  simp [drop, h]

theorem drop_self (C : ι → Subalgebra ℂ (Module.End ℂ V)) (v : ι) {d : Module.End ℂ V}
    (hd : d ∈ drop C v v) : ∃ r : ℂ, algebraMap ℂ (Module.End ℂ V) r = d := by
  have h : drop C v v = ⊥ := by simp [drop]
  rw [h] at hd
  exact Algebra.mem_bot.mp hd

theorem comm_drop (C : ι → Subalgebra ℂ (Module.End ℂ V)) (v : ι) {U U' : Submodule ℂ V}
    (hc : Comm C U) (hle : U' ≤ U) : Comm (drop C v) U' := by
  intro w₁ w₂ hw c hc' d hd x hx
  by_cases h1 : w₁ = v
  · rw [h1] at hc'
    obtain ⟨r, rfl⟩ := drop_self C v hc'
    simp [Module.algebraMap_end_apply]
  · by_cases h2 : w₂ = v
    · rw [h2] at hd
      obtain ⟨r, rfl⟩ := drop_self C v hd
      simp [Module.algebraMap_end_apply]
    · rw [drop_ne C v h1] at hc'
      rw [drop_ne C v h2] at hd
      exact hc w₁ w₂ hw c hc' d hd x (hle hx)

theorem map_le_self {C : ι → Subalgebra ℂ (Module.End ℂ V)} {v : ι} {U : Submodule ℂ V}
    {c₀ : Module.End ℂ V} (hS : Stab C U) (hc₀ : c₀ ∈ C v) : U.map c₀ ≤ U := by
  rintro _ ⟨x, hx, rfl⟩
  exact hS v c₀ hc₀ x hx

theorem stab_drop {C : ι → Subalgebra ℂ (Module.End ℂ V)} {v : ι} {U : Submodule ℂ V}
    {c₀ : Module.End ℂ V} (hS : Stab C U) (hC : Comm C U) (hc₀ : c₀ ∈ C v) :
    Stab (drop C v) (U.map c₀) := by
  rintro w d hd _ ⟨x, hx, rfl⟩
  by_cases h : w = v
  · rw [h] at hd
    obtain ⟨r, rfl⟩ := drop_self C v hd
    rw [Module.algebraMap_end_apply]
    exact Submodule.smul_mem _ r (Submodule.mem_map_of_mem hx)
  · rw [drop_ne C v h] at hd
    have e : d (c₀ x) = c₀ (d x) := (hC v w (Ne.symm h) c₀ hc₀ d hd x hx).symm
    rw [e]
    exact Submodule.mem_map_of_mem (hS w d hd x hx)

def orbSpan (C : ι → Subalgebra ℂ (Module.End ℂ V)) (v : ι) (Y : Submodule ℂ V) :
    Submodule ℂ V :=
  Submodule.span ℂ {x | ∃ a ∈ C v, ∃ y ∈ Y, a y = x}

theorem orbSpan_eq {C : ι → Subalgebra ℂ (Module.End ℂ V)} {v : ι} {U : Submodule ℂ V}
    (hS : Stab C U) (hC : Comm C U) (hI : Irr C U) {Y : Submodule ℂ V}
    (hYU : Y ≤ U) (hYS : Stab (drop C v) Y) (hY : Y ≠ ⊥) : orbSpan C v Y = U := by
  have hle : orbSpan C v Y ≤ U := by
    rw [orbSpan, Submodule.span_le]
    rintro _ ⟨a, ha, y, hy, rfl⟩
    exact hS v a ha y (hYU hy)
  have hst : Stab C (orbSpan C v Y) := by
    intro w c hc x hx
    have key : orbSpan C v Y ≤ (orbSpan C v Y).comap c := by
      unfold orbSpan
      rw [Submodule.span_le]
      rintro _ ⟨a, ha, y, hy, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap]
      by_cases h : w = v
      · rw [h] at hc
        exact Submodule.subset_span ⟨c * a, mul_mem hc ha, y, hy, rfl⟩
      · have hc' : c ∈ drop C v w := by rw [drop_ne C v h]; exact hc
        rw [hC w v h c hc a ha y (hYU hy)]
        exact Submodule.subset_span ⟨a, ha, c y, hYS w c hc' y hy, rfl⟩
    exact key hx
  have hYle : Y ≤ orbSpan C v Y := fun y hy =>
    Submodule.subset_span ⟨1, one_mem _, y, hy, by simp⟩
  rcases hI _ hle hst with h | h
  · exact absurd (eq_bot_iff.mpr (h ▸ hYle)) hY
  · exact h

theorem irr_drop {C : ι → Subalgebra ℂ (Module.End ℂ V)} {v : ι} {U : Submodule ℂ V}
    {c₀ : Module.End ℂ V} (hS : Stab C U) (hC : Comm C U) (hI : Irr C U) (hc₀ : c₀ ∈ C v)
    (hsc : ∀ a ∈ C v, ∃ μ : ℂ, ∀ x ∈ U, c₀ (a (c₀ x)) = μ • c₀ x) :
    Irr (drop C v) (U.map c₀) := by
  intro Y hY hYS
  by_cases hb : Y = ⊥
  · exact Or.inl hb
  right
  apply le_antisymm hY
  have hsp := orbSpan_eq hS hC hI (hY.trans (map_le_self hS hc₀)) hYS hb
  rw [Submodule.map_le_iff_le_comap, ← hsp, orbSpan, Submodule.span_le]
  rintro _ ⟨a, ha, y, hy, rfl⟩
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp (hY hy)
  obtain ⟨μ, hμ⟩ := hsc a ha
  show c₀ (a (c₀ x)) ∈ Y
  rw [hμ x hx]
  exact Y.smul_mem μ hy

theorem kills_drop {C : ι → Subalgebra ℂ (Module.End ℂ V)} {v : ι} {U : Submodule ℂ V}
    {c₀ : Module.End ℂ V} (hS : Stab C U) (hC : Comm C U) (hI : Irr C U) (hc₀ : c₀ ∈ C v)
    (hne : U.map c₀ ≠ ⊥) (w : ι) (d : Module.End ℂ V) (hd : d ∈ drop C v w) :
    Kills d (U.map c₀) ↔ Kills d U := by
  have hU : U ≠ ⊥ := by
    rintro rfl
    exact hne (Submodule.map_bot _)
  by_cases h : w = v
  · rw [h] at hd
    obtain ⟨r, rfl⟩ := drop_self C v hd
    rw [kills_scalar hne, kills_scalar hU]
  · rw [drop_ne C v h] at hd
    constructor
    · intro hk
      have hsp := orbSpan_eq hS hC hI (map_le_self hS hc₀) (stab_drop hS hC hc₀) hne
      have key : orbSpan C v (U.map c₀) ≤ LinearMap.ker d := by
        rw [orbSpan, Submodule.span_le]
        rintro _ ⟨a, ha, y, hy, rfl⟩
        rw [SetLike.mem_coe, LinearMap.mem_ker]
        rw [hC w v h d hd a ha y (map_le_self hS hc₀ hy), hk y hy, map_zero]
      intro x hx
      rw [← hsp] at hx
      exact key hx
    · intro hk x hx
      exact hk x (map_le_self hS hc₀ hx)

theorem glue (C : ι → Subalgebra ℂ (Module.End ℂ V)) (v : ι) {U₁ U₂ : Submodule ℂ V}
    {c₀ : Module.End ℂ V} (hc₀ : c₀ ∈ C v)
    (hS₁ : Stab C U₁) (hS₂ : Stab C U₂) (hC₁ : Comm C U₁) (hC₂ : Comm C U₂)
    (hI₁ : Irr C U₁) (hI₂ : Irr C U₂) (hk₁ : ¬ Kills c₀ U₁) (hk₂ : ¬ Kills c₀ U₂)
    (hsc : ∀ a ∈ C v, ∃ μ : ℂ, (∀ x ∈ U₁, c₀ (a (c₀ x)) = μ • c₀ x) ∧
      (∀ x ∈ U₂, c₀ (a (c₀ x)) = μ • c₀ x))
    {X' : Submodule ℂ (V × V)} (hX' : Graph (drop C v) (U₁.map c₀) (U₂.map c₀) X') :
    ∃ X, Graph C U₁ U₂ X := by
  obtain ⟨hX'0, hX'U, hX'S, hX'l, hX'r⟩ := hX'
  set S : Set (V × V) := {z | ∃ a ∈ C v, ∃ z' ∈ X', (a z'.1, a z'.2) = z} with hSdef
  have hsub : X' ≤ Submodule.span ℂ S := fun z hz =>
    Submodule.subset_span ⟨1, one_mem _, z, hz, by simp⟩
  have hU : Submodule.span ℂ S ≤ U₁.prod U₂ := by
    rw [Submodule.span_le]
    rintro _ ⟨a, ha, z', hz', rfl⟩
    obtain ⟨h1, h2⟩ := hX'U z' hz'
    exact ⟨hS₁ v a ha _ (map_le_self hS₁ hc₀ h1), hS₂ v a ha _ (map_le_self hS₂ hc₀ h2)⟩
  have hst : ∀ w, ∀ c ∈ C w, ∀ z ∈ Submodule.span ℂ S, (c z.1, c z.2) ∈ Submodule.span ℂ S := by
    intro w c hc z hz
    have key : Submodule.span ℂ S ≤ (Submodule.span ℂ S).comap (c.prodMap c) := by
      rw [Submodule.span_le]
      rintro _ ⟨a, ha, z', hz', rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.prodMap_apply]
      by_cases h : w = v
      · rw [h] at hc
        exact Submodule.subset_span ⟨c * a, mul_mem hc ha, z', hz', rfl⟩
      · obtain ⟨h1, h2⟩ := hX'U z' hz'
        have hc' : c ∈ drop C v w := by rw [drop_ne C v h]; exact hc
        rw [hC₁ w v h c hc a ha _ (map_le_self hS₁ hc₀ h1),
          hC₂ w v h c hc a ha _ (map_le_self hS₂ hc₀ h2)]
        exact Submodule.subset_span ⟨a, ha, (c z'.1, c z'.2), hX'S w c hc' z' hz', rfl⟩
    have := key hz
    rwa [Submodule.mem_comap, LinearMap.prodMap_apply] at this
  have hc₀X : ∀ z ∈ Submodule.span ℂ S, (c₀ z.1, c₀ z.2) ∈ X' := by
    intro z hz
    have key : Submodule.span ℂ S ≤ X'.comap (c₀.prodMap c₀) := by
      rw [Submodule.span_le]
      rintro _ ⟨a, ha, z', hz', rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.prodMap_apply]
      obtain ⟨h1, h2⟩ := hX'U z' hz'
      obtain ⟨x₁, hx₁, e₁⟩ := Submodule.mem_map.mp h1
      obtain ⟨x₂, hx₂, e₂⟩ := Submodule.mem_map.mp h2
      obtain ⟨μ, hμ₁, hμ₂⟩ := hsc a ha
      have e : (c₀ (a z'.1), c₀ (a z'.2)) = μ • z' := by
        ext
        · simp only [Prod.smul_fst]
          rw [← e₁, hμ₁ x₁ hx₁]
        · simp only [Prod.smul_snd]
          rw [← e₂, hμ₂ x₂ hx₂]
      rw [e]
      exact X'.smul_mem μ hz'
    have := key hz
    rwa [Submodule.mem_comap, LinearMap.prodMap_apply] at this
  refine ⟨Submodule.span ℂ S, ?_, fun z hz => Submodule.mem_prod.mp (hU hz), hst, ?_, ?_⟩
  · intro h
    apply hX'0
    rw [eq_bot_iff, ← h]
    exact hsub
  · set K := (Submodule.span ℂ S).comap (LinearMap.inr ℂ V V) with hK
    have hKU : K ≤ U₂ := fun u hu => (Submodule.mem_prod.mp (hU hu)).2
    have hKS : Stab C K := by
      intro w c hc u hu
      have h0 := hst w c hc _ hu
      simp only [LinearMap.inr_apply, map_zero] at h0
      simpa [hK] using h0
    rcases hI₂ K hKU hKS with h | h
    · intro u hu
      have hu' : u ∈ K := by simpa [hK] using hu
      rw [h] at hu'
      exact (Submodule.mem_bot ℂ).mp hu'
    · exfalso
      apply hk₂
      intro u hu
      rw [← h] at hu
      have h0 := hc₀X _ hu
      simp only [LinearMap.inr_apply, map_zero] at h0
      exact hX'l _ h0
  · set K := (Submodule.span ℂ S).comap (LinearMap.inl ℂ V V) with hK
    have hKU : K ≤ U₁ := fun u hu => (Submodule.mem_prod.mp (hU hu)).1
    have hKS : Stab C K := by
      intro w c hc u hu
      have h0 := hst w c hc _ hu
      simp only [LinearMap.inl_apply, map_zero] at h0
      simpa [hK] using h0
    rcases hI₁ K hKU hKS with h | h
    · intro u hu
      have hu' : u ∈ K := by simpa [hK] using hu
      rw [h] at hu'
      exact (Submodule.mem_bot ℂ).mp hu'
    · exfalso
      apply hk₁
      intro u hu
      rw [← h] at hu
      have h0 := hc₀X _ hu
      simp only [LinearMap.inl_apply, map_zero] at h0
      exact hX'r _ h0

theorem main_ind (n : ℕ) : ∀ (C : ι → Subalgebra ℂ (Module.End ℂ V)) (U₁ U₂ : Submodule ℂ V),
    FiniteDimensional ℂ U₁ → finrank ℂ U₁ = n → U₁ ≠ ⊥ → U₂ ≠ ⊥ →
    Stab C U₁ → Stab C U₂ → Comm C U₁ → Comm C U₂ →
    (∀ v, ∀ c ∈ C v, Kills c U₁ ↔ Kills c U₂) → Irr C U₁ → Irr C U₂ →
    ∃ X, Graph C U₁ U₂ X := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro C U₁ U₂ hfd hn h₁ h₂ hS₁ hS₂ hC₁ hC₂ hK hI₁ hI₂
  classical
  haveI := hfd
  by_cases hB : ∀ v, ∀ a ∈ C v, ∃ μ : ℂ, ∀ x ∈ U₁, a x = μ • x
  · apply graph_of_scalars C U₁ U₂ h₁ h₂
    intro v a ha
    obtain ⟨μ, hμ⟩ := hB v a ha
    refine ⟨μ, hμ, ?_⟩
    have hm : a - algebraMap ℂ (Module.End ℂ V) μ ∈ C v :=
      sub_mem ha (Subalgebra.algebraMap_mem _ μ)
    have hk : Kills (a - algebraMap ℂ (Module.End ℂ V) μ) U₁ := by
      intro x hx
      simp [hμ x hx]
    intro x hx
    have := (hK v _ hm).mp hk x hx
    simpa [sub_eq_zero] using this
  push_neg at hB
  obtain ⟨v₁, a₁, ha₁, hna⟩ := hB
  obtain ⟨μ₁, hμ₁⟩ := eig_drop U₁ h₁ a₁ (fun x hx => hS₁ v₁ a₁ ha₁ x hx)
  have he₁m : a₁ - algebraMap ℂ (Module.End ℂ V) μ₁ ∈ C v₁ :=
    sub_mem ha₁ (Subalgebra.algebraMap_mem _ μ₁)
  have he₁ne : U₁.map (a₁ - algebraMap ℂ (Module.End ℂ V) μ₁) ≠ ⊥ := by
    intro h
    obtain ⟨x, hx, hne⟩ := hna μ₁
    apply hne
    have := (kills_iff_map _ U₁).mpr h x hx
    simpa [sub_eq_zero] using this
  have hex : ∃ m, ∃ v, ∃ c ∈ C v, U₁.map c ≠ ⊥ ∧ finrank ℂ (U₁.map c) = m :=
    ⟨_, v₁, _, he₁m, he₁ne, rfl⟩
  obtain ⟨v, c₀, hc₀, hc₀ne, hc₀fr⟩ := Nat.find_spec hex
  have hmin : ∀ w, ∀ c ∈ C w, U₁.map c ≠ ⊥ → Nat.find hex ≤ finrank ℂ (U₁.map c) :=
    fun w c hc hne => Nat.find_min' hex ⟨w, c, hc, hne, rfl⟩
  have hlt : finrank ℂ (U₁.map c₀) < n := by
    have := hmin v₁ _ he₁m he₁ne
    omega
  have hsc : ∀ a ∈ C v, ∃ μ : ℂ, (∀ x ∈ U₁, c₀ (a (c₀ x)) = μ • c₀ x) ∧
      (∀ x ∈ U₂, c₀ (a (c₀ x)) = μ • c₀ x) := by
    intro a ha
    have hg : ∀ x ∈ U₁.map c₀, (c₀ * a) x ∈ U₁.map c₀ := by
      rintro _ ⟨y, hy, rfl⟩
      exact Submodule.mem_map_of_mem (hS₁ v a ha _ (hS₁ v c₀ hc₀ y hy))
    obtain ⟨μ, hμ⟩ := eig_drop (U₁.map c₀) hc₀ne (c₀ * a) hg
    have hem : (c₀ * a - algebraMap ℂ (Module.End ℂ V) μ) * c₀ ∈ C v :=
      mul_mem (sub_mem (mul_mem hc₀ ha) (Subalgebra.algebraMap_mem _ μ)) hc₀
    have hmap : U₁.map ((c₀ * a - algebraMap ℂ (Module.End ℂ V) μ) * c₀) =
        (U₁.map c₀).map (c₀ * a - algebraMap ℂ (Module.End ℂ V) μ) := by
      rw [Module.End.mul_eq_comp, Submodule.map_comp]
    have hk : Kills ((c₀ * a - algebraMap ℂ (Module.End ℂ V) μ) * c₀) U₁ := by
      rw [kills_iff_map]
      by_contra hne
      have := hmin v _ hem hne
      rw [hmap] at this
      omega
    refine ⟨μ, fun x hx => ?_, fun x hx => ?_⟩
    · have := hk x hx
      simpa [sub_eq_zero] using this
    · have := (hK v _ hem).mp hk x hx
      simpa [sub_eq_zero] using this
  have hk₁ : ¬ Kills c₀ U₁ := fun h => hc₀ne ((kills_iff_map c₀ U₁).mp h)
  have hk₂ : ¬ Kills c₀ U₂ := fun h => hk₁ ((hK v c₀ hc₀).mpr h)
  have h₂' : U₂.map c₀ ≠ ⊥ := fun h => hk₂ ((kills_iff_map c₀ U₂).mpr h)
  have hsc₁ : ∀ a ∈ C v, ∃ μ : ℂ, ∀ x ∈ U₁, c₀ (a (c₀ x)) = μ • c₀ x :=
    fun a ha => (hsc a ha).imp fun _ h => h.1
  have hsc₂ : ∀ a ∈ C v, ∃ μ : ℂ, ∀ x ∈ U₂, c₀ (a (c₀ x)) = μ • c₀ x :=
    fun a ha => (hsc a ha).imp fun _ h => h.2
  obtain ⟨X', hX'⟩ := ih _ hlt (drop C v) (U₁.map c₀) (U₂.map c₀) inferInstance rfl hc₀ne h₂'
    (stab_drop hS₁ hC₁ hc₀) (stab_drop hS₂ hC₂ hc₀)
    (comm_drop C v hC₁ (map_le_self hS₁ hc₀)) (comm_drop C v hC₂ (map_le_self hS₂ hc₀))
    (fun w d hd => by
      rw [kills_drop hS₁ hC₁ hI₁ hc₀ hc₀ne w d hd, kills_drop hS₂ hC₂ hI₂ hc₀ h₂' w d hd]
      exact hK w d (drop_le C v w hd))
    (irr_drop hS₁ hC₁ hI₁ hc₀ hsc₁) (irr_drop hS₂ hC₂ hI₂ hc₀ hsc₂)
  exact glue C v hc₀ hS₁ hS₂ hC₁ hC₂ hI₁ hI₂ hk₁ hk₂ hsc hX'

theorem stable_graph : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ι : Type) (C : ι → Subalgebra ℂ (Module.End ℂ V)) (U₁ U₂ : Submodule ℂ V), FiniteDimensional ℂ U₁ → U₁ ≠ ⊥ → U₂ ≠ ⊥ → (∀ v, ∀ c ∈ C v, ∀ x ∈ U₁, c x ∈ U₁) → (∀ v, ∀ c ∈ C v, ∀ x ∈ U₂, c x ∈ U₂) → (∀ v w, v ≠ w → ∀ c ∈ C v, ∀ d ∈ C w, (∀ x ∈ U₁, c (d x) = d (c x)) ∧ (∀ x ∈ U₂, c (d x) = d (c x))) → (∀ v, ∀ c ∈ C v, (∀ x ∈ U₁, c x = 0) ↔ (∀ x ∈ U₂, c x = 0)) → (∀ Y ≤ U₁, (∀ v, ∀ c ∈ C v, ∀ x ∈ Y, c x ∈ Y) → Y = ⊥ ∨ Y = U₁) → (∀ Y ≤ U₂, (∀ v, ∀ c ∈ C v, ∀ x ∈ Y, c x ∈ Y) → Y = ⊥ ∨ Y = U₂) → ∃ X : Submodule ℂ (V × V), X ≠ ⊥ ∧ (∀ z ∈ X, z.1 ∈ U₁ ∧ z.2 ∈ U₂) ∧ (∀ v, ∀ c ∈ C v, ∀ z ∈ X, (c z.1, c z.2) ∈ X) ∧ (∀ u, ((0 : V), u) ∈ X → u = 0) ∧ (∀ u, (u, (0 : V)) ∈ X → u = 0) := by
  intro V _ _ ι C U₁ U₂ hfd h₁ h₂ hS₁ hS₂ hCm hK hI₁ hI₂
  exact main_ind (finrank ℂ U₁) C U₁ U₂ hfd rfl h₁ h₂ hS₁ hS₂
    (fun v w h c hc d hd x hx => (hCm v w h c hc d hd).1 x hx)
    (fun v w h c hc d hd x hx => (hCm v w h c hc d hd).2 x hx) hK hI₁ hI₂

end GlobalTheory.CommDet
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsStableGraphOfEqualAnnihilatorsStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_stable_graph_of_equal_annihilators : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ι : Type) (C : ι → Subalgebra ℂ (Module.End ℂ V)) (U₁ U₂ : Submodule ℂ V), FiniteDimensional ℂ U₁ → U₁ ≠ ⊥ → U₂ ≠ ⊥ → (∀ v, ∀ c ∈ C v, ∀ x ∈ U₁, c x ∈ U₁) → (∀ v, ∀ c ∈ C v, ∀ x ∈ U₂, c x ∈ U₂) → (∀ v w, v ≠ w → ∀ c ∈ C v, ∀ d ∈ C w, (∀ x ∈ U₁, c (d x) = d (c x)) ∧ (∀ x ∈ U₂, c (d x) = d (c x))) → (∀ v, ∀ c ∈ C v, (∀ x ∈ U₁, c x = 0) ↔ (∀ x ∈ U₂, c x = 0)) → (∀ Y ≤ U₁, (∀ v, ∀ c ∈ C v, ∀ x ∈ Y, c x ∈ Y) → Y = ⊥ ∨ Y = U₁) → (∀ Y ≤ U₂, (∀ v, ∀ c ∈ C v, ∀ x ∈ Y, c x ∈ Y) → Y = ⊥ ∨ Y = U₂) → ∃ X : Submodule ℂ (V × V), X ≠ ⊥ ∧ (∀ z ∈ X, z.1 ∈ U₁ ∧ z.2 ∈ U₂) ∧ (∀ v, ∀ c ∈ C v, ∀ z ∈ X, (c z.1, c z.2) ∈ X) ∧ (∀ u, ((0 : V), u) ∈ X → u = 0) ∧ (∀ u, (u, (0 : V)) ∈ X → u = 0) := by
  first | exact @GlobalTheory.CommDet.stable_graph | exact GlobalTheory.CommDet.stable_graph | (intros; apply GlobalTheory.CommDet.stable_graph <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AlgebraicModularFormsHeckeModulesIsoAllPlaces
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.HeckeIso

section Abstract

variable {G V ι : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : G →* Module.End ℂ V} {Gv Gc : ι → Subgroup G}
  {J : Subgroup G}

theorem graph_of_local' (H : PlaceSys Gv Gc J) (horb : ∀ x, ((fun k => ρ k x) '' (J : Set G)).Finite)
    {S₁ S₂ : Submodule ℂ V} (h₁ : Irr ρ S₁) (h₂ : Irr ρ S₂) (n₁ : fixIn ρ J S₁ ≠ ⊥) (n₂ : fixIn ρ J S₂ ≠ ⊥)
    (hfd : FiniteDimensional ℂ (fixIn ρ J S₁)) (hloc : ∀ v, ∃ X, IsGraph ρ (Gv v) S₁ S₂ X) :
    ∃ W, IsGraph ρ ⊤ S₁ S₂ W := by
  obtain ⟨X, hX0, hXm, hX, i₁, i₂⟩ := GlobalTheory.T.exists_stable_graph_of_equal_annihilators V ι (fun v => locAlg ρ (Gv v) (Gc v) ⊓ fixAlg ρ J)
    (fixIn ρ J S₁) (fixIn ρ J S₂) hfd n₁ n₂
    (fun v c hc x hx => ⟨locAlg_mem hc.1 h₁.stab hx.1, hc.2 x hx.2⟩)
    (fun v c hc x hx => ⟨locAlg_mem hc.1 h₂.stab hx.1, hc.2 x hx.2⟩)
    (fun v w hvw c hc d hd => ⟨fun x _ => locAlg_comm (H.le v w hvw) hc.1 hd.1 x,
      fun x _ => locAlg_comm (H.le v w hvw) hc.1 hd.1 x⟩)
    (fun v c hc => by
      obtain ⟨P, hP⟩ := exists_avg ρ (Gv v ⊓ J) fun x => (horb x).subset (Set.image_mono fun k hk => hk.2)
      obtain ⟨Q, hQ⟩ := exists_avg ρ (Gc v ⊓ J) fun x => (horb x).subset (Set.image_mono fun k hk => hk.2)
      obtain ⟨X, hX⟩ := hloc v
      exact ⟨ann_transfer (H.comm v) (H.dec v) (H.decJ v) hP hQ h₁ h₂ n₁ hX hc.1,
        ann_transfer (H.comm v) (H.dec v) (H.decJ v) hP hQ h₂ h₁ n₂ hX.swap hc.1⟩)
    (fun Y hY hst => fixIn_simple H horb h₁ Y hY hst) (fun Y hY hst => fixIn_simple H horb h₂ Y hY hst)
  exact graph_of_fixed_graph H horb h₁ h₂ n₁ n₂ X hX0 hXm hX i₁ i₂

theorem graph_of_local (H : PlaceSys Gv Gc J) {S₁ S₂ : Submodule ℂ V} (h₁ : Irr ρ S₁) (h₂ : Irr ρ S₂)
    (horb : ∀ x ∈ S₁ ⊔ S₂, ((fun k => ρ k x) '' (J : Set G)).Finite)
    (n₁ : fixIn ρ J S₁ ≠ ⊥) (n₂ : fixIn ρ J S₂ ≠ ⊥)
    (hfd : FiniteDimensional ℂ (fixIn ρ J S₁)) (hloc : ∀ v, ∃ X, IsGraph ρ (Gv v) S₁ S₂ X) :
    ∃ W, IsGraph ρ ⊤ S₁ S₂ W := by
  have hne : ∀ S ≤ S₁ ⊔ S₂, fixIn ρ J S ≠ ⊥ →
      fixIn (res ρ _ (sup_stab h₁ h₂)) J (S.comap (S₁ ⊔ S₂).subtype) ≠ ⊥ := by
    intro S hS h
    obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
    exact (Submodule.ne_bot_iff _).2 ⟨⟨f, hS hf.1⟩, ⟨hf.1, fun k hk => Subtype.ext (hf.2 k hk)⟩,
      fun e => hf0 (congrArg Subtype.val e)⟩
  obtain ⟨W, hW⟩ := graph_of_local' (ρ := res ρ _ (sup_stab h₁ h₂)) H (orbit_res horb) (h₁.res le_sup_left)
    (h₂.res le_sup_right) (hne _ le_sup_left n₁) (hne _ le_sup_right n₂)
    (FiniteDimensional.of_injective
      (((S₁ ⊔ S₂).subtype.comp (fixIn (res ρ _ (sup_stab h₁ h₂)) J (S₁.comap (S₁ ⊔ S₂).subtype)).subtype).codRestrict
        (fixIn ρ J S₁) (fun f => ⟨f.2.1, fun k hk => congrArg Subtype.val (f.2.2 k hk)⟩))
      (fun a b e => by
        have e' := congrArg Subtype.val e
        exact Subtype.ext (Subtype.ext e')))
    (fun v => by
      obtain ⟨X, hX⟩ := hloc v
      exact ⟨_, hX.res le_sup_left le_sup_right⟩)
  exact ⟨_, hW.of_res⟩

end Abstract

variable (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)

def rtRep (W : Type) [AddCommGroup W] [Module ℂ W] : GAf L n →* Module.End ℂ (GAf L n → W) where
  toFun g := NG.rt L n g
  map_one' := LinearMap.ext fun φ => funext fun x => by
    show φ (x * 1) = φ x
    rw [mul_one]
  map_mul' g g' := LinearMap.ext fun φ => funext fun x => by
    show φ (x * (g * g')) = φ (x * g * g')
    rw [mul_assoc]

def Gaway (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : Subgroup (GAf L n) where
  carrier := {x | TrivOutside {v}ᶜ x}
  mul_mem' := fun hx hy => GlobalTheory.SatInd.CosetFin.trivOutside_mul hx hy
  one_mem' := GlobalTheory.InertSph.trivOutside_one _
  inv_mem' := fun hx => GlobalTheory.SatInd.CosetFin.trivOutside_inv hx

theorem placeSys {N : ℕ} (hN : 0 < N) :
    PlaceSys (GlobalTheory.InertSph.Gv L n) (Gaway L n) (GlobalTheory.IsotOrth.congSub L n N) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact fun v x hx y hy => (GlobalTheory.InertSph.commute_of_trivOutside v x y hx hy).eq
  · intro v w hvw x hx u hu
    apply hx u
    have : u = v := by simpa using hu
    subst this
    simpa using hvw
  · intro v g
    obtain ⟨x, y, hx, hy, e⟩ := GlobalTheory.T.finiteAdelicUnitary_eq_mul_trivOutside_place_and_at_place L n v g
    exact ⟨x, hx, y, hy, e⟩
  · intro v k hk
    obtain ⟨x, y, hx, hy, cx, cy, e⟩ := GlobalTheory.T.principalCongruence_split_trivOutside_and_at_place L n N v k hk
    exact ⟨x, ⟨hx, cx⟩, y, ⟨hy, cy⟩, e⟩
  · exact fun p h1 h2 => GlobalTheory.T.finiteAdelicGL_induction_over_places L n N hN p h1 (fun v x y hx hy => h2 v x hx y hy)

variable {L n}

theorem irr_of {a : NG.AlgWt L n} {S : Submodule ℂ (GAf L n → a.W)} (h : NG.IsIrrRep a.ρ S) :
    Irr (rtRep L n a.W) S :=
  ⟨h.1.stable, fun T hT hst => h.2.2 T ⟨hT.trans h.1.le, hst⟩ hT⟩

theorem orbit_fin {a : NG.AlgWt L n} {S₁ S₂ : Submodule ℂ (GAf L n → a.W)} (h₁ : NG.IsIrrRep a.ρ S₁)
    (h₂ : NG.IsIrrRep a.ρ S₂) {K : Subgroup (GAf L n)} (hK : K ≤ Umax L n) :
    ∀ x ∈ S₁ ⊔ S₂, ((fun k => rtRep L n a.W k x) '' (K : Set (GAf L n))).Finite := by
  intro x hx
  obtain ⟨N, hN, hx⟩ := (sup_le h₁.1.le h₂.1.le hx).2
  exact (GlobalTheory.IsotOrth.orbit_finite (rtRep L n a.W) hN x fun κ hκ => funext fun g => hx κ hκ g).subset
    (Set.image_mono hK)

theorem main : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S₁ S₂ : Submodule ℂ (GAf L n → a.W)), NG.IsIrrRep a.ρ S₁ → NG.IsIrrRep a.ρ S₂ → (∀ s : SplitPlace L, ∃ σ₁ σ₂ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L)), IsLocS S₁ s σ₁ ∧ IsLocS S₂ s σ₂ ∧ Nonempty (σ₁.ρ.Equiv σ₂.ρ)) → (∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)), (∀ s : SplitPlace L, s.v ≠ v) → ∃ (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ), NG.OverPl w v ∧ (∃ f ∈ S₁, f ≠ 0 ∧ ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ f = f) ∧ (∃ f ∈ S₂, f ≠ 0 ∧ ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ f = f) ∧ ∀ U : Subgroup (GAf L n), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) → ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n), (∀ f ∈ S₁, (∀ κ ∈ U, NG.rt L n κ f = f) → heckeFunI L n U Dv h f = Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield L) v) h α • f) ∧ (∀ f ∈ S₂, (∀ κ ∈ U, NG.rt L n κ f = f) → heckeFunI L n U Dv h f = Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield L) v) h α • f)) → ∀ N : ℕ, 0 < N → (∃ f ∈ S₁, (∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) ∧ f ≠ 0) → ∃ φ : (GAf L n → a.W) →ₗ[ℂ] (GAf L n → a.W), (∀ f ∈ S₁, (∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) → φ f ∈ S₂ ∧ ∀ κ, NG.Cong L n N κ → NG.rt L n κ (φ f) = φ f) ∧ (∃ f ∈ S₁, (∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) ∧ φ f ≠ 0) ∧ (∀ (g : GAf L n) (f : GAf L n → a.W), f ∈ S₁ → (∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) → φ (NG.heckeD (GlobalTheory.IsotOrth.congSub L n N) {x | ∃ u ∈ GlobalTheory.IsotOrth.congSub L n N, ∃ u' ∈ GlobalTheory.IsotOrth.congSub L n N, x = u * g * u'} f) = NG.heckeD (GlobalTheory.IsotOrth.congSub L n N) {x | ∃ u ∈ GlobalTheory.IsotOrth.congSub L n N, ∃ u' ∈ GlobalTheory.IsotOrth.congSub L n N, x = u * g * u'} (φ f)) := by
  intro L _ _ _ n a S₁ S₂ h₁ h₂ hsplit hinert N hN hf
  refine GlobalTheory.T.exists_doubleCosetCommuting_map_principalCongruence L n a S₁ S₂ h₁ ?_ N hN hf
  obtain ⟨g₁, hg₁, hg₁0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h₁.2.1
  obtain ⟨g₂, hg₂, hg₂0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h₂.2.1
  obtain ⟨M₁, hM₁, e₁⟩ := (h₁.1.le hg₁).2
  obtain ⟨M₂, hM₂, e₂⟩ := (h₂.1.le hg₂).2
  have hM : 0 < M₁ * M₂ := Nat.mul_pos hM₁ hM₂
  have H := placeSys L n hM
  haveI : FiniteDimensional ℂ a.W := a.alg.1
  obtain ⟨W, hW⟩ := graph_of_local H (irr_of h₁) (irr_of h₂) (orbit_fin h₁ h₂ fun k hk => hk.1)
    ((Submodule.ne_bot_iff _).2 ⟨g₁, ⟨hg₁, fun k hk => funext fun g => e₁ k (NG.Cong.of_mul_left L n hk) g⟩, hg₁0⟩)
    ((Submodule.ne_bot_iff _).2 ⟨g₂, ⟨hg₂, fun k hk => funext fun g => e₂ k (NG.Cong.of_mul_right L n hk) g⟩, hg₂0⟩)
    (by
      have := GlobalTheory.AlgFormsFin.fixedForms_finite L n a.ρ (GlobalTheory.T.finite_doubleCosets_definiteUnitary_maximalLevel L n) hM
      refine Submodule.finiteDimensional_of_le (S₂ := GlobalTheory.AlgFormsFin.fixedForms L n a.ρ (M₁ * M₂)) ?_
      rintro f ⟨hfS, hfU⟩
      exact ⟨(h₁.1.le hfS).1, fun κ hκ g => congrFun (hfU κ hκ) g⟩)
    (fun v => by
      by_cases hv : ∃ s : SplitPlace L, s.v = v
      · obtain ⟨s, rfl⟩ := hv
        obtain ⟨σ₁, σ₂, l₁, l₂, he⟩ := hsplit s
        obtain ⟨X, x1, x2, x3, x4, x5⟩ := GlobalTheory.T.exists_stable_graph_of_iso_splitPlace_components L n a S₁ S₂ s σ₁ σ₂ l₁ l₂ he
        exact ⟨X, x1, x2, x3, x4, x5⟩
      · obtain ⟨w, Dv, α, -, ⟨f₁, hf₁, n₁, k₁⟩, ⟨f₂, hf₂, n₂, k₂⟩, hH⟩ := hinert v fun s hs => hv ⟨s, hs⟩
        refine graph_of_hecke (K := GlobalTheory.InertSph.Kv L n v) (H.comm v) (H.dec v) inf_le_right (irr_of h₁) (irr_of h₂)
          (orbit_fin h₁ h₂ inf_le_left) hf₁ hf₂ n₁ n₂ (fun k hk => k₁ k hk.1 hk.2) (fun k hk => k₂ k hk.1 hk.2)
          fun x hx => ?_
        obtain ⟨R, h, hR, hh, hA⟩ := GlobalTheory.T.inertDoubleCosetOperator_eq_inertHeckeOperator L n v w Dv (GlobalTheory.T.inertDatum_local_mem_unitaryGroup_antidiagonal L n v w Dv) (GlobalTheory.T.inertDatum_local_stdLatticeStabilizer_mem_maxCompact L n v w Dv)
          (GlobalTheory.T.exists_trivOutside_inertDatum_local_eq L n v w Dv) (GlobalTheory.T.inertDatum_local_injective_on_trivOutside L n v w Dv) x hx
        have hK : ∀ κ : GAf L n, κ ∈ Umax L n → TrivOutside {v} κ → ∃ hκ : Dv.loc κ ∈ Formalism.UG.GU Dv.σw n,
            (⟨Dv.loc κ, hκ⟩ : Formalism.UG.GU Dv.σw n) ∈ Formalism.UG.KU Dv.σw n :=
          fun κ hκ _ => ⟨GlobalTheory.T.inertDatum_local_mem_unitaryGroup_antidiagonal L n v w Dv κ, GlobalTheory.T.inertDatum_local_stdLatticeStabilizer_mem_maxCompact L n v w Dv κ hκ _⟩
        have hKv : ∀ κ : GAf L n, TrivOutside {v} κ → (κ ∈ GlobalTheory.InertSph.Kv L n v ↔ κ ∈ Umax L n) :=
          fun κ hκ => ⟨fun h => h.1, fun h => ⟨h, hκ⟩⟩
        obtain ⟨γ, ⟨hγ, -⟩, -⟩ := hR.2 x ⟨1, one_mem _, 1, one_mem _, by simp⟩
        refine ⟨R, Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield L) v) h α, ⟨γ, hγ⟩, hR.1, ?_, ?_⟩
        · refine (hA a.W f₁ k₁).trans ?_
          rw [GlobalTheory.T.inertHeckeOperator_level_independent L n v w Dv hK (Umax L n) _ (fun _ _ => Iff.rfl) hKv a.W h hh.1 f₁ k₁]
          exact (hH _ hKv h hh).1 f₁ hf₁ fun k hk => k₁ k hk.1 hk.2
        · refine (hA a.W f₂ k₂).trans ?_
          rw [GlobalTheory.T.inertHeckeOperator_level_independent L n v w Dv hK (Umax L n) _ (fun _ _ => Iff.rfl) hKv a.W h hh.1 f₂ k₂]
          exact (hH _ hKv h hh).2 f₂ hf₂ fun k hk => k₂ k hk.1 hk.2)
  exact GlobalTheory.T.equivariant_iso_of_translationStable_graph L n a.ρ a.ρ S₁ S₂ W h₁ h₂ hW.mem (fun h w hw => hW.stab h trivial w hw) hW.inj₁ hW.inj₂ hW.ne

end GlobalTheory.HeckeIso
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AlgebraicModularFormsHeckeModulesIsoAllPlacesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraicModularForms_heckeModules_iso_all_places : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S₁ S₂ : Submodule ℂ (GAf L n → a.W)), NG.IsIrrRep a.ρ S₁ → NG.IsIrrRep a.ρ S₂ → (∀ s : SplitPlace L, ∃ σ₁ σ₂ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L)), IsLocS S₁ s σ₁ ∧ IsLocS S₂ s σ₂ ∧ Nonempty (σ₁.ρ.Equiv σ₂.ρ)) → (∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)), (∀ s : SplitPlace L, s.v ≠ v) → ∃ (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ), NG.OverPl w v ∧ (∃ f ∈ S₁, f ≠ 0 ∧ ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ f = f) ∧ (∃ f ∈ S₂, f ≠ 0 ∧ ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ f = f) ∧ ∀ U : Subgroup (GAf L n), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) → ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n), (∀ f ∈ S₁, (∀ κ ∈ U, NG.rt L n κ f = f) → heckeFunI L n U Dv h f = Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield L) v) h α • f) ∧ (∀ f ∈ S₂, (∀ κ ∈ U, NG.rt L n κ f = f) → heckeFunI L n U Dv h f = Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield L) v) h α • f)) → ∀ N : ℕ, 0 < N → (∃ f ∈ S₁, (∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) ∧ f ≠ 0) → ∃ φ : (GAf L n → a.W) →ₗ[ℂ] (GAf L n → a.W), (∀ f ∈ S₁, (∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) → φ f ∈ S₂ ∧ ∀ κ, NG.Cong L n N κ → NG.rt L n κ (φ f) = φ f) ∧ (∃ f ∈ S₁, (∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) ∧ φ f ≠ 0) ∧ (∀ (g : GAf L n) (f : GAf L n → a.W), f ∈ S₁ → (∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) → φ (NG.heckeD (GlobalTheory.IsotOrth.congSub L n N) {x | ∃ u ∈ GlobalTheory.IsotOrth.congSub L n N, ∃ u' ∈ GlobalTheory.IsotOrth.congSub L n N, x = u * g * u'} f) = NG.heckeD (GlobalTheory.IsotOrth.congSub L n N) {x | ∃ u ∈ GlobalTheory.IsotOrth.congSub L n N, ∃ u' ∈ GlobalTheory.IsotOrth.congSub L n N, x = u * g * u'} (φ f)) := by
  first | exact @GlobalTheory.HeckeIso.main | exact GlobalTheory.HeckeIso.main | (intros; apply GlobalTheory.HeckeIso.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AlgebraicModularFormsStrongMultiplicityOne
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.GlobDet

theorem main : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S₁ S₂ : Submodule ℂ (GAf L n → a.W)) (h₁ : NG.IsIrrRep a.ρ S₁) (h₂ : NG.IsIrrRep a.ρ S₂), (∀ s : SplitPlace L, ∃ σ₁ σ₂ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L)), IsLocS S₁ s σ₁ ∧ IsLocS S₂ s σ₂ ∧ Nonempty (σ₁.ρ.Equiv σ₂.ρ)) → (∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)), (∀ s : SplitPlace L, s.v ≠ v) → ∃ (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ), NG.OverPl w v ∧ NG.SatAt { a with S := S₁, irrS := h₁ } Dv α ∧ NG.SatAt { a with S := S₂, irrS := h₂ } Dv α) → NG.IsoRep S₁ S₂ := by
  intro L _ _ _ n a S₁ S₂ h₁ h₂ hsplit hinert
  obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h₁.2.1
  obtain ⟨N, hN, hNf⟩ := (h₁.1.le hf).2
  have hfix : ∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f := fun κ hκ => funext fun g => hNf κ hκ g
  obtain ⟨φ, hφ1, hφ2, hφ3⟩ := GlobalTheory.T.algebraicModularForms_heckeModules_iso_all_places L n a S₁ S₂ h₁ h₂ hsplit (fun v hv => by
    obtain ⟨w, Dv, α, hw, hs1, hs2⟩ := hinert v hv
    have k1 : ∃ f ∈ S₁, f ≠ 0 ∧ ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ f = f := by
      obtain ⟨f, hf, hf0, U, hfU, hU, -⟩ := hs1
      exact ⟨f, hf, hf0, fun κ hκ ht => hfU κ ((hU κ ht).2 hκ)⟩
    have k2 : ∃ f ∈ S₂, f ≠ 0 ∧ ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ f = f := by
      obtain ⟨f, hf, hf0, U, hfU, hU, -⟩ := hs2
      exact ⟨f, hf, hf0, fun κ hκ ht => hfU κ ((hU κ ht).2 hκ)⟩
    exact ⟨w, Dv, α, hw, k1, k2, fun U hU h hh =>
      ⟨fun f hf hfU => GlobalTheory.InertSph.satU_of_fixed L n a S₁ h₁ v w Dv α hw hs1 U hU f hf hfU h hh,
       fun f hf hfU => GlobalTheory.InertSph.satU_of_fixed L n a S₂ h₂ v w Dv α hw hs2 U hU f hf hfU h hh⟩⟩) N hN ⟨f, hf, hfix, hf0⟩
  exact GlobalTheory.HeckeRecon.recon L n a a S₁ S₂ h₁ h₂ N hN φ hφ1 hφ2 hφ3

end GlobalTheory.GlobDet
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AlgebraicModularFormsStrongMultiplicityOneStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraic_modular_forms_strong_multiplicity_one : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S₁ S₂ : Submodule ℂ (GAf L n → a.W)) (h₁ : NG.IsIrrRep a.ρ S₁) (h₂ : NG.IsIrrRep a.ρ S₂), (∀ s : SplitPlace L, ∃ σ₁ σ₂ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L)), IsLocS S₁ s σ₁ ∧ IsLocS S₂ s σ₂ ∧ Nonempty (σ₁.ρ.Equiv σ₂.ρ)) → (∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)), (∀ s : SplitPlace L, s.v ≠ v) → ∃ (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ), NG.OverPl w v ∧ NG.SatAt { a with S := S₁, irrS := h₁ } Dv α ∧ NG.SatAt { a with S := S₂, irrS := h₂ } Dv α) → NG.IsoRep S₁ S₂ := by
  first | exact @GlobalTheory.GlobDet.main | exact GlobalTheory.GlobDet.main | (intros; apply GlobalTheory.GlobDet.main <;> assumption)
end
