module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.GeometricLemma

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedInPrincipalSeries
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedInPrincipalSeries
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.Published GlobalTheory.SplitWeil
open GroundTheory.Automorphic.Spherical

namespace GlobalTheory.CompanionTheory.SphSupp.PsBridge

section SlopeTestRemainingChoices

open ValuativeRel Matrix GroundTheory.Automorphic GroundTheory.Automorphic.Iwasawa

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem valuation_uniformizerUnit :
    valuation k ((uniformizerUnit k : kˣ) : k) = ValuativeRel.uniformizer k := by
  apply le_antisymm
  · exact le_uniformizer_iff.2 (GLnLocal.valuation_uniformizer_lt_one k)
  · obtain ⟨ϖ, hϖ⟩ := valuation_surjective (ValuativeRel.uniformizer k)
    have hlt : valuation k ϖ < 1 := hϖ ▸ uniformizer_lt_one
    let y : 𝒪[k] := ⟨ϖ, hlt.le⟩
    have hy : y ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ 1 := by
      rw [pow_one, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one]
      exact hlt.ne
    have h := (GLnLocal.mem_maximalIdeal_pow_iff k).1 hy
    rw [pow_one] at h
    rw [← hϖ]
    exact h

theorem ord_zpow' (x : kˣ) (m : ℤ) : ord k (x ^ m) = m * ord k x := by
  let o : kˣ →* Multiplicative ℤ := MonoidHom.mk' (fun x => .ofAdd (ord k x)) fun x y => by
    rw [ord_mul, ofAdd_add]
  have h := map_zpow o x m
  have h2 : ord k (x ^ m) = m • ord k x := congrArg Multiplicative.toAdd h
  simpa using h2

variable {n : ℕ}

def diagUnit (p : blockUpper k n (id : Fin n → Fin n)) (i : Fin n) : kˣ :=
  Units.mk0 (((p : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i i)
    (apply_self_ne_zero_of_mem_borel k n p.2 i)

def toParab (p : blockUpper k n (id : Fin n → Fin n)) : parab k (points (Fin n)) :=
  ⟨p.1, fun _ _ h => p.2 h⟩

theorem det_leviProj (p : blockUpper k n (id : Fin n → Fin n)) (i : Fin n) :
    GeneralLinearGroup.det (GlobalTheory.SmGL.leviProj k (points (Fin n)) (toParab p) i) = diagUnit p i := by
  ext
  simp only [GeneralLinearGroup.val_det_apply, Matrix.det_unique]
  rfl

theorem deltaHalf_eq (p : blockUpper k n (id : Fin n → Fin n)) :
    (deltaHalf k (fun _ : Fin n => Unit) (GlobalTheory.SmGL.leviProj k (points (Fin n)) (toParab p)) : ℂ) =
      GroundTheory.Automorphic.Parabolic.sqrtModular k n id p := by
  rw [val_deltaHalf]
  change _ = ((NNReal.sqrt (MeasureTheory.Measure.modularCharacter p) : ℝ) : ℂ)
  congr 1
  rw [Real.coe_sqrt]
  congr 1
  rw [Measures.modularCharacter_borel, GlobalTheory.SmGL.modulus]
  push_cast
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [det_leviProj, modExp_fin _ (fun _ => by simp)]
  have h := Measures.modulus_units (diagUnit p i)
  have h2 : Measures.modulus (((p : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i i) =
      MeasureTheory.distribHaarChar k (diagUnit p i) := h
  rw [h2]
  rfl

theorem paramChar_leviProj (α : Fin n → ℂˣ) (p : blockUpper k n (id : Fin n → Fin n)) :
    paramChar k α (GroundTheory.Automorphic.Parabolic.leviProj k n id p) = ∏ i, ((α i ^ ord k (diagUnit p i) : ℂˣ) : ℂ) := by
  set l : Fin n → ℤ := fun i => ord k (diagUnit p i) with hl
  let e : Fin n → kˣ := fun i => diagUnit p i * uniformizerUnit k ^ (-l i)
  have he : ∀ i, valuation k (e i : k) = 1 := fun i => ord_eq_zero_iff.1 (by
    have h1 : ord k (uniformizerUnit k) = 1 := ord_eq_one valuation_uniformizerUnit
    have h2 : ord k (e i) = l i + ord k ((uniformizerUnit k) ^ (-l i)) := ord_mul k _ _
    rw [h2, ord_zpow', h1]
    ring)
  let u : GroundTheory.Automorphic.Parabolic.levi k n (id : Fin n → Fin n) := ⟨diagGL k n e, GroundTheory.Automorphic.Parabolic.diagGL_mem_levi e⟩
  have hdec : GroundTheory.Automorphic.Parabolic.leviProj k n id p = torusLevi k n l * u := by
    refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
    change ((GroundTheory.Automorphic.Parabolic.leviProj k n id p :
        GroundTheory.Automorphic.Parabolic.levi k n (id : Fin n → Fin n)) : GL (Fin n) k) i j =
      ((torusPow k n l : Matrix (Fin n) (Fin n) k) * (diagGL k n e : Matrix (Fin n) (Fin n) k)) i j
    rw [GroundTheory.Automorphic.Parabolic.leviProj_apply, coe_torusPow, coe_diagGL, diagonal_mul_diagonal,
      diagonal_apply]
    by_cases h : i = j
    · subst h
      have hϖ : (GLnLocal.uniformizer k : k) ≠ 0 := (uniformizerUnit k).ne_zero
      have he' : ((e i : kˣ) : k) = ((p : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i i *
          (GLnLocal.uniformizer k : k) ^ (-l i) := by
        simp only [e, Units.val_mul, Units.val_zpow_eq_zpow_val, coe_uniformizerUnit]
        rfl
      rw [if_pos rfl, if_pos rfl, he', mul_left_comm, ← zpow_add₀ hϖ, add_neg_cancel, zpow_zero,
        mul_one]
    · simp [h]
  have hu : (u : GL (Fin n) k) ∈ GLnLocal.integralGL k n := by
    have key : ∀ d : Fin n → kˣ, (∀ i, valuation k (d i : k) = 1) →
        ∀ i j, (diagGL k n d : GL (Fin n) k) i j ∈ 𝒪[k] := by
      intro d hd i j
      change (diagGL k n d : Matrix (Fin n) (Fin n) k) i j ∈ _
      rw [coe_diagGL, diagonal_apply]
      split_ifs
      · exact (hd i).le
      · exact (𝒪[k]).zero_mem
    rw [GLnLocal.mem_integralGL_iff]
    refine ⟨key e he, ?_⟩
    change ∀ i j, ((diagGL k n e)⁻¹ : GL (Fin n) k) i j ∈ 𝒪[k]
    rw [← map_inv]
    exact key _ fun i => by simp [he i]
  rw [hdec, map_mul, paramChar_torusLevi, isUnramified_paramChar α u hu, mul_one,
    monomialChar_apply]

theorem exists_open_fix {G V : Type} [Group G] [TopologicalSpace G]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (hρ : GlobalTheory.PRep.IsSmooth ρ) (v : V) :
    ∃ K : Subgroup G, IsOpen (K : Set G) ∧ ∀ x ∈ K, ρ x v = v :=
  ⟨stabilizerOf ρ v, hρ v, fun _ h => mem_stabilizerOf.1 h⟩

end SlopeTestRemainingChoices

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem char_apply (α : Fin n → ℂˣ) (p : GroundTheory.Automorphic.Iwasawa.blockUpper k n (id : Fin n → Fin n)) (z : ℂ) :
    ((GlobalTheory.SmGL.ofChar (GlobalTheory.SmGL.torusChar fun i => unrChar k (α i))).comp (leviTorus k (Fin n)).symm.toMonoidHom)
        (GlobalTheory.SmGL.leviProj k (points (Fin n)) (toParab p)) z =
      (∏ i, ((α i ^ ord k (diagUnit p i) : ℂˣ) : ℂ)) * z := by
  have h1 : ∀ i, ((leviTorus k (Fin n)).symm (GlobalTheory.SmGL.leviProj k (points (Fin n)) (toParab p))) i =
      diagUnit p i := det_leviProj p
  change GlobalTheory.SmGL.ofChar (GlobalTheory.SmGL.torusChar fun i => unrChar k (α i))
    ((leviTorus k (Fin n)).symm (GlobalTheory.SmGL.leviProj k (points (Fin n)) (toParab p))) z = _
  rw [GlobalTheory.SmGL.ofChar_apply, GlobalTheory.SmGL.torusChar_apply, Units.coe_prod]
  simp only [h1, unrChar_apply]

theorem addChar_theta_law_rearrangement_identity (α : Fin n → ℂˣ)
    (f : IndSp (points (Fin n)) ((GlobalTheory.SmGL.ofChar (GlobalTheory.SmGL.torusChar fun i => unrChar k (α i))).comp (leviTorus k (Fin n)).symm.toMonoidHom))
    (p : GroundTheory.Automorphic.Iwasawa.blockUpper k n (id : Fin n → Fin n)) (g : GL (Fin n) k) :
    f.1.1 ((p : GL (Fin n) k) * g) = borelChar (paramChar k α) p * f.1.1 g := by
  have h := parInd_law (points (Fin n)) _ f (toParab p) g
  have h2 : f.1.1 ((p : GL (Fin n) k) * g) = _ := h
  rw [h2, borelChar_apply, paramChar_leviProj, ← deltaHalf_eq, smul_eq_mul, char_apply, mul_assoc]

theorem induced_vector_smooth_open_subgroup (ρ : Representation ℂ (Levi k fun _ : Fin n => Unit) ℂ)
    (f : IndSp (points (Fin n)) ρ) :
    ∃ K : Subgroup (GL (Fin n) k), IsOpen (K : Set (GL (Fin n) k)) ∧
      ∀ x ∈ K, ∀ g, f.1.1 (g * x) = f.1.1 g := by
  obtain ⟨K, hK, hKf⟩ := exists_open_fix _ (isSmooth_parInd (points (Fin n)) ρ) f
  refine ⟨K, hK, fun x hx g => ?_⟩
  have h := congrArg (fun v : IndSp (points (Fin n)) ρ => v.1.1 g) (hKf x hx)
  exact (parInd_apply (points (Fin n)) ρ x g f).symm.trans h
end

theorem indSp_mem_principalSeriesSpace : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (α : Fin n → ℂˣ) (f : IndSp (points (Fin n)) ((GlobalTheory.SmGL.ofChar (GlobalTheory.SmGL.torusChar fun i => unrChar k (α i))).comp (leviTorus k (Fin n)).symm.toMonoidHom)), (fun g => f.1.1 g) ∈ principalSeriesSpace k n (paramChar k α) := by
  intro k _ _ _ _ n α f
  rw [mem_principalSeriesSpace]
  exact ⟨fun p g => addChar_theta_law_rearrangement_identity α f p g, induced_vector_smooth_open_subgroup _ f⟩

end GlobalTheory.CompanionTheory.SphSupp.PsBridge
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedInPrincipalSeriesStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.Published GlobalTheory.SplitWeil
open GroundTheory.Automorphic.Spherical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.induced_in_principal_series : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (α : Fin n → ℂˣ) (f : IndSp (points (Fin n)) ((GlobalTheory.SmGL.ofChar (GlobalTheory.SmGL.torusChar fun i => unrChar k (α i))).comp (leviTorus k (Fin n)).symm.toMonoidHom)), (fun g => f.1.1 g) ∈ principalSeriesSpace k n (paramChar k α) := by
  first | exact @GlobalTheory.CompanionTheory.SphSupp.PsBridge.indSp_mem_principalSeriesSpace | exact GlobalTheory.CompanionTheory.SphSupp.PsBridge.indSp_mem_principalSeriesSpace | (intros; apply GlobalTheory.CompanionTheory.SphSupp.PsBridge.indSp_mem_principalSeriesSpace <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubquotientPrincipalSeriesBound
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubquotientPrincipalSeriesBound
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.Published GlobalTheory.SplitWeil
open GroundTheory.Automorphic.Spherical

namespace GlobalTheory.CompanionTheory.HeckeSub

theorem isSatakeParameter_subquotient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (α : Fin n → ℂˣ) (X V : Type) [AddCommGroup X] [Module ℂ X] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) k) X), IsSmooth ρ → ∀ (ι : ρ.IntertwiningMap (principalSeries k n (paramChar k α))), Function.Injective ι → ∀ (π : Representation ℂ (GL (Fin n) k) V), IsSubquotient π ρ → ∀ [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)] (μ : MeasureTheory.Measure (GL (Fin n) k)) [μ.IsHaarMeasure], IsSatakeParameter π μ α := by
  intro k _ _ _ _ n α X V _ _ _ _ ρ hρ ι hι π hπ _ _ μ _ h v hv
  obtain ⟨S, f, hf⟩ := hπ
  have hS : IsSmooth S.toRepresentation :=
    IsSubquotient.isSmooth (ρ := ρ) ⟨S, .id _, Function.surjective_id⟩ hρ
  obtain ⟨u, rfl⟩ := hf v
  have hfix : ∀ g ∈ GroundTheory.Automorphic.GLnLocal.integralGL k n, π g (f u) = f u := fun g hg =>
    GroundTheory.Automorphic.mem_fixedVectors.1 hv g hg
  obtain ⟨w, hw, hfw⟩ := IwahoriOnto.exists_fixed_map_eq hS
    (GroundTheory.Automorphic.GLnLocal.isCompact_integralGL k n) f.toLinearMap u fun g hg => by
      show f (S.toRepresentation g u) = f u
      rw [f.isIntertwining]
      exact hfix g hg
  have hfw' : f w = f u := hfw
  have hw' : w ∈ GroundTheory.Automorphic.fixedVectors S.toRepresentation
      (GroundTheory.Automorphic.GLnLocal.integralGL k n) := by
    simpa [fixed, eig, GroundTheory.Automorphic.fixedVectors] using hw
  let T : S.toRepresentation.IntertwiningMap (principalSeries k n (paramChar k α)) :=
    ⟨ι.toLinearMap ∘ₗ S.toSubmodule.subtype, fun g => by
      refine LinearMap.ext fun x => ?_
      exact ι.isIntertwining _ _ g x⟩
  have hT : Function.Injective T := fun a b e => Subtype.ext (hι e)
  have hTw : T w ∈ GroundTheory.Automorphic.fixedVectors (principalSeries k n (paramChar k α))
      (GroundTheory.Automorphic.GLnLocal.integralGL k n) :=
    GroundTheory.Automorphic.mem_fixedVectors.2 fun g hg => by
      rw [← T.isIntertwining, GroundTheory.Automorphic.mem_fixedVectors.1 hw' g hg]
  have hmem := (h : GroundTheory.Automorphic.HeckeAlgebra μ).mem
  set c := GroundTheory.Automorphic.Spherical.evalAt α (satakeTransform μ h) with hc
  have hPS := isSatakeParameter_principalSeries (F := k) (μ := μ) α h (T w) hTw
  have hact : GroundTheory.Automorphic.heckeAct μ S.toRepresentation (h : GroundTheory.Automorphic.HeckeAlgebra μ) w = c • w := by
    apply hT
    rw [GroundTheory.Automorphic.map_heckeAct T hmem (hS w), hPS, map_smul]
  rw [← hfw', ← GroundTheory.Automorphic.map_heckeAct f hmem (hS w), hact, map_smul]

end GlobalTheory.CompanionTheory.HeckeSub
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubquotientPrincipalSeriesBoundStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.Published GlobalTheory.SplitWeil
open GroundTheory.Automorphic.Spherical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subquotient_principal_series_bound : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (α : Fin n → ℂˣ) (X V : Type) [AddCommGroup X] [Module ℂ X] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) k) X), IsSmooth ρ → ∀ (ι : ρ.IntertwiningMap (principalSeries k n (paramChar k α))), Function.Injective ι → ∀ (π : Representation ℂ (GL (Fin n) k) V), IsSubquotient π ρ → ∀ [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)] (μ : MeasureTheory.Measure (GL (Fin n) k)) [μ.IsHaarMeasure], IsSatakeParameter π μ α := by
  first | exact @GlobalTheory.CompanionTheory.HeckeSub.isSatakeParameter_subquotient | exact GlobalTheory.CompanionTheory.HeckeSub.isSatakeParameter_subquotient | (intros; apply GlobalTheory.CompanionTheory.HeckeSub.isSatakeParameter_subquotient <;> assumption)
end
end

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.Published GlobalTheory.SplitWeil
open GroundTheory.Automorphic.Spherical

namespace GlobalTheory.CompanionTheory.SphSupp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mem_principalSeriesSpace_of_indSp {n : ℕ} (α : Fin n → ℂˣ)
    (f : IndSp (points (Fin n))
      ((GlobalTheory.SmGL.ofChar (GlobalTheory.SmGL.torusChar fun i => unrChar k (α i))).comp (leviTorus k (Fin n)).symm.toMonoidHom)) :
    (fun g => f.1.1 g) ∈ principalSeriesSpace k n (paramChar k α) :=
  GlobalTheory.T.induced_in_principal_series k n α f

theorem isSatakeParameter_of_isSubquotient_of_injective {n : ℕ} (α : Fin n → ℂˣ) {X V : Type}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ (GL (Fin n) k) X}
    (hρ : IsSmooth ρ) (ι : ρ.IntertwiningMap (principalSeries k n (paramChar k α))) (hι : Function.Injective ι)
    {π : Representation ℂ (GL (Fin n) k) V} (h : IsSubquotient π ρ)
    [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)] (μ : MeasureTheory.Measure (GL (Fin n) k))
    [μ.IsHaarMeasure] : IsSatakeParameter π μ α :=
  GlobalTheory.T.subquotient_principal_series_bound k n α X V ρ hρ ι hι π h μ

theorem KO_eq_integralGL (n : ℕ) : KO k (Fin n) = GroundTheory.Automorphic.GLnLocal.integralGL k n := rfl

theorem fixed_eq_fixedVectors {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (H : Subgroup G) : fixed ρ H = GroundTheory.Automorphic.fixedVectors ρ H := by
  ext v
  simp [fixed, eig, GroundTheory.Automorphic.fixedVectors]

def bridge {n : ℕ} (α : Fin n → ℂˣ) :
    (prinSeries fun i => unrChar k (α i)).IntertwiningMap (principalSeries k n (paramChar k α)) where
  toFun f := ⟨fun g => f.1.1 g, mem_principalSeriesSpace_of_indSp α f⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  isIntertwining' g := LinearMap.ext fun f => Subtype.ext (funext fun x => by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply]
    rfl)

theorem bridge_injective {n : ℕ} (α : Fin n → ℂˣ) : Function.Injective (bridge (k := k) α) := fun f f' e =>
  by
  have := congrArg Subtype.val e
  apply Subtype.ext
  apply Subtype.ext
  exact this

theorem isSatakeParameter_of_isSubquotient {n : ℕ} (α : Fin n → ℂˣ) {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin n) k) V} (h : IsSubquotient π (prinSeries fun i => unrChar k (α i)))
    [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)] (μ : MeasureTheory.Measure (GL (Fin n) k))
    [μ.IsHaarMeasure] : IsSatakeParameter π μ α :=
  isSatakeParameter_of_isSubquotient_of_injective α (isSmooth_parInd _ _) (bridge α) (bridge_injective α) h μ

theorem hasSupport_prinSeries (n : ℕ) (χ : Fin n → kˣ →* ℂˣ) (hχ : ∀ i, IsSmoothChar (χ i))
    (π : IrrRep (GL (Fin n) k)) (h : IsSubquotient π.ρ (prinSeries χ)) :
    HasSupport π.ρ (Finset.univ.val.map fun i => IrrGL.ofChar (χ i) (hχ i)) := by
  have H : GlobalTheory.SmGL.IsCuspSupport π.ρ (fun _ : Fin n => 1) fun a => detRep (Fin 1) (χ a) :=
    ⟨π.irr, fun a => ⟨one_pos, isIrreducible_ofChar _, isCuspidal_detRep_one (hχ a)⟩, _,
      h.trans (GlobalTheory.PrinProd.isSubquotient_prinSeries_multiProd k n χ)⟩
  exact hasSupport_of_isCuspSupport H

end GlobalTheory.CompanionTheory.SphSupp

namespace GlobalTheory.CompanionTheory.SphSupp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isSpherical_iff_fixedVectors {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V) :
    IsSpherical π ↔ GroundTheory.Automorphic.fixedVectors π (GroundTheory.Automorphic.GLnLocal.integralGL k n) ≠ ⊥ := by
  show fixed π (KO k (Fin n)) ≠ ⊥ ↔ _
  rw [KO_eq_integralGL, fixed_eq_fixedVectors]

end GlobalTheory.CompanionTheory.SphSupp
