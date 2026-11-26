module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlatVectorEqUnitMulCentralTranslateLiftVector
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusActionIntegrality

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProdVal
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.FlatConj

theorem xiR_val {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} (hC : GlobalTheory.Hk3.Core R F)
    (t : T0) (PP : Pl D.host.E) (hP : PP ∈ R.Q t) (u : (kP PP)ˣ) :
    ∃ s : (AE D)ˣ, ((R.xiR t PP u : ℂˣ) : ℂ) = ((R.xi t s : Circle) : ℂ) := by
  obtain ⟨a, k, hk, hx⟩ := GlobalTheory.ConjRes.exists_lift PP u
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨e, he, -⟩ := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3 PP
  refine ⟨Formalism.L2.JoinChr.locU he.1 k, ?_⟩
  rw [hC.lev.xiR t PP hP a k u hk hx, (hC.lev.xi t).2 PP e he k _ (Formalism.L2.JoinChr.locU_val he.1 k)]

theorem prod_val {D : D7} (ξ : (AE D)ˣ →* Circle) (S : Finset (Pl D.host.E)) (v : Pl D.host.E → ℂ)
    (hv : ∀ PP ∈ S, ∃ s : (AE D)ˣ, v PP = ((ξ s : Circle) : ℂ)) :
    ∃ s : (AE D)ˣ, ∏ PP ∈ S, v PP = ((ξ s : Circle) : ℂ) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, by simp⟩
  | insert a S ha ih =>
    obtain ⟨s0, h0⟩ := hv a (Finset.mem_insert_self a S)
    obtain ⟨s1, h1⟩ := ih fun PP hP => hv PP (Finset.mem_insert_of_mem hP)
    refine ⟨s0 * s1, ?_⟩
    rw [Finset.prod_insert ha, h0, h1, map_mul, Circle.coe_mul]

end GlobalTheory.FlatConj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeChoiceFlatVectorFactoredForm
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlatVectorEqGaussSumSmulCentralTranslate
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddSumEqProd
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharacterValueAtConjugatePlacePow
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharacterValueAtConjugatePlacePow
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.ConjLocVal

theorem value_at_conj_place : ∀ (D : D7) (PP : Pl D.host.E) (e : AE D) (ϖ : 𝓞 D.host.E) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (n : ℕ) (y : (AE D)ˣ), Formalism.L2.NTheta.IsIdemAt e PP → ϖ ∈ PP.asIdeal → ϖ ∉ PP.asIdeal ^ 2 → ChrEq c χ → χ.UnrAt (Formalism.L2.DIV.conjPl PP) → (y : AE D) = 1 + cA D e * (incA D (star (ϖ : D.host.E)) ^ n - 1) → ((c y : Circle) : ℂ) = ((χ.val (Formalism.L2.DIV.conjPl PP) : ℂˣ) : ℂ) ^ n := by
  intro D PP e ϖ c χ n y he h1 h2 hc hU hy
  obtain ⟨⟨e1, e2, v, ε, hε, e3⟩, e4⟩ := Formalism.IndefR.Fin.LevelGroupLemmas.isIdemAt_conj he
  have hpl : Formalism.L2.JoinChr.IsPlIdem D (cA D e) (Formalism.L2.DIV.conjPl PP) := ⟨e1, ⟨v, ε, hε, Or.inl ⟨e2, e3⟩⟩, e4⟩
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    exact h2 (zero_mem _)
  have hϖE : (ϖ : D.host.E) ≠ 0 := by exact_mod_cast hϖ0
  have hs0 : star (ϖ : D.host.E) ≠ 0 := star_ne_zero.2 hϖE
  set k : D.host.Eˣ := Units.mk0 (star (ϖ : D.host.E)) hs0 with hk
  have hy' : (y : AE D) = Formalism.L2.JoinChr.locE D (cA D e) ((k ^ n : D.host.Eˣ) : D.host.E) := by
    rw [hy, Formalism.L2.JoinChr.locE, Units.val_pow_eq_pow_val, map_pow]
    rfl
  rw [hc.2 _ _ hpl (k ^ n) y hy', map_pow, Units.val_pow_eq_pow_val]
  congr 1
  have hmem : Formalism.L2.DIV.starO ϖ ∈ (Formalism.L2.DIV.conjPl PP).asIdeal := by
    show Formalism.L2.DIV.starO (Formalism.L2.DIV.starO ϖ) ∈ PP.asIdeal
    rw [Formalism.L2.DIV.starO_starO]; exact h1
  have hnsq : Formalism.L2.DIV.starO ϖ ∉ (Formalism.L2.DIV.conjPl PP).asIdeal ^ 2 := by
    intro hm
    have hm' := Ideal.le_comap_pow (f := Formalism.L2.DIV.starOHom) (K := PP.asIdeal) 2 hm
    rw [Ideal.mem_comap] at hm'
    apply h2
    have : Formalism.L2.DIV.starOHom (Formalism.L2.DIV.starO ϖ) = ϖ := Formalism.L2.DIV.starO_starO ϖ
    rwa [this] at hm'
  have hunif : Formalism.L2.Host.IsUnifAt (Formalism.L2.DIV.conjPl PP) (Formalism.L2.Host.atFin (Formalism.L2.DIV.conjPl PP) k) := by
    show Valued.v (((star (ϖ : D.host.E) : D.host.E)) : (Formalism.L2.DIV.conjPl PP).adicCompletion D.host.E) = _
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', ← Formalism.L2.DIV.starO_coe,
      HeightOneSpectrum.valuation_of_algebraMap]
    exact GlobalTheory.LatIntFacts.intValuation_uniformiser _ hmem hnsq
  have hval : χ.loc (Formalism.L2.DIV.conjPl PP) (Formalism.L2.Host.atFin (Formalism.L2.DIV.conjPl PP) k) = χ.val (Formalism.L2.DIV.conjPl PP) := by
    have hu : Formalism.L2.Host.IsUnitAt (Formalism.L2.DIV.conjPl PP)
        (Formalism.L2.Host.atFin (Formalism.L2.DIV.conjPl PP) k * (Formalism.L2.Host.atFin (Formalism.L2.DIV.conjPl PP) (Formalism.L2.Host.unif (Formalism.L2.DIV.conjPl PP)))⁻¹) := by
      have h2' := Formalism.L2.Host.unif_spec (Formalism.L2.DIV.conjPl PP)
      unfold Formalism.L2.Host.IsUnitAt
      unfold Formalism.L2.Host.IsUnifAt at hunif h2'
      rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hunif, h2']
      exact mul_inv_cancel₀ (by simp)
    have h3 := hU _ hu
    rw [map_mul, map_inv, mul_inv_eq_one] at h3
    exact h3
  show ((χ.loc (Formalism.L2.DIV.conjPl PP) (Formalism.L2.Host.atFin (Formalism.L2.DIV.conjPl PP) k) : ℂˣ) : ℂ) = _
  rw [hval]

end GlobalTheory.ConjLocVal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharacterValueAtConjugatePlacePowStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeCharacter_value_at_conjugatePlace_pow : ∀ (D : D7) (PP : Pl D.host.E) (e : AE D) (ϖ : 𝓞 D.host.E) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (n : ℕ) (y : (AE D)ˣ), Formalism.L2.NTheta.IsIdemAt e PP → ϖ ∈ PP.asIdeal → ϖ ∉ PP.asIdeal ^ 2 → ChrEq c χ → χ.UnrAt (Formalism.L2.DIV.conjPl PP) → (y : AE D) = 1 + cA D e * (incA D (star (ϖ : D.host.E)) ^ n - 1) → ((c y : Circle) : ℂ) = ((χ.val (Formalism.L2.DIV.conjPl PP) : ℂˣ) : ℂ) ^ n := by
  first | exact @GlobalTheory.ConjLocVal.value_at_conj_place | exact GlobalTheory.ConjLocVal.value_at_conj_place | (intros; apply GlobalTheory.ConjLocVal.value_at_conj_place <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixesUntwistedLiftDataConjugatePrimeValueSqrtNor
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixesUntwistedLiftDataConjugatePrimeValueSqrtNor
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.ConjFix

variable {D : D7}

noncomputable def starOEquiv : 𝓞 D.host.E ≃+* 𝓞 D.host.E :=
  { Formalism.L2.DIV.starOHom (E := D.host.E) with
    invFun := Formalism.L2.DIV.starOHom (E := D.host.E)
    left_inv := fun a => Formalism.L2.DIV.starO_starO a
    right_inv := fun a => Formalism.L2.DIV.starO_starO a }

theorem natCast_mem_conjPl_iff (PP : Pl D.host.E) (N : ℕ) :
    ((N : 𝓞 D.host.E)) ∈ (Formalism.L2.DIV.conjPl PP).asIdeal ↔ ((N : 𝓞 D.host.E)) ∈ PP.asIdeal := by
  show Formalism.L2.DIV.starOHom (N : 𝓞 D.host.E) ∈ PP.asIdeal ↔ _
  rw [map_natCast]

theorem absNorm_conjPl (PP : Pl D.host.E) :
    Ideal.absNorm (Formalism.L2.DIV.conjPl PP).asIdeal = Ideal.absNorm PP.asIdeal := by
  have h : (Formalism.L2.DIV.conjPl PP).asIdeal = PP.asIdeal.map (starOEquiv (D := D)) := by
    rw [← Ideal.comap_symm]; rfl
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv PP.asIdeal (Formalism.L2.DIV.conjPl PP).asIdeal (starOEquiv (D := D)) h).toEquiv).symm

theorem fixBase_split_conj {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D)
    [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (i : Fin D.R.m) (τ : ℂ ≃+* ℂ) (PP : Pl D.host.E) :
    FixBase T R i τ → ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal →
      τ ((((R.C.mu0 i * R.C.eta⁻¹).val (Formalism.L2.DIV.conjPl PP) : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm PP.asIdeal : ℝ) : ℝ) : ℂ)) =
        (((R.C.mu0 i * R.C.eta⁻¹).val (Formalism.L2.DIV.conjPl PP) : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm PP.asIdeal : ℝ) : ℝ) : ℂ) := by
  intro hF hN
  have hN' : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ (Formalism.L2.DIV.conjPl PP).asIdeal := by
    rwa [natCast_mem_conjPl_iff]
  have := hF.split (Formalism.L2.DIV.conjPl PP) hN'
  rwa [absNorm_conjPl] at this

end GlobalTheory.ConjFix
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixesUntwistedLiftDataConjugatePrimeValueSqrtNorStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixesUntwistedLiftData_conjugatePrime_value_sqrtNorm : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (i : Fin D.R.m) (τ : ℂ ≃+* ℂ) (PP : Pl D.host.E), FixBase T R i τ → ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal → τ ((((R.C.mu0 i * R.C.eta⁻¹).val (Formalism.L2.DIV.conjPl PP) : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm PP.asIdeal : ℝ) : ℝ) : ℂ)) = (((R.C.mu0 i * R.C.eta⁻¹).val (Formalism.L2.DIV.conjPl PP) : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm PP.asIdeal : ℝ) : ℝ) : ℂ) := by
  first | exact @GlobalTheory.ConjFix.fixBase_split_conj | exact GlobalTheory.ConjFix.fixBase_split_conj | (intros; apply GlobalTheory.ConjFix.fixBase_split_conj <;> assumption)
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.FlatConst

theorem one_add_sum_eq_prod {R ι : Type} [CommRing R] [DecidableEq ι] (s : Finset ι) (f a : ι → R)
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → f i * f j = 0) :
    1 + ∑ i ∈ s, f i * (a i - 1) = ∏ i ∈ s, (1 + f i * (a i - 1)) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj,
      ← ih fun k hk l hl hkl => h k (Finset.mem_insert_of_mem hk) l (Finset.mem_insert_of_mem hl) hkl]
    have h0 : f j * (a j - 1) * ∑ k ∈ s, f k * (a k - 1) = 0 := by
      rw [Finset.mul_sum]
      refine Finset.sum_eq_zero fun k hk => ?_
      have hne : j ≠ k := fun e => hj (e ▸ hk)
      have := h j (Finset.mem_insert_self j s) k (Finset.mem_insert_of_mem hk) hne
      calc f j * (a j - 1) * (f k * (a k - 1)) = (f j * f k) * ((a j - 1) * (a k - 1)) := by ring
        _ = 0 := by rw [this, zero_mul]
    linear_combination (-1 : R) * h0

theorem chr_inv_val {D : D7} (c : (AE D)ˣ →* Circle) (x : (AE D)ˣ) : ((c x⁻¹ : Circle) : ℂ) = ((c x : Circle) : ℂ)⁻¹ := by
  rw [map_inv, Circle.coe_inv]

theorem chrW_val {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (t' : T0) (x : (AE D)ˣ) :
    (((Lift.chrTh (R.toLevCh.mu t') R.eta ((i : ℕ) + 1)).2 x : Circle) : ℂ) =
      ((R.mu0 ((i : ℕ) + 1) x : Circle) : ℂ) * ((R.xi t' x : Circle) : ℂ) * ((R.eta x : Circle) : ℂ)⁻¹ := by
  unfold Lift.chrTh LevCh.mu Lift.tup
  simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, Circle.coe_mul, Circle.coe_inv]

end GlobalTheory.FlatConst


open GlobalTheory.FlatConst in
theorem GlobalTheory.FlatConst.flat_const : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (t : T0) (es : Pl D.host.E → AE D) (ϖ : Pl D.host.E → 𝓞 D.host.E) (n : ℕ) (x : (AE D)ˣ), (∀ PP ∈ R.Q t, Formalism.L2.NTheta.IsIdemAt (es PP) PP) → (∑ PP ∈ R.Q t, es PP) * cA D (∑ PP ∈ R.Q t, es PP) = 0 → (∀ PP ∈ R.Q t, ϖ PP ∈ PP.asIdeal ∧ ϖ PP ∉ PP.asIdeal ^ 2) → (x : AE D) = 1 + ∑ PP ∈ R.Q t, cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) ^ n - 1) → ∃ b : ℂ, (∀ τ : ℂ ≃+* ℂ, FixBase T R i τ → τ (b * ∏ PP ∈ R.Q t, (((Real.sqrt (Ideal.absNorm PP.asIdeal : ℝ) : ℝ) : ℂ)⁻¹) ^ n) = b * ∏ PP ∈ R.Q t, (((Real.sqrt (Ideal.absNorm PP.asIdeal : ℝ) : ℝ) : ℂ)⁻¹) ^ n) ∧ (∀ t' : T0, (((Lift.chrTh (R.toLevCh.mu t') R.eta ((i : ℕ) + 1)).2 x : Circle) : ℂ)⁻¹ = b * ((R.xi t' x⁻¹ : Circle) : ℂ)) ∧ (∀ (t' : T0) (S : Finset (Pl D.host.E)), S ⊆ R.Q t' → ∀ u : ∀ PP : Pl D.host.E, (kP PP)ˣ, ∃ s : (AE D)ˣ, ∏ PP ∈ S, ((R.xiR t' PP (u PP) : ℂˣ) : ℂ) = ((R.xi t' s : Circle) : ℂ)) := by
  intro D G _ _ Pl0 T0 A T _ R F hC i t es ϖ n x hes hc hϖ hx
  set Q := R.Q t with hQ

  have hidem : ∀ PP ∈ Q, cA D (es PP) * cA D (es PP) = cA D (es PP) := fun PP hP =>
    Formalism.IndefR.Fin.LevelGroupLemmas.isIdem_cA (hes PP hP).1.1
  have hϖ0 : ∀ PP ∈ Q, star ((ϖ PP : 𝓞 D.host.E) : D.host.E) ≠ 0 := fun PP hP h0 => by
    have : (ϖ PP : D.host.E) = 0 := by rw [← star_star ((ϖ PP : 𝓞 D.host.E) : D.host.E), h0, star_zero]
    exact (hϖ PP hP).2 (by rw [show ϖ PP = 0 from RingOfIntegers.ext this]; exact zero_mem _)
  let y : Q → (AE D)ˣ := fun P =>
    Formalism.L2.JoinChr.locU (hidem P.1 P.2) ((Units.mk0 (star ((ϖ P.1 : 𝓞 D.host.E) : D.host.E)) (hϖ0 P.1 P.2)) ^ n)
  have hyv : ∀ P : Q, ((y P : (AE D)ˣ) : AE D) = 1 + cA D (es P.1) * (incA D (star ((ϖ P.1 : 𝓞 D.host.E) : D.host.E)) ^ n - 1) := by
    intro P
    show Formalism.L2.JoinChr.locE D _ _ = _
    unfold Formalism.L2.JoinChr.locE
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, map_pow]
  have horth : ∀ P ∈ Q.attach, ∀ P' ∈ Q.attach, P ≠ P' → cA D (es P.1) * cA D (es P'.1) = 0 := by
    intro P _ P' _ hne
    rw [← map_mul, Formalism.IndefR.Fin.LevelGroupLemmas.idemSum_orth hes rfl hc P.2 P'.2 (fun e => hne (Subtype.ext e)), map_zero]
  have hxy : x = ∏ P ∈ Q.attach, y P := by
    apply Units.ext
    rw [Units.coe_prod, hx]
    simp only [hyv]
    rw [← Finset.sum_attach Q (fun PP => cA D (es PP) * (incA D (star ((ϖ PP : 𝓞 D.host.E) : D.host.E)) ^ n - 1))]
    exact one_add_sum_eq_prod Q.attach (fun P => cA D (es P.1)) (fun P => incA D (star ((ϖ P.1 : 𝓞 D.host.E) : D.host.E)) ^ n) horth

  have hg : ∀ PP ∈ Q, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := fun PP hP =>
    GlobalTheory.StdFrames.g_not_mem (hC.lev.Q_pl t) hP
  have hgc : ∀ PP ∈ Q, ∀ k : Fin 2, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ (Formalism.L2.DIV.conjPl PP).asIdeal := by
    intro PP hP k hk
    have hk' : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
      have : Formalism.L2.DIV.starOHom ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := hk
      rwa [map_natCast] at this
    apply hg PP hP
    rw [Nat.cast_mul]
    fin_cases k
    · exact Ideal.mul_mem_right _ _ hk'
    · exact Ideal.mul_mem_left _ _ hk'
  have unrM : ∀ PP ∈ Q, (R.C.mu0 i).UnrAt (Formalism.L2.DIV.conjPl PP) := fun PP hP =>
    (R.C.isMu0 i).unr _ fun k => hgc PP hP k
  have unrE : ∀ PP ∈ Q, R.C.eta.UnrAt (Formalism.L2.DIV.conjPl PP) := fun PP _ => R.C.isEta.unr _

  have hvM : ((R.mu0 ((i : ℕ) + 1) x : Circle) : ℂ) = ∏ PP ∈ Q, (((R.C.mu0 i).val (Formalism.L2.DIV.conjPl PP) : ℂˣ) : ℂ) ^ n := by
    have := map_prod (Circle.coeHom.comp (R.mu0 ((i : ℕ) + 1))) y Q.attach
    rw [← hxy] at this
    show (Circle.coeHom.comp (R.mu0 ((i : ℕ) + 1))) x = _
    rw [this, ← Finset.prod_attach Q]
    refine Finset.prod_congr rfl fun P _ => ?_
    exact GlobalTheory.T.heckeCharacter_value_at_conjugatePlace_pow D P.1 (es P.1) (ϖ P.1) _ _ n (y P) (hes P.1 P.2) (hϖ P.1 P.2).1 (hϖ P.1 P.2).2 (hC.lev.mu0 i)
      (unrM P.1 P.2) (hyv P)
  have hvE : ((R.eta x : Circle) : ℂ) = ∏ PP ∈ Q, ((R.C.eta.val (Formalism.L2.DIV.conjPl PP) : ℂˣ) : ℂ) ^ n := by
    have := map_prod (Circle.coeHom.comp R.eta) y Q.attach
    rw [← hxy] at this
    show (Circle.coeHom.comp R.eta) x = _
    rw [this, ← Finset.prod_attach Q]
    refine Finset.prod_congr rfl fun P _ => ?_
    exact GlobalTheory.T.heckeCharacter_value_at_conjugatePlace_pow D P.1 (es P.1) (ϖ P.1) _ _ n (y P) (hes P.1 P.2) (hϖ P.1 P.2).1 (hϖ P.1 P.2).2 hC.lev.eta
      (unrE P.1 P.2) (hyv P)
  set sq : Pl D.host.E → ℂ := fun PP => ((Real.sqrt (Ideal.absNorm PP.asIdeal : ℝ) : ℝ) : ℂ) with hsq
  set v : Pl D.host.E → ℂ := fun PP => (((R.C.mu0 i * R.C.eta⁻¹).val (Formalism.L2.DIV.conjPl PP) : ℂˣ) : ℂ) with hv
  refine ⟨(((R.mu0 ((i : ℕ) + 1) x : Circle) : ℂ) * ((R.eta x : Circle) : ℂ)⁻¹)⁻¹, ?_, ?_, ?_⟩
  · intro τ hτ
    have key : (((R.mu0 ((i : ℕ) + 1) x : Circle) : ℂ) * ((R.eta x : Circle) : ℂ)⁻¹)⁻¹ * ∏ PP ∈ Q, (sq PP)⁻¹ ^ n =
        ∏ PP ∈ Q, ((v PP * sq PP)⁻¹) ^ n := by
      rw [hvM, hvE]
      simp only [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun PP _ => ?_
      simp only [hv, Formalism.L2.Host.HChar.val_mul, Formalism.L2.Host.HChar.val_inv, Units.val_mul, Units.val_inv_eq_inv_val]
      ring
    show τ (_ * ∏ PP ∈ Q, (sq PP)⁻¹ ^ n) = _ * ∏ PP ∈ Q, (sq PP)⁻¹ ^ n
    rw [key, map_prod]
    refine Finset.prod_congr rfl fun PP hP => ?_
    rw [map_pow, map_inv₀]
    congr 2
    exact GlobalTheory.T.fixesUntwistedLiftData_conjugatePrime_value_sqrtNorm T R i τ PP hτ (hg PP hP)
  · intro t'
    have h1 := chrW_val R i t' x
    have h2 := chr_inv_val (R.xi t') x
    simp only [h1, h2]
    ring
  · intro t' S hS u
    exact GlobalTheory.FlatConj.prod_val (R.xi t') S (fun PP => ((R.xiR t' PP (u PP) : ℂˣ) : ℂ))
      fun PP hP => GlobalTheory.FlatConj.xiR_val hC t' PP (hS hP) (u PP)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OmegaQEqGaussMulFlatTransform
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option maxHeartbeats 1600000

namespace GlobalTheory.FlatForm

open GlobalTheory.FlatConj

theorem gaussGL_inv {k : Type} [Field k] [Fintype k] (ψ : AddChar k ℂ) (ξ : kˣ →* ℂˣ) (r : ℕ) :
    gaussGL ψ⁻¹ ξ⁻¹ r = (starRingEnd ℂ) (gaussGL ψ ξ r) := by
  unfold gaussGL
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_mul, AddChar.inv_apply, AddChar.map_neg_eq_conj]
  congr 1
  set u := Matrix.GeneralLinearGroup.det x
  have h1 : ((ξ u : ℂˣ) : ℂ) ^ Fintype.card kˣ = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one, map_one, Units.val_one]
  have h2 : ‖((ξ u : ℂˣ) : ℂ)‖ = 1 := Complex.norm_eq_one_of_pow_eq_one h1 Fintype.card_ne_zero
  rw [MonoidHom.inv_apply, inv_inv, Units.val_inv_eq_inv_val, map_inv₀, ← Complex.inv_eq_conj h2, inv_inv]

theorem gaussGL_mul_inv {k : Type} [Field k] [Fintype k] (ψ : AddChar k ℂ) (ξ : kˣ →* ℂˣ) (r : ℕ)
    (hψ : ψ.IsPrimitive) (hξ : ξ ≠ 1) :
    gaussGL ψ ξ r * gaussGL ψ⁻¹ ξ⁻¹ r = (Fintype.card k : ℂ) ^ (r ^ 2) := by
  obtain ⟨hnorm, -⟩ := GlobalTheory.T.galois_matrix_gaussSum_eq_char_pow_mul k ψ ξ r hψ hξ (gaussGL ψ ξ r) rfl
  rw [gaussGL_inv, Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]
  push_cast
  rfl

theorem gaussGL_ne_zero {k : Type} [Field k] [Fintype k] (ψ : AddChar k ℂ) (ξ : kˣ →* ℂˣ) (r : ℕ)
    (hψ : ψ.IsPrimitive) (hξ : ξ ≠ 1) : gaussGL ψ ξ r ≠ 0 := fun h => by
  have := gaussGL_mul_inv ψ ξ r hψ hξ
  rw [h, zero_mul] at this
  exact pow_ne_zero _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) this.symm

theorem fourier_flat (k : Type) [Field k] [Fintype k] (ψ : AddChar k ℂ) (ξ : kˣ →* ℂˣ) (r t : ℕ) (hψ : ψ.IsPrimitive)
    (hξ : ξ ≠ 1) (u : Matrix (Fin (r + t)) (Fin r) k) :
    (∑ y : Matrix (Fin r) (Fin (r + t)) k, (if h : IsUnit (topL r (-y)).det then ((ξ h.unit : ℂˣ) : ℂ) else 0) *
      ψ (Matrix.trace (y * u))) = ((Fintype.card k : ℂ) ^ ((r + t) * r) * (gaussGL ψ ξ r)⁻¹) *
      (if h : LowZero r u ∧ IsUnit (topL r u).det then ((ξ h.2.unit : ℂˣ) : ℂ) ^ (-1 : ℤ) else 0) := by
  have hψ' : (ψ⁻¹).IsPrimitive := addChar_inv_isPrimitive_of_isPrimitive ψ hψ
  have hξ' : ξ⁻¹ ≠ 1 := inv_ne_one.mpr hξ
  obtain ⟨hsing, hinv⟩ := GlobalTheory.matrixGaussSum_singular_and_invertible k ℂ ψ⁻¹ ξ⁻¹ r hψ' hξ'
  have hmul := gaussGL_mul_inv ψ ξ r hψ hξ
  have hne := gaussGL_ne_zero ψ ξ r hψ hξ
  set G : ℂ := ∑ x : GL (Fin r) k, (((ξ⁻¹ (Matrix.GeneralLinearGroup.det x))⁻¹ : ℂˣ) : ℂ) *
    ψ⁻¹ (Matrix.trace (x : Matrix (Fin r) (Fin r) k)) with hG
  set q : ℂ := (Fintype.card k : ℂ) with hq
  have hC : q ^ ((r + t) * r) * (gaussGL ψ ξ r)⁻¹ = q ^ (r * t) * G := by
    have hG' : gaussGL ψ⁻¹ ξ⁻¹ r = G := rfl
    rw [hG'] at hmul
    rw [show (r + t) * r = r * t + r ^ 2 by ring, pow_add, ← hmul]
    field_simp
  rw [hC]
  set u₁ := u.submatrix (Fin.castAdd t) id
  set u₂ := u.submatrix (Fin.natAdd r) id
  have hsplit : ∀ p : Matrix (Fin r) (Fin r) k × Matrix (Fin r) (Fin t) k,
      ((if h : IsUnit (-p.1).det then ((ξ h.unit : ℂˣ) : ℂ) else 0) * ψ (trace (p.1 * u₁))) *
        ψ (trace (p.2 * u₂)) =
      (if h : IsUnit (topL r (-(squareAndRectColumnsEquivWideMatrix p))).det then ((ξ h.unit : ℂˣ) : ℂ) else 0) *
        ψ (Matrix.trace (squareAndRectColumnsEquivWideMatrix p * u)) := by
    intro p
    have e1 : (squareAndRectColumnsEquivWideMatrix p).submatrix id (Fin.castAdd t) = p.1 :=
      congrArg Prod.fst (squareAndRectColumnsEquivWideMatrix.symm_apply_apply p)
    have e2 : (squareAndRectColumnsEquivWideMatrix p).submatrix id (Fin.natAdd r) = p.2 :=
      congrArg Prod.snd (squareAndRectColumnsEquivWideMatrix.symm_apply_apply p)
    rw [mul_assoc, ← AddChar.map_add_eq_mul, trace_mul_split_castAdd_natAdd _ u, topLeftBlock_neg_eq_submatrix_castAdd, e1, e2]
  rw [← Fintype.sum_equiv squareAndRectColumnsEquivWideMatrix _ _ hsplit, Fintype.sum_prod_type]
  rw [show (∑ x : Matrix (Fin r) (Fin r) k, ∑ y : Matrix (Fin r) (Fin t) k,
      (if h : IsUnit (-(x, y).1).det then ((ξ h.unit : ℂˣ) : ℂ) else 0) * ψ (trace ((x, y).1 * u₁)) *
        ψ (trace ((x, y).2 * u₂))) =
      (∑ x : Matrix (Fin r) (Fin r) k, (if h : IsUnit (-x).det then ((ξ h.unit : ℂˣ) : ℂ) else 0) *
        ψ (trace (x * u₁))) * ∑ y : Matrix (Fin r) (Fin t) k, ψ (trace (y * u₂)) by
    rw [Finset.sum_mul_sum]]
  rw [sum_GL_character_neg_det_addChar_trace, sum_addChar_trace_rectMatrix_mul ψ hψ u₂]
  by_cases hu2 : u₂ = 0
  swap
  · rw [if_neg hu2, mul_zero, dite_eq_right (fun h => hu2 ((lowZero_iff_submatrix_natAdd_eq_zero u).mp h.1)), mul_zero]
  rw [if_pos hu2]
  by_cases hdet : IsUnit u₁.det
  swap
  · have h0 : u₁.det = 0 := by
      by_contra h; exact hdet (isUnit_iff_ne_zero.mpr h)
    rw [hsing u₁ h0, zero_mul, dite_eq_right, mul_zero]
    rintro ⟨-, h⟩
    rw [topLeftBlock_eq_submatrix_castAdd] at h
    exact hdet h
  have hh : LowZero r u ∧ IsUnit (topL r u).det := ⟨(lowZero_iff_submatrix_natAdd_eq_zero u).mpr hu2, by rw [topLeftBlock_eq_submatrix_castAdd]; exact hdet⟩
  rw [dif_pos hh]
  set a : GL (Fin r) k := Matrix.GeneralLinearGroup.mkOfDetNeZero u₁ hdet.ne_zero
  have ha := hinv a
  simp only [Matrix.one_mul] at ha
  have hau : (a : Matrix (Fin r) (Fin r) k) = u₁ := rfl
  rw [hau] at ha
  rw [ha, ← hG]
  have hunit : hh.2.unit = Matrix.GeneralLinearGroup.det a := Units.ext (by simp [hau, topLeftBlock_eq_submatrix_castAdd, u₁])
  rw [hunit, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, _root_.zpow_neg_one]
  ring

theorem gaussP_ne_zero {E : Type} [Field E] [NumberField E] (PP : Pl E) (ψ : AddChar (kP PP) ℂ) (ξ : (kP PP)ˣ →* ℂˣ) (r : ℕ)
    (hψ : ψ.IsPrimitive) (hξ : ξ ≠ 1) : gaussP PP ψ ξ r ≠ 0 :=
  @gaussGL_ne_zero (kP PP) (resField PP) (resFintype PP) ψ ξ r hψ hξ

theorem omegaQ_eq_gauss_mul_flat_transform (D : D7) [inst : ∀ PP : Pl D.host.E, Fintype (kP PP)] (Q : Finset (Pl D.host.E))
    (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ψP : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ) (r n : ℕ) (hrn : r ≤ n)
    (hQ : ∀ PP ∈ Q, (ψP PP).IsPrimitive ∧ ξ PP ≠ 1) (ub : ∀ PP : Pl D.host.E, Matrix (Fin n) (Fin r) (kP PP)) :
    omegaQ Q r ξ (-1) ub = (∏ PP ∈ Q, ((Nat.card (kP PP) : ℂ) ^ (n * r) * (gaussP PP (ψP PP) (ξ PP) r)⁻¹))⁻¹ *
      ∑ y : (∀ PP : ↥Q, Matrix (Fin r) (Fin n) (kP PP.1)),
        omegaFlat Q r ξ (fun PP => if h : PP ∈ Q then -(y ⟨PP, h⟩) else 0) *
          ∏ PP : ↥Q, ψP PP.1 (Matrix.trace (y PP * ub PP.1)) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hrn
  obtain rfl : inst = fun PP => resFintype PP := Subsingleton.elim _ _
  letI : ∀ PP : Pl D.host.E, Fintype (kP PP) := fun PP => resFintype PP
  let fl : ∀ PP : Pl D.host.E, Matrix (Fin r) (Fin (r + t)) (kP PP) → ℂ := fun PP y =>
    if h : IsUnit (topL r y).det then ((ξ PP h.unit : ℂˣ) : ℂ) else 0
  let fq : ∀ PP : Pl D.host.E, Matrix (Fin (r + t)) (Fin r) (kP PP) → ℂ := fun PP u =>
    if h : LowZero r u ∧ IsUnit (topL r u).det then ((ξ PP h.2.unit : ℂˣ) : ℂ) ^ (-1 : ℤ) else 0
  let C : Pl D.host.E → ℂ := fun PP => (Nat.card (kP PP) : ℂ) ^ ((r + t) * r) * (gaussP PP (ψP PP) (ξ PP) r)⁻¹
  have hC0 : ∀ PP : ↥Q, C PP ≠ 0 := fun PP =>
    mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.mpr Nat.card_pos.ne'))
      (inv_ne_zero (gaussP_ne_zero _ _ _ _ (hQ _ PP.2).1 (hQ _ PP.2).2))
  have hCe : ∀ (PP : ↥Q) (u : Matrix (Fin (r + t)) (Fin r) (kP PP.1)),
      (∑ y : Matrix (Fin r) (Fin (r + t)) (kP PP.1), fl PP.1 (-y) * ψP PP.1 (Matrix.trace (y * u))) = C PP * fq PP.1 u := by
    intro PP u
    have := @fourier_flat (kP PP.1) (resField PP.1) (resFintype PP.1) (ψP PP.1) (ξ PP.1) r t (hQ _ PP.2).1 (hQ _ PP.2).2 u
    rw [← Nat.card_eq_fintype_card] at this
    exact this
  have hq : omegaQ Q r ξ (-1) ub = ∏ PP : ↥Q, fq PP.1 (ub PP.1) := by
    rw [← Finset.attach_eq_univ]
    unfold omegaQ
    convert GlobalTheory.FlatFourierQ.dite_prod' Q (fun PP => LowZero r (ub PP) ∧ IsUnit (topL r (ub PP)).det)
      (fun PP h => ((ξ PP h.2.unit : ℂˣ) : ℂ) ^ (-1 : ℤ))
  have hf : ∀ y : (∀ PP : ↥Q, Matrix (Fin r) (Fin (r + t)) (kP PP.1)),
      omegaFlat Q r ξ (fun PP => if h : PP ∈ Q then -(y ⟨PP, h⟩) else 0) = ∏ PP : ↥Q, fl PP.1 (-(y PP)) := by
    intro y
    have e0 : ∀ Y : ∀ PP : Pl D.host.E, Matrix (Fin r) (Fin (r + t)) (kP PP),
        omegaFlat Q r ξ Y = ∏ PP ∈ Q.attach, fl PP.1 (Y PP.1) := by
      intro Y
      unfold omegaFlat
      convert GlobalTheory.FlatFourierQ.dite_prod' Q (fun PP => IsUnit (topL r (Y PP)).det) (fun PP h => ((ξ PP h.unit : ℂˣ) : ℂ))
    rw [e0, Finset.attach_eq_univ]
    refine Finset.prod_congr rfl fun PP _ => ?_
    simp only [dif_pos PP.2, Subtype.coe_eta]
  have hprod : (∏ PP ∈ Q, C PP) = ∏ PP : ↥Q, C PP := (Finset.prod_coe_sort Q C).symm
  show _ = (∏ PP ∈ Q, C PP)⁻¹ * _
  simp only [hf, ← Finset.prod_mul_distrib]
  have hs := Finset.prod_univ_sum (t := fun (PP : ↥Q) => (Finset.univ : Finset (Matrix (Fin r) (Fin (r + t)) (kP PP.1))))
    (f := fun (PP : ↥Q) (y : Matrix (Fin r) (Fin (r + t)) (kP PP.1)) => fl PP.1 (-y) * ψP PP.1 (Matrix.trace (y * ub PP.1)))
  rw [Fintype.piFinset_univ] at hs
  rw [← hs]
  simp only [hCe]
  rw [hprod, Finset.prod_mul_distrib (f := fun PP : ↥Q => C PP) (g := fun PP : ↥Q => fq PP.1 (ub PP.1)), hq, ← mul_assoc, inv_mul_cancel₀ (Finset.prod_ne_zero_iff.2 fun PP _ => hC0 PP), one_mul]

end GlobalTheory.FlatForm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlatVectorEqGaussSumSmulCentralTranslate
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.FlatForm

theorem lift_eq_gauss_model_flat : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (t₀ : T0), VStd D i → ∀ eQ : AE D, IsIdemSum eQ (R.Q t₀) → ∀ ϖ : 𝓞 D.host.E, ϖ ≠ 0 → (∀ PP ∈ R.Q t₀, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) → ∃ ψP : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ, (∀ PP ∈ R.Q t₀, (ψP PP).IsPrimitive) ∧ ∀ t : T0, R.Q t = R.Q t₀ → ∀ (eg : AE D) (fg : WO (Vc D i) (Wc D i) → ℂ), IsIdemSum eg R.Pg → IsThetaAt R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) (cA D eg) (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) 1 (R.vacP i) (fun x => if IsHalf (cA D eg) x ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then omegaK R.Pg (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) else 0) fg → ∀ Gc : ℂ, Gc = (∏ PP ∈ R.Q t₀, ((Nat.card (kP PP) : ℂ) ^ ((Vc D i).rank * (Wc D i).rank) * (GlobalTheory.FlatConj.gaussP PP (ψP PP) (R.xiR t PP) (Wc D i).rank)⁻¹))⁻¹ → IsSBHalf eQ (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) (fun x => Gc * (if IsHalf eQ (x.map fun w => incA D (ϖ : D.host.E) * w) ∧ IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (x.map fun w => incA D (ϖ : D.host.E) * w)) then omegaFlat (R.Q t) (Wc D i).rank (R.xiR t) (fun PP => redM PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (x.map fun w => incA D (ϖ : D.host.E) * w))) else 0)) ∧ ∀ (Tm : (WO (Vc D i) (Wc D i) → ℂ) →ₗ[ℂ] (WO (Vc D i) (Wc D i) → ℂ)), IsPlaceModel R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) eQ (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) 1 fg Tm → R.vP i t = Tm (fun x => Gc * (if IsHalf eQ (x.map fun w => incA D (ϖ : D.host.E) * w) ∧ IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (x.map fun w => incA D (ϖ : D.host.E) * w)) then omegaFlat (R.Q t) (Wc D i).rank (R.xiR t) (fun PP => redM PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (x.map fun w => incA D (ϖ : D.host.E) * w))) else 0)) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC hQG i t₀ hV eQ heQ ϖ hϖ0 hϖ
  obtain ⟨ψP, Rs, hall⟩ := LiftFlatModel.exists_reps_pairing D G Pl0 T0 A Ks R F hC hQG i t₀ hV eQ heQ ϖ hϖ0 hϖ
  refine ⟨ψP, hall.1, fun t hQt eg fg heg hfg Gc hGc => ?_⟩
  rw [← hQt] at hall heQ hϖ hGc
  obtain ⟨hprim, hRs, hk, hbij, hiii, hiv, hv⟩ := hall
  letI : ∀ PP : Pl D.host.E, Fintype (kP PP) := fun PP => Fintype.ofFinite _
  have rV : (Vc D i).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  have rW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hfin := omegaQ_eq_gauss_mul_flat_transform D (R.Q t) (R.xiR t) ψP (Wc D i).rank (Vc D i).rank (by omega)
    (fun PP hPP => ⟨hprim PP hPP, GlobalTheory.ChainTw.RModel.xiR_ne R hC.lev t PP hPP⟩)
  rw [← hGc] at hfin
  have hE : (ϖ : D.host.E) ≠ 0 := fun h => hϖ0 (by exact_mod_cast h)
  have hu : IsUnit (incA D (ϖ : D.host.E)) := (Ne.isUnit hE).map (incA D)
  have F1 : ∀ x : WO (Vc D i) (Wc D i), IsHalf eQ (x.map fun w => incA D (ϖ : D.host.E) * w) ↔ IsHalf eQ x := by
    intro x
    constructor
    · intro h a b
      have h1 := h a b
      simp only [Matrix.map_apply] at h1
      rw [mul_left_comm] at h1
      exact hu.mul_left_cancel h1
    · intro h a b
      simp only [Matrix.map_apply]
      rw [mul_left_comm, h a b]
  have F2 : ∀ x : WO (Vc D i) (Wc D i), ((-x).map fun w => incA D (ϖ : D.host.E) * w) =
      -(x.map fun w => incA D (ϖ : D.host.E) * w) := by
    intro x
    ext a b
    simp [mul_neg]
  have hPsiNeg : ∀ u ∈ Rs, (if IsHalf eQ ((-u).map fun w => incA D (ϖ : D.host.E) * w) ∧
        IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) ((-u).map fun w => incA D (ϖ : D.host.E) * w)) then
        omegaFlat (R.Q t) (Wc D i).rank (R.xiR t) (fun PP => redM PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i)
          ((-u).map fun w => incA D (ϖ : D.host.E) * w))) else 0) =
      omegaFlat (R.Q t) (Wc D i).rank (R.xiR t) (fun PP => if h : PP ∈ R.Q t then
        -((fun PP : ↥(R.Q t) => redM PP.1 (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i)
          (u.map fun w => incA D (ϖ : D.host.E) * w))) ⟨PP, h⟩) else 0) := by
    intro u hu'
    have hh : IsHalf eQ ((-u).map fun w => incA D (ϖ : D.host.E) * w) := by
      rw [F2]
      exact LiftFlatModel.isHalf_neg ((F1 u).2 (hRs u hu').1)
    have hi : IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) ((-u).map fun w => incA D (ϖ : D.host.E) * w)) := by
      rw [F2, LiftFlatModel.frMapO_neg]
      exact LiftFlatModel.isIntM_neg (hRs u hu').2
    rw [if_pos ⟨hh, hi⟩]
    apply LiftFlatModel.omegaFlat_congr
    intro PP hPP
    rw [dite_eq_left hPP, F2, LiftFlatModel.frMapO_neg, LiftFlatModel.redM_neg _ (hRs u hu').2]

  have hA : ∀ x : WO (Vc D i) (Wc D i),
      (if IsHalf eQ (x.map fun w => incA D (ϖ : D.host.E) * w) ∧
        IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (x.map fun w => incA D (ϖ : D.host.E) * w)) then
        omegaFlat (R.Q t) (Wc D i).rank (R.xiR t) (fun PP => redM PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i)
          (x.map fun w => incA D (ϖ : D.host.E) * w))) else 0) =
      ∑ u ∈ Rs, (if IsHalf eQ ((-u).map fun w => incA D (ϖ : D.host.E) * w) ∧
        IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) ((-u).map fun w => incA D (ϖ : D.host.E) * w)) then
        omegaFlat (R.Q t) (Wc D i).rank (R.xiR t) (fun PP => redM PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i)
          ((-u).map fun w => incA D (ϖ : D.host.E) * w))) else 0) *
        halfInd eQ (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) (x + u) := by
    intro x
    by_cases hx : IsHalf eQ (x.map fun w => incA D (ϖ : D.host.E) * w) ∧
        IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (x.map fun w => incA D (ϖ : D.host.E) * w))
    · obtain ⟨u, ⟨huR, hured⟩, huniq⟩ := hbij (fun PP => -(redM PP.1 (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i)
        (x.map fun w => incA D (ϖ : D.host.E) * w))))
      have hxh : IsHalf eQ x := (F1 x).1 hx.1
      rw [Finset.sum_eq_single u]
      · have hmem : x + u ∈ latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) (fun _ => True) :=
          (hiii x hxh u huR).2 ⟨hx.2, fun PP hPP => by rw [hured ⟨PP, hPP⟩, neg_neg]⟩
        have hhalf : IsHalf eQ (x + u) := (LiftFlatModel.isHalf_add_iff (hRs u huR).1).2 hxh
        rw [show halfInd eQ (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) (x + u) = 1 from
          if_pos ⟨hmem, hhalf⟩, mul_one, hPsiNeg u huR, if_pos hx]
        apply LiftFlatModel.omegaFlat_congr
        intro PP hPP
        rw [dite_eq_left hPP]
        show _ = -(redM PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (u.map fun w => incA D (ϖ : D.host.E) * w)))
        rw [hured ⟨PP, hPP⟩, neg_neg]
      · intro u' hu' hne
        rw [show halfInd eQ (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) (x + u') = 0 from if_neg ?_,
          mul_zero]
        rintro ⟨hmem, -⟩
        obtain ⟨-, hred⟩ := (hiii x hxh u' hu').1 hmem
        exact hne (huniq u' ⟨hu', fun PP => by
          show _ = -(redM PP.1 (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (x.map fun w => incA D (ϖ : D.host.E) * w)))
          rw [hred PP.1 PP.2, neg_neg]⟩)
      · intro h
        exact absurd huR h
    · rw [if_neg hx]
      symm
      refine Finset.sum_eq_zero fun u hu' => ?_
      rw [show halfInd eQ (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) (x + u) = 0 from if_neg ?_,
        mul_zero]
      rintro ⟨hmem, hhalf⟩
      have hxh : IsHalf eQ x := (LiftFlatModel.isHalf_add_iff (hRs u hu').1).1 hhalf
      exact hx ⟨(F1 x).2 hxh, ((hiii x hxh u hu').1 hmem).1⟩
  have hB : ∀ x : WO (Vc D i) (Wc D i),
      (if IsHalf (cA D eQ) x ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then
        omegaQ (R.Q t) (Wc D i).rank (R.xiR t) (-1) (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x))
        else 0) =
      halfInd (cA D eQ) (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) x *
        ∑ u ∈ Rs, (Gc * (if IsHalf eQ ((-u).map fun w => incA D (ϖ : D.host.E) * w) ∧
          IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) ((-u).map fun w => incA D (ϖ : D.host.E) * w)) then
          omegaFlat (R.Q t) (Wc D i).rank (R.xiR t) (fun PP => redM PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i)
            ((-u).map fun w => incA D (ϖ : D.host.E) * w))) else 0)) * R.ψ (symplO (Vc D i) (Wc D i) x u) := by
    intro x
    by_cases hx : x ∈ latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) (fun _ => True) ∧ IsHalf (cA D eQ) x
    · have hint := (hiv x hx.2).1 hx.1
      rw [if_pos ⟨hx.2, hint⟩, show halfInd (cA D eQ) (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) x = 1 from
        if_pos hx, one_mul, hfin, Finset.mul_sum]
      symm
      refine Finset.sum_bij (fun u _ => fun PP : ↥(R.Q t) => redM PP.1 (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i)
          (u.map fun w => incA D (ϖ : D.host.E) * w))) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
      · intro a ha b hb hab
        exact (hbij _).unique ⟨ha, fun PP => rfl⟩ ⟨hb, fun PP => (congrFun hab PP).symm⟩
      · intro y _
        obtain ⟨u, ⟨hu', hred⟩, -⟩ := hbij y
        exact ⟨u, hu', funext hred⟩
      · intro u hu'
        rw [hPsiNeg u hu', hv x hx.2 hint u hu', ← Finset.univ_eq_attach]
        ring
    · rw [show halfInd (cA D eQ) (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) x = 0 from if_neg hx,
        zero_mul, if_neg]
      rintro ⟨hh, hint⟩
      exact hx ⟨(hiv x hh).2 hint, hh⟩
  have hθ := GlobalTheory.T.thetaLiftVector_isThetaFunction_twoStepModel D G Pl0 T0 A Ks R F hC hQG i t eg eQ fg heg heQ hfg
  have hvP := LiftFlatModel.thetaAt_sum hθ (fun u hu' => by rw [LiftFlatModel.cA_cA]; exact (hRs u hu').1) hB
  have hΨ : ∀ x : WO (Vc D i) (Wc D i), Gc * (if IsHalf eQ (x.map fun w => incA D (ϖ : D.host.E) * w) ∧
        IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (x.map fun w => incA D (ϖ : D.host.E) * w)) then
        omegaFlat (R.Q t) (Wc D i).rank (R.xiR t) (fun PP => redM PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i)
          (x.map fun w => incA D (ϖ : D.host.E) * w))) else 0) =
      ∑ u ∈ Rs, (Gc * (if IsHalf eQ ((-u).map fun w => incA D (ϖ : D.host.E) * w) ∧
        IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) ((-u).map fun w => incA D (ϖ : D.host.E) * w)) then
        omegaFlat (R.Q t) (Wc D i).rank (R.xiR t) (fun PP => redM PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i)
          ((-u).map fun w => incA D (ϖ : D.host.E) * w))) else 0)) *
        halfInd eQ (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) (x + u) := by
    intro x
    rw [hA x, Finset.mul_sum]
    exact Finset.sum_congr rfl fun u _ => by ring
  refine ⟨LiftFlatModel.isSBHalf_of_sum (fun u hu' => (hRs u hu').1) hΨ hk, fun Tm hTm => ?_⟩
  rw [LiftFlatModel.placeModel_sum hTm (fun u hu' => (hRs u hu').1) hΨ]
  exact hvP

theorem om_model_eq_dilate : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (t₀ : T0), VStd D i → ∀ (eQ : AE D) (es : Pl D.host.E → AE D), IsIdemSum eQ (R.Q t₀) → (∀ PP ∈ R.Q t₀, Formalism.L2.NTheta.IsIdemAt (es PP) PP) → eQ = ∑ PP ∈ R.Q t₀, es PP → ∀ ϖ : 𝓞 D.host.E, ϖ ≠ 0 → (∀ PP ∈ R.Q t₀, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) → ∃ (z : GA D (Vc D i)) (x : (AE D)ˣ), IsCentAt i (R.Q t₀) z ∧ (x : AE D) = 1 + ∑ PP ∈ R.Q t₀, cA D (es PP) * (incA D (star (ϖ : D.host.E)) ^ (Vc D i).rank - 1) ∧ ∀ t : T0, R.Q t = R.Q t₀ → ∀ (eg : AE D) (fg : WO (Vc D i) (Wc D i) → ℂ), IsIdemSum eg R.Pg → IsThetaAt R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) (cA D eg) (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) 1 (R.vacP i) (fun x => if IsHalf (cA D eg) x ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then omegaK R.Pg (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) else 0) fg → ∀ (Tm : (WO (Vc D i) (Wc D i) → ℂ) →ₗ[ℂ] (WO (Vc D i) (Wc D i) → ℂ)), IsPlaceModel R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) eQ (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) 1 fg Tm → ∀ Ψ : WO (Vc D i) (Wc D i) → ℂ, IsSBHalf eQ (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) Ψ → R.ωP i t (z, 1) (Tm Ψ) = ((((Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).2 x : Circle) : ℂ)⁻¹ * ((Real.sqrt ((((∏ PP ∈ R.Q t₀, Nat.card (kP PP)) ^ ((Vc D i).rank * (Wc D i).rank) : ℕ) : ℝ)) : ℝ) : ℂ)) • Tm (fun x => Ψ (x.map fun w => incA D ((ϖ : D.host.E)⁻¹) * w)) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC hQG i t₀ hV eQ es heQ hes hsum ϖ hϖ0 hϖ
  have hϖE : (ϖ : D.host.E) ≠ 0 := by exact_mod_cast hϖ0
  obtain ⟨⟨z, hz⟩, hall⟩ := (GlobalTheory.ZRep.central_reps D G Pl0 T0 A Ks R F hC hQG i t₀).2.2 eQ es (fun _ => ϖ) heQ hes hϖ hsum
  obtain ⟨⟨hcent, hsupp, ⟨x, hx, hxv⟩, -⟩, Λe, Λc, Xe, Xc, Re, Rr, -, -, hE, hCc⟩ := hall z hz _ rfl
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hR1, hR2, -, hcard, -⟩ := hE
  obtain ⟨-, -, -, hR3, -⟩ := hCc
  refine ⟨z, x, hcent, hxv, fun t hQt eg fg heg hfg Tm hTm Ψ hΨ => ?_⟩
  have hz' : mt (Vc D i) z = Matrix.diagonal (fun _ => eQ * incA D ((ϖ : D.host.E)⁻¹) + cA D eQ * cA D (incA D (ϖ : D.host.E)) +
      (1 - eQ - cA D eQ)) := by
    rw [hz]
    congr 1
    funext _
    have hs : incA D (star (ϖ : D.host.E)) = cA D (incA D (ϖ : D.host.E)) := rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, ← map_sum, ← hsum, hs]
    ring
  have hK := GlobalTheory.OnCmp.kerDat_tuple (i := i) hC.lev hC.thP t
  have heQ' : IsIdemSum eQ (R.Q t) := by rw [hQt]; exact heQ
  obtain ⟨hSV, hSW, hθ, hfix⟩ := GlobalTheory.T.tameKernel_typePlaceThetaVector_latticeFixed D G Pl0 T0 A Ks R F hC hQG i hV _ _ _ _ _ _ hK ⟨t, subset_rfl⟩ eg eQ fg heg heQ' hfg
  have hW := hC.thP.ωP i t
  have hN : (∏ PP ∈ R.Q t₀, Nat.card (kP PP)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun PP _ => Nat.card_pos.ne'
  have hNQ : ∀ PP ∈ R.Q t₀, ((∏ PP ∈ R.Q t₀, Nat.card (kP PP) : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    intro PP hPP
    obtain ⟨c, hc⟩ : Nat.card (kP PP) ∣ ∏ PP ∈ R.Q t₀, Nat.card (kP PP) := Finset.dvd_prod_of_mem _ hPP
    rw [hc, Nat.cast_mul]
    refine Ideal.mul_mem_right _ _ ?_
    have := Ideal.absNorm_mem PP.asIdeal
    rwa [Ideal.absNorm_apply, Submodule.cardQuot_apply] at this
  obtain ⟨-, -, hpull, hsb, hlat⟩ :=
    GlobalTheory.DilScalar.scalar_dil_facts D (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) (R.Q t₀) eQ heQ _ hN hNQ ϖ hϖE hϖ z hz'
  have hom := GlobalTheory.SumHecke.om_eq_sum_idemSum D R.ψ (Vc D i) (Wc D i) _ _ _ hW (R.ΛV i) (R.ΛW i) hSV hSW (R.Q t₀) eQ heQ z x hsupp hx
    Rr hR1 hR2 hR3 fg hθ hfix
  have hsum := GlobalTheory.T.sum_heisenbergTranslates_baseVector_eq_card_smul D R.ψ hW.std (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) hSV hSW (R.Q t₀) eQ heQ z hlat Rr hR1 hR2 hR3 fg Tm hTm
  rw [← hcard]
  have hvac : R.ωP i t (z, 1) fg = ((((Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).2 x : Circle) : ℂ)⁻¹ *
      ((Real.sqrt (Rr.card : ℝ) : ℝ) : ℂ)) •
      Tm (Formalism.IndefR.Fin.LevelGroupLemmas.actPull (z, (1 : GA D (Wc D i))) (halfInd eQ (Formalism.IndefR.Fin.latAll (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i)))) := by
    rw [hom, hsum, smul_smul]
    congr 1
    have hs : ((Rr.card : ℕ) : ℂ) = ((Real.sqrt (Rr.card : ℝ) : ℝ) : ℂ) * ((Real.sqrt (Rr.card : ℝ) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]
    rw [hs]
    simp only [splitFacO, map_one, mul_one, Circle.coe_mul, Circle.coe_inv]
    by_cases h0 : ((Real.sqrt (Rr.card : ℝ) : ℝ) : ℂ) = 0
    · rw [h0]; simp
    · field_simp
  have h := GlobalTheory.T.weilRep_apply_eq_smul_of_halfIndicator_base D R.ψ (Vc D i) (Wc D i) _ _ _ hW (R.ΛV i) (R.ΛW i) hSV hSW (R.Q t₀) eQ heQ fg hθ hfix Tm hTm (z, 1) _ hsb
    hvac Ψ hΨ
  rw [h, hpull Ψ hΨ.1]

theorem scalar_identity {ι : Type} (Q : Finset ι) (q : ι → ℕ) (g : ι → ℂ) (b ξ : ℂ) (n a : ℕ) (hq : ∀ P ∈ Q, q P ≠ 0) :
    ((b * ξ⁻¹ * ((Real.sqrt ((((∏ P ∈ Q, q P) ^ (n * (2 * a + 1)) : ℕ) : ℝ)) : ℝ) : ℂ)) *
      (∏ P ∈ Q, ((q P : ℂ) ^ (n * (2 * a + 1)) * (g P)⁻¹))⁻¹)⁻¹ =
    (b * ∏ P ∈ Q, (((Real.sqrt (q P : ℝ) : ℝ) : ℂ)⁻¹) ^ n)⁻¹ * (((∏ P ∈ Q, q P) ^ (n * a) : ℕ) : ℂ) *
      (∏ P ∈ Q, g P) ^ (-1 : ℤ) * ξ := by
  set S : ℂ := ∏ P ∈ Q, ((Real.sqrt (q P : ℝ) : ℝ) : ℂ) with hS
  have hSr : S = ((∏ P ∈ Q, Real.sqrt (q P : ℝ) : ℝ) : ℂ) := by rw [hS, Complex.ofReal_prod]
  have hsq : (∏ P ∈ Q, Real.sqrt (q P : ℝ)) ^ 2 = ((∏ P ∈ Q, q P : ℕ) : ℝ) := by
    rw [← Finset.prod_pow, Nat.cast_prod]
    exact Finset.prod_congr rfl fun P _ => Real.sq_sqrt (Nat.cast_nonneg _)
  have hM : ((∏ P ∈ Q, q P : ℕ) : ℂ) = S ^ 2 := by
    rw [hSr, ← Complex.ofReal_pow, hsq, Complex.ofReal_natCast]
  have hS0 : S ≠ 0 := fun h => by
    rw [h, zero_pow two_ne_zero, Nat.cast_eq_zero] at hM
    exact Finset.prod_ne_zero_iff.2 hq hM
  have h1 : ((Real.sqrt ((((∏ P ∈ Q, q P) ^ (n * (2 * a + 1)) : ℕ) : ℝ)) : ℝ) : ℂ) = S ^ (n * (2 * a + 1)) := by
    rw [Nat.cast_pow, ← hsq, ← pow_mul, mul_comm 2, pow_mul,
      Real.sqrt_sq (pow_nonneg (Finset.prod_nonneg fun P _ => Real.sqrt_nonneg _) _), hSr, Complex.ofReal_pow]
  have h2 : (∏ P ∈ Q, ((q P : ℂ) ^ (n * (2 * a + 1)) * (g P)⁻¹)) = (S ^ 2) ^ (n * (2 * a + 1)) * (∏ P ∈ Q, g P)⁻¹ := by
    rw [Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_inv_distrib, ← hM, Nat.cast_prod]
  have h3 : (∏ P ∈ Q, (((Real.sqrt (q P : ℝ) : ℝ) : ℂ)⁻¹) ^ n) = (S ^ n)⁻¹ := by
    rw [Finset.prod_pow, Finset.prod_inv_distrib, inv_pow]
  have h4 : (S ^ 2) ^ (n * (2 * a + 1)) = S ^ (n * (2 * a + 1)) * (S ^ n * (S ^ 2) ^ (n * a)) := by ring
  rw [h1, h2, h3, Nat.cast_pow, hM, _root_.zpow_neg_one, h4]
  have h5 : S ^ (n * (2 * a + 1)) ≠ 0 := pow_ne_zero _ hS0
  generalize S ^ (n * (2 * a + 1)) = U at h5
  simp only [mul_inv, inv_inv]
  calc _ = (U⁻¹ * U) * (b⁻¹ * S ^ n * (S ^ 2) ^ (n * a) * (∏ P ∈ Q, g P)⁻¹ * ξ) := by ring
    _ = _ := by rw [inv_mul_cancel₀ h5, one_mul]

theorem flat_eq_gauss_smul_om : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (t : T0), VStd D i → ∃ (z : GA D (Vc D i)) (B : ℂ) (ε : ℤ) (r : ℕ) (ψP : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ), IsCentAt i (R.Q t) z ∧ (∀ τ : ℂ ≃+* ℂ, FixBase T R i τ → τ B = B) ∧ (∀ PP ∈ R.Q t, (ψP PP).IsPrimitive) ∧ ∀ t' : T0, R.Q t' = R.Q t → ∀ f', IsFlatVec R i t' f' → ∃ s : (AE D)ˣ, f' = (B * (∏ PP ∈ R.Q t, GlobalTheory.FlatConj.gaussP PP (ψP PP) (R.xiR t' PP) r) ^ ε * ((R.xi t' s : Circle) : ℂ)) • R.ωP i t' (z, 1) (R.vP i t') := by
  intro D G _ _ Pl0 T0 A T _ R F hC hQG i t hV
  obtain ⟨eQ, heQ⟩ := (GlobalTheory.ZRep.central_reps D G Pl0 T0 A T.Q.c.F R F hC hQG i t).1
  obtain ⟨es, hes, hsum⟩ := heQ.1
  obtain ⟨ϖ, hϖ0, hϖ⟩ := GlobalTheory.FlatLift.exists_unif D.host.E (R.Q t)
  have hϖE : (ϖ : D.host.E) ≠ 0 := by exact_mod_cast hϖ0
  obtain ⟨z, x, hz, hx, hact⟩ := om_model_eq_dilate D G Pl0 T0 A T.Q.c.F R F hC hQG i t hV eQ es heQ hes hsum ϖ hϖ0 hϖ
  obtain ⟨ψP, hprim, hlift⟩ := lift_eq_gauss_model_flat D G Pl0 T0 A T.Q.c.F R F hC hQG i t hV eQ heQ ϖ hϖ0 hϖ
  obtain ⟨b, hb, hχ, -⟩ := GlobalTheory.FlatConst.flat_const D G Pl0 T0 A T R F hC i t es (fun _ => ϖ) (Vc D i).rank x hes
    (by rw [← hsum]; exact heQ.2) hϖ hx
  have hcardN : ∀ PP : Pl D.host.E, Ideal.absNorm PP.asIdeal = Nat.card (kP PP) := fun PP => by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  simp only [hcardN] at hb
  obtain ⟨a, ha⟩ : ∃ a, (Wc D i).rank = 2 * a + 1 := by
    have rW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
    obtain ⟨a, ha⟩ := D.R.k_even
    obtain ⟨c, hc⟩ := D.R.m_even
    have h2 := D.R.two_le_m
    exact ⟨a + c - 1, by rw [rW]; simp only [Ranks.r]; omega⟩
  refine ⟨z, (b * ∏ PP ∈ R.Q t, (((Real.sqrt (Nat.card (kP PP) : ℝ) : ℝ) : ℂ)⁻¹) ^ (Vc D i).rank)⁻¹ *
    (((∏ PP ∈ R.Q t, Nat.card (kP PP)) ^ ((Vc D i).rank * a) : ℕ) : ℂ), -1, (Wc D i).rank, ψP, hz, fun τ hτ => ?_, hprim,
    fun t' hQt f hf => ⟨x, ?_⟩⟩
  · rw [map_mul, map_inv₀, hb τ hτ, map_natCast]
  obtain ⟨eg, eQ', fg, heg, heQ', hfg, hf⟩ := hf
  obtain rfl : eQ = eQ' := GlobalTheory.ConjDatum.idemSum_unique (Vc D i) (hQt ▸ heQ') heQ
  obtain ⟨hSB, hvP⟩ := hlift t' hQt eg fg heg hfg _ rfl
  obtain ⟨Tm, hTm⟩ := hf.1
  have hfT := hf.2 Tm hTm
  have hvT := hvP Tm hTm
  have hactT := hact t' hQt eg fg heg hfg Tm hTm _ hSB
  have hid := scalar_identity (R.Q t) (fun PP => Nat.card (kP PP))
    (fun PP => GlobalTheory.FlatConj.gaussP PP (ψP PP) (R.xiR t' PP) (Wc D i).rank) b ((R.xi t' x : Circle) : ℂ) (Vc D i).rank a
    (fun PP _ => Nat.card_pos.ne')
  rw [← ha, ← GlobalTheory.FlatConst.chr_inv_val, ← hχ t'] at hid
  rw [← hid]
  generalize hκ : (((Lift.chrTh (R.toLevCh.mu t') R.eta ((i : ℕ) + 1)).2 x : Circle) : ℂ)⁻¹ * ((Real.sqrt ((((∏ PP ∈ R.Q t, Nat.card (kP PP)) ^ ((Vc D i).rank * (Wc D i).rank) : ℕ) : ℝ)) : ℝ) : ℂ) = κ at hactT ⊢
  generalize hGc : (∏ PP ∈ R.Q t, ((Nat.card (kP PP) : ℂ) ^ ((Vc D i).rank * (Wc D i).rank) * (GlobalTheory.FlatConj.gaussP PP (ψP PP) (R.xiR t' PP) (Wc D i).rank)⁻¹))⁻¹ = Gc at hactT hvT ⊢
  have hκ0 : κ ≠ 0 := by
    rw [← hκ]
    refine mul_ne_zero (inv_ne_zero (Circle.coe_ne_zero _)) ?_
    rw [Complex.ofReal_ne_zero, Real.sqrt_ne_zero (Nat.cast_nonneg _), Nat.cast_ne_zero]
    exact pow_ne_zero _ (Finset.prod_ne_zero_iff.2 fun PP _ => Nat.card_pos.ne')
  have hG0 : Gc ≠ 0 := by
    rw [← hGc]
    refine inv_ne_zero (Finset.prod_ne_zero_iff.2 fun PP hPP => mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 Nat.card_pos.ne'))
      (inv_ne_zero (gaussP_ne_zero _ _ _ _ (hprim PP hPP) ?_)))
    exact GlobalTheory.ChainTw.RModel.xiR_ne R hC.lev t' PP (hQt ▸ hPP)
  have hne : κ * Gc ≠ 0 := mul_ne_zero hκ0 hG0
  have hcomp : ∀ x : WO (Vc D i) (Wc D i),
      ((x.map fun w => incA D ((ϖ : D.host.E)⁻¹) * w).map fun w => incA D (ϖ : D.host.E) * w) = x := by
    intro x
    ext a b
    simp only [Matrix.map_apply, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hϖE, map_one, one_mul]
  rw [hvT, hactT]
  simp only [hcomp]
  have hsm : (fun x : WO (Vc D i) (Wc D i) => Gc * (if IsHalf eQ x ∧ IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then omegaFlat (R.Q t') (Wc D i).rank (R.xiR t') (fun PP => redM PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) else 0)) =
      Gc • (fun x : WO (Vc D i) (Wc D i) => if IsHalf eQ x ∧ IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then omegaFlat (R.Q t') (Wc D i).rank (R.xiR t') (fun PP => redM PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) else 0) := rfl
  rw [hsm, map_smul, ← hfT, smul_smul, smul_smul, mul_assoc (κ * Gc)⁻¹, inv_mul_cancel₀ hne, one_smul]

end GlobalTheory.FlatForm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlatVectorEqGaussSumSmulCentralTranslateStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatVector_eq_gaussSum_smul_centralTranslate : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (t : T0), VStd D i → ∃ (z : GA D (Vc D i)) (B : ℂ) (ε : ℤ) (r : ℕ) (ψP : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ), IsCentAt i (R.Q t) z ∧ (∀ τ : ℂ ≃+* ℂ, FixBase T R i τ → τ B = B) ∧ (∀ PP ∈ R.Q t, (ψP PP).IsPrimitive) ∧ ∀ t' : T0, R.Q t' = R.Q t → ∀ f', IsFlatVec R i t' f' → ∃ s : (AE D)ˣ, f' = (B * (∏ PP ∈ R.Q t, GlobalTheory.FlatConj.gaussP PP (ψP PP) (R.xiR t' PP) r) ^ ε * ((R.xi t' s : Circle) : ℂ)) • R.ωP i t' (z, 1) (R.vP i t') := by
  first | exact @GlobalTheory.FlatForm.flat_eq_gauss_smul_om | exact GlobalTheory.FlatForm.flat_eq_gauss_smul_om | (intros; apply GlobalTheory.FlatForm.flat_eq_gauss_smul_om <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeChoiceFlatVectorFactoredForm
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.FlatConj

theorem flatVec_factored_form : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (t : T0), VStd D i → ∃ (z : GA D (Vc D i)) (B : ℂ) (ε : ℤ) (r : ℕ) (ψP : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ), IsCentAt i (R.Q t) z ∧ (∀ τ : ℂ ≃+* ℂ, FixBase T R i τ → τ B = B) ∧ (∀ PP ∈ R.Q t, (ψP PP).IsPrimitive) ∧ ∀ t' : T0, R.Q t' = R.Q t → ∀ f', IsFlatVec R i t' f' → ∃ s : (AE D)ˣ, f' = (B * (∏ PP ∈ R.Q t, GlobalTheory.FlatConj.gaussP PP (ψP PP) (R.xiR t' PP) r) ^ ε * ((R.xi t' s : Circle) : ℂ)) • R.ωP i t' (z, 1) (R.vP i t') :=
  GlobalTheory.T.flatVector_eq_gaussSum_smul_centralTranslate

end GlobalTheory.FlatConj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeChoiceFlatVectorFactoredFormStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChoice_flatVector_factoredForm : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (t : T0), VStd D i → ∃ (z : GA D (Vc D i)) (B : ℂ) (ε : ℤ) (r : ℕ) (ψP : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ), IsCentAt i (R.Q t) z ∧ (∀ τ : ℂ ≃+* ℂ, FixBase T R i τ → τ B = B) ∧ (∀ PP ∈ R.Q t, (ψP PP).IsPrimitive) ∧ ∀ t' : T0, R.Q t' = R.Q t → ∀ f', IsFlatVec R i t' f' → ∃ s : (AE D)ˣ, f' = (B * (∏ PP ∈ R.Q t, GlobalTheory.FlatConj.gaussP PP (ψP PP) (R.xiR t' PP) r) ^ ε * ((R.xi t' s : Circle) : ℂ)) • R.ωP i t' (z, 1) (R.vP i t') := by
  first | exact @GlobalTheory.FlatConj.flatVec_factored_form | exact GlobalTheory.FlatConj.flatVec_factored_form | (intros; apply GlobalTheory.FlatConj.flatVec_factored_form <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeChoiceFlatScalarConjTwist
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical


set_option maxHeartbeats 4000000 in
theorem GlobalTheory.FlatConj.flat_conj : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (τ : ℂ ≃+* ℂ) (t t' : T0), VStd D i → FixBase T R i τ → ConjTup R τ t t' → ∀ f f', IsFlatVec R i t f → IsFlatVec R i t' f' → ∃ (z : GA D (Vc D i)) (c c' : ℂ) (s : (AE D)ˣ), IsCentAt i (R.Q t) z ∧ f = c • R.ωP i t (z, 1) (R.vP i t) ∧ f' = c' • R.ωP i t' (z, 1) (R.vP i t') ∧ c' = ((R.xi t' s : Circle) : ℂ) * τ c := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hC hQG i τ t t' hV hFix hct f f' hf hf'
  obtain ⟨z, B, ε, r, ψP, hz, hB, hprim, hform⟩ := GlobalTheory.T.heckeChoice_flatVector_factoredForm D G Pl0 T0 A T R F hC hQG i t hV
  obtain ⟨s1, e1⟩ := hform t rfl f hf
  obtain ⟨s2, e2⟩ := hform t' hct.1 f' hf'
  obtain ⟨h1, hne, -, -⟩ := GlobalTheory.ConjRes.conj_res D G Pl0 T0 A T R F κ v₀ hC τ t t' hct
  have hg : ∀ PP ∈ R.Q t, ∃ a : (kP PP)ˣ, τ (GlobalTheory.FlatConj.gaussP PP (ψP PP) (R.xiR t PP) r) =
      ((R.xiR t' PP a : ℂˣ) : ℂ) ^ r * GlobalTheory.FlatConj.gaussP PP (ψP PP) (R.xiR t' PP) r := by
    intro PP hP
    obtain ⟨a, -, ha⟩ := (@GlobalTheory.complexMatrixGaussSum_norm_integral_galois (kP PP) (GlobalTheory.FlatConj.resField PP) (GlobalTheory.FlatConj.resFintype PP) (Classical.decEq _)
      (ψP PP) (R.xiR t PP) r (hprim PP hP) (hne PP hP) _ rfl).2.2.2 τ (R.xiR t' PP) (h1 PP hP)
    exact ⟨a, ha⟩
  choose a ha using hg
  let v : Pl D.host.E → ℂ := fun PP => if h : PP ∈ R.Q t then ((R.xiR t' PP (a PP h) : ℂˣ) : ℂ) else 1
  obtain ⟨s3, e3⟩ := GlobalTheory.FlatConj.prod_val (R.xi t') (R.Q t) v fun PP hP => by
    simp only [v, dif_pos hP]
    exact GlobalTheory.FlatConj.xiR_val hC t' PP (hct.1 ▸ hP) _
  have hprod : ∏ PP ∈ R.Q t, τ (GlobalTheory.FlatConj.gaussP PP (ψP PP) (R.xiR t PP) r) =
      (∏ PP ∈ R.Q t, v PP) ^ r * ∏ PP ∈ R.Q t, GlobalTheory.FlatConj.gaussP PP (ψP PP) (R.xiR t' PP) r := by
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun PP hP => ?_
    simp only [v, dif_pos hP]
    exact ha PP hP
  refine ⟨z, _, _, s2 * s1⁻¹ * s3 ^ (-((r : ℤ) * ε)), hz, e1, e2, ?_⟩
  have hX : ((R.xi t' s1 : Circle) : ℂ) ≠ 0 := Circle.coe_ne_zero _
  have hV3 : ((R.xi t' s3 : Circle) : ℂ) ≠ 0 := Circle.coe_ne_zero _
  have key : τ (B * (∏ PP ∈ R.Q t, GlobalTheory.FlatConj.gaussP PP (ψP PP) (R.xiR t PP) r) ^ ε * ((R.xi t s1 : Circle) : ℂ)) =
      B * ((∏ PP ∈ R.Q t, v PP) ^ r * ∏ PP ∈ R.Q t, GlobalTheory.FlatConj.gaussP PP (ψP PP) (R.xiR t' PP) r) ^ ε *
        ((R.xi t' s1 : Circle) : ℂ) := by
    rw [map_mul, map_mul, map_zpow₀, map_prod, hprod, hB τ hFix, ← hct.2 s1]
  rw [key, e3]
  simp only [map_mul, map_inv, map_zpow, Circle.coe_mul, Circle.coe_inv, Circle.coe_zpow]
  rw [mul_zpow, ← zpow_natCast, ← _root_.zpow_mul, _root_.zpow_neg]
  have hW : ((R.xi t' s3 : Circle) : ℂ) ^ ((r : ℤ) * ε) ≠ 0 := zpow_ne_zero _ hV3
  field_simp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeChoiceFlatScalarConjTwistStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChoice_flatScalar_conj_twist : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (τ : ℂ ≃+* ℂ) (t t' : T0), VStd D i → FixBase T R i τ → ConjTup R τ t t' → ∀ f f', IsFlatVec R i t f → IsFlatVec R i t' f' → ∃ (z : GA D (Vc D i)) (c c' : ℂ) (s : (AE D)ˣ), IsCentAt i (R.Q t) z ∧ f = c • R.ωP i t (z, 1) (R.vP i t) ∧ f' = c' • R.ωP i t' (z, 1) (R.vP i t') ∧ c' = ((R.xi t' s : Circle) : ℂ) * τ c := by
  first | exact @GlobalTheory.FlatConj.flat_conj | exact GlobalTheory.FlatConj.flat_conj | (intros; apply GlobalTheory.FlatConj.flat_conj <;> assumption)
end
