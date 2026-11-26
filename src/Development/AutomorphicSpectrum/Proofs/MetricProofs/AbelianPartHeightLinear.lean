module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsometryPreservesHermitianAndAction
public import GroundTheory.HeightsAndTheta.Heights.Slopes.PCanonicalFiltration
public import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PInteriorDichotomy
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsStokesGeo
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.CxSimple

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.AbelianPartHeightLinear
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp

open NumberField GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights Polynomial

theorem exists_integral_generator (E : Type) [Field E] [NumberField E] :
    ∃ (θ : 𝓞 E) (m : ℤ[X]), m.Monic ∧ aeval θ m = 0 ∧ m.natDegree = Module.finrank ℚ E ∧
      ∀ a : 𝓞 E, ∃ (n : ℤ) (P : ℤ[X]), n ≠ 0 ∧ (n : 𝓞 E) * a = aeval θ P := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ E
  have halg : IsAlgebraic ℤ α :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic α)
  obtain ⟨n, hn, hint⟩ := halg.exists_integral_multiple
  set β : E := n • α with hβ
  have hnq : ((n : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hn
  have hαβ : α = ((n : ℚ))⁻¹ • β := by
    rw [hβ, ← Int.cast_smul_eq_zsmul ℚ n α, smul_smul, inv_mul_cancel₀ hnq, one_smul]
  have htop : IntermediateField.adjoin ℚ {β} = ⊤ := by
    rw [eq_top_iff, ← hα, IntermediateField.adjoin_simple_le_iff, hαβ]
    exact (IntermediateField.adjoin ℚ {β}).smul_mem (IntermediateField.mem_adjoin_simple_self ℚ β)
  have hintQ : IsIntegral ℚ β := Algebra.IsIntegral.isIntegral β
  let θ : 𝓞 E := ⟨β, hint⟩
  have hinj : Function.Injective (algebraMap (𝓞 E) E) := RingOfIntegers.coe_injective
  have hcoe : ∀ P : ℤ[X], algebraMap (𝓞 E) E (aeval θ P) = aeval β P := fun P => by
    have := aeval_algHom_apply (IsScalarTower.toAlgHom ℤ (𝓞 E) E) θ P
    exact this.symm
  refine ⟨θ, minpoly ℤ β, minpoly.monic hint, ?_, ?_, ?_⟩
  · apply hinj
    rw [hcoe, minpoly.aeval, map_zero]
  · have h1 := minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hint
    have h2 := IntermediateField.adjoin.finrank hintQ
    rw [htop, IntermediateField.finrank_top', h1, (minpoly.monic hint).natDegree_map] at h2
    exact h2.symm
  · intro a
    have ha : (a : E) ∈ Algebra.adjoin ℚ {β} := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hintQ.isAlgebraic, htop]
      exact Algebra.mem_top
    rw [Algebra.adjoin_singleton_eq_range_aeval] at ha
    obtain ⟨Q, hQ⟩ := ha
    obtain ⟨b, hbmem, hb⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) Q
    refine ⟨b, IsLocalization.integerNormalization (nonZeroDivisors ℤ) Q,
      nonZeroDivisors.coe_ne_zero ⟨b, hbmem⟩, ?_⟩
    apply hinj
    have hQ' : aeval β Q = (a : E) := hQ
    rw [hcoe, ← aeval_map_algebraMap ℚ, hb, map_mul, map_intCast, zsmul_eq_mul, map_mul, map_intCast, hQ']

theorem ker_aeval_prod_le {L V : Type} [Field L] [AddCommGroup V] [Module L V] (T : Module.End L V) (S : Finset L) :
    LinearMap.ker (aeval T (∏ c ∈ S, (X - C c))) ≤ ⨆ c ∈ S, Module.End.eigenspace T c := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [Module.End.one_eq_id]
  | insert c S hc ih =>
    rw [Finset.prod_insert hc]
    have hcop : IsCoprime (X - C c) (∏ d ∈ S, (X - C d)) :=
      IsCoprime.prod_right fun d hd => isCoprime_X_sub_C_of_isUnit_sub
        (sub_ne_zero.2 (fun h : c = d => hc (by rw [h]; exact hd))).isUnit
    rw [← sup_ker_aeval_eq_ker_aeval_mul_of_coprime T hcop, Finset.iSup_insert]
    refine sup_le_sup ?_ ih
    intro x hx
    rw [LinearMap.mem_ker] at hx
    rw [Module.End.mem_eigenspace_iff]
    simpa [sub_eq_zero] using hx

theorem iSup_eigSp_eq_top {E L V ι : Type} [Field E] [NumberField E] [Field L] [CharZero L] [AddCommGroup V] [Module L V]
    [Fintype ι] (ρ : 𝓞 E →+* Module.End L V) (σ : ι → (𝓞 E →+* L)) (hσ : Function.Injective σ)
    (hcard : Fintype.card ι = Module.finrank ℚ E) : ⨆ s, eigSp ρ (σ s) = ⊤ := by
  classical
  obtain ⟨θ, m, hmon, hm0, hdeg, hgen⟩ := exists_integral_generator E
  have hagree : ∀ (τ : 𝓞 E →+* L) (P : ℤ[X]), τ (aeval θ P) = aeval (τ θ) P := fun τ P =>
    (aeval_algHom_apply τ.toIntAlgHom θ P).symm
  have hinjc : Function.Injective fun s => σ s θ := by
    intro s t hst
    apply hσ
    ext a
    obtain ⟨n, P, hn, hP⟩ := hgen a
    have h1 := hagree (σ s) P
    have h2 := hagree (σ t) P
    have hst' : σ s θ = σ t θ := hst
    rw [hst', ← h2, ← hP, map_mul, map_mul, map_intCast, map_intCast] at h1
    exact mul_left_cancel₀ (by exact_mod_cast hn) h1
  set S : Finset L := Finset.univ.image fun s => σ s θ with hS
  have hScard : S.card = Module.finrank ℚ E := by
    rw [hS, Finset.card_image_of_injective _ hinjc, Finset.card_univ, hcard]
  set mL : L[X] := m.map (algebraMap ℤ L) with hmL
  have hmLmon : mL.Monic := hmon.map _
  have hmLdeg : mL.natDegree = Module.finrank ℚ E := by rw [hmL, hmon.natDegree_map, hdeg]
  have hprodmon : (∏ c ∈ S, (X - C c)).Monic := monic_prod_of_monic _ _ fun c _ => monic_X_sub_C c
  have hprodeg : (∏ c ∈ S, (X - C c) : L[X]).natDegree = Module.finrank ℚ E := by
    rw [natDegree_prod_of_monic _ _ fun c _ => monic_X_sub_C c]
    simp [hScard]
  have hdvd : (∏ c ∈ S, (X - C c)) ∣ mL := by
    refine Finset.prod_dvd_of_coprime ?_ ?_
    · intro c _ d _ hcd
      exact isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.2 hcd).isUnit
    · intro c hc
      obtain ⟨s, -, rfl⟩ := Finset.mem_image.1 hc
      rw [dvd_iff_isRoot, IsRoot.def, hmL, eval_map_algebraMap, ← hagree, hm0, map_zero]
  have heq : mL = ∏ c ∈ S, (X - C c) :=
    eq_of_monic_of_dvd_of_natDegree_le hprodmon hmLmon hdvd (by rw [hmLdeg, hprodeg])
  have hρ : ∀ P : ℤ[X], aeval (ρ θ) P = ρ (aeval θ P) := fun P =>
    aeval_algHom_apply ρ.toIntAlgHom θ P
  have hT : aeval (ρ θ) (∏ c ∈ S, (X - C c)) = 0 := by
    rw [← heq, hmL, aeval_map_algebraMap, hρ, hm0, map_zero]
  rw [eq_top_iff]
  have hker : (⊤ : Submodule L V) ≤ LinearMap.ker (aeval (ρ θ) (∏ c ∈ S, (X - C c))) := by
    rw [hT, LinearMap.ker_zero]
  refine hker.trans ((ker_aeval_prod_le (ρ θ) S).trans (iSup₂_le fun c hc => ?_))
  obtain ⟨s, -, rfl⟩ := Finset.mem_image.1 hc
  refine le_trans ?_ (le_iSup _ s)
  intro x hx
  rw [Module.End.mem_eigenspace_iff] at hx
  have hpow : ∀ k : ℕ, ((ρ θ) ^ k) x = (σ s θ) ^ k • x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hx, smul_smul, pow_succ]
  have hP : ∀ P : ℤ[X], (aeval (ρ θ) P) x = (aeval (σ s θ) P) • x := by
    intro P
    induction P using Polynomial.induction_on' with
    | add p q hp hq => simp only [map_add (f := _), LinearMap.add_apply, hp, hq, add_smul]
    | monomial k a =>
      simp only [aeval_monomial, Module.End.mul_apply, hpow, eq_intCast, map_intCast]
      rw [Module.End.intCast_apply, mul_smul, Int.cast_smul_eq_zsmul]
  simp only [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    sub_eq_zero]
  intro a
  obtain ⟨n, P, hn, hnP⟩ := hgen a
  have h2 := hP P
  rw [hρ, ← hagree, ← hnP, map_mul, map_mul, map_intCast, map_intCast] at h2
  rw [Module.End.mul_apply, Module.End.intCast_apply, mul_smul, ← Int.cast_smul_eq_zsmul L n] at h2
  exact smul_right_injective V (by exact_mod_cast hn : (n : L) ≠ 0) h2

section Lattice

variable {L V : Type} [Field L] [NumberField L] [AddCommGroup V] [Module L V] [Module (𝓞 L) V]
  [IsScalarTower (𝓞 L) L V]

theorem exists_smul_mem_of_span {Λ : Submodule (𝓞 L) V} (h : Submodule.span L (Λ : Set V) = ⊤) (p : V) :
    ∃ b : 𝓞 L, b ≠ 0 ∧ b • p ∈ Λ :=
  by apply _root_.UpperTheory.Reformulated.B.ClearDenominatorsLattice.exists_integer_smul_mem_of_span_top <;> assumption

end Lattice

namespace LinPt

variable {E L Ψ : Type} [Field E] [NumberField E] [Field L] [NumberField L] [Fintype Ψ] {V : Type} [AddCommGroup V]
  [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (A : LinPt E L Ψ V)

theorem img_eq (s : Ψ ⊕ Ψ) :
    A.img s = (((eigSp A.ρ (A.σ s)).restrictScalars (𝓞 L)).comap A.Λ.subtype).map A.f := by
  unfold img eig
  rw [Submodule.comap_inf, Submodule.comap_subtype_self, top_inf_eq]

theorem saturation_iSup_img (hcard : 2 * Fintype.card Ψ = Module.finrank ℚ E) :
    CanonicalFiltration.saturation A.Bq (⨆ s, A.img s) = ⊤ := by
  have htop := iSup_eigSp_eq_top A.ρ A.σ A.σ_bij.1 (by rw [Fintype.card_sum, ← hcard]; ring)
  have key : ∀ x : V, ∃ b : 𝓞 L, b ≠ 0 ∧ ∃ h : b • x ∈ A.Λ, A.f ⟨b • x, h⟩ ∈ ⨆ s, A.img s := by
    intro x
    have hx : x ∈ ⨆ s, eigSp A.ρ (A.σ s) := htop ▸ Submodule.mem_top
    refine Submodule.iSup_induction _
      (motive := fun x => ∃ b : 𝓞 L, b ≠ 0 ∧ ∃ h : b • x ∈ A.Λ, A.f ⟨b • x, h⟩ ∈ ⨆ s, A.img s) hx ?_ ?_ ?_
    · intro s x hx
      obtain ⟨b, hb, hbx⟩ := exists_smul_mem_of_span A.span x
      refine ⟨b, hb, hbx, Submodule.mem_iSup_of_mem s ?_⟩
      rw [img_eq]
      refine Submodule.mem_map_of_mem ?_
      show b • x ∈ eigSp A.ρ (A.σ s)
      rw [← algebraMap_smul L b x]
      exact Submodule.smul_mem _ _ hx
    · have h0 : (1 : 𝓞 L) • (0 : V) ∈ A.Λ := by simp
      refine ⟨1, one_ne_zero, h0, ?_⟩
      have e : (⟨(1 : 𝓞 L) • (0 : V), h0⟩ : A.Λ) = 0 := Subtype.ext (by simp)
      rw [e, map_zero]
      exact Submodule.zero_mem _
    · rintro x y ⟨b, hb, hbx, hfx⟩ ⟨c, hc, hcy, hfy⟩
      have e0 : (b * c) • (x + y) = c • (b • x) + b • (c • y) := by
        rw [smul_add, smul_smul, smul_smul, mul_comm c b]
      have h1 : (b * c) • (x + y) ∈ A.Λ := by
        rw [e0]
        exact A.Λ.add_mem (A.Λ.smul_mem _ hbx) (A.Λ.smul_mem _ hcy)
      have e : (⟨(b * c) • (x + y), h1⟩ : A.Λ) = c • ⟨b • x, hbx⟩ + b • ⟨c • y, hcy⟩ := Subtype.ext e0
      refine ⟨b * c, mul_ne_zero hb hc, h1, ?_⟩
      rw [e, map_add (f := _), map_smul, map_smul]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ hfx) (Submodule.smul_mem _ _ hfy)
  rw [eq_top_iff]
  intro y _
  obtain ⟨a, x, ha, hfx⟩ := A.full y
  obtain ⟨b, hb, hbx, hf⟩ := key x
  refine ⟨b * a, mul_ne_zero hb ha, ?_⟩
  have e : (⟨b • (x : V), hbx⟩ : A.Λ) = b • x := Subtype.ext rfl
  rw [e, map_smul, hfx, smul_smul] at hf
  exact hf

end LinPt

end GlobalTheory.CompanionTheory.Ar.Cusp
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagHeightPolynomialWeightForm
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagHeightPolynomialWeightForm
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

namespace FlLines

section Geo

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem exists_integralCombination_of_mem_completedLattice {A B D : Type} [Fintype A] [Fintype B] [Fintype D] (ca : A → ℤ) (bb : A → D → ℤ) (P : B → ℤ)
    (G : D → B → ℤ) :
    ∑ k, (∑ a, ca a * bb a k) * ∑ w, P w * G k w = ∑ a, ∑ w, (P w * ca a) * ∑ k, bb a k * G k w := by
  have h1 : ∀ k, (∑ a, ca a * bb a k) * ∑ w, P w * G k w = ∑ a, ∑ w, (ca a * bb a k) * (P w * G k w) :=
    fun k => Finset.sum_mul_sum _ _ _ _
  simp only [h1, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun k _ => by ring

theorem geoNum_polar {σ : Type} [Fintype σ] (n : ℕ) (V : Ideal (MRing ι)) (c : Fin n → σ → ℤ) (b : σ → K → ℤ) :
    geoNum n V (fun r k => ∑ a, c r a * b a k) =
      ∑ w : Fin n → σ, (∏ r, c r (w r)) * geoNum n V (fun r => b (w r)) := by
  classical
  induction n generalizing V with
  | zero =>
    have h : ∀ a a' : Fin 0 → K → ℤ, geoNum 0 V a = geoNum 0 V a' := fun a a' => by
      rw [Subsingleton.elim a a']
    simp only [Fintype.sum_unique, Finset.univ_eq_empty, Finset.prod_empty, one_mul]
    exact h _ _
  | succ n ih =>
    by_cases hV : IsRelevant V
    · rw [← (Fin.snocEquiv (fun _ => σ)).sum_comp, Fintype.sum_prod_type]
      simp only [geoNum, dif_pos hV]
      have hin : ∀ (a : σ) (w' : Fin n → σ),
          Fin.init (fun r => b ((Fin.snocEquiv (fun _ => σ)) (a, w') r)) = fun r => b (w' r) := by
        intro a w'
        funext r
        simp [Fin.init, Fin.snocEquiv]
      have hla : ∀ (a : σ) (w' : Fin n → σ), (Fin.snocEquiv (fun _ => σ)) (a, w') (Fin.last n) = a := by
        intro a w'
        simp [Fin.snocEquiv]
      have hca : ∀ (a : σ) (w' : Fin n → σ) (r : Fin n),
          (Fin.snocEquiv (fun _ => σ)) (a, w') r.castSucc = w' r := by
        intro a w' r
        simp [Fin.snocEquiv]
      have hi2 : Fin.init (fun r k => ∑ a, c r a * b a k) =
          fun (r : Fin n) k => ∑ a, c r.castSucc a * b a k := by
        funext r k
        simp [Fin.init]
      simp only [hin, hla, Fin.prod_univ_castSucc, hca, hi2]
      have e : ∀ (k : K) (f : Ideal (MRing ι) → ℤ),
          ∑ᶠ W ∈ divSupp V (X ⟨k, (hV k).choose⟩ : MRing ι), f W =
            ∑ W ∈ (divSupp_finite V (X ⟨k, (hV k).choose⟩ : MRing ι)).toFinset, f W :=
        fun k f => finsum_mem_eq_finite_toFinset_sum f (divSupp_finite _ _)
      simp only [e]
      simp only [ih _ (fun r => c r.castSucc)]
      rw [← exists_integralCombination_of_mem_completedLattice (fun a => c (Fin.last n) a) b (fun w' : Fin n → σ => ∏ r, c r.castSucc (w' r))]
      refine Finset.sum_congr rfl fun k _ => ?_
      congr 1
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun W _ => ?_
      ring
    · have e : ∀ a, geoNum (n + 1) V a = 0 := fun a => by simp only [geoNum, dif_neg hV]
      simp [e]

theorem degSum_polar {σ : Type} [Fintype σ] (e : ℕ) (S : Set (Ideal (MRing ι))) (hS : S.Finite)
    (m : Ideal (MRing ι) → ℝ) (lam : σ → ℤ) (b : σ → K → ℤ) :
    ∑ w : Fin e → σ, (∏ r, (lam (w r) : ℝ)) * ∑ᶠ V ∈ S, m V * (geoNum e V (fun r => b (w r)) : ℝ) =
      ∑ᶠ V ∈ S, m V * (geoNum e V (fun _ k => ∑ a, lam a * b a k) : ℝ) := by
  have e' : ∀ f : Ideal (MRing ι) → ℝ, ∑ᶠ V ∈ S, f V = ∑ V ∈ hS.toFinset, f V :=
    fun f => finsum_mem_eq_finite_toFinset_sum f hS
  have hp : ∀ V : Ideal (MRing ι), geoNum e V (fun _ k => ∑ a, lam a * b a k) =
      ∑ w : Fin e → σ, (∏ r, lam (w r)) * geoNum e V (fun r => b (w r)) :=
    fun V => geoNum_polar e V (fun _ => lam) b
  simp only [e', hp]
  push_cast
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun V _ => Finset.sum_congr rfl fun w _ => ?_
  ring

end Geo

section Wt

variable {Ψ : Type} {N : ℕ}

def gapZ (lam : Ψ × Fin N → ℤ) (p : Ψ × Fin N) : ℤ :=
  lam p - if h : (p.2 : ℕ) + 1 < N then lam (p.1, ⟨(p.2 : ℕ) + 1, h⟩) else 0

theorem gap_cast (lam : Ψ × Fin N → ℤ) (p : Ψ × Fin N) :
    gap (fun q => (lam q : ℝ)) p = (gapZ lam p : ℝ) := by
  unfold gap gapX gapZ
  split_ifs <;> simp

theorem formPoly_eq_toWt [Fintype Ψ] (n : ℕ) (ax ay : (Fin n → Ψ × Fin N) → ℝ)
    (h : ∀ lam : Ψ × Fin N → ℤ, ∑ w, (∏ r, (lam (w r) : ℝ)) * ax w = ∑ w, (∏ r, (gapZ lam (w r) : ℝ)) * ay w) :
    formPoly n ax = toWt (formPoly n ay) := by
  refine MvPolynomial.funext_set (fun _ => Set.range (fun z : ℤ => (z : ℝ)))
    (fun _ => Set.infinite_range_of_injective Int.cast_injective) ?_
  intro x hx
  choose lam hlam using fun i => hx i (Set.mem_univ i)
  have hxl : x = fun p => (lam p : ℝ) := funext fun p => (hlam p).symm
  rw [hxl, eval_toWt_gap, (formPoly_isHomogeneous_and_eval _ n ax).2, (formPoly_isHomogeneous_and_eval _ n ay).2]
  simp only [gap_cast]
  simpa only [mul_comm] using h lam

end Wt

section Flag

variable (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ)

def yDeg (p : Ψ × Fin N) : FlBlock Ψ N → ℤ :=
  fun q => if q.1 = p.1 ∧ (q.2 : ℕ) = p.2 then 1 else 0

variable {Ψ N}

theorem deg_abel (lam : Ψ × Fin N → ℤ) (q : FlBlock Ψ N) :
    ∑ p, lam p * xDeg Ψ N p q = ∑ p, gapZ lam p * yDeg Ψ N p q := by
  classical
  obtain ⟨τ, i⟩ := q
  have hi : (i : ℕ) + 1 < N := by have := i.2; omega
  have hi0 : (i : ℕ) < N := by omega
  have hx : ∀ p : Ψ × Fin N, xDeg Ψ N p (τ, i) =
      (if p = (τ, ⟨(i : ℕ), hi0⟩) then 1 else 0) - (if p = (τ, ⟨(i : ℕ) + 1, hi⟩) then 1 else 0) := by
    rintro ⟨τ', a⟩
    by_cases ht : τ = τ'
    · subst ht
      simp [xDeg, Fin.ext_iff, eq_comm]
    · simp [xDeg, ht, Ne.symm ht]
  have hy : ∀ p : Ψ × Fin N, yDeg Ψ N p (τ, i) = if p = (τ, ⟨(i : ℕ), hi0⟩) then 1 else 0 := by
    rintro ⟨τ', a⟩
    by_cases ht : τ = τ'
    · subst ht
      simp [yDeg, Fin.ext_iff, eq_comm]
    · simp [yDeg, ht, Ne.symm ht]
  simp only [hx, hy, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  simp [gapZ, hi]

theorem deg_abel_smul (lam : Ψ × Fin N → ℤ) :
    ∑ p, lam p • xDeg Ψ N p = ∑ p, gapZ lam p • yDeg Ψ N p := by
  funext q
  simpa [Finset.sum_apply] using deg_abel lam q

end Flag

end FlLines

open FlLines

theorem flLines_polys : Inputs → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] [Nonempty Ψ] (N : ℕ), 2 ≤ N → IsArithVar (PFl Ψ N) (antisymDegree Ψ N + 1) → hFlPoly Ψ N II = toWt (formPoly (antisymDegree Ψ N + 1) fun w => II (FlBlock Ψ N) (FlIdx Ψ N) (PFl Ψ N) (antisymDegree Ψ N + 1) fun r => yLineFl Ψ N (w r)) ∧ degFlPoly Ψ N = toWt (formPoly (antisymDegree Ψ N) fun w => ptsIntegral (PFl Ψ N) (pot fun r => yLineFl Ψ N (w r)) fun _ => 1) := by
  intro hIn II hII Ψ _ _ _ N _ hP
  have hI := hII.1 (FlBlock Ψ N) (FlIdx Ψ N)
  refine ⟨formPoly_eq_toWt _ _ _ fun lam => ?_, formPoly_eq_toWt _ _ _ fun lam => ?_⟩
  · have h1 := FlagHeightMultilinear.I_fsHerm_sum hI hP (fun _ => lam) (xDeg Ψ N)
    have h2 := FlagHeightMultilinear.I_fsHerm_sum hI hP (fun _ => gapZ lam) (yDeg Ψ N)
    rw [deg_abel_smul lam, h2] at h1
    exact h1.symm
  · set S : Set (Ideal (MRing (FlIdx Ψ N))) := divSupp (PFl Ψ N) (C (((2 : ℕ) : ℤ))) with hSdef
    have hS : S.Finite := divSupp_finite _ _
    set m : Ideal (MRing (FlIdx Ψ N)) → ℝ :=
      fun V => (multAt (PFl Ψ N ⊔ Ideal.span {C (((2 : ℕ) : ℤ))}) V : ℝ) with hm
    have hD : ∀ L : Fin (antisymDegree Ψ N) → HermLine (FlIdx Ψ N), (∀ j, IsSmoothHerm (L j)) →
        ptsIntegral (PFl Ψ N) (pot L) (fun _ => 1) = ∑ᶠ V ∈ S, m V * (geoNum _ V (fun j => (L j).a) : ℝ) :=
      fun L hL => hIn.degree _ _ _ _ L 2 hP hL Nat.prime_two
    have hsm : ∀ a : FlBlock Ψ N → ℤ, IsSmoothHerm (fsHerm (FlIdx Ψ N) a) :=
      FlagHeightMultilinear.isSmoothHerm_fsHerm
    have h1 := degSum_polar (antisymDegree Ψ N) S hS m lam (xDeg Ψ N)
    have h2 := degSum_polar (antisymDegree Ψ N) S hS m (gapZ lam) (yDeg Ψ N)
    have hv : (fun (_ : Fin (antisymDegree Ψ N)) k => ∑ a, lam a * xDeg Ψ N a k) =
        fun _ k => ∑ a, gapZ lam a * yDeg Ψ N a k := by
      funext _ k
      exact deg_abel lam k
    rw [hv, ← h2] at h1
    have ex : ∀ w : Fin (antisymDegree Ψ N) → Ψ × Fin N,
        ptsIntegral (PFl Ψ N) (pot fun r => xLine Ψ N (w r)) (fun _ => 1) =
          ∑ᶠ V ∈ S, m V * (geoNum _ V (fun r => xDeg Ψ N (w r)) : ℝ) :=
      fun w => hD _ fun _ => hsm _
    have ey : ∀ w : Fin (antisymDegree Ψ N) → Ψ × Fin N,
        ptsIntegral (PFl Ψ N) (pot fun r => yLineFl Ψ N (w r)) (fun _ => 1) =
          ∑ᶠ V ∈ S, m V * (geoNum _ V (fun r => yDeg Ψ N (w r)) : ℝ) :=
      fun w => hD _ fun _ => hsm _
    simp only [ex, ey]
    exact h1

end GlobalTheory.CompanionTheory.Ar.PB
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagHeightPolynomialWeightFormStatement
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_height_polynomial_weight_form : Inputs → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] [Nonempty Ψ] (N : ℕ), 2 ≤ N → IsArithVar (PFl Ψ N) (antisymDegree Ψ N + 1) → hFlPoly Ψ N II = toWt (formPoly (antisymDegree Ψ N + 1) fun w => II (FlBlock Ψ N) (FlIdx Ψ N) (PFl Ψ N) (antisymDegree Ψ N + 1) fun r => yLineFl Ψ N (w r)) ∧ degFlPoly Ψ N = toWt (formPoly (antisymDegree Ψ N) fun w => ptsIntegral (PFl Ψ N) (pot fun r => yLineFl Ψ N (w r)) fun _ => 1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.flLines_polys | exact GlobalTheory.CompanionTheory.Ar.PB.flLines_polys | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.flLines_polys <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsSncAdaptedChartAtPoint
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsSncAdaptedChartAtPoint
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.LocalForm

theorem holoOn_coord {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (hψ : IsCompatChart A ψ) (i : Fin e) :
    A.HoloOn ψ.source (fun y => ψ y i) := by
  intro j z hz
  exact (analyticAt_pi_iff.1 ((hψ j).1 z hz)) i

theorem exists_local_form : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set X), IsSNC A L s m W → ∀ x, ∃ (φ : OpenPartialHomeomorph X (Fin e → ℂ)) (S : Finset (Fin e)) (μ : Fin e → ℕ) (v : X → ℂ), IsCompatChart A φ ∧ x ∈ φ.source ∧ Metric.closedBall (0 : Fin e → ℂ) 2 ⊆ φ.target ∧ φ x = 0 ∧ φ.source ⊆ L.U x ∧ (∀ i ∈ S, 1 ≤ μ i) ∧ A.HoloOn φ.source v ∧ (∀ y ∈ φ.source, v y ≠ 0) ∧ ∀ y ∈ φ.source, s x y = v y * ∏ i ∈ S, φ y i ^ μ i := by
  intro e X _ A L s nb m W hsnc x
  obtain ⟨ψ, hψ, hxψ, hψU, σ, hinj, -, u, hu, hu0, hs⟩ := hsnc x
  obtain ⟨c, hc⟩ : ∃ c, c = ψ x := ⟨_, rfl⟩
  have hev : ∀ᶠ z in 𝓝 c, z ∈ ψ.target ∧ ∀ i, c i ≠ 0 → z i ≠ 0 := by
    have h1 : ∀ᶠ z in 𝓝 c, z ∈ ψ.target := ψ.open_target.mem_nhds (hc ▸ ψ.map_source hxψ)
    refine h1.and ?_
    rw [eventually_all]
    intro i
    by_cases h : c i = 0
    · simp [h]
    · filter_upwards [((continuous_apply i).continuousAt (x := c)).eventually_ne h] with z hz _
      exact hz
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  have hV : IsOpen (ψ.source ∩ ψ ⁻¹' Metric.ball c r) :=
    ψ.continuousOn.isOpen_inter_preimage ψ.open_source Metric.isOpen_ball
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have ha : (3 / r : ℂ) ≠ 0 := by simpa using hrC
  obtain ⟨φ, hφ⟩ : ∃ φ, φ = (ψ.restrOpen _ hV).transHomeomorph (pa_aff (3 / r : ℂ) ha c) := ⟨_, rfl⟩
  have hφc : IsCompatChart A φ := hφ ▸ pa_compat_aff A _ (pa_compat_restr A _ hψ _ hV) _ ha _
  have hsrc : ∀ y ∈ φ.source, y ∈ ψ.source ∧ ψ y ∈ Metric.ball c r := by
    intro y hy
    subst hφ
    exact ⟨hy.1, hy.2.2⟩
  have hφapp : ∀ y, φ y = (3 / r : ℂ) • (ψ y - c) := by
    intro y
    subst hφ
    rfl
  have hxφ : x ∈ φ.source := by
    subst hφ
    refine ⟨hxψ, hxψ, ?_⟩
    show ψ x ∈ Metric.ball c r
    rw [← hc]
    exact Metric.mem_ball_self hr
  have htarget : Metric.closedBall (0 : Fin e → ℂ) 2 ⊆ φ.target := by
    intro z hz
    subst hφ
    set w : Fin e → ℂ := (3 / r : ℂ)⁻¹ • z + c with hw
    have hwb : w ∈ Metric.ball c r := by
      rw [Metric.mem_ball, dist_eq_norm, hw, add_sub_cancel_right, norm_smul]
      have hz' : ‖z‖ ≤ 2 := by simpa using hz
      have : ‖(3 / r : ℂ)⁻¹‖ = r / 3 := by
        rw [norm_inv, norm_div, Complex.norm_real, Real.norm_of_nonneg hr.le]
        norm_num
      rw [this]
      nlinarith
    have hwT : w ∈ ψ.target := (hball _ hwb).1
    have hmem : w ∈ (ψ.restrOpen _ hV).target :=
      ⟨hwT, ψ.map_target hwT, by simpa [ψ.right_inv hwT] using hwb⟩
    exact hmem

  let g : Fin nb → X → ℂ := fun k y => (σ k).elim 1 (fun i => ψ y i ^ m k)
  have hg : ∀ k y, (match σ k with
      | some i => ψ y i ^ m k
      | none => 1) = g k y := by
    intro k y
    simp only [g]
    cases σ k <;> rfl
  have hgholo : ∀ k, A.HoloOn ψ.source (g k) := by
    intro k j z hz
    simp only [g]
    cases σ k with
    | none => exact analyticAt_const
    | some i => exact (holoOn_coord A ψ hψ i j z hz).pow (m k)
  let K : Finset (Fin nb) := Finset.univ.filter (fun k => ∃ i, σ k = some i ∧ c i = 0 ∧ 1 ≤ m k)
  let S : Finset (Fin e) := Finset.univ.filter (fun i => c i = 0 ∧ ∃ k, σ k = some i ∧ 1 ≤ m k)
  let μ : Fin e → ℕ := fun i => ∑ k, if σ k = some i then m k else 0
  have hμ : ∀ k i, σ k = some i → μ i = m k := by
    intro k i hk
    refine (Finset.sum_eq_single k (fun b _ hb => if_neg fun h => hb (hinj _ _ i h hk))
      (by simp)).trans (if_pos hk)
  have hKS : ∀ y, ∏ k ∈ K, g k y = ∏ i ∈ S, ψ y i ^ μ i := by
    intro y
    refine Finset.prod_bij (fun k hk => Classical.choose (Finset.mem_filter.1 hk).2) ?_ ?_ ?_ ?_
    · intro k hk
      obtain ⟨h1, h2, h3⟩ := Classical.choose_spec (Finset.mem_filter.1 hk).2
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, h2, k, h1, h3⟩
    · intro k hk k' hk' hkk
      obtain ⟨h1, -, -⟩ := Classical.choose_spec (Finset.mem_filter.1 hk).2
      obtain ⟨h1', -, -⟩ := Classical.choose_spec (Finset.mem_filter.1 hk').2
      exact hinj k k' _ h1 (hkk ▸ h1')
    · intro i hi
      obtain ⟨-, h0, k, hk, hm⟩ := Finset.mem_filter.1 hi
      have hkK : k ∈ K := Finset.mem_filter.2 ⟨Finset.mem_univ _, i, hk, h0, hm⟩
      refine ⟨k, hkK, ?_⟩
      obtain ⟨h1, -, -⟩ := Classical.choose_spec (Finset.mem_filter.1 hkK).2
      exact Option.some.inj (h1.symm.trans hk)
    · intro k hk
      obtain ⟨h1, -, -⟩ := Classical.choose_spec (Finset.mem_filter.1 hk).2
      have key : ∀ i, σ k = some i → g k y = ψ y i ^ μ i := by
        intro i hi
        simp only [g]
        rw [hi, hμ k i hi]
        rfl
      exact key _ h1
  let T : Finset (Fin nb) := Finset.univ.filter
    (fun k => ¬ ∃ i, σ k = some i ∧ c i = 0 ∧ 1 ≤ m k)
  let C : ℂ := ((r : ℂ) / 3) ^ (∑ i ∈ S, μ i)
  have hC : C ≠ 0 := pow_ne_zero _ (div_ne_zero hrC (by norm_num))
  refine ⟨φ, S, μ, fun y => u y * C * ∏ k ∈ T, g k y, hφc, hxφ, htarget, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hφapp, ← hc, sub_self, smul_zero]
  · exact fun y hy => hψU (hsrc y hy).1
  · intro i hi
    obtain ⟨-, -, k, hk, hm⟩ := Finset.mem_filter.1 hi
    rw [hμ k i hk]
    exact hm
  · intro j z hz
    have hz' : z ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' ψ.source := ⟨hz.1, (hsrc _ hz.2).1⟩
    exact ((hu j z hz').mul analyticAt_const).mul
      (Finset.analyticAt_fun_prod _ fun k _ => hgholo k j z hz')
  · intro y hy
    obtain ⟨hy1, hy2⟩ := hsrc y hy
    refine mul_ne_zero (mul_ne_zero (hu0 y hy1) hC) (Finset.prod_ne_zero_iff.2 ?_)
    intro k hk
    have hk' := (Finset.mem_filter.1 hk).2
    simp only [g]
    cases hσ : σ k with
    | none => exact one_ne_zero
    | some i =>
      by_cases hm : m k = 0
      · simp [hm]
      · have hci : c i ≠ 0 := fun h0 => hk' ⟨i, hσ, h0, Nat.one_le_iff_ne_zero.2 hm⟩
        exact pow_ne_zero _ ((hball _ hy2).2 i hci)
  · intro y hy
    obtain ⟨hy1, -⟩ := hsrc y hy
    have hcoord : ∀ i ∈ S, ψ y i = ((r : ℂ) / 3) * φ y i := by
      intro i hi
      obtain ⟨-, h0, -⟩ := Finset.mem_filter.1 hi
      rw [hφapp]
      simp only [Pi.smul_apply, Pi.sub_apply, h0, sub_zero, smul_eq_mul]
      field_simp
    have hsplit : ∏ k, g k y = (∏ k ∈ K, g k y) * ∏ k ∈ T, g k y :=
      (Finset.prod_filter_mul_prod_filter_not _ _ _).symm
    have hmono : ∏ i ∈ S, ψ y i ^ μ i = C * ∏ i ∈ S, φ y i ^ μ i := by
      rw [Finset.prod_congr rfl (fun i hi => by rw [hcoord i hi, mul_pow]),
        Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    have h2 : s x y = u y * ∏ k, g k y := by
      rw [hs y hy1]
      congr 1
      exact Finset.prod_congr rfl (fun k _ => hg k y)
    show s x y = u y * C * (∏ k ∈ T, g k y) * ∏ i ∈ S, φ y i ^ μ i
    rw [h2, hsplit, hKS, hmono]
    ring

end GlobalTheory.CompanionTheory.Ar.PB.LocalForm
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsSncAdaptedChartAtPointStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_snc_adapted_chart_at_point : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set X), IsSNC A L s m W → ∀ x, ∃ (φ : OpenPartialHomeomorph X (Fin e → ℂ)) (S : Finset (Fin e)) (μ : Fin e → ℕ) (v : X → ℂ), IsCompatChart A φ ∧ x ∈ φ.source ∧ Metric.closedBall (0 : Fin e → ℂ) 2 ⊆ φ.target ∧ φ x = 0 ∧ φ.source ⊆ L.U x ∧ (∀ i ∈ S, 1 ≤ μ i) ∧ A.HoloOn φ.source v ∧ (∀ y ∈ φ.source, v y ≠ 0) ∧ ∀ y ∈ φ.source, s x y = v y * ∏ i ∈ S, φ y i ^ μ i := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.LocalForm.exists_local_form | exact GlobalTheory.CompanionTheory.Ar.PB.LocalForm.exists_local_form | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.LocalForm.exists_local_form <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorSumIdentityBaseChange
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorSumIdentityBaseChange
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.MinorAny

theorem minorIJ_map {R S : Type} [CommRing R] [CommRing S] {N : ℕ} (f : R →+* S)
    (A : Matrix (Fin N) (Fin N) R) (I J : Finset (Fin N)) :
    minorIJ (A.map f) I J = f (minorIJ A I J) := by
  unfold minorIJ
  split_ifs with e
  · rw [RingHom.map_det]
    rfl
  · exact (map_zero f).symm

def gap {N : ℕ} {Ω : Type} [Field Ω] (T : Matrix (Fin N) (Fin N) Ω) (c₀ c₁ : Ω)
    (coef u : Finset (Fin N) → Ω) (J : Finset (Fin N)) (S : Type) [CommRing S] [Algebra Ω S]
    (h : Matrix (Fin N) (Fin N) S) : S :=
  algebraMap Ω S c₀ * ∑ I, algebraMap Ω S (coef I) * minorIJ (T.map (algebraMap Ω S) * h) I J -
    algebraMap Ω S c₁ * ∑ I, algebraMap Ω S (u I) * minorIJ h I J

theorem gap_map {N : ℕ} {Ω : Type} [Field Ω] (T : Matrix (Fin N) (Fin N) Ω) (c₀ c₁ : Ω)
    (coef u : Finset (Fin N) → Ω) (J : Finset (Fin N)) {S S' : Type} [CommRing S] [Algebra Ω S]
    [CommRing S'] [Algebra Ω S'] (f : S →ₐ[Ω] S') (h : Matrix (Fin N) (Fin N) S) :
    f (gap T c₀ c₁ coef u J S h) = gap T c₀ c₁ coef u J S' (h.map f.toRingHom) := by
  have hm : ∀ (M : Matrix (Fin N) (Fin N) S) (I J : Finset (Fin N)),
      f (minorIJ M I J) = minorIJ (M.map f.toRingHom) I J :=
    fun M I J => (minorIJ_map f.toRingHom M I J).symm
  have hT : (T.map (algebraMap Ω S) * h).map f.toRingHom = T.map (algebraMap Ω S') * h.map f.toRingHom := by
    rw [Matrix.map_mul, Matrix.map_map]
    congr 1
    congr 1
    funext x
    exact f.commutes x
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gap, map_sub, map_mul, map_sum, AlgHom.commutes, hm, hT]

theorem minor_any : ∀ (Ω : Type) [Field Ω] [Infinite Ω] (N j : ℕ) (T : Matrix (Fin N) (Fin N) Ω) (c₀ c₁ : Ω) (coef u : Finset (Fin N) → Ω) (J : Finset (Fin N)), (∀ h : Matrix (Fin N) (Fin N) Ω, IsBlockDiag j h → c₀ * ∑ I, coef I * minorIJ (T * h) I J = c₁ * ∑ I, u I * minorIJ h I J) → ∀ (S : Type) [CommRing S] [Algebra Ω S] (h : Matrix (Fin N) (Fin N) S), IsBlockDiag j h → algebraMap Ω S c₀ * ∑ I, algebraMap Ω S (coef I) * minorIJ (T.map (algebraMap Ω S) * h) I J = algebraMap Ω S c₁ * ∑ I, algebraMap Ω S (u I) * minorIJ h I J := by
  intro Ω _ _ N j T c₀ c₁ coef u J hyp S _ _ h hh
  have hT : T.map (algebraMap Ω Ω) = T := Matrix.ext fun _ _ => rfl
  have key : ∀ M : Matrix (Fin N) (Fin N) Ω, IsBlockDiag j M → gap T c₀ c₁ coef u J Ω M = 0 := by
    intro M hM
    simp only [gap, hT]
    exact sub_eq_zero.mpr (hyp M hM)
  let G : Matrix (Fin N) (Fin N) (MvPolynomial (Fin N × Fin N) Ω) :=
    Matrix.of fun a b => if ((a : ℕ) < N - j ↔ (b : ℕ) < N - j) then X (a, b) else 0
  have hP : gap T c₀ c₁ coef u J (MvPolynomial (Fin N × Fin N) Ω) G = 0 := by
    apply MvPolynomial.funext
    intro x
    show aeval x (gap T c₀ c₁ coef u J (MvPolynomial (Fin N × Fin N) Ω) G) = aeval x 0
    rw [map_zero, gap_map]
    apply key
    intro a b hab
    simp only [G, Matrix.map_apply, Matrix.of_apply, if_neg hab, map_zero]
  have hG : G.map (aeval (fun p : Fin N × Fin N => h p.1 p.2)).toRingHom = h := by
    ext a b
    simp only [G, Matrix.map_apply, Matrix.of_apply]
    split_ifs with hab
    · simp [aeval_X]
    · rw [map_zero]
      exact (hh a b hab).symm
  have hz := congrArg (aeval (fun p : Fin N × Fin N => h p.1 p.2)) hP
  rw [gap_map, hG, map_zero] at hz
  simp only [gap] at hz
  exact sub_eq_zero.mp hz

end GlobalTheory.CompanionTheory.Ar.PB.MinorAny
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorSumIdentityBaseChangeStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.minor_sum_identity_base_change : ∀ (Ω : Type) [Field Ω] [Infinite Ω] (N j : ℕ) (T : Matrix (Fin N) (Fin N) Ω) (c₀ c₁ : Ω) (coef u : Finset (Fin N) → Ω) (J : Finset (Fin N)), (∀ h : Matrix (Fin N) (Fin N) Ω, IsBlockDiag j h → c₀ * ∑ I, coef I * minorIJ (T * h) I J = c₁ * ∑ I, u I * minorIJ h I J) → ∀ (S : Type) [CommRing S] [Algebra Ω S] (h : Matrix (Fin N) (Fin N) S), IsBlockDiag j h → algebraMap Ω S c₀ * ∑ I, algebraMap Ω S (coef I) * minorIJ (T.map (algebraMap Ω S) * h) I J = algebraMap Ω S c₁ * ∑ I, algebraMap Ω S (u I) * minorIJ h I J := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.MinorAny.minor_any | exact GlobalTheory.CompanionTheory.Ar.PB.MinorAny.minor_any | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.MinorAny.minor_any <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RootOriginWeightComparison
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RootOriginWeightComparison
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Small.Fund

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Small.Fund

theorem sum_neg_mul_eq_sum_fundCo {Ψ : Type} [Fintype Ψ] {N : ℕ} (f : Ψ → Fin N → ℝ) (B R : Ψ × Fin N → ℝ)
    (h : ∀ τ i, R (τ, i) = -∑ k ∈ Finset.Iic i, B (τ, k)) :
    ∑ r : Ψ × Fin N, -f r.1 r.2 * B r = ∑ r : Ψ × Fin N, fundCo (f r.1) r.2 * R r := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have e := sum_fundCo_mul_sum_Iic (f τ) fun k => B (τ, k)
  simp only [h, mul_neg, Finset.sum_neg_distrib, neg_mul]
  rw [e]

theorem weight_sub_log_sing :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (RM : RootModel (CMType H) (D.p + D.q)) (Sys : PB.AnSys (dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (Or : RootOrigin Y S RM Fx) (lam nu : Wt (CMType H) (D.p + D.q)) (n' : Option (RootIx D) → ℤ) (s : ℝ) (x : Or.Re.R.X), (∀ j, (n' j : ℝ) = RM.coef lam 0 j) → scale s ≤ Sys.t₀ → Or.Re.π x ∈ Sys.open' → RM.weight (scale s) (lam - s • nu) s (Or.Re.R.lift x x) - Real.log (∏ r, (Or.sing r).h (Or.Re.R.lift x x) ^ n' (some r)) = s / RM.kA * Real.log (RM.A.h (Or.Re.R.lift x x)) - s * ∑ r : RootIx D, fundCo (nu r.1) r.2 * Real.log ((Or.Re.ref (some r)).h (Or.Re.R.lift x x)) + ∑ r : RootIx D, fundCo ((lam - s • nu) r.1) r.2 * Sys.phT (some r) (scale s) (Or.Re.π x) - ∑ r : RootIx D, fundCo (lam r.1) r.2 * Sys.ph (some r) (Or.Re.π x) := by
  intro E _ _ _ H D l Xo c O _ β Y S RM Sys Fx Or lam nu n' s x hn ht hop
  have hw := Or.Re.R.mem x x (Or.Re.R.mem_U x)
  have ht0 : 0 < scale s := Real.exp_pos _
  have hreg : ∀ τ i, Real.log ((Or.Re.ref (some (τ, i))).h (Or.Re.R.lift x x)) +
      Sys.phT (some (τ, i)) (scale s) (Or.Re.π x) =
      -∑ k ∈ Finset.Iic i, Real.log ((RM.x (scale s) (τ, k)).h (Or.Re.R.lift x x)) := fun τ i => by
    rw [← Or.fund_reg τ i (scale s) ht0 ht _ hw, Or.Re.line_eq (some (τ, i)) (scale s) ht0 ht x]
  have hsing : ∀ τ i, Real.log ((Or.Re.ref (some (τ, i))).h (Or.Re.R.lift x x)) +
      Sys.ph (some (τ, i)) (Or.Re.π x) =
      -∑ k ∈ Finset.Iic i, Real.log ((Or.sing (τ, k)).h (Or.Re.R.lift x x)) :=
    fun τ i => Or.fund_sing τ i x hop
  have e1 := sum_neg_mul_eq_sum_fundCo (lam - s • nu)
    (fun r => Real.log ((RM.x (scale s) r).h (Or.Re.R.lift x x)))
    (fun r => Real.log ((Or.Re.ref (some r)).h (Or.Re.R.lift x x)) +
      Sys.phT (some r) (scale s) (Or.Re.π x)) hreg
  have e2 := sum_neg_mul_eq_sum_fundCo lam
    (fun r => Real.log ((Or.sing r).h (Or.Re.R.lift x x)))
    (fun r => Real.log ((Or.Re.ref (some r)).h (Or.Re.R.lift x x)) +
      Sys.ph (some r) (Or.Re.π x)) hsing
  have hlog : Real.log (∏ r, (Or.sing r).h (Or.Re.R.lift x x) ^ n' (some r)) =
      ∑ r : RootIx D, -lam r.1 r.2 * Real.log ((Or.sing r).h (Or.Re.R.lift x x)) := by
    rw [Real.log_prod fun r _ => zpow_ne_zero _ ((Or.sing r).pos _ hw.1).ne']
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Real.log_zpow, hn (some r)]
    rfl
  have hwt : RM.weight (scale s) (lam - s • nu) s (Or.Re.R.lift x x) =
      s / RM.kA * Real.log (RM.A.h (Or.Re.R.lift x x)) +
        ∑ r : RootIx D, -(lam - s • nu) r.1 r.2 * Real.log ((RM.x (scale s) r).h (Or.Re.R.lift x x)) := by
    unfold RootModel.weight
    rw [Fintype.sum_option]
    rfl
  rw [hwt, hlog, e1, e2]
  have hco : ∀ r : RootIx D, fundCo ((lam - s • nu) r.1) r.2 = fundCo (lam r.1) r.2 - s * fundCo (nu r.1) r.2 := by
    intro r
    have : (lam - s • nu) r.1 = lam r.1 - s • nu r.1 := rfl
    rw [this, fundCo_sub, fundCo_smul]
  simp only [mul_add, Finset.sum_add_distrib]
  rw [Finset.mul_sum]
  have hρ : ∑ r : RootIx D, fundCo ((lam - s • nu) r.1) r.2 * Real.log ((Or.Re.ref (some r)).h (Or.Re.R.lift x x)) =
      ∑ r : RootIx D, fundCo (lam r.1) r.2 * Real.log ((Or.Re.ref (some r)).h (Or.Re.R.lift x x)) -
        ∑ r : RootIx D, s * (fundCo (nu r.1) r.2 * Real.log ((Or.Re.ref (some r)).h (Or.Re.R.lift x x))) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hco]
    ring
  rw [hρ]
  ring

end GlobalTheory.CompanionTheory.Ar.Small.Fund
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RootOriginWeightComparisonStatement
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Small.Fund

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_origin_weight_comparison : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (RM : RootModel (CMType H) (D.p + D.q)) (Sys : PB.AnSys (dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (Or : RootOrigin Y S RM Fx) (lam nu : Wt (CMType H) (D.p + D.q)) (n' : Option (RootIx D) → ℤ) (s : ℝ) (x : Or.Re.R.X), (∀ j, (n' j : ℝ) = RM.coef lam 0 j) → scale s ≤ Sys.t₀ → Or.Re.π x ∈ Sys.open' → RM.weight (scale s) (lam - s • nu) s (Or.Re.R.lift x x) - Real.log (∏ r, (Or.sing r).h (Or.Re.R.lift x x) ^ n' (some r)) = s / RM.kA * Real.log (RM.A.h (Or.Re.R.lift x x)) - s * ∑ r : RootIx D, fundCo (nu r.1) r.2 * Real.log ((Or.Re.ref (some r)).h (Or.Re.R.lift x x)) + ∑ r : RootIx D, fundCo ((lam - s • nu) r.1) r.2 * Sys.phT (some r) (scale s) (Or.Re.π x) - ∑ r : RootIx D, fundCo (lam r.1) r.2 * Sys.ph (some r) (Or.Re.π x) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Small.Fund.weight_sub_log_sing | exact GlobalTheory.CompanionTheory.Ar.Small.Fund.weight_sub_log_sing | (intros; apply GlobalTheory.CompanionTheory.Ar.Small.Fund.weight_sub_log_sing <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.GenericFlagAlgebraicallyIndependent
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.GenericFlagAlgebraicallyIndependent
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

theorem IsGenericFlag.indep_twist_mul_genUp : ∀ (Ω Φ : Type) [Field Ω] [Field Φ] [Algebra Ω Φ] (Ψ : Type) (N j : ℕ) (g : Ψ → Matrix (Fin N) (Fin N) Φ) (T : Ψ → Matrix (Fin N) (Fin N) Ω), (∀ τ, IsBlockDiag j (g τ)) → IsGenericFlag Ω j g → (∀ τ, IsBlockDiag j (T τ) ∧ (T τ).det ≠ 0) → AlgebraicIndependent Ω (fun q : inertBlockIndex Ψ N j => (((T q.1.1)⁻¹.map (algebraMap Ω (MvPolynomial (UpIdx Ψ N j) Φ))) * ((g q.1.1).map (C : Φ →+* MvPolynomial (UpIdx Ψ N j) Φ) * genUp Φ N j q.1.1)) q.1.2.1 q.1.2.2) := by
  intro Ω Φ _ _ _ Ψ N j g T hg hgen hT
  have hTu : ∀ τ, IsUnit (T τ).det := fun τ => isUnit_iff_ne_zero.mpr (hT τ).2
  have hM : ∀ τ, IsBlockDiag j ((g τ).map (C : Φ →+* MvPolynomial (UpIdx Ψ N j) Φ) * genUp Φ N j τ) :=
    fun τ => IsBlockDiag.mul (IsBlockDiag.map (hg τ) (C : Φ →+* MvPolynomial (UpIdx Ψ N j) Φ))
      (genUp_blockDiag (R := Φ) τ)
  have key : ∀ (R : Type) [CommRing R] [Algebra Ω R] (f : MvPolynomial (inertBlockIndex Ψ N j) Ω →ₐ[Ω] R)
      (Z : Ψ → Matrix (Fin N) (Fin N) R), (∀ τ, IsBlockDiag j (Z τ)) →
      (∀ q : inertBlockIndex Ψ N j, f (X q) = Z q.1.1 q.1.2.1 q.1.2.2) →
      ∀ τ c b, f (genericBlockMatrix Ω N j τ c b) = Z τ c b := by
    intro R _ _ f Z hZ hf τ c b
    exact congrFun (congrFun (generic_block_matrix_map f.toRingHom hZ hf τ) c) b
  have hlin : ∀ (R : Type) [CommRing R] [Algebra Ω R] (f : MvPolynomial (inertBlockIndex Ψ N j) Ω →ₐ[Ω] R)
      (U : Matrix (Fin N) (Fin N) Ω) (G : Matrix (Fin N) (Fin N) (MvPolynomial (inertBlockIndex Ψ N j) Ω)) (a b : Fin N),
      f ((U.map (algebraMap Ω (MvPolynomial (inertBlockIndex Ψ N j) Ω)) * G) a b)
        = (U.map (algebraMap Ω R) * G.map f) a b := by
    intro R _ _ f U G a b
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mul_apply, map_sum, map_mul, Matrix.map_apply, AlgHom.commutes]
  obtain ⟨φ, hφ⟩ : ∃ φ : MvPolynomial (inertBlockIndex Ψ N j) Ω →ₐ[Ω] MvPolynomial (inertBlockIndex Ψ N j) Ω,
      ∀ q : inertBlockIndex Ψ N j, φ (X q) = ((T q.1.1)⁻¹.map (algebraMap Ω (MvPolynomial (inertBlockIndex Ψ N j) Ω))
        * genericBlockMatrix Ω N j q.1.1) q.1.2.1 q.1.2.2 :=
    ⟨MvPolynomial.aeval (fun q : inertBlockIndex Ψ N j => ((T q.1.1)⁻¹.map (algebraMap Ω (MvPolynomial (inertBlockIndex Ψ N j) Ω))
        * genericBlockMatrix Ω N j q.1.1) q.1.2.1 q.1.2.2), fun q => MvPolynomial.aeval_X _ q⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : MvPolynomial (inertBlockIndex Ψ N j) Ω →ₐ[Ω] MvPolynomial (inertBlockIndex Ψ N j) Ω,
      ∀ q : inertBlockIndex Ψ N j, ψ (X q) = ((T q.1.1).map (algebraMap Ω (MvPolynomial (inertBlockIndex Ψ N j) Ω))
        * genericBlockMatrix Ω N j q.1.1) q.1.2.1 q.1.2.2 :=
    ⟨MvPolynomial.aeval (fun q : inertBlockIndex Ψ N j => ((T q.1.1).map (algebraMap Ω (MvPolynomial (inertBlockIndex Ψ N j) Ω))
        * genericBlockMatrix Ω N j q.1.1) q.1.2.1 q.1.2.2), fun q => MvPolynomial.aeval_X _ q⟩
  have hZ : ∀ τ, IsBlockDiag j ((T τ).map (algebraMap Ω (MvPolynomial (inertBlockIndex Ψ N j) Ω)) * genericBlockMatrix Ω N j τ) :=
    fun τ => IsBlockDiag.mul (IsBlockDiag.map (hT τ).1 (algebraMap Ω (MvPolynomial (inertBlockIndex Ψ N j) Ω)))
      (generic_block_matrix_isBlockDiag (R := Ω) τ)
  have hψg := key _ ψ _ hZ hψ
  have hGψ : ∀ τ, (genericBlockMatrix Ω N j τ).map ψ
      = (T τ).map (algebraMap Ω (MvPolynomial (inertBlockIndex Ψ N j) Ω)) * genericBlockMatrix Ω N j τ :=
    fun τ => Matrix.ext fun c b => by rw [Matrix.map_apply]; exact hψg τ c b
  have hcomp : ∀ p, ψ (φ p) = p := by
    have hc : ψ.comp φ = AlgHom.id Ω _ := by
      apply MvPolynomial.algHom_ext
      intro q
      rw [AlgHom.comp_apply, AlgHom.id_apply, hφ, hlin _ ψ, hGψ, ← Matrix.mul_assoc, ← Matrix.map_mul,
        Matrix.nonsing_inv_mul _ (hTu _),
        show ((1 : Matrix (Fin N) (Fin N) Ω).map (algebraMap Ω (MvPolynomial (inertBlockIndex Ψ N j) Ω))) = 1 from
          (algebraMap Ω (MvPolynomial (inertBlockIndex Ψ N j) Ω)).mapMatrix.map_one,
        Matrix.one_mul, generic_block_matrix_apply]
    intro p
    exact DFunLike.congr_fun hc p
  have hx := IsGenericFlag.indep_mul_genUp hg hgen
  have hxg := key _ (MvPolynomial.aeval (fun q : inertBlockIndex Ψ N j =>
      ((g q.1.1).map (C : Φ →+* MvPolynomial (UpIdx Ψ N j) Φ) * genUp Φ N j q.1.1) q.1.2.1 q.1.2.2)) _ hM
    (fun q => MvPolynomial.aeval_X _ q)
  have hGx : ∀ τ, (genericBlockMatrix Ω N j τ).map (MvPolynomial.aeval (fun q : inertBlockIndex Ψ N j =>
      ((g q.1.1).map (C : Φ →+* MvPolynomial (UpIdx Ψ N j) Φ) * genUp Φ N j q.1.1) q.1.2.1 q.1.2.2))
      = (g τ).map (C : Φ →+* MvPolynomial (UpIdx Ψ N j) Φ) * genUp Φ N j τ :=
    fun τ => Matrix.ext fun c b => by rw [Matrix.map_apply]; exact hxg τ c b
  have h1 : ∀ r, MvPolynomial.aeval (fun q : inertBlockIndex Ψ N j => (((T q.1.1)⁻¹.map (algebraMap Ω (MvPolynomial (UpIdx Ψ N j) Φ)))
        * ((g q.1.1).map (C : Φ →+* MvPolynomial (UpIdx Ψ N j) Φ) * genUp Φ N j q.1.1)) q.1.2.1 q.1.2.2) r
      = MvPolynomial.aeval (fun q : inertBlockIndex Ψ N j =>
        ((g q.1.1).map (C : Φ →+* MvPolynomial (UpIdx Ψ N j) Φ) * genUp Φ N j q.1.1) q.1.2.1 q.1.2.2) (φ r) := by
    have hc : (MvPolynomial.aeval (fun q : inertBlockIndex Ψ N j => (((T q.1.1)⁻¹.map (algebraMap Ω (MvPolynomial (UpIdx Ψ N j) Φ)))
        * ((g q.1.1).map (C : Φ →+* MvPolynomial (UpIdx Ψ N j) Φ) * genUp Φ N j q.1.1)) q.1.2.1 q.1.2.2))
      = (MvPolynomial.aeval (fun q : inertBlockIndex Ψ N j =>
        ((g q.1.1).map (C : Φ →+* MvPolynomial (UpIdx Ψ N j) Φ) * genUp Φ N j q.1.1) q.1.2.1 q.1.2.2)).comp φ := by
      apply MvPolynomial.algHom_ext
      intro q
      rw [AlgHom.comp_apply, MvPolynomial.aeval_X, hφ, hlin, hGx]
    intro r
    exact DFunLike.congr_fun hc r
  rw [algebraicIndependent_iff_injective_aeval] at hx ⊢
  intro p p' hpp
  have h2 : φ p = φ p' := hx (by rw [← h1, ← h1]; exact hpp)
  calc p = ψ (φ p) := (hcomp p).symm
    _ = ψ (φ p') := by rw [h2]
    _ = p' := hcomp p'

end GlobalTheory.CompanionTheory.Ar.PB
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.GenericFlagAlgebraicallyIndependentStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_flag_algebraically_independent : ∀ (Ω Φ : Type) [Field Ω] [Field Φ] [Algebra Ω Φ] (Ψ : Type) (N j : ℕ) (g : Ψ → Matrix (Fin N) (Fin N) Φ) (T : Ψ → Matrix (Fin N) (Fin N) Ω), (∀ τ, IsBlockDiag j (g τ)) → IsGenericFlag Ω j g → (∀ τ, IsBlockDiag j (T τ) ∧ (T τ).det ≠ 0) → AlgebraicIndependent Ω (fun q : inertBlockIndex Ψ N j => (((T q.1.1)⁻¹.map (algebraMap Ω (MvPolynomial (UpIdx Ψ N j) Φ))) * ((g q.1.1).map (C : Φ →+* MvPolynomial (UpIdx Ψ N j) Φ) * genUp Φ N j q.1.1)) q.1.2.1 q.1.2.2) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.IsGenericFlag.indep_twist_mul_genUp | exact GlobalTheory.CompanionTheory.Ar.PB.IsGenericFlag.indep_twist_mul_genUp | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.IsGenericFlag.indep_twist_mul_genUp <;> assumption)
end
end
