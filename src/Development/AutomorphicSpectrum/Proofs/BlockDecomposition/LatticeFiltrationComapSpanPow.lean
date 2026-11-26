module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemLatticeSubIffSum
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.ConeSite
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.SeamDefs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.BasisB
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRing
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensTop
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InOpenOfThickeningMorphism

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeFiltrationComapSpanPow
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeFiltrationComapSpanPow
open DividedPowers CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LatPdpEq

section
variable {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ)

def dq (i : ℕ) : ℚ := ((i.factorial : ℚ))⁻¹ * (((l : ℚ) ^ M)⁻¹) ^ i

theorem dq_ne_zero (hl : l ≠ 0) (i : ℕ) : dq l M i ≠ 0 := by
  have h1 : (l : ℚ) ≠ 0 := by exact_mod_cast hl
  have h2 : (i.factorial : ℚ) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
  unfold dq
  positivity

theorem dpE_eq_smul (i : ℕ) : Lat.dpE f ξ l M i = dq l M i • f ξ ^ i := by
  unfold Lat.dpE Lat.η dq
  rw [smul_pow, smul_smul]

theorem dpE_eq_zero {m i : ℕ} (hm : f ξ ^ m = 0) (hi : m ≤ i) : Lat.dpE f ξ l M i = 0 := by
  rw [dpE_eq_smul, ← Nat.add_sub_of_le hi, pow_add, hm, zero_mul, smul_zero]

theorem dpE_mem_span {k i : ℕ} (hi : k ≤ i) : Lat.dpE f ξ l M i ∈ Ideal.span {f ξ ^ k} := by
  rw [dpE_eq_smul, Algebra.smul_def]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton.2 (pow_dvd_pow _ hi))

theorem ι_mem (x : Lat.A f ξ l M) : Lat.ι f ξ l M x ∈ Lat.sub f ξ l M :=
  Subtype.property (p := fun y => y ∈ Lat.sub f ξ l M) x

theorem dpA_one_mem : Lat.dpA f ξ l M 1 ∈ Lat.I f ξ l M := by
  show Lat.dpE f ξ l M 1 ∈ Lat.IB f ξ
  have := dpE_mem_span f ξ l M (k := 1) le_rfl
  simpa [Lat.IB] using this

theorem dpow_dpA (hc : Lat.DPClosed (Lat.ι f ξ l M) (Lat.γB f ξ)) (i : ℕ) :
    (Lat.γ f ξ l M hc).dpow i (Lat.dpA f ξ l M 1) = Lat.dpA f ξ l M i := by
  apply Lat.ι_injective f ξ l M
  rw [Lat.ι_γ f ξ l M hc (dpA_one_mem f ξ l M), Lat.ι_dpA, Lat.ι_dpA]
  have hy : Lat.dpE f ξ l M 1 ∈ Lat.IB f ξ := dpA_one_mem f ξ l M
  rw [RatAlgebra.dpow_eq_inv_fact_smul _ (Lat.γB f ξ) hy, Ring.inverse_eq_inv']
  simp [Lat.dpE]

theorem dpA_mem_pdP (hl : l ≠ 0) (hc : Lat.DPClosed (Lat.ι f ξ l M) (Lat.γB f ξ)) {r i : ℕ} (hi : r ≤ i) :
    Lat.dpA f ξ l M i ∈ pdP (Lat.γ f ξ l M hc) r := by
  refine Ideal.subset_span ⟨[(i, Lat.dpA f ξ l M 1)], ?_, by simpa using hi, ?_⟩
  · intro q hq
    rw [List.mem_singleton] at hq
    subst hq
    exact dpA_one_mem f ξ l M
  · simp [dpow_dpA f ξ l M hc i]

variable {f ξ l M}

theorem coeff_dvd {m j : ℕ} (h : Lat.Hyp f ξ l m) (hl : l ≠ 0) (hj : j < m) (c : ℕ → W)
    (hy : ∑ i ∈ Finset.Ico j (m + 1), f (c i) * Lat.dpE f ξ l M i ∈ Ideal.span {f ξ ^ (j + 1)}) :
    ξ ∣ c j := by
  rw [Finset.sum_eq_sum_Ico_succ_bot (by omega)] at hy
  have ht : ∑ i ∈ Finset.Ico (j + 1) (m + 1), f (c i) * Lat.dpE f ξ l M i ∈ Ideal.span {f ξ ^ (j + 1)} :=
    Ideal.sum_mem _ fun i hi => Ideal.mul_mem_left _ _ (dpE_mem_span f ξ l M (Finset.mem_Ico.1 hi).1)
  have hh := (Ideal.add_mem_iff_left _ ht).1 hy
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.1 hh
  refine h.gr j hj (c j) ((dq l M j)⁻¹ • b) ?_
  rw [dpE_eq_smul, mul_smul_comm] at hb
  rw [mul_smul_comm, ← hb, smul_smul, inv_mul_cancel₀ (dq_ne_zero l M hl j), one_smul]

theorem push {m j : ℕ} (h : Lat.Hyp f ξ l m) (hl : l ≠ 0) (hj : j < m) (c : ℕ → W) {y : B}
    (e : y = ∑ i ∈ Finset.Ico j (m + 1), f (c i) * Lat.dpE f ξ l M i)
    (hy : y ∈ Ideal.span {f ξ ^ (j + 1)}) :
    ∃ c' : ℕ → W, y = ∑ i ∈ Finset.Ico (j + 1) (m + 1), f (c' i) * Lat.dpE f ξ l M i := by
  obtain ⟨d, hd⟩ := coeff_dvd h hl hj c (M := M) (e ▸ hy)
  refine ⟨Function.update c (j + 1) (c (j + 1) + d * ((l : W) ^ M * ((j : W) + 1))), ?_⟩
  rw [e, Finset.sum_eq_sum_Ico_succ_bot (by omega), Finset.sum_eq_sum_Ico_succ_bot (a := j + 1) (by omega),
    Finset.sum_eq_sum_Ico_succ_bot (a := j + 1) (by omega)]
  have hs : ∑ i ∈ Finset.Ico (j + 1 + 1) (m + 1), f (Function.update c (j + 1)
      (c (j + 1) + d * ((l : W) ^ M * ((j : W) + 1))) i) * Lat.dpE f ξ l M i =
      ∑ i ∈ Finset.Ico (j + 1 + 1) (m + 1), f (c i) * Lat.dpE f ξ l M i := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Function.update_of_ne (by have := (Finset.mem_Ico.1 hi).1; omega)]
  rw [hs, Function.update_self, hd, map_mul, mul_assoc, mul_left_comm (f ξ) (f d), GlobalTheory.CompanionTheory.LatDp.mul_divPow_eq f ξ l M hl j]
  simp only [map_add (f := _), map_mul, map_pow, map_natCast, map_one]
  ring

theorem exists_rep {m : ℕ} (hm : f ξ ^ m = 0) {y : B} (hy : y ∈ Lat.sub f ξ l M) :
    ∃ c : ℕ → W, y = ∑ i ∈ Finset.Ico 0 (m + 1), f (c i) * Lat.dpE f ξ l M i := by
  obtain ⟨n, c, rfl⟩ := (GlobalTheory.CompanionTheory.LatSpan.mem_sub_iff f ξ l M y).1 hy
  refine ⟨fun i => if h : i < n then c ⟨i, h⟩ else 0, ?_⟩
  have h1 : ∑ i : Fin n, f (c i) * Lat.dpE f ξ l M i =
      ∑ i ∈ Finset.range n, f (if h : i < n then c ⟨i, h⟩ else 0) * Lat.dpE f ξ l M i := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => f (if h : i < n then c ⟨i, h⟩ else 0) * Lat.dpE f ξ l M i) n]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp
  rw [h1, Nat.Ico_zero_eq_range]
  have h2 := Finset.sum_subset (s₁ := Finset.range n) (s₂ := Finset.range (n + m + 1))
    (f := fun i => f (if h : i < n then c ⟨i, h⟩ else 0) * Lat.dpE f ξ l M i)
    (fun i hi => by simp only [Finset.mem_range] at hi ⊢; omega)
    (fun i _ hi => by simp only [Finset.mem_range] at hi; simp [hi])
  have h3 := Finset.sum_subset (s₁ := Finset.range (m + 1)) (s₂ := Finset.range (n + m + 1))
    (f := fun i => f (if h : i < n then c ⟨i, h⟩ else 0) * Lat.dpE f ξ l M i)
    (fun i hi => by simp only [Finset.mem_range] at hi ⊢; omega)
    (fun i _ hi => by
      simp only [Finset.mem_range] at hi
      simp only [dpE_eq_zero f ξ l M hm (show m ≤ i by omega), mul_zero])
  exact h2.trans h3.symm

theorem exists_rep_high {m r : ℕ} (h : Lat.Hyp f ξ l m) (hl : l ≠ 0) {y : B} (hy : y ∈ Lat.sub f ξ l M)
    (hr : y ∈ Ideal.span {f ξ ^ r}) (j : ℕ) (hjr : j ≤ r) (hjm : j ≤ m) :
    ∃ c : ℕ → W, y = ∑ i ∈ Finset.Ico j (m + 1), f (c i) * Lat.dpE f ξ l M i := by
  induction j with
  | zero => exact exists_rep h.nil hy
  | succ j ih =>
    obtain ⟨c, e⟩ := ih (by omega) (by omega)
    have hle : Ideal.span {f ξ ^ r} ≤ Ideal.span {f ξ ^ (j + 1)} :=
      Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ hjr)
    exact push h hl (by omega) c e (hle hr)

end

theorem dividedPowerFiltration_eq : ∀ {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ) (m : ℕ),
    Lat.Hyp f ξ l m → ∀ hc : Lat.DPClosed (Lat.ι f ξ l M) (Lat.γB f ξ), ∀ r : ℕ,
    pdP (Lat.γ f ξ l M hc) r = (Ideal.span {f ξ ^ r}).comap (Lat.ι f ξ l M) := by
  intro W B _ _ _ f ξ l M m h hc r
  have hl : l ≠ 0 := fun e => h.l0 (by simp [e])
  apply le_antisymm
  · intro x hx
    have hdp : IsDPMorphism (Lat.γ f ξ l M hc) (Lat.γB f ξ) (Lat.ι f ξ l M) :=
      ⟨Ideal.map_le_iff_le_comap.2 le_rfl, fun {n} a ha => (Lat.ι_γ f ξ l M hc ha).symm⟩
    have := dividedPowerFiltration_map hdp r hx
    rwa [GlobalTheory.CompanionTheory.DPFiltration.pdP_γB f ξ r] at this
  · intro x hx
    obtain ⟨c, e⟩ := exists_rep_high h hl (ι_mem f ξ l M x) hx (min r m) (by omega) (by omega)
    have hx' : x = ∑ i ∈ Finset.Ico (min r m) (m + 1), Lat.ofW f ξ l M (c i) * Lat.dpA f ξ l M i := by
      apply Lat.ι_injective f ξ l M
      set_option synthInstance.maxHeartbeats 100000 in
        rw [e, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, Lat.ι_ofW, Lat.ι_dpA]
    rw [hx']
    refine Ideal.sum_mem _ fun i hi => Ideal.mul_mem_left _ _ ?_
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hi
    by_cases hir : r ≤ i
    · exact dpA_mem_pdP f ξ l M hl hc hir
    · have : Lat.dpA f ξ l M i = 0 := by
        apply Lat.ι_injective f ξ l M
        rw [Lat.ι_dpA, map_zero]
        exact dpE_eq_zero f ξ l M h.nil (by omega)
      rw [this]
      exact Ideal.zero_mem _

end GlobalTheory.CompanionTheory.LatPdpEq
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeFiltrationComapSpanPowStatement
open DividedPowers CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_filtration_comap_span_pow : ∀ {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ) (m : ℕ), Lat.Hyp f ξ l m → ∀ hc : Lat.DPClosed (Lat.ι f ξ l M) (Lat.γB f ξ), ∀ r : ℕ, pdP (Lat.γ f ξ l M hc) r = (Ideal.span {f ξ ^ r}).comap (Lat.ι f ξ l M) := by
  first | exact @GlobalTheory.CompanionTheory.LatPdpEq.dividedPowerFiltration_eq | exact GlobalTheory.CompanionTheory.LatPdpEq.dividedPowerFiltration_eq | (intros; apply GlobalTheory.CompanionTheory.LatPdpEq.dividedPowerFiltration_eq <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepresentativeRestrict
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeRep

theorem rep_resB {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (A : C ⥤ CommAlgCat.{0} R) (a b : IdF A)
    {U V : ObjectProperty C} (h : V ≤ U) {j : ℕ} (z : CH.Cn (CH.modF (U.ι ⋙ A)) j) (c : HU (sq a b) U j) :
    Rep (a.res U.ι) (b.res U.ι) z c → Rep (a.res V.ι) (b.res V.ι) (resB A h z) ((resU (sq a b) h).pull j c) := by
  rintro ⟨f, hf, hc, hz⟩
  have hf' : CH.d (U.ι ⋙ sq a b) j f = 0 := hf
  have hb : CH.d (V.ι ⋙ sq a b) j ((resU (sq a b) h).pullC j f) = 0 := by
    rw [(resU (sq a b) h).d_pullC, hf', map_zero]
  have hcl : (resU (sq a b) h).pull j c = (CH.cx (V.ι ⋙ sq a b)).cls ((resU (sq a b) h).pullC j f) hb := by
    have hc' : c = (CH.cx (U.ι ⋙ sq a b)).cls f hf' := hc
    rw [hc']
    rfl
  exact ⟨(resU (sq a b) h).pullC j f, hb, hcl, fun s => hz (s ⋙ ObjectProperty.ιOfLE h)⟩

end GlobalTheory.CompanionTheory.ConeRep
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeCocycleClosed
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeCocycleClosed
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
open GlobalTheory.CatH (face toLast)

namespace GlobalTheory.CompanionTheory.ConeZcoc

theorem plogK_map {B B' : Type} [CommRing B] [CommRing B'] {J : Ideal B} {J' : Ideal B'}
    {δ : DividedPowers J} {δ' : DividedPowers J'} {f : B →+* B'} (hf : IsDPMorphism δ δ' f) (s : ℕ)
    {x : B} (hx : x ∈ J) : f (plogK δ s x) = plogK δ' s (f x) := by
  unfold plogK
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_mul, map_pow, map_neg, map_one, map_natCast, ← hf.2 x hx]

theorem units_cancel {G : Type} [CommGroup G] (a b c d e f : G) :
    (a * b * c⁻¹) * (c * d * e⁻¹) = (b * d * f⁻¹) * (a * f * e⁻¹) := by
  have h1 : (a * b * c⁻¹) * (c * d * e⁻¹) = a * b * d * e⁻¹ := by
    simp only [mul_assoc, inv_mul_cancel_left]
  have h2 : (b * d * f⁻¹) * (a * f * e⁻¹) = (a * b * d) * e⁻¹ * (f⁻¹ * f) := by
    simp only [mul_assoc, mul_left_comm, mul_comm]
  rw [h1, h2, inv_mul_cancel, mul_one]

theorem plogK_four {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (s : ℕ) (hs : pdP δ s = ⊥)
    (hu : ∀ n : ℕ, n ≠ 0 → IsUnit (n : B)) {a b c d : B} (ha : a - 1 ∈ J) (hb : b - 1 ∈ J) (hc : c - 1 ∈ J)
    (hd : d - 1 ∈ J) (h : a * b = c * d) :
    plogK δ s (a - 1) + plogK δ s (b - 1) = plogK δ s (c - 1) + plogK δ s (d - 1) := by
  rw [← GlobalTheory.T.truncated_log_multiplicative δ s hs hu ha hb, ← GlobalTheory.T.truncated_log_multiplicative δ s hs hu hc hd]
  simp only [add_sub_cancel]
  rw [h]

theorem add_eq {B : Type} [CommRing B] {a c d b a' c' d' b' : B} (h₁ : a = a') (h₂ : c = c') (h₃ : d = d')
    (h₄ : b = b') (h : a' + c' = d' + b') : a + c = d + b := by
  rw [h₁, h₂, h₃, h₄, h]

variable {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}
  {C : Type 1} [Category.{0} C] {g : C ⥤ Thick (smFun X q)} {D : E.LineData X}

def rr (Λ : CLiftK g D) {a b c : C} (φ : a ⟶ b) (ψ : b ⟶ c) (χ : a ⟶ c) : (g.obj c).Bˣ :=
  Units.map (g.map ψ).φ.toMonoidHom (Λ.w φ) * Λ.w ψ * (Λ.w χ)⁻¹

theorem r_eq (Λ : CLiftK g D) (σ : ComposableArrows C 2) :
    Λ.r σ = rr Λ (σ.map' 0 1) (σ.map' 1 2) (σ.map' 0 2) := rfl

theorem rr_coboundary (Λ : CLiftK g D) {c₀ c₁ c₂ c₃ : C} (f₀₁ : c₀ ⟶ c₁) (f₁₂ : c₁ ⟶ c₂) (f₂₃ : c₂ ⟶ c₃)
    (f₀₂ : c₀ ⟶ c₂) (f₁₃ : c₁ ⟶ c₃) (f₀₃ : c₀ ⟶ c₃) (h₀₂ : f₀₂ = f₀₁ ≫ f₁₂) (h₁₃ : f₁₃ = f₁₂ ≫ f₂₃) :
    Units.map (g.map f₂₃).φ.toMonoidHom (rr Λ f₀₁ f₁₂ f₀₂) * rr Λ f₀₂ f₂₃ f₀₃ =
      rr Λ f₁₂ f₂₃ f₁₃ * rr Λ f₀₁ f₁₃ f₀₃ := by
  subst h₀₂ h₁₃
  have e : Units.map (g.map (f₁₂ ≫ f₂₃)).φ.toMonoidHom (Λ.w f₀₁) =
      Units.map (g.map f₂₃).φ.toMonoidHom (Units.map (g.map f₁₂).φ.toMonoidHom (Λ.w f₀₁)) := by
    rw [g.map_comp]; rfl
  unfold rr
  rw [e, map_mul, map_mul, map_inv]
  exact units_cancel _ _ _ _ _ _

theorem map_zK (Λ : CLiftK g D) (s : ℕ) (σ : ComposableArrows C 2) {c : C} (ρ : σ.obj (Fin.last 2) ⟶ c) :
    (show (g.obj c).B from ((g ⋙ O (smFun X q)).map ρ).hom (zK Λ s σ)) =
      plogK (g.obj c).δ s (((Units.map (g.map ρ).φ.toMonoidHom (Λ.r σ) : (g.obj c).Bˣ) : (g.obj c).B) - 1) := by
  change (g.map ρ).φ (plogK (g.obj (σ.obj (Fin.last 2))).δ s ((Λ.r σ : (g.obj (σ.obj (Fin.last 2))).B) - 1)) = _
  rw [plogK_map (g.map ρ).dp s (GlobalTheory.T.cone_lift_ratio_mem_ideal Λ σ), map_sub, map_one]
  rfl

theorem mem_J (Λ : CLiftK g D) (σ : ComposableArrows C 2) {c : C} (ρ : σ.obj (Fin.last 2) ⟶ c) :
    ((Units.map (g.map ρ).φ.toMonoidHom (Λ.r σ) : (g.obj c).Bˣ) : (g.obj c).B) - 1 ∈ (g.obj c).J := by
  have := (g.map ρ).hle (GlobalTheory.T.cone_lift_ratio_mem_ideal Λ σ)
  rw [Ideal.mem_comap, map_sub, map_one] at this
  exact this

theorem map_id_unit {c : C} (ρ : c ⟶ c) (h : ρ = 𝟙 c) (u : (g.obj c).Bˣ) :
    Units.map (g.map ρ).φ.toMonoidHom u = u := by
  subst h
  rw [g.map_id]
  ext; rfl

theorem nat_isUnit (T : Thick (smFun X q)) (n : ℕ) (hn : n ≠ 0) : IsUnit (n : T.B) := by
  have h : IsUnit (n : K) := (Nat.cast_ne_zero.2 hn).isUnit
  have := h.map T.i
  rwa [map_natCast] at this

theorem main : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)} {C : Type 1} [Category.{0} C] {g : C ⥤ Thick (smFun X q)} {D : E.LineData X} (Λ : CLiftK g D) (s : ℕ), (∀ c, (g.obj c).pdPow s = ⊥) → CH.d _ 2 (zK Λ s) = 0 := by
  intro K _ _ X q C _ g D Λ s hs
  funext τ
  change ∑ i : Fin 4, (-1 : ℤ) ^ (i : ℕ) • ((g ⋙ O (smFun X q)).map (toLast i τ)).hom (zK Λ s (face i τ)) = 0
  rw [Fin.sum_univ_four]
  have h0 := map_zK Λ s (face 0 τ) (toLast 0 τ)
  have h1 := map_zK Λ s (face 1 τ) (toLast 1 τ)
  have h2 := map_zK Λ s (face 2 τ) (toLast 2 τ)
  have h3 := map_zK Λ s (face 3 τ) (toLast 3 τ)
  have m0 := mem_J Λ (face 0 τ) (toLast 0 τ)
  have m1 := mem_J Λ (face 1 τ) (toLast 1 τ)
  have m2 := mem_J Λ (face 2 τ) (toLast 2 τ)
  have m3 := mem_J Λ (face 3 τ) (toLast 3 τ)
  have e0 : Units.map (g.map (toLast 0 τ)).φ.toMonoidHom (Λ.r (face 0 τ)) = Λ.r (face 0 τ) :=
    map_id_unit (g := g) (c := τ.obj (Fin.last 3)) (toLast 0 τ) (τ.map_id _) _
  have e1 : Units.map (g.map (toLast 1 τ)).φ.toMonoidHom (Λ.r (face 1 τ)) = Λ.r (face 1 τ) :=
    map_id_unit (g := g) (c := τ.obj (Fin.last 3)) (toLast 1 τ) (τ.map_id _) _
  have e2 : Units.map (g.map (toLast 2 τ)).φ.toMonoidHom (Λ.r (face 2 τ)) = Λ.r (face 2 τ) :=
    map_id_unit (g := g) (c := τ.obj (Fin.last 3)) (toLast 2 τ) (τ.map_id _) _
  have key : Units.map (g.map (toLast 3 τ)).φ.toMonoidHom (Λ.r (face 3 τ)) *
      Units.map (g.map (toLast 1 τ)).φ.toMonoidHom (Λ.r (face 1 τ)) =
      Units.map (g.map (toLast 0 τ)).φ.toMonoidHom (Λ.r (face 0 τ)) *
      Units.map (g.map (toLast 2 τ)).φ.toMonoidHom (Λ.r (face 2 τ)) := by
    rw [e0, e1, e2]
    exact rr_coboundary Λ (τ.map' 0 1) (τ.map' 1 2) (τ.map' 2 3) (τ.map' 0 2) (τ.map' 1 3) (τ.map' 0 3)
      (τ.map'_comp 0 1 2) (τ.map'_comp 1 2 3)
  have hval := congrArg (Units.val) key
  rw [Units.val_mul, Units.val_mul] at hval
  have p := plogK_four (g.obj (τ.obj (Fin.last 3))).δ s (hs _) (nat_isUnit (g.obj (τ.obj (Fin.last 3)))) m3 m1 m0 m2 hval
  have fin : ∀ a b c d : (g ⋙ O (smFun X q)).obj (τ.obj (Fin.last 3)), a + c = d + b →
      (-1 : ℤ) ^ ((0 : Fin 4) : ℕ) • a + (-1 : ℤ) ^ ((1 : Fin 4) : ℕ) • b + (-1 : ℤ) ^ ((2 : Fin 4) : ℕ) • c +
        (-1 : ℤ) ^ ((3 : Fin 4) : ℕ) • d = 0 := by
    intro a b c d h
    have e3 : ((3 : Fin 4) : ℕ) = 3 := rfl
    have e2 : ((2 : Fin 4) : ℕ) = 2 := rfl
    have e1 : ((1 : Fin 4) : ℕ) = 1 := rfl
    have e0 : ((0 : Fin 4) : ℕ) = 0 := rfl
    rw [e0, e1, e2, e3]
    have : (-1 : ℤ) ^ 3 = -1 := by norm_num
    rw [this, pow_zero, pow_one, show (-1 : ℤ) ^ 2 = 1 by norm_num, one_smul, one_smul, neg_one_smul, neg_one_smul]
    calc a + -b + c + -d = (a + c) - (d + b) := by abel
      _ = 0 := by rw [h, sub_self]
  refine fin _ _ _ _ ?_
  exact add_eq (B := (g.obj (τ.obj (Fin.last 3))).B) h0 h2 h3 h1 p.symm

end GlobalTheory.CompanionTheory.ConeZcoc
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeCocycleClosedStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cone_cocycle_closed : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)} {C : Type 1} [Category.{0} C] {g : C ⥤ Thick (smFun X q)} {D : E.LineData X} (Λ : CLiftK g D) (s : ℕ), (∀ c, (g.obj c).pdPow s = ⊥) → CH.d _ 2 (zK Λ s) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.ConeZcoc.main | exact GlobalTheory.CompanionTheory.ConeZcoc.main | (intros; apply GlobalTheory.CompanionTheory.ConeZcoc.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemLatticeIdealIffSum
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemLatticeIdealIffSum
open DividedPowers CrystallineSemistableComparison.Pb

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.LatIdeal

section
variable {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ)

theorem dpE_succ_mem_IB (i : ℕ) : Lat.dpE f ξ l M (i + 1) ∈ Lat.IB f ξ := by
  have h1 : Lat.η f ξ l M ∈ Lat.IB f ξ := by
    unfold Lat.η Lat.IB
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  unfold Lat.dpE
  rw [Algebra.smul_def, pow_succ]
  exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ h1)

theorem dpE_zero : Lat.dpE f ξ l M 0 = 1 := by
  unfold Lat.dpE
  rw [pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul]

private theorem dpE_mul_dpE_eq_choose_mul (a b : ℕ) :
    Lat.dpE f ξ l M a * Lat.dpE f ξ l M b =
      (((a + b).choose a : ℕ) : B) * Lat.dpE f ξ l M (a + b) := by
  have h0 : (a + b).choose a * a.factorial * b.factorial = (a + b).factorial := by
    have h1 := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right a b)
    rwa [Nat.add_sub_cancel_left] at h1
  have hC : (((a + b).choose a : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (Nat.le_add_right a b)).ne'
  have key : ((a.factorial : ℚ))⁻¹ * ((b.factorial : ℚ))⁻¹ =
      (((a + b).choose a : ℕ) : ℚ) * (((a + b).factorial : ℕ) : ℚ)⁻¹ := by
    rw [← h0, Nat.cast_mul, Nat.cast_mul, mul_inv, mul_inv, ← mul_assoc, ← mul_assoc,
      mul_inv_cancel₀ hC, one_mul]
  have key' : algebraMap ℚ B ((a.factorial : ℚ))⁻¹ * algebraMap ℚ B ((b.factorial : ℚ))⁻¹ =
      (((a + b).choose a : ℕ) : B) * algebraMap ℚ B (((a + b).factorial : ℕ) : ℚ)⁻¹ := by
    rw [← map_mul, key, map_mul, map_natCast]
  unfold Lat.dpE
  rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, pow_add]
  linear_combination (Lat.η f ξ l M ^ a * Lat.η f ξ l M ^ b) * key'

private theorem mul_mem_set_f_mul_dpE {y z : B}
    (hy : y ∈ {y : B | ∃ (w : W) (k : ℕ), y = f w * Lat.dpE f ξ l M k})
    (hz : z ∈ {y : B | ∃ (w : W) (k : ℕ), y = f w * Lat.dpE f ξ l M k}) :
    y * z ∈ {y : B | ∃ (w : W) (k : ℕ), y = f w * Lat.dpE f ξ l M k} := by
  obtain ⟨w, a, rfl⟩ := hy
  obtain ⟨w', b, rfl⟩ := hz
  refine ⟨w * w' * (((a + b).choose a : ℕ) : W), a + b, ?_⟩
  rw [map_mul, map_mul, map_natCast]
  linear_combination (f w * f w') * dpE_mul_dpE_eq_choose_mul f ξ l M a b

private theorem mul_mem_closure_f_mul_dpE {y z : B}
    (hy : y ∈ AddSubgroup.closure {y : B | ∃ (w : W) (k : ℕ), y = f w * Lat.dpE f ξ l M k})
    (hz : z ∈ AddSubgroup.closure {y : B | ∃ (w : W) (k : ℕ), y = f w * Lat.dpE f ξ l M k}) :
    y * z ∈ AddSubgroup.closure {y : B | ∃ (w : W) (k : ℕ), y = f w * Lat.dpE f ξ l M k} := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy' =>
    induction hz using AddSubgroup.closure_induction with
    | mem z hz' => exact AddSubgroup.subset_closure (mul_mem_set_f_mul_dpE f ξ l M hy' hz')
    | zero => rw [mul_zero]; exact zero_mem _
    | add z1 z2 _ _ h1 h2 => rw [mul_add]; exact add_mem h1 h2
    | neg z _ h => rw [mul_neg]; exact neg_mem h
  | zero => rw [zero_mul]; exact zero_mem _
  | add y1 y2 _ _ h1 h2 => rw [add_mul]; exact add_mem h1 h2
  | neg y _ h => rw [neg_mul]; exact neg_mem h

private theorem mem_closure_f_mul_dpE_of_mem_sub {y : B} (hy : y ∈ Lat.sub f ξ l M) :
    y ∈ AddSubgroup.closure {y : B | ∃ (w : W) (k : ℕ), y = f w * Lat.dpE f ξ l M k} := by
  unfold Lat.sub at hy
  induction hy using Subring.closure_induction with
  | mem y hy' =>
    apply AddSubgroup.subset_closure
    rcases hy' with ⟨w, rfl⟩ | ⟨k, rfl⟩
    · exact ⟨w, 0, by rw [dpE_zero, mul_one]⟩
    · exact ⟨1, k, by rw [map_one, one_mul]⟩
  | zero => exact zero_mem _
  | one => exact AddSubgroup.subset_closure ⟨1, 0, by rw [dpE_zero, map_one, mul_one]⟩
  | add y z _ _ h1 h2 => exact add_mem h1 h2
  | neg y _ h => exact neg_mem h
  | mul y z _ _ h1 h2 => exact mul_mem_closure_f_mul_dpE f ξ l M h1 h2

private theorem exists_repr_of_mem_closure_f_mul_dpE {y : B}
    (hy : y ∈ AddSubgroup.closure {y : B | ∃ (w : W) (k : ℕ), y = f w * Lat.dpE f ξ l M k}) :
    ∃ (w₀ : W) (c : ℕ →₀ W), y = f w₀ + c.sum (fun i w => f w * Lat.dpE f ξ l M (i + 1)) := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy' =>
    obtain ⟨w, k, rfl⟩ := hy'
    cases k with
    | zero => exact ⟨w, 0, by rw [dpE_zero, mul_one, Finsupp.sum_zero_index, add_zero]⟩
    | succ j =>
      refine ⟨0, Finsupp.single j w, ?_⟩
      rw [map_zero, zero_add, Finsupp.sum_single_index]
      simp
  | zero => exact ⟨0, 0, by rw [map_zero, Finsupp.sum_zero_index, add_zero]⟩
  | add y z _ _ h1 h2 =>
    obtain ⟨a, c, rfl⟩ := h1
    obtain ⟨b, d, rfl⟩ := h2
    refine ⟨a + b, c + d, ?_⟩
    rw [Finsupp.sum_add_index', map_add (f := _)]
    · ring
    · intro i
      simp
    · intro i b1 b2
      simp [add_mul]
  | neg y _ h =>
    obtain ⟨a, c, rfl⟩ := h
    refine ⟨-a, -c, ?_⟩
    rw [Finsupp.sum_neg_index, map_neg, neg_add]
    · simp only [map_neg, neg_mul, Finsupp.sum, Finset.sum_neg_distrib]
    · intro i
      simp

private theorem exists_fin_sum_eq_finsupp_sum_f_mul_dpE (c : ℕ →₀ W) :
    ∃ (n : ℕ) (c' : Fin n → W), c.sum (fun i w => f w * Lat.dpE f ξ l M (i + 1)) =
      ∑ i : Fin n, f (c' i) * Lat.dpE f ξ l M (i + 1) := by
  have hs : c.support ⊆ Finset.range (c.support.sup id + 1) := by
    intro i hi
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact Finset.le_sup (f := id) hi
  refine ⟨c.support.sup id + 1, fun i => c i, ?_⟩
  rw [Finsupp.sum_of_support_subset c hs (fun i w => f w * Lat.dpE f ξ l M (i + 1))
    (fun _ _ => by simp)]
  exact (Fin.sum_univ_eq_sum_range (fun i => f (c i) * Lat.dpE f ξ l M (i + 1)) _).symm

private theorem f_xi_eq_f_pow_mul_dpE_one (hl : (l : ℚ) ≠ 0) :
    f ξ = f ((l : W) ^ M) * Lat.dpE f ξ l M 1 := by
  have h1 : Lat.dpE f ξ l M 1 = ((l : ℚ) ^ M)⁻¹ • f ξ := by
    unfold Lat.dpE Lat.η
    rw [pow_one, Nat.factorial_one, Nat.cast_one, inv_one, one_smul]
  rw [h1, Algebra.smul_def, ← mul_assoc, map_pow, map_natCast,
    ← map_natCast (algebraMap ℚ B) l, ← map_pow, ← map_mul, mul_inv_cancel₀ (pow_ne_zero _ hl),
    map_one, one_mul]

private theorem finsupp_sum_add_single_zero_f_mul_dpE (c : ℕ →₀ W) (v : W) :
    (c + Finsupp.single 0 v).sum (fun i w => f w * Lat.dpE f ξ l M (i + 1))
      = c.sum (fun i w => f w * Lat.dpE f ξ l M (i + 1)) + f v * Lat.dpE f ξ l M 1 := by
  rw [Finsupp.sum_add_index', Finsupp.sum_single_index]
  all_goals simp [add_mul]

theorem mem_I_iff (m : ℕ) (H : Lat.Hyp f ξ l m) (x : Lat.A f ξ l M) :
    x ∈ Lat.I f ξ l M ↔
      ∃ (n : ℕ) (c : Fin n → W), Lat.ι f ξ l M x = ∑ i, f (c i) * Lat.dpE f ξ l M (i + 1) := by
  have hI : x ∈ Lat.I f ξ l M ↔ Lat.ι f ξ l M x ∈ Lat.IB f ξ := Iff.rfl
  rw [hI]
  constructor
  · intro hx
    have hsub : Lat.ι f ξ l M x ∈ Lat.sub f ξ l M := (x : ↥(Lat.sub f ξ l M)).2
    obtain ⟨w₀, c, hc⟩ := exists_repr_of_mem_closure_f_mul_dpE f ξ l M (mem_closure_f_mul_dpE_of_mem_sub f ξ l M hsub)
    have hS : c.sum (fun i w => f w * Lat.dpE f ξ l M (i + 1)) ∈ Lat.IB f ξ :=
      by
        unfold Finsupp.sum
        exact Ideal.sum_mem _ (fun i _ => Ideal.mul_mem_left _ _ (dpE_succ_mem_IB f ξ l M i))
    have hw : f w₀ ∈ Lat.IB f ξ := by
      have h2 := sub_mem hx hS
      rwa [hc, add_sub_cancel_right] at h2
    unfold Lat.IB at hw
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hw
    obtain ⟨w', rfl⟩ := H.gr 0 H.one_le w₀ b
      (by rw [pow_zero, mul_one, zero_add, pow_one, ← hb, mul_comm])
    have hl : (l : ℚ) ≠ 0 := by
      intro h
      apply H.l0
      have h3 : l = 0 := by exact_mod_cast h
      rw [h3, Nat.cast_zero]
    obtain ⟨n, c', hc'⟩ := exists_fin_sum_eq_finsupp_sum_f_mul_dpE f ξ l M (c + Finsupp.single 0 ((l : W) ^ M * w'))
    refine ⟨n, c', ?_⟩
    rw [← hc', finsupp_sum_add_single_zero_f_mul_dpE f ξ l M, hc]
    simp only [map_mul]
    rw [f_xi_eq_f_pow_mul_dpE_one f ξ l M hl]
    ring
  · rintro ⟨n, c, hc⟩
    rw [hc]
    exact Ideal.sum_mem _ (fun i _ => Ideal.mul_mem_left _ _ (dpE_succ_mem_IB f ξ l M _))

end

theorem mem_I : ∀ {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ) (m : ℕ),
    Lat.Hyp f ξ l m → ∀ x : Lat.A f ξ l M, x ∈ Lat.I f ξ l M ↔
      ∃ (n : ℕ) (c : Fin n → W), Lat.ι f ξ l M x = ∑ i, f (c i) * Lat.dpE f ξ l M (i + 1) := by
  intro W B _ _ _ f ξ l M m H x
  exact mem_I_iff f ξ l M m H x

end GlobalTheory.CompanionTheory.LatIdeal
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemLatticeIdealIffSumStatement
open DividedPowers CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_lattice_ideal_iff_sum : ∀ {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ) (m : ℕ), Lat.Hyp f ξ l m → ∀ x : Lat.A f ξ l M, x ∈ Lat.I f ξ l M ↔ ∃ (n : ℕ) (c : Fin n → W), Lat.ι f ξ l M x = ∑ i, f (c i) * Lat.dpE f ξ l M (i + 1) := by
  first | exact @GlobalTheory.CompanionTheory.LatIdeal.mem_I | exact GlobalTheory.CompanionTheory.LatIdeal.mem_I | (intros; apply GlobalTheory.CompanionTheory.LatIdeal.mem_I <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeFiltrationTopEqBot
open DividedPowers CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LatNil

theorem isDPMorphism_ι {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ)
    (hc : Lat.DPClosed (Lat.ι f ξ l M) (Lat.γB f ξ)) :
    IsDPMorphism (Lat.γ f ξ l M hc) (Lat.γB f ξ) (Lat.ι f ξ l M) := by
  refine ⟨Ideal.map_comap_le, ?_⟩
  intro n a ha
  exact (Lat.ι_γ f ξ l M hc ha).symm

theorem dividedPowerFiltration_eq_bot : ∀ {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ) (m : ℕ),
    Lat.Hyp f ξ l m → ∀ hc : Lat.DPClosed (Lat.ι f ξ l M) (Lat.γB f ξ), pdP (Lat.γ f ξ l M hc) m = ⊥ := by
  intro W B _ _ _ f ξ l M m h hc
  rw [eq_bot_iff]
  intro x hx
  rw [Ideal.mem_bot]
  have h1 : Lat.ι f ξ l M x ∈ pdP (Lat.γB f ξ) m := dividedPowerFiltration_map (isDPMorphism_ι f ξ l M hc) m hx
  rw [GlobalTheory.T.divided_power_filtration_span_pow f ξ m, h.nil, Ideal.mem_span_singleton, zero_dvd_iff] at h1
  exact Lat.ι_injective f ξ l M (by rw [h1, map_zero])

end GlobalTheory.CompanionTheory.LatNil
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalarMultiplicationShiftsFiltration
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalarMultiplicationShiftsFiltration
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LecShift

theorem leC_shift : ∀ {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {I : Ideal A} (γ : DividedPowers I) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (l s : ℕ) (𝒱 : Set X.Opens) (i : ℕ) (a : A), a ∈ pdP γ i → ∀ r : ℤ,
    (smO γ q l s 𝒱).LeC a (sFil _ (r - i)) (sFil _ r) := by
  intro O A _ _ _ I γ X q l s 𝒱 i a ha r T x hx
  have hx' : (show T.obj.B from x) ∈ pdP T.obj.δ (r - i).toNat := hx
  have h1 : T.obj.i a ∈ pdP T.obj.δ i := dividedPowerFiltration_map T.obj.compat i ha
  have h2 := GlobalTheory.CompanionTheory.DPFil.dividedPowerFiltration_mul_le T.obj.δ i (r - i).toNat (Ideal.mul_mem_mul h1 hx')
  exact T.obj.pdPow_anti (show r.toNat ≤ i + (r - i).toNat by omega) h2

end GlobalTheory.CompanionTheory.LecShift
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalarMultiplicationShiftsFiltrationStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scalar_multiplication_shifts_filtration : ∀ {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {I : Ideal A} (γ : DividedPowers I) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (l s : ℕ) (𝒱 : Set X.Opens) (i : ℕ) (a : A), a ∈ pdP γ i → ∀ r : ℤ,
    (smO γ q l s 𝒱).LeC a (sFil _ (r - i)) (sFil _ r) := by
  first | exact @GlobalTheory.CompanionTheory.LecShift.leC_shift | exact GlobalTheory.CompanionTheory.LecShift.leC_shift | (intros; apply GlobalTheory.CompanionTheory.LecShift.leC_shift <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedSplittingOverField
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedSplittingOverField
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.GrSplitField

theorem exists_step {K B : Type} [Field K] [CommRing B] [Algebra K B] {I : Ideal B}
    (γ : DividedPowers I) (i : ℕ) :
    ∃ C : Submodule K B, (∀ n ∈ C, n ∈ pdP γ i) ∧ (∀ n ∈ C, n ∈ pdP γ (i + 1) → n = 0) ∧
      ∀ x ∈ pdP γ i, ∃ n ∈ C, x - n ∈ pdP γ (i + 1) := by
  have hQ : (pdP γ (i + 1)).restrictScalars K ≤ (pdP γ i).restrictScalars K :=
    fun x hx => (Ideal.span_mono fun _ ⟨l, hl, hr, hz⟩ => ⟨l, hl, (Nat.le_succ i).trans hr, hz⟩ :
      pdP γ (i + 1) ≤ pdP γ i) hx
  obtain ⟨c, hc⟩ := exists_isCompl
    (⟨(pdP γ (i + 1)).restrictScalars K, hQ⟩ : Set.Iic ((pdP γ i).restrictScalars K))
  have hinf : (pdP γ (i + 1)).restrictScalars K ⊓ c.1 = ⊥ := congrArg Subtype.val hc.inf_eq_bot
  have hsup : (pdP γ (i + 1)).restrictScalars K ⊔ c.1 = (pdP γ i).restrictScalars K :=
    congrArg Subtype.val hc.sup_eq_top
  refine ⟨c.1, fun n hn => c.2 hn, fun n hn hn' => ?_, fun x hx => ?_⟩
  · have : n ∈ (pdP γ (i + 1)).restrictScalars K ⊓ c.1 := ⟨hn', hn⟩
    rw [hinf] at this
    simpa using this
  · have hx' : x ∈ (pdP γ (i + 1)).restrictScalars K ⊔ c.1 := by
      rw [hsup]
      exact hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx'
    exact ⟨z, hz, by simpa using hy⟩

theorem nonempty_grSplit : ∀ {K B : Type} [Field K] [CommRing B] [Algebra K B] {I : Ideal B} (γ : DividedPowers I) (m : ℕ),
    pdP γ m = ⊥ → Nonempty (GrSplit K γ m) := by
  intro K B _ _ _ I γ m hm
  choose C hC₁ hC₂ hC₃ using fun i : ℕ => exists_step (K := K) γ i
  exact ⟨{
    N := fun i => C i
    ν := fun i => (C i).subtype
    mem := fun i n => hC₁ i n n.2
    inj := fun i n h => Subtype.ext (hC₂ i n n.2 h)
    surj := fun i x hx => by
      obtain ⟨n, hn, h⟩ := hC₃ i x hx
      exact ⟨⟨n, hn⟩, h⟩
    nil := hm }⟩

end GlobalTheory.CompanionTheory.GrSplitField
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedSplittingOverFieldStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_splitting_over_field : ∀ {K B : Type} [Field K] [CommRing B] [Algebra K B] {I : Ideal B} (γ : DividedPowers I) (m : ℕ),
    pdP γ m = ⊥ → Nonempty (GrSplit K γ m) := by
  first | exact @GlobalTheory.CompanionTheory.GrSplitField.nonempty_grSplit | exact GlobalTheory.CompanionTheory.GrSplitField.nonempty_grSplit | (intros; apply GlobalTheory.CompanionTheory.GrSplitField.nonempty_grSplit <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TestFunctionExists
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TestFunctionExists
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Mass
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.MassTest

theorem exists_bump {W : Type} [TopologicalSpace W] [T2Space W] [LocallyCompactSpace W] [MeasurableSpace W]
    [BorelSpace W] (ν : Measure W) [ν.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts ν] {U : Set W}
    (hU : IsOpen U) {x : W} (hx : x ∈ U) :
    ∃ φ : W → ℝ, Continuous φ ∧ HasCompactSupport φ ∧ (∀ X, 0 ≤ φ X) ∧ tsupport φ ⊆ U ∧
      ∫⁻ X, ENNReal.ofReal (φ X) ∂ν ≠ 0 ∧ ∫⁻ X, ENNReal.ofReal (φ X) ∂ν ≠ ⊤ := by
  obtain ⟨K, hK, hxK, hKU⟩ := exists_compact_subset hU hx
  obtain ⟨f, hf1, hf0, hfc, hfr⟩ := exists_continuous_one_zero_of_isCompact (isCompact_singleton (x := x))
    (isOpen_interior (s := K)).isClosed_compl (by simpa using hxK)
  have hsupp : Function.support f ⊆ K := by
    intro y hy
    by_contra hyK
    exact hy (hf0 (fun h => hyK (interior_subset h)))
  have hg : Continuous fun X => ENNReal.ofReal (f X) := ENNReal.continuous_ofReal.comp f.continuous
  refine ⟨f, f.continuous, hfc, fun X => (hfr X).1, ?_, ?_, ?_⟩
  · exact (closure_minimal hsupp hK.isClosed).trans hKU
  · intro h0
    have hpos : 0 < ν {X | ENNReal.ofReal (f X) ≠ 0} := by
      refine IsOpen.measure_pos ν (isOpen_ne_fun hg continuous_const) ⟨x, ?_⟩
      have : f x = 1 := hf1 (Set.mem_singleton x)
      simp [this]
    exact hpos.ne' (ae_iff.1 ((lintegral_eq_zero_iff hg.measurable).1 h0))
  · exact (f.continuous.integrable_of_hasCompactSupport hfc).lintegral_lt_top.ne

theorem exists_compactOpen {W : Type} [TopologicalSpace W] [T2Space W] [LocallyCompactSpace W]
    [TotallyDisconnectedSpace W] [MeasurableSpace W] (ν : Measure W) [ν.IsOpenPosMeasure]
    [IsFiniteMeasureOnCompacts ν] {U : Set W} (hU : IsOpen U) {x : W} (hx : x ∈ U) :
    ∃ A : Set W, IsCompact A ∧ IsOpen A ∧ A ⊆ U ∧ ν A ≠ 0 ∧ ν A ≠ ⊤ := by
  obtain ⟨K, hK, hxK, hKU⟩ := exists_compact_subset hU hx
  obtain ⟨C, hC, hxC, hCK⟩ := (loc_compact_Haus_tot_disc_of_zero_dim (X := W)).exists_subset_of_mem_open hxK
    isOpen_interior
  have hCc : IsCompact C := hK.of_isClosed_subset hC.1 (hCK.trans interior_subset)
  exact ⟨C, hCc, hC.2, (hCK.trans interior_subset).trans hKU, (hC.2.measure_pos ν ⟨x, hxC⟩).ne',
    hCc.measure_lt_top.ne⟩

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E}

theorem gramR_ratTup_apply (R : Type) [CommRing R] [Algebra F R] {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (Y : Fin n → Fin M → E) (a c : Fin n) :
    gramR R σ J (ratTup R Y) a c = inclR R (gramE σ J Y a c) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [gramR, gramE, hR, hE, hform, ratTup, JR, sigR, inclR, map_sum, map_mul]

theorem exists_unit_vector (R : Type) [CommRing R] [Algebra F R] {J : Matrix (Fin 2) (Fin 2) E}
    (hA : Aniso σ J) : ∃ X : Fin 1 → Fin 2 → R ⊗[F] E, IsUnit (gramR R σ J X).det := by
  have hx : hE σ J (fun _ => 1) (fun _ => 1) ≠ 0 := fun h => one_ne_zero (congrFun (hA _ h) 0)
  refine ⟨ratTup R fun _ _ => 1, ?_⟩
  rw [Matrix.det_fin_one, gramR_ratTup_apply]
  exact (IsUnit.mk0 _ hx).map (inclR R)

end Alg

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem isOpen_unit (hcm : IsCMExt F E σ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    (hloc : IsLocR R) (J : Matrix (Fin 2) (Fin 2) E) :
    IsOpen {X : Fin 1 → Fin 2 → R ⊗[F] E | IsUnit (gramR R σ J X).det} := by
  obtain ⟨hTR, hLC, hSC, hT2, -, -, hu, -⟩ := id hloc
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨-, -, -, -, -, -, -, -, -, t10⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hcm R
  have hO : IsOpen {r : R | IsUnit r} := hu.isOpen_range
  exact (PI.VolStabS.isOpen_isUnit_det R hO 1).preimage (t10 1 2 J)

theorem exists_test_fun (hcm : IsCMExt F E σ) {J : Matrix (Fin 2) (Fin 2) E} (hA : Aniso σ J)
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R]
    (hloc : IsLocR R) {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R) (hl : lam.IsAddHaarMeasure) :
    ∃ φ : (Fin 1 → Fin 2 → R ⊗[F] E) → ℝ, Continuous φ ∧ HasCompactSupport φ ∧ (∀ X, 0 ≤ φ X) ∧
      tsupport φ ⊆ {X | IsUnit (gramR R σ J X).det} ∧
      ∫⁻ X, ENNReal.ofReal (φ X) ∂(coordW R b lam 1 2) ≠ 0 ∧
      ∫⁻ X, ENNReal.ofReal (φ X) ∂(coordW R b lam 1 2) ≠ ⊤ := by
  obtain ⟨hTR, hLC, hSC, hT2, -⟩ := id hloc
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  obtain ⟨t1, t2, t3, t4, -, -, -, t8, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hcm R
  haveI := t1
  haveI := t2
  haveI := t3
  haveI := t4
  haveI := t8 1 2
  haveI := (coord_measures_haar F E σ hcm R d b lam hl).2.1 1 2
  obtain ⟨X, hX⟩ := exists_unit_vector R hA
  exact exists_bump _ (isOpen_unit hcm R hloc J) hX

theorem exists_test_set (hcm : IsCMExt F E σ) {J : Matrix (Fin 2) (Fin 2) E} (hA : Aniso σ J)
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R]
    [TotallyDisconnectedSpace R] (hloc : IsLocR R) {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R)
    (hl : lam.IsAddHaarMeasure) :
    ∃ A : Set (Fin 1 → Fin 2 → R ⊗[F] E), IsCompact A ∧ IsOpen A ∧
      A ⊆ {X | IsUnit (gramR R σ J X).det} ∧ coordW R b lam 1 2 A ≠ 0 ∧ coordW R b lam 1 2 A ≠ ⊤ := by
  obtain ⟨hTR, hLC, hSC, hT2, -⟩ := id hloc
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  obtain ⟨t1, t2, t3, t4, -, -, -, t8, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hcm R
  haveI := t1
  haveI := t2
  haveI := t3
  haveI := t4
  haveI := t8 1 2
  haveI := (coord_measures_haar F E σ hcm R d b lam hl).2.1 1 2
  haveI : TotallyDisconnectedSpace (R ⊗[F] E) := (GlobalTheory.CompanionTheory.SW.TopK.coordHomeo R b).symm.totallyDisconnectedSpace
  obtain ⟨X, hX⟩ := exists_unit_vector R hA
  exact exists_compactOpen _ (isOpen_unit hcm R hloc J) hX

end Loc

theorem testEx : TestEx := by
  intro F E _ _ _ _ _ σ J d b li lam μ 𝓕 mi m hcm hJ hA hli hlam _ _ _ _ S
  have hLi : IsLocR (Ainf F) := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hcm.1
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨φ, h1, h2, h3, h4, h5, h6⟩ := exists_test_fun hcm hA (Ainf F) hLi b li hli.1
  have hA' : ∀ v : HeightOneSpectrum (𝓞 F), ∃ A : Set (Fin 1 → Fin 2 → Fv F v ⊗[F] E), IsCompact A ∧ IsOpen A ∧
      A ⊆ {X | IsUnit (gramR (Fv F v) σ J X).det} ∧ coordW (Fv F v) b (lam v) 1 2 A ≠ 0 ∧
      coordW (Fv F v) b (lam v) 1 2 A ≠ ⊤ := fun v => by
    haveI : BorelSpace (Fv F v) := ⟨rfl⟩
    exact exists_test_set hcm hA (Fv F v) (GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v) b (lam v) (hlam v).1
  choose A0 hc ho hs hn ht using hA'
  classical
  have hv : vol b li lam S φ (fun v => if v ∈ S then A0 v else latV b v) =
      (∫⁻ X, ENNReal.ofReal (φ X) ∂(coordW (Ainf F) b li 1 2)) * ∏ v ∈ S, coordW (Fv F v) b (lam v) 1 2 (A0 v) := by
    unfold vol
    congr 1
    exact Finset.prod_congr rfl fun v hvS => by simp [hvS]
  refine ⟨φ, fun v => if v ∈ S then A0 v else latV b v, ⟨h1, h2, h3, h4, ?_, ?_⟩, ?_, ?_⟩
  · intro v hvS
    simp only [hvS, if_true]
    exact ⟨hc v, ho v, hs v⟩
  · intro v hvS
    simp [hvS]
  · rw [hv]
    exact mul_ne_zero h5 (Finset.prod_ne_zero_iff.2 fun v _ => hn v)
  · rw [hv]
    exact ENNReal.mul_ne_top h6 (ENNReal.prod_ne_top fun v _ => ht v)

end GlobalTheory.CompanionTheory.SW.MassTest
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TestFunctionExistsStatement
open PositivityTheory.Rg.Mass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.test_function_exists : TestEx := by
  first | exact @GlobalTheory.CompanionTheory.SW.MassTest.testEx | exact GlobalTheory.CompanionTheory.SW.MassTest.testEx | (intros; apply GlobalTheory.CompanionTheory.SW.MassTest.testEx <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartPropertyPropagates
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartPropertyPropagates
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeSite

theorem wK_rel : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {N m : ℕ}
    (i : X ⟶ PSpace K N) (y : Fin m → MvPolynomial (Fin (N + 1)) K) (s : ℕ) (k : Fin m) ⦃T T' : Thick (smFun X q)⦄,
    (T ⟶ T') → wK q i y s k T → (∃ β, wK q i y s β T') → wK q i y s k T' := by
  intro K _ X q N m i y s k T T' φ h h'
  obtain ⟨β, hQ, -⟩ := h'
  obtain ⟨-, V, hV, hT⟩ := h
  exact ⟨hQ, V, hV, GlobalTheory.CompanionTheory.ThickPt.inU_map V φ hT⟩

end GlobalTheory.CompanionTheory.ConeSite
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartPropertyPropagatesStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_property_propagates : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {N m : ℕ}
    (i : X ⟶ PSpace K N) (y : Fin m → MvPolynomial (Fin (N + 1)) K) (s : ℕ) (k : Fin m) ⦃T T' : Thick (smFun X q)⦄,
    (T ⟶ T') → wK q i y s k T → (∃ β, wK q i y s β T') → wK q i y s k T' := by
  first | exact @GlobalTheory.CompanionTheory.ConeSite.wK_rel | exact GlobalTheory.CompanionTheory.ConeSite.wK_rel | (intros; apply GlobalTheory.CompanionTheory.ConeSite.wK_rel <;> assumption)
end
end
