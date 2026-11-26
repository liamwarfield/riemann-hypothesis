module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetFactorDepthInChartChartIndependent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtremalLowestKtypeKilledByCompactRoots
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestKtypeHolomorphicKilledByLoweringRoots

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestKTypeKilledByNegativeNoncompactRoots
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestKTypeKilledByNegativeNoncompactRoots
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LowestKilled

open Formalism.REAL GlobalTheory.HolDict GlobalTheory.HolDict.Lowering

variable {n : ℕ}

lemma vNormSq_congr (ε ε' : Fin n → Bool) (h : ∀ i j, ε i = ε j ↔ ε' i = ε' j) (μ : Fin n → ℝ) :
    vNormSq ε μ = vNormSq ε' μ := by
  have : rhoC ε = rhoC ε' := by
    funext a
    simp only [rhoC, h]
  simp only [vNormSq, this]

lemma vNormSq_lt_of_blocks (p : ℕ) (s : Bool) (ε : Fin n → Bool) (hε : ∀ a : Fin n, ε a = if (a : ℕ) < p then s else !s)
    (lam μ : Fin n → ℝ) (hlam : StrictAnti lam)
    (hΛ : ∀ i j, i < j → ε i = ε j → Formalism.QuantumDeterminants.lowK ε lam j ≤ Formalism.QuantumDeterminants.lowK ε lam i)
    (hμ : ∀ i j, i < j → ε i = ε j → μ j ≤ μ i)
    (a c : Fin n) (ha : ε a = s) (hc : ε c = !s) (hd : CDom ε (μ + root a c) (Formalism.QuantumDeterminants.lowK ε lam)) :
    vNormSq ε μ < vNormSq ε (Formalism.QuantumDeterminants.lowK ε lam) := by
  let ε' : Fin n → Bool := fun a => decide ((a : ℕ) < p)
  have h : ∀ i j, ε i = ε j ↔ ε' i = ε' j := by
    intro i j
    rw [hε i, hε j]
    by_cases hi : (i : ℕ) < p <;> by_cases hj : (j : ℕ) < p <;> cases s <;> simp [ε', hi, hj]
  rw [vNormSq_congr ε ε' h, vNormSq_congr ε ε' h]
  refine vNormSq_lt p ε' (fun _ => rfl) _ μ (fun i j hij e => hΛ i j hij ((h i j).2 e))
    (fun i j hij e => hμ i j hij ((h i j).2 e)) ?_ a c ?_ ?_ ?_
  · intro a c ha hc
    rw [← vNormSq_congr ε ε' h, ← vNormSq_congr ε ε' h]
    refine GlobalTheory.HolDict.VoganRoot.vNormSq_lowK_sub_root_lt ε hlam ?_
    simp only [ε', decide_eq_true_eq, decide_eq_false_iff_not] at ha hc
    exact Fin.lt_def.mpr (by omega)
  · rw [hε] at ha
    by_cases hi : (a : ℕ) < p <;> cases s <;> simp_all [ε']
  · rw [hε] at hc
    by_cases hi : (c : ℕ) < p <;> cases s <;> simp_all [ε']
  · obtain ⟨co, hco, hd⟩ := hd
    exact ⟨co, fun i j e => ⟨(hco i j e).1, (h i j).1 (hco i j e).2⟩, hd⟩

lemma conjH_single_ne {ε : Fin n → Bool} (a c : Fin n) (hac : ε a ≠ ε c) :
    conjH (Formalism.REAL.Jm ε) (Matrix.single c a (1 : ℂ)) = Matrix.single a c 1 := by
  unfold conjH
  rw [Matrix.inv_eq_left_inv (Jm_mul_self ε)]
  ext i j
  simp only [Formalism.REAL.Jm, Matrix.neg_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.conjTranspose_apply,
    Matrix.single_apply]
  by_cases h : a = i ∧ c = j
  · obtain ⟨rfl, rfl⟩ := h
    cases ha : ε a <;> cases hc : ε c <;> simp_all
  · have h' : ¬(c = j ∧ a = i) := fun h' => h ⟨h'.2, h'.1⟩
    simp [h, h']

theorem dRepC_single_eq_zero (p : ℕ) (s : Bool) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Mt n → (H →L[ℂ] H)) (hlam : StrictAnti lam)
    (hε : ∀ a : Fin n, ε a = if (a : ℕ) < p then s else !s) (hDS : IsDS ε lam σ) (v : H) (hv : v ∈ lowKSub ε lam σ)
    (hsm : SmoothVec (lieH (Formalism.REAL.Jm ε)) σ v) (a c : Fin n) (ha : ε a = s) (hc : ε c = !s) :
    dRepC (Formalism.REAL.Jm ε) σ (Matrix.single c a 1) v = 0 := by
  obtain ⟨hcomp, -, hσ, -, -, ⟨S₀, hS₀⟩, hmin⟩ := hDS
  have hH : (Formalism.REAL.Jm ε).IsHermitian := Jm_conjTranspose ε
  have hdet : (Formalism.REAL.Jm ε).det ≠ 0 := (Matrix.isUnit_det_of_left_inverse (Jm_mul_self ε)).ne_zero
  have hU : IsURepOn (Formalism.QuantumDeterminants.UH (Formalism.REAL.Jm ε)) σ := hσ
  obtain ⟨hspan, hsmv⟩ := GlobalTheory.UnitarySmVec.smoothVec_basic n _ H σ hH hdet hU
  have hlie := GlobalTheory.HolDict.LieAct.main n _ H σ hH hdet hU
  obtain ⟨W, hWf, hWK, hWle, hvW⟩ := exists_fin_stable lam hv
  set J := Formalism.REAL.Jm ε with hJ
  let u₀ : ℂ := if s then 1 else -1
  let V : Submodule ℂ H := W ⊓ Submodule.span ℂ {w | SmoothVec (lieH J) σ w}
  have hVs : ∀ w ∈ V, SmoothVec (lieH J) σ w := fun w hw => hspan w hw.2
  haveI : FiniteDimensional ℂ V := Submodule.finiteDimensional_of_le inf_le_left
  have hVK : ∀ g ∈ Kset ε, ∀ w ∈ V, σ g w ∈ V := fun g hg w hw =>
    ⟨hWK g hg w hw.1, Submodule.subset_span ((hsmv w (hVs w hw)).1 g (kset_sub hg))⟩
  have hs0 : SmoothVec (lieH J) σ 0 := hspan 0 (Submodule.zero_mem _)
  have hz1 : ∀ w, SmoothVec (lieH J) σ w → dRepC J σ 0 w = 0 := by
    intro w hw
    have := ((hlie w w hw hw).1 1 0 0).1
    simpa using this
  have hz2 : ∀ Z, dRepC J σ Z 0 = 0 := by
    intro Z
    have := ((hlie 0 0 hs0 hs0).1 1 Z Z).2.1
    simpa using this
  have hsm1 : ∀ w, SmoothVec (lieH J) σ w → ∀ (t : ℂ) Z, dRepC J σ (t • Z) w = t • dRepC J σ Z w := by
    intro w hw t Z
    have := ((hlie w w hw hw).1 t Z 0).1
    rwa [add_zero, hz1 w hw, add_zero] at this
  let B : Mt n →ₗ[ℂ] V →ₗ[ℂ] H := LinearMap.mk₂ ℂ (fun Z w => dRepC J σ Z w)
    (fun Z Z' w => by simpa using ((hlie w w (hVs _ w.2) (hVs _ w.2)).1 1 Z Z').1)
    (fun t Z w => hsm1 w (hVs _ w.2) t Z)
    (fun Z w w' => by simpa using ((hlie w w' (hVs _ w.2) (hVs _ w'.2)).1 1 Z Z).2.1)
    (fun t Z w => by
      have := ((hlie w 0 (hVs _ w.2) hs0).1 t Z Z).2.1
      rwa [add_zero, hz2, add_zero] at this)
  let G : Set H := {x | ∃ Z : Mt n, (Z * J = u₀ • Z ∧ J * Z = -(u₀ • Z)) ∧ ∃ w ∈ V, x = dRepC J σ Z w}
  let S : Submodule ℂ H := Submodule.span ℂ G
  have hSf : FiniteDimensional ℂ S := by
    refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range (TensorProduct.lift B)) ?_
    refine Submodule.span_le.2 ?_
    rintro x ⟨Z, -, w, hw, rfl⟩
    exact ⟨Z ⊗ₜ ⟨w, hw⟩, rfl⟩
  have hSK : IsKStableOn ε σ S := by
    intro g hg
    have : S ≤ S.comap (σ g : H →ₗ[ℂ] H) := by
      refine Submodule.span_le.2 ?_
      rintro x ⟨Z, ⟨hZ1, hZ2⟩, w, hw, rfl⟩
      refine Submodule.subset_span ⟨g * Z * g⁻¹, ⟨?_, ?_⟩, σ g w, hVK g hg w hw,
        (hlie w w (hVs w hw) (hVs w hw)).2.2.1 g (kset_sub hg) Z⟩
      · rw [kset_inv hg, Matrix.mul_assoc, (kset_star hg).2, ← Matrix.mul_assoc, Matrix.mul_assoc g Z, hZ1]
        simp
      · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hg.2, Matrix.mul_assoc g _ Z, hZ2]
        simp
    exact fun x hx => this hx
  have hSs : ∀ x ∈ S, SmoothVec (lieH J) σ x := by
    intro x hx
    refine hspan x (Submodule.span_mono ?_ hx)
    rintro x ⟨Z, -, w, hw, rfl⟩
    exact (hsmv w (hVs w hw)).2.2.1 Z
  by_contra hne
  have hS0 : S ≠ ⊥ := by
    intro h0
    refine hne ((Submodule.mem_bot ℂ).1 (h0 ▸ Submodule.subset_span
      ⟨Matrix.single c a 1, ⟨?_, ?_⟩, v, ⟨hvW, Submodule.subset_span hsm⟩, rfl⟩))
    · ext i j
      simp only [hJ, Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.single_apply, Matrix.smul_apply]
      by_cases h : c = i ∧ a = j
      · obtain ⟨rfl, rfl⟩ := h
        cases s <;> simp [ha, u₀]
      · simp [h]
    · ext i j
      simp only [hJ, Formalism.REAL.Jm, Matrix.diagonal_mul, Matrix.neg_apply, Matrix.single_apply, Matrix.smul_apply]
      by_cases h : c = i ∧ a = j
      · obtain ⟨rfl, rfl⟩ := h
        cases s <;> simp [hc, u₀]
      · simp [h]
  obtain ⟨μ, S', hS'le, hS'⟩ := GlobalTheory.KTypeExists.exists_kType n ε H σ hσ S hSf hSK hS0
  obtain ⟨u, huS', hu0, hu⟩ := hS'.2.2.2.1
  have huS := hS'le huS'
  have hus := hSs u huS
  have hex : ∃ a' c' : Fin n, ε a' = s ∧ ε c' = !s ∧ ∃ w ∈ V,
      ⟪dRepC J σ (Matrix.single c' a' 1) w, u⟫_ℂ ≠ 0 := by
    by_contra hn
    push Not at hn
    have h : S ≤ (ℂ ∙ u)ᗮ := by
      refine Submodule.span_le.2 ?_
      rintro x ⟨Z, ⟨hZ1, hZ2⟩, w, hw, rfl⟩
      have h1 : dRepC J σ Z w = ∑ i, ∑ j, Z i j • dRepC J σ (Matrix.single i j 1) w := by
        have : B Z ⟨w, hw⟩ = ∑ i, ∑ j, Z i j • B (Matrix.single i j 1) ⟨w, hw⟩ := by
          conv_lhs => rw [Matrix.matrix_eq_sum_single Z]
          set_option synthInstance.maxHeartbeats 100000 in
            simp only [map_sum, LinearMap.sum_apply]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          rw [← LinearMap.smul_apply, ← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]
        exact this
      rw [SetLike.mem_coe, h1]
      refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
      by_cases hij : Z i j = 0
      · rw [hij, zero_smul]
        exact Submodule.zero_mem _
      · refine Submodule.smul_mem _ _ (Submodule.mem_orthogonal_singleton_iff_inner_left.2 (hn j i ?_ ?_ w hw))
        · have := congrFun (congrFun hZ1 i) j
          simp only [hJ, Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul, u₀] at this
          by_contra hj
          cases s
          · rw [if_pos (by simpa using hj), if_neg (by simp)] at this
            exact hij (by linear_combination (1 / 2 : ℂ) * this)
          · rw [if_neg hj, if_pos rfl] at this
            exact hij (by linear_combination (-1 / 2 : ℂ) * this)
        · have := congrFun (congrFun hZ2 i) j
          simp only [hJ, Formalism.REAL.Jm, Matrix.diagonal_mul, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul,
            u₀] at this
          by_contra hi
          cases s
          · rw [if_neg (by simpa using hi), if_neg (by simp)] at this
            exact hij (by linear_combination (-1 / 2 : ℂ) * this)
          · rw [if_pos (by simpa using hi), if_pos rfl] at this
            exact hij (by linear_combination (1 / 2 : ℂ) * this)
    exact hu0 (inner_self_eq_zero.1 (Submodule.mem_orthogonal_singleton_iff_inner_left.1 (h huS)))
  obtain ⟨a', c', ha', hc', w, hw, hwu⟩ := hex
  rw [(hlie w u (hVs w hw) hus).2.2.2, neg_ne_zero, hJ, conjH_single_ne a' c' (by rw [ha', hc']; cases s <;> simp), ← hJ] at hwu
  have hy : IsWtOn (Kset ε) σ (μ + root a' c') (dRepC J σ (Matrix.single a' c' 1) u) := by
    intro θ hθ
    have h1 := (hlie u u hus hus).2.2.1 _ (kset_sub hθ) (Matrix.single a' c' 1)
    have h2 := ((hlie u 0 hus hs0).1 (Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I))
      (Matrix.single a' c' 1) 0).2.1
    rw [add_zero, hz2, add_zero] at h2
    rw [h1, tor_conj, hsm1 _ ((hsmv u hus).1 _ (kset_sub hθ)), hu θ hθ, h2, smul_smul, ← Complex.exp_add]
    congr 2
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, sum_root_mul]
    push_cast
    ring
  have hd := cdom_of_inner_ne hσ lam hy (hWle hw.1) hwu
  exact absurd (hmin μ S' hS') (not_le.2 (vNormSq_lt_of_blocks p s ε hε lam μ hlam (dominant_of_isKTypeOf hσ hS₀)
    (dominant_of_isKTypeOf hσ hS') a' c' ha' hc' hd))

theorem lowK_killed : ∀ (n : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin n → Bool) (lam : Fin n → ℝ) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (p : ℕ) (s : Bool), (∀ a : Fin n, ε a = if (a : ℕ) < p then s else !s) → StrictAnti lam → IsDS ε lam π → ∀ v ∈ lowKSub ε lam π, SmoothVec {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0} π v → ∀ a b : Fin n, ε a ≠ ε b → b < a → ∀ X ∈ {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0}, ∀ Y ∈ {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0}, X + Complex.I • Y = Matrix.single a b 1 → dRep π X v + Complex.I • dRep π Y v = 0 := by
  intro n H _ _ ε lam π p s hε hlam hDS v hv hsm a b hab hba X hX Y hY hXY
  have hb : ε b = s ∧ ε a = !s := by
    rw [hε a, hε b] at hab ⊢
    rw [Fin.lt_def] at hba
    by_cases ha : (a : ℕ) < p
    · rw [if_pos ha, if_pos (hba.trans ha)] at hab
      exact absurd rfl hab
    · by_cases hb : (b : ℕ) < p
      · simp [ha, hb]
      · rw [if_neg ha, if_neg hb] at hab
        exact absurd rfl hab
  have h := dRepC_single_eq_zero p s ε lam H π hlam hε hDS v hv hsm b a hb.1 hb.2
  rw [← hXY] at h
  exact (GlobalTheory.HolDict.LieAct.dRepC_parts (Matrix.isUnit_det_of_left_inverse (Jm_mul_self ε)).ne_zero hX hY v).symm.trans h

end GlobalTheory.LowestKilled
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestKTypeKilledByNegativeNoncompactRootsStatement
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowestKType_killed_by_negative_noncompact_roots : ∀ (n : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin n → Bool) (lam : Fin n → ℝ) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (p : ℕ) (s : Bool), (∀ a : Fin n, ε a = if (a : ℕ) < p then s else !s) → StrictAnti lam → IsDS ε lam π → ∀ v ∈ lowKSub ε lam π, SmoothVec {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0} π v → ∀ a b : Fin n, ε a ≠ ε b → b < a → ∀ X ∈ {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0}, ∀ Y ∈ {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0}, X + Complex.I • Y = Matrix.single a b 1 → dRep π X v + Complex.I • dRep π Y v = 0 := by
  first | exact @GlobalTheory.LowestKilled.lowK_killed | exact GlobalTheory.LowestKilled.lowK_killed | (intros; apply GlobalTheory.LowestKilled.lowK_killed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtremalLowestKTypeKilledCompactRoots
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtremalLowestKTypeKilledCompactRoots
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HolRead.KCpt

open GlobalTheory.HolDict GlobalTheory.HolDict.BorelK

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Mt n → (H →L[ℂ] H)}

theorem revNeg_lt {a b : Fin n} (ha : ε a = false) (hb : ε b = false) (h : b < a) : revNeg ε a < revNeg ε b := by
  have ma : a ∈ negS ε := by simp [negS, ha]
  have mb : b ∈ negS ε := by simp [negS, hb]
  have h1 : revNeg ε a = (revOn ε ⟨a, ma⟩ : Fin n) := Equiv.Perm.ofSubtype_apply_of_mem _ ma
  have h2 : revNeg ε b = (revOn ε ⟨b, mb⟩ : Fin n) := Equiv.Perm.ofSubtype_apply_of_mem _ mb
  rw [h1, h2]
  have h3 : (⟨b, mb⟩ : {x // x ∈ negS ε}) < ⟨a, ma⟩ := h
  have h4 := ((negS ε).orderIsoOfFin rfl).symm.strictMono h3
  exact ((negS ε).orderIsoOfFin rfl).strictMono (Fin.rev_lt_rev.2 h4)

theorem isWtOn_root (hσ : IsURepOn (UJset ε) σ) {μ : Fin n → ℝ} {v : H}
    (hs : SmoothVec (lieH (Formalism.REAL.Jm ε)) σ v) (hv : IsWtOn (Formalism.REAL.Kset ε) σ μ v) (a c : Fin n) :
    IsWtOn (Formalism.REAL.Kset ε) σ (μ + Formalism.REAL.root a c) (dRepC (Formalism.REAL.Jm ε) σ (Matrix.single a c 1) v) := by
  have hh : (Formalism.REAL.Jm ε).IsHermitian := Formalism.REAL.Jm_conjTranspose ε
  have z0 : ∀ x : H, dRepC (Formalism.REAL.Jm ε) σ 0 x = 0 := by
    intro x
    simp [dRepC, conjH, dRep]
  have l1 : ∀ (s : ℂ) Z, dRepC (Formalism.REAL.Jm ε) σ (s • Z) v = s • dRepC (Formalism.REAL.Jm ε) σ Z v := by
    intro s Z
    have := LieAct.dRepC_lin hh det_Jm hσ hs s Z 0
    rwa [add_zero, z0, add_zero] at this
  have l2 : ∀ (s : ℂ) Z, dRepC (Formalism.REAL.Jm ε) σ Z (s • v) = s • dRepC (Formalism.REAL.Jm ε) σ Z v := by
    intro s Z
    have := LieAct.dRepC_vec (π := σ) hh det_Jm hs hs (s - 1) Z
    rw [sub_smul, one_smul, sub_add_cancel, sub_smul, one_smul, sub_add_cancel] at this
    exact this
  intro θ hθ
  have hinv : (diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I))⁻¹ =
      diagonal fun a => Complex.exp (-((θ a : ℂ) * Complex.I)) := by
    apply Matrix.inv_eq_left_inv
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext b
    rw [← Complex.exp_add]; simp
  have e : (diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)) * Matrix.single a c (1 : ℂ) *
      (diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I))⁻¹ =
      Complex.exp ((θ a : ℂ) * Complex.I + -((θ c : ℂ) * Complex.I)) • Matrix.single a c (1 : ℂ) := by
    rw [hinv]
    ext i j
    simp only [mul_diagonal, diagonal_mul, Matrix.smul_apply, Matrix.single_apply]
    by_cases h' : a = i ∧ c = j
    · obtain ⟨rfl, rfl⟩ := h'
      simp [Complex.exp_add]
    · simp [h']
  rw [LieAct.rep_dRepC hh det_Jm hσ hs (kset_uj hθ), e, hv θ hθ, l2, l1, smul_smul, ← Complex.exp_add]
  congr 2
  simp [Formalism.REAL.root, Pi.single_apply, add_mul, Finset.sum_add_distrib, sub_eq_add_neg]

theorem killed {lam : Fin n → ℝ} (hσ : IsURepOn (UJset ε) σ) {v : H} (hv : v ∈ lowKSub ε lam σ)
    (hs : SmoothVec (lieH (Formalism.REAL.Jm ε)) σ v)
    (hw : IsWtOn (Formalism.REAL.Kset ε) σ (fun a => Formalism.QuantumDeterminants.lowK ε lam (revNeg ε a)) v) {a c : Fin n} (hac : ε a = ε c)
    (hlt : revNeg ε a < revNeg ε c) : dRepC (Formalism.REAL.Jm ε) σ (Matrix.single a c 1) v = 0 := by
  have hε : ∀ b, ε ((revNeg ε).symm b) = ε b := fun b => by
    rw [← eps_revNeg ε ((revNeg ε).symm b), Equiv.apply_symm_apply]
  have h1 := isWtOn_perm hσ (revNeg ε).symm hε (isWtOn_root hσ hs hw a c)
  have e : (fun b => ((fun a => Formalism.QuantumDeterminants.lowK ε lam (revNeg ε a)) + Formalism.REAL.root a c) ((revNeg ε).symm b)) =
      Formalism.QuantumDeterminants.lowK ε lam + Formalism.REAL.root (revNeg ε a) (revNeg ε c) := by
    funext b
    simp [Formalism.REAL.root, Pi.single_apply, Equiv.symm_apply_eq]
  rw [e] at h1
  have h2 := orth_of_not_cdom hσ h1 (not_cdom _ hlt)
  have hK := pM_mem (revNeg ε).symm hε
  have h3 : ∀ x ∈ lowKSub ε lam σ, ⟪dRepC (Formalism.REAL.Jm ε) σ (Matrix.single a c 1) v, x⟫_ℂ = 0 := by
    intro x hx
    rw [← inner_rep hσ hK]
    exact h2 _ (stable_sSup _ hK x hx)
  exact inner_self_eq_zero.1 (inner_dRepC stable_sSup h3 hv hac)

theorem extremal_killed_compact : ∀ (n : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin n → Bool) (lam : Fin n → ℝ) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) π → ∀ v ∈ lowKSub ε lam π, SmoothVec {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0} π v → IsWtOn (Formalism.REAL.Kset ε) π (fun a => Formalism.QuantumDeterminants.lowK ε lam (revNeg ε a)) v → ∀ a b : Fin n, ((ε a = true ∧ ε b = true ∧ a < b) ∨ (ε a = false ∧ ε b = false ∧ b < a)) → ∀ X ∈ {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0}, ∀ Y ∈ {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0}, X + Complex.I • Y = Matrix.single a b 1 → dRep π X v + Complex.I • dRep π Y v = 0 := by
  intro n H _ _ ε lam π hπ v hv hs hw a b hab X hX Y hY hE
  rw [← LieAct.dRepC_parts (G := Formalism.REAL.Jm ε) det_Jm hX hY, hE]
  rcases hab with ⟨ha, hb, h⟩ | ⟨ha, hb, h⟩
  · exact killed hπ hv hs hw (ha.trans hb.symm) (by rwa [revNeg_of_pos ε ha, revNeg_of_pos ε hb])
  · exact killed hπ hv hs hw (ha.trans hb.symm) (revNeg_lt ha hb h)

end GlobalTheory.HolRead.KCpt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtremalLowestKTypeKilledCompactRootsStatement
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extremal_lowestKType_killed_compact_roots : ∀ (n : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin n → Bool) (lam : Fin n → ℝ) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) π → ∀ v ∈ lowKSub ε lam π, SmoothVec {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0} π v → IsWtOn (Formalism.REAL.Kset ε) π (fun a => Formalism.QuantumDeterminants.lowK ε lam (revNeg ε a)) v → ∀ a b : Fin n, ((ε a = true ∧ ε b = true ∧ a < b) ∨ (ε a = false ∧ ε b = false ∧ b < a)) → ∀ X ∈ {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0}, ∀ Y ∈ {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0}, X + Complex.I • Y = Matrix.single a b 1 → dRep π X v + Complex.I • dRep π Y v = 0 := by
  first | exact @GlobalTheory.HolRead.KCpt.extremal_killed_compact | exact GlobalTheory.HolRead.KCpt.extremal_killed_compact | (intros; apply GlobalTheory.HolRead.KCpt.extremal_killed_compact <;> assumption)
end
end

open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolRead.ExtKill

section Conj

variable {n : ℕ} {J P G : Matrix (Fin n) (Fin n) ℂ}

theorem conj_cancel (hP : IsUnit P) (g : Matrix (Fin n) (Fin n) ℂ) : P * (P⁻¹ * g * P) * P⁻¹ = g := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  calc P * (P⁻¹ * g * P) * P⁻¹ = (P * P⁻¹) * g * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
    _ = g := by rw [h1]; simp

theorem lie_conj (hP : IsUnit P) (hG : Pᴴ * J * P = G) {X : Matrix (Fin n) (Fin n) ℂ} (hX : Xᴴ * G + G * X = 0) :
    (P * X * P⁻¹)ᴴ * J + J * (P * X * P⁻¹) = 0 := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  calc (P * X * P⁻¹)ᴴ * J + J * (P * X * P⁻¹)
      = (P * X * P⁻¹)ᴴ * J * (P * P⁻¹) + (P * P⁻¹)ᴴ * J * (P * X * P⁻¹) := by rw [h1]; simp
    _ = (P⁻¹)ᴴ * (Xᴴ * G + G * X) * P⁻¹ := by
        rw [← hG]; simp only [conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul]
    _ = 0 := by rw [hX]; simp

theorem lie_conj_inv (hP : IsUnit P) (hG : Pᴴ * J * P = G) {X : Matrix (Fin n) (Fin n) ℂ} (hX : Xᴴ * J + J * X = 0) :
    (P⁻¹ * X * P)ᴴ * G + G * (P⁻¹ * X * P) = 0 := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  calc (P⁻¹ * X * P)ᴴ * G + G * (P⁻¹ * X * P)
      = Pᴴ * (Xᴴ * ((P * P⁻¹)ᴴ * J) + J * (P * P⁻¹) * X) * P := by
        rw [← hG]; simp only [conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul]
    _ = 0 := by rw [h1, conjTranspose_one, Matrix.one_mul, Matrix.mul_one, hX]; simp

theorem exp_smul_conj (hP : IsUnit P) (X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    NormedSpace.exp (t • (P * X * P⁻¹)) = P * NormedSpace.exp (t • X) * P⁻¹ := by
  rw [← Matrix.exp_conj _ _ hP, Matrix.mul_smul, Matrix.smul_mul]

theorem exp_smul_conj_inv (hP : IsUnit P) (X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    NormedSpace.exp (t • (P⁻¹ * X * P)) = P⁻¹ * NormedSpace.exp (t • X) * P := by
  rw [← Matrix.exp_conj' _ _ hP, Matrix.mul_smul, Matrix.smul_mul]

theorem prod_conj_inv (hP : IsUnit P) (l : List (Matrix (Fin n) (Fin n) ℂ)) :
    (l.map fun g => P⁻¹ * g * P).prod = P⁻¹ * l.prod * P := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  induction l with
  | nil => simp [h2]
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, List.prod_cons, ih]
    calc P⁻¹ * a * P * (P⁻¹ * l.prod * P) = P⁻¹ * a * (P * P⁻¹) * l.prod * P := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1]; simp only [Matrix.mul_assoc, Matrix.one_mul]

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem dRep_conj (hP : IsUnit P) (X : Matrix (Fin n) (Fin n) ℂ) (w : H) :
    dRep (fun g => σ (P * g * P⁻¹)) X w = dRep σ (P * X * P⁻¹) w := by
  unfold dRep
  simp only [exp_smul_conj hP]

theorem smoothVec_conj (hP : IsUnit P) (hG : Pᴴ * J * P = G) {w : H}
    (hw : SmoothVec {X | Xᴴ * G + G * X = 0} (fun g => σ (P * g * P⁻¹)) w) :
    SmoothVec {X | Xᴴ * J + J * X = 0} σ w := by
  intro k Xs hXs
  have h := hw k (fun i => P⁻¹ * Xs i * P) fun i => lie_conj_inv hP hG (hXs i)
  have e : ∀ t : Fin k → ℝ, P * (List.ofFn fun i => NormedSpace.exp (t i • (P⁻¹ * Xs i * P))).prod * P⁻¹ =
      (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod := by
    intro t
    have : (List.ofFn fun i => NormedSpace.exp (t i • (P⁻¹ * Xs i * P))) =
        (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).map fun g => P⁻¹ * g * P := by
      rw [List.map_ofFn]
      congr 1
      funext i
      exact exp_smul_conj_inv hP _ _
    rw [this, prod_conj_inv hP, conj_cancel hP]
  simpa only [e] using h

end Conj

theorem kill_and_weight : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (T : MMap M), IsInfFam θ → IsMultMap θ M J χ T → ∀ v : M.Vec, IsExtVec M v → ∀ (ρ : D.what₂.Tau) (p : ℕ) (s : Bool), (∀ a : Fin V.rank, M.ε ρ a = if (a : ℕ) < p then s else !s) → (∀ a b, KillPair (M.ε ρ) a b → RderC θ V ρ ((M.fr ρ)⁻¹ * Matrix.single a b 1 * M.fr ρ) (T v) = 0) ∧ ∀ (t : Fin V.rank → ℝ) (g : GA D V), T v (g * atTau θ V ρ ((M.fr ρ)⁻¹ * Matrix.diagonal (fun a => Complex.exp ((t a : ℂ) * Complex.I)) * M.fr ρ)) = Complex.exp (((∑ a, extWt M ρ a * t a : ℝ) : ℂ) * Complex.I) * T v g := by
  intro D θ V S M J χ T hθ hT v hv ρ p s hε
  have hP := M.fr_unit ρ
  have hG := M.fr_gram ρ
  obtain ⟨-, hlow, hwt⟩ := hv ρ
  have hlow' : (v ρ : M.H ρ) ∈ lowKSub (M.ε ρ) (M.lam ρ) (M.σ ρ) := hlow
  refine ⟨fun a b hab => ?_, fun t g => ?_⟩
  · obtain ⟨hs, hd⟩ := GlobalTheory.T.right_derivative_multiplicity_map_value_eq D θ V S M J χ T hθ hT v ρ
    have hs' := smoothVec_conj (σ := M.σ ρ) hP hG hs
    set Z := (M.fr ρ)⁻¹ * Matrix.single a b 1 * M.fr ρ with hZ
    obtain ⟨hX, hY⟩ := GlobalTheory.SmoothAutCheck.parts_mem V ρ Z
    have hXY := GlobalTheory.SmoothAutCheck.parts_sum V ρ Z
    unfold RderC
    generalize (1 / 2 : ℂ) • (Z + conjAt V ρ Z) = X at hX hXY ⊢
    generalize (1 / (2 * Complex.I)) • (Z - conjAt V ρ Z) = Y at hY hXY ⊢
    obtain ⟨u, hu, eu⟩ := hd X hX
    obtain ⟨u', hu', eu'⟩ := hd Y hY
    have hX' := lie_conj hP hG hX
    have hY' := lie_conj hP hG hY
    have hE : M.fr ρ * X * (M.fr ρ)⁻¹ + Complex.I • (M.fr ρ * Y * (M.fr ρ)⁻¹) = Matrix.single a b 1 := by
      rw [← conj_cancel hP (Matrix.single a b 1), ← hZ, ← hXY]
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
    have key : dRep (M.σ ρ) (M.fr ρ * X * (M.fr ρ)⁻¹) (v ρ : M.H ρ) +
        Complex.I • dRep (M.σ ρ) (M.fr ρ * Y * (M.fr ρ)⁻¹) (v ρ : M.H ρ) = 0 := by
      rcases hab with h | h | h
      · exact GlobalTheory.T.extremal_lowestKType_killed_compact_roots _ _ _ _ _ (M.ds ρ).2.2.1 _ hlow' hs' hwt a b (Or.inl h) _ hX' _ hY' hE
      · exact GlobalTheory.T.extremal_lowestKType_killed_compact_roots _ _ _ _ _ (M.ds ρ).2.2.1 _ hlow' hs' hwt a b (Or.inr h) _ hX' _ hY' hE
      · exact GlobalTheory.T.lowestKType_killed_by_negative_noncompact_roots _ _ _ _ _ p s hε (M.enum ρ).1 (M.ds ρ) _ hlow' hs' a b h.1 h.2 _ hX' _ hY' hE
    have h0 : u + Complex.I • u' = 0 := by
      apply Subtype.ext
      show (u : M.H ρ) + Complex.I • (u' : M.H ρ) = 0
      rw [hu, hu', ← key, ← dRep_conj hP, ← dRep_conj hP]
      rfl
    have hsmul : T (Function.update v ρ (Complex.I • u')) = Complex.I • T (Function.update v ρ u') := by
      simpa only [RingHom.id_apply] using T.map_update_smul v ρ Complex.I u'
    rw [eu, eu', ← hsmul, ← T.map_update_add, h0, T.map_update_zero]
  · have hK := Formalism.IndefR.FWT.diag_mem (ε := M.ε ρ) t
    have hg := GlobalTheory.HolDict.ModelRep.conj_mem_inv hP hG (kset_uj hK)
    have h := hT.equiv ρ _ hg v (Complex.exp (((∑ a, extWt M ρ a * t a : ℝ) : ℂ) * Complex.I) • v ρ) (by
      unfold DSModel.rep
      rw [conj_cancel hP, hwt t hK]
      rfl)
    rw [T.map_update_smul, Function.update_eq_self] at h
    exact (congrFun h g).symm

end GlobalTheory.HolRead.ExtKill
