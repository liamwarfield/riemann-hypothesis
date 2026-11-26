module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.HdFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullHkSmooth
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.LocInt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PerKer

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.PerLim
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CorrLim
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.ConeCpt
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.coneCpt :
    UpperTheory.V.Cj.H.ConeCpt := by
  intro E _ _ a K hK hKc
  refine ⟨_, (UpperTheory.V.Cj.A.sandCpt E a).2 K hK hKc, fun p hp => ?_⟩
  obtain ⟨g, rfl⟩ := hK hp
  exact ⟨g, hp, rfl⟩
end

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem basis_bd {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {n : ℕ}
    (b : Module.Basis (Fin n) ℝ V) (q : ℕ) : ∃ c : ℝ, 0 ≤ c ∧ ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F]
      (m : V [⋀^Fin q]→L[ℝ] F) (δ : ℝ), 0 ≤ δ → (∀ I : Fin q → Fin n, ‖m fun i => b (I i)‖ ≤ δ) →
      ∀ v, ‖m v‖ ≤ c * δ * ∏ i, ‖v i‖ := by
  refine ⟨∑ I : Fin q → Fin n, ∏ i, ‖LinearMap.toContinuousLinearMap (b.coord (I i))‖, by positivity, ?_⟩
  intro F _ _ m δ hδ h v
  have e : m v = ∑ I : Fin q → Fin n, (∏ i, b.repr (v i) (I i)) • m fun i => b (I i) := by
    have e1 : v = fun i => ∑ j, b.repr (v i) j • b j := funext fun i => (b.sum_repr (v i)).symm
    conv_lhs => rw [e1]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [ContinuousAlternatingMap.map_sum]
    exact Finset.sum_congr rfl fun I _ => m.map_smul_univ _ _
  rw [e, mul_assoc, Finset.sum_mul]
  refine norm_sum_le_of_le _ fun I _ => ?_
  rw [norm_smul, norm_prod, mul_comm δ, ← mul_assoc, ← Finset.prod_mul_distrib]
  refine mul_le_mul (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ => ?_) (h I) (norm_nonneg _) (by positivity)
  exact (LinearMap.toContinuousLinearMap (b.coord (I i))).le_opNorm (v i)

private theorem ev_cmp {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a d : ℕ}
    (m : Sm E a ⊗[ℂ] (Fin d → ℂ)) (g : GA E a) (j : Fin d) : ev m g j = (cmp j m).1 g := by
  induction m using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]; rfl
  | tmul φ v => simp [mul_comm]
  | add x y hx hy => simp only [map_add (f := _), Pi.add_apply, Submodule.coe_add, hx, hy]

private theorem cont_inf (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) :
    Continuous (infGL E a) := by
  have hs : Continuous (sInf E : Cinf E → Ad E) := (GlobalTheory.CuspRep.continuous_infEq E).prodMk continuous_const
  exact Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map hs))

theorem UpperTheory.V.Cj.H.corrLim :
    UpperTheory.V.Cj.H.CorrLim := by
  intro E _ _ _ a ho U Ξ q ω w hw hl s K hK hKc
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
  obtain ⟨C, hC, hCK⟩ := coneCpt E a K hK hKc
  have c1 : Continuous fun g : GL (Fin a) (Cinf E) => toL g.val :=
    Units.continuous_val (M := Matrix (Fin a) (Fin a) (Cinf E))
  have c2 : Continuous fun g : GL (Fin a) (Cinf E) => toL (g⁻¹).val :=
    Units.continuous_coe_inv (M := Matrix (Fin a) (Fin a) (Cinf E))
  obtain ⟨R1, hR1⟩ := hC.exists_bound_of_continuousOn c1.continuousOn
  obtain ⟨R2, hR2⟩ := hC.exists_bound_of_continuousOn c2.continuousOn
  obtain ⟨B, hB, hM⟩ := matBd E a Ξ (max R1 R2)
  let b := Module.finBasis ℝ (HV E a)
  obtain ⟨c, hc, hb⟩ := basis_bd b q
  have hD : IsCompact ((fun g => infGL E a g * finGL E a x) '' C) :=
    hC.image ((cont_inf E a).mul continuous_const)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hA : 0 ≤ c * B * B ^ q := by positivity
  obtain ⟨δ, hδ, hδε⟩ := exists_pos_mul_lt hε (c * B * B ^ q)
  have hev : ∀ᶠ k in atTop, ∀ (I : Fin q → Fin (Module.finrank ℝ (HV E a))) (j : Fin Ξ.d),
      ∀ y ∈ (fun g => infGL E a g * finGL E a x) '' C,
        dist ((0 : Sm E a).1 y) ((cmp j (ω k fun i => hv.symm (b (I i)))).1 y) < δ :=
    eventually_all.2 fun I => eventually_all.2 fun j =>
      Metric.tendstoUniformlyOn_iff.1 (hl (fun i => hv.symm (b (I i))) j _ hD) δ hδ
  filter_upwards [hev] with k hk p hp
  obtain ⟨g, hg, rfl⟩ := hCK p hp
  obtain ⟨m1, -, m3⟩ := hM g ((hR1 g hg).trans (le_max_left _ _)) ((hR2 g hg).trans (le_max_right _ _))
  rw [Pi.zero_apply, dist_zero_left]
  refine lt_of_le_of_lt (ContinuousAlternatingMap.opNorm_le_bound _ (by positivity) fun v => ?_) hδε
  have key := hb _ (((w k).1 x (sand g (hOne E a))).compContinuousLinearMap ((2 : ℝ) • sand g)) (B * δ)
    (by positivity) (fun I => ?_) fun i => (1 / 2 : ℝ) • sand g⁻¹ (v i)
  · have e : (((2 : ℝ) • sand g : HV E a →L[ℝ] HV E a) ∘ fun i => (1 / 2 : ℝ) • sand g⁻¹ (v i)) = v := by
      funext i
      simp only [Function.comp_apply, ContinuousLinearMap.smul_apply, map_smul, smul_smul]
      rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      norm_num
    rw [ContinuousAlternatingMap.compContinuousLinearMap_apply, e] at key
    have hp : ∏ i, ‖(1 / 2 : ℝ) • sand g⁻¹ (v i)‖ ≤ B ^ q * ∏ i, ‖v i‖ := by
      have : B ^ q * ∏ i, ‖v i‖ = ∏ i, B * ‖v i‖ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [this]
      refine Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => ?_
      rw [norm_smul]
      have h3 := m3 (v i)
      have h4 := norm_nonneg (sand g⁻¹ (v i))
      have h5 : ‖(1 / 2 : ℝ)‖ = 1 / 2 := by norm_num
      rw [h5]
      linarith
    calc _ ≤ _ := key
      _ ≤ c * (B * δ) * (B ^ q * ∏ i, ‖v i‖) := mul_le_mul_of_nonneg_left hp (by positivity)
      _ = _ := by ring
  · have hc := hw k g x fun i => hv.symm (b (I i))
    simp only [LinearEquiv.apply_symm_apply] at hc
    rw [ContinuousAlternatingMap.compContinuousLinearMap_apply]
    refine (congrArg norm hc).le.trans ((m1 _).trans (mul_le_mul_of_nonneg_left ?_ hB))
    refine (pi_norm_le_iff_of_nonneg hδ.le).2 fun j => ?_
    have := hk I j _ ⟨g, hg, rfl⟩
    rw [ev_cmp]
    simpa using this.le
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.ZigLim
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.PoinOp
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.ConeLim
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.coneLim :
    UpperTheory.V.Cj.H.ConeLim := by
  intro V F _ _ _ _ Y hY p hp q w hw K hKY hK
  obtain ⟨C, hC⟩ := (hK.image (continuous_id.sub continuous_const :
    Continuous fun x : V => x - p)).isBounded.exists_norm_le
  set K' : Set V := (fun z : ℝ × V => p + z.1 • (z.2 - p)) '' (Set.Icc (0 : ℝ) 1 ×ˢ K)
  have hK'c : IsCompact K' := (isCompact_Icc.prod hK).image (by fun_prop)
  have hK'Y : K' ⊆ Y := by
    rintro _ ⟨⟨t, x⟩, ⟨ht, hx⟩, rfl⟩
    exact hY.add_smul_sub_mem hp (hKY hx) ht
  have hwK := hw K' hK'Y hK'c
  rw [Metric.tendstoUniformlyOn_iff] at hwK ⊢
  intro ε hε
  have hR : 0 < |C| + 1 := by positivity
  filter_upwards [hwK (ε / 2 / (|C| + 1)) (by positivity)] with k hk x hx
  simp only [Pi.zero_apply, dist_zero_left] at hk ⊢
  have hxp : ‖x - p‖ ≤ |C| + 1 := by
    have h0 := hC (x - p) ⟨x, hx, rfl⟩
    linarith [le_abs_self C]
  have hbound : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
      ‖t ^ q • (w k (p + t • (x - p))).curryLeft (x - p)‖ ≤ ε / 2 / (|C| + 1) * (|C| + 1) := by
    intro t ht
    rw [Set.uIoc_of_le zero_le_one] at ht
    have hy : p + t • (x - p) ∈ K' := ⟨(t, x), ⟨⟨ht.1.le, ht.2⟩, hx⟩, rfl⟩
    have h1 := hk _ hy
    rw [norm_smul, norm_pow, Real.norm_eq_abs, abs_of_pos ht.1]
    have h2 : t ^ q ≤ 1 := pow_le_one₀ ht.1.le ht.2
    have h3 : ‖(w k (p + t • (x - p))).curryLeft (x - p)‖
        ≤ ‖w k (p + t • (x - p))‖ * ‖x - p‖ := by
      refine (ContinuousLinearMap.le_opNorm _ _).trans_eq ?_
      rw [ContinuousAlternatingMap.norm_curryLeft]
    have h4 : ‖w k (p + t • (x - p))‖ * ‖x - p‖ ≤ ε / 2 / (|C| + 1) * (|C| + 1) :=
      mul_le_mul h1.le hxp (norm_nonneg _) (by positivity)
    calc t ^ q * ‖(w k (p + t • (x - p))).curryLeft (x - p)‖
        ≤ 1 * ‖(w k (p + t • (x - p))).curryLeft (x - p)‖ :=
          mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      _ ≤ ε / 2 / (|C| + 1) * (|C| + 1) := by
          rw [one_mul]
          exact h3.trans h4
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  have e : ε / 2 / (|C| + 1) * (|C| + 1) = ε / 2 := by field_simp
  rw [e] at hint
  simp only [sub_zero, abs_one, mul_one] at hint
  calc ‖UpperTheory.V.Cj.H.coneOp p (w k) x‖
      = ‖∫ t in (0 : ℝ)..1, t ^ q • (w k (p + t • (x - p))).curryLeft (x - p)‖ := rfl
    _ ≤ ε / 2 := hint
    _ < ε := by linarith
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.ConeD
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.coneD :
    UpperTheory.V.Cj.H.ConeD := by
  intro V F _ _ _ _ _ _ Y hYo hYc p hp q w hw
  have hseg : ∀ x ∈ Y, ∀ t ∈ Set.Icc (0:ℝ) 1, p + t • (x - p) ∈ Y := by
    intro x hx t ht
    have h := hYc hp hx (sub_nonneg.2 ht.2) ht.1 (by ring)
    convert h using 1
    rw [smul_sub, sub_smul, one_smul]
    abel
  let g : V × ℝ → V := fun z => p + z.2 • (z.1 - p)
  have hg : ContDiff ℝ ⊤ g := by
    exact contDiff_const.add (contDiff_snd.smul (contDiff_fst.sub contDiff_const))
  let W : Set (V × ℝ) := g ⁻¹' Y
  have hW : IsOpen W := hYo.preimage hg.continuous
  let Φ : V × ℝ → V [⋀^Fin q]→L[ℝ] F :=
    fun z => z.2 ^ q • (w (p + z.2 • (z.1 - p))).curryLeft (z.1 - p)
  have hΦ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ W := by
    have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : V × ℝ => w (g z)) W :=
      hw.comp (hg.of_le le_top).contDiffOn (fun z hz => hz)
    let L := (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := V) (F := F) (n := q)).toContinuousLinearMap
    have hfst : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : V × ℝ => z.1 - p) :=
      contDiff_fst.sub contDiff_const
    have h2 := (L.contDiff.comp_contDiffOn h1).clm_apply (hfst.contDiffOn (s := W))
    have hsnd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : V × ℝ => z.2 ^ q) :=
      contDiff_snd.pow q
    exact hsnd.contDiffOn.smul h2
  have hsub : Y ×ˢ Set.Icc (0:ℝ) 1 ⊆ W := fun z hz => hseg z.1 hz.1 z.2 hz.2
  refine ⟨UpperTheory.V.Lit.Dr.paramSmooth V (V [⋀^Fin q]→L[ℝ] F) Y W Φ hYo hW hsub hΦ, ?_⟩
  intro hcl x hx
  have hd := UpperTheory.V.Lit.Dr.paramDeriv V (V [⋀^Fin q]→L[ℝ] F) x W Φ hW (fun t ht => hseg x hx t ht) hΦ
  have hI : Set.uIcc (0:ℝ) 1 = Set.Icc 0 1 := Set.uIcc_of_le zero_le_one
  let A := ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ V F (n := q)
  have hint : IntervalIntegrable (fun t => fderiv ℝ (fun y => Φ (y, t)) x) MeasureTheory.volume 0 1 :=
    (hI ▸ hd.1).intervalIntegrable
  have hcont' : ContinuousOn (fun t => A (fderiv ℝ (fun y => Φ (y, t)) x)) (Set.uIcc 0 1) :=
    hI ▸ (A.continuous.comp_continuousOn hd.1)
  have hderiv : ∀ t ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun r : ℝ => r ^ (q + 1) • w (p + r • (x - p))) (A (fderiv ℝ (fun y => Φ (y, t)) x)) t := by
    intro t ht
    rw [hI] at ht
    have hm := hseg x hx t ht
    have hdiff : DifferentiableAt ℝ w (p + t • (x - p)) :=
      (hw.contDiffAt (hYo.mem_nhds hm)).differentiableAt (by simp)
    exact UpperTheory.V.Lit.Dr.poinPt V F q w p x t hdiff (hcl _ hm)
  have hfd : fderiv ℝ (UpperTheory.V.Cj.H.coneOp p w) x = ∫ t in (0:ℝ)..1, fderiv ℝ (fun y => Φ (y, t)) x :=
    hd.2.fderiv
  have key : extDeriv (UpperTheory.V.Cj.H.coneOp p w) x = A (fderiv ℝ (UpperTheory.V.Cj.H.coneOp p w) x) := rfl
  rw [key, hfd, ← A.intervalIntegral_comp_comm hint,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont'.intervalIntegrable)]
  simp
end

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

section

variable {Γ V S : Type} [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] {d : ℕ} (G : Dr.Geo Γ V S d)

private theorem tr_tr (q : ℕ) (γ δ : Γ) (h : γ * δ = 1) (m : V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) :
    G.tr q γ (G.tr q δ m) = m := by
  have hδ : δ = γ⁻¹ := eq_inv_of_mul_eq_one_right h
  subst hδ
  ext v
  rw [Geo.tr_apply, Geo.tr_apply, Matrix.mulVec_mulVec, ← map_mul, mul_inv_cancel, map_one,
    Matrix.one_mulVec]
  have hv : (fun i => (G.ρ γ⁻¹⁻¹) ((G.ρ γ⁻¹) (v i))) = v := by
    funext i
    exact Geo.ρ_inv_apply G γ⁻¹ (v i)
  rw [hv]

private theorem tr_coneOp (q : ℕ) (γ : Γ) (w : V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) (p x : V) :
    G.tr q γ (coneOp p w (G.ρ γ⁻¹ x)) = coneOp (G.ρ γ p) (fun y => G.tr (q + 1) γ (w (G.ρ γ⁻¹ y))) x := by
  let L : (V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) ≃L[ℝ] (V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) :=
    ContinuousLinearEquiv.equivOfInverse (G.tr q γ) (G.tr q γ⁻¹)
      (fun m => tr_tr G q γ⁻¹ γ (inv_mul_cancel γ) m)
      (fun m => tr_tr G q γ γ⁻¹ (mul_inv_cancel γ) m)
  have hL : ∀ m, L m = G.tr q γ m := fun m => rfl
  have key : ∀ f : ℝ → (V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)),
      L (∫ t in (0:ℝ)..1, f t) = ∫ t in (0:ℝ)..1, L (f t) := by
    intro f
    simp only [intervalIntegral, map_sub, L.integral_comp_comm]
  have hpt : ∀ t : ℝ, G.ρ γ⁻¹ (G.ρ γ p + t • (x - G.ρ γ p)) = p + t • (G.ρ γ⁻¹ x - p) := by
    intro t
    simp [map_add (f := _), map_smul, map_sub, Geo.ρ_inv_apply]
  rw [← hL]
  unfold coneOp
  rw [key]
  congr 1
  funext t
  rw [map_smul]
  beta_reduce
  rw [hpt]
  congr 1
  ext v
  rw [hL, Geo.tr_apply, ContinuousAlternatingMap.curryLeft_apply_apply,
    ContinuousAlternatingMap.curryLeft_apply_apply, Geo.tr_apply]
  congr 2
  funext i
  refine Fin.cases ?_ ?_ i
  · simp [Geo.ρ_inv_apply]
  · intro j
    simp

end

theorem UpperTheory.V.Cj.H.poinOp :
    UpperTheory.V.Cj.H.PoinOp := by
  intro Γ V S _ _ _ _ d G hconv q
  classical
  have hD := coneD V (Fin d → ℂ) G.Y G.isOpen hconv
  let f : V → G.Om (q + 1) → S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ) :=
    fun p w s x => if x ∈ G.Y then coneOp p ((w : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s) x else 0
  have hwm : ∀ (w : G.Om (q + 1)) (s : S),
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ((w : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s) G.Y ∧
        ∀ x ∉ G.Y, (w : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s x = 0 := fun w => w.2
  have hf : ∀ p ∈ G.Y, ∀ w, f p w ∈ G.Om q := by
    intro p hp w
    refine fun s => ⟨?_, ?_⟩
    · exact ((hD p hp q _ (hwm w s).1).1).congr (fun x hx => if_pos hx)
    · intro x hx
      exact if_neg hx
  let K : V → G.Om (q + 1) → G.Om q := fun p w => if hp : p ∈ G.Y then ⟨f p w, hf p hp w⟩ else 0
  have hK : ∀ p (hp : p ∈ G.Y) w, ((K p w : G.Om q) : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) = f p w := by
    intro p hp w
    simp [K, hp]
  refine ⟨K, ?_, ?_, ?_⟩
  · intro p hp w hw0
    apply Subtype.ext
    funext s x
    by_cases hx : x ∈ G.Y
    · rw [Geo.dOm_apply G (K p w) s hx, hK p hp w]
      have hclosed : ∀ y ∈ G.Y, extDeriv ((w : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s) y = 0 := by
        intro y hy
        have h0 := congrArg
          (fun u : G.Om (q + 1 + 1) => (u : S → V → V [⋀^Fin (q + 1 + 1)]→L[ℝ] (Fin d → ℂ)) s y) hw0
        rw [Geo.dOm_apply G w s hy] at h0
        simpa using h0
      have hloc : extDeriv (f p w s) x =
          extDeriv (coneOp p ((w : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s)) x := by
        rw [← extDerivWithin_univ, ← extDerivWithin_univ]
        apply Filter.EventuallyEq.extDerivWithin_eq_of_mem _ (Set.mem_univ x)
        rw [nhdsWithin_univ]
        exact Filter.eventually_of_mem (G.isOpen.mem_nhds hx) (fun y hy => if_pos hy)
      rw [hloc]
      exact (hD p hp q _ (hwm w s).1).2 hclosed x hx
    · have h1 := ((G.dOm q (K p w)).2 s).2 x hx
      have h2 := (hwm w s).2 x hx
      rw [h1, h2]
  · intro γ p hp w
    have hp' : G.ρ γ p ∈ G.Y := G.maps γ p hp
    apply Subtype.ext
    funext s x
    show G.tr q γ (((K p w : G.Om q) : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) (G.σ γ⁻¹ s) (G.ρ γ⁻¹ x)) =
      ((K (G.ρ γ p) (G.act (q + 1) γ w) : G.Om q) : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s x
    rw [hK p hp, hK _ hp']
    by_cases hx : x ∈ G.Y
    · have hx' : G.ρ γ⁻¹ x ∈ G.Y := G.maps γ⁻¹ x hx
      simp only [f, if_pos hx, if_pos hx']
      exact tr_coneOp G q γ _ p x
    · have hx' : G.ρ γ⁻¹ x ∉ G.Y := by
        intro h
        apply hx
        have h2 := G.maps γ _ h
        have h3 := Geo.ρ_inv_apply G γ⁻¹ x
        rw [inv_inv] at h3
        rwa [h3] at h2
      simp only [f, if_neg hx, if_neg hx', map_zero]
  · intro p hp w hw s C hC hCc
    have h := coneLim V (Fin d → ℂ) G.Y hconv p hp q
      (fun k => ((w k : G.Om (q + 1)) : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s)
      (fun C' hC' hC'c => hw s C' hC' hC'c) C hC hCc
    refine h.congr ?_
    filter_upwards with k
    intro x hx
    rw [hK p hp]
    simp [f, hC hx]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.HdHd
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.hdHd :
    UpperTheory.V.Cj.H.HdHd := by
  intro Γ M _ _ _ ρ k b hb
  refine ⟨?_, fun x _ => UpperTheory.V.Cj.A.hdFacts.1 Γ M b x⟩
  exact UpperTheory.V.Cj.A.hdFacts.2.2.2.2.2 Γ Γ M ρ k b hb
end

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

section

variable {Γ V S : Type} [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] {d : ℕ} {G : Dr.Geo Γ V S d} {q : ℕ}

private theorem fLim_add {w w' : ℕ → G.Om q} (h : FLim G w) (h' : FLim G w') : FLim G fun j => w j + w' j := by
  intro s K hK hc
  have := (h s K hK hc).add (h' s K hK hc)
  rw [add_zero] at this
  exact this

private theorem fLim_zsmul (n : ℤ) {w : ℕ → G.Om q} (h : FLim G w) : FLim G fun j => n • w j := by
  intro s K hK hKc
  have h1 := (uniformContinuous_id.const_smul n).comp_tendstoUniformlyOn (h s K hK hKc)
  convert (preTransparency := .reducible) h1 using 1
  · funext k x
    simp
  · funext x
    simp

private theorem fLim_sum {ι : Type} (T : Finset ι) {w : ι → ℕ → G.Om q} (h : ∀ i ∈ T, FLim G (w i)) :
    FLim G fun j => ∑ i ∈ T, w i j := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro s K _ _
    simp only [Finset.sum_empty, ZeroMemClass.coe_zero, Pi.zero_apply]
    exact Metric.tendstoUniformlyOn_iff.2 fun ε hε =>
      Filter.Eventually.of_forall fun _ x _ => by simpa using hε
  | insert i T hi ih =>
    have hsum := fLim_add (h i (Finset.mem_insert_self i T))
      (ih fun i' hi' => h i' (Finset.mem_insert_of_mem hi'))
    simpa [Finset.sum_insert hi] using hsum

end

theorem UpperTheory.V.Cj.H.zigLim :
    UpperTheory.V.Cj.H.ZigLim := by
  intro Γ V S _ _ _ _ d G hconv hne
  obtain ⟨p, hp⟩ := hne
  have hincl := inclFacts Γ V S d G hconv ⟨p, hp⟩
  have main : ∀ (q k : ℕ) (u : ℕ → List Γ → G.Om q), (∀ j, HCoc (G.act q) k (u j)) →
      (∀ j (x : List Γ), x.length = k + 1 → G.dOm q (u j x) = 0) →
      (∀ x : List Γ, x.length = k + 1 → FLim G fun j => u j x) →
      ∃ c : ℕ → List Γ → S → Fin d → ℂ, (∀ j, Zig G q k (u j) (c j)) ∧
        ∀ x : List Γ, x.length = k + q + 1 → ∀ s, Tendsto (fun j => c j x s) atTop (𝓝 0) := by
    intro q
    induction q with
    | zero =>
      intro k u _ hcl hlim
      classical
      have hex : ∀ j (x : List Γ), x.length = k + 1 → ∃ f, G.incl f = u j x :=
        fun j x hx => (hincl.2.2 (u j x)).mp (hcl j x hx)
      choose f hf using hex
      refine ⟨fun j x => if h : x.length = k + 1 then f j x h else 0, ?_, ?_⟩
      · intro j x hx
        show u j x = G.incl (if h : x.length = k + 1 then f j x h else 0)
        rw [dif_pos hx, hf j x hx]
      · intro x hx s
        have hx' : x.length = k + 1 := by simpa using hx
        have ht := (hlim x hx' s {p} (Set.singleton_subset_iff.2 hp)
          isCompact_singleton).tendsto_at (Set.mem_singleton p)
        have hc := ((continuous_eval_const (fun _ : Fin 0 => (0 : V))).tendsto _).comp ht
        have heq : ∀ j, ((u j x : S → V → V [⋀^Fin 0]→L[ℝ] (Fin d → ℂ)) s p) (fun _ => 0) =
            f j x hx' s := by
          intro j
          rw [← hf j x hx']
          simp [Dr.Geo.incl, Set.indicator_of_mem hp]
        simp only [dif_pos hx']
        have hfun : (fun j => f j x hx' s) =
            fun j => ((u j x : S → V → V [⋀^Fin 0]→L[ℝ] (Fin d → ℂ)) s p) (fun _ => 0) :=
          funext fun j => (heq j).symm
        rw [hfun]
        simp at hc
        exact hc
    | succ q ih =>
      intro k u hcoc hcl hlim
      obtain ⟨K, hK1, hK2, hK3⟩ := poinOp Γ V S d G hconv q
      have hpt : ∀ x : List Γ, G.ρ (x.headD 1) p ∈ G.Y := fun x => G.maps _ p hp
      have hbeq : ∀ j, HEquiv (G.act q) k (fun x => K (G.ρ (x.headD 1) p) (u j x)) := by
        intro j γ x hx
        have hne : x ≠ [] := by
          rintro rfl
          simp at hx
        obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_ne_nil hne
        have hu := (hcoc j).1 γ (y :: ys) hx
        simp only [List.map_cons] at hu
        simp only [List.map_cons, List.headD_cons, map_mul]
        rw [hu, hK2 γ _ (G.maps y p hp)]
        rfl
      have hlen : ∀ (x : List Γ) i, x.length = k + 1 + 1 → i ∈ Finset.range x.length →
          (x.eraseIdx i).length = k + 1 := by
        intro x i hx hi
        rw [List.length_eraseIdx_of_lt (Finset.mem_range.1 hi)]
        omega
      have hcl' : ∀ j (x : List Γ), x.length = k + 1 + 1 →
          G.dOm q (hd (fun x => K (G.ρ (x.headD 1) p) (u j x)) x) = 0 := by
        intro j x hx
        have h0 := (hcoc j).2 x hx
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [hd, map_sum, map_zsmul] at h0 ⊢
        rw [← h0]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [hK1 _ (hpt _) _ (hcl j _ (hlen x i hx hi))]
      have hlim' : ∀ x : List Γ, x.length = k + 1 + 1 →
          FLim G fun j => hd (fun x => K (G.ρ (x.headD 1) p) (u j x)) x := by
        intro x hx
        simp only [hd]
        apply fLim_sum
        intro i hi
        apply fLim_zsmul
        exact hK3 _ (hpt _) _ (hlim _ (hlen x i hx hi))
      obtain ⟨c, hc1, hc2⟩ := ih (k + 1) (fun j => hd (fun x => K (G.ρ (x.headD 1) p) (u j x)))
        (fun j => hdHd Γ (G.Om q) (G.act q) k _ (hbeq j)) hcl' hlim'
      refine ⟨c, fun j => ⟨_, hbeq j, fun x hx => hK1 _ (hpt _) _ (hcl j x hx), hc1 j⟩, ?_⟩
      intro x hx s
      exact hc2 x (by omega) s
  exact main
end

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.perLim :
    UpperTheory.V.Cj.H.PerLim := by
  intro E _ _ _ a U Ξ q ω hω h0 hl
  have hc := (coneConvex E a).1
  have hn : (cone E a).Nonempty := ⟨_, hOne_mem_cone⟩
  have ho : IsOpen (cone E a) := isOpen_iff_mem_nhds.2 fun p hp => by
    obtain ⟨τ, -, hτ⟩ := locSec E a p hp
    exact hτ.mono fun x hx => ⟨τ x, hx⟩
  have key : ∀ k, ∃ w : (geo ho U Ξ).Om q, Corr U Ξ (ω k) w.1 ∧ (∀ γ, (geo ho U Ξ).act q γ w = w) ∧
      (geo ho U Ξ).dOm q w = 0 := fun k => by
    have hv : ∀ X, LeftInv (ω k X) ∧ RightInv U (ω k X) := fun X => (levelVal E a U Ξ _).1 ((hω k).val X)
    obtain ⟨w, hw, hw0⟩ := corrFwd E a U Ξ q (ω k) (hω k).equiv fun X => (hv X).2
    let w' : (geo ho U Ξ).Om q := ⟨w, fun s => ⟨corrSmooth E a U Ξ q _ w hw s, hw0 s⟩⟩
    have hw' : Corr U Ξ (ω k) w'.1 := hw
    have h := corrD E a ho U Ξ q _ _ hw'
    rw [h0 k] at h
    exact ⟨w', hw', fun γ => (corrInv E a ho U Ξ q _ _ hw').1 (fun X => (hv X).1) γ,
      (corrUniq E a ho U Ξ (q + 1)).2 0 _ 0 h (corr_zero U Ξ)⟩
  choose w hw hi hd0 using key
  obtain ⟨c, hz, hlim⟩ := zigLim _ _ _ _ (geo ho U Ξ) hc hn q 0 (fun k _ => w k)
    (fun k => ⟨fun γ _ _ => (hi k γ).symm, fun x hx => by simp [hd, hx, Finset.sum_range_succ]⟩)
    (fun k _ _ => hd0 k) (fun _ _ => corrLim E a ho U Ξ q ω w hw hl)
  exact ⟨c, fun k => ⟨ho, w k, hw k, hz k⟩, fun x hx => hlim x (by omega)⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.HCobLim
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.AbsSolve
noncomputable section

open Filter Topology

namespace UpperTheory.V.Cj.H

set_option maxHeartbeats 400000 in
theorem absSolve : AbsSolve := by
  intro I J L c cn hcn hlim
  classical
  let ψ : (J →₀ ℂ) →ₗ[ℂ] (I →₀ ℂ) := Finsupp.linearCombination ℂ L
  let φ : (J →₀ ℂ) →ₗ[ℂ] ℂ := Finsupp.linearCombination ℂ c
  have hsum : ∀ (b : I → ℂ) (v : I →₀ ℂ),
      (v.sum fun i x => x * b i) = Finsupp.linearCombination ℂ b v := by
    intro b v
    rw [Finsupp.linearCombination_apply]
    rfl
  have hcomp : ∀ (b : I → ℂ), (Finsupp.linearCombination ℂ b) ∘ₗ ψ
      = Finsupp.linearCombination ℂ (fun j => Finsupp.linearCombination ℂ b (L j)) := by
    intro b
    apply Finsupp.lhom_ext
    intro j x
    simp [ψ, Finsupp.linearCombination_single]
  have hker : LinearMap.ker ψ ≤ LinearMap.ker φ := by
    intro a ha
    rw [LinearMap.mem_ker] at ha ⊢
    have h0 : ∀ k, Finsupp.linearCombination ℂ (cn k) a = 0 := by
      intro k
      obtain ⟨b, hb⟩ := hcn k
      have h1 := congrArg (fun m => m a) (hcomp b)
      simp only [LinearMap.comp_apply, ha, map_zero] at h1
      rw [show cn k = fun j => Finsupp.linearCombination ℂ b (L j) from
        funext fun j => ((hsum b (L j)).symm.trans (hb j)).symm]
      exact h1.symm
    have hT : Tendsto (fun k => Finsupp.linearCombination ℂ (cn k) a) atTop (𝓝 (φ a)) := by
      simp only [φ, Finsupp.linearCombination_apply, Finsupp.sum]
      apply tendsto_finsetSum
      intro j _
      exact (hlim j).const_smul (a j)
    simp only [h0] at hT
    exact tendsto_nhds_unique hT tendsto_const_nhds
  let f0 : LinearMap.range ψ →ₗ[ℂ] ℂ :=
    ((LinearMap.ker ψ).liftQ φ hker) ∘ₗ
      (ψ.quotKerEquivRange.symm : LinearMap.range ψ →ₗ[ℂ] (J →₀ ℂ) ⧸ LinearMap.ker ψ)
  obtain ⟨g, hg⟩ := LinearMap.exists_extend f0
  have hgψ : ∀ a, g (ψ a) = φ a := by
    intro a
    have h2 := congrArg (fun m => m ⟨ψ a, LinearMap.mem_range_self ψ a⟩) hg
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h2
    rw [h2]
    simp [f0, LinearMap.quotKerEquivRange_symm_apply_image]
  have hgb : Finsupp.linearCombination ℂ (fun i => g (Finsupp.single i 1)) = g := by
    apply Finsupp.lhom_ext
    intro i x
    rw [Finsupp.linearCombination_single, ← map_smul, Finsupp.smul_single_one]
  refine ⟨fun i => g (Finsupp.single i 1), fun j => ?_⟩
  refine (hsum (fun i => g (Finsupp.single i 1)) (L j)).trans ?_
  rw [hgb]
  have h3 := hgψ (Finsupp.single j 1)
  simpa [ψ, φ, Finsupp.linearCombination_single] using h3

end UpperTheory.V.Cj.H
end
end

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private def Fty {I : Type} (f : (I → ℂ) → ℂ) : Prop :=
  ∃ L : I →₀ ℂ, ∀ b : I → ℂ, Finsupp.linearCombination ℂ b L = f b

private theorem fty_ev {I : Type} (a : ℂ) (i : I) : Fty fun b : I → ℂ => a * b i :=
  ⟨Finsupp.single i a, fun b => by rw [Finsupp.linearCombination_single, smul_eq_mul]⟩

private theorem fty_sub {I : Type} {f g : (I → ℂ) → ℂ} (hf : Fty f) (hg : Fty g) : Fty fun b => f b - g b := by
  obtain ⟨L, hL⟩ := hf
  obtain ⟨M, hM⟩ := hg
  exact ⟨L - M, fun b => by rw [map_sub, hL, hM]⟩

private theorem fty_sum {I K : Type} (t : Finset K) (f : K → (I → ℂ) → ℂ) (hf : ∀ k, Fty (f k)) :
    Fty fun b => ∑ k ∈ t, f k b := by
  choose L hL using hf
  exact ⟨∑ k ∈ t, L k, fun b => by rw [map_sum]; exact Finset.sum_congr rfl fun k _ => hL k b⟩

private theorem fty_solve {I J : Type} (f : J → (I → ℂ) → ℂ) (hf : ∀ j, Fty (f j)) (c : J → ℂ) (cn : ℕ → J → ℂ)
    (h : ∀ k, ∃ b, ∀ j, f j b = cn k j) (hl : ∀ j, Tendsto (fun k => cn k j) atTop (𝓝 (c j))) :
    ∃ b, ∀ j, f j b = c j := by
  choose L hL using hf
  have hs : ∀ (b : I → ℂ) j, (L j).sum (fun i x => x * b i) = f j b := by
    intro b j
    rw [← hL, Finsupp.linearCombination_apply]
    rfl
  obtain ⟨b, hb⟩ := absSolve I J L c cn (fun k => by
    obtain ⟨b, hb⟩ := h k
    exact ⟨b, fun j => by rw [hs, hb]⟩) hl
  exact ⟨b, fun j => by rw [← hs, hb]⟩

theorem UpperTheory.V.Cj.H.hCobLim :
    UpperTheory.V.Cj.H.HCobLim := by
  intro Γ S _ d ρ hρ q c cn h hl
  have hlim : ∀ x : List Γ, x.length = q + 1 → ∀ s i,
      Tendsto (fun k => (c - cn k) x s i) atTop (𝓝 (c x s i)) := by
    intro x hx s i
    have h1 : Tendsto (fun k => cn k x s i) atTop (𝓝 0) := tendsto_pi_nhds.1 (hl x hx s) i
    simpa using (tendsto_const_nhds (x := c x s i)).sub h1
  cases q with
  | zero =>
    intro x hx
    funext s i
    have h1 := hlim x hx s i
    have h2 : (fun k => (c - cn k) x s i) = fun _ => (0 : ℂ) := by
      funext k
      rw [h k x hx]
      rfl
    rw [h2] at h1
    exact tendsto_nhds_unique h1 tendsto_const_nhds
  | succ q =>
    let cur : (List Γ × S × Fin d → ℂ) → List Γ → S → Fin d → ℂ := fun b x s i => b (x, s, i)
    let f : (Γ × {x : List Γ // x.length = q + 1} × S × Fin d) ⊕ ({x : List Γ // x.length = q + 2} × S × Fin d) →
        (List Γ × S × Fin d → ℂ) → ℂ :=
      Sum.elim (fun p b => cur b (p.2.1.1.map (p.1 * ·)) p.2.2.1 p.2.2.2 - ρ p.1 (cur b p.2.1.1) p.2.2.1 p.2.2.2)
        (fun p b => hd (cur b) p.1.1 p.2.1 p.2.2)
    have hf : ∀ j, Fty (f j) := by
      rintro (⟨γ, x, s, i⟩ | ⟨x, s, i⟩)
      · obtain ⟨s', B, hB⟩ := hρ γ s
        have e : f (Sum.inl (γ, x, s, i)) =
            fun b => 1 * b (x.1.map (γ * ·), s, i) - ∑ j, B i j * b (x.1, s', j) := by
          funext b
          simp only [f, Sum.elim_inl, hB, one_mul]
          rfl
        rw [e]
        exact fty_sub (fty_ev _ _) (fty_sum _ _ fun j => fty_ev _ _)
      · have e : f (Sum.inr (x, s, i)) =
            fun b => ∑ j ∈ Finset.range x.1.length, ((-1 : ℂ) ^ j) * b (x.1.eraseIdx j, s, i) := by
          funext b
          simp [f, cur, hd, Finset.sum_apply]
        rw [e]
        exact fty_sum _ _ fun j => fty_ev _ _
    obtain ⟨b, hb⟩ := fty_solve f hf (Sum.elim (fun _ => 0) fun p => c p.1.1 p.2.1 p.2.2)
      (fun k => Sum.elim (fun _ => 0) fun p => (c - cn k) p.1.1 p.2.1 p.2.2) (fun k => by
        obtain ⟨b, h1, h2⟩ := h k
        refine ⟨fun p => b p.1 p.2.1 p.2.2, ?_⟩
        rintro (⟨γ, x, s, i⟩ | ⟨x, s, i⟩)
        · change b (x.1.map (γ * ·)) s i - ρ γ (b x.1) s i = 0
          rw [h1 γ x.1 x.2, sub_self]
        · change hd b x.1 s i = (c - cn k) x.1 s i
          rw [h2 x.1 x.2]) (by
        rintro (p | ⟨x, s, i⟩)
        · exact tendsto_const_nhds
        · exact hlim x.1 x.2 s i)
    refine ⟨cur b, fun γ x hx => ?_, fun x hx => ?_⟩
    · funext s i
      exact sub_eq_zero.1 (hb (Sum.inl (γ, ⟨x, hx⟩, s, i)))
    · funext s i
      exact (hb (Sum.inr (⟨x, hx⟩, s, i))).symm
end

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.exactLim :
    UpperTheory.V.Cj.H.ExactLim := by
  intro E _ _ _ a ha U hU Ξ q β ω hβ dβ hω dω hl hex
  obtain ⟨c, hc⟩ := (perEx E a U Ξ q).1 β hβ dβ
  obtain ⟨cn, hcn, ht⟩ := perLim E a U Ξ q ω hω dω hl
  refine (perKer E a ha U hU Ξ q β c hβ hc).1
    (hCobLim _ _ _ _ (fun γ s => ⟨_, _, fun f => rfl⟩) q c cn (fun k => ?_) ht)
  have h1 := (perEx E a U Ξ q).2.2 β (ω k) c (cn k) 1 (-1) hc (hcn k)
  have h2 := (levLin E a U Ξ q).1 β (ω k) 1 (-1) hβ (hω k)
  have e1 : (1 : ℂ) • β + (-1 : ℂ) • ω k = β - ω k := by
    ext X
    simp [sub_eq_add_neg]
  have e2 : (1 : ℂ) • c + (-1 : ℂ) • cn k = c - cn k := by
    rw [one_smul, neg_smul, one_smul, sub_eq_add_neg]
  rw [e1] at h1 h2
  rw [e2] at h1
  exact (perKer E a ha U hU Ξ q _ _ h2 h1).2 (hex k)
