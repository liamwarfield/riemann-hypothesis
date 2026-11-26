module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsTwOps

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PfCsBdd
open UpperTheory.V.Lit.Geo

section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum

private theorem exists_split' {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (g : GA E a) :
    ∃ t : ℝ, splitCentre E a t * g = (retractOne g : UpperTheory.V.KernelIndexFullLattice.G1 E a).1 := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact ⟨0, Units.ext (Subsingleton.elim _ _)⟩
  have h1 : (0 : ℝ) < a := Nat.cast_pos.2 ha
  have h2 : (0 : ℝ) < Module.finrank ℚ E := Nat.cast_pos.2 Module.finrank_pos
  refine ⟨Real.log ((Reduction.detModule E a g)⁻¹).1 / (a * Module.finrank ℚ E), ?_⟩
  rw [UpperTheory.V.KernelIndexFullLattice.splitEq_holds E a, coe_retractOne, ← centralSection_inv_mul_comm,
    ← map_inv (Reduction.centralSection E a)]
  refine congrArg (fun s => Reduction.centralSection E a s * g) (Subtype.ext ?_)
  change Real.exp _ = _
  rw [mul_div_cancel₀ _ (mul_pos h1 h2).ne', Real.exp_log ((Reduction.detModule E a g)⁻¹).2]

theorem UpperTheory.V.Lit.Geo.Pf.csBdd :
    UpperTheory.V.Lit.Geo.Pf.CsBdd := by
  intro E _ _ _ a F hF h
  rcases h with ⟨R, hR⟩ | ⟨C, hC⟩
  · obtain ⟨K, hK, hK'⟩ := (qhtFacts E a).2.2.2 R
    obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hF.cont.continuousOn
    refine ⟨max M 0, fun g => ?_⟩
    rcases lt_or_ge R (qht g) with hg | hg
    · rw [hR g hg, norm_zero]; exact le_max_right _ _
    · obtain ⟨γ, t, hm⟩ := hK' g hg
      have := hM _ hm
      rw [mul_assoc, hF.left, hF.centre] at this
      exact this.trans (le_max_left _ _)
  · refine ⟨C, fun g => ?_⟩
    obtain ⟨t, ht⟩ := exists_split' g
    rw [← hF.centre t g, ht]
    exact hC _

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PfBddInt
open UpperTheory.V.Lit.Geo

theorem UpperTheory.V.Lit.Geo.Pf.bddInt :
    UpperTheory.V.Lit.Geo.Pf.BddInt := by
  intro E _ _ _ a μ _ F hF ⟨C, hC⟩
  haveI := GlobalTheory.CovolGL.isFiniteMeasure_quotMeasure E a μ
  have h := GlobalTheory.CuspQuot.memL2_of_bound (μ := μ) hF.cont
    (GlobalTheory.CuspRep.CuspidalL2GL.leftInv_latticeGL hF.left hF.centre) hC
  exact ⟨h.2.integrable one_le_two, h⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PfAdjInt
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PfStokesFn
open UpperTheory.V.Lit.Geo
open NumberField Matrix MeasureTheory GlobalTheory.CuspRep UpperTheory.V.Af GlobalTheory.UnitaryBC
open scoped GlobalTheory.CuspRep.CuspidalL2GL

private theorem one_mem {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} :
    (fun _ => (1 : ℂ)) ∈ Sm E a := fun g =>
  (contDiffOn_const (c := (1 : ℂ))).congr fun x hx => by
    have hx' : IsUnit (Matrix.of x) := hx
    simp [chart, hx']

private theorem lie_one {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (X : Lie E a) :
    lie E a X ⟨fun _ => (1 : ℂ), one_mem⟩ = 0 := by
  obtain ⟨c, c0, -, -, cder, -⟩ := UpperTheory.V.Lit.Bor.oneParam E a X
  refine Subtype.ext (funext fun g => ?_)
  exact (hasDerivAt_curve (⟨fun _ => (1 : ℂ), one_mem⟩ : Sm E a) g c X c0 cder).unique (hasDerivAt_const (0 : ℝ) (1 : ℂ))

theorem UpperTheory.V.Lit.Geo.Pf.stokesFn :
    UpperTheory.V.Lit.Geo.Pf.StokesFn := by
  intro E _ _ _ a μ _ θ X hθ hc
  let u : Sm E a := ⟨fun _ => (1 : ℂ), one_mem⟩
  have hu : IsOpen {k | act (.fin k) u = u} := by
    have e : {k | act (.fin k) u = u} = Set.univ := Set.eq_univ_of_forall fun k => rfl
    rw [e]
    exact isOpen_univ
  obtain ⟨h1, h2⟩ := Pf.invLie E a θ hθ
  have h3 := (Pf.invLie E a _ (h2 X)).1
  have m1 := (Pf.bddInt E a μ _ h1 (Pf.csBdd E a _ h1 (.inl hc))).2
  have m2 := (Pf.bddInt E a μ _ h3 (Pf.csBdd E a _ h3 (.inl (Pf.csLie E a θ X hc)))).2
  have m3 := (Pf.bddInt E a μ u.1 ⟨continuous_const, fun _ _ => rfl, fun _ _ => rfl⟩ ⟨1, fun _ => norm_one.le⟩).2
  have e0 : (lie E a X u).1 = fun _ => 0 := congrArg Subtype.val (lie_one X)
  have m4 : GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (latticeGL E a) μ (lie E a X u).1 := by
    rw [e0]
    exact (Pf.bddInt E a μ _ ⟨continuous_const, fun _ _ => rfl, fun _ _ => rfl⟩ ⟨0, fun _ => norm_zero.le⟩).2
  have h := UpperTheory.V.Lit.Bor.skew_lie_action_L2 E a μ X u θ hu hθ.level m3 m1 m4 m2
  rw [GlobalTheory.AutomorphicL2Unitary.MemL2Quotient.inner_toL2_eq_theta_pairing, GlobalTheory.AutomorphicL2Unitary.MemL2Quotient.inner_toL2_eq_theta_pairing, e0] at h
  simpa [GlobalTheory.AutomorphicL2Unitary.pet, GlobalTheory.AutomorphicL2Unitary.descend, Pf.qint, u] using h
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PfTwLie
open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC
open UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem open_stab {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (v : V) {S : Set G} (hS : IsOpen S) (h1 : (1 : G) ∈ S) (h : ∀ g ∈ S, ρ g v = v) :
    IsOpen {g | ρ g v = v} := by
  rw [isOpen_iff_forall_mem_open]
  intro g hg
  refine ⟨(fun x => g⁻¹ * x) ⁻¹' S, fun x hx => ?_, hS.preimage (by fun_prop), by simpa using h1⟩
  have e : x = g * (g⁻¹ * x) := by group
  have hg' : ρ g v = v := hg
  show ρ x v = v
  rw [e, map_mul, Module.End.mul_apply, h _ hx, hg']

private theorem cmp_lT {W : Type} [AddCommGroup W] [Module ℂ W] {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℂ)
    (y : W ⊗[ℂ] (Fin d → ℂ)) (j : Fin d) :
    cmp j ((Matrix.toLin' Q).lTensor W y) = ∑ k, Q j k • cmp k y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy, smul_add, Finset.sum_add_distrib]
  | tmul φ v =>
    simp only [LinearMap.lTensor_tmul, cmp_tmul, smul_smul, ← Finset.sum_smul]
    rfl

private theorem cmp_rT {W : Type} [AddCommGroup W] [Module ℂ W] {d : ℕ} (S : Module.End ℂ W)
    (y : W ⊗[ℂ] (Fin d → ℂ)) (j : Fin d) :
    cmp j (S.rTensor (Fin d → ℂ) y) = S (cmp j y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul φ v => simp only [LinearMap.rTensor_tmul, cmp_tmul, map_smul]

private def invSub (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) : Submodule ℂ (Sm E a) where
  carrier := {φ | Pf.SInv φ}
  zero_mem' := ⟨fun _ _ => rfl, fun _ _ => rfl, by
    change IsOpen {k | finRep E a k (0 : Sm E a) = 0}
    simpa only [map_zero, Set.ofPred_true] using
      (isOpen_univ : IsOpen (Set.univ : Set (GL (Fin a) (Af E))))⟩
  add_mem' := by
    intro φ ψ h h'
    refine ⟨fun γ g => congrArg₂ (· + ·) (h.left γ g) (h'.left γ g),
      fun t g => congrArg₂ (· + ·) (h.centre t g) (h'.centre t g), ?_⟩
    have h1 : IsOpen {k | finRep E a k φ = φ} := h.level
    have h2 : IsOpen {k | finRep E a k ψ = ψ} := h'.level
    refine open_stab (finRep E a) _ (h1.inter h2) ⟨by simp, by simp⟩ ?_
    rintro k ⟨e1, e2⟩
    exact (map_add _ _ _).trans (congrArg₂ (· + ·) e1 e2)
  smul_mem' := by
    intro c φ h
    refine ⟨fun γ g => congrArg (c • ·) (h.left γ g), fun t g => congrArg (c • ·) (h.centre t g), ?_⟩
    have h1 : IsOpen {k | finRep E a k φ = φ} := h.level
    refine open_stab (finRep E a) _ h1 (by simp) ?_
    intro k e1
    exact (map_smul _ _ _).trans (congrArg (c • ·) e1)

theorem UpperTheory.V.Lit.Geo.Pf.twLie :
    UpperTheory.V.Lit.Geo.Pf.TwLie := by
  intro E _ _ _ a Ξ r χ hχ X x hx
  let N : Submodule ℂ (Sm E a) := (invSub E a).comap (mulChi a χ).toLinearMap
  have hiff : ∀ y : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ), Pf.TwInv χ y ↔ y ∈ tens Ξ.d N := fun y => by
    rw [mem_tens]; rfl
  rw [hiff] at hx
  rw [hiff, hiff]
  have hA : smA Ξ X x ∈ tens Ξ.d N := mem_tens.2 fun j => by
    rw [smA_apply, cmp_rT]
    have h0 : cmp j x ∈ N := mem_tens.1 hx j
    have h1 : lie E a X (cmp j x) + ((r * ell E a X : ℝ) : ℂ) • cmp j x ∈ N := by
      change Pf.SInv (mulChi a χ _)
      rw [← hχ.2]
      exact (Pf.invLie E a _ h0).2 X
    exact (N.add_mem_iff_left (N.smul_mem _ h0)).1 h1
  have hB : smB Ξ X x ∈ tens Ξ.d N := mem_tens.2 fun j => by
    rw [smB_apply, cmp_lT]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (mem_tens.1 hx k)
  constructor
  · have : smLie Ξ X x = smA Ξ X x + smB Ξ X x := by
      simp only [smB, LinearMap.sub_apply, add_sub_cancel]
    rw [this]
    exact Submodule.add_mem _ hA hB
  · rw [smAdj, adj_apply]
    refine Submodule.sub_mem _ (Submodule.sub_mem _ hB hA) ?_
    exact Submodule.smul_of_tower_mem _ _ hx
end

open UpperTheory.V.Lit.Geo

theorem UpperTheory.V.Lit.Geo.Pf.adjInt :
    UpperTheory.V.Lit.Geo.Pf.AdjInt := by
  intro E _ _ _ a μ _ Ξ r χ G htw hadm X x y hx hy hs
  have hint : ∀ u v, Pf.TwInv χ u → Pf.TwInv χ v → Pf.Cs (Pf.pt χ G u v) → Pf.QInt μ (Pf.pt χ G u v) :=
    fun u v hu hv hc =>
      have hC := (Pf.ptInv E a χ _ G u v).2.1 hu hv
      (Pf.bddInt E a μ _ hC (Pf.csBdd E a _ hC (.inl hc))).1
  refine (fun (h : _ ∧ _) (h3 : _ ∧ _ → _) => ⟨h.1, h.2, h3 h⟩) ⟨?_, ?_⟩ ?_
  · exact hint _ _ hx (Pf.twLie E a Ξ r χ htw _ y hy).1
      (hs.elim (fun h => Pf.cs_pt_left χ G _ h)
        fun h => Pf.cs_pt_right χ G _ (Pf.csTens E a Ξ r _ y h).1)
  · exact hint _ _ (Pf.twLie E a Ξ r χ htw _ x hx).2 hy
      (hs.elim (fun h => Pf.cs_pt_left χ G _ (Pf.csTens E a Ξ r _ x h).2)
        fun h => Pf.cs_pt_right χ G _ h)
  rintro ⟨h1, h2⟩
  obtain ⟨θ, hθ, hd⟩ := Pf.ptDiv E a Ξ r χ G htw hadm x y
  have hS := (Pf.ptInv E a χ _ G x y).2.2 θ hθ hx hy
  have hc : Pf.Cs θ.1 := by
    rw [show θ.1 = _ from funext hθ]
    exact hs.elim (fun h => Pf.cs_pt_left χ G _ h) fun h => Pf.cs_pt_right χ G _ h
  have h0 := fun Y => Pf.stokesFn E a μ θ Y hS hc
  refine sub_eq_zero.1 ?_
  unfold Pf.qint at h0 ⊢
  rw [← MeasureTheory.integral_sub h1 h2]
  simp only [← hd X]
  exact h0 _
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PfRapidBdd
open UpperTheory.V.Lit.Geo
open Matrix

private theorem norm_form_le {d : ℕ} (G : Matrix (Fin d) (Fin d) ℂ) (x y : Fin d → ℂ) :
    ‖star x ⬝ᵥ G *ᵥ y‖ ≤ (∑ i, ∑ j, ‖G i j‖) * (‖x‖ * ‖y‖) := by
  simp only [dotProduct, mulVec, Finset.sum_mul, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul, norm_mul, Pi.star_apply, norm_star, mul_left_comm]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul (norm_le_pi_norm x i) (norm_le_pi_norm y j) (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)

private theorem mul_le_of_bounds {u v t A B : ℝ} (hu : 0 ≤ u) (ht : 0 ≤ t) (h1 : u * t ≤ A) (h2 : v ≤ B * t) :
    u * v ≤ |B| * A :=
  calc u * v ≤ u * (|B| * t) :=
        mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_right (le_abs_self B) ht)) hu
    _ = |B| * (u * t) := by ring
    _ ≤ |B| * A := mul_le_mul_of_nonneg_left h1 (abs_nonneg B)

theorem UpperTheory.V.Lit.Geo.Pf.rapidBdd :
    UpperTheory.V.Lit.Geo.Pf.RapidBdd := by
  intro E _ _ _ a Ξ χ s hs G n e q α β hα hβ
  obtain ⟨N, hN⟩ := hβ
  choose B hB using hN
  choose A hA using fun X => hα X N
  refine ⟨∑ I : Fin q → Fin n, (∑ i, ∑ j, ‖G i j‖) * (|B fun i => e (I i)| * A fun i => e (I i)), fun g => ?_⟩
  have h1 := Pf.chiOne E a χ s hs g
  have hq : 0 ≤ qht (E := E) (a := a) g.1 ^ N := pow_nonneg (zero_le_one.trans ((qhtFacts E a).1 _)) N
  unfold ptIp
  rw [h1, one_pow, Complex.ofReal_one, one_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun I _ => (norm_form_le G _ _).trans ?_)
  exact mul_le_mul_of_nonneg_left (mul_le_of_bounds (norm_nonneg _) hq (hA _ g) (hB _ g))
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PtZsmulRight
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Geo
open scoped TensorProduct

namespace UpperTheory.V.Lit.Geo.Pf

section
variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (χ : Formalism.L2.Host.HChar E) {d : ℕ}
  (G : Matrix (Fin d) (Fin d) ℂ) (g : GA E a)

private theorem ev_eq (x : Sm E a ⊗[ℂ] (Fin d → ℂ)) : ev x g = fun j => (cmp j x).1 g :=
  funext fun j => (cmp_ev x j g).symm

private theorem ev_add' (x y : Sm E a ⊗[ℂ] (Fin d → ℂ)) : ev (x + y) g = ev x g + ev y g := by
  funext j
  simp [ev_eq]

private noncomputable def ptL (y : Sm E a ⊗[ℂ] (Fin d → ℂ)) : Sm E a ⊗[ℂ] (Fin d → ℂ) →+ ℂ :=
  AddMonoidHom.mk' (fun x => pt χ G x y g) fun x x' => by
    simp only [pt, ev_add', star_add, add_dotProduct, mul_add]

private noncomputable def ptR (x : Sm E a ⊗[ℂ] (Fin d → ℂ)) : Sm E a ⊗[ℂ] (Fin d → ℂ) →+ ℂ :=
  AddMonoidHom.mk' (fun y => pt χ G x y g) fun y y' => by
    simp only [pt, ev_add', mulVec_add, dotProduct_add, mul_add]

private theorem pt_sum_left {ι : Type} (s : Finset ι) (x : ι → Sm E a ⊗[ℂ] (Fin d → ℂ)) (y : Sm E a ⊗[ℂ] (Fin d → ℂ)) :
    pt χ G (∑ i ∈ s, x i) y g = ∑ i ∈ s, pt χ G (x i) y g := map_sum (ptL χ G g y) x s

private theorem pt_sum_right {ι : Type} (s : Finset ι) (x : Sm E a ⊗[ℂ] (Fin d → ℂ)) (y : ι → Sm E a ⊗[ℂ] (Fin d → ℂ)) :
    pt χ G x (∑ i ∈ s, y i) g = ∑ i ∈ s, pt χ G x (y i) g := map_sum (ptR χ G g x) y s

private theorem pt_zsmul_left (k : ℤ) (x y : Sm E a ⊗[ℂ] (Fin d → ℂ)) :
    pt χ G (k • x) y g = k • pt χ G x y g := map_zsmul (ptL χ G g y) k x

private theorem pt_zsmul_right (k : ℤ) (x y : Sm E a ⊗[ℂ] (Fin d → ℂ)) :
    pt χ G x (k • y) g = k • pt χ G x y g := map_zsmul (ptR χ G g x) k y

end

end UpperTheory.V.Lit.Geo.Pf

open UpperTheory.V.Lit.Geo.Pf in
theorem UpperTheory.V.Lit.Geo.Pf.ptD :
    UpperTheory.V.Lit.Geo.Pf.PtD := by
  intro E _ _ _ a Ξ χ G n e q L β η g
  refine ⟨?_, ?_⟩
  · have key : ∀ i : Fin (q + 1), ∑ I : Fin (q + 1) → Fin n,
        pt χ G (β fun k => e (I k)) ((-1 : ℤ) ^ (i : ℕ) • L (toL (e (I i)).1) (η (i.removeNth fun k => e (I k)))) g =
        ∑ J : Fin q → Fin n, ∑ j,
          pt χ G (β (Matrix.vecCons (e j) fun i => e (J i))) (L (toL (e j).1) (η fun i => e (J i))) g := fun i => by
      rw [← (Fin.insertNthEquiv (fun _ => Fin n) i).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
      refine Finset.sum_congr rfl fun J _ => Finset.sum_congr rfl fun j _ => ?_
      have h1 : (fun k => e ((Fin.insertNthEquiv (fun _ => Fin n) i (j, J)) k)) =
          i.insertNth (α := fun _ => Herm E a) (e j) (fun k => e (J k)) := by
        funext k
        refine Fin.succAboveCases i ?_ (fun k => ?_) k <;> simp [Fin.insertNthEquiv]
      have h2 : (Fin.insertNthEquiv (fun _ => Fin n) i (j, J)) i = j := by simp [Fin.insertNthEquiv]
      rw [h1, h2, Fin.removeNth_insertNth, AlternatingMap.map_insertNth, pt_zsmul_left, pt_zsmul_right,
        smul_smul, ← mul_pow]
      simp
    have h0 : ptIp χ G e β (dCo L η) g = ∑ i : Fin (q + 1), ∑ I : Fin (q + 1) → Fin n,
        pt χ G (β fun k => e (I k)) ((-1 : ℤ) ^ (i : ℕ) • L (toL (e (I i)).1) (η (i.removeNth fun k => e (I k)))) g := by
      rw [Finset.sum_comm, ptIp_eq]
      refine Finset.sum_congr rfl fun I _ => ?_
      rw [dCo_apply, pt_sum_right]
    rw [h0, Finset.sum_congr rfl fun i _ => key i]
    simp
  · rw [ptIp_eq]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [del_apply, pt_sum_left]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PfZeroInt
open UpperTheory.V.Lit.Geo
open NumberField MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC
open UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open scoped GlobalTheory.CuspRep.CuspidalL2GL

theorem UpperTheory.V.Lit.Geo.Pf.zeroInt :
    UpperTheory.V.Lit.Geo.Pf.ZeroInt := by
  intro E _ _ _ a μ _ F hF hpos hI h0
  have hL : GlobalTheory.AutomorphicL2Unitary.LeftInv (latticeGL E a) F := CuspidalL2GL.leftInv_latticeGL hF.left hF.centre
  have hn : ∀ g, F g = ((‖F g‖ : ℝ) : ℂ) := fun g => by
    obtain ⟨t, ht, e⟩ := hpos g
    rw [e, Complex.norm_real, Real.norm_of_nonneg ht]
  have h1 : ∫ x : GlobalTheory.AutomorphicL2Unitary.Quot (latticeGL E a), ‖F x.out‖ ∂(GlobalTheory.AutomorphicL2Unitary.quotMeasure (latticeGL E a) μ) = 0 := by
    have h2 : Pf.qint μ F =
        ((∫ x : GlobalTheory.AutomorphicL2Unitary.Quot (latticeGL E a), ‖F x.out‖ ∂(GlobalTheory.AutomorphicL2Unitary.quotMeasure (latticeGL E a) μ) : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => hn _)
    rw [h0] at h2
    exact_mod_cast h2.symm
  have h3 := (integral_eq_zero_iff_of_nonneg (fun x => norm_nonneg _) (Integrable.norm hI)).1 h1
  have h4 : F =ᵐ[μ] fun _ => 0 := by
    filter_upwards [GlobalTheory.AutomorphicL2Unitary.ae_quotMeasure_iff.1 h3] with g hg
    have e : F (GlobalTheory.AutomorphicL2Unitary.mk (latticeGL E a) g).out = F g := hL.descend_mk g
    simpa [e] using hg
  exact fun g => congrFun ((Continuous.ae_eq_iff_eq μ hF.cont continuous_const).1 h4) g
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PfPtPos
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open UpperTheory.V.Lit.Geo
open scoped TensorProduct ComplexOrder

theorem UpperTheory.V.Lit.Geo.Pf.ptPos :
    UpperTheory.V.Lit.Geo.Pf.PtPos := by
  intro E _ _ _ a Ξ χ G hG n e he q α
  have hnn : ∀ v : Fin Ξ.d → ℂ, 0 ≤ star v ⬝ᵥ G *ᵥ v := fun v => hG.pos.posSemidef.dotProduct_mulVec_nonneg v
  refine ⟨fun g => ?_, fun h0 => ?_⟩
  · have h : 0 ≤ ptIp χ G e α α g :=
      mul_nonneg (Complex.zero_le_real.2 (by positivity)) (Finset.sum_nonneg fun I _ => hnn _)
    obtain ⟨h1, h2⟩ := Complex.nonneg_iff.1 h
    exact ⟨_, h1, Complex.ext rfl h2.symm⟩
  · have h2 : ∀ I : Fin q → Fin n, (α fun i => e (I i)) = 0 := fun I => by
      have hev : ∀ g, ev (α fun i => e (I i)) g = 0 := fun g => by
        have h := h0 g
        rw [ptIp, mul_eq_zero] at h
        rcases h with h | h
        · simp at h
        · have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun I _ => hnn _)).1 h I (Finset.mem_univ _)
          by_contra hne
          exact (hG.pos.dotProduct_mulVec_pos hne).ne' h1
      rw [← sum_cmp (α fun i => e (I i))]
      refine Finset.sum_eq_zero fun j _ => ?_
      have : cmp j (α fun i => e (I i)) = 0 := Subtype.ext (funext fun g => by
        rw [Pf.cmp_ev, hev]; rfl)
      rw [this, TensorProduct.zero_tmul]
    refine AlternatingMap.ext fun X => ?_
    have hX : X = fun i => ∑ j, trF (e j).1 (X i).1 • e j := funext fun i => he (X i)
    have h3 : α X = ∑ I : Fin q → Fin n, α fun i => trF (e (I i)).1 (X i).1 • e (I i) := by
      conv_lhs => rw [hX]
      exact α.toMultilinearMap.map_sum (fun i j => trF (e j).1 (X i).1 • e j)
    rw [h3, AlternatingMap.zero_apply]
    refine Finset.sum_eq_zero fun I _ => ?_
    rw [α.map_smul_univ (fun i => trF (e (I i)).1 (X i).1) (fun i => e (I i)), h2, smul_zero]
end

open UpperTheory.V.Lit.Geo

theorem UpperTheory.V.Lit.Geo.pairFacts :
    PairFacts :=
  Pf.pairFacts_of_steps Pf.bddInt Pf.csBdd Pf.levInv Pf.ptInv Pf.adjInt Pf.ptD Pf.rapidBdd Pf.zeroInt Pf.ptPos
