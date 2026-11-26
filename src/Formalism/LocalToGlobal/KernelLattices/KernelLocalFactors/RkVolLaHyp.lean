module

public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.RkVolSeam
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.RkVolChain
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ExistsIntegralMulOrderElement

@[expose] public section

section -- merged from Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.RkVolLat
noncomputable section
open scoped BigOperators ComplexConjugate
open NumberField Formalism.BasicNotions

namespace Formalism.L2.Ker.Cd.KS.Lat

open Formalism.L2.Ker.KS.Lat hiding La_theta al_eq_La alphaQ_isom delta_ne eNat_laF form_flat herm_hSc img_comap isLat_La isLat_comap isLat_laF isom_flat matH_hSc odd_of_cmOK posDef_hSc relIdx_comap relIdx_laF relIdx_laF_eq sc_pos selfDual_comap selfDual_laF thHalf_laF thMoved_laF thZero_laF th_comap th_laF theta_laF

open Formalism.MainNotions Formalism.L2.Col Formalism.L2.Th1.H
open Formalism.L2.AlgTh (hSc)
open Formalism.L2.Th1.F (cmTheta)

section Gen

variable {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] [FiniteDimensional ℂ W] {H : Sesq V} {H' : Sesq W} (g : V ≃ₗ[ℂ] W)

theorem img_comap (Λ' : AddSubgroup W) :
    imgLat (g : V →ₗ[ℂ] W) (Λ'.comap (g : V →ₗ[ℂ] W).toAddMonoidHom) = Λ' :=
  AddSubgroup.map_comap_eq_self_of_surjective (f := (g : V →ₗ[ℂ] W).toAddMonoidHom) g.surjective Λ'

theorem selfDual_comap (hI : IsIsom H H' (g : V →ₗ[ℂ] W)) {Λ' : AddSubgroup W} (h : IsSelfDual H' Λ') :
    IsSelfDual H (Λ'.comap (g : V →ₗ[ℂ] W).toAddMonoidHom) := by
  unfold IsSelfDual at h ⊢
  ext x
  constructor
  · intro hx
    show g x ∈ Λ'
    rw [← h]
    intro y hy
    obtain ⟨m, hm⟩ := hx (g.symm y) (by show g (g.symm y) ∈ Λ'; rw [g.apply_symm_apply]; exact hy)
    refine ⟨m, ?_⟩
    rw [← hm]
    have h1 := hI x (g.symm y)
    have h2 : (g : V →ₗ[ℂ] W) (g.symm y) = y := g.apply_symm_apply y
    rw [h2] at h1
    unfold altE
    rw [← h1]
    rfl
  · intro hx y hy
    have hx' : g x ∈ dualLat H' Λ' := by rw [h]; exact hx
    obtain ⟨m, hm⟩ := hx' (g y) hy
    refine ⟨m, ?_⟩
    rw [← hm]
    unfold altE
    rw [← hI x y]
    rfl

theorem isLat_comap {Λ' : AddSubgroup W} (h : IsLat Λ') : IsLat (Λ'.comap (g : V →ₗ[ℂ] W).toAddMonoidHom) := by
  constructor
  · have := h.1
    let f : (Λ'.comap (g : V →ₗ[ℂ] W).toAddMonoidHom) → Λ' := fun x => ⟨g x.1, x.2⟩
    have hf : Continuous f :=
      Continuous.subtype_mk (((g : V →ₗ[ℂ] W).continuous_of_finiteDimensional).comp continuous_subtype_val) _
    have hinj : Function.Injective f := by
      intro x y hxy
      exact Subtype.ext (g.injective (congrArg Subtype.val hxy))
    exact DiscreteTopology.of_continuous_injective hf hinj
  · rw [eq_top_iff]
    intro v _
    let p : W →ₗ[ℝ] V := (g.symm : W →ₗ[ℂ] V).restrictScalars ℝ
    have h2 : (Submodule.span ℝ (Λ' : Set W)).map p ≤
        Submodule.span ℝ ((Λ'.comap (g : V →ₗ[ℂ] W).toAddMonoidHom : AddSubgroup V) : Set V) := by
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      apply Submodule.subset_span
      show g (g.symm y) ∈ Λ'
      rw [g.apply_symm_apply]
      exact hy
    refine h2 ⟨g v, by rw [h.2]; trivial, ?_⟩
    show g.symm (g v) = v
    exact g.symm_apply_apply v

theorem th_comap (hI : IsIsom H H' (g : V →ₗ[ℂ] W)) {Λ' : AddSubgroup W} {α' : W → ℂ} {G : W → ℂ} (hG : G ∈ Th H' α' Λ') :
    (fun v => G (g v)) ∈ Th H (fun v => α' (g v)) (Λ'.comap (g : V →ₗ[ℂ] W).toAddMonoidHom) := by
  refine (ThIsom_of heisenbergIsometry V W H H' g hI _ α' G).1 ?_
  rw [img_comap]
  exact hG

theorem relIdx_comap (Λ₁ Λ₂ : AddSubgroup W) :
    relIdx (Λ₁.comap (g : V →ₗ[ℂ] W).toAddMonoidHom) (Λ₂.comap (g : V →ₗ[ℂ] W).toAddMonoidHom) = relIdx Λ₁ Λ₂ := by
  unfold relIdx
  rw [AddSubgroup.relIndex_comap]
  congr 1
  exact AddSubgroup.map_comap_eq_self_of_surjective (f := (g : V →ₗ[ℂ] W).toAddMonoidHom) g.surjective Λ₂

theorem alphaQ_isom (hI : IsIsom H H' (g : V →ₗ[ℂ] W)) (c : ℝ) (v : V) : alphaQ c H' (g v) = alphaQ c H v := by
  unfold alphaQ Formalism.L2.Th1.H.qOf
  have := hI v v
  rw [← this]
  rfl

end Gen

section Form

variable {D : Car} {X : Fields} (s : Seam D X)

theorem form_flat (A : ℝ) (a b : ℕ) (x y : DVar X.Tau a b → ℂ) :
    matH (hSc X.Tau a b A⁻¹) x y = formV A D.what₂.Tau a b (s.flatV a b x) (s.flatV a b y) := by
  rw [formV_apply]
  show (∑ i, ∑ j, x i * hSc X.Tau a b A⁻¹ i j * conj (y j)) = _
  have h1 : ∀ i : DVar X.Tau a b, (∑ j, x i * hSc X.Tau a b A⁻¹ i j * conj (y j)) = x i * conj (y i) / (A : ℂ) := by
    intro i
    rw [Finset.sum_eq_single i]
    · unfold hSc
      rw [Matrix.diagonal_apply_eq]
      push_cast
      field_simp
    · intro j _ hj
      unfold hSc
      rw [Matrix.diagonal_apply_ne _ (Ne.symm hj)]
      simp
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  simp only [h1]
  rw [← Finset.sum_div]
  congr 1
  rw [Fintype.sum_prod_type, ← Equiv.sum_comp s.iT.symm]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Fintype.sum_prod_type]
  rfl

theorem isom_flat (A : ℝ) (a b : ℕ) :
    IsIsom (matH (hSc X.Tau a b A⁻¹)) (formV A D.what₂.Tau a b)
      ((s.flatV a b : (DVar X.Tau a b → ℂ) ≃ₗ[ℂ] Formalism.L2.Ker.Cd.TaylorLogMetric.VC D a b) : (DVar X.Tau a b → ℂ) →ₗ[ℂ] Formalism.L2.Ker.Cd.TaylorLogMetric.VC D a b) :=
  fun x y => (form_flat s A a b x y).symm

theorem matH_hSc (sc : ℝ) (a b : ℕ) (x y : DVar X.Tau a b → ℂ) :
    matH (hSc X.Tau a b sc) x y = (sc : ℂ) * ∑ k, x k * conj (y k) := by
  show (∑ i, ∑ j, x i * hSc X.Tau a b sc i j * conj (y j)) = _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · unfold hSc
    rw [Matrix.diagonal_apply_eq]
    ring
  · intro j _ hj
    unfold hSc
    rw [Matrix.diagonal_apply_ne _ (Ne.symm hj)]
    simp
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem herm_hSc (sc : ℝ) (a b : ℕ) : IsHerm (matH (hSc X.Tau a b sc)) := by
  intro x y
  set_option synthInstance.maxHeartbeats 100000 in
    rw [matH_hSc, matH_hSc, map_mul, Complex.conj_ofReal, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, Complex.conj_conj, mul_comm]

theorem posDef_hSc {sc : ℝ} (hsc : 0 < sc) (a b : ℕ) : IsPosDef (matH (hSc X.Tau a b sc)) := by
  intro x hx
  rw [matH_hSc]
  have h1 : (∑ k, x k * conj (x k)) = ((∑ k, Complex.normSq (x k) : ℝ) : ℂ) := by
    push_cast
    exact Finset.sum_congr rfl fun k _ => Complex.mul_conj (x k)
  rw [h1, ← Complex.ofReal_mul, Complex.ofReal_re]
  apply mul_pos hsc
  obtain ⟨k, hk⟩ : ∃ k, x k ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hx (funext hcon)
  exact Finset.sum_pos' (fun i _ => Complex.normSq_nonneg _) ⟨k, Finset.mem_univ k, Complex.normSq_pos.2 hk⟩

end Form

section Lat

variable {D : Car} {X : Fields} (s : Seam D X) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ)


include B in
theorem sc_pos : 0 < (TaylorLogMetric.area (Formalism.L2.Ker.Cd.TaylorLogMetric.lamOf D cc δ))⁻¹ := by
  rw [show TaylorLogMetric.area (Formalism.L2.Ker.Cd.TaylorLogMetric.lamOf D cc δ) = Formalism.L2.Th1.F.area B.L from B.areaOK]
  exact inv_pos.2 (Formalism.L2.Th1.F.areaPos_thm B.L)

theorem delta_ne (hcc : Formalism.L2.Ker.Cd.TaylorLogMetric.IsCurveIdeal D cc) (hδ : Formalism.L2.Ker.Cd.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) : δ ≠ 0 :=
  Formalism.L2.Ker.Cd.IntegralLatticeDensity.delta_nonzero_link D cc hcc δ hδ

variable {a b : ℕ} {L : Submodule (𝓞 D.host.E) (Fin a → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)}

theorem isLat_La (hcc : Formalism.L2.Ker.Cd.TaylorLogMetric.IsCurveIdeal D cc) (hδ : Formalism.L2.Ker.Cd.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hA : Formalism.L2.Ker.Cd.TaylorLogMetric.admitted D a b L L') :
    IsLat (Formalism.L2.Ker.Cd.TaylorLogMetric.La D B.tor L L') := by
  have hL := B.latAll hcc hδ (delta_ne hcc hδ)
  have h0 : IsLat (Formalism.L2.Ker.Cd.TaylorLogMetric.La D B.tor (Formalism.L2.Ker.Cd.StandardLatticesGL3.stdL D a) (Formalism.L2.Ker.Cd.StandardLatticesGL3.stdL D b)) :=
    Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.J.lat0IsLat (B.stdOK hcc hδ) a b
  have hc := hL.2 a b _ _ _ _ (Formalism.L2.Ker.Cd.Base.first_coordinate_admissible hA) hA
  exact KR.isLat_of_comm h0 hc.2 hc.1

theorem isLat_laF (hcc : Formalism.L2.Ker.Cd.TaylorLogMetric.IsCurveIdeal D cc) (hδ : Formalism.L2.Ker.Cd.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hA : Formalism.L2.Ker.Cd.TaylorLogMetric.admitted D a b L L') :
    IsLat (s.laF B.tor L L') :=
  isLat_comap (s.flatV a b) (isLat_La B hcc hδ hA)

theorem selfDual_laF (hcc : Formalism.L2.Ker.Cd.TaylorLogMetric.IsCurveIdeal D cc) (hδ : Formalism.L2.Ker.Cd.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hA : Formalism.L2.Ker.Cd.TaylorLogMetric.admitted D a b L L') :
    IsSelfDual (matH (hSc X.Tau a b (TaylorLogMetric.area (Formalism.L2.Ker.Cd.TaylorLogMetric.lamOf D cc δ))⁻¹)) (s.laF B.tor L L') :=
  selfDual_comap (s.flatV a b) (isom_flat s _ a b) ((B.latAll hcc hδ (delta_ne hcc hδ)).1 a b L L' hA).1

theorem La_theta {x : Formalism.L2.Ker.Cd.TaylorLogMetric.VC D a b} (hx : x ∈ Formalism.L2.Ker.Cd.TaylorLogMetric.La D B.tor L L') : cmTheta 1 D.host.d • x ∈ Formalism.L2.Ker.Cd.TaylorLogMetric.La D B.tor L L' := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, hw, A, hA, rfl⟩ := hx
    refine AddSubgroup.subset_closure ⟨cmTheta 1 D.host.d * w, Formalism.L2.Ker.Cd.IntegralLatticeDensity.SO.lam_theta hw, A, hA, ?_⟩
    rw [smul_smul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ h1 h2 => rw [smul_add]; exact add_mem h1 h2
  | neg x _ h => rw [smul_neg]; exact neg_mem h

theorem theta_laF {b₀ : ℤ} (hb : Odd b₀) {x : DVar X.Tau a b → ℂ} (hx : x ∈ s.laF B.tor L L') :
    cmTheta b₀ D.host.d • x ∈ s.laF B.tor L L' := by
  obtain ⟨k, rfl⟩ := hb
  have h1 : cmTheta (2 * k + 1) D.host.d = (k : ℂ) + cmTheta 1 D.host.d := by
    unfold cmTheta
    push_cast
    ring
  show s.flatV a b (cmTheta (2 * k + 1) D.host.d • x) ∈ Formalism.L2.Ker.Cd.TaylorLogMetric.La D B.tor L L'
  rw [map_smul, h1, add_smul]
  refine add_mem ?_ (La_theta B hx)
  have h2 : ((k : ℂ) • s.flatV a b x) = k • s.flatV a b x := by
    rw [← Int.cast_smul_eq_zsmul ℂ]
  rw [h2]
  exact AddSubgroup.zsmul_mem _ hx k

theorem odd_of_cmOK {a₀ : ℕ} {b₀ c₀ : ℤ} {d : ℕ} (h : CmOK a₀ b₀ c₀ d) : Odd b₀ := by
  obtain ⟨h1, -, h3, -⟩ := h
  by_contra hcon
  rw [Int.not_odd_iff_even] at hcon
  obtain ⟨k, rfl⟩ := hcon
  have h4 : (d : ℤ) % 8 = 7 := by exact_mod_cast h3
  have h5 : 4 * ((a₀ : ℤ) * c₀) = 4 * (k * k) + d := by rw [← mul_assoc, h1]; ring
  generalize (a₀ : ℤ) * c₀ = u at h5
  generalize k * k = v at h5
  omega

theorem al_eq_La (hcc : Formalism.L2.Ker.Cd.TaylorLogMetric.IsCurveIdeal D cc) (hδ : Formalism.L2.Ker.Cd.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hA : Formalism.L2.Ker.Cd.TaylorLogMetric.admitted D a b L L') :
    ∀ x ∈ Formalism.L2.Ker.Cd.TaylorLogMetric.La D B.tor L L', Formalism.L2.Ker.Cd.TaylorLogMetric.al D B.tor x =
      alphaQ (Real.sqrt D.host.d / 2) (formV (TaylorLogMetric.area (Formalism.L2.Ker.Cd.TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau a b) x := by
  intro x hx
  obtain ⟨m, hm⟩ := Formalism.L2.Ker.Cd.IntegralLatticeDensity.rational_integrality_link D cc hcc δ hδ B a b L L' hA x hx
  exact al_eq D B.tor x m hm

theorem th_laF (hcc : Formalism.L2.Ker.Cd.TaylorLogMetric.IsCurveIdeal D cc) (hδ : Formalism.L2.Ker.Cd.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hA : Formalism.L2.Ker.Cd.TaylorLogMetric.admitted D a b L L') {G : Formalism.L2.Ker.Cd.TaylorLogMetric.VC D a b → ℂ}
    (hG : G ∈ Th (formV (TaylorLogMetric.area (Formalism.L2.Ker.Cd.TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau a b) (Formalism.L2.Ker.Cd.TaylorLogMetric.al D B.tor) (Formalism.L2.Ker.Cd.TaylorLogMetric.La D B.tor L L')) :
    (fun z => G (s.flatV a b z)) ∈ Th (matH (hSc X.Tau a b (TaylorLogMetric.area (Formalism.L2.Ker.Cd.TaylorLogMetric.lamOf D cc δ))⁻¹))
      (alphaQ (Real.sqrt D.host.d / 2) (matH (hSc X.Tau a b (TaylorLogMetric.area (Formalism.L2.Ker.Cd.TaylorLogMetric.lamOf D cc δ))⁻¹))) (s.laF B.tor L L') := by
  have h1 := Th_congr _ _ _ _ (al_eq_La B hcc hδ hA) hG
  have h2 := th_comap (s.flatV a b) (isom_flat s _ a b) h1
  refine Th_congr _ _ _ _ (fun x _ => ?_) h2
  exact alphaQ_isom (s.flatV a b) (isom_flat s _ a b) _ x

theorem thZero_laF (hcc : Formalism.L2.Ker.Cd.TaylorLogMetric.IsCurveIdeal D cc) (hδ : Formalism.L2.Ker.Cd.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (ha : Even a) (hb : Even b) :
    (fun z => B.thZero a b (s.flatV a b z)) ∈ Th (matH (hSc X.Tau a b (TaylorLogMetric.area (Formalism.L2.Ker.Cd.TaylorLogMetric.lamOf D cc δ))⁻¹))
      (alphaQ (Real.sqrt D.host.d / 2) (matH (hSc X.Tau a b (TaylorLogMetric.area (Formalism.L2.Ker.Cd.TaylorLogMetric.lamOf D cc δ))⁻¹)))
      (s.laF B.tor (Formalism.L2.Ker.Cd.StandardLatticesGL3.stdL D a) (Formalism.L2.Ker.Cd.StandardLatticesGL3.stdL D b)) :=
  th_laF s B hcc hδ (Formalism.L2.Ker.Cd.Inhab.Adm_std D a b ha hb) (B.thZeroMem (B.stdOK hcc hδ) a b)

theorem thHalf_laF (hcc : Formalism.L2.Ker.Cd.TaylorLogMetric.IsCurveIdeal D cc) (hδ : Formalism.L2.Ker.Cd.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hA : Formalism.L2.Ker.Cd.TaylorLogMetric.admitted D a b L L') :
    (fun z => B.thHalf a b L (s.flatV a b z)) ∈ Th (matH (hSc X.Tau a b (TaylorLogMetric.area (Formalism.L2.Ker.Cd.TaylorLogMetric.lamOf D cc δ))⁻¹))
      (alphaQ (Real.sqrt D.host.d / 2) (matH (hSc X.Tau a b (TaylorLogMetric.area (Formalism.L2.Ker.Cd.TaylorLogMetric.lamOf D cc δ))⁻¹)))
      (s.laF B.tor L (Formalism.L2.Ker.Cd.StandardLatticesGL3.stdL D b)) :=
  th_laF s B hcc hδ (Formalism.L2.Ker.Cd.Base.isAdmissible_flagPair_of_unitriangular_left_automorphism hA) (B.thHalf_mem (B.stdOK hcc hδ) (B.latAll hcc hδ (delta_ne hcc hδ)) hA)

theorem thMoved_laF (hcc : Formalism.L2.Ker.Cd.TaylorLogMetric.IsCurveIdeal D cc) (hδ : Formalism.L2.Ker.Cd.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hA : Formalism.L2.Ker.Cd.TaylorLogMetric.admitted D a b L L') :
    (fun z => B.thMoved a b L L' (s.flatV a b z)) ∈ Th (matH (hSc X.Tau a b (TaylorLogMetric.area (Formalism.L2.Ker.Cd.TaylorLogMetric.lamOf D cc δ))⁻¹))
      (alphaQ (Real.sqrt D.host.d / 2) (matH (hSc X.Tau a b (TaylorLogMetric.area (Formalism.L2.Ker.Cd.TaylorLogMetric.lamOf D cc δ))⁻¹))) (s.laF B.tor L L') :=
  th_laF s B hcc hδ hA (B.thMoved_mem (B.latAll hcc hδ (delta_ne hcc hδ)) (B.thZeroMem (B.stdOK hcc hδ) a b) hA)

theorem eNat_laF (hcc : Formalism.L2.Ker.Cd.TaylorLogMetric.IsCurveIdeal D cc) (hδ : Formalism.L2.Ker.Cd.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (χ : Formalism.L2.Ker.Cd.TaylorLogMetric.IdE D → ℂ) (hA : Formalism.L2.Ker.Cd.TaylorLogMetric.admitted D a b L L') :
    (fun z => B.eNat χ a b L L' (s.flatV a b z)) ∈ Th (matH (hSc X.Tau a b (TaylorLogMetric.area (Formalism.L2.Ker.Cd.TaylorLogMetric.lamOf D cc δ))⁻¹))
      (alphaQ (Real.sqrt D.host.d / 2) (matH (hSc X.Tau a b (TaylorLogMetric.area (Formalism.L2.Ker.Cd.TaylorLogMetric.lamOf D cc δ))⁻¹))) (s.laF B.tor L L') :=
  Submodule.smul_mem _ (Formalism.L2.Ker.Cd.Base.chiFac χ a b L L') (thMoved_laF s B hcc hδ hA)

theorem relIdx_laF (hcc : Formalism.L2.Ker.Cd.TaylorLogMetric.IsCurveIdeal D cc) (hδ : Formalism.L2.Ker.Cd.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ)
    {L₁ : Submodule (𝓞 D.host.E) (Fin a → D.host.E)} {L₁' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)}
    (hA : Formalism.L2.Ker.Cd.TaylorLogMetric.admitted D a b L L') (hA₁ : Formalism.L2.Ker.Cd.TaylorLogMetric.admitted D a b L₁ L₁') :
    relIdx (s.laF B.tor L L') (s.laF B.tor L₁ L₁') ≠ 0 := by
  unfold Formalism.L2.Ker.Cd.Seam.laF
  rw [relIdx_comap]
  exact ((B.latAll hcc hδ (delta_ne hcc hδ)).2 a b _ _ _ _ hA hA₁).1

theorem relIdx_laF_eq {L₁ : Submodule (𝓞 D.host.E) (Fin a → D.host.E)} {L₁' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)} :
    relIdx (s.laF B.tor L L') (s.laF B.tor L₁ L₁') = relIdx (Formalism.L2.Ker.Cd.TaylorLogMetric.La D B.tor L L') (Formalism.L2.Ker.Cd.TaylorLogMetric.La D B.tor L₁ L₁') := by
  unfold Formalism.L2.Ker.Cd.Seam.laF
  rw [relIdx_comap]

end Lat

end Formalism.L2.Ker.Cd.KS.Lat
end
end

section -- merged from Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.RkVolTies
open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker.Cd

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Th1.H Formalism.L2.Col

variable {D : Car} {X : Fields}

def Seam.push (s : Seam D X) {a b : ℕ} (F : VCx X.Tau a b → ℂ) : TaylorLogMetric.VC D a b → ℂ := fun z => F fun τ => z (s.iT τ)

variable (s : Seam D X) {a b : ℕ}

end Formalism.L2.Ker.Cd
end
end

open NumberField IsDedekindDomain
open scoped Pointwise

noncomputable section

namespace Formalism.L2.Ker.Cd

open Formalism.BasicNotions Formalism.MainNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Th1.H

section Per

variable {D : Car} {X : Fields} (s : Seam D X) {a b : ℕ}

def Seam.ptE (a b : ℕ) : VCx X.Tau a b ≃ₗ[ℂ] Formalism.L2.Ker.Cd.TaylorLogMetric.VC D a b where
  toFun t := fun τ => t (s.iT.symm τ)
  invFun z := fun τ => z (s.iT τ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv t := by funext τ; simp
  right_inv z := by funext τ; simp

theorem ptE_embH (hok : s.Ok) (δ : ℂ) (x : HomE X.E a b) : s.ptE a b (embH (X.embC s.σ₀) δ x) = Formalism.L2.Ker.Cd.KS.phi s δ x := by
  funext τ i j
  show δ * s.σ₀ (X.emb (s.iT.symm τ) (x (Pi.single j 1) i)) = δ * TaylorLogMetric.embT D τ (s.iE (x (Pi.single j 1) i))
  rw [hok.1, Equiv.apply_symm_apply]

theorem lamC_eq (hok : s.Ok) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) :
    LamC (X.embC s.σ₀) δ (Formalism.L2.Ker.Cd.KS.aaX s cc) N N' = Formalism.L2.Ker.Cd.KS.pb (s.ptE a b) (Formalism.L2.Ker.Cd.TaylorLogMetric.La D (Formalism.L2.Ker.Cd.TaylorLogMetric.tor0 D cc δ) (s.lat N) (s.lat N')) := by
  ext t
  rw [← Formalism.L2.Ker.Cd.KS.phi_per]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, (ptE_embH s hok δ x).symm⟩
  · rintro ⟨x, hx, h⟩
    refine ⟨x, hx, (s.ptE a b).injective ?_⟩
    rw [ptE_embH s hok]
    exact h

theorem HV_ptE (A : ℝ) (x y : VCx X.Tau a b) : HV A⁻¹ x y = formV A D.what₂.Tau a b (s.ptE a b x) (s.ptE a b y) := by
  simp only [HV, formV, LinearMap.mk₂'ₛₗ_apply]
  rw [div_eq_inv_mul, Complex.ofReal_inv]
  congr 1
  refine Fintype.sum_equiv s.iT _ _ (fun τ => ?_)
  simp [Seam.ptE]

end Per

section Facts

variable {D : Car} {X : Fields} (s : Seam D X) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : Formalism.L2.Ker.Cd.TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) {a b : ℕ}
  (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b))

theorem alV_ptE (hcc : Formalism.L2.Ker.Cd.TaylorLogMetric.IsCurveIdeal D cc) (hδ : Formalism.L2.Ker.Cd.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hA : Formalism.L2.Ker.Cd.TaylorLogMetric.admitted D a b (s.lat N) (s.lat N')) (x : VCx X.Tau a b)
    (hx : s.ptE a b x ∈ Formalism.L2.Ker.Cd.TaylorLogMetric.La D B.tor (s.lat N) (s.lat N')) :
    alV D.host.d (TaylorLogMetric.area (Formalism.L2.Ker.Cd.TaylorLogMetric.lamOf D cc δ))⁻¹ x = Formalism.L2.Ker.Cd.TaylorLogMetric.al D B.tor (s.ptE a b x) := by
  rw [Formalism.L2.Ker.Cd.KS.Lat.al_eq_La B hcc hδ hA _ hx]
  unfold alV alphaQ Formalism.L2.Th1.H.qOf
  rw [HV_ptE s]

theorem laFacts_ambOf (hok : s.Ok) (hcc : Formalism.L2.Ker.Cd.TaylorLogMetric.IsCurveIdeal D cc) (hδ : Formalism.L2.Ker.Cd.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hA : Formalism.L2.Ker.Cd.TaylorLogMetric.admitted D a b (s.lat N) (s.lat N')) :
    LaFacts (X.embC (ambOf s B χ cD : Amb X).σ₀) (ambOf s B χ cD : Amb X).δ (ambOf s B χ cD : Amb X).d (ambOf s B χ cD : Amb X).sc
      (ambOf s B χ cD : Amb X).AA N N' := by
  have hL := (B.latAll hcc hδ (Formalism.L2.Ker.Cd.KS.Lat.delta_ne hcc hδ)).1 a b _ _ hA
  show IsSelfDual (HV (TaylorLogMetric.area (Formalism.L2.Ker.Cd.TaylorLogMetric.lamOf D cc δ))⁻¹) (LamC (X.embC s.σ₀) δ (Formalism.L2.Ker.Cd.KS.aaX s cc) N N') ∧
    IsSemiChar (HV (TaylorLogMetric.area (Formalism.L2.Ker.Cd.TaylorLogMetric.lamOf D cc δ))⁻¹) (LamC (X.embC s.σ₀) δ (Formalism.L2.Ker.Cd.KS.aaX s cc) N N') (alV D.host.d (TaylorLogMetric.area (Formalism.L2.Ker.Cd.TaylorLogMetric.lamOf D cc δ))⁻¹)
  rw [lamC_eq s hok]
  exact ⟨Formalism.L2.Ker.Cd.KS.selfDual_pb (s.ptE a b) _ _ (HV_ptE s _) hL.1,
    Formalism.L2.Ker.Cd.KS.semi_pb (s.ptE a b) _ _ (HV_ptE s _) (alV_ptE s B N N' hcc hδ hA) hL.2⟩

theorem e_fixed_ambOf (hok : s.Ok) (hcc : Formalism.L2.Ker.Cd.TaylorLogMetric.IsCurveIdeal D cc) (hδ : Formalism.L2.Ker.Cd.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hA : Formalism.L2.Ker.Cd.TaylorLogMetric.admitted D a b (s.lat N) (s.lat N')) :
    (ambOf s B χ cD : Amb X).e a b N N' ∈ fixedBy (HV (ambOf s B χ cD : Amb X).sc) (alV (ambOf s B χ cD : Amb X).d (ambOf s B χ cD : Amb X).sc)
      (LamC (X.embC (ambOf s B χ cD : Amb X).σ₀) (ambOf s B χ cD : Amb X).δ (ambOf s B χ cD : Amb X).AA N N') := by
  have h1 : B.eNat χ a b (s.lat N) (s.lat N') ∈ Th (formV (TaylorLogMetric.area (Formalism.L2.Ker.Cd.TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau a b) (Formalism.L2.Ker.Cd.TaylorLogMetric.al D B.tor)
      (Formalism.L2.Ker.Cd.TaylorLogMetric.La D B.tor (s.lat N) (s.lat N')) :=
    Submodule.smul_mem _ (Formalism.L2.Ker.Cd.Base.chiFac χ a b (s.lat N) (s.lat N'))
      (B.thMoved_mem (B.latAll hcc hδ (Formalism.L2.Ker.Cd.KS.Lat.delta_ne hcc hδ)) (B.thZeroMem (B.stdOK hcc hδ) a b) hA)
  show (fun z => B.eNat χ a b (s.lat N) (s.lat N') (s.ptE a b z)) ∈ fixedBy (HV (TaylorLogMetric.area (Formalism.L2.Ker.Cd.TaylorLogMetric.lamOf D cc δ))⁻¹)
    (alV D.host.d (TaylorLogMetric.area (Formalism.L2.Ker.Cd.TaylorLogMetric.lamOf D cc δ))⁻¹) (LamC (X.embC s.σ₀) δ (Formalism.L2.Ker.Cd.KS.aaX s cc) N N')
  rw [lamC_eq s hok]
  exact Formalism.L2.Ker.Cd.KS.fixed_pb (s.ptE a b) _ _ (HV_ptE s _) (alV_ptE s B N N' hcc hδ hA) h1.2

end Facts

section IdealS

variable {D : Car} {X : Fields} (s : Seam D X)

def Seam.oE : 𝓞 X.E ≃+* 𝓞 D.host.E := RingOfIntegers.mapRingEquiv s.iE

theorem oE_symm_coe (r : 𝓞 D.host.E) : ((s.oE.symm r : 𝓞 X.E) : X.E) = s.iE.symm (r : D.host.E) := rfl

def Seam.PrimeTo (I : Ideal (𝓞 D.host.E)) (P : HeightOneSpectrum (𝓞 X.E)) : Prop := ∃ t ∈ I, s.oE.symm t ∉ P.asIdeal

theorem primeTo_top (P : HeightOneSpectrum (𝓞 X.E)) : s.PrimeTo ⊤ P := ⟨1, Submodule.mem_top, by
  rw [map_one]
  exact fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h)⟩

theorem primeTo_mono {I J : Ideal (𝓞 D.host.E)} (h : I ≤ J) {P : HeightOneSpectrum (𝓞 X.E)} (hI : s.PrimeTo I P) : s.PrimeTo J P := by
  obtain ⟨t, ht, htP⟩ := hI
  exact ⟨t, h ht, htP⟩

theorem primeTo_half {P : HeightOneSpectrum (𝓞 X.E)} (h : s.PrimeTo (differentIdeal (𝓞 D.host.K) (𝓞 D.host.E)) P) : s.PrimeTo D.host.𝔟 P := by
  refine primeTo_mono s ?_ h
  rw [D.host.𝔟_spec.1]
  exact Submodule.mul_le.mpr fun x hx y _ => D.host.𝔟.mul_mem_right y hx

theorem half_ne_bot (D : Car) : D.host.𝔟 ≠ ⊥ := by
  intro h
  have h1 := D.host.𝔟_spec.1
  rw [h, Submodule.bot_mul] at h1
  exact differentIdeal_ne_bot h1

theorem exists_integral_mul_order_element {t₀ : 𝓞 D.host.E} (h₀ : t₀ ∈ D.host.𝔟) {t : D.host.E} (ht : t ∈ D.host.AA0) :
    ∃ w : 𝓞 D.host.E, (w : D.host.E) = (t₀ : D.host.E) * t := by
  have hb : (D.host.𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
    exact half_ne_bot D
  have ht' : t ∈ (D.host.𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)⁻¹ := ht
  have hm := FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem (nonZeroDivisors (𝓞 D.host.E)) h₀) ht'
  rw [mul_inv_cancel₀ hb, FractionalIdeal.mem_one_iff] at hm
  obtain ⟨w, hw⟩ := hm
  exact ⟨w, hw⟩

variable (cc : Ideal (𝓞 D.host.K))

theorem half_smul_aa {t₀ : 𝓞 D.host.E} (h₀ : t₀ ∈ D.host.𝔟) {r : X.E} (hr : r ∈ Formalism.L2.Ker.Cd.KS.aaX s cc) :
    s.oE.symm t₀ • r ∈ (1 : Submodule (𝓞 X.E) X.E) := by
  induction hr using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc, t, ht, rfl⟩ := hx
    obtain ⟨w, hw⟩ := exists_integral_mul_order_element h₀ ht
    rw [Submodule.mem_one]
    refine ⟨s.oE.symm (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c * w), ?_⟩
    rw [Algebra.smul_def]
    show ((s.oE.symm (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c * w) : 𝓞 X.E) : X.E) = ((s.oE.symm t₀ : 𝓞 X.E) : X.E) * _
    rw [oE_symm_coe, oE_symm_coe, ← map_mul]
    congr 1
    rw [show ((algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c * w : 𝓞 D.host.E) : D.host.E)
        = ((algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c : 𝓞 D.host.E) : D.host.E) * (w : D.host.E)
        from map_mul (algebraMap (𝓞 D.host.E) D.host.E) _ _, hw]
    rw [show ((algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c : 𝓞 D.host.E) : D.host.E)
        = (((c : 𝓞 D.host.K) : D.host.K) : D.host.E) from rfl]
    ring
  | zero => simp
  | add x y _ _ hx hy =>
    rw [smul_add]
    exact add_mem hx hy
  | smul a x _ hx =>
    rw [smul_smul, mul_comm, ← smul_smul]
    exact Submodule.smul_mem _ a hx

theorem aa_fg : (Formalism.L2.Ker.Cd.KS.aaX s cc).FG := by
  obtain ⟨t₀, h₀, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (half_ne_bot D)
  have hu : ((s.oE.symm t₀ : 𝓞 X.E) : X.E) ≠ 0 := by
    rw [oE_symm_coe, map_ne_zero_iff _ s.iE.symm.injective]
    exact_mod_cast hne
  refine (isNoetherian_submodule.mp (isNoetherian_of_fg_of_noetherian _
    (Submodule.fg_span_singleton (((s.oE.symm t₀ : 𝓞 X.E) : X.E)⁻¹)))) _ ?_
  intro r hr
  obtain ⟨y, hy⟩ := Submodule.mem_one.mp (half_smul_aa s cc h₀ hr)
  rw [Submodule.mem_span_singleton]
  refine ⟨y, ?_⟩
  rw [Algebra.smul_def] at hy ⊢
  have e : algebraMap (𝓞 X.E) X.E (s.oE.symm t₀) = ((s.oE.symm t₀ : 𝓞 X.E) : X.E) := rfl
  rw [e] at hy
  rw [hy, mul_comm, ← mul_assoc, inv_mul_cancel₀ hu, one_mul]

theorem aa_unit_at (P : HeightOneSpectrum (𝓞 X.E)) (hb : s.PrimeTo D.host.𝔟 P)
    (hc : s.PrimeTo (cc.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))) P) :
    localization₂ P.asIdeal (Formalism.L2.Ker.Cd.KS.aaX s cc) = localization₂ P.asIdeal (1 : Submodule (𝓞 X.E) X.E) := by
  obtain ⟨t₀, h₀, hβ⟩ := hb
  obtain ⟨c, hcc, hγ⟩ : ∃ c ∈ cc, s.oE.symm (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c) ∉ P.asIdeal := by
    obtain ⟨t, ht, hnt⟩ := hc
    by_contra H
    push Not at H
    have h1 : cc.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) ≤ P.asIdeal.comap (s.oE.symm : 𝓞 D.host.E →+* 𝓞 X.E) :=
      Ideal.map_le_iff_le_comap.2 fun c hc => H c hc
    exact hnt (h1 ht)
  ext x
  rw [mem_locP, mem_locP]
  constructor
  · rintro ⟨σ, hσ, hx⟩
    refine ⟨s.oE.symm t₀ * σ, fun h => (P.isPrime.mem_or_mem h).elim hβ hσ, ?_⟩
    rw [mul_smul]
    exact half_smul_aa s cc h₀ hx
  · rintro ⟨σ, hσ, hx⟩
    obtain ⟨o, ho⟩ := Submodule.mem_one.1 hx
    refine ⟨s.oE.symm (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c) * σ, fun h => (P.isPrime.mem_or_mem h).elim hγ hσ, ?_⟩
    have hmem : ((s.oE.symm (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c) : 𝓞 X.E) : X.E) ∈ Formalism.L2.Ker.Cd.KS.aaX s cc :=
      Submodule.subset_span ⟨c, hcc, 1, Formalism.L2.Ker.Cd.IntegralLatticeDensity.FL.one_mem_inverse_halfDifferent D, by rw [mul_one]; rfl⟩
    have e : s.oE.symm (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c) • algebraMap (𝓞 X.E) X.E o =
        o • ((s.oE.symm (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c) : 𝓞 X.E) : X.E) := by
      rw [Algebra.smul_def, Algebra.smul_def, mul_comm]
    rw [mul_smul, ← ho, e]
    exact Submodule.smul_mem _ o hmem

end IdealS

section NatS

variable {D : Car} {X : Fields} (s : Seam D X)

end NatS

section Main

variable {D : Car} {X : Fields} (s : Seam D X) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : Formalism.L2.Ker.Cd.TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)

include s in
theorem nonempty_tau : Nonempty X.Tau := by
  have h2 : 0 < D.R.f := by
    show 0 < 2 * D.R.ord
    have := D.R.m_le_f
    have := D.R.two_le_m
    omega
  have h3 : 0 < @Fintype.card D.what₂.Tau D.what₂.instTau := by
    rw [D.what₂.card_Tau]
    exact h2
  haveI : Nonempty D.what₂.Tau := (@Fintype.card_pos_iff _ D.what₂.instTau).mp h3
  exact s.iT.nonempty

theorem laHyp_ambOf (hok : s.Ok) (hcc : Formalism.L2.Ker.Cd.TaylorLogMetric.IsCurveIdeal D cc) (hδ : Formalism.L2.Ker.Cd.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) {a b : ℕ} (ha : Even a) (hb : Even b)
    (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (hconj : ∀ P ∈ Sall, conjPrime₂ P ∉ Sall) (hhalf : ∀ P ∈ Sall, s.PrimeTo D.host.𝔟 P)
    (hcur : ∀ P ∈ Sall, s.PrimeTo (cc.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))) P) :
    (ambOf s B χ cD : Amb X).LaHyp a b Sall :=
  ⟨Formalism.L2.Ker.Cd.KS.Lat.delta_ne hcc hδ, nonempty_tau s, hconj, fun P hP => aa_unit_at s cc P (hhalf P hP) (hcur P hP), aa_fg s cc,
    fun N N' hN hN' => ⟨e_fixed_ambOf s B χ cD N N' hok hcc hδ (s.admissible_of_selfDual_lattices hok ha hb hN hN'),
      laFacts_ambOf s B χ cD N N' hok hcc hδ (s.admissible_of_selfDual_lattices hok ha hb hN hN')⟩⟩

theorem laHyp_ambOf_top {δ : ℂ} (B : Base D (⊤ : Ideal (𝓞 D.host.K)) δ) (hok : s.Ok) (hδ : Formalism.L2.Ker.Cd.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D ⊤ δ) {a b : ℕ} (ha : Even a) (hb : Even b)
    (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (hconj : ∀ P ∈ Sall, conjPrime₂ P ∉ Sall) (hhalf : ∀ P ∈ Sall, s.PrimeTo D.host.𝔟 P) :
    (ambOf s B χ cD : Amb X).LaHyp a b Sall := laHyp_ambOf s B χ cD hok ⟨top_ne_bot, by rw [Ideal.absNorm_top]; exact Nat.coprime_one_left _⟩ hδ ha hb Sall hconj hhalf
    (fun P _ => by rw [Ideal.map_top]; exact primeTo_top s P)

end Main

section Bad

open Formalism.EigenvalueLevelCeiling (plc)

variable {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

variable {sel}

variable (sel)

end Bad

section Chain

variable {D : Car} {X : Fields} {Pr : Primes X} (s : Seam D X) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : Formalism.L2.Ker.Cd.TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

end Chain

end Formalism.L2.Ker.Cd
