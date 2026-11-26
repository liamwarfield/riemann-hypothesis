module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.RhGradStatementPfB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfE

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.RhGradStatementPf
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.RgE

open Matrix Topology Filter
open scoped ComplexOrder Matrix ContDiff
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB
  ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD ReciprocityTheory.ChartRestriction.G.AR.Up.RgC

variable {f p q : ℕ}

theorem dkV_contDiff (k : Fin f) :
    ContDiff ℝ ∞ (fun v : V (nD f p q) => dk v k) := by
  have hZ : ∀ a b, ContDiff ℝ ∞ (fun v : V (nD f p q) => Zof v k a b) := by
    intro a b
    unfold Zof
    simp only [Matrix.of_apply]
    exact ((EuclideanSpace.proj (𝕜 := ℂ)
      (finProdFinEquiv (k, finProdFinEquiv (a, b)))).contDiff).restrict_scalars ℝ
  have hM : ∀ a b, ContDiff ℝ ∞ (fun v : V (nD f p q) =>
      (1 - Zof v k * (Zof v k)ᴴ : Matrix (Fin p) (Fin p) ℂ) a b) := by
    intro a b
    simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
    exact contDiff_const.sub (ContDiff.sum fun c _ => (hZ a c).mul (Complex.conjCLE.contDiff.comp (hZ b c)))
  have hdet : ContDiff ℝ ∞ (fun v : V (nD f p q) => (1 - Zof v k * (Zof v k)ᴴ).det) := by
    simp only [Matrix.det_apply']
    exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => hM (σ i) i)
  unfold dk
  exact Complex.reCLM.contDiff.comp hdet

private lemma fderiv_ofReal_sub_const {n : ℕ} (g : V n → ℝ) (K : ℝ) :
    fderiv ℝ (fun y => (((g y - K : ℝ)) : ℂ)) = fderiv ℝ (fun y => ((g y : ℝ) : ℂ)) := by
  funext y
  have h : (fun y => (((g y - K : ℝ)) : ℂ)) = fun y => ((g y : ℝ) : ℂ) - (K : ℂ) := by
    funext z
    push_cast
    ring
  rw [h, fderiv_sub_const]

private lemma wd_ofReal_sub_const {n : ℕ} (g : V n → ℝ) (K : ℝ) (j : Fin n) (y : V n) :
    wd n j (fun y => (((g y - K : ℝ)) : ℂ)) y = wd n j (fun y => ((g y : ℝ) : ℂ)) y := by
  unfold wd
  rw [fderiv_ofReal_sub_const]

private lemma leviV_ofReal_sub_const {n : ℕ} (g : V n → ℝ) (K : ℝ) (y : V n) (ξ : Fin n → ℂ) :
    leviV n (fun y => (((g y - K : ℝ)) : ℂ)) y ξ = leviV n (fun y => ((g y : ℝ) : ℂ)) y ξ := by
  have h : ∀ k, wdb n k (fun y => (((g y - K : ℝ)) : ℂ)) = wdb n k (fun y => ((g y : ℝ) : ℂ)) := by
    intro k
    funext z
    unfold wdb
    rw [fderiv_ofReal_sub_const]
  unfold leviV
  simp only [h]

theorem rhGrad_main (hf : 0 < f) (hm : 0 < min p q) (v0 : V (nD f p q)) (hv0 : v0 ∈ Dset f p q)
    (ξ : Fin (nD f p q) → ℂ) :
    Complex.normSq (∑ j, wd (nD f p q) j (fun w => ((rh w : ℝ) : ℂ)) v0 * ξ j) ≤
      ((f * min p q : ℕ) : ℝ) * (leviV (nD f p q) (fun w => ((rh w : ℝ) : ℂ)) v0 ξ).re := by
  classical
  have hf0 : (f : ℝ) ≠ 0 := by exact_mod_cast hf.ne'
  have hfR : (0 : ℝ) < (f : ℝ) := by exact_mod_cast hf
  have hmR : (0 : ℝ) < ((min p q : ℕ) : ℝ) := by exact_mod_cast hm
  have hm0 : ((min p q : ℕ) : ℝ) ≠ 0 := hmR.ne'
  have hC_eq : (((f * min p q : ℕ)) : ℝ) = (f : ℝ) * ((min p q : ℕ) : ℝ) := by push_cast; ring
  have hCpos : (0 : ℝ) < ((f * min p q : ℕ) : ℝ) := by rw [hC_eq]; positivity
  haveI : Nonempty (Fin f) := ⟨⟨0, hf⟩⟩
  choose Q hQc hQL hQ0 hQle using fun k : Fin f => RgD.block hm hv0 k
  have hdk : ∀ v ∈ Dset f p q, ∀ k, 0 < dk v k := by
    intro v hv k
    have hv' : ∀ k, (1 - Zof v k * (Zof v k)ᴴ).PosDef := hv
    have h := (hv' k).det_pos
    exact (Complex.pos_iff.mp h).1
  have hkey : ∀ v ∈ Dset f p q, 0 < ∑ k, Q k v ∧
      -((f * min p q : ℕ) : ℝ) * Real.log (∑ k, Q k v) ≤
        rh v - (rh v0 + ((f * min p q : ℕ) : ℝ) * Real.log ((f * min p q : ℕ) : ℝ)) := by
    intro v hv
    have ht : ∀ k, 0 < Q k v / ((min p q : ℕ) : ℝ) := by
      intro k
      have h1 := hQle k v hv
      have ha : 0 < dk v k ^ (((min p q : ℕ) : ℝ)⁻¹) := Real.rpow_pos_of_pos (hdk v hv k) _
      have ha0 : 0 < dk v0 k ^ (((min p q : ℕ) : ℝ)⁻¹) := Real.rpow_pos_of_pos (hdk v0 hv0 k) _
      by_contra hneg
      push_neg at hneg
      have h2 : dk v0 k ^ (((min p q : ℕ) : ℝ)⁻¹) * (Q k v / ((min p q : ℕ) : ℝ)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos ha0.le hneg
      linarith
    have hlog : ∀ k, Real.log (dk v k) ≤
        Real.log (dk v0 k) + ((min p q : ℕ) : ℝ) * Real.log (Q k v / ((min p q : ℕ) : ℝ)) := by
      intro k
      have h1 := hQle k v hv
      have ha : 0 < dk v k ^ (((min p q : ℕ) : ℝ)⁻¹) := Real.rpow_pos_of_pos (hdk v hv k) _
      have h2 := Real.log_le_log ha h1
      rw [Real.log_mul (Real.rpow_pos_of_pos (hdk v0 hv0 k) _).ne' (ht k).ne',
        Real.log_rpow (hdk v hv k), Real.log_rpow (hdk v0 hv0 k)] at h2
      have h3 := mul_le_mul_of_nonneg_left h2 hmR.le
      have hmm : ((min p q : ℕ) : ℝ) * ((min p q : ℕ) : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hm0
      rw [mul_add, ← mul_assoc, ← mul_assoc, hmm] at h3
      simpa only [one_mul] using h3
    have hQpos : ∀ k, 0 < Q k v := fun k => (div_pos_iff_of_pos_right hmR).mp (ht k)
    have hSpos : 0 < ∑ k, Q k v := Finset.sum_pos (fun k _ => hQpos k) Finset.univ_nonempty
    refine ⟨hSpos, ?_⟩
    have hJ : ∑ k, (f : ℝ)⁻¹ • Real.log (Q k v / ((min p q : ℕ) : ℝ)) ≤
        Real.log (∑ k, (f : ℝ)⁻¹ • (Q k v / ((min p q : ℕ) : ℝ))) :=
      (strictConcaveOn_log_Ioi.concaveOn).le_map_sum (fun _ _ => inv_nonneg.mpr hfR.le)
        (by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            exact mul_inv_cancel₀ hf0)
        (fun k _ => ht k)
    have hS : ∑ k, (f : ℝ)⁻¹ • (Q k v / ((min p q : ℕ) : ℝ)) =
        (∑ k, Q k v) / ((f * min p q : ℕ) : ℝ) := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [smul_eq_mul, hC_eq]
      field_simp
    have hL : ∑ k, (f : ℝ)⁻¹ • Real.log (Q k v / ((min p q : ℕ) : ℝ)) =
        (f : ℝ)⁻¹ * ∑ k, Real.log (Q k v / ((min p q : ℕ) : ℝ)) := by
      simp only [smul_eq_mul, Finset.mul_sum]
    rw [hS, hL, Real.log_div hSpos.ne' hCpos.ne'] at hJ
    have hsum : ∑ k, Real.log (dk v k) ≤ ∑ k, Real.log (dk v0 k) +
        ((min p q : ℕ) : ℝ) * ∑ k, Real.log (Q k v / ((min p q : ℕ) : ℝ)) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun k _ => hlog k
    have hmX : ((min p q : ℕ) : ℝ) * ∑ k, Real.log (Q k v / ((min p q : ℕ) : ℝ)) =
        ((f * min p q : ℕ) : ℝ) * ((f : ℝ)⁻¹ * ∑ k, Real.log (Q k v / ((min p q : ℕ) : ℝ))) := by
      rw [hC_eq]
      field_simp
    have hCJ : ((f * min p q : ℕ) : ℝ) * ((f : ℝ)⁻¹ * ∑ k, Real.log (Q k v / ((min p q : ℕ) : ℝ))) ≤
        ((f * min p q : ℕ) : ℝ) * Real.log (∑ k, Q k v) -
          ((f * min p q : ℕ) : ℝ) * Real.log ((f * min p q : ℕ) : ℝ) := by
      rw [← mul_sub]
      exact mul_le_mul_of_nonneg_left hJ hCpos.le
    have hrv : rh v = -∑ k, Real.log (dk v k) := rfl
    have hrv0 : rh v0 = -∑ k, Real.log (dk v0 k) := rfl
    rw [hrv, hrv0]
    linarith
  have hle : ∀ᶠ v in 𝓝 v0, -((f * min p q : ℕ) : ℝ) * Real.log (∑ k, Q k v) ≤
      rh v - (rh v0 + ((f * min p q : ℕ) : ℝ) * Real.log ((f * min p q : ℕ) : ℝ)) := by
    filter_upwards [(isOpen_Dset f p q).mem_nhds hv0] with v hv using (hkey v hv).2
  have h2c : ∀ {g : V (nD f p q) → ℝ}, ContDiff ℝ ∞ g → ContDiffAt ℝ 2 g v0 := fun hg => by
    simpa using (contDiff_infty.mp hg 2).contDiffAt
  have hrhc : ContDiffAt ℝ 2 (fun v : V (nD f p q) =>
      rh v - (rh v0 + ((f * min p q : ℕ) : ℝ) * Real.log ((f * min p q : ℕ) : ℝ))) v0 := by
    have h1 : ContDiffAt ℝ 2 (fun v : V (nD f p q) => -∑ k, Real.log (dk v k)) v0 := by
      refine ContDiffAt.neg (ContDiffAt.sum fun k _ => ?_)
      exact (h2c (dkV_contDiff k)).log (hdk v0 hv0 k).ne'
    exact h1.sub contDiffAt_const
  have hΨc : ContDiffAt ℝ 2 (fun v : V (nD f p q) => ∑ k, Q k v) v0 :=
    ContDiffAt.sum fun k _ => h2c (hQc k)
  have hLev : (leviV (nD f p q) (fun y => ((∑ k, Q k y : ℝ) : ℂ)) v0 ξ).re ≤ 0 := by
    rw [leviV_ofReal_sum (fun k => h2c (hQc k)) ξ,
      Complex.re_sum]
    exact Finset.sum_nonpos fun k _ => hQL k ξ
  have hSv0 : ∑ k, Q k v0 = ((f * min p q : ℕ) : ℝ) := by
    simp only [hQ0, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [hC_eq]
  have heq : rh v0 - (rh v0 + ((f * min p q : ℕ) : ℝ) * Real.log ((f * min p q : ℕ) : ℝ)) =
      -((f * min p q : ℕ) : ℝ) * Real.log (∑ k, Q k v0) := by
    rw [hSv0]
    ring
  have hmain := RgA.grad_le_of_minorant
    (fun v : V (nD f p q) =>
      rh v - (rh v0 + ((f * min p q : ℕ) : ℝ) * Real.log ((f * min p q : ℕ) : ℝ)))
    (fun v : V (nD f p q) => ∑ k, Q k v) v0 ((f * min p q : ℕ) : ℝ) hCpos
    (hkey v0 hv0).1 hrhc hΨc ξ hLev hle heq
  simp only [wd_ofReal_sub_const (fun w : V (nD f p q) => rh w), leviV_ofReal_sub_const (fun w : V (nD f p q) => rh w)]
    at hmain
  exact hmain

end ReciprocityTheory.ChartRestriction.G.AR.Up.RgE

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up.RgE

theorem RhGradStatement_holds : RhGradStatement := by
  intro f p q v hv ξ
  by_cases h : 0 < f ∧ 0 < min p q
  · exact rhGrad_main h.1 h.2 v hv ξ
  · have hn : nD f p q = 0 := by
      simp only [nD]
      rcases Nat.eq_zero_or_pos f with hf | hf
      · simp [hf]
      · have hm : ¬ 0 < min p q := fun hm => h ⟨hf, hm⟩
        rcases Nat.min_eq_zero_iff.mp (Nat.eq_zero_of_not_pos hm) with hp | hq
        · simp [hp]
        · simp [hq]
    haveI : IsEmpty (Fin (nD f p q)) := by rw [hn]; infer_instance
    simp [leviV]

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.RGF

open Filter Topology Set Matrix NumberField ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst
  ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ContDiff ComplexOrder

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

def eΨ : Fin X.Ψ.card ≃ X.Ψ := X.Ψ.equivFin.symm

def Zmap (z : V (nd X)) : V (nD X.Ψ.card X.p0 (r - X.p0)) :=
  WithLp.toLp 2 fun j => ExF.Zt X z (eΨ X (finProdFinEquiv.symm j).1)
    (finProdFinEquiv.symm (finProdFinEquiv.symm j).2).1 (finProdFinEquiv.symm (finProdFinEquiv.symm j).2).2

theorem Zof_Zmap (z : V (nd X)) (k : Fin X.Ψ.card) : Zof (Zmap X z) k = ExF.Zt X z (eΨ X k) := by
  ext a b
  change ExF.Zt X z (eΨ X (finProdFinEquiv.symm (finProdFinEquiv (k, finProdFinEquiv (a, b)))).1) _ _ = _
  simp only [Equiv.symm_apply_apply]

private theorem contDiff_nM_apply (τ : X.Ψ) (a b : Fin r) :
    ContDiff ℂ ∞ fun z : V (nd X) => ExF.nM X z τ a b := by
  unfold ExF.nM
  simp only [mat, Matrix.of_apply, nmat]
  split_ifs
  · first
    | exact ((contDiff_piLp _).mp contDiff_id) _
    | fun_prop
  · exact contDiff_const
  · exact contDiff_const

private theorem det_n1_eq_one (z : V (nd X)) (τ : X.Ψ) : (ExF.n1 X z τ).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · apply Finset.prod_eq_one
    intro i _
    change nmat X z τ (Fin.castLE X.p0_le i) (Fin.castLE X.p0_le i) = 1
    simp [nmat]
  · intro i j hij
    have hlt : i < j := OrderDual.toDual_lt_toDual.mp hij
    rw [Fin.lt_def] at hlt
    change nmat X z τ (Fin.castLE X.p0_le i) (Fin.castLE X.p0_le j) = 0
    have h1 : ¬ (Fin.castLE X.p0_le j < Fin.castLE X.p0_le i) := by
      rw [Fin.lt_def]; simp only [Fin.coe_castLE]; omega
    have h2 : Fin.castLE X.p0_le i ≠ Fin.castLE X.p0_le j := by
      intro h; rw [Fin.ext_iff] at h; simp only [Fin.coe_castLE] at h; omega
    simp only [nmat, dif_neg h1, if_neg h2]

private theorem inv_n1_eq_adjugate (z : V (nd X)) (τ : X.Ψ) : (ExF.n1 X z τ)⁻¹ = (ExF.n1 X z τ).adjugate := by
  rw [Matrix.inv_def, det_n1_eq_one, Ring.inverse_one, one_smul]

private theorem contDiff_det_of_contDiff_entries {n : ℕ} (M : V (nd X) → Matrix (Fin n) (Fin n) ℂ)
    (hM : ∀ i j, ContDiff ℂ ∞ fun z => M z i j) : ContDiff ℂ ∞ fun z => (M z).det := by
  simp only [Matrix.det_apply']
  refine ContDiff.sum fun σ _ => contDiff_const.mul ?_
  first
  | exact contDiff_prod fun i _ => hM _ _
  | fun_prop

private theorem contDiff_adjugate_apply_of_contDiff_entries {n : ℕ} (M : V (nd X) → Matrix (Fin n) (Fin n) ℂ)
    (hM : ∀ i j, ContDiff ℂ ∞ fun z => M z i j) (a b : Fin n) :
    ContDiff ℂ ∞ fun z => (M z).adjugate a b := by
  simp only [Matrix.adjugate_apply]
  apply contDiff_det_of_contDiff_entries
  intro i j
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact contDiff_const
  · exact hM i j

theorem Zmap_contDiff : ContDiff ℂ ∞ (Zmap X) := by
  have hn1 : ∀ τ : X.Ψ, ∀ i j, ContDiff ℂ ∞ fun z : V (nd X) => ExF.n1 X z τ i j :=
    fun τ i j => contDiff_nM_apply X τ (Fin.castLE X.p0_le i) (Fin.castLE X.p0_le j)
  have hW : ∀ τ : X.Ψ, ∀ b c, ContDiff ℂ ∞ fun z : V (nd X) => ExF.Wm X z τ b c :=
    fun τ b c => contDiff_nM_apply X τ (ExF.qI X b) (Fin.castLE X.p0_le c)
  refine (contDiff_piLp _).mpr fun j => ?_
  change ContDiff ℂ ∞ fun z : V (nd X) => ExF.Zt X z _ _ _
  simp only [ExF.Zt, Matrix.transpose_apply, inv_n1_eq_adjugate, Matrix.mul_apply]
  exact ContDiff.sum fun c _ => (hW _ _ _).mul (contDiff_adjugate_apply_of_contDiff_entries X (fun z => ExF.n1 X z _) (hn1 _) _ _)

theorem rh_Zmap (x0 : Frame X.Ψ r) (ho : IsOrth X x0) {z : V (nd X)} (hz : z ∈ OmF X x0) :
    rh (Zmap X z) = rhF X x0 z := by
  rw [ExF.rhF_eq_sum X x0 ho, rh]
  congr 1
  rw [← (eΨ X).sum_comp]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Zof_Zmap]
  have hpd := (ExF.mem_OmF_iff X x0 ho z).1 hz (eΨ X k)
  rw [show (1 - ExF.Zt X z (eΨ X k) * (ExF.Zt X z (eΨ X k))ᴴ) = ExF.Am X z (eΨ X k) from rfl,
    ExF.norm_of_pos hpd.det_pos]

theorem Zmap_mem (x0 : Frame X.Ψ r) (ho : IsOrth X x0) {z : V (nd X)} (hz : z ∈ OmF X x0) :
    Zmap X z ∈ Dset X.Ψ.card X.p0 (r - X.p0) := by
  intro k
  rw [Zof_Zmap]
  exact (ExF.mem_OmF_iff X x0 ho z).1 hz (eΨ X k)

theorem rh_contDiffAt {f p q : ℕ} {v : V (nD f p q)} (hv : v ∈ Dset f p q) :
    ContDiffAt ℝ 2 (fun w : V (nD f p q) => ((rh w : ℝ) : ℂ)) v := by
  have hZ : ∀ k a b, ContDiff ℝ 2 fun w : V (nD f p q) => Zof w k a b := by
    intro k a b
    simp only [Zof, Matrix.of_apply]
    first
    | exact ((contDiff_piLp _).mp contDiff_id) _
    | fun_prop
  have hM : ∀ k i j, ContDiff ℝ 2 fun w : V (nD f p q) => (1 - Zof w k * (Zof w k)ᴴ : Matrix (Fin p) (Fin p) ℂ) i j := by
    intro k i j
    simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
    refine contDiff_const.sub (ContDiff.sum fun l _ => (hZ k i l).mul ?_)
    have h := hZ k j l
    first
    | exact h.star
    | exact Complex.conjCLE.contDiff.comp h
    | fun_prop
  have hdet : ∀ k, ContDiff ℝ 2 fun w : V (nD f p q) => (1 - Zof w k * (Zof w k)ᴴ).det := by
    intro k
    simp only [Matrix.det_apply']
    refine ContDiff.sum fun σ _ => contDiff_const.mul ?_
    first
    | exact contDiff_prod fun i _ => hM k _ _
    | fun_prop
  have hpos : ∀ k, 0 < ((1 - Zof v k * (Zof v k)ᴴ).det).re := by
    intro k
    have h := (hv k).det_pos
    first
    | exact (Complex.pos_iff.mp h).1
    | simpa using (Complex.lt_def.mp h).1
  have hlog : ∀ k, ContDiffAt ℝ 2
      (fun w : V (nD f p q) => Real.log ((1 - Zof w k * (Zof w k)ᴴ).det.re)) v := by
    intro k
    have hre : ContDiff ℝ 2 fun w : V (nD f p q) => ((1 - Zof w k * (Zof w k)ᴴ).det).re :=
      Complex.reCLM.contDiff.comp (hdet k)
    exact (Real.contDiffAt_log.mpr (hpos k).ne').comp v hre.contDiffAt
  have hsum : ContDiffAt ℝ 2 (fun w : V (nD f p q) => rh w) v := by
    unfold rh
    exact (ContDiffAt.sum fun k _ => hlog k).neg
  exact Complex.ofRealCLM.contDiff.contDiffAt.comp v hsum

end

theorem rhGradF_holds {E : Type} [Field E] [NumberField E] [IsCMField E] : RhGradFStatement (E := E) := by
  intro r X x0 ho z hz ξ
  have hU := ExF.isOpen_OmF X x0
  have hZ : ContDiff ℂ ∞ (Zmap X) := Zmap_contDiff X
  have hZd : HasFDerivAt (Zmap X) (fderiv ℂ (Zmap X) z) z :=
    (hZ.differentiable (by simp) z).hasFDerivAt
  have hmem := Zmap_mem X x0 ho hz
  have hg := rh_contDiffAt hmem
  have hev : (fun w : V (nd X) => ((rhF X x0 w : ℝ) : ℂ)) =ᶠ[𝓝 z]
      (fun w : V (nD X.Ψ.card X.p0 (r - X.p0)) => ((rh w : ℝ) : ℂ)) ∘ Zmap X := by
    filter_upwards [hU.mem_nhds hz] with w hw
    simp only [Function.comp_apply, rh_Zmap X x0 ho hw]
  have h1 : ∑ j, wd (nd X) j (fun w => ((rhF X x0 w : ℝ) : ℂ)) z * ξ j =
      ∑ a, wd _ a (fun w => ((rh w : ℝ) : ℂ)) (Zmap X z) *
        fderiv ℂ (Zmap X) z (WithLp.toLp 2 ξ) a := by
    rw [← gc_sum_wd_comp _ _ _ _ _ z (hg.differentiableAt (by norm_num)) hZd ξ]
    exact Finset.sum_congr rfl fun j _ => by rw [wd_congr (nd X) j _ _ z hev]
  have h2 : leviV (nd X) (fun w => ((rhF X x0 w : ℝ) : ℂ)) z ξ =
      leviV _ (fun w => ((rh w : ℝ) : ℂ)) (Zmap X z) (fun b => fderiv ℂ (Zmap X) z (WithLp.toLp 2 ξ) b) := by
    rw [Y.fc_leviV_congr (nd X) _ _ z hev]
    exact gc_leviV_comp _ _ _ _ Set.univ isOpen_univ z trivial (hZ.contDiffOn.of_le (m := 2) (WithTop.coe_le_coe.mpr le_top)) hg ξ
  rw [h1, h2]
  exact RhGradStatement_holds _ _ _ _ hmem _

end ReciprocityTheory.ChartRestriction.G.AR.Up.RGF

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField

theorem RhGradFStatement_holds {E : Type} [Field E] [NumberField E] [IsCMField E] :
    RhGradFStatement (E := E) := RGF.rhGradF_holds

end ReciprocityTheory.ChartRestriction.G.AR.Up
