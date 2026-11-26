module

public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet
public import Formalism.LocalToGlobal.ProjectiveLattices.FullExists

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitScalar

open GlobalTheory.LatVac GlobalTheory.DualPairCheck

variable {D : D7}

theorem gramInv_star (S : HSp D) (i j : Fin S.rank) : star (S.gram⁻¹ i j) = S.gram⁻¹ j i := by
  have h : S.gramᴴ = S.gram := Matrix.ext fun i j => GlobalTheory.LatVac.gram_star S j i
  have h2 : (S.gram⁻¹)ᴴ = S.gram⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, h]
  exact congrFun (congrFun h2 j) i

theorem hO_herm (S T : HSp D) (x y : WO S T) : cA D (hO S T x y) = hO S T y x := by
  unfold hO
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, RingHom.map_mul, cA_incA, GlobalTheory.DualPairCheck.cA_cA, gramInv_star, GlobalTheory.LatVac.gram_star]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  ring

theorem symplO_skew (S T : HSp D) (x y : WO S T) : symplO S T y x = -symplO S T x y := by
  unfold symplO
  rw [← trace_cA, RingHom.map_mul, cA_incA, star_purely_imaginary_eq_neg, hO_herm, RingHom.map_neg, neg_mul, map_neg]

theorem hO_smul_left (S T : HSp D) (a : AE D) (x y : WO S T) : hO S T (a • x) y = a * hO S T x y := by
  simp only [hO, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

theorem hO_smul_right (S T : HSp D) (a : AE D) (x y : WO S T) : hO S T x (a • y) = cA D a * hO S T x y := by
  simp only [hO, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.map_mul]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

theorem symplO_smul (S T : HSp D) (a : AE D) (x y : WO S T) :
    symplO S T (a • x) y = symplO S T x (cA D a • y) := by
  rw [symplO, symplO, hO_smul_left, hO_smul_right, GlobalTheory.DualPairCheck.cA_cA]

theorem symplO_zero_left (S T : HSp D) (y : WO S T) : symplO S T 0 y = 0 := by
  rw [← symplHom_apply, map_zero]; rfl

theorem symplO_zero_right (S T : HSp D) (x : WO S T) : symplO S T x 0 = 0 := by
  rw [← symplHom_apply, map_zero]

theorem symplO_sub_left (S T : HSp D) (x x' y : WO S T) :
    symplO S T (x - x') y = symplO S T x y - symplO S T x' y := by
  rw [← symplHom_apply, map_sub]; rfl

theorem isHalf_iff {m n : ℕ} (e : AE D) (u : Mx D m n) : IsHalf e u ↔ e • u = u :=
  ⟨fun h => Matrix.ext fun i j => h i j, fun h i j => congrFun (congrFun h i) j⟩

theorem symplO_eq_zero (S T : HSp D) {a b : AE D} (hab : cA D a * b = 0) {x y : WO S T} (hx : IsHalf a x)
    (hy : IsHalf b y) : symplO S T x y = 0 := by
  rw [← (isHalf_iff _ _).1 hx, ← (isHalf_iff _ _).1 hy, symplO_smul, smul_smul, hab, zero_smul, symplO_zero_right]

theorem symplOH_add_left (S T : HSp D) (x x' y : WO S T) :
    symplOH S T (x + x') y = symplOH S T x y + symplOH S T x' y := by
  simp only [symplOH, symplO_add_left, mul_add]

theorem symplOH_add_right (S T : HSp D) (x y y' : WO S T) :
    symplOH S T x (y + y') = symplOH S T x y + symplOH S T x y' := by
  simp only [symplOH, symplO_add_right, mul_add]

theorem symplOH_add_self (S T : HSp D) (x y : WO S T) :
    symplOH S T x y + symplOH S T x y = symplO S T x y := by
  rw [symplOH, ← add_mul, ← map_add (f := _), add_halves, map_one, one_mul]

theorem symplOH_skew (S T : HSp D) (x y : WO S T) : symplOH S T y x = -symplOH S T x y := by
  rw [symplOH, symplOH, symplO_skew, mul_neg]

theorem heisO_heisO (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w w' : WO S T) (f : WO S T → ℂ) :
    heisO ψ S T w (heisO ψ S T w' f) = ψ (symplOH S T w w') • heisO ψ S T (w + w') f := by
  funext u
  simp only [heisO, Pi.smul_apply, smul_eq_mul, symplOH_add_left, symplOH_add_right, AddChar.map_add_eq_mul,
    add_assoc]
  ring

theorem heisO_add_of_orth (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {w w' : WO S T} (h : symplO S T w w' = 0)
    (f : WO S T → ℂ) : heisO ψ S T (w + w') f = heisO ψ S T w (heisO ψ S T w' f) := by
  rw [heisO_heisO, symplOH, h, mul_zero, AddChar.map_zero_eq_one, one_smul]

theorem heisO_comm (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w w' : WO S T) (f : WO S T → ℂ) :
    heisO ψ S T w (heisO ψ S T w' f) = ψ (symplO S T w w') • heisO ψ S T w' (heisO ψ S T w f) := by
  rw [heisO_heisO, heisO_heisO, smul_smul, ← AddChar.map_add_eq_mul, add_comm w' w, ← symplOH_add_self,
    symplOH_skew S T w w', add_neg_cancel_right]

theorem heisO_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f : WO S T → ℂ) : heisO ψ S T 0 f = f := by
  funext u
  simp only [heisO, symplOH, symplO_zero_right, mul_zero, AddChar.map_zero_eq_one, one_mul, add_zero]

def heisL (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) : Module.End ℂ (WO S T → ℂ) where
  toFun := heisO ψ S T w
  map_add' f g := by funext u; simp only [heisO, Pi.add_apply, mul_add]
  map_smul' c f := by funext u; simp only [heisO, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem heisL_apply (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) (f : WO S T → ℂ) :
    heisL ψ S T w f = heisO ψ S T w f := rfl

theorem heisO_smul (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) (c : ℂ) (f : WO S T → ℂ) :
    heisO ψ S T w (c • f) = c • heisO ψ S T w f := (heisL ψ S T w).map_smul c f

theorem heisO_sum (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) {ι : Type} (s : Finset ι)
    (f : ι → WO S T → ℂ) : heisO ψ S T w (∑ i ∈ s, f i) = ∑ i ∈ s, heisO ψ S T w (f i) :=
  map_sum (heisL ψ S T w) f s

def realIdem (D : D7) : AE D := pairA D.host.F 1 0 ⊗ₜ[D.host.F] (1 : D.host.E)

theorem cA_realIdem : cA D (realIdem D) = realIdem D := by
  show pairA D.host.F 1 0 ⊗ₜ[D.host.F] D.sp.cm.sig (1 : D.host.E) = _
  rw [map_one]; rfl

theorem infPart_realIdem : infPart D (realIdem D) = 1 := rfl

theorem finPart_realIdem : finPart D (realIdem D) = 0 := TensorProduct.zero_tmul _ _

theorem adele_ext {a b : AE D} (h1 : infPart D a = infPart D b) (h2 : finPart D a = finPart D b) : a = b :=
  sub_eq_zero.1 (GlobalTheory.FockCompare.RealChart.adele_tensor_ext (a - b)
    (show infPart D (a - b) = 0 by rw [RingHom.map_sub, h1, sub_self])
    (show finPart D (a - b) = 0 by rw [RingHom.map_sub, h2, sub_self]))

theorem realIdem_mul_of_fin {a : AE D} (h : infPart D a = 0) : realIdem D * a = 0 :=
  adele_ext (by rw [RingHom.map_mul, h, mul_zero, RingHom.map_zero])
    (by rw [RingHom.map_mul, finPart_realIdem, zero_mul, RingHom.map_zero])

theorem realIdem_mul_of_real {a : AE D} (h : finPart D a = 0) : realIdem D * a = a :=
  adele_ext (by rw [RingHom.map_mul, infPart_realIdem, one_mul])
    (by rw [RingHom.map_mul, h, mul_zero])

theorem symplO_real_fin (S T : HSp D) {x y : WO S T} (hx : x.map (finPart D) = 0) (hy : y.map (infPart D) = 0) :
    symplO S T x y = 0 := by
  have h1 : realIdem D • x = x := Matrix.ext fun i j => realIdem_mul_of_real (congrFun (congrFun hx i) j)
  have h2 : realIdem D • y = 0 := Matrix.ext fun i j => realIdem_mul_of_fin (congrFun (congrFun hy i) j)
  rw [← h1, symplO_smul, cA_realIdem, h2, symplO_zero_right]

theorem latO_fin {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {u : WO S T} (hu : u ∈ latO S T LS LT fun _ => True) : u.map (infPart D) = 0 := by
  refine latO_induction (p := fun u => u.map (infPart D) = 0) (fun α _ M _ => ?_) ?_ (fun x y hx hy => ?_)
    (fun x hx => ?_) hu
  · ext i j
    exact TensorProduct.zero_tmul _ _
  · ext i j
    exact (infPart D).map_zero
  · ext i j
    have h1 : infPart D (x i j) = 0 := congrFun (congrFun hx i) j
    have h2 : infPart D (y i j) = 0 := congrFun (congrFun hy i) j
    show infPart D (x i j + y i j) = 0
    rw [RingHom.map_add (f := _), h1, h2, add_zero]
  · ext i j
    have h1 : infPart D (x i j) = 0 := congrFun (congrFun hx i) j
    show infPart D (-x i j) = 0
    rw [RingHom.map_neg, h1, neg_zero]

theorem isSplitIdem_conj {e : AE D} (he : IsSplitIdem D e) : IsSplitIdem D (cA D e) := by
  obtain ⟨h1, h2, v, ε, h3, h4⟩ := he
  refine ⟨by rw [← RingHom.map_mul, h1], by rw [GlobalTheory.DualPairCheck.cA_cA, mul_comm, h2], v, ε, h3, ?_⟩
  rw [GlobalTheory.DualPairCheck.cA_cA, add_comm, h4]

theorem infPart_splitIdem {e : AE D} (he : IsSplitIdem D e) : infPart D e = 0 := by
  obtain ⟨h1, h2, v, ε, ⟨α, rfl, -⟩, h4⟩ := he
  have h5 : infPart D (e + cA D e) = 0 := by
    rw [h4]
    exact TensorProduct.zero_tmul _ _
  have h6 : e = e * (e + cA D e) := by rw [mul_add, h1, h2, add_zero]
  rw [h6, RingHom.map_mul, h5, mul_zero]

theorem half_fin {m n : ℕ} {e : AE D} (he : IsSplitIdem D e) {u : Mx D m n} (hu : IsHalf e u) :
    u.map (infPart D) = 0 := by
  ext i j
  show infPart D (u i j) = 0
  rw [← hu i j, RingHom.map_mul, infPart_splitIdem he, zero_mul]

theorem continuous_symplO (S T : HSp D) {X : Type} [TopologicalSpace X] {x y : X → WO S T} (hx : Continuous x)
    (hy : Continuous y) : Continuous fun t => symplO S T (x t) (y t) := by
  have ht : Continuous (Algebra.trace (AF D.host.F) (AE D)) := IsModuleTopology.continuous_of_linearMap _
  have hy' : ∀ i j, Continuous fun t => cA D (y t i j) := fun i j =>
    GlobalTheory.FockCompare.ThetaCont.continuous_conj.comp ((continuous_apply j).comp ((continuous_apply i).comp hy))
  have hx' : ∀ i j, Continuous fun t => x t i j := fun i j =>
    (continuous_apply j).comp ((continuous_apply i).comp hx)
  refine ht.comp (continuous_const.mul ?_)
  exact continuous_finsetSum _ fun _ _ => continuous_finsetSum _ fun _ _ => continuous_finsetSum _ fun _ _ =>
      continuous_finsetSum _ fun _ _ => ((continuous_const.mul (hy' _ _)).mul continuous_const).mul (hx' _ _)

theorem exists_nsmul_mem {m n : ℕ} (U : AddSubgroup (Mx D m n)) (hU : IsOpen (U : Set (Mx D m n))) {y : Mx D m n}
    (hy : y.map (infPart D) = 0) : ∃ N : ℕ, 0 < N ∧ N • y ∈ U := by
  let φ : Af D.host.F → Mx D m n := fun α => Matrix.of fun i j => pairA D.host.F 0 α • y i j
  have hp : Continuous fun α : Af D.host.F => pairA D.host.F 0 α := continuous_const.prodMk continuous_id
  have hφ : Continuous φ := continuous_pi fun i => continuous_pi fun j => hp.smul continuous_const
  have h0 : φ 0 = 0 := Matrix.ext fun i j => zero_smul (AF D.host.F) (y i j)
  obtain ⟨N, hN, h⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele D.host.F (φ ⁻¹' U)
    (hφ.continuousAt.preimage_mem_nhds (hU.mem_nhds (h0 ▸ U.zero_mem)))
  refine ⟨N, hN, ?_⟩
  have h1 : φ (N • 1) ∈ U := h 1 fun v => one_mem _
  have h2 : φ (N • 1) = N • y := by
    refine Matrix.ext fun i j => ?_
    have e1 : pairA D.host.F 0 (N • 1) = N • (1 - pairA D.host.F 1 0) :=
      Prod.ext (show (0 : Ainf D.host.F) = N • (1 - 1) by rw [sub_self, smul_zero])
        (show (N • 1 : Af D.host.F) = N • (1 - 0) by rw [sub_zero])
    have e2 : pairA D.host.F 1 0 • y i j = 0 := by
      rw [Algebra.smul_def]
      exact realIdem_mul_of_fin (congrFun (congrFun hy i) j)
    show pairA D.host.F 0 (N • 1) • y i j = N • y i j
    rw [e1, smul_assoc, sub_smul, one_smul, e2, sub_zero]
  rwa [h2] at h1

end GlobalTheory.SplitScalar

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmAtSmulRight
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.VacUnique

open GlobalTheory.FockCompare

variable {D : D7}

def hAt (S T : HSp D) (τ : D.what₂.Tau) (x y : Matrix (Fin T.rank) (Fin S.rank) ℂ) : ℂ :=
  ((gramAt D S τ)⁻¹ * yᴴ * gramAt D T τ * x).trace

def omAt (S T : HSp D) (τ : D.what₂.Tau) (x y : Matrix (Fin T.rank) (Fin S.rank) ℂ) : ℝ :=
  2 * (tauE D τ D.host.xi0 * hAt S T τ x y).re

theorem omAt_add_left (S T : HSp D) (τ : D.what₂.Tau) (x x' y : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    omAt S T τ (x + x') y = omAt S T τ x y + omAt S T τ x' y := by
  simp only [omAt, hAt, Matrix.mul_add, Matrix.trace_add, mul_add, Complex.add_re]

theorem omAt_add_right (S T : HSp D) (τ : D.what₂.Tau) (x y y' : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    omAt S T τ x (y + y') = omAt S T τ x y + omAt S T τ x y' := by
  simp only [omAt, hAt, Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul, Matrix.trace_add, mul_add,
    Complex.add_re]

theorem omAt_smul_left (S T : HSp D) (τ : D.what₂.Tau) (c : ℝ) (x y : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    omAt S T τ (c • x) y = c * omAt S T τ x y := by
  simp only [omAt, hAt, Matrix.mul_smul, Matrix.trace_smul, mul_smul_comm, Complex.smul_re, smul_eq_mul]
  ring

theorem omAt_smul_right (S T : HSp D) (τ : D.what₂.Tau) (c : ℝ) (x y : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    omAt S T τ x (c • y) = c * omAt S T τ x y := by
  simp only [omAt, hAt, Matrix.conjTranspose_smul, star_trivial, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul,
    mul_smul_comm, Complex.smul_re, smul_eq_mul]
  ring

def omO (S T : HSp D) : RW T S →ₗ[ℝ] RW T S →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => ∑ τ, omAt S T τ (x τ) (y τ))
    (fun x x' y => by rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun τ _ => omAt_add_left S T τ _ _ _)
    (fun c x y => by rw [smul_eq_mul, Finset.mul_sum]; exact Finset.sum_congr rfl fun τ _ => omAt_smul_left S T τ c _ _)
    (fun x y y' => by rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun τ _ => omAt_add_right S T τ _ _ _)
    (fun c x y => by rw [smul_eq_mul, Finset.mul_sum]; exact Finset.sum_congr rfl fun τ _ => omAt_smul_right S T τ c _ _)

theorem omO_apply (S T : HSp D) (x y : RW T S) : omO S T x y = ∑ τ, omAt S T τ (x τ) (y τ) := rfl

theorem cplxO_add {m n : ℕ} (s : Matrix (Fin n) (Fin n) ℂ) (t : Matrix (Fin m) (Fin m) ℂ)
    (x y : Matrix (Fin m) (Fin n) ℂ) : cplxO s t (x + y) = cplxO s t x + cplxO s t y := by
  simp only [cplxO, Matrix.mul_add, Matrix.add_mul, smul_add]

theorem cplxO_smul {m n : ℕ} (s : Matrix (Fin n) (Fin n) ℂ) (t : Matrix (Fin m) (Fin m) ℂ) (c : ℝ)
    (x : Matrix (Fin m) (Fin n) ℂ) : cplxO s t (c • x) = c • cplxO s t x := by
  simp only [cplxO, Matrix.mul_smul, Matrix.smul_mul]
  exact smul_comm _ _ _

def jO (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) : RW T S →ₗ[ℝ] RW T S where
  toFun x := fun τ => cplxO (sS τ) (sT τ) (x τ)
  map_add' x y := by funext τ; exact cplxO_add _ _ _ _
  map_smul' c x := by funext τ; exact cplxO_smul _ _ c _

theorem jO_apply (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (x : RW T S) (τ : D.what₂.Tau) :
    jO S T sS sT x τ = cplxO (sS τ) (sT τ) (x τ) := rfl

def infRat (S T : HSp D) : Matrix (Fin T.rank) (Fin S.rank) D.host.E →+ RW T S where
  toFun γ := fun τ i j => tauE D τ (γ i j)
  map_zero' := by funext τ i j; exact (tauE D τ).map_zero
  map_add' x y := by funext τ i j; exact (tauE D τ).map_add _ _

def finRat (S T : HSp D) : Matrix (Fin T.rank) (Fin S.rank) D.host.E →+ WO S T where
  toFun γ := Matrix.of fun i j => (pairA D.host.F 0 1) ⊗ₜ[D.host.F] (γ i j)
  map_zero' := by funext i j; exact TensorProduct.tmul_zero _ _
  map_add' x y := by funext i j; exact TensorProduct.tmul_add _ _ _

theorem finRat_inf (S T : HSp D) (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    (finRat S T γ).map (infPart D) = 0 := by
  funext i j
  show (0 : Ainf D.host.F) ⊗ₜ[D.host.F] (γ i j) = 0
  exact TensorProduct.zero_tmul _ _

theorem finRat_fin (S T : HSp D) (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    (finRat S T γ).map (finPart D) = (ratW T S γ).map (finPart D) := rfl

theorem piW_of_inf (θ : InfFam D) {S T : HSp D} {u : WO S T} (hu : u.map (infPart D) = 0) :
    piW θ T S u = 0 := by
  funext τ i j
  have : infPart D (u i j) = 0 := congrFun (congrFun hu i) j
  show θ τ (infPart D (u i j)) = 0
  rw [this, RingHom.map_zero]

theorem piW_ratW {θ : InfFam D} (hθ : IsInfFam θ) (S T : HSp D)
    (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) : piW θ T S (ratW T S γ) = infRat S T γ := by
  funext τ i j
  exact comp_incA hθ τ _

theorem ratW_eq {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : Chart θ σ) (S T : HSp D)
    (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    ratW T S γ = iotaW σ T S (infRat S T γ) + finRat S T γ := by
  have e : (ratW T S γ - finRat S T γ : WA T S) = iotaW σ T S (infRat S T γ) := by
    refine h.real_ext ?_ (h.real_iota T S _) ?_
    · funext i j
      have e1 : finPart D (finRat S T γ i j) = finPart D (ratW T S γ i j) := rfl
      show finPart D (ratW T S γ i j - finRat S T γ i j) = 0
      rw [RingHom.map_sub, e1, sub_self]
    · rw [AddMonoidHom.map_sub, piW_of_inf θ (finRat_inf S T γ), piW_ratW h.inf, h.pi_iota, sub_zero]
  exact sub_eq_iff_eq_add.1 e

theorem latO_inf (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) {u : WO S T} (hu : u ∈ latO S T LS LT P) :
    u.map (infPart D) = 0 := by
  have : latO S T LS LT P ≤ ((infPart D).toAddMonoidHom.mapMatrix (m := Fin T.rank) (n := Fin S.rank)).ker := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, -, -, a, -, s, -, t, -, rfl⟩
    funext i j
    show (0 : Ainf D.host.F) ⊗ₜ[D.host.F] _ = 0
    exact TensorProduct.zero_tmul _ _
  exact this hu

end GlobalTheory.VacUnique

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StdCharFinitePartRationalEqExpTrace
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StdCharFinitePartRationalEqExpTrace
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.LatVac
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdRat

theorem sum_cmType_eq_trace {F E ι : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [Fintype ι] (h2 : Module.finrank F E = 2) (τ : ι → (E →+* ℂ)) (hi : Function.Injective τ)
    (hcm : ∀ σ, (∃ t, τ t = σ) ↔ ¬ ∃ t, τ t = ComplexEmbedding.conjugate σ) (x : F)
    (hx : ∀ σ : E →+* ℂ, ComplexEmbedding.conjugate σ (algebraMap F E x) = σ (algebraMap F E x)) :
    ∑ t, τ t (algebraMap F E x) = ((Algebra.trace ℚ F x : ℚ) : ℂ) := by
  classical
  set y := algebraMap F E x with hy
  have h1 : ((Algebra.trace ℚ E y : ℚ) : ℂ) = ∑ σ : E →+* ℂ, σ y := by
    have := trace_eq_sum_embeddings (K := ℚ) (L := E) ℂ (x := y)
    rw [eq_ratCast] at this
    rw [this]
    exact (Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ) _ _ fun _ => rfl).symm
  have h3 : Algebra.trace ℚ E y = 2 * Algebra.trace ℚ F x := by
    rw [← Algebra.trace_trace (S := F), hy, Algebra.trace_algebraMap, h2, map_nsmul, nsmul_eq_mul]
    rfl
  have hb : Function.Bijective (Sum.elim τ fun t => ComplexEmbedding.conjugate (τ t)) := by
    have hc : ∀ σ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ :=
      fun σ => star_star σ
    constructor
    · rintro (a | a) (b | b) h <;> simp only [Sum.elim_inl, Sum.elim_inr] at h
      · rw [hi h]
      · exact absurd ⟨a, h⟩ ((hcm (τ b)).1 ⟨b, rfl⟩)
      · exact absurd ⟨b, h.symm⟩ ((hcm (τ a)).1 ⟨a, rfl⟩)
      · have := congrArg ComplexEmbedding.conjugate h
        rw [hc, hc] at this
        rw [hi this]
    · intro σ
      by_cases h : ∃ t, τ t = ComplexEmbedding.conjugate σ
      · obtain ⟨t, ht⟩ := h
        exact ⟨Sum.inr t, by simp only [Sum.elim_inr]; rw [ht, hc]⟩
      · obtain ⟨t, ht⟩ := (hcm σ).2 h
        exact ⟨Sum.inl t, ht⟩
  have h4 := hb.sum_comp fun σ : E →+* ℂ => σ y
  rw [Fintype.sum_sum_type, ← h1, h3] at h4
  simp only [Sum.elim_inl, Sum.elim_inr, hx] at h4
  push_cast at h4
  linear_combination h4 / 2

theorem tauE_injective (D : D7) : Function.Injective (tauE D) := fun _ _ h =>
  D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

theorem tauE_cm (D : D7) (σ : D.host.E →+* ℂ) :
    (∃ τ, tauE D τ = σ) ↔ ¬ ∃ τ, tauE D τ = ComplexEmbedding.conjugate σ := by
  obtain ⟨g, rfl⟩ := (factEmb D.R D.host).1.2 σ
  have hc : ComplexEmbedding.conjugate (D.host.emb g) = D.host.emb (g * D.R.cc) := by
    rw [Formalism.L2.Geo.emb_mul_cc_comp]
    refine RingHom.ext fun x => ?_
    have hcm := D.host.isCMField_hostE
    have h : IsCMField.complexConj D.host.E x = D.host.conj x := by
      apply D.host.φ₀.injective
      rw [IsCMField.complexEmbedding_complexConj]
      exact (D.host.toHostAx.conjE_apply _ x).symm
    show starRingEnd ℂ (D.host.emb g x) = D.host.emb g (D.host.conj x)
    rw [← h, IsCMField.complexEmbedding_complexConj]
  have h : ∀ g, (∃ τ, tauE D τ = D.host.emb g) ↔ g ∈ D.R.Psi := fun g => by
    rw [← Formalism.L2.Geo.exists_tauEmb_iff D g]
    exact exists_congr fun τ => eq_comm
  rw [hc, h, h]
  exact Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem g

theorem sum_tauE_eq_trace (D : D7) (x : D.host.F) :
    ∑ t, tauE D t (algebraMap D.host.F D.host.E x) = ((Algebra.trace ℚ D.host.F x : ℚ) : ℂ) := by
  have hcm := D.host.isCMField_hostE
  refine sum_cmType_eq_trace ?_ _ (tauE_injective D) (tauE_cm D) x fun σ => ?_
  · exact Algebra.IsQuadraticExtension.finrank_eq_two _ _
  · show starRingEnd ℂ (σ _) = _
    rw [← IsCMField.complexEmbedding_complexConj]
    exact congrArg σ ((IsCMField.complexConj D.host.E).commutes x)

theorem char_fin_rat {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (h : IsCharAF F ψ) (x : F) :
    ψ (pairA F 0 (algebraMap F (Af F) x)) = psiInf F ψ (algebraMap F (Ainf F) (-x)) := by
  have e : pairA F 0 (algebraMap F (Af F) x) =
      algebraMap F (AF F) x + pairA F (algebraMap F (Ainf F) (-x)) 0 := by
    refine Prod.ext ?_ (add_zero _).symm
    show (0 : Ainf F) = algebraMap F (Ainf F) x + algebraMap F (Ainf F) (-x)
    rw [map_neg, add_neg_cancel]
  rw [e, AddChar.map_add_eq_mul, h.2.2.1, one_mul, psiInf]

theorem tmul_one_eq {F E A : Type} [Field F] [Field E] [CommRing A] [Algebra F E] [Algebra F A] (x : F) :
    (algebraMap F A x) ⊗ₜ[F] (1 : E) = (1 : A) ⊗ₜ[F] (algebraMap F E x) := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

theorem stdChar_fin_rat : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ x : D.host.F, ψ (pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) x)) = Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ D.host.F x : ℚ) : ℂ)) := by
  intro D ψ hψ x
  obtain ⟨θ, hθ⟩ := hψ.2.1
  rw [char_fin_rat ψ hψ.1, hψ.2.2 θ hθ, tmul_one_eq,
    Finset.sum_congr rfl fun ρ _ => (hθ ρ).1 _, sum_tauE_eq_trace, map_neg]
  congr 1
  push_cast
  ring

end GlobalTheory.StdRat

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StdCharFinitePartRationalEqExpTraceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.LatVac
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stdChar_finitePart_rational_eq_exp_trace : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ x : D.host.F, ψ (pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) x)) = Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ D.host.F x : ℚ) : ℂ)) := by
  first | exact @GlobalTheory.StdRat.stdChar_fin_rat | exact GlobalTheory.StdRat.stdChar_fin_rat | (intros; apply GlobalTheory.StdRat.stdChar_fin_rat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousCharacterFiniteOrderIntegralUnits
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousCharacterFiniteOrderIntegralUnits
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CharFin

theorem finite_order_of_small {R A B : Type} [CommRing R] [CommRing A] [CommRing B]
    [TopologicalSpace R] [TopologicalSpace A] [TopologicalSpace B] [ContinuousAdd B]
    (p : R →+* A) (q : R →+* B) (s : A × B → R) (hs : Continuous s) (hsz : ∀ z, s (p z, q z) = z)
    (S : Subring B) (hsmall : ∀ W ∈ 𝓝 (0 : B), ∃ N : ℕ, 0 < N ∧ ∀ y ∈ S, N • y ∈ W)
    (hfin : ∀ N : ℕ, 0 < N → Finite (S ⧸ Ideal.span {(N : S)}))
    (χ : Rˣ →* Circle) (hχ : Continuous χ) :
    ∃ N : ℕ, 0 < N ∧ (∀ x : Rˣ, (p x = 1 ∧ q x ∈ S ∧ q (x⁻¹ : Rˣ) ∈ S) →
      (∃ y ∈ S, q x - 1 = N • y) → χ x = 1) ∧
      ∃ m : ℕ, 0 < m ∧ ∀ x : Rˣ, (p x = 1 ∧ q x ∈ S ∧ q (x⁻¹ : Rˣ) ∈ S) → χ x ^ m = 1 := by
  have hV : χ ⁻¹' Circle.centeredArc (Real.pi / 2) ∈ 𝓝 (1 : Rˣ) := by
    refine ((Circle.isOpen_centeredArc _).preimage hχ).mem_nhds ?_
    rw [Set.mem_preimage, map_one, Circle.mem_centeredArc (by linarith [Real.pi_pos])]
    simp [Real.pi_pos]
  rw [Units.isInducing_embedProduct.nhds_eq_comap, Filter.mem_comap] at hV
  obtain ⟨T, hT, hTV⟩ := hV
  obtain ⟨T1, hT1, T2, hT2, hTT⟩ := mem_nhds_prod_iff.1 hT
  let f : B → R := fun b => s (1, 1 + b)
  have hf : Continuous f := hs.comp (continuous_const.prodMk (continuous_const.add continuous_id))
  have hf0 : f 0 = 1 := by simpa [f] using hsz 1
  have h1 : f ⁻¹' T1 ∈ 𝓝 (0 : B) := hf.continuousAt.preimage_mem_nhds (by rw [hf0]; exact hT1)
  have h2 : (fun b => MulOpposite.op (f b)) ⁻¹' T2 ∈ 𝓝 (0 : B) :=
    (MulOpposite.continuous_op.comp hf).continuousAt.preimage_mem_nhds
      (by rw [Function.comp_apply, hf0]; exact hT2)
  obtain ⟨N, hN, hNW⟩ := hsmall _ (Filter.inter_mem h1 h2)
  have hpinv : ∀ x : Rˣ, p x = 1 → p (x⁻¹ : Rˣ) = 1 := fun x hx => by
    have := congrArg p x.mul_inv
    rwa [map_mul, hx, one_mul, map_one] at this
  let G : Subgroup Rˣ :=
    { carrier := {x | p x = 1 ∧ q x ∈ S ∧ q (x⁻¹ : Rˣ) ∈ S}
      one_mem' := by simp
      mul_mem' := fun {x y} hx hy => by
        refine ⟨by simp [hx.1, hy.1], ?_, ?_⟩
        · rw [Units.val_mul, map_mul]; exact mul_mem hx.2.1 hy.2.1
        · rw [mul_inv, Units.val_mul, map_mul]; exact mul_mem hx.2.2 hy.2.2
      inv_mem' := fun {x} hx => ⟨hpinv x hx.1, hx.2.2, by simpa using hx.2.1⟩ }
  let ψ : G →* S :=
    { toFun := fun x => ⟨q (x : Rˣ), x.2.2.1⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by ext; simp }
  let φ : G →* (S ⧸ Ideal.span {(N : S)})ˣ :=
    ((Ideal.Quotient.mk (Ideal.span {(N : S)})).toMonoidHom.comp ψ).toHomUnits
  have hφ : ∀ x : G, φ x = 1 ↔ ∃ y ∈ S, q (x : Rˣ) - 1 = N • y := by
    intro x
    have : φ x = 1 ↔ Ideal.Quotient.mk (Ideal.span {(N : S)}) (ψ x) = Ideal.Quotient.mk _ 1 := by
      rw [Units.ext_iff]; rfl
    rw [this, Ideal.Quotient.eq, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y, y.2, by simpa [ψ] using congrArg Subtype.val hy⟩
    · rintro ⟨y, hy, h⟩
      exact ⟨⟨y, hy⟩, Subtype.ext (by simpa [ψ] using h)⟩
  have hfx : ∀ x : G, φ x = 1 → ∃ y ∈ S, ((x : Rˣ) : R) = f (N • y) := by
    intro x hx
    obtain ⟨y, hy, h⟩ := (hφ x).1 hx
    refine ⟨y, hy, ?_⟩
    have := hsz (x : Rˣ)
    rw [x.2.1] at this
    simp only [f, ← h, add_sub_cancel, this]
  have harc : ∀ x : G, φ x = 1 → χ x ∈ Circle.centeredArc (Real.pi / 2) := by
    intro x hx
    obtain ⟨y, hy, h⟩ := hfx x hx
    obtain ⟨y', hy', h'⟩ := hfx x⁻¹ (by rw [map_inv, hx, inv_one])
    refine hTV (hTT ⟨?_, ?_⟩)
    · change ((x : Rˣ) : R) ∈ T1
      rw [h]; exact (hNW y hy).1
    · change MulOpposite.op (((x⁻¹ : G) : Rˣ) : R) ∈ T2
      rw [h']; exact (hNW y' hy').2
  have hker : ∀ x : G, φ x = 1 → χ x = 1 := by
    intro x hx
    refine Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two fun n _ => ?_
    have := harc (x ^ n) (by rw [map_pow, hx, one_pow])
    rwa [Subgroup.coe_pow, map_pow] at this
  haveI := hfin N hN
  refine ⟨N, hN, fun x hx h => hker ⟨x, hx⟩ ((hφ _).2 h),
    Nat.card (S ⧸ Ideal.span {(N : S)})ˣ, Nat.card_pos, fun x hx => ?_⟩
  have := hker ((⟨x, hx⟩ : G) ^ Nat.card (S ⧸ Ideal.span {(N : S)})ˣ)
    (by rw [map_pow, pow_card_eq_one'])
  rwa [Subgroup.coe_pow, map_pow] at this

open GlobalTheory.AdLat

section Integral

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

noncomputable def hatRing : Subring (RA F E) where
  toAddSubgroup := hat1 F (Set.range (algebraMap (𝓞 E) E))
  one_mem' := one_tmul_mem_adelicCompletionOfElementSet F ⟨1, map_one _⟩
  mul_mem' := fun hx hy => mul_mem_adelicCompletionOfElementSet_of_mul_mem F
    (by rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩; exact ⟨x * y, map_mul _ _ _⟩) hx hy

theorem exists_int_add_nsmul (N : ℕ) (hN : 0 < N) (z : RA F E)
    (hz : z ∈ hat1 F (Set.range (algebraMap (𝓞 E) E))) :
    ∃ (x : 𝓞 E), ∃ w ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)),
      z = (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (x : E) + N • w := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, _, ⟨x, rfl⟩, rfl⟩ := hz
    obtain ⟨r, b, hb, rfl⟩ := (strong_approximation_mod_nat F N hN).2 a ha
    refine ⟨algebraMap (𝓞 F) (𝓞 E) r * x, _, tmul_mem_adelicCompletion_of_integral F hb ⟨x, rfl⟩, ?_⟩
    rw [TensorProduct.add_tmul, TensorProduct.smul_tmul', Algebra.algebraMap_eq_smul_one (r : F),
      TensorProduct.smul_tmul, Algebra.smul_def]
    rfl
  | zero => exact ⟨0, 0, zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨x, u, hu, rfl⟩ := hx
    obtain ⟨y, w, hw, rfl⟩ := hy
    refine ⟨x + y, u + w, add_mem hu hw, ?_⟩
    rw [show ((x + y : 𝓞 E) : E) = (x : E) + y from rfl, TensorProduct.tmul_add, smul_add]; abel
  | neg x _ hx =>
    obtain ⟨x, u, hu, rfl⟩ := hx
    refine ⟨-x, -u, neg_mem hu, ?_⟩
    rw [show ((-x : 𝓞 E) : E) = -(x : E) from rfl, TensorProduct.tmul_neg, smul_neg]; abel

theorem finite_quotient_hatRing (N : ℕ) (hN : 0 < N) :
    Finite (hatRing F E ⧸ Ideal.span {(N : hatRing F E)}) := by
  let ι : 𝓞 E →+* hatRing F E :=
    ((Algebra.TensorProduct.includeRight (R := F) (A := FiniteAdeleRing (𝓞 F) F)
      (B := E)).toRingHom.comp (algebraMap (𝓞 E) E)).codRestrict _
      fun x => one_tmul_mem_adelicCompletionOfElementSet F ⟨x, rfl⟩
  haveI : Finite (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hN.ne')
  refine Finite.of_surjective (Ideal.quotientMap (I := Ideal.span {(N : 𝓞 E)})
    (Ideal.span {(N : hatRing F E)}) ι ?_) ?_
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    change ι N ∈ Ideal.span {(N : hatRing F E)}
    rw [map_natCast]
    exact Ideal.mem_span_singleton_self _
  · intro z
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨x, w, hw, h⟩ := exists_int_add_nsmul F E N hN z z.2
    refine ⟨Ideal.Quotient.mk _ x, ?_⟩
    rw [Ideal.quotientMap_mk, eq_comm, Ideal.Quotient.eq, Ideal.mem_span_singleton]
    refine ⟨⟨w, hw⟩, Subtype.ext ?_⟩
    change (z : RA F E) - (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (x : E) = ((N : hatRing F E) : RA F E) * w
    rw [h, add_sub_cancel_left, nsmul_eq_mul]
    simp

end Integral

theorem integralFiniteAdeles_eq_adelicCompletion_integers (D : D7) :
    intAE D = hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E)) := by
  unfold intAE hat1
  congr 1
  ext z
  constructor
  · rintro ⟨a, ha, x, rfl⟩
    exact ⟨a, ha, _, ⟨x, rfl⟩, rfl⟩
  · rintro ⟨a, ha, _, ⟨x, rfl⟩, rfl⟩
    exact ⟨a, ha, x, rfl⟩

theorem char_finUnit_finite_order : ∀ (D : D7) (χ : (AE D)ˣ →* Circle), Continuous χ → ∃ N : ℕ, 0 < N ∧ (∀ x, FinUnit x → (∃ y ∈ intAE D, finPart D (x : AE D) - 1 = N • y) → χ x = 1) ∧ ∃ m : ℕ, 0 < m ∧ ∀ x, FinUnit x → χ x ^ m = 1 := by
  intro D χ hχ
  obtain ⟨e, he, -, he'⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  haveI : IsModuleTopology (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (RA D.host.F D.host.E) := ⟨rfl⟩
  haveI : ContinuousAdd (RA D.host.F D.host.E) :=
    IsModuleTopology.toContinuousAdd (FiniteAdeleRing (𝓞 D.host.F) D.host.F) _
  have hsmall := (OpenLat.isOpen_nsmul_hat D.host.F D.host.E 0 ⊤ (by simp)).2
  have := finite_order_of_small (infPart D) (finPart D) e.symm he'
    (fun z => by
      rw [RingEquiv.symm_apply_eq]
      exact Prod.ext (he z).1.symm (he z).2.symm)
    (hatRing D.host.F D.host.E) hsmall (finite_quotient_hatRing D.host.F D.host.E) χ hχ
  unfold FinUnit
  rw [integralFiniteAdeles_eq_adelicCompletion_integers]
  exact this

end GlobalTheory.CharFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousCharacterFiniteOrderIntegralUnitsStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_character_finite_order_integral_units : ∀ (D : D7) (χ : (AE D)ˣ →* Circle), Continuous χ → ∃ N : ℕ, 0 < N ∧ (∀ x, FinUnit x → (∃ y ∈ intAE D, finPart D (x : AE D) - 1 = N • y) → χ x = 1) ∧ ∃ m : ℕ, 0 < m ∧ ∀ x, FinUnit x → χ x ^ m = 1 := by
  first | exact @GlobalTheory.CharFin.char_finUnit_finite_order | exact GlobalTheory.CharFin.char_finUnit_finite_order | (intros; apply GlobalTheory.CharFin.char_finUnit_finite_order <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsOpenCongruenceIdelesAndRealFiniteParts
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsOpenCongruenceIdelesAndRealFiniteParts
noncomputable section

namespace GlobalTheory.IdeleParts

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem isOpen_nsmul_adelicCompletion_integers (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (N : ℕ) (hN : 0 < N) :
    letI : TopologicalSpace (FiniteAdeleRing (𝓞 F) F ⊗[F] E) :=
      moduleTopology (FiniteAdeleRing (𝓞 F) F) (FiniteAdeleRing (𝓞 F) F ⊗[F] E)
    IsOpen {z : GlobalTheory.AdLat.RA F E | ∃ y ∈ GlobalTheory.AdLat.hat1 F (Set.range (algebraMap (𝓞 E) E)), z = N • y} := by
  letI : TopologicalSpace (FiniteAdeleRing (𝓞 F) F ⊗[F] E) :=
      moduleTopology (FiniteAdeleRing (𝓞 F) F) (FiniteAdeleRing (𝓞 F) F ⊗[F] E)
  let L : Submodule (𝓞 E) (Fin 1 → E) :=
    (1 : Submodule (𝓞 E) E).comap (LinearMap.proj (R := 𝓞 E) (φ := fun _ : Fin 1 => E) 0)
  have hL : ∀ x : Fin 1 → E, x ∈ L ↔ x 0 ∈ Set.range (algebraMap (𝓞 E) E) := by
    intro x
    simp only [L, Submodule.mem_comap, Submodule.mem_one, LinearMap.proj_apply, Set.mem_range]
  have hspan : Submodule.span E (L : Set (Fin 1 → E)) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have h1 : (fun _ => (1 : E)) ∈ L := (hL _).2 ⟨1, map_one _⟩
    have : x = x 0 • (fun _ : Fin 1 => (1 : E)) := by
      funext i
      rw [Subsingleton.elim i 0]
      simp
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span h1)
  have ho := (GlobalTheory.AdLat.OpenLat.isOpen_nsmul_hat F E 1 L hspan).1 N hN
  have hc : Continuous (fun z : GlobalTheory.AdLat.RA F E => fun _ : Fin 1 => z) := continuous_pi fun _ => continuous_id
  have h1 : ∀ y ∈ GlobalTheory.AdLat.hat F (L : Set (Fin 1 → E)),
      y 0 ∈ GlobalTheory.AdLat.hat1 F (Set.range (algebraMap (𝓞 E) E)) := by
    intro y hy
    induction hy using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hz
      exact AddSubgroup.subset_closure ⟨a, ha, x 0, (hL x).1 hx, rfl⟩
    | zero => exact zero_mem _
    | add u v _ _ hu hv => exact add_mem hu hv
    | neg u _ hu => exact neg_mem hu
  have h2 : ∀ y ∈ GlobalTheory.AdLat.hat1 F (Set.range (algebraMap (𝓞 E) E)),
      (fun _ : Fin 1 => y) ∈ GlobalTheory.AdLat.hat F (L : Set (Fin 1 → E)) := by
    intro y hy
    induction hy using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hz
      exact AddSubgroup.subset_closure ⟨a, ha, fun _ => x, (hL _).2 hx, rfl⟩
    | zero => exact zero_mem _
    | add u v _ _ hu hv => exact add_mem hu hv
    | neg u _ hu => exact neg_mem hu
  convert ho.preimage hc using 1
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨_, h2 y hy, rfl⟩
  · rintro ⟨y, hy, h⟩
    exact ⟨y 0, h1 y hy, congrFun h 0⟩

theorem integralFiniteAdeles_eq_adelicCompletion_integers (D : D7) :
    intAE D = GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E)) := by
  unfold intAE GlobalTheory.AdLat.hat1
  congr 1
  ext z
  constructor
  · rintro ⟨a, ha, x, rfl⟩
    exact ⟨a, ha, _, ⟨x, rfl⟩, rfl⟩
  · rintro ⟨a, ha, _, ⟨x, rfl⟩, rfl⟩
    exact ⟨a, ha, x, rfl⟩

theorem exists_units_parts {R A B : Type} [Ring R] [Ring A] [Ring B] [TopologicalSpace R] [TopologicalSpace A]
    [TopologicalSpace B] (e : R ≃+* A × B) (hec : Continuous e) (hes : Continuous e.symm)
    (f : R → A) (g : R → B) (he : ∀ z, (e z).1 = f z ∧ (e z).2 = g z) :
    ∃ a b : Rˣ →* Rˣ, Continuous a ∧ Continuous b ∧ (∀ x, x = a x * b x) ∧
      (∀ x, f (a x : R) = f (x : R) ∧ g (a x : R) = 1) ∧ ∀ x, f (b x : R) = 1 ∧ g (b x : R) = g (x : R) := by
  let a0 : R →* R := e.symm.toRingHom.toMonoidHom.comp
    ((MonoidHom.inl _ _).comp ((MonoidHom.fst _ _).comp e.toRingHom.toMonoidHom))
  let b0 : R →* R := e.symm.toRingHom.toMonoidHom.comp
    ((MonoidHom.inr _ _).comp ((MonoidHom.snd _ _).comp e.toRingHom.toMonoidHom))
  have ha0 : ∀ z, a0 z = e.symm ((e z).1, 1) := fun z => rfl
  have hb0 : ∀ z, b0 z = e.symm (1, (e z).2) := fun z => rfl
  have hac : Continuous a0 := by
    rw [show (a0 : R → R) = fun z => e.symm ((e z).1, 1) from funext ha0]
    exact hes.comp ((continuous_fst.comp hec).prodMk continuous_const)
  have hbc : Continuous b0 := by
    rw [show (b0 : R → R) = fun z => e.symm (1, (e z).2) from funext hb0]
    exact hes.comp (continuous_const.prodMk (continuous_snd.comp hec))
  refine ⟨Units.map a0, Units.map b0, Continuous.units_map a0 hac, Continuous.units_map b0 hbc,
    fun x => ?_, fun x => ?_, fun x => ?_⟩
  · apply Units.ext
    rw [Units.val_mul, Units.coe_map, Units.coe_map, ha0, hb0, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
    exact (e.symm_apply_apply _).symm
  · rw [Units.coe_map, ha0, ← (he _).1, ← (he _).2, e.apply_symm_apply]
    exact ⟨(he _).1, rfl⟩
  · rw [Units.coe_map, hb0, ← (he _).1, ← (he _).2, e.apply_symm_apply]
    exact ⟨rfl, (he _).2⟩

theorem congr_open_and_parts : ∀ (D : D7), (∀ N : ℕ, 0 < N → IsOpen {x : (AE D)ˣ | finPart D (x : AE D) ∈ intAE D ∧ finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D ∧ ∃ y ∈ intAE D, finPart D (x : AE D) - 1 = N • y}) ∧ ∃ a b : (AE D)ˣ →* (AE D)ˣ, Continuous a ∧ Continuous b ∧ (∀ x, x = a x * b x) ∧ (∀ x, infPart D (a x : AE D) = infPart D (x : AE D) ∧ finPart D (a x : AE D) = 1) ∧ ∀ x, infPart D (b x : AE D) = 1 ∧ finPart D (b x : AE D) = finPart D (x : AE D) := by
  intro D
  letI tf : TopologicalSpace (Af D.host.F ⊗[D.host.F] D.host.E) :=
    moduleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E)
  letI ti : TopologicalSpace (Ainf D.host.F ⊗[D.host.F] D.host.E) :=
    moduleTopology (Ainf D.host.F) (Ainf D.host.F ⊗[D.host.F] D.host.E)
  obtain ⟨e, he, hec, hes⟩ : ∃ e : AE D ≃+* (Ainf D.host.F ⊗[D.host.F] D.host.E) × (Af D.host.F ⊗[D.host.F] D.host.E),
      (∀ z, (e z).1 = infPart D z ∧ (e z).2 = finPart D z) ∧ Continuous e ∧ Continuous e.symm :=
    GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have hfc : Continuous (finPart D) := by
    have : (finPart D : AE D → _) = fun z => (e z).2 := funext fun z => (he z).2.symm
    rw [this]
    exact continuous_snd.comp hec
  refine ⟨fun N hN => ?_, ?_⟩
  · haveI : IsModuleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
    haveI : ContinuousAdd (Af D.host.F ⊗[D.host.F] D.host.E) :=
      IsModuleTopology.toContinuousAdd (Af D.host.F) _
    have hN' : IsOpen {z : Af D.host.F ⊗[D.host.F] D.host.E | ∃ y ∈ intAE D, z = N • y} := by
      rw [integralFiniteAdeles_eq_adelicCompletion_integers]
      exact isOpen_nsmul_adelicCompletion_integers D.host.F D.host.E N hN
    have h1 : IsOpen {z : Af D.host.F ⊗[D.host.F] D.host.E | z ∈ intAE D} := by
      have := isOpen_nsmul_adelicCompletion_integers D.host.F D.host.E 1 one_pos
      rw [← integralFiniteAdeles_eq_adelicCompletion_integers] at this
      convert this using 1
      ext z
      simp
    have c1 : Continuous fun x : (AE D)ˣ => finPart D (x : AE D) := hfc.comp Units.continuous_val
    have c2 : Continuous fun x : (AE D)ˣ => finPart D ((x⁻¹ : (AE D)ˣ) : AE D) :=
      hfc.comp Units.continuous_coe_inv
    have c3 : Continuous fun x : (AE D)ˣ => finPart D (x : AE D) - 1 := by
      simp only [sub_eq_add_neg]
      exact c1.add continuous_const
    exact (h1.preimage c1).inter ((h1.preimage c2).inter (hN'.preimage c3))
  · exact exists_units_parts e hec hes (infPart D) (finPart D) he

end GlobalTheory.IdeleParts
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsOpenCongruenceIdelesAndRealFinitePartsStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_congruence_ideles_and_real_finite_parts : ∀ (D : D7), (∀ N : ℕ, 0 < N → IsOpen {x : (AE D)ˣ | finPart D (x : AE D) ∈ intAE D ∧ finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D ∧ ∃ y ∈ intAE D, finPart D (x : AE D) - 1 = N • y}) ∧ ∃ a b : (AE D)ˣ →* (AE D)ˣ, Continuous a ∧ Continuous b ∧ (∀ x, x = a x * b x) ∧ (∀ x, infPart D (a x : AE D) = infPart D (x : AE D) ∧ finPart D (a x : AE D) = 1) ∧ ∀ x, infPart D (b x : AE D) = 1 ∧ finPart D (b x : AE D) = finPart D (x : AE D) := by
  first | exact @GlobalTheory.IdeleParts.congr_open_and_parts | exact GlobalTheory.IdeleParts.congr_open_and_parts | (intros; apply GlobalTheory.IdeleParts.congr_open_and_parts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AddCharTrivialIntegralFiniteAdeleMul
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AddCharTrivialIntegralFiniteAdeleMul
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.LatVac
open scoped TensorProduct Topology

namespace GlobalTheory.IntDense

theorem mem_of_isClosed (F : Type) [Field F] [NumberField F] {C : Set (FiniteAdeleRing (𝓞 F) F)}
    (hC : IsClosed C) (h : ∀ a : 𝓞 F, algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F) ∈ C)
    (α : FiniteAdeleRing (𝓞 F) F) (hα : ∀ v, α v ∈ v.adicCompletionIntegers F) : α ∈ C := by
  by_contra hn
  have hc : Continuous fun y : FiniteAdeleRing (𝓞 F) F => α - y := continuous_const.sub continuous_id
  have hU : (fun y : FiniteAdeleRing (𝓞 F) F => α - y) ⁻¹' Cᶜ ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F) :=
    (hC.isOpen_compl.preimage hc).mem_nhds (by simpa using hn)
  obtain ⟨N, hN, hNU⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F _ hU
  obtain ⟨a, β, hβ, e⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat F N hN).2 α hα
  refine hNU β hβ ?_
  change α - N • β ∈ C
  rw [e, add_sub_cancel_right]
  exact h a

theorem addChar_eq_one_of_integral : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), Continuous ψ → ∀ x : F, (∀ a : 𝓞 F, ψ (pairA F 0 (algebraMap F (Af F) ((a : F) * x))) = 1) → ∀ α ∈ intAf F, ψ (pairA F 0 (α * algebraMap F (Af F) x)) = 1 := by
  intro F _ _ ψ hψ x h α hα
  have hp : Continuous fun y : Af F => pairA F 0 (y * algebraMap F (Af F) x) :=
    Continuous.prodMk continuous_const (continuous_id.mul continuous_const)
  refine mem_of_isClosed F (C := {y | ψ (pairA F 0 (y * algebraMap F (Af F) x)) = 1})
    (isClosed_eq (hψ.comp hp) continuous_const) (fun a => ?_) α hα
  have := h a
  rwa [map_mul] at this

end GlobalTheory.IntDense
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AddCharTrivialIntegralFiniteAdeleMulStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.LatVac
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.addChar_trivial_integralFiniteAdele_mul : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), Continuous ψ → ∀ x : F, (∀ a : 𝓞 F, ψ (pairA F 0 (algebraMap F (Af F) ((a : F) * x))) = 1) → ∀ α ∈ intAf F, ψ (pairA F 0 (α * algebraMap F (Af F) x)) = 1 := by
  first | exact @GlobalTheory.IntDense.addChar_eq_one_of_integral | exact GlobalTheory.IntDense.addChar_eq_one_of_integral | (intros; apply GlobalTheory.IntDense.addChar_eq_one_of_integral <;> assumption)
end
end
