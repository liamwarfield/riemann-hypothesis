module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LFixWA
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LFixThA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitarisableOfIsLocCompCusp

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LFixWG
section -- merged from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LFixWF
section -- merged from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LFixWE
noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

open scoped Matrix NNReal TensorProduct
open IsDedekindDomain NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.AdelicU
  GlobalTheory.MixModel GlobalTheory.StdUnn GlobalTheory.Doubling Filter MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Rsw.L.LFixW

variable {D : D7} {n : ℕ}

theorem block_matrix_apply_inl_inl_alt {R : Type} (a b c d : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    blk4 a b c d (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) = a i j := by
  simp only [blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁]

theorem block_matrix_apply_inl_inr_alt {R : Type} (a b c d : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    blk4 a b c d (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr j)) = b i j := by
  simp only [blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₂]

theorem block_matrix_apply_inr_inr_alt {R : Type} (a b c d : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    blk4 a b c d (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inr j)) = d i j := by
  simp only [blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₂]

theorem block_matrix_mul_comm_ring {R : Type} [CommRing R] (a b c d a' b' c' d' : Matrix (Fin n) (Fin n) R) :
    blk4 a b c d * blk4 a' b' c' d' =
      blk4 (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  rw [blk4, blk4, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  rfl

theorem one_ll {R : Type} [Zero R] [One R] (i j : Fin n) :
    (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) =
      (1 : Matrix (Fin n) (Fin n) R) i j := by
  by_cases h : i = j
  · subst h; simp
  · rw [Matrix.one_apply_ne (fun h' => h (Sum.inl_injective (finSumFinEquiv.injective h'))), Matrix.one_apply_ne h]

theorem one_lr {R : Type} [Zero R] [One R] (i j : Fin n) :
    (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr j)) = 0 :=
  Matrix.one_apply_ne fun h => Sum.inl_ne_inr (finSumFinEquiv.injective h)

variable {S : Finset (Pl D)}

theorem offM_of_N {g : G D n} (hg : g ∈ KOff D n S) {b : Mx D n n} (hb : mat g = blk4 1 b 0 1) : OffM S b := by
  intro i j
  have e : b i j = mat g (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr j)) := by rw [hb, block_matrix_apply_inl_inr_alt]
  refine ⟨fun w => ?_, fun v hv => ?_, fun v hv => ?_⟩
  · rw [e, LFixTh.kOff_inf hg, one_lr]
  · rw [e, LFixTh.kOff_at hg hv, one_lr]
  · rw [e]; exact (LFixTh.kOff_int hg hv _ _).1

theorem intS_inner (V : HSp D) {S : Finset (Pl D)} (hQ : ∀ i j, IntS S (rat V.gram i j)) {x : Mx D V.rank n}
    (hx : IntOff S x) (i j : Fin n) : IntS S (GlobalTheory.StdUnn.inner V x x i j) :=
  intS_mul (adj_intS ((intOff_iff x).1 hx)) (intS_mul hQ ((intOff_iff x).1 hx)) i j

theorem fixN (V : HSp D) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) :
    ∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S → ∀ (n : ℕ) (θ : InfFam D) (μ : Measure (Mx D V.rank n))
      (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)) (χ : (AE D)ˣ →* Circle),
      GlobalTheory.StdUnn.IsWeilSch ψ χ θ V μ ω →
      ∀ g ∈ KOff D n S, IsN g → ∀ Ψ : schwartzA θ V.rank n, (∀ x, ¬ IntOff S x → Ψ.1 x = 0) → ω g Ψ = Ψ := by
  classical
  obtain ⟨S₁, hS₁⟩ := psi_off hψ
  obtain ⟨S₂, hS₂⟩ := exists_rat_int V.gram
  refine ⟨S₁ ∪ S₂, fun S hS n θ μ ω χ hω g hg hN Ψ hΨ => ?_⟩
  obtain ⟨b, hb⟩ := hN
  have hQ := hS₂ S (fun v h => hS (Finset.mem_union_right _ h))
  refine Subtype.ext (funext fun x => ?_)
  rw [hω.unip g b hb Ψ x]
  by_cases hx : IntOff S x
  · have h := (hS₁ S (fun v h => hS (Finset.mem_union_left _ h)) _
      (offS_trace (offS_mul_right (offM_of_N hg hb) (intS_inner V hQ hx)))).2
    rw [h, one_mul]
  · rw [hΨ x hx, mul_zero]

end PositivityTheory.Rg.Rsw.L.LFixW

end
end

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

open scoped Matrix NNReal TensorProduct
open IsDedekindDomain NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.AdelicU
  GlobalTheory.MixModel GlobalTheory.StdUnn GlobalTheory.Doubling Filter MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Rsw.L.LFixW

variable {D : D7} {n : ℕ}

def UnitTriv (D : D7) (χ : (AE D)ˣ →* Circle) (S : Finset (Pl D)) : Prop :=
  ∀ u : (AE D)ˣ, (∀ w, compInf D.host.F D.host.E w (u : AE D) = 1) → (∀ v ∈ S, cv D v (u : AE D) = 1) →
    (∀ v ∉ S, cv D v (u : AE D) ∈ intLoc D.host.F D.host.E v ∧
      cv D v ((u⁻¹ : (AE D)ˣ) : AE D) ∈ intLoc D.host.F D.host.E v) → χ u = 1 ∧ absA D u = 1

theorem cA_cA (z : AE D) : cA D (cA D z) = z := by
  have := congrFun (congrFun (adj_adj (D := D) (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => z)) 0) 0
  simpa [adj] using this

theorem det_mem_intLoc {v : Pl D} {M : Matrix (Fin n) (Fin n) (Fv D.host.F v ⊗[D.host.F] D.host.E)}
    (h : ∀ i j, M i j ∈ intLoc D.host.F D.host.E v) : M.det ∈ intLoc D.host.F D.host.E v := by
  let M' : Matrix (Fin n) (Fin n) (intLoc D.host.F D.host.E v) := fun i j => ⟨M i j, h i j⟩
  have h1 := (intLoc D.host.F D.host.E v).subtype.map_det M'
  have e : (intLoc D.host.F D.host.E v).subtype.mapMatrix M' = M := by ext i j; rfl
  rw [e] at h1
  rw [← h1]
  exact (M'.det).2

theorem map_one_entry {R : Type} [CommRing R] (f : AE D →+* R) (k j : Fin n) :
    f ((1 : Mx D n n) k j) = (1 : Matrix (Fin n) (Fin n) R) k j := by
  by_cases h : k = j
  · subst h; simp
  · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h, map_zero]

variable {S : Finset (Pl D)} {e : AE D}

theorem fixM (V : HSp D) {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D}
    {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} (hω : IsWeilSch ψ χ θ V μ ω)
    (he : IsIdem S e) (hU : UnitTriv D χ S) {g : G D n} (hg : g ∈ KOff D n S) (hM : IsM g)
    (Ψ : schwartzA θ V.rank n) (hΨ : Good S e Ψ.1) : ω g Ψ = Ψ := by
  obtain ⟨a, ha⟩ := hM
  have hll : ∀ i j, a.1 i j = mat g (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) := fun i j => by
    rw [ha, block_matrix_apply_inl_inl_alt]
  have hrr : ∀ i j, (a⁻¹).1 i j = cA D (mat g (finSumFinEquiv (Sum.inr j)) (finSumFinEquiv (Sum.inr i))) := fun i j => by
    rw [ha, block_matrix_apply_inr_inr_alt]
    show _ = cA D (cA D ((a⁻¹).1 i j))
    rw [cA_cA]
  have hinf : ∀ w i j, compInf D.host.F D.host.E w (a.1 i j) = (1 : Matrix (Fin n) (Fin n) _) i j := fun w i j => by
    rw [hll, LFixTh.kOff_inf hg, one_ll]
  have hat : ∀ v ∈ S, ∀ i j, cv D v (a.1 i j) = (1 : Matrix (Fin n) (Fin n) _) i j := fun v hv i j => by
    rw [hll, LFixTh.kOff_at hg hv, one_ll]
  have hint : ∀ i j, IntS S (a.1 i j) := fun i j v hv => by rw [hll]; exact (LFixTh.kOff_int hg hv _ _).1
  have hint' : ∀ i j, IntS S ((a⁻¹).1 i j) := fun i j => by
    rw [hrr]
    exact IntS.cA (fun v hv => (LFixTh.kOff_int hg hv _ _).1)
  have hone : ∀ k j, IntS S ((1 : Mx D n n) k j) := fun k j v _ => by
    rw [map_one_entry]
    by_cases h : k = j
    · subst h; rw [Matrix.one_apply_eq]; exact one_mem _
    · rw [Matrix.one_apply_ne h]; exact zero_mem _
  have hoff : ∀ k j, OffS S (a.1 k j - (1 : Mx D n n) k j) := fun k j =>
    ⟨fun w => by rw [RingHom.map_sub, hinf, map_one_entry, sub_self],
      fun v hv => by rw [RingHom.map_sub, hat v hv, map_one_entry, sub_self],
      (hint k j).add (hone k j).neg⟩
  set u := Matrix.GeneralLinearGroup.det a with hudef
  have hu : (u : AE D) = a.1.det := Matrix.GeneralLinearGroup.val_det_apply a
  have hu' : ((u⁻¹ : (AE D)ˣ) : AE D) = (a⁻¹).1.det := by
    rw [hudef, ← map_inv]; exact Matrix.GeneralLinearGroup.val_det_apply _
  have hmap : ∀ {R : Type} [CommRing R] (f : AE D →+* R), (∀ i j, f (a.1 i j) = (1 : Matrix (Fin n) (Fin n) R) i j) →
      f a.1.det = 1 := by
    intro R _ f hf
    rw [RingHom.map_det]
    have : f.mapMatrix a.1 = 1 := by ext i j; exact hf i j
    rw [this, Matrix.det_one]
  obtain ⟨hχu, habs⟩ := hU u (fun w => by rw [hu]; exact hmap _ (hinf w)) (fun v hv => by rw [hu]; exact hmap _ (hat v hv))
    (fun v hv => ⟨by rw [hu, RingHom.map_det]; exact det_mem_intLoc fun i j => hint i j v hv,
      by rw [hu', RingHom.map_det]; exact det_mem_intLoc fun i j => hint' i j v hv⟩)
  have hxa : ∀ x : Mx D V.rank n, IntOff S (x * a.1) ↔ IntOff S x := by
    intro x
    rw [intOff_iff, intOff_iff]
    constructor
    · intro h i j
      have ex : x = (x * a.1) * (a⁻¹).1 := by
        rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
      rw [ex]
      exact intS_mul h hint' i j
    · intro h i j
      exact intS_mul h hint i j
  have hexa : ∀ x : Mx D V.rank n, e • (x * a.1) = e • x := by
    intro x
    ext i j
    rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, Matrix.mul_apply, Finset.mul_sum]
    have : ∀ k, e * (x i k * a.1 k j) = e * (x i k * (1 : Mx D n n) k j) := by
      intro k
      have h0 := idem_mul_offS he (hoff k j)
      linear_combination (x i k) * h0
    simp_rw [this, ← Finset.mul_sum, ← Matrix.mul_apply, Matrix.mul_one]
  refine Subtype.ext (funext fun x => ?_)
  rw [hω.levi g a ha Ψ x]
  change (χ u : ℂ) * npow (absA D u) ((V.rank : ℂ) / 2) * Ψ.1 (x * a.1) = Ψ.1 x
  rw [hχu, habs]
  simp only [npow, NNReal.coe_one, Complex.ofReal_one, Complex.one_cpow, Circle.coe_one, one_mul]
  rw [hΨ (x * a.1), hΨ x, hxa, hexa]

end PositivityTheory.Rg.Rsw.L.LFixW

end
end

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

open scoped Matrix NNReal TensorProduct
open IsDedekindDomain NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.AdelicU
  GlobalTheory.MixModel GlobalTheory.StdUnn GlobalTheory.Doubling Filter MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Rsw.L.LFixW

variable {D : D7} {n : ℕ}

theorem adj_neg_one : adj (-1 : Mx D n n) = -1 := by
  rw [adj_neg]
  congr 1
  ext i j
  by_cases h : i = j
  · subst h; simp [adj]
  · simp [adj, Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h)]

theorem intOff_neg {S : Finset (Pl D)} {a b : ℕ} (x : Mx D a b) : IntOff S (-x) ↔ IntOff S x := by
  rw [intOff_iff, intOff_iff]
  refine ⟨fun h i j => ?_, fun h i j => (h i j).neg⟩
  have := (h i j).neg
  rwa [Matrix.neg_apply, neg_neg] at this

theorem absA_ne (u : (AE D)ˣ) : absA D u ≠ 0 := by
  intro h0
  have := map_mul (absA D) u u⁻¹
  rw [mul_inv_cancel, map_one, h0, zero_mul] at this
  exact zero_ne_one this.symm

theorem npow_ne (r : ℝ≥0) (hr : r ≠ 0) (t : ℂ) : npow r t ≠ 0 := by
  intro h
  have := (Complex.cpow_eq_zero_iff _ _).1 h
  exact hr (by exact_mod_cast this.1)

theorem fixWc (V : HSp D) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) :
    ∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S → ∀ e, IsIdem S e → ∀ (n : ℕ) (θ : InfFam D) (μ : Measure (Mx D V.rank n))
      (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)) (χ : (AE D)ˣ →* Circle), IsWeilSch ψ χ θ V μ ω →
      μ.IsAddHaarMeasure → ∀ w u : G D n, IsW w → IsN u → u ∈ KOff D n S → ∀ Φ : schwartzA θ V.rank n,
        Good S e Φ.1 → ω (w * u * w⁻¹) Φ = Φ := by
  classical
  obtain ⟨S₁, hS₁⟩ := fixN V hψ
  obtain ⟨S₂, hS₂⟩ := ft_supp V.gram (gram_det_ne V) hψ
  refine ⟨S₁ ∪ S₂, fun S hS e he n θ μ ω χ hω hμ w u hw hNu hu Φ hΦ => ?_⟩
  set Φ' := ω (w⁻¹ * w⁻¹) Φ with hΦ'
  have hmw : mat (w * w) = blk4 ((-1 : GL (Fin n) (AE D)) : Mx D n n) 0 0
      (adj (((-1 : GL (Fin n) (AE D))⁻¹ : GL (Fin n) (AE D)) : Mx D n n)) := by
    rw [LFixTh.mat_mul, hw, block_matrix_mul_comm_ring, inv_neg, inv_one, Units.val_neg, Units.val_one, adj_neg_one]
    simp
  set c : ℂ := (χ (Matrix.GeneralLinearGroup.det (-1 : GL (Fin n) (AE D))) : ℂ) *
    npow (absA D (Matrix.GeneralLinearGroup.det (-1 : GL (Fin n) (AE D)))) ((V.rank : ℂ) / 2) with hcdef
  have hc0 : c ≠ 0 := mul_ne_zero (Circle.coe_ne_zero _) (npow_ne _ (absA_ne _) _)
  have hww : ω (w * w) Φ' = Φ := by
    rw [hΦ', ← Module.End.mul_apply, ← map_mul]
    have : w * w * (w⁻¹ * w⁻¹) = 1 := by group
    rw [this, map_one, Module.End.one_apply]
  have hc : ∀ y, Φ.1 y = c * Φ'.1 (-y) := by
    intro y
    have h := hω.levi (w * w) (-1) hmw Φ' y
    rw [hww] at h
    rw [h, Units.val_neg, Units.val_one, Matrix.mul_neg, Matrix.mul_one]
  have hc' : ∀ y, Φ'.1 y = c⁻¹ * Φ.1 (-y) := by
    intro y
    rw [hc (-y), neg_neg, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
  have hgood : Good S e Φ'.1 := by
    refine good_of he (fun y hy => ?_) (fun y z hz => ?_)
    · rw [hc', good_supp hΦ (fun h => hy ((intOff_neg y).1 h)), mul_zero]
    · rw [hc', hc', neg_add, good_shift he hΦ (-y) (z := -z) (fun i j => (hz i j).neg)]
  have hsupp : ∀ x, ¬ IntOff S x → (ω w⁻¹ Φ).1 x = 0 := by
    intro x hx
    have e1 : ω w⁻¹ Φ = ω w Φ' := by
      rw [hΦ', ← Module.End.mul_apply, ← map_mul]
      congr 2
      group
    rw [e1, hω.weyl w hw Φ' x]
    exact hS₂ S (fun v h => hS (Finset.mem_union_right _ h)) e he n μ hμ Φ'.1 hgood x hx
  have hfix := hS₁ S (fun v h => hS (Finset.mem_union_left _ h)) n θ μ ω χ hω u hu hNu (ω w⁻¹ Φ) hsupp
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hfix, ← Module.End.mul_apply, ← map_mul,
    mul_inv_cancel, map_one, Module.End.one_apply]

end PositivityTheory.Rg.Rsw.L.LFixW

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.UnitTriv
section -- merged from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.FinitePartMemIntegralAdeles
noncomputable section

set_option synthInstance.maxHeartbeats 400000

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LFixW.U2

section Gen

theorem tmul_den {F E A : Type} [Field F] [Field E] [Algebra F E] [CommRing A] [Algebra F A] (x : A) {c : F}
    (hc : c ≠ 0) (b : E) : (x * algebraMap F A c⁻¹) ⊗ₜ[F] (c • b) = x ⊗ₜ[F] b := by
  rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_left_comm, ← map_mul,
    mul_inv_cancel₀ hc, map_one, mul_one]

theorem map_smul_basis {F E R R' ι : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R] [CommRing R']
    [Algebra F R'] (φ : R →ₐ[F] R') (b : Module.Basis ι F E) (r : R) (k : ι) :
    Algebra.TensorProduct.map φ (AlgHom.id F E) (r • Algebra.TensorProduct.basis R b k) = φ r ⊗ₜ[F] b k := by
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply]

end Gen

variable {D : D7}

abbrev bA (D : D7) := Algebra.TensorProduct.basis (AF D.host.F) (bE D.host.F D.host.E)

theorem crd_cv (v : Pl D) (z : AE D) (k : Fin (Module.finrank D.host.F D.host.E)) :
    (bV (E := D.host.E) v).repr (cv D v z) k = evFin D.host.F v ((bA D).repr z k) :=
  LIdemEx.repr_map' (evFin D.host.F v) (bE D.host.F D.host.E) z k

theorem finPart_plc_mem (v : Pl D) {t : Fv D.host.F v ⊗[D.host.F] D.host.E} (ht : t ∈ intLoc D.host.F D.host.E v) :
    finPart D (plc D.host.E v t) ∈ intAE D := by
  refine intLoc_induction (p := fun t => finPart D (plc D.host.E v t) ∈ intAE D) (fun a ha x => ?_) (by simp)
    (fun y z hy hz => by rw [LinearMap.map_add (f := _), RingHom.map_add (f := _)]; exact add_mem hy hz)
    (fun y hy => by rw [LinearMap.map_neg, RingHom.map_neg]; exact neg_mem hy) ht
  rw [plc_tmul]
  refine AddSubgroup.subset_closure ⟨(iV v a).2, fun w => ?_, x, rfl⟩
  by_cases h : w = v
  · subst h
    show (iV w a).2 w ∈ _
    rw [show (iV w a).2 w = a from GlobalTheory.CompanionTheory.PsiCondLoc.single_self w a]
    exact ha
  · show (iV v a).2 w ∈ _
    rw [show (iV v a).2 w = 0 from GlobalTheory.CompanionTheory.PsiCondLoc.single_ne v a h]
    exact zero_mem _

theorem finPart_mem_of_good {z : AE D} (hb : ∀ v, ¬ IsGood D.host.F D.host.E v → cv D v z = 0)
    (hz : ∀ v, cv D v z ∈ intLoc D.host.F D.host.E v) : finPart D z ∈ intAE D := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← (bA D).sum_repr z, map_sum]
  refine sum_mem fun k _ => ?_
  have hN : (den (bE D.host.F D.host.E k) : D.host.F) ≠ 0 := by exact_mod_cast den_ne (bE D.host.F D.host.E k)
  let o : 𝓞 D.host.E := ⟨(den (bE D.host.F D.host.E k) : D.host.E) * bE D.host.F D.host.E k, den_int _⟩
  have ho : (o : D.host.E) = (den (bE D.host.F D.host.E k) : D.host.F) • bE D.host.F D.host.E k := by
    rw [Algebra.smul_def, map_intCast]
    rfl
  have e1 : finPart D ((bA D).repr z k • (bA D) k) =
      sndA D.host.F ((bA D).repr z k) ⊗ₜ[D.host.F] bE D.host.F D.host.E k :=
    map_smul_basis (sndA D.host.F) (bE D.host.F D.host.E) _ k
  rw [e1]
  refine AddSubgroup.subset_closure ⟨sndA D.host.F ((bA D).repr z k) *
    algebraMap D.host.F (Af D.host.F) ((den (bE D.host.F D.host.E k) : D.host.F))⁻¹, fun v => ?_, o,
    by rw [ho]; exact (tmul_den _ hN _).symm⟩
  show evalV D.host.F v (sndA D.host.F ((bA D).repr z k) * algebraMap D.host.F (Af D.host.F) _) ∈ _
  rw [map_mul, AlgHom.commutes]
  have hc : evalV D.host.F v (sndA D.host.F ((bA D).repr z k)) = (bV (E := D.host.E) v).repr (cv D v z) k :=
    (crd_cv v z k).symm
  rw [hc]
  by_cases hv : IsGood D.host.F D.host.E v
  · exact mul_mem ((mem_intLoc_iff hv _).1 (hz v) k) (hv.deninv k)
  · rw [hb v hv, map_zero, Finsupp.zero_apply, zero_mul]
    exact zero_mem _

open Classical in
theorem cv_sub_plc (z : AE D) (B : Finset (Pl D)) (z' : AE D) (hz' : z' = z - ∑ v ∈ B, plc D.host.E v (cv D v z))
    (w : Pl D) : cv D w z' = if w ∈ B then 0 else cv D w z := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hz', RingHom.map_sub, map_sum]
  by_cases hw : w ∈ B
  · rw [if_pos hw, Finset.sum_eq_single w (fun v _ hv => compFin_plc_ne (Ne.symm hv) _) (fun h => absurd hw h),
      compFin_plc_self, sub_self]
  · rw [if_neg hw, Finset.sum_eq_zero (fun v hv => compFin_plc_ne (fun h => hw (by rw [h]; exact hv)) _), sub_zero]

open Classical in
theorem finite_part_mem_integral_adeles (z z' : AE D) (hz : ∀ v, cv D v z ∈ intLoc D.host.F D.host.E v)
    (hfin : {x | ¬IsGood D.host.F D.host.E x}.Finite) (B : Finset (Pl D)) (hB : B = hfin.toFinset)
    (hcv : ∀ w, cv D w z' = if w ∈ B then 0 else cv D w z) : finPart D z' ∈ intAE D := by
  refine finPart_mem_of_good (fun v hv => ?_) (fun v => ?_)
  · rw [hcv, if_pos (by rw [hB]; exact (Set.Finite.mem_toFinset hfin).2 hv)]
  · rw [hcv]
    split_ifs
    · exact zero_mem _
    · exact hz v

theorem finPart_mem (z : AE D) (hz : ∀ v, cv D v z ∈ intLoc D.host.F D.host.E v) : finPart D z ∈ intAE D := by
  have hfin : {x | ¬IsGood D.host.F D.host.E x}.Finite :=
    Filter.eventually_cofinite.1 (eventually_good (F := D.host.F) (E := D.host.E))
  have h1 := finite_part_mem_integral_adeles z _ hz hfin _ rfl (cv_sub_plc z hfin.toFinset _ rfl)
  have e : z = (z - ∑ v ∈ hfin.toFinset, plc D.host.E v (cv D v z)) + ∑ v ∈ hfin.toFinset, plc D.host.E v (cv D v z) :=
    (sub_add_cancel _ _).symm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, RingHom.map_add (f := _), map_sum]
  exact add_mem h1 (sum_mem fun v _ => finPart_plc_mem v (hz v))

theorem infPart_eq_one {z : AE D} (h : ∀ w, compInf D.host.F D.host.E w z = 1) : infPart D z = 1 := by
  let bI := Algebra.TensorProduct.basis (Ainf D.host.F) (bE D.host.F D.host.E)
  apply bI.repr.injective
  refine Finsupp.ext fun k => ?_
  have h1 := LIdemEx.repr_map' (fstA D.host.F) (bE D.host.F D.host.E) z k
  have h2 := LIdemEx.repr_map' (fstA D.host.F) (bE D.host.F D.host.E) (1 : AE D) k
  have e1 : infPart D z = Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) z := rfl
  have e2 : (1 : Ainf D.host.F ⊗[D.host.F] D.host.E) =
      Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) (1 : AE D) := (map_one _).symm
  rw [e1, e2, h1, h2]
  funext w
  have g1 := LIdemEx.repr_map' (evInf D.host.F w) (bE D.host.F D.host.E) z k
  have g2 := LIdemEx.repr_map' (evInf D.host.F w) (bE D.host.F D.host.E) (1 : AE D) k
  have hz : Algebra.TensorProduct.map (evInf D.host.F w) (AlgHom.id D.host.F D.host.E) z =
      Algebra.TensorProduct.map (evInf D.host.F w) (AlgHom.id D.host.F D.host.E) 1 := by
    rw [map_one]; exact h w
  rw [hz] at g1
  exact g1.symm.trans g2

end PositivityTheory.Rg.Rsw.L.LFixW.U2

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.NatCastMulGen
noncomputable section

set_option synthInstance.maxHeartbeats 400000

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LFixW.U2

variable {D : D7}

theorem norm_mem {v : Pl D} (hv : IsGood D.host.F D.host.E v) {x : Fv D.host.F v ⊗[D.host.F] D.host.E}
    (hx : x ∈ intLoc D.host.F D.host.E v) :
    Algebra.norm (Fv D.host.F v) x ∈ v.adicCompletionIntegers D.host.F := by
  classical
  rw [Algebra.norm_eq_matrix_det (bV (E := D.host.E) v), Matrix.det_apply]
  have hM : ∀ i j, Algebra.leftMulMatrix (bV (E := D.host.E) v) x i j ∈ v.adicCompletionIntegers D.host.F := by
    intro i j
    rw [Algebra.leftMulMatrix_eq_repr_mul]
    have hb : bV (E := D.host.E) v j ∈ intLoc D.host.F D.host.E v := by
      rw [bV_apply]; exact one_tmul_b_mem hv j
    exact (mem_intLoc_iff hv _).1 (mul_mem hx hb) i
  refine sum_mem fun σ _ => ?_
  rw [Units.smul_def]
  exact zsmul_mem (prod_mem fun i _ => hM _ _) _

theorem absEv_eq_one {v : Pl D} (hv : IsGood D.host.F D.host.E v) (x : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ)
    (h1 : (x : Fv D.host.F v ⊗[D.host.F] D.host.E) ∈ intLoc D.host.F D.host.E v)
    (h2 : ((x⁻¹ : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ) : Fv D.host.F v ⊗[D.host.F] D.host.E) ∈
      intLoc D.host.F D.host.E v) :
    absEv D.host.F D.host.E v x = 1 := by
  have k : ∀ y : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ, (y : Fv D.host.F v ⊗[D.host.F] D.host.E) ∈
      intLoc D.host.F D.host.E v → absEv D.host.F D.host.E v y ≤ 1 := fun y hy => by
    rw [absEv_apply]
    exact_mod_cast Valued.toNormedField.norm_le_one_iff.2 (norm_mem hv hy)
  have a1 := k x h1
  have a2 := k _ h2
  have hm : absEv D.host.F D.host.E v x * absEv D.host.F D.host.E v x⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  refine le_antisymm a1 ?_
  calc (1 : ℝ≥0) = absEv D.host.F D.host.E v x * absEv D.host.F D.host.E v x⁻¹ := hm.symm
    _ ≤ absEv D.host.F D.host.E v x * 1 := mul_le_mul_of_nonneg_left a2 (by positivity)
    _ = absEv D.host.F D.host.E v x := mul_one _

def cN (D : D7) (N : ℕ) : AE D := algebraMap D.host.F (AF D.host.F) ((N : D.host.F)⁻¹) ⊗ₜ[D.host.F] (1 : D.host.E)

theorem cv_cN (v : Pl D) (N : ℕ) :
    cv D v (cN D N) = algebraMap D.host.F (Fv D.host.F v) ((N : D.host.F)⁻¹) ⊗ₜ[D.host.F] (1 : D.host.E) := by
  show evFin D.host.F v (algebraMap D.host.F (AF D.host.F) _) ⊗ₜ[D.host.F] (1 : D.host.E) = _
  rw [AlgHom.commutes]

theorem natCast_mul_gen {F E A : Type} [Field F] [Field E] [Algebra F E] [CommRing A] [Algebra F A] {N : ℕ}
    (hN : (N : F) ≠ 0) : (N : A ⊗[F] E) * (algebraMap F A ((N : F)⁻¹) ⊗ₜ[F] (1 : E)) = 1 := by
  rw [(map_natCast (Algebra.TensorProduct.includeLeftRingHom (R := F) (A := A) (B := E)) N).symm]
  show ((N : A) ⊗ₜ[F] (1 : E)) * _ = 1
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← map_natCast (algebraMap F A) N, ← map_mul,
    mul_inv_cancel₀ hN, map_one]
  rfl

theorem natCast_mul_cN {N : ℕ} (hN : 0 < N) : (N : AE D) * cN D N = 1 :=
  natCast_mul_gen (by exact_mod_cast hN.ne')

end PositivityTheory.Rg.Rsw.L.LFixW.U2

end
end

noncomputable section

set_option synthInstance.maxHeartbeats 400000

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LFixW


set_option maxHeartbeats 1000000 in
open U2 in
theorem unit_triv (D : D7) (χ : (AE D)ˣ →* Circle) (hχ : IsHeckeChar D χ) : ∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S →
    ∀ u : (AE D)ˣ, (∀ w, compInf D.host.F D.host.E w (u : AE D) = 1) → (∀ v ∈ S, cv D v (u : AE D) = 1) →
    (∀ v ∉ S, cv D v (u : AE D) ∈ intLoc D.host.F D.host.E v ∧
      cv D v ((u⁻¹ : (AE D)ˣ) : AE D) ∈ intLoc D.host.F D.host.E v) →
    χ u = 1 ∧ absA D u = 1 := by
  obtain ⟨N, hN, hker, -⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D χ hχ.1
  have hbad : {v : Pl D | ¬ (IsGood D.host.F D.host.E v ∧
      algebraMap D.host.F (Fv D.host.F v) ((N : D.host.F)⁻¹) ∈ v.adicCompletionIntegers D.host.F)}.Finite :=
    Filter.eventually_cofinite.1 ((eventually_good (F := D.host.F) (E := D.host.E)).and
      (eventually_int (F := D.host.F) ((N : D.host.F)⁻¹)))
  refine ⟨hbad.toFinset, fun S hS u hinf hSv hoff => ?_⟩
  have hgood : ∀ v ∉ S, IsGood D.host.F D.host.E v ∧
      algebraMap D.host.F (Fv D.host.F v) ((N : D.host.F)⁻¹) ∈ v.adicCompletionIntegers D.host.F := by
    intro v hv
    by_contra h
    exact hv (hS ((Set.Finite.mem_toFinset hbad).2 h))
  have hinv : ∀ v ∈ S, cv D v ((u⁻¹ : (AE D)ˣ) : AE D) = 1 := by
    intro v hv
    have := congrArg (cv D v) u.inv_mul
    rw [RingHom.map_mul, RingHom.map_one, hSv v hv, mul_one] at this
    exact this
  have hint : ∀ z : AE D, (∀ v ∈ S, cv D v z ∈ intLoc D.host.F D.host.E v) →
      (∀ v ∉ S, cv D v z ∈ intLoc D.host.F D.host.E v) → finPart D z ∈ intAE D := by
    intro z h1 h2
    refine finPart_mem z fun v => ?_
    by_cases hv : v ∈ S
    · exact h1 v hv
    · exact h2 v hv
  have hfu : FinUnit u := ⟨infPart_eq_one hinf,
    hint _ (fun v hv => by rw [hSv v hv]; exact one_mem _) (fun v hv => (hoff v hv).1),
    hint _ (fun v hv => by rw [hinv v hv]; exact one_mem _) (fun v hv => (hoff v hv).2)⟩
  have hy1 : ∀ v ∈ S, cv D v (cN D N * ((u : AE D) - 1)) ∈ intLoc D.host.F D.host.E v := by
    intro v hv
    rw [RingHom.map_mul, RingHom.map_sub, hSv v hv, RingHom.map_one, sub_self, mul_zero]
    exact zero_mem _
  have hy2 : ∀ v ∉ S, cv D v (cN D N * ((u : AE D) - 1)) ∈ intLoc D.host.F D.host.E v := by
    intro v hv
    rw [RingHom.map_mul, RingHom.map_sub, RingHom.map_one]
    have ha : cv D v (cN D N) ∈ intLoc D.host.F D.host.E v := by
      rw [cv_cN]
      exact tmul_one_mem (E := D.host.E) (hgood v hv).2
    have hb : cv D v (u : AE D) - 1 ∈ intLoc D.host.F D.host.E v :=
      (intLoc D.host.F D.host.E v).sub_mem (hoff v hv).1 (intLoc D.host.F D.host.E v).one_mem
    exact (intLoc D.host.F D.host.E v).mul_mem ha hb
  have hy3 : finPart D (u : AE D) - 1 = N • finPart D (cN D N * ((u : AE D) - 1)) := by
    rw [nsmul_eq_mul, ← map_natCast (finPart D) N, ← RingHom.map_mul, ← mul_assoc, natCast_mul_cN hN, one_mul,
      RingHom.map_sub, RingHom.map_one]
  refine ⟨hker u hfu ⟨_, hint _ hy1 hy2, hy3⟩, ?_⟩
  show absE D.host.F D.host.E u = 1
  rw [absE_apply]
  have h1 : ∀ w, absEw D.host.F D.host.E w (unitInf D.host.F D.host.E w u) = 1 := fun w => by
    rw [show unitInf D.host.F D.host.E w u = 1 from Units.ext (hinf w), map_one]
  have h2 : ∀ v, absEv D.host.F D.host.E v (unitFin D.host.F D.host.E v u) = 1 := by
    intro v
    by_cases hv : v ∈ S
    · rw [show unitFin D.host.F D.host.E v u = 1 from Units.ext (hSv v hv), map_one]
    · exact absEv_eq_one (hgood v hv).1 _ (hoff v hv).1 (hoff v hv).2
  rw [Finset.prod_eq_one fun w _ => h1 w, finprod_congr h2, finprod_one, one_mul]

end PositivityTheory.Rg.Rsw.L.LFixW

end
end

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L

theorem fixW : IdemEx → GenK → WMaj → FixW := by
  classical
  intro _ hG hWM D n V ψ hψ χ hχ hres θ hθ μ hμ ω hω
  have hHaar : μ.IsAddHaarMeasure := by
    obtain ⟨_, h, -⟩ := hμ
    exact h
  obtain ⟨S1, hS1⟩ := LFixW.fixN V hψ
  obtain ⟨S2, hS2⟩ := LFixW.fixWc V hψ
  obtain ⟨S3, hS3⟩ := LFixW.unit_triv D χ hχ
  obtain ⟨S4, hS4⟩ := hG D n
  refine ⟨S1 ∪ S2 ∪ S3 ∪ S4, fun S hS e he Φ hΦ u hu => ?_⟩
  have h1 : S1 ⊆ S := fun x hx => hS (by simp [hx])
  have h2 : S2 ⊆ S := fun x hx => hS (by simp [hx])
  have h3 : S3 ⊆ S := fun x hx => hS (by simp [hx])
  have h4 : S4 ⊆ S := fun x hx => hS (by simp [hx])
  have hcont := (hWM D n V ψ hψ χ hχ hres θ hθ μ hμ ω hω Φ).1
  have hA : IsClosed {g : G D n | ω g Φ = Φ} := by
    have hEq : {g : G D n | ω g Φ = Φ} = ⋂ x, {g : G D n | (ω g Φ).1 x = Φ.1 x} := by
      ext g
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      constructor
      · intro h x
        rw [h]
      · intro h
        exact Subtype.ext (funext h)
    rw [hEq]
    exact isClosed_iInter fun x =>
      isClosed_eq (hcont.comp (continuous_id.prodMk continuous_const)) continuous_const
  have h1A : (1 : G D n) ∈ {g : G D n | ω g Φ = Φ} := by
    show ω 1 Φ = Φ
    rw [map_one]
    rfl
  have key := hS4 S h4 {g : G D n | ω g Φ = Φ} hA h1A (by
    intro g hg hcases x hx
    have hx' : ω x Φ = Φ := hx
    show ω (g * x) Φ = Φ
    rw [map_mul]
    show ω g (ω x Φ) = Φ
    rw [hx']
    rcases hcases with hN | hM | ⟨w, u', hw, hu', hu'K, rfl⟩
    · exact hS1 S h1 n θ μ ω χ hω g hg hN Φ (fun y hy => by rw [hΦ y, if_neg hy])
    · exact LFixW.fixM V hω he (hS3 S h3) hg hM Φ hΦ
    · exact hS2 S h2 e he n θ μ ω χ hω hHaar w u' hw hu' hu'K Φ hΦ)
  exact key hu

end PositivityTheory.Rg.Rsw.L

end
