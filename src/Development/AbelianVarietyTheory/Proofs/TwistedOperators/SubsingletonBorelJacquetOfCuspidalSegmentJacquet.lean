module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsingletonBorelJacquetOfCuspidalSegmentJacquet
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsingletonBorelJacquetOfCuspidalSegmentJacquet
open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel
open scoped TensorProduct

namespace GlobalTheory.SmGL.CuspSegment

def intervals (l d : ℕ) : (Σ _ : Fin l, Fin d) ≃ Fin (l * d) :=
  (Equiv.sigmaEquivProd _ _).trans finProdFinEquiv

theorem intervals_lt {l d : ℕ} {a b : Fin l} {i j : Fin d}
    (h : intervals l d ⟨a, i⟩ < intervals l d ⟨b, j⟩) : a < b ∨ (a = b ∧ i < j) := by
  have key : (i : ℕ) + d * a < j + d * b := by
    simpa [intervals, finProdFinEquiv, Fin.lt_def] using h
  rcases lt_trichotomy a b with hab | rfl | hab
  · exact Or.inl hab
  · exact Or.inr ⟨rfl, Fin.lt_def.2 (by omega)⟩
  · exfalso
    have h1 : (b : ℕ) + 1 ≤ a := hab
    have h2 : d * ((b : ℕ) + 1) ≤ d * a := Nat.mul_le_mul_left d h1
    have hj := j.isLt
    rw [Nat.mul_succ] at h2
    omega

variable {R : Type} [CommRing R]

theorem unipRad_intervals_le (l d : ℕ) : unipRad R (intervals l d) ≤ unipB R (Fin (l * d)) := by
  intro g hg
  obtain ⟨hpar, hdiag⟩ := mem_unipRad.1 hg
  rw [mem_parab] at hpar
  rw [mem_unipB]
  refine ⟨fun p q hqp => ?_, fun p => ?_⟩
  · obtain ⟨⟨a, i⟩, rfl⟩ := (intervals l d).surjective p
    obtain ⟨⟨b, j⟩, rfl⟩ := (intervals l d).surjective q
    rcases intervals_lt hqp with hba | ⟨rfl, hji⟩
    · exact hpar _ _ (by simpa using hba)
    · rw [hdiag]
      exact Matrix.one_apply_ne hji.ne'
  · obtain ⟨⟨a, i⟩, rfl⟩ := (intervals l d).surjective p
    rw [hdiag]
    exact Matrix.one_apply_eq i

theorem leviEmb_intervals_mem {l d : ℕ} (g : Levi R fun _ : Fin l => Fin d)
    (hg : ∀ a, g a ∈ unipB R (Fin d)) : leviEmb R (intervals l d) g ∈ unipB R (Fin (l * d)) := by
  rw [mem_unipB]
  refine ⟨fun p q hqp => ?_, fun p => ?_⟩
  · obtain ⟨⟨a, i⟩, rfl⟩ := (intervals l d).surjective p
    obtain ⟨⟨b, j⟩, rfl⟩ := (intervals l d).surjective q
    rcases intervals_lt hqp with hba | ⟨rfl, hji⟩
    · exact leviEmb_apply_ne _ _ _ hba.ne' _ _
    · rw [leviEmb_apply_same]
      exact ((mem_unipB (R := R)).1 (hg b)).1 i j hji
  · obtain ⟨⟨a, i⟩, rfl⟩ := (intervals l d).surjective p
    rw [leviEmb_apply_same]
    exact ((mem_unipB (R := R)).1 (hg a)).2 i

theorem twKer_unipB_eq_top {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {d : ℕ} (hd : 1 < d) {W : Type} [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ (GL (Fin d) k) W} (hσ : IsCuspidal σ) :
    twKer σ (unipB k (Fin d)) 1 = ⊤ := by
  classical
  obtain ⟨-, hcusp⟩ := hσ

  let e : (Σ _ : Fin d, Fin 1) ≃ Fin d := Equiv.sigmaUnique (Fin d) fun _ => Fin 1
  have hblk : ∀ i, blk e i = i := fun i => rfl
  have hne : unipRad k e ≠ ⊥ := by
    rw [CuspMax.unipRad_ne_bot_iff]
    refine ⟨⟨0, by omega⟩, ⟨1, hd⟩, ?_⟩
    rw [hblk, hblk]
    exact Fin.mk_lt_mk.2 Nat.zero_lt_one
  have hsub : Subsingleton (Jacquet σ (unipRad k e)) := hcusp d (fun _ => 1) e hne
  have hB : Subsingleton (Jacquet σ (unipRad k (points (Fin d)))) :=
    CuspMax.subsingleton_jacquet_of_perm σ (e := e) (e' := points (Fin d)) (Equiv.refl _)
      (fun i j h => h) hsub
  exact Submodule.Quotient.subsingleton_iff.1 hB

private theorem deltaHalf_eq_one_of_unipB {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {l d : ℕ} (g : Levi k fun _ : Fin l => Fin d)
    (hg : ∀ a, g a ∈ unipB k (Fin d)) : deltaHalf k (fun _ : Fin l => Fin d) g = 1 := by
  rw [deltaHalf_apply]
  refine Finset.prod_eq_one fun a _ => ?_
  rw [det_eq_one_of_mem_unipRad (hu := (show g a ∈ unipRad k (points (Fin d)) from hg a)), map_one]

theorem subsingleton_jacquet_unipB (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (l d : ℕ) (hl : 0 < l) (hd : 1 < d) (V : Type) [AddCommGroup V]
    [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin d) k) W)
    (π : Representation ℂ (GL (Fin (l * d)) k) V) (hσ : IsCuspidal σ)
    (h : ∀ e : (Σ _ : Fin l, Fin d) ≃ Fin (l * d),
      Nonempty ((jac e π).Equiv (piTensor (segTerm σ l)))) :
    Subsingleton (Jacquet π (unipB k (Fin (l * d)))) := by
  classical
  obtain ⟨φ⟩ := h (intervals l d)
  obtain ⟨a₀⟩ : Nonempty (Fin l) := ⟨⟨0, hl⟩⟩
  set K := twKer π (unipB k (Fin (l * d))) 1 with hK

  have hgen : ∀ u ∈ unipB k (Fin (l * d)), ∀ v : V, π u v - v ∈ K := by
    intro u hu v
    exact Submodule.subset_span ⟨⟨u, hu⟩, v, by simp⟩

  have hUK : twKer π (unipRad k (intervals l d)) 1 ≤ K := by
    refine Submodule.span_le.2 ?_
    rintro w ⟨n, v, rfl⟩
    simpa using hgen n (unipRad_intervals_le l d n.2) v
  let P := Submodule.factor hUK
  have hP : ∀ v : V, P (Submodule.Quotient.mk v) = Submodule.Quotient.mk v := fun v =>
    Submodule.factor_mk hUK v

  have hlevi : ∀ g : Levi k (fun _ : Fin l => Fin d), (∀ a, g a ∈ unipB k (Fin d)) →
      ∀ q, P (jac (intervals l d) π g q) = P q := by
    intro g hg q
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [jac_mk, deltaHalf_eq_one_of_unipB g hg, inv_one, Units.val_one, one_smul, hP, hP]
    exact (Submodule.Quotient.eq _).2 (hgen _ (leviEmb_intervals_mem g hg) v)

  have hfwd : ∀ g z, φ (jac (intervals l d) π g z) = piTensor (segTerm σ l) g (φ z) := by
    intro g z
    have := LinearMap.congr_fun (φ.isIntertwining' g) z
    simpa using this
  have hint : ∀ g y, φ.symm (piTensor (segTerm σ l) g y) = jac (intervals l d) π g (φ.symm y) := by
    intro g y
    apply EquivLike.injective φ
    rw [hfwd, Representation.Equiv.apply_symm_apply, Representation.Equiv.apply_symm_apply]
  let F : (⨂[ℂ] _ : Fin l, W) →ₗ[ℂ] V ⧸ K := P ∘ₗ φ.symm.toLinearMap
  have hFapp : ∀ y, F y = P (φ.symm y) := fun y => rfl
  have hF : ∀ g : Levi k (fun _ : Fin l => Fin d), (∀ a, g a ∈ unipB k (Fin d)) →
      ∀ y, F (piTensor (segTerm σ l) g y) = F y := by
    intro g hg y
    rw [hFapp, hFapp, hint]
    exact hlevi g hg _

  have htop : twKer (segTerm σ l a₀) (unipB k (Fin d)) 1 = ⊤ :=
    twKer_unipB_eq_top hd (LocGL.isCuspidal_twist hσ (LocGL.isSmoothChar_absPow _))
  have htens : ∀ x : Fin l → W, F (PiTensorProduct.tprod ℂ x) = 0 := by
    intro x
    let Lx := (PiTensorProduct.tprod ℂ).toLinearMap x a₀
    have hker : twKer (segTerm σ l a₀) (unipB k (Fin d)) 1 ≤ LinearMap.ker (F ∘ₗ Lx) := by
      refine Submodule.span_le.2 ?_
      rintro w ⟨u, v, rfl⟩
      have hg : ∀ a, (Pi.mulSingle a₀ (u : GL (Fin d) k) : Levi k fun _ : Fin l => Fin d) a ∈
          unipB k (Fin d) := by
        intro a
        by_cases ha : a = a₀
        · rw [ha, Pi.mulSingle_eq_same]
          exact u.2
        · rw [Pi.mulSingle_eq_of_ne ha]
          exact one_mem _
      have hact : Lx (segTerm σ l a₀ u v) =
          piTensor (segTerm σ l) (Pi.mulSingle a₀ (u : GL (Fin d) k)) (Lx v) := by
        simp only [Lx, MultilinearMap.toLinearMap_apply, piTensor_tprod]
        congr 1
        funext a
        by_cases ha : a = a₀
        · rw [ha]
          simp
        · simp [ha]
      simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.comp_apply, MonoidHom.one_apply,
        Units.val_one, one_smul, map_sub, hact, hF _ hg, sub_self]
    have hx : Lx (x a₀) = PiTensorProduct.tprod ℂ x := by
      simp [Lx]
    rw [← hx]
    exact LinearMap.mem_ker.1 (hker (by rw [htop]; exact Submodule.mem_top))
  have hF0 : F = 0 := PiTensorProduct.ext (MultilinearMap.ext fun x => by simpa using htens x)

  have hv : ∀ v : V, (Submodule.Quotient.mk v : V ⧸ K) = 0 := by
    intro v
    rw [← hP v]
    have hPF : P (Submodule.Quotient.mk v) = F (φ (Submodule.Quotient.mk v)) := by
      rw [hFapp, Representation.Equiv.symm_apply_apply]
    rw [hPF, hF0, LinearMap.zero_apply]
  refine ⟨fun a b => ?_⟩
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  exact (hv v).trans (hv w).symm

end GlobalTheory.SmGL.CuspSegment
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsingletonBorelJacquetOfCuspidalSegmentJacquetStatement
open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subsingleton_borelJacquet_of_cuspidal_segment_jacquet : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (l d : ℕ), 0 < l → 1 < d → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin d) k) W) (π : Representation ℂ (GL (Fin (l * d)) k) V), IsCuspidal σ → (∀ e : (Σ _ : Fin l, Fin d) ≃ Fin (l * d), Nonempty ((jac e π).Equiv (piTensor (segTerm σ l)))) → Subsingleton (Jacquet π (unipB k (Fin (l * d)))) := by
  first | exact @GlobalTheory.SmGL.CuspSegment.subsingleton_jacquet_unipB | exact GlobalTheory.SmGL.CuspSegment.subsingleton_jacquet_unipB | (intros; apply GlobalTheory.SmGL.CuspSegment.subsingleton_jacquet_unipB <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelInvariantFormUpperTriangularPairAction
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryBorelPreservesMixedModelLatticeLowerBlock
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryBorelPreservesMixedModelLatticeLowerBlock
open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SphTheta.MixStab

variable {L : Type} [Field L]

theorem sum_hi {M : Type} [AddCommMonoid M] (N : ℕ) (f : Fin N → M)
    (hf : ∀ i : Fin N, i.1 < N - N / 2 → f i = 0) : ∑ i, f i = ∑ k, f (hi N k) := by
  rw [← Finset.sum_image (s := Finset.univ) (g := hi N) (f := f)]
  · symm
    refine Finset.sum_subset (Finset.subset_univ _) fun i _ hni => hf i ?_
    by_contra hc
    have := i.isLt
    exact hni (Finset.mem_image.2 ⟨⟨i.1 - (N - N / 2), by omega⟩, Finset.mem_univ _, Fin.ext (by simp only [hi]; omega)⟩)
  · intro x _ y _ hxy
    have := congrArg Fin.val hxy
    simp only [hi] at this
    exact Fin.ext (by omega)

theorem embLow_hi {n' n : ℕ} (z : Matrix (Fin (n' / 2)) (Fin (n / 2)) L) (k : Fin (n' / 2)) (l : Fin (n / 2)) :
    embLow n' n z (hi n' k) (hi n l) = z k l := by
  rw [embLow, dite_eq_left ⟨by simp [hi], by simp [hi]⟩]
  congr 1 <;> ext <;> simp [hi]

theorem embLow_eq_zero {n' n : ℕ} (z : Matrix (Fin (n' / 2)) (Fin (n / 2)) L) (r : Fin n') (c : Fin n)
    (h : r.1 < n' - n' / 2 ∨ c.1 < n - n / 2) : embLow n' n z r c = 0 := by
  rw [embLow, dite_eq_right (by omega)]

theorem mul_embLow_mul_apply {n' n : ℕ} (A : Matrix (Fin n') (Fin n') L) (B : Matrix (Fin n) (Fin n) L)
    (z : Matrix (Fin (n' / 2)) (Fin (n / 2)) L) (r : Fin n') (c : Fin n) :
    (A * embLow n' n z * B) r c = ∑ l, (∑ k, A r (hi n' k) * z k l) * B (hi n l) c := by
  rw [Matrix.mul_apply, sum_hi n]
  · refine Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.mul_apply, sum_hi n']
    · simp only [embLow_hi]
    · intro i hi'
      rw [embLow_eq_zero z i _ (Or.inl hi'), mul_zero]
  · intro j hj
    rw [Matrix.mul_apply, Finset.sum_eq_zero, zero_mul]
    intro i _
    rw [embLow_eq_zero z i j (Or.inr hj), mul_zero]

theorem lowBlock_mul_apply {n' n : ℕ} (A : Matrix (Fin n') (Fin n') L) (B : Matrix (Fin n) (Fin n) L)
    (z : Matrix (Fin (n' / 2)) (Fin (n / 2)) L) (r : Fin (n' / 2)) (c : Fin (n / 2)) :
    (lowBlock A * z * lowBlock B) r c = ∑ l, (∑ k, A (hi n' r) (hi n' k) * z k l) * B (hi n l) (hi n c) := by
  simp only [Matrix.mul_apply, lowBlock, Matrix.submatrix_apply]

theorem exists_hi {N : ℕ} (r : Fin N) (hr : N - N / 2 ≤ r.1) : ∃ k, r = hi N k :=
  ⟨⟨r.1 - (N - N / 2), by have := r.isLt; omega⟩, Fin.ext (by simp only [hi]; omega)⟩

theorem mul_embLow_mul_eq {n' n : ℕ} (A : Matrix (Fin n') (Fin n') L) (B : Matrix (Fin n) (Fin n) L)
    (hB : ∀ i j : Fin n, j < i → B i j = 0) (z : Matrix (Fin (n' / 2)) (Fin (n / 2)) L) (r : Fin n') (c : Fin n)
    (h : n' - n' / 2 ≤ r.1 ∨ c.1 < n - n / 2) :
    (A * embLow n' n z * B) r c = embLow n' n (lowBlock A * z * lowBlock B) r c := by
  by_cases hc : c.1 < n - n / 2
  · rw [embLow_eq_zero _ r c (Or.inr hc), mul_embLow_mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [hB (hi n l) c (Fin.lt_def.2 (by simp only [hi]; omega)), mul_zero]
  · have hr : n' - n' / 2 ≤ r.1 := by omega
    obtain ⟨r', rfl⟩ := exists_hi r hr
    obtain ⟨c', rfl⟩ := exists_hi c (by omega)
    rw [mul_embLow_mul_apply, embLow_hi, lowBlock_mul_apply]

variable [Valued L (WithZero (Multiplicative ℤ))]

theorem mem_mixLat_iff {n' n : ℕ} (x : Matrix (Fin n') (Fin n) L) : x ∈ mixLat L n' n ↔
    ∀ r c, (n' - n' / 2 ≤ r.1 ∨ n' / 2 ≤ r.1 ∧ c.1 < n / 2 → x r c = 0) ∧
      (n' / 2 ≤ r.1 → c.1 < n - n / 2 → x r c ∈ intL L) := Iff.rfl

theorem borel_mid_int {σ : L →+* L} {N : ℕ} (hv : ∀ x, Valued.v (σ x) = Valued.v x) {b : GU σ N}
    (hb : IsBorelU b) (i : Fin N) (hi' : i.rev = i) : b.1.1 i i ∈ intL L := by
  have h := P.fSatake_unit_diag hb i
  rw [hi'] at h
  have h2 := congrArg Valued.v h
  rw [map_mul, hv, map_one] at h2
  rw [mem_intL]
  by_contra hc
  rw [not_le] at hc
  have : (1 : WithZero (Multiplicative ℤ)) < Valued.v (b.1.1 i i) * Valued.v (b.1.1 i i) := one_lt_mul'' hc hc
  rw [h2] at this
  exact lt_irrefl _ this

theorem row_mul_eq {n' n : ℕ} (A : Matrix (Fin n') (Fin n') L) (hA : ∀ i j : Fin n', j < i → A i j = 0)
    (a : Matrix (Fin n') (Fin n) L) (ha : a ∈ mixLat L n' n) (r : Fin n') (hr : n' / 2 ≤ r.1) (j : Fin n) :
    (A * a) r j = A r r * a r j := by
  rw [mem_mixLat_iff] at ha
  rw [Matrix.mul_apply, Finset.sum_eq_single r]
  · intro i _ hir
    rcases lt_or_gt_of_ne hir with h1 | h1
    · rw [hA r i h1, zero_mul]
    · rw [(ha i j).1 (Or.inl (by have := Fin.lt_def.1 h1; omega)), mul_zero]
  · simp

theorem borel_mul_mem {σ : L →+* L} {n' n : ℕ} (hv : ∀ x, Valued.v (σ x) = Valued.v x) {g : GU σ n} {h : GU σ n'}
    (hg : IsBorelU g) (hh : IsBorelU h) (a : Matrix (Fin n') (Fin n) L) (ha : a ∈ mixLat L n' n) :
    (h.1.1 * a * g.1.1 : Matrix (Fin n') (Fin n) L) ∈ mixLat L n' n := by
  have ha' := (mem_mixLat_iff a).1 ha
  rw [mem_mixLat_iff]
  intro r c
  constructor
  · intro hrc
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [row_mul_eq _ hh a ha r (by omega)]
    rcases hrc with hr | ⟨hr, hc⟩
    · rw [(ha' r j).1 (Or.inl hr), mul_zero, zero_mul]
    · by_cases hjc : j.1 ≤ c.1
      · rw [(ha' r j).1 (Or.inr ⟨hr, by omega⟩), mul_zero, zero_mul]
      · rw [hg j c (Fin.lt_def.2 (by omega)), mul_zero]
  · intro hr hc
    rw [Matrix.mul_apply, Finset.sum_eq_single c]
    · rw [row_mul_eq _ hh a ha r hr]
      by_cases hz : a r c = 0
      · rw [hz, mul_zero, zero_mul]; exact zero_mem _
      · have h1 : ¬ (n' - n' / 2 ≤ r.1 ∨ n' / 2 ≤ r.1 ∧ c.1 < n / 2) := fun e => hz ((ha' r c).1 e)
        have hrr : r.rev = r := Fin.ext (by rw [Fin.val_rev]; omega)
        have hcc : c.rev = c := Fin.ext (by rw [Fin.val_rev]; omega)
        exact mul_mem (mul_mem (borel_mid_int hv hh r hrr) ((ha' r c).2 hr hc)) (borel_mid_int hv hg c hcc)
    · intro j _ hjc
      rcases lt_or_gt_of_ne hjc with h1 | h1
      · rw [row_mul_eq _ hh a ha r hr, (ha' r j).1 (Or.inr ⟨hr, by have := Fin.lt_def.1 h1; omega⟩), mul_zero, zero_mul]
      · rw [hg j c h1, mul_zero]
    · simp

end GlobalTheory.SphTheta.MixStab

namespace GlobalTheory.SphTheta


open MixStab in
theorem borel_mixLat_lowBlock : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q → ∀ (n n' : ℕ) (g : GU σ n) (h : GU σ n'), IsBorelU g → IsBorelU h → (∀ a : Matrix (Fin n') (Fin n) L, a ∈ mixLat L n' n → (h.1.1 * a * g.1.1 : Matrix (Fin n') (Fin n) L) ∈ mixLat L n' n) ∧ ∀ (z : Matrix (Fin (n' / 2)) (Fin (n / 2)) L), ∃ a ∈ mixLat L n' n, (∀ (r : Fin n') (c : Fin n), c.1 < n - n / 2 → a r c = 0) ∧ (h.1.1 * embLow n' n z * g.1.1 : Matrix (Fin n') (Fin n) L) = a + embLow n' n (lowBlock h.1.1 * z * lowBlock g.1.1) := by
  intro L _ _ ϖ σ q hU n n' g h hg hh
  refine ⟨fun a ha => borel_mul_mem hU.2.1 hg hh a ha, fun z => ?_⟩
  have key : ∀ (r : Fin n') (c : Fin n), n' - n' / 2 ≤ r.1 ∨ c.1 < n - n / 2 →
      (h.1.1 * embLow n' n z * g.1.1 - embLow n' n (lowBlock h.1.1 * z * lowBlock g.1.1)) r c = 0 := fun r c e => by
    rw [Matrix.sub_apply, sub_eq_zero]
    exact mul_embLow_mul_eq _ _ hg _ r c e
  refine ⟨h.1.1 * embLow n' n z * g.1.1 - embLow n' n (lowBlock h.1.1 * z * lowBlock g.1.1), ?_,
    fun r c hc => key r c (Or.inr hc), (sub_add_cancel _ _).symm⟩
  rw [mem_mixLat_iff]
  intro r c
  refine ⟨fun e => key r c (by omega), fun _ hc => ?_⟩
  rw [key r c (Or.inr hc)]
  exact zero_mem _

end GlobalTheory.SphTheta
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryBorelPreservesMixedModelLatticeLowerBlockStatement
open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryBorel_preserves_mixedModelLattice_lowerBlock : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q → ∀ (n n' : ℕ) (g : GU σ n) (h : GU σ n'), IsBorelU g → IsBorelU h → (∀ a : Matrix (Fin n') (Fin n) L, a ∈ mixLat L n' n → (h.1.1 * a * g.1.1 : Matrix (Fin n') (Fin n) L) ∈ mixLat L n' n) ∧ ∀ (z : Matrix (Fin (n' / 2)) (Fin (n / 2)) L), ∃ a ∈ mixLat L n' n, (∀ (r : Fin n') (c : Fin n), c.1 < n - n / 2 → a r c = 0) ∧ (h.1.1 * embLow n' n z * g.1.1 : Matrix (Fin n') (Fin n) L) = a + embLow n' n (lowBlock h.1.1 * z * lowBlock g.1.1) := by
  first | exact @GlobalTheory.SphTheta.borel_mixLat_lowBlock | exact GlobalTheory.SphTheta.borel_mixLat_lowBlock | (intros; apply GlobalTheory.SphTheta.borel_mixLat_lowBlock <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelInvariantFormUpperTriangularPairAction
open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

namespace GlobalTheory.SphTheta

theorem isBorelU_inv_mixeq {L : Type} [Field L] {σ : L →+* L} {n : ℕ} {g : GU σ n} (hg : IsBorelU g) :
    IsBorelU g⁻¹ := by
  intro i j hij
  exact Formalism.UG.P.spherical_upper_inv (g : GL (Fin n) L) ((Formalism.UG.P.spherical_upper_iff _).1 hg) hij

theorem mixLat_form_borel : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (ψ : AddChar L ℂ) (n n' : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (ω : GU σ n × GU σ n' →* Module.End ℂ M) (s : M), IsStd ϖ σ q δ ψ ρ ω s → ∀ ℓ : M →ₗ[ℂ] ℂ, (∀ a ∈ mixLat L n' n, ∀ v, ℓ (ρ a v) = ℓ v) → (∀ ℓ' : M →ₗ[ℂ] ℂ, (∀ a ∈ mixLat L n' n, ∀ v, ℓ' (ρ a v) = ℓ' v) → ∀ v, ℓ' v = ℓ' s * ℓ v) → ∀ (g : GU σ n) (h : GU σ n'), IsBorelU g → IsBorelU h → (∀ v, ℓ (ω (g, h) v) = ℓ (ω (g, h) s) * ℓ v) ∧ ∀ (z : Matrix (Fin (n' / 2)) (Fin (n / 2)) L) (v : M), ℓ (ρ (embLow n' n z) (ω (g, h) v)) = ℓ (ω (g, h) s) * ℓ (ρ (embLow n' n (lowBlock (h⁻¹).1.1 * z * lowBlock g.1.1)) v) := by
  intro L _ _ ϖ σ q δ ψ n n' M _ _ ρ ω s hS ℓ hℓ huniq g h hg hh
  have hU := hS.1.unr
  have hnorm : ∀ (g : GU σ n) (h : GU σ n') (x : Matrix (Fin n') (Fin n) L),
      ω (g, h) * ρ x = ρ (h.1.1 * x * ((g.1)⁻¹ : GL (Fin n) L).1) * ω (g, h) := hS.1.norm
  have c1 : ∀ (g : GU σ n) (h : GU σ n'), IsBorelU g → IsBorelU h →
      ∀ v, ℓ (ω (g, h) v) = ℓ (ω (g, h) s) * ℓ v := by
    intro g h hg hh
    refine huniq (ℓ.comp (ω (g, h))) (fun a ha v => ?_)
    have hm := (GlobalTheory.T.unitaryBorel_preserves_mixedModelLattice_lowerBlock L ϖ σ q hU n n' g⁻¹ h (isBorelU_inv_mixeq hg) hh).1 a ha
    show ℓ (ω (g, h) (ρ a v)) = ℓ (ω (g, h) v)
    rw [← Module.End.mul_apply, hnorm, Module.End.mul_apply]
    exact hℓ _ hm _
  refine ⟨c1 g h hg hh, fun z v => ?_⟩
  obtain ⟨a, ha, ha0, he⟩ := (GlobalTheory.T.unitaryBorel_preserves_mixedModelLattice_lowerBlock L ϖ σ q hU n n' g h⁻¹ hg (isBorelU_inv_mixeq hh)).2 z
  have key : ρ (embLow n' n z) * ω (g, h) = ω (g, h) * ρ ((h⁻¹).1.1 * embLow n' n z * g.1.1) := by
    rw [hnorm]
    congr 2
    simp [Matrix.mul_assoc]
  set E' := embLow n' n (lowBlock (h⁻¹).1.1 * z * lowBlock g.1.1) with hE'
  have h0 : locH σ δ (antiG L n) (antiG L n') a E' = 0 := by
    rw [locH_antiG]
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_)
    by_cases hj : j.1 < n - n / 2
    · rw [ha0 i j hj, zero_mul]
    · rw [hE', embLow, dite_eq_right (by simp only [Fin.val_rev]; omega), map_zero, mul_zero]
  have hsplit : ρ (a + E') = ρ a * ρ E' := by
    rw [hS.1.rho_mul, h0]
    simp
  rw [← Module.End.mul_apply, key, Module.End.mul_apply, c1 g h hg hh, he, hsplit, Module.End.mul_apply, hℓ a ha]

end GlobalTheory.SphTheta
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelInvariantFormUpperTriangularPairActionStatement
open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedModelInvariantForm_upperTriangular_pair_action : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (ψ : AddChar L ℂ) (n n' : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (ω : GU σ n × GU σ n' →* Module.End ℂ M) (s : M), IsStd ϖ σ q δ ψ ρ ω s → ∀ ℓ : M →ₗ[ℂ] ℂ, (∀ a ∈ mixLat L n' n, ∀ v, ℓ (ρ a v) = ℓ v) → (∀ ℓ' : M →ₗ[ℂ] ℂ, (∀ a ∈ mixLat L n' n, ∀ v, ℓ' (ρ a v) = ℓ' v) → ∀ v, ℓ' v = ℓ' s * ℓ v) → ∀ (g : GU σ n) (h : GU σ n'), IsBorelU g → IsBorelU h → (∀ v, ℓ (ω (g, h) v) = ℓ (ω (g, h) s) * ℓ v) ∧ ∀ (z : Matrix (Fin (n' / 2)) (Fin (n / 2)) L) (v : M), ℓ (ρ (embLow n' n z) (ω (g, h) v)) = ℓ (ω (g, h) s) * ℓ (ρ (embLow n' n (lowBlock (h⁻¹).1.1 * z * lowBlock g.1.1)) v) := by
  first | exact @GlobalTheory.SphTheta.mixLat_form_borel | exact GlobalTheory.SphTheta.mixLat_form_borel | (intros; apply GlobalTheory.SphTheta.mixLat_form_borel <;> assumption)
end
end
