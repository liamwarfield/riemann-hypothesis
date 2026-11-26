module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwasawaBlockTriangular
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsingletonJacquetOfPerm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsSelfDualOfHasConductor
public import GroundTheory.GlobalFields.TateThesis.GaussianSchwartz
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilTensorLiftConclusion
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScaledBasisMemChainLattice
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEmbXMul
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

namespace GlobalTheory.RootEx.Unram
open GlobalTheory.StepData

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

variable {k : Type} [Field k] [ValuativeRel k] {n n' : Type} {c : ℕ} in
private theorem affPt_apply_of_not_free {p : ℕ} (x₀ : Matrix n n' k)
    (e : { rs // _root_.GlobalTheory.RootEx.Free p rs } → k) {r : n ⊕ Fin c} {s : n' ⊕ Fin (c + 1)}
    (hf : ¬ _root_.GlobalTheory.RootEx.Free p (r, s)) :
    _root_.GlobalTheory.RootEx.affPt (c := c) p x₀ e r s = _root_.GlobalTheory.RootEx.basePt c x₀ r s := by
  simp only [_root_.GlobalTheory.RootEx.affPt, Matrix.add_apply, Matrix.of_apply, dif_neg hf, add_zero]

variable {k : Type} [Field k] [ValuativeRel k] {n n' : Type} {c : ℕ} in
private theorem affPt_apply_of_free {p : ℕ} (x₀ : Matrix n n' k)
    (e : { rs // _root_.GlobalTheory.RootEx.Free p rs } → k) {r : n ⊕ Fin c} {s : n' ⊕ Fin (c + 1)}
    (hf : _root_.GlobalTheory.RootEx.Free p (r, s)) :
    _root_.GlobalTheory.RootEx.affPt (c := c) p x₀ e r s = e ⟨(r, s), hf⟩ := by
  simp only [_root_.GlobalTheory.RootEx.affPt, _root_.GlobalTheory.RootEx.basePt, Matrix.add_apply,
    Matrix.of_apply, dif_pos hf]
  have hf' := hf
  rcases r with i | l <;> rcases s with j | m <;> simp only [_root_.GlobalTheory.RootEx.Free] at hf' <;>
    simp [Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂] <;>
    omega

variable {k : Type} [Field k] [ValuativeRel k] {n n' : Type} {c : ℕ} in
private theorem intM_basePt_of_intM {x₀ : Matrix n n' k}
    (hx : _root_.GlobalTheory.StepData.IntM x₀) :
    _root_.GlobalTheory.StepData.IntM (_root_.GlobalTheory.RootEx.basePt c x₀) := by
  unfold _root_.GlobalTheory.RootEx.basePt
  refine _root_.GlobalTheory.StepData.intM_fromBlocks.mpr
    ⟨hx, _root_.GlobalTheory.StepData.intM_zero, _root_.GlobalTheory.StepData.intM_zero, fun l i => ?_⟩
  simp only [Matrix.of_apply]
  split_ifs
  exacts [one_mem _, zero_mem _]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype n] [DecidableEq n] [Fintype n']
  [DecidableEq n'] in
theorem _root_.GlobalTheory.RootEx.Unram.intM_affPt {p : ℕ} (x₀ : Matrix n n' k) (e) :
    _root_.GlobalTheory.StepData.IntM (_root_.GlobalTheory.RootEx.affPt (c := c) p x₀ e) ↔
      _root_.GlobalTheory.StepData.IntM x₀ ∧ ∀ rs, e rs ∈ 𝒪[k] := by
  constructor
  · intro h
    refine ⟨fun i j => ?_, fun rs => ?_⟩
    · have hij := h (Sum.inl i) (Sum.inl j)
      rwa [affPt_apply_of_not_free x₀ e (by simp [_root_.GlobalTheory.RootEx.Free]),
        _root_.GlobalTheory.RootEx.basePt, Matrix.fromBlocks_apply₁₁] at hij
    · obtain ⟨⟨r, s⟩, hf⟩ := rs
      have hrs := h r s
      rwa [affPt_apply_of_free x₀ e hf] at hrs
  · rintro ⟨hx, he⟩ r s
    by_cases hf : _root_.GlobalTheory.RootEx.Free p (r, s)
    · rw [affPt_apply_of_free x₀ e hf]
      exact he _
    · rw [affPt_apply_of_not_free x₀ e hf]
      exact intM_basePt_of_intM hx r s

theorem _root_.GlobalTheory.RootEx.Unram.psi_eq_one {ψ : AddChar k Circle}
    (hψ : _root_.GlobalTheory.SplitWeil.HasConductor ψ 1) {x : k} (hx : x ∈ 𝒪[k]) : ψ x = 1 := by
  have h1 := (hψ x).mpr (by
    rw [Units.val_one, map_one]
    exact (Valuation.mem_integer_iff _ _).mp hx)
  exact h1 x le_rfl

theorem _root_.GlobalTheory.RootEx.Unram.mem_of_psi {ψ : AddChar k Circle}
    (hψ : _root_.GlobalTheory.SplitWeil.HasConductor ψ 1) {x : k}
    (hx : ∀ t ∈ 𝒪[k], ψ (t * x) = 1) : x ∈ 𝒪[k] := by
  rw [Valuation.mem_integer_iff]
  have hmain := (hψ x).mp ?_
  · simpa using hmain
  intro y hy
  by_cases hx0 : x = 0
  · subst hx0
    have hy0 : y = 0 := by simpa using hy
    simp [hy0]
  · have hv : valuation k (y / x) ≤ 1 := by
      rw [map_div₀]
      exact div_le_one_of_le₀ hy zero_le'
    have hyx := hx (y / x) ((Valuation.mem_integer_iff _ _).mpr hv)
    rwa [div_mul_cancel₀ y hx0] at hyx

variable [MeasurableSpace k] [BorelSpace k]

variable {k : Type} [Field k] [ValuativeRel k] {n n' : Type} {c : ℕ} in
private theorem ch_affPt_mem_of_integral {p : ℕ} (x₀ : Matrix n n' k)
    (e : { rs // _root_.GlobalTheory.RootEx.Free p rs } → k) (he : ∀ rs, e rs ∈ 𝒪[k]) :
    _root_.GlobalTheory.RootEx.ch (_root_.GlobalTheory.RootEx.affPt (c := c) p x₀ e) ∈ 𝒪[k] := by
  unfold _root_.GlobalTheory.RootEx.ch
  refine sum_mem fun i _ => ?_
  have hf : _root_.GlobalTheory.RootEx.Free (n := n) (n' := n') p (Sum.inr i, Sum.inr i.succ) := by
    simp [_root_.GlobalTheory.RootEx.Free]
  rw [affPt_apply_of_free x₀ e hf]
  exact he _

omit [DecidableEq n] [DecidableEq n'] in
open Classical in
theorem _root_.GlobalTheory.RootEx.Unram.opE_of_ite {p : ℕ} {ψ : AddChar k Circle}
    (hψ : _root_.GlobalTheory.SplitWeil.HasConductor ψ 1) {ν : Measure k} (hν : _root_.GlobalTheory.SplitWeil.IsUnitVol ν)
    (Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x₀ : Matrix n n' k) (P : Prop)
    (h : ∀ e, Ψ (_root_.GlobalTheory.RootEx.affPt p x₀ e) = if P ∧ ∀ rs, e rs ∈ 𝒪[k] then 1 else 0) :
    _root_.GlobalTheory.RootEx.opE ψ ν p Ψ x₀ = if P then 1 else 0 := by
  haveI := _root_.GlobalTheory.SplitWeil.secondCountable k
  haveI := hν.1
  set S : Set ({ rs // _root_.GlobalTheory.RootEx.Free (n := n) (c := c) (n' := n') p rs } → k) :=
    Set.univ.pi fun _ => (𝒪[k] : Set k) with hS
  have hSm : MeasurableSet S :=
    MeasurableSet.univ_pi fun _ => (_root_.GlobalTheory.SplitWeil.isOpen_int k).measurableSet
  have hint : ∀ e : { rs // _root_.GlobalTheory.RootEx.Free (n := n) (c := c) (n' := n') p rs } → k,
      Ψ (_root_.GlobalTheory.RootEx.affPt p x₀ e) *
          ((ψ (-_root_.GlobalTheory.RootEx.ch (_root_.GlobalTheory.RootEx.affPt p x₀ e)) : Circle) : ℂ) =
        if P then S.indicator (fun _ => (1 : ℂ)) e else 0 := by
    intro e
    rw [h e]
    by_cases hP : P
    · by_cases he : ∀ rs, e rs ∈ 𝒪[k]
      · have heS : e ∈ S := fun rs _ => he rs
        rw [if_pos ⟨hP, he⟩, if_pos hP, Set.indicator_of_mem heS,
          _root_.GlobalTheory.RootEx.Unram.psi_eq_one hψ
            (neg_mem (ch_affPt_mem_of_integral x₀ e he))]
        simp
      · have heS : e ∉ S := fun heS => he fun rs => heS rs (Set.mem_univ _)
        rw [if_neg (fun h' => he h'.2), if_pos hP, Set.indicator_of_notMem heS, zero_mul]
    · rw [if_neg (fun h' => hP h'.1), if_neg hP, zero_mul]
  unfold _root_.GlobalTheory.RootEx.opE
  simp_rw [hint]
  split_ifs with hP
  · rw [integral_indicator_const _ hSm, Measure.real_def, hS, Measure.pi_pi]
    simp [hν.2]
  · simp

omit [DecidableEq n] [DecidableEq n'] in
theorem _root_.GlobalTheory.RootEx.Unram.psi_ch_eq_one {p : ℕ} (ψ : AddChar k Circle)
    (ν : Measure k) [ν.IsAddHaarMeasure]
    (Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x₀ : Matrix n n' k)
    (h : _root_.GlobalTheory.RootEx.opE ψ ν p Ψ x₀ ≠ 0)
    (D : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)
    (hD : ∀ r s, ¬ _root_.GlobalTheory.RootEx.Free p (r, s) → D r s = 0)
    (hΨ : ∀ x, Ψ (x + D) = Ψ x) : ψ (-_root_.GlobalTheory.RootEx.ch D) = 1 := by
  haveI := _root_.GlobalTheory.SplitWeil.secondCountable k
  set d : { rs // _root_.GlobalTheory.RootEx.Free (n := n) (c := c) (n' := n') p rs } → k :=
    fun rs => D rs.1.1 rs.1.2 with hd
  have haff : ∀ e, _root_.GlobalTheory.RootEx.affPt p x₀ (e + d) = _root_.GlobalTheory.RootEx.affPt p x₀ e + D := by
    intro e
    ext r s
    simp only [_root_.GlobalTheory.RootEx.affPt, Matrix.add_apply, Matrix.of_apply]
    by_cases hf : _root_.GlobalTheory.RootEx.Free p (r, s)
    · simp only [dif_pos hf, Pi.add_apply, hd]
      ring
    · simp only [dif_neg hf, hD r s hf, add_zero]
  have hch : ∀ A B : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k,
      _root_.GlobalTheory.RootEx.ch (A + B) =
        _root_.GlobalTheory.RootEx.ch A + _root_.GlobalTheory.RootEx.ch B := by
    intro A B
    simp [_root_.GlobalTheory.RootEx.ch, Finset.sum_add_distrib]
  have key : _root_.GlobalTheory.RootEx.opE ψ ν p Ψ x₀ =
      ((ψ (-_root_.GlobalTheory.RootEx.ch D) : Circle) : ℂ) * _root_.GlobalTheory.RootEx.opE ψ ν p Ψ x₀ := by
    unfold _root_.GlobalTheory.RootEx.opE
    rw [← integral_const_mul, ← integral_add_right_eq_self _ d]
    congr 1
    ext e
    rw [haff, hΨ, hch, neg_add, AddChar.map_add_eq_mul, Circle.coe_mul]
    ring
  have h1 : ((ψ (-_root_.GlobalTheory.RootEx.ch D) : Circle) : ℂ) = 1 :=
    mul_right_cancel₀ h (key.symm.trans (one_mul _).symm)
  exact Circle.ext (h1.trans Circle.coe_one.symm)

end GlobalTheory.RootEx.Unram
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsBorelSphRevInv
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound Matrix

namespace GlobalTheory.SatakeFlip

section Ring

variable {R : Type} [CommRing R] {n : ℕ}

theorem revT_mul (A B : Matrix (Fin n) (Fin n) R) :
    Aᵀ.submatrix Fin.rev Fin.rev * Bᵀ.submatrix Fin.rev Fin.rev = (B * A)ᵀ.submatrix Fin.rev Fin.rev := by
  rw [transpose_mul]
  exact submatrix_mul_equiv Aᵀ Bᵀ Fin.rev Fin.revPerm Fin.rev

theorem revT_one : (1 : Matrix (Fin n) (Fin n) R)ᵀ.submatrix Fin.rev Fin.rev = 1 := by
  rw [transpose_one]
  exact submatrix_one_equiv Fin.revPerm

def invRevT : GL (Fin n) R →* GL (Fin n) R where
  toFun g := ⟨(g⁻¹).valᵀ.submatrix Fin.rev Fin.rev, g.valᵀ.submatrix Fin.rev Fin.rev,
    by rw [revT_mul, Units.mul_inv, revT_one], by rw [revT_mul, Units.inv_mul, revT_one]⟩
  map_one' := Units.ext (by simp only [inv_one, Units.val_one]; exact revT_one)
  map_mul' g h := Units.ext (by simp only [_root_.mul_inv_rev, Units.val_mul]; rw [revT_mul])

theorem invRevT_apply (g : GL (Fin n) R) (i j : Fin n) :
    (invRevT g).val i j = (g⁻¹).val j.rev i.rev := rfl

theorem invRevT_invRevT (g : GL (Fin n) R) : invRevT (invRevT g) = g := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [invRevT_apply, ← map_inv, invRevT_apply, inv_inv, Fin.rev_rev, Fin.rev_rev]

theorem invRevT_mem_borel {b : GL (Fin n) R} (hb : b ∈ GlobalTheory.SmGL.borel R (Fin n)) :
    invRevT b ∈ GlobalTheory.SmGL.borel R (Fin n) :=
  (mem_borel R).2 fun _ _ h => (mem_borel R).1 (inv_mem hb) _ _ (Fin.rev_lt_rev.2 h)

theorem inv_diag_mul {b : GL (Fin n) R} (hb : b ∈ GlobalTheory.SmGL.borel R (Fin n)) (i : Fin n) :
    (b⁻¹).val i i * b.val i i = 1 := by
  have h := congrFun (congrFun (Units.inv_mul b) i) i
  change ((b⁻¹).val * b.val) i i = (1 : Matrix (Fin n) (Fin n) R) i i at h
  rw [Matrix.mul_apply, one_apply_eq, Finset.sum_eq_single i] at h
  · exact h
  · intro j _ hj
    rcases lt_or_gt_of_ne hj with h' | h'
    · rw [(mem_borel R).1 (inv_mem hb) _ _ h', zero_mul]
    · rw [(mem_borel R).1 hb _ _ h', mul_zero]
  · simp

end Ring

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem invRevT_mem_KO {g : GL (Fin n) k} (hg : g ∈ KO k (Fin n)) : invRevT g ∈ KO k (Fin n) := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.SplitFlip.mem_KO_iff g).1 hg
  refine (GlobalTheory.SplitFlip.mem_KO_iff _).2 ⟨fun i j => h2 _ _, fun i j => ?_⟩
  rw [← map_inv, invRevT_apply, inv_inv]
  exact h1 _ _

theorem ord_inv_eq_neg (x : kˣ) : ord k x⁻¹ = -ord k x := by
  have h := ord_mul k x⁻¹ x
  rw [inv_mul_cancel, ord_eq_zero (k := k) (x := 1) (by simp)] at h
  omega

def cosetMap : GL (Fin n) k ⧸ KO k (Fin n) → GL (Fin n) k ⧸ KO k (Fin n) :=
  Quotient.map' invRevT fun a b h => by
    rw [QuotientGroup.leftRel_apply] at h ⊢
    rw [← map_inv, ← map_mul]
    exact invRevT_mem_KO h

theorem cosetMap_mk (g : GL (Fin n) k) :
    cosetMap (g : GL (Fin n) k ⧸ KO k (Fin n)) = (invRevT g : GL (Fin n) k) := rfl

theorem cosetMap_cosetMap (c : GL (Fin n) k ⧸ KO k (Fin n)) : cosetMap (cosetMap c) = c := by
  induction c using QuotientGroup.induction_on with
  | H g => rw [cosetMap_mk, cosetMap_mk, invRevT_invRevT]

theorem cosetMap_smul (x : GL (Fin n) k) (c : GL (Fin n) k ⧸ KO k (Fin n)) :
    cosetMap (x • c) = invRevT x • cosetMap c := by
  induction c using QuotientGroup.induction_on with
  | H g =>
    rw [MulAction.Quotient.smul_mk, cosetMap_mk, cosetMap_mk, MulAction.Quotient.smul_mk, smul_eq_mul,
      smul_eq_mul, map_mul]

theorem exists_isBorelSph_rev_inv (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (γ : Fin n → ℂ) (φ : GL (Fin n) k → ℂ)
    (h : IsBorelSph k γ φ) (hS : HasBoundedSums k φ) :
    ∃ ψ : GL (Fin n) k → ℂ, IsBorelSph k (fun i => (γ (Fin.rev i))⁻¹) ψ ∧ HasBoundedSums k ψ := by
  classical
  refine ⟨fun g => φ (invRevT g), ⟨fun g x hx => ?_, fun b hb t ht => ?_⟩, fun S hK => ?_⟩
  · show φ (invRevT (g * x)) = φ (invRevT g)
    rw [map_mul, h.1 _ _ (invRevT_mem_KO hx)]
  · show φ (invRevT b) = _
    rw [h.2 _ (invRevT_mem_borel hb) (fun i => (t i.rev)⁻¹) fun i => ?_]
    · refine Fintype.prod_equiv Fin.revPerm _ _ fun i => ?_
      simp only [Fin.revPerm_apply, Fin.rev_rev, ord_inv_eq_neg, _root_.zpow_neg, _root_.inv_zpow]
    · rw [invRevT_apply, Units.val_inv_eq_inv_val, ← ht]
      exact eq_inv_of_mul_eq_one_left (inv_diag_mul hb _)
  · have hinj : Function.Injective (cosetMap (k := k) (n := n)) :=
      Function.LeftInverse.injective cosetMap_cosetMap
    have h1 := hS (S.image cosetMap) fun x hx c hc => by
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 hc
      refine Finset.mem_image.2 ⟨invRevT x • d, hK _ (invRevT_mem_KO hx) _ hd, ?_⟩
      rw [cosetMap_smul, invRevT_invRevT]
    rw [Finset.card_image_of_injective _ hinj, Finset.sum_image fun _ _ _ _ e => hinj e] at h1
    refine le_of_eq_of_le (congrArg _ (Finset.sum_congr rfl fun c _ => ?_)) h1
    obtain ⟨x, hx⟩ := QuotientGroup.mk_out_eq_mul (KO k (Fin n)) (invRevT c.out)
    rw [← cosetMap_mk, QuotientGroup.out_eq'] at hx
    show φ (invRevT c.out) = _
    rw [hx, h.1 _ _ x.2]

end GlobalTheory.SatakeFlip
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntertwiningSymplecticAndGroupLaw
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntertwiningSymplecticAndGroupLaw
noncomputable section

open GlobalTheory.RealWeil MeasureTheory Complex
open scoped SchwartzMap Matrix Real RealInnerProductSpace

namespace GlobalTheory.RealWeil.Intertw

variable {l : Type} [Fintype l]

theorem sympl_smul_left (r : ℝ) (w w' : l ⊕ l → ℝ) : sympl (r • w) w' = r * sympl w w' := by
  simp only [sympl, pPart_smul, qPart_smul, real_inner_smul_left]
  ring

theorem sympl_smul_right (r : ℝ) (w w' : l ⊕ l → ℝ) : sympl w (r • w') = r * sympl w w' := by
  simp only [sympl, pPart_smul, qPart_smul, real_inner_smul_right]
  ring

theorem sympl_antisymm (w w' : l ⊕ l → ℝ) : sympl w w' = -sympl w' w := by
  simp only [sympl, real_inner_comm (pPart w) (qPart w'), real_inner_comm (qPart w) (pPart w')]
  ring

theorem sympl_sub_left (u u' z : l ⊕ l → ℝ) : sympl (u - u') z = sympl u z - sympl u' z := by
  have h1 : pPart (u - u') = pPart u - pPart u' := rfl
  have h2 : qPart (u - u') = qPart u - qPart u' := rfl
  simp only [sympl, h1, h2, inner_sub_left]
  ring

theorem eq_zero_of_exp_eq_one (D : ℝ) (h : ∀ r : ℝ, exp (((π * (r * D) : ℝ) : ℂ) * I) = 1) : D = 0 := by
  by_contra hD
  have := h D⁻¹
  rw [inv_mul_cancel₀ hD, mul_one, Complex.exp_pi_mul_I] at this
  norm_num at this

theorem rhoFun_gaussian_ne_zero (w : l ⊕ l → ℝ) :
    rhoFun w ⇑(GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ l)) (-pPart w) ≠ 0 := by
  simp only [rhoFun, neg_add_cancel, GroundTheory.Global.gaussianSchwartz_apply]
  refine mul_ne_zero ?_ ?_
  · intro h
    have := norm_phase w (-pPart w)
    rw [h, norm_zero] at this
    exact zero_ne_one this
  · simp

theorem coe_smul_sch (c : ℂ) (f : Sch l) : ⇑(c • f) = c • ⇑f := by
  funext x
  simp

theorem eq_of_smul_eq_smul {c c' : ℂ} {F : EuclideanSpace ℝ l → ℂ} {x : EuclideanSpace ℝ l} (hx : F x ≠ 0)
    (h : c • F = c' • F) : c = c' := by
  have := congrFun h x
  simp only [Pi.smul_apply, smul_eq_mul] at this
  exact mul_right_cancel₀ hx this

theorem eq_of_rhoFun_eq {u u' : l ⊕ l → ℝ} (h : ∀ g : Sch l, rhoFun u ⇑g = rhoFun u' ⇑g) : u = u' := by
  classical
  set g0 := GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ l) with hg0
  have key : ∀ z : l ⊕ l → ℝ, exp (((π * (2 * sympl (u - u') z) : ℝ) : ℂ) * I) = 1 := by
    intro z
    obtain ⟨g1, hg1⟩ := exists_schwartz_rhoFun l z g0
    have h1 := h g1
    rw [hg1, rhoFun_rhoFun, rhoFun_rhoFun] at h1
    have h2 := congrArg (rhoFun z) (h g0)
    rw [rhoFun_rhoFun, rhoFun_rhoFun, add_comm z u, add_comm z u', sympl_antisymm z u, sympl_antisymm z u'] at h2
    set a := sympl u z
    set b := sympl u' z
    set F := rhoFun (u + z) ⇑g0
    set G := rhoFun (u' + z) ⇑g0
    have h3 : (exp (((π * -b : ℝ) : ℂ) * I) * exp (((π * a : ℝ) : ℂ) * I)) • F =
        (exp (((π * b : ℝ) : ℂ) * I) * exp (((π * -a : ℝ) : ℂ) * I)) • F := by
      rw [mul_smul, h1, smul_smul, mul_comm, ← smul_smul, ← h2, smul_smul, mul_smul]
    have h4 := eq_of_smul_eq_smul (rhoFun_gaussian_ne_zero (u + z)) h3
    rw [← Complex.exp_add, ← Complex.exp_add] at h4
    rw [sympl_sub_left]
    have e : ((π * (2 * (a - b)) : ℝ) : ℂ) * I =
        (((π * -b : ℝ) : ℂ) * I + ((π * a : ℝ) : ℂ) * I) - (((π * b : ℝ) : ℂ) * I + ((π * -a : ℝ) : ℂ) * I) := by
      push_cast
      ring
    rw [e, Complex.exp_sub, h4, div_self (exp_ne_zero _)]
  have hz : ∀ z, sympl (u - u') z = 0 := by
    intro z
    have := eq_zero_of_exp_eq_one (2 * sympl (u - u') z) fun r => by
      have := key (r • z)
      rwa [sympl_smul_right, show 2 * (r * sympl (u - u') z) = r * (2 * sympl (u - u') z) by ring] at this
    linarith
  have hJ : Matrix.J l ℝ *ᵥ (u - u') = 0 := by
    ext b
    have := hz (Pi.single b 1)
    rw [sympl_antisymm, sympl_single] at this
    simpa using this
  have hd : u - u' = 0 := by
    have : u - u' = -((Matrix.J l ℝ * Matrix.J l ℝ) *ᵥ (u - u')) := by
      rw [Matrix.J_squared, Matrix.neg_mulVec, Matrix.one_mulVec, neg_neg]
    rw [this, ← Matrix.mulVec_mulVec, hJ, Matrix.mulVec_zero, neg_zero]
  exact sub_eq_zero.mp hd

end GlobalTheory.RealWeil.Intertw

namespace GlobalTheory.RealWeil

open Intertw in
theorem intertwining_symplectic_and_group_law : ∀ (l : Type) [Fintype l]
    (A : ℝ → (l ⊕ l → ℝ) →ₗ[ℝ] (l ⊕ l → ℝ)) (T : ℝ → Sch l →ₗ[ℂ] Sch l),
    (∀ s t f, T (s + t) f = T s (T t f)) → (∀ f, T 0 f = f) →
    (∀ t w (f f₁ : Sch l), ⇑f₁ = rhoFun w ⇑f → ⇑(T t f₁) = rhoFun (A t w) ⇑(T t f)) →
    (∀ t f, ∫ x, ‖T t f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2) →
    (∀ t w w', sympl (A t w) (A t w') = sympl w w') ∧ (∀ s t w, A (s + t) w = A s (A t w)) ∧ ∀ w, A 0 w = w := by
  intro l _ A T hadd h0 hI _
  have hsurj : ∀ t (h : Sch l), T t (T (-t) h) = h := fun t h => by rw [← hadd, add_neg_cancel, h0]
  refine ⟨fun t w w' => ?_, fun s t w => ?_, fun w => ?_⟩
  · have hE : ∀ v v' : l ⊕ l → ℝ, exp (((π * sympl (A t v) (A t v') : ℝ) : ℂ) * I) =
        exp (((π * sympl v v' : ℝ) : ℂ) * I) := by
      intro v v'
      set g0 := GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ l) with hg0
      obtain ⟨f₁, hf₁⟩ := exists_schwartz_rhoFun l v' (T (-t) g0)
      obtain ⟨f₂, hf₂⟩ := exists_schwartz_rhoFun l v f₁
      obtain ⟨f₃, hf₃⟩ := exists_schwartz_rhoFun l (v + v') (T (-t) g0)
      have e2 : f₂ = exp (((π * sympl v v' : ℝ) : ℂ) * I) • f₃ := by
        apply DFunLike.coe_injective
        rw [coe_smul_sch, hf₂, hf₁, hf₃, rhoFun_rhoFun]
      have k1 := hI t v' (T (-t) g0) f₁ hf₁
      have k2 := hI t v f₁ f₂ hf₂
      have k3 := hI t (v + v') (T (-t) g0) f₃ hf₃
      rw [hsurj] at k1 k3
      rw [k1, rhoFun_rhoFun, e2, map_smul, coe_smul_sch, k3, map_add (f := _)] at k2
      exact (eq_of_smul_eq_smul (rhoFun_gaussian_ne_zero (A t v + A t v')) k2).symm
    apply sub_eq_zero.mp
    refine eq_zero_of_exp_eq_one _ fun r => ?_
    have := hE (r • w) w'
    rw [map_smul, sympl_smul_left, sympl_smul_left] at this
    rw [show ((π * (r * (sympl (A t w) (A t w') - sympl w w')) : ℝ) : ℂ) * I =
        ((π * (r * sympl (A t w) (A t w')) : ℝ) : ℂ) * I - ((π * (r * sympl w w') : ℝ) : ℂ) * I by push_cast; ring,
      Complex.exp_sub, this, div_self (exp_ne_zero _)]
  · apply Intertw.eq_of_rhoFun_eq
    intro g
    obtain ⟨f₁, hf₁⟩ := exists_schwartz_rhoFun l w (T (-(s + t)) g)
    have h1 := hI (s + t) w _ f₁ hf₁
    have h2 := hI t w _ f₁ hf₁
    have h3 := hI s (A t w) _ _ h2
    rw [hsurj] at h1
    rw [← hadd, ← hadd, hsurj, h1] at h3
    exact h3
  · apply Intertw.eq_of_rhoFun_eq
    intro g
    obtain ⟨f₁, hf₁⟩ := exists_schwartz_rhoFun l w g
    have h := hI 0 w g f₁ hf₁
    rw [h0, h0] at h
    rw [← h, hf₁]

end GlobalTheory.RealWeil
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntertwiningSymplecticAndGroupLawStatement
open GlobalTheory.RealWeil MeasureTheory
open scoped SchwartzMap Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplectic_and_flow_of_intertwining_unitary : ∀ (l : Type) [Fintype l] (A : ℝ → (l ⊕ l → ℝ) →ₗ[ℝ] (l ⊕ l → ℝ)) (T : ℝ → Sch l →ₗ[ℂ] Sch l), (∀ s t f, T (s + t) f = T s (T t f)) → (∀ f, T 0 f = f) → (∀ t w (f f₁ : Sch l), ⇑f₁ = rhoFun w ⇑f → ⇑(T t f₁) = rhoFun (A t w) ⇑(T t f)) → (∀ t f, ∫ x, ‖T t f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2) → (∀ t w w', sympl (A t w) (A t w') = sympl w w') ∧ (∀ s t w, A (s + t) w = A s (A t w)) ∧ ∀ w, A 0 w = w := by
  first | exact @GlobalTheory.RealWeil.intertwining_symplectic_and_group_law | exact GlobalTheory.RealWeil.intertwining_symplectic_and_group_law | (intros; apply GlobalTheory.RealWeil.intertwining_symplectic_and_group_law <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsOpenSetOfLeRank
open Matrix Topology

namespace GlobalTheory

theorem exists_mul_mul_eq_one_of_le_rank {k : Type} [Field k] {m n : Type} [Fintype m] [Fintype n]
    {κ : ℕ} (x : Matrix m n k) (h : κ ≤ x.rank) :
    ∃ (A : Matrix (Fin κ) m k) (B : Matrix n (Fin κ) k), A * x * B = 1 := by
  classical
  obtain ⟨w, hw⟩ := exists_linearIndependent_of_le_finrank
    (R := k) (M := LinearMap.range x.mulVecLin) (n := κ) h
  choose v hv using fun i => (w i).2
  let B : Matrix n (Fin κ) k := Matrix.of fun j i => v i j
  have hw' : LinearIndependent k (fun i => (w i : m → k)) :=
    hw.map' (LinearMap.range x.mulVecLin).subtype (Submodule.ker_subtype _)
  have hcol : (x * B).col = fun i => (w i : m → k) := by
    funext i j
    rw [← hv i]
    simp [B, Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.col]
  have hinj : Function.Injective (x * B).mulVec := by
    rw [Matrix.mulVec_injective_iff, hcol]
    exact hw'
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' (x * B))
    (LinearMap.ker_eq_bot.2 (fun a b hab => hinj (by simpa only [Matrix.toLin'_apply] using hab)))
  refine ⟨LinearMap.toMatrix' g, B, ?_⟩
  have := congrArg LinearMap.toMatrix' hg
  rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at this
  rw [Matrix.mul_assoc, this]

theorem isOpen_setOf_le_rank (k : Type) [Field k] [TopologicalSpace k] [IsTopologicalRing k]
    [T1Space k] (m n : Type) [Fintype m] [Fintype n] (κ : ℕ) :
    IsOpen {x : Matrix m n k | κ ≤ x.rank} := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨A, B, hAB⟩ := exists_mul_mul_eq_one_of_le_rank x hx
  refine ⟨{y | (A * y * B).det ≠ 0}, ?_, ?_, ?_⟩
  · intro y hy
    have hu : IsUnit (A * y * B) :=
      (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hy)
    have h1 := Matrix.rank_of_isUnit _ hu
    rw [Fintype.card_fin] at h1
    change κ ≤ y.rank
    rw [← h1]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  · have hc : Continuous fun y : Matrix m n k => (A * y * B).det :=
      ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).matrix_det
    exact isOpen_ne.preimage hc
  · simp [hAB]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEqActStdLat
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms GlobalTheory.RootEx.UnfoldShape

namespace GlobalTheory.RootEx.UnfoldShape

theorem exists_eq_act_stdLat (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ι : Type) [Fintype ι] [DecidableEq ι]
    (L : Submodule 𝒪[k] (ι → k)) (hL : Submodule.IsFullLattice k L) :
    ∃ g : GL ι k, L = act g (stdLat k ι) := by
  haveI := hL
  haveI : Module.Free 𝒪[k] L := Submodule.IsLattice.free k L
  haveI : Module.Finite 𝒪[k] L := Module.Finite.iff_fg.mpr hL.fg
  have hr : Module.finrank 𝒪[k] L = Fintype.card ι := ((Submodule.IsFullLattice.finrank_eq k L).trans (Module.finrank_fintype_fun_eq_card k))
  let b : Module.Basis ι 𝒪[k] L :=
    (Module.finBasisOfFinrankEq 𝒪[k] L hr).reindex (Fintype.equivFin ι).symm
  let c : Module.Basis ι k (ι → k) := b.extendOfIsLattice k
  have hc : ∀ i, c i = (b i : ι → k) := fun i => Module.Basis.extendOfIsLattice_apply k b i
  let A : Matrix ι ι k := Matrix.of fun i j => (b j : ι → k) i
  have hA : IsUnit A := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    have : A.col = c := by
      funext j i
      rw [hc]; rfl
    rw [this]; exact c.linearIndependent
  obtain ⟨g, hg⟩ := hA
  have key : ∀ a : ι → 𝒪[k], (g : Matrix ι ι k) *ᵥ (fun i => (a i : k))
      = ((∑ j, a j • b j : L) : ι → k) := by
    intro a
    funext i
    rw [hg, Submodule.coe_sum, Finset.sum_apply]
    simp only [Matrix.mulVec, dotProduct, A, Matrix.of_apply, Submodule.coe_smul, Pi.smul_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]; rfl
  refine ⟨g, ?_⟩
  ext v
  rw [mem_act]
  constructor
  · intro hv
    refine ⟨fun i => (b.repr ⟨v, hv⟩ i : k), mem_stdLat.2 fun i => (b.repr ⟨v, hv⟩ i).2, ?_⟩
    rw [key, b.sum_repr]
  · rintro ⟨w, hw, rfl⟩
    rw [mem_stdLat] at hw
    have := key fun i => ⟨w i, hw i⟩
    change (g : Matrix ι ι k) *ᵥ w = _ at this
    rw [this]
    exact Subtype.property _

end GlobalTheory.RootEx.UnfoldShape
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitThetaGridPathAvoidsOppositeCorner
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitThetaGridPathAvoidsOppositeCorner
namespace GlobalTheory.SplitFlip

def vertexDiff (X : ℕ × ℕ) : ℤ := (X.1 : ℤ) - X.2

theorem vertexDiff_tgt (e : Edge) : vertexDiff e.tgt = vertexDiff e.src + 1 := by
  cases e <;> simp [vertexDiff, Edge.src, Edge.tgt] <;> omega

theorem IsPath.pairwise_vertexDiff : ∀ {γ : List Edge}, IsPath γ →
    γ.Pairwise fun a b => vertexDiff a.src < vertexDiff b.src := by
  intro γ h
  let r : Edge → Edge → Prop := fun a b => vertexDiff a.src < vertexDiff b.src
  let : Trans r r r := ⟨fun hab hbc => lt_trans hab hbc⟩
  change γ.Pairwise r
  apply List.IsChain.pairwise
  refine List.IsChain.imp (fun {a b} hab => ?_) h
  change vertexDiff a.src < vertexDiff b.src
  rw [← hab, vertexDiff_tgt]
  omega

theorem IsPath.eq_of_vertexDiff_eq {γ : List Edge} (hγ : IsPath γ) {a b : Edge} (ha : a ∈ γ) (hb : b ∈ γ)
    (h : vertexDiff a.src = vertexDiff b.src) : a = b := by
  by_contra hne
  have hpw := hγ.pairwise_vertexDiff
  have key : ∀ {l : List Edge}, l.Pairwise (fun a b => vertexDiff a.src < vertexDiff b.src) →
      ∀ {a b : Edge}, a ∈ l → b ∈ l → a ≠ b → vertexDiff a.src ≠ vertexDiff b.src := by
    intro l hl
    induction hl with
    | nil => intro a b ha; simp at ha
    | @cons x l hx _ ih =>
      intro a b ha hb hab
      rcases List.mem_cons.1 ha with rfl | ha' <;> rcases List.mem_cons.1 hb with rfl | hb'
      · exact absurd rfl hab
      · exact (hx b hb').ne
      · exact (hx a ha').ne'
      · exact ih ha' hb' hab
  exact key hpw ha hb hne h

theorem pathAvoid : ∀ {γ : List Edge} {i j : ℕ}, IsPath γ → PassesThrough i j γ →
    ∀ b ∈ γ, b.src ≠ (i + 1, j + 1) ∧ b.tgt ≠ (i + 1, j + 1) := by
  intro γ i j hγ hp b hb
  have hθ : Edge.theta i j ∈ γ := hp.subset (by simp)
  have hx : Edge.ex i j ∈ γ := hp.subset (by simp)
  refine ⟨fun hs => ?_, fun ht => ?_⟩
  · have := hγ.eq_of_vertexDiff_eq hb hx (by rw [hs]; simp [vertexDiff, Edge.src])
    subst this
    simp [Edge.src] at hs
  · have h1 := vertexDiff_tgt b
    rw [ht] at h1
    have := hγ.eq_of_vertexDiff_eq hb hθ (by simp [vertexDiff, Edge.src] at h1 ⊢; omega)
    subst this
    simp [Edge.tgt] at ht

end GlobalTheory.SplitFlip
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitThetaGridPathAvoidsOppositeCornerStatement
open GlobalTheory.SplitFlip
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitThetaGridPath_avoids_opposite_corner : ∀ {γ : List Edge} {i j : ℕ}, IsPath γ → PassesThrough i j γ → ∀ b ∈ γ, b.src ≠ (i + 1, j + 1) ∧ b.tgt ≠ (i + 1, j + 1) := by
  first | exact @GlobalTheory.SplitFlip.pathAvoid | exact GlobalTheory.SplitFlip.pathAvoid | (intros; apply GlobalTheory.SplitFlip.pathAvoid <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLatticeChainLatAndComap
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.Imports
namespace GlobalTheory.SmulMemOfMemSpan

theorem exists_smul_mem_of_mem_span {R K V : Type} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [AddCommGroup V] [Module R V] [Module K V]
    [IsScalarTower R K V] (M : Submodule R V) {v : V}
    (hv : v ∈ Submodule.span K (M : Set V)) : ∃ a : R, a ≠ 0 ∧ a • v ∈ M := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [mul_comm a b, mul_smul]; exact M.smul_mem b hax
    · rw [mul_smul]; exact M.smul_mem a hby
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.surj (nonZeroDivisors R) c
    dsimp only at hnd
    refine ⟨d * a, mul_ne_zero (nonZeroDivisors.ne_zero d.2) ha, ?_⟩
    have key : (d : R) • c • x = n • x := by
      rw [← algebraMap_smul K (d : R) (c • x), smul_smul, mul_comm, hnd, algebraMap_smul]
    rw [mul_comm (d : R) a, mul_smul, key, smul_comm a n x]
    exact M.smul_mem n hax

theorem main : ∀ {R K V : Type} [inst : CommRing R] [IsDomain R] [inst_2 : Field K] [inst_3 : Algebra R K] [IsFractionRing R K] [inst_5 : AddCommGroup V] [inst_6 : Module R V] [inst_7 : Module K V] [IsScalarTower R K V] (M : Submodule R V) {v : V}, v ∈ Submodule.span K (↑M : Set V) → ∃ (a : R), a ≠ (0 : R) ∧ a • v ∈ M :=
  by
  intro R K V _ _ _ _ _ _ _ _ _ M v hv
  exact exists_smul_mem_of_mem_span M hv

end GlobalTheory.SmulMemOfMemSpan
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ImportsAlt
namespace GlobalTheory.LemmaTwoFortyThirteen

theorem main {R K V : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
    (M : Submodule R V) (h : ∀ v : V, ∃ a : R, a ≠ (0 : R) ∧ a • v ∈ M) :
    Submodule.span K (↑M : Set V) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  obtain ⟨a, ha, hav⟩ := h v
  have hK : algebraMap R K a ≠ 0 := by
    simpa using (IsFractionRing.injective R K).ne ha
  have hv : v = (algebraMap R K a)⁻¹ • (a • v) := by
    rw [← algebraMap_smul K a v, smul_smul, inv_mul_cancel₀ hK, one_smul]
  rw [hv]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hav)

end GlobalTheory.LemmaTwoFortyThirteen
end

open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms GlobalTheory.RootEx.UnfoldShape

namespace GlobalTheory.RootEx.ChainLattice

theorem exists_smul_mem {R K V : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
    (M : Submodule R V) {v : V} (hv : v ∈ Submodule.span K (M : Set V)) :
    ∃ a : R, a ≠ 0 ∧ a • v ∈ M := by
  first
  | (rename_i h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11; revert R K V h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 M v hv; exact @_root_.GlobalTheory.SmulMemOfMemSpan.main)
  | exact @_root_.GlobalTheory.SmulMemOfMemSpan.main
  | exact _root_.GlobalTheory.SmulMemOfMemSpan.main
  | (apply _root_.GlobalTheory.SmulMemOfMemSpan.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.SmulMemOfMemSpan.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SmulMemOfMemSpan.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SmulMemOfMemSpan.main ..)

theorem span_eq_top_of_smul_mem {R K V : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
    (M : Submodule R V) (h : ∀ v : V, ∃ a : R, a ≠ 0 ∧ a • v ∈ M) :
    Submodule.span K (M : Set V) = ⊤ := by
  first
  | (rename_i h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11; revert R K V h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 M h; exact @_root_.GlobalTheory.LemmaTwoFortyThirteen.main)
  | exact @_root_.GlobalTheory.LemmaTwoFortyThirteen.main
  | exact _root_.GlobalTheory.LemmaTwoFortyThirteen.main
  | (apply _root_.GlobalTheory.LemmaTwoFortyThirteen.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.LemmaTwoFortyThirteen.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LemmaTwoFortyThirteen.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LemmaTwoFortyThirteen.main ..)

theorem isLattice_chainLat_and_comap :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (n : Type) [Fintype n] [DecidableEq n] (c : ℕ),
      (∀ (ϖ : 𝒪[k]), (ϖ : k) ≠ 0 → ∀ L : Submodule 𝒪[k] (n → k), Submodule.IsLattice k L →
        Submodule.IsLattice k (chainLat ϖ c L)) ∧
      ∀ Λ : Submodule 𝒪[k] (n ⊕ Fin c → k), Submodule.IsLattice k Λ →
        Submodule.IsLattice k (Λ.comap (inX k n c)) := by
  intro k _ _ _ _ n _ _ c
  refine ⟨fun ϖ hϖ L hL => ⟨?_, ?_⟩, fun Λ hΛ => ⟨?_, ?_⟩⟩
  · exact (hL.fg.map _).sup (Submodule.fg_span (Set.finite_range _))
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli
  · refine Submodule.fg_of_fg_map_injective (inX k n c) ?_
      (hΛ.fg.of_le (Submodule.map_comap_le _ _))
    intro x y hxy
    funext r
    have := congrFun hxy (Sum.inl r)
    simpa [inX_apply] using this
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli

end GlobalTheory.RootEx.ChainLattice
end
