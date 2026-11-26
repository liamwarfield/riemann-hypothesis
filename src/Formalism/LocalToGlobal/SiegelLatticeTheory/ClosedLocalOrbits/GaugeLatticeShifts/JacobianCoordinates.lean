module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.InfCut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObjInhab
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormCoreGamProdSum
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHNeat
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDictK
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RowsAbsX

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacobianCoordinates
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal ComplexConjugate
open Matrix

namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting

variable {n r : ℕ}

def SLoc (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) : Set (Formalism.REAL.UJ ε) :=
  {g | InS e z (uMat g)}

def IsHaarS {ε : Fin n → Bool} (S : Set (Formalism.REAL.UJ ε)) (μ : Measure (Formalism.REAL.UJ ε)) : Prop :=
  IsHaarLoc S μ ∧ IsFiniteMeasureOnCompacts μ

structure FrameLoc (ε : Fin n → Bool) (k : ℕ) (e : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) (T T' : ℝ) : Prop where
  dim : n = 2 * r + 1 + k
  k_pos : 1 ≤ k
  sig : (Finset.univ.filter (fun i => ε i = false)).card = r + 1
  e_li : LinearIndependent ℂ e
  ee : ∀ a b, hJ ε (e a) (e b) = 0
  ez : ∀ a, hJ ε (e a) z = 0
  ez' : ∀ a, hJ ε (e a) z' = 0
  zz : hJ ε z z = -(T : ℂ)
  zz' : hJ ε z' z' = -(T' : ℂ)
  T_pos : 0 < T
  T'_pos : 0 < T'

def ZLoc (ε : Fin n → Bool) (sc : ℝ) (e : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) (g : Formalism.REAL.UJ ε) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ :=
  Zhat ε (famSc sc e z) (famSc sc e z') (uMat g)

def GoodLoc (T T' : ℝ) : Set (Fin (r + 1) → ℂ) :=
  {c | (∀ l, c l ≠ 0) ∧ 0 < Gv T T' (Matrix.diagonal c)}

def wtLoc (k : ℕ) (T T' : ℝ) (c : Fin (r + 1) → ℂ) : ℝ :=
  Gv T T' (Matrix.diagonal c) ^ (k - 1) * JacV (Matrix.diagonal c)

def dcLoc : Measure (Fin (r + 1) → ℂ) :=
  Measure.pi fun _ => (2 : ℝ≥0∞) • (volume : Measure ℂ)

def IsSecLoc (ε : Fin n → Bool) (sc : ℝ) (e : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) (T T' : ℝ)
    (h : (Fin (r + 1) → ℂ) → Formalism.REAL.UJ ε) : Prop :=
  ∀ c ∈ GoodLoc (r := r) T T', ZLoc ε sc e z z' (h c) = Matrix.diagonal c

def DisintLoc (ε : Fin n → Bool) (k : ℕ) (T T' : ℝ) (μS μS' : Measure (Formalism.REAL.UJ ε))
    (h : (Fin (r + 1) → ℂ) → Formalism.REAL.UJ ε) (C : ℝ) : Prop :=
  ∀ φ : Formalism.REAL.UJ ε → ℝ≥0∞, Measurable φ →
    ∫⁻ x, φ x ∂(Formalism.REAL.muG ε) =
      ∫⁻ c in GoodLoc (r := r) T T', ENNReal.ofReal (C * wtLoc k T T' c) *
        ∫⁻ s, ∫⁻ s', φ (s * h c * s'⁻¹) ∂μS' ∂μS ∂(dcLoc (r := r))

def JacLoc : Prop :=
  ∀ (n r k : ℕ) (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) (T T' sc : ℝ),
    FrameLoc ε k e z z' T T' → 0 < sc →
    ∀ μS μS' : Measure (Formalism.REAL.UJ ε), IsHaarS (SLoc ε e z) μS → IsHaarS (SLoc ε e z') μS' →
    ∀ h, IsSecLoc ε sc e z z' T T' h → ∃ C, 0 < C ∧ DisintLoc ε k T T' μS μS' h C

def DiagDCLoc : Prop :=
  ∀ (n r k : ℕ) (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) (T T' sc : ℝ),
    FrameLoc ε k e z z' T T' →
    ∀ c ∈ GoodLoc (r := r) T T', ∀ g g' : Formalism.REAL.UJ ε,
      ZLoc ε sc e z z' g = Matrix.diagonal c → ZLoc ε sc e z z' g' = Matrix.diagonal c →
      ∃ s ∈ SLoc ε e z, ∃ s' ∈ SLoc ε e z', g' = s * g * s'⁻¹

def SecMeasLoc : Prop :=
  ∀ (n r k : ℕ) (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) (T T' sc : ℝ),
    FrameLoc ε k e z z' T T' → 0 < sc → ∃ h, Measurable h ∧ IsSecLoc ε sc e z z' T T' h

def NLoc (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) : Set (Formalism.REAL.UJ ε) :=
  {g | InN ε e z (uMat g)}

def HLoc (ε : Fin n → Bool) (e p : Fin r → Fin n → ℂ) (z : Fin n → ℂ) : Set (Formalism.REAL.UJ ε) :=
  {g | (∀ a, uMat g *ᵥ e a = e a) ∧ (∀ a, uMat g *ᵥ p a = p a) ∧ uMat g *ᵥ z = z}

def UnimodLoc : Prop :=
  ∀ (n r k : ℕ) (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) (T T' : ℝ),
    FrameLoc ε k e z z' T T' →
    ∀ μ : Measure (Formalism.REAL.UJ ε), IsHaarS (SLoc ε e z) μ →
    ∀ s ∈ SLoc ε e z, μ.map (fun x => x * s) = μ

def NHLoc : Prop :=
  ∀ (n r k : ℕ) (ε : Fin n → Bool) (e p : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) (T T' : ℝ),
    FrameLoc ε k e z z' T T' → (∀ a b, hJ ε (e a) (p b) = if a = b then 1 else 0) → (∀ a b, hJ ε (p a) (p b) = 0) →
    (∀ b, hJ ε z (p b) = 0) →
    ∀ μN μH : Measure (Formalism.REAL.UJ ε), IsHaarS (NLoc ε e z) μN → IsHaarS (HLoc ε e p z) μH →
    IsHaarS (SLoc ε e z) ((μN.prod μH).map (fun q => q.1 * q.2))

def P5 : Prop := JacLoc → DiagDCLoc → SecMeasLoc → UnimodLoc → NHLoc → StepReal → HaarDisintegrationReal

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ProductExactness
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ComplexConjugate
open Matrix

namespace Formalism.L2.SG.RealObj.InfCut.ProductExactness

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting

def WittGram : Prop :=
  ∀ (n m : ℕ) (ε : Fin n → Bool) (x y : Fin m → Fin n → ℂ),
    (∀ i j, hJ ε (x i) (x j) = hJ ε (y i) (y j)) →
    (Matrix.of fun i j => hJ ε (x i) (x j)).det ≠ 0 → ∃ g : Formalism.REAL.UJ ε, ∀ i, uMat g *ᵥ x i = y i

section Pure

variable {n : ℕ} (ε : Fin n → Bool)

theorem hJ_smul_l (a : ℂ) (x y : Fin n → ℂ) : hJ ε (a • x) y = conj a * hJ ε x y := by
  unfold hJ
  rw [star_smul, smul_dotProduct, smul_eq_mul]
  rfl

theorem hJ_smul_r (a : ℂ) (x y : Fin n → ℂ) : hJ ε x (a • y) = a * hJ ε x y := by
  unfold hJ
  rw [mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem hJ_add_l (x x' y : Fin n → ℂ) : hJ ε (x + x') y = hJ ε x y + hJ ε x' y := by
  unfold hJ
  rw [star_add, add_dotProduct]

theorem hJ_add_r (x y y' : Fin n → ℂ) : hJ ε x (y + y') = hJ ε x y + hJ ε x y' := by
  unfold hJ
  rw [mulVec_add, dotProduct_add]

theorem hJ_cj (x y : Fin n → ℂ) : hJ ε x y = conj (hJ ε y x) :=
  Formalism.L2.SG.PoincareInHH.Cut.hJ_conj ε x y

theorem hJ_zero_of_cj {x y : Fin n → ℂ} (h : hJ ε y x = 0) : hJ ε x y = 0 := by
  rw [hJ_cj, h, map_zero]

theorem witt_idx (W : WittGram) {ι : Type} [Fintype ι] [DecidableEq ι] (x y : ι → Fin n → ℂ)
    (hG : ∀ i j, hJ ε (x i) (x j) = hJ ε (y i) (y j))
    (hnd : (Matrix.of fun i j => hJ ε (x i) (x j)).det ≠ 0) :
    ∃ g : Formalism.REAL.UJ ε, ∀ i, uMat g *ᵥ x i = y i := by
  let e := Fintype.equivFin ι
  have hM : (Matrix.of fun i j => hJ ε ((x ∘ e.symm) i) ((x ∘ e.symm) j)) =
      Matrix.reindex e e (Matrix.of fun i j => hJ ε (x i) (x j)) := by
    ext i j; rfl
  obtain ⟨g, hg⟩ := W n (Fintype.card ι) ε (x ∘ e.symm) (y ∘ e.symm) (fun i j => hG _ _)
    (by rw [hM, Matrix.det_reindex_self]; exact hnd)
  exact ⟨g, fun i => by simpa using hg (e i)⟩

def tup {r : ℕ} (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ) : (Fin r ⊕ Fin r) ⊕ Unit → Fin n → ℂ
  | .inl (.inl a) => e a
  | .inl (.inr a) => f a
  | .inr _ => z

theorem normSq_last_sub_pos_of_Gv_diagonal_pos {r : ℕ} (T T' : ℝ) (c : Fin (r + 1) → ℂ) (hG : 0 < Gv T T' (Matrix.diagonal c)) :
    0 < ‖c (Fin.last r)‖ ^ 2 - T * T' := by
  have h1 := Dl_diagonal c (r + 1) le_rfl
  have h2 := Dl_diagonal c r (Nat.le_succ r)
  rw [Fin.prod_univ_castSucc] at h1
  set P := ∏ i : Fin r, c (Fin.castSucc i)
  have e1 : (∏ i : Fin r, c (Fin.castLE le_rfl (Fin.castSucc i))) = P :=
    Finset.prod_congr rfl fun i _ => by congr 1
  have e2 : (∏ i : Fin r, c (Fin.castLE (Nat.le_succ r) i)) = P :=
    Finset.prod_congr rfl fun i _ => by congr 1
  have e3 : Fin.castLE (le_refl (r + 1)) (Fin.last r) = Fin.last r := Fin.ext rfl
  rw [e1, e3] at h1
  rw [e2] at h2
  unfold Gv at hG
  rw [h1, h2, norm_mul, mul_pow] at hG
  by_contra hn
  push Not at hn
  have hP : 0 ≤ ‖P‖ ^ 2 := sq_nonneg _
  nlinarith

theorem real_loc (W : WittGram) {r : ℕ} (e f : Fin r → Fin n → ℂ) (z z' w : Fin n → ℂ) (T T' sc : ℝ)
    (hee : ∀ a b, hJ ε (e a) (e b) = 0) (hff : ∀ a b, hJ ε (f a) (f b) = 0)
    (hef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0)
    (hez : ∀ a, hJ ε (e a) z = 0) (hfz : ∀ a, hJ ε (f a) z = 0)
    (hez' : ∀ a, hJ ε (e a) z' = 0) (hfz' : ∀ a, hJ ε (f a) z' = 0)
    (hzz : hJ ε z z = -(T : ℂ)) (hz'z' : hJ ε z' z' = -(T' : ℂ))
    (hew : ∀ a, hJ ε (e a) w = 0) (hfw : ∀ a, hJ ε (f a) w = 0) (hzw : hJ ε z w = 0)
    (hww : hJ ε w w = 1) (hT : 0 < T) (hT' : 0 < T') (hsc : 0 < sc)
    (c : Fin (r + 1) → ℂ) (hc : ∀ l, c l ≠ 0) (hG : 0 < Gv T T' (Matrix.diagonal c)) :
    ∃ g : Formalism.REAL.UJ ε, Zhat ε (famSc sc e z) (famSc sc e z') (uMat g) = Matrix.diagonal c := by
  have hsc0 : (sc : ℂ) ≠ 0 := by exact_mod_cast hsc.ne'
  have hT0 : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  have hT'0 : (T' : ℂ) ≠ 0 := by exact_mod_cast hT'.ne'
  have hfe : ∀ a b, hJ ε (f a) (e b) = if a = b then 1 else 0 := fun a b => by
    rw [hJ_cj, hef]; split_ifs with h1 h2 h2 <;> simp_all
  have hze : ∀ a, hJ ε z (e a) = 0 := fun a => hJ_zero_of_cj ε (hez a)
  have hzf : ∀ a, hJ ε z (f a) = 0 := fun a => hJ_zero_of_cj ε (hfz a)
  have hz'e : ∀ a, hJ ε z' (e a) = 0 := fun a => hJ_zero_of_cj ε (hez' a)
  have hz'f : ∀ a, hJ ε z' (f a) = 0 := fun a => hJ_zero_of_cj ε (hfz' a)
  have hwe : ∀ a, hJ ε w (e a) = 0 := fun a => hJ_zero_of_cj ε (hew a)
  have hwf : ∀ a, hJ ε w (f a) = 0 := fun a => hJ_zero_of_cj ε (hfw a)
  have hwz : hJ ε w z = 0 := hJ_zero_of_cj ε hzw
  set sf : Fin r → ℂ := fun b => ((sc : ℂ) ^ (r - b.1))⁻¹ with hsf
  have hsf0 : ∀ b, sf b ≠ 0 := fun b => inv_ne_zero (pow_ne_zero _ hsc0)
  have hsfc : ∀ b, conj (sf b) = sf b := fun b => by
    simp only [hsf, map_inv₀, map_pow, Complex.conj_ofReal]
  set lam : Fin r → ℂ := fun b => c (Fin.castSucc b) / (sf b * sf b) with hlam
  have hlam0 : ∀ b, lam b ≠ 0 := fun b => div_ne_zero (hc _) (mul_ne_zero (hsf0 b) (hsf0 b))
  have hclam0 : ∀ b, conj (lam b) ≠ 0 := fun b => (map_ne_zero _).2 (hlam0 b)
  set cl := c (Fin.last r) with hcl
  have hgap := normSq_last_sub_pos_of_Gv_diagonal_pos T T' c hG
  set q : ℝ := ‖cl‖ ^ 2 / T - T' with hq
  have hq0 : 0 ≤ q := by
    rw [hq, div_sub' hT.ne']
    exact div_nonneg (by nlinarith) hT.le
  set α : ℂ := -cl / T with hα
  set β : ℂ := ((Real.sqrt q : ℝ) : ℂ) with hβ
  have hββ : conj β * β = (q : ℂ) := by
    rw [hβ, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt hq0]
  have hαα : conj α * α * (-(T : ℂ)) + (q : ℂ) = -(T' : ℂ) := by
    rw [← Complex.normSq_eq_conj_mul_self, hα, Complex.normSq_div, Complex.normSq_neg,
      Complex.normSq_ofReal, Complex.normSq_eq_norm_sq, hq]
    push_cast
    field_simp
    ring
  let x := tup e f z'
  let y := tup (fun b => lam b • f b) (fun b => (conj (lam b))⁻¹ • e b) (α • z + β • w)
  have hGram : ∀ i j, hJ ε (x i) (x j) = hJ ε (y i) (y j) := by
    intro i j
    rcases i with (a | a) | ⟨⟩ <;> rcases j with (b | b) | ⟨⟩ <;>
      simp only [x, y, tup, hJ_smul_l, hJ_smul_r, hJ_add_l, hJ_add_r, hee, hff, hef, hfe, hez, hfz, hez', hfz',
        hze, hzf, hz'e, hz'f, hew, hfw, hzw, hwe, hwf, hwz, hww, hzz, hz'z', mul_zero, add_zero,
        zero_add, mul_one]
    · split_ifs with h
      · subst h
        rw [mul_one, inv_mul_cancel₀ (hclam0 a)]
      · simp
    · split_ifs with h
      · subst h
        simp only [map_inv₀, Complex.conj_conj, mul_one]
        exact (mul_inv_cancel₀ (hlam0 a)).symm
      · simp
    · rw [← hαα, ← hββ]
      ring
  have hnd : (Matrix.of fun i j => hJ ε (x i) (x j)).det ≠ 0 := by
    intro hdet
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
    apply hv0
    have hA : ∀ a, v (.inl (.inr a)) = 0 := fun a => by
      have h1 := congrFun hv (.inl (.inl a))
      simpa [mulVec, dotProduct, Fintype.sum_sum_type, x, tup, hee, hef, hez'] using h1
    have hB : ∀ a, v (.inl (.inl a)) = 0 := fun a => by
      have h1 := congrFun hv (.inl (.inr a))
      simpa [mulVec, dotProduct, Fintype.sum_sum_type, x, tup, hff, hfe, hfz'] using h1
    have hC : v (.inr ()) = 0 := by
      have h1 := congrFun hv (.inr ())
      simp [mulVec, dotProduct, Fintype.sum_sum_type, x, tup, hz'e, hz'f, hz'z'] at h1
      tauto
    funext i
    rcases i with (a | a) | ⟨⟩
    · exact hB a
    · exact hA a
    · exact hC
  obtain ⟨g, hg⟩ := witt_idx ε W x y hGram hnd
  have hge : ∀ b, uMat g *ᵥ e b = lam b • f b := fun b => hg (.inl (.inl b))
  have hgz : uMat g *ᵥ z' = α • z + β • w := hg (.inr ())
  refine ⟨g, ?_⟩
  have hne : ∀ b : Fin r, Fin.last r ≠ Fin.castSucc b := fun b h => Fin.castSucc_ne_last b h.symm
  ext a b
  refine Fin.lastCases ?_ (fun a => ?_) a <;> refine Fin.lastCases ?_ (fun b => ?_) b
  · simp only [Zhat, famSc, fam, Fin.snoc_last, Fin.val_last, Nat.sub_self, pow_zero, inv_one, one_smul, hgz,
      hJ_add_r, hJ_smul_r, hzz, hzw, mul_zero, add_zero, Matrix.diagonal_apply_eq, hα, hcl]
    field_simp
  · simp only [Zhat, famSc, fam, Fin.snoc_last, Fin.snoc_castSucc, Fin.val_last, Nat.sub_self, pow_zero, inv_one,
      one_smul, mulVec_smul, hge, hJ_smul_r, hzf, mul_zero, Matrix.diagonal_apply_ne _ (hne b)]
  · simp only [Zhat, famSc, fam, Fin.snoc_last, Fin.snoc_castSucc, Fin.val_last, Nat.sub_self, pow_zero, inv_one,
      one_smul, hgz, hJ_smul_l, hJ_add_r, hJ_smul_r, hez, hew, mul_zero, add_zero,
      Matrix.diagonal_apply_ne _ (hne a).symm]
  · simp only [Zhat, famSc, fam, Fin.snoc_castSucc, Fin.val_castSucc, mulVec_smul, hge, hJ_smul_l, hJ_smul_r, hef,
      Matrix.diagonal_apply, Fin.castSucc_inj]
    split_ifs with h
    · subst h
      have := hsfc a
      simp only [hsf] at this
      rw [this, hlam]
      simp only [hsf]
      field_simp
    · simp

end Pure

section Glob

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem hJ_X (v : InfinitePlace X.B.I.F) (p q : (Formalism.MainNotions.S.VS D).V) :
    hJ (X.B.I.ε v) (rv X.B.I v (X.crd p)) (rv X.B.I v (X.crd q)) = embS D (X.pl v) ((Formalism.MainNotions.S.VS D).hT p q) :=
  Formalism.L2.SG.PoincareInHH.Cut.hJ_crd X v p q

theorem Tw_pos (u : D.what₂.Word) : 0 < Tw (D := D) u := by
  unfold Tw
  exact_mod_cast (D.mem u).A.T_prime.pos

theorem stepReal_of_witt (W : WittGram) : StepReal := by
  intro D X u u' sc hsc c hc
  have hk : 0 < D.R.k := by have := D.R.m_add_three_le_k; omega
  simp only [Good, Set.mem_ofPred_eq] at hc
  have key : ∀ v, ∃ g : Formalism.REAL.UJ (X.B.I.ε v),
      Zhat (X.B.I.ε v) (frm X u sc v) (frm X u' sc v) (uMat g) = Matrix.diagonal (c v) := by
    intro v
    have h0 : ∀ a b, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.eR b)) = 0 := fun a b =>
      (hJ_X X v _ _).trans (by rw [X.ee]; simp)
    have h1 : ∀ a b, hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) (rv X.B.I v (X.fR b)) = 0 := fun a b =>
      (hJ_X X v _ _).trans (by rw [X.ff]; simp)
    have h2 : ∀ a b, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.fR b)) = if a = b then 1 else 0 :=
      fun a b => (hJ_X X v _ _).trans (by rw [X.ef]; split_ifs <;> simp)
    have h3 : ∀ (w : D.what₂.Word) a, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR w)) = 0 := fun w a =>
      (hJ_X X v _ _).trans (by rw [(X.zu_orth w a).1]; simp)
    have h4 : ∀ (w : D.what₂.Word) a, hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) (rv X.B.I v (X.zR w)) = 0 := fun w a =>
      (hJ_X X v _ _).trans (by rw [(X.zu_orth w a).2]; simp)
    have h5 : ∀ (w : D.what₂.Word), hJ (X.B.I.ε v) (rv X.B.I v (X.zR w)) (rv X.B.I v (X.zR w)) = -(Tw (D := D) w : ℂ) :=
      fun w => (hJ_X X v _ _).trans (by rw [X.zu_norm w]; simp [Tw])
    have hw := X.wfr_perp u v ⟨0, hk⟩
    have hww : hJ (X.B.I.ε v) (X.wfr u v ⟨0, hk⟩) (X.wfr u v ⟨0, hk⟩) = 1 := by
      rw [X.wfr_on]; simp
    exact real_loc (X.B.I.ε v) W (fun a => rv X.B.I v (X.eR a)) (fun a => rv X.B.I v (X.fR a))
      (rv X.B.I v (X.zR u)) (rv X.B.I v (X.zR u')) (X.wfr u v ⟨0, hk⟩) (Tw u) (Tw u') sc h0 h1 h2 (h3 u) (h4 u)
      (h3 u') (h4 u') (h5 u) (h5 u') (fun a => (hw.1 a).1) (fun a => (hw.1 a).2) hw.2 hww (Tw_pos u) (Tw_pos u')
      hsc (c v) (hc v).1 (hc v).2
  choose γ hγ using key
  exact ⟨γ, fun v => hγ v⟩

end Glob

end Formalism.L2.SG.RealObj.InfCut.ProductExactness
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RankOneTensors
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace Formalism.L2.SG.RealObj.RankOneTensors

open Formalism.L2.SG.RealObj

section Rk1

variable {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V']

theorem norm_rankOneInnerOperator (a : V) (b : V') : ‖TermOp.rk1 a b‖ = ‖a‖ * ‖b‖ := by
  unfold TermOp.rk1
  rw [ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm, mul_comm]

theorem continuous_rankOneOperator {T : Type*} [TopologicalSpace T] {f : T → V} {g : T → V'} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun x => TermOp.rk1 (f x) (g x) := by
  have h1 : Continuous fun x => innerSL ℂ (g x) := (innerSL ℂ).continuous.comp hg
  have h2 : Continuous fun x => ContinuousLinearMap.smulRightL ℂ V' V (innerSL ℂ (g x)) :=
    (ContinuousLinearMap.smulRightL ℂ V' V).continuous.comp h1
  unfold TermOp.rk1
  exact h2.clm_apply hf

end Rk1

section Tens

variable {ι : Type*} [Fintype ι] {V : ι → Type*} [∀ v, NormedAddCommGroup (V v)] [∀ v, InnerProductSpace ℂ (V v)]
  {Vt : Type*} [NormedAddCommGroup Vt] [InnerProductSpace ℂ Vt] (T : (∀ v, V v) → Vt)

theorem norm_tens (hT : ∀ x y, ⟪T x, T y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ) (x : ∀ v, V v) : ‖T x‖ = ∏ v, ‖x v‖ := by
  have h := hT x x
  simp only [inner_self_eq_norm_sq_to_K] at h
  have h' : ‖T x‖ ^ 2 = (∏ v, ‖x v‖) ^ 2 := by
    rw [← Finset.prod_pow]
    exact_mod_cast h
  exact (pow_left_inj₀ (norm_nonneg _) (Finset.prod_nonneg fun _ _ => norm_nonneg _) two_ne_zero).1 h'

theorem tens_eq_zero (hT : ∀ x y, ⟪T x, T y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ) (x : ∀ v, V v) (v0 : ι) (h0 : x v0 = 0) :
    T x = 0 := by
  rw [← norm_eq_zero, norm_tens T hT x]
  exact Finset.prod_eq_zero (Finset.mem_univ v0) (by rw [h0, norm_zero])

theorem eq_of_inner_tens (hS : Submodule.span ℂ (Set.range T) = ⊤) (a b : Vt)
    (h : ∀ z, ⟪T z, a⟫_ℂ = ⟪T z, b⟫_ℂ) : a = b := by
  rw [← sub_eq_zero]
  have hmem : ∀ w ∈ Submodule.span ℂ (Set.range T), ⟪w, a - b⟫_ℂ = 0 := by
    intro w hw
    refine Submodule.span_induction (fun y hy => ?_) ?_ (fun y z _ _ hy hz => ?_) (fun c y _ hy => ?_) hw
    · obtain ⟨z, rfl⟩ := hy
      rw [inner_sub_right, h z, sub_self]
    · exact inner_zero_left _
    · rw [inner_add_left, hy, hz, add_zero]
    · rw [inner_smul_left, hy, mul_zero]
  have h2 := hmem (a - b) (by rw [hS]; exact Submodule.mem_top)
  exact inner_self_eq_zero.mp h2

end Tens

section Fact

variable {ι : Type*} [Fintype ι] {G : ι → Type*} [∀ v, Group (G v)] [∀ v, TopologicalSpace (G v)]
  [∀ v, IsTopologicalGroup (G v)] [∀ v, MeasurableSpace (G v)] [∀ v, BorelSpace (G v)]
  [∀ v, SecondCountableTopology (G v)] (μ : ∀ v, Measure (G v)) [∀ v, SigmaFinite (μ v)]
  {V V' : ι → Type*} [∀ v, NormedAddCommGroup (V v)] [∀ v, InnerProductSpace ℂ (V v)]
  [∀ v, FiniteDimensional ℂ (V v)] [∀ v, NormedAddCommGroup (V' v)] [∀ v, InnerProductSpace ℂ (V' v)]
  [∀ v, FiniteDimensional ℂ (V' v)]
  {Vt Vt' : Type*} [NormedAddCommGroup Vt] [InnerProductSpace ℂ Vt] [FiniteDimensional ℂ Vt]
  [NormedAddCommGroup Vt'] [InnerProductSpace ℂ Vt'] [FiniteDimensional ℂ Vt']
  (T : (∀ v, V v) → Vt) (T' : (∀ v, V' v) → Vt')
  (hT : ∀ x y, ⟪T x, T y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ) (hT' : ∀ x y, ⟪T' x, T' y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ)
  (hS : Submodule.span ℂ (Set.range T) = ⊤)
  (W : ∀ v, G v → V v) (W' : ∀ v, G v → V' v) (hW : ∀ v, Continuous (W v)) (hW' : ∀ v, Continuous (W' v))
  (Wt : (∀ v, G v) → Vt) (Wt' : (∀ v, G v) → Vt') (hWt : Continuous Wt) (hWt' : Continuous Wt')
  (hten : ∀ x, Wt x = T fun v => W v (x v)) (hten' : ∀ x, Wt' x = T' fun v => W' v (x v))


include hT hT' hS hW hW' hWt hWt' hten hten' in
theorem oo_factor (γ : ∀ v, G v) (y : ∀ v, V' v) :
    haveI : ∀ v, CompleteSpace (V v) := fun v => FiniteDimensional.complete ℂ (V v)
    haveI := FiniteDimensional.complete ℂ Vt
    (∫ x, TermOp.rk1 (Wt x) (Wt' (γ⁻¹ * x)) ∂(Measure.pi μ)) (T' y) =
      T fun v => (∫ s, TermOp.rk1 (W v s) (W' v ((γ v)⁻¹ * s)) ∂(μ v)) (y v) := by
  have : ∀ v, CompleteSpace (V v) := fun v => FiniteDimensional.complete ℂ (V v)
  have := FiniteDimensional.complete ℂ Vt
  let f : ∀ v, G v → (V' v →L[ℂ] V v) := fun v s => TermOp.rk1 (W v s) (W' v ((γ v)⁻¹ * s))
  let F : (∀ v, G v) → (Vt' →L[ℂ] Vt) := fun x => TermOp.rk1 (Wt x) (Wt' (γ⁻¹ * x))
  show (∫ x, F x ∂(Measure.pi μ)) (T' y) = T fun v => (∫ s, f v s ∂(μ v)) (y v)
  have hfc : ∀ v, Continuous (f v) := fun v =>
    continuous_rankOneOperator (hW v) ((hW' v).comp (continuous_const.mul continuous_id))
  have hFc : Continuous F := continuous_rankOneOperator hWt (hWt'.comp (continuous_const.mul continuous_id))
  have hnorm : ∀ x, ‖F x‖ = ∏ v, ‖f v (x v)‖ := by
    intro x
    simp only [F, f, norm_rankOneInnerOperator, hten, hten', norm_tens T hT, norm_tens T' hT', Finset.prod_mul_distrib]
    rfl
  have hzero : ∀ v0, ¬ Integrable (f v0) (μ v0) → (T fun v => (∫ s, f v s ∂(μ v)) (y v)) = 0 := by
    intro v0 h0
    refine tens_eq_zero T hT _ v0 ?_
    show (∫ s, f v0 s ∂(μ v0)) (y v0) = 0
    rw [integral_undef h0, ContinuousLinearMap.zero_apply]
  by_cases hF : Integrable F (Measure.pi μ)
  · by_cases hloc : ∀ v, Integrable (f v) (μ v)
    · refine eq_of_inner_tens T hS _ _ fun z => ?_
      rw [ContinuousLinearMap.integral_apply hF, ← integral_inner (hF.apply_continuousLinearMap _), hT]
      have hl : ∀ v, ⟪z v, (∫ s, f v s ∂(μ v)) (y v)⟫_ℂ =
          ∫ s, ⟪W' v ((γ v)⁻¹ * s), y v⟫_ℂ * ⟪z v, W v s⟫_ℂ ∂(μ v) := by
        intro v
        rw [ContinuousLinearMap.integral_apply (hloc v), ← integral_inner ((hloc v).apply_continuousLinearMap _)]
        refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
        simp only [f, TermOp.rankOneInnerOperator_apply, inner_smul_right]
      have hp : ∀ x, ⟪T z, F x (T' y)⟫_ℂ = ∏ v, ⟪W' v ((γ v)⁻¹ * x v), y v⟫_ℂ * ⟪z v, W v (x v)⟫_ℂ := by
        intro x
        simp only [F, TermOp.rankOneInnerOperator_apply, inner_smul_right, hten, hten', hT, hT', Finset.prod_mul_distrib]
        rfl
      simp only [hl, hp]
      exact integral_fintype_prod_eq_prod (μ := μ)
        (fun v s => ⟪W' v ((γ v)⁻¹ * s), y v⟫_ℂ * ⟪z v, W v s⟫_ℂ)
    · push Not at hloc
      obtain ⟨v0, h0⟩ := hloc
      rw [hzero v0 h0]
      have h0' : ¬ Integrable (fun s => ‖f v0 s‖) (μ v0) := fun h =>
        h0 ((integrable_norm_iff (hfc v0).aestronglyMeasurable).1 h)
      have hprod : ∫ x, ∏ v, ‖f v (x v)‖ ∂(Measure.pi μ) = 0 := by
        have := integral_fintype_prod_eq_prod (𝕜 := ℝ) (μ := μ) (fun v s => ‖f v s‖)
        rw [this]
        exact Finset.prod_eq_zero (Finset.mem_univ v0) (integral_undef h0')
      have hint : Integrable (fun x => ∏ v, ‖f v (x v)‖) (Measure.pi μ) := by
        have := hF.norm
        simpa only [hnorm] using this
      have h00 := (integral_eq_zero_iff_of_nonneg
        (fun x => Finset.prod_nonneg fun v _ => norm_nonneg (f v (x v))) hint).1 hprod
      have hae : F =ᵐ[Measure.pi μ] 0 := h00.mono fun x hx => by
        have h1 : ‖F x‖ = 0 := by rw [hnorm]; simpa only [Pi.zero_apply] using hx
        simpa only [Pi.zero_apply] using norm_eq_zero.1 h1
      rw [integral_congr_ae hae]
      simp
  · rw [integral_undef hF, ContinuousLinearMap.zero_apply]
    by_cases hloc : ∀ v, Integrable (f v) (μ v)
    · exfalso
      apply hF
      have hP : Integrable (fun x => ∏ v, ‖f v (x v)‖) (Measure.pi μ) :=
        Integrable.fintype_prod_dep (fun v => (hloc v).norm)
      exact hP.mono' hFc.aestronglyMeasurable (Filter.Eventually.of_forall fun x => (hnorm x).le)
    · push Not at hloc
      obtain ⟨v0, h0⟩ := hloc
      exact (hzero v0 h0).symm

end Fact

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem OOFactor_holds {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) : OOFactor X u u' := by
  intro γ y
  have h := oo_factor (fun v => Formalism.REAL.muG (X.B.I.ε v)) (X.tensU u) (X.tensU u') (X.tensU_inner u)
    (X.tensU_inner u') (X.tensU_span u) (X.Wloc u) (X.Wloc u') (X.Wloc_cont u) (X.Wloc_cont u')
    (X.Wu u) (X.Wu u') (X.Wu_spec u).2.2.1 (X.Wu_spec u').2.2.1 (X.Wu_tens u) (X.Wu_tens u') γ y
  simpa only [OOinf, Jv, TermOp.OO, Measure.restrict_univ] using h

end Formalism.L2.SG.RealObj.RankOneTensors
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormLinks
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ColFreePf
noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace Formalism.L2.SG.NormCut

section ColFreeBij

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (TR : TypedRed X) {u : D.what₂.Word}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (cs : ColSys X u what₂)

def colD (h h' : Hfin X u) : X.B.I.Gf := ((h : X.B.I.Gf) * X.xu u)⁻¹ * ((h' : X.B.I.Gf) * X.xu u)

def LeviOnto : Prop :=
  ∀ (q : {Λ // Λ ∈ what₂}) (s : Iof TR), ∃ h : Hfin X u,
    colD (cs.h (cs.base q.1)) h ∈ X.B.I.Kset ∧ colD h (cs.h (cs.base q.1)) ∈ X.B.I.Kset ∧
      levi TR (colD (cs.h (cs.base q.1)) h) = s

def ColLatRep (hK : X.LevelSubgroupCharacter) : Prop :=
  ∀ (q : {Λ // Λ ∈ what₂}) (h : Hfin X u) (ρ : cs.Cl) (γ : Gam X u) (κ : Ku X u hK),
    colD (cs.h (cs.base q.1)) h ∈ X.B.I.Kset → h = iotaF X u γ * cs.h ρ * (κ : Hfin X u) → cs.lamOf ρ = q.1

theorem UG_mul {x y : Iof TR} (hx : x ∈ UG TR) (hy : y ∈ UG TR) : x * y ∈ UG TR := fun v =>
  Formalism.L2.SG.NormCut.PsiNatEquivPf.isUni_mul (hx v) (hy v)

theorem UG_inv {x : Iof TR} (hx : x ∈ UG TR) : x⁻¹ ∈ UG TR := fun v =>
  Formalism.L2.SG.NormCut.PsiNatEquivPf.isUni_inv (hx v)

theorem colD_mul (h h' h'' : Hfin X u) : colD h h' * colD h' h'' = colD h h'' := by
  unfold colD; group

theorem colD_inv (h h' : Hfin X u) : (colD h h')⁻¹ = colD h' h := by
  unfold colD; group

theorem good_colD {h h' : Hfin X u} (hk : colD h h' ∈ X.B.I.Kset) : Good X (colD h h') :=
  colGood X u h h' hk (by have := K_inv X.B.I hk; rw [colD_inv] at this; exact this)

theorem scOf_eq (ρ : cs.Cl) : scOf TR cs ρ = levi TR (colD (cs.h (cs.base (cs.lamOf ρ))) (cs.h ρ)) := rfl

theorem colD_conj (γ h h' : Hfin X u) : colD h (γ * h) * colD h h' = colD h (γ * h') := by
  unfold colD; simp only [Subgroup.coe_mul]; group

theorem colD_ku (hK : X.LevelSubgroupCharacter) {h h' : Hfin X u} (hm : colD h h' ∈ X.K2) : h⁻¹ * h' ∈ Ku X u hK := by
  show (X.xu u)⁻¹ * ((h⁻¹ * h' : Hfin X u) : X.B.I.Gf) * X.xu u ∈ X.K2
  have e : (X.xu u)⁻¹ * ((h⁻¹ * h' : Hfin X u) : X.B.I.Gf) * X.xu u = colD h h' := by
    unfold colD; simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
  rw [e]; exact hm

theorem colFreeBij_of (hK : X.LevelSubgroupCharacter) (hR : ColReps hK cs) (hN : Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u hK) (hL : ColLatK cs)
    (hO : LeviOnto TR cs) (hRep : ColLatRep cs hK) (q : {Λ // Λ ∈ what₂}) :
    Function.Bijective (fun x : Aset TR cs q × {ρ : cs.Cl // lamQ cs ρ = q} × UG TR =>
      (x.1 : Iof TR) * scOf TR cs x.2.1.1 * (x.2.2 : Iof TR)) := by
  set hb : Hfin X u := cs.h (cs.base q.1) with hhb
  have hbl : cs.lamOf (cs.base q.1) = q.1 := cs.base_lam _ q.2
  have lamρ : ∀ ρ : {ρ : cs.Cl // lamQ cs ρ = q}, cs.lamOf ρ.1 = q.1 := fun ρ => congrArg Subtype.val ρ.2
  have kK : ∀ ρ : cs.Cl, cs.lamOf ρ = q.1 → colD hb (cs.h ρ) ∈ X.B.I.Kset := fun ρ hρ =>
    hL (cs.base q.1) ρ (hbl.trans hρ.symm)
  have kKi : ∀ ρ : cs.Cl, cs.lamOf ρ = q.1 → colD (cs.h ρ) hb ∈ X.B.I.Kset := fun ρ hρ =>
    hL ρ (cs.base q.1) (hρ.trans hbl.symm)
  have scρ : ∀ ρ : {ρ : cs.Cl // lamQ cs ρ = q}, scOf TR cs ρ.1 = levi TR (colD hb (cs.h ρ.1)) := fun ρ => by
    rw [scOf_eq, lamρ ρ]
  have aK : ∀ γ : Gam X u, ((cs.h (cs.base q.1) : X.B.I.Gf) * X.xu u)⁻¹ * (iotaF X u γ : X.B.I.Gf) *
      ((cs.h (cs.base q.1) : X.B.I.Gf) * X.xu u) = colD hb (iotaF X u γ * hb) := fun γ => by
    unfold colD; rw [hhb, Subgroup.coe_mul]; group
  constructor
  · rintro ⟨⟨a1, ha1⟩, ρ1, w1⟩ ⟨⟨a2, ha2⟩, ρ2, w2⟩ heq
    obtain ⟨γ1, hγ1K, ha1e⟩ := ha1
    obtain ⟨γ2, hγ2K, ha2e⟩ := ha2
    simp only at heq
    rw [aK] at hγ1K hγ2K ha1e ha2e
    rw [ha1e, ha2e, scρ, scρ] at heq
    rw [← levi_mul TR (good_colD hγ1K) (good_colD (kK _ (lamρ ρ1))),
      ← levi_mul TR (good_colD hγ2K) (good_colD (kK _ (lamρ ρ2))), colD_conj, colD_conj] at heq
    have hP1 : colD hb (iotaF X u γ1 * cs.h ρ1.1) ∈ X.B.I.Kset := by
      rw [← colD_conj]; exact K_mul X.B.I hγ1K (kK _ (lamρ ρ1))
    have hP2 : colD hb (iotaF X u γ2 * cs.h ρ2.1) ∈ X.B.I.Kset := by
      rw [← colD_conj]; exact K_mul X.B.I hγ2K (kK _ (lamρ ρ2))
    have hmK : colD (iotaF X u γ1 * cs.h ρ1.1) (iotaF X u γ2 * cs.h ρ2.1) ∈ X.B.I.Kset := by
      rw [← colD_mul _ hb, ← colD_inv]; exact K_mul X.B.I (K_inv X.B.I hP1) hP2
    have hlm : levi TR (colD (iotaF X u γ1 * cs.h ρ1.1) (iotaF X u γ2 * cs.h ρ2.1)) =
        (w1 : Iof TR) * (w2 : Iof TR)⁻¹ := by
      rw [← colD_mul _ hb, ← colD_inv, levi_mul TR (good_inv X (good_colD hP1)) (good_colD hP2),
        levi_inv TR (good_colD hP1)]
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, heq, mul_assoc, mul_inv_cancel, mul_one]
    have hmU : ∀ v, Formalism.L2.SG.GGMirabolic.IsUni D.R.k
        (levi TR (colD (iotaF X u γ1 * cs.h ρ1.1) (iotaF X u γ2 * cs.h ρ2.1)) v) := by
      rw [hlm]; exact UG_mul TR w1.2 (UG_inv TR w2.2)
    have hm2 := mem_level_of_unitriangular TR (good_colD hmK) (ncong_colDiff u _ _ hmK) hmU
    have hku := colD_ku hK hm2

    have hρ : ρ1.1 = ρ2.1 := by
      have hu := hR (cs.h ρ2.1)
      refine hu.unique ?_ ⟨1, 1, by simp⟩
      refine ⟨γ2⁻¹ * γ1, ⟨_, hku⟩, ?_⟩
      simp only [map_mul, map_inv]
      group
    have hρ' : ρ1 = ρ2 := Subtype.ext hρ
    subst hρ'

    have hγ : γ1 = γ2 := by
      have h0 : γ1⁻¹ * γ2 = 1 := by
        refine hN (cs.h ρ1.1) (γ1⁻¹ * γ2) ?_
        have e : (cs.h ρ1.1)⁻¹ * iotaF X u (γ1⁻¹ * γ2) * cs.h ρ1.1 =
            (iotaF X u γ1 * cs.h ρ1.1)⁻¹ * (iotaF X u γ2 * cs.h ρ1.1) := by
          simp only [map_mul, map_inv]; group
        rw [e]; exact hku
      rw [inv_mul_eq_one] at h0; exact h0
    subst hγ
    have ha : a1 = a2 := ha1e.trans ha2e.symm
    subst ha
    have hw : (w1 : Iof TR) = w2 := mul_left_cancel heq
    have : w1 = w2 := Subtype.ext hw
    subst this
    rfl
  · intro s
    obtain ⟨h, hk, hki, hs⟩ := hO q s
    obtain ⟨ρ, ⟨γ, κ, hh⟩, -⟩ := hR h
    have hlam : cs.lamOf ρ = q.1 := hRep q h ρ γ κ hk hh
    have hκ2 : colD 1 (κ : Hfin X u) ∈ X.K2 := by
      have := κ.2
      have e : colD 1 (κ : Hfin X u) = (X.xu u)⁻¹ * ((κ : Hfin X u) : X.B.I.Gf) * X.xu u := by
        unfold colD; simp only [Subgroup.coe_one, one_mul]; group
      rw [e]; exact this
    have hκK : colD 1 (κ : Hfin X u) ∈ X.B.I.Kset := hκ2.1
    have haE : colD hb (iotaF X u γ * hb) = colD hb h * (colD 1 (κ : Hfin X u))⁻¹ * colD (cs.h ρ) hb := by
      rw [hh]; unfold colD; simp only [Subgroup.coe_mul, Subgroup.coe_one, one_mul]; group
    have haK : colD hb (iotaF X u γ * hb) ∈ X.B.I.Kset := by
      rw [haE]; exact K_mul X.B.I (K_mul X.B.I hk (K_inv X.B.I hκK)) (kKi ρ hlam)
    have ga := good_colD haK
    have gr := good_colD (kK ρ hlam)
    have gk := good_colD hκK
    refine ⟨⟨⟨levi TR (colD hb (iotaF X u γ * hb)), γ, by rw [aK]; exact haK, by rw [aK]⟩,
      ⟨ρ, Subtype.ext hlam⟩, ⟨levi TR (colD 1 (κ : Hfin X u)), fun v => unitriangular_reduction_of_mem_level TR gk hκ2 v⟩⟩, ?_⟩
    simp only
    rw [show scOf TR cs ρ = levi TR (colD hb (cs.h ρ)) by rw [scOf_eq, hlam], ← levi_mul TR ga gr,
      ← levi_mul TR (good_mul X ga gr) gk, colD_conj]
    have e2 : colD hb (iotaF X u γ * cs.h ρ) * colD 1 (κ : Hfin X u) = colD hb h := by
      rw [hh]; unfold colD; simp only [Subgroup.coe_mul, Subgroup.coe_one, one_mul]; group
    rw [e2, hs]

end ColFreeBij

end Formalism.L2.SG.NormCut
end
end

noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace Formalism.L2.SG.NormCut

section Links

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (TR : TypedRed X) {u u' : D.what₂.Word}
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
  {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (cs : ColSys X u what₂) (cs' : ColSys X u' rows')


variable (F0) in
def MassA {w : D.what₂.Word} {rs : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (c : ColSys X w rs) : Prop :=
  ∀ q : {Λ // Λ ∈ rs}, wRow D F0 q.1 = ((Nat.card (Aset TR c q) : ℝ))⁻¹

theorem colPhase_holds (hTF : FrameTie X u u' F0 F0') : ColPhase F0 F0' TR cs cs' (scOf TR cs) (scOf TR cs') := by
  have hN := adm_norm_of_fixed_frames cs cs' hTF (Formalism.L2.SG.Pf.termK X cs cs') (Formalism.L2.SG.Pf.modGAt X)
  have hA := adm_parity_of_norm cs cs' (Formalism.L2.SG.Pf.termK X cs cs') hN
  exact colPhase_of TR cs cs' (leviCols_of TR cs cs' (Formalism.L2.SG.Pf.colLatK X cs) (Formalism.L2.SG.Pf.colLatK X cs') hA)
    (phaseAt_of TR cs cs' (Formalism.L2.SG.Pf.colLatK X cs) (Formalism.L2.SG.Pf.colLatK X cs') hA hN)

theorem colFree_steps (hK : X.LevelSubgroupCharacter) (hR : ColReps hK cs) (hCL : Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u hK)
    (hO : Formalism.L2.SG.Pf.NormSteps.LeviOntoS TR cs) (hRep : Formalism.L2.SG.Pf.NormSteps.ColLatRepS cs hK)
    (hMass : MassA TR F0 cs) : ColFree F0 TR cs (Aset TR cs) (scOf TR cs) := fun q =>
  ⟨colFreeBij_of TR cs hK hR hCL (Formalism.L2.SG.Pf.colLatK X cs) hO hRep q, hMass q⟩

end Links

end Formalism.L2.SG.NormCut
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SpanPreservation
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S
open Matrix

namespace Formalism.L2.SG.RealObj.SpanPreservation

open Formalism.L2.SG.HidaSetting

theorem span_pres {n r : ℕ} (e : Fin r → Fin n → ℂ) (g : Matrix (Fin n) (Fin n) ℂ)
    (hg : ∀ a : Fin r, (g - 1) *ᵥ e a ∈ spanLt e a.1) {y : Fin n → ℂ} (hy : y ∈ spanLt e r) :
    g *ᵥ y ∈ spanLt e r := by
  have hmono : ∀ a : Fin r, spanLt e a.1 ≤ spanLt e r := fun a =>
    Submodule.span_mono (Set.image_mono fun b (hb : b.1 < a.1) => lt_trans hb a.2)
  have hgen : ∀ a : Fin r, g *ᵥ e a ∈ spanLt e r := by
    intro a
    have e1 : g *ᵥ e a = e a + (g - 1) *ᵥ e a := by rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
    rw [e1]
    exact Submodule.add_mem _ (Submodule.subset_span ⟨a, a.2, rfl⟩) (hmono a (hg a))
  unfold spanLt at hy
  induction hy using Submodule.span_induction with
  | mem w hw => obtain ⟨b, -, rfl⟩ := hw; exact hgen b
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [Matrix.mulVec_add]; exact add_mem ha hb
  | smul c a _ ha => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ _ ha

theorem inN_inv {n r : ℕ} (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (g gi : Matrix (Fin n) (Fin n) ℂ)
    (h1 : gi * g = 1) (hg : InN ε e z g) : InN ε e z gi := by
  have hS : InS e z gi := Formalism.L2.SG.RealObj.InfCut.inS_inv e z g gi h1 hg.1
  refine ⟨hS, fun y hy => ?_⟩
  have key : (gi - 1) *ᵥ y = -(gi *ᵥ ((g - 1) *ᵥ y)) := by
    simp [Matrix.sub_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec, h1]
  rw [key]
  exact Submodule.neg_mem _ (span_pres e gi hS.1 (hg.2 y hy))

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem ninfU_inv (u : D.what₂.Word) {s : X.B.I.Ginf} (hs : s ∈ X.NinfU u) : s⁻¹ ∈ X.NinfU u := fun v =>
  inN_inv _ _ _ (uMat (s v)) (uMat (s⁻¹ v)) (Formalism.L2.SG.RealObj.InfCut.uMat_inv_mul' (s v)) (hs v)

end Formalism.L2.SG.RealObj.SpanPreservation
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TraceEqSumPlaces
noncomputable section

open NumberField
open scoped ComplexConjugate

namespace Formalism.L2.SG.RealObj.PlaceEmbeddingTraceSums

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def embOf (φ : InfinitePlace F → (E →+* ℂ)) (p : InfinitePlace F × Bool) : E →+* ℂ :=
  if p.2 then (starRingEnd ℂ).comp (φ p.1) else φ p.1

theorem embOf_injective [IsTotallyReal F] [IsTotallyComplex E] (φ : InfinitePlace F → (E →+* ℂ))
    (hφ : ∀ v (a : F), φ v (algebraMap F E a) = v.embedding a) : Function.Injective (embOf φ) := by
  have hre : ∀ (v : InfinitePlace F) (a : F), starRingEnd ℂ (v.embedding a) = v.embedding a := by
    intro v a
    have h := ComplexEmbedding.isReal_iff.1 (InfinitePlace.isReal_iff.1 (IsTotallyReal.isReal v))
    exact RingHom.congr_fun h a
  have hres : ∀ p : InfinitePlace F × Bool, (embOf φ p).comp (algebraMap F E) = p.1.embedding := by
    rintro ⟨v, b⟩
    ext a
    cases b <;> simp [embOf, hφ, hre]
  have hnr : ∀ v, (starRingEnd ℂ).comp (φ v) ≠ φ v := by
    intro v h
    have hc := IsTotallyComplex.isComplex (InfinitePlace.mk (φ v))
    rw [InfinitePlace.isComplex_mk_iff, ComplexEmbedding.isReal_iff] at hc
    exact hc (RingHom.ext fun x => RingHom.congr_fun h x)
  rintro ⟨v, b⟩ ⟨v', b'⟩ h
  have hv : v = v' := by
    have := congrArg (fun σ => σ.comp (algebraMap F E)) h
    simp only [hres] at this
    rw [← InfinitePlace.mk_embedding v, ← InfinitePlace.mk_embedding v', this]
  subst hv
  cases b <;> cases b' <;> simp [embOf] at h ⊢
  · exact hnr v h.symm
  · exact hnr v h

theorem embOf_bijective [IsTotallyReal F] [IsTotallyComplex E] (h2 : Module.finrank F E = 2)
    (φ : InfinitePlace F → (E →+* ℂ)) (hφ : ∀ v (a : F), φ v (algebraMap F E a) = v.embedding a) :
    Function.Bijective (embOf φ) := by
  classical
  refine (Fintype.bijective_iff_injective_and_card _).2 ⟨embOf_injective φ hφ, ?_⟩
  rw [Fintype.card_prod, Fintype.card_bool, Embeddings.card E ℂ,
    InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyReal.nrComplexPlaces_eq_zero, add_zero,
    ← Module.finrank_mul_finrank ℚ F E, h2]
  have h := InfinitePlace.card_add_two_mul_card_eq_rank F
  rw [IsTotallyReal.nrComplexPlaces_eq_zero, mul_zero, add_zero] at h
  rw [h]

theorem trace_eq_sum_places [IsTotallyReal F] [IsTotallyComplex E] (h2 : Module.finrank F E = 2)
    (φ : InfinitePlace F → (E →+* ℂ)) (hφ : ∀ v (a : F), φ v (algebraMap F E a) = v.embedding a) (x : E) :
    ((Algebra.trace ℚ E x : ℚ) : ℂ) = ∑ v, (φ v x + starRingEnd ℂ (φ v x)) := by
  classical
  have h1 : algebraMap ℚ ℂ (Algebra.trace ℚ E x) = ∑ τ : E →ₐ[ℚ] ℂ, τ x := trace_eq_sum_embeddings ℂ
  have h3 : ∑ σ : E →+* ℂ, σ x = ∑ τ : E →ₐ[ℚ] ℂ, τ x :=
    Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ) (fun f => f x) (fun τ => τ x)
      (fun _ => by simp [RingHom.equivRatAlgHom_apply])
  have h4 : ∑ p : InfinitePlace F × Bool, embOf φ p x = ∑ σ : E →+* ℂ, σ x :=
    (embOf_bijective h2 φ hφ).sum_comp (fun σ => σ x)
  rw [show ((Algebra.trace ℚ E x : ℚ) : ℂ) = algebraMap ℚ ℂ (Algebra.trace ℚ E x) from rfl, h1, ← h3, ← h4,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Fintype.sum_bool]
  simp [embOf, add_comm]

end General

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem TraceSum_holds : Formalism.L2.SG.RealObj.RootCoordinateFrames.TraceSum := by
  intro D X g x
  have : IsTotallyReal X.B.I.F := X.B.I.cm.totReal
  have : IsTotallyComplex X.B.I.E := X.B.I.cm.cmUnram.1
  have htr : ((Algebra.trace ℚ D.host.E (X.ιE x) : ℚ) : ℂ) = ((Algebra.trace ℚ X.B.I.E x : ℚ) : ℂ) := by
    rw [show X.ιE x = X.ιE.toRatAlgEquiv x from rfl, Algebra.trace_eq_of_algEquiv]
  unfold Formalism.L2.SG.PairVal.psiInf
  rw [htr, trace_eq_sum_places X.B.I.cm.deg2 X.B.I.φ X.B.I.φ_over x, ← Complex.exp_sum]
  congr 1
  rw [← Finset.mul_sum, Finset.sum_div]
  rfl

end Formalism.L2.SG.RealObj.PlaceEmbeddingTraceSums
end
end
