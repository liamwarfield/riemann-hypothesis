module

public import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.ArvOSobPfSt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChainRuleSmooth.ExpIntertwine

@[expose] public section

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.MemSpanSmoothVec
section -- merged from Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.DifferentiableUpdate
noncomputable section

open scoped ContDiff

namespace Formalism.IndefR.Tow.OrbStPf

variable {N : ℕ} {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

def pd (i : Fin N) (f : (Fin N → ℝ) → H) : (Fin N → ℝ) → H :=
  fun p => fderiv ℝ f p (Pi.single i 1)

def pds (L : List (Fin N)) (f : (Fin N → ℝ) → H) : (Fin N → ℝ) → H := L.foldr pd f

@[simp] lemma pds_nil (f : (Fin N → ℝ) → H) : pds [] f = f := rfl

@[simp] lemma pds_cons (i : Fin N) (L : List (Fin N)) (f : (Fin N → ℝ) → H) :
    pds (i :: L) f = pd i (pds L f) := rfl

lemma contDiff_pd (i : Fin N) {f : (Fin N → ℝ) → H} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (pd i f) := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (m := ∞) (by simp)
  exact hd.clm_apply contDiff_const

lemma contDiff_pds (L : List (Fin N)) {f : (Fin N → ℝ) → H} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (pds L f) := by
  induction L with
  | nil => simpa using hf
  | cons i L ih => simpa only [pds_cons] using contDiff_pd i ih

lemma differentiable_pds (L : List (Fin N)) {f : (Fin N → ℝ) → H} (hf : ContDiff ℝ ∞ f) :
    Differentiable ℝ (pds L f) := by
  exact (contDiff_pds L hf).differentiable (by simp)

lemma pd_hasDerivAt (i : Fin N) {f : (Fin N → ℝ) → H} (p : Fin N → ℝ) (hf : DifferentiableAt ℝ f p) :
    HasDerivAt (fun t : ℝ => f (p + t • Pi.single i 1)) (pd i f p) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => p + t • (Pi.single i 1 : Fin N → ℝ)) (Pi.single i 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single i (1 : ℝ) : Fin N → ℝ)).const_add p
  have h2 : HasFDerivAt f (fderiv ℝ f (p + (0 : ℝ) • Pi.single i 1)) (p + (0 : ℝ) • Pi.single i 1) := by
    simpa using hf.hasFDerivAt
  have h3 := h2.comp_hasDerivAt (0 : ℝ) h1
  simpa [pd, Function.comp_def] using h3

lemma pd_eq_deriv (i : Fin N) {f : (Fin N → ℝ) → H} (p : Fin N → ℝ) (hf : DifferentiableAt ℝ f p) :
    pd i f p = deriv (fun t : ℝ => f (p + t • Pi.single i 1)) 0 := by
  exact (pd_hasDerivAt i p hf).deriv.symm

lemma pd_clm (i : Fin N) (A : H →L[ℝ] H) {f : (Fin N → ℝ) → H} (hf : Differentiable ℝ f) :
    pd i (fun p => A (f p)) = fun p => A (pd i f p) := by
  funext p
  have h := (A.hasFDerivAt.comp p (hf p).hasFDerivAt).fderiv
  simp only [pd]
  rw [show (fun q => A (f q)) = A ∘ f from rfl, h]
  rfl

lemma pds_clm (L : List (Fin N)) (A : H →L[ℝ] H) {f : (Fin N → ℝ) → H} (hf : ContDiff ℝ ∞ f) :
    pds L (fun p => A (f p)) = fun p => A (pds L f p) := by
  induction L with
  | nil => rfl
  | cons i L ih =>
    simp only [pds_cons]
    rw [ih, pd_clm i A (differentiable_pds L hf)]

lemma update_add_single {i j : Fin N} (hij : i ≠ j) (r : Fin N → ℝ) (s t : ℝ) :
    Function.update (r + t • Pi.single i 1) j s = Function.update r j s + t • Pi.single i 1 := by
  funext k
  by_cases hk : k = j <;> simp [Function.update_apply, hk, Pi.single_apply, Ne.symm hij]

lemma differentiable_update (j : Fin N) (s : ℝ) :
    Differentiable ℝ (fun r : Fin N → ℝ => Function.update r j s) := by
  refine differentiable_pi.2 fun k => ?_
  by_cases hk : k = j
  · subst hk
    simp
  · simpa [Function.update_of_ne hk] using
      (differentiable_apply k : Differentiable ℝ fun r : Fin N → ℝ => r k)

lemma pd_update (i j : Fin N) (hij : i ≠ j) (s : ℝ) {g : (Fin N → ℝ) → H} (hg : Differentiable ℝ g) :
    pd i (fun r => g (Function.update r j s)) = fun r => pd i g (Function.update r j s) := by
  funext r
  rw [pd_eq_deriv i (f := fun r => g (Function.update r j s)) r
      ((hg.comp (differentiable_update j s)) r),
    pd_eq_deriv i _ (hg _)]
  congr 1
  funext t
  rw [update_add_single hij r s t]

lemma pds_update (L : List (Fin N)) (j : Fin N) (hL : ∀ i ∈ L, i ≠ j) (s : ℝ) {g : (Fin N → ℝ) → H}
    (hg : ContDiff ℝ ∞ g) :
    pds L (fun r => g (Function.update r j s)) = fun r => pds L g (Function.update r j s) := by
  induction L with
  | nil => rfl
  | cons i L ih =>
    simp only [pds_cons]
    rw [ih (fun k hk => hL k (by simp [hk])),
      pd_update i j (hL i (by simp)) s (differentiable_pds L hg)]

end Formalism.IndefR.Tow.OrbStPf

end
end

noncomputable section

open scoped ContDiff
open Formalism.L2.Theta

namespace Formalism.IndefR.Tow.OrbStPf

variable {n : ℕ} {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  (ρ : Matrix (Fin n) (Fin n) ℂ → (E →L[ℂ] E)) (Lie U : Set (Matrix (Fin n) (Fin n) ℂ))

section SV

variable {ρ Lie}

end SV

variable {ρ Lie U}
variable (hU1 : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ U) (hUm : ∀ a ∈ U, ∀ b ∈ U, a * b ∈ U)
  (hρ : ∀ a ∈ U, ∀ b ∈ U, ρ (a * b) = (ρ a).comp (ρ b))
  (hexp : ∀ Y ∈ Lie, ∀ t : ℝ, NormedSpace.exp (t • Y) ∈ U)

include hU1 hUm in
lemma list_prod_mem (l : List (Matrix (Fin n) (Fin n) ℂ)) (hl : ∀ a ∈ l, a ∈ U) : l.prod ∈ U := by
  induction l with
  | nil => simpa using hU1
  | cons a l ih =>
    rw [List.prod_cons]
    exact hUm a (hl a (by simp)) _ (ih (fun b hb => hl b (by simp [hb])))

include hU1 hUm hexp in
lemma prod_drop_mem {N : ℕ} (Z : Fin N → Matrix (Fin n) (Fin n) ℂ) (hZ : ∀ i, Z i ∈ Lie) (r : Fin N → ℝ) (j : ℕ) :
    ((List.ofFn fun i => NormedSpace.exp (r i • Z i)).drop j).prod ∈ U := by
  refine list_prod_mem hU1 hUm _ ?_
  intro a ha
  have ha' := List.mem_of_mem_drop ha
  simp only [List.mem_ofFn] at ha'
  obtain ⟨i, rfl⟩ := ha'
  exact hexp _ (hZ i) _


include hU1 hUm hρ hexp in
lemma smoothVec_rep_exp {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ Lie) (s : ℝ) {w : E} (hw : SmoothVec Lie ρ w) :
    SmoothVec Lie ρ (ρ (NormedSpace.exp (s • X)) w) := by
  intro k Xs hXs
  have hX' : ∀ i, (Fin.snoc Xs X : Fin (k + 1) → Matrix (Fin n) (Fin n) ℂ) i ∈ Lie := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hX
    · simpa using hXs j
  have hsn : ContDiff ℝ ∞ (fun t : Fin k → ℝ => (Fin.snoc t s : Fin (k + 1) → ℝ)) := by
    refine contDiff_pi.2 fun i => ?_
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using (contDiff_const : ContDiff ℝ ∞ fun _ : Fin k → ℝ => s)
    · simpa using (contDiff_pi.1 contDiff_id j : ContDiff ℝ ∞ fun t : Fin k → ℝ => t j)
  have h := (hw (k + 1) (Fin.snoc Xs X) hX').comp hsn
  convert h using 1
  funext t
  simp only [Function.comp_apply]
  rw [List.ofFn_succ', List.concat_eq_append, List.prod_append, List.prod_singleton]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  have hP : (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod ∈ U := by
    refine list_prod_mem hU1 hUm _ (fun a ha => ?_)
    simp only [List.mem_ofFn] at ha
    obtain ⟨i, rfl⟩ := ha
    exact hexp _ (hXs i) _
  rw [hρ _ hP _ (hexp _ hX _)]
  rfl


variable (ρ) in
def orb {N : ℕ} (Z : Fin N → Matrix (Fin n) (Fin n) ℂ) (u : E) (j : ℕ) (r : Fin N → ℝ) : E :=
  ρ (((List.ofFn fun i => NormedSpace.exp (r i • Z i)).drop j).prod) u

def mask {N : ℕ} (j : ℕ) (r : Fin N → ℝ) : Fin N → ℝ := fun i => if i.val < j then 0 else r i

lemma prod_mask {N : ℕ} (Z : Fin N → Matrix (Fin n) (Fin n) ℂ) (j : ℕ) (r : Fin N → ℝ) :
    (List.ofFn fun i => NormedSpace.exp (mask j r i • Z i)).prod =
      ((List.ofFn fun i => NormedSpace.exp (r i • Z i)).drop j).prod := by
  have hd : (List.ofFn fun i => NormedSpace.exp (mask j r i • Z i)).drop j =
      (List.ofFn fun i => NormedSpace.exp (r i • Z i)).drop j := by
    apply List.ext_getElem
    · simp
    · intro k h1 h2
      simp only [List.getElem_drop, List.getElem_ofFn, mask]
      rw [if_neg (by simp)]
  have ht : ((List.ofFn fun i => NormedSpace.exp (mask j r i • Z i)).take j).prod = 1 := by
    apply List.prod_eq_one
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hx
    have hkj : k < j := by simp at hk; omega
    simp [List.getElem_take, mask, hkj]
  rw [← List.prod_take_mul_prod_drop (List.ofFn fun i => NormedSpace.exp (mask j r i • Z i)) j, ht, one_mul, hd]

lemma contDiff_mask {N : ℕ} (j : ℕ) : ContDiff ℝ ∞ (mask (N := N) j) := by
  refine contDiff_pi.2 fun i => ?_
  by_cases h : i.val < j
  · simp only [mask, h, if_true]
    exact contDiff_const
  · simp only [mask, h, if_false]
    exact contDiff_pi.1 contDiff_id i

lemma contDiff_orb {N : ℕ} (Z : Fin N → Matrix (Fin n) (Fin n) ℂ) (hZ : ∀ i, Z i ∈ Lie) {u : E}
    (hu : SmoothVec Lie ρ u) (j : ℕ) : ContDiff ℝ ∞ (orb ρ Z u j) := by
  have h := (hu N Z hZ).comp (contDiff_mask (N := N) j)
  convert h using 1
  funext r
  simp only [Function.comp_apply, orb, prod_mask]

include hU1 hUm hρ hexp in
lemma orb_update {N : ℕ} (Z : Fin N → Matrix (Fin n) (Fin n) ℂ) (hZ : ∀ i, Z i ∈ Lie) (u : E) (j : ℕ)
    (hj : j < N) (r : Fin N → ℝ) (s : ℝ) :
    orb ρ Z u j (Function.update r ⟨j, hj⟩ s) = ρ (NormedSpace.exp (s • Z ⟨j, hj⟩)) (orb ρ Z u (j + 1) r) := by
  simp only [orb]
  have hlen : j < (List.ofFn fun i => NormedSpace.exp (Function.update r ⟨j, hj⟩ s i • Z i)).length := by
    simpa using hj
  rw [List.drop_eq_getElem_cons hlen, List.prod_cons]
  have hdrop : (List.ofFn fun i => NormedSpace.exp (Function.update r ⟨j, hj⟩ s i • Z i)).drop (j + 1) =
      (List.ofFn fun i => NormedSpace.exp (r i • Z i)).drop (j + 1) := by
    apply List.ext_getElem
    · simp
    · intro k h1 h2
      simp only [List.getElem_drop, List.getElem_ofFn]
      rw [Function.update_apply, if_neg]
      intro h
      simp only [Fin.mk.injEq] at h
      omega
  rw [hdrop, List.getElem_ofFn, Function.update_apply, if_pos rfl,
    hρ _ (hexp _ (hZ _) _) _ (prod_drop_mem hU1 hUm hexp Z hZ r (j + 1))]
  rfl

lemma orb_last {k : ℕ} (Z : Fin (k + 1) → Matrix (Fin n) (Fin n) ℂ) (u : E) (r : Fin (k + 1) → ℝ) :
    orb ρ Z u k r = ρ (NormedSpace.exp (r (Fin.last k) • Z (Fin.last k))) u := by
  simp only [orb]
  rw [List.ofFn_succ', List.concat_eq_append, List.drop_left' (by simp), List.prod_singleton]

include hU1 hUm hρ hexp in
theorem word_pds {k : ℕ} (l : List (Matrix (Fin n) (Fin n) ℂ)) (hl : l.length = k)
    (Z : Fin (k + 1) → Matrix (Fin n) (Fin n) ℂ) (hZ : ∀ i, Z i ∈ Lie)
    (hZl : ∀ (i : Fin (k + 1)) (h : i.val < k), Z i = l[i.val]'(by omega)) :
    ∀ d j, j + d = k → ∃ L : List (Fin (k + 1)), (∀ i ∈ L, j ≤ i.val ∧ i.val < k) ∧
      ∀ u, SmoothVec Lie ρ u → ∀ r : Fin (k + 1) → ℝ, (∀ i : Fin (k + 1), j ≤ i.val → i.val < k → r i = 0) →
        (l.drop j).foldr (dRep ρ) (orb ρ Z u k r) = pds L (orb ρ Z u j) r := by
  intro d
  induction d with
  | zero =>
    intro j hj
    refine ⟨[], by simp, ?_⟩
    intro u _ r _
    obtain rfl : j = k := by omega
    have h0 : l.drop j = [] := List.drop_eq_nil_of_le (by omega)
    rw [h0, List.foldr_nil, pds_nil]
  | succ d ih =>
    intro j hj
    obtain ⟨L', hL'1, hL'2⟩ := ih (j + 1) (by omega)
    have hjk : j < k := by omega
    refine ⟨⟨j, by omega⟩ :: L', ?_, ?_⟩
    · intro i hi
      rcases List.mem_cons.1 hi with h | h
      · subst h
        exact ⟨le_refl _, hjk⟩
      · have := hL'1 i h
        exact ⟨by omega, this.2⟩
    · intro u hu r hr
      have hjl : j < l.length := by omega
      rw [List.drop_eq_getElem_cons hjl, List.foldr_cons,
        hL'2 u hu r (fun i h1 h2 => hr i (by omega) h2), pds_cons]
      have hne : ∀ i ∈ L', i ≠ (⟨j, by omega⟩ : Fin (k + 1)) := by
        intro i hi h
        have := (hL'1 i hi).1
        rw [h] at this
        simp at this
      have hF : ContDiff ℝ ∞ (pds L' (orb ρ Z u j)) := contDiff_pds L' (contDiff_orb Z hZ hu j)
      have hdiff : DifferentiableAt ℝ (pds L' (orb ρ Z u j)) r := hF.differentiable (by simp) r
      rw [pd_eq_deriv _ r hdiff]
      have hZj : Z ⟨j, by omega⟩ = l[j] := hZl ⟨j, by omega⟩ hjk
      have hfun : (fun t : ℝ => pds L' (orb ρ Z u j) (r + t • Pi.single (⟨j, by omega⟩ : Fin (k + 1)) (1 : ℝ))) =
          fun t => ρ (NormedSpace.exp (t • Z ⟨j, by omega⟩)) (pds L' (orb ρ Z u (j + 1)) r) := by
        funext t
        have hup : r + t • Pi.single (⟨j, by omega⟩ : Fin (k + 1)) (1 : ℝ) = Function.update r ⟨j, by omega⟩ t := by
          funext i
          by_cases h : i = ⟨j, by omega⟩
          · subst h
            simp [hr ⟨j, by omega⟩ (le_refl j) hjk]
          · simp [h, Pi.single_apply, Function.update_apply]
        have h1 : pds L' (orb ρ Z u j) (Function.update r ⟨j, by omega⟩ t) =
            pds L' (fun r' => orb ρ Z u j (Function.update r' ⟨j, by omega⟩ t)) r := by
          rw [pds_update L' _ hne t (contDiff_orb Z hZ hu j)]
        have h2 : (fun r' => orb ρ Z u j (Function.update r' ⟨j, by omega⟩ t)) =
            fun r' => ((ρ (NormedSpace.exp (t • Z ⟨j, by omega⟩))).restrictScalars ℝ) (orb ρ Z u (j + 1) r') := by
          funext r'
          exact orb_update hU1 hUm hρ hexp Z hZ u j (by omega) r' t
        rw [hup, h1, h2, pds_clm L' _ (contDiff_orb Z hZ hu (j + 1))]
        rfl
      (rw [hfun, hZj]) <;> rfl



include hU1 hUm hρ hexp in
lemma word_eval (l : List (Matrix (Fin n) (Fin n) ℂ)) (hl : ∀ Y ∈ l, Y ∈ Lie)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ Lie) :
    ∃ (Z : Fin (l.length + 1) → Matrix (Fin n) (Fin n) ℂ) (L : List (Fin (l.length + 1))), (∀ i, Z i ∈ Lie) ∧
      Z (Fin.last _) = X ∧ ∀ v, SmoothVec Lie ρ v → ∀ t : ℝ,
        l.foldr (dRep ρ) (ρ (NormedSpace.exp (t • X)) v) = pds L (orb ρ Z v 0) (t • Pi.single (Fin.last _) 1) := by
  let Z : Fin (l.length + 1) → Matrix (Fin n) (Fin n) ℂ := fun i => if h : i.val < l.length then l[i.val] else X
  have hZ : ∀ i, Z i ∈ Lie := by
    intro i
    simp only [Z]
    split_ifs with h
    · exact hl _ (by simp)
    · exact hX
  have hZl : ∀ (i : Fin (l.length + 1)) (h : i.val < l.length), Z i = l[i.val]'(by omega) := by
    intro i h
    simp only [Z, dif_pos h]
  obtain ⟨L, -, hL⟩ := word_pds hU1 hUm hρ hexp l rfl Z hZ hZl l.length 0 (by simp)
  refine ⟨Z, L, hZ, by simp [Z], ?_⟩
  intro v hv t
  have hr : ∀ i : Fin (l.length + 1), 0 ≤ i.val → i.val < l.length →
      (t • Pi.single (Fin.last l.length) (1 : ℝ)) i = 0 := by
    intro i _ h
    have : i ≠ Fin.last _ := by
      intro h'
      rw [h'] at h
      simp at h
    simp [Pi.single_apply, this]
  have := hL v hv _ hr
  rw [List.drop_zero] at this
  rw [← this, orb_last]
  simp [Z]



end Formalism.IndefR.Tow.OrbStPf

end
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Mult
  MeasureTheory Matrix Filter Topology
open scoped ContDiff

namespace Formalism.IndefR.Tow.SobPf

section Gen

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem one_mem_UH (G : Matrix (Fin n) (Fin n) ℂ) : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Formalism.QuantumDeterminants.UH G := by
  show (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * G * 1 = G
  simp

theorem zero_mem_lieG (G : Matrix (Fin n) (Fin n) ℂ) : (0 : Matrix (Fin n) (Fin n) ℂ) ∈ lieG G := by
  show (0 : Matrix (Fin n) (Fin n) ℂ)ᴴ * G + G * 0 = 0
  simp

theorem expS_mem_UH {G X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieG G) (t : ℝ) :
    NormedSpace.exp (t • X) ∈ Formalism.QuantumDeterminants.UH G := by
  have h := CCRuleCW.lie_smul G X hX t
  rw [Complex.coe_smul] at h
  exact CCRuleCW.exp_mem_UH G (t • X) h

theorem mul_mem_UH₂ (G : Matrix (Fin n) (Fin n) ℂ) :
    ∀ a ∈ Formalism.QuantumDeterminants.UH G, ∀ b ∈ Formalism.QuantumDeterminants.UH G, a * b ∈ Formalism.QuantumDeterminants.UH G := by
  intro a ha b hb
  have ha' : aᴴ * G * a = G := ha
  have hb' : bᴴ * G * b = G := hb
  show (a * b)ᴴ * G * (a * b) = G
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * G * (a * b) = bᴴ * (aᴴ * G * a) * b := by simp only [Matrix.mul_assoc]
    _ = G := by rw [ha', hb']

theorem smooth_oneProd {G : Matrix (Fin n) (Fin n) ℂ} {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hπ : IsGRep G π) {w : H} (hw : SmoothVec (lieG G) π w) :
    ∀ {d : ℕ} (Y : Fin d → Matrix (Fin n) (Fin n) ℂ), (∀ i, Y i ∈ lieG G) → ∀ t : Fin d → ℝ,
      SmoothVec (lieG G) π (π (oneProd Y t) w) ∧ oneProd Y t ∈ Formalism.QuantumDeterminants.UH G := by
  intro d
  induction d with
  | zero =>
    intro Y _ t
    simp only [oneProd, List.ofFn_zero, List.prod_nil, hπ.1]
    exact ⟨hw, one_mem_UH G⟩
  | succ d ih =>
    intro Y hY t
    have e : oneProd Y t = NormedSpace.exp (t 0 • Y 0) * oneProd (fun i => Y i.succ) (fun i => t i.succ) := by
      simp [oneProd, List.ofFn_succ]
    obtain ⟨h1, h2⟩ := ih (fun i => Y i.succ) (fun i => hY _) (fun i => t i.succ)
    rw [e, hπ.2.1 _ (expS_mem_UH (hY 0) _) _ h2]
    exact ⟨OrbStPf.smoothVec_rep_exp (U := Formalism.QuantumDeterminants.UH G) (one_mem_UH G) (mul_mem_UH₂ G) hπ.2.1 (fun Y hY t => expS_mem_UH hY t) (hY 0) (t 0) h1,
      mul_mem_UH₂ G _ (expS_mem_UH (hY 0) _) _ h2⟩

end Gen

section Append

theorem append_line {N d : ℕ} (r : Fin N → ℝ) (t : Fin d → ℝ) (i : Fin N) (s : ℝ) :
    Fin.append (r + s • Pi.single i 1) t = Fin.append r t + s • Pi.single (Fin.castAdd d i) 1 := by
  funext j
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · simp [Pi.single_apply, Fin.castAdd_inj]
  · have hne : (Fin.natAdd N j : Fin (N + d)) ≠ Fin.castAdd d i := by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.coe_natAdd, Fin.coe_castAdd] at this
      omega
    simp [Pi.single_apply, hne]

theorem contDiff_append_left {N d : ℕ} (t : Fin d → ℝ) : ContDiff ℝ ∞ (fun r : Fin N → ℝ => Fin.append r t) := by
  refine contDiff_pi.2 fun j => ?_
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · simp only [Fin.append_left]
    exact contDiff_apply ℝ (fun _ => ℝ) j
  · simp only [Fin.append_right]
    exact contDiff_const

theorem continuous_append_right {N d : ℕ} (r : Fin N → ℝ) :
    Continuous (fun t : Fin d → ℝ => Fin.append r t) := by
  refine continuous_pi fun j => ?_
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · simp only [Fin.append_left]
    exact continuous_const
  · simp only [Fin.append_right]
    exact continuous_apply j

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem pd_append {N d : ℕ} (f : (Fin (N + d) → ℝ) → E) (hf : Differentiable ℝ f) (t : Fin d → ℝ) (i : Fin N) :
    OrbStPf.pd i (fun r => f (Fin.append r t)) = fun r => OrbStPf.pd (Fin.castAdd d i) f (Fin.append r t) := by
  funext r
  simp only [OrbStPf.pd]
  have hg : Differentiable ℝ (fun r : Fin N → ℝ => Fin.append r t) :=
    (contDiff_infty_iff_fderiv.1 (contDiff_append_left t)).1
  rw [fderiv_comp' r (hf _) (hg r), ContinuousLinearMap.comp_apply]
  congr 1
  have h1 : HasDerivAt (fun s : ℝ => Fin.append (r + s • (Pi.single i 1 : Fin N → ℝ)) t)
      (fderiv ℝ (fun r : Fin N → ℝ => Fin.append r t) r (Pi.single i 1)) 0 := by
    have hl : HasDerivAt (fun s : ℝ => r + s • (Pi.single i 1 : Fin N → ℝ)) (Pi.single i 1) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single i 1 : Fin N → ℝ)).const_add r
    have h3 := (hg (r + (0 : ℝ) • (Pi.single i 1 : Fin N → ℝ))).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hl
    rw [zero_smul, add_zero] at h3
    exact h3
  have h2 : HasDerivAt (fun s : ℝ => Fin.append (r + s • (Pi.single i 1 : Fin N → ℝ)) t)
      (Pi.single (Fin.castAdd d i) 1) 0 := by
    simp only [append_line]
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const
      (Pi.single (Fin.castAdd d i) 1 : Fin (N + d) → ℝ)).const_add (Fin.append r t)
  exact h1.unique h2

private theorem pds_contDiff_lemma {N : ℕ} (L : List (Fin N)) (f : (Fin N → ℝ) → E)
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (OrbStPf.pds L f) := by
  induction L with
  | nil => exact hf
  | cons a L ih =>
    show ContDiff ℝ ∞ (fun p => fderiv ℝ (OrbStPf.pds L f) p (Pi.single a 1))
    exact (contDiff_infty_iff_fderiv.1 ih).2.clm_apply contDiff_const

theorem pds_append {N d : ℕ} (L : List (Fin N)) (f : (Fin (N + d) → ℝ) → E) (hf : ContDiff ℝ ∞ f)
    (t : Fin d → ℝ) :
    OrbStPf.pds L (fun r => f (Fin.append r t)) =
      fun r => OrbStPf.pds (L.map (Fin.castAdd d)) f (Fin.append r t) := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    have hg : ContDiff ℝ ∞ (OrbStPf.pds (L.map (Fin.castAdd d)) f) := pds_contDiff_lemma _ f hf
    show OrbStPf.pd a (OrbStPf.pds L fun r => f (Fin.append r t)) =
      fun r => OrbStPf.pd (Fin.castAdd d a) (OrbStPf.pds (L.map (Fin.castAdd d)) f) (Fin.append r t)
    rw [ih]
    exact pd_append _ (contDiff_infty_iff_fderiv.1 hg).1 t a

end Append

theorem foldCont_holds : FoldCont := by
  intro n H _ _ G π hπ w hw l hl d Y hY
  have hexp : ∀ Y ∈ lieG G, ∀ t : ℝ, NormedSpace.exp (t • Y) ∈ Formalism.QuantumDeterminants.UH G := fun Y hY t => expS_mem_UH hY t
  obtain ⟨Z, L, hZ, -, hval⟩ := OrbStPf.word_eval (U := Formalism.QuantumDeterminants.UH G) (ρ := π) (Lie := lieG G) (one_mem_UH G) (mul_mem_UH₂ G) hπ.2.1 hexp l hl (zero_mem_lieG G)
  set W : Fin (l.length + 1 + d) → Matrix (Fin n) (Fin n) ℂ := Fin.append Z Y with hWdef
  have hW : ∀ i, W i ∈ lieG G := fun i =>
    Fin.addCases (fun a => by simpa [W, Fin.append_left] using hZ a) (fun b => by simpa [W, Fin.append_right] using hY b) i
  have hG : ContDiff ℝ ∞ (OrbStPf.orb π W w 0) := OrbStPf.contDiff_orb W hW hw 0
  have key : ∀ t, dL π l (π (oneProd Y t) w) =
      OrbStPf.pds (L.map (Fin.castAdd d)) (OrbStPf.orb π W w 0) (Fin.append 0 t) := by
    intro t
    have hv := (smooth_oneProd hπ hw Y hY t)
    have h0 := hval _ hv.1 0
    simp only [zero_smul, NormedSpace.exp_zero, hπ.1, ContinuousLinearMap.one_apply] at h0
    have e : OrbStPf.orb π Z (π (oneProd Y t) w) 0 = fun r => OrbStPf.orb π W w 0 (Fin.append r t) := by
      funext r
      have hA : (List.ofFn fun i => NormedSpace.exp (r i • Z i)).prod ∈ Formalism.QuantumDeterminants.UH G :=
        OrbStPf.list_prod_mem (one_mem_UH G) (mul_mem_UH₂ G) _ (fun a ha => by
          obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha; exact hexp _ (hZ _) _)
      simp only [OrbStPf.orb, List.drop_zero]
      rw [List.ofFn_add (m := d), List.prod_append]
      have e1 : ∀ i : Fin (l.length + 1), Fin.append r t (Fin.castLE (Nat.le_add_right _ d) i) = r i :=
        fun i => Fin.append_left r t i
      have e2 : ∀ i : Fin (l.length + 1), Fin.append Z Y (Fin.castLE (Nat.le_add_right _ d) i) = Z i :=
        fun i => Fin.append_left Z Y i
      simp only [W, e1, e2, Fin.append_right]
      rw [show (List.ofFn fun j : Fin d => NormedSpace.exp (t j • Y j)).prod = oneProd Y t from rfl,
        hπ.2.1 _ hA _ hv.2]
      rfl
    unfold dL
    rw [h0, e, pds_append L _ hG t]
  rw [show (fun t => dL π l (π (oneProd Y t) w)) =
      fun t => OrbStPf.pds (L.map (Fin.castAdd d)) (OrbStPf.orb π W w 0) (Fin.append 0 t) from funext key]
  exact (OrbStPf.contDiff_pds _ hG).continuous.comp (continuous_append_right 0)


end Formalism.IndefR.Tow.SobPf

end
