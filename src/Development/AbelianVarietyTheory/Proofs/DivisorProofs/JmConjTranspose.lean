module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelReal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdaptedFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffPartLe
noncomputable section

namespace GlobalTheory.IndLine

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n d d₁ : ℕ} {Y : Spc F E n} {W : Spc F E d}

def IsTwEig (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W) {P : Type} [AddCommGroup P] [Module ℂ P]
    (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (χ : Chr F E) (z : ℝ) (x : P) : Prop :=
  ∀ k ∈ KInf σ W B.emb, ∀ t : (AE F E)ˣ, IsLevi H' t (1 : UA σ W₁.J) k → ∀ f ∈ M.Pol B.ψ B.emb,
    ∀ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) f f₁ → p f = x →
      p f₁ = ((χ t : ℂ) * (((absE F E t : ℝ) ^ z : ℝ) : ℂ)) • x

def IsOffEig (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W) {P : Type} [AddCommGroup P] [Module ℂ P]
    (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (χ : Chr F E) (z : ℝ) (x : P) : Prop :=
  ∃ k ∈ KInf σ W B.emb, ∃ t : (AE F E)ˣ, IsLevi H' t (1 : UA σ W₁.J) k ∧ ∃ c : ℂ,
    c ≠ (χ t : ℂ) * (((absE F E t : ℝ) ^ z : ℝ) : ℂ) ∧ ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
      Acts (evI F) (om (1, k)) f f₁ → p f = x → p f₁ = c • x

def twPart (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W) {P : Type} [AddCommGroup P] [Module ℂ P]
    (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (χ : Chr F E) (z : ℝ)
    (V : Submodule ℂ P) : Submodule ℂ P :=
  Submodule.span ℂ {x | x ∈ V ∧ IsTwEig B M om p W₁ H' χ z x}

def offPart (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W) {P : Type} [AddCommGroup P] [Module ℂ P]
    (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (χ : Chr F E) (z : ℝ)
    (V : Submodule ℂ P) : Submodule ℂ P :=
  Submodule.span ℂ {x | x ∈ V ∧ IsOffEig B M om p W₁ H' χ z x}

def KStabL (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W) {P : Type} [AddCommGroup P] [Module ℂ P]
    (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (N : Submodule ℂ P) : Prop :=
  ∀ k ∈ KInf σ W B.emb, ∀ k₁ ∈ KInf σ W₁ B.emb, IsLevi H' 1 k₁ k → ∀ f ∈ M.Pol B.ψ B.emb,
    ∀ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) f f₁ → p f ∈ N → p f₁ ∈ N

theorem twPart_le (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W) {P : Type} [AddCommGroup P] [Module ℂ P]
    (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (χ : Chr F E) (z : ℝ)
    (V : Submodule ℂ P) : twPart B M om p W₁ H' χ z V ≤ V :=
  Submodule.span_le.2 fun _ hx => hx.1

end GlobalTheory.IndLine
end
end

noncomputable section

open scoped TensorProduct Matrix Classical
open NumberField Formalism.BasicNotions.TH GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.FockBridge

section Ind

variable {T P : Type} [AddCommGroup T] [Module ℂ T] [AddCommGroup P] [Module ℂ P]

def Keeps (q : T →ₗ[ℂ] P) (L : Module.End ℂ T) : Prop := ∀ t, q t = 0 → q (L t) = 0

def indOp (q : T →ₗ[ℂ] P) (L : Module.End ℂ T) : Module.End ℂ P :=
  if h : Function.Surjective q ∧ Keeps q L then
    (q.quotKerEquivOfSurjective h.1).toLinearMap ∘ₗ
      ((LinearMap.ker q).mapQ (LinearMap.ker q) L fun t ht => LinearMap.mem_ker.2 (h.2 t (LinearMap.mem_ker.1 ht))) ∘ₗ
        (q.quotKerEquivOfSurjective h.1).symm.toLinearMap
  else 0

theorem indOp_apply {q : T →ₗ[ℂ] P} {L : Module.End ℂ T} (hq : Function.Surjective q) (hL : Keeps q L) (t : T) :
    indOp q L (q t) = q (L t) := by
  have e : (q.quotKerEquivOfSurjective hq).symm (q t) = Submodule.Quotient.mk t :=
    (LinearEquiv.symm_apply_eq _).2 (by simp)
  rw [indOp, dite_eq_left ⟨hq, hL⟩, LinearMap.comp_apply, LinearMap.comp_apply]
  simp only [LinearEquiv.coe_coe]
  rw [e]
  rfl

theorem indOp_eq {q : T →ₗ[ℂ] P} {L : Module.End ℂ T} (hq : Function.Surjective q) (hL : Keeps q L)
    (M : Module.End ℂ P) (h : ∀ t, M (q t) = q (L t)) : indOp q L = M := by
  ext x
  obtain ⟨t, rfl⟩ := hq x
  rw [indOp_apply hq hL, h]

theorem keeps_mul {q : T →ₗ[ℂ] P} {L L' : Module.End ℂ T} (h : Keeps q L) (h' : Keeps q L') : Keeps q (L * L') :=
  fun t ht => h _ (h' t ht)

theorem keeps_sub {q : T →ₗ[ℂ] P} {L L' : Module.End ℂ T} (h : Keeps q L) (h' : Keeps q L') : Keeps q (L - L') :=
  fun t ht => by simp [h t ht, h' t ht]

theorem indOp_mul {q : T →ₗ[ℂ] P} {L L' : Module.End ℂ T} (hq : Function.Surjective q) (h : Keeps q L)
    (h' : Keeps q L') : indOp q (L * L') = indOp q L * indOp q L' :=
  indOp_eq hq (keeps_mul h h') _ fun t => by
    rw [Module.End.mul_apply, indOp_apply hq h', indOp_apply hq h]; rfl

theorem indOp_sub {q : T →ₗ[ℂ] P} {L L' : Module.End ℂ T} (hq : Function.Surjective q) (h : Keeps q L)
    (h' : Keeps q L') : indOp q (L - L') = indOp q L - indOp q L' :=
  indOp_eq hq (keeps_sub h h') _ fun t => by
    rw [LinearMap.sub_apply, indOp_apply hq h', indOp_apply hq h, LinearMap.sub_apply, map_sub]

end Ind

section Place

variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

theorem atPl_mul (w : ι) (L L' : Module.End ℂ (V w)) : atPl w (L * L') = atPl w L * atPl w L' := by
  unfold atPl
  rw [← PiTensorProduct.map_mul]
  congr 1
  funext i
  by_cases h : i = w
  · subst h; simp
  · simp only [Function.update_of_ne h]; first | rfl | simp [Module.End.mul_eq_comp]

theorem atPl_comm {w w' : ι} (hw : w ≠ w') (L : Module.End ℂ (V w)) (L' : Module.End ℂ (V w')) :
    atPl w L * atPl w' L' = atPl w' L' * atPl w L := by
  unfold atPl
  rw [← PiTensorProduct.map_mul, ← PiTensorProduct.map_mul]
  congr 1
  funext i
  by_cases h : i = w
  · subst h; simp only [Function.update_self, Function.update_of_ne hw]; first | rfl | simp [Module.End.mul_eq_comp]
  · by_cases h' : i = w'
    · subst h'; simp only [Function.update_self, Function.update_of_ne h]; first | rfl | simp [Module.End.mul_eq_comp]
    · simp only [Function.update_of_ne h, Function.update_of_ne h']

end Place

section Fock

variable {F : Type} [Field F] [NumberField F] {P : Type} [AddCommGroup P] [Module ℂ P] {p₁ q₁ r s : ℕ}

def fockOp (q : Tens F p₁ q₁ r s →ₗ[ℂ] P) (w : InfinitePlace F) : Mat r s →ₗ[ℂ] Module.End ℂ P :=
  if h : Function.Surjective q ∧ ∀ Y, Keeps q (atPl w (fockAct2 p₁ q₁ r s Y)) then
    { toFun := fun Y => indOp q (atPl w (fockAct2 p₁ q₁ r s Y))
      map_add' := fun Y Z => by
        apply indOp_eq h.1 (h.2 _)
        intro t
        rw [LinearMap.add_apply, indOp_apply h.1 (h.2 Y), indOp_apply h.1 (h.2 Z), map_add (f := _), Main.atPl_add,
          LinearMap.add_apply, map_add]
      map_smul' := fun c Y => by
        apply indOp_eq h.1 (h.2 _)
        intro t
        rw [RingHom.id_apply, LinearMap.smul_apply, indOp_apply h.1 (h.2 Y), map_smul, Main.atPl_smul,
          LinearMap.smul_apply, map_smul] }
  else 0

theorem fockOp_eq {q : Tens F p₁ q₁ r s →ₗ[ℂ] P} {w : InfinitePlace F} (hq : Function.Surjective q)
    (hK : ∀ Y, Keeps q (atPl w (fockAct2 p₁ q₁ r s Y))) (Y : Mat r s) :
    fockOp q w Y = indOp q (atPl w (fockAct2 p₁ q₁ r s Y)) := by
  rw [fockOp, dite_eq_left ⟨hq, hK⟩]
  rfl

theorem fockOp_apply {q : Tens F p₁ q₁ r s →ₗ[ℂ] P} {w : InfinitePlace F} (hq : Function.Surjective q)
    (hK : ∀ Y, Keeps q (atPl w (fockAct2 p₁ q₁ r s Y))) (Y : Mat r s) (t : Tens F p₁ q₁ r s) :
    fockOp q w Y (q t) = q (atPl w (fockAct2 p₁ q₁ r s Y) t) := by
  rw [fockOp_eq hq hK, indOp_apply hq (hK Y)]


variable (r s) in
def negT : Mat r s →ₗ[ℂ] Mat r s where
  toFun Y := -Yᵀ
  map_add' Y Z := by rw [Matrix.transpose_add, neg_add]
  map_smul' c Y := by rw [Matrix.transpose_smul, RingHom.id_apply, smul_neg]

theorem negT_apply (Y : Mat r s) : negT r s Y = -Yᵀ := rfl

def twAct (ε : Bool) (q : Tens F p₁ q₁ r s →ₗ[ℂ] P) (w : InfinitePlace F) : Mat r s →ₗ[ℂ] Module.End ℂ P :=
  if ε then fockOp q w else fockOp q w ∘ₗ negT r s

end Fock

section Frames

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def IsFrames (B : Base F E) {n d : ℕ} (Y : Spc F E n) (W : Spc F E d) {p₁ q₁ r s : ℕ}
    (A : InfinitePlace F → Matrix (Fin n) (Ix p₁ q₁) ℂ) (C : InfinitePlace F → Matrix (Fin d) (Ix r s) ℂ) : Prop :=
  Framed B.emb (incM F Y.J) (incM F W.J) 1 Complex.I A C ∧ (∀ w, Y.θ w * A w = A w * Jm p₁ q₁) ∧
    ∀ w, W.θ w * C w = C w * Jm r s

def IsFockData (B : Base F E) {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} (M : Model σ Y W) {p₁ q₁ r s : ℕ}
    (A : InfinitePlace F → Matrix (Fin n) (Ix p₁ q₁) ℂ) (C : InfinitePlace F → Matrix (Fin d) (Ix r s) ℂ)
    (Φ : Tens F p₁ q₁ r s →ₗ[ℂ] SInf F (Fin n × Fin d)) : Prop :=
  IsFrames B Y W A C ∧ IsFockMap B.ψ B.emb M.co A C Φ

def IsAdaptedFrame (B : Base F E) {d d₁ : ℕ} (H' : Plane E d d₁) {r s : ℕ}
    (C : InfinitePlace F → Matrix (Fin d) (Ix r s) ℂ) (r₀ : Fin r) (s₀ : Fin s) : Prop :=
  ∀ w, (∃ c : ℂ, c ≠ 0 ∧ ∀ i, (B.emb w).1 (H'.x i) = c * (C w i (.inl r₀) + C w i (.inr s₀))) ∧
    (∃ c₁ c₂ : ℂ, ∀ i, (B.emb w).1 (H'.y i) = c₁ * C w i (.inl r₀) + c₂ * C w i (.inr s₀)) ∧
    ∀ a, a ≠ .inl r₀ → a ≠ .inr s₀ → ∃ z : Fin d₁ → ℂ, ∀ i, C w i a = (H'.ι.map (B.emb w).1 *ᵥ z) i

end Frames

section Laws

variable {F : Type} [Field F] [NumberField F] {P : Type} [AddCommGroup P] [Module ℂ P] {p₁ q₁ r s : ℕ}

theorem atPl_sub {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (w : ι) (L L' : Module.End ℂ (V w)) : atPl w (L - L') = atPl w L - atPl w L' := by
  simp only [Main.atPl_eq, MultilinearMap.map_update_sub]

theorem fockOp_lie {q : Tens F p₁ q₁ r s →ₗ[ℂ] P} {w : InfinitePlace F} (hq : Function.Surjective q)
    (hK : ∀ Y, Keeps q (atPl w (fockAct2 p₁ q₁ r s Y))) (Y Z : Mat r s) :
    fockOp q w (Y * Z - Z * Y) = fockOp q w Y * fockOp q w Z - fockOp q w Z * fockOp q w Y := by
  rw [fockOp_eq hq hK, fockOp_eq hq hK, fockOp_eq hq hK, (GlobalTheory.FockPair.pair_lie_commute p₁ q₁ r s).2.1 Y Z,
    atPl_sub, atPl_mul, atPl_mul, indOp_sub hq (keeps_mul (hK Y) (hK Z)) (keeps_mul (hK Z) (hK Y)),
    indOp_mul hq (hK Y) (hK Z), indOp_mul hq (hK Z) (hK Y)]

theorem fockOp_comm {q : Tens F p₁ q₁ r s →ₗ[ℂ] P} (hq : Function.Surjective q)
    (hK : ∀ w Y, Keeps q (atPl w (fockAct2 p₁ q₁ r s Y))) {w w' : InfinitePlace F} (hw : w ≠ w') (Y Z : Mat r s) :
    fockOp q w Y * fockOp q w' Z = fockOp q w' Z * fockOp q w Y := by
  rw [fockOp_eq hq (hK w), fockOp_eq hq (hK w'), ← indOp_mul hq (hK w Y) (hK w' Z),
    ← indOp_mul hq (hK w' Z) (hK w Y), atPl_comm hw]

theorem negT_negT (Y : Mat r s) : negT r s (negT r s Y) = Y := by
  simp [negT_apply]

theorem negT_lie (Y Z : Mat r s) : negT r s (Y * Z - Z * Y) = negT r s Y * negT r s Z - negT r s Z * negT r s Y := by
  simp only [negT_apply, Matrix.transpose_sub, Matrix.transpose_mul, neg_mul_neg, neg_sub]

theorem sameBlock_symm {a b : Ix r s} (h : sameBlock a b) : sameBlock b a := by
  rcases a with a | a <;> rcases b with b | b <;> simp_all [sameBlock]

theorem isKC_negT {Y : Mat r s} (hY : IsKC Y) : IsKC (negT r s Y) := fun a b hab => by
  rw [negT_apply, Matrix.neg_apply, Matrix.transpose_apply, hY b a fun h => hab (sameBlock_symm h), neg_zero]

theorem negT_Eab (a b : Ix r s) : negT r s (Eab a b) = -Eab b a := by
  rw [negT_apply, Eab, Eab, Matrix.transpose_single]

theorem twAct_lie {q : Tens F p₁ q₁ r s →ₗ[ℂ] P} {w : InfinitePlace F} (hq : Function.Surjective q)
    (hK : ∀ Y, Keeps q (atPl w (fockAct2 p₁ q₁ r s Y))) (ε : Bool) (Y Z : Mat r s) :
    twAct ε q w (Y * Z - Z * Y) = twAct ε q w Y * twAct ε q w Z - twAct ε q w Z * twAct ε q w Y := by
  cases ε
  · simp only [twAct, Bool.false_eq_true, if_false, LinearMap.comp_apply]
    rw [negT_lie, fockOp_lie hq hK]
  · simp only [twAct, if_true]
    exact fockOp_lie hq hK Y Z

theorem twAct_comm {q : Tens F p₁ q₁ r s →ₗ[ℂ] P} (hq : Function.Surjective q)
    (hK : ∀ w Y, Keeps q (atPl w (fockAct2 p₁ q₁ r s Y))) (ε : Bool) {w w' : InfinitePlace F} (hw : w ≠ w')
    (Y Z : Mat r s) : twAct ε q w Y * twAct ε q w' Z = twAct ε q w' Z * twAct ε q w Y := by
  cases ε
  · simp only [twAct, Bool.false_eq_true, if_false, LinearMap.comp_apply]
    exact fockOp_comm hq hK hw _ _
  · simp only [twAct, if_true]
    exact fockOp_comm hq hK hw _ _

end Laws

end GlobalTheory.FockBridge
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanPolynomialTensorWeight
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KStab
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.IndLine

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n d d₁ : ℕ} {Y : Spc F E n} {W : Spc F E d}

def PGen (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W) {P : Type} [AddCommGroup P] [Module ℂ P]
    (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (V : Submodule ℂ P) : Prop :=
  ∀ N : Submodule ℂ P, V ≤ N →
    (∀ γ ∈ Lines σ W, (∀ s, γ s ∈ unip σ W H') → ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
      ActsD (evI F) (fun s => om (1, γ (Multiplicative.ofAdd s))) f f₁ → p f ∈ N → p f₁ ∈ N) →
    (∀ γ ∈ Lines σ W, (∃ (t : Multiplicative ℝ →* (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))ˣ) (γ₁ : Multiplicative ℝ →* UA σ W₁.J), γ₁ ∈ Lines σ W₁ ∧
        ∀ s, IsLevi H' (t s) (γ₁ s) (γ s)) → ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
      ActsD (evI F) (fun s => om (1, γ (Multiplicative.ofAdd s))) f f₁ → p f ∈ N → p f₁ ∈ N) →
    N = ⊤

def KStab (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W) {P : Type} [AddCommGroup P] [Module ℂ P]
    (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) (V : Submodule ℂ P) : Prop :=
  (∀ k ∈ KInf σ W B.emb, ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
      Acts (evI F) (om (1, k)) f f₁ → p f ∈ V → p f₁ ∈ V) ∧
    ∀ γ ∈ Lines σ W, (∀ s, γ s ∈ KInf σ W B.emb) → ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
      ActsD (evI F) (fun s => om (1, γ (Multiplicative.ofAdd s))) f f₁ → p f ∈ V → p f₁ ∈ V

end GlobalTheory.IndLine
end
end

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)
open GlobalTheory.RealLift Formalism.BasicNotions.TH
open scoped Classical

noncomputable section
namespace GlobalTheory.FockKStab
open GlobalTheory.ExpAct
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem mem_of_exp {V : Type} [AddCommGroup V] [Module ℂ V] (L : Module.End ℂ V) (hL : LocFin L) (N : Submodule ℂ V)
    (T : V) (h : ∀ s : ℝ, ∃ U : Module.End ℂ V, IsExp ((s : ℂ) • L) U ∧ U T ∈ N) : L T ∈ N := by
  rw [← Submodule.Quotient.mk_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro l'
  set l : V →ₗ[ℂ] ℂ := l' ∘ₗ N.mkQ with hldef
  have hl : ∀ v ∈ N, l v = 0 := fun v hv => by simp [hldef, (Submodule.Quotient.mk_eq_zero N).2 hv]
  show l (L T) = 0
  obtain ⟨N0, hfin, hT, hN0⟩ := hL T
  set A := mat L N0 hN0
  set x := crd N0 ⟨T, hT⟩
  set φ := l ∘ₗ emb N0
  have hpow : ∀ n : ℕ, φ ((A ^ n) *ᵥ x) = l ((L ^ n) T) := fun n => by
    simp only [φ, LinearMap.comp_apply, A, emb_pow_mulVec, x, emb_crd]
  have hg : ∀ s : ℝ, φ (NormedSpace.exp (s • A) *ᵥ x) = 0 := by
    intro s
    obtain ⟨U, hU, hUN⟩ := h s
    have h1 := hU T l
    have h2 := hasSum_exp_mulVec (s • A) φ x
    have e : ∀ n : ℕ, ((n.factorial : ℂ))⁻¹ * φ (((s • A) ^ n) *ᵥ x) =
        ((n.factorial : ℂ))⁻¹ * l ((((s : ℂ) • L) ^ n) T) := fun n => by
      rw [smul_pow, smul_pow, Matrix.smul_mulVec, LinearMap.map_smul_of_tower, hpow, LinearMap.smul_apply,
        map_smul]
      simp [Complex.real_smul]
    simp only [e] at h2
    rw [h2.unique h1, hl _ hUN]
  let ψ : Matrix (Fin (Module.finrank ℂ N0)) (Fin (Module.finrank ℂ N0)) ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun M => φ (M *ᵥ x)
      map_add' := fun M M' => by simp [Matrix.add_mulVec]
      map_smul' := fun r M => by
        rw [Matrix.smul_mulVec, LinearMap.map_smul_of_tower]; rfl }
  have hd : HasDerivAt (fun u : ℝ => ψ.toContinuousLinearMap (NormedSpace.exp (u • A)))
      (ψ.toContinuousLinearMap (A * NormedSpace.exp ((0 : ℝ) • A))) 0 :=
    (ψ.toContinuousLinearMap).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_exp_smul_const' A (0 : ℝ))
  have hz : (fun u : ℝ => ψ.toContinuousLinearMap (NormedSpace.exp (u • A))) = fun _ => 0 := by
    funext u; exact hg u
  rw [hz] at hd
  have := hd.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))
  simp only [zero_smul, NormedSpace.exp_zero, mul_one] at this
  have e2 : ψ.toContinuousLinearMap A = l (L T) := by
    show φ (A *ᵥ x) = _
    simp only [φ, LinearMap.comp_apply, A, emb_mulVec, x, emb_crd]
  rw [← e2]; exact this

end GlobalTheory.FockKStab
end

noncomputable section
namespace GlobalTheory.FockKStab
open Matrix

theorem jm_mul_jm (R S : ℕ) : Formalism.BasicNotions.TH.Jm R S * Formalism.BasicNotions.TH.Jm R S = 1 := by
  simp [Formalism.BasicNotions.TH.Jm, Formalism.UG.Jpq, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

theorem commute_jm {R S : ℕ} {X : Mat R S} (hX : IsKC X) : Commute X (Formalism.BasicNotions.TH.Jm R S) := by
  show X * _ = _ * X
  have h1 : ∀ i j, X (Sum.inl i) (Sum.inr j) = 0 := fun i j => hX _ _ (by simp [sameBlock])
  have h2 : ∀ i j, X (Sum.inr i) (Sum.inl j) = 0 := fun i j => hX _ _ (by simp [sameBlock])
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Formalism.BasicNotions.TH.Jm, Formalism.UG.Jpq, Matrix.mul_apply, Matrix.fromBlocks, Fintype.sum_sum_type, Matrix.one_apply, h1, h2]

theorem isKC_smul {R S : ℕ} {X : Mat R S} (hX : IsKC X) (c : ℂ) : IsKC (c • X) := fun a b h => by
  simp [hX a b h]

theorem isKC_zero (R S : ℕ) : IsKC (0 : Mat R S) := fun a b _ => rfl

theorem isKC_add {R S : ℕ} {X X' : Mat R S} (hX : IsKC X) (hX' : IsKC X') : IsKC (X + X') := fun a b h => by
  simp [hX a b h, hX' a b h]

theorem isKC_conjTranspose {R S : ℕ} {X : Mat R S} (hX : IsKC X) : IsKC Xᴴ := fun a b h => by
  have h' : ¬ sameBlock b a := by
    intro h2; apply h; rcases a with a | a <;> rcases b with b | b <;> simp_all [sameBlock]
  simp [Matrix.conjTranspose_apply, hX b a h']

theorem mem_upq {R S : ℕ} {X : Mat R S} (hX : IsKC X) (hs : Xᴴ = -X) : X ∈ upq R S := by
  show Xᴴ * _ + _ * X = 0
  rw [hs, ← (commute_jm hX).eq]; simp

theorem frame_inv {α : Type} [Fintype α] [DecidableEq α] {R S : ℕ} {M : Matrix α α ℂ} {C : Matrix α (Ix R S) ℂ}
    {A' : Matrix (Ix R S) α ℂ} (h : IsFrame M C) (hA : C * A' = 1) : A' * C = 1 := by
  set K := M * C.map star * Formalism.BasicNotions.TH.Jm R S
  have h1 : Cᵀ * K = 1 := by
    simp only [K, ← Matrix.mul_assoc, h.1, jm_mul_jm]
  have h2 : Kᵀ * C = 1 := by
    have := congrArg Matrix.transpose h1
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this
  have h3 : A' = Kᵀ := by
    calc A' = (Kᵀ * C) * A' := by rw [h2, Matrix.one_mul]
      _ = Kᵀ := by rw [Matrix.mul_assoc, hA, Matrix.mul_one]
  rw [h3, h2]

theorem commute_of_frame {α : Type} [Fintype α] [DecidableEq α] {R S : ℕ} {C : Matrix α (Ix R S) ℂ}
    {A' : Matrix (Ix R S) α ℂ} (hCA : C * A' = 1) (hAC : A' * C = 1) {G θ : Matrix α α ℂ} {E : Mat R S}
    (hG : G * C = C * E) (hθ : θ * C = C * Formalism.BasicNotions.TH.Jm R S) (hE : Commute E (Formalism.BasicNotions.TH.Jm R S)) : Commute G θ := by
  have hG' : G = C * E * A' := by rw [← hG, Matrix.mul_assoc, hCA, Matrix.mul_one]
  have hθ' : A' * θ = Formalism.BasicNotions.TH.Jm R S * A' := by
    calc A' * θ = A' * θ * (C * A') := by rw [hCA, Matrix.mul_one]
      _ = A' * (θ * C) * A' := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hθ]; simp only [← Matrix.mul_assoc, hAC, Matrix.one_mul]
  show G * θ = θ * G
  rw [hG']
  calc C * E * A' * θ = C * E * (A' * θ) := by rw [Matrix.mul_assoc]
    _ = C * (E * Formalism.BasicNotions.TH.Jm R S) * A' := by rw [hθ']; simp only [Matrix.mul_assoc]
    _ = (θ * C) * E * A' := by rw [hE.eq, hθ]; simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

end GlobalTheory.FockKStab
end

noncomputable section
namespace GlobalTheory.FockKStab
open Matrix

section Tensor
variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

theorem atPl_eq' (w : ι) (L : Module.End ℂ (V w)) :
    atPl w L = PiTensorProduct.mapMultilinear ℂ V V (Function.update (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w L) := rfl

theorem atPl_add' (w : ι) (L L' : Module.End ℂ (V w)) : atPl w (L + L') = atPl w L + atPl w L' := by
  simp only [atPl_eq', MultilinearMap.map_update_add]

theorem atPl_smul' (w : ι) (c : ℂ) (L : Module.End ℂ (V w)) : atPl w (c • L) = c • atPl w L := by
  simp only [atPl_eq', MultilinearMap.map_update_smul, RingHom.id_apply]

theorem atPl_zero' (w : ι) : atPl w (0 : Module.End ℂ (V w)) = 0 := by
  simp only [atPl_eq', MultilinearMap.map_update_zero]

theorem atPl_one' (w : ι) : atPl w (1 : Module.End ℂ (V w)) = 1 := by
  rw [atPl_eq', show Function.update (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w 1 = fun i => LinearMap.id by
    funext i; by_cases h : i = w
    · subst h; simp; rfl
    · simp [Function.update_of_ne h]]
  exact PiTensorProduct.map_id

end Tensor

theorem locFin_fock2' (P Q R S : ℕ) (Y : Mat R S) (hY : IsKC Y) (c : ℂ) :
    LocFin (fockAct2 P Q R S Y + c • 1) := fun v => by
  obtain ⟨⟨W, hW, hv, hs⟩, -⟩ := (GlobalTheory.FockPolGK.pol_locFin_weights P Q R S).2 v
  exact ⟨W, hW, hv, fun y hy => W.add_mem (hs Y hY y hy) (W.smul_mem c hy)⟩


set_option maxHeartbeats 1000000 in
theorem kstab_skew : GlobalTheory.RealLift.ActsLaws → GlobalTheory.RealLift.LineEx → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d P Q R S : ℕ) (X : Spc F E n) (W : Spc F E d) (om : Rep σ X W)
    (C : InfinitePlace F → Matrix (Fin d) (Formalism.BasicNotions.TH.Ix R S) ℂ) (Φ : GlobalTheory.RealLift.Tens F P Q R S →ₗ[ℂ] SInf F (Fin n × Fin d))
    (c : InfinitePlace F → ℂ), IsCMExt F E σ →
    (∀ w, GlobalTheory.RealLift.IsFrame (Complex.I • (incM F W.J).map (piInf (B.emb w))) (C w)) →
    (∀ w, W.θ w * C w = C w * Formalism.BasicNotions.TH.Jm R S) → Function.Injective Φ →
    GlobalTheory.RealLift.ActsBy B.emb C (om.comp (MonoidHom.inr _ _)) Φ (Formalism.BasicNotions.TH.fockAct2 P Q R S) c →
    (∀ g, ∀ l ∈ (adeleClass F).adm (Fin n × Fin d), l ∘ₗ om g ∈ (adeleClass F).adm (Fin n × Fin d)) →
    ∀ N : Submodule ℂ (GlobalTheory.RealLift.Tens F P Q R S),
      (∀ k ∈ KInf σ W B.emb, ∀ T ∈ N, ∀ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) (Φ T) f₁ → f₁ ∈ N.map Φ) →
      ∀ w (Y : Formalism.BasicNotions.TH.Mat R S), Formalism.BasicNotions.TH.IsKC Y → Yᴴ = -Y → ∀ T ∈ N,
        GlobalTheory.RealLift.atPl (V := fun _ : InfinitePlace F => Formalism.BasicNotions.TH.Pol P Q R S) w (Formalism.BasicNotions.TH.fockAct2 P Q R S Y) T ∈ N := by
  intro hAL hLE F E _ _ _ _ _ σ B n d P Q R S X W om C Φ c hcm hC hθ hinj hact hadm N hN w
  intro Y hY hYs T hT
  set L0 : Module.End ℂ (Tens F P Q R S) :=
    atPl (V := fun _ : InfinitePlace F => Formalism.BasicNotions.TH.Pol P Q R S) w (fockAct2 P Q R S Y + (c w * Y.trace) • 1) with hL0
  set Ys : ℝ → InfinitePlace F → Mat R S := fun s w' => if w' = w then (s : ℂ) • Y else 0 with hYsdef
  have hYsKC : ∀ s w', IsKC (Ys s w') := by
    intro s w'; by_cases h : w' = w
    · simp only [hYsdef, if_pos h]; exact isKC_smul hY _
    · simp only [hYsdef, if_neg h]; exact isKC_zero R S
  have hYsU : ∀ s w', Ys s w' ∈ upq R S := by
    intro s w'; apply mem_upq (hYsKC s w'); by_cases h : w' = w
    · simp [hYsdef, h, Matrix.conjTranspose_smul, hYs]
    · simp [hYsdef, h]
  have hsum : ∀ s : ℝ, sumPl (V := fun _ : InfinitePlace F => Formalism.BasicNotions.TH.Pol P Q R S)
      (fun w' => fockAct2 P Q R S (Ys s w') + (c w' * (Ys s w').trace) • 1) = (s : ℂ) • L0 := by
    intro s
    unfold sumPl
    rw [Finset.sum_eq_single w]
    · rw [hL0, ← atPl_smul']
      congr 1
      simp only [hYsdef, if_pos rfl, map_smul, Matrix.trace_smul, smul_add, smul_smul, smul_eq_mul]
      congr 2; ring
    · intro w' _ hw'; simp [hYsdef, hw', atPl_zero']
    · simp
  have hloc : ∀ s : ℝ, LocFin (sumPl (V := fun _ : InfinitePlace F => Formalism.BasicNotions.TH.Pol P Q R S)
      (fun w' => fockAct2 P Q R S (Ys s w') + (c w' * (Ys s w').trace) • 1)) := fun s =>
    GlobalTheory.RealLift.locFin_sumPl _ _ _ (fun w' => locFin_fock2' P Q R S _ (hYsKC s w') _)
  have hexp : ∀ s : ℝ, ∃ U : Module.End ℂ (Tens F P Q R S), IsExp ((s : ℂ) • L0) U ∧ U T ∈ N := by
    intro s
    obtain ⟨γ, hγ, hgen⟩ := hLE F E σ (Fin d) R S B.emb (incM F W.J) Complex.I C hcm hC (Ys s) (hYsU s)
    obtain ⟨U, hU, hSA⟩ := GlobalTheory.ExpAct.expAct_fock F (Fin n × Fin d) _ Φ _
      ((om.comp (MonoidHom.inr _ _)).comp γ) (hloc s) (fun t l hl => hadm _ l hl) (fun T => hact γ hγ (Ys s) hgen T)
    refine ⟨U, hsum s ▸ hU, ?_⟩
    have h1 := (hAL F _ (Φ T) (Φ (U T)) (Φ (U T))).2.1 _ (map_zero _) (hSA T)
    have hk : γ (Multiplicative.ofAdd 1) ∈ KInf σ W B.emb := by
      refine ⟨hγ.2 _, fun w' => ?_⟩
      obtain ⟨A', hA'⟩ := (hC w').2
      exact commute_of_frame hA' (frame_inv (hC w') hA') (hgen 1 w') (hθ w')
        (Commute.exp_left (Commute.smul_left (commute_jm (hYsKC s w')) _))
    have h2 := hN _ hk T hT _ h1
    obtain ⟨y, hy, e⟩ := Submodule.mem_map.1 h2
    exact hinj e ▸ hy
  have hL0loc : LocFin L0 := by
    have := hloc 1
    rwa [hsum 1, Complex.ofReal_one, one_smul] at this
  have hmem := mem_of_exp L0 hL0loc N T hexp
  have e : L0 T = atPl (V := fun _ : InfinitePlace F => Formalism.BasicNotions.TH.Pol P Q R S) w (fockAct2 P Q R S Y) T +
      (c w * Y.trace) • T := by
    simp [hL0, atPl_add', atPl_smul', atPl_one']
  rw [e] at hmem
  simpa using N.sub_mem hmem (N.smul_mem (c w * Y.trace) hT)


set_option maxHeartbeats 1000000 in
theorem kstab : GlobalTheory.RealLift.ActsLaws → GlobalTheory.RealLift.LineEx →
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d P Q R S : ℕ) (X : Spc F E n) (W : Spc F E d) (om : Rep σ X W)
    (C : InfinitePlace F → Matrix (Fin d) (Formalism.BasicNotions.TH.Ix R S) ℂ) (Φ : GlobalTheory.RealLift.Tens F P Q R S →ₗ[ℂ] SInf F (Fin n × Fin d))
    (c : InfinitePlace F → ℂ), IsCMExt F E σ →
    (∀ w, GlobalTheory.RealLift.IsFrame (Complex.I • (incM F W.J).map (piInf (B.emb w))) (C w)) →
    (∀ w, W.θ w * C w = C w * Formalism.BasicNotions.TH.Jm R S) → Function.Injective Φ →
    GlobalTheory.RealLift.ActsBy B.emb C (om.comp (MonoidHom.inr _ _)) Φ (Formalism.BasicNotions.TH.fockAct2 P Q R S) c →
    (∀ g, ∀ l ∈ (adeleClass F).adm (Fin n × Fin d), l ∘ₗ om g ∈ (adeleClass F).adm (Fin n × Fin d)) →
    ∀ N : Submodule ℂ (GlobalTheory.RealLift.Tens F P Q R S),
      (∀ k ∈ KInf σ W B.emb, ∀ T ∈ N, ∀ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) (Φ T) f₁ → f₁ ∈ N.map Φ) →
      ∀ w (Z : Formalism.BasicNotions.TH.Mat R S), Formalism.BasicNotions.TH.IsKC Z → ∀ T ∈ N,
        GlobalTheory.RealLift.atPl (V := fun _ : InfinitePlace F => Formalism.BasicNotions.TH.Pol P Q R S) w (Formalism.BasicNotions.TH.fockAct2 P Q R S Z) T ∈ N := by
  intro hAL hLE F E _ _ _ _ _ σ B n d P Q R S X W om C Φ c hcm hC hθ hinj hact hadm N hN w Z hZ T hT
  have key := kstab_skew hAL hLE F E σ B n d P Q R S X W om C Φ c hcm hC hθ hinj hact hadm N hN w
  obtain ⟨Y1, hY1⟩ : ∃ Y1 : Mat R S, Y1 = (1 / 2 : ℂ) • (Z - Zᴴ) := ⟨_, rfl⟩
  obtain ⟨Y2, hY2⟩ : ∃ Y2 : Mat R S, Y2 = (1 / (2 * Complex.I)) • (Z + Zᴴ) := ⟨_, rfl⟩
  have hZ' : Z = Y1 + Complex.I • Y2 := by
    rw [hY1, hY2, smul_smul, show Complex.I * (1 / (2 * Complex.I)) = 1 / 2 by field_simp, ← smul_add]
    rw [show Z - Zᴴ + (Z + Zᴴ) = (2 : ℂ) • Z by rw [two_smul]; abel, smul_smul]; norm_num
  have hZh : IsKC Zᴴ := isKC_conjTranspose hZ
  have k1 : IsKC Y1 := hY1 ▸ isKC_smul (by rw [sub_eq_add_neg]; exact isKC_add hZ (by simpa using isKC_smul hZh (-1))) _
  have k2 : IsKC Y2 := hY2 ▸ isKC_smul (isKC_add hZ hZh) _
  have s1 : Y1ᴴ = -Y1 := by
    rw [hY1, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose]
    rw [show star (1 / 2 : ℂ) = 1 / 2 by simp, ← smul_neg, neg_sub]
  have s2 : Y2ᴴ = -Y2 := by
    rw [hY2, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose]
    rw [show star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) by simp, neg_smul, add_comm]
  rw [hZ', map_add (f := _), map_smul, atPl_add', atPl_smul', LinearMap.add_apply, LinearMap.smul_apply]
  exact N.add_mem (key Y1 k1 s1 T hT) (N.smul_mem _ (key Y2 k2 s2 T hT))

end GlobalTheory.FockKStab
end
end

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.RealLift Formalism.BasicNotions.TH GlobalTheory.FockBridge

namespace GlobalTheory.FockBottom

section Alg

variable {V Z : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup Z] [Module ℂ Z]

theorem isExp_mem {L U : Module.End ℂ V} (hU : IsExp L U) (N : Submodule ℂ V) (hN : ∀ v ∈ N, L v ∈ N) {T : V}
    (hT : T ∈ N) : U T ∈ N := by
  rw [← Submodule.Quotient.mk_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro l'
  have hp : ∀ n : ℕ, (L ^ n) T ∈ N := fun n => by
    induction n with
    | zero => simpa using hT
    | succ n ih => rw [pow_succ', Module.End.mul_apply]; exact hN _ ih
  have h := hU T (l' ∘ₗ N.mkQ)
  have e : (fun n : ℕ => ((n.factorial : ℂ))⁻¹ * (l' ∘ₗ N.mkQ) ((L ^ n) T)) = fun _ => 0 := by
    funext n
    simp [(Submodule.Quotient.mk_eq_zero N).2 (hp n)]
  rw [e] at h
  exact h.unique hasSum_zero

theorem isExp_eig {L U : Module.End ℂ V} (hU : IsExp L U) (q : V →ₗ[ℂ] Z) (L0 : Module.End ℂ Z)
    (h : ∀ v, q (L v) = L0 (q v)) {T : V} {μ : ℂ} (hT : L0 (q T) = μ • q T) : q (U T) = Complex.exp μ • q T := by
  refine sub_eq_zero.1 ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun l => ?_)
  rw [map_sub, sub_eq_zero, map_smul, smul_eq_mul]
  have hp : ∀ n : ℕ, q ((L ^ n) T) = μ ^ n • q T := fun n => by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', Module.End.mul_apply, h, ih, map_smul, hT, smul_smul, pow_succ]
  have a := hU T (l ∘ₗ q)
  simp only [LinearMap.comp_apply, hp, map_smul, smul_eq_mul] at a
  have b := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) μ).mul_right (l (q T))
  rw [← Complex.exp_eq_exp_ℂ] at b
  simp only [smul_eq_mul, mul_assoc] at b
  exact a.unique b

theorem exp_mul_eq {a b : ℂ} (h : ∀ s : ℝ, Complex.exp (s * a) = Complex.exp (s * b)) : a = b := by
  have d : ∀ z : ℂ, HasDerivAt (fun s : ℝ => Complex.exp (s * z)) z 0 := fun z => by
    have h1 : HasDerivAt (fun s : ℝ => (s : ℂ) * z) z 0 := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := 0)).mul_const z
    simpa using h1.cexp
  have e : (fun s : ℝ => Complex.exp (s * a)) = fun s : ℝ => Complex.exp (s * b) := funext h
  exact (d a).unique (e ▸ d b)

theorem bottom_of_sum (D₁ D₂ : Module.End ℂ V) (a : ℂ) {v : V}
    (hv : v ∈ ⨆ n : ℕ × ℕ, D₁.eigenspace (a + n.1) ⊓ D₂.eigenspace (-a + n.2)) (h0 : D₁ v + D₂ v = 0) :
    D₁ v = a • v ∧ D₂ v = (-a) • v := by
  have hle : (⨆ n : ℕ × ℕ, D₁.eigenspace (a + n.1) ⊓ D₂.eigenspace (-a + n.2)) ≤
      (D₁.eigenspace a ⊓ D₂.eigenspace (-a)) ⊔ ⨆ μ ≠ (0 : ℂ), (D₁ + D₂).eigenspace μ := by
    refine iSup_le fun n => ?_
    by_cases hn : n = 0
    · subst hn; simp
    · refine le_sup_of_le_right (le_iSup₂_of_le ((n.1 + n.2 : ℕ) : ℂ) ?_ ?_)
      · rw [Nat.cast_ne_zero]
        intro h; apply hn; ext <;> simp <;> omega
      · intro x hx
        have h1 := Module.End.mem_eigenspace_iff.1 hx.1
        have h2 := Module.End.mem_eigenspace_iff.1 hx.2
        rw [Module.End.mem_eigenspace_iff, LinearMap.add_apply, h1, h2, ← add_smul]
        congr 1; push_cast; ring
  obtain ⟨y, hy, z, hz, e⟩ := Submodule.mem_sup.1 (hle hv)
  have h1 := Module.End.mem_eigenspace_iff.1 hy.1
  have h2 := Module.End.mem_eigenspace_iff.1 hy.2
  have hz0 : z ∈ (D₁ + D₂).eigenspace 0 := by
    rw [Module.End.mem_eigenspace_iff, zero_smul, show z = v - y by rw [← e]; abel, map_sub, LinearMap.add_apply, h0,
      LinearMap.add_apply, h1, h2]
    simp
  have := (Submodule.disjoint_def.1 ((Module.End.eigenspaces_iSupIndep (D₁ + D₂)) 0)) z hz0 hz
  rw [this, add_zero] at e
  exact e ▸ ⟨h1, h2⟩

theorem eq_zero_of_below (D : Module.End ℂ V) (a : ℂ) {ι : Type} (f : ι → ℕ) (N : ι → Submodule ℂ V)
    (hN : ∀ i, N i ≤ D.eigenspace (a + f i)) {v : V} (hv : v ∈ ⨆ i, N i) (h : D v = (a - 1) • v) : v = 0 := by
  have hle : (⨆ i, N i) ≤ ⨆ μ ≠ (a - 1), D.eigenspace μ := by
    refine iSup_le fun i => le_iSup₂_of_le (a + f i) ?_ (hN i)
    intro e
    have : ((f i + 1 : ℕ) : ℂ) = 0 := by push_cast; linear_combination e
    exact Nat.succ_ne_zero _ (Nat.cast_eq_zero.1 this)
  exact (Submodule.disjoint_def.1 ((Module.End.eigenspaces_iSupIndep D) (a - 1))) v
    (Module.End.mem_eigenspace_iff.2 h) (hle hv)

end Alg

section Mat

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem exp_col {n : Type} [Fintype n] [DecidableEq n] (Y : Matrix n n ℂ) (c : n) (μ : ℂ)
    (h : ∀ a, Y a c = if a = c then μ else 0) (a : n) :
    NormedSpace.exp Y a c = if a = c then Complex.exp μ else 0 := by
  have hp : ∀ (k : ℕ) a, (Y ^ k) a c = if a = c then μ ^ k else 0 := fun k => by
    induction k with
    | zero => intro a; simp [Matrix.one_apply]
    | succ k ih =>
      intro a
      rw [pow_succ', Matrix.mul_apply]
      simp only [ih, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, h]
      split_ifs <;> simp [pow_succ']
  have h1 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) Y).mapL
    (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ a c))
  have e : ∀ M : Matrix n n ℂ, LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ a c) M = M a c := fun _ => rfl
  simp only [e, Matrix.smul_apply, hp] at h1
  split_ifs at h1 ⊢
  · rw [Complex.exp_eq_exp_ℂ]
    exact h1.unique (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) μ)
  · simp only [smul_zero] at h1
    exact h1.unique hasSum_zero

theorem mul_exp_col {m n : Type} [Fintype n] [DecidableEq n] (C : Matrix m n ℂ) (Y : Matrix n n ℂ) (c : n) (μ : ℂ)
    (h : ∀ a, Y a c = if a = c then μ else 0) (i : m) :
    (C * NormedSpace.exp Y) i c = Complex.exp μ * C i c := by
  rw [Matrix.mul_apply]
  simp [exp_col Y c μ h, mul_comm]

end Mat

theorem jm_conjTranspose (R S : ℕ) : (Formalism.BasicNotions.TH.Jm R S)ᴴ = Formalism.BasicNotions.TH.Jm R S := by
  simp [Formalism.BasicNotions.TH.Jm, Formalism.UG.Jpq, Matrix.fromBlocks_conjTranspose]

theorem upq_decomp {R S : ℕ} (Z : Mat R S) : ∃ Y₁ ∈ upq R S, ∃ Y₂ ∈ upq R S, Z = Y₁ + Complex.I • Y₂ := by
  set J := Formalism.BasicNotions.TH.Jm R S
  have hJ : J * J = 1 := GlobalTheory.FockKStab.jm_mul_jm R S
  have hJ' : Jᴴ = J := jm_conjTranspose R S
  have h1 : ∀ M : Mat R S, J * (J * M) = M := fun M => by rw [← Matrix.mul_assoc, hJ, Matrix.one_mul]
  refine ⟨(1 / 2 : ℂ) • (Z - J * Zᴴ * J), ?_, (1 / (2 * Complex.I)) • (Z + J * Zᴴ * J), ?_, ?_⟩
  · show _ * J + J * _ = 0
    rw [Matrix.conjTranspose_smul, show star (1 / 2 : ℂ) = 1 / 2 by simp, Matrix.smul_mul, Matrix.mul_smul, ← smul_add]
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJ', Matrix.sub_mul,
      Matrix.mul_sub, Matrix.mul_assoc, hJ, h1, Matrix.mul_one]
    simp
  · show _ * J + J * _ = 0
    rw [Matrix.conjTranspose_smul, show star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) by simp, neg_smul,
      Matrix.neg_mul, Matrix.smul_mul, Matrix.mul_smul, neg_add_eq_zero]
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJ', Matrix.add_mul,
      Matrix.mul_add, Matrix.mul_assoc, hJ, h1, Matrix.mul_one]
    rw [add_comm]
  · rw [smul_smul, show Complex.I * (1 / (2 * Complex.I)) = 1 / 2 by field_simp, ← smul_add]
    rw [show Z - J * Zᴴ * J + (Z + J * Zᴴ * J) = (2 : ℂ) • Z by rw [two_smul]; abel, smul_smul]; norm_num

section Tens

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d P Q R S : ℕ} {Y : Spc F E n} {W : Spc F E d}

def genOp (P Q : ℕ) (c : InfinitePlace F → ℂ) (Yg : InfinitePlace F → Mat R S) : Module.End ℂ (Tens F P Q R S) :=
  sumPl (V := fun _ : InfinitePlace F => Formalism.BasicNotions.TH.Pol P Q R S) fun w => fockAct2 P Q R S (Yg w) + (c w * (Yg w).trace) • 1

theorem genOp_apply (c : InfinitePlace F → ℂ) (Yg : InfinitePlace F → Mat R S) (T : Tens F P Q R S) :
    genOp P Q c Yg T = ∑ w, (atPl (V := fun _ : InfinitePlace F => Formalism.BasicNotions.TH.Pol P Q R S) w (fockAct2 P Q R S (Yg w)) T +
      (c w * (Yg w).trace) • T) := by
  simp [genOp, sumPl, LinearMap.sum_apply, Main.atPl_add, Main.atPl_smul, Main.atPl_one]

theorem genOp_single (c : InfinitePlace F → ℂ) (w : InfinitePlace F) (Z : Mat R S) (T : Tens F P Q R S) :
    genOp P Q c (Pi.single w Z) T = atPl (V := fun _ : InfinitePlace F => Formalism.BasicNotions.TH.Pol P Q R S) w (fockAct2 P Q R S Z) T +
      (c w * Z.trace) • T := by
  rw [genOp_apply, Finset.sum_eq_single w]
  · simp
  · intro w' _ h
    simp [Pi.single_eq_of_ne h, Main.atPl_zero]
  · simp

theorem genOp_smul (c : InfinitePlace F → ℂ) (Yg : InfinitePlace F → Mat R S) (s : ℂ) :
    genOp P Q c (s • Yg) = s • genOp P Q c Yg := by
  refine LinearMap.ext fun T => ?_
  rw [LinearMap.smul_apply, genOp_apply, genOp_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [Pi.smul_apply, map_smul, Main.atPl_smul, LinearMap.smul_apply, Matrix.trace_smul, smul_add, smul_smul,
    smul_eq_mul]
  congr 2; ring

theorem genOp_locFin (c : InfinitePlace F → ℂ) {Yg : InfinitePlace F → Mat R S} (h : ∀ w, IsKC (Yg w)) :
    LocFin (genOp P Q c Yg) :=
  Main.i_locfin _ _ _ fun w => Main.locFin_fock2 P Q R S (Yg w) (h w) _

variable {B : Base F E} {om : Rep σ Y W} {C : InfinitePlace F → Matrix (Fin d) (Ix R S) ℂ}
  {Φ : Tens F P Q R S →ₗ[ℂ] SInf F (Fin n × Fin d)} {c : InfinitePlace F → ℂ}

theorem acts_unique {T : ((Fin n × Fin d → AF F) → ℂ) → (Fin n × Fin d → AF F) → ℂ} {f f₁ f₂ : SInf F (Fin n × Fin d)}
    (h₁ : Acts (evI F) T f f₁) (h₂ : Acts (evI F) T f f₂) : f₁ = f₂ :=
  (Main.i_actslaws F _ f f₁ f₂).2.2.2.1 T h₁ h₂

theorem exp_of_gen (hact : ActsBy B.emb C (om.comp (MonoidHom.inr _ _)) Φ (fockAct2 P Q R S) c)
    (hadm : ∀ g, ∀ l ∈ (adeleClass F).adm (Fin n × Fin d), l ∘ₗ om g ∈ (adeleClass F).adm (Fin n × Fin d))
    {γ : Multiplicative ℝ →* UG (cA σ) (incM F W.J)} (hγ : γ ∈ RLines (σ := σ) (incM F W.J)) {Yg : InfinitePlace F → Mat R S}
    (hY : IsGen B.emb C γ Yg) (hKC : ∀ w, IsKC (Yg w)) :
    ∃ U : Module.End ℂ (Tens F P Q R S), IsExp (genOp P Q c Yg) U ∧
      ∀ T, Acts (evI F) (om (1, γ (Multiplicative.ofAdd 1))) (Φ T) (Φ (U T)) := by
  obtain ⟨U, hU, hSA⟩ := Main.i_expact F (Fin n × Fin d) _ Φ _ ((om.comp (MonoidHom.inr _ _)).comp γ)
    (genOp_locFin c hKC) (fun t l hl => hadm _ l hl) (fun T => hact γ hγ Yg hY T)
  exact ⟨U, hU, fun T => (Main.i_actslaws F _ (Φ T) (Φ (U T)) (Φ T)).2.1 _ (map_zero _) (hSA T)⟩

theorem exp_of_kInf (hcm : IsCMExt F E σ) (hC : ∀ w, IsFrame (Complex.I • (incM F W.J).map (piInf (B.emb w))) (C w))
    (hθ : ∀ w, W.θ w * C w = C w * Formalism.BasicNotions.TH.Jm R S)
    (hact : ActsBy B.emb C (om.comp (MonoidHom.inr _ _)) Φ (fockAct2 P Q R S) c)
    (hadm : ∀ g, ∀ l ∈ (adeleClass F).adm (Fin n × Fin d), l ∘ₗ om g ∈ (adeleClass F).adm (Fin n × Fin d))
    {k : UA σ W.J} (hk : k ∈ KInf σ W B.emb) :
    ∃ (Yg : InfinitePlace F → Mat R S) (U : Module.End ℂ (Tens F P Q R S)), (∀ w, IsKC (Yg w)) ∧
      IsExp (genOp P Q c Yg) U ∧ ∀ T, Acts (evI F) (om (1, k)) (Φ T) (Φ (U T)) := by
  obtain ⟨γ, hγ, Yg, hgen, hKC, hγ1⟩ :=
    Main.i_kline Main.i_lineex F E σ (Fin d) R S B.emb (incM F W.J) Complex.I C W.θ hcm hC hθ k hk.1 hk.2
  obtain ⟨U, hU, hA⟩ := exp_of_gen hact hadm hγ hgen hKC
  exact ⟨Yg, U, hKC, hU, hγ1 ▸ hA⟩

theorem exp_of_skew (hcm : IsCMExt F E σ) (hC : ∀ w, IsFrame (Complex.I • (incM F W.J).map (piInf (B.emb w))) (C w))
    (hθ : ∀ w, W.θ w * C w = C w * Formalism.BasicNotions.TH.Jm R S)
    (hact : ActsBy B.emb C (om.comp (MonoidHom.inr _ _)) Φ (fockAct2 P Q R S) c)
    (hadm : ∀ g, ∀ l ∈ (adeleClass F).adm (Fin n × Fin d), l ∘ₗ om g ∈ (adeleClass F).adm (Fin n × Fin d))
    (Yg : InfinitePlace F → Mat R S) (hKC : ∀ w, IsKC (Yg w)) (hs : ∀ w, (Yg w)ᴴ = -Yg w) :
    ∃ k ∈ KInf σ W B.emb, (∀ w, (mat k).map (piInf (B.emb w)) * C w = C w * NormedSpace.exp (Yg w)) ∧
      ∃ U : Module.End ℂ (Tens F P Q R S), IsExp (genOp P Q c Yg) U ∧ ∀ T, Acts (evI F) (om (1, k)) (Φ T) (Φ (U T)) := by
  obtain ⟨γ, hγ, hgen⟩ := Main.i_lineex F E σ (Fin d) R S B.emb (incM F W.J) Complex.I C hcm hC Yg
    fun w => GlobalTheory.FockKStab.mem_upq (hKC w) (hs w)
  have h1 : ∀ w, (mat (γ (Multiplicative.ofAdd 1))).map (piInf (B.emb w)) * C w = C w * NormedSpace.exp (Yg w) := fun w => by
    have := hgen 1 w
    rwa [one_smul] at this
  refine ⟨γ (Multiplicative.ofAdd 1), ⟨hγ.2 _, fun w => ?_⟩, h1, exp_of_gen hact hadm hγ hgen hKC⟩
  obtain ⟨A', hA'⟩ := (hC w).2
  exact GlobalTheory.FockKStab.commute_of_frame hA' (GlobalTheory.FockKStab.frame_inv (hC w) hA') (h1 w) (hθ w)
    (Commute.exp_left (GlobalTheory.FockKStab.commute_jm (hKC w)))

theorem eq_of_frame (hcm : IsCMExt F E σ) (hC : ∀ w, IsFrame (Complex.I • (incM F W.J).map (piInf (B.emb w))) (C w))
    {k k' : UA σ W.J} (hk : k ∈ UAt σ W (evI F)) (hk' : k' ∈ UAt σ W (evI F))
    (h : ∀ w, (mat k).map (piInf (B.emb w)) * C w = (mat k').map (piInf (B.emb w)) * C w) : k = k' := by
  apply Subtype.ext; apply Units.ext
  show mat k = mat k'
  ext i j
  rw [← sub_eq_zero]
  refine GlobalTheory.RealLift.KLineProof.eq_zero_of_piInf hcm B.emb _ (fun u hu => ?_) fun w => ?_
  · have a := congrFun (congrFun (hk u hu) i) j
    have b := congrFun (congrFun (hk' u hu) i) j
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.zero_apply] at a b
    rw [show mat k i j - mat k' i j = (mat k i j - (1 : Matrix (Fin d) (Fin d) (AE F E)) i j) -
      (mat k' i j - (1 : Matrix (Fin d) (Fin d) (AE F E)) i j) by ring, smul_sub, a, b, sub_zero]
  · obtain ⟨A', hA'⟩ := (hC w).2
    have e := congrArg (· * A') (h w)
    simp only [Matrix.mul_assoc, hA', Matrix.mul_one] at e
    have := congrFun (congrFun e i) j
    simp only [Matrix.map_apply] at this
    rw [map_sub, this, sub_self]

theorem stab_of_fix (hcm : IsCMExt F E σ) (hC : ∀ w, IsFrame (Complex.I • (incM F W.J).map (piInf (B.emb w))) (C w))
    (hθ : ∀ w, W.θ w * C w = C w * Formalism.BasicNotions.TH.Jm R S)
    (hact : ActsBy B.emb C (om.comp (MonoidHom.inr _ _)) Φ (fockAct2 P Q R S) c)
    (hadm : ∀ g, ∀ l ∈ (adeleClass F).adm (Fin n × Fin d), l ∘ₗ om g ∈ (adeleClass F).adm (Fin n × Fin d))
    (I : Set (Ix R S)) (N : Submodule ℂ (Tens F P Q R S))
    (hN : ∀ k ∈ KInf σ W B.emb, (∀ w, ∀ b ∈ I, ∀ i, ((mat k).map (piInf (B.emb w)) * C w) i b = C w i b) →
      ∀ T ∈ N, ∀ T', Acts (evI F) (om (1, k)) (Φ T) (Φ T') → T' ∈ N)
    (w : InfinitePlace F) (Z : Mat R S) (hZ : IsKC Z) (hI : ∀ b ∈ I, ∀ a, Z a b = 0 ∧ Z b a = 0) {T : Tens F P Q R S}
    (hT : T ∈ N) : atPl (V := fun _ : InfinitePlace F => Formalism.BasicNotions.TH.Pol P Q R S) w (fockAct2 P Q R S Z) T ∈ N := by
  have key : ∀ Y : Mat R S, IsKC Y → Yᴴ = -Y → (∀ b ∈ I, ∀ a, Y a b = 0) →
      atPl (V := fun _ : InfinitePlace F => Formalism.BasicNotions.TH.Pol P Q R S) w (fockAct2 P Q R S Y) T ∈ N := by
    intro Y hY hs h0
    have hKC : ∀ (s : ℂ) w', IsKC ((s • (Pi.single w Y : InfinitePlace F → Mat R S)) w') := fun s w' => by
      refine GlobalTheory.FockKStab.isKC_smul ?_ s
      by_cases h : w' = w
      · subst h; simpa using hY
      · simpa [Pi.single_eq_of_ne h] using GlobalTheory.FockKStab.isKC_zero R S
    have hmem := GlobalTheory.FockKStab.mem_of_exp (genOp P Q c (Pi.single w Y)) (genOp_locFin c (by simpa using hKC 1)) N T
      fun s => by
        obtain ⟨k, hk, hkC, U, hU, hA⟩ := exp_of_skew hcm hC hθ hact hadm ((s : ℂ) • Pi.single w Y) (hKC s) fun w' => by
          by_cases h : w' = w
          · subst h; simp [Matrix.conjTranspose_smul, hs]
          · simp [Pi.single_eq_of_ne h]
        refine ⟨U, genOp_smul c _ (s : ℂ) ▸ hU, hN k hk (fun w' b hb i => ?_) T hT _ (hA T)⟩
        rw [hkC, mul_exp_col _ _ b 0, Complex.exp_zero, one_mul]
        intro a
        by_cases h : w' = w
        · subst h; simp [h0 b hb a]
        · simp [Pi.single_eq_of_ne h]
    rw [genOp_single] at hmem
    simpa using N.sub_mem hmem (N.smul_mem (c w * Y.trace) hT)
  have hZh : IsKC Zᴴ := GlobalTheory.FockKStab.isKC_conjTranspose hZ
  have hZ' : Z = (1 / 2 : ℂ) • (Z - Zᴴ) + Complex.I • (1 / (2 * Complex.I)) • (Z + Zᴴ) := by
    rw [smul_smul, show Complex.I * (1 / (2 * Complex.I)) = 1 / 2 by field_simp, ← smul_add]
    rw [show Z - Zᴴ + (Z + Zᴴ) = (2 : ℂ) • Z by rw [two_smul]; abel, smul_smul]; norm_num
  rw [hZ', map_add (f := _), map_smul _ Complex.I, Main.atPl_add, Main.atPl_smul, LinearMap.add_apply, LinearMap.smul_apply]
  refine N.add_mem (key _ ?_ ?_ ?_) (N.smul_mem _ (key _ ?_ ?_ ?_))
  · exact GlobalTheory.FockKStab.isKC_smul (fun a b h => by rw [Matrix.sub_apply, hZ a b h, hZh a b h, sub_zero]) _
  · rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose]
    rw [show star (1 / 2 : ℂ) = 1 / 2 by simp, ← smul_neg, neg_sub]
  · intro b hb a; simp [Matrix.conjTranspose_apply, hI b hb a]
  · exact GlobalTheory.FockKStab.isKC_smul (GlobalTheory.FockKStab.isKC_add hZ hZh) _
  · rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose]
    rw [show star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) by simp, neg_smul, add_comm]
  · intro b hb a; simp [Matrix.conjTranspose_apply, hI b hb a]

end Tens

end GlobalTheory.FockBottom
