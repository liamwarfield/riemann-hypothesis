module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.SplitLineAlt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleFiniteLength
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalSatakeAlmostAll

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.FinprodSplitAlt
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

def cv {G : Type} [Group G] (K : Subgroup G) (f g : G → ℂ) : G → ℂ := fun y => hint K fun z => f z * g (z⁻¹ * y)

def cf (q a b j : ℕ) (p : Fin (a + 1) × Fin (b + 1)) : ℂ :=
  if (p.1 : ℕ) + p.2 = j then
    (q : ℂ) ^ ((((p.1 : ℕ) : ℂ) * ((b : ℂ) - (p.2 : ℕ)) + ((p.2 : ℕ) : ℂ) * ((a : ℂ) - (p.1 : ℕ))) / 2) else 0

def chi {E : Type} [Field E] [NumberField E] [IsCMField E] (μ : HChar E) (a b : ℕ) (w : Pl E) (m : GLw a w × GLw b w) : ℂ :=
  (μ.loc w ((-1) ^ (a * b) * GeneralLinearGroup.det m.1 ^ b * GeneralLinearGroup.det m.2 ^ a) : ℂˣ)

def HintSph : Prop := ∀ (G : Type) [Group G] (K : Subgroup G) (u : G → ℂ), (∀ k ∈ K, ∀ x, u (x * k) = u x) → hint K u = ∑ᶠ q : G ⧸ K, u q.out

def CvHecke : Prop := ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G), IsOpen (K : Set G) → IsCompact (K : Set G) → ∀ f g : G → ℂ, IsHecke K f → IsHecke K g → IsHecke K (cv K f g)

def CvOp : Prop := ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G), IsOpen (K : Set G) → IsCompact (K : Set G) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (f g : G → ℂ), IsHecke K f → IsHecke K g →
  ∀ x ∈ fixed ρ K, levOp ρ K K (cv K f g) LinearMap.id x = levOp ρ K K f LinearMap.id (levOp ρ K K g LinearMap.id x) ∧
    levOp ρ K K g LinearMap.id x ∈ fixed ρ K ∧ levOp ρ K K g LinearMap.id x = heckeVec ρ K g x

def CtSph : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (n a b : ℕ) (h : a + b = n) (f : GLw n w → ℂ), IsHecke (KGL w (n := n)) f → ∀ m,
  ct h w f m = absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) *
      ∑ᶠ q : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) ⧸ intMat a b w, f (blk h w m (Multiplicative.toAdd q.out)) ∧
    (Function.support fun q : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) ⧸ intMat a b w =>
      f (blk h w m (Multiplicative.toAdd q.out))).Finite

def CtLin : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (n a b : ℕ) (h : a + b = n) (f g : GLw n w → ℂ) (c : ℂ), IsHecke (KGL w (n := n)) f → IsHecke (KGL w (n := n)) g →
  ct h w (fun y => f y + g y) = (fun m => ct h w f m + ct h w g m) ∧ ct h w (fun y => c * f y) = fun m => c * ct h w f m

def CtUnit : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (n a b : ℕ) (h : a + b = n), ct h w ((KGL w (n := n) : Set _).indicator 1) = (K2 a b w : Set _).indicator 1

def CtT : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (n a b : ℕ) (h : a + b = n) (j : Fin (n + 1)) (m : GLw a w × GLw b w),
  ct h w (Tj ℂ n (Ov E w) (unif w) j) m = ∑ p : Fin (a + 1) × Fin (b + 1),
    cf (qV E w) a b j p * (Tj ℂ a (Ov E w) (unif w) p.1 m.1 * Tj ℂ b (Ov E w) (unif w) p.2 m.2)

def CtMul : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (n a b : ℕ) (h : a + b = n) (f g : GLw n w → ℂ), IsHecke (KGL w (n := n)) f → IsHecke (KGL w (n := n)) g →
  ct h w (cv (KGL w (n := n)) f g) = cv (K2 a b w) (ct h w f) (ct h w g)

def SatSum : Prop := ∀ (q a b : ℕ), q ≠ 0 → ∀ (B₁ B₂ : Multiset ℂˣ) (c₁ c₂ : ℂˣ), B₁.card = a → B₂.card = b → ∀ j : ℕ,
  satEig q (a + b) (B₁.map (· * c₁) + B₂.map (· * c₂)) j = ∑ p : Fin (a + 1) × Fin (b + 1),
    cf q a b j p * (c₁ : ℂ) ^ (p.1 : ℕ) * (c₂ : ℂ) ^ (p.2 : ℕ) * (satEig q a B₁ p.1 * satEig q b B₂ p.2)

def MuTw : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (μ : HChar E), μ.UnrAt w → ∀ (a b : ℕ),
  (∀ m ∈ K2 a b w, chi μ a b w m = 1) ∧ (∀ m m', chi μ a b w (m * m') = chi μ a b w m * chi μ a b w m') ∧
  ∀ (i j : ℕ) (m : GLw a w × GLw b w), i ≤ a → j ≤ b → Tj ℂ a (Ov E w) (unif w) i m.1 * Tj ℂ b (Ov E w) (unif w) j m.2 ≠ 0 →
    chi μ a b w m = ((μ.val w ^ b : ℂˣ) : ℂ) ^ i * ((μ.val w ^ a : ℂˣ) : ℂ) ^ j

def LevelU : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E), IsSplitAt w → (∀ f : GLw n w → ℂ, Lc (KGL w (n := n)) f → Lc (KL n w) fun x : UL n w => f x.1) ∧
  ∀ f : GLw n w → ℂ, IsHecke (KGL w (n := n)) f → IsHecke (KL n w) fun x : UL n w => f x.1

def UnitHecke : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (w : Pl E), IsOpen (KL n w : Set (UL n w)) ∧ IsHecke (KL n w) ((KL n w : Set _).indicator 1) ∧
  IsOpen (KGL w (n := n) : Set (GLw n w)) ∧ IsCompact (KGL w (n := n) : Set (GLw n w)) ∧
  IsOpen (K2 a b w : Set (GLw a w × GLw b w)) ∧ IsCompact (K2 a b w : Set (GLw a w × GLw b w)) ∧
  ∀ k ∈ KGL w (n := n), thL n w k ∈ KGL w (n := n)

def TrUnit : Prop := ∀ (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G),
  twTr ρ K K ((K : Set G).indicator 1) LinearMap.id = (Module.finrank ℂ (fixed ρ K) : ℂ)

def TrSph : Prop := ExAct → SplitLine → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (τ : SmIrr (GLw n w)) (B : Multiset ℂˣ), HasSatGL w τ.ρ B → ∀ e,
  twTr τ.ρ (KGL w (n := n)) (KGL w (n := n)) (fn1 n w e) LinearMap.id = ev1 n w e B

def UnramOf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)) (π : Submodule ℂ (UA E n → ℂ)) (K' : ∀ w : Pl E, Subgroup (UL n w)), HasLevel S π K' →
  ∀ w ∈ S, K' w = KL n w → IsUnramU π w

def FinprodSplit : Prop := ∀ (α : Type) (S : Set α) (Z T : Finset α) (F : α → ℂ), (∀ w ∈ Z, w ∈ S) → (∀ w ∈ T, w ∈ S) → Disjoint T Z →
  (∀ w ∈ S, w ∉ Z → w ∉ T → F w = 1) → ∏ᶠ w ∈ S, F w = (∏ w ∈ Z, F w) * ∏ w ∈ T, F w

def DcosSep : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (ϖ : (w.adicCompletion E)ˣ), ordL (ϖ : w.adicCompletion E) = 1 → ∀ x : Fin n → ℤ, StrictAnti x →
  Lc (KGL w (n := n)) (dcos n w (tdiag ϖ x)) ∧ ∀ y, dcos n w (tdiag ϖ x) y ≠ 0 → y.val.charpoly.Separable

def DcosTr : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (ϖ : (w.adicCompletion E)ˣ), ordL (ϖ : w.adicCompletion E) = 1 → ∀ (τ : SmIrr (GLw n w)),
  fixed τ.ρ (KGL w (n := n)) ≠ ⊥ → ∃ x : Fin n → ℤ, StrictAnti x ∧ trc τ.ρ (KGL w (n := n)) (dcos n w (tdiag ϖ x)) ≠ 0

def TrLevel : Prop := ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G), IsOpen (K : Set G) → IsCompact (K : Set G) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (f : G → ℂ) (K₁ K₂ : Subgroup G),
  IsOpen (K₂ : Set G) → K₂ ≤ K₁ → K₁ ≤ K → IsHecke K₁ f → FiniteDimensional ℂ (fixed ρ K₂) →
  twTr ρ K K₂ f LinearMap.id = twTr ρ K K₁ f LinearMap.id

def admitted : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (τ : SmIrr (GLw n w)) (U : Subgroup (GLw n w)), IsOpen (U : Set (GLw n w)) →
  FiniteDimensional ℂ (fixed τ.ρ U)

def RCtEx : Prop := ExAct → CtLin → CtUnit → CtT → CtMul → SatSum → MuTw → HintSph → CtEx

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.HintTranslate
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.BCT Formalism.UG
open PositivityTheory.Rg.BcB.G8 (K2)
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

section Generic

variable {G : Type} [Group G]

private theorem hint_of_rinv (K : Subgroup G) (u : G → ℂ) (hu : ∀ k ∈ K, ∀ x, u (x * k) = u x) :
    hint K u = ∑ᶠ q : G ⧸ K, u q.out := by
  have h : rStab u ⊓ K = K := inf_eq_right.2 fun k hk => hu k hk
  unfold hint
  rw [h, Subgroup.relIndex_self]
  simp

private theorem out_mk_eq (K : Subgroup G) (u : G → ℂ) (hu : ∀ k ∈ K, ∀ x, u (x * k) = u x) (x : G) :
    u ((x : G ⧸ K).out) = u x := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K x
  rw [hh]
  exact hu h h.2 x

private theorem hint_translate (K : Subgroup G) (u : G → ℂ) (hu : ∀ k ∈ K, ∀ x, u (x * k) = u x) (k : G) :
    hint K (fun z => u (k * z)) = hint K u := by
  rw [hint_of_rinv K u hu, hint_of_rinv K _ fun c hc x => by
    show u (k * (x * c)) = u (k * x)
    rw [← mul_assoc]
    exact hu c hc _]
  calc ∑ᶠ q : G ⧸ K, u (k * q.out)
      = ∑ᶠ q : G ⧸ K, (fun q' : G ⧸ K => u q'.out) ((MulAction.toPerm k : Equiv.Perm (G ⧸ K)) q) := by
        refine finsum_congr fun q => ?_
        have hq : (MulAction.toPerm k : Equiv.Perm (G ⧸ K)) q = ((k * q.out : G) : G ⧸ K) := by
          conv_lhs => rw [← QuotientGroup.out_eq' q]
          rfl
        show _ = u (((MulAction.toPerm k : Equiv.Perm (G ⧸ K)) q).out)
        rw [hq, out_mk_eq K u hu]
    _ = ∑ᶠ q : G ⧸ K, u q.out := finsum_comp_equiv (f := fun q' : G ⧸ K => u q'.out) (MulAction.toPerm k : Equiv.Perm (G ⧸ K))

variable [TopologicalSpace G] [IsTopologicalGroup G]

private theorem isHecke_conv (K : Subgroup G) {A B : G → ℂ} (hA : IsHecke K A) (hB : IsHecke K B) :
    IsHecke K fun y => hint K fun z => A z * B (z⁻¹ * y) := by
  refine ⟨?_, fun k hk x => ⟨?_, ?_⟩⟩
  · refine HasCompactSupport.of_support_subset_isCompact (hA.1.isCompact.mul hB.1.isCompact) fun y hy => ?_
    have hy' : hint K (fun z => A z * B (z⁻¹ * y)) ≠ 0 := hy
    obtain ⟨z, hz⟩ : ∃ z, A z * B (z⁻¹ * y) ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hy' (by simp [hint, hc])
    exact Set.mem_mul.2 ⟨z, subset_tsupport _ (left_ne_zero_of_mul hz), z⁻¹ * y,
      subset_tsupport _ (right_ne_zero_of_mul hz), by group⟩
  · have hu : ∀ c ∈ K, ∀ z, (fun z => A z * B (z⁻¹ * x)) (z * c) = (fun z => A z * B (z⁻¹ * x)) z := by
      intro c hc z
      show A (z * c) * B ((z * c)⁻¹ * x) = A z * B (z⁻¹ * x)
      rw [(hA.2 c hc z).2, _root_.mul_inv_rev, mul_assoc, (hB.2 c⁻¹ (K.inv_mem hc) _).1]
    show hint K (fun z => A z * B (z⁻¹ * (k * x))) = hint K (fun z => A z * B (z⁻¹ * x))
    rw [← hint_translate K (fun z => A z * B (z⁻¹ * x)) hu k⁻¹]
    congr 1
    funext z
    show A z * B (z⁻¹ * (k * x)) = A (k⁻¹ * z) * B ((k⁻¹ * z)⁻¹ * x)
    rw [(hA.2 k⁻¹ (K.inv_mem hk) z).1]
    congr 2
    group
  · have h : (fun z => A z * B (z⁻¹ * (x * k))) = fun z => A z * B (z⁻¹ * x) := by
      funext z
      rw [← mul_assoc, (hB.2 k hk _).2]
    show hint K (fun z => A z * B (z⁻¹ * (x * k))) = hint K (fun z => A z * B (z⁻¹ * x))
    rw [h]

private theorem isHecke_ind (K : Subgroup G) (hK : IsCompact (K : Set G)) (S : Set G)
    (hl : ∀ k ∈ K, ∀ x ∈ S, k * x ∈ S) (hr : ∀ k ∈ K, ∀ x ∈ S, x * k ∈ S)
    (ht : ∀ x ∈ S, ∀ y ∈ S, ∃ a ∈ K, ∃ b ∈ K, y = a * x * b) :
    IsHecke K (S.indicator (1 : G → ℂ)) := by
  refine ⟨?_, fun k hk x => ⟨?_, ?_⟩⟩
  · rcases S.eq_empty_or_nonempty with rfl | ⟨d, hd⟩
    · exact HasCompactSupport.of_support_subset_isCompact isCompact_empty (by simp)
    · refine HasCompactSupport.of_support_subset_isCompact
        (IsCompact.mul (IsCompact.mul hK (isCompact_singleton (x := d))) hK) fun y hy => ?_
      have hyS : y ∈ S := by
        by_contra h
        exact hy (Set.indicator_of_notMem h _)
      obtain ⟨a, ha, b, hb, rfl⟩ := ht d hd y hyS
      exact Set.mul_mem_mul (Set.mul_mem_mul ha rfl) hb
  · have : k * x ∈ S ↔ x ∈ S := ⟨fun h => by simpa using hl k⁻¹ (K.inv_mem hk) _ h, hl k hk x⟩
    by_cases hx : x ∈ S
    · simp [hx, this]
    · simp [hx, this]
  · have : x * k ∈ S ↔ x ∈ S := ⟨fun h => by simpa using hr k⁻¹ (K.inv_mem hk) _ h, hr k hk x⟩
    by_cases hx : x ∈ S
    · simp [hx, this]
    · simp [hx, this]

private theorem isHecke_fn {ι : Type} (K : Subgroup G) (hK : IsCompact (K : Set G)) (g : ι → G → ℂ)
    (hg : ∀ i, IsHecke K (g i)) (e : Ex ι) : IsHecke K (e.fn K g) := by
  induction e with
  | one =>
    exact isHecke_ind K hK _ (fun k hk x hx => K.mul_mem hk hx) (fun k hk x hx => K.mul_mem hx hk)
      fun x hx y hy => ⟨y * x⁻¹, K.mul_mem hy (K.inv_mem hx), 1, K.one_mem, by group⟩
  | gen i => exact hg i
  | smul c a ih =>
    refine ⟨HasCompactSupport.of_support_subset_isCompact ih.1.isCompact fun y hy => ?_, fun k hk x => ?_⟩
    · exact subset_tsupport _ (right_ne_zero_of_mul hy)
    · show c * a.fn K g (k * x) = c * a.fn K g x ∧ c * a.fn K g (x * k) = c * a.fn K g x
      rw [(ih.2 k hk x).1, (ih.2 k hk x).2]
      exact ⟨rfl, rfl⟩
  | add a b iha ihb =>
    refine ⟨iha.1.add ihb.1, fun k hk x => ?_⟩
    show a.fn K g (k * x) + b.fn K g (k * x) = a.fn K g x + b.fn K g x ∧
      a.fn K g (x * k) + b.fn K g (x * k) = a.fn K g x + b.fn K g x
    rw [(iha.2 k hk x).1, (iha.2 k hk x).2, (ihb.2 k hk x).1, (ihb.2 k hk x).2]
    exact ⟨rfl, rfl⟩
  | mul a b iha ihb => exact isHecke_conv K iha ihb

end Generic

private theorem isHecke_pair {G H : Type} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H] (K₁ : Subgroup G) (K₂ : Subgroup H) {f : G → ℂ} {g : H → ℂ}
    (hf : IsHecke K₁ f) (hg : IsHecke K₂ g) : IsHecke (K₁.prod K₂) fun y : G × H => f y.1 * g y.2 := by
  refine ⟨HasCompactSupport.of_support_subset_isCompact (hf.1.isCompact.prod hg.1.isCompact) fun y hy =>
    ⟨subset_tsupport _ (left_ne_zero_of_mul hy), subset_tsupport _ (right_ne_zero_of_mul hy)⟩, fun k hk x => ?_⟩
  obtain ⟨h1, h2⟩ := Subgroup.mem_prod.1 hk
  show f (k.1 * x.1) * g (k.2 * x.2) = _ ∧ f (x.1 * k.1) * g (x.2 * k.2) = _
  rw [(hf.2 _ h1 _).1, (hf.2 _ h1 _).2, (hg.2 _ h2 _).1, (hg.2 _ h2 _).2]
  exact ⟨rfl, rfl⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private theorem isHecke_Tj (n : ℕ) (w : Pl E) (ϖ : w.adicCompletion E) (j : ℕ) :
    IsHecke (GlobalTheory.LFun.KGL w (n := n)) (Tj ℂ n (Ov E w) ϖ j) := by
  have hKe : GlobalTheory.LFun.KGL w (n := n) = GLint (Fin n) (Ov E w) := rfl
  have hc := (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w n).2
  unfold Tj
  refine isHecke_ind _ hc _ ?_ ?_ ?_
  · rintro k hk x ⟨a, ha, b, hb, hx⟩
    refine ⟨k * a, (GLint (Fin n) (Ov E w)).mul_mem (hKe ▸ hk) ha, b, hb, ?_⟩
    rw [Units.val_mul, Units.val_mul, hx]
    simp only [mul_assoc]
  · rintro k hk x ⟨a, ha, b, hb, hx⟩
    refine ⟨a, ha, b * k, (GLint (Fin n) (Ov E w)).mul_mem hb (hKe ▸ hk), ?_⟩
    rw [Units.val_mul, Units.val_mul, hx]
    simp only [mul_assoc]
  · rintro x ⟨a, ha, b, hb, hx⟩ y ⟨c, hc', d, hd, hy⟩
    refine ⟨c * a⁻¹, hKe ▸ (GLint (Fin n) (Ov E w)).mul_mem hc' ((GLint (Fin n) (Ov E w)).inv_mem ha),
      b⁻¹ * d, hKe ▸ (GLint (Fin n) (Ov E w)).mul_mem ((GLint (Fin n) (Ov E w)).inv_mem hb) hd, ?_⟩
    apply Units.ext
    have h1 : (a⁻¹).val * a.val = 1 := Units.inv_mul a
    have h2 : b.val * (b⁻¹).val = 1 := Units.mul_inv b
    simp only [Units.val_mul]
    rw [hx, hy]
    calc c.val * diagJ n ϖ j * d.val
        = c.val * 1 * diagJ n ϖ j * 1 * d.val := by simp
      _ = c.val * ((a⁻¹).val * a.val) * diagJ n ϖ j * (b.val * (b⁻¹).val) * d.val := by rw [h1, h2]
      _ = _ := by simp only [mul_assoc]

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

open UpperTheory.V.Z.Tf.GlobalTraceComparison in
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.exHecke2 :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.ExHecke2 := by
  intro E _ _ _ a b w e
  exact UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.isHecke_fn (K2 a b w)
    ((GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).2.prod (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).2) _
    (fun p => UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.isHecke_pair _ _ (UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.isHecke_Tj a w _ _)
      (UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.isHecke_Tj b w _ _)) e
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.Places
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitAtIffCPlNeAndCPlCPl
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.EulerTw

theorem isSplitAt_iff_cPl_ne_and_cPl_cPl :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E),
      (IsSplitAt w ↔ GlobalTheory.EulerTw.cPl E w ≠ w) ∧ GlobalTheory.EulerTw.cPl E (GlobalTheory.EulerTw.cPl E w) = w := by
  intro E _ _ _ w
  refine ⟨⟨fun h => (GlobalTheory.SplitPts.over_split h).1, fun h => ?_⟩, GlobalTheory.SplitPts.conjSrc_conjSrc_cm w⟩
  by_contra hs
  exact h (GlobalTheory.LocInj.conjSrc_eq_of_not_split hs)

end GlobalTheory.EulerTw
end

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private theorem eq_or_eq_cPl (w u : Pl E)
    (h : u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))) : u = w ∨ u = cPl w := by
  by_cases hs : IsSplitAt w
  · exact (GlobalTheory.SplitPts.over_split hs).2.2 u h
  · by_contra hc
    exact hs ⟨u, fun e => hc (Or.inl e), h⟩

private theorem exists_section : ∃ S : Set (Pl E), IsSection S := by
  let s : Setoid (Pl E) := Setoid.ker fun w : Pl E => w.under (𝓞 (maximalRealSubfield E))
  refine ⟨Set.range fun q : Quotient s => q.out, fun w => ⟨(Quotient.mk s w).out, ⟨⟨_, rfl⟩, ?_⟩, ?_⟩⟩
  · exact Quotient.mk_out (s := s) w
  · rintro u ⟨⟨q, rfl⟩, h⟩
    have hq : q = Quotient.mk s w := by
      conv_lhs => rw [← Quotient.out_eq q]
      exact Quotient.sound h
    rw [hq]

private theorem infinite_split : {w : Pl E | IsSplitAt w}.Infinite := by
  intro hfin
  obtain ⟨m, hm⟩ := (hfin.image fun w : Pl E => Ideal.absNorm w.asIdeal).bddAbove
  obtain ⟨p, hp, hmp, hs⟩ := GlobalTheory.LargeSplitPrime.exists_splitsCompl E m
  haveI hPmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  have hinj : Function.Injective (algebraMap ℤ (𝓞 E)) := (algebraMap ℤ (𝓞 E)).injective_int
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 E)
    (Ideal.span {(p : ℤ)}) (by rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]; exact bot_le)
  have hpQ : (p : 𝓞 E) ∈ Q := by
    have : (p : ℤ) ∈ Ideal.under ℤ Q := by
      rw [hQ]
      exact Ideal.subset_span rfl
    simpa using this
  have hp0 : (p : 𝓞 E) ≠ 0 := by exact_mod_cast hp.ne_zero
  let w : Pl E := ⟨Q, hQmax.isPrime, fun h => hp0 (by rw [h] at hpQ; simpa using hpQ)⟩
  have hv : (p : 𝓞 (maximalRealSubfield E)) ∈ (w.under (𝓞 (maximalRealSubfield E))).asIdeal := by
    show algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) (p : 𝓞 (maximalRealSubfield E)) ∈ w.asIdeal
    rw [map_natCast]
    exact hpQ
  have h2 : Module.finrank (maximalRealSubfield E) E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have hsplit : IsSplitAt w := by
    obtain ⟨a, b, hab, ha, hb⟩ :=
      GlobalTheory.SplitPlace.isSplit_of_norm h2 hp (fun u hu => hs u.asIdeal u.isMaximal hu) _ hv
    by_cases h : a = w
    · exact ⟨b, fun e => hab (h.trans e.symm), HeightOneSpectrum.ext hb⟩
    · exact ⟨a, h, HeightOneSpectrum.ext ha⟩
  have hN : Ideal.absNorm w.asIdeal = p := (hs w.asIdeal w.isMaximal hpQ).1
  have hle : Ideal.absNorm w.asIdeal ≤ m := hm ⟨w, hsplit, rfl⟩
  omega

theorem places : Places := by
  intro E _ _ _
  refine ⟨exists_section, fun w => ?_, infinite_split, fun S hS w => ⟨?_, fun h₁ h₂ => ?_⟩⟩
  · obtain ⟨h₁, h₂⟩ := GlobalTheory.EulerTw.isSplitAt_iff_cPl_ne_and_cPl_cPl E w
    exact ⟨h₂, h₁⟩
  · obtain ⟨u, ⟨hu, hw⟩, -⟩ := hS w
    rcases eq_or_eq_cPl w u hw with rfl | rfl
    · exact Or.inl hu
    · exact Or.inr hu
  · exact (hS w).unique ⟨h₂, GlobalTheory.LocInj.under_conjSrc w⟩ ⟨h₁, rfl⟩

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.SmallTendsto
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

theorem small_tendsto {x : ℕ → ℂ} (h : Small (1 / 2) x) : Tendsto x atTop (𝓝 0) := by
  obtain ⟨C, N, h⟩ := h
  refine squeeze_zero_norm h ?_
  have h1 := (tendsto_pow_const_mul_const_pow_of_abs_lt_one N (r := (1 / 2 : ℝ)) (by norm_num [abs_of_pos])).comp
    (tendsto_add_atTop_nat 1)
  have h2 := h1.const_mul (C * 2)
  rw [mul_zero] at h2
  refine h2.congr fun k => ?_
  simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one, pow_succ]
  rw [add_comm (k : ℝ) 1]
  ring

theorem sat_card {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {D : CD E n} {w : Pl E} {B : Multiset ℂˣ}
    (h : D.Sat w B) : B.card = n := by
  obtain ⟨b, hb, rfl⟩ := h
  refine Eq.trans ?_ D.sum
  rw [Multiset.card_sum]
  exact Finset.sum_congr rfl fun i _ => (hb i).card

theorem off_cofinite {E : Type} [Field E] [NumberField E] [IsCMField E] (hP : Places) (Z : Finset (Pl E)) :
    ∀ᶠ w : Pl E in cofinite, Off Z w := by
  have h1 : ∀ᶠ w : Pl E in cofinite, w ∉ Z := Z.eventually_cofinite_notMem
  have h2 : ∀ᶠ w : Pl E in cofinite, w ∉ Z.image cPl := (Z.image cPl).eventually_cofinite_notMem
  filter_upwards [h1, h2] with w a b
  exact ⟨a, fun h => b (Finset.mem_image.2 ⟨_, h, ((hP E).2.1 w).1⟩)⟩

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.InertLine
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.inertLine :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.InertLine := by
  intro E _ _ _ hU n w _ σ hne hfd
  exact GlobalTheory.CompanionTheory.SphLine.sphOne E hU n w σ hne hfd
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.RegCt
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.regCt :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.RegCt := by
  intro E _ _ _ w hw μ n a b h f hf
  exact GlobalTheory.BCT.CtReg.ctMu_regAt2 E a b n h w (μ.loc w) (fun x => f w x.1) hw (fun y => hf y.1)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.SplitLine
open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep
open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun GlobalTheory.LGrp GlobalTheory.LFun.SatCompare

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

section

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

private theorem eq_bot_or_top {ρ : Representation ℂ G V} (hi : ρ.IsIrreducible) (S : Submodule ℂ V)
    (hS : ∀ g, ∀ x ∈ S, ρ g x ∈ S) : S = ⊥ ∨ S = ⊤ := by
  let P : Subrepresentation ρ := ⟨S, fun g x hx => hS g x hx⟩
  exact (hi.eq_bot_or_eq_top P).imp (fun e => congrArg Subrepresentation.toSubmodule e)
    fun e => congrArg Subrepresentation.toSubmodule e

variable [TopologicalSpace G] [IsTopologicalGroup G]

private theorem rank_le [SecondCountableTopology G] {ρ : Representation ℂ G V} (hs : IsSmooth ρ)
    (hi : ρ.IsIrreducible) {v : V} (hv : v ≠ 0) : Module.rank ℂ V ≤ Cardinal.aleph0 := by
  rw [← rank_top]
  refine GlobalTheory.CompanionTheory.SatAe.rank_le_of_simple (⊤ : Submodule ℂ V) (fun g : G => ρ g)
    ((Submodule.ne_bot_iff _).2 ⟨v, trivial, hv⟩) (fun W _ hW => eq_bot_or_top hi W hW) fun x _ => ?_
  exact ⟨_, GlobalTheory.CompanionTheory.SatAe.countable_orbit ρ x (hs x), fun _ _ => trivial, fun g => Submodule.subset_span ⟨g, rfl⟩⟩

private theorem fixed_eq_span [SecondCountableTopology G] {ρ : Representation ℂ G V} {K : Subgroup G}
    (hs : IsSmooth ρ) (hi : ρ.IsIrreducible) (hc : IsCompact (K : Set G)) (hK : IsCommensurated K)
    (hcomm : ∀ f₁ ∈ Hecke ℂ K, ∀ f₂ ∈ Hecke ℂ K, conv K f₁ f₂ = conv K f₂ f₁)
    {v : V} (hv : v ∈ fixed ρ K) (hv0 : v ≠ 0) : fixed ρ K = Submodule.span ℂ {v} := by
  have hr := rank_le hs hi hv0
  have hb : GlobalTheory.CompanionTheory.SatAe.IsBiSimple ρ := fun S h1 _ => eq_bot_or_top hi S h1
  have hle : Submodule.span ℂ {v} ≤ fixed ρ K := (Submodule.span_singleton_le_iff_mem _ _).2 hv
  have hH : ∀ f ∈ Hecke ℂ K, ∀ x ∈ Submodule.span ℂ {v}, heckeVec ρ K f x ∈ Submodule.span ℂ {v} := by
    intro f hf x hx
    obtain ⟨c, hc'⟩ := GlobalTheory.CompanionTheory.SatAe.exists_scalar hs hc hK hcomm hb hr f hf
    rw [hc' x (hle hx)]
    exact Submodule.smul_mem _ _ hx
  have hB : ∀ b : Module.End ℂ V, (∀ g, b * ρ g = ρ g * b) → ∀ x ∈ Submodule.span ℂ {v},
      b x ∈ Submodule.span ℂ {v} := by
    intro b hbc x hx
    obtain ⟨c, hc'⟩ := GlobalTheory.CompanionTheory.SatAe.scalar_of_simple hr (Set.range fun g => ρ g)
      (fun W hW => eq_bot_or_top hi W fun g => hW _ ⟨g, rfl⟩) b (by
        rintro _ ⟨g, rfl⟩
        exact (hbc g).symm)
    rw [hc' x]
    exact Submodule.smul_mem _ _ hx
  refine ((GlobalTheory.CompanionTheory.SatAe.fixed_simple hs hc hK hb _ hle hH hB).resolve_left fun h => hv0 ?_).symm
  have : v ∈ Submodule.span ℂ {v} := Submodule.mem_span_singleton_self v
  rw [h] at this
  exact (Submodule.mem_bot ℂ).1 this

end

theorem splitLine : SplitLine := by
  intro E _ _ _ n w τ hne
  rcases τ with @⟨V, _, _, ρ, hs, hi⟩
  change fixed ρ (KGL w (n := n)) ≠ ⊥ at hne
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hne
  have hc := (isOpen_isCompact_KGL w n).2
  have hK := Final.GLintComm E w n
  have hcomm := Final.HeckeCommGL E w n ℂ
  have hline := fixed_eq_span hs hi hc hK hcomm hv hv0
  refine ⟨?_, GlobalTheory.CompanionTheory.SatAe.exists_hasSatGL_of_scalar (fun h hh => ?_) hne⟩
  · change Module.finrank ℂ (fixed ρ (KGL w (n := n))) = 1
    rw [hline]
    exact finrank_span_singleton hv0
  · exact GlobalTheory.CompanionTheory.SatAe.exists_scalar hs hc hK hcomm (fun S h1 _ => eq_bot_or_top hi S h1)
      (rank_le hs hi hv0) h hh

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.ConstantTermParabolicAverage
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private def lprod {ι : Type} : List (Ex ι) → Ex ι
  | [] => Ex.one
  | a :: l => Ex.mul a (lprod l)

private theorem ev_lprod {ι : Type} (x : ι → ℂ) (l : List (Ex ι)) :
    (lprod l).ev x = (l.map (Ex.ev x)).prod := by
  induction l with
  | nil => simp [lprod, Ex.ev]
  | cons a l ih => simp [lprod, Ex.ev, ih]

private theorem exists_aff {ι : Type} (x y : ι → ℂ) (i : ι) (h : x i ≠ y i) :
    ∃ e : Ex ι, e.ev x = 1 ∧ e.ev y = 0 := by
  have hd : x i - y i ≠ 0 := sub_ne_zero.2 h
  refine ⟨Ex.smul (x i - y i)⁻¹ (Ex.add (Ex.gen i) (Ex.smul (-y i) Ex.one)), ?_, ?_⟩
  · simp only [Ex.ev]
    have : x i + -y i * 1 = x i - y i := by ring
    rw [this]
    exact inv_mul_cancel₀ hd
  · simp [Ex.ev]

private theorem sep_one (n : ℕ) (w : Pl E) {A A' : Multiset ℂˣ} (h : A.card = n) (h' : A'.card = n)
    (hne : A' ≠ A) : ∃ e : Ex (Fin (n + 1)), ev1 n w e A = 1 ∧ ev1 n w e A' = 0 := by
  have hex : ∃ j, j ≤ n ∧ satEig (qV E w) n A j ≠ satEig (qV E w) n A' j := by
    by_contra hc
    push_neg at hc
    exact hne (eq_of_satEig_eq (qV_ne_zero w) h h' hc).symm
  obtain ⟨j, hj, hj'⟩ := hex
  exact exists_aff (fun j : Fin (n + 1) => satEig (qV E w) n A j)
    (fun j : Fin (n + 1) => satEig (qV E w) n A' j) ⟨j, Nat.lt_succ_of_le hj⟩ hj'

private theorem sep_at (hP : Places) (n : ℕ) (S : Set (Pl E)) (hS : IsSection S) (Z : Finset (Pl E))
    (B C : Pl E → Multiset ℂˣ)
    (h : ∃ w, Off Z w ∧ IsSplitAt w ∧ (B w).card = n ∧ (C w).card = n ∧ C w ≠ B w) :
    ∃ (t : Pl E) (e₁ e₂ : Ex (Fin (n + 1))), t ∈ S ∧ IsSplitAt t ∧ t ∉ Z ∧ ev1 n t e₁ (B t) = 1 ∧
      ev1 n t e₂ (inv (B (cPl t))) = 1 ∧ ev1 n t e₁ (C t) * ev1 n t e₂ (inv (C (cPl t))) = 0 := by
  obtain ⟨-, hc, -, hs⟩ := hP E
  obtain ⟨w, ⟨hwZ, hcZ⟩, hsp, hB, hC, hne⟩ := h
  rcases (hs S hS w).1 with hw | hw
  · obtain ⟨e, h1, h0⟩ := sep_one n w hB hC hne
    refine ⟨w, e, Ex.one, hw, hsp, hwZ, h1, ?_, ?_⟩
    · simp [ev1, Ex.ev]
    · rw [h0, zero_mul]
  · have hcc : cPl (cPl w) = w := (hc w).1
    have hsp' : IsSplitAt (cPl w) :=
      (hc (cPl w)).2.2 (by rw [hcc]; exact fun h => (hc w).2.1 hsp |>.elim h.symm)
    obtain ⟨e, h1, h0⟩ := sep_one n (cPl w) (A := inv (B w)) (A' := inv (C w))
      (by simpa [inv] using hB) (by simpa [inv] using hC)
      (fun h => hne (Multiset.map_injective inv_injective h))
    refine ⟨cPl w, Ex.one, e, hw, hsp', hcZ, by simp [ev1, Ex.ev], by rw [hcc]; exact h1, ?_⟩
    rw [hcc, h0, mul_zero]

private def comb {I : Type} [Fintype I] {n : ℕ} (t : I → Pl E) (e : I → Ex (Fin (n + 1))) (w : Pl E) :
    Ex (Fin (n + 1)) :=
  lprod ((Finset.univ : Finset I).toList.map fun j => if t j = w then e j else Ex.one)

private theorem evaluation_combined_test_function {I : Type} [Fintype I] {n : ℕ} (t : I → Pl E) (e : I → Ex (Fin (n + 1)))
    (w : Pl E) (X : Multiset ℂˣ) :
    ev1 n w (comb t e w) X = ∏ j, if t j = w then ev1 n w (e j) X else 1 := by
  rw [← Finset.prod_map_toList]
  simp only [ev1, comb]
  rw [ev_lprod, List.map_map]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  by_cases hj : t j = w <;> simp [hj, Ex.ev]

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.rSep :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.RSep := by
  intro hP E _ _ _ n S hS Z I _ B C h
  haveI := Fintype.ofFinite I
  choose t e₁ e₂ htS hts htZ hB₁ hB₂ hC using fun j => sep_at hP n S hS Z B (C j) (h j)
  refine ⟨Finset.univ.image t, comb t e₁, comb t e₂, ?_, ?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hw
    exact ⟨htS j, hts j⟩
  · refine Finset.disjoint_left.2 fun w hw hz => ?_
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hw
    exact htZ j hz
  · refine Finset.prod_eq_one fun w _ => ?_
    rw [evaluation_combined_test_function, evaluation_combined_test_function]
    rw [show ∀ a b : ℂ, a = 1 → b = 1 → a * b = 1 from fun a b ha hb => by rw [ha, hb, one_mul]]
    · refine Finset.prod_eq_one fun j _ => ?_
      split_ifs with hj
      · subst hj
        exact hB₁ j
      · rfl
    · refine Finset.prod_eq_one fun j _ => ?_
      split_ifs with hj
      · subst hj
        exact hB₂ j
      · rfl
  · intro j
    refine Finset.prod_eq_zero (Finset.mem_image_of_mem t (Finset.mem_univ j)) ?_
    rw [evaluation_combined_test_function, evaluation_combined_test_function]
    rcases mul_eq_zero.1 (hC j) with h0 | h0
    · exact mul_eq_zero.2 (Or.inl (Finset.prod_eq_zero (Finset.mem_univ j) (by rw [if_pos rfl]; exact h0)))
    · exact mul_eq_zero.2 (Or.inr (Finset.prod_eq_zero (Finset.mem_univ j) (by rw [if_pos rfl]; exact h0)))
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.LevelFn
noncomputable section

open GlobalTheory.BCT GlobalTheory.PRep Matrix
open UpperTheory.V.Z.Tf.GlobalTraceComparison

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

section Generic

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

private theorem rStab_ind (K' : Subgroup G) :
    rStab ((K' : Set G).indicator (1 : G → ℂ)) = K' := by
  classical
  ext k
  constructor
  · intro hk
    have h := hk 1
    simp only [one_mul] at h
    by_contra hn
    rw [Set.indicator_of_notMem (by simpa using hn), Set.indicator_of_mem (by simp [K'.one_mem])] at h
    simp at h
  · intro hk x
    by_cases hx : x ∈ K'
    · rw [Set.indicator_of_mem (show x * k ∈ (K' : Set G) from K'.mul_mem hx hk),
        Set.indicator_of_mem (show x ∈ (K' : Set G) from hx)]
      rfl
    · have hxk : x * k ∉ K' := fun h => hx (by simpa using K'.mul_mem h (K'.inv_mem hk))
      rw [Set.indicator_of_notMem (show x * k ∉ (K' : Set G) from hxk),
        Set.indicator_of_notMem (show x ∉ (K' : Set G) from hx)]

private theorem ind_inv (K' : Subgroup G) :
    (fun y : G => (K' : Set G).indicator (1 : G → ℂ) y⁻¹) = (K' : Set G).indicator (1 : G → ℂ) := by
  classical
  funext y
  by_cases hy : y ∈ K'
  · rw [Set.indicator_of_mem (show y⁻¹ ∈ (K' : Set G) from K'.inv_mem hy),
      Set.indicator_of_mem (show y ∈ (K' : Set G) from hy)]
    rfl
  · have : y⁻¹ ∉ K' := fun h => hy (by simpa using K'.inv_mem h)
    rw [Set.indicator_of_notMem (show y⁻¹ ∉ (K' : Set G) from this),
      Set.indicator_of_notMem (show y ∉ (K' : Set G) from hy)]

private theorem levOp_ind (ρ : Representation ℂ G V) (K K' : Subgroup G) (x : V) (hx : x ∈ fixed ρ K') :
    levOp ρ K K' ((K' : Set G).indicator (1 : G → ℂ)) LinearMap.id x = ((K'.relIndex K : ℕ) : ℂ)⁻¹ • x := by
  classical
  have hfx : ∀ h ∈ K', ρ h x = x := fun h hh => by simpa using hx ⟨h, hh⟩
  have hout : ∀ q : G ⧸ K', q.out ∈ K' ↔ q = (QuotientGroup.mk 1 : G ⧸ K') := by
    intro q
    constructor
    · intro h
      have h2 : ((q.out : G) : G ⧸ K') = QuotientGroup.mk 1 :=
        QuotientGroup.eq.2 (by simpa using K'.inv_mem h)
      rwa [QuotientGroup.out_eq'] at h2
    · rintro rfl
      have := QuotientGroup.mk_out_eq_mul K' (1 : G)
      obtain ⟨h, hh⟩ := this
      rw [hh]
      simpa using h.2
  unfold levOp
  rw [finsum_eq_single _ (QuotientGroup.mk 1 : G ⧸ K')]
  · rw [Set.indicator_of_mem (show (QuotientGroup.mk 1 : G ⧸ K').out ∈ (K' : Set G) from (hout _).2 rfl)]
    simp [hfx _ ((hout _).2 rfl)]
  · intro q hq
    rw [Set.indicator_of_notMem (show q.out ∉ (K' : Set G) from fun h => hq ((hout q).1 h))]
    simp

private theorem trc_ind_ne (ρ : Representation ℂ G V) (K K' : Subgroup G) (hle : K' ≤ K) (hi : K'.relIndex K ≠ 0)
    (hfd : FiniteDimensional ℂ (fixed ρ K')) (hne : fixed ρ K' ≠ ⊥) :
    trc ρ K ((K' : Set G).indicator (1 : G → ℂ)) ≠ 0 := by
  have hlev : K ⊓ rStab ((K' : Set G).indicator (1 : G → ℂ)) ⊓
      rStab (fun y : G => (K' : Set G).indicator (1 : G → ℂ) y⁻¹) = K' := by
    rw [ind_inv, rStab_ind, inf_assoc, inf_idem]
    exact inf_eq_right.2 hle
  unfold trc
  rw [hlev]
  have hc : ∀ v ∈ fixed ρ K', levOp ρ K K' ((K' : Set G).indicator (1 : G → ℂ)) LinearMap.id v ∈ fixed ρ K' := by
    intro v hv
    rw [levOp_ind ρ K K' v hv]
    exact Submodule.smul_mem _ _ hv
  have hr : (levOp ρ K K' ((K' : Set G).indicator (1 : G → ℂ)) LinearMap.id).restrict hc =
      ((K'.relIndex K : ℕ) : ℂ)⁻¹ • LinearMap.id := by
    ext v
    simp [LinearMap.restrict_apply, levOp_ind ρ K K' v v.2]
  unfold twTr
  rw [dite_eq_left hc, hr, map_smul, LinearMap.trace_id, smul_eq_mul]
  have hpos : Module.finrank ℂ (fixed ρ K') ≠ 0 := by
    intro h0
    exact hne (Submodule.finrank_eq_zero.1 h0)
  exact mul_ne_zero (inv_ne_zero (by exact_mod_cast hi)) (by exact_mod_cast hpos)

end Generic

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.levelFn :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.LevelFn := by
  intro E _ _ _ n w τ
  obtain ⟨ho, hc⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w n
  have hnt : Nontrivial τ.V := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    have hs : Subsingleton (Subrepresentation τ.ρ) :=
      ⟨fun a b => by
        apply Subrepresentation.toSubmodule_injective
        exact Subsingleton.elim _ _⟩
    haveI := τ.irred
    exact not_subsingleton (Subrepresentation τ.ρ) hs
  obtain ⟨v, hv⟩ := exists_ne (0 : τ.V)
  let U : Subgroup (GLw n w) :=
    { carrier := {g | τ.ρ g v = v}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
        rw [hb, ha]
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at *
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul]
        simp }
  have hU : IsOpen (U : Set (GLw n w)) := τ.smooth v
  let K' : Subgroup (GLw n w) := U ⊓ GlobalTheory.LFun.KGL w (n := n)
  have hKo : IsOpen (K' : Set (GLw n w)) := hU.inter ho
  have hKc : IsCompact (K' : Set (GLw n w)) := hc.inter_left (U.isClosed_of_isOpen hU)
  have hle : K' ≤ GlobalTheory.LFun.KGL w (n := n) := inf_le_right
  have hfd : FiniteDimensional ℂ (fixed τ.ρ K') := finiteDimensional_fixed_openSubgroup_GLw E n w τ K' hKo
  have hne : fixed τ.ρ K' ≠ ⊥ := by
    intro hb
    have hm : v ∈ fixed τ.ρ K' := fun h => by
      have h1 : τ.ρ h v = v := h.2.1
      simpa using h1
    rw [hb] at hm
    exact hv ((Submodule.mem_bot ℂ).1 hm)
  have hi : K'.relIndex (GlobalTheory.LFun.KGL w (n := n)) ≠ 0 := by
    haveI : CompactSpace (GlobalTheory.LFun.KGL w (n := n)) := isCompact_iff_compactSpace.1 hc
    haveI : Finite ((GlobalTheory.LFun.KGL w (n := n)) ⧸ K'.subgroupOf (GlobalTheory.LFun.KGL w (n := n))) :=
      Subgroup.quotient_finite_of_isOpen _ (hKo.preimage continuous_subtype_val)
    exact (Subgroup.finiteIndex_of_finite_quotient (H := K'.subgroupOf (GlobalTheory.LFun.KGL w (n := n)))).index_ne_zero
  refine ⟨(K' : Set (GLw n w)).indicator 1, ⟨K', hKo, hle, ?_, ?_⟩, UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.trc_ind_ne τ.ρ _ K' hle hi hfd hne⟩
  · exact HasCompactSupport.intro' hKc (K'.isClosed_of_isOpen hKo) fun x hx => Set.indicator_of_notMem hx _
  · classical
    intro k hk x
    have h1 : (k * x ∈ (K' : Set (GLw n w))) ↔ x ∈ (K' : Set (GLw n w)) := K'.mul_mem_cancel_left hk
    have h2 : (x * k ∈ (K' : Set (GLw n w))) ↔ x ∈ (K' : Set (GLw n w)) := K'.mul_mem_cancel_right hk
    show (K' : Set (GLw n w)).indicator 1 (k * x) = _ ∧ (K' : Set (GLw n w)).indicator 1 (x * k) = _
    rw [Set.indicator_apply, Set.indicator_apply, Set.indicator_apply]
    simp only [h1, h2, Pi.one_apply, and_self]
end
end
