module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Definitions.JetCones.SymCapRev
open scoped InnerProductSpace
open Finset

noncomputable section

namespace GlobalTheory.CompanionTheory.AlgRepEndIrreducible

def KRel {A : Type*} [Ring A] {n : ℕ} (ε : Fin n → Bool) (D : Fin n → Fin n → A) : Prop :=
  ∀ a b c d : Fin n, ε a = ε b → ε c = ε d → D a b * D c d - D c d * D a b =
    (if b = c then D a d else 0) - (if d = a then D c b else 0)

def KAdj {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (D : Fin n → Fin n → Module.End ℂ V) : Prop :=
  ∀ a b : Fin n, ε a = ε b → ∀ x y : V, ⟪D a b x, y⟫_ℂ = ⟪x, D b a y⟫_ℂ

def KMap {W X : Type*} [AddCommGroup W] [Module ℂ W] [AddCommGroup X] [Module ℂ X] {n : ℕ}
    (ε : Fin n → Bool) (D : Fin n → Fin n → Module.End ℂ W) (E : Fin n → Fin n → Module.End ℂ X)
    (ω : W →ₗ[ℂ] X) : Prop :=
  ∀ a b, ε a = ε b → ∀ w, ω (D a b w) = E a b (ω w)

end GlobalTheory.CompanionTheory.AlgRepEndIrreducible

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.JetProofs.EvFirst
open GlobalTheory.CompanionTheory.AlgRepEndIrreducible PI.UpqRep Matrix
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.AlgRepEndIrreducible.Vev

private noncomputable def ev {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
    (D : Fin n → Fin n → Module.End ℂ V) (v : V) (l : List (Fin n × Fin n)) : ℂ :=
  ⟪v, (l.map fun x => D x.1 x.2).prod v⟫_ℂ

private theorem ev_swap {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
    {ε : Fin n → Bool} {D : Fin n → Fin n → Module.End ℂ V} (h : KRel ε D) (v : V)
    (l₁ l₂ : List (Fin n × Fin n)) (x y : Fin n × Fin n) (hx : ε x.1 = ε x.2) (hy : ε y.1 = ε y.2) :
    ev D v (l₁ ++ x :: y :: l₂) = ev D v ((l₁ ++ [y]) ++ x :: l₂)
      + (if x.2 = y.1 then ev D v (l₁ ++ (x.1, y.2) :: l₂) else 0)
      - (if y.2 = x.1 then ev D v (l₁ ++ (y.1, x.2) :: l₂) else 0) := by
  have h1 := h x.1 x.2 y.1 y.2 hx hy
  have h2 : D x.1 x.2 * D y.1 y.2 = D y.1 y.2 * D x.1 x.2 + (if x.2 = y.1 then D x.1 y.2 else 0)
      - (if y.2 = x.1 then D y.1 x.2 else 0) := by
    rw [add_sub_assoc, ← h1]; abel
  simp only [ev, List.map_append, List.map_cons, List.prod_append, List.prod_cons, List.map_nil,
    List.prod_nil, mul_one]
  rw [← mul_assoc (D x.1 x.2), h2]
  split_ifs <;>
    simp [mul_add, add_mul, mul_sub, sub_mul, mul_assoc, inner_add_right, inner_sub_right]

private theorem ev_last {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
    {ε : Fin n → Bool} {D : Fin n → Fin n → Module.End ℂ V} {μ : Fin n → ℝ} {v : V}
    (h : Formalism.REAL.KHighest ε D μ v)
    (l₁ : List (Fin n × Fin n)) (x : Fin n × Fin n) (hx : ε x.1 = ε x.2) (hle : x.1 ≤ x.2) :
    ev D v (l₁ ++ [x]) = (if x.1 = x.2 then (μ x.1 : ℂ) else 0) * ev D v l₁ := by
  simp only [ev, List.map_append, List.map_cons, List.prod_append, List.prod_cons, List.map_nil,
    List.prod_nil, mul_one, Module.End.mul_apply]
  split_ifs with he
  · rw [← he, h.1 x.1, map_smul, inner_smul_right]
  · rw [h.2 x.1 x.2 (lt_of_le_of_ne hle he) hx]; simp

private theorem ev_first {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
    {ε : Fin n → Bool} {D : Fin n → Fin n → Module.End ℂ V} {μ : Fin n → ℝ} {v : V}
    (ha : KAdj ε D) (h : Formalism.REAL.KHighest ε D μ v)
    (l : List (Fin n × Fin n)) (x : Fin n × Fin n) (hx : ε x.1 = ε x.2) (hlt : x.2 < x.1) :
    ev D v (x :: l) = 0 := by
  simp only [ev, List.map_cons, List.prod_cons, Module.End.mul_apply]
  rw [← ha x.2 x.1 hx.symm, h.2 x.2 x.1 hlt hx.symm, inner_zero_left]

theorem vev_eq : ∀ (n : ℕ) (ε : Fin n → Bool) (V V' : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] (D : Fin n → Fin n → Module.End ℂ V) (D' : Fin n → Fin n → Module.End ℂ V') (μ : Fin n → ℝ) (v : V) (v' : V'), KRel ε D → KRel ε D' → KAdj ε D → KAdj ε D' → Formalism.REAL.KHighest ε D μ v → Formalism.REAL.KHighest ε D' μ v' → ∀ l : List (Fin n × Fin n), (∀ x ∈ l, ε x.1 = ε x.2) → ⟪v, (l.map fun x => D x.1 x.2).prod v⟫_ℂ * ⟪v', v'⟫_ℂ = ⟪v', (l.map fun x => D' x.1 x.2).prod v'⟫_ℂ * ⟪v, v⟫_ℂ := by
  intro n ε V V' _ _ _ _ D D' μ v v' hR hR' hA hA' hH hH'
  suffices H : ∀ (N : ℕ) (l : List (Fin n × Fin n)), l.length = N → (∀ x ∈ l, ε x.1 = ε x.2) →
      ev D v l * ⟪v', v'⟫_ℂ = ev D' v' l * ⟪v, v⟫_ℂ from fun l hl => H _ l rfl hl
  intro N
  induction N with
  | zero =>
    intro l hl _
    obtain rfl := List.length_eq_zero_iff.mp hl
    simp only [ev, List.map_nil, List.prod_nil, Module.End.one_apply]
    ring
  | succ N ih =>
    have key : ∀ (x : Fin n × Fin n), ε x.1 = ε x.2 → x.1 ≤ x.2 → ∀ (l₂ l₁ : List (Fin n × Fin n)),
        l₁.length + l₂.length = N → (∀ z ∈ l₁, ε z.1 = ε z.2) → (∀ z ∈ l₂, ε z.1 = ε z.2) →
        ev D v (l₁ ++ x :: l₂) * ⟪v', v'⟫_ℂ = ev D' v' (l₁ ++ x :: l₂) * ⟪v, v⟫_ℂ := by
      intro x hx hle l₂
      induction l₂ with
      | nil =>
        intro l₁ hl h₁ _
        rw [ev_last hH l₁ x hx hle, ev_last hH' l₁ x hx hle, mul_assoc, mul_assoc,
          ih l₁ (by simpa using hl) h₁]
      | cons y l₂ ih₂ =>
        intro l₁ hl h₁ h₂
        have hy : ε y.1 = ε y.2 := h₂ y (by simp)
        have h₂' : ∀ z ∈ l₂, ε z.1 = ε z.2 := fun z hz => h₂ z (by simp [hz])
        have hs : ∀ w : Fin n × Fin n, ε w.1 = ε w.2 →
            ev D v (l₁ ++ w :: l₂) * ⟪v', v'⟫_ℂ = ev D' v' (l₁ ++ w :: l₂) * ⟪v, v⟫_ℂ := by
          intro w hw
          refine ih _ (by simpa using hl) ?_
          intro z hz
          simp only [List.mem_append, List.mem_cons] at hz
          rcases hz with hz | rfl | hz
          exacts [h₁ z hz, hw, h₂' z hz]
        have hm := ih₂ (l₁ ++ [y]) (by simp at hl ⊢; omega) (by
          intro z hz
          simp only [List.mem_append, List.mem_singleton] at hz
          rcases hz with hz | rfl
          exacts [h₁ z hz, hy]) h₂'
        rw [ev_swap hR v l₁ l₂ x y hx hy, ev_swap hR' v' l₁ l₂ x y hx hy]
        simp only [sub_mul, add_mul, hm, ite_mul, zero_mul]
        congr 1
        · congr 1
          split_ifs with e
          · exact hs _ (by simp only; rw [hx, e, hy])
          · rfl
        · split_ifs with e
          · exact hs _ (by simp only; rw [hy, e, hx])
          · rfl
    intro l hl hc
    cases l with
    | nil => simp at hl
    | cons x l =>
      have hx : ε x.1 = ε x.2 := hc x (by simp)
      rcases le_or_gt x.1 x.2 with hle | hlt
      · exact key x hx hle l [] (by simpa using hl) (by simp) (fun z hz => hc z (by simp [hz]))
      · rw [ev_first hA hH l x hx hlt, ev_first hA' hH' l x hx hlt]; simp

end GlobalTheory.CompanionTheory.AlgRepEndIrreducible.Vev
end

section -- merged from Development.AutomorphicSpectrum.Proofs.JetProofs.GraphExtend
open GlobalTheory.CompanionTheory.AlgRepEndIrreducible PI.UpqRep Matrix
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.AlgRepEndIrreducible.HwMap

theorem word_adj {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {D : Fin n → Fin n → Module.End ℂ V} (h : KAdj ε D) (l : List (Fin n × Fin n))
    (hl : ∀ x ∈ l, ε x.1 = ε x.2) (x y : V) :
    ⟪(l.map fun x => D x.1 x.2).prod x, y⟫_ℂ =
      ⟪x, (((l.map Prod.swap).reverse).map fun x => D x.1 x.2).prod y⟫_ℂ := by
  induction l generalizing y with
  | nil => simp
  | cons a l ih =>
    have ha := hl a (by simp)
    have ih' := ih (fun x hx => hl x (by simp [hx])) (D a.2 a.1 y)
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, List.reverse_cons,
      List.map_append, List.prod_append, List.map_nil, List.prod_nil, mul_one, Prod.fst_swap,
      Prod.snd_swap]
    rw [h _ _ ha, ih']

theorem graph_extend {n : ℕ} {ε : Fin n → Bool} {V V' : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [AddCommGroup V'] [Module ℂ V']
    {D : Fin n → Fin n → Module.End ℂ V} {D' : Fin n → Fin n → Module.End ℂ V'} (h : KAdj ε D)
    (G : Submodule ℂ (V × V')) (hG : ∀ g ∈ G, g.1 = 0 → g.2 = 0)
    (hst : ∀ a b, ε a = ε b → ∀ g ∈ G, (D a b g.1, D' a b g.2) ∈ G) :
    ∃ T : V →ₗ[ℂ] V', (∀ g ∈ G, T g.1 = g.2) ∧ KMap ε D D' T := by
  let A : G →ₗ[ℂ] V := (LinearMap.fst ℂ V V').comp G.subtype
  have hA : Function.Injective A := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro g hg
    have h1 : g.1.1 = 0 := hg
    exact Subtype.ext (Prod.ext h1 (hG _ g.2 h1))
  let U : Submodule ℂ V := LinearMap.range A
  let e : G ≃ₗ[ℂ] U := LinearEquiv.ofInjective A hA
  let T : V →ₗ[ℂ] V' := ((LinearMap.snd ℂ V V').comp G.subtype).comp
    (e.symm.toLinearMap.comp (U.orthogonalProjectionOnto : V →ₗ[ℂ] U))
  have key : ∀ g ∈ G, ∀ z ∈ Uᗮ, T (g.1 + z) = g.2 := by
    intro g hg z hz
    have h1 : U.orthogonalProjectionOnto (g.1 + z) = e ⟨g, hg⟩ := by
      rw [map_add (f := _), Submodule.orthogonalProjectionOnto_eq_zero_iff.2 hz, add_zero]
      exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (e ⟨g, hg⟩)
    show ((e.symm (U.orthogonalProjectionOnto (g.1 + z)) : G) : V × V').2 = g.2
    rw [h1, e.symm_apply_apply]
  refine ⟨T, fun g hg => by simpa using key g hg 0 (zero_mem _), ?_⟩
  intro a b hab w
  obtain ⟨u, hu, z, hz, rfl⟩ := U.exists_add_mem_mem_orthogonal w
  obtain ⟨g, rfl⟩ := hu
  have hz' : D a b z ∈ Uᗮ := by
    rw [Submodule.mem_orthogonal]
    rintro _ ⟨g', rfl⟩
    rw [← h b a hab.symm]
    exact (Submodule.mem_orthogonal _ _).1 hz _ ⟨⟨_, hst b a hab.symm _ g'.2⟩, rfl⟩
  have h1 := key _ (hst a b hab _ g.2) _ hz'
  have h2 := key _ g.2 _ hz
  have h3 : A g = g.1.1 := rfl
  rw [h3, h2, map_add (f := _)]
  exact h1

theorem hwmap : ∀ (n : ℕ) (ε : Fin n → Bool) (V V' : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] (D : Fin n → Fin n → Module.End ℂ V) (D' : Fin n → Fin n → Module.End ℂ V') (μ : Fin n → ℝ) (v : V) (v' : V'), KRel ε D → KRel ε D' → KAdj ε D → KAdj ε D' → Formalism.REAL.KHighest ε D μ v → Formalism.REAL.KHighest ε D' μ v' → v ≠ 0 → ∃ T : V →ₗ[ℂ] V', T v = v' ∧ KMap ε D D' T := by
  intro n ε V V' _ _ _ _ _ D D' μ v v' hR hR' hA hA' hv hv' hv0
  have vev := GlobalTheory.CompanionTheory.AlgRepEndIrreducible.Vev.vev_eq n ε V V' D D' μ v v' hR hR' hA hA' hv hv'
  let S : Set (V × V') := {g | ∃ l : List (Fin n × Fin n), (∀ x ∈ l, ε x.1 = ε x.2) ∧
    g = ((l.map fun x => D x.1 x.2).prod v, (l.map fun x => D' x.1 x.2).prod v')}
  have hin : ∀ g ∈ Submodule.span ℂ S, ∀ g' ∈ Submodule.span ℂ S,
      ⟪g.1, g'.1⟫_ℂ * ⟪v', v'⟫_ℂ = ⟪g.2, g'.2⟫_ℂ * ⟪v, v⟫_ℂ := by
    intro g hg g' hg'
    induction hg using Submodule.span_induction with
    | zero => simp
    | add x y _ _ hx hy => simp only [Prod.fst_add, Prod.snd_add, inner_add_left, add_mul, hx, hy]
    | smul c x _ hx => simp only [Prod.smul_fst, Prod.smul_snd, inner_smul_left, mul_assoc, hx]
    | mem x hx =>
      induction hg' using Submodule.span_induction with
      | zero => simp
      | add x y _ _ hx hy =>
        simp only [Prod.fst_add, Prod.snd_add, inner_add_right, add_mul, hx, hy]
      | smul c x _ hx => simp only [Prod.smul_fst, Prod.smul_snd, inner_smul_right, mul_assoc, hx]
      | mem y hy =>
        obtain ⟨l, hl, rfl⟩ := hx
        obtain ⟨l', hl', rfl⟩ := hy
        have := vev ((l.map Prod.swap).reverse ++ l') (by
          intro x hx
          rcases List.mem_append.1 hx with hx | hx
          · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 (List.mem_reverse.1 hx)
            exact (hl y hy).symm
          · exact hl' x hx)
        simp only [List.map_append, List.prod_append, Module.End.mul_apply] at this
        dsimp only
        rw [word_adj hA l hl, word_adj hA' l hl, this]
  obtain ⟨T, hT, hK⟩ := graph_extend (D' := D') hA (Submodule.span ℂ S) (by
    intro g hg h0
    have := hin g hg g hg
    rw [h0, inner_zero_left, zero_mul] at this
    rcases mul_eq_zero.1 this.symm with h | h
    · exact inner_self_eq_zero.1 h
    · exact absurd (inner_self_eq_zero.1 h) hv0) (by
    intro a b hab g hg
    induction hg using Submodule.span_induction with
    | zero =>
      simp only [Prod.fst_zero, Prod.snd_zero, map_zero]
      exact Submodule.zero_mem _
    | add x y _ _ hx hy => simpa using Submodule.add_mem _ hx hy
    | smul c x _ hx => simpa using Submodule.smul_mem _ c hx
    | mem x hx =>
      obtain ⟨l, hl, rfl⟩ := hx
      refine Submodule.subset_span ⟨(a, b) :: l, ?_, by simp⟩
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hab
      · exact hl x hx)
  exact ⟨T, hT (v, v') (Submodule.subset_span ⟨[], by simp, by simp⟩), hK⟩

end GlobalTheory.CompanionTheory.AlgRepEndIrreducible.HwMap
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HighestWeightTensorDecomposition
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

namespace GlobalTheory.CompanionTheory.RealCount.ExtHw

theorem inner_word_eq_zero {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (D : Fin n → Fin n → Module.End ℂ H) (μ : Fin n → ℝ) (hR : Formalism.REAL.GlRel D)
    (hA : ∀ a b (x y : H), ⟪D a b x, y⟫_ℂ = ⟪x, D b a y⟫_ℂ) (Hs : Submodule ℂ H)
    (hs : ∀ x ∈ Hs, Formalism.REAL.KHighest (fun _ => true) D μ x) {x y : H} (hx : x ∈ Hs) (hy : y ∈ Hs)
    (hxx : ⟪x, x⟫_ℂ = 1) (hyy : ⟪y, y⟫_ℂ = 1) (hxy : ⟪x, y⟫_ℂ = 0)
    (l : List (Fin n × Fin n)) : ⟪x, (l.map fun z => D z.1 z.2).prod y⟫_ℂ = 0 := by
  have hyx : ⟪y, x⟫_ℂ = 0 := by rw [← inner_conj_symm, hxy, map_zero]
  have vev : ∀ u ∈ Hs, ∀ v ∈ Hs,
      ⟪u, (l.map fun z => D z.1 z.2).prod u⟫_ℂ * ⟪v, v⟫_ℂ =
        ⟪v, (l.map fun z => D z.1 z.2).prod v⟫_ℂ * ⟪u, u⟫_ℂ := fun u hu v hv =>
    GlobalTheory.CompanionTheory.AlgRepEndIrreducible.Vev.vev_eq n (fun _ => true) H H D D μ u v (fun a b c d _ _ => hR a b c d)
      (fun a b c d _ _ => hR a b c d) (fun a b _ => hA a b) (fun a b _ => hA a b)
      (hs u hu) (hs v hv) l (fun _ _ => rfl)
  generalize (l.map fun z => D z.1 z.2).prod = W at vev ⊢
  have h1 := vev x hx y hy
  have h2 := vev (x + y) (Hs.add_mem hx hy) x hx
  have h3 := vev (x + Complex.I • y) (Hs.add_mem hx (Hs.smul_mem _ hy)) x hx
  simp only [map_add (f := _), map_smul, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    hxx, hyy, hxy, hyx, Complex.conj_I] at h1 h2 h3
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have h4 : ⟪x, W y⟫_ℂ + ⟪y, W x⟫_ℂ = 0 := by linear_combination h2 + h1
  have h5 : Complex.I * (⟪x, W y⟫_ℂ - ⟪y, W x⟫_ℂ) = 0 := by
    linear_combination h3 + h1 + (⟪y, W y⟫_ℂ - ⟪x, W x⟫_ℂ) * hI
  have h6 : ⟪x, W y⟫_ℂ - ⟪y, W x⟫_ℂ = 0 :=
    (mul_eq_zero.1 h5).resolve_left Complex.I_ne_zero
  linear_combination (1 / 2 : ℂ) * h4 + (1 / 2 : ℂ) * h6

theorem kmap_extend : ∀ {n : ℕ} (H V : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [NormedAddCommGroup V] [InnerProductSpace ℂ V] (D : Fin n → Fin n → Module.End ℂ H) (D' : Fin n → Fin n → Module.End ℂ V) (μ : Fin n → ℝ), Formalism.REAL.GlRel D → Formalism.REAL.GlRel D' → (∀ a b (x y : H), ⟪D a b x, y⟫_ℂ = ⟪x, D b a y⟫_ℂ) → (∀ a b (x y : V), ⟪D' a b x, y⟫_ℂ = ⟪x, D' b a y⟫_ℂ) → ∀ Hs : Submodule ℂ H, (∀ x ∈ Hs, Formalism.REAL.KHighest (fun _ => true) D μ x) → ∀ f : Hs →ₗ[ℂ] V, (∀ x, Formalism.REAL.KHighest (fun _ => true) D' μ (f x)) → ∃ T : H →ₗ[ℂ] V, (∀ x : Hs, T x = f x) ∧ ∀ a b w, T (D a b w) = D' a b (T w) := by
  intro n H V _ _ _ _ _ D D' μ hR hR' hA hA' Hs hs f hf
  let ξ := stdOrthonormalBasis ℂ Hs
  have hself : ∀ i, ⟪(ξ i : H), (ξ i : H)⟫_ℂ = 1 := fun i => by
    have := (orthonormal_iff_ite.1 ξ.orthonormal) i i
    rw [if_pos rfl] at this
    exact this
  have hoff : ∀ i j, i ≠ j → ⟪(ξ i : H), (ξ j : H)⟫_ℂ = 0 := fun i j hij => by
    have := (orthonormal_iff_ite.1 ξ.orthonormal) i j
    rw [if_neg hij] at this
    exact this
  have hne : ∀ i, (ξ i : H) ≠ 0 := fun i h0 => by
    have := hself i
    rw [h0, inner_zero_left] at this
    exact zero_ne_one this
  have hex : ∀ i, ∃ T : H →ₗ[ℂ] V, T (ξ i : H) = f (ξ i) ∧ GlobalTheory.CompanionTheory.AlgRepEndIrreducible.KMap (fun _ => true) D D' T :=
    fun i => GlobalTheory.CompanionTheory.AlgRepEndIrreducible.HwMap.hwmap n (fun _ => true) H V D D' μ (ξ i : H) (f (ξ i))
      (fun a b c d _ _ => hR a b c d) (fun a b c d _ _ => hR' a b c d)
      (fun a b _ => hA a b) (fun a b _ => hA' a b) (hs _ (ξ i).2) (hf _) (hne i)
  choose Ti hTi hTK using hex
  let Z : _ → Submodule ℂ H := fun i => Submodule.span ℂ
    (Set.range fun l : List (Fin n × Fin n) => (l.map fun z => D z.1 z.2).prod (ξ i : H))
  have hst : ∀ i a b, ∀ z ∈ Z i, D a b z ∈ Z i := by
    intro i a b z hz
    induction hz using Submodule.span_induction with
    | zero => simp
    | add x y _ _ hx hy => simpa using Submodule.add_mem _ hx hy
    | smul c x _ hx => simpa using Submodule.smul_mem _ c hx
    | mem x hx =>
      obtain ⟨l, rfl⟩ := hx
      exact Submodule.subset_span ⟨(a, b) :: l, by simp⟩
  have hperp : ∀ i a b, ∀ z ∈ (Z i)ᗮ, D a b z ∈ (Z i)ᗮ := by
    intro i a b z hz
    rw [Submodule.mem_orthogonal] at hz ⊢
    intro u hu
    rw [← hA b a]
    exact hz _ (hst i b a u hu)
  have hcomm : ∀ i a b w, (Z i).starProjection (D a b w) = D a b ((Z i).starProjection w) := by
    intro i a b w
    obtain ⟨u, hu, z, hz, rfl⟩ := (Z i).exists_add_mem_mem_orthogonal w
    have e1 : (Z i).starProjection u = u := Submodule.starProjection_eq_self_iff.2 hu
    have e2 : (Z i).starProjection z = 0 := (Submodule.starProjection_apply_eq_zero_iff _).2 hz
    have e3 : (Z i).starProjection (D a b u) = D a b u :=
      Submodule.starProjection_eq_self_iff.2 (hst i a b u hu)
    have e4 : (Z i).starProjection (D a b z) = 0 :=
      (Submodule.starProjection_apply_eq_zero_iff _).2 (hperp i a b z hz)
    rw [map_add (f := _), map_add (f := _), map_add (f := _), e1, e2, e3, e4, add_zero, add_zero]
  have hdiag : ∀ i, (Z i).starProjection (ξ i : H) = ξ i := fun i =>
    Submodule.starProjection_eq_self_iff.2 (Submodule.subset_span ⟨[], by simp⟩)
  have hzero : ∀ i j, i ≠ j → (Z i).starProjection (ξ j : H) = 0 := by
    intro i j hij
    refine (Submodule.starProjection_apply_eq_zero_iff _).2 ?_
    rw [Submodule.mem_orthogonal]
    intro u hu
    induction hu using Submodule.span_induction with
    | zero => simp
    | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
    | smul c x _ hx => rw [inner_smul_left, hx, mul_zero]
    | mem x hx =>
      obtain ⟨l, rfl⟩ := hx
      rw [GlobalTheory.CompanionTheory.AlgRepEndIrreducible.HwMap.word_adj (ε := fun _ => true) (fun a b _ => hA a b) l (fun _ _ => rfl)]
      exact inner_word_eq_zero D μ hR hA Hs hs (ξ i).2 (ξ j).2 (hself i) (hself j) (hoff i j hij) _
  let T : H →ₗ[ℂ] V := ∑ i, (Ti i).comp ((Z i).starProjection : H →L[ℂ] H).toLinearMap
  have hTapp : ∀ w, T w = ∑ i, Ti i ((Z i).starProjection w) := fun w => by
    simp [T, LinearMap.sum_apply]
  refine ⟨T, ?_, ?_⟩
  · have hb : T.comp Hs.subtype = f := by
      refine ξ.toBasis.ext fun j => ?_
      rw [OrthonormalBasis.coe_toBasis, LinearMap.comp_apply, Submodule.subtype_apply, hTapp,
        Finset.sum_eq_single j]
      · rw [hdiag, hTi]
      · intro i _ hij
        rw [hzero i j hij, map_zero]
      · intro h
        exact absurd (Finset.mem_univ j) h
    intro x
    exact LinearMap.congr_fun hb x
  · intro a b w
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hTapp, hTapp, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hcomm, hTK i a b rfl]

end GlobalTheory.CompanionTheory.RealCount.ExtHw
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HighestWeightTensorDecompositionStatement
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.highest_weight_tensor_decomposition : ∀ {n : ℕ} (H V : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [NormedAddCommGroup V] [InnerProductSpace ℂ V] (D : Fin n → Fin n → Module.End ℂ H) (D' : Fin n → Fin n → Module.End ℂ V) (μ : Fin n → ℝ), Formalism.REAL.GlRel D → Formalism.REAL.GlRel D' → (∀ a b (x y : H), ⟪D a b x, y⟫_ℂ = ⟪x, D b a y⟫_ℂ) → (∀ a b (x y : V), ⟪D' a b x, y⟫_ℂ = ⟪x, D' b a y⟫_ℂ) → ∀ Hs : Submodule ℂ H, (∀ x ∈ Hs, Formalism.REAL.KHighest (fun _ => true) D μ x) → ∀ f : Hs →ₗ[ℂ] V, (∀ x, Formalism.REAL.KHighest (fun _ => true) D' μ (f x)) → ∃ T : H →ₗ[ℂ] V, (∀ x : Hs, T x = f x) ∧ ∀ a b w, T (D a b w) = D' a b (T w) := by
  first | exact @GlobalTheory.CompanionTheory.RealCount.ExtHw.kmap_extend | exact GlobalTheory.CompanionTheory.RealCount.ExtHw.kmap_extend | (intros; apply GlobalTheory.CompanionTheory.RealCount.ExtHw.kmap_extend <;> assumption)
end
