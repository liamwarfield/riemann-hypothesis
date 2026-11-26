module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FGe
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qk42.M4 :
    Type → Type :=
    fun (R : Type) ↦ Matrix (Fin (4 : ℕ)) (Fin (4 : ℕ)) R

noncomputable def UpperTheory.Reformulated.B.Qk42.FGe :
    {R : Type} → [CommRing R] → (Fin (4 : ℕ) → ℤ) → ℤ → UpperTheory.Reformulated.B.Qk42.M4 R → Prop :=
    fun {R : Type} [CommRing R] (m : Fin (4 : ℕ) → ℤ) (p : ℤ) (X : UpperTheory.Reformulated.B.Qk42.M4 R) ↦
      ∀ (i j : Fin (4 : ℕ)), m i - m j < p → X i j = (0 : R)

theorem UpperTheory.Reformulated.B.Qk42.mul :
    ∀ {R : Type} [inst : CommRing R] {m : Fin (4 : ℕ) → ℤ} {p q : ℤ} {A B : UpperTheory.Reformulated.B.Qk42.M4 R},
      UpperTheory.Reformulated.B.Qk42.FGe m p A → UpperTheory.Reformulated.B.Qk42.FGe m q B → UpperTheory.Reformulated.B.Qk42.FGe m (p + q) (A * B) := by
  intro R _ m p q A B hA hB i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : m i - m k < p
  · rw [hA i k hk, zero_mul]
  · rw [hB k j (by omega), mul_zero]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedTanDefs
noncomputable section

open UpperTheory.V.GradeZeroInterpolatingElement

namespace UpperTheory.V.Ws

section Mat

variable {R : Type} [CommRing R]

def cmp (m : Fin 4 → ℤ) (p : ℤ) : M4 R →ₗ[R] M4 R where
  toFun X := Matrix.of fun i j => if m i - m j = p then X i j else 0
  map_add' X Y := by ext i j; simp only [Matrix.of_apply, Matrix.add_apply]; split_ifs <;> simp
  map_smul' c X := by ext i j; simp only [Matrix.of_apply, Matrix.smul_apply, RingHom.id_apply]; split_ifs <;> simp

theorem cmp_apply (m : Fin 4 → ℤ) (p : ℤ) (X : M4 R) (i j : Fin 4) :
    cmp m p X i j = if m i - m j = p then X i j else 0 := rfl

def FGe (m : Fin 4 → ℤ) (p : ℤ) (X : M4 R) : Prop := ∀ i j, m i - m j < p → X i j = 0

def Lim (m : Fin 4 → ℤ) (A A₀ : M4 R) : Prop := FGe m 0 A ∧ A₀ = cmp m 0 A

def Symp (m : Fin 4 → ℤ) : Prop := ∀ i : Fin 4, m i + m i.rev = m 0 + m 3

theorem FGe.mul {m : Fin 4 → ℤ} {p q : ℤ} {A B : M4 R} (hA : FGe m p A) (hB : FGe m q B) : FGe m (p + q) (A * B) :=
  _root_.UpperTheory.Reformulated.B.Qk42.mul hA hB

theorem cmp_mul {m : Fin 4 → ℤ} {p q : ℤ} {A B : M4 R} (hA : FGe m p A) (hB : FGe m q B) :
    cmp m (p + q) (A * B) = cmp m p A * cmp m q B := by
  ext i j
  simp only [cmp_apply, Matrix.mul_apply]
  split_ifs with h
  · refine Finset.sum_congr rfl fun l _ => ?_
    by_cases h1 : m i - m l < p
    · simp [hA i l h1]
    · by_cases h2 : m l - m j < q
      · simp [hB l j h2]
      · rw [if_pos (by omega), if_pos (by omega)]
  · refine (Finset.sum_eq_zero fun l _ => ?_).symm
    split_ifs with h1 h2
    · omega
    all_goals simp

theorem FGe.add {m : Fin 4 → ℤ} {p : ℤ} {A B : M4 R} (hA : FGe m p A) (hB : FGe m p B) : FGe m p (A + B) :=
  fun i j h => by rw [Matrix.add_apply, hA i j h, hB i j h, add_zero]

theorem FGe.sub {m : Fin 4 → ℤ} {p : ℤ} {A B : M4 R} (hA : FGe m p A) (hB : FGe m p B) : FGe m p (A - B) :=
  fun i j h => by rw [Matrix.sub_apply, hA i j h, hB i j h, sub_zero]

theorem FGe.adj {m : Fin 4 → ℤ} (hm : Symp m) {p : ℤ} {A : M4 R} (hA : FGe m p A) : FGe m p (adj A) := by
  intro i j h
  have h1 := hm i
  have h2 := hm j
  rw [adj_apply, hA _ _ (by omega), smul_zero]

theorem cmp_adj {m : Fin 4 → ℤ} (hm : Symp m) (p : ℤ) (A : M4 R) : cmp m p (adj A) = adj (cmp m p A) := by
  ext i j
  have h1 := hm i
  have h2 := hm j
  simp only [cmp_apply, adj_apply]
  by_cases h : m i - m j = p
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega), smul_zero]

end Mat

namespace Fr

variable {O Γ : Type} [CommRing O] [Group Γ] (Φ : Fr O Γ) {R : Type} [CommRing R]

def cmpT (m : Fin 4 → ℤ) (p : ℤ) : ((Γ → M4 R) × (Φ.ι → M4 R)) →ₗ[R] ((Γ → M4 R) × (Φ.ι → M4 R)) :=
  LinearMap.prodMap ((cmp m p).compLeft Γ) ((cmp m p).compLeft Φ.ι)

theorem cmpT_fst (m : Fin 4 → ℤ) (p : ℤ) (x : (Γ → M4 R) × (Φ.ι → M4 R)) (g : Γ) :
    (Φ.cmpT m p x).1 g = cmp m p (x.1 g) := rfl

theorem cmpT_snd (m : Fin 4 → ℤ) (p : ℤ) (x : (Γ → M4 R) × (Φ.ι → M4 R)) (v : Φ.ι) :
    (Φ.cmpT m p x).2 v = cmp m p (x.2 v) := rfl

variable [TopologicalSpace Γ]

def TanS (S : Finset (ℤ × ℤ)) (c : PD Φ.ι Γ R) : Submodule R ((Γ → M4 R) × (Φ.ι → M4 R)) where
  carrier := Φ.Tan S c
  add_mem' := by
    rintro x y ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩
    refine ⟨a1.add b1, fun g => add_mem (a2 g) (b2 g), fun g h => ?_, fun g h => ?_, a5.add b5, fun g i j h1 h2 => ?_,
      fun v => ⟨add_mem (a7 v).1 (b7 v).1, fun i j h => ?_⟩, fun v s hs i j h => ?_⟩
    · simp only [Prod.fst_add, Pi.add_apply, a3, b3, mul_add, add_mul]; abel
    · simp [a4 g h, b4 g h]
    · simp only [Prod.fst_add, Pi.add_apply, add_mul, Matrix.add_apply, a6 g i j h1 h2, b6 g i j h1 h2, add_zero]
    · simp only [Prod.snd_add, Pi.add_apply, add_mul, mul_add, Matrix.add_apply, (a7 v).2 i j h, (b7 v).2 i j h, add_zero]
    · have e : (x + y).1 s + c.r s * (x + y).2 v * c.r s⁻¹ - (x + y).2 v =
          (x.1 s + c.r s * x.2 v * c.r s⁻¹ - x.2 v) + (y.1 s + c.r s * y.2 v * c.r s⁻¹ - y.2 v) := by
        simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, mul_add, add_mul]; abel
      rw [e, mul_add, add_mul, Matrix.add_apply, a8 v s hs i j h, b8 v s hs i j h, add_zero]
  zero_mem' := ⟨IsLocallyConstant.const 0, fun _ => zero_mem _, by simp, by simp, Matrix.isDiag_zero,
    fun g i j _ _ => by simp, fun v => ⟨zero_mem _, by simp⟩, fun v s _ i j _ => by simp⟩
  smul_mem' := by
    rintro t x ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩
    refine ⟨a1.comp (t • ·), fun g => Submodule.smul_mem _ t (a2 g), fun g h => ?_, fun g h => ?_, a5.smul t,
      fun g i j h1 h2 => ?_, fun v => ⟨Submodule.smul_mem _ t (a7 v).1, fun i j h => ?_⟩, fun v s hs i j h => ?_⟩
    · simp only [Prod.smul_fst, Pi.smul_apply, a3, smul_add, Matrix.mul_smul, Matrix.smul_mul]
    · simp [a4 g h]
    · simp only [Prod.smul_fst, Pi.smul_apply, Matrix.smul_mul, Matrix.smul_apply, a6 g i j h1 h2, smul_zero]
    · simp only [Prod.smul_snd, Pi.smul_apply, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_apply, (a7 v).2 i j h, smul_zero]
    · have e : (t • x).1 s + c.r s * (t • x).2 v * c.r s⁻¹ - (t • x).2 v =
          t • (x.1 s + c.r s * x.2 v * c.r s⁻¹ - x.2 v) := by
        simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, Matrix.mul_smul, Matrix.smul_mul, smul_add, smul_sub]
      rw [e, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, a8 v s hs i j h, smul_zero]

theorem span_Tan (S : Finset (ℤ × ℤ)) (c : PD Φ.ι Γ R) : Submodule.span R (Φ.Tan S c) = Φ.TanS S c :=
  Submodule.span_eq (Φ.TanS S c)

variable (a : O →+* R)

def OneOdd (S : Finset (ℤ × ℤ)) (c : PD Φ.ι Γ R) : Prop :=
  ∃ i₀ j₀ : Fin 4, wt i₀ j₀ ∈ oddRoots ∧ ∀ x ∈ Φ.Tan S c, (∀ g, x.1 g i₀ j₀ = 0) →
    ∀ i j : Fin 4, i ≤ j.rev → wt i j ∈ oddRoots → ∃ n, Φ.LocTriv a (wt i j) (fun g => x.1 g i j) n


omit [TopologicalSpace Γ] in
def splitPs (b : Φ.ι → R) : PD Φ.ι Γ R := ⟨(Φ.split a).r, fun v => 1 + b v • Xm R⟩

variable {Φ a}

theorem Ok.rt_wt (h : Φ.Ok a) (i j : Fin 4) (g : Γ) : Φ.rt (wt i j) g = Φ.χ i g * (Φ.χ j g)⁻¹ := by
  have h0 := h.mul 0 g
  have h1 := h.mul 1 g
  have e : Φ.χ 3 g = Φ.χ 1 g * Φ.χ 2 g * (Φ.χ 0 g)⁻¹ := by
    have : Φ.χ 0 g * Φ.χ 3 g = Φ.χ 1 g * Φ.χ 2 g := h0.trans h1.symm
    rw [← this, mul_comm (Φ.χ 0 g), mul_inv_cancel_right]
  apply Additive.ofMul.injective
  fin_cases i <;> fin_cases j <;>
    simp [Fr.rt, wt, lamW, muW, e] <;> abel

theorem Ok.conj_split (h : Φ.Ok a) (g : Γ) (Y : M4 R) (i j : Fin 4) :
    ((Φ.split a).r g * Y * (Φ.split a).r g⁻¹) i j = a (Φ.rt (wt i j) g) * Y i j := by
  have e : ∀ g, (Φ.split a).r g = Matrix.diagonal fun i => a (Φ.χ i g) := fun g => by
    ext i j
    simp only [Fr.split, mapRep_apply, diagRep, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.diagonal_apply]
    split_ifs <;> simp
  rw [e, e, Matrix.mul_diagonal, Matrix.diagonal_mul, h.rt_wt, map_inv, Units.val_mul, map_mul]
  ring

omit [TopologicalSpace Γ] in
theorem split_r_apply (g : Γ) (i j : Fin 4) : (Φ.split a).r g i j = if i = j then a (Φ.χ i g) else 0 := by
  simp only [Fr.split, mapRep_apply, diagRep, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.diagonal_apply]
  split_ifs <;> simp

end Fr

end UpperTheory.V.Ws

end
end

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Ws

theorem rank_le_of_lowest : ∀ {k V : Type} [Field k] [AddCommGroup V] [Module k V] (π : ℤ → V →ₗ[k] V) (T U : Submodule k V),
      (∀ p q x, π p (π q x) = if p = q then π q x else 0) → (∃ lo : ℤ, ∀ q < lo, π q = 0) →
      (∃ hi : ℤ, ∀ x, (∀ q < hi, π q x = 0) → x = 0) →
      (∀ p, ∀ x ∈ T, (∀ q < p, π q x = 0) → π p x ∈ U) → Module.rank k T ≤ Module.rank k U := by
  intro k V _ _ _ π T U h ⟨lo, hlo⟩ ⟨hi, hhi⟩ H
  let K : ℤ → Submodule k V := fun p => ⨅ q < p, LinearMap.ker (π q)
  have hK : ∀ p x, x ∈ K p ↔ ∀ q < p, π q x = 0 := fun p x => by simp [K, Submodule.mem_iInf]
  have step : ∀ (W : Submodule k V) p, Module.rank k ↥(W ⊓ K p) =
      Module.rank k ↥((W ⊓ K p).map (π p)) + Module.rank k ↥(W ⊓ K (p + 1)) := by
    intro W p
    rw [← LinearMap.rank_range_add_rank_ker ((π p).domRestrict (W ⊓ K p)), LinearMap.range_domRestrict]
    congr 1
    rw [LinearMap.ker_domRestrict]
    have e : W ⊓ K (p + 1) = (W ⊓ K p) ⊓ LinearMap.ker (π p) := by
      ext x
      simp only [Submodule.mem_inf, hK, LinearMap.mem_ker]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1, fun q hq => h2 q (by omega)⟩, h2 p (by omega)⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨h1, fun q hq => ?_⟩
        rcases lt_or_eq_of_le (show q ≤ p by omega) with h4 | rfl
        exacts [h2 q h4, h3]
    rw [e, ← Submodule.map_comap_subtype (W ⊓ K p) (LinearMap.ker (π p))]
    exact (Submodule.equivMapOfInjective _ (W ⊓ K p).subtype_injective _).rank_eq
  have main : ∀ p ≤ max hi lo, Module.rank k ↥(T ⊓ K p) ≤ Module.rank k ↥(U ⊓ K p) := by
    intro p hp
    induction p using Int.inductionOn' (b := max hi lo) with
    | zero =>
      have : T ⊓ K (max hi lo) = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        exact hhi x fun q hq => (hK _ _).1 hx.2 q (lt_max_of_lt_left hq)
      rw [this]; simp
    | succ n hn ih => omega
    | pred n hn ih =>
      rw [step T, step U, sub_add_cancel]
      refine add_le_add (Submodule.rank_mono ?_) (ih hn)
      rintro _ ⟨x, ⟨h1, h2⟩, rfl⟩
      refine ⟨π (n - 1) x, ⟨H _ x h1 ((hK _ _).1 h2), (hK _ _).2 fun q hq => ?_⟩, ?_⟩
      · rw [h, if_neg hq.ne]
      · rw [h, if_pos rfl]
  have top : K lo = ⊤ := by
    rw [eq_top_iff]
    intro x _
    exact (hK _ _).2 fun q hq => by simp [hlo q hq]
  have := main lo (le_max_right _ _)
  rwa [top, inf_top_eq, inf_top_eq] at this

theorem tan_lowest : ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] (Φ : Fr O Γ) {k : Type} [Field k] (S : Finset (ℤ × ℤ)) (c c₀ : PD Φ.ι Γ k) (m : Fin 4 → ℤ), Symp m →
      (∀ g, Lim m (c.r g) (c₀.r g)) → (∀ v, Lim m (c.n v) (c₀.n v)) → ∀ p : ℤ, ∀ x ∈ Φ.Tan S c,
      (∀ g, FGe m p (x.1 g)) → (∀ v, FGe m p (x.2 v)) → Φ.cmpT m p x ∈ Φ.Tan S c₀ := by
  intro O Γ _ _ _ Φ k _ S c c₀ m hm hr hn p x ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ hX hY
  have c3 : ∀ {A B Z : M4 k}, FGe m 0 A → FGe m 0 B → FGe m p Z →
      FGe m p (A * Z * B) ∧ cmp m p (A * Z * B) = cmp m 0 A * cmp m p Z * cmp m 0 B := by
    intro A B Z hA hB hZ
    have h1 := (hA.mul hZ).mul hB
    have h2 := cmp_mul (hA.mul hZ) hB
    rw [cmp_mul hA hZ] at h2
    simp only [zero_add, add_zero] at h1 h2
    exact ⟨h1, h2⟩
  have csp : ∀ {Z : M4 k}, Z ∈ sp4 k → cmp m p Z ∈ sp4 k := by
    intro Z hZ
    show adj _ = -_
    rw [← cmp_adj hm, show adj Z = -Z from hZ, map_neg]
  have cz : ∀ {Z : M4 k} {i j}, Z i j = 0 → cmp m p Z i j = 0 := by
    intro Z i j h
    simp [cmp_apply, h]
  have cn : ∀ v {Z : M4 k}, FGe m p Z → adj (c₀.n v) * cmp m p Z * c₀.n v = cmp m p (adj (c.n v) * Z * c.n v) := by
    intro v Z hZ
    rw [(c3 ((hn v).1.adj hm) (hn v).1 hZ).2, cmp_adj hm, ← (hn v).2]
  refine ⟨a1.comp (cmp m p), fun g => csp (a2 g), fun g h => ?_, fun g h => ?_, fun i j h => cz (a5 h),
    fun g i j h1 h2 => ?_, fun v => ⟨csp (a7 v).1, fun i j h => ?_⟩, fun v s hs i j h => ?_⟩
  · simp only [Fr.cmpT_fst]
    rw [a3, map_add (f := _), (c3 (hr g).1 (hr g⁻¹).1 (hX h)).2, ← (hr g).2, ← (hr g⁻¹).2]
  · rw [Fr.cmpT_fst, a4 g h, map_zero]
  · have := cmp_mul (hX g) (hr g).1
    rw [add_zero, ← (hr g).2] at this
    rw [Fr.cmpT_fst, ← this]
    exact cz (a6 g i j h1 h2)
  · rw [Fr.cmpT_snd, cn v (hY v)]
    exact cz ((a7 v).2 i j h)
  · have h3 := c3 (hr s).1 (hr s⁻¹).1 (hY v)
    rw [← (hr s).2, ← (hr s⁻¹).2] at h3
    rw [Fr.cmpT_snd, Fr.cmpT_fst, ← h3.2, ← map_add (f := _), ← map_sub, cn v (((hX s).add h3.1).sub (hY v))]
    exact cz (a8 v s hs i j h)

theorem tan_flow {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] (Φ : Fr O Γ) {k : Type} [Field k]
    (S : Finset (ℤ × ℤ)) (c c₀ : PD Φ.ι Γ k) (m : Fin 4 → ℤ) (hm : Symp m)
    (hr : ∀ g, Lim m (c.r g) (c₀.r g)) (hn : ∀ v, Lim m (c.n v) (c₀.n v)) :
    Module.rank k (Φ.TanS S c) ≤ Module.rank k (Φ.TanS S c₀) := by
  obtain ⟨N, hN⟩ : ∃ N : ℤ, ∀ i j, |m i - m j| < N :=
    ⟨∑ z : Fin 4 × Fin 4, |m z.1 - m z.2| + 1, fun i j => Int.lt_add_one_of_le
      (Finset.single_le_sum (f := fun z : Fin 4 × Fin 4 => |m z.1 - m z.2|) (fun _ _ => abs_nonneg _) (Finset.mem_univ (i, j)))⟩
  have ge : ∀ {p : ℤ} {Z : M4 k}, (∀ q < p, cmp m q Z = 0) → FGe m p Z := by
    intro p Z h i j hij
    have := congrFun (congrFun (h _ hij) i) j
    simpa [cmp_apply] using this
  have cc : ∀ (p q : ℤ) (Z : M4 k), cmp m p (cmp m q Z) = if p = q then cmp m q Z else 0 := by
    intro p q Z
    ext i j
    by_cases h : p = q
    · subst h; simp only [cmp_apply, if_true]; split_ifs <;> rfl
    · simp only [cmp_apply, if_neg h, Matrix.zero_apply]
      split_ifs with h1 h2
      · omega
      all_goals rfl
  refine rank_le_of_lowest (Φ.cmpT m) _ _ (fun p q x => ?_) ⟨-N, fun q hq => ?_⟩ ⟨N, fun x hx => ?_⟩ fun p x hx h => ?_
  · refine Prod.ext (funext fun g => ?_) (funext fun v => ?_)
    · rw [Fr.cmpT_fst, Fr.cmpT_fst, cc]; split_ifs <;> rfl
    · rw [Fr.cmpT_snd, Fr.cmpT_snd, cc]; split_ifs <;> rfl
  · have : ∀ Z : M4 k, cmp m q Z = 0 := fun Z => by
      ext i j
      have := abs_lt.1 (hN i j)
      rw [cmp_apply, if_neg (by omega)]; rfl
    exact LinearMap.ext fun x => Prod.ext (funext fun g => this _) (funext fun v => this _)
  · refine Prod.ext (funext fun g => ?_) (funext fun v => ?_) <;> ext i j
    · exact ge (fun q hq => congrArg (·.1 g) (hx q hq)) i j (abs_lt.1 (hN i j)).2
    · exact ge (fun q hq => congrArg (·.2 v) (hx q hq)) i j (abs_lt.1 (hN i j)).2
  · exact tan_lowest Φ S c c₀ m hm hr hn p x hx (fun g => ge fun q hq => congrArg (·.1 g) (h q hq))
      fun v => ge fun q hq => congrArg (·.2 v) (h q hq)

end UpperTheory.V.Ws
