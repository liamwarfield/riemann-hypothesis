module

public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IsCongIdealTwoTorsion
open CompanionTheory.Rg.FlB

noncomputable section

namespace GlobalTheory.CompanionTheory.Iwahori

structure IsPieces {E ι : Type} [Ring E] [Fintype ι] (P : ι → E) : Prop where
  orth : ∀ i j, i ≠ j → P i * P j = 0
  idem : ∀ i, P i * P i = P i
  sum : ∑ i, P i = 1

def IsUpper {E ι : Type} [Ring E] (wt : ι → ℕ) (P : ι → E) (a : E) : Prop :=
  ∀ i j, wt j < wt i → P i * a * P j = 0

def IsLower {E ι : Type} [Ring E] (wt : ι → ℕ) (P : ι → E) (b : E) : Prop :=
  ∀ i j, wt i < wt j → P i * b * P j = 0

def IsLowerUni {E ι : Type} [Ring E] (wt : ι → ℕ) (P : ι → E) (b : E) : Prop :=
  IsLower wt P b ∧ ∀ i, P i * b * P i = P i

structure IsCongIdeal {E ι : Type} [Ring E] (J : AddSubgroup E) (P : ι → E) : Prop where
  mul_mem : ∀ x ∈ J, ∀ y ∈ J, x * y ∈ J
  left_mem : ∀ i, ∀ x ∈ J, P i * x ∈ J
  right_mem : ∀ i, ∀ x ∈ J, x * P i ∈ J
  inv : ∀ x ∈ J, ∃ y ∈ J, (1 + x) * (1 + y) = 1 ∧ (1 + y) * (1 + x) = 1

abbrev Idx (l : ℕ) := Option (Fin l ⊕ Fin l)

def wt {l : ℕ} : Idx l → ℕ
  | some (Sum.inl i) => i
  | none => l
  | some (Sum.inr i) => 2 * l - i

def rev {l : ℕ} : Idx l → Idx l
  | some (Sum.inl i) => some (Sum.inr i)
  | none => none
  | some (Sum.inr i) => some (Sum.inl i)

section Concrete

variable {L V : Type} [NontriviallyNormedField L] [AddCommGroup V] [Module L V]

def tau {l : ℕ} (s : L →+* L) (u : Fin l → L) : Idx l → L
  | some (Sum.inl i) => u i
  | none => 1
  | some (Sum.inr i) => (s (u i))⁻¹

def hLin {s : L →+* L} {h : V → V → L} (hh : IsHerm s h) (x : V) : V →ₗ[L] L where
  toFun := h x
  map_add' := hh.1 x
  map_smul' a y := by simpa using hh.2.1 a x y

def projE {s : L →+* L} {h : V → V → L} (hh : IsHerm s h) (δ : L) {l : ℕ} (e f : Fin l → V) (i : Fin l) :
    Module.End L V := (s δ)⁻¹ • (hLin hh (f i)).smulRight (e i)

def projF {s : L →+* L} {h : V → V → L} (hh : IsHerm s h) (δ : L) {l : ℕ} (e f : Fin l → V) (i : Fin l) :
    Module.End L V := δ⁻¹ • (hLin hh (e i)).smulRight (f i)

def piece {s : L →+* L} {h : V → V → L} (hh : IsHerm s h) (δ : L) {l : ℕ} (e f : Fin l → V) :
    Idx l → Module.End L V
  | some (Sum.inl i) => projE hh δ e f i
  | none => 1 - ∑ i, (projE hh δ e f i + projF hh δ e f i)
  | some (Sum.inr i) => projF hh δ e f i

def congJ (Λ : AddSubgroup V) (π : L) : AddSubgroup (Module.End L V) where
  carrier := {g | ∀ x ∈ Λ, ∃ y ∈ Λ, g x = π • y}
  zero_mem' x _ := ⟨0, Λ.zero_mem, by simp⟩
  add_mem' {g g'} hg hg' x hx := by
    obtain ⟨y, hy, e1⟩ := hg x hx
    obtain ⟨y', hy', e2⟩ := hg' x hx
    exact ⟨y + y', Λ.add_mem hy hy', by simp [e1, e2, smul_add]⟩
  neg_mem' {g} hg x hx := by
    obtain ⟨y, hy, e1⟩ := hg x hx
    exact ⟨-y, Λ.neg_mem hy, by simp [e1]⟩

end Concrete

end GlobalTheory.CompanionTheory.Iwahori

end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TorusStatement
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TorusStatement
open CompanionTheory.Rg.FlB

noncomputable section

namespace GlobalTheory.CompanionTheory.FrameTorus

variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]

def gens {l : ℕ} (e f : Fin l → V) (W : Submodule L V) : Set V :=
  Set.range e ∪ Set.range f ∪ (W : Set V)

theorem span_gens {h : V → V → L} {δ : L} {l : ℕ} {e f : Fin l → V} {W : Submodule L V}
    (hF : IsFrame h δ e f W) : Submodule.span L (gens e f W) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨a, b, w, hw, rfl⟩ := hF.2.2.2.2.2 x
  refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) (Submodule.subset_span (Or.inr hw))
  · exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Or.inl (Or.inl ⟨i, rfl⟩)))
  · exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Or.inl (Or.inr ⟨i, rfl⟩)))

theorem gens_induction {h : V → V → L} {δ : L} {l : ℕ} {e f : Fin l → V} {W : Submodule L V}
    (hF : IsFrame h δ e f W) {P : V → Prop} (hg : ∀ x ∈ gens e f W, P x) (h0 : P 0)
    (ha : ∀ x y, P x → P y → P (x + y)) (hm : ∀ (a : L) x, P x → P (a • x)) (x : V) : P x := by
  have hx : x ∈ Submodule.span L (gens e f W) := by
    rw [span_gens hF]
    trivial
  induction hx using Submodule.span_induction with
  | mem x h => exact hg x h
  | zero => exact h0
  | add x y _ _ hx hy => exact ha x y hx hy
  | smul a x _ hx => exact hm a x hx

def pair {s : L →+* L} {h : V → V → L} (hH : IsHerm s h) (x : V) : V →ₗ[L] L where
  toFun := h x
  map_add' := hH.1 x
  map_smul' a y := by simp [hH.2.1]

theorem add_left {s : L →+* L} {h : V → V → L} (hH : IsHerm s h) (x x' y : V) :
    h (x + x') y = h x y + h x' y := by
  rw [hH.2.2.1 y (x + x'), hH.1, map_add (f := _), ← hH.2.2.1, ← hH.2.2.1]

theorem smul_left {s : L →+* L} {h : V → V → L} (hH : IsHerm s h) (a : L) (x y : V) :
    h (a • x) y = s a * h x y := by
  rw [hH.2.2.1 y (a • x), hH.2.1, map_mul, ← hH.2.2.1]

def tor {s : L →+* L} {h : V → V → L} (hH : IsHerm s h) (δ : L) {l : ℕ} (e f : Fin l → V)
    (u : Fin l → L) : V →ₗ[L] V :=
  LinearMap.id + (∑ i, ((u i - 1) * (s δ)⁻¹) • (pair hH (f i)).smulRight (e i)) +
    ∑ i, (((s (u i))⁻¹ - 1) * δ⁻¹) • (pair hH (e i)).smulRight (f i)

theorem tor_apply {s : L →+* L} {h : V → V → L} (hH : IsHerm s h) (δ : L) {l : ℕ} (e f : Fin l → V)
    (u : Fin l → L) (x : V) :
    tor hH δ e f u x = x + (∑ i, ((u i - 1) * (s δ)⁻¹) • (h (f i) x • e i)) +
      ∑ i, (((s (u i))⁻¹ - 1) * δ⁻¹) • (h (e i) x • f i) := by
  simp [tor, pair, LinearMap.add_apply, LinearMap.sum_apply]

section Frame

variable {s : L →+* L} {h : V → V → L} {δ : L} {l : ℕ} {e f : Fin l → V} {W : Submodule L V}

theorem pair_fe (hH : IsHerm s h) (hF : IsFrame h δ e f W) (i j : Fin l) :
    h (f i) (e j) = if i = j then s δ else 0 := by
  rw [hH.2.2.1 (e j) (f i), hF.2.2.1 j i]
  by_cases hij : i = j
  · simp [hij]
  · simp [hij, Ne.symm hij]

theorem tor_e (hH : IsHerm s h) (hF : IsFrame h δ e f W) (hδ : δ ≠ 0) (u : Fin l → L) (j : Fin l) :
    tor hH δ e f u (e j) = u j • e j := by
  have hs : s δ ≠ 0 := (map_ne_zero s).2 hδ
  rw [tor_apply]
  simp only [pair_fe hH hF, hF.1, zero_smul, smul_zero, Finset.sum_const_zero, add_zero, ite_smul,
    smul_ite, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [smul_smul, mul_assoc, inv_mul_cancel₀ hs, mul_one, sub_smul, one_smul]
  abel

theorem tor_f (hH : IsHerm s h) (hF : IsFrame h δ e f W) (hδ : δ ≠ 0) (u : Fin l → L) (j : Fin l) :
    tor hH δ e f u (f j) = (s (u j))⁻¹ • f j := by
  rw [tor_apply]
  simp only [hF.2.1, hF.2.2.1, zero_smul, smul_zero, Finset.sum_const_zero, add_zero, ite_smul,
    smul_ite, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [smul_smul, mul_assoc, inv_mul_cancel₀ hδ, mul_one, sub_smul, one_smul]
  abel

theorem tor_w (hH : IsHerm s h) (hF : IsFrame h δ e f W) (u : Fin l → L) {w : V} (hw : w ∈ W) :
    tor hH δ e f u w = w := by
  rw [tor_apply]
  simp [(hF.2.2.2.1 w hw _).1, (hF.2.2.2.1 w hw _).2]

theorem tor_inv (hH : IsHerm s h) (hF : IsFrame h δ e f W) (hδ : δ ≠ 0) (u : Fin l → L)
    (hu : ∀ i, u i ≠ 0) :
    (tor hH δ e f u).comp (tor hH δ e f fun i => (u i)⁻¹) = LinearMap.id := by
  refine LinearMap.ext_on (span_gens hF) ?_
  rintro x ((⟨i, rfl⟩ | ⟨i, rfl⟩) | hx)
  · simp [tor_e hH hF hδ, hu i]
  · have : s (u i) ≠ 0 := (map_ne_zero s).2 (hu i)
    simp [tor_e hH hF hδ, tor_f hH hF hδ, this]
  · simp [tor_w hH hF _ hx]

theorem tor_iso_gens (hs : ∀ x, s (s x) = x) (hH : IsHerm s h) (hF : IsFrame h δ e f W) (hδ : δ ≠ 0)
    (u : Fin l → L) (hu : ∀ i, u i ≠ 0) {x y : V} (hx : x ∈ gens e f W) (hy : y ∈ gens e f W) :
    h (tor hH δ e f u x) (tor hH δ e f u y) = h x y := by
  have hsu : ∀ i, s (u i) ≠ 0 := fun i => (map_ne_zero s).2 (hu i)
  have hwe : ∀ {w : V}, w ∈ W → ∀ i, h w (e i) = 0 := fun hw i => by
    rw [hH.2.2.1 (e i) _, (hF.2.2.2.1 _ hw i).1, map_zero]
  have hwf : ∀ {w : V}, w ∈ W → ∀ i, h w (f i) = 0 := fun hw i => by
    rw [hH.2.2.1 (f i) _, (hF.2.2.2.1 _ hw i).2, map_zero]
  rcases hx with (⟨i, rfl⟩ | ⟨i, rfl⟩) | hx <;> rcases hy with (⟨j, rfl⟩ | ⟨j, rfl⟩) | hy
  · simp [tor_e hH hF hδ, smul_left hH, hH.2.1, hF.1]
  · rw [tor_e hH hF hδ, tor_f hH hF hδ, smul_left hH, hH.2.1, hF.2.2.1]
    by_cases hij : i = j
    · subst hij
      simp [hsu i]
    · simp [hij]
  · rw [tor_e hH hF hδ, tor_w hH hF u hy, smul_left hH, (hF.2.2.2.1 _ hy i).1, mul_zero]
  · rw [tor_f hH hF hδ, tor_e hH hF hδ, smul_left hH, hH.2.1, pair_fe hH hF]
    by_cases hij : i = j
    · subst hij
      simp [hs, hu i]
    · simp [hij]
  · simp [tor_f hH hF hδ, smul_left hH, hH.2.1, hF.2.1]
  · rw [tor_f hH hF hδ, tor_w hH hF u hy, smul_left hH, (hF.2.2.2.1 _ hy i).2, mul_zero]
  · rw [tor_w hH hF u hx, tor_e hH hF hδ, hH.2.1, hwe hx, mul_zero]
  · rw [tor_w hH hF u hx, tor_f hH hF hδ, hH.2.1, hwf hx, mul_zero]
  · rw [tor_w hH hF u hx, tor_w hH hF u hy]

theorem tor_iso (hs : ∀ x, s (s x) = x) (hH : IsHerm s h) (hF : IsFrame h δ e f W) (hδ : δ ≠ 0)
    (u : Fin l → L) (hu : ∀ i, u i ≠ 0) (x y : V) :
    h (tor hH δ e f u x) (tor hH δ e f u y) = h x y := by
  have hz : ∀ z, h z 0 = 0 := fun z => by simpa using hH.2.1 0 z 0
  have hz' : ∀ z, h 0 z = 0 := fun z => by simpa using smul_left hH 0 0 z
  have step : ∀ g ∈ gens e f W, ∀ y, h (tor hH δ e f u g) (tor hH δ e f u y) = h g y := by
    intro g hg
    refine gens_induction hF (fun y hy => tor_iso_gens hs hH hF hδ u hu hg hy) ?_ ?_ ?_
    · simp [hz]
    · intro y y' hy hy'
      simp only [map_add (f := _), hH.1, hy, hy']
    · intro a y hy
      simp only [map_smul, hH.2.1, hy]
  refine gens_induction hF (P := fun x => ∀ y, h (tor hH δ e f u x) (tor hH δ e f u y) = h x y)
    step ?_ ?_ ?_ x y
  · simp [hz']
  · intro x x' hx hx' y
    rw [map_add (f := _), add_left hH, hx, hx', add_left hH]
  · intro a x hx y
    simp only [map_smul, smul_left hH, hx]

end Frame

theorem stTor : StTor := by
  unfold StTor ForAll
  intro L _ _ _ _ s hs δ hδ V _ _ _ h hH l e f W hF u hu
  have hδ0 : δ ≠ 0 := hδ.1
  have hui : ∀ i, (u i)⁻¹ ≠ 0 := fun i => inv_ne_zero (hu i)
  let t : V ≃ₗ[L] V := LinearEquiv.ofLinear (tor hH δ e f u) (tor hH δ e f fun i => (u i)⁻¹)
    (tor_inv hH hF hδ0 u hu)
    (by simpa using tor_inv hH hF hδ0 (fun i => (u i)⁻¹) hui)
  refine ⟨t, fun x y => tor_iso hs.1 hH hF hδ0 u hu x y, ⟨fun i => tor_e hH hF hδ0 u i,
    fun i => tor_f hH hF hδ0 u i, fun w hw => tor_w hH hF u hw⟩, ?_⟩
  rintro t' ⟨h1, h2, h3⟩
  apply LinearEquiv.toLinearMap_injective
  refine LinearMap.ext_on (span_gens hF) ?_
  rintro x ((⟨i, rfl⟩ | ⟨i, rfl⟩) | hx)
  · exact (h1 i).trans (tor_e hH hF hδ0 u i).symm
  · exact (h2 i).trans (tor_f hH hF hδ0 u i).symm
  · exact (h3 x hx).trans (tor_w hH hF u hx).symm

end GlobalTheory.CompanionTheory.FrameTorus

end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TorusStatementStatement
open CompanionTheory.Rg.FlB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.TorusStatement : StTor := by
  first | exact @GlobalTheory.CompanionTheory.FrameTorus.stTor | exact GlobalTheory.CompanionTheory.FrameTorus.stTor | (intros; apply GlobalTheory.CompanionTheory.FrameTorus.stTor <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.PairingOfSandwichStatement
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.PairingOfSandwichStatement
open CompanionTheory.Rg.FlB

noncomputable section

namespace GlobalTheory.CompanionTheory.HermLat

section Lat

variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]

theorem smul_mem_of_isLat {Λ : AddSubgroup V} (hΛ : IsLat L Λ) {a : L} (ha : ‖a‖ ≤ 1) {x : V}
    (hx : x ∈ Λ) : a • x ∈ Λ := by
  obtain ⟨m, b, hb⟩ := hΛ
  rw [hb] at hx ⊢
  intro i
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, norm_mul]
  exact mul_le_one₀ ha (norm_nonneg _) (hx i)

theorem exists_smul_mem_of_isLat {Λ : AddSubgroup V} (hΛ : IsLat L Λ) (v : V) :
    ∃ a : L, a ≠ 0 ∧ a • v ∈ Λ := by
  obtain ⟨m, b, hb⟩ := hΛ
  have hS0 : 0 ≤ ∑ i, ‖b.repr v i‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  obtain ⟨a, ha0, ha⟩ := NormedField.exists_norm_lt L
    (show (0 : ℝ) < 1 / (1 + ∑ i, ‖b.repr v i‖) by positivity)
  refine ⟨a, norm_pos_iff.mp ha0, (hb _).2 fun i => ?_⟩
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, norm_mul]
  have h1 : ‖b.repr v i‖ ≤ 1 + ∑ i, ‖b.repr v i‖ := by
    have := Finset.single_le_sum (f := fun i => ‖b.repr v i‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ i)
    linarith
  calc ‖a‖ * ‖b.repr v i‖ ≤ (1 / (1 + ∑ i, ‖b.repr v i‖)) * (1 + ∑ i, ‖b.repr v i‖) := by
        gcongr
    _ = 1 := by field_simp


variable (L) in
def adjoin [IsUltrametricDist L] (Λ : AddSubgroup V) (v : V) : AddSubgroup V where
  carrier := {z | ∃ l ∈ Λ, ∃ a : L, ‖a‖ ≤ 1 ∧ z = l + a • v}
  add_mem' := by
    rintro _ _ ⟨l, hl, a, ha, rfl⟩ ⟨l', hl', a', ha', rfl⟩
    refine ⟨l + l', Λ.add_mem hl hl', a + a',
      (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha ha'), ?_⟩
    rw [add_smul]
    abel
  zero_mem' := ⟨0, Λ.zero_mem, 0, by simp, by simp⟩
  neg_mem' := by
    rintro _ ⟨l, hl, a, ha, rfl⟩
    refine ⟨-l, Λ.neg_mem hl, -a, by simpa using ha, ?_⟩
    rw [neg_smul]
    abel

end Lat

section Herm

variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]
  {s : L →+* L} {h : V → V → L}

theorem herm_add_left (hh : IsHerm s h) (x y z : V) : h (x + y) z = h x z + h y z := by
  rw [hh.2.2.1 z (x + y), hh.1, map_add (f := _), ← hh.2.2.1, ← hh.2.2.1]

theorem herm_smul_left (hh : IsHerm s h) (a : L) (x y : V) : h (a • x) y = s a * h x y := by
  rw [hh.2.2.1 y (a • x), hh.2.1, map_mul, ← hh.2.2.1]

theorem herm_add_add (hh : IsHerm s h) (u v : V) :
    h (u + v) (u + v) = h u u + (h u v + s (h u v)) + h v v := by
  rw [herm_add_left hh, hh.1, hh.1, ← hh.2.2.1 u v]
  ring

end Herm

section Main

variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {V : Type} [AddCommGroup V]
  [Module L V] {s : L →+* L} {δ : L} {h : V → V → L}

theorem norm_sub_le_of_le {a b : L} {c : ℝ} (ha : ‖a‖ ≤ c) (hb : ‖b‖ ≤ c) : ‖a - b‖ ≤ c := by
  rw [sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha (by simpa using hb))

theorem pairing_le (hδ : IsDelta s δ) (hh : IsHerm s h) {Λ : AddSubgroup V}
    (hL : IsLat L Λ) (hint : ∀ x ∈ Λ, ‖h x x‖ ≤ 1) {x y : V} (hx : x ∈ Λ) (hy : y ∈ Λ) :
    ‖h x y‖ ≤ ‖δ‖ := by
  refine (hδ.2.1 _).1 fun t ht => ?_
  have hty : t • y ∈ Λ := smul_mem_of_isLat hL ht hy
  have e := herm_add_add hh x (t • y)
  have e' : h x y * t + s (h x y * t) =
      h (x + t • y) (x + t • y) - h x x - h (t • y) (t • y) := by
    rw [e, hh.2.1 t x y, mul_comm t]
    ring
  rw [e']
  exact norm_sub_le_of_le (norm_sub_le_of_le (hint _ (Λ.add_mem hx hty)) (hint _ hx)) (hint _ hty)

theorem adjoin_integral (hs : IsInv s) (hδ : IsDelta s δ) (hh : IsHerm s h) {Λ : AddSubgroup V}
    (hint : ∀ x ∈ Λ, ‖h x x‖ ≤ 1) {p : L} (hp0 : p ≠ 0) {x : V}
    (hq : ‖h x x‖ ≤ ‖p‖ ^ 2) (hsmall : ∀ y ∈ Λ, ‖h x y‖ ≤ ‖p‖ * ‖δ‖) :
    ∀ z ∈ adjoin (L := L) Λ (p⁻¹ • x), ‖h z z‖ ≤ 1 := by
  rintro _ ⟨l, hl, a, ha, rfl⟩
  have hpn : 0 < ‖p‖ := norm_pos_iff.mpr hp0
  rw [herm_add_add hh]
  have hb : ‖h l (a • p⁻¹ • x)‖ ≤ ‖δ‖ := by
    rw [hh.2.1, hh.2.1, hh.2.2.1 x l, norm_mul, norm_mul, norm_inv, hs.2.1]
    have h1 := hsmall l hl
    calc ‖a‖ * (‖p‖⁻¹ * ‖h x l‖) ≤ 1 * (‖p‖⁻¹ * (‖p‖ * ‖δ‖)) := by gcongr
      _ = ‖δ‖ := by field_simp
  have htr : ‖h l (a • p⁻¹ • x) + s (h l (a • p⁻¹ • x))‖ ≤ 1 := by
    have := (hδ.2.1 _).2 hb 1 (by simp)
    simpa using this
  have hlast : ‖h (a • p⁻¹ • x) (a • p⁻¹ • x)‖ ≤ 1 := by
    rw [herm_smul_left hh, herm_smul_left hh, hh.2.1, hh.2.1, norm_mul, norm_mul, norm_mul,
      norm_mul, hs.2.1, hs.2.1, norm_inv]
    have hpp : ‖p‖⁻¹ * (‖p‖⁻¹ * ‖p‖ ^ 2) = 1 := by field_simp
    calc ‖a‖ * (‖p‖⁻¹ * (‖a‖ * (‖p‖⁻¹ * ‖h x x‖)))
        ≤ 1 * (‖p‖⁻¹ * (1 * (‖p‖⁻¹ * ‖p‖ ^ 2))) := by gcongr
      _ = 1 := by rw [one_mul, one_mul, hpp]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le
    ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hint l hl) htr)) hlast)

theorem pairing_of_sandwich : StSandwich → StPairing := by
  intro hS L _ _ _ _ s hs δ hδ V _ _ _ h hh Λ hΛ
  obtain ⟨hL, hint, hmax⟩ := hΛ
  refine ⟨fun x hx y hy => pairing_le hδ hh hL hint hx hy, ?_⟩
  intro p hp hunif x hx hxp hq
  have hp0 : p ≠ 0 := by
    rintro rfl
    obtain ⟨a, ha0, ha⟩ := NormedField.exists_norm_lt L (show (0 : ℝ) < 1 by norm_num)
    have := hunif a ha
    rw [norm_zero] at this
    linarith
  have hδ0 : δ ≠ 0 := hδ.1
  have hδn : 0 < ‖δ‖ := norm_pos_iff.mpr hδ0
  by_cases hex : ∃ y ∈ Λ, ‖h x y‖ = ‖δ‖
  · obtain ⟨y, hy, hyn⟩ := hex
    have hne : h x y ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hyn
      exact hδ0 (norm_eq_zero.mp hyn.symm)
    refine ⟨(δ / h x y) • y, smul_mem_of_isLat hL ?_ hy, ?_⟩
    · rw [norm_div, hyn, div_self hδn.ne']
    · rw [hh.2.1]
      field_simp
  · exfalso
    have hsmall : ∀ y ∈ Λ, ‖h x y‖ ≤ ‖p‖ * ‖δ‖ := by
      intro y hy
      have hlt : ‖h x y‖ < ‖δ‖ :=
        lt_of_le_of_ne (pairing_le hδ hh hL hint hx hy) fun e => hex ⟨y, hy, e⟩
      have h2 : ‖h x y / δ‖ < 1 := by
        rw [norm_div, div_lt_one hδn]
        exact hlt
      have h3 := hunif _ h2
      rw [norm_div, div_le_iff₀ hδn] at h3
      exact h3
    have hle : Λ ≤ adjoin (L := L) Λ (p⁻¹ • x) := fun l hl => ⟨l, hl, 0, by simp, by simp⟩
    have hL' : IsLat L (adjoin (L := L) Λ (p⁻¹ • x)) := by
      refine hS L V Λ _ p hL hp0 ?_ ?_ ?_
      · rintro _ ⟨l, hl, a, ha, rfl⟩
        have e : p • (l + a • p⁻¹ • x) = p • l + a • x := by
          rw [smul_add, smul_comm p a, smul_smul p, mul_inv_cancel₀ hp0, one_smul]
        rw [e]
        exact Λ.add_mem (smul_mem_of_isLat hL hp.le hl) (smul_mem_of_isLat hL ha hx)
      · intro v
        obtain ⟨a, ha, hav⟩ := exists_smul_mem_of_isLat hL v
        exact ⟨a, ha, hle hav⟩
      · rintro b hb _ ⟨l, hl, a, ha, rfl⟩
        refine ⟨b • l, smul_mem_of_isLat hL hb hl, b * a, ?_, ?_⟩
        · rw [norm_mul]
          exact mul_le_one₀ hb (norm_nonneg _) ha
        · rw [smul_add, smul_smul]
    have heq := hmax _ hL' (adjoin_integral hs hδ hh hint hp0 hq hsmall) hle
    apply hxp
    rw [← heq]
    exact ⟨0, Λ.zero_mem, 1, by simp, by simp⟩

end Main

end GlobalTheory.CompanionTheory.HermLat

end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.PairingOfSandwichStatementStatement
open CompanionTheory.Rg.FlB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairing_of_sandwich_statement : StSandwich → StPairing := by
  first | exact @GlobalTheory.CompanionTheory.HermLat.pairing_of_sandwich | exact GlobalTheory.CompanionTheory.HermLat.pairing_of_sandwich | (intros; apply GlobalTheory.CompanionTheory.HermLat.pairing_of_sandwich <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.AnisotropicOfHenselAndSandwich
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.AnisotropicOfHenselAndSandwich
open CompanionTheory.Rg.FlB

noncomputable section

namespace GlobalTheory.CompanionTheory.HermAniso

section Core

variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]
  {s : L →+* L} {h : V → V → L}

lemma add_left (hh : IsHerm s h) (x y z : V) : h (x + y) z = h x z + h y z := by
  have h1 := hh.2.2.1
  rw [h1 z (x + y), hh.1, map_add (f := _), h1 z x, h1 z y]

lemma smul_left (hh : IsHerm s h) (a : L) (x y : V) : h (a • x) y = s a * h x y := by
  have h1 := hh.2.2.1
  rw [h1 y (a • x), hh.2.1, map_mul, h1 y x]

lemma q_add (hh : IsHerm s h) (x y : V) :
    h (x + y) (x + y) = h x x + h y y + (h x y + h y x) := by
  rw [add_left hh, hh.1, hh.1]; ring

lemma norm_q_smul (hs : IsInv s) (hh : IsHerm s h) (a : L) (x : V) :
    ‖h (a • x) (a • x)‖ = ‖a‖ * ‖a‖ * ‖h x x‖ := by
  rw [smul_left hh, hh.2.1, norm_mul, norm_mul, hs.2.1]; ring

lemma pair_le [IsUltrametricDist L] [CompleteSpace L] (hH : StHensel) (hs : IsInv s) (hh : IsHerm s h)
    (hani : ∀ x, h x x = 0 → x = 0) {x y : V} (hx : ‖h x x‖ ≤ 1) (hy : ‖h y y‖ ≤ 1) :
    ‖h x y + h y x‖ ≤ 1 := by
  have h1 := hh.2.2.1
  by_contra hb
  push_neg at hb
  obtain ⟨b, hbd⟩ : ∃ b, b = h x y + h y x := ⟨_, rfl⟩
  rw [← hbd] at hb
  have hbpos : 0 < ‖b‖ := by linarith
  have hb0 : b ≠ 0 := norm_pos_iff.mp hbpos
  have hsb : s b = b := by
    rw [hbd, map_add (f := _), ← h1 x y, ← h1 y x, add_comm]
  have hsx : s (h x x) = h x x := (h1 x x).symm
  have hsy : s (h y y) = h y y := (h1 y y).symm
  have hc1 : s (h y y / b ^ 2) = h y y / b ^ 2 := by
    rw [map_div₀, map_pow, hsb, hsy]
  have hc2 : ‖h y y / b ^ 2‖ < 1 := by
    rw [norm_div, norm_pow, div_lt_one (by positivity)]
    nlinarith
  obtain ⟨u, hsu, hu, he⟩ := hH L s hs (h y y / b ^ 2) (h x x) hc1 hsx hc2 hx
  obtain ⟨t, htd⟩ : ∃ t, t = u / b := ⟨_, rfl⟩
  have hst : s t = t := by rw [htd, map_div₀, hsu, hsb]
  have hq : h (x + t • y) (x + t • y) = 0 := by
    rw [q_add hh, smul_left hh, hh.2.1, hh.2.1, smul_left hh, hst]
    have e1 : t * (t * h y y) + t * h x y + t * h y x = t * b + t ^ 2 * h y y := by
      rw [hbd]; ring
    have e2 : t * b = u := by rw [htd]; field_simp
    have e3 : t ^ 2 * h y y = h y y / b ^ 2 * u ^ 2 := by rw [htd]; field_simp
    linear_combination he + e1 + e2 + e3
  have hz := hani _ hq
  have hxe : x = (-t) • y := by
    rw [neg_smul]; exact eq_neg_of_add_eq_zero_left hz
  have hxy : h x y = -t * h y y := by
    have : h x y = h ((-t) • y) y := congrArg (fun z => h z y) hxe
    rw [this, smul_left hh, map_neg, hst]
  have hyx : h y x = -t * h y y := by
    have : h y x = h y ((-t) • y) := congrArg (fun z => h y z) hxe
    rw [this, hh.2.1]
  have ht : ‖t‖ < 1 := by
    rw [htd, norm_div, div_lt_one hbpos]; linarith
  have hle : ‖-t * h y y‖ < 1 := by
    rw [norm_mul, norm_neg]
    nlinarith [norm_nonneg t, norm_nonneg (h y y)]
  have : ‖b‖ < 1 := by
    rw [hbd, hxy, hyx]
    exact lt_of_le_of_lt ((IsUltrametricDist.norm_add_le_max _ _).trans (by simp)) hle
  linarith

lemma exists_ball [IsUltrametricDist L] (hs : IsInv s) (hh : IsHerm s h)
    (hp : ∀ x y : V, ‖h x x‖ ≤ 1 → ‖h y y‖ ≤ 1 → ‖h x y + h y x‖ ≤ 1) :
    ∃ V₀ : AddSubgroup V, ∀ x, x ∈ V₀ ↔ ‖h x x‖ ≤ 1 := by
  refine ⟨{ carrier := {x | ‖h x x‖ ≤ 1}, add_mem' := ?_, zero_mem' := ?_, neg_mem' := ?_ }, fun x => Iff.rfl⟩
  · intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [q_add hh]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (hp a b ha hb))
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  · have := hh.2.1 (0 : L) (0 : V) (0 : V)
    simp only [zero_smul, zero_mul] at this
    simp [this]
  · intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    have := norm_q_smul hs hh (-1 : L) a
    simp only [neg_smul, one_smul, norm_neg, norm_one, one_mul] at this
    rwa [this]

lemma coord_comb [FiniteDimensional L V] (hh : IsHerm s h) {m : ℕ} (b : Module.Basis (Fin m) L V) :
    ∃ M : Fin m → Fin m → L, ∀ x i, b.repr x i = ∑ j, M i j * h (b j) x := by
  have h1 := hh.2.2.1
  let φ : V →ₗ[L] (Fin m → L) :=
    { toFun := fun x j => h (b j) x
      map_add' := fun x y => by ext j; simp [hh.1]
      map_smul' := fun a x => by ext j; simp [hh.2.1] }
  have hker : LinearMap.ker φ = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    let ℓ : V →ₗ[L] L :=
      { toFun := fun y => h x y
        map_add' := fun y z => hh.1 x y z
        map_smul' := fun a y => by simp [hh.2.1] }
    have hl : ℓ = 0 := by
      refine b.ext fun j => ?_
      have : h (b j) x = 0 := congrFun hx j
      change h x (b j) = 0
      rw [h1 (b j) x, this, map_zero]
    exact hh.2.2.2 x fun y => LinearMap.congr_fun hl y
  obtain ⟨ψ, hψ⟩ := φ.exists_leftInverse_of_injective hker
  refine ⟨fun i j => ((b.coord i) ∘ₗ ψ) (fun k => if j = k then 1 else 0), fun x i => ?_⟩
  have e : ψ (φ x) = x := LinearMap.congr_fun hψ x
  have := LinearMap.pi_apply_eq_sum_univ ((b.coord i) ∘ₗ ψ) (φ x)
  simp only [LinearMap.comp_apply, Module.Basis.coord_apply, smul_eq_mul, e] at this
  rw [this]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]
  rfl

end Core

theorem aniso : StHensel → StSandwich → StAniso := by
  intro hH hS
  unfold StAniso ForAll
  intro L _ _ _ _ s hs δ hδ V _ _ _ h hh hani Λ hΛ x
  have h1 := hh.2.2.1
  have hp : ∀ x y : V, ‖h x x‖ ≤ 1 → ‖h y y‖ ≤ 1 → ‖h x y + h y x‖ ≤ 1 :=
    fun x y hx hy => pair_le hH hs hh hani hx hy
  obtain ⟨V₀, hV₀⟩ := exists_ball hs hh hp
  have hsmul : ∀ a : L, ‖a‖ ≤ 1 → ∀ x ∈ V₀, a • x ∈ V₀ := by
    intro a ha x hx
    rw [hV₀] at hx ⊢
    rw [norm_q_smul hs hh]
    have := norm_nonneg a
    have h2 := norm_nonneg (h x x)
    calc ‖a‖ * ‖a‖ * ‖h x x‖ ≤ 1 * 1 * 1 := by gcongr
      _ = 1 := by norm_num
  have hδle : ∀ x ∈ V₀, ∀ y ∈ V₀, ‖h x y‖ ≤ ‖δ‖ := by
    intro x hx y hy
    refine (hδ.2.1 (h x y)).mp fun a ha => ?_
    have hay := hsmul a ha y hy
    have := hp x (a • y) ((hV₀ x).mp hx) ((hV₀ _).mp hay)
    rw [h1 x (a • y), hh.2.1] at this
    rwa [mul_comm]
  have hle : Λ ≤ V₀ := fun y hy => (hV₀ y).mpr (hΛ.2.1 y hy)
  obtain ⟨m, b, hb⟩ := hΛ.1
  have hbΛ : ∀ j, b j ∈ Λ := by
    intro j
    rw [hb]
    intro i
    rw [Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs <;> simp
  obtain ⟨M, hM⟩ := coord_comb hh b
  obtain ⟨C, hC0, hC⟩ : ∃ C : ℝ, 0 < C ∧ ∀ x ∈ V₀, ∀ i, ‖b.repr x i‖ ≤ C := by
    refine ⟨∑ i, ∑ j, ‖M i j‖ * ‖δ‖ + 1, ?_, fun x hx i => ?_⟩
    · have : 0 ≤ ∑ i, ∑ j, ‖M i j‖ * ‖δ‖ :=
        Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity
      linarith
    · have e1 : ‖b.repr x i‖ ≤ ∑ j, ‖M i j‖ * ‖δ‖ := by
        rw [hM]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hδle _ (hle (hbΛ j)) x hx) (norm_nonneg _)
      have e2 : ∑ j, ‖M i j‖ * ‖δ‖ ≤ ∑ i, ∑ j, ‖M i j‖ * ‖δ‖ :=
        Finset.single_le_sum (f := fun i => ∑ j, ‖M i j‖ * ‖δ‖)
          (fun i _ => Finset.sum_nonneg fun j _ => by positivity) (Finset.mem_univ i)
      linarith
  obtain ⟨c, hc0, hc1⟩ := NormedField.exists_norm_lt L (inv_pos.mpr hC0)
  have hcne : c ≠ 0 := norm_pos_iff.mp hc0
  have hbound : ∀ x ∈ V₀, c • x ∈ Λ := by
    intro x hx
    rw [hb]
    intro i
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul, norm_mul]
    have e := hC x hx i
    have e2 : ‖c‖ * C ≤ 1 := by
      have := mul_le_mul_of_nonneg_right hc1.le hC0.le
      rwa [inv_mul_cancel₀ hC0.ne'] at this
    calc ‖c‖ * ‖b.repr x i‖ ≤ ‖c‖ * C := mul_le_mul_of_nonneg_left e hc0.le
      _ ≤ 1 := e2
  have hab : ∀ x : V, ∃ a : L, a ≠ 0 ∧ a • x ∈ V₀ := by
    intro x
    have hpos : (0 : ℝ) < (1 + ‖h x x‖)⁻¹ := by positivity
    obtain ⟨a, ha0, ha1⟩ := NormedField.exists_norm_lt L hpos
    refine ⟨a, norm_pos_iff.mp ha0, ?_⟩
    rw [hV₀, norm_q_smul hs hh]
    have hq := norm_nonneg (h x x)
    have e1 : ‖a‖ * (1 + ‖h x x‖) ≤ 1 := by
      have := mul_le_mul_of_nonneg_right ha1.le (by positivity : (0 : ℝ) ≤ 1 + ‖h x x‖)
      rwa [inv_mul_cancel₀ (by positivity)] at this
    have e2 : ‖a‖ ≤ 1 := by nlinarith
    have e3 : ‖a‖ * ‖h x x‖ ≤ 1 := by nlinarith
    calc ‖a‖ * ‖a‖ * ‖h x x‖ = ‖a‖ * (‖a‖ * ‖h x x‖) := by ring
      _ ≤ 1 * 1 := by gcongr
      _ = 1 := by norm_num
  have hlat : IsLat L V₀ :=
    hS L V Λ V₀ c ⟨m, b, hb⟩ hcne hbound hab hsmul
  have heq : V₀ = Λ := hΛ.2.2 V₀ hlat (fun x hx => (hV₀ x).mp hx) hle
  rw [← heq]
  exact hV₀ x

end GlobalTheory.CompanionTheory.HermAniso

end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.AnisotropicOfHenselAndSandwichStatement
open CompanionTheory.Rg.FlB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.anisotropic_of_hensel_and_sandwich : StHensel → StSandwich → StAniso := by
  first | exact @GlobalTheory.CompanionTheory.HermAniso.aniso | exact GlobalTheory.CompanionTheory.HermAniso.aniso | (intros; apply GlobalTheory.CompanionTheory.HermAniso.aniso <;> assumption)
end
end
