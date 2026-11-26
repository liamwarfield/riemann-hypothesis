module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalBasic

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ExponentTerms
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise

noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms
open GlobalTheory.SplitWeil GlobalTheory.RootEx

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Lattices
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def MapsInto (x : Matrix κ ι k) (M' : Submodule 𝒪[k] (ι → k)) (M : Submodule 𝒪[k] (κ → k)) : Prop :=
  ∀ v ∈ M', x *ᵥ v ∈ M

def InjMod (ϖ : 𝒪[k]) (x : Matrix κ ι k) (M' : Submodule 𝒪[k] (ι → k)) (M : Submodule 𝒪[k] (κ → k)) : Prop :=
  MapsInto x M' M ∧ ∀ v ∈ M', x *ᵥ v ∈ ϖ • M → v ∈ ϖ • M'

def act (g : GL ι k) (M : Submodule 𝒪[k] (ι → k)) : Submodule 𝒪[k] (ι → k) :=
  M.map ((Matrix.mulVecLin g.val).restrictScalars 𝒪[k])

def stdLat (k : Type) [Field k] [ValuativeRel k] (ι : Type) : Submodule 𝒪[k] (ι → k) :=
  Submodule.pi Set.univ fun _ => (1 : Submodule 𝒪[k] k)

def IsReps (ϖ : 𝒪[k]) (M : Submodule 𝒪[k] (ι → k)) (T : Finset (ι → k)) : Prop :=
  (∀ t ∈ T, t ∈ M) ∧ ∀ v ∈ M, ∃! t, t ∈ T ∧ v - t ∈ ϖ • M

def SuppIn (Ψ : Matrix κ ι k → ℂ) (M' : Submodule 𝒪[k] (ι → k)) (M : Submodule 𝒪[k] (κ → k)) : Prop :=
  ∀ x, Ψ x ≠ 0 → MapsInto x M' M

def PeriodicMod (ϖ : 𝒪[k]) (Ψ : Matrix κ ι k → ℂ) (M' : Submodule 𝒪[k] (ι → k))
    (M : Submodule 𝒪[k] (κ → k)) : Prop :=
  ∀ x y, MapsInto y M' M → Ψ (x + (ϖ : k) • y) = Ψ x

end Lattices

section Chain
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

def aux (k : Type) [Field k] (n : Type) [DecidableEq n] {c : ℕ} (i : Fin c) : n ⊕ Fin c → k :=
  Pi.single (Sum.inr i) 1

def inX (k : Type) [Field k] [ValuativeRel k] (n : Type) (c : ℕ) : (n → k) →ₗ[𝒪[k]] (n ⊕ Fin c → k) where
  toFun v := Sum.elim v 0
  map_add' v w := by ext (r | r) <;> simp
  map_smul' a v := by ext (r | r) <;> simp

def chainLat (ϖ : 𝒪[k]) (c : ℕ) (L : Submodule 𝒪[k] (n → k)) : Submodule 𝒪[k] (n ⊕ Fin c → k) :=
  L.map (inX k n c) ⊔
    Submodule.span 𝒪[k] (Set.range fun i : Fin c => (ϖ : k) ^ (i.val + 1) • aux k n i)

def Yle (k : Type) [Field k] [ValuativeRel k] (n : Type) (c i : ℕ) : Submodule 𝒪[k] (n ⊕ Fin c → k) where
  carrier := {v | ∀ l : Fin c, i < l.val + 1 → v (Sum.inr l) = 0}
  add_mem' hv hw l hl := by simp [hv l hl, hw l hl]
  zero_mem' l _ := rfl
  smul_mem' a v hv l hl := by simp [hv l hl]

def pt (x₀ : Matrix n n' k) (y : Fin c → (n ⊕ Fin c → k)) : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k :=
  basePt c x₀ + Matrix.of fun r s =>
    Sum.elim (fun _ => 0) (fun j : Fin (c + 1) => Fin.cases 0 (fun i => y i r) j) s

def expo (c d : ℕ) : ℕ := ∑ i ∈ Finset.Icc 1 c, (i * d + i * (i - 1) / 2)

variable [MeasurableSpace k] [BorelSpace k]

def OneClass (ϖ : 𝒪[k]) (ψ : AddChar k Circle) (ν : Measure k) (n : Type) [Fintype n] [DecidableEq n]
    (hc : 1 ≤ c) (L' : Submodule 𝒪[k] (n' → k)) : Prop :=
  ∀ (Λ : Submodule 𝒪[k] (n ⊕ Fin c → k)), Submodule.IsLattice k Λ →
    ∀ Ψ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k),
      SuppIn Ψ (chainLat ϖ (c + 1) L') Λ → PeriodicMod ϖ Ψ (chainLat ϖ (c + 1) L') Λ →
      opE ψ ν 1 Ψ ≠ 0 →
        (∀ i : Fin c, (Λ ⊓ Yle k n c (i.val + 1)).map (LinearMap.proj (Sum.inr i)) =
          Submodule.span 𝒪[k] {(ϖ : k) ^ (i.val + 1)}) ∧
        (ϖ : k) • aux k n (⟨0, hc⟩ : Fin c) ∈ Λ ∧
        (∃ u ∈ N k n c 1, act u Λ = chainLat ϖ c (Λ.comap (inX k n c))) ∧
        ∃ r ∈ R k n c 1, Λ = act r (chainLat ϖ c (stdLat k n))

def OneCoset (ϖ : 𝒪[k]) (ψ : AddChar k Circle) (ν : Measure k) (n : Type) [Fintype n] [DecidableEq n]
    (c : ℕ) (L' : Submodule 𝒪[k] (n' → k)) : Prop :=
  (∀ (μ : kˣ →* ℂˣ), ∀ Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k),
      SuppIn Φ (chainLat ϖ (c + 1) L') (chainLat ϖ c (stdLat k n)) →
      PeriodicMod ϖ Φ (chainLat ϖ (c + 1) L') (chainLat ϖ c (stdLat k n)) →
      ∀ (h' : GL (n' ⊕ Fin (c + 1)) k) (h : GL (n ⊕ Fin c) k),
        act h' (chainLat ϖ (c + 1) L') = chainLat ϖ (c + 1) L' →
        opE ψ ν 1 (om μ h' h Φ) ≠ 0 →
          ∃ r ∈ R k n c 1, ∃ t : GL (n ⊕ Fin c) k,
            act t (chainLat ϖ c (stdLat k n)) = chainLat ϖ c (stdLat k n) ∧ h = r * t) ∧
  ∀ J : Subgroup (GL (n ⊕ Fin c) k),
    (∀ j ∈ J, act j (chainLat ϖ c (stdLat k n)) = chainLat ϖ c (stdLat k n)) →
    (∀ j : GL (n ⊕ Fin c) k, act j (chainLat ϖ c (stdLat k n)) = chainLat ϖ c (stdLat k n) →
      MapsInto (j.val - 1) (chainLat ϖ c (stdLat k n)) (ϖ • chainLat ϖ c (stdLat k n)) → j ∈ J) →
    ∃ T : Finset (GL (n ⊕ Fin c) k),
      (∀ t ∈ T, act t (chainLat ϖ c (stdLat k n)) = chainLat ϖ c (stdLat k n)) ∧
      ∀ h : GL (n ⊕ Fin c) k,
        (∃ r ∈ R k n c 1, ∃ t : GL (n ⊕ Fin c) k,
            act t (chainLat ϖ c (stdLat k n)) = chainLat ϖ c (stdLat k n) ∧ h = r * t) ↔
          ∃ r ∈ R k n c 1, ∃ t ∈ T, ∃ j ∈ J, h = r * t * j

end Chain

end GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms
end
end

open MeasureTheory ValuativeRel Matrix
open scoped Pointwise

noncomputable section
namespace GlobalTheory.RootEx.UnfoldShape
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms

variable {k : Type} [Field k] [ValuativeRel k]

section
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem _root_.GlobalTheory.RootEx.UnfoldShape.mem_act {g : GL ι k} {M : Submodule 𝒪[k] (ι → k)} {v : ι → k} :
    v ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.act g M ↔ ∃ w ∈ M, g.val *ᵥ w = v := by
  simp [_root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.act]

theorem _root_.GlobalTheory.RootEx.UnfoldShape.mem_act_iff_inv {g : GL ι k} {M : Submodule 𝒪[k] (ι → k)} {v : ι → k} :
    v ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.act g M ↔ (g⁻¹).val *ᵥ v ∈ M := by
  rw [_root_.GlobalTheory.RootEx.UnfoldShape.mem_act]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rwa [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  · intro hv
    refine ⟨_, hv, ?_⟩
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

theorem _root_.GlobalTheory.RootEx.UnfoldShape.act_one (M : Submodule 𝒪[k] (ι → k)) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.act (1 : GL ι k) M = M := by
  ext v
  simp [_root_.GlobalTheory.RootEx.UnfoldShape.mem_act_iff_inv]

theorem _root_.GlobalTheory.RootEx.UnfoldShape.act_mul (g h : GL ι k) (M : Submodule 𝒪[k] (ι → k)) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.act (g * h) M = _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.act g (_root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.act h M) := by
  ext v
  simp only [_root_.GlobalTheory.RootEx.UnfoldShape.mem_act_iff_inv, _root_.mul_inv_rev, Units.val_mul, Matrix.mulVec_mulVec]

omit [Fintype ι] [DecidableEq ι] in
theorem _root_.GlobalTheory.RootEx.UnfoldShape.mem_smul_iff {ϖ : 𝒪[k]} {M : Submodule 𝒪[k] (ι → k)} {v : ι → k} :
    v ∈ ϖ • M ↔ ∃ w ∈ M, (ϖ : k) • w = v := by
  rw [Submodule.mem_smul_pointwise_iff_exists]
  rfl

omit [Fintype ι] [DecidableEq ι] in
theorem _root_.GlobalTheory.RootEx.UnfoldShape.mem_stdLat {v : ι → k} :
    v ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.stdLat k ι ↔ ∀ i, v i ∈ 𝒪[k] := by
  simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.stdLat, Submodule.mem_pi, Set.mem_univ, true_implies,
    Submodule.mem_one]
  refine forall_congr' fun i => ⟨?_, fun h => ⟨⟨v i, h⟩, rfl⟩⟩
  rintro ⟨a, ha⟩
  rw [← ha]
  exact a.2

end

variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

omit [Fintype n] [DecidableEq n] in
theorem inX_apply (v : n → k) : inX k n c v = Sum.elim v 0 := rfl

omit [Fintype n] [DecidableEq n] in
theorem mem_Yle {i : ℕ} {v : n ⊕ Fin c → k} :
    v ∈ Yle k n c i ↔ ∀ l : Fin c, i < l.val + 1 → v (Sum.inr l) = 0 := Iff.rfl

omit [Fintype n] in
theorem _root_.GlobalTheory.RootEx.UnfoldShape.mem_chainLat {ϖ : 𝒪[k]} {L : Submodule 𝒪[k] (n → k)} {v : n ⊕ Fin c → k} :
    v ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.chainLat ϖ c L ↔
      (fun r => v (Sum.inl r)) ∈ L ∧ ∀ i : Fin c, ∃ a : 𝒪[k], v (Sum.inr i) = a * (ϖ : k) ^ (i.val + 1) := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.chainLat
  rw [Submodule.mem_sup]
  constructor
  · rintro ⟨y, hy, z, hz, rfl⟩
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hy
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hz
    refine ⟨?_, fun i => ⟨a i, ?_⟩⟩
    · simpa [_root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.inX, _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.aux, Finset.sum_apply,
        Pi.single_apply] using hw
    · simp [_root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.inX, _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.aux, Finset.sum_apply,
        Pi.single_apply, Subring.smul_def]
  · rintro ⟨hL, ha⟩
    choose a ha using ha
    refine ⟨_root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.inX k n c (fun r => v (Sum.inl r)),
      Submodule.mem_map_of_mem hL,
      ∑ i, a i • ((ϖ : k) ^ (i.val + 1) • _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.aux k n i),
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩), ?_⟩
    funext r
    rcases r with r | i
    · simp [_root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.inX, _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.aux, Finset.sum_apply,
        Pi.single_apply]
    · simp [_root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.inX, _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.aux, Finset.sum_apply,
        Pi.single_apply, Subring.smul_def, ha i]

omit [Fintype n] in
theorem _root_.GlobalTheory.RootEx.UnfoldShape.inX_mem_chainLat {ϖ : 𝒪[k]} {L : Submodule 𝒪[k] (n → k)} {v : n → k} :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.inX k n c v ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.chainLat ϖ c L ↔ v ∈ L := by
  rw [_root_.GlobalTheory.RootEx.UnfoldShape.mem_chainLat]
  exact ⟨fun h => h.1, fun h => ⟨h, fun i => ⟨0, by simp [_root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.inX]⟩⟩⟩

omit [Fintype n] in
theorem _root_.GlobalTheory.RootEx.UnfoldShape.scaled_basis_mem_chainLattice (ϖ : 𝒪[k]) (L : Submodule 𝒪[k] (n → k)) (i : Fin c) :
    (ϖ : k) ^ (i.val + 1) • _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.aux k n i ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.chainLat ϖ c L :=
  Submodule.mem_sup_right (Submodule.subset_span ⟨i, rfl⟩)

def colMat (n' : Type) (y : Fin c → (n ⊕ Fin c → k)) : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k :=
  Matrix.of fun r s => Sum.elim (fun _ => 0) (fun j : Fin (c + 1) => Fin.cases 0 (fun i => y i r) j) s

open Classical in
def col (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free 1 rs} → k) (i : Fin c) : n ⊕ Fin c → k := by
  classical
  exact fun r => if h : Free (n' := n') 1 (r, Sum.inr i.succ) then e ⟨_, h⟩ else 0

def uncol (n' : Type) (y : Fin c → (n ⊕ Fin c → k)) :
    {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free 1 rs} → k := fun rs => colMat n' y rs.1.1 rs.1.2

section
omit [ValuativeRel k] [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

theorem pt_eq (x₀ : Matrix n n' k) (y : Fin c → (n ⊕ Fin c → k)) : pt x₀ y = basePt c x₀ + colMat n' y := rfl

omit [ValuativeRel k] [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] in
theorem _root_.GlobalTheory.RootEx.UnfoldShape.colMat_smul (a : k) (y : Fin c → (n ⊕ Fin c → k)) :
    _root_.GlobalTheory.RootEx.UnfoldShape.colMat n' (a • y) = a • _root_.GlobalTheory.RootEx.UnfoldShape.colMat n' y := by
  ext r (s | j)
  · simp [_root_.GlobalTheory.RootEx.UnfoldShape.colMat]
  · refine Fin.cases ?_ (fun i => ?_) j <;> simp [_root_.GlobalTheory.RootEx.UnfoldShape.colMat]

end

section
omit [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

end

section
omit [ValuativeRel k] [Fintype n] [DecidableEq n] [DecidableEq n']

end

variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable {k : Type} [Field k] [ValuativeRel k] in
omit [Fintype n] [DecidableEq n] in
theorem _root_.GlobalTheory.RootEx.UnfoldShape.mapsInto_colMat {ϖ : 𝒪[k]} {L' : Submodule 𝒪[k] (n' → k)}
    {Λ : Submodule 𝒪[k] (n ⊕ Fin c → k)} {y : Fin c → (n ⊕ Fin c → k)}
    (hy : ∀ i, (ϖ : k) ^ (i.val + 2) • y i ∈ Λ) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.MapsInto (_root_.GlobalTheory.RootEx.UnfoldShape.colMat n' y) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.chainLat ϖ (c + 1) L') Λ := by
  intro v hv
  obtain ⟨-, ha⟩ := _root_.GlobalTheory.RootEx.UnfoldShape.mem_chainLat.1 hv
  choose a ha using ha
  have hsum : _root_.GlobalTheory.RootEx.UnfoldShape.colMat n' y *ᵥ v = ∑ i : Fin c, a i.succ • ((ϖ : k) ^ (i.val + 2) • y i) := by
    funext r
    simp only [Matrix.mulVec, dotProduct, _root_.GlobalTheory.RootEx.UnfoldShape.colMat, Matrix.of_apply, Fintype.sum_sum_type,
      Sum.elim_inl, Sum.elim_inr, zero_mul, Finset.sum_const_zero, zero_add, Fin.sum_univ_succ,
      Fin.cases_zero, Fin.cases_succ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Subring.smul_def]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ha i.succ, Fin.val_succ]
    ring
  rw [hsum]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hy i)

variable [MeasurableSpace k] [BorelSpace k]

section

variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ} in
omit [ValuativeRel k] in
private theorem affPt_eq_pt_col (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // _root_.GlobalTheory.RootEx.Free 1 rs} → k) :
    _root_.GlobalTheory.RootEx.affPt 1 x₀ e = _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.pt x₀ (_root_.GlobalTheory.RootEx.UnfoldShape.col e) := by
  unfold _root_.GlobalTheory.RootEx.affPt _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.pt
  congr 1
  ext r s
  rcases s with s | j
  · rcases r with r | l <;> simp [_root_.GlobalTheory.RootEx.Free]
  · refine Fin.cases ?_ (fun i => ?_) j
    · rcases r with r | l <;> simp [_root_.GlobalTheory.RootEx.Free]
    · by_cases h : _root_.GlobalTheory.RootEx.Free (n' := n') 1 (r, Sum.inr i.succ) <;>
        simp [_root_.GlobalTheory.RootEx.UnfoldShape.col, h]

variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ} in
omit [ValuativeRel k] in
private theorem col_mem_Yle' [ValuativeRel k]
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // _root_.GlobalTheory.RootEx.Free 1 rs} → k) (i : Fin c) :
    _root_.GlobalTheory.RootEx.UnfoldShape.col e i ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.Yle k n c (i.val + 1) := by
  intro l hl
  simp only [_root_.GlobalTheory.RootEx.UnfoldShape.col]
  rw [dite_eq_right]
  simp only [_root_.GlobalTheory.RootEx.Free, Fin.val_succ]
  omega

theorem _root_.GlobalTheory.RootEx.UnfoldShape.exists_pt_ne_zero {ψ : AddChar k Circle} {ν : Measure k}
    {Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ} {x₀ : Matrix n n' k} (h : _root_.GlobalTheory.RootEx.opE ψ ν 1 Ψ x₀ ≠ 0) :
    ∃ y : Fin c → (n ⊕ Fin c → k), (∀ i, y i ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.Yle k n c (i.val + 1)) ∧
      Ψ (_root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.pt x₀ y) ≠ 0 := by
  by_contra hne
  push_neg at hne
  apply h
  have hzero : ∀ e, Ψ (_root_.GlobalTheory.RootEx.affPt 1 x₀ e) = 0 := fun e => by
    rw [affPt_eq_pt_col]
    exact hne _ fun i => col_mem_Yle' e i
  unfold _root_.GlobalTheory.RootEx.opE
  simp [hzero]

variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ} in
omit [ValuativeRel k] in
private theorem colMat_eq_zero_of_not_free [ValuativeRel k] {y : Fin c → (n ⊕ Fin c → k)}
    (hy : ∀ i, y i ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.Yle k n c (i.val + 1)) {r : n ⊕ Fin c} {s : n' ⊕ Fin (c + 1)}
    (h : ¬ _root_.GlobalTheory.RootEx.Free 1 (r, s)) : _root_.GlobalTheory.RootEx.UnfoldShape.colMat n' y r s = 0 := by
  rcases s with s | j
  · simp [_root_.GlobalTheory.RootEx.UnfoldShape.colMat]
  · induction j using Fin.cases with
    | zero => simp [_root_.GlobalTheory.RootEx.UnfoldShape.colMat]
    | succ i =>
      simp only [_root_.GlobalTheory.RootEx.UnfoldShape.colMat, Matrix.of_apply, Sum.elim_inr, Fin.cases_succ]
      rcases r with r | l
      · exact absurd (by simp [_root_.GlobalTheory.RootEx.Free]) h
      · apply hy i l
        simp only [_root_.GlobalTheory.RootEx.Free, Fin.val_succ] at h
        omega

variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ} in
omit [ValuativeRel k] in
private theorem affPt_add_uncol [ValuativeRel k] (x₀ : Matrix n n' k) {y : Fin c → (n ⊕ Fin c → k)}
    (hy : ∀ i, y i ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.Yle k n c (i.val + 1))
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // _root_.GlobalTheory.RootEx.Free 1 rs} → k) :
    _root_.GlobalTheory.RootEx.affPt 1 x₀ (e + _root_.GlobalTheory.RootEx.UnfoldShape.uncol n' y) =
      _root_.GlobalTheory.RootEx.affPt 1 x₀ e + _root_.GlobalTheory.RootEx.UnfoldShape.colMat n' y := by
  unfold _root_.GlobalTheory.RootEx.affPt
  rw [add_assoc]
  congr 1
  ext r s
  by_cases h : _root_.GlobalTheory.RootEx.Free 1 (r, s)
  · simp [h, _root_.GlobalTheory.RootEx.UnfoldShape.uncol]
  · simp [h, colMat_eq_zero_of_not_free hy h]

variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ} in
omit [ValuativeRel k] in
private theorem ch_add_colMat (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)
    (y : Fin c → (n ⊕ Fin c → k)) :
    _root_.GlobalTheory.RootEx.ch (x + _root_.GlobalTheory.RootEx.UnfoldShape.colMat n' y) =
      _root_.GlobalTheory.RootEx.ch x + ∑ i, y i (Sum.inr i) := by
  simp [_root_.GlobalTheory.RootEx.ch, Finset.sum_add_distrib, _root_.GlobalTheory.RootEx.UnfoldShape.colMat]

theorem _root_.GlobalTheory.RootEx.UnfoldShape.opE_translate (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure]
    {Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ} {y : Fin c → (n ⊕ Fin c → k)}
    (hy : ∀ i, y i ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.Yle k n c (i.val + 1)) (hΨ : ∀ x, Ψ (x + _root_.GlobalTheory.RootEx.UnfoldShape.colMat n' y) = Ψ x)
    (x₀ : Matrix n n' k) :
    _root_.GlobalTheory.RootEx.opE ψ ν 1 Ψ x₀ = (ψ (-∑ i, y i (Sum.inr i)) : ℂ) * _root_.GlobalTheory.RootEx.opE ψ ν 1 Ψ x₀ := by
  haveI := _root_.GlobalTheory.SplitWeil.secondCountable k
  unfold _root_.GlobalTheory.RootEx.opE
  conv_lhs => rw [← integral_add_right_eq_self _ (_root_.GlobalTheory.RootEx.UnfoldShape.uncol n' y)]
  rw [← integral_const_mul]
  congr 1
  funext e
  rw [affPt_add_uncol x₀ hy, hΨ, ch_add_colMat, neg_add, AddChar.map_add_eq_mul,
    Circle.coe_mul]
  ring
end

end GlobalTheory.RootEx.UnfoldShape
