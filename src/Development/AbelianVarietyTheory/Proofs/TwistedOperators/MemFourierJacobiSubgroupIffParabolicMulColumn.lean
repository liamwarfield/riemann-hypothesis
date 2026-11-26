module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilFormulaRootExchangeParabolicIntersection
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FramePositiveSum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotientIntegralParabolicUnfolding
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiUnipotentEqProdRootExchange
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviIntegralFacts

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemFourierJacobiSubgroupIffParabolicMulColumn
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemFourierJacobiSubgroupIffParabolicMulColumn
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage

namespace GlobalTheory.RootEx.FourierJacobiGroup

theorem uni_conj {k : Type*} [Field k] {ι : Type*} [Fintype ι] [DecidableEq ι] {b : ι → ℕ}
    {A B M : Matrix ι ι k} (hA : ∀ r s, b r ≠ b s → A r s = 0) (hB : ∀ r s, b r ≠ b s → B r s = 0)
    (hAB : A * B = 1) (hM : Radical.Uni b M) : Radical.Uni b (A * M * B) := by
  intro r s hrs
  have : (A * M * B) r s = (A * (1 : Matrix ι ι k) * B) r s := by
    simp only [Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun t _ => ?_
    by_cases h1 : b r = b t
    · by_cases h2 : b u = b s
      · rw [hM t u (by omega)]
      · rw [hB u s h2, mul_zero, mul_zero]
    · simp only [hA r t h1, zero_mul]
  rw [this, Matrix.mul_one, hAB]

variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

theorem colE_add (q : ℕ) (β γ : n → k) : colE c q β * colE c q γ = colE c q (β + γ) := by
  apply Units.ext
  simp only [colE, upU, Units.val_mul, fromBlocks_multiply]
  congr 1 <;> simp
  ext r i
  by_cases h : i.val + 1 = q <;> simp [h, add_comm]

theorem colE_inv (q : ℕ) (β : n → k) : (colE c q β)⁻¹ = colE c q (-β) :=
  inv_eq_of_mul_eq_one_right (QuotStep.colE_neg q β)

theorem colE_zero (q : ℕ) : colE c q (0 : n → k) = 1 := by
  have := QuotStep.colE_neg (c := c) q (0 : n → k)
  rwa [colE_add, add_neg_cancel] at this

theorem colE_offdiag (q : ℕ) (β : n → k) (r s : n ⊕ Fin c) (h : lev q r ≠ lev q s) :
    (colE c q β).val r s = 0 := by
  rcases r with r | r <;> rcases s with s | s
  · simp [lev] at h
  · simp only [lev, Sum.elim_inl, Sum.elim_inr] at h
    simp [colE, upU, h.symm]
  · simp [colE, upU]
  · have : r ≠ s := by
      rintro rfl
      exact h rfl
    simp [colE, upU, this]

theorem colE_conj_mem (q : ℕ) (β : n → k) {u : GL (n ⊕ Fin c) k} (hu : u ∈ N k n c q) :
    colE c q β * u * (colE c q β)⁻¹ ∈ N k n c q := by
  rw [Radical.mem_N_iff] at hu ⊢
  rw [colE_inv]
  exact uni_conj (b := lev q) (colE_offdiag q β) (colE_offdiag q (-β))
    (congrArg Units.val (QuotStep.colE_neg q β)) hu

theorem exists_of_mem_N {p : ℕ} (hp : p < c) {g : GL (n ⊕ Fin c) k} (hg : g ∈ N k n c p) :
    ∃ u ∈ N k n c (p + 1), ∃ β : n → k, g = u * colE c (p + 1) β := by
  let β : n → k := fun x => g.val (Sum.inl x) (Sum.inr ⟨p, hp⟩)
  refine ⟨g * colE c (p + 1) (-β), ?_, β, by rw [mul_assoc, colE_add, neg_add_cancel, colE_zero, mul_one]⟩
  have h1 := (Radical.mem_N_iff _).1 (mul_mem hg (Radical.colE_mem (-β) (Nat.lt_succ_self p)))
  have h0 := (Radical.mem_N_iff _).1 hg
  rw [Radical.mem_N_iff]
  intro r s hrs
  by_cases h : lev p s ≤ lev p r
  · exact h1 r s h
  rcases r with r | r <;> rcases s with s | s <;> simp only [lev, Sum.elim_inl, Sum.elim_inr] at h hrs
  · omega
  · obtain rfl : s = ⟨p, hp⟩ := Fin.ext (by simp only; omega)
    have h2 : ∀ y, g.val (Sum.inl r) (Sum.inl y) = (1 : Matrix n n k) r y := fun y => by
      rw [h0 _ _ (by simp [lev])]; simp [Matrix.one_apply]
    simp [colE, upU, Matrix.mul_apply, Fintype.sum_sum_type, h2, Matrix.one_apply, β]
  · omega
  · omega

theorem colE_conj_mem_R (q : ℕ) (β : n → k) {r : GL (n ⊕ Fin c) k} (hr : r ∈ R k n c q) :
    ∃ r' ∈ R k n c q, ∃ γ : n → k, colE c q β * r = r' * colE c q γ := by
  obtain ⟨x, u, hu, rfl⟩ := Radical.exists_of_mem_R hr
  refine ⟨embX c x * (colE c q ((x⁻¹).val.mulVec β) * u * (colE c q ((x⁻¹).val.mulVec β))⁻¹),
    mul_mem (Subgroup.mem_sup_left ⟨x, rfl⟩) (Subgroup.mem_sup_right (colE_conj_mem q _ hu)),
    (x⁻¹).val.mulVec β, ?_⟩
  rw [← QuotStep.conj_colE, map_inv]
  group

theorem mem_RFJ_iff : ∀ (k : Type) [Field k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) (_ : 1 ≤ ρ) (_ : ρ < c), (∀ g, g ∈ RFJ k n c ρ ↔ ∃ r ∈ R k n c (ρ + 1), ∃ β : n → k, g = r * colE c (ρ + 1) β) ∧ ∀ β : n → k, ∀ u ∈ N k n c (ρ + 1), colE c (ρ + 1) β * u * (colE c (ρ + 1) β)⁻¹ ∈ N k n c (ρ + 1) := by
  intro k _ n _ _ c ρ _ hρ
  refine ⟨fun g => ⟨fun hg => ?_, ?_⟩, fun β u hu => colE_conj_mem _ β hu⟩
  · let S : Subgroup (GL (n ⊕ Fin c) k) :=
      { carrier := {g | ∃ r ∈ R k n c (ρ + 1), ∃ β : n → k, g = r * colE c (ρ + 1) β}
        one_mem' := ⟨1, one_mem _, 0, by rw [colE_zero, mul_one]⟩
        mul_mem' := by
          rintro _ _ ⟨r, hr, β, rfl⟩ ⟨r₂, hr₂, β₂, rfl⟩
          obtain ⟨r', hr', γ, e⟩ := colE_conj_mem_R (ρ + 1) β hr₂
          refine ⟨r * r', mul_mem hr hr', γ + β₂, ?_⟩
          rw [← colE_add, mul_assoc r, ← mul_assoc _ r₂, e]
          simp only [mul_assoc]
        inv_mem' := by
          rintro _ ⟨r, hr, β, rfl⟩
          obtain ⟨r', hr', γ, e⟩ := colE_conj_mem_R (ρ + 1) (-β) (inv_mem hr)
          exact ⟨r', hr', γ, by rw [_root_.mul_inv_rev, colE_inv, e]⟩ }
    have hR : R k n c (ρ + 1) ≤ S := fun r hr => ⟨r, hr, 0, by rw [colE_zero, mul_one]⟩
    have : RFJ k n c ρ ≤ S := by
      refine sup_le (sup_le (le_trans le_sup_left hR) fun g hg => ?_) hR
      obtain ⟨u, hu, β, rfl⟩ := exists_of_mem_N hρ hg
      exact ⟨u, Subgroup.mem_sup_right hu, β, rfl⟩
    exact this hg
  · rintro ⟨r, hr, β, rfl⟩
    exact mul_mem (Subgroup.mem_sup_right hr)
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right (Radical.colE_mem β (Nat.lt_succ_self ρ))))

end GlobalTheory.RootEx.FourierJacobiGroup
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemFourierJacobiSubgroupIffParabolicMulColumnStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_fourierJacobiSubgroup_iff_parabolic_mul_column : ∀ (k : Type) [Field k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) (_ : 1 ≤ ρ) (_ : ρ < c), (∀ g, g ∈ RFJ k n c ρ ↔ ∃ r ∈ R k n c (ρ + 1), ∃ β : n → k, g = r * colE c (ρ + 1) β) ∧ ∀ β : n → k, ∀ u ∈ N k n c (ρ + 1), colE c (ρ + 1) β * u * (colE c (ρ + 1) β)⁻¹ ∈ N k n c (ρ + 1) := by
  first | exact @GlobalTheory.RootEx.FourierJacobiGroup.mem_RFJ_iff | exact GlobalTheory.RootEx.FourierJacobiGroup.mem_RFJ_iff | (intros; apply GlobalTheory.RootEx.FourierJacobiGroup.mem_RFJ_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsSymmetricPositionLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsSymmetricPositionLevel
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

noncomputable section
namespace GlobalTheory.SymLevelExists

section Plain
variable {F : Type} [Field F] {κ l : ℕ}

def symGroup (F : Type) [Field F] (κ l p : ℕ) : Subgroup (GL (Fin κ ⊕ Fin l) F) where
  carrier := {x | ∃ u ∈ N F (Fin κ) l p, ∃ γ : GL (Fin κ) F, IsUpperUnip Fin.val γ.val ∧ x = u * embX l γ}
  one_mem' := ⟨1, one_mem _, 1, fun _ _ _ => rfl, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨u, hu, γ, hγ, rfl⟩ ⟨u', hu', γ', hγ', rfl⟩
    refine ⟨_, mul_mem hu (Radical.conj_mem γ hu'), γ * γ',
      Radical.Uni.mul (b := Fin.val) hγ hγ', ?_⟩
    rw [map_mul]; group
  inv_mem' := by
    rintro _ ⟨u, hu, γ, hγ, rfl⟩
    refine ⟨_, Radical.conj_mem γ⁻¹ (inv_mem hu), γ⁻¹, Radical.Uni.inv (b := Fin.val) hγ, ?_⟩
    rw [map_inv]; group

theorem simpleSum_mul_embX (u : GL (Fin κ ⊕ Fin l) F) (γ : GL (Fin κ) F) :
    simpleSum (u * embX l γ) = simpleSum u := by
  have hv : ∀ i j, (u * embX l γ).val (Sum.inr i) (Sum.inr j) = u.val (Sum.inr i) (Sum.inr j) := by
    intro i j
    rw [Units.val_mul, Radical.embX_val, ← fromBlocks_toBlocks u.val]
    simp [fromBlocks_multiply]
  simp only [simpleSum, hv]

theorem toBlocks₁₁_mul_embX {p : ℕ} {u : GL (Fin κ ⊕ Fin l) F} (hu : u ∈ N F (Fin κ) l p) (γ : GL (Fin κ) F) :
    (u * embX l γ).val.toBlocks₁₁ = γ.val := by
  rw [Units.val_mul, Radical.embX_val]
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks u.val]
  simp [fromBlocks_multiply, Radical.toBlocks₁₁_of_mem hu]

theorem superSum_mul {a : Type} [Fintype a] [DecidableEq a] {pos : a → ℕ} {M M' : Matrix a a F}
    (h : IsUpperUnip pos M) (h' : IsUpperUnip pos M') :
    superSum pos (M * M') = superSum pos M + superSum pos M' := by
  simp only [superSum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs with hij
  · exact Radical.Uni.mul_apply_succ (b := pos) h h' hij
  · simp

def symSum (x : GL (Fin κ ⊕ Fin l) F) : F := simpleSum x + superSum Fin.val x.val.toBlocks₁₁

theorem symSum_eq {p : ℕ} {u : GL (Fin κ ⊕ Fin l) F} (hu : u ∈ N F (Fin κ) l p) (γ : GL (Fin κ) F) :
    symSum (u * embX l γ) = simpleSum u + superSum Fin.val γ.val := by
  rw [symSum, simpleSum_mul_embX, toBlocks₁₁_mul_embX hu]

theorem symSum_mul {p : ℕ} {x y : GL (Fin κ ⊕ Fin l) F} (hx : x ∈ symGroup F κ l p) (hy : y ∈ symGroup F κ l p) :
    symSum (x * y) = symSum x + symSum y := by
  obtain ⟨u, hu, γ, hγ, rfl⟩ := hx
  obtain ⟨u', hu', γ', hγ', rfl⟩ := hy
  have e : u * embX l γ * (u' * embX l γ') = u * (embX l γ * u' * (embX l γ)⁻¹) * embX l (γ * γ') := by
    rw [map_mul]; group
  rw [e, symSum_eq (mul_mem hu (Radical.conj_mem γ hu')), symSum_eq hu, symSum_eq hu',
    Radical.simpleSum_mul hu (Radical.conj_mem γ hu'), Radical.simpleSum_conj, Units.val_mul, superSum_mul hγ hγ']
  ring

end Plain

section Local
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_residue_char {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {ϖ : kˣ} (hϖ : IsUnif ϖ) :
    ∃ χ : 𝓀[k] → Circle, (∀ y z, χ (y + z) = χ y * χ z) ∧
      ∀ y : 𝒪[k], χ (IsLocalRing.residue 𝒪[k] y) = ψ ((ϖ⁻¹ : kˣ) * (y : k)) := by
  have hs : Function.Surjective (IsLocalRing.residue 𝒪[k]) := IsLocalRing.residue_surjective
  have key : ∀ y z : 𝒪[k], IsLocalRing.residue 𝒪[k] y = IsLocalRing.residue 𝒪[k] z →
      ψ ((ϖ⁻¹ : kˣ) * (y : k)) = ψ ((ϖ⁻¹ : kˣ) * (z : k)) := by
    intro y z h
    have h1 : valuation k ((y : k) - z) < 1 := (residue_eq_iff_lt y z).1 h
    have h2 := (hϖ _).1 h1
    have h3 : ψ ((ϖ⁻¹ : kˣ) * ((y : k) - z)) = 1 := by
      refine hψ.eq_one ?_
      have h0 : 0 < valuation k (ϖ : k) := by simp [zero_lt_iff]
      simp only [cball, Set.mem_ofPred_eq, Units.val_one, map_one, map_mul, Units.val_inv_eq_inv_val, map_inv₀]
      rwa [inv_mul_le_one₀ h0]
    rw [show ((ϖ⁻¹ : kˣ) : k) * (y : k) = (ϖ⁻¹ : kˣ) * ((y : k) - z) + (ϖ⁻¹ : kˣ) * (z : k) by ring,
      AddChar.map_add_eq_mul, h3, one_mul]
  have h2 : ∀ y : 𝒪[k], ψ ((ϖ⁻¹ : kˣ) * ((Function.surjInv hs (IsLocalRing.residue 𝒪[k] y) : 𝒪[k]) : k)) =
      ψ ((ϖ⁻¹ : kˣ) * (y : k)) := fun y => key _ _ (Function.surjInv_eq hs _)
  refine ⟨fun y => ψ ((ϖ⁻¹ : kˣ) * ((Function.surjInv hs y : 𝒪[k]) : k)), fun y z => ?_, h2⟩
  obtain ⟨y, rfl⟩ := hs y
  obtain ⟨z, rfl⟩ := hs z
  beta_reduce
  rw [← map_add (f := _), h2, h2, h2, ← AddChar.map_add_eq_mul, ← mul_add]
  rfl

def symSumInt {κ l : ℕ} (g : GL (Fin κ ⊕ Fin l) 𝒪[k]) : 𝒪[k] :=
  (∑ i : Fin l, ∑ j : Fin l, if j.val = i.val + 1 then g.val (Sum.inr i) (Sum.inr j) else 0) +
    ∑ i : Fin κ, ∑ j : Fin κ, if j.val = i.val + 1 then g.val (Sum.inl i) (Sum.inl j) else 0

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem map_symSumInt {F : Type} [Field F] (f : 𝒪[k] →+* F) {κ l : ℕ} (g : GL (Fin κ ⊕ Fin l) 𝒪[k]) :
    f (symSumInt g) = symSum (Matrix.GeneralLinearGroup.map f g) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [symSumInt, symSum, simpleSum, superSum, map_add (f := _), map_sum, apply_ite f, map_zero]
  rfl

end Local

theorem exists_isSymLevel :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (ψ : AddChar k Circle), HasConductor ψ 1 → ∀ ϖ : kˣ, IsUnif ϖ →
      ∀ ρ κ l : ℕ, ∃ P : GlobalTheory.StepData.TypeDatum k (Fin κ ⊕ Fin l),
        GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsSymLevel ψ ϖ ρ P := by
  intro k _ _ _ _ ψ hψ ϖ hϖ ρ κ l
  obtain ⟨χ, hadd, hres⟩ := exists_residue_char hψ hϖ
  let χ' : symGroup 𝓀[k] κ l (ρ + 1) →* ℂˣ :=
    MonoidHom.mk' (fun x => Circle.toUnits (χ (symSum (x : GL (Fin κ ⊕ Fin l) 𝓀[k])))) fun x y => by
      rw [Subgroup.coe_mul, symSum_mul x.2 y.2, hadd, map_mul]
  refine ⟨TypeDatum.ofResidue _ χ', fun g => ⟨?_, ?_⟩, ?_⟩
  · rintro ⟨g₀, ⟨u, hu, γ, hγ, e⟩, rfl⟩
    exact ⟨u, hu, γ, hγ, g₀, rfl, e⟩
  · rintro ⟨u, hu, γ, hγ, g₀, rfl, e⟩
    exact ⟨g₀, ⟨u, hu, γ, hγ, e⟩, rfl⟩
  · rintro ⟨_, g₀, hg, rfl⟩
    rw [TypeDatum.ofResidue_lam _ χ' g₀ hg]
    change ((χ (symSum (Matrix.GeneralLinearGroup.map (IsLocalRing.residue 𝒪[k]) g₀)) : Circle) : ℂ) = _
    rw [← map_symSumInt, hres, ← Circle.coe_mul, ← AddChar.map_add_eq_mul, ← mul_add]
    exact congrArg (fun z : k => ((ψ ((ϖ⁻¹ : kˣ) * z) : Circle) : ℂ)) (map_symSumInt (algebraMap 𝒪[k] k) g₀)

end GlobalTheory.SymLevelExists
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsSymmetricPositionLevelStatement
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isSymmetricPositionLevel :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (ψ : AddChar k Circle), HasConductor ψ 1 → ∀ ϖ : kˣ, IsUnif ϖ →
      ∀ ρ κ l : ℕ, ∃ P : GlobalTheory.StepData.TypeDatum k (Fin κ ⊕ Fin l),
        GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsSymLevel ψ ϖ ρ P :=
  @GlobalTheory.SymLevelExists.exists_isSymLevel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProperTriple
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProperTriple
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage

namespace GlobalTheory.RootEx.ProperTriple

private lemma unipotent_block_entries_eq_one_zero {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n]
    {c ρ : ℕ} {u : GL (n ⊕ Fin c) k} (hu : u ∈ _root_.GlobalTheory.RootEx.N k n c (ρ + 1)) :
    (∀ t t' : n, (u : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (Sum.inl t) (Sum.inl t') =
      (1 : Matrix n n k) t t') ∧
    (∀ (t : n) (i : Fin c), (i : ℕ) + 1 = ρ + 1 →
      (u : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (Sum.inl t) (Sum.inr i) = 0) ∧
    (∀ (t : n) (i : Fin c), (i : ℕ) + 1 = ρ + 1 →
      (u : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (Sum.inr i) (Sum.inl t) = 0) := by
  have h := _root_.GlobalTheory.RootEx.Model.mem_N_iff.1 hu
  unfold _root_.GlobalTheory.RootEx.InN _root_.GlobalTheory.RootEx.lev at h
  refine ⟨fun t t' => ?_, fun t i hi => ?_, fun t i hi => ?_⟩
  · rw [h _ _ (by simp)]
    simp [Matrix.one_apply]
  · rw [h _ _ (by simp [hi])]
    simp
  · rw [h _ _ (by simp [hi])]
    simp

private lemma recover_colE_vec_from_embX_product {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n]
    {c ρ : ℕ} (hρc : ρ < c) (x : GL n k) (u : _root_.GlobalTheory.RootEx.N k n c (ρ + 1))
    (β : n → k) (r : n) :
    ∑ s, (↑(_root_.GlobalTheory.RootEx.embX c x * (u : GL (n ⊕ Fin c) k) *
        _root_.GlobalTheory.RootEx.colE c (ρ + 1) β)⁻¹ : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
        (Sum.inl r) (Sum.inl s) *
      (↑(_root_.GlobalTheory.RootEx.embX c x * (u : GL (n ⊕ Fin c) k) *
        _root_.GlobalTheory.RootEx.colE c (ρ + 1) β) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
        (Sum.inl s) (Sum.inr ⟨ρ, hρc⟩) = β r := by
  obtain ⟨hll, hlr, -⟩ := unipotent_block_entries_eq_one_zero u.2
  obtain ⟨hll', -, hrl'⟩ := unipotent_block_entries_eq_one_zero (inv_mem u.2)
  have h1 : ∀ s, (↑(_root_.GlobalTheory.RootEx.embX c x * (u : GL (n ⊕ Fin c) k) *
      _root_.GlobalTheory.RootEx.colE c (ρ + 1) β) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
        (Sum.inl s) (Sum.inr ⟨ρ, hρc⟩) = ((x : Matrix n n k) *ᵥ β) s := by
    intro s
    rw [Units.val_mul, Units.val_mul, _root_.GlobalTheory.RootEx.Radical.embX_val,
      _root_.GlobalTheory.RootEx.ExchangeSupport.colE_val]
    simp [Matrix.mul_apply, Fintype.sum_sum_type, hll, hlr, _root_.GlobalTheory.RootEx.ExchangeSupport.colM,
      Matrix.mulVec, dotProduct, Matrix.one_apply]
  have h2 : ∀ s, (↑(_root_.GlobalTheory.RootEx.embX c x * (u : GL (n ⊕ Fin c) k) *
      _root_.GlobalTheory.RootEx.colE c (ρ + 1) β)⁻¹ : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
        (Sum.inl r) (Sum.inl s) = (↑x⁻¹ : Matrix n n k) r s := by
    intro s
    rw [_root_.mul_inv_rev, _root_.mul_inv_rev, Units.val_mul, Units.val_mul, ← map_inv,
      _root_.GlobalTheory.RootEx.Radical.embX_val, _root_.GlobalTheory.RootEx.ExchangeSupport.colE_inv_val]
    simp only [Matrix.coe_units_inv] at hll' hrl' ⊢
    have hz : ∀ i : Fin c, (i : ℕ) = ρ →
        ∑ a, ((u : GL (n ⊕ Fin c) k) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)⁻¹ (Sum.inr i) (Sum.inl a) *
          (↑x : Matrix n n k)⁻¹ a s = 0 :=
      fun i hi => Finset.sum_eq_zero fun a _ => by rw [hrl' a i (by omega), zero_mul]
    simp +contextual [Matrix.mul_apply, Fintype.sum_sum_type, hll', _root_.GlobalTheory.RootEx.ExchangeSupport.colM,
      Matrix.one_apply, hz]
  simp_rw [h1, h2]
  change ((↑x⁻¹ : Matrix n n k) *ᵥ ((x : Matrix n n k) *ᵥ β)) r = β r
  rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]

theorem _root_.GlobalTheory.RootEx.ProperTriple.proper_triple : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) (_ : 1 ≤ ρ)
    (_ : ρ < c) (C : Set (GL (n ⊕ Fin c) k)) (_ : IsCompact C),
    ∃ D : Set (GL n k × _root_.GlobalTheory.RootEx.N k n c (ρ + 1) × (n → k)), IsCompact D ∧
      ∀ z : GL n k × _root_.GlobalTheory.RootEx.N k n c (ρ + 1) × (n → k),
        _root_.GlobalTheory.RootEx.embX c z.1 * (z.2.1 : GL (n ⊕ Fin c) k) *
          _root_.GlobalTheory.RootEx.colE c (ρ + 1) z.2.2 ∈ C → z ∈ D := by
  intro k _ _ _ _ n _ _ c ρ _ hρc C hC
  let F : GL (n ⊕ Fin c) k → (n → k) := fun g r =>
    ∑ s, (↑g⁻¹ : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (Sum.inl r) (Sum.inl s) *
      (g : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (Sum.inl s) (Sum.inr ⟨ρ, hρc⟩)
  have hF : Continuous F := by
    refine continuous_pi fun r => continuous_finsetSum _ fun s _ => ?_
    exact (Units.continuous_coe_inv.matrix_elem _ _).mul (Units.continuous_val.matrix_elem _ _)
  have hK : IsCompact (F '' C) := hC.image hF
  have hC' : IsCompact ((fun q : GL (n ⊕ Fin c) k × (n → k) =>
      q.1 * (_root_.GlobalTheory.RootEx.colE c (ρ + 1) q.2)⁻¹) '' (C ×ˢ (F '' C))) :=
    (hC.prod hK).image (continuous_fst.mul
      (_root_.GlobalTheory.RootEx.ExchangeSupport.continuous_colE.comp continuous_snd).inv)
  obtain ⟨D₀, hD₀, hD₀C⟩ := _root_.GlobalTheory.QuotInt.compact_preimage
    (_root_.GlobalTheory.RootEx.VolN.isClosed_N (k := k) (n := n) (c := c) (ρ + 1)) hC'
  refine ⟨(fun q : (GL n k × _root_.GlobalTheory.RootEx.N k n c (ρ + 1)) × (n → k) =>
    (q.1.1, q.1.2, q.2)) '' (D₀ ×ˢ (F '' C)), (hD₀.prod hK).image (by fun_prop), ?_⟩
  intro z hz
  have hβ : z.2.2 ∈ F '' C := ⟨_, hz, funext (recover_colE_vec_from_embX_product hρc z.1 z.2.1 z.2.2)⟩
  have hz' : (z.1, z.2.1) ∈ D₀ := hD₀C _ ⟨(_, z.2.2), ⟨hz, hβ⟩, by simp⟩
  exact ⟨((z.1, z.2.1), z.2.2), ⟨hz', hβ⟩, rfl⟩

end GlobalTheory.RootEx.ProperTriple
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProperTripleStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compact_preimage_embX_mul_colE : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) (_ : 1 ≤ ρ) (_ : ρ < c) (C : Set (GL (n ⊕ Fin c) k)) (_ : IsCompact C), ∃ D : Set (GL n k × N k n c (ρ + 1) × (n → k)), IsCompact D ∧ ∀ z : GL n k × N k n c (ρ + 1) × (n → k), embX c z.1 * (z.2.1 : GL (n ⊕ Fin c) k) * colE c (ρ + 1) z.2.2 ∈ C → z ∈ D := by
  first | exact @GlobalTheory.RootEx.ProperTriple.proper_triple | exact GlobalTheory.RootEx.ProperTriple.proper_triple | (intros; apply GlobalTheory.RootEx.ProperTriple.proper_triple <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemRootExchangeParabolicAndFourierJacobiIffEntri
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemRootExchangeParabolicAndFourierJacobiIffEntri
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage

namespace GlobalTheory.RootEx.ParabolicEntries

open GlobalTheory.RootEx.Radical

variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}

def Par (L : ℕ) (b : Fin c → ℕ) (M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) : Prop :=
  ∀ r s : n ⊕ Fin c, (r.isRight ∨ s.isRight) → Sum.elim (fun _ => L) b s ≤ Sum.elim (fun _ => L) b r →
    M r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s

omit [Fintype n] in
theorem Par.blockTri {L : ℕ} {b : Fin c → ℕ} {M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k} (h : Par L b M) :
    M.BlockTriangular (Sum.elim (fun _ => L) b) := by
  intro r s hrs
  have hne : r ≠ s := by
    rintro rfl
    exact lt_irrefl _ hrs
  rw [h r s _ hrs.le, Matrix.one_apply_ne hne]
  rcases r with r | r <;> rcases s with s | s <;> simp_all

theorem Par.mul_left {L : ℕ} {b : Fin c → ℕ} {M M' : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k} (h : Par L b M)
    (h' : M'.BlockTriangular (Sum.elim (fun _ => L) b)) {r s : n ⊕ Fin c} (hr : r.isRight)
    (hrs : Sum.elim (fun _ => L) b s ≤ Sum.elim (fun _ => L) b r) : (M * M') r s = M' r s := by
  have : (M * M') r s = ((1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) * M') r s := by
    simp only [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun t _ => ?_
    rcases le_or_gt (Sum.elim (fun _ => L) b t) (Sum.elim (fun _ => L) b r) with ht | ht
    · rw [h r t (Or.inl hr) ht]
    · rw [h' (lt_of_le_of_lt hrs ht), mul_zero, mul_zero]
  rw [this, Matrix.one_mul]

theorem Par.mul_right {L : ℕ} {b : Fin c → ℕ} {M M' : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k} (h : Par L b M)
    (h' : M'.BlockTriangular (Sum.elim (fun _ => L) b)) {r s : n ⊕ Fin c} (hs : s.isRight)
    (hrs : Sum.elim (fun _ => L) b s ≤ Sum.elim (fun _ => L) b r) : (M' * M) r s = M' r s := by
  have : (M' * M) r s = (M' * (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)) r s := by
    simp only [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun t _ => ?_
    rcases le_or_gt (Sum.elim (fun _ => L) b s) (Sum.elim (fun _ => L) b t) with ht | ht
    · rw [h t s (Or.inr hs) ht]
    · rw [h' (lt_of_lt_of_le ht hrs), zero_mul, zero_mul]
  rw [this, Matrix.mul_one]

theorem Par.blockTri_inv {L : ℕ} {b : Fin c → ℕ} {g : GL (n ⊕ Fin c) k} (h : Par L b g.val) :
    (g⁻¹).val.BlockTriangular (Sum.elim (fun _ => L) b) := by
  letI : Invertible g.val := g.invertible
  rw [Matrix.coe_units_inv]
  exact Matrix.blockTriangular_inv_of_blockTriangular h.blockTri

def parGroup (k : Type*) [Field k] (n : Type*) [Fintype n] [DecidableEq n] (L : ℕ) (b : Fin c → ℕ) :
    Subgroup (GL (n ⊕ Fin c) k) where
  carrier := {g | Par L b g.val}
  one_mem' := fun _ _ _ _ => rfl
  mul_mem' := by
    intro g h hg hh r s hor hrs
    rw [Units.val_mul]
    rcases hor with hr | hs
    · rw [Par.mul_left hg (Par.blockTri hh) hr hrs, hh r s (Or.inl hr) hrs]
    · rw [Par.mul_right hh (Par.blockTri hg) hs hrs, hg r s (Or.inr hs) hrs]
  inv_mem' := by
    intro g hg r s hor hrs
    rcases hor with hr | hs
    · rw [← Par.mul_left hg (Par.blockTri_inv hg) hr hrs, Units.mul_inv]
    · rw [← Par.mul_right hg (Par.blockTri_inv hg) hs hrs, Units.inv_mul]

theorem embX_mem (L : ℕ) (b : Fin c → ℕ) (x : GL n k) : embX c x ∈ parGroup k n L b := by
  intro r s hor _
  rw [embX_val]
  rcases r with r | r <;> rcases s with s | s <;> simp_all [Matrix.one_apply]

theorem toBlocks₁₁_mul {L : ℕ} {b : Fin c → ℕ} {g h : GL (n ⊕ Fin c) k} (hg : g ∈ parGroup k n L b)
    (hh : h ∈ parGroup k n L b) : (g * h).val.toBlocks₁₁ = g.val.toBlocks₁₁ * h.val.toBlocks₁₁ := by
  ext r s
  simp only [Units.val_mul, Matrix.toBlocks₁₁, Matrix.of_apply, Matrix.mul_apply, Fintype.sum_sum_type]
  rw [add_eq_left]
  refine Finset.sum_eq_zero fun t _ => ?_
  rcases le_total (b t) L with ht | ht
  · rw [hg (Sum.inl r) (Sum.inr t) (by simp) ht, Matrix.one_apply_ne (by simp), zero_mul]
  · rw [hh (Sum.inr t) (Sum.inl s) (by simp) ht, Matrix.one_apply_ne (by simp), mul_zero]

theorem exists_eq_embX_mul {L : ℕ} {b : Fin c → ℕ} {g : GL (n ⊕ Fin c) k} (hg : g ∈ parGroup k n L b) :
    ∃ (x : GL n k) (u : GL (n ⊕ Fin c) k), Uni (Sum.elim (fun _ => L) b) u.val ∧ g = embX c x * u := by
  have h1 : ((1 : GL (n ⊕ Fin c) k)).val.toBlocks₁₁ = 1 := by
    ext r s
    simp [Matrix.toBlocks₁₁, Matrix.one_apply]
  let x : GL n k := ⟨g.val.toBlocks₁₁, (g⁻¹).val.toBlocks₁₁,
    by rw [← toBlocks₁₁_mul hg (inv_mem hg), mul_inv_cancel, h1],
    by rw [← toBlocks₁₁_mul (inv_mem hg) hg, inv_mul_cancel, h1]⟩
  refine ⟨x, embX c x⁻¹ * g, ?_, by rw [map_inv, mul_inv_cancel_left]⟩
  have hm : embX c x⁻¹ * g ∈ parGroup k n L b := mul_mem (embX_mem L b _) hg
  have h11 : (embX c x⁻¹ * g).val.toBlocks₁₁ = 1 := by
    rw [toBlocks₁₁_mul (embX_mem L b _) hg, embX_val, Matrix.toBlocks_fromBlocks₁₁]
    exact x.inv_mul
  intro r s hrs
  by_cases hor : r.isRight ∨ s.isRight
  · exact hm r s hor hrs
  · rcases r with r | r <;> rcases s with s | s
    · have := congrFun (congrFun h11 r) s
      simp only [Matrix.toBlocks₁₁, Matrix.of_apply] at this
      rw [this]
      simp [Matrix.one_apply]
    all_goals simp at hor

theorem embX_mem_R (p : ℕ) (x : GL n k) : embX c x ∈ R k n c p :=
  Subgroup.mem_sup_left ⟨x, rfl⟩

theorem R_le {L p : ℕ} {b : Fin c → ℕ} (h : N k n c p ≤ parGroup k n L b) : R k n c p ≤ parGroup k n L b := by
  refine sup_le ?_ h
  rintro _ ⟨x, rfl⟩
  exact embX_mem L b x

theorem mem_R_iff_and_mem_RFJ_iff : ∀ (k : Type) [Field k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ), (∀ g : GL (n ⊕ Fin c) k, g ∈ R k n c ρ ↔ ∀ r s : n ⊕ Fin c, (r.isRight ∨ s.isRight) → Sum.elim (fun _ => ρ) (fun i : Fin c => i.val + 1) s ≤ Sum.elim (fun _ => ρ) (fun i : Fin c => i.val + 1) r → g.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s) ∧ (1 ≤ ρ → ρ < c → ∀ g : GL (n ⊕ Fin c) k, g ∈ RFJ k n c ρ ↔ ∀ r s : n ⊕ Fin c, (r.isRight ∨ s.isRight) → Sum.elim (fun _ => 2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1)) s ≤ Sum.elim (fun _ => 2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1)) r → g.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s) := by
  intro k _ n _ _ c ρ
  refine ⟨fun g => ⟨fun hg => ?_, fun hg => ?_⟩, fun h1 hc g => ⟨fun hg => ?_, fun hg => ?_⟩⟩
  · exact R_le (L := ρ) (b := fun i : Fin c => i.val + 1)
      (fun u hu r s _ hrs => (mem_N_iff u).1 hu r s hrs) hg
  · obtain ⟨x, u, hu, rfl⟩ := exists_eq_embX_mul (L := ρ) (b := fun i : Fin c => i.val + 1) hg
    exact mul_mem (embX_mem_R ρ x) (Subgroup.mem_sup_right ((mem_N_iff u).2 hu))
  · have hN : NFJ k n c ρ ≤ parGroup k n (2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1)) :=
      fun u hu r s _ hrs => ((GlobalTheory.RootEx.FJUnipotent.fj_unipotent k n c ρ h1 hc).2.1 u).1 hu r s hrs
    exact sup_le (R_le (le_sup_left.trans hN)) (R_le (le_sup_right.trans hN)) hg
  · obtain ⟨x, u, hu, rfl⟩ :=
      exists_eq_embX_mul (L := 2 * ρ + 1) (b := fun i : Fin c => 2 * (i.val + 1)) hg
    have hN : NFJ k n c ρ ≤ RFJ k n c ρ := sup_le_sup le_sup_right le_sup_right
    exact mul_mem (Subgroup.mem_sup_left (embX_mem_R ρ x))
      (hN (((GlobalTheory.RootEx.FJUnipotent.fj_unipotent k n c ρ h1 hc).2.1 u).2 hu))

end GlobalTheory.RootEx.ParabolicEntries
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemRootExchangeParabolicAndFourierJacobiIffEntriStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_rootExchangeParabolic_and_fourierJacobi_iff_entries : ∀ (k : Type) [Field k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ), (∀ g : GL (n ⊕ Fin c) k, g ∈ R k n c ρ ↔ ∀ r s : n ⊕ Fin c, (r.isRight ∨ s.isRight) → Sum.elim (fun _ => ρ) (fun i : Fin c => i.val + 1) s ≤ Sum.elim (fun _ => ρ) (fun i : Fin c => i.val + 1) r → g.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s) ∧ (1 ≤ ρ → ρ < c → ∀ g : GL (n ⊕ Fin c) k, g ∈ RFJ k n c ρ ↔ ∀ r s : n ⊕ Fin c, (r.isRight ∨ s.isRight) → Sum.elim (fun _ => 2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1)) s ≤ Sum.elim (fun _ => 2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1)) r → g.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s) := by
  first | exact @GlobalTheory.RootEx.ParabolicEntries.mem_R_iff_and_mem_RFJ_iff | exact GlobalTheory.RootEx.ParabolicEntries.mem_R_iff_and_mem_RFJ_iff | (intros; apply GlobalTheory.RootEx.ParabolicEntries.mem_R_iff_and_mem_RFJ_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricDatumEigenvectorTwoBlockParahoric
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricDatumEigenvectorTwoBlockParahoric
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

noncomputable section

namespace GlobalTheory.DatumEigen

variable {k : Type} [Field k] [ValuativeRel k]

theorem val_det_sub_lt {m : Type} [Fintype m] [DecidableEq m] {M N : Matrix m m k}
    (hM : ∀ i j, M i j ∈ 𝒪[k]) (hN : ∀ i j, N i j ∈ 𝒪[k]) (h : ∀ i j, valuation k (M i j - N i j) < 1) :
    valuation k (M.det - N.det) < 1 := by
  have key : ∀ x : 𝒪[k], IsLocalRing.residue 𝒪[k] x = 0 ↔ valuation k (algebraMap 𝒪[k] k x) < 1 := by
    intro x
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one]
    exact ⟨fun h => lt_of_le_of_ne x.2 h, fun h => h.ne⟩
  let M' : Matrix m m 𝒪[k] := fun i j => ⟨M i j, hM i j⟩
  let N' : Matrix m m 𝒪[k] := fun i j => ⟨N i j, hN i j⟩
  have eM : M = (algebraMap 𝒪[k] k).mapMatrix M' := rfl
  have eN : N = (algebraMap 𝒪[k] k).mapMatrix N' := rfl
  have hres : (IsLocalRing.residue 𝒪[k]).mapMatrix M' = (IsLocalRing.residue 𝒪[k]).mapMatrix N' := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [← sub_eq_zero, ← map_sub, key]
    exact h i j
  rw [eM, eN, ← RingHom.map_det, ← RingHom.map_det, ← map_sub, ← key, map_sub, RingHom.map_det,
    RingHom.map_det, hres, sub_self]

theorem val_mul_lt {a b : k} (ha : valuation k a ≤ 1) (hb : valuation k b < 1) : valuation k (a * b) < 1 := by
  rw [map_mul]
  exact (mul_le_of_le_one_left' ha).trans_lt hb

theorem det_int {m : Type} [Fintype m] [DecidableEq m] {M : Matrix m m k} (hM : ∀ i j, M i j ∈ 𝒪[k]) :
    M.det ∈ 𝒪[k] := by
  let M' : Matrix m m 𝒪[k] := fun i j => ⟨M i j, hM i j⟩
  have eM : M = (algebraMap 𝒪[k] k).mapMatrix M' := rfl
  rw [eM, ← RingHom.map_det]
  exact (M'.det).2

theorem eq_one_of_mul {a b : ValueGroupWithZero k} (ha : a ≤ 1) (hb : b ≤ 1) (h : a * b = 1) : a = 1 := by
  refine le_antisymm ha ?_
  by_contra hlt
  replace hlt := not_le.1 hlt
  have : a * b < 1 := (mul_le_of_le_one_right' hb).trans_lt hlt
  exact this.ne h

theorem tame_eq {ξ : kˣ →* ℂˣ} (hξ : IsTame ξ) {a b : kˣ} (hb : valuation k (b : k) = 1)
    (h : valuation k ((a : k) - b) < 1) : ξ a = ξ b := by
  have hb0 : (b : k) ≠ 0 := b.ne_zero
  have h1 : ξ (a * b⁻¹) = 1 := by
    apply hξ
    have e : ((a * b⁻¹ : kˣ) : k) - 1 = ((a : k) - b) * (b : k)⁻¹ := by
      rw [Units.val_mul, Units.val_inv_eq_inv_val]; field_simp
    rw [e, map_mul, map_inv₀, hb, inv_one, mul_one]
    exact h
  rw [map_mul, map_inv, mul_inv_eq_one] at h1
  exact h1

variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Blocks

variable {A D E : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]

theorem int_of_mem {j : GL (A ⊕ D) k} (hj : j ∈ parahoric k A D) (i l : A ⊕ D) : j.val i l ∈ 𝒪[k] :=
  ((GlobalTheory.SplitFlip.mem_KO_iff j).1 (mem_parahoric.1 hj).1).1 i l

theorem det_cong {j : GL (A ⊕ D) k} (hj : j ∈ parahoric k A D) :
    valuation k (j.val.det - j.val.toBlocks₁₁.det * j.val.toBlocks₂₂.det) < 1 := by
  have hJ := int_of_mem hj
  have hl := (mem_parahoric.1 hj).2
  rw [← det_fromBlocks_zero₂₁ j.val.toBlocks₁₁ j.val.toBlocks₁₂ j.val.toBlocks₂₂]
  refine val_det_sub_lt hJ ?_ ?_
  · rintro (i | i) (l | l) <;> simp [toBlocks₁₁, toBlocks₁₂, toBlocks₂₂, hJ]
  · rintro (i | i) (l | l) <;> simp [toBlocks₁₁, toBlocks₁₂, toBlocks₂₂, hl]

theorem val_det_blocks {j : GL (A ⊕ D) k} (hj : j ∈ parahoric k A D) :
    valuation k j.val.toBlocks₁₁.det = 1 ∧ valuation k j.val.toBlocks₂₂.det = 1 := by
  have hJ := int_of_mem hj
  have h1 : valuation k j.val.det = 1 := by
    have := nabs_det_of_mem_KO (mem_parahoric.1 hj).1
    rwa [nabs_eq_one_iff] at this
  have h2 := Valuation.map_eq_of_sub_lt _ (show valuation k (j.val.toBlocks₁₁.det * j.val.toBlocks₂₂.det
      - j.val.det) < valuation k j.val.det by
    rw [h1, ← Valuation.map_neg, neg_sub]; exact det_cong hj)
  rw [h1, map_mul] at h2
  have i11 : valuation k j.val.toBlocks₁₁.det ≤ 1 := det_int fun i l => hJ _ _
  have i22 : valuation k j.val.toBlocks₂₂.det ≤ 1 := det_int fun i l => hJ _ _
  exact ⟨eq_one_of_mul i11 i22 h2, eq_one_of_mul i22 i11 (by rw [mul_comm]; exact h2)⟩

omit [Fintype E] [DecidableEq E] in
theorem inSupp_mul {x : Matrix (A ⊕ E) (A ⊕ D) k} (hx : InSupp x) {j : GL (A ⊕ D) k}
    (hj : j ∈ parahoric k A D) : InSupp (x * j.val) ∧
      valuation k ((x * j.val).toBlocks₁₁.det - x.toBlocks₁₁.det * j.val.toBlocks₁₁.det) < 1 := by
  have hJ := int_of_mem hj
  have hl := (mem_parahoric.1 hj).2
  obtain ⟨hxi, hxd, hxl⟩ := hx
  have hprod : ∀ i l, (x * j.val) i l ∈ 𝒪[k] := fun i l => by
    rw [Matrix.mul_apply]; exact sum_mem fun m _ => mul_mem (hxi i m) (hJ m l)
  have hcong : valuation k ((x * j.val).toBlocks₁₁.det - x.toBlocks₁₁.det * j.val.toBlocks₁₁.det) < 1 := by
    rw [← det_mul]
    refine val_det_sub_lt (fun i l => hprod _ _) (fun i l => ?_) (fun i l => ?_)
    · rw [Matrix.mul_apply]; exact sum_mem fun m _ => mul_mem (hxi _ _) (hJ _ _)
    · simp only [toBlocks₁₁, of_apply, Matrix.mul_apply, Fintype.sum_sum_type, add_sub_cancel_left]
      exact Valuation.map_sum_lt _ one_ne_zero fun m _ => val_mul_lt (hxi _ _) (hl _ _)
  have hd1 : valuation k (x.toBlocks₁₁.det * j.val.toBlocks₁₁.det) = 1 := by
    rw [map_mul, hxd, one_mul, (val_det_blocks hj).1]
  refine ⟨⟨hprod, ?_, ?_⟩, hcong⟩
  · rw [← hd1]
    refine Valuation.map_eq_of_sub_lt _ ?_
    rw [hd1]; exact hcong
  · intro e a
    rw [Matrix.mul_apply, Fintype.sum_sum_type]
    refine Valuation.map_add_lt _ (Valuation.map_sum_lt _ one_ne_zero fun m _ => ?_)
      (Valuation.map_sum_lt _ one_ne_zero fun m _ => ?_)
    · rw [mul_comm]; exact val_mul_lt (hJ _ _) (hxl _ _)
    · exact val_mul_lt (hxi _ _) (hl _ _)

end Blocks

theorem om_datum : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (A D E : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
    (ξ μ₀ : kˣ →* ℂˣ), IsTame ξ → IsUnram μ₀ →
    ∀ j ∈ parahoric k A D, ∀ d : kˣ, (d : k) = (j : Matrix (A ⊕ D) (A ⊕ D) k).toBlocks₂₂.det →
    om (μ₀ * ξ) j (1 : GL (A ⊕ E) k) (datum ξ : Matrix (A ⊕ E) (A ⊕ D) k → ℂ) = fun x => (ξ d : ℂ) * datum ξ x := by
  intro k _ _ _ _ A D E _ _ _ _ _ _ ξ μ₀ hξ hμ j hj d hd
  funext x
  have hK := (mem_parahoric.1 hj).1
  have hdetv : valuation k (GeneralLinearGroup.det j : k) = 1 := (nabs_eq_one_iff _).1 (nabs_det_of_mem_KO hK)
  have hμj : μ₀ (GeneralLinearGroup.det j) = 1 := hμ _ hdetv
  simp only [om, nabs_det_of_mem_KO hK, MonoidHom.mul_apply, hμj, one_mul, map_one, mul_one, inv_one,
    Units.val_one, Real.one_rpow, Complex.ofReal_one]
  rw [show nabs k 1 = 1 by simp [nabs], Real.one_rpow, Complex.ofReal_one, mul_one, Matrix.one_mul]
  unfold datum
  obtain ⟨h11, h22⟩ := val_det_blocks hj
  by_cases hx : InSupp x
  · obtain ⟨hs, hc⟩ := inSupp_mul hx hj
    have n11 : j.val.toBlocks₁₁.det ≠ 0 := fun h0 => by rw [h0, map_zero] at h11; exact zero_ne_one h11
    set u : kˣ := Units.mk0 _ n11 with hu
    have hdv : valuation k (d : k) = 1 := by rw [hd]; exact h22
    have t1 : ξ (GeneralLinearGroup.det j) = ξ (u * d) := by
      refine tame_eq hξ (by rw [Units.val_mul, map_mul, hdv, mul_one]; exact h11) ?_
      rw [Units.val_mul, hd, GeneralLinearGroup.val_det_apply]
      exact det_cong hj
    have t2 : ξ (Units.mk0 _ hs.det_ne) = ξ (Units.mk0 _ hx.det_ne * u) := by
      refine tame_eq hξ (by rw [Units.val_mul, map_mul, Units.val_mk0, hx.2.1, one_mul]; exact h11) ?_
      rw [Units.val_mul, Units.val_mk0, Units.val_mk0]
      exact hc
    rw [dite_eq_left hs, dite_eq_left hx, t1, t2, map_mul, map_mul]
    simp only [Units.val_mul, _root_.mul_inv_rev, Units.val_inv_eq_inv_val]
    have a1 : (ξ u : ℂ) ≠ 0 := Units.ne_zero _
    field_simp
  · have hs : ¬ InSupp (x * j.val) := fun hs => by
      have := (inSupp_mul hs (inv_mem hj)).1
      rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one] at this
      exact hx this
    rw [dite_eq_right hs, dite_eq_right hx, mul_zero, mul_zero]

end GlobalTheory.DatumEigen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricDatumEigenvectorTwoBlockParahoricStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parahoricDatum_eigenvector_twoBlockParahoric : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (A D E : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
    (ξ μ₀ : kˣ →* ℂˣ), IsTame ξ → IsUnram μ₀ →
    ∀ j ∈ parahoric k A D, ∀ d : kˣ, (d : k) = (j : Matrix (A ⊕ D) (A ⊕ D) k).toBlocks₂₂.det →
    om (μ₀ * ξ) j (1 : GL (A ⊕ E) k) (datum ξ : Matrix (A ⊕ E) (A ⊕ D) k → ℂ) = fun x => (ξ d : ℂ) * datum ξ x := by
  first | exact @GlobalTheory.DatumEigen.om_datum | exact GlobalTheory.DatumEigen.om_datum | (intros; apply GlobalTheory.DatumEigen.om_datum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteQuotientCosetsScaledStandardLatticeBox
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteQuotientCosetsScaledStandardLatticeBox
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

namespace GlobalTheory.BoxCosets

theorem finite_cosets (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] (c₁ c₂ : kˣ) :
    {yb : (n → k) ⧸ box n c₂ | ∃ y ∈ box n c₁, Submodule.Quotient.mk y = yb}.Finite := by
  have e : ∀ c : kˣ, (box n c : Set (n → k)) = Set.pi Set.univ (fun _ => cball c) := by
    intro c
    ext y
    simp only [Set.mem_pi, Set.mem_univ, true_implies]
    rfl
  have hc : IsCompact (box n c₁ : Set (n → k)) := by
    rw [e]; exact isCompact_univ_pi fun _ => isCompact_cball c₁
  have ho : IsOpen (box n c₂ : Set (n → k)) := by
    rw [e]; exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_cball c₂
  obtain ⟨t, -, ht⟩ := hc.elim_nhds_subcover
    (fun x => (fun y => y - x) ⁻¹' (box n c₂ : Set (n → k))) (by
      intro x _
      refine (ho.preimage (continuous_id.sub continuous_const)).mem_nhds ?_
      simp)
  refine (t.finite_toSet.image (fun x => (Submodule.Quotient.mk x : (n → k) ⧸ box n c₂))).subset ?_
  rintro _ ⟨y, hy, rfl⟩
  have := ht hy
  simp only [Set.mem_iUnion] at this
  obtain ⟨x, hx, hxy⟩ := this
  exact ⟨x, hx, ((Submodule.Quotient.eq _).2 hxy).symm⟩

end GlobalTheory.BoxCosets
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteQuotientCosetsScaledStandardLatticeBoxStatement
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_quotient_cosets_scaledStandardLatticeBox : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] (c₁ c₂ : kˣ), {yb : (n → k) ⧸ box n c₂ | ∃ y ∈ box n c₁, Submodule.Quotient.mk y = yb}.Finite := by
  first | exact @GlobalTheory.BoxCosets.finite_cosets | exact GlobalTheory.BoxCosets.finite_cosets | (intros; apply GlobalTheory.BoxCosets.finite_cosets <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsOpenIsCompactTwoBlockParahoricSubgroup
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsOpenIsCompactTwoBlockParahoricSubgroup
noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection
  GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

namespace GlobalTheory.ParahoricOpenCompact

theorem KOne_le_parahoric (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] :
    KOne k (A ⊕ D) ≤ parahoric k A D := by
  intro g hg
  refine mem_parahoric.2 ⟨StepData.KOne_le_KO hg, fun i j => ?_⟩
  have h := StepData.mem_KOne.1 hg
  have h' : valuation k ((g.val - 1) (.inr i) (.inl j)) < 1 := h _ _
  simpa using h'

theorem isOpen_isCompact_parahoric : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D],
    IsOpen (parahoric k A D : Set (GL (A ⊕ D) k)) ∧ IsCompact (parahoric k A D : Set (GL (A ⊕ D) k)) := by
  intro k _ _ _ _ A D _ _ _ _
  have ho : IsOpen (parahoric k A D : Set (GL (A ⊕ D) k)) :=
    Subgroup.isOpen_mono (KOne_le_parahoric k A D) StepData.isOpen_KOne
  exact ⟨ho, SplitFlip.isCompact_KO.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ ho)
    fun _ hg => (mem_parahoric.1 hg).1⟩

end GlobalTheory.ParahoricOpenCompact
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsOpenIsCompactTwoBlockParahoricSubgroupStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_isCompact_twoBlockParahoricSubgroup : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D],
    IsOpen (parahoric k A D : Set (GL (A ⊕ D) k)) ∧ IsCompact (parahoric k A D : Set (GL (A ⊕ D) k)) := by
  first | exact @GlobalTheory.ParahoricOpenCompact.isOpen_isCompact_parahoric | exact GlobalTheory.ParahoricOpenCompact.isOpen_isCompact_parahoric | (intros; apply GlobalTheory.ParahoricOpenCompact.isOpen_isCompact_parahoric <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatrixEntrywiseProductMeasureUniformizerPowerBox
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatrixEntrywiseProductMeasureUniformizerPowerBox
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound
open scoped NNReal ENNReal

noncomputable section

namespace GlobalTheory.BoxVolume

theorem prod_zpow_nnreal {ι : Type} (d : ℝ≥0) (hd : d ≠ 0) (f : ι → ℤ) (s : Finset ι) :
    ∏ i ∈ s, d ^ f i = d ^ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hd]

theorem volM_box : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ϖ : kˣ),
    valuation k (ϖ : k) = uniformizer k →
    ∀ (A D : Type) [Fintype A] [Fintype D] (c : A → D → ℤ),
    volM ν A D {y | ∀ i j, valuation k (y i j) ≤ valuation k ((ϖ : k) ^ c i j)} =
      ν (𝒪[k] : Set k) ^ (Fintype.card A * Fintype.card D) *
        ENNReal.ofReal ((resCard k : ℝ) ^ (-∑ i, ∑ j, c i j)) := by
  intro k _ _ _ _ _ _ ν _ ϖ hϖ A D _ _ c
  haveI := secondCountable k
  haveI := t2Space k
  have hset : ({y : Matrix A D k | ∀ i j, valuation k (y i j) ≤ valuation k ((ϖ : k) ^ c i j)} :
      Set (A → D → k)) = Set.univ.pi fun i => Set.univ.pi fun j => cball (ϖ ^ c i j) := by
    ext y
    simp only [Set.mem_univ_pi, cball, Set.mem_setOf_eq, Units.val_zpow_eq_zpow_val]
    rfl
  set d : ℝ≥0 := distribHaarChar k ϖ with hd
  have hdq : (d : ℝ) = (resCard k : ℝ)⁻¹ := nabs_unif hϖ
  have hd0 : d ≠ 0 := (distribHaarChar_pos (A := k) (g := ϖ)).ne'
  have hcb : ∀ i j, ν (cball (ϖ ^ c i j)) = ((d ^ c i j : ℝ≥0) : ℝ≥0∞) * ν (𝒪[k] : Set k) := by
    intro i j
    rw [measure_cball, map_zpow]
  rw [volM]
  erw [hset, Measure.pi_pi]
  simp_rw [Measure.pi_pi, hcb, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  rw [← pow_mul, mul_comm (ν _ ^ _)]
  rw [Nat.mul_comm (Fintype.card D)]
  congr 1
  have hz : ∏ i, ∏ j, d ^ c i j = d ^ (∑ i, ∑ j, c i j) := by
    simp_rw [prod_zpow_nnreal d hd0]
  have hz' : (∏ i, ∏ j, ((d ^ c i j : ℝ≥0) : ℝ≥0∞)) =
      ((d ^ (∑ i, ∑ j, c i j) : ℝ≥0) : ℝ≥0∞) := by
    exact_mod_cast hz
  rw [hz', ← ENNReal.ofReal_coe_nnreal]
  congr 1
  rw [NNReal.coe_zpow, hdq, _root_.inv_zpow']

end GlobalTheory.BoxVolume
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatrixEntrywiseProductMeasureUniformizerPowerBoxStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrixEntrywiseProductMeasure_uniformizer_power_box : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ϖ : kˣ),
    valuation k (ϖ : k) = uniformizer k →
    ∀ (A D : Type) [Fintype A] [Fintype D] (c : A → D → ℤ),
    volM ν A D {y | ∀ i j, valuation k (y i j) ≤ valuation k ((ϖ : k) ^ c i j)} =
      ν (𝒪[k] : Set k) ^ (Fintype.card A * Fintype.card D) *
        ENNReal.ofReal ((resCard k : ℝ) ^ (-∑ i, ∑ j, c i j)) := by
  first | exact @GlobalTheory.BoxVolume.volM_box | exact GlobalTheory.BoxVolume.volM_box | (intros; apply GlobalTheory.BoxVolume.volM_box <;> assumption)
end
end
