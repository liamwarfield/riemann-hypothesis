module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CapelliLowestGelfandConj
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselCharacterLocalElementEqSimpleEntrySum

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLocalModelSliceSourceLine
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLocalModelSliceSourceLine
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod

noncomputable section
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SliceModel

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)

theorem ι_e (x : k) : p.e * p.ι x = p.ι x := by
  rw [← p.ι_π (p.ι x), p.π_ι]

theorem ι_mul (x y : k) : p.ι (x * y) = p.ι x * p.ι y := by
  have h1 : p.ι (x * y) = p.ι (p.π (p.ι x * p.ι y)) := by rw [map_mul p.π, p.π_ι, p.π_ι]
  rw [h1, p.ι_π, ← mul_assoc, ι_e]

theorem ι_mul_right (x : k) (z : AE D) : p.ι x * z = p.ι (x * p.π z) := by
  rw [ι_mul, p.ι_π, ← mul_assoc, mul_comm (p.ι x) p.e, ι_e]

theorem ι_mul_left (x : k) (z : AE D) : z * p.ι x = p.ι (p.π z * x) := by
  rw [mul_comm, ι_mul_right, mul_comm]

def prH : D.host.E →+* k := p.π.comp (incA D)

theorem prH_apply (a : D.host.E) : prH p a = p.pr a := rfl

theorem map_ι_mul_rat {l m o : Type} [Fintype m] (M : Matrix l m k) (N : Matrix m o D.host.E) :
    M.map p.ι * N.map (incA D) = (M * N.map (prH p)).map p.ι := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, ι_mul_right]
  rfl

section Frames

variable {ρ : ℕ} (B : BesLev D ρ) (S : HSp D) (s : k) {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n)

theorem qA_iA_k : B.o.qA.map (prH p) * B.o.iA.map (prH p) = 1 := by
  rw [← Matrix.map_mul, B.o.qA_iA, Matrix.map_one _ (map_zero _) (map_one _)]

theorem qA_iB_k : B.o.qA.map (prH p) * B.o.iB.map (prH p) = 0 := by
  rw [← Matrix.map_mul, B.o.qA_iB, Matrix.map_zero _ (map_zero _)]

variable {p B s FA F₀}

theorem β_eq (h : p.IsCoreFrame B s FA F₀) :
    F₀.β = B.o.iA.map (prH p) * fromCols FA.β 0 +
      B.o.iB.map (prH p) * fromCols 0 (Matrix.of fun i (_ : Unit) => s * prH p (B.ζ i)) := by
  ext r j
  rcases j with a | u
  · rw [h.1 r a]
    simp [Matrix.mul_apply, fromCols]
    rfl
  · rw [h.2 r]
    have := RingHom.map_mulVec (prH p) B.o.iB B.ζ r
    simp only [vecB] at *
    rw [prH_apply] at this
    rw [this]
    simp [Matrix.mul_apply, fromCols, Matrix.mulVec, dotProduct, Finset.mul_sum]
    ring_nf

theorem qA_β (h : p.IsCoreFrame B s FA F₀) : B.o.qA.map (prH p) * F₀.β = fromCols FA.β 0 := by
  rw [β_eq h, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, qA_iA_k, qA_iB_k, Matrix.one_mul, Matrix.zero_mul,
    add_zero]

theorem γ_qA (h : p.IsCoreFrame B s FA F₀) : FA.γ * B.o.qA.map (prH p) = F₀.γ.toRows₁ := by
  have e : FA.γ * B.o.qA.map (prH p) = FA.γ * B.o.qA.map (prH p) * (F₀.β * F₀.γ) := by rw [F₀.βγ, Matrix.mul_one]
  rw [e, ← Matrix.mul_assoc, Matrix.mul_assoc FA.γ, qA_β h, Matrix.mul_fromCols, FA.γβ, Matrix.mul_zero,
    ← Matrix.fromRows_toRows F₀.γ, Matrix.fromCols_mul_fromRows, Matrix.one_mul, Matrix.zero_mul, add_zero, Matrix.toRows₁_fromRows]

theorem γ_iA (h : p.IsCoreFrame B s FA F₀) : F₀.γ * B.o.iA.map (prH p) = fromRows FA.γ (0 : Matrix Unit (Fin B.A.rank) k) := by
  have e1 : B.o.iA.map (prH p) * FA.β = F₀.β * (fromRows (1 : Matrix n' n' k) (0 : Matrix Unit n' k) : Matrix (n' ⊕ Unit) n' k) := by
    rw [← Matrix.fromCols_toCols F₀.β, Matrix.fromCols_mul_fromRows, Matrix.mul_one, Matrix.mul_zero, add_zero]
    ext r a
    exact (h.1 r a).symm
  calc F₀.γ * B.o.iA.map (prH p) = F₀.γ * (B.o.iA.map (prH p) * FA.β) * FA.γ := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, FA.βγ, Matrix.mul_one]
    _ = (F₀.γ * F₀.β) * (fromRows (1 : Matrix n' n' k) (0 : Matrix Unit n' k) : Matrix (n' ⊕ Unit) n' k) * FA.γ := by
        rw [e1]; simp only [Matrix.mul_assoc]
    _ = fromRows FA.γ 0 := by rw [F₀.γβ, Matrix.one_mul, Matrix.fromRows_mul, Matrix.one_mul, Matrix.zero_mul]

theorem up_slice (h : p.IsCoreFrame B s FA F₀) (x : Matrix n n' k) :
    (B.o.resS S).symm (p.up FA FS x, 0) = p.up F₀ FS (fromCols x 0) := by
  have e : fromCols x (0 : Matrix n Unit k) * F₀.γ = x * F₀.γ.toRows₁ := by
    conv_lhs => rw [← Matrix.fromRows_toRows F₀.γ]
    rw [Matrix.fromCols_mul_fromRows, Matrix.zero_mul, add_zero]
  rw [OrthDec.resS_symm_apply, Matrix.zero_mul, add_zero, OrthDec.pA, GlobalTheory.MixModel.rat, Place.up, Place.up, map_ι_mul_rat,
    Matrix.mul_assoc, γ_qA h, Matrix.mul_assoc FS.β (fromCols x 0) F₀.γ, e, Matrix.mul_assoc]

theorem res_up (h : p.IsCoreFrame B s FA F₀) (x : Matrix n (n' ⊕ Unit) k) :
    (B.o.resS S (p.up F₀ FS x)).1 = p.up FA FS x.toCols₁ := by
  have e : x * fromRows FA.γ (0 : Matrix Unit (Fin B.A.rank) k) = x.toCols₁ * FA.γ := by
    conv_lhs => rw [← Matrix.fromCols_toCols x]
    rw [Matrix.fromCols_mul_fromRows, Matrix.mul_zero, add_zero]
  show (p.up F₀ FS x) * B.o.jA = _
  rw [OrthDec.jA, GlobalTheory.MixModel.rat, Place.up, Place.up, map_ι_mul_rat, Matrix.mul_assoc, γ_iA h, Matrix.mul_assoc, e,
    Matrix.mul_assoc]

end Frames

section Tensor

variable (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

def splitH : Matrix n (n' ⊕ Unit) k ≃ₜ Matrix n n' k × (n → k) where
  toFun x := (x.toCols₁, fun r => x r (Sum.inr ()))
  invFun q := fromCols q.1 (Matrix.of fun r (_ : Unit) => q.2 r)
  left_inv x := by
    ext r j
    rcases j with j | j <;> rfl
  right_inv q := rfl
  continuous_toFun := (continuous_matrix fun i j => continuous_id.matrix_elem i (Sum.inl j)).prodMk
    (continuous_pi fun r => continuous_id.matrix_elem r (Sum.inr ()))
  continuous_invFun := continuous_matrix fun i j => by
    rcases j with j | j
    · exact continuous_fst.matrix_elem i j
    · exact (continuous_apply i).comp continuous_snd

variable {n n'}

def tens (a : (n → k) → ℂ) (ha : a ∈ SB (n → k)) : SB (Matrix n n' k) →ₗ[ℂ] SB (Matrix n (n' ⊕ Unit) k) where
  toFun Ξ := GlobalTheory.LocFlat.CFac.comapH (splitH n n') (GlobalTheory.LocFlat.CFac.prodSB Ξ ⟨a, ha⟩)
  map_add' Ξ Ξ' := by
    ext x
    simp [GlobalTheory.LocFlat.CFac.comapH_apply, GlobalTheory.LocFlat.CFac.prodSB_apply, add_mul]
  map_smul' c Ξ := by
    ext x
    simp [GlobalTheory.LocFlat.CFac.comapH_apply, GlobalTheory.LocFlat.CFac.prodSB_apply, mul_assoc]

theorem tens_apply (a : (n → k) → ℂ) (ha : a ∈ SB (n → k)) (Ξ : SB (Matrix n n' k)) (x : Matrix n (n' ⊕ Unit) k) :
    (tens a ha Ξ).1 x = Ξ.1 x.toCols₁ * a fun r => x r (Sum.inr ()) := rfl

end Tensor

theorem symplO_zero_right'' (S T : HSp D) (x : WO S T) : symplO S T x 0 = 0 := by
  simp [symplO, hO]

theorem exists_isModel_slice : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ρ : ℕ) (B : BesLev D ρ) (S : HSp D) (s : k) (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n), p.IsCoreFrame B s FA F₀ → ∀ T₀, p.IsModel ψ F₀ FS T₀ → ∀ (a : (n → k) → ℂ), a ∈ SB _ → ∀ v : WO B.L S, ∃ T₁, p.IsModel ψ FA FS T₁ ∧ ∀ (Ξ : SB (Matrix n n' k)) (Ψ : SB (Matrix n (n' ⊕ Unit) k)), (∀ x, Ψ.1 x = Ξ.1 x.toCols₁ * a fun r => x r (Sum.inr ())) → ∀ u, T₀ Ψ ((B.o.resS S).symm (u, v)) = T₁ Ξ u := by
  intro D k _ _ _ _ p ψ n n' _ _ _ _ ρ B S s FA F₀ FS h T₀ hT a ha v
  let T₁ : SB (Matrix n n' k) →ₗ[ℂ] (WO B.A S → ℂ) :=
    (LinearMap.funLeft ℂ ℂ fun u => (B.o.resS S).symm (u, v)) ∘ₗ T₀ ∘ₗ tens a ha
  have hT₁ : ∀ Φ u, T₁ Φ u = T₀ (tens a ha Φ) ((B.o.resS S).symm (u, v)) := fun _ _ => rfl
  refine ⟨T₁, ⟨fun Φ => ?_, fun x Φ Φ' hΦ => ?_, fun y hy Φ Φ' hΦ => ?_⟩, fun Ξ Ψ hΨ u => ?_⟩
  · exact GlobalTheory.BoxSlice.isThetaFunO_slice_left B.o (hT.theta (tens a ha Φ)) v
  · have h1 : ∀ t, (tens a ha Φ').1 t = (tens a ha Φ).1 (t + fromCols x 0) := by
      intro t
      rw [tens_apply, tens_apply, hΦ]
      congr 2
      ext i j; simp [Matrix.toCols₁, fromCols]
    have h2 := hT.trans (fromCols x 0) _ _ h1
    funext u
    rw [hT₁, h2, ← up_slice S FS h x]
    simp only [heisO, hT₁]
    rw [← map_add (B.o.resS S).symm, Prod.mk_add_mk, add_zero, B.o.symplOH_resS, AddEquiv.apply_symm_apply,
      AddEquiv.apply_symm_apply, GlobalTheory.MixModel.symplOH_zero_right, add_zero]
  · have hY : IsHalf (cA D p.e) ((B.o.resS S).symm (y, 0)) := by
      intro i j
      rw [OrthDec.resS_symm_apply, Matrix.zero_mul, add_zero]
      simp only [Matrix.mul_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [← mul_assoc, hy i l]
    have h1 : ∀ t, (tens a ha Φ').1 t =
        ψ (symplO B.V₀ S (p.up F₀ FS t) ((B.o.resS S).symm (y, 0))) * (tens a ha Φ).1 t := by
      intro t
      rw [tens_apply, tens_apply, hΦ, B.o.symplO_resS, AddEquiv.apply_symm_apply, res_up S FS h,
        symplO_zero_right'', add_zero, mul_assoc]
    have h2 := hT.modul _ hY _ _ h1
    funext u
    rw [hT₁, h2]
    simp only [heisO, hT₁]
    rw [← map_add (B.o.resS S).symm, Prod.mk_add_mk, add_zero, B.o.symplOH_resS, AddEquiv.apply_symm_apply,
      AddEquiv.apply_symm_apply, GlobalTheory.MixModel.symplOH_zero_right, add_zero]
  · have e : Ψ = tens a ha Ξ := Subtype.ext (funext fun x => (hΨ x).trans (tens_apply a ha Ξ x).symm)
    rw [e, hT₁]

end GlobalTheory.SliceModel

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLocalModelSliceSourceLineStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_model_slice_source_line : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ρ : ℕ) (B : BesLev D ρ) (S : HSp D) (s : k) (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n), p.IsCoreFrame B s FA F₀ → ∀ T₀, p.IsModel ψ F₀ FS T₀ → ∀ (a : (n → k) → ℂ), a ∈ SB _ → ∀ v : WO B.L S, ∃ T₁, p.IsModel ψ FA FS T₁ ∧ ∀ (Ξ : SB (Matrix n n' k)) (Ψ : SB (Matrix n (n' ⊕ Unit) k)), (∀ x, Ψ.1 x = Ξ.1 x.toCols₁ * a fun r => x r (Sum.inr ())) → ∀ u, T₀ Ψ ((B.o.resS S).symm (u, v)) = T₁ Ξ u := by
  first | exact @GlobalTheory.SliceModel.exists_isModel_slice | exact GlobalTheory.SliceModel.exists_isModel_slice | (intros; apply GlobalTheory.SliceModel.exists_isModel_slice <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IndexEquivalenceReduction
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.StepData NumberField
open scoped Classical

namespace GlobalTheory.FunObj.TieLev

theorem mem_iter_gen {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {R t : Type} [Fintype R] [DecidableEq R] [Fintype t] [DecidableEq t]
    (P : TypeDatum k R) (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (j : ℕ) (g : GL (Ix R t j) k) :
    g ∈ (P.iter t μ hμ j).J ↔ g ∈ KO k (Ix R t j) ∧
      (∀ a b : Ix R t j, b.blk < a.blk → valuation k (g.val a b) < 1) ∧
      ∃ x ∈ P.J, x.val = g.val.submatrix Sum.inl Sum.inl := by
  induction j with
  | zero =>
    refine ⟨fun h => ⟨TypeDatum.le_KO _ h, fun a b hab => ?_, _, h, rfl⟩, fun ⟨_, _, x, hx, e⟩ => ?_⟩
    · have := Ix.blk_le a
      omega
    · change (reGL (ixZero R t)).symm g ∈ P.J
      rwa [show (reGL (ixZero R t)).symm g = x from Units.ext (by rw [reGL_symm_val, e]; rfl)]
  | succ j ih =>
    have e : g ∈ (P.iter t μ hμ (j + 1)).J ↔
        (reGL (ixSucc R t j)).symm g ∈ (P.iter t μ hμ j).stepJ t := Iff.rfl
    rw [e, TypeDatum.mem_stepJ_iff]
    constructor
    · rintro ⟨h0, ⟨u, hu, eu⟩, hC⟩
      obtain ⟨-, h1, x, hx, ex⟩ := (ih u).1 hu
      refine ⟨(reGL_symm_mem_KO _ _).1 h0, fun a b hab => ?_, x, hx, ?_⟩
      · obtain ⟨a, rfl⟩ := (ixSucc R t j).surjective a
        obtain ⟨b, rfl⟩ := (ixSucc R t j).surjective b
        rcases a with a | a <;> rcases b with b | b
        · rw [blk_ixSucc_inl, blk_ixSucc_inl] at hab
          have := h1 a b hab
          rw [eu] at this
          exact this
        · rw [blk_ixSucc_inl, blk_ixSucc_inr] at hab
          have := Ix.blk_le a
          omega
        · exact hC a b
        · exact absurd hab (lt_irrefl _)
      · rw [ex, eu]; rfl
    · rintro ⟨h0, h1, x, hx, ex⟩
      have h0' := (reGL_symm_mem_KO (ixSucc R t j) g).2 h0
      have hC : MaxM ((reGL (ixSucc R t j)).symm g).val.toBlocks₂₁ := fun a b =>
        h1 (ixSucc R t j (.inr a)) (ixSucc R t j (.inl b)) (by
          rw [blk_ixSucc_inl, blk_ixSucc_inr]; exact Nat.lt_succ_of_le (Ix.blk_le b))
      obtain ⟨u, hu, eu⟩ := (exists_diag_blocks h0' hC).1
      refine ⟨h0', ⟨u, (ih u).2 ⟨hu, fun a b hab => ?_, x, hx, ?_⟩, eu⟩, hC⟩
      · rw [eu]
        exact h1 (ixSucc R t j (.inl a)) (ixSucc R t j (.inl b)) (by rwa [blk_ixSucc_inl, blk_ixSucc_inl])
      · rw [ex, eu]; rfl

end GlobalTheory.FunObj.TieLev

namespace GlobalTheory.FunObj.TieLev

section Num
variable {R : Type} {r t j a : ℕ}

def IsIxR (e₀ : R ≃ Fin r) (ea : Ix R (Fin t) j ≃ Fin a) : Prop :=
  a = r + j * t ∧ (∀ i, (ea (.inl i)).val = (e₀ i).val) ∧ ∀ c s, (ea (.inr (c, s))).val = r + (s.val + t * c.val)

theorem isIxR_of_isIx {e₀ : R ≃ Fin r} {ea : Ix R (Fin t) j ≃ Fin a}
    (h : GlobalTheory.FunObj.Comparison₂.IsIx ((Equiv.sumCongr e₀.symm (Equiv.refl (Fin j × Fin t))).trans ea)) : IsIxR e₀ ea :=
  ⟨h.1, fun i => by simpa using h.2.1 (e₀ i), fun c s => by simpa using h.2.2 c s⟩

theorem IsIxR.blkOf {e₀ : R ≃ Fin r} {ea : Ix R (Fin t) j ≃ Fin a} (h : IsIxR e₀ ea) (i : Ix R (Fin t) j) :
    Formalism.L2.DIV.blkOf r t (ea i) = i.blk := by
  rcases i with i | ⟨c, s⟩
  · rw [Formalism.L2.DIV.blkOf, if_pos (by rw [h.2.1]; exact (e₀ i).2)]; rfl
  · rw [Formalism.L2.DIV.blkOf, h.2.2, if_neg (by omega), Nat.add_sub_cancel_left, Nat.add_mul_div_left _ _ s.pos,
      Nat.div_eq_of_lt s.2, zero_add]; rfl

variable {b : ℕ} {e₀ : R ≃ Fin r} {ea : Ix R (Fin t) j ≃ Fin a} {eb : Ix R (Fin t) (j + 1) ≃ Fin b}

theorem val_succ_inl (ha : IsIxR e₀ ea) (hb : IsIxR e₀ eb) (i : Ix R (Fin t) j) :
    (eb (ixSucc _ _ j (.inl i))).val = (ea i).val := by
  rcases i with i | ⟨c, s⟩
  · exact (hb.2.1 i).trans (ha.2.1 i).symm
  · exact (hb.2.2 c.castSucc s).trans (ha.2.2 c s).symm

theorem topL_a {κ : Type} [Zero κ] (ha : IsIxR e₀ ea) (hb : IsIxR e₀ eb) (y : Matrix (Fin b) (Fin a) κ)
    (i l : Ix R (Fin t) j) : topL a y (ea i) (ea l) = y (eb (ixSucc _ _ j (.inl i))) (ea l) := by
  have h : (ea i).val < b ∧ (ea l).val < a := ⟨val_succ_inl ha hb i ▸ (eb _).2, (ea l).2⟩
  rw [topL, dite_eq_left h]
  exact congrArg₂ y (Fin.ext (val_succ_inl ha hb i).symm) rfl

end Num

end GlobalTheory.FunObj.TieLev

namespace GlobalTheory.FunObj.TieLev

section Red
variable {S κ K : Type} [CommRing S] [CommRing κ] [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {φ : S →+* κ} {ψ : S →+* K}
variable {R : Type} {r t j a b : ℕ} {e₀ : R ≃ Fin r} {ea : Ix R (Fin t) j ≃ Fin a} {eb : Ix R (Fin t) (j + 1) ≃ Fin b}


omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem lowZero_a (h : GlobalTheory.FunObj.Comparison₂.IsRed φ ψ) (ha : IsIxR e₀ ea) (hb : IsIxR e₀ eb) (N : Matrix (Fin b) (Fin a) S) :
    LowZero a (N.map φ) ↔ MaxM (((N.map ψ).submatrix eb ea).submatrix (ixSucc _ _ j) id).toRows₂ := by
  refine ⟨fun H i l => (h.ker _).1 (H _ _ ?_ (ea l).2), fun H i l hi _ => ?_⟩
  · have := hb.2.2 (Fin.last j) i
    rw [Fin.val_last, mul_comm] at this
    exact ha.1.le.trans (le_of_le_of_eq (by omega) this.symm)
  obtain ⟨i, rfl⟩ := eb.surjective i
  obtain ⟨l, rfl⟩ := ea.surjective l
  obtain ⟨i | i, rfl⟩ := (ixSucc _ _ j).surjective i
  · exact absurd (val_succ_inl ha hb i ▸ hi) (ea i).2.not_ge
  · exact (h.ker _).2 (H i l)


omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem diagonalBlock_det_blockTriangular (ha : IsIxR e₀ ea) {g : GL (Fin a) κ} (hg : g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t)) (c : Fin j) :
    (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf r t) (c.val + 1) g : κ) = (Ix.diagonalBlockOfMatrix (g.val.submatrix ea ea) c).det := by
  have hb : Function.Bijective fun s : Fin t =>
      (⟨ea (.inr (c, s)), ha.blkOf _⟩ : {i : Fin a // Formalism.L2.DIV.blkOf r t i = c.val + 1}) := by
    refine ⟨fun s s' h => by simpa using congrArg Subtype.val h, fun ⟨i, hi⟩ => ?_⟩
    obtain ⟨i | ⟨c', s⟩, rfl⟩ := ea.surjective i
    · exact absurd ((ha.blkOf _).symm.trans hi) (Nat.succ_ne_zero _).symm
    · obtain rfl : c' = c := Fin.ext (Nat.succ_injective ((ha.blkOf _).symm.trans hi))
      exact ⟨s, rfl⟩
  rw [Formalism.L2.DIV.diag_block_det_val _ hg, ← det_submatrix_equiv_self (Equiv.ofBijective _ hb)]
  rfl


omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem firstBlock_topBlockMatrix_reduction_eq (ha : IsIxR e₀ ea) (hb : IsIxR e₀ eb) (hr : r ≤ a) (N : Matrix (Fin b) (Fin a) S) {g : GL (Fin a) κ}
    (hg : g.val = topL a (N.map φ)) (hbt : g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t)) :
    (Formalism.L2.DIV.upperLeftBlock hr g).val.submatrix e₀ e₀ =
      ((N.submatrix (fun i => eb (ixSucc _ _ j (.inl i))) ea).submatrix Sum.inl Sum.inl).map φ := by
  ext i l
  rw [submatrix_apply, Formalism.L2.DIV.upper_block_val_submatrix hr (Formalism.L2.DIV.blockTri_blkOf_le r t hbt), submatrix_apply, hg,
    show Fin.castLE hr (e₀ i) = ea (.inl i) from Fin.ext (ha.2.1 i).symm,
    show Fin.castLE hr (e₀ l) = ea (.inl l) from Fin.ext (ha.2.1 l).symm, topL_a ha hb]
  rfl

end Red

end GlobalTheory.FunObj.TieLev

namespace GlobalTheory.FunObj.TieLev

theorem iterPhi_read : ∀ (S κ k : Type) [CommRing S] [CommRing κ] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (φ : S →+* κ) (ψ : S →+* k), GlobalTheory.FunObj.Comparison₂.IsRed φ ψ → ∀ (R : Type) [Fintype R] [DecidableEq R] (r t j a b : ℕ) (e₀ : R ≃ Fin r) (ea : Ix R (Fin t) j ≃ Fin a) (eb : Ix R (Fin t) (j + 1) ≃ Fin b), GlobalTheory.FunObj.Comparison₂.IsIx ((Equiv.sumCongr e₀.symm (Equiv.refl (Fin j × Fin t))).trans ea) → GlobalTheory.FunObj.Comparison₂.IsIx ((Equiv.sumCongr e₀.symm (Equiv.refl (Fin (j + 1) × Fin t))).trans eb) → ∀ (hr : r ≤ a) (P : TypeDatum k R) (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ c, IsTame (μ c)) (χ : ℕ → κˣ →* ℂˣ), (∀ c, c ≤ j → GlobalTheory.FunObj.Comparison₂.Compat φ ψ (χ (c + 1)) (μ (c + 1))) → ∀ Rd : P.J → GL (Fin r) κ → Prop, (∀ (x : P.J) (g : GL (Fin r) κ) (M : Matrix R R S), g.val.submatrix e₀ e₀ = M.map φ → (Rd x g ↔ MaxM ((x : GL R k).val - M.map ψ))) → ∀ N : Matrix (Fin b) (Fin a) S, (P.iterPhi (Fin t) μ hμ j ((N.map ψ).submatrix eb ea) ≠ 0 → LowZero a (N.map φ) ∧ ∃ g : GL (Fin a) κ, g.val = topL a (N.map φ) ∧ g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t) ∧ ∃ x, Rd x (Formalism.L2.DIV.upperLeftBlock hr g)) ∧ (LowZero a (N.map φ) → ∀ g : GL (Fin a) κ, g.val = topL a (N.map φ) → g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t) → ∀ x, Rd x (Formalism.L2.DIV.upperLeftBlock hr g) → P.iterPhi (Fin t) μ hμ j ((N.map ψ).submatrix eb ea) = (P.lam x : ℂ) * (∏ c ∈ Finset.range j, (χ (c + 1) (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf r t) (c + 1) g) : ℂ)) * (χ (j + 1) (Matrix.GeneralLinearGroup.det g) : ℂ)⁻¹) := by
  intro S κ k _ _ _ _ _ _ φ ψ h R _ _ r t j a b e₀ ea eb hA hB hr P μ hμ χ hχ Rd hRd N
  have ha := isIxR_of_isIx hA
  have hb := isIxR_of_isIx hB
  set M := N.submatrix (fun i => eb (ixSucc _ _ j (.inl i))) ea with hM
  have hy : (topL a (N.map φ)).submatrix ea ea = M.map φ := Matrix.ext (topL_a ha hb (N.map φ))
  have e1 : ∀ g : GL (Fin a) κ, g.val = topL a (N.map φ) → (g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t) ↔
      ∀ i l : Ix R (Fin t) j, l.blk < i.blk → valuation k (ψ (M i l)) < 1) := fun g hg => by
    rw [Formalism.L2.DIV.mem_blockTri, hg, ea.surjective.forall₂]
    refine forall₂_congr fun i l => ?_
    rw [ha.blkOf, ha.blkOf, ← h.ker]
    exact imp_congr_right fun _ => iff_of_eq (congrArg (· = 0) (congrFun (congrFun hy i) l))
  have e3 : (topL a (N.map φ)).det = (M.map φ).det := by rw [← hy, det_submatrix_equiv_self]
  have hsub : ∀ g' : GL (Ix R (Fin t) j) k, g'.val = M.map ψ →
      g'.val.submatrix Sum.inl Sum.inl = (M.submatrix Sum.inl Sum.inl).map ψ := fun g' e => by rw [e]; rfl
  refine ⟨fun h0 => ?_, fun hlow g hg hbt x hx => ?_⟩
  · rw [TypeDatum.iterPhi, TypeDatum.Phi_ne_zero_iff] at h0
    obtain ⟨⟨g', hg', e'⟩, hlow⟩ := h0
    have e'' : g'.val = M.map ψ := e'
    obtain ⟨k1, k2, x, hx, ex⟩ := (mem_iter_gen P μ hμ j g').1 hg'
    obtain ⟨g, hg⟩ := (Matrix.isUnit_iff_isUnit_det _).2 (e3 ▸ (h.isUnit_det_iff M).2 ⟨g', k1, e''⟩)
    have hbt : g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t) := (e1 g hg).2 fun i l hil => by
      have := k2 i l hil
      rwa [e''] at this
    refine ⟨(lowZero_a h ha hb N).2 hlow, g, hg, hbt, ⟨x, hx⟩, (hRd ⟨x, hx⟩ _ _ (firstBlock_topBlockMatrix_reduction_eq ha hb hr N hg hbt)).2 ?_⟩
    change MaxM (x.val - _)
    rw [ex, hsub g' e'', sub_self]
    exact maxM_zero
  · have hmx := (hRd x _ _ (firstBlock_topBlockMatrix_reduction_eq ha hb hr N hg hbt)).1 hx
    obtain ⟨g', k1, e''⟩ := (h.isUnit_det_iff M).1 (e3 ▸ hg ▸ (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit)
    have hx' : MaxM (g'.val.submatrix Sum.inl Sum.inl - (x : GL R k).val) := fun i l => by
      rw [hsub g' e'', Matrix.sub_apply, ← neg_sub, Valuation.map_neg]
      exact hmx i l
    obtain ⟨x', hx'J, ex'⟩ := P.exists_of_congr x.2 hx'
    have hJ : g' ∈ (P.iter (Fin t) μ hμ j).J := (mem_iter_gen P μ hμ j g').2
      ⟨k1, fun i l hil => by rw [e'']; exact (e1 g hg).1 hbt i l hil, x', hx'J, ex'⟩
    obtain ⟨g₀, D, e0, hD, el⟩ := GlobalTheory.SymBridge.iter_lam_closed k R (Fin t) P μ hμ j ⟨g', hJ⟩
    have hl : P.lam g₀ = P.lam x := by
      have h5 : MaxM ((g₀ : GL R k).val - (x : GL R k).val) := by
        rw [e0]; exact hx'
      have := P.lam_eq_one (x⁻¹ * g₀) (inv_mul_mem_KOne (P.le_KO x.2) h5)
      rw [map_mul, map_inv, inv_mul_eq_one] at this
      exact this.symm
    have hblk : ∀ c : Fin j, μ (c.val + 1) (Matrix.GeneralLinearGroup.det (D c)) =
        χ (c.val + 1) (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf r t) (c.val + 1) g) := fun c =>
      ((hχ c c.2.le).det (Ix.diagonalBlockOfMatrix M c) (by rw [diagonalBlock_det_blockTriangular ha hbt c, hg, hy]; rfl)
        (by rw [Matrix.GeneralLinearGroup.val_det_apply, (hD c).2, e'']; rfl)).symm
    have hdet : μ (j + 1) (Matrix.GeneralLinearGroup.det g') = χ (j + 1) (Matrix.GeneralLinearGroup.det g) :=
      ((hχ j le_rfl).det M (by rw [← hy, det_submatrix_equiv_self, ← hg]; rfl)
        (by rw [Matrix.GeneralLinearGroup.val_det_apply, e''])).symm
    rw [TypeDatum.iterPhi, TypeDatum.Phi_of_mem (x := ((N.map ψ).submatrix eb ea).submatrix (ixSucc _ _ j) id) _ _
      ⟨g', hJ⟩ e'' ((lowZero_a h ha hb N).1 hlow), el, hl, hdet, Units.val_mul, Units.coe_prod,
      Units.val_inv_eq_inv_val, Finset.prod_range]
    simp only [hblk]

end GlobalTheory.FunObj.TieLev
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPairSpaceLinearMapViaPartialFourier
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPairSpaceLinearMapViaPartialFourier
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LocFlat.CQLast

open scoped TensorProduct

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]

theorem eq_zero_of_hat_eq_zero (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) (hψ : Continuous ψ)
    (hne : ψ ≠ 1) {n : Type} [Fintype n] [DecidableEq n] {f : (n → k) → ℂ} (hf : f ∈ SB (n → k))
    (h0 : ∀ η, GlobalTheory.StepData.hat ψ ν (-1) f η = 0) (a : n → k) : f a = 0 := by
  classical
  have := GlobalTheory.SplitWeil.secondCountable k
  have := GlobalTheory.SplitWeil.t2Space k
  obtain ⟨c, hc⟩ := (GlobalTheory.SplitWeil.conductor_exists k).1 ψ hψ hne
  set μ : Measure (n → k) := Measure.pi fun _ => ν with hμ
  have hF : ∀ y, ∫ x, f x * (ψ (x ⬝ᵥ y) : ℂ) ∂μ = 0 := by
    intro y
    have h1 := h0 (-y)
    simp only [GlobalTheory.StepData.hat] at h1
    rw [← h1]
    congr 1
    funext x
    rw [neg_dotProduct, neg_one_mul, neg_neg, dotProduct_comm]
  set g : (n → k) → ℂ := fun x => f (x + a) with hgdef
  have hg : g ∈ SB (n → k) :=
    ⟨hf.1.comp_continuous (continuous_add_const a), hf.2.comp_homeomorph (Homeomorph.addRight a)⟩
  have hpsi : ∀ u v : k, (ψ (u + v) : ℂ) = ψ u * ψ v := fun u v => by
    rw [AddChar.map_add_eq_mul, Circle.coe_mul]
  have hpsi' : ∀ u : k, (ψ (-u) : ℂ) * ψ u = 1 := fun u => by
    rw [← hpsi, neg_add_cancel, AddChar.map_zero_eq_one, Circle.coe_one]
  have hG : ∀ y, ∫ x, g x * (ψ (x ⬝ᵥ y) : ℂ) ∂μ = 0 := by
    intro y
    have e : ∀ x, g x * (ψ (x ⬝ᵥ y) : ℂ) = (ψ (-(a ⬝ᵥ y)) : ℂ) * (f (x + a) * ψ ((x + a) ⬝ᵥ y)) := by
      intro x
      rw [add_dotProduct, hpsi, hgdef]
      linear_combination (f (x + a) * (ψ (x ⬝ᵥ y) : ℂ)) * (hpsi' (a ⬝ᵥ y)).symm
    simp_rw [e]
    rw [integral_const_mul, integral_add_right_eq_self (fun x => f x * (ψ (x ⬝ᵥ y) : ℂ)) a, hF, mul_zero]
  obtain ⟨s, hs⟩ := FourierPi.fourier_inversion_pi μ hc hg
  simp only [hG, integral_zero] at hs
  have hpos : ∀ r : kˣ, 0 < μ.real (FourierPi.box n r) := by
    intro r
    refine ENNReal.toReal_pos ((FourierPi.isOpen_box r).measure_pos μ ⟨0, ?_⟩).ne'
      (FourierPi.isCompact_box r).measure_lt_top.ne
    simp [FourierPi.box, cball]
  have h2 : g 0 = 0 := by
    rcases mul_eq_zero.1 hs.symm with h | h
    · exfalso
      have := mul_pos (hpos s) (hpos (c * s⁻¹))
      exact this.ne' (by exact_mod_cast h)
    · exact h
  simpa [hgdef] using h2

def withLast {n n' : Type} (x₀ : Matrix n n' k) (y : n → k) : Matrix n (n' ⊕ Unit) k :=
  fromCols x₀ (Matrix.of fun r (_ : Unit) => y r)

theorem withLast_toCols {n n' : Type} (x : Matrix n (n' ⊕ Unit) k) :
    withLast x.toCols₁ (fun r => x r (Sum.inr ())) = x := by
  ext r (j | u)
  · rfl
  · cases u; rfl

theorem continuous_withLast {n n' : Type} (x₀ : Matrix n n' k) : Continuous (withLast x₀) := by
  refine continuous_matrix fun i j => ?_
  rcases j with a | u
  · simp only [withLast, Matrix.fromCols_apply_inl]; exact continuous_const
  · simp only [withLast, Matrix.fromCols_apply_inr, Matrix.of_apply]; exact continuous_apply i

theorem slice_mem_SB {n n' : Type} [Fintype n] [Fintype n'] {Ψ : Matrix n (n' ⊕ Unit) k → ℂ}
    (hΨ : Ψ ∈ SB (Matrix n (n' ⊕ Unit) k)) (x₀ : Matrix n n' k) :
    (fun y : n → k => Ψ (withLast x₀ y)) ∈ SB (n → k) := by
  have := GlobalTheory.SplitWeil.t2Space k
  have hcl : Topology.IsClosedEmbedding (withLast x₀) :=
    Function.LeftInverse.isClosedEmbedding (f := fun x : Matrix n (n' ⊕ Unit) k => fun r => x r (Sum.inr ()))
      (fun y => rfl) (by fun_prop) (continuous_withLast x₀)
  exact ⟨hΨ.1.comp_continuous (continuous_withLast x₀), hΨ.2.comp_isClosedEmbedding hcl⟩

def partialHat (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) (hψ : Continuous ψ) (n n' : Type)
    [Fintype n] [Fintype n'] :
    SB (Matrix n (n' ⊕ Unit) k) →ₗ[ℂ] (Matrix n n' k × (n → k) → ℂ) where
  toFun Ψ p := GlobalTheory.StepData.hat ψ ν (-1) (fun y => Ψ.1 (withLast p.1 y)) p.2
  map_add' Ψ Ψ' := by
    funext p
    simp only [GlobalTheory.StepData.hat, Submodule.coe_add, Pi.add_apply, add_mul]
    exact integral_add (GlobalTheory.StepData.integrable_hat ψ ν (-1) hψ (slice_mem_SB Ψ.2 p.1) p.2)
      (GlobalTheory.StepData.integrable_hat ψ ν (-1) hψ (slice_mem_SB Ψ'.2 p.1) p.2)
  map_smul' a Ψ := by
    funext p
    simp only [GlobalTheory.StepData.hat, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
    exact integral_const_mul a _

theorem partialHat_injective (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) (hψ : Continuous ψ)
    (hne : ψ ≠ 1) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] :
    Function.Injective (partialHat ν ψ hψ n n') := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro Ψ h
  ext x
  have h1 := eq_zero_of_hat_eq_zero ν ψ hψ hne (slice_mem_SB Ψ.2 x.toCols₁)
    (fun η => congrFun h (x.toCols₁, η)) (fun r => x r (Sum.inr ()))
  simpa [withLast_toCols] using h1

def coupleBil (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) (hψ : Continuous ψ) (n n' Z : Type)
    [Fintype n] [Fintype n'] :
    SB (Matrix Z n k) →ₗ[ℂ] SB (Matrix n (n' ⊕ Unit) k) →ₗ[ℂ] (Matrix n n' k × Matrix (Z ⊕ Unit) n k → ℂ) :=
  LinearMap.mk₂ ℂ (fun g Ψ q => g.1 q.2.toRows₁ * partialHat ν ψ hψ n n' Ψ (q.1, q.2 (Sum.inr ())))
    (fun g g' Ψ => by funext q; simp [add_mul])
    (fun a g Ψ => by funext q; simp [mul_assoc])
    (fun g Ψ Ψ' => by funext q; simp [mul_add])
    (fun a g Ψ => by funext q; simp; ring)

theorem coupleBil_injective (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) (hψ : Continuous ψ)
    (hne : ψ ≠ 1) (n n' Z : Type) [Fintype n] [DecidableEq n] [Fintype n'] :
    Function.Injective (TensorProduct.lift (coupleBil ν ψ hψ n n' Z)) := by
  classical
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro t ht
  let b := Module.Free.chooseBasis ℂ (SB (Matrix Z n k))
  set c := TensorProduct.equivFinsuppOfBasisLeft b t with hc
  have ht' : t = c.sum fun i m => b i ⊗ₜ m := by
    rw [hc, ← TensorProduct.equivFinsuppOfBasisLeft_symm_apply, LinearEquiv.symm_apply_apply]
  have hm : ∀ (x₀ : Matrix n n' k) (η : n → k) (x : Matrix Z n k),
      ∑ i ∈ c.support, (b i).1 x * partialHat ν ψ hψ n n' (c i) (x₀, η) = 0 := by
    intro x₀ η x
    have hrow : (fromRows x (Matrix.of fun (_ : Unit) r => η r)) (Sum.inr ()) = η := by
      funext r; simp
    have := congrFun ht (x₀, fromRows x (Matrix.of fun (_ : Unit) r => η r))
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [ht', Finsupp.sum, map_sum, TensorProduct.lift.tmul] at this
    simpa [coupleBil, Finset.sum_apply, hrow] using this
  have hzero : c = 0 := by
    ext i : 1
    by_cases hi : i ∈ c.support
    · have hP : partialHat ν ψ hψ n n' (c i) = partialHat ν ψ hψ n n' 0 := by
        rw [map_zero]
        funext p
        have hli := (linearIndependent_iff'.mp b.linearIndependent) c.support
          (fun j => partialHat ν ψ hψ n n' (c j) p)
          (by
            ext x
            simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
              ZeroMemClass.coe_zero, Pi.zero_apply]
            rw [← hm p.1 p.2 x]
            exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)) i hi
        simpa using hli
      simpa using partialHat_injective ν ψ hψ hne n n' hP
    · simp [Finsupp.notMem_support_iff.mp hi]
  rw [ht', hzero]
  simp

theorem exists_pair_map : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), ν.IsAddHaarMeasure → ∀ (ψk : AddChar k Circle), Continuous ψk → ψk ≠ 1 → ∀ (n n' Z : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype Z] [DecidableEq Z] (M : Type) [AddCommGroup M] [Module ℂ M] (Bl : SB (Matrix Z n k) →ₗ[ℂ] SB (Matrix n (n' ⊕ Unit) k) →ₗ[ℂ] M), ∃ Λ : SB (Matrix n n' k × Matrix (Z ⊕ Unit) n k) →ₗ[ℂ] M, (∀ (Ψ₁ : SB (Matrix n (n' ⊕ Unit) k)) (Ψ₂ : SB (Matrix Z n k)) (Ξ : SB (Matrix n n' k × Matrix (Z ⊕ Unit) n k)), (∀ q, Ξ.1 q = Ψ₂.1 q.2.toRows₁ * GlobalTheory.StepData.hat ψk ν (-1) (fun y => Ψ₁.1 (fromCols q.1 (Matrix.of fun r _ => y r))) (q.2 (Sum.inr ()))) → Λ Ξ = Bl Ψ₂ Ψ₁) ∧ ∀ (Ξ₁ : SB (Matrix n n' k)) (a : SB (Matrix Z n k)) (c : SB (Matrix n Unit k)) (Ψ₁ : SB (Matrix n (n' ⊕ Unit) k)) (Ξ : SB (Matrix n n' k × Matrix (Z ⊕ Unit) n k)), (∀ x, Ψ₁.1 x = Ξ₁.1 x.toCols₁ * c.1 (Matrix.of fun r _ => x r (Sum.inr ()))) → (∀ q, Ξ.1 q = Ξ₁.1 q.1 * (a.1 q.2.toRows₁ * GlobalTheory.StepData.hat ψk ν (-1) (fun y => c.1 (Matrix.of fun r _ => y r)) (q.2 (Sum.inr ())))) → Λ Ξ = Bl a Ψ₁ := by
  intro k _ _ _ _ _ _ ν hν ψk hψ hne n n' Z _ _ _ _ _ _ M _ _ Bl
  classical
  set T := TensorProduct.lift (coupleBil ν ψk hψ n n' Z) with hT
  have hinj := coupleBil_injective ν ψk hψ hne n n' Z
  let eT := LinearEquiv.ofInjective T hinj
  let W : Submodule ℂ (SB (Matrix n n' k × Matrix (Z ⊕ Unit) n k)) :=
    (LinearMap.range T).comap (SB (Matrix n n' k × Matrix (Z ⊕ Unit) n k)).subtype
  let res : W →ₗ[ℂ] LinearMap.range T :=
    (SB (Matrix n n' k × Matrix (Z ⊕ Unit) n k)).subtype.restrict (fun x hx => hx)
  let Λ₀ : W →ₗ[ℂ] M := (TensorProduct.lift Bl).comp (eT.symm.toLinearMap.comp res)
  obtain ⟨Λ, hΛ⟩ := LinearMap.exists_extend Λ₀
  have key : ∀ (Ψ₁ : SB (Matrix n (n' ⊕ Unit) k)) (Ψ₂ : SB (Matrix Z n k))
      (Ξ : SB (Matrix n n' k × Matrix (Z ⊕ Unit) n k)), Ξ.1 = T (Ψ₂ ⊗ₜ Ψ₁) → Λ Ξ = Bl Ψ₂ Ψ₁ := by
    intro Ψ₁ Ψ₂ Ξ hΞ
    have hmem : Ξ ∈ W := ⟨Ψ₂ ⊗ₜ Ψ₁, hΞ.symm⟩
    have h1 := LinearMap.congr_fun hΛ ⟨Ξ, hmem⟩
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype] at h1
    rw [h1]
    have h2 : res ⟨Ξ, hmem⟩ = eT (Ψ₂ ⊗ₜ Ψ₁) := Subtype.ext (by
      rw [LinearEquiv.ofInjective_apply]
      exact hΞ)
    simp only [Λ₀, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, h2, LinearEquiv.symm_apply_apply,
      TensorProduct.lift.tmul]
  refine ⟨Λ, fun Ψ₁ Ψ₂ Ξ h => key Ψ₁ Ψ₂ Ξ (funext fun q => ?_),
    fun Ξ₁ a c Ψ₁ Ξ h1 h2 => key Ψ₁ a Ξ (funext fun q => ?_)⟩
  · rw [h q, hT, TensorProduct.lift.tmul]
    rfl
  · rw [h2 q, hT, TensorProduct.lift.tmul]
    have e : (fun y => Ψ₁.1 (withLast q.1 y)) = fun y => Ξ₁.1 q.1 * c.1 (Matrix.of fun r (_ : Unit) => y r) := by
      funext y
      rw [h1]
      rfl
    change _ = a.1 q.2.toRows₁ * GlobalTheory.StepData.hat ψk ν (-1) (fun y => Ψ₁.1 (withLast q.1 y)) (q.2 (Sum.inr ()))
    rw [e]
    simp only [GlobalTheory.StepData.hat, mul_assoc]
    rw [integral_const_mul]
    ring

end GlobalTheory.LocFlat.CQLast
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPairSpaceLinearMapViaPartialFourierStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pair_space_linear_map_via_partial_fourier : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), ν.IsAddHaarMeasure → ∀ (ψk : AddChar k Circle), Continuous ψk → ψk ≠ 1 → ∀ (n n' Z : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype Z] [DecidableEq Z] (M : Type) [AddCommGroup M] [Module ℂ M] (Bl : SB (Matrix Z n k) →ₗ[ℂ] SB (Matrix n (n' ⊕ Unit) k) →ₗ[ℂ] M), ∃ Λ : SB (Matrix n n' k × Matrix (Z ⊕ Unit) n k) →ₗ[ℂ] M, (∀ (Ψ₁ : SB (Matrix n (n' ⊕ Unit) k)) (Ψ₂ : SB (Matrix Z n k)) (Ξ : SB (Matrix n n' k × Matrix (Z ⊕ Unit) n k)), (∀ q, Ξ.1 q = Ψ₂.1 q.2.toRows₁ * GlobalTheory.StepData.hat ψk ν (-1) (fun y => Ψ₁.1 (fromCols q.1 (Matrix.of fun r _ => y r))) (q.2 (Sum.inr ()))) → Λ Ξ = Bl Ψ₂ Ψ₁) ∧ ∀ (Ξ₁ : SB (Matrix n n' k)) (a : SB (Matrix Z n k)) (c : SB (Matrix n Unit k)) (Ψ₁ : SB (Matrix n (n' ⊕ Unit) k)) (Ξ : SB (Matrix n n' k × Matrix (Z ⊕ Unit) n k)), (∀ x, Ψ₁.1 x = Ξ₁.1 x.toCols₁ * c.1 (Matrix.of fun r _ => x r (Sum.inr ()))) → (∀ q, Ξ.1 q = Ξ₁.1 q.1 * (a.1 q.2.toRows₁ * GlobalTheory.StepData.hat ψk ν (-1) (fun y => c.1 (Matrix.of fun r _ => y r)) (q.2 (Sum.inr ())))) → Λ Ξ = Bl a Ψ₁ := by
  first | exact @GlobalTheory.LocFlat.CQLast.exists_pair_map | exact GlobalTheory.LocFlat.CQLast.exists_pair_map | (intros; apply GlobalTheory.LocFlat.CQLast.exists_pair_map <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedChainThetaLiftUpSpan
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedChainThetaLiftUpSpan
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt

noncomputable section

namespace GlobalTheory.ChainTw.UpSpanTw

variable {D : D7}

theorem multT_le_noLevel {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) (J : Set (GA D V))
    (χ : GA D V → ℂ) : MultT θ M J χ ≤ MultT θ M ∅ 1 := by
  intro x hx
  rw [mem_multT] at hx ⊢
  refine Submodule.span_mono ?_ hx
  intro T hT
  exact ⟨hT.aut, hT.cusp, fun v k hk => absurd hk (Set.notMem_empty k), hT.equiv, hT.cont⟩

theorem conj_inv_of_norm_one {z : ℂ} (hz : ‖z‖ = 1) : conj z⁻¹ = z := by
  have h1 : Complex.normSq z = 1 := by rw [Complex.normSq_eq_norm_sq, hz]; norm_num
  rw [Complex.inv_def, h1, inv_one, Complex.ofReal_one, mul_one, Complex.conj_conj]

theorem upSpanQ_of : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay →
    GlobalTheory.Published.CasselmanWallach → ∀ D : D7, LevelLawQ D → UpSpanQ D := by
  intro h1 h2 h3 h4 D hLL hgap c w hw k hk s s' hs hs' p hp u φ v _hv
  have hc := hw.com
  obtain ⟨hwe, hvac⟩ := GlobalTheory.T.twisted_chain_step_weil_exponents_fock_vacuum D hgap c w hw k hk s s' hs hs' p hp hk
  obtain ⟨hr, hL0, hfl⟩ := hs
  obtain ⟨hr', hL1, hfl'⟩ := hs'
  have hpar := GlobalTheory.T.chainPar_of_nodeGap' D hgap ⟨k, hk⟩
  obtain ⟨T, hTK, hKT, hL⟩ := GlobalTheory.T.thetaLift_upward_multiplicity_cuspidal_realType h1 h2 h3 h4 D ⟨k, hk⟩ s.V s'.V s.par s'.par s.M s'.M c.θ c.ψ p.ω p.f
    hfl.par hfl'.par hc.inf hpar hwe hvac s.ν s.fd hfl.haar hfl.fund
  obtain ⟨F', hF', hint⟩ := hL _ (multT_le_noLevel c.θ s.M _ _ u.2)
  have hlaw : ∀ P v', ∀ κ ∈ Lev.levG s'.V s'.β s'.L, ∀ g,
      F' (T P v') (g * κ) = Lev.levChi s'.V s'.β s'.L κ * F' (T P v') g := by
    intro P v' κ hκ g
    rw [← (hint P v' (g * κ)).2, ← (hint P v' g).2, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g' => ?_)
    have hω : thetaKO p.ω g' (g * κ) (ptOf c.ψ c.θ s.M s'.M p.f P) =
        (Lev.levChi s'.V s'.β s'.L κ)⁻¹ * thetaKO p.ω g' g (ptOf c.ψ c.θ s.M s'.M p.f P) := by
      have hm : ((g', g * κ) : GA D s.V × GA D s'.V) = (g', g) * (1, κ) := by simp
      have h2 := (hLL hgap c w hw k hk s s' ⟨hr, hL0, hfl⟩ ⟨hr', hL1, hfl'⟩ p hp P).2 κ hκ
      simp only [thetaKO]
      rw [hm, map_mul, Module.End.mul_apply]
      erw [h2]
      rw [map_smul]
      rfl
    simp only
    rw [hω, map_mul, conj_inv_of_norm_one (GlobalTheory.ChainOnto.LevelFacts.levChi_norm s'.β s'.L κ), mul_assoc]
  have hCC : F' ∈ s'.CC c := by
    refine GlobalTheory.T.mem_multiplicitySpace_level_of_KFinite_tensors D s'.V s'.par s'.M c.θ hc.inf _ _ ?_ F' hF' ?_
    · intro κ hκ
      exact hκ.1
    · intro w' hw' κ hκ g
      have hx := hKT hw'
      clear hw'
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨P, v', _, rfl⟩ := hx
        exact hlaw P v' κ hκ g
      | zero => simp
      | add x y _ _ hx hy => simp only [map_add (f := _), Pi.add_apply, hx, hy, mul_add]
      | smul a x _ hx => simp only [map_smul, Pi.smul_apply, smul_eq_mul, hx]; ring
  have hup : p.up φ (PiLocalization₂.val u v) = F' (T φ v) := by
    funext h
    exact (hint φ v h).2
  rw [hup]
  exact Submodule.subset_span ⟨⟨F', hCC⟩, T φ v, hTK φ v, rfl⟩

end GlobalTheory.ChainTw.UpSpanTw
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedChainThetaLiftUpSpanStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedChain_thetaLiftUpSpan : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → ∀ D : D7, LevelLawQ D → UpSpanQ D := by
  first | exact @GlobalTheory.ChainTw.UpSpanTw.upSpanQ_of | exact GlobalTheory.ChainTw.UpSpanTw.upSpanQ_of | (intros; apply GlobalTheory.ChainTw.UpSpanTw.upSpanQ_of <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DefiniteScalarComponentIsCuspAndCongruenceFixedA
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DefiniteScalarComponentIsCuspAndCongruenceFixedA
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh

noncomputable section

namespace GlobalTheory.DownLift.DefiniteComp

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem extV_mul_inf (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H)
    {k : GA D (Vc D i)} (hk : k ∈ GinfC (Vc D i)) (h : GA D (Vc D i)) :
    R.extV i t y (h * k) = (R.cV i).ρ k⁻¹ (R.extV i t y h) := by
  have hr : (finHom (Vc D i)).rangeRestrict (h * k) = (finHom (Vc D i)).rangeRestrict h := by
    apply Subtype.ext
    simp [MonoidHom.mem_ker.1 hk]
  show (R.cV i).ρ (h * k)⁻¹ ((R.HV i t).e y ((finHom (Vc D i)).rangeRestrict (h * k))) =
    (R.cV i).ρ k⁻¹ ((R.cV i).ρ h⁻¹ ((R.HV i t).e y ((finHom (Vc D i)).rangeRestrict h)))
  refine (congrArg ((R.cV i).ρ (h * k)⁻¹) (congrArg ((R.HV i t).e y) hr)).trans ?_
  have e : (R.cV i).ρ (h * k)⁻¹ = (R.cV i).ρ k⁻¹ * (R.cV i).ρ h⁻¹ := by rw [_root_.mul_inv_rev, map_mul]
  exact congrArg (fun f : Module.End ℂ (R.cV i).W => f ((R.HV i t).e y ((finHom (Vc D i)).rangeRestrict h))) e

theorem extV_mul_Kg (R : RealDat D A Ks) (hM : R.IsModels) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H)
    {κ : GA D (Vc D i)} (hκ : κ ∈ GfC (Vc D i))
    (hK : finE (Vc D i) κ ∈ Kg D.sp.cm (Vc D i).gram (R.βV i) (R.Pg ∪ R.Q t)) (h : GA D (Vc D i)) :
    R.extV i t y (h * κ) = R.extV i t y h := by
  have h2 : Kg D.sp.cm (Vc D i).gram (R.βV i) (R.Pg ∪ R.Q t) ≤
      lev D.sp.cm (Vc D i).gram (R.βV i) (flag1L (R.datVt i t)) :=
    Kg_le_lev (D := flag1L (R.datVt i t)) Finset.subset_union_left Finset.subset_union_right
  have hlev : κ ∈ levG (Vc D i) (R.βV i) (flag1L (R.datVt i t)) := mem_levA.2 ⟨hκ, h2 hK⟩
  have hred : ∀ PP ∈ R.Pg ∪ R.Q t, redFn (R.βV i) PP (finE (Vc D i) κ) = 1 := fun PP hP =>
    (mem_princAt.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hK.2 PP) hP)).2
  have hfn : levFn (R.βV i) (flag1L (R.datVt i t)) (finE (Vc D i) κ) = 1 :=
    GlobalTheory.ThetaIntegrand.levFn_eq_one (R.βV i) _ (flag1L (R.datVt i t))
      (fun PP hP => hred PP (Finset.mem_union_left _ hP)) (fun PP hP => hred PP (Finset.mem_union_right _ hP))
  have hchi : levChi (Vc D i) (R.βV i) (flag1L (R.datVt i t)) κ = 1 :=
    (congrArg (fun u : ℂˣ => (u : ℂ)) hfn).trans Units.val_one
  exact (GlobalTheory.DownLift.GenFinite.extV_type R hM i t y κ hlev h).trans (by simp only [hchi, one_smul])

def compL (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) :
    ((R.cV i).W →ₗ[ℂ] ℂ) →ₗ[ℂ] (GA D (Vc D i) → ℂ) :=
  LinearMap.pi fun g => LinearMap.applyₗ (R := ℂ) (R.extV i t y g)

theorem mul_inf_mem_range (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (l : (R.cV i).W →ₗ[ℂ] ℂ)
    {k : GA D (Vc D i)} (hk : k ∈ GinfC (Vc D i)) :
    (fun g => l (R.extV i t y (g * k))) ∈ LinearMap.range (compL R i t y) :=
  ⟨l ∘ₗ (R.cV i).ρ k⁻¹, funext fun g => (congrArg l (extV_mul_inf R i t y hk g)).symm⟩

theorem definiteScalarComponent_isCusp_and_congruence_fixed : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t cA a, Defin R.θ (Vc D i) cA a → ∀ (y : (R.HV i t).H) (l : (R.cV i).W →ₗ[ℂ] ℂ), (fun g => l (R.extV i t y g)) ∈ GlobalTheory.Cusp.A0 R.θ (Vc D i) cA ∧ ∀ κ ∈ prin (Vc D i) (R.βV i) (R.Pg ∪ R.Q t), ∀ g, l (R.extV i t y (g * κ)) = l (R.extV i t y g) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG _ i t cA a hd y l
  have hM : R.IsModels := hG.core.models
  have hf : (R.HV i t).e y ∈ Formalism.IndefR.Bridge.AdForms (Formalism.IndefR.Bridge.ratF (Vc D i)) (R.cV i).coef.ρ
      (levEnv _ (R.βV i) (R.datVt i t)).J (levEnv _ (R.βV i) (R.datVt i t)).χ :=
    (hM.HV i t).2.1.le (LinearMap.mem_range_self _ y)
  have hcont : Continuous fun g => l (R.extV i t y g) :=
    (LinearMap.continuous_of_finiteDimensional l).comp
      (GlobalTheory.ThetaIntegrand.ext_continuous (R.cV i) (hM.cV i) (R.βV i) (R.datVt i t) hf)
  have hleft : ∀ γ ∈ GQ (Vc D i), ∀ g, l (R.extV i t y (γ * g)) = l (R.extV i t y g) := fun γ hγ g =>
    congrArg l (GlobalTheory.ThetaIntegrand.ext_invariant (R.cV i) hf γ hγ g)
  have hlevel : ∃ U : Subgroup (GA D (Vc D i)), IsOpen (U : Set (GA D (Vc D i))) ∧
      ∀ k ∈ U, k ∈ GfC (Vc D i) → ∀ g, l (R.extV i t y (g * k)) = l (R.extV i t y g) :=
    ⟨_, GlobalTheory.DefiniteEnd.isOpen_Kg (Vc D i) (R.βV i) (R.Pg ∪ R.Q t), fun k hk hkf g =>
      congrArg l (extV_mul_Kg R hM i t y hkf hk g)⟩
  have hkfin : FiniteDimensional ℂ (Submodule.span ℂ {ψ : GA D (Vc D i) → ℂ |
      ∃ k ∈ GinfC (Vc D i), ψ = rTr (Vc D i) k fun g => l (R.extV i t y g)}) :=
    Submodule.finiteDimensional_of_le (Submodule.span_le.2 (by
      rintro _ ⟨k, hk, rfl⟩
      exact mul_inf_mem_range R i t y l hk))
  have hdef : IsAutFunDef (Vc D i) fun g => l (R.extV i t y g) := ⟨⟨hleft, hlevel, hcont⟩, hkfin⟩
  have hdefn : (Vc D i).IsDefinite := fun τ => Or.inl (hd.pos τ)
  have hsm := ((GlobalTheory.DefiniteForms.autFunDefIffSm D) R.θ hd.inf (Vc D i) hd.sig hdefn _).1 hdef
  have hcusp : IsCuspFun (Vc D i) fun g => l (R.extV i t y g) := fun r C hC =>
    absurd hC (GlobalTheory.Per.isAniso_of_posDef hd.sig hd.pos r C)
  have hK : GlobalTheory.Doubling.IsKFinite (GlobalTheory.Cusp.Kinf R.θ (Vc D i) cA) fun g => l (R.extV i t y g) :=
    GlobalTheory.Doubling.isKFinite_iff.2 ⟨LinearMap.range (compL R i t y), inferInstance, fun k hk =>
      mul_inf_mem_range R i t y l (GlobalTheory.Cusp.Kinf_le hk)⟩
  refine ⟨GlobalTheory.Cusp.mem_cuspForms.2 ⟨⟨hsm, hcusp⟩, hK⟩, fun κ hκ g => ?_⟩
  have h1 := mem_levA.1 hκ
  have h2 : finE (Vc D i) κ ∈ Kg D.sp.cm (Vc D i).gram (R.βV i) (R.Pg ∪ R.Q t) :=
    (Model.lev_prinDat (Vc D i) (R.βV i) (R.Pg ∪ R.Q t)) ▸ h1.2
  exact congrArg l (extV_mul_Kg R hM i t y h1.1 h2 g)

end GlobalTheory.DownLift.DefiniteComp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DefiniteScalarComponentIsCuspAndCongruenceFixedAStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearForm_extV_mem_A0_and_prin_invariant : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t cA a, Defin R.θ (Vc D i) cA a → ∀ (y : (R.HV i t).H) (l : (R.cV i).W →ₗ[ℂ] ℂ), (fun g => l (R.extV i t y g)) ∈ GlobalTheory.Cusp.A0 R.θ (Vc D i) cA ∧ ∀ κ ∈ prin (Vc D i) (R.βV i) (R.Pg ∪ R.Q t), ∀ g, l (R.extV i t y (g * κ)) = l (R.extV i t y g) := by
  first | exact @GlobalTheory.DownLift.DefiniteComp.definiteScalarComponent_isCusp_and_congruence_fixed | exact GlobalTheory.DownLift.DefiniteComp.definiteScalarComponent_isCusp_and_congruence_fixed | (intros; apply GlobalTheory.DownLift.DefiniteComp.definiteScalarComponent_isCusp_and_congruence_fixed <;> assumption)
end
end
