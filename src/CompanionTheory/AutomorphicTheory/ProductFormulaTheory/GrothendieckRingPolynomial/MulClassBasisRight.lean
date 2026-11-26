module

public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.ProdList
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSstAtOfIsCrysAt
public import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.BernsteinZelevinsky.TopAdm
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientProductIrreducible

@[expose] public section

section -- merged from CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.MulClassBasisRight
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult GlobalTheory.ProdReorder

set_option synthInstance.maxHeartbeats 400000

namespace CompanionTheory.Groth

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace GrothendieckAssociativity

theorem class_congr_equiv {N : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (GL (Fin N) k) V} {τ : Representation ℂ (GL (Fin N) k) W}
    (φ : Nonempty (π.Equiv τ)) : cl0 π = cl0 τ := by
  obtain ⟨φ⟩ := φ
  unfold cl0
  by_cases h : HasFiniteLength π
  · rw [dif_pos h, dif_pos (h.of_equiv φ)]
    exact clsGL_congr φ _ _
  · rw [dite_eq_right h, dite_eq_right (fun h' => h (h'.of_equiv φ.symm))]

theorem class_induced_cast {r t N : ℕ} (h : r + t = N) {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (GL (Fin r) k × GL (Fin t) k) W) :
    cl0 (ind₂ (stdSum h) ρ) = cl0 (ind₂ (stdSum (rfl : r + t = r + t)) ρ) := by
  subst h
  rfl

theorem class_of_chosen_rep (x : IrrGL (k := k)) : cl0 (IrrGL.rep x) = sg x := by
  exact (dif_pos x.2.rep.hasFiniteLength).trans ((clsGL_irr x.2.rep x.2.rep.hasFiniteLength).trans
    (congrArg (fun c => Finsupp.single (⟨x.1, c⟩ : IrrGL (k := k)) (1 : ℤ)) x.2.cl_rep))

theorem mulR_sg (x y : IrrGL (k := k)) : mulR (sg x) (sg y) = cl0 (prod₂ (IrrGL.rep x) (IrrGL.rep y)) := by
  have h1 := Finsupp.sum_single_index (a := x) (b := (1 : ℤ)) (h := fun z m => (sg y).sum fun w n => (m * n) • cl0 (prod₂ (IrrGL.rep z) (IrrGL.rep w))) (by simp only [Finsupp.sum, zero_mul, zero_smul, Finset.sum_const_zero])
  have h2 := Finsupp.sum_single_index (a := y) (b := (1 : ℤ)) (h := fun w n => ((1 : ℤ) * n) • cl0 (prod₂ (IrrGL.rep x) (IrrGL.rep w))) (by simp only [mul_zero, zero_smul])
  exact h1.trans (h2.trans (by simp only [mul_one, one_smul]))

theorem assoc_gen (h : MulCls k) {r s t : ℕ} {V₁ V₂ V₃ U U' : Type} [AddCommGroup V₁] [Module ℂ V₁]
    [AddCommGroup V₂] [Module ℂ V₂] [AddCommGroup V₃] [Module ℂ V₃] [AddCommGroup U] [Module ℂ U]
    [AddCommGroup U'] [Module ℂ U']
    (π₁ : Representation ℂ (GL (Fin r) k) V₁) (π₂ : Representation ℂ (GL (Fin s) k) V₂)
    (π₃ : Representation ℂ (GL (Fin t) k) V₃) (P : Representation ℂ (GL (Fin (r + s)) k) U)
    (R : Representation ℂ (GL (Fin (s + t)) k) U') (φ : Nonempty (P.Equiv (prod₂ π₁ π₂)))
    (ψ : Nonempty (R.Equiv (prod₂ π₂ π₃))) (s₁ : IsSmooth π₁) (s₂ : IsSmooth π₂) (s₃ : IsSmooth π₃)
    (sP : IsSmooth P) (sR : IsSmooth R) (f₁ : HasFiniteLength π₁) (f₃ : HasFiniteLength π₃)
    (fP : HasFiniteLength P) (fR : HasFiniteLength R) :
    mulR (cl0 P) (cl0 π₃) = mulR (cl0 π₁) (cl0 R) := by
  obtain ⟨a⟩ := ind₂_congr (k := k) (rfl : r + s + t = r + s + t) φ (eqv_refl π₃)
  obtain ⟨b⟩ := ind₂_assoc' (k := k) (rfl : r + s = r + s) (rfl : r + s + t = r + s + t) (rfl : s + t = s + t)
    (Nat.add_assoc r s t).symm π₁ π₂ π₃ s₁ s₂ s₃
  obtain ⟨c⟩ := ind₂_congr (k := k) (Nat.add_assoc r s t).symm (eqv_refl π₁) (eqv_symm ψ)
  have e1 : mulR (cl0 P) (cl0 π₃) = cl0 (prod₂ P π₃) := (h _ _ _ _ P π₃ fP f₃ sP s₃).2.symm
  have e2 : cl0 (prod₂ P π₃) = cl0 (ind₂ (stdSum (Nat.add_assoc r s t).symm) (extTensor π₁ R)) :=
    class_congr_equiv ⟨(a.trans b).trans c⟩
  have e3 : cl0 (ind₂ (stdSum (Nat.add_assoc r s t).symm) (extTensor π₁ R)) = cl0 (prod₂ π₁ R) :=
    class_induced_cast (Nat.add_assoc r s t).symm (extTensor π₁ R)
  have e4 : cl0 (prod₂ π₁ R) = mulR (cl0 π₁) (cl0 R) := (h _ _ _ _ π₁ R f₁ fR s₁ sR).2
  exact e1.trans (e2.trans (e3.trans e4))

end GrothendieckAssociativity

open GrothendieckAssociativity

variable (k)

theorem assoc (h : MulCls k) : Assoc k := by
  intro x y z
  have hxy : HasFiniteLength (prod₂ (IrrGL.rep x) (IrrGL.rep y)) :=
    (h x.1 y.1 _ _ (IrrGL.rep x) (IrrGL.rep y) x.2.rep.hasFiniteLength y.2.rep.hasFiniteLength
      x.2.rep.smooth y.2.rep.smooth).1
  have hyz : HasFiniteLength (prod₂ (IrrGL.rep y) (IrrGL.rep z)) :=
    (h y.1 z.1 _ _ (IrrGL.rep y) (IrrGL.rep z) y.2.rep.hasFiniteLength z.2.rep.hasFiniteLength
      y.2.rep.smooth z.2.rep.smooth).1
  have e1 : mulR (mulR (sg x) (sg y)) (sg z) = mulR (cl0 (prod₂ (IrrGL.rep x) (IrrGL.rep y))) (cl0 (IrrGL.rep z)) :=
    (congrArg (fun a => mulR a (sg z)) (mulR_sg x y)).trans
      (congrArg (mulR (cl0 (prod₂ (IrrGL.rep x) (IrrGL.rep y)))) (class_of_chosen_rep z).symm)
  have e2 : mulR (cl0 (prod₂ (IrrGL.rep x) (IrrGL.rep y))) (cl0 (IrrGL.rep z)) =
      mulR (cl0 (IrrGL.rep x)) (cl0 (prod₂ (IrrGL.rep y) (IrrGL.rep z))) :=
    assoc_gen h (IrrGL.rep x) (IrrGL.rep y) (IrrGL.rep z) (prod₂ (IrrGL.rep x) (IrrGL.rep y))
      (prod₂ (IrrGL.rep y) (IrrGL.rep z)) (eqv_refl _) (eqv_refl _) x.2.rep.smooth y.2.rep.smooth
      z.2.rep.smooth (isSmooth_prod₂ _ _) (isSmooth_prod₂ _ _) x.2.rep.hasFiniteLength
      z.2.rep.hasFiniteLength hxy hyz
  have e3 : mulR (cl0 (IrrGL.rep x)) (cl0 (prod₂ (IrrGL.rep y) (IrrGL.rep z))) = mulR (sg x) (mulR (sg y) (sg z)) :=
    (congrArg (fun a => mulR a (cl0 (prod₂ (IrrGL.rep y) (IrrGL.rep z)))) (class_of_chosen_rep x)).trans
      (congrArg (mulR (sg x)) (mulR_sg y z).symm)
  exact e1.trans (e2.trans e3)

theorem one : One k := by
  intro x
  let c0 : IrrCl (GL (Fin 0) k) := (IrrRep.det (k := k) (Fin 0) 1 isSmoothChar_one).cl
  let e : (Σ _ : Fin 0, Fin 0) ≃ Fin 0 := Equiv.equivOfIsEmpty _ _
  let τ : ∀ a : Fin 0, Representation ℂ (GL (Fin ((fun _ : Fin 0 => 0) a)) k) ((fun _ : Fin 0 => ℂ) a) :=
    fun a => a.elim0
  have A : Nonempty ((multiProd e τ).Equiv (IrrRep.det (k := k) (Fin 0) 1 isSmoothChar_one).ρ) :=
    SupportRing.nonempty_equiv_unit e τ
  have B : Nonempty ((IrrGL.rep (⟨0, c0⟩ : IrrGL (k := k))).Equiv (multiProd e τ)) :=
    eqv_trans (IrrRep.nonempty_equiv_rep _) (eqv_symm A)
  have C : Nonempty ((ind₂ (stdSum (Nat.zero_add x.1)) (extTensor (IrrGL.rep (⟨0, c0⟩ : IrrGL (k := k))) (IrrGL.rep x))).Equiv
      (ind₂ (stdSum (Nat.zero_add x.1)) (extTensor (multiProd e τ) (IrrGL.rep x)))) :=
    ind₂_congr (k := k) (Nat.zero_add x.1) B (eqv_refl (IrrGL.rep x))
  have D : Nonempty ((ind₂ (stdSum (Nat.zero_add x.1)) (extTensor (multiProd e τ) (IrrGL.rep x))).Equiv (IrrGL.rep x)) :=
    GlobalTheory.T.parabolicInductionTwoBlocks_empty_product_left k x.1 0 (Nat.zero_add x.1) _ (IrrGL.rep x) x.2.rep.smooth (fun _ => 0) (fun _ => ℂ) τ e
  have e1 : mulR (GrothGL.unit k) (sg x) = cl0 (prod₂ (IrrGL.rep (⟨0, c0⟩ : IrrGL (k := k))) (IrrGL.rep x)) :=
    mulR_sg _ _
  have e2 : cl0 (prod₂ (IrrGL.rep (⟨0, c0⟩ : IrrGL (k := k))) (IrrGL.rep x)) =
      cl0 (ind₂ (stdSum (Nat.zero_add x.1)) (extTensor (IrrGL.rep (⟨0, c0⟩ : IrrGL (k := k))) (IrrGL.rep x))) :=
    (class_induced_cast (Nat.zero_add x.1) _).symm
  obtain ⟨c⟩ := C
  obtain ⟨dd⟩ := D
  exact e1.trans (e2.trans ((class_congr_equiv ⟨c.trans dd⟩).trans (class_of_chosen_rep x)))

end CompanionTheory.Groth
end
end

section -- merged from CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.JhMultSegCl
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M Zc.Cos

set_option synthInstance.maxHeartbeats 400000

namespace CompanionTheory.Groth

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace SegJ


open Classical in
theorem jhMult_seg_cl (hA : GlobalTheory.Published.IrreducibleAdmissibleGL)
    {Z : ∀ Δ : Segment k, IrrCl (GL (Fin (Δ.len * Δ.d)) k)} (hZ : IsSegmentClass k Z) (Δ : Segment k)
    (y : Fin Δ.len → IrrCl (GL (Fin Δ.d) k)) (hd : ∑ _ : Fin Δ.len, Δ.d = Δ.len * Δ.d) :
    jhMult (piTensor fun a => (y a).rep.ρ) (jac (stdBlocks (fun _ : Fin Δ.len => Δ.d) hd) (Z Δ).rep.ρ) =
      if (∀ a, (⟨Δ.d, y a⟩ : IrrGL (k := k)) = Δ.term a) then 1 else 0 := by
  obtain ⟨Φ⟩ := ((hZ Δ Δ.start.rep Δ.start.cl_rep (stdBlocks (fun _ : Fin Δ.len => Δ.d) hd) (Z Δ).rep).2).1
    (Z Δ).cl_rep
  let Ψ : (piTensor (segTerm Δ.start.rep.ρ Δ.len)).Equiv (piTensor fun a => (Δ.term a).rep) :=
    piTensorEquiv fun _ => Δ.first.twEquiv _ (isSmoothChar_absPow _)
  have hT : (piTensor fun a => (Δ.term a).rep).IsIrreducible :=
    GlobalTheory.CompanionTheory.FrobJm.piTensor_rep_isIrreducible hA Δ.term
  rw [jhMult_congr_right _ (Φ.trans Ψ)]
  split_ifs with h
  · have hy : ∀ a, y a = (Δ.term a).2 := fun a => eq_of_heq (Sigma.mk.inj_iff.1 (h a)).2
    obtain rfl : y = fun a => (Δ.term a).2 := funext hy
    exact jhMult_self hT
  · by_contra hne
    have hy : (piTensor fun a => (y a).rep.ρ).IsIrreducible :=
      GlobalTheory.CompanionTheory.FrobJm.piTensor_rep_isIrreducible hA (fun a => (⟨Δ.d, y a⟩ : IrrGL (k := k)))
    obtain ⟨φ⟩ := GlobalTheory.LocGL.SupportUnique.nonempty_equiv_of_isSubquotient hy hT (jhMult_ne_zero_iff.1 hne)
    have hcl := GlobalTheory.T.tensor_product_determines_factor_classes (Fin Δ.len) (fun _ => GL (Fin Δ.d) k) (fun a => (Δ.term a).2.rep)
      (fun a => (y a).rep) ⟨φ⟩
    refine h fun a => ?_
    have h1 : (Δ.term a).2 = y a := (IrrCl.cl_rep _).symm.trans ((hcl a).trans (IrrCl.cl_rep _))
    rw [← h1]
    rfl


open Classical in
theorem jm_seg (hA : GlobalTheory.Published.IrreducibleAdmissibleGL)
    {Z : ∀ Δ : Segment k, IrrCl (GL (Fin (Δ.len * Δ.d)) k)} (hZ : IsSegmentClass k Z) (Δ : Segment k)
    {m : ℕ} (y : Fin m → IrrGL (k := k)) (hy : ∀ a, (y a).1 = Δ.d) (hd : ∑ a, (y a).1 = Δ.len * Δ.d) :
    jm y hd (IrrGL.rep (⟨Δ.len * Δ.d, Z Δ⟩ : IrrGL (k := k))) =
      if ∃ h : m = Δ.len, ∀ a, y a = Δ.term (Fin.cast h a) then 1 else 0 := by
  have hm : m = Δ.len := by
    have h1 : ∑ a, (y a).1 = m * Δ.d := by simp [hy]
    exact Nat.eq_of_mul_eq_mul_right Δ.d_pos (h1.symm.trans hd)
  subst hm
  obtain ⟨y', rfl⟩ : ∃ y' : Fin Δ.len → IrrCl (GL (Fin Δ.d) k), y = fun a => ⟨Δ.d, y' a⟩ :=
    ⟨fun a => cast (congrArg (fun n => IrrCl (GL (Fin n) k)) (hy a)) (y a).2,
      funext fun a => Sigma.ext (hy a) (cast_heq _ _).symm⟩
  show jhMult (piTensor fun a => (y' a).rep.ρ) (jac (stdBlocks (fun _ : Fin Δ.len => Δ.d) hd) (Z Δ).rep.ρ) = _
  rw [jhMult_seg_cl hA hZ Δ y' hd]
  congr 1
  exact propext ⟨fun h => ⟨rfl, fun a => by simpa using h a⟩, fun ⟨_, h⟩ a => by simpa using h a⟩


open Classical in
theorem jmL_seg (hA : GlobalTheory.Published.IrreducibleAdmissibleGL)
    {Z : ∀ Δ : Segment k, IrrCl (GL (Fin (Δ.len * Δ.d)) k)} (hZ : IsSegmentClass k Z) (Δ : Segment k)
    (W : List (IrrGL (k := k))) (hW : ∀ w ∈ W, w.1 = Δ.d) (hl : W.length = Δ.len) :
    jmL W (IrrGL.rep (⟨Δ.len * Δ.d, Z Δ⟩ : IrrGL (k := k))) = if W = List.ofFn Δ.term then 1 else 0 := by
  have hy : ∀ a, (W.get a).1 = Δ.d := fun a => hW _ (List.get_mem _ _)
  have hd : ∑ a, (W.get a).1 = Δ.len * Δ.d := by
    rw [Finset.sum_congr rfl fun a _ => hy a]
    simp [hl]
  unfold jmL
  rw [dite_eq_left hd, jm_seg hA hZ Δ W.get hy hd]
  congr 1
  refine propext ⟨fun ⟨h, h2⟩ => ?_, ?_⟩
  · refine List.ext_get (by simp [h]) fun n h1 h3 => ?_
    simpa using h2 ⟨n, h1⟩
  · rintro rfl
    exact ⟨List.length_ofFn, fun a => by simp; rfl⟩

theorem vWord_ne (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) (S : Finset (Fin Δ.len))
    (hS : S ∈ vSets Δ) (hne : S ≠ ∅) : vWord Δ S ≠ List.ofFn Δ.term := by
  intro H
  rw [vWord, List.ofFn_eq_map] at H
  have H2 := (List.map_injective_iff.2 (GlobalTheory.T.segment_term_injective hA Δ)) H
  obtain ⟨s, hs⟩ := Finset.nonempty_iff_ne_empty.2 hne
  have hL1 : ((List.finRange Δ.len).filter fun a => a ∈ S) ≠ [] :=
    List.ne_nil_of_mem (List.mem_filter.2 ⟨List.mem_finRange s, by simpa using hs⟩)
  obtain ⟨x, t, hxt⟩ := List.exists_cons_of_ne_nil (List.reverse_ne_nil_iff.2 hL1)
  have hx : x ∈ S := by
    have : x ∈ ((List.finRange Δ.len).filter fun a => a ∈ S).reverse := hxt ▸ List.mem_cons_self ..
    simpa using this
  rw [hxt] at H2
  have h0 := congrArg (fun L => L[0]?) H2
  simp at h0
  have h3 := (Finset.mem_filter.1 hS).2 x hx
  rw [List.getElem?_eq_getElem (by simpa using Δ.len_pos)] at h0
  have h4 := Option.some.inj h0
  apply h3
  rw [h4]
  simp

end SegJ


open SegJ in
variable (k) in
theorem jSeg : JSeg k := by
  intro Z hZ Δ
  have hA := CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  have hterm : ∀ a, (Δ.term a).1 = Δ.d := fun _ => rfl
  refine ⟨?_, fun S hS hne => ?_⟩
  · rw [jmL_seg hA hZ Δ _ (fun w hw => by rw [List.mem_ofFn] at hw; obtain ⟨a, rfl⟩ := hw; rfl) List.length_ofFn, if_pos rfl]
  · rw [jmL_seg hA hZ Δ _ ?_ ?_, if_neg (vWord_ne hA Δ S hS hne)]
    · intro w hw
      obtain ⟨a, -, rfl⟩ := List.mem_map.1 hw
      rfl
    · simp [vWord]
      rw [← List.length_eq_length_filter_add]
      simp

end CompanionTheory.Groth

end
end
