module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IntegralityNearIdentity.TensEig
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.StabSp
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocallyConstantCompactSupportUnipotent
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.SuppCusp

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.ImportsAlt
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

theorem UpperTheory.V.Cj.S.step :
    UpperTheory.V.Cj.S.PairEig → UpperTheory.V.Cj.S.SliceBdd → UpperTheory.V.Cj.S.Iwa → UpperTheory.V.Cj.S.CtCap → UpperTheory.V.Cj.S.CtSat → UpperTheory.V.Cj.S.CapRel → UpperTheory.V.Cj.S.HkRel → UpperTheory.V.Cj.S.CapArith → UpperTheory.V.Cj.S.SatArith → UpperTheory.V.Cj.S.Step := by
  intro hPair hSlice hIwa hCtCap hCtSat hCapRel hHkRel hCapA hSatA E _ _ _ r s φ₀ m B h₀ hne₀
  obtain ⟨φ, hφ, hne⟩ := hIwa E r s φ₀ m B h₀ hne₀
  obtain ⟨S₁, S₂, hS₁, hS₂, hs₁, hs₂⟩ := hSlice E r s φ hφ.aut
  obtain ⟨ψ, hψ, hNI, hcap⟩ := hCtCap E (r + s) r φ hφ.aut
  rw [← hψ] at hne hs₁ hs₂
  have hψ0 : ψ ≠ 0 := by
    rintro rfl
    obtain ⟨x, y, h⟩ := hne
    exact h rfl
  obtain ⟨φ₁, φ₂, m₁, m₂, B₁, B₂, h₁, h₂, hc, hs⟩ := hPair E r s (res ψ.1) S₁ S₂ hS₁ hS₂ hne hs₁ hs₂
  refine ⟨φ₁, φ₂, m₁, m₂, B₁, B₂, h₁, h₂, fun t => ?_, fun ν ν' hν hν' => ?_⟩
  · refine hCapA (m t) (m₁ t) (m₂ t) _ _ fun u => ?_
    have e1 : u + ((-((s : ℝ) / 2) : ℝ) : ℂ) = u - (s : ℂ) / 2 := by push_cast; ring
    have e2 : u + (((r : ℝ) / 2 : ℝ) : ℂ) = u + (r : ℂ) / 2 := by push_cast; ring
    rw [e1, e2]
    refine hc t _ _ _ _ (hCapRel E r s ψ hNI t u) fun x y => ?_
    rw [hcap t u, (hφ.cap t).2 u, hψ]
    simp only [res, constantTerm, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
    exact MeasureTheory.integral_const_mul _ _
  · filter_upwards [hφ.sat, h₁.sat, h₂.sat, hs] with w hw hw₁ hw₂ hw₃
    have hv := hCtSat E (r + s) r φ ψ hφ.aut hψ hψ0 w (B w) hw
    obtain ⟨ϖ, hu⟩ := exists_isUnifV w
    refine hSatA (qV E w) r s (qV_ne_zero w) (B w) (B₁ w) (B₂ w) hw.2.2.1 hw₁.2.2.1 hw₂.2.2.1 (fun j hj => ?_) _ _ ?_ ?_
    · obtain ⟨G, hG, hsum⟩ := hHkRel E r s ψ hNI w hv.2.1 ϖ hu j hj
      refine hw₃ ϖ hu _ G _ hG fun x y => ?_
      rw [hsum x y]
      have : tOp (r + s) w hu j ψ = satEig (qV E w) (r + s) (B w) j • ψ := hv.2.2.2 ϖ hu j hj
      rw [this]
      rfl
    · rw [hν.2.1 w]
      congr 1
      push_cast; ring
    · rw [hν'.2.1 w]
      congr 1
      push_cast; ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.TwoVar
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

namespace UpperTheory.V.Cj.S

section SlopeTestRemainingChoices

variable {X Y V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

private noncomputable def sl1 (jW : W →ₗ[ℂ] (Y → ℂ)) (y : Y) : V ⊗[ℂ] W →ₗ[ℂ] V :=
  (TensorProduct.rid ℂ V).toLinearMap ∘ₗ LinearMap.lTensor V (LinearMap.proj y ∘ₗ jW)

private theorem slice_first_tmul (jW : W →ₗ[ℂ] (Y → ℂ)) (y : Y) (v : V) (w : W) : sl1 jW y (v ⊗ₜ[ℂ] w) = jW w y • v := by
  simp [sl1]

end SlopeTestRemainingChoices

end UpperTheory.V.Cj.S

private theorem tensor_exists_finBasis_expansion {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ V] (t : V ⊗[ℂ] W) :
    ∃ m : Fin (Module.finrank ℂ V) → W, t = ∑ a, Module.finBasis ℂ V a ⊗ₜ[ℂ] m a := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul v w =>
    refine ⟨fun a => (Module.finBasis ℂ V).repr v a • w, ?_⟩
    conv_lhs => rw [← (Module.finBasis ℂ V).sum_repr v]
    rw [TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    exact TensorProduct.smul_tmul _ _ _
  | add t1 t2 h1 h2 =>
    obtain ⟨m1, rfl⟩ := h1
    obtain ⟨m2, rfl⟩ := h2
    exact ⟨m1 + m2, by simp [TensorProduct.tmul_add, Finset.sum_add_distrib]⟩

private theorem tensor_eq_zero_of_sl1_vanishing {V W Y : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ V] (jW : W →ₗ[ℂ] (Y → ℂ)) (hjW : Function.Injective jW) (t : V ⊗[ℂ] W)
    (ht : ∀ y, UpperTheory.V.Cj.S.sl1 jW y t = 0) : t = 0 := by
  obtain ⟨m, rfl⟩ := tensor_exists_finBasis_expansion (V := V) (W := W) t
  have hm : ∀ a, m a = 0 := by
    intro a
    apply hjW
    rw [map_zero]
    funext y
    have hy := ht y
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, UpperTheory.V.Cj.S.slice_first_tmul] at hy
    have := (Fintype.linearIndependent_iff.mp (Module.finBasis ℂ V).linearIndependent) (fun a => jW (m a) y) hy a
    simpa using this
  simp [hm]

private theorem exists_vec_of_dual_apply_col {X Y V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ V] (jV : V →ₗ[ℂ] (X → ℂ)) (hjV : Function.Injective jV)
    (jW : W →ₗ[ℂ] (Y → ℂ)) (col : Y → V) (hrow : ∀ x, ∃ w : W, jW w = fun y => jV (col y) x)
    (φ : Module.Dual ℂ V) : ∃ w : W, jW w = fun y => φ (col y) := by
  let P : Submodule ℂ (Module.Dual ℂ V) :=
    { carrier := {ψ | ∃ w : W, jW w = fun y => ψ (col y)}
      add_mem' := by
        rintro ψ χ ⟨w1, h1⟩ ⟨w2, h2⟩
        exact ⟨w1 + w2, by rw [map_add (f := _), h1, h2]; rfl⟩
      zero_mem' := ⟨0, by rw [map_zero]; rfl⟩
      smul_mem' := by
        rintro c ψ ⟨w, h⟩
        exact ⟨c • w, by rw [map_smul, h]; rfl⟩ }
  have hev : ∀ x, (LinearMap.proj x ∘ₗ jV) ∈ P := by
    intro x
    obtain ⟨w, h⟩ := hrow x
    exact ⟨w, h⟩
  have hco : P.dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_dualCoannihilator] at hv
    rw [Submodule.mem_bot]
    apply hjV
    funext x
    simpa using hv _ (hev x)
  have htop : P = ⊤ := by
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := P), hco, Submodule.dualAnnihilator_bot]
  have hφ : φ ∈ P := by
    rw [htop]
    exact Submodule.mem_top
  exact hφ

theorem UpperTheory.V.Cj.S.twoVar :
    UpperTheory.V.Cj.S.TensEig → UpperTheory.V.Cj.S.TwoVar := by
  intro hT X Y M N V W hVf hWf ι κ A B hAV hBW hAc hBc F hF hcol hrow
  let jV : V →ₗ[ℂ] (X → ℂ) := M.subtype ∘ₗ V.subtype
  let jW : W →ₗ[ℂ] (Y → ℂ) := N.subtype ∘ₗ W.subtype
  have hjV : Function.Injective jV := Subtype.val_injective.comp Subtype.val_injective
  have hjW : Function.Injective jW := Subtype.val_injective.comp Subtype.val_injective
  choose col hcolV hcolF using hcol
  let colV : Y → V := fun y => ⟨col y, hcolV y⟩
  have hjcol : ∀ y, jV (colV y) = fun x => F x y := fun y => hcolF y
  have hrow' : ∀ x, ∃ w : W, jW w = fun y => jV (colV y) x := by
    intro x
    obtain ⟨f, hfW, hf⟩ := hrow x
    refine ⟨⟨f, hfW⟩, ?_⟩
    funext y
    rw [hjcol]
    show (f : Y → ℂ) y = F x y
    rw [hf]
  let bV := Module.finBasis ℂ V
  choose w hw using fun a => exists_vec_of_dual_apply_col jV hjV jW colV hrow' (bV.coord a)
  let z : V ⊗[ℂ] W := ∑ a, bV a ⊗ₜ[ℂ] w a
  have hz : ∀ y, UpperTheory.V.Cj.S.sl1 jW y z = colV y := by
    intro y
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [z, map_sum, UpperTheory.V.Cj.S.slice_first_tmul, hw]
    simpa [Module.Basis.coord_apply] using bV.sum_repr (colV y)
  have hFz : ∀ x y, jV (UpperTheory.V.Cj.S.sl1 jW y z) x = F x y := by
    intro x y
    rw [hz, hjcol]
  have hz0 : z ≠ 0 := by
    obtain ⟨x0, y0, h0⟩ := hF
    intro h
    apply h0
    rw [← hFz, h]
    simp
  let A' : ι → Module.End ℂ V := fun i => (A i).restrict (hAV i)
  let B' : κ → Module.End ℂ W := fun k => (B k).restrict (hBW k)
  have hA' : ∀ i (v : V), ((A' i v : V) : M) = A i v := fun i v => rfl
  have hB' : ∀ k (w : W), ((B' k w : W) : N) = B k w := fun k w => rfl
  have cA : ∀ i i', Commute (A' i) (A' i') := by
    intro i i'
    exact LinearMap.ext fun v => Subtype.ext (hAc i i' v v.2)
  have cB : ∀ k k', Commute (B' k) (B' k') := by
    intro k k'
    exact LinearMap.ext fun w => Subtype.ext (hBc k k' w w.2)
  obtain ⟨v, w', l, m, hv, hw', hAv, hBw, hprop⟩ := hT V W ι κ A' B' cA cB z hz0
  refine ⟨v, v.2, w', w'.2, l, m, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    exact hv (Subtype.ext h)
  · intro h
    exact hw' (Subtype.ext h)
  · intro i
    have := congrArg Subtype.val (hAv i)
    simpa [hA'] using this
  · intro k
    have := congrArg Subtype.val (hBw k)
    simpa [hB'] using this
  · intro σ _ c ip kp G e hAct hsum
    have hsumV : ∀ y', (∑ a, jW (w a) y' • bV a) = colV y' := by
      intro y'
      simpa [hw, Module.Basis.coord_apply] using bV.sum_repr (colV y')
    have key : ∀ i k (Gp : X → Y → ℂ), Act2 (A i) (B k) F Gp → ∀ x y,
        jV (UpperTheory.V.Cj.S.sl1 jW y (TensorProduct.map (A' i) (B' k) z)) x = Gp x y := by
      intro i k Gp hG x y
      obtain ⟨H, h1, h2⟩ := hG
      have hH : ∀ x' y', H x' y' = ∑ a, jW (w a) y' * jV (A' i (bV a)) x' := by
        intro x' y'
        obtain ⟨f, hf1, hf2⟩ := h1 y'
        have hf : f = ((∑ a, jW (w a) y' • bV a : V) : M) := by
          apply Subtype.val_injective
          rw [hf1, hsumV]
          exact (hjcol y').symm
        have := congrFun hf2 x'
        rw [← this, hf]
        set_option synthInstance.maxHeartbeats 100000 in
          simp [map_sum, jV, hA']
      obtain ⟨f', hf'1, hf'2⟩ := h2 x
      have hf' : f' = ((∑ a, jV (A' i (bV a)) x • w a : W) : N) := by
        apply Subtype.val_injective
        rw [hf'1]
        funext y'
        rw [hH]
        simp [jW, jV, Finset.sum_apply, mul_comm]
      rw [← hf'2, hf']
      set_option synthInstance.maxHeartbeats 100000 in
        simp [z, map_sum, TensorProduct.map_tmul, UpperTheory.V.Cj.S.slice_first_tmul, jV, jW, hB', mul_comm]
    apply hprop σ c ip kp e
    rw [← sub_eq_zero]
    apply tensor_eq_zero_of_sl1_vanishing jW hjW
    intro y
    apply hjV
    rw [map_zero]
    funext x
    have key' : ∀ p, jV (UpperTheory.V.Cj.S.sl1 jW y (TensorProduct.map (A' (ip p)) (B' (kp p)) z)) x = G p x y :=
      fun p => key _ _ _ (hAct p) x y
    have hval : jV (UpperTheory.V.Cj.S.sl1 jW y
        (∑ p, c p • TensorProduct.map (A' (ip p)) (B' (kp p)) z - e • z)) x = ∑ p, c p * G p x y - e * F x y := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sub, map_sum, map_smul, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, key', hFz]
    rw [hval, hsum, sub_self]
    rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.CapRel
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

private theorem slice_cap (h : UpperTheory.V.Cj.S.Slice) {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a n : ℕ}
    (e : Fin a ↪ Fin n) (g : GA E n) :
    ∃ f : Sm E n →ₗ[ℂ] Sm E a, (∀ ψ x, (f ψ).1 x = ψ.1 (g * emb e x)) ∧
      ∀ t u ψ, cap t u (f ψ) = f (capB e t u ψ) := by
  obtain ⟨f, hf, hE⟩ := h E a n e g
  exact ⟨f, hf, fun t u ψ => (UpperTheory.algMod_of_injective_intertwining _ _ a f _ _ (hE t) _ ψ).symm⟩

theorem UpperTheory.V.Cj.S.capRel :
    UpperTheory.V.Cj.S.Slice → UpperTheory.V.Cj.S.CapBlock → UpperTheory.V.Cj.S.CapRel := by
  intro hS hB E _ _ _ r s ψ hψ t u
  refine ⟨res (capB (e1 r s) t (u - (s : ℂ) / 2) ψ).1, fun y => ?_, fun x => ?_⟩
  · obtain ⟨f, hf, hc⟩ := slice_cap hS (e1 r s) (emb (e2 r s) y)
    have key : ∀ φ : Sm E (r + s), (f φ).1 = fun x => res φ.1 x y := fun φ => funext fun x => by
      rw [hf, res, blk, UpperTheory.V.Af.Fin.emb_comm]
    exact ⟨f ψ, key ψ, by rw [hc, key]⟩
  · obtain ⟨f, hf, hc⟩ := slice_cap hS (e2 r s) (emb (e1 r s) x)
    have key : ∀ φ : Sm E (r + s), (f φ).1 = res φ.1 x := fun φ => funext fun y => hf φ y
    refine ⟨f _, key _, ?_⟩
    rw [hc, key]
    exact funext fun y => (hB E r s ψ hψ t u x y).symm
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.CapOfEig
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

theorem UpperTheory.V.Cj.S.capOfEig :
    UpperTheory.V.Cj.S.CapOfEig := by
  intro E _ _ _ a φ h0 hc
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℂ h0
  have key : ∀ t : E →+* ℂ, ∃ m : Multiset ℂ, Multiset.card m = a ∧
      ∀ u : ℂ, cap t u φ = (m.map (u + ·)).prod • φ := fun t => by
    obtain ⟨m, hm, h⟩ := GlobalTheory.CuspRep.exists_multiset_qdet (Eop (a := a) t) (((a : ℂ) - 1) / 2) φ f hf
    refine ⟨m, hm, fun u => ?_⟩
    obtain ⟨c, h1⟩ := hc t u
    have h2 : f (cap t u φ) = _ := h u
    rw [h1, map_smul, hf, smul_eq_mul, mul_one] at h2
    rw [h1, h2]
  choose m hm h using key
  exact ⟨m, fun t => ⟨hm t, h t⟩⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.CapArith
open Polynomial

namespace UpperTheory.V.Cj.S

private theorem eq_of_prod_eq (m n : Multiset ℂ) (h : ∀ u : ℂ, (m.map (u + ·)).prod = (n.map (u + ·)).prod) : m = n := by
  have key : ∀ (k : Multiset ℂ) (u : ℂ),
      (((k.map fun x => -x).map fun x => X - C x).prod).eval u = (k.map (u + ·)).prod := by
    intro k u
    rw [eval_multiset_prod, Multiset.map_map, Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun x _ => ?_
    simp
  have hp : ((m.map fun x => -x).map fun x => X - C x).prod = ((n.map fun x => -x).map fun x => X - C x).prod :=
    Polynomial.funext fun u => by rw [key, key, h]
  have hr := congrArg Polynomial.roots hp
  rw [roots_multiset_prod_X_sub_C, roots_multiset_prod_X_sub_C] at hr
  exact Multiset.map_injective neg_injective hr

theorem capArith : CapArith := by
  intro m m₁ m₂ α β h
  refine eq_of_prod_eq _ _ fun u => ?_
  rw [← h u, Multiset.map_add (f := _), Multiset.prod_add, Multiset.map_map, Multiset.map_map]
  congr 2
  · exact Multiset.map_congr rfl fun x _ => by simp only [Function.comp]; ring
  · exact Multiset.map_congr rfl fun x _ => by simp only [Function.comp]; ring

end UpperTheory.V.Cj.S
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.SingleBdd
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

private theorem exists_types {G H : Type} [Group G] [Group H] (i : H →* G) (W : Submodule ℂ (G → ℂ))
    [FiniteDimensional ℂ W] (hW : ∀ h, ∀ f ∈ W, (fun g => f (g * i h)) ∈ W) :
    ∃ V : Submodule ℂ (H → ℂ), FiniteDimensional ℂ V ∧ (∀ f ∈ V, ∀ k', (fun k => f (k * k')) ∈ V) ∧
      ∀ f ∈ W, ∀ g, (fun k => f (g * i k)) ∈ V := by
  let ρ : H → W →ₗ[ℂ] W := fun h => (LinearMap.funLeft ℂ ℂ fun g => g * i h).restrict (hW h)
  have hρ : ∀ k k' w, ρ (k * k') w = ρ k (ρ k' w) := fun k k' w =>
    Subtype.ext (funext fun g => by
      change w.1 (g * i (k * k')) = w.1 (g * i k * i k')
      rw [map_mul, mul_assoc])
  let m : Module.Dual ℂ W →ₗ[ℂ] W →ₗ[ℂ] (H → ℂ) :=
    LinearMap.mk₂ ℂ (fun l w k => l (ρ k w)) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
      (fun _ _ _ => by funext k; simp) (fun _ _ _ => by funext k; simp)
  refine ⟨LinearMap.range (TensorProduct.lift m), inferInstance, ?_, fun f hf g => ?_⟩
  · rintro _ ⟨t, rfl⟩ k'
    induction t using TensorProduct.inductionOn with
    | tmul l w => exact ⟨l ⊗ₜ ρ k' w, funext fun k => congrArg l (hρ k k' w).symm⟩
    | add s t hs ht => rw [map_add]; exact add_mem hs ht
  · exact ⟨((LinearMap.proj g).comp W.subtype) ⊗ₜ ⟨f, hf⟩, rfl⟩

private theorem exists_types' {G H : Type} [Group G] [Group H] (i : H →* G) (C : Subgroup G) (hi : ∀ k, i k ∈ C) (f : G → ℂ)
    (hf : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : C => GroundTheory.Automorphic.rightTranslate (k : G) f))) :
    ∃ V : Submodule ℂ (H → ℂ), FiniteDimensional ℂ V ∧ (∀ f ∈ V, ∀ k', (fun k => f (k * k')) ∈ V) ∧
      ∀ g, (fun k => f (g * i k)) ∈ V := by
  obtain ⟨V, h1, h2, h3⟩ := exists_types i
    (Submodule.span ℂ (Set.range fun k : C => GroundTheory.Automorphic.rightTranslate (k : G) f)) (fun k ψ hψ => by
      induction hψ using Submodule.span_induction with
      | mem ψ hψ =>
        obtain ⟨l, rfl⟩ := hψ
        exact Submodule.subset_span ⟨⟨i k, hi k⟩ * l, funext fun g => congrArg f (mul_assoc g (i k) l.1).symm⟩
      | zero => exact zero_mem _
      | add _ _ _ _ a b => exact add_mem a b
      | smul c _ _ a => exact Submodule.smul_mem _ c a)
  exact ⟨V, h1, h2, h3 f (Submodule.subset_span ⟨1, funext fun g => congrArg f (mul_one g)⟩)⟩

private theorem exists_monic {M : Type} [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M) (W : Submodule ℂ M)
    [FiniteDimensional ℂ W] (hW : ∀ x ∈ W, T x ∈ W) : UpperTheory.V.Af.Fin.AlgMod W ⊥ T := by
  obtain ⟨p, hp, h⟩ := LinearMap.exists_monic_and_aeval_eq_zero ℂ (T.restrict hW)
  refine ⟨p, hp, fun x hx => ?_⟩
  have key : ∀ q : Polynomial ℂ, Polynomial.aeval T q x = (Polynomial.aeval (T.restrict hW) q ⟨x, hx⟩ : W) := by
    intro q
    induction q using Polynomial.induction_on' with
    | add q r hq hr => simp only [map_add (f := _), LinearMap.add_apply, hq, hr, Submodule.coe_add]
    | monomial n c =>
      simp only [Polynomial.aeval_monomial, mul_apply_eq_comp, Module.algebraMap_end_apply, Submodule.coe_smul,
        Module.End.pow_restrict n hW, LinearMap.restrict_apply]
  rw [key, h]
  rfl

open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm in
private theorem bdd_span {K : Type} [Field K] [NumberField K] {n : ℕ} (f : archSmooth K n) (h : IsAutomorphicForm f.1) :
    Bdd (Submodule.span ℂ {f}) := by
  refine ⟨fun φ hφ => ?_, fun φ hφ => ?_, ?_, ?_, fun z hz => ?_⟩
  · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hφ
    exact h.isLeftInvariant.smul c
  · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hφ
    exact h.hasModerateGrowth.smul c
  · obtain ⟨U, -, hU⟩ := exists_openSubgroup_rightInvariant h.isSmooth h.isKFinite
    refine ⟨U.toSubgroup, U.isOpen, fun φ hφ u hu g => ?_⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hφ
    exact congrArg (c • ·) (hU g u hu)
  · have hK := h.isKFinite
    unfold IsKFinite at hK
    obtain ⟨V, h1, h2, h3⟩ := exists_types' ((infEmb K n).comp (archCompact K n).subtype) Reduction.maxCompact
      (fun k => k.2) f.1 hK
    refine ⟨V, h1, h2, fun φ hφ g => ?_⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hφ
    exact V.smul_mem c (h3 g)
  · have hZ : IsZFinite f := h.isZFinite
    unfold IsZFinite at hZ
    refine (exists_monic (uAction z) (Submodule.span ℂ
      ((fun z => uAction z f) '' ((isExpLieAlgebra K n).centerU : Set (UEnv K n)))) (fun ψ hψ => ?_)).mono
      (Submodule.span_mono ?_)
    · induction hψ using Submodule.span_induction with
      | mem ψ hψ =>
        obtain ⟨y, hy, rfl⟩ := hψ
        exact Submodule.subset_span ⟨z * y, mul_mem hz hy, by simp only [map_mul, mul_apply_eq_comp]⟩
      | zero => rw [map_zero]; exact zero_mem _
      | add _ _ _ _ a b => rw [map_add]; exact add_mem a b
      | smul c _ _ a => rw [map_smul]; exact Submodule.smul_mem _ c a
    · rintro _ rfl
      exact ⟨1, one_mem _, by simp only [map_one, Module.End.one_apply]⟩

theorem UpperTheory.V.Cj.S.singleBdd :
    UpperTheory.V.Cj.S.SingleBdd := by
  intro E _ _ _ a φ h
  unfold BddS
  rw [Submodule.map_span, Set.image_singleton]
  exact bdd_span _ ((UpperTheory.V.Cm.isAutForm_iff φ).1 h)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.SuppTwist
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

private theorem sum_map {ι α : Type} [Fintype ι] (f : α → α) (C : ι → Multiset α) :
    ∑ i, (C i).map f = (∑ i, C i).map f := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← Multiset.coe_mapAddMonoidHom, map_sum]

private theorem sat_twist {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (π : CG E a) {w : Pl E}
    {B : Multiset ℂˣ} (h : π.HasSat w B) {χ : HChar E} (hχ : χ.UnrAt w) :
    (π.twist χ).HasSat w (B.map (· * χ.val w)) := by
  induction π using Quotient.inductionOn
  exact GlobalTheory.SphGal.hasSatGL_twist _ _ _ χ w B hχ h

theorem UpperTheory.V.Cj.S.suppTwist :
    UpperTheory.V.Cj.S.SuppTwist := by
  rintro E _ _ _ a k m B ⟨ι, _, n, π, μ, hk, hn, ha, hμ, hm, hB⟩ x ν hν
  refine ⟨ι, inferInstance, n, fun i => (π i).twist ν, fun i t => (μ i t).map (· + (x : ℂ)), hk, hn, ha,
    fun i t => ?_, fun t => ?_, hB.mono ?_⟩
  · have h := (hμ i t).twist ν
    rwa [(InfType.expo_of_infType E ν).2.1 x hν t] at h
  · rw [sum_map, hm]
  · rintro w ⟨C, hC, hs⟩
    exact ⟨fun i => (C i).map (· * ν.val w), fun i => sat_twist _ (hC i) (hν.1 w), by rw [sum_map, hs]⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.CtSat
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

theorem UpperTheory.V.Cj.S.ctSat :
    UpperTheory.V.Cj.S.CtSat := by
  intro E _ _ _ n r φ ψ hφ hψ h0 w B hB
  let C : Submodule ℂ (Sm E n) :=
    { carrier := {f | Continuous f.1}
      add_mem' := fun h h' => Continuous.add h h'
      zero_mem' := continuous_const
      smul_mem' := fun c _ h => Continuous.const_smul h c }
  have hC : ∀ g, ∀ f ∈ C, fL n w g f ∈ C := fun g f hf =>
    show Continuous fun x => f.1 (x * finGL E n (locGL E n w g)) from
      Continuous.comp (show Continuous f.1 from hf) (continuous_id.mul continuous_const)
  have hc : φ ∈ C := ((UpperTheory.V.Cm.isAutForm_iff φ).1 hφ).continuous
  let F : C →ₗ[ℂ] (GA E n → ℂ) :=
    { toFun := fun f => constantTerm r f.1.1
      map_add' := fun f f' => funext fun g => GroundTheory.Automorphic.AutomorphicForm.constantTerm_add f.2 f'.2 g
      map_smul' := fun c f => funext fun g => GroundTheory.Automorphic.AutomorphicForm.constantTerm_smul c f.1.1 g }
  have h1 : IsSatVecGL w (GlobalTheory.PRep.sub (fL n w) C hC) ⟨φ, hc⟩ B :=
    IsSatVecGL.of_map C.subtype (fun _ _ => rfl) Subtype.val_injective hB
  have hF : F ⟨φ, hc⟩ = ψ.1 := hψ.symm
  have h2 := h1.map (ρ' := (GlobalTheory.PRep.rightReg ℂ (GA E n) ℂ).comp ((finGL E n).comp (locGL E n w))) F
    (fun g f => funext fun x =>
      GroundTheory.Automorphic.AutomorphicForm.constantTerm_rightTranslate f.1.1 (finGL E n (locGL E n w g)) x)
    (by rw [hF]; exact fun h => h0 (Subtype.ext h))
  rw [hF] at h2
  exact IsSatVecGL.of_map (Sm E n).subtype (fun _ _ => rfl) Subtype.val_injective h2
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.CapBlock
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

private theorem cast_ne_nat {r s : ℕ} (i : Fin r) (j : Fin s) : Fin.castAdd s i ≠ Fin.natAdd r j := fun h => by
  have := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at this
  omega

private theorem std_eq (r s : ℕ) : GlobalTheory.SmGL.stdSum (rfl : r + s = r + s) = finSumFinEquiv :=
  Equiv.ext fun _ => rfl

open UpperTheory.V.Af.Fin in
private theorem lev_left {R : Type} [CommRing R] {r s : ℕ} (x : GL (Fin r) R) :
    GlobalTheory.CompanionTheory.CTFin.lev R r s (x, 1) = emb (e1 r s) x := by
  refine Units.ext ?_
  rw [GlobalTheory.SmGL.val_emb₂, coe_emb, std_eq]
  ext i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · have := matrixExtendByZero_apply (e1 r s) (x.val - 1) i j
    simp only [orderedCechToCatCochainsOne_apply_valueAtSubset] at this
    simp [this, Matrix.one_apply]
  · rw [Matrix.add_apply, matrixExtendByZero_apply_of_outside_col _ _ _ fun k => (cast_ne_nat k j).symm]
    simp [Matrix.one_apply, cast_ne_nat]
  · rw [Matrix.add_apply, extendByZero_apply_eq_zero_of_row_not_mem _ _ fun k => (cast_ne_nat k i).symm]
    simp [Matrix.one_apply, (cast_ne_nat _ _).symm]
  · rw [Matrix.add_apply, extendByZero_apply_eq_zero_of_row_not_mem _ _ fun k => (cast_ne_nat k i).symm]
    simp [Matrix.one_apply]

open UpperTheory.V.Af.Fin in
private theorem lev_right {R : Type} [CommRing R] {r s : ℕ} (y : GL (Fin s) R) :
    GlobalTheory.CompanionTheory.CTFin.lev R r s (1, y) = emb (e2 r s) y := by
  refine Units.ext ?_
  rw [GlobalTheory.SmGL.val_emb₂, coe_emb, std_eq]
  ext i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · rw [Matrix.add_apply, extendByZero_apply_eq_zero_of_row_not_mem _ _ fun k => cast_ne_nat i k]
    simp [Matrix.one_apply]
  · rw [Matrix.add_apply, extendByZero_apply_eq_zero_of_row_not_mem _ _ fun k => cast_ne_nat i k]
    simp [Matrix.one_apply, cast_ne_nat]
  · rw [Matrix.add_apply, matrixExtendByZero_apply_of_outside_col _ _ _ fun k => cast_ne_nat j k]
    simp [Matrix.one_apply, (cast_ne_nat _ _).symm]
  · have := matrixExtendByZero_apply (e2 r s) (y.val - 1) i j
    simp only [alternatingToOrderedCechDegreeTwo_apply_valueAtSubset] at this
    simp [this, Matrix.one_apply]

private theorem lev_eq_blk {R : Type} [CommRing R] {r s : ℕ} (x : GL (Fin r) R) (y : GL (Fin s) R) :
    GlobalTheory.CompanionTheory.CTFin.lev R r s (x, y) = blk x y := by
  rw [blk, ← lev_left, ← lev_right, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]

theorem UpperTheory.V.Cj.S.capBlock :
    UpperTheory.V.Cj.S.CapBlock := by
  intro E _ _ _ r s ψ hψ t u x y
  have h := GlobalTheory.CompanionTheory.CTFin.CapFactor.cap_levi E r s t u ψ (fun X g => by
    have e : unip X = unipGL (fun p : UPos (r + s) r => X ⟨p.1, p.2.1, p.2.2⟩) := Units.ext rfl
    rw [e]
    exact hψ _ g) (x, y)
  rw [lev_eq_blk] at h
  exact h
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HullOps
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

section

open UpperTheory.V

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem hull_stable {T : Module.End ℂ (Sm E a)} (hT : T ∈ Comm E a) (S : Submodule ℂ (Sm E a)) :
    ∀ φ ∈ hull S, T φ ∈ hull S := by
  have : hull S ≤ (hull S).comap T := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨T', hT', φ, hφ, rfl⟩
    exact Submodule.subset_span ⟨T * T', ⟨fun k => (hT.1 k).mul_left (hT'.1 k),
      fun z hz => (hT.2.1 z hz).mul_left (hT'.2.1 z hz), fun ψ h => hT.2.2 _ (hT'.2.2 ψ h)⟩, φ, hφ, rfl⟩
  exact fun φ hφ => this hφ

private theorem aut_cap (t : E →+* ℂ) (u : ℂ) (φ : Sm E a) (h : IsAutForm φ) : IsAutForm (cap t u φ) := by
  obtain ⟨p, -, q, -, e⟩ := Cm.mem_Zalg_iff.1 (Cm.cap_mem_Zalg (a := a) t u)
  obtain ⟨ψ, rfl⟩ := Cm.mem_range_ofAut.2 h
  refine Cm.mem_range_ofAut.1 ⟨GroundTheory.Automorphic.AutomorphicForm.uActionAF E a p ψ +
    Complex.I • GroundTheory.Automorphic.AutomorphicForm.uActionAF E a q ψ, ?_⟩
  rw [e, map_add (f := _), map_smul]
  rfl

private theorem smEq_fin (g : GL (Fin a) (Af E)) (φ : Sm E a) :
    Cm.smEq E a (finRep E a g φ) = GroundTheory.Automorphic.AutomorphicForm.rtFin g (Cm.smEq E a φ) :=
  Subtype.ext (funext fun x => (congrArg (fun f : GL (Fin a) (Af E) →* GA E a => φ.1 (x * f g)) Fb.finEmb_eq).symm)

private theorem fin_mem (g : GL (Fin a) (Af E)) : finRep E a g ∈ Comm E a := by
  refine ⟨fun k => ?_, fun z _ => ?_, fun φ h => ?_⟩
  · exact Commute.map (show Commute (finGL E a g) (infGL E a (Unitary.toUnits k)) from (infGL_comm _ _).symm) (rt E a)
  · refine LinearMap.ext fun φ => (Cm.smEq E a).injective ?_
    rw [Module.End.mul_apply, Module.End.mul_apply, smEq_fin, Cm.smEq_uTC, Cm.smEq_uTC, smEq_fin,
      GroundTheory.Automorphic.AutomorphicForm.uAction_rtFin]
  · refine (Cm.isAutForm_iff _).2 ?_
    rw [← Cm.coe_smEq, smEq_fin]
    exact ((Cm.isAutForm_iff _).1 h).rightTranslate_finEmb g

end

theorem UpperTheory.V.Cj.S.hullOps :
    UpperTheory.V.Cj.S.CapAct → UpperTheory.V.Cj.S.HullOps := by
  intro hc E _ _ _ a S
  refine ⟨fun φ hφ => Submodule.subset_span ⟨1, ⟨fun _ => Commute.one_left _, fun _ _ => Commute.one_left _,
    fun _ h => h⟩, φ, hφ, rfl⟩, fun t u => hull_stable ⟨fun k => (hc E a t u).2.1 (.cpt k),
      fun z _ => (hc E a t u).2.2.1 z, aut_cap t u⟩ S, fun g => hull_stable (fin_mem g) S⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.PairEig
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

private theorem UpperTheory.V.Cj.S.eig_of_joint (hS : SatOfEig) (hC : CapOfEig)
    {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} {T : Set (Pl E)} (hT : T.Finite)
    (φ : Sm E a) (h0 : φ ≠ 0) (haut : IsAutForm φ) (hfix : ∀ w ∉ T, φ ∈ fixed (fL a w) (KGL w (n := a)))
    (l : Ix a T → ℂ) (hl : ∀ i, opIx i φ = l i • φ) :
    ∃ (m : (E →+* ℂ) → Multiset ℂ) (B : Pl E → Multiset ℂˣ), Eig φ m B ∧
      (∀ t u, l (.inl (t, u)) = ((m t).map (u + ·)).prod) ∧
      ∀ (w : Pl E) (hw : w ∉ T) (ϖ : HeightOneSpectrum.adicCompletion E w) (hu : IsUnifV E w ϖ), ∀ j ≤ a,
        l (.inr ⟨⟨w, hw⟩, ⟨_, Tj_mem_hecke hu j⟩⟩) = satEig (qV E w) a (B w) j := by
  classical
  obtain ⟨m, hm⟩ := hC E a φ h0 fun t u => ⟨_, hl (.inl (t, u))⟩
  have hB : ∀ w : Pl E, ∃ B : Multiset ℂˣ, w ∉ T → IsSatVecGL w (fL a w) φ B := by
    intro w
    by_cases hw : w ∈ T
    · exact ⟨0, fun h => (h hw).elim⟩
    · obtain ⟨B, hB⟩ := hS E w a _ (fL a w) φ h0 (hfix w hw) fun h hh => ⟨_, hl (.inr ⟨⟨w, hw⟩, ⟨h, hh⟩⟩)⟩
      exact ⟨B, fun _ => hB⟩
  choose B hB using hB
  refine ⟨m, B, ⟨h0, haut, hm, ?_⟩, fun t u => ?_, fun w hw ϖ hu j hj => ?_⟩
  · exact hT.eventually_cofinite_notMem.mono hB
  · exact smul_left_injective ℂ h0 ((hl (.inl (t, u))).symm.trans ((hm t).2 u))
  · exact smul_left_injective ℂ h0
      ((hl (.inr ⟨⟨w, hw⟩, ⟨_, Tj_mem_hecke hu j⟩⟩)).symm.trans ((hB w hw).2.2.2 ϖ hu j hj))

theorem UpperTheory.V.Cj.S.pairEig :
    UpperTheory.V.Cj.S.TwoVar → UpperTheory.V.Cj.S.StabSp → UpperTheory.V.Cj.S.OpComm → UpperTheory.V.Cj.S.SatOfEig → UpperTheory.V.Cj.S.CapOfEig → UpperTheory.V.Cj.S.PairEig := by
  intro hTV hSt hOp hS hC E _ _ _ r s F S₁ S₂ b₁ b₂ hF h₁ h₂
  obtain ⟨T₁, hT₁, V₁, hS₁, fd₁, aut₁, fix₁, st₁⟩ := hSt E r S₁ b₁
  obtain ⟨T₂, hT₂, V₂, hS₂, fd₂, aut₂, fix₂, st₂⟩ := hSt E s S₂ b₂
  obtain ⟨φ₁, hφ₁, φ₂, hφ₂, l₁, l₂, n₁, n₂, e₁, e₂, H⟩ :=
    hTV _ _ (Sm E r) (Sm E s) V₁ V₂ fd₁ fd₂ (Ix r T₁) (Ix s T₂) opIx opIx st₁ st₂
      (fun i i' v hv => hOp E r T₁ i i' v fun w hw => fix₁ w hw hv)
      (fun i i' v hv => hOp E s T₂ i i' v fun w hw => fix₂ w hw hv) F hF
      (fun y => (h₁ y).imp fun f hf => ⟨hS₁ hf.1, hf.2⟩) (fun x => (h₂ x).imp fun f hf => ⟨hS₂ hf.1, hf.2⟩)
  obtain ⟨m₁, B₁, E₁, c₁, s₁⟩ := eig_of_joint hS hC hT₁ φ₁ n₁ (aut₁ _ hφ₁) (fun w hw => fix₁ w hw hφ₁) l₁ e₁
  obtain ⟨m₂, B₂, E₂, c₂, s₂⟩ := eig_of_joint hS hC hT₂ φ₂ n₂ (aut₂ _ hφ₂) (fun w hw => fix₂ w hw hφ₂) l₂ e₂
  refine ⟨φ₁, φ₂, m₁, m₂, B₁, B₂, E₁, E₂, fun t u v G e hG he => ?_, ?_⟩
  · have := H Unit (fun _ => 1) (fun _ => .inl (t, u)) (fun _ => .inl (t, v)) (fun _ => G) e (fun _ => hG)
      (fun x y => by simpa using he x y)
    rw [← c₁, ← c₂]
    simpa using this
  · filter_upwards [hT₁.eventually_cofinite_notMem, hT₂.eventually_cofinite_notMem] with w hw₁ hw₂ ϖ hu c G e hG he
    have := H (Fin (r + 1) × Fin (s + 1)) c (fun p => .inr ⟨⟨w, hw₁⟩, ⟨_, Tj_mem_hecke hu p.1⟩⟩)
      (fun p => .inr ⟨⟨w, hw₂⟩, ⟨_, Tj_mem_hecke hu p.2⟩⟩) G e hG he
    rw [← this]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [s₁ w hw₁ ϖ hu p.1 (Nat.lt_succ_iff.1 p.1.2), s₂ w hw₂ ϖ hu p.2 (Nat.lt_succ_iff.1 p.2.2)]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.MemFixed
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

private theorem mem_fixed' {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    {H : Subgroup G} {v : V} : v ∈ fixed ρ H ↔ ∀ k ∈ H, ρ k v = v := by
  change (∀ h : H, ρ (h : G) v = (((1 : H →* ℂˣ) h : ℂˣ) : ℂ) • v) ↔ _
  simp

private theorem blk_mul {r s : ℕ} {R : Type} [CommRing R] (a a' : GL (Fin r) R) (b b' : GL (Fin s) R) :
    blk (a * a') (b * b') = blk a b * blk a' b' := by
  simp only [blk, map_mul, mul_assoc]
  rw [← mul_assoc (emb (e2 r s) b), ← UpperTheory.V.Af.Fin.emb_comm, mul_assoc]

private theorem fL_apply {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ} (w : Pl E)
    (b : GL (Fin n) (w.adicCompletion E)) (φ : Sm E n) (x : GA E n) :
    (fL n w b φ).1 x = φ.1 (x * finGL E n (locGL E n w b)) := rfl

private theorem tOp_apply (hS : HkSum) {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ} (w : Pl E)
    {ϖ : w.adicCompletion E} (hϖ : ϖ ∈ Ov E w) (hu : IsUnifV E w ϖ) [Fintype (satakeRes (Ov E w) ⟨ϖ, hϖ⟩)] (j : ℕ)
    (hj : j ≤ n) (φ : Sm E n) (hφ : φ ∈ fixed (fL n w) (KGL w (n := n))) (x : GA E n) :
    (tOp n w hu j φ).1 x =
      ∑ i : SatakeIdx w hϖ (n := n) j, φ.1 (x * finGL E n (locGL E n w (satakeB w hϖ hu i))) := by
  have h := hS E w n (Sm E n) (fL n w) ϖ hϖ hu j hj φ hφ
  have h' : tOp n w hu j φ = ∑ i : SatakeIdx w hϖ (n := n) j, fL n w (satakeB w hϖ hu i) φ := h
  rw [h', Submodule.coe_sum, Finset.sum_apply]
  rfl

theorem UpperTheory.V.Cj.S.hkRel :
    UpperTheory.V.Cj.S.Slice → UpperTheory.V.Cj.S.HkSum → UpperTheory.V.Cj.S.HkLocal → UpperTheory.V.Cj.S.HeckeLocalBlock → UpperTheory.V.Cj.S.HkRel := by
  intro hSl hS hL hB E _ _ _ r s ψ hN w hψ ϖ hu j hj
  have hϖ : ϖ ∈ Ov E w := mem_Ov_of_isUnifV hu
  have := satake_res_finite w hϖ hu
  letI : Fintype (satakeRes (Ov E w) ⟨ϖ, hϖ⟩) := Fintype.ofFinite _
  obtain ⟨b1, b2, b3, b4⟩ := hB E w r s
  have hfix : ∀ k ∈ KGL w (n := (r + s)), ∀ g, ψ.1 (g * finGL E _ (locGL E _ w k)) = ψ.1 g := fun k hk g =>
    congrFun (congrArg Subtype.val (mem_fixed'.1 hψ k hk)) g
  have hs1 : ∀ y : GA E s, ∃ f : Sm E r, (∀ x, f.1 x = ψ.1 (blk x y)) ∧ f ∈ fixed (fL r w) (KGL w (n := r)) := fun y => by
    obtain ⟨f, hf, -⟩ := hSl E r (r + s) (e1 r s) (emb (e2 r s) y)
    have hf' : ∀ x, (f ψ).1 x = ψ.1 (blk x y) := fun x => by rw [hf, blk, UpperTheory.V.Af.Fin.emb_comm]
    refine ⟨f ψ, hf', mem_fixed'.2 fun k hk => Subtype.ext (funext fun x => ?_)⟩
    rw [fL_apply, hf', hf', ← hfix _ (b4 k hk 1 (one_mem _)) (blk x y), b1, ← blk_mul, map_one, map_one, mul_one]
  have hs2 : ∀ x : GA E r, ∃ f : Sm E s, (∀ y, f.1 y = ψ.1 (blk x y)) ∧ f ∈ fixed (fL s w) (KGL w (n := s)) := fun x => by
    obtain ⟨f, hf, -⟩ := hSl E s (r + s) (e2 r s) (emb (e1 r s) x)
    have hf' : ∀ y, (f ψ).1 y = ψ.1 (blk x y) := fun y => by rw [hf, blk]
    refine ⟨f ψ, hf', mem_fixed'.2 fun k hk => Subtype.ext (funext fun y => ?_)⟩
    rw [fL_apply, hf', hf', ← hfix _ (b4 1 (one_mem _) k hk) (blk x y), b1, ← blk_mul, map_one, map_one, mul_one]
  choose f2 hf2 hf2' using hs2
  refine ⟨fun p x y => ∑ i₁ : SatakeIdx w hϖ (n := r) p.1, ∑ i₂ : SatakeIdx w hϖ (n := s) p.2,
    ψ.1 (blk (x * finGL E r (locGL E r w (satakeB w hϖ hu i₁))) (y * finGL E s (locGL E s w (satakeB w hϖ hu i₂)))),
    fun p => ⟨fun x y => ∑ i₁ : SatakeIdx w hϖ (n := r) p.1,
      ψ.1 (blk (x * finGL E r (locGL E r w (satakeB w hϖ hu i₁))) y), fun y => ?_, fun x => ?_⟩, fun x y => ?_⟩
  · obtain ⟨f, hf, hf'⟩ := hs1 y
    refine ⟨f, funext hf, funext fun x => ?_⟩
    rw [tOp_apply hS w hϖ hu _ (Nat.lt_succ_iff.mp p.1.2) f hf']
    simp only [hf]
  · have hv : ∀ y, (∑ i₁ : SatakeIdx w hϖ (n := r) p.1,
        f2 (x * finGL E r (locGL E r w (satakeB w hϖ hu i₁)))).1 y = ∑ i₁ : SatakeIdx w hϖ (n := r) p.1,
        ψ.1 (blk (x * finGL E r (locGL E r w (satakeB w hϖ hu i₁))) y) := fun y => by
      rw [Submodule.coe_sum, Finset.sum_apply]
      simp only [hf2]
    refine ⟨_, funext hv, funext fun y => ?_⟩
    rw [tOp_apply hS w hϖ hu _ (Nat.lt_succ_iff.mp p.2.2) _ (Submodule.sum_mem _ fun i _ => hf2' _)]
    simp only [hv]
    exact Finset.sum_comm
  · rw [res, tOp_apply hS w hϖ hu j hj ψ hψ,
      hL E w r s ϖ hϖ hu j (fun g => ψ.1 (blk x y * finGL E _ (locGL E _ w g))) (fun X g => by
        obtain ⟨Y, hY⟩ := b2 X
        obtain ⟨Y', hY'⟩ := b3 x y Y
        simp only [map_mul]
        rw [hY, ← mul_assoc, hY', mul_assoc, hN])]
    simp only [b1, blk_mul]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HullBdd
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

private theorem hull_le {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
    {S U : Submodule ℂ (Sm E a)} (h : ∀ T ∈ Comm E a, ∀ φ ∈ S, T φ ∈ U) : hull S ≤ U := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨T, hT, φ, hφ, rfl⟩
  exact h T hT φ hφ

private theorem smEq_aeval {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
    (z : GroundTheory.Automorphic.AutomorphicForm.UEnv E a) (p : Polynomial ℂ) (φ : Sm E a) :
    Polynomial.aeval (GroundTheory.Automorphic.AutomorphicForm.uAction z) p (UpperTheory.V.Cm.smEq E a φ) =
      UpperTheory.V.Cm.smEq E a (Polynomial.aeval (UpperTheory.V.Cm.uTC E a z) p φ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add (f := _), LinearMap.add_apply, hp, hq]
  | monomial n c =>
    simp only [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, map_smul]
    congr 1
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih, UpperTheory.V.Cm.smEq_uTC]

private theorem commute_aeval {A : Type} [Ring A] [Algebra ℂ A] {T z : A} (h : Commute T z) (p : Polynomial ℂ) :
    Commute T (Polynomial.aeval z p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _)]; exact hp.add_right hq
  | monomial n c =>
    rw [Polynomial.aeval_monomial]
    exact (Algebra.commute_algebraMap_right c T).mul_right (h.pow_right n)

theorem UpperTheory.V.Cj.S.hullBdd :
    UpperTheory.V.Cj.S.TypesComm → UpperTheory.V.Cj.S.HullBdd := by
  intro hTC E _ _ _ a S hS L hL
  have haut : ∀ φ ∈ hull S, GroundTheory.Automorphic.AutomorphicForm.IsAutomorphicForm φ.1 := fun φ hφ =>
    (Cm.isAutForm_iff φ).1 (Cm.mem_range_ofAut.1 (hull_le (U := LinearMap.range (Cm.ofAut E a))
      (fun T hT ψ hψ => Cm.mem_range_ofAut.2 (hT.2.2 ψ ((Cm.isAutForm_iff ψ).2
        (UpperTheory.isAutomorphicForm_of_bdd_submodule E a _ hS _ ⟨ψ, hψ, rfl⟩)))) hφ))
  refine ⟨?_, ?_, ⟨L, hL, ?_⟩, ?_, fun z hz => ?_⟩
  · rintro _ ⟨φ, hφ, rfl⟩
    exact (haut φ hφ.1).isLeftInvariant
  · rintro _ ⟨φ, hφ, rfl⟩
    exact (haut φ hφ.1).hasModerateGrowth
  · rintro _ ⟨φ, hφ, rfl⟩ u hu g
    rw [Fb.finEmb_eq]
    have h1 : finRep E a u φ = φ := (hφ.2 ⟨u, hu⟩).trans (by simp)
    exact congrFun (congrArg Subtype.val h1) g
  · obtain ⟨V, hV, hst, hm⟩ := hS.types
    refine ⟨V, hV, hst, ?_⟩
    rintro _ ⟨φ, hφ, rfl⟩ g
    let U : Submodule ℂ (Sm E a) :=
      { carrier := {ψ | (fun k : archCompact E a => ψ.1 (g * infEmb E a k.1)) ∈ V}
        zero_mem' := V.zero_mem
        add_mem' := fun hx hy => V.add_mem hx hy
        smul_mem' := fun c _ hx => V.smul_mem c hx }
    exact hull_le (U := U) (fun T hT ψ hψ => hTC E a V hV T hT.1 ψ (hm _ ⟨ψ, hψ, rfl⟩) g) hφ.1
  · obtain ⟨p, hp, hm⟩ := hS.centre z hz
    refine ⟨p, hp, ?_⟩
    rintro _ ⟨φ, hφ, rfl⟩
    have h0 : φ ∈ LinearMap.ker (Polynomial.aeval (Cm.uTC E a z) p) := by
      refine hull_le (fun T hT ψ hψ => ?_) hφ.1
      have h1 := hm _ ⟨ψ, hψ, rfl⟩
      rw [Submodule.mem_bot, LinearEquiv.coe_coe, smEq_aeval] at h1
      have h1 : Polynomial.aeval (Cm.uTC E a z) p ψ = 0 :=
        (Cm.smEq E a).injective (h1.trans (Cm.smEq E a).map_zero.symm)
      rw [LinearMap.mem_ker, ← Module.End.mul_apply, ← (commute_aeval (hT.2.1 z hz) p).eq, Module.End.mul_apply, h1,
        map_zero]
    rw [Submodule.mem_bot, LinearEquiv.coe_coe, smEq_aeval, LinearMap.mem_ker.1 h0, (Cm.smEq E a).map_zero]
end

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.LFun Formalism.L2.Host
open GroundTheory.Automorphic.AutomorphicForm (constantTerm)

namespace UpperTheory.V.Cj.S

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

private theorem Supp.congr {a k : ℕ} {m m' : (E →+* ℂ) → Multiset ℂ} {B B' : Pl E → Multiset ℂˣ} (h : Supp E a k m B)
    (hm : ∀ t, m' t = m t) (hB : ∀ᶠ w in Filter.cofinite, B' w = B w) : Supp E a k m' B' := by
  obtain ⟨ι, _, n, π, μ, h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨ι, inferInstance, n, π, μ, h1, h2, h3, h4, fun t => (h5 t).trans (hm t).symm, ?_⟩
  filter_upwards [h6, hB] with w ⟨C, c1, c2⟩ e
  exact ⟨C, c1, c2.trans e.symm⟩

private theorem Supp.mono {a k l : ℕ} {m : (E →+* ℂ) → Multiset ℂ} {B : Pl E → Multiset ℂˣ} (h : Supp E a k m B)
    (hl : l ≤ k) : Supp E a l m B := by
  obtain ⟨ι, _, n, π, μ, h1, h2⟩ := h
  exact ⟨ι, inferInstance, n, π, μ, hl.trans h1, h2⟩

private theorem supp_two (hS : Step) (hT : SuppTwist) (hA : SuppAdd) {a : ℕ}
    (ih : ∀ b < a, 1 ≤ b → ∀ (φ : Sm E b) m B, Eig φ m B → Supp E b 1 m B)
    {φ : Sm E a} {m : (E →+* ℂ) → Multiset ℂ} {B : Pl E → Multiset ℂˣ} (h : Eig φ m B) (hc : ¬ IsCuspForm φ) :
    Supp E a 2 m B := by
  have h1 : ¬ GroundTheory.Automorphic.AutomorphicForm.IsCuspidal φ.1 := fun h2 =>
    hc ((Cm.isCuspForm_iff φ).2 ⟨(Cm.isAutForm_iff φ).1 h.aut, h2⟩)
  unfold GroundTheory.Automorphic.AutomorphicForm.IsCuspidal at h1
  push Not at h1
  obtain ⟨r, h0, hr, hg⟩ := h1
  obtain ⟨s, rfl⟩ : ∃ s, a = r + s := ⟨a - r, by omega⟩
  obtain ⟨φ₁, φ₂, m₁, m₂, B₁, B₂, e₁, e₂, hm, hB⟩ := hS E r s φ m B h hg
  have hν := fun x : ℝ => GlobalTheory.Mem.Chr.CharModel.absChar_isAbsPow (F := E) x
  exact (hA E r s 1 1 _ _ _ _ (hT E r 1 _ _ (ih r hr h0 _ _ _ e₁) _ _ (hν _))
    (hT E s 1 _ _ (ih s (by omega) (by omega) _ _ _ e₂) _ _ (hν _))).congr hm (hB _ _ (hν _) (hν _))

private theorem supp_one (hS : Step) (hT : SuppTwist) (hA : SuppAdd) (hC : SuppCusp) (a : ℕ) :
    1 ≤ a → ∀ (φ : Sm E a) m B, Eig φ m B → Supp E a 1 m B := by
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    intro ha φ m B h
    by_cases hc : IsCuspForm φ
    · exact hC E a ha φ m B h hc
    · exact (supp_two hS hT hA ih h hc).mono one_le_two

theorem cuspSupport_of (hS : Step) (hT : SuppTwist) (hA : SuppAdd) (hC : SuppCusp) (hP : CuspProj) (hτ : TauSat) :
    CuspSupport := by
  intro E _ _ _ a ha τ m j hj hfin haut hcap
  by_cases hc : ∀ v, IsCuspForm (j v)
  · left
    obtain ⟨v, hv⟩ : ∃ v, j v ≠ 0 := by
      by_contra h
      push Not at h
      exact hj (LinearMap.ext h)
    let j' : τ.V →ₗ[ℂ] CI a m := j.codRestrict _ fun v => mem_CI.2 ⟨hc v, fun t => (hcap v t).2⟩
    obtain ⟨π, h1, p, h2, h3⟩ := hP E a ha m (fun t => (hcap v t).1) (j' v) fun e => hv (congrArg Subtype.val e)
    exact ⟨π, ⟨p ∘ₗ j', fun e => h2 (LinearMap.congr_fun e v), fun g x => h3 g (j' x) (j' (τ.ρ g x)) (hfin g x)⟩, h1⟩
  · right
    push Not at hc
    obtain ⟨v, hv⟩ := hc
    have h0 : j v ≠ 0 := fun e => hv (e ▸ Cm.mem_range_ofCusp.1 (Submodule.zero_mem _))
    have hv0 : v ≠ 0 := fun e => h0 (by rw [e, map_zero])
    have h1 := hτ E a τ v hv0
    classical
    let B : Pl E → Multiset ℂˣ := fun w =>
      if h : ∃ B, HasSatGL w (locOf τ.ρ w) B ∧ IsSatVecGL w (locOf τ.ρ w) v B then h.choose else 0
    have h2 : ∀ᶠ w in Filter.cofinite, HasSatGL w (locOf τ.ρ w) (B w) ∧ IsSatVecGL w (locOf τ.ρ w) v (B w) :=
      h1.mono fun w h => by simp only [B, dif_pos h]; exact h.choose_spec
    have he : Eig (j v) m B :=
      ⟨h0, haut v, hcap v, h2.mono fun w h => h.2.map j (fun g y => hfin _ y) h0⟩
    obtain ⟨ι, _, n, π, μ, c1, c2, c3, c4, c5, c6⟩ :=
      supp_two hS hT hA (fun b _ => supp_one hS hT hA hC b) he hv
    refine ⟨ι, inferInstance, n, π, μ, c1, c2, fun i => ?_, c3, c4, c5, ?_⟩
    · obtain ⟨k, hk⟩ := Fintype.exists_ne_of_one_lt_card c1 i
      rw [← c3]
      exact Finset.single_lt_sum hk (Finset.mem_univ i) (Finset.mem_univ k) (c2 k) fun _ _ _ => Nat.zero_le _
    · filter_upwards [c6, h2] with w ⟨C, d1, d2⟩ h
      exact ⟨C, d1, d2 ▸ h.1⟩

theorem cuspSupport : CuspSupport :=
  cuspSupport_of
    (step (pairEig (twoVar tensEigB) (stabSp capAct levelSplit (hullBdd typesComm) (hullOps capAct)) (opComm capAct) satOfEig capOfEig) (sliceBdd singleBdd) (iwa (rtK capAct)) ctCap ctSat (capRel slice capBlock) (hkRel slice hkSum (hkLocal sumInner matBlock) gl2_local_to_adelic_embedding) capArith satArith)
    suppTwist suppAdd (suppCusp (cuspProj capAct (ciBasic capAct) (ciCompl (ciBasic capAct))))
    (cuspProj capAct (ciBasic capAct) (ciCompl (ciBasic capAct))) tauSat

end UpperTheory.V.Cj.S
