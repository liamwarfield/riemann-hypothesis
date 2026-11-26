module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HeckeLocalBlock
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommuteRtOfMemZalg
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalSatakeAlmostAll

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.CapAct
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

theorem UpperTheory.V.Cj.S.capAct :
    UpperTheory.V.Cj.S.CapAct := by
  intro E _ _ _ a t u
  have h0 : ∀ w : Cm.UC E a, Commute (cap (a := a) t u) (Cm.uC E a w) := fun w => by
    rw [← Cm.uC_capC]
    exact Commute.map (Subalgebra.mem_center_iff.1 (Cm.capC_mem_center t u) w).symm (Cm.uC E a)
  have h1 : ∀ g, Commute (cap (a := a) t u) (rt E a g) := fun g =>
    GlobalTheory.CompanionTheory.CTFin.Slice1.commute_rt_of_mem_Zalg (Cm.cap_mem_Zalg t u) g
  refine ⟨h1, fun o => ?_, fun z => ?_, fun t' u' => ?_⟩
  · cases o with
    | fin k => exact h1 _
    | cpt k => exact h1 _
    | lie X =>
      have := h0 (Cm.ιC E a X)
      rw [Cm.uC_ιC] at this
      exact this
  · have := h0 (1 ⊗ₜ z)
    rwa [Cm.uC_tmul, one_smul] at this
  · have := h0 (Cm.capC t' u')
    rwa [Cm.uC_capC] at this
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HkSum
noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host
open GlobalTheory.PRep (fixed)

namespace UpperTheory.V.Cj.S

theorem hkSum : HkSum := by
  intro E _ _ w n V _ _ ρ ϖ hϖ hu _ j hj x hx
  classical
  have hr := satake_range_eq (n := n) w hϖ hu Final.TjCosets hj
  unfold heckeVec
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.univ.image (fun i : SatakeIdx w hϖ (n := n) j =>
      ((satakeB w hϖ hu i : GL (Fin n) (w.adicCompletion E)) :
        GL (Fin n) (w.adicCompletion E) ⧸ KGL w (n := n)))) ?_]
  · rw [Finset.sum_image (fun i _ i' _ h => satakeB_inj w hϖ hu h)]
    refine Finset.sum_congr rfl fun i _ => ?_
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (KGL w (n := n)) (satakeB w hϖ hu i)
    have hfix : ρ (k : GL (Fin n) (w.adicCompletion E)) x = x := GlobalTheory.LGrp.mem_fixed.1 hx _ k.2
    rw [hk, satake_Tj_eq, Set.indicator_of_mem (satake_Tset_right w (satakeB_mem w hϖ hu i) k.2),
      Pi.one_apply, one_smul, map_mul, Module.End.mul_apply, hfix]
  · intro y hy
    have hT : Tj ℂ n (Ov E w) ϖ j y.out ≠ 0 := fun h0 => hy (by simp only [h0, zero_smul])
    have hy' : y ∈ Set.range _ := hr.ge ((satake_Tj_ne_zero_iff w ℂ ϖ j _).1 hT)
    obtain ⟨i, rfl⟩ := hy'
    exact Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_univ i))

end UpperTheory.V.Cj.S
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.Gl2LocalToAdelicEmbedding
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

section SlopeTestRemainingChoices

open UpperTheory.V.Af.Fin GroundTheory.Automorphic.AutomorphicForm

variable {R S : Type} [CommRing R] [CommRing S]

private theorem corner_sub_one {a : ℕ} (s : R →ₙ+* S) (g : GL (Fin a) R) (i j : Fin a) :
    ((cornerGL a s g).val - 1) i j = s ((g.val - 1) i j) := by
  change (1 : Matrix (Fin a) (Fin a) S) i j - s ((1 : Matrix (Fin a) (Fin a) R) i j) + s (g.val i j)
    - (1 : Matrix (Fin a) (Fin a) S) i j = s (g.val i j - (1 : Matrix (Fin a) (Fin a) R) i j)
  rw [map_sub]
  ring

private theorem corner_emb {a n : ℕ} (e : Fin a ↪ Fin n) (s : R →ₙ+* S) (g : GL (Fin a) R) :
    cornerGL n s (emb e g) = emb e (cornerGL a s g) := by
  refine Units.ext (sub_left_injective (b := (1 : Matrix (Fin n) (Fin n) S)) ?_)
  ext i j
  beta_reduce
  rw [corner_sub_one, coe_emb, coe_emb, add_sub_cancel_left, add_sub_cancel_left]
  by_cases hi : ∃ k, i = e k
  · obtain ⟨k, rfl⟩ := hi
    by_cases hj : ∃ l, j = e l
    · obtain ⟨l, rfl⟩ := hj
      rw [matrixExtendByZero_apply, matrixExtendByZero_apply, corner_sub_one]
    · push Not at hj
      rw [matrixExtendByZero_apply_of_outside_col e _ _ hj, matrixExtendByZero_apply_of_outside_col e _ _ hj, map_zero]
  · push Not at hi
    rw [extendByZero_apply_eq_zero_of_row_not_mem e _ hi, extendByZero_apply_eq_zero_of_row_not_mem e _ hi, map_zero]

private theorem corner_blk {r t : ℕ} (s : R →ₙ+* S) (g : GL (Fin r) R) (h : GL (Fin t) R) :
    cornerGL (r + t) s (blk g h) = blk (cornerGL r s g) (cornerGL t s h) := by
  rw [blk, blk, map_mul, corner_emb, corner_emb]

private theorem corner_unip {n r : ℕ} (s : R →ₙ+* S) (X : UPos n r → R) :
    cornerGL n s (unipGL X) = unipGL fun p => s (X p) := by
  refine Units.ext (sub_left_injective (b := (1 : Matrix (Fin n) (Fin n) S)) ?_)
  ext i j
  beta_reduce
  rw [corner_sub_one]
  change s ((1 + blockEntry X - 1) i j) = (1 + blockEntry (fun p => s (X p)) - 1) i j
  rw [add_sub_cancel_left, add_sub_cancel_left, blockEntry_apply, blockEntry_apply]
  split_ifs
  · rfl
  · exact map_zero s

private theorem emb_mem {L : Type} [Field L] (O : Subring L) {a n : ℕ} (e : Fin a ↪ Fin n) {k : GL (Fin a) L}
    (hk : k ∈ GLint (Fin a) O) : emb e k ∈ GLint (Fin n) O := by
  obtain ⟨k, rfl⟩ := hk
  exact ⟨emb e k, emb_map e O.subtype k⟩

end SlopeTestRemainingChoices

theorem UpperTheory.V.Cj.S.gl2_local_to_adelic_embedding :
    UpperTheory.V.Cj.S.HeckeLocalBlock := by
  intro E _ _ w r s
  refine ⟨fun b₁ b₂ => ?_, fun X => ?_, fun x y Y => ?_, fun k₁ h₁ k₂ h₂ => ?_⟩
  · simp only [finGL, locGL, corner_blk]
  · simp only [finGL, locGL, corner_unip]
    exact ⟨_, rfl⟩
  · obtain ⟨c, hc⟩ := UpperTheory.blockDiag_conj_unipotent_linear (Ad E) r s x y
    exact ⟨_, hc (Ad E) (RingHom.id _) Y⟩
  · exact mul_mem (emb_mem _ _ h₁) (emb_mem _ _ h₂)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.SatOfEig
noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep
open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun GlobalTheory.LGrp GlobalTheory.LFun.SatCompare GlobalTheory.LocGL GlobalTheory.WeylGL

namespace UpperTheory.V.Cj.S

theorem satOfEig : SatOfEig := by
  intro E _ _ w n V _ _ π x hx0 hx hsc
  have hK : IsCommensurated (KGL w (n := n)) := Final.GLintComm E w n
  obtain ⟨ϖ, hu⟩ := exists_isUnifV w
  have h0 := ne_zero_of_isUnifV hu
  choose c hc using fun j => hsc _ (Tj_mem_hecke (n := n) hu j)
  have c0 : c 0 = 1 := by
    have e : Tj ℂ n (Ov E w) ϖ 0 = dosetInd ℂ (KGL w (n := n)) 1 := by
      rw [Tj_eq h0]
      congr 1
    refine smul_left_injective ℂ hx0 ?_
    simp only [← hc 0, e, heckeVec_one hK hx, one_smul]
  have cn : c n ≠ 0 := by
    intro e
    have h1 := hc n
    have hTn : Tj ℂ n (Ov E w) ϖ n = dosetInd ℂ (KGL w (n := n)) (tor h0 fun _ => 1) := by
      rw [Tj_eq h0]; simp
    rw [e, zero_smul, hTn, heckeVec_dosetInd (R := {tor h0 fun _ => 1}) hx, Finset.sum_singleton] at h1
    · exact hx0 (by simpa [← Module.End.mul_apply, ← map_mul] using congrArg (π (tor h0 fun _ => 1)⁻¹) h1)
    · intro γ hγ
      exact mem_doset.2 ⟨1, one_mem _, 1, one_mem _, by simpa using hγ⟩
    · intro g hg
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_doset.1 hg
      refine ⟨_, ⟨Finset.mem_singleton_self _, ?_⟩, fun γ hγ => Finset.mem_singleton.1 hγ.1⟩
      rw [← tor_const_comm, mul_assoc, inv_mul_cancel_left]
      exact mul_mem ha hb
  obtain ⟨B, hB, hBc⟩ := GlobalTheory.T.exists_multiset_satakeEigenvalue_eq (qV E w) n (qV_ne_zero w) c c0 cn
  refine ⟨B, hx0, hx, hB, fun ϖ' hu' j hj => ?_⟩
  have hv : Valued.v (ϖ' / ϖ) = 1 := by
    rw [map_div₀, hu, hu', div_self WithZero.coe_ne_zero]
  have e := Final.TjIndep _ (Ov E w) ϖ (ϖ' / ϖ) ℂ n j hv.le
    (show Valued.v (ϖ' / ϖ)⁻¹ ≤ 1 by rw [map_inv₀, hv, inv_one]) (div_ne_zero (ne_zero_of_isUnifV hu') h0)
  rw [div_mul_cancel₀ _ h0] at e
  rw [e, hc j, hBc j hj]

end UpperTheory.V.Cj.S
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.CiBasic
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

attribute [local instance 100] LieRing.ofAssociativeRing in
private theorem one_mem_centerU (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) :
    UniversalEnvelopingAlgebra.ι ℝ (UpperTheory.V.Cm.lieEq E a (oneL E a)) ∈ (isExpLieAlgebra E a).centerU := by
  refine Subalgebra.mem_center_iff.2 fun u => ?_
  induction u using GroundTheory.Automorphic.AutomorphicForm.UEnv.induction with
  | halg r => exact Algebra.commutes r _
  | hι Y =>
    have h : ⁅Y, UpperTheory.V.Cm.lieEq E a (oneL E a)⁆ = 0 := by
      refine Subtype.ext ?_
      rw [LieSubalgebra.coe_bracket, UpperTheory.V.Cm.lieEq_oneL, Ring.lie_def, mul_one, one_mul, sub_self]
      rfl
    rw [← sub_eq_zero, ← Ring.lie_def, ← LieHom.map_lie, h, map_zero]
  | hmul x y hx hy => rw [mul_assoc, hy, ← mul_assoc, hx, mul_assoc]
  | hadd x y hx hy => rw [add_mul, mul_add, hx, hy]

private theorem scalar_of_mem_Zalg {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
    (m : (E →+* ℂ) → Multiset ℂ) {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) :
    ∃ c : ℂ, ∀ φ ∈ CI a m, z φ = c • φ := by
  induction hz using Algebra.adjoin_induction with
  | mem z hz =>
    obtain ⟨t, u, rfl⟩ := hz
    exact ⟨_, fun φ hφ => (mem_CI.1 hφ).2 t u⟩
  | algebraMap r => exact ⟨r, fun φ _ => rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc⟩ := hx
    obtain ⟨d, hd⟩ := hy
    exact ⟨c + d, fun φ hφ => by rw [LinearMap.add_apply, hc φ hφ, hd φ hφ, add_smul]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨c, hc⟩ := hx
    obtain ⟨d, hd⟩ := hy
    exact ⟨d * c, fun φ hφ => by rw [Module.End.mul_apply, hd φ hφ, map_smul, hc φ hφ, mul_smul]⟩

theorem UpperTheory.V.Cj.S.ciBasic :
    UpperTheory.V.Cj.S.CapAct → UpperTheory.V.Cj.S.CiBasic := by
  intro hc E _ _ _ a m
  refine ⟨fun o φ hφ => mem_CI.2 ⟨UpperTheory.V.Cm.isCuspForm_act o (mem_CI.1 hφ).1, fun t u => ?_⟩, ?_⟩
  · have h := LinearMap.congr_fun ((hc E a t u).2.1 o).eq φ
    rw [Module.End.mul_apply, Module.End.mul_apply, (mem_CI.1 hφ).2 t u, map_smul] at h
    exact h
  · rw [← UpperTheory.V.Cm.uTC_ι]
    exact scalar_of_mem_Zalg m (UpperTheory.V.Cm.uTC_mem_Zalg (one_mem_centerU E a))
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.SumInner
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

private theorem sum_three {A B C P R : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype P] [Fintype R]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq P]
    (f : A → P) (f' : B → P) (f'' : C → P) (h : Function.Bijective (Sum.elim (Sum.elim f f') f''))
    (g : (A → R) → (B → R) → ℂ) :
    ∑ c : P → R, g (c ∘ f) (c ∘ f') = (Fintype.card R : ℂ) ^ Fintype.card C * ∑ c₁, ∑ c₂, g c₁ c₂ := by
  let e : (P → R) ≃ ((A → R) × (B → R)) × (C → R) :=
    ((Equiv.ofBijective _ h).symm.arrowCongr (Equiv.refl R)).trans
      ((Equiv.sumArrowEquivProdArrow _ _ _).trans
        ((Equiv.sumArrowEquivProdArrow _ _ _).prodCongr (Equiv.refl _)))
  have h1 : ∑ c : P → R, g (c ∘ f) (c ∘ f') = ∑ x : ((A → R) × (B → R)) × (C → R), g x.1.1 x.1.2 :=
    Fintype.sum_equiv e _ _ (fun c => rfl)
  rw [h1, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, nsmul_eq_mul]
  rw [← Finset.mul_sum, Fintype.sum_prod_type]
  push_cast
  rfl

private def pair3 {r s : ℕ} (S : Finset (Fin (r + s))) (p : sub1 S × ((sub2 S)ᶜ : Finset (Fin s))) : satakePairs S :=
  ⟨(Fin.castAdd s p.1.1, Fin.natAdd r p.2.1), (Finset.mem_filter.1 p.1.2).2, by simpa [sub2] using p.2.2, by
    have := p.1.1.2
    simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]
    omega⟩

private theorem bij3 {r s : ℕ} (S : Finset (Fin (r + s))) :
    Function.Bijective (Sum.elim (Sum.elim (pair1 S) (pair2 S)) (pair3 S)) := by
  constructor
  · rintro ((⟨⟨a, b⟩, h⟩ | ⟨⟨a, b⟩, h⟩) | ⟨⟨a, h⟩, ⟨b, h'⟩⟩) ((⟨⟨c, d⟩, k⟩ | ⟨⟨c, d⟩, k⟩) | ⟨⟨c, k⟩, ⟨d, k'⟩⟩) H <;>
      simp only [Sum.elim_inl, Sum.elim_inr, pair1, pair2, pair3, Subtype.mk.injEq, Prod.mk.injEq, Fin.ext_iff,
        Fin.val_castAdd, Fin.val_natAdd, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at H ⊢ <;>
      omega
  · rintro ⟨⟨a, b⟩, h1, h2, h3⟩
    induction a using Fin.addCases with
    | left a =>
      induction b using Fin.addCases with
      | left b =>
        exact ⟨.inl (.inl ⟨(a, b), by simpa [sub1] using h1, by simpa [sub1] using h2, h3⟩), rfl⟩
      | right b =>
        exact ⟨.inr (⟨a, by simpa [sub1] using h1⟩, ⟨b, by simpa [sub2] using h2⟩), rfl⟩
    | right a =>
      induction b using Fin.addCases with
      | left b =>
        exfalso
        simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd] at h3
        omega
      | right b =>
        refine ⟨.inl (.inr ⟨(a, b), by simpa [sub2] using h1, by simpa [sub2] using h2, ?_⟩), rfl⟩
        simp only [Fin.lt_def, Fin.val_natAdd] at h3 ⊢
        omega

theorem UpperTheory.V.Cj.S.sumInner :
    UpperTheory.V.Cj.S.SumInner := by
  intro r s R _ S g
  rw [sum_three (pair1 S) (pair2 S) (pair3 S) (bij3 S) g]
  simp only [Fintype.card_prod, Fintype.card_coe, Finset.card_compl, Fintype.card_fin]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.CiCompl
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

section

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem stable_twist (χ : HChar E) {U : Submodule ℂ (Sm E a)} (h : _root_.GlobalTheory.CuspRep.IsStable U) :
    _root_.GlobalTheory.CuspRep.IsStable (U.map (mulChi a χ).toLinearMap) := by
  rintro o _ ⟨φ, hφ, rfl⟩
  exact ⟨_, add_mem (U.smul_mem _ (h o φ hφ)) (U.smul_mem _ hφ), (act_mulChi χ o φ).symm⟩

private theorem map_twist_inv (χ : HChar E) (U : Submodule ℂ (Sm E a)) :
    (U.map (mulChi a χ).toLinearMap).map (mulChi a χ⁻¹).toLinearMap = U := by
  rw [← Submodule.map_comp]
  have : (mulChi a χ⁻¹).toLinearMap ∘ₗ (mulChi a χ).toLinearMap = LinearMap.id := LinearMap.ext fun φ => by
    change mulChi a χ⁻¹ (mulChi a χ φ) = φ
    rw [← mulChi_mul, mul_inv_cancel, mulChi_one]
  rw [this, Submodule.map_id]

private theorem exists_twist (ha : 1 ≤ a) (c : ℂ) :
    ∃ χ : HChar E, dchi χ (Matrix.of (oneL E a)).trace = -c := by
  have hn : (Fintype.card (InfinitePlace E) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have ha' : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  refine ⟨Model.absC E (-c / (a * (2 * Fintype.card (InfinitePlace E)))), ?_⟩
  have e : (Matrix.of (oneL E a)).trace = a • (1 : Cinf E) := by
    change Matrix.trace (1 : Matrix (Fin a) (Fin a) (Cinf E)) = _
    simp
  rw [e, map_nsmul, GlobalTheory.GKCoh.Tests.dchi_absC_one, nsmul_eq_mul]
  push_cast
  field_simp

private theorem compl_zero {C : Submodule ℂ (Sm E a)} (hc : ∀ φ ∈ C, IsCuspForm φ)
    (h0 : ∀ φ ∈ C, lie E a (oneL E a) φ = 0) (hs : _root_.GlobalTheory.CuspRep.IsStable C) {U : Submodule ℂ (Sm E a)} (hU : U ≤ C)
    (hsU : _root_.GlobalTheory.CuspRep.IsStable U) : ∃ D ≤ C, _root_.GlobalTheory.CuspRep.IsStable D ∧ U ⊓ D = ⊥ ∧ U ⊔ D = C := by
  have hr : C ≤ LinearMap.range (UpperTheory.V.Cm.ofCusp E a) := fun φ h => UpperTheory.V.Cm.mem_range_ofCusp.2 (hc φ h)
  have hz : C.comap (UpperTheory.V.Cm.ofCusp E a) ≤ GroundTheory.Automorphic.AutomorphicForm.centralCuspForms E a :=
    fun ψ h => UpperTheory.V.Cm.mem_centralCuspForms_of (h0 _ h)
  have st := UpperTheory.V.Cm.stab_comap hsU
  obtain ⟨D, -, d2, d3, d4, d5, d6⟩ := GroundTheory.Automorphic.AutomorphicForm.exists_compl_centralCuspForms
    (U.comap (UpperTheory.V.Cm.ofCusp E a)) ((Submodule.comap_mono hU).trans hz) st.ρ st.σ st.τ
  have hUe : (U.comap (UpperTheory.V.Cm.ofCusp E a)).map (UpperTheory.V.Cm.ofCusp E a) = U :=
    Submodule.map_comap_eq_self (hU.trans hr)
  have hD : _root_.GlobalTheory.CuspRep.IsStable (D.map (UpperTheory.V.Cm.ofCusp E a)) := UpperTheory.V.Cm.isStable_map ⟨d2, d3, d4⟩
  refine ⟨D.map (UpperTheory.V.Cm.ofCusp E a) ⊓ C, inf_le_right, fun o φ h => ⟨hD o φ h.1, hs o φ h.2⟩, ?_, ?_⟩
  · rw [← inf_assoc, ← hUe, ← Submodule.map_inf _ UpperTheory.V.Cm.ofCusp_injective, d5, Submodule.map_bot, bot_inf_eq]
  · rw [← sup_inf_assoc_of_le _ hU, inf_eq_right, ← hUe, ← Submodule.map_sup, d6]
    exact (Submodule.map_comap_eq_self hr).ge.trans (Submodule.map_mono hz)

end

theorem UpperTheory.V.Cj.S.ciCompl :
    UpperTheory.V.Cj.S.CiBasic → UpperTheory.V.Cj.S.CiCompl := by
  intro hb E _ _ _ a ha m U hU hsU
  obtain ⟨hs, c, hc⟩ := hb E a m
  obtain ⟨χ, hχ⟩ := exists_twist (E := E) ha c
  obtain ⟨D, d1, d2, d3, d4⟩ := compl_zero (C := (CI a m).map (mulChi a χ).toLinearMap)
    (by rintro _ ⟨φ, h, rfl⟩; exact (mem_CI.1 h).1.mulChi χ)
    (by
      rintro _ ⟨φ, h, rfl⟩
      rw [LinearEquiv.coe_coe, lie_mulChi, hc φ h, hχ, neg_smul, add_neg_cancel, map_zero])
    (stable_twist χ hs) (Submodule.map_mono hU) (stable_twist χ hsU)
  refine ⟨D.map (mulChi a χ⁻¹).toLinearMap, (Submodule.map_mono d1).trans (map_twist_inv χ _).le,
    stable_twist _ d2, ?_, ?_⟩
  · rw [← map_twist_inv χ U, ← Submodule.map_inf _ (mulChi a χ⁻¹).injective, d3, Submodule.map_bot]
  · rw [← map_twist_inv χ U, ← Submodule.map_sup, d4, map_twist_inv]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.MatBlock
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

section SlopeTestRemainingChoices

open UpperTheory.V.Af.Fin GroundTheory.Automorphic.AutomorphicForm

private theorem cn_ne {r s : ℕ} (i : Fin r) (j : Fin s) : Fin.castAdd s i ≠ Fin.natAdd r j := fun h => by
  have := congrArg Fin.val h
  simp at this
  omega

private theorem block_embedding_first_val {R : Type} [CommRing R] {r s : ℕ} (m : GL (Fin r) R) :
    (emb (e1 r s) m).val = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks m.val 0 0 1) := by
  ext i j
  rw [coe_emb, Matrix.add_apply]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · have := matrixExtendByZero_apply (e1 r s) (m.val - 1) i j
    simp only [orderedCechToCatCochainsOne_apply_valueAtSubset] at this
    rw [this]
    simp [Matrix.one_apply]
  · rw [matrixExtendByZero_apply_of_outside_col _ _ _ fun k => (cn_ne k j).symm]
    simp [Matrix.one_apply_ne (cn_ne i j)]
  · rw [extendByZero_apply_eq_zero_of_row_not_mem _ _ fun k => (cn_ne k i).symm]
    simp [Matrix.one_apply_ne (cn_ne j i).symm]
  · rw [extendByZero_apply_eq_zero_of_row_not_mem _ _ fun k => (cn_ne k i).symm]
    simp [Matrix.one_apply]

private theorem block_embedding_second_val {R : Type} [CommRing R] {r s : ℕ} (m : GL (Fin s) R) :
    (emb (e2 r s) m).val = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 1 0 0 m.val) := by
  ext i j
  rw [coe_emb, Matrix.add_apply]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · rw [extendByZero_apply_eq_zero_of_row_not_mem _ _ fun k => (cn_ne i k)]
    simp [Matrix.one_apply]
  · rw [extendByZero_apply_eq_zero_of_row_not_mem _ _ fun k => (cn_ne i k)]
    simp [Matrix.one_apply_ne (cn_ne i j)]
  · rw [matrixExtendByZero_apply_of_outside_col _ _ _ fun k => (cn_ne j k)]
    simp [Matrix.one_apply_ne (cn_ne j i).symm]
  · have := matrixExtendByZero_apply (e2 r s) (m.val - 1) i j
    simp only [alternatingToOrderedCechDegreeTwo_apply_valueAtSubset] at this
    rw [this]
    simp [Matrix.one_apply]

private theorem unip_val {R : Type} [CommRing R] {r s : ℕ} (Y : Matrix (Fin r) (Fin s) R) :
    ∃ X : UPos (r + s) r → R,
      unipMatrix X = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 1 Y 0 1) := by
  refine ⟨fun p => Y ⟨p.1.1, p.2.1⟩ ⟨p.1.2 - r, by have := p.2.2; have := p.1.2.2; omega⟩, ?_⟩
  ext i j
  rw [unipMatrix, Matrix.add_apply, blockEntry_apply]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · simp [Matrix.one_apply]
  · simp [Matrix.one_apply_ne (cn_ne i j)]
  · simp [Matrix.one_apply_ne (cn_ne j i).symm]
  · simp [Matrix.one_apply]

private theorem block_form {R : Type} [CommRing R] {r s : ℕ} (b : GL (Fin (r + s)) R) (m₁ : GL (Fin r) R)
    (m₂ : GL (Fin s) R) (h₁ : ∀ i j, b.val (Fin.castAdd s i) (Fin.castAdd s j) = m₁.val i j)
    (h₂ : ∀ i j, b.val (Fin.natAdd r i) (Fin.natAdd r j) = m₂.val i j)
    (h₀ : ∀ i j, b.val (Fin.natAdd r i) (Fin.castAdd s j) = 0) :
    ∃ X : UPos (r + s) r → R, b = unipGL X * blk m₁ m₂ := by
  let B : Matrix (Fin r) (Fin s) R := b.val.submatrix (Fin.castAdd s) (Fin.natAdd r)
  have hb' : b.val = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks m₁.val B 0 m₂.val) := by
    ext i j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp [h₁]
    · simp [B]
    · simp [h₀]
    · simp [h₂]
  obtain ⟨X, hX⟩ := unip_val (B * (m₂⁻¹).val)
  refine ⟨X, Units.ext ?_⟩
  rw [blk, Units.val_mul, Units.val_mul, coe_unipGL, hX, block_embedding_first_val, block_embedding_second_val, hb']
  simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp [Matrix.mul_assoc]

end SlopeTestRemainingChoices

theorem UpperTheory.V.Cj.S.matBlock :
    UpperTheory.V.Cj.S.MatBlock := by
  intro L _ O r s π hπ S c
  refine block_form _ _ _ (fun i j => ?_) (fun i j => ?_) fun i j => ?_
  · have hm : ∀ k, k ∈ sub1 S ↔ Fin.castAdd s k ∈ S := fun k => by simp [sub1]
    have hN : satakeN O S c (Fin.castAdd s i) (Fin.castAdd s j) = satakeN O (sub1 S) (c ∘ pair1 S) i j := by
      unfold satakeN
      by_cases h : i ∈ sub1 S ∧ j ∉ sub1 S ∧ i < j
      · rw [dite_eq_left h, dite_eq_left ⟨(hm i).1 h.1, fun h' => h.2.1 ((hm j).2 h'), h.2.2⟩]
        rfl
      · rw [dite_eq_right h, dite_eq_right fun h' => h ⟨(hm i).2 h'.1, fun h'' => h'.2.1 ((hm j).1 h''), h'.2.2⟩]
    rw [satakeGL_apply, satakeGL_apply, hN]
    simp [Matrix.one_apply, hm]
  · have hm : ∀ k, k ∈ sub2 S ↔ Fin.natAdd r k ∈ S := fun k => by simp [sub2]
    have hN : satakeN O S c (Fin.natAdd r i) (Fin.natAdd r j) = satakeN O (sub2 S) (c ∘ pair2 S) i j := by
      unfold satakeN
      by_cases h : i ∈ sub2 S ∧ j ∉ sub2 S ∧ i < j
      · rw [dite_eq_left h, dite_eq_left ⟨(hm i).1 h.1, fun h' => h.2.1 ((hm j).2 h'), Nat.add_lt_add_left h.2.2 r⟩]
        rfl
      · rw [dite_eq_right h, dite_eq_right fun h' => h ⟨(hm i).2 h'.1, fun h'' => h'.2.1 ((hm j).1 h''),
          Nat.lt_of_add_lt_add_left h'.2.2⟩]
    rw [satakeGL_apply, satakeGL_apply, hN]
    simp [Matrix.one_apply, hm]
  · apply satakeGL_lower
    change (Fin.castAdd s j).val < (Fin.natAdd r i).val
    simp
    omega
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HkLocal
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

theorem UpperTheory.V.Cj.S.hkLocal :
    UpperTheory.V.Cj.S.SumInner → UpperTheory.V.Cj.S.MatBlock → UpperTheory.V.Cj.S.HkLocal := by
  intro hSum hMat E _ _ w r s ϖ hϖ hu _ j Φ hΦ
  have hπ0 : ((⟨ϖ, hϖ⟩ : Ov E w) : HeightOneSpectrum.adicCompletion E w) ≠ 0 := by
    intro h0
    have h1 : Valued.v ϖ = 0 := by
      have h2 : ϖ = 0 := h0
      rw [h2, map_zero]
    rw [hu] at h1
    exact WithZero.coe_ne_zero h1
  have hq : Fintype.card (satakeRes (Ov E w) ⟨ϖ, hϖ⟩) = qV E w := by
    have key : ∀ z : WithZero (Multiplicative ℤ), z < 1 → z ≤ ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
      intro z hz
      induction z using WithZero.recZeroCoe with
      | zero => exact zero_le'
      | coe a =>
        rw [← WithZero.coe_one, WithZero.coe_lt_coe] at hz
        rw [WithZero.coe_le_coe]
        have h1 : (Multiplicative.toAdd a : ℤ) < 0 := hz
        change (Multiplicative.toAdd a : ℤ) ≤ -1
        omega
    have hlt : ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) < 1 := by
      rw [← WithZero.coe_one, WithZero.coe_lt_coe]
      change (-1 : ℤ) < 0
      omega
    have hint := Valuation.valuationSubring.integers
      (Valued.v : Valuation (HeightOneSpectrum.adicCompletion E w) (WithZero (Multiplicative ℤ)))
    have hmax : Ideal.span {(⟨ϖ, hϖ⟩ : HeightOneSpectrum.adicCompletionIntegers E w)} =
        IsLocalRing.maximalIdeal (HeightOneSpectrum.adicCompletionIntegers E w) := by
      ext x
      rw [Ideal.mem_span_singleton]
      constructor
      · intro h
        have h2 := hint.le_of_dvd h
        exact (Valuation.mem_maximalIdeal_iff (v := Valued.v)).2 (lt_of_le_of_lt (h2.trans_eq hu) hlt)
      · intro h
        have h2 := (Valuation.mem_maximalIdeal_iff (v := Valued.v)).1 h
        exact hint.dvd_of_le ((key _ h2).trans_eq hu.symm)
    rw [Fintype.card_eq_nat_card, ← tjcosets_card_residue w]
    show Nat.card (↥(HeightOneSpectrum.adicCompletionIntegers E w) ⧸
      Ideal.span {(⟨ϖ, hϖ⟩ : HeightOneSpectrum.adicCompletionIntegers E w)}) = _
    rw [hmax]
    rfl
  obtain ⟨T, hT⟩ : ∃ T : Finset (Fin r) → Finset (Fin s) → ℂ, ∀ A B, T A B =
      ∑ c₁ : satakePairs A → satakeRes (Ov E w) ⟨ϖ, hϖ⟩, ∑ c₂ : satakePairs B → satakeRes (Ov E w) ⟨ϖ, hϖ⟩,
        Φ (blk (satakeGL (Ov E w) hπ0 A (fun p => satakeSec (Ov E w) ⟨ϖ, hϖ⟩ (c₁ p)))
          (satakeGL (Ov E w) hπ0 B (fun p => satakeSec (Ov E w) ⟨ϖ, hϖ⟩ (c₂ p)))) :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨κ, hκ⟩ : ∃ κ : Finset (Fin r) × Finset (Fin s) → Fin (r + 1) × Fin (s + 1),
      ∀ AB, κ AB = (⟨AB.1.card, Nat.lt_succ_of_le (by simpa using Finset.card_le_univ AB.1)⟩,
        ⟨AB.2.card, Nat.lt_succ_of_le (by simpa using Finset.card_le_univ AB.2)⟩) :=
    ⟨_, fun _ => rfl⟩
  have hS : ∀ S : Finset (Fin (r + s)),
      ∑ c : satakePairs S → satakeRes (Ov E w) ⟨ϖ, hϖ⟩,
        Φ (satakeGL (Ov E w) hπ0 S (fun p => satakeSec (Ov E w) ⟨ϖ, hϖ⟩ (c p))) =
      (qV E w : ℂ) ^ ((sub1 S).card * (s - (sub2 S).card)) * T (sub1 S) (sub2 S) := by
    intro S
    rw [hT]
    have h := hSum r s (satakeRes (Ov E w) ⟨ϖ, hϖ⟩) S (fun c₁ c₂ =>
      Φ (blk (satakeGL (Ov E w) hπ0 (sub1 S) (fun p => satakeSec (Ov E w) ⟨ϖ, hϖ⟩ (c₁ p)))
        (satakeGL (Ov E w) hπ0 (sub2 S) (fun p => satakeSec (Ov E w) ⟨ϖ, hϖ⟩ (c₂ p)))))
    rw [hq] at h
    rw [← h]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    obtain ⟨X, hX⟩ := hMat _ (Ov E w) r s _ hπ0 S (fun p => satakeSec (Ov E w) ⟨ϖ, hϖ⟩ (c p))
    rw [hX, hΦ]
    rfl
  have hcard : ∀ S : Finset (Fin (r + s)), S.card = (sub1 S).card + (sub2 S).card := by
    intro S
    calc S.card = ∑ i : Fin (r + s), if i ∈ S then 1 else 0 := by simp [Finset.sum_boole]
      _ = _ := Fin.sum_univ_add _
      _ = _ := by simp [sub1, sub2, Finset.sum_boole]
  let e : Finset (Fin (r + s)) ≃ Finset (Fin r) × Finset (Fin s) :=
    { toFun := fun S => (sub1 S, sub2 S)
      invFun := fun AB => AB.1.map (Fin.castAddEmb s) ∪ AB.2.map (Fin.natAddEmb r)
      left_inv := by
        intro S
        ext x
        refine Fin.addCases (fun i => ?_) (fun i => ?_) x <;> simp [sub1, sub2] <;>
          intro y hy h <;> rw [← h] <;> exact hy
      right_inv := by
        rintro ⟨A, B⟩
        ext i <;> simp [sub1, sub2] <;> intro y _ h <;> exfalso <;> rw [Fin.ext_iff] at h <;>
          simp at h <;> have := i.isLt <;> have := y.isLt <;> omega }
  have hsubj : ∀ F : Finset (Fin (r + s)) → ℂ,
      ∑ S : {S : Finset (Fin (r + s)) // S.card = j}, F S.1 =
        ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin (r + s)) => S.card = j), F S :=
    fun F => (Finset.sum_subtype _ (fun S => by simp) F).symm
  have hG : ∑ i : SatakeIdx (n := r + s) w hϖ j, Φ (satakeB w hϖ hu i) =
      ∑ AB, coef (qV E w) r s j (κ AB) * T AB.1 AB.2 := by
    calc ∑ i : SatakeIdx (n := r + s) w hϖ j, Φ (satakeB w hϖ hu i)
        = ∑ S : {S : Finset (Fin (r + s)) // S.card = j},
            ∑ c : satakePairs S.1 → satakeRes (Ov E w) ⟨ϖ, hϖ⟩,
              Φ (satakeGL (Ov E w) hπ0 S.1 (fun p => satakeSec (Ov E w) ⟨ϖ, hϖ⟩ (c p))) :=
          Fintype.sum_sigma (fun i => Φ (satakeB w hϖ hu i))
      _ = ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin (r + s)) => S.card = j),
            ∑ c : satakePairs S → satakeRes (Ov E w) ⟨ϖ, hϖ⟩,
              Φ (satakeGL (Ov E w) hπ0 S (fun p => satakeSec (Ov E w) ⟨ϖ, hϖ⟩ (c p))) :=
          hsubj (fun S => ∑ c : satakePairs S → satakeRes (Ov E w) ⟨ϖ, hϖ⟩,
              Φ (satakeGL (Ov E w) hπ0 S (fun p => satakeSec (Ov E w) ⟨ϖ, hϖ⟩ (c p))))
      _ = ∑ S : Finset (Fin (r + s)), if S.card = j then
            (qV E w : ℂ) ^ ((sub1 S).card * (s - (sub2 S).card)) * T (sub1 S) (sub2 S) else 0 := by
          rw [Finset.sum_filter]
          simp only [hS]
      _ = ∑ S, coef (qV E w) r s j (κ (e S)) * T (e S).1 (e S).2 := by
          refine Finset.sum_congr rfl (fun S _ => ?_)
          simp only [e, Equiv.coe_fn_mk, hκ, coef, hcard S]
          split_ifs <;> simp
      _ = ∑ AB, coef (qV E w) r s j (κ AB) * T AB.1 AB.2 :=
          Fintype.sum_equiv e _ _ (fun _ => rfl)
  have hR : ∀ a b : ℕ, ∑ i₁ : SatakeIdx (n := r) w hϖ a, ∑ i₂ : SatakeIdx (n := s) w hϖ b,
      Φ (blk (satakeB w hϖ hu i₁) (satakeB w hϖ hu i₂)) =
      ∑ AB ∈ (Finset.univ.filter (fun A : Finset (Fin r) => A.card = a)) ×ˢ
        (Finset.univ.filter (fun B : Finset (Fin s) => B.card = b)), T AB.1 AB.2 := by
    intro a b
    rw [Finset.sum_product]
    calc _ = ∑ A : {A : Finset (Fin r) // A.card = a}, ∑ c₁ : satakePairs A.1 → satakeRes (Ov E w) ⟨ϖ, hϖ⟩,
            ∑ i₂ : SatakeIdx (n := s) w hϖ b,
              Φ (blk (satakeGL (Ov E w) hπ0 A.1 (fun p => satakeSec (Ov E w) ⟨ϖ, hϖ⟩ (c₁ p)))
                (satakeB w hϖ hu i₂)) :=
          Fintype.sum_sigma (fun i₁ => ∑ i₂ : SatakeIdx (n := s) w hϖ b,
            Φ (blk (satakeB w hϖ hu i₁) (satakeB w hϖ hu i₂)))
      _ = ∑ A : {A : Finset (Fin r) // A.card = a}, ∑ B : {B : Finset (Fin s) // B.card = b}, T A.1 B.1 := by
          refine Finset.sum_congr rfl (fun A _ => ?_)
          simp only [hT]
          refine (Finset.sum_congr rfl (fun c₁ _ => Fintype.sum_sigma _)).trans ?_
          exact Finset.sum_comm
      _ = _ := by
          rw [← Finset.sum_subtype (Finset.univ.filter (fun A : Finset (Fin r) => A.card = a)) (by simp)
            (fun A => ∑ B : {B : Finset (Fin s) // B.card = b}, T A B.1)]
          refine Finset.sum_congr rfl (fun A _ => ?_)
          exact (Finset.sum_subtype _ (by simp) _).symm
  rw [hG]
  simp only [hR]
  rw [← Finset.sum_fiberwise Finset.univ κ]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Finset.mul_sum]
  have hfib : Finset.univ.filter (fun AB => κ AB = p) =
      (Finset.univ.filter (fun A : Finset (Fin r) => A.card = (p.1 : ℕ))) ×ˢ
        (Finset.univ.filter (fun B : Finset (Fin s) => B.card = (p.2 : ℕ))) := by
    ext ⟨A, B⟩
    simp [hκ, Prod.ext_iff, Fin.ext_iff]
  rw [hfib]
  refine Finset.sum_congr rfl (fun AB hAB => ?_)
  have hp : κ AB = p := by
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hAB
    rw [hκ]
    ext <;> simp [hAB]
  rw [hp]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.Imports
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

theorem UpperTheory.V.Cj.S.iwa :
    UpperTheory.V.Cj.S.RtK → UpperTheory.V.Cj.S.Iwa := by
  intro hK E _ _ _ r s φ m B hφ ⟨g, hg⟩
  obtain ⟨b, hb, k, hk, rfl⟩ := GroundTheory.Automorphic.Reduction.exists_adelicBorel_mul_maxCompact (K := E) (n := r + s) g
  obtain ⟨X, m₁, m₂, rfl⟩ := UpperTheory.upperTriangular_eq_unipotent_mul_levi _ r s b (GroundTheory.Automorphic.Reduction.mem_adelicBorel.1 hb)
  refine ⟨_, hK E (r + s) φ m B hφ k hk, m₁, m₂, ?_⟩
  have hl : GroundTheory.Automorphic.AutomorphicForm.IsLeftInvariant φ.1 := hφ.aut.left
  rw [mul_assoc, UpperTheory.constantTerm_unipotent_left_invariant E (r + s) r φ.1 hl] at hg
  rw [← GroundTheory.Automorphic.AutomorphicForm.constantTerm_rightTranslate] at hg
  exact hg
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.CtCap
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

theorem UpperTheory.V.Cj.S.ctCap :
    UpperTheory.V.Cj.S.CtCap := by
  intro E _ _ _ n r φ hφ
  have ha := (UpperTheory.V.Cm.isAutForm_iff φ).1 hφ
  obtain ⟨f, hf, hfu⟩ := UpperTheory.exists_constantTerm_linearMap_equivariant_universalEnveloping E n r
  let φ' : GroundTheory.Automorphic.AutomorphicForm.automorphicForms E n := ⟨φ.1, ha⟩
  refine ⟨(UpperTheory.V.Cm.smEq E n).symm (f φ'), hf φ', fun X g => ?_, fun t u => ?_⟩
  · rw [UpperTheory.V.Cm.coe_smEq_symm, hf]
    exact UpperTheory.constantTerm_unipotent_left_invariant E n r φ.1 ha.isLeftInvariant X g
  · obtain ⟨p, -, q, -, e⟩ := UpperTheory.V.Cm.mem_Zalg_iff.1 (UpperTheory.V.Cm.cap_mem_Zalg (a := n) t u)
    have h := hf (GroundTheory.Automorphic.AutomorphicForm.uActionAF E n p φ' +
      Complex.I • GroundTheory.Automorphic.AutomorphicForm.uActionAF E n q φ')
    rw [map_add (f := _), map_smul, hfu, hfu] at h
    rw [e]
    exact h
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.LevelSplit
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

theorem UpperTheory.V.Cj.S.levelSplit :
    UpperTheory.V.Cj.S.LevelSplit := by
  intro E _ _ a L hL
  have ho : IsOpen ((L ⊓ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E a : Subgroup (GL (Fin a) (Af E))) :
      Set (GL (Fin a) (Af E))) := hL.inter (GroundTheory.Automorphic.AdelicGLn.isOpen_integralFiniteGL E a)
  have hev := LocSph.eventually_mem (ho.mem_nhds (one_mem _))
  refine ⟨_, ho, inf_le_left, _, Filter.eventually_cofinite.1 hev, fun w hw => ?_⟩
  have hw' := not_not.1 hw
  have h1 : ∀ k ∈ KGL w (n := a), locGL E a w k ∈ L ⊓ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E a := by
    rintro _ ⟨g, rfl⟩
    exact hw' g
  refine ⟨h1, fun u hu => ?_⟩
  have hk : GeneralLinearGroup.map (pLoc E w) u ∈ KGL w (n := a) := by
    obtain ⟨h2, h3⟩ := (GroundTheory.Automorphic.AdelicGLn.mem_integralFiniteGL_iff E a).1 hu.2
    refine GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩
    · exact h2 i j w
    · rw [← map_inv]
      exact h3 i j w
  exact ⟨_, hk, _, mul_mem (inv_mem (h1 _ hk)) hu, LocEx.map_pLoc_inv_mul w u, (mul_inv_cancel_left _ _).symm⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.OpComm
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

private theorem hk_comm_of {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    {K : Subgroup G} (hK : IsCommensurated K) {h : G → ℂ} (hh : h ∈ Hecke ℂ K) (A : Module.End ℂ V)
    (hA : ∀ g, Commute A (ρ g)) (x : V) : A (hkOp ρ hK hh x) = hkOp ρ hK hh (A x) :=
  map_heckeVec hK hh (ρ' := ρ) A (fun g y => LinearMap.congr_fun (hA g).eq y) x

theorem UpperTheory.V.Cj.S.opComm :
    UpperTheory.V.Cj.S.CapAct → UpperTheory.V.Cj.S.OpComm := by
  intro hC E _ _ _ a T i i' φ hφ
  rcases i with ⟨t, u⟩ | ⟨⟨w, hw⟩, h, hh⟩ <;> rcases i' with ⟨t', u'⟩ | ⟨⟨w', hw'⟩, h', hh'⟩
  · exact LinearMap.congr_fun ((hC E a t u).2.2.2 t' u').eq φ
  · exact hk_comm_of (fL a w') (Final.GLintComm E w' a) hh' (cap t u) (fun g => (hC E a t u).1 _) φ
  · exact (hk_comm_of (fL a w) (Final.GLintComm E w a) hh (cap t' u') (fun g => (hC E a t' u').1 _) φ).symm
  · by_cases e : w = w'
    · subst e
      have hK := Final.GLintComm E w a
      change heckeVec (fL a w) (KGL w (n := a)) h (heckeVec (fL a w) (KGL w (n := a)) h' φ) =
        heckeVec (fL a w) (KGL w (n := a)) h' (heckeVec (fL a w) (KGL w (n := a)) h φ)
      rw [← SatCompare.heckeVec_conv hK hh hh' (hφ w hw), ← SatCompare.heckeVec_conv hK hh' hh (hφ w hw),
        Final.HeckeCommGL E w a ℂ h hh h' hh']
    · refine hk_comm_of (fL a w') (Final.GLintComm E w' a) hh' (hkOp (fL a w) (Final.GLintComm E w a) hh)
        (fun g => LinearMap.ext fun y => ?_) φ
      refine (hk_comm_of (fL a w) (Final.GLintComm E w a) hh (fL a w' g) (fun k => ?_) y).symm
      exact Commute.map (LocUniq.comm_locGL w (pLoc_locGL_of_ne e g) k) (finRep E a)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.LieEqLam
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

open UpperTheory.V UpperTheory.V.Af.Fin in
private theorem lie_eq_lam {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (i j : Fin a) (x : Cinf E)
    (φ : Sm E a) :
    Cm.smEq E a (lie E a (toL (Matrix.single i j x)) φ) =
      lam E a (Matrix.single i j (Cm.mixEq E x)) (Cm.smEq E a φ) := by
  rw [← Cm.uAction_ι_smEq, lam_apply]
  congr 3
  refine Subtype.ext (Matrix.ext fun k l => ?_)
  change Cm.mixEq E (Matrix.single i j x k l) = Matrix.single i j (Cm.mixEq E x) k l
  simp only [Matrix.single_apply, apply_ite (Cm.mixEq E), map_zero]

open UpperTheory.V UpperTheory.V.Af.Fin in
theorem UpperTheory.V.Cj.S.slice :
    UpperTheory.V.Cj.S.Slice := by
  intro E _ _ _ a n e g
  obtain ⟨f, hf, hl⟩ := UpperTheory.exists_restriction_blockEmbedding_intertwines_lie E a n e g
  have key : ∀ i j x ψ, (Cm.smEq E a).symm (f (Cm.smEq E n (lie E n (toL (Matrix.single (e i) (e j) x)) ψ))) =
      lie E a (toL (Matrix.single i j x)) ((Cm.smEq E a).symm (f (Cm.smEq E n ψ))) := fun i j x ψ => by
    rw [LinearEquiv.symm_apply_eq, lie_eq_lam, lie_eq_lam, LinearEquiv.apply_symm_apply, ← matrixExtendByZero_single, hl]
  refine ⟨(Cm.smEq E a).symm.toLinearMap ∘ₗ f ∘ₗ (Cm.smEq E n).toLinearMap, fun ψ x => hf _ x, fun t i j ψ => ?_⟩
  rw [← Cm.uC_genC, ← Cm.uC_genC]
  simp only [Cm.genC, AlgRepEndIrreducible.eL, map_smul, map_sub, Cm.uC_ιC, LinearMap.smul_apply, LinearMap.sub_apply]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, key]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.SuppAdd
namespace UpperTheory.V.Cj.S

theorem suppAdd : SuppAdd := by
  intro E _ _ _ r s k l m₁ m₂ B₁ B₂ h₁ h₂
  obtain ⟨ι, _, n, π, μ, hk, hn, hs, hi, hm, hB⟩ := h₁
  obtain ⟨κ, _, n', π', μ', hk', hn', hs', hi', hm', hB'⟩ := h₂
  refine ⟨ι ⊕ κ, inferInstance, Sum.elim n n', fun i => Sum.rec (fun i => π i) (fun i => π' i) i, Sum.elim μ μ',
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Fintype.card_sum]
    exact Nat.add_le_add hk hk'
  · rintro (i | i)
    · exact hn i
    · exact hn' i
  · rw [Fintype.sum_sum_type, ← hs, ← hs']
    rfl
  · rintro (i | i) t
    · exact hi i t
    · exact hi' i t
  · intro t
    rw [Fintype.sum_sum_type]
    show ∑ i, μ i t + ∑ i, μ' i t = m₁ t + m₂ t
    rw [hm t, hm' t]
  · filter_upwards [hB, hB'] with w hw hw'
    obtain ⟨C, hC, hCs⟩ := hw
    obtain ⟨C', hC', hCs'⟩ := hw'
    refine ⟨Sum.elim C C', ?_, ?_⟩
    · rintro (i | i)
      · exact hC i
      · exact hC' i
    · rw [Fintype.sum_sum_type]
      show ∑ i, C i + ∑ i, C' i = B₁ w + B₂ w
      rw [hCs, hCs']

end UpperTheory.V.Cj.S
end
