module

public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsAbelianTorusGeneratorsAtPlace

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AbelianPartCokernelLengthLe
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.RangeIdempotentRankSumEigenspaceDim
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.RangeIdempotentRankSumEigenspaceDim
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem finrank_iSup_indep {K V I : Type} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]
    [Fintype I] (S : I → Submodule K V) (hi : iSupIndep S) :
    Module.finrank K ↥(⨆ i, S i) = ∑ i, Module.finrank K (S i) := by
  classical
  rw [Submodule.iSup_eq_range_dfinsupp_lsum, LinearMap.finrank_range_of_inj hi.dfinsupp_lsum_injective]
  exact Module.finrank_directSum (R := K) (fun i => S i)

private theorem range_idem {O : Type} [CommRing O] [IsLocalRing O] {g : ℕ} (P : Matrix (Fin g) (Fin g) O)
    (h : P * P = P) : ∃ r : ℕ, Matrix.trace P = (r : O) ∧ Module.finrank O (LinearMap.range (Matrix.mulVecLin P)) = r ∧
      Nonempty (LinearMap.range (Matrix.mulVecLin P) ≃ₗ[O] (Fin r → O)) := by
  have hf : IsIdempotentElem (Matrix.mulVecLin P) := by
    show Matrix.mulVecLin P ∘ₗ Matrix.mulVecLin P = _
    rw [← Matrix.mulVecLin_mul, h]
  have hp := LinearMap.IsIdempotentElem.isProj_range _ hf
  haveI : Module.Projective O (LinearMap.range (Matrix.mulVecLin P)) :=
    Module.Projective.of_split (LinearMap.range (Matrix.mulVecLin P)).subtype hp.codRestrict (by
      ext x : 1
      exact hp.codRestrict_apply_cod x)
  haveI : Module.Free O (LinearMap.range (Matrix.mulVecLin P)) := Module.free_of_flat_of_isLocalRing
  haveI : Module.Projective O (LinearMap.ker (Matrix.mulVecLin P)) := by
    have hq := LinearMap.IsIdempotentElem.isProj_range _ hf.one_sub
    have : LinearMap.range (1 - Matrix.mulVecLin P) = LinearMap.ker (Matrix.mulVecLin P) :=
      (LinearMap.IsIdempotentElem.ker_eq_range_one_sub hf).symm
    rw [this] at hq
    exact Module.Projective.of_split (LinearMap.ker (Matrix.mulVecLin P)).subtype hq.codRestrict (by
      ext x : 1
      exact hq.codRestrict_apply_cod x)
  haveI : Module.Finite O (LinearMap.ker (Matrix.mulVecLin P)) := by
    rw [LinearMap.IsIdempotentElem.ker_eq_range_one_sub hf]
    infer_instance
  haveI : Module.Free O (LinearMap.ker (Matrix.mulVecLin P)) := Module.free_of_flat_of_isLocalRing
  refine ⟨_, ?_, rfl, ⟨(Module.finBasis O _).equivFun⟩⟩
  rw [← hp.trace, ← Matrix.toLin'_apply', Matrix.trace_toLin'_eq]

theorem range_idempotent_equiv_sum_eigDim : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] [StarRing OE] (g : ℕ) (ρ : (ℤ_[p] ⊗[ℤ] OE) →+* Matrix (Fin g) (Fin g) O) (e : ℤ_[p] ⊗[ℤ] OE), e * e = e → ∀ (n : ℕ) (t : Fin n ≃ Emb (O := O) e), Nonempty (LinearMap.range (Matrix.mulVecLin (ρ e)) ≃ₗ[O] (Fin (∑ j, eigDim C (fun a : OE => ρ (1 ⊗ₜ[ℤ] a)) ((algebraMap O C).comp ((t j : Emb (O := O) e) : OE →+* O))) → O)) := by
  intro p _ C _ _ _ v O _ _ hv _ _ _ OE _ _ _ _ _ _ g ρ e he n t
  haveI : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  have hP : ρ e * ρ e = ρ e := by rw [← map_mul, he]
  obtain ⟨r, htr, -, hne⟩ := range_idem (ρ e) hP
  have hPC : (ρ e).map (algebraMap O C) * (ρ e).map (algebraMap O C) = (ρ e).map (algebraMap O C) := by
    rw [← Matrix.map_mul, hP]
  obtain ⟨r', htr', hrk, -⟩ := range_idem _ hPC
  have hrr : r = r' := by
    have : ((r : ℕ) : C) = r' := by
      rw [← htr', ← AddMonoidHom.map_trace (algebraMap O C) (ρ e), htr]
      simp
    exact_mod_cast this
  let σ : (ℤ_[p] ⊗[ℤ] OE) →+* Module.End C (Fin g → C) :=
    (Matrix.toLinAlgEquiv' (R := C) (n := Fin g)).toRingEquiv.toRingHom.comp
      ((algebraMap O C).mapMatrix.comp ρ)
  have hσ : ∀ x, σ x = Matrix.toLin' ((ρ x).map (algebraMap O C)) := fun x => rfl
  let ρE : OE →+* Module.End C (Fin g → C) :=
    σ.comp (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℤ_[p]) (B := OE)).toRingHom
  obtain ⟨-, hd⟩ := GlobalTheory.order_rep_diagonalisable C OE
  obtain ⟨hind, htop⟩ := hd (Fin g → C) ρE
  obtain ⟨hex, h01, -⟩ := GlobalTheory.ChF.embeddings_idempotents_conjugation p C v O hv OE
  have hz := (GlobalTheory.ChF.padicInt_algebra_of_isAdicComplete_and_matrix_unique p O).2 g
    (ρ.comp (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := ℤ_[p]) (B := OE)))
  set E : (OE →+* C) → Submodule C (Fin g → C) :=
    fun τ => ⨅ a : OE, Module.End.eigenspace (ρE a) (τ a) with hE
  have hact : ∀ (τ : OE →+* O) (y : Fin g → C), y ∈ E ((algebraMap O C).comp τ) →
      ∀ x, σ x y = algebraMap O C (tauExt τ x) • y := by
    intro τ y hy x
    have hy' : ∀ a, σ (1 ⊗ₜ[ℤ] a) y = algebraMap O C (τ a) • y := by
      intro a
      have := (Submodule.mem_iInf _).1 hy a
      exact Module.End.mem_eigenspace_iff.1 this
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x x' h h' => rw [map_add (f := _), map_add (f := _), map_add (f := _), LinearMap.add_apply, h, h', add_smul]
    | tmul c a =>
      have h1 : (c ⊗ₜ[ℤ] a : ℤ_[p] ⊗[ℤ] OE) = (c ⊗ₜ[ℤ] 1) * (1 ⊗ₜ[ℤ] a) := by simp
      have h2 : ρ (c ⊗ₜ[ℤ] 1) = algebraMap ℤ_[p] O c • (1 : Matrix (Fin g) (Fin g) O) := hz c
      have h3 : ∀ z, σ (c ⊗ₜ[ℤ] 1) z = algebraMap O C (algebraMap ℤ_[p] O c) • z := by
        intro z
        have : (algebraMap ℤ_[p] O c • (1 : Matrix (Fin g) (Fin g) O)).map (algebraMap O C)
            = algebraMap O C (algebraMap ℤ_[p] O c) • (1 : Matrix (Fin g) (Fin g) C) := by
          ext i j
          rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, map_mul,
            Matrix.one_apply, Matrix.one_apply]
          split_ifs
          · rw [map_one]
          · rw [map_zero]
        rw [hσ, h2, this, map_smul, Matrix.toLin'_one]
        rfl
      have h4 : tauExt τ (c ⊗ₜ[ℤ] a) = algebraMap ℤ_[p] O c * τ a := by
        simp [tauExt, Algebra.ofId_apply]
      rw [h4, h1, map_mul, Module.End.mul_apply, h3, hy', smul_smul, map_mul]
  have hinj : Function.Injective
      (fun j : Fin n => (algebraMap O C).comp ((t j : Emb (O := O) e) : OE →+* O)) := by
    intro i j hij
    apply t.injective
    apply Subtype.ext
    exact (hex _).unique hij rfl
  have hrange : LinearMap.range (σ e) =
      ⨆ j : Fin n, E ((algebraMap O C).comp ((t j : Emb (O := O) e) : OE →+* O)) := by
    apply le_antisymm
    · rw [LinearMap.range_eq_map, ← htop, Submodule.map_iSup]
      refine iSup_le fun τ => ?_
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨τ', rfl, -⟩ := hex τ
      rw [hact τ' y hy e]
      rcases h01 e τ' he with h | h
      · rw [h]; simp
      · rw [h, map_one, one_smul]
        refine Submodule.mem_iSup_of_mem (t.symm ⟨τ', h⟩) ?_
        rw [Equiv.apply_symm_apply]
        exact hy
    · refine iSup_le fun j => fun y hy => ⟨y, ?_⟩
      have h : tauExt ((t j : Emb (O := O) e) : OE →+* O) e = 1 := (t j).2
      rw [hact _ y hy e, h, map_one, one_smul]
  have hsum := finrank_iSup_indep _ (hind.comp hinj)
  have hfin : r' = ∑ j, eigDim C (fun a : OE => ρ (1 ⊗ₜ[ℤ] a))
      ((algebraMap O C).comp ((t j : Emb (O := O) e) : OE →+* O)) := by
    have h1 : Module.finrank C (LinearMap.range (σ e)) = r' := hrk
    rw [← h1, hrange]
    exact hsum
  rw [← hfin, ← hrr]
  exact hne

end GlobalTheory.ChF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.RangeIdempotentRankSumEigenspaceDimStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.range_idempotent_rank_sum_eigenspaceDim : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] [StarRing OE] (g : ℕ) (ρ : (ℤ_[p] ⊗[ℤ] OE) →+* Matrix (Fin g) (Fin g) O) (e : ℤ_[p] ⊗[ℤ] OE), e * e = e → ∀ (n : ℕ) (t : Fin n ≃ Emb (O := O) e), Nonempty (LinearMap.range (Matrix.mulVecLin (ρ e)) ≃ₗ[O] (Fin (∑ j, eigDim C (fun a : OE => ρ (1 ⊗ₜ[ℤ] a)) ((algebraMap O C).comp ((t j : Emb (O := O) e) : OE →+* O))) → O)) := by
  first | exact @GlobalTheory.ChF.range_idempotent_equiv_sum_eigDim | exact GlobalTheory.ChF.range_idempotent_equiv_sum_eigDim | (intros; apply GlobalTheory.ChF.range_idempotent_equiv_sum_eigDim <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AbelianPartCokernelLengthLe
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem place_mul_bar {p : ℕ} [Fact p.Prime] {OE : Type} [CommRing OE] [StarRing OE] (w : Place p OE)
    (hinv : ∀ x, sig p OE (sig p OE x) = x) : w.e * w.bar = 0 := by
  have hb : w.bar * w.bar = w.bar := by
    unfold Place.bar
    rw [← map_mul, w.idem]
  rcases w.prim (w.e * w.bar) (by rw [_root_.mul_mul_mul_comm, w.idem, hb])
    (by rw [mul_right_comm, w.idem]) with h | h
  · exact h
  · exfalso
    apply w.split
    have h2 := congrArg (sig p OE) h
    unfold Place.bar at h h2
    rw [map_mul, hinv, mul_comm, h] at h2
    exact h2.symm

theorem abelian_coker_bound : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] [StarRing OE] (cp : O), HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp → ∀ (g : ℕ) (H : HodgeTateDatum p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp), H.P = 0 → H.PL = 0 → ∀ (w : Place p OE) (t : Fin w.n ≃ Emb (O := O) w.e) (rm : ℕ), (∀ τ ∈ Emb (O := O) w.bar, eigDim C (fun a : OE => H.ρL (1 ⊗ₜ[ℤ] a)) ((algebraMap O C).comp τ) ≤ rm) → ∃ cw : NNReal, HasLen v O (htCoker H w.e w.bar) cw ∧ (v (algebraMap O C (p : O)) : ℝ) ^ (((w.n : ℝ) * rm) / ((p : ℝ) - 1)) ≤ cw := by
  intro p _ C _ _ _ v O _ _ hv _ _ _ OE _ _ _ _ _ _ cp hS g H hP hPL w t rm hrm
  obtain ⟨-, -, hstar⟩ := GlobalTheory.ChF.embeddings_idempotents_conjugation p C v O hv OE
  have hsig : ∀ x, sig p OE x = sigE p OE x := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rfl
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
  have hinv : ∀ x, sig p OE (sig p OE x) = x := fun x => by rw [hsig, hsig, hS.invol]
  have h0 : w.e * w.bar = 0 := place_mul_bar w hinv
  have he := w.idem
  have hbar : sigE p OE w.e = w.bar := (hsig _).symm
  have hbar' : sigE p OE w.bar = w.e := by rw [← hbar, hS.invol]
  have hb : w.bar * w.bar = w.bar := by rw [← hbar, ← map_mul, w.idem]
  let c : OE →+* OE := ((starRingAut : RingAut OE) : OE ≃+* OE).toRingHom
  have hcc : ∀ τ : OE →+* O, (τ.comp c).comp c = τ := fun τ => by
    ext a
    simp [c]
  let s : Emb (O := O) w.e ≃ Emb (O := O) w.bar :=
    { toFun := fun τ => ⟨τ.1.comp c, by
        have := τ.2
        simp only [Emb, Set.mem_setOf_eq] at this ⊢
        rw [(hstar τ.1 w.bar).1, hbar', this]⟩
      invFun := fun τ => ⟨τ.1.comp c, by
        have := τ.2
        simp only [Emb, Set.mem_setOf_eq] at this ⊢
        rw [(hstar τ.1 w.e).1, hbar, this]⟩
      left_inv := fun τ => Subtype.ext (hcc τ.1)
      right_inv := fun τ => Subtype.ext (hcc τ.1) }
  have hd := GlobalTheory.T.range_idempotent_rank_sum_eigenspaceDim p C v O hv OE g H.ρL w.bar hb w.n (t.trans s)
  obtain ⟨cw, hcw⟩ : ∃ x, HasLen v O (htCoker H w.e w.bar) x :=
    lenEx C v O hv g H.Ht (H.ρL w.e) ((H.ρ w.bar).map (algebraMap ℤ_[p] O))
  refine ⟨cw, hcw, ?_⟩
  have hav := lengthDegree_abelianVariety p g C v O _ _ cp hS H 3 ![w.e, w.bar, 1 - w.e - w.bar] (Equiv.swap 0 1)
    (by
      intro i j
      fin_cases i <;> fin_cases j <;> simp <;>
        first
        | exact he
        | exact hb
        | linear_combination h0
        | linear_combination -he - h0
        | linear_combination -hb - h0
        | linear_combination he + hb + 2 * h0)
    (by
      intro i
      fin_cases i
      · simpa using hbar
      · simpa using hbar'
      · have : (Equiv.swap (0 : Fin 3) 1) 2 = 2 := by decide
        simp only [Fin.reduceFinMk, this, Matrix.cons_val, map_sub, map_one, hbar, hbar']
        ring)
    (by simp [Fin.sum_univ_three, hP]) (by simp [hP])
    (by simp [Fin.sum_univ_three, hPL]) (by simp [hPL])
    0 (by decide) _ hd cw hcw
  refine le_trans ?_ hav
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  refine Real.rpow_le_rpow_of_exponent_ge ?_ ?_ ?_
  · exact_mod_cast pos_iff_ne_zero.2 hS.p_ne
  · exact_mod_cast hS.p_lt.le
  · refine div_le_div_of_nonneg_right ?_ (by linarith)
    have := Finset.sum_le_card_nsmul Finset.univ _ rm (fun j _ => hrm _ ((t.trans s) j).2)
    simp only [Finset.card_univ, Fintype.card_fin, smul_eq_mul] at this
    exact_mod_cast this

end GlobalTheory.ChF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AbelianPartCokernelLengthLeStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianPart_cokernel_length_le : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] [StarRing OE] (cp : O), HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp → ∀ (g : ℕ) (H : HodgeTateDatum p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp), H.P = 0 → H.PL = 0 → ∀ (w : Place p OE) (t : Fin w.n ≃ Emb (O := O) w.e) (rm : ℕ), (∀ τ ∈ Emb (O := O) w.bar, eigDim C (fun a : OE => H.ρL (1 ⊗ₜ[ℤ] a)) ((algebraMap O C).comp τ) ≤ rm) → ∃ cw : NNReal, HasLen v O (htCoker H w.e w.bar) cw ∧ (v (algebraMap O C (p : O)) : ℝ) ^ (((w.n : ℝ) * rm) / ((p : ℝ) - 1)) ≤ cw := by
  first | exact @GlobalTheory.ChF.abelian_coker_bound | exact GlobalTheory.ChF.abelian_coker_bound | (intros; apply GlobalTheory.ChF.abelian_coker_bound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.DiscrPowerBasis
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PowerBasisDiscr

private theorem val_discr {C : Type} [Field C] (v : Valuation C NNReal) {n : ℕ} (a : Fin n → C) :
    v (discr a) = v ((Matrix.vandermonde a).det ^ 2) := by
  have h := Finset.prod_prod_Ioi_mul_eq_prod_prod_off_diag (fun i j : Fin n => v (a j - a i))
  rw [Matrix.det_vandermonde, map_pow, Up.discr]
  simp only [map_prod]
  rw [sq, ← Finset.prod_mul_distrib]
  simp only [← Finset.prod_mul_distrib]
  have h2 : ∀ i : Fin n, Finset.univ.erase i = ({i}ᶜ : Finset (Fin n)) := by
    intro i; ext j; simp
  simp only [h2]
  rw [← h]
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  rw [Valuation.map_sub_swap v (a i) (a j)]

private theorem inj_of_discr {C : Type} [Field C] {n : ℕ} (a : Fin n → C) (h : discr a ≠ 0) :
    Function.Injective a := by
  intro i j hij
  by_contra hne
  apply h
  refine Finset.prod_eq_zero (Finset.mem_univ i) (Finset.prod_eq_zero (i := j) ?_ ?_)
  · simp [Ne.symm hne]
  · rw [hij, sub_self]

private theorem det_change {R M O : Type} [CommRing R] [AddCommGroup M] [Module R M] [CommRing O]
    [Algebra R O] {n : ℕ} (b b' : Module.Basis (Fin n) R M) (f : Fin n → M →ₗ[R] O) :
    ∃ u : O, IsUnit u ∧ (Matrix.of fun i j => f j (b' i)).det = u * (Matrix.of fun i j => f j (b i)).det := by
  refine ⟨algebraMap R O (b.toMatrix b').det, ?_, ?_⟩
  · exact (b.isUnit_det b').map _
  · rw [← Matrix.det_transpose (b.toMatrix b'), RingHom.map_det, ← Matrix.det_mul]
    congr 1
    ext i j
    simp only [Matrix.of_apply, Matrix.mul_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
      Matrix.transpose_apply, Module.Basis.toMatrix_apply]
    conv_lhs => rw [← b.sum_repr (b' i)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Algebra.smul_def]

theorem discr_power_basis : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] [StarRing OE] (w : Place p OE) (t : Fin w.n ≃ Emb (O := O) w.e) (vd : ℝ), HasVd p v w t vd → ∀ (α : ℤ_[p] ⊗[ℤ] OE) (b : Module.Basis (Fin w.n) ℤ_[p] w.Ow), (∀ k, (b k : ℤ_[p] ⊗[ℤ] OE) = w.e * α ^ (k : ℕ)) → Function.Injective (fun j => tauExt ((t j : Emb (O := O) w.e) : OE →+* O) α) ∧ 0 ≤ (w.n : ℝ) * vd ∧ (v (discr fun j => algebraMap O C (tauExt ((t j : Emb (O := O) w.e) : OE →+* O) α)) : ℝ) = (v (algebraMap O C (p : O)) : ℝ) ^ ((w.n : ℝ) * vd) := by
  intro p _ C _ _ _ v O _ _ hv hp _ _ OE _ _ _ _ _ _ w t vd hvd α b hb
  obtain ⟨b', hb'⟩ := hvd
  obtain ⟨u, hu, hdet⟩ := det_change b b'
    (fun j => (tauExt ((t j : Emb (O := O) w.e) : OE →+* O)).toLinearMap ∘ₗ w.Ow.subtype)
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, AlgHom.toLinearMap_apply] at hdet
  have hM : (Matrix.of fun i j => tauExt ((t j : Emb (O := O) w.e) : OE →+* O) (b i : ℤ_[p] ⊗[ℤ] OE)) =
      (Matrix.vandermonde fun j => tauExt ((t j : Emb (O := O) w.e) : OE →+* O) α)ᵀ := by
    ext i j
    have h1 : tauExt ((t j : Emb (O := O) w.e) : OE →+* O) w.e = 1 := (t j).2
    simp [hb, h1, Matrix.vandermonde_apply]
  have hvu : v (algebraMap O C u) = 1 := hv.isUnit_iff_valuation_eq_one.1 hu
  have key : v (discr fun j => algebraMap O C (tauExt ((t j : Emb (O := O) w.e) : OE →+* O) α)) =
      v (algebraMap O C (Matrix.det (Matrix.of fun i j =>
        tauExt ((t j : Emb (O := O) w.e) : OE →+* O) (b' i : ℤ_[p] ⊗[ℤ] OE)) ^ 2)) := by
    rw [val_discr, hdet, hM, Matrix.det_transpose, mul_pow, map_mul, map_mul, map_pow, map_pow, map_pow,
      hvu, one_pow, _root_.one_mul, map_pow, map_pow, RingHom.map_det]
    congr 3
    ext i j
    simp [Matrix.vandermonde_apply]
  have hq0 : 0 < (v (algebraMap O C (p : O)) : ℝ) := by
    have : v (algebraMap O C (p : O)) ≠ 0 := by
      rw [map_natCast, Valuation.ne_zero_iff]
      exact_mod_cast (Fact.out : p.Prime).ne_zero
    exact_mod_cast pos_iff_ne_zero.2 this
  have hq1 : (v (algebraMap O C (p : O)) : ℝ) < 1 := by
    have : v (algebraMap O C (p : O)) < 1 :=
      lt_of_le_of_ne (hv.map_le_one _) fun h => hp.out (hv.isUnit_iff_valuation_eq_one.2 h)
    exact_mod_cast this
  refine ⟨?_, ?_, by rw [key, hb']⟩
  · refine Function.Injective.of_comp (f := algebraMap O C) (inj_of_discr _ fun h0 => ?_)
    have h3 := Real.rpow_pos_of_pos hq0 ((w.n : ℝ) * vd)
    rw [← hb', ← key] at h3
    have h4 : discr (fun j => algebraMap O C (tauExt ((t j : Emb (O := O) w.e) : OE →+* O) α)) = 0 := h0
    rw [h4] at h3
    simp at h3
  · by_contra hneg
    have h3 := Real.one_lt_rpow_of_pos_of_lt_one_of_neg hq0 hq1 (not_le.1 hneg)
    rw [← hb'] at h3
    have h4 := hv.map_le_one (Matrix.det (Matrix.of fun i j =>
        tauExt ((t j : Emb (O := O) w.e) : OE →+* O) (b' i : ℤ_[p] ⊗[ℤ] OE)) ^ 2)
    exact absurd h4 (not_le.2 (by exact_mod_cast h3))

end GlobalTheory.PowerBasisDiscr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LatticeInequalityValuationIntegers
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LatticeInequalityValuationIntegers
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

section aux

variable {C : Type} [Field C] {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C]

private theorem exists_basisMat (hv : v.Integers O) {κ : Type} [Fintype κ] [DecidableEq κ]
    (N : Submodule O (κ → O)) (hN : N.FG) (D : O) (hD : D ≠ 0) (hDN : ∀ z, D • z ∈ N) :
    ∃ B : Matrix κ κ O, B.det ≠ 0 ∧ LinearMap.range B.mulVecLin = N := by
  have : IsDomain O := hv.hom_inj.isDomain
  have : IsFractionRing O C := hv.isFractionRing
  have : ValuationRing O := ValuationRing.of_integers v hv
  have : Module.Finite O N := Module.Finite.iff_fg.2 hN
  have : Module.Flat O N := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, ← Submodule.isTorsionFree_iff_torsion_eq_bot]
    infer_instance
  have : Module.Free O N := Module.free_of_flat_of_isLocalRing
  have h1 : Module.finrank O N ≤ Module.finrank O (κ → O) :=
    LinearMap.finrank_le_finrank_of_injective (f := N.subtype) N.injective_subtype
  have h2 : Module.finrank O (κ → O) ≤ Module.finrank O N := by
    refine LinearMap.finrank_le_finrank_of_injective
      (f := LinearMap.codRestrict N (D • LinearMap.id) (fun z => hDN z)) ?_
    intro x y hxy
    have h3 : D • x = D • y := congrArg Subtype.val hxy
    funext i
    exact mul_left_cancel₀ hD (congrFun h3 i)
  have h3 : Module.finrank O N = Fintype.card κ := by
    rw [← Module.finrank_fintype_fun_eq_card O]; omega
  let b : Module.Basis κ O N :=
    (Module.finBasisOfFinrankEq O N h3).reindex (Fintype.equivFin κ).symm
  have hB : ∀ c : κ → O, (Matrix.of fun i j => (b j : κ → O) i) *ᵥ c =
      ((∑ j, c j • b j : N) : κ → O) := by
    intro c
    funext i
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  refine ⟨Matrix.of fun i j => (b j : κ → O) i, ?_, ?_⟩
  · intro h0
    obtain ⟨c, hc, hc0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    rw [hB] at hc0
    have h4 : (∑ j, c j • b j : N) = 0 := Subtype.ext hc0
    exact hc (funext (Fintype.linearIndependent_iff.1 b.linearIndependent c h4))
  · ext x
    constructor
    · rintro ⟨c, rfl⟩
      rw [Matrix.mulVecLin_apply, hB]
      exact Subtype.property _
    · intro hx
      refine ⟨b.repr ⟨x, hx⟩, ?_⟩
      rw [Matrix.mulVecLin_apply, hB, b.sum_repr]

private theorem det_map_ne (hv : v.Integers O) {κ : Type} [Fintype κ] [DecidableEq κ]
    {B : Matrix κ κ O} (hB : B.det ≠ 0) : (B.map (algebraMap O C)).det ≠ 0 := by
  have h := RingHom.map_det (algebraMap O C) B
  rw [RingHom.mapMatrix_apply] at h
  rw [← h]
  exact fun h0 => hB (hv.hom_inj (by rw [h0, map_zero]))

private theorem integral_iff (hv : v.Integers O) {κ : Type} (c : κ → C) :
    (∀ j, v (c j) ≤ 1) ↔ ∃ c₀ : κ → O, c = fun j => algebraMap O C (c₀ j) := by
  constructor
  · intro hc
    choose c₀ hc₀ using fun j => hv.exists_of_le_one (hc j)
    exact ⟨c₀, funext fun j => (hc₀ j).symm⟩
  · rintro ⟨c₀, rfl⟩ j
    exact hv.map_le_one _

private theorem mem_pts (hv : v.Integers O) {κ : Type} [Fintype κ] [DecidableEq κ]
    {B : Matrix κ κ O} (L : Lat v κ) (hL : L.B = B.map (algebraMap O C)) (x : κ → C) :
    x ∈ L.pts ↔ ∃ z ∈ LinearMap.range B.mulVecLin, x = fun j => algebraMap O C (z j) := by
  have key : ∀ c₀ : κ → O, L.B *ᵥ (fun j => algebraMap O C (c₀ j)) =
      fun j => algebraMap O C ((B *ᵥ c₀) j) := by
    intro c₀
    funext i
    simp [hL, Matrix.mulVec, dotProduct]
  constructor
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨c₀, rfl⟩ := (integral_iff hv c).1 hc
    exact ⟨B *ᵥ c₀, ⟨c₀, rfl⟩, key c₀⟩
  · rintro ⟨_, ⟨c₀, rfl⟩, rfl⟩
    exact ⟨_, (integral_iff hv _).2 ⟨c₀, rfl⟩, (key c₀).symm⟩

private theorem len_eq (hv : v.Integers O) {κ : Type} [Fintype κ] [DecidableEq κ]
    {B B' : Matrix κ κ O} (hB : B.det ≠ 0) (M M' : Submodule O (κ → O))
    (hM : LinearMap.range B.mulVecLin = M) (hM' : LinearMap.range B'.mulVecLin = M')
    (hle : M' ≤ M) {c : NNReal} (hc : HasLen v O (M ⧸ M'.comap M.subtype) c) :
    c = v (B'.map (algebraMap O C)).det / v (B.map (algebraMap O C)).det := by
  have : IsDomain O := hv.hom_inj.isDomain
  subst hM hM'
  have hcol : ∀ j, ∃ x : κ → O, B *ᵥ x = B' *ᵥ Pi.single j 1 := fun j =>
    hle ⟨Pi.single j 1, rfl⟩
  choose X hX using hcol
  have hBX : B * (Matrix.of X)ᵀ = B' := by
    ext i j
    have := congrFun (hX j) i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Pi.single_apply] using this
  have hinj : Function.Injective B.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro m hm
    by_contra h0
    exact hB (Matrix.exists_mulVec_eq_zero_iff.1 ⟨m, h0, hm⟩)
  let e := LinearEquiv.ofInjective B.mulVecLin hinj
  have hmap : (LinearMap.range ((Matrix.of X)ᵀ).mulVecLin).map
      (e : (κ → O) →ₗ[O] LinearMap.range B.mulVecLin) =
      (LinearMap.range B'.mulVecLin).comap (LinearMap.range B.mulVecLin).subtype := by
    ext y
    constructor
    · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
      refine ⟨w, ?_⟩
      show B' *ᵥ w = B *ᵥ ((Matrix.of X)ᵀ *ᵥ w)
      rw [Matrix.mulVec_mulVec, hBX]
    · rintro ⟨w, hw⟩
      refine ⟨_, ⟨w, rfl⟩, Subtype.ext ?_⟩
      show B *ᵥ ((Matrix.of X)ᵀ *ᵥ w) = _
      rw [Matrix.mulVec_mulVec, hBX]
      exact hw
  have h1 := hasLen_of_equiv (Submodule.Quotient.equiv _ _ e hmap) hc
  have h2 := hasLen_unique hv h1 (hasLen_coker_det' v O hv κ _)
  have h3 : v (B.map (algebraMap O C)).det ≠ 0 := (Valuation.ne_zero_iff v).2 (det_map_ne hv hB)
  have h4 := RingHom.map_det (algebraMap O C) ((Matrix.of X)ᵀ)
  rw [RingHom.mapMatrix_apply] at h4
  rw [h2, ← hBX, Matrix.map_mul, Matrix.det_mul, map_mul, h4, mul_div_cancel_left₀ _ h3]


omit [Algebra O C] in
private theorem full_of_stable [IsDomain O] {n s : ℕ} (a : Fin n → O) (ha : Function.Injective a)
    (M : Submodule O (Fin n × Fin s → O))
    (hst : ∀ f ∈ M, (fun y : Fin n × Fin s => a y.1 * f y) ∈ M)
    (hsur : ∀ (τ : Fin n) (z : Fin s → O), ∃ f ∈ M, ∀ i, f (τ, i) = z i) :
    ∃ D : O, D ≠ 0 ∧ ∀ z, D • z ∈ M := by
  classical
  have hprod : ∀ (S : Finset (Fin n)), ∀ f ∈ M,
      (fun y : Fin n × Fin s => (∏ σ ∈ S, (a y.1 - a σ)) * f y) ∈ M := by
    intro S
    induction S using Finset.induction_on with
    | empty => intro f hf; simpa using hf
    | insert σ S hσ ih =>
      intro f hf
      have h1 := M.sub_mem (hst _ (ih f hf)) (M.smul_mem (a σ) (ih f hf))
      convert h1 using 1
      funext y
      simp only [Finset.prod_insert hσ, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
  set p : Fin n → O := fun τ => ∏ σ ∈ Finset.univ.erase τ, (a τ - a σ) with hp
  refine ⟨∏ τ, p τ, ?_, fun z => ?_⟩
  · refine Finset.prod_ne_zero_iff.2 fun τ _ => Finset.prod_ne_zero_iff.2 fun σ hσ => ?_
    exact sub_ne_zero.2 fun h => (Finset.ne_of_mem_erase hσ) (ha h).symm
  · choose f hfM hf using fun τ => hsur τ (fun i => z (τ, i))
    have h1 := M.sum_mem (t := Finset.univ) fun τ _ =>
      M.smul_mem (∏ σ ∈ Finset.univ.erase τ, p σ) (hprod (Finset.univ.erase τ) _ (hfM τ))
    convert h1 using 1
    funext y
    obtain ⟨τ, i⟩ := y
    rw [Finset.sum_apply, Finset.sum_eq_single τ]
    · simp only [Pi.smul_apply, smul_eq_mul, hf]
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ τ), _root_.mul_assoc]
    · intro σ _ hσ
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [Finset.prod_eq_zero (s := Finset.univ.erase σ) (i := τ) (f := fun ρ => a τ - a ρ)
        (Finset.mem_erase.2 ⟨hσ.symm, Finset.mem_univ _⟩) (sub_self _)]
      simp
    · simp

private theorem killed_of_hasLen {M : Type} [AddCommGroup M] [Module O M] {x : NNReal}
    (h : HasLen v O M x) (hx : x ≠ 0) : ∃ d : O, d ≠ 0 ∧ ∀ y : M, d • y = 0 := by
  obtain ⟨m, c, ⟨e⟩, rfl⟩ := h
  have hd : v (algebraMap O C (∏ i, c i)) = ∏ i, v (algebraMap O C (c i)) := by
    simp only [map_prod]
  refine ⟨∏ i, c i, fun h0 => hx (by rw [← hd, h0]; simp), fun y => ?_⟩
  apply e.injective
  rw [map_smul, map_zero]
  funext i
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (e y i)
  rw [Pi.smul_apply, ← hr, Pi.zero_apply, Algebra.smul_def]
  show Ideal.Quotient.mk _ _ * _ = 0
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  exact (Finset.dvd_prod_of_mem c (Finset.mem_univ i)).mul_right r


omit [Algebra O C] in
private theorem proj_span {n s h : ℕ} (a : Fin n → O) (φ : Fin h → Fin n × Fin s → O) (τ : Fin n)
    (z : Fin s → O) :
    z ∈ Submodule.span O (Set.range fun l => fun i => φ l (τ, i)) ↔
      ∃ f ∈ Submodule.span O (Set.range fun q : Fin n × Fin h =>
        fun y : Fin n × Fin s => a y.1 ^ (q.1 : ℕ) * φ q.2 y), z = fun i => f (τ, i) := by
  constructor
  · intro hz
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 hz
    refine ⟨∑ l, c l • φ l, Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨(⟨0, τ.pos⟩, l), ?_⟩), ?_⟩
    · funext y; simp
    · funext i; simp [Finset.sum_apply]
  · rintro ⟨f, hf, rfl⟩
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 hf
    have h1 := Submodule.sum_mem (Submodule.span O (Set.range fun l => fun i => φ l (τ, i)))
      (t := Finset.univ) (f := fun q : Fin n × Fin h =>
        (c q * a τ ^ (q.1 : ℕ)) • fun i => φ q.2 (τ, i))
      fun q _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨q.2, rfl⟩)
    convert h1 using 1
    funext i
    simp [Finset.sum_apply, _root_.mul_assoc]

end aux

theorem lattice_ineq_integers : ∀ (C : Type) [Field C] [IsAlgClosed C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → (∃ c : C, 0 < v c ∧ v c < 1) → ∀ (n s h : ℕ) (a : Fin n → O), Function.Injective a → ∀ (M : Submodule O (Fin n × Fin s → O)), M.FG → (∀ f ∈ M, (fun y : Fin n × Fin s => a y.1 * f y) ∈ M) → (∀ (τ : Fin n) (z : Fin s → O), ∃ f ∈ M, ∀ i, f (τ, i) = z i) → ∀ (φ : Fin h → Fin n × Fin s → O), (∀ l, φ l ∈ M) → ∀ c : NNReal, c ≠ 0 → HasLen v O (M ⧸ (Submodule.span O (Set.range fun q : Fin n × Fin h => fun y : Fin n × Fin s => a y.1 ^ (q.1 : ℕ) * φ q.2 y)).comap M.subtype) c → ∃ x : Fin n → NNReal, (∀ τ, HasLen v O ((Fin s → O) ⧸ Submodule.span O (Set.range fun l => fun i => φ l (τ, i))) (x τ)) ∧ c ^ 2 * v (discr fun τ => algebraMap O C (a τ)) ^ h ≤ (∏ τ, x τ) ^ 2 * v (discr fun τ => algebraMap O C (a τ)) ^ s := by
  intro C _ _ v O _ _ hv hnt n s h a ha M hM hst hsur φ hφ c hc0 hc
  have : IsDomain O := hv.hom_inj.isDomain
  set M' := Submodule.span O (Set.range fun q : Fin n × Fin h =>
    fun y : Fin n × Fin s => a y.1 ^ (q.1 : ℕ) * φ q.2 y) with hM'def
  have hpow : ∀ (k : ℕ), ∀ f ∈ M, (fun y : Fin n × Fin s => a y.1 ^ k * f y) ∈ M := by
    intro k f hf
    induction k with
    | zero => simpa using hf
    | succ k ih =>
      convert hst _ ih using 1
      funext y
      ring
  have hle : M' ≤ M := Submodule.span_le.2 (by rintro _ ⟨q, rfl⟩; exact hpow _ _ (hφ q.2))
  obtain ⟨D, hD, hDM⟩ := full_of_stable a ha M hst hsur
  obtain ⟨d, hd, hdM⟩ := killed_of_hasLen hc hc0
  have hdD : d * D ≠ 0 := mul_ne_zero hd hD
  have hDM' : ∀ z, (d * D) • z ∈ M' := by
    intro z
    have h1 := hdM (Submodule.Quotient.mk ⟨D • z, hDM z⟩)
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h1
    rw [mul_smul]
    exact h1
  have hDτ : ∀ τ z, (d * D) • z ∈ Submodule.span O (Set.range fun l => fun i => φ l (τ, i)) :=
    fun τ z => (proj_span a φ τ _).2 ⟨_, hDM' (fun y => z y.2), rfl⟩
  obtain ⟨B, hB, hBM⟩ := exists_basisMat hv M hM D hD hDM
  obtain ⟨B', hB', hBM'⟩ := exists_basisMat hv M' (Submodule.fg_span (Set.finite_range _)) _ hdD hDM'
  choose Bτ hBτ hBMτ using fun τ => exists_basisMat hv _
    (Submodule.fg_span (Set.finite_range _)) _ hdD (hDτ τ)
  have hainj : Function.Injective fun τ => algebraMap O C (a τ) := hv.hom_inj.comp ha
  let L : Lat v (Fin n × Fin s) := ⟨_, det_map_ne hv hB⟩
  let L' : Lat v (Fin n × Fin s) := ⟨_, det_map_ne hv hB'⟩
  let Lτ : Fin n → Lat v (Fin s) := fun τ => ⟨_, det_map_ne hv (hBτ τ)⟩
  let F : Lat v (Fin n × Fin h) := ⟨freeMat (fun τ => algebraMap O C (a τ)) h, by
    rw [det_freeMat]
    exact pow_ne_zero _ (Matrix.det_vandermonde_ne_zero_iff.2 hainj)⟩
  have hL := mem_pts hv L rfl
  have hL' := mem_pts hv L' rfl
  have hLτ := fun τ => mem_pts hv (Lτ τ) rfl
  have hstd := mem_pts hv (B := 1) (Lat.std v (Fin s)) (by simp [Lat.std])
  simp only [hBM, hBM', hBMτ] at hL hL' hLτ
  refine ⟨fun τ => colen (Lτ τ) (Lat.std v (Fin s)), fun τ => ?_, ?_⟩
  · have h1 := hasLen_coker_det' v O hv _ (Bτ τ)
    rw [hBMτ, RingHom.map_det, RingHom.mapMatrix_apply] at h1
    simpa [colen, Lat.std, Lτ] using h1
  refine lat_conseq C v O hv hnt n _ hainj (fun τ => hv.map_le_one _) s h
    (fun τ => Matrix.of fun i l => algebraMap O C (φ l (τ, i))) F L L' (fun _ => Lat.std v (Fin s))
    Lτ rfl (fun τ => ?_) ?_ ?_ (fun τ => ?_) (fun τ => ?_) c (len_eq hv hB M M' hBM hBM' hle hc).le
  · intro w
    have hne : algebraMap O C (d * D) ≠ 0 := fun h0 => hdD (hv.hom_inj (by rw [h0, map_zero]))
    choose r hr using fun j => (Submodule.mem_span_range_iff_exists_fun O).1
      (hDτ τ (Pi.single j 1))
    refine ⟨fun l => ∑ j, w j / algebraMap O C (d * D) * algebraMap O C (r j l), ?_⟩
    funext i
    have h1 : ∀ j, ∑ l, algebraMap O C (φ l (τ, i)) * algebraMap O C (r j l) =
        if i = j then algebraMap O C (d * D) else 0 := by
      intro j
      have h2 := congrArg (algebraMap O C) (congrFun (hr j) i)
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, Pi.single_apply, mul_ite,
        _root_.mul_one, mul_zero] at h2
      rw [apply_ite (algebraMap O C), map_zero] at h2
      rw [← h2]
      exact Finset.sum_congr rfl fun l _ => by rw [map_mul, mul_comm]
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    have h3 : ∀ j, ∑ l, algebraMap O C (φ l (τ, i)) *
        (w j / algebraMap O C (d * D) * algebraMap O C (r j l)) =
        if i = j then w j else 0 := by
      intro j
      simp only [mul_left_comm _ (w j / _), ← Finset.mul_sum, h1]
      split_ifs
      · exact div_mul_cancel₀ _ hne
      · exact mul_zero _
    simp only [h3]
    simp
  · have key : ∀ c₀ : Fin n × Fin h → O, (fun y : Fin n × Fin s =>
        ∑ l, algebraMap O C (φ l (y.1, y.2)) *
          (F.B *ᵥ fun q => algebraMap O C (c₀ q)) (y.1, l)) =
        fun j => algebraMap O C ((∑ q : Fin n × Fin h, c₀ q •
          fun y : Fin n × Fin s => a y.1 ^ (q.1 : ℕ) * φ q.2 y) j) := by
      intro c₀
      funext y
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [F, freeMat, Matrix.mulVec, dotProduct, Matrix.of_apply, Fintype.sum_prod_type,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, map_pow, ite_mul, zero_mul,
        Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    ext x
    rw [hL']
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨c₀, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 hz
      exact ⟨_, ⟨_, (integral_iff hv _).2 ⟨c₀, rfl⟩, rfl⟩, key c₀⟩
    · rintro ⟨_, ⟨c₁, hc₁, rfl⟩, rfl⟩
      obtain ⟨c₀, rfl⟩ := (integral_iff hv c₁).1 hc₁
      exact ⟨_, (Submodule.mem_span_range_iff_exists_fun O).2 ⟨c₀, rfl⟩, key c₀⟩
  · intro w hw
    obtain ⟨z, hz, rfl⟩ := (hL w).1 hw
    exact (hL _).2 ⟨_, hst z hz, by funext y; simp⟩
  · ext x
    rw [hstd]
    constructor
    · rintro ⟨z, -, rfl⟩
      obtain ⟨f, hf, hfz⟩ := hsur τ z
      exact ⟨_, (hL _).2 ⟨f, hf, rfl⟩, by funext i; simp [hfz]⟩
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨z, hz, rfl⟩ := (hL w).1 hw
      exact ⟨fun i => z (τ, i), ⟨fun i => z (τ, i), by simp⟩, rfl⟩
  · ext x
    rw [hLτ]
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨f, hf, rfl⟩ := (proj_span a φ τ z).1 hz
      exact ⟨_, (hL' _).2 ⟨f, hf, rfl⟩, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨z, hz, rfl⟩ := (hL' w).1 hw
      exact ⟨fun i => z (τ, i), (proj_span a φ τ _).2 ⟨z, hz, rfl⟩, rfl⟩

end GlobalTheory.ChF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LatticeInequalityValuationIntegersStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_inequality_valuation_integers : ∀ (C : Type) [Field C] [IsAlgClosed C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → (∃ c : C, 0 < v c ∧ v c < 1) → ∀ (n s h : ℕ) (a : Fin n → O), Function.Injective a → ∀ (M : Submodule O (Fin n × Fin s → O)), M.FG → (∀ f ∈ M, (fun y : Fin n × Fin s => a y.1 * f y) ∈ M) → (∀ (τ : Fin n) (z : Fin s → O), ∃ f ∈ M, ∀ i, f (τ, i) = z i) → ∀ (φ : Fin h → Fin n × Fin s → O), (∀ l, φ l ∈ M) → ∀ c : NNReal, c ≠ 0 → HasLen v O (M ⧸ (Submodule.span O (Set.range fun q : Fin n × Fin h => fun y : Fin n × Fin s => a y.1 ^ (q.1 : ℕ) * φ q.2 y)).comap M.subtype) c → ∃ x : Fin n → NNReal, (∀ τ, HasLen v O ((Fin s → O) ⧸ Submodule.span O (Set.range fun l => fun i => φ l (τ, i))) (x τ)) ∧ c ^ 2 * v (discr fun τ => algebraMap O C (a τ)) ^ h ≤ (∏ τ, x τ) ^ 2 * v (discr fun τ => algebraMap O C (a τ)) ^ s := by
  first | exact @GlobalTheory.ChF.lattice_ineq_integers | exact GlobalTheory.ChF.lattice_ineq_integers | (intros; apply GlobalTheory.ChF.lattice_ineq_integers <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ColengthBoundSplitPlaceLinearData
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem lav_fp {O : Type} [CommRing O] {J : Type} [Fintype J]
    (h : ∀ (n : ℕ) (M N : Submodule O (Fin n → O)), M.FG → N.FG → N ≤ M →
      Module.FinitePresentation O (M ⧸ N.comap M.subtype))
    (M N : Submodule O (J → O)) (hM : M.FG) (hN : N.FG) (hle : N ≤ M) :
    Module.FinitePresentation O (M ⧸ N.comap M.subtype) := by
  let e : (J → O) ≃ₗ[O] (Fin (Fintype.card J) → O) :=
    LinearEquiv.funCongrLeft O O (Fintype.equivFin J).symm
  have h1 := h _ (M.map e.toLinearMap) (N.map e.toLinearMap) (hM.map _) (hN.map _)
    (Submodule.map_mono hle)
  refine Module.FinitePresentation.of_equiv
    (Submodule.Quotient.equiv ((N.map e.toLinearMap).comap (M.map e.toLinearMap).subtype) (N.comap M.subtype)
      (e.submoduleMap M).symm ?_)
  ext x
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
  constructor
  · rintro ⟨y, ⟨z, hz, hzy⟩, rfl⟩
    have : (((e.submoduleMap M).symm y : M) : J → O) = z := by
      rw [LinearEquiv.submoduleMap_symm_apply, ← hzy]
      exact e.symm_apply_apply z
    exact this ▸ hz
  · intro hx
    exact ⟨e.submoduleMap M x, ⟨x, hx, rfl⟩, (e.submoduleMap M).symm_apply_apply x⟩

private theorem lav_num (P D c cw X : ℝ) (n rm vd q : ℝ) (rp rm' h : ℕ) (hrm : rm = rm')
    (hP0 : 0 < P) (hP1 : P ≤ 1) (hvd : 0 ≤ n * vd) (hD : D = P ^ (n * vd)) (hh : h ≤ rp + rm')
    (hcw : P ^ ((n * rm) / q) ≤ cw) (hc : cw ≤ c) (hX : 0 ≤ X)
    (hl : c ^ 2 * D ^ h ≤ X ^ 2 * D ^ rp) : P ^ (n * rm * (1 / q + vd / 2)) ≤ X := by
  have hD0 : 0 < D := hD ▸ Real.rpow_pos_of_pos hP0 _
  have hD1 : D ≤ 1 := hD ▸ Real.rpow_le_one hP0.le hP1 hvd
  have h0 : 0 < P ^ ((n * rm) / q) := Real.rpow_pos_of_pos hP0 _
  have h1 : D ^ (rp + rm') ≤ D ^ h := pow_le_pow_of_le_one hD0.le hD1 hh
  have h2 : c ^ 2 * D ^ rm' ≤ X ^ 2 := by
    have : c ^ 2 * D ^ rm' * D ^ rp ≤ X ^ 2 * D ^ rp := by
      calc c ^ 2 * D ^ rm' * D ^ rp = c ^ 2 * D ^ (rp + rm') := by ring
        _ ≤ c ^ 2 * D ^ h := mul_le_mul_of_nonneg_left h1 (sq_nonneg c)
        _ ≤ _ := hl
    exact le_of_mul_le_mul_right this (pow_pos hD0 _)
  have h3 : (P ^ (n * rm * (1 / q + vd / 2))) ^ 2 = (P ^ ((n * rm) / q)) ^ 2 * D ^ rm' := by
    rw [hD, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hP0.le,
      ← Real.rpow_mul hP0.le, ← Real.rpow_mul hP0.le, ← Real.rpow_add hP0, ← hrm]
    congr 1
    push_cast
    ring
  refine (pow_le_pow_iff_left₀ (Real.rpow_pos_of_pos hP0 _).le hX two_ne_zero).1 ?_
  rw [h3]
  refine le_trans ?_ h2
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0.le (hcw.trans hc) 2) (pow_pos hD0 _).le

theorem colength_bound_linDat : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] [StarRing OE] (cp : O), HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp → ∀ (g : ℕ) (H : HodgeTateDatum p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (d r m : ℕ) (A : Matrix (Fin d) (Fin r) O) (B : Matrix (Fin g) (Fin d) O) (ρG : OE →+* Matrix (Fin d) (Fin d) O) (N : OE →+* Matrix (Fin r) (Fin r) ℤ) (s : Fin m → Fin d → O), LinDat H A B ρG N s → ∀ (w : Place p OE) (t : Fin w.n ≃ Emb (O := O) w.e) (vd : ℝ), HasVd p v w t vd → ∀ (rp rm : ℕ) (W : Fin w.n → Fin rp → Fin d → O), (∀ j, EigB ρG ((t j : Emb (O := O) w.e) : OE →+* O) (W j)) → (∀ τ ∈ Emb (O := O) w.bar, ∃ W' : Fin rm → Fin d → O, EigB ρG τ W') → ∃ xs : Fin w.n → NNReal, (∀ j, HasLen v O ((Fin rp → O) ⧸ Submodule.span O (Set.range fun k => Pdiv.ChartF.res (W j) (s k))) (xs j)) ∧ v (algebraMap O C (p : O)) ^ ((w.n : ℝ) * rm * (1 / ((p : ℝ) - 1) + vd / 2)) ≤ ∏ j, xs j := by
  intro p _ C _ _ _ v O _ _ hv _ _ _ OE _ _ _ _ _ _ cp hU g H d r m A B ρG N s hL w t vd hvd rp rm W hW hW'
  have hp0 : 0 < v (algebraMap O C (p : O)) := by
    rw [map_natCast, zero_lt_iff, Ne, map_eq_zero]
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hp1 : v (algebraMap O C (p : O)) < 1 :=
    lt_of_le_of_ne (hv.map_le_one _) fun h =>
      (Fact.out : ¬IsUnit (p : O)) (hv.isUnit_iff_valuation_eq_one.2 h)
  obtain ⟨-, -, α, b, hb⟩ := GlobalTheory.PlaceMono.place_monogenic p OE ⟨w.e, w.idem, w.ne_zero, w.prim⟩
  have hrm : ∀ τ ∈ Emb (O := O) w.bar,
      eigDim C (fun a : OE => H.ρL (1 ⊗ₜ[ℤ] a)) ((algebraMap O C).comp τ) ≤ rm := by
    intro τ hτ
    obtain ⟨W', hW''⟩ := hW' τ hτ
    have h1 := (GlobalTheory.ChF.eigB_res_surjective C v O hv OE d rm ρG τ W' hW'').2.2
    have h2 := (GlobalTheory.T.eigenspaceDim_add_split_exact_transpose C O OE d r g A B hL.exact ρG
      ((RingHom.mapMatrix (Int.castRingHom O)).comp N)
      (H.ρL.comp (Algebra.TensorProduct.includeRight : OE →ₐ[ℤ] ℤ_[p] ⊗[ℤ] OE).toRingHom)
      hL.eqB hL.eqA ((algebraMap O C).comp τ)).1
    rw [h1] at h2
    exact le_of_le_of_eq (Nat.le_add_left _ _) h2.symm
  obtain ⟨cw, hcw, hcwb⟩ := GlobalTheory.T.abelianPart_cokernel_length_le p C v O hv OE cp hU g H hL.noPad.1 hL.noPad.2 w t rm hrm
  obtain ⟨h, ψ, hh, hψ, f, hf⟩ := GlobalTheory.T.exists_abelian_torus_generators_at_place p C v O hv OE cp hU g H d r m A B ρG N s hL w t α b hb rp rm W hW hrm
  obtain ⟨hinj, hvd0, hD⟩ := GlobalTheory.PowerBasisDiscr.discr_power_basis p C v O hv OE w t vd hvd α b hb
  obtain ⟨hex, hmono, hfp⟩ := GlobalTheory.ChF.hasLen_exists_mono_fp C v O hv
  have hres := fun j => GlobalTheory.ChF.eigB_res_surjective C v O hv OE d rp ρG _ (W j) (hW j)
  have hstab : ∀ (x : ℤ_[p] ⊗[ℤ] OE) (u : Fin d → O), ∃ u' : Fin d → O, ∀ j,
      Pdiv.ChartF.res (W j) u' = tauExt ((t j : Emb (O := O) w.e) : OE →+* O) x • Pdiv.ChartF.res (W j) u := by
    intro x u
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, fun j => by simp⟩
    | tmul c a =>
      refine ⟨algebraMap ℤ_[p] O c • ((ρG a)ᵀ *ᵥ u), fun j => ?_⟩
      rw [map_smul, (hres j).2.1, smul_smul]
      simp [tauExt, Algebra.ofId_apply]
    | add x y hx hy =>
      obtain ⟨u1, h1⟩ := hx
      obtain ⟨u2, h2⟩ := hy
      exact ⟨u1 + u2, fun j => by rw [map_add (f := _), h1, h2, map_add (f := _), add_smul]⟩
  let κ : (Fin d → O) →ₗ[O] (Fin w.n × Fin rp → O) :=
    LinearMap.pi fun y : Fin w.n × Fin rp => (LinearMap.proj y.2).comp (Pdiv.ChartF.res (W y.1))
  have hκa : ∀ u y, κ u y = Pdiv.ChartF.res (W y.1) u y.2 := fun u y => rfl
  have hMfg : (LinearMap.range κ).FG := by
    rw [LinearMap.range_eq_map]; exact Module.Finite.fg_top.map _
  have hmem : ∀ (x : ℤ_[p] ⊗[ℤ] OE) (u : Fin d → O), (fun y : Fin w.n × Fin rp =>
      tauExt ((t y.1 : Emb (O := O) w.e) : OE →+* O) x * κ u y) ∈ LinearMap.range κ := by
    intro x u
    obtain ⟨u', hu'⟩ := hstab x u
    refine ⟨u', funext fun y => ?_⟩
    rw [hκa, hκa, hu']
    rfl
  obtain ⟨c, hc⟩ := hex _ (lav_fp hfp (LinearMap.range κ)
    (Submodule.span O (Set.range fun q : Fin w.n × Fin h => fun y : Fin w.n × Fin rp =>
      tauExt ((t y.1 : Emb (O := O) w.e) : OE →+* O) α ^ (q.1 : ℕ) * Pdiv.ChartF.res (W y.1) (ψ q.2) y.2))
    hMfg (Submodule.fg_span (Set.finite_range _)) (by
      rw [Submodule.span_le]
      rintro _ ⟨q, rfl⟩
      have := hmem (α ^ (q.1 : ℕ)) (ψ q.2)
      simp only [map_pow] at this
      exact this))
  have hcc : cw ≤ c := hmono _ _ f cw c hf hcw hc
  have hcw0 : (0 : ℝ) < cw := lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast hp0) _) hcwb
  have hc0 : c ≠ 0 := (lt_of_lt_of_le (by exact_mod_cast hcw0) hcc : (0 : NNReal) < c).ne'
  obtain ⟨x, hx, hineq⟩ := GlobalTheory.T.lattice_inequality_valuation_integers C v O hv ⟨_, hp0, hp1⟩ w.n rp h
    (fun j => tauExt ((t j : Emb (O := O) w.e) : OE →+* O) α) hinj (LinearMap.range κ) hMfg
    (by rintro _ ⟨u, rfl⟩; exact hmem α u)
    (by
      intro τ z
      obtain ⟨u, hu⟩ := (hres τ).1 z
      exact ⟨κ u, ⟨u, rfl⟩, fun i => by rw [hκa, hu]⟩)
    (fun l => κ (ψ l)) (fun l => ⟨ψ l, rfl⟩) c hc0 hc
  have hxs : ∀ j, ∃ y, HasLen v O ((Fin rp → O) ⧸ Submodule.span O
      (Set.range fun k => Pdiv.ChartF.res (W j) (s k))) y ∧ x j ≤ y := by
    intro j
    have hle : Submodule.span O (Set.range fun l => fun i => κ (ψ l) (j, i)) ≤
        Submodule.span O (Set.range fun k => Pdiv.ChartF.res (W j) (s k)) := by
      rw [Submodule.span_le]
      rintro _ ⟨l, rfl⟩
      exact hψ l j
    obtain ⟨y, hy⟩ := hex ((Fin rp → O) ⧸ Submodule.span O
      (Set.range fun k => Pdiv.ChartF.res (W j) (s k)))
      (Module.finitePresentation_of_surjective (Submodule.mkQ _) (Submodule.mkQ_surjective _)
        (by rw [Submodule.ker_mkQ]; exact Submodule.fg_span (Set.finite_range _)))
    exact ⟨y, hy, hmono _ _ (Submodule.factor hle) _ _ (Submodule.factor_surjective hle) (hx j) hy⟩
  choose xs hxs1 hxs2 using hxs
  refine ⟨xs, hxs1, le_trans ?_ (Finset.prod_le_prod' fun j _ => hxs2 j)⟩
  rw [← NNReal.coe_le_coe, NNReal.coe_rpow]
  refine lav_num _ _ c cw _ _ _ _ _ rp rm h rfl (by exact_mod_cast hp0) (by exact_mod_cast hp1.le) hvd0 hD hh
    hcwb (by exact_mod_cast hcc) (NNReal.coe_nonneg _) ?_
  exact_mod_cast hineq

end GlobalTheory.ChF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ColengthBoundSplitPlaceLinearDataStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.colength_bound_split_place_linear_data : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] [StarRing OE] (cp : O), HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp → ∀ (g : ℕ) (H : HodgeTateDatum p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (d r m : ℕ) (A : Matrix (Fin d) (Fin r) O) (B : Matrix (Fin g) (Fin d) O) (ρG : OE →+* Matrix (Fin d) (Fin d) O) (N : OE →+* Matrix (Fin r) (Fin r) ℤ) (s : Fin m → Fin d → O), LinDat H A B ρG N s → ∀ (w : Place p OE) (t : Fin w.n ≃ Emb (O := O) w.e) (vd : ℝ), HasVd p v w t vd → ∀ (rp rm : ℕ) (W : Fin w.n → Fin rp → Fin d → O), (∀ j, EigB ρG ((t j : Emb (O := O) w.e) : OE →+* O) (W j)) → (∀ τ ∈ Emb (O := O) w.bar, ∃ W' : Fin rm → Fin d → O, EigB ρG τ W') → ∃ xs : Fin w.n → NNReal, (∀ j, HasLen v O ((Fin rp → O) ⧸ Submodule.span O (Set.range fun k => Pdiv.ChartF.res (W j) (s k))) (xs j)) ∧ v (algebraMap O C (p : O)) ^ ((w.n : ℝ) * rm * (1 / ((p : ℝ) - 1) + vd / 2)) ≤ ∏ j, xs j := by
  first | exact @GlobalTheory.ChF.colength_bound_linDat | exact GlobalTheory.ChF.colength_bound_linDat | (intros; apply GlobalTheory.ChF.colength_bound_linDat <;> assumption)
end
