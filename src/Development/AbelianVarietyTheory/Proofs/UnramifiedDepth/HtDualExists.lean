module

public import ReciprocityTheory.DualLattices.SubMemOfCompat
public import ReciprocityTheory.DualLattices.CharR
public import ReciprocityTheory.DualLattices.ThmAAll
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ChainLemmaMultivariatePowerSeriesCoordinateForm
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FormalGroupCoordinatesPullbackLinearTangentBasis
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NabValColumnsCongr

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HtDualExists
noncomputable section

open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2

namespace GlobalTheory

private def htDualRing {R₀ : Type} [CommRing R₀] {Λ S : LAlg R₀} (Dq : DualPair S) (ψ : LHom Λ S) :
    DualNum.DN Λ →+* (Dq.D : Type) :=
  Ideal.Quotient.lift _
    (Polynomial.eval₂RingHom ((Dq.σ.1.comp ψ.1 : (Λ : Type) →ₐ[R₀] (Dq.D : Type)) :
      (Λ : Type) →+* (Dq.D : Type)) Dq.η) (fun a ha => by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, map_pow, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, sq, Dq.η_sq, mul_zero])

private lemma htDualRing_C {R₀ : Type} [CommRing R₀] {Λ S : LAlg R₀} (Dq : DualPair S)
    (ψ : LHom Λ S) (r : (Λ : Type)) :
    htDualRing Dq ψ (Ideal.Quotient.mk _ (Polynomial.C r)) = Dq.σ.1 (ψ.1 r) := by
  rw [htDualRing, Ideal.Quotient.lift_mk, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
  rfl

private lemma htDualRing_X {R₀ : Type} [CommRing R₀] {Λ S : LAlg R₀} (Dq : DualPair S)
    (ψ : LHom Λ S) : htDualRing Dq ψ (DualNum.eta Λ) = Dq.η := by
  rw [htDualRing, DualNum.eta, Ideal.Quotient.lift_mk, Polynomial.coe_eval₂RingHom,
    Polynomial.eval₂_X]

private lemma htDualRing_π {R₀ : Type} [CommRing R₀] {Λ S : LAlg R₀} (Dq : DualPair S)
    (ψ : LHom Λ S) (x : DualNum.DN Λ) :
    Dq.π.1 (htDualRing Dq ψ x) = ψ.1 (DualNum.ev Λ x) := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  induction f using Polynomial.induction_on with
  | C a => rw [htDualRing_C, Dq.sect, DualNum.ev_mk, Polynomial.eval_C]
  | add f g hf hg => simp only [map_add (f := _), hf, hg]
  | monomial n a _ =>
    have h := htDualRing_X Dq ψ
    rw [DualNum.eta] at h
    rw [DualNum.ev_mk, pow_succ Polynomial.X n, ← mul_assoc, map_mul, map_mul, h, map_mul, Dq.π_η]
    simp

private lemma htDual_exists {R₀ : Type} [CommRing R₀] {Λ S : LAlg R₀} (Dq : DualPair S)
    (ψ : LHom Λ S) :
    ∃ f : LHom (DualNum.dualPair Λ).D Dq.D,
      (∀ x, Dq.π.1 (f.1 x) = ψ.1 ((DualNum.dualPair Λ).π.1 x)) ∧
      (∀ x, f.1 ((DualNum.dualPair Λ).σ.1 x) = Dq.σ.1 (ψ.1 x)) ∧
      f.1 (DualNum.dualPair Λ).η = Dq.η := by
  let fA : DualNum.DN Λ →ₐ[R₀] (Dq.D : Type) :=
    { htDualRing Dq ψ with
      commutes' := fun r => by
        show htDualRing Dq ψ (algebraMap R₀ (DualNum.DN Λ) r) = _
        rw [← Ideal.Quotient.mk_algebraMap, Polynomial.algebraMap_apply, htDualRing_C,
          AlgHom.commutes, AlgHom.commutes] }
  refine ⟨mkLHom (R := (DualNum.dualPair Λ).D) fA fun a ha => ?_, fun x => htDualRing_π Dq ψ x,
    fun x => ?_, htDualRing_X Dq ψ⟩
  · refine (DualNum.dualPair Λ).isUnit_of_π ?_
    have h1 : IsUnit (Dq.π.1 (htDualRing Dq ψ a)) := ha.map Dq.π.1
    exact ψ.2.map_nonunit _ ((htDualRing_π Dq ψ a) ▸ h1)
  · show htDualRing Dq ψ (algebraMap (Λ : Type) (DualNum.DN Λ) x) = _
    rw [← Ideal.Quotient.mk_algebraMap, Polynomial.algebraMap_apply, htDualRing_C]
    rfl

private lemma ht_padic_val {p : ℕ} [Fact p.Prime] (a : ℤ_[p]) :
    ∃ b : ℤ_[p], a - ((PadicInt.toZMod a).val : ℤ_[p]) = p * b := by
  have h : a - ((PadicInt.toZMod a).val : ℤ_[p]) ∈ RingHom.ker (PadicInt.toZMod (p := p)) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at h
  obtain ⟨b, hb⟩ := h
  exact ⟨b, by rw [← hb, mul_comm]⟩

theorem evHt_of_lam :
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw} [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe} {cp : (Tw.O : Type)} (D : Dat p g B Tw Dt Oe σ cp), 0 < g → maximalIdeal (D.K : Type) = ⊥ ∧ IsNilOver D.wd.ρ1 ∧ ∀ i : D.fin.ι,
    ∃ (Λ : LAlg R₀) (μ : LHom (D.fin.AAx i) Λ) (j : LHom (Tw.R 0) Λ) (ρΛ : LHom Λ D.K),
      IsNilOver ρΛ ∧ Function.Surjective μ.1 ∧ ρΛ.comp j = D.wd.ρ1 ∧ μ.comp (D.fin.sO i) = j.comp (Tw.q 0) ∧
      ∀ φ : LHom (D.fin.AAx i) Tw.O, φ.comp (D.fin.sO i) = LHom.id Tw.O →
        ∃ ψ : LHom Λ (Tw.R 0), ψ.comp μ = (Tw.q 0).comp φ ∧ ψ.comp j = LHom.id (Tw.R 0) ∧ D.wd.ρ1.comp ψ = ρΛ) →
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw} [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe} {cp : (Tw.O : Type)} (D : Dat p g B Tw Dt Oe σ cp), EvHtStatement D) := by
  intro hLam R₀ _ p _ g B Tw Dt _ Oe _ _ σ cp D C _ _ k
  have hg : 0 < g := Nat.zero_lt_of_lt k.2
  obtain ⟨-, -, hL⟩ := hLam D hg
  clear hLam
  choose Λ μ j ρΛ _ hμ _ _ hψ using hL
  have hB1 := pairingProperties B
  have hchar := Tw.toATower.char_R 0
  have hcharΛ : ∀ i, ((p ^ (0 + 1) : ℕ) : (Λ i : Type)) = 0 := fun i => by
    rw [← map_natCast (j i).1, hchar, map_zero]
  have hy : ∀ i, (p ^ (0 + 1)) • B.map (μ i) (D.fin.y i) = 0 := fun i => by
    rw [← map_nsmul, zero_add, pow_one, D.fin.y_p, map_zero]
  choose h hh using fun i =>
    B.isHeight_exists hB1 (DualNum.dualPair (Λ i)) (p ^ (0 + 1)) (hcharΛ i) _ (hy i)
  choose F hF using fun i => hμ i (h i (D.ch.gb k))
  refine ⟨D.evAll C F, Submodule.subset_span ⟨F, rfl⟩, fun t => ?_⟩
  obtain ⟨hs, hyt, -⟩ := Classical.choose_spec (Classical.choose_spec
    (D.fin.univ Tw.O (LHom.id Tw.O) (ptOf B D.L.τ (red p g t)) (D.pt_p (red p g t))))
  change (D.ptMap (red p g t)).comp (D.fin.sO (D.ptIdx (red p g t))) = LHom.id Tw.O at hs
  change B.map (D.ptMap (red p g t)) (D.fin.y (D.ptIdx (red p g t))) = ptOf B D.L.τ (red p g t) at hyt
  obtain ⟨ψ, hψμ, -, -⟩ := hψ _ _ hs
  obtain ⟨f, f1, f2, f3⟩ := htDual_exists (Dt.Dp 0) ψ
  have H1 := B.isHeight_map hB1 _ _ ψ f f1 f2 f3 _ _ _ (hh (D.ptIdx (red p g t)))
  rw [← B.map_comp, hψμ, B.map_comp, hyt] at H1
  choose b hb using fun i => ht_padic_val (t i)
  have hp0 : ((p : ℕ) : (Tw.R 0 : Type)) = 0 := by simpa using hchar
  have hy2 : ∀ i, (p ^ (0 + 1)) • B.map (Tw.q 0) (D.L.τ i 0) = 0 := fun i => by
    rw [← map_nsmul, D.L.τ_tors, map_zero]
  have H2 := B.isHeight_sum hB1 (Dt.Dp 0) _ hchar Finset.univ
    (fun i => (((red p g t i).val : ℕ) : ℤ) • B.map (Tw.q 0) (D.L.τ i 0))
    (fun i => by rw [smul_comm, hy2, smul_zero]) _
    (fun i => B.isHeight_zsmul hB1 (Dt.Dp 0) _ hchar (hy2 i) (D.L.ht_spec i 0) _)
  have e1 : ∑ i, (((red p g t i).val : ℕ) : ℤ) • B.map (Tw.q 0) (D.L.τ i 0) =
      B.map (Tw.q 0) (ptOf B D.L.τ (red p g t)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [ptOf, map_sum, map_nsmul, natCast_zsmul]
  rw [e1] at H2
  have hyp : (p ^ (0 + 1)) • B.map (Tw.q 0) (ptOf B D.L.τ (red p g t)) = 0 := by
    rw [← map_nsmul, zero_add, pow_one, D.pt_p, map_zero]
  have hU := LinearMap.congr_fun (B.isHeight_unique hB1 _ _ hchar _ hyp _ _ H1 H2) (D.ch.gb k)
  have hmem : (D.H.Ht *ᵥ (algebraMap ℤ_[p] (Tw.O : Type) ∘ t)) k -
      (D.ptMap (red p g t)).1 (F (D.ptIdx (red p g t))) ∈ RingHom.ker (Tw.q 0).1 := by
    rw [RingHom.mem_ker, map_sub, sub_eq_zero]
    have e2 : (Tw.q 0).1 ((D.ptMap (red p g t)).1 (F (D.ptIdx (red p g t)))) =
        ψ.1 (h (D.ptIdx (red p g t)) (D.ch.gb k)) := by
      rw [← hF]
      exact (congrArg (fun u : LHom _ _ => u.1 (F (D.ptIdx (red p g t)))) hψμ).symm
    rw [e2]
    refine Eq.trans ?_ hU.symm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [LinearMap.sum_apply, Matrix.mulVec, dotProduct, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e3 : t i = ((red p g t i).val : ℤ_[p]) + p * b i := by
      rw [← hb i]
      show t i = ((PadicInt.toZMod (t i)).val : ℤ_[p]) + _
      ring
    rw [D.L.Ht_eq, Function.comp_apply, e3]
    rw [map_add (f := _), map_mul (algebraMap ℤ_[p] (Tw.O : Type)), map_natCast, map_natCast, map_mul, map_add (f := _),
      map_mul (Tw.q 0).1, map_natCast, map_natCast, hp0, zero_mul, add_zero, natCast_zsmul,
      LinearMap.smul_apply, nsmul_eq_mul, mul_comm]
    rfl
  rw [D.tower_zero_ker, Ideal.mem_span_singleton'] at hmem
  obtain ⟨r, hr⟩ := hmem
  refine ⟨r, ?_⟩
  rw [Dat.evAll, ← map_sub, ← hr, mul_comm]

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LeafCoordinateWeightNonnegOfAdaptedChainData
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LeafCoordinateWeightNonnegOfAdaptedChainData
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
open Formalism.BaseCaseIdentities (Data Kn s0)
open ReciprocityTheory.PGsh (OrdGe lgSum)

namespace GlobalTheory.LeafCoordWeight

theorem chain_data {C : Type} [Field C] [CharZero C] {Z I : Type} [Fintype I] (D : Data C Z I)
    {N : ℕ} (em : Fin N → I) (hem : ∀ δ, D.lev (em δ) = 0) (t : I → MvPowerSeries (Fin N) C)
    (ht : ∀ c, MvPowerSeries.constantCoeff (t c) = 0)
    (hz : ∀ (b : I) (μ : Fin N →₀ ℕ), ∑ s ∈ Finset.range (μ.degree + 1), ∑ c,
      (if s = 0 then (if c = b then 1 else 0) else D.al c s b) *
        MvPowerSeries.coeff μ (t c ^ (D.l ^ s)) =
      MvPowerSeries.coeff μ (∑ j, MvPowerSeries.C (R := C) (if b = em j then 1 else 0) *
        (MvPowerSeries.X j : MvPowerSeries (Fin N) C))) :
    (∀ c, D.lev c < Kn D.i →
      OrdGe D.v (fun _ => 1 / ((D.l : ℝ) ^ 2 - 1) + 3 / (8 * (D.l : ℝ) ^ D.i))
        (t c - ∑ j, MvPowerSeries.C (R := C)
          (GlobalTheory.ChainCoord.kap C D.l (D.lev c) * chainMat D (D.lev c) c (em j)) *
          (MvPowerSeries.X j : MvPowerSeries (Fin N) C) ^ ((D.l ^ 2) ^ D.lev c))
        (1 + 1 / ((D.l : ℝ) ^ 2 - 1))) ∧
    ∀ c, ¬ D.lev c < Kn D.i →
      OrdGe D.v (fun _ => 1 / ((D.l : ℝ) ^ 2 - 1) + 3 / (8 * (D.l : ℝ) ^ D.i)) (t c)
        (1 + 1 / ((D.l : ℝ) ^ 2 - 1)) := by
  obtain ⟨ε⟩ : Nonempty (Fin (Fintype.card I) ≃ I) := ⟨(Fintype.equivFin I).symm⟩
  have hK := Kn_eq D.i_odd
  have hl0 : (D.l : C) ≠ 0 := by exact_mod_cast D.l_prime.ne_zero
  have key := GlobalTheory.ChainCoord.chain C D.v D.l D.l_prime D.v_l D.l_ge (Fintype.card I) N (s0 D.i)
    {c | D.good (ε c)}
    (fun s => Finset.univ.filter fun c => D.lev (ε c) = s ∧ s < Kn D.i)
    (fun c s b => if s = 0 then (if ε c = ε b then 1 else 0) else D.al (ε c) s (ε b))
    (fun s e j => chainMat D s (ε e) (em j)) (fun c => t (ε c))
    (fun s c hc => by
      obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 hc).2
      exact D.pure_good _ (h1 ▸ h2))
    (fun s s' c _ _ hc hc' =>
      (Finset.mem_filter.1 hc).2.1.symm.trans (Finset.mem_filter.1 hc').2.1)
    (fun c e => by simp)
    (fun c n e => by
      by_cases hn : n = 0
      · subst hn
        by_cases h : ε c = ε e <;> simp [h]
      · simp only [if_neg hn]
        exact D.al_all _ _ _)
    (fun c hc => ⟨by
      funext e
      simpa using D.al_one _ hc (ε e), fun n e hn => by
      simp only [if_neg (show n ≠ 0 by omega)]
      have := D.al_good _ hc n (ε e) hn
      rwa [neg_sub] at this⟩)
    (fun s hs c hc e he => by
      obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 hc).2
      have h3 : D.lev (ε e) ≠ D.lev (ε c) + 1 := fun h =>
        he (Finset.mem_filter.2 ⟨Finset.mem_univ _, by omega, by omega⟩)
      simp only [if_neg (show (2 : ℕ) ≠ 0 by omega)]
      rw [D.al_two _ (by omega), D.g_supp _ (by omega) _ h3, zero_add, inv_mul_cancel_left₀ hl0]
      exact D.lam_int _ _)
    (fun c j => by
      simp only [chainMat_zero]
      split_ifs <;> simp)
    (fun c hc => by
      funext j
      simp only [chainMat_zero, Pi.zero_apply]
      refine if_neg fun h => hc (Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_, by omega⟩)
      rw [h, hem])
    (fun s e j => by
      simp only [chainMat_succ, if_neg (show (2 : ℕ) ≠ 0 by omega)]
      rw [Finset.sum_filter, Finset.sum_filter, ← ε.sum_comp])
    (fun c => ht _)
    (fun e => by
      ext μ
      refine Eq.trans ?_ (hz (ε e) μ)
      change ∑ n ∈ Finset.range (Finsupp.degree μ + 1), ∑ a, _ = _
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [← ε.sum_comp])
  rw [two_mul_chainStartIndex_add_one_of_odd D.i_odd] at key
  refine ⟨fun c hc => ?_, fun c hc => ?_⟩
  · obtain ⟨c, rfl⟩ := ε.surjective c
    exact key.1 _ (by omega) c (Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl, hc⟩)
  · obtain ⟨c, rfl⟩ := ε.surjective c
    refine key.2 c fun s _ h => hc ?_
    obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 h).2
    omega

theorem wtGe1_of_ordGe {C : Type} [Field C] {V : VF C} {i N : ℕ} {w : ℝ}
    {f : MvPowerSeries (Fin N) C}
    (h : OrdGe V.v (fun _ => 1 / ((V.l : ℝ) ^ 2 - 1) + 3 / (8 * (V.l : ℝ) ^ i)) f w) :
    WtGe1 V i w f := by
  intro μ
  have h1 : r1 V.l i - del V.l i = 1 / ((V.l : ℝ) ^ 2 - 1) + 3 / (8 * (V.l : ℝ) ^ i) := by
    have : (V.l : ℝ) ≠ 0 := by exact_mod_cast V.l_prime.ne_zero
    have h3 : 1 / (2 * (V.l : ℝ) ^ i) - 1 / (8 * (V.l : ℝ) ^ i) = 3 / (8 * (V.l : ℝ) ^ i) := by
      field_simp
      ring
    rw [← h3]
    unfold r1 del rho
    ring
  have h2 : (μ.degree : ℝ) = ∑ m, (μ m : ℝ) := by
    rw [Finsupp.degree_eq_sum]
    push_cast
    rfl
  refine le_trans ?_ (add_le_add (h μ) le_rfl)
  rw [← WithTop.coe_add, h1, h2, ← Finset.mul_sum]
  exact WithTop.coe_le_coe.2 (le_of_eq (by ring))

theorem weight_nonneg : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (d : ℕ) [NeZero d] (I J : Type) [Fintype I] [Fintype J] (G : Cart V d I J) (S : Sys G) (Z : Type) (D : Formalism.BaseCaseIdentities.Data C Z I) (a : ZMod d) (i : ℕ), Adapted S D a i → ∀ t : I → MvPowerSeries I C, S.IsT t → ∀ (N : ℕ) (em : Fin N → I), (∀ δ, D.lev (em δ) = 0) → ∀ c, WtGe1 V i 0 (linPull (fun δ => S.tan (em δ)) (t c)) := by
  intro C _ _ V d _ I J _ _ G S Z D a i h t ht N em hem c
  obtain ⟨h1, h2, -⟩ := GlobalTheory.MainTerm.linPull_coords C V d I J G S t ht (Fin N) (fun δ => S.tan (em δ))
    (fun b j => if b = em j then 1 else 0)
    (fun c s b => if s = 0 then (if c = b then 1 else 0) else D.al c s b)
    (fun j x => by simp) (fun c b => by simp)
    (fun c k x hk => by
      simp only [if_neg (show k ≠ 0 by omega)]
      exact h.2.2.2.1 c k x hk)
  rw [← h.2.1] at h2
  obtain ⟨k1, k2⟩ := chain_data D em hem _ h1 h2
  have h3 : (3 : ℝ) ≤ D.l := by exact_mod_cast D.l_ge
  have hq : 0 < (D.l : ℝ) ^ 2 - 1 := by nlinarith
  have hρ : 0 < 1 / ((D.l : ℝ) ^ 2 - 1) := by positivity
  apply wtGe1_of_ordGe
  rw [← h.1, ← h.2.1, ← h.2.2.1]
  by_cases hc : D.lev c < Kn D.i
  · have hint : ∀ j, ((0 : ℝ) : WithTop ℝ) ≤ D.v (chainMat D (D.lev c) c (em j)) := fun j => by
      rw [h.1]
      exact h.chainMat_int _ _ _
    have hP := GlobalTheory.ChainCoord.ord_pure (v := D.v) fun j =>
      GlobalTheory.ChainCoord.ord_pure_level (σ := 3 / (8 * (D.l : ℝ) ^ D.i)) (s := D.lev c) (c := (0 : Fin 1))
        (π := fun s _ j => chainMat D s c (em j)) D.l_ge D.v_l hint j
    have := GlobalTheory.ChainCoord.ord_add (GlobalTheory.ChainCoord.ord_mono (k1 c hc) (w' := 0) (by linarith))
      (GlobalTheory.ChainCoord.ord_mono hP (w' := 0) (by positivity))
    rwa [sub_add_cancel] at this
  · exact GlobalTheory.ChainCoord.ord_mono (k2 c hc) (by linarith)

end GlobalTheory.LeafCoordWeight
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LeafCoordinateWeightNonnegOfAdaptedChainDataStatement
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leafCoordinate_weight_nonneg_of_adaptedChainData : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (d : ℕ) [NeZero d] (I J : Type) [Fintype I] [Fintype J] (G : Cart V d I J) (S : Sys G) (Z : Type) (D : Formalism.BaseCaseIdentities.Data C Z I) (a : ZMod d) (i : ℕ), Adapted S D a i → ∀ t : I → MvPowerSeries I C, S.IsT t → ∀ (N : ℕ) (em : Fin N → I), (∀ δ, D.lev (em δ) = 0) → ∀ c, WtGe1 V i 0 (linPull (fun δ => S.tan (em δ)) (t c)) := by
  first | exact @GlobalTheory.LeafCoordWeight.weight_nonneg | exact GlobalTheory.LeafCoordWeight.weight_nonneg | (intros; apply GlobalTheory.LeafCoordWeight.weight_nonneg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PSerFrobOfInvariance
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2

namespace GlobalTheory

private lemma pSerOf_trunc {R₀ : Type} [CommRing R₀] {g : ℕ} (N : ℕ) (G₁ : MvPolynomial (Fin g) R₀) :
    ∃ G : MvPolynomial (Fin g) R₀,
      (∀ m, AddMonoidAlgebra.coeff G m = if ∀ i, m i < N then AddMonoidAlgebra.coeff G₁ m else 0) ∧
      ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a : Fin g → S), (∀ i, a i ^ N = 0) →
        MvPolynomial.aeval a G = MvPolynomial.aeval a G₁ := by
  classical
  refine ⟨∑ m ∈ G₁.support.filter (fun m => ∀ i, m i < N),
    MvPolynomial.monomial m (AddMonoidAlgebra.coeff G₁ m), ?_, ?_⟩
  · intro m
    rw [MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_monomial]
    rw [Finset.sum_ite_eq']
    by_cases h : ∀ i, m i < N
    · by_cases h0 : AddMonoidAlgebra.coeff G₁ m = 0
      · simp [h0]
      · simp [h, h0]
    · rw [if_neg h, if_neg]
      intro hm
      exact h (Finset.mem_filter.1 hm).2
  · intro S _ _ a ha
    conv_rhs => rw [G₁.as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun m _ => ?_
    split_ifs with h
    · rfl
    · push Not at h
      obtain ⟨i, hi⟩ := h
      have hz : ∏ j, a j ^ m j = 0 :=
        Finset.prod_eq_zero (f := fun j => a j ^ m j) (Finset.mem_univ i)
          (pow_eq_zero_of_le hi (ha i))
      rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (by simp), hz, mul_zero]

theorem pSerFrob_of_invariance :
  (∀ {R₀ : Type} [CommRing R₀] {ι : Type} [Fintype ι] [DecidableEq ι] (f : MvPowerSeries ι R₀) (S : Type) [CommRing S] [Algebra R₀ S] (a : ι → S),
    (∀ N : ℕ, (∀ i, a i ^ N = 0) → nEval f a = tEval N f a) ∧
    ((∀ i, IsNilpotent (a i)) → (∀ (S' : Type) [CommRing S'] [Algebra R₀ S'] (φ : S →ₐ[R₀] S'), φ (nEval f a) = nEval f (fun i => φ (a i))) ∧
      nEval f a - algebraMap R₀ S (MvPowerSeries.coeff 0 f) ∈ Ideal.span (Set.range a))) →
  (∀ {R₀ : Type} [CommRing R₀] {g : ℕ} {B : BX R₀} {K : LAlg R₀} (ch : FormalChartAtZero B K g) (n : ℕ) (S : Type) [CommRing S] [Algebra R₀ S], (n : S) = 0 → ∀ a e : Fin g → S, (∀ i, IsNilpotent (a i)) →
    (∀ i j, e i * e j = 0) → nsmulF ch.F (a + e) n = nsmulF ch.F a n) →
  (∀ {R₀ : Type} [CommRing R₀] (p : ℕ) [Fact p.Prime] (g N : ℕ) (G : MvPolynomial (Fin g) R₀),
    (∀ (S : Type) [CommRing S] [Algebra R₀ S], (p : S) = 0 → ∀ a e : Fin g → S, (∀ i, a i ^ N = 0) → (∀ i j, e i * e j = 0) →
      MvPolynomial.aeval (a + e) G = MvPolynomial.aeval a G) →
    ∀ m : Fin g →₀ ℕ, (∀ i, m i < N) → (∃ i, ¬ p ∣ m i) → ∃ r : R₀, AddMonoidAlgebra.coeff G m = p * r) →
  (∀ {R₀ : Type} [CommRing R₀] (p : ℕ) [Fact p.Prime] {g : ℕ} {B : BX R₀} (K : LAlg R₀) (ch : FormalChartAtZero B K g), PSerFrobStatement p K ch) := by
  intro hev hinv hcoef R₀ _ p _ g B K ch N
  classical

  have hnil : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a b : Fin g → S),
      (∀ i, IsNilpotent (a i)) → (∀ i, IsNilpotent (b i)) → ∀ k, IsNilpotent (fAdd ch.F a b k) := by
    intro S _ _ a b ha hb k
    have h0 : algebraMap R₀ S (MvPowerSeries.coeff 0 (ch.F k)) = 0 := by
      have h1 := ((hev (ch.F k) S (Sum.elim (0 : Fin g → S) (0 : Fin g → S))).2
        (by rintro (i | i) <;> simp)).2
      have h2 : nEval (ch.F k) (Sum.elim (0 : Fin g → S) (0 : Fin g → S)) = 0 :=
        congrFun (ch.F_unit S 0 (by simp)) k
      have h3 : Ideal.span (Set.range (Sum.elim (0 : Fin g → S) (0 : Fin g → S))) = ⊥ := by
        rw [Ideal.span_eq_bot]
        rintro _ ⟨i | i, rfl⟩ <;> simp
      rw [h2, h3, Ideal.mem_bot, zero_sub, neg_eq_zero] at h1
      exact h1
    have h1 := ((hev (ch.F k) S (Sum.elim a b)).2 (by rintro (i | i); exacts [ha i, hb i])).2
    rw [h0, sub_zero] at h1
    have h2 : Ideal.span (Set.range (Sum.elim a b)) ≤ nilradical S := by
      rw [Ideal.span_le]
      rintro _ ⟨i | i, rfl⟩
      exacts [mem_nilradical.2 (ha i), mem_nilradical.2 (hb i)]
    exact mem_nilradical.1 (h2 h1)
  have hnil' : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a : Fin g → S),
      (∀ i, IsNilpotent (a i)) → ∀ n k, IsNilpotent (nsmulF ch.F a n k) := by
    intro S _ _ a ha n
    induction n with
    | zero => intro k; simp [nsmulF]
    | succ n ih => exact hnil S _ _ ih ha
  have hnat : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S']
      (φ : S →ₐ[R₀] S') (a : Fin g → S), (∀ i, IsNilpotent (a i)) → ∀ n k,
      φ (nsmulF ch.F a n k) = nsmulF ch.F (fun i => φ (a i)) n k := by
    intro S _ _ S' _ _ φ a ha n
    induction n with
    | zero => intro k; simp [nsmulF]
    | succ n ih =>
      intro k
      have h1 := ((hev (ch.F k) S (Sum.elim (nsmulF ch.F a n) a)).2
        (by rintro (i | i); exacts [hnil' S a ha n i, ha i])).1 S' φ
      change φ (nEval (ch.F k) (Sum.elim (nsmulF ch.F a n) a)) =
        nEval (ch.F k) (Sum.elim (nsmulF ch.F (fun i => φ (a i)) n) (fun i => φ (a i)))
      rw [h1]
      congr 1
      funext i
      rcases i with i | i
      · exact ih i
      · rfl

  let I : Ideal (MvPolynomial (Fin g) R₀) :=
    Ideal.span (Set.range fun j : Fin g => (MvPolynomial.X j : MvPolynomial (Fin g) R₀) ^ (N + 1))
  let x : Fin g → MvPolynomial (Fin g) R₀ ⧸ I := fun j => Ideal.Quotient.mk I (MvPolynomial.X j)
  have hx : ∀ j, IsNilpotent (x j) := fun j => ⟨N + 1, by
    change Ideal.Quotient.mk I (MvPolynomial.X j) ^ (N + 1) = 0
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span ⟨j, rfl⟩⟩
  choose G₁ hG₁ using fun k => Ideal.Quotient.mk_surjective (nsmulF ch.F x p k)
  have huniv : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a : Fin g → S),
      (∀ i, a i ^ (N + 1) = 0) → ∀ k, nsmulF ch.F a p k = MvPolynomial.aeval a (G₁ k) := by
    intro S _ _ a ha k
    let φ : (MvPolynomial (Fin g) R₀ ⧸ I) →ₐ[R₀] S :=
      Ideal.Quotient.liftₐ I (MvPolynomial.aeval a) (by
        intro f hf
        have : I ≤ RingHom.ker (MvPolynomial.aeval a : MvPolynomial (Fin g) R₀ →ₐ[R₀] S) := by
          rw [Ideal.span_le]
          rintro _ ⟨j, rfl⟩
          simp [RingHom.mem_ker, ha j]
        exact this hf)
    have hφ : ∀ f, φ (Ideal.Quotient.mk I f) = MvPolynomial.aeval a f := fun f => rfl
    have h1 := hnat _ S φ x hx p k
    have h2 : (fun i => φ (x i)) = a := by
      funext i
      change φ (Ideal.Quotient.mk I _) = _
      rw [hφ, MvPolynomial.aeval_X]
    rw [h2, ← hG₁ k, hφ] at h1
    exact h1.symm
  choose G hG hGe using fun k => pSerOf_trunc N (G₁ k)
  refine ⟨G, ?_, ?_⟩
  · intro k m hm
    rw [hG]
    split_ifs with h
    · refine hcoef p g N (G₁ k) ?_ m h hm
      intro S _ _ hp a e ha he
      have h1 : ∀ i, (a + e) i ^ (N + 1) = 0 := fun i =>
        (Commute.all (a i) (e i)).add_pow_eq_zero_of_add_le_succ_of_pow_eq_zero (ha i)
          (show e i ^ 2 = 0 by rw [sq, he]) (by omega)
      have h2 : ∀ i, a i ^ (N + 1) = 0 := fun i => by rw [pow_succ, ha i, zero_mul]
      rw [← huniv S _ h1, ← huniv S _ h2, hinv ch p S hp a e (fun i => ⟨N, ha i⟩) he]
    · exact ⟨0, by simp⟩
  · intro S _ _ a ha
    funext k
    rw [hGe k S a ha]
    exact huniv S a (fun i => by rw [pow_succ, ha i, zero_mul]) k

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ConstantCoeffDmonOfEigen
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.CharacterColumns

theorem dof_zero_dir {R : Type} [CommRing R] {d : ℕ} (F : Fin d → PS R 2 d) (f : PS R 1 d) :
    Dof F 0 f = 0 := by
  simp [Dof]

theorem dmonOf_congr_dir {R : Type} [CommRing R] {d : ℕ} (F : Fin d → PS R 2 d) {ι : Type}
    [Fintype ι] (u u' : ι → Fin d → R) (mo : ι →₀ ℕ) (hu : ∀ l, mo l ≠ 0 → u l = u' l)
    (f : PS R 1 d) : DmonOf F u mo f = DmonOf F u' mo f := by
  unfold DmonOf
  congr 1
  funext l g
  by_cases hl : mo l = 0
  · rw [hl]; rfl
  · rw [hu l hl]

theorem nabVal_congr_dir {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
    {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d) (w0 : O)
    (m : ℕ) (f : PS k 1 d) {ι : Type} [Fintype ι] (u u' : ι → Fin d → k) (mo : ι →₀ ℕ)
    (hu : ∀ l, mo l ≠ 0 → u l = u' l) :
    B.nabVal k h w0 m f u (MvPolynomial.monomial mo 1) =
      B.nabVal k h w0 m f u' (MvPolynomial.monomial mo 1) := by
  unfold FB.nabVal
  rw [PullbackColumn.dpolyOf_monomial_one, PullbackColumn.dpolyOf_monomial_one,
    dmonOf_congr_dir _ u u' mo hu]

theorem constantCoeff_dmonOf_eigen {R : Type} [CommRing R] {d : ℕ} (F : Fin d → PS R 2 d) {ι : Type}
    [Fintype ι] (u : ι → Fin d → R) (S : Set ι) (χ : PS R 1 d) (y : ι → R)
    (h1 : constantCoeff χ = 1) (hχ : ∀ l ∈ S, Dof F (u l) χ = C (y l) * χ) (mo : ι →₀ ℕ)
    (hmo : ∀ l, mo l ≠ 0 → l ∈ S) :
    constantCoeff (DmonOf F (S.indicator u) mo χ) = ∏ l, y l ^ mo l := by
  have key := constantCoeff_dmonOf_sub_mem R d F ⊥ ι (S.indicator u) (S.indicator y) χ (by
    intro l mo'
    by_cases hl : l ∈ S
    · rw [Set.indicator_of_mem hl, Set.indicator_of_mem hl, hχ l hl, sub_self, map_zero]
      exact Ideal.zero_mem _
    · rw [Set.indicator_of_notMem hl, Set.indicator_of_notMem hl, dof_zero_dir, map_zero, zero_mul,
        sub_self, map_zero]
      exact Ideal.zero_mem _) mo
  rw [Ideal.mem_bot, sub_eq_zero, h1, mul_one] at key
  rw [key]
  refine Finset.prod_congr rfl fun l _ => ?_
  by_cases hl : mo l = 0
  · rw [hl, pow_zero, pow_zero]
  · rw [Set.indicator_of_mem (hmo l hl)]

end GlobalTheory.CharacterColumns

namespace GlobalTheory

open CharacterColumns

theorem nabVal_character_columns :
  (∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h → Function.Injective (algebraMap R k) → ∀ (w0 a c : O) (N m : ℕ) (I : Ideal R), star a * a = (N : O) * c → (N : R) ∈ I →
    ∀ (ι : Type) [Fintype ι] (u : ι → Fin d → R) (α : ι → R), (∀ l, α l - 1 ∈ I) → (∀ l, IsUnit (α l)) →
    (∀ l, (dAct k B a).mulVec (fun i => algebraMap R k (u l i)) = algebraMap R k (α l) • (fun i => algebraMap R k (u l i))) →
    (∀ l l', dotProduct (fun i => algebraMap R k (u l i)) ((bilinPart k h).mulVec ((dAct k B (c * w0)).mulVec (fun i => algebraMap R k (u l' i)))) ∈ (algebraMap R k).range) →
    ∀ χ : PS R 1 d, ∃ g : PS R 1 d, ∀ mo : ι →₀ ℕ, ∃ r ∈ I,
      B.nabVal k h w0 m (FB.toK k g) (fun l i => algebraMap R k (u l i)) (MvPolynomial.monomial mo 1) =
        algebraMap R k (constantCoeff (DmonOf B.G.F u mo χ) + r)) →
  (∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h → Function.Injective (algebraMap R k) → ∀ (w0 : O) (N m n : ℕ) (I : Ideal R), (N : R) ∈ I → ∀ (a c : Fin n → O), (∀ b, star (a b) * a b = (N : O) * c b) →
    ∀ (ι : Type) [Fintype ι] (u : ι → Fin d → R) (S : Fin n → Set ι) (α : Fin n → ι → R), (∀ b, ∀ l ∈ S b, α b l - 1 ∈ I ∧ IsUnit (α b l) ∧
      (dAct k B (a b)).mulVec (fun i => algebraMap R k (u l i)) = algebraMap R k (α b l) • (fun i => algebraMap R k (u l i))) →
    (∀ b, ∀ l ∈ S b, ∀ l' ∈ S b, dotProduct (fun i => algebraMap R k (u l i)) ((bilinPart k h).mulVec ((dAct k B (c b * w0)).mulVec (fun i => algebraMap R k (u l' i)))) ∈ (algebraMap R k).range) →
    ∀ (χ : Fin n → PS R 1 d) (y : ι × Fin n → R), (∀ b, constantCoeff (χ b) = 1) → (∀ b, ∀ l ∈ S b, Dof B.G.F (u l) (χ b) = C (y (l, b)) * χ b) →
    ∀ P : MvPolynomial (ι × Fin n) R, (∀ mo ∈ P.support, ∀ l b, mo (l, b) ≠ 0 → l ∈ S b) →
    ∃ g : Fin n → PS R 1 d, ∃ r ∈ I, ∑ mo ∈ P.support, algebraMap R k (P.coeff mo) *
      ∏ b, B.nabVal k h w0 m (FB.toK k (g b)) (fun l i => algebraMap R k (u l i)) (MvPolynomial.monomial (colM mo b) 1) =
        algebraMap R k (MvPolynomial.eval y P + r)) := by
  intro COL R _ d O _ _ k _ _ _ B h hh hinj w0 N m n I hN a c hac ι _ u S α hα hβ χ y h1 hχ P hP
  classical
  have hcol : ∀ b, ∃ g : PS R 1 d, ∀ mo : ι →₀ ℕ, (∀ l, mo l ≠ 0 → l ∈ S b) → ∃ s : R,
      s - ∏ l, y (l, b) ^ mo l ∈ I ∧
      B.nabVal k h w0 m (FB.toK k g) (fun l i => algebraMap R k (u l i))
        (MvPolynomial.monomial mo 1) = algebraMap R k s := by
    intro b
    have hz : (fun i => algebraMap R k ((0 : Fin d → R) i)) = 0 := by
      funext i; simp
    obtain ⟨g, hg⟩ := COL R d O k B h hh hinj w0 (a b) (c b) N m I (hac b) hN ι ((S b).indicator u)
      (fun l => if l ∈ S b then α b l else 1)
      (by
        intro l
        by_cases hl : l ∈ S b
        · rw [if_pos hl]; exact (hα b l hl).1
        · rw [if_neg hl, sub_self]; exact I.zero_mem)
      (by
        intro l
        by_cases hl : l ∈ S b
        · rw [if_pos hl]; exact (hα b l hl).2.1
        · rw [if_neg hl]; exact isUnit_one)
      (by
        intro l
        by_cases hl : l ∈ S b
        · rw [if_pos hl, Set.indicator_of_mem hl]; exact (hα b l hl).2.2
        · rw [Set.indicator_of_notMem hl, hz, Matrix.mulVec_zero, smul_zero])
      (by
        intro l l'
        by_cases hl : l ∈ S b
        · by_cases hl' : l' ∈ S b
          · rw [Set.indicator_of_mem hl, Set.indicator_of_mem hl']; exact hβ b l hl l' hl'
          · rw [Set.indicator_of_notMem hl', hz, Matrix.mulVec_zero, Matrix.mulVec_zero,
              dotProduct_zero]
            exact zero_mem _
        · rw [Set.indicator_of_notMem hl, hz, zero_dotProduct]
          exact zero_mem _)
      (χ b)
    refine ⟨g, fun mo hmo => ?_⟩
    obtain ⟨r, hr, e⟩ := hg mo
    refine ⟨∏ l, y (l, b) ^ mo l + r, by rwa [add_sub_cancel_left], ?_⟩
    rw [constantCoeff_dmonOf_eigen B.G.F u (S b) (χ b) (fun l => y (l, b)) (h1 b) (hχ b) mo hmo] at e
    rw [← e]
    refine nabVal_congr_dir B h w0 m _ _ _ mo fun l hl => ?_
    rw [Set.indicator_of_mem (hmo l hl)]
  choose g hg using hcol
  have hs : ∀ (mo : ι × Fin n →₀ ℕ) (b : Fin n), ∃ s : R, mo ∈ P.support →
      s - ∏ l, y (l, b) ^ mo (l, b) ∈ I ∧
      B.nabVal k h w0 m (FB.toK k (g b)) (fun l i => algebraMap R k (u l i))
        (MvPolynomial.monomial (colM mo b) 1) = algebraMap R k s := by
    intro mo b
    by_cases hmo : mo ∈ P.support
    · obtain ⟨s, hs⟩ := hg b (colM mo b) (fun l hl => hP mo hmo l b hl)
      exact ⟨s, fun _ => hs⟩
    · exact ⟨0, fun h' => absurd h' hmo⟩
  choose s hs using hs
  refine ⟨g, ∑ mo ∈ P.support, P.coeff mo * ∏ b, s mo b - MvPolynomial.eval y P, ?_, ?_⟩
  · rw [MvPolynomial.eval_eq', ← Finset.sum_sub_distrib]
    refine I.sum_mem fun mo hmo => ?_
    rw [← mul_sub]
    refine I.mul_mem_left _ ?_
    rw [Fintype.prod_prod_type_right, ← Ideal.Quotient.eq, map_prod, map_prod]
    exact Finset.prod_congr rfl fun b _ => Ideal.Quotient.eq.2 (hs mo b hmo).1
  · set_option synthInstance.maxHeartbeats 100000 in
    rw [add_sub_cancel, map_sum]
    refine Finset.sum_congr rfl fun mo hmo => ?_
    rw [map_mul, map_prod]
    congr 1
    exact Finset.prod_congr rfl fun b _ => (hs mo b hmo).2

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PairingNsmulRight
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2

noncomputable section

namespace GlobalTheory

namespace SignChar

variable {R₀ : Type} [CommRing R₀]

section Pairing

variable (B : BX R₀) {R : LAlg R₀}

lemma pairing_zero_left (N : ℕ) (y : B.G R) (hy : N • y = 0) : B.IsPairing N 0 y 1 := by
  obtain ⟨z, hz⟩ := B.pairing_exists N 0 y (smul_zero N) hy
  have h2 := B.isPairingValue_add_left N 0 0 y z z hz hz
  rw [add_zero] at h2
  have h3 : z * z = z := B.pairing_unique N 0 y _ _ h2 hz
  have h4 : z = 1 := mul_eq_left.1 h3
  rwa [h4] at hz

lemma pairing_zero_right (N : ℕ) (x : B.G R) (hx : N • x = 0) : B.IsPairing N x 0 1 := by
  have h := B.pairing_sw N 0 x 1 (pairing_zero_left B N x hx)
  rwa [inv_one] at h

lemma pairing_nsmul_left (N : ℕ) (x y : B.G R) (z : (R : Type)ˣ) (h : B.IsPairing N x y z)
    (n : ℕ) : B.IsPairing N (n • x) y (z ^ n) := by
  induction n with
  | zero =>
    rw [zero_nsmul, pow_zero]
    exact pairing_zero_left B N y h.2.1
  | succ n ih =>
    rw [succ_nsmul, pow_succ]
    exact B.isPairingValue_add_left N _ _ _ _ _ ih h

lemma pairing_nsmul_right (N : ℕ) (x y : B.G R) (z : (R : Type)ˣ) (h : B.IsPairing N x y z)
    (n : ℕ) : B.IsPairing N x (n • y) (z ^ n) := by
  induction n with
  | zero =>
    rw [zero_nsmul, pow_zero]
    exact pairing_zero_right B N x h.1
  | succ n ih =>
    rw [succ_nsmul, pow_succ]
    exact B.isPairingValue_add_right N _ _ _ _ _ ih h

lemma pairing_sum_left {ι : Type} (s : Finset ι) (N : ℕ) (x : ι → B.G R) (y : B.G R)
    (z : ι → (R : Type)ˣ) (hy : N • y = 0) (h : ∀ i, B.IsPairing N (x i) y (z i)) :
    B.IsPairing N (∑ i ∈ s, x i) y (∏ i ∈ s, z i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.prod_empty]
    exact pairing_zero_left B N y hy
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact B.isPairingValue_add_left N _ _ _ _ _ (h a) ih

lemma pairing_sum_right {ι : Type} (s : Finset ι) (N : ℕ) (x : B.G R) (y : ι → B.G R)
    (z : ι → (R : Type)ˣ) (hx : N • x = 0) (h : ∀ i, B.IsPairing N x (y i) (z i)) :
    B.IsPairing N x (∑ i ∈ s, y i) (∏ i ∈ s, z i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.prod_empty]
    exact pairing_zero_right B N x hx
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact B.isPairingValue_add_right N _ _ _ _ _ (h a) ih

end Pairing

variable {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw}
  [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe}
  {cp : (Tw.O : Type)}

lemma ptMap_spec (D : Dat p g B Tw Dt Oe σ cp) (t : Nb p g) :
    (D.ptMap t).comp (D.fin.sO (D.ptIdx t)) = LHom.id Tw.O ∧
      B.map (D.ptMap t) (D.fin.y (D.ptIdx t)) = ptOf B D.L.τ t := by
  have h := Classical.choose_spec (Classical.choose_spec
    (D.fin.univ Tw.O (LHom.id Tw.O) (ptOf B D.L.τ t) (D.pt_p t)))
  exact ⟨h.1, h.2.1⟩

lemma toZMod_eq_of_q (a : ℤ_[p]) (k : ℕ)
    (h : (Tw.q 0).1 (algebraMap ℤ_[p] (Tw.O : Type) a) = k) :
    PadicInt.toZMod a = (k : ZMod p) := by
  have h1 : ¬ IsUnit (a - k) := by
    intro hu
    have h2 := (hu.map (algebraMap ℤ_[p] (Tw.O : Type))).map (Tw.q 0).1
    rw [map_sub, map_sub, h, map_natCast, map_natCast, sub_self] at h2
    exact not_isUnit_zero h2
  have h3 : a - k ∈ RingHom.ker (PadicInt.toZMod (p := p)) := by
    rw [PadicInt.ker_toZMod]
    exact h1
  rw [RingHom.mem_ker, map_sub, map_natCast, sub_eq_zero] at h3
  exact h3

lemma pairing_ptOf (D : Dat p g B Tw Dt Oe σ cp) (s t : TT p g) :
    ∃ n : ℕ, (n : ZMod p) = PadicInt.toZMod (pair p g D.H.E s t) ∧
      B.IsPairing p (ptOf B D.L.τ (red p g s)) (ptOf B D.L.τ (red p g t)) (Tw.ζ 0 ^ n) := by
  choose k hk hpair using fun i j => D.L.E_spec i j 0
  simp only [zero_add, pow_one] at hpair
  refine ⟨∑ i, (∑ j, k i j * (red p g t j).val) * (red p g s i).val, ?_, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [pair, dotProduct, mulVec, map_sum, map_mul, Nat.cast_sum, Nat.cast_mul,
      ZMod.natCast_zmod_val, red]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_comm]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [toZMod_eq_of_q _ _ (hk i j)]
  · rw [← Finset.prod_pow_eq_pow_sum]
    refine pairing_sum_left B _ p _ _ _ (D.pt_p _) fun i => ?_
    rw [pow_mul]
    refine pairing_nsmul_left B p _ _ _ ?_ _
    rw [← Finset.prod_pow_eq_pow_sum]
    refine pairing_sum_right B _ p _ _ _ (hpair i i).1 fun j => ?_
    rw [pow_mul]
    exact pairing_nsmul_right B p _ _ _ (hpair i j) _

end SignChar

theorem signChar_mem_evImg :
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw} [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe} {cp : (Tw.O : Type)} (D : Dat p g B Tw Dt Oe σ cp), EvenTwoEvaluationSign D) := by
  intro R₀ _ p _ g B Tw Dt _ Oe _ _ σ cp D C _ _ _ _ hp s
  have hex : ∀ i, ∃ z, B.IsPairing p (B.map (D.fin.sO i) (ptOf B D.L.τ (red p g s)))
      (D.fin.y i) z := fun i =>
    B.pairing_exists p _ _ (by rw [← map_nsmul, D.pt_p, map_zero]) (D.fin.y_p i)
  choose e he using hex
  refine ⟨D.evAll C fun i => (e i : (D.fin.AAx i : Type)), Submodule.subset_span ⟨_, rfl⟩,
    fun t => ?_⟩
  obtain ⟨h1, h2⟩ := SignChar.ptMap_spec D (red p g t)
  have h3 := B.pairing_map (D.ptMap (red p g t)) p _ _ _ (he (D.ptIdx (red p g t)))
  rw [← B.map_comp, h1, B.map_id, h2] at h3
  obtain ⟨n, hn, h4⟩ := SignChar.pairing_ptOf D s t
  have h5 := congrArg Units.val (B.pairing_unique p _ _ _ _ h3 h4)
  rw [Units.val_pow_eq_pow_val, D.zeta0 hp, Units.coe_map] at h5
  have h6 : (D.ptMap (red p g t)).1 (e (D.ptIdx (red p g t)) : (D.fin.AAx _ : Type)) =
      (-1) ^ n := h5
  have h7 : (PadicInt.toZMod (pair p g D.H.E s t)).val % 2 = n % 2 := by
    rw [← hn, ZMod.val_natCast, ← hp, Nat.mod_mod]
  unfold Dat.evAll
  rw [h6, map_pow, map_neg, map_one, neg_one_pow_eq_pow_mod_two n, ← h7,
    ← neg_one_pow_eq_pow_mod_two]

end GlobalTheory
end
end
