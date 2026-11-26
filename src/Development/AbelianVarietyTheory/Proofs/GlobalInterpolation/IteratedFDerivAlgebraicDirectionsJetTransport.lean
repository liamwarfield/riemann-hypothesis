module

public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LocalDualIndex
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.OverLatticeIffSelfDualOverBase

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IteratedFDerivAlgebraicDirectionsJetTransport
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IteratedFDerivAlgebraicDirectionsJetTransport
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

noncomputable section

namespace GlobalTheory.JetTransport

section Formal

variable {σ : Type} [Fintype σ] [DecidableEq σ] {p : ℕ} [Fact p.Prime]

def factP (n : σ →₀ ℕ) : ℂ_[p] := ∏ i, ((n i).factorial : ℂ_[p])

theorem multiIndexFactorial_zero : (factP (0 : σ →₀ ℕ) : ℂ_[p]) = 1 := by simp [factP]

theorem multiIndexFactorial_add_single (n : σ →₀ ℕ) (k : σ) :
    (factP (n + Finsupp.single k 1) : ℂ_[p]) = factP n * ((n k : ℂ_[p]) + 1) := by
  unfold factP
  have h : ∀ i, (((n + Finsupp.single k 1 : σ →₀ ℕ) i).factorial : ℂ_[p]) =
      ((n i).factorial : ℂ_[p]) * (if i = k then (n k : ℂ_[p]) + 1 else 1) := by
    intro i
    by_cases hi : i = k
    · subst hi
      rw [Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ, if_pos rfl]
      push_cast; ring
    · rw [Finsupp.add_apply, if_neg hi]
      simp [Finsupp.single_apply, Ne.symm hi]
  rw [Finset.prod_congr rfl fun i _ => h i, Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ k]
  simp

theorem coeff_pd (k : σ) (F : MvPowerSeries σ ℂ_[p]) (n : σ →₀ ℕ) :
    MvPowerSeries.coeff n (pd k F) = ((n k : ℂ_[p]) + 1) * MvPowerSeries.coeff (n + Finsupp.single k 1) F := rfl

def cntL (l : List σ) : σ →₀ ℕ := (l.map fun k => Finsupp.single k 1).sum

theorem coeff_foldr_pd (F : MvPowerSeries σ ℂ_[p]) : ∀ (l : List σ) (n : σ →₀ ℕ),
    factP n * MvPowerSeries.coeff n (l.foldr (fun k G => pd k G) F) =
      factP (n + cntL l) * MvPowerSeries.coeff (n + cntL l) F
  | [], n => by simp [cntL]
  | k :: l, n => by
    have hc : cntL (k :: l) = Finsupp.single k 1 + cntL l := by simp [cntL]
    rw [List.foldr_cons, coeff_pd, ← mul_assoc, ← multiIndexFactorial_add_single, coeff_foldr_pd F l, hc, add_assoc]

theorem pd_sum_smul {ι : Type} (s : Finset ι) (a : ι → ℂ_[p]) (P : ι → MvPowerSeries σ ℂ_[p]) (k : σ) :
    pd k (∑ i ∈ s, a i • P i) = ∑ i ∈ s, a i • pd k (P i) := by
  ext n
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [coeff_pd, map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem foldr_expand {β : Type} (c : β → σ → ℂ_[p]) (F : MvPowerSeries σ ℂ_[p]) : ∀ (m : ℕ) (y : Fin m → β),
    (List.ofFn y).foldr (fun b G => ∑ k, algebraMap ℂ_[p] (MvPowerSeries σ ℂ_[p]) (c b k) * pd k G) F =
      ∑ f : Fin m → σ, (∏ j, c (y j) (f j)) • (List.ofFn f).foldr (fun k G => pd k G) F
  | 0, y => by simp
  | m + 1, y => by
    rw [List.ofFn_succ, List.foldr_cons, foldr_expand c F m]
    rw [← (Fin.consEquiv (fun _ : Fin (m + 1) => σ)).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Algebra.smul_def, pd_sum_smul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    have e : (Fin.consEquiv (fun _ : Fin (m + 1) => σ)) (k, f) = Fin.cons k f := rfl
    rw [e, List.ofFn_cons, List.foldr_cons, Fin.prod_univ_succ, smul_smul]
    simp only [Fin.cons_zero, Fin.cons_succ]

theorem cntL_ofFn {m : ℕ} (f : Fin m → σ) : cntL (List.ofFn f) = ∑ j, Finsupp.single (f j) 1 := by
  simp [cntL, List.map_ofFn, List.sum_ofFn]

end Formal

section Cplx

variable {σ : Type} [Fintype σ]

def cnt {k : ℕ} (f : Fin k → σ) (i : σ) : ℕ := (Finset.univ.filter fun j => f j = i).card

theorem perm_of_cnt {k : ℕ} (f l : Fin k → σ) (h : ∀ i, cnt f i = cnt l i) :
    ∃ e : Equiv.Perm (Fin k), f = l ∘ e := by
  have e : ∀ c, {a // f a = c} ≃ {b // l b = c} := fun c =>
    Fintype.equivOfCardEq (by rw [Fintype.card_subtype, Fintype.card_subtype]; exact h c)
  refine ⟨Equiv.ofFiberEquiv e, ?_⟩
  funext a
  exact (Equiv.ofFiberEquiv_map e a).symm

theorem cnt_toList (α : σ →₀ ℕ) (i : σ) :
    cnt (fun j : Fin (Multiset.card α.toMultiset) => α.toMultiset.toList.get ⟨j, by simpa using j.2⟩) i = α i := by
  set l := fun j : Fin (Multiset.card α.toMultiset) => α.toMultiset.toList.get ⟨j, by simpa using j.2⟩
  have hmap : Multiset.map l Finset.univ.val = α.toMultiset := by
    rw [Fin.univ_val_map]
    have : List.ofFn l = α.toMultiset.toList := by
      refine List.ext_get (by simp) ?_
      intro n h1 h2
      simp [l]
    rw [this, Multiset.coe_toList]
  have h := congrArg (Multiset.count i) hmap
  rw [Multiset.count_map, Finsupp.count_toMultiset] at h
  rw [← h]
  unfold cnt
  rw [Finset.card_def, Finset.filter_val]
  congr 1
  exact Multiset.filter_congr fun j _ => eq_comm

def cntF {m : ℕ} (f : Fin m → σ) : σ →₀ ℕ := ∑ j, Finsupp.single (f j) 1

theorem cntF_apply {m : ℕ} (f : Fin m → σ) (i : σ) : cntF f i = cnt f i := by
  rw [cntF, cnt, Finsupp.finsetSum_apply, Finset.card_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : f j = i
  · rw [h, if_pos rfl, Finsupp.single_eq_same]
  · rw [if_neg h, Finsupp.single_apply, if_neg h]

theorem card_cntF {m : ℕ} (f : Fin m → σ) : Multiset.card (cntF f).toMultiset = m := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [cntF, map_sum, Multiset.card_sum]
  simp

end Cplx

section Main

variable {D : D7} {N N' : ℕ}

theorem vec_eq (v : VC D N N') :
    v = ∑ k : D.what₂.Tau × Fin N' × Fin N, v k.1 k.2.1 k.2.2 • coordV D k := by
  funext τ i j
  simp only [Finset.sum_apply, Pi.smul_apply, coordV, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (τ, i, j)]
  · simp
  · rintro ⟨a, b, c⟩ _ hb
    rw [if_neg]
    rintro ⟨rfl, rfl, rfl⟩
    exact hb rfl
  · simp

theorem mlin_expand {m : ℕ} (A : ContinuousMultilinearMap ℂ (fun _ : Fin m => VC D N N') ℂ) (v : Fin m → VC D N N') :
    A v = ∑ f : Fin m → D.what₂.Tau × Fin N' × Fin N,
      (∏ j, v j (f j).1 (f j).2.1 (f j).2.2) * A (fun j => coordV D (f j)) := by
  have hv : v = fun j => ∑ k : D.what₂.Tau × Fin N' × Fin N, v j k.1 k.2.1 k.2.2 • coordV D k :=
    funext fun j => vec_eq (v j)
  conv_lhs => rw [hv]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [A.map_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [A.map_smul_univ, smul_eq_mul]

theorem iFD_coord (G : VC D N N' → ℂ) (hG : ContDiff ℂ ⊤ G) {m : ℕ} (f : Fin m → D.what₂.Tau × Fin N' × Fin N) :
    iteratedFDeriv ℂ m G 0 (fun j => coordV D (f j)) =
      (∏ i, ((cntF f i).factorial : ℂ)) * taylor D G (cntF f) := by
  have key : ∀ (k : ℕ) (hk : k = m) (l : Fin k → D.what₂.Tau × Fin N' × Fin N), (∀ i, cnt l i = cntF f i) →
      iteratedFDeriv ℂ k G 0 (fun j => coordV D (l j)) = iteratedFDeriv ℂ m G 0 (fun j => coordV D (f j)) := by
    rintro k rfl l hl
    obtain ⟨e, he⟩ := perm_of_cnt f l (fun i => by rw [hl, cntF_apply])
    rw [he]
    exact (hG.contDiffAt.iteratedFDeriv_comp_perm (fun j => coordV D (l j)) e).symm
  have e1 : iteratedFDeriv ℂ (Multiset.card (cntF f).toMultiset) G 0
      (fun i => coordV D ((cntF f).toMultiset.toList.get ⟨i, by simpa using i.2⟩)) =
      iteratedFDeriv ℂ m G 0 (fun j => coordV D (f j)) :=
    key _ (card_cntF f) _ (cnt_toList (cntF f))
  have h0 : ((cntF f).prod fun _ n => (n.factorial : ℂ)) = ∏ i, ((cntF f i).factorial : ℂ) :=
    Finsupp.prod_fintype _ _ (by simp)
  have hne : (∏ i, ((cntF f i).factorial : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun _ _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  unfold taylor
  rw [e1, h0, mul_div_cancel₀ _ hne]

theorem embT_mem (τ : D.what₂.Tau) (x : D.host.E) : embT D τ x ∈ Qbar :=
  mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom (embT D τ).toRatAlgHom)

theorem lam_mk {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (a : ℂ) (h : a ∈ Qbar) :
    lam ⟨a, h⟩ = lamC lam a := by
  unfold lamC; rw [dite_eq_left h]

end Main

end GlobalTheory.JetTransport

namespace GlobalTheory.JetTransport

theorem jet_pSer : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (N N' : ℕ) (G : VC D N N' → ℂ), ContDiff ℂ ⊤ G → CoefIn D G Qbar → ∀ (m : ℕ) (y : Fin m → Matrix (Fin N') (Fin N) D.host.E), iteratedFDeriv ℂ m G 0 (fun j => embV D (tor0 D cc δ) (y j)) ∈ Qbar ∧ jet D lam y (pSer D lam G) = lamC lam (iteratedFDeriv ℂ m G 0 fun j => embV D (tor0 D cc δ) (y j)) := by
  intro D cc δ p _ lam N N' G hG hco m y
  have hC : iteratedFDeriv ℂ m G 0 (fun j => embV D (tor0 D cc δ) (y j)) =
      ∑ f : Fin m → D.what₂.Tau × Fin N' × Fin N, (∏ j, embT D (f j).1 (y j (f j).2.1 (f j).2.2)) *
        ((∏ i, ((cntF f i).factorial : ℂ)) * taylor D G (cntF f)) := by
    rw [mlin_expand]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [iFD_coord G hG f]
    rfl
  have hP : jet D lam y (pSer D lam G) =
      ∑ f : Fin m → D.what₂.Tau × Fin N' × Fin N, (∏ j, lamC lam (embT D (f j).1 (y j (f j).2.1 (f j).2.2))) *
        ((∏ i, ((cntF f i).factorial : ℂ_[p])) * lamC lam (taylor D G (cntF f))) := by
    unfold jet
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    have hx := foldr_expand (fun (b : Matrix (Fin N') (Fin N) D.host.E) (k : D.what₂.Tau × Fin N' × Fin N) =>
      lamC lam (embT D k.1 (b k.2.1 k.2.2))) (pSer D lam G) m y
    erw [hx, map_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [map_smul, smul_eq_mul]
    congr 1
    have h := coeff_foldr_pd (pSer D lam G) (List.ofFn f) 0
    rw [zero_add, cntL_ofFn, multiIndexFactorial_zero, one_mul] at h
    rw [h]
    rfl
  set z : Qbar := ∑ f : Fin m → D.what₂.Tau × Fin N' × Fin N,
    (∏ j, (⟨embT D (f j).1 (y j (f j).2.1 (f j).2.2), embT_mem _ _⟩ : Qbar)) *
      ((∏ i, ((cntF f i).factorial : Qbar)) * ⟨taylor D G (cntF f), hco _⟩) with hzdef
  have hz : (z : ℂ) = iteratedFDeriv ℂ m G 0 (fun j => embV D (tor0 D cc δ) (y j)) := by
    rw [hC, hzdef, IntermediateField.coe_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [IntermediateField.coe_mul, IntermediateField.coe_mul, IntermediateField.coe_prod, IntermediateField.coe_prod]
    simp
  have hl : lam z = jet D lam y (pSer D lam G) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hP, hzdef, map_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    simp only [map_mul, map_prod, map_natCast, lam_mk]
  refine ⟨hz ▸ z.2, ?_⟩
  rw [← hz, ← hl]
  exact lam_mk lam _ z.2

end GlobalTheory.JetTransport
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IteratedFDerivAlgebraicDirectionsJetTransportStatement
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iteratedFDeriv_algebraic_directions_jet_transport : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (N N' : ℕ) (G : VC D N N' → ℂ), ContDiff ℂ ⊤ G → CoefIn D G Qbar → ∀ (m : ℕ) (y : Fin m → Matrix (Fin N') (Fin N) D.host.E), iteratedFDeriv ℂ m G 0 (fun j => embV D (tor0 D cc δ) (y j)) ∈ Qbar ∧ jet D lam y (pSer D lam G) = lamC lam (iteratedFDeriv ℂ m G 0 fun j => embV D (tor0 D cc δ) (y j)) := by
  first | exact @GlobalTheory.JetTransport.jet_pSer | exact GlobalTheory.JetTransport.jet_pSer | (intros; apply GlobalTheory.JetTransport.jet_pSer <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EqOnPadicIntOfEqOnNaturalsMoment
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EqOnPadicIntOfEqOnNaturalsMoment
noncomputable section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

namespace GlobalTheory.MomentPinned

theorem isLocallyConstant_toZModPow {p : ℕ} [Fact p.Prime] (n : ℕ) :
    IsLocallyConstant (PadicInt.toZModPow (p := p) n) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hq : (0 : ℝ) < (p : ℝ) ^ (-(n : ℤ)) := zpow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _
  filter_upwards [Metric.ball_mem_nhds x hq] with y hy
  rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZModPow, ← PadicInt.norm_le_pow_iff_mem_span_pow]
  rw [Metric.mem_ball, dist_eq_norm] at hy
  exact hy.le

theorem isLocallyConstant_red {p : ℕ} [Fact p.Prime] (r n : ℕ) :
    IsLocallyConstant (fun a : Fin r → ℤ_[p] => fun i => PadicInt.toZModPow n (a i)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have : ∀ i, ∀ᶠ y in nhds x, PadicInt.toZModPow n (y i) = PadicInt.toZModPow n (x i) := fun i =>
    ((isLocallyConstant_toZModPow n).comp_continuous (continuous_apply i)).eventually_eq x
  filter_upwards [Filter.eventually_all.2 this] with y hy using funext hy

theorem continuous_zc {p : ℕ} [Fact p.Prime] : Continuous (JMB.zc : ℤ_[p] → ℂ_[p]) := by
  unfold JMB.zc
  exact (continuous_algebraMap ℚ_[p] ℂ_[p]).comp continuous_subtype_val

theorem continuous_pairD {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (Ω : ℂ_[p]) {g : ℕ} (d : ℕ)
    (Hm : Matrix (Fin g) (Fin g) ℂ) {r : ℕ} (b : Fin r → Fin g → ℂ) (y : Fin g → ℂ) :
    Continuous (JMB.pairD lam Ω d Hm b y) := by
  unfold JMB.pairD
  have := continuous_zc (p := p)
  fun_prop

theorem continuous_charPart {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {g : ℕ}
    (Hm : Matrix (Fin g) (Fin g) ℂ) {r : ℕ} (n : ℕ) (b : Fin r → Fin g → ℂ) (Y : Fin g → ℂ) :
    Continuous fun a : Fin r → ℤ_[p] => JMB.lamA lam (JMB.kap Hm (JMB.vecA n b a) Y) :=
  ((isLocallyConstant_red (p := p) r n).comp (fun s : Fin r → ZMod (p ^ n) =>
    JMB.lamA lam (JMB.kap Hm (∑ i, (((s i).val : ℕ) : ℂ) • b i) Y))).continuous

theorem eq_of_natCast : ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (Ω : ℂ_[p]) (g : ℕ) (S : JMB.Setup g) (r n k : ℕ) (bS : Fin r → Fin g → ℂ) (Y : Fin g → ℂ) (ys : Fin k → Fin g → ℂ) (f : C(Fin r → ℤ_[p], ℂ_[p])), (∀ a : Fin r → ℕ, f (fun i => (a i : ℤ_[p])) = JMB.lamA lam (JMB.kap S.Hm (JMB.vecA n bS (fun i => (a i : ℤ_[p]))) Y) * ∏ j, JMB.pairD lam Ω S.d S.Hm bS (ys j) (fun i => (a i : ℤ_[p]))) → ∀ a, f a = JMB.lamA lam (JMB.kap S.Hm (JMB.vecA n bS a) Y) * ∏ j, JMB.pairD lam Ω S.d S.Hm bS (ys j) a := by
  intro p _ lam Ω g S r n k bS Y ys f h a
  have hR : Continuous fun a : Fin r → ℤ_[p] =>
      JMB.lamA lam (JMB.kap S.Hm (JMB.vecA n bS a) Y) * ∏ j, JMB.pairD lam Ω S.d S.Hm bS (ys j) a :=
    (continuous_charPart lam S.Hm n bS Y).mul
      (continuous_finsetProd Finset.univ fun j _ => continuous_pairD lam Ω S.d S.Hm bS (ys j))
  have hd : DenseRange (fun a : Fin r → ℕ => fun i => (a i : ℤ_[p])) :=
    DenseRange.piMap fun _ : Fin r => PadicInt.denseRange_natCast (p := p)
  exact congr_fun (hd.equalizer f.continuous hR (funext h)) a

end GlobalTheory.MomentPinned
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EqOnPadicIntOfEqOnNaturalsMomentStatement
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_on_padicInt_of_eq_on_naturals_moment : ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (Ω : ℂ_[p]) (g : ℕ) (S : JMB.Setup g) (r n k : ℕ) (bS : Fin r → Fin g → ℂ) (Y : Fin g → ℂ) (ys : Fin k → Fin g → ℂ) (f : C(Fin r → ℤ_[p], ℂ_[p])), (∀ a : Fin r → ℕ, f (fun i => (a i : ℤ_[p])) = JMB.lamA lam (JMB.kap S.Hm (JMB.vecA n bS (fun i => (a i : ℤ_[p]))) Y) * ∏ j, JMB.pairD lam Ω S.d S.Hm bS (ys j) (fun i => (a i : ℤ_[p]))) → ∀ a, f a = JMB.lamA lam (JMB.kap S.Hm (JMB.vecA n bS a) Y) * ∏ j, JMB.pairD lam Ω S.d S.Hm bS (ys j) a := by
  first | exact @GlobalTheory.MomentPinned.eq_of_natCast | exact GlobalTheory.MomentPinned.eq_of_natCast | (intros; apply GlobalTheory.MomentPinned.eq_of_natCast <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryQuotientIntegralProdOverPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryQuotientIntegralProdOverPlaces
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct

noncomputable section

namespace GlobalTheory.RealQuotProd

variable {P Q P' Q' : ℕ}

theorem act_mul (g h : UpqT P Q) (x : ActionCoordinates.Wsp P Q) :
    ActionCoordinates.act (g * h) x = ActionCoordinates.act g (ActionCoordinates.act h x) := by
  unfold ActionCoordinates.act
  rw [Matrix.mulVec_mulVec]; rfl

theorem act_one (x : ActionCoordinates.Wsp P Q) : ActionCoordinates.act (1 : UpqT P Q) x = x := Matrix.one_mulVec x

theorem act_mul_inv {a : UpqT P Q} {x : ActionCoordinates.Wsp P Q} (ha : ActionCoordinates.act a x = x) (g : UpqT P Q) :
    ActionCoordinates.act (a * g)⁻¹ x = ActionCoordinates.act g⁻¹ x := by
  have : ActionCoordinates.act a⁻¹ x = x := by
    conv_lhs => rw [← ha]
    rw [← act_mul, inv_mul_cancel, act_one]
  rw [_root_.mul_inv_rev, act_mul, this]

theorem measurable_act_inv (x : ActionCoordinates.Wsp P Q) :
    Measurable fun g : UpqT P Q => ActionCoordinates.act g⁻¹ x := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.UpqTopology.upq_lcsc P Q
  exact ((GlobalTheory.UpqTopology.continuous_mat.comp continuous_inv).matrix_mulVec
    continuous_const).measurable

theorem sigmaFinite_cd (c : CDHaar) (P Q : ℕ) : SigmaFinite (c.cd P Q) := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.UpqTopology.upq_lcsc P Q
  haveI : (c.cd P Q).IsHaarMeasure := c.haar P Q
  infer_instance

theorem one_place (H : ActionCoordinates.QuotientMeasure) (c : CDHaar) {β : ℝ} (hβ : β = 1 ∨ β = -1)
    {x : ActionCoordinates.Wsp P Q} (hx : ActionCoordinates.qf x = β) {k : ActionCoordinates.Wsp P' Q' →ₗ[ℂ] ActionCoordinates.Wsp P Q}
    {ι : UpqT P' Q' → UpqT P Q} (hk : ActionCoordinates.IsPerpFrame x k ι) {u : UpqT P Q → ℝ≥0∞}
    (hu : Measurable u) (hu' : ∀ g, Measurable (fun h => u (ι h * g)) ∧
      ∫⁻ h, u (ι h * g) ∂(c.cd P' Q') = 1)
    {fib : ℝ → Measure (ActionCoordinates.Wsp P Q)} (hfib : ActionCoordinates.IsDxDq β fib)
    {φ : ActionCoordinates.Wsp P Q → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ g, φ (ActionCoordinates.act g⁻¹ x) * u g ∂(c.cd P Q) =
      (ActionCoordinates.cM (P + Q))⁻¹ * ∫⁻ y, φ y ∂(fib β) := by
  classical
  obtain ⟨h1, -, h3⟩ := H P Q β hβ x hx
  choose! s hs using h1
  have hae : ∀ᵐ y ∂(fib β), ActionCoordinates.qf y = β := by
    obtain ⟨U, B, -, -, -, hF⟩ := hfib
    have h1 : ∀ᵐ y ∂(fib β), y ∈ ActionCoordinates.qf ⁻¹' {id β} ∩ U := hF.1 β
    filter_upwards [h1] with y hy using hy.1
  rw [(h3 P' Q' k ι hk).2 c fib hfib s hs (fun g => φ (ActionCoordinates.act g⁻¹ x) * u g)
    ((hφ.comp (measurable_act_inv x)).mul hu),
    Measure.restrict_eq_self_of_ae_mem (s := {y | ActionCoordinates.qf y = β}) hae]
  congr 1
  refine lintegral_congr_ae (hae.mono fun y hy => ?_)
  have e : ∀ h, φ (ActionCoordinates.act (ι h * s y)⁻¹ x) = φ y := fun h => by
    rw [act_mul_inv (hk.2.2 h).1, hs y hy]
  simp only [e]
  rw [lintegral_const_mul _ (hu' _).1, (hu' _).2, mul_one]

theorem quot_integral_prod : ActionCoordinates.QuotientMeasure → ∀ (c : CDHaar) (T : Type) [Fintype T] (P Q P' Q' : ℕ) (β : ℝ), (β = 1 ∨ β = -1) → ∀ x : T → ActionCoordinates.Wsp P Q, (∀ ρ, ActionCoordinates.qf (x ρ) = β) → ∀ (k : T → (ActionCoordinates.Wsp P' Q' →ₗ[ℂ] ActionCoordinates.Wsp P Q)) (ι : T → UpqT P' Q' → UpqT P Q), (∀ ρ, ActionCoordinates.IsPerpFrame (x ρ) (k ρ) (ι ρ)) → ∀ u : T → UpqT P Q → ℝ≥0∞, (∀ ρ, Measurable (u ρ) ∧ ∀ g, Measurable (fun h => u ρ (ι ρ h * g)) ∧ ∫⁻ h, u ρ (ι ρ h * g) ∂(c.cd P' Q') = 1) → ∀ j : (T → UpqT P' Q') →* (T → UpqT P Q), (∀ b ρ, j b ρ = ι ρ (b ρ)) → ∀ ν : Measure (LatticeTensorUnfolding.RCosets j), LatticeTensorUnfolding.IsQuotMeasure j (Measure.pi fun _ => c.cd P Q) (Measure.pi fun _ => c.cd P' Q') ν → ∀ fib : ℝ → Measure (ActionCoordinates.Wsp P Q), ActionCoordinates.IsDxDq β fib → ∀ φ : T → ActionCoordinates.Wsp P Q → ℝ≥0∞, (∀ ρ, Measurable (φ ρ)) → ∫⁻ s : LatticeTensorUnfolding.RCosets j, ∏ ρ, φ ρ (ActionCoordinates.act (s.out ρ)⁻¹ (x ρ)) ∂ν = ∏ ρ, (ActionCoordinates.cM (P + Q))⁻¹ * ∫⁻ y, φ ρ y ∂(fib β) := by
  intro H c T _ P Q P' Q' β hβ x hx k ι hk u hu j hj ν hν fib hfib φ hφ
  haveI := sigmaFinite_cd c P Q
  haveI := sigmaFinite_cd c P' Q'
  let f : T → UpqT P Q → ℝ≥0∞ := fun ρ g => φ ρ (ActionCoordinates.act g⁻¹ (x ρ)) * u ρ g
  have hf : ∀ ρ, Measurable (f ρ) := fun ρ =>
    ((hφ ρ).comp (measurable_act_inv (x ρ))).mul (hu ρ).1
  have key := hν (fun g => ∏ ρ, f ρ (g ρ))
    (Finset.measurable_prod _ fun ρ _ => (hf ρ).comp (measurable_pi_apply ρ))
  rw [GlobalTheory.SnMass.Push.lintegral_fintype_prod f hf] at key
  rw [← Finset.prod_congr rfl fun ρ _ =>
    one_place H c hβ (hx ρ) (hk ρ) (hu ρ).1 (hu ρ).2 hfib (hφ ρ)]
  refine Eq.trans (lintegral_congr fun s => ?_) key.symm
  have e : ∀ h : T → UpqT P' Q', ∏ ρ, f ρ ((j h * s.out) ρ) =
      ∏ ρ, (fun ρ b => φ ρ (ActionCoordinates.act (s.out ρ)⁻¹ (x ρ)) * u ρ (ι ρ b * s.out ρ)) ρ (h ρ) :=
    fun h => Finset.prod_congr rfl fun ρ _ => by
      simp only [f, Pi.mul_apply, hj]
      rw [act_mul_inv ((hk ρ).2.2 _).1]
  rw [lintegral_congr e, GlobalTheory.SnMass.Push.lintegral_fintype_prod
    (fun ρ b => φ ρ (ActionCoordinates.act (s.out ρ)⁻¹ (x ρ)) * u ρ (ι ρ b * s.out ρ))
    (fun ρ => (((hu ρ).2 _).1).const_mul _)]
  refine Finset.prod_congr rfl fun ρ _ => ?_
  rw [lintegral_const_mul _ ((hu ρ).2 _).1, ((hu ρ).2 _).2, mul_one]

end GlobalTheory.RealQuotProd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryQuotientIntegralProdOverPlacesStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryQuotientIntegral_prod_over_places : ActionCoordinates.QuotientMeasure → ∀ (c : CDHaar) (T : Type) [Fintype T] (P Q P' Q' : ℕ) (β : ℝ), (β = 1 ∨ β = -1) → ∀ x : T → ActionCoordinates.Wsp P Q, (∀ ρ, ActionCoordinates.qf (x ρ) = β) → ∀ (k : T → (ActionCoordinates.Wsp P' Q' →ₗ[ℂ] ActionCoordinates.Wsp P Q)) (ι : T → UpqT P' Q' → UpqT P Q), (∀ ρ, ActionCoordinates.IsPerpFrame (x ρ) (k ρ) (ι ρ)) → ∀ u : T → UpqT P Q → ℝ≥0∞, (∀ ρ, Measurable (u ρ) ∧ ∀ g, Measurable (fun h => u ρ (ι ρ h * g)) ∧ ∫⁻ h, u ρ (ι ρ h * g) ∂(c.cd P' Q') = 1) → ∀ j : (T → UpqT P' Q') →* (T → UpqT P Q), (∀ b ρ, j b ρ = ι ρ (b ρ)) → ∀ ν : Measure (LatticeTensorUnfolding.RCosets j), LatticeTensorUnfolding.IsQuotMeasure j (Measure.pi fun _ => c.cd P Q) (Measure.pi fun _ => c.cd P' Q') ν → ∀ fib : ℝ → Measure (ActionCoordinates.Wsp P Q), ActionCoordinates.IsDxDq β fib → ∀ φ : T → ActionCoordinates.Wsp P Q → ℝ≥0∞, (∀ ρ, Measurable (φ ρ)) → ∫⁻ s : LatticeTensorUnfolding.RCosets j, ∏ ρ, φ ρ (ActionCoordinates.act (s.out ρ)⁻¹ (x ρ)) ∂ν = ∏ ρ, (ActionCoordinates.cM (P + Q))⁻¹ * ∫⁻ y, φ ρ y ∂(fib β) := by
  first | exact @GlobalTheory.RealQuotProd.quot_integral_prod | exact GlobalTheory.RealQuotProd.quot_integral_prod | (intros; apply GlobalTheory.RealQuotProd.quot_integral_prod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsSecondFunctional
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection
open scoped TensorProduct

namespace GlobalTheory.SecondFunctional

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : HeightOneSpectrum (𝓞 F)}

theorem mem_primeOf_prPbar {σ : E →ₐ[F] E}
    {φ : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F}
    (hφ : IsSplitting σ v φ) (a : intV E v) :
    a ∈ primeOf (prPbar φ) ↔ Valued.v (prPbar φ a) < 1 := by
  refine ⟨fun h => ?_, fun h => Ideal.subset_span h⟩
  induction h using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => simp
  | add x y _ _ hx hy =>
    rw [Subring.coe_add, map_add (f := _)]
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hx hy)
  | smul c x _ hx =>
    have hc : Valued.v (prPbar φ c) ≤ 1 := ((hφ.2.2 c).1 c.2).2
    rw [smul_eq_mul, Subring.coe_mul, map_mul, map_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_right hc zero_le' hx

theorem exists_max {ι : Type} (g : ι → WithZero (Multiplicative ℤ)) (t : WithZero (Multiplicative ℤ))
    (ht : t ≠ 0) (hb : ∀ y, t * g y ≤ 1) (y₁ : ι) (h₁ : g y₁ ≠ 0) : ∃ y₀, ∀ y, g y ≤ g y₀ := by
  obtain ⟨n, ⟨y₀, hy₀⟩, hn⟩ := Int.exists_greatest_of_bdd (P := fun n => ∃ y, g y = WithZero.exp n)
    ⟨-WithZero.log t, fun z ⟨y, hy⟩ => by
      have := hb y
      rw [hy, ← WithZero.exp_log ht, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp] at this
      omega⟩ ⟨_, y₁, (WithZero.exp_log h₁).symm⟩
  refine ⟨y₀, fun y => ?_⟩
  by_cases hy : g y = 0
  · rw [hy]; exact zero_le'
  · rw [hy₀, ← WithZero.exp_log hy, WithZero.exp_le_exp]
    exact hn _ ⟨y, (WithZero.exp_log hy).symm⟩

theorem hform_add_right {A n : Type} [CommRing A] [Fintype n] (σ : A →+* A) (J : Matrix n n A)
    (x y z : n → A) : hform σ J x (y + z) = hform σ J x y + hform σ J x z := by
  simp [hform, mul_add, Finset.sum_add_distrib]

theorem hform_smul_right {A n : Type} [CommRing A] [Fintype n] (σ : A →+* A) (J : Matrix n n A)
    (x y : n → A) (a : A) : hform σ J x (a • y) = a * hform σ J x y := by
  simp only [hform, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hform_nsmul_left {A n : Type} [CommRing A] [Fintype n] (σ : A →+* A) (J : Matrix n n A)
    (x y : n → A) (T : ℕ) : hform σ J (T • x) y = T * hform σ J x y := by
  simp only [hform, Finset.mul_sum, Pi.smul_apply, nsmul_eq_mul, map_mul, map_natCast]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring


set_option maxHeartbeats 800000 in
theorem exists_second_functional :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (s : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), IsSplitting σ v s → ∀ (k : ℕ) (J : Matrix (Fin k) (Fin k) (E ⊗[F] v.adicCompletion F)) (L₁ L₂ : Submodule (intV E v) (Fin k → E ⊗[F] v.adicCompletion F)), (∀ y ∈ L₁, ∀ x ∈ L₂, hform (sigR σ (v.adicCompletion F)) J x y ∈ intV E v) → (∀ x, x ∈ L₁ ↔ ∀ y ∈ L₂, hform (sigR σ (v.adicCompletion F)) J x y ∈ intV E v) → ∀ (T : ℕ), T ≠ 0 → (∀ x ∈ L₂, T • x ∈ L₁) → (∃ x ∈ L₂, x ∉ L₁ ∧ ∀ i, prPbar s (x i) = 0) → ∃ f : L₂ →ₗ[intV E v] (intV E v ⧸ primeOf (prPbar s)), Function.Surjective f ∧ (∀ x : L₂, x.1 ∈ L₁ → f x = 0) ∧ ∀ x : L₂, (∀ i, prPbar s (x.1 i) = 0) → f x = 0 := by
  intro F E _ _ _ _ _ σ v s hs k J L₁ L₂ h1 h2 T hT hTL ⟨x, hx2, hx1, hx0⟩
  obtain ⟨H, hH⟩ : ∃ H : (Fin k → E ⊗[F] v.adicCompletion F) → E ⊗[F] v.adicCompletion F,
    ∀ y, H y = hform (sigR σ (v.adicCompletion F)) J x y := ⟨_, fun _ => rfl⟩
  have e2 : ∀ a, prPbar s a = (s a).2 := fun _ => rfl
  have hfst : ∀ y, (s (H y)).1 = 0 := by
    intro y
    have : ∀ i, prP s (sigR σ (v.adicCompletion F) (x i)) = 0 := fun i =>
      (congrArg Prod.fst (hs.2.1 (x i))).trans (hx0 i)
    show prP s (H y) = 0
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hH, hform, map_sum, map_mul, this, zero_mul, Finset.sum_const_zero]
  have hTK : (T : v.adicCompletion F) ≠ 0 := by
    rw [← map_natCast (algebraMap F (v.adicCompletion F))]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 hT)
  obtain ⟨y₁, hy₁, hy₁'⟩ : ∃ y ∈ L₂, H y ∉ intV E v := by
    by_contra hc
    push_neg at hc
    exact hx1 ((h2 x).2 fun y hy => hH y ▸ hc y hy)
  have hgt : 1 < Valued.v (prPbar s (H y₁)) := by
    by_contra hc
    exact hy₁' ((hs.2.2 _).2 ⟨by rw [hfst]; exact zero_mem _, not_lt.1 hc⟩)
  obtain ⟨y₀, hy₀⟩ := exists_max (fun y : L₂ => Valued.v (prPbar s (H y))) (Valued.v (T : v.adicCompletion F))
    (by simpa using hTK) (fun y => by
      have h := ((hs.2.2 _).1 ((h2 _).1 (hTL x hx2) y y.2)).2
      rw [hform_nsmul_left, ← e2, map_mul, map_natCast, ← hH] at h
      rw [← map_mul]; exact h) ⟨y₁, hy₁⟩ (ne_of_gt (lt_trans zero_lt_one hgt))
  obtain ⟨c, hc⟩ : ∃ c, c = prPbar s (H y₀) := ⟨_, rfl⟩
  replace hy₀ : ∀ y : L₂, Valued.v (prPbar s (H y)) ≤ Valued.v c := hc ▸ hy₀
  have hc1 : 1 < Valued.v c := lt_of_lt_of_le hgt (hy₀ ⟨y₁, hy₁⟩)
  have hcv : 0 < Valued.v c := lt_trans zero_lt_one hc1
  have hc0 : c ≠ 0 := by
    intro h; rw [h, map_zero] at hcv; exact lt_irrefl _ hcv
  obtain ⟨d, hd⟩ : ∃ d, d = s.symm (0, c⁻¹) := ⟨_, rfl⟩
  have hd2 : ∀ y, prPbar s (H y * d) = prPbar s (H y) / c := fun y => by
    rw [map_mul, e2 d, hd, s.apply_symm_apply, div_eq_mul_inv]
  have hmem : ∀ y : L₂, H y * d ∈ intV E v := fun y => by
    refine (hs.2.2 _).2 ⟨?_, ?_⟩
    · rw [map_mul, Prod.fst_mul, hfst, zero_mul]; exact zero_mem _
    · show Valued.v (prPbar s (H y * d)) ≤ 1
      rw [hd2, map_div₀, div_le_one₀ hcv]
      exact hy₀ y
  let g : L₂ →ₗ[intV E v] intV E v :=
    { toFun := fun y => ⟨H y * d, hmem y⟩
      map_add' := fun y z => Subtype.ext (by
        show H (y.1 + z.1) * d = H y * d + H z * d
        simp only [hH, hform_add_right, add_mul])
      map_smul' := fun a y => Subtype.ext (by
        show H ((a : E ⊗[F] v.adicCompletion F) • y.1) * d = a * (H y * d)
        simp only [hH, hform_smul_right, mul_assoc]) }
  have hg : ∀ y : L₂, prPbar s (g y) = prPbar s (H y) / c := fun y => hd2 y
  have hz : ∀ y : L₂, Valued.v (prPbar s (H y)) ≤ 1 → (primeOf (prPbar s)).mkQ (g y) = 0 := by
    intro y hy
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, mem_primeOf_prPbar hs, hg, map_div₀,
      div_lt_one₀ hcv]
    exact lt_of_le_of_lt hy hc1
  refine ⟨(primeOf (prPbar s)).mkQ ∘ₗ g, fun b => ?_, fun y hy => hz y ?_, fun y hy => hz y ?_⟩
  · obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    refine ⟨a • y₀, ?_⟩
    rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, mem_primeOf_prPbar hs, map_smul,
      smul_eq_mul, AddSubgroupClass.coe_sub, Subring.coe_mul, map_sub, map_mul, hg, ← hc, div_self hc0]
    simp
  · rw [hH]; exact ((hs.2.2 _).1 (h1 y hy x hx2)).2
  · have : prPbar s (H y) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hH, hform, map_sum, map_mul, hy, mul_zero, Finset.sum_const_zero]
    rw [this]; simp

end GlobalTheory.SecondFunctional
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FibreIntegralPiProdEqProdFibreIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FibreIntegralPiProdEqProdFibreIntegral
open MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Set Topology
open scoped ENNReal

namespace GlobalTheory.FibreProd

theorem le_of_lintegral_ball_eq {X : Type} [PseudoMetricSpace X] [ProperSpace X] [MeasurableSpace X]
    [BorelSpace X] (ν : Measure X) [ν.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts ν]
    (G H : X → ℝ≥0∞) (b : X) (hG : ContinuousAt G b) (hH : ContinuousAt H b)
    (h : ∀ r > 0, ∫⁻ x in Metric.ball b r, G x ∂ν = ∫⁻ x in Metric.ball b r, H x ∂ν) :
    H b ≤ G b := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨c, hc1, hc2⟩ := exists_between hlt
  obtain ⟨d, hd1, hd2⟩ := exists_between hc2
  have e : ∀ᶠ x in 𝓝 b, G x < c ∧ d < H x :=
    (hG.eventually (gt_mem_nhds hc1)).and (hH.eventually (lt_mem_nhds hd2))
  obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff_ball.1 e
  have h1 : ∫⁻ x in Metric.ball b r, G x ∂ν ≤ c * ν (Metric.ball b r) := by
    rw [← setLIntegral_const]
    exact setLIntegral_mono' measurableSet_ball fun x hx => (hb x hx).1.le
  have h2 : d * ν (Metric.ball b r) ≤ ∫⁻ x in Metric.ball b r, H x ∂ν := by
    rw [← setLIntegral_const]
    exact setLIntegral_mono' measurableSet_ball fun x hx => (hb x hx).2.le
  have h3 : c * ν (Metric.ball b r) < d * ν (Metric.ball b r) :=
    ENNReal.mul_lt_mul_left (Metric.measure_ball_pos ν b hr).ne' measure_ball_lt_top.ne hd1
  exact absurd (h2.trans ((h r hr).symm.le.trans h1)) h3.not_ge

theorem lintegral_preimage {V X : Type} [TopologicalSpace V] [MeasurableSpace V]
    [BorelSpace V] [TopologicalSpace X] [MeasurableSpace X] {μ : Measure V} {ν : Measure X}
    {f : V → X} {U : Set V} {B : Set X} {fib : X → Measure V}
    (hf : Measurable f) (hU : IsOpen U) (h : IsFibreFamily μ f id U ν B fib)
    (φ : V → ℝ≥0∞) (hφ : Measurable φ) (hs : ∀ v, v ∉ U → φ v = 0)
    (S : Set X) (hS : MeasurableSet S) :
    ∫⁻ v, (f ⁻¹' S).indicator φ v ∂μ = ∫⁻ b in S, ∫⁻ v, φ v ∂(fib b) ∂ν := by
  have h2 := h.2.1 ((f ⁻¹' S).indicator φ) (hφ.indicator (hf hS))
  have e1 : ∫⁻ v, (f ⁻¹' S).indicator φ v ∂μ = ∫⁻ v in U, (f ⁻¹' S).indicator φ v ∂μ := by
    rw [← lintegral_indicator hU.measurableSet]
    congr 1
    funext v
    by_cases hv : v ∈ U
    · rw [indicator_of_mem hv]
    · rw [indicator_of_notMem hv]
      exact indicator_apply_eq_zero.2 fun _ => hs v hv
  rw [e1, h2, ← lintegral_indicator hS]
  congr 1
  funext b
  have hb : ∀ᵐ v ∂(fib b), f v = b := by
    have : ∀ᵐ v ∂(fib b), v ∈ f ⁻¹' {id b} ∩ U := h.1 b
    filter_upwards [this] with v hv using hv.1
  by_cases hbS : b ∈ S
  · rw [indicator_of_mem hbS]
    apply lintegral_congr_ae
    filter_upwards [hb] with v hv
    exact indicator_of_mem (by simpa [hv] using hbS) _
  · rw [indicator_of_notMem hbS, ← lintegral_zero (μ := fib b)]
    apply lintegral_congr_ae
    filter_upwards [hb] with v hv
    exact indicator_of_notMem (by simpa [hv] using hbS) _

theorem lintegral_fibre_prod : ∀ (T V : Type) [Fintype T] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ₀ : Measure V) [SigmaFinite μ₀] (q : V → ℝ), Continuous q → ∀ U : Set V, IsOpen U → ∀ fib : ℝ → Measure V, IsFibreFamily μ₀ q id U (volume : Measure ℝ) Set.univ fib → ∀ B : Set (T → ℝ), IsOpen B → ∀ Fib : (T → ℝ) → Measure (T → V), IsFibreFamily (Measure.pi fun _ : T => μ₀) (fun x ρ => q (x ρ)) id Set.univ (volume : Measure (T → ℝ)) B Fib → ∀ b ∈ B, ∀ φ : T → V → ℝ, (∀ ρ, Continuous (φ ρ) ∧ HasCompactSupport (φ ρ) ∧ tsupport (φ ρ) ⊆ U ∧ ∀ y, 0 ≤ φ ρ y) → ∫⁻ x, ∏ ρ, ENNReal.ofReal (φ ρ (x ρ)) ∂(Fib b) = ∏ ρ, ∫⁻ y, ENNReal.ofReal (φ ρ y) ∂(fib (b ρ)) := by
  intro T V _ _ _ _ _ _ μ₀ _ q hq U hU fib hfib B hB Fib hFib b hb φ hφ
  classical
  haveI : ProperSpace V := FiniteDimensional.proper_real V
  have hΦc : Continuous fun x : T → V => ∏ ρ, φ ρ (x ρ) :=
    continuous_finsetProd _ fun ρ _ => (hφ ρ).1.comp (continuous_apply ρ)
  have hΦs : HasCompactSupport fun x : T → V => ∏ ρ, φ ρ (x ρ) := by
    refine HasCompactSupport.intro (isCompact_univ_pi fun ρ => (hφ ρ).2.1) fun x hx => ?_
    rw [mem_univ_pi, not_forall] at hx
    obtain ⟨ρ, hρ⟩ := hx
    exact Finset.prod_eq_zero (Finset.mem_univ ρ) (image_eq_zero_of_notMem_tsupport hρ)
  obtain ⟨hI, hC⟩ := hFib.2.2 _ hΦc hΦs (subset_univ _)
  have hm : ∀ ρ, Measurable fun y => ENNReal.ofReal (φ ρ y) := fun ρ =>
    ENNReal.measurable_ofReal.comp (hφ ρ).1.measurable
  have hGc : ContinuousOn (fun b => ∫⁻ x, ∏ ρ, ENNReal.ofReal (φ ρ (x ρ)) ∂(Fib b)) B := by
    refine (ENNReal.continuous_ofReal.comp_continuousOn hC).congr fun b hb => ?_
    have := ofReal_integral_eq_lintegral_ofReal (hI b hb)
      (Filter.Eventually.of_forall fun x => Finset.prod_nonneg fun ρ _ => (hφ ρ).2.2.2 _)
    simp only [Function.comp_apply]
    rw [this]
    congr 1
    funext x
    rw [ENNReal.ofReal_prod_of_nonneg fun ρ _ => (hφ ρ).2.2.2 _]
  have hg : ∀ ρ t, ∫⁻ y, ENNReal.ofReal (φ ρ y) ∂(fib t) = ENNReal.ofReal (∫ y, φ ρ y ∂(fib t)) :=
    fun ρ t => (ofReal_integral_eq_lintegral_ofReal
      ((hfib.2.2 _ (hφ ρ).1 (hφ ρ).2.1 (hφ ρ).2.2.1).1 t (mem_univ _))
      (Filter.Eventually.of_forall (hφ ρ).2.2.2)).symm
  have hgc : ∀ ρ, Continuous fun t => ∫ y, φ ρ y ∂(fib t) := fun ρ =>
    continuousOn_univ.1 (hfib.2.2 _ (hφ ρ).1 (hφ ρ).2.1 (hφ ρ).2.2.1).2
  have hgm : ∀ ρ, Measurable fun t => ∫⁻ y, ENNReal.ofReal (φ ρ y) ∂(fib t) := fun ρ => by
    simp only [hg]
    exact ENNReal.measurable_ofReal.comp (hgc ρ).measurable
  have hHc : Continuous fun b : T → ℝ => ∏ ρ, ∫⁻ y, ENNReal.ofReal (φ ρ y) ∂(fib (b ρ)) := by
    have : (fun b : T → ℝ => ∏ ρ, ∫⁻ y, ENNReal.ofReal (φ ρ y) ∂(fib (b ρ))) =
        fun b => ENNReal.ofReal (∏ ρ, ∫ y, φ ρ y ∂(fib (b ρ))) := by
      funext b
      rw [ENNReal.ofReal_prod_of_nonneg fun ρ _ => integral_nonneg (hφ ρ).2.2.2]
      simp only [hg]
    rw [this]
    exact ENNReal.continuous_ofReal.comp
      (continuous_finsetProd _ fun ρ _ => (hgc ρ).comp (continuous_apply ρ))
  have key : ∀ r > 0, ∫⁻ c in Metric.ball b r, ∫⁻ x, ∏ ρ, ENNReal.ofReal (φ ρ (x ρ)) ∂(Fib c) =
      ∫⁻ c in Metric.ball b r, ∏ ρ, ∫⁻ y, ENNReal.ofReal (φ ρ y) ∂(fib (c ρ)) := by
    intro r hr
    have hQ : Measurable fun (x : T → V) ρ => q (x ρ) :=
      (continuous_pi fun ρ => hq.comp (continuous_apply ρ)).measurable
    rw [← lintegral_preimage hQ isOpen_univ hFib (fun x => ∏ ρ, ENNReal.ofReal (φ ρ (x ρ)))
      (Finset.measurable_prod _ fun ρ _ => (hm ρ).comp (measurable_pi_apply ρ))
      (fun v hv => absurd (mem_univ v) hv) _ measurableSet_ball,
      ← lintegral_indicator measurableSet_ball, ball_pi b hr]
    have e1 : ∀ x : T → V, ((fun (x : T → V) ρ => q (x ρ)) ⁻¹'
        (Set.pi univ fun ρ => Metric.ball (b ρ) r)).indicator
        (fun x => ∏ ρ, ENNReal.ofReal (φ ρ (x ρ))) x =
        ∏ ρ, (q ⁻¹' Metric.ball (b ρ) r).indicator (fun y => ENNReal.ofReal (φ ρ y)) (x ρ) := by
      intro x
      by_cases hx : ∀ ρ, x ρ ∈ q ⁻¹' Metric.ball (b ρ) r
      · rw [indicator_of_mem (by simpa using hx)]
        exact Finset.prod_congr rfl fun ρ _ => by rw [indicator_of_mem (hx ρ)]
      · rw [indicator_of_notMem (by simpa using hx)]
        obtain ⟨ρ, hρ⟩ := not_forall.1 hx
        exact (Finset.prod_eq_zero (Finset.mem_univ ρ) (indicator_of_notMem hρ _)).symm
    have e2 : ∀ c : T → ℝ, (Set.pi univ fun ρ => Metric.ball (b ρ) r).indicator
        (fun c => ∏ ρ, ∫⁻ y, ENNReal.ofReal (φ ρ y) ∂(fib (c ρ))) c =
        ∏ ρ, (Metric.ball (b ρ) r).indicator
          (fun t => ∫⁻ y, ENNReal.ofReal (φ ρ y) ∂(fib t)) (c ρ) := by
      intro c
      by_cases hx : ∀ ρ, c ρ ∈ Metric.ball (b ρ) r
      · rw [indicator_of_mem (by simpa using hx)]
        exact Finset.prod_congr rfl fun ρ _ => by rw [indicator_of_mem (hx ρ)]
      · rw [indicator_of_notMem (by simpa using hx)]
        obtain ⟨ρ, hρ⟩ := not_forall.1 hx
        exact (Finset.prod_eq_zero (Finset.mem_univ ρ) (indicator_of_notMem hρ _)).symm
    simp only [e1, e2]
    rw [volume_pi, GlobalTheory.SnMass.Push.lintegral_fintype_prod
        (fun ρ => (q ⁻¹' Metric.ball (b ρ) r).indicator (fun y => ENNReal.ofReal (φ ρ y)))
        (fun ρ => (hm ρ).indicator (hq.measurable measurableSet_ball)),
      GlobalTheory.SnMass.Push.lintegral_fintype_prod
        (fun ρ => (Metric.ball (b ρ) r).indicator
          (fun t => ∫⁻ y, ENNReal.ofReal (φ ρ y) ∂(fib t)))
        (fun ρ => (hgm ρ).indicator measurableSet_ball)]
    refine Finset.prod_congr rfl fun ρ _ => ?_
    rw [lintegral_indicator (s := Metric.ball (b ρ) r) measurableSet_ball]
    refine lintegral_preimage hq.measurable hU hfib _ (hm ρ) (fun v hv => ?_) _ measurableSet_ball
    rw [image_eq_zero_of_notMem_tsupport fun h => hv ((hφ ρ).2.2.1 h), ENNReal.ofReal_zero]
  have hGb := hGc.continuousAt (hB.mem_nhds hb)
  exact le_antisymm
    (le_of_lintegral_ball_eq volume _ _ b hHc.continuousAt hGb fun r hr => (key r hr).symm)
    (le_of_lintegral_ball_eq volume _ _ b hGb hHc.continuousAt key)

end GlobalTheory.FibreProd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FibreIntegralPiProdEqProdFibreIntegralStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibreIntegral_pi_prod_eq_prod_fibreIntegral : ∀ (T V : Type) [Fintype T] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ₀ : Measure V) [SigmaFinite μ₀] (q : V → ℝ), Continuous q → ∀ U : Set V, IsOpen U → ∀ fib : ℝ → Measure V, IsFibreFamily μ₀ q id U (volume : Measure ℝ) Set.univ fib → ∀ B : Set (T → ℝ), IsOpen B → ∀ Fib : (T → ℝ) → Measure (T → V), IsFibreFamily (Measure.pi fun _ : T => μ₀) (fun x ρ => q (x ρ)) id Set.univ (volume : Measure (T → ℝ)) B Fib → ∀ b ∈ B, ∀ φ : T → V → ℝ, (∀ ρ, Continuous (φ ρ) ∧ HasCompactSupport (φ ρ) ∧ tsupport (φ ρ) ⊆ U ∧ ∀ y, 0 ≤ φ ρ y) → ∫⁻ x, ∏ ρ, ENNReal.ofReal (φ ρ (x ρ)) ∂(Fib b) = ∏ ρ, ∫⁻ y, ENNReal.ofReal (φ ρ y) ∂(fib (b ρ)) := by
  first | exact @GlobalTheory.FibreProd.lintegral_fibre_prod | exact GlobalTheory.FibreProd.lintegral_fibre_prod | (intros; apply GlobalTheory.FibreProd.lintegral_fibre_prod <;> assumption)
end
end
