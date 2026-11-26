module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentLevelZeroEqOne
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CastVMulVecLift
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.StrictUpperNeg
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RightStabilizerMem
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormRankZeroApply

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.PairOperatorCommute
open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Fr

section Abstract

variable {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {r : ℕ}

theorem fn_comm6 (L : R.LevelData A r) {x y : A} (hx : x ∈ L.fns) (hy : y ∈ L.fns) : x * y = y * x := L.fns_comm x hx y hy

theorem c_fns (L : R.LevelData A r) (l : Fin r) : L.c l ∈ L.fns := by
  exact Or.inl (Or.inl (Or.inl (Or.inl ⟨l, rfl⟩)))
theorem ci_fns (L : R.LevelData A r) (l : Fin r) : L.ci l ∈ L.fns := by
  exact Or.inl (Or.inl (Or.inl (Or.inr ⟨l, rfl⟩)))
theorem cb_fns (L : R.LevelData A r) (l : Fin r) : L.cb l ∈ L.fns := by
  exact Or.inl (Or.inl (Or.inr ⟨l, rfl⟩))
theorem cbi_fns (L : R.LevelData A r) (l : Fin r) : L.cbi l ∈ L.fns := by
  exact Or.inl (Or.inr ⟨l, rfl⟩)

theorem hol_comm_star (L : R.LevelData A r) (hp : ∀ l, star (L.p l) = -L.pb l) (hc : ∀ l, star (L.c l) = L.cb l)
    (hci : ∀ l, star (L.ci l) = L.cbi l) (l m : Fin r) :
    ∀ x ∈ hol (⟨L.p l, L.c l, L.ci l⟩ : Site A), ∀ y ∈ hol (⟨L.p m, L.c m, L.ci m⟩ : Site A), Commute x (star y) := by
  have hf : ∀ x ∈ L.fns, ∀ y ∈ L.fns, Commute x y := fun x hx y hy => L.fns_comm x hx y hy
  intro x hx y hy
  simp only [hol, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hy with rfl | rfl | rfl
  · rw [hp]
    refine Commute.neg_right ?_
    rcases hx with rfl | rfl | rfl
    · exact L.p_pb l m
    · exact (L.pb_c m l).symm
    · exact (L.pb_ci m l).symm
  · rw [hc]
    rcases hx with rfl | rfl | rfl
    · exact L.p_cb l m
    · exact hf _ (Or.inl (Or.inl (Or.inl (Or.inl ⟨l, rfl⟩)))) _ (Or.inl (Or.inl (Or.inr ⟨m, rfl⟩)))
    · exact hf _ (Or.inl (Or.inl (Or.inl (Or.inr ⟨l, rfl⟩)))) _ (Or.inl (Or.inl (Or.inr ⟨m, rfl⟩)))
  · rw [hci]
    rcases hx with rfl | rfl | rfl
    · exact L.p_cbi l m
    · exact hf _ (Or.inl (Or.inl (Or.inl (Or.inl ⟨l, rfl⟩)))) _ (Or.inl (Or.inr ⟨m, rfl⟩))
    · exact hf _ (Or.inl (Or.inl (Or.inl (Or.inr ⟨l, rfl⟩)))) _ (Or.inl (Or.inr ⟨m, rfl⟩))

theorem hol_comm_hol (L : R.LevelData A r) {l m : Fin r} (hlm : l ≠ m) :
    ∀ x ∈ hol (⟨L.p l, L.c l, L.ci l⟩ : Site A), ∀ y ∈ hol (⟨L.p m, L.c m, L.ci m⟩ : Site A), Commute x y := by
  have hf : ∀ x ∈ L.fns, ∀ y ∈ L.fns, Commute x y := fun x hx y hy => L.fns_comm x hx y hy
  have hlm' : m ≠ l := fun h => hlm h.symm
  intro x hx y hy
  simp only [hol, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
  · exact L.p_p l m
  · have := L.p_c l m; rw [if_neg hlm, add_zero] at this; exact this
  · have := L.p_ci l m; rw [if_neg hlm, sub_zero] at this; exact this
  · have := L.p_c m l; rw [if_neg hlm', add_zero] at this; exact this.symm
  · exact hf _ (Or.inl (Or.inl (Or.inl (Or.inl ⟨l, rfl⟩)))) _ (Or.inl (Or.inl (Or.inl (Or.inl ⟨m, rfl⟩))))
  · exact hf _ (Or.inl (Or.inl (Or.inl (Or.inl ⟨l, rfl⟩)))) _ (Or.inl (Or.inl (Or.inl (Or.inr ⟨m, rfl⟩))))
  · have := L.p_ci m l; rw [if_neg hlm', sub_zero] at this; exact this.symm
  · exact hf _ (Or.inl (Or.inl (Or.inl (Or.inr ⟨l, rfl⟩)))) _ (Or.inl (Or.inl (Or.inl (Or.inl ⟨m, rfl⟩))))
  · exact hf _ (Or.inl (Or.inl (Or.inl (Or.inr ⟨l, rfl⟩)))) _ (Or.inl (Or.inl (Or.inl (Or.inr ⟨m, rfl⟩))))

theorem good_of_adm {S : Type} (st : Fr.Start A) (w : List (Letter ℂ S)) (hw : Fr.admitted st w) : Good w := by
  obtain ⟨h1, h2, -, h4⟩ := hw
  refine ⟨h1, h2, h4.imp fun {l l'} h => ?_⟩
  unfold RegL
  split_ifs
  · simpa using h 1 (by norm_num)
  · intro h'
    apply h (-1) (by norm_num)
    push_cast
    linear_combination -h'

end Abstract

section Pairs

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem pair_operator_commute {a b c d : Module.End ℂ V} (h1 : a * c = c * a) (h2 : d * b = b * d) :
    (mkP a b : Pr V) * mkP c d = mkP c d * mkP a b := by
  refine Prod.ext ?_ ?_
  · show a * c = c * a
    exact h1
  · show MulOpposite.op b * MulOpposite.op d = MulOpposite.op d * MulOpposite.op b
    rw [← MulOpposite.op_mul, ← MulOpposite.op_mul, h2]

end Pairs

section Levels

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem star_site_ops {X : ActualOps k r z z' π π'} {L : R.LevelData (Pr (RadSp k r z z' π π')) r}
    (hL : IsActualLevel X L) :
    (∀ l, star (L.p l) = -L.pb l) ∧ (∀ l, star (L.c l) = L.cb l) ∧ ∀ l, star (L.ci l) = L.cbi l := by
  obtain ⟨hp, hpb, hc, hci, hcb, hcbi, -⟩ := hL
  have hs : ∀ a b : Module.End ℂ (RadSp k r z z' π π'), star (mkP a b : Pr (RadSp k r z z' π π')) = mkP b a :=
    fun a b => rfl
  refine ⟨fun l => ?_, fun l => ?_, fun l => ?_⟩
  · rw [hp, hpb, hs]
    refine Prod.ext rfl ?_
    show MulOpposite.op (X.op l 0) = -MulOpposite.op (-X.op l 0)
    rw [← MulOpposite.op_neg, neg_neg]
  · rw [hc, hcb, hs]
  · rw [hci, hcbi, hs]

theorem isSite_actual {X : ActualOps k r z z' π π'} {L : R.LevelData (Pr (RadSp k r z z' π π')) r}
    (hL : IsActualLevel X L) (l : Fin r) : IsSite (site L l) := by
  obtain ⟨hp, hc, hci⟩ := star_site_ops hL
  refine ⟨⟨L.c_ci l, L.ci_c l, ?_⟩, hol_comm_star L hp hc hci l l⟩
  have h := L.p_c l l
  rw [if_pos rfl] at h
  exact h

theorem QQi_mem_all (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (st : Fr.Start (Pr (RadSp k r z z' π π')))
    (𝒜 : StarSubalgebra ℂ (Pr (RadSp k r z z' π π'))) (i : Fin (r + 1)) (Y : ℂ)
    (hQ : ∀ a b, st.QQ Y a b ∈ 𝒜)
    (hS : ∀ l : Fin r, i.val ≤ l.val → L.p l ∈ 𝒜 ∧ L.c l ∈ 𝒜 ∧ L.ci l ∈ 𝒜) (a b : Fin 2) :
    QQi L st i Y a b ∈ 𝒜 := by
  have hmul : ∀ M N : M2 (Pr (RadSp k r z z' π π')), (∀ a b, M a b ∈ 𝒜) → (∀ a b, N a b ∈ 𝒜) →
      ∀ a b, (M * N) a b ∈ 𝒜 := by
    intro M N hM hN a b
    rw [Matrix.mul_apply]
    exact Subalgebra.sum_mem _ fun c _ => Subalgebra.mul_mem _ (hM a c) (hN c b)
  have hone : ∀ a b, (1 : M2 (Pr (RadSp k r z z' π π'))) a b ∈ 𝒜 := by
    intro a b
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hct : ∀ M : M2 (Pr (RadSp k r z z' π π')), (∀ a b, M a b ∈ 𝒜) → ∀ a b, Mᴴ a b ∈ 𝒜 := by
    intro M hM a b
    rw [Matrix.conjTranspose_apply]
    exact star_mem (hM b a)
  have hts : ∀ (Y' : ℂ) (l : Fin r), i.val ≤ l.val → ∀ a b, Ts (site L l) Y' a b ∈ 𝒜 := by
    intro Y' l hl a b
    obtain ⟨hp, hc, hci⟩ := hS l hl
    fin_cases a <;> fin_cases b
    · exact add_mem (algebraMap_mem 𝒜 Y') hp
    · exact neg_mem hc
    · exact hci
    · exact zero_mem _
  have htp : ∀ (Y' : ℂ) (n j : ℕ), r - j = n → i.val ≤ j → ∀ a b, tprod L Y' j a b ∈ 𝒜 := by
    intro Y' n
    induction n with
    | zero =>
      intro j hj hij
      rw [tprod, dite_eq_right (by omega)]
      exact hone
    | succ n ih =>
      intro j hj hij
      rw [tprod, dite_eq_left (by omega)]
      exact hmul _ _ (ih (j + 1) (by omega) (by omega)) (hts Y' ⟨j, by omega⟩ hij)
  unfold QQi
  exact hmul _ _ (hmul _ _ (hct _ (htp _ _ _ rfl le_rfl)) hQ) (htp _ _ _ rfl le_rfl) a b

theorem QQi_castSucc (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (st : Fr.Start (Pr (RadSp k r z z' π π')))
    (l : Fin r) (Y : ℂ) (hY : star Y = Y) :
    QQi L st l.castSucc Y = (Ts (site L l) Y)ᴴ * QQi L st l.succ Y * Ts (site L l) Y := by
  have ht : ∀ Y' : ℂ, tprod L Y' (l.castSucc : ℕ) = tprod L Y' (l.succ : ℕ) * Ts (site L l) Y' := by
    intro Y'
    rw [tprod, dite_eq_left (show (l.castSucc : ℕ) < r from l.isLt)]
    rfl
  unfold QQi
  rw [ht, ht, hY, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

end Levels

section Top

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

theorem qqCommutes_actual (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (hD : IsData P z z' π π' X μ L st l0) (l : Fin P.r) : QQCommutes (QQi L st l.succ) (site L l) := by
  obtain ⟨hpl, -, hL, hQQ, -⟩ := hD
  obtain ⟨sp, sc, sci⟩ := star_site_ops hL
  obtain ⟨hp, -, hc, hci, -⟩ := hL
  have ht : ∀ (i : Fin 6) (Y : ℂ) (a b : Fin 2), X.t Y a b * X.op l i = X.op l i * X.t Y a b :=
    fun i => (Formalism.FourierDecayAlt.P.level_coordinates_commute Wp Wq P z z' π π' hpl X l i).1
  have htn : ∀ (i : Fin 6) (Y : ℂ) (a b : Fin 2), X.t Y a b * -X.op l i = -X.op l i * X.t Y a b := by
    intro i Y a b; rw [mul_neg, neg_mul, ht]
  intro Y
  have hmem : ∀ a b, QQi L st l.succ Y a b ∈ StarSubalgebra.centralizer ℂ (hol (site L l)) := by
    refine QQi_mem_all L st _ l.succ Y ?_ ?_
    · intro a b
      rw [hQQ Y, Matrix.smul_apply]
      refine SMulMemClass.smul_mem _ ?_
      simp only [ActualOps.QQ, Matrix.of_apply]
      rw [StarSubalgebra.mem_centralizer_iff]
      intro g hg
      simp only [hol, site, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl
      · rw [hp l]
        exact ⟨pair_operator_commute (ht _ _ _ _).symm (htn _ _ _ _), pair_operator_commute (htn _ _ _ _).symm (ht _ _ _ _)⟩
      · rw [hc l]
        exact ⟨pair_operator_commute (ht _ _ _ _).symm (ht _ _ _ _), pair_operator_commute (ht _ _ _ _).symm (ht _ _ _ _)⟩
      · rw [hci l]
        exact ⟨pair_operator_commute (ht _ _ _ _).symm (ht _ _ _ _), pair_operator_commute (ht _ _ _ _).symm (ht _ _ _ _)⟩
    · intro m hm
      have hne : l ≠ m := by
        intro h; rw [← h, Fin.val_succ] at hm; omega
      have key : ∀ y ∈ hol (site L m), y ∈ StarSubalgebra.centralizer ℂ (hol (site L l)) := by
        intro y hy
        rw [StarSubalgebra.mem_centralizer_iff]
        intro g hg
        exact ⟨hol_comm_hol L hne g hg y hy, (hol_comm_star L sp sc sci m l y hy g hg).symm⟩
      exact ⟨key _ (by simp [hol, site]), key _ (by simp [hol, site]), key _ (by simp [hol, site])⟩
  intro a b x hx
  have h := hmem a b
  rw [StarSubalgebra.mem_centralizer_iff] at h
  rcases hx with hx | hx
  · exact (h x hx).1.symm
  · have h2 := (h _ hx).2
    rw [star_star] at h2
    exact h2.symm

theorem siteStep_actual (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (w : List (Letter ℂ S)) (hD : IsData P z z' π π' X μ L st l0) (hw : WordOK P z z' π π' st l0 w) (l : Fin P.r) :
    star (bTl L l w) * RRi L st l.succ w * bTl L l w = RRi L st l.castSucc w := (by
    have hL := hD.2.2.1
    exact Formalism.FourierDecayAlt.P.site_exchange_relation ℂ _ S (site L l) (QQi L st l.succ) (QQi L st l.castSucc) w
      (isSite_actual hL l) (qqCommutes_actual P z z' π π' X μ L st l0 hD l)
      (fun Y hY => QQi_castSucc L st l Y hY) (good_of_adm st w hw.1))

end Top

end Formalism.FourierDecayAlt.P5.HerA
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.AeSS
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.FourierDecayAlt.P.S3dx4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

theorem ae_mem_UWset_and_mem_Nset {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    [SigmaFinite D.μW] [SigmaFinite D.μN] :
    ∀ᵐ p ∂(D.μW.prod D.μN), Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r D.z ∧ Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r := by
  have hW : ∀ᵐ x ∂D.μW, Matrix.of x ∈ Formalism.QuantumDeterminants.UWset k r D.z := by
    rw [ae_iff]
    exact measure_mono_null (fun x hx => hx) D.haarW.conc
  have hN : ∀ᵐ x ∂D.μN, Matrix.of x ∈ Formalism.QuantumDeterminants.Nset k r := by
    rw [ae_iff]
    exact measure_mono_null (fun x hx => hx) D.haarN.conc
  exact (Measure.quasiMeasurePreserving_fst.ae hW).and (Measure.quasiMeasurePreserving_snd.ae hN)

set_option maxHeartbeats 800000 in
theorem quadB_of (hNI : NormInv) (hGS : GrowthS) (hGG : GrowthG) (hDD : DecDD) (hIn : Inputs) {k r : ℕ}
    {Wp Wq : Type}
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    (D : B.RealPlaceData k r Wp Wq) {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {h : ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Mx k r → (H →L[ℂ] H)} {w0 : H}
    {u : Fin k → ℝ} {νq : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hS1 : Side k r ε lam h σ w0 D.z Formalism.QuantumDeterminants.cStd u D.π D.μW D.μN D.μG νq)
    {l : H → Wp}
    (hbe : ∀ x ∈ DDsp σ w0, ∀ y ∈ DDsp σ w0,
        be D.z Formalism.QuantumDeterminants.cStd D.π σ D.μW D.μN x y = (innerSL ℂ (l y)).smulRight (l x)) :
    ∫⁻ zz, ∫⁻ zz', ∫⁻ s,
      ((‖⟪σ (Matrix.of zz) w0, σ (Matrix.of s) (σ (Matrix.of zz') w0)⟫_ℂ‖₊ : ℝ≥0) : ℝ≥0∞) *
        ((‖l (σ (Matrix.of zz) w0)‖₊ : ℝ≥0) : ℝ≥0∞) * ((‖l (σ (Matrix.of zz') w0)‖₊ : ℝ≥0) : ℝ≥0∞)
      ∂(muSof D.μW D.μN) ∂νq ∂νq < ⊤ := by
  have hS1' := hS1
  obtain ⟨hl, hds, -, hG, hw0, hz1, hT, -, hπ, hW, hN, hGm, hq⟩ := hS1'
  have : SigmaFinite D.μW := hW.1
  have : SigmaFinite D.μN := hN.1
  have : SigmaFinite D.μG := hGm.1
  have hGc : ∀ᵐ x ∂D.μG, Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
    rw [ae_iff]; simpa using hGm.2.2.1
  have hw0DD := cmHalfIntegralGenerator_mem_algebraicClosure hds w0
  have hf1 := DDSmoothness.muSof_facts hW hN
  have hae1 := DDSmoothness.ae_UH_of_quot hGm.2.2.1 hf1.1 hf1.2 hq
  by_cases hA : ∃ v ∈ DDsp σ w0, l v ≠ 0
  swap
  · push Not at hA
    calc _ ≤ ∫⁻ zz, (0 : ℝ≥0∞) ∂νq := by
          apply lintegral_mono_ae
          filter_upwards [hae1] with zz hzz
          simp [hA _ (dd_stable hds hzz w0 hw0DD)]
      _ < ⊤ := by simp
  obtain ⟨v, hv, hlv⟩ := hA
  obtain ⟨e0, he0, hee0⟩ := coef_ext hds w0 w0
  obtain ⟨e1, he1, hee1⟩ := coef_ext hds v w0
  obtain ⟨C0, hC0⟩ := hDD hIn k r ε lam h H σ w0 Wp D.z Formalism.QuantumDeterminants.cStd u D.π D.μW D.μN D.μG νq hS1 w0 hw0DD
    w0 hw0DD
  obtain ⟨C1, hC1⟩ := hDD hIn k r ε lam h H σ w0 Wp D.z Formalism.QuantumDeterminants.cStd u D.π D.μW D.μN D.μG νq hS1 w0 hw0DD v hv
  have hb0e : ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ‖e0 y‖ ≤ C0 * B.gN y ^ (-aOf r h) :=
    fun y hy => by rw [hee0 y hy]; exact hC0 y hy
  have hb1 : ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ‖e1 y‖ ≤ C1 * B.gN y ^ (-aOf r h) :=
    fun y hy => by rw [hee1 y hy]; exact hC1 y hy
  have h4 := gap4 hG
  have hAG := ag_nonneg k r
  have hn2 : (0 : ℝ) ≤ 9 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 := by positivity
  obtain ⟨ee, heedef⟩ : ∃ ee : ℝ, ee = AG k r + 1 := ⟨_, rfl⟩
  have hee0' : 0 ≤ ee := by rw [heedef]; linarith
  have heea : ee ≤ aOf r h := by rw [heedef]; linarith
  have hLs : ∫⁻ p, ‖B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (-ee)‖ₑ ∂(D.μW.prod D.μN) < ⊤ :=
    (hGS k r D.z D.μW D.μN D.μG νq ee hz1 hT hW hN hGm hq (by rw [heedef]; linarith)).hasFiniteIntegral
  obtain ⟨Ls, hLsdef⟩ : ∃ Ls : ℝ≥0∞, Ls = ∫⁻ p, ‖B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (-ee)‖ₑ ∂(D.μW.prod D.μN) :=
    ⟨_, rfl⟩
  rw [← hLsdef] at hLs
  have hKg : ∫⁻ x, ‖B.gN (Matrix.of x) ^ (-(aOf r h - ee))‖ₑ ∂D.μG < ⊤ :=
    (hGG k r D.μG _ hGm (by rw [heedef]; linarith)).hasFiniteIntegral
  have hpUH : ∀ᵐ p ∂(D.μW.prod D.μN), Matrix.of p.1 * Matrix.of p.2 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
    (prod_ae hW hN).mono fun p hp => DDSmoothness.uh_mul hp.1.1 hp.2.1
  obtain ⟨K1, hK1⟩ : ∃ K1 : ℝ≥0∞, K1 = ‖((‖l v‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * ‖l v‖ₑ := ⟨_, rfl⟩
  have hK : K1 * K1 ≠ ⊤ := by rw [hK1]; simp [ENNReal.mul_eq_top]
  have hA1m := Aext_meas he1
  have hI1m := Iint_meas hA1m (D.μW.prod D.μN)
  obtain ⟨LL, hLL⟩ : ∃ LL : Formalism.QuantumDeterminants.Mt k r → Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞, LL = Lam1 e0 (D.μW.prod D.μN) := ⟨_, rfl⟩
  have hLLm : Measurable (fun t : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => LL t.1 t.2) := by
    rw [hLL]; exact measurable_lambda_integral he0 (D.μW.prod D.μN)
  have step1 : ∀ᵐ zz ∂νq, ∀ᵐ zz' ∂νq, ∫⁻ s,
      ((‖⟪σ (Matrix.of zz) w0, σ (Matrix.of s) (σ (Matrix.of zz') w0)⟫_ℂ‖₊ : ℝ≥0) : ℝ≥0∞) *
        ((‖l (σ (Matrix.of zz) w0)‖₊ : ℝ≥0) : ℝ≥0∞) * ((‖l (σ (Matrix.of zz') w0)‖₊ : ℝ≥0) : ℝ≥0∞)
      ∂(muSof D.μW D.μN) ≤
      (K1 * K1) * (Iint (Aext e1) (D.μW.prod D.μN) zz * (Iint (Aext e1) (D.μW.prod D.μN) zz' * LL zz zz')) := by
    filter_upwards [hae1] with zz hzz
    filter_upwards [hae1] with zz' hzz'
    have bl : ‖l (σ (Matrix.of zz) w0)‖ₑ ≤ K1 * Iint (Aext e1) (D.μW.prod D.μN) zz := by
      rw [hK1]; exact l_le_I (c := Formalism.QuantumDeterminants.cStd) hds hT hπ hW hN hbe hv hlv hw0DD hee1 hzz
    have bl' : ‖l (σ (Matrix.of zz') w0)‖ₑ ≤ K1 * Iint (Aext e1) (D.μW.prod D.μN) zz' := by
      rw [hK1]; exact l_le_I (c := Formalism.QuantumDeterminants.cStd) hds hT hπ hW hN hbe hv hlv hw0DD hee1 hzz'
    have hc : ‖l (σ (Matrix.of zz) w0)‖ₑ * ‖l (σ (Matrix.of zz') w0)‖ₑ ≠ ⊤ :=
      ENNReal.mul_ne_top enorm_ne_top enorm_ne_top
    have hqi := quad_inner1 hds w0 he0 hee0 hf1.2 hzz hzz'
    rw [← hLL] at hqi
    simp only [← enorm_eq_nnnorm]
    calc ∫⁻ s, ‖⟪σ (Matrix.of zz) w0, σ (Matrix.of s) (σ (Matrix.of zz') w0)⟫_ℂ‖ₑ *
          ‖l (σ (Matrix.of zz) w0)‖ₑ * ‖l (σ (Matrix.of zz') w0)‖ₑ ∂(muSof D.μW D.μN)
        = ∫⁻ s, ‖⟪σ (Matrix.of zz) w0, σ (Matrix.of s) (σ (Matrix.of zz') w0)⟫_ℂ‖ₑ *
          (‖l (σ (Matrix.of zz) w0)‖ₑ * ‖l (σ (Matrix.of zz') w0)‖ₑ) ∂(muSof D.μW D.μN) :=
          lintegral_congr fun s => mul_assoc _ _ _
      _ = (∫⁻ s, ‖⟪σ (Matrix.of zz) w0, σ (Matrix.of s) (σ (Matrix.of zz') w0)⟫_ℂ‖ₑ ∂(muSof D.μW D.μN)) *
          (‖l (σ (Matrix.of zz) w0)‖ₑ * ‖l (σ (Matrix.of zz') w0)‖ₑ) := lintegral_mul_const' _ _ hc
      _ = LL zz zz' * (‖l (σ (Matrix.of zz) w0)‖ₑ * ‖l (σ (Matrix.of zz') w0)‖ₑ) := by rw [hqi]
      _ ≤ LL zz zz' * ((K1 * Iint (Aext e1) (D.μW.prod D.μN) zz) * (K1 * Iint (Aext e1) (D.μW.prod D.μN) zz')) := by
          gcongr
      _ = (K1 * K1) * (Iint (Aext e1) (D.μW.prod D.μN) zz * (Iint (Aext e1) (D.μW.prod D.μN) zz' * LL zz zz')) := by
          ring
  have hinvR : ∀ zz, ∀ᵐ z ∂νq, ∀ᵐ q ∂(D.μW.prod D.μN),
      LL zz (fun i j => (Matrix.of q.1 * Matrix.of q.2 * Matrix.of z) i j) = LL zz z := by
    intro zz
    rw [hLL]
    exact Filter.Eventually.of_forall fun z => (ae_mem_UWset_and_mem_Nset D).mono
      fun q hq0 => lambda_right_translation he0 D.haarW D.haarN hz1 hT hq0.1 hq0.2 zz z
  have hinvL : ∀ᵐ z ∂νq, ∀ᵐ p ∂(D.μW.prod D.μN),
      (∫⁻ y, Aext e1 y * LL (fun i j => (Matrix.of p.1 * Matrix.of p.2 * Matrix.of z) i j) y ∂D.μG) =
        ∫⁻ y, Aext e1 y * LL z y ∂D.μG := by
    rw [hLL]
    exact Filter.Eventually.of_forall fun z => (prod_ae hW hN).mono
      fun p hp0 => lintegral_congr fun y => by rw [lambda_left_translation he0 hW hN hz1 hp0.1 hp0.2 z y]
  have hLz : ∀ zz, Measurable (fun y => LL zz y) := fun zz => hLLm.comp (measurable_const.prodMk measurable_id)
  have hΦm : Measurable (fun x => ∫⁻ y, Aext e1 y * LL x y ∂D.μG) :=
    ((hA1m.comp measurable_snd).mul hLLm).lintegral_prod_right'
  obtain ⟨Fx, hFx⟩ : ∃ Fx : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞, Fx = fun x => ‖B.gN (Matrix.of x) ^ (-(aOf r h - ee))‖ₑ :=
    ⟨_, rfl⟩
  have hFxm : Measurable Fx := by
    rw [hFx]; exact (((gN_cont.comp mt_cont).measurable).pow_const _).enorm
  have hKg' : ∫⁻ x, Fx x ∂D.μG < ⊤ := by rw [hFx]; exact hKg
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ≥0∞, c = ENNReal.ofReal |C1| * ENNReal.ofReal |C1| * (ENNReal.ofReal |C0| * Ls) :=
    ⟨_, rfl⟩
  have hc : c ≠ ⊤ := by
    rw [hcdef]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hLs.ne)
  have hgpos : ∀ x : Mx k r, x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) → 0 < B.gN x :=
    fun x hx => lt_of_lt_of_le one_pos ((hNI k r).2 x hx).2
  have hpt : ∀ᵐ x ∂D.μG, Aext e1 x * ∫⁻ y, Aext e1 y * LL x y ∂D.μG ≤ ∫⁻ y, c * (Fx x * Fx y) ∂D.μG := by
    filter_upwards [hGc] with x hx
    rw [← lintegral_const_mul' (Aext e1 x) _ (by unfold Aext; exact enorm_ne_top)]
    apply lintegral_mono_ae
    filter_upwards [hGc] with y hy
    have hL := lambda_integral_bound hNI hb0e hee0' heea hpUH hx hy
    rw [← hLL, ← hLsdef] at hL
    have hx0 := hgpos _ hx
    have hy0 := hgpos _ hy
    have w1 := e_weight (b := ee) hb1 hx hx0
    have w2 := e_weight (b := ee) hb1 hy hy0
    have split : ENNReal.ofReal (|C0| * (B.gN (Matrix.of x) * B.gN (Matrix.of y)) ^ ee) =
        ENNReal.ofReal |C0| * (ENNReal.ofReal (B.gN (Matrix.of x) ^ ee) * ENNReal.ofReal (B.gN (Matrix.of y) ^ ee)) := by
      rw [Real.mul_rpow hx0.le hy0.le, ENNReal.ofReal_mul (abs_nonneg _),
        ENNReal.ofReal_mul (Real.rpow_nonneg hx0.le _)]
    have hFxx : Fx x = ‖B.gN (Matrix.of x) ^ (-(aOf r h - ee))‖ₑ := by rw [hFx]
    have hFxy : Fx y = ‖B.gN (Matrix.of y) ^ (-(aOf r h - ee))‖ₑ := by rw [hFx]
    calc Aext e1 x * (Aext e1 y * LL x y)
        ≤ Aext e1 x * (Aext e1 y * (ENNReal.ofReal (|C0| * (B.gN (Matrix.of x) * B.gN (Matrix.of y)) ^ ee) * Ls)) := by
          gcongr
      _ = (Aext e1 x * ENNReal.ofReal (B.gN (Matrix.of x) ^ ee)) *
            (Aext e1 y * ENNReal.ofReal (B.gN (Matrix.of y) ^ ee)) * (ENNReal.ofReal |C0| * Ls) := by
          rw [split]; ring
      _ ≤ (ENNReal.ofReal |C1| * Fx x) * (ENNReal.ofReal |C1| * Fx y) * (ENNReal.ofReal |C0| * Ls) := by
          rw [hFxx, hFxy]
          exact mul_le_mul' (mul_le_mul' w1 w2) le_rfl
      _ = c * (Fx x * Fx y) := by rw [hcdef]; ring
  calc _ ≤ ∫⁻ zz, ∫⁻ zz', (K1 * K1) * (Iint (Aext e1) (D.μW.prod D.μN) zz *
          (Iint (Aext e1) (D.μW.prod D.μN) zz' * LL zz zz')) ∂νq ∂νq :=
        lintegral_mono_ae (step1.mono fun zz h => lintegral_mono_ae h)
    _ = (K1 * K1) * ∫⁻ zz, Iint (Aext e1) (D.μW.prod D.μN) zz *
          ∫⁻ zz', Iint (Aext e1) (D.μW.prod D.μN) zz' * LL zz zz' ∂νq ∂νq :=
        pull2 _ _ _ hK (fun zz => hI1m.mul (hLz zz))
    _ = (K1 * K1) * ∫⁻ zz, Iint (Aext e1) (D.μW.prod D.μN) zz * ∫⁻ y, Aext e1 y * LL zz y ∂D.μG ∂νq := by
        congr 1; apply lintegral_congr; intro zz; congr 1
        exact unfold_Iint hq hA1m (hLz zz) (hinvR zz)
    _ = (K1 * K1) * ∫⁻ x, Aext e1 x * ∫⁻ y, Aext e1 y * LL x y ∂D.μG ∂D.μG := by
        congr 1
        exact unfold_Iint hq hA1m hΦm hinvL
    _ ≤ (K1 * K1) * ∫⁻ x, ∫⁻ y, c * (Fx x * Fx y) ∂D.μG ∂D.μG := by
        gcongr 1
        exact lintegral_mono_ae hpt
    _ = (K1 * K1) * (c * ((∫⁻ x, Fx x ∂D.μG) * ∫⁻ y, Fx y ∂D.μG)) := by rw [final2 Fx hFxm hc]
    _ < ⊤ := ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hK)
          (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hc) (ENNReal.mul_lt_top hKg' hKg'))

end Formalism.FourierDecayAlt.P.S3dx4
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.DetCornerMatrixLevelZero
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.DframeCommute
noncomputable section

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.Dx2.DF
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.PBI

section commute

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem inWb_of_zero (hr : r = 0) (v : Fin (2 * r + k + 1) → ℂ) : inWb k r v := by
  subst hr; intro i hi; exfalso; have := i.isLt; omega

theorem prW_perp0 (hr : r = 0) (z v : Fin (2 * r + k + 1) → ℂ) (hvz : herm (Hpk k r) v z = 0) :
    D.prW k r z v = v := by
  rw [prW_eq, Wb_of_inWb (inWb_of_zero hr v), hvz, zero_div, zero_smul, sub_zero]

theorem herm_unit {g : B.Mat k r} (hg : g ∈ UH (Hpk k r)) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (g *ᵥ v) w = herm (Hpk k r) v (g⁻¹ *ᵥ w) := by
  have hu := WeylGroupFacts.isUnit_of_uh hg
  conv_lhs => rw [show w = g *ᵥ (g⁻¹ *ᵥ w) by rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu,
    Matrix.one_mulVec]]
  exact herm_m0_mulVec_invariant g hg v _

theorem dframe_commute (S : B.RealPlaceData k r Wp Wq) (hr : r = 0) {ν' : Fin (2 * r + k + 1) → ℂ} {m₀ : B.Mat k r}
    (hbase : D.IsBaseFrame S ν' m₀) {γ : B.Mat k r} (hγ : γ ∈ B.GV k r) (hD : D.IsDFrame S ν' m₀ γ)
    (hdet : (Zhat k r S.z S.z' γ).det ≠ 0) {hB : B.Mat k r} (hhB : hB ∈ UWset k r S.z') (hBν : hB *ᵥ ν' = ν') :
    (m₀ * hB * m₀⁻¹) * γ * hB⁻¹ = γ := by
  obtain ⟨hν, hνz, hνν, ⟨hmU, hmfix⟩, hmz⟩ := hbase
  obtain ⟨⟨a1, ha1, h1⟩, ⟨a2, ha2, h2⟩, h3⟩ := hD
  have hz := S.z_mem
  have hz' := S.z'_mem
  have um := WeylGroupFacts.isUnit_of_uh hmU
  have uγ := WeylGroupFacts.isUnit_of_uh hγ
  have uB := WeylGroupFacts.isUnit_of_uh hhB.1
  set ζ := (Zhat k r S.z S.z' γ).det with hζdef
  have hzν : herm (Hpk k r) S.z' ν' = 0 := herm_zν hνz
  have hzz0 : herm (Hpk k r) S.z' S.z' ≠ 0 := by
    rw [herm_self_alt]; have := S.T'_pos; intro h; simp at h; linarith
  have hzz0' : herm (Hpk k r) S.z S.z ≠ 0 := by
    rw [herm_self_alt]; have := S.T_pos; intro h; simp at h; linarith

  have hlast : ∀ b : Fin (r + 1), b = Fin.last r := fun b => Fin.ext (by have := b.isLt; simp only [Fin.val_last]; omega)
  have hfz : ∀ (x : Fin (2 * r + k + 1) → ℂ) (b : Fin (r + 1)), fvec k r x b = x := by
    intro x b; rw [hlast b]; exact fvec_lastI x
  have hadj : ∀ a b : Fin (r + 1), (Zhat k r S.z S.z' γ).adjugate a b = 1 := by
    subst hr; intro a b
    rw [Matrix.adjugate_fin_one]; fin_cases a; fin_cases b; rfl
  have hcofR : D.cofR S γ = γ *ᵥ S.z' := by
    unfold D.cofR; subst hr; simp [hadj, hfz]
  have hcofL : D.cofL S γ = S.z := by
    unfold D.cofL; subst hr; simp [hadj, hfz]
  rw [hcofR, prW_eq, Wb_of_inWb (inWb_of_zero hr _)] at h1
  rw [hcofL, prW_eq, Wb_of_inWb (inWb_of_zero hr _)] at h2

  set c1 := herm (Hpk k r) (γ *ᵥ S.z') S.z / herm (Hpk k r) S.z S.z with hc1
  set c2 := herm (Hpk k r) (γ⁻¹ *ᵥ S.z) S.z' / herm (Hpk k r) S.z' S.z' with hc2
  have hγz' : γ *ᵥ S.z' = c1 • S.z + ((a1 : ℂ) * ζ) • (m₀ *ᵥ ν') := by rw [← h1]; abel
  have hγiz : γ⁻¹ *ᵥ S.z = c2 • S.z' + ((a2 : ℂ) * conj ζ) • ν' := by rw [← h2]; abel
  set μ := Real.sqrt (Tz k r S.z' / Tz k r S.z) with hμdef
  have hμ : 0 < μ := Real.sqrt_pos.2 (div_pos S.T'_pos S.T_pos)
  have hμ' : (μ : ℂ) ≠ 0 := by exact_mod_cast hμ.ne'
  have hmiz : m₀⁻¹ *ᵥ S.z = (μ : ℂ)⁻¹ • S.z' := by
    have : S.z = (μ : ℂ)⁻¹ • (m₀ *ᵥ S.z') := by rw [hmz, smul_smul, inv_mul_cancel₀ hμ', one_smul]
    rw [this, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ um, Matrix.one_mulVec]
  set σ := m₀⁻¹ * γ with hσdef

  have hσz' : σ *ᵥ S.z' = (c1 * (μ : ℂ)⁻¹) • S.z' + ((a1 : ℂ) * ζ) • ν' := by
    rw [hσdef, ← Matrix.mulVec_mulVec, hγz', Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hmiz,
      Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ um, Matrix.one_mulVec, smul_smul]
  have ha2ζ : (a2 : ℂ) * conj ζ ≠ 0 := by
    refine mul_ne_zero (by exact_mod_cast ha2.ne') ?_
    simpa using hdet
  have hγν : γ *ᵥ ν' = ((a2 : ℂ) * conj ζ)⁻¹ • (S.z - c2 • (γ *ᵥ S.z')) := by
    have e : γ *ᵥ (γ⁻¹ *ᵥ S.z) = S.z := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ uγ, Matrix.one_mulVec]
    rw [hγiz, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul] at e
    rw [← e]
    rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ha2ζ, one_smul]
  have hσν : σ *ᵥ ν' = (((a2 : ℂ) * conj ζ)⁻¹ * (μ : ℂ)⁻¹) • S.z' -
      (((a2 : ℂ) * conj ζ)⁻¹ * c2) • (σ *ᵥ S.z') := by
    simp only [hσdef, ← Matrix.mulVec_mulVec]
    rw [hγν, Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.mulVec_smul, hmiz, smul_sub, smul_smul, smul_smul]

  have hfix : ∀ u, herm (Hpk k r) u S.z' = 0 → herm (Hpk k r) u ν' = 0 → σ *ᵥ u = u := by
    intro u hu1 hu2
    have e1 : herm (Hpk k r) (γ *ᵥ u) S.z = 0 := by
      rw [herm_unit hγ, hγiz, B2x4.herm_add_right, B2x4.herm_smul_right, B2x4.herm_smul_right, hu1, hu2]
      simp
    have e2 : herm (Hpk k r) (γ *ᵥ u) (γ *ᵥ S.z') = 0 := by rw [herm_m0_mulVec_invariant γ hγ, hu1]
    have key := h3 (γ *ᵥ u) (fun a => ⟨by rw [hfz]; exact e1, by rw [hfz]; exact e2⟩)
    rw [prW_perp0 hr S.z _ e1, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ uγ, Matrix.one_mulVec,
      prW_perp0 hr S.z' u hu1] at key
    rw [hσdef, ← Matrix.mulVec_mulVec, key, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ um, Matrix.one_mulVec]

  have hBz' : hB *ᵥ S.z' = S.z' := hhB.2.2
  have hBperp : ∀ u, herm (Hpk k r) u S.z' = 0 → herm (Hpk k r) u ν' = 0 →
      herm (Hpk k r) (hB *ᵥ u) S.z' = 0 ∧ herm (Hpk k r) (hB *ᵥ u) ν' = 0 := by
    intro u h1u h2u
    refine ⟨?_, ?_⟩
    · conv_lhs => rw [← hBz']
      rw [herm_m0_mulVec_invariant hB hhB.1, h1u]
    · conv_lhs => rw [← hBν]
      rw [herm_m0_mulVec_invariant hB hhB.1, h2u]

  have hcomm : σ * hB = hB * σ := by
    refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
    simp only [Matrix.toLin'_apply]
    set α := herm (Hpk k r) v S.z' / herm (Hpk k r) S.z' S.z' with hα
    set β := herm (Hpk k r) v ν' with hβ
    set v0 := v - α • S.z' - β • ν' with hv0
    have hv0z : herm (Hpk k r) v0 S.z' = 0 := by
      rw [hv0, B2x4.herm_sub_left, B2x4.herm_sub_left, B2x4.herm_smul_left, B2x4.herm_smul_left, hνz, hα]
      field_simp; ring
    have hv0ν : herm (Hpk k r) v0 ν' = 0 := by
      rw [hv0, B2x4.herm_sub_left, B2x4.herm_sub_left, B2x4.herm_smul_left, B2x4.herm_smul_left, hzν, hνν, hβ]
      ring
    have hv : v = v0 + α • S.z' + β • ν' := by rw [hv0]; abel
    obtain ⟨hb1, hb2⟩ := hBperp v0 hv0z hv0ν
    rw [← Matrix.mulVec_mulVec v σ hB, ← Matrix.mulVec_mulVec v hB σ, hv]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hBz', hBν, hfix v0 hv0z hv0ν,
      hfix (hB *ᵥ v0) hb1 hb2]
    rw [hσν, hσz']
    simp only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, hBz', hBν]

  have hγσ : γ = m₀ * σ := by rw [hσdef, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ um, Matrix.one_mul]
  rw [hγσ]
  calc m₀ * hB * m₀⁻¹ * (m₀ * σ) * hB⁻¹ = m₀ * hB * (m₀⁻¹ * m₀) * σ * hB⁻¹ := by simp only [Matrix.mul_assoc]
    _ = m₀ * (σ * hB) * hB⁻¹ := by rw [Matrix.nonsing_inv_mul _ um, hcomm]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = m₀ * σ := by rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ uB, Matrix.mul_one]

end commute

end Formalism.FourierDecayAlt.P.PBI
end
end

noncomputable section

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.Dx2.DF
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.PBI

section lev

variable {k : ℕ}

theorem det_corner_matrix_level_zero {r' : ℕ} (hr : r' = 0) (z z' : Fin (2 * r' + k + 1) → ℂ) (g : B.Mat k r') :
    (Zhat k r' z z' g).det = Q.zetaL k r' z z' (Fin.last r') g := by
  subst hr
  exact (Matrix.det_fin_one _).trans rfl

end lev

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem grpInt_at_dframe (p : KB.Pl P Wp Wq) {ν'r : Fin (2 * (P.r - P.r) + P.k + 1) → ℂ}
    {m₀r : B.Mat P.k (P.r - P.r)} (hLev : LevFrame p ν'r m₀r)
    (Ψ : Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π
      (p.T.bs P.r).π')
    (x : (Fin (JC.parLev P P.r).r → ℂ) × Q.Mx (JC.parLev P P.r).k (JC.parLev P P.r).r)
    (hx : x ∈ Q.DomR (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z')
    {γ₀ : B.Mat P.k (P.r - P.r)} (hγG : γ₀ ∈ B.GV P.k (P.r - P.r))
    (hζ : Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) γ₀ =
      Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) x.2)
    (hγF : D.IsDFrame (p.T.bs P.r) ν'r m₀r γ₀) :
    GrpInt (p.T.bs P.r) ν'r m₀r ((Ψ : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 γ₀) := by
  have hG : 0 < Complex.normSq (Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) x.2) -
      Tz P.k (P.r - P.r) (p.T.bs P.r).z * Tz P.k (P.r - P.r) (p.T.bs P.r).z' := hx.2.2
  have hT := mul_pos (p.T.bs P.r).T_pos (p.T.bs P.r).T'_pos
  have hdet : (Zhat P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' γ₀).det ≠ 0 := by
    rw [det_corner_matrix_level_zero (Nat.sub_self P.r), hζ]
    intro h0
    rw [h0, map_zero] at hG
    linarith
  have hdom : ((x.1, γ₀) : (Fin (JC.parLev P P.r).r → ℂ) × Q.Mx (JC.parLev P P.r).k (JC.parLev P P.r).r) ∈
      Q.DomR (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z' := by
    refine ⟨hx.1, ⟨hγG, fun a _ => ?_⟩, ?_⟩
    · exfalso
      have ha := a.isLt
      revert ha
      show ¬ (a.val < P.r - P.r)
      omega
    · show 0 < Complex.normSq (Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) γ₀) -
        Tz P.k (P.r - P.r) (p.T.bs P.r).z * Tz P.k (P.r - P.r) (p.T.bs P.r).z'
      rw [hζ]
      exact hG
  obtain ⟨-, -, he⟩ := Ψ.2
  intro hB hhB hBν
  have e := he (x.1, γ₀) hdom _ (Formalism.FourierDecayAlt.P.Topx1.vecw_conj_mem _ hLev.2.2 hhB) _ (Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hhB)
  try dsimp only at e
  have hc := Formalism.FourierDecayAlt.P.PBI.dframe_commute _ (Nat.sub_self P.r) hLev.2.2 hγG hγF hdet hhB hBν
  exact e.symm.trans (congrArg (fun g => (Ψ : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 g) hc)

end place

end Formalism.FourierDecayAlt.P.PBI
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CptCoefContSupp
noncomputable section

open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CompactCoefficientAppend

section coef

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem cptCoef_cont_supp (Bs : B.RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (hF : KB.CptCoef Bs F) :
    ContinuousOn F (B.GV k r) ∧ ∃ R : ℝ, ∀ g ∈ B.GV k r, F g ≠ 0 → B.gN g ≤ R :=
  ⟨Formalism.FourierDecayAlt.P.B5.ckOn_continuousOn hF.1, hF.2.1⟩

end coef

section point

theorem cast_perm_val {m n : ℕ} (e : m = n) (σ : Equiv.Perm (Fin m)) (x : Fin n) :
    ((e ▸ σ) x).val = (σ (Fin.cast e.symm x)).val := by
  subst e; rfl

theorem ptSize_app (h : C.LPt) (n : ℕ) (hh : D.IsLocPt h n) (ζ : ℂ) : D.ptSize (h ++ [(1, ζ)]) = n + 1 := by
  rw [Formalism.FourierDecayAlt.P.Dx2.SL.ptSize_append, hh.2]

theorem perm_app (h : C.LPt) (n : ℕ) (hh : D.IsLocPt h n) (ζ : ℂ) (hζ : ζ ≠ 0) :
    U.hMat (hh.2 ▸ D.ptPerm h) (hh.2 ▸ D.ptDiag h) = D.ptMatN h n ∧ (∀ a, (hh.2 ▸ D.ptDiag h) a ≠ 0) ∧
    D.ptMatN (h ++ [(1, ζ)]) (n + 1) =
      C2.monoP (ptSize_app h n hh ζ ▸ D.ptPerm (h ++ [(1, ζ)])) (ptSize_app h n hh ζ ▸ D.ptDiag (h ++ [(1, ζ)])) ∧
    (∀ a, (ptSize_app h n hh ζ ▸ D.ptDiag (h ++ [(1, ζ)])) a ≠ 0) ∧
    (∀ a : Fin n, (ptSize_app h n hh ζ ▸ D.ptPerm (h ++ [(1, ζ)])).symm a.castSucc =
      ((hh.2 ▸ D.ptPerm h) a).castSucc) := by
  have hq : D.IsLocPt (h ++ [(1, ζ)]) (n + 1) := Formalism.FourierDecayAlt.P.PBI.isLocPt_app h n hh ζ hζ
  obtain ⟨h1, h2⟩ := Formalism.FourierDecayAlt.P.Dx2.VV.ptMatN_monoP' h n hh.2 hh.1
  obtain ⟨h3, h4⟩ := Formalism.FourierDecayAlt.P.Dx2.VV.ptMatN_monoP' (h ++ [(1, ζ)]) (n + 1) (ptSize_app h n hh ζ) hq.1
  refine ⟨?_, h2, h3, h4, ?_⟩
  · rw [h1]
    refine (Formalism.FourierDecayAlt.P.Dx1.monomialMatrix_eq_hMat _ _ ?_).symm
    intro a
    apply Fin.ext
    have e : Fin.cast hh.2.symm ((hh.2 ▸ D.ptPerm h) a) = D.ptPerm h (Fin.cast hh.2.symm a) :=
      Fin.ext (by rw [Fin.val_cast, cast_perm_val])
    rw [cast_perm_val, e, Formalism.FourierDecayAlt.P.Dx1.ptPerm_invol, Fin.val_cast]
  · intro a
    rw [Equiv.symm_apply_eq]
    apply Fin.ext
    have hs := hh.2
    have hb := ((hh.2 ▸ D.ptPerm h) a).isLt
    rw [cast_perm_val, Formalism.FourierDecayAlt.P.Dx1.ptPerm_val, Formalism.FourierDecayAlt.P.Dx2.SL.partner_append 1 ζ h _ (by
      simp only [Fin.val_cast, Fin.val_castSucc]; omega)]
    rw [if_pos (by simp only [Fin.val_cast, Fin.val_castSucc]; omega)]
    simp only [Fin.val_cast, Fin.val_castSucc]
    rw [cast_perm_val]
    have e1 := Formalism.FourierDecayAlt.P.Dx1.ptPerm_val h (D.ptPerm h (Fin.cast hh.2.symm a))
    rw [Formalism.FourierDecayAlt.P.Dx1.ptPerm_invol] at e1
    rw [← e1, Fin.val_cast]

end point

section frame

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem baseFrame_last (p : KB.Pl P Wp Wq) (ν'r : Fin (2 * (P.r - P.r) + P.k + 1) → ℂ) (m₀r : B.Mat P.k (P.r - P.r))
    (hν : D.castV (by omega) (liftVec P.k P.r (P.r - P.r) ν'r) = p.ν')
    (hm : D.castM (by omega) (ιLev P.k P.r (P.r - P.r) m₀r) = p.m₀) :
    D.IsBaseFrame (p.T.bs P.r) ν'r m₀r := by
  have h : P.r + (P.r - P.r) = P.r := by omega
  have e1 : ν'r = Formalism.FourierDecayAlt.P.PBI.nuR p := by
    rw [Formalism.FourierDecayAlt.P.PBI.nuR, ← hν, Formalism.FourierDecayAlt.P.PBI.zL_lift]
  have e2 : m₀r = Formalism.FourierDecayAlt.P.PBI.m0R p := by
    ext i j
    rw [Formalism.FourierDecayAlt.P.PBI.m0R, ← hm]
    simp only [D.castM, Matrix.reindex_apply, Matrix.submatrix_apply, ιLev]
    rw [dite_eq_left (by simp; omega), dite_eq_left (by simp; omega)]
    congr 1 <;> ext <;> simp
  rw [e1, e2]
  exact (Formalism.FourierDecayAlt.P.PBI.levFrame_nuR p).2.2

end frame

end Formalism.FourierDecayAlt.P.CompactCoefficientAppend
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.MeasurePreservingProdRearrange
namespace Formalism.FourierDecayAlt.P.StabilizerDisintegration.ME

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem measurePreserving_prod_rearrange {L M P N : Type*} [MeasurableSpace L] [MeasurableSpace M] [MeasurableSpace P] [MeasurableSpace N]
    (μL : Measure L) (μM : Measure M) (μP : Measure P) (μN : Measure N) [SigmaFinite μL] [SigmaFinite μM]
    [SigmaFinite μP] [SigmaFinite μN] :
    MeasurePreserving (fun p : L × (M × (P × N)) => (p.2.1, ((p.1, p.2.2.1), p.2.2.2)))
      (μL.prod (μM.prod (μP.prod μN))) (μM.prod ((μL.prod μP).prod μN)) := by
  have h1 := (measurePreserving_prodAssoc μL μM (μP.prod μN)).symm
  have h2 := (Measure.measurePreserving_swap (μ := μL) (ν := μM)).prod (MeasurePreserving.id (μP.prod μN))
  have h3 := measurePreserving_prodAssoc μM μL (μP.prod μN)
  have h4 := (MeasurePreserving.id μM).prod (measurePreserving_prodAssoc μL μP μN).symm
  have := h4.comp (h3.comp (h2.comp h1))
  convert this using 1
  funext ⟨l, m, p, n⟩
  rfl

theorem muSS_eq (S : B.RealPlaceData k r Wp Wq) (w : Equiv.Perm (Fin (r + 1)))
    (e : ((C2.Lstidx w → ℂ) × (C2.LPidx w → ℂ)) ≃ᵐ (G.UT (r + 1) → ℂ)) (he : MeasurePreserving e volume volume)
    (μ0 μ0' : Measure (Mt k r)) (hμ0 : B.IsHaarOn (C2.N0set k r S.z) μ0)
    (hμ0' : B.IsHaarOn (C2.N0set k r S.z') μ0') (c1 c2 : NNReal)
    (hN1 : S.μN = c1 • ((volume : Measure (G.UT (r + 1) → ℂ)).prod μ0).map
      (fun p => Matrix.of.symm (C2.tauM k r S.z (G.upper p.1) * Matrix.of p.2)))
    (hN2 : S.μN = c2 • ((volume : Measure (G.UT (r + 1) → ℂ)).prod μ0').map
      (fun p => Matrix.of.symm (C2.tauM k r S.z' (G.upper p.1) * Matrix.of p.2))) :
    S.μSS = (c1 * c2) • ((volume : Measure (C2.Lstidx w → ℂ)).prod (OD.nuR S w μ0 μ0')).map
      (fun p => OD.Xi S w e p.1 p.2) := by
  have sf : ∀ {V : Set (B.Mat k r)} {μ : Measure (Mt k r)}, B.IsHaarOn V μ → SigmaFinite μ := by
    intro V μ h
    haveI : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => h.finite_compact K hK⟩
    infer_instance
  haveI := sf S.haarW
  haveI := sf S.haarW'
  haveI := sf hμ0
  haveI := sf hμ0'
  have m1 : Measurable (fun p : (G.UT (r + 1) → ℂ) × Mt k r =>
      Matrix.of.symm (C2.tauM k r S.z (G.upper p.1) * Matrix.of p.2)) := (HC.cont_Phi S.z).measurable
  have m2 : Measurable (fun p : (G.UT (r + 1) → ℂ) × Mt k r =>
      Matrix.of.symm (C2.tauM k r S.z' (G.upper p.1) * Matrix.of p.2)) := (HC.cont_Phi S.z').measurable

  have hA : MeasurePreserving
      (fun p : (C2.Lstidx w → ℂ) × OD.RR k r w => ((p.2.1.1, (e (p.1, p.2.1.2.1), p.2.1.2.2)), p.2.2))
      ((volume : Measure (C2.Lstidx w → ℂ)).prod (OD.nuR S w μ0 μ0'))
      ((S.μW.prod ((volume : Measure (G.UT (r + 1) → ℂ)).prod μ0)).prod
        (S.μW'.prod ((volume : Measure (G.UT (r + 1) → ℂ)).prod μ0'))) := by
    have h1 := (measurePreserving_prodAssoc (volume : Measure (C2.Lstidx w → ℂ))
      (S.μW.prod ((volume : Measure (C2.LPidx w → ℂ)).prod μ0))
      (S.μW'.prod ((volume : Measure (G.UT (r + 1) → ℂ)).prod μ0'))).symm
    have h2 := (measurePreserving_prod_rearrange (volume : Measure (C2.Lstidx w → ℂ)) S.μW (volume : Measure (C2.LPidx w → ℂ)) μ0).prod
      (MeasurePreserving.id (S.μW'.prod ((volume : Measure (G.UT (r + 1) → ℂ)).prod μ0')))
    have h3 := ((MeasurePreserving.id S.μW).prod (he.prod (MeasurePreserving.id μ0))).prod
      (MeasurePreserving.id (S.μW'.prod ((volume : Measure (G.UT (r + 1) → ℂ)).prod μ0')))
    have := h3.comp (h2.comp h1)
    simp only [OD.nuR]
    convert this using 1
    all_goals first | rfl | (funext p; rfl)
  have hB : Measurable (Prod.map
      (Prod.map (id : Mt k r → Mt k r) (fun p : (G.UT (r + 1) → ℂ) × Mt k r =>
        Matrix.of.symm (C2.tauM k r S.z (G.upper p.1) * Matrix.of p.2)))
      (Prod.map (id : Mt k r → Mt k r) (fun p : (G.UT (r + 1) → ℂ) × Mt k r =>
        Matrix.of.symm (C2.tauM k r S.z' (G.upper p.1) * Matrix.of p.2)))) :=
    (measurable_id.prodMap m1).prodMap (measurable_id.prodMap m2)
  have hXi : (fun p : (C2.Lstidx w → ℂ) × OD.RR k r w => OD.Xi S w e p.1 p.2) =
      (Prod.map
        (Prod.map (id : Mt k r → Mt k r) (fun p : (G.UT (r + 1) → ℂ) × Mt k r =>
          Matrix.of.symm (C2.tauM k r S.z (G.upper p.1) * Matrix.of p.2)))
        (Prod.map (id : Mt k r → Mt k r) (fun p : (G.UT (r + 1) → ℂ) × Mt k r =>
          Matrix.of.symm (C2.tauM k r S.z' (G.upper p.1) * Matrix.of p.2)))) ∘
      (fun p : (C2.Lstidx w → ℂ) × OD.RR k r w => ((p.2.1.1, (e (p.1, p.2.1.2.1), p.2.1.2.2)), p.2.2)) := by
    funext p; rfl
  rw [hXi, ← Measure.map_map hB hA.measurable, hA.map_eq,
    ← Measure.map_prod_map _ _ (measurable_id.prodMap m1) (measurable_id.prodMap m2),
    ← Measure.map_prod_map _ _ measurable_id m1, ← Measure.map_prod_map _ _ measurable_id m2,
    Measure.map_id, Measure.map_id]
  show (S.μW.prod S.μN).prod (S.μW'.prod S.μN) = _
  have e2 : S.μW'.prod S.μN = S.μW'.prod (c2 • ((volume : Measure (G.UT (r + 1) → ℂ)).prod μ0').map
      (fun p => Matrix.of.symm (C2.tauM k r S.z' (G.upper p.1) * Matrix.of p.2))) := by rw [← hN2]
  rw [e2, hN1]
  rw [ENNReal.smul_def c1, ENNReal.smul_def c2, ENNReal.smul_def (c1 * c2), Measure.prod_smul_right,
    Measure.prod_smul_right, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, ENNReal.coe_mul]

end

end Formalism.FourierDecayAlt.P.StabilizerDisintegration.ME
end
