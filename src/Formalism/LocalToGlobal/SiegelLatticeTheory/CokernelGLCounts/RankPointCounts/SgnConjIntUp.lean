module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.CoefXFinsetSum
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.EmbeddingIntegerAlgebraMap
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LocGlobInt
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SharpDualSpans.GlueConvA

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FrFacInvMul
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IotaMemO
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IntPFmat
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MemSpanAaF
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.FibQ

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups PI.PairValDefs PI.NRCW Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Loc

variable {D : D7} (Z : LocDat D) (p : PlF D)

theorem mem_span_aaF {N : D.host.E} {c b : Fin (D.R.rS + 1)} (hN : ∀ x ∈ aaF D b, x * N ∈ aaF D c)
    {y : (D.s.atP p).Ep}
    (hy : y ∈ Submodule.span (Z.M p).L.O ((D.s.atP p).ιE '' ((aaF D b : FractionalIdeal _ _) : Set D.host.E))) :
    (D.s.atP p).ιE N * y ∈
      Submodule.span (Z.M p).L.O ((D.s.atP p).ιE '' ((aaF D c : FractionalIdeal _ _) : Set D.host.E)) := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    apply Submodule.subset_span
    refine ⟨x * N, hN x hx, ?_⟩
    rw [map_mul, mul_comm]
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [mul_add]; exact Submodule.add_mem _ hy hz
  | smul o y _ hy =>
    have e : (D.s.atP p).ιE N * (o • y) = o • ((D.s.atP p).ιE N * y) := by
      show _ * ((o : (D.s.atP p).Ep) * y) = (o : (D.s.atP p).Ep) * (_ * y)
      ring
    rw [e]
    exact Submodule.smul_mem _ _ hy

theorem loc_int {N : D.host.E} {c b : Fin (D.R.rS + 1)} (hN : ∀ x ∈ aaF D b, x * N ∈ aaF D c) :
    ∃ o ∈ (Z.M p).L.O, (D.s.atP p).ιE N * frFac Z.δ p b = frFac Z.δ p c * o := by
  have hD := Formalism.L2.SG.Pf.locDiffC_holds D Z
  have hb : frFac Z.δ p b ∈
      Submodule.span (Z.M p).L.O ((D.s.atP p).ιE '' ((aaF D b : FractionalIdeal _ _) : Set D.host.E)) := by
    rw [hD p b]
    exact Submodule.subset_span rfl
  have h := mem_span_aaF Z p hN hb
  rw [hD p c, Submodule.mem_span_singleton] at h
  obtain ⟨o, ho⟩ := h
  refine ⟨o, o.2, ?_⟩
  rw [← ho]
  show (o : (D.s.atP p).Ep) * frFac Z.δ p c = frFac Z.δ p c * o
  ring

def locU (N : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) :
    Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep :=
  Matrix.diagonal (fun a => Ring.inverse (frFac Z.δ p a)) * N.map (D.s.atP p).ιE *
    Matrix.diagonal (frFac Z.δ p)

theorem locU_apply (N : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) (c b : Fin (D.R.rS + 1)) :
    locU Z p N c b = Ring.inverse (frFac Z.δ p c) * (D.s.atP p).ιE (N c b) * frFac Z.δ p b := by
  simp [locU, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem locU_int (N : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E)
    (hU : ∀ a b, b < a → N a b = 0) (hd : ∀ a, N a a = 1)
    (hN : ∀ c b, c < b → ∀ x ∈ aaF D b, x * N c b ∈ aaF D c) :
    (∀ a, locU Z p N a a = 1) ∧ (∀ a b, b < a → locU Z p N a b = 0) ∧ ∀ a b, locU Z p N a b ∈ (Z.M p).L.O := by
  have hu : ∀ a, Ring.inverse (frFac Z.δ p a) * frFac Z.δ p a = 1 := fun a =>
    Ring.inverse_mul_cancel _ (Formalism.L2.SG.Pf.BBTie.bt_frFac_unit Z p a)
  refine ⟨fun a => ?_, fun a b h => ?_, fun a b => ?_⟩
  · rw [locU_apply, hd, map_one, mul_one, hu]
  · rw [locU_apply, hU a b h, map_zero, mul_zero, zero_mul]
  · rcases lt_trichotomy a b with h | h | h
    · obtain ⟨o, ho, he⟩ := loc_int Z p (hN a b h)
      rw [locU_apply, mul_assoc, he, ← mul_assoc, hu, one_mul]
      exact ho
    · subst h
      rw [locU_apply, hd, map_one, mul_one, hu]
      exact Subring.one_mem _
    · rw [locU_apply, hU a b h, map_zero, mul_zero, zero_mul]
      exact Subring.zero_mem _

end Loc

end Formalism.L2.SG.Pf.FibQ
end
end

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.FibQ

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat PI.PairValDefs PI.NRCW IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Cong

variable (D : D7)

theorem intP_fmat (P : HeightOneSpectrum (𝓞 D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T : D.host.E}
    (G : LFlag (D.sp.Y 0) D.R.rS T) (m : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hm : m ∈ NLam Λ G)
    (hC : IsFixedConv Λ (gS D) G) (hP : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) (hz : G.fl.z ∈ Λ)
    (c b : Fin (D.R.rS + 1)) : IntP P (fmat D G m c b) := by
  have hfLP : ∀ c, frame G c ∈ LP P Λ := by
    intro c
    induction c using Fin.lastCases with
    | last => rw [frame_last]; exact mem_localization_of_mem₃ P hz
    | cast i => rw [frame_castSucc]; exact e_mem_LP P hC hP i
  have hmLP : m (frame G b) - frame G b ∈ LP P Λ :=
    sub_mem_localization P (LP_map P (m : (VS D).V →ₗ[D.host.E] (VS D).V) (fun v hv => nlam_mem hm hv) (hfLP b)) (hfLP b)
  have h01 : ∀ (t : Prop) [Decidable t], IntP P (if t then (1 : D.host.E) else 0) := by
    intro t _
    split_ifs
    · simpa using intP_O P 1
    · simpa using intP_O P 0
  unfold fmat
  apply intP_add P (h01 _)
  split_ifs with h
  · exact coef_intP P hC hP hmLP (frame_d_mem G hm b) _
  · simpa using intP_O P 0

theorem frame_nm (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E} (G : LFlag (D.sp.Y 0) D.R.rS T)
    (G₁ : LFlag (D.sp.Y 0) D.R.rS T') (n m : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hn : n ∈ NLam Λ G)
    (hm : m ∈ NLam Λ G₁) (b : Fin (D.R.rS + 1)) :
    n (m (frame G₁ b)) = ∑ d, (fmat D G n * fmat D G₁ m) d b • frame G d +
      n (∑ c, fmat D G₁ m c b • (frame G₁ c - frame G c)) := by
  rw [(stepExp D Λ G₁ m hm).2 b]
  have e1 : ∑ c, fmat D G₁ m c b • frame G₁ c =
      ∑ c, fmat D G₁ m c b • frame G c + ∑ c, fmat D G₁ m c b • (frame G₁ c - frame G c) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [← smul_add, add_sub_cancel]
  rw [e1, map_add (f := _)]
  congr 1
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [map_smul, (stepExp D Λ G n hn).2, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun c _ => ?_))
  rw [mul_comm]

theorem cong_at (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E} (G : LFlag (D.sp.Y 0) D.R.rS T)
    (G₁ G₂ : LFlag (D.sp.Y 0) D.R.rS T') (n m : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hn : n ∈ NLam Λ G)
    (hm : m ∈ NLam Λ G₁) (hfr : ∀ a, frame G₂ a = n (m (frame G₁ a))) (hC : IsFixedConv Λ (gS D) G)
    (hC₁ : IsFixedConv Λ (gS D) G₁) (hA1 : AdmWit Λ (gS D) G G₁ 1) (hA2 : AdmWit Λ (gS D) G G₂ 1)
    (hz₁ : G₁.fl.z ∈ Λ) (P : HeightOneSpectrum (𝓞 D.host.E)) (hP : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal)
    (hg : ((gS D : ℕ) : D.host.E) ≠ 0) (d : Fin D.R.rS) (b : Fin (D.R.rS + 1)) :
    IntP P ((fmat D G n * fmat D G₁ m - 1) d.castSucc b / (gS D : D.host.E)) := by
  have hw : ∀ c, frame G₁ c - frame G c ∈ LP P (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ) := by
    intro c
    have := hA1.2.2 c P hP
    rw [frameAct_one] at this
    exact this
  have hw2 : ∀ c, frame G₂ c - frame G c ∈ LP P (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ) := by
    intro c
    have := hA2.2.2 c P hP
    rw [frameAct_one] at this
    exact this
  have hNU := (stepExp D Λ G n hn).1
  have hMU := (stepExp D Λ G₁ m hm).1

  set Y := ∑ d', (fmat D G n * fmat D G₁ m - 1) d' b • frame G d' with hYdef
  have hYeq : Y = (frame G₂ b - frame G b) - n (∑ c, fmat D G₁ m c b • (frame G₁ c - frame G c)) := by
    rw [hfr b, frame_nm D Λ G G₁ n m hn hm b, hYdef]
    simp only [Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib]
    have e1 : ∑ d', (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) d' b • frame G d' = frame G b := by
      simp [Matrix.one_apply]
    rw [e1]
    abel
  have hYLg : Y ∈ LP P (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ) := by
    rw [hYeq]
    refine sub_mem (hw2 b) ?_
    exact LP_map P (n : (VS D).V →ₗ[D.host.E] (VS D).V) (nlam_gLam hn _)
      (LP_sum P _ _ fun c _ => smul_mem_localization P (intP_fmat D P Λ G₁ m hm hC₁ hP hz₁ c b) (hw c))

  have hlast : (fmat D G n * fmat D G₁ m - 1) (Fin.last D.R.rS) b = 0 := by
    rw [Matrix.sub_apply, Matrix.mul_apply, Finset.sum_eq_single (Fin.last D.R.rS)]
    · rw [(hNU _ _).2 rfl, one_mul, Matrix.one_apply]
      by_cases hb : Fin.last D.R.rS = b
      · rw [(hMU _ _).2 hb, if_pos hb, sub_self]
      · have hlt : b < Fin.last D.R.rS := lt_of_le_of_ne (Fin.le_last b) (Ne.symm hb)
        rw [(hMU _ _).1 hlt, if_neg hb, sub_self]
    · intro c _ hc
      have hlt : c < Fin.last D.R.rS := lt_of_le_of_ne (Fin.le_last c) hc
      rw [(hNU _ _).1 hlt, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hYsum : Y = ∑ d' : Fin D.R.rS, (fmat D G n * fmat D G₁ m - 1) d'.castSucc b • G.fl.e d' := by
    rw [hYdef, Fin.sum_univ_castSucc, hlast, zero_smul, add_zero]
    refine Finset.sum_congr rfl (fun d' _ => ?_)
    rw [frame_castSucc]
  have hYX : Y ∈ G.fl.X := by
    rw [hYsum]
    exact Submodule.sum_mem _ fun d' _ => Submodule.smul_mem _ _ (e_mem_X _ d')
  have hcoef := coef_intP_g P hC hP hg hYLg hYX d
  have hYd : G.fl.coefX Y d = (fmat D G n * fmat D G₁ m - 1) d.castSucc b := by
    rw [hYsum, coefX_finset_sum _ _ _ (fun d' => Submodule.smul_mem _ _ (e_mem_X _ d'))]
    simp only [coefX_smul_e, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hYd] at hcoef
  exact hcoef

end Cong

end Formalism.L2.SG.Pf.FibQ
end
end

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.FibQ

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups PI.PairValDefs PI.NRCW IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Bridge

variable {D : D7}

def condI (y : D.host.E) : Ideal (𝓞 D.host.E) where
  carrier := {t | ∃ o : 𝓞 D.host.E, (t : D.host.E) * y = o}
  add_mem' := by
    rintro a b ⟨o₁, h₁⟩ ⟨o₂, h₂⟩
    exact ⟨o₁ + o₂, by push_cast; rw [add_mul, h₁, h₂]⟩
  zero_mem' := ⟨0, by simp⟩
  smul_mem' := by
    rintro c a ⟨o, h⟩
    exact ⟨c * o, by rw [smul_eq_mul]; push_cast; rw [mul_assoc, h]⟩

theorem iota_mem_O (p : PlF D) (y : D.host.E)
    (h : ∀ P : HeightOneSpectrum (𝓞 D.host.E),
      P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = p.asIdeal → IntP P y) :
    (D.s.atP p).ιE y ∈ (D.s.atP p).O := by
  rw [Formalism.L2.SG.Pf.LocalDenominators.iE_mem_O_iff_D]
  have := p.isPrime
  by_contra hno
  push Not at hno
  have hle : (condI y).comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) ≤ p.asIdeal := by
    intro s hs
    by_contra hsp
    obtain ⟨o, ho⟩ := hs
    apply hno s hsp
    have e : algebraMap D.host.F D.host.E (s : D.host.F) =
        ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s : 𝓞 D.host.E) : D.host.E) := by
      rw [← IsScalarTower.algebraMap_apply (𝓞 D.host.F) D.host.F D.host.E,
        IsScalarTower.algebraMap_apply (𝓞 D.host.F) (𝓞 D.host.E) D.host.E]
    rw [e, ho]
    exact o.2
  obtain ⟨Q, hIQ, hQp, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p.asIdeal (condI y) hle
  have hQ0 : Q ≠ ⊥ := by
    intro hb
    apply p.ne_bot
    rw [← hQc, hb]
    change Ideal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) ⊥ = ⊥
    rw [Ideal.comap_bot_of_injective]
    exact FaithfulSMul.algebraMap_injective (𝓞 D.host.F) (𝓞 D.host.E)
  obtain ⟨t, ht, o, hto⟩ := h ⟨Q, hQp, hQ0⟩ hQc
  exact ht (hIQ ⟨o, hto⟩)

end Bridge

end Formalism.L2.SG.Pf.FibQ
end
end

noncomputable section

open scoped Classical Matrix

namespace Formalism.L2.SG.Pf.FibQ

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups PI.PairValDefs PI.NRCW IsDedekindDomain
  Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Key

variable {D : D7} (Z : LocDat D) (p : PlF D)

theorem cj_iota (x : D.host.E) :
    (Z.M p).L.cj ((D.s.atP p).ιE x) = (D.s.atP p).ιE (star x) := by
  have hstar : star x = D.conjF x := by
    rw [D.conjF_eq]
    have := D.host.isCMField_hostE
    apply D.host.φ₀.injective
    change D.host.φ₀ (NumberField.IsCMField.complexConj D.host.E x) = D.host.φ₀ (D.host.conj x)
    rw [NumberField.IsCMField.complexEmbedding_complexConj]
    exact (D.host.toHostAx.conjE_apply D.host.φ₀ x).symm
  rw [Z.hcj p, (D.s.atP p).cj_ιE, hstar]

theorem frFac_inv_mul (a : Fin (D.R.rS + 1)) : Ring.inverse (frFac Z.δ p a) * frFac Z.δ p a = 1 :=
  Ring.inverse_mul_cancel _ (Formalism.L2.SG.Pf.BBTie.bt_frFac_unit Z p a)

theorem frFac_mul_inv (a : Fin (D.R.rS + 1)) : frFac Z.δ p a * Ring.inverse (frFac Z.δ p a) = 1 :=
  Ring.mul_inverse_cancel _ (Formalism.L2.SG.Pf.BBTie.bt_frFac_unit Z p a)

theorem key_rel (N M Z₁ Z₂ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E)
    (hrel : Nᴴ * Z₂ = Z₁ * M) :
    ((locU Z p N).map (Z.M p).L.cj)ᵀ * Formalism.L2.SG.CntLocal.ZhatLoc Z.M Z.δ p Z₂ =
      Formalism.L2.SG.CntLocal.ZhatLoc Z.M Z.δ p Z₁ * locU Z p M := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, locU_apply,
    Formalism.L2.SG.CntLocal.ZhatLoc, Matrix.of_apply]
  have hL : ∀ c, (Z.M p).L.cj (Ring.inverse (frFac Z.δ p c) * (D.s.atP p).ιE (N c a) * frFac Z.δ p a) *
      (frFac Z.δ p b * (Z.M p).L.cj (frFac Z.δ p c) * (D.s.atP p).ιE (Z₂ c b)) =
      (Z.M p).L.cj (frFac Z.δ p a) * frFac Z.δ p b * (D.s.atP p).ιE (star (N c a) * Z₂ c b) := by
    intro c
    rw [map_mul, map_mul, cj_iota Z p, map_mul (D.s.atP p).ιE]
    have h1 : (Z.M p).L.cj (Ring.inverse (frFac Z.δ p c)) * (Z.M p).L.cj (frFac Z.δ p c) = 1 := by
      rw [← map_mul, frFac_inv_mul, map_one]
    calc _ = ((Z.M p).L.cj (Ring.inverse (frFac Z.δ p c)) * (Z.M p).L.cj (frFac Z.δ p c)) *
          ((Z.M p).L.cj (frFac Z.δ p a) * frFac Z.δ p b *
            ((D.s.atP p).ιE (star (N c a)) * (D.s.atP p).ιE (Z₂ c b))) := by ring
      _ = _ := by rw [h1, one_mul]
  have hR : ∀ c, frFac Z.δ p c * (Z.M p).L.cj (frFac Z.δ p a) * (D.s.atP p).ιE (Z₁ a c) *
      (Ring.inverse (frFac Z.δ p c) * (D.s.atP p).ιE (M c b) * frFac Z.δ p b) =
      (Z.M p).L.cj (frFac Z.δ p a) * frFac Z.δ p b * (D.s.atP p).ιE (Z₁ a c * M c b) := by
    intro c
    rw [map_mul (D.s.atP p).ιE]
    calc _ = (frFac Z.δ p c * Ring.inverse (frFac Z.δ p c)) *
          ((Z.M p).L.cj (frFac Z.δ p a) * frFac Z.δ p b *
            ((D.s.atP p).ιE (Z₁ a c) * (D.s.atP p).ιE (M c b))) := by ring
      _ = _ := by rw [frFac_mul_inv, one_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.sum_congr rfl (fun c _ => hL c), Finset.sum_congr rfl (fun c _ => hR c), ← Finset.mul_sum,
    ← Finset.mul_sum, ← map_sum, ← map_sum]
  congr 2
  have := congrFun (congrFun hrel a) b
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply] at this
  exact this

end Key

end Formalism.L2.SG.Pf.FibQ
end
end

noncomputable section

open scoped Classical Matrix

namespace Formalism.L2.SG.Pf.FibQ

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups PI.PairValDefs PI.NRCW IsDedekindDomain
  Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section ModeL

variable {D : D7} (Z : LocDat D) (p : PlF D)

theorem permSign_mul_self₂ : Formalism.L2.SG.LsDatumB.sgnP (D := D) p * Formalism.L2.SG.LsDatumB.sgnP p = 1 := by
  unfold Formalism.L2.SG.LsDatumB.sgnP
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext b
  rw [← pow_add, ← two_mul, pow_mul]
  simp

theorem sgn_conj_intUp {ρ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep}
    (hρ : (∀ a, ρ a a = 1) ∧ (∀ a b, b < a → ρ a b = 0) ∧ ∀ a b, ρ a b ∈ (Z.M p).R) :
    (∀ a, (Formalism.L2.SG.LsDatumB.sgnP p * ρ * Formalism.L2.SG.LsDatumB.sgnP p) a a = 1) ∧
      (∀ a b, b < a → (Formalism.L2.SG.LsDatumB.sgnP p * ρ * Formalism.L2.SG.LsDatumB.sgnP p) a b = 0) ∧
      ∀ a b, (Formalism.L2.SG.LsDatumB.sgnP p * ρ * Formalism.L2.SG.LsDatumB.sgnP p) a b ∈ (Z.M p).R := by
  have e : ∀ a b, (Formalism.L2.SG.LsDatumB.sgnP p * ρ * Formalism.L2.SG.LsDatumB.sgnP p) a b =
      ((-1 : (D.s.atP p).Ep) ^ (D.R.rS - a.val)) * ρ a b * (-1) ^ (D.R.rS - b.val) := by
    intro a b
    simp [Formalism.L2.SG.LsDatumB.sgnP, Matrix.mul_diagonal, Matrix.diagonal_mul]
  refine ⟨fun a => ?_, fun a b h => ?_, fun a b => ?_⟩
  · rw [e, hρ.1 a, mul_one, ← pow_add, ← two_mul, pow_mul]; simp
  · rw [e, hρ.2.1 a b h]; simp
  · rw [e]
    refine Subring.mul_mem _ (Subring.mul_mem _ (Subring.pow_mem _ (Subring.neg_mem _ (Subring.one_mem _)) _)
      (hρ.2.2 a b)) (Subring.pow_mem _ (Subring.neg_mem _ (Subring.one_mem _)) _)

theorem modeL (hs : (Z.M p).split = none) (u u' : D.what₂.Word)
    (N M Z₁ Z₂ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E)
    (hNU : ∀ a b, b < a → N a b = 0) (hNd : ∀ a, N a a = 1) (hMU : ∀ a b, b < a → M a b = 0)
    (hMd : ∀ a, M a a = 1)
    (hNb : ∀ c b, c < b → ∀ x ∈ aaF D b, x * N c b ∈ aaF D c)
    (hMb : ∀ c b, c < b → ∀ x ∈ aaF D b, x * M c b ∈ aaF D c) (hrel : Nᴴ * Z₂ = Z₁ * M) :
    ∃ l ρ, Formalism.MainNotions.S.TieN.IntLow (Z.M p) l ∧ Formalism.MainNotions.S.TieN.IntUp (Z.M p) ρ ∧
      Formalism.L2.SG.CntLocal.ZZP (M := Z.M) Z.δ u u' p Z₂ * Formalism.L2.SG.LsDatumB.sgnP p =
        l * (Formalism.L2.SG.CntLocal.ZZP (M := Z.M) Z.δ u u' p Z₁ * Formalism.L2.SG.LsDatumB.sgnP p) * ρ := by
  have hR : (Z.M p).R = (Z.M p).L.O := by
    unfold Formalism.MainNotions.S.Loc.Model.R
    rw [hs]
  have eZZ : ∀ X, Formalism.L2.SG.CntLocal.ZZP (M := Z.M) Z.δ u u' p X = Formalism.L2.SG.CntLocal.ZhatLoc Z.M Z.δ p X := by
    intro X
    simp only [Formalism.L2.SG.CntLocal.ZZP, Formalism.MainNotions.S.Loc.HermSp.ZZplusOf, hs]
  obtain ⟨hN1, hN0, hNO⟩ := locU_int Z p N hNU hNd hNb
  obtain ⟨hM1, hM0, hMO⟩ := locU_int Z p M hMU hMd hMb
  set K := ((locU Z p N).map (Z.M p).L.cj)ᵀ with hKdef
  have hK := key_rel Z p N M Z₁ Z₂ hrel
  have hKlow : Formalism.MainNotions.S.TieN.IntLow (Z.M p) K := by
    refine ⟨fun a => ?_, fun a b h => ?_, fun a b => ?_⟩
    · simp only [hKdef, Matrix.transpose_apply, Matrix.map_apply, hN1 a, map_one]
    · simp only [hKdef, Matrix.transpose_apply, Matrix.map_apply, hN0 b a h, map_zero]
    · rw [hR]
      simp only [hKdef, Matrix.transpose_apply, Matrix.map_apply]
      exact PI.LocCntLat.GC.cj_mem_O _ (hNO b a)
  have hρ : Formalism.MainNotions.S.TieN.IntUp (Z.M p) (locU Z p M) := ⟨hM1, hM0, fun a b => by rw [hR]; exact hMO a b⟩
  have hdet : IsUnit K.det := by
    have hb : K.BlockTriangular OrderDual.toDual := fun i j hij => hKlow.2.1 i j hij
    have hd : K.det = 1 := by
      rw [Matrix.det_of_lowerTriangular K hb]
      simp [hKlow.1]
    rw [hd]
    exact isUnit_one
  have hY : Formalism.L2.SG.CntLocal.ZhatLoc Z.M Z.δ p Z₂ =
      K⁻¹ * Formalism.L2.SG.CntLocal.ZhatLoc Z.M Z.δ p Z₁ * locU Z p M := by
    rw [Matrix.mul_assoc, ← hK, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul K hdet, Matrix.one_mul]
  refine ⟨K⁻¹, Formalism.L2.SG.LsDatumB.sgnP p * locU Z p M * Formalism.L2.SG.LsDatumB.sgnP p,
    Formalism.L2.SG.Pf.LocOrbCut.intLow_inv (Z.M p) hKlow, sgn_conj_intUp Z p hρ, ?_⟩
  rw [eZZ, eZZ, hY]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Formalism.L2.SG.LsDatumB.sgnP p) (Formalism.L2.SG.LsDatumB.sgnP p), permSign_mul_self₂, Matrix.one_mul]

end ModeL

end Formalism.L2.SG.Pf.FibQ
