module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPinG
public import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.FramesTurn
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqCut

@[expose] public section

section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.FramesSh
set_option linter.unusedVariables false

noncomputable section

namespace Formalism.MainNotions.S.Pv.Frames

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.FrameBoundFromBesselTorus Formalism.MainNotions.S.Bridge Formalism.BasicNotions

variable {k r : ℕ}

theorem orbSqO_le_turn (L : LocBessel k r) (ka : ℝ) (hka : 0 < ka) (hc : L.c = ((2 * ka : ℝ) : ℂ))
    (f : Mx k r → (L.Wq →L[ℂ] L.Wp)) (p : Point ℂ (r + 1)) :
    orbSqO L f p ≤ orbSq (turnL L ka) (turnF L ka f) (turnPt p) := by
  unfold orbSqO orbSq
  refine iSup_le fun g => iSup_le fun μR => iSup_le fun ν => iSup_le fun hg => ?_
  rw [← OrbInt_turn L ka hc f g ν]
  exact le_iSup_of_le (tTi k r * g * tT k r) (le_iSup_of_le (μR.map (cA k r))
    (le_iSup_of_le (ν.map (thP k r)) (le_iSup_of_le
      ⟨isPtRep_turn L ka hg.1, isRelStab_turn L ka hc hg.2.1, isRootMeas_turn L ka hka hc hg.2.2.1,
        isOrbQuot_turn L ka hg.2.2.2⟩ le_rfl)))

section OneRec

variable (D : D7)

end OneRec

end Formalism.MainNotions.S.Pv.Frames

end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ThmBTies
noncomputable section

namespace Formalism.L2.SG.Pf.OrderedProducts

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.BesselShellMomentBounds Formalism.L2.SG.RowsConc Formalism.FourierDecayAlt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Lists

def oprod {X : Type*} (G : ℕ → X × ℕ → ℝ) : ℕ → List (X × ℕ) → ℝ
  | _, [] => 1
  | a, b :: L => G (a + b.2) b * oprod G (a + b.2) L

theorem oprod_cons {X : Type*} (G : ℕ → X × ℕ → ℝ) (a : ℕ) (b : X × ℕ) (L : List (X × ℕ)) :
    oprod G a (b :: L) = G (a + b.2) b * oprod G (a + b.2) L := rfl

theorem fin_prod_oprod {K : Type} [Field K] (G : ℕ → K × ℕ → ℝ) :
    ∀ (L : List (K × ℕ)) (a : ℕ), ∏ i : Fin L.length, G (a + pS L ((i : ℕ) + 1)) L[i] = oprod G a L
  | [], a => by simp [oprod]
  | b :: L, a => by
    refine (Fin.prod_univ_succ _).trans ?_
    rw [oprod_cons, ← fin_prod_oprod G L (a + b.2)]
    simp [pS, add_assoc]

theorem fin_prod_list {X : Type*} (f : X → ℝ) : ∀ L : List X, ∏ i : Fin L.length, f L[i] = (L.map f).prod
  | [] => by simp
  | x :: L => by
    refine (Fin.prod_univ_succ _).trans ?_
    simp

end Lists

section Weights

variable (k r : ℕ) (T T' : ℝ)

def pW (L : List (ℂ × ℕ)) : ℝ := (L.map fun b => ‖b.1‖ ^ (2 * b.2)).prod

def gW : List (ℂ × ℕ) → ℝ
  | [] => 1
  | [b] => if b.2 = 1 then Complex.normSq b.1 - T * T' else ‖b.1‖ ^ (2 * b.2)
  | b :: c :: L => ‖b.1‖ ^ (2 * b.2) * gW (c :: L)

def eG (j : ℕ) (b : ℂ × ℕ) : ℝ := ‖b.1‖ ^ (2 * b.2 * (2 * (r + 1 - j) + b.2 - 1))

theorem expo (k s x : ℕ) (hk : 1 ≤ k) (hs : 1 ≤ s) :
    2 * s * (2 * x + k + 1 + s - 3) = 2 * s * (k - 1) + 2 * s * (2 * x + s - 1) := by
  have h : 2 * x + k + 1 + s - 3 = (k - 1) + (2 * x + s - 1) := by omega
  rw [h, Nat.mul_add]

theorem ptWeightFrom_eq (hk : 1 ≤ k) : ∀ (L : List (ℂ × ℕ)) (a : ℕ), (∀ b ∈ L, 1 ≤ b.2) →
    a + (L.map Prod.snd).sum = r + 1 → ptWeightFrom k r T T' a L = gW T T' L ^ (k - 1) * oprod (eG r) a L
  | [], a, _, _ => by simp [ptWeightFrom, gW, oprod]
  | [(t, s)], a, hs, hl => by
    have hs1 : 1 ≤ s := hs (t, s) (by simp)
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hl
    by_cases h1 : s = 1
    · subst h1
      rw [ptWeightFrom, if_pos ⟨rfl, hl⟩]
      simp [ptWeightFrom, gW, oprod, eG, hl]
    · have hc : ¬ (s = 1 ∧ a + 1 = r + 1) := fun h => h1 h.1
      rw [ptWeightFrom, if_neg hc]
      simp only [ptWeightFrom, gW, oprod, eG, if_neg h1, mul_one]
      rw [hl, ← pow_mul, ← pow_add]
      congr 1
      have e := expo k s (r + 1 - (r + 1)) hk hs1
      simp only [Ml] at e ⊢
      rw [e]
  | (t, s) :: c :: L, a, hs, hl => by
    have hs1 : 1 ≤ s := hs (t, s) (by simp)
    have hc1 : 1 ≤ c.2 := hs c (by simp)
    have hsr : ∀ b ∈ c :: L, 1 ≤ b.2 := fun b hb => hs b (List.mem_cons_of_mem _ hb)
    simp only [List.map_cons, List.sum_cons] at hl
    have hl' : a + s + ((c :: L).map Prod.snd).sum = r + 1 := by
      simp only [List.map_cons, List.sum_cons]; omega
    have hn : ¬ (s = 1 ∧ a + 1 = r + 1) := by
      rintro ⟨rfl, h⟩; omega
    rw [ptWeightFrom, if_neg hn, ptWeightFrom_eq hk (c :: L) (a + s) hsr hl']
    simp only [gW, oprod_cons, eG]
    have e := expo k s (r + 1 - (a + s)) hk hs1
    simp only [Ml]
    rw [e, pow_add, pow_mul, mul_pow]
    ring

end Weights

section Minors

theorem comp_last {n : ℕ} (c : Composition (n + 1)) (h : 0 < c.length) :
    c.sizeUpTo (c.length - 1) + c.blocksFun ⟨c.length - 1, by omega⟩ = n + 1 := by
  have h1 : c.length - 1 + 1 = c.length := by omega
  have h2 := c.sizeUpTo_succ' ⟨c.length - 1, by omega⟩
  simp only [Fin.val_mk, h1, Composition.sizeUpTo_length] at h2
  exact h2.symm

theorem comp_not_end {n : ℕ} (c : Composition (n + 1)) (h : 0 < c.length)
    (hb : c.blocksFun ⟨c.length - 1, by omega⟩ ≠ 1) (q : ℕ) : n ≠ c.sizeUpTo q := by
  intro heq
  have hlast := comp_last c h
  have hpos := c.one_le_blocksFun ⟨c.length - 1, by omega⟩
  rcases Nat.lt_or_ge q c.length with hq | hq
  · have hmono : c.sizeUpTo q ≤ c.sizeUpTo (c.length - 1) := c.monotone_sizeUpTo (by omega)
    omega
  · have := c.sizeUpTo_ofLength_le q hq
    omega

theorem comp_len_pos {n : ℕ} (c : Composition (n + 1)) : 0 < c.length := by
  first
    | exact c.length_pos_of_pos (Nat.succ_pos n)
    | exact Composition.length_pos_of_pos c (Nat.succ_pos n)

theorem blocksFun_toComp {K : Type} [Field K] {d : ℕ} (p : Point K d) (a : Fin (toComp p).length) :
    (toComp p).blocksFun a = (p.1[(a : ℕ)]'(lt_of_lt_of_eq a.2 (toComp_length p))).2 := by
  unfold toComp
  simp only [Composition.blocksFun]
  first
    | exact List.getElem_map Prod.snd
    | exact List.getElem_map ..
    | exact List.get_map Prod.snd
    | exact List.get_map ..
    | (rw [List.get_eq_getElem]; simp)

theorem pW_append (L0 : List (ℂ × ℕ)) (t : ℂ) (s : ℕ) : pW (L0 ++ [(t, s)]) = pW L0 * ‖t‖ ^ (2 * s) := by
  simp [pW, List.map_append, List.prod_append]

theorem gW_cons (T T' : ℝ) (b : ℂ × ℕ) (L : List (ℂ × ℕ)) (hL : L ≠ []) :
    gW T T' (b :: L) = ‖b.1‖ ^ (2 * b.2) * gW T T' L := by
  cases L with
  | nil => exact absurd rfl hL
  | cons c L =>
    first
    | rfl
    | simp [gW]

theorem gW_append (T T' : ℝ) (t : ℂ) (s : ℕ) : ∀ L0 : List (ℂ × ℕ),
    gW T T' (L0 ++ [(t, s)]) = pW L0 * (if s = 1 then Complex.normSq t - T * T' else ‖t‖ ^ (2 * s))
  | [] => by simp [gW, pW]
  | b :: L0 => by
    rw [List.cons_append, gW_cons T T' b _ (by simp), gW_append T T' t s L0]
    simp [pW, mul_assoc]

theorem normSq_lead_top {r : ℕ} (p : Point ℂ (r + 1)) :
    Complex.normSq (leadMinor (ptMat p) (r + 1) le_rfl) = pW p.1 := by
  have e1 : leadMinor (ptMat p) (r + 1) le_rfl = Formalism.HermitianLatticeCounting.ExpansionTerms.leadingPrincipalMinor (Formalism.HermitianLatticeCounting.ExpansionTerms.blockAntidiagonalMatrix (toComp p) (toT p)) (r + 1) := by
    rw [← ptMat_eq]; exact leadMinorK_eq _ _ _
  have v := Formalism.HermitianLatticeCounting.Final.ExpansionTerms.e4aValue ℂ (r + 1) (toComp p) (toT p) (toComp p).length
  rw [(toComp p).sizeUpTo_length] at v
  rw [e1, v, map_prod, Finset.filter_true_of_mem (fun a _ => a.2)]
  have h : ∀ a : Fin (toComp p).length, Complex.normSq ((-1) ^ ((toComp p).blocksFun a).choose 2 * toT p a ^ (toComp p).blocksFun a) =
      ‖(p.1[(a : ℕ)]'(lt_of_lt_of_eq a.2 (toComp_length p))).1‖ ^ (2 * (p.1[(a : ℕ)]'(lt_of_lt_of_eq a.2 (toComp_length p))).2) := by
    intro a
    rw [map_mul, map_pow, map_pow, Complex.normSq_neg, Complex.normSq_one, one_pow, one_mul,
      Complex.normSq_eq_norm_sq, ← pow_mul]
    rw [blocksFun_toComp]
    rfl
  rw [Finset.prod_congr rfl fun a _ => h a, pW, ← fin_prod_list]
  exact Fintype.prod_equiv (finCongr (toComp_length p)) _ _ fun a => rfl

theorem lead_r_zero {r : ℕ} (p : Point ℂ (r + 1)) (L0 : List (ℂ × ℕ)) (t : ℂ) (s : ℕ)
    (hp : p.1 = L0 ++ [(t, s)]) (hs : s ≠ 1) : leadMinor (ptMat p) r (Nat.le_succ r) = 0 := by
  have e0 : leadMinor (ptMat p) r (Nat.le_succ r) = Formalism.HermitianLatticeCounting.ExpansionTerms.leadingPrincipalMinor (Formalism.HermitianLatticeCounting.ExpansionTerms.blockAntidiagonalMatrix (toComp p) (toT p)) r := by
    rw [← ptMat_eq]; exact leadMinorK_eq _ _ _
  rw [e0]
  have hlen : (toComp p).length = L0.length + 1 := by rw [toComp_length, hp]; simp
  have hb : (toComp p).blocksFun ⟨(toComp p).length - 1, by omega⟩ = s := by
    have e1 := comp_last (toComp p) (comp_len_pos _)
    have e2 : (toComp p).sizeUpTo ((toComp p).length - 1) = (L0.map Prod.snd).sum := by
      rw [sizeUpTo_toComp, hlen, Nat.add_sub_cancel]
      unfold pS; rw [hp]; simp
    have e3 : (L0.map Prod.snd).sum + s = r + 1 := by
      have e := p.2.2; rw [hp] at e; simpa using e
    omega
  exact Formalism.HermitianLatticeCounting.Final.ExpansionTerms.e4aVanish ℂ (r + 1) (toComp p) (toT p) r (Nat.le_succ r)
    (comp_not_end (toComp p) (comp_len_pos _) (by rw [hb]; exact hs))

theorem GPoint_eq_gW {r : ℕ} (T T' : ℝ) (p : Point ℂ (r + 1)) : Gpt T T' p = gW T T' p.1 := by
  have hne : p.1 ≠ [] := by
    intro h; have e := p.2.2; rw [h] at e; simp at e
  obtain ⟨L0, b, hp⟩ : ∃ L0 b, p.1 = L0 ++ [b] := ⟨_, _, (List.dropLast_append_getLast hne).symm⟩
  obtain ⟨t, s⟩ := b
  have ht : t ≠ 0 := (p.2.1 (t, s) (by rw [hp]; simp)).1
  have htop := normSq_lead_top p
  rw [hp, pW_append] at htop
  rw [hp, gW_append]
  unfold Gpt
  by_cases hs : s = 1
  · subst hs
    obtain ⟨h1, -⟩ := last_block p t (by rw [hp]; simp)
    rw [h1, Complex.normSq_mul] at htop ⊢
    rw [if_pos rfl]
    have hn : Complex.normSq t = ‖t‖ ^ (2 * 1) := by rw [Complex.normSq_eq_norm_sq]
    have hpos : 0 < Complex.normSq t := Complex.normSq_pos.2 ht
    have e : Complex.normSq (leadMinor (ptMat p) r (Nat.le_succ r)) = pW L0 := by
      rw [← hn] at htop; exact mul_right_cancel₀ hpos.ne' htop
    rw [e]; ring
  · rw [if_neg hs, lead_r_zero p L0 t s hp hs, map_zero, mul_zero, sub_zero, htop]

end Minors

section Rat

variable (D : D7)

theorem one_le_rd : 1 ≤ D.host.rdE := by
  unfold Formalism.BasicNotions.Host.rdE
  refine Real.one_le_rpow ?_ (by positivity)
  have h : (1 : ℤ) ≤ |NumberField.discr D.host.E| := Int.one_le_abs (NumberField.discr_ne_zero D.host.E)
  have h' : (1 : ℝ) ≤ ((|NumberField.discr D.host.E| : ℤ) : ℝ) := by exact_mod_cast h
  rwa [Int.cast_abs] at h'

theorem dlast_eq (w : Point D.host.E (D.R.rS + 1)) : DlastPt (toPts w) = leadMinorK (ptMat w) (D.R.rS + 1) le_rfl := by
  have hpos : 0 < (toPts w).1.length := comp_len_pos _
  unfold DlastPt
  rw [dite_eq_left hpos]
  unfold endMin
  rw [E5minor_eq]
  have e : (toPts w).1.sizeUpTo (((⟨(toPts w).1.length - 1, by omega⟩ : Fin (toPts w).1.length) : ℕ) + 1) = D.R.rS + 1 := by
    simp only [Nat.sub_add_cancel hpos, (toPts w).1.sizeUpTo_length]
  rw [e, leadMinorK_eq, ptMat_eq]
  rfl

theorem dr_eq (w : Point D.host.E (D.R.rS + 1)) : DrPt (toPts w) = leadMinorK (ptMat w) D.R.rS (Nat.le_succ _) := by
  have hpos : 0 < (toPts w).1.length := comp_len_pos _
  have hl := comp_last (toPts w).1 hpos
  have eL : leadMinorK (ptMat w) D.R.rS (Nat.le_succ _) =
      Formalism.HermitianLatticeCounting.ExpansionTerms.leadingPrincipalMinor (Formalism.HermitianLatticeCounting.ExpansionTerms.blockAntidiagonalMatrix (toPts w).1 (toPts w).2) D.R.rS := by
    rw [leadMinorK_eq, ptMat_eq]; rfl
  rw [eL]
  unfold DrPt
  rw [dite_eq_left hpos]
  by_cases hb : (toPts w).1.blocksFun ⟨(toPts w).1.length - 1, by omega⟩ = 1
  · rw [if_pos hb]
    have hr : D.R.rS = (toPts w).1.sizeUpTo ((toPts w).1.length - 1) := by omega
    by_cases h2 : 2 ≤ (toPts w).1.length
    · rw [dite_eq_left h2]
      unfold endMin
      rw [E5minor_eq, congrArg (Formalism.HermitianLatticeCounting.ExpansionTerms.leadingPrincipalMinor _) hr]
      congr 2
      simp only
      omega
    · rw [dite_eq_right h2]
      have h1 : (toPts w).1.length - 1 = 0 := by omega
      rw [congrArg (Formalism.HermitianLatticeCounting.ExpansionTerms.leadingPrincipalMinor _) hr, Formalism.HermitianLatticeCounting.Final.ExpansionTerms.e4aValue, h1]
      simp
  · rw [if_neg hb]
    exact (Formalism.HermitianLatticeCounting.Final.ExpansionTerms.e4aVanish D.host.E (D.R.rS + 1) (toPts w).1 (toPts w).2 D.R.rS (Nat.le_succ _)
      (comp_not_end (toPts w).1 hpos hb)).symm

theorem GPt_eq (T T' : ℕ) (w : Point D.host.E (D.R.rS + 1)) : GPt (T * T') (toPts w) = Gglob D T T' w := by
  unfold GPt Gglob
  rw [dlast_eq, dr_eq, Formalism.BasicNotions.Examples₂.star_eq_conj (H := D.host), Formalism.BasicNotions.Examples₂.star_eq_conj (H := D.host), Nat.cast_mul]

end Rat

section Weight

variable (D : D7)

theorem alf_sq (n : ℕ) : (∏ i : Fin n, alf D i) ^ 2 = D.host.rdE ^ (-((n : ℤ) * (2 * (D.R.rS : ℤ) + 1 - n))) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.prod_univ_castSucc, mul_pow]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]
    unfold alf
    rw [show (D.host.rdE ^ (-((D.R.rS : ℤ) - (n : ℤ)))) ^ 2 = D.host.rdE ^ (-((D.R.rS : ℤ) - (n : ℤ)) * 2) by
      rw [zpow_mul, zpow_two, sq], ← zpow_add₀ (rdE_pos D).ne']
    congr 1; push_cast; ring

theorem alfq : ((∏ i : Fin D.R.rS, alf D i) ^ 2) ^ 2 = (D.host.rdE ^ (2 * D.R.rS * (D.R.rS + 1)))⁻¹ := by
  rw [alf_sq, ← zpow_natCast D.host.rdE, ← zpow_neg, sq, ← zpow_add₀ (rdE_pos D).ne']
  congr 1; push_cast; ring

theorem rho_eq (a s : ℕ) (hs : 1 ≤ s) (h : a + s ≤ D.R.rS + 1) :
    rhoReal D (a + 1) s = (D.host.rdE ^ (2 * D.R.rS + 1 + s - 2 * (a + s)))⁻¹ := by
  unfold rhoReal
  rw [← zpow_natCast, ← zpow_neg]
  congr 1
  have h2 : 2 * (a + s) ≤ 2 * D.R.rS + 1 + s := by omega
  push_cast [Nat.cast_sub h2]
  ring

theorem eW_loc (v : D.what₂.Tau) : ∀ (L : List (D.host.E × ℕ)) (a : ℕ), (∀ b ∈ L, 1 ≤ b.2) →
    a + (L.map Prod.snd).sum ≤ D.R.rS + 1 →
    oprod (eG D.R.rS) a (locBlocksFrom D (rhoReal D) v a L) =
      oprod (fun j b => ((D.host.rdE ^ (2 * D.R.rS + 1 + b.2 - 2 * j))⁻¹ * ‖plEmb D v b.1‖) ^
        (2 * b.2 * (2 * (D.R.rS + 1 - j) + b.2 - 1))) a L
  | [], a, _, _ => rfl
  | (t, s) :: L, a, hs, h => by
    have hs1 : 1 ≤ s := hs (t, s) (by simp)
    simp only [List.map_cons, List.sum_cons] at h
    rw [locBlocksFrom, oprod_cons, oprod_cons]
    dsimp only
    rw [eW_loc v L (a + s) (fun b hb => hs b (List.mem_cons_of_mem _ hb)) (by omega)]
    congr 1
    simp only [eG]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (rhoReal_pos D _ _).le, rho_eq D a s hs1 (by omega)]

theorem gpart (T T' : ℕ) (v : D.what₂.Tau) (w : Point D.host.E (D.R.rS + 1))
    (hG : 0 < Gpt (T : ℝ) (T' : ℝ) (ptLoc D v w)) :
    (D.host.rdE ^ (2 * D.R.rS * (D.R.rS + 1)))⁻¹ * plOf D v (GPt (T * T') (toPts w)) =
      Gpt (T : ℝ) (T' : ℝ) (ptLoc D v w) := by
  have hP : 0 < ∏ i : Fin D.R.rS, alf D i := Finset.prod_pos fun i _ => alf_pos D i
  have hQ : 0 < ((∏ i : Fin D.R.rS, alf D i) ^ 2) ^ 2 := by positivity
  have hloc : Gpt (T : ℝ) (T' : ℝ) (ptLoc D v w) = ((∏ i : Fin D.R.rS, alf D i) ^ 2) ^ 2 *
      (Complex.normSq (plEmb D v (leadMinorK (ptMat w) (D.R.rS + 1) le_rfl)) -
        (T : ℝ) * (T' : ℝ) * Complex.normSq (plEmb D v (leadMinorK (ptMat w) D.R.rS (Nat.le_succ _)))) :=
    GPoint_loc D _ _ v w
  have e1 : plOf D v (GPt (T * T') (toPts w)) =
      |Complex.normSq (plEmb D v (leadMinorK (ptMat w) (D.R.rS + 1) le_rfl)) -
        (T : ℝ) * (T' : ℝ) * Complex.normSq (plEmb D v (leadMinorK (ptMat w) D.R.rS (Nat.le_succ _)))| := by
    rw [plOf_apply, GPt_eq]
    show ‖plEmb D v (Gglob D T T' w)‖ = _
    rw [plEmb_Gglob, Complex.norm_real, Real.norm_eq_abs]
  have hXp : 0 < Complex.normSq (plEmb D v (leadMinorK (ptMat w) (D.R.rS + 1) le_rfl)) -
        (T : ℝ) * (T' : ℝ) * Complex.normSq (plEmb D v (leadMinorK (ptMat w) D.R.rS (Nat.le_succ _))) := by
    rw [hloc] at hG; exact pos_of_mul_pos_right hG hQ.le
  rw [e1, abs_of_pos hXp, hloc, ← alfq D]

theorem nPt_eq (T T' : ℕ) (w : Point D.host.E (D.R.rS + 1)) (hG : ∀ v, 0 < Gpt (T : ℝ) (T' : ℝ) (ptLoc D v w)) :
    nPt D.host.rdE D.R.k (T * T') (toPts w) = ptWeightG D (rhoReal D) T T' w.1 := by
  have hk : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  rw [ptWeightG_eq_prod]
  unfold nPt
  symm
  refine Fintype.prod_bijective (plOf D) (plOf_bij D) _ _ fun v => ?_
  unfold nLoc ptWeight
  rw [ptWeightFrom_eq D.R.k D.R.rS (T : ℝ) (T' : ℝ) hk _ 0 (fun b hb => ((ptLoc D v w).2.1 b hb).2)
    (by rw [zero_add]; exact (ptLoc D v w).2.2), ← GPoint_eq_gW, gpart D T T' v w (hG v)]
  congr 1
  show oprod (eG D.R.rS) 0 (locBlocksFrom D (rhoReal D) v 0 w.1) = _
  rw [eW_loc D v w.1 0 (fun b hb => (w.2.1 b hb).2) (by rw [zero_add, w.2.2]), ← fin_prod_oprod]
  refine Fintype.prod_equiv (finCongr (toComp_length w).symm) _ _ fun i => ?_
  simp only [zero_add]
  simp [Composition.blocksFun, toComp, toPts, endIdx, plOf_apply, absV, finCongr]
  rfl

end Weight

section Joint

variable (D : D7)

theorem ng_le (T T' : ℕ) (w : Point D.host.E (D.R.rS + 1)) :
    NGPt D.host.rdE (T * T') (toPts w) * NDPt D.host.rdE (toPts w) ≤ normWt D T T' w := by
  have hrd := one_le_rd D
  have hrd0 : 0 ≤ D.host.rdE := zero_le_one.trans hrd
  have hle : ∀ (N : ℕ) (x : ℝ), 0 ≤ x → (D.host.rdE ^ N)⁻¹ * x ≤ x := fun N x hx =>
    mul_le_of_le_one_left hx (inv_le_one_of_one_le₀ (one_le_pow₀ hrd))
  have hnn : ∀ (N : ℕ) (x : ℝ), 0 ≤ x → 0 ≤ (D.host.rdE ^ N)⁻¹ * x := fun N x hx =>
    mul_nonneg (inv_nonneg.2 (pow_nonneg hrd0 _)) hx
  unfold normWt
  refine mul_le_mul ?_ ?_ (Finset.prod_nonneg fun a _ => Finset.prod_nonneg fun p _ => hnn _ _ (sq_nonneg _))
    (Finset.prod_nonneg fun v _ => norm_nonneg _)
  · unfold NGPt NF
    rw [GPt_eq]
    calc ∏ p, (D.host.rdE ^ (2 * D.R.rS * (D.R.rS + 1)))⁻¹ * p (Gglob D T T' w)
        ≤ ∏ p : NumberField.InfinitePlace D.host.E, p (Gglob D T T' w) :=
          Finset.prod_le_prod₀ (fun p _ => hnn _ _ (apply_nonneg p _)) (fun p _ => hle _ _ (apply_nonneg p _))
      _ = ∏ v, absV D v (Gglob D T T' w) :=
          (Fintype.prod_bijective (plOf D) (plOf_bij D) _ _ fun v => (plOf_apply D v _).symm).symm
  · unfold NDPt
    refine (Finset.prod_le_prod₀ (fun a _ => Finset.prod_nonneg fun p _ => hnn _ _ (sq_nonneg _))
      (fun a _ => Finset.prod_le_prod₀ (fun p _ => hnn _ _ (sq_nonneg _)) (fun p _ => hle _ _ (sq_nonneg _)))).trans
      (le_of_eq ?_)
    rw [blockEnds_prod]
    symm
    refine Fintype.prod_equiv (finCongr (toComp_length w).symm) _ _ fun a => ?_
    have hle' : 0 + pS w.1 ((a : ℕ) + 1) ≤ D.R.rS + 1 := by rw [zero_add]; exact (toComp w).sizeUpTo_le _
    rw [dite_eq_left hle', NE]
    refine Fintype.prod_bijective (plOf D) (plOf_bij D) _ _ fun v => ?_
    rw [plOf_apply]
    congr 2
    show _ = Formalism.HermitianLatticeCounting.ExpansionTerms.IndexedMinorEntry (toComp w).blocksFun (toT w) _
    rw [E5minor_eq, leadMinorK_eq, ptMat_eq]
    simp [sizeUpTo_toComp]

theorem nPt_nonneg (k TT : ℕ) (γ : PN.Pts D.host.E D.R.rS) : 0 ≤ nPt D.host.rdE k TT γ := by
  have hrd0 : 0 ≤ D.host.rdE := zero_le_one.trans (one_le_rd D)
  unfold nPt
  exact Finset.prod_nonneg fun p _ => mul_nonneg
    (pow_nonneg (mul_nonneg (inv_nonneg.2 (pow_nonneg hrd0 _)) (apply_nonneg p _)) _)
    (Finset.prod_nonneg fun a _ => pow_nonneg (mul_nonneg (inv_nonneg.2 (pow_nonneg hrd0 _)) (apply_nonneg p _)) _)

theorem wt_core (T T' A : ℕ) (w : Point D.host.E (D.R.rS + 1)) (hG : ∀ v, 0 < Gpt (T : ℝ) (T' : ℝ) (ptLoc D v w)) :
    Formalism.HermitianLatticeCounting.ExpansionTerms.blockMinorWeight (toPts w) * nPt D.host.rdE D.R.k (T * T') (toPts w) *
              (NGPt D.host.rdE (T * T') (toPts w) * NDPt D.host.rdE (toPts w)) ^ (A * (D.R.rS + 1) ^ 2) ≤
      1 * (wPt D w * ptWeightG D (rhoReal D) T T' w.1 *
        normWt D T T' w ^ ((A : ℝ) * ((D.R.rS : ℝ) + 1) ^ 2)) := by
  have hrd0 : 0 ≤ D.host.rdE := zero_le_one.trans (one_le_rd D)
  have hW : 0 ≤ wPt D w * ptWeightG D (rhoReal D) T T' w.1 :=
    mul_nonneg (wPt_pos D w).le (by rw [← nPt_eq D T T' w hG]; exact nPt_nonneg D _ _ _)
  have h0 : 0 ≤ NGPt D.host.rdE (T * T') (toPts w) * NDPt D.host.rdE (toPts w) := by
    unfold NGPt NDPt
    exact mul_nonneg (Finset.prod_nonneg fun p _ => mul_nonneg (inv_nonneg.2 (pow_nonneg hrd0 _)) (apply_nonneg p _))
      (Finset.prod_nonneg fun a _ => Finset.prod_nonneg fun p _ =>
        mul_nonneg (inv_nonneg.2 (pow_nonneg hrd0 _)) (sq_nonneg _))
  rw [one_mul, show Formalism.HermitianLatticeCounting.ExpansionTerms.blockMinorWeight (toPts w) = wPt D w from (wPt_eq D w).symm, nPt_eq D T T' w hG,
    show ((A : ℝ) * ((D.R.rS : ℝ) + 1) ^ 2) = ((A * (D.R.rS + 1) ^ 2 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 (ng_le D T T' w) _) hW

end Joint

end Formalism.L2.SG.Pf.OrderedProducts

namespace Formalism.L2.SG.Pf

theorem weightConclusion : Formalism.L2.SG.ThmBUse.WtTieConc := fun D T T' A w hw =>
  Formalism.L2.SG.Pf.OrderedProducts.wt_core D T T' A w hw.2

end Formalism.L2.SG.Pf
end
end

noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.ThB
open scoped ENNReal

set_option linter.dupNamespace false

namespace Formalism.L2.SG.Pf.BDat

section Loc

variable (D : D7)

theorem kaRe_eq : kaRe D = Formalism.MainNotions.S.Bridge.kaS D := by
  unfold kaRe Formalism.MainNotions.S.Bridge.kaS gg
  rfl

abbrev locB (τ : D.what₂.Tau) (w w' : D.what₂.Word) (θ : ℝ) (W : LocW D.R.k D.R.rS)
    (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W) (hW : GoodW D τ w w' θ W) (hA : GoodS D lam A)
    (hT : 0 < Tr D w) (hT' : 0 < Tr D w') : LocBessel D.R.k D.R.rS :=
  Formalism.MainNotions.S.Pv.Frames.turnL (toBessel D τ w w' θ W lam A hW hA hT hT') (Formalism.MainNotions.S.Bridge.kaS D)

theorem toBessel_c (τ : D.what₂.Tau) (w w' : D.what₂.Word) (θ : ℝ) (W : LocW D.R.k D.R.rS)
    (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W) (hW : GoodW D τ w w' θ W) (hA : GoodS D lam A)
    (hT : 0 < Tr D w) (hT' : 0 < Tr D w') :
    (toBessel D τ w w' θ W lam A hW hA hT hT').c = ((2 * Formalism.MainNotions.S.Bridge.kaS D : ℝ) : ℂ) := by
  show ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) = _
  unfold Formalism.MainNotions.S.Bridge.kaS gg
  congr 1
  ring

theorem lOne_self {n : ℕ} (x : Fin n → ℝ) : l1 x x = 0 := by
  simp [l1]

theorem one_le_k : 1 ≤ D.R.k := by
  have := D.R.m_add_three_le_k
  omega

theorem m_le_k : ((2 * D.R.rS + 2 : ℕ) : ℝ) ≤ (D.R.k : ℝ) := by
  have h1 := dimS_eq D.R
  have h2 := D.R.two_le_m
  have h4 := D.R.m_add_three_le_k
  unfold Ranks.r at h1
  have h3 : 2 * D.R.rS + 2 ≤ D.R.k := by omega
  exact_mod_cast h3

theorem locOk_locB {Ch Cg b : ℝ} (τ : D.what₂.Tau) (w w' : D.what₂.Word) (θ : ℝ) (W : LocW D.R.k D.R.rS)
    (A : LocS W) (hW : GoodW D τ w w' θ W) (hA : GoodS D (lamD D τ) A) (hT : 0 < Tr D w) (hT' : 0 < Tr D w')
    (hka : 0 < Formalism.MainNotions.S.Bridge.kaS D) (hv : 0 < D.host.v) (hθ : 0 < θ)
    (hS : StdHyp Ch Cg D.R.k D.R.rS (epsSH D.R) (lamD D τ) (uS D w τ) (uS D w' τ) (Tr D w) (Tr D w')
      (Formalism.MainNotions.S.Bridge.kaS D) b)
    (hF : 1 ≤ Tr D w * Formalism.MainNotions.S.Bridge.kaS D ^ (2 * D.R.rS))
    (hF' : 1 ≤ Tr D w' * Formalism.MainNotions.S.Bridge.kaS D ^ (2 * D.R.rS)) :
    LocOk D Ch Cg (locB D τ w w' θ W (lamD D τ) A hW hA hT hT') (lamSH D.R (D.hc τ)) (kaRe D) b (kaRe D) := by
  have hz : Formalism.QuantumDeterminants.Tz D.R.k D.R.rS W.z = Tr D w := hW.2.2.2.2.1
  have hz' : Formalism.QuantumDeterminants.Tz D.R.k D.R.rS W.z' = Tr D w' := hW.2.2.2.2.2.1
  have hkk : kaRe D / kaRe D = 1 := by rw [kaRe_eq]; exact div_self hka.ne'
  refine ⟨one_le_k D, rfl, ?_, ?_, ENNReal.ofReal_ne_top, ?_, ?_, ?_⟩
  · show Formalism.MainNotions.S.cOfDpsi ((Formalism.MainNotions.S.Bridge.kaS D : ℝ) : ℂ) = Formalism.MainNotions.S.cOfDpsi ((kaRe D : ℝ) : ℂ)
    rw [kaRe_eq]
  · show 0 < ENNReal.ofReal ((2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * θ)
    exact ENNReal.ofReal_pos.2 (mul_pos (Real.rpow_pos_of_pos (by positivity) _) hθ)
  · show StdHyp Ch Cg D.R.k D.R.rS (epsSH D.R) (lamD D τ) (uS D w τ) (uS D w' τ)
      (Formalism.QuantumDeterminants.Tz D.R.k D.R.rS W.z * (kaRe D / kaRe D) ^ (2 * D.R.rS))
      (Formalism.QuantumDeterminants.Tz D.R.k D.R.rS W.z' * (kaRe D / kaRe D) ^ (2 * D.R.rS)) (kaRe D) b
    rw [hkk, one_pow, mul_one, mul_one, hz, hz', kaRe_eq]
    exact hS
  · show 1 ≤ Formalism.QuantumDeterminants.Tz D.R.k D.R.rS W.z * kaRe D ^ (2 * D.R.rS)
    rw [hz, kaRe_eq]; exact hF
  · show 1 ≤ Formalism.QuantumDeterminants.Tz D.R.k D.R.rS W.z' * kaRe D ^ (2 * D.R.rS)
    rw [hz', kaRe_eq]; exact hF'

end Loc

section Build

variable (D : D7)

structure Inputs (u u' : D.what₂.Word) (θ : ℝ) (hT : 0 < Tr D u) (hT' : 0 < Tr D u') where
  W : D.what₂.Tau → LocW D.R.k D.R.rS
  A : ∀ τ, LocS (W τ)
  hW : ∀ τ, GoodW D τ u u' θ (W τ)
  hA : ∀ τ, GoodS D (lamD D τ) (A τ)
  f : ∀ τ, Mx D.R.k D.R.rS →
    ((toBessel D τ u u' θ (W τ) (lamD D τ) (A τ) (hW τ) (hA τ) hT hT').Wq →L[ℂ]
      (toBessel D τ u u' θ (W τ) (lamD D τ) (A τ) (hW τ) (hA τ) hT hT').Wp)
  hf : ∀ τ, IsKFinCoefH (toBessel D τ u u' θ (W τ) (lamD D τ) (A τ) (hW τ) (hA τ) hT hT').σ (f τ)

variable {D}

abbrev Inputs.L {u u' : D.what₂.Word} {θ : ℝ} {hT : 0 < Tr D u} {hT' : 0 < Tr D u'} (I : Inputs D u u' θ hT hT')
    (τ : D.what₂.Tau) : LocBessel D.R.k D.R.rS :=
  locB D τ u u' θ (I.W τ) (lamD D τ) (I.A τ) (I.hW τ) (I.hA τ) hT hT'

def Inputs.sec {u u' : D.what₂.Word} {θ : ℝ} {hT : 0 < Tr D u} {hT' : 0 < Tr D u'} (I : Inputs D u u' θ hT hT')
    (τ : D.what₂.Tau) : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ :=
  (Formalism.MainNotions.BridgeLemma.section_exists D.R.k D.R.rS (I.L τ) (one_le_k D)).choose

theorem Inputs.sec_spec {u u' : D.what₂.Word} {θ : ℝ} {hT : 0 < Tr D u} {hT' : 0 < Tr D u'}
    (I : Inputs D u u' θ hT hT') (τ : D.what₂.Tau) :
    Formalism.QuantumDeterminants.IsSection D.R.k D.R.rS (I.L τ).z (I.L τ).z' (I.sec τ) :=
  (Formalism.MainNotions.BridgeLemma.section_exists D.R.k D.R.rS (I.L τ) (one_le_k D)).choose_spec

def bdOf {Ch Cg b : ℝ} {u u' : D.what₂.Word} {θ : ℝ} {hT : 0 < Tr D u} {hT' : 0 < Tr D u'}
    (I : Inputs D u u' θ hT hT')
    (hok : ∀ τ, LocOk D Ch Cg (I.L τ) (lamSH D.R (D.hc τ)) (kaRe D) b (kaRe D)) :
    BData D Ch Cg (D.mem u).A.T (D.mem u').A.T b 0 where
  L := I.L
  f τ := Formalism.MainNotions.S.Pv.Frames.turnF _ (Formalism.MainNotions.S.Bridge.kaS D) (I.f τ)
  μsec := I.sec
  hL := hok
  hnear τ := by rw [show (I.L τ).lam = lamSH D.R (D.hc τ) from rfl, lOne_self]
  hcoef τ := Formalism.MainNotions.S.Pv.Frames.turn_kfin _ _ (I.hf τ)
  hsec := I.sec_spec
  hT τ := ⟨(I.hW τ).2.2.2.2.1, (I.hW τ).2.2.2.2.2.1⟩

theorem gaps_bdOf {Ch Cg Cg' b : ℝ} {u u' : D.what₂.Word} {θ : ℝ} {hT : 0 < Tr D u} {hT' : 0 < Tr D u'}
    (I : Inputs D u u' θ hT hT') (hok : ∀ τ, LocOk D Ch Cg (I.L τ) (lamSH D.R (D.hc τ)) (kaRe D) b (kaRe D))
    (hg : ∀ τ, AllGaps (lamD D τ) (Cg' * D.R.k * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3)) (h0 : 0 ≤ Cg) (h1 : Cg ≤ Cg') :
    ∀ τ, AllGaps ((bdOf I hok).L τ).lam (Cg * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 4) := by
  intro τ s s' hss
  have hm := m_le_k D
  have hm0 : (0 : ℝ) ≤ ((2 * D.R.rS + 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have key : Cg * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 4 ≤ Cg' * D.R.k * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 := by
    have h3 : 0 ≤ ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 := pow_nonneg hm0 3
    have : Cg * ((2 * D.R.rS + 2 : ℕ) : ℝ) ≤ Cg' * D.R.k :=
      mul_le_mul h1 hm hm0 (h0.trans h1)
    calc Cg * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 4 = (Cg * ((2 * D.R.rS + 2 : ℕ) : ℝ)) * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 := by
          ring
      _ ≤ (Cg' * D.R.k) * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 := mul_le_mul_of_nonneg_right this h3
  exact key.trans (hg τ s s' hss)

theorem jSqG_bdOf {Ch Cg b : ℝ} {u u' : D.what₂.Word} {θ : ℝ} {hT : 0 < Tr D u} {hT' : 0 < Tr D u'}
    (I : Inputs D u u' θ hT hT') (hok : ∀ τ, LocOk D Ch Cg (I.L τ) (lamSH D.R (D.hc τ)) (kaRe D) b (kaRe D)) :
    jSqG D (bdOf I hok) =
      ∏ τ, jNorm2 (toBessel D τ u u' θ (I.W τ) (lamD D τ) (I.A τ) (I.hW τ) (I.hA τ) hT hT') (I.f τ) (I.sec τ) := by
  unfold jSqG
  refine Finset.prod_congr rfl fun τ _ => ?_
  exact Formalism.MainNotions.S.Pv.Frames.jNorm2_turn _ _ (toBessel_c D τ u u' θ _ _ _ _ _ hT hT') _ _

theorem orbSqO_le_bdOf {Ch Cg b : ℝ} {u u' : D.what₂.Word} {θ : ℝ} {hT : 0 < Tr D u} {hT' : 0 < Tr D u'}
    (I : Inputs D u u' θ hT hT') (hok : ∀ τ, LocOk D Ch Cg (I.L τ) (lamSH D.R (D.hc τ)) (kaRe D) b (kaRe D))
    (hka : 0 < Formalism.MainNotions.S.Bridge.kaS D) (τ : D.what₂.Tau) (p : Point ℂ (D.R.rS + 1)) :
    Formalism.MainNotions.S.Bridge.orbSqO (toBessel D τ u u' θ (I.W τ) (lamD D τ) (I.A τ) (I.hW τ) (I.hA τ) hT hT') (I.f τ) p ≤
      orbSq ((bdOf I hok).L τ) ((bdOf I hok).f τ) (Formalism.MainNotions.S.Pv.Frames.turnPt p) :=
  Formalism.MainNotions.S.Pv.Frames.orbSqO_le_turn _ _ hka (toBessel_c D τ u u' θ _ _ _ _ _ hT hT') _ _

end Build

section Amp

open Formalism.QuantumDeterminants

variable {D : D7}

structure AmpIn (large₂ : SizeData₂ D) (C1 Ca : ℝ) (u u' : D.what₂.Word) (θ : ℝ) (hT : 0 < Tr D u) (hT' : 0 < Tr D u')
    extends Inputs D u u' θ hT hT' where
  K : D.what₂.Tau → ℝ
  hK : ∀ τ, 0 < K τ
  hMM : ∀ τ μsec, IsSection D.R.k D.R.rS (W τ).z (W τ).z' μsec →
    ENNReal.ofReal (K τ) *
      jNorm2 (toBessel D τ u u' θ (W τ) (lamD D τ) (A τ) (hW τ) (hA τ) hT hT') (f τ) μsec ≤ MMv D u u' (A τ) μsec
  hJ : ∀ τ γ p, RelPt D (W τ).z (W τ).z' γ p → ∀ θ', normWin D large₂ C1 θ' → ∀ νR, RMeas D (W τ) γ θ' νR →
    ENNReal.ofReal (hsNormSq ((A τ).J νR γ)) ≤
      ENNReal.ofReal (K τ * large₂.sc.b ^ (Ca * (D.R.m : ℝ) ^ 2)) *
        Formalism.MainNotions.S.Bridge.orbSqO (toBessel D τ u u' θ (W τ) (lamD D τ) (A τ) (hW τ) (hA τ) hT hT') (f τ) p

def JointAmplitudeFactorization {τ₀ Rw I₀ H H₁ : Type} [Fintype I₀] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : Formalism.FourierDecayAlt.PB.Terms τ₀ Rw I₀ H H₁)
    {Cl Nu : Type} (N : Formalism.FourierDecayAlt.PN.NGData τ₀ D.host.E D.R.rS Cl Nu) (large₂ : SizeData₂ D) (C1 : ℝ)
    (W : D.what₂.Tau → LocW D.R.k D.R.rS) (A : ∀ τ, LocS (W τ)) (T T' : ℕ) (Cfac : ℝ) : Prop :=
  ∀ γ (w : Point D.host.E (D.R.rS + 1)), Formalism.FourierDecayAlt.PN.IsPt X N γ → Formalism.L2.SG.RowsConc.toPts w = γ →
    Formalism.L2.SG.ThmBUse.IsRowPt D T T' w → 0 < N.jacobianSquareBound γ →
    ∃ (g : D.what₂.Tau → MatKR D.R.k D.R.rS) (p : D.what₂.Tau → Point ℂ (D.R.rS + 1)) (θ' : D.what₂.Tau → ℝ)
      (νR : D.what₂.Tau → Measure (Mt D.R.k D.R.rS)),
      (∀ τ, RelPt D (W τ).z (W τ).z' (g τ) (p τ) ∧ normWin D large₂ C1 (θ' τ) ∧ RMeas D (W τ) (g τ) (θ' τ) (νR τ) ∧
        Formalism.MainNotions.S.Pv.Frames.turnPt (p τ) = ptLoc D τ w) ∧
      ENNReal.ofReal (N.jacobianSquareBound γ) ≤ ENNReal.ofReal Cfac * ∏ τ, ENNReal.ofReal (hsNormSq ((A τ).J (νR τ) (g τ)))

theorem jSqG_le_MM {large₂ : SizeData₂ D} {C1 Ca Ch Cg b : ℝ} {u u' : D.what₂.Word} {θ : ℝ} {hT : 0 < Tr D u}
    {hT' : 0 < Tr D u'} (I : AmpIn large₂ C1 Ca u u' θ hT hT')
    (hok : ∀ τ, LocOk D Ch Cg (I.L τ) (lamSH D.R (D.hc τ)) (kaRe D) b (kaRe D)) :
    ENNReal.ofReal (∏ τ, I.K τ) * jSqG D (bdOf I.toInputs hok) ≤ ∏ τ, MMv D u u' (I.A τ) (I.sec τ) := by
  rw [jSqG_bdOf, ENNReal.ofReal_prod_of_nonneg (fun τ _ => (I.hK τ).le), ← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod' fun τ _ => I.hMM τ (I.sec τ) (I.sec_spec τ)

end Amp

section Conc

open scoped Classical
open Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.LocWSOf Formalism.QuantumDeterminants NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def PtFacts {D : D7} {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word) : Prop :=
  ∀ t ∈ (Y.tO u u').ngSet, (Y.tO u u').vec t ≠ 0 →
    Formalism.L2.SG.ThmBUse.IsRowPt D (D.mem u).A.T (D.mem u').A.T (Formalism.L2.SG.PairVal.ptOf t.toTerm)

theorem point_amplitude_relation_normalized {D : D7} {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word) (h : PtFacts Y u u')
    (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : Formalism.FourierDecayAlt.PN.Pts D.host.E D.R.rS → ℝ) :
    Formalism.L2.SG.ThmBUse.PtTie (Y.tO u u') (NOf2 Y u u' νL νB ng) (D.mem u).A.T (D.mem u').A.T := by
  rintro γ ⟨c, ν, t, ht, hv, -, hpt, -⟩
  exact ⟨Formalism.L2.SG.PairVal.ptOf t.toTerm, hpt, h t ht hv⟩

abbrev WX {D : D7} {X : HidaSetting D} {θ : ℝ} (C : Choice X θ) (u u' : D.what₂.Word) : D.what₂.Tau → LocW D.R.k D.R.rS :=
  fun τ => locW C u u' τ

abbrev AX {D : D7} {X : HidaSetting D} {θ : ℝ} {C : Choice X θ} (hB : WuBessel C) (u u' : D.what₂.Word) :
    ∀ τ, LocS (WX C u u' τ) :=
  fun τ => locS hB u u' τ

def RowBData {D : D7} (large₂ : SizeData₂ D) {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word)
    (νB : X.B.I.Ginf → Measure X.B.I.Ginf) (C1 Cn Ire : ℝ) : Prop :=
  0 ≤ Ire ∧ ∃ (θ : ℝ) (C : Choice X θ) (hB : WuBessel C), 0 < θ ∧ normWin D large₂ C1 θ ∧
    (∀ τ, ColsTypeTr C u τ ∧ ColsTypeTr C u' τ ∧ ZTr C u τ ∧ ZTr C u' τ ∧ HaarTr C τ ∧ GoodSRest hB u u' τ) ∧
    ∃ Cfac : ℝ, 0 ≤ Cfac ∧
      (∀ (νL : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : Formalism.FourierDecayAlt.PN.Pts D.host.E D.R.rS → ℝ),
        JointAmplitudeFactorization (Y.tO u u') (NOf2 Y u u' νL νB ng) large₂ C1 (WX C u u') (AX hB u u') (D.mem u).A.T (D.mem u').A.T Cfac) ∧
      ∀ sec : D.what₂.Tau → ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ,
        (∀ τ, IsSection D.R.k D.R.rS (WX C u u' τ).z (WX C u u' τ).z' (sec τ)) →
        ENNReal.ofReal Cfac * ∏ τ, MMv D u u' (AX hB u u' τ) (sec τ) ≤
          ENNReal.ofReal (large₂.sc.b ^ (Cn * (D.R.m : ℝ) ^ 2 * D.R.f) * Ire)

def AmpUnif : Prop :=
  ∀ Cg cb Cu cT CT C0 C1 : ℝ, ∃ Ca : ℝ, 0 ≤ Ca ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D), Formalism.MainNotions.S.Bridge.AmpIsBessel D large₂ C' Cl Cg cb Cu cT CT C0 0 C1 Ca

def PtUnif : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' → PtFacts Y u u'

def RowBDataUnif : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C1 Cn : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
        (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ), MassDataTie X hb X0 ψ →
      ∀ (sd C Th : ℝ) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
        (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))
        (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
        (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (Irat Ire : ℝ),
        MassDataAdmissible X Y u u' (bkU X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq) Irat Ire →
      ∀ ν, Pinned X u u' ν → RowBData large₂ Y u u' ν C1 Cn Ire

end Conc

section Final

open scoped Classical
open Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.LocWSOf Formalism.QuantumDeterminants NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def ampInOf {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT C0 C1 Ca : ℝ}
    (hAmp : Formalism.MainNotions.S.Bridge.AmpIsBessel D large₂ C' Cl Cg cb Cu cT CT C0 0 C1 Ca)
    (hH : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) {u u' : D.what₂.Word} (hTT : HypTT D u u') {θ : ℝ}
    (hθ : normWin D large₂ C1 θ) (hT : 0 < Tr D u) (hT' : 0 < Tr D u')
    (W : D.what₂.Tau → LocW D.R.k D.R.rS) (A : ∀ τ, LocS (W τ)) (hW : ∀ τ, GoodW D τ u u' θ (W τ))
    (hA : ∀ τ, GoodS D (lamD D τ) (A τ)) : AmpIn large₂ C1 Ca u u' θ hT hT' :=
  have hd : ∀ τ, l1dist (lamD D τ) (lamD D τ) ≤ 0 * D.R.k * (D.R.m : ℝ) ^ 3 := fun τ => by simp [l1dist]
  have h := fun τ => hAmp hH τ u u' hTT θ hθ (W τ) (hW τ) (lamD D τ) (hd τ) (A τ) (hA τ) hT hT'
  { W := W, A := A, hW := hW, hA := hA, f := fun τ => (h τ).choose,
    hf := fun τ => (h τ).choose_spec.choose_spec.2.1,
    K := fun τ => (h τ).choose_spec.choose, hK := fun τ => (h τ).choose_spec.choose_spec.1,
    hMM := fun τ μsec hs => ((h τ).choose_spec.choose_spec.2.2.1 μsec hs).2,
    hJ := fun τ => (h τ).choose_spec.choose_spec.2.2.2 }

theorem m_eq' (D : D7) : ((2 * D.R.rS + 2 : ℕ) : ℝ) = (D.R.m : ℝ) := by
  have h1 := dimS_eq D.R
  have h2 := D.R.two_le_m
  unfold Ranks.r at h1
  have h3 : 2 * D.R.rS + 2 = D.R.m := by omega
  exact_mod_cast h3

theorem card_Tau (D : D7) : Fintype.card D.what₂.Tau = D.R.f := by
  rw [← Nat.card_eq_fintype_card, Nat.card_congr D.eTau]
  exact (Formalism.BasicNotions.factCardPsi D.R D.host).1

theorem cl_le_m {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT C0 : ℝ} (hH : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) :
    Cl ≤ (D.R.m : ℝ) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h24, _⟩ := hH.1
  exact h24

theorem expo_le (L f m Ca Cn Cb Cβ : ℝ) (hL : 0 ≤ L) (hf : 0 ≤ f) (hm : 1 ≤ m) (hβ : 0 ≤ Cβ) :
    Ca * m ^ 2 * f * L + Cb * m ^ 5 * f * (Cβ * L) + Cn * m ^ 2 * f * L ≤
      (max 0 Cb * Cβ + |Ca| + |Cn|) * m ^ 5 * f * L := by
  have hP : 0 ≤ f * L := mul_nonneg hf hL
  have hm2 : m ^ 2 ≤ m ^ 5 := pow_le_pow_right₀ hm (by norm_num)
  have hm5 : 0 ≤ m ^ 5 := by positivity
  have hm2' : 0 ≤ m ^ 2 := by positivity
  have h1 : Ca * m ^ 2 ≤ |Ca| * m ^ 5 :=
    (mul_le_mul_of_nonneg_right (le_abs_self Ca) hm2').trans (mul_le_mul_of_nonneg_left hm2 (abs_nonneg _))
  have h2 : Cn * m ^ 2 ≤ |Cn| * m ^ 5 :=
    (mul_le_mul_of_nonneg_right (le_abs_self Cn) hm2').trans (mul_le_mul_of_nonneg_left hm2 (abs_nonneg _))
  have h3 : Cb * Cβ * m ^ 5 ≤ max 0 Cb * Cβ * m ^ 5 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right 0 Cb) hβ) hm5
  have h4 : Ca * m ^ 2 + Cb * Cβ * m ^ 5 + Cn * m ^ 2 ≤ (max 0 Cb * Cβ + |Ca| + |Cn|) * m ^ 5 := by
    nlinarith [h1, h2, h3]
  calc Ca * m ^ 2 * f * L + Cb * m ^ 5 * f * (Cβ * L) + Cn * m ^ 2 * f * L
      = (Ca * m ^ 2 + Cb * Cβ * m ^ 5 + Cn * m ^ 2) * (f * L) := by ring
    _ ≤ ((max 0 Cb * Cβ + |Ca| + |Cn|) * m ^ 5) * (f * L) := mul_le_mul_of_nonneg_right h4 hP
    _ = (max 0 Cb * Cβ + |Ca| + |Cn|) * m ^ 5 * f * L := by ring

theorem normTie_bdOf {large₂ : SizeData₂ D} {C1 Ca Ch Cg Cβ Cb Cn Cfac Ire : ℝ} {u u' : D.what₂.Word} {θ : ℝ}
    {hT : 0 < Tr D u} {hT' : 0 < Tr D u'} (I : AmpIn large₂ C1 Ca u u' θ hT hT')
    (hok : ∀ τ, LocOk D Ch Cg (I.L τ) (lamSH D.R (D.hc τ)) (kaRe D) (large₂.sc.b ^ Cβ) (kaRe D))
    (hCfac : 0 ≤ Cfac) (hIre : 0 ≤ Ire) (hβ : 0 ≤ Cβ)
    (hNF : ENNReal.ofReal Cfac * ∏ τ, MMv D u u' (I.A τ) (I.sec τ) ≤
      ENNReal.ofReal (large₂.sc.b ^ (Cn * (D.R.m : ℝ) ^ 2 * D.R.f) * Ire)) :
    Formalism.L2.SG.ThmBUse.NormTie (bdOf I.toInputs hok) 1 (Cfac * ∏ τ, (I.K τ * large₂.sc.b ^ (Ca * (D.R.m : ℝ) ^ 2))) Cb
      (Real.exp ((max 0 Cb * Cβ + |Ca| + |Cn|) * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 5 * D.R.f * Real.log large₂.sc.b) * Ire) := by
  have hb1 : 1 < large₂.sc.b := by unfold Scale.b; exact Real.one_lt_exp_iff.2 (by
    have := large₂.sc.one_lt_alt; unfold Scale.L; exact lt_of_lt_of_le zero_lt_one (Real.one_le_rpow this.le large₂.sc.eps_pos.le))
  have hb0 : 0 < large₂.sc.b := by linarith
  have hlog : 0 ≤ Real.log large₂.sc.b := (Real.log_pos hb1).le
  have hcard : (Fintype.card D.what₂.Tau : ℝ) = D.R.f := by exact_mod_cast card_Tau D
  have hm := m_eq' D
  set c : ℝ := large₂.sc.b ^ (Ca * (D.R.m : ℝ) ^ 2) with hc
  have hc0 : 0 < c := Real.rpow_pos_of_pos hb0 _
  have hK0 : 0 ≤ ∏ τ, I.K τ := Finset.prod_nonneg fun τ _ => (I.hK τ).le
  have hprod : ∏ τ, (I.K τ * c) = (∏ τ, I.K τ) * c ^ Fintype.card D.what₂.Tau := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  set E : ℝ := Real.exp (Cb * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 5 * (Fintype.card D.what₂.Tau : ℝ) *
    Real.log (large₂.sc.b ^ Cβ)) with hE
  set B : ℝ := large₂.sc.b ^ (Cn * (D.R.m : ℝ) ^ 2 * D.R.f) with hB
  have hcpow : 0 ≤ c ^ Fintype.card D.what₂.Tau := pow_nonneg hc0.le _
  have hMM := jSqG_le_MM I hok

  have hreal : c ^ Fintype.card D.what₂.Tau * E * B ≤
      Real.exp ((max 0 Cb * Cβ + |Ca| + |Cn|) * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 5 * D.R.f * Real.log large₂.sc.b) := by
    rw [hc, hE, hB, Real.log_rpow hb0, Real.rpow_def_of_pos hb0, Real.rpow_def_of_pos hb0, ← Real.exp_nat_mul,
      ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp, hcard, hm]
    have := expo_le (Real.log large₂.sc.b) (D.R.f : ℝ) (D.R.m : ℝ) Ca Cn Cb Cβ hlog (Nat.cast_nonneg _)
      (by have := D.R.two_le_m; exact_mod_cast (by omega : 1 ≤ D.R.m)) hβ
    nlinarith [this]
  unfold Formalism.L2.SG.ThmBUse.NormTie
  rw [one_mul, hprod, ENNReal.ofReal_mul hCfac, ENNReal.ofReal_mul hK0]
  calc ENNReal.ofReal Cfac * (ENNReal.ofReal (∏ τ, I.K τ) * ENNReal.ofReal (c ^ Fintype.card D.what₂.Tau)) *
        (ENNReal.ofReal E * jSqG D (bdOf I.toInputs hok))
      = ENNReal.ofReal (c ^ Fintype.card D.what₂.Tau) * ENNReal.ofReal E *
          (ENNReal.ofReal Cfac * (ENNReal.ofReal (∏ τ, I.K τ) * jSqG D (bdOf I.toInputs hok))) := by ring
    _ ≤ ENNReal.ofReal (c ^ Fintype.card D.what₂.Tau) * ENNReal.ofReal E *
          (ENNReal.ofReal Cfac * ∏ τ, MMv D u u' (I.A τ) (I.sec τ)) := by gcongr
    _ ≤ ENNReal.ofReal (c ^ Fintype.card D.what₂.Tau) * ENNReal.ofReal E * ENNReal.ofReal (B * Ire) := by gcongr
    _ = ENNReal.ofReal (c ^ Fintype.card D.what₂.Tau * E * B * Ire) := by
        rw [← ENNReal.ofReal_mul hcpow, ← ENNReal.ofReal_mul (mul_nonneg hcpow (Real.exp_pos _).le),
          ← mul_assoc]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hreal hIre)

theorem hypTT_of {u u' : D.what₂.Word} (h : Formalism.MainNotions.S.Cnt.Stand D u u') : HypTT D u u' := by
  obtain ⟨-, hpu, hpu', h3u, h3u', -, -, -, -, -, -, -, hmod⟩ := h
  refine ⟨hpu, hpu', h3u, h3u', ?_⟩
  unfold Int.ModEq
  have e : (D.mem u).A.T % (D.host.g 0 * D.host.g 1) = (D.mem u').A.T % (D.host.g 0 * D.host.g 1) := hmod
  have e2 := congrArg (fun n : ℕ => (n : ℤ)) e
  simpa [Int.natCast_mod] using e2

theorem tr_pos {u u' : D.what₂.Word} (h : Formalism.MainNotions.S.Cnt.Stand D u u') : 0 < Tr D u ∧ 0 < Tr D u' := by
  obtain ⟨-, -, -, h3u, h3u', -⟩ := h
  exact ⟨Nat.cast_pos.2 (show 0 < (D.mem u).A.T from lt_of_lt_of_le (by norm_num) h3u),
    Nat.cast_pos.2 (show 0 < (D.mem u').A.T from lt_of_lt_of_le (by norm_num) h3u')⟩

end Final

section Gen

open scoped Classical
open Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.LocWSOf Formalism.QuantumDeterminants NumberField
  Formalism.L2.SG.Pf.MainEqCut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def PtFactsG {X : HidaSetting D} (Y : Full X) (u : D.what₂.Word) : Prop :=
  ∀ t ∈ (Y.tO u u).genSet, (Y.tO u u).vec t ≠ 0 →
    Formalism.L2.SG.ThmBUse.IsRowPt D (D.mem u).A.T (D.mem u).A.T (Formalism.L2.SG.PairVal.ptOf t.toTerm)

theorem ptTie_NOfG {X : HidaSetting D} (Y : Full X) (u : D.what₂.Word) (h : PtFactsG Y u)
    (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : Formalism.FourierDecayAlt.PN.Pts D.host.E D.R.rS → ℝ) :
    Formalism.L2.SG.ThmBUse.PtTie (genT (Y.tO u u)) (NOfG Y u νL νB ng) (D.mem u).A.T (D.mem u).A.T := by
  rintro γ ⟨c, ν, t, ht, hv, -, hpt, -⟩
  rw [genT_ngSet] at ht
  exact ⟨Formalism.L2.SG.PairVal.ptOf t.toTerm, hpt, h t ht hv⟩

theorem wtTie_NOfG {X : HidaSetting D} (Y : Full X) (u : D.what₂.Word) (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf)
    (ng : Formalism.FourierDecayAlt.PN.Pts D.host.E D.R.rS → ℝ) (A : ℕ) :
    Formalism.L2.SG.ThmBUse.WtTie (genT (Y.tO u u)) (NOfG Y u νL νB ng) (D.mem u).A.T (D.mem u).A.T A 1 := by
  intro γ w _ hw hb
  subst hw
  exact Formalism.L2.SG.Pf.weightConclusion D _ _ A w hb

end Gen

section GenStep

open scoped Classical
open Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.LocWSOf Formalism.QuantumDeterminants NumberField
  Formalism.L2.SG.Pf.MainEqCut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def PtUnifG : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u → PtFactsG Y u

def StepThmBG : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∀ A : ℕ, ∃ CB : ℝ, 0 ≤ CB ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u →
      ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
        (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ), MassDataTie X hb X0 ψ →
      ∀ (sd C Th : ℝ) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
        (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))
        (vR : Formalism.L2.SG.TermDef.Term D u u F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u F0 what₂)
        (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (Irat Ire : ℝ),
        MassDataAdmissible X Y u u (bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq) Irat Ire →
      ∀ ν, Pinned X u u ν → ∀ (νL : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : Formalism.FourierDecayAlt.PN.Pts D.host.E D.R.rS → ℝ),
        Formalism.FourierDecayAlt.PN.PointSumInput (genT (Y.tO u u)) (NOfG Y u νL ν ng) (A * (D.R.rS + 1) ^ 2)
          (Real.exp (CB * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 5 * D.R.f * Real.log large₂.sc.b) * Ire)

end GenStep

section Comparison₂

open scoped Classical
open Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.LocWSOf Formalism.QuantumDeterminants NumberField
  Formalism.L2.SG.Pf.MainEqCut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end Comparison₂

end Formalism.L2.SG.Pf.BDat
