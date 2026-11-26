module

public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CountDefs
public import Formalism.SharpRestriction.GrowthBounds.JointsLit

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.BinomialRatio.PairLift
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory

def FamOK (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (C0 CE1 CE2 Cm : ℝ) (X : Loc) [NeZero X.m]
    (β : ∀ j : Fin (numSeg X.TT), SegBlock (segS X.TT j) X.m)
    (u : ∀ j : Fin (numSeg X.TT), SegVs O X.m (segS X.TT j) (X.seg C0 CE1 CE2 j).t) : Prop :=
  ∀ j, u j ∈ Lj O C0 CE1 CE2 Cm X j ∧ ∀ b, b ≠ β j → u j b = 0


open Classical in
def PairLiftAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ct Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (jO : W →+* O) (w : O),
    UnramifiedQuadraticSetting X.p X.n' W Qq O Kf ι σ jO w → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X → 1 ≤ X.c →
    ∀ e : Edge W Qq (X.m + 1), IsEdge X.p X.n' 1 e →
      ∃ (κ : (∀ j : Fin (numSeg X.TT), SegBlock (segS X.TT j) X.m) → O)
        (F : (∀ j : Fin (numSeg X.TT), SegBlock (segS X.TT j) X.m) →
          (∀ j : Fin (numSeg X.TT), SegVs O X.m (segS X.TT j) (X.seg C0 CE1 CE2 j).t) →
          VHH (m := X.m) Kf X.TT X.aT X.bT)
        (G : (∀ j : Fin (numSeg X.TT), SegBlock (segS X.TT j) X.m) →
          (∀ j : Fin (numSeg X.TT), SegVs O X.m (segS X.TT j) (X.seg C0 CE1 CE2 j).t) →
          Module.Dual Kf (VHH (m := X.m) Kf X.TT X.aT X.bT)),
        (∀ β, κ β ≠ 0 ∧ vLEO X.p (κ β) (4 * X.kap0)) ∧
        (∀ β u, FamOK O C0 CE1 CE2 Cm X β u →
          F β u ∈ CCe X.p ι σ w X.TT X.aT X.bT ⌊X.t0 C0 Ct⌋₊ X.c e ∧
          G β u ∈ CCe' X.p ι σ w X.TT X.aT X.bT ⌊X.t0 C0 Ct⌋₊ X.c e) ∧
        ∀ β u β' u', FamOK O C0 CE1 CE2 Cm X β u → FamOK O C0 CE1 CE2 Cm X β' u' →
          ∀ a : Fin (numSeg X.TT) → O,
            (∀ j, segForm O X.p X.m (X.seg C0 CE1 CE2 j) (u j) (u' j) = algebraMap O (KK O) (a j)) →
            ∃ ν : O, beHH (m := X.m) X.p X.TT X.aT X.bT (F β u) (G β' u') =
              algebraMap O Kf ((if β = β' then κ β * ∏ j, a j else 0) + w ^ X.c * ν)

private theorem addVal_toNat_mul_of_ne_zero {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {a b : O} (ha : a ≠ 0) (hb : b ≠ 0) :
    (IsDiscreteValuationRing.addVal O (a * b)).toNat =
      (IsDiscreteValuationRing.addVal O a).toNat + (IsDiscreteValuationRing.addVal O b).toNat := by
  have ha' : IsDiscreteValuationRing.addVal O a ≠ ⊤ := by
    rwa [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
  have hb' : IsDiscreteValuationRing.addVal O b ≠ ⊤ := by
    rwa [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
  rw [AddValuation.map_mul, ENat.toNat_add ha' hb']

private theorem vO_eq_addVal_div_ramE_of_ne_zero' {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) {z : O}
    (hz : z ≠ 0) :
    vO p z = ((((IsDiscreteValuationRing.addVal O z).toNat : ℚ) / (ramE p O : ℚ) : ℚ) : WithTop ℚ) := by
  have hz' : algebraMap O (KK O) z ≠ 0 := by
    intro h
    exact hz ((IsFractionRing.to_map_eq_zero_iff).mp h)
  have hspec := Classical.choose_spec (IsLocalization.surj (nonZeroDivisors O) (algebraMap O (KK O) z))
  simp only [vO, vK, ordW, if_neg hz']
  generalize Classical.choose (IsLocalization.surj (nonZeroDivisors O) (algebraMap O (KK O) z)) = ab at hspec ⊢
  rw [← map_mul] at hspec
  have hmul : z * (ab.2 : O) = ab.1 := IsFractionRing.injective O (KK O) hspec
  have hb : (ab.2 : O) ≠ 0 := nonZeroDivisors.coe_ne_zero ab.2
  rw [← hmul, addVal_toNat_mul_of_ne_zero hz hb]
  simp only [WithTop.map_coe]
  congr 1
  push_cast
  ring

theorem vLEO_mul {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {p : ℕ} {w : O} (hw : Irreducible w)
    (h2 : w ^ 2 = (p : O)) {x y : O} (hx : x ≠ 0) (hy : y ≠ 0) {D E : ℝ} (h : vLEO p x D) (h' : vLEO p y E) :
    vLEO p (x * y) (D + E) := by
  obtain ⟨q, hq, hqD⟩ := h
  obtain ⟨q', hq', hqE⟩ := h'
  rw [vO_eq_addVal_div_ramE_of_ne_zero' p hx] at hq
  rw [vO_eq_addVal_div_ramE_of_ne_zero' p hy] at hq'
  have e1 := WithTop.coe_eq_coe.mp hq
  have e2 := WithTop.coe_eq_coe.mp hq'
  refine ⟨q + q', ?_, ?_⟩
  · rw [vO_eq_addVal_div_ramE_of_ne_zero' p (mul_ne_zero hx hy), addVal_toNat_mul_of_ne_zero hx hy, ← e1, ← e2]
    congr 1
    push_cast
    ring
  · push_cast
    linarith

theorem vLEO_prod {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {p : ℕ} {w : O} (hw : Irreducible w)
    (h2 : w ^ 2 = (p : O)) {ι : Type} (s : Finset ι) (z : ι → O) (D : ι → ℝ)
    (h : ∀ i ∈ s, z i ≠ 0 ∧ vLEO p (z i) (D i)) : (∏ i ∈ s, z i) ≠ 0 ∧ vLEO p (∏ i ∈ s, z i) (∑ i ∈ s, D i) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    rw [Finset.prod_empty, Finset.sum_empty]
    refine ⟨one_ne_zero, 0, ?_, by simp⟩
    rw [vO_eq_addVal_div_ramE_of_ne_zero' p one_ne_zero]
    simp
  · intro a s ha ih hh
    have hs : ∀ i ∈ s, z i ≠ 0 ∧ vLEO p (z i) (D i) := fun i hi => hh i (Finset.mem_insert_of_mem hi)
    obtain ⟨h1, h1'⟩ := ih hs
    obtain ⟨ha0, ha1⟩ := hh a (Finset.mem_insert_self a s)
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact ⟨mul_ne_zero ha0 h1, vLEO_mul hw h2 ha0 h1 ha1 h1'⟩

theorem liftVecAt_of {C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ct Cc H : ℝ}
    (hstd : ∀ X : Loc, D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X → Std C0 Cde CE1 CE2 H X)
    (h : PairLiftAt C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ct Cc) : LiftVecAt C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ct Cc := by
  classical
  intro X _ W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ jO w hS hH hc Dj g hD hBD hcD e he
  have hD1 : D1num X := ⟨hS.1.prime, hS.1.five_le, hS.1.two_le, hS.1.even⟩
  have hs := hstd X hD1 hH hc
  have hw : Irreducible w := hS.2.1
  have h2 : w ^ 2 = (X.p : O) := hS.1.w_sq
  have hkap : 0 ≤ X.kap0 := by
    have hk : 0 ≤ X.k := by unfold Loc.k; positivity
    have hN : 0 ≤ X.N := by unfold Loc.N; positivity
    have hp : (1 : ℝ) < (X.p : ℝ) := by have := hs.p5; exact_mod_cast (by omega : 1 < X.p)
    have hl : 0 ≤ Real.logb X.p X.a := by
      unfold Real.logb
      exact div_nonneg (le_trans zero_le_one hs.loga) (Real.log_nonneg hp.le)
    unfold Loc.kap0 kap0G4
    positivity
  have hc1 : 1 ≤ X.c := by
    have hsum : 0 ≤ ∑ j, Dj j := Finset.sum_nonneg fun j _ => hD j
    have : (0 : ℝ) < (X.c : ℝ) := by linarith
    exact_mod_cast this
  obtain ⟨κ, F, G, hκ, hmem, hpair⟩ := h X W Qq O Kf ι σ jO w hS hH hc hc1 e he
  choose x y β z hxy hsupp hz hform using hBD
  have hfx : ∀ I : (∀ j, Fin (g j)), FamOK O C0 CE1 CE2 Cm X (fun j => β j (I j)) (fun j => x j (I j)) :=
    fun I j => ⟨(hxy j (I j)).1, fun b hb => (hsupp j (I j) b hb).1⟩
  have hfy : ∀ I : (∀ j, Fin (g j)), FamOK O C0 CE1 CE2 Cm X (fun j => β j (I j)) (fun j => y j (I j)) :=
    fun I j => ⟨(hxy j (I j)).2, fun b hb => (hsupp j (I j) b hb).2⟩
  refine ⟨fun I => F (fun j => β j (I j)) (fun j => x j (I j)), fun I => G (fun j => β j (I j)) (fun j => y j (I j)),
    fun I => κ (fun j => β j (I j)) * ∏ j, z j (I j), fun I => (hmem _ _ (hfx I)).1, fun I => (hmem _ _ (hfy I)).2, ?_, ?_⟩
  · intro I
    have hp := vLEO_prod hw h2 Finset.univ (fun j => z j (I j)) Dj fun j _ => hz j (I j)
    refine ⟨mul_ne_zero (hκ _).1 hp.1, ?_⟩
    have := vLEO_mul hw h2 (hκ _).1 hp.1 (hκ (fun j => β j (I j))).2 hp.2
    rwa [add_comm] at this
  · intro I J
    obtain ⟨ν, hν⟩ := hpair _ _ _ _ (hfx I) (hfy J) (fun j => if I j = J j then z j (I j) else 0) (fun j => by
      rw [hform j (I j) (J j)]
      split_ifs <;> simp)
    refine ⟨ν, ?_⟩
    rw [hν]
    congr 2
    by_cases hIJ : I = J
    · subst hIJ
      simp
    · rw [if_neg hIJ]
      obtain ⟨j0, hj0⟩ := Function.ne_iff.mp hIJ
      have h0 : (∏ j, if I j = J j then z j (I j) else 0) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ j0) (if_neg hj0)
      rw [h0, mul_zero]
      simp

def RestPairLift : Prop :=
  TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc => ∃ Ct0 : ℝ, 0 < Ct0 ∧ ∀ Ct : ℝ, Ct0 ≤ Ct →
    PairLiftAt C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ct Cc

theorem restLiftVec_of (h : RestPairLift) : RestLiftVec := by
  unfold RestPairLift at h
  unfold RestLiftVec
  refine TransportedAlt.mono ?_ (TransportedAlt.and thr_std h)
  intro C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc hh
  obtain ⟨⟨_, hstd⟩, Ct0, hCt0, hall⟩ := hh
  exact ⟨Ct0, hCt0, fun Ct hCt => liftVecAt_of hstd (hall Ct hCt)⟩

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.BinomialRatio.ChainDim
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

theorem card_tuples (r g : ℕ) (hr : 0 < r) : Nat.card {P : Fin r → ℕ // ∑ i, P i = g} = sdXi r g := by
  classical
  rw [← Nat.card_congr (Sym.equivNatSumOfFintype (Fin r) g), Nat.card_eq_fintype_card, Sym.card_sym_eq_choose,
    Fintype.card_fin]
  unfold sdXi
  rw [show r + g - 1 = g + r - 1 by omega]
  exact Nat.choose_symm_of_eq_add (by omega)

def monoEquiv (N r : ℕ) (d : Fin N → ℕ) :
    ↥({m | ∀ i, multideg m i = d i} : Set (Fin N × Fin r →₀ ℕ)) ≃ (∀ i, {P : Fin r → ℕ // ∑ c, P c = d i}) where
  toFun m := fun i => ⟨fun c => m.1 (i, c), m.2 i⟩
  invFun f := ⟨Finsupp.equivFunOnFinite.symm (fun x => (f x.1).1 x.2), fun i => by
    show ∑ c, (Finsupp.equivFunOnFinite.symm (fun x : Fin N × Fin r => (f x.1).1 x.2)) (i, c) = d i
    simpa using (f i).2⟩
  left_inv m := by
    apply Subtype.ext
    ext x
    simp
  right_inv f := by
    funext i
    apply Subtype.ext
    funext c
    simp

theorem finrank_Pol (K : Type*) [Field K] (N r : ℕ) (hr : 0 < r) (d : Fin N → ℕ) :
    Module.finrank K (Pol K r d) = ∏ i, sdXi r (d i) := by
  classical
  unfold Pol
  rw [Module.finrank_eq_nat_card_basis (MvPolynomial.basisRestrictSupport K _), Nat.card_congr (monoEquiv N r d),
    Nat.card_pi]
  exact Finset.prod_congr rfl fun i _ => card_tuples r (d i) hr

instance fact5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩

def dvr5 : UniformizedDVR 5 ℤ_[5] where
  w := (5 : ℕ)
  w_irr := PadicInt.irreducible_p
  p_mem := by
    rw [PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.mem_span_singleton_self _
  p_ne := by exact_mod_cast (by norm_num : (5 : ℕ) ≠ 0)
  complete := inferInstance

theorem chainDim_of (hY : DimYAt) : ChainDimAt := by
  intro N r _ LL
  have h := hY 5 ℤ_[5] dvr5 N r LL 0 Fin.elim0 Fin.elim0 (fun k => k.elim0)
  rw [← h]
  unfold Yjt chPol
  rw [iInf_of_empty, inf_top_eq, finrank_Pol _ N r (NeZero.pos r) LL.deg, Nat.cast_prod]

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.BinomialRatio.RankOnDigitsCast
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

theorem cast_finsum {α : Sort*} (f : α → ℕ) : ((∑ᶠ a, f a : ℕ) : ℚ) = ∑ᶠ a, (f a : ℚ) :=
  AddMonoidHom.map_finsum_of_injective (Nat.castAddMonoidHom ℚ) Nat.cast_injective f

theorem segTies_J_le {s r : ℕ} (p : ℕ) (S : SegData s) (b : SegBlock s r) (k : Fin (segTies p S b).q) :
    (segTies p S b).J k ≤ 2 * s + 1 := by
  unfold segTies
  dsimp only
  split_ifs with h
  · have := (uTop S ⟨k, h⟩).2
    omega
  · exact le_rfl

theorem blockRank_cast (hB : BlockRankAt) (hY : DimYAt) (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (Sd : UniformizedDVR p O) {s r : ℕ} [NeZero r] (S : SegData s) (aTop : Fin s → ℕ)
    (aPlus : ℕ) (m : ℝ) (b : SegBlock s r) :
    (blockRank O p r S aTop aPlus m b : ℚ) =
      (let D := blockData p S aTop aPlus m b
       open Classical in
       ∑ᶠ x : (Fin D.T.t → ℕ) × ℕ, if D.LevelOK x.1 x.2 then
        chainSum (r := r) (D.lettersAt x.1 x.2) D.T.J D.T.thr * (sdXi r (D.B - x.2) : ℚ) else 0) := by
  classical
  have h1 := hB O (2 * s + 1) r (blockData p S aTop aPlus m b)
  have h2 : blockRank O p r S aTop aPlus m b =
      Module.finrank (KK O) (Submodule.span (KK O)
        (((blockData p S aTop aPlus m b).SSZ O (r := r) :
            Submodule O (MvPolynomial (BVar (2 * s + 1) r (blockData p S aTop aPlus m b).T.t) (KK O))) :
          Set (MvPolynomial (BVar (2 * s + 1) r (blockData p S aTop aPlus m b).T.t) (KK O)))) := rfl
  rw [h2, h1, cast_finsum]
  dsimp only
  refine finsum_congr fun x => ?_
  by_cases hx : (blockData p S aTop aPlus m b).LevelOK x.1 x.2
  · rw [if_pos hx, if_pos hx]
    push_cast
    congr 1
    exact hY p O Sd (2 * s + 1) r _ _ _ _ (fun k => segTies_J_le p S b k)
  · rw [if_neg hx, if_neg hx]
    simp

theorem rankOnDigits_cast (hB : BlockRankAt) (hY : DimYAt) (C0 CE1 CE2 : ℝ) (X : Loc) [NeZero X.m] [Fact X.p.Prime]
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Sd : UniformizedDVR X.p O)
    (j : Fin (numSeg X.TT)) (m : ℝ) (rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ) :
    (rankOnDigits O C0 CE1 CE2 X j m rz ry : ℚ) = chainCount C0 CE1 CE2 X j m rz ry := by
  classical
  unfold rankOnDigits chainCount
  rw [cast_finsum]
  refine finsum_congr fun b => ?_
  by_cases hb : Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b ∧ b.rz = rz ∧ b.ry = ry
  · rw [if_pos hb, if_pos hb]
    exact blockRank_cast hB hY X.p O Sd _ _ _ m b
  · rw [if_neg hb, if_neg hb]
    simp

theorem restUp_of (hB : BlockRankAt) (hY : DimYAt) (_hCZ : CharZeroAt) (hC : RestCountUp) : RestUp := by
  refine TransportedAlt.mono ?_ hC
  intro C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc h X _ W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ jO w hS hH hc j m hm rz ry hd
  have hD1 : D1num X := ⟨hS.1.prime, hS.1.five_le, hS.1.two_le, hS.1.even⟩
  haveI : Fact X.p.Prime := ⟨hS.1.prime⟩
  have h1 := h X hD1 hH hc j m hm rz ry hd
  rw [← rankOnDigits_cast hB hY C0 CE1 CE2 X O (dvrOfStd hS) j m rz ry] at h1
  exact_mod_cast h1

theorem restLow_of (hB : BlockRankAt) (hY : DimYAt) (_hCZ : CharZeroAt) (hC : RestCountLow) : RestLow := by
  refine TransportedAlt.mono ?_ hC
  intro C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc h X _ W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ jO w hS hH hc j m hm hm2 rz ry hd
  have hD1 : D1num X := ⟨hS.1.prime, hS.1.five_le, hS.1.two_le, hS.1.even⟩
  haveI : Fact X.p.Prime := ⟨hS.1.prime⟩
  have h1 := h X hD1 hH hc j m hm hm2 rz ry hd
  rw [← rankOnDigits_cast hB hY C0 CE1 CE2 X O (dvrOfStd hS) j m rz ry] at h1
  simpa using h1

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.BinomialRatio.StWeyl
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

theorem wdim_shift {r : ℕ} (lam : Fin r → ℤ) (c : ℤ) : wdim (fun i => lam i + c) = wdim lam := by
  unfold wdim
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  split_ifs
  · congr 1
    push_cast
    ring
  · rfl

theorem wdim_nat {r : ℕ} (nu : Fin r → ℕ) :
    wdim (fun i => (nu i : ℤ)) = ∏ i : Fin r, ∏ j : Fin r,
      if i < j then ((nu i : ℚ) - (nu j : ℚ) + (j : ℚ) - (i : ℚ)) / ((j : ℚ) - (i : ℚ)) else 1 := by
  unfold wdim
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  simp only [Int.cast_natCast]

theorem antitone_of_interlace {r : ℕ} {lamN : Fin (r + 1) → ℕ} (hl : Antitone lamN) (nu : Fin r → ℕ)
    (h : ∀ i : Fin r, lamN i.succ ≤ nu i ∧ nu i ≤ lamN i.castSucc) : Antitone nu := by
  intro i j hij
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact le_rfl
  · have h1 : i.succ ≤ j.castSucc := by
      rw [Fin.le_def]
      have : (i : ℕ) < (j : ℕ) := hlt
      simpa using this
    exact ((h j).2.trans (hl h1)).trans (h i).1

theorem numBranch_of {D : Formalism.BasicNotions.D7} (h2 : adm2 D) (h3 : adm3 D) : NumBranchAt := by
  intro r mu hmu
  classical
  set c : ℤ := mu (Fin.last r) with hc
  let lamN : Fin (r + 1) → ℕ := fun i => (mu i - c).toNat
  have hge : ∀ i, c ≤ mu i := fun i => hmu (Fin.le_last i)
  have hcast : ∀ i, (lamN i : ℤ) = mu i - c := fun i => Int.toNat_of_nonneg (by linarith [hge i])
  have hanti : Antitone lamN := by
    intro i j hij
    have h1 := hmu hij
    have : (lamN j : ℤ) ≤ (lamN i : ℤ) := by rw [hcast, hcast]; linarith
    exact_mod_cast this
  have e1 : wdim mu = (Module.finrank ℚ (Formalism.GradedWeylDivisibility.dualWeyl ℚ (r + 1) (r + 1) lamN) : ℚ) := by
    have hmu' : mu = fun i => (lamN i : ℤ) + c := funext fun i => by rw [hcast]; ring
    calc wdim mu = wdim (fun i => (lamN i : ℤ) + c) := congrArg wdim hmu'
      _ = wdim (fun i => (lamN i : ℤ)) := wdim_shift _ c
      _ = _ := by rw [wdim_nat, h3 ℚ (r + 1) lamN hanti]
  rw [e1, h2 ℚ r lamN hanti]
  push_cast
  set F := (Fintype.piFinset (fun _ : Fin r => Finset.range (lamN 0 + 1))).filter
    (fun nu => ∀ i : Fin r, lamN i.succ ≤ nu i ∧ nu i ≤ lamN i.castSucc) with hF
  have hinj : Set.InjOn (fun (nu : Fin r → ℕ) (i : Fin r) => (nu i : ℤ) + c) F := by
    intro a _ b _ hab
    funext i
    have := congrFun hab i
    simp only at this
    omega
  rw [finsum_eq_sum_of_support_subset (s := F.image (fun (nu : Fin r → ℕ) (i : Fin r) => (nu i : ℤ) + c))]
  · rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun nu hnu => ?_
    rw [hF, Finset.mem_filter] at hnu
    have hnu2 := hnu.2
    have hA : Antitone nu := antitone_of_interlace hanti nu hnu2
    rw [if_pos, wdim_shift, wdim_nat, h3 ℚ r nu hA]
    intro i
    show mu i.succ ≤ (nu i : ℤ) + c ∧ (nu i : ℤ) + c ≤ mu i.castSucc
    have h1 := hnu2 i
    have a1 := hcast i.succ
    have a2 := hcast i.castSucc
    constructor <;> omega
  · intro lam hlam
    rw [Function.mem_support] at hlam
    have hcond : ∀ i : Fin r, mu i.succ ≤ lam i ∧ lam i ≤ mu i.castSucc := by
      by_contra hn
      exact hlam (if_neg hn)
    rw [Finset.coe_image]
    refine ⟨fun i => (lam i - c).toNat, ?_, ?_⟩
    · rw [Finset.mem_coe, hF, Finset.mem_filter, Fintype.mem_piFinset]
      have hl : ∀ i, ((lam i - c).toNat : ℤ) = lam i - c := fun i =>
        Int.toNat_of_nonneg (by linarith [hge i.succ, (hcond i).1])
      refine ⟨fun i => ?_, fun i => ?_⟩
      · rw [Finset.mem_range]
        show (lam i - c).toNat < lamN 0 + 1
        have a0 := hcast 0
        have h0 : mu i.castSucc ≤ mu 0 := hmu (Fin.zero_le _)
        have := hl i
        have := (hcond i).2
        omega
      · show lamN i.succ ≤ (lam i - c).toNat ∧ (lam i - c).toNat ≤ lamN i.castSucc
        have a1 := hcast i.succ
        have a2 := hcast i.castSucc
        have b1 := hl i
        have b2 := hcond i
        constructor <;> omega
    · funext i
      have : ((lam i - c).toNat : ℤ) = lam i - c :=
        Int.toNat_of_nonneg (by linarith [hge i.succ, (hcond i).1])
      simp only [this]
      ring

theorem stWeylAt (D : Formalism.BasicNotions.D7) : StWeylAt := by
  intro n N LL B P
  have h := Formalism.MainNotions.G.Joints.Lit.weyl_dimension_formula_index_sets D n N P.mu (P.dom (Fin.last N))
  rw [h]
  rfl

end Formalism.MainNotions.ColumnSystems.Pf
end
end
