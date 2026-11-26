module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuBesselLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTieOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocJEq
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ColDictValCPf

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuBLGapPf
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Inh

namespace Formalism.L2.SG.Pf.WuBL

theorem gap_lt (R : Ranks) (P : HCParam R)
    (hg : ∀ (j : Fin R.m) (h : j.1 + 1 < R.m), 16 * (R.r : ℚ) ^ 19 ≤ P.b ⟨j.1 + 1, h⟩ - P.b j)
    (a b : Fin (2 * R.rS + R.k + 1)) (hab : a < b) (he : epsSH R a ≠ epsSH R b) :
    16 * (R.r : ℝ) ^ 19 ≤ lamSH R P a - lamSH R P b := by
  have hk := R.m_add_three_le_k
  have hm := R.two_le_m
  have hr : R.r = R.k + R.m - 1 := rfl
  have hdim : 2 * R.rS + R.k + 1 = R.r := dimS_eq R
  have h0 : (0 : ℚ) ≤ 16 * (R.r : ℚ) ^ 19 := by positivity
  have bmono : ∀ n : ℕ, ∀ (j j' : Fin R.m), j'.val = j.val + n + 1 →
      16 * (R.r : ℚ) ^ 19 ≤ P.b j' - P.b j := by
    intro n
    induction n with
    | zero =>
      intro j j' hj
      have h := hg j (by omega)
      have e : (⟨j.1 + 1, by omega⟩ : Fin R.m) = j' := Fin.ext (by simp [hj])
      rw [e] at h
      exact h
    | succ n ih =>
      intro j j' hj
      have h1 := ih j ⟨j.1 + n + 1, by omega⟩ rfl
      have h2 := hg ⟨j.1 + n + 1, by omega⟩ (by first | omega | (simp; omega))
      have e : (⟨j.1 + n + 1 + 1, by omega⟩ : Fin R.m) = j' := Fin.ext (by first | omega | (simp; omega))
      simp only at h2
      rw [e] at h2
      linarith
  have umono : ∀ n : ℕ, ∀ i : Fin R.k, i.val + n = R.k - 1 → P.u ⟨R.k - 1, by omega⟩ ≤ P.u i := by
    intro n
    induction n with
    | zero =>
      intro i hi
      have e : i = ⟨R.k - 1, by omega⟩ := Fin.ext (by simpa using hi)
      rw [e]
    | succ n ih =>
      intro i hi
      have h1 := ih ⟨i.1 + 1, by omega⟩ (by first | omega | (simp; omega))
      have h2 := P.v_gt_u ⟨i.1, by omega⟩
      have h3 := P.u_gt_v ⟨i.1, by omega⟩
      simp only at h2 h3
      linarith
  have hlast := P.u_last_gt (by omega) (by omega)
  unfold epsSH epsS at he
  unfold lamSH lamS
  simp only [Fin.coe_cast] at he ⊢
  have ha : a.val < R.r := by have := a.isLt; omega
  have hb : b.val < R.r := by have := b.isLt; omega
  have hab' : a.val < b.val := hab
  by_cases hak : a.val < R.k - 1 <;> by_cases hbk : b.val < R.k - 1
  · rw [if_pos hak, if_pos hbk] at he
    exact absurd rfl he
  · rw [if_pos hak, if_neg hbk] at he
    have hjb : b.val - (R.k - 1) < R.m := by omega
    have hodd : (b.val - (R.k - 1)) % 2 ≠ 0 := by
      intro h
      exact he (by simp [h])
    rw [dite_eq_left hak, dite_eq_right hbk, dite_eq_left hjb]
    have h1 := bmono (b.val - (R.k - 1) - 1) ⟨0, by omega⟩ ⟨b.val - (R.k - 1), hjb⟩ (by first | omega | (simp; omega))
    have h2 := umono (R.k - 1 - (a.val + 1)) ⟨a.val + 1, by omega⟩ (by first | omega | (simp; omega))
    have h3 := P.v_gt_u ⟨a.val, hak⟩
    simp only at h3
    have hq : 16 * (R.r : ℚ) ^ 19 ≤ P.v ⟨a.val, hak⟩ + P.b ⟨b.val - (R.k - 1), hjb⟩ := by linarith
    have hq' := (Rat.cast_le (K := ℝ)).2 hq
    push_cast at hq'
    linarith
  · omega
  · rw [if_neg hak, if_neg hbk] at he
    have hja : a.val - (R.k - 1) < R.m := by omega
    have hjb : b.val - (R.k - 1) < R.m := by omega
    have hne : a.val - (R.k - 1) ≠ b.val - (R.k - 1) := by
      intro h
      exact he (by simp [h])
    rw [dite_eq_right hak, dite_eq_right hbk, dite_eq_left hja, dite_eq_left hjb]
    have h1 := bmono (b.val - (R.k - 1) - (a.val - (R.k - 1)) - 1) ⟨a.val - (R.k - 1), hja⟩
      ⟨b.val - (R.k - 1), hjb⟩ (by first | omega | (simp; omega))
    have hq' := (Rat.cast_le (K := ℝ)).2 h1
    push_cast at hq'
    linarith

theorem gapAtLeast_of (R : Ranks) (P : HCParam R)
    (hg : ∀ (j : Fin R.m) (h : j.1 + 1 < R.m), 16 * (R.r : ℚ) ^ 19 ≤ P.b ⟨j.1 + 1, h⟩ - P.b j) :
    Formalism.QuantumDeterminants.GapAtLeast (epsSH R) (lamSH R P) (16 * (R.r : ℝ) ^ 19) := by
  intro a b he
  rcases lt_trichotomy a b with hab | rfl | hab
  · exact (gap_lt R P hg a b hab he).trans (le_abs_self _)
  · exact absurd rfl he
  · rw [abs_sub_comm]
    exact (gap_lt R P hg b a hab (Ne.symm he)).trans (le_abs_self _)


set_option maxHeartbeats 800000 in
theorem gapOK_of (R : Ranks) (h1801 : 1801 ≤ R.r) :
    Formalism.FourierDecayAlt.ThreeDimData.GapOK R.k R.rS (16 * (R.r : ℝ) ^ 19) := by
  have hr : R.r = R.k + R.m - 1 := rfl
  have hrs : R.rS = R.m / 2 - 1 := rfl
  have hmk := R.m_add_three_le_k
  have hm2 := R.two_le_m
  have hN : 2 * R.rS + R.k + 1 ≤ 2 * R.r := by omega
  have h16 : 60 ≤ R.r ^ 16 := le_trans (by omega) (Nat.le_self_pow (by norm_num) R.r)
  have hx0 : (0:ℝ) ≤ (R.rS:ℝ) := Nat.cast_nonneg _
  have hk0 : (0:ℝ) ≤ (R.k:ℝ) := Nat.cast_nonneg _
  have hxr : (R.rS:ℝ) ≤ (R.r:ℝ) := by exact_mod_cast (show R.rS ≤ R.r by omega)
  have hkr : (R.k:ℝ) ≤ (R.r:ℝ) := by exact_mod_cast (show R.k ≤ R.r by omega)
  have hρ : (1801:ℝ) ≤ (R.r:ℝ) := by exact_mod_cast h1801
  have hρ0 : (0:ℝ) ≤ (R.r:ℝ) := by linarith
  have hs : Real.sqrt (2 * ((R.rS:ℝ) + 1)) ≤ 2 * (R.r:ℝ) := by
    calc Real.sqrt (2 * ((R.rS:ℝ) + 1)) ≤ Real.sqrt ((2 * (R.r:ℝ)) ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith)
      _ = 2 * (R.r:ℝ) := Real.sqrt_sq (by linarith)
  have hsp : 0 < Real.sqrt (2 * ((R.rS:ℝ) + 1)) := Real.sqrt_pos.mpr (by linarith)
  have p0 : (1:ℝ) ≤ (R.r:ℝ) ^ 2 := by nlinarith
  have p23 : 16 * (R.r:ℝ) ^ 2 ≤ (R.r:ℝ) ^ 3 := by nlinarith
  have p35 : (R.r:ℝ) ^ 3 ≤ (R.r:ℝ) ^ 5 := by nlinarith
  have p13 : (400:ℝ) ≤ (R.r:ℝ) ^ 13 := by
    have h2 : (1801:ℝ) ^ 13 ≤ (R.r:ℝ) ^ 13 := by gcongr
    nlinarith
  have p6 : 0 ≤ (R.r:ℝ) ^ 6 := by positivity
  have hbig : 6400 * (R.r:ℝ) ^ 6 ≤ 16 * (R.r:ℝ) ^ 19 := by nlinarith
  have fin : ∀ E : ℝ, E ≤ 400 * (R.r:ℝ) ^ 5 →
      E ≤ 16 * (R.r:ℝ) ^ 19 / (8 * Real.sqrt (2 * ((R.rS:ℝ) + 1))) := by
    intro E hE
    rw [le_div_iff₀ (by positivity)]
    have h1 := mul_le_mul_of_nonneg_right hE hsp.le
    have h2 : 400 * (R.r:ℝ) ^ 5 * Real.sqrt (2 * ((R.rS:ℝ) + 1)) ≤ 400 * (R.r:ℝ) ^ 5 * (2 * R.r) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    nlinarith
  have hxx := mul_le_mul hxr hxr hx0 hρ0
  have hxk := mul_le_mul hxr hkr hk0 hρ0
  have hG : 4 * ((R.k:ℝ) + R.rS) * ((R.rS:ℝ) + 1) ≤ 16 * (R.r:ℝ) ^ 2 := by
    have := mul_le_mul (show (R.k:ℝ) + R.rS ≤ 2 * R.r by linarith) (show (R.rS:ℝ) + 1 ≤ 2 * R.r by linarith)
      (by linarith) (by linarith)
    nlinarith
  have hG0 : 0 ≤ 4 * ((R.k:ℝ) + R.rS) * ((R.rS:ℝ) + 1) := by positivity
  unfold Formalism.FourierDecayAlt.ThreeDimData.GapOK Formalism.FourierDecayAlt.ThreeDimData.AS Formalism.FourierDecayAlt.ThreeDimData.dN Formalism.FourierDecayAlt.ThreeDimData.aOf Formalism.FourierDecayAlt.ThreeDimData.AG Formalism.FourierDecayAlt.ThreeDimData.Mexp
  refine ⟨by omega, ?_, fin _ ?_, fin _ ?_⟩
  · have h3 : (2 * R.rS + R.k + 1) ^ 3 ≤ (2 * R.r) ^ 3 := Nat.pow_le_pow_left hN 3
    have key : 120 * (2 * R.rS + R.k + 1) ^ 3 ≤ 16 * R.r ^ 19 := by
      calc 120 * (2 * R.rS + R.k + 1) ^ 3 ≤ 120 * (2 * R.r) ^ 3 := Nat.mul_le_mul_left 120 h3
        _ = 960 * R.r ^ 3 := by ring
        _ ≤ 16 * (R.r ^ 3 * R.r ^ 16) := by nlinarith [Nat.zero_le (R.r ^ 3)]
        _ = 16 * R.r ^ 19 := by ring
    exact_mod_cast key
  · push_cast
    have hD : (R.rS:ℝ) * ((R.rS:ℝ) - 1) + 2 * R.rS * ((R.k:ℝ) + 1) + (R.rS:ℝ) ^ 2 ≤ 6 * (R.r:ℝ) ^ 2 := by
      nlinarith
    have hD0 : 0 ≤ (R.rS:ℝ) * ((R.rS:ℝ) - 1) + 2 * R.rS * ((R.k:ℝ) + 1) + (R.rS:ℝ) ^ 2 := by nlinarith
    have hAS := mul_le_mul (show 2 * (R.rS:ℝ) + R.k ≤ 3 * R.r by linarith) hD hD0 (by linarith)
    have hsum : (2 * (R.rS:ℝ) + R.k) * ((R.rS:ℝ) * ((R.rS:ℝ) - 1) + 2 * R.rS * ((R.k:ℝ) + 1) + (R.rS:ℝ) ^ 2) +
        4 * ((R.k:ℝ) + R.rS) * ((R.rS:ℝ) + 1) ≤ 19 * (R.r:ℝ) ^ 3 := by nlinarith
    have hsum0 : 0 ≤ (2 * (R.rS:ℝ) + R.k) * ((R.rS:ℝ) * ((R.rS:ℝ) - 1) + 2 * R.rS * ((R.k:ℝ) + 1) + (R.rS:ℝ) ^ 2) +
        4 * ((R.k:ℝ) + R.rS) * ((R.rS:ℝ) + 1) := by positivity
    have hA : 2 * (2 * ((R.rS:ℝ) ^ 2 + R.rS + 1)) ≤ 12 * (R.r:ℝ) ^ 2 := by nlinarith
    have hprod := mul_le_mul hA hsum hsum0 (by positivity)
    nlinarith
  · push_cast
    have hq := mul_le_mul (show 2 * (R.rS:ℝ) + R.k + 1 ≤ 4 * R.r by linarith)
      (show 2 * (R.rS:ℝ) + R.k + 1 ≤ 4 * R.r by linarith) (by positivity) (by linarith)
    have hq0 : 0 ≤ (2 * (R.rS:ℝ) + R.k + 1) * (2 * (R.rS:ℝ) + R.k + 1) := by positivity
    have hc := mul_le_mul (show (R.rS:ℝ) + 1 ≤ 2 * R.r by linarith) hq hq0 (by linarith)
    linarith [hc, hG, p0, p23, p35]

theorem parameter_gap_of_hypothesis : GapOfHyp := by
  intro D hD τ
  exact ⟨16 * (D.R.r : ℝ) ^ 19, gapAtLeast_of D.R (D.hc τ) (hD.2 τ), gapOK_of D.R hD.1⟩

end Formalism.L2.SG.Pf.WuBL
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.FibreCounting
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
  Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.Pf.FibreCounting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem dcrel_of_heq {Λ₁ Λ₂ : Submodule (𝓞 E) S.V} (h : Λ₁ = Λ₂) {T T' : E} (F : LFlag S r T)
    (P : Submodule (𝓞 E) S.V → LFlag S r T' → Prop) (x : TermDef.Carrier (P Λ₁)) (y : TermDef.Carrier (P Λ₂))
    (he : HEq (TermDef.mk Λ₁ F (P Λ₁) x) (TermDef.mk Λ₂ F (P Λ₂) y)) : TermDef.DCRel Λ₂ F x.1 y.1 := by
  subst h
  have h2 : Quot.mk _ x = Quot.mk _ y := eq_of_heq he
  have h3 := Quot.eqvGen_exact h2
  clear he h2
  induction h3 with
  | rel a b hab => exact hab
  | refl a => apply Formalism.L2.SG.TermDef.dcrel_refl
  | symm a b _ ih => exact Formalism.L2.SG.Pf.dcrel_symm (h := ih)
  | trans a b c _ _ ih1 ih2 => exact Formalism.L2.SG.Pf.dcrel_trans (h := ih1) (h' := ih2)

theorem nlam_isom {Λ : Submodule (𝓞 E) S.V} {T : E} {F : LFlag S r T} {n : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F) :
    n ∈ Formalism.HermitianLatticesTheory.isom S.hT := hn.1.1

theorem nlam_gmap {Λ : Submodule (𝓞 E) S.V} {T : E} {F : LFlag S r T} {n : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F) :
    Formalism.HermitianLatticesTheory.gmap n Λ = Λ := hn.1.2

theorem gmap_inv_of {Λ : Submodule (𝓞 E) S.V} {g : S.V ≃ₗ[E] S.V} (h : Formalism.HermitianLatticesTheory.gmap g Λ = Λ) :
    Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ = Λ := by
  have hinv : ∀ y : S.V, g⁻¹ (g y) = y := fun y => g.symm_apply_apply y
  ext x
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : y ∈ Formalism.HermitianLatticesTheory.gmap g Λ := by rw [h]; exact hy
    simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe] at hy'
    obtain ⟨z, hz, rfl⟩ := hy'
    rw [hinv]
    exact hz
  · intro hx
    refine ⟨g x, ?_, hinv x⟩
    rw [← h]
    exact Submodule.mem_map_of_mem hx

end Gen

section Fib

variable {D : D7} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word}

theorem frame_lf {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (a : Fin (D.R.rS + 1)) :
    frame (lf D F0) a = F0.fvec a := rfl

theorem lin_isom (s : TT Y u u') : s.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := s.rep.2.2.1

theorem lin_gmap (s : TT Y u u') : Formalism.HermitianLatticesTheory.gmap s.lin s.lam' = s.lam := s.rep.2.2.2.1

theorem frame_eq (s : TT Y u u') : s.frame = Formalism.L2.SG.Saturated.mapL s.lin (lin_isom s) (lf D (X.Fu u')) := by
  unfold Formalism.L2.SG.TermOp.GTerm.frame Formalism.L2.SG.TermOp.mapLF
  rw [dite_eq_left (lin_isom s)]
  rfl

theorem frame_apply (s : TT Y u u') (a : Fin (D.R.rS + 1)) : frame s.frame a = s.lin ((X.Fu u').fvec a) := by
  rw [frame_eq]
  show (Formalism.L2.SG.Saturated.mapFlag s.lin (lin_isom s) (lf D (X.Fu u')).fl).fvec a =
    s.lin ((lf D (X.Fu u')).fl.fvec a)
  generalize (lf D (X.Fu u')).fl = F
  refine Fin.lastCases ?_ (fun i => ?_) a
  · simp only [Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_last, Formalism.L2.SG.Saturated.mapFlag]
  · simp only [Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc, Formalism.L2.SG.Saturated.mapFlag]

theorem stabF_of_fix {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) {c : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hc : c ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (hfix : ∀ a, c (F0.fvec a) = F0.fvec a) : c ∈ stabF D F0 := by
  have he : ∀ i, c (F0.e i) = F0.e i := fun i => by
    have h1 := hfix i.castSucc
    simpa only [Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc] using h1
  refine ⟨hc, fun j => ?_, ?_⟩
  · unfold Formalism.MainNotions.S.FlagG.Xa
    rw [Submodule.map_span, Set.image_image]
    simp only [LinearEquiv.coe_coe, he]
  · have h1 := hfix (Fin.last _)
    simpa only [Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_last] using h1

theorem fib_dec {s s' : TT Y u u'} (h : s.toTerm = s'.toTerm) :
    s.lam = s'.lam ∧ ∃ n ∈ NLam s.lam (lf D (X.Fu u)), ∃ ν ∈ NLam s.lam' (lf D (X.Fu u')),
      ∃ c : (VS D).V ≃ₗ[D.host.E] (VS D).V, c ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧
        Formalism.HermitianLatticesTheory.gmap c s'.lam' = s.lam' ∧ (∀ a, c ((X.Fu u').fvec a) = (X.Fu u').fvec a) ∧
        s'.lin = n * s.lin * ν * c := by

  have hmul : ∀ (f g : (VS D).V ≃ₗ[D.host.E] (VS D).V) (x : (VS D).V), (f * g) x = f (g x) :=
    fun _ _ _ => rfl
  have hinv : ∀ (f : (VS D).V ≃ₗ[D.host.E] (VS D).V) (x : (VS D).V), f⁻¹ (f x) = x :=
    fun f x => f.symm_apply_apply x
  have hinv' : ∀ (f : (VS D).V ≃ₗ[D.host.E] (VS D).V) (x : (VS D).V), f (f⁻¹ x) = x :=
    fun f x => f.apply_symm_apply x
  have gmul : ∀ (f g : (VS D).V ≃ₗ[D.host.E] (VS D).V) (L : Submodule (𝓞 D.host.E) (VS D).V),
      Formalism.HermitianLatticesTheory.gmap (f * g) L = Formalism.HermitianLatticesTheory.gmap f (Formalism.HermitianLatticesTheory.gmap g L) := by
    intro f g L
    unfold Formalism.HermitianLatticesTheory.gmap
    rw [← Submodule.map_comp]
    rfl
  have gone : ∀ L : Submodule (𝓞 D.host.E) (VS D).V, Formalism.HermitianLatticesTheory.gmap (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) L = L := by
    intro L
    unfold Formalism.HermitianLatticesTheory.gmap
    exact Submodule.map_id L

  have h' := h
  unfold Formalism.L2.SG.TermOp.GTerm.toTerm at h'
  injection h' with h1 h3
  have hd : TermDef.DCRel s'.lam (lf D (X.Fu u)) s.frame s'.frame :=
    dcrel_of_heq h1 (lf D (X.Fu u)) (fun Λ => TermDef.PD D Λ (lf D (X.Fu u)) u')
      ⟨s.frame, s.rep.2.2.2.2⟩ ⟨s'.frame, s'.rep.2.2.2.2⟩ h3
  obtain ⟨n, hn, m, hm, hfr, -⟩ := hd
  have hnL : n ∈ NLam s.lam (lf D (X.Fu u)) := by rw [h1]; exact hn

  have hm' : m ∈ NLam (Formalism.HermitianLatticesTheory.gmap s.lin s.lam')
      (Formalism.L2.SG.Saturated.mapL s.lin (lin_isom s) (lf D (X.Fu u'))) := by
    rw [lin_gmap, h1, ← frame_eq]
    exact hm
  have hν : s.lin⁻¹ * m * s.lin ∈ NLam s.lam' (lf D (X.Fu u')) :=
    (Formalism.L2.SG.Pf.mem_NLam_map _ _ _ _ _).1 hm'
  have hback : Formalism.HermitianLatticesTheory.gmap s.lin⁻¹ s.lam = s.lam' := by
    rw [← lin_gmap s, ← gmul, inv_mul_cancel, gone]
  generalize hνdef : s.lin⁻¹ * m * s.lin = ν at hν
  refine ⟨h1, n, hnL, ν, hν, (n * s.lin * ν)⁻¹ * s'.lin,
    ?_, ?_, ?_, (mul_inv_cancel_left _ _).symm⟩
  · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mul_mem _
      (Subgroup.mul_mem _ (nlam_isom hn) (lin_isom s)) (nlam_isom hν))) (lin_isom s')
  · rw [gmul, lin_gmap s', ← h1, mul_inv_rev (n * s.lin) ν, mul_inv_rev n s.lin, gmul, gmul, gmap_inv_of (nlam_gmap hnL),
      hback, gmap_inv_of (nlam_gmap hν)]
  · intro a
    have e1 := hfr a
    rw [frame_apply, frame_apply] at e1
    rw [hmul, e1]
    have e2 : n (m (s.lin ((X.Fu u').fvec a))) = (n * s.lin * ν) ((X.Fu u').fvec a) := by
      rw [← hνdef]
      simp only [hmul, hinv']
    rw [e2, hinv]

theorem lam'_eq {s s' : TT Y u u'} (h : s.toTerm = s'.toTerm) : s.lam' = s'.lam' := by
  obtain ⟨-, n, -, ν, -, c, hc, hgc, hfix, -⟩ := fib_dec h
  have hstab : c ∈ stabF D (X.Fu u') := stabF_of_fix (X.Fu u') hc hfix
  have hone : (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) ∈ stabF D (X.Fu u') :=
    stabF_of_fix (X.Fu u') (Subgroup.one_mem _) (fun _ => rfl)
  have hg1 : Formalism.HermitianLatticesTheory.gmap (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) s.lam' = s.lam' := by
    unfold Formalism.HermitianLatticesTheory.gmap
    exact Submodule.map_id _
  have hR := Y.rowsOK u'
  obtain ⟨Λ0, -, huniq⟩ := hR.2 s.lam' (hR.1 _ s.mem')
  have e1 := huniq s.lam' ⟨s.mem', 1, hone, hg1⟩
  have e2 := huniq s'.lam' ⟨s'.mem', c, hstab, hgc⟩
  exact e1.trans e2.symm

theorem gterm_eq {s s' : TT Y u u'} (hl : s.lam = s'.lam) (hl' : s.lam' = s'.lam')
    (h : ∃ n ∈ NLam s.lam (lf D (X.Fu u)), ∃ n' ∈ NLam s.lam' (lf D (X.Fu u')), s'.lin = n * s.lin * n') : s = s' := by
  obtain ⟨n, hn, n', hn', hq⟩ := h
  rcases s with ⟨l, hm, l', hm', c⟩
  rcases s' with ⟨k, km, k', km', c'⟩
  simp only at hl hl'
  subst hl
  subst hl'
  have hc : c = c' :=
    (Quot.out_eq c).symm.trans ((Quot.sound ⟨n, hn, n', hn', hq⟩).trans (Quot.out_eq c'))
  subst hc
  rfl

end Fib

end Formalism.L2.SG.Pf.FibreCounting
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BuiltPf
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.Built

open Formalism.L2.SG.Pf.Carrier

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

def chiStd (x : ℝ) : ℝ := Real.smoothTransition (2 * x - 1)

theorem isCut0_chiStd : Formalism.FourierDecayAlt.C6.IsCut0 chiStd := by
  unfold Formalism.FourierDecayAlt.C6.IsCut0
  refine ⟨?_, ⟨1 / 2, by norm_num, fun x hx => ?_⟩, fun x hx => ?_⟩
  · show ContDiff ℝ _ (Real.smoothTransition ∘ fun x : ℝ => 2 * x - 1)
    exact Real.smoothTransition.contDiff.comp (by fun_prop)
  · exact Real.smoothTransition.zero_of_nonpos (by linarith)
  · exact Real.smoothTransition.one_of_one_le (by linarith)

section tower

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def towerOf (B : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (h1 : B.μW Set.univ = 1) (h2 : B.μW' Set.univ = 1)
    (h3 : B.μN = Formalism.FourierDecayAlt.D.muN k r) : Formalism.FourierDecayAlt.D.LevTower k r Wp Wq :=
  (Formalism.FourierDecayAlt.P.exists_level_tower k r Wp Wq B h1 h2 h3).choose

theorem towerOf_base (B : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (h1 : B.μW Set.univ = 1) (h2 : B.μW' Set.univ = 1)
    (h3 : B.μN = Formalism.FourierDecayAlt.D.muN k r) : (towerOf B h1 h2 h3).base = B :=
  (Formalism.FourierDecayAlt.P.exists_level_tower k r Wp Wq B h1 h2 h3).choose_spec.1

theorem towerOf_norm (B : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (h1 : B.μW Set.univ = 1) (h2 : B.μW' Set.univ = 1)
    (h3 : B.μN = Formalism.FourierDecayAlt.D.muN k r) : Formalism.FourierDecayAlt.D.TowerNormalised (towerOf B h1 h2 h3) :=
  (Formalism.FourierDecayAlt.P.exists_level_tower k r Wp Wq B h1 h2 h3).choose_spec.2

end tower

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}

abbrev par (I : CarrierIn X u u') (v : Fin I.nf) : Formalism.FourierDecayAlt.M.Par := Formalism.FourierDecayAlt.D.parOf (sOf I) v

def sgOf {nf : ℕ} (G : Formalism.FourierDecayAlt.Sz.Glob (InfinitePlace D.host.E)) (pl : Fin nf ≃ InfinitePlace D.host.E)
    (T T' : ℝ) (de de' : ℕ → ℝ) (l : ℕ) (v : Fin nf) : ℂ :=
  Formalism.FourierDecayAlt.M.sgn ⟨G.k, G.r, T, T', (G.place (pl v)).u de, (G.place (pl v)).u de'⟩ l

theorem sg_of (I : CarrierIn X u u')
    (h : I.sg = sgOf I.G I.pl ((D.mem u).A.T : ℝ) ((D.mem u').A.T : ℝ) I.de I.de' (I.l + 1)) :
    ∀ v, I.sg v = Formalism.FourierDecayAlt.M.sgn (par I v) ((sOf I).l + 1) := by
  intro v
  rw [h]
  rfl

def ParNums (I : CarrierIn X u u') : Prop :=
  ∀ v, (∀ i ∈ Finset.Icc 1 (par I v).k, ∃ n : ℤ, (par I v).u i - (par I v).u 1 = n) ∧
    (∀ i ∈ Finset.Icc 1 (par I v).k, ∃ n : ℤ, (par I v).u' i - (par I v).u 1 = n) ∧
    ∀ i ∈ Finset.Icc 1 ((par I v).k - 1), (par I v).lo i ≤ (par I v).hi i

def Types (I : CarrierIn X u u') : Prop :=
  ∀ v, Formalism.FourierDecayAlt.Q.IsType I.G.k I.G.r (I.T v).base.z (I.T v).base.π (par I v).u ∧
    Formalism.FourierDecayAlt.Q.IsType I.G.k I.G.r (I.T v).base.z' (I.T v).base.π' (par I v).u'

def Frames (I : CarrierIn X u u') : Prop := ∀ v, Formalism.FourierDecayAlt.D.IsBaseFrame (I.T v).base (I.ν' v) (I.m₀ v)

def CoefCC (I : CarrierIn X u u') : Prop := ∀ v (m : ℕ), Formalism.FourierDecayAlt.B.InCC I.A₀ m (I.fc v)

def CoefCap (I : CarrierIn X u u') : Prop :=
  ∀ v (Y : ℝ), ∀ g ∈ Formalism.FourierDecayAlt.B.GV I.G.k I.G.r,
    Formalism.FourierDecayAlt.Q.CV I.G.k I.G.r (Y : ℂ) (I.fc v) g = (((sOf I).P v Y : ℝ) : ℂ) • I.fc v g

theorem isPlace_of (I : CarrierIn X u u') (hN : ParNums I) (hty : Types I) (v : Fin I.nf) :
    Formalism.FourierDecayAlt.Q.IsPlace (par I v) (I.T v).base.z (I.T v).base.z' (I.T v).base.π (I.T v).base.π' := by
  unfold Formalism.FourierDecayAlt.Q.IsPlace
  obtain ⟨h1, h2, h3⟩ := hN v
  obtain ⟨t1, t2⟩ := hty v
  obtain ⟨e1, e2⟩ := I.hT v
  have p1 := (I.T v).base.T_pos
  have p2 := (I.T v).base.T'_pos
  rw [e1] at p1
  rw [e2] at p2
  exact ⟨⟨(I.T v).base.k_pos, p1, p2, h1, h2, h3⟩, (I.T v).base.z_mem, (I.T v).base.z'_mem, e1, e2, t1, t2⟩

end Formalism.L2.SG.Pf.Built
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuBLReproPf
noncomputable section

open MeasureTheory Formalism.QuantumDeterminants Formalism.MainNotions.S
open scoped ENNReal InnerProductSpace
open Matrix

namespace Formalism.L2.SG.Pf.WuBL

variable {k r : ℕ}

def conjH (a b a' b' : Formalism.FourierDecayAlt.B.Mat k r) (hab : a' * a = 1) (hbb : b * b' = 1) (hab' : a * a' = 1)
    (hbb' : b' * b = 1) : Mt k r ≃ₜ Mt k r where
  toFun g := Matrix.of.symm (a * Matrix.of g * b)
  invFun g := Matrix.of.symm (a' * Matrix.of g * b')
  left_inv g := by
    show Matrix.of.symm (a' * (a * Matrix.of g * b) * b') = g
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hab, Matrix.one_mul, Matrix.mul_assoc, hbb, Matrix.mul_one]; rfl
  right_inv g := by
    show Matrix.of.symm (a * (a' * Matrix.of g * b') * b) = g
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hab', Matrix.one_mul, Matrix.mul_assoc, hbb', Matrix.mul_one]; rfl
  continuous_toFun := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.of_symm_apply]
    fun_prop
  continuous_invFun := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.of_symm_apply]
    fun_prop

theorem meas_rmul (a : Formalism.FourierDecayAlt.B.Mat k r) : Measurable (Formalism.FourierDecayAlt.B.rmulF a : Mt k r → Mt k r) := by
  apply Continuous.measurable
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Formalism.FourierDecayAlt.B.rmulF, Matrix.mul_apply, Matrix.of_apply]
  fun_prop

private theorem hpk_sq_lemma {k r : ℕ} : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  by_cases hm : r ≤ i.val ∧ i.val ≤ r + k
  · rw [Finset.sum_eq_single i]
    · simp only [Hpk]
      split_ifs <;> (try simp only [Fin.ext_iff, ne_eq, Fin.val_mk, and_true, true_and, not_true_eq_false, not_false_eq_true] at *) <;>
        first | omega | (norm_num; done) | (exfalso; omega)
    · intro l _ hl
      have h0 : Hpk k r i l = 0 := by
        simp only [Hpk]
        split_ifs <;> (try simp only [Fin.ext_iff, ne_eq, Fin.val_mk, and_true, true_and, not_true_eq_false, not_false_eq_true] at *) <;>
        first | omega | (norm_num; done) | (exfalso; omega)
      rw [h0, zero_mul]
    · simp
  · have hlt : 2 * r + k - i.val < 2 * r + k + 1 := by omega
    rw [Finset.sum_eq_single ⟨2 * r + k - i.val, hlt⟩]
    · simp only [Hpk]
      split_ifs <;> (try simp only [Fin.ext_iff, ne_eq, Fin.val_mk, and_true, true_and, not_true_eq_false, not_false_eq_true] at *) <;>
        first | omega | (norm_num; done) | (exfalso; omega)
    · intro l _ hl
      have h0 : Hpk k r i l = 0 := by
        simp only [Hpk]
        split_ifs <;> (try simp only [Fin.ext_iff, ne_eq, Fin.val_mk, and_true, true_and, not_true_eq_false, not_false_eq_true] at *) <;>
        first | omega | (norm_num; done) | (exfalso; omega)
      rw [h0, zero_mul]
    · simp

theorem reproduction_translation : ReproTr := by
  intro k r μG hμ H _ _ σ hσ hiso Vp _ _ W w y hy hrep x hx
  have hmulU : ∀ a ∈ UH (Hpk k r), ∀ b ∈ UH (Hpk k r), a * b ∈ UH (Hpk k r) := by
    intro a ha b hb
    have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
    have hb' : bᴴ * Hpk k r * b = Hpk k r := hb
    show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r
    rw [Matrix.conjTranspose_mul]
    calc bᴴ * aᴴ * Hpk k r * (a * b) = bᴴ * (aᴴ * Hpk k r * a) * b := by
          simp only [Matrix.mul_assoc]
      _ = Hpk k r := by rw [ha', hb']
  obtain ⟨yi, hyi⟩ : ∃ yi : Formalism.FourierDecayAlt.B.Mat k r, yi = Hpk k r * yᴴ * Hpk k r := ⟨_, rfl⟩
  have hy' : yᴴ * Hpk k r * y = Hpk k r := hy
  have hyiy : yi * y = 1 := by
    rw [hyi, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc yᴴ, hy', hpk_sq_lemma]
  have hyyi : y * yi = 1 := mul_eq_one_comm.1 hyiy
  have hyiU : yi ∈ UH (Hpk k r) := by
    show yiᴴ * Hpk k r * yi = Hpk k r
    calc yiᴴ * Hpk k r * yi = yiᴴ * (yᴴ * Hpk k r * y) * yi := by rw [hy']
      _ = (y * yi)ᴴ * Hpk k r * (y * yi) := by
          rw [Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = Hpk k r := by rw [hyyi, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have hcU : ∀ g ∈ UH (Hpk k r), yi * g * y ∈ UH (Hpk k r) := fun g hg =>
    hmulU _ (hmulU _ hyiU _ hg) _ hy
  have hinner : ∀ g ∈ UH (Hpk k r), ∀ u v : H, ⟪σ g u, σ g v⟫_ℂ = ⟪u, v⟫_ℂ := by
    intro g hg u v
    let L : H →ₗᵢ[ℂ] H := ⟨(σ g : H →ₗ[ℂ] H), fun z => hiso g hg z⟩
    exact L.inner_map_map u v
  have hinnerc : ∀ g ∈ UH (Hpk k r), ⟪σ y w, σ g (σ y w)⟫_ℂ = ⟪w, σ (yi * g * y) w⟫_ℂ := by
    intro g hg
    have e1 : g * y = y * (yi * g * y) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hyyi, Matrix.one_mul]
    have h1 : σ g (σ y w) = σ y (σ (yi * g * y) w) := by
      rw [← ContinuousLinearMap.comp_apply, ← hσ.2 g hg y hy, e1, hσ.2 y hy _ (hcU g hg),
        ContinuousLinearMap.comp_apply]
    rw [h1, hinner y hy]
  have hmL : Measurable (lmulM (k := k) (r := r) yi) := by
    apply Continuous.measurable
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [lmulM, Matrix.mul_apply, Matrix.of_apply]
    fun_prop
  obtain ⟨Φ, hΦdef⟩ : ∃ Φ : Mt k r ≃ₜ Mt k r, Φ = conjH yi y y yi hyyi hyyi hyiy hyiy := ⟨_, rfl⟩
  have hΦg : ∀ g : Mt k r, Matrix.of (Φ g) = yi * Matrix.of g * y := by
    intro g
    rw [hΦdef] <;> rfl
  have hΦ : MeasurePreserving Φ μG μG := by
    rw [hΦdef]
    exact (⟨meas_rmul y, hμ.right y hy⟩ : MeasurePreserving (Formalism.FourierDecayAlt.B.rmulF y) μG μG).comp
      ⟨hmL, hμ.left yi hyiU⟩
  have hae : ∀ᵐ z ∂μG, Matrix.of z ∈ UH (Hpk k r) := by
    have h0 : μG (UH (Hpk k r))ᶜ = 0 := hμ.conc
    filter_upwards [compl_mem_ae_iff.2 h0] with z hz
    by_contra hc
    exact hz hc
  have hfdeg : fdegH μG σ (σ y w) = fdegH μG σ w := by
    unfold fdegH
    rw [hiso y hy w]
    congr 1
    have hint : (fun z : Mt k r => ‖⟪σ y w, σ (Matrix.of z) (σ y w)⟫_ℂ‖ ^ 2) =ᵐ[μG]
        (fun z => ‖⟪w, σ (Matrix.of (Φ z)) w⟫_ℂ‖ ^ 2) := by
      filter_upwards [hae] with z hz
      rw [hinnerc _ hz, hΦg]
    rw [integral_congr_ae hint]
    exact hΦ.integral_comp Φ.measurableEmbedding (fun h => ‖⟪w, σ (Matrix.of h) w⟫_ℂ‖ ^ 2)
  have heF : ∀ g : Mt k r, Matrix.of g ∈ UH (Hpk k r) →
      eFun μG σ (σ y w) (Matrix.of g) = eFun μG σ w (Matrix.of (Φ g)) := by
    intro g hg
    unfold eFun
    rw [hfdeg, hinnerc _ hg, hΦg]
  have e2 : ∀ g : Mt k r, x * Matrix.of g * y = x * y * Matrix.of (Φ g) := by
    intro g
    rw [hΦg]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc y yi, hyyi, Matrix.one_mul]
  have hpt : (fun g : Mt k r => eFun μG σ (σ y w) (Matrix.of g) • W (x * Matrix.of g * y)) =ᵐ[μG]
      (fun g => eFun μG σ w (Matrix.of (Φ g)) • W (x * y * Matrix.of (Φ g))) := by
    filter_upwards [hae] with g hg
    rw [heF g hg, e2 g]
  obtain ⟨hI, hR⟩ := hrep (x * y) (hmulU _ hx _ hy)
  refine ⟨?_, ?_⟩
  · have h2 : Integrable (fun g => eFun μG σ w (Matrix.of (Φ g)) • W (x * y * Matrix.of (Φ g))) μG :=
      (hΦ.integrable_comp_emb Φ.measurableEmbedding).2 hI
    exact h2.congr hpt.symm
  · unfold rconv at hR ⊢
    calc ∫ g, eFun μG σ (σ y w) (Matrix.of g) • W (x * Matrix.of g * y) ∂μG
        = ∫ g, eFun μG σ w (Matrix.of (Φ g)) • W (x * y * Matrix.of (Φ g)) ∂μG := integral_congr_ae hpt
      _ = ∫ h, eFun μG σ w (Matrix.of h) • W (x * y * Matrix.of h) ∂μG :=
          hΦ.integral_comp Φ.measurableEmbedding (fun h => eFun μG σ w (Matrix.of h) • W (x * y * Matrix.of h))
      _ = W (x * y) := hR

end Formalism.L2.SG.Pf.WuBL
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ColDictPf
noncomputable section

open scoped Classical InnerProductSpace TensorProduct ComplexOrder
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.ColDict

namespace Formalism.L2.SG.Pf.ColDictPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

abbrev unitaryGroupFiniteAdeles (D : D7) : Subgroup (GL (Fin (D.R.N 0)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :=
  Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)

abbrev unitaryGroupRational (D : D7) : Subgroup (GL (Fin (D.R.N 0)) D.host.E) :=
  Formalism.UG.UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _))

abbrev bcA (D : D7) :
    GL (Fin (D.R.N 0)) D.host.E →* GL (Fin (D.R.N 0)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
  Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))

abbrev G0 (D : D7) : D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ :=
  Formalism.L2.Forms.gramC (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Formalism.L2.Forms.embT D)

instance instGroupUP0 (D : D7) : Group (unitaryGroupFiniteAdeles D) := Subgroup.toGroup _

set_option synthInstance.maxHeartbeats 200000

structure TrFacts {D : D7} (X : HidaSetting D) {u : D.what₂.Word} {F : Formalism.L2.Forms.Forms0 D u}
    (Tr : Transport X u F) : Prop where
  tot : ∀ h : Hfin X u, ∃ y : unitaryGroupFiniteAdeles D, RepF X Tr.wt Tr.ιA (h : X.B.I.Gf) y
  onto : ∀ y : unitaryGroupFiniteAdeles D, ∃ h : Hfin X u, RepF X Tr.wt Tr.ιA (h : X.B.I.Gf) y
  uniq : ∀ (h : X.B.I.Gf) (y y' : unitaryGroupFiniteAdeles D), RepF X Tr.wt Tr.ιA h y → RepF X Tr.wt Tr.ιA h y' → y = y'
  inj : ∀ (h h' : Hfin X u) (y : unitaryGroupFiniteAdeles D), RepF X Tr.wt Tr.ιA (h : X.B.I.Gf) y →
    RepF X Tr.wt Tr.ιA (h' : X.B.I.Gf) y → h = h'
  ratF : ∀ γ : Gam X u, ∃ γ' ∈ unitaryGroupRational D, ∃ y : unitaryGroupFiniteAdeles D, (y : GL _ _) = bcA D γ' ∧
      RepF X Tr.wt Tr.ιA (iotaF X u γ : X.B.I.Gf) y
  ratB : ∀ γ' ∈ unitaryGroupRational D, ∃ γ : Gam X u, (∃ y : unitaryGroupFiniteAdeles D, (y : GL _ _) = bcA D γ' ∧
      RepF X Tr.wt Tr.ιA (iotaF X u γ : X.B.I.Gf) y) ∧
      ∀ τ, sTil X Tr.wt (iotaI X u γ : X.B.I.Ginf) τ =
        Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) (γ' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ
  infOnto : ∀ g : D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ, (∀ τ, (g τ)ᴴ * G0 D τ * g τ = G0 D τ) →
    ∃ s ∈ Hinf X u, ∀ τ, sTil X Tr.wt s τ * g τ = 1

section RepAlg

variable {D : D7} (X : HidaSetting D) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
  (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)


end RepAlg

section Phi

variable {D : D7} {X : HidaSetting D} {u : D.what₂.Word} {F : Formalism.L2.Forms.Forms0 D u} {Tr : Transport X u F}
  (G : TrFacts X Tr)

end Phi

section Sharp

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter)

theorem piU_inner (s : Hinf X u) (a b : X.Vpi u) :
    ⟪X.piU u (s : X.B.I.Ginf) a, X.piU u (s : X.B.I.Ginf) b⟫_ℂ = ⟪a, b⟫_ℂ := (X.piU_rep u).2.2.1 _ (hinf_le_sinf X u _ s.2) a b

theorem piU_adj (s : Hinf X u) (a b : X.Vpi u) :
    ⟪X.piU u (s : X.B.I.Ginf) a, b⟫_ℂ = ⟪a, X.piU u ((s⁻¹ : Hinf X u) : X.B.I.Ginf) b⟫_ℂ := by
  have hs := hinf_le_sinf X u _ s.2
  have hs' := hinf_le_sinf X u _ (s⁻¹ : Hinf X u).2
  have hm := (X.piU_rep u).2.1 _ hs _ hs'
  have e : X.piU u (s : X.B.I.Ginf) (X.piU u ((s⁻¹ : Hinf X u) : X.B.I.Ginf) b) = b := by
    have h1 : (s : X.B.I.Ginf) * ((s⁻¹ : Hinf X u) : X.B.I.Ginf) = 1 := by simp
    rw [← ContinuousLinearMap.mul_apply, ← hm, h1, (X.piU_rep u).1, ContinuousLinearMap.one_apply]
  conv_lhs => rw [← e]
  exact (X.piU_rep u).2.2.1 _ hs _ _

theorem norm_psiK (κ : Ku X u hK) : ‖((psiK X u hK κ : ℂˣ) : ℂ)‖ = 1 := by
  show ‖X.chi2 ((X.xu u)⁻¹ * ((κ : Hfin X u) : X.B.I.Gf) * X.xu u)‖ = 1
  exact hK.2.2.2.2 _ κ.2

theorem rieszVector_rat (T : Cu X u hK) (γ : Gam X u) (h : Hfin X u) (κ : Ku X u hK) :
    shP X u T.1 (iotaF X u γ * h * (κ : Hfin X u)) =
      starRingEnd ℂ ((psiK X u hK κ : ℂˣ) : ℂ) • X.piU u (iotaI X u γ : X.B.I.Ginf) (shP X u T.1 h) := by
  obtain ⟨hT1, hT2⟩ := T.2
  have hsh : ∀ (g : Hfin X u) (ξ : X.Vpi u), ⟪shP X u T.1 g, ξ⟫_ℂ = T.1 ξ (1, g) := by
    intro g ξ
    simp [shP, InnerProductSpace.toDual_symm_apply]
  apply ext_inner_right ℂ
  intro ξ
  obtain ⟨hf1, hf2⟩ := hT1 ξ
  rw [hsh, inner_smul_left, Complex.conj_conj, piU_adj X u (iotaI X u γ), hsh]
  have e1 : ((1 : Hinf X u), iotaF X u γ * h * (κ : Hfin X u)) =
      ((1 : Hinf X u), iotaF X u γ * h) * (1, (κ : Hfin X u)) := by simp
  have e2 : ((1 : Hinf X u), iotaF X u γ * h) = (iotaI X u γ, iotaF X u γ) * ((iotaI X u γ)⁻¹, h) := by simp
  rw [e1, hf2, e2, hf1]
  rw [show T.1 (X.piU u (((iotaI X u γ)⁻¹ : Hinf X u) : X.B.I.Ginf) ξ) (1, h) =
      T.1 ξ ((1, h) * ((iotaI X u γ)⁻¹, 1)) from hT2 _ ξ _]
  simp

theorem rieszVector_rightTranslate (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) (δ h : Hfin X u) :
    shP X u (rtr X δ T) h = shP X u T (h * δ) := by
  unfold shP
  congr 1
  ext ξ
  simp [rtr]

theorem reps_equiv {ι ι' : Type} (s : ι → Hfin X u) (s' : ι' → Hfin X u) (K : Subgroup (Hfin X u))
    (hs : ∀ h, ∃! i, ∃ (γ : Gam X u) (κ : K), h = iotaF X u γ * s i * (κ : Hfin X u))
    (hs' : ∀ h, ∃! i, ∃ (γ : Gam X u) (κ : K), h = iotaF X u γ * s' i * (κ : Hfin X u)) :
    ∃ e : ι ≃ ι', ∀ i, ∃ (γ : Gam X u) (κ : K), s i = iotaF X u γ * s' (e i) * (κ : Hfin X u) := by
  classical
  have inv_rel : ∀ (a b : Hfin X u) (γ : Gam X u) (κ : K), a = iotaF X u γ * b * (κ : Hfin X u) →
      b = iotaF X u γ⁻¹ * a * ((κ⁻¹ : K) : Hfin X u) := by
    intro a b γ κ h
    subst h
    simp [mul_assoc]
  let f : ι → ι' := fun i => (hs' (s i)).exists.choose
  let g : ι' → ι := fun i' => (hs (s' i')).exists.choose
  have hf : ∀ i, ∃ (γ : Gam X u) (κ : K), s i = iotaF X u γ * s' (f i) * (κ : Hfin X u) :=
    fun i => (hs' (s i)).exists.choose_spec
  have hg : ∀ i', ∃ (γ : Gam X u) (κ : K), s' i' = iotaF X u γ * s (g i') * (κ : Hfin X u) :=
    fun i' => (hs (s' i')).exists.choose_spec
  refine ⟨⟨f, g, fun i => ?_, fun i' => ?_⟩, hf⟩
  · obtain ⟨γ, κ, h⟩ := hf i
    exact (hs (s' (f i))).unique (hg (f i)) ⟨γ⁻¹, κ⁻¹, inv_rel _ _ _ _ h⟩
  · obtain ⟨γ, κ, h⟩ := hg i'
    exact (hs' (s (g i'))).unique (hf (g i')) ⟨γ⁻¹, κ⁻¹, inv_rel _ _ _ _ h⟩

theorem sum_reps {ι ι' : Type} [Fintype ι] [Fintype ι'] (s : ι → Hfin X u) (s' : ι' → Hfin X u)
    (K : Subgroup (Hfin X u))
    (hs : ∀ h, ∃! i, ∃ (γ : Gam X u) (κ : K), h = iotaF X u γ * s i * (κ : Hfin X u))
    (hs' : ∀ h, ∃! i, ∃ (γ : Gam X u) (κ : K), h = iotaF X u γ * s' i * (κ : Hfin X u))
    (Q : Hfin X u → ℂ) (hQ : ∀ (γ : Gam X u) (h : Hfin X u) (κ : K), Q (iotaF X u γ * h * (κ : Hfin X u)) = Q h) :
    ∑ i, Q (s i) = ∑ i', Q (s' i') := by
  obtain ⟨e, he⟩ := reps_equiv X u s s' K hs hs'
  calc ∑ i, Q (s i) = ∑ i, Q (s' (e i)) := Finset.sum_congr rfl fun i _ => by
          obtain ⟨γ, κ, h⟩ := he i
          rw [h, hQ]
    _ = ∑ i', Q (s' i') := Equiv.sum_comp e (fun i' => Q (s' i'))

theorem inner_shP_rat (T T' : Cu X u hK) (γ : Gam X u) (h : Hfin X u) (κ : Ku X u hK) :
    ⟪shP X u T'.1 (iotaF X u γ * h * (κ : Hfin X u)), shP X u T.1 (iotaF X u γ * h * (κ : Hfin X u))⟫_ℂ =
      ⟪shP X u T'.1 h, shP X u T.1 h⟫_ℂ := by
  rw [rieszVector_rat X u hK T γ h κ, rieszVector_rat X u hK T' γ h κ, inner_smul_left, inner_smul_right,
    piU_inner X u (iotaI X u γ), Complex.conj_conj, ← mul_assoc, Complex.mul_conj,
    Complex.normSq_eq_norm_sq, norm_psiK X u hK κ]
  simp

end Sharp

section Adelic

variable {D : D7} {X : HidaSetting D} {u : D.what₂.Word} {F : Formalism.L2.Forms.Forms0 D u} {Tr : Transport X u F}
  (G : TrFacts X Tr) {hK : X.LevelSubgroupCharacter} (hL : LevelMatch X Tr hK)

end Adelic

section Adelic2

variable {D : D7} {X : HidaSetting D} {u : D.what₂.Word} {F : Formalism.L2.Forms.Forms0 D u} {Tr : Transport X u F}
  (G : TrFacts X Tr) {hK : X.LevelSubgroupCharacter} (hL : LevelMatch X Tr hK)

end Adelic2

section Onto

variable {D : D7} {X : HidaSetting D} {u : D.what₂.Word} {F : Formalism.L2.Forms.Forms0 D u} {Tr : Transport X u F}
  (G : TrFacts X Tr)

theorem vpi_nontrivial (X : HidaSetting D) (u : D.what₂.Word) : Nontrivial (X.Vpi u) := by
  have hloc : ∀ v, ∃ x : X.Vloc u v, x ≠ 0 := fun v => by
    have := (X.piLoc_type u v).1
    exact exists_ne 0
  choose x hx using hloc
  refine ⟨⟨X.tensU u x, 0, fun h => ?_⟩⟩
  have h1 := X.tensU_inner u x x
  rw [h, inner_zero_left] at h1
  exact (Finset.prod_ne_zero_iff.2 (fun v _ => inner_self_ne_zero.2 (hx v))) h1.symm

end Onto

section Bij

variable {D : D7} {X : HidaSetting D} {u : D.what₂.Word} {F : Formalism.L2.Forms.Forms0 D u} {Tr : Transport X u F}
  (G : TrFacts X Tr) {hK : X.LevelSubgroupCharacter} (hL : LevelMatch X Tr hK)

end Bij

section Isom

variable {D : D7} {X : HidaSetting D} {u : D.what₂.Word} {F : Formalism.L2.Forms.Forms0 D u} {Tr : Transport X u F}
  (G : TrFacts X Tr) {hK : X.LevelSubgroupCharacter} (hL : LevelMatch X Tr hK)

end Isom

section Assembly

variable {D : D7} {X : HidaSetting D} {u : D.what₂.Word} {F : Formalism.L2.Forms.Forms0 D u} {hK : X.LevelSubgroupCharacter}

end Assembly

end Formalism.L2.SG.Pf.ColDictPf

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.Pf.ColDictPf

end Formalism.L2.SG.Pf
end
end
