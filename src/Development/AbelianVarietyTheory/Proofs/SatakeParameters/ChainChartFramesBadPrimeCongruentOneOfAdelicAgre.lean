module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlainTorExistsChars
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormsFiniteGL

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChainChartFramesBadPrimeCongruentOneOfAdelicAgre
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChainChartFramesBadPrimeCongruentOneOfAdelicAgre
noncomputable section

namespace GlobalTheory.FrameAway

open NumberField IsDedekindDomain Matrix _root_.Formalism.BasicNotions _root_.Formalism.UG _root_.Formalism.L2.Col GlobalTheory.TwU GlobalTheory.TwU.Model
open scoped TensorProduct

section Core

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}

theorem intAtA_of_prV (P : HeightOneSpectrum (𝓞 E)) (z : E ⊗[F] FiniteAdeleRing (𝓞 F) F)
    (h : ∀ v : HeightOneSpectrum (𝓞 F), IsOver v P → prV (E := E) v z = 0) : IntAtA (F := F) P z :=
  GlobalTheory.T.integralAt_of_component_zero_under_prime P z h

theorem intAt_of_intAtA (P : HeightOneSpectrum (𝓞 E)) (x : E) (h : IntAtA (F := F) P (iA F E x)) : IntAt P x :=
  GlobalTheory.T.integralAt_of_adelic_integralAt P x h

theorem intAtA_of_intAt (P : HeightOneSpectrum (𝓞 E)) (x : E) (h : IntAt P x) : IntAtA (F := F) P (iA F E x) := by
  obtain ⟨r, s, hs, e⟩ := h
  refine ⟨s, hs, ?_⟩
  rw [← map_mul, e]
  exact (Formalism.L2.DIV.toRInt F E r).2

theorem intAtA_neg (P : HeightOneSpectrum (𝓞 E)) {a : E ⊗[F] FiniteAdeleRing (𝓞 F) F} (h : IntAtA (F := F) P a) :
    IntAtA (F := F) P (-a) := by
  have := intAtA_mul (intAtA_int (F := F) (P := P) (-1)) h
  simpa using this

theorem intAtA_pow (P : HeightOneSpectrum (𝓞 E)) {a : E ⊗[F] FiniteAdeleRing (𝓞 F) F} (h : IntAtA (F := F) P a) (m : ℕ) :
    IntAtA (F := F) P (a ^ m) := by
  induction m with
  | zero => simpa using intAtA_int (F := F) (P := P) 1
  | succ m ih => rw [pow_succ]; exact intAtA_mul ih h

theorem frame_core [StarRing E] (Q : HeightOneSpectrum (𝓞 E)) (n : ℕ) (hn : 1 ≤ n)
    (y y₁ : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (G G₁ : GL (Fin N) E)
    (h : CongAt Q n (y⁻¹ * ratA F G)) (h₁ : CongAt Q n (y₁⁻¹ * ratA F G₁))
    (hv : ∀ v : HeightOneSpectrum (𝓞 F), IsOver v Q → bc (prV (E := E) v) y₁ = bc (prV (E := E) v) y) (a b : Fin N) :
    IntAt Q ((((qOf Q : ℕ) : E) ^ n)⁻¹ * (((G⁻¹ * G₁ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) - 1) a b) := by
  have hq : ((qOf Q : ℕ) : E) ≠ 0 := by
    have : qOf Q ≠ 0 := fun h0 => Q.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    exact_mod_cast this
  set qi := iA F E (((qOf Q : ℕ) : E) ^ n)⁻¹ with hqi
  set d := iA F E (((qOf Q : ℕ) : E) ^ n) with hdd
  have hdq : d * qi = 1 := by
    rw [hqi, hdd, ← map_mul, mul_inv_cancel₀ (pow_ne_zero _ hq), map_one]
  have hd : IntAtA (F := F) Q d := by
    have := intAtA_int (F := F) (P := Q) (((qOf Q : ℕ) : 𝓞 E) ^ n)
    simpa [hdd] using this
  set Am : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := ((y⁻¹ * ratA F G : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) - 1 with hAm
  set Bm : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := ((y₁⁻¹ * ratA F G₁ : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) - 1 with hBm
  set Cm : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := ((y⁻¹ * y₁ : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) - 1 with hCm
  set Mm : Matrix (Fin N) (Fin N) E := ((G⁻¹ * G₁ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) - 1 with hMm
  set Mh : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := Mm.map (iA F E) with hMh
  have hMh' : Mh = ((ratA F (G⁻¹ * G₁) : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) - 1 := by
    rw [hMh, hMm, Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
    rfl
  have key : (1 + Am) * (1 + Mh) = (1 + Cm) * (1 + Bm) := by
    rw [hMh', hAm, hBm, hCm, add_sub_cancel, add_sub_cancel, add_sub_cancel, add_sub_cancel, ← Units.val_mul, ← Units.val_mul]
    congr 1
    rw [map_mul, map_inv]
    group
  have e1 : Mh = Cm * (1 + Bm) + Bm - Am - Am * Mh := by
    have e0 : Mh = (1 + Am) * (1 + Mh) - 1 - Am - Am * Mh := by noncomm_ring
    rw [key] at e0
    exact e0.trans (by noncomm_ring)
  have hC : ∀ v : HeightOneSpectrum (𝓞 F), IsOver v Q → ∀ i j, prV (E := E) v (Cm i j) = 0 := by
    intro v hvv i j
    have h1 : bc (prV (E := E) v) (y⁻¹ * y₁) = 1 := by
      rw [map_mul, map_inv, hv v hvv, inv_mul_cancel]
    have h2 := congrArg (fun g : GL (Fin N) (E ⊗[F] v.adicCompletion F) => (g : Matrix (Fin N) (Fin N) (E ⊗[F] v.adicCompletion F)) i j) h1
    simp only [Units.val_one] at h2
    change prV (E := E) v (((y⁻¹ * y₁ : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) i j) = (1 : Matrix (Fin N) (Fin N) _) i j at h2
    rw [hCm, Matrix.sub_apply, map_sub, h2, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hA : ∀ i j, IntAtA (F := F) Q (qi * Am i j) := fun i j => h i j
  have hB : ∀ i j, IntAtA (F := F) Q (qi * Bm i j) := fun i j => h₁ i j
  have step : ∀ m : ℕ, (∀ i j, IntAtA (F := F) Q (d ^ (m + 1) * (qi * Mh i j))) → ∀ i j, IntAtA (F := F) Q (d ^ m * (qi * Mh i j)) := by
    intro m hm i j
    have e2 : d ^ m * (qi * Mh i j) = d ^ m * (qi * (Cm * (1 + Bm)) i j) + d ^ m * (qi * Bm i j) + -(d ^ m * (qi * Am i j)) +
        -(∑ l, (qi * Am i l) * (d ^ (m + 1) * (qi * Mh l j))) := by
      have es : ∑ l, (qi * Am i l) * (d ^ (m + 1) * (qi * Mh l j)) = d ^ m * (qi * ∑ l, Am i l * Mh l j) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        linear_combination (d ^ m * qi * Am i l * Mh l j) * hdq
      rw [es]
      conv_lhs => rw [e1]
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply (M := Am)]
      ring
    rw [e2]
    refine intAtA_add (intAtA_add (intAtA_add ?_ (intAtA_mul (intAtA_pow Q hd m) (hB i j))) (intAtA_neg Q (intAtA_mul (intAtA_pow Q hd m) (hA i j)))) (intAtA_neg Q (intAtA_sum _ _ fun l _ => intAtA_mul (hA i l) (hm l j)))
    refine intAtA_of_prV Q _ fun v hvv => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_mul, map_mul, Matrix.mul_apply, map_sum]
    simp [hC v hvv]
  have desc : ∀ m : ℕ, (∀ i j, IntAtA (F := F) Q (d ^ m * (qi * Mh i j))) → ∀ i j, IntAtA (F := F) Q (qi * Mh i j) := by
    intro m
    induction m with
    | zero => intro hm i j; simpa using hm i j
    | succ m ih => intro hm; exact ih (step m hm)
  obtain ⟨J, hJ⟩ := qth_bound Q Mm
  have hqv : Q.valuation E ((qOf Q : ℕ) : E) ≤ WithZero.exp (-1 : ℤ) := by
    have h0 : ((qOf Q : ℕ) : 𝓞 E) ∈ Q.asIdeal ^ 1 := by rw [pow_one]; exact Ideal.absNorm_mem _
    have := (Q.intValuation_le_pow_iff_mem _ 1).2 h0
    rw [← HeightOneSpectrum.valuation_of_algebraMap (K := E)] at this
    simpa using this
  have hbig : ∀ i j, IntAtA (F := F) Q (d ^ (J + 1) * (qi * Mh i j)) := by
    intro i j
    have e : d ^ (J + 1) * (qi * Mh i j) = iA F E (((qOf Q : ℕ) : E) ^ (n * J) * Mm i j) := by
      rw [hMh, Matrix.map_apply, hdd, hqi, ← map_pow, ← map_mul, ← map_mul]
      congr 1
      rw [pow_succ, mul_assoc, mul_inv_cancel_left₀ (pow_ne_zero _ hq), ← pow_mul]
    rw [e]
    refine intAtA_of_intAt Q _ ((qth_intAt_iff Q _).2 ?_)
    rw [map_mul, map_pow]
    calc Q.valuation E ((qOf Q : ℕ) : E) ^ (n * J) * Q.valuation E (Mm i j) ≤ WithZero.exp (-1 : ℤ) ^ (n * J) * WithZero.exp (J : ℤ) :=
          mul_le_mul' (pow_le_pow_left₀ zero_le hqv _) (hJ i j)
      _ ≤ 1 := by
          rw [← WithZero.exp_nsmul, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp]
          have : (J : ℤ) ≤ (n : ℤ) * J := by exact_mod_cast Nat.le_mul_of_pos_left J hn
          rw [nsmul_eq_mul]
          push_cast
          linarith
  have hfin := desc (J + 1) hbig a b
  show IntAt Q ((((qOf Q : ℕ) : E) ^ n)⁻¹ * Mm a b)
  refine intAt_of_intAtA (F := F) Q _ ?_
  have e3 : iA F E ((((qOf Q : ℕ) : E) ^ n)⁻¹ * Mm a b) = qi * Mh a b := by rw [map_mul, hMh, Matrix.map_apply]
  rw [e3]
  exact hfin

end Core

section Seam

open _root_.Formalism.L2.Ker _root_.Formalism.MainNotions

variable {D : D7} {X : Fields} (s : Seam D X)

theorem qOf_seamP (P : HeightOneSpectrum (𝓞 X.E)) : qOf (seamP s P) = qOf P := by
  have hI : (seamP s P).asIdeal = P.asIdeal.map (RingOfIntegers.mapRingEquiv s.iE) := by
    ext y
    rw [Ideal.mem_map_of_equiv]
    constructor
    · intro hy
      refine ⟨(RingOfIntegers.mapRingEquiv s.iE).symm y, (mem_seamP s P _).1 (by simpa using hy), by simp⟩
    · rintro ⟨x, hx, rfl⟩
      exact (mem_seamP s P x).2 hx
  unfold qOf
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr (Ideal.quotientEquiv _ _ (RingOfIntegers.mapRingEquiv s.iE) hI).symm.toEquiv

theorem intAt_of_seamP (P : HeightOneSpectrum (𝓞 X.E)) (z : X.E) (h : IntAt (seamP s P) (s.iE z)) : IntAt P z := by
  obtain ⟨r, c, hc, e⟩ := h
  set f := RingOfIntegers.mapRingEquiv s.iE
  refine ⟨f.symm r, f.symm c, fun hm => hc ?_, ?_⟩
  · have := (mem_seamP s P (f.symm c)).2 hm
    rwa [show (RingOfIntegers.mapRingEquiv s.iE) (f.symm c) = c from f.apply_symm_apply c] at this
  · apply s.iE.injective
    rw [map_mul]
    have h1 : ∀ w : 𝓞 D.host.E, s.iE (algebraMap (𝓞 X.E) X.E (f.symm w)) = algebraMap (𝓞 D.host.E) D.host.E w := by
      intro w
      have h2 : ∀ x : 𝓞 X.E, s.iE (algebraMap (𝓞 X.E) X.E x) = algebraMap (𝓞 D.host.E) D.host.E (f x) := fun x => rfl
      rw [h2, f.apply_symm_apply]
    rw [h1, h1, e]

end Seam

open _root_.Formalism.BasicNotions _root_.Formalism.MainNotions _root_.Formalism.L2.Ker _root_.Formalism.L2.DIV GlobalTheory.TwV in
theorem frame_away : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
    {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
    (A : AdData t u μ St) (dtU : (letI := D.host.cmStar; Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm) →* D.Dt) (a : 𝓞 D.host.E), AdPins A dtU → AdTie A dtU a →
    ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x₁ : UA D i hi) (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i),
    IsPtAd A a i hi β x p → IsPtAd A a i hi β x₁ p₁ → ∀ P : SB t μ,
    (∀ v : HeightOneSpectrum (𝓞 D.host.F), IsOver v (seamP t.seam P.1) → bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
    ∃ k : Sp t.X.E (D.R.N i) ≃ₗ[t.X.E] Sp t.X.E (D.R.N i), frsF t.sel (t.tup μ) p₁ P = frsF t.sel (t.tup μ) p P * k ∧
      ∀ s l, IntAt P.1 (((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ * (k (Pi.single s (1 : t.X.E)) l - (Pi.single s (1 : t.X.E) : Sp t.X.E (D.R.N i)) l)) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _ _ i hi β x x₁ p p₁ hp hp₁ P hv
  letI := D.host.cmStar
  have hD := (t.idx_ok μ).cst_ok.D_pos P
  set k := (frsF t.sel (t.tup μ) p P)⁻¹ * frsF t.sel (t.tup μ) p₁ P with hk
  refine ⟨k, (mul_inv_cancel_left _ _).symm, fun s l => ?_⟩
  have hf : CongAt (seamP t.seam P.1) ((t.cst μ).D P)
      ((ratA D.host.F (A.crd i hi) * x.1 * ratA D.host.F (A.fb i hi β P))⁻¹ * ratA D.host.F (seamGL t.seam (frsF t.sel (t.tup μ) p P))) :=
    hp.frame P
  have hf₁ : CongAt (seamP t.seam P.1) ((t.cst μ).D P)
      ((ratA D.host.F (A.crd i hi) * x₁.1 * ratA D.host.F (A.fb i hi β P))⁻¹ * ratA D.host.F (seamGL t.seam (frsF t.sel (t.tup μ) p₁ P))) :=
    hp₁.frame P
  have hw : ∀ v : HeightOneSpectrum (𝓞 D.host.F), IsOver v (seamP t.seam P.1) →
      bc (prV (E := D.host.E) v) (ratA D.host.F (A.crd i hi) * x₁.1 * ratA D.host.F (A.fb i hi β P)) =
        bc (prV (E := D.host.E) v) (ratA D.host.F (A.crd i hi) * x.1 * ratA D.host.F (A.fb i hi β P)) := by
    intro v hvv
    have e := hv v hvv
    simp only [map_mul]
    rw [e]
  have hc := frame_core (F := D.host.F) (seamP t.seam P.1) ((t.cst μ).D P) hD _ _ _ _ hf hf₁ hw l s
  rw [← map_inv, ← map_mul, qOf_seamP, ← hk] at hc
  refine intAt_of_seamP t.seam P.1 _ ?_
  convert hc using 1
  have hm := congrFun (seamGL_mulVec t.seam k (Pi.single s 1)) l
  have hs1 : (fun j => t.seam.iE ((Pi.single s (1 : t.X.E) : Sp t.X.E (D.R.N i)) j)) = Pi.single s (1 : D.host.E) := by
    funext j
    rw [Pi.single_apply, Pi.single_apply]
    split_ifs <;> simp
  rw [hs1, Matrix.mulVec_single_one] at hm
  rw [map_mul, map_inv₀, map_pow, map_natCast, map_sub, ← hm, Matrix.sub_apply, Matrix.one_apply, Pi.single_apply]
  by_cases h : l = s
  · subst h; simp [Matrix.col_apply]
  · simp [h, Matrix.col_apply]

end GlobalTheory.FrameAway
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChainChartFramesBadPrimeCongruentOneOfAdelicAgreStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open Formalism.UG (bc prV)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chainChart_frames_badPrime_congruent_one_of_adelic_agree : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
    {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
    (A : AdData t u μ St) (dtU : (letI := D.host.cmStar; Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm) →* D.Dt) (a : 𝓞 D.host.E), AdPins A dtU → AdTie A dtU a →
    ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x₁ : UA D i hi) (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i),
    IsPtAd A a i hi β x p → IsPtAd A a i hi β x₁ p₁ → ∀ P : SB t μ,
    (∀ v : HeightOneSpectrum (𝓞 D.host.F), IsOver v (seamP t.seam P.1) → bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
    ∃ k : Sp t.X.E (D.R.N i) ≃ₗ[t.X.E] Sp t.X.E (D.R.N i), frsF t.sel (t.tup μ) p₁ P = frsF t.sel (t.tup μ) p P * k ∧
      ∀ s l, IntAt P.1 (((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ * (k (Pi.single s (1 : t.X.E)) l - (Pi.single s (1 : t.X.E) : Sp t.X.E (D.R.N i)) l)) := by
  first | exact @GlobalTheory.FrameAway.frame_away | exact GlobalTheory.FrameAway.frame_away | (intros; apply GlobalTheory.FrameAway.frame_away <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspRepCharacterSupportLiftTransTower
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspidalBaseChangeTransTower
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspidalBaseChangeTransTower
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.LiftTrans

open Matrix

section Places

variable {K M N : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Field N] [NumberField N]
  [Algebra K M] [Algebra M N] [Algebra K N] [IsScalarTower K M N]

theorem under_under (w : HeightOneSpectrum (𝓞 N)) :
    (w.under (𝓞 M)).under (𝓞 K) = w.under (𝓞 K) := by
  apply HeightOneSpectrum.ext
  simp only [HeightOneSpectrum.under_asIdeal]
  exact Ideal.under_under w.asIdeal

theorem eq_under_of_continuous {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 N)}
    (i : v.adicCompletion K →+* w.adicCompletion N) (hi : Continuous i)
    (he : ∀ x : K, i (algebraMap K _ x) = algebraMap N _ (algebraMap K N x)) : v = w.under (𝓞 K) := by
  have h1 : v.asIdeal ≤ (w.under (𝓞 K)).asIdeal := by
    intro x hx
    rw [HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, GlobalTheory.DegOneLift.mem_iff_lt_one]
    rw [GlobalTheory.DegOneLift.mem_iff_lt_one] at hx
    have := GlobalTheory.DegOneLift.lt_one_of_continuous i hi hx
    rw [he] at this
    exact this
  exact HeightOneSpectrum.ext (v.isMaximal.eq_of_le (w.under (𝓞 K)).isPrime.ne_top h1)

end Places

end GlobalTheory.LiftTrans


open GlobalTheory.LiftTrans in
theorem GlobalTheory.LiftTrans.isLift_trans : ∀ (K M N : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field M] [NumberField M] [_root_.NumberField.IsTotallyComplex M] [Field N] [NumberField N] [_root_.NumberField.IsTotallyComplex N] [Algebra K M] [Algebra M N] [Algebra K N] [IsScalarTower K M N] (a : ℕ) (π : CuspSub K a) (P : CuspSub M a) (Q : CuspSub N a), IsLift π P → IsLift P Q → IsLift π Q := by
  intro K M N _ _ _ _ _ _ _ _ _ _ _ _ _ a π P Q h1 h2
  refine ⟨?_, ?_, ?_⟩
  · intro w f B hf hB
    obtain ⟨f1, hf1⟩ := GlobalTheory.AboveL.ResDeg.normV_eq_under_pow K M (w.under (𝓞 M))
    obtain ⟨f2, hf2⟩ := GlobalTheory.AboveL.ResDeg.normV_eq_under_pow M N w
    rw [under_under] at hf1
    have hP := h1.sat (w.under (𝓞 M)) f1 B (by rw [under_under]; exact hf1) (by rw [under_under]; exact hB)
    have hQ := h2.sat w f2 _ hf2 hP
    have hff : f = f1 * f2 := by
      have h2le := GlobalTheory.DegOneLift.two_le_normV (w.under (𝓞 K))
      apply Nat.pow_right_injective h2le
      change normV (w.under (𝓞 K)) ^ f = normV (w.under (𝓞 K)) ^ (f1 * f2)
      rw [← hf, pow_mul, ← hf1, hf2]
    rw [Multiset.map_map] at hQ
    convert hQ using 2
    simp [Function.comp, hff, pow_mul]
  · intro τ
    rw [h2.inf τ, h1.inf, RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]
  · intro v w i hi hie σ σ' hσ hσ'
    have hv := eq_under_of_continuous i.toRingHom hi hie
    subst hv
    set u := w.under (𝓞 M) with hu
    haveI : w.asIdeal.LiesOver u.asIdeal := by rw [hu, HeightOneSpectrum.under_asIdeal]; infer_instance
    haveI : u.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := by
      constructor
      rw [hu, HeightOneSpectrum.under_asIdeal, HeightOneSpectrum.under_asIdeal, Ideal.under_under]
    haveI : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := by rw [HeightOneSpectrum.under_asIdeal]; infer_instance
    let φ1 := GroundTheory.Global.adicCompletionMap (w.under (𝓞 K)) u
    let φ2 := GroundTheory.Global.adicCompletionMap u w
    have hcomp : ∀ y, φ2 (φ1 y) = GroundTheory.Global.adicCompletionMap (w.under (𝓞 K)) w y := fun y =>
      congrFun (congrArg DFunLike.coe (GlobalTheory.BCChar.adicCompletionMap_comp_adicCompletionMap (w.under (𝓞 K)) u w)) y
    have hiφ : ∀ y, i y = φ2 (φ1 y) := fun y => by
      rw [hcomp]
      exact congrFun ((HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 K) (K := K) (w.under (𝓞 K))).equalizer hi
        (GroundTheory.Global.continuous_adicCompletionMap _ _)
        (funext fun x => (hie x).trans (GroundTheory.Global.adicCompletionMap_algebraMap _ _ x).symm)) y
    have hb2 : Function.Bijective φ2 := ⟨φ2.injective, fun z => by
      obtain ⟨y, rfl⟩ := i.surjective z
      exact ⟨φ1 y, (hiφ y).symm⟩⟩
    have hb1 : Function.Bijective φ1 := ⟨φ1.injective, fun t => by
      obtain ⟨y, hy⟩ := i.surjective (φ2 t)
      exact ⟨y, hb2.1 (by rw [← hiφ, hy])⟩⟩
    obtain ⟨τ, hτ, -⟩ := GlobalTheory.CuspRep.LocEx.exists_isLocComp GlobalTheory.automorphicFormsFiniteGL M a P u
    obtain ⟨e1, he1⟩ := h1.loc (w.under (𝓞 K)) u (RingEquiv.ofBijective φ1 hb1)
      (GroundTheory.Global.continuous_adicCompletionMap _ _) (fun x => GroundTheory.Global.adicCompletionMap_algebraMap _ _ x) σ τ hσ hτ
    obtain ⟨e2, he2⟩ := h2.loc u w (RingEquiv.ofBijective φ2 hb2)
      (GroundTheory.Global.continuous_adicCompletionMap _ _) (fun x => GroundTheory.Global.adicCompletionMap_algebraMap _ _ x) τ σ' hτ hσ'
    refine ⟨e1.trans e2, fun g x => ?_⟩
    have hg : Matrix.GeneralLinearGroup.map (RingEquiv.ofBijective φ2 hb2).toRingHom
        (Matrix.GeneralLinearGroup.map (RingEquiv.ofBijective φ1 hb1).toRingHom g) =
        Matrix.GeneralLinearGroup.map i.toRingHom g := by
      apply Units.ext
      ext j k
      simp only [Matrix.GeneralLinearGroup.map_apply]
      exact congrArg _ (hiφ _).symm
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, he1, he2, hg]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspidalBaseChangeTransTowerStatement
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_baseChange_trans_tower : ∀ (K M N : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field M] [NumberField M] [_root_.NumberField.IsTotallyComplex M] [Field N] [NumberField N] [_root_.NumberField.IsTotallyComplex N] [Algebra K M] [Algebra M N] [Algebra K N] [IsScalarTower K M N] (a : ℕ) (π : CuspSub K a) (P : CuspSub M a) (Q : CuspSub N a), IsLift π P → IsLift P Q → IsLift π Q := by
  first | (exact @GlobalTheory.LiftTrans.isLift_trans) | (exact GlobalTheory.LiftTrans.isLift_trans) | (intros; apply GlobalTheory.LiftTrans.isLift_trans  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspRepCharacterSupportLiftTransTower
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RoadU

theorem chars_congr {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
    {ξ ξ' : Fin n → (kˣ →* ℂˣ)} (hξ : ∀ j, IsSmoothChar (ξ j)) (hξ' : ∀ j, IsSmoothChar (ξ' j)) (e : ξ = ξ') :
    chars ξ hξ = chars ξ' hξ' := by
  subst e; rfl

theorem charLift_trans : ∀ (K M N : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field M] [NumberField M] [_root_.NumberField.IsTotallyComplex M] [Field N] [NumberField N] [_root_.NumberField.IsTotallyComplex N] [Algebra K M] [Algebra M N] [Algebra K N] [IsScalarTower K M N] (a : ℕ) (π : CuspSub K a) (P : CuspSub M a) (Q : CuspSub N a), CharLift π P → CharLift P Q → CharLift π Q := by
  intro K M N _ _ _ _ _ _ _ _ _ _ _ _ _ a π P Q h1 h2
  refine ⟨GlobalTheory.T.cuspidal_baseChange_trans_tower K M N a π P Q h1.1 h2.1, ?_⟩
  intro v w _ τ T hτ hT ξ hξ hs
  let u : HeightOneSpectrum (𝓞 M) := w.under (𝓞 M)
  haveI hwu : w.asIdeal.LiesOver u.asIdeal := ⟨rfl⟩
  haveI huv : u.asIdeal.LiesOver v.asIdeal := Ideal.LiesOver.tower_bot w.asIdeal u.asIdeal v.asIdeal
  obtain ⟨σ, hσ, -⟩ := GlobalTheory.CuspRep.LocEx.exists_isLocComp GlobalTheory.automorphicFormsFiniteGL M a P u
  have h3 := h1.2 v u τ σ hτ hσ ξ hξ hs
  have h4 := h2.2 u w σ T hσ hT _ _ h3
  have e := GlobalTheory.BCChar.normU_comp_normU v u w
  refine (congrArg (HasSupport T.ρ) (chars_congr _ _ ?_)).mp h4
  funext j
  rw [MonoidHom.comp_assoc, e]

end GlobalTheory.RoadU
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspRepCharacterSupportLiftTransTowerStatement
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspRep_characterSupportLift_trans_tower : ∀ (K M N : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field M] [NumberField M] [_root_.NumberField.IsTotallyComplex M] [Field N] [NumberField N] [_root_.NumberField.IsTotallyComplex N] [Algebra K M] [Algebra M N] [Algebra K N] [IsScalarTower K M N] (a : ℕ) (π : CuspSub K a) (P : CuspSub M a) (Q : CuspSub N a), CharLift π P → CharLift P Q → CharLift π Q := by
  first | (exact @GlobalTheory.RoadU.charLift_trans) | (exact GlobalTheory.RoadU.charLift_trans) | (intros; apply GlobalTheory.RoadU.charLift_trans  <;> assumption)
end
end
