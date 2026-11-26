module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsParallelWeightInvertibleSection

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinRatMemLatOOfPerO
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.RatLatPer

open GlobalTheory.LatVac

theorem finRat_mem_latO_of_perO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → (ΛS : Set (Fin S.rank → D.host.E)) = latFr S hS N → (ΛT : Set (Fin T.rank → D.host.E)) = latFr T hT N' → ∀ x ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N', GlobalTheory.VacUnique.finRat S T ((LinearMap.toMatrix' (x)).reindex (finCongr hT.symm) (finCongr hS.symm)) ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
  intro D ψ θ S T a b hS hT δ sc hP N N' ΛS ΛT hΛS hΛT h1 h2 x hx
  subst hS hT
  have e1 : N = ΛS := (SetLike.coe_injective h1).symm
  have e2 : N' = ΛT := (SetLike.coe_injective h2).symm
  subst e1 e2
  have hr : (LinearMap.toMatrix' x).reindex (finCongr (rfl : T.rank = T.rank)) (finCongr (rfl : S.rank = S.rank)) =
      LinearMap.toMatrix' x := by
    ext i j; rfl
  rw [hr, GlobalTheory.LatVacSign.finRat_eq]
  refine GlobalTheory.LatVac.finTens_mem_latO (one_mem_intAf _) ?_
  rw [GlobalTheory.AdForm.RatLat.mem_latRat_iff_perO N' hΛS, Matrix.toLin'_toMatrix', GlobalTheory.AdForm.RatLat.AA_eq hP.cc]
  exact hx

end GlobalTheory.AdForm.RatLatPer

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualCOf
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HalfBInt

variable {D : D7}

theorem selfDualC_of (V : HSp D) (hV : V.gram = 1) (N : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (h : Formalism.L2.Col.IsSdLat N) : IsSelfDualC V N := by
  refine ⟨h.1, fun y => ?_⟩
  have h2 : Formalism.HermitianLatticesTheory.dual (Formalism.L2.Col.hStd D.host.E V.rank) N = N := h.2
  conv_lhs => rw [← h2]
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply, Submodule.mem_one]
  refine forall_congr' fun x => imp_congr_right fun _ => ?_
  have e : Formalism.L2.Col.hStd D.host.E V.rank x y = ∑ i, ∑ j, star (x i) * V.gram i j * y j := by
    rw [hV]
    simp [Formalism.L2.Col.hStd, Matrix.one_apply]
  rw [e]

theorem noConj {e : AE D} {SS : Finset (Formalism.L2.DIV.Pl D.host.E)} (hE : IsIdemSum e SS) :
    ∀ P ∈ SS, Formalism.L2.Col.conjPrime₂ P ∉ SS := by
  obtain ⟨⟨es, hes, he⟩, hc⟩ := hE
  intro P hP hP'
  have hv : Formalism.IndefR.Fin.belowPl P = Formalism.IndefR.Fin.belowPl (Formalism.L2.Col.conjPrime₂ P) :=
    HeightOneSpectrum.ext (congrArg HeightOneSpectrum.asIdeal (GlobalTheory.GridPlaces.under_conjP P)).symm
  have h := Formalism.IndefR.Fin.LevelGroupLemmas.idemSum_below_inj hes he hc hP hP' hv
  exact GlobalTheory.ModulusNorm.conjPl_ne_of_isIdemAt (hes P hP) ((GlobalTheory.PlaceDict.conjP_eq_conjPl D P).symm.trans h.symm)

end GlobalTheory.HalfBInt


open GlobalTheory.HalfBInt in
theorem GlobalTheory.HalfBInt.trace_int : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (c : ℕ), 0 < c → Odd c → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → (ΛS : Set (Fin S.rank → D.host.E)) = latFr S hS N → (ΛT : Set (Fin T.rank → D.host.E)) = latFr T hT N' → ∀ y ∈ halfBO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, ∃ k : ℤ, (k : ℚ) = Algebra.trace ℚ D.host.E (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2 * GlobalTheory.LatVac.hRat S T ((LinearMap.toMatrix' (y)).reindex (finCongr hT.symm) (finCongr hS.symm)) ((LinearMap.toMatrix' (y)).reindex (finCongr hT.symm) (finCongr hS.symm))) := by
  intro D ψ θ S T a b hS hT δ sc hP e SS hE N N' c hc _ _ ΛS ΛT dS dT eS eT y hy
  subst hS hT
  obtain rfl : ΛS = N := SetLike.coe_injective eS
  obtain rfl : ΛT = N' := SetLike.coe_injective eT
  have hnc := noConj hE
  have hyT : y ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) ΛS (twist₂ ΛT c (expS SS)) := by
    rw [← Formalism.L2.Ker.twist_homomorphism _ _ _ _ ΛS ΛT c _ dS.1.fg hc]
    exact hy
  have hsdT := (GlobalTheory.ThetaMove.TwistSd.isSdLat_twO_expS _ _ ΛT c SS hnc (GlobalTheory.StdMove.isSdLat_of T hP.gT ΛT dT) hc).1
  have dT' : IsSelfDualC T (twist₂ ΛT c (expS SS)) := selfDualC_of T hP.gT _ hsdT
  have hrat := GlobalTheory.AdForm.RatLatPer.finRat_mem_latO_of_perO D ψ θ S T _ _ rfl rfl δ sc hP ΛS (twist₂ ΛT c (expS SS)) ΛS (twist₂ ΛT c (expS SS)) dS dT' rfl rfl y hyT
  have hneg : GlobalTheory.VacUnique.finRat S T (-((LinearMap.toMatrix' y).reindex (finCongr (rfl : T.rank = T.rank).symm) (finCongr (rfl : S.rank = S.rank).symm))) ∈
      latO S T ((ΛS : Set (Fin S.rank → D.host.E))) ((twist₂ ΛT c (expS SS) : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
    rw [map_neg]
    exact neg_mem hrat
  have h0 : IsLatVac (heisO ψ S T) (latO S T ((ΛS : Set (Fin S.rank → D.host.E))) ((twist₂ ΛT c (expS SS) : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) : Set (Fin T.rank → D.host.E)) (fun _ => True)) (0 : WO S T → ℂ) :=
    ⟨fun _ _ => by funext w; simp [heisO], fun _ _ _ _ _ => by funext w; simp [heisO]⟩
  obtain ⟨k, hk, -⟩ := GlobalTheory.LatVacSign.heisO_finRat_sign ψ S T ΛS (twist₂ ΛT c (expS SS)) hP.std dS dT' 0 h0 _ hneg
  exact ⟨k, hk⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPrimeToDvdAway
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.HalfTmul

theorem exists_prime_to_dvd_away {R : Type} [CommRing R] [IsDedekindDomain R] (SS : Finset (HeightOneSpectrum R))
    (m : R) (hm : m ≠ 0) : ∃ t : R, t ≠ 0 ∧ (∀ Q ∈ SS, t ∉ Q.asIdeal) ∧
      ∀ Q : HeightOneSpectrum R, Q ∉ SS → ∃ u : R, u ∉ Q.asIdeal ∧ ∃ w : R, u * t = m * w := by
  classical
  have hI : Ideal.span {m} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hm
  have hfac : ∀ Q : HeightOneSpectrum R, ∃ n : ℕ, ∃ J : Ideal R, ¬ Q.asIdeal ∣ J ∧ Ideal.span {m} = Q.asIdeal ^ n * J :=
    fun Q => WfDvdMonoid.max_power_factor hI Q.prime.irreducible
  choose n J hJ using hfac
  have hT := Ideal.finite_factors hI
  obtain ⟨t0, ht0⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := SS ∪ hT.toFinset) (fun Q => Q.asIdeal)
    (fun Q => if Q ∈ SS then 1 else n Q) (fun Q _ => Q.prime) (fun Q _ Q' _ h e => h (HeightOneSpectrum.ext e))
    (fun Q => if (Q : HeightOneSpectrum R) ∈ SS then 1 else 0)
  have hone : ∀ Q : HeightOneSpectrum R, (1 : R) ∉ Q.asIdeal := fun Q h1 =>
    Q.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  have hSS : ∀ Q ∈ SS, t0 ∉ Q.asIdeal := by
    intro Q hQ hmem
    have h := ht0 Q (Finset.mem_union_left _ hQ)
    simp only [if_pos hQ, pow_one] at h
    exact hone Q (by simpa using Q.asIdeal.sub_mem hmem h)
  have hgood : ∀ Q : HeightOneSpectrum R, Q ∉ SS → ∃ u : R, u ∉ Q.asIdeal ∧ ∃ w : R, u * t0 = m * w := by
    intro Q hQ
    by_cases hQT : Q.asIdeal ∣ Ideal.span {m}
    · have h := ht0 Q (Finset.mem_union_right _ (hT.mem_toFinset.2 hQT))
      simp only [if_neg hQ, sub_zero] at h
      obtain ⟨hnd, hEq⟩ := hJ Q
      rw [Ideal.dvd_iff_le] at hnd
      obtain ⟨u, huJ, huQ⟩ := SetLike.not_le_iff_exists.1 hnd
      refine ⟨u, huQ, ?_⟩
      have hmem : t0 * u ∈ Ideal.span {m} := by
        rw [hEq]; exact Ideal.mul_mem_mul h huJ
      obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.1 hmem
      exact ⟨w, by rw [mul_comm u, hw]⟩
    · refine ⟨m, ?_, t0, rfl⟩
      intro hmem
      exact hQT (Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hmem))
  by_cases h0 : t0 = 0
  · refine ⟨m, hm, ?_, fun Q _ => ⟨1, hone Q, 1, by ring⟩⟩
    intro Q hQ
    exact absurd (h0 ▸ Q.asIdeal.zero_mem) (hSS Q hQ)
  · exact ⟨t0, h0, hSS, hgood⟩

theorem tmul_mem_of {E : Type} [Field E] [NumberField E] [StarRing E] {W : Type} [AddCommGroup W] [Module E W]
    [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W] (M : Submodule (𝓞 E) W) (SS : Finset (HeightOneSpectrum (𝓞 E)))
    (c : ℕ) (hc : 0 < c) (y : W) (hy : y ∈ twist₂ M c (expS SS)) (t : 𝓞 E)
    (ht : ∀ Q : HeightOneSpectrum (𝓞 E), Q ∉ SS → ∃ u : 𝓞 E, u ∉ Q.asIdeal ∧ ∃ w : 𝓞 E, u * t = (c : 𝓞 E) ^ 2 * w) :
    ((t : E) * (c : E)⁻¹) • y ∈ M := by
  have hcE : (c : E) ≠ 0 := by exact_mod_cast hc.ne'
  have hcast : ∀ (r : 𝓞 E) (z : W), (r : E) • z = r • z := fun r z => IsScalarTower.algebraMap_smul E r z
  have hcy : (c : E) • y ∈ M := by
    have h := (GlobalTheory.CommonReps.mem_twO_zero M c _).1 (GlobalTheory.CommonReps.natsmul_mem_twO M c _ _ (fun Q => by
      rcases expS_cases SS Q with h | h | h <;> rw [h] <;> norm_num) hy)
    rwa [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul E] at h
  apply Formalism.L2.Ker.mem_of_forall_locP M
  intro Q
  by_cases hQ : Q ∈ SS
  · have h1 := (Formalism.L2.Ker.mem_twO M c _ y).1 hy Q
    simp only [expS, if_pos hQ, zpow_one] at h1
    obtain ⟨s, hs, hsy⟩ := h1
    refine ⟨s, hs, ?_⟩
    have e : s • (((t : E) * (c : E)⁻¹) • y) = t • (s • ((c : E)⁻¹ • y)) := by
      rw [← hcast s, ← hcast t, ← hcast s]
      simp only [smul_smul]
      congr 1; ring
    rw [e]; exact M.smul_mem t hsy
  · obtain ⟨u, hu, w, huw⟩ := ht Q hQ
    refine ⟨u, hu, ?_⟩
    have huwE : (u : E) * (t : E) = (c : E) ^ 2 * (w : E) := by
      have := congrArg (fun r : 𝓞 E => (r : E)) huw
      simpa using this
    have e : u • (((t : E) * (c : E)⁻¹) • y) = w • ((c : E) • y) := by
      rw [← hcast u, ← hcast w]
      simp only [smul_smul]
      congr 1
      field_simp
      linear_combination huwE
    rw [e]; exact M.smul_mem w hcy

theorem exists_tmul_mem_perO : ∀ (D : D7) (a b : ℕ) (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (c : ℕ), 0 < c → ∀ y ∈ halfBO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, ∃ t : 𝓞 D.host.E, t ≠ 0 ∧ (∀ Q ∈ SS, t ∉ Q.asIdeal) ∧ ((t : D.host.E) * (c : D.host.E)⁻¹) • y ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' := by
  intro D a b N N' SS c hc y hy
  obtain ⟨t, ht0, hSS, hgood⟩ := exists_prime_to_dvd_away SS ((c : 𝓞 D.host.E) ^ 2)
    (pow_ne_zero _ (by exact_mod_cast hc.ne'))
  exact ⟨t, ht0, hSS, tmul_mem_of _ SS c hc y hy t hgood⟩

end GlobalTheory.HalfTmul
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CharSymplOHConjHalfRest
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ConjHalfCocycle

variable {D : D7} {S T : HSp D}

theorem comm4 {R : Type} [CommRing R] (c a h H : R) : c * (a * h * H) = c * a * H * h := by ring

theorem split_half {E R : Type} [Field E] [CharZero E] [CommRing R] (f : E →+* R) (x k : R) :
    x * k = x * (k * f ((2 : ℕ) : E)⁻¹) + x * (k * f ((2 : ℕ) : E)⁻¹) := by
  have h : f ((2 : ℕ) : E)⁻¹ * (1 + 1) = 1 := by
    rw [← map_one f, ← map_add (f := _), ← map_mul]
    congr 1
    norm_num
  linear_combination (-(x * k)) * h

theorem half_add {F R : Type} [Field F] [CharZero F] [CommRing R] (g : F →+* R) (t : R) :
    g (1 / 2) * (t + t) = t := by
  have h : g (1 / 2) * (1 + 1) = 1 := by
    rw [← map_one g, ← map_add (f := _), ← map_mul]
    congr 1
    norm_num
  linear_combination t * h

theorem hO_smul_right (a : AE D) (x y : WO S T) : hO S T x (a • y) = cA D a * hO S T x y := by
  have h := GlobalTheory.LatVacSign.hO_smul_smul 1 a x y
  rwa [one_smul, one_mul] at h

theorem hO_nsmul_right (n : ℕ) (x y : WO S T) : hO S T x (n • y) = (n : AE D) * hO S T x y := by
  unfold hO
  simp only [Matrix.smul_apply, nsmul_eq_mul, map_mul, map_natCast, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hO_nsmul_left (n : ℕ) (x y : WO S T) : hO S T (n • x) y = (n : AE D) * hO S T x y := by
  unfold hO
  simp only [Matrix.smul_apply, nsmul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => ?_
  ring


set_option maxHeartbeats 1000000 in
theorem char_symplOH_conjHalf_rest : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → (∀ Q ∈ SS, (2 : 𝓞 D.host.E) ∉ Q.asIdeal) → ∀ (c : ℕ), 0 < c → ∀ (Y Z : WO S T), c • Y ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) → Z ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) → e • Y = c • (e • Z) → ψ (symplOH S T (cA D e • Y) ((1 - cA D e) • Y)) = 1 := by
  intro D ψ S T ΛS ΛT hψ hS hT e SS he h2 c hc Y Z hY hZ heq
  have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have hec : e * cA D e = 0 := he.2
  have hcc : cA D (cA D e) = e := GlobalTheory.LatVac.cA_cA e
  have hP : ∀ PP ∈ SS, ((2 : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := by
    intro PP hPP
    rw [Nat.cast_ofNat]
    exact h2 PP hPP
  have hint : finPart D (e * incA D ((2 : ℕ) : D.host.E)⁻¹) ∈ intAE D :=
    GlobalTheory.PlaceDatum.finPart_mem_of_toEAf (GlobalTheory.DatumFourier.idem_div_int he two_ne_zero hP)
  have hZ' := GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ hint Z hZ
  have hcA2 : cA D (incA D ((2 : ℕ) : D.host.E)⁻¹) = incA D ((2 : ℕ) : D.host.E)⁻¹ := by
    change incA D (star ((2 : ℕ) : D.host.E)⁻¹) = _
    rw [star_inv₀, star_natCast]
  have k1 : hO S T (cA D e • Y) ((1 - cA D e) • Y) = (c : AE D) * cA D e * hO S T Y Z := by
    have a1 := GlobalTheory.LatVacSign.hO_smul_smul (cA D e) (1 - cA D e) Y Y
    have a2 := hO_smul_right e Y Y
    rw [heq, hO_nsmul_right, hO_smul_right] at a2
    rw [a1, map_sub, map_one, hcc]
    have : cA D e * (1 - e) = cA D e := by
      rw [mul_sub, mul_one, mul_comm, hec, sub_zero]
    rw [this, mul_assoc, ← a2]
  have k2 : hO S T (c • Y) ((e * incA D ((2 : ℕ) : D.host.E)⁻¹) • Z) =
      (c : AE D) * cA D e * hO S T Y Z * incA D ((2 : ℕ) : D.host.E)⁻¹ := by
    rw [hO_nsmul_left, hO_smul_right, map_mul, hcA2]
    exact comm4 _ _ _ _
  rw [symplOH, symplO, k1, split_half (incA D) (incA D D.host.xi0) ((c : AE D) * cA D e * hO S T Y Z), map_add (f := _),
    half_add (algebraMap D.host.F (AF D.host.F)), ← k2]
  exact GlobalTheory.LatVac.char_sympl_eq_one hψ hS hT hY hZ'

end GlobalTheory.ConjHalfCocycle

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CmulMemPerOOfMemHalfBO
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfBCMul

theorem cmul_mem_perO_of_mem_halfBO : ∀ (D : D7) (a b : ℕ) (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (c : ℕ), 0 < c → ∀ y ∈ halfBO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, (c : D.host.E) • y ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' := by
  intro D a b N N' SS c hc y hy
  have h1 := GlobalTheory.CommonReps.natsmul_mem_twO _ c (expS SS) (fun _ => 0) (fun Q => by
    unfold expS; split_ifs <;> omega) hy
  rw [GlobalTheory.CommonReps.mem_twO_zero] at h1
  have e : ((c : 𝓞 D.host.E) • y) = (c : D.host.E) • y := by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  rwa [e] at h1

end GlobalTheory.HalfBCMul
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorConjugateHalfVacuumEqSemichara
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ConjHalfHeis

theorem mem_localization_of_mem_halfBO {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}
    (SS : Finset (HeightOneSpectrum (𝓞 E))) (M : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b)) (c : ℕ)
    (y : Formalism.L2.Col.HomE E a b) (hy : y ∈ halfBO SS M c) (Q : HeightOneSpectrum (𝓞 E))
    (hQ : ¬ (Q ∈ SS ∨ Formalism.L2.Col.conjPrime₂ Q ∈ SS)) : y ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M := by
  have h1 := (Formalism.L2.Ker.mem_twO M c _ y).1 hy Q
  have h0 : expS SS Q = 0 := by
    unfold expS
    rw [if_neg (fun h => hQ (Or.inl h)), if_neg (fun h => hQ (Or.inr h))]
  rw [h0, zpow_zero, inv_one, one_smul] at h1
  exact h1


set_option maxHeartbeats 400000 in
theorem off_part_mem (D : D7) (S T : HSp D) (Λ : AddSubgroup (WO S T))
    (hstab : ∀ w : AE D, finPart D w ∈ intAE D → ∀ u ∈ Λ, w • u ∈ Λ)
    (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)) (he : IsIdemSum e SS) (c : ℕ) (hc : 0 < c) (d : 𝓞 D.host.E) (hd0 : d ≠ 0)
    (hdP : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), (c : 𝓞 D.host.E) ∈ Q.asIdeal → d ∈ Q.asIdeal →
      Q ∈ SS ∨ Formalism.L2.Col.conjPrime₂ Q ∈ SS)
    (Y : WO S T) (hcY : incA D (c : D.host.E) • Y ∈ Λ) (hdY : incA D (d : D.host.E) • Y ∈ Λ) :
    (1 - e - cA D e) • Y ∈ Λ := by
  obtain ⟨a₁, a₂, ha₁, ha₂, hsum⟩ := GlobalTheory.OffIdemTwo.off_two D e SS he c hc d hd0 hdP
  have h : (1 - e - cA D e) • Y = a₁ • (incA D (c : D.host.E) • Y) + a₂ • (incA D (d : D.host.E) • Y) := by
    ext i j
    simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
    rw [hsum]; ring
  rw [h]
  exact add_mem (hstab _ ha₁ _ hcY) (hstab _ ha₂ _ hdY)


open GlobalTheory.LatVac in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem heisO_conjHalf_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (c : ℕ), 0 < c → Odd c → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → LaFacts (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → (ΛS : Set (Fin S.rank → D.host.E)) = latFr S hS N → (ΛT : Set (Fin T.rank → D.host.E)) = latFr T hT N' → ∀ f₀, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (latFr S hS N) (latFr T hT N') f₀ → ∀ y' ∈ halfBO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, heisO ψ S T (((LinearMap.toMatrix' (y')).reindex (finCongr hT.symm) (finCongr hS.symm)).map fun r => cA D e * incA D r) f₀ = alV D.host.d sc (embH (tauE D) δ y') • heisO ψ S T (GlobalTheory.VacUnique.finRat S T ((LinearMap.toMatrix' (y')).reindex (finCongr hT.symm) (finCongr hS.symm))) f₀ := by
  intro D ψ θ S T a b hS hT δ sc hP e SS he N N' c hc hcP h2qd hLa ΛS ΛT hSd hTd hΛS hΛT f₀ hf₀ y' hy'
  set M : Matrix (Fin T.rank) (Fin S.rank) D.host.E :=
    (LinearMap.toMatrix' y').reindex (finCongr hT.symm) (finCongr hS.symm) with hM
  set Y := GlobalTheory.VacUnique.finRat S T M with hY
  set Λ := latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True with hΛ
  have hvac : IsLatVac (heisO ψ S T) Λ f₀ := by
    have h := hf₀.2.lat
    rw [hΛ, hΛS, hΛT]; exact h
  have hstab : ∀ w : AE D, finPart D w ∈ intAE D → ∀ u ∈ Λ, w • u ∈ Λ :=
    fun w hw u hu => GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ w hw u hu
  have hsmM : ∀ (r : D.host.E) (X : Matrix (Fin T.rank) (Fin S.rank) D.host.E),
      GlobalTheory.VacUnique.finRat S T (r • X) = incA D r • GlobalTheory.VacUnique.finRat S T X := by
    intro r X
    ext i j
    change (pairA D.host.F 0 1) ⊗ₜ[D.host.F] (r * X i j) = incA D r * ((pairA D.host.F 0 1) ⊗ₜ[D.host.F] X i j)
    rw [show incA D r = (1 : AF D.host.F) ⊗ₜ[D.host.F] r from rfl, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  have hsm : ∀ (r : D.host.E) (x : Formalism.L2.Col.HomE D.host.E a b),
      GlobalTheory.VacUnique.finRat S T ((LinearMap.toMatrix' (r • x)).reindex (finCongr hT.symm) (finCongr hS.symm)) =
        incA D r • GlobalTheory.VacUnique.finRat S T ((LinearMap.toMatrix' x).reindex (finCongr hT.symm) (finCongr hS.symm)) := by
    intro r x
    ext i j
    change (pairA D.host.F 0 1) ⊗ₜ[D.host.F] (LinearMap.toMatrix' (r • x) _ _) =
      incA D r * ((pairA D.host.F 0 1) ⊗ₜ[D.host.F] (LinearMap.toMatrix' x _ _))
    rw [LinearMap.toMatrix'_apply, LinearMap.toMatrix'_apply, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul,
      show incA D r = (1 : AF D.host.F) ⊗ₜ[D.host.F] r from rfl, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  have hsmY : ∀ r : D.host.E, GlobalTheory.VacUnique.finRat S T
      ((LinearMap.toMatrix' (r • y')).reindex (finCongr hT.symm) (finCongr hS.symm)) = incA D r • Y := fun r => by
    rw [hsm]
  have hrat := fun x hx => GlobalTheory.AdForm.RatLatPer.finRat_mem_latO_of_perO D ψ θ S T a b hS hT δ sc hP N N' ΛS ΛT hSd hTd hΛS hΛT x hx
  have hc0 : (c : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  have hnat : ∀ (n : ℕ) (u : WO S T), n • u = incA D (n : D.host.E) • u := by
    intro n u; rw [map_natCast, Nat.cast_smul_eq_nsmul]

  have ha : c • Y ∈ Λ := by
    rw [hnat, ← hsmY]; exact hrat _ (GlobalTheory.HalfBCMul.cmul_mem_perO_of_mem_halfBO D a b N N' SS c hc y' hy')

  obtain ⟨t, ht0, htP, htm⟩ := GlobalTheory.HalfTmul.exists_tmul_mem_perO D a b N N' SS c hc y' hy'
  have heI : finPart D (e * incA D ((t : D.host.E))⁻¹) ∈ intAE D := GlobalTheory.IdemSumInt.finPart_idemSum_mul_inv_mem D e SS he t htP
  set Z := (e * incA D ((t : D.host.E))⁻¹) • GlobalTheory.VacUnique.finRat S T
    ((LinearMap.toMatrix' (((t : D.host.E) * (c : D.host.E)⁻¹) • y')).reindex (finCongr hT.symm) (finCongr hS.symm)) with hZ
  have hZm : Z ∈ Λ := hstab _ heI _ (hrat _ htm)
  have he2 : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have ht0' : (t : D.host.E) ≠ 0 := by
    intro h; exact ht0 (by exact_mod_cast h)
  have hb : e • Y = c • (e • Z) := by
    have h1 : (c : D.host.E) * ((t : D.host.E)⁻¹ * ((t : D.host.E) * (c : D.host.E)⁻¹)) = 1 := by
      field_simp
    have h2 : incA D (c : D.host.E) * (e * (e * incA D (t : D.host.E)⁻¹) * incA D ((t : D.host.E) * (c : D.host.E)⁻¹)) = e := by
      calc _ = (e * e) * incA D ((c : D.host.E) * ((t : D.host.E)⁻¹ * ((t : D.host.E) * (c : D.host.E)⁻¹))) := by
              simp only [map_mul]; ring
        _ = e := by rw [h1, map_one, mul_one, he2]
    rw [hZ, hsmY]
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul]
    rw [← map_natCast (incA D) c]
    calc e * Y i j = (incA D (c : D.host.E) * (e * (e * incA D (t : D.host.E)⁻¹) *
          incA D ((t : D.host.E) * (c : D.host.E)⁻¹))) * Y i j := by rw [h2]
      _ = _ := by ring

  have hR0 : (1 - e - cA D e) • Y ∈ Λ := by
    obtain ⟨d, hd0, hdm, hdP⟩ := GlobalTheory.OffDen.exists_den_avoid D.host.E a b (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N')
      (fun Q => Q ∈ SS ∨ Formalism.L2.Col.conjPrime₂ Q ∈ SS) c hc y' (GlobalTheory.HalfBCMul.cmul_mem_perO_of_mem_halfBO D a b N N' SS c hc y' hy') (mem_localization_of_mem_halfBO SS _ c y' hy')
    have hdY : incA D (d : D.host.E) • Y ∈ Λ := by
      rw [← hsmY]; exact hrat _ hdm
    exact off_part_mem D S T Λ hstab e SS he c hc d hd0 hdP Y (hnat c Y ▸ ha) hdY
  have heint : finPart D e ∈ intAE D := by
    have h := GlobalTheory.IdemSumInt.finPart_idemSum_mul_inv_mem D e SS he 1 (fun Q _ h => Q.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h))
    simpa using h
  set R := (1 - cA D e) • Y with hRdef
  have hR : R ∈ Λ := by
    have h : R = c • (e • Z) + (1 - e - cA D e) • Y := by
      rw [hRdef, ← hb, ← add_smul]; congr 1; ring
    rw [h]; exact add_mem (nsmul_mem (hstab _ heint _ hZm) c) hR0
  have h2 : ∀ Q ∈ SS, (2 : 𝓞 D.host.E) ∉ Q.asIdeal := by
    intro Q hQ h; apply h2qd Q hQ
    obtain ⟨t, ht⟩ := D.host.toHostRaw.two_dvd_condN
    have e2 : ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) = 2 * ((t : ℕ) : 𝓞 D.host.E) := by
      rw [show D.host.QS * D.host.q * D.host.d = 2 * t from ht]; push_cast; ring
    rw [e2]; exact Q.asIdeal.mul_mem_right _ h
  have hcoc : ψ (symplOH S T (cA D e • Y) R) = 1 :=
    GlobalTheory.ConjHalfCocycle.char_symplOH_conjHalf_rest D ψ S T ΛS ΛT hP.std hSd hTd e SS he h2 c hc Y Z ha hZm hb

  have hbil : ∀ (x y : WO S T) (k : ℕ), symplOH S T (k • x) (k • y) = (k * k) • symplOH S T x y := by
    intro x y k
    have h1 : symplO S T (k • x) (k • y) = (k * k) • symplO S T x y := by
      rw [← symplHom_apply, map_nsmul, map_nsmul, AddMonoidHom.nsmul_apply, symplHom_apply, smul_smul]
    rw [symplOH, symplOH, h1]
    simp only [nsmul_eq_mul]
    ring
  have hcc : c • c • Y ∈ Λ := nsmul_mem ha c
  obtain ⟨k, hk, hsign⟩ := GlobalTheory.LatVacSign.heisO_finRat_sign ψ S T ΛS ΛT hP.std hSd hTd f₀ hvac
    (-(((c : D.host.E) ^ 2) • M)) (by
      rw [neg_neg, hsmM, ← hY, pow_two, map_mul, mul_smul, ← hnat, ← hnat]; exact hcc)
  rw [neg_neg, hsmM, ← hY, pow_two, map_mul, mul_smul, ← hnat, ← hnat] at hsign
  set X1 := cA D e • (c • c • Y) with hX1
  have hY1 : cA D e • Y + R = Y := by rw [hRdef, ← add_smul, add_sub_cancel, one_smul]
  have hdec : c • c • Y = X1 + c • c • R := by
    calc c • c • Y = c • c • (cA D e • Y + R) := by rw [hY1]
      _ = X1 + c • c • R := by rw [hX1, smul_add, smul_add, smul_comm (cA D e) c, smul_comm (cA D e) c]
  have hfixX := (GlobalTheory.IdemSumVac.heisO_idemSum_fix D ψ S T Λ f₀ hvac hstab e SS he _ hcc).2
  have hfixXn : heisO ψ S T (-X1) f₀ = f₀ := by
    have h := (GlobalTheory.IdemSumVac.heisO_idemSum_fix D ψ S T Λ f₀ hvac hstab e SS he _ (neg_mem hcc)).2
    rwa [smul_neg] at h
  have hzero : symplOH S T (-X1) X1 = 0 := by
    have h0 : hO S T (-X1) X1 = 0 := by
      rw [hX1, ← smul_neg, GlobalTheory.LatVacSign.hO_smul_smul, GlobalTheory.LatVac.cA_cA, mul_comm (cA D e) e, he.2, zero_mul]
    rw [symplOH, symplO, h0, mul_zero, map_zero, mul_zero]
  have hinv : ∀ g, heisO ψ S T (-X1) (heisO ψ S T X1 g) = g := by
    intro g
    rw [GlobalTheory.LatVac.heisO_heisO, hzero, AddChar.map_zero_eq_one, one_smul, neg_add_cancel, GlobalTheory.LatVac.heisO_zero]
  have hcoc4 : ψ (symplOH S T X1 (c • c • R)) = 1 := by
    have e1 : X1 = c • c • (cA D e • Y) := by rw [hX1, smul_comm (cA D e) c, smul_comm (cA D e) c]
    rw [e1, hbil, hbil, ← mul_nsmul, AddChar.map_nsmul_eq_pow, hcoc, one_pow]
  obtain ⟨m, hm⟩ := id hcP
  have hR2eq : c • c • R = R + 2 • ((2 * m * m + 2 * m) • R) := by
    have h1 : R + 2 • ((2 * m * m + 2 * m) • R) = (1 + 2 * (2 * m * m + 2 * m)) • R := by
      rw [add_smul 1 (2 * (2 * m * m + 2 * m)) R, one_smul, mul_smul]
    rw [h1, smul_smul]
    congr 1; subst hm; ring
  have hRR : heisO ψ S T (c • c • R) f₀ = heisO ψ S T R f₀ := by
    have hmR : (2 * m * m + 2 * m) • R ∈ Λ := nsmul_mem hR _
    have h1 := GlobalTheory.LatVac.heisO_heisO ψ R (2 • ((2 * m * m + 2 * m) • R)) f₀
    have hs : symplOH S T R (2 • ((2 * m * m + 2 * m) • R)) = symplO S T R ((2 * m * m + 2 * m) • R) := by
      rw [symplOH, ← symplHom_apply, map_nsmul, symplHom_apply, nsmul_eq_mul, ← mul_assoc]
      have h12 : algebraMap D.host.F (AF D.host.F) (1 / 2) * ((2 : ℕ) : AF D.host.F) = 1 := by
        rw [← map_natCast (algebraMap D.host.F (AF D.host.F)), ← map_mul]; norm_num
      rw [h12, one_mul]
    rw [hvac.1 _ hmR, hs, GlobalTheory.LatVac.char_sympl_eq_one hP.std hSd hTd hR hmR, one_smul, ← hR2eq] at h1
    exact h1.symm
  have hRk : heisO ψ S T R f₀ = ((-1 : ℂ) ^ k) • f₀ := by
    have h1 := GlobalTheory.LatVac.heisO_heisO ψ X1 (c • c • R) f₀
    rw [hcoc4, one_smul, ← hdec, hsign, hRR] at h1
    have h2' := congrArg (heisO ψ S T (-X1)) h1
    rw [hinv, GlobalTheory.LatVac.heisO_smul, hfixXn] at h2'
    exact h2'

  obtain ⟨k₀, hk₀⟩ := GlobalTheory.HalfBInt.trace_int D ψ θ S T a b hS hT δ sc hP e SS he N N' c hc hcP h2qd ΛS ΛT hSd hTd hΛS hΛT y' hy'
  have hα := GlobalTheory.SemiTrace.alV_embH_eq_neg_one_zpow D ψ θ S T a b hS hT δ sc hP y' k₀ hk₀
  have hkk : k = (c : ℤ) ^ 4 * k₀ := by
    have e1 : GlobalTheory.LatVac.hRat S T (-(((c : D.host.E) ^ 2) • M)) (-(((c : D.host.E) ^ 2) • M)) =
        ((c : ℚ) ^ 4 : ℚ) • GlobalTheory.LatVac.hRat S T M M := by
      rw [← neg_smul, GlobalTheory.LatVacSign.hRat_smul_smul, star_neg, star_pow, star_natCast, Algebra.smul_def]
      push_cast; ring
    have e2 : (k : ℚ) = (c : ℚ) ^ 4 * k₀ := by
      rw [hk, e1, mul_smul_comm, map_smul, hk₀, smul_eq_mul]
    exact_mod_cast e2
  have hodd : Odd ((c : ℤ) ^ 4) := by
    obtain ⟨m', hm'⟩ := id hcP
    exact (show Odd (c : ℤ) from ⟨m', by exact_mod_cast hm'⟩).pow
  have hsgn : ((-1 : ℂ) ^ k) = alV D.host.d sc (embH (tauE D) δ y') := by
    rw [hα, hkk, _root_.zpow_mul, hodd.neg_one_zpow]
  have hα2 : alV D.host.d sc (embH (tauE D) δ y') * alV D.host.d sc (embH (tauE D) δ y') = 1 := by
    rw [hα, ← mul_zpow]; norm_num

  have hLHS : M.map (fun r => cA D e * incA D r) = cA D e • Y := by
    have h0 : infPart D (cA D e) = 0 := GlobalTheory.PlaceDatum.infPart_cA (GlobalTheory.PlaceDatum.infPart_idemSum he)
    ext i j
    change cA D e * incA D (M i j) = cA D e * ((pairA D.host.F 0 1) ⊗ₜ[D.host.F] M i j)
    rw [show (pairA D.host.F 0 1) ⊗ₜ[D.host.F] M i j = ((pairA D.host.F 0 1) ⊗ₜ[D.host.F] (1 : D.host.E)) * incA D (M i j) by
      rw [show incA D (M i j) = (1 : AF D.host.F) ⊗ₜ[D.host.F] M i j from rfl, Algebra.TensorProduct.tmul_mul_tmul,
        mul_one, one_mul], ← mul_assoc, GlobalTheory.PlaceDatum.mul_pair_one h0]
  have hfin := GlobalTheory.LatVac.heisO_heisO ψ (cA D e • Y) R f₀
  rw [hRk, hsgn, GlobalTheory.LatVac.heisO_smul, hcoc, one_smul, hY1] at hfin
  rw [hLHS, ← hfin, smul_smul, hα2, one_smul]

end GlobalTheory.ConjHalfHeis
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorConjugateHalfVacuumEqSemicharaStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergOperator_conjugateHalf_vacuum_eq_semicharacter : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (c : ℕ), 0 < c → Odd c → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → LaFacts (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → (ΛS : Set (Fin S.rank → D.host.E)) = latFr S hS N → (ΛT : Set (Fin T.rank → D.host.E)) = latFr T hT N' → ∀ f₀, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (latFr S hS N) (latFr T hT N') f₀ → ∀ y' ∈ halfBO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, heisO ψ S T (((LinearMap.toMatrix' (y')).reindex (finCongr hT.symm) (finCongr hS.symm)).map fun r => cA D e * incA D r) f₀ = alV D.host.d sc (embH (tauE D) δ y') • heisO ψ S T (GlobalTheory.VacUnique.finRat S T ((LinearMap.toMatrix' (y')).reindex (finCongr hT.symm) (finCongr hS.symm))) f₀ := by
  first | exact @GlobalTheory.ConjHalfHeis.heisO_conjHalf_eq | exact GlobalTheory.ConjHalfHeis.heisO_conjHalf_eq | (intros; apply GlobalTheory.ConjHalfHeis.heisO_conjHalf_eq <;> assumption)
end
