module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.Classical
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.WeilCharactersModular.LocCFT
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.CopNormLt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaCyc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaArtinLit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.GlBridge

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.DenseBox
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.Weier
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.MuDvd
open PowerSeries IsLocalRing UpperTheory.V.abelian₂
open IsDiscreteValuationRing (addVal)
open scoped Pointwise TensorProduct Topology

theorem UpperTheory.V.abelian₂.mu_dvd :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ f : O⟦X⟧,
      (∀ m : ℕ, (m : ℕ∞) ≤ mu f ↔ C ϖ ^ m ∣ f) ∧ (mu f = 0 ↔ map (residue O) f ≠ 0) ∧
        (mu f = 0 → lam f = (map (residue O) f).order.toNat) ∧
        ∀ m : ℕ, mu (C ϖ ^ m * f) = m + mu f ∧ lam (C ϖ ^ m * f) = lam f := by
  intro O _ _ _ ϖ hϖ f
  have hpow : ∀ m : ℕ, addVal O (ϖ ^ m) = m := by
    intro m
    rw [IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_uniformizer hϖ]
    simp
  have hdvd : ∀ m : ℕ, C ϖ ^ m ∣ f ↔ ∀ n, ϖ ^ m ∣ coeff n f := by
    intro m
    constructor
    · rintro ⟨g, rfl⟩ n
      rw [← map_pow, PowerSeries.coeff_C_mul]
      exact dvd_mul_right _ _
    · intro h
      choose g hg using h
      refine ⟨PowerSeries.mk g, ?_⟩
      ext n
      rw [← map_pow, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, ← hg n]
  have h1 : ∀ m : ℕ, (m : ℕ∞) ≤ mu f ↔ C ϖ ^ m ∣ f := by
    intro m
    rw [hdvd, mu, le_iInf_iff]
    refine forall_congr' fun n => ?_
    rw [← hpow m, IsDiscreteValuationRing.addVal_le_iff_dvd]
  have hmu0 : mu f = 0 → map (residue O) f ≠ 0 := by
    intro h hzero
    have hc := addVal_coeff_lam f
    rw [h, IsDiscreteValuationRing.addVal_eq_zero_iff, ← residue_ne_zero_iff_isUnit] at hc
    apply hc
    rw [← PowerSeries.coeff_map, hzero, map_zero]
  refine ⟨h1, ⟨hmu0, ?_⟩, ?_, ?_⟩
  · intro h
    obtain ⟨n, hn⟩ : ∃ n, coeff n (map (residue O) f) ≠ 0 := by
      by_contra hall
      push_neg at hall
      exact h (PowerSeries.ext fun n => by simpa using hall n)
    rw [PowerSeries.coeff_map, residue_ne_zero_iff_isUnit,
      ← IsDiscreteValuationRing.addVal_eq_zero_iff] at hn
    have hle := mu_le f n
    rw [hn] at hle
    exact le_antisymm hle bot_le
  · intro h
    have hord : (map (residue O) f).order = (lam f : ℕ∞) := by
      rw [PowerSeries.order_eq_nat]
      constructor
      · rw [PowerSeries.coeff_map, residue_ne_zero_iff_isUnit,
          ← IsDiscreteValuationRing.addVal_eq_zero_iff, addVal_coeff_lam, h]
      · intro i hi
        rw [PowerSeries.coeff_map]
        by_contra hne
        have hu : IsUnit (coeff i f) := (residue_ne_zero_iff_isUnit _).1 hne
        rw [← IsDiscreteValuationRing.addVal_eq_zero_iff] at hu
        have hli : lam f ≤ i := Nat.sInf_le (by
          show addVal O (coeff i f) = mu f
          rw [hu, h])
        omega
    rw [hord, ENat.toNat_coe]
  · intro m
    have hcoeff : ∀ n, addVal O (coeff n (C ϖ ^ m * f)) = m + addVal O (coeff n f) := by
      intro n
      rw [← map_pow, PowerSeries.coeff_C_mul, IsDiscreteValuationRing.addVal_mul, hpow]
    have hmu : mu (C ϖ ^ m * f) = m + mu f := by
      rw [mu, mu, ENat.add_iInf]
      exact iInf_congr hcoeff
    refine ⟨hmu, ?_⟩
    rw [lam, lam]
    congr 1
    ext n
    simp only [Set.mem_setOf_eq, hcoeff, hmu]
    exact ⟨fun h => WithTop.add_left_cancel (ENat.coe_ne_top m) h, fun h => by rw [h]⟩
end

open PowerSeries IsLocalRing UpperTheory.V.abelian₂
open IsDiscreteValuationRing (addVal)
open scoped Pointwise TensorProduct Topology

theorem UpperTheory.V.abelian₂.weier :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] (ϖ : O), Irreducible ϖ → ∀ f : O⟦X⟧, f ≠ 0 →
      ∃ (m : ℕ) (P : Polynomial O) (U : O⟦X⟧), mu f = m ∧ P.IsDistinguishedAt (maximalIdeal O) ∧ P.natDegree = lam f ∧
        IsUnit U ∧ f = C ϖ ^ m * (P : O⟦X⟧) * U := by
  intro O _ _ _ _ ϖ hϖ f hf
  have htop : mu f ≠ ⊤ := fun h => hf (mu_eq_top_iff.mp h)
  have hM := mu_dvd O ϖ hϖ
  obtain ⟨m, hmf⟩ : ∃ m : ℕ, (m : ℕ∞) = mu f := ⟨(mu f).toNat, ENat.coe_toNat htop⟩
  obtain ⟨g, hgf⟩ := ((hM f).1 m).mp hmf.le
  subst hgf
  obtain ⟨-, hzero, hlam, hshift⟩ := hM g
  obtain ⟨hmu, hl⟩ := hshift m
  have hg0 : mu g = 0 := by
    have h1 : (m : ℕ∞) + mu g = (m : ℕ∞) + 0 := by rw [add_zero, ← hmu, hmf]
    exact (WithTop.add_left_cancel (ENat.coe_ne_top m) h1)
  have hmap : (map (residue O)) g ≠ 0 := hzero.mp hg0
  obtain ⟨P, U, H⟩ := exists_isWeierstrassFactorization hmap
  refine ⟨m, P, U, hmf.symm, H.isDistinguishedAt, ?_, H.isUnit, ?_⟩
  · rw [hl, hlam hg0, H.natDegree_eq_toNat_order_map]
  · rw [mul_assoc, ← H.eq_mul]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.SepIffInjective
namespace UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite

variable {O R K : Type*} [CommRing O] [CommRing R] [CommRing K] [Algebra O R] [Algebra O K]

def Sep (Y : Set (R →ₐ[O] K)) : Prop := ∀ f : R, (∀ y ∈ Y, y f = 0) → f = 0

end UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.ExistsPt
open IsLocalRing UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite UpperTheory.V.HV UpperTheory.V.Alg

section SlopeTestRemainingChoices

open Polynomial

private theorem exPt_intIff {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l) : IsIntegral ℤ_[l] x ↔ ‖x‖ ≤ 1 := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have h0 : ‖x‖ = spectralValue (minpoly ℚ_[l] x) := rfl
  rw [h0, spectralValue_le_one_iff (minpoly.monic hi)]
  constructor
  · intro h n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, coeff_map]
    exact PadicInt.norm_le_one _
  · intro h
    have hl' : minpoly ℚ_[l] x ∈ lifts (algebraMap ℤ_[l] ℚ_[l]) :=
      (lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := lifts_and_degree_eq_and_monic hl' (minpoly.monic hi)
    exact ⟨q, hqm, by rw [← aeval_def, ← aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩

end SlopeTestRemainingChoices

private theorem exPt_coef {l : ℕ} [Fact l.Prime] (c : Coef l) (s : Finset (PadicAlgCl l))
    (hs : ∀ x ∈ s, IsIntegral ℤ_[l] x) : ∃ c' : Coef l, c.O ≤ c'.O ∧ ∀ x ∈ s, x ∈ c'.O := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨c, le_rfl, by simp⟩
  | insert a s _ ih =>
    obtain ⟨d, hd, hd'⟩ := ih fun x hx => hs x (Finset.mem_insert_of_mem hx)
    obtain ⟨e, he, he'⟩ := (coefSup l).2.2.1 d a (hs a (Finset.mem_insert_self _ _))
    refine ⟨e, hd.trans he, fun x hx => ?_⟩
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact he'
    · exact he (hd' x hx)

private theorem exPt_nonunit {l : ℕ} [Fact l.Prime] (c : Coef l) (x : c.O) (hx : ‖(x : PadicAlgCl l)‖ < 1) :
    ¬ IsUnit x := by
  intro hu
  obtain ⟨w, hw⟩ := hu.exists_right_inv
  have hi : IsIntegral ℤ_[l] (w : PadicAlgCl l) :=
    (Algebra.IsIntegral.isIntegral (R := ℤ_[l]) w).map c.O.val
  have h1 := (exPt_intIff _).1 hi
  have h2 : (x : PadicAlgCl l) * w = 1 := congrArg Subtype.val hw
  have h3 := congrArg norm h2
  rw [norm_mul, norm_one] at h3
  nlinarith [norm_nonneg (x : PadicAlgCl l), norm_nonneg (w : PadicAlgCl l)]

private theorem exPt_ev (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] {R σ : Type} [CommRing R] [Finite σ] (f : R →+* O)
    (a : σ → O) (ha : ∀ i, ¬ IsUnit (a i)) :
    ∃ G : MvPowerSeries σ R →+* O, (∀ r, G (MvPowerSeries.C r) = f r) ∧ ∀ i, G (MvPowerSeries.X i) = a i := by
  haveI : IsAdicComplete (maximalIdeal O) O := (UpperTheory.V.abelian₂.dvr_finite l O).1
  obtain ⟨F, ⟨hC, hX⟩, -⟩ := co_ev O O O σ (AlgHom.id _ _) a ha
  refine ⟨(F : MvPowerSeries σ O →+* O).comp (MvPowerSeries.map f), fun r => ?_, fun i => ?_⟩
  · rw [RingHom.comp_apply, MvPowerSeries.map_C, RingHom.coe_coe, hC]
    rfl
  · rw [RingHom.comp_apply, MvPowerSeries.map_X, RingHom.coe_coe, hX]

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.existsPt :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (σ : Type) [Finite σ] (z : σ → PadicAlgCl l), (∀ i, ‖z i‖ < 1) → ∃ (c' : Coef l) (y : MvPowerSeries σ c.O →ₐ[c.O] PadicAlgCl l), c.O ≤ c'.O ∧ (∀ f, y f ∈ c'.O) ∧ ∀ i, y (MvPowerSeries.X i) = z i := by
  intro l _ c σ _ z hz
  classical
  haveI := Fintype.ofFinite σ
  obtain ⟨c', hc, hm⟩ := exPt_coef c (Finset.univ.image z) fun x hx => by
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
    exact (exPt_intIff _).2 (hz i).le
  have hm' : ∀ i, z i ∈ c'.O := fun i => hm _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  obtain ⟨G, hC, hX⟩ := exPt_ev l c'.O (Subalgebra.inclusion hc).toRingHom (fun i => ⟨z i, hm' i⟩)
    fun i => exPt_nonunit c' _ (hz i)
  refine ⟨c', ⟨c'.O.val.toRingHom.comp G, fun r => ?_⟩, hc, fun f => (G f).2, fun i => ?_⟩
  · exact congrArg Subtype.val (hC r)
  · exact congrArg Subtype.val (hX i)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.OneVar
open IsLocalRing

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.oneVar :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [Field K] (ι : O →+* K), Function.Injective ι → ∀ (g : PowerSeries O) (Z : Set K), Z.Infinite → (∀ z ∈ Z, ∃ y : PowerSeries O →+* K, (∀ a, y (PowerSeries.C a) = ι a) ∧ y PowerSeries.X = z ∧ y g = 0) → g = 0 := by
  intro O K _ _ _ _ _ ι hι g Z hZ h
  by_contra hg
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨m, P, U, -, hP, -, hU, hfac⟩ := UpperTheory.V.abelian₂.weier O ϖ hϖ g hg
  have hmon : (P.map ι).Monic := hP.monic.map ι
  have hϖ0 : ι ϖ ≠ 0 := fun h0 => hϖ.ne_zero (hι (by rw [h0, map_zero]))
  refine hmon.ne_zero (Polynomial.eq_zero_of_infinite_isRoot _ (hZ.mono ?_))
  intro z hz
  obtain ⟨y, hyC, hyX, hy0⟩ := h z hz
  have hyP : y (P : PowerSeries O) = (P.map ι).eval z := by
    have e : y.comp Polynomial.coeToPowerSeries.ringHom = Polynomial.eval₂RingHom ι z := by
      apply Polynomial.ringHom_ext
      · intro a
        simp [hyC]
      · simp [hyX]
    have := RingHom.congr_fun e P
    simpa [Polynomial.eval_map] using this
  rw [hfac, map_mul, map_mul, map_pow, hyC, hyP] at hy0
  have hyU : y U ≠ 0 := (hU.map y).ne_zero
  show (P.map ι).IsRoot z
  rcases mul_eq_zero.1 hy0 with h1 | h1
  · rcases mul_eq_zero.1 h1 with h2 | h2
    · exact absurd h2 (pow_ne_zero m hϖ0)
    · exact h2
  · exact absurd h1 hyU
end

open IsLocalRing UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite UpperTheory.V.HV UpperTheory.V.Alg

private theorem algHom_mvPowerSeries_C_eq_algebraMap {A K : Type} [CommRing A] [CommRing K] [Algebra A K] {σ : Type}
    (y : MvPowerSeries σ A →ₐ[A] K) (a : A) : y (MvPowerSeries.C a) = algebraMap A K a := by
  have h := y.commutes a
  simpa [MvPowerSeries.algebraMap_apply] using h

private theorem exists_injective_mvPowerSeries_last_to_powerSeries (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (D : ℕ) :
    ∃ S : MvPowerSeries (Fin (D + 1)) R →+* PowerSeries (MvPowerSeries (Fin D) R),
      Function.Injective S ∧
      (∀ a : R, S (MvPowerSeries.C a) = PowerSeries.C (MvPowerSeries.C a)) ∧
      S (MvPowerSeries.X (Fin.last D)) = PowerSeries.X ∧
      ∀ i : Fin D, S (MvPowerSeries.X i.castSucc) = PowerSeries.C (MvPowerSeries.X i) := by
  haveI hA : UpperTheory.V.Alg.IsCO R (MvPowerSeries (Fin D) R) := UpperTheory.V.Alg.co_mvps R R (Fin D)
  haveI hB : UpperTheory.V.Alg.IsCO R (MvPowerSeries (Fin (D + 1)) R) :=
    UpperTheory.V.Alg.co_mvps R R (Fin (D + 1))
  haveI hP : UpperTheory.V.Alg.IsCO R (MvPowerSeries Unit (MvPowerSeries (Fin D) R)) :=
    UpperTheory.V.Alg.co_mvps R (MvPowerSeries (Fin D) R) Unit
  have nX : ∀ (τ : Type) (s : τ), MvPowerSeries.X s ∈
      IsLocalRing.maximalIdeal (MvPowerSeries τ R) := by
    intro τ s
    rw [IsLocalRing.mem_maximalIdeal]
    intro h
    rw [MvPowerSeries.isUnit_iff_constantCoeff, MvPowerSeries.constantCoeff_X] at h
    exact not_isUnit_zero h
  have nX' : (MvPowerSeries.X () : MvPowerSeries Unit (MvPowerSeries (Fin D) R)) ∈
      IsLocalRing.maximalIdeal _ := by
    rw [IsLocalRing.mem_maximalIdeal]
    intro h
    rw [MvPowerSeries.isUnit_iff_constantCoeff, MvPowerSeries.constantCoeff_X] at h
    exact not_isUnit_zero h
  have hmem : ∀ s : Fin (D + 1), (Fin.lastCases (MvPowerSeries.X ())
      (fun i => MvPowerSeries.C (MvPowerSeries.X i)) s :
        MvPowerSeries Unit (MvPowerSeries (Fin D) R)) ∈ IsLocalRing.maximalIdeal _ := by
    intro s
    refine Fin.lastCases ?_ (fun i => ?_) s
    · rw [Fin.lastCases_last]
      exact nX'
    · rw [Fin.lastCases_castSucc, IsLocalRing.mem_maximalIdeal]
      intro h
      rw [MvPowerSeries.isUnit_iff_constantCoeff, MvPowerSeries.constantCoeff_C] at h
      exact (IsLocalRing.mem_maximalIdeal _).1 (nX (Fin D) i) h
  obtain ⟨S, ⟨hSC, hSX⟩, -⟩ := UpperTheory.V.Alg.co_ev R R (MvPowerSeries Unit (MvPowerSeries (Fin D) R))
    (Fin (D + 1)) (Algebra.ofId R _) _ hmem
  obtain ⟨ι, ⟨hιC, hιX⟩, -⟩ := UpperTheory.V.Alg.co_ev R R (MvPowerSeries (Fin (D + 1)) R) (Fin D)
    (Algebra.ofId R _) (fun i => MvPowerSeries.X i.castSucc) (fun i => nX _ _)
  obtain ⟨T, ⟨hTC, hTX⟩, -⟩ := UpperTheory.V.Alg.co_ev R (MvPowerSeries (Fin D) R)
    (MvPowerSeries (Fin (D + 1)) R) Unit ι (fun _ => MvPowerSeries.X (Fin.last D)) (fun _ => nX _ _)
  obtain ⟨F, -, hF⟩ := UpperTheory.V.Alg.co_ev R R (MvPowerSeries (Fin (D + 1)) R) (Fin (D + 1))
    (Algebra.ofId R _) MvPowerSeries.X (fun s => nX _ s)
  have hTS : T.comp S = AlgHom.id R _ := by
    have e1 := hF (T.comp S) ⟨fun x => ?_, fun s => ?_⟩
    · have e2 := hF (AlgHom.id R _) ⟨fun x => ?_, fun s => rfl⟩
      · rw [e1, e2]
      · simp [Algebra.ofId_apply, MvPowerSeries.algebraMap_apply]
    · rw [AlgHom.comp_apply, hSC, Algebra.ofId_apply, AlgHom.commutes, Algebra.ofId_apply]
    · refine Fin.lastCases ?_ (fun i => ?_) s
      · rw [AlgHom.comp_apply, hSX, Fin.lastCases_last, hTX]
      · rw [AlgHom.comp_apply, hSX, Fin.lastCases_castSucc, hTC, hιX]
  refine ⟨S.toRingHom, fun x y h => ?_, fun a => ?_, ?_, fun i => ?_⟩
  · have h' : T (S x) = T (S y) := congrArg T h
    simpa [← AlgHom.comp_apply, hTS] using h'
  · have := hSC a
    simp only [Algebra.ofId_apply, MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply] at this
    exact this
  · exact (hSX (Fin.last D)).trans (by rw [Fin.lastCases_last]; rfl)
  · exact (hSX i.castSucc).trans (by rw [Fin.lastCases_castSucc]; rfl)

private theorem eq_zero_of_eval_eq_zero_on_infinite_unit_ball (l : ℕ) [Fact l.Prime] : ∀ (D : ℕ) (c : Coef l)
    (Z : Fin D → Set (PadicAlgCl l)), (∀ i, (Z i).Infinite) → (∀ i, ∀ z ∈ Z i, ‖z‖ < 1) →
    ∀ f : MvPowerSeries (Fin D) c.O,
      (∀ (c' : Coef l) (y : MvPowerSeries (Fin D) c.O →ₐ[c.O] PadicAlgCl l),
        (∀ g, y g ∈ c'.O) → (∀ i, y (MvPowerSeries.X i) ∈ Z i) → y f = 0) → f = 0 := by
  intro D
  induction D with
  | zero =>
    intro c Z hZ hn f hf
    obtain ⟨c', y, -, hy, -⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.existsPt l c (Fin 0) (fun i => i.elim0)
      (fun i => i.elim0)
    have h1 : f = MvPowerSeries.C (MvPowerSeries.constantCoeff f) := by
      ext n
      have hn0 : n = 0 := Subsingleton.elim _ _
      subst hn0
      simp
    have h2 := hf c' y hy (fun i => i.elim0)
    rw [h1, algHom_mvPowerSeries_C_eq_algebraMap] at h2
    have h3 : MvPowerSeries.constantCoeff f = 0 := Subtype.ext h2
    rw [h1, h3, map_zero]
  | succ D ih =>
    intro c Z hZ hn f hf
    haveI := c.dvr
    haveI := c.fin
    obtain ⟨hcpl, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
    obtain ⟨S, hSi, hSC, hSl, hSc⟩ := exists_injective_mvPowerSeries_last_to_powerSeries c.O D
    apply hSi
    rw [map_zero]
    refine PowerSeries.ext fun n => ?_
    rw [map_zero]
    apply ih c (fun i => Z i.castSucc) (fun i => hZ _) (fun i => hn _)
    intro c'' y'' hint hX
    haveI := c''.dvr
    haveI := c''.fin
    obtain ⟨hcpl'', -⟩ := UpperTheory.V.abelian₂.dvr_finite l c''.O
    let ycr : MvPowerSeries (Fin D) c.O →+* c''.O := y''.toRingHom.codRestrict c''.O hint
    have hycr : ∀ x, ((ycr x : c''.O) : PadicAlgCl l) = y'' x := fun x => rfl
    have hg : PowerSeries.map ycr (S f) = 0 := by
      refine UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.oneVar c''.O (PadicAlgCl l) c''.O.val.toRingHom
        Subtype.val_injective _ (Z (Fin.last D)) (hZ _) ?_
      intro z hz
      obtain ⟨c3, ev, -, hev, hevX⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.existsPt l c'' Unit (fun _ => z)
        (fun _ => hn _ z hz)
      have hevC : ∀ b : c''.O, ev (PowerSeries.C b) = b := fun b => algHom_mvPowerSeries_C_eq_algebraMap ev b
      let G : MvPowerSeries (Fin (D + 1)) c.O →ₐ[c.O] PadicAlgCl l :=
        { toRingHom := ev.toRingHom.comp ((PowerSeries.map ycr).comp S)
          commutes' := by
            intro a
            show ev (PowerSeries.map ycr (S (algebraMap c.O _ a))) = _
            rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, hSC,
              PowerSeries.map_C, hevC, hycr, algHom_mvPowerSeries_C_eq_algebraMap] }
      have hG : G f = 0 := by
        refine hf c3 G (fun g => hev _) (fun i => ?_)
        refine Fin.lastCases ?_ (fun j => ?_) i
        · show ev (PowerSeries.map ycr (S (MvPowerSeries.X (Fin.last D)))) ∈ _
          rw [hSl, PowerSeries.map_X]
          exact (hevX ()).symm ▸ hz
        · show ev (PowerSeries.map ycr (S (MvPowerSeries.X j.castSucc))) ∈ _
          rw [hSc, PowerSeries.map_C, hevC, hycr]
          exact hX j
      exact ⟨ev.toRingHom, fun a => hevC a, hevX (), hG⟩
    have h4 := congrArg (PowerSeries.coeff n) hg
    rw [PowerSeries.coeff_map, map_zero] at h4
    have h5 := congrArg Subtype.val h4
    rw [hycr] at h5
    exact h5

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.denseBox :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (D : ℕ) (Z : Fin D → Set (PadicAlgCl l)), (∀ i, (Z i).Infinite) → (∀ i, ∀ z ∈ Z i, ‖z‖ < 1) → Sep {y : MvPowerSeries (Fin D) c.O →ₐ[c.O] PadicAlgCl l | ∀ i, y (MvPowerSeries.X i) ∈ Z i} := by
  intro l _ c D Z hZ hn f hf
  exact eq_zero_of_eval_eq_zero_on_infinite_unit_ball l D c Z hZ hn f (fun c' y _ hX => hf y hX)
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

section Ball

variable {l : ℕ} [Fact l.Prime]

private theorem du_nrm {x : Qbar l} (h : ‖x - 1‖ < 1) : ‖x‖ = 1 := by
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := x - 1) (y := 1) (by rw [norm_one]; exact h.ne)
  rwa [sub_add_cancel, norm_one, max_eq_right h.le] at this

private theorem du_mul {x y : Qbar l} {ε : ℝ} (h1 : ε ≤ 1) (hx : ‖x - 1‖ < ε) (hy : ‖y - 1‖ < ε) : ‖x * y - 1‖ < ε := by
  have e : x * y - 1 = x * (y - 1) + (x - 1) := by ring
  rw [e]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ hx)
  rwa [norm_mul, du_nrm (hx.trans_le h1), one_mul]

variable (l) in
private def du_ball (ε : ℝ) (h0 : 0 < ε) (h1 : ε ≤ 1) : Subgroup (Qbar l)ˣ where
  carrier := {x | ‖(x : Qbar l) - 1‖ < ε}
  one_mem' := by simpa using h0
  mul_mem' hx hy := du_mul h1 hx hy
  inv_mem' := by
    intro x hx
    have hx' : ‖(x : Qbar l) - 1‖ < ε := hx
    have e : ((x⁻¹ : (Qbar l)ˣ) : Qbar l) - 1 = -((x : Qbar l)⁻¹ * (x - 1)) := by
      have := x.ne_zero
      push_cast; field_simp; ring
    show ‖((x⁻¹ : (Qbar l)ˣ) : Qbar l) - 1‖ < ε
    rwa [e, norm_neg, norm_mul, norm_inv, du_nrm (hx'.trans_le h1), inv_one, one_mul]

private theorem du_ball_open (ε : ℝ) (h0 : 0 < ε) (h1 : ε ≤ 1) : IsOpen (du_ball l ε h0 h1 : Set (Qbar l)ˣ) :=
  isOpen_lt ((Units.continuous_val.sub continuous_const).norm) continuous_const

private theorem du_norm_l : ‖(l : Qbar l)‖ < 1 := by
  have h : (l : Qbar l) = algebraMap ℚ_[l] (Qbar l) (l : ℚ_[l]) := by simp
  rw [h, norm_algebraMap']
  exact Padic.norm_p_lt_one

private theorem du_step {x : Qbar l} (hx : ‖x - 1‖ < 1) : ‖x ^ l - 1‖ ≤ ‖x - 1‖ * max ‖x - 1‖ ‖(l : Qbar l)‖ := by
  have hp : ∀ i : ℕ, ‖x ^ i - 1‖ ≤ ‖x - 1‖ := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have e : x ^ (i + 1) - 1 = x * (x ^ i - 1) + (x - 1) := by ring
      rw [e]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ le_rfl)
      rwa [norm_mul, du_nrm hx, one_mul]
  have e : ∑ i ∈ Finset.range l, x ^ i = ∑ i ∈ Finset.range l, (x ^ i - 1) + l := by simp
  rw [← mul_geom_sum, norm_mul, e]
  refine mul_le_mul_of_nonneg_left ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max ?_ le_rfl)) (norm_nonneg _)
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => hp i

private theorem du_small {x : Qbar l} (hx : ‖x - 1‖ < 1) {ε : ℝ} (h0 : 0 < ε) : ∃ k : ℕ, ‖x ^ l ^ k - 1‖ < ε := by
  set ρ := max ‖x - 1‖ ‖(l : Qbar l)‖ with hρ
  have h1 : ρ < 1 := max_lt hx du_norm_l
  have h2 : 0 ≤ ρ := (norm_nonneg _).trans (le_max_left _ _)
  have key : ∀ k : ℕ, ‖x ^ l ^ k - 1‖ ≤ ρ ^ (k + 1) := by
    intro k
    induction k with
    | zero => simp [hρ]
    | succ k ih =>
      have h3 : ρ ^ (k + 1) ≤ ρ := pow_le_of_le_one h2 h1.le k.succ_ne_zero
      rw [pow_succ l, pow_mul, pow_succ ρ]
      exact (du_step ((ih.trans h3).trans_lt h1)).trans
        (mul_le_mul ih (max_le (ih.trans h3) (le_max_right _ _)) ((norm_nonneg _).trans (le_max_left _ _)) (pow_nonneg h2 _))
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one h0 h1
  exact ⟨k, (key k).trans_lt ((pow_le_pow_of_le_one h2 h1.le k.le_succ).trans_lt hk)⟩

private theorem du_root_norm {ζ : Qbar l} {n : ℕ} (hn : n ≠ 0) (h : ζ ^ n = 1) : ‖ζ‖ = 1 := by
  have := congrArg norm h
  rw [norm_pow, norm_one] at this
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).1 this

private theorem du_root {ζ : Qbar l} {n : ℕ} (h : ζ ^ l ^ n = 1) : ‖ζ - 1‖ < 1 := by
  have hl : l.Prime := Fact.out
  have h1 := du_root_norm (pow_ne_zero _ hl.ne_zero) h
  let B : Subring (Qbar l) := (NormedField.valuation (K := Qbar l)).integer
  let z : B := ⟨ζ, h1.le⟩
  obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq hl (z - 1) 1 n
  have hr' := congrArg B.subtype hr
  simp only [map_pow, map_add (f := _), map_mul, map_sub, map_one, map_natCast, sub_add_cancel, one_pow,
    Subring.coe_subtype, mul_one] at hr'
  have hz : (z : Qbar l) = ζ := rfl
  rw [hz, h] at hr'
  have h2 : (ζ - 1) ^ l ^ n = -((l : Qbar l) * ((z - 1) * r : B)) := by
    push_cast
    rw [hz]
    linear_combination -hr'
  have h3 : ‖ζ - 1‖ ^ l ^ n < 1 := by
    rw [← norm_pow, h2, norm_neg, norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) du_norm_l ((z - 1) * r).2
  exact lt_of_pow_lt_pow_left₀ (l ^ n) zero_le_one (by rwa [one_pow])

private theorem du_prim (N : ℕ) (hN : N ≠ 0) : ∃ ζ : Qbar l, IsPrimitiveRoot ζ N := by
  haveI : NeZero N := ⟨hN⟩
  haveI : NeZero ((N : ℕ) : Qbar l) := ⟨Nat.cast_ne_zero.2 hN⟩
  exact HasEnoughRootsOfUnity.exists_primitiveRoot (Qbar l) N

private theorem du_near {u : Qbar l} {M : ℕ} (hM : 0 < M) (h : ‖u ^ M - 1‖ < 1) : ∃ ω : Qbar l, ω ^ M = 1 ∧ ‖u * ω - 1‖ < 1 := by
  obtain ⟨ζ, hζ⟩ := du_prim (l := l) M hM.ne'
  have e := congrArg (eval u) (X_pow_sub_one_eq_prod hM hζ)
  simp only [eval_sub, eval_pow, eval_X, eval_one, eval_prod, eval_C] at e
  rw [e, norm_prod] at h
  by_contra hn
  push Not at hn
  refine h.not_ge (Finset.prod_induction _ (fun t : ℝ => 1 ≤ t) (fun _ _ => one_le_mul_of_one_le_of_one_le) le_rfl fun η hη => ?_)
  have h1 : η ^ M = 1 := (mem_nthRootsFinset hM _).1 hη
  have h2 := du_root_norm hM.ne' h1
  have h0 : η ≠ 0 := fun h => by simp [h] at h2
  have h3 := hn η⁻¹ (by rw [inv_pow, h1, inv_one])
  rwa [show u * η⁻¹ - 1 = (u - η) * η⁻¹ by field_simp, norm_mul, norm_inv, h2, inv_one, mul_one] at h3

private theorem du_sets {σ : Type} {n : ℕ} (idx : σ → Fin n) (u : σ → Qbar l) {M : ℕ} (hM : 0 < M)
    (h : ∀ s, ‖u s ^ M - 1‖ < 1) : ∃ R : σ → Set (Qbar l), (∀ s, (R s).Infinite) ∧
      (∀ s, ∀ η ∈ R s, IsOfFinOrder η ∧ ‖u s * η - 1‖ < 1) ∧ ∀ s s', idx s ≠ idx s' → ∀ η ∈ R s, η ∉ R s' := by
  have hl : l.Prime := Fact.out
  choose ω hω hω' using fun s => du_near hM (h s)
  choose ζ hζ using fun k : ℕ => du_prim (l := l) (l ^ k) (pow_ne_zero _ hl.ne_zero)
  have k1 : ∀ s s' a b, a < b → ω s * ζ (M * a) ≠ ω s' * ζ (M * b) := fun s s' a b hab e => by
    have e1 := congrArg (· ^ (M * l ^ (M * a))) e
    simp only [mul_pow, pow_mul (ω _), hω, one_pow, one_mul] at e1
    rw [mul_comm M (l ^ _), pow_mul, (hζ _).pow_eq_one, one_pow] at e1
    have e2 := (hζ _).dvd_of_pow_eq_one _ e1.symm
    have e3 : l ^ (M * a) * l ^ M ∣ l ^ (M * a) * M := by
      rw [← pow_add]
      exact (pow_dvd_pow l (by nlinarith)).trans e2
    have e4 := Nat.le_of_dvd hM (Nat.dvd_of_mul_dvd_mul_left (pow_pos hl.pos _) e3)
    exact (Nat.lt_pow_self hl.one_lt).not_ge e4
  have k2 : ∀ s s' a b, ω s * ζ (M * a) = ω s' * ζ (M * b) → a = b := fun s s' a b e => by
    rcases lt_trichotomy a b with h | h | h
    exacts [absurd e (k1 _ _ _ _ h), h, absurd e.symm (k1 _ _ _ _ h)]
  refine ⟨fun s => Set.range fun t : ℕ => ω s * ζ (M * (idx s + n * t)), fun s => Set.infinite_range_of_injective
    fun t t' e => ?_, ?_, ?_⟩
  · have := k2 _ _ _ _ e
    exact Nat.eq_of_mul_eq_mul_left (idx s).pos (Nat.add_left_cancel this)
  · rintro s _ ⟨t, rfl⟩
    refine ⟨(isOfFinOrder_iff_pow_eq_one.2 ⟨M, hM, hω s⟩).mul ((hζ _).isOfFinOrder (pow_ne_zero _ hl.ne_zero)), ?_⟩
    show ‖u s * (ω s * _) - 1‖ < 1
    rw [← mul_assoc]
    exact du_mul le_rfl (hω' s) (du_root (hζ _).pow_eq_one)
  · rintro s s' hs _ ⟨t, rfl⟩ ⟨t', e⟩
    have := congrArg (· % n) (k2 _ _ _ _ e)
    simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (Fin.is_lt _)] at this
    exact hs (Fin.ext this.symm)

end Ball

section Grp

variable {l : ℕ} [Fact l.Prime] {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]

private theorem du_pow (Φ : Γ →* (Qbar l)ˣ) (hΦ : Continuous Φ) : ∃ M, 0 < M ∧ ∀ g, ‖(Φ g : Qbar l) ^ M - 1‖ < 1 := by
  let H := (du_ball l 1 one_pos le_rfl).comap Φ
  haveI := H.quotient_finite_of_isOpen ((du_ball_open 1 one_pos le_rfl).preimage hΦ)
  refine ⟨H.index, Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite, fun g => ?_⟩
  have h : Φ (g ^ H.index) ∈ du_ball l 1 one_pos le_rfl := H.pow_index_mem g
  rw [map_pow] at h
  exact h

variable {I : Subgroup Γ} {d : ℕ} (A : W.LocAb l Γ I d)

private theorem du_ker (Φ : Γ →* (Qbar l)ˣ) (hΦ : Continuous Φ) : ∃ M, 0 < M ∧ ∀ g, A.a g = 1 → Φ g ^ M = 1 := by
  obtain ⟨M, hM, h1⟩ := du_pow Φ hΦ
  haveI := A.b.ker.quotient_finite_of_isOpen A.b_open
  refine ⟨A.b.ker.index * M, Nat.mul_pos (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) hM, fun g hg => ?_⟩
  let Ψ : Γ →* (Qbar l)ˣ := (powMonoidHom (A.b.ker.index * M)).comp Φ
  have hΨ : Continuous Ψ := hΦ.pow _
  have h2 : ∀ x, ‖(Ψ x : Qbar l) - 1‖ < 1 := fun x => by
    have := h1 (x ^ A.b.ker.index)
    rwa [map_pow, Units.val_pow_eq_pow_val, ← pow_mul] at this
  have h3 : ∀ x ∈ W.muG l Γ, Ψ x = 1 := fun x hx => by
    have e1 := A.b_mu _ (pow_mem hx A.b.ker.index)
    rw [MonoidHom.mem_ker.1 (A.b.ker.pow_index_mem x)] at e1
    have e2 : x ^ A.b.ker.index ∈ (commutator Γ).topologicalClosure := (QuotientGroup.eq_one_iff _).1 e1.symm
    have e3 : Φ (x ^ A.b.ker.index) = 1 := Subgroup.topologicalClosure_minimal _ (Abelianization.commutator_subset_ker Φ)
      (isClosed_singleton.preimage hΦ) e2
    show Φ x ^ (A.b.ker.index * M) = 1
    rw [pow_mul, ← map_pow, e3, one_pow]
  show Ψ g = 1
  refine Units.ext (sub_eq_zero.1 (norm_le_zero_iff.1 (le_of_forall_pos_le_add fun ε hε => ?_)))
  have h0 : 0 < min ε 1 := lt_min hε one_pos
  let B := du_ball l _ h0 (min_le_right _ _)
  let χ := (QuotientGroup.mk' B).comp Ψ
  have hk : ∀ x, x ∈ χ.rangeRestrict.ker ↔ Ψ x ∈ B := fun x => by
    rw [MonoidHom.ker_rangeRestrict]
    exact QuotientGroup.eq_one_iff _
  have ho : IsOpen (χ.rangeRestrict.ker : Set Γ) := by
    rw [show (χ.rangeRestrict.ker : Set Γ) = Ψ ⁻¹' B from Set.ext hk]
    exact (du_ball_open _ _ _).preimage hΨ
  haveI := χ.rangeRestrict.ker.quotient_finite_of_isOpen ho
  haveI : Finite χ.range := Finite.of_equiv _ (QuotientGroup.quotientKerEquivOfSurjective _ χ.rangeRestrict_surjective).toEquiv
  have hp : IsPGroup l χ.range := by
    rintro ⟨_, x, rfl⟩
    obtain ⟨k, hk'⟩ := du_small (h2 x) h0
    refine ⟨k, Subtype.ext ?_⟩
    show (QuotientGroup.mk' B) (Ψ x) ^ l ^ k = 1
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).2 hk'
  have h4 : ‖(Ψ g : Qbar l) - 1‖ < min ε 1 :=
    (hk g).1 (A.univ χ.range hp χ.rangeRestrict ho (fun x hx => (hk x).2 (by rw [h3 x hx]; exact B.one_mem)) hg)
  rw [zero_add]
  exact h4.le.trans (min_le_left _ _)

private theorem du_fin (Φ : Γ →* (Qbar l)ˣ) (hΦ : Continuous Φ) (γ : Fin d → Γ)
    (hγ : ∀ j, A.a (γ j) = Multiplicative.ofAdd (Pi.single j 1, 0)) (ho : ∀ j, IsOfFinOrder (Φ (γ j))) :
    ∃ N, 0 < N ∧ ∀ g ∈ I, Φ g ^ N = 1 := by
  obtain ⟨M, hM, h1⟩ := du_ker A Φ hΦ
  let N := M * ∏ j, orderOf (Φ (γ j))
  refine ⟨N, Nat.mul_pos hM (Finset.prod_pos fun j _ => (ho j).orderOf_pos), fun g hg => ?_⟩
  let K := ((powMonoidHom N).comp Φ).ker
  have hK : IsClosed (K : Set Γ) := isClosed_singleton.preimage (hΦ.pow N)
  have hS : IsClosed (K.map A.a : Set (Multiplicative ((Fin d → ℤ_[l]) × ℤ_[l]))) := (hK.isCompact.image A.cont).isClosed
  have hγK : ∀ j, γ j ∈ K := fun j =>
    orderOf_dvd_iff_pow_eq_one.1 ((Finset.dvd_prod_of_mem _ (Finset.mem_univ j)).mul_left M)
  have hd : DenseRange (Pi.map fun (_ : Fin d) => (Nat.cast : ℕ → ℤ_[l])) :=
    DenseRange.piMap fun _ => PadicInt.denseRange_natCast
  have key : ∀ x : Fin d → ℤ_[l], Multiplicative.ofAdd (x, (0 : ℤ_[l])) ∈ K.map A.a := fun x => by
    refine hd.induction_on x (hS.preimage (continuous_ofAdd.comp (continuous_id.prodMk continuous_const))) fun m => ?_
    refine ⟨(List.ofFn fun j => γ j ^ m j).prod, ?_, ?_⟩
    · exact K.list_prod_mem fun y hy => by
        obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hy
        exact pow_mem (hγK j) _
    · rw [map_list_prod, List.map_ofFn, List.prod_ofFn]
      apply Multiplicative.toAdd.injective
      simp only [Function.comp_apply, map_pow, hγ, toAdd_prod, toAdd_pow, toAdd_ofAdd]
      refine Prod.ext (funext fun j => ?_) ?_
      · simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
      · simp [Prod.snd_sum]
  have h2 : (A.a g).toAdd.2 = 0 := (A.inertia _).1 ⟨g, hg, rfl⟩
  obtain ⟨k, hk, e⟩ := key (A.a g).toAdd.1
  have h3 : A.a (k⁻¹ * g) = 1 := by
    rw [map_mul, map_inv, e, inv_mul_eq_one, ← h2]
    rfl
  have h4 : k⁻¹ * g ∈ K := by
    show Φ _ ^ (M * _) = 1
    rw [pow_mul, h1 _ h3, one_pow]
  exact (K.mul_mem_cancel_left (inv_mem hk)).1 h4

omit [IsTopologicalGroup Γ] [CompactSpace Γ] in
private theorem du_cont (c : Coef l) (R : Type) [CommRing R] [Algebra c.O R] [Alg.IsCO c.O R] (x : R →ₐ[c.O] Qbar l)
    (ψ : Γ →* Rˣ) (hψ : Alg.AdicCont (maximalIdeal R) fun g => (ψ g : R)) : Continuous (W.pushCh (x : R →+* Qbar l) ψ) := by
  obtain ⟨-, a, ha1, ha0, ha⟩ := (GradeZeroInterpolatingElement.coPt c R).1 x
  refine Units.isEmbedding_val₀.continuous_iff.2 (continuous_iff_continuousAt.2 fun g => Metric.tendsto_nhds.2 fun ε hε => ?_)
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε ha1
  filter_upwards [(hψ k).eventually_eq g] with g' hg'
  rw [dist_eq_norm]
  have := ha k _ (Ideal.Quotient.eq.1 hg')
  rw [map_sub] at this
  exact this.trans_lt hk

end Grp

section Loc

private theorem du_Uc (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (U : Subgroup kˣ) (hU : IsOpen (U : Set kˣ)) : ∃ e, ∀ e', e ≤ e' → Uc k e' ≤ U := by
  obtain ⟨e, he⟩ := (glBridge k 1 ℂ 1).2.2.2.1 (U.comap Matrix.GeneralLinearGroup.det) (hU.preimage continuous_glDet)
  refine ⟨e, fun e' h => ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  have h1 : Ideal.Quotient.mk _ u.val = Ideal.Quotient.mk _ 1 := congrArg Units.val (MonoidHom.mem_ker.1 hu)
  have h2 := Ideal.Quotient.eq.2 (Ideal.pow_le_pow_right h (Ideal.Quotient.eq.1 h1))
  have h3 := he ⟨Matrix.GeneralLinearGroup.scalar (Fin 1) u, by
    refine Units.ext (Matrix.ext fun i j => ?_)
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
    simpa using h2, rfl⟩
  rw [Subgroup.mem_comap] at h3
  convert h3 using 1
  ext
  simp

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
  {A : ValuationSubring Ω} {w : Plc F} {h : IsPlaceOver A w} {a : Weil h →* (w.adicCompletion F)ˣ}

private theorem du_unit (ha : IsLocalArtin h a) (s : Weil h) : a s ∈ Uo (w.adicCompletion F) ↔ (s : G F Ω) ∈ Ine (F := F) A := by
  rw [← deg_eq_zero_iff, ← neg_eq_zero, ← ha.ord_eq, ord_eq_zero_iff]
  rfl

private theorem du_alg (H : GlobalTheory.Published.GlobalArtinReciprocity) (ha : IsLocalArtin h a) (hh : (F →+* Qbar l) → ℤ) :
    ∃ δ : Dec (F := F) A →* (Qbar l)ˣ, Continuous δ ∧ ∀ s : Weil h, (s : G F Ω) ∈ Ine (F := F) A →
      (δ (Subgroup.inclusion (Weil_le_Dec h) s) : Qbar l) = algPow w hh (a s : w.adicCompletion F) := by
  haveI := GlobalTheory.HeckeGal.finite_contEmb (l := l) w
  letI := Fintype.ofFinite {j : w.adicCompletion F →+* Qbar l // Continuous j}
  haveI := compactSpace_Ine (E := F) A
  let α : (w.adicCompletion F)ˣ →* (Qbar l)ˣ := ∏ j : {j : w.adicCompletion F →+* Qbar l // Continuous j},
    Units.map j.1.toMonoidHom ^ hh (j.1.comp (algebraMap F _))
  have hα : ∀ y, (α y : Qbar l) = algPow w hh (y : w.adicCompletion F) := fun y => by
    simp [α, algPow, finprod_eq_prod_of_fintype, MonoidHom.finsetProd_apply]
  have hc : Continuous α := by
    have : (α : _ → _) = fun y => ∏ j : {j : w.adicCompletion F →+* Qbar l // Continuous j},
      Units.map j.1.toMonoidHom y ^ hh (j.1.comp (algebraMap F _)) := funext fun y => by
        simp [α, MonoidHom.finsetProd_apply]
    rw [this]
    exact continuous_finsetProd _ fun j _ => (continuous_zpow _).comp (Continuous.units_map _ j.2)
  let β : (w.adicCompletion F)ˣ →* (Qbar l)ˣ := MonoidHom.mk' (fun y => α (a (frob h)) ^ ord _ y) fun x y => by
    rw [ord_mul, zpow_add]
  have hβ : Continuous β := by
    refine GlobalTheory.HeckeGal.continuous_of_isOpen_ker' β (Subgroup.isOpen_mono (H₁ := (GlobalTheory.SmGL.unrChar _ (Units.mk0 (2 : ℂ) two_ne_zero)).ker)
      (fun x hx => ?_) (isSmoothChar_of_isUnram (isUnram_unrChar _ _)))
    have h1 : (2 : ℂ) ^ ord _ x = 1 := by simpa [GlobalTheory.SmGL.unrChar_apply] using congrArg Units.val (MonoidHom.mem_ker.1 hx)
    have h2 : (2 : ℝ) ^ ord _ x = 1 := by simpa using congrArg norm h1
    have h3 : ord _ x = 0 := (zpow_eq_one_iff_right₀ zero_le_two (by norm_num)).1 h2
    show α _ ^ ord _ x = 1
    rw [h3, zpow_zero]
  obtain ⟨M, hM, h1⟩ := du_pow ((α.comp a).comp (ineIncl h)) (hc.comp ha.cont)
  obtain ⟨δ, ⟨c1, c2⟩, -⟩ := Loc.laExists H h a ha (α * β) (hc.mul hβ) fun x => by
    obtain ⟨s, rfl⟩ := ha.surj x
    obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul deg_frob s
    have e : (α * β) (a s) = α (a (ineIncl h τ)) := by
      show α (a s) * α _ ^ ord _ (a s) = _
      rw [ha.ord_eq]
      conv_lhs => enter [1]; rw [hτ, map_mul, map_mul, map_zpow, map_zpow]
      rw [mul_right_comm, ← zpow_add, add_neg_cancel, zpow_zero, one_mul]
    have h2 := du_nrm (h1 τ)
    rw [norm_pow] at h2
    rw [e]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hM.ne').1 h2
  refine ⟨δ, c1, fun s hs => ?_⟩
  rw [c2, ← hα]
  show ((α (a s) * α _ ^ ord _ (a s) : (Qbar l)ˣ) : Qbar l) = _
  rw [ha.ord_eq, deg_eq_zero_iff.2 hs, neg_zero, zpow_zero, mul_one]

private theorem du_arith (ha : IsLocalArtin h a) (Φ : Dec (F := F) A →* (Qbar l)ˣ) (hΦ : Continuous Φ) {N : ℕ} (hN : 0 < N)
    (h1 : ∀ g ∈ (Ine (F := F) A).subgroupOf (Dec (F := F) A), Φ g ^ N = 1) :
    ∃ e, ∀ e', e ≤ e' → ∀ s : Weil h, a s ∈ Uc _ e' → Φ (Subgroup.inclusion (Weil_le_Dec h) s) = 1 := by
  obtain ⟨ι⟩ : Nonempty (Qbar l ≃+* ℂ) := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex l
  let i : Ine (F := F) A →* Dec (F := F) A := (Subgroup.inclusion (Weil_le_Dec h)).comp (ineIncl h)
  have hi : Continuous i := continuous_subtype_val.subtype_mk _
  have ho := GlobalTheory.HeckeGal.isOpen_ker_of_pow (Φ.comp i) (hΦ.comp hi) hN fun σ => h1 _ σ.2
  let ξ : Weil h →* ℂˣ := (Units.map ι.toRingHom.toMonoidHom).comp (Φ.comp (Subgroup.inclusion (Weil_le_Dec h)))
  obtain ⟨χ, hχ, e⟩ := ha.factor ξ (Subgroup.isOpen_mono (H₂ := (ξ.comp (ineIncl h)).ker) (fun x hx => by
    show Units.map _ ((Φ.comp i) x) = 1
    rw [MonoidHom.mem_ker.1 hx, map_one]) ho)
  obtain ⟨k, hk⟩ := du_Uc _ χ.ker hχ
  refine ⟨k, fun e' he s hs => Units.ext (ι.injective ?_)⟩
  have h2 : ξ s = 1 := by rw [e]; exact hk e' he hs
  exact (congrArg Units.val h2).trans (map_one ι).symm

private theorem du_cyc : Continuous (cycBar F Ω l) :=
  (Continuous.units_map ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom).toMonoidHom
    ((continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val)).comp (continuous_cycZ F Ω l)

private theorem du_pos {E : Type} [Field E] [NumberField E] [Algebra E Ω] [IsAlgClosure E Ω] {v : Plc E}
    (h : IsPlaceOver A v) (hw : ((l : ℕ) : 𝓞 E) ∈ v.asIdeal) {d : ℕ}
    (B : W.LocAb l (Dec (F := F) A) ((Ine (F := F) A).subgroupOf (Dec (F := F) A)) d) : 0 < d := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  haveI : CompactSpace (Dec (F := F) A) := isCompact_iff_compactSpace.1 (isClosed_Dec A).isCompact
  by_contra hd
  obtain rfl : d = 0 := by omega
  obtain ⟨N, hN, h1⟩ := du_fin B ((cycBar F Ω l).comp (Dec (F := F) A).subtype) (du_cyc.comp continuous_subtype_val)
    Fin.elim0 (fun j => j.elim0) fun j => j.elim0
  obtain ⟨j, rfl⟩ := (Loc.decEmb (F := E) (Ω := Ω) (v := l)).1 A v h hw
  obtain ⟨-, φ, b1, -, -, b4, b5, -⟩ := (Loc.decEmb (F := F) (Ω := Ω) (v := l)).2 j
  obtain ⟨-, _, ⟨⟨g, rfl⟩, hg⟩, h2⟩ := (Loc.cycInertia l).2 φ.range b1.isOpen_range
  rw [b5] at h2
  refine h2 (isOfFinOrder_iff_pow_eq_one.2 ⟨N, hN, Units.ext (Subtype.ext ((algebraMap ℚ_[l] (Qbar l)).injective ?_))⟩)
  have h3 := congrArg Units.val (h1 g ((b4 g).1 hg))
  simp [cycBar] at h3 ⊢
  exact h3

end Loc

private theorem du_box {l : ℕ} [Fact l.Prime] (c : Coef l) {σ : Type} [Fintype σ] {n : ℕ} (idx : σ → Fin n) (u : σ → Qbar l)
    (h : ∀ s, ∃ M, 0 < M ∧ ‖u s ^ M - 1‖ < 1) (f : MvPowerSeries σ c.O)
    (hf : ∀ (y : MvPowerSeries σ c.O →ₐ[c.O] Qbar l) (η : σ → Qbar l), (∀ s, IsOfFinOrder (η s)) →
      (∀ s s', idx s ≠ idx s' → η s ≠ η s') → (∀ s, 1 + y (MvPowerSeries.X s) = u s * η s) → y f = 0) : f = 0 := by
  choose M hM h using h
  have hp : ∀ (x : Qbar l) (k : ℕ), ‖x - 1‖ < 1 → ‖x ^ k - 1‖ < 1 := fun x k hx => by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ]; exact du_mul le_rfl ih hx
  obtain ⟨R, h1, h2, h3⟩ := du_sets idx u (M := ∏ s, M s) (Finset.prod_pos fun s _ => hM s) fun s => by
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem M (Finset.mem_univ s)
    rw [hk, pow_mul]
    exact hp _ _ (h s)
  have h0 : ∀ s, u s ≠ 0 := fun s e => by simpa [e, (hM s).ne'] using h s
  let e := Finite.equivFin σ
  let E := MvPowerSeries.renameEquiv c.O e
  refine E.injective ?_
  rw [map_zero]
  refine AlgebraTools.AnnihilatorQuotientFinite.denseBox l c (Nat.card σ) (fun j => (fun η => u (e.symm j) * η - 1) '' R (e.symm j))
    (fun j => (h1 _).image fun x _ y _ hxy => mul_left_cancel₀ (h0 _) (sub_left_injective hxy)) ?_ _ fun y hy => ?_
  · rintro j _ ⟨η, hη, rfl⟩
    exact (h2 _ _ hη).2
  · choose η hη hη' using fun s => hy (e s)
    simp only [Equiv.symm_apply_apply] at hη hη'
    refine hf (y.comp (E : MvPowerSeries σ c.O →ₐ[c.O] MvPowerSeries (Fin (Nat.card σ)) c.O)) η (fun s => (h2 _ _ (hη s)).1)
      (fun s s' hs e' => h3 s s' hs _ (hη s) (e' ▸ hη s')) fun s => ?_
    rw [← sub_add_cancel (u s * η s) 1, hη', add_comm]
    simp [E]

theorem UpperTheory.V.Hi.denseU :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O), ∀ (r : Resid V.frame c.O n) (Λ : LamObj r) (θ : (hset Q τ₀).X.I.T →* Λ.Λˣ), IsTheta Q τ₀ Λ θ → IsDomain Λ.Λ ∧ ∀ lam, (hset Q τ₀).DenseWt θ lam := by
  intro hN l _ L Ω _ _ _ _ _ _ s n _ V Q c m τ₀ r Λ θ hθ
  classical
  haveI : IsAdicComplete (maximalIdeal c.O) c.O := (UpperTheory.V.Base.dvrFacts l c.O).2.2.2.1
  haveI : IsLocalHom (algebraMap ℤ_[l] c.O) := (UpperTheory.V.Base.dvrFacts l c.O).2.2.1
  haveI : Finite (ResidueField ℤ_[l]) := Finite.of_equiv _ (PadicInt.residueField (p := l)).symm.toEquiv
  haveI : Finite (ResidueField c.O) := Module.finite_of_finite (ResidueField ℤ_[l])
  haveI : CharP (ResidueField ℤ_[l]) l :=
    charP_of_injective_ringHom (f := (PadicInt.residueField (p := l)).symm.toRingHom)
      (PadicInt.residueField (p := l)).symm.injective l
  haveI : CharP (ResidueField c.O) l :=
    charP_of_injective_ringHom (algebraMap (ResidueField ℤ_[l]) (ResidueField c.O)).injective l
  obtain ⟨d₀, -, hA⟩ := W.locCFT hN.aut.art ⟨hN.coh.lf, hN.coh.lt, hN.coh.le, hN.coh.gf, hN.coh.ge, hN.coh.gw, hN.coh.pt,
    GlobalTheory.Published.TameLocal_of_duality hN.coh.lt⟩ l L Ω s
  let d : V.frame.Vl → ℕ := d₀
  let A : ∀ v : V.frame.Vl, W.LocAb l (V.frame.Gv v) (V.frame.Iv v) (d v) := fun v => (hA v).some
  have hd : ∀ v : V.frame.Vl, 0 < d v := fun v => du_pos (s.hA v.1) v.2 (hA v).some
  obtain ⟨e, ψ₀, hψ₀, he⟩ := (W.lam_ex_free l V.frame c.O n r d A).2 Λ
  haveI : IsDomain (MvPowerSeries (Σ v : V.frame.Vl, Fin n × Fin (d v)) c.O) := NoZeroDivisors.to_isDomain _
  refine ⟨MulEquiv.isDomain _ e.symm.toMulEquiv, fun lam f hf => ?_⟩
  have ha : ∀ v : V.frame.Vl, IsLocalArtin (s.hw v.1) (artOf (s.hw v.1)) :=
    fun v => Classical.epsilon_spec (Loc.localArtinReciprocity hN _)
  choose δ hδ hδ' using fun (v : V.frame.Vl) (i : Fin n) => du_alg (l := l) hN.aut.art (ha v) (lowW lam i)
  choose ψ hψ hκ using Λ.inert
  let ω : ∀ v : V.frame.Vl, Fin n → V.frame.Gv v →* (Qbar l)ˣ := fun v i =>
    ((cycBar L Ω l).comp (Dec (F := L) (s.A v.1)).subtype) ^ (i : ℕ) * δ v i
  have hω : ∀ v i, Continuous (ω v i) := fun v i => ((du_cyc.comp continuous_subtype_val).pow (i : ℕ)).mul (hδ v i)
  let Φ : (Λ.Λ →ₐ[c.O] Qbar l) → ∀ v : V.frame.Vl, Fin n → V.frame.Gv v →* (Qbar l)ˣ := fun x v i =>
    W.pushCh (x : Λ.Λ →+* Qbar l) (ψ v i) * ω v i
  have hΦ : ∀ x v i, Continuous (Φ x v i) := fun x v i => (du_cont c Λ.Λ x _ (hψ v i).cont).mul (hω v i)
  have key : ∀ (x : Λ.Λ →ₐ[c.O] Qbar l) (v : V.frame.Vl) i (t : Weil (s.hw v.1)) (y : Uo ((s.w v.1).adicCompletion L)),
      artOf (s.hw v.1) t = y → (hset Q τ₀).finPart θ (x : Λ.Λ →+* Qbar l) lam v i y =
        ((Φ x v i (Subgroup.inclusion (Weil_le_Dec _) t) : (Qbar l)ˣ) : Qbar l)⁻¹ := by
    intro x v i t y hy
    have ht := (du_unit (ha v) t).1 (hy ▸ y.2)
    have h1 := congrArg (fun z : Λ.Λˣ => x z) (hθ v i t (Subgroup.inclusion (Weil_le_Dec _) t) ht y rfl hy)
    simp only [hκ, Units.val_mul, map_mul, Units.val_pow_eq_pow_val, map_pow, Units.val_one, map_one] at h1
    have h2 : x ((hset Q τ₀).epsV Λ.Λ v (Subgroup.inclusion (Weil_le_Dec _) t) : Λ.Λˣ) = cycBar L Ω l t := x.commutes _
    have h3 := hδ' v i t ht
    rw [hy] at h3
    show x _ / algPow (s.w v.1) _ _ = (x (ψ v i _) * ((cycBar L Ω l t ^ (i : ℕ) : (Qbar l)ˣ) * δ v i _))⁻¹
    rw [h3, ← mul_assoc, mul_inv, div_eq_mul_inv, Units.val_pow_eq_pow_val]
    exact congrArg (· * _) (eq_inv_of_mul_eq_one_right (by rw [← h2]; exact h1))
  choose γ hγI hγ using fun (v : V.frame.Vl) (j : Fin (d v)) => ((A v).inertia (Pi.single j 1, 0)).2 rfl
  let χ : ∀ v : V.frame.Vl, Fin n → V.frame.Gv v →* (Qbar l)ˣ := fun v i =>
    (W.pushCh (Algebra.ofId c.O (Qbar l) : c.O →+* Qbar l) (ψ₀ v i) * ω v i)⁻¹
  have hχ : ∀ v i, Continuous (χ v i) := fun v i => ((du_cont c c.O _ _ (hψ₀ v i).cont).mul (hω v i)).inv
  refine e.symm.injective ?_
  rw [map_zero]
  refine du_box c (σ := Σ v, Fin n × Fin (d v)) (fun p => p.2.1) (fun p => χ p.1 p.2.1 (γ p.1 p.2.2))
    (fun p => (du_pow _ (hχ p.1 p.2.1)).imp fun M hM => ⟨hM.1, hM.2 _⟩) _ fun y η h1 h2 h3 => ?_
  let x : Λ.Λ →ₐ[c.O] Qbar l := y.comp e.symm.toAlgHom
  have hx : ∀ v i j, (Φ x v i (γ v j) : Qbar l) = η ⟨v, i, j⟩ := fun v i j => by
    have h4 := congrArg x (he v i j ⟨γ v j, hγI v j⟩ (hγ v j))
    have h5 : x (e (MvPowerSeries.X ⟨v, i, j⟩)) = y (MvPowerSeries.X ⟨v, i, j⟩) := congrArg y (e.symm_apply_apply _)
    rw [hκ, map_mul, map_add (f := _), map_one, x.commutes, h5, h3] at h4
    show x (ψ v i (γ v j)) * (ω v i (γ v j) : Qbar l) = _
    refine (congrArg (· * _) h4).trans ?_
    have h6 : (χ v i (γ v j) : Qbar l) = (algebraMap c.O (Qbar l) (ψ₀ v i (γ v j)) * ω v i (γ v j))⁻¹ :=
      Units.val_inv_eq_inv_val _
    have h7 : algebraMap c.O (Qbar l) (ψ₀ v i (γ v j)) * ω v i (γ v j) ≠ 0 := fun h => by
      rw [h, inv_zero] at h6
      exact Units.ne_zero _ h6
    simp only [h6]
    rw [mul_right_comm, mul_inv_cancel_left₀ h7]
  refine hf x ⟨trivial, ?_, fun v i j hij => ?_⟩
  · choose N hN hN' using fun v i => du_fin (A v) (Φ x v i) (hΦ x v i) (γ v) (hγ v) fun j => by
      rw [← Units.isOfFinOrder_val, hx]
      exact h1 _
    choose k hk using fun v i => du_arith (ha v) (Φ x v i) (hΦ x v i) (hN v i) (hN' v i)
    refine ⟨∑ v, ∑ i, k v i, fun v i z hz => ?_⟩
    obtain ⟨t, ht⟩ := (ha v).surj z.1
    refine (key x v i t z ht).trans ?_
    have h9 := hk v i _ ((Finset.single_le_sum (f := k v) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans
      (Finset.single_le_sum (f := fun v => ∑ i, k v i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ v))) t (ht ▸ hz)
    exact inv_eq_one.2 (congrArg Units.val h9)
  · let t : Weil (s.hw v.1) := ⟨(γ v ⟨0, hd v⟩).1, Ine_le_Weil _ (hγI v _)⟩
    let z : Uo ((s.w v.1).adicCompletion L) := ⟨_, (du_unit (ha v) t).2 (hγI v _)⟩
    refine ⟨z, fun h' => ?_⟩
    have h := inv_injective (((key x v i t z rfl).symm.trans h').trans (key x v j t z rfl))
    exact h2 ⟨v, i, ⟨0, hd v⟩⟩ ⟨v, j, ⟨0, hd v⟩⟩ hij (((hx v i _).symm.trans h).trans (hx v j _))
