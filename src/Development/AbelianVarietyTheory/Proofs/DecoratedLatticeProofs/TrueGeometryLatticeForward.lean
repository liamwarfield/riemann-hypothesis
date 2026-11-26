module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIdemSumLeft

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitFormUnitaryIntegralEntriesOfLevelLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitFormUnitaryIntegralEntriesOfLevelLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.UnitLevelInt

theorem entry_mem_of_levelVL : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), (∀ x, σ (σ x) = x) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), J = 1 → ∀ (t : 𝓞 E), (t : E) ≠ 0 → ∀ (Λ : Submodule (𝓞 E) (Fin n → E)), (∀ x, x ∈ Λ ↔ ∀ j : Fin n, ∃ r : 𝓞 E, x j = (r : E) ∧ (j.1 + 1 = n → t ∣ r)) → ∀ (v : HeightOneSpectrum (𝓞 F)) (g : GL (Fin n) (E ⊗[F] v.adicCompletion F)), g ∈ Formalism.UG.levelVL σ J v Λ → ∀ i j, g.1 i j ∈ Formalism.UG.tensInt (F := F) (v.adicCompletion F) (Formalism.UG.intOE E) (v.adicCompletionIntegers F).toSubring := by
  intro F E _ _ _ _ _ σ hσ n J hJ t ht Λ hΛ v g hg
  subst hJ
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · intro i; exact i.elim0
  haveI : NeZero n := ⟨by omega⟩
  have hlast : ∀ j : Fin n, j.1 + 1 = n ↔ j = Formalism.L2.Col.lastIdx n := by
    intro j
    constructor
    · intro h; ext; simp [Formalism.L2.Col.lastIdx]; omega
    · rintro rfl; simp [Formalism.L2.Col.lastIdx]; omega
  have hΛeq : Λ = Formalism.L2.Col.rll_dLat n ((t : E)⁻¹) := by
    ext x
    rw [hΛ, Formalism.L2.Col.rll_mem_dLat]
    constructor
    · intro h
      refine ⟨fun i hi => ?_, ?_⟩
      · obtain ⟨r, hr, -⟩ := h i
        exact ⟨r, hr.symm⟩
      · obtain ⟨r, hr, hd⟩ := h (Formalism.L2.Col.lastIdx n)
        obtain ⟨q, rfl⟩ := hd ((hlast _).2 rfl)
        refine ⟨q, ?_⟩
        rw [hr]
        show (q : E) = (t : E)⁻¹ * ((t * q : 𝓞 E) : E)
        rw [show ((t * q : 𝓞 E) : E) = (t : E) * q from rfl, inv_mul_cancel_left₀ ht]
    · rintro ⟨h1, q, hq⟩
      intro j
      by_cases hj : j = Formalism.L2.Col.lastIdx n
      · subst hj
        refine ⟨t * q, ?_, fun _ => dvd_mul_right t q⟩
        have hq' : (q : E) = (t : E)⁻¹ * x (Formalism.L2.Col.lastIdx n) := hq
        rw [show ((t * q : 𝓞 E) : E) = (t : E) * q from rfl, hq', mul_inv_cancel_left₀ ht]
      · obtain ⟨r, hr⟩ := h1 j hj
        exact ⟨r, hr.symm, fun h => absurd ((hlast j).1 h) hj⟩
  set S := Formalism.BasicNotions.intV E v with hSdef
  let ι := Formalism.UG.inclE (F := F) (E := E) (v.adicCompletion F)
  have hmem : ∀ z : Fin n → E ⊗[F] v.adicCompletion F,
      z ∈ Formalism.UG.latS (F := F) (v.adicCompletion F) S Λ ↔
        (∀ i, i ≠ Formalism.L2.Col.lastIdx n → z i ∈ S) ∧ ι (t : E)⁻¹ * z (Formalism.L2.Col.lastIdx n) ∈ S := by
    intro z
    rw [hΛeq]
    exact Formalism.L2.Col.rll_mem_loc_dLat (F := F) n v _ (inv_ne_zero ht) z
  have htS : ι (t : E) ∈ S := GlobalTheory.UnitLocLastRow.inclE_int v t
  have hcols : ∀ h : GL (Fin n) (E ⊗[F] v.adicCompletion F),
      h ∈ Formalism.UG.stabGL (Formalism.UG.latS (F := F) (v.adicCompletion F) S Λ) →
      ∀ i j, j ≠ Formalism.L2.Col.lastIdx n → (i ≠ Formalism.L2.Col.lastIdx n → h.1 i j ∈ S) ∧
        ι (t : E)⁻¹ * h.1 (Formalism.L2.Col.lastIdx n) j ∈ S := by
    intro h hh i j hj
    have he : (Pi.single j 1 : Fin n → E ⊗[F] v.adicCompletion F) ∈
        Formalism.UG.latS (F := F) (v.adicCompletion F) S Λ := by
      rw [hmem]
      refine ⟨fun k _ => ?_, ?_⟩
      · by_cases hk : k = j
        · subst hk; rw [Pi.single_eq_same]; exact one_mem _
        · rw [Pi.single_eq_of_ne hk]; exact zero_mem _
      · rw [Pi.single_eq_of_ne (Ne.symm hj), mul_zero]; exact zero_mem _
    have h2 := (hmem _).1 ((hh _).1 he)
    rw [Matrix.mulVec_single_one] at h2
    exact ⟨fun hi => h2.1 i hi, h2.2⟩
  have hlastcol : ∀ i, ι (t : E) * g.1 i (Formalism.L2.Col.lastIdx n) ∈ S ∧
      (i = Formalism.L2.Col.lastIdx n → g.1 i (Formalism.L2.Col.lastIdx n) ∈ S) := by
    intro i
    have he : (Pi.single (Formalism.L2.Col.lastIdx n) (ι (t : E)) : Fin n → E ⊗[F] v.adicCompletion F) ∈
        Formalism.UG.latS (F := F) (v.adicCompletion F) S Λ := by
      rw [hmem]
      refine ⟨fun k hk => ?_, ?_⟩
      · rw [Pi.single_eq_of_ne hk]; exact zero_mem _
      · rw [Pi.single_eq_same, ← map_mul, inv_mul_cancel₀ ht, map_one]; exact one_mem _
    have h2 := (hmem _).1 ((hg.2 _).1 he)
    have e : ∀ k, ((g.1 : Matrix (Fin n) (Fin n) _) *ᵥ
        (Pi.single (Formalism.L2.Col.lastIdx n) (ι (t : E)) : Fin n → E ⊗[F] v.adicCompletion F)) k =
          g.1 k (Formalism.L2.Col.lastIdx n) * ι (t : E) := by
      intro k
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    refine ⟨?_, fun hi => ?_⟩
    · by_cases hi : i = Formalism.L2.Col.lastIdx n
      · subst hi
        have := h2.2
        rw [e, mul_comm (g.1 _ _), ← mul_assoc, ← map_mul, inv_mul_cancel₀ ht, map_one, one_mul] at this
        exact mul_mem htS this
      · have := h2.1 i hi
        rw [e, mul_comm] at this
        exact this
    · subst hi
      have := h2.2
      rw [e, mul_comm (g.1 _ _), ← mul_assoc, ← map_mul, inv_mul_cancel₀ ht, map_one, one_mul] at this
      exact this

  have hU : Formalism.UG.cT (Formalism.UG.sigR σ (v.adicCompletion F)) g.1 * g.1 = 1 := by
    have h1 := hg.1
    change Formalism.UG.cT _ g.1 * ((1 : Matrix (Fin n) (Fin n) E).map ι) * g.1 = (1 : Matrix (Fin n) (Fin n) E).map ι at h1
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at h1
    exact h1
  have hinv : ((g⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) = Formalism.UG.cT (Formalism.UG.sigR σ (v.adicCompletion F)) g.1 :=
    Units.inv_eq_of_mul_eq_one_left hU
  have hginv := hcols g⁻¹ (inv_mem hg.2)
  intro i j
  by_cases hj : j = Formalism.L2.Col.lastIdx n
  · subst hj
    by_cases hi : i = Formalism.L2.Col.lastIdx n
    · exact (hlastcol i).2 hi
    · have h3 := (hginv (Formalism.L2.Col.lastIdx n) i hi).2
      rw [hinv] at h3
      change ι (t : E)⁻¹ * Formalism.UG.sigR σ (v.adicCompletion F) (g.1 i (Formalism.L2.Col.lastIdx n)) ∈ S at h3
      have h4 := GlobalTheory.UnitLocLastRow.sigR_mem_intV σ v h3
      rw [map_mul, GlobalTheory.UnitLocLastRow.sigR_sigR σ hσ, GlobalTheory.UnitLocLastRow.sigR_inclE] at h4
      have hs : ι (σ (t : E)) ∈ S := by
        have := GlobalTheory.UnitLocLastRow.sigR_mem_intV σ v htS
        rwa [GlobalTheory.UnitLocLastRow.sigR_inclE] at this
      have hst : σ (t : E) ≠ 0 := by
        intro h0; apply ht
        have := congrArg σ h0
        rwa [hσ, map_zero] at this
      have e : g.1 i (Formalism.L2.Col.lastIdx n) = ι (σ (t : E)) * (ι (σ (t : E)⁻¹) * g.1 i (Formalism.L2.Col.lastIdx n)) := by
        rw [← mul_assoc, ← map_mul, map_inv₀, mul_inv_cancel₀ hst, map_one, one_mul]
      rw [e]
      exact mul_mem hs h4
  · have h2 := hcols g hg.2 i j hj
    by_cases hi : i = Formalism.L2.Col.lastIdx n
    · subst hi
      have e : g.1 (Formalism.L2.Col.lastIdx n) j = ι (t : E) * (ι (t : E)⁻¹ * g.1 (Formalism.L2.Col.lastIdx n) j) := by
        rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ ht, map_one, one_mul]
      rw [e]; exact mul_mem htS h2.2
    · exact h2.1 hi

end GlobalTheory.UnitLevelInt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitFormUnitaryIntegralEntriesOfLevelLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitFormUnitary_integralEntries_of_levelLattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), (∀ x, σ (σ x) = x) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), J = 1 → ∀ (t : 𝓞 E), (t : E) ≠ 0 → ∀ (Λ : Submodule (𝓞 E) (Fin n → E)), (∀ x, x ∈ Λ ↔ ∀ j : Fin n, ∃ r : 𝓞 E, x j = (r : E) ∧ (j.1 + 1 = n → t ∣ r)) → ∀ (v : HeightOneSpectrum (𝓞 F)) (g : GL (Fin n) (E ⊗[F] v.adicCompletion F)), g ∈ Formalism.UG.levelVL σ J v Λ → ∀ i j, g.1 i j ∈ Formalism.UG.tensInt (F := F) (v.adicCompletion F) (Formalism.UG.intOE E) (v.adicCompletionIntegers F).toSubring := by
  first | exact @GlobalTheory.UnitLevelInt.entry_mem_of_levelVL | exact GlobalTheory.UnitLevelInt.entry_mem_of_levelVL | (intros; apply GlobalTheory.UnitLevelInt.entry_mem_of_levelVL <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentIntegralOfFiniteMatrixIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentIntegralOfFiniteMatrixIntegral
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinIntBridge

theorem comm_symm_mem {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) {a : E ⊗[F] v.adicCompletion F}
    (ha : a ∈ Formalism.UG.tensInt (F := F) (v.adicCompletion F) (Formalism.UG.intOE E) (v.adicCompletionIntegers F).toSubring) :
    (Algebra.TensorProduct.comm F (v.adicCompletion F) E).symm a ∈ GlobalTheory.AdelicU.intLoc F E v := by
  have hle : Formalism.UG.tensInt (F := F) (v.adicCompletion F) (Formalism.UG.intOE E) (v.adicCompletionIntegers F).toSubring ≤
      (GlobalTheory.AdelicU.intLoc F E v).comap
      ((Algebra.TensorProduct.comm F (v.adicCompletion F) E).symm : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F ⊗[F] E) := by
    unfold Formalism.UG.tensInt
    rw [Subring.closure_le]
    rintro z (⟨⟨e, he⟩, rfl⟩ | ⟨⟨b, hb⟩, rfl⟩)
    · obtain ⟨x, rfl⟩ := RingHom.mem_range.1 (show e ∈ (algebraMap (𝓞 E) E).range from he)
      simp only [SetLike.mem_coe, Subring.mem_comap, RingHom.coe_coe]
      simpa using GlobalTheory.AdelicU.tmul_mem_intLoc (E := E) (v := v) (one_mem _) x
    · simp only [SetLike.mem_coe, Subring.mem_comap, RingHom.coe_coe]
      simpa using GlobalTheory.AdelicU.tmul_mem_intLoc (E := E) (v := v) (a := b) hb 1
  exact hle ha

theorem prV_gen {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (y : AF F ⊗[F] E) :
    (Algebra.TensorProduct.comm F (v.adicCompletion F) E).symm (Formalism.UG.prV (E := E) v
      (Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) y))) =
      Algebra.TensorProduct.map (GlobalTheory.AdelicU.evFin F v) (AlgHom.id F E) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem mem_intLoc_of_finM : ∀ (D : D7) (V : HSp D) (n : ℕ) (hn : V.rank = n) (κ : GA D V) (x : GL (Fin n) (GlobalTheory.AdForm.EF D)), GlobalTheory.AdForm.finM V hn κ = x.1 → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)), (∀ i j, (Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) x).1 i j ∈ Formalism.UG.tensInt (F := D.host.F) (v.adicCompletion D.host.F) (Formalism.UG.intOE D.host.E) (v.adicCompletionIntegers D.host.F).toSubring) → ∀ i j, (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig V.gram (GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v κ)).1 i j ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v := by
  intro D V n hn κ x hx v h i j
  have h1 := comm_symm_mem v (h (finCongr hn i) (finCongr hn j))
  have h2 : (Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) x).1 (finCongr hn i) (finCongr hn j) =
      Formalism.UG.prV (E := D.host.E) v (toEAf D (Formalism.L2.Theta.mt V κ i j)) := by
    change Formalism.UG.prV (E := D.host.E) v (x.1 (finCongr hn i) (finCongr hn j)) = _
    rw [← hx]
    simp only [GlobalTheory.AdForm.finM, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.map_apply, Equiv.symm_apply_apply]
  rw [h2] at h1
  have h3 := prV_gen (F := D.host.F) (E := D.host.E) v (Formalism.L2.Theta.mt V κ i j)
  exact (congrArg (· ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v) h3).mp h1

end GlobalTheory.FinIntBridge
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentIntegralOfFiniteMatrixIntegralStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localComponent_integral_of_finiteMatrix_integral : ∀ (D : D7) (V : HSp D) (n : ℕ) (hn : V.rank = n) (κ : GA D V) (x : GL (Fin n) (GlobalTheory.AdForm.EF D)), GlobalTheory.AdForm.finM V hn κ = x.1 → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)), (∀ i j, (Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) x).1 i j ∈ Formalism.UG.tensInt (F := D.host.F) (v.adicCompletion D.host.F) (Formalism.UG.intOE D.host.E) (v.adicCompletionIntegers D.host.F).toSubring) → ∀ i j, (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig V.gram (GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v κ)).1 i j ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v := by
  first | exact @GlobalTheory.FinIntBridge.mem_intLoc_of_finM | exact GlobalTheory.FinIntBridge.mem_intLoc_of_finM | (intros; apply GlobalTheory.FinIntBridge.mem_intLoc_of_finM <;> assumption)
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FamTrace.LatFwd

theorem finM_inv_eq {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) (κ : GA D V) (x : GL (Fin n) (GlobalTheory.AdForm.EF D))
    (h : GlobalTheory.AdForm.finM V hn κ = x.1) : GlobalTheory.AdForm.finM V hn κ⁻¹ = (x⁻¹).1 := by
  subst hn
  have e : GlobalTheory.AdForm.finM V rfl κ * GlobalTheory.AdForm.finM V rfl κ⁻¹ = 1 := by
    have e1 : ∀ g, GlobalTheory.AdForm.finM V rfl g = (mt V g).map (toEAf D) := fun g => rfl
    have e2 : mt V κ * mt V κ⁻¹ = 1 := by
      simp only [Formalism.L2.Theta.mt]
      rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
    rw [e1, e1, ← Matrix.map_mul, e2]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  rw [h] at e
  exact (Units.inv_eq_of_mul_eq_one_right e).symm

theorem proj_mem_stabLoc_std {D : D7} (V : HSp D) (g : GA D V) (v : HeightOneSpectrum (𝓞 D.host.F))
    (hM : ∀ i j, (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig V.gram (GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g)).1 i j ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v)
    (hM' : ∀ i j, (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig V.gram (GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g⁻¹)).1 i j ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v) :
    GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram (GlobalTheory.AdelicU.stdLattice D.host.E V.rank) v := by
  rw [map_inv, map_inv] at hM'
  set M := GlobalTheory.AdelicU.matHom _ D.sp.cm.sig V.gram (GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g)
  have hint : ∀ (N : Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v ⊗[D.host.F] D.host.E)),
      (∀ i j, N i j ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v) → ∀ z : Fin V.rank → Fv D.host.F v ⊗[D.host.F] D.host.E,
      (∀ i, z i ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v) → ∀ i, (N *ᵥ z) i ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v :=
    fun N hN z hz i => by
      simp only [Matrix.mulVec, dotProduct]
      exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hN i j) (hz j)
  refine GlobalTheory.AdelicU.mem_stabLoc.2 fun z => ?_
  simp only [GlobalTheory.AdelicU.mem_latLoc_stdLattice]
  refine ⟨fun hz => hint _ hM z hz, fun hz => ?_⟩
  have e : (M⁻¹).1 *ᵥ (M.1 *ᵥ z) = z := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  rw [← e]
  exact hint _ hM' _ hz

end GlobalTheory.FamTrace.LatFwd

namespace GlobalTheory.FamTrace.LatFwd


end GlobalTheory.FamTrace.LatFwd

end
