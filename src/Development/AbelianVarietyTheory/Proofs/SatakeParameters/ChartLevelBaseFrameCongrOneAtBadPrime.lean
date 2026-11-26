module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalisationEqStdAtOfCongruentOneAtPrime
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GlobLatCompanOfLev

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartBaseFrameBadPrimeEqCompanionLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompanionLatticeAdelicLatticeLocalizationEq
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompanionLatticeAdelicLatticeLocalizationEq
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanLatAd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem full_span {n : ℕ} (M : Submodule (𝓞 E) (Fin n → E))
    (hM : Submodule.IsFullLattice E M) : Submodule.span E (M : Set (Fin n → E)) = ⊤ := by
  letI := hM
  exact Submodule.IsFullLattice.span_eq_top

theorem dualL_fg {n : ℕ} (τ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (hJ : IsUnit J.det)
    (M : Submodule (𝓞 E) (Fin n → E)) (hM : Submodule.IsFullLattice E M) : (dualL τ J M).FG := by
  classical
  obtain ⟨S, hS⟩ := hM.fg
  have hSE : Submodule.span E ((S : Set (Fin n → E))) = ⊤ := by
    rw [← Submodule.span_span_of_tower (𝓞 E) E, hS]
    exact full_span M hM
  let Θ : (Fin n → E) →ₗ[𝓞 E] (S → E) :=
    { toFun := fun y s => hform τ J s.1 y
      map_add' := fun y y' => by
        funext s
        simp only [hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun r y => by
        funext s
        simp only [RingHom.id_apply, Pi.smul_apply]
        rw [show r • y = (r : E) • y from (algebraMap_smul E r y).symm, GlobalTheory.LevelHecke.DualConj.hform_smul_right,
          Algebra.smul_def] }
  have hΘ : Function.Injective Θ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have h0 : ∀ x ∈ Submodule.span E (S : Set (Fin n → E)), hform τ J x y = 0 := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx => exact congrFun hy ⟨x, hx⟩
      | zero => simp [hform]
      | add x x' _ _ hx hx' =>
        have e : hform τ J (x + x') y = hform τ J x y + hform τ J x' y := by
          simp only [hform, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]
        rw [e, hx, hx', add_zero]
      | smul c x _ hx => rw [GlobalTheory.LevelHecke.DualConj.hform_smul_left, hx, mul_zero]
    have hJy : J *ᵥ y = 0 := by
      funext i
      have := h0 (Pi.single i 1) (by rw [hSE]; trivial)
      show (J *ᵥ y) i = 0
      rw [← this]
      simp [hform, Pi.single_apply, Matrix.mulVec, dotProduct]
    have : y = J⁻¹ *ᵥ (J *ᵥ y) := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul J hJ, Matrix.one_mulVec]
    rw [this, hJy, Matrix.mulVec_zero]
  let P : Submodule (𝓞 E) (S → E) := LinearMap.range
    (LinearMap.pi fun s : S => (Algebra.linearMap (𝓞 E) E).comp (LinearMap.proj s) : (S → 𝓞 E) →ₗ[𝓞 E] (S → E))
  have hP : P.FG := by
    show (LinearMap.range _).FG
    rw [← Submodule.map_top]
    exact Module.Finite.fg_top.map _
  haveI := isNoetherian_of_fg_of_noetherian _ hP
  refine Submodule.fg_of_fg_map_injective Θ hΘ (Submodule.FG.of_le_of_isNoetherian (T := P) ?_)
  rintro _ ⟨y, hy, rfl⟩
  have hy' := (GlobalTheory.LevelHecke.DualConj.mem_dualL τ J M y).1 hy
  choose f hf using fun s : S => hy' s.1 (hS ▸ Submodule.subset_span s.2)
  refine ⟨f, ?_⟩
  funext s
  exact hf s

end GlobalTheory.CompanLatAd

namespace GlobalTheory.CompanLatAd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mem_latS_sup_smul_iff (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (M N : Submodule (𝓞 E) (Fin n → E)) (a : 𝓞 E)
    (z : Fin n → E ⊗[F] v.adicCompletion F) :
    z ∈ latS (F := F) (v.adicCompletion F) (intV E v) (M ⊔ Ideal.span {a} • N) ↔
      ∃ m ∈ latS (F := F) (v.adicCompletion F) (intV E v) M, ∃ w ∈ latS (F := F) (v.adicCompletion F) (intV E v) N,
        z = m + inclE (F := F) (v.adicCompletion F) (a : E) • w := by
  set c := inclE (F := F) (v.adicCompletion F) (a : E) with hc
  have hincl : ∀ y y' : Fin n → E, (fun i => inclE (F := F) (v.adicCompletion F) ((y + y') i)) =
      (fun i => inclE (F := F) (v.adicCompletion F) (y i)) + fun i => inclE (F := F) (v.adicCompletion F) (y' i) := by
    intro y y'; funext i; simp
  have hsm : ∀ y : Fin n → E, (fun i => inclE (F := F) (v.adicCompletion F) ((a • y) i)) =
      c • fun i => inclE (F := F) (v.adicCompletion F) (y i) := by
    intro y; funext i
    simp only [Pi.smul_apply, smul_eq_mul, hc, ← map_mul]
    rw [Algebra.smul_def]
  have hcw : ∀ w ∈ latS (F := F) (v.adicCompletion F) (intV E v) N,
      c • w ∈ latS (F := F) (v.adicCompletion F) (intV E v) (Ideal.span {a} • N) := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨y, hy, rfl⟩ := hw
      rw [← hsm]
      exact Submodule.subset_span ⟨a • y, Submodule.smul_mem_smul (Ideal.mem_span_singleton_self a) hy, rfl⟩
    | zero => rw [smul_zero]; exact zero_mem _
    | add w w' _ _ hw hw' => rw [smul_add]; exact add_mem hw hw'
    | smul s w _ hw =>
      rw [Subring.smul_def, smul_comm]
      exact Submodule.smul_mem _ s hw
  constructor
  · intro hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨y, hy, rfl⟩ := hz
      obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.1 hy
      rw [Submodule.ideal_span_singleton_smul] at hq
      obtain ⟨q', hq', rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hq
      exact ⟨_, Submodule.subset_span ⟨p, hp, rfl⟩, _, Submodule.subset_span ⟨q', hq', rfl⟩, by
        show (fun i => inclE (F := F) (v.adicCompletion F) ((p + a • q') i)) = _
        rw [hincl, hsm]⟩
    | zero => exact ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
    | add z z' _ _ hz hz' =>
      obtain ⟨m, hm, w, hw, rfl⟩ := hz
      obtain ⟨m', hm', w', hw', rfl⟩ := hz'
      exact ⟨m + m', add_mem hm hm', w + w', add_mem hw hw', by rw [smul_add]; abel⟩
    | smul s z _ hz =>
      obtain ⟨m, hm, w, hw, rfl⟩ := hz
      refine ⟨s • m, Submodule.smul_mem _ s hm, s • w, Submodule.smul_mem _ s hw, ?_⟩
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, Subring.smul_def, smul_eq_mul]
      ring
  · rintro ⟨m, hm, w, hw, rfl⟩
    have h1 : (M : Set (Fin n → E)) ⊆ ((M ⊔ Ideal.span {a} • N : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) :=
      SetLike.coe_subset_coe.2 le_sup_left
    have h2 : ((Ideal.span {a} • N : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) ⊆
        ((M ⊔ Ideal.span {a} • N : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) :=
      SetLike.coe_subset_coe.2 le_sup_right
    exact add_mem (Submodule.span_mono (Set.image_mono h1) hm) (Submodule.span_mono (Set.image_mono h2) (hcw w hw))

end GlobalTheory.CompanLatAd

namespace GlobalTheory.CompanLatAd

theorem isLattice_compan {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (sp : Spaces R F E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (hJ : IsUnit J.det) (a : 𝓞 E)
    (M : Submodule (𝓞 E) (Fin N → E)) (hM : Submodule.IsFullLattice E M) :
    Submodule.IsFullLattice E (compan (sp := sp) J a M) := by
  have hfg : (compan (sp := sp) J a M).FG :=
    hM.fg.sup (Submodule.FG.smul (IsNoetherian.noetherian (Ideal.span {a}))
      (dualL_fg (sp.cm.sig : E →+* E) J hJ M hM))
  refine { toIsLattice := Submodule.IsLattice.of_fg E hfg, span_eq_top := ?_ }
  apply top_unique
  rw [← full_span M hM]
  apply Submodule.span_mono
  exact SetLike.coe_subset_coe.mpr le_sup_left
theorem compan_latAd_eq {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (sp : Spaces R F E) {N : ℕ} (σ : E →ₐ[F] E) (hσ : (σ : E →+* E) = sp.cm.sig) (J : Matrix (Fin N) (Fin N) E)
    (hJ : IsUnit J.det) (a : 𝓞 E) (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (hx : x ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)) (Lb : Submodule (𝓞 E) (Fin N → E)) (hfg : Lb.FG)
    (hspan : Submodule.span E (Lb : Set (Fin N → E)) = ⊤) :
    compan (sp := sp) J a (latAd x Lb) = latAd x (compan (sp := sp) J a Lb) := by
  have hcomp : ∀ M : Submodule (𝓞 E) (Fin N → E),
      compan (sp := sp) J a M = M ⊔ Ideal.span {a} • dualL (σ : E →+* E) J M := by
    intro M
    unfold compan dualL
    rw [hσ]
  have hLb : Submodule.IsFullLattice E Lb :=
    { toIsLattice := Submodule.IsLattice.of_fg E hfg, span_eq_top := hspan }
  have hfin : Module.Finite (𝓞 E) Lb := Module.Finite.iff_fg.mpr hfg
  have hlatAd : ∀ M : Submodule (𝓞 E) (Fin N → E), Submodule.IsFullLattice E M → Submodule.IsFullLattice E (latAd x M) := by
    intro M hM
    have e : latAd x M = Formalism.UG.CS.globLat x M := Submodule.span_eq (Formalism.UG.CS.globLat x M)
    rw [e]
    exact Formalism.UG.P.csGlob_lattice M (Module.Finite.iff_fg.mpr hM.fg) (full_span M hM) x
  have hΛ := hlatAd Lb hLb
  have hcL := isLattice_compan sp J hJ a Lb hLb
  have hcΛ := isLattice_compan sp J hJ a (latAd x Lb) hΛ
  have hRHS := hlatAd _ hcL
  have key : ∀ (v : HeightOneSpectrum (𝓞 F)) (z : Fin N → E ⊗[F] v.adicCompletion F),
      z ∈ latS (F := F) (v.adicCompletion F) (intV E v) (compan (sp := sp) J a (latAd x Lb)) ↔
        z ∈ latS (F := F) (v.adicCompletion F) (intV E v) (latAd x (compan (sp := sp) J a Lb)) := by
    intro v z
    set g := bc (prV (E := E) v) x with hg
    have hgU : g ∈ UPts σ J (v.adicCompletion F) := GlobalTheory.MemDual.bc_prV_mem_UPts σ J v hx
    have hcar1 := GlobalTheory.LocCarry.mem_latS_latAd_iff x Lb hfin hspan v
    have hcar2 := GlobalTheory.LocCarry.mem_latS_latAd_iff x (compan (sp := sp) J a Lb)
      (Module.Finite.iff_fg.mpr hcL.fg) (full_span _ hcL) v
    have hdm := GlobalTheory.DualCompletion.dual_move F E σ N J v (latAd x Lb) Lb g hJ hΛ hLb hgU hcar1
    have hgg : ∀ w : Fin N → E ⊗[F] v.adicCompletion F, ((g⁻¹ : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) *ᵥ
        ((g : Matrix (Fin N) (Fin N) _) *ᵥ w) = w := by
      intro w
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    have hgg' : ∀ w : Fin N → E ⊗[F] v.adicCompletion F, (g : Matrix (Fin N) (Fin N) _) *ᵥ
        (((g⁻¹ : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) *ᵥ w) = w := by
      intro w
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    rw [hcar2, hcomp, hcomp, mem_latS_sup_smul_iff, mem_latS_sup_smul_iff]
    constructor
    · rintro ⟨m, hm, w, hw, rfl⟩
      exact ⟨_, (hcar1 m).1 hm, _, (hdm w).1 hw, by rw [Matrix.mulVec_add, Matrix.mulVec_smul]⟩
    · rintro ⟨m, hm, w, hw, he⟩
      refine ⟨(g : Matrix (Fin N) (Fin N) _) *ᵥ m, (hcar1 _).2 (by rw [hgg]; exact hm),
        (g : Matrix (Fin N) (Fin N) _) *ᵥ w, (hdm _).2 (by rw [hgg]; exact hw), ?_⟩
      rw [← Matrix.mulVec_smul, ← Matrix.mulVec_add, ← he, hgg']
  apply le_antisymm
  · intro w hw
    refine GlobalTheory.LatLocGlob.mem_of_forall_locLat (F := F) _ (Module.Finite.iff_fg.mpr hRHS.fg) (full_span _ hRHS) w fun v => ?_
    exact (key v _).1 (Submodule.subset_span ⟨w, hw, rfl⟩)
  · intro w hw
    refine GlobalTheory.LatLocGlob.mem_of_forall_locLat (F := F) _ (Module.Finite.iff_fg.mpr hcΛ.fg) (full_span _ hcΛ) w fun v => ?_
    exact (key v _).2 (Submodule.subset_span ⟨w, hw, rfl⟩)

theorem locP_companion_latAd : ∀ {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (sp : Spaces R F E) {N : ℕ} (σ : E →ₐ[F] E), (σ : E →+* E) = sp.cm.sig → ∀ (J : Matrix (Fin N) (Fin N) E), IsUnit J.det → ∀ (a : 𝓞 E) (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)), x ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) → ∀ (Lb : Submodule (𝓞 E) (Fin N → E)), Lb.FG → Submodule.span E (Lb : Set (Fin N → E)) = ⊤ → ∀ (P : HeightOneSpectrum (𝓞 E)), Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (compan (sp := sp) J a (latAd x Lb)) = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (latAd x (compan (sp := sp) J a Lb)) := by
  intro R F E _ _ _ _ _ _ sp N σ hσ J hJ a x hx Lb hfg hspan P
  rw [compan_latAd_eq sp σ hσ J hJ a x hx Lb hfg hspan]

end GlobalTheory.CompanLatAd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompanionLatticeAdelicLatticeLocalizationEqStatement
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.companionLattice_adelicLattice_localization_eq : ∀ {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (sp : Spaces R F E) {N : ℕ} (σ : E →ₐ[F] E), (σ : E →+* E) = sp.cm.sig → ∀ (J : Matrix (Fin N) (Fin N) E), IsUnit J.det → ∀ (a : 𝓞 E) (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)), x ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) → ∀ (Lb : Submodule (𝓞 E) (Fin N → E)), Lb.FG → Submodule.span E (Lb : Set (Fin N → E)) = ⊤ → ∀ (P : HeightOneSpectrum (𝓞 E)), Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (compan (sp := sp) J a (latAd x Lb)) = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (latAd x (compan (sp := sp) J a Lb)) := by
  first | exact @GlobalTheory.CompanLatAd.locP_companion_latAd | exact GlobalTheory.CompanLatAd.locP_companion_latAd | (intros; apply GlobalTheory.CompanLatAd.locP_companion_latAd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalisationEqStdAtOfCongruentOneAtPrimeStatement
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localisation_eq_stdAt_of_congruentOne_atPrime : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {N : ℕ} (P : HeightOneSpectrum (𝓞 E)) (d : ℕ), 1 ≤ d → ∀ (y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (R : GL (Fin N) E) (M : Submodule (𝓞 E) (Fin N → E)), M.FG → Submodule.span E (M : Set (Fin N → E)) = ⊤ → CongAt (F := F) P d (y⁻¹ * ratA F R) → Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (latAd y M) = mvL R (stdAt E N P) → Formalism.HermitianLatticesTheory.localization₂ P.asIdeal M = stdAt E N P := by
  first | exact @GlobalTheory.CongStdLoc.localization_eq_stdAt_of_congAt | exact GlobalTheory.CongStdLoc.localization_eq_stdAt_of_congAt | (intros; apply GlobalTheory.CongStdLoc.localization_eq_stdAt_of_congAt <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompanionHermitianLatticeFg
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ImportsRest
namespace GlobalTheory.ExistsSmulMem

theorem exists_smul_mem {E : Type} [inst : Field E] [NumberField E] {N : ℕ}
    (Lb : Submodule (NumberField.RingOfIntegers E) (Fin N → E))
    (h : Submodule.span E (↑Lb : Set (Fin N → E)) = ⊤) (v : Fin N → E) :
    ∃ (c : NumberField.RingOfIntegers E), c ≠ (0 : NumberField.RingOfIntegers E) ∧ c • v ∈ Lb := by
  have hv : v ∈ Submodule.span E (↑Lb : Set (Fin N → E)) := h ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine Lb.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact Lb.smul_mem _ hax
    · rw [mul_smul]; exact Lb.smul_mem _ hby
  | smul r x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := NumberField.RingOfIntegers E) r
    have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
    have hq1 : algebraMap (NumberField.RingOfIntegers E) E q ≠ 0 := by
      intro h0
      exact hq0 (FaithfulSMul.algebraMap_injective (NumberField.RingOfIntegers E) E
        (by rw [h0, map_zero]))
    refine ⟨q * a, mul_ne_zero hq0 ha, ?_⟩
    have key : (q * a) • ((algebraMap (NumberField.RingOfIntegers E) E p /
        algebraMap (NumberField.RingOfIntegers E) E q) • x) = p • (a • x) := by
      rw [← algebraMap_smul E (q * a), ← algebraMap_smul E p, ← algebraMap_smul E a,
        smul_smul, smul_smul, map_mul]
      congr 1
      field_simp
    rw [key]
    exact Lb.smul_mem _ hax

end GlobalTheory.ExistsSmulMem
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompanionHermitianLatticeFg
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

namespace GlobalTheory.CompanFG

theorem fg_of_le_fg {R M : Type*} [CommRing R] [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    {P Q : Submodule R M} (hQ : Q.FG) (hPQ : P ≤ Q) : P.FG := by
  haveI := isNoetherian_of_fg_of_noetherian Q hQ
  have h1 : (P.comap Q.subtype).FG := IsNoetherian.noetherian _
  have h2 := h1.map Q.subtype
  rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hPQ] at h2

theorem exists_smul_mem {E : Type} [Field E] [NumberField E] {N : ℕ} (Lb : Submodule (𝓞 E) (Fin N → E))
    (hsp : Submodule.span E (Lb : Set (Fin N → E)) = ⊤) (v : Fin N → E) :
    ∃ c : 𝓞 E, c ≠ 0 ∧ c • v ∈ Lb := by
  first
  | exact @_root_.GlobalTheory.ExistsSmulMem.exists_smul_mem
  | exact _root_.GlobalTheory.ExistsSmulMem.exists_smul_mem
  | (apply _root_.GlobalTheory.ExistsSmulMem.exists_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.ExistsSmulMem.exists_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ExistsSmulMem.exists_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ExistsSmulMem.exists_smul_mem ..)

theorem hform_single {E : Type} [Field E] {N : ℕ} (σ : E →+* E) (J : Matrix (Fin N) (Fin N) E)
    (c : E) (i : Fin N) (y : Fin N → E) :
    hform σ J (c • Pi.single i 1) y = σ c * (J *ᵥ y) i := by
  simp [hform, Pi.single_apply, mulVec, dotProduct, Finset.mul_sum, mul_assoc, apply_ite σ, ite_mul]

theorem dualSet_le_fg {E : Type} [Field E] [NumberField E] {N : ℕ} (σ : E →+* E)
    (J : Matrix (Fin N) (Fin N) E) (hJ : IsUnit J.det) (Lb : Submodule (𝓞 E) (Fin N → E))
    (hsp : Submodule.span E (Lb : Set (Fin N → E)) = ⊤) :
    ∃ M : Submodule (𝓞 E) (Fin N → E), M.FG ∧ dualSet σ J Lb ⊆ M := by
  choose c hc0 hcm using fun i : Fin N => exists_smul_mem Lb hsp (Pi.single i 1)
  refine ⟨Submodule.span (𝓞 E) (Set.range fun i => (σ (c i : E))⁻¹ • (J⁻¹ *ᵥ Pi.single i 1)),
    Submodule.fg_span (Set.finite_range _), ?_⟩
  intro y hy
  have hint : ∀ i, ∃ w : 𝓞 E, (w : E) = σ (c i : E) * (J *ᵥ y) i := by
    intro i
    have h := hy _ (hcm i)
    rw [← algebraMap_smul E (c i), hform_single] at h
    obtain ⟨w, hw⟩ := h
    exact ⟨w, hw⟩
  choose w hw using hint
  have hσ : ∀ i, σ (c i : E) ≠ 0 := fun i => by
    rw [map_ne_zero]
    exact_mod_cast hc0 i
  have hy' : y = ∑ i, w i • ((σ (c i : E))⁻¹ • (J⁻¹ *ᵥ Pi.single i 1)) := by
    have e1 : y = J⁻¹ *ᵥ (J *ᵥ y) := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul J hJ, Matrix.one_mulVec]
    conv_lhs => rw [e1, ← Finset.univ_sum_single (J *ᵥ y)]
    rw [Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← algebraMap_smul E (w i), smul_smul, ← Matrix.mulVec_smul]
    congr 1
    ext k
    simp only [Pi.single_apply, Pi.smul_apply, smul_eq_mul]
    split_ifs
    · subst_vars
      show (J *ᵥ y) k = (algebraMap (𝓞 E) E (w k)) * (σ (c k : E))⁻¹ * 1
      rw [show algebraMap (𝓞 E) E (w k) = (w k : E) from rfl, hw k]
      field_simp [hσ k]
    · simp
  rw [hy']
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end GlobalTheory.CompanFG

namespace GlobalTheory


open GlobalTheory.CompanFG in
theorem compan_fg {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (sp : Spaces R F E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (hJ : IsUnit J.det) (a : 𝓞 E)
    (Lb : Submodule (𝓞 E) (Fin N → E)) (hfg : Lb.FG) (hsp : Submodule.span E (Lb : Set (Fin N → E)) = ⊤) :
    (compan (sp := sp) J a Lb).FG := by
  obtain ⟨M, hM, hle⟩ := dualSet_le_fg (sp.cm.sig : E →+* E) J hJ Lb hsp
  have h1 : (Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) J Lb)).FG :=
    fg_of_le_fg hM (Submodule.span_le.mpr hle)
  exact hfg.sup (fg_of_le_fg h1 Submodule.smul_le_right)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompanionHermitianLatticeFgStatement
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.companionHermitianLattice_fg : ∀ {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (sp : Spaces R F E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E), IsUnit J.det → ∀ (a : 𝓞 E) (Lb : Submodule (𝓞 E) (Fin N → E)), Lb.FG → Submodule.span E (Lb : Set (Fin N → E)) = ⊤ → (compan (sp := sp) J a Lb).FG := by
  first | exact @GlobalTheory.compan_fg | exact GlobalTheory.compan_fg | (intros; apply GlobalTheory.compan_fg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TransportedFrameStandardLocalEqLocalization
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TransportedFrameStandardLocalEqLocalization
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.FrameLat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def seamVec {D : D7} {X : Fields} (s : Seam D X) (n : ℕ) :
    Sp X.E n →ₛₗ[(RingOfIntegers.mapRingEquiv s.iE : 𝓞 X.E →+* 𝓞 D.host.E)] (Fin n → D.host.E) where
  toFun x l := s.iE (x l)
  map_add' x y := by funext l; simp
  map_smul' r x := by
    funext l
    simp only [Pi.smul_apply, Algebra.smul_def, map_mul]
    rfl

theorem seamVec_apply {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} (x : Sp X.E n) (l : Fin n) :
    seamVec s n x l = s.iE (x l) := rfl

theorem seamVec_injective {D : D7} {X : Fields} (s : Seam D X) (n : ℕ) : Function.Injective (seamVec s n) := by
  intro x y hxy
  funext l
  exact s.iE.injective (congrFun hxy l)

theorem seam_lat_eq_map {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} (M : Submodule (𝓞 X.E) (Sp X.E n)) :
    s.lat M = M.map (seamVec s n) := by
  unfold Seam.lat
  rw [show ((fun (x : Sp X.E n) (i : Fin n) => s.iE (x i)) '' (M : Set (Sp X.E n))) = seamVec s n '' M from rfl,
    ← Submodule.map_coe]
  exact Submodule.span_eq _

theorem localization_map_seamVec {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} (P : HeightOneSpectrum (𝓞 X.E))
    (M : Submodule (𝓞 X.E) (Sp X.E n)) :
    Formalism.HermitianLatticesTheory.localization₂ (seamP s P).asIdeal (M.map (seamVec s n)) = (Formalism.HermitianLatticesTheory.localization₂ P.asIdeal M).map (seamVec s n) := by
  set ψ : 𝓞 X.E ≃+* 𝓞 D.host.E := RingOfIntegers.mapRingEquiv s.iE with hψ
  ext x
  constructor
  · rintro ⟨r, hr, z, hz, hzx⟩
    have hfy : seamVec s n (fun l => s.iE.symm (x l)) = x := by
      funext l
      simp [seamVec_apply]
    refine ⟨fun l => s.iE.symm (x l), ⟨ψ.symm r, ?_, ?_⟩, hfy⟩
    · intro hm
      apply hr
      have := (mem_seamP s P (ψ.symm r)).2 hm
      simpa [ψ] using this
    · have : ψ.symm r • (fun l => s.iE.symm (x l)) = z := by
        apply seamVec_injective s n
        rw [(seamVec s n).map_smulₛₗ, hfy, hzx]
        show ψ (ψ.symm r) • x = r • x
        rw [RingEquiv.apply_symm_apply]
      rw [this]
      exact hz
  · rintro ⟨y, ⟨r, hr, hy⟩, rfl⟩
    refine ⟨ψ r, ?_, r • y, hy, ?_⟩
    · intro hm
      exact hr ((mem_seamP s P r).1 hm)
    · rw [(seamVec s n).map_smulₛₗ]
      rfl

theorem stdLat_map_seamVec {D : D7} {X : Fields} (s : Seam D X) (n : ℕ) :
    (stdLat X.E n).map (seamVec s n) = stdLat D.host.E n := by
  ext y
  rw [Submodule.mem_map]
  unfold Formalism.L2.Col.stdLat
  simp only [Submodule.mem_pi, Set.mem_univ, true_implies]
  constructor
  · rintro ⟨x, hx, rfl⟩ l
    obtain ⟨r, hr⟩ := (Submodule.mem_one).1 (hx l)
    refine (Submodule.mem_one).2 ⟨RingOfIntegers.mapRingEquiv s.iE r, ?_⟩
    rw [seamVec_apply, ← hr]
    rfl
  · intro hy
    refine ⟨fun l => s.iE.symm (y l), fun l => ?_, ?_⟩
    · obtain ⟨r, hr⟩ := (Submodule.mem_one).1 (hy l)
      refine (Submodule.mem_one).2 ⟨(RingOfIntegers.mapRingEquiv s.iE).symm r, ?_⟩
      show _ = s.iE.symm (y l)
      rw [← hr]
      rfl
    · funext l
      simp [seamVec_apply]

theorem mvL_seamGL_map {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} (g : Sp X.E n ≃ₗ[X.E] Sp X.E n)
    (M : Submodule (𝓞 X.E) (Sp X.E n)) :
    mvL (seamGL s g) (M.map (seamVec s n)) = (M.map (g.toLinearMap.restrictScalars (𝓞 X.E))).map (seamVec s n) := by
  unfold mvL
  ext y
  simp only [Submodule.mem_map]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨g x, ⟨x, hx, rfl⟩, ?_⟩
    show seamVec s n (g x) = toLE (seamGL s g) (seamVec s n x)
    rw [toLE_apply]
    exact (seamGL_mulVec s g x).symm
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨seamVec s n x, ⟨x, hx, rfl⟩, ?_⟩
    show toLE (seamGL s g) (seamVec s n x) = seamVec s n (g x)
    rw [toLE_apply]
    exact seamGL_mulVec s g x

theorem seamGL_stdAt : ∀ {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} (P : HeightOneSpectrum (𝓞 X.E)) (g : Sp X.E n ≃ₗ[X.E] Sp X.E n)
    (N : Submodule (𝓞 X.E) (Sp X.E n)), (∀ x, g x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N ↔ x ∈ stdAt X.E n P) →
    mvL (seamGL s g) (stdAt D.host.E n (seamP s P)) = Formalism.HermitianLatticesTheory.localization₂ (seamP s P).asIdeal (s.lat N) := by
  intro D X s n P g N hg
  have hstd : (stdAt X.E n P).map (g.toLinearMap.restrictScalars (𝓞 X.E)) = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N := by
    ext y
    simp only [Submodule.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hg x).2 hx
    · intro hy
      refine ⟨g.symm y, (hg _).1 (by simpa using hy), by simp⟩
  show mvL (seamGL s g) (Formalism.HermitianLatticesTheory.localization₂ (seamP s P).asIdeal (stdLat D.host.E n)) = _
  rw [← stdLat_map_seamVec s n, localization_map_seamVec, mvL_seamGL_map, ← stdAt, hstd, seam_lat_eq_map, localization_map_seamVec]

end GlobalTheory.FrameLat

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TransportedFrameStandardLocalEqLocalizationStatement
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transportedFrame_standardLocal_eq_localization : ∀ {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} (P : HeightOneSpectrum (𝓞 X.E)) (g : Sp X.E n ≃ₗ[X.E] Sp X.E n) (N : Submodule (𝓞 X.E) (Sp X.E n)), (∀ x, g x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N ↔ x ∈ stdAt X.E n P) → mvL (seamGL s g) (stdAt D.host.E n (seamP s P)) = Formalism.HermitianLatticesTheory.localization₂ (seamP s P).asIdeal (s.lat N) := by
  first | exact @GlobalTheory.FrameLat.seamGL_stdAt | exact GlobalTheory.FrameLat.seamGL_stdAt | (intros; apply GlobalTheory.FrameLat.seamGL_stdAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicPointLatticeMulRationalGL
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicPointLatticeMulRationalGL
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TwV

theorem mulVec_mem_hatL_mvL {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    {N : ℕ} (h : GL (Fin N) E) (M : Submodule (𝓞 E) (Fin N → E))
    (w : Fin N → E ⊗[F] FiniteAdeleRing (𝓞 F) F) (hw : w ∈ Formalism.L2.Herm.hatL (F := F) M) :
    ((ratA F h : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ w ∈
      Formalism.L2.Herm.hatL (F := F) (mvL h M) := by
  unfold Formalism.L2.Herm.hatL latS at hw ⊢
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨x, hxM, rfl⟩ := hx
    refine Submodule.subset_span ⟨(h : Matrix (Fin N) (Fin N) E) *ᵥ x, ?_, ?_⟩
    · exact ⟨x, hxM, rfl⟩
    · exact (bc_mulVec (F := F) h x).symm
  | zero => simp
  | add a b _ _ ha hb => rw [Matrix.mulVec_add]; exact add_mem ha hb
  | smul s a _ ha =>
    rw [Matrix.mulVec_smul]
    exact Submodule.smul_mem _ s ha

theorem mvL_one_lat {E : Type} [Field E] [NumberField E] {N : ℕ} (M : Submodule (𝓞 E) (Fin N → E)) : mvL 1 M = M := by
  unfold mvL
  ext x
  simp only [Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨y, hy, h⟩
    change ((1 : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ y = x at h
    rw [Units.val_one, Matrix.one_mulVec] at h
    simpa [h] using hy
  · intro hx
    refine ⟨x, hx, ?_⟩
    change ((1 : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ x = x
    rw [Units.val_one, Matrix.one_mulVec]

theorem latAd_mul_ratA : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {N : ℕ}
    (y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (g : GL (Fin N) E) (M : Submodule (𝓞 E) (Fin N → E)),
    latAd (y * ratA F g) M = latAd y (mvL g M) := by
  intro F E _ _ _ _ _ _ N y g M
  have key : ∀ w : Fin N → E ⊗[F] FiniteAdeleRing (𝓞 F) F,
      ((ratA F g⁻¹ : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ w ∈
        Formalism.L2.Herm.hatL (F := F) M ↔ w ∈ Formalism.L2.Herm.hatL (F := F) (mvL g M) := by
    intro w
    constructor
    · intro hw
      have := mulVec_mem_hatL_mvL g M _ hw
      rwa [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
        Matrix.one_mulVec] at this
    · intro hw
      have := mulVec_mem_hatL_mvL g⁻¹ (mvL g M) w hw
      rwa [← mvL_mul, inv_mul_cancel, mvL_one_lat] at this
  unfold latAd
  congr 1
  ext x
  rw [Set.mem_setOf_eq, Set.mem_setOf_eq, _root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec, ← map_inv, key]

end GlobalTheory.TwV
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicPointLatticeMulRationalGLStatement
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicPointLattice_mul_rationalGL : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {N : ℕ} (y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (g : GL (Fin N) E) (M : Submodule (𝓞 E) (Fin N → E)), latAd (y * ratA F g) M = latAd y (mvL g M) := by
  first | exact @GlobalTheory.TwV.latAd_mul_ratA | exact GlobalTheory.TwV.latAd_mul_ratA | (intros; apply GlobalTheory.TwV.latAd_mul_ratA <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartBaseFrameBadPrimeEqCompanionLattice
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BaseFrameLat

theorem locP_map_equiv' {R W W' : Type*} [CommRing R] [AddCommGroup W] [Module R W] [AddCommGroup W'] [Module R W']
    (e : W ≃ₗ[R] W') (q : Ideal R) [q.IsPrime] (Λ : Submodule R W) :
    Formalism.HermitianLatticesTheory.localization₂ q (Λ.map (e : W →ₗ[R] W')) = (Formalism.HermitianLatticesTheory.localization₂ q Λ).map (e : W →ₗ[R] W') := by
  ext x
  constructor
  · rintro ⟨s, hs, z, hz, hzx⟩
    refine ⟨e.symm x, ⟨s, hs, ?_⟩, by simp⟩
    have : s • e.symm x = z := by
      apply e.injective
      rw [map_smul, e.apply_symm_apply]
      exact hzx.symm
    rw [this]
    exact hz
  · rintro ⟨y, ⟨s, hs, hy⟩, rfl⟩
    exact ⟨s, hs, s • y, hy, by simp⟩

theorem locP_mvL_comm {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ} (c : GL (Fin N) E) (q : Ideal (𝓞 E)) [q.IsPrime]
    (Λ : Submodule (𝓞 E) (Fin N → E)) : Formalism.HermitianLatticesTheory.localization₂ q (mvL c Λ) = mvL c (Formalism.HermitianLatticesTheory.localization₂ q Λ) :=
  locP_map_equiv' ((toLE c).restrictScalars (𝓞 E)) q Λ

theorem mvL_one' {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ} (Λ : Submodule (𝓞 E) (Fin N → E)) : mvL 1 Λ = Λ := by
  unfold mvL
  convert Submodule.map_id _
  refine LinearMap.ext fun z => ?_
  show toLE 1 z = z
  rw [toLE_apply, Units.val_one, Matrix.one_mulVec]

theorem span_mvL {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ} (c : GL (Fin N) E) (Λ : Submodule (𝓞 E) (Fin N → E))
    (h : Submodule.span E (Λ : Set (Fin N → E)) = ⊤) : Submodule.span E ((mvL c Λ : Submodule (𝓞 E) (Fin N → E)) : Set (Fin N → E)) = ⊤ := by
  have e : ((mvL c Λ : Submodule (𝓞 E) (Fin N → E)) : Set (Fin N → E)) = (toLE c : (Fin N → E) →ₗ[E] (Fin N → E)) '' (Λ : Set (Fin N → E)) := by
    unfold mvL
    rw [Submodule.map_coe]
    rfl
  rw [e, ← Submodule.map_span, h, Submodule.map_top, LinearMap.range_eq_top]
  exact (toLE c).surjective

end GlobalTheory.BaseFrameLat


open GlobalTheory.BaseFrameLat in
theorem GlobalTheory.TwV.baseFrame_std_eq_compan : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x : UA D i hi) p, IsPtAd A a i hi β x p → ∀ P : SB t μ, mvL (A.fb i hi β P) (stdAt D.host.E (D.R.N i) (seamP t.seam P.1)) = Formalism.HermitianLatticesTheory.localization₂ (seamP t.seam P.1).asIdeal (compan (sp := D.sp) (gramN D i hi) a ((St i hi).K β).lev.Lb)) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hpins htie i hi β x p hp P
  have hd : 1 ≤ (t.cst μ).D P := (t.idx_ok μ).cst_ok.D_pos P
  have hR := GlobalTheory.T.transportedFrame_standardLocal_eq_localization t.seam P.1 (frsF t.sel (t.tup μ) p P) p.deco.1.N (GlobalTheory.TopStep.frsF_mem p P)
  rw [hp.lat] at hR
  have hJ : IsUnit (gramN D i hi).det := by
    rw [← hpins.crd_orth i hi, Matrix.det_mul]
    have hc : IsUnit ((A.crd i hi).1).det := (Matrix.isUnit_iff_isUnit_det _).mp (A.crd i hi).isUnit
    refine IsUnit.mul ?_ hc
    show IsUnit ((((A.crd i hi).1).map (sigD D : D.host.E →+* D.host.E))ᵀ).det
    rw [Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hc.map _
  have hfg : (((St i hi).K β).lev.Lb).FG := Module.Finite.iff_fg.mp ((St i hi).K β).lev.Lb_fin
  have hsp := ((St i hi).K β).lev.Lb_span
  have h4 := GlobalTheory.T.companionLattice_adelicLattice_localization_eq D.sp (sigD D) rfl (gramN D i hi) hJ a x.1 x.2 _ hfg hsp (seamP t.seam P.1)
  have hCfg := GlobalTheory.T.companionHermitianLattice_fg D.sp (gramN D i hi) hJ a _ hfg hsp
  set C := compan (sp := D.sp) (gramN D i hi) a ((St i hi).K β).lev.Lb with hC
  have hCs : Submodule.span D.host.E (C : Set (Fin (D.R.N i) → D.host.E)) = ⊤ := by
    refine eq_top_iff.2 (hsp ▸ Submodule.span_mono ?_)
    intro z hz
    exact (le_sup_left : ((St i hi).K β).lev.Lb ≤ C) hz
  unfold latCo at hR
  rw [locP_mvL_comm, h4, ← locP_mvL_comm] at hR
  have e1 : mvL (A.crd i hi) (latAd x.1 C) = latAd (ratA D.host.F (A.crd i hi) * x.1 * ratA D.host.F (A.fb i hi β P)) (mvL (A.fb i hi β P)⁻¹ C) := by
    rw [GlobalTheory.T.adelicPointLattice_mul_rationalGL, ← mvL_mul, mul_inv_cancel, mvL_one']
    exact (latAd_rat _ _ _).symm
  rw [e1] at hR
  have h3 := GlobalTheory.T.localisation_eq_stdAt_of_congruentOne_atPrime (seamP t.seam P.1) _ hd _ _ (mvL (A.fb i hi β P)⁻¹ C) (hCfg.map _) (span_mvL _ _ hCs) (hp.frame P) hR.symm
  rw [← h3, ← locP_mvL_comm, ← mvL_mul, mul_inv_cancel, mvL_one']
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartBaseFrameBadPrimeEqCompanionLatticeStatement
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartBaseFrame_badPrime_eq_companion_lattice : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x : UA D i hi) p, IsPtAd A a i hi β x p → ∀ P : SB t μ, mvL (A.fb i hi β P) (stdAt D.host.E (D.R.N i) (seamP t.seam P.1)) = Formalism.HermitianLatticesTheory.localization₂ (seamP t.seam P.1).asIdeal (compan (sp := D.sp) (gramN D i hi) a ((St i hi).K β).lev.Lb)) := by
  first | exact @GlobalTheory.TwV.baseFrame_std_eq_compan | exact GlobalTheory.TwV.baseFrame_std_eq_compan | (intros; apply GlobalTheory.TwV.baseFrame_std_eq_compan <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartLevelBaseFrameCongrOneAtBadPrime
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV

theorem congAt_fb_lev : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x : UA D i hi) p (κ : ((St i hi).K β).lev.U), IsPtAd A a i hi β x p → ∀ P : SB t μ, CongAt (seamP t.seam P.1) 0 ((ratA D.host.F (A.fb i hi β P))⁻¹ * κ.1 * ratA D.host.F (A.fb i hi β P)) ∧ CongAt (seamP t.seam P.1) 0 ((ratA D.host.F (A.fb i hi β P))⁻¹ * κ.1 * ratA D.host.F (A.fb i hi β P))⁻¹) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP H i hi β x p κ hp P
  exact GlobalTheory.LevStab.lev_stab_cong i hi _ a κ _ _ (GlobalTheory.T.chartBaseFrame_badPrime_eq_companion_lattice A dtU a hP H i hi β x p hp P)

end GlobalTheory.TwV

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartLevelBaseFrameCongrOneAtBadPrimeStatement
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartLevel_baseFrame_congr_one_at_badPrime : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x : UA D i hi) p (κ : ((St i hi).K β).lev.U), IsPtAd A a i hi β x p → ∀ P : SB t μ, CongAt (seamP t.seam P.1) 0 ((ratA D.host.F (A.fb i hi β P))⁻¹ * κ.1 * ratA D.host.F (A.fb i hi β P)) ∧ CongAt (seamP t.seam P.1) 0 ((ratA D.host.F (A.fb i hi β P))⁻¹ * κ.1 * ratA D.host.F (A.fb i hi β P))⁻¹) := by
  first | exact @GlobalTheory.TwV.congAt_fb_lev | exact GlobalTheory.TwV.congAt_fb_lev | (intros; apply GlobalTheory.TwV.congAt_fb_lev <;> assumption)
end
