module

public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelLPfL

@[expose] public section

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelLPfD
noncomputable section

namespace Formalism.MainNotions.N.Ln34.MLD

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (π' : LetA O n) (c : ZMod n)

theorem toLA_tmul' (S : Submodule O (LcQ W T π' c)) (a : ↥W.AΔ) (s : ↥S) :
    toLA W T π' c S (a ⊗ₜ s) = algebraMap (LetA O n) W.EE ((letE c : LetA O n) * a) ⊗ₜ (s : LcQ W T π' c) := by
  simp [toLA, TensorProduct.map_tmul]

theorem smulLA_tmul' (b : LetA O n) (e : W.EE) (y : LcQ W T π' c) :
    smulLA W T π' c b (e ⊗ₜ y) = (algebraMap (LetA O n) W.EE b * e) ⊗ₜ y := by
  simp [smulLA, TensorProduct.map_tmul]

theorem smulLA_mul' (a b : LetA O n) (x : LA W T π' c) :
    smulLA W T π' c (a * b) x = smulLA W T π' c a (smulLA W T π' c b x) := by
  induction x using TensorProduct.inductionOn with
  | tmul x y => simp [smulLA_tmul', map_mul, mul_assoc]
  | add x y hx hy => simp [map_add (f := _), hx, hy]

theorem eat_mem (E : ZMod n → Polynomial O) (hπ : π' ∈ W.AΔ) : Formalism.MainNotions.DeltaInvariantLattices.Eat E π' ∈ W.AΔ := by
  intro δ hδ
  have h := hπ δ hδ
  funext i
  have hi := congrFun h i
  simp only [LocWach.γA, letγ, AlgHom.pi_apply, AlgHom.comp_apply, Pi.evalAlgHom_apply] at hi ⊢
  simp only [Formalism.MainNotions.DeltaInvariantLattices.Eat]
  rw [← Polynomial.aeval_algHom_apply, hi]


open PowerSeries in
theorem filtration_value_local (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (Eπ : LetA O n) (h' : ℕ)
    (hEΔ : Eπ ∈ W.AΔ)
    (hlev : ∀ τ ζ, Pt c ζ τ → constantCoeff (W.lev c ζ Eπ) = 0)
    (hval : ∀ τ ζ, Pt c ζ τ → ∀ y ∈ NcS W T (c - 1),
      valAt W T c ζ y ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (-(h' : ℤ)))
    (hanti : ∀ (τ : K →ₐ[Qp] LL) (a' a : ℤ), a' ≤ a →
      Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ a ≤ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ a') :
    (LinearMap.range (toLA W T π' c ⊤)).map (smulLA W T π' c (Eπ ^ h')) ≤ NL W T Pt π' Eπ h' c := by
  rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
  induction t using TensorProduct.inductionOn with
  | add x y hx hy => simpa only [map_add] using add_mem hx hy
  | tmul a s =>
    apply Submodule.subset_span
    obtain ⟨⟨y, hy⟩, hys⟩ := Submodule.Quotient.mk_surjective _ (s : LcQ W T π' c)
    have hΛΔ : Eπ ^ h' ∈ W.AΔ := Subalgebra.pow_mem _ hEΔ h'
    let a' : Fin 1 → ↥W.AΔ := fun _ => ⟨Eπ ^ h' * Eπ ^ h' * a, Subalgebra.mul_mem _
      (Subalgebra.mul_mem _ hΛΔ hΛΔ) a.2⟩
    let y' : Fin 1 → W.DD T := fun _ => y
    refine ⟨1, a', y', ⟨fun _ => hy, ?_⟩, ?_⟩
    · rw [Fin.sum_univ_one, toLA_tmul', smulLA_tmul', smulLA_tmul', ← map_mul, ← map_mul]
      have hm : mkL W T π' c (y' 0) hy = (s : LcQ W T π' c) := hys
      rw [hm]
      congr 2
      simp only [a']
      ring
    · intro τ ζ hpt i
      simp only [expS, Fin.sum_univ_one, serC, a', y']
      split_ifs with hi
      · by_cases hlt : i.toNat < 2 * h'
        · have hX : X ^ (2 * h') ∣ W.lev c ζ (Eπ ^ h' * Eπ ^ h' * (a : LetA O n)) := by
            have hXE : X ∣ W.lev c ζ Eπ := PowerSeries.X_dvd_iff.mpr (hlev τ ζ hpt)
            have h2 : W.lev c ζ (Eπ ^ h' * Eπ ^ h' * (a : LetA O n)) =
                W.lev c ζ Eπ ^ (2 * h') * W.lev c ζ (a : LetA O n) := by
              rw [map_mul, map_mul, map_pow, ← pow_add, two_mul]
            rw [h2]
            exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd hXE _) _
          have hc : coeff i.toNat (W.lev c ζ (Eπ ^ h' * Eπ ^ h' * (a : LetA O n))) = 0 :=
            (PowerSeries.X_pow_dvd_iff.mp hX) _ hlt
          rw [hc, zero_smul]
          exact Submodule.zero_mem _
        · refine Submodule.smul_mem _ _ ?_
          refine hanti τ _ _ (by omega) (hval τ ζ hpt y hy)
      · exact Submodule.zero_mem _

theorem R_smul' {b : LetA O n} (hb : b ∈ W.AΔ) {r : LA W T π' c}
    (hr : r ∈ LinearMap.range (toLA W T π' c ⊤)) :
    smulLA W T π' c b r ∈ LinearMap.range (toLA W T π' c ⊤) := by
  obtain ⟨t, rfl⟩ := hr
  induction t using TensorProduct.inductionOn with
  | tmul a s =>
    refine ⟨(⟨b, hb⟩ * a) ⊗ₜ s, ?_⟩
    rw [toLA_tmul', toLA_tmul', smulLA_tmul', ← map_mul]
    congr 2
    simp only [Subalgebra.coe_mul]
    ring
  | add x y hx hy => simpa only [map_add] using add_mem hx hy

theorem lattice_contains_power_local (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (Eπ : LetA O n) (h' M : ℕ)
    (hEΔ : Eπ ∈ W.AΔ)
    (h4 : (LinearMap.range (toLA W T π' c ⊤)).map (smulLA W T π' c (Eπ ^ h')) ≤ NL W T Pt π' Eπ h' c) :
    JLA W T π' Eπ h' M c ≤ piNL W T Pt π' Eπ h' c M := by
  rintro _ ⟨r, hr, rfl⟩
  have hr2 := R_smul' W T π' c (Subalgebra.pow_mem _ hEΔ (2 * h')) hr
  refine ⟨smulLA W T π' c (Eπ ^ h') (smulLA W T π' c (Eπ ^ (2 * h')) r), h4 ⟨_, hr2, rfl⟩, ?_⟩
  rw [← smulLA_mul', ← smulLA_mul']
  congr 1
  rw [show 3 * h' = h' + 2 * h' by ring, pow_add]
  ring

end Local


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem val_fil (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (h1 : adm1 D HW F Cm) {l : ℕ} [Fact l.Prime] (K LL : FinExt l) (hG : Good K 1 LL)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (hT : IsCrys ((D.loc l).PD K) T.ρ) (h' : ℕ)
    (hJ : ∀ τ, JumpsInV ((D.loc l).PD K) T.ρ τ (Set.Icc (-(h' : ℤ)) h'))
    (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) (c : ZMod (finrank ℚ_[l] ↥(K0 K))) (ζ : ↥LL.1)
    (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (hpt : Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ)
    (y : ((HW l).W K 1 LL hG).DD T) (hy : y ∈ NcS ((HW l).W K 1 LL hG) T (c - 1)) :
    valAt ((HW l).W K 1 LL hG) T c ζ y ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := (D.loc l).PD K) T τ (-(h' : ℤ)) := by
  have hyL : (letE (c - 1) : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) • y = y := by
    have := hy.2
    simpa [letS, LinearMap.mem_ker, sub_eq_zero] using this
  have hφ := MLC.φD_letter' ((HW l).W K 1 LL hG) T hyL
  rw [sub_add_cancel] at hφ
  have hp4 := ((h1 l K 1 LL hG).2.2.2.1 T hT).2 c ζ τ hpt
  have key : ∀ (k : ℕ) (hz : ((HW l).W K 1 LL hG).Q ^ k • ((HW l).W K 1 LL hG).φD T y ∈
      ((HW l).W K 1 LL hG).N T),
      ((HW l).W K 1 LL hG).levN T c ζ ⟨_, hz⟩ (k : ℤ) ∈
        Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := (D.loc l).PD K) T τ (-(h' : ℤ)) := by
    intro k hz
    have h3 := hp4.2.1 ⟨_, hz⟩ (k : ℤ)
    have hsub : ((letE c : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) •
        (⟨_, hz⟩ : ↥(((HW l).W K 1 LL hG).N T))) = ⟨_, hz⟩ := by
      apply Subtype.ext
      show (letE c : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) •
          (((HW l).W K 1 LL hG).Q ^ k • ((HW l).W K 1 LL hG).φD T y) = _
      rw [smul_comm, hφ]
    rw [hsub] at h3
    exact MLC.filC_le_bot T τ h' (hJ τ) _ (Submodule.mem_inf.mp h3).2
  unfold valAt
  split_ifs with h
  · exact Submodule.smul_mem _ _ (key _ _)
  · exact Submodule.zero_mem _


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
open PowerSeries in
theorem lev_eat_zero (D : D7) (HW : HWOf D.loc) {l : ℕ} [Fact l.Prime] (K LL : FinExt l)
    (hG : Good K 1 LL) (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K)))
    (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL))
    (hr : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E)
    (c : ZMod (finrank ℚ_[l] ↥(K0 K))) (ζ : ↥LL.1) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1)
    (hpt : Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ) :
    constantCoeff (((HW l).W K 1 LL hG).lev c ζ (Formalism.MainNotions.DeltaInvariantLattices.Eat E π')) = 0 := by
  have hζ := framepf_pt_prim D HW hG c ζ τ hpt
  have hζ' : IsPrimitiveRoot ζ ((D.loc l).PD K).p := by rw [(D.loc l).PD_p K]; exact hζ
  obtain ⟨u, hu, -⟩ := framepf_lev_q_simple ((HW l).W K 1 LL hG) c ζ hζ'
  obtain ⟨w, hw⟩ := hr.2.2.2.2.1
  have h1 := congrArg (fun f => constantCoeff (((HW l).W K 1 LL hG).lev c ζ f)) hw
  simp only [hu, map_mul, constantCoeff_X, zero_mul] at h1
  have hwu : IsUnit (constantCoeff (((HW l).W K 1 LL hG).lev c ζ (w : LetA ↥(OL LL) _))) :=
    (PowerSeries.isUnit_iff_constantCoeff).mp (w.isUnit.map _)
  exact (hwu.mul_right_eq_zero).mp h1.symm


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem model_lattice_filtration (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (CA CB CK : ℝ) (hA : Adm1 D HW F Cm CA CB CK) (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) (K LL : FinExt l)
    (hG : Good K 1 LL) (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K)))
    (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL))
    (hr : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E) (h' : ℕ) (hh' : 1 ≤ h')
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (hT : IsCrys ((D.loc l).PD K) T.ρ)
    (hJ : ∀ τ, JumpsInV ((D.loc l).PD K) T.ρ τ (Set.Icc (-(h' : ℤ)) h'))
    (c : ZMod (finrank ℚ_[l] ↥(K0 K))) :
    (LinearMap.range (toLA ((HW l).W K 1 LL hG) T π' c ⊤)).map
        (smulLA ((HW l).W K 1 LL hG) T π' c (Formalism.MainNotions.DeltaInvariantLattices.Eat E π' ^ h')) ≤
      NL ((HW l).W K 1 LL hG) T (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' c :=
  filtration_value_local ((HW l).W K 1 LL hG) T π' c (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h'
    (eat_mem ((HW l).W K 1 LL hG) π' E hr.1)
    (fun τ ζ hpt => lev_eat_zero D HW K LL hG π' E hr c ζ τ hpt)
    (fun τ ζ hpt y hy => val_fil D HW F Cm hA.1 K LL hG T hT h' hJ π' c ζ τ hpt y hy)
    (fun τ a' a h => u3upPf_FilC_anti (PD := (D.loc l).PD K) T τ h)


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem model_lattice_power (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (CA CB CK : ℝ) (hA : Adm1 D HW F Cm CA CB CK) (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) (K LL : FinExt l)
    (hG : Good K 1 LL) (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K)))
    (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL))
    (hr : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E) (h' : ℕ) (hh' : 1 ≤ h')
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (hT : IsCrys ((D.loc l).PD K) T.ρ)
    (hJ : ∀ τ, JumpsInV ((D.loc l).PD K) T.ρ τ (Set.Icc (-(h' : ℤ)) h'))
    (c : ZMod (finrank ℚ_[l] ↥(K0 K))) :
    JLA ((HW l).W K 1 LL hG) T π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' (MK l K h') c ≤
      piNL ((HW l).W K 1 LL hG) T (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' c (MK l K h') :=
  lattice_contains_power_local ((HW l).W K 1 LL hG) T π' c (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' (MK l K h')
    (eat_mem ((HW l).W K 1 LL hG) π' E hr.1)
    (model_lattice_filtration D HW F Cm CA CB CK hA l hl K LL hG π' E hr h' hh' T hT hJ c)

end Formalism.MainNotions.N.Ln34.MLD

end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelLPfK
noncomputable section

namespace Formalism.MainNotions.N.Ln34.MLK

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module


set_option maxHeartbeats 800000 in
theorem lev_Eat_simple (D : D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) (K LL : FinExt l)
    (hG : Good K 1 LL) (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K)))
    (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL))
    (hr : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E) (c : ZMod (finrank ℚ_[l] ↥(K0 K)))
    (ζ : ↥LL.1) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (hpt : Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ) :
    ∃ U : PowerSeries ↥LL.1, ((HW l).W K 1 LL hG).lev c ζ (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') = PowerSeries.X * U ∧
      PowerSeries.constantCoeff U ≠ 0 := by
  obtain ⟨τs, hIs, -⟩ := hpt
  obtain ⟨-, hIs2⟩ := hIs
  unfold Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations at hr
  obtain ⟨-, -, -, -, ⟨w, hw⟩, -, -, -⟩ := hr
  generalize (HW l).W K 1 LL hG = W at hw ⊢

  have hz : (D.loc l).ζQ 1 ^ l = 1 := by
    have h := (D.loc l).ζQ_succ 0
    rw [(D.loc l).ζQ_zero] at h
    simpa using h
  have hmem : (D.loc l).ζQ 1 ∈ Ks K 1 := by
    show (D.loc l).ζQ 1 ∈ K0 K ⊔ IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ 1) = 1}
    exact SetLike.le_def.mp le_sup_right (IntermediateField.subset_adjoin ℚ_[l] _ (by simpa using hz))
  have hζ : τs ⟨_, hmem⟩ = ζ := hIs2 ⟨_, hmem⟩ rfl
  have hζl : ζ ^ l = 1 := by
    have h1 : (⟨_, hmem⟩ : ↥(Ks K 1)) ^ l = 1 := Subtype.ext (by simpa using hz)
    rw [← hζ, ← map_pow, h1, map_one]
  have hne : ζ ≠ 1 := by
    intro h1
    have h2 : (⟨_, hmem⟩ : ↥(Ks K 1)) = 1 :=
      RingHom.injective (τs : ↥(Ks K 1) →+* ↥LL.1) (by simp [hζ, h1])
    exact (D.loc l).ζQ_one (by simpa using congrArg Subtype.val h2)
  have hprim : IsPrimitiveRoot ζ l := by
    have h := IsPrimitiveRoot.orderOf ζ
    rwa [orderOf_eq_prime hζl hne] at h
  have hl0 : ((l : ℕ) : ↥LL.1) ≠ 0 := by
    intro h
    have h' := (D.loc l).v_l LL
    rw [h, AddValuation.map_zero] at h'
    simp at h'

  obtain ⟨F, hF0, hFd, hFπ⟩ :=
    W.lev_π c ζ ⟨1, by rw [(D.loc l).PD_p K, pow_one]; exact hprim⟩
  obtain ⟨F1, hF1⟩ : PowerSeries.X ∣ F - 1 := by
    rw [PowerSeries.X_dvd_iff, map_sub, hF0, map_one, sub_self]
  have hF1c : PowerSeries.constantCoeff F1 = 1 := by
    have hd := congrArg (fun f : PowerSeries ↥LL.1 => PowerSeries.constantCoeff (PowerSeries.derivative f)) hF1
    simp only [map_sub, Derivation.map_one_eq_zero, sub_zero, hFd, hF0, Derivation.leibniz,
      PowerSeries.derivative_X, smul_eq_mul, map_add, map_mul, map_one, PowerSeries.constantCoeff_X,
      zero_mul, zero_add, mul_one] at hd
    exact hd.symm

  have hq : (letπ : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) * W.q =
      (1 + letπ) ^ ((D.loc l).PD K).p - 1 := by
    funext i
    exact W.q₀_def
  have hl1 : W.lev c ζ 1 = 1 := map_one (W.lev c ζ)
  have hadd : W.lev c ζ (1 + letπ) = 1 + W.lev c ζ letπ := by
    rw [← hl1]
    exact (W.lev c ζ).map_add 1 letπ
  have hlq := congrArg (W.lev c ζ) hq
  rw [map_mul (W.lev c ζ), map_sub (W.lev c ζ), map_pow (W.lev c ζ), hadd, hl1, hFπ, (D.loc l).PD_p K, mul_pow, ← map_pow PowerSeries.C ζ l, hζl,
    map_one PowerSeries.C, one_mul, ← mul_geom_sum, hF1, hw, map_mul (W.lev c ζ)] at hlq
  have hy0 : PowerSeries.constantCoeff (W.lev c ζ letπ) ≠ 0 := by
    have h := congrArg PowerSeries.constantCoeff hFπ
    rw [map_add (f := _), map_one, map_mul, PowerSeries.constantCoeff_C, hF0, mul_one] at h
    have h' : PowerSeries.constantCoeff (W.lev c ζ letπ) = ζ - 1 := by linear_combination h
    rw [h']
    exact sub_ne_zero.mpr hne
  obtain ⟨u, hu⟩ : IsUnit (W.lev c ζ letπ * W.lev c ζ ↑w) :=
    (PowerSeries.isUnit_iff_constantCoeff.mpr (isUnit_iff_ne_zero.mpr hy0)).mul
      (w.isUnit.map (W.lev c ζ))
  rw [← mul_assoc, ← hu] at hlq
  refine ⟨↑u⁻¹ * (F1 * ∑ i ∈ Finset.range l, F ^ i), ?_, ?_⟩
  · calc _ = ↑u⁻¹ * (↑u * W.lev c ζ (Formalism.MainNotions.DeltaInvariantLattices.Eat E π')) := by
          rw [← mul_assoc, Units.inv_mul, one_mul]
      _ = _ := by rw [hlq]; ring
  · rw [map_mul]
    refine mul_ne_zero ((u⁻¹).isUnit.map PowerSeries.constantCoeff).ne_zero ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_mul, hF1c, one_mul, map_sum]
    simpa [hF0] using hl0

end Formalism.MainNotions.N.Ln34.MLK
end
end

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

theorem modell_pf : ModelLStep := by
  unfold ModelLStep modelLR recU
  intro D HW F Cm CA CB CK hA l _ hl K LL hG π' E hr h' hh' T hT hJ c
  obtain ⟨u₀, hu₀, hΛ⟩ := MLL.exists_mul_gamma_Eat_pow_eq_Eat_pow D HW F Cm CA CB CK hA l hl K LL hG π' E hr h'
  obtain ⟨hu, hu1⟩ := MLL.rec_u D HW l hl K LL hG
  have hwd := MLL.rec_WD D HW F Cm CA CB CK hA l hl K LL hG π' E hr T hT c
  have hlet := Formalism.MainNotions.ArcLiftingSetup.γA_letE ((HW l).W K 1 LL hG) ((HW l).W K 1 LL hG).gamK c
  have hlev := fun τ ζ (hpt : Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ) a =>
    MLL.rec_lev D HW F Cm l hl K LL hG c τ ζ hpt a
  unfold ModelL
  refine ⟨MLF.nl_le _ _ _ _ _ _ _, fun x hx => MLH.nl_γ _ _ _ _ _ _ _ hu₀ hΛ hlet _ hlev hx,
    fun a ha x hx => MLF.nl_smulA _ _ _ _ _ _ _ ha hx,
    MLD.model_lattice_filtration D HW F Cm CA CB CK hA l hl K LL hG π' E hr h' hh' T hT hJ c,
    fun x hx k hk => MLF.nl_sat _ _ _ _ _ _ _ hwd ?_ hx k hk,
    MLD.model_lattice_power D HW F Cm CA CB CK hA l hl K LL hG π' E hr h' hh' T hT hJ c,
    fun x hx hγ => MLJ.local_form _ _ _ _ _ _ _ hwd hu₀ hΛ hlet _ hu hu1 hlev ?_ hx hγ⟩
  · rw [map_natCast]
    exact Formalism.MainNotions.LiftingTheory.tr_pLL_ne ((HW l).W K 1 LL hG)
  · intro τ ζ hpt
    obtain ⟨U, hU, hU0⟩ := MLK.lev_Eat_simple D HW l hl K LL hG π' E hr c ζ τ hpt
    refine ⟨U ^ h', ?_, ?_⟩
    · rw [map_pow, hU, mul_pow]
    · rw [map_pow]
      exact pow_ne_zero _ hU0

end Formalism.MainNotions.N.Ln34

end
