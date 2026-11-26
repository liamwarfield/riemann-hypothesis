module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.LevelSAllOfSemiNHSHeisLev
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.ToMatrixLin
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.ModulusAllExtensions

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.NCAsmM
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.NCAsmV
noncomputable section

namespace PI.LevelKSplit.W.NCA

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory Topology
open PI.LevelKSplit PI.LevelKSplit.W.NC PI.LevelKSplit.W.SemiA
open scoped TensorProduct

section Gen

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V]
  [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]

theorem map_eq_of_split (p : V →+ V) (hp : Continuous p) (hpp : ∀ v, p (p v) = p v)
    (W : AddSubgroup V) (hW : ∀ v, v ∈ W ↔ p v = v)
    (g : V →+ V) (hg : Continuous g) (hgU : ∀ u, p u = 0 → g u = u)
    (hV : ∀ μ : Measure V, μ.IsAddHaarMeasure → μ.map g = μ)
    (f : W → W) (hf : ∀ w, (f w : V) = g w) (μ : Measure W) (hμ : μ.IsAddHaarMeasure) :
    μ.map f = μ := by
  classical
  haveI := hμ
  set U : AddSubgroup V := p.ker with hUdef
  have hWc : IsClosed (W : Set V) := by
    have e : (W : Set V) = {v | p v = v} := Set.ext fun v => hW v
    rw [e]
    exact isClosed_eq hp continuous_id
  have hUc : IsClosed (U : Set V) := by
    have e : (U : Set V) = {v | p v = 0} := Set.ext fun v => by simp [hUdef, AddMonoidHom.mem_ker]
    rw [e]
    exact isClosed_eq hp continuous_const
  haveI : LocallyCompactSpace W := hWc.locallyCompactSpace
  haveI : LocallyCompactSpace U := hUc.locallyCompactSpace
  haveI : BorelSpace W := Subtype.borelSpace (fun x => x ∈ (W : Set V))
  haveI : BorelSpace U := Subtype.borelSpace (fun x => x ∈ (U : Set V))
  haveI : SecondCountableTopology W := TopologicalSpace.Subtype.secondCountableTopology (W : Set V)
  haveI : SecondCountableTopology U := TopologicalSpace.Subtype.secondCountableTopology (U : Set V)
  haveI : BorelSpace (W × U) := Prod.borelSpace
  have hpW : ∀ w : W, p w = w := fun w => (hW w).1 w.2
  have hfc : Continuous f := by
    apply continuous_induced_rng.2
    have e : (Subtype.val ∘ f : W → V) = fun w : W => g (w : V) := funext hf
    rw [e]
    exact hg.comp continuous_subtype_val
  let Φ : W × U →+ V := W.subtype.comp (AddMonoidHom.fst W U) + U.subtype.comp (AddMonoidHom.snd W U)
  have hΦ : ∀ x : W × U, Φ x = (x.1 : V) + (x.2 : V) := fun x => rfl
  have hΦc : Continuous Φ := by
    have e : (Φ : W × U → V) = fun x => (x.1 : V) + (x.2 : V) := funext hΦ
    rw [e]
    exact (continuous_subtype_val.comp continuous_fst).add (continuous_subtype_val.comp continuous_snd)
  let Ψ : V → W × U := fun v => (⟨p v, (hW _).2 (hpp v)⟩,
    ⟨v - p v, by simp [hUdef, AddMonoidHom.mem_ker, map_sub, hpp]⟩)
  have hΨc : Continuous Ψ :=
    (hp.subtype_mk fun v => (hW _).2 (hpp v)).prodMk ((continuous_id.sub hp).subtype_mk fun v => by
      simp [hUdef, AddMonoidHom.mem_ker, map_sub, hpp])
  have hΦΨ : ∀ v, Φ (Ψ v) = v := fun v => by
    rw [hΦ]
    simp [Ψ]
  have hΨΦ : ∀ x, Ψ (Φ x) = x := by
    rintro ⟨w, u⟩
    have hu : p u = 0 := u.2
    have hpx : p (Φ (w, u)) = w := by rw [hΦ, map_add (f := _), hpW, hu, add_zero]
    apply Prod.ext
    · apply Subtype.ext
      show p (Φ (w, u)) = w
      exact hpx
    · apply Subtype.ext
      show Φ (w, u) - p (Φ (w, u)) = u
      rw [hpx, hΦ]
      simp
  have hΦs : Function.Surjective Φ := fun v => ⟨Ψ v, hΦΨ v⟩
  let e : (W × U) ≃ₜ V :=
    { toFun := Φ, invFun := Ψ, left_inv := hΨΦ, right_inv := hΦΨ,
      continuous_toFun := hΦc, continuous_invFun := hΨc }
  let ν : Measure U := Measure.addHaar
  set P : Measure (W × U) := μ.prod ν with hP
  haveI hPH : P.IsAddHaarMeasure := by rw [hP]; infer_instance
  have hHaar : (P.map Φ).IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_map P Φ hΦc hΦs e.isClosedEmbedding.tendsto_cocompact
  have hmap := hV _ hHaar
  have hgΦ : (g : V → V) ∘ Φ = Φ ∘ Prod.map f id := by
    funext x
    obtain ⟨w, u⟩ := x
    simp only [Function.comp, Prod.map, id, hΦ, map_add (f := _), hgU u u.2, hf]
  have hfm : Measurable f := hfc.measurable
  have hPm : Measurable (Prod.map f (id : U → U)) := hfm.prodMap measurable_id
  rw [Measure.map_map hg.measurable hΦc.measurable, hgΦ,
    ← Measure.map_map hΦc.measurable hPm] at hmap
  have hinv : ∀ Q : Measure (W × U), (Q.map Φ).map Ψ = Q := by
    intro Q
    rw [Measure.map_map hΨc.measurable hΦc.measurable]
    have e2 : Ψ ∘ Φ = id := funext hΨΦ
    rw [e2, Measure.map_id]
  have hP' : P.map (Prod.map f id) = P := by
    have h2 := congrArg (fun Q => Q.map Ψ) hmap
    simpa only [hinv] using h2
  obtain ⟨K, hKc, hKn⟩ := exists_compact_mem_nhds (0 : U)
  have hK0 : ν K ≠ 0 := (Measure.measure_pos_of_mem_nhds ν hKn).ne'
  have hKt : ν K ≠ ⊤ := hKc.measure_lt_top.ne
  ext A hA
  rw [Measure.map_apply hfm hA]
  have h1 : (P.map (Prod.map f id)) (A ×ˢ K) = P (A ×ˢ K) := by rw [hP']
  rw [Measure.map_apply hPm (hA.prod hKc.measurableSet)] at h1
  have hpre : Prod.map f id ⁻¹' (A ×ˢ K) = (f ⁻¹' A) ×ˢ K := by
    ext x
    simp
  rw [hpre, hP, Measure.prod_prod, Measure.prod_prod] at h1
  have h2 := congrArg (fun t => t / ν K) h1
  simp only [ENNReal.mul_div_cancel_right hK0 hKt] at h2
  exact h2

end Gen

namespace DatL

open PI.LevelKSplit.W.SemiG PI.LevelKSplit.W.SemiG.Dat

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
  {D : PI.LevelKSplit.W.SemiG.Dat A n r}

theorem h_e_pXv (H : D.Hyp) (b : Fin r) (v : n → A) : D.h (D.e b) (D.pXv v) = D.h (D.e b) v := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← Dat.hL_apply, Dat.pXv, LinearMap.sum_apply, map_sum]
  simp only [LinearMap.smulRight_apply, map_smul, smul_eq_mul, Dat.hL_apply, H.ef, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem h_f_pX (H : D.Hyp) (b : Fin r) (v : n → A) : D.h (D.f b) (D.pX v) = D.h (D.f b) v := by
  have hfe : ∀ a, D.h (D.f b) (D.e a) = if b = a then 1 else 0 := by
    intro a
    rw [Dat.h_symm H (D.e a) (D.f b), H.ef]
    by_cases hab : a = b
    · subst hab; simp
    · rw [if_neg hab, if_neg (Ne.symm hab), map_zero]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← Dat.hL_apply, Dat.pX, LinearMap.sum_apply, map_sum]
  simp only [LinearMap.smulRight_apply, map_smul, smul_eq_mul, Dat.hL_apply, hfe, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem h_f_pXv (H : D.Hyp) (b : Fin r) (v : n → A) : D.h (D.f b) (D.pXv v) = 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← Dat.hL_apply, Dat.pXv, LinearMap.sum_apply, map_sum]
  simp only [LinearMap.smulRight_apply, map_smul, smul_eq_mul, Dat.hL_apply, H.ff, mul_zero,
    Finset.sum_const_zero]


variable (D) in
def pL : (n → A) →ₗ[A] (n → A) := LinearMap.id - D.pX - D.pXv

theorem pL_apply (v : n → A) : pL D v = v - D.pX v - D.pXv v := rfl

theorem h_e_pL (H : D.Hyp) (b : Fin r) (v : n → A) : D.h (D.e b) (pL D v) = 0 := by
  have h0 : D.h (D.e b) (D.pX v) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Dat.hL_apply, Dat.pX, LinearMap.sum_apply, map_sum]
    simp only [LinearMap.smulRight_apply, map_smul, smul_eq_mul, Dat.hL_apply, H.ee, mul_zero,
      Finset.sum_const_zero]
  rw [pL_apply, ← Dat.hL_apply, map_sub, map_sub]
  simp only [Dat.hL_apply]
  rw [h0, h_e_pXv H]
  ring

theorem h_f_pL (H : D.Hyp) (b : Fin r) (v : n → A) : D.h (D.f b) (pL D v) = 0 := by
  rw [pL_apply, ← Dat.hL_apply, map_sub, map_sub]
  simp only [Dat.hL_apply]
  rw [h_f_pX H, h_f_pXv H]
  ring

theorem pL_of {v : n → A} (he : ∀ a, D.h (D.e a) v = 0) (hf : ∀ a, D.h (D.f a) v = 0) :
    pL D v = v := by
  have h1 : D.pX v = 0 := by
    simp only [Dat.pX, LinearMap.sum_apply, LinearMap.smulRight_apply, Dat.hL_apply, hf, zero_smul,
      Finset.sum_const_zero]
  have h2 : D.pXv v = 0 := by
    simp only [Dat.pXv, LinearMap.sum_apply, LinearMap.smulRight_apply, Dat.hL_apply, he, zero_smul,
      Finset.sum_const_zero]
  rw [pL_apply, h1, h2, sub_zero, sub_zero]

theorem pL_pL (H : D.Hyp) (v : n → A) : pL D (pL D v) = pL D v :=
  pL_of (fun a => h_e_pL H a v) (fun a => h_f_pL H a v)

theorem fix_of_pL_zero {S : (n → A) →ₗ[A] (n → A)} (hSe : ∀ a, S (D.e a) = D.e a)
    (hSf : ∀ a, S (D.f a) = D.f a) {u : n → A} (hu : pL D u = 0) : S u = u := by
  have hu' : u = D.pX u + D.pXv u := by
    rw [pL_apply, sub_sub, sub_eq_zero] at hu
    exact hu
  rw [hu', map_add (f := _)]
  congr 1
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [Dat.pX, LinearMap.sum_apply, LinearMap.smulRight_apply, map_sum, map_smul, hSe]
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [Dat.pXv, LinearMap.sum_apply, LinearMap.smulRight_apply, map_sum, map_smul, hSf]

end DatL

section Wp

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ} {P : Frame E M r} {T : F}

theorem mem_Wp_iff (H : (datR R σ J P T).Hyp) (v : Fin M → R ⊗[F] E) :
    v ∈ NC.Wp R σ J P ↔ DatL.pL (datR R σ J P T) v = v := by
  constructor
  · rintro ⟨he, hf⟩
    exact DatL.pL_of (fun a => he a) (fun a => hf a)
  · intro h
    change (∀ a, _) ∧ (∀ a, _)
    refine ⟨fun a => ?_, fun a => ?_⟩
    · have h1 := DatL.h_e_pL H a v
      rw [h] at h1
      exact h1
    · have h1 := DatL.h_f_pL H a v
      rw [h] at h1
      exact h1

theorem lin_mem_Wp {h : HA R σ J} (hh : h ∈ Hsub R σ J P) {w : Fin M → R ⊗[F] E}
    (hw : w ∈ NC.Wp R σ J P) : lin R σ J h w ∈ NC.Wp R σ J P := by
  obtain ⟨he, hf⟩ := hw
  have hfix : ∀ i, lin R σ J h (ratV (F := F) R (tupH P i)) = ratV (F := F) R (tupH P i) :=
    fun i => congrFun (MulAction.mem_stabilizer_iff.mp hh) i
  change (∀ a, _) ∧ (∀ a, _)
  refine ⟨fun a => ?_, fun a => ?_⟩
  · have h1 := hfix (Fin.castAdd r (Fin.castSucc a))
    simp only [tupH, F0, Fin.append_left, Fin.snoc_castSucc] at h1
    rw [← h1, hR_lin]
    exact he a
  · have h1 := hfix (Fin.natAdd (r + 1) a)
    simp only [tupH, Fin.append_right] at h1
    rw [← h1, hR_lin]
    exact hf a

def linWp {h : HA R σ J} (hh : h ∈ Hsub R σ J P) (w : NC.Wp R σ J P) : NC.Wp R σ J P :=
  ⟨lin R σ J h w, lin_mem_Wp hh w.2⟩

end Wp

section Af

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ} {P : Frame E M r} {T : F}

theorem sc_tens : SecondCountableTopology (Af F ⊗[F] E) := by
  haveI := PI.LevelKSplit.W.SC.finite_adeles_secondCountable F
  infer_instance

theorem wp_map (hσσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (hP : P.IsStd σ J T)
    (hV : PI.LevelKSplit.W.CD.ModV F E σ M J) {h : HA (Af F) σ J} (hh : h ∈ Hsub (Af F) σ J P)
    (μ : Measure (NC.Wp (Af F) σ J P)) (hμ : μ.IsAddHaarMeasure) : μ.map (linWp hh) = μ := by
  haveI := sc_tens (F := F) (E := E)
  have H := datR_hyp (R := Af F) hσσ hJ hP
  have hfix : ∀ i, lin (Af F) σ J h (ratV (F := F) (Af F) (tupH P i)) = ratV (F := F) (Af F) (tupH P i) :=
    fun i => congrFun (MulAction.mem_stabilizer_iff.mp hh) i
  have hSe : ∀ a, lin (Af F) σ J h ((datR (Af F) σ J P T).e a) = (datR (Af F) σ J P T).e a := by
    intro a
    have h1 := hfix (Fin.castAdd r (Fin.castSucc a))
    simp only [tupH, F0, Fin.append_left, Fin.snoc_castSucc] at h1
    exact h1
  have hSf : ∀ a, lin (Af F) σ J h ((datR (Af F) σ J P T).f a) = (datR (Af F) σ J P T).f a := by
    intro a
    have h1 := hfix (Fin.natAdd (r + 1) a)
    simp only [tupH, Fin.append_right] at h1
    exact h1
  refine map_eq_of_split (DatL.pL (datR (Af F) σ J P T)).toAddMonoidHom ?_
    (fun v => DatL.pL_pL H v) (NC.Wp (Af F) σ J P) (fun v => mem_Wp_iff H v)
    (lin (Af F) σ J h).toAddMonoidHom ?_ (fun u hu => DatL.fix_of_pL_zero hSe hSf hu)
    (fun ν hν => hV hJ hσσ h ν hν) (linWp hh) (fun w => rfl) μ hμ
  · exact LinearMap.continuous_on_pi _
  · exact LinearMap.continuous_on_pi _

end Af

end PI.LevelKSplit.W.NCA
end
end

noncomputable section

namespace PI.LevelKSplit.W.NCA

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory Topology
open PI.LevelKSplit PI.LevelKSplit.W.NC PI.LevelKSplit.W.SemiA PI.VolSemiDirect.W
open scoped TensorProduct

theorem conjInv_of_one {X : Type} [Group X] [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] (N H : Subgroup X) (hN : LCSC N)
    (hex : ∀ h ∈ H, ∃ μ0 : Measure N, μ0.IsHaarMeasure ∧ ∀ f : X → ENNReal, Measurable f →
      ∫⁻ n, f (h * (n : X) * h⁻¹) ∂μ0 = ∫⁻ n, f (n : X) ∂μ0) : ConjInv N H := by
  obtain ⟨hlc, hsc, ht2, htg⟩ := hN
  intro μN hμN h hh f hf
  obtain ⟨μ0, hμ0, hinv⟩ := hex h hh
  rw [Measure.isMulLeftInvariant_eq_smul μN μ0, lintegral_smul_measure, lintegral_smul_measure,
    hinv f hf]

section Af

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [FiniteDimensional F E] {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E}

theorem conjNH_of (hC : NCoord F E σ M J) (hV : PI.LevelKSplit.W.CD.ModV F E σ M J) :
    PI.LevelKSplit.W.ExS.ConjNH F E σ M J := by
  intro hJ hσσ r P T hP
  have hsc : SecondCountableTopology (Af F) := PI.LevelKSplit.W.SC.finite_adeles_secondCountable F
  have hL : LCSC (HA (Af F) σ J) := PI.LevelKSplit.W.ExS.lcsc_HAf hsc
  have : BorelSpace (HA (Af F) σ J) := ⟨rfl⟩
  have : SecondCountableTopology (HA (Af F) σ J) := hL.2.1
  obtain ⟨-, cN, -⟩ := PI.LevelKSplit.W.ExC.closed_SNH hJ hσσ P T hP
  obtain ⟨lN, -⟩ := subgroup_locally_compact_holds (HA (Af F) σ J) ⊥ _ hL cN inferInstance inferInstance
  refine conjInv_of_one _ _ lN ?_
  intro h hh
  obtain ⟨A, Z, Ψ, cA, cZ, hleft, hconj⟩ := hC hJ hσσ r P T hP
  obtain ⟨⟨lcA, scA, t2A, tgA⟩, -⟩ :=
    subgroup_locally_compact_holds (HA (Af F) σ J) ⊥ A hL cA inferInstance inferInstance
  obtain ⟨⟨lcZ, scZ, t2Z, tgZ⟩, -⟩ :=
    subgroup_locally_compact_holds (HA (Af F) σ J) ⊥ Z hL cZ inferInstance inferInstance
  obtain ⟨lcN, scN, t2N, tgN⟩ := lN
  have : BorelSpace A := Subtype.borelSpace _
  have : BorelSpace Z := Subtype.borelSpace _
  have : BorelSpace (Nsub (Af F) σ J P) := Subtype.borelSpace _
  have : SecondCountableTopology (Af F ⊗[F] E) := sc_tens
  have : BorelSpace (Af F ⊗[F] E) := ⟨rfl⟩
  have : BorelSpace (Fin M → Af F ⊗[F] E) := Pi.borelSpace
  have H := SemiA.datR_hyp (R := Af F) hσσ hJ hP
  have cW : IsClosed ((NC.Wp (Af F) σ J P : AddSubgroup (Fin M → Af F ⊗[F] E)) :
      Set (Fin M → Af F ⊗[F] E)) := by
    have e1 : ((NC.Wp (Af F) σ J P : AddSubgroup (Fin M → Af F ⊗[F] E)) : Set (Fin M → Af F ⊗[F] E)) =
        {v | PI.LevelKSplit.W.NCA.DatL.pL (SemiA.datR (Af F) σ J P T) v = v} := by
      ext v
      exact mem_Wp_iff H v
    rw [e1]
    exact isClosed_eq (LinearMap.continuous_on_pi _) continuous_id
  have : LocallyCompactSpace (NC.Wp (Af F) σ J P) := cW.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology (NC.Wp (Af F) σ J P) :=
    TopologicalSpace.secondCountableTopology_induced _ _ Subtype.val
  have : BorelSpace (NC.Wp (Af F) σ J P) := Subtype.borelSpace _
  have : BorelSpace (Fin r → NC.Wp (Af F) σ J P) := Pi.borelSpace
  have : BorelSpace ((Fin r → NC.Wp (Af F) σ J P) × Z) := Prod.borelSpace
  have : BorelSpace (A × ((Fin r → NC.Wp (Af F) σ J P) × Z)) := Prod.borelSpace
  let μA : Measure A := Measure.haar
  let μZ : Measure Z := Measure.haar
  let μW : Measure (NC.Wp (Af F) σ J P) := Measure.addHaar
  let μQ : Measure (Fin r → NC.Wp (Af F) σ J P) := Measure.pi fun _ => μW
  let ρ : Measure (A × ((Fin r → NC.Wp (Af F) σ J P) × Z)) := μA.prod (μQ.prod μZ)
  have hΨm : Measurable Ψ := Ψ.continuous.measurable
  refine ⟨ρ.map Ψ, ?_, ?_⟩
  · have hli : (ρ.map Ψ).IsMulLeftInvariant := by
      refine ⟨fun n0 => ?_⟩
      obtain ⟨a0, t, c, ht, hc, hform⟩ := hleft n0
      have hcomm : (fun n => n0 * n) ∘ Ψ = Ψ ∘ (fun p : A × ((Fin r → NC.Wp (Af F) σ J P) × Z) =>
          (a0 * p.1, (p.2.1 + t p.1, c (p.1, p.2.1) * p.2.2))) := by
        funext ⟨u, y, z⟩
        exact hform u y z
      have hinner : ∀ u : A, MeasurePreserving
          (fun q : (Fin r → NC.Wp (Af F) σ J P) × Z => (q.1 + t u, c (u, q.1) * q.2))
          (μQ.prod μZ) (μQ.prod μZ) := by
        intro u
        refine (measurePreserving_add_right μQ (t u)).skew_product (g := fun y z => c (u, y) * z)
          ?_ (Filter.Eventually.of_forall fun y => map_mul_left_eq_self μZ (c (u, y)))
        exact (show Continuous fun q : (Fin r → NC.Wp (Af F) σ J P) × Z => c (u, q.1) * q.2 from
          (hc.comp (continuous_const.prodMk continuous_fst)).mul continuous_snd).measurable
      have hgm : Continuous fun p : A × ((Fin r → NC.Wp (Af F) σ J P) × Z) =>
          (p.2.1 + t p.1, c (p.1, p.2.1) * p.2.2) :=
        (continuous_snd.fst.add (ht.comp continuous_fst)).prodMk
          ((hc.comp (continuous_fst.prodMk continuous_snd.fst)).mul continuous_snd.snd)
      have hT : MeasurePreserving (fun p : A × ((Fin r → NC.Wp (Af F) σ J P) × Z) =>
          (a0 * p.1, (p.2.1 + t p.1, c (p.1, p.2.1) * p.2.2))) ρ ρ :=
        (measurePreserving_mul_left μA a0).skew_product
          (g := fun (u : A) (q : (Fin r → NC.Wp (Af F) σ J P) × Z) => (q.1 + t u, c (u, q.1) * q.2)) hgm.measurable
          (Filter.Eventually.of_forall fun u => (hinner u).map_eq)
      rw [Measure.map_map (measurable_const_mul n0) hΨm, hcomm, ← Measure.map_map hΨm hT.measurable,
        hT.map_eq]
    have hfc : IsFiniteMeasureOnCompacts (ρ.map Ψ) := Measure.IsFiniteMeasureOnCompacts.map ρ Ψ
    have hop : (ρ.map Ψ).IsOpenPosMeasure := Ψ.continuous.isOpenPosMeasure_map Ψ.surjective
    have := hfc
    have := hli
    have := hop
    exact Measure.IsHaarMeasure.mk
  · intro f hf
    have hF : Measurable fun n : Nsub (Af F) σ J P => f (h * (n : HA (Af F) σ J) * h⁻¹) :=
      hf.comp ((continuous_const.mul continuous_subtype_val).mul continuous_const).measurable
    have hF0 : Measurable fun n : Nsub (Af F) σ J P => f (n : HA (Af F) σ J) :=
      hf.comp continuous_subtype_val.measurable
    have hlinm : Measurable (linWp hh) :=
      (((LinearMap.continuous_on_pi (lin (Af F) σ J h)).comp continuous_subtype_val).subtype_mk
        _).measurable
    let Lq : (Fin r → NC.Wp (Af F) σ J P) → (Fin r → NC.Wp (Af F) σ J P) := fun y a => linWp hh (y a)
    have hLq : MeasurePreserving Lq μQ μQ :=
      measurePreserving_pi (fun _ => μW) (fun _ => μW)
        (fun _ => ⟨hlinm, wp_map hσσ hJ hP hV hh μW inferInstance⟩)
    have hT : MeasurePreserving (Prod.map id (Prod.map Lq id)) ρ ρ :=
      (MeasurePreserving.id μA).prod (hLq.prod (MeasurePreserving.id μZ))
    rw [lintegral_map hF hΨm, lintegral_map hF0 hΨm]
    calc ∫⁻ p, f (h * (Ψ p : HA (Af F) σ J) * h⁻¹) ∂ρ
        = ∫⁻ p, f (Ψ (Prod.map id (Prod.map Lq id) p) : HA (Af F) σ J) ∂ρ := by
          congr 1
          funext ⟨u, y, z⟩
          obtain ⟨y', hy', he⟩ := hconj h hh u y z
          have e2 : y' = Lq y := funext fun a => Subtype.ext (hy' a)
          show f (h * (Ψ (u, y, z) : HA (Af F) σ J) * h⁻¹) = f (Ψ (u, Lq y, z) : HA (Af F) σ J)
          rw [he, e2]
      _ = ∫⁻ p, f (Ψ p : HA (Af F) σ J) ∂ρ :=
          hT.lintegral_comp (show Measurable fun p => f (Ψ p : HA (Af F) σ J) from
            hf.comp (continuous_subtype_val.comp Ψ.continuous).measurable)

theorem normal_conjugation_hypothesis : NCAsm F E σ M J := fun hC hV => conjNH_of hC hV

end Af

theorem normal_conjugation_all : NCAsmAll := by
  intro F E _ _ _ _ _ σ hσ M J hJ
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  exact normal_conjugation_hypothesis

end PI.LevelKSplit.W.NCA
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.SemiTop
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.MulInvPiGMemN
noncomputable section

namespace PI.LevelKSplit.W.SemiA

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
open scoped TensorProduct

section R

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ} {P : Frame E M r} {T : F}
  (hσσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (hP : P.IsStd σ J T)
include hσσ hJ hP

theorem piG_mem_H (g : HA R σ J) (hg : g ∈ Ssub R σ J P) : piG hσσ hJ hP g hg ∈ Hsub R σ J P := by
  have H := datR_hyp (R := R) hσσ hJ hP
  unfold Hsub
  rw [mem_stabT]
  intro b
  rw [lin_piG]
  refine Fin.addCases (fun b => ?_) (fun b => ?_) b
  · rw [tupH, Fin.append_left]
    refine Fin.lastCases ?_ (fun a => ?_) b
    · rw [F0, Fin.snoc_last]
      exact SemiG.Dat.unipotent_proj_fixes_normal H _
    · rw [F0, Fin.snoc_castSucc]
      exact SemiG.Dat.Pi_e H _ a
  · rw [tupH, Fin.append_right]
    exact SemiG.Dat.Pi_f H _ b

theorem piG_of_H {h : HA R σ J} (hh : h ∈ Hsub R σ J P) (hg : h ∈ Ssub R σ J P) :
    piG hσσ hJ hP h hg = h := by
  have hext : ∀ {g₁ g₂ : HA R σ J}, (∀ x, lin R σ J g₁ x = lin R σ J g₂ x) → g₁ = g₂ := by
    intro g₁ g₂ hgg
    have hm : ((HA.mat R σ J g₁ : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) =
        (HA.mat R σ J g₂ : GL (Fin M) (R ⊗[F] E)) := by
      ext i j
      have h1 := hgg (Pi.single j 1)
      simp only [lin, Matrix.mulVecLin_apply, Matrix.mulVec_single_one] at h1
      exact congrFun h1 i
    exact Subtype.ext (Units.ext hm)
  have H := datR_hyp (R := R) hσσ hJ hP
  unfold Hsub at hh
  rw [mem_stabT] at hh
  have he : ∀ a, lin R σ J h (ratV (F := F) R (P.e a)) = ratV (F := F) R (P.e a) := fun a => by
    have h1 := hh (Fin.castAdd r (Fin.castSucc a))
    rwa [tupH, Fin.append_left, F0, Fin.snoc_castSucc] at h1
  have hz : lin R σ J h (ratV (F := F) R P.z) = ratV (F := F) R P.z := by
    have h1 := hh (Fin.castAdd r (Fin.last r))
    rwa [tupH, Fin.append_left, F0, Fin.snoc_last] at h1
  have hf : ∀ a, lin R σ J h (ratV (F := F) R (P.f a)) = ratV (F := F) R (P.f a) := fun a => by
    have h1 := hh (Fin.natAdd (r + 1) a)
    rwa [tupH, Fin.append_right] at h1
  refine hext fun x => ?_
  rw [lin_piG]
  exact SemiG.Dat.Pi_of_fix H ⟨he, hz⟩ hf (uni_lin h) x

theorem piG_of_N {n : HA R σ J} (hn : n ∈ Nsub R σ J P) (hg : n ∈ Ssub R σ J P) :
    piG hσσ hJ hP n hg = 1 := by
  have hext : ∀ {g₁ g₂ : HA R σ J}, (∀ x, lin R σ J g₁ x = lin R σ J g₂ x) → g₁ = g₂ := by
    intro g₁ g₂ hgg
    have hm : ((HA.mat R σ J g₁ : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) =
        (HA.mat R σ J g₂ : GL (Fin M) (R ⊗[F] E)) := by
      ext i j
      have h1 := hgg (Pi.single j 1)
      simp only [lin, Matrix.mulVecLin_apply, Matrix.mulVec_single_one] at h1
      exact congrFun h1 i
    exact Subtype.ext (Units.ext hm)
  have H := datR_hyp (R := R) hσσ hJ hP
  obtain ⟨-, hn2⟩ := hn
  refine hext fun x => ?_
  rw [lin_piG, lin_one]
  refine SemiG.Dat.Pi_of_N H (fun v hv => spanR_le Set.univ (hn2 v fun a => ?_)) x
  have h1 := hv a
  rwa [datR_h] at h1

theorem piG_mul {g g' : HA R σ J} (hg : g ∈ Ssub R σ J P) (hg' : g' ∈ Ssub R σ J P) :
    piG hσσ hJ hP (g * g') ((Ssub R σ J P).mul_mem hg hg') =
      piG hσσ hJ hP g hg * piG hσσ hJ hP g' hg' := by
  have hext : ∀ {g₁ g₂ : HA R σ J}, (∀ x, lin R σ J g₁ x = lin R σ J g₂ x) → g₁ = g₂ := by
    intro g₁ g₂ hgg
    have hm : ((HA.mat R σ J g₁ : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) =
        (HA.mat R σ J g₂ : GL (Fin M) (R ⊗[F] E)) := by
      ext i j
      have h1 := hgg (Pi.single j 1)
      simp only [lin, Matrix.mulVecLin_apply, Matrix.mulVec_single_one] at h1
      exact congrFun h1 i
    exact Subtype.ext (Units.ext hm)
  refine hext fun x => ?_
  rw [lin_piG, lin_mul, lin_piG, lin_piG, Pi_lin_mul hσσ hJ hP hg hg']
  rfl

theorem mul_inv_piG_mem_N {s : HA R σ J} (hs : s ∈ Ssub R σ J P) :
    s * (piG hσσ hJ hP s hs)⁻¹ ∈ Nsub R σ J P := by
  have H := datR_hyp (R := R) hσσ hJ hP
  set π := piG hσσ hJ hP s hs with hπ
  have hpe : ∀ b, lin R σ J π (ratV (F := F) R (P.e b)) = ratV (F := F) R (P.e b) := fun b => by
    rw [hπ, lin_piG]
    exact SemiG.Dat.Pi_e H _ b
  have hpie : ∀ b, lin R σ J π⁻¹ (ratV (F := F) R (P.e b)) = ratV (F := F) R (P.e b) := fun b => by
    conv_lhs => rw [← hpe b]
    rw [lin_inv_lin]
  refine ⟨fun b => ?_, fun v hv => ?_⟩
  · rw [lin_mul, hpie]
    exact S_e hs b
  · set u := lin R σ J π⁻¹ v with hu
    have hu' : ∀ a, (datR R σ J P T).h ((datR R σ J P T).e a) u = 0 := fun a => by
      rw [datR_h]
      show hR R σ J (ratV (F := F) R (P.e a)) u = 0
      rw [← hR_lin π, hpe, hu, lin_lin_inv]
      exact hv a
    have hZ : lin R σ J s (datR R σ J P T).z - (datR R σ J P T).z ∈
        Submodule.span (R ⊗[F] E) (Set.range (datR R σ J P T).e) :=
      spanR_le Set.univ (stabilizer_fixes_tail_coords hs)
    have h1 := SemiG.Dat.N_part H (mapX_S hs) (mapW_S hs) hZ u hu'
    have h2 : (datR R σ J P T).Pi (lin R σ J s) u = v := by
      rw [← lin_piG hσσ hJ hP s hs, ← hπ, hu, lin_lin_inv]
    rw [h2] at h1
    rw [lin_mul, ← hu]
    exact span_le_spanR h1

end R

end PI.LevelKSplit.W.SemiA
end
end

noncomputable section

namespace PI.LevelKSplit.W.SemiT

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub PI.LevelKSplit.W.SemiA
open scoped TensorProduct

section Cont

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] {R : Type}
  [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ} {P : Frame E M r} {T : F}

theorem piMat_eq (g : HA R σ J) :
    piMat (P := P) (T := T) g = LinearMap.toMatrix' (datR R σ J P T).pU +
      LinearMap.toMatrix' (datR R σ J P T).pW *
        ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *
          LinearMap.toMatrix' (datR R σ J P T).pW := by
  rw [piMat, PI.LevelKSplit.W.SemiG.Dat.Pi, map_add (f := _), LinearMap.toMatrix'_comp,
    LinearMap.toMatrix'_comp, lin, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin', Matrix.mul_assoc]

theorem continuous_piMat : Continuous fun g : HA R σ J => piMat (P := P) (T := T) g := by
  have hm : Continuous fun g : HA R σ J =>
      ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) :=
    Units.continuous_val.comp continuous_subtype_val
  have he : (fun g : HA R σ J => piMat (P := P) (T := T) g) = fun g =>
      LinearMap.toMatrix' (datR R σ J P T).pU + LinearMap.toMatrix' (datR R σ J P T).pW *
        ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *
          LinearMap.toMatrix' (datR R σ J P T).pW := funext piMat_eq
  rw [he]
  exact continuous_const.add ((continuous_const.matrix_mul hm).matrix_mul continuous_const)

theorem continuous_piMat_inv : Continuous fun g : HA R σ J => piMat (P := P) (T := T) g⁻¹ := by
  exact (continuous_piMat (P := P) (T := T)).comp continuous_inv


variable (R) in
def fwdM (hP : P.IsStd σ J T) (p : Nsub R σ J P × Hsub R σ J P) : Ssub R σ J P :=
  ⟨(p.1 : HA R σ J) * (p.2 : HA R σ J), (Ssub R σ J P).mul_mem (N_le_S' (R := R) hP p.1.2) (H_le_S p.2.2)⟩

theorem continuous_fwdM (hP : P.IsStd σ J T) : Continuous (fwdM R hP) := by
  apply continuous_induced_rng.2
  exact (continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)

variable (hσσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (hP : P.IsStd σ J T)
include hσσ hJ hP

theorem continuous_piG : Continuous fun s : Ssub R σ J P => piG hσσ hJ hP (s : HA R σ J) s.2 := by
  apply continuous_induced_rng.2
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact (continuous_piMat (P := P) (T := T)).comp continuous_subtype_val
  · exact (continuous_piMat_inv (P := P) (T := T)).comp continuous_subtype_val


variable (R) in
def bwdM (s : Ssub R σ J P) : Nsub R σ J P × Hsub R σ J P :=
  (⟨(s : HA R σ J) * (piG (R := R) hσσ hJ hP (s : HA R σ J) s.2)⁻¹, mul_inv_piG_mem_N hσσ hJ hP s.2⟩,
    ⟨piG (R := R) hσσ hJ hP (s : HA R σ J) s.2, piG_mem_H hσσ hJ hP (s : HA R σ J) s.2⟩)

theorem continuous_bwdM : Continuous (bwdM R hσσ hJ hP) := by
  have hpi := continuous_piG (R := R) hσσ hJ hP
  refine Continuous.prodMk ?_ ?_
  · apply continuous_induced_rng.2
    exact continuous_subtype_val.mul hpi.inv
  · apply continuous_induced_rng.2
    exact hpi

theorem bwd_fwd : Function.LeftInverse (bwdM R hσσ hJ hP) (fwdM R hP) := by
  rintro ⟨n, h⟩
  have hnS := N_le_S' (R := R) hP n.2
  have hhS := H_le_S (R := R) h.2
  have key : piG (R := R) hσσ hJ hP ((n : HA R σ J) * (h : HA R σ J))
      ((Ssub R σ J P).mul_mem hnS hhS) = h := by
    rw [piG_mul hσσ hJ hP hnS hhS, piG_of_N hσσ hJ hP n.2 hnS, piG_of_H hσσ hJ hP h.2 hhS, one_mul]
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · show (n : HA R σ J) * (h : HA R σ J) *
      (piG (R := R) hσσ hJ hP ((n : HA R σ J) * (h : HA R σ J)) _)⁻¹ = n
    rw [key, mul_inv_cancel_right]
  · exact key

theorem fwd_bwd : Function.RightInverse (bwdM R hσσ hJ hP) (fwdM R hP) := by
  intro s
  apply Subtype.ext
  exact inv_mul_cancel_right _ _


variable (R) in
def homeoNH : (Nsub R σ J P × Hsub R σ J P) ≃ₜ Ssub R σ J P where
  toFun := fwdM R hP
  invFun := bwdM R hσσ hJ hP
  left_inv := bwd_fwd hσσ hJ hP
  right_inv := fwd_bwd hσσ hJ hP
  continuous_toFun := continuous_fwdM hP
  continuous_invFun := continuous_bwdM (R := R) hσσ hJ hP

theorem semi_gen : PI.VolSemiDirect.W.Semi (Ssub R σ J P) (Nsub R σ J P) (Hsub R σ J P) :=
  ⟨fun _ hh _ hn => norm_N hh hn, homeoNH R hσσ hJ hP, fun _ => rfl⟩

end Cont

theorem semidirect_topological_all : PI.LevelKSplit.W.ExS.SemiNHSAll := by
  unfold PI.LevelKSplit.W.ExS.SemiNHSAll PI.LevelKSplit.ForAllCM PI.LevelKSplit.W.ExS.SemiNHS
  intro F E _ _ _ _ _ σ _ M J _ hJ hσσ r P T hP
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  exact semi_gen hσσ hJ hP

end PI.LevelKSplit.W.SemiT
end
end

namespace PI.LevelKSplit.W.Top6

theorem levelSplitting_of_heisenberg_levi (hH : PI.LevelKSplit.W.NC.HeisPAll) (hL : PI.LevelKSplit.W.NC.LevPAll) :
    PI.LevelKSplit.LevelSAll :=
  PI.LevelKSplit.W.NC.levelSAll_of_semiNHS_heis_lev PI.LevelKSplit.W.SemiT.semidirect_topological_all hH hL
    PI.LevelKSplit.W.MVA.modulus_all_extensions PI.LevelKSplit.W.NCA.normal_conjugation_all

end PI.LevelKSplit.W.Top6
