module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.IntIffNorm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.NewformAut0
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.InertiaRankTwo.LocalConditionRankThreeLinkOfInertiaOrdinary
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.InertiaRankTwo.FlagAll
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TLinkedRig
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TSolDescent
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.EndsRankThreeOfLocal

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.RigidEndTwoWOfPrintedAdjointLifting
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.RigidityEndomorphismWeightTwo
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.GalN.V
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.HV GlobalTheory.GalOfCusp UpperTheory.V.Th
open UpperTheory.V.U3 UpperTheory.V.Base in
def UpperTheory.GalN.V.RigidityEndomorphismWeightTwo : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : Coef l)
    [CharP (ResidueField c.O) l] (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (η : G ℚ Ω →* ℤˣ) (σ g₁ : G ℚ Ω)
    (B : ValuationSubring Ω) (M : ℕ), Pr.LinkHyp c N e η σ B M → Chr.Psi l e (Chr.dirG ℚ Ω ψ) σ = 1 →
    Pr.HasFrame c η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ B M →
    ∀ (A : Subalgebra c.O (PadicAlgCl l)) [IsDiscreteValuationRing A] [Module.Finite c.O A]
      (r : G ℚ Ω →* GG (m := 3) (R := A)),
      Pr.OrdPt l η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B r → TypeII η (UnitaryThreeInertia.push A.val r) → (∀ g ∈ η.ker, (r g).mat 1 1 = 1) →
      ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra K Ω], Module.finrank ℚ K = 2 → η.ker = galOf ℚ K Ω →
      ∀ W : G ℚ Ω →* GL (Fin 2) (Qbar l), Continuous W → (∀ g ∈ η.ker, (W g).val = corner (UnitaryThreeInertia.push A.val r g).mat) →
      (∀ g, (W g).val.det = ((η g : ℤˣ) : ℤ)) →
      (∃ π : GlobalTheory.CuspRep.CuspSub K 2, (GlobalTheory.CuspRep.CG.mk π).IsRegAlg ∧
        Af.AttC ι (W.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω)) π) →
      _root_.UpperTheory.V.Z.Win.WitA ι (W.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω)) → FreeAt l W → AdZero2 K η W
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.GalN.V
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.HV GlobalTheory.GalOfCusp UpperTheory.V.Th
open UpperTheory.V.Z.Win in
theorem UpperTheory.V.Z.Win.Dn.rigid_end_two_w_of_printed_adjoint_lifting :
    _root_.UpperTheory.V.Af.HypothesesH' → _root_.UpperTheory.V.Th.AdjointLiftingTheorem → _root_.UpperTheory.GalN.V.RigidityEndomorphismWeightTwo := by
  intro hH hAd Ω _ _ _ l _ ι c _ N _ e ψ η σ g₁ B M H hΨσ hF A _ _ r hr hII h11 K _ _ _ _ hK2 hK W hWc hW hdet haut hWit hfree θ hθ R hR
  obtain ⟨L, _, _, _, _, g₂, Φ, C₀, ⟨k⟩, hok, hbig, hseed⟩ := hF
  haveI := Db.algClo L Ω
  haveI := Db.algClo K Ω
  obtain ⟨-, ka, hka, hrig⟩ := _root_.UpperTheory.V.Th.linked_rigid_of_printed_adjoint_lifting hH hAd Ω l ι c N e ψ η σ g₂ B M H L Φ C₀ k hok hbig hseed
  have hof := UpperTheory.V.Z.Keep.ordFlag2 Ω l c N e ψ η σ g₂ B M H L Φ C₀ k hok A r
  generalize Chr.Psi l e (Chr.dirG ℚ Ω ψ) = Ψ at *
  have hl : l ∣ M := (dvd_mul_right l N).trans H.dvd
  have hσ : σ * σ = 1 := Db.cc_sq H.cc
  have hmk := Pr.marks_of_link k hok hl hσ hΨσ
  have hLη := Db.galL_le k
  obtain ⟨_, _⟩ := Db.algKL K L Ω (hK ▸ hLη)
  obtain ⟨_, hsol⟩ := Db.galKL K L k.ab
  haveI := Db.locHom c A
  haveI := (isNoetherianRing_iff_ideal_fg A).2 fun I => (IsPrincipalIdealRing.principal I).fg
  haveI : Normal ℚ L := k.ab.toIsGalois.to_normal
  have hb : U3.Block η r := fun g hg a b hab => Subtype.ext (hII.1 g hg a b hab)
  have hg₂ : g₂ ∈ η.ker := hmk.ηg
  have hgs : U3.gstar σ g₂ ∈ η.ker := by
    show η (σ * g₂⁻¹ * σ) = 1
    rw [map_mul, map_mul, map_inv, hmk.ηg, hmk.ηc]
    simp
  have hr' : Pr.OrdPt l η Ψ σ g₂ B r :=
    ⟨hr.red, hr.cont, ⟨hr.norm.atc,
      by rw [U3.zmat, Matrix.sub_apply, hb _ hg₂ _ _ (by decide), hb _ hgs _ _ (by decide), sub_zero],
      by rw [U3.zmat, Matrix.sub_apply, hb _ hg₂ _ _ (by decide), hb _ hgs _ _ (by decide), sub_zero]⟩, hr.away, hr.ord⟩
  have hFl : Flagged (W.comp (Base.galEmb ℚ K Ω)) := Dn.flagAll_of K Ω l 2 _ fun w hw =>
    let ⟨A', a1, κ, a2⟩ := hof hr' hb h11 K hK _ (fun s => hW _ (hK.ge (Base.galEmb_mem ℚ K Ω s))) w hw
    ⟨A', a1, κ, a2.choose_spec.2.1⟩
  obtain ⟨ρ', h1, h2, h3⟩ := Pr.exists_nrep2 k hok hl hσ r hr' hb
  have hηL : ∀ s : G L Ω, η (Base.galEmb ℚ L Ω s) = 1 := fun s => hLη (Base.galEmb_mem ℚ L Ω s)
  have hηK : ∀ s : G K Ω, η (Base.galEmb ℚ K Ω s) = 1 := fun s => hK.ge (Base.galEmb_mem ℚ K Ω s)
  let χ : G ℚ Ω →* (ResidueField A)ˣ := (Units.map ((residue A).comp (algebraMap c.O A)).toMonoidHom).comp Ψ
  have hU : U3.MatIrr ((Base.galOf ℚ L Ω).subgroupOf η.ker) (Pr.gm (W.comp η.ker.subtype)) := by
    have irr2 {G κ k A : Type} [Group G] [Field κ] [IsAlgClosed κ] [Field k] [CommRing A]
        (r : G →* GL (Fin 2) κ) (hr : U3.MatIrr ⊤ (Pr.gm r)) (j : A →+* κ) (hj : Function.Injective j) (φ : A →+* k)
        (χ : G →* kˣ) (t : G → A) (ht : ∀ g, j (t g) = (Pr.gm r g).trace)
        (hχ : ∀ g, φ (t g) = (χ g : kˣ) + ((χ g)⁻¹ : kˣ)) (U : Subgroup G) [U.Normal] {u : G} (hu : u ∈ U)
        (hd : (Pr.gm r u).det = 1) (hne : χ u ^ 2 ≠ 1) : U3.MatIrr U (Pr.gm r) := by
      have hy : ((χ u : kˣ) : k) ^ 2 - 1 ≠ 0 := fun h => hne (Units.ext (by simpa [sub_eq_zero] using h))
      rcases Pr.cliffPrime G κ 2 Nat.prime_two r hr U with h | h | ⟨b, la, π, -, hla, hπ, htr⟩
      · exact h
      · exfalso
        obtain ⟨a, ha⟩ := h u hu
        have e : t u ^ 2 = 4 := by
          apply hj
          rw [map_pow, ht, map_ofNat]
          rw [ha] at hd ⊢
          simp only [Matrix.det_smul, Matrix.det_one, Fintype.card_fin, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul] at hd ⊢
          push_cast
          linear_combination 4 * hd
        have e2 := congrArg φ e
        rw [map_pow, hχ, map_ofNat] at e2
        have e3 := (χ u).mul_inv
        apply pow_ne_zero 2 hy
        linear_combination ((χ u : kˣ) : k) ^ 2 * e2 - (2 * ((χ u : kˣ) : k) ^ 2 + (χ u : kˣ) * ((χ u)⁻¹ : kˣ) + 1) * e3
      · exfalso
        obtain ⟨g, hg⟩ := htr 0 1
        have hne' : ∀ i, π g i ≠ i := by
          intro i hi
          fin_cases i
          · exact absurd (hg.symm.trans hi) (by decide)
          · exact absurd ((π g).injective (hg.trans hi.symm)) (by decide)
        have tr0 : ∀ s ∈ U, (Pr.gm r (g * s)).trace = 0 := fun s hs => by
          rw [← Matrix.trace_toLin'_eq, LinearMap.trace_eq_matrix_trace κ b]
          refine Finset.sum_eq_zero fun i _ => ?_
          obtain ⟨a, ha⟩ := hπ g i
          have := hla i ⟨s, hs⟩
          simp only [Pr.gm] at this ha
          rw [Matrix.diag_apply, LinearMap.toMatrix_apply, Matrix.toLin'_apply]
          simp only [Pr.gm, map_mul, Units.val_mul, ← Matrix.mulVec_mulVec]
          rw [this, Matrix.mulVec_smul, ha]
          simp [hne' i]
        have z : ∀ s ∈ U, ((χ (g * s) : kˣ) : k) ^ 2 + 1 = 0 := fun s hs => by
          have e : t (g * s) = 0 := hj (by rw [ht, tr0 s hs, map_zero])
          have e2 := hχ (g * s)
          rw [e, map_zero] at e2
          have e3 := (χ (g * s)).mul_inv
          linear_combination -((χ (g * s) : kˣ) : k) * e2 - e3
        have z1 := z 1 U.one_mem
        have z2 := z u hu
        rw [mul_one] at z1
        rw [map_mul, Units.val_mul] at z2
        apply hy
        linear_combination ((χ u : kˣ) : k) ^ 2 * z1 - z2
    refine irr2 (W.comp η.ker.subtype) (fun V hV => hII.2 V fun g hg v hv => ?_) (A.val : A →+* PadicAlgCl l)
      Subtype.val_injective (residue A) (χ.comp η.ker.subtype) (fun g => (r g).mat 0 0 + (r g).mat 2 2) (fun g => ?_) (fun g => ?_)
      _ (u := ⟨g₂, hg₂⟩) ?_ ?_ ?_
    · have := hV ⟨g, hg⟩ trivial v hv
      beta_reduce
      rw [← hW g hg]
      exact this
    · show _ = (W g).val.trace
      rw [hW g g.2, Matrix.trace_fin_two, map_add (f := _)]
      rfl
    · have e2 : ∀ i, residue A ((r g).mat i i) = residue A (algebraMap c.O A ((U3.r0 η Ψ g).mat i i)) := fun i =>
        Ideal.Quotient.eq.2 (hr.red.red g i i)
      rw [map_add (f := _), e2, e2, ← map_inv]
      show _ = residue A (algebraMap c.O A (Ψ g : c.Oˣ)) + residue A (algebraMap c.O A (Ψ (g : G ℚ Ω)⁻¹ : c.Oˣ))
      simp [U3.GG.mat, U3.tor_val, U3.wt1]
    · rw [Subgroup.mem_subgroupOf, k.gal]
      exact ⟨k.g0.1, hg₂⟩
    · show (W g₂).val.det = 1
      rw [hdet, hmk.ηg]
      simp
    · intro h
      refine (hmk.Ψg.map ((residue A).comp (algebraMap c.O A))).ne_zero ?_
      rw [map_sub, map_pow, map_one, sub_eq_zero]
      have h' := congrArg Units.val h
      rw [Units.val_pow_eq_pow_val] at h'
      exact h'
  have hirr : Af.IsIrr (W.comp (Base.galEmb ℚ L Ω)) :=
    Db.irr_of_matIrr (by norm_num) (Base.galOf ℚ L Ω) (fun g => (W g).val)
      (fun V hV => hU V fun g hg v hv => hV g hg v hv) (Base.galEmb ℚ L Ω) (Base.range_galEmb ℚ L Ω).ge _ fun _ => rfl
  obtain ⟨J, hJ⟩ : ∃ J : GL (Fin 2) (Qbar l),
      ∀ M : Matrix (Fin 2) (Fin 2) (Qbar l), M.transpose * J.val * M = M.det • J.val := by
    refine ⟨⟨!![0, 1; -1, 0], !![0, -1; 1, 0], by simp [Matrix.one_fin_two],
      by simp [Matrix.one_fin_two]⟩, fun M => ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two] <;> ring
  have hpair : ∀ s : G ℚ Ω, η s = 1 →
      (W s).val.transpose * (J * (W σ)⁻¹).val * (W (σ * s * σ⁻¹)).val = (J * (W σ)⁻¹).val := fun s hs => by
    have e1 : J * (W σ)⁻¹ * W (σ * s * σ⁻¹) = J * W s * (W σ)⁻¹ := by
      rw [map_mul, map_mul, map_inv]; group
    rw [Matrix.mul_assoc, ← Units.val_mul, e1, Units.val_mul, Units.val_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hJ, hdet,
      hs, Units.val_mul]
    simp
  have halg : Af.IsAlgChar ι (1 : G ℚ Ω →* (Qbar l)ˣ) := by
    refine (_root_.UpperTheory.V.Af.algOfCyc_s hH ℚ Ω l ι).1 _ continuous_const fun w _ => ?_
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    exact ⟨A, hA, 0, 1, one_pos, fun s _ => by simp⟩
  have hautL : Af.IsAut ι (W.comp (Base.galEmb ℚ L Ω)) :=
    (Z.Bc.solC_of_solDescent (_root_.UpperTheory.V.Af.solvable_descent_of_printed_hida hH) ℚ K L Ω hsol ⟨inferInstance, Or.inr ⟨hK2, inferInstance⟩⟩ inferInstance
      inferInstance l ι 2 (by norm_num) (W.comp (Base.galEmb ℚ K Ω)) 1 (hWc.comp (Base.galEmbTop ℚ K Ω).1.continuous) hirr halg
      (fun _ _ _ _ => rfl) ⟨σ, J * (W σ)⁻¹, H.cc, fun s s' hs => by
        have hs' : Base.galEmb ℚ K Ω s' = σ * Base.galEmb ℚ K Ω s * σ⁻¹ := hs
        rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hs', hpair _ (hηK s)]
        simp⟩).1 ((_root_.UpperTheory.GalN.V.automorphy_bridge_of_printed_hida hH K Ω l ι 2 _).2.1.2 haut)
  have hcsd : _root_.UpperTheory.V.Z.Win.IsAutCsdA ι (Af.tw (W.comp (Base.galEmb ℚ L Ω)) ka) := by
    obtain ⟨hc, art, χ, a, h'⟩ := hka.alg
    have hCL := (_root_.UpperTheory.GalN.V.automorphy_bridge_of_printed_hida hH L Ω l ι 2 _).2.1.1 hautL
    have hWL : _root_.UpperTheory.V.Z.Win.WitA ι (W.comp (Base.galEmb ℚ L Ω)) :=
      _root_.UpperTheory.V.Z.Win.Dn.automorphy_up_base_change (r := W.comp (Base.galEmb ℚ K Ω)) L hH hsol (by norm_num) (hWc.comp (Base.galEmbTop ℚ K Ω).1.continuous) hirr
        ⟨ℚ, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, 1, σ, J * (W σ)⁻¹, halg,
          fun _ _ _ _ => rfl, H.cc, fun s s' hs => by
            have hs' : Base.galEmb ℚ K Ω s' = σ * Base.galEmb ℚ K Ω s * σ⁻¹ := hs
            rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hs', hpair _ (hηK s)]
            simp⟩ haut hFl hWit
    refine _root_.UpperTheory.GalN.V.mkCsd'_alt ?_ fun _ => _root_.UpperTheory.V.Z.Win.Dn.twist'_alt hH.toClassicalTheorems ⟨χ, hc, art, a, h'⟩ hc hWL
    refine _root_.UpperTheory.GalN.V.csdOf0_alt hH ℚ L Ω inferInstance l ι 2 (by norm_num) _ σ (J * (W σ)⁻¹) H.cc
      (_root_.UpperTheory.V.Af.twist_invariance_automorphic hH L Ω l ι 2 _ ka hautL ⟨χ, hc, art, a, h'⟩) fun s s' hs => ?_
    have hs' : Base.galEmb ℚ L Ω s' = σ * Base.galEmb ℚ L Ω s * σ⁻¹ := hs
    have hp := hpair _ (hηL s)
    rw [← hs'] at hp
    rw [MonoidHom.zpow_apply, ← hka.conj s s' hs', Units.val_mul (ka s)]
    simp only [Af.tw_val, MonoidHom.comp_apply, Matrix.transpose_smul, smul_mul_assoc, mul_smul_comm, hp]
    rw [mul_comm, mul_smul]
  obtain ⟨s, V, ρ, a1, a2, a3⟩ := hrig A ρ' h1 h3 (W.comp (Base.galEmb ℚ L Ω))
    (fun s => by rw [h2, MonoidHom.comp_apply, hW _ (hηL s)]; rfl) hirr hcsd
    (_root_.UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.freeRes L W hfree)
  refine adDown Ω l K L hK2 (hK ▸ hLη) s V 2 _ _ R (hWc.comp (Base.galEmbTop ℚ K Ω).1.continuous) hR ρ ka
    (fun g t ht => ?_) (fun g g' t hg ht => ?_) a3
  · rw [a1]
    show _ • (W (Base.galEmb ℚ L Ω g)).val = _ • (W (Base.galEmb ℚ K Ω t)).val
    rw [ht]
  · have : θ (Base.galEmb ℚ K Ω t) = 1 := Units.ext (by rw [hθ, hηK]; simp)
    rw [← a2 g g' hg]
    exact mul_eq_left.2 this
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
open UpperTheory.GalN.V
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.HV GlobalTheory.GalOfCusp UpperTheory.V.Th
open UpperTheory.V.Base UpperTheory.V.Alg in
theorem UpperTheory.V.Z.Win.RR.rigII_a_alt :
    U3.CohInp → _root_.UpperTheory.V.Af.HypothesesH' → _root_.UpperTheory.V.Th.AdjointLiftingTheorem → _root_.UpperTheory.V.Th.RigiditySecondCase := by
  intro hC hH hL Ω _ _ _ K _ _ _ _ l hl c N _ e ψ D U g₁ hM S f hf ι hII W hW hext hdet hmod
  have hpt := U3.isPt_push D hM S f hf
  have he := D.gd.e_pos
  haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩
  obtain ⟨B, hB, -, -, -, hBj, -⟩ := U3.dat_loc D
  haveI : IsLocalHom (algebraMap ℤ_[l] c.O) := (dvrFacts l c.O).2.2.1
  haveI : CharP (ResidueField c.O) l := by
    rw [CharP.charP_iff_prime_eq_zero hl.out, ← map_natCast (residue c.O), residue_eq_zero_iff,
      mem_maximalIdeal, mem_nonunits_iff, ← map_natCast (algebraMap ℤ_[l] c.O)]
    intro hu
    exact PadicInt.prime_p.not_unit (isUnit_of_map_unit _ _ hu)
  have hram : ∀ B' : ValuationSubring Ω, ¬ Ine (F := ℚ) B' ≤ D.η.ker →
      B'.valuation ((l * N * (discr K).natAbs : ℕ) : Ω) < 1 := by
    intro B' h
    haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
    have hd : B'.valuation ((discr K : ℤ) : Ω) < 1 := by
      by_contra h4
      refine h fun s hs => ?_
      rw [D.η_ker]
      have key := GlobalTheory.UnramDiscr.embedding_eq B' h4 ((s : Ω →+* Ω).comp (algebraMap K Ω)) (algebraMap K Ω) (fun x => by
        refine hs.2 _ ((B'.valuation_le_one_iff _).mpr (GlobalTheory.UnramDiscr.mem_of_isIntegral B' ?_))
        exact (RingOfIntegers.isIntegral_coe x).map (algebraMap K Ω).toIntAlgHom)
      exact fun x => DFunLike.congr_fun key x
    have hd' : B'.valuation (((discr K).natAbs : ℕ) : Ω) < 1 := by
      rcases Int.natAbs_eq (discr K) with h1 | h1
      · rw [h1, Int.cast_natCast] at hd; exact hd
      · rw [h1, Int.cast_neg, Int.cast_natCast, Valuation.map_neg] at hd; exact hd
    rw [Nat.cast_mul, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' ((B'.valuation_le_one_iff _).2 (natCast_mem B' _))) hd'
  have hd0 : (discr K).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (discr_ne_zero K)
  have hlink : Pr.LinkHyp c N e D.η D.cc B (l * N * (discr K).natAbs) :=
    ⟨he, dvd_mul_right _ _, mul_ne_zero (mul_ne_zero hl.out.ne_zero (NeZero.ne N)) hd0, hram, hB, D.conj⟩
  have hN := hH.litN
  have hframe := Fr.gd_ex ⟨⟨hN.coh.lf, hN.coh.lt, hN.coh.le, hN.coh.gf, hN.coh.ge, hN.coh.pt⟩, hN.coh.uo, hN.coh.gw⟩
    Ω K l c N e ψ D B hB
  have hfactor : ∃ (A : Subalgebra c.O (PadicAlgCl l)) (_ : IsDiscreteValuationRing A)
      (_ : Module.Finite c.O A), ∀ x, f x ∈ A := by
    have := (dvrFacts l c.O).2.2.2.1
    obtain ⟨E, hE⟩ := Loc.ptFin (l := l) S.R ((TrivSqZeroExt.inlAlgHom c.O _ _).comp f) hf
    have := E.2
    have integral_of_norm (x : PadicAlgCl l) (hx : ‖x‖ ≤ 1) : IsIntegral ℤ_[l] x := by
      have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
      change spectralValue (minpoly ℚ_[l] x) ≤ 1 at hx
      rw [spectralValue_le_one_iff (minpoly.monic hi)] at hx
      have hlifts : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) :=
        (Polynomial.lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, hx n⟩, rfl⟩
      obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hlifts (minpoly.monic hi)
      exact ⟨q, hqm, by
        rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩
    have hint (x : S.R) : IsIntegral ℤ_[l] (f x) := by
      obtain ⟨a, ha⟩ := IsCO.res_surj (O := c.O) x
      have ha' : IsIntegral ℤ_[l] (f (algebraMap c.O S.R a)) := by
        rw [f.commutes]
        exact (IsIntegral.of_finite (R := ℤ_[l]) a).map (IsScalarTower.toAlgHom ℤ_[l] c.O (PadicAlgCl l))
      have hsum := (integral_of_norm _ (hf _ ha).le).add ha'
      rwa [← map_add, sub_add_cancel] at hsum
    obtain ⟨hDVR, hfin, -⟩ := UpperTheory.V.abelian₂.dvr_intClosure l E.1
    let j : E.1 →ₐ[ℤ_[l]] PadicAlgCl l := E.1.val.restrictScalars ℤ_[l]
    have hj : Function.Injective j := Subtype.val_injective
    let equiv := (integralClosure ℤ_[l] E.1).equivMapOfInjective j hj
    let B₀ := (integralClosure ℤ_[l] E.1).map j
    have hB₀ : ∀ x, f x ∈ B₀ := fun x =>
      ⟨⟨f x, (hE x).1⟩, (isIntegral_algHom_iff j hj).1 (hint x), rfl⟩
    let A : Subalgebra c.O (PadicAlgCl l) :=
      { B₀.toSubsemiring with algebraMap_mem' := fun a => f.commutes a ▸ hB₀ _ }
    have hA : IsDiscreteValuationRing B₀ := IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing equiv
    have hAfin : Module.Finite ℤ_[l] B₀ := Module.Finite.equiv equiv.toLinearEquiv
    have : Module.Finite ℤ_[l] A := hAfin
    exact ⟨A, hA, Module.Finite.of_restrictScalars_finite ℤ_[l] c.O A, hB₀⟩
  obtain ⟨A, hA1, hA2, hfA⟩ := hfactor
  haveI : Module.Finite ℤ_[l] A := Module.Finite.trans c.O A
  haveI := (UpperTheory.V.abelian₂.dvr_finite l A).1
  have hlocal : IsLocalHom (f.codRestrict A hfA) := by
    let fA := f.codRestrict A hfA
    let g : S.R →+* fA.range := fA.rangeRestrict
    have hg : IsLocalHom g := IsLocalHom.of_surjective _ fA.rangeRestrict_surjective
    have : Algebra.IsIntegral c.O A := Algebra.IsIntegral.of_finite c.O A
    have : Algebra.IsIntegral fA.range A := Algebra.IsIntegral.tower_top (R := c.O)
    have hi : IsLocalHom (algebraMap fA.range A) := Algebra.IsIntegral.isLocalHom _ _
    exact ⟨fun x hx => hg.map_nonunit x (hi.map_nonunit (g x) hx)⟩
  have hord := Pr.ordPt_of_gd hC.loc D g₁ hM U S B hBj A (f.codRestrict A hfA) hlocal
  have hpush : UnitaryThreeInertia.push A.val (U3.push (f.codRestrict A hfA) S.r.hom) = U3.push f S.r.hom := rfl
  have hM1 : 1 ≤ N * (discr K).natAbs := Nat.one_le_iff_ne_zero.2 (mul_ne_zero (NeZero.ne N) hd0)
  have hm : StrictAnti ![(e : ℤ), -(e : ℤ)] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> omega
  have hlev := (U3.typeII_ord hC D hM hpt hII W hext hW hdet).1
  have hwt : Af.IsCycWt l 0 (Matrix.GeneralLinearGroup.det.comp W) := by
    have hodd : Odd (discr K).natAbs := Nat.coprime_two_right.1 (D.gd.cop.coprime_dvd_right D.gd.N_even.two_dvd)
    refine ⟨(discr K).natAbs, Matrix.GeneralLinearGroup.det.comp W, hodd.pos, fun s hs => Units.ext ?_, by simp⟩
    have h1 : s ∈ D.η.ker := D.η_ker ▸ UpperTheory.mem_galOf_quadratic_of_fixes_discr_roots_of_unity Ω K D.gd.quad hodd s hs
    have h2 := hdet s
    rw [show D.η s = 1 from h1] at h2
    simpa using h2
  have hcyc := U3.typeII_irr_cyc hC D hM hpt hII W hext
  have hirrK : Af.IsIrr (W.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω)) :=
    ⟨top_ne_bot, fun _ _ _ => trivial, fun X hX hs => hcyc.2.2 X hX fun g v hv => hs g v hv⟩
  have hWQ := _root_.UpperTheory.GalN.V.witAQ_of_isModularA hH.toClassicalTheorems hW hwt he hmod
  obtain ⟨nf, hnf⟩ := _root_.UpperTheory.GalN.V.mod0'_alt hmod
  have hadm : ∃ θ, Af.IsCycWt l 0 θ ∧ Af.DualTw W θ :=
      ⟨_, hwt, Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; -1, 0] (by simp), fun s => by
        have hd : ((Matrix.GeneralLinearGroup.det.comp W s : (Qbar l)ˣ) : Qbar l) = (W s).val.det := rfl
        rw [hd, Matrix.det_fin_two (W s).val]
        ext i j
        simp only [Matrix.mul_apply, Fin.sum_univ_two]
        fin_cases i <;> fin_cases j <;> simp <;> ring⟩
  have haut := _root_.UpperTheory.GalN.V.autKQ0_alt hH K Ω D.gd.quad l ι 2 (by norm_num) W 0 hW
    (_root_.UpperTheory.GalN.V.newformAut0_alt hH.toClassicalTheorems _ (by omega) nf l Ω ι W _ hnf) hadm hirrK
  have hunl := (unlRes K Ω l 2 _ _ W hM1).2 (fun i j => by
    fin_cases i <;> fin_cases j <;> simp <;> omega) hlev
  have hres : Continuous (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω) := (galEmbTop ℚ K Ω).1.continuous
  have hfree := _root_.UpperTheory.V.Z.Win.RR.freePUA_alt hH K Ω D.gd.quad l D.gd.l_odd ι 2 le_rfl _ _ _ hM1 hm (hW.comp hres) haut (hWQ K D.gd.quad hirrK) hunl
  obtain ⟨π, hreg, -, hatt⟩ := haut
  refine _root_.UpperTheory.V.Z.Win.Dn.rigid_end_two_w_of_printed_adjoint_lifting hH hL Ω l ι c N e ψ D.η D.cc g₁ B _ hlink (U3.dat_facts D).2.2.1 hframe A _ hord hII
    (fun g hg => Subtype.ext ((U3.typeII_facts hC D hM hpt hII).1 g hg)) K D.gd.quad D.η_ker W hW hext.1 hdet
    ⟨π, hreg, hatt⟩ (hWQ K D.gd.quad hirrK) fun A' hA' => ?_
  obtain ⟨g, hg, hc, α, hα, hp⟩ := hfree A' hA'
  exact ⟨AlgEquiv.restrictScalarsHom ℚ g, hg, hc, α, hα, hp⟩
end
