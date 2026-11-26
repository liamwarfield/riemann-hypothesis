module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.WeightInfinitesimalCharacters.PtHypU
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WStmtx

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypeIIOfBlochKatoLocalPoint
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.KatoUsedOf
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3
open scoped Matrix
private theorem cls_eq_one {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (N : ℕ) [NeZero N] (g : G ℚ Ω)
    (hg : ∀ ζ : Ω, ζ ^ N = 1 → g ζ = ζ) : Chr.cls ℚ Ω N g = 1 := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : NeZero ((N : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne N)⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω N
  have h1 := Chr.cls_spec N g ζ hζ.pow_eq_one
  rw [hg ζ hζ.pow_eq_one] at h1
  have h2 : ζ ^ (1 : ZMod N).val = ζ := by
    rw [ZMod.val_one_eq_one_mod, hζ.eq_orderOf, pow_mod_orderOf, pow_one]
  apply Units.ext
  apply ZMod.val_injective
  exact hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) (h1.symm.trans h2.symm)
theorem UpperTheory.V.Z.Kato.used_of_alt :
    CohInp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) {U : (_root_.UpperTheory.V.U3.Univ (_root_.UpperTheory.V.U3.GCond.noCondition _ (D.η.comp D.ι) (D.Ψ.comp D.ι)))}
      {g₁ : G ℚ Ω}, D.Marked g₁ → ∀ {r : G ℚ Ω →* GG (m := 3) (R := PadicAlgCl l)} (_ : D.IsPt U g₁ r),
      TypeII D.η r → ∀ W : G ℚ Ω →* GL (Fin 2) (PadicAlgCl l), D.IsExt r W → Continuous W →
      (∀ g, (W g : Matrix (Fin 2) (Fin 2) (PadicAlgCl l)) = Wfun r g) →
      (∀ g, (W g : Matrix (Fin 2) (Fin 2) (PadicAlgCl l)).det = ((D.η g : ℤˣ) : ℤ)) →
      ∀ ι : Qbar l ≃+* ℂ, D.IsModularDense ι W →
      UpperTheory.V.Z.Kato.Used l Ω K e N ((Units.map (Int.castRingHom (PadicAlgCl l)).toMonoidHom).comp D.η)
        ((Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom).comp (Chr.dirG ℚ Ω ψ)) W := by
  intro hC Ω _ _ _ K _ _ _ l hl c N _ e ψ D U g₁ hM r h hII W hext hcont hW hdet ι hmod
  obtain ⟨h11, -, -⟩ := typeII_facts hC D hM h hII
  obtain ⟨-, hηc, hΨc, -, -, -, -, -, -, -, hl1⟩ := dat_facts D
  obtain ⟨A₀, hA₀, -, hIn, -, -, hcyc, hconj⟩ := dat_loc D
  set θ : G ℚ Ω →* (PadicAlgCl l)ˣ := (Units.map (Int.castRingHom (PadicAlgCl l)).toMonoidHom).comp D.η with hθdef
  set ψQ : G ℚ Ω →* (Qbar l)ˣ := (Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom).comp (Chr.dirG ℚ Ω ψ) with hψdef
  have hθ0 : ∀ g, (θ g : PadicAlgCl l) = ((D.η g : ℤˣ) : ℤ) := fun g => rfl
  have hΨ : ∀ g, D.ΨQ g = cycBar ℚ Ω l g ^ (e : ℤ) * ψQ g := fun g => by
    show Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom (chiO ℚ Ω l c.O g ^ (e : ℤ) * Chr.dirG ℚ Ω ψ g) = _
    rw [map_mul, map_zpow]
    rfl
  have hord := typeII_ord hC D hM h hII W hext hcont hdet
  have w0 : wt1 0 = 1 := by decide
  have w1 : wt1 1 = 0 := by decide
  have w2 : wt1 2 = -1 := by decide
  have h00 : ∀ g, (r0 D.η D.ΨQ g).mat 0 0 = (D.ΨQ g : PadicAlgCl l) := fun g => by
    simp only [GG.mat, unitaryThreeReflection_left, tor_val, Matrix.diagonal_apply_eq, w0, _root_.zpow_one]
  have h22 : ∀ g, (r0 D.η D.ΨQ g).mat 2 2 = (((D.ΨQ g)⁻¹ : (PadicAlgCl l)ˣ) : PadicAlgCl l) := fun g => by
    simp only [GG.mat, unitaryThreeReflection_left, tor_val, Matrix.diagonal_apply_eq, w2, _root_.zpow_neg, _root_.zpow_one]
  have h11' : ∀ g, (r0 D.η D.ΨQ g).mat 1 1 = 1 := fun g => by
    simp only [GG.mat, unitaryThreeReflection_left, tor_val, Matrix.diagonal_apply_eq, w1, _root_.zpow_zero, Units.val_one]
  have htrW : ∀ g, (W g : Matrix (Fin 2) (Fin 2) (PadicAlgCl l)).trace = (θ g : PadicAlgCl l) * (r g).mat 0 0 + (r g).mat 2 2 := by
    intro g
    rw [hW, Wfun, hθ0, h.mult g]
    rcases Int.units_eq_one_or (D.η g) with hg | hg
    · rw [hg, if_pos rfl, Matrix.trace_fin_two]
      show (r g).mat 0 0 + (r g).mat 2 2 = _
      simp
    · rw [hg, if_neg (by decide), Matrix.trace_fin_two, Matrix.mul_diagonal, Matrix.mul_diagonal]
      show (r g).mat 0 0 * (-1) + (r g).mat 2 2 * 1 = _
      simp
  refine
    { l_odd := D.gd.l_odd, e_pos := D.gd.e_pos, gen := D.gd.gen, quad := D.gd.quad, imag := D.gd.imag, l_cop := D.gd.l_cop,
      N_pos := NeZero.pos N, N_even := D.gd.N_even, cop := D.gd.cop, θ_ker := ?_, θ_sq := fun g => ?_, ψ_mu := fun s hs => ?_,
      ψ_ord := ⟨orderOf ψ, D.gd.ord, fun g => ?_⟩, ψ_ine := fun A hA s hs => ?_, even := ⟨D.cc, D.conj, ?_⟩,
      level := hord.1, ord := ⟨A₀, N, hA₀, NeZero.pos N, hord.2 A₀ hA₀⟩, det := fun g => by rw [hdet, hθ0],
      tr_ine := fun A hA s hs => ?_, red := fun g => ?_, flag := ?_, irr := typeII_irr_cyc hC D hM h hII W hext }
  · rw [← D.η_ker]
    ext g
    simp only [MonoidHom.mem_ker, Units.ext_iff, hθ0, Units.val_one]
    rcases Int.units_eq_one_or (D.η g) with hg | hg <;> rw [hg] <;> norm_num
  · show Units.map (Int.castRingHom (PadicAlgCl l)).toMonoidHom (D.η g) ^ 2 = 1
    rw [← map_pow, Int.units_sq, map_one]
  · show Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom (ψ.toUnitHom (Chr.cls ℚ Ω N s)) = 1
    rw [cls_eq_one N s hs, map_one, map_one]
  · show Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom (ψ.toUnitHom (Chr.cls ℚ Ω N g)) ^ _ = 1
    rw [← map_pow]
    have : ψ.toUnitHom (Chr.cls ℚ Ω N g) ^ orderOf ψ = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, MulChar.coe_toUnitHom, ← MulChar.pow_apply_coe, pow_orderOf_eq_one, MulChar.one_apply_coe,
        Units.val_one]
    rw [this, map_one]
  · obtain ⟨x, -, hxI⟩ := hconj A hA
    have h1 := (hxI s).1 hs
    rw [← hIn] at h1
    obtain ⟨σ, hσI, hσ⟩ := h1
    have h2 := D.Ψ_I σ hσI
    have h3 : Loc.cycA l l c.O σ = chiO ℚ Ω l c.O (D.ι σ) := by
      show Units.map _ (Loc.cyc l l σ) = Units.map _ (cycZ ℚ Ω l (D.ι σ))
      rw [hcyc]
      rfl
    have h4 : Chr.dirG ℚ Ω ψ (D.ι σ) = Chr.dirG ℚ Ω (comp l ψ) (D.ι σ) := by
      rw [h3, Chr.Psi, MonoidHom.mul_apply, MonoidHom.zpow_apply, _root_.zpow_natCast] at h2
      exact mul_left_cancel h2
    have h5 : Chr.dirG ℚ Ω ψ s = Chr.dirG ℚ Ω ψ (D.ι σ) := by
      rw [hσ]
      simp only [map_mul, map_inv, inv_mul_cancel_comm]
    show Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom (Chr.dirG ℚ Ω ψ s) ^ 2 = 1
    have h6 : Chr.dirG ℚ Ω (comp l ψ) (D.ι σ) ^ 2 = 1 := by
      apply Units.ext
      show (((comp l ψ).toUnitHom (Chr.cls ℚ Ω N (D.ι σ)) ^ 2 : c.Oˣ) : c.O) = _
      rw [Units.val_pow_eq_pow_val, MulChar.coe_toUnitHom, ← MulChar.pow_apply_coe, D.gd.ine, MulChar.one_apply_coe,
        Units.val_one]
    rw [← map_pow, h5, h4, h6, map_one]
  · rw [← hΨ]
    show Units.map _ (D.Ψ D.cc) = 1
    rw [hΨc, map_one]
  · obtain ⟨hch, -⟩ := pt_inertia_above hC D hM h A hA
    have hk : s ∈ D.η.ker := (hl1 A hA).1 hs
    have htr : (r s).mat.trace = (r0 D.η D.ΨQ s).mat.trace := by
      rw [Matrix.trace_eq_neg_charpoly_coeff, Matrix.trace_eq_neg_charpoly_coeff, hch s hs]
    rw [Matrix.trace_fin_three, Matrix.trace_fin_three, h00, h22, h11', h11 s hk] at htr
    rw [htrW, ← hΨ, hθ0, show D.η s = 1 from hk]
    simp only [Units.val_one, Int.cast_one, one_mul]
    linear_combination htr
  · rw [htrW, ← hΨ]
    have a0 := h.red g 0 0
    have a2 := h.red g 2 2
    rw [h00] at a0
    rw [h22] at a2
    have hn : ‖(θ g : PadicAlgCl l)‖ = 1 := by
      rw [hθ0]
      rcases Int.units_eq_one_or (D.η g) with hg | hg <;> simp [hg]
    have e1 : (θ g : PadicAlgCl l) * (r g).mat 0 0 + (r g).mat 2 2 -
        ((θ g : PadicAlgCl l) * (D.ΨQ g : PadicAlgCl l) + (((D.ΨQ g)⁻¹ : (PadicAlgCl l)ˣ) : PadicAlgCl l)) =
        (θ g : PadicAlgCl l) * ((r g).mat 0 0 - D.ΨQ g) + ((r g).mat 2 2 - (((D.ΨQ g)⁻¹ : (PadicAlgCl l)ˣ) : PadicAlgCl l)) := by
      ring
    rw [e1]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ a2)
    rw [norm_mul, hn, one_mul]
    exact a0
  · let χ : G ℚ Ω →* (Qbar l)ˣ :=
      (Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom).comp (Chr.dirG ℚ Ω (HV.comp l ψ))
    have hχ2 (g : G ℚ Ω) : χ g * χ g = 1 := by
      have hχg : Chr.dirG ℚ Ω (HV.comp l ψ) g * Chr.dirG ℚ Ω (HV.comp l ψ) g = 1 := by
        apply Units.ext
        show (HV.comp l ψ) (Chr.cls ℚ Ω N g) * (HV.comp l ψ) (Chr.cls ℚ Ω N g) = 1
        rw [← MulChar.mul_apply, ← sq, D.gd.ine, MulChar.one_apply (Units.isUnit _)]
      show Units.map _ _ * Units.map _ _ = 1
      rw [← map_mul, hχg, map_one]
    have hψχ : ∀ s ∈ Ine (F := ℚ) A₀, ψQ s = χ s := fun s hs => by
      rw [← hIn] at hs
      obtain ⟨g, hg, rfl⟩ := hs
      show Units.map _ _ = Units.map _ _
      rw [GlobalTheory.Ord2.psi_ine D g hg]
    obtain ⟨hIk, s₀, hs₀, hu⟩ := hl1 A₀ hA₀
    have hlocal : ∃ κ : Fin 2 → ↥(Dec (F := ℚ) A₀) →* (Qbar l)ˣ,
        Af.IsFlagOn W (Dec (F := ℚ) A₀) κ ∧
          ∀ s : ↥(Dec (F := ℚ) A₀), (s : G ℚ Ω) ∈ Ine (F := ℚ) A₀ →
            κ 0 s = D.ΨQ s ∧ κ 1 s = (D.ΨQ s)⁻¹ := by
      have hblk (s : G ℚ Ω) (hs : s ∈ D.η.ker) :
          (r s).mat = !![W s 0 0, 0, W s 0 1; 0, 1, 0; W s 1 0, 0, W s 1 1] := by
        have hcorner : (W s : Matrix (Fin 2) (Fin 2) (Qbar l)) = corner (r s).mat := hext.1 s hs
        have e01 := hII.1 s hs 0 1 (by decide)
        have e10 := hII.1 s hs 1 0 (by decide)
        have e12 := hII.1 s hs 1 2 (by decide)
        have e21 := hII.1 s hs 2 1 (by decide)
        ext i j
        fin_cases i <;> fin_cases j <;> simp [hcorner, corner, e01, e10, e12, e21, h11 s hs]
      obtain ⟨-, M, hup, hdiag⟩ := pt_inertia_above hC D hM h A₀ hA₀
      obtain ⟨hnorm, hID, -⟩ := Chr.decCyc Ω l A₀ hl.out hA₀
      have hs₀' : (D.ΨQ s₀ : Qbar l) ^ 2 ≠ 1 := by
        have hu' := (hu.map (algebraMap c.O (PadicAlgCl l))).ne_zero
        rwa [map_sub, map_pow, map_one, sub_ne_zero] at hu'
      set v : Fin 3 → Qbar l :=
        ((M⁻¹ : GL (Fin 3) (Qbar l)) : Matrix (Fin 3) (Fin 3) (Qbar l)) *ᵥ Pi.single 0 1 with hv
      have hv0 : v ≠ 0 := fun h0 => by
        have he := congrArg (fun x => ((M : Matrix (Fin 3) (Fin 3) (Qbar l)) *ᵥ x) 0) (hv.symm.trans h0)
        simp only [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec, Matrix.mulVec_zero] at he
        simp at he
      have hev : ∀ s ∈ Ine (F := ℚ) A₀,
          !![W s 0 0, 0, W s 0 1; 0, 1, 0; W s 1 0, 0, W s 1 1] *ᵥ v = (D.ΨQ s : Qbar l) • v := by
        intro s hs
        have hr : (r s).right = 1 := (h.mult s).trans (hIk hs)
        have hmat : (conjBy M r s).mat =
            (M : Matrix (Fin 3) (Fin 3) (Qbar l)) * (r s).mat *
              ((M⁻¹ : GL (Fin 3) (Qbar l)) : Matrix (Fin 3) (Fin 3) (Qbar l)) := by
          simp [conjBy, GG.mat, hr]
        have hcol : (conjBy M r s).mat *ᵥ Pi.single 0 1 =
            (D.ΨQ s : Qbar l) • (Pi.single 0 1 : Fin 3 → Qbar l) := by
          rw [Matrix.mulVec_single_one]
          funext i
          fin_cases i
          · change (conjBy M r s).mat 0 0 = _
            rw [hdiag s hs 0, h00]
            simp
          · simpa using hup s (hID hs) (hIk hs) 1 0 (by decide)
          · simpa using hup s (hID hs) (hIk hs) 2 0 (by decide)
        rw [← hblk s (hIk hs), hv, ← Matrix.mulVec_smul, ← hcol, hmat,
          Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
          Units.inv_mul, Matrix.one_mul]
      have hv1 : v 1 = 0 := by
        have he := congrFun (hev s₀ hs₀) 1
        simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at he
        by_contra hne
        have hval : (D.ΨQ s₀ : Qbar l) = 1 := (mul_right_cancel₀ hne ((one_mul _).trans he)).symm
        exact hs₀' (by rw [hval, one_pow])
      exact UpperTheory.exists_isFlagOn_of_eigenvector_normal_subgroup (Dec (F := ℚ) A₀) (Ine (F := ℚ) A₀) W D.ΨQ ![v 0, v 2]
        (fun d hd s hs => hnorm.conj_mem' ⟨s, hID hs⟩ hs ⟨d, hd⟩)
        (fun h0 => hv0 (by
          funext i
          fin_cases i
          · exact congrFun h0 0
          · exact hv1
          · exact congrFun h0 1))
        (fun s hs => by
          have a0 := congrFun (hev s hs) 0
          have a2 := congrFun (hev s hs) 2
          funext i
          fin_cases i
          · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two] using a0
          · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two] using a2)
        (fun s hs => by rw [hdet, show D.η s = 1 from hIk hs]; simp)
        ⟨s₀, hs₀, hs₀'⟩
    obtain ⟨κ, hflag, hκ⟩ := hlocal
    refine ⟨A₀, χ, κ, ?_, ?_, hflag, ?_, ?_⟩
    · obtain ⟨hex, htop, hover, -⟩ := places ℚ Ω l A₀
      have hne : A₀ ≠ ⊤ := fun ht => (htop ht).2 hA₀
      obtain ⟨v, hv⟩ := hex hne
      exact ⟨v, hv, (hover v hv).1 hA₀⟩
    · intro s hs
      show Units.map _ _ = 1
      rw [GlobalTheory.killsMu_comp_of_sq_eq_one ψ D.gd.l_odd D.gd.ine s hs, map_one]
    · intro s hs
      rw [MonoidHom.mem_ker]
      apply Units.ext
      rw [hθ0, hIk hs]
      simp
    · intro s hs
      rw [(hκ s hs).1, (hκ s hs).2, hΨ, hψχ s hs, mul_inv, ← _root_.zpow_neg]
      refine ⟨rfl, ?_⟩
      congr 1
      exact inv_eq_of_mul_eq_one_right (hχ2 s)
end
end

set_option maxHeartbeats 10000000
set_option stderrAsMessages false
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3
open scoped TensorProduct

namespace TypeIIHelpers

-- Decompose the adjoint representation using the block on indices 0 and 2.
private def IsBlockSL2Embedding {R : Type} [CommRing R] (x : GG (m := 3) (R := R)) : Prop :=
  ∃ a b c d : R, a * d - b * c = 1 ∧ x.mat = !![a, 0, b; 0, 1, 0; c, 0, d]

private theorem theta_eq {R : Type} [CommRing R] (X : Matrix (Fin 3) (Fin 3) R) :
    thetaLie X = !![-X 2 2, -X 1 2, -X 0 2; -X 2 1, -X 1 1, -X 0 1; -X 2 0, -X 1 0, -X 0 0] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [thetaLie, Matrix.mul_apply, Fin.sum_univ_three, Jmat, Fin.rev]

private theorem conj_eq {R : Type} [CommRing R] (a b c d : R) (Y : Matrix (Fin 3) (Fin 3) R) :
    !![a, 0, b; 0, 1, 0; c, 0, d] * Y * !![d, 0, -b; 0, 1, 0; -c, 0, a] =
    !![(a * Y 0 0 + b * Y 2 0) * d - (a * Y 0 2 + b * Y 2 2) * c, a * Y 0 1 + b * Y 2 1,
        -(a * Y 0 0 + b * Y 2 0) * b + (a * Y 0 2 + b * Y 2 2) * a;
      Y 1 0 * d - Y 1 2 * c, Y 1 1, -Y 1 0 * b + Y 1 2 * a;
      (c * Y 0 0 + d * Y 2 0) * d - (c * Y 0 2 + d * Y 2 2) * c, c * Y 0 1 + d * Y 2 1,
        -(c * Y 0 0 + d * Y 2 0) * b + (c * Y 0 2 + d * Y 2 2) * a] := by
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp <;> ring

private theorem ad_eq {R : Type} [CommRing R] {x : GG (m := 3) (R := R)} {a b c d : R} (h : a * d - b * c = 1)
    (hx : x.mat = !![a, 0, b; 0, 1, 0; c, 0, d]) (X : Matrix (Fin 3) (Fin 3) R) :
    x.adFun X = !![a, 0, b; 0, 1, 0; c, 0, d] * (if x.right = 1 then X else thetaLie X) *
      !![d, 0, -b; 0, 1, 0; -c, 0, a] := by
  have : ((x.left⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) = !![d, 0, -b; 0, 1, 0; -c, 0, a] := by
    apply Units.inv_eq_of_mul_eq_one_right
    change x.mat * _ = 1
    rw [hx]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;>
      first | ring1 | linear_combination h
  rw [GG.adFun, this, hx]

private def pA {R : Type} [CommRing R] : Matrix (Fin 3) (Fin 3) R →ₗ[R] Matrix (Fin 2) (Fin 2) R := {
  toFun X := !![X 0 0, X 0 2; X 2 0, X 2 2]
  map_add' X Y := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_smul' a X := by ext i j; fin_cases i <;> fin_cases j <;> simp
}

private def sA {R : Type} [CommRing R] : Matrix (Fin 2) (Fin 2) R →ₗ[R] Matrix (Fin 3) (Fin 3) R := {
  toFun Y := !![Y 0 0, 0, Y 0 1; 0, 0, 0; Y 1 0, 0, Y 1 1]
  map_add' X Y := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_smul' a X := by ext i j; fin_cases i <;> fin_cases j <;> simp
}

private def pB {R : Type} [CommRing R] (t : R) : Matrix (Fin 3) (Fin 3) R →ₗ[R] (Fin 2 → R) := {
  toFun X := ![X 0 1 + t * X 1 2, X 2 1 - t * X 1 0]
  map_add' X Y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' a X := by ext i; fin_cases i <;> simp <;> ring
}

private def sB {R : Type} [CommRing R] (t : R) : (Fin 2 → R) →ₗ[R] Matrix (Fin 3) (Fin 3) R := {
  toFun v := !![0, v 0, 0; -(t * v 1), 0, t * v 0; 0, v 1, 0]
  map_add' X Y := by ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring
  map_smul' a X := by ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring
}

private def pC {R : Type} [CommRing R] : Matrix (Fin 3) (Fin 3) R →ₗ[R] Matrix (Fin 3) (Fin 3) R := {
  toFun X := !![0, 0, 0; 0, X 1 1, 0; 0, 0, 0]
  map_add' X Y := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_smul' a X := by ext i j; fin_cases i <;> fin_cases j <;> simp
}

private theorem decomp {R : Type} [CommRing R] (u : R) (hu : 2 * u = 1) (X : Matrix (Fin 3) (Fin 3) R) :
    X = sA (pA X) + u • sB 1 (pB 1 X) + u • sB (-1) (pB (-1) X) + pC (pC X) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sA, pA, sB, pB, pC]
  · linear_combination (-X 0 1) * hu
  · linear_combination (-X 1 0) * hu
  · linear_combination (-X 1 2) * hu
  · linear_combination (-X 2 1) * hu

private theorem pA_sA {R : Type} [CommRing R] (Y : Matrix (Fin 2) (Fin 2) R) : pA (sA Y) = Y := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem ad_sA {R : Type} [CommRing R] {x : GG (m := 3) (R := R)} (hx : IsBlockSL2Embedding x) (Y : Matrix (Fin 2) (Fin 2) R) :
    sA (pA (x.adFun (sA Y))) = x.adFun (sA Y) := by
  obtain ⟨a, b, c, d, h, hx⟩ := hx
  rw [ad_eq h hx, theta_eq, conj_eq]
  by_cases hsign : x.right = 1 <;> simp only [hsign, if_true, if_false]
  all_goals
    ext i j
    fin_cases i <;> fin_cases j <;> first | rfl | simp [sA, pA]

private theorem pA_ad {R : Type} [CommRing R] {x : GG (m := 3) (R := R)} (hx : IsBlockSL2Embedding x) (X : Matrix (Fin 3) (Fin 3) R) :
    pA (x.adFun X) = pA (x.adFun (sA (pA X))) := by
  obtain ⟨a, b, c, d, h, hx⟩ := hx
  rw [ad_eq h hx, ad_eq h hx, theta_eq, theta_eq, conj_eq, conj_eq]
  ext i j
  split_ifs <;> fin_cases i <;> fin_cases j <;> simp [sA, pA]

private def wOf {R : Type} [CommRing R] (x : GG (m := 3) (R := R)) : Matrix (Fin 2) (Fin 2) R :=
  if x.right = 1 then corner x.mat else corner x.mat * Matrix.diagonal ![-1, 1]

private theorem wOf_eq {R : Type} [CommRing R] {x : GG (m := 3) (R := R)} {a b c d : R} (hx : x.mat = !![a, 0, b; 0, 1, 0; c, 0, d]) :
    wOf x = if x.right = 1 then !![a, b; c, d] else !![-a, b; -c, d] := by
  have : corner x.mat = !![a, b; c, d] := by
    rw [hx]
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  dsimp only [wOf]
  rw [this]
  split_ifs
  · rfl
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal]

private theorem pB_ad {R : Type} [CommRing R] {x : GG (m := 3) (R := R)} (hx : IsBlockSL2Embedding x) (t : R) (ht : t * t = 1) (X : Matrix (Fin 3) (Fin 3) R) :
    pB t (x.adFun X) = ((if x.right = 1 then 1 else t) • wOf x) *ᵥ pB t X := by
  obtain ⟨a, b, c, d, h, hx⟩ := hx
  rw [ad_eq h hx, theta_eq, conj_eq, wOf_eq hx]
  ext i
  split_ifs <;> fin_cases i <;>
    simp [pB, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
    first | ring1 | linear_combination (a * X 1 2 + b * X 1 0) * ht | linear_combination (c * X 1 2 + d * X 1 0) * ht

private theorem ad_sB {R : Type} [CommRing R] {x : GG (m := 3) (R := R)} (hx : IsBlockSL2Embedding x) (t : R) (ht : t * t = 1) (v : Fin 2 → R) :
    sB t (((if x.right = 1 then 1 else t) • wOf x) *ᵥ v) = x.adFun (sB t v) := by
  obtain ⟨a, b, c, d, h, hx⟩ := hx
  rw [ad_eq h hx, theta_eq, conj_eq, wOf_eq hx]
  ext i j
  split_ifs <;> fin_cases i <;> fin_cases j <;>
    simp [sB, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
    first | ring1 | linear_combination (c * v 0 - d * v 1) * ht | linear_combination (-a * v 0 + b * v 1) * ht

private theorem pC_ad {R : Type} [CommRing R] {x : GG (m := 3) (R := R)} (hx : IsBlockSL2Embedding x) (X : Matrix (Fin 3) (Fin 3) R) :
    pC (x.adFun X) = (if x.right = 1 then 1 else -1 : R) • pC X := by
  obtain ⟨a, b, c, d, h, hx⟩ := hx
  rw [ad_eq h hx, theta_eq, conj_eq]
  by_cases hs : x.right = 1 <;> simp only [hs, if_true, if_false]
  all_goals
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pC]

private theorem ad_pC {R : Type} [CommRing R] {x : GG (m := 3) (R := R)} (hx : IsBlockSL2Embedding x) (X : Matrix (Fin 3) (Fin 3) R) :
    x.adFun (pC X) = (if x.right = 1 then 1 else -1 : R) • pC X := by
  obtain ⟨a, b, c, d, h, hx⟩ := hx
  rw [ad_eq h hx, theta_eq, conj_eq]
  by_cases hs : x.right = 1 <;> simp only [hs, if_true, if_false]
  all_goals
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pC]

private theorem pA_ad_one {R : Type} [CommRing R] {x : GG (m := 3) (R := R)} (hx : IsBlockSL2Embedding x) (h1 : x.right = 1) (w : GL (Fin 2) R)
    (hw : (w : Matrix (Fin 2) (Fin 2) R) = wOf x) (Y : Matrix (Fin 2) (Fin 2) R) :
    pA (x.adFun (sA Y)) = (w : Matrix (Fin 2) (Fin 2) R) * Y * ((w⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) := by
  obtain ⟨a, b, c, d, h, hx⟩ := hx
  rw [wOf_eq hx, if_pos h1] at hw
  have : ((w⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) = !![d, -b; -c, a] := by
    apply Units.inv_eq_of_mul_eq_one_right
    rw [hw]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | ring1 | linear_combination h
  rw [ad_eq h hx, if_pos h1, this, hw, conj_eq]
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp [sA, pA] <;> ring

private theorem pA_ad_c {R : Type} [CommRing R] {x : GG (m := 3) (R := R)} (hx : x.mat = 1) (h1 : x.right = -1) (Y : Matrix (Fin 2) (Fin 2) R) :
    pA (x.adFun (sA Y)) = -(Jmat R 2 * Yᵀ * Jmat R 2) := by
  have hx' : x.mat = !![1, 0, 0; 0, 1, 0; 0, 0, 1] := by
    rw [hx]; ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [ad_eq (by ring) hx', if_neg (by rw [h1]; decide), theta_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sA, pA, Jmat, Fin.rev, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two]

private def repA {R : Type} [CommRing R] {Γ : Type} [Group Γ] (r : Γ →* GG (m := 3) (R := R)) (hr : ∀ g, IsBlockSL2Embedding (r g)) :
    Representation R Γ (Matrix (Fin 2) (Fin 2) R) := {
  toFun g := pA ∘ₗ adRep r g ∘ₗ sA
  map_one' := by
    refine LinearMap.ext fun Y => ?_
    simp [pA_sA]
  map_mul' g h := by
    refine LinearMap.ext fun Y => ?_
    change pA ((r (g * h)).adFun (sA Y)) = pA ((r g).adFun (sA (pA ((r h).adFun (sA Y)))))
    rw [ad_sA (hr h), map_mul, GG.adFun_mul]
}

private theorem pair_eq {R : Type} [CommRing R] (w : Matrix (Fin 2) (Fin 2) R) :
    wᵀ * Jmat R 2 * (!![-1, 0; 0, 1] * w * !![-1, 0; 0, 1]) = w.det • Jmat R 2 := by
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two]
  fin_cases i <;> fin_cases j <;> simp [Jmat, Fin.rev] <;> ring

private theorem isBlock_reducible_three_dim {R : Type} [CommRing R] {Γ : Type} [Group Γ] (η : Γ →* ℤˣ) (Ψ : Γ →* Rˣ) (g : Γ) : IsBlockSL2Embedding (r0 η Ψ g) := by
  refine ⟨(Ψ g : R), 0, 0, ((Ψ g)⁻¹ : Rˣ), by simp, ?_⟩
  rw [GG.mat, unitaryThreeReflection_left, tor_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wt1]

private theorem pC_mem {R : Type} [CommRing R] (X : Matrix (Fin 3) (Fin 3) R) : pC X ∈ gw R 0 := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> first | rfl | exact absurd (by decide) hab


end TypeIIHelpers

open TypeIIHelpers

theorem UpperTheory.V.Z.Kato.WeilSphericalRecords.bloch_kato_selmer_vanishes_of_type_ii_modular_ext :
    U3.CohInp → _root_.UpperTheory.V.Z.Kato.WeilSphericalRecords.KatoTwoW → _root_.UpperTheory.V.Th.RigiditySecondCase → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [IsCMField K] [Algebra K Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) {U : (_root_.UpperTheory.V.U3.Univ (_root_.UpperTheory.V.U3.GCond.noCondition _ (D.η.comp D.ι) (D.Ψ.comp D.ι)))} {g₁ : G ℚ Ω}, D.Marked g₁ → ∀ (S : D.Ring U g₁) (f : S.R →ₐ[c.O] PadicAlgCl l), IsLocPt f → ∀ ι : Qbar l ≃+* ℂ, TypeII D.η (push f S.r.hom) → (∀ W : G ℚ Ω →* GL (Fin 2) (PadicAlgCl l), D.IsExt (push f S.r.hom) W → D.IsModularDense ι W) → Af.BlochKatoSelmerVanishes l (adRep (push f S.r.hom)) := by
  intro hC hK hRig Ω _ _ _ K _ _ _ _ l _ c N _ e ψ D U g₁ hm S f₀ hf₀ ι hII hmod
  have h := isPt_push D hm S f₀ hf₀
  have hR := hRig D hm S f₀ hf₀ ι hII
  generalize push f₀ S.r.hom = r at h hR hII hmod ⊢
  obtain ⟨hcc, hηc, -, hlc, -, -, -, hCM, -⟩ := dat_facts D
  obtain ⟨h11, hdet, W, hext, hWc, -, hW, hWd⟩ := typeII_facts hC D hm h hII
  dbg_trace "main argument"
  have hW' : ∀ g, (W g).val = wOf (r g) := hW
  have hblk0 : ∀ g ∈ D.η.ker, IsBlockSL2Embedding (r g) := by
    intro g hg
    refine ⟨(r g).mat 0 0, (r g).mat 0 2, (r g).mat 2 0, (r g).mat 2 2, ?_, ?_⟩
    · have := hdet g hg
      rw [Matrix.det_fin_two] at this
      exact this
    · ext i j
      fin_cases i <;> fin_cases j <;> first
        | rfl
        | exact h11 g hg
        | exact hII.1 g hg _ _ (by decide)
  have hblk : ∀ g, IsBlockSL2Embedding (r g) := by
    intro g
    rcases Int.units_eq_one_or (D.η g) with hg | hg
    · exact hblk0 g hg
    · have hk : D.η (g * D.cc⁻¹) = 1 := by rw [map_mul, map_inv, hg, hηc, mul_inv_cancel]
      have e1 : r g = r (g * D.cc⁻¹) * r D.cc := by rw [← map_mul, inv_mul_cancel_right]
      have hr : (r (g * D.cc⁻¹)).right = 1 := (h.mult _).trans hk
      have e2 : (r g).mat = (r (g * D.cc⁻¹)).mat := by
        have hrc := h.norm.atc
        rw [e1]
        simp only [GG.mat] at hrc ⊢
        rw [SemidirectProduct.mul_left, hr, sgnAct_one, Units.val_mul, hrc, Matrix.mul_one]
      obtain ⟨a, b, c, d, h1, h2⟩ := hblk0 _ hk
      exact ⟨a, b, c, d, h1, e2.trans h2⟩
  let θ : G ℚ Ω →* (PadicAlgCl l)ˣ := (Units.map (Int.castRingHom (PadicAlgCl l)).toMonoidHom).comp D.η
  have hθ0 : ∀ g, (θ g : PadicAlgCl l) = ((D.η g : ℤˣ) : ℤ) := fun g => rfl
  have hθ : ∀ g, (θ g : PadicAlgCl l) = if (r g).right = 1 then 1 else -1 := by
    intro g
    rw [hθ0, h.mult g]
    rcases Int.units_eq_one_or (D.η g) with hg | hg <;> simp [hg]
  obtain ⟨hB1, hB2⟩ := _root_.UpperTheory.V.Z.Kato.WeilSphericalRecords.kUse' hK D (θ := θ) (_root_.UpperTheory.V.Z.Kato.used_of_alt hC D hm h hII W hext hWc hW hWd ι (hmod W hext)) ι (hmod W hext)
  haveI : IsAlgClosure K Ω := by
    haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
    haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
    exact ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩
  have hker : ∀ s : G K Ω, D.η (s.restrictScalars ℚ) = 1 := fun s => by
    have : galEmb ℚ K Ω s ∈ D.η.ker := D.η_ker ▸ galEmb_mem ℚ K Ω s
    exact this
  have hrc : (r D.cc).right = -1 := (h.mult _).trans hηc
  have hWcc : (W D.cc).val = !![-1, 0; 0, 1] := by
    have hx' : (r D.cc).mat = !![1, 0, 0; 0, 1, 0; 0, 0, 1] := by
      rw [h.norm.atc]; ext i j; fin_cases i <;> fin_cases j <;> simp
    rw [hW', wOf_eq hx', if_neg (by rw [hrc]; decide), neg_zero]
  have hA : Af.BlochKatoSelmerVanishes l (repA r hblk) := by
    refine hR W hWc hext hWd (hmod W hext) θ hθ0 _ ⟨D.cc, Jgl _ 2, D.conj, fun s s' hs => ?_, fun s X => ?_, fun X => ?_⟩
    · have e1 : W (s'.restrictScalars ℚ) = W D.cc * W (s.restrictScalars ℚ) * W D.cc := by
        rw [hs, inv_eq_of_mul_eq_one_right hcc, map_mul, map_mul]
      have e2 := hWd (s.restrictScalars ℚ)
      change (W (s.restrictScalars ℚ)).valᵀ * Jmat _ 2 *
        (W (s'.restrictScalars ℚ)).val =
          (θ (s.restrictScalars ℚ) : PadicAlgCl l) • Jmat _ 2
      rw [e1, hθ0, ← e2, Units.val_mul, Units.val_mul, hWcc]
      exact pair_eq _
    · exact pA_ad_one (hblk _) ((h.mult _).trans (hker s)) _ (hW' _) X
    · exact pA_ad_c h.norm.atc hrc X
  intro γ hγ hbk
  have eA : ∀ g X, pA (adRep r g X) = repA r hblk g (pA X) := fun g X => pA_ad (hblk g) X
  have eA' : ∀ g Y, sA (repA r hblk g Y) = adRep r g (sA Y) := fun g Y => ad_sA (hblk g) Y
  have t1 : ∀ g v, Loc.colRep (Af.tw W 1) g v =
      ((if (r g).right = 1 then 1 else 1 : PadicAlgCl l) • wOf (r g)) *ᵥ v := fun g v => by
    rw [← hW', ite_self]
    exact congrArg (· *ᵥ v) (Af.tw_val W 1 g)
  have t2 : ∀ g v, Loc.colRep (Af.tw W θ) g v =
      ((if (r g).right = 1 then 1 else -1 : PadicAlgCl l) • wOf (r g)) *ᵥ v := fun g v => by
    rw [← hW', ← hθ]
    exact congrArg (· *ᵥ v) (Af.tw_val W θ g)
  have eB1 : ∀ g X, pB 1 (adRep r g X) = Loc.colRep (Af.tw W 1) g (pB 1 X) := fun g X => by
    rw [t1]; exact pB_ad (hblk g) 1 (by ring) X
  have eB1' : ∀ g v, sB 1 (Loc.colRep (Af.tw W 1) g v) = adRep r g (sB 1 v) := fun g v => by
    rw [t1]; exact ad_sB (hblk g) 1 (by ring) v
  have eB2 : ∀ g X, pB (-1) (adRep r g X) = Loc.colRep (Af.tw W θ) g (pB (-1) X) := fun g X => by
    rw [t2]; exact pB_ad (hblk g) (-1) (by ring) X
  have eB2' : ∀ g v, sB (-1) (Loc.colRep (Af.tw W θ) g v) = adRep r g (sB (-1) v) := fun g v => by
    rw [t2]; exact ad_sB (hblk g) (-1) (by ring) v
  have hblkz : ∀ g, IsBlockSL2Embedding (r0 D.η D.ΨQ g) := fun g => isBlock_reducible_three_dim _ _ g
  have eC : ∀ g X, pC (adRep r g X) = adRep (r0 D.η D.ΨQ) g (pC X) := fun g X => by
    refine (pC_ad (hblk g) X).trans (Eq.trans ?_ (ad_pC (hblkz g) X).symm)
    rw [h.mult g, unitaryThreeReflection_right]
  have eC' : ∀ g X, pC (adRep (r0 D.η D.ΨQ) g X) = adRep r g (pC X) := fun g X => by
    refine (pC_ad (hblkz g) X).trans (Eq.trans ?_ (ad_pC (hblk g) X).symm)
    rw [h.mult g, unitaryThreeReflection_right]
  have cont_pA {R : Type} [CommRing R] [TopologicalSpace R] : Continuous (pA : Matrix (Fin 3) (Fin 3) R → _) := by
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> exact continuous_id.matrix_elem _ _

  have cont_pB {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (t : R) : Continuous (pB t) := by
    refine continuous_pi fun i => ?_
    fin_cases i
    · exact (continuous_id.matrix_elem 0 1).add (continuous_const.mul (continuous_id.matrix_elem 1 2))
    · exact (continuous_id.matrix_elem 2 1).sub (continuous_const.mul (continuous_id.matrix_elem 1 0))

  have cont_pC {R : Type} [CommRing R] [TopologicalSpace R] : Continuous (pC : Matrix (Fin 3) (Fin 3) R → _) := by
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> first | exact continuous_const | exact continuous_id.matrix_elem 1 1

  dbg_trace "bk_map"
  have bk_map {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime]
      {C : Type} [CommRing C] [Algebra ℚ_[l] C]
      {V : Type} [AddCommGroup V] [Module C V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] C V] [TopologicalSpace V]
      [IsTopologicalAddGroup V] [ContinuousConstSMul C V]
      {V' : Type} [AddCommGroup V'] [Module C V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] C V'] [TopologicalSpace V']
      [IsTopologicalAddGroup V'] [ContinuousConstSMul C V']
      (ρ : Representation C (G F Ω) V) (ρ' : Representation C (G F Ω) V') (f : V →ₗ[C] V') (hfc : Continuous f)
      (hf : ∀ g x, f (ρ g x) = ρ' g (f x)) {γ : G F Ω → V} (h1 : γ ∈ Z1 ρ) (h2 : Af.IsBK l ρ γ) :
      (fun g => f (γ g)) ∈ Z1 ρ' ∧ Af.IsBK l ρ' (fun g => f (γ g)) := by
    refine ⟨⟨hfc.comp h1.1, fun g h => by simp only [h1.2 g h, map_add (f := _), hf]⟩, fun w hw => ?_, fun τ => ?_⟩
    · obtain ⟨A, hA, x, hx⟩ := h2.away w hw
      exact ⟨A, hA, f x, fun s hs => by simp only [hx s hs, map_sub, hf]⟩
    · obtain ⟨j, hj, ⟨hc, hcc⟩, x, hx⟩ := h2.above τ
      refine ⟨j, hj, ⟨hfc.comp hc, fun g h => ?_⟩, LinearMap.rTensor (Loc.Bcr l) (f.restrictScalars ℚ_[l]) x, fun g => ?_⟩
      · have := congrArg f (hcc g h)
        rw [map_add (f := _)] at this
        exact this.trans (congrArg _ (hf _ _))
      · have key : ∀ y : V ⊗[ℚ_[l]] Loc.Bcr l, LinearMap.rTensor (Loc.Bcr l) (f.restrictScalars ℚ_[l])
            (Loc.actC ((MonoidHom.snd _ _).comp (Af.decJ F j).subtype)
              (ρ.comp ((MonoidHom.fst _ _).comp (Af.decJ F j).subtype)) g y) =
            Loc.actC ((MonoidHom.snd _ _).comp (Af.decJ F j).subtype)
              (ρ'.comp ((MonoidHom.fst _ _).comp (Af.decJ F j).subtype)) g
              (LinearMap.rTensor (Loc.Bcr l) (f.restrictScalars ℚ_[l]) y) := by
          intro y
          induction y using TensorProduct.induction_on with
          | zero => simp
          | tmul a b => simp [Loc.actC, hf]
          | add a b ha hb => simp only [map_add (f := _), ha, hb]
        rw [← key, ← map_sub, ← hx g, LinearMap.rTensor_tmul]
        rfl
  obtain ⟨zA, bA⟩ := bk_map (adRep r) (repA r hblk) pA cont_pA eA hγ hbk
  obtain ⟨z1, b1⟩ := bk_map (adRep r) _ (pB 1) (cont_pB 1) eB1 hγ hbk
  obtain ⟨z2, b2⟩ := bk_map (adRep r) _ (pB (-1)) (cont_pB (-1)) eB2 hγ hbk
  obtain ⟨zC, bC⟩ := bk_map (adRep r) _ pC cont_pC eC hγ hbk
  obtain ⟨xA, hxA⟩ := (mem_coboundaries1 _ _).1 (hA _ zA bA)
  obtain ⟨x1, hx1⟩ := (mem_coboundaries1 _ _).1 (hB1 _ z1 b1)
  obtain ⟨x2, hx2⟩ := (mem_coboundaries1 _ _).1 (hB2 _ z2 b2)
  obtain ⟨xC, hxC⟩ := (mem_coboundaries1 _ _).1
    (bloch_kato_nonpositive_weight hC D 0 le_rfl _ zC (fun g => pC_mem (γ g)) bC)
  refine (mem_coboundaries1 _ _).2 ⟨sA xA + (2⁻¹ : PadicAlgCl l) • sB 1 x1 + (2⁻¹ : PadicAlgCl l) • sB (-1) x2 + pC xC, fun g => ?_⟩
  rw [decomp (2⁻¹ : PadicAlgCl l) (by norm_num) (γ g), hxA g, hx1 g, hx2 g, hxC g]
  simp only [map_sub, map_add (f := _), map_smul, eA', eB1', eB2', eC', smul_sub]
  abel
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3
theorem UpperTheory.V.Z.J.ptHyp_of_autB_of_lemW_of_isBase :
    U3.CohInp → _root_.UpperTheory.V.Z.Kato.WeilSphericalRecords.KatoTwoW → _root_.UpperTheory.V.Th.RigidityFirstCase → _root_.UpperTheory.V.Th.RigiditySecondCase → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) {U : (_root_.UpperTheory.V.U3.Univ (_root_.UpperTheory.V.U3.GCond.noCondition _ (D.η.comp D.ι) (D.Ψ.comp D.ι)))} {g₁ : G ℚ Ω}, D.Marked g₁ → ∀ (S : D.Ring U g₁), ∀ [IsCMField K] (ι : Qbar l ≃+* ℂ), _root_.UpperTheory.V.Aut.AutBAlt D ι g₁ → _root_.UpperTheory.V.Aut.LemWAlt D ι g₁ →
      ∀ x₀ : S.R →ₐ[c.O] c.O, IsBase D.η D.Ψ S.r.hom x₀ → PtHyp D.η S.r.hom x₀ := by
  intro hC hK hRI hRII Ω _ _ _ K _ _ _ l _ c N _ e ψ D U g₁ hM S _ ι hB hW x₀ hx
  have h0 : push (toBar x₀) S.r.hom = r0 D.η D.ΨQ := by
    have e1 : push (toBar x₀) S.r.hom =
        (GG.map (algebraMap c.O (PadicAlgCl l))).comp (push x₀ S.r.hom) := rfl
    rw [e1, show push x₀ S.r.hom = r0 D.η D.Ψ from hx]
    refine MonoidHom.ext fun g => SemidirectProduct.ext (Units.ext ?_) rfl
    let φ := algebraMap c.O (PadicAlgCl l)
    show (tor c.O (D.Ψ g) : Matrix (Fin 3) (Fin 3) c.O).map φ =
      tor (PadicAlgCl l) (Units.map φ.toMonoidHom (D.Ψ g))
    rw [tor_val, tor_val, Matrix.diagonal_map (map_zero _)]
    congr 1
    funext i
    exact congrArg Units.val (map_zpow (Units.map φ.toMonoidHom) (D.Ψ g) (wt1 i))
  have hCob {Γ κ : Type} [Group Γ] [CommRing κ] (r : Γ →* GG (m := 3) (R := κ))
      (γ : Γ → Matrix (Fin 3) (Fin 3) κ) (h : γ ∈ ReciprocityTheory.Gal.B1 (adRep r)) :
      ∃ X, γ = cob r X := by
    obtain ⟨X, rfl⟩ := LinearMap.mem_range.mp h
    refine ⟨-X, funext fun g => ?_⟩
    show adRep r g X - X = -X - adRep r g (-X)
    rw [map_neg]
    abel
  refine ⟨fun f hf hU hL => ?_, fun j hj F hF hw => ?_, fun f hf F hF => ?_⟩
  · rw [h0]
    exact pt_fixed hC D hM (isPt_push D hM S f hf) hU hL
  · have hLoc : IsLocPt (toBar x₀) := by
      intro y hy
      have hsurj : Function.Surjective x₀ := fun a => ⟨algebraMap c.O S.R a, x₀.commutes a⟩
      have hmax : (Ideal.comap (x₀ : S.R →+* c.O) (IsLocalRing.maximalIdeal c.O)).IsMaximal :=
        Ideal.comap_isMaximal_of_surjective _ hsurj
      have hxy : x₀ y ∈ IsLocalRing.maximalIdeal c.O := by
        change y ∈ Ideal.comap (x₀ : S.R →+* c.O) (IsLocalRing.maximalIdeal c.O)
        rwa [IsLocalRing.eq_maximalIdeal hmax]
      have hnonunit := (IsLocalRing.mem_maximalIdeal _).mp hxy
      change ‖(x₀ y : PadicAlgCl l)‖ < 1
      by_cases hzero : x₀ y = 0
      · simp [hzero]
      have hval : (IsDiscreteValuationRing.addVal c.O (x₀ y)).toNat ≠ 0 := by
        rw [Ne, ENat.toNat_eq_zero, IsDiscreteValuationRing.addVal_eq_zero_iff,
          IsDiscreteValuationRing.addVal_eq_top_iff]
        exact fun h => h.elim hnonunit hzero
      have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
      have hpow := pow_lt_one₀ (by positivity) (inv_lt_one_of_one_lt₀ hl) hval
      rw [← normO l c.O (x₀ y) hzero] at hpow
      exact lt_of_not_ge fun h => (not_lt_of_ge (one_le_pow₀ h)) hpow
    have h1 := tanCoc_isBK hC D hM S F (hF ▸ hLoc)
    rw [hF, h0] at h1
    rw [h0]
    exact hCob _ _ (bloch_kato_nonpositive_weight hC D j hj _ h1.1 hw h1.2)
  · have h1 := tanCoc_isBK hC D hM S F (hF ▸ hf.1)
    rw [hF] at h1
    have hp := isPt_push D hM S f hf.1
    have hPush : IsPush (f.comp (entAlg c.O S.r.hom).val) S.r.hom (push f S.r.hom) := by
      intro g
      refine ⟨rfl, fun a b => ⟨?_, rfl⟩⟩
      unfold entAlg
      exact Algebra.subset_adjoin ⟨g, a, b, rfl⟩
    have hz : Af.BlochKatoSelmerVanishes l (adRep (push f S.r.hom)) := by
      rcases (twoPt_shape S D.gd.l_odd hM f hf).1 with h | h
      · exact hRI D hM S f hf.1 hp.mult ι h (hB U S _ _ hp.mult hPush h)
      · exact _root_.UpperTheory.V.Z.Kato.WeilSphericalRecords.bloch_kato_selmer_vanishes_of_type_ii_modular_ext hC hK hRII D hM S f hf.1 ι h
          (hW U S _ _ hPush h (typeII_facts hC D hM hp h).1)
    exact hCob _ _ (hz _ h1.1 h1.2)
end
