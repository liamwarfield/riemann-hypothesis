module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.DistributionApply
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.InOfIntIff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsModularFunctionTowerAlgebraicCoefficients
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.SmoothedZetaClassHodgeTateLawStatement
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.ChiQuad
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrdinaryEisensteinEigenfunctionalExists
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeProjectorNewformGaloisImage

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.GmEx
open UpperTheory.V.Z.Kato.Joint
open scoped Matrix MatrixGroups

theorem UpperTheory.V.Z.Kato.Joint.gmEx :
    UpperTheory.V.Z.Kato.Joint.GmEx := by
  intro l _ N h
  have hN : (N : ZMod l) * (N : ZMod l)⁻¹ = 1 := ZMod.coe_mul_inv_eq_one N h.symm
  let m : (ZMod l)ˣ → ℤ := fun r => (((-(r : ZMod l)) * (N : ZMod l)⁻¹).val : ℤ)
  have hm : ∀ r : (ZMod l)ˣ, (N : ZMod l) * ((m r : ℤ) : ZMod l) = -(r : ZMod l) := by
    intro r
    simp only [m, Int.cast_natCast, ZMod.natCast_zmod_val]
    rw [mul_left_comm, hN, mul_one]
  refine ⟨fun r => ⟨!![1, 0; (N : ℤ) * m r, 1], by simp [Matrix.det_fin_two]⟩, fun r => ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine (CongruenceSubgroup.Gamma1_mem N _).2 ⟨?_, ?_, ?_⟩ <;> simp
  · simp
  · simp [hm r]
  · refine ⟨-1, ?_⟩
    ext i
    fin_cases i <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, hm r]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.TowerEx
open UpperTheory.V.Z.Kato.Joint

theorem UpperTheory.V.Z.Kato.Joint.towerEx :
    UpperTheory.V.Z.Kato.Joint.TowerEx := by
  intro Ω _ _ _ ε
  obtain ⟨T, -⟩ := GlobalTheory.T.exists_modular_function_tower_algebraic_coefficients Ω ε
  exact ⟨T⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.ChiStab
open UpperTheory.V.Z.Kato.Joint

theorem UpperTheory.V.Z.Kato.Joint.chiStab :
    UpperTheory.V.Z.Kato.Joint.ChiStab := by
  intro l hp Ω _ _ _ ε X N w χ hl hlN hN hw T b hT hb
  have hNl : Nat.Coprime N l := ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hlN).symm
  obtain ⟨φ, h1, h2⟩ := X.j_hol
  refine ⟨GlobalTheory.T.hecke_letter_preserves_basis_set ε X ε.injective ⟨φ, h2, h1⟩ N l w hl hN hNl hw T hT b hb.1, fun d hd => ?_⟩
  have h := GlobalTheory.T.modularTowerB_admissibleHecke_commute ε X ε.injective ⟨φ, h2, h1⟩ N l w hl hN hNl hw T (GlobalTheory.KZ.Letter.D d) hT hd b hb.1
  change X.op N l T (X.diam N l d b) = X.diam N l d (X.op N l T b) at h
  rw [← h, hb.2 d hd, map_smul]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.CgpTrans
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.CyclotomicQExpansion GlobalTheory.KummerEisensteinGalois GlobalTheory.K4 GlobalTheory.LambdaValuationPowers
open scoped Matrix MatrixGroups TensorProduct

namespace UpperTheory.V.Z.Kato.Joint

variable {l : ℕ} [Fact l.Prime]

private theorem cgp_refl (n : ℕ) (x : Qbar l) : Cg n x x := by simp [Cg]

private theorem cgp_symm {n : ℕ} {x y : Qbar l} (h : Cg n x y) : Cg n y x := by
  unfold Cg at *
  rwa [norm_sub_rev]

private theorem cgp_add {n : ℕ} {x y x' y' : Qbar l} (h : Cg n x y) (h' : Cg n x' y') : Cg n (x + x') (y + y') := by
  unfold Cg at *
  rw [add_sub_add_comm]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h h')

private theorem cgp_trans {n : ℕ} {x y z : Qbar l} (h : Cg n x y) (h' : Cg n y z) : Cg n x z := by
  unfold Cg at *
  rw [← sub_add_sub_cancel x y z]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h h')

private theorem cgp_mul {n : ℕ} {a x y : Qbar l} (ha : ‖a‖ ≤ 1) (h : Cg n x y) : Cg n (a * x) (a * y) := by
  simpa using cg_mul_left (k := 0) (Nat.zero_le _) (by simpa using ha) h

private theorem fop_cg {k n : ℕ} {χ : ℕ → Qbar l} (hχ : ∀ d, ‖χ d‖ ≤ 1) (T : Letter) {f g : ℕ → Qbar l}
    (h : ∀ i, Cg n (f i) (g i)) (i : ℕ) : Cg n (fop k l χ T f i) (fop k l χ T g i) := by
  cases T with
  | T q =>
    show Cg n (GlobalTheory.EisM.To k (χ q) q f i) (GlobalTheory.EisM.To k (χ q) q g i)
    unfold GlobalTheory.EisM.To GlobalTheory.EisM.Vo
    refine cgp_add (h _) (cgp_mul ?_ ?_)
    · rw [norm_mul, norm_pow]
      exact mul_le_one₀ (hχ q) (by positivity)
        (pow_le_one₀ (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _))
    · split_ifs
      · exact h _
      · exact cgp_refl _ _
  | U => exact h _
  | D d => exact cgp_mul (hχ d) (h i)

theorem thP : ThP := by
  intro hOp hStab l _ Ω _ _ _ ε X A N w j χ hS P hP
  set F := FreeAlgebra.lift (Qbar l) (fop (w + 2) l fun d => ((χ d : ℤ_[l]) : Qbar l)) with hF
  set G := FreeAlgebra.lift (Qbar l) (X.opV N l (Qbar l)) with hG
  have hχ : ∀ d, ‖((χ d : ℤ_[l]) : Qbar l)‖ ≤ 1 := fun d => by
    rw [norm_algebraMap']
    exact (χ d).2
  have hw : ∀ x ∈ Submonoid.closure (FreeAlgebra.ι (Qbar l) '' {T | GlobalTheory.KZ.admitted N l T}), ∀ n : ℕ,
      (∀ f g : ℕ → Qbar l, (∀ i, Cg n (f i) (g i)) → ∀ i, Cg n (F x f i) (F x g i)) ∧
      ∀ b, InChi X N w χ b → ∃ b', InChi X N w χ b' ∧
        G x ((1 : Qbar l) ⊗ₜ[ℤ_[l]] b) = (1 : Qbar l) ⊗ₜ[ℤ_[l]] b' ∧
        ∀ i, Cg n (F x (th X A N j n b) i) (th X A N j n b' i) := by
    intro x hx n
    induction hx using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨T, hT, rfl⟩ := hx
      rw [hF, hG, FreeAlgebra.lift_ι_apply, FreeAlgebra.lift_ι_apply]
      refine ⟨fun f g h i => fop_cg hχ T h i, fun b hb => ⟨X.op N l T b,
        hStab l Ω ε X N w χ hS.2.1 hS.2.2.1 hS.2.2.2.1 hS.2.2.2.2.1 T b hT hb, ?_,
        fun i => cgp_symm (hOp l Ω ε X A N w j χ hS n T b hT hb i)⟩⟩
      rw [Tower.opV, LinearMap.baseChange_tmul]
    | one =>
      rw [map_one, map_one]
      exact ⟨fun f g h i => h i, fun b hb => ⟨b, hb, rfl, fun i => cgp_refl _ _⟩⟩
    | mul x y _ _ hx hy =>
      rw [map_mul, map_mul]
      refine ⟨fun f g h i => hx.1 _ _ (hy.1 f g h) i, fun b hb => ?_⟩
      obtain ⟨b', hb', e', c'⟩ := hy.2 b hb
      obtain ⟨b'', hb'', e'', c''⟩ := hx.2 b' hb'
      refine ⟨b'', hb'', ?_, fun i => cgp_trans (hx.1 _ _ c' i) (c'' i)⟩
      rw [Module.End.mul_apply, e', e'']
  have hP' : P ∈ Submodule.span (Qbar l)
      (Submonoid.closure (FreeAlgebra.ι (Qbar l) '' {T | GlobalTheory.KZ.admitted N l T}) : Set (FreeAlgebra (Qbar l) Letter)) := by
    rw [← Algebra.adjoin_eq_span]
    exact hP
  clear hP
  induction hP' using Submodule.span_induction with
  | mem x hx =>
    refine ⟨0, fun n _ Θ hΘ b hb i => ?_⟩
    obtain ⟨b', hb', e', c'⟩ := (hw x hx n).2 b hb
    rw [e', Nat.sub_zero]
    exact cgp_trans (c' i) (cgp_symm (hΘ b' hb'.1 i))
  | zero =>
    refine ⟨0, fun n _ Θ hΘ b hb i => ?_⟩
    simp only [map_zero, LinearMap.zero_apply]
    exact cgp_refl _ _
  | add x y _ _ hx hy =>
    obtain ⟨c, hc⟩ := hx
    obtain ⟨d, hd⟩ := hy
    refine ⟨c + d, fun n hn Θ hΘ b hb i => ?_⟩
    simp only [map_add (f := _), LinearMap.add_apply, Pi.add_apply]
    exact cgp_add (cg_mono (by omega) (hc n (by omega) Θ hΘ b hb i))
      (cg_mono (by omega) (hd n (by omega) Θ hΘ b hb i))
  | smul a x _ hx =>
    obtain ⟨c, hc⟩ := hx
    obtain ⟨k, hk⟩ := exists_le_l_pow l ‖a‖
    refine ⟨c + k, fun n hn Θ hΘ b hb i => ?_⟩
    simp only [map_smul, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
    rw [← Nat.sub_sub]
    exact cg_mul_left (by omega) hk (hc n (by omega) Θ hΘ b hb i)

end UpperTheory.V.Z.Kato.Joint

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.RhoFrobAlt
open UpperTheory.V.Z.Kato.Joint

theorem UpperTheory.V.Z.Kato.Joint.rhoFrob :
    UpperTheory.V.Z.Kato.Joint.RhoFrob := by
  intro l _ Ω _ _ _ ι e S A W g χ hN _ hatt ρ hρ
  have h : ∀ s, (ρ s : Matrix (Fin 2) (Fin 2) (Formalism.ConjugateSelfDual.Qbar l)) = _ := fun s =>
    (hρ s).trans (GlobalTheory.RhoAdm.untw_val' e W χ s).symm
  refine ⟨?_, fun V hV => GlobalTheory.RhoAdm.untw_irr e W χ hN.irr V fun s v hv => ?_⟩
  · obtain ⟨S0, hS0⟩ := GlobalTheory.RhoAdm.frob_trace_det ι e W g χ hatt
    refine ⟨S0, fun q hq hqS s hs => ?_⟩
    rw [h s]
    exact hS0 q hq hqS s hs
  · rw [← h s]
    exact hV s v hv
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.AvgMF
open UpperTheory.V.Z.Kato.Joint GlobalTheory.EisM

theorem UpperTheory.V.Z.Kato.Joint.avgMF :
    UpperTheory.V.Z.Kato.Joint.AvgMF := by
  intro k l N m θ χ f t α B c hp hk hodd hN hlN hm hχ hf hα hE
  haveI : NeZero N := ⟨hN.ne'⟩
  have hsq : ∀ ν : DirichletCharacter ℂ N, ν (-1) * ν (-1) = 1 := fun ν => by rw [← map_mul]; simp
  have hform : ∀ ν : DirichletCharacter ℂ N, ν (-1) = -θ (-1) → MF k (N * l) (ch (θ⁻¹ * ν)) (frm l N m k θ ν f) :=
    fun ν hν => (GlobalTheory.iterU_level_val_stable k N l m (θ⁻¹ * ν) (fun _ => 0) α B c _ (by omega) hp hα
      (GlobalTheory.T.isModularFormCoeffSeq_eisensteinProduct_parity k N l m (θ⁻¹ * ν) θ ν f hk hodd hN hp hm hlN rfl hν hf)).1
  have hsign : (θ * χ) (-1) = -θ (-1) := by
    rw [MulChar.coeToFun_mul, Pi.mul_apply, hχ]; ring
  have hmain := hform (θ * χ) hsign
  rw [inv_mul_cancel_left] at hmain
  refine ⟨hmain, ?_⟩
  have hφ : (N.totient : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.2 hN).ne'
  have htw : tw2 N (θ (-1)) =
      fun y => ∑ ν : DirichletCharacter ℂ N, ((N.totient : ℂ)⁻¹ * (1 - θ (-1) * ν (-1))) * ch ν y := by
    funext y
    rw [GlobalTheory.T.tw2_eq_inv_totient_mul_sum_characters N (θ (-1)) hN y, Finset.mul_sum]
    exact Finset.sum_congr rfl fun ν _ => by ring
  have hmes : mesMu k l (hat θ) (tw2 N (θ (-1))) α B c m f =
      ∑ ν : DirichletCharacter ℂ N, ((N.totient : ℂ)⁻¹ * (1 - θ (-1) * ν (-1))) *
        ((α ^ m)⁻¹ * lam B c (frm l N m k θ ν f)) := by
    unfold mesMu
    rw [htw, funext (measMu_zm_sum k l (hat θ) Finset.univ _ _ _), measMu_val_sum]
    rfl
  rw [hmes, Finset.sum_eq_single_of_mem (θ * χ) (Finset.mem_univ _)]
  · have h2 : (1 : ℂ) - θ (-1) * (θ * χ) (-1) = 2 := by
      rw [hsign]; linear_combination hsq θ
    rw [h2]
    field_simp
  · intro ν _ hne
    have h0 : (ν (-1) - θ (-1)) * (ν (-1) + θ (-1)) = 0 := by linear_combination hsq ν - hsq θ
    rcases mul_eq_zero.1 h0 with h | h
    · rw [sub_eq_zero.1 h, hsq θ]; ring
    · have hne' : θ⁻¹ * ν ≠ χ := fun h' => hne (by rw [← h', mul_inv_cancel_left])
      rw [hE.kill _ _ hne' (hform ν (eq_neg_of_add_eq_zero_left h))]
      ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.SmNzNorm
open UpperTheory.V.Z.Kato.Joint

private lemma smNz_unit {l : ℕ} [Fact l.Prime] {n : ℕ} (h : ¬ l ∣ n) : IsUnit (n : ZMod l) := by
  rw [isUnit_iff_ne_zero, Ne, ZMod.natCast_eq_zero_iff]
  exact h

private lemma smNz_norm {l : ℕ} [Fact l.Prime] (χ : DirichletCharacter ℂ l) {n : ℕ} (h : ¬ l ∣ n) :
    ‖χ (n : ZMod l)‖ = 1 := by
  have hu := smNz_unit (l := l) h
  have := χ.unit_norm_eq_one hu.unit
  rwa [IsUnit.unit_spec] at this

theorem UpperTheory.V.Z.Kato.Joint.smNz :
    UpperTheory.V.Z.Kato.Joint.SmNz := by
  intro l _ ι e N c d ψ a b hN hN0 hc0 hd0 hc hd ha hce hdb
  have hp : l.Prime := Fact.out
  refine ⟨?_, ?_⟩
  · intro i
    fin_cases i <;> simp [smT, hp.dvd_mul, hN, hc, hd]
  · simp only [Fin.sum_univ_four, smB, smT, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, map_mul,
      map_neg, map_pow, map_zpow₀, map_natCast, RingEquiv.apply_symm_apply, Nat.cast_mul,
      MulChar.inv_apply_eq_inv', mul_pow]
    have hC : (c : ℂ) ≠ 0 := by exact_mod_cast hc0.ne'
    have hD : (d : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
    have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN0.ne'
    have hψN : ψ (N : ZMod l) ≠ 0 := by
      intro h0
      have := smNz_norm ψ hN
      rw [h0, norm_zero] at this
      exact zero_ne_one this
    have hψc : ψ (c : ZMod l) ≠ 0 := by
      intro h0
      have := smNz_norm ψ hc
      rw [h0, norm_zero] at this
      exact zero_ne_one this
    have hCe : (c : ℂ) ^ e ≠ 0 := pow_ne_zero _ hC
    have hw : (c : ℂ) ^ ((3 : ℤ) - ((2 * e + 1 : ℕ) : ℤ)) * (c : ℂ) ^ e = (c : ℂ) ^ 2 * ((c : ℂ) ^ e)⁻¹ := by
      rw [← zpow_natCast (c : ℂ) e, ← zpow_add₀ hC, ← zpow_natCast (c : ℂ) 2, ← zpow_neg,
        ← zpow_add₀ hC]
      congr 1
      push_cast
      ring
    set w := (c : ℂ) ^ ((3 : ℤ) - ((2 * e + 1 : ℕ) : ℤ)) with hwdef
    have hfac : (c : ℂ) ^ 2 * (d : ℂ) ^ 2 * (ψ (N : ZMod l))⁻¹ * (N : ℂ) ^ e +
        -(w * a * (d : ℂ) ^ 2) * (ψ (N : ZMod l) * ψ (c : ZMod l))⁻¹ * ((N : ℂ) ^ e * (c : ℂ) ^ e) +
        -((c : ℂ) ^ 2 * ((d : ℂ) * b)) * (ψ (N : ZMod l) * ψ (d : ZMod l))⁻¹ * ((N : ℂ) ^ e * (d : ℂ) ^ e) +
        w * a * ((d : ℂ) * b) * (ψ (N : ZMod l) * ψ (c : ZMod l) * ψ (d : ZMod l))⁻¹ *
          ((N : ℂ) ^ e * (c : ℂ) ^ e * (d : ℂ) ^ e) =
        (N : ℂ) ^ e * (ψ (N : ZMod l))⁻¹ *
          ((c : ℂ) ^ 2 - w * (c : ℂ) ^ e * a * (ψ (c : ZMod l))⁻¹) *
          ((d : ℂ) ^ 2 - (d : ℂ) * b * (d : ℂ) ^ e * (ψ (d : ZMod l))⁻¹) := by
      ring
    rw [hfac, hw]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hNc) (inv_ne_zero hψN)) ?_) ?_
    · have h1 : (c : ℂ) ^ 2 - (c : ℂ) ^ 2 * ((c : ℂ) ^ e)⁻¹ * a * (ψ (c : ZMod l))⁻¹ =
          (c : ℂ) ^ 2 * ((c : ℂ) ^ e)⁻¹ * ((c : ℂ) ^ e - a * (ψ (c : ZMod l))⁻¹) := by
        field_simp
      rw [h1]
      refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ hC) (inv_ne_zero hCe)) ?_
      rw [sub_ne_zero]
      apply hce
      rw [norm_mul, norm_inv, ha, smNz_norm ψ hc]
      norm_num
    · intro h0
      apply hdb
      rw [zpow_neg_one, pow_succ]
      linear_combination h0
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.Imports
open UpperTheory.V.Z.Kato.Joint

theorem UpperTheory.V.Z.Kato.Joint.mono :
    UpperTheory.V.Z.Kato.Joint.Mono := by
  intro l _ Ω _ _ c c' h
  refine ⟨?_, ?_, ?_⟩
  · rintro W y S' ⟨h1, h2, h3, h4, h5⟩
    refine ⟨fun s i j => h (h1 s i j), h2, fun s i => h (h3 s i), h4, fun n hn w hw hd ψ hk hs => ?_⟩
    obtain ⟨Y, P, u, b, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h5 n hn w hw hd ψ hk hs
    refine ⟨Y, P, u, b, a1, fun s x i => h (a2 s x i), h a3, a4, fun i => h (a5 i), a6, a7, a8, fun q hq hl => ?_⟩
    obtain ⟨B, hB, t, ht, ht'⟩ := a9 q hq hl
    exact ⟨B, hB, t, fun x i => h (ht x i), ht'⟩
  · rintro A ν Z ⟨h1, h2, h3⟩
    exact ⟨h1, fun r => ⟨fun s x => h ((h2 r).1 s x), (h2 r).2⟩, h3⟩
  · rintro A Z j m₀ c₀ Rhs ⟨ζ, hζ, H⟩
    refine ⟨ζ, hζ, fun m hm => ?_⟩
    obtain ⟨ι, inst, P, o, ⟨p1, p2, p3, p4, p5⟩, hc⟩ := H m hm
    exact ⟨ι, inst, P, o, ⟨p1, p2, fun i => h (p3 i), p4, p5⟩, hc⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.PsiEx
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ
open UpperTheory.V.Z.Kato.Joint

private theorem apply_eq_pow_cycMod_of_pow_eq_one (l : ℕ) [Fact (Nat.Prime l)] (Ω : Type) [Field Ω] [Algebra ℚ Ω]
    [IsAlgClosure ℚ Ω] (s : G ℚ Ω) (ζ : Ω) (hζ : ζ ^ l = 1) :
    s ζ = ζ ^ ((cycMod ℚ Ω l 1 s : ZMod (l ^ 1)).val) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := (RingHom.charZero_iff (algebraMap ℚ Ω).injective).1 inferInstance
  haveI : NeZero (l : Ω) := ⟨Nat.cast_ne_zero.2 (Fact.out : Nat.Prime l).ne_zero⟩
  exact cyclotomicCharacter.spec l (n := 1) (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) ζ
    (by rwa [pow_one])

private theorem cyc1_surjective (l : ℕ) [Fact (Nat.Prime l)] (Ω : Type) [Field Ω] [Algebra ℚ Ω]
    [IsAlgClosure ℚ Ω] (u : (ZMod l)ˣ) : ∃ s : G ℚ Ω, cyc1 l s = u := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := (RingHom.charZero_iff (algebraMap ℚ Ω).injective).1 inferInstance
  haveI : NeZero (l : Ω) := ⟨Nat.cast_ne_zero.2 (Fact.out : Nat.Prime l).ne_zero⟩
  haveI : NeZero l := ⟨(Fact.out : Nat.Prime l).ne_zero⟩
  haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω l
  set K := IntermediateField.adjoin ℚ ({ζ} : Set Ω) with hK
  haveI : IsCyclotomicExtension {l} ℚ K := by
    convert hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
    exact Subsingleton.elim _ _
  haveI : NumberField K := IsCyclotomicExtension.numberField {l} ℚ K
  haveI : IsScalarTower ℚ K Ω := IsScalarTower.of_algebraMap_eq (fun x => by simp)
  let σ := (IsCyclotomicExtension.Rat.galEquivZMod l K).symm u
  let ζK : K := ⟨ζ, IntermediateField.mem_adjoin_simple_self ℚ ζ⟩
  have hζK : ζK ^ l = 1 := Subtype.ext (by simpa using hζ.pow_eq_one)
  refine ⟨σ.liftNormal Ω, ?_⟩
  have h1 : (σ.liftNormal Ω) ζ = ζ ^ (u : ZMod l).val := by
    have h2 := σ.liftNormal_commutes Ω ζK
    rw [IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq l K σ hζK,
      show IsCyclotomicExtension.Rat.galEquivZMod l K σ = u from MulEquiv.apply_symm_apply _ u] at h2
    simpa [ζK] using h2
  have h3 := apply_eq_pow_cycMod_of_pow_eq_one l Ω (σ.liftNormal Ω) ζ hζ.pow_eq_one
  rw [h1] at h3
  have hc : (cycMod ℚ Ω l 1 (σ.liftNormal Ω) : ZMod (l ^ 1)).val < l := by
    simpa [pow_one] using ZMod.val_lt (cycMod ℚ Ω l 1 (σ.liftNormal Ω) : ZMod (l ^ 1))
  have h4 := hζ.pow_inj (ZMod.val_lt (u : ZMod l)) hc h3
  unfold cyc1
  rw [← h4, ZMod.natCast_zmod_val]

theorem UpperTheory.V.Z.Kato.Joint.psiEx :
    UpperTheory.V.Z.Kato.Joint.PsiEx := by
  intro l _ Ω _ _ _ ι χ hχ
  have key : ∀ s t : G ℚ Ω, cyc1 l s = cyc1 l t → χ s = χ t := by
    intro s t hst
    have hv : (cycMod ℚ Ω l 1 s : ZMod (l ^ 1)).val = (cycMod ℚ Ω l 1 t : ZMod (l ^ 1)).val := by
      have h1 := congrArg ZMod.val hst
      unfold cyc1 at h1
      have hs : (cycMod ℚ Ω l 1 s : ZMod (l ^ 1)).val < l := by
        simpa [pow_one] using ZMod.val_lt (cycMod ℚ Ω l 1 s : ZMod (l ^ 1))
      have ht : (cycMod ℚ Ω l 1 t : ZMod (l ^ 1)).val < l := by
        simpa [pow_one] using ZMod.val_lt (cycMod ℚ Ω l 1 t : ZMod (l ^ 1))
      rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt ht] at h1
      exact h1
    have hfix : ∀ ζ : Ω, ζ ^ l = 1 → (t⁻¹ * s) ζ = ζ := by
      intro ζ hζ
      rw [AlgEquiv.mul_apply, apply_eq_pow_cycMod_of_pow_eq_one l Ω s ζ hζ, hv, ← apply_eq_pow_cycMod_of_pow_eq_one l Ω t ζ hζ]
      exact t.symm_apply_apply ζ
    have h1 := hχ (t⁻¹ * s) hfix
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1.symm
  have hd : l ∣ l ^ 1 := by rw [pow_one]
  have hcast : ∀ s : G ℚ Ω, cyc1 l s = ZMod.cast (cycMod ℚ Ω l 1 s : ZMod (l ^ 1)) := by
    intro s
    unfold cyc1
    rw [ZMod.cast_eq_val]
  have hone : cyc1 l (1 : G ℚ Ω) = 1 := by
    rw [hcast, map_one, Units.val_one, ZMod.cast_one hd]
  have hmul : ∀ s t : G ℚ Ω, cyc1 l (s * t) = cyc1 l s * cyc1 l t := by
    intro s t
    rw [hcast, hcast, hcast, map_mul, Units.val_mul, ZMod.cast_mul hd]
  let sec : (ZMod l)ˣ → G ℚ Ω := fun u => (cyc1_surjective l Ω u).choose
  have hsec : ∀ u, cyc1 l (sec u) = u := fun u => (cyc1_surjective l Ω u).choose_spec
  let f : (ZMod l)ˣ →* ℂˣ :=
    { toFun := fun u => Units.map ι.toMonoidHom (χ (sec u))
      map_one' := by
        rw [key (sec 1) 1 (by rw [hsec, hone, Units.val_one]), map_one, map_one]
      map_mul' := by
        intro u v
        rw [key (sec (u * v)) (sec u * sec v) (by rw [hsec, hmul, hsec, hsec, Units.val_mul]),
          map_mul, map_mul] }
  refine ⟨MulChar.ofUnitHom f, fun s => ?_⟩
  let w : (ZMod l)ˣ := Units.map (ZMod.castHom hd (ZMod l)).toMonoidHom (cycMod ℚ Ω l 1 s)
  have hw : (w : ZMod l) = cyc1 l s := by
    rw [hcast]
    rfl
  rw [← hw, MulChar.ofUnitHom_coe]
  show (χ s : Formalism.ConjugateSelfDual.Qbar l) = ι.symm (ι (χ (sec w) : Formalism.ConjugateSelfDual.Qbar l))
  rw [RingEquiv.symm_apply_apply, key s (sec w) (by rw [hsec, hw])]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.JEx
open UpperTheory.V.Z.Kato.Joint

theorem UpperTheory.V.Z.Kato.Joint.jEx :
    UpperTheory.V.Z.Kato.Joint.JEx := by
  intro l _ Ω _ _ _ A hA
  obtain ⟨v, hv, hl⟩ := hA
  have hAl : A.valuation ((l : ℕ) : Ω) < 1 := by
    have := (hv ((l : ℕ) : NumberField.RingOfIntegers ℚ)).2 hl
    simpa using this
  exact ⟨(ValuationSubring.mem_nonunits_iff _).2 hAl, Formalism.BasicNotions.Examples₂.LB.exists_emb A hAl⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.EulerSystemNorms
open UpperTheory.V.Z.Kato.Joint Topology Filter

private theorem mem_fixingSubgroup_of_fixes_finite_set (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    (E : IntermediateField K Ω) [FiniteDimensional K E] :
    ∃ T : Finset Ω, ∀ g : Ω ≃ₐ[K] Ω, (∀ x ∈ T, g x = x) → g ∈ E.fixingSubgroup := by
  have h1 : (Subalgebra.toSubmodule E.toSubalgebra).FG :=
    Module.Finite.iff_fg.1 (inferInstanceAs (Module.Finite K E))
  obtain ⟨t, ht⟩ := h1
  refine ⟨t, fun g hg => ?_⟩
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have hle : Algebra.adjoin K (t : Set Ω) ≤ AlgHom.equalizer (g : Ω →ₐ[K] Ω) (AlgHom.id K Ω) :=
    Algebra.adjoin_le (fun y hy => by
      rw [SetLike.mem_coe, AlgHom.mem_equalizer]
      simpa using hg y hy)
  have hx1 : x ∈ Submodule.span K (t : Set Ω) := by
    rw [ht]
    exact hx
  have hx2 : x ∈ Algebra.adjoin K (t : Set Ω) := Algebra.span_le_adjoin K _ hx1
  have hx3 := hle hx2
  rw [AlgHom.mem_equalizer] at hx3
  simpa using hx3

private theorem uniform_continuity_galois_group (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] {X : Type} [NormedAddCommGroup X]
    (f : (Ω ≃ₐ[K] Ω) → X) (hf : Continuous f) (δ : ℝ) (hδ : 0 < δ) :
    ∃ E0 : Finset Ω, ∀ s s' : Ω ≃ₐ[K] Ω, (∀ x ∈ E0, s' x = x) → ‖f (s * s') - f s‖ < δ := by
  classical
  have hδ2 : 0 < δ / 2 := half_pos hδ
  have key : ∀ s : Ω ≃ₐ[K] Ω, ∃ E : IntermediateField K Ω, FiniteDimensional K E ∧
      ∀ g ∈ E.fixingSubgroup, ‖f (s * g) - f s‖ < δ / 2 := by
    intro s
    have hc : Continuous fun g : Ω ≃ₐ[K] Ω => ‖f (s * g) - f s‖ :=
      ((hf.comp (continuous_const.mul continuous_id)).sub continuous_const).norm
    have hA : {g : Ω ≃ₐ[K] Ω | ‖f (s * g) - f s‖ < δ / 2} ∈ 𝓝 (1 : Ω ≃ₐ[K] Ω) :=
      IsOpen.mem_nhds (isOpen_lt hc continuous_const) (by simp [hδ2])
    obtain ⟨E, hE, hsub⟩ := (krullTopology_mem_nhds_one_iff K Ω _).1 hA
    exact ⟨E, hE, fun g hg => hsub hg⟩
  choose E hEf hE using key
  let U : (Ω ≃ₐ[K] Ω) → Set (Ω ≃ₐ[K] Ω) := fun i => {h | i⁻¹ * h ∈ (E i).fixingSubgroup}
  have hUo : ∀ i, IsOpen (U i) := by
    intro i
    haveI := hEf i
    exact (IntermediateField.fixingSubgroup_isOpen (E i)).preimage (continuous_const.mul continuous_id)
  have hUc : Set.univ ⊆ ⋃ i, U i := by
    intro h _
    refine Set.mem_iUnion.2 ⟨h, ?_⟩
    show h⁻¹ * h ∈ (E h).fixingSubgroup
    rw [inv_mul_cancel]
    exact one_mem _
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover U hUo hUc
  have hT : ∀ i, ∃ T : Finset Ω, ∀ g : Ω ≃ₐ[K] Ω, (∀ x ∈ T, g x = x) → g ∈ (E i).fixingSubgroup := by
    intro i
    haveI := hEf i
    exact mem_fixingSubgroup_of_fixes_finite_set K Ω (E i)
  choose T hT using hT
  refine ⟨S.biUnion T, fun s s' hs' => ?_⟩
  obtain ⟨i, hiS, hi⟩ := Set.mem_iUnion₂.1 (hS (Set.mem_univ s))
  have hi' : i⁻¹ * s ∈ (E i).fixingSubgroup := hi
  have hs'i : s' ∈ (E i).fixingSubgroup :=
    hT i s' (fun x hx => hs' x (Finset.mem_biUnion.2 ⟨i, hiS, hx⟩))
  have h1 := hE i _ (mul_mem hi' hs'i)
  have h2 := hE i _ hi'
  rw [← mul_assoc, mul_inv_cancel_left] at h1
  rw [mul_inv_cancel_left] at h2
  have h3 : f (s * s') - f s = (f (s * s') - f i) - (f s - f i) := by abel
  rw [h3]
  have := norm_sub_le (f (s * s') - f i) (f s - f i)
  linarith

theorem UpperTheory.V.Z.Kato.Joint.unif :
    UpperTheory.V.Z.Kato.Joint.Unif := by
  intro l _ Ω _ _ _ f hf δ hδ
  haveI : IsGalois ℚ Ω := inferInstance
  exact uniform_continuity_galois_group ℚ Ω f hf δ hδ
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.FrobUNormV
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open UpperTheory.V.Z.Kato.Joint

private theorem frobU_normV {p : ℕ} (hp : p.Prime) {v : Pl} (hv : ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) : normV v = p := by
  have hN : normV v = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  have hspan : Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 ℚ)}) = p := by
    rw [Ideal.absNorm_span_singleton]
    have h1 : ((p : ℕ) : 𝓞 ℚ) = algebraMap ℤ (𝓞 ℚ) (p : ℤ) := by simp
    rw [h1, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank, Module.finrank_self, pow_one]
    simp
  have hle : Ideal.span {((p : ℕ) : 𝓞 ℚ)} ≤ v.asIdeal := (Ideal.span_singleton_le_iff_mem _).2 hv
  have hd := Ideal.absNorm_dvd_absNorm_of_le hle
  rw [hspan] at hd
  rcases hp.eq_one_or_self_of_dvd _ hd with h1 | h1
  · exact absurd (Ideal.absNorm_eq_one_iff.1 h1) v.isPrime.ne_top
  · rw [hN, h1]

theorem UpperTheory.V.Z.Kato.Joint.frobU :
    UpperTheory.V.Z.Kato.Joint.FrobU := by
  intro l hl Ω _ _ _ e S A W hW
  refine ⟨?_, fun s hs => ?_, fun s => ?_⟩
  · obtain ⟨v, hA, hv⟩ := hW.atL
    obtain ⟨σ, hσ⟩ := exists_isFrob (F := ℚ) hA
    rw [frobU_normV hl.out hv] at hσ
    exact ⟨σ, mem_Dec.2 hσ.1, hσ⟩
  · obtain ⟨c, hc⟩ := hW.int
    have hm : mat W s * mat W s⁻¹ = 1 := by
      rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
    have h11 : mat W s 1 1 * mat W s⁻¹ 1 1 = 1 := by
      have h := congrFun (congrFun hm 1) 1
      rw [Matrix.mul_apply, Fin.sum_univ_two, hW.upper s hs, zero_mul, zero_add, Matrix.one_apply_eq] at h
      exact h
    have ha := GlobalTheory.Ord2.CupCob.norm_le_one_of_mem c (hc s 1 1)
    have hb := GlobalTheory.Ord2.CupCob.norm_le_one_of_mem c (hc s⁻¹ 1 1)
    have hn : ‖mat W s 1 1‖ * ‖mat W s⁻¹ 1 1‖ = 1 := by rw [← norm_mul, h11, norm_one]
    refine le_antisymm ha ?_
    calc (1 : ℝ) = ‖mat W s 1 1‖ * ‖mat W s⁻¹ 1 1‖ := hn.symm
      _ ≤ ‖mat W s 1 1‖ := mul_le_of_le_one_right (norm_nonneg _) hb
  · have h : eps l s = algebraMap ℚ_[l] (Qbar l) ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) := rfl
    rw [h, norm_algebraMap']
    exact PadicInt.norm_units _
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.CoefUb
open UpperTheory.V.Z.Kato.Joint

theorem UpperTheory.V.Z.Kato.Joint.coefUb :
    UpperTheory.V.Z.Kato.Joint.CoefUb := by
  intro l _ c c' F hF
  obtain ⟨d, h1, h2⟩ := (UpperTheory.V.HV.coefSup l).1 c c'
  obtain ⟨d', h3, h4⟩ := (UpperTheory.V.Th.Nm.inOf d).1 {x // x ∈ F} (fun x => x.1) (fun x => hF x.1 x.2)
  exact ⟨d', h1.trans h3, h2.trans h3, fun x hx => h4 ⟨x, hx⟩⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.NormLeOfPow
open UpperTheory.V.Z.Kato.Joint

private theorem norm_le_of_pow {l : ℕ} [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) (z : ℂ) (n : ℕ) (hn : n ≠ 0)
    (h : z ^ n = 1) : ‖ι.symm z‖ ≤ 1 := by
  have h1 : ‖ι.symm z‖ ^ n = 1 := by rw [← norm_pow, ← map_pow, h, map_one, norm_one]
  exact ((pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).mp h1).le

private theorem hat_std {N : ℕ} [NeZero N] (φ : ZMod N → ℂ) (d : ℤ) :
    GlobalTheory.EisM.hat φ d = ∑ y : ZMod N, φ y * ZMod.stdAddChar (y * (d : ZMod N)) := by
  unfold GlobalTheory.EisM.hat
  refine Finset.sum_nbij' (fun i => (i : ZMod N)) (fun y => y.val) (fun _ _ => Finset.mem_univ _)
    (fun y _ => Finset.mem_range.mpr (ZMod.val_lt y)) (fun i hi => ZMod.val_cast_of_lt (Finset.mem_range.mp hi))
    (fun y _ => ZMod.natCast_zmod_val y) (fun i _ => ?_)
  have h : ((i : ZMod N)) * (d : ZMod N) = (((i : ℤ) * d : ℤ) : ZMod N) := by push_cast; rfl
  rw [h, ZMod.stdAddChar_coe]
  push_cast
  rfl

private theorem norm_two' {l : ℕ} [hl : Fact l.Prime] (h : l ≠ 2) : ‖(2 : PadicAlgCl l)‖ = 1 := by
  have h1 : (2 : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) ((2 : ℕ) : ℚ_[l]) := by
    rw [map_natCast]; rfl
  rw [h1, norm_algebraMap']
  exact Padic.norm_natCast_eq_one_iff.mpr ((Nat.coprime_primes hl.out Nat.prime_two).mpr h)

theorem UpperTheory.V.Z.Kato.Joint.hatW :
    UpperTheory.V.Z.Kato.Joint.HatW := by
  intro l _ ι N _ θ hl
  refine ⟨?_, fun d => ?_, fun d => ?_⟩
  · by_contra hc
    push Not at hc
    have h0 : ZMod.dft (fun y : ZMod N => θ y) = 0 := by
      funext k
      have := hc (-k)
      rw [hat_std] at this
      rw [ZMod.dft_apply, Pi.zero_apply, ← this]
      refine Finset.sum_congr rfl fun y _ => ?_
      simp [mul_comm]
    have h1 := congrFun ((LinearEquiv.map_eq_zero_iff _).mp h0) 1
    simp at h1
  · have h2 : ι.symm 2 = 2 := map_ofNat _ 2
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_div₀, norm_div, h2, norm_two' hl, div_one, hat_std, map_sum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun y _ => ?_
    rw [map_mul, norm_mul]
    refine mul_le_one₀ ?_ (norm_nonneg _) ?_
    · by_cases hy : IsUnit y
      · obtain ⟨u, rfl⟩ := hy
        refine norm_le_of_pow ι _ (Fintype.card (ZMod N)ˣ) Fintype.card_ne_zero ?_
        rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one]
      · rw [MulChar.map_nonunit _ hy]; simp
    · refine norm_le_of_pow ι _ N (NeZero.ne N) ?_
      rw [← AddChar.map_nsmul_eq_pow]
      simp
  · rw [hat_std, hat_std]
    simp
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.LawMono
open UpperTheory.V.Z.Kato.Joint
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ

private theorem norm_l_lt_one (l : ℕ) [Fact l.Prime] : ‖((l : ℕ) : Qbar l)‖ < 1 := by
  have h : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (PadicAlgCl l) ((l : ℕ) : ℚ_[l]) := by simp
  rw [h, PadicAlgCl.norm_extends]
  exact Padic.norm_p_lt_one

private theorem cg_scale {l : ℕ} [Fact l.Prime] (K : Qbar l) : ∃ N : ℕ, ∀ m, N ≤ m → ∀ (c₀ : ℕ) (u x y : Qbar l),
    ‖u‖ = 1 → Cg (2 * m) x y → Cg (m - c₀) (u * K * y) (u * K * x) := by
  have hl0 : 0 ≤ ‖((l : ℕ) : Qbar l)‖ := norm_nonneg _
  have hl1 := norm_l_lt_one l
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ‖((l : ℕ) : Qbar l)‖ ^ N * ‖K‖ ≤ 1 := by
    rcases eq_or_ne ‖K‖ 0 with hK | hK
    · exact ⟨0, by rw [hK, mul_zero]; exact zero_le_one⟩
    · obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (inv_pos.2 (lt_of_le_of_ne (norm_nonneg K) (Ne.symm hK))) hl1
      refine ⟨N, ?_⟩
      have hKpos : 0 < ‖K‖ := lt_of_le_of_ne (norm_nonneg K) (Ne.symm hK)
      calc ‖((l : ℕ) : Qbar l)‖ ^ N * ‖K‖ ≤ ‖K‖⁻¹ * ‖K‖ :=
            mul_le_mul_of_nonneg_right hN.le hKpos.le
        _ = 1 := inv_mul_cancel₀ hK
  refine ⟨N, fun m hm c₀ u x y hu hxy => ?_⟩
  unfold Cg at hxy ⊢
  rw [norm_pow] at hxy ⊢
  have hdiff : u * K * y - u * K * x = -(u * K * (x - y)) := by ring
  rw [hdiff, norm_neg, norm_mul, norm_mul, hu, one_mul]
  have hmN : ‖((l : ℕ) : Qbar l)‖ ^ m ≤ ‖((l : ℕ) : Qbar l)‖ ^ N := pow_le_pow_of_le_one hl0 hl1.le hm
  have hmc : ‖((l : ℕ) : Qbar l)‖ ^ m ≤ ‖((l : ℕ) : Qbar l)‖ ^ (m - c₀) :=
    pow_le_pow_of_le_one hl0 hl1.le (Nat.sub_le m c₀)
  have hKm : ‖((l : ℕ) : Qbar l)‖ ^ m * ‖K‖ ≤ 1 :=
    le_trans (mul_le_mul_of_nonneg_right hmN (norm_nonneg K)) hN
  calc ‖K‖ * ‖x - y‖ ≤ ‖K‖ * ‖((l : ℕ) : Qbar l)‖ ^ (2 * m) :=
        mul_le_mul_of_nonneg_left hxy (norm_nonneg K)
    _ = (‖((l : ℕ) : Qbar l)‖ ^ m * ‖K‖) * ‖((l : ℕ) : Qbar l)‖ ^ m := by ring
    _ ≤ 1 * ‖((l : ℕ) : Qbar l)‖ ^ m :=
        mul_le_mul_of_nonneg_right hKm (pow_nonneg hl0 m)
    _ ≤ ‖((l : ℕ) : Qbar l)‖ ^ (m - c₀) := by rw [one_mul]; exact hmc

private theorem law_mono {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {c : Coef l}
    {Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l} {j : Ω →+* Qbar l} {m₀ m₁ c₀ : ℕ}
    {R : ∀ m : ℕ, DirichletCharacter (Qbar l) (l ^ m) → Qbar l → Qbar l} (hm : m₀ ≤ m₁) (h : HTLawCsOfCoef A c Z j m₀ c₀ R) :
    HTLawCsOfCoef A c Z j m₁ c₀ R := by
  obtain ⟨ζ, hζ, hlaw⟩ := h
  exact ⟨ζ, hζ, fun m hm' => hlaw m (hm.trans hm')⟩

open Classical in
private theorem cg_cases {l : ℕ} [Fact l.Prime] {κ₀ κ : Qbar l} (hκ : κ ≠ 0) : ∃ N : ℕ, ∀ m, N ≤ m →
    ∀ (c₀ : ℕ) (v a p s X b g w : Qbar l), ‖v‖ = 1 → ‖a‖ = 1 → p ^ 2 = 1 → s ^ 2 = 1 →
    (p = s → Cg (2 * m) X (κ * b * g * w)) → (p = -s → Cg (2 * m) X 0) →
    Cg (m - c₀) (if p = s then v * κ₀ * a ^ m * (b * g * w) else 0) (v * (κ₀ / κ) * a ^ m * X) := by
  obtain ⟨N, hN⟩ := cg_scale (κ₀ / κ)
  refine ⟨N, fun m hm c₀ v a p s X b g w hv ha hp hs h1 h2 => ?_⟩
  have hu : ‖v * a ^ m‖ = 1 := by rw [norm_mul, norm_pow, hv, ha, one_pow, one_mul]
  by_cases hE : p = s
  · rw [if_pos hE]
    have h3 := hN m hm c₀ (v * a ^ m) X (κ * b * g * w) hu (h1 hE)
    have e1 : v * a ^ m * (κ₀ / κ) * (κ * b * g * w) = v * κ₀ * a ^ m * (b * g * w) := by
      field_simp
    have e2 : v * a ^ m * (κ₀ / κ) * X = v * (κ₀ / κ) * a ^ m * X := by ring
    rw [e1, e2] at h3
    exact h3
  · have hps : p ^ 2 = s ^ 2 := by rw [hp, hs]
    have hO : p = -s := (sq_eq_sq_iff_eq_or_eq_neg.1 hps).resolve_left hE
    rw [if_neg hE]
    have h3 := hN m hm c₀ (v * a ^ m) X 0 hu (h2 hO)
    have e2 : v * a ^ m * (κ₀ / κ) * X = v * (κ₀ / κ) * a ^ m * X := by ring
    rw [mul_zero, e2] at h3
    exact h3

theorem UpperTheory.V.Z.Kato.Joint.pinOf :
    UpperTheory.V.Z.Kato.Joint.PinOf := by
  intro hM hU hMo l _ Ω _ _ ι e A W c ν Z j u w ψ α B cc v n β t hl he hα hj hν hσ hμ hv ht hne hE
  obtain ⟨cO, L, κ, φ, n₀, r₁, hκ, hL, hφ, h1, h2, h3⟩ :=
    hM l ι e _ u w ψ α B cc v n β t hl he rfl hμ hv ht hne
  obtain ⟨c', hc, hcO, -⟩ := hU l c cO ∅ (fun x hx => absurd hx (Finset.notMem_empty x))
  obtain ⟨κ₀, vv, m₀, c₀, hκ₀, hvv, hH⟩ := hE
  obtain ⟨σ, hσ1, hσ2, hσ3⟩ := hσ
  obtain ⟨N, hN⟩ := cg_cases (κ₀ := κ₀) hκ
  have hH' := law_mono (le_max_left m₀ (max N 1)) ((hMo l Ω c c' hc).2.2 A Z j m₀ c₀ _ hH)
  refine ⟨c', hc, ?_⟩
  unfold Pin7
  refine ⟨ν σ, ι.symm α, κ₀ / κ, vv, j, _, L, φ, max m₀ (max N 1), c₀, n₀, hν, ⟨σ, hσ1, hσ2, rfl⟩, hσ3, hα, hvv,
    div_ne_zero hκ₀ hκ, hj, fun k => hcO (hL k), hH', ?_, ?_, r₁, h3⟩
  · intro m hm ψ' _ z hz
    have hm1 : 1 ≤ m := by omega
    have hmN : N ≤ m := by omega
    have ha : ψ' (-1) ^ 2 = 1 := by rw [← map_pow, neg_one_sq, map_one]
    have hb : (ι.symm ((-1) ^ e * ψ (-1))) ^ 2 = 1 := by
      rw [← map_pow, mul_pow, ← map_pow, ← pow_mul, mul_comm e 2, pow_mul, neg_one_sq, neg_one_sq, one_pow, map_one,
        one_mul, map_one]
    exact hN m hmN c₀ _ _ _ _ _ _ _ _ (hvv m).1 hα ha hb (fun hs => h1 m hm1 ψ' hs z hz) (fun hs => h2 m hm1 ψ' hs z hz)
  · intro r _ x
    apply ι.injective
    rw [map_inv₀, hφ, MulChar.inv_apply_eq_inv', inv_inv]
    exact ι.apply_symm_apply _
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.DetIne
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ
open UpperTheory.V.Z.Kato.Joint Polynomial

section

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

private theorem cont_of_apply [IsAlgClosure ℚ Ω] {Y : Type} [TopologicalSpace Y] (ζ : Ω) (f : G ℚ Ω → Y)
    (h : ∀ s t : G ℚ Ω, s ζ = t ζ → f s = f t) : Continuous f := by
  have hint : IsIntegral ℚ ζ :=
    ((IsAlgClosure.isAlgebraic (R := ℚ) (K := Ω)).isAlgebraic ζ).isIntegral
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {ζ}) :=
    IntermediateField.adjoin.finiteDimensional hint
  have hH : IsOpen (((IntermediateField.adjoin ℚ {ζ}).fixingSubgroup : Subgroup (Ω ≃ₐ[ℚ] Ω)) :
      Set (Ω ≃ₐ[ℚ] Ω)) := IntermediateField.fixingSubgroup_isOpen _
  refine continuous_iff_continuousAt.2 fun t => ?_
  have hU : IsOpen ((fun s : Ω ≃ₐ[ℚ] Ω => t⁻¹ * s) ⁻¹'
      (((IntermediateField.adjoin ℚ {ζ}).fixingSubgroup : Subgroup (Ω ≃ₐ[ℚ] Ω)) :
        Set (Ω ≃ₐ[ℚ] Ω))) := hH.preimage (continuous_const_mul _)
  have ht : t ∈ (fun s : Ω ≃ₐ[ℚ] Ω => t⁻¹ * s) ⁻¹'
      (((IntermediateField.adjoin ℚ {ζ}).fixingSubgroup : Subgroup (Ω ≃ₐ[ℚ] Ω)) :
        Set (Ω ≃ₐ[ℚ] Ω)) := by
    simp only [Set.mem_preimage, inv_mul_cancel, SetLike.mem_coe]
    exact Subgroup.one_mem _
  refine (continuousAt_const (y := f t)).congr ?_
  filter_upwards [hU.mem_nhds ht] with s hs
  have h1 : (t⁻¹ * s) ζ = ζ :=
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 hs ζ
      (IntermediateField.mem_adjoin_simple_self ℚ ζ)
  have h2 : s ζ = t ζ := by
    have h3 := congrArg t h1
    rw [AlgEquiv.mul_apply] at h3
    simpa using h3
  exact (h s t h2).symm

private theorem root_pow {M n : ℕ} (hM : M ≠ 0) {B : ValuationSubring Ω} {v : Pl} (hB : IsPlaceOver B v)
    (hv : ((M : ℕ) : 𝓞 ℚ) ∉ v.asIdeal) {s : G ℚ Ω} {ζ : Ω} (hζ : ζ ^ M = 1)
    (hs : ∀ x, B.valuation x ≤ 1 → B.valuation (s x - x ^ n) < 1) : s ζ = ζ ^ n := by
  have hN : ¬ B.valuation (M : Ω) < 1 := fun h => hv ((hB _).1 (by simpa using h))
  refine eq_of_pow_eq_one B hN ?_ ?_ (hs ζ (valuation_eq_one_of_pow_eq_one B hM hζ).le)
  · rw [← map_pow, hζ, map_one]
  · rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]

private theorem expo_eq {M a b : ℕ} [NeZero M] {ζ : Ω} (hζ : IsPrimitiveRoot ζ M) (h : ζ ^ a = ζ ^ b) :
    (a : ZMod M) = b := by
  have hu := hζ.isUnit (NeZero.ne M)
  have h1 : IsPrimitiveRoot hu.unit M := IsPrimitiveRoot.coe_units_iff.mp (by simpa using hζ)
  have h2 : hu.unit ^ a = hu.unit ^ b := Units.ext (by simpa using h)
  rw [pow_eq_pow_iff_modEq, ← h1.eq_orderOf] at h2
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr h2

private theorem det_of_charpoly {K : Type} [Field K] (ι : K ≃+* ℂ) {A : Matrix (Fin 2) (Fin 2) K} {a d : ℂ}
    (h : A.charpoly.map ι.toRingHom = X ^ 2 - C a * X + C d) : ι A.det = d := by
  have h0 := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p 0) h
  simp [Polynomial.coeff_map] at h0
  rw [Matrix.det_eq_sign_charpoly_coeff]
  simp [h0]

end

theorem UpperTheory.V.Z.Kato.Joint.detIne :
    UpperTheory.V.Z.Kato.Joint.DetIne := by
  intro l _ Ω _ _ _ ι e S A W g χ hN hK hl hAtt s hs
  have hM : g.M ≠ 0 := g.pos.ne'
  haveI : NeZero g.M := ⟨hM⟩
  have hl0 : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : NeZero ((g.M : ℕ) : Ω) := ⟨Nat.cast_ne_zero.2 hM⟩
  haveI : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.2 hl0⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω g.M
  obtain ⟨η, hη⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω l
  let F : Ω → Qbar l := fun x =>
    ι.symm (g.χ ((Classical.epsilon (fun k : ℕ => ζ ^ k = x) : ℕ) : ZMod g.M))
  have hF : ∀ k : ℕ, F (ζ ^ k) = ι.symm (g.χ k) := by
    intro k
    have h1 : ζ ^ (Classical.epsilon (fun j : ℕ => ζ ^ j = ζ ^ k)) = ζ ^ k :=
      Classical.epsilon_spec (p := fun j : ℕ => ζ ^ j = ζ ^ k) ⟨k, rfl⟩
    show ι.symm (g.χ _) = _
    rw [expo_eq hζ h1]
  let f : G ℚ Ω → Qbar l := fun t => ((dt W t * (χ t)⁻¹ ^ 2 : (Qbar l)ˣ) : Qbar l)
  have hf'c : Continuous (fun t : G ℚ Ω => F (t ζ)) :=
    cont_of_apply ζ _ (fun a b h => by simp only [h])
  have hcop : ∀ w : Pl, ((l : ℕ) : 𝓞 ℚ) ∈ w.asIdeal → ((g.M : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := by
    intro w hlw hmem
    obtain ⟨a, b, hab⟩ : IsCoprime (l : ℤ) (g.M : ℤ) :=
      Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hl)
    apply w.isPrime.ne_top
    rw [Ideal.eq_top_iff_one]
    have h2 : (a : 𝓞 ℚ) * (l : 𝓞 ℚ) + (b : 𝓞 ℚ) * (g.M : 𝓞 ℚ) = 1 := by
      exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 ℚ) hab
    rw [← h2]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hlw) (Ideal.mul_mem_left _ _ hmem)
  have key : f = fun t => F (t ζ) := by
    have hχc : Continuous (fun t : G ℚ Ω => (((χ t)⁻¹ ^ 2 : (Qbar l)ˣ) : Qbar l)) := by
      refine cont_of_apply η _ (fun a b hab => ?_)
      have h0 : χ (b⁻¹ * a) = 1 := hK (b⁻¹ * a) (fun x hx => by
        obtain ⟨i, -, rfl⟩ := hη.eq_pow_of_pow_eq_one hx
        rw [map_pow]
        simp [AlgEquiv.mul_apply, hab])
      rw [map_mul, map_inv, inv_mul_eq_one] at h0
      rw [h0]
    have hdt : ∀ t, ((W t : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)).det =
        ((dt W t : (Qbar l)ˣ) : Qbar l) := fun t => rfl
    have hdc : Continuous (fun t : G ℚ Ω => ((dt W t : (Qbar l)ˣ) : Qbar l)) := by
      simp only [← hdt]
      exact (Units.continuous_val.comp hN.cont).matrix_det
    have hfc : Continuous f := by
      have h3 : f = fun t => ((dt W t : (Qbar l)ˣ) : Qbar l) *
          (((χ t)⁻¹ ^ 2 : (Qbar l)ˣ) : Qbar l) := by
        funext t
        simp only [f, Units.val_mul]
      rw [h3]
      exact hdc.mul hχc
    have hbad := Filter.eventually_cofinite.1 hAtt.2
    have hI : Ideal.span {((g.M * l : ℕ) : 𝓞 ℚ)} ≠ 0 := by
      rw [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]
      exact Nat.cast_ne_zero.2 (mul_ne_zero hM hl0)
    refine GlobalTheory.Published.ChebotarevDegreeOne.eq_of_frob GlobalTheory.Published.chebotarevDegreeOne'
      (hbad.union (Ideal.finite_factors hI)) hfc hf'c ?_
    intro w hw _ B hB σ hσ
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hw
    obtain ⟨hP, hdiv⟩ := hw
    have hlw : ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := by
      intro h4
      apply hdiv
      rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem, Nat.cast_mul]
      exact Ideal.mul_mem_left _ _ h4
    have hMw : ((g.M : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := by
      intro h4
      apply hdiv
      rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem, Nat.cast_mul]
      exact Ideal.mul_mem_right _ _ h4
    have hσζ : σ ζ = ζ ^ normV w := root_pow hM hB hMw hζ.pow_eq_one hσ.2
    show f σ = F (σ ζ)
    rw [hσζ, hF]
    have hch := (hP B hB).2 σ hσ
    rw [Newform.heckePoly] at hch
    have hdet := det_of_charpoly ι hch
    have hcyc : ((cycBar ℚ Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV w : Qbar l) := by
      have h5 := cycZ_of_isFrob hlw hB hσ
      simp [cycBar, h5]
    rw [tw_val, Matrix.det_smul, Fintype.card_fin, hdt] at hdet
    simp [map_inv, hcyc] at hdet
    have hd0 : ι ((dt W σ : (Qbar l)ˣ) : Qbar l) ≠ 0 := (map_ne_zero ι).2 (Units.ne_zero _)
    have hx0 : ι ((χ σ : (Qbar l)ˣ) : Qbar l) ≠ 0 := (map_ne_zero ι).2 (Units.ne_zero _)
    have hn0 : (normV w : ℂ) ≠ 0 := by
      have h6 : (normV w : Qbar l) ≠ 0 := hcyc ▸ Units.ne_zero _
      exact_mod_cast (Nat.cast_ne_zero.1 h6)
    apply ι.injective
    rw [RingEquiv.apply_symm_apply]
    simp only [f]
    simp [map_inv]
    apply mul_right_cancel₀ (pow_ne_zero (2 * e) hn0)
    rw [← hdet]
    field_simp
    ring
  obtain ⟨v, hv, hlv⟩ := hN.atL
  have hs' : s ∈ Inertia A := hs
  have hsζ : s ζ = ζ ^ 1 :=
    root_pow hM hv (hcop v hlv) hζ.pow_eq_one (fun x hx => by simpa using hs'.2 x hx)
  have h1 := congrFun key s
  simp only [f, hsζ, hF, Nat.cast_one, map_one, Units.val_eq_one] at h1
  rw [inv_pow, mul_inv_eq_one] at h1
  exact h1
end

namespace UpperTheory.V.Z.Kato.Joint

theorem kato_global_admissibility_of_admissible (hA : AdmTop) : AdmFR := by
  have hK : NewformPartOfTowerModule := fun {Ω} _ _ _ ε X => GlobalTheory.T.heckeProjector_newform_galoisImage ε X
  have hR : AdmRho := GlobalTheory.T.untwisted_representation_ordinary_triangular_shape
  exact admissibleFunctional_of_projection hA hK hR jEx rhoFrob unif LocFacts₂ finP coefUb thLin thOp chiStab thP lamEig2 chiQuad aqBd

end UpperTheory.V.Z.Kato.Joint
