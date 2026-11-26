module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SphericalDecomposition.SphOfWitAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TCentChar

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UnramifiedAlgebraicWeights
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
namespace GlobalTheory.NewLevel
open UpperTheory.V.Af.Nf CongruenceSubgroup GlobalTheory.CuspRep Neutral.B1 _root_.Formalism.L2.Host
private theorem level_zero_eq_maximal_compact (w : HeightOneSpectrum (𝓞 ℚ)) : UpperTheory.V.Sd.K1 w 0 = GlobalTheory.LFun.KGL w (n := 2) := by
  ext g
  refine ⟨fun ⟨k, _, e⟩ => ⟨k, e⟩, fun ⟨k, e⟩ => ⟨k, ?_, e⟩⟩
  haveI : Subsingleton (w.adicCompletionIntegers ℚ ⧸ IsLocalRing.maximalIdeal (w.adicCompletionIntegers ℚ) ^ 0) :=
    Ideal.Quotient.subsingleton_iff.2 (by simp)
  exact Subsingleton.elim _ _
private theorem locGL_comm' {v w : HeightOneSpectrum (𝓞 ℚ)} (h : v ≠ w) (g : GL (Fin 2) (v.adicCompletion ℚ))
    (k : GL (Fin 2) (w.adicCompletion ℚ)) : locGL ℚ 2 v g * locGL ℚ 2 w k = locGL ℚ 2 w k * locGL ℚ 2 v g := by
  refine UpperTheory.V.Af.GlobalFixedVectors.gl_ext fun x => ?_
  rw [map_mul, map_mul]
  by_cases hx : x = v
  · subst hx; rw [pLoc_locGL_of_ne h, mul_one, one_mul]
  · rw [pLoc_locGL_of_ne hx, mul_one, one_mul]
private theorem normV_surj' {p : ℕ} (hp : p.Prime) : ∃ w : HeightOneSpectrum (𝓞 ℚ), normV w = p := by
  have h0 : Prime ((p : ℕ) : 𝓞 ℚ) := by
    have h : Prime ((p : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp hp
    have e : ((p : ℕ) : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm ((p : ℕ) : ℤ) := by simp
    rw [e]
    exact (MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm.toMulEquiv).mpr h
  let w : HeightOneSpectrum (𝓞 ℚ) := ⟨Ideal.span {((p : ℕ) : 𝓞 ℚ)}, (Ideal.span_singleton_prime h0.ne_zero).mpr h0,
    by rw [Ne, Ideal.span_singleton_eq_bot]; exact h0.ne_zero⟩
  refine ⟨w, (places w).2.2.1.symm.trans ?_⟩
  change Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 ℚ)}) = p
  rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank]
  simp
private noncomputable abbrev Eo (v : InfinitePlace ℚ) (i j : Fin 2) : Module.End ℂ (TR.Sm ℚ 2) := TR.Eop v i j
private noncomputable def LowS (k : ℕ) : Submodule ℂ (TR.Sm ℚ 2) :=
  (⨅ v : InfinitePlace ℚ, LinearMap.ker (Eo v 0 1 - Eo v 1 0 - (Complex.I * (k : ℂ)) • (1 : Module.End ℂ (TR.Sm ℚ 2)))) ⊓
  (⨅ v : InfinitePlace ℚ, LinearMap.ker (Eo v 0 0 - Eo v 1 1 - Complex.I • (Eo v 0 1 + Eo v 1 0))) ⊓
  (⨅ v : InfinitePlace ℚ, LinearMap.ker (Eo v 0 0 + Eo v 1 1))
private theorem mem_LowS {k : ℕ} {φ : TR.Sm ℚ 2} : φ ∈ LowS k ↔ ((∀ v, TR.Eop v 0 1 φ - TR.Eop v 1 0 φ = (Complex.I * (k : ℂ)) • φ) ∧
      (∀ v, TR.Eop v 0 0 φ - TR.Eop v 1 1 φ = Complex.I • (TR.Eop v 0 1 φ + TR.Eop v 1 0 φ)) ∧
      (∀ v, TR.Eop v 0 0 φ + TR.Eop v 1 1 φ = 0)) := by
  simp only [LowS, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.add_apply, Module.End.one_apply, sub_eq_zero, and_assoc]
private theorem lowS_fin {k : ℕ} {φ : TR.Sm ℚ 2} (h : φ ∈ LowS k) (u : GL (Fin 2) (Af ℚ)) : TR.finRep ℚ 2 u φ ∈ LowS k := by
  obtain ⟨h1, h2, h3⟩ := mem_LowS.1 h
  have e : ∀ v i j, TR.Eop v i j (TR.finRep ℚ 2 u φ) = TR.finRep ℚ 2 u (TR.Eop v i j φ) := fun v i j =>
    LinearMap.congr_fun (TR.lie_rt_fin _ u) φ
  refine mem_LowS.2 ⟨fun v => ?_, fun v => ?_, fun v => ?_⟩
  · rw [e, e, ← map_sub, h1, map_smul]
  · rw [e, e, e, e, ← map_sub, h2, map_smul, map_add (f := _)]
  · rw [e, e, ← map_add (f := _), h3, map_zero]
theorem not_dvd_level_of_satake_hecke_poly_cofinite : _root_.UpperTheory.V.Af.Hypotheses' → Published.CuspSemisimpleReal → ∀ (k : ℕ), 2 ≤ k → ∀ (g : Newform k) (j : ℤ) (π : TR.CuspSub ℚ 2),
    (∀ᶠ w : Pl in Filter.cofinite, ∃ Bs, π.HasSat w Bs ∧
      ((algSat 2 (normV w) Bs).map fun b => Polynomial.X - Polynomial.C ((normV w : ℂ) ^ j * b)).prod = g.heckePoly (normV w)) →
    ∀ (w : Pl) (Bs : Multiset ℂˣ), π.HasSat w Bs → ¬ normV w ∣ g.M := by
  intro P hS k hk g j π hπ w Bs hw hd
  have hM : 1 ≤ g.M := g.pos
  have hk1 : 1 ≤ k := by omega
  obtain ⟨π₀, ψ, hψ, hψ0, hlev, hlow, hsat⟩ := UpperTheory.V.Z.Kato.NewVec.newVec hS P.admR k hk g
  obtain ⟨B, hB⟩ := GlobalTheory.NewLevel.spherical_of_normTwist P.smoR k hk g j π π₀ hπ hsat w Bs hw
  let L : Submodule ℂ (TR.Sm ℚ 2) :=
    LowS k ⊓ ⨅ q, ⨅ (_ : q ≠ w), Hi.fixd (UpperTheory.V.Sd.locSm ℚ q) (UpperTheory.V.Sd.K1 q (lev g.M q))
  let U : Submodule ℂ π₀.V := L.comap π₀.V.subtype
  have hU : ∀ h, ∀ x ∈ U, π₀.locRep w h x ∈ U := by
    intro h x hx
    simp only [U, L, Submodule.mem_comap, Submodule.mem_inf, Submodule.mem_iInf, Submodule.subtype_apply] at hx ⊢
    refine ⟨lowS_fin hx.1 _, fun q hq u hu => ?_⟩
    have h1 : TR.finRep ℚ 2 (locGL ℚ 2 q u) x.1 = x.1 := hx.2 q hq u hu
    change TR.finRep ℚ 2 (locGL ℚ 2 q u) (TR.finRep ℚ 2 (locGL ℚ 2 w h) x.1) = TR.finRep ℚ 2 (locGL ℚ 2 w h) x.1
    rw [← Module.End.mul_apply, ← map_mul, locGL_comm' hq, map_mul, Module.End.mul_apply, h1]
  have hU0 : U ≠ ⊥ := by
    intro h
    have hm : (⟨ψ, hψ⟩ : π₀.V) ∈ U := by
      simp only [U, L, Submodule.mem_comap, Submodule.mem_inf, Submodule.mem_iInf, Submodule.subtype_apply]
      exact ⟨mem_LowS.2 hlow, fun q _ => hlev q⟩
    rw [h, Submodule.mem_bot] at hm
    exact hψ0 (congrArg Subtype.val hm)
  obtain ⟨σ, hσ⟩ := (_root_.UpperTheory.V.Af.local_comp_real_of_printed_results P ℚ 2 π₀ w).1
  have hiso := (_root_.UpperTheory.V.Af.local_comp_real_of_printed_results P ℚ 2 π₀ w).2 σ hσ
  have hσf : HasFixed σ.ρ (GlobalTheory.LFun.KGL w (n := 2)) := by
    refine hiso.hasFixed (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w 2).2 ?_
    obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 hB.1
    exact ⟨y, hy0, fun u hu => GlobalTheory.LGrp.mem_fixed.1 hy u hu⟩
  obtain ⟨x, hxU, hx0, hxf⟩ := UpperTheory.V.Af.GlobalFixedVectors.sub_fixed σ.ρ σ.irred (π₀.locRep w) hiso.2 U hU hU0 _ hσf
  simp only [U, L, Submodule.mem_comap, Submodule.mem_inf, Submodule.mem_iInf, Submodule.subtype_apply] at hxU
  obtain ⟨hxl, hxq⟩ := hxU
  obtain ⟨hwt, hlo, hone⟩ := mem_LowS.1 hxl
  have hx0' : (x : TR.Sm ℚ 2) ≠ 0 := fun e => hx0 (Subtype.ext e)
  have hp := (places w).1
  have hN : 1 ≤ g.M / normV w := Nat.div_pos (Nat.le_of_dvd hM hd) hp.pos
  have hNM : g.M / normV w ∣ g.M := Nat.div_dvd_of_dvd hd
  have hNne : g.M / normV w ≠ g.M := (Nat.div_lt_self hM hp.one_lt).ne
  have hcusp := π₀.cusp x.1 x.2
  have hfix : ∀ u ∈ K1G (g.M / normV w), TR.finRep ℚ 2 u x.1 = x.1 :=
    GlobalTheory.NewLevelInv.inv_K1G g.M w hM hd x.1 hcusp.1.level (fun q hq => hxq q hq) (by
      rw [level_zero_eq_maximal_compact]; exact fun u hu => congrArg Subtype.val (hxf u hu))
  obtain ⟨ω, hω, -⟩ := _root_.UpperTheory.V.Sd.Wc.centChar_alt P ℚ π₀
  have hc : ∀ (z : Ideles ℚ) (g' : GA ℚ 2),
      x.1.1 (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g') = ((ω.1 z : ℂˣ) : ℂ) * x.1.1 g' :=
    fun z g' => hω z x.1 x.2 g'
  obtain ⟨χ, hχ⟩ := UpperTheory.V.Br.charOf _ hN ω x.1 hx0' hone hfix hc
  obtain ⟨f, hf, hL⟩ := UpperTheory.V.Br.deadel k _ hN χ ω hχ x.1 hcusp ⟨hwt, hlo, hone⟩ hfix hc
  haveI : NeZero (g.M / normV w) := ⟨by omega⟩
  have hf0 : f ≠ 0 := by
    rintro rfl
    refine hx0' (Subtype.ext (funext fun g' => ?_))
    obtain ⟨γ, h, u, hu, rfl⟩ := decomp _ hN g'
    rw [hL γ h u hu]
    simp [nsl]
  have hhol : UpperTheory.V.Sd.IsHol k (lev (g.M / normV w)) ω x.1 :=
    ⟨hcusp.1, fun q u hu => hfix _ (kLocal _ hN q u hu), hc, hwt, hlo⟩
  refine hf0 (g.new _ hNM hNne f χ hf ?_)
  refine Filter.eventually_cofinite.2 ((Set.finite_le_nat g.M).subset fun q hq => ?_)
  simp only [Set.mem_setOf_eq] at hq
  have hqp : Nat.Prime q := by
    by_contra h
    exact hq (fun hp => False.elim (h hp))
  by_contra hqM
  have hqd : ¬ q ∣ g.M := fun h => hqM (Nat.le_of_dvd hM h)
  obtain ⟨wq, rfl⟩ := normV_surj' hqp
  obtain ⟨α, β, hq2, hsum, -⟩ := hsat wq hqd
  have hqN : ¬ normV wq ∣ g.M / normV w := fun h => hqd (h.trans hNM)
  have hv : GlobalTheory.LFun.IsSatVecGL wq (UpperTheory.V.Sd.locSm ℚ wq) x.1 {α, β} :=
    (hq2.2 x (GlobalTheory.LGrp.mem_fixed.2 fun u hu => Subtype.ext (hfix _ (kLocal _ hN wq u (by
      rwa [(places wq).2.2.2 _ hN hqN, level_zero_eq_maximal_compact])))) hx0).map π₀.V.subtype (fun _ _ => rfl) hx0'
  obtain ⟨h1, -⟩ := UpperTheory.V.Br.eigOf k _ hk1 hN χ ω hχ f x.1 hL hhol wq α β hqN hv
  rw [hsum] at h1
  exact hq (fun _ => h1)
end GlobalTheory.NewLevel
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ExistsRep
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
noncomputable section
open Polynomial Pointwise
namespace GlobalTheory.Ord2.SrcForm
open TwDet
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]
theorem exists_rep_alt (P : _root_.UpperTheory.V.Af.Hypotheses') [IsAlgClosure ℚ Ω] {k : ℕ} (hk : 2 ≤ k) (f : Newform k) (ι : Qbar l ≃+* ℂ) (W : R2 Ω l) (j : ℤ)
    (hf : f.Att ι (tw W (cycBar ℚ Ω l ^ j))) :
    ∃ π : TR.CuspSub ℚ 2, π.IsRegAlg ∧ AttR ι W π ∧ ∀ᶠ w : Pl in Filter.cofinite, ∃ Bs, π.HasSat w Bs ∧
      ((algSat 2 (normV w) Bs).map fun b => X - C ((normV w : ℂ) ^ (-j) * b)).prod = f.heckePoly (normV w) := by
  have hl : Fact l.Prime := inferInstance
  obtain ⟨π, hinf, hsat⟩ := P.newform k hk f (-j)
  refine ⟨π, fun v => ⟨_, hinf v, ?_, ?_⟩, ⟨ss_of_tw _ _ hf.1, ?_⟩, ?_⟩
  · simp only [Multiset.insert_eq_cons, Multiset.nodup_cons, Multiset.mem_singleton, Multiset.nodup_singleton, and_true]
    intro h
    have h1 : (k : ℂ) = 1 := by linear_combination h
    have h2 : k = 1 := by exact_mod_cast h1
    omega
  · intro z hz
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact ⟨-j, by push_cast; ring⟩
    · exact ⟨1 - k - j, by push_cast; ring⟩
  · filter_upwards [hf.2, ev_not_mem l hl.out.ne_zero, ev_not_mem f.M f.pos.ne'] with w hw hwl hwM
    obtain ⟨B, hB, hpoly⟩ := hsat w (not_dvd_of_not_mem hwM)
    refine ⟨B, hB, fun A hA => ⟨fun s hs => ?_, fun σ hσ => ?_⟩⟩
    · have h1 := (hw A hA).1 s hs
      have h2 : cycZ ℚ Ω l s = 1 := by
        refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
        rw [cycZ_toZModPow_eq (v := w) (σ := s) hwl hA (q := 1) (fun x hx => by simpa only [pow_one] using hs.2 x hx) n]
        simp
      have h3 : (cycBar ℚ Ω l ^ j) s = 1 := by
        rw [MonoidHom.zpow_apply, cycBar, MonoidHom.comp_apply, h2, map_one, one_zpow]
      apply Units.ext
      have h4 := congrArg Units.val h1
      rwa [tw_val, h3, Units.val_one, one_smul] at h4
    · have h1 := (hw A hA).2 σ hσ
      rw [tw_val, ← hpoly] at h1
      refine scale_charpoly ι.toRingHom _ _ (Units.ne_zero ((cycBar ℚ Ω l ^ j) σ⁻¹)) _ ?_
      rw [h1]
      have h2 : ((cycBar ℚ Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV w : ℕ) := by
        change algebraMap ℚ_[l] (Qbar l) (PadicInt.Coe.ringHom ((cycZ ℚ Ω l σ : ℤ_[l]ˣ) : ℤ_[l])) = _
        rw [cycZ_of_isFrob hwl hA hσ, map_natCast, map_natCast]
      have h3 : ι.toRingHom (((cycBar ℚ Ω l ^ j) σ⁻¹ : (Qbar l)ˣ) : Qbar l) = (normV w : ℂ) ^ (-j) := by
        rw [MonoidHom.zpow_apply, map_inv, Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val, h2, map_zpow₀,
          map_inv₀, map_natCast, inv_zpow']
      rw [h3]
  · filter_upwards [ev_not_mem f.M f.pos.ne'] with w hwM
    exact hsat w (not_dvd_of_not_mem hwM)
end GlobalTheory.Ord2.SrcForm
namespace GlobalTheory.Ord2
open TwDet SrcForm
end GlobalTheory.Ord2
end
end
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
open Polynomial Pointwise
namespace GlobalTheory.Ord2
open TwDet SrcForm
private theorem sources_of_spherical (P : _root_.UpperTheory.V.Af.HypothesesH') (hT : TwNewQ) (hF : UpperTheory.V.Z.Kato.WeilSphericalRecords.FrobRoot) (l : ℕ) [hl : Fact l.Prime] (Ω : Type) [Field Ω]
    [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (W : R2 Ω l) (hl2 : l ≠ 2) (he : 1 ≤ e) (h : admitted ι e W)
    (hS : UpperTheory.V.Z.Kato.SphAt ι e W) : GlobalTheory.Ord2.SrcL ι e W := by
  have hl0 : 0 < l := hl.out.pos
  obtain ⟨N, hN, hNk⟩ := UpperTheory.V.CF.kwAbs Ω (dt W).ker (ker_open h.cont h.det2)
    (Abelianization.commutator_subset_ker (dt W))
  have hθN : KillsMu N (dt W) := fun s hs => hNk s hs
  obtain ⟨A, χ, κ, hA, hχ, hfl, hine, hk⟩ := h.flag
  set φ : G ℚ Ω →* (Qbar l)ˣ := (dt W)⁻¹ * χ⁻¹ with hφdef
  have hNl : 0 < N * l := Nat.mul_pos hN hl0
  have hφ : KillsMu (N * l) φ :=
    killsMu_mul (killsMu_dvd (kills_inv hθN) (dvd_mul_right N l)) (killsMu_dvd (kills_inv hχ) (dvd_mul_left l N))
  obtain ⟨g, hg⟩ := hT l Ω ι e W hl2 he h (N * l) φ hNl hφ
  have hVc : Continuous (tw W φ) := tw_cont h.cont (cont_of_kills hNl hφ)
  have hVi : IsIrr (tw W φ) := irr_tw W φ _ h.irr
  have hVa : ∃ M : ℕ, 1 ≤ M ∧ LevelAway l M (tw W φ) := by
    obtain ⟨M, hM, hlev⟩ := h.away
    refine ⟨M * (N * l), Nat.mul_pos hM hNl, fun w hw => ?_⟩
    obtain ⟨B, hB, ψ, hψ, hd⟩ := hlev w hw
    exact ⟨B, hB, fun i => ψ i * φ, fun i => killsMu_mul (killsMu_dvd (hψ i) (dvd_mul_right _ _))
      (killsMu_dvd hφ (dvd_mul_left _ _)), diag_twist φ hd⟩
  have hVd : ∃ M : ℕ, 1 ≤ M ∧ KillsMu M (dt (tw W φ)) := by
    refine ⟨N * l, hNl, ?_⟩
    rw [dt_tw, pow_two]
    exact killsMu_mul (killsMu_mul hφ hφ) (killsMu_dvd hθN (dvd_mul_right N l))
  have hVf := flag_twist φ hfl
  have hVk : ∀ s : ↥(Dec (F := ℚ) A), (s : G ℚ Ω) ∈ Ine (F := ℚ) A →
      (κ 0 * φ.comp (Dec (F := ℚ) A).subtype) s = cycBar ℚ Ω l s ^ (e : ℤ) ∧
      (κ 1 * φ.comp (Dec (F := ℚ) A).subtype) s = cycBar ℚ Ω l s ^ (-(e : ℤ)) := by
    intro s hs
    have h1 : dt W (s : G ℚ Ω) = 1 := hine hs
    obtain ⟨h0, h1'⟩ := hk s hs
    simp only [hφdef, MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.inv_apply, Subgroup.coe_subtype, h1, inv_one,
      one_mul, h0, h1', mul_inv_cancel_right, and_self]
  obtain ⟨π, hreg, hatt, hsat⟩ := _root_.GlobalTheory.Ord2.SrcForm.exists_rep_alt P.toClassicalTheorems (by omega) g ι (tw W φ) (-(e : ℤ)) hg
  obtain ⟨v, hv, hlv⟩ := id hA
  have hnv : normV v = l := normV_of_mem hl.out hlv
  obtain ⟨Bs, hBs⟩ := hS (N * l) φ hNl hφ A v _ hv hlv hVf hVk π hreg hatt
  have hlev : ¬ l ∣ g.M := hnv ▸ _root_.GlobalTheory.NewLevel.not_dvd_level_of_satake_hecke_poly_cofinite P.toClassicalTheorems P.ssR _ (by omega) g _ π hsat v Bs hBs
  obtain ⟨σ, hσ⟩ := exists_isFrob (Ω := Ω) hv
  rw [hnv] at hσ
  obtain ⟨α, hroot, hα⟩ := hF l Ω ι e (tw W φ) A _ g hl2 he hVc hVi hVd hA ⟨hVf, hVk⟩ hg hlev ⟨σ, hσ.1⟩ hσ
  set u : (Qbar l)ˣ := (κ 0 * φ.comp (Dec (F := ℚ) A).subtype) ⟨σ, hσ.1⟩ * cycBar ℚ Ω l σ ^ (-(e : ℤ)) with hu
  have hun : ‖(u : Qbar l)‖ = 1 := by
    rw [hu, Units.val_mul, norm_mul, norm_flag hVc hVf 0, Units.val_zpow_eq_zpow_val, norm_zpow, norm_cyc, one_zpow, one_mul]
  have hα' : α = ι (u : Qbar l) ∨ α = (ι (u : Qbar l))⁻¹ := hα.imp id fun h => by rw [← h, inv_inv]
  have hαn : ‖ι.symm α‖ = 1 := by
    rcases hα' with h1 | h1
    · rw [h1, RingEquiv.symm_apply_apply, hun]
    · rw [h1, map_inv₀, RingEquiv.symm_apply_apply, norm_inv, hun, inv_one]
  obtain ⟨hal, hpow⟩ := GlobalTheory.T.newform_unit_root_not_root_of_unity_odd_weight l ι e g α hl2 he hlev hroot hαn
  refine ⟨⟨g, χ⁻¹, A, κ, hlev, hal, kills_inv hχ, ?_, hA, hfl, fun s hs => ?_⟩, fun A' κ' hA' hfl' => ?_⟩
  · rw [tw_tw] at hg
    rw [mul_assoc]
    exact hg
  · have h1 : dt W (s : G ℚ Ω) = 1 := hine hs
    have h2 : (cycBar ℚ Ω l (s : G ℚ Ω) : Qbar l) ≠ 0 := Units.ne_zero _
    have h3 : (χ (s : G ℚ Ω) : Qbar l) ≠ 0 := Units.ne_zero _
    have h4 : (cycBar ℚ Ω l (s : G ℚ Ω) : Qbar l) ^ (e : ℤ) ≠ 0 := zpow_ne_zero _ h2
    rw [(hk s hs).2, h1, MonoidHom.inv_apply, Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val,
      Units.val_one, inv_one, one_mul, zpow_neg]
    field_simp
  · by_contra hn
    push Not at hn
    obtain ⟨m, hm, hχm⟩ := pow_eq_one_of_kills hl0 hχ
    obtain ⟨t, ht, htk⟩ := cyc_inf hA
    obtain ⟨h0, h1⟩ := hk ⟨t, Ine_le_Dec A ht⟩ ht
    rcases eps_mem hA hA' hfl hfl' hn with hc | hc
    · rw [← hc] at h0
      simp only at h0
      have he1 : e = 1 := by
        by_contra hne
        obtain ⟨d, rfl⟩ : ∃ d, e = d + 1 := ⟨e - 1, by omega⟩
        refine htk (d * m) (Nat.mul_ne_zero (by omega) (by omega)) ?_
        have h2 : cycBar ℚ Ω l t ^ d * χ t = 1 := by
          rw [zpow_natCast, pow_succ', mul_assoc] at h0
          exact (left_eq_mul.1 h0)
        rw [pow_mul, eq_inv_of_mul_eq_one_left h2, inv_pow, hχm, inv_one]
      obtain ⟨m', hm', hφm⟩ := pow_eq_one_of_kills hNl hφ
      have hu' : u = φ σ := by
        rw [hu, MonoidHom.mul_apply, ← hc, he1]
        simp [mul_inv_cancel_comm]
      have hu1 : ι (u : Qbar l) ^ m' = 1 := by
        rw [← map_pow, ← Units.val_pow_eq_pow_val, hu', hφm, Units.val_one, map_one]
      refine hpow m' hm' ?_
      rcases hα' with h1 | h1
      · rw [h1, hu1]
      · rw [h1, inv_pow, hu1, inv_one]
    · rw [← hc] at h1
      simp only at h1
      refine htk ((e + 1) * m) (Nat.mul_ne_zero (by omega) (by omega)) ?_
      have h2 : cycBar ℚ Ω l t ^ (e + 1) = χ t := by
        rw [pow_succ]
        nth_rewrite 2 [h1]
        rw [zpow_neg, zpow_natCast, mul_inv_cancel_left]
      rw [pow_mul, h2, hχm]
end GlobalTheory.Ord2
end
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Z.Win UpperTheory.V.Z.Kato UpperTheory.V.Z.Kato.WeilSphericalRecords UpperTheory.Zero.LLC
theorem UpperTheory.V.Z.Kato.WeilSphericalRecords.srcS_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → GlobalTheory.Ord2.TwNewQ → FrobRoot → SrcS :=
  fun P hT hF l _ Ω _ _ _ ι e W hl he hW hS => GlobalTheory.Ord2.sources_of_spherical P hT hF l Ω ι e W hl he hW hS
end
