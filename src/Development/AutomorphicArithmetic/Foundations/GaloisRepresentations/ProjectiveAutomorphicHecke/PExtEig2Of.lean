module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CentralEig2

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PExtEig2Of
open Module

noncomputable section

namespace UpperTheory.Gal.CertificateRingHomMap

open GlobalTheory.LKDef.HeckeTraceForms

section

variable {Γ H A Z V J : Type} [Group Γ] [Group H] [Group A] [Group Z] [AddCommGroup V] [Module ℂ V]

private theorem rop_add (r : H →₀ ℂ) (Φ Ψ : H → V) : rop r (Φ + Ψ) = rop r Φ + rop r Ψ := by
  funext g
  simp only [rop, Pi.add_apply, smul_add, Finsupp.sum_add]

private theorem rop_smul (r : H →₀ ℂ) (a : ℂ) (Φ : H → V) : rop r (a • Φ) = a • rop r Φ := by
  funext g
  simp only [rop, Pi.smul_apply, Finsupp.smul_sum, smul_smul, mul_comm]

private def eigForms (ι : Γ →* H) (K : Subgroup H) (ξ : Representation ℂ Γ V) (r : J → H →₀ ℂ) (θ : J → ℂ) :
    Submodule ℂ (H → V) where
  carrier := {Φ | Φ ∈ forms ι K ξ ∧ ∀ j, rop (r j) Φ = θ j • Φ}
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨add_mem ha hb, fun j => by rw [rop_add, ha', hb', smul_add]⟩
  zero_mem' := ⟨zero_mem _, fun j => by
    have := rop_smul (r j) (0 : ℂ) (0 : H → V)
    simpa using this⟩
  smul_mem' := by
    rintro a b ⟨hb, hb'⟩
    exact ⟨Submodule.smul_mem _ a hb, fun j => by rw [rop_smul, hb', smul_comm]⟩

end

theorem pExtEig2_of : ExtZero → CentralEig2 → ExtEig2 := by
  intro hZ hC
  unfold ExtEig2
  intro Γ H A Z V _ _ _ _ _ _ ι K ξ c ζ hcen hs φ hφ hφne J r θ hsupp hforms heig
  obtain ⟨s, hs⟩ := hs
  obtain ⟨u₀, hu₀, hφu₀⟩ := hφne
  have memF : ∀ Ψ : H → V, Ψ ∈ forms ι K ξ ↔
      ((∀ γ g, Ψ (ι γ * g) = ξ γ (Ψ g)) ∧ ∀ k ∈ K, ∀ g, Ψ (g * k) = Ψ g) := fun Ψ => Iff.rfl
  obtain ⟨Φ, hΦ, hext, hsup⟩ := hZ Γ H A V ι K ξ c φ hφ
  obtain ⟨hΦ1, hΦ2⟩ := (memF Φ).1 hΦ
  have hΦne : Φ ≠ 0 := by
    intro h
    apply hφu₀
    rw [← hext u₀ hu₀, h]
    rfl
  have hΦeig : ∀ j, rop (r j) Φ = θ j • Φ := by
    intro j
    have hu : ∀ u, c u = 1 → rop (r j) Φ u = θ j • Φ u := by
      intro u hu
      rw [hext u hu, ← heig j u hu]
      simp only [rop, Finsupp.sum]
      apply Finset.sum_congr rfl
      intro v hv
      rw [hext (u * v) (by rw [map_mul, hu, hsupp j v hv, one_mul])]
    obtain ⟨hf1, hf2⟩ := (memF _).1 (hforms j Φ hΦ)
    funext g
    by_cases hg : ∃ γ u k, c u = 1 ∧ k ∈ K ∧ g = ι γ * u * k
    · obtain ⟨γ, u, k, hu', hk, rfl⟩ := hg
      rw [Pi.smul_apply, mul_assoc, hf1 γ (u * k), hf2 k hk u, hΦ1 γ (u * k), hΦ2 k hk u,
        hu u hu', map_smul]
    · have h0 : Φ g = 0 := by
        by_contra h
        exact hg (hsup g h)
      rw [Pi.smul_apply, h0, smul_zero]
      simp only [rop, Finsupp.sum]
      apply Finset.sum_eq_zero
      intro v hv
      have hcv := hsupp j v hv
      have hz : Φ (g * v) = 0 := by
        by_contra h
        obtain ⟨γ, u, k, hu', hk, he⟩ := hsup _ h
        apply hg
        refine ⟨γ, u * (k * v⁻¹ * k⁻¹), k, ?_, hk, ?_⟩
        · simp [map_mul, map_inv, hu', hcv]
        · calc g = g * v * v⁻¹ := by group
            _ = ι γ * u * k * v⁻¹ := by rw [he]
            _ = ι γ * (u * (k * v⁻¹ * k⁻¹)) * k := by group
      rw [hz, smul_zero]
  have trForms : ∀ Ψ ∈ forms ι K ξ, ∀ z, (fun g => Ψ (g * ζ z)) ∈ forms ι K ξ := by
    intro Ψ hΨ z
    obtain ⟨h1, h2⟩ := (memF Ψ).1 hΨ
    refine (memF _).2 ⟨fun γ g => ?_, fun k hk g => ?_⟩
    · show Ψ (ι γ * g * ζ z) = ξ γ (Ψ (g * ζ z))
      rw [mul_assoc, h1]
    · show Ψ (g * k * ζ z) = Ψ (g * ζ z)
      rw [mul_assoc, ← hcen z k, ← mul_assoc, h2 k hk]
  have trRop : ∀ (Ψ : H → V) j z,
      rop (r j) (fun g => Ψ (g * ζ z)) = fun g => rop (r j) Ψ (g * ζ z) := by
    intro Ψ j z
    funext g
    simp only [rop, Finsupp.sum]
    apply Finset.sum_congr rfl
    intro u _
    rw [mul_assoc g (ζ z), hcen z u, mul_assoc]
  have key : ∀ z, ∃ t ∈ s, ∃ a : ℂ, (fun g => Φ (g * ζ z)) = a • fun g => Φ (g * ζ t) := by
    intro z
    obtain ⟨t, ht, z₀, z₁, rfl, hz₀, γ, a, hz₁, ha⟩ := hs z
    refine ⟨t, ht, a, ?_⟩
    funext g
    show Φ (g * ζ (t * z₀ * z₁)) = a • Φ (g * ζ t)
    rw [map_mul, map_mul, ← mul_assoc, ← mul_assoc, ← hcen z₁, hz₁, hΦ1, ha, hΦ2 _ hz₀]
  let M : Submodule ℂ (H → V) := Submodule.span ℂ ((fun t g => Φ (g * ζ t)) '' (s : Set Z))
  have hfin : FiniteDimensional ℂ M :=
    FiniteDimensional.span_of_finite ℂ ((s.finite_toSet).image _)
  have trM : ∀ z, (fun g => Φ (g * ζ z)) ∈ M := by
    intro z
    obtain ⟨t, ht, a, he⟩ := key z
    rw [he]
    exact M.smul_mem a (Submodule.subset_span ⟨t, ht, rfl⟩)
  have hΦM : Φ ∈ M := by
    have h := trM 1
    simp only [map_one, mul_one] at h
    exact h
  have hle : M ≤ eigForms ι K ξ r θ := by
    apply Submodule.span_le.2
    rintro _ ⟨t, _, rfl⟩
    show (fun g => Φ (g * ζ t)) ∈ forms ι K ξ ∧
      ∀ j, rop (r j) (fun g => Φ (g * ζ t)) = θ j • (fun g => Φ (g * ζ t))
    refine ⟨trForms Φ hΦ t, fun j => ?_⟩
    rw [trRop, hΦeig j]
    rfl
  have hE : ∀ Ψ ∈ M, Ψ ∈ forms ι K ξ ∧ ∀ j, rop (r j) Ψ = θ j • Ψ := fun Ψ h => hle h
  have hne : M ≠ ⊥ := by
    intro h
    apply hΦne
    have h' := hΦM
    rw [h] at h'
    exact (Submodule.mem_bot ℂ).1 h'
  have hclos : ∀ Ψ ∈ M, ∀ z, (fun g => Ψ (g * ζ z)) ∈ M := by
    intro Ψ hΨ z
    have hL : M ≤ M.comap (LinearMap.funLeft ℂ V (fun g : H => g * ζ z)) := by
      apply Submodule.span_le.2
      rintro _ ⟨t, _, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap]
      have h := trM (z * t)
      simp only [map_mul, ← mul_assoc] at h
      exact h
    exact hL hΨ
  obtain ⟨Ψ, hΨM, hΨne, ψ, hψ⟩ :=
    hC Γ H Z V ι K ξ ζ hcen M hfin (fun Ψ h => (hE Ψ h).1) hne hclos
  exact ⟨Ψ, (hE Ψ hΨM).1, hΨne, (hE Ψ hΨM).2, ψ, hψ⟩

end UpperTheory.Gal.CertificateRingHomMap

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.MemLevUpdateOfErase
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LevEraseLe
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsGoodWithoutBad
theorem UpperTheory.exists_good_without_bad :
    ∀ {P : Type} [DecidableEq P] (Good : Finset P → Prop) (bad : P → Prop), (∀ (S : Finset P) (w : P), Good S → w ∈ S → bad w → Good (S.erase w)) → ∀ S : Finset P, Good S → ∃ T : Finset P, Good T ∧ ∀ w ∈ T, ¬ bad w := by
  intro P _ Good bad h S
  induction S using Finset.strongInduction with
  | H S ih =>
    intro hS
    by_cases hb : ∃ w ∈ S, bad w
    · obtain ⟨w, hw, hbw⟩ := hb
      exact ih (S.erase w) (Finset.erase_ssubset hw) (h S w hS hw hbw)
    · exact ⟨S, hS, fun w hw hbw => hb ⟨w, hw, hbw⟩⟩
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsOpenStabilizerLinearMap
theorem UpperTheory.isOpen_stabilizer_linear_map :
    ∀ {G V M : Type} [TopologicalSpace G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [AddCommGroup M] [Module ℂ M] (R : G → M →ₗ[ℂ] M) (f : V →ₗ[ℂ] M), (∀ v : V, IsOpen {g : G | R g (f v) = f v}) → IsOpen {g : G | R g ∘ₗ f = f} := by
  intro G V M _ _ _ _ _ _ R f h
  let b := Module.finBasis ℂ V
  have key : {g : G | R g ∘ₗ f = f} = ⋂ i, {g : G | R g (f (b i)) = f (b i)} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro hg i
      exact LinearMap.congr_fun hg (b i)
    · intro hg
      exact b.ext fun i => hg i
  rw [key]
  exact isOpen_iInter_of_finite fun i => h (b i)
end

namespace UpperTheory.Reformulated.B.Grk2

open UpperTheory.Gal.CertificateRingHomMap

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {n : ℕ}

private theorem mem_lev (S : Finset (Plc E)) (Kw : (w : Plc E) → Subgroup (GLw n w)) (k : GUf E n) :
    k ∈ lev S Kw ↔ (sim k ∈ ZU ∧ ∀ w ∈ S, comp w k ∈ Kw w) ∧
      ∀ w : Plc E, (w ∉ S ∧ cj w ∉ S) → comp w k ∈ GlobalTheory.LFun.KGL w (n := n) := by
  simp only [lev, Subgroup.mem_inf, Subgroup.mem_iInf, Subgroup.mem_comap]

private theorem isOpen_stab (π : GlobalTheory.DefU.AutSub E n) (W : GlobalTheory.DefU.Wt E n)
    (f : GlobalTheory.DefU.algForms W) (hf : f ∈ π.finPart W) :
    IsOpen {u : GlobalTheory.UnitaryBC.finU (E := E) (n := n) | GlobalTheory.DefU.algRep W u f = f} := by
  obtain ⟨V, hV⟩ := π
  have h1 := hV.1
  have hv : ∀ v : W.Sp, f.1 v ∈ V := fun v => by
    have := (Submodule.mem_iInf _).1 hf v
    exact this
  have key := UpperTheory.isOpen_stabilizer_linear_map (fun u : GlobalTheory.UnitaryBC.finU (E := E) (n := n) => GlobalTheory.UnitaryBC.RU E n u.1) f.1
    (fun v => by
      obtain ⟨-, -, h, -⟩ := h1 _ (hv v)
      exact h)
  convert key using 2 with u
  ext u
  exact Subtype.ext_iff

open Classical in
private theorem lev_erase_le (S : Finset (Plc E)) (Kw : (w : Plc E) → Subgroup (GLw n w)) (w : Plc E)
    (hc : cj w ∉ S) (k : GUf E n) (hk : k ∈ lev (S.erase w) Kw) :
    comp w k ∈ GlobalTheory.LFun.KGL w (n := n) ∧ k ∈ lev S (Function.update Kw w (GlobalTheory.LFun.KGL w (n := n))) := by
  rw [mem_lev] at hk
  obtain ⟨⟨h1, h2⟩, h3⟩ := hk
  have hw : comp w k ∈ GlobalTheory.LFun.KGL w (n := n) :=
    h3 w ⟨Finset.notMem_erase _ _, fun h => hc (Finset.mem_of_mem_erase h)⟩
  refine ⟨hw, (mem_lev _ _ _).2 ⟨⟨h1, fun v hv => ?_⟩, fun v hv => h3 v
    ⟨fun h => hv.1 (Finset.mem_of_mem_erase h), fun h => hv.2 (Finset.mem_of_mem_erase h)⟩⟩⟩
  by_cases e : v = w
  · subst e
    rw [Function.update_self]
    exact hw
  · rw [Function.update_of_ne e]
    exact h2 v (Finset.mem_erase.2 ⟨e, hv⟩)

end UpperTheory.Reformulated.B.Grk2

open UpperTheory.Gal.CertificateRingHomMap in
theorem UpperTheory.Reformulated.B.Grk2.pVecU_of :
    UpperTheory.Gal.CertificateRingHomMap.NbhdU → UpperTheory.Gal.CertificateRingHomMap.StepAt → UpperTheory.Gal.CertificateRingHomMap.SphType → UpperTheory.Gal.CertificateRingHomMap.LocComm → UpperTheory.Gal.CertificateRingHomMap.VecU := by
  classical
  intro hN hS hT hL E _ _ _ n π W hne Up hUp w₀ hw₀ hU₀ J χ hJo hJc hJ
  obtain ⟨f₀, hf₀, hf₀ne⟩ := (Submodule.ne_bot_iff _).1 hne
  let O : Subgroup (GlobalTheory.UnitaryBC.finU (E := E) (n := n)) :=
    { carrier := {u | GlobalTheory.DefU.algRep W u f₀ = f₀}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_mul, Module.End.mul_apply, hb, ha]
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  obtain ⟨S₀, Kw, hsh₀, hO⟩ := hN E n O (isOpen_stab π W f₀ hf₀) Up hUp w₀ hw₀ hU₀
  obtain ⟨S, ⟨hsh, f, hf, hfne, hfix⟩, hgood⟩ := UpperTheory.exists_good_without_bad
    (fun S : Finset (Plc E) => Shape Up w₀ S Kw ∧ ∃ f ∈ π.finPart W, f ≠ 0 ∧
      ∀ u : GlobalTheory.UnitaryBC.finU (E := E) (n := n), ofU u ∈ lev S Kw → GlobalTheory.DefU.algRep W u f = f)
    (fun w => GlobalTheory.UnitaryBC.IsSplitAt w ∧ w ≠ w₀ ∧ HasType π.V w (GlobalTheory.LFun.KGL w (n := n)) 1)
    (by
      rintro S w ⟨⟨s1, s2, s3, s4, s5⟩, f, hf, hfne, hfix⟩ hwS ⟨hw, hww, hty⟩
      have hc := (s5 w hwS hw).2
      obtain ⟨f', hf', hf'ne, hf'e⟩ := hS E n π W f hf hfne S Kw w hw hwS hc hfix _ 1
        (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).2 hty
      refine ⟨⟨Finset.mem_erase.2 ⟨hww.symm, s1⟩,
        fun v hv => s2 v (Finset.mem_of_mem_erase hv),
        fun v hv => s3 v (Finset.mem_of_mem_erase hv),
        fun v hv => s4 v (Finset.mem_of_mem_erase hv),
        fun v hv h => ⟨(s5 v (Finset.mem_of_mem_erase hv) h).1,
          fun h' => (s5 v (Finset.mem_of_mem_erase hv) h).2 (Finset.mem_of_mem_erase h')⟩⟩,
        f', hf', hf'ne, fun u hu => ?_⟩
      obtain ⟨a, b⟩ := lev_erase_le S Kw w hc _ hu
      simpa using hf'e u b a)
    S₀ ⟨hsh₀, f₀, hf₀, hf₀ne, hO⟩
  obtain ⟨s1, s2, s3, s4, s5⟩ := hsh
  obtain ⟨f', hf', hf'ne, hf'e⟩ :=
    hS E n π W f hf hfne S Kw w₀ hw₀ s1 (s5 w₀ s1 hw₀).2 hfix J χ hJc hJ
  refine ⟨S, Function.update Kw w₀ J, ⟨s1, fun v hv => ?_, fun v hv => ?_, fun v hv e => ?_, s5⟩,
    Function.update_self _ _ _, fun w hw hap hsat => ?_, f', hf', hf'ne, hf'e⟩
  · by_cases e : v = w₀
    · subst e
      rw [Function.update_self]
      exact hJo
    · rw [Function.update_of_ne e]
      exact s2 v hv
  · by_cases e : v = w₀
    · subst e
      rw [Function.update_self]
      exact hJc
    · rw [Function.update_of_ne e]
      exact s3 v hv
  · rw [Function.update_of_ne e]
    exact s4 v hv e
  · obtain ⟨t1, t2⟩ := (hT E n π w hw).1 hsat
    obtain ⟨a1, a2⟩ := ((hL E n w₀ hw₀).2.1 w).1 hap
    obtain ⟨-, -, -, b1, b2, -⟩ := hL E n w hw
    refine ⟨fun h => hgood w h ⟨hw, a1, t1⟩, fun h => hgood _ h ⟨b1, fun e => a2 ?_, t2⟩⟩
    rw [← e, b2]
end

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open GlobalTheory.LFun (KGL)
open GlobalTheory.CongL (SatU)
open GlobalTheory.Cong (Apart)
open scoped Classical

namespace UpperTheory.Gal.CertificateRingHomMap

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

end UpperTheory.Gal.CertificateRingHomMap

theorem UpperTheory.Gal.CertificateRingHomMap.pVecU_of :
    UpperTheory.Gal.CertificateRingHomMap.NbhdU → UpperTheory.Gal.CertificateRingHomMap.StepAt → UpperTheory.Gal.CertificateRingHomMap.SphType → UpperTheory.Gal.CertificateRingHomMap.LocComm → UpperTheory.Gal.CertificateRingHomMap.VecU :=
  _root_.UpperTheory.Reformulated.B.Grk2.pVecU_of
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PStepAt
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

noncomputable section

namespace UpperTheory.Gal.CertificateRingHomMap.LevelShrinking

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem comm_of_cLoc {w : Plc E} (hw : IsSplitAt w) (z : UA E n) (hz : cLoc w z = 1)
    (y : UA E n) (hy : y ∈ locU n w) : y * z = z * y := by
  have hyf := (Subgroup.mem_inf.1 hy).1
  have hyo := (Subgroup.mem_inf.1 hy).2
  have hc : z * y * z⁻¹ * y⁻¹ ∈ locU n w := by
    refine Subgroup.mem_inf.2 ⟨?_, Subgroup.mem_iInf.2 fun u => Subgroup.mem_iInf.2 fun hu => ?_⟩
    · have h1 : cInf y = 1 := MonoidHom.mem_ker.1 hyf
      exact MonoidHom.mem_ker.2 (by simp [h1])
    · have h1 : cLoc u y = 1 := MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hyo u) hu)
      exact MonoidHom.mem_ker.2 (by simp [h1])
  have h1 := GlobalTheory.SplitPts.eq_one_of_cLoc hw ⟨_, hc⟩ (by simp [hz])
  have h2 : z * y * z⁻¹ * y⁻¹ = 1 := congrArg Subtype.val h1
  exact (mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h2)).symm

private def CJ {w : Plc E} (J : Subgroup (GLw n w)) : Subgroup (UA E n) := locU n w ⊓ J.comap (cLoc w)

private theorem isCompact_CJ {w : Plc E} (hw : IsSplitAt w) (J : Subgroup (GLw n w))
    (hJ : IsCompact (J : Set (GLw n w))) : IsCompact (CJ J : Set (UA E n)) := by
  have hc : Continuous fun x : GLw n w => (((locE hw).symm x : locU n w) : UA E n) :=
    continuous_subtype_val.comp (locE hw).symm.continuous
  have he : (CJ J : Set (UA E n)) = (fun x : GLw n w => (((locE hw).symm x : locU n w) : UA E n)) '' (J : Set (GLw n w)) := by
    ext g
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨cLoc w g, h2, ?_⟩
      have : (locE hw).symm (cLoc w g) = ⟨g, h1⟩ := by
        apply (locE hw).injective
        rw [ContinuousMulEquiv.apply_symm_apply, locE_apply]
      simp [this]
    · rintro ⟨x, hx, rfl⟩
      refine ⟨((locE hw).symm x).2, ?_⟩
      show cLoc w (locF hw x).1 ∈ J
      rw [cLoc_locF]
      exact hx
  rw [he]
  exact hJ.image hc

private theorem finite_index {w : Plc E} (hw : IsSplitAt w) (J : Subgroup (GLw n w))
    (hJ : IsCompact (J : Set (GLw n w))) (φ : UA E n → ℂ) (hφ : IsAutFormU φ) :
    ∃ N : Subgroup (CJ J : Subgroup (UA E n)), N.FiniteIndex ∧ ∀ k ∈ N, RU E n (k : UA E n) φ = φ := by
  haveI : CompactSpace (CJ J : Subgroup (UA E n)) := isCompact_iff_compactSpace.1 (isCompact_CJ hw J hJ)
  let N : Subgroup (CJ J : Subgroup (UA E n)) :=
    { carrier := {k | RU E n (k : UA E n) φ = φ}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb => by
        show RU E n ((a * b : CJ J) : UA E n) φ = φ
        rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, hb, ha]
      inv_mem' := fun {a} ha => by
        show RU E n ((a⁻¹ : CJ J) : UA E n) φ = φ
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul]
        simp }
  have hle : (CJ J : Subgroup (UA E n)) ≤ finU (E := E) (n := n) := fun k hk => (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hk).1).1
  have hop : IsOpen (N : Set (CJ J : Subgroup (UA E n))) :=
    hφ.level.preimage (f := fun k : (CJ J : Subgroup (UA E n)) => (⟨k.1, hle k.2⟩ : finU (E := E) (n := n)))
      (Continuous.subtype_mk continuous_subtype_val _)
  haveI := Subgroup.quotient_finite_of_isOpen N hop
  exact ⟨N, Subgroup.finiteIndex_of_finite_quotient, fun k hk => hk⟩

private theorem step_core (π : AutSub E n) (W : Wt E n) (f : algForms W) {w : Plc E} (hw : IsSplitAt w)
    (hf : f ∈ π.finPart W) (r : UA E n →₀ ℂ) (hr : ∀ g ∈ r.support, g ∈ locU n w) :
    ∃ f' ∈ π.finPart W, (∀ v, f'.1 v = r.sum fun g a => a • RU E n g (f.1 v)) ∧
      ∀ u : finU (E := E) (n := n), cLoc w u.1 = 1 → algRep W u f = f → algRep W u f' = f' := by
  have hle : locU n w ≤ finU (E := E) (n := n) := inf_le_left
  let F : r.support → algForms W := fun g => r g.1 • algRep W ⟨g.1, hle (hr _ g.2)⟩ f
  have hval : ∀ v, (∑ g : r.support, F g).1 v = r.sum fun g a => a • RU E n g (f.1 v) := by
    intro v
    rw [Finsupp.sum, ← Finset.sum_coe_sort r.support, Submodule.coe_sum, LinearMap.sum_apply]
    rfl
  refine ⟨∑ g : r.support, F g, AutSub.mem_finPart.2 fun v => ?_, hval, fun u hu hfix => ?_⟩
  · rw [hval]
    exact Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (π.isAut.stable _ _ (AutSub.mem_finPart.1 hf v))
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [map_sum]
      refine Finset.sum_congr rfl fun g _ => ?_
      have hcm : u * (⟨g.1, hle (hr _ g.2)⟩ : finU (E := E) (n := n)) = ⟨g.1, hle (hr _ g.2)⟩ * u :=
        Subtype.ext (comm_of_cLoc hw u.1 hu g.1 (hr _ g.2)).symm
      simp only [F]
      rw [map_smul, ← Module.End.mul_apply, ← map_mul, hcm, map_mul, Module.End.mul_apply, hfix]

private theorem mem_lev_off (hC : LocComm) {S : Finset (Plc E)} {Kw : ∀ w : Plc E, Subgroup (GLw n w)} {w : Plc E}
    (hw : IsSplitAt w) (hwS : w ∈ S) (hcj : cj w ∉ S) {J : Subgroup (GLw n w)} (u : finU (E := E) (n := n))
    (hu : ofU u ∈ lev S (Function.update Kw w J)) (x : GLw n w) (u' : finU (E := E) (n := n)) (hx : u = locF hw x * u')
    (h1 : cLoc w u'.1 = 1) : ofU u' ∈ lev S Kw := by
  obtain ⟨-, hap, -, -, hcc, -⟩ := hC E n w hw
  obtain ⟨-, hu2, hu3⟩ := mem_lev.1 hu
  have hsame : ∀ t : Plc E, GlobalTheory.Cong.Apart t w → comp t (ofU u') = comp t (ofU u) := by
    intro t ht
    have h2 : comp t (loc hw x) = 1 := comp_loc_of_apart hw ht x
    rw [hx, map_mul, map_mul]
    have h3 : comp t (ofU (locF hw x)) = 1 := h2
    rw [h3, one_mul]
  refine mem_lev.2 ⟨by rw [sim_ofU]; exact one_mem _, fun t ht => ?_, fun t ht hct => ?_⟩
  · by_cases htw : t = w
    · subst htw
      rw [comp_ofU, h1]
      exact one_mem _
    · have hne : t ≠ cj w := fun h => hcj (h ▸ ht)
      rw [hsame t ((hap t).2 ⟨htw, hne⟩)]
      have := hu2 t ht
      rwa [Function.update_of_ne htw] at this
  · have htw : t ≠ w := fun h => ht (h ▸ hwS)
    have hne : t ≠ cj w := fun h => hct (by rw [h, hcc]; exact hwS)
    rw [hsame t ((hap t).2 ⟨htw, hne⟩)]
    exact hu3 t ht hct

end UpperTheory.Gal.CertificateRingHomMap.LevelShrinking

open UpperTheory.Gal.CertificateRingHomMap.LevelShrinking in
theorem UpperTheory.Gal.CertificateRingHomMap.pStepAt_of :
    UpperTheory.Gal.CertificateRingHomMap.LocAdj → UpperTheory.Gal.CertificateRingHomMap.LocComm → UpperTheory.Gal.CertificateRingHomMap.OfUBij → UpperTheory.Gal.CertificateRingHomMap.StepAt := by
  intro hA hC _ E _ _ _ n π W f hf hf0 S Kw w hw hwS hcj hfix J χ hJc hT
  obtain ⟨φ, hφπ, hφ0, hφ⟩ := hT
  let χ' : (CJ J : Subgroup (UA E n)) →* ℂˣ :=
    χ.comp (((cLoc w).comp (CJ J : Subgroup (UA E n)).subtype).codRestrict J fun k => (Subgroup.mem_inf.1 k.2).2)
  have hf1 : f.1 ≠ 0 := fun h => hf0 (Subtype.ext h)
  obtain ⟨r, hrH, ⟨v₀, hv₀⟩, hrχ⟩ := hA (UA E n) (UA E n → ℂ) W.Sp (RU E n) π.V π.isAut.stable π.isAut.irred
    (locU n w) (CJ J) inf_le_left
    (fun g => ⟨(locF hw (cLoc w g)).1, locF_mem hw _, (locF hw (cLoc w g)).1⁻¹ * g,
      fun y hy => (comm_of_cLoc hw _ (by simp) y hy).symm, by simp⟩)
    (fun ψ hψ => finite_index hw J hJc ψ (π.isAut.aut ψ hψ)) χ'
    ⟨φ, hφπ, hφ0, fun k => hφ k.1 (Subgroup.mem_inf.1 k.2).1 (Subgroup.mem_inf.1 k.2).2⟩
    f.1 hf1 (AutSub.mem_finPart.1 hf)
  obtain ⟨f', hf', hval, hoff⟩ := step_core π W f hw hf r hrH
  refine ⟨f', hf', fun h => hv₀ ?_, fun u hu h => ?_⟩
  · rw [← hval, h]
    rfl
  · set x := cLoc w u.1 with hxdef
    set a := locF hw x with hadef
    have hax : cLoc w a.1 = x := cLoc_locF hw x
    have h1 : cLoc w ((a⁻¹ * u : finU (E := E) (n := n)) : UA E n) = 1 := by
      have : ((a⁻¹ * u : finU (E := E) (n := n)) : UA E n) = a.1⁻¹ * u.1 := rfl
      rw [this, map_mul, map_inv, hax, ← hxdef, inv_mul_cancel]
    have hu' : u = a * (a⁻¹ * u) := by group
    have hfix' : algRep W (a⁻¹ * u) f = f :=
      hfix _ (mem_lev_off hC hw hwS hcj u hu x _ hu' h1)
    have hstep := hoff _ h1 hfix'
    have hak : a.1 ∈ (CJ J : Subgroup (UA E n)) :=
      Subgroup.mem_inf.2 ⟨locF_mem hw x, by show cLoc w a.1 ∈ J; rw [hax]; exact h⟩
    have hχ : ((χ' ⟨a.1, hak⟩ : ℂˣ) : ℂ) = ((χ ⟨x, h⟩ : ℂˣ) : ℂ) := by
      have : (((cLoc w).comp (CJ J : Subgroup (UA E n)).subtype).codRestrict J
          fun k => (Subgroup.mem_inf.1 k.2).2) ⟨a.1, hak⟩ = ⟨x, h⟩ := Subtype.ext hax
      simp only [χ', MonoidHom.comp_apply, this]
    have e : algRep W u f' = algRep W a f' := by
      conv_lhs => rw [hu', map_mul, Module.End.mul_apply, hstep]
    rw [e]
    refine Subtype.ext (LinearMap.ext fun v => ?_)
    have h2 := hrχ ⟨a.1, hak⟩ v
    rw [← hval, hχ] at h2
    exact h2

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PLocAdj
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

namespace UpperTheory.Gal.CertificateRingHomMap.LocalAdjunction

variable {C V : Type} [Group C] [AddCommGroup V] [Module ℂ V]

private structure Lvl (χ : C →* ℂˣ) where
  N : Subgroup C
  nrm : N.Normal
  fin : N.FiniteIndex
  triv : ∀ n ∈ N, χ n = 1

attribute [instance] Lvl.nrm Lvl.fin

private noncomputable instance {χ : C →* ℂˣ} (L : Lvl χ) : Fintype (C ⧸ L.N) := Fintype.ofFinite _

private noncomputable def Lvl.ofFI {χ : C →* ℂˣ} (N : Subgroup C) (hN : N.FiniteIndex) (h : ∀ n ∈ N, χ n = 1) : Lvl χ :=
  ⟨N.normalCore, inferInstance, inferInstance, fun n hn => h n (Subgroup.normalCore_le N hn)⟩

private theorem Lvl.ofFI_le {χ : C →* ℂˣ} (N : Subgroup C) (hN : N.FiniteIndex) (h : ∀ n ∈ N, χ n = 1) :
    (Lvl.ofFI N hN h).N ≤ N := Subgroup.normalCore_le N

private def Lvl.inf {χ : C →* ℂˣ} (L L' : Lvl χ) : Lvl χ :=
  ⟨L.N ⊓ L'.N, inferInstance, inferInstance, fun n hn => L.triv n hn.1⟩

private def Fx (σ : Representation ℂ C V) (N : Subgroup C) (x : V) : Prop := ∀ n ∈ N, σ n x = x

private theorem Fx.mono {σ : Representation ℂ C V} {N N' : Subgroup C} {x : V} (h : Fx σ N x) (hle : N' ≤ N) : Fx σ N' x :=
  fun n hn => h n (hle hn)

private noncomputable def tw (σ : Representation ℂ C V) (χ : C →* ℂˣ) (x : V) (k : C) : V := ((χ k : ℂˣ) : ℂ)⁻¹ • σ k x

private noncomputable def av (σ : Representation ℂ C V) (χ : C →* ℂˣ) (L : Lvl χ) : V →ₗ[ℂ] V :=
  (Nat.card (C ⧸ L.N) : ℂ)⁻¹ • ∑ q : C ⧸ L.N, ((χ q.out : ℂˣ) : ℂ)⁻¹ • σ q.out

variable {σ : Representation ℂ C V} {χ : C →* ℂˣ}

private theorem av_apply (L : Lvl χ) (x : V) :
    av σ χ L x = (Nat.card (C ⧸ L.N) : ℂ)⁻¹ • ∑ q : C ⧸ L.N, tw σ χ x q.out := by
  simp [av, tw, LinearMap.sum_apply]

private theorem card_ne (L : Lvl χ) : (Nat.card (C ⧸ L.N) : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.2 Nat.card_pos.ne'

private theorem tw_congr (L : Lvl χ) {x : V} (hx : Fx σ L.N x) {a b : C} (h : (a : C ⧸ L.N) = b) :
    tw σ χ x a = tw σ χ x b := by
  have hn : a⁻¹ * b ∈ L.N := QuotientGroup.eq.1 h
  have hb : b = a * (a⁻¹ * b) := by group
  generalize a⁻¹ * b = n at hn hb
  subst hb
  simp only [tw, map_mul, Module.End.mul_apply, hx n hn, L.triv n hn, mul_one]

private theorem tw_left (x : V) (k a : C) : σ k (tw σ χ x a) = ((χ k : ℂˣ) : ℂ) • tw σ χ x (k * a) := by
  simp only [tw, map_smul, map_mul, Module.End.mul_apply, Units.val_mul, smul_smul]
  congr 1
  have h1 : ((χ k : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have h2 : ((χ a : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  field_simp

private theorem tw_right (x : V) (k a : C) : tw σ χ (σ k x) a = ((χ k : ℂˣ) : ℂ) • tw σ χ x (a * k) := by
  simp only [tw, map_mul, Module.End.mul_apply, Units.val_mul, smul_smul]
  congr 1
  have h1 : ((χ k : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have h2 : ((χ a : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  field_simp

private theorem av_eig (L : Lvl χ) {x : V} (hx : Fx σ L.N x) (k : C) :
    σ k (av σ χ L x) = ((χ k : ℂˣ) : ℂ) • av σ χ L x := by
  have hs : ∑ q : C ⧸ L.N, tw σ χ x q.out = ∑ q : C ⧸ L.N, tw σ χ x (k * q.out) := by
    rw [← Equiv.sum_comp (Equiv.mulLeft (k : C ⧸ L.N)) (fun q => tw σ χ x q.out)]
    refine Finset.sum_congr rfl fun q _ => tw_congr L hx ?_
    simp
  have e : ∑ q : C ⧸ L.N, σ k (tw σ χ x q.out) = ((χ k : ℂˣ) : ℂ) • ∑ q : C ⧸ L.N, tw σ χ x q.out := by
    rw [hs, Finset.smul_sum]
    exact Finset.sum_congr rfl fun q _ => tw_left x k _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [av_apply, map_smul, map_sum, e, smul_comm]

private theorem av_translate (L : Lvl χ) {x : V} (hx : Fx σ L.N x) (k : C) :
    av σ χ L (σ k x) = ((χ k : ℂˣ) : ℂ) • av σ χ L x := by
  have hs : ∑ q : C ⧸ L.N, tw σ χ x q.out = ∑ q : C ⧸ L.N, tw σ χ x (q.out * k) := by
    rw [← Equiv.sum_comp (Equiv.mulRight (k : C ⧸ L.N)) (fun q => tw σ χ x q.out)]
    refine Finset.sum_congr rfl fun q _ => tw_congr L hx ?_
    simp
  rw [av_apply, av_apply, hs, smul_comm]
  simp only [tw_right, Finset.smul_sum]

private theorem av_of_eig (L : Lvl χ) {y : V} (hy : ∀ k, σ k y = ((χ k : ℂˣ) : ℂ) • y) : av σ χ L y = y := by
  have h : ∀ k, tw σ χ y k = y := fun k => by
    rw [tw, hy k, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul]
  simp only [av_apply, h, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul ℂ]
  rw [smul_smul, inv_mul_cancel₀ (card_ne L), one_smul]

private theorem av_refine {L' L : Lvl χ} (hle : L'.N ≤ L.N) {x : V} (hx : Fx σ L.N x) : av σ χ L' x = av σ χ L x := by
  have h1 : av σ χ L' (av σ χ L x) = av σ χ L x := av_of_eig L' (av_eig L hx)
  have h2 : av σ χ L' (av σ χ L x) = av σ χ L' x := by
    have h : ∀ k, av σ χ L' (tw σ χ x k) = av σ χ L' x := fun k => by
      rw [tw, map_smul, av_translate L' (hx.mono hle), smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [av_apply L x, map_smul, map_sum]
    simp only [h, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul ℂ]
    rw [smul_smul, inv_mul_cancel₀ (card_ne L), one_smul]
  rw [← h2, h1]

private theorem av_indep {L L' : Lvl χ} {x : V} (hx : Fx σ L.N x) (hx' : Fx σ L'.N x) : av σ χ L x = av σ χ L' x :=
  (av_refine (L' := L.inf L') inf_le_left hx).symm.trans (av_refine (L' := L.inf L') inf_le_right hx')

private theorem av_comm (L : Lvl χ) (T : V →ₗ[ℂ] V) (hT : ∀ k x, T (σ k x) = σ k (T x)) (x : V) :
    av σ χ L (T x) = T (av σ χ L x) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [av_apply, map_smul, map_sum, tw, hT]

private def Z (σ : Representation ℂ C V) (χ : C →* ℂˣ) (x : V) : Prop := ∃ L : Lvl χ, Fx σ L.N x ∧ av σ χ L x = 0

private theorem Z.av_eq {x : V} (h : Z σ χ x) {L : Lvl χ} (hx : Fx σ L.N x) : av σ χ L x = 0 := by
  obtain ⟨L', h', h0⟩ := h
  rw [av_indep hx h', h0]

private theorem Z.add {x y : V} (hx : Z σ χ x) (hy : Z σ χ y) : Z σ χ (x + y) := by
  obtain ⟨L, h, h0⟩ := id hx
  obtain ⟨L', h', h0'⟩ := id hy
  have a : Fx σ (L.inf L').N x := h.mono inf_le_left
  have b : Fx σ (L.inf L').N y := h'.mono inf_le_right
  exact ⟨L.inf L', fun n hn => by rw [map_add (f := _), a n hn, b n hn], by rw [map_add (f := _), hx.av_eq a, hy.av_eq b, add_zero]⟩

private theorem Z.smul {x : V} (hx : Z σ χ x) (a : ℂ) : Z σ χ (a • x) := by
  obtain ⟨L, h, h0⟩ := hx
  exact ⟨L, fun n hn => by rw [map_smul, h n hn], by rw [map_smul, h0, smul_zero]⟩

private theorem exists_lvl {π : Submodule ℂ V} (hsm : ∀ φ ∈ π, ∃ N : Subgroup C, N.FiniteIndex ∧ Fx σ N φ)
    (L₀ : Lvl χ) (s : Finset V) (hs : ∀ x ∈ s, x ∈ π) : ∃ L : Lvl χ, ∀ x ∈ s, Fx σ L.N x := by
  induction s using Finset.induction_on with
  | empty => exact ⟨L₀, by simp⟩
  | insert a s _ ih =>
    obtain ⟨L, hL⟩ := ih fun x hx => hs x (Finset.mem_insert_of_mem hx)
    obtain ⟨N, hN, hfix⟩ := hsm a (hs a (Finset.mem_insert_self _ _))
    have hfi : (L.N ⊓ N).FiniteIndex := inferInstance
    have hle := Lvl.ofFI_le (χ := χ) (L.N ⊓ N) hfi (fun n hn => L.triv n hn.1)
    refine ⟨Lvl.ofFI (L.N ⊓ N) hfi (fun n hn => L.triv n hn.1), fun x hx => ?_⟩
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact hfix.mono (hle.trans inf_le_right)
    · exact (hL x hx).mono (hle.trans inf_le_left)

end UpperTheory.Gal.CertificateRingHomMap.LocalAdjunction

open UpperTheory.Gal.CertificateRingHomMap.LocalAdjunction in
theorem UpperTheory.Gal.CertificateRingHomMap.pLocAdj_of :
    UpperTheory.Gal.CertificateRingHomMap.LocAdj := by
  intro G V X _ _ _ _ _ _ ρ π hinv hirr H C hCH hdec hsm χ ⟨φ₀, hφ₀π, hφ₀, hφ₀χ⟩ f hf hfπ
  let σ : Representation ℂ C V := ρ.comp C.subtype
  have hσ : ∀ (k : C) x, σ k x = ρ (k : G) x := fun _ _ => rfl
  have hsm' : ∀ φ ∈ π, ∃ N : Subgroup C, N.FiniteIndex ∧ Fx σ N φ := hsm
  obtain ⟨N₀, hN₀, hfix₀⟩ := hsm' φ₀ hφ₀π
  have hχ₀ : ∀ n ∈ N₀, χ n = 1 := fun n hn => by
    have h1 : ((χ n : ℂˣ) : ℂ) • φ₀ = (1 : ℂ) • φ₀ := by rw [one_smul, ← hφ₀χ n]; exact hfix₀ n hn
    exact Units.ext (smul_left_injective ℂ hφ₀ h1)
  let L₀ : Lvl χ := Lvl.ofFI N₀ hN₀ hχ₀
  have hfixL₀ : Fx σ L₀.N φ₀ := hfix₀.mono (Lvl.ofFI_le _ _ _)

  let Nn : Submodule ℂ V :=
    { carrier := {φ | φ ∈ π ∧ ∀ h ∈ H, Z σ χ (ρ h φ)}
      zero_mem' := ⟨π.zero_mem, fun h _ => ⟨L₀, fun n _ => by simp, by simp⟩⟩
      add_mem' := fun {a b} ha hb => ⟨π.add_mem ha.1 hb.1, fun h hh => by
        rw [map_add (f := _)]; exact (ha.2 h hh).add (hb.2 h hh)⟩
      smul_mem' := fun c x hx => ⟨π.smul_mem c hx.1, fun h hh => by
        rw [map_smul]; exact (hx.2 h hh).smul c⟩ }
  have hNn : Nn ≤ π := fun x hx => hx.1
  have hstab : ∀ g, ∀ φ ∈ Nn, ρ g φ ∈ Nn := by
    rintro g φ ⟨hπ, hZ⟩
    obtain ⟨h₁, hh₁, c, hc, rfl⟩ := hdec g
    refine ⟨hinv _ _ hπ, fun h hh => ?_⟩
    obtain ⟨L, hL, h0⟩ := hZ (h * h₁) (H.mul_mem hh hh₁)
    have e : ρ h (ρ (h₁ * c) φ) = ρ c (ρ (h * h₁) φ) := by
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, ← mul_assoc, hc (h * h₁) (H.mul_mem hh hh₁)]
    have hT : ∀ (k : C) x, ρ c (σ k x) = σ k (ρ c x) := fun k x => by
      rw [hσ, hσ, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, hc k (hCH k.2)]
    rw [e]
    exact ⟨L, fun n hn => by rw [← hT, hL n hn], by rw [av_comm L (ρ c) hT, h0, map_zero]⟩
  have hφ₀N : φ₀ ∉ Nn := fun h => by
    have h1 := h.2 1 H.one_mem
    rw [map_one, Module.End.one_apply] at h1
    exact hφ₀ ((av_of_eig L₀ hφ₀χ).symm.trans (h1.av_eq hfixL₀))
  have hbot : Nn = ⊥ := by
    rcases hirr Nn hNn hstab with h | h
    · exact h
    · exact absurd (h ▸ hφ₀π) hφ₀N
  obtain ⟨v₀, hv₀⟩ : ∃ v, f v ≠ 0 := by
    by_contra hh
    push_neg at hh
    exact hf (LinearMap.ext hh)
  obtain ⟨h, hh, hZ⟩ : ∃ h ∈ H, ¬ Z σ χ (ρ h (f v₀)) := by
    by_contra hcon
    push_neg at hcon
    have : f v₀ ∈ Nn := ⟨hfπ v₀, hcon⟩
    rw [hbot] at this
    exact hv₀ ((Submodule.mem_bot ℂ).1 this)
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℂ X).FG)
  obtain ⟨L, hL⟩ := exists_lvl (σ := σ) hsm' L₀ (s.image fun v => ρ h (f v)) (fun x hx => by
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hx
    exact hinv _ _ (hfπ v))
  have hfix : ∀ v, Fx σ L.N (ρ h (f v)) := fun v n hn => by
    have := LinearMap.ext_on hs (f := (σ n) ∘ₗ (ρ h) ∘ₗ f) (g := (ρ h) ∘ₗ f) (fun v hv =>
      hL _ (Finset.mem_image_of_mem _ hv) n hn)
    exact LinearMap.congr_fun this v
  let r : G →₀ ℂ := ∑ q : C ⧸ L.N, Finsupp.single (((q.out : C) : G) * h)
    ((Nat.card (C ⧸ L.N) : ℂ)⁻¹ * ((χ q.out : ℂˣ) : ℂ)⁻¹)
  have hr : ∀ v, (r.sum fun g a => a • ρ g (f v)) = av σ χ L (ρ h (f v)) := fun v => by
    have e : (r.sum fun g a => a • ρ g (f v)) = Finsupp.linearCombination ℂ (fun g => ρ g (f v)) r :=
      (Finsupp.linearCombination_apply _ _).symm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e, av_apply, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finsupp.linearCombination_single, map_mul, Module.End.mul_apply, tw, mul_smul]
    rfl
  refine ⟨r, fun g hg => ?_, ⟨v₀, ?_⟩, fun k v => ?_⟩
  · have : r ∈ Finsupp.supported ℂ ℂ (H : Set G) :=
      Submodule.sum_mem _ fun q _ => Finsupp.single_mem_supported ℂ _ (H.mul_mem (hCH q.out.2) hh)
    exact Finsupp.mem_supported _ _ |>.1 this hg
  · rw [hr]
    exact fun h0 => hZ ⟨L, hfix v₀, h0⟩
  · rw [hr]
    exact av_eig L (hfix v) k
end
