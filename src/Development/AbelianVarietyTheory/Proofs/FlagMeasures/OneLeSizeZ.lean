module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountTermsGramClassOverSublattice
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowLatticesMeanEqGenusMean
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsCommonSublatticeSmallDet
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EncardSublatticesBoundedDetLeSum
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PairIsometryUniqueOnOrthModIsotropic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeSeenInDefiniteSpaceDetRankIndex
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDataWithTermSingleOrbitPrimeTo

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthTransversalFlagsInfIsotropicEqBot
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthTransversalFlagsInfIsotropicEqBot
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical

namespace GlobalTheory.LoopC.PerpFlags

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem mem_orth (U : Submodule E S.V) (v : S.V) : v ∈ orth S U ↔ ∀ x ∈ U, S.hT x v = 0 := by
  simp [orth, Submodule.mem_iInf]

theorem orth_anti {U U' : Submodule E S.V} (h : U ≤ U') : orth S U' ≤ orth S U := fun v hv =>
  (mem_orth _ _).2 fun x hx => (mem_orth _ _).1 hv x (h hx)

theorem xplus_le {T : E} {Λ : Submodule (𝓞 E) S.V} (hΛ : Submodule.IsFullLattice E Λ) (F : LFlag S r T)
    (M : Submodule (𝓞 E) S.V) (h1 : XLam Λ F ≤ M) (h2 : F.fl.z ∈ M) : Xplus F ≤ spanE S M := by
  refine sup_le (fun v hv => ?_) ((Submodule.span_singleton_le_iff_mem _ _).2 (Submodule.subset_span h2))
  obtain ⟨d, hd0, hd⟩ := GlobalTheory.Mass.RowPerp.exists_smul_mem hΛ v
  have h3 : d • v ∈ M := h1 ⟨hd, (toO S (Xsp F)).smul_mem d hv⟩
  have h4 := Submodule.smul_mem _ (algebraMap (𝓞 E) E d)⁻¹ (Submodule.subset_span (R := E) h3)
  rwa [← algebraMap_smul E d v,
    inv_smul_smul₀ ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr hd0)] at h4

theorem gflag_eq_zero {T T' : E} (F : FlagG S r T) (F' : FlagG S r T') (c : Fin r → E) (hc : c ≠ 0)
    (h : ∀ b, S.hT (∑ a, c a • F.e a) (F'.fvec b) = 0) : Gflag F F' = 0 := by
  have hz : ∀ b, ∑ a : Fin r, star (c a) * Zhat F F' a.castSucc b = 0 := fun b => by
    have := h b
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      starRingEnd_apply] at this
    simpa [Zhat, brS, FlagG.fvec] using this
  obtain ⟨a0, ha0⟩ := Function.ne_iff.1 hc
  have d1 : Dl F F' r = 0 := by
    rw [Dl, leadMinorE, dite_eq_left (Nat.le_succ r), ← Matrix.exists_vecMul_eq_zero_iff]
    refine ⟨fun a => star (c a), fun e => ha0 (star_eq_zero.1 (congrFun e a0)), funext fun b => ?_⟩
    exact hz (Fin.castLE (Nat.le_succ r) b)
  have d2 : Dl F F' (r + 1) = 0 := by
    rw [Dl, leadMinorE, dite_eq_left le_rfl, ← Matrix.exists_vecMul_eq_zero_iff]
    refine ⟨Fin.snoc (α := fun _ => E) (fun a => star (c a)) 0, fun e => ha0 ?_, funext fun b => ?_⟩
    · simpa using congrFun e a0.castSucc
    · simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_castSucc] using hz b
  simp [Gflag, d1, d2]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (T T' : E) (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (F' : LFlag S r T'), Submodule.IsFullLattice E Λ → IsLift Λ F → IsLift Λ F' → Gval F F' ≠ 0 → Hp Λ F F' ≤ orth S (Xplus F) ∧ Hp Λ F F' ≤ orth S (Xplus F') ∧ Hp Λ F F' ⊓ Xsp F = ⊥ := by
  intro E _ _ _ S r T T' Λ F F' hΛ hF hF' hG
  have a1 : Hp Λ F F' ≤ orth S (Xplus F) := orth_anti (xplus_le hΛ F _
    (le_sup_of_le_left (le_sup_of_le_left le_sup_left))
    (Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_right
      (hF.2 ▸ Submodule.mem_span_singleton_self _)))))
  have a2 : Hp Λ F F' ≤ orth S (Xplus F') := orth_anti (xplus_le hΛ F' _
    (le_sup_of_le_left le_sup_right)
    (Submodule.mem_sup_right (hF'.2 ▸ Submodule.mem_span_singleton_self _)))
  refine ⟨a1, a2, eq_bot_iff.2 fun x hx => ?_⟩
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hx.2
  by_cases hc : c = 0
  · simp [hc]
  refine absurd (gflag_eq_zero F.fl F'.fl c hc fun b => ?_) hG
  refine GlobalTheory.Mass.RowPerp.swap_zero S.herm ((mem_orth _ _).1 (a2 hx.1) _ ?_)
  refine Fin.lastCases ?_ (fun i => ?_) b
  · rw [FlagG.fvec, Fin.snoc_last]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  · rw [FlagG.fvec, Fin.snoc_castSucc]
    exact Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩)

end GlobalTheory.LoopC.PerpFlags
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthTransversalFlagsInfIsotropicEqBotStatement
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orth_transversal_flags_inf_isotropic_eq_bot : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (T T' : E) (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (F' : LFlag S r T'), Submodule.IsFullLattice E Λ → IsLift Λ F → IsLift Λ F' → Gval F F' ≠ 0 → Hp Λ F F' ≤ orth S (Xplus F) ∧ Hp Λ F F' ≤ orth S (Xplus F') ∧ Hp Λ F F' ⊓ Xsp F = ⊥ := by
  first | exact @GlobalTheory.LoopC.PerpFlags.main | exact GlobalTheory.LoopC.PerpFlags.main | (intros; apply GlobalTheory.LoopC.PerpFlags.main <;> first | assumption | exact (by assumption : Submodule.IsFullLattice _ _).toIsLattice)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PairLatticeLeLiftedPairLatticeSupIsotropic
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PairLatticeLeLiftedPairLatticeSupIsotropic
noncomputable section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LoopC.PairLat

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' T₂ : E}
  {Λ : Submodule (𝓞 E) S.V} {g : ℕ}

theorem mem_orth {U : Submodule E S.V} {x : S.V} : x ∈ orth S U ↔ ∀ u ∈ U, S.hT u x = 0 := by
  simp [orth, Submodule.mem_iInf, LinearMap.mem_ker]

theorem hT_z_X (F : LFlag S r T) {x : S.V} (hx : x ∈ Xsp F) : S.hT F.fl.z x = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    have h := S.herm.eq (F.fl.e a) F.fl.z
    rw [F.fl.z_orth a] at h
    simpa using h.symm
  | zero => simp
  | add y z _ _ h1 h2 => simp [h1, h2]
  | smul c y _ h => simp [h]

theorem X_eq_Xflag (F : LFlag S r T) : Xsp F = Xflag F r := by
  change Submodule.span E (Set.range F.fl.e) = Submodule.span E (F.fl.e '' {i | i.1 < r})
  congr 1
  ext y
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, a.2, rfl⟩
  · rintro ⟨a, _, rfl⟩
    exact ⟨a, rfl⟩

theorem mem_Lsub_of {F : LFlag S r T} {l y : S.V} (hl : l ∈ Lrep Λ F) (h : y - l ∈ Xsp F) :
    y ∈ Lsub Λ F := by
  have hlo : l ∈ orth S (Xsp F) := (Submodule.mem_inf.1 hl).2
  have hy : y = l + (y - l) := by abel
  refine Submodule.mem_inf.2 ⟨?_, ?_⟩
  · rw [hy]
    exact Submodule.add_mem_sup hl h
  · rw [hy]
    exact (orth S (Xsp F)).add_mem hlo (FrEqv.X_le_orth h)

theorem IotaRel_zero (F : LFlag S r T) (F' : LFlag S r T') : IotaRel Λ g F F' 0 :=
  ⟨0, Submodule.zero_mem _, by simp, 0, Submodule.zero_mem _, by simp, by simp⟩

theorem IotaRel_add {F : LFlag S r T} {F' : LFlag S r T'} {x y : S.V}
    (hx : IotaRel Λ g F F' x) (hy : IotaRel Λ g F F' y) : IotaRel Λ g F F' (x + y) := by
  obtain ⟨l, hl, h1, l', hl', h2, h3⟩ := hx
  obtain ⟨m, hm, k1, m', hm', k2, k3⟩ := hy
  refine ⟨l + m, Submodule.add_mem _ hl hm, ?_, l' + m', Submodule.add_mem _ hl' hm', ?_, ?_⟩
  · have := (Xsp F).add_mem h1 k1
    rwa [show x - l + (y - m) = x + y - (l + m) by abel] at this
  · have := (Xsp F').add_mem h2 k2
    rwa [show x - l' + (y - m') = x + y - (l' + m') by abel] at this
  · have := Submodule.add_mem _ h3 k3
    rwa [show l - l' + (m - m') = l + m - (l' + m') by abel] at this

theorem IotaRel_smul {F : LFlag S r T} {F' : LFlag S r T'} {x : S.V} (o : 𝓞 E)
    (hx : IotaRel Λ g F F' x) : IotaRel Λ g F F' (o • x) := by
  obtain ⟨l, hl, h1, l', hl', h2, h3⟩ := hx
  refine ⟨o • l, Submodule.smul_mem _ o hl, ?_, o • l', Submodule.smul_mem _ o hl', ?_, ?_⟩
  · rw [← smul_sub]
    exact (toO S (Xsp F)).smul_mem o h1
  · rw [← smul_sub]
    exact (toO S (Xsp F')).smul_mem o h2
  · rw [← smul_sub]
    exact Submodule.smul_mem _ o h3

theorem La_props {F : LFlag S r T} {F' : LFlag S r T'} {x : S.V} (hx : x ∈ La Λ g F F') :
    x ∈ L0sub Λ F ∧ x ∈ L0sub Λ F' ∧ IotaRel Λ g F F' x := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact hx.2
  | zero => exact ⟨Submodule.zero_mem _, Submodule.zero_mem _, IotaRel_zero F F'⟩
  | add y z _ _ h1 h2 =>
    exact ⟨Submodule.add_mem _ h1.1 h2.1, Submodule.add_mem _ h1.2.1 h2.2.1, IotaRel_add h1.2.2 h2.2.2⟩
  | smul c y _ h =>
    exact ⟨Submodule.smul_mem _ c h.1, Submodule.smul_mem _ c h.2.1, IotaRel_smul c h.2.2⟩

theorem map_Lrep {F' F'' : LFlag S r T'} {β : S.V ≃ₗ[E] S.V} (hβ : IsAutLam S Λ β)
    (hX : (Xsp F').map (β : S.V →ₗ[E] S.V) = Xsp F'') {l : S.V} (hl : l ∈ Lrep Λ F') :
    β l ∈ Lrep Λ F'' := by
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hl
  refine Submodule.mem_inf.2 ⟨(FrEqv.aut_mem_iff hβ l).2 h1, ?_⟩
  refine mem_orth.2 fun u hu => ?_
  rw [← hX] at hu
  obtain ⟨v, hv, rfl⟩ := hu
  have := hβ.1 v l
  exact this.trans (mem_orth.1 h2 v hv)

theorem Mlat_le_La_sup (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (T T' : E)
    (Λ : Submodule (𝓞 E) S.V) (g : ℕ) (F : LFlag S r T) (F' F'' : LFlag S r T') (β : S.V ≃ₗ[E] S.V)
    (hP : IsPair Λ F F' F'' β g) : Mlat Λ F F' F'' β g ≤ La Λ g F F'' ⊔ toO S (Xsp F) := by
  obtain ⟨hβ, hfl, hz, hc⟩ := hP
  have hX : (Xsp F').map (β : S.V →ₗ[E] S.V) = Xsp F'' := by
    rw [X_eq_Xflag F', X_eq_Xflag F'']
    exact hfl r
  intro x₁ hx
  obtain ⟨hLa, hTh⟩ := Submodule.mem_inf.1 hx
  obtain ⟨h0, h0', l, hl, hxl, l', hl', hxl', hll⟩ := La_props hLa
  have hz1 : S.hT F.fl.z x₁ = 0 := (Submodule.mem_inf.1 h0).2
  have hz1' : S.hT F'.fl.z x₁ = 0 := (Submodule.mem_inf.1 h0').2
  obtain ⟨⟨a, x₂⟩, hp, he⟩ := (Submodule.restrictScalars_mem _ _ _).1 hTh
  have hax : a = x₁ := he
  subst hax
  obtain ⟨⟨hprod, h12⟩, hβ12⟩ := Submodule.mem_inf.1 hp |>.imp_left Submodule.mem_inf.1
  have hx₂ : x₂ ∈ Hp Λ F F'' := hprod.2
  have h12 : a - x₂ ∈ Xsp F := h12
  have hβ12 : β a - x₂ ∈ Xsp F'' := hβ12
  have hβl : β l' ∈ Lrep Λ F'' := map_Lrep hβ hX hl'
  have hβd : β (a - l') ∈ Xsp F'' := by
    rw [← hX]
    exact ⟨a - l', hxl', rfl⟩
  have k1 : x₂ - l ∈ Xsp F := by
    have := (Xsp F).sub_mem hxl h12
    rwa [show a - l - (a - x₂) = x₂ - l by abel] at this
  have k2 : x₂ - β l' ∈ Xsp F'' := by
    have := (Xsp F'').sub_mem hβd hβ12
    rwa [map_sub, show β a - β l' - (β a - x₂) = x₂ - β l' by abel] at this
  have m1 : S.hT F.fl.z x₂ = 0 := by
    have := hT_z_X F h12
    rw [map_sub, hz1, zero_sub, neg_eq_zero] at this
    exact this
  have m2 : S.hT F''.fl.z x₂ = 0 := by
    have := hT_z_X F'' hβ12
    rw [map_sub, ← hz, hβ.1 F'.fl.z a, hz1', zero_sub, neg_eq_zero, hz] at this
    exact this
  have hmem : x₂ ∈ La Λ g F F'' := by
    refine Submodule.subset_span ⟨hx₂, Submodule.mem_inf.2 ⟨mem_Lsub_of hl k1, m1⟩,
      Submodule.mem_inf.2 ⟨mem_Lsub_of hβl k2, m2⟩, l, hl, k1, β l', hβl, k2, ?_⟩
    exact (hc l' hl' l hl).1 hll
  have hsum : a = x₂ + (a - x₂) := by abel
  rw [hsum]
  exact Submodule.add_mem_sup hmem h12

end GlobalTheory.LoopC.PairLat

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PairLatticeLeLiftedPairLatticeSupIsotropicStatement
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairLattice_le_liftedPairLattice_sup_isotropic : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (T T' : E) (Λ : Submodule (𝓞 E) S.V) (g : ℕ) (F : LFlag S r T) (F' F'' : LFlag S r T') (β : S.V ≃ₗ[E] S.V), IsPair Λ F F' F'' β g → Mlat Λ F F' F'' β g ≤ La Λ g F F'' ⊔ toO S (Xsp F) := by
  first | exact @GlobalTheory.LoopC.PairLat.Mlat_le_La_sup | exact GlobalTheory.LoopC.PairLat.Mlat_le_La_sup | (intros; apply GlobalTheory.LoopC.PairLat.Mlat_le_La_sup <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.XLamLeSmulSupXLamAdmissibleFlag
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.XLamLeSmulSupXLamAdmissibleFlag
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdmFlagSub

open IsDedekindDomain Formalism.HermitianLatticesTheory

section Loc

variable {R W : Type} [CommRing R] [AddCommGroup W] [Module R W] (p : Ideal R) [hp : p.IsPrime]

theorem mem_localization_iff (L : Submodule R W) (x : W) :
    x ∈ localization₂ p L ↔ ∃ s, s ∉ p ∧ s • x ∈ L := Iff.rfl

theorem le_localized_self (L : Submodule R W) : L ≤ localization₂ p L := fun x hx =>
  (mem_localization_iff p L x).2 ⟨1, fun h => hp.ne_top ((Ideal.eq_top_iff_one _).2 h), by simpa using hx⟩

theorem localization_le_of_le_localization₂ {L N : Submodule R W} (h : L ≤ localization₂ p N) : localization₂ p L ≤ localization₂ p N := by
  intro x hx
  obtain ⟨s, hs, hsx⟩ := (mem_localization_iff p L x).1 hx
  obtain ⟨t, ht, htx⟩ := (mem_localization_iff p N _).1 (h hsx)
  refine (mem_localization_iff p N x).2 ⟨t * s, fun hm => ?_, by rwa [mul_smul]⟩
  rcases hp.mem_or_mem hm with h1 | h1
  · exact ht h1
  · exact hs h1

end Loc

theorem mem_of_forall_locP {E W : Type} [Field E] [NumberField E] [AddCommGroup W]
    [Module (𝓞 E) W] (N : Submodule (𝓞 E) W) (x : W)
    (h : ∀ P : HeightOneSpectrum (𝓞 E), x ∈ (haveI := P.isPrime; localization₂ P.asIdeal N)) : x ∈ N := by
  by_contra hx
  let I : Ideal (𝓞 E) := N.comap (LinearMap.toSpanSingleton (𝓞 E) W x)
  have hI : I ≠ ⊤ := by
    intro hI
    have : (1 : 𝓞 E) ∈ I := by rw [hI]; trivial
    apply hx
    simpa [I] using this
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hI
  have hM0 : M ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField E)
  obtain ⟨s, hs, hsx⟩ := h ⟨M, hM.isPrime, hM0⟩
  exact hs (hIM (by simpa [I] using hsx))

theorem xLam_le_smul_sup_xLam :
    ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (T T' : E)
      (Λ : Submodule (𝓞 E) S.V) (g : ℕ) (F : LFlag S r T) (F' : LFlag S r T'),
      IsFixedConv Λ g F → IsFixedConv Λ g F' → IsAdmissible Λ g F F' →
        XLam Λ F ≤ Ideal.span {(g : 𝓞 E)} • Λ ⊔ XLam Λ F' := by
  intro E _ _ _ S r T T' Λ g F F' hF hF' hA x hx
  obtain ⟨ξ, hξ0, hξ1, hξ⟩ := hA
  set N : Submodule (𝓞 E) S.V := Ideal.span {(g : 𝓞 E)} • Λ ⊔ XLam Λ F' with hN
  apply mem_of_forall_locP
  intro P
  haveI := P.isPrime
  by_cases hg : (g : 𝓞 E) ∈ P.asIdeal
  swap
  · refine (mem_localization_iff _ _ _).2 ⟨g, hg, Submodule.mem_sup_left ?_⟩
    exact Submodule.smul_mem_smul (Ideal.subset_span rfl) hx.1
  obtain ⟨c, -, hc1, hc⟩ := hF.1 P
  obtain ⟨c', -, hc1', hc'⟩ := hF'.1 P
  simp only [hc1 hg, one_smul] at hc
  simp only [hc1' hg, one_smul] at hc'
  have he' : ∀ b, F'.fl.e b ∈ localization₂ P.asIdeal N := by
    intro b
    have h1 : F'.fl.e b ∈ localization₂ P.asIdeal (XLam Λ F') := by
      rw [hc']
      exact le_localized_self _ _ (Submodule.subset_span ⟨b, rfl⟩)
    exact localization_le_of_le_localization₂ _ (le_sup_right.trans (le_localized_self _ _)) h1
  have hf : ∀ n : ℕ, ∀ b : Fin r, b.1 = n → F.fl.e b ∈ localization₂ P.asIdeal N := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro b hb
      have h1 : frame F' b.castSucc - frameAct (frame F) ξ b.castSucc ∈ localization₂ P.asIdeal N :=
        localization_le_of_le_localization₂ _ (le_sup_left.trans (le_localized_self _ _)) (hξ b.castSucc P hg)
      have h2 : frame F' b.castSucc = F'.fl.e b := by simp [frame, FlagG.fvec]
      have h3 : frameAct (frame F) ξ b.castSucc ∈ localization₂ P.asIdeal N := by
        have := Submodule.sub_mem _ (he' b) h1
        rw [h2] at this
        simpa using this
      have h4 : frameAct (frame F) ξ b.castSucc =
          F.fl.e b + ∑ a ∈ Finset.univ.erase b, ξ a.castSucc b.castSucc • F.fl.e a := by
        unfold frameAct
        rw [Fin.sum_univ_castSucc, hξ0 (Fin.last r) b.castSucc (Fin.castSucc_lt_last b),
          ← Finset.add_sum_erase _ _ (Finset.mem_univ b), hξ1]
        simp only [frame, FlagG.fvec, Fin.snoc_castSucc, RingOfIntegers.coe_eq_algebraMap, map_zero,
          map_one, zero_smul, add_zero, one_smul, algebraMap_smul]
      have h5 : ∑ a ∈ Finset.univ.erase b, ξ a.castSucc b.castSucc • F.fl.e a ∈
          localization₂ P.asIdeal N := by
        refine Submodule.sum_mem _ fun a ha => ?_
        rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase ha) with hab | hab
        · exact Submodule.smul_mem _ _ (ih a.1 (hb ▸ hab) a rfl)
        · rw [hξ0 _ _ (Fin.castSucc_lt_castSucc_iff.2 hab), zero_smul]
          exact Submodule.zero_mem _
      rw [h4] at h3
      simpa using Submodule.sub_mem _ h3 h5
  have hx' : x ∈ localization₂ P.asIdeal (XLam Λ F) := le_localized_self _ _ hx
  rw [hc] at hx'
  refine localization_le_of_le_localization₂ _ ?_ hx'
  rw [Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  exact hf _ a rfl

end GlobalTheory.AdmFlagSub

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.XLamLeSmulSupXLamAdmissibleFlagStatement
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.xLam_le_smul_sup_xLam_admissible_flag : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (T T' : E) (Λ : Submodule (𝓞 E) S.V) (g : ℕ) (F : LFlag S r T) (F' : LFlag S r T'), IsFixedConv Λ g F → IsFixedConv Λ g F' → IsAdmissible Λ g F F' → XLam Λ F ≤ Ideal.span {(g : 𝓞 E)} • Λ ⊔ XLam Λ F' := by
  first | exact @GlobalTheory.AdmFlagSub.xLam_le_smul_sup_xLam | exact GlobalTheory.AdmFlagSub.xLam_le_smul_sup_xLam | (intros; apply GlobalTheory.AdmFlagSub.xLam_le_smul_sup_xLam <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LiftedFlagLatticeChainSpans
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LiftedFlagLatticeChainSpans
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LoopC.LatChain

section
variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E}

theorem mem_orth {U : Submodule E S.V} {v : S.V} : v ∈ orth S U ↔ ∀ x ∈ U, S.hT x v = 0 := by
  simp [orth, Submodule.mem_iInf]

theorem exists_mul_mem {Λ : Submodule (𝓞 E) S.V} (hΛ : Submodule.IsFullLattice E Λ) (v : S.V) :
    ∃ d : 𝓞 E, d ≠ 0 ∧ d • v ∈ Λ := by
  have hv : v ∈ Submodule.span E (Λ : Set S.V) := by
    letI := hΛ
    rw [Submodule.IsFullLattice.span_eq_top]; trivial
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 E)) E _ v hv
  rw [Submodule.span_eq] at ht
  exact ⟨t, nonZeroDivisors.ne_zero t.2, ht⟩

theorem le_spanE {Λ M : Submodule (𝓞 E) S.V} (hΛ : Submodule.IsFullLattice E Λ) {U : Submodule E S.V}
    (h : Λ ⊓ toO S U ≤ M) : U ≤ spanE S M := by
  intro v hv
  obtain ⟨d, hd0, hd⟩ := exists_mul_mem hΛ v
  have h0 : d • v ∈ toO S U := (toO S U).smul_mem d hv
  have h1 : d • v ∈ M := h ⟨hd, h0⟩
  have h2 := Submodule.smul_mem _ (algebraMap (𝓞 E) E d)⁻¹ (Submodule.subset_span (R := E) h1)
  rwa [← algebraMap_smul E d v, inv_smul_smul₀
    ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr hd0)] at h2

theorem spanE_le {M : Submodule (𝓞 E) S.V} {U : Submodule E S.V} (h : M ≤ toO S U) : spanE S M ≤ U :=
  Submodule.span_le.2 h

variable {r : ℕ} {T T' : E} {Λ : Submodule (𝓞 E) S.V}

theorem mem_L0sub {F : LFlag S r T} {x : S.V} (hx : x ∈ Lrep Λ F) (hz : S.hT F.fl.z x = 0) :
    x ∈ L0sub Λ F :=
  ⟨⟨Submodule.mem_sup_left hx, hx.2⟩, hz⟩

theorem thp_le_la (g : ℕ) {F : LFlag S r T} {F' : LFlag S r T'} (hΛ : Submodule.IsFullLattice E Λ)
    (hF : IsLift Λ F) (hF' : IsLift Λ F') : Thp Λ F F' ≤ La Λ g F F' := by
  intro x hx
  have hperp : ∀ y ∈ UUE Λ F F', S.hT y x = 0 := mem_orth.1 hx.2
  have hX : Xsp F ≤ UUE Λ F F' :=
    le_spanE hΛ (le_sup_of_le_left (le_sup_of_le_left le_sup_left))
  have hX' : Xsp F' ≤ UUE Λ F F' := le_spanE hΛ (le_sup_of_le_left le_sup_right)
  have hz : F.fl.z ∈ UUE Λ F F' := by
    rw [← hF.2]
    exact Submodule.subset_span (Submodule.mem_sup_left (Submodule.mem_sup_left
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))))
  have hz' : F'.fl.z ∈ UUE Λ F F' := by
    rw [← hF'.2]
    exact Submodule.subset_span (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
  have h1 : x ∈ Lrep Λ F := ⟨hx.1, mem_orth.2 fun y hy => hperp y (hX hy)⟩
  have h2 : x ∈ Lrep Λ F' := ⟨hx.1, mem_orth.2 fun y hy => hperp y (hX' hy)⟩
  refine Submodule.subset_span ⟨hx.2, mem_L0sub h1 (hperp _ hz), mem_L0sub h2 (hperp _ hz'),
    x, h1, ?_, x, h2, ?_, ?_⟩ <;> rw [sub_self] <;> exact Submodule.zero_mem _

end

theorem lattice_chain_spans : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (T T' : E) (Λ : Submodule (𝓞 E) S.V) (g : ℕ) (F : LFlag S r T) (F' : LFlag S r T'), Submodule.IsFullLattice E Λ → IsLift Λ F → IsLift Λ F' → Thp Λ F F' ≤ La Λ g F F' ∧ La Λ g F F' ≤ L0sub Λ F ⊓ toO S (Hp Λ F F') ∧ spanE S (Thp Λ F F') = Hp Λ F F' ∧ ∀ (F'' : LFlag S r T') (β : S.V ≃ₗ[E] S.V), spanE S (Mlat Λ F F' F'' β g) = Th Λ F F' F'' β := by
  intro E _ _ _ S r T T' Λ g F F' hΛ hF hF'
  have h1 := thp_le_la g hΛ hF hF'
  refine ⟨h1, Submodule.span_le.2 fun x hx => ⟨hx.2.1, hx.1⟩,
    le_antisymm (spanE_le inf_le_right) (le_spanE hΛ le_rfl), fun F'' β =>
    le_antisymm (spanE_le inf_le_right) (le_spanE hΛ fun x hx => ⟨h1 ⟨hx.1, ?_⟩, hx.2⟩)⟩
  obtain ⟨p, hp, e⟩ := hx.2
  have : p.1 = x := e
  rw [← this]
  exact hp.1.1.1

end GlobalTheory.LoopC.LatChain
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LiftedFlagLatticeChainSpansStatement
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftedFlag_lattice_chain_spans : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (T T' : E) (Λ : Submodule (𝓞 E) S.V) (g : ℕ) (F : LFlag S r T) (F' : LFlag S r T'), Submodule.IsFullLattice E Λ → IsLift Λ F → IsLift Λ F' → Thp Λ F F' ≤ La Λ g F F' ∧ La Λ g F F' ≤ L0sub Λ F ⊓ toO S (Hp Λ F F') ∧ spanE S (Thp Λ F F') = Hp Λ F F' ∧ ∀ (F'' : LFlag S r T') (β : S.V ≃ₗ[E] S.V), spanE S (Mlat Λ F F' F'' β g) = Th Λ F F' F'' β := by
  first | exact @GlobalTheory.LoopC.LatChain.lattice_chain_spans | exact GlobalTheory.LoopC.LatChain.lattice_chain_spans | (intros; apply GlobalTheory.LoopC.LatChain.lattice_chain_spans <;> first | assumption | (letI := ‹Submodule.IsFullLattice _ _›; infer_instance))
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LoopCountExponentBound
open NumberField Module Matrix Formalism.BasicNotions
open scoped ENNReal

namespace GlobalTheory

theorem loop_count_exponent_bound : ∀ C₁ Ad : ℝ, 1 ≤ C₁ → ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ C ≥ C₀, ∀ (s r f : ℕ) (De NT HH : ℝ), 1 ≤ s → 1 ≤ f → 1 ≤ De → 1 ≤ NT → 1 ≤ HH → De ≤ HH ^ Ad → NT ≤ HH → De ^ (4 + Real.logb 2 (2 * f)) * (De * NT) ^ (C₁ * s + C₁ * Real.log f) * (9 ^ (s * f) * (HH ^ (max Ad 3)) ^ (3 * r + 5 * s + 5 * s * r + 2 * r ^ 2)) ^ 2 ≤ HH ^ (C * ((s : ℝ) + (2 * r + 2)) * (2 * r + 2) + C * (1 + Real.logb 2 (2 * f))) * (C * s * f) ^ (6 * s * f) := by
  intro C₁ Ad hC₁
  have ha3 : (3 : ℝ) ≤ max Ad 3 := le_max_right _ _
  have haA : Ad ≤ max Ad 3 := le_max_left _ _
  generalize max Ad 3 = a at ha3 haA ⊢
  have hb : (0 : ℝ) ≤ (a + 1) * C₁ := by positivity
  refine ⟨5 * a + (a + 1) * C₁, by linarith, ?_⟩
  intro C hC s r f De NT HH hs hf hDe hNT hHH hDA hN
  have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hr' : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hH0 : 0 < HH := by linarith
  have hlf0 : 0 ≤ Real.log f := Real.log_nonneg hf'
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl21 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
  have hlfL : Real.log f ≤ Real.logb 2 (2 * f) := by
    rw [Real.logb, le_div_iff₀ hl2, Real.log_mul (by norm_num) (by linarith)]
    nlinarith
  have hL0 : 0 ≤ Real.logb 2 (2 * (f : ℝ)) := le_trans hlf0 hlfL
  generalize Real.logb 2 (2 * (f : ℝ)) = L at hlfL hL0 ⊢
  generalize Real.log (f : ℝ) = l at hlfL hlf0 ⊢
  have hDa : De ≤ HH ^ a := hDA.trans (Real.rpow_le_rpow_of_exponent_le hHH haA)
  have hDN : De * NT ≤ HH ^ (a + 1) := by
    rw [Real.rpow_add hH0, Real.rpow_one]
    exact mul_le_mul hDa hN (by linarith) (by positivity)
  have h1 : De ^ (4 + L) ≤ HH ^ (a * (4 + L)) := by
    rw [Real.rpow_mul hH0.le]
    exact Real.rpow_le_rpow (by linarith) hDa (by linarith)
  have h2 : (De * NT) ^ (C₁ * s + C₁ * l) ≤ HH ^ ((a + 1) * (C₁ * s + C₁ * l)) := by
    rw [Real.rpow_mul hH0.le]
    exact Real.rpow_le_rpow (by positivity) hDN (by positivity)
  have h3 : ((HH ^ a) ^ (3 * r + 5 * s + 5 * s * r + 2 * r ^ 2)) ^ 2
      = HH ^ (a * (2 * (3 * (r : ℝ) + 5 * s + 5 * s * r + 2 * r ^ 2))) := by
    rw [← pow_mul, ← Real.rpow_natCast, ← Real.rpow_mul hH0.le]
    congr 1
    push_cast
    ring
  have hC3 : (3 : ℝ) ≤ C * s * f := by
    have h0 : (3 : ℝ) ≤ C := by linarith
    have : (3 : ℝ) ≤ C * s := by nlinarith
    nlinarith
  have h4 : ((9 : ℝ) ^ (s * f)) ^ 2 ≤ (C * s * f) ^ (6 * s * f) := by
    calc ((9 : ℝ) ^ (s * f)) ^ 2 = 3 ^ (4 * (s * f)) := by
          rw [show (9 : ℝ) = 3 ^ 2 by norm_num, ← pow_mul, ← pow_mul]
          congr 1; ring
      _ ≤ 3 ^ (6 * s * f) := pow_le_pow_right₀ (by norm_num) (by nlinarith [Nat.zero_le (s * f)])
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) hC3 _
  have hexp : a * (4 + L) + (a + 1) * (C₁ * s + C₁ * l)
      + a * (2 * (3 * (r : ℝ) + 5 * s + 5 * s * r + 2 * r ^ 2))
      ≤ C * ((s : ℝ) + (2 * r + 2)) * (2 * r + 2) + C * (1 + L) := by
    set P : ℝ := ((s : ℝ) + (2 * r + 2)) * (2 * r + 2) with hP
    have hsr : (0 : ℝ) ≤ s * r := by positivity
    have hrr : (0 : ℝ) ≤ r ^ 2 := by positivity
    have e1 : (s : ℝ) ≤ P := by rw [hP]; nlinarith
    have e2 : 2 * (3 * (r : ℝ) + 5 * s + 5 * s * r + 2 * r ^ 2) ≤ 5 * P := by rw [hP]; nlinarith
    have hP0 : 0 ≤ P := by linarith
    have e3 : (5 * a + (a + 1) * C₁) * P ≤ C * P := mul_le_mul_of_nonneg_right hC hP0
    have e4 : (5 * a + (a + 1) * C₁) * (1 + L) ≤ C * (1 + L) :=
      mul_le_mul_of_nonneg_right hC (by linarith)
    have e5 : (a + 1) * C₁ * s ≤ (a + 1) * C₁ * P := mul_le_mul_of_nonneg_left e1 hb
    have e6 : (a + 1) * C₁ * l ≤ (a + 1) * C₁ * (1 + L) := mul_le_mul_of_nonneg_left (by linarith) hb
    have e7 := mul_le_mul_of_nonneg_left e2 (show 0 ≤ a by linarith)
    have e8 : a * (4 + L) ≤ a * (5 * (1 + L)) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have e9 : C * ((s : ℝ) + (2 * r + 2)) * (2 * r + 2) = C * P := by rw [hP]; ring
    rw [e9]
    clear_value P
    linear_combination e3 + e4 + e5 + e6 + e7 + e8
  rw [mul_pow, h3]
  calc _ ≤ HH ^ (a * (4 + L)) * HH ^ ((a + 1) * (C₁ * s + C₁ * l)) *
        ((C * s * f) ^ (6 * s * f) * HH ^ (a * (2 * (3 * (r : ℝ) + 5 * s + 5 * s * r + 2 * r ^ 2)))) := by
        gcongr
    _ = HH ^ (a * (4 + L) + (a + 1) * (C₁ * s + C₁ * l)
      + a * (2 * (3 * (r : ℝ) + 5 * s + 5 * s * r + 2 * r ^ 2))) * (C * s * f) ^ (6 * s * f) := by
        rw [Real.rpow_add hH0, Real.rpow_add hH0]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hHH hexp) (by positivity)

end GlobalTheory
end

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LoopC.PairMean

theorem cnt_triples {α γ ι : Type} {E : α → α → Prop} (hE : Equivalence E) (X : Set (α × α × γ))
    (R : α × α × γ → α × α × γ → Prop) (hR : ∀ p ∈ X, ∀ q ∈ X, R p q ↔ E p.1 q.1 ∧ E p.2.1 q.2.1)
    (S : Set ι) (Y₁ Y₂ : ι → Set α) (h : ∀ p ∈ X, ∃ i ∈ S, p.1 ∈ Y₁ i ∧ p.2.1 ∈ Y₂ i) (K : ℝ≥0∞) (hK : K ≠ 0)
    (h₁ : ∀ i ∈ S, (cntCl (Y₁ i) E : ℝ≥0∞) ≤ K) (h₂ : ∀ i ∈ S, (cntCl (Y₂ i) E : ℝ≥0∞) ≤ K) :
    (cntCl X R : ℝ≥0∞) ≤ (S.encard : ℝ≥0∞) * (K * K) := by
  rcases S.finite_or_infinite with hS | hS
  swap
  · rw [hS.encard_eq, ENat.toENNReal_top, ENNReal.top_mul (mul_ne_zero hK hK)]
    exact le_top
  lift S to Finset ι using hS
  let c : α → Set α := fun a => {b | E a b}
  have e1 : cntCl X R ≤ (⋃ i ∈ S, (c '' Y₁ i) ×ˢ (c '' Y₂ i)).encard := by
    refine le_trans (Set.encard_le_encard ?_)
      (Set.encard_image_le (fun C : Set α × Set α => {q | q ∈ X ∧ q.1 ∈ C.1 ∧ q.2.1 ∈ C.2}) _)
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨i, hi, a1, a2⟩ := h p hp
    refine ⟨(c p.1, c p.2.1), ?_, ?_⟩
    · simp only [Set.mem_iUnion]
      exact ⟨i, hi, ⟨_, a1, rfl⟩, ⟨_, a2, rfl⟩⟩
    · ext q
      exact and_congr_right fun hq => (hR p hp q hq).symm
  have e2 := e1.trans (FrEqv.encard_biUnion_le' S _)
  refine (ENat.toENNReal_le.2 e2).trans ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [show ((∑ i ∈ S, ((c '' Y₁ i) ×ˢ (c '' Y₂ i)).encard : ℕ∞) : ℝ≥0∞) =
    ∑ i ∈ S, ((((c '' Y₁ i) ×ˢ (c '' Y₂ i)).encard : ℕ∞) : ℝ≥0∞) from map_sum ENat.toENNRealRingHom _ _]
  refine (Finset.sum_le_card_nsmul S _ (K * K) fun i hi => ?_).trans ?_
  · rw [Set.encard_prod, ENat.toENNReal_mul, ← FrEqv.cntCl_eq_encard hE, ← FrEqv.cntCl_eq_encard hE]
    exact mul_le_mul' (h₁ i hi) (h₂ i hi)
  · simp

theorem Xflag_top {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}
    (F : LFlag S r T) : Xflag F r = Xsp F := by
  unfold Xflag Xsp FlagG.Xa FlagG.X
  congr 1
  ext x
  simp

theorem X_le_L0sub {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}
    (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) : toO S (Xsp F) ≤ L0sub Λ F := by
  intro x hx
  refine ⟨⟨Submodule.mem_sup_right hx, FrEqv.X_le_orth hx⟩, ?_⟩
  have : Xsp F ≤ LinearMap.ker (S.hT F.fl.z) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, rfl⟩
    exact GlobalTheory.Mass.RowPerp.swap_zero S.herm (F.fl.z_orth a)
  exact this hx

theorem seen_mono (D : D7) {T : D.host.E} (F : Fg D T) {N N' : LatV D} (h : N ≤ N' ⊔ toO (hS D) (Xsp F)) :
    seen D F N ≤ seen D F N' :=
  Submodule.comap_mono (sup_le h le_sup_right)

theorem fixedHyp_full (D : D7) {T : D.host.E} (F : Fg D T) (Λ : LatV D)
    (hF : FixedHyp D Λ F) : Submodule.IsFullLattice D.host.E Λ := by
  letI := hF.1
  exact ⟨GlobalTheory.LoopC.Base.span_eq_top_of_unimodular (hS D).hT
    (hS D).herm (hS D).nondeg hF.1 hF.2.1⟩

theorem term_seen (D : D7) {T T' : D.host.E} (F : Fg D T) (F' : Fg D T') (Λ : LatV D) (hF : FixedHyp D Λ F)
    (hW : WHyp D F (Wsp D)) (h : IsTermF D Λ F F') :
    seen D F (La Λ (gS D) F F') ≤ L0X D Λ F ∧ seen D F (Thp Λ F F') ≤ seen D F (La Λ (gS D) F F') ∧
    rkW D (seen D F (Thp Λ F F')) = rkW D (seen D F (La Λ (gS D) F F')) ∧
    idxW D (seen D F (La Λ (gS D) F F')) (seen D F (Thp Λ F F')) = iIdx Λ (gS D) F F' := by
  obtain ⟨a1, -, a3⟩ := GlobalTheory.T.orth_transversal_flags_inf_isotropic_eq_bot _ _ _ _ _ Λ F F' (by first | exact fixedHyp_full D F Λ hF | exact (fixedHyp_full D F Λ hF).toIsLattice) hF.2.2.1 h.1.1 h.1.2.2
  obtain ⟨b1, b2, b3, -⟩ := GlobalTheory.T.liftedFlag_lattice_chain_spans _ _ _ _ _ Λ (gS D) F F' (fixedHyp_full D F Λ hF) hF.2.2.1 h.1.1
  have b4 : La Λ (gS D) F F' ≤ toO (hS D) (Hp Λ F F') := b2.trans inf_le_right
  obtain ⟨-, c2, c3⟩ := GlobalTheory.T.latticeSeenInDefiniteSpace_det_rank_index D T F _ hW a1 a3 _ _ b4 (b1.trans b4)
  obtain ⟨-, d2, -⟩ := GlobalTheory.T.latticeSeenInDefiniteSpace_det_rank_index D T F _ hW a1 a3 _ _ (b1.trans b4) b4
  refine ⟨Submodule.comap_mono (sup_le (b2.trans inf_le_left) (X_le_L0sub Λ F)),
    seen_mono D F (b1.trans le_sup_left), ?_, c3⟩
  have : spanE (hS D) (La Λ (gS D) F F') = Hp Λ F F' :=
    le_antisymm (Submodule.span_le.2 b4) (b3.symm.le.trans (Submodule.span_mono b1))
  rw [c2, d2, b3, this]

theorem pair_sub (D : D7) {T T' : D.host.E} (F : Fg D T) (Λ : LatV D) (hF : FixedHyp D Λ F)
    (hW : WHyp D F (Wsp D)) (hpos : IsPosDef (D.sp.X 0).hT) (hfg : (L0X D Λ F).FG)
    (hint : Formalism.HermitianLatticesTheory.IsIntegralLat (D.sp.X 0).hT (L0X D Λ F)) (Z' Z'' : GramM D) (s : ℕ) (hs : 1 ≤ s) (De : ℝ)
    (p : Trip D T') (hp : p ∈ PairSet D Λ T' F Z' Z'' s De) :
    ∃ P ∈ {P : LatW D | P ≤ L0X D Λ F ∧ rkW D P = D.R.k - s ∧ detW D P ≤ De},
      p.1 ∈ FrSet D Λ F T' Z' P ∧ p.2.1 ∈ FrSet D Λ F T' Z'' P := by
  obtain ⟨t1, t2, hpr, z1, z2, hs0, hd⟩ := hp
  obtain ⟨a1, a2, a3, a4⟩ := term_seen D F p.1 Λ hF hW t1
  obtain ⟨b1, b2, b3, b4⟩ := term_seen D F p.2.1 Λ hF hW t2
  obtain ⟨c1, -, c3⟩ := GlobalTheory.T.orth_transversal_flags_inf_isotropic_eq_bot _ _ _ _ _ Λ F p.1 (by first | exact fixedHyp_full D F Λ hF | exact (fixedHyp_full D F Λ hF).toIsLattice) hF.2.2.1 t1.1.1 t1.1.2.2
  obtain ⟨-, d2, -, d4⟩ := GlobalTheory.T.liftedFlag_lattice_chain_spans _ _ _ _ _ Λ (gS D) F p.1 (fixedHyp_full D F Λ hF) hF.2.2.1 t1.1.1
  have hM : Mlat Λ F p.1 p.2.1 p.2.2 (gS D) ≤ La Λ (gS D) F p.1 := inf_le_left
  have hMH := hM.trans (d2.trans inf_le_right)
  obtain ⟨e1, e2, -⟩ := GlobalTheory.T.latticeSeenInDefiniteSpace_det_rank_index D T F _ hW c1 c3 _ _ hMH hMH
  have m1 := seen_mono D F (hM.trans le_sup_left)
  have m2 := seen_mono D F (GlobalTheory.T.pairLattice_le_liftedPairLattice_sup_isotropic _ _ _ _ _ Λ (gS D) F p.1 p.2.1 p.2.2 hpr)
  obtain ⟨P, q1, q2, q3, q4, q5⟩ := GlobalTheory.T.exists_common_sublattice_small_det D _ _ _ _ _ _ hpos hfg hint m1 m2 a1 b1 a2 b2 a3 b3
  refine ⟨P, ⟨q1.trans (m1.trans a1), ?_, ?_⟩, ⟨t1, z1, q2⟩, ⟨t2, z2, q3⟩⟩
  · rw [q4, e2, d4]
    unfold s0 at hs0
    omega
  · rw [e1, a4, b4] at q5
    exact q5.trans hd

theorem pEqv_iff (D : D7) {T : D.host.E} {T' : ℕ} (hT' : 0 < T') (hg : 3 ≤ gS D) (F : Fg D T) (Λ : LatV D)
    (hF : FixedHyp D Λ F) (Z' Z'' : GramM D) (s : ℕ) (De : ℝ) (p : Trip D (T' : D.host.E))
    (hp : p ∈ PairSet D Λ (T' : D.host.E) F Z' Z'' s De) (q : Trip D (T' : D.host.E))
    (hq : q ∈ PairSet D Λ (T' : D.host.E) F Z' Z'' s De) :
    PEqv D Λ F p q ↔ TEqv D Λ F p.1 q.1 ∧ TEqv D Λ F p.2.1 q.2.1 := by
  constructor
  · rintro ⟨n', h', n'', h'', a, b, -⟩
    exact ⟨⟨n', h', a⟩, ⟨n'', h'', b⟩⟩
  · rintro ⟨⟨n', h', a⟩, ⟨n'', h'', b⟩⟩
    refine ⟨n', h', n'', h'', a, b, ?_⟩
    obtain ⟨t1, t2, hpr, -⟩ := hq
    obtain ⟨c1, c2, c3, c4⟩ := GlobalTheory.T.isPair_move_by_integralUnipotent D _ _ Λ (gS D) F p.1 p.2.1 q.1 q.2.1 p.2.2 n' n'' hp.2.2.1 h' h'' a b
    have hX := hpr.2.1 D.R.rS
    rw [Xflag_top, Xflag_top] at hX
    exact GlobalTheory.T.pair_isometry_unique_on_orth_mod_isotropic _ _ _ _ _ Λ (gS D) F q.1 q.2.1 q.2.2 _ hF.1 hF.2.1 hg (Nat.cast_ne_zero.2 hT'.ne')
      (GlobalTheory.T.trace_form_pos_on_orth_liftedFlag D T' q.1 hT')
      (GlobalTheory.T.xLam_le_smul_sup_xLam_admissible_flag _ _ _ _ _ Λ (gS D) F q.1 hF.2.2.2 t1.2.1 t1.1.2.1)
      (GlobalTheory.T.xLam_le_smul_sup_xLam_admissible_flag _ _ _ _ _ Λ (gS D) F q.2.1 hF.2.2.2 t2.2.1 t2.1.2.1)
      hpr.1 hX (by rw [hpr.2.2.1, sub_self]; exact Submodule.zero_mem _) hpr.2.2.2 c1 c2 c3 c4

theorem mean_le {ι : Type} (what₂ : Finset ι) (w cnt : ι → ℝ≥0∞) (N : ℕ → ι → ℝ≥0∞) (I : Finset ℕ) (c B : ℕ → ℝ)
    (K Bd : ℝ) (hK : 0 ≤ K) (hc : ∀ d ∈ I, 0 ≤ c d) (hB : ∀ d ∈ I, 0 ≤ B d)
    (h1 : ∀ i ∈ what₂, cnt i ≤ (∑ d ∈ I, N d i * ENNReal.ofReal (c d)) * (ENNReal.ofReal K * ENNReal.ofReal K))
    (h2 : ∀ d ∈ I, ∑ i ∈ what₂, w i * N d i ≤ (∑ i ∈ what₂, w i) * ENNReal.ofReal (B d))
    (h3 : (∑ d ∈ I, B d * c d) * K ^ 2 ≤ Bd) :
    ∑ i ∈ what₂, w i * cnt i ≤ (∑ i ∈ what₂, w i) * ENNReal.ofReal Bd := by
  calc ∑ i ∈ what₂, w i * cnt i
      ≤ ∑ i ∈ what₂, w i * ((∑ d ∈ I, N d i * ENNReal.ofReal (c d)) * (ENNReal.ofReal K * ENNReal.ofReal K)) :=
        Finset.sum_le_sum fun i hi => mul_le_mul' le_rfl (h1 i hi)
    _ = ∑ d ∈ I, (∑ i ∈ what₂, w i * N d i) * (ENNReal.ofReal (c d) * (ENNReal.ofReal K * ENNReal.ofReal K)) := by
        simp only [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    _ ≤ ∑ d ∈ I, ((∑ i ∈ what₂, w i) * ENNReal.ofReal (B d)) *
          (ENNReal.ofReal (c d) * (ENNReal.ofReal K * ENNReal.ofReal K)) :=
        Finset.sum_le_sum fun d hd => mul_le_mul' (h2 d hd) le_rfl
    _ = (∑ i ∈ what₂, w i) * ENNReal.ofReal ((∑ d ∈ I, B d * c d) * K ^ 2) := by
        rw [ENNReal.ofReal_mul (Finset.sum_nonneg fun d hd => mul_nonneg (hB d hd) (hc d hd)),
          ENNReal.ofReal_sum_of_nonneg (fun d hd => mul_nonneg (hB d hd) (hc d hd)), ENNReal.ofReal_pow hK,
          Finset.sum_mul I, Finset.mul_sum I]
        refine Finset.sum_congr rfl fun d hd => ?_
        rw [ENNReal.ofReal_mul (hB d hd)]
        ring
    _ ≤ _ := mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal h3)

theorem sum_bound (k : ℕ) (De N e e' l X X' : ℝ) (hDe : 1 ≤ De) (hN : 1 ≤ N) (he : 0 ≤ e) (hee : e ≤ e') (hl : 0 ≤ l)
    (hX : 0 ≤ X) (hXX : X ≤ X') :
    ∑ d ∈ Finset.Icc 1 ⌊De⌋₊, ((d : ℝ) / N) ^ k * ((d : ℝ) * N) ^ e * X * (De / d) ^ ((k : ℝ) + l + 1) ≤
      (De / N) ^ k * X' * (De ^ (4 + l) * (De * N) ^ e') := by
  have hD0 : 0 < De := by linarith
  have hN0 : 0 < N := by linarith
  have hX' : 0 ≤ X' := hX.trans hXX
  refine (Finset.sum_le_card_nsmul _ _ ((De / N) ^ k * X' * (De ^ (l + 1) * (De * N) ^ e')) fun d hd => ?_).trans ?_
  · obtain ⟨d1, d2⟩ := Finset.mem_Icc.1 hd
    have d1' : (1 : ℝ) ≤ d := by exact_mod_cast d1
    have d2' : (d : ℝ) ≤ De := (Nat.le_floor_iff hD0.le).1 d2
    have d0 : (0 : ℝ) < d := by linarith
    have a1 : ((d : ℝ) * N) ^ e ≤ (De * N) ^ e' :=
      (Real.rpow_le_rpow (by positivity) (by gcongr) he).trans
        (Real.rpow_le_rpow_of_exponent_le (one_le_mul_of_one_le_of_one_le hDe hN) hee)
    have a2 : (De / d) ^ (l + 1) ≤ De ^ (l + 1) :=
      Real.rpow_le_rpow (by positivity) (div_le_self hD0.le d1') (by linarith)
    have a3 : (De / N) ^ k = ((d : ℝ) / N) ^ k * (De / d) ^ k := by
      rw [← mul_pow]; congr 1; field_simp
    rw [add_assoc, Real.rpow_add (by positivity), Real.rpow_natCast, a3]
    calc _ = ((d : ℝ) / N) ^ k * (De / d) ^ k * X * ((De / d) ^ (l + 1) * ((d : ℝ) * N) ^ e) := by ring
      _ ≤ _ := by gcongr
  · have a1 : De * De ^ (l + 1) ≤ De ^ (4 + l) := by
      calc De * De ^ (l + 1) = De ^ (1 + (l + 1)) := by rw [Real.rpow_add hD0 1, Real.rpow_one]
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hDe (by linarith)
    have a2 : (⌊De⌋₊ : ℝ) ≤ De := Nat.floor_le hD0.le
    rw [Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    calc _ ≤ De * ((De / N) ^ k * X' * (De ^ (l + 1) * (De * N) ^ e')) := by gcongr
      _ = (De / N) ^ k * X' * (De * De ^ (l + 1) * (De * N) ^ e') := by ring
      _ ≤ _ := by gcongr

theorem K_bound (s r f : ℕ) (De N H : ℝ) (hDe : 0 ≤ De) (hN : 0 ≤ N) (hH : 1 ≤ H) (h1 : De ≤ H) (h2 : N ≤ H) :
    N ^ (2 * r) * De ^ r * 9 ^ (s * f) * H ^ (9 * s + 9 * s * r + 16 * r ^ 2) ≤
      9 ^ (s * f) * (H ^ 8) ^ (3 * r + 5 * s + 5 * s * r + 2 * r ^ 2) := by
  have hH0 : 0 ≤ H := by linarith
  calc _ ≤ H ^ (2 * r) * H ^ r * 9 ^ (s * f) * H ^ (9 * s + 9 * s * r + 16 * r ^ 2) := by gcongr
    _ = 9 ^ (s * f) * H ^ (3 * r + 9 * s + 9 * s * r + 16 * r ^ 2) := by ring
    _ ≤ _ := by
      rw [← pow_mul]
      refine mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hH ?_) (by positivity)
      nlinarith [Nat.zero_le (s * r), Nat.zero_le r, Nat.zero_le s]

theorem mass_nonneg (D : D7) (j : ℕ) : 0 ≤ massS D j := by
  unfold massS massU Formalism.HermitianLatticesTheory.mass
  split_ifs
  · positivity
  · exact le_rfl

theorem Xi_mono (D : D7) (u : D.what₂.Word) (HH C C' : ℝ) (s : ℕ) (hH : 1 ≤ HH) (hN : 1 ≤ NT D u) (hC : 0 ≤ C)
    (hCC : C ≤ C') : 0 ≤ XiS D u HH C s ∧ XiS D u HH C s ≤ XiS D u HH C' s := by
  unfold XiS Xi
  split_ifs
  · exact ⟨div_nonneg (mul_nonneg (mass_nonneg D _) (mass_nonneg D _)) (mass_nonneg D _), le_rfl⟩
  · have h1 := one_le_mul_of_one_le_of_one_le hH hN
    have h0 : 0 ≤ HH * NT D u := by linarith
    have hC' : 0 ≤ C' := hC.trans hCC
    refine ⟨by positivity, mul_le_mul (by gcongr) (Real.rpow_le_rpow_of_exponent_le h1 (by gcongr))
      (by positivity) (by positivity)⟩
  · exact ⟨le_rfl, le_rfl⟩

theorem one_le_sizeZ (D : D7) (b C : ℝ) (Z : GramM D) : 1 ≤ sizeZ D b C Z := by
  unfold sizeZ
  have key : ∀ {ι : Type} (s : Finset ι) (f : ι → ℝ), (∀ i ∈ s, 1 ≤ f i) → 1 ≤ ∏ i ∈ s, f i := by
    intro ι s f h
    exact Finset.prod_induction f (fun x => 1 ≤ x) (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb) le_rfl h
  exact key _ _ fun τ _ => key _ _ fun l _ => le_max_left _ _

theorem rpow_le_HHZ (D : D7) (b C x : ℝ) (hb : 1 ≤ b) (hC : 1 ≤ C) (hx : x ≤ C * (D.R.m : ℝ) ^ 2 * D.R.f)
    (Z : GramM D) : b ^ x ≤ HHZ D b C Z := by
  have hm : (1 : ℝ) ≤ D.R.m := by have := D.R.two_le_m; exact_mod_cast (by omega : 1 ≤ D.R.m)
  have h1 : 1 ≤ b ^ (C * (D.R.m : ℝ) ^ 2 * D.R.f) := Real.one_le_rpow hb (by positivity)
  calc b ^ x ≤ b ^ (C * (D.R.m : ℝ) ^ 2 * D.R.f) := Real.rpow_le_rpow_of_exponent_le hb hx
    _ ≤ (b ^ (C * (D.R.m : ℝ) ^ 2 * D.R.f)) ^ (C * (D.R.m : ℝ)) :=
      Real.self_le_rpow_of_one_le h1 (one_le_mul_of_one_le_of_one_le hC hm)
    _ ≤ _ := le_mul_of_one_le_right (by positivity) (one_le_pow₀ (one_le_sizeZ D b C Z))

theorem main : ∀ Cg cb Cu cT CT C0 A Ad C₁ : ℝ, 0 ≤ C₁ → ∃ C₀ : ℝ, ∀ C ≥ C₀, ∀ (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl : ℝ), 1 ≤ Cl → Formalism.MainNotions.S.UnitaryVolumeMass.stLem3L0 D u → Formalism.MainNotions.S.UnitaryVolumeMass.congruence_at_split_frobenius_holds D large₂ u u' C' Cl Cg cb Cu cT CT C0 A C₁ → Formalism.MainNotions.S.UnitaryVolumeMass.MeanFlagPairCount D large₂ u u' C' Cl Cg cb Cu cT CT C0 A Ad C := by
  intro Cg cb Cu cT CT C0 A Ad C₁ hC₁
  obtain ⟨C₂, hC₂⟩ := GlobalTheory.T.count_terms_gramClass_over_sublattice Cg cb Cu cT CT C0 A
  obtain ⟨C₃, -, hC₃⟩ := GlobalTheory.loop_count_exponent_bound (max C₁ 1) (max Ad 1 * 8) (le_max_right _ _)
  refine ⟨max (max C₂ C₃) (max (max C₁ 1) |CT|), ?_⟩
  intro C hC D large₂ u u' C' Cl hCl _ H1 hyp F0 he hz what₂ hrows Z' Z'' r1 r2 s s2 sk De d1 d2
  simp only [ge_iff_le, max_le_iff] at hC
  obtain ⟨⟨c2, c3⟩, ⟨c1, c0⟩, cT'⟩ := hC
  rcases what₂.eq_empty_or_nonempty with rfl | ⟨Λ₀, hΛ₀⟩
  · simp [MeanLe]
  have hst : Stand D u u' := hyp.2.1
  have hbase : IsBase D u F0 := ⟨he, hz⟩
  obtain ⟨-, p1, p2, p3, p4, p5, -, g1, g2, -⟩ := id hst
  have hg : 3 ≤ gS D := by
    have := g1.two_le
    have := g2.two_le
    unfold Formalism.MainNotions.S.Lat.gS
    nlinarith
  have hb : 1 ≤ large₂.sc.b := Real.one_le_exp (Real.rpow_nonneg (by linarith [large₂.sc.one_lt_alt]) _)
  have hT : Tr D u ≤ large₂.sc.b ^ (CT * D.R.m) := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := hyp.1.1
    exact (h u).2
  have hf : 1 ≤ D.R.f := by
    have := D.R.m_le_f
    have := D.R.two_le_m
    unfold Ranks.f Ranks.n
    omega
  have hm1 : (1 : ℝ) ≤ D.R.m := by have := D.R.two_le_m; exact_mod_cast (by omega : 1 ≤ D.R.m)
  have hm : (D.R.m : ℝ) = 2 * D.R.rS + 2 := by exact_mod_cast (GlobalTheory.real_places_facts D).2.2.2.1
  have hN1 : 1 ≤ NT D u := one_le_pow₀ (by exact_mod_cast (show 1 ≤ Tu D u by omega))
  have o1 : 1 ≤ HHZ D large₂.sc.b C Z' := by simpa using rpow_le_HHZ D _ C 0 hb c0 (by positivity) Z'
  have o2 : 1 ≤ HHZ D large₂.sc.b C Z'' := by simpa using rpow_le_HHZ D _ C 0 hb c0 (by positivity) Z''
  have hN : NT D u ≤ HHZ D large₂.sc.b C Z' := by
    refine le_trans ?_ (rpow_le_HHZ D _ C (CT * D.R.m * (D.R.f : ℕ)) hb c0 ?_ Z')
    · rw [Real.rpow_mul_natCast (by linarith), NT]
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) hT _
    · refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
      have := le_abs_self CT
      nlinarith [mul_le_mul_of_nonneg_right (this.trans cT') (by linarith : (0 : ℝ) ≤ D.R.m),
        mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ C) (by linarith : (0 : ℝ) ≤ D.R.m))
          (by linarith : (0 : ℝ) ≤ D.R.m - 1)]
  have hHb : Hb large₂.sc.b C₁ D.R.m D.R.f ≤ HHZ D large₂.sc.b C Z' := rpow_le_HHZ D _ C _ hb c0 (by gcongr) Z'
  have q1 : HHZ D large₂.sc.b C Z' ≤ HHZ D large₂.sc.b C Z' * HHZ D large₂.sc.b C Z'' := le_mul_of_one_le_right (by linarith) o2
  have q2 : HHZ D large₂.sc.b C Z'' ≤ HHZ D large₂.sc.b C Z' * HHZ D large₂.sc.b C Z'' := le_mul_of_one_le_left (by linarith) o1
  generalize HHZ D large₂.sc.b C Z' * HHZ D large₂.sc.b C Z'' = HH at q1 q2 d2 ⊢
  have hH : 1 ≤ HH := o1.trans q1
  have e1 : HH ≤ HH ^ max Ad 1 := Real.self_le_rpow_of_one_le hH (le_max_right _ _)
  have e2 : De ≤ HH ^ max Ad 1 := d2.trans (Real.rpow_le_rpow_of_exponent_le hH (le_max_left _ _))
  have e3 : (HH ^ max Ad 1) ^ 8 = HH ^ (max Ad 1 * 8) := by
    rw [← Real.rpow_mul_natCast (by linarith)]; norm_num
  have e4 : max (max Ad 1 * 8) 3 = max Ad 1 * 8 := max_eq_left (by linarith [le_max_right Ad 1])
  have e5 : 1 ≤ HH ^ max Ad 1 := hH.trans e1
  have e6 : De ≤ (HH ^ max Ad 1) ^ 3 := e2.trans (le_self_pow₀ e5 (by norm_num))
  have fin := hC₃ C c3 s D.R.rS D.R.f De (NT D u) HH (by omega) hf d1 hN1 hH
    (by rw [← e3]; exact e2.trans (le_self_pow₀ e5 (by norm_num))) (hN.trans q1)
  rw [e4, ← e3, ← hm] at fin
  have kb := K_bound s D.R.rS D.R.f De (NT D u) _ (by linarith) (by linarith) e5 e2 ((hN.trans q1).trans e1)
  have s23 := fun Λ hΛ Z hZ P hP hr hd hh => hC₂ C c2 D large₂ u u' C' Cl hCl hyp F0 he hz Λ hΛ Z hZ s (by omega) sk P hP hr
    De (HH ^ max Ad 1) d1 hd hh e6
  have k0 : 0 < NT D u ^ (2 * D.R.rS) * De ^ D.R.rS * 9 ^ (s * D.R.f) *
    (HH ^ max Ad 1) ^ (9 * s + 9 * s * D.R.rS + 16 * D.R.rS ^ 2) := by positivity
  generalize NT D u ^ (2 * D.R.rS) * De ^ D.R.rS * 9 ^ (s * D.R.f) *
    (HH ^ max Ad 1) ^ (9 * s + 9 * s * D.R.rS + 16 * D.R.rS ^ 2) = K at kb s23 k0
  obtain ⟨x0, x1⟩ := Xi_mono D u HH C₁ C s hH hN1 hC₁ c1
  have hf' : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf
  have lf0 : 0 ≤ Real.log D.R.f := Real.log_nonneg hf'
  have l0 : 0 ≤ lg2f D.R.f := Real.logb_nonneg (by norm_num) (by linarith)
  obtain ⟨hWH, -, hpos, hlat₀, -⟩ := GlobalTheory.T.standardBaseFlag_complement_integralLattice D u u' F0 Λ₀ hst hbase (hrows.1 Λ₀ hΛ₀)
  have hfull : Submodule.IsFullLattice D.host.E (L0X D Λ₀ (lf D F0)) := by
    refine { toIsLattice := hlat₀, span_eq_top := ?_ }
    apply eq_top_iff.mpr
    intro w _
    have hΛ₀ : Submodule.span D.host.E (Λ₀ : Set (VS D).V) = ⊤ :=
      (fixedHyp_full D (lf D F0) Λ₀ (hrows.1 Λ₀ hΛ₀).2.1).span_eq_top
    have hw : D.sp.iXY 0 w ∈ orth (hS D) F0.Xplus :=
      hWH.1.le (Submodule.mem_sup_left ⟨w, rfl⟩)
    have hwX : D.sp.iXY 0 w ∈ orth (hS D) F0.X :=
      (Formalism.MainNotions.mem_orth_iff _ _).2 fun x hx =>
        (Formalism.MainNotions.mem_orth_iff _ _).1 hw x (Submodule.mem_sup_left hx)
    have hwz : (hS D).hT F0.z (D.sp.iXY 0 w) = 0 :=
      (Formalism.MainNotions.mem_orth_iff _ _).1 hw _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 D.host.E)) D.host.E Λ₀ (D.sp.iXY 0 w) (hΛ₀ ▸ Submodule.mem_top)
    rw [Submodule.span_eq] at ht
    have ht0 : (algebraMap (𝓞 D.host.E) D.host.E t) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors t.2
    have hmem : (t : 𝓞 D.host.E) • w ∈ L0X D Λ₀ (lf D F0) := by
      change D.sp.iXY 0 ((t : 𝓞 D.host.E) • w) ∈ L0sub Λ₀ (lf D F0)
      rw [← algebraMap_smul D.host.E, map_smul, algebraMap_smul]
      have hort : (t : 𝓞 D.host.E) • D.sp.iXY 0 w ∈ toO (hS D) (orth (hS D) F0.X) := by
        change (t : 𝓞 D.host.E) • D.sp.iXY 0 w ∈ (orth (hS D) F0.X).restrictScalars (𝓞 D.host.E)
        exact Submodule.smul_mem _ _ hwX
      refine ⟨⟨Submodule.mem_sup_left ⟨ht, hort⟩, hort⟩, ?_⟩
      change (hS D).hT F0.z ((t : 𝓞 D.host.E) • D.sp.iXY 0 w) = 0
      rw [← algebraMap_smul D.host.E, map_smul, hwz, smul_zero]
    have hspan : (t : 𝓞 D.host.E) • w ∈ Submodule.span D.host.E ((L0X D Λ₀ (lf D F0)) : Set (D.sp.X 0).V) :=
      Submodule.subset_span hmem
    have hspan' : (algebraMap (𝓞 D.host.E) D.host.E t) • w ∈
        Submodule.span D.host.E ((L0X D Λ₀ (lf D F0)) : Set (D.sp.X 0).V) := by
      rw [algebraMap_smul]
      exact hspan
    have := (Submodule.span D.host.E ((L0X D Λ₀ (lf D F0)) : Set (D.sp.X 0).V)).smul_mem (algebraMap (𝓞 D.host.E) D.host.E t)⁻¹ hspan'
    rw [smul_smul, inv_mul_cancel₀ ht0, one_smul] at this
    exact this
  obtain ⟨⟨reps, hreps⟩, -, hmass⟩ := Formalism.HermitianLatticesTheory.final_massBasic _ _ (D.sp.X 0).hT (D.sp.X 0).herm
    (GlobalTheory.Mass.GenusOrb.trace_pos_of_PD _ hpos) _ hfull
  refine mean_le what₂ _ _ (fun d Λ => (cntPrim (D.sp.X 0).hT (L0X D Λ (lf D F0)) (D.R.k - s) d : ℝ≥0∞))
    (Finset.Icc 1 ⌊De⌋₊) (fun d => (De / (d : ℝ)) ^ ((D.R.k : ℝ) + lg2f D.R.f + 1))
    (fun d => ((d : ℝ) / NT D u) ^ D.R.k * ((d : ℝ) * NT D u) ^ (C₁ * s + C₁ * Real.log D.R.f) * XiS D u HH C₁ s)
    K _ k0.le (fun d _ => by positivity) (fun d _ => by positivity) (fun Λ hΛ => ?_) (fun d hd => ?_) ?_
  · have hR := hrows.1 Λ hΛ
    obtain ⟨hW, -, -, hlat, hint, -⟩ := GlobalTheory.T.standardBaseFlag_complement_integralLattice D u u' F0 Λ hst hbase hR
    refine (cnt_triples (FrEqv.TEqv_equivalence D Λ (lf D F0)) _ _
      (pEqv_iff D (by omega) hg _ Λ hR.2.1 Z' Z'' s De) _ _ _
      (pair_sub D _ Λ hR.2.1 hW hpos hlat.fg hint Z' Z'' s (by omega) De) (ENNReal.ofReal K)
      (ENNReal.ofReal_pos.2 k0).ne' (fun P hP => s23 Λ hR Z' r1 P hP.1 hP.2.1 hP.2.2 (q1.trans e1))
      (fun P hP => s23 Λ hR Z'' r2 P hP.1 hP.2.1 hP.2.2 (q2.trans e1))).trans (mul_le_mul' ?_ le_rfl)
    exact GlobalTheory.T.encard_sublattices_bounded_det_le_sum D _ hpos (GlobalTheory.Mass.RowPerp.main D u F0 he hz).1.2 hlat.fg hint _ De d1
  · have a1 := GlobalTheory.T.rowLattices_mean_eq_genus_mean D u p1 p3 p5 F0 he hz what₂ hrows Λ₀ (hrows.1 Λ₀ hΛ₀) reps hreps
      (fun L => cntPrim (D.sp.X 0).hT L (D.R.k - s) d) (fun γ hγ L => GlobalTheory.T.cntPrim_latticeImage_isometry _ _ _ γ hγ L _ _)
    have a2 := H1 hyp F0 he hz Λ₀ (hrows.1 Λ₀ hΛ₀) reps hreps s s2 sk d (Finset.mem_Icc.1 hd).1 HH (hHb.trans q1)
    rw [ENNReal.ofReal_mul hmass.le] at a2
    refine (ENNReal.mul_le_mul_iff_left (ENNReal.ofReal_pos.2 hmass).ne' ENNReal.ofReal_ne_top).1 ?_
    rw [a1, mul_assoc]
    exact mul_le_mul' le_rfl (a2.trans (mul_comm _ _).le)
  · have a1 := sum_bound D.R.k De (NT D u) (C₁ * s + C₁ * Real.log D.R.f)
      (max C₁ 1 * s + max C₁ 1 * Real.log D.R.f) (lg2f D.R.f) _ _ d1 hN1 (by positivity)
      (by have := le_max_left C₁ 1; gcongr) l0 x0 x1
    have x2 := x0.trans x1
    refine (mul_le_mul a1 (pow_le_pow_left₀ k0.le kb 2) (by positivity) (by positivity)).trans ?_
    rw [mul_assoc ((De / NT D u) ^ D.R.k * XiS D u HH C s), mul_assoc ((De / NT D u) ^ D.R.k * XiS D u HH C s)]
    exact mul_le_mul_of_nonneg_left fin (by positivity)

end GlobalTheory.LoopC.PairMean
