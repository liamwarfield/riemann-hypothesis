module

public import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantUniformizer

@[expose] public section

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.DvdCondition
noncomputable section

namespace Formalism.MainNotions.N.Ln34.DvdPf

open Formalism.BasicNotions Formalism.BasicNotions.Loc Module

private theorem finrank_cyclotomicExt_dvd_sub_one {F Ω : Type*} [Field F] [CharZero F] [Field Ω] [Algebra F Ω]
    [IsAlgClosed Ω] [CharZero Ω] [Algebra.IsIntegral F Ω] (E K : IntermediateField F Ω) (hEK : E ≤ K) (l : ℕ) (hp : l.Prime)
    (hle : K ≤ E ⊔ IntermediateField.adjoin F {x : Ω | x ^ (l ^ 1) = 1}) :
    Module.finrank E (IntermediateField.extendScalars hEK) ∣ l - 1 := by
  have hl0 : 0 < l := hp.pos
  haveI : NeZero l := ⟨hp.ne_zero⟩
  haveI : NeZero (l : Ω) := ⟨Nat.cast_ne_zero.mpr hp.ne_zero⟩
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap F E).injective
  haveI : NeZero (l : E) := ⟨Nat.cast_ne_zero.mpr hp.ne_zero⟩
  haveI : Algebra.IsIntegral E Ω := ⟨fun x => (Algebra.IsIntegral.isIntegral (R := F) x).tower_top⟩

  obtain ⟨ζ, hζ⟩ : ∃ ζ : Ω, IsPrimitiveRoot ζ l := by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic l Ω)
      (Polynomial.degree_cyclotomic_pos l Ω hl0).ne'
    exact ⟨z, Polynomial.isRoot_cyclotomic_iff.mp hz⟩
  set M : IntermediateField E Ω := IntermediateField.adjoin E {ζ} with hM
  haveI hcyc : IsCyclotomicExtension {l} E M := by
    first
    | exact hζ.intermediateField_adjoin_isCyclotomicExtension E
    | exact hζ.intermediateField_adjoin_isCyclotomicExtension
    | exact IsPrimitiveRoot.intermediateField_adjoin_isCyclotomicExtension E hζ
  haveI : FiniteDimensional E M := by
    first
    | exact IntermediateField.adjoin.finiteDimensional (hζ.isIntegral hl0).tower_top
    | exact IsCyclotomicExtension.finiteDimensional {l} E M
  haveI : IsGalois E M := IsCyclotomicExtension.isGalois {l} E M

  have hcard : Module.finrank E M ∣ l - 1 := by
    have hμ := IsCyclotomicExtension.zeta_spec l E M
    have hinj := IsPrimitiveRoot.autToPow_injective E hμ
    have h1 : Nat.card (M ≃ₐ[E] M) ∣ Nat.card (ZMod l)ˣ := by
      rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
      exact Subgroup.card_subgroup_dvd_card _
    have h2 : Nat.card (M ≃ₐ[E] M) = Module.finrank E M := by
      first
      | exact IsGalois.card_aut_eq_finrank E M
      | (rw [Nat.card_eq_fintype_card]; exact IsGalois.card_aut_eq_finrank E M)
    have h3 : Nat.card (ZMod l)ˣ = l - 1 := by
      haveI : Fact l.Prime := ⟨hp⟩
      first
      | (rw [Nat.card_eq_fintype_card, ZMod.card_units])
      | (rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hp])
    rw [← h2, ← h3]
    exact h1

  have hsup : E ⊔ IntermediateField.adjoin F {x : Ω | x ^ (l ^ 1) = 1} ≤ M.restrictScalars F := by
    apply sup_le
    · intro y hy
      rw [IntermediateField.mem_restrictScalars]
      exact M.algebraMap_mem ⟨y, hy⟩
    · rw [IntermediateField.adjoin_le_iff]
      intro y hy
      have hy' : y ^ l = 1 := by simpa using hy
      have hζM : ζ ∈ M := IntermediateField.mem_adjoin_simple_self E ζ
      show y ∈ M.restrictScalars F
      rw [IntermediateField.mem_restrictScalars]
      first
      | (obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hy'
         exact pow_mem hζM i)
      | (obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hy' hl0
         exact pow_mem hζM i)
  have hKM : IntermediateField.extendScalars hEK ≤ M := by
    intro x hx
    rw [IntermediateField.mem_extendScalars] at hx
    exact (IntermediateField.mem_restrictScalars F).mp (hsup (hle hx))

  have hdvd : Module.finrank E (IntermediateField.extendScalars hEK) ∣ Module.finrank E M := by
    first
    | (have h := IntermediateField.relfinrank_mul_relfinrank
          (bot_le : (⊥ : IntermediateField E Ω) ≤ IntermediateField.extendScalars hEK) hKM
       rw [IntermediateField.relfinrank_bot_left, IntermediateField.relfinrank_bot_left] at h
       exact Dvd.intro _ h)
    | exact IntermediateField.finrank_dvd_of_le_right hKM
  exact hdvd.trans hcard

theorem dvdCondition : Formalism.MainNotions.N.Ln34.DvdStep := by
  intro l _ hl K LL hG
  have hle : K.1 ≤ Ks K 1 := hG.2.2.1
  have hEK : K0 K ≤ K.1 := inf_le_left
  haveI : CharZero (Om l) := charZero_of_injective_algebraMap (algebraMap ℚ_[l] (Om l)).injective
  have h := finrank_cyclotomicExt_dvd_sub_one (F := ℚ_[l]) (K0 K) K.1 hEK l (Fact.out) hle
  first
  | exact h
  | (show Module.finrank (K0 K) K.1 ∣ l - 1
     convert h using 1
     exact LinearEquiv.finrank_eq
       { toFun := fun y => ⟨y.1, y.2⟩
         invFun := fun y => ⟨y.1, y.2⟩
         map_add' := fun _ _ => rfl
         map_smul' := fun _ _ => rfl
         left_inv := fun _ => rfl
         right_inv := fun _ => rfl })

end Formalism.MainNotions.N.Ln34.DvdPf
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.NinLamPf
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section NinLamPfLocal

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem ninLamPf_local (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (Eπ : LetA O n) (h' : ℕ)
    (w : (LetA O n)ˣ) (hs1 : W.s = 1) (hw : W.q = (w : LetA O n) * Eπ)
    (h5 : ∀ i, ∀ y ∈ W.Nl T i, W.Q ^ h' • y ∈ Formalism.MainNotions.DeltaInvariantLattices.φspan W T (W.Nl T (i - 1))) :
    NinLam W T Eπ h' := by
  intro c y hy
  unfold NcS at hy
  rw [Submodule.mem_inf, Submodule.mem_inf] at hy
  obtain ⟨⟨hyN, hyD⟩, hyL⟩ := hy
  rw [Submodule.restrictScalars_mem] at hyN
  unfold LamPS
  rw [Submodule.mem_inf, Submodule.mem_inf]
  refine ⟨⟨?_, hyD⟩, hyL⟩
  rw [Submodule.restrictScalars_mem, Submodule.mem_comap]
  unfold letS at hyL
  rw [LinearMap.mem_ker] at hyL
  simp only [LinearMap.restrictScalars_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero] at hyL
  have hNl : y ∈ W.Nl T c := by
    unfold LocWach.Nl
    refine Submodule.mem_map.2 ⟨y, hyN, ?_⟩
    rw [LinearMap.smul_apply, LinearMap.id_apply, hyL]
  have h5' := h5 c y hNl
  have hQ : W.Q = W.q := by simp [LocWach.Q, hs1]
  have hE : Eπ ^ h' = ((w⁻¹ : (LetA O n)ˣ) : LetA O n) ^ h' * W.Q ^ h' := by
    rw [hQ, hw, mul_pow, ← mul_assoc, ← mul_pow, Units.inv_mul, one_pow, one_mul]
  unfold Formalism.MainNotions.DeltaInvariantLattices.smulA
  rw [LinearMap.smul_apply, LinearMap.id_apply, hE, mul_smul]
  exact Submodule.smul_mem _ _ h5'

end NinLamPfLocal

theorem ninlam_pf : NinLamStep := by
  intro D HW F Cm CA CB CK hA l _ hl K LL hG π' E hp9 T h' hcrys hjumps
  have hT1 := hA.1 l K 1 LL hG
  have hP5 := hT1.2.2.2.2.1
  obtain ⟨w, hw⟩ := hp9.2.2.2.2.1
  have hJ : Formalism.MainNotions.DeltaInvariantLattices.JumpsLet ((HW l).W K 1 LL hG) T (fun _ => h') (fun _ => h') := by
    intro τ i _
    exact hjumps τ
  have h5 := (hP5 T (fun _ => h') (fun _ => h') hcrys hJ).2.1
  exact ninLamPf_local _ T _ h' w ((HW l).W_s K 1 LL hG) hw h5

end Formalism.MainNotions.N.Ln34

end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.GradNPfA
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

private theorem gammaA_letE_eq_letE (g : W.Gam) (c : ZMod n) : W.γA g (letE c) = (letE c : LetA O n) := by
  funext i
  change (W.γ₀ g) ((letE c : LetA O n) i) = (letE c : LetA O n) i
  by_cases h : i = c
  · subst h; simp [letE]
  · simp [letE, h]

theorem gradNPf_γD_smul (g : W.Gam) (a : LetA O n) (x : W.DD T) :
    W.γD T g (a • x) = W.γA g a • W.γD T g x := by
  have h := W.γD_smul T g (algebraMap (LetA O n) W.EE a) x
  rw [algebraMap_smul, W.γE_ext, algebraMap_smul] at h
  first
  | exact h
  | simpa [Formalism.BasicNotions.LocWach.γA] using h

theorem gradNPf_tf (a : LetA O n) (ha : IsUnit (algebraMap (LetA O n) W.EE a)) (x : W.DD T)
    (hx : a • x = 0) : x = 0 := by
  obtain ⟨u, hu⟩ := ha
  have h1 : (algebraMap (LetA O n) W.EE a) • x = 0 := by rw [algebraMap_smul]; exact hx
  calc x = (↑(u⁻¹) : W.EE) • ((↑u : W.EE) • x) := by rw [smul_smul, Units.inv_mul, one_smul]
    _ = 0 := by rw [hu, h1, smul_zero]

private theorem mem_DelS_iff_forall_gammaD_fixed {x : W.DD T} : x ∈ DelS W T ↔ ∀ δ ∈ W.DelF, W.γD T δ x = x := by
  first
  | exact mem_DelS W T x
  | simp only [DelS, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero]

theorem gradNPf_DelS_γ (g : W.Gam) {x : W.DD T} (hx : x ∈ DelS W T) : W.γD T g x ∈ DelS W T := by
  have hx' := (mem_DelS_iff_forall_gammaD_fixed W T).mp hx
  refine (mem_DelS_iff_forall_gammaD_fixed W T).mpr fun δ hδ => ?_
  rw [← W.γD_mul, mul_comm, W.γD_mul, hx' δ hδ]

private theorem mem_letS_iff_letE_smul_eq (c : ZMod n) {x : W.DD T} :
    x ∈ letS W T c ↔ (letE c : LetA O n) • x = x := by
  first
  | exact mem_letS W T c x
  | simp only [letS, LinearMap.mem_ker, LinearMap.restrictScalars_apply, LinearMap.coe_restrictScalars,
      LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]

theorem gradNPf_letS_γ (g : W.Gam) (c : ZMod n) {x : W.DD T} (hx : x ∈ letS W T c) :
    W.γD T g x ∈ letS W T c := by
  have hx' := (mem_letS_iff_letE_smul_eq W T c).mp hx
  refine (mem_letS_iff_letE_smul_eq W T c).mpr ?_
  rw [← gammaA_letE_eq_letE W g c, ← gradNPf_γD_smul W T g (letE c) x, hx']

theorem gradNPf_PiNS_DelS (π' : LetA O n) (k : ℕ) {x : W.DD T} (hx : x ∈ PiNS W T π' k) :
    x ∈ DelS W T := by
  first
  | exact (Submodule.mem_inf.mp hx).2
  | (simp only [PiNS, Submodule.mem_inf] at hx; exact hx.2)

theorem gradNPf_PiNS_anti (π' : LetA O n) {j k : ℕ} (h : j ≤ k) {x : W.DD T}
    (hx : x ∈ PiNS W T π' k) : x ∈ PiNS W T π' j := by
  simp only [PiNS, Formalism.MainNotions.DeltaInvariantLattices.aN, Submodule.mem_inf, Submodule.restrictScalars_mem,
    Submodule.mem_map] at hx ⊢
  obtain ⟨⟨y, hy, rfl⟩, h2⟩ := hx
  refine ⟨⟨π' ^ (k - j) • y, Submodule.smul_mem _ _ hy, ?_⟩, h2⟩
  change π' ^ j • (π' ^ (k - j) • y) = π' ^ k • y
  rw [smul_smul, ← pow_add, Nat.add_sub_of_le h]

theorem exists_gam_pow_smul_sub_eq (π' f t : LetA O n) (c₀ : O) (hf : W.γA W.gam π' = π' * f)
    (ht : f - algebraMap O (LetA O n) c₀ = π' * t)
    (hγN : ∀ x ∈ W.NΔ T, ∃ d ∈ W.N T, W.γD T W.gam x - x = π' • d)
    (y : ℕ) (r₀ : W.DD T) (hr₀ : r₀ ∈ W.NΔ T) :
    ∃ w ∈ W.N T, W.γD T W.gam (π' ^ y • r₀) - π' ^ y • r₀ - (c₀ ^ y - 1) • (π' ^ y • r₀) =
      π' ^ (y + 1) • w := by
  have hr₀N : r₀ ∈ W.N T := hr₀.1
  obtain ⟨d, hdN, hd⟩ := hγN r₀ hr₀
  have hd' : W.γD T W.gam r₀ = r₀ + π' • d := sub_eq_iff_eq_add'.mp hd
  obtain ⟨e, he⟩ := sub_dvd_pow_sub_pow f (algebraMap O (LetA O n) c₀) y
  rw [ht] at he
  have hs : f ^ y = algebraMap O (LetA O n) c₀ ^ y + π' * (t * e) := by linear_combination he
  refine ⟨(t * e) • r₀ + f ^ y • d, Submodule.add_mem _ (Submodule.smul_mem _ _ hr₀N)
    (Submodule.smul_mem _ _ hdN), ?_⟩
  rw [gradNPf_γD_smul, map_pow, hf, mul_pow, hd', ← algebraMap_smul (LetA O n) (c₀ ^ y - 1)]
  simp only [map_sub, map_pow, map_one]
  simp only [smul_add, smul_smul]
  have c2 : π' ^ y * f ^ y * π' = π' ^ (y + 1) * f ^ y := by ring
  have c1 : π' ^ (y + 1) * (t * e) =
      π' ^ y * f ^ y - π' ^ y - (algebraMap O (LetA O n) c₀ ^ y - 1) * π' ^ y := by
    rw [hs]; ring
  rw [c2, c1, sub_smul, sub_smul]
  abel

theorem gradNPf_coker (π' f t : LetA O n) (c₀ : O) (hf : W.γA W.gam π' = π' * f)
    (ht : f - algebraMap O (LetA O n) c₀ = π' * t)
    (hu : IsUnit (algebraMap (LetA O n) W.EE π'))
    (hπΔ : ∀ δ ∈ W.DelF, W.γA δ π' = π')
    (hγN : ∀ x ∈ W.NΔ T, ∃ d ∈ W.N T, W.γD T W.gam x - x = π' • d)
    (c : ZMod n) (z : W.DD T) (hz : z ∈ PiNS W T π' 1 ⊓ letS W T c) (k : ℕ) (hk : 1 ≤ k) :
    ∃ x ∈ PiNS W T π' 1 ⊓ letS W T c,
      (∏ y ∈ Finset.Ico 1 k, (c₀ ^ y - 1)) • z - (W.γD T W.gam x - x) ∈
        PiNS W T π' k ⊓ letS W T c := by
  induction k, hk using Nat.le_induction with
  | base =>
    refine ⟨0, Submodule.zero_mem _, ?_⟩
    simp only [Finset.Ico_self, Finset.prod_empty, one_smul, map_zero, sub_zero]
    exact hz
  | succ k hk ih =>
    obtain ⟨xk, hxk, hr⟩ := ih
    set R := (∏ y ∈ Finset.Ico 1 k, (c₀ ^ y - 1)) • z - (W.γD T W.gam xk - xk) with hR
    have hrP := (Submodule.mem_inf.mp hr).1
    have hrL := (Submodule.mem_inf.mp hr).2
    have hrP' := hrP
    simp only [PiNS, Formalism.MainNotions.DeltaInvariantLattices.aN, Submodule.mem_inf, Submodule.restrictScalars_mem,
      Submodule.mem_map] at hrP'
    obtain ⟨⟨r', hr'N, hr'eq⟩, hrΔ⟩ := hrP'
    have hr'eq' : π' ^ k • r' = R := hr'eq
    have hΔr := (mem_DelS_iff_forall_gammaD_fixed W T).mp hrΔ
    have hr'Δ : r' ∈ W.NΔ T := by
      show r' ∈ W.N T ∧ ∀ δ ∈ W.DelF, W.γD T δ r' = r'
      refine ⟨hr'N, fun δ hδ => ?_⟩
      have h2 : W.γA δ (π' ^ k) = π' ^ k := by rw [map_pow, hπΔ δ hδ]
      have h1 : π' ^ k • (W.γD T δ r' - r') = 0 := by
        rw [smul_sub, ← h2, ← gradNPf_γD_smul, h2, hr'eq', hΔr δ hδ, sub_self]
      have hu' : IsUnit (algebraMap (LetA O n) W.EE (π' ^ k)) := by
        rw [map_pow]; exact hu.pow k
      exact sub_eq_zero.mp (gradNPf_tf W T (π' ^ k) hu' _ h1)
    obtain ⟨w, hwN, hw⟩ := exists_gam_pow_smul_sub_eq W T π' f t c₀ hf ht hγN k r' hr'Δ
    rw [hr'eq'] at hw
    have hxkP := (Submodule.mem_inf.mp hxk).1
    have hxkL := (Submodule.mem_inf.mp hxk).2
    have hzP := (Submodule.mem_inf.mp hz).1
    have hzL := (Submodule.mem_inf.mp hz).2
    have hRP1 : R ∈ PiNS W T π' 1 := gradNPf_PiNS_anti W T π' hk hrP
    have hxP : (c₀ ^ k - 1) • xk + R ∈ PiNS W T π' 1 :=
      Submodule.add_mem _ (Submodule.smul_mem _ _ hxkP) hRP1
    have hxL : (c₀ ^ k - 1) • xk + R ∈ letS W T c :=
      Submodule.add_mem _ (Submodule.smul_mem _ _ hxkL) hrL
    refine ⟨(c₀ ^ k - 1) • xk + R, Submodule.mem_inf.mpr ⟨hxP, hxL⟩, ?_⟩
    have hPz : (∏ y ∈ Finset.Ico 1 k, (c₀ ^ y - 1)) • z = R + (W.γD T W.gam xk - xk) := by
      rw [hR]; abel
    have hE : (∏ y ∈ Finset.Ico 1 (k + 1), (c₀ ^ y - 1)) • z -
        (W.γD T W.gam ((c₀ ^ k - 1) • xk + R) - ((c₀ ^ k - 1) • xk + R)) = π' ^ (k + 1) • (-w) := by
      rw [Finset.prod_Ico_succ_top hk, mul_comm, mul_smul, hPz, map_add (f := _), map_smul, smul_neg, ← hw]
      simp only [smul_add, smul_sub]
      abel
    have hγxP : W.γD T W.gam ((c₀ ^ k - 1) • xk + R) ∈ DelS W T :=
      gradNPf_DelS_γ W T W.gam (gradNPf_PiNS_DelS W T π' 1 hxP)
    have hγxL := gradNPf_letS_γ W T W.gam c hxL
    have hzΔ := gradNPf_PiNS_DelS W T π' 1 hzP
    have hxΔ := gradNPf_PiNS_DelS W T π' 1 hxP
    rw [PiNS]
    refine Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
    · rw [hE]
      exact (Submodule.restrictScalars_mem _ _ _).mpr
        (Submodule.mem_map.mpr ⟨-w, Submodule.neg_mem _ hwN, rfl⟩)
    · exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hzΔ) (Submodule.sub_mem _ hγxP hxΔ)
    · exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hzL) (Submodule.sub_mem _ hγxL hxL)

theorem gradNPf_local (π' f t : LetA O n) (c₀ : O) (hf : W.γA W.gam π' = π' * f)
    (ht : f - algebraMap O (LetA O n) c₀ = π' * t)
    (hu : IsUnit (algebraMap (LetA O n) W.EE π'))
    (hπΔ : ∀ δ ∈ W.DelF, W.γA δ π' = π')
    (hγN : ∀ x ∈ W.NΔ T, ∃ d ∈ W.N T, W.γD T W.gam x - x = π' • d)
    (hK : W.gamK = W.gam) (σ M : ℕ) (hM : 1 ≤ M) (a : O)
    (ha : ((PD.p : ℕ) : O) ^ σ = a * ∏ y ∈ Finset.Ico 1 M, (c₀ ^ y - 1)) :
    GradN W T π' σ M := by
  intro c z hz
  obtain ⟨x, hx, hr⟩ := gradNPf_coker W T π' f t c₀ hf ht hu hπΔ hγN c z hz M hM
  refine ⟨a • x, Submodule.smul_mem _ _ hx, ?_⟩
  have e : ((PD.p : ℕ) : O) ^ σ • z - (W.γD T W.gamK (a • x) - a • x) =
      a • ((∏ y ∈ Finset.Ico 1 M, (c₀ ^ y - 1)) • z - (W.γD T W.gam x - x)) := by
    rw [hK, ha, map_smul, mul_smul, smul_sub, smul_sub]
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.mem_inf.1 hr).1

theorem gradNPf_small (π' : LetA O n) (σ M : ℕ) (hM : M ≤ 1) : GradN W T π' σ M := by
  unfold GradN
  intro c z hz
  refine ⟨0, Submodule.zero_mem _, ?_⟩
  simp only [map_zero, sub_zero]
  exact gradNPf_PiNS_anti W T π' hM (Submodule.smul_mem _ _ (Submodule.mem_inf.mp hz).1)

end Local

end Formalism.MainNotions.N.Ln34

end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ExtPfMultVEqZero
noncomputable section

namespace Formalism.MainNotions.N.Ln34.ExtPf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

section Gen

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem extPf_filV_succ_le (a : ℤ) :
    FilV PD (LL := LL) (V := V) (a + 1) ≤ FilV PD (LL := LL) (V := V) a := by
  have hle : (PD.Fil (a + 1)).restrictScalars Qp ≤ (PD.Fil a).restrictScalars Qp :=
    fun x hx => PD.Fil_anti a hx
  unfold FilV
  rintro _ ⟨t, rfl⟩
  refine ⟨AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (Submodule.inclusion hle) t, ?_⟩
  rw [← LinearMap.comp_apply, ← AlgebraTensorModule.map_comp]
  rfl

theorem extPf_fildR_succ_le (τ : K →ₐ[Qp] LL) (a : ℤ) :
    FildR PD ρ τ (a + 1) ≤ FildR PD ρ τ a :=
  inf_le_inf_left _ (extPf_filV_succ_le PD (LL := LL) (V := V) a)

theorem extPf_multV_eq_zero (τ : K →ₐ[Qp] LL) (a : ℤ) (h : ¬ IsJumpV PD ρ τ a) :
    multV PD ρ τ a = 0 := by
  unfold IsJumpV at h
  unfold multV
  rw [not_not.1 h, sub_self]

theorem extPf_not_jump (τ : K →ₐ[Qp] LL) (hfin : Module.Finite LL ↥(DdRE PD ρ τ)) (a : ℤ)
    (h : multV PD ρ τ a = 0) : ¬ IsJumpV PD ρ τ a := by
  intro hj
  unfold IsJumpV at hj
  apply hj
  haveI : FiniteDimensional LL ↥(DdRE PD ρ τ) := hfin
  have hsub : FildR PD ρ τ a ≤ DdRE PD ρ τ := by
    unfold FildR
    exact inf_le_left
  haveI : FiniteDimensional LL ↥(FildR PD ρ τ a) := Submodule.finiteDimensional_of_le hsub
  apply Submodule.eq_of_le_of_finrank_eq (extPf_fildR_succ_le PD ρ τ a)
  unfold multV at h
  omega

end Gen

theorem ext_pf : Formalism.MainNotions.N.Ln34.ExtStep := by
  intro D HW F Cm CA CB CK hA l _ _ K LL hG T h' hh' hc hj κ hκ
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h8, h11, -⟩ := hA
  have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  obtain ⟨h1, hz⟩ := Formalism.MainNotions.LiftingTheory.lone_HOne0 ((HW l).W K 1 LL hG)
  obtain ⟨Tp, ι, π, hcp, hext⟩ := Formalism.MainNotions.LiftingTheory.lext_HExt_D D HW F l K 1 LL hG h1 T κ hc hκ
  refine ⟨Tp, ι, π, hext, hcp, h1, fun τ a ha => ?_⟩
  by_contra hout
  obtain ⟨-, -, hadd⟩ := h11 l K LL T Tp ((HW l).W K 1 LL hG).one ι π hext.1 hcp
  have hfin := ((h8 l K LL Tp).2 τ).1
  have h0 : multV ((D.loc l).PD K) T.ρ τ a = 0 :=
    extPf_multV_eq_zero _ _ τ a fun hT => hout (hj τ a hT)
  have h2 : multV ((D.loc l).PD K) ((HW l).W K 1 LL hG).one.ρ τ a = 0 := by
    refine extPf_multV_eq_zero _ _ τ a fun hO => hout ?_
    rw [hz τ a hO]
    exact Set.mem_Icc.2 ⟨by omega, by omega⟩
  exact extPf_not_jump _ _ τ hfin a (by have := hadd τ a; omega) ha

end Formalism.MainNotions.N.Ln34.ExtPf

end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.GamPiPf
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem gampi_delta {x : W.DD T} (hx : ∀ δ ∈ W.DelF, W.γD T δ x = x) :
    ∀ δ ∈ W.DelF, W.γD T δ (W.γD T W.gamK x - x) = W.γD T W.gamK x - x := by
  intro δ hδ
  rw [map_sub, ← W.γD_mul, mul_comm, W.γD_mul, hx δ hδ]

theorem gampi_letter (c : ZMod n) {x : W.DD T} (hx : x ∈ letS W T c) :
    W.γD T W.gamK x - x ∈ letS W T c := by
  have hl : letγ (W.γ₀ W.gamK) (letE c : LetA O n) = letE c := by
    funext j
    show W.γ₀ W.gamK ((letE c : LetA O n) j) = (letE c : LetA O n) j
    rcases eq_or_ne j c with rfl | h
    · simp [letE]
    · simp [letE, Pi.single_apply, h]
  have key : ∀ y : W.DD T, W.γD T W.gamK ((letE c : LetA O n) • y) = (letE c : LetA O n) • W.γD T W.gamK y := by
    intro y
    rw [← algebraMap_smul W.EE (letE c : LetA O n) y, W.γD_smul, W.γE_ext, hl, algebraMap_smul]
  unfold letS at hx ⊢
  rw [LinearMap.mem_ker] at hx ⊢
  simp only [LinearMap.restrictScalars_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply] at hx ⊢
  rw [smul_sub, ← key, sub_eq_zero.1 hx, sub_self]

theorem gampi_local (π' π'₀ u : LetA O n) (hu : π'₀ = u * π')
    (hm : ∀ x ∈ W.NΔ T, ∃ x' ∈ W.NΔ T, W.γD T W.gamK x - x = π'₀ • x') :
    GamPi W T π' := by
  intro c x hx
  unfold NcS at hx
  rw [Submodule.mem_inf, Submodule.mem_inf] at hx
  obtain ⟨⟨hxN, hxD⟩, hxL⟩ := hx
  rw [Submodule.restrictScalars_mem] at hxN
  have hxfix : ∀ δ ∈ W.DelF, W.γD T δ x = x := by
    intro δ hδ
    unfold DelS at hxD
    have h1 := (Submodule.mem_iInf _).1 hxD δ
    have h2 := (Submodule.mem_iInf _).1 h1 hδ
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at h2
    exact h2
  have hxΔ : x ∈ W.NΔ T := show x ∈ W.N T ∧ ∀ δ ∈ W.DelF, W.γD T δ x = x from ⟨hxN, hxfix⟩
  obtain ⟨x', hx'mem, hx'⟩ := hm x hxΔ
  have hx'N : x' ∈ W.N T := (show x' ∈ W.N T ∧ ∀ δ ∈ W.DelF, W.γD T δ x' = x' from hx'mem).1
  rw [Submodule.mem_inf]
  refine ⟨?_, gampi_letter W T c hxL⟩
  unfold PiNS
  rw [Submodule.mem_inf]
  refine ⟨?_, ?_⟩
  · rw [Submodule.restrictScalars_mem]
    unfold Formalism.MainNotions.DeltaInvariantLattices.aN
    refine Submodule.mem_map.2 ⟨u • x', (W.N T).smul_mem u hx'N, ?_⟩
    unfold Formalism.MainNotions.DeltaInvariantLattices.smulA
    rw [LinearMap.smul_apply, LinearMap.id_apply, hx', hu, pow_one, smul_smul, mul_comm]
  · unfold DelS
    rw [Submodule.mem_iInf]
    intro δ
    rw [Submodule.mem_iInf]
    intro hδ
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
    exact gampi_delta W T hxfix δ hδ

end Local

theorem gamPiCondition : GamPiStep := by
  intro D HW F Cm CA CB CK hA l _ hl K LL hG π' E hp9 T hcrys
  have hT1 := hA.1 l K 1 LL hG
  have hP9 := hT1.2.2.2.2.2.2.2.2.1
  have hs1 : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hp2 : ((D.loc l).PD K).p ≠ 2 := by rw [hp]; exact hl
  obtain ⟨-, ⟨π₁, E₁, hr₁, hm₁⟩, -⟩ := hP9 T hcrys hs1 hp2
  obtain ⟨w₁, hw₁⟩ := hr₁.2.2.1
  obtain ⟨w, hw⟩ := hp9.2.2.1
  have hgam : ((HW l).W K 1 LL hG).gamK = ((HW l).W K 1 LL hG).gam :=
    ((HW l).W K 1 LL hG).gamK_eq_one hs1 hp2
  refine gampi_local _ T π' π₁ ((w₁ * w⁻¹ : (LetA _ _)ˣ) : LetA _ _) ?_ ?_
  · rw [hw₁, hw, hp, Units.val_mul, mul_assoc, Units.inv_mul_cancel_left]
  · intro x hx
    obtain ⟨x', hx', h⟩ := hm₁.2 x hx
    exact ⟨x', hx', by rw [hgam]; exact h⟩

end Formalism.MainNotions.N.Ln34

end
end
