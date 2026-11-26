module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsCrystallineExtensionIffMemFiniteCocycles
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrdinarySelmerVanishesOfDualVanishes
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StrictVanishingDualOfLiterature
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalDualityCharacterOrthogonalClasses

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Foundations.CohomologyInputsOfUnitary
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV
open scoped Matrix

namespace GlobalTheory.Ord2.Test

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem eps_eq (s : G ℚ Ω) : eps l s = algebraMap ℤ_[l] (Qbar l) (cycZ ℚ Ω l s : ℤ_[l]) := rfl

theorem cycZ_ine [IsAlgClosure ℚ Ω] {v : Pl} (hl : ((l : ℕ) : 𝓞 ℚ) ∉ v.asIdeal) {A : ValuationSubring Ω}
    (hA : IsPlaceOver A v) {σ : G ℚ Ω} (hσ : σ ∈ Ine (F := ℚ) A) : cycZ ℚ Ω l σ = 1 := by
  refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
  rw [cycZ_toZModPow_eq hl hA (q := 1) (fun x hx => by simpa using hσ.2 x hx) n]
  simp

end GlobalTheory.Ord2.Test

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrdinarySelmerDualVanishesOfStrict
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrdinarySelmerDualVanishesOfStrict
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.Upgrade

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem mat_mul (W : R2 Ω l) (s t : G ℚ Ω) : mat W (s * t) = mat W s * mat W t := by simp [mat]

theorem mat_one (W : R2 Ω l) : mat W 1 = 1 := by simp [mat]

theorem det_upper (W : R2 Ω l) {s : G ℚ Ω} (h : mat W s 1 0 = 0) : (mat W s).det = mat W s 0 0 * mat W s 1 1 := by
  rw [Matrix.det_fin_two, h]; ring

theorem galoisRepRankTwoTateDual_matrix_apply (W : R2 Ω l) (h : dt W ^ 2 = 1) (s : G ℚ Ω) (i j : Fin 2) :
    mat (dual1 W) s i j = eps l s * (mat W s).det * mat W s i j := by
  rw [CupCob.mat_dual1 W h, Matrix.smul_apply, smul_eq_mul]

theorem continuous_galoisRepRankTwoTateDual (W : R2 Ω l) (h : dt W ^ 2 = 1) (hc : Continuous W) : Continuous (dual1 W) := by
  have hm : Continuous fun s => mat W s := Units.continuous_val.comp hc
  have hf : Continuous fun s => mat (dual1 W) s := by
    simp_rw [CupCob.mat_dual1 W h]
    exact (CupCob.eps_cont.mul hm.matrix_det).smul hm
  rw [Units.continuous_iff]
  constructor
  · exact hf
  · have e : ∀ s, (((dual1 W s)⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) = mat (dual1 W) s⁻¹ := by
      intro s; simp only [mat, map_inv]
    simp_rw [e]
    exact hf.comp continuous_inv

theorem dt_sq_apply (W : R2 Ω l) (h : dt W ^ 2 = 1) (s : G ℚ Ω) : (mat W s).det ^ 2 = 1 := CupCob.det_sq W h s

theorem nontriv (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) [IsAlgClosure ℚ Ω] (W : R2 Ω l) (hW : Nf e S A W) :
    (∃ s ∈ Dec (F := ℚ) A, mat W s 1 1 ≠ 1) ∧ (∃ s ∈ Dec (F := ℚ) A, mat (dual1 W) s 0 0 ≠ 1) := by
  set D := Dec (F := ℚ) A with hDdef
  have hup : ∀ s ∈ D, mat W s 1 0 = 0 := hW.upper
  have h00 : ∀ s t, t ∈ D → mat W (s * t) 0 0 = mat W s 0 0 * mat W t 0 0 := by
    intro s t ht; rw [mat_mul, Matrix.mul_apply, Fin.sum_univ_two, hup t ht]; ring
  have hv : A.valuation (l : Ω) < 1 := by
    obtain ⟨v, hA, hlv⟩ := hW.atL
    simpa using (hA _).2 hlv
  obtain ⟨u0, hu0⟩ := GrOfKill.exists_unit_one_add l
  obtain ⟨t, htI, htu⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hv u0
  have heps : eps l t = ((1 + l : ℕ) : Qbar l) := by
    simp [eps, cycBar, htu, hu0]
  obtain ⟨m, hm1, hm⟩ := hW.wt
  have htD : t ∈ D := Ine_le_Dec A htI
  have hpow00 : ∀ s ∈ D, ∀ n : ℕ, mat W (s ^ n) 0 0 = mat W s 0 0 ^ n := by
    intro s hs n
    induction n with
    | zero => simp [mat_one]
    | succ n ih => rw [pow_succ, h00 _ _ hs, ih, pow_succ]
  set T := t ^ (2 * m) with hTdef
  have hTD : T ∈ D := D.pow_mem htD _
  set Nq : ℕ := (1 + l) ^ (2 * (e * m)) with hNq
  have hT00 : mat W T 0 0 = (Nq : Qbar l) := by
    rw [hTdef, hpow00 t htD, pow_mul', hm t htI, heps, hNq]; push_cast; ring
  have hdT : (mat W T).det = 1 := by
    have h2 : dt W t ^ 2 = 1 := by
      have := congrArg (fun f => f t) hW.det2
      simpa using this
    have h3 : dt W T = 1 := by rw [hTdef, map_pow, pow_mul, h2, one_pow]
    have h4 : ((dt W T : (Qbar l)ˣ) : Qbar l) = (mat W T).det := rfl
    rw [← h4, h3, Units.val_one]
  have hepsT : eps l T = (((1 + l) ^ (2 * m) : ℕ) : Qbar l) := by
    have : eps l T = eps l t ^ (2 * m) := by simp [hTdef, eps]
    rw [this, heps]; push_cast; ring
  have hl1 : 1 < 1 + l := by have := (Fact.out : l.Prime).two_le; omega
  have hNq1 : 1 < Nq := by
    rw [hNq]; exact Nat.one_lt_pow (by have := hW.e_pos; positivity) hl1
  refine ⟨⟨T, hTD, fun h => ?_⟩, ⟨T, hTD, fun h => ?_⟩⟩
  · have h5 : (Nq : Qbar l) * 1 = 1 := by
      have h7 := det_upper W (hup T hTD)
      rw [hdT, hT00, h] at h7
      exact h7.symm
    have h6 : Nq = 1 := by exact_mod_cast (mul_one (Nq : Qbar l)).symm.trans h5
    omega
  · rw [galoisRepRankTwoTateDual_matrix_apply W hW.det2, hdT, hepsT, hT00] at h
    have h6 : (1 + l) ^ (2 * m) * Nq = 1 := by exact_mod_cast (by simpa using h : ((((1 + l) ^ (2 * m) * Nq : ℕ)) : Qbar l) = 1)
    have : 1 < (1 + l) ^ (2 * m) * Nq := one_lt_mul_of_le_of_lt (Nat.one_le_pow _ _ (by omega)) hNq1
    omega

theorem place_unique {v w : Pl} (hv : ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) (hw : ((l : ℕ) : 𝓞 ℚ) ∈ w.asIdeal) : v = w := by
  by_contra hne
  have hne' : v.asIdeal ≠ w.asIdeal := fun h => hne (HeightOneSpectrum.ext h)
  have hmax : v.asIdeal ⊔ w.asIdeal = ⊤ := Ideal.IsMaximal.coprime_of_ne v.isMaximal w.isMaximal hne'
  have hmul : v.asIdeal * w.asIdeal = v.asIdeal ⊓ w.asIdeal := Ideal.mul_eq_inf_of_coprime hmax
  have hle : Ideal.span {((l : ℕ) : 𝓞 ℚ)} ≤ v.asIdeal * w.asIdeal := by
    rw [hmul, Ideal.span_singleton_le_iff_mem]; exact ⟨hv, hw⟩
  have hd := Ideal.absNorm_dvd_absNorm_of_le hle
  rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank, Module.finrank_self, pow_one, map_mul] at hd
  have h1 := NumberField.HeightOneSpectrum.one_lt_absNorm v
  have h2 := NumberField.HeightOneSpectrum.one_lt_absNorm w
  have hp : l.Prime := Fact.out
  have ha : Ideal.absNorm v.asIdeal = l :=
    (hp.eq_one_or_self_of_dvd _ (dvd_of_mul_right_dvd hd)).resolve_left (by omega)
  have hb : Ideal.absNorm w.asIdeal = l :=
    (hp.eq_one_or_self_of_dvd _ (dvd_of_mul_left_dvd hd)).resolve_left (by omega)
  rw [ha, hb] at hd
  have := Nat.le_of_dvd hp.pos hd
  have := hp.two_le
  nlinarith

theorem coc_eq (V : R2 Ω l) {a : G ℚ Ω → Fin 2 → Qbar l} (ha : a ∈ Z1 (Loc.colRep V)) (s t : G ℚ Ω) :
    a (s * t) = a s + mat V s *ᵥ a t := by
  rw [ha.2 s t]; rfl

theorem isIntegralCocycleOneModPow_of_integral_cocycle (c : Coef l) (n : ℕ) (V : R2 Ω l) (H : Subgroup (G ℚ Ω)) {a : G ℚ Ω → Fin 2 → Qbar l}
    (ha : a ∈ Z1 (Loc.colRep V)) (hint : ∀ s i, a s i ∈ c.O) : Coc1 c n V H a :=
  ⟨ha.1.continuousOn, hint, fun s _ t _ i => by rw [coc_eq V ha s t]; simp [Cg]⟩

theorem isIntegralCoboundaryOneModPow_of_integral_vector (c : Coef l) (n : ℕ) (V : R2 Ω l) (H : Subgroup (G ℚ Ω)) {a : G ℚ Ω → Fin 2 → Qbar l}
    (h : ∃ x : Fin 2 → Qbar l, (∀ i, x i ∈ c.O) ∧ ∀ s ∈ H, a s = mat V s *ᵥ x - x) : Cob1 c n V H a := by
  obtain ⟨x, hx, h⟩ := h
  exact ⟨x, hx, fun s hs i => by rw [h s hs]; simp [Cg]⟩

theorem kummerTower_coboundaryTwo_congr {c : Coef l} {n : ℕ} {H : Subgroup (G ℚ Ω)} {ξ ξ' : G ℚ Ω → G ℚ Ω → Qbar l} (h : Cob2 c n H ξ)
    (e : ∀ s ∈ H, ∀ t ∈ H, ξ s t = ξ' s t) : Cob2 c n H ξ' := by
  obtain ⟨u, hu, hui, hc⟩ := h
  exact ⟨u, hu, hui, fun s hs t ht => by rw [← e s hs t ht]; exact hc s hs t ht⟩

theorem amitsur_d0_apply (V : R2 Ω l) (v : Fin 2 → Qbar l) (s : G ℚ Ω) :
    d0 (Loc.colRep V) v s = mat V s *ᵥ v - v := rfl

theorem commAlgFunctorCoboundaryZero_mem_cocyclesOne (V : R2 Ω l) (hc : Continuous V) (v : Fin 2 → Qbar l) : d0 (Loc.colRep V) v ∈ Z1 (Loc.colRep V) := by
  refine ⟨?_, fun g h => ?_⟩
  · have e : d0 (Loc.colRep V) v = fun s => mat V s *ᵥ v - v := funext fun s => amitsur_d0_apply V v s
    rw [e]
    exact ((Units.continuous_val.comp hc).matrix_mulVec continuous_const).sub continuous_const
  · change d0 (Loc.colRep V) v (g * h) = d0 (Loc.colRep V) v g + mat V g *ᵥ d0 (Loc.colRep V) v h
    rw [amitsur_d0_apply, amitsur_d0_apply, amitsur_d0_apply, mat_mul, ← Matrix.mulVec_mulVec, Matrix.mulVec_sub]
    abel

theorem galoisRepRankTwoTateDual_unramified_outside [IsAlgClosure ℚ Ω] (S : Finset Pl) (W : R2 Ω l) (h : dt W ^ 2 = 1) (hS : ContainsAbove S l)
    (hu : ∀ w, w ∉ S → ∀ B : ValuationSubring Ω, IsPlaceOver B w → Ine (F := ℚ) B ≤ W.ker) :
    ∀ w, w ∉ S → ∀ B : ValuationSubring Ω, IsPlaceOver B w → Ine (F := ℚ) B ≤ (dual1 W).ker := by
  intro w hw B hB s hs
  have h1 : W s = 1 := hu w hw B hB hs
  have h2 : eps l s = 1 := by
    rw [Test.eps_eq, Test.cycZ_ine (fun h' => hw (hS w h')) hB hs]; simp
  rw [MonoidHom.mem_ker]
  refine Units.ext ?_
  change mat (dual1 W) s = 1
  rw [CupCob.mat_dual1 W h, h2]
  simp [mat, h1]

theorem upgrade : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l),
    Nf e S A W → ES W A → StrZero (dual1 W) A → GrZero (dual1 W) A := by
  intro hLit l _ Ω _ _ _ e S A W hW hES hStr z hz hzU hzGr
  obtain ⟨c, y, S', hWc, hy, hyint, hyU, hyGr, -⟩ := hES
  have hdet2 := hW.det2
  have hc := hW.cont
  have hc' : Continuous (dual1 W) := continuous_galoisRepRankTwoTateDual W hdet2 hc
  have hup : ∀ s ∈ Dec (F := ℚ) A, mat W s 1 0 = 0 := hW.upper
  have hup' : ∀ s ∈ Dec (F := ℚ) A, mat (dual1 W) s 1 0 = 0 := fun s hs => by
    rw [galoisRepRankTwoTateDual_matrix_apply W hdet2, hup s hs, mul_zero]

  obtain ⟨c1, j, hc1, hyint1, hyunr1, -, -⟩ := GlobalTheory.T.galois_cocycle_integral_after_scaling l Ω S W c y hc hWc hW.unr hy hyU A
  have hWc1 : ∀ s i j, mat W s i j ∈ c1.O := fun s i j => hc1 (hWc s i j)
  have hW'c1 : ∀ s i j, mat (dual1 W) s i j ∈ c1.O := CupCob.dual_representation_integral c1 W hdet2 hWc1
  obtain ⟨c2, k, hc2, hzint2, hzunr2, -, hzgr2⟩ :=
    GlobalTheory.T.galois_cocycle_integral_after_scaling l Ω S (dual1 W) c1 z hc' hW'c1 (galoisRepRankTwoTateDual_unramified_outside S W hdet2 hW.above hW.unr) hz hzU A
  obtain ⟨x, hxO, hx⟩ := hzgr2 hzGr
  have hWc2 : ∀ s i j, mat W s i j ∈ c2.O := fun s i j => hc2 (hWc1 s i j)
  have hW'c2 : ∀ s i j, mat (dual1 W) s i j ∈ c2.O := CupCob.dual_representation_integral c2 W hdet2 hWc2
  have hL : ((l : ℕ) : Qbar l) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  set L : Qbar l := ((l : ℕ) : Qbar l) with hLdef
  set v0 : Fin 2 → Qbar l := ![0, x] with hv0
  have hv0O : ∀ i, v0 i ∈ c2.O := fun i => by
    fin_cases i
    · simpa [hv0] using c2.O.zero_mem
    · simpa [hv0] using hxO
  set y1 : G ℚ Ω → Fin 2 → Qbar l := L ^ j • y with hy1
  set z1 : G ℚ Ω → Fin 2 → Qbar l := L ^ k • z - d0 (Loc.colRep (dual1 W)) v0 with hz1
  have hy1s : ∀ s i, y1 s i = L ^ j * y s i := fun s i => rfl
  have hz1s : ∀ s, z1 s = L ^ k • z s - (mat (dual1 W) s *ᵥ v0 - v0) := fun s => rfl
  have hy1Z : y1 ∈ Z1 (Loc.colRep W) := Submodule.smul_mem _ _ hy
  have hz1Z : z1 ∈ Z1 (Loc.colRep (dual1 W)) :=
    Submodule.sub_mem _ (Submodule.smul_mem _ _ hz) (commAlgFunctorCoboundaryZero_mem_cocyclesOne (dual1 W) hc' v0)
  have hy1int : ∀ s i, y1 s i ∈ c2.O := fun s i => by rw [hy1s]; exact hc2 (hyint1 s i)
  have hz1int : ∀ s i, z1 s i ∈ c2.O := fun s i => by
    rw [hz1s, Pi.sub_apply, Pi.sub_apply]
    exact sub_mem (hzint2 s i) (sub_mem (CupCob.mulVec_mem c2 _ _ (hW'c2 s) hv0O i) (hv0O i))
  have hz1D : ∀ s ∈ Dec (F := ℚ) A, z1 s 1 = 0 := fun s hs => by
    rw [hz1s]
    have := hx s hs
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hv0, hup' s hs] at this ⊢
    rw [this]; ring
  have hy1unr : ∀ q : Pl, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∀ B : ValuationSubring Ω, IsPlaceOver B q →
      ∃ x : Fin 2 → Qbar l, (∀ i, x i ∈ c2.O) ∧ ∀ s ∈ Ine (F := ℚ) B, y1 s = mat W s *ᵥ x - x := by
    intro q hq B hB
    obtain ⟨x', hx'O, hx'⟩ := hyunr1 q hq B hB
    exact ⟨x', fun i => hc2 (hx'O i), fun s hs => hx' s hs⟩
  have hz1unr : ∀ q : Pl, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∀ B : ValuationSubring Ω, IsPlaceOver B q →
      ∃ x : Fin 2 → Qbar l, (∀ i, x i ∈ c2.O) ∧ ∀ s ∈ Ine (F := ℚ) B, z1 s = mat (dual1 W) s *ᵥ x - x := by
    intro q hq B hB
    obtain ⟨x', hx'O, hx'⟩ := hzunr2 q hq B hB
    refine ⟨x' - v0, fun i => sub_mem (hx'O i) (hv0O i), fun s hs => ?_⟩
    rw [hz1s, hx' s hs, Matrix.mulVec_sub]
    abel
  have hy1U : Unr W y1 := fun w hw => by
    obtain ⟨B, hB⟩ := exists_isPlaceOver Ω w
    obtain ⟨x', -, hx'⟩ := hy1unr w hw B hB
    exact ⟨B, hB, x', hx'⟩
  have hz1U : Unr (dual1 W) z1 := fun w hw => by
    obtain ⟨B, hB⟩ := exists_isPlaceOver Ω w
    obtain ⟨x', -, hx'⟩ := hz1unr w hw B hB
    exact ⟨B, hB, x', hx'⟩

  obtain ⟨p, hAp, hlp⟩ := hW.atL
  have hpS : p ∈ S := hW.above p hlp
  have hCobA : ∀ n, Cob2 c2 n (Dec (F := ℚ) A) (cup W y1 z1) := fun n => by
    refine GlobalTheory.T.integralTwoCocycle_reciprocity_trivial_at_last_place hLit l Ω c2 n S (cup W y1 z1) p hW.l_odd hW.above
      (GlobalTheory.T.cupProductDualTwist_isTwoCocycle_unramified l Ω c2 n S W y1 z1 hc hWc2 hdet2 hW.above hW.unr hy1Z hz1Z hy1int hz1int hy1U hz1U) hpS ?_ A hAp
    intro v _ hvp
    have hlv : ((l : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := fun h => hvp (place_unique h hlp)
    obtain ⟨B, hB⟩ := exists_isPlaceOver Ω v
    exact ⟨B, hB, GlobalTheory.T.cupProduct_unramifiedClasses_vanishes hLit l Ω c2 n W v B y1 z1 hc hWc2 hdet2 hB hlv
      (isIntegralCocycleOneModPow_of_integral_cocycle c2 n W _ hy1Z hy1int) (isIntegralCocycleOneModPow_of_integral_cocycle c2 n (dual1 W) _ hz1Z hz1int)
      (isIntegralCoboundaryOneModPow_of_integral_vector c2 n W _ (hy1unr v hlv B hB)) (isIntegralCoboundaryOneModPow_of_integral_vector c2 n (dual1 W) _ (hz1unr v hlv B hB))⟩

  have hm : Continuous fun s => mat W s := Units.continuous_val.comp hc
  have hm' : Continuous fun s => mat (dual1 W) s := Units.continuous_val.comp hc'
  have hloc := GlobalTheory.T.local_duality_character_orthogonal_classes hLit l Ω c2 A (fun s => mat W s 1 1) (fun s => mat (dual1 W) s 0 0) (fun s => z1 s 0)
    (fun s => -y1 s 1) hW.atL (hm.matrix_elem 1 1).continuousOn (hm'.matrix_elem 0 0).continuousOn
    ((continuous_apply 0).comp hz1Z.1).continuousOn ((continuous_apply 1).comp hy1Z.1).neg.continuousOn
    (fun s hs => ⟨hWc2 s 1 1, hW'c2 s 0 0, hz1int s 0, neg_mem (hy1int s 1), by
      rw [galoisRepRankTwoTateDual_matrix_apply W hdet2, det_upper W (hup s hs)]
      have h := dt_sq_apply W hdet2 s
      rw [det_upper W (hup s hs)] at h
      linear_combination (eps l s) * h⟩)
    (fun s hs t ht => ⟨by rw [mat_mul, Matrix.mul_apply, Fin.sum_univ_two, hup s hs]; ring,
      by rw [mat_mul, Matrix.mul_apply, Fin.sum_univ_two, hup' t ht]; ring,
      by
        rw [coc_eq W hy1Z s t]
        simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hup s hs]; ring,
      by
        rw [coc_eq (dual1 W) hz1Z s t]
        simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hz1D t ht]⟩)
    (nontriv e S A W hW).1 (nontriv e S A W hW).2
    (fun n => kummerTower_coboundaryTwo_congr (hCobA n) fun s hs t ht => by
      simp only [cup, om, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hz1D t ht, hup' s hs]; ring)
  rcases hloc with ⟨x', hx'⟩ | ⟨x', hx'⟩
  · exfalso
    refine hyGr ⟨-x' / L ^ j, fun s hs => ?_⟩
    have h := hx' s hs
    simp only [hy1s] at h
    have hLj : L ^ j ≠ 0 := pow_ne_zero _ hL
    field_simp
    linear_combination -h
  · have hTriv : Triv (dual1 W) A z1 := ⟨![x', 0], fun s hs => by
      ext i
      fin_cases i
      · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hx' s hs]
      · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hup' s hs, hz1D s hs]⟩
    have hB := hStr z1 hz1Z hz1U hTriv
    have hLk : L ^ k ≠ 0 := pow_ne_zero _ hL
    have e : z = (L ^ k)⁻¹ • (z1 + d0 (Loc.colRep (dual1 W)) v0) := by
      rw [hz1, sub_add_cancel, smul_smul, inv_mul_cancel₀ hLk, one_smul]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.add_mem _ hB (LinearMap.mem_range_self _ _))

end GlobalTheory.Ord2.Upgrade

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrdinarySelmerDualVanishesOfStrictStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ordinarySelmer_dual_vanishes_of_strict : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ES W A → StrZero (dual1 W) A → GrZero (dual1 W) A := by
  first | exact @GlobalTheory.Ord2.Upgrade.upgrade | exact GlobalTheory.Ord2.Upgrade.upgrade | (intros; apply GlobalTheory.Ord2.Upgrade.upgrade <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.BlochKatoCocycleUnramifiedAndGreenbergOrdinary
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasWeightNegOfCyclotomicPowOnInertia
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasWeightNegOfCyclotomicPowOnInertia
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Matrix

namespace GlobalTheory

theorem hasWeight_neg_of_pow_cyc_inertia : ∀ (l : ℕ) [Fact l.Prime] (κ : GQ l →* (Qbar l)ˣ),
    Continuous (fun σ => (κ σ : Qbar l)) → ∀ (e m : ℕ), 1 ≤ m →
    (∀ σ ∈ Loc.Iq l, (κ σ * Loc.cycA l l (Qbar l) σ ^ (e : ℤ)) ^ m = 1) →
    Loc.HasWeight (MonoidHom.id (GQ l)) κ (-(e : ℤ)) := by
  intro l _ κ hκ e m hm h
  have hcyc : Continuous (Loc.cyc l l) := cyclotomicCharacter.continuous l ℚ_[l] (Om l)
  have ha : Continuous (algebraMap ℤ_[l] (Qbar l)) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] (Qbar l)]
    exact (continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val
  have hA : Continuous (fun σ => (Loc.cycA l l (Qbar l) σ : Qbar l)) :=
    Units.continuous_val.comp
      ((Continuous.units_map (algebraMap ℤ_[l] (Qbar l) : ℤ_[l] →* Qbar l) ha).comp hcyc)
  set f : GQ l → Qbar l := fun σ => ((κ σ * Loc.cycA l l (Qbar l) σ ^ (e : ℤ) : (Qbar l)ˣ) : Qbar l) with hf_def
  have hf : Continuous f := by
    have : f = fun σ => (κ σ : Qbar l) * (Loc.cycA l l (Qbar l) σ : Qbar l) ^ e := by
      funext σ
      simp only [hf_def, Units.val_mul, zpow_natCast, Units.val_pow_eq_pow_val]
    rw [this]
    exact hκ.mul (hA.pow e)
  have hf1 : f 1 = 1 := by simp [hf_def]
  have hm0 : 0 < m := hm
  have hfin : ({z : Qbar l | z ^ m = 1} \ {1}).Finite := by
    refine Set.Finite.subset (Multiset.finite_toSet (Polynomial.nthRoots m (1 : Qbar l))) fun z hz => ?_
    exact (Polynomial.mem_nthRoots hm0).2 hz.1
  have ho : IsOpen (f ⁻¹' ({z : Qbar l | z ^ m = 1} \ {1})ᶜ) :=
    hfin.isClosed.isOpen_compl.preimage hf
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one ho
    (fun hx => hx.2 hf1)
  refine ⟨U.toOpenSubgroup.toSubgroup, U.toOpenSubgroup.isOpen, fun g hg hgI => ?_⟩
  have hgI' : g ∈ Loc.Iq l := hgI
  have hpow : f g ^ m = 1 := by
    have := congrArg Units.val (h g hgI')
    simpa [hf_def, Units.val_pow_eq_pow_val] using this
  have hone : f g = 1 := by
    by_contra hne
    exact hU hg ⟨hpow, hne⟩
  have hu : κ g * Loc.cycA l l (Qbar l) g ^ (e : ℤ) = 1 := Units.ext hone
  simp only [MonoidHom.id_apply, zpow_neg]
  exact eq_inv_of_mul_eq_one_left hu

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasWeightNegOfCyclotomicPowOnInertiaStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasWeight_neg_of_cyclotomic_pow_on_inertia : ∀ (l : ℕ) [Fact l.Prime] (κ : GQ l →* (Qbar l)ˣ), Continuous (fun σ => (κ σ : Qbar l)) → ∀ (e m : ℕ), 1 ≤ m → (∀ σ ∈ Loc.Iq l, (κ σ * Loc.cycA l l (Qbar l) σ ^ (e : ℤ)) ^ m = 1) → Loc.HasWeight (MonoidHom.id (GQ l)) κ (-(e : ℤ)) := by
  first | exact @GlobalTheory.hasWeight_neg_of_pow_cyc_inertia | exact GlobalTheory.hasWeight_neg_of_pow_cyc_inertia | (intros; apply GlobalTheory.hasWeight_neg_of_pow_cyc_inertia <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CrystallineClassRestrictDecompositionGroup
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CrystallineClassRestrictDecompositionGroup
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Matrix

namespace GlobalTheory.Ord2

private theorem locEmb_conj {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    {A B : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 k)} (hA : IsPlaceOver A v) (hB : IsPlaceOver B v) :
    ∃ g : G k Ω, (∀ τ ∈ Ine (F := k) B, g⁻¹ * τ * g ∈ Ine (F := k) A) ∧
      (∀ τ ∈ Dec (F := k) B, g⁻¹ * τ * g ∈ Dec (F := k) A) ∧
      ∀ τ ∈ Dec (F := k) A, g * τ * g⁻¹ ∈ Dec (F := k) B := by
  obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (F := k) hA hB
  have h : IsLift (RingEquiv.refl k) g.toRingEquiv := fun x => g.commutes x
  have hm : ∀ x, g.toRingEquiv x ∈ B ↔ x ∈ A := fun x => by
    show g • x ∈ B ↔ _
    rw [← hg]
    exact ValuationSubring.smul_mem_pointwise_smul_iff
  have hm' : ∀ x, g.toRingEquiv.symm x ∈ A ↔ x ∈ B := fun x => by
    rw [← hm, RingEquiv.apply_symm_apply]
  exact ⟨g, fun τ hτ => conjGal_mem_Ine h hm hτ, fun τ hτ => conjGal_mem_Dec h hm hτ,
    fun τ hτ => conjGal_mem_Dec h.symm hm' hτ⟩

theorem bk_locEmb : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (W : R2 Ω l) (A : ValuationSubring Ω), OverL l A → ∀ z ∈ Z1 (Loc.colRep W), IsBK l (Loc.colRep W) z → ∃ ι : GQ l →* G ℚ Ω, Continuous ι ∧ (∀ σ, ι σ ∈ Dec (F := ℚ) A) ∧ (∀ s ∈ Dec (F := ℚ) A, ∃ σ, ι σ = s) ∧ (∀ σ ∈ Loc.Iq l, ι σ ∈ Ine (F := ℚ) A) ∧ (∀ σ, cycZ ℚ Ω l (ι σ) = Loc.cyc l l σ) ∧ (fun σ => z (ι σ)) ∈ Loc.finiteCocycles (MonoidHom.id (GQ l)) ((Loc.colRep W).comp ι) := by
  intro l _ Ω _ iA _ W A hA z hz hb
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  obtain rfl : iA = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  obtain ⟨v, hAv, hv⟩ := hA
  obtain ⟨j, -, -, x, hx⟩ := hb.above (algebraMap ℚ (Om l))
  obtain ⟨i1, i2, -, i4, i5, i6, -⟩ := Loc.iotaFacts j
  have h0 : (fun σ => z (Loc.iota j σ)) ∈
      Loc.finiteCocycles (MonoidHom.id (GQ l)) ((Loc.colRep W).comp (Loc.iota j)) :=
    ⟨⟨hz.1.comp i1.continuous, fun g h => (congrArg z (map_mul _ g h)).trans (hz.2 _ _)⟩, x,
      fun σ => hx ⟨(Loc.iota j σ, σ), fun y => (Loc.iota_spec j σ y).symm⟩⟩
  obtain ⟨g, g1, g2, g3⟩ := locEmb_conj hAv ((i6 v).2 hv)
  let ι : GQ l →* G ℚ Ω := (MulAut.conj g⁻¹).toMonoidHom.comp (Loc.iota j)
  have hι : ∀ σ, ι σ = g⁻¹ * Loc.iota j σ * g := fun σ => by simp [ι]
  have hc : Continuous ι := by
    have : (ι : GQ l → G ℚ Ω) = fun σ => g⁻¹ * Loc.iota j σ * g := funext hι
    rw [this]
    exact (continuous_const.mul i1.continuous).mul continuous_const
  refine ⟨ι, hc, fun σ => ?_, fun s hs => ?_, fun σ hσ => ?_, fun σ => ?_, ?_⟩
  · rw [hι]
    exact g2 _ (by rw [← i2]; exact ⟨σ, rfl⟩)
  · have h1 : g * s * g⁻¹ ∈ Dec (F := ℚ) (Loc.placeJ j) := g3 s hs
    rw [← i2] at h1
    obtain ⟨σ, hσ⟩ := h1
    exact ⟨σ, by rw [hι, hσ]; group⟩
  · rw [hι]
    exact g1 _ (by rw [← i4]; exact ⟨σ, hσ, rfl⟩)
  · rw [hι, map_mul, map_mul, map_inv, mul_comm _ (cycZ ℚ Ω l (Loc.iota j σ)), inv_mul_cancel_right]
    exact DFunLike.congr_fun (i5 l) σ
  · have h1 := Loc.z1fCoef (MonoidHom.id (GQ l)) ((Loc.colRep W).comp (Loc.iota j)) ((Loc.colRep W).comp ι)
      ((Loc.colRep W g⁻¹).restrictScalars ℚ_[l]) (LinearMap.continuous_on_pi (Loc.colRep W g⁻¹))
      (fun σ y => by
        show Loc.colRep W g⁻¹ (Loc.colRep W (Loc.iota j σ) y) = Loc.colRep W (ι σ) (Loc.colRep W g⁻¹ y)
        rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, hι, mul_inv_cancel_right]) _ h0
    have hcob : ∀ σ, Loc.colRep W (ι σ) (z g⁻¹) - z g⁻¹ = z (ι σ * g⁻¹) - z (ι σ) - z g⁻¹ := fun σ => by
      rw [hz.2]; abel
    have h2 : (fun σ => Loc.colRep W (ι σ) (z g⁻¹) - z g⁻¹) ∈
        Loc.finiteCocycles (MonoidHom.id (GQ l)) ((Loc.colRep W).comp ι) := by
      refine ⟨⟨?_, fun a b => ?_⟩, z g⁻¹ ⊗ₜ 1, fun σ => ?_⟩
      · rw [funext hcob]
        exact ((hz.1.comp (hc.mul continuous_const)).sub (hz.1.comp hc)).sub continuous_const
      · show Loc.colRep W (ι (a * b)) (z g⁻¹) - z g⁻¹ = Loc.colRep W (ι a) (z g⁻¹) - z g⁻¹ +
          Loc.colRep W (ι a) (Loc.colRep W (ι b) (z g⁻¹) - z g⁻¹)
        rw [map_mul, map_mul, Module.End.mul_apply, map_sub]; abel
      · simp [Loc.actC, TensorProduct.sub_tmul]
    have h3 := Submodule.sub_mem _ h1 h2
    convert h3 using 1
    funext σ
    show z (ι σ) = Loc.colRep W g⁻¹ (z (Loc.iota j σ)) - (Loc.colRep W (ι σ) (z g⁻¹) - z g⁻¹)
    have e1 := hz.2 g⁻¹ (Loc.iota j σ)
    rw [hcob, hι, mul_inv_cancel_right, e1]
    abel

end GlobalTheory.Ord2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CrystallineClassRestrictDecompositionGroupStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystallineClass_restrict_decompositionGroup : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (W : R2 Ω l) (A : ValuationSubring Ω), OverL l A → ∀ z ∈ Z1 (Loc.colRep W), IsBK l (Loc.colRep W) z → ∃ ι : GQ l →* G ℚ Ω, Continuous ι ∧ (∀ σ, ι σ ∈ Dec (F := ℚ) A) ∧ (∀ s ∈ Dec (F := ℚ) A, ∃ σ, ι σ = s) ∧ (∀ σ ∈ Loc.Iq l, ι σ ∈ Ine (F := ℚ) A) ∧ (∀ σ, cycZ ℚ Ω l (ι σ) = Loc.cyc l l σ) ∧ (fun σ => z (ι σ)) ∈ Loc.finiteCocycles (MonoidHom.id (GQ l)) ((Loc.colRep W).comp ι) := by
  first | exact @GlobalTheory.Ord2.bk_locEmb | exact GlobalTheory.Ord2.bk_locEmb | (intros; apply GlobalTheory.Ord2.bk_locEmb <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CrystallineCocycleCoboundaryOfNegativeWeight
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CrystallineCocycleCoboundaryOfNegativeWeight
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Matrix

noncomputable section

namespace GlobalTheory.NegVan

private theorem fd_adjoin_range (l : ℕ) [Fact l.Prime] {ι : Type} [Finite ι] (f : ι → PadicAlgCl l) :
    FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] (Set.range f)) := by
  haveI : Finite (Set.range f) := (Set.finite_range _).to_subtype
  exact IntermediateField.finiteDimensional_adjoin fun z _ =>
      (Algebra.IsAlgebraic.isAlgebraic z).isIntegral


open TensorProduct in
private theorem desc {l : ℕ} [Fact l.Prime] {H : Type} [Group H] [TopologicalSpace H] (φ : H →* GQ l)
    (κ : H →* (PadicAlgCl l)ˣ) (E₀ : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] E₀]
    (hκ : ∀ g, (κ g : PadicAlgCl l) ∈ E₀) (c : H → PadicAlgCl l) (hc : c ∈ Loc.finiteCocycles φ (Loc.chRep κ)) :
    ∃ (E : IntermediateField ℚ_[l] (PadicAlgCl l)) (_ : FiniteDimensional ℚ_[l] E) (κ' : H →* Eˣ) (c' : H → E),
      (∀ g, ((κ' g : E) : PadicAlgCl l) = κ g) ∧ (∀ g, (c' g : PadicAlgCl l) = c g) ∧ c' ∈ Loc.finiteCocycles φ (Loc.chRep κ') := by
  obtain ⟨⟨hcc, hcoc⟩, x, hx⟩ := hc
  obtain ⟨S, rfl⟩ := TensorProduct.exists_finset x
  obtain ⟨T⟩ := Loc.tiedP l
  haveI : IsDomain (Loc.Bcr l) := GlobalTheory.RegularRing.isDomain_of_tied T (Loc.botExt l)
  haveI := fd_adjoin_range l (fun p : S => p.1.1)
  let E : IntermediateField ℚ_[l] (PadicAlgCl l) := E₀ ⊔ IntermediateField.adjoin ℚ_[l] (Set.range fun p : S => p.1.1)
  have hκE : ∀ g, (κ g : PadicAlgCl l) ∈ E := fun g => (le_sup_left : E₀ ≤ E) (hκ g)
  have hS : ∀ p ∈ S, p.1 ∈ E := fun p hp =>
    (le_sup_right : _ ≤ E) (IntermediateField.subset_adjoin _ _ ⟨⟨p, hp⟩, rfl⟩)
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap E (PadicAlgCl l))
    (LinearMap.ker_eq_bot.2 (algebraMap E (PadicAlgCl l)).injective)
  have hπ1 : ∀ y : E, π (y : PadicAlgCl l) = y := fun y => LinearMap.congr_fun hπ y
  let κ' : H →* Eˣ := MonoidHom.toHomUnits
    { toFun := fun g => ⟨κ g, hκE g⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun g h => Subtype.ext (by simp) }
  have hκ' : ∀ g, ((κ' g : E) : PadicAlgCl l) = κ g := fun g => rfl
  have hπ2 : ∀ g y, π (κ g * y) = κ' g * π y := fun g y => map_smul π (κ' g : E) y
  let f : PadicAlgCl l →ₗ[ℚ_[l]] E := π.restrictScalars ℚ_[l]
  let i : E →ₗ[ℚ_[l]] PadicAlgCl l := E.val.toLinearMap
  have key : ∀ g (y : PadicAlgCl l ⊗[ℚ_[l]] Loc.Bcr l), LinearMap.rTensor (Loc.Bcr l) f (Loc.actC φ (Loc.chRep κ) g y) =
      Loc.actC φ (Loc.chRep κ') g (LinearMap.rTensor (Loc.Bcr l) f y) := by
    intro g y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [Loc.actC, Loc.chRep, f, hπ2]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have key' : ∀ g (y : E ⊗[ℚ_[l]] Loc.Bcr l), LinearMap.rTensor (Loc.Bcr l) i (Loc.actC φ (Loc.chRep κ') g y) =
      Loc.actC φ (Loc.chRep κ) g (LinearMap.rTensor (Loc.Bcr l) i y) := by
    intro g y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [Loc.actC, Loc.chRep, i, hκ']
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  set x := ∑ p ∈ S, p.1 ⊗ₜ[ℚ_[l]] p.2 with hxd
  have hix : LinearMap.rTensor (Loc.Bcr l) i (LinearMap.rTensor (Loc.Bcr l) f x) = x := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hxd, map_sum, map_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [LinearMap.rTensor_tmul, LinearMap.rTensor_tmul]
    congr 1
    exact congrArg Subtype.val (hπ1 ⟨p.1, hS p hp⟩)
  have hx' : ∀ g, f (c g) ⊗ₜ[ℚ_[l]] (1 : Loc.Bcr l) =
      Loc.actC φ (Loc.chRep κ') g (LinearMap.rTensor (Loc.Bcr l) f x) - LinearMap.rTensor (Loc.Bcr l) f x := fun g => by
    rw [← key, ← map_sub, ← hx g, LinearMap.rTensor_tmul]
  have hcE : ∀ g, ((f (c g) : E) : PadicAlgCl l) = c g := fun g => by
    have h1 := congrArg (LinearMap.rTensor (Loc.Bcr l) i) (hx' g)
    rw [map_sub, key', hix, ← hx g, LinearMap.rTensor_tmul] at h1
    exact Algebra.TensorProduct.includeLeft_injective (R := ℚ_[l]) (S := ℚ_[l]) (B := Loc.Bcr l)
      (algebraMap ℚ_[l] (Loc.Bcr l)).injective h1
  refine ⟨E, inferInstance, κ', fun g => f (c g), hκ', hcE, ⟨?_, fun g h => ?_⟩, _, hx'⟩
  · exact continuous_induced_rng.2 (hcc.congr fun g => (hcE g).symm)
  · have := hcoc g h
    simp only [Loc.chRep] at this ⊢
    simp [this, f, hπ2]

private theorem coef_finext {l : ℕ} [Fact l.Prime] (c : Coef l) :
    ∃ K : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] K ∧ ∀ x ∈ c.O, x ∈ K := by
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top (R := ℤ_[l]) (M := c.O))
  refine ⟨_, fd_adjoin_range l (fun q : s => ((q : c.O) : PadicAlgCl l)), fun x hx => ?_⟩
  let K := IntermediateField.adjoin ℚ_[l] (Set.range fun q : s => ((q : c.O) : PadicAlgCl l))
  let M : Submodule ℤ_[l] (PadicAlgCl l) := (K.toSubalgebra.restrictScalars ℤ_[l]).toSubmodule
  have hmem : (⟨x, hx⟩ : c.O) ∈ Submodule.span ℤ_[l] (s : Set c.O) := hs ▸ Submodule.mem_top
  have hle : Submodule.span ℤ_[l] (s : Set c.O) ≤ M.comap c.O.val.toLinearMap := by
    rw [Submodule.span_le]
    intro q hq
    exact IntermediateField.subset_adjoin _ _ ⟨⟨q, hq⟩, rfl⟩
  exact hle hmem

end GlobalTheory.NegVan


open GlobalTheory.NegVan in
theorem GlobalTheory.NegVan.crys_cocycle_coboundary_of_neg_weight :
    Loc.LocalPublishedTheorems → ∀ (l : ℕ) [Fact l.Prime] (κ : GQ l →* (Qbar l)ˣ), Continuous (fun σ => (κ σ : Qbar l)) →
      ∀ c : Coef l, (∀ σ, (κ σ : Qbar l) ∈ c.O) → ∀ w : ℤ, w < 0 → Loc.HasWeight (MonoidHom.id (GQ l)) κ w →
      ∀ f ∈ Loc.finiteCocycles (MonoidHom.id (GQ l)) (Loc.chRep κ), ∃ x, ∀ σ, f σ = (κ σ : Qbar l) * x - x := by
  intro hP l _ κ hκc c hκO w hw hwt f hf
  obtain ⟨K₀, hK₀, hK⟩ := coef_finext c
  obtain ⟨E, _, κ', c', hκ, hc', hf'⟩ := desc (MonoidHom.id (GQ l)) κ K₀ (fun g => hK _ (hκO g)) f hf
  haveI : IsModuleTopology ℚ_[l] E := isModuleTopologyOfFiniteDimensional
  have hw' : Loc.HasWeight (MonoidHom.id (GQ l)) κ' w := by
    obtain ⟨U, hU, hUw⟩ := hwt
    refine ⟨U, hU, fun g hg hI => ?_⟩
    have h := hUw g hg hI
    have hcy : Units.map ((algebraMap E (PadicAlgCl l) : E →+* PadicAlgCl l) : E →* PadicAlgCl l)
        (Loc.cycA l l E g) = Loc.cycA l l (PadicAlgCl l) g := by
      refine Units.ext ?_
      simp only [Units.coe_map, MonoidHom.coe_coe, Loc.cycA, MonoidHom.comp_apply]
      rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] E, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l)]
      rfl
    apply Units.map_injective (f := ((algebraMap E (PadicAlgCl l) : E →+* PadicAlgCl l) : E →* PadicAlgCl l))
      (algebraMap E (PadicAlgCl l)).injective
    rw [map_zpow, MonoidHom.id_apply, hcy, ← MonoidHom.id_apply (GQ l) g, ← h]
    exact Units.ext (hκ g)
  have hz := (Loc.z1fChar hP (MonoidHom.id (GQ l)) Topology.IsOpenEmbedding.id κ'
    (continuous_induced_rng.2 (hκc.congr fun g => (hκ g).symm)) w hw').1 hw
  rw [hz.1, mem_coboundaries1] at hf'
  obtain ⟨m, hm⟩ := hf'
  refine ⟨(m : PadicAlgCl l), fun σ => ?_⟩
  have h4 : c' σ = κ' σ * m - m := hm σ
  rw [← hc' σ, h4, AddSubgroupClass.coe_sub, MulMemClass.coe_mul, hκ]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CrystallineCocycleCoboundaryOfNegativeWeightStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystallineCocycle_coboundary_of_negative_weight : Loc.LocalPublishedTheorems → ∀ (l : ℕ) [Fact l.Prime] (κ : GQ l →* (Qbar l)ˣ), Continuous (fun σ => (κ σ : Qbar l)) → ∀ c : Coef l, (∀ σ, (κ σ : Qbar l) ∈ c.O) → ∀ w : ℤ, w < 0 → Loc.HasWeight (MonoidHom.id (GQ l)) κ w → ∀ f ∈ Loc.finiteCocycles (MonoidHom.id (GQ l)) (Loc.chRep κ), ∃ x, ∀ σ, f σ = (κ σ : Qbar l) * x - x := by
  first | exact @GlobalTheory.NegVan.crys_cocycle_coboundary_of_neg_weight | exact GlobalTheory.NegVan.crys_cocycle_coboundary_of_neg_weight | (intros; apply GlobalTheory.NegVan.crys_cocycle_coboundary_of_neg_weight <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.BlochKatoCocycleUnramifiedAndGreenbergOrdinary
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Matrix

namespace GlobalTheory.Ord2

theorem bk_unr_gr : Loc.LocalPublishedTheorems → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ z ∈ Z1 (Loc.colRep W), IsBK l (Loc.colRep W) z → Unr W z ∧ Gr W A z := by
  intro hP l _ Ω _ _ _ e S A W hN z hz hbk
  have hcol : ∀ s x, Loc.colRep W s x = mat W s *ᵥ x := fun s x => by
    simp [Loc.colRep, Matrix.toLin'_apply]
  refine ⟨fun w hw => ?_, ?_⟩
  · obtain ⟨B, hB, x, hx⟩ := hbk.away w hw
    exact ⟨B, hB, x, fun s hs => by rw [hx s hs, hcol]⟩
  obtain ⟨ι, hιc, hιD, hιS, hιI, hιcyc, hιZ⟩ := GlobalTheory.T.crystallineClass_restrict_decompositionGroup l Ω W A hN.atL z hz hbk
  have hup : ∀ σ, mat W (ι σ) 1 0 = 0 := fun σ => hN.upper _ (hιD σ)
  let k0 : GQ l →* Qbar l :=
    { toFun := fun σ => mat W (ι σ) 1 1
      map_one' := by simp [mat]
      map_mul' := fun σ τ => by
        have h := hup σ
        simp only [mat] at h
        simp only [mat, map_mul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, h, zero_mul, zero_add] }
  let κ : GQ l →* (Qbar l)ˣ := k0.toHomUnits
  have hκ : ∀ σ, (κ σ : Qbar l) = mat W (ι σ) 1 1 := fun σ => rfl
  have hκc : Continuous fun σ => (κ σ : Qbar l) :=
    ((Units.continuous_val.comp (hN.cont.comp hιc)).matrix_elem 1 1)
  let f : (Fin 2 → Qbar l) →ₗ[ℚ_[l]] Qbar l := LinearMap.proj (R := ℚ_[l]) (φ := fun _ : Fin 2 => Qbar l) 1
  have hf : ∀ σ x, f (((Loc.colRep W).comp ι) σ x) = Loc.chRep κ σ (f x) := fun σ x => by
    have h := hup σ
    simp only [mat] at h
    simp [f, Loc.chRep, hcol, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hκ, mat, h]
  have hc := Loc.z1fCoef (MonoidHom.id (GQ l)) _ _ f (continuous_apply 1) hf _ hιZ
  obtain ⟨c, hcO⟩ := hN.int
  obtain ⟨m, hm1, hm⟩ := hN.wt
  have hw : Loc.HasWeight (MonoidHom.id (GQ l)) κ (-(e : ℤ)) := by
    refine GlobalTheory.T.hasWeight_neg_of_cyclotomic_pow_on_inertia l κ hκc e (2 * m) (by omega) fun σ hσ => ?_
    have hs := hιI σ hσ
    have h0 := hm _ hs
    have hd : (dt W (ι σ) : Qbar l) ^ 2 = 1 := by
      have := congrArg (fun u : G ℚ Ω →* (Qbar l)ˣ => ((u (ι σ) : (Qbar l)ˣ) : Qbar l)) hN.det2
      simpa using this
    have hdet : (dt W (ι σ) : Qbar l) = mat W (ι σ) 0 0 * mat W (ι σ) 1 1 := by
      have h := hup σ
      simp only [mat] at h
      simp [dt, Matrix.det_fin_two, mat, h]
    have hcy : (Loc.cycA l l (Qbar l) σ : Qbar l) = eps l (ι σ) := by
      simp only [Loc.cycA, eps, cycBar, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, hιcyc, RingHom.coe_comp, Function.comp_apply]
      rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Qbar l)]
      rfl
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val, Units.val_mul, Units.val_zpow_eq_zpow_val, zpow_natCast, Units.val_one, hκ, hcy]
    rw [hdet] at hd
    calc (mat W (ι σ) 1 1 * eps l (ι σ) ^ e) ^ (2 * m) = (mat W (ι σ) 1 1) ^ (2 * m) * (eps l (ι σ) ^ (e * m)) ^ 2 := by ring
      _ = ((mat W (ι σ) 0 0 * mat W (ι σ) 1 1) ^ 2) ^ m := by rw [← h0]; ring
      _ = 1 := by rw [hd, one_pow]
  obtain ⟨x, hx⟩ := GlobalTheory.T.crystallineCocycle_coboundary_of_negative_weight hP l κ hκc c (fun σ => hcO _ 1 1) (-(e : ℤ)) (by have := hN.e_pos; omega) hw _ hc
  refine ⟨x, fun s hs => ?_⟩
  obtain ⟨σ, rfl⟩ := hιS s hs
  have := hx σ
  simpa [f, hκ] using this

end GlobalTheory.Ord2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.BlochKatoCocycleUnramifiedAndGreenbergOrdinaryStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blochKato_cocycle_unramified_and_greenbergOrdinary : Loc.LocalPublishedTheorems → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ z ∈ Z1 (Loc.colRep W), IsBK l (Loc.colRep W) z → Unr W z ∧ Gr W A z := by
  first | exact @GlobalTheory.Ord2.bk_unr_gr | exact GlobalTheory.Ord2.bk_unr_gr | (intros; apply GlobalTheory.Ord2.bk_unr_gr <;> assumption)
end
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem localGaloisCohomology_of_galoisCohomology (h : GlobalTheory.Mem.LiteralAutomorphy.LitCoh) : Loc.LocalPublishedTheorems :=
  ⟨h.lfK, h.ltK, h.leK, h.lf, h.lt, h.le, h.bk⟩

theorem es_vanish : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ES W A → BlochKatoSelmerVanishes l (Loc.colRep W) := by
  intro hLit l _ Ω _ _ _ e S A W hNf hES c hc hBK
  have hStr : StrZero (dual1 W) A := GlobalTheory.T.strict_vanishing_dual_of_literature hLit l Ω e S A W hNf hES
  have hGrD : GrZero (dual1 W) A := GlobalTheory.T.ordinarySelmer_dual_vanishes_of_strict hLit l Ω e S A W hNf hES hStr
  have hGr : GrZero W A := GlobalTheory.T.ordinarySelmer_vanishes_of_dual_vanishes hLit l Ω e S A W hNf hGrD
  obtain ⟨hU, hG⟩ := GlobalTheory.T.blochKato_cocycle_unramified_and_greenbergOrdinary (localGaloisCohomology_of_galoisCohomology hLit) l Ω e S A W hNf c hc hBK
  exact hGr c hc hU hG

end GlobalTheory.Ord2
