module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHopfIdealKerIdealOfBialgHom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsRingHomComplexCompEqOfCountable
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinWeierstrassValuesLatticeTau
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AreaTauPair
noncomputable section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F

namespace GlobalTheory.WpFam.LatConst

theorem area_tauPair (τ : ℍ) : area (tauPair τ) = τ.im := by
  have h1 : (tauPair τ).ω₁ = (τ : ℂ) := rfl
  have h2 : (tauPair τ).ω₂ = 1 := rfl
  rw [area, h1, h2]
  simp [abs_of_pos τ.im_pos]

theorem wEta_one (τ : ℍ) : wEta (tauPair τ) 1 = EisensteinSeries.G2 τ := by
  have h1 : (tauPair τ).ω₁ = (τ : ℂ) := rfl
  have h2 : (tauPair τ).ω₂ = 1 := rfl
  have h := (etaEisenstein (tauPair τ)).2
  rw [h1, h2] at h
  rw [h, one_mul, ← LegendreModelEllipticTorsion.tsum_e2Summand]
  refine tsum_congr fun m => ?_
  rw [EisensteinSeries.e2Summand]
  refine tsum_congr fun n => ?_
  simp [EisensteinSeries.eisSummand, zpow_ofNat]

theorem main : ∀ τ : ℍ, s2 (tauPair τ) = G2s τ ∧ area (tauPair τ) = τ.im := by
  intro τ
  refine ⟨?_, area_tauPair τ⟩
  have h := etaSplit (tauPair τ) 1
  rw [wEta_one, area_tauPair] at h
  rw [G2s, h]
  simp

end GlobalTheory.WpFam.LatConst
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinWeierstrassValuesLatticeTau
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.WpFam.TauVal

theorem complex_div_pow_div_div_pow (a x k : ℂ) (n : ℕ) (hk : k ≠ 0) :
    a / k ^ n / (x / k) ^ n = a / x ^ n := by
  by_cases hx : x = 0
  · subst hx
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp
    · simp [zero_pow h.ne']
  · rw [div_pow]; field_simp

theorem two_pi_I_ne_zero : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
  have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp [this, Complex.I_ne_zero]

theorem main : ∀ (Λ : PeriodPair) (c Ω : ℂ) (τ : ℍ), IsTauOf Λ c τ → (G2s τ / (2 * (Real.pi : ℂ) * Complex.I) ^ 2 / (Ω * c / (2 * Real.pi * Complex.I)) ^ 2 = s2 Λ / Ω ^ 2) ∧ ∀ (N : ℕ) (x : Fin 2 → ZMod N), wp N x τ / (Ω * c / (2 * Real.pi * Complex.I)) ^ 2 = Λ.weierstrassP (c * tors N τ x) / Ω ^ 2 ∧ wpd N x τ / (Ω * c / (2 * Real.pi * Complex.I)) ^ 3 = Λ.derivWeierstrassP (c * tors N τ x) / Ω ^ 3 := by
  intro Λ c Ω τ h
  obtain ⟨_, hP, hD, hs, _⟩ := GlobalTheory.T.weierstrassP_homogeneity_of_isTauOf Λ c τ h
  have hG := (GlobalTheory.WpFam.LatConst.main τ).1
  have hk := two_pi_I_ne_zero
  refine ⟨?_, fun N x => ⟨?_, ?_⟩⟩
  · rw [complex_div_pow_div_div_pow _ _ _ _ hk, hs, hG, mul_pow, inv_mul_eq_div, div_div, mul_comm]
  · rw [wp, complex_div_pow_div_div_pow _ _ _ _ hk, hP, mul_pow, inv_mul_eq_div, div_div, mul_comm]
  · rw [wpd, complex_div_pow_div_div_pow _ _ _ _ hk, hD, mul_pow, inv_mul_eq_div, div_div, mul_comm]

end GlobalTheory.WpFam.TauVal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinWeierstrassValuesLatticeTauStatement
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisensteinWeierstrass_values_lattice_tau : ∀ (Λ : PeriodPair) (c Ω : ℂ) (τ : ℍ), IsTauOf Λ c τ → (G2s τ / (2 * (Real.pi : ℂ) * Complex.I) ^ 2 / (Ω * c / (2 * Real.pi * Complex.I)) ^ 2 = s2 Λ / Ω ^ 2) ∧ ∀ (N : ℕ) (x : Fin 2 → ZMod N), wp N x τ / (Ω * c / (2 * Real.pi * Complex.I)) ^ 2 = Λ.weierstrassP (c * tors N τ x) / Ω ^ 2 ∧ wpd N x τ / (Ω * c / (2 * Real.pi * Complex.I)) ^ 3 = Λ.derivWeierstrassP (c * tors N τ x) / Ω ^ 3 := by
  first | exact @GlobalTheory.WpFam.TauVal.main | exact GlobalTheory.WpFam.TauVal.main | (intros; apply GlobalTheory.WpFam.TauVal.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieConditionsOfEtaleGaloisQuotient
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieConditionsOfEtaleGaloisQuotient
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT.EtaleLie

variable {S : Scheme.{0}}

theorem fst_spMap_epsScaleR {R' : Type} [CommRing R'] (c : R') :
    spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ spMap (epsScaleR c) =
      spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact RingHom.ext fun r => TrivSqZeroExt.fst_map _ r

theorem existsUnique_dual_lift {R' : Type} [CommRing R'] {A B : Over S} [GrpObj A] [GrpObj B] (ψ : A ⟶ B)
    [IsMonHom ψ] [Etale ψ.left] (x : Sp R' ⟶ S) (h : Sp (DualNumber R') ⟶ B.left)
    (hh : spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ h = (1 : Over.mk x ⟶ B).left) :
    ∃! l : Sp (DualNumber R') ⟶ A.left,
      spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ l = (1 : Over.mk x ⟶ A).left ∧ l ≫ ψ.left = h := by
  let π : CommRingCat.of (DualNumber R') ⟶ CommRingCat.of R' :=
    CommRingCat.ofHom (TrivSqZeroExt.fstHom R' R' R').toRingHom
  have hπ : Function.Surjective π := fun a => ⟨TrivSqZeroExt.inl a, rfl⟩
  have hsq : ∀ a b : DualNumber R', a.fst = 0 → b.fst = 0 → a * b = 0 := fun a b ha hb => by
    ext <;> simp [ha, hb]
  have hnil : IsNilpotent (RingHom.ker π.hom) :=
    ⟨2, by
      rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
      exact fun a ha b hb => hsq a b ha hb⟩
  refine GlobalTheory.existsUnique_lift_of_etale_of_surjective ψ.left π hπ hnil _ h ?_
  show (1 : Over.mk x ⟶ A).left ≫ ψ.left = spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ h
  rw [hh]
  exact congrArg (·.left) (MonObj.one_comp ψ)

theorem lie_of_etale : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (M : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b M s) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (act' : OActN D.O A') (ψ : o.A ⟶ A') (Ga : Type) [Group Ga] (ρ : Ga → (o.A.left ⟶ o.A.left)), IsAbelianScheme A' → IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover Ga ρ ψ.left → (∀ c' : D.O, o.act.act c' ≫ ψ = ψ ≫ act'.act c') → (∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ S), x ≫ s = spMap β → ∀ v : epsPtR x ⟶ A', IsTanScal act' x (algebraMap (𝓞 D.F) D.O D.ω) (β b.ρ) v → ∃ w : Fin D.a → (epsPtR x ⟶ A'), (∀ i, ∀ c : 𝓞 D.F, IsTanScal act' x (algebraMap (𝓞 D.F) D.O c) (β (b.t i c)) (w i)) ∧ v = (List.ofFn w).prod) ∧ (∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (β : R →+* κ), x ≫ s = spMap β → ∀ i, LieMult (act'.toF D) x (β.comp (b.t i)) D.m) := by
  intro p _ D R _ b M S s o A' _ _ act' ψ Ga _ ρ _hab hψ hG hact
  haveI := hψ
  haveI : Etale ψ.left := hG.etale
  refine ⟨?_, ?_⟩
  · intro R' _ β x hx v hv
    obtain ⟨l, ⟨hl₁, hl₂⟩, -⟩ := existsUnique_dual_lift ψ x v.left hv.1
    let u : epsPtR x ⟶ o.A := Over.homMk l (by
      show l ≫ o.A.hom = _
      rw [← Over.w ψ, ← Category.assoc, hl₂]; exact Over.w v)
    have hu : IsTanScal o.act x (algebraMap (𝓞 D.F) D.O D.ω) (β b.ρ) u := by
      refine ⟨hl₁, ?_⟩
      have hh : spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ (spMap (epsScaleR (β b.ρ)) ≫ v.left) =
          (1 : Over.mk x ⟶ A').left := by
        rw [← Category.assoc, fst_spMap_epsScaleR, hv.1]
      haveI := o.act.hom (algebraMap (𝓞 D.F) D.O D.ω)
      refine (existsUnique_dual_lift ψ x _ hh).unique ⟨?_, ?_⟩ ⟨?_, ?_⟩
      · show _ ≫ l ≫ (o.act.act _).left = _
        rw [← Category.assoc, hl₁]
        have e : ((1 : Over.mk x ⟶ o.A) ≫ o.act.act (algebraMap (𝓞 D.F) D.O D.ω)).left = (1 : Over.mk x ⟶ o.A).left :=
          congrArg Over.Hom.left (MonObj.one_comp _)
        exact e
      · show (l ≫ (o.act.act _).left) ≫ ψ.left = _
        rw [Category.assoc, ← Over.comp_left, hact, Over.comp_left, ← Category.assoc, hl₂, ← hv.2]
        rfl
      · show _ ≫ spMap _ ≫ l = _
        rw [← Category.assoc, fst_spMap_epsScaleR, hl₁]
      · show (spMap _ ≫ l) ≫ ψ.left = _
        rw [Category.assoc, hl₂]
    obtain ⟨w, hw, hvw⟩ := o.lie R' β x hx u hu
    refine ⟨fun i => w i ≫ ψ, fun i c => ⟨?_, ?_⟩, ?_⟩
    · show _ ≫ (w i).left ≫ ψ.left = _
      rw [← Category.assoc, (hw i c).1]
      have e : ((1 : Over.mk x ⟶ o.A) ≫ ψ).left = (1 : Over.mk x ⟶ A').left :=
        congrArg Over.Hom.left (MonObj.one_comp ψ)
      exact e
    · show ((w i ≫ ψ) ≫ act'.act _).left = spMap _ ≫ (w i).left ≫ ψ.left
      rw [Category.assoc, ← hact, ← Category.assoc, Over.comp_left, (hw i c).2, Category.assoc]
    · apply Over.OverMorphism.ext
      rw [← GlobalTheory.LieEtale.ofFn_prod_comp ψ w, ← hvw]
      exact hl₂.symm
  · intro κ _ _ x β hx i
    exact (GlobalTheory.LieEtale.lieMult_iff_of_etale (𝓞 D.F) S o.A A' ψ (o.act.toF D) (act'.toF D) hψ hG.etale
      (fun c => hact _) κ x (β.comp (b.t i)) D.m).mp (o.lieRank κ x β hx i)

end GlobalTheory.UPel.HT.EtaleLie
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieConditionsOfEtaleGaloisQuotientStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_lie_conditions_of_etale_galois_quotient : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (M : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b M s) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (act' : OActN D.O A') (ψ : o.A ⟶ A') (Ga : Type) [Group Ga] (ρ : Ga → (o.A.left ⟶ o.A.left)), IsAbelianScheme A' → IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover Ga ρ ψ.left → (∀ c' : D.O, o.act.act c' ≫ ψ = ψ ≫ act'.act c') → (∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ S), x ≫ s = spMap β → ∀ v : epsPtR x ⟶ A', IsTanScal act' x (algebraMap (𝓞 D.F) D.O D.ω) (β b.ρ) v → ∃ w : Fin D.a → (epsPtR x ⟶ A'), (∀ i, ∀ c : 𝓞 D.F, IsTanScal act' x (algebraMap (𝓞 D.F) D.O c) (β (b.t i c)) (w i)) ∧ v = (List.ofFn w).prod) ∧ (∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (β : R →+* κ), x ≫ s = spMap β → ∀ i, LieMult (act'.toF D) x (β.comp (b.t i)) D.m) := by
  first | exact @GlobalTheory.UPel.HT.EtaleLie.lie_of_etale | exact GlobalTheory.UPel.HT.EtaleLie.lie_of_etale | (intros; apply GlobalTheory.UPel.HT.EtaleLie.lie_of_etale <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MuDvdFrobXiSub
set_option autoImplicit false

noncomputable section

open GlobalTheory.QLog GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta

namespace GlobalTheory.WinLift

section Nil

theorem isNil_of_theta_eq {B R ι : Type} [CommRing B] [CommRing R] [IsLocalRing R] [Fintype ι]
    (p : ℕ) [Fact p.Prime] (θ : B →+* R) (σ : B →+* B) (hp : ¬IsUnit (p : R))
    (hσ : ∀ b, (p : B) ∣ σ b - b ^ p) (M M' : Matrix ι ι B) (h : ∀ i j, θ (M i j) = θ (M' i j))
    (hM : IsNil θ σ M) : IsNil θ σ M' := by
  obtain ⟨N, hN⟩ := hM
  refine ⟨N, fun v i => ?_⟩
  have hs : ∀ z : B, θ z ∈ IsLocalRing.maximalIdeal R → θ (σ z) ∈ IsLocalRing.maximalIdeal R := by
    intro z hz
    obtain ⟨c, hc⟩ := hσ z
    have e : σ z = z ^ p + p * c := by rw [← hc]; ring
    rw [e, map_add (f := _), map_pow, map_mul, map_natCast]
    exact Ideal.add_mem _ (Ideal.pow_mem_of_mem _ hz _ (Fact.out : p.Prime).pos)
      (Ideal.mul_mem_right _ _ ((IsLocalRing.mem_maximalIdeal _).2 hp))
  have key : ∀ (n : ℕ) (w : ι → B) (i : ι),
      θ (((fun w : ι → B => M.mulVec fun j => σ (w j))^[n] w) i) -
        θ (((fun w : ι → B => M'.mulVec fun j => σ (w j))^[n] w) i) ∈
          IsLocalRing.maximalIdeal R := by
    intro n
    induction n with
    | zero => intro w i; simp
    | succ n ih =>
      intro w i
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      simp only [Matrix.mulVec, dotProduct]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_sum, ← Finset.sum_sub_distrib]
      refine Ideal.sum_mem _ fun j _ => ?_
      rw [map_mul, map_mul, h i j, ← mul_sub, ← map_sub, ← map_sub]
      exact Ideal.mul_mem_left _ _ (hs _ (by rw [map_sub]; exact ih w j))
  intro hu
  have h1 := (IsLocalRing.mem_maximalIdeal _).2 (hN v i)
  have h2 := Ideal.sub_mem _ h1 (key N v i)
  rw [sub_sub_cancel] at h2
  exact (IsLocalRing.mem_maximalIdeal _).1 h2 hu

theorem isNil_of_map {A B R ι : Type} [CommRing A] [CommRing B] [CommRing R] [Fintype ι]
    (a : A →+* B) (θA : A →+* R) (θB : B →+* R) (φ : A →+* A) (σ : B →+* B)
    (hθ : ∀ x, θB (a x) = θA x) (hσ : ∀ x, σ (a x) = a (φ x)) (M : Matrix ι ι A)
    (h : IsNil θB σ (M.map a)) : IsNil θA φ M := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun v i => ?_⟩
  have key : ∀ (n : ℕ) (w : ι → A),
      (fun w : ι → B => (M.map a).mulVec fun j => σ (w j))^[n] (fun j => a (w j)) =
        fun j => a (((fun w : ι → A => M.mulVec fun j => φ (w j))^[n] w) j) := by
    intro n
    induction n with
    | zero => intro w; rfl
    | succ n ih =>
      intro w
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      funext j
      set_option synthInstance.maxHeartbeats 100000 in
        simp [Matrix.mulVec, dotProduct, map_sum, hσ]
  have := hN (fun j => a (v j)) i
  rwa [key, hθ] at this

theorem map_inv_of_isUnit {R S ι : Type} [CommRing R] [CommRing S] [Fintype ι] [DecidableEq ι]
    (f : R →+* S) (M : Matrix ι ι R) (hM : IsUnit M) : (M.map f)⁻¹ = M⁻¹.map f := by
  apply Matrix.inv_eq_right_inv
  rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← map_mul,
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det M).1 hM), map_one]

end Nil

end GlobalTheory.WinLift

namespace GlobalTheory.WinLift

section Frob

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]

theorem frob_teich (x : PreTilt O p) :
    WittVector.frobenius (WittVector.teichmuller p x) = WittVector.teichmuller p x ^ p := by
  rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, map_pow]

theorem frob_xi (ε : PreTilt O p) :
    WittVector.frobenius (xi ε) = ∑ i ∈ Finset.range p, WittVector.teichmuller p ε ^ i := by
  have : root ε ^ p = ε := (_root_.frobeniusEquiv (PreTilt O p) p).apply_symm_apply ε
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [xi, map_sum, map_pow, frob_teich]
  simp only [← map_pow, this]

theorem frob_mu (ε : PreTilt O p) :
    WittVector.frobenius (Sandwich.mu ε) = WittVector.frobenius (xi ε) * Sandwich.mu ε := by
  rw [frob_xi, Sandwich.mu, geom_sum_mul, map_sub, map_one, frob_teich]

theorem mu_dvd_frob_xi_sub (ε : PreTilt O p) :
    Sandwich.mu ε ∣ WittVector.frobenius (xi ε) - p := by
  have : (p : Ainf p O) = ∑ i ∈ Finset.range p, 1 ^ i := by simp
  rw [this, frob_xi, ← Finset.sum_sub_distrib]
  exact Finset.dvd_sum fun i _ => sub_dvd_pow_sub_pow _ _ i

end Frob

end GlobalTheory.WinLift

namespace GlobalTheory.WinLift

section Frame

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O] {ε : PreTilt O p}

theorem root_prim (hε : IsPrimitiveSystem ε) : IsPrimitiveRoot (PreTilt.untilt (root ε)) p := by
  simpa [zeta] using hε 1

theorem theta_mu (hv : v.Integers O) (hε : IsPrimitiveSystem ε) :
    WittVector.fontaineTheta O p (Sandwich.mu ε) = 0 :=
  Sandwich.Model.theta_mu hv (root_prim hε)

theorem theta_frob_xi (hv : v.Integers O) (hε : IsPrimitiveSystem ε) :
    WittVector.fontaineTheta O p (WittVector.frobenius (xi ε)) = p := by
  have h1 : WittVector.fontaineTheta O p (WittVector.teichmuller p ε) = 1 := by
    have := theta_mu hv hε
    rw [Sandwich.mu, map_sub, map_one, sub_eq_zero] at this
    exact this
  set_option synthInstance.maxHeartbeats 100000 in
    rw [frob_xi, map_sum]
  simp [h1]

variable (F : BFrame ε)

theorem tf (b : F.B) (h : (p : F.B) * b = 0) : b = 0 := by
  apply F.frame.inj
  have h1 := congrArg (algebraMap F.B F.Q) h
  rw [map_mul, map_natCast, map_zero] at h1
  rw [map_zero]
  exact (F.frame.unit_p.mul_right_eq_zero).1 h1

theorem theta_tau (hv : v.Integers O) (hε : IsPrimitiveSystem ε) : F.θ F.τ = 0 := by
  apply F.frame.sat
  have h := congrArg F.θ F.p_τ
  rw [map_mul, map_natCast, F.θ_a, theta_mu hv hε] at h
  exact h

theorem sigma_tau : F.σ F.τ = F.a (WittVector.frobenius (xi ε)) * F.τ := by
  apply sub_eq_zero.1
  apply tf F
  have h := congrArg F.σ F.p_τ
  rw [map_mul, map_natCast, F.σ_a, frob_mu, map_mul, ← F.p_τ] at h
  rw [mul_sub, h]
  ring

theorem tau_dvd_sigma (b : F.B) (h : F.τ ∣ b) : F.τ ∣ F.σ b := by
  obtain ⟨c, rfl⟩ := h
  rw [map_mul, sigma_tau]
  exact ⟨F.a (WittVector.frobenius (xi ε)) * F.σ c, by ring⟩

theorem mu_dvd_of_p_mul (F : BFrame ε) (z : Ainf p O) (h : Sandwich.mu ε ∣ (p : Ainf p O) * z) :
    Sandwich.mu ε ∣ z := by
  obtain ⟨w, hw⟩ := h
  apply (F.τ_mul z).1
  apply tf F
  have h1 := congrArg F.a hw
  rw [map_mul, map_natCast, map_mul, ← F.p_τ] at h1
  calc (p : F.B) * (F.τ * F.a z) = F.τ * ((p : F.B) * F.a z) := by ring
    _ = 0 := by rw [h1]; linear_combination (p * F.a w) * F.τ_sq

theorem mu_dvd_of_xi_mul (F : BFrame ε) (z : Ainf p O)
    (h : Sandwich.mu ε ∣ WittVector.frobenius (xi ε) * z) : Sandwich.mu ε ∣ z := by
  apply mu_dvd_of_p_mul F
  have h2 := (mu_dvd_frob_xi_sub ε).mul_right z
  have := dvd_sub h h2
  rwa [sub_mul, sub_sub_cancel] at this

end Frame

end GlobalTheory.WinLift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffSubstEqZeroOfDegreeLt
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory

theorem coeff_subst_eq_zero_of_degree_lt :
    ∀ (R : Type) [CommRing R] (σ τ : Type) [Fintype σ] (u : σ → MvPowerSeries τ R)
      (f : MvPowerSeries σ R) (M : ℕ), (∀ i, constantCoeff (u i) = 0) →
      (∀ α : σ →₀ ℕ, α.degree < M → coeff α f = 0) →
      ∀ β : τ →₀ ℕ, β.degree < M → coeff β (subst u f) = 0 := by
  intro R _ σ τ _ u f M hu hf β hβ
  have hs : HasSubst u := ⟨fun i => by rw [hu i]; exact IsNilpotent.zero, fun _ => Set.toFinite _⟩
  rw [coeff_subst hs]
  apply finsum_eq_zero_of_forall_eq_zero
  intro d
  by_cases hd : d.degree < M
  · simp [hf d hd]
  · push_neg at hd
    have hord : ((d.degree : ℕ) : ℕ∞) ≤ (d.prod fun s e => u s ^ e).order := by
      unfold Finsupp.prod
      refine le_trans ?_ (le_order_prod (fun s => u s ^ d s) d.support)
      have hdeg : d.degree = ∑ i ∈ d.support, d i := rfl
      rw [hdeg, Nat.cast_sum]
      exact Finset.sum_le_sum fun s _ => le_order_pow_of_constantCoeff_eq_zero (d s) (hu s)
    have h0 : coeff β (d.prod fun s e => u s ^ e) = 0 := by
      apply coeff_of_lt_order
      exact lt_of_lt_of_le (by exact_mod_cast (lt_of_lt_of_le hβ hd)) hord
    rw [h0, smul_zero]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCharacterHarishChandraProductCuspidalGLOfRegul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCharacterHarishChandraProductCuspidalGLOfRegul
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin


open Polynomial SemidirectProduct in
open scoped Classical in
theorem _root_.GlobalTheory.Shin.isChar_J_of_reg : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ), (∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ L : List (ℕ × ℕ), (∀ p ∈ L, 0 < p.1 ∧ _root_.GlobalTheory.Shin.Reg (Nat.card F) p.1 p.2) → ∀ n, n = _root_.GlobalTheory.Shin.deg L → _root_.GlobalTheory.BI.IsChar ℂ ℂ (_root_.GlobalTheory.Shin.J θ L n) := by
  intro F _ _ θ hθ L
  induction L with
  | nil =>
    intro _ n _
    rw [_root_.GlobalTheory.Shin.J_nil]
    exact _root_.GlobalTheory.BI.isChar_one ℂ ℂ _
  | cons p L ih =>
    intro hL n hn
    rw [_root_.GlobalTheory.Shin.J_cons]
    have hp := hL p List.mem_cons_self
    refine _root_.GlobalTheory.Shin.HCChar.hc_isChar F _ _ n ?_ _ _
      (_root_.GlobalTheory.Shin.isChar_cusp_and_norm_of_reg F θ hθ p.1 p.2 hp.1 hp.2).1
      (ih (fun q hq => hL q (List.mem_cons_of_mem p hq)) _ rfl)
    rw [hn]
    simp [_root_.GlobalTheory.Shin.deg]

end GlobalTheory.Shin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCharacterHarishChandraProductCuspidalGLOfRegulStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCharacter_harishChandraProductCuspidalGL_of_regular : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ), (∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ L : List (ℕ × ℕ), (∀ p ∈ L, 0 < p.1 ∧ Reg (Nat.card F) p.1 p.2) → ∀ n, n = deg L → IsChar ℂ ℂ (J θ L n) := by
  first | (exact @GlobalTheory.Shin.isChar_J_of_reg) | (exact GlobalTheory.Shin.isChar_J_of_reg) | (intros; apply GlobalTheory.Shin.isChar_J_of_reg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NmulSucc
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.MapNMul

theorem cc_subst {R : Type} [CommRing R] {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ R}
    (ha : ∀ i, constantCoeff (a i) = 0) (f : MvPowerSeries σ R) :
    constantCoeff (subst a f) = constantCoeff f := by
  have hs : HasSubst a := hasSubst_of_constantCoeff_zero ha
  have h1 : f = (f - C (constantCoeff f)) + C (constantCoeff f) := by ring
  conv_lhs => rw [h1]
  rw [subst_add hs, map_add (f := _), constantCoeff_subst_eq_zero hs ha (by simp), subst_C, zero_add]
  simp

theorem nmul_succ {R : Type} [CommRing R] {d : ℕ} (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (k : ℕ) :
    nmul μ (k + 1) = op μ (nmul μ k) (fun i => X i) := by
  unfold nmul
  rw [Function.iterate_succ_apply']

theorem cc_nmul {R : Type} [CommRing R] {d : ℕ} (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (hμ : ∀ i, constantCoeff (μ i) = 0) : ∀ (k : ℕ) (i : Fin d), constantCoeff (nmul μ k i) = 0 := by
  intro k
  induction k with
  | zero => intro i; simp [nmul]
  | succ k ih =>
    intro i
    rw [nmul_succ]
    simp only [op, at2]
    rw [cc_subst (fun s => by cases s <;> simp [ih]), hμ]

theorem map_nmul (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : ∀ i, constantCoeff (μ i) = 0) :
    ∀ (k : ℕ) (i : Fin d), map φ (nmul μ k i) = nmul (fun j => map φ (μ j)) k i := by
  intro k
  induction k with
  | zero => intro i; simp [nmul]
  | succ k ih =>
    intro i
    rw [nmul_succ, nmul_succ]
    simp only [op, at2]
    have hs : HasSubst (Sum.elim (nmul μ k) (fun i => (X i : MvPowerSeries (Fin d) R))) :=
      hasSubst_of_constantCoeff_zero fun s => by cases s <;> simp [cc_nmul μ hμ]
    rw [map_subst hs]
    congr 1
    funext s
    cases s <;> simp [ih]

end GlobalTheory.MapNMul
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesLiftQuotient
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

theorem mvPowerSeries_lift_quotient :
    ∀ (O σ : Type) [CommRing O] (I : Ideal O), (∀ g : MvPowerSeries σ (O ⧸ I), ∃ f : MvPowerSeries σ O, map (Ideal.Quotient.mk I) f = g ∧ (constantCoeff g = 0 → constantCoeff f = 0)) ∧ (∀ f : MvPowerSeries σ O, map (Ideal.Quotient.mk I) f = 0 ↔ ∀ α, coeff α f ∈ I) ∧ ∀ (a : O) (f : MvPowerSeries σ O), (∀ α, a ∣ coeff α f) ↔ ∃ g, f = a • g := by
  classical
  intro O σ _ I
  refine ⟨?_, ?_, ?_⟩
  · intro g
    let s : O ⧸ I → O := fun x => if x = 0 then 0 else Quotient.out x
    have hs : ∀ x, Ideal.Quotient.mk I (s x) = x := by
      intro x
      by_cases hx : x = 0
      · simp [s, hx]
      · simp only [s, if_neg hx]
        exact Ideal.Quotient.mk_out x
    let f : MvPowerSeries σ O := fun α => s (coeff α g)
    refine ⟨f, ?_, ?_⟩
    · ext α
      rw [coeff_map]
      exact hs _
    · intro h0
      have : coeff (0 : σ →₀ ℕ) g = 0 := by simpa [coeff_zero_eq_constantCoeff_apply] using h0
      rw [← coeff_zero_eq_constantCoeff_apply]
      show s (coeff 0 g) = 0
      simp [s, this]
  · intro f
    constructor
    · intro h α
      have := congrArg (coeff α) h
      rw [coeff_map, map_zero] at this
      exact Ideal.Quotient.eq_zero_iff_mem.mp this
    · intro h
      ext α
      rw [coeff_map, map_zero]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (h α)
  · intro a f
    constructor
    · intro h
      choose c hc using h
      let g : MvPowerSeries σ O := fun α => c α
      have hg : ∀ α, coeff α g = c α := fun _ => rfl
      refine ⟨g, ?_⟩
      ext α
      rw [coeff_smul, hg, hc α]
    · rintro ⟨g, rfl⟩ α
      rw [coeff_smul]
      exact dvd_mul_right _ _

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPAdicPowerSeriesValueMapOfContinuousEvaluatio
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPAdicPowerSeriesValueMapOfContinuousEvaluatio
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory

theorem eval_coe_polynomial_of_isEval {p : ℕ} {B : Type} [CommRing B] {σ : Type}
    (z : σ → B) (E : MvPowerSeries σ B →ₐ[B] B) (hE : IsEval p z E) (P : MvPolynomial σ B) :
    E (P : MvPowerSeries σ B) = MvPolynomial.eval z P := by
  have h : E.comp (MvPolynomial.coeToMvPowerSeries.algHom B) = MvPolynomial.aeval z := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [MvPolynomial.coeToMvPowerSeries.algHom_apply, hE.1 i]
  have := congrArg (fun φ => φ P) h
  simpa [MvPolynomial.coeToMvPowerSeries.algHom_apply] using this

theorem hasVal_map_of_isEval : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (z : σ → B), (∀ i, ∃ N : ℕ, (p : B) ∣ z i ^ N) → ∀ E : MvPowerSeries σ B →ₐ[B] B, IsEval p z E → ∀ s : MvPowerSeries σ B, HasVal p z (map (algebraMap B Q) s) (algebraMap B Q (E s)) := by
  intro p _ B O Q _ _ _ _ θ _ σ _ _ z _ E hE s m
  obtain ⟨N, hN⟩ := hE.2 m
  refine ⟨N, fun N' hN' => ?_⟩
  set n : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => N'
  have hdiv : (p : B) ^ m ∣ E (s - (trunc' B n s : MvPowerSeries σ B)) := by
    apply hN
    intro α hα
    have hle : α ≤ n := by
      intro i
      have h1 : α i ≤ α.degree := by
        classical
        rw [Finsupp.degree]
        by_cases hi : i ∈ α.support
        · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi
        · simp [Finsupp.notMem_support_iff.1 hi]
      show α i ≤ N'
      omega
    rw [map_sub, MvPolynomial.coeff_coe, coeff_trunc', if_pos hle, sub_self]
  obtain ⟨b, hb⟩ := hdiv
  refine ⟨b, ?_⟩
  rw [map_sub, eval_coe_polynomial_of_isEval z E hE] at hb
  have key : algebraMap B Q (MvPolynomial.eval z (trunc' B n s)) =
      MvPolynomial.eval₂ (algebraMap B Q) (fun i => algebraMap B Q (z i)) (trunc' B n s) := by
    rw [MvPolynomial.eval, MvPolynomial.coe_eval₂Hom]
    exact MvPolynomial.eval₂_comp_left _ _ _ _
  rw [trunc'_map, MvPolynomial.eval_map, ← key, ← map_sub, hb]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPAdicPowerSeriesValueMapOfContinuousEvaluatioStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasPAdicPowerSeriesValue_map_of_continuousEvaluation : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (z : σ → B), (∀ i, ∃ N : ℕ, (p : B) ∣ z i ^ N) → ∀ E : MvPowerSeries σ B →ₐ[B] B, IsEval p z E → ∀ s : MvPowerSeries σ B, HasVal p z (map (algebraMap B Q) s) (algebraMap B Q (E s)) := by
  first | exact @GlobalTheory.hasVal_map_of_isEval | exact GlobalTheory.hasVal_map_of_isEval | (intros; apply GlobalTheory.hasVal_map_of_isEval <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantDerivationFormalGroupLawLeibniz
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantDerivationFormalGroupLawLeibniz
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LawDer

theorem atZero_subst_of_unit (R : Type) [CommRing R] (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hc : ∀ i, constantCoeff (μ i) = 0)
    (hu : op μ (fun i => (X i : MvPowerSeries (Fin d) R)) (fun _ => 0) = fun i => X i)
    (F : MvPowerSeries (Fin d) R) : atZero (subst μ F) = F := by
  have hμ : HasSubst μ := hasSubst_of_constantCoeff_zero hc
  have hz : HasSubst (Sum.elim (fun i : Fin d => (X i : MvPowerSeries (Fin d) R)) fun _ : Fin d => (0 : MvPowerSeries (Fin d) R)) :=
    hasSubst_of_constantCoeff_zero (by intro s; cases s <;> simp)
  unfold atZero
  rw [subst_comp_subst_apply hμ hz]
  have : (fun i => subst (Sum.elim (fun i : Fin d => (X i : MvPowerSeries (Fin d) R)) fun _ : Fin d => (0 : MvPowerSeries (Fin d) R)) (μ i))
      = fun i => X i := hu
  rw [this, subst_self]
  rfl

theorem invDer_mul : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) → op μ (fun i => (X i : MvPowerSeries (Fin d) R)) (fun _ => 0) = (fun i => X i) → ∀ (u : Fin d → R) (F G : MvPowerSeries (Fin d) R), invDer μ u (F * G) = invDer μ u F * G + F * invDer μ u G := by
  intro R _ d μ hc hu u F G
  have hμ : HasSubst μ := hasSubst_of_constantCoeff_zero hc
  have hz : HasSubst (Sum.elim (fun i : Fin d => (X i : MvPowerSeries (Fin d) R)) fun _ : Fin d => (0 : MvPowerSeries (Fin d) R)) :=
    hasSubst_of_constantCoeff_zero (by intro s; cases s <;> simp)
  have hmul : ∀ H K : MvPowerSeries (Fin d ⊕ Fin d) R, atZero (H * K) = atZero H * atZero K := by
    intro H K; unfold atZero; exact subst_mul hz H K
  have h0 := atZero_subst_of_unit R d μ hc hu
  have key : ∀ i, atZero (MvPowerSeries.pderiv (Sum.inr i) (subst μ (F * G))) =
      atZero (MvPowerSeries.pderiv (Sum.inr i) (subst μ F)) * G + F * atZero (MvPowerSeries.pderiv (Sum.inr i) (subst μ G)) := by
    intro i
    rw [subst_mul hμ, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    unfold atZero
    rw [subst_add hz, subst_mul hz, subst_mul hz]
    have hF := h0 F; have hG := h0 G; unfold atZero at hF hG
    rw [hF, hG]; ring
  unfold invDer
  simp_rw [key, smul_add, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm]

end GlobalTheory.LawDer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantDerivationFormalGroupLawLeibnizStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariantDerivationFormalGroupLaw_leibniz : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) → op μ (fun i => (X i : MvPowerSeries (Fin d) R)) (fun _ => 0) = (fun i => X i) → ∀ (u : Fin d → R) (F G : MvPowerSeries (Fin d) R), invDer μ u (F * G) = invDer μ u F * G + F * invDer μ u G := by
  first | exact @GlobalTheory.LawDer.invDer_mul | exact GlobalTheory.LawDer.invDer_mul | (intros; apply GlobalTheory.LawDer.invDer_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomEqZeroOfIsConnOfIsEt
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

namespace PDivGroup

variable {p : ℕ} {k : Type} [Field k]


omit [Field k] in
theorem mem_augIdeal_iff' {R A : Type} [CommRing R] [CommRing A] [Bialgebra R A] (a : A) :
    a ∈ augIdeal R A ↔ counit (R := R) a = 0 := by
  rw [augIdeal, RingHom.mem_ker, Bialgebra.counitAlgHom_apply]

theorem eq_zero_of_app_augIdeal {G H : PDivGroup p k} (f : G ⟶ H)
    (hf : ∀ n, ∀ a ∈ augIdeal k (H.A n), f.app n a = 0) : f = 0 := by
  refine Hom.ext (funext fun n => BialgHom.ext fun a => ?_)
  have hmem : a - algebraMap k (H.A n) (counit (R := k) a) ∈ augIdeal k (H.A n) := by
    rw [mem_augIdeal_iff', map_sub, ← Bialgebra.counitAlgHom_apply (R := k),
      ← Bialgebra.counitAlgHom_apply (R := k), AlgHom.commutes, Algebra.algebraMap_self,
      RingHom.id_apply, sub_self]
  have h := hf n _ hmem
  rw [map_sub, AlgHomClass.commutes, sub_eq_zero] at h
  exact h

variable [Fact p.Prime] [CharP k p] [PerfectRing k p]

theorem exists_augIdeal_pow_eq {A : Type} [CommRing A] [Bialgebra k A] [Module.Finite k A]
    [IsReduced A] (r : ℕ) : ∀ a ∈ augIdeal k A, ∃ b ∈ augIdeal k A, a = b ^ p ^ r := by
  induction r with
  | zero => exact fun a ha => ⟨a, ha, by rw [pow_zero, pow_one]⟩
  | succ r ih =>
    intro a ha
    obtain ⟨b, hb, rfl⟩ := ih a ha
    obtain ⟨c, rfl⟩ := exists_pow_char_eq_of_isReduced_finite p k A b
    refine ⟨c, ?_, by rw [← pow_mul, ← pow_succ']⟩
    rw [mem_augIdeal_iff'] at hb ⊢
    rw [← Bialgebra.counitAlgHom_apply (R := k), map_pow, Bialgebra.counitAlgHom_apply] at hb
    exact pow_eq_zero_iff (Fact.out : p.Prime).ne_zero |>.1 hb

theorem eq_zero_of_isConn_of_isEt {G H : PDivGroup p k} (hG : G.IsConn) (hH : H.IsEt)
    (f : G ⟶ H) : f = 0 := by
  refine eq_zero_of_app_augIdeal f fun n a ha => ?_
  haveI := hH n
  haveI : IsNoetherianRing (G.A n) := isNoetherian_of_tower k inferInstance
  obtain ⟨N, hN⟩ := (Ideal.FG.isNilpotent_iff_le_nilradical
    (IsNoetherian.noetherian (augIdeal k (G.A n)))).2 fun x hx => mem_nilradical.2 (hG n x hx)
  obtain ⟨b, hb, rfl⟩ := exists_augIdeal_pow_eq (A := H.A n) N a ha
  have hfb : f.app n b ∈ augIdeal k (G.A n) := by
    rw [mem_augIdeal_iff', CoalgHomClass.counit_comp_apply]
    exact (mem_augIdeal_iff' b).1 hb
  have hle : N ≤ p ^ N := (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le
  have h1 := Ideal.pow_le_pow_right hle (Ideal.pow_mem_pow hfb (p ^ N))
  rw [hN] at h1
  rw [map_pow]
  exact (Submodule.mem_bot _).1 h1

theorem eq_zero_of_isEt_of_isConn {G H : PDivGroup p k} (hG : G.IsConn) (hH : H.IsEt)
    (f : H ⟶ G) : f = 0 := by
  refine eq_zero_of_app_augIdeal f fun n a ha => ?_
  haveI := hH n
  exact ((hG n a ha).map (f.app n)).eq_zero

end PDivGroup

theorem PDivGroup.hom_eq_zero_of_isConn_of_isEt :
    ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p]
      (G H : PDivGroup p k), G.IsConn → H.IsEt → (∀ f : G ⟶ H, f = 0) ∧ ∀ f : H ⟶ G, f = 0 :=
  fun _ _ _ _ _ _ _ _ hG hH =>
    ⟨PDivGroup.eq_zero_of_isConn_of_isEt hG hH, PDivGroup.eq_zero_of_isEt_of_isConn hG hH⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeSubAFiniteFree
noncomputable section

namespace GlobalTheory.UPel.HT.HeckeAd

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

variable {S : Scheme.{0}} {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R]

def heckeSubA {b : Base D R} {M : ℕ} {s : S ⟶ Sp R} (o : Obj b M s) (f : D.La →+ D.La) (N : ℕ) :
    Subgroup (𝟙_ (Over S) ⟶ o.A) where
  carrier := {h | ∃ x, h = o.eta (N • f x)}
  one_mem' := ⟨0, by rw [map_zero, smul_zero, eta_zero]⟩
  mul_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, by rw [map_add (f := _), smul_add, o.eta_add]⟩
  inv_mem' := by
    rintro _ ⟨x, rfl⟩
    exact ⟨-x, by rw [map_neg, smul_neg, eta_neg]⟩

theorem mem_heckeSubA {b : Base D R} {M : ℕ} {s : S ⟶ Sp R} (o : Obj b M s) (f : D.La →+ D.La) (N : ℕ)
    (x : D.La) : o.eta (N • f x) ∈ heckeSubA o f N := ⟨x, rfl⟩

theorem eta_pow {b : Base D R} {M : ℕ} {s : S ⟶ Sp R} (o : Obj b M s) (n : ℕ) (z : D.La) :
    (o.eta z) ^ n = o.eta (n • z) := by
  induction n with
  | zero => rw [pow_zero, zero_smul, eta_zero]
  | succ n ih => rw [pow_succ, ih, succ_nsmul, o.eta_add]

theorem pow_eq_one_of_mem {b : Base D R} {N k : ℕ} {s : S ⟶ Sp R} (o : Obj b (N * k) s) (f : D.La →+ D.La)
    (h : 𝟙_ (Over S) ⟶ o.A) (hh : h ∈ heckeSubA o f N) : h ^ k = 1 := by
  obtain ⟨x, rfl⟩ := hh
  rw [eta_pow, smul_smul, show k * N = N * k from mul_comm _ _, o.eta_ker]

theorem act_mem {b : Base D R} {N k : ℕ} {s : S ⟶ Sp R} (o : Obj b (N * k) s) (f : D.La →+ D.La)
    (hf : ∀ (a : D.O) (x : D.La), ∃ z, f (a • x) = a • f x + (N * k) • z) (a : D.O)
    (h : 𝟙_ (Over S) ⟶ o.A) (hh : h ∈ heckeSubA o f N) : h ≫ o.act.act a ∈ heckeSubA o f N := by
  obtain ⟨x, rfl⟩ := hh
  obtain ⟨z, hz⟩ := hf a x
  refine ⟨a • x, ?_⟩
  rw [hz, smul_add, o.eta_add, smul_smul, show N * (N * k) = (N * k) * N from mul_comm _ _, ← smul_smul,
    o.eta_ker, _root_.mul_one, ← o.eta_lin, smul_comm]

theorem heckeSubA_finite_free (b : Base D R) (f : D.La →+ D.La) (k N : ℕ) (hk : 0 < k) (hN : 0 < N)
    (hkp : k.Coprime p) (hNp : N.Coprime p) (s : S ⟶ Sp R) (o : Obj b (N * k) s) :
    Finite (heckeSubA o f N) ∧ ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (h : 𝟙_ (Over S) ⟶ o.A),
      h ∈ heckeSubA o f N → toUnit (Over.mk x) ≫ h = 1 → h = 1 := by
  refine ⟨?_, ?_⟩
  · haveI := D.finLa
    let K : Submodule ℤ D.La := LinearMap.range ((k : ℤ) • LinearMap.id)
    haveI : Finite (D.La ⧸ K) := by
      apply Module.finite_of_fg_torsion
      intro q
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective K q
      refine ⟨⟨(k : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hk.ne')⟩, ?_⟩
      show (k : ℤ) • (Submodule.Quotient.mk y : D.La ⧸ K) = 0
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact ⟨y, by simp⟩
    let σ := Function.surjInv (Submodule.Quotient.mk_surjective K)
    refine Finite.of_surjective
      (fun q : D.La ⧸ K => (⟨o.eta (N • f (σ q)), mem_heckeSubA o f N _⟩ : heckeSubA o f N)) ?_
    rintro ⟨h, x, rfl⟩
    refine ⟨Submodule.Quotient.mk x, Subtype.ext ?_⟩
    have e : Submodule.Quotient.mk (σ (Submodule.Quotient.mk x)) = (Submodule.Quotient.mk x : D.La ⧸ K) :=
      Function.surjInv_eq _ _
    rw [Submodule.Quotient.eq] at e
    obtain ⟨z, hz⟩ := e
    have hz' : σ (Submodule.Quotient.mk x) = x + k • z := by
      simp only [LinearMap.smul_apply, LinearMap.id_apply, natCast_zsmul] at hz
      rw [hz]; abel
    show o.eta (N • f (σ (Submodule.Quotient.mk x))) = o.eta (N • f x)
    rw [hz', map_add (f := _), map_nsmul, smul_add, smul_smul, o.eta_add, o.eta_ker, _root_.mul_one]
  · intro κ _ _ x h hh h1
    obtain ⟨x0, rfl⟩ := hh
    have hβ : x ≫ s = spMap (Spec.preimage (x ≫ s)).hom := (Spec.map_preimage _).symm
    obtain ⟨I, hI⟩ := o.geom κ x _ hβ
    have h2 : I.ev (N * k) (N • f x0) = 1 := by rw [← hI]; exact h1
    obtain ⟨y, hy⟩ := (I.ker (N * k) (Nat.mul_pos hN hk) (Nat.Coprime.mul_left hNp hkp) _).1 h2
    rw [hy, o.eta_ker]

end GlobalTheory.UPel.HT.HeckeAd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffSubstOfForallConstantCoeffZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffSubstOfForallConstantCoeffZero
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

theorem constantCoeff_subst_of_constantCoeff_zero :
    ∀ (R : Type) [CommRing R] (σ τ : Type) [Finite σ] (a : σ → MvPowerSeries τ R),
      (∀ i, constantCoeff (a i) = 0) → ∀ g : MvPowerSeries σ R,
        constantCoeff (subst a g) = constantCoeff g := by
  intro R _ σ τ _ a h g
  have ha : HasSubst a := hasSubst_of_constantCoeff_zero h
  have e : g = MvPowerSeries.C (constantCoeff g) + (g - MvPowerSeries.C (constantCoeff g)) := by ring
  conv_lhs => rw [e]
  rw [subst_add ha, map_add (f := _), subst_C,
    constantCoeff_subst_eq_zero ha h (f := g - MvPowerSeries.C (constantCoeff g)) (by simp)]
  simp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffSubstOfForallConstantCoeffZeroStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constantCoeff_subst_of_forall_constantCoeff_zero : ∀ (R : Type) [CommRing R] (σ τ : Type) [Finite σ] (a : σ → MvPowerSeries τ R), (∀ i, constantCoeff (a i) = 0) → ∀ g : MvPowerSeries σ R, constantCoeff (subst a g) = constantCoeff g := by
  first | exact @GlobalTheory.constantCoeff_subst_of_constantCoeff_zero | exact GlobalTheory.constantCoeff_subst_of_constantCoeff_zero | (intros; apply GlobalTheory.constantCoeff_subst_of_constantCoeff_zero <;> assumption)
end
end
